# The diagram-to-programme compilers.

# Oracle for a linear programme over stochastic policies with one linear side
# constraint: an optimum lies on an edge of the policy polytope, so it is a mixture of
# two deterministic policies. `J[a, z]` objective, `G[a, z]` constraint, `G·π ≤ b`.
function oracle_constrained_lp(J, G, b)
    na, nz = size(J)
    policies = all_policies(na, nz)
    val(π) = sum(J[π[z], z] for z in 1:nz)
    use(π) = sum(G[π[z], z] for z in 1:nz)
    best = nothing
    for π in policies, ρ in policies
        vπ, vρ, gπ, gρ = val(π), val(ρ), use(π), use(ρ)
        gπ <= b || continue                     # π feasible; move towards ρ as far as allowed
        λ = gρ <= b ? 1 // 1 : (b - gπ) // (gρ - gπ)
        v = (1 - λ) * vπ + λ * vρ
        (best === nothing || v > best) && (best = v)
    end
    return best
end

@testset "compiling pipelines to programmes" begin
    rng = Xoshiro(20261201)

    @testset "one decision: the linear programme is exact" begin
        for _ in 1:20
            x = random_pieces(rng)
            p = closed_pipeline(x)
            Q = oracle_payoff(x)
            expected = oracle_informed_value(x.prior, x.L, Q)
            prog = policy_program(p)
            @test prog isa DecisionProgram && prog.name === :pipeline_policy
            @test prog.model isa JuMP.GenericModel{Rational{BigInt}}
            @test size(prog.variables.π) == (2, 2)
            @test JuMP.num_variables(prog.model) == 4
            @test length(prog.constraints.simplex) == 2 && isempty(prog.constraints.side)
            # three routes to the same model
            internal = solve_program(prog)
            @test internal.status === :optimal && internal.exact
            @test internal.objective == expected
            @test solve_program(policy_program(p);
                                optimizer=CDDLib.Optimizer{Rational{BigInt}}).objective ==
                  expected
            highs = solve_program(policy_program(p); optimizer=HiGHS.Optimizer)
            @test highs.objective == expected && highs.exact
            # the same number from the core and from CategoricalInfluenceDiagrams
            @test expected == value_with_information(p) == value_of_information(p).informed
            o = open_influence_diagram(p)
            @test contextual_optimize(o.diagram, o.kernels, o.utilities).expected_utility ≈
                  Float64(expected)
            # the objective at a policy is the expected utility of the pipeline with it bound
            sol = solve_policy_program(p)
            @test sol.status === :optimal && sol.value == expected && sol.exact
            @test sol.actions == [:none, :treat] && sol.observations == [:z1, :z2]
            @test pipeline_value(p; policies=(:manager => sol.policy)) == expected
            for π in all_policies(2, 2)
                table = [π[z] == a ? 1 : 0 for a in 1:2, z in 1:2]
                J = [sum(x.prior[θ] * x.L[z, θ] * Q[a, θ] for θ in 1:3)
                     for a in 1:2, z in 1:2]
                @test sum(J .* table) == pipeline_value(p; policies=(:manager => table))
            end
            # the dual certificate: the column maxima of the objective coefficients
            J = [sum(x.prior[θ] * x.L[z, θ] * Q[a, θ] for θ in 1:3) for a in 1:2, z in 1:2]
            @test sum(maximum(J; dims=1)) == expected
        end
        # with ties broken by the simplex the optimum may be reported at a vertex or not;
        # without ties it is deterministic
        x = (; prior=[1 // 2, 1 // 4, 1 // 4], L=[1 0 0; 0 1 1],
             consequence=reshape([1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1] .//
                                 1,
                                 3, 2, 3), u_outcome=[0, 10, 30], u_action=[0, -1])
        sol = solve_policy_program(closed_pipeline(x))
        @test sol.deterministic && occursin("deterministic", sprint(show, sol))
    end

    @testset "floating-point pipelines" begin
        x = random_pieces(rng)
        xf = map(v -> v isa AbstractArray ? Float64.(v) : v, x)
        p = closed_pipeline(xf)
        prog = policy_program(p)
        @test prog.model isa JuMP.GenericModel{Float64}
        @test solve_program(prog).objective ≈
              Float64(value_with_information(closed_pipeline(x)))
        @test solve_program(policy_program(p); optimizer=HiGHS.Optimizer).objective ≈
              Float64(value_with_information(closed_pipeline(x)))
    end

    @testset "a budget constraint that the influence-diagram solvers cannot express" begin
        for _ in 1:25
            x = random_pieces(rng)
            p = closed_pipeline(x)
            Q = oracle_payoff(x)
            J = [sum(x.prior[θ] * x.L[z, θ] * Q[a, θ] for θ in 1:3) for a in 1:2, z in 1:2]
            # the expected number of ponds handled: 1 when treating, 0 otherwise
            G = [a == 2 ? sum(x.prior[θ] * x.L[z, θ] for θ in 1:3) : 0 // 1
                 for a in 1:2, z in 1:2]
            budget = rand(rng, 1:9) // 10
            cap = expectation_constraint(:capacity, AA, [0, 1]; at_most=budget)
            sol = solve_policy_program(p; constraints=[cap])
            @test sol.status === :optimal
            @test sol.value == oracle_constrained_lp(J, G, budget)
            @test sum(G .* sol.policy) <= budget
            @test sol.value <= value_with_information(p)
            # the three routes agree
            @test solve_policy_program(p; constraints=[cap],
                                       optimizer=CDDLib.Optimizer{Rational{BigInt}}).value ==
                  sol.value
            @test solve_policy_program(p; constraints=[cap],
                                       optimizer=HiGHS.Optimizer).value ==
                  sol.value
            # the policy returned really has that value and that use, on the pipeline
            @test pipeline_value(p; policies=(:manager => sol.policy)) == sol.value
            # deterministic policies under the same budget: no better than the randomised
            det = solve_strategy_program(strategy_program(p; constraints=[cap]))
            feasible = [π
                        for π in all_policies(2, 2)
                        if sum(G[π[z], z] for z in 1:2) <= budget]
            @test det.value == maximum(sum(J[π[z], z] for z in 1:2) for π in feasible)
            @test det.value <= sol.value
            highs = solve_strategy_program(strategy_program(p; constraints=[cap]);
                                           optimizer=HiGHS.Optimizer)
            @test highs.value == det.value && !highs.exact && highs.route === :optimizer
        end
        # a case where the budget binds and the best policy randomises
        st = :pond => [:clear, :infected]
        act = :action => [:none, :treat]
        p = decision_pipeline(belief_box(:prior, st, [1 // 2, 1 // 2]),
                              policy_box(:manager, (), act),
                              utility_box(:frogs, (act, st), [60 20; 50 50]))
        cap = expectation_constraint(:capacity, act, [0, 1]; at_most=1 // 4)
        sol = solve_policy_program(p; constraints=[cap])
        @test !sol.deterministic && sol.policy == reshape([3 // 4, 1 // 4], 2, 1)
        @test sol.value == 85 // 2                        # 40 + (50 − 40)/4
        @test value_with_information(p) == 50             # unconstrained: always treat
        @test solve_strategy_program(strategy_program(p; constraints=[cap])).value == 40
        floor_ = expectation_constraint(:floor, (act, st), [60 20; 50 50]; at_least=100)
        @test solve_policy_program(p; constraints=[floor_]).status === :infeasible
        @test solve_strategy_program(strategy_program(p; constraints=[floor_])).status ===
              :infeasible
        @test_throws ArgumentError expectation_constraint(:c, act, [0, 1])
        @test_throws ArgumentError expectation_constraint(:c, act, [0, 1]; at_most=1,
                                                          at_least=0)
        @test_throws CompilationError policy_program(p;
                                                     constraints=[expectation_constraint(:c,
                                                                                         :nowhere,
                                                                                         [0,
                                                                                          1];
                                                                                         at_most=1)])
        @test_throws CompilationError policy_program(p;
                                                     constraints=[expectation_constraint(:c,
                                                                                         act,
                                                                                         [0,
                                                                                          1,
                                                                                          2];
                                                                                         at_most=1)])
    end

    @testset "a chance constraint" begin
        for _ in 1:20
            x = random_pieces(rng)
            p = closed_pipeline(x)
            Q = oracle_payoff(x)
            J = [sum(x.prior[θ] * x.L[z, θ] * Q[a, θ] for θ in 1:3) for a in 1:2, z in 1:2]
            # P(outcome = y1), the bad outcome, by policy cell
            G = [sum(x.prior[θ] * x.L[z, θ] * x.consequence[1, a, θ] for θ in 1:3)
                 for a in 1:2, z in 1:2]
            lo = sum(minimum(G; dims=1))
            level = lo + rand(rng, 0:5) // 20
            risk = chance_constraint(:collapse, YY, y -> y === :y1; at_most=level)
            sol = solve_policy_program(p; constraints=[risk])
            @test sol.value == oracle_constrained_lp(J, G, level)
            @test sum(G .* sol.policy) <= level
        end
    end

    @testset "strategy programmes: several decisions" begin
        ob2 = :second_look => [:s1, :s2]
        act2 = :follow_up => [:leave, :cull]
        for _ in 1:8
            x = random_pieces(rng)
            L2 = rational_kernel(rng, 2, 3; zeros=true)
            u2 = rand(rng, -10:20, 2, 2, 3)                 # [action, follow_up, state]
            first_part = decision_pipeline(belief_box(:prior, TH, x.prior),
                                           channel_box(:survey, TH, ZZ, x.L),
                                           policy_box(:manager, ZZ, AA),
                                           utility_box(:handling, AA, x.u_action);
                                           outputs=[:state, :action])
            # the second decision sees a second observation, not the first one: no recall
            second_part = decision_pipeline(channel_box(:resurvey, TH, ob2, L2),
                                            policy_box(:ranger, ob2, act2),
                                            utility_box(:animals, (AA, act2, TH), u2);
                                            inputs=[:state, :action])
            whole = compose(first_part, second_part)
            # exhaustive oracle: every pair of deterministic policies, from the definition
            oracle = maximum(sum(x.prior[θ] * x.L[z, θ] * L2[s, θ] *
                                 (x.u_action[π[z]] + u2[π[z], ρ[s], θ])
                                 for θ in 1:3, z in 1:2, s in 1:2)
                             for π in all_policies(2, 2), ρ in all_policies(2, 2))
            glued = strategy_program(whole)
            chain = strategy_program([first_part, second_part])
            composed = compose(strategy_program(first_part),
                               open_strategy_program(second_part))
            for prog in (glued, chain, composed)
                enumerated = solve_strategy_program(prog)
                @test enumerated.status === :optimal && enumerated.exact
                @test enumerated.value == oracle
                @test enumerated.strategies == 16
                solved = solve_strategy_program(prog; optimizer=HiGHS.Optimizer)
                @test solved.value == oracle
                # the policies found attain the value on the pipeline
                @test pipeline_value(whole; policies=solved.policies) == oracle
            end
            # compiling the composite = composing the compiled parts: the same decisions
            # and the same optimum (checked above for all three)
            @test Set(keys(glued.policies)) == Set(keys(chain.policies)) ==
                  Set(keys(composed.policies)) == Set([:manager, :ranger])
            @test JuMP.num_variables(chain.model) == JuMP.num_variables(composed.model)
            @test length(chain.parts) == 2 && length(glued.parts) == 1
            # and the same as CategoricalInfluenceDiagrams on the glued diagram
            o = open_influence_diagram(whole)
            @test contextual_optimize(o.diagram, o.kernels, o.utilities).expected_utility ≈
                  Float64(oracle)
        end
    end

    @testset "strategy programme of one decision = the linear programme" begin
        for _ in 1:10
            x = random_pieces(rng)
            p = closed_pipeline(x)
            s = solve_strategy_program(strategy_program(p))
            @test s.value == value_with_information(p) == solve_policy_program(p).value
            @test size(s.policies[:manager]) == (2,)
            @test occursin("1 decision", sprint(show, strategy_program(p)))
            @test occursin("enumeration", sprint(show, s))
        end
        # no decision at all: the programme is the evaluation
        x = random_pieces(rng)
        bound = closed_pipeline(x; policy=:treat)
        @test solve_strategy_program(strategy_program(bound)).value == pipeline_value(bound)
    end

    @testset "what cannot be compiled" begin
        x = random_pieces(rng)
        p = closed_pipeline(x)
        two = decision_pipeline(p, policy_box(:second, (), :extra => [:a, :b]))
        @test_throws CompilationError policy_program(two)
        @test_throws CompilationError policy_program(closed_pipeline(x; policy=:treat))
        open_model = consequence_box(:model, (AA, TH), YY, x.consequence)
        @test_throws CompilationError policy_program(decision_pipeline(open_model,
                                                                       policy_box(:m, (),
                                                                                  AA)))
        @test_throws CompilationError strategy_program(open_model)
        @test_throws CompilationError solve_strategy_program(open_strategy_program(open_model))
        @test_throws CompilationError solve_strategy_program(strategy_program(p);
                                                             max_strategies=1)
        @test_throws CompilationError compose(strategy_program(p), strategy_program(p))
        @test_throws CompilationError strategy_program(p;
                                                       constraints=[expectation_constraint(:c,
                                                                                           :nowhere,
                                                                                           [1];
                                                                                           at_most=1)])
        @test_throws ArgumentError strategy_program(DecisionPipeline[])
        @test_throws WireMismatchError strategy_program([p, open_model])
    end
end
