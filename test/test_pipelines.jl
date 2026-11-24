# Decision pipelines: construction, compositional evaluation, the interpreters into the
# core, and agreement with CategoricalInfluenceDiagrams.

@testset "pipelines" begin
    rng = Xoshiro(20261129)

    @testset "construction" begin
        x = random_pieces(rng)
        p = closed_pipeline(x)
        @test length(pipeline_boxes(p)) == 6
        @test Set(first.(pipeline_wires(p))) == Set([:state, :signal, :action, :outcome])
        @test [b.kind for b in pipeline_boxes(p)] ==
              [:belief, :channel, :policy, :consequence, :utility, :utility]
        @test !pipeline_boxes(p)[3].bound && pipeline_boxes(p)[1].bound
        @test isempty(dom(p)) && isempty(codom(p))
        @test occursin("(open)", sprint(show, p))
        g = pipeline_graph(p)
        @test g isa PipelineGraph
        @test CDA.nparts(g, :Box) == 6 && CDA.nparts(g, :Wire) == 4
        @test CDA.nparts(g, :InPort) == 6 && CDA.nparts(g, :OutPort) == 4
        @test BOX_KINDS == (:belief, :channel, :policy, :consequence, :utility)
        # a single box is a pipeline with its wires as interface
        c = channel_box(:survey, TH, ZZ, x.L)
        @test dom(c) == FiniteSpace(:state, [:t1, :t2, :t3])
        @test codom(c) == FiniteSpace(:signal, [:z1, :z2])
        @test p == closed_pipeline(x)
        @test utility_box(:u, (AA, TH), (a, θ) -> a === :treat ? 1 : 0) ==
              utility_box(:u, (AA, TH), [0 0 0; 1 1 1])
        @test dom(identity_pipeline(TH, ZZ)) == codom(identity_pipeline(TH, ZZ))
        @test identity_pipeline(dom(c)) == identity_pipeline(TH)
    end

    @testset "ill-formed pipelines" begin
        x = random_pieces(rng)
        @test_throws PipelineStructureError channel_box(:c, TH, ZZ, [1 0; 0 1])   # shape
        @test_throws PipelineStructureError channel_box(:c, TH, ZZ, [1 1 1; 1 0 0])  # sums
        @test_throws PipelineStructureError channel_box(:c, TH, ZZ, [2 1 1; -1 0 0])
        @test_throws PipelineStructureError utility_box(:u, YY, [1, 2])
        @test_throws PipelineStructureError utility_box(:u, YY, [1.0, Inf, 2.0])
        @test_throws WireMismatchError belief_box(:b, TH,
                                                  FiniteBelief([:a, :b, :c], [1, 0, 0]))
        @test_throws ArgumentError belief_box(:b, TH, "certain")
        @test_throws ArgumentError channel_box(:c, :state, ZZ, x.L)
        @test_throws ArgumentError channel_box(:c, TH, ZZ, x.L; error=-1)
        # two producers of one wire, a repeated box name, a cycle, mismatched labels
        @test_throws PipelineStructureError decision_pipeline(belief_box(:b1, TH, x.prior),
                                                              belief_box(:b2, TH, x.prior))
        @test_throws PipelineStructureError decision_pipeline(belief_box(:b, TH, x.prior),
                                                              channel_box(:b, TH, ZZ, x.L))
        back = channel_box(:back, ZZ, TH, rational_kernel(rng, 3, 2))
        @test_throws PipelineStructureError decision_pipeline(channel_box(:c, TH, ZZ, x.L),
                                                              back)
        @test_throws WireMismatchError decision_pipeline(belief_box(:b, TH, x.prior),
                                                         channel_box(:c,
                                                                     :state => [:a, :b, :c],
                                                                     ZZ, x.L))
        @test_throws PipelineStructureError decision_pipeline(belief_box(:b, TH, x.prior);
                                                              outputs=[:nowhere])
        @test_throws PipelineStructureError decision_pipeline(channel_box(:c, TH, ZZ, x.L);
                                                              inputs=[:signal])
        @test_throws ArgumentError decision_pipeline()
        @test_throws PipelineStructureError channel_box(:c, (TH, TH), ZZ, ones(2, 3, 3))
        p = closed_pipeline(x)
        @test_throws PipelineStructureError bind_policy(p, :survey => :none)
        @test_throws PipelineStructureError bind_policy(p, :nobody => :none)
        @test_throws ArgumentError bind_policy(p, :manager => :shoot)
        @test_throws PipelineStructureError box_provenance(p, :nowhere)
        @test_throws UnboundBoxError evaluate(p)
        @test sprint(showerror, UnboundBoxError(:manager, :policy, :evaluate)) ==
              "UnboundBoxError: `evaluate` needs a table for the policy box `manager`, " *
              "which has none"
    end

    @testset "policies in every form" begin
        x = random_pieces(rng)
        p = closed_pipeline(x)
        forms = (Dict(:z1 => :none, :z2 => :treat), [:none, :treat],
                 z -> z === :z1 ? :none : :treat, [1 0; 0 1],
                 Dict((:z1,) => :none, (:z2,) => :treat))
        values = [pipeline_value(p; policies=(:manager => f)) for f in forms]
        @test all(==(first(values)), values)
        @test pipeline_value(bind_policy(p, :manager => :treat)) ==
              pipeline_value(p; policies=Dict(:manager => [:treat, :treat]))
        bound = bind_policy(p, :manager => :treat)
        @test pipeline_boxes(bound)[3].bound
        @test !pipeline_boxes(bind_policy(bound, :manager => nothing))[3].bound
        # a stochastic policy is the mixture of the deterministic ones
        mixed = pipeline_value(p; policies=(:manager => [1//2 1//2; 1//2 1//2]))
        @test mixed ==
              (pipeline_value(p; policies=(:manager => :none)) +
               pipeline_value(p; policies=(:manager => :treat))) / 2
        @test_throws PipelineStructureError pipeline_value(channel_box(:c, TH, ZZ, x.L))
    end

    @testset "evaluation: against the definition" begin
        for _ in 1:25
            x = random_pieces(rng)
            p = closed_pipeline(x)
            Q = oracle_payoff(x)
            for policy in all_policies(2, 2)
                labels = [AA[2][a] for a in policy]
                expected = sum(x.prior[θ] * x.L[z, θ] * Q[policy[z], θ]
                               for θ in 1:3, z in 1:2)
                v = evaluate(p; policies=(:manager => labels))
                @test only(v.reward) == expected ==
                      pipeline_value(p; policies=(:manager => labels))
                @test only(v.kernel.table) == 1
            end
        end
    end

    @testset "evaluation is compositional" begin
        for _ in 1:25
            x = random_pieces(rng)
            policy = rand(rng, all_policies(2, 2))
            labels = [AA[2][a] for a in policy]
            p1 = decision_pipeline(belief_box(:prior, TH, x.prior),
                                   channel_box(:survey, TH, ZZ, x.L);
                                   outputs=[:state, :signal])
            p2 = decision_pipeline(policy_box(:manager, ZZ, AA, labels),
                                   consequence_box(:model, (AA, TH), YY, x.consequence),
                                   utility_box(:animals, YY, x.u_outcome),
                                   utility_box(:handling, AA, x.u_action);
                                   inputs=[:state, :signal], outputs=[:outcome])
            p3 = decision_pipeline(channel_box(:reporting, YY, WW, x.report),
                                   utility_box(:credit, WW, x.u_report); outputs=[:report])
            v1, v2, v3 = evaluate(p1), evaluate(p2), evaluate(p3)
            # compose
            @test evaluate(compose(p1, p2)) == compose(v1, v2)
            @test evaluate(compose(p2, p3)) == compose(v2, v3)
            @test evaluate(compose(p1, p2, p3)) == compose(v1, v2, v3)
            @test compose(compose(v1, v2), v3) == compose(v1, compose(v2, v3))
            @test compose(compose(p1, p2), p3) == compose(p1, compose(p2, p3))
            # the glued pipeline is the composite
            glued = decision_pipeline(p1, p2, p3; outputs=[:report])
            @test evaluate(glued) == evaluate(compose(p1, p2, p3))
            # identities
            @test evaluate(compose(identity_pipeline(TH, ZZ), p2)) == v2
            @test evaluate(compose(p2, identity_pipeline(YY))) == v2
            idv = evaluate(identity_pipeline(YY))
            @test kernel_matrix(idv.kernel) == [1 0 0; 0 1 0; 0 0 1] &&
                  all(iszero, idv.reward)
            # tensor
            q3 = rename_boxes(rename_wires(p3, :outcome => :outcome2, :report => :report2),
                              :reporting => :reporting2, :credit => :credit2)
            @test evaluate(otimes(p3, q3)) == otimes(v3, evaluate(q3))
            @test evaluate(otimes(p1, q3)) == otimes(v1, evaluate(q3))
            @test dom(otimes(p3, q3)) == FiniteKernels.tensor_space(dom(p3), dom(q3))
            # interchange: (p1 ⊗ q3-first-half) etc. reduces to the tensor of composites
            @test evaluate(otimes(compose(p1, p2), q3)) ==
                  otimes(compose(v1, v2), evaluate(q3))
            # value pullback along the valued kernel is evaluation with a continuation
            u = rand(rng, -9:9, 2)
            K3, W3 = reward_matrices(v3)
            @test value_pullback(v3, u) == vec(sum(W3; dims=1)) .+ transpose(K3) * u
            @test value_pullback(compose(v2, v3), u) ==
                  value_pullback(v2, value_pullback(v3, u))
            # the kernel part alone is FiniteKernels' composition
            @test compose(v2, v3).kernel == compose_kernel(v2.kernel, v3.kernel)
            # agreement with the reward kernels of CategoricalInfluenceDiagrams
            @test reward_kernel(compose(v1, v2, v3)) ≈
                  CID.compose(reward_kernel(v1), reward_kernel(v2), reward_kernel(v3))
            @test reward_kernel(otimes(v3, evaluate(q3))) ≈
                  CID.otimes(reward_kernel(v3), reward_kernel(evaluate(q3)))
        end
        x = random_pieces(rng)
        c = channel_box(:survey, TH, ZZ, x.L)
        r = channel_box(:reporting, YY, WW, x.report)
        @test_throws WireMismatchError compose(c, r)
        @test_throws PipelineStructureError otimes(c, c)
        @test_throws PipelineStructureError compose(c,
                                                    rename_wires(channel_box(:survey, ZZ,
                                                                             WW,
                                                                             [1 0; 0 1])))
        @test occursin("WireMismatchError",
                       sprint(showerror,
                              WireMismatchError(:compose, nothing,
                                                dom(c), codom(c))))
        v = evaluate(c)
        @test v ≈ v && hash(v) == hash(evaluate(c)) &&
              occursin("ValuedKernel", sprint(show, v))
        @test_throws ArgumentError ValuedKernel(v.kernel, zeros(2, 2))
    end

    @testset "agreement with interpret of CategoricalInfluenceDiagrams" begin
        for _ in 1:15
            x = random_pieces(rng)
            policy = [AA[2][a] for a in rand(rng, all_policies(2, 2))]
            whole = closed_pipeline(x; policy)
            o = open_influence_diagram(whole)
            r = interpret(o.diagram, o.kernels, o.utilities, o.strategy)
            @test only(r.reward) ≈ Float64(pipeline_value(whole))
            # an open piece, with an observed and a hidden input
            piece = decision_pipeline(policy_box(:manager, ZZ, AA, policy),
                                      consequence_box(:model, (AA, TH), YY, x.consequence),
                                      utility_box(:animals, YY, x.u_outcome);
                                      inputs=[:state, :signal], outputs=[:outcome])
            op = open_influence_diagram(piece)
            @test interpret(op.diagram, op.kernels, op.utilities, op.strategy) ≈
                  reward_kernel(evaluate(piece))
        end
        x = random_pieces(rng)
        stochastic = closed_pipeline(x; policy=[1//2 1//2; 1//2 1//2])
        @test_throws ArgumentError open_influence_diagram(stochastic)
    end

    @testset "into the core: payoff table, experiment, value of information" begin
        for _ in 1:25
            x = random_pieces(rng)
            p = closed_pipeline(x)
            Q = oracle_payoff(x)
            problem = decision_problem(p; baseline=:none)
            @test problem.payoff.Q == Q
            @test problem.payoff.actions == [:none, :treat]
            @test problem.payoff.states == [:t1, :t2, :t3]
            @test problem.belief == FiniteBelief([:t1, :t2, :t3], x.prior)
            @test problem.baseline == :none
            e = observation_experiment(p)
            @test e.likelihood == x.L && e.signals == [:z1, :z2] &&
                  e.states == problem.payoff.states
            # every interpreter forwards to the core on the same problem
            core = DecisionProblem(PayoffTable([:none, :treat], [:t1, :t2, :t3], Q),
                                   x.prior)
            for rule in (MaxExpectedUtility(), Maximin(), MinimaxRegret())
                @test decide(p, rule).chosen == decide(core, rule).chosen
                @test decide(p, rule).scores == decide(core, rule).scores
                @test select(rule_selection(rule), p) == decide(core, rule).chosen
            end
            @test regret_table(p) == regret_table(core)
            @test evpi(p) == evpi(core) && act_now_value(p) == act_now_value(core)
            experiment = Experiment(x.L)
            @test evsi(p) == evsi(core, experiment)
            @test evsi(p, Experiment([1 0 0; 0 1 0; 0 0 1])) == evpi(core)
            @test value_with_information(p) == value_with_information(core, experiment)
            voi = value_of_information(p)
            @test voi.evsi == evsi(core, experiment) && voi.evpi == evpi(core)
            @test voi.act_now == act_now_value(core) && 0 <= voi.evsi <= voi.evpi
            @test voi.informed == oracle_informed_value(x.prior, x.L, Q)
            # the optimum of the pipeline over its policies
            @test voi.informed ==
                  maximum(pipeline_value(p; policies=(:manager => [AA[2][a] for a in π]))
                          for π in all_policies(2, 2))
            o = open_influence_diagram(p)
            @test contextual_optimize(o.diagram, o.kernels, o.utilities).expected_utility ≈
                  Float64(voi.informed)
            @test contextual_optimize(o.diagram, o.kernels, o.utilities;
                                      brute_force=true).expected_utility ≈
                  Float64(voi.informed)
        end
    end

    @testset "the action as an input wire, and intervention as substitution" begin
        for _ in 1:15
            x = random_pieces(rng)
            open_model = decision_pipeline(belief_box(:prior, TH, x.prior),
                                           consequence_box(:model, (AA, TH), YY,
                                                           x.consequence),
                                           utility_box(:animals, YY, x.u_outcome),
                                           utility_box(:handling, AA, x.u_action))
            @test axis_names_of(open_model) == [:action]
            problem = decision_problem(open_model)
            @test problem.payoff.Q == oracle_payoff(x)
            # each row of the table is the model with the action plugged in, state by state
            for (a, label) in enumerate(AA[2]), (θ, state) in enumerate(TH[2])
                plugged = intervene(open_model, :action => label, :state => state)
                @test isempty(dom(plugged))
                @test pipeline_value(plugged) == problem.payoff.Q[a, θ]
            end
            # plugging a lottery over actions mixes the rows
            lottery = intervene(open_model, :action => [1 // 4, 3 // 4])
            @test pipeline_value(lottery) ==
                  sum(x.prior .*
                      (problem.payoff.Q[1, :] ./ 4 .+ 3 .* problem.payoff.Q[2, :] ./ 4))
            @test observation_experiment(open_model).likelihood == [1 1 1]
            @test evaluate(open_model).reward == problem.payoff.Q * x.prior
        end
        # do(): cutting a mechanism. Conditioning on a wire is not intervening on it.
        confounded = decision_pipeline(belief_box(:weather, :wet => [:no, :yes],
                                                  [1 // 2, 1 // 2]),
                                       channel_box(:growth, :wet => [:no, :yes],
                                                   :lush => [:no, :yes],
                                                   [9//10 1//10; 1//10 9//10]),
                                       utility_box(:frogs, (:wet => [:no, :yes],),
                                                   [10, 50]))
        @test pipeline_value(confounded) == 30
        @test pipeline_value(intervene(confounded, :lush => :yes)) == 30   # frogs follow rain
        @test pipeline_value(intervene(confounded, :wet => :yes)) == 50
        made = pipeline_boxes(intervene(confounded, :lush => :yes))
        @test any(b -> b.name === :do_lush && b.kind === :belief, made)
        @test !any(b -> b.name === :growth, made)
        @test_throws PipelineStructureError intervene(confounded, :sunny => :yes)
    end

    @testset "beliefs of other monads" begin
        x = random_pieces(rng)
        credal = CredalSet([:t1, :t2, :t3], [[1 // 2, 1 // 2, 0], [0, 1 // 2, 1 // 2]])
        p = decision_pipeline(belief_box(:prior, TH, credal), policy_box(:manager, (), AA),
                              consequence_box(:model, (AA, TH), YY, x.consequence),
                              utility_box(:animals, YY, x.u_outcome))
        problem = decision_problem(p)
        @test problem.belief == credal
        core = DecisionProblem(PayoffTable([:none, :treat], [:t1, :t2, :t3],
                                           oracle_payoff(merge(x, (; u_action=[0, 0])))),
                               credal)
        for rule in (GammaMaximin(), EAdmissible(), Maximal(), Maximin())
            @test decide(p, rule).chosen == decide(core, rule).chosen
        end
        @test_throws BeliefFormError decide(p, MaxExpectedUtility())
        @test_throws MonadMismatchError evaluate(p; policies=(:manager => :none))
        scenario = replace_box(p, :prior, ScenarioSet([:t1, :t3]))
        @test decide(scenario, Maximin()).chosen ==
              decide(DecisionProblem(core.payoff, ScenarioSet([:t1, :t3])),
                     Maximin()).chosen
        point = replace_box(p, :prior, :t2)
        @test pipeline_value(point; policies=(:manager => :treat)) == core.payoff.Q[2, 2]
        @test evpi(point) == 0
    end

    @testset "several belief boxes, and the limits of the normal form" begin
        hab = :habitat => [:poor, :good]
        dis = :disease => [:absent, :present]
        table = [10 30; 4 12;;; 8 28; 6 20]        # [action, habitat, disease]
        p = decision_pipeline(belief_box(:habitat_prior, hab, [1 // 4, 3 // 4]),
                              belief_box(:disease_prior, dis, [2 // 3, 1 // 3]),
                              policy_box(:manager, (), AA),
                              utility_box(:frogs, (AA, hab, dis), table))
        problem = decision_problem(p)
        @test problem.payoff.states ==
              [:poor_absent, :good_absent, :poor_present, :good_present]
        @test problem.payoff.Q == reshape(table, 2, 4)
        @test probabilities(problem.belief) == [1 // 6, 1 // 2, 1 // 12, 1 // 4]
        @test act_now_value(p) ==
              maximum(reshape(table, 2, 4) * probabilities(problem.belief))
        # two open policies: no normal form
        two = decision_pipeline(p, policy_box(:second, (), :extra => [:a, :b]))
        @test_throws PipelineStructureError decision_problem(two)
        @test_throws PipelineStructureError decision_problem(utility_box(:u, AA, [0, 1]))
        @test_throws PipelineStructureError decision_problem(decision_pipeline(belief_box(:b,
                                                                                          hab,
                                                                                          [1,
                                                                                           0])))
        # an observation that informs about a hidden wire that is not a belief box
        hidden = :hidden => [:h1, :h2]
        leaky = decision_pipeline(belief_box(:prior, hab, [1 // 2, 1 // 2]),
                                  channel_box(:nature, hab, hidden, [1//2 1//2; 1//2 1//2]),
                                  channel_box(:peek, hidden, ZZ, [1 0; 0 1]),
                                  policy_box(:manager, ZZ, AA),
                                  utility_box(:frogs, (AA, hidden), [1 0; 0 1]))
        @test_throws PipelineStructureError observation_experiment(leaky)
        @test_throws PipelineStructureError value_of_information(leaky)
        # the compiled programme still gets it right (it does not use the normal form)
        @test solve_policy_program(leaky).value == 1
    end

    @testset "provenance" begin
        x = random_pieces(rng)
        p = decision_pipeline(closed_pipeline(x), channel_box(:reporting, YY, WW, x.report))
        all_boxes = box_provenance(p)
        @test [b.name for b in all_boxes] ==
              [:prior, :survey, :manager, :model, :animals, :handling]   # not :reporting
        @test [b.name for b in box_provenance(p, :signal)] == [:prior, :survey]
        @test [b.name for b in box_provenance(p, :handling)] ==
              [:prior, :survey, :manager, :handling]
        @test [b.name for b in box_provenance(p, :report)] ==
              [:prior, :survey, :manager, :model, :reporting]
        @test all(b -> b.kind in BOX_KINDS, all_boxes)
    end
end
