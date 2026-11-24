# Sequential problems: the product of selection functions against exhaustive search,
# the refusals, and the two counterexamples of the Lean development.

# Rockafellar and Uryasev's objective maximised over the atoms: the definition of `cvar`
# in the Lean development (`Finite/BackwardInductionFails.lean`).
function rockafellar_uryasev_cvar(α, p, x)
    return maximum(x[i] - sum(p[j] * max(x[i] - x[j], 0) for j in eachindex(x)) / α
                   for i in eachindex(x))
end

@testset "sequential problems" begin
    rng = Xoshiro(20261127)
    D, P, C = DistributionMonad(), PowersetMonad(), CredalMonad()

    # A random problem and the same problem as plain data for the oracle.
    function random_problem(shape; monad=D)
        stages, data = Any[], Any[]
        for (k, kind) in enumerate(shape)
            if kind === :d
                actions = [Symbol(:a, k, :_, i) for i in 1:2]
                push!(stages, DecisionStage(Symbol(:d, k), actions))
                push!(data, (:decision, actions))
            else
                outcomes = [Symbol(:x, k, :_, i) for i in 1:2]
                w = rational_probabilities(rng, 2)
                law = monad isa DistributionMonad ? FiniteDistribution(outcomes, w) :
                      FiniteSubset(outcomes)
                push!(stages, ChanceStage(Symbol(:c, k), outcomes, law))
                push!(data, (:chance, (outcomes, w)))
            end
        end
        table = Dict{Tuple,Rational{Int}}()
        payoff = h -> get!(() -> rand(rng, 0:12) // 1, table, h)
        problem = SequentialProblem(monad, stages, payoff)
        foreach(payoff, CDA._histories(problem, length(stages)))     # fix the table
        return problem, data, h -> table[h]
    end

    shapes = ((:d, :c), (:c, :d), (:d, :c, :d), (:c, :d, :c), (:d, :d, :c),
              (:d, :c, :d, :c))

    @testset "expectation: product = exhaustive search" begin
        for shape in shapes, _ in 1:6
            problem, data, payoff = random_problem(shape)
            oracle = maximum(oracle_expectation(oracle_outcomes(data, payoff, π))
                             for π in oracle_policies(data))
            bi = backward_induction(problem, MaxExpectedUtility())
            ps = policy_search(problem, Expectation())
            @test bi.value == oracle == ps.value
            @test bi.label === :optimal && bi.recursion_value == bi.value
            @test bi.method === :backward_induction && ps.method === :policy_search
            # the policy returned attains the value, and its law is the product's law
            @test policy_value(problem, bi.policy, Expectation()) == oracle
            @test policy_law(problem, bi.policy) == bi.law
            @test nested_value(problem, bi.policy, Expectation()) == oracle
            @test ps.policies == length(oracle_policies(data))
        end
    end

    @testset "worst and best case: product = exhaustive search" begin
        for shape in shapes, _ in 1:4
            problem, data, payoff = random_problem(shape; monad=P)
            for (rule, summary, α) in ((Maximin(), oracle_minimum, InfimumAlgebra()),
                                       (Maximax(), oracle_maximum, SupremumAlgebra()))
                oracle = maximum(summary(oracle_outcomes(data, payoff, π))
                                 for π in oracle_policies(data))
                @test backward_induction(problem, rule).value == oracle
                @test backward_induction(problem, α).value == oracle
                @test policy_search(problem, rule).value == oracle
            end
        end
    end

    @testset "lower expectation over the sequential composite" begin
        for _ in 1:8
            function law()
                return CredalHull([FiniteDistribution([:x, :y],
                                                      rational_probabilities(rng, 2))
                                   for _ in 1:2])
            end
            table = Dict(h => rand(rng, 0:9)
                         for h in Iterators.product([:a, :b], [:x, :y],
                                                    [:l, :r], [:x, :y]))
            problem = SequentialProblem(C,
                                        [DecisionStage(:d1, [:a, :b]),
                                         ChanceStage(:c1, [:x, :y], law()),
                                         DecisionStage(:d2, [:l, :r]),
                                         ChanceStage(:c2, [:x, :y], law())], h -> table[h])
            bi = backward_induction(problem, GammaMaximin())
            @test bi.value == policy_search(problem, LowerExpectation()).value
            @test bi.label === :optimal
        end
    end

    @testset "a certainty equivalent admits backward induction on terminal payoffs" begin
        cube = TransportedAlgebra(ExpectationAlgebra(), x -> float(x)^3, cbrt)
        for _ in 1:6
            problem, _, _ = random_problem((:d, :c, :d, :c))
            @test backward_induction(problem, cube).value ≈
                  policy_search(problem, cube).value
        end
    end

    @testset "history-dependent chance and a decision on a signal" begin
        # The decision tree of a test: signal first, then the action, then the state from
        # its posterior. Its value is the core's value with information.
        for _ in 1:20
            t = random_payoff_table(rng, 2, 3; T=Rational{Int})
            prior = rational_probabilities(rng, 3)
            e = Experiment(rational_kernel(rng, 2, 3; zeros=true); signals=[:neg, :pos])
            inv = bayesian_inverse(FiniteBelief(t.states, prior), e)
            keep = [z for z in 1:2 if !iszero(inv.evidence[z])]
            signal = FiniteDistribution(e.signals[keep], inv.evidence[keep])
            function state_law(h)
                return FiniteDistribution(t.states,
                                          posterior(inv, findfirst(==(h[1]), e.signals)))
            end
            row, col = Dict(zip(t.actions, 1:2)), Dict(zip(t.states, 1:3))
            tree = SequentialProblem([ChanceStage(:signal, e.signals, signal),
                                      DecisionStage(:act, t.actions),
                                      ChanceStage(:state, t.states, state_law)],
                                     h -> t.Q[row[h[2]], col[h[3]]])
            problem = DecisionProblem(t, prior)
            @test backward_induction(tree, MaxExpectedUtility()).value ==
                  value_with_information(problem, e)
            @test policy_search(tree, MaxExpectedUtility()).value ==
                  value_with_information(problem, e)
        end
    end

    @testset "CVaR: the Lean counterexample (cvar_backward_induction_suboptimal)" begin
        # x₁ a fair coin paying 0 or 10; then safe pays 1, risky pays 0 or 4 on a second
        # fair coin; level 3/4.
        coin1 = FiniteDistribution([:zero, :ten], [1 // 2, 1 // 2])
        coin2 = FiniteDistribution([:tails, :heads], [1 // 2, 1 // 2])
        first_reward = Dict(:zero => 0, :ten => 10)
        second(a, c) = a === :safe ? 1 : (c === :heads ? 4 : 0)
        problem = SequentialProblem([ChanceStage(:x1, [:zero, :ten], coin1),
                                     DecisionStage(:act, [:safe, :risky]),
                                     ChanceStage(:x2, [:tails, :heads], coin2)],
                                    h -> first_reward[h[1]] + second(h[2], h[3]))
        rule = DecisionRule(CVaR(3 // 4))
        @test_throws BackwardInductionError backward_induction(problem, rule)
        @test_throws BackwardInductionError backward_induction(problem, CVaR(3 // 4))
        @test_throws BackwardInductionError backward_induction(problem, CVaRMap(3 // 4))
        nested = backward_induction(problem, rule; nested=true)
        best = policy_search(problem, rule)
        @test nested.label === :nested
        @test nested.policy == Dict((:zero,) => :risky, (:ten,) => :risky)
        @test nested.value == 14 // 3            # what the nested policy is worth, flat
        @test best.value == 5                    # the best policy for flat CVaR
        @test best.policy == Dict((:zero,) => :risky, (:ten,) => :safe)
        @test best.label === :optimal
        # backward induction is optimal for the nested rule: no policy has a larger
        # nested value
        policies = [Dict((:zero,) => a, (:ten,) => b)
                    for a in (:safe, :risky),
                        b in (:safe, :risky)]
        @test nested.recursion_value ==
              maximum(nested_value(problem, π, rule) for π in policies)
        @test nested.recursion_value == nested_value(problem, nested.policy, rule)
        # and the nested rule is a different rule from the flat one
        @test nested_value(problem, best.policy, rule) == 41 // 9
        @test nested_value(problem, best.policy, rule) < nested.recursion_value == 14 // 3
        @test backward_induction(problem, rule; heuristic=true).label === :nested
        err = try
            backward_induction(problem, rule)
        catch e
            e
        end
        @test occursin("nested", sprint(showerror, err))
    end

    @testset "nested rules: backward induction is optimal for the nested value" begin
        for α in (CVaRMap(1 // 2), QuantileMap(1 // 2)), _ in 1:6
            problem, data, _ = random_problem((:c, :d, :c))
            sol = backward_induction(problem, α; nested=true)
            policies = oracle_policies(data)
            @test sol.recursion_value ==
                  maximum(nested_value(problem, π, α) for π in policies)
            @test sol.value <= policy_search(problem, α).value
            # the policy search agrees with an oracle written from the definition
            if α isa CVaRMap
                _, data2, payoff2 = problem, data, problem.payoff
                @test policy_search(problem, α).value ==
                      maximum(oracle_cvar(oracle_outcomes(data2, payoff2, π), 1 // 2)
                              for π in policies)
            end
        end
        hurwicz, data, _ = random_problem((:d, :c, :d, :c); monad=P)
        @test backward_induction(hurwicz, HurwiczMap(1 // 2); nested=true).value <=
              policy_search(hurwicz, HurwiczMap(1 // 2)).value
        @test_throws BackwardInductionError backward_induction(hurwicz,
                                                               DecisionRule(Hurwicz(1 // 2)))
        @test_throws BackwardInductionError backward_induction(hurwicz,
                                                               DecisionRule(Laplace()))
    end

    @testset "minimax regret: the Lean counterexample" begin
        # Plans over two states: stop = (0, 9), b = (10, 0), c = (6, 3). Stage one chooses
        # between stopping and going on; stage two between b and c.
        plan = Dict(:b => (10, 0), :c => (6, 3))
        payoff(h) = h[1] === :stop ? (h[3] === :s1 ? 0 : 9) :
                    plan[h[2]][h[3] === :s1 ? 1 : 2]
        problem = SequentialProblem(P,
                                    [DecisionStage(:first, [:stop, :go]),
                                     DecisionStage(:second, [:b, :c]),
                                     ChanceStage(:state, [:s1, :s2],
                                                 FiniteSubset([:s1, :s2]))],
                                    payoff)
        @test_throws BackwardInductionError backward_induction(problem, MinimaxRegret())
        @test_throws BackwardInductionError backward_induction(problem, MinimaxRegret();
                                                               nested=true)
        staged = backward_induction(problem, MinimaxRegret(); heuristic=true)
        best = policy_search(problem, MinimaxRegret())
        @test staged.label === :heuristic && staged.recursion_value === nothing
        @test staged.policy[()] == :go && staged.policy[(:go,)] == :b
        @test staged.value == 9                   # backward induction picks b
        @test best.value == 6                     # the full menu's minimax regret: c
        @test best.policy[()] == :go && best.policy[(:go,)] == :c
        # the same from the core, on the table of plans
        t = PayoffTable([:stop, :b, :c], [:s1, :s2], [0 9; 10 0; 6 3])
        core = decide(DecisionProblem(t, ScenarioSet([:s1, :s2])), MinimaxRegret())
        @test core.chosen == [:c] && minimum(core.scores) == 6
        @test_throws BackwardInductionError backward_induction(problem,
                                                               rule_selection(MinimaxRegret()))
    end

    @testset "minimax regret: policy search against the core on the strategic form" begin
        for _ in 1:10
            table = Dict(h => rand(rng, 0:9)
                         for h in Iterators.product([:a, :b], [:l, :r],
                                                    [:x, :y]))
            problem = SequentialProblem(P,
                                        [DecisionStage(:d1, [:a, :b]),
                                         DecisionStage(:d2, [:l, :r]),
                                         ChanceStage(:nature, [:x, :y],
                                                     FiniteSubset([:x, :y]))],
                                        h -> table[h])
            plans = [(a, b) for a in (:a, :b) for b in (:l, :r)]
            Q = [table[(a, b, ω)] for (a, b) in plans, ω in (:x, :y)]
            core = decide(DecisionProblem(PayoffTable(Q), ScenarioSet([:s1, :s2])),
                          MinimaxRegret())
            @test policy_search(problem, MinimaxRegret()).value == minimum(core.scores)
            @test backward_induction(problem, MinimaxRegret(); heuristic=true).value >=
                  minimum(core.scores)
        end
        dist, _, _ = random_problem((:d, :c))
        @test_throws MonadMismatchError policy_search(dist, MinimaxRegret())
        dependent = SequentialProblem(P,
                                      [DecisionStage(:d, [:a, :b]),
                                       ChanceStage(:c, [:x, :y], h -> FiniteSubset([:x]))],
                                      h -> 1)
        @test_throws ArgumentError policy_search(dependent, MinimaxRegret())
    end

    @testset "set-valued products: deterministic problems only" begin
        for _ in 1:20
            table = Dict(h => rand(rng, 0:3)
                         for h in Iterators.product([:a, :b], [:l, :r],
                                                    [:u, :v]))
            problem = SequentialProblem([DecisionStage(:d1, [:a, :b]),
                                         DecisionStage(:d2, [:l, :r]),
                                         DecisionStage(:d3, [:u, :v])], h -> table[h])
            best = maximum(values(table))
            exhaustive = FiniteSubset([h for (h, v) in table if v == best])
            @test optimal_plays(problem) == exhaustive
            @test backward_induction(problem, MaxExpectedUtility()).value == best
        end
        # With nature in the product the set is too small: here every policy is
        # maximin-optimal (the worst case is 0 whatever is done), so both plays after
        # :good can occur under an optimal policy, but the product keeps only one.
        worth = Dict((:bad, :l) => 0, (:bad, :r) => 0, (:good, :l) => 5, (:good, :r) => 1)
        M, α = PowersetMonad(), SupremumAlgebra()
        nature = constant_selection([:bad, :good], FiniteSubset([:bad, :good]);
                                    algebra=InfimumAlgebra())
        reply = argmax_selection([:l, :r]; monad=M, algebra=InfimumAlgebra(), ties=:all)
        plays = select(selection_product(nature, reply), h -> worth[h])
        @test !((:good, :r) in plays) && (:good, :l) in plays
        chancy = SequentialProblem(P,
                                   [ChanceStage(:c, [:bad, :good],
                                                FiniteSubset([:bad, :good])),
                                    DecisionStage(:d, [:l, :r])], h -> worth[h])
        @test_throws ArgumentError optimal_plays(chancy)
        @test policy_search(chancy, Maximin()).value == 0
    end

    @testset "CVaR: Rockafellar-Uryasev over the atoms = the sorted tail" begin
        # The Lean development defines CVaR by the first form and does not prove it equal
        # to the second, which is what the core and `CVaRMap` compute.
        for _ in 1:400
            n = rand(rng, 1:6)
            x = rand(rng, -10:10, n) .// 1
            p = rational_probabilities(rng, n; zeros=rand(rng) < 0.3)
            α = rand(rng, 1:8) // 8
            sorted_tail = CVaRMap(α)((d -> monad_map(D, i -> x[i], d))(FiniteDistribution(collect(1:n),
                                                                                          p)))
            @test rockafellar_uryasev_cvar(α, p, x) == sorted_tail
            t = PayoffTable(reshape(x, 1, n))
            @test aggregate(CVaR(α), DecisionProblem(t, p)) == [sorted_tail]
        end
    end

    @testset "construction and errors" begin
        @test_throws ArgumentError SequentialProblem([], h -> 0)
        @test_throws ArgumentError SequentialProblem([DecisionStage(:d, [:a]),
                                                      DecisionStage(:d, [:b])], h -> 0)
        @test_throws ArgumentError SequentialProblem([:not_a_stage], h -> 0)
        @test_throws ArgumentError DecisionStage(:d, Symbol[])
        @test_throws ArgumentError DecisionStage(:d, [:a, :a])
        @test_throws ArgumentError ChanceStage(:c, [:x, :x], FiniteSubset([:x]))
        problem, _, _ = random_problem((:d, :c))
        @test_throws MonadMismatchError backward_induction(problem, Maximin())
        @test_throws MonadMismatchError policy_value(problem, Dict(() => :a1_1),
                                                     InfimumAlgebra())
        @test_throws ArgumentError policy_law(problem, Dict{Tuple,Symbol}())
        @test_throws ArgumentError policy_search(problem, Satisfice(0))
        @test_throws ArgumentError policy_search(problem, EAdmissible())
        @test_throws ArgumentError policy_search(problem, Expectation(); max_policies=1)
        @test_throws ArgumentError policy_value(problem, Dict(() => :a1_1), MinimaxRegret())
        @test_throws ArgumentError nested_value(problem, Dict(() => :a1_1), MinimaxRegret())
        @test_throws ArgumentError policy_search(problem,
                                                 DecisionRule(Expectation();
                                                              transform=RegretTransform()))
        @test occursin("decide d1 → chance c2", sprint(show, problem))
        @test occursin("policy_search", sprint(show, policy_search(problem, Expectation())))
    end
end
