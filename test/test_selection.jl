# Selection functions: every rule of the core as a selection function, and the product.

@testset "selection functions" begin
    rng = Xoshiro(20261126)

    @testset "every scalar rule reproduces decide" begin
        scalar_rules = [MaxExpectedUtility(), Maximin(), Maximax(), MinimaxRegret(),
                        Satisfice(0), Satisfice(3; aggregator=WorstCase()),
                        Satisfice(5; transform=RegretTransform()),
                        DecisionRule(Hurwicz(1 // 3)), DecisionRule(Laplace()),
                        DecisionRule(CVaR(1 // 4)), DecisionRule(Quantile(1 // 2)),
                        DecisionRule(Expectation(); transform=RegretTransform()),
                        DecisionRule(CVaR(1 // 2); transform=RegretTransform()),
                        DecisionRule(Hurwicz(1 // 4); transform=RegretTransform()),
                        DecisionRule(Laplace(); transform=RegretTransform()),
                        DecisionRule(WorstCase(); scenarios=[:s1, :s3])]
        credal_rules = [GammaMaximin(), DecisionRule(UpperExpectation()),
                        DecisionRule(AlphaMaxmin(1 // 3)), EAdmissible(), Maximal(),
                        IntervalDominance()]
        compared = 0
        for _ in 1:40
            t = random_payoff_table(rng, 4, 4; T=Rational{Int})
            # ties are common with small integers, which is what we want to test
            t = PayoffTable(t.actions, t.states, round.(Int, 4 .* t.Q) .// 1)
            beliefs = [FiniteBelief(t.states, rational_probabilities(rng, 4; zeros=true)),
                       ScenarioSet(t.states[[1, 3, 4]]), PointBelief(t.states[2]),
                       random_credal_set(rng, 4, 3; T=Rational{Int})]
            beliefs[4] = CredalSet(t.states, extreme_points(beliefs[4]))
            for belief in beliefs, rule in vcat(scalar_rules, credal_rules)
                p = DecisionProblem(t, belief; feasible=[true, true, false, true])
                expected = try
                    decide(p, rule)
                catch err
                    err isa Union{BeliefFormError,ArgumentError} || rethrow()
                    nothing
                end
                r = rule_selection(rule)
                if expected === nothing
                    # Where the core refuses the pairing, the selection function either
                    # refuses it too or reads the belief through a monad morphism.
                    continue
                end
                @test select(r, p) == expected.chosen
                expected.scores === nothing || @test rule_scores(r, p) == expected.scores
                expected.scores === nothing ||
                    @test quantifier(r, p) == (expected.sense === :max ?
                                               maximum(expected.scores) :
                                               minimum(expected.scores))
                compared += 1
            end
        end
        @test compared > 1500
    end

    @testset "floating point, with the core's tie tolerance" begin
        for _ in 1:30
            t = random_payoff_table(rng, 4, 5)
            p = DecisionProblem(t, random_belief(rng, 5))
            for rule in (MaxExpectedUtility(), Maximin(), MinimaxRegret(),
                         DecisionRule(CVaR(0.3)), DecisionRule(Laplace()))
                @test select(rule_selection(rule), p) == decide(p, rule).chosen
                @test rule_scores(rule_selection(rule), p) ≈ decide(p, rule).scores
            end
            c = DecisionProblem(t, random_credal_set(rng, 5, 3))
            for rule in (GammaMaximin(), Maximal(), IntervalDominance(), EAdmissible())
                @test select(rule_selection(rule), c) == decide(c, rule).chosen
            end
        end
    end

    @testset "the pairing of belief and algebra" begin
        t = PayoffTable([:a, :b], [:s1, :s2], [3 0; 1 1])
        credal = DecisionProblem(t, CredalSet(t.states, [[1, 0], [0, 1]]))
        scen = DecisionProblem(t, ScenarioSet(t.states))
        # no morphism from credal sets or from sets to distributions: refused, as in the core
        @test_throws MonadMismatchError select(rule_selection(MaxExpectedUtility()), credal)
        @test_throws BeliefFormError decide(credal, MaxExpectedUtility())
        @test_throws MonadMismatchError select(rule_selection(MaxExpectedUtility()), scen)
        # a set read as a credal set along the morphism P⁺ → C: Γ-maximin is then maximin.
        # The core refuses this pairing; the morphism makes it meaningful.
        @test_throws BeliefFormError decide(scen, GammaMaximin())
        @test select(rule_selection(GammaMaximin()), scen) == decide(scen, Maximin()).chosen
        # a single prior read as a credal set: the robust rules reduce to the Bayes actions
        single = DecisionProblem(t, [1 // 4, 3 // 4])
        for rule in (GammaMaximin(), EAdmissible(), Maximal(), IntervalDominance())
            @test select(rule_selection(rule), single) ==
                  decide(single, MaxExpectedUtility()).chosen
        end
        sample = DecisionProblem(t, SampleBelief(2))
        @test_throws BeliefFormError select(rule_selection(DecisionRule(Laplace())), sample)
    end

    @testset "swapping the two boxes" begin
        t = PayoffTable([:nothing, :levee, :relocate], [:low, :moderate, :high, :extreme],
                        [0 -10 -60 -150; -20 -20 -25 -90; -48 -48 -48 -48])
        p = DecisionProblem(t, [1 // 2, 3 // 10, 3 // 20, 1 // 20])
        @test select(rule_selection(; algebra=ExpectationAlgebra()), p) == [:nothing]
        @test select(rule_selection(; algebra=InfimumAlgebra()), p) == [:relocate]
        @test select(rule_selection(; algebra=SupremumAlgebra()), p) == [:nothing]
        @test select(rule_selection(; algebra=InfimumAlgebra(), transform=:regret), p) ==
              [:levee]
        @test select(rule_selection(; algebra=ExpectationAlgebra(),
                                    selector=(:threshold, -25)), p) == [:nothing, :levee]
        @test select(rule_selection(; algebra=Laplace()), p) ==
              decide(p, DecisionRule(Laplace())).chosen
        @test select(rule_selection(; algebra=CVaR(1 // 10)), p) ==
              decide(p, DecisionRule(CVaR(1 // 10))).chosen
        @test quantifier(rule_selection(MinimaxRegret()), p) == 42
        @test rule_scores(rule_selection(EAdmissible()), p) === nothing
        @test_throws ArgumentError quantifier(rule_selection(Maximal()), p)
        @test_throws ArgumentError rule_selection(; algebra=ExpectationAlgebra(),
                                                  transform=:square)
        @test_throws ArgumentError rule_selection(; algebra=ExpectationAlgebra(),
                                                  selector=:satisfice)
        zero_best = DecisionProblem(PayoffTable([1 0; -1 -2]), [1 // 2, 1 // 2])
        @test_throws ArgumentError select(rule_selection(; algebra=InfimumAlgebra(),
                                                         transform=:relative_regret),
                                          zero_best)
        @test occursin("MinimaxRegret", sprint(show, rule_selection(MinimaxRegret())))
    end

    @testset "Pareto front" begin
        for _ in 1:30
            tables = [random_payoff_table(rng, 5, 3; T=Rational{Int}) for _ in 1:2]
            prior = rational_probabilities(rng, 3)
            problems = [DecisionProblem(t, prior) for t in tables]
            @test pareto_selection(problems) == decide(problems, ParetoFront()).chosen
        end
        @test_throws ArgumentError pareto_selection(DecisionProblem[])
    end

    @testset "selection functions and quantifiers" begin
        ε = argmax_selection([:a, :b, :c])
        q = Dict(:a => 1, :b => 5, :c => 5)
        @test select(ε, x -> q[x]) == :b                       # the first maximiser
        @test select(ε, [1, 5, 5]) == :b                       # an effect as a vector
        @test quantifier(ε, x -> q[x]) == 5
        @test select(argmin_selection([:a, :b, :c]), x -> q[x]) == :a
        all_best = argmax_selection([:a, :b, :c]; monad=PowersetMonad(), ties=:all)
        @test select(all_best, x -> q[x]) == FiniteSubset([:b, :c])
        @test quantifier(all_best, x -> q[x]) == 5
        lottery = FiniteDistribution([:a, :b], [1 // 4, 3 // 4])
        chance = constant_selection([:a, :b, :c], lottery)
        @test select(chance, x -> q[x]) == lottery             # nature ignores the payoffs
        @test quantifier(chance, x -> q[x]) == 4               # the expectation
        worst = constant_selection([:a, :b], FiniteSubset([:a, :b]))
        @test quantifier(worst, x -> q[x]) == 1
        @test_throws ArgumentError argmax_selection([:a]; ties=:random)
        @test_throws ArgumentError argmax_selection([:a]; ties=:all)
        @test_throws ArgumentError argmax_selection(Symbol[])
        @test_throws ArgumentError constant_selection([:a], FiniteDistribution([:z], [1]))
        @test_throws MonadMismatchError argmax_selection([:a]; monad=DistributionMonad(),
                                                         algebra=InfimumAlgebra())
        @test occursin("argmax", sprint(show, ε))
    end

    @testset "product of selection functions" begin
        # the quantifier of the product is the nested quantifier (Lean `quantifier_selProd`)
        for _ in 1:40
            A, B = [:a1, :a2, :a3], [:b1, :b2]
            worth = Dict((a, b) => rand(rng, 0:9) for a in A for b in B)
            q = ab -> worth[ab]
            ε = argmax_selection(A)
            δ = a -> argmax_selection(B)
            prod = selection_product(ε, δ)
            @test quantifier(prod, q) ==
                  quantifier(ε, a -> quantifier(δ(a), b -> worth[(a, b)]))
            @test quantifier(prod, q) == maximum(values(worth))      # both maximise
            @test worth[select(prod, q)] == maximum(values(worth))
            # maximin is a product: argmax over actions, argmin over states
            # (Lean `quantifier_selProd_maximin`)
            maximin = selection_product(argmax_selection(A), argmin_selection(B))
            @test quantifier(maximin, q) ==
                  maximum(minimum(worth[(a, b)] for b in B) for a in A)
            t = PayoffTable(A, B, [worth[(a, b)] for a in A, b in B])
            @test select(maximin, q)[1] ==
                  first_choice(decide(DecisionProblem(t, ScenarioSet(B)), Maximin()))
            # a decision followed by a chance node, in the distribution monad
            law = FiniteDistribution(B, rational_probabilities(rng, 2))
            D = DistributionMonad()
            mixed = selection_product(argmax_selection(A; monad=D),
                                      constant_selection(B, law))
            eu = [sum(probability_of(law, b) * worth[(a, b)] for b in B) for a in A]
            @test quantifier(mixed, q) == maximum(eu)
            play = select(mixed, q)
            @test all(ab -> ab[1] == A[findfirst(==(maximum(eu)), eu)], play.outcomes)
        end
        @test_throws MonadMismatchError selection_product(argmax_selection([:a]),
                                                          argmax_selection([:b];
                                                                           monad=DistributionMonad()))
        @test_throws ArgumentError selection_product(argmax_selection([:a]), _ -> 3)
    end

    @testset "which rules admit backward induction" begin
        for rule in (MaxExpectedUtility(), Maximin(), Maximax(), GammaMaximin(),
                     DecisionRule(UpperExpectation()))
            @test admits_backward_induction(rule)
            @test backward_induction_class(rule) === :flat
            @test admits_backward_induction(rule_selection(rule))
        end
        for rule in (DecisionRule(CVaR(1 // 2)), DecisionRule(Quantile(1 // 2)),
                     DecisionRule(Hurwicz(1 // 2)), DecisionRule(Laplace()),
                     DecisionRule(AlphaMaxmin(1 // 2)))
            @test !admits_backward_induction(rule)
            @test backward_induction_class(rule) === :nested
            @test backward_induction_class(rule_selection(rule)) === :nested
        end
        for rule in (MinimaxRegret(), Satisfice(0), EAdmissible(), Maximal(),
                     IntervalDominance(), ParetoFront())
            @test !admits_backward_induction(rule)
            @test backward_induction_class(rule) === :none
        end
        @test backward_induction_class(rule_selection(MinimaxRegret())) === :none
        @test !admits_backward_induction(rule_selection(EAdmissible()))
        @test admits_backward_induction(Expectation()) &&
              !admits_backward_induction(CVaR(1 // 2))
        @test backward_induction_class(CVaR(1)) === :flat          # CVaR(1) is the mean
    end
end
