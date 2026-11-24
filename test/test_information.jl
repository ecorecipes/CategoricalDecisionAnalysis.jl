# Information preorders, experiments as distributions over posteriors, and the regret
# transform under coarsening.

@testset "information" begin
    rng = Xoshiro(20261128)
    random_problem(m=3, n=4) = DecisionProblem(random_payoff_table(rng, m, n;
                                                                   T=Rational{Int}),
                                               rational_probabilities(rng, n; zeros=true))

    @testset "garbling is a preorder and value is monotone on it" begin
        for _ in 1:15
            e = Experiment(rational_kernel(rng, 3, 4; zeros=true))
            G, H = rational_kernel(rng, 3, 3), rational_kernel(rng, 2, 3)
            e1, e2 = garble(e, G), garble(garble(e, G), H)
            @test is_garbling(e, e)                               # reflexive
            @test is_garbling(e1, e) && is_garbling(e2, e1)
            @test is_garbling(e2, e)                              # transitive
            for _ in 1:4
                p = random_problem()
                @test information_value(p, e2) <= information_value(p, e1) <=
                      information_value(p, e)
                @test information_value(p, e) == value_with_information(p, e)
            end
        end
        # not antisymmetric: a relabelling is a garbling both ways and a different experiment
        e = Experiment([4//5 1//5; 1//5 4//5])
        flipped = garble(e, [0 1; 1 0])
        @test is_garbling(e, flipped) && is_garbling(flipped, e) && e != flipped
        # incomparable experiments exist
        a = Experiment([1 0 0; 0 1 1])
        b = Experiment([1 1 0; 0 0 1])
        @test !is_garbling(a, b) && !is_garbling(b, a)
    end

    @testset "refinement is a preorder and value is monotone on it" begin
        fine, mid, coarse = [:a, :b, :c, :d], [:x, :x, :y, :z], [:u, :u, :v, :v]
        bottom = [:all, :all, :all, :all]
        @test refines(fine, mid) && refines(mid, coarse) && refines(fine, coarse)
        @test refines(coarse, bottom) && refines(mid, mid)
        @test !refines(coarse, mid) && !refines([:p, :q, :p, :q], coarse)
        @test_throws ArgumentError refines([:a], [:a, :b])
        for _ in 1:25
            p = random_problem()
            v = [information_value(p, q) for q in (bottom, coarse, mid, fine)]
            @test issorted(v)
            @test v[1] == act_now_value(p)
            @test v[4] == act_now_value(p) + evpi(p)
            for q in (coarse, mid, fine)
                e = partition_experiment(q; states=p.payoff.states)
                # EVPPI of a partition = EVSI of the deterministic experiment
                @test evppi(p, q) == evsi(p, e)
                @test information_value(p, q) - act_now_value(p) == evppi(p, q)
            end
            # refinement embeds in garbling (Lean `Labelling.toExperiment_monotone`)
            @test is_garbling(partition_experiment(coarse), partition_experiment(mid))
            @test is_garbling(partition_experiment(mid), partition_experiment(fine))
            @test !is_garbling(partition_experiment(mid), partition_experiment(coarse))
        end
        @test partition_experiment([1, 1, 2]).signals == [:cell1, :cell2]
        @test partition_experiment([:a, :a, :b]).likelihood == [1 1 0; 0 0 1]
    end

    @testset "an experiment as a distribution over posteriors" begin
        for _ in 1:40
            p = random_problem()
            e = Experiment(rational_kernel(rng, 3, 4; zeros=true))
            μ = posterior_distribution(p.belief, e)
            @test posterior_mean(μ) == p.belief.probabilities       # averages to the prior
            @test value_at_posteriors(p, μ) == value_with_information(p, e)
            # relabelling or duplicating signals does not change the distribution
            doubled = Experiment(vcat(e.likelihood .// 2, e.likelihood .// 2))
            @test posterior_distribution(p.belief, doubled) == μ
            # a garbling is below in the convex order: every convex function of the
            # posterior has a smaller mean. Convex functions: values of random problems.
            g = garble(e, rational_kernel(rng, 2, 3))
            ν = posterior_distribution(p.belief, g)
            for _ in 1:3
                other = DecisionProblem(random_payoff_table(rng, 3, 4; T=Rational{Int}),
                                        p.belief)
                @test value_at_posteriors(other, ν) <= value_at_posteriors(other, μ)
            end
            # the point mass at the prior is the bottom: no information
            none = posterior_distribution(p.belief, Experiment(ones(Int, 1, 4)))
            @test value_at_posteriors(p, none) == act_now_value(p)
            pp = posterior_payoff(p, e)
            @test sum(pp.signals.probabilities) == 1
            @test size(pp.payoff, 1) == 3
        end
        @test posterior_distribution([1 // 2, 1 // 2], Experiment([1 0; 0 1])) ==
              FiniteDistribution([[1 // 1, 0 // 1], [0 // 1, 1 // 1]], [1 // 2, 1 // 2])
        credal = DecisionProblem(PayoffTable([1 0; 0 1]), CredalSet([[1, 0], [0, 1]]))
        @test_throws BeliefFormError posterior_payoff(credal, Experiment([1 0; 0 1]))
    end

    @testset "deficiency: value is Lipschitz, and the enrichment" begin
        for _ in 1:8
            e = Experiment(rational_kernel(rng, 2, 3; zeros=true))
            f = Experiment(rational_kernel(rng, 2, 3; zeros=true))
            g = Experiment(rational_kernel(rng, 2, 3; zeros=true))
            for _ in 1:3
                p = random_problem(3, 3)
                @test information_value(p, f) - information_value(p, e) <=
                      value_gap_bound(p, e, f)
                @test abs(information_value(p, f) - information_value(p, e)) <=
                      largest_regret(p) * information_distance(e, f)
            end
            @test deficiency(e, e) == 0 && information_distance(e, e) == 0
            # the triangle inequality of the Lawvere metric
            @test deficiency(e, g) <= deficiency(e, f) + deficiency(f, g)
            @test information_distance(e, f) == information_distance(f, e)
            # deficiency zero is garbling
            @test (deficiency(e, f) == 0) == is_garbling(f, e)
        end
    end

    @testset "regret under coarsening (C6)" begin
        partitions = ([:a, :a, :b, :b], [:a, :b, :b, :b], [:all, :all, :all, :all],
                      [:a, :b, :c, :d], [1, 2, 1, 2])
        for _ in 1:40, partition in partitions
            p = random_problem()
            r = regret_coarsening(p, partition)
            Q, prior = p.payoff.Q, p.belief.probabilities
            cells = unique(partition)
            # written out from the definition
            coarse = [sum(prior[θ] * Q[a, θ] for θ in 1:4 if partition[θ] == c;
                          init=0 // 1)
                      for a in 1:3, c in cells]
            R = regret_table(p)
            @test r.coarse_payoff == coarse
            @test r.coarse_regret == maximum(coarse; dims=1) .- coarse
            @test r.coarsened_regret ==
                  [sum(prior[θ] * R[a, θ] for θ in 1:4 if partition[θ] == c; init=0 // 1)
                   for a in 1:3, c in cells]
            # lax, with the same gap for every action
            @test all(r.coarse_regret .<= r.coarsened_regret)
            @test all(r.coarsened_regret .- r.coarse_regret .== permutedims(r.gap))
            @test all(>=(0), r.gap)
            # the gaps add up to what is left to learn
            @test sum(r.gap) == evpi(p) - evppi(p, partition)
            # in terms of expected regret: fine minus coarse, the same for every action
            @test vec(sum(r.coarsened_regret; dims=2)) == expected_regret(p)
            @test all(==(evpi(p) - evppi(p, partition)),
                      expected_regret(p) .- vec(sum(r.coarse_regret; dims=2)))
            @test r.mass == [sum(prior[θ] for θ in 1:4 if partition[θ] == c) for c in cells]
            # equality exactly when a common best action on every cell
            @test coarsening_is_lossless(p, partition) == all(iszero, r.gap)
            @test coarsening_is_lossless(p, partition) ==
                  (evppi(p, partition) == evpi(p))
        end
        p = DecisionProblem(PayoffTable([0 -10 -60 -150; -20 -20 -25 -90]),
                            [1 // 2, 3 // 10, 3 // 20, 1 // 20])
        @test regret_coarsening(p, [:mild, :mild, :severe, :severe]).gap == [0, 0]
        @test coarsening_is_lossless(p, [:mild, :mild, :severe, :severe])
        @test !coarsening_is_lossless(p, [:all, :all, :all, :all])
        @test sum(regret_coarsening(p, [:all, :all, :all, :all]).gap) == evpi(p)
        # a cell of probability zero is a column of zeros
        z = DecisionProblem(PayoffTable([1 0 5; 0 1 0]), [1 // 2, 1 // 2, 0])
        rz = regret_coarsening(z, [:a, :a, :b])
        @test rz.mass == [1, 0] && all(iszero, rz.coarse_payoff[:, 2]) && rz.gap[2] == 0
        @test coarsening_is_lossless(z, [:a, :b, :b])      # the zero state is ignored
        point = DecisionProblem(PayoffTable([1 0; 0 1]), PointBelief(:s2))
        @test regret_coarsening(point, [:a, :a]).gap == [0]
        @test occursin("total gap", sprint(show, rz))
        scen = DecisionProblem(PayoffTable([1 0; 0 1]), ScenarioSet([:s1, :s2]))
        @test_throws BeliefFormError regret_coarsening(scen, [:a, :a])
        @test_throws BeliefFormError coarsening_is_lossless(scen, [:a, :a])
        @test_throws ArgumentError regret_coarsening(p, [:a, :b])
        @test_throws ArgumentError coarsening_is_lossless(p, [:a, :b])
    end
end
