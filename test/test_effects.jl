# Effects and value pullback: functoriality on random kernels for every monad, the
# fast path against the generic one, agreement with RewardKernel, and the interchange
# gap against the core's values of information.

@testset "effects and value pullback" begin
    rng = Xoshiro(20261124)
    D, P, C, Id, R = DistributionMonad(), PowersetMonad(), CredalMonad(), IdentityMonad(),
                     RewardMonad()

    function random_kleisli(M, nx, ny)
        dom, codom = collect(1:nx), collect(1:ny)
        function image()
            return M isa IdentityMonad ? rand(rng, codom) :
                   M isa DistributionMonad ?
                   FiniteDistribution(codom, rational_probabilities(rng, ny; zeros=true)) :
                   M isa PowersetMonad ?
                   FiniteSubset(unique(rand(rng, codom, rand(rng, 1:ny)))) :
                   M isa CredalMonad ?
                   CredalHull([FiniteDistribution(codom,
                                                  rational_probabilities(rng, ny;
                                                                         zeros=true))
                               for _ in 1:rand(rng, 1:2)]) :
                   FiniteDistribution([(rand(rng, -3:3), rand(rng, codom)) for _ in 1:2],
                                      rational_probabilities(rng, 2))
        end
        return KleisliMap(M, dom, codom, [image() for _ in dom])
    end

    @testset "functor laws: $(nameof(typeof(α)))" for α in (IdentityAlgebra(),
                                                            ExpectationAlgebra(),
                                                            InfimumAlgebra(),
                                                            SupremumAlgebra(),
                                                            LowerExpectationAlgebra(),
                                                            UpperExpectationAlgebra(),
                                                            TotalRewardAlgebra())
        M = monad_of(α)
        for _ in 1:(M isa CredalMonad ? 15 : 40)
            f, g = random_kleisli(M, 3, 3), random_kleisli(M, 3, 2)
            u = rand(rng, -9:9, 2) .// 1
            # identity
            @test value_pullback(kleisli_identity(M, [1, 2]), u, α) == u
            # contravariant composition: (f ; g)* u = f* (g* u)
            @test value_pullback(kleisli_compose(f, g), u, α) ==
                  value_pullback(f, value_pullback(g, u, α), α)
        end
    end

    @testset "functoriality fails for a structure map that is not an algebra" begin
        f = kleisli_map([1//2 0; 1//2 1]; dom=[:x, :y], codom=[:u, :v])
        g = kleisli_map([1//2 0; 1//2 0; 0 1]; dom=[:u, :v], codom=[0, 10, 4])
        u = [0, 10, 4]
        α = CVaRMap(1 // 2)
        @test value_pullback(kleisli_compose(f, g), u, α) !=
              value_pullback(f, value_pullback(g, u, α), α)
        @test value_pullback(kleisli_compose(f, g), u, ExpectationAlgebra()) ==
              value_pullback(f, value_pullback(g, u, ExpectationAlgebra()),
                             ExpectationAlgebra())
    end

    @testset "the matrix fast path against the generic pullback" begin
        for _ in 1:40
            K = rational_kernel(rng, 4, 3; zeros=true)
            u = rand(rng, -20:20, 4)
            @test value_pullback(K, u) == value_pullback(kleisli_map(K), u)
            # written out from the definition
            @test value_pullback(K, u) == [sum(K[y, x] * u[y] for y in 1:4) for x in 1:3]
            # a function for the effect
            @test value_pullback(kleisli_map(K), y -> u[y]) == value_pullback(K, u)
        end
        X, Y = FiniteSpace(:X, [:a, :b]), FiniteSpace(:Y, [:u, :v, :w])
        k = random_kernel(rng, X, Y)
        u = [1.0, -2.0, 5.0]
        @test value_pullback(k, u) ≈ value_pullback(kleisli_map(k), u)
        @test_throws ArgumentError value_pullback([1 0; 0 1], [1, 2, 3])
        @test_throws ArgumentError value_pullback(kleisli_map([1 0; 0 1]), [1, 2, 3])
        @test_throws MonadMismatchError value_pullback(kleisli_map([1 0; 0 1]), [1, 2],
                                                       InfimumAlgebra())
    end

    @testset "push the belief forward = pull the utility back" begin
        # Lean `expectedUtility_push`: ⟨K p, u⟩ = ⟨p, Kᵀ u⟩.
        for _ in 1:40
            K = rational_kernel(rng, 4, 3; zeros=true)
            p = rational_probabilities(rng, 3; zeros=true)
            u = rand(rng, -20:20, 4)
            @test sum((K * p) .* u) == sum(p .* value_pullback(K, u))
            # the same through the monad: E(T u (p >>= f)) = E(T (f* u) p)
            f = kleisli_map(K)
            belief = FiniteDistribution(collect(1:3), p)
            pushed = monad_bind(D, belief, f)
            pulled = value_pullback(f, u)
            @test ExpectationAlgebra()(monad_map(D, y -> u[y], pushed)) ==
                  ExpectationAlgebra()(monad_map(D, x -> pulled[x], belief))
        end
    end

    @testset "monotone and constant-preserving for stochastic kernels" begin
        for _ in 1:30
            K = rational_kernel(rng, 4, 3; zeros=true)
            u = rand(rng, -20:20, 4)
            v = u .+ rand(rng, 0:5, 4)
            @test all(value_pullback(K, u) .<= value_pullback(K, v))
            @test value_pullback(K, fill(7, 4)) == fill(7, 3)
        end
        # neither holds for a table that is not a stochastic kernel
        signed = [1 -1; 0 2]
        @test value_pullback(signed, [1, 0])[2] < value_pullback(signed, [0, 0])[2]
        @test value_pullback([1//2 1//2; 1//4 1//4], [3, 3]) != [3, 3]   # sub-stochastic
    end

    @testset "the support is lax: worst case ≤ expectation ≤ best case" begin
        τ = monad_morphism(D, P)
        for _ in 1:40
            f = random_kleisli(D, 3, 4)
            u = rand(rng, -20:20, 4)
            sup = change_monad(τ, f)
            lo = value_pullback(sup, u, InfimumAlgebra())
            mid = value_pullback(f, u, ExpectationAlgebra())
            hi = value_pullback(sup, u, SupremumAlgebra())
            @test all(lo .<= mid) && all(mid .<= hi)
        end
        # the inequality is strict in general
        f = kleisli_map(reshape([1 // 2, 1 // 2], 2, 1))
        @test value_pullback(change_monad(τ, f), [0, 10], InfimumAlgebra()) == [0]
        @test value_pullback(f, [0, 10]) == [5]
    end

    @testset "agreement with RewardKernel of CategoricalInfluenceDiagrams" begin
        X, Y, Z = FiniteSpace(:X, [:a, :b]), FiniteSpace(:Y, [:u, :v, :w]),
                  FiniteSpace(:Z, [:p, :q])
        for _ in 1:20
            # a plain kernel: pullback is the continuation value with zero reward
            k = random_kernel(rng, X, Y)
            u = randn(rng, 3)
            r = RewardKernel(k)
            @test value_pullback(k, u) ≈ continuation_value(r; continuation=u)
            # a kernel with reward
            W = randn(rng, 3, 2)
            rw = RewardKernel(k, W)
            @test value_pullback(rw, u) ≈ continuation_value(rw; continuation=u)
            @test value_pullback(rw, u) ≈ vec(sum(W; dims=1)) .+ kernel_matrix(k)' * u
        end
        # the reward monad maps onto reward kernels, compatibly with composition
        function reward_map(dom, codom)
            return KleisliMap(R, dom, codom,
                              [FiniteDistribution([(rand(rng, -4:4), rand(rng, codom))
                                                   for _ in 1:3],
                                                  rational_probabilities(rng, 3))
                               for _ in dom])
        end
        for _ in 1:20
            f = reward_map([:a, :b], [:u, :v, :w])
            g = reward_map([:u, :v, :w], [:p, :q])
            rf = reward_kernel(f; dom=:X, codom=:Y)
            rg = reward_kernel(g; dom=:Y, codom=:Z)
            composite = reward_kernel(kleisli_compose(f, g); dom=:X, codom=:Z)
            @test composite ≈ CID.compose(rf, rg)
            u = rand(rng, -5:5, 2)
            exact = value_pullback(kleisli_compose(f, g), u, TotalRewardAlgebra())
            @test Float64.(exact) ≈ continuation_value(CID.compose(rf, rg);
                                                       continuation=Float64.(u))
            @test Float64.(exact) ≈ value_pullback(composite, Float64.(u))
        end
    end

    @testset "interchange gap = the values of information" begin
        for _ in 1:40
            t = random_payoff_table(rng, 3, 4; T=Rational{Int})
            prior = rational_probabilities(rng, 4; zeros=true)
            p = DecisionProblem(t, prior)
            e = Experiment(rational_kernel(rng, 3, 4; zeros=true))
            Q, L = t.Q, e.likelihood
            # the Lean form: weights and objectives[i, a]
            @test interchange_gap(prior, transpose(Q)) == evpi(p)
            J = [sum(prior[θ] * L[z, θ] * Q[a, θ] for θ in 1:4) for z in 1:3, a in 1:3]
            @test interchange_gap(ones(Int, 3), J) == evsi(p, e)
            partition = [:c1, :c1, :c2, :c3]
            cells = unique(partition)
            Cm = [sum(prior[θ] * Q[a, θ] for θ in 1:4 if partition[θ] == c; init=0 // 1)
                  for c in cells, a in 1:3]
            @test interchange_gap(ones(Int, 3), Cm) == evppi(p, partition)
            @test interchange_gap(prior, transpose(Q)) >= 0
            # the monadic form
            @test interchange_gap(p) == evpi(p)
            @test interchange_gap(ExpectationAlgebra(), belief_value(p.belief), Q;
                                  states=t.states) == evpi(p)
            pp = posterior_payoff(p, e)
            @test interchange_gap(ExpectationAlgebra(), pp.signals, pp.payoff) == evsi(p, e)
            # convex, concave, affine
            m = belief_value(p.belief)
            @test interchange_gap(ExpectationAlgebra(), m, Q; states=t.states, h=minimum) <=
                  0
            @test interchange_gap(ExpectationAlgebra(), m, Q; states=t.states, h=sum) == 0
            # worst case: the minimax gap; best case: two maxima commute
            scen = DecisionProblem(t, ScenarioSet(t.states))
            @test interchange_gap(scen) ==
                  minimum(maximum(Q; dims=1)) - maximum(minimum(Q; dims=2))
            @test interchange_gap(scen) >= 0
            @test interchange_gap(scen, SupremumAlgebra()) == 0
            @test interchange_gap(DecisionProblem(t, PointBelief(t.states[2]))) == 0
        end
        @test expectation_rewrite(:affine) == :(==)
        @test expectation_rewrite(:convex) == :(<=)
        @test expectation_rewrite(:concave) == :(>=)
        @test_throws ArgumentError expectation_rewrite(:monotone)
        @test_throws ArgumentError interchange_gap([1, 2], [1 2 3])
        @test_throws ArgumentError interchange_gap(ExpectationAlgebra(),
                                                   FiniteDistribution([1], [1]), [1 2];
                                                   states=[1])
    end
end
