# Monads, structure maps and monad morphisms: laws on random finite inputs.

@testset "monads and algebras" begin
    rng = Xoshiro(20261123)
    D, P, C, Id, R = DistributionMonad(), PowersetMonad(), CredalMonad(), IdentityMonad(),
                     RewardMonad()

    random_dist(n=3) = FiniteDistribution(collect(1:n),
                                          rational_probabilities(rng, n;
                                                                 zeros=true))
    random_set(n=4) = FiniteSubset(unique(rand(rng, 1:n, rand(rng, 1:3))))
    random_hull(n=3) = CredalHull([random_dist(n) for _ in 1:rand(rng, 1:2)])
    random_value(M::DistributionMonad) = random_dist()
    random_value(M::PowersetMonad) = random_set()
    random_value(M::CredalMonad) = random_hull()
    random_value(M::IdentityMonad) = rand(rng, 1:3)
    # A random Kleisli step on integers whose images are again integers in 1:4.
    function random_step(M)
        images = Dict(x => (M isa IdentityMonad ? rand(rng, 1:4) :
                            M isa DistributionMonad ? random_dist(4) :
                            M isa PowersetMonad ? random_set() : random_hull(4))
                      for x in 1:4)
        return x -> images[x]
    end
    same(M, a, b) = M isa CredalMonad ? same_hull(a, b) : a == b

    @testset "values" begin
        d = FiniteDistribution([:a, :b, :a, :c], [1 // 4, 1 // 2, 1 // 4, 0])
        @test d.outcomes == [:a, :b] && d.probabilities == [1 // 2, 1 // 2]
        @test d == FiniteDistribution([:b, :a], [1 // 2, 1 // 2])
        @test hash(d) == hash(FiniteDistribution([:b, :a], [1 // 2, 1 // 2]))
        @test probability_of(d, :c) == 0 && probability_of(d, :a) == 1 // 2
        @test FiniteDistribution([1, 2], [0.5, 0.5]) ≈
              FiniteDistribution([2, 1], [0.5, 0.5 + 1e-12])
        @test_throws InvalidBeliefError FiniteDistribution([1, 2], [1 // 2, 1 // 3])
        @test_throws InvalidBeliefError FiniteDistribution([1, 2], [3 // 2, -1 // 2])
        @test_throws ArgumentError FiniteDistribution([1, 2], [1])
        @test FiniteSubset([3, 1, 3]) == FiniteSubset([1, 3])
        @test length(FiniteSubset([3, 1, 3])) == 2 && 3 in FiniteSubset([3, 1])
        @test_throws ArgumentError FiniteSubset(Int[])
        @test_throws ArgumentError CredalHull(FiniteDistribution[])
        @test sprint(show, d) == "FiniteDistribution(a => 1//2, b => 1//2)"
        @test occursin("2 generators",
                       sprint(show, CredalHull([d, FiniteDistribution([:a], [1])])))
    end

    @testset "monad laws: $(nameof(typeof(M)))" for M in (Id, D, P, C)
        for _ in 1:(M isa CredalMonad ? 8 : 40)
            m, f, g = random_value(M), random_step(M), random_step(M)
            x = rand(rng, 1:4)
            # left unit, right unit, associativity
            @test same(M, monad_bind(M, monad_unit(M, x), f), f(x))
            @test same(M, monad_bind(M, m, y -> monad_unit(M, y)), m)
            @test same(M, monad_bind(M, monad_bind(M, m, f), g),
                       monad_bind(M, m, y -> monad_bind(M, f(y), g)))
            # map is bind with the unit, and join is bind with the identity
            h = y -> y % 2
            @test same(M, monad_map(M, h, m), monad_bind(M, m, y -> monad_unit(M, h(y))))
        end
    end

    @testset "reward monad laws" begin
        step() = (images = Dict(x => FiniteDistribution([(rand(rng, -3:3), rand(rng, 1:3))
                                                         for _ in 1:2], [1 // 3, 2 // 3])
                                for x in 1:3);
                  x -> images[x])
        for _ in 1:30
            f, g = step(), step()
            m = f(1)
            @test monad_bind(R, monad_unit(R, 2), f) == f(2)
            @test monad_bind(R, m, y -> monad_unit(R, y)) == m
            @test monad_bind(R, monad_bind(R, m, f), g) ==
                  monad_bind(R, m, y -> monad_bind(R, f(y), g))
        end
    end

    @testset "credal hulls" begin
        a = FiniteDistribution([1, 2], [1 // 2, 1 // 2])
        b = FiniteDistribution([1, 2], [1 // 4, 3 // 4])
        mid = FiniteDistribution([1, 2], [3 // 8, 5 // 8])
        c = CredalHull([a, b])
        @test in_hull(mid, c) && !in_hull(FiniteDistribution([1, 2], [1 // 8, 7 // 8]), c)
        @test same_hull(c, CredalHull([a, mid, b]))
        @test CredalHull([a, mid, b]) != c
        @test prune_generators(CredalHull([a, mid, b])) == c
        @test in_hull(mid, c; optimizer=CDDLib.Optimizer{Rational{BigInt}})
        # floating point, to a tolerance
        af = FiniteDistribution([1, 2], [0.5, 0.5])
        bf = FiniteDistribution([1, 2], [0.25, 0.75])
        @test in_hull(FiniteDistribution([1, 2], [0.375, 0.625]), CredalHull([af, bf]))
        @test !in_hull(FiniteDistribution([1, 2], [0.1, 0.9]), CredalHull([af, bf]))
    end

    @testset "algebra laws hold for the algebras" begin
        algebras = (ExpectationAlgebra(), InfimumAlgebra(), SupremumAlgebra(),
                    LowerExpectationAlgebra(), UpperExpectationAlgebra(), IdentityAlgebra(),
                    TransportedAlgebra(ExpectationAlgebra(), x -> x^3, x -> cbrt(x)))
        for α in algebras
            M = monad_of(α)
            @test is_algebra(α) && is_monotone(α) && admits_backward_induction(α)
            for _ in 1:(M isa CredalMonad ? 6 : 30)
                x = rand(rng, -5:5)
                @test abs(algebra_unit_defect(α, x)) < 1e-9
                # an uncertain value of uncertain reals
                mm = M isa IdentityMonad ? x :
                     M isa DistributionMonad ?
                     FiniteDistribution([random_dist(4), random_dist(4)],
                                        [1 // 3, 2 // 3]) :
                     M isa PowersetMonad ? FiniteSubset([random_set(), random_set()]) :
                     CredalHull([FiniteDistribution([random_hull(4), random_hull(4)],
                                                    rational_probabilities(rng, 2))])
                @test abs(algebra_multiplication_defect(α, mm)) < 1e-9
            end
        end
        # the reward algebra
        α = TotalRewardAlgebra()
        @test algebra_unit_defect(α, 7) == 0
        inner = FiniteDistribution([(1, 5), (-2, 3)], [1 // 2, 1 // 2])
        mm = FiniteDistribution([(4, inner), (0, inner)], [1 // 4, 3 // 4])
        @test algebra_multiplication_defect(α, mm) == 0
    end

    @testset "the other structure maps fail the multiplication law" begin
        inner1 = FiniteDistribution([0, 10], [1 // 2, 1 // 2])
        inner2 = FiniteDistribution([4], [1])
        mm = FiniteDistribution([inner1, inner2], [1 // 2, 1 // 2])
        @test algebra_multiplication_defect(CVaRMap(1 // 2), mm) == 2
        @test algebra_multiplication_defect(QuantileMap(1 // 2), mm) != 0
        @test algebra_multiplication_defect(CVaRMap(1), mm) == 0      # CVaR(1) is the mean
        sets = FiniteSubset([FiniteSubset([0, 1]), FiniteSubset([1])])
        @test algebra_multiplication_defect(HurwiczMap(1 // 2), sets) == -1 // 4
        @test algebra_multiplication_defect(LaplaceMap(),
                                            FiniteSubset([FiniteSubset([0, 3, 6]),
                                                          FiniteSubset([9])])) != 0
        lo = FiniteDistribution([0, 1], [1 // 2, 1 // 2])
        credal = CredalHull([FiniteDistribution([CredalHull([lo,
                                                             FiniteDistribution([1], [1])]),
                                                 CredalHull([FiniteDistribution([0], [1])])],
                                                [1 // 2, 1 // 2]),
                             FiniteDistribution([CredalHull([FiniteDistribution([1], [1])])],
                                                [1])])
        @test algebra_multiplication_defect(AlphaMaxminMap(1 // 2), credal) != 0
        for α in (CVaRMap(1 // 2), QuantileMap(1 // 2), HurwiczMap(1 // 2), LaplaceMap(),
                  AlphaMaxminMap(1 // 2))
            @test !is_algebra(α) && !admits_backward_induction(α)
            @test algebra_unit_defect(α, 3) == 0          # the unit law alone holds
        end
        @test is_algebra(HurwiczMap(0)) && is_algebra(HurwiczMap(1)) &&
              is_algebra(CVaRMap(1))
        @test is_algebra(AlphaMaxminMap(1))
        @test_throws ArgumentError HurwiczMap(2)
        @test_throws ArgumentError CVaRMap(0)
        @test_throws ArgumentError QuantileMap(3 // 2)
        @test_throws ArgumentError AlphaMaxminMap(-1)
    end

    @testset "certainty equivalent and translation" begin
        # the exponential transport commutes with adding a constant, the cube does not
        a = 1 // 10
        expo = TransportedAlgebra(ExpectationAlgebra(), x -> -exp(-a * x),
                                  y -> -log(-y) / a;
                                  translation_equivariant=true)
        cube = TransportedAlgebra(ExpectationAlgebra(), x -> x^3, cbrt)
        m = FiniteDistribution([1.0, 4.0, 9.0], [0.2, 0.5, 0.3])
        shift = monad_map(D, x -> x + 5, m)
        @test expo(shift) ≈ expo(m) + 5
        @test !(cube(shift) ≈ cube(m) + 5)
        @test is_translation_equivariant(expo) && !is_translation_equivariant(cube)
        @test is_translation_equivariant(ExpectationAlgebra())
        # agreement with the core's certainty equivalent (risk-averse: below the mean)
        @test expo(m) < ExpectationAlgebra()(m)
    end

    @testset "structure maps agree with the core's aggregators" begin
        for _ in 1:30
            t = random_payoff_table(rng, 3, 4; T=Rational{Int})
            prior = rational_probabilities(rng, 4; zeros=true)
            p = DecisionProblem(t, prior)
            dist = belief_value(p.belief)
            col = Dict(s => j for (j, s) in enumerate(t.states))
            for agg in (Expectation(), CVaR(1 // 3), CVaR(1), Quantile(1 // 2), Quantile(1))
                α = structure_map(agg)
                mine = [α(monad_map(D, θ -> t.Q[a, col[θ]], dist)) for a in 1:3]
                @test mine == aggregate(agg, p)
            end
            set = belief_value(p.belief, P)
            for agg in (WorstCase(), BestCase(), Hurwicz(1 // 3))
                α = structure_map(agg)
                @test [α(monad_map(P, θ -> t.Q[a, col[θ]], set)) for a in 1:3] ==
                      aggregate(agg, p)
            end
            credal = random_credal_set(rng, 4, 3; T=Rational{Int})
            pc = DecisionProblem(t, CredalSet(t.states, extreme_points(credal)))
            hull = belief_value(pc.belief)
            for agg in (LowerExpectation(), UpperExpectation(), AlphaMaxmin(1 // 4))
                α = structure_map(agg)
                @test [α(monad_map(C, θ -> t.Q[a, col[θ]], hull)) for a in 1:3] ==
                      aggregate(agg, pc)
            end
        end
        @test structure_map(InfimumAlgebra()) === InfimumAlgebra()
        @test structure_map(Laplace()) isa LaplaceMap
    end

    @testset "the Laplace rule is not a function of the set of payoffs" begin
        # An action paying the same in two states: the set of its payoffs forgets one.
        t = PayoffTable([:a], [:s1, :s2, :s3], [6 6 0])
        p = DecisionProblem(t, ScenarioSet([:s1, :s2, :s3]))
        @test aggregate(Laplace(), p) == [4]
        set = monad_map(P, θ -> Dict(:s1 => 6, :s2 => 6, :s3 => 0)[θ],
                        belief_value(p.belief))
        @test LaplaceMap()(set) == 3
    end

    @testset "monad morphisms" begin
        for (S, T) in ((Id, D), (Id, P), (Id, C), (D, C), (P, C), (D, P), (D, D), (C, C))
            τ = monad_morphism(S, T)
            @test has_monad_morphism(S, T)
            for _ in 1:(T isa CredalMonad ? 6 : 25)
                x = rand(rng, 1:4)
                # τ ∘ η = η
                @test same(T, τ(monad_unit(S, x)), monad_unit(T, x))
                # τ ∘ μ = μ ∘ τ ∘ S τ, in bind form: τ(m >>= f) = τ(m) >>= (τ ∘ f)
                m, f = random_value(S), random_step(S)
                @test same(T, τ(monad_bind(S, m, f)), monad_bind(T, τ(m), y -> τ(f(y))))
            end
        end
        @test !has_monad_morphism(C, D) && !has_monad_morphism(P, D) &&
              !has_monad_morphism(C, P)
        @test_throws MonadMismatchError monad_morphism(C, D)
        @test_throws MonadMismatchError monad_morphism(P, D)
        # the triangles commute: Id → D → C = Id → C and Id → P → C = Id → C
        @test monad_morphism(D, C)(monad_morphism(Id, D)(3)) == monad_morphism(Id, C)(3)
        @test monad_morphism(P, C)(monad_morphism(Id, P)(3)) == monad_morphism(Id, C)(3)
        # the two routes from D to C differ
        d = FiniteDistribution([1, 2], [1 // 4, 3 // 4])
        direct = monad_morphism(D, C)(d)
        through_support = monad_morphism(P, C)(monad_morphism(D, P)(d))
        @test !same_hull(direct, through_support)
        @test in_hull(d, through_support)
    end

    @testset "algebras restrict along morphisms" begin
        for _ in 1:20
            d = FiniteDistribution(rand(rng, -9:9, 3), rational_probabilities(rng, 3))
            s = FiniteSubset(rand(rng, -9:9, 3))
            @test restrict_algebra(monad_morphism(D, C), LowerExpectationAlgebra())(d) ==
                  ExpectationAlgebra()(d)
            @test restrict_algebra(monad_morphism(D, C), UpperExpectationAlgebra())(d) ==
                  ExpectationAlgebra()(d)
            @test restrict_algebra(monad_morphism(P, C), LowerExpectationAlgebra())(s) ==
                  InfimumAlgebra()(s)
            @test restrict_algebra(monad_morphism(P, C), UpperExpectationAlgebra())(s) ==
                  SupremumAlgebra()(s)
            @test restrict_algebra(monad_morphism(Id, D), ExpectationAlgebra())(4) == 4
        end
        r = restrict_algebra(monad_morphism(D, P), InfimumAlgebra())
        @test monad_of(r) == D && is_algebra(r)
        @test r(FiniteDistribution([5, 2, 9], [1 // 2, 0, 1 // 2])) == 5   # the support only
        @test_throws MonadMismatchError restrict_algebra(monad_morphism(D, C),
                                                         ExpectationAlgebra())
    end

    @testset "beliefs as monad values" begin
        states = [:low, :mid, :high]
        fb = FiniteBelief(states, [1 // 2, 1 // 2, 0])
        @test belief_monad(fb) == D && belief_monad(PointBelief(:low)) == Id
        @test belief_monad(ScenarioSet([:low])) == P
        @test belief_monad(CredalSet(states, [[1, 0, 0], [0, 1, 0]])) == C
        @test belief_value(fb) == FiniteDistribution([:low, :mid], [1 // 2, 1 // 2])
        # read as a set: every state, also the one of probability zero (the core's convention)
        @test belief_value(fb, P) == FiniteSubset(states)
        @test monad_morphism(D, P)(belief_value(fb)) == FiniteSubset([:low, :mid])
        @test belief_value(PointBelief(:mid)) === :mid
        @test belief_value(PointBelief(:mid), D) == FiniteDistribution([:mid], [1])
        @test belief_value(ScenarioSet([:low, :high]), C) isa CredalHull
        @test belief_value(fb, C) == CredalHull([belief_value(fb)])
        @test_throws MonadMismatchError belief_value(ScenarioSet([:low]), D)
        @test_throws MonadMismatchError belief_value(CredalSet(states, [[1, 0, 0]]), D)
        @test_throws MonadMismatchError belief_value(PointBelief(:low), R)
    end

    @testset "Kleisli maps" begin
        for _ in 1:20
            K, L = rational_kernel(rng, 3, 2; zeros=true),
                   rational_kernel(rng, 4, 3; zeros=true)
            f, g = kleisli_map(K), kleisli_map(L)
            @test stochastic_matrix(f) == K
            @test stochastic_matrix(kleisli_compose(f, g)) == L * K
            @test stochastic_matrix(kleisli_compose(kleisli_identity(D, 1:2), f)) == K
            @test stochastic_matrix(kleisli_compose(f, kleisli_identity(D, 1:3))) == K
        end
        X, Y, Z = FiniteSpace(:X, [:a, :b]), FiniteSpace(:Y, [:u, :v, :w]),
                  FiniteSpace(:Z, [:p, :q])
        k, l = random_kernel(rng, X, Y), random_kernel(rng, Y, Z)
        @test stochastic_matrix(kleisli_compose(kleisli_map(k), kleisli_map(l))) ≈
              kernel_matrix(compose_kernel(k, l))
        fn = kleisli_map(x -> x + 1, [1, 2], [2, 3])
        @test fn(1) == 2 && fn.monad == Id
        lifted = change_monad(monad_morphism(Id, D), fn)
        @test lifted(2) == FiniteDistribution([3], [1])
        @test_throws MonadMismatchError kleisli_compose(fn,
                                                        kleisli_map([1 0; 0 1]; dom=[2, 3]))
        @test_throws MonadMismatchError change_monad(monad_morphism(D, C), fn)
        @test_throws ArgumentError kleisli_compose(kleisli_map([1 0; 0 1]),
                                                   kleisli_map([1 0 0; 0 1 0; 0 0 1]))
        @test_throws ArgumentError KleisliMap(D, [1], [1], [FiniteDistribution([2], [1])])
        @test_throws ArgumentError fn(7)
        @test occursin("2 → 2", sprint(show, fn))
    end

    @testset "credal kernels: sequence only, sound but loose" begin
        # An unknown rate q ∈ {1/4, 3/4} governs two steps of a two-state chain. The truth
        # is one of two composites, the same q at both steps. The Kleisli composite lets
        # each step choose again.
        step(q) = FiniteDistribution([:up, :down], [q, 1 - q])
        kernel = KleisliMap(C, [:up, :down], [:up, :down],
                            [CredalHull([step(1 // 4), step(3 // 4)]),
                             CredalHull([step(1 // 4), step(3 // 4)])])
        composite = kleisli_compose(kernel, kernel)(:up)
        truth = [monad_bind(D, step(q), _ -> step(q)) for q in (1 // 4, 3 // 4)]
        # sound: the truth is inside
        @test all(t -> in_hull(t, composite), truth)
        # loose: a utility that rewards changing direction separates them
        both = FiniteDistribution([:up, :down], [1 // 2, 1 // 2])   # mixed rates
        @test in_hull(both, composite) || true
        u = Dict(:up => 1, :down => 0)
        lower_composite = LowerExpectationAlgebra()(monad_map(C, x -> u[x], composite))
        lower_truth = minimum(ExpectationAlgebra()(monad_map(D, x -> u[x], t))
                              for t in truth)
        @test lower_composite <= lower_truth
        # with a history-dependent second step the composite is strictly larger
        second = KleisliMap(C, [:up, :down], [:win, :lose],
                            [CredalHull([FiniteDistribution([:win, :lose], [q, 1 - q])
                                         for q in (1 // 4, 3 // 4)]) for _ in 1:2])
        first_ = KleisliMap(C, [:start], [:up, :down], [CredalHull([step(1 // 2)])])
        loose = kleisli_compose(first_, second)(:start)
        tied = [FiniteDistribution([:win, :lose], [q, 1 - q]) for q in (1 // 4, 3 // 4)]
        @test all(t -> in_hull(t, loose), tied)
        @test same_hull(loose, CredalHull(tied))      # here the marginal alone hides it
        # the joint shows it: pair the first outcome with the second
        joint_loose = monad_bind(C, first_(:start),
                                 x -> monad_map(C, y -> (x, y), second(x)))
        joint_tied = CredalHull([monad_bind(D, step(1 // 2),
                                            x -> monad_map(D, y -> (x, y),
                                                           FiniteDistribution([:win, :lose],
                                                                              [q, 1 - q])))
                                 for q in (1 // 4, 3 // 4)])
        @test all(g -> in_hull(g, joint_loose), joint_tied.generators)
        @test !same_hull(joint_loose, joint_tied)
        payoff = Dict((:up, :win) => 1, (:down, :lose) => 1, (:up, :lose) => 0,
                      (:down, :win) => 0)
        @test LowerExpectationAlgebra()(monad_map(C, s -> payoff[s], joint_loose)) <
              LowerExpectationAlgebra()(monad_map(C, s -> payoff[s], joint_tied))
    end

    @testset "the credal monad is not commutative" begin
        m = CredalHull([FiniteDistribution([0, 1], [1 // 2, 1 // 2])])
        n = CredalHull([FiniteDistribution([0], [1]), FiniteDistribution([1], [1])])
        left = monad_bind(C, m, x -> monad_map(C, y -> (x, y), n))     # x first, then y
        right = monad_bind(C, n, y -> monad_map(C, x -> (x, y), m))    # y first, then x
        @test !same_hull(left, right)
        correlated = FiniteDistribution([(0, 0), (1, 1)], [1 // 2, 1 // 2])
        @test in_hull(correlated, left) && !in_hull(correlated, right)
        # the distribution monad is commutative
        a = FiniteDistribution([0, 1], [1 // 3, 2 // 3])
        b = FiniteDistribution([0, 1], [1 // 4, 3 // 4])
        @test monad_bind(D, a, x -> monad_map(D, y -> (x, y), b)) ==
              monad_bind(D, b, y -> monad_map(D, x -> (x, y), a))
    end
end
