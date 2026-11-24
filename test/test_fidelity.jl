# Compositional fidelity: the divergence is sub-additive under composition and tensor,
# and the bound read off a diagram holds when an emulator replaces a submodel.

@testset "fidelity" begin
    rng = Xoshiro(20261130)

    @testset "kernel distance" begin
        K = [9//10 1//5; 1//10 4//5]
        K′ = [4//5 1//5; 1//5 4//5]
        @test kernel_distance(K, K′) == 1 // 10
        @test kernel_distance(K, K) == 0
        @test kernel_distance(K, K′) == kernel_distance(K′, K)
        # written out: the largest total variation over the inputs
        for _ in 1:30
            A, B = rational_kernel(rng, 4, 3; zeros=true),
                   rational_kernel(rng, 4, 3; zeros=true)
            @test kernel_distance(A, B) ==
                  maximum(sum(abs.(A[:, x] .- B[:, x])) / 2 for x in 1:3)
            @test 0 <= kernel_distance(A, B) <= 1
        end
        X, Y = FiniteSpace(:X, [:a, :b]), FiniteSpace(:Y, [:u, :v])
        k, l = random_kernel(rng, X, Y), random_kernel(rng, X, Y)
        @test kernel_distance(k, l) ≈ kernel_distance(kernel_matrix(k), kernel_matrix(l))
        @test kernel_distance(kleisli_map(K), kleisli_map(K′)) == 1 // 10
        # arrays with several input axes: the table of a box
        T1 = reshape(reduce(hcat, [rational_probabilities(rng, 3) for _ in 1:6]), 3, 2, 3)
        T2 = reshape(reduce(hcat, [rational_probabilities(rng, 3) for _ in 1:6]), 3, 2, 3)
        @test kernel_distance(T1, T2) ==
              kernel_distance(reshape(T1, 3, 6), reshape(T2, 3, 6))
        @test_throws ArgumentError kernel_distance(K, [1 0 0; 0 1 1])
        @test_throws ArgumentError kernel_distance(K, K′; divergence=:kullback_leibler)
    end

    @testset "sub-additive under composition and tensor: total variation, exactly" begin
        for _ in 1:60
            f, f′ = rational_kernel(rng, 3, 2; zeros=true),
                    rational_kernel(rng, 3, 2; zeros=true)
            g, g′ = rational_kernel(rng, 4, 3; zeros=true),
                    rational_kernel(rng, 4, 3; zeros=true)
            h, h′ = rational_kernel(rng, 2, 4; zeros=true),
                    rational_kernel(rng, 2, 4; zeros=true)
            # composition (diagrammatic f ; g is the matrix product g * f)
            @test kernel_distance(g * f, g′ * f′) <=
                  kernel_distance(f, f′) + kernel_distance(g, g′)
            # a chain: a fold with +
            @test kernel_distance(h * g * f, h′ * g′ * f′) <=
                  kernel_distance(f, f′) + kernel_distance(g, g′) + kernel_distance(h, h′)
            # tensor
            @test kernel_distance(kron(g, f), kron(g′, f′)) <=
                  kernel_distance(f, f′) + kernel_distance(g, g′)
            # data processing: a shared second kernel cannot increase the distance
            @test kernel_distance(g * f, g * f′) <= kernel_distance(f, f′)
            @test kernel_distance(g * f, g′ * f) <= kernel_distance(g, g′)
        end
        # through FiniteKernels' own composition and tensor
        X, Y, Z = FiniteSpace(:X, [:a, :b]), FiniteSpace(:Y, [:u, :v, :w]),
                  FiniteSpace(:Z, [:p, :q])
        for _ in 1:20
            f, f′ = random_kernel(rng, X, Y), random_kernel(rng, X, Y)
            g, g′ = random_kernel(rng, Y, Z), random_kernel(rng, Y, Z)
            bound = kernel_distance(f, f′) + kernel_distance(g, g′)
            @test kernel_distance(compose_kernel(f, g), compose_kernel(f′, g′)) <=
                  bound + 1e-12
            @test kernel_distance(tensor_kernel(f, g), tensor_kernel(f′, g′)) <=
                  bound + 1e-12
        end
    end

    @testset "Jensen-Shannon distance" begin
        @test jensen_shannon_distance([1, 0], [1, 0]) == 0
        @test jensen_shannon_distance([1, 0], [0, 1]) ≈ sqrt(log(2))
        X, Y, Z = FiniteSpace(:X, [:a, :b]), FiniteSpace(:Y, [:u, :v, :w]),
                  FiniteSpace(:Z, [:p, :q])
        js(a, b) = kernel_distance(a, b; divergence=:jensen_shannon)
        for _ in 1:40
            p, q, r = random_belief(rng, 4), random_belief(rng, 4), random_belief(rng, 4)
            pp, qq, rr = probabilities(p), probabilities(q), probabilities(r)
            d = jensen_shannon_distance(pp, qq)
            @test d ≈ jensen_shannon_distance(qq, pp)
            @test d <=
                  jensen_shannon_distance(pp, rr) + jensen_shannon_distance(rr, qq) + 1e-12
            @test total_variation(pp, qq) <= sqrt(2) * d + 1e-12
            f, f′ = random_kernel(rng, X, Y), random_kernel(rng, X, Y)
            g, g′ = random_kernel(rng, Y, Z), random_kernel(rng, Y, Z)
            @test js(compose_kernel(f, g), compose_kernel(f′, g′)) <=
                  js(f, f′) + js(g, g′) + 1e-12
            @test js(tensor_kernel(f, g), tensor_kernel(f′, g′)) <=
                  js(f, f′) + js(g, g′) + 1e-12
        end
        @test_throws ArgumentError jensen_shannon_distance([1, 0], [1, 0, 0])
    end

    @testset "Kullback-Leibler: sub-additive along composition, but not a metric" begin
        # The plan said that KL "does not compose additively". In the supremum form it
        # does (chain rule); what it lacks is symmetry and the triangle inequality.
        kl(p, q) = sum(iszero(a) ? 0.0 : a * log(a / b) for (a, b) in zip(p, q))
        supkl(A, B) = maximum(kl(A[:, x], B[:, x]) for x in axes(A, 2))
        X, Y, Z = FiniteSpace(:X, [:a, :b]), FiniteSpace(:Y, [:u, :v, :w]),
                  FiniteSpace(:Z, [:p, :q])
        for _ in 1:200
            f, f′ = kernel_matrix(random_kernel(rng, X, Y)),
                    kernel_matrix(random_kernel(rng, X, Y))
            g, g′ = kernel_matrix(random_kernel(rng, Y, Z)),
                    kernel_matrix(random_kernel(rng, Y, Z))
            @test supkl(g * f, g′ * f′) <= supkl(f, f′) + supkl(g, g′) + 1e-12
        end
        p, q, r = [0.9, 0.1], [0.5, 0.5], [0.1, 0.9]
        @test kl(p, r) > kl(p, q) + kl(q, r)                 # no triangle inequality
        @test !(kl([0.9, 0.1], [0.5, 0.5]) ≈ kl([0.5, 0.5], [0.9, 0.1]))   # not symmetric
    end

    @testset "the bound read off a diagram: an emulator replaces a submodel" begin
        env = :rain => [:dry, :normal, :wet]
        hab = :habitat => [:poor, :fair, :good]
        act = :action => [:none, :restore]
        pop = :frogs => [:few, :some, :many]
        violations = 0
        for _ in 1:40
            prior = rational_probabilities(rng, 3)
            environment = rational_kernel(rng, 3, 3)                  # rain → habitat
            population = reshape(reduce(hcat,
                                        [rational_probabilities(rng, 3) for _ in 1:6]),
                                 3, 2, 3)                             # [frogs, action, habitat]
            counts = [5, 40, 120]
            function build(E, P)
                return decision_pipeline(belief_box(:climate, env, prior),
                                         channel_box(:environment, env, hab, E),
                                         policy_box(:manager, (), act),
                                         consequence_box(:population, (act, hab), pop, P),
                                         utility_box(:count, pop, counts))
            end
            truth = build(environment, population)
            # emulators: each table perturbed towards another random one
            mix(A, B, w) = (1 - w) .* A .+ w .* B
            E′ = mix(environment, rational_kernel(rng, 3, 3), 1 // 20)
            P′ = mix(population,
                     reshape(reduce(hcat, [rational_probabilities(rng, 3) for _ in 1:6]), 3,
                             2, 3),
                     1 // 10)
            ε_env, ε_pop = kernel_distance(environment, E′), kernel_distance(population,
                                                                             P′)
            emulated = with_error(build(E′, P′), :environment => ε_env,
                                  :population => ε_pop)
            @test box_errors(emulated) == Dict(:environment => ε_env, :population => ε_pop)
            @test total_error(emulated) == ε_env + ε_pop
            @test utility_range(emulated) == 115
            bound = fidelity_bound(emulated)
            @test bound == decision_loss_bound(115, ε_env + ε_pop) ==
                  2 * 115 * (ε_env + ε_pop)
            # decide with the emulated diagram, pay in the true one
            chosen = first_choice(decide(emulated, MaxExpectedUtility()))
            loss = act_now_value(truth) -
                   pipeline_value(truth; policies=(:manager => chosen))
            @test 0 <= loss <= bound
            # every policy's value moves by at most B Σε
            for a in act[2]
                @test abs(pipeline_value(truth; policies=(:manager => a)) -
                          pipeline_value(emulated; policies=(:manager => a))) <= bound / 2
            end
            # replace_box does the same as rebuilding
            swapped = replace_box(replace_box(truth, :environment, E′; error=ε_env),
                                  :population, P′; error=ε_pop)
            @test swapped == emulated && fidelity_bound(swapped) == bound
            # an error on the belief adds as well: 2B(ε₀ + Σεᵢ)
            prior′ = mix(prior, rational_probabilities(rng, 3), 1 // 10)
            ε0 = total_variation(prior, prior′)
            all_wrong = with_error(replace_box(emulated, :climate, prior′), :climate => ε0)
            @test fidelity_bound(all_wrong) == 2 * 115 * (ε0 + ε_env + ε_pop)
            chosen′ = first_choice(decide(all_wrong, MaxExpectedUtility()))
            loss′ = act_now_value(truth) -
                    pipeline_value(truth; policies=(:manager => chosen′))
            @test 0 <= loss′ <= fidelity_bound(all_wrong)
        end
    end

    @testset "what the bound counts" begin
        st = :state => [:a, :b]
        act = :action => [:x, :y]
        p = decision_pipeline(belief_box(:prior, st, [1 // 2, 1 // 2]),
                              channel_box(:unused, st, :noise => [:n1, :n2], [1 0; 0 1];
                                          error=1 // 4),
                              policy_box(:manager, (), act),
                              utility_box(:u, (act, st), [10 0; 4 4]),
                              utility_box(:v, act, [0, 3]))
        # a box that feeds no utility does not count
        @test total_error(p) == 0 && fidelity_bound(p) == 0
        @test box_errors(p) == Dict(:unused => 1 // 4)
        # the range is of the total utility: 10 + 0 down to 0 + 0
        @test utility_range(p) == 10
        @test utility_range(decision_pipeline(belief_box(:prior, st, [1, 0]))) == 0
        q = with_error(p, :prior => 1 // 10)
        @test fidelity_bound(q) == 2
        # an emulator that is not normalised is refused: the bound is not proved for it
        @test_throws PipelineStructureError replace_box(p, :unused, [1//2 0; 1//4 1])
        @test_throws ArgumentError with_error(p, :prior => -1 // 10)
        @test_throws PipelineStructureError with_error(p, :nobody => 1 // 10)
    end
end
