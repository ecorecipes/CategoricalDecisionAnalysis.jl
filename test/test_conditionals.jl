# Conditionals: Bayesian inversion through sub-stochastic kernels.

@testset "conditionals" begin
    rng = Xoshiro(20261125)

    @testset "normalisation is total" begin
        @test normalize_mass([1 // 10, 3 // 10]) == (2 // 5, [1 // 4, 3 // 4])
        @test normalize_mass([0 // 1, 0 // 1]) == (0 // 1, [0 // 1, 0 // 1])
        mass, v = normalize_mass([0.2, 0.6])
        @test mass ≈ 0.8 && v ≈ [0.25, 0.75]
        @test normalize_mass([0, 0]) == (0, [0.0, 0.0])
        @test_throws ArgumentError normalize_mass([1, -1])
    end

    @testset "agreement with the core's bayes_invert" begin
        for _ in 1:60
            n, nz = rand(rng, 2:4), rand(rng, 2:4)
            prior = FiniteBelief(rational_probabilities(rng, n; zeros=true))
            L = rational_kernel(rng, nz, n; zeros=true)
            if rand(rng) < 0.5      # a signal that never occurs
                L = vcat(L, zeros(Rational{Int}, 1, n))
                nz += 1
            end
            e = Experiment(L; states=prior.states)
            mine, core = bayesian_inverse(prior, e), bayes_invert(prior, e)
            @test mine.joint == core.joint
            @test mine.evidence == core.marginal
            for z in 1:nz
                if core.posteriors[z] === nothing
                    @test iszero(mine.evidence[z])
                    @test all(iszero, mine.inverse[:, z])     # a value, not an exception
                    @test posterior(mine, z) === nothing
                else
                    @test mine.inverse[:, z] == probabilities(core.posteriors[z])
                    @test posterior(mine, z) == probabilities(core.posteriors[z])
                    @test sum(mine.inverse[:, z]) == 1
                end
            end
            # mass × posterior = joint, also where the mass is zero
            @test mine.inverse .* permutedims(mine.evidence) == permutedims(mine.joint)
        end
    end

    @testset "zero-probability evidence" begin
        inv = bayesian_inverse([3 // 5, 2 // 5], [4//5 1//5; 1//5 4//5; 0 0])
        @test inv.evidence == [14 // 25, 11 // 25, 0]
        @test inv.inverse == [6//7 3//11 0; 1//7 8//11 0]
        @test posterior(inv, 3) === nothing
        @test occursin("1 of probability zero", sprint(show, inv))
        # a state of prior probability zero is no difficulty either
        inv0 = bayesian_inverse([1, 0], [1//2 1; 1//2 0])
        @test inv0.inverse == [1 1; 0 0]
        labelled = bayesian_inverse(FiniteBelief([:lo, :hi], [1 // 2, 1 // 2]),
                                    Experiment([1 0; 0 1]; signals=[:neg, :pos]))
        @test posterior(labelled, :pos) == [0, 1]
        @test_throws ArgumentError posterior(labelled, :maybe)
        @test_throws ArgumentError bayesian_inverse([1 // 2, 1 // 2], [1 0 0; 0 1 1])
        @test_throws ArgumentError bayesian_inverse([3 // 2, -1 // 2], [1 0; 0 1])
        @test_throws LabelMismatchError bayesian_inverse(FiniteBelief([:a, :b],
                                                                      [1 // 2, 1 // 2]),
                                                         Experiment([1 0; 0 1];
                                                                    states=[:x, :y]))
    end

    @testset "inversion of a composite = composite of inversions, at every evidence" begin
        for _ in 1:80
            n, ny, nz = rand(rng, 2:4), rand(rng, 2:4), rand(rng, 2:4)
            p = rational_probabilities(rng, n; zeros=true)
            f = rational_kernel(rng, ny, n; zeros=true)
            g = rational_kernel(rng, nz, ny; zeros=true)
            first_ = bayesian_inverse(p, f)
            second = bayesian_inverse(first_.evidence, g)      # against the pushed prior
            whole = bayesian_inverse(p, g * f)
            # normalised form: every column, also those of probability zero
            @test whole.inverse == inverse_compose(first_, second)
            # joint form, no division: joint_{f;g}[z, θ] = Σ_y g[z, y] · joint_f[y, θ]
            @test whole.joint == g * first_.joint
            # and through the inverse of f: joint_{f;g}[z, θ] = Σ_y joint_g[z, y] inverse_f[θ, y]
            @test whole.joint == second.joint * transpose(first_.inverse)
            @test whole.evidence == second.evidence
        end
        a = bayesian_inverse([1 // 2, 1 // 2], [1 0; 0 1])
        b = bayesian_inverse([1 // 3, 2 // 3], [1 0; 0 1])
        @test_throws ArgumentError inverse_compose(a, b)
        @test_throws ArgumentError inverse_compose(a, bayesian_inverse([1 // 1], [1;;]))
    end

    @testset "FiniteKernel inputs and floating point" begin
        X, Y = FiniteSpace(:X, [:a, :b, :c]), FiniteSpace(:Y, [:u, :v])
        prior = FiniteKernels.state(X, [0.2, 0.3, 0.5])
        k = random_kernel(rng, X, Y)
        inv = bayesian_inverse(prior, k)
        @test inv.evidence ≈ kernel_matrix(k) * [0.2, 0.3, 0.5]
        @test all(≈(1), sum(inv.inverse; dims=1))
        @test_throws FiniteKernels.SpaceMismatchError bayesian_inverse(FiniteKernels.state(Y,
                                                                                           [0.5,
                                                                                            0.5]),
                                                                       k)
        @test_throws ArgumentError bayesian_inverse(k, k)
    end
end
