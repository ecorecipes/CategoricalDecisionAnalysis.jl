# Kernel bridges.

using ResilienceCore: ResilienceCore

@testset "kernel bridges" begin
    now_ = :state_now => [:low, :high]
    next = :state_next => [:low, :high]
    columns = [9//10 3//10; 1//10 7//10]          # columns[y, x] = P(y | x)
    k = finite_kernel(columns, now_, next)
    @test kernel_matrix(k) == columns && eltype(k) == Rational{Int}
    @test k.dom == FiniteSpace(:state_now, [:low, :high])
    @test finite_kernel(permutedims(columns), now_, next; orientation=:rows) == k
    @test finite_kernel(columns, now_).codom == k.dom
    # a ResilienceCore Markov kernel is row-stochastic
    m = ResilienceCore.MarkovKernel([0.9 0.1; 0.3 0.7])
    km = finite_kernel(m, now_, next)
    @test kernel_matrix(km) ≈ [0.9 0.3; 0.1 0.7]
    # and back through FiniteKernels' own bridge
    endo = finite_kernel(m, now_, now_)
    @test ResilienceCore.linearise(endo).P ≈ m.P
    @test_throws ArgumentError finite_kernel(columns, now_, next; orientation=:diagonal)
    @test_throws FiniteKernels.KernelNormalizationError finite_kernel(permutedims(columns),
                                                                      now_, next)
    @test_throws FiniteKernels.KernelShapeError finite_kernel(columns, now_,
                                                              :other => [:a, :b, :c])
    # a bridged kernel is a box: two steps of a chain, with a utility at the end
    step1 = channel_box(:step1, now_, next, k.table)
    step2 = consequence_box(:step2, next, :state_after => [:low, :high], k.table)
    chain = decision_pipeline(belief_box(:start, now_, [1, 0]), step1, step2,
                              utility_box(:frogs, :state_after => [:low, :high], [10, 50]))
    @test pipeline_value(chain) == sum((columns * columns * [1, 0]) .* [10, 50])

    # FiniteBelief and Experiment bidirectional bridges + unified prune_generators + invert_kernel parity
    b = FiniteBelief([:low, :high], [3 // 5, 2 // 5])
    kb = finite_kernel(b; name=:state)
    @test eltype(kb) == Rational{Int} && FiniteBelief(kb) == b
    ex = Experiment([4//5 1//5; 1//5 4//5]; signals=[:neg, :pos],
                    states=[:low, :high])
    ke = finite_kernel(ex; state_name=:state, signal_name=:signal)
    @test eltype(ke) == Rational{Int} && Experiment(ke) == ex
    if isdefined(FiniteKernels, :invert_kernel)
        fk_inv = FiniteKernels.invert_kernel(kb, ke)
        cda_inv = bayesian_inverse(kb, ke)
        @test vec(kernel_matrix(fk_inv.evidence)) == cda_inv.evidence
        @test kernel_matrix(fk_inv.inverse) == cda_inv.inverse
    end
    # prune_generators dispatches cleanly on both DecisionAnalysis.CredalSet and CredalHull
    cs = CredalSet([:s1, :s2], [[1 // 1, 0 // 1], [0 // 1, 1 // 1], [1 // 2, 1 // 2]])
    @test length(extreme_points(prune_generators(cs))) == 2
    ch = belief_value(cs, CredalMonad())
    @test length(prune_generators(ch).generators) == 2
end
