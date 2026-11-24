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
end
