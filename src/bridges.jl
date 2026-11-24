# Kernel bridges (component 9 of the plan): model-side stochastic operators as
# FiniteKernels, so that model components can be boxes of a pipeline. Anything that
# needs a model package belongs in an extension of that package, not here.

"""
    finite_kernel(P::AbstractMatrix, input, output=input; orientation=:columns, atol) -> FiniteKernel
    finite_kernel(m::ResilienceCore.MarkovKernel, input, output; atol) -> FiniteKernel

A stochastic matrix as a `FiniteKernel` from the wire `input` to the wire `output`
(each written `:name => labels`, or a `FiniteAxis`).

- With `orientation = :columns` (the default) the matrix is column-stochastic,
  `P[y, x] = P(y | x)`: the convention of FiniteKernels and of the likelihood of an
  `Experiment`.
- With `orientation = :rows` it is row-stochastic, `P[x, y] = P(y | x)`: the
  convention of most Markov-chain and hidden-Markov-model code, and of
  `ResilienceCore.MarkovKernel`, whose method uses it.

The element type is kept, so a rational matrix gives an exact kernel. A matrix that
is not stochastic in the stated orientation throws FiniteKernels'
`KernelNormalizationError`. The table of the kernel (`kernel.table`) is what
[`channel_box`](@ref) and [`consequence_box`](@ref) take.

A transition matrix maps a variable to itself at the next step, and the wires of a
pipeline are named, so the two ends need different names (`:state_t`,
`:state_next`) even when their labels are the same.
"""
function finite_kernel(P::AbstractMatrix{<:Real}, input, output=input;
                       orientation::Symbol=:columns,
                       atol::Real=_exact(eltype(P)) ? 0 : FiniteKernels.DEFAULT_ATOL)
    orientation in (:columns, :rows) ||
        throw(ArgumentError("`orientation` must be :columns or :rows, got :$orientation"))
    X, Y = FiniteSpace(_axis_of(input)), FiniteSpace(_axis_of(output))
    K = orientation === :columns ? P : permutedims(P)
    return FiniteKernel(X, Y, K; atol)
end

function finite_kernel(m::ResilienceCore.MarkovKernel, input, output; atol::Real=1e-8)
    return finite_kernel(m.P, input, output; orientation=:rows, atol)
end
