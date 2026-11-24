# Compositional fidelity (component 8 of the plan and its revision).
#
# Contract with the Lean development (theorems T10 and T11). For kernels given as
# column-stochastic matrices `K[y, x]`,
#
#     D(K, K′) = max_x TV(K[·, x], K′[·, x]),      TV = half the ℓ¹ distance.
#
# D is a divergence on finite kernels in Perrone's sense: for composable kernels
#     D(f ; g, f′ ; g′) ≤ D(f, f′) + D(g, g′),     D(f ⊗ g, f′ ⊗ g′) ≤ D(f, f′) + D(g, g′),
# and copying, discarding and identities have distance zero from themselves. Hence the
# joint law of a diagram under any fixed policy moves by at most Σ_i ε_i when box i is
# replaced by a box within ε_i of it, every expected utility moves by at most B Σ ε_i
# (B the range of the total utility), and deciding with the approximate diagram loses
# at most
#
#     2 B Σ_i ε_i.

_kernel_columns(K::AbstractMatrix) = K
_kernel_columns(K::AbstractArray) = reshape(K, size(K, 1), :)
_kernel_columns(k::FiniteKernel) = kernel_matrix(k)
_kernel_columns(f::KleisliMap{DistributionMonad}) = stochastic_matrix(f)

"""
    jensen_shannon_distance(p::AbstractVector, q::AbstractVector)

The Jensen-Shannon distance between two probability vectors: the square root of the
Jensen-Shannon divergence `½ KL(p ‖ m) + ½ KL(q ‖ m)`, `m = (p + q) / 2`, in nats.
It is a metric, lies in `[0, √log 2]`, and bounds the total variation:
`total_variation(p, q) ≤ √2 · jensen_shannon_distance(p, q)` (Pinsker's inequality
applied to each half). Always a floating-point number.
"""
function jensen_shannon_distance(p::AbstractVector{<:Real}, q::AbstractVector{<:Real})
    length(p) == length(q) ||
        throw(ArgumentError("the vectors have lengths $(length(p)) and $(length(q))"))
    function kl(a, m)
        return sum(iszero(x) ? 0.0 : Float64(x) * log(Float64(x) / y)
                   for (x, y) in zip(a, m))
    end
    m = (Float64.(p) .+ Float64.(q)) ./ 2
    return sqrt(max(0.0, (kl(p, m) + kl(q, m)) / 2))
end

"""
    kernel_distance(K, K′; divergence=:total_variation)

The distance between two stochastic kernels with the same inputs and outputs: the
largest distance, over the inputs, between the two output distributions,

    D(K, K′) = max_x d(K[·, x], K′[·, x]).

`K` and `K′` are column-stochastic matrices `K[y, x] = P(y | x)`, arrays with the
output axis first (the tables of pipeline boxes), `FiniteKernel`s, or Kleisli maps
of the distribution monad. With `divergence = :total_variation` (the default), `d`
is DecisionAnalysis's `total_variation`, half the ℓ¹ distance, exact for rational
kernels; with `:jensen_shannon` it is the [`jensen_shannon_distance`](@ref).

Both are **divergences that compose**: sub-additive under sequential composition and
under tensor,

    D(f ; g, f′ ; g′) ≤ D(f, f′) + D(g, g′),      D(f ⊗ g, f′ ⊗ g′) ≤ D(f, f′) + D(g, g′)

(theorem T11 of the Lean development; after Perrone). This is the per-box error
that [`fidelity_bound`](@ref) adds up.

The Kullback-Leibler divergence is not offered. In this supremum form it is also
sub-additive along composition (by its chain rule; the test suite checks this on
random kernels), so the reason is not that it fails to compose. It is that it is not
a metric (not symmetric, no triangle inequality, infinite when supports differ) and
bounds total variation only through a square root (Pinsker), so a sum of
Kullback-Leibler errors does not give the linear loss bound `2 B Σ ε`.
"""
function kernel_distance(K, K′; divergence::Symbol=:total_variation)
    A, B = _kernel_columns(K), _kernel_columns(K′)
    size(A) == size(B) ||
        throw(ArgumentError("the kernels have shapes $(size(A)) and $(size(B))"))
    d = divergence === :total_variation ? total_variation :
        divergence === :jensen_shannon ? jensen_shannon_distance :
        throw(ArgumentError("`divergence` must be :total_variation or :jensen_shannon " *
                            "(Kullback-Leibler is not a metric and gives no linear " *
                            "loss bound; it is not offered); got :$divergence"))
    return maximum(d(A[:, x], B[:, x]) for x in axes(A, 2))
end

"""
    utility_range(p::DecisionPipeline)

The range `B` of the total utility of a pipeline: the largest minus the smallest
value of the sum of its utility boxes over every joint value of the wires they read
(whether or not the model gives it positive probability). It is the constant of
[`fidelity_bound`](@ref).
"""
function utility_range(p::DecisionPipeline)
    utilities = [s for s in _specs(p) if s.kind === :utility]
    isempty(utilities) && return 0
    wires = unique(reduce(vcat, [s.ins for s in utilities]))
    axes = FiniteAxis[_axis(p, w) for w in wires]
    position = Dict(w => i for (i, w) in enumerate(wires))
    totals = [sum(s.table[(ci[position[w]] for w in s.ins)...] for s in utilities)
              for ci in CartesianIndices(Tuple(length(a) for a in axes))]
    lo, hi = extrema(totals)
    return hi - lo
end

"""
    total_error(p::DecisionPipeline)

The sum of the stated errors ([`with_error`](@ref)) of the boxes that the expected
utility depends on: every box upstream of a utility box
([`box_provenance`](@ref)). Errors of boxes that feed no utility are left out,
because replacing such a box changes no expected utility.
"""
function total_error(p::DecisionPipeline)
    return sum((b.error for b in box_provenance(p)); init=0)
end

"""
    fidelity_bound(p::DecisionPipeline)

The decision-loss bound read off the diagram: `2 · B · Σ ε`, with `B` the
[`utility_range`](@ref) and `Σ ε` the [`total_error`](@ref), computed by
DecisionAnalysis's `decision_loss_bound`.

Meaning. Let the pipeline `p` be an approximation of a true pipeline of the same
shape, in which each box of `p` is within its stated error of the true box (in
[`kernel_distance`](@ref), total variation). Then the policy that is best for `p`
is worth, in the true pipeline, at most `fidelity_bound(p)` less than the policy
that is best for the true pipeline. The errors add because total variation is
sub-additive along composition and tensor, so the joint law of the diagram under
any fixed policy moves by at most `Σ ε`; an expected utility then moves by at most
`B Σ ε`, and comparing two policies costs the factor two. The bound is usually far
from tight; the vignette on emulators shows the actual loss beside it.
"""
fidelity_bound(p::DecisionPipeline) = decision_loss_bound(utility_range(p), total_error(p))
