# Conditionals: Bayesian inversion through sub-stochastic kernels and normalisation
# (component 2 of the plan, revision 2; after Di Lavore and Román's partial Markov
# categories).
#
# Contract with the Lean development (theorem C3). For a prior `p` on Θ and a channel
# `L[z, θ] = P(z | θ)`:
#
#     joint[z, θ]   = L[z, θ] p(θ)                    (a sub-stochastic kernel Z ⇸ Θ)
#     evidence[z]   = Σ_θ joint[z, θ]
#     inverse[θ, z] = joint[z, θ] / evidence[z]  if evidence[z] > 0,  else 0.
#
# A column of `inverse` for a signal of probability zero is the zero vector: the
# failure value of a sub-stochastic kernel, not an exception and not an arbitrary
# distribution. For channels `f : Θ → Y` and `g : Y → Z`,
#
#     joint_{f;g}[z, θ] = Σ_y joint_g[z, y] · inverse_f[θ, y]         (no side condition)
#     inverse_{f;g}[θ, z] = Σ_y inverse_f[θ, y] · inverse_g[y, z]      (every z; both
#                                                 sides are zero off the support)
#
# where `joint_g` and `inverse_g` are taken against the pushed prior `f p`.

"""
    normalize_mass(v::AbstractVector) -> (mass, normalized)

Normalisation of a sub-probability vector as a total operation: its mass `Σ v` and
`v / mass`, or the zero vector when the mass is zero. A zero vector is the failure
value of the sub-distribution monad: "this was observed with probability zero", kept
as a value so that conditioning never throws and never invents a distribution.
Entries must be nonnegative (`ArgumentError`).

```jldoctest
julia> normalize_mass([1 // 10, 3 // 10])
(2//5, Rational{Int64}[1//4, 3//4])

julia> normalize_mass([0 // 1, 0 // 1])
(0//1, Rational{Int64}[0, 0])
```
"""
function normalize_mass(v::AbstractVector{<:Real})
    all(>=(0), v) || throw(ArgumentError("a sub-probability vector has a negative entry"))
    mass = sum(v)
    T = typeof(one(eltype(v)) / one(eltype(v)))
    iszero(mass) && return (mass, zeros(T, length(v)))
    return (mass, convert(Vector{T}, v ./ mass))
end

"""
    BayesianInverse

What [`bayesian_inverse`](@ref) returns: the inversion of a channel against a prior,
with zero-probability evidence as a value. Fields:

- `prior`: the prior `p(θ)`.
- `channel`: the channel `L[z, θ] = P(z | θ)`, column-stochastic.
- `joint`: the sub-stochastic kernel `joint[z, θ] = L[z, θ] p(θ)`.
- `evidence`: the mass of each signal, `evidence[z] = Σ_θ joint[z, θ]`: the pushed
  prior on the signals.
- `inverse`: `inverse[θ, z] = P(θ | z)`. The column of a signal of positive mass is
  its posterior and sums to one; the column of a signal of mass zero is zero. It is
  a sub-stochastic kernel `Z ⇸ Θ`, total exactly on the support of the evidence.
- `states`, `signals`: labels, when the inputs carried them (`nothing` otherwise).
"""
struct BayesianInverse{T<:Real}
    prior::Vector{T}
    channel::Matrix{T}
    joint::Matrix{T}
    evidence::Vector{T}
    inverse::Matrix{T}
    states::Union{Nothing,Vector{Symbol}}
    signals::Union{Nothing,Vector{Symbol}}
end

function Base.show(io::IO, b::BayesianInverse)
    return print(io, "BayesianInverse(", size(b.channel, 2), " states, ",
                 size(b.channel, 1), " signals, ", count(iszero, b.evidence),
                 " of probability zero)")
end

"""
    bayesian_inverse(prior::AbstractVector, channel::AbstractMatrix) -> BayesianInverse
    bayesian_inverse(prior::FiniteBelief, experiment::Experiment) -> BayesianInverse
    bayesian_inverse(prior::FiniteKernel, channel::FiniteKernel) -> BayesianInverse

Bayesian inversion of the channel `L[z, θ] = P(z | θ)` against the prior `p(θ)`,
computed as a sub-stochastic kernel followed by normalisation: first the joint
`L[z, θ] p(θ)`, then each signal's row divided by its mass, **when that mass is not
zero**. A signal of probability zero gets the zero column in `inverse` and mass zero
in `evidence`; nothing is thrown and nothing is invented
([`normalize_mass`](@ref)). Exact for rational inputs.

It agrees with DecisionAnalysis's `bayes_invert`: the same joint and marginal, the
same posteriors where they exist, and a zero column exactly where `bayes_invert`
returns `nothing`. [`inverse_compose`](@ref) composes inversions and
[`posterior`](@ref) reads one off.

```jldoctest
julia> inv = bayesian_inverse([3 // 5, 2 // 5], [4//5 1//5; 1//5 4//5; 0 0]);

julia> inv.evidence == [14 // 25, 11 // 25, 0]
true

julia> inv.inverse == [6//7 3//11 0; 1//7 8//11 0]   # the third column is zero
true
```
"""
function bayesian_inverse(prior::AbstractVector{<:Real}, channel::AbstractMatrix{<:Real};
                          states=nothing, signals=nothing)
    size(channel, 2) == length(prior) ||
        throw(ArgumentError("the channel has $(size(channel, 2)) columns for a prior " *
                            "on $(length(prior)) states"))
    all(>=(0), prior) || throw(ArgumentError("the prior has a negative entry"))
    all(>=(0), channel) || throw(ArgumentError("the channel has a negative entry"))
    T = typeof(one(promote_type(eltype(prior), eltype(channel))) / one(eltype(prior)))
    p = convert(Vector{T}, prior)
    L = convert(Matrix{T}, channel)
    joint = L .* permutedims(p)
    evidence = vec(sum(joint; dims=2))
    inverse = zeros(T, length(p), size(L, 1))
    for z in axes(L, 1)
        _, inverse[:, z] = normalize_mass(view(joint, z, :))
    end
    return BayesianInverse{T}(p, L, joint, evidence, inverse, states, signals)
end

function bayesian_inverse(prior::FiniteBelief, experiment::Experiment)
    experiment.states === nothing || experiment.states == prior.states ||
        throw(LabelMismatchError("states of the prior and the experiment", prior.states,
                                 experiment.states))
    return bayesian_inverse(prior.probabilities, experiment.likelihood; states=prior.states,
                            signals=experiment.signals)
end

function bayesian_inverse(prior::FiniteKernel, channel::FiniteKernel)
    length(prior.dom) == 1 ||
        throw(ArgumentError("the prior must be a state, a kernel out of the unit space"))
    prior.codom == channel.dom ||
        throw(FiniteKernels.SpaceMismatchError(:bayesian_inverse, prior.codom, channel.dom))
    return bayesian_inverse(vec(kernel_matrix(prior)), kernel_matrix(channel))
end

"""
    posterior(inv::BayesianInverse, z) -> Union{Nothing,Vector}

The posterior over the states given signal `z` (an index, or a label when the
inversion has signal labels), or `nothing` when `z` has probability zero.
"""
function posterior(inv::BayesianInverse, z)
    i = z isa Integer ? z :
        something(findfirst(==(Symbol(z)), something(inv.signals, Symbol[])), 0)
    1 <= i <= length(inv.evidence) || throw(ArgumentError("unknown signal $z"))
    return iszero(inv.evidence[i]) ? nothing : inv.inverse[:, i]
end

"""
    inverse_compose(first::BayesianInverse, second::BayesianInverse) -> Matrix

The composite of two inversions, for channels in series `f : Θ → Y` then
`g : Y → Z`: with `first = bayesian_inverse(p, f)` and
`second = bayesian_inverse(f p, g)` (the second taken against the evidence of the
first), the matrix `first.inverse * second.inverse`, a sub-stochastic kernel
`Z ⇸ Θ`.

**Inversion of a composite is the composite of the inversions**:

    bayesian_inverse(p, g * f).inverse == inverse_compose(first, second)

for every signal, with no side condition: on a signal of probability zero both sides
are the zero column, and on the others both are the posterior (theorem C3 of the
Lean development; the textbook statement holds "on the support", which is here the
set of nonzero columns). The second inversion must have been taken against the
evidence of the first (`ArgumentError` otherwise).
"""
function inverse_compose(first::BayesianInverse, second::BayesianInverse)
    length(second.prior) == length(first.evidence) ||
        throw(ArgumentError("the second inversion is over $(length(second.prior)) " *
                            "states and the first has $(length(first.evidence)) signals"))
    all(a -> isapprox(a[1], a[2]; atol=_default_atol(typeof(a[1]))),
        zip(second.prior, first.evidence)) ||
        throw(ArgumentError("the second inversion must be taken against the evidence " *
                            "of the first (the pushed prior)"))
    return first.inverse * second.inverse
end
