# Effects and value pullback (component 1 of the plan), and Jensen as structure
# (revision 3): the interchange gap whose instances are EVPI, EVPPI and EVSI.
#
# Contract with the Lean development (theorem C2). An effect on a finite set `Y` is a
# function `u : Y → ℝ`. For a Kleisli map `f : X → T Y` and a structure map
# `α : T ℝ → ℝ`,
#
#     (f* u)(x) = α( T u (f x) ).
#
# When `α` is an Eilenberg-Moore algebra, `id* u = u` and `(f ; g)* u = f* (g* u)`.
# For the distribution monad and the expectation, `f* u = Kᵀ u` with `K` the
# column-stochastic matrix of `f`.

"""
    default_algebra(monad) -> StructureMap

The structure map used when none is given: [`IdentityAlgebra`](@ref) for the
[`IdentityMonad`](@ref), [`ExpectationAlgebra`](@ref) for the
[`DistributionMonad`](@ref), [`InfimumAlgebra`](@ref) (the worst case) for the
[`PowersetMonad`](@ref), [`LowerExpectationAlgebra`](@ref) for the
[`CredalMonad`](@ref) and [`TotalRewardAlgebra`](@ref) for the
[`RewardMonad`](@ref).
"""
default_algebra(::IdentityMonad) = IdentityAlgebra()
default_algebra(::DistributionMonad) = ExpectationAlgebra()
default_algebra(::PowersetMonad) = InfimumAlgebra()
default_algebra(::CredalMonad) = LowerExpectationAlgebra()
default_algebra(::RewardMonad) = TotalRewardAlgebra()

# An effect given as a vector aligned with `points`, or as a function, as a function.
function _effect(u::AbstractVector, points::AbstractVector)
    length(u) == length(points) ||
        throw(ArgumentError("the effect has $(length(u)) values for " *
                            "$(length(points)) points"))
    lookup = Dict(zip(points, u))
    return y -> lookup[y]
end
_effect(u, ::AbstractVector) = u

"""
    value_pullback(f::KleisliMap, u, [α::StructureMap]) -> Vector
    value_pullback(K::AbstractMatrix, u::AbstractVector) -> Vector
    value_pullback(k::FiniteKernel, u::AbstractVector) -> Vector
    value_pullback(r::RewardKernel, u::AbstractVector) -> Vector

Pull the effect (utility) `u` on the codomain of a kernel back to its domain:

    (f* u)(x) = α( T u (f x) ),

the summary, by the structure map `α`, of the uncertain utility reached from `x`.
For the distribution monad and the expectation it is the conditional expected
utility `E[u | x]`, the weakest pre-expectation of `u`. `u` is a vector aligned with
`f.codom`, or a function; the result is aligned with `f.dom`. `α` defaults to
[`default_algebra`](@ref) of the map's monad and must be a structure map of that
monad ([`MonadMismatchError`](@ref) otherwise; see [`restrict_algebra`](@ref) and
[`change_monad`](@ref)).

**Functoriality.** When `α` is an Eilenberg-Moore algebra ([`is_algebra`](@ref)),
pullback is contravariantly functorial:

    value_pullback(kleisli_identity(M, X), u, α) == u
    value_pullback(kleisli_compose(f, g), u, α) == value_pullback(f, value_pullback(g, u, α), α)

which is what lets a submodel be replaced without touching the rest of an
evaluation (theorem C2 of the Lean development). For a structure map that is not an
algebra ([`CVaRMap`](@ref), say) the second identity fails, and the test suite
shows it.

The matrix and `FiniteKernel` methods are the fast path for stochastic kernels and
the expectation, `Kᵀ u` with `K[y, x] = P(y | x)`. For a `RewardKernel` `(K, W)` of
CategoricalInfluenceDiagrams the pullback is `Σ_y W[y, x] + Σ_y K[y, x] u(y)`, the
expected reward on the way plus the expected continuation, which is that package's
`continuation_value(r; continuation = u)`.

```jldoctest
julia> K = [9//10 1//5; 1//10 4//5];   # K[y, x] = P(y | x)

julia> value_pullback(K, [100, 20]) == [92, 36]
true

julia> f = kleisli_map(K);

julia> value_pullback(f, [100, 20]) == value_pullback(K, [100, 20])
true
```
"""
function value_pullback(f::KleisliMap, u, α::StructureMap=default_algebra(f.monad))
    monad_of(α) == f.monad ||
        throw(MonadMismatchError(:value_pullback, f.monad, monad_of(α),
                                 "the structure map is not of the kernel's monad"))
    effect = _effect(u, f.codom)
    return [α(monad_map(f.monad, effect, m)) for m in f.images]
end

function value_pullback(K::AbstractMatrix{<:Real}, u::AbstractVector{<:Real})
    size(K, 1) == length(u) ||
        throw(ArgumentError("the effect has $(length(u)) values for the " *
                            "$(size(K, 1)) outputs of the kernel"))
    return transpose(K) * u
end
function value_pullback(k::FiniteKernel, u::AbstractVector{<:Real})
    return value_pullback(kernel_matrix(k),
                          u)
end
function value_pullback(r::RewardKernel, u::AbstractVector{<:Real})
    return vec(sum(reward_matrix(r); dims=1)) .+ value_pullback(kernel(r), u)
end

"""
    reward_kernel(f::KleisliMap{RewardMonad}; dom=:X, codom=:Y) -> RewardKernel

The `RewardKernel` `(K, W)` of CategoricalInfluenceDiagrams determined by a Kleisli
map of the [`RewardMonad`](@ref) whose points are labels (`Symbol`s):
`K(y | x) = Σ_r f(x)(r, y)` and `W[y, x] = Σ_r r · f(x)(r, y)`. `dom` and `codom`
name the two axes. The assignment preserves composition:
`reward_kernel(kleisli_compose(f, g))` is `compose(reward_kernel(f),
reward_kernel(g))`, and value pullback along `f` with the
[`TotalRewardAlgebra`](@ref) equals value pullback along its reward kernel. A reward
kernel holds `Float64` tables, so this conversion leaves exact arithmetic.
"""
function reward_kernel(f::KleisliMap{RewardMonad,Symbol,Symbol}; dom::Symbol=:X,
                       codom::Symbol=:Y)
    X, Y = FiniteSpace(dom, f.dom), FiniteSpace(codom, f.codom)
    K = zeros(Float64, length(f.codom), length(f.dom))
    W = zeros(Float64, length(f.codom), length(f.dom))
    for (j, m) in enumerate(f.images), ((r, y), p) in _pairs(m)
        i = findfirst(==(y), f.codom)
        K[i, j] += p
        W[i, j] += r * p
    end
    return RewardKernel(FiniteKernel(X, Y, K), W)
end

# The interchange gap
# -------------------

"""
    interchange_gap(α::StructureMap, m, Q::AbstractMatrix; states=axes(Q, 2), h=maximum)
    interchange_gap(problem::DecisionProblem, [α::StructureMap])

How far the map `h` (by default the maximum over actions) is from commuting with the
structure map `α` at the uncertain state `m`:

    gap = α( T (θ ↦ h(Q[:, θ])) m )  −  h( [ α( T (θ ↦ Q[a, θ]) m ) for a ] ),

"summarise the best payoff in each state" minus "the best of the summarised
payoffs". `Q[a, θ]` has one row per action and one column per state; `m` is a value
of the monad of `α` over `states` (column indices by default).

- For the expectation and `h = maximum` the gap is `E max − max E`, the **expected
  value of perfect information**, and it is nonnegative because the maximum is
  convex: a convex map is an oplax morphism of expectation algebras (Jensen's
  inequality). A concave `h` (`minimum`) gives a nonpositive gap, an affine one
  (`sum`) gives zero.
- The same statement at a coarser `m` gives the other values of information: with
  `m` the distribution of the signal of an experiment and `Q` the posterior payoff
  it is EVSI; with `m` the distribution over the cells of a partition it is EVPPI
  ([`posterior_payoff`](@ref)).
- For the worst case ([`InfimumAlgebra`](@ref)) the gap is
  `min_θ max_a Q − max_a min_θ Q`, the minimax gap, also nonnegative; for the best
  case ([`SupremumAlgebra`](@ref)) it is zero, since two maxima commute.

This is the precise form of "the value of information is an interchange gap"
(theorem C4b of the Lean development; after Fritz and Perrone, who identify the lax
and oplax algebra morphisms with the concave and convex maps).

The method for a problem uses its belief as `m`, its feasible actions as the rows
of `Q`, and by default the algebra of the belief's monad
([`default_algebra`](@ref)).

```jldoctest
julia> p = DecisionProblem(PayoffTable([0 -100; -30 -30]), [3 // 5, 2 // 5]);

julia> interchange_gap(p) == evpi(p)
true
```
"""
function interchange_gap(α::StructureMap, m, Q::AbstractMatrix{<:Real};
                         states=axes(Q, 2), h=maximum)
    length(states) == size(Q, 2) ||
        throw(ArgumentError("$(length(states)) states for the $(size(Q, 2)) columns " *
                            "of the table"))
    M = monad_of(α)
    column = Dict(s => j for (j, s) in enumerate(states))
    outer = α(monad_map(M, θ -> h(view(Q, :, column[θ])), m))
    inner = h([α(monad_map(M, θ -> Q[a, column[θ]], m)) for a in axes(Q, 1)])
    return outer - inner
end

"""
    interchange_gap(weights::AbstractVector, objectives::AbstractMatrix)

The interchange gap of the maximum and a weighted sum, in the form of the Lean
development (`interchangeGap`): with `objectives[i, a]` the objective of action `a`
(column) at index `i` (row),

    Σ_i w_i max_a W[i, a]  −  max_a Σ_i w_i W[i, a],

"maximise then average, minus average then maximise". It is nonnegative for
nonnegative weights (`interchangeGap_nonneg`). The weights need not sum to one,
which is what lets one function give all three values of information:

    evpi  == interchange_gap(p, transpose(Q))                       (i = state)
    evsi  == interchange_gap(ones(n_signals), J),  J[z, a] = Σ_θ p(θ) L[z, θ] Q[a, θ]
    evppi == interchange_gap(ones(n_cells), C),    C[c, a] = Σ_{θ ∈ c} p(θ) Q[a, θ]

(`evpi_eq_interchangeGap`, `evsi_eq_interchangeGap`, `evppi_eq_interchangeGap`;
each is a test). **Note the layout**: rows are the index that is averaged over and
columns are actions, the transpose of a payoff table.
"""
function interchange_gap(weights::AbstractVector{<:Real},
                         objectives::AbstractMatrix{<:Real})
    length(weights) == size(objectives, 1) ||
        throw(ArgumentError("$(length(weights)) weights for the $(size(objectives, 1)) " *
                            "rows of the objectives"))
    return sum(weights[i] * maximum(view(objectives, i, :)) for i in eachindex(weights)) -
           maximum(transpose(objectives) * weights)
end

"""
    expectation_rewrite(kind::Symbol) -> Symbol

The relation that holds when a map `h` on the reals is moved through an expectation
box, `h(E X)` against `E h(X)`, by the kind of `h`: `:affine` gives `:(==)` (affine
maps are exactly the maps that commute with expectation, Lean
`commutesWithMix_iff_affine`), `:convex` gives `:(<=)` (`h(E X) ≤ E h(X)`: a convex
map is an oplax morphism of expectation algebras, `isOplax_iff_convexOn`) and
`:concave` gives `:(>=)`. Any other kind throws `ArgumentError`: a rewrite of a
pipeline through an expectation is licensed only with one of these three labels.
The maximum over actions is convex, which is the nonnegative
[`interchange_gap`](@ref); a risk-averse (concave) utility gives a certainty
equivalent below the mean.
"""
function expectation_rewrite(kind::Symbol)
    kind === :affine && return :(==)
    kind === :convex && return :(<=)
    kind === :concave && return :(>=)
    throw(ArgumentError("a map can be moved through an expectation only as :affine " *
                        "(=), :convex (≤) or :concave (≥); got :$kind"))
end

function interchange_gap(problem::DecisionProblem,
                         α::StructureMap=default_algebra(belief_monad(problem.belief)))
    m = belief_value(problem.belief, monad_of(α); states=problem.payoff.states)
    Q = problem.payoff.Q[problem.feasible, :]
    return interchange_gap(α, m, Q; states=problem.payoff.states)
end
