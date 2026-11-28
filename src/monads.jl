# Uncertainty monads on finite sets, their values, their structure maps on the reals
# and the monad morphisms between them (component 3 of the plan).
#
# The definitions here are a contract with the Lean development (tier C):
#
#   Id   T X = X                         η x = x           m >>= f = f m
#   D    finite distributions            η x = δ_x         (m >>= f)(y) = Σ_x m(x) f(x)(y)
#   P⁺   non-empty finite subsets        η x = {x}         m >>= f = ⋃_{x ∈ m} f(x)
#   C    finitely generated credal sets  η x = {δ_x}       m >>= f = conv{ Σ_x p(x) q_x :
#                                                            p ∈ gen(m), q_x ∈ gen(f x) }
#   R    D(ℝ × −), reward and outcome    η x = δ_(0, x)    rewards add along >>=
#
# A structure map is a function α : T ℝ → ℝ. It is an Eilenberg-Moore algebra when
# α(η x) = x and α(μ M) = α(T α M) for every M ∈ T T ℝ. Identity (Id), expectation (D),
# minimum and maximum (P⁺), lower and upper expectation (C) and expected total reward
# (R) are algebras; Hurwicz, Laplace, CVaR, quantiles and α-maxmin are structure maps
# that are not.

# Monads
# ------

"""
    UncertaintyMonad

Supertype of the uncertainty monads on finite sets: [`IdentityMonad`](@ref) (no
uncertainty), [`DistributionMonad`](@ref) (finite probability distributions),
[`PowersetMonad`](@ref) (non-empty finite sets of possibilities, no probabilities),
[`CredalMonad`](@ref) (finitely generated convex sets of distributions) and
[`RewardMonad`](@ref) (distributions over a reward and an outcome). Each has
[`monad_unit`](@ref), [`monad_bind`](@ref), [`monad_map`](@ref) and
[`monad_join`](@ref), and its Eilenberg-Moore algebras on the reals are structure
maps ([`StructureMap`](@ref)).

For someone who does not use the word: a monad here is a kind of uncertain value
("one outcome", "a distribution over outcomes", "a set of possible outcomes", "a set
of candidate distributions") together with the rule for chaining two uncertain
steps into one.
"""
abstract type UncertaintyMonad end

"""
    IdentityMonad()

No uncertainty: a value of `Id X` is an element of `X`. Its Kleisli maps are
functions, and its algebra on the reals is [`IdentityAlgebra`](@ref).
"""
struct IdentityMonad <: UncertaintyMonad end

"""
    DistributionMonad()

Finite probability distributions: a value of `D X` is a
[`FiniteDistribution`](@ref). Its Kleisli maps are stochastic matrices, and its
algebra on the reals is the expectation, [`ExpectationAlgebra`](@ref).
"""
struct DistributionMonad <: UncertaintyMonad end

"""
    PowersetMonad()

Non-empty finite sets (written `P⁺`): a value is a [`FiniteSubset`](@ref), the
outcomes that are possible, with no probabilities attached. Its Kleisli maps are
total multivalued maps. Its algebras on the reals are the minimum
([`InfimumAlgebra`](@ref), the worst case) and the maximum
([`SupremumAlgebra`](@ref), the best case).
"""
struct PowersetMonad <: UncertaintyMonad end

"""
    CredalMonad()

Finitely generated credal sets: a value is a [`CredalHull`](@ref), the convex hull
of finitely many finite distributions. Its algebras on the reals are the lower and
the upper expectation ([`LowerExpectationAlgebra`](@ref),
[`UpperExpectationAlgebra`](@ref)).

**Sequential composition only.** Chaining with [`monad_bind`](@ref) (and so
[`kleisli_compose`](@ref)) is well defined and sound: the composite set contains
every distribution that the two steps can produce. It is also loose: the second step
may choose a different member of its set for every outcome of the first, so a
constraint that ties the steps together ("the same unknown rate at both steps") is
forgotten and the composite set is larger than the truth. The monad is not
commutative (the two orders of pairing two credal values give different sets), so
its Kleisli category has no tensor product and this package offers no string
diagrams for credal kernels (Liell-Cock and Staton 2025; graded credal kernels are
the known repair and are not implemented).
"""
struct CredalMonad <: UncertaintyMonad end

"""
    RewardMonad()

Distributions over a reward and an outcome, `R X = D(ℝ × X)`: a value is a
[`FiniteDistribution`](@ref) over pairs `(r, x)`. Chaining adds the rewards. Its
algebra on the reals is the expected total reward, [`TotalRewardAlgebra`](@ref),
`α(m) = Σ m(r, v) (r + v)`.

This is the monad behind `RewardKernel` of CategoricalInfluenceDiagrams: a Kleisli
map `X → R Y` determines the reward kernel `(K, W)` with `K(y | x) = Σ_r f(x)(r, y)`
and `W[y, x] = Σ_r r f(x)(r, y)` ([`reward_kernel`](@ref)), Kleisli composition maps
to the expectation-semiring composition `(K₁K₂, W₁K₂ + K₁W₂)`, and value pullback
along `f` is the continuation value of that reward kernel. Of the three semantics
that Abadi and Plotkin (2020) give for choice with probability and reward, this is
the one in which only the **expected** reward is carried: `(K, W)` forgets how
reward and outcome are correlated beyond the mean of the reward given the outcome,
which is all that an expected-utility evaluation needs and not enough for a
risk-sensitive one.
"""
struct RewardMonad <: UncertaintyMonad end

# Values
# ------

_exact(::Type{<:Integer}) = true
_exact(::Type{<:Rational}) = true
_exact(::Type) = false
_default_atol(::Type{T}) where {T} = _exact(T) ? 0 : 1e-9

"""
    FiniteDistribution(outcomes, probabilities; atol)

A probability distribution with finite support: a value of the
[`DistributionMonad`](@ref). `outcomes` may be of any type and may repeat; equal
outcomes are merged and outcomes of probability zero are dropped, so the stored
`outcomes` are the support, in order of first appearance, and `probabilities` are
positive and sum to one. The check is exact for integer and rational probabilities
(`atol = 0`) and to `atol = 1e-9` in floating point. Probabilities that are negative
or do not sum to one throw `InvalidBeliefError` (DecisionAnalysis).

Two distributions are equal when they give every outcome the same probability,
whatever the order they were written in.

```jldoctest
julia> d = FiniteDistribution([:wet, :dry, :wet], [1 // 4, 1 // 2, 1 // 4])
FiniteDistribution(wet => 1//2, dry => 1//2)

julia> ExpectationAlgebra()(FiniteDistribution([10, 20], [1 // 4, 3 // 4]))
35//2
```
"""
struct FiniteDistribution{X,T<:Real}
    outcomes::Vector{X}
    probabilities::Vector{T}
    global function _distribution(outcomes::Vector{X},
                                  probabilities::Vector{T}) where {X,T<:Real}
        return new{X,T}(outcomes, probabilities)
    end
end

function FiniteDistribution(outcomes::AbstractVector, probabilities::AbstractVector{T};
                            atol::Real=_default_atol(T)) where {T<:Real}
    length(outcomes) == length(probabilities) ||
        throw(ArgumentError("$(length(outcomes)) outcomes for " *
                            "$(length(probabilities)) probabilities"))
    isempty(outcomes) &&
        throw(InvalidBeliefError("a distribution needs at least one outcome"))
    all(p -> isfinite(p) && p >= -atol, probabilities) ||
        throw(InvalidBeliefError("the probabilities have a negative or non-finite entry"))
    abs(sum(probabilities) - 1) <= atol ||
        throw(InvalidBeliefError("the probabilities sum to $(sum(probabilities)), " *
                                 "not to one"))
    X = eltype(outcomes)
    index = Dict{X,Int}()
    xs, ps = X[], T[]
    for (x, p) in zip(outcomes, probabilities)
        p > 0 || continue
        i = get(index, x, 0)
        if i == 0
            push!(xs, x)
            push!(ps, p)
            index[x] = length(xs)
        else
            ps[i] += p
        end
    end
    return _distribution(xs, ps)
end

_pairs(d::FiniteDistribution) = zip(d.outcomes, d.probabilities)

function Base.:(==)(a::FiniteDistribution, b::FiniteDistribution)
    length(a.outcomes) == length(b.outcomes) || return false
    for (x, p) in _pairs(a)
        i = findfirst(isequal(x), b.outcomes)
        (i !== nothing && b.probabilities[i] == p) || return false
    end
    return true
end
Base.isequal(a::FiniteDistribution, b::FiniteDistribution) = a == b
function Base.hash(d::FiniteDistribution, h::UInt)
    return hash(Set(_pairs(d)), hash(:FiniteDistribution, h))
end

"""
    isapprox(a::FiniteDistribution, b::FiniteDistribution; atol=1e-9)

Whether two distributions have the same support and probabilities within `atol`.
"""
function Base.isapprox(a::FiniteDistribution, b::FiniteDistribution; atol::Real=1e-9)
    length(a.outcomes) == length(b.outcomes) || return false
    for (x, p) in _pairs(a)
        i = findfirst(isequal(x), b.outcomes)
        (i !== nothing && abs(b.probabilities[i] - p) <= atol) || return false
    end
    return true
end

function Base.show(io::IO, d::FiniteDistribution)
    print(io, "FiniteDistribution(")
    join(io, (string(x, " => ", p) for (x, p) in _pairs(d)), ", ")
    return print(io, ")")
end

"""
    probability_of(d::FiniteDistribution, x)

The probability that `d` gives to the outcome `x`; zero for an outcome outside the
support.
"""
function probability_of(d::FiniteDistribution{X,T}, x) where {X,T}
    i = findfirst(isequal(x), d.outcomes)
    return i === nothing ? zero(T) : d.probabilities[i]
end

"""
    FiniteSubset(elements)

A non-empty finite set: a value of the [`PowersetMonad`](@ref). Repeated elements
are merged; the order of first appearance is kept for printing and is not part of
the value (two subsets with the same elements are equal). An empty collection throws
`ArgumentError`.

```jldoctest
julia> FiniteSubset([:low, :high, :low])
FiniteSubset(low, high)

julia> InfimumAlgebra()(FiniteSubset([30, 10, 20]))
10
```
"""
struct FiniteSubset{X}
    elements::Vector{X}
    function FiniteSubset(elements::AbstractVector)
        isempty(elements) &&
            throw(ArgumentError("a FiniteSubset is a non-empty set; got no elements"))
        xs = unique(elements)
        return new{eltype(xs)}(xs)
    end
end

Base.:(==)(a::FiniteSubset, b::FiniteSubset) = issetequal(a.elements, b.elements)
Base.isequal(a::FiniteSubset, b::FiniteSubset) = a == b
Base.hash(s::FiniteSubset, h::UInt) = hash(Set(s.elements), hash(:FiniteSubset, h))
Base.length(s::FiniteSubset) = length(s.elements)
Base.in(x, s::FiniteSubset) = any(isequal(x), s.elements)

function Base.show(io::IO, s::FiniteSubset)
    print(io, "FiniteSubset(")
    join(io, s.elements, ", ")
    return print(io, ")")
end

"""
    CredalHull(generators::AbstractVector{<:FiniteDistribution})

A finitely generated credal set: the convex hull of the listed distributions, a
value of the [`CredalMonad`](@ref). Repeated generators are merged. A generator need
not be an extreme point; [`prune_generators`](@ref) removes those that are not.

`==` compares the lists of generators as sets, which is sufficient but not necessary
for two hulls to be the same set. [`same_hull`](@ref) decides equality of the hulls
themselves (by linear programme), and is what the monad laws hold up to.
"""
struct CredalHull{X,T<:Real}
    generators::Vector{FiniteDistribution{X,T}}
    function CredalHull(generators::AbstractVector{<:FiniteDistribution})
        isempty(generators) &&
            throw(ArgumentError("a CredalHull needs at least one generating distribution"))
        X = mapreduce(g -> eltype(g.outcomes), typejoin, generators)
        T = mapreduce(g -> eltype(g.probabilities), promote_type, generators)
        gs = FiniteDistribution{X,T}[_distribution(convert(Vector{X}, g.outcomes),
                                                   convert(Vector{T}, g.probabilities))
                                     for g in generators]
        return new{X,T}(unique(gs))
    end
end

function Base.:(==)(a::CredalHull, b::CredalHull)
    return issetequal(a.generators, b.generators)
end
Base.isequal(a::CredalHull, b::CredalHull) = a == b
Base.hash(c::CredalHull, h::UInt) = hash(Set(c.generators), hash(:CredalHull, h))

function Base.show(io::IO, c::CredalHull)
    return print(io, "CredalHull with ", length(c.generators), " generator",
                 length(c.generators) == 1 ? "" : "s")
end

# Unit, bind, map, join
# ---------------------

"""
    monad_unit(monad, x)

The certain value: `x` itself for the [`IdentityMonad`](@ref), the point mass at `x`
for the [`DistributionMonad`](@ref), the singleton `{x}` for the
[`PowersetMonad`](@ref), the set containing only the point mass for the
[`CredalMonad`](@ref), and the point mass at `(0, x)` (no reward) for the
[`RewardMonad`](@ref).
"""
monad_unit(::IdentityMonad, x) = x
monad_unit(::DistributionMonad, x) = _distribution([x], [1])
monad_unit(::PowersetMonad, x) = FiniteSubset([x])
monad_unit(::CredalMonad, x) = CredalHull([_distribution([x], [1])])
monad_unit(::RewardMonad, x) = _distribution([(0, x)], [1])

"""
    monad_bind(monad, m, f)

Chain an uncertain value `m` with a step `f` that turns each outcome into an
uncertain value of the same monad (Kleisli extension, `m >>= f`):

- identity: `f(m)`;
- distributions: the mixture `Σ_x m(x) f(x)`;
- non-empty sets: the union of the `f(x)` for `x` in `m`;
- credal sets: the hull of every mixture `Σ_x p(x) q_x` with `p` a generator of `m`
  and `q_x` a generator of `f(x)`, chosen separately for each `x` (see
  [`CredalMonad`](@ref) for why this is sound but loose);
- rewards: the mixture, with the reward of `m` added to the reward of `f(x)`.
"""
monad_bind(::IdentityMonad, m, f) = f(m)

function monad_bind(::DistributionMonad, m::FiniteDistribution, f)
    images = [f(x) for x in m.outcomes]
    return _mixture(m.probabilities, images)
end

function _mixture(weights::AbstractVector, images::AbstractVector)
    all(q -> q isa FiniteDistribution, images) ||
        throw(MonadMismatchError(:monad_bind, DistributionMonad(), typeof(first(images)),
                                 "the step must return a FiniteDistribution"))
    X = mapreduce(q -> eltype(q.outcomes), typejoin, images)
    T = promote_type(eltype(weights),
                     mapreduce(q -> eltype(q.probabilities), promote_type, images))
    xs, ps = X[], T[]
    for (w, q) in zip(weights, images), (y, p) in _pairs(q)
        push!(xs, y)
        push!(ps, w * p)
    end
    return FiniteDistribution(xs, ps; atol=_exact(T) ? 0 : 1e-6)
end

function monad_bind(::PowersetMonad, m::FiniteSubset, f)
    images = [f(x) for x in m.elements]
    all(s -> s isa FiniteSubset, images) ||
        throw(MonadMismatchError(:monad_bind, PowersetMonad(), typeof(first(images)),
                                 "the step must return a FiniteSubset"))
    return FiniteSubset(reduce(vcat, [s.elements for s in images]))
end

function monad_bind(::CredalMonad, m::CredalHull, f)
    out = FiniteDistribution[]
    cache = Dict{Any,Any}()
    for p in m.generators
        images = [get!(() -> f(x), cache, x) for x in p.outcomes]
        all(c -> c isa CredalHull, images) ||
            throw(MonadMismatchError(:monad_bind, CredalMonad(), typeof(first(images)),
                                     "the step must return a CredalHull"))
        for choice in Iterators.product((c.generators for c in images)...)
            push!(out, _mixture(p.probabilities, collect(choice)))
        end
    end
    return CredalHull(out)
end

function monad_bind(::RewardMonad, m::FiniteDistribution, f)
    images = map(m.outcomes) do (r, x)
        q = f(x)
        return _distribution([(r + s, y) for (s, y) in q.outcomes], q.probabilities)
    end
    return _mixture(m.probabilities, images)
end

"""
    monad_map(monad, f, m)

Apply the function `f` to every outcome of the uncertain value `m` (the functor
part of the monad, `T f`). Outcomes that `f` identifies are merged. For the
[`RewardMonad`](@ref) the reward is kept and `f` acts on the outcome.
"""
monad_map(::IdentityMonad, f, m) = f(m)
function monad_map(::DistributionMonad, f, m::FiniteDistribution)
    return FiniteDistribution([f(x) for x in m.outcomes], m.probabilities;
                              atol=_exact(eltype(m.probabilities)) ? 0 : 1e-6)
end
monad_map(::PowersetMonad, f, m::FiniteSubset) = FiniteSubset([f(x) for x in m.elements])
function monad_map(::CredalMonad, f, m::CredalHull)
    return CredalHull([monad_map(DistributionMonad(), f, p) for p in m.generators])
end
function monad_map(::RewardMonad, f, m::FiniteDistribution)
    return FiniteDistribution([(r, f(x)) for (r, x) in m.outcomes], m.probabilities;
                              atol=_exact(eltype(m.probabilities)) ? 0 : 1e-6)
end

"""
    monad_join(monad, mm)

Flatten an uncertain value of uncertain values (the multiplication `μ` of the
monad): `monad_bind(monad, mm, identity)`. For distributions it is the mixture of a
distribution over distributions; for sets, the union of a set of sets.
"""
monad_join(M::UncertaintyMonad, mm) = monad_bind(M, mm, identity)

# Credal hulls: membership, equality, pruning
# -------------------------------------------

# The smallest ℓ∞ distance from `q` to the hull of `gens`, by linear programme
# (stated as a JuMP model and solved through DecisionAnalysis's `solve_program`):
#   minimise t  s.t.  −t ≤ Σ_k λ_k p_k(x) − q(x) ≤ t for every x,  Σ λ = 1,  λ ≥ 0.
function _hull_distance(q::FiniteDistribution, gens::AbstractVector; optimizer=nothing)
    support = unique(vcat(q.outcomes, reduce(vcat, [g.outcomes for g in gens])))
    S = promote_type(eltype(q.probabilities),
                     mapreduce(g -> eltype(g.probabilities), promote_type, gens))
    T = _exact(S) ? Rational{BigInt} : Float64
    model = JuMP.GenericModel{T}()
    K = length(gens)
    λ = JuMP.@variable(model, [1:K], lower_bound = zero(T), base_name = "λ")
    t = JuMP.@variable(model, lower_bound = zero(T), base_name = "t")
    simplex = JuMP.@constraint(model, sum(λ) == one(T))
    P = T[T(probability_of(g, x)) for x in support, g in gens]
    b = T[T(probability_of(q, x)) for x in support]
    upper = JuMP.@constraint(model, [i = eachindex(support)],
                             sum(P[i, k] * λ[k] for k in 1:K) - t <= b[i])
    lower = JuMP.@constraint(model, [i = eachindex(support)],
                             sum(P[i, k] * λ[k] for k in 1:K) + t >= b[i])
    JuMP.@objective(model, Min, t)
    prog = DecisionProgram(:hull_membership, model, (; λ, t), (; simplex, upper, lower))
    sol = solve_program(prog; optimizer)
    sol.status === :optimal || throw(LinearProgramError(:hull_membership, sol.status))
    return sol.objective
end

"""
    in_hull(q::FiniteDistribution, c::CredalHull; atol, optimizer=nothing) -> Bool

Whether the distribution `q` lies in the credal set `c`, the convex hull of its
generators. Decided by a linear programme, stated as a JuMP model and solved by
DecisionAnalysis's `solve_program` (the built-in exact simplex unless an `optimizer`
is given): exactly for rational probabilities, and to `atol = 1e-9` in the largest
coordinate in floating point.
"""
function in_hull(q::FiniteDistribution, c::CredalHull;
                 atol::Real=_default_atol(promote_type(eltype(q.probabilities),
                                                       eltype(first(c.generators).probabilities))),
                 optimizer=nothing)
    any(isequal(q), c.generators) && return true
    return _hull_distance(q, c.generators; optimizer) <= atol
end

"""
    same_hull(a::CredalHull, b::CredalHull; atol, optimizer=nothing) -> Bool

Whether two credal sets are the same set of distributions: every generator of each
lies in the hull of the other ([`in_hull`](@ref)). This is the equality up to which
the laws of the [`CredalMonad`](@ref) hold; two hulls can be equal with different
lists of generators.
"""
function same_hull(a::CredalHull, b::CredalHull; kw...)
    return all(g -> in_hull(g, b; kw...), a.generators) &&
           all(g -> in_hull(g, a; kw...), b.generators)
end

"""
    prune_generators(c::CredalHull; atol, optimizer=nothing) -> CredalHull

The same credal set with every generator removed that lies in the hull of the
others, so that what is left are its extreme points. One linear programme per
generator.
"""
function prune_generators(c::CredalHull; kw...)
    keep = collect(c.generators)
    i = 1
    while i <= length(keep) && length(keep) > 1
        others = CredalHull(keep[setdiff(eachindex(keep), i)])
        if in_hull(keep[i], others; kw...)
            deleteat!(keep, i)
        else
            i += 1
        end
    end
    return CredalHull(keep)
end

# Structure maps and algebras
# ---------------------------

"""
    StructureMap

Supertype of the maps `α : T ℝ → ℝ` that turn an uncertain real number into one
number, for an [`UncertaintyMonad`](@ref) `T`. A structure map is called on a value
of its monad: `α(m)`. [`monad_of`](@ref) gives the monad.

Some are **Eilenberg-Moore algebras** ([`is_algebra`](@ref)): they satisfy
`α(η x) = x` and `α(μ M) = α(T α M)`, which says that summarising in two stages is
the same as summarising at once. These are [`IdentityAlgebra`](@ref),
[`ExpectationAlgebra`](@ref), [`InfimumAlgebra`](@ref), [`SupremumAlgebra`](@ref),
[`LowerExpectationAlgebra`](@ref), [`UpperExpectationAlgebra`](@ref),
[`TotalRewardAlgebra`](@ref) and [`TransportedAlgebra`](@ref). The others
([`HurwiczMap`](@ref), [`LaplaceMap`](@ref), [`CVaRMap`](@ref),
[`QuantileMap`](@ref), [`AlphaMaxminMap`](@ref)) are aggregators in common use that
fail the second law; [`algebra_multiplication_defect`](@ref) exhibits the failure.
The distinction decides which rules can be solved stage by stage
([`admits_backward_induction`](@ref)) and for which value pullback is functorial
([`value_pullback`](@ref)).
"""
abstract type StructureMap end

"""
    IdentityAlgebra()

The algebra of the [`IdentityMonad`](@ref) on the reals: a certain number is its own
summary.
"""
struct IdentityAlgebra <: StructureMap end
(::IdentityAlgebra)(x::Real) = x

"""
    ExpectationAlgebra()

The algebra of the [`DistributionMonad`](@ref) on the reals: the expectation
`α(m) = Σ_x m(x) x`. It is the algebra behind maximum expected utility.
"""
struct ExpectationAlgebra <: StructureMap end
function (::ExpectationAlgebra)(m::FiniteDistribution{<:Real})
    return sum(p * x for (x, p) in _pairs(m))
end

"""
    InfimumAlgebra()

The minimum of a non-empty finite set of reals: an algebra of the
[`PowersetMonad`](@ref), and the one behind the worst case (Wald's maximin).
"""
struct InfimumAlgebra <: StructureMap end
(::InfimumAlgebra)(m::FiniteSubset{<:Real}) = minimum(m.elements)

"""
    SupremumAlgebra()

The maximum of a non-empty finite set of reals: the other algebra of the
[`PowersetMonad`](@ref) on the reals, behind the best case (maximax) and, applied to
regrets, behind minimax regret.
"""
struct SupremumAlgebra <: StructureMap end
(::SupremumAlgebra)(m::FiniteSubset{<:Real}) = maximum(m.elements)

"""
    LowerExpectationAlgebra()

The lower expectation over a credal set, `α(c) = min_{p ∈ c} Σ_x p(x) x`, attained
at a generator: an algebra of the [`CredalMonad`](@ref), behind Γ-maximin.
"""
struct LowerExpectationAlgebra <: StructureMap end
function (::LowerExpectationAlgebra)(c::CredalHull{<:Real})
    return minimum(ExpectationAlgebra()(p) for p in c.generators)
end

"""
    UpperExpectationAlgebra()

The upper expectation over a credal set, `max_{p ∈ c} Σ_x p(x) x`: an algebra of the
[`CredalMonad`](@ref).
"""
struct UpperExpectationAlgebra <: StructureMap end
function (::UpperExpectationAlgebra)(c::CredalHull{<:Real})
    return maximum(ExpectationAlgebra()(p) for p in c.generators)
end

"""
    TotalRewardAlgebra()

The algebra of the [`RewardMonad`](@ref) on the reals: the expected total reward
`α(m) = Σ m(r, v) (r + v)`, the reward collected so far plus the value of the
outcome.
"""
struct TotalRewardAlgebra <: StructureMap end
function (::TotalRewardAlgebra)(m::FiniteDistribution{<:Tuple{Real,Real}})
    return sum(p * (r + v) for ((r, v), p) in _pairs(m))
end

"""
    TransportedAlgebra(base, φ, φ_inverse; translation_equivariant=false)

The algebra `φ⁻¹ ∘ base ∘ T φ` obtained by carrying the algebra `base` along an
increasing bijection `φ` of the reals. With `base` the expectation and `φ` a utility
function this is the **certainty equivalent**, `u⁻¹(E u(X))`: it is again an
Eilenberg-Moore algebra, and monotone, so it admits backward induction on terminal
payoffs. It commutes with adding a constant only for special `φ` (the exponential
family); say so with `translation_equivariant = true` (see
[`is_translation_equivariant`](@ref)). The caller is responsible for `φ_inverse`
being the inverse of `φ` and for `φ` being increasing.
"""
struct TransportedAlgebra{A<:StructureMap,F,G} <: StructureMap
    base::A
    φ::F
    φ_inverse::G
    translation_equivariant::Bool
end
function TransportedAlgebra(base::StructureMap, φ, φ_inverse;
                            translation_equivariant::Bool=false)
    return TransportedAlgebra(base, φ, φ_inverse, translation_equivariant)
end
(α::TransportedAlgebra)(m) = α.φ_inverse(α.base(monad_map(monad_of(α.base), α.φ, m)))

function _unit_level(α::Real, what)
    return 0 <= α <= 1 ? α :
           throw(ArgumentError("$what must lie in [0, 1], got $α"))
end
function _tail_level(α::Real, what)
    return 0 < α <= 1 ? α :
           throw(ArgumentError("$what must lie in (0, 1], got $α"))
end

"""
    HurwiczMap(α)

The Hurwicz criterion on a non-empty finite set of reals,
`α · max + (1 − α) · min`, with `α` in `[0, 1]` the weight on the best outcome (the
convention of DecisionAnalysis's `Hurwicz`). A structure map of the
[`PowersetMonad`](@ref) that is **not** an algebra unless `α` is 0 or 1.
"""
struct HurwiczMap{T<:Real} <: StructureMap
    α::T
    HurwiczMap(α::T) where {T<:Real} = new{T}(_unit_level(α, "the optimism index α"))
end
function (h::HurwiczMap)(m::FiniteSubset{<:Real})
    return h.α * maximum(m.elements) + (1 - h.α) * minimum(m.elements)
end

"""
    LaplaceMap()

The unweighted mean of the **distinct** values in a non-empty finite set of reals. A
structure map of the [`PowersetMonad`](@ref) that is **not** an algebra: the mean of
means is not the mean of the union.

It is not the Laplace rule of a decision table. A set has no multiplicities, so when
an action pays the same in two states the set of its payoffs has one element where
the table has two columns, and the two means differ. The Laplace criterion
(DecisionAnalysis's `Laplace`) is the **expectation under the uniform distribution on
the states**: it lives in the [`DistributionMonad`](@ref), reached from the set of
states by a map that is not a monad morphism, and [`rule_selection`](@ref) exhibits
it that way. `LaplaceMap` is what `Laplace()` means as a criterion for a
[`SequentialProblem`](@ref) whose chance stages are sets.
"""
struct LaplaceMap <: StructureMap end
function (::LaplaceMap)(m::FiniteSubset{<:Real})
    xs = m.elements
    return eltype(xs) <: Integer ? sum(xs) // length(xs) : sum(xs) / length(xs)
end

"""
    CVaRMap(α)

Conditional value at risk at level `α` in `(0, 1]` of a distribution on the reals:
the mean of the worst `α` share of the probability mass (the convention of
DecisionAnalysis's `CVaR`: a tail mean of a utility, so higher is better). A
structure map of the [`DistributionMonad`](@ref) that is **not** an algebra for
`α < 1`: the CVaR of a mixture is not the CVaR of the components' CVaRs, which is
why it cannot be optimised stage by stage.
"""
struct CVaRMap{T<:Real} <: StructureMap
    α::T
    CVaRMap(α::T) where {T<:Real} = new{T}(_tail_level(α, "the tail level α"))
end
function (c::CVaRMap)(m::FiniteDistribution{<:Real})
    order = sortperm(m.outcomes)
    remaining = c.α * one(eltype(m.probabilities))
    total = zero(promote_type(eltype(m.outcomes), eltype(m.probabilities), typeof(c.α)))
    for i in order
        mass = min(m.probabilities[i], remaining)
        total += mass * m.outcomes[i]
        remaining -= mass
        remaining > 0 || break
    end
    return total / (c.α - max(remaining, zero(remaining)))
end

"""
    QuantileMap(α)

The lower `α`-quantile, `α` in `(0, 1]`, of a distribution on the reals: the
smallest outcome `x` with `P(X ≤ x) ≥ α`. A structure map of the
[`DistributionMonad`](@ref) that is **not** an algebra.
"""
struct QuantileMap{T<:Real} <: StructureMap
    α::T
    QuantileMap(α::T) where {T<:Real} = new{T}(_tail_level(α, "the level α"))
end
function (q::QuantileMap)(m::FiniteDistribution{<:Real})
    order = sortperm(m.outcomes)
    cumulative = zero(eltype(m.probabilities))
    for i in order
        cumulative += m.probabilities[i]
        cumulative >= q.α && return m.outcomes[i]
    end
    return m.outcomes[last(order)]
end

"""
    AlphaMaxminMap(α)

The α-maxmin criterion on a credal set of distributions on the reals,
`α · lower + (1 − α) · upper` expectation, `α` in `[0, 1]` the weight on the lower
one (the convention of DecisionAnalysis's `AlphaMaxmin`). A structure map of the
[`CredalMonad`](@ref) that is **not** an algebra unless `α` is 0 or 1.
"""
struct AlphaMaxminMap{T<:Real} <: StructureMap
    α::T
    function AlphaMaxminMap(α::T) where {T<:Real}
        return new{T}(_unit_level(α, "the ambiguity-aversion index α"))
    end
end
function (a::AlphaMaxminMap)(c::CredalHull{<:Real})
    return a.α * LowerExpectationAlgebra()(c) + (1 - a.α) * UpperExpectationAlgebra()(c)
end

"""
    SmoothAmbiguityMap(η; weights=nothing)
    SmoothAmbiguityMap(phi, inverse; weights=nothing)

The smooth ambiguity criterion of Klibanoff, Marinacci & Mukerji (2005) on a credal set
of distributions on the reals (the structure map of DecisionAnalysis's `SmoothAmbiguity`):
`ϕ⁻¹(Σ_k μ_k ϕ(E_{p_k}[X]))`, where `p_k` are the generating distributions of the
[`CredalHull`](@ref) and `μ` are second-order prior weights (uniform by default).

With a real ambiguity-aversion parameter `η`, `ϕ(x) = -exp(-η x)` (evaluated with a
shift-invariant log-sum-exp, collapsing to the weighted mean at `η = 0`). A structure map
of the [`CredalMonad`](@ref) that is **not** an Eilenberg-Moore algebra in general.
"""
struct SmoothAmbiguityMap{F,G,W} <: StructureMap
    phi::F
    inverse::G
    weights::W
end
function SmoothAmbiguityMap(η::Real; weights=nothing)
    isfinite(η) || throw(ArgumentError("SmoothAmbiguityMap η must be finite, got $η"))
    w = weights === nothing ? nothing : _check_smooth_weights(weights)
    return SmoothAmbiguityMap(Float64(η), nothing, w)
end
function SmoothAmbiguityMap(phi::Function, inverse::Function; weights=nothing)
    w = weights === nothing ? nothing : _check_smooth_weights(weights)
    return SmoothAmbiguityMap(phi, inverse, w)
end
function _check_smooth_weights(weights)
    w = Float64.(collect(weights))
    (!isempty(w) && all(x -> isfinite(x) && x >= 0, w) && sum(w) > 0) ||
        throw(ArgumentError("SmoothAmbiguityMap weights must be finite, nonnegative, and have positive sum"))
    return w ./ sum(w)
end
function (s::SmoothAmbiguityMap)(c::CredalHull{<:Real})
    E = ExpectationAlgebra()
    vals = Float64[Float64(E(g)) for g in c.generators]
    K = length(vals)
    μ = if s.weights === nothing
        fill(1.0 / K, K)
    else
        length(s.weights) == K ||
            throw(ArgumentError("SmoothAmbiguityMap received $(length(s.weights)) " *
                                "second-order weights for $K generating priors"))
        s.weights
    end
    if s.phi isa Float64
        η = s.phi
        iszero(η) && return sum(μ[k] * vals[k] for k in 1:K)
        α = -η
        xstar = α < 0 ? minimum(vals[k] for k in 1:K if μ[k] > 0) :
                maximum(vals[k] for k in 1:K if μ[k] > 0)
        total = sum(μ[k] * exp(α * (vals[k] - xstar)) for k in 1:K if μ[k] > 0)
        return xstar + log(total) / α
    end
    return s.inverse(sum(μ[k] * s.phi(vals[k]) for k in 1:K))
end

"""
    RestrictedMap(morphism, α)

The structure map `α ∘ τ` of the source monad of the monad morphism `τ`: the
aggregator `α` read through `τ`. Built by [`restrict_algebra`](@ref). When `α` is an
algebra, so is the result.
"""
struct RestrictedMap{M,A<:StructureMap} <: StructureMap
    morphism::M
    α::A
end
(r::RestrictedMap)(m) = r.α(r.morphism(m))

"""
    monad_of(α::StructureMap) -> UncertaintyMonad

The monad whose values the structure map `α` summarises.
"""
monad_of(::IdentityAlgebra) = IdentityMonad()
monad_of(::Union{ExpectationAlgebra,CVaRMap,QuantileMap}) = DistributionMonad()
monad_of(::Union{InfimumAlgebra,SupremumAlgebra,HurwiczMap,LaplaceMap}) = PowersetMonad()
function monad_of(::Union{LowerExpectationAlgebra,UpperExpectationAlgebra,AlphaMaxminMap,
                          SmoothAmbiguityMap})
    return CredalMonad()
end
monad_of(::TotalRewardAlgebra) = RewardMonad()
monad_of(α::TransportedAlgebra) = monad_of(α.base)
monad_of(r::RestrictedMap) = r.morphism.source

"""
    is_algebra(α::StructureMap) -> Bool

Whether `α` is an Eilenberg-Moore algebra of its monad: `α(η x) = x` and
`α(μ M) = α(T α M)`. This is a declared property of each type (the statements are
theorems C2, C4 and C5 of the Lean development), and
[`algebra_unit_defect`](@ref) and [`algebra_multiplication_defect`](@ref) check it
numerically on given inputs.
"""
is_algebra(::StructureMap) = false
function is_algebra(::Union{IdentityAlgebra,ExpectationAlgebra,InfimumAlgebra,
                            SupremumAlgebra,
                            LowerExpectationAlgebra,UpperExpectationAlgebra,
                            TotalRewardAlgebra})
    return true
end
is_algebra(α::TransportedAlgebra) = is_algebra(α.base)
is_algebra(h::HurwiczMap) = iszero(h.α) || isone(h.α)
is_algebra(a::AlphaMaxminMap) = iszero(a.α) || isone(a.α)
is_algebra(c::CVaRMap) = isone(c.α)
is_algebra(r::RestrictedMap) = is_algebra(r.α)

"""
    is_monotone(α::StructureMap) -> Bool

Whether making every outcome at least as good never lowers the summary:
`α(T f m) ≤ α(T g m)` whenever `f ≤ g` pointwise. Every structure map of this
package is monotone ([`TransportedAlgebra`](@ref) under its stated assumption that
`φ` is increasing); the function exists because monotonicity is one of the two
conditions for backward induction and a user-defined map must declare it.
"""
is_monotone(::StructureMap) = true

"""
    is_translation_equivariant(α::StructureMap) -> Bool

Whether adding a constant to every outcome adds it to the summary,
`α(T (c + ·) m) = c + α(m)`: "adding a stage reward is an algebra map" (the third
condition of Brede and Botta 2021). It holds for every structure map of this package
except a [`TransportedAlgebra`](@ref) (a certainty equivalent), where it holds only
for special transports and must be declared.

The backward induction of this package works on the payoff of whole histories, so
it does not need this property; a dynamic programme that adds rewards stage by stage
does.
"""
is_translation_equivariant(::StructureMap) = true
is_translation_equivariant(s::SmoothAmbiguityMap) = s.phi isa Float64
is_translation_equivariant(α::TransportedAlgebra) = α.translation_equivariant
is_translation_equivariant(r::RestrictedMap) = is_translation_equivariant(r.α)

"""
    admits_backward_induction(α::StructureMap) -> Bool
    admits_backward_induction(rule) -> Bool

Whether a sequential problem under this criterion can be solved from the last stage
backwards with the guarantee that the result is a best policy:
`is_algebra(α) && is_monotone(α)`.

| criterion | admits backward induction |
|:--|:--|
| expectation (`MaxExpectedUtility`) | yes |
| worst case (`Maximin`), best case (`Maximax`) | yes |
| lower and upper expectation (`GammaMaximin`) | yes, for the sequential (rectangular) composite of the credal kernels |
| certainty equivalent ([`TransportedAlgebra`](@ref)) | yes, on terminal payoffs |
| Hurwicz, Laplace | no: not an algebra |
| CVaR, quantile | no: not an algebra |
| α-maxmin | no: not an algebra |
| minimax regret | no: regret depends on the menu, and the menu of a subproblem is not the menu of the whole problem |

For a rule of DecisionAnalysis the answer is that of its aggregator, and `false`
for any rule with a regret transform. The two counterexamples are in the test suite
and in the vignette on backward induction (theorem C7c of the Lean development).
"""
admits_backward_induction(α::StructureMap) = is_algebra(α) && is_monotone(α)

"""
    algebra_unit_defect(α::StructureMap, x::Real)

`α(η x) − x`: zero when `α` satisfies the unit law of an Eilenberg-Moore algebra at
`x`.
"""
algebra_unit_defect(α::StructureMap, x::Real) = α(monad_unit(monad_of(α), x)) - x

"""
    algebra_multiplication_defect(α::StructureMap, mm)

`α(μ mm) − α(T α mm)` for an uncertain value of uncertain reals `mm ∈ T T ℝ`: zero
when `α` satisfies the multiplication law of an Eilenberg-Moore algebra at `mm`.
Summarise the flattened value, or summarise each inner value and then the results:
an algebra gives the same number both ways.

```jldoctest
julia> inner1 = FiniteDistribution([0, 10], [1 // 2, 1 // 2]);

julia> inner2 = FiniteDistribution([4], [1]);

julia> mm = FiniteDistribution([inner1, inner2], [1 // 2, 1 // 2]);

julia> algebra_multiplication_defect(ExpectationAlgebra(), mm)
0//1

julia> algebra_multiplication_defect(CVaRMap(1 // 2), mm)
2//1
```
"""
function algebra_multiplication_defect(α::StructureMap, mm)
    M = monad_of(α)
    return α(monad_join(M, mm)) - α(monad_map(M, α, mm))
end

# Monad morphisms
# ---------------

"""
    MonadMorphism(source, target)

A monad morphism `τ : S ⇒ T` between two uncertainty monads, applied to a value by
calling it: `τ(m)`. Build one with [`monad_morphism`](@ref). The morphisms offered:

| from | to | what it does |
|:--|:--|:--|
| identity | any | the unit: a certain value as a point mass, a singleton, ... |
| distributions | credal sets | the set containing only that distribution |
| non-empty sets | credal sets | every distribution on the set (the hull of its point masses) |
| distributions | non-empty sets | the support |

and the identity of each monad. They satisfy `τ ∘ η = η` and
`τ ∘ μ = μ ∘ τ ∘ S τ` (tested on random inputs; for a credal target up to
[`same_hull`](@ref)). There is none from credal sets to distributions or from sets
to distributions: a set of possibilities does not determine probabilities.

**The support is lax for the algebras.** As a map of monads the support commutes
with units and chaining (the support of a mixture is the union of the supports).
It does not carry the expectation to the worst case with equality: the worst case
over the support is a lower bound on the expectation,
`min over the support ≤ expectation ≤ max over the support` (Lean
`pullbackMin_le_pullbackD`). Replacing an expectation box by a worst-case box is a
bound, not a rewrite.

**Two routes from distributions to credal sets differ.** The direct morphism sends
`p` to `{p}`. Going through the support sends it to every distribution on the
support of `p`, a much larger set. `monad_morphism(DistributionMonad(),
CredalMonad())` is the direct one.
"""
struct MonadMorphism{S<:UncertaintyMonad,T<:UncertaintyMonad}
    source::S
    target::T
end

(τ::MonadMorphism{S,S})(m) where {S<:UncertaintyMonad} = m
(τ::MonadMorphism{IdentityMonad,T})(x) where {T<:UncertaintyMonad} = monad_unit(τ.target, x)
(τ::MonadMorphism{IdentityMonad,IdentityMonad})(x) = x
(::MonadMorphism{DistributionMonad,CredalMonad})(m::FiniteDistribution) = CredalHull([m])
function (::MonadMorphism{PowersetMonad,CredalMonad})(m::FiniteSubset)
    return CredalHull([_distribution([x], [1]) for x in m.elements])
end
function (::MonadMorphism{DistributionMonad,PowersetMonad})(m::FiniteDistribution)
    return FiniteSubset(m.outcomes)
end

const _MORPHISMS = Set([(DistributionMonad, CredalMonad), (PowersetMonad, CredalMonad),
                        (DistributionMonad, PowersetMonad)])

"""
    has_monad_morphism(source, target) -> Bool

Whether [`monad_morphism`](@ref) offers a morphism between the two monads.
"""
function has_monad_morphism(S::UncertaintyMonad, T::UncertaintyMonad)
    return S == T || (S isa IdentityMonad && !(T isa RewardMonad)) ||
           (typeof(S), typeof(T)) in _MORPHISMS
end

"""
    monad_morphism(source, target) -> MonadMorphism

The monad morphism from `source` to `target` (see [`MonadMorphism`](@ref) for the
list). Throws [`MonadMismatchError`](@ref) when there is none.

```jldoctest
julia> τ = monad_morphism(PowersetMonad(), CredalMonad());

julia> LowerExpectationAlgebra()(τ(FiniteSubset([3, 1, 2])))   # lower expectation = minimum
1
```
"""
function monad_morphism(S::UncertaintyMonad, T::UncertaintyMonad)
    has_monad_morphism(S, T) ||
        throw(MonadMismatchError(:monad_morphism, T, S,
                                 "there is no monad morphism from $S to $T"))
    return MonadMorphism(S, T)
end

"""
    restrict_algebra(τ::MonadMorphism, α::StructureMap) -> RestrictedMap

The structure map `α ∘ τ` of the source monad of `τ`. Restricting an algebra along a
monad morphism gives an algebra, and the standard ones restrict to each other: the
lower expectation along distributions → credal sets is the expectation, and along
sets → credal sets is the minimum. This is the sense in which a belief and an
aggregator of different monads fit together when a morphism connects them.
"""
function restrict_algebra(τ::MonadMorphism, α::StructureMap)
    monad_of(α) == τ.target ||
        throw(MonadMismatchError(:restrict_algebra, τ.target, monad_of(α),
                                 "the structure map is not on the target of the morphism"))
    return RestrictedMap(τ, α)
end

# Core aggregators and beliefs as structure maps and monad values
# ---------------------------------------------------------------

"""
    structure_map(aggregator) -> StructureMap

The structure map that a DecisionAnalysis aggregator applies:
`Expectation` → [`ExpectationAlgebra`](@ref), `WorstCase` → [`InfimumAlgebra`](@ref),
`BestCase` → [`SupremumAlgebra`](@ref), `Hurwicz` → [`HurwiczMap`](@ref),
`Laplace` → [`LaplaceMap`](@ref), `LowerExpectation` →
[`LowerExpectationAlgebra`](@ref), `UpperExpectation` →
[`UpperExpectationAlgebra`](@ref), `AlphaMaxmin` → [`AlphaMaxminMap`](@ref),
`CVaR` → [`CVaRMap`](@ref), `Quantile` → [`QuantileMap`](@ref). A structure map is
returned unchanged.
"""
structure_map(α::StructureMap) = α
structure_map(::Expectation) = ExpectationAlgebra()
structure_map(::WorstCase) = InfimumAlgebra()
structure_map(::BestCase) = SupremumAlgebra()
structure_map(a::Hurwicz) = HurwiczMap(a.α)
structure_map(::Laplace) = LaplaceMap()
structure_map(::LowerExpectation) = LowerExpectationAlgebra()
structure_map(::UpperExpectation) = UpperExpectationAlgebra()
structure_map(a::AlphaMaxmin) = AlphaMaxminMap(a.α)
structure_map(a::SmoothAmbiguity) = SmoothAmbiguityMap(a.phi, a.inverse, a.weights)
structure_map(a::CVaR) = CVaRMap(a.α)
structure_map(a::Quantile) = QuantileMap(a.α)

function admits_backward_induction(a::AbstractAggregator)
    return admits_backward_induction(structure_map(a))
end
function admits_backward_induction(rule::DecisionRule)
    return rule.metric.transform isa IdentityTransform && rule.selector isa Optimize &&
           admits_backward_induction(rule.metric.summary)
end
admits_backward_induction(::AbstractRule) = false

"""
    belief_monad(belief) -> UncertaintyMonad

The monad a DecisionAnalysis belief is a value of: `PointBelief` →
[`IdentityMonad`](@ref); `FiniteBelief` and `SampleBelief` →
[`DistributionMonad`](@ref); `ScenarioSet` → [`PowersetMonad`](@ref); `CredalSet` →
[`CredalMonad`](@ref).
"""
belief_monad(::PointBelief) = IdentityMonad()
belief_monad(::Union{FiniteBelief,SampleBelief}) = DistributionMonad()
belief_monad(::ScenarioSet) = PowersetMonad()
belief_monad(::CredalSet) = CredalMonad()

# A distribution over state labels that keeps the states of probability zero out of the
# support (as every `FiniteDistribution` does).
_state_distribution(states, p) = FiniteDistribution(states, p)

"""
    belief_value(belief, [monad]; states=nothing)

A DecisionAnalysis belief as a value of an uncertainty monad over its state labels:
a `Symbol`, a [`FiniteDistribution`](@ref), a [`FiniteSubset`](@ref) or a
[`CredalHull`](@ref). Without `monad` it is the belief's own
([`belief_monad`](@ref)). With another monad the belief is carried along the monad
morphism when there is one ([`monad_morphism`](@ref)), with **one deliberate
exception that follows DecisionAnalysis**: a `FiniteBelief`, `SampleBelief` or
`CredalSet` read as a set of possibilities ([`PowersetMonad`](@ref)) is the set of
**all** its states, including states of probability zero, because that is the set
the state-wise rules of DecisionAnalysis (`Maximin`, `Maximax`, `Hurwicz`,
`Laplace`, `MinimaxRegret`) range over. It is not the support morphism, and for a
credal set no monad morphism to sets is offered at all. `states` gives the states of
the payoff table for a `PointBelief` read as a distribution or a set. Anything else
throws [`MonadMismatchError`](@ref).
"""
belief_value(b::AbstractBelief; kw...) = belief_value(b, belief_monad(b); kw...)
belief_value(b::PointBelief, ::IdentityMonad; states=nothing) = b.state
function belief_value(b::PointBelief, M::UncertaintyMonad; states=nothing)
    M isa RewardMonad && throw(MonadMismatchError(:belief_value, belief_monad(b), M,
                                                  "a belief carries no reward"))
    return monad_morphism(IdentityMonad(), M)(b.state)
end
function belief_value(b::Union{FiniteBelief,SampleBelief}, ::DistributionMonad;
                      states=nothing)
    return _state_distribution(state_labels(b), probabilities(b))
end
function belief_value(b::Union{FiniteBelief,SampleBelief,CredalSet}, ::PowersetMonad;
                      states=nothing)
    return FiniteSubset(state_labels(b))
end
function belief_value(b::Union{FiniteBelief,SampleBelief}, ::CredalMonad; states=nothing)
    return CredalHull([_state_distribution(state_labels(b), probabilities(b))])
end
belief_value(b::ScenarioSet, ::PowersetMonad; states=nothing) = FiniteSubset(b.states)
function belief_value(b::ScenarioSet, ::CredalMonad; states=nothing)
    return monad_morphism(PowersetMonad(), CredalMonad())(FiniteSubset(b.states))
end
function belief_value(b::CredalSet, ::CredalMonad; states=nothing)
    return CredalHull([_state_distribution(b.states, p) for p in b.points])
end
function belief_value(b::AbstractBelief, M::UncertaintyMonad; states=nothing)
    return throw(MonadMismatchError(:belief_value, belief_monad(b), M,
                                    "there is no monad morphism from the belief's monad to " *
                                    "the one asked for"))
end

# Kleisli maps
# ------------

"""
    KleisliMap(monad, dom, codom, images)

A kernel in the uncertainty monad `T`: a map from the finite set `dom` to uncertain
values over the finite set `codom`, stored as one value of `T(codom)` per element of
`dom` (`images[i]` for `dom[i]`). For the [`DistributionMonad`](@ref) it is a
stochastic kernel, for the [`IdentityMonad`](@ref) a function, for the
[`PowersetMonad`](@ref) a total multivalued map, for the [`CredalMonad`](@ref) a
credal kernel. Call it on an element of `dom` to get the image.

Build one from a column-stochastic matrix or a `FiniteKernel` with
[`kleisli_map`](@ref); compose with [`kleisli_compose`](@ref); pull a utility back
along it with [`value_pullback`](@ref).
"""
struct KleisliMap{M<:UncertaintyMonad,X,Y}
    monad::M
    dom::Vector{X}
    codom::Vector{Y}
    images::Vector{Any}
    function KleisliMap(monad::M, dom::AbstractVector, codom::AbstractVector,
                        images::AbstractVector) where {M<:UncertaintyMonad}
        length(dom) == length(images) ||
            throw(ArgumentError("$(length(dom)) points in the domain for " *
                                "$(length(images)) images"))
        allunique(dom) || throw(ArgumentError("the points of the domain repeat"))
        allunique(codom) || throw(ArgumentError("the points of the codomain repeat"))
        for m in images, y in _outcomes(monad, m)
            any(isequal(y), codom) ||
                throw(ArgumentError("the image contains $y, which is not a point of " *
                                    "the codomain"))
        end
        return new{M,eltype(dom),eltype(codom)}(monad, collect(dom), collect(codom),
                                                collect(Any, images))
    end
end

_outcomes(::IdentityMonad, m) = (m,)
_outcomes(::DistributionMonad, m::FiniteDistribution) = m.outcomes
_outcomes(::PowersetMonad, m::FiniteSubset) = m.elements
function _outcomes(::CredalMonad, m::CredalHull)
    return unique(reduce(vcat, [g.outcomes for g in m.generators]))
end
_outcomes(::RewardMonad, m::FiniteDistribution) = unique(last.(m.outcomes))
function _outcomes(M::UncertaintyMonad, m)
    return throw(MonadMismatchError(:KleisliMap, M, typeof(m),
                                    "the image is not a value of the monad"))
end

function (f::KleisliMap)(x)
    i = findfirst(isequal(x), f.dom)
    i === nothing && throw(ArgumentError("$x is not a point of the domain"))
    return f.images[i]
end

function Base.show(io::IO, f::KleisliMap)
    return print(io, "KleisliMap(", nameof(typeof(f.monad)), ", ", length(f.dom), " → ",
                 length(f.codom), " points)")
end

"""
    kleisli_identity(monad, points) -> KleisliMap

The identity kernel on a finite set: every point goes to the certain value
[`monad_unit`](@ref) of itself.
"""
function kleisli_identity(M::UncertaintyMonad, points::AbstractVector)
    return KleisliMap(M, points, points, [monad_unit(M, x) for x in points])
end

"""
    kleisli_compose(f::KleisliMap, g::KleisliMap, hs...) -> KleisliMap

Sequential composition in diagrammatic order (first `f`, then `g`):
`(f ; g)(x) = monad_bind(f(x), g)`. For distributions this is the product of the
stochastic matrices, and agrees with `compose_kernel` of FiniteKernels. For credal
kernels it is the sound, loose composite described at [`CredalMonad`](@ref). The two
maps must be of the same monad ([`MonadMismatchError`](@ref)) and the codomain of
`f` must be the domain of `g` (`ArgumentError`).
"""
function kleisli_compose(f::KleisliMap, g::KleisliMap)
    f.monad == g.monad ||
        throw(MonadMismatchError(:kleisli_compose, f.monad, g.monad,
                                 "carry one map along a monad morphism first " *
                                 "(`change_monad`)"))
    f.codom == g.dom ||
        throw(ArgumentError("the codomain of the first map is not the domain of the " *
                            "second"))
    return KleisliMap(f.monad, f.dom, g.codom,
                      [monad_bind(f.monad, m, g) for m in f.images])
end
function kleisli_compose(f::KleisliMap, g::KleisliMap, h::KleisliMap, hs::KleisliMap...)
    return kleisli_compose(kleisli_compose(f, g), h, hs...)
end

"""
    change_monad(τ::MonadMorphism, f::KleisliMap) -> KleisliMap

The Kleisli map `x ↦ τ(f(x))` of the target monad of `τ`: a function as a stochastic
kernel, a stochastic kernel as a credal kernel, and so on. It preserves identities
and composition because `τ` is a monad morphism.
"""
function change_monad(τ::MonadMorphism, f::KleisliMap)
    f.monad == τ.source ||
        throw(MonadMismatchError(:change_monad, τ.source, f.monad,
                                 "the map is not of the source monad of the morphism"))
    return KleisliMap(τ.target, f.dom, f.codom, [τ(m) for m in f.images])
end

"""
    kleisli_map(K::AbstractMatrix; dom=1:size(K, 2), codom=1:size(K, 1)) -> KleisliMap
    kleisli_map(k::FiniteKernel) -> KleisliMap
    kleisli_map(f::Function, dom, codom) -> KleisliMap

A stochastic kernel as a Kleisli map of the [`DistributionMonad`](@ref). The matrix
is column-stochastic, `K[y, x] = P(y | x)` (outputs first, as in FiniteKernels and
as the likelihood of an `Experiment`). For a `FiniteKernel` the points are the
joint states of its domain and codomain (tuples of labels, in `joint_states`
order). A function becomes a Kleisli map of the [`IdentityMonad`](@ref).
"""
function kleisli_map(K::AbstractMatrix{<:Real}; dom=1:size(K, 2), codom=1:size(K, 1))
    size(K) == (length(codom), length(dom)) ||
        throw(ArgumentError("a $(size(K, 1))×$(size(K, 2)) matrix for " *
                            "$(length(codom)) codomain and $(length(dom)) domain points"))
    ys = collect(codom)
    return KleisliMap(DistributionMonad(), collect(dom), ys,
                      [FiniteDistribution(ys, K[:, j]) for j in axes(K, 2)])
end
function kleisli_map(k::FiniteKernel)
    return kleisli_map(kernel_matrix(k); dom=joint_states(k.dom),
                       codom=joint_states(k.codom))
end
function kleisli_map(f::Function, dom::AbstractVector, codom::AbstractVector)
    return KleisliMap(IdentityMonad(), dom, codom, [f(x) for x in dom])
end

"""
    stochastic_matrix(f::KleisliMap) -> Matrix

The column-stochastic matrix `K[y, x] = f(x)(y)` of a Kleisli map of the
[`DistributionMonad`](@ref), rows in the order of `f.codom` and columns in the order
of `f.dom`.
"""
function stochastic_matrix(f::KleisliMap{DistributionMonad})
    T = mapreduce(m -> eltype(m.probabilities), promote_type, f.images)
    return T[probability_of(m, y) for y in f.codom, m in f.images]
end
