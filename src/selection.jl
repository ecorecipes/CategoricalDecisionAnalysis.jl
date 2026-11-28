# Selection functions (component 4 of the plan and its revisions).
#
# Contract with the Lean development (theorems C7a to C7c). For an uncertainty monad
# `T` and a structure map `α : T ℝ → ℝ`, a selection function on a finite set `X` is
#
#     ε : (X → ℝ) → T X,          with quantifier   ε̄(q) = α( T q (ε q) ).
#
# The product of `ε` on `X` and a family `δ_x` on `Y` (Escardó and Oliva; in the
# monadic form of Hedges) is the selection function on pairs
#
#     (ε ⊗ δ)(q) = ε(f) >>= λx. T (y ↦ (x, y)) (b x)
#     where  b x = δ_x(y ↦ q(x, y))   and   f x = α( T (y ↦ q(x, y)) (b x) ).
#
# Backward induction on a finite sequential problem is the iterated product of one
# selection function per stage: the first maximiser at a decision stage (as a certain
# value), the stage's law at a chance stage (a constant selection function).

"""
    SelectionFunction(name, points, monad, algebra, choose)

A selection function `ε : (X → ℝ) → T X` on the finite set `points`, for the
uncertainty monad `monad` (`T`) and the structure map `algebra` (`α : T ℝ → ℝ`).
`choose` takes a function `q : X → ℝ` (an effect: what each point is worth) and
returns a value of `T X` (which point, or points, or distribution over points, is
selected). [`select`](@ref) applies it and [`quantifier`](@ref) gives the worth of
what is selected, `α(T q (ε q))`.

With the identity monad it is the classical selection function of Escardó and
Oliva, such as "a point where `q` is largest" ([`argmax_selection`](@ref)); its
quantifier is then the maximum. With the distribution monad a chance node is the
selection function that ignores `q` and returns its law
([`constant_selection`](@ref)); its quantifier is the expectation. That one type
covers both is what lets [`selection_product`](@ref) express a decision followed by
a chance node.
"""
struct SelectionFunction{M<:UncertaintyMonad,A<:StructureMap,F}
    name::Symbol
    points::Vector{Any}
    monad::M
    algebra::A
    choose::F
    function SelectionFunction(name::Symbol, points::AbstractVector, monad::M, algebra::A,
                               choose::F) where {M<:UncertaintyMonad,A<:StructureMap,F}
        isempty(points) && throw(ArgumentError("a selection function needs a point"))
        monad_of(algebra) == monad ||
            throw(MonadMismatchError(:SelectionFunction, monad, monad_of(algebra),
                                     "the structure map is not of the monad"))
        return new{M,A,F}(name, collect(Any, points), monad, algebra, choose)
    end
end

function Base.show(io::IO, ε::SelectionFunction)
    return print(io, "SelectionFunction(", ε.name, ", ", length(ε.points), " points, ",
                 nameof(typeof(ε.monad)), ", ", nameof(typeof(ε.algebra)), ")")
end

"""
    select(ε::SelectionFunction, q)
    select(r::RuleSelection, problem::DecisionProblem; atol=0, rtol) -> Vector{Symbol}

Apply a selection function. For a [`SelectionFunction`](@ref), `q` is a function on
its points or a vector aligned with them, and the result is a value of its monad
over the points. For a [`RuleSelection`](@ref) the result is the set of actions the
rule chooses in the problem, in table order (possibly empty for a satisficing rule),
with the tie tolerance of DecisionAnalysis's `decide`.
"""
select(ε::SelectionFunction, q) = ε.choose(_effect(q, ε.points))

"""
    quantifier(ε::SelectionFunction, q)
    quantifier(r::RuleSelection, problem::DecisionProblem)

The quantifier of a selection function at `q`: the worth of what it selects,
`α(T q (ε q))`. For [`argmax_selection`](@ref) it is `max q`, for a chance node
([`constant_selection`](@ref) of a distribution) the expectation of `q`. For a
[`RuleSelection`](@ref) it is the best score of the rule in the problem.
"""
function quantifier(ε::SelectionFunction, q)
    effect = _effect(q, ε.points)
    return ε.algebra(monad_map(ε.monad, effect, ε.choose(effect)))
end

function _best_points(points, q, better)
    values = [q(x) for x in points]
    best = values[1]
    for v in values
        better(v, best) && (best = v)
    end
    return [x for (x, v) in zip(points, values) if v == best]
end

"""
    argmax_selection(points; monad=IdentityMonad(), algebra=default_algebra(monad), ties=:first)

The selection function "a point of `points` where the effect is largest". With
`ties = :first` (the default) it returns the first maximiser in the order of
`points`, as a certain value of `monad` ([`monad_unit`](@ref)): nothing is random,
as in DecisionAnalysis. With `ties = :all`, for the [`PowersetMonad`](@ref) only, it
returns every maximiser as a [`FiniteSubset`](@ref) (the set-valued variant; the
algebra defaults to [`SupremumAlgebra`](@ref)). Its quantifier is the maximum.
"""
function argmax_selection(points::AbstractVector; monad::UncertaintyMonad=IdentityMonad(),
                          algebra::StructureMap=_argmax_algebra(monad), ties::Symbol=:first)
    return _extremum_selection(:argmax, points, monad, algebra, ties, >)
end
_argmax_algebra(M::UncertaintyMonad) = default_algebra(M)
_argmax_algebra(::PowersetMonad) = SupremumAlgebra()

"""
    argmin_selection(points; monad=IdentityMonad(), algebra=default_algebra(monad), ties=:first)

The selection function "a point where the effect is smallest", as
[`argmax_selection`](@ref); used on losses such as regret.
"""
function argmin_selection(points::AbstractVector; monad::UncertaintyMonad=IdentityMonad(),
                          algebra::StructureMap=default_algebra(monad), ties::Symbol=:first)
    return _extremum_selection(:argmin, points, monad, algebra, ties, <)
end

function _extremum_selection(name, points, monad, algebra, ties, better)
    ties in (:first, :all) ||
        throw(ArgumentError("`ties` must be :first or :all, got :$ties"))
    ties === :all && !(monad isa PowersetMonad) &&
        throw(ArgumentError("`ties = :all` returns a set of points and needs the " *
                            "PowersetMonad"))
    pts = collect(Any, points)
    choose = if ties === :first
        q -> monad_unit(monad, first(_best_points(pts, q, better)))
    else
        q -> FiniteSubset(_best_points(pts, q, better))
    end
    return SelectionFunction(name, pts, monad, algebra, choose)
end

"""
    constant_selection(points, value; monad, algebra=default_algebra(monad))

The selection function that ignores the effect and returns `value`, a value of
`monad` over `points`: a **chance node**. Nature does not choose by looking at the
payoffs. Its quantifier is the structure map applied to the effect: the expectation
for a distribution, the worst case for a set under the [`InfimumAlgebra`](@ref).
`monad` defaults to the one `value` is a value of.
"""
function constant_selection(points::AbstractVector, value;
                            monad::UncertaintyMonad=_value_monad(value),
                            algebra::StructureMap=default_algebra(monad))
    for x in _outcomes(monad, value)
        any(isequal(x), points) ||
            throw(ArgumentError("the value contains $x, which is not one of the points"))
    end
    return SelectionFunction(:chance, points, monad, algebra, _ -> value)
end
_value_monad(::FiniteDistribution) = DistributionMonad()
_value_monad(::FiniteSubset) = PowersetMonad()
_value_monad(::CredalHull) = CredalMonad()
_value_monad(::Any) = IdentityMonad()

"""
    selection_product(ε::SelectionFunction, δ) -> SelectionFunction

The product of selection functions: `ε` on `X` and `δ` on `Y`, where `δ` is a
selection function or a function `x ↦ δ_x` giving one for each point of `X` (the
later choice may depend on the earlier one). The result is a selection function on
the pairs `(x, y)`:

    (ε ⊗ δ)(q) = ε(f) >>= λx. T (y ↦ (x, y)) (b x),
    b x = δ_x(y ↦ q((x, y))),      f x = α( T (y ↦ q((x, y))) (b x) ).

In words: for each first move `x`, let the second stage select against what is left
of `q`; value `x` by what that selection is worth; let the first stage select
against those values; and return the joint play. Both factors must have the same
monad and structure map ([`MonadMismatchError`](@ref)).

With the identity monad this is the product of Escardó and Oliva, and iterating it
over the stages of a deterministic problem computes an optimal play by backward
induction (theorem C7a). With chance nodes it is the monadic product (Hedges); it
then computes a best policy **when the structure map is an Eilenberg-Moore algebra
and monotone** ([`admits_backward_induction`](@ref), theorem C7b) and not in general
otherwise. [`backward_induction`](@ref) builds the iterated product for a
[`SequentialProblem`](@ref) and enforces that condition.

```jldoctest
julia> first_move = argmax_selection([:a, :b]);

julia> second_move = argmax_selection([:c, :d]);

julia> worth = Dict((:a, :c) => 1, (:a, :d) => 4, (:b, :c) => 3, (:b, :d) => 2);

julia> select(selection_product(first_move, second_move), xy -> worth[xy])
(:a, :d)
```
"""
function selection_product(ε::SelectionFunction, δ)
    family = δ isa SelectionFunction ? (_ -> δ) : δ
    M, α = ε.monad, ε.algebra
    members = Dict{Any,SelectionFunction}()
    function member(x)
        return get!(members, x) do
            d = family(x)
            d isa SelectionFunction ||
                throw(ArgumentError("the family must return a SelectionFunction"))
            (d.monad == M && d.algebra == α) ||
                throw(MonadMismatchError(:selection_product, (M, α),
                                         (d.monad, d.algebra),
                                         "the factors of a product share one monad " *
                                         "and one structure map"))
            return d
        end
    end
    points = Any[(x, y) for x in ε.points for y in member(x).points]
    function choose(q)
        replies = Dict{Any,Any}()
        reply(x) = get!(() -> select(member(x), y -> q((x, y))), replies, x)
        f(x) = α(monad_map(M, y -> q((x, y)), reply(x)))
        return monad_bind(M, select(ε, f), x -> monad_map(M, y -> (x, y), reply(x)))
    end
    return SelectionFunction(Symbol(ε.name, :⊗), points, M, α, choose)
end

# Core rules as selection functions
# ---------------------------------

"""
    RuleSelection

A decision rule of DecisionAnalysis exhibited as a selection function on the
actions of a problem, with outcome type `ℝ^Θ` (an action's payoff in every state):
`(A → ℝ^Θ) → P(A)`. Built by [`rule_selection`](@ref). It has two parts that can be
changed independently, and changing them is how one rule becomes another:

- the **algebra box**: `transform` (`:identity`, `:regret` or `:relative_regret`,
  applied to the payoff table first) and `algebra` (a [`StructureMap`](@ref)) that
  summarises each action's row against the belief, read in the monad of the algebra
  ([`belief_value`](@ref)); with `uniform` set, the belief is replaced by the uniform
  distribution on the states it allows, which is how the Laplace rule is an
  expectation;
- the **selection box**: `selector`, which is `:optimize` (every best action; ties
  are all returned), a threshold `(:threshold, level)` (every action that is good
  enough), or one of the set-valued rules over a credal set, `:e_admissible`,
  `:maximal` and `:interval_dominance`.

[`select`](@ref) gives the chosen actions, [`rule_scores`](@ref) the score of every
feasible action and [`quantifier`](@ref) the best score. The scores and choices
equal those of DecisionAnalysis's `decide` for the same rule, which the test suite
checks for every rule on random problems; the two computations share no code beyond
the linear-programme solver used for E-admissibility.
"""
struct RuleSelection{A<:Union{Nothing,StructureMap}}
    name::Symbol
    transform::Symbol
    algebra::A
    selector::Any
    scenarios::Union{Nothing,Vector{Symbol}}
    uniform::Bool
end
function RuleSelection(name, transform, algebra, selector, scenarios)
    return RuleSelection(name, transform, algebra, selector, scenarios, false)
end

function Base.show(io::IO, r::RuleSelection)
    return print(io, "RuleSelection(", r.name, ": transform = ", r.transform,
                 ", algebra = ",
                 r.algebra === nothing ? "expectations over the credal set" :
                 nameof(typeof(r.algebra)), ", selector = ", r.selector, ")")
end

"""
    rule_selection(rule) -> RuleSelection
    rule_selection(; algebra, selector=:optimize, transform=:identity, name=:custom)

A rule of DecisionAnalysis as a [`RuleSelection`](@ref): any `DecisionRule` (and so
`MaxExpectedUtility`, `Maximin`, `Maximax`, `MinimaxRegret`, `GammaMaximin`,
`Satisfice` and every rule assembled from an aggregator, a transform and a
selector), and the set-valued `EAdmissible`, `Maximal` and `IntervalDominance`. The
keyword form assembles one from its two boxes directly; `algebra` may be a
[`StructureMap`](@ref) or a DecisionAnalysis aggregator. With a regret transform the
algebra is read on the side of losses, as in DecisionAnalysis: the worst case
([`InfimumAlgebra`](@ref)) of a regret is the largest regret, so minimax regret is
`rule_selection(; algebra=InfimumAlgebra(), transform=:regret)`.

`ParetoFront` compares several objectives and is exhibited by
[`pareto_selection`](@ref).

```jldoctest
julia> t = PayoffTable([:nothing, :levee, :relocate], [:low, :moderate, :high, :extreme],
                       [0 -10 -60 -150; -20 -20 -25 -90; -48 -48 -48 -48]);

julia> p = DecisionProblem(t, [1 // 2, 3 // 10, 3 // 20, 1 // 20]);

julia> select(rule_selection(MaxExpectedUtility()), p)
1-element Vector{Symbol}:
 :nothing

julia> select(rule_selection(; algebra=InfimumAlgebra()), p)     # swap the algebra box
1-element Vector{Symbol}:
 :relocate

julia> select(rule_selection(; algebra=InfimumAlgebra(), transform=:regret), p)  # worst regret
1-element Vector{Symbol}:
 :levee
```
"""
function rule_selection(rule::DecisionRule)
    transform = rule.metric.transform isa IdentityTransform ? :identity :
                rule.metric.transform isa RegretTransform ? :regret : :relative_regret
    selector = rule.selector isa Optimize ? :optimize : (:threshold, rule.selector.level)
    laplace = rule.metric.summary isa Laplace
    algebra = laplace ? ExpectationAlgebra() : structure_map(rule.metric.summary)
    return RuleSelection(rule.name, transform, algebra, selector, rule.metric.scenarios,
                         laplace)
end
function rule_selection(::EAdmissible)
    return RuleSelection(:EAdmissible, :identity, nothing,
                         :e_admissible, nothing)
end
rule_selection(::Maximal) = RuleSelection(:Maximal, :identity, nothing, :maximal, nothing)
function rule_selection(::IntervalDominance)
    return RuleSelection(:IntervalDominance, :identity, nothing, :interval_dominance,
                         nothing)
end
function rule_selection(r::StochasticDominance)
    return RuleSelection(:StochasticDominance, :identity, nothing,
                         (:stochastic_dominance, r.order), nothing)
end
function rule_selection(; algebra, selector=:optimize, transform::Symbol=:identity,
                        name::Symbol=:custom, scenarios=nothing, uniform::Bool=false)
    transform in (:identity, :regret, :relative_regret) ||
        throw(ArgumentError("`transform` must be :identity, :regret or " *
                            ":relative_regret, got :$transform"))
    _check_selector(selector)
    laplace = uniform || algebra isa Laplace
    return RuleSelection(name, transform,
                         algebra isa Laplace ? ExpectationAlgebra() :
                         structure_map(algebra),
                         selector, scenarios === nothing ? nothing : Symbol.(scenarios),
                         laplace)
end

function _check_selector(s)
    s === :optimize && return nothing
    s isa Tuple{Symbol,Real} && s[1] === :threshold && return nothing
    return throw(ArgumentError("`selector` must be :optimize or (:threshold, level), got $s"))
end

function admits_backward_induction(r::RuleSelection)
    return r.transform === :identity &&
           r.selector === :optimize && !r.uniform &&
           r.algebra !== nothing &&
           admits_backward_induction(r.algebra)
end

_rule_sense(r::RuleSelection) = r.transform === :identity ? :max : :min

function _transformed(r::RuleSelection, Q::AbstractMatrix)
    r.transform === :identity && return Q
    best = maximum(Q; dims=1)
    r.transform === :regret && return best .- Q
    j = findfirst(iszero, best)
    j === nothing ||
        throw(ArgumentError("relative regret is undefined: the best payoff in column " *
                            "$(j[2]) of the table is zero"))
    return (best .- Q) ./ abs.(best)
end

# The columns of the payoff table that the transform sees: the states the belief
# allows (regret is measured within them).
_allowed_states(b::ScenarioSet, states) = [s for s in states if s in b.states]
_allowed_states(b::PointBelief, states) = [b.state]
_allowed_states(::AbstractBelief, states) = states

_tie_rtol(::Type{T}) where {T} = _exact(T) ? 0 : sqrt(eps(float(T)))
_tie_tolerance(x, atol, rtol) = max(atol, rtol * maximum(abs, x; init=zero(rtol)))

"""
    rule_scores(r::RuleSelection, problem::DecisionProblem) -> Vector

The score of every feasible action of `problem` under the rule: the structure map
applied to the action's (transformed) payoffs pushed along the belief,
`α(T (θ ↦ M[a, θ]) m)`. With a regret transform the score is a loss, lower is
better, and it is computed as `−α(T (θ ↦ −M[a, θ]) m)`, the convention of
DecisionAnalysis (the worst case of a regret is the largest regret). The set-valued
rules over a credal set have no scalar score and return `nothing`.
"""
function rule_scores(r::RuleSelection, problem::DecisionProblem)
    r.algebra === nothing && return nothing
    p = r.scenarios === nothing ? problem : restrict_scenarios(problem, r.scenarios)
    states = p.payoff.states
    allowed = _allowed_states(p.belief, states)
    cols = [findfirst(==(s), states) for s in allowed]
    M = _transformed(r, p.payoff.Q[p.feasible, cols])
    column = Dict(s => j for (j, s) in enumerate(allowed))
    T = monad_of(r.algebra)
    if r.uniform
        p.belief isa SampleBelief &&
            throw(BeliefFormError(:Laplace, :SampleBelief,
                                  "an unweighted mean over the draws ignores their " *
                                  "weights; use the expectation"))
        uniform = FiniteDistribution(allowed, fill(1 // length(allowed), length(allowed)))
        m = T isa DistributionMonad ? uniform :
            monad_morphism(DistributionMonad(), T)(uniform)
    else
        m = belief_value(p.belief, T; states)
    end
    sign = _rule_sense(r) === :max ? 1 : -1
    return [sign * r.algebra(monad_map(T, θ -> sign * M[a, column[θ]], m))
            for a in axes(M, 1)]
end

# Expected utility of each feasible action at each generator of the belief, read as a
# credal set.
function _generator_expectations(problem::DecisionProblem)
    states = problem.payoff.states
    c = belief_value(problem.belief, CredalMonad(); states)
    column = Dict(s => j for (j, s) in enumerate(states))
    Q = problem.payoff.Q[problem.feasible, :]
    E = ExpectationAlgebra()
    return [E(monad_map(DistributionMonad(), θ -> Q[a, column[θ]], g))
            for a in axes(Q, 1), g in c.generators]
end

# E-admissibility of row `a` of `E` (expected utilities by action and generator): the
# optimum of  max t  s.t.  Σ_k λ_k (E[a, k] − E[b, k]) ≥ t ∀b,  λ in the simplex.
function _eadmissible_slack(E::AbstractMatrix, a::Integer; optimizer=nothing)
    T = _exact(eltype(E)) ? Rational{BigInt} : Float64
    n, K = size(E)
    model = JuMP.GenericModel{T}()
    λ = JuMP.@variable(model, [1:K], lower_bound = zero(T), base_name = "λ")
    t = JuMP.@variable(model, base_name = "t")
    simplex = JuMP.@constraint(model, sum(λ) == one(T))
    optimal = JuMP.@constraint(model, [b = 1:n],
                               sum((T(E[a, k]) - T(E[b, k])) * λ[k] for k in 1:K) - t >=
                               zero(T))
    JuMP.@objective(model, Max, t)
    sol = solve_program(DecisionProgram(:e_admissible_selection, model, (; λ, t),
                                        (; simplex, optimal)); optimizer)
    sol.status === :optimal || throw(LinearProgramError(:e_admissible_selection,
                                                        sol.status))
    return sol.objective
end

function select(r::RuleSelection, problem::DecisionProblem; atol::Real=0,
                rtol::Real=_tie_rtol(eltype(problem.payoff)), optimizer=nothing)
    actions = feasible_actions(problem)
    if r.algebra === nothing
        if r.selector isa Tuple{Symbol,Int} && r.selector[1] === :stochastic_dominance
            order = r.selector[2]
            states = problem.payoff.states
            # Validates that the belief is a single probability distribution (or point mass)
            m = belief_value(problem.belief, DistributionMonad(); states)
            p = [probability_of(m, s) for s in states]
            Q = problem.payoff.Q[problem.feasible, :]
            dom_fn = order == 1 ? fsd_dominates : ssd_dominates
            n = size(Q, 1)
            idx = findall(1:n) do a
                qa = view(Q, a, :)
                return !any(b -> b != a && dom_fn(view(Q, b, :), p, qa, p; strict=true,
                                                  atol=atol), 1:n)
            end
            return actions[idx]
        end
        E = _generator_expectations(problem)
        tol = _tie_tolerance(E, atol, rtol)
        n = size(E, 1)
        idx = if r.selector === :interval_dominance
            lower = vec(minimum(E; dims=2))
            findall(a -> maximum(view(E, a, :)) >= maximum(lower) - tol, 1:n)
        elseif r.selector === :maximal
            findall(a -> !any(b -> all(k -> E[b, k] - E[a, k] > tol, axes(E, 2)), 1:n), 1:n)
        else
            findall(a -> _eadmissible_slack(E, a; optimizer) >= -tol, 1:n)
        end
        return actions[idx]
    end
    scores = rule_scores(r, problem)
    sense = _rule_sense(r)
    if r.selector === :optimize
        tol = _tie_tolerance(scores, atol, rtol)
        best = sense === :max ? maximum(scores) : minimum(scores)
        keep = sense === :max ? (s -> s >= best - tol) : (s -> s <= best + tol)
        return actions[findall(keep, scores)]
    end
    level = r.selector[2]
    return actions[findall(sense === :max ? >=(level) : <=(level), scores)]
end

function quantifier(r::RuleSelection, problem::DecisionProblem)
    scores = rule_scores(r, problem)
    scores === nothing &&
        throw(ArgumentError("the set-valued rule $(r.name) has no scalar quantifier"))
    return _rule_sense(r) === :max ? maximum(scores) : minimum(scores)
end

"""
    pareto_selection(problems::AbstractVector{<:DecisionProblem}; algebra=ExpectationAlgebra(), atol=0, rtol)
        -> Vector{Symbol}

The Pareto front as a set-valued selection function with outcome type `ℝ^k`, one
coordinate per objective: the feasible actions whose vector of scores (one per
problem, each summarised by `algebra`) is not dominated by another action's
(at least as good in every objective and better in one). It reproduces
DecisionAnalysis's `decide(problems, ParetoFront())`. The problems must have the
same feasible actions.
"""
function pareto_selection(problems::AbstractVector{<:DecisionProblem};
                          algebra=ExpectationAlgebra(), atol::Real=0,
                          rtol::Real=mapreduce(p -> _tie_rtol(eltype(p.payoff)), max,
                                               problems; init=0))
    isempty(problems) && throw(ArgumentError("a Pareto front needs an objective"))
    actions = feasible_actions(first(problems))
    all(p -> feasible_actions(p) == actions, problems) ||
        throw(LabelMismatchError("feasible actions of the objectives of a Pareto front",
                                 actions, feasible_actions(last(problems))))
    r = rule_selection(; algebra)
    S = reduce(hcat, [rule_scores(r, p) for p in problems])
    tol = _tie_tolerance(S, atol, rtol)
    function dominates(b, a)
        return all(j -> S[b, j] >= S[a, j] - tol, axes(S, 2)) &&
               any(j -> S[b, j] > S[a, j] + tol, axes(S, 2))
    end
    return actions[findall(a -> !any(b -> dominates(b, a), axes(S, 1)), axes(S, 1))]
end

"""
    backward_induction_class(criterion) -> Symbol

What solving stage by stage means for a criterion (a [`StructureMap`](@ref), an
aggregator or rule of DecisionAnalysis, or a [`RuleSelection`](@ref)):

- `:flat`: the structure map is an Eilenberg-Moore algebra and monotone, so the
  stage-by-stage (nested) value **is** the criterion applied to the whole problem,
  and backward induction is optimal for it. Expectation, worst case, best case,
  lower and upper expectation, certainty equivalents.
- `:nested`: monotone but not an algebra. Backward induction is optimal for the
  nested rule, which is a different rule. CVaR, quantiles, Hurwicz, Laplace,
  α-maxmin.
- `:none`: no stage-by-stage form is offered: minimax regret (and any rule with a
  regret transform or a threshold selector), and a structure map that is not
  monotone.

[`admits_backward_induction`](@ref) is `true` exactly for `:flat`. The
classification is that of the Lean development (`Finite/Sequential.lean`,
`Finite/BackwardInductionFails.lean`): monotonicity alone makes backward induction
optimal for the nested value, and the algebra laws are what make the nested value
the flat one.
"""
function backward_induction_class(α::StructureMap)
    return !is_monotone(α) ? :none : is_algebra(α) ? :flat : :nested
end
backward_induction_class(a::AbstractAggregator) = backward_induction_class(structure_map(a))
function backward_induction_class(rule::DecisionRule)
    (rule.metric.transform isa IdentityTransform && rule.selector isa Optimize) ||
        return :none
    return backward_induction_class(rule.metric.summary)
end
backward_induction_class(::AbstractRule) = :none
function backward_induction_class(r::RuleSelection)
    (r.transform === :identity && r.selector === :optimize && r.algebra !== nothing) ||
        return :none
    return r.uniform ? :nested : backward_induction_class(r.algebra)
end

# Finite sequential problems
# --------------------------

"""
    DecisionStage(name, actions)

A stage of a [`SequentialProblem`](@ref) at which the decision-maker chooses one of
`actions`, knowing every earlier move.
"""
struct DecisionStage
    name::Symbol
    actions::Vector{Symbol}
    function DecisionStage(name, actions)
        as = Symbol[Symbol(a) for a in actions]
        (isempty(as) || !allunique(as)) &&
            throw(ArgumentError("a decision stage needs distinct actions"))
        return new(Symbol(name), as)
    end
end

"""
    ChanceStage(name, outcomes, law)

A stage of a [`SequentialProblem`](@ref) at which nature moves. `law` is a value of
the problem's monad over `outcomes` (a [`FiniteDistribution`](@ref) for a
probabilistic problem, a [`FiniteSubset`](@ref) when only the possible outcomes are
known, a [`CredalHull`](@ref) for a set of candidate distributions), or a function
of the history (the tuple of earlier moves) returning one, when what can happen
depends on what was done or seen before.
"""
struct ChanceStage{L}
    name::Symbol
    outcomes::Vector{Symbol}
    law::L
    function ChanceStage(name, outcomes, law::L) where {L}
        os = Symbol[Symbol(o) for o in outcomes]
        (isempty(os) || !allunique(os)) &&
            throw(ArgumentError("a chance stage needs distinct outcomes"))
        return new{L}(Symbol(name), os, law)
    end
end

_law(stage::ChanceStage{<:Function}, history::Tuple) = stage.law(history)
_law(stage::ChanceStage, ::Tuple) = stage.law
_options(stage::DecisionStage) = stage.actions
_options(stage::ChanceStage) = stage.outcomes

"""
    SequentialProblem(monad, stages, payoff)
    SequentialProblem(stages, payoff)

A finite sequential decision problem in stage form: a list of
[`DecisionStage`](@ref)s and [`ChanceStage`](@ref)s, played in order with every
earlier move known at every stage (perfect recall, full observation), and a `payoff`
function of the complete history (a tuple of one move per stage) counted in
individuals. `monad` is the uncertainty monad of the chance stages and defaults to
the [`DistributionMonad`](@ref).

A decision made on a noisy observation of a hidden state is written with the
observation first: a chance stage for the signal with its marginal law, the
decision, and then a chance stage for the state whose law is the posterior given
the signal ([`bayesian_inverse`](@ref)); that flip is the textbook decision tree.

Solve it with [`backward_induction`](@ref) (stage by stage, for criteria that admit
it) or [`policy_search`](@ref) (every policy, any criterion).
"""
struct SequentialProblem{M<:UncertaintyMonad,F}
    monad::M
    stages::Vector{Union{DecisionStage,ChanceStage}}
    payoff::F
    function SequentialProblem(monad::M, stages::AbstractVector,
                               payoff::F) where {M<:UncertaintyMonad,F}
        isempty(stages) && throw(ArgumentError("a sequential problem needs a stage"))
        all(s -> s isa Union{DecisionStage,ChanceStage}, stages) ||
            throw(ArgumentError("every stage is a DecisionStage or a ChanceStage"))
        allunique([s.name for s in stages]) ||
            throw(ArgumentError("the stage names repeat"))
        return new{M,F}(monad, collect(Union{DecisionStage,ChanceStage}, stages), payoff)
    end
end
function SequentialProblem(stages::AbstractVector, payoff)
    return SequentialProblem(DistributionMonad(), stages, payoff)
end

function Base.show(io::IO, p::SequentialProblem)
    return print(io, "SequentialProblem(", nameof(typeof(p.monad)), ", ",
                 join((string(s isa DecisionStage ? "decide " : "chance ", s.name)
                       for s in p.stages), " → "), ")")
end

# All histories of the first `k` stages.
function _histories(p::SequentialProblem, k::Integer)
    hs = Tuple[()]
    for stage in p.stages[1:k]
        hs = Tuple[(h..., x) for h in hs for x in _options(stage)]
    end
    return hs
end

"""
    SequentialSolution

What [`backward_induction`](@ref) and [`policy_search`](@ref) return. Fields:

- `criterion`: the name of the criterion.
- `value`: the value of the returned policy under the criterion, computed from the
  law of its plays (for minimax regret, its largest regret: lower is better).
- `policy`: a dictionary from histories at decision stages (tuples of earlier
  moves) to the action chosen there.
- `law`: the uncertain play under the policy, a value of the problem's monad over
  complete histories.
- `method`: `:backward_induction` or `:policy_search`.
- `label`: what the solution is. `:optimal`: the policy is best for the criterion
  applied to the whole problem. `:nested`: the criterion is monotone but not an
  algebra (CVaR, say) and the stage-by-stage answer was asked for; the policy is
  best for the **nested** rule, the criterion applied stage by stage, which is a
  different rule, and `recursion_value` is its nested value while `value` is what
  the policy is worth under the criterion applied to the whole problem.
  `:heuristic`: minimax regret solved stage by stage; no optimality is claimed.
- `recursion_value`: the value computed by the stage-by-stage recursion; equal to
  `value` when the label is `:optimal`, and `nothing` for minimax regret.
- `policies`: the number of policies examined (`policy_search`) or `nothing`.
"""
struct SequentialSolution
    criterion::Symbol
    value::Any
    policy::Dict{Tuple,Symbol}
    law::Any
    method::Symbol
    label::Symbol
    recursion_value::Any
    policies::Union{Nothing,Int}
end

function Base.show(io::IO, s::SequentialSolution)
    return print(io, "SequentialSolution(", s.criterion, ", value = ", s.value, ", ",
                 s.method, s.label === :optimal ? "" : ", $(s.label)", ")")
end

"""
    policy_law(problem::SequentialProblem, policy::AbstractDict)

The uncertain play when `policy` (a dictionary from histories at decision stages to
actions) is followed: a value of the problem's monad over complete histories, built
by chaining the chance stages with [`monad_bind`](@ref).
"""
function policy_law(p::SequentialProblem, policy::AbstractDict)
    function go(k, h)
        k > length(p.stages) && return monad_unit(p.monad, h)
        stage = p.stages[k]
        if stage isa DecisionStage
            haskey(policy, h) ||
                throw(ArgumentError("the policy has no action for the history $h"))
            return go(k + 1, (h..., policy[h]))
        end
        return monad_bind(p.monad, _law(stage, h), x -> go(k + 1, (h..., x)))
    end
    return go(1, ())
end

"""
    policy_value(problem::SequentialProblem, policy::AbstractDict, criterion)

The value of following `policy` under a scalar criterion (a
[`StructureMap`](@ref), a DecisionAnalysis aggregator, or a rule built on one): the
structure map applied to the payoff of the uncertain play,
`α(T payoff (policy_law))`.
"""
function policy_value(p::SequentialProblem, policy::AbstractDict, criterion)
    α = _criterion_map(criterion)
    α === nothing &&
        throw(ArgumentError("minimax regret is not a function of one policy's payoffs; " *
                            "use `policy_search` or `backward_induction`"))
    _check_criterion_monad(p, α)
    return α(monad_map(p.monad, p.payoff, policy_law(p, policy)))
end

# A criterion as a structure map; `nothing` stands for minimax regret.
_criterion_map(α::StructureMap) = α
_criterion_map(a::AbstractAggregator) = structure_map(a)
function _criterion_map(rule::DecisionRule)
    rule.selector isa Optimize ||
        throw(ArgumentError("a sequential criterion optimises; a threshold selector " *
                            "is not supported"))
    rule.metric.scenarios === nothing ||
        throw(ArgumentError("a sequential criterion takes no scenario restriction"))
    rule.metric.transform isa IdentityTransform && return structure_map(rule.metric.summary)
    (rule.metric.transform isa RegretTransform && rule.metric.summary isa WorstCase) ||
        throw(ArgumentError("the only regret criterion for sequential problems is " *
                            "minimax regret"))
    return nothing
end
function _criterion_map(r::RuleSelection)
    (r.selector === :optimize && r.algebra !== nothing && r.scenarios === nothing &&
     !r.uniform) ||
        throw(ArgumentError("a sequential criterion is a scalar rule that optimises"))
    r.transform === :identity && return r.algebra
    (r.transform === :regret && r.algebra isa InfimumAlgebra) ||
        throw(ArgumentError("the only regret criterion for sequential problems is " *
                            "minimax regret"))
    return nothing
end
function _criterion_map(x)
    return throw(ArgumentError("a criterion is a StructureMap, an aggregator or a scalar rule " *
                               "of DecisionAnalysis; got $(typeof(x))"))
end
_criterion_name(α::StructureMap) = nameof(typeof(α))
_criterion_name(a::AbstractAggregator) = nameof(typeof(a))
_criterion_name(r::RuleSelection) = r.name
function _criterion_name(r::DecisionRule)
    return r.name === :DecisionRule ? nameof(typeof(r.metric.summary)) : r.name
end

function _check_criterion_monad(p::SequentialProblem, α::StructureMap)
    monad_of(α) == p.monad ||
        throw(MonadMismatchError(:sequential_criterion, p.monad, monad_of(α),
                                 "the criterion's structure map is not of the " *
                                 "problem's monad"))
    return nothing
end

# Every policy: one action for each history at each decision stage.
function _all_policies(p::SequentialProblem)
    slots = Tuple{Tuple,Vector{Symbol}}[]
    for (k, stage) in enumerate(p.stages)
        stage isa DecisionStage || continue
        for h in _histories(p, k - 1)
            push!(slots, (h, stage.actions))
        end
    end
    isempty(slots) && return [Dict{Tuple,Symbol}()]
    return (Dict{Tuple,Symbol}(slots[i][1] => choice[i] for i in eachindex(slots))
            for choice in Iterators.product((s[2] for s in slots)...))
end

function _policy_count(p::SequentialProblem)
    total = big(1)
    for (k, stage) in enumerate(p.stages)
        stage isa DecisionStage || continue
        total *= big(length(stage.actions))^length(_histories(p, k - 1))
    end
    return total
end

# Scenario form, for regret: the chance stages are sets of outcomes that do not depend
# on the history, and a scenario fixes one outcome for each.
function _scenarios(p::SequentialProblem)
    p.monad isa PowersetMonad ||
        throw(MonadMismatchError(:minimax_regret, PowersetMonad(), p.monad,
                                 "regret compares payoffs scenario by scenario and " *
                                 "needs chance stages given as sets of outcomes"))
    sets = Vector{Symbol}[]
    for stage in p.stages
        stage isa ChanceStage || continue
        stage.law isa FiniteSubset ||
            throw(ArgumentError("for minimax regret the outcomes of chance stage " *
                                "`$(stage.name)` must not depend on the history"))
        push!(sets, [o for o in stage.outcomes if o in stage.law])
    end
    return vec([collect(Symbol, ω) for ω in Iterators.product(sets...)])
end

# The play of `policy` in scenario `ω` (one outcome per chance stage, in order).
function _play(p::SequentialProblem, policy, ω)
    h = ()
    c = 0
    for stage in p.stages
        if stage isa DecisionStage
            h = (h..., policy[h])
        else
            c += 1
            h = (h..., ω[c])
        end
    end
    return h
end

# The best payoff achievable in scenario `ω` with hindsight.
function _hindsight(p::SequentialProblem, ω)
    function go(k, h, c)
        k > length(p.stages) && return p.payoff(h)
        stage = p.stages[k]
        stage isa ChanceStage && return go(k + 1, (h..., ω[c + 1]), c + 1)
        return maximum(go(k + 1, (h..., a), c) for a in stage.actions)
    end
    return go(1, (), 0)
end

function _max_regret(p::SequentialProblem, policy, scenarios, hindsight)
    return maximum(hindsight[i] - p.payoff(_play(p, policy, ω))
                   for (i, ω) in enumerate(scenarios))
end

"""
    policy_search(problem::SequentialProblem, criterion; max_policies=1_000_000)
        -> SequentialSolution

Solve a sequential problem by examining **every** policy: the exact optimum for any
criterion, at a cost that grows very fast with the number of decision histories
(more than `max_policies` policies throws `ArgumentError`). `criterion` is a
[`StructureMap`](@ref), a DecisionAnalysis aggregator (`Expectation()`,
`CVaR(1 // 4)`, ...) or scalar rule (`MaxExpectedUtility()`, `Maximin()`,
`MinimaxRegret()`, ...).

For a scalar criterion `α` the value of a policy is `α` of the payoff of its
uncertain play ([`policy_value`](@ref)) and the largest is returned, with the first
policy that attains it. For minimax regret the problem's monad must be the
[`PowersetMonad`](@ref) with chance outcomes that do not depend on the history; a
scenario fixes one outcome per chance stage, the regret of a policy in a scenario is
the best payoff achievable there with hindsight minus its own, and the policy with
the smallest largest regret is returned.

This is the reference that [`backward_induction`](@ref) is tested against, and the
method to use for criteria that do not admit backward induction.
"""
function policy_search(p::SequentialProblem, criterion; max_policies::Integer=1_000_000)
    n = _policy_count(p)
    n <= max_policies ||
        throw(ArgumentError("the problem has $n policies, more than `max_policies` = " *
                            "$max_policies"))
    α = _criterion_map(criterion)
    name = _criterion_name(criterion)
    best_value, best_policy = nothing, nothing
    if α === nothing
        scenarios = _scenarios(p)
        hindsight = [_hindsight(p, ω) for ω in scenarios]
        for policy in _all_policies(p)
            v = _max_regret(p, policy, scenarios, hindsight)
            if best_value === nothing || v < best_value
                best_value, best_policy = v, policy
            end
        end
    else
        _check_criterion_monad(p, α)
        for policy in _all_policies(p)
            v = α(monad_map(p.monad, p.payoff, policy_law(p, policy)))
            if best_value === nothing || v > best_value
                best_value, best_policy = v, policy
            end
        end
    end
    return SequentialSolution(name, best_value, best_policy, policy_law(p, best_policy),
                              :policy_search, :optimal, best_value, Int(n))
end

# The selection function of the stages from `k` on, after history `h`: a selection
# function on nested pairs (x_k, (x_{k+1}, (..., ()))).
function _stage_selection(p::SequentialProblem, α::StructureMap, k::Integer, h::Tuple)
    M = p.monad
    k > length(p.stages) &&
        return SelectionFunction(:end, Any[()], M, α, _ -> monad_unit(M, ()))
    stage = p.stages[k]
    head = stage isa DecisionStage ? argmax_selection(stage.actions; monad=M, algebra=α) :
           constant_selection(stage.outcomes, _law(stage, h); monad=M, algebra=α)
    return selection_product(head, x -> _stage_selection(p, α, k + 1, (h..., x)))
end

_flatten(x::Tuple{}) = ()
_flatten(x::Tuple) = (x[1], _flatten(x[2])...)

# The stage-by-stage policy for a scalar structure map: at every decision history the
# first action maximising the recursive value.
function _recursive_policy(p::SequentialProblem, α::StructureMap)
    policy = Dict{Tuple,Symbol}()
    function go(k, h)
        k > length(p.stages) && return p.payoff(h)
        stage = p.stages[k]
        if stage isa DecisionStage
            values = [go(k + 1, (h..., a)) for a in stage.actions]
            i = findfirst(==(maximum(values)), values)
            policy[h] = stage.actions[i]
            return values[i]
        end
        return α(monad_map(p.monad, x -> go(k + 1, (h..., x)), _law(stage, h)))
    end
    nested = go(1, ())
    # Histories that the recursion did not reach (outside the support of a law) still
    # need an action for the policy to be total.
    for (k, stage) in enumerate(p.stages)
        stage isa DecisionStage || continue
        for h in _histories(p, k - 1)
            haskey(policy, h) || (policy[h] = first(stage.actions))
        end
    end
    return policy, nested
end

# The stage-by-stage answer for minimax regret: at every decision history, the action
# with the smallest largest regret among the continuations, regret being measured
# within the subproblem.
function _local_regret_policy(p::SequentialProblem)
    policy = Dict{Tuple,Symbol}()
    function go(k, h)
        k > length(p.stages) && return Dict{Tuple,Any}(() => p.payoff(h))
        stage = p.stages[k]
        if stage isa ChanceStage
            out = Dict{Tuple,Any}()
            for x in stage.outcomes
                x in stage.law || continue
                for (ω, v) in go(k + 1, (h..., x))
                    out[(x, ω...)] = v
                end
            end
            return out
        end
        tables = [go(k + 1, (h..., a)) for a in stage.actions]
        worst = [maximum(maximum(t[ω] for t in tables) - table[ω] for ω in keys(table))
                 for table in tables]
        i = findfirst(==(minimum(worst)), worst)
        policy[h] = stage.actions[i]
        return tables[i]
    end
    go(1, ())
    return policy
end

"""
    backward_induction(problem::SequentialProblem, criterion; nested=false, heuristic=false)
        -> SequentialSolution

Solve a sequential problem stage by stage from the last, as the iterated
[`selection_product`](@ref) of one selection function per stage (the first best
action at a decision stage, the stage's law at a chance stage). What the result
means depends on the class of the criterion ([`backward_induction_class`](@ref)):

- **`:flat`** (expectation, worst case, best case, lower and upper expectation,
  certainty equivalents): the structure map is an Eilenberg-Moore algebra and
  monotone, so the stage-by-stage value is the criterion applied to the whole
  problem and the policy is a best one, equal in value to [`policy_search`](@ref)
  (Lean `TwoStage.IsBackwardPolicy.flatValue_optimal`; tested against exhaustive
  search). The solution is labelled `:optimal`.
- **`:nested`** (CVaR, quantiles, Hurwicz, Laplace, α-maxmin): the structure map is
  monotone but not an algebra. Backward induction is then optimal for the **nested**
  rule, the criterion applied at every stage to the values of the next, and that is
  a different rule from the criterion applied to the distribution of the final
  payoff (Lean `cvar_two_step_ne_one_step`): the policy it finds can be strictly
  worse for the latter (`cvar_backward_induction_suboptimal`). The function throws
  [`BackwardInductionError`](@ref) unless `nested = true`, and then labels the
  solution `:nested`: `recursion_value` is the nested value, which no policy
  exceeds, and `value` is what the policy is worth under the criterion applied to
  the whole problem.
- **`:none`** (minimax regret): regret is measured against a menu, and the menu of a
  subproblem is not the menu of the problem
  (`minimaxRegret_backward_induction_suboptimal`). The function throws unless
  `heuristic = true`, which runs the recursion with regret measured within each
  subproblem and labels the solution `:heuristic`; nothing is claimed for it.

`heuristic = true` also accepts a `:nested` criterion. A chance stage's law is a
[`FiniteDistribution`](@ref), which is normalised by construction; the theorem needs
that (a sub-stochastic stage, with a stopping probability, breaks it), so there is
no way to pass one. For a credal problem ([`CredalMonad`](@ref)) the optimum is with
respect to the sequential composite of the credal kernels, which lets nature choose
afresh at every chance stage.
"""
function backward_induction(p::SequentialProblem, criterion; nested::Bool=false,
                            heuristic::Bool=false)
    α = _criterion_map(criterion)
    name = _criterion_name(criterion)
    if α === nothing
        heuristic ||
            throw(BackwardInductionError(name,
                                         "regret is measured against the best action " *
                                         "of a menu, and the menu of a subproblem is " *
                                         "not the menu of the whole problem"))
        scenarios = _scenarios(p)
        policy = _local_regret_policy(p)
        hindsight = [_hindsight(p, ω) for ω in scenarios]
        value = _max_regret(p, policy, scenarios, hindsight)
        return SequentialSolution(name, value, policy, policy_law(p, policy),
                                  :backward_induction, :heuristic, nothing, nothing)
    end
    _check_criterion_monad(p, α)
    class = backward_induction_class(α)
    class === :none &&
        throw(BackwardInductionError(name, "it is not monotone"))
    class === :flat || nested || heuristic ||
        throw(BackwardInductionError(name,
                                     "it is not an Eilenberg-Moore algebra of the " *
                                     "problem's monad, so applying it stage by stage " *
                                     "is a different rule (the nested one) from " *
                                     "applying it to the whole problem; pass " *
                                     "`nested = true` to solve the nested rule"))
    product = _stage_selection(p, α, 1, ())
    worth(nested_play) = p.payoff(_flatten(nested_play))
    law = monad_map(p.monad, _flatten, select(product, worth))
    # The value of the play that the product selects is the criterion applied to the
    # whole play; the stage-by-stage (nested) value comes from the direct recursion.
    policy, recursion_value = _recursive_policy(p, α)
    value = α(monad_map(p.monad, p.payoff, law))
    return SequentialSolution(name, value, policy, law, :backward_induction,
                              class === :flat ? :optimal : :nested, recursion_value,
                              nothing)
end

"""
    nested_value(problem::SequentialProblem, policy::AbstractDict, criterion)

The **nested** value of a policy under a scalar criterion: the structure map applied
at every chance stage to the values of the next stage, from the last stage
backwards. For a criterion of class `:flat` it equals [`policy_value`](@ref); for a
`:nested` one (CVaR, say) it is the value of a different rule, the one that
[`backward_induction`](@ref) with `nested = true` optimises.
"""
function nested_value(p::SequentialProblem, policy::AbstractDict, criterion)
    α = _criterion_map(criterion)
    α === nothing && throw(ArgumentError("minimax regret has no nested value"))
    _check_criterion_monad(p, α)
    function go(k, h)
        k > length(p.stages) && return p.payoff(h)
        stage = p.stages[k]
        stage isa DecisionStage && return go(k + 1, (h..., policy[h]))
        return α(monad_map(p.monad, x -> go(k + 1, (h..., x)), _law(stage, h)))
    end
    return go(1, ())
end

"""
    optimal_plays(problem::SequentialProblem) -> FiniteSubset

Every complete history of a **deterministic** sequential problem (decision stages
only) that attains the largest payoff, computed by the product of set-valued
selection functions (`argmax_selection(...; ties = :all)` in the
[`PowersetMonad`](@ref)). For such problems the product returns exactly the set of
optimal plays, which the test suite checks against enumeration.

It is not offered for problems with chance stages. With nature's moves in the
product, the set it returns is the plays of the policies that are optimal in every
subproblem, which is in general a strict subset of the plays of all optimal
policies (a worst-case-optimal policy may do anything off the worst path), and for
games with several players set-valued products are known to be wrong (Bolt, Hedges
and Zahn). A problem with a chance stage throws `ArgumentError`.
"""
function optimal_plays(p::SequentialProblem)
    all(s -> s isa DecisionStage, p.stages) ||
        throw(ArgumentError("`optimal_plays` is offered for deterministic problems " *
                            "only: with chance stages the set-valued product is not " *
                            "the set of plays of all optimal policies"))
    M, α = PowersetMonad(), SupremumAlgebra()
    function stage_selection(k)
        k > length(p.stages) &&
            return SelectionFunction(:end, Any[()], M, α, _ -> monad_unit(M, ()))
        head = argmax_selection(p.stages[k].actions; monad=M, algebra=α, ties=:all)
        return selection_product(head, _ -> stage_selection(k + 1))
    end
    plays = select(stage_selection(1), nested -> p.payoff(_flatten(nested)))
    return monad_map(M, _flatten, plays)
end
