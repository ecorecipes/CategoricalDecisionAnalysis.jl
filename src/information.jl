# Information preorders (component 5 of the plan and its revisions): experiments under
# garbling, partitions under refinement, value as a monotone map out of each, an
# experiment as a distribution over posteriors, and the deficiency-enriched form.
#
# Contract with the Lean development (theorem C8, over T0, T4, T6 and T6a):
#
#   e′ ⪯ e   iff  L_e′ = G · L_e for a column-stochastic G            (garbling)
#   P ⪯ P′   iff  every cell of P′ lies inside a cell of P            (P′ refines P)
#   value is monotone on both:  x ⪯ y  ⟹  value(x) ≤ value(y)
#   value(e′) − value(e) ≤ largest_regret · δ(e, e′)                   (Lipschitz form)

"""
    is_garbling(e′::Experiment, e::Experiment; kw...) -> Bool

Whether `e′ ⪯ e` in the garbling (Blackwell) preorder on experiments over the same
states: `e′` is `e` followed by a noisy channel, so `e′` tells no more than `e`. The
relation is reflexive and transitive (theorem T0 of the Lean development), and two
experiments can each be a garbling of the other without being equal, so it is a
preorder and not a partial order.

Decided by DecisionAnalysis's `garbling_result` (a linear programme; keywords such
as `optimizer` are passed on), which also returns the witness matrix or, for an
exact "no", a decision problem in which `e′` is worth strictly more.
"""
is_garbling(e′::Experiment, e::Experiment; kw...) = garbling_result(e′, e;
                                                                    kw...).is_garbling

"""
    refines(fine::AbstractVector, coarse::AbstractVector) -> Bool

Whether the partition `fine` refines the partition `coarse`: two states in the same
cell of `fine` are in the same cell of `coarse`. A partition is a vector with one
cell label per state, as for DecisionAnalysis's `evppi`. Refinement is a preorder on
such vectors (a partial order on the partitions they describe), with the one-cell
partition at the bottom (nothing is learned) and the partition into single states at
the top (everything is).

```jldoctest
julia> refines([:a, :b, :c, :c], [:x, :x, :y, :y])
true

julia> refines([:x, :x, :y, :y], [:a, :b, :c, :c])
false
```
"""
function refines(fine::AbstractVector, coarse::AbstractVector)
    length(fine) == length(coarse) ||
        throw(ArgumentError("the partitions are over $(length(fine)) and " *
                            "$(length(coarse)) states"))
    image = Dict{Any,Any}()
    for (f, c) in zip(fine, coarse)
        isequal(get!(image, f, c), c) || return false
    end
    return true
end

"""
    partition_experiment(partition::AbstractVector; states=nothing) -> Experiment

The deterministic experiment that reveals the cell of a partition: one signal per
cell, with likelihood one when the state is in the cell and zero otherwise. Learning
the cell is this experiment, so the partial-information value of the partition is
its sample-information value,

    evppi(problem, partition) == evsi(problem, partition_experiment(partition)),

and a refinement of a partition is an experiment of which the coarser one is a
garbling: the refinement preorder embeds in the garbling preorder.
"""
function partition_experiment(partition::AbstractVector; states=nothing)
    cells = unique(partition)
    L = [isequal(partition[j], c) ? 1 // 1 : 0 // 1
         for c in cells, j in eachindex(partition)]
    signals = all(c -> c isa Union{Symbol,AbstractString}, cells) ? Symbol.(cells) :
              [Symbol(:cell, i) for i in eachindex(cells)]
    return states === nothing ? Experiment(L; signals) : Experiment(L; signals, states)
end

"""
    information_value(problem::DecisionProblem, experiment::Experiment)
    information_value(problem::DecisionProblem, partition::AbstractVector)

The value of deciding after the information: the monotone map out of the garbling
preorder (first form, DecisionAnalysis's `value_with_information`) and out of the
refinement preorder (second form, the same for
[`partition_experiment`](@ref)`(partition)`). Monotone means

    is_garbling(e′, e)   ⟹  information_value(problem, e′) ≤ information_value(problem, e)
    refines(fine, coarse) ⟹  information_value(problem, coarse) ≤ information_value(problem, fine)

for every problem with a single prior (Blackwell's theorem, easy direction: T6 and
T4). EVPI, EVPPI and EVSI are this map at particular points, minus its value at the
bottom of the preorder (DecisionAnalysis's `act_now_value`).
"""
function information_value(problem::DecisionProblem, experiment::Experiment)
    return value_with_information(problem, experiment)
end
function information_value(problem::DecisionProblem, partition::AbstractVector)
    return value_with_information(problem,
                                  partition_experiment(partition;
                                                       states=problem.payoff.states))
end

"""
    posterior_distribution(prior, experiment::Experiment) -> FiniteDistribution

An experiment represented by the distribution it induces over posterior beliefs: a
[`FiniteDistribution`](@ref) whose outcomes are posterior probability vectors over
the states and whose probabilities are those of the signals that lead to them.
Signals of probability zero do not appear, and signals with the same posterior are
merged, so two experiments that differ only by relabelling or splitting signals have
the same distribution. `prior` is a `FiniteBelief` or a probability vector.

The mean of the distribution is the prior ([`posterior_mean`](@ref)). The value of
the experiment is the expectation, under this distribution, of the convex function
"best expected payoff at the posterior" ([`value_at_posteriors`](@ref)). A garbling
gives a distribution that is smaller in the convex order (a mean-preserving
contraction), which is why one Jensen-type lemma gives EVPI ≥ 0, 0 ≤ EVSI ≤ EVPI and
Blackwell's easy direction (after Fritz, Gonda, Perrone and Rischel).
"""
function posterior_distribution(prior::AbstractVector{<:Real}, experiment::Experiment)
    inv = bayesian_inverse(collect(prior), experiment.likelihood)
    keep = findall(!iszero, inv.evidence)
    return FiniteDistribution([inv.inverse[:, z] for z in keep], inv.evidence[keep])
end
function posterior_distribution(prior::FiniteBelief, experiment::Experiment)
    return posterior_distribution(prior.probabilities, experiment)
end

"""
    posterior_mean(μ::FiniteDistribution) -> Vector

The mean of a distribution over posterior vectors, `Σ_π μ(π) π`. For
[`posterior_distribution`](@ref)`(prior, e)` it is the prior, whatever the
experiment (the posteriors average back to the prior).
"""
function posterior_mean(μ::FiniteDistribution{<:AbstractVector})
    return sum(p .* π for (π, p) in _pairs(μ))
end

"""
    value_at_posteriors(problem::DecisionProblem, μ::FiniteDistribution)

The expectation under a distribution over posterior vectors of the best expected
payoff at each posterior, `Σ_π μ(π) max_a Σ_θ π(θ) Q[a, θ]`, over the feasible
actions. With `μ` the [`posterior_distribution`](@ref) of an experiment it is
DecisionAnalysis's `value_with_information`.
"""
function value_at_posteriors(problem::DecisionProblem,
                             μ::FiniteDistribution{<:AbstractVector})
    Q = problem.payoff.Q[problem.feasible, :]
    return sum(p * maximum(Q * π) for (π, p) in _pairs(μ))
end

"""
    posterior_payoff(problem::DecisionProblem, experiment::Experiment)
        -> (signals::FiniteDistribution, payoff::Matrix)

The decision problem after the experiment, as a table indexed by the signal: the
distribution of the signals of positive probability (over their indices) and the
posterior expected payoff `payoff[a, k] = E[Q[a, θ] | signal k]` of each feasible
action given each of them. The value of sample information is then the interchange
gap of the maximum at the signal distribution,

    interchange_gap(ExpectationAlgebra(), signals, payoff) == evsi(problem, experiment),

the same statement that gives EVPI at the prior ([`interchange_gap`](@ref)).
"""
function posterior_payoff(problem::DecisionProblem, experiment::Experiment)
    problem.belief isa FiniteBelief ||
        throw(BeliefFormError(:posterior_payoff, nameof(typeof(problem.belief)),
                              "a single finite prior is needed"))
    inv = bayesian_inverse(problem.belief, experiment)
    keep = findall(!iszero, inv.evidence)
    Q = problem.payoff.Q[problem.feasible, :]
    return (; signals=FiniteDistribution(collect(eachindex(keep)), inv.evidence[keep]),
            payoff=Q * inv.inverse[:, keep])
end

"""
    information_distance(e::Experiment, e′::Experiment; kw...)

Le Cam's distance between two experiments on the same states,
`max(deficiency(e, e′), deficiency(e′, e))`. It is zero exactly when each is a
garbling of the other. Each deficiency satisfies `δ(e, e) = 0` and the triangle
inequality `δ(e, e″) ≤ δ(e, e′) + δ(e′, e″)`, which makes the experiments a
Lawvere metric space, an enrichment of the garbling preorder (`δ(e, e′) = 0` iff
`e′ ⪯ e`). Keywords go to DecisionAnalysis's `deficiency`.
"""
function information_distance(e::Experiment, e′::Experiment; kw...)
    return max(deficiency(e, e′; kw...), deficiency(e′, e; kw...))
end

"""
    value_gap_bound(problem::DecisionProblem, e::Experiment, e′::Experiment; kw...)

The deficiency bound on how much more `e′` can be worth than `e` in `problem`:

    information_value(problem, e′) − information_value(problem, e)
        ≤ largest_regret(problem) · deficiency(e, e′).

Value is therefore not only monotone on the garbling preorder but Lipschitz for the
deficiency: an experiment that is nearly a garbling of another is worth at most a
little more (theorem T6a of the Lean development; after Le Cam). With deficiency
zero it is Blackwell's theorem. Computed with DecisionAnalysis's `deficiency` and
`deficiency_value_bound`; keywords go to `deficiency`.
"""
function value_gap_bound(problem::DecisionProblem, e::Experiment, e′::Experiment; kw...)
    return deficiency_value_bound(problem, deficiency(e, e′; kw...))
end

# The regret transform under coarsening (component 7 of the plan, theorem C6)
# ---------------------------------------------------------------------------
#
# Contract with the Lean development. For feasible payoffs Q[a, θ], a prior p and a
# partition of the states into cells c, all in joint (mass-weighted) form:
#
#   coarse payoff        Q̃[a, c]  = Σ_{θ ∈ c} p(θ) Q[a, θ]
#   coarse regret        R̃[a, c]  = max_a′ Q̃[a′, c] − Q̃[a, c]
#   coarsened regret     S[a, c]  = Σ_{θ ∈ c} p(θ) (max_a′ Q[a′, θ] − Q[a, θ])
#   gap                  g[c]     = Σ_{θ ∈ c} p(θ) max_a Q[a, θ] − max_a Σ_{θ ∈ c} p(θ) Q[a, θ]
#
#   R̃[a, c] + g[c] = S[a, c] for every action,   g[c] ≥ 0,   Σ_c g[c] = EVPI − EVPPI,
#   g[c] = 0  iff  one action is best at every state of positive probability in c.

"""
    RegretCoarsening

What [`regret_coarsening`](@ref) returns. Fields (rows are feasible actions, columns
the cells of the partition, everything weighted by the prior mass of the cell):

- `actions`, `cells`: the labels of rows and columns.
- `mass`: the prior probability of each cell.
- `coarse_payoff`: `Σ_{θ ∈ c} p(θ) Q[a, θ]`.
- `coarse_regret`: the regret table of `coarse_payoff`, "regret after coarsening".
- `coarsened_regret`: `Σ_{θ ∈ c} p(θ) R[a, θ]` with `R` the regret table of the
  problem, "coarsening after regret".
- `gap`: one number per cell, `coarsened_regret[a, c] − coarse_regret[a, c]`, the
  same for every action: the prior mass of the cell times the expected value of
  perfect information within the cell.
"""
struct RegretCoarsening{T<:Real}
    actions::Vector{Symbol}
    cells::Vector{Any}
    mass::Vector{T}
    coarse_payoff::Matrix{T}
    coarse_regret::Matrix{T}
    coarsened_regret::Matrix{T}
    gap::Vector{T}
end

function Base.show(io::IO, r::RegretCoarsening)
    return print(io, "RegretCoarsening(", length(r.actions), " actions, ",
                 length(r.cells), " cells, total gap ", sum(r.gap), ")")
end

"""
    regret_coarsening(problem::DecisionProblem, partition::AbstractVector) -> RegretCoarsening

Savage regret as an operation on payoff tables indexed by the menu of actions, and
what happens to it when states are merged. With `Q[a, θ]` the feasible payoffs, `p`
the prior and the partition's cells `c`, in mass-weighted form:

    regret(coarsen(Q))[a, c]  ≤  coarsen(regret(Q))[a, c],

**regret is lax under coarsening**, and the difference is the same for every action:

    gap[c] = Σ_{θ ∈ c} p(θ) max_a Q[a, θ]  −  max_a Σ_{θ ∈ c} p(θ) Q[a, θ]  ≥ 0,

the prior mass of the cell times the expected value of perfect information given
the cell (the conditional EVPI). It is zero exactly when one action is best at every
state of positive probability in the cell, and the gaps add up to what is still to
be learned after learning the cell:

    sum(gap) == evpi(problem) − evppi(problem, partition).

The statement is about the **prior-weighted** regret table and so about expected
regret: summing a row over the cells, an action's expected regret in the fine
problem exceeds its expected regret in the coarse one by `evpi − evppi`, the same
for every action, so coarsening never reorders actions by expected regret. Nothing
is claimed for maximum regret. [`coarsening_is_lossless`](@ref) decides whether the
gap is zero without computing it. This is theorem C6 of the Lean development
(`expectedRegret_sub_coarseExpectedRegret`, `coarseRegret_le`,
`coarseExpectedRegret_eq_expectedRegret_iff`); no earlier categorical treatment of
Savage regret was found by the literature search (stated as "not found", not "does
not exist"). The mass-weighted form needs no division, so a cell of probability zero
is a column of zeros and not a special case. Needs a single finite prior.

```jldoctest
julia> p = DecisionProblem(PayoffTable([0 -10 -60 -150; -20 -20 -25 -90]),
                           [1 // 2, 3 // 10, 3 // 20, 1 // 20]);

julia> r = regret_coarsening(p, [:mild, :mild, :severe, :severe]);

julia> r.gap == [0, 0]     # one action is best throughout each cell
true

julia> sum(regret_coarsening(p, [:all, :all, :all, :all]).gap) == evpi(p)
true
```
"""
function regret_coarsening(problem::DecisionProblem, partition::AbstractVector)
    return _regret_coarsening(problem, partition)
end

"""
    coarsening_is_lossless(problem::DecisionProblem, partition::AbstractVector) -> Bool

Whether merging the states of each cell of `partition` loses nothing for this
decision: every cell has an action that is best at every one of its states of
positive probability. This is decided without computing any regret, and it is
equivalent to the gap of [`regret_coarsening`](@ref) being zero in every cell, that
is to `evppi(problem, partition) == evpi(problem)` (Lean
`coarseExpectedRegret_eq_expectedRegret_iff`). Exact for rational problems; in
floating point "best" is exact comparison, so prefer rational inputs.
"""
function coarsening_is_lossless(problem::DecisionProblem, partition::AbstractVector)
    problem.belief isa FiniteBelief ||
        throw(BeliefFormError(:coarsening_is_lossless, nameof(typeof(problem.belief)),
                              "a single finite prior is needed"))
    p = problem.belief.probabilities
    Q = problem.payoff.Q[problem.feasible, :]
    length(partition) == length(p) ||
        throw(ArgumentError("the partition has $(length(partition)) entries for " *
                            "$(length(p)) states"))
    best = [Set(findall(==(maximum(view(Q, :, j))), view(Q, :, j))) for j in axes(Q, 2)]
    for c in unique(partition)
        cols = [j for j in axes(Q, 2) if isequal(partition[j], c) && !iszero(p[j])]
        isempty(cols) || !isempty(intersect(best[cols]...)) || return false
    end
    return true
end

function _regret_coarsening(problem::DecisionProblem, partition::AbstractVector)
    problem.belief isa Union{FiniteBelief,PointBelief} ||
        throw(BeliefFormError(:regret_coarsening, nameof(typeof(problem.belief)),
                              "the coarsening weights states by a single finite prior"))
    states = problem.payoff.states
    length(partition) == length(states) ||
        throw(ArgumentError("the partition has $(length(partition)) entries for the " *
                            "$(length(states)) states of the payoff table"))
    p = problem.belief isa PointBelief ?
        [s == problem.belief.state ? 1 // 1 : 0 // 1 for s in states] :
        problem.belief.probabilities
    Q = problem.payoff.Q[problem.feasible, :]
    R = maximum(Q; dims=1) .- Q
    cells = unique(partition)
    member = [isequal(partition[j], c) ? 1 : 0 for j in eachindex(partition), c in cells]
    weights = p .* member                        # [θ, c] = p(θ) if θ ∈ c
    coarse_payoff = Q * weights
    coarse_regret = maximum(coarse_payoff; dims=1) .- coarse_payoff
    coarsened_regret = R * weights
    gap = vec(maximum(Q; dims=1) * weights) .- vec(maximum(coarse_payoff; dims=1))
    T = promote_type(eltype(coarse_payoff), eltype(gap))
    return RegretCoarsening{T}(feasible_actions(problem), collect(Any, cells),
                               convert(Vector{T}, vec(sum(weights; dims=1))),
                               convert(Matrix{T}, coarse_payoff),
                               convert(Matrix{T}, coarse_regret),
                               convert(Matrix{T}, coarsened_regret),
                               convert(Vector{T}, gap))
end
