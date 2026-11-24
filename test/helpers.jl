# Random inputs and slow oracles for the test suite. An oracle here shares no code with
# the function it checks: it is written from the definition, by direct enumeration.

# A random probability vector with rational entries; some entries are zero when
# `zeros` is true.
function rational_probabilities(rng, n; zeros::Bool=false)
    w = [zeros && rand(rng) < 0.25 ? 0 : rand(rng, 1:9) for _ in 1:n]
    all(iszero, w) && (w[rand(rng, 1:n)] = 1)
    return w .// sum(w)
end

# A random column-stochastic `m × n` matrix with rational entries.
function rational_kernel(rng, m, n; zeros::Bool=false)
    return reduce(hcat, [rational_probabilities(rng, m; zeros) for _ in 1:n])
end

rational_table(rng, m, n; range=-20:20) = rand(rng, range, m, n) .// 1

# Oracle for sequential problems: every policy as a function on histories, evaluated by
# walking the tree. Returns the list of `(policy, outcome)` with `outcome` a vector of
# `(probability, payoff)` (distribution monad) or of payoffs (set monad).
function oracle_outcomes(stages, payoff, policy)
    # `stages` is a vector of (:decision, actions) or (:chance, outcomes => weights).
    function walk(k, h)
        k > length(stages) && return [(1 // 1, payoff(h))]
        kind, data = stages[k]
        kind === :decision && return walk(k + 1, (h..., policy[h]))
        out = Tuple{Rational{Int},Any}[]
        for (x, w) in zip(data...)
            iszero(w) && continue
            for (q, v) in walk(k + 1, (h..., x))
                push!(out, (w * q, v))
            end
        end
        return out
    end
    return walk(1, ())
end

function oracle_policies(stages)
    slots = Tuple{Tuple,Vector{Symbol}}[]
    hs = Tuple[()]
    for (kind, data) in stages
        options = kind === :decision ? data : data[1]
        kind === :decision && append!(slots, [(h, options) for h in hs])
        hs = Tuple[(h..., x) for h in hs for x in options]
    end
    return [Dict{Tuple,Symbol}(slots[i][1] => c[i] for i in eachindex(slots))
            for c in Iterators.product((s[2] for s in slots)...)]
end

oracle_expectation(outcome) = sum(w * v for (w, v) in outcome)
oracle_minimum(outcome) = minimum(v for (_, v) in outcome)
oracle_maximum(outcome) = maximum(v for (_, v) in outcome)
function oracle_cvar(outcome, α)
    sorted = sort(outcome; by=last)
    remaining, total = α, 0 // 1
    for (w, v) in sorted
        take = min(w, remaining)
        total += take * v
        remaining -= take
        remaining > 0 || break
    end
    return total / α
end

# Oracle for a pipeline given as plain data: a closed chain belief → channel → policy →
# utility, by explicit sums.
function oracle_informed_value(prior, L, Q)
    # Σ_z max_a Σ_θ p(θ) L[z, θ] Q[a, θ]
    return sum(maximum(sum(prior[θ] * L[z, θ] * Q[a, θ] for θ in eachindex(prior))
                       for a in axes(Q, 1)) for z in axes(L, 1))
end

# Every deterministic policy `z ↦ a` of a decision with `nz` observations and `na`
# actions, as vectors of action indices.
all_policies(na, nz) = vec([collect(c) for c in Iterators.product(fill(1:na, nz)...)])

axis_names_of(p::DecisionPipeline) = FiniteKernels.axis_names(dom(p))

# Wires and random pieces of a pipeline, shared by the pipeline, compiler and
# certificate tests.
const TH = :state => [:t1, :t2, :t3]
const ZZ = :signal => [:z1, :z2]
const AA = :action => [:none, :treat]
const YY = :outcome => [:y1, :y2, :y3]
const WW = :report => [:w1, :w2]

# Random pieces of a pipeline, with rational tables.
function random_pieces(rng)
    prior = rational_probabilities(rng, 3; zeros=true)
    L = rational_kernel(rng, 2, 3; zeros=true)
    consequence = reshape(reduce(hcat, [rational_probabilities(rng, 3) for _ in 1:6]),
                          3, 2, 3)                      # [y, a, θ]
    u_outcome = rand(rng, 0:40, 3)
    u_action = [0, -rand(rng, 0:5)]
    report = rational_kernel(rng, 2, 3)
    u_report = rand(rng, -5:5, 2)
    return (; prior, L, consequence, u_outcome, u_action, report, u_report)
end

function closed_pipeline(x; policy=nothing)
    return decision_pipeline(belief_box(:prior, TH, x.prior),
                             channel_box(:survey, TH, ZZ, x.L),
                             policy_box(:manager, ZZ, AA, policy),
                             consequence_box(:model, (AA, TH), YY, x.consequence),
                             utility_box(:animals, YY, x.u_outcome),
                             utility_box(:handling, AA, x.u_action))
end

# The payoff table of the pieces, written out from the definition.
function oracle_payoff(x)
    return [sum(x.consequence[y, a, θ] * x.u_outcome[y] for y in 1:3) + x.u_action[a]
            for a in 1:2, θ in 1:3]
end
