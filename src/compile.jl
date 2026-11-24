# Programmes as an interpretation of the diagram: compile a decision pipeline to a
# JuMP model.
#
# Two compilers.
#
# 1. `policy_program`: one decision with a fixed information structure. The policy is a
#    stochastic matrix π[a, z]; everything is linear in it, so the result is a linear
#    programme, returned as a `DecisionProgram` of DecisionAnalysis and solved by its
#    `solve_program` (exactly by default).
#
#        maximise    Σ_{a,z} J[a, z] π[a, z]
#        subject to  Σ_a π[a, z] = 1 for every z,   π ≥ 0,
#                    Σ_{a,z} G_c[a, z] π[a, z] ≤ b_c   for every constraint c,
#
#    with J[a, z] = E[utility · 1{Z = z} | do(a)] and G_c likewise for the constrained
#    quantity. Contract with the Lean development: the feasible set without extra
#    constraints is the set of stochastic policies, its vertices are the deterministic
#    policies, and the objective at π is the expected utility of the pipeline with
#    that policy bound.
#
# 2. `strategy_program`: any number of decisions, deterministic local policies, in the
#    path formulation of Salo, Andelmin and Oliveira (DecisionProgramming.jl), made
#    open so that programmes compose (after the open optimisation problems of
#    AlgebraicOptimization.jl). For a component with joint wire values s, chance weight
#    w(s) = Π chance tables, inputs x(s) and input mass m(x):
#
#        z_k[a, i] ∈ {0, 1},  Σ_a z_k[a, i] = 1        (a local policy per decision k)
#        0 ≤ φ(s) ≤ w(s) m(x(s)),   φ(s) ≤ z_k[a_k(s), i_k(s)] for every k,
#        Σ_{s : x(s) = x} φ(s) = m(x)                    (flow conservation)
#        objective  Σ_s φ(s) U(s),    output mass  m′(y) = Σ_{s : y(s) = y} φ(s).
#
#    For binary z the flow is forced to φ(s) = w(s) m(x(s)) on the paths the policies
#    allow and zero elsewhere, so the objective is the expected utility. Composing two
#    programmes in series identifies the output mass of the first with the input mass
#    of the second and adds the objectives.

"""
    ExpectationConstraint

A linear constraint on a compiled pipeline: a bound on the expectation, under the
policy being chosen, of a quantity that is a function of some wires. Build one with
[`expectation_constraint`](@ref) (a budget in individuals handled, a floor on an
expected count) or [`chance_constraint`](@ref) (a cap on the probability of an
event). Fields: `name`, `wires`, `values` (an array over the wires' labels, or a
function of the labels), `sense` (`:at_most` or `:at_least`) and `bound`.

These are constraints that the influence-diagram solvers of the ecosystem
(`optimize`, `contextual_optimize`) cannot express: they maximise expected utility
over all policies, with no side condition.
"""
struct ExpectationConstraint
    name::Symbol
    wires::Vector{Symbol}
    values::Any
    sense::Symbol
    bound::Any
end

_wire_names(w::Union{Tuple,AbstractVector}) = Symbol[_wire_name(x) for x in w]
_wire_names(w) = Symbol[_wire_name(w)]
_wire_name(w::Symbol) = w
_wire_name(w::Pair) = Symbol(first(w))
_wire_name(w::FiniteAxis) = w.name

"""
    expectation_constraint(name, wires, values; at_most=nothing, at_least=nothing)
        -> ExpectationConstraint

The constraint `E[values(wires)] ≤ at_most` or `≥ at_least` (exactly one of the
two) for a compiled pipeline. `wires` is a wire or a tuple of wires (names, or
`name => labels` pairs) and `values` an array with one axis per wire or a function
of the wires' labels. Typical uses: a **budget** counted in individuals or effort
(the expected number of animals handled is at most the capacity of the field team)
and a **floor** (the expected number of survivors is at least a target).
"""
function expectation_constraint(name, wires, values; at_most=nothing, at_least=nothing)
    (at_most === nothing) != (at_least === nothing) ||
        throw(ArgumentError("give exactly one of `at_most` and `at_least`"))
    return ExpectationConstraint(Symbol(name), _wire_names(wires), values,
                                 at_most === nothing ? :at_least : :at_most,
                                 something(at_most, at_least))
end

"""
    chance_constraint(name, wires, event; at_most=nothing, at_least=nothing)
        -> ExpectationConstraint

The constraint `P(event) ≤ at_most` or `≥ at_least` for a compiled pipeline, where
`event` is a predicate on the labels of `wires`: for example that the probability
of local extinction stays below one in twenty. It is the expectation constraint of
the event's indicator, and so linear in the policy.
"""
function chance_constraint(name, wires, event; at_most=nothing, at_least=nothing)
    return expectation_constraint(name, wires, (labels...) -> event(labels...) ? 1 : 0;
                                  at_most, at_least)
end

# The constrained quantity as an array over its wires.
function _constraint_table(p::DecisionPipeline, c::ExpectationConstraint)
    axes = FiniteAxis[]
    for w in c.wires
        any(a -> a.name == w, _axes(p)) ||
            throw(CompilationError("constraint `$(c.name)` is over the wire `$w`, " *
                                   "which the pipeline does not have"))
        push!(axes, _axis(p, w))
    end
    sizes = Tuple(length(a) for a in axes)
    if c.values isa AbstractArray
        size(c.values) == sizes ||
            throw(CompilationError("constraint `$(c.name)` has a table of size " *
                                   "$(size(c.values)); its wires have $sizes"))
        return c.values
    end
    return [c.values(ntuple(i -> axes[i].labels[ci[i]], length(axes))...)
            for ci in CartesianIndices(sizes)]
end

# The pipeline with its utility boxes replaced by the constrained quantity.
function _with_quantity(p::DecisionPipeline, c::ExpectationConstraint)
    specs = [s for s in _specs(p) if s.kind !== :utility]
    push!(specs,
          _BoxSpec(Symbol(:constraint_, c.name), :utility, c.wires, nothing,
                   _constraint_table(p, c), 0))
    return _assemble(_axes(p), specs, p.inputs, p.outputs)
end

function _number_type(::Type{S}) where {S}
    return _exact(S) ? Rational{BigInt} :
           S <: AbstractFloat ? S : Float64
end

"""
    policy_program(p::DecisionPipeline; constraints=[]) -> DecisionProgram

Compile a pipeline with **one open policy box** and no input wires to a linear
programme, as a `DecisionProgram` of DecisionAnalysis (a `JuMP.GenericModel{T}`,
`T = Rational{BigInt}` for a pipeline with integer or rational tables). The decision
box becomes the variables, the chance boxes the coefficients, the utility boxes the
objective:

    maximise    Σ_{a,z} J[a, z] π[a, z]
    subject to  Σ_a π[a, z] = 1          for every joint observation z,    (simplex[z])
                Σ_{a,z} G_c[a, z] π[a, z] ≤ b_c   (or ≥) for every constraint c,
                π[a, z] ≥ 0,

where `π[a, z]` is the probability of action `a` after observing `z` (a stochastic
policy; `z` runs over the joint values of the wires the policy box reads),
`J[a, z] = E[utility · 1{Z = z} | do(a)]`, and `G_c` is the same for the quantity of
the [`ExpectationConstraint`](@ref) `c`. `variables.π` is the matrix of variables
(rows = actions, columns = joint observations in `joint_states` order), and
`constraints.simplex` and `constraints.side` the constraint references.

Without side constraints the optimum is attained at a deterministic policy and
equals `value_with_information(p)`, the optimum that `contextual_optimize` of
CategoricalInfluenceDiagrams finds by enumerating policies (tested on every small
problem). With a side constraint the best policy may have to randomise, which is
why the variables are probabilities.

Solve it with DecisionAnalysis's `solve_program` (the built-in exact simplex by
default, or any JuMP optimiser), or read the policy back with
[`solve_policy_program`](@ref). Shape: `n_a · n_z` variables and `n_z` plus the
number of side constraints constraints.
"""
function policy_program(p::DecisionPipeline; constraints=ExpectationConstraint[])
    open = _open_policies(p)
    length(open) == 1 ||
        throw(CompilationError("the linear programme is for one decision with a fixed " *
                               "information structure; the pipeline has " *
                               "$(length(open)) open policy boxes (use " *
                               "`strategy_program`)"))
    isempty(p.inputs) ||
        throw(CompilationError("the pipeline has input wires $(p.inputs); plug values " *
                               "into them first (`intervene`)"))
    policy = only(open)
    keep = vcat([policy.out], policy.ins)
    mass, reward = _accumulate(p, keep, [policy.name], :policy_program)
    na = size(reward, 1)
    J = reshape(reward, na, :)
    nz = size(J, 2)
    tables = [reshape(_accumulate(_with_quantity(p, c), keep, [policy.name],
                                  :policy_program)[2], na, nz) for c in constraints]
    S = mapreduce(eltype, promote_type, tables; init=eltype(J))
    S = mapreduce(c -> typeof(c.bound), promote_type, constraints; init=S)
    T = _number_type(S)
    model = JuMP.GenericModel{T}()
    π = JuMP.@variable(model, [1:na, 1:nz], lower_bound = zero(T), base_name = "π")
    simplex = JuMP.@constraint(model, [z = 1:nz], sum(π[a, z] for a in 1:na) == one(T))
    side = map(zip(constraints, tables)) do (c, G)
        lhs = sum(T(G[a, z]) * π[a, z] for a in 1:na, z in 1:nz)
        return c.sense === :at_most ? JuMP.@constraint(model, lhs <= T(c.bound)) :
               JuMP.@constraint(model, lhs >= T(c.bound))
    end
    JuMP.@objective(model, Max, sum(T(J[a, z]) * π[a, z] for a in 1:na, z in 1:nz))
    return DecisionProgram(:pipeline_policy, model, (; π), (; simplex, side))
end

"""
    PolicySolution

What [`solve_policy_program`](@ref) returns: `status` (`:optimal`, `:infeasible`,
...), `value` (the optimal expected utility), `policy` (the matrix `π[a, z]`, rows =
actions, columns = joint observations), `actions` and `observations` (the labels of
its rows and columns), `deterministic` (whether every column of the policy is a
single action), `exact` and `route` (as in DecisionAnalysis's `ProgramSolution`).
"""
struct PolicySolution
    status::Symbol
    value::Any
    policy::Any
    actions::Vector{Symbol}
    observations::Vector{Symbol}
    deterministic::Bool
    exact::Bool
    route::Symbol
end

function Base.show(io::IO, s::PolicySolution)
    return print(io, "PolicySolution(", s.status, ", value = ", s.value,
                 s.deterministic ? ", deterministic" : ", randomised", ")")
end

"""
    solve_policy_program(p::DecisionPipeline; constraints=[], optimizer=nothing, rounding_tol)
        -> PolicySolution

Compile the one-decision pipeline with [`policy_program`](@ref) and solve it with
DecisionAnalysis's `solve_program`: by default the built-in exact simplex, otherwise
the JuMP `optimizer` given (an exact one, or a floating-point one whose solution is
rounded and verified exactly). The policy is returned with its labels.
"""
function solve_policy_program(p::DecisionPipeline; constraints=ExpectationConstraint[],
                              optimizer=nothing, kw...)
    sol = solve_program(policy_program(p; constraints); optimizer, kw...)
    policy = only(_open_policies(p))
    actions = copy(_axis(p, policy.out).labels)
    observations = isempty(policy.ins) ? [:nothing_observed] :
                   _joint_labels(FiniteAxis[_axis(p, w) for w in policy.ins])
    sol.status === :optimal ||
        return PolicySolution(sol.status, nothing, nothing, actions, observations, false,
                              sol.exact, sol.route)
    π = sol.values.π
    return PolicySolution(:optimal, sol.objective, π, actions, observations,
                          all(x -> iszero(x) || isone(x), π), sol.exact, sol.route)
end

# Strategy programmes
# -------------------

"""
    StrategyProgram

A pipeline, or a chain of pipelines in series, compiled to a mixed-integer linear
programme over deterministic policies: what [`strategy_program`](@ref) returns.
Fields:

- `parts`: the pipelines of the chain, in order.
- `model`: the `JuMP.GenericModel{T}`.
- `policies`: for each open policy box, the array of binary variables
  `z[a, observations...]`.
- `flows`: for each part, the dictionary from joint wire values (a
  `CartesianIndex`) to the flow variable of that path.
- `output_mass`: the expressions for the probability of each joint output of the
  last part (in `joint_states` order), the variables a further part would share.
- `objective`: the objective expression, the sum of the parts' expected utilities.
- `constraints`: the side constraints that were compiled.

`compose` of two strategy programmes is the programme of the chain: the output mass
of the first is identified with the input mass of the second and the objectives are
added.
"""
struct StrategyProgram{T}
    parts::Vector{DecisionPipeline}
    model::JuMP.GenericModel{T}
    policies::Dict{Symbol,Any}
    flows::Vector{Dict{CartesianIndex,Any}}
    output_mass::Vector{Any}
    objective::Any
    constraints::Vector{ExpectationConstraint}
end

function Base.show(io::IO, s::StrategyProgram)
    return print(io, "StrategyProgram(", length(s.parts), " part",
                 length(s.parts) == 1 ? "" : "s", ", ", JuMP.num_variables(s.model),
                 " variables, ", length(s.policies), " decision",
                 length(s.policies) == 1 ? "" : "s", ")")
end

# Add one component to `model`. `input_mass` is a vector over the joint inputs of `p`
# (numbers or affine expressions); returns the flow variables, the policy variables,
# the objective term and the output mass.
function _add_component!(model::JuMP.GenericModel{T}, p::DecisionPipeline, input_mass,
                         constraints) where {T}
    axes = _axes(p)
    names = [a.name for a in axes]
    index = Dict(n => i for (i, n) in enumerate(names))
    open = _open_policies(p)
    skip = [s.name for s in open]
    mass, reward = _accumulate(p, names, skip, :strategy_program)
    quantities = [_accumulate(_with_quantity(p, c), names, skip, :strategy_program)[2]
                  for c in constraints]
    z = Dict{Symbol,Any}()
    for s in open
        shape = (length(axes[index[s.out]]), (length(axes[index[w]]) for w in s.ins)...)
        vars = Array{Any}(undef, shape)
        for ci in CartesianIndices(shape)
            vars[ci] = JuMP.@variable(model, binary = true,
                                      base_name = "z_$(s.name)$(Tuple(ci))")
        end
        for obs in CartesianIndices(shape[2:end])
            JuMP.@constraint(model,
                             sum(vars[a, Tuple(obs)...] for a in 1:shape[1]) == one(T))
        end
        z[s.name] = vars
    end
    in_idx = Int[index[w] for w in p.inputs]
    out_idx = Int[index[w] for w in p.outputs]
    in_sizes = Tuple(length(axes[i]) for i in in_idx)
    out_sizes = Tuple(length(axes[i]) for i in out_idx)
    linear(sizes, idx, ci) = LinearIndices(sizes)[(ci[i] for i in idx)...]
    flows = Dict{CartesianIndex,Any}()
    conservation = [zero(JuMP.GenericAffExpr{T,JuMP.GenericVariableRef{T}})
                    for _ in 1:prod(in_sizes)]
    output_mass = Any[zero(JuMP.GenericAffExpr{T,JuMP.GenericVariableRef{T}})
                      for _ in 1:prod(out_sizes)]
    objective = zero(JuMP.GenericAffExpr{T,JuMP.GenericVariableRef{T}})
    sides = [zero(JuMP.GenericAffExpr{T,JuMP.GenericVariableRef{T}}) for _ in constraints]
    for ci in CartesianIndices(size(mass))
        w = mass[ci]
        iszero(w) && continue
        x = linear(in_sizes, in_idx, ci)
        φ = JuMP.@variable(model, lower_bound = zero(T), base_name = "φ$(Tuple(ci))")
        flows[ci] = φ
        JuMP.@constraint(model, φ <= T(w) * input_mass[x])
        for s in open
            at = (ci[index[s.out]], (ci[index[v]] for v in s.ins)...)
            JuMP.@constraint(model, φ <= z[s.name][at...])
        end
        JuMP.add_to_expression!(conservation[x], φ)
        JuMP.add_to_expression!(output_mass[linear(out_sizes, out_idx, ci)], φ)
        JuMP.add_to_expression!(objective, T(reward[ci] / w), φ)
        for (k, q) in enumerate(quantities)
            JuMP.add_to_expression!(sides[k], T(q[ci] / w), φ)
        end
    end
    for x in eachindex(conservation)
        JuMP.@constraint(model, conservation[x] == input_mass[x])
    end
    return flows, z, objective, output_mass, sides
end

function _build_strategy_program(parts::Vector{DecisionPipeline}, constraints,
                                 ::Type{T}) where {T}
    isempty(first(parts).inputs) ||
        throw(CompilationError("the first pipeline has input wires " *
                               "$(first(parts).inputs); plug values into them first " *
                               "(`intervene`)"))
    for i in 2:length(parts)
        codom(parts[i - 1]) == dom(parts[i]) ||
            throw(WireMismatchError(:compose, nothing, codom(parts[i - 1]), dom(parts[i])))
    end
    model = JuMP.GenericModel{T}()
    policies = Dict{Symbol,Any}()
    flows = Dict{CartesianIndex,Any}[]
    objective = zero(JuMP.GenericAffExpr{T,JuMP.GenericVariableRef{T}})
    mass = Any[one(T)]
    placed = falses(length(constraints))
    for part in parts
        wires = Set(a.name for a in _axes(part))
        mine = [k
                for k in eachindex(constraints)
                if !placed[k] && all(in(wires), constraints[k].wires)]
        placed[mine] .= true
        φ, z, obj, mass, sides = _add_component!(model, part, mass, constraints[mine])
        isempty(intersect(keys(z), keys(policies))) ||
            throw(PipelineStructureError("two parts have policy boxes of the same name"))
        merge!(policies, z)
        push!(flows, φ)
        JuMP.add_to_expression!(objective, obj)
        for (k, side) in zip(mine, sides)
            c = constraints[k]
            c.sense === :at_most ? JuMP.@constraint(model, side <= T(c.bound)) :
            JuMP.@constraint(model, side >= T(c.bound))
        end
    end
    all(placed) ||
        throw(CompilationError("constraint `$(constraints[findfirst(!, placed)].name)` " *
                               "is over wires that no single part of the chain has"))
    JuMP.@objective(model, Max, objective)
    return StrategyProgram{T}(parts, model, policies, flows, mass, objective,
                              collect(ExpectationConstraint, constraints))
end

function _strategy_number_type(parts, constraints)
    S = Int
    for p in parts, s in _specs(p)
        s.table isa AbstractArray && (S = promote_type(S, eltype(s.table)))
        s.table isa FiniteBelief && (S = promote_type(S, eltype(s.table.probabilities)))
    end
    for c in constraints
        S = promote_type(S, typeof(c.bound))
        c.values isa AbstractArray && (S = promote_type(S, eltype(c.values)))
    end
    return _number_type(S)
end

"""
    strategy_program(p::DecisionPipeline; constraints=[], T=nothing) -> StrategyProgram

Compile a pipeline with no input wires and **any number of open policy boxes** to a
mixed-integer linear programme over deterministic policies, in the path formulation
that DecisionProgramming.jl uses for influence diagrams (Salo, Andelmin and
Oliveira 2022). With `s` a joint value of every wire, `w(s)` the product of the
chance tables along it, and `U(s)` the sum of the utility boxes:

    maximise    Σ_s U(s) φ(s)
    subject to  Σ_a z_k[a, i] = 1                 for every decision k and observation i,
                φ(s) ≤ w(s),   φ(s) ≤ z_k[a_k(s), i_k(s)]   for every decision k,
                Σ_s φ(s) = 1,
                side constraints  Σ_s G_c(s) φ(s) ≤ b_c  (or ≥),
                z binary,  φ ≥ 0.

Decision boxes become the binary variables `z` (one local policy each), chance boxes
the weights `w`, utility boxes the objective. For binary `z` the constraints force
`φ(s) = w(s)` on the paths that the policies allow and zero on the others, so the
feasible points are in bijection with the deterministic strategies and the objective
is the expected utility. Decisions need not remember what earlier decisions saw or
did (no perfect recall is assumed), which is why the programme is mixed-integer and
not linear.

`T` is the number type of the model (`Rational{BigInt}` for integer or rational
tables, `Float64` otherwise, unless given). [`solve_strategy_program`](@ref) solves
it.

**Programmes compose.** For pipelines in series,
`compose(strategy_program(p), strategy_program(q))` is one model in which the
probability of each joint value of the shared wires is a shared quantity (the output
mass of `p`'s flow is the input mass of `q`'s) and the objective is the sum of the
two; this is the open-optimisation-problem construction of AlgebraicOptimization.jl
(Hanks et al. 2024) specialised to decision diagrams. It has the same optimum as the
programme of the glued pipeline `strategy_program(compose(p, q))`. Its flow
variables are a sum over the parts where the glued programme has a product over all
wires, which is smaller when the parts have many internal wires and a narrow
interface, and can be larger when the interface carries most of the wires. What
composes here is the **programme**, not its solution: the composite is solved as
one model.
"""
function strategy_program(p::DecisionPipeline; constraints=ExpectationConstraint[],
                          T=nothing)
    parts = DecisionPipeline[p]
    return _build_strategy_program(parts, constraints,
                                   something(T, _strategy_number_type(parts, constraints)))
end

"""
    strategy_program(parts::AbstractVector{DecisionPipeline}; constraints=[], T=nothing)

The strategy programme of a chain of pipelines in series, built part by part with
shared interface masses: the same as composing the programmes of the parts.
"""
function strategy_program(parts::AbstractVector{DecisionPipeline};
                          constraints=ExpectationConstraint[], T=nothing)
    ps = collect(DecisionPipeline, parts)
    isempty(ps) && throw(ArgumentError("a chain needs at least one pipeline"))
    return _build_strategy_program(ps, constraints,
                                   something(T, _strategy_number_type(ps, constraints)))
end

function compose(a::StrategyProgram{S}, b::StrategyProgram{T}) where {S,T}
    isempty(first(b.parts).inputs) &&
        throw(CompilationError("the second programme is closed: it has no input " *
                               "interface to share. Compile the open pipeline as a " *
                               "chain, `strategy_program([p, q])`"))
    return _build_strategy_program(vcat(a.parts, b.parts),
                                   vcat(a.constraints, b.constraints), promote_type(S, T))
end

"""
    open_strategy_program(q::DecisionPipeline; constraints=[]) -> StrategyProgram

The strategy programme of an **open** pipeline (one with input wires), with the
input mass left as free variables: a programme waiting for its context. It is not
solvable alone; `compose(strategy_program(p), open_strategy_program(q))` joins it
to a closed programme upstream.
"""
function open_strategy_program(q::DecisionPipeline; constraints=ExpectationConstraint[])
    T = _strategy_number_type([q], constraints)
    model = JuMP.GenericModel{T}()
    n = length(dom(q))
    m = Any[JuMP.@variable(model, lower_bound = zero(T), base_name = "m[$x]") for x in 1:n]
    φ, z, objective, mass, sides = _add_component!(model, q, m, constraints)
    for (c, side) in zip(constraints, sides)
        c.sense === :at_most ? JuMP.@constraint(model, side <= T(c.bound)) :
        JuMP.@constraint(model, side >= T(c.bound))
    end
    JuMP.@objective(model, Max, objective)
    return StrategyProgram{T}(DecisionPipeline[q], model, z, [φ], mass, objective,
                              collect(ExpectationConstraint, constraints))
end

"""
    StrategySolution

What [`solve_strategy_program`](@ref) returns: `status`, `value` (the expected
utility of the strategy, recomputed exactly from the pipeline), `policies` (for each
decision box, the array of action labels, one per joint observation), `route`
(`:enumeration` or `:optimizer`), `exact` (whether optimality is an exact statement:
true for enumeration, false for an optimiser, whose strategy is feasible and whose
value is exact but whose optimality rests on the optimiser) and `strategies` (the
number examined by enumeration, or `nothing`).
"""
struct StrategySolution
    status::Symbol
    value::Any
    policies::Dict{Symbol,Any}
    route::Symbol
    exact::Bool
    strategies::Union{Nothing,Int}
end

function Base.show(io::IO, s::StrategySolution)
    return print(io, "StrategySolution(", s.status, ", value = ", s.value, ", ", s.route,
                 ")")
end

function _glued(parts::Vector{DecisionPipeline})
    length(parts) == 1 && return only(parts)
    return _glue(parts, first(parts).inputs, last(parts).outputs)
end

# The value and the constrained quantities of a pipeline under bound policies.
function _strategy_outcome(p::DecisionPipeline, constraints, binding)
    q = bind_policy(p, binding...)
    value = pipeline_value(q)
    quantities = [pipeline_value(_with_quantity(q, c)) for c in constraints]
    return value, quantities
end

function _satisfied(c::ExpectationConstraint, x, tol)
    return c.sense === :at_most ? x <= c.bound + tol :
           x >= c.bound - tol
end

"""
    solve_strategy_program(program::StrategyProgram; optimizer=nothing, max_strategies=100_000)
        -> StrategySolution

Solve a strategy programme.

- **`optimizer = nothing` (the default): exact enumeration.** Every deterministic
  strategy is evaluated on the pipeline in exact arithmetic, those violating a side
  constraint are discarded, and the best is returned. No solver is needed; it is
  meant for small problems (more than `max_strategies` strategies throw
  [`CompilationError`](@ref)).
- **A mixed-integer optimiser** (anything `JuMP.set_optimizer` accepts, for example
  `HiGHS.Optimizer`): the model is solved in `Float64`, the binary variables are
  read back as a strategy, and that strategy is then evaluated on the pipeline in
  exact arithmetic and its side constraints checked. The value returned is therefore
  exact for the strategy returned; that no better strategy exists is the optimiser's
  claim (`exact = false`).

The programme must be closed (no free input mass).
"""
function solve_strategy_program(program::StrategyProgram; optimizer=nothing,
                                max_strategies::Integer=100_000)
    p = _glued(program.parts)
    isempty(p.inputs) ||
        throw(CompilationError("the programme is open (inputs $(p.inputs)); compose it " *
                               "with a closed programme upstream first"))
    open = _open_policies(p)
    cs = program.constraints
    shapes = Dict(s.name => Tuple(length(_axis(p, w)) for w in s.ins) for s in open)
    labels = Dict(s.name => _axis(p, s.out).labels for s in open)
    T = eltype(program)
    tol = _exact(T) ? 0 : 1e-9
    if optimizer === nothing
        slots = [(s.name, ci) for s in open for ci in CartesianIndices(shapes[s.name])]
        total = prod(big(length(labels[name])) for (name, _) in slots; init=big(1))
        total <= max_strategies ||
            throw(CompilationError("$total deterministic strategies are more than " *
                                   "`max_strategies` = $max_strategies; pass a " *
                                   "mixed-integer optimiser"))
        best, best_tables = nothing, nothing
        choices = isempty(slots) ? [()] :
                  Iterators.product((labels[name] for (name, _) in slots)...)
        for choice in choices
            tables = Dict{Symbol,Any}(s.name => Array{Symbol}(undef, shapes[s.name])
                                      for s in open)
            for (k, (name, ci)) in enumerate(slots)
                tables[name][ci] = choice[k]
            end
            value, quantities = _strategy_outcome(p, cs, pairs(tables))
            all(_satisfied(c, x, tol) for (c, x) in zip(cs, quantities)) || continue
            if best === nothing || value > best
                best, best_tables = value, tables
            end
        end
        best === nothing &&
            return StrategySolution(:infeasible, nothing, Dict{Symbol,Any}(),
                                    :enumeration, true, Int(total))
        return StrategySolution(:optimal, best, best_tables, :enumeration, true,
                                Int(total))
    end
    twin = T === Float64 ? program :
           _build_strategy_program(program.parts, cs, Float64)
    JuMP.set_optimizer(twin.model, optimizer)
    JuMP.set_silent(twin.model)
    JuMP.optimize!(twin.model)
    status = JuMP.termination_status(twin.model)
    status == JuMP.MOI.OPTIMAL ||
        return StrategySolution(status == JuMP.MOI.INFEASIBLE ? :infeasible :
                                Symbol(lowercase(string(status))), nothing,
                                Dict{Symbol,Any}(), :optimizer, false, nothing)
    tables = Dict{Symbol,Any}()
    for s in open
        z = twin.policies[s.name]
        tables[s.name] = [labels[s.name][argmax([JuMP.value(z[a, Tuple(ci)...])
                                                 for a in eachindex(labels[s.name])])]
                          for ci in CartesianIndices(shapes[s.name])]
    end
    value, quantities = _strategy_outcome(p, cs, pairs(tables))
    all(_satisfied(c, x, _exact(T) ? 0 : 1e-6) for (c, x) in zip(cs, quantities)) ||
        throw(ExactVerificationError(:strategy_program,
                                     "the strategy returned by the optimiser violates " *
                                     "a side constraint when evaluated exactly"))
    return StrategySolution(:optimal, value, tables, :optimizer, false, nothing)
end

Base.eltype(::StrategyProgram{T}) where {T} = T
