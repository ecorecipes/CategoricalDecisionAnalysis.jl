# Decision pipelines (component 6 of the plan): typed diagrams with box kinds Belief,
# Channel, Policy, Consequence and Utility, and the interpreters that map a diagram
# into DecisionAnalysis.
#
# Structural syntax and numerical semantics are separate, as in the open influence
# diagrams of CategoricalInfluenceDiagrams (its ADR 0018): the shape of a pipeline is
# an ACSet (`PipelineGraph`), and the tables of its boxes are kept beside it, never as
# ACSet attributes.
#
# A pipeline is a string diagram written with named wires: a wire used by several
# boxes is copied, a wire used by none is discarded. Its semantics for fixed policies
# is the expectation-semiring kernel `(K, W)` of CategoricalInfluenceDiagrams'
# `RewardKernel`, here with entries of any real type (`ValuedKernel`), so that
# rational pipelines are evaluated exactly.

@present SchDecisionPipeline(FreeSchema) begin
    (Wire, Box, InPort, OutPort)::Ob
    in_box::Hom(InPort, Box)
    in_wire::Hom(InPort, Wire)
    out_box::Hom(OutPort, Box)
    out_wire::Hom(OutPort, Wire)
    (Name, Labels)::AttrType
    wire_name::Attr(Wire, Name)
    wire_labels::Attr(Wire, Labels)
    box_name::Attr(Box, Name)
    box_kind::Attr(Box, Name)
end

@acset_type PipelineGraph(SchDecisionPipeline,
                          index=[:in_box, :in_wire, :out_box, :out_wire])

@doc """
    PipelineGraph

The ACSet type that holds the shape of a [`DecisionPipeline`](@ref): parts `Wire`
(attributes `wire_name`, `wire_labels`), `Box` (`box_name`, `box_kind`), `InPort`
(`in_box`, `in_wire`) and `OutPort` (`out_box`, `out_wire`). The input ports of a
box are ordered by part number. Tables are not stored here.
""" PipelineGraph

const BOX_KINDS = (:belief, :channel, :policy, :consequence, :utility)

@doc """
    BOX_KINDS

The five kinds of box in a [`DecisionPipeline`](@ref):
`(:belief, :channel, :policy, :consequence, :utility)`.
""" BOX_KINDS

struct _BoxSpec
    name::Symbol
    kind::Symbol
    ins::Vector{Symbol}
    out::Union{Nothing,Symbol}
    table::Any
    error::Any
end

"""
    DecisionPipeline

A decision analysis as a typed diagram. Wires are named finite variables (a name and
its labels); boxes consume and produce wires and have one of five kinds:

| kind | shape | meaning | table |
|:--|:--|:--|:--|
| Belief | `I → Θ` | what is believed about a state | a belief of DecisionAnalysis |
| Channel | `Θ… → Z` | an observation process | `P(z | inputs)`, output axis first |
| Policy | `Z… → A` | a decision; open until a policy is bound | optional `P(a | observations)` |
| Consequence | `A, Θ… → Y` | an outcome model | `P(y | inputs)`, output axis first |
| Utility | `Y… → ℝ` | individuals counted | one number per joint input |

Build single boxes with [`belief_box`](@ref), [`channel_box`](@ref),
[`policy_box`](@ref), [`consequence_box`](@ref) and [`utility_box`](@ref), and join
them by wire name with [`decision_pipeline`](@ref), or categorically with `compose` (in
series, the interfaces must match) and `otimes` (side by side). A wire read by
several boxes is copied and a wire read by none is discarded, as in any string
diagram of a Markov category. Wires that no box produces are the inputs of the
pipeline (`dom`); the wires it exposes are its outputs (`codom`). **An action can be
an input wire**: the model is then open in the action, and
[`intervene`](@ref) substitutes a value on the wire.

Interpreters, each a function from the diagram into DecisionAnalysis:

- [`evaluate`](@ref evaluate(::DecisionPipeline)): the kernel and expected utility
  of the diagram for fixed policies, compositionally ([`ValuedKernel`](@ref));
- [`decision_problem`](@ref) and [`observation_experiment`](@ref): the payoff table,
  belief and experiment of a pipeline with one decision, on which `decide`,
  `regret_table`, `evpi`, `evsi` and `value_with_information` are then forwarded;
- [`value_of_information`](@ref): the values of the pipeline's own observation and
  of perfect information;
- [`box_provenance`](@ref): which boxes a number depends on;
- [`fidelity_bound`](@ref): the decision-loss bound read off the boxes' stated
  errors;
- [`policy_program`](@ref) and [`strategy_program`](@ref): the diagram compiled to a
  JuMP model.

The shape is an ACSet ([`PipelineGraph`](@ref), from [`pipeline_graph`](@ref)); the
tables are kept beside it. A pipeline is immutable: every operation returns a new
one.
"""
struct DecisionPipeline
    graph::PipelineGraph{Symbol,Vector{Symbol}}
    tables::Dict{Symbol,Any}
    errors::Dict{Symbol,Any}
    inputs::Vector{Symbol}
    outputs::Vector{Symbol}
    global function _pipeline(graph, tables, errors, inputs, outputs)
        return new(graph, tables, errors, inputs, outputs)
    end
end

# Reading the ACSet
# -----------------

"""
    pipeline_graph(p::DecisionPipeline) -> PipelineGraph

The shape of the pipeline as an ACSet (a copy).
"""
pipeline_graph(p::DecisionPipeline) = copy(p.graph)

function _axes(p::DecisionPipeline)
    g = p.graph
    return FiniteAxis[FiniteAxis(subpart(g, w, :wire_name), subpart(g, w, :wire_labels))
                      for w in parts(g, :Wire)]
end
_axis(p::DecisionPipeline, name::Symbol) = _axes(p)[_wire_index(p, name)]
function _wire_index(p::DecisionPipeline, name::Symbol)
    i = findfirst(==(name), subpart(p.graph, :wire_name))
    i === nothing && throw(PipelineStructureError("the pipeline has no wire `$name`"))
    return i
end

function _specs(p::DecisionPipeline)
    g = p.graph
    return map(parts(g, :Box)) do b
        name = subpart(g, b, :box_name)
        ins = Symbol[subpart(g, subpart(g, port, :in_wire), :wire_name)
                     for port in sort(incident(g, b, :in_box))]
        outs = Symbol[subpart(g, subpart(g, port, :out_wire), :wire_name)
                      for port in incident(g, b, :out_box)]
        return _BoxSpec(name, subpart(g, b, :box_kind), ins,
                        isempty(outs) ? nothing : only(outs), get(p.tables, name, nothing),
                        get(p.errors, name, 0))
    end
end

function _spec(p::DecisionPipeline, box::Symbol)
    i = findfirst(s -> s.name == box, _specs(p))
    i === nothing && throw(PipelineStructureError("the pipeline has no box `$box`"))
    return _specs(p)[i]
end

"""
    pipeline_boxes(p::DecisionPipeline) -> Vector{NamedTuple}

The boxes of the pipeline in the order they were added, each as
`(name, kind, inputs, output, bound, error)`: `bound` says whether the box has a
table (an open policy box has none) and `error` is its stated fidelity error.
"""
function pipeline_boxes(p::DecisionPipeline)
    return [(name=s.name, kind=s.kind, inputs=copy(s.ins), output=s.out,
             bound=s.table !== nothing, error=s.error) for s in _specs(p)]
end

"""
    pipeline_wires(p::DecisionPipeline) -> Vector{Pair{Symbol,Vector{Symbol}}}

The wires of the pipeline, each as `name => labels`.
"""
pipeline_wires(p::DecisionPipeline) = [a.name => copy(a.labels) for a in _axes(p)]

function Base.show(io::IO, p::DecisionPipeline)
    specs = _specs(p)
    print(io, "DecisionPipeline: ", length(specs), " box", length(specs) == 1 ? "" : "es",
          ", inputs ", p.inputs, ", outputs ", p.outputs)
    for s in specs
        print(io, "\n  ", rpad(s.kind, 12), s.name, " : ",
              isempty(s.ins) ? "I" :
              join(s.ins, " ⊗ "), " → ",
              s.out === nothing ? "ℝ" : s.out)
        s.table === nothing && print(io, "   (open)")
        iszero(s.error) || print(io, "   (error ", s.error, ")")
    end
    return nothing
end

function Base.:(==)(a::DecisionPipeline, b::DecisionPipeline)
    return a.inputs == b.inputs && a.outputs == b.outputs &&
           Set(pipeline_wires(a)) == Set(pipeline_wires(b)) &&
           Set(pipeline_boxes(a)) == Set(pipeline_boxes(b)) && a.tables == b.tables
end

# Assembly and validation
# -----------------------

_axis_of(w::FiniteAxis) = w
function _axis_of(w::Pair)
    return FiniteAxis(Symbol(first(w)), Symbol[Symbol(l) for l in last(w)])
end
function _axis_of(w)
    throw(ArgumentError("a wire is written `name => labels` (or is a FiniteAxis); " *
                        "got $w"))
end
_axes_of(ws::Union{Tuple,AbstractVector}) = FiniteAxis[_axis_of(w) for w in ws]
_axes_of(w) = FiniteAxis[_axis_of(w)]

function _stochastic_defect(table::AbstractArray, what)
    T = eltype(table)
    atol = _default_atol(T)
    all(x -> isfinite(x) && x >= -atol, table) ||
        return "the table of $what has a negative or non-finite entry"
    sums = sum(table; dims=1)
    all(s -> abs(s - 1) <= atol, sums) ||
        return "the table of $what does not sum to one over its output for every input"
    return nothing
end

function _check_table(s::_BoxSpec, axis::Dict{Symbol,FiniteAxis})
    s.table === nothing && return nothing
    insize = Tuple(length(axis[w]) for w in s.ins)
    if s.kind === :belief
        s.table isa AbstractBelief ||
            throw(PipelineStructureError("the belief box `$(s.name)` holds no belief"))
        labels = axis[s.out].labels
        ok = s.table isa PointBelief ? s.table.state in labels :
             s.table isa ScenarioSet ? all(in(labels), s.table.states) :
             state_labels(s.table) == labels
        ok || throw(WireMismatchError(:belief_box, s.out, labels, state_labels(s.table)))
    elseif s.kind === :utility
        size(s.table) == insize ||
            throw(PipelineStructureError("the table of utility box `$(s.name)` has size " *
                                         "$(size(s.table)); its inputs have $insize"))
        all(isfinite, s.table) ||
            throw(PipelineStructureError("the table of utility box `$(s.name)` has an " *
                                         "entry that is not finite"))
    else
        expected = (length(axis[s.out]), insize...)
        size(s.table) == expected ||
            throw(PipelineStructureError("the table of $(s.kind) box `$(s.name)` has " *
                                         "size $(size(s.table)); expected $expected " *
                                         "(output axis first, then the inputs)"))
        defect = _stochastic_defect(s.table, "$(s.kind) box `$(s.name)`")
        defect === nothing || throw(PipelineStructureError(defect))
    end
    return nothing
end

# Boxes in an order in which every box comes after the producers of its inputs.
function _topological(specs::Vector{_BoxSpec})
    producer = Dict(s.out => i for (i, s) in enumerate(specs) if s.out !== nothing)
    order, state = Int[], zeros(Int, length(specs))
    function visit(i)
        state[i] == 2 && return nothing
        state[i] == 1 &&
            throw(PipelineStructureError("the pipeline has a cycle through box " *
                                         "`$(specs[i].name)`"))
        state[i] = 1
        for w in specs[i].ins
            haskey(producer, w) && visit(producer[w])
        end
        state[i] = 2
        push!(order, i)
        return nothing
    end
    foreach(visit, eachindex(specs))
    return order
end

function _assemble(axes::Vector{FiniteAxis}, specs::Vector{_BoxSpec},
                   inputs::Vector{Symbol}, outputs::Vector{Symbol})
    axis = Dict{Symbol,FiniteAxis}()
    for a in axes
        if haskey(axis, a.name)
            axis[a.name] == a ||
                throw(WireMismatchError(:pipeline, a.name, axis[a.name].labels, a.labels))
        else
            axis[a.name] = a
        end
    end
    allunique([s.name for s in specs]) ||
        throw(PipelineStructureError("two boxes have the same name: " *
                                     "$([s.name for s in specs])"))
    allunique(inputs) || throw(PipelineStructureError("an input wire is listed twice"))
    allunique(outputs) || throw(PipelineStructureError("an output wire is listed twice"))
    produced = Set{Symbol}()
    for s in specs
        s.kind in BOX_KINDS ||
            throw(PipelineStructureError("unknown box kind `$(s.kind)`"))
        (s.kind === :utility) == (s.out === nothing) ||
            throw(PipelineStructureError("box `$(s.name)`: a utility box has no output " *
                                         "wire and every other box has exactly one"))
        s.kind === :belief && !isempty(s.ins) &&
            throw(PipelineStructureError("the belief box `$(s.name)` has input wires"))
        allunique(s.ins) ||
            throw(PipelineStructureError("box `$(s.name)` reads a wire twice"))
        for w in (s.ins..., (s.out === nothing ? () : (s.out,))...)
            haskey(axis, w) ||
                throw(PipelineStructureError("box `$(s.name)` uses the unknown wire `$w`"))
        end
        if s.out !== nothing
            s.out in produced &&
                throw(PipelineStructureError("wire `$(s.out)` is produced by two boxes"))
            push!(produced, s.out)
        end
        (s.error isa Real && s.error >= 0) ||
            throw(ArgumentError("the error of box `$(s.name)` must be a nonnegative " *
                                "number, got $(s.error)"))
        _check_table(s, axis)
    end
    for w in inputs
        haskey(axis, w) || throw(PipelineStructureError("unknown input wire `$w`"))
        w in produced &&
            throw(PipelineStructureError("the input wire `$w` is produced by a box"))
    end
    for w in outputs
        haskey(axis, w) || throw(PipelineStructureError("unknown output wire `$w`"))
    end
    for s in specs, w in s.ins
        (w in produced || w in inputs) ||
            throw(PipelineStructureError("box `$(s.name)` reads wire `$w`, which no box " *
                                         "produces and which is not an input"))
    end
    for a in axes
        (a.name in produced || a.name in inputs) ||
            throw(PipelineStructureError("wire `$(a.name)` is neither produced by a box " *
                                         "nor an input"))
    end
    _topological(specs)
    g = PipelineGraph{Symbol,Vector{Symbol}}()
    names = unique([a.name for a in axes])
    wire = Dict(n => add_part!(g, :Wire; wire_name=n, wire_labels=copy(axis[n].labels))
                for n in names)
    tables, errors = Dict{Symbol,Any}(), Dict{Symbol,Any}()
    for s in specs
        b = add_part!(g, :Box; box_name=s.name, box_kind=s.kind)
        for w in s.ins
            add_part!(g, :InPort; in_box=b, in_wire=wire[w])
        end
        s.out === nothing || add_part!(g, :OutPort; out_box=b, out_wire=wire[s.out])
        s.table === nothing ||
            (tables[s.name] = s.table isa AbstractArray ? copy(s.table) : s.table)
        iszero(s.error) || (errors[s.name] = s.error)
    end
    return _pipeline(g, tables, errors, copy(inputs), copy(outputs))
end

function _single_box(name, kind, ins, out, table, error)
    in_axes = _axes_of(ins)
    out_axis = out === nothing ? nothing : _axis_of(out)
    axes = out_axis === nothing ? in_axes : vcat(in_axes, [out_axis])
    spec = _BoxSpec(Symbol(name), kind, [a.name for a in in_axes],
                    out_axis === nothing ? nothing : out_axis.name, table, error)
    return _assemble(axes, [spec], [a.name for a in in_axes],
                     out_axis === nothing ? Symbol[] : [out_axis.name])
end

_as_belief(b::AbstractBelief, ::FiniteAxis) = b
_as_belief(p::AbstractVector{<:Real}, a::FiniteAxis) = FiniteBelief(a.labels, p)
_as_belief(s::Symbol, ::FiniteAxis) = PointBelief(s)
function _as_belief(x, ::FiniteAxis)
    throw(ArgumentError("a belief is a belief of DecisionAnalysis, a probability " *
                        "vector or a state label; got $(typeof(x))"))
end

"""
    belief_box(name, wire, belief; error=0) -> DecisionPipeline

A Belief box `I → Θ`: what is believed about the state carried by `wire`
(`:name => labels`). `belief` is a probability vector over the labels, a state label
(a point belief), or any belief of DecisionAnalysis over those labels (`FiniteBelief`,
`PointBelief`, `CredalSet`, `ScenarioSet`). The monad of the belief is part of the
type of the pipeline: an interpreter that needs a single distribution refuses a
credal or scenario belief ([`MonadMismatchError`](@ref)), and rules are matched to
it as in DecisionAnalysis. `error` is a stated total-variation error of the belief
(see [`fidelity_bound`](@ref)).
"""
function belief_box(name, wire, belief; error::Real=0)
    axis = _axis_of(wire)
    return _single_box(name, :belief, FiniteAxis[], axis, _as_belief(belief, axis), error)
end

"""
    channel_box(name, inputs, output, table; error=0) -> DecisionPipeline

A Channel box: an observation process from the `inputs` (one wire or a tuple of
wires) to the `output` wire. `table[z, inputs...] = P(z | inputs)`, output axis
first; for one input it is the likelihood matrix of an `Experiment`
(rows = signals, columns = states). `error` is the stated error of the table as a
model of the true process: the largest total-variation distance, over the inputs,
between the two ([`kernel_distance`](@ref), [`fidelity_bound`](@ref)).
"""
function channel_box(name, inputs, output, table::AbstractArray{<:Real}; error::Real=0)
    return _single_box(name, :channel, inputs, output, table, error)
end

"""
    consequence_box(name, inputs, output, table; error=0) -> DecisionPipeline

A Consequence box: an outcome model from the `inputs` (typically an action and a
state; one wire or a tuple of wires) to the `output` wire, with
`table[y, inputs...] = P(y | inputs)`, output axis first. It differs from a
[`channel_box`](@ref) only in what it is for: a channel is observed before deciding,
a consequence follows from the decision. `error` is as for a channel.
"""
function consequence_box(name, inputs, output, table::AbstractArray{<:Real}; error::Real=0)
    return _single_box(name, :consequence, inputs, output, table, error)
end

"""
    policy_box(name, observations, action, [policy]) -> DecisionPipeline

A Policy box: a decision that sets the `action` wire knowing the `observations`
(one wire, a tuple of wires, or `()` for none). Without `policy` the box is **open**:
it is what the optimising interpreters choose. With `policy` it is bound
([`bind_policy`](@ref) describes the forms a policy can take).
"""
function policy_box(name, observations, action, policy=nothing)
    p = _single_box(name, :policy, observations, action, nothing, 0)
    return policy === nothing ? p : bind_policy(p, Symbol(name) => policy)
end

"""
    utility_box(name, inputs, table) -> DecisionPipeline

A Utility box: an effect on the `inputs` (one wire or a tuple of wires), a count of
individuals for every joint value of them, `table[inputs...]`. Several utility boxes
in one pipeline add. Utilities are counts of individuals of the focal species (for a
disease, uninfected individuals count for and infected against), never money.
"""
function utility_box(name, inputs, table::AbstractArray{<:Real})
    return _single_box(name, :utility, inputs, nothing, table, 0)
end
function utility_box(name, inputs, f::Function)
    axes = _axes_of(inputs)
    table = [f(ntuple(i -> axes[i].labels[ci[i]], length(axes))...)
             for ci in CartesianIndices(Tuple(length(a) for a in axes))]
    return utility_box(name, inputs, table)
end

function _glue(parts::Vector{DecisionPipeline}, inputs, outputs)
    axes = reduce(vcat, [_axes(p) for p in parts]; init=FiniteAxis[])
    specs = reduce(vcat, [_specs(p) for p in parts]; init=_BoxSpec[])
    produced = Set(s.out for s in specs if s.out !== nothing)
    free = unique([w for p in parts for w in p.inputs if !(w in produced)])
    ins = inputs === nothing ? free : Symbol[Symbol(w) for w in inputs]
    inputs === nothing || issetequal(ins, free) ||
        throw(PipelineStructureError("the inputs given are $ins; the wires that no box " *
                                     "produces are $free"))
    outs = outputs === nothing ? Symbol[] : Symbol[Symbol(w) for w in outputs]
    return _assemble(unique(axes), specs, ins, outs)
end

"""
    decision_pipeline(parts::DecisionPipeline...; inputs=nothing, outputs=Symbol[]) -> DecisionPipeline

Join pipelines (usually single boxes) by wire name: a wire that one part produces and
others read is connected to all of them. The wires that no part produces are the
inputs of the result (`inputs` may give their order), and `outputs` lists the wires
to expose, none by default. Two wires with the same name must have the same labels
([`WireMismatchError`](@ref)); a wire produced twice, a cycle or a repeated box name
throw [`PipelineStructureError`](@ref).

```jldoctest
julia> state = :pond => [:clear, :infected]; action = :action => [:wait, :treat];

julia> p = decision_pipeline(belief_box(:prior, state, [7 // 10, 3 // 10]),
                             policy_box(:manager, (), action),
                             utility_box(:frogs, (action, state), [90 20; 70 60]));

julia> decision_problem(p).payoff.Q
2×2 Matrix{Int64}:
 90  20
 70  60

julia> decide(p, MaxExpectedUtility()).chosen
1-element Vector{Symbol}:
 :wait
```
"""
function decision_pipeline(parts::DecisionPipeline...; inputs=nothing, outputs=Symbol[])
    isempty(parts) && throw(ArgumentError("`decision_pipeline` needs at least one part"))
    return _glue(collect(DecisionPipeline, parts), inputs, outputs)
end

"""
    identity_pipeline(wires...) -> DecisionPipeline

The pipeline with no boxes that passes the given wires through: the identity on
them for `compose`.
"""
function identity_pipeline(wires...)
    axes = _axes_of(collect(wires))
    names = [a.name for a in axes]
    return _assemble(axes, _BoxSpec[], names, names)
end
identity_pipeline(X::FiniteSpace) = identity_pipeline(factors(X)...)

dom(p::DecisionPipeline) = FiniteSpace(FiniteAxis[_axis(p, w) for w in p.inputs])
codom(p::DecisionPipeline) = FiniteSpace(FiniteAxis[_axis(p, w) for w in p.outputs])

function _check_disjoint(operation, p::DecisionPipeline, q::DecisionPipeline, shared)
    boxes = intersect([s.name for s in _specs(p)], [s.name for s in _specs(q)])
    isempty(boxes) ||
        throw(PipelineStructureError("`$operation`: both pipelines have boxes named " *
                                     "$boxes; rename one side"))
    wires = setdiff(intersect([a.name for a in _axes(p)], [a.name for a in _axes(q)]),
                    shared)
    isempty(wires) ||
        throw(PipelineStructureError("`$operation`: both pipelines have wires named " *
                                     "$wires that are not on the shared interface; " *
                                     "rename one side (`rename_wires`)"))
    return nothing
end

function compose(p::DecisionPipeline, q::DecisionPipeline)
    codom(p) == dom(q) || throw(WireMismatchError(:compose, nothing, codom(p), dom(q)))
    _check_disjoint(:compose, p, q, p.outputs)
    return _glue([p, q], p.inputs, q.outputs)
end
function compose(p::DecisionPipeline, q::DecisionPipeline, r::DecisionPipeline,
                 rs::DecisionPipeline...)
    return compose(compose(p, q), r, rs...)
end

function otimes(p::DecisionPipeline, q::DecisionPipeline)
    _check_disjoint(:otimes, p, q, Symbol[])
    return _glue([p, q], vcat(p.inputs, q.inputs), vcat(p.outputs, q.outputs))
end
function otimes(p::DecisionPipeline, q::DecisionPipeline, r::DecisionPipeline,
                rs::DecisionPipeline...)
    return otimes(otimes(p, q), r, rs...)
end

@doc """
    compose(p::DecisionPipeline, q::DecisionPipeline, rs...) -> DecisionPipeline
    compose(a::ValuedKernel, b::ValuedKernel, cs...) -> ValuedKernel

Sequential composition in diagrammatic order (first `p`, then `q`), a method of
Catlab's `compose`. For pipelines, the outputs of `p` must be the inputs of `q`, the
same wires in the same order ([`WireMismatchError`](@ref)); they are joined, and
apart from them the two pipelines must share no wire or box name
([`PipelineStructureError`](@ref); see [`rename_wires`](@ref)). For valued kernels
it is the expectation-semiring composition `(K₁K₂, W₁K₂ + K₁W₂)`.

Evaluation is compositional: `evaluate(compose(p, q)) == compose(evaluate(p),
evaluate(q))` for pipelines whose policies are bound.
""" compose(::DecisionPipeline, ::DecisionPipeline)

@doc """
    otimes(p::DecisionPipeline, q::DecisionPipeline, rs...) -> DecisionPipeline
    otimes(a::ValuedKernel, b::ValuedKernel, cs...) -> ValuedKernel

Parallel composition, a method of Catlab's `otimes`: the two pipelines side by side,
with no wire or box name in common. For valued kernels it is
`(K₁ ⊗ K₂, W₁ ⊗ K₂ + K₁ ⊗ W₂)`. Evaluation preserves it:
`evaluate(otimes(p, q)) == otimes(evaluate(p), evaluate(q))`.
""" otimes(::DecisionPipeline, ::DecisionPipeline)

@doc """
    dom(p::DecisionPipeline) -> FiniteSpace
    codom(p::DecisionPipeline) -> FiniteSpace
    dom(v::ValuedKernel), codom(v::ValuedKernel)

The input and output interface as a `FiniteSpace` of FiniteKernels (one axis per
wire, in order): methods of Catlab's `dom` and `codom`.
""" dom(::DecisionPipeline)

"""
    rename_wires(p::DecisionPipeline, renames::Pair{Symbol,Symbol}...) -> DecisionPipeline

The same pipeline with wires renamed (`:old => :new`). Wires are joined by name, so
two copies of a model, or two steps of a process on the same variable, need distinct
names before they are composed. Box names are changed with
[`rename_boxes`](@ref).
"""
function rename_wires(p::DecisionPipeline, renames::Pair{Symbol,Symbol}...)
    r = Dict(renames)
    f(w) = get(r, w, w)
    axes = FiniteAxis[FiniteAxis(f(a.name), a.labels) for a in _axes(p)]
    specs = _BoxSpec[_BoxSpec(s.name, s.kind, f.(s.ins),
                              s.out === nothing ? nothing :
                              f(s.out), s.table, s.error)
                     for s in _specs(p)]
    return _assemble(axes, specs, f.(p.inputs), f.(p.outputs))
end

"""
    rename_boxes(p::DecisionPipeline, renames::Pair{Symbol,Symbol}...) -> DecisionPipeline

The same pipeline with boxes renamed (`:old => :new`).
"""
function rename_boxes(p::DecisionPipeline, renames::Pair{Symbol,Symbol}...)
    r = Dict(renames)
    specs = _BoxSpec[_BoxSpec(get(r, s.name, s.name), s.kind, s.ins, s.out, s.table,
                              s.error) for s in _specs(p)]
    return _assemble(_axes(p), specs, p.inputs, p.outputs)
end

function _replace_spec(p::DecisionPipeline, box::Symbol, f)
    specs = _specs(p)
    i = findfirst(s -> s.name == box, specs)
    i === nothing && throw(PipelineStructureError("the pipeline has no box `$box`"))
    specs[i] = f(specs[i])
    return _assemble(_axes(p), specs, p.inputs, p.outputs)
end

# A policy in any accepted form as a table `P(a | observations)`, output axis first.
function _policy_table(policy::AbstractArray{<:Real}, ::FiniteAxis, ::Vector{FiniteAxis})
    return policy
end
function _policy_table(policy, action::FiniteAxis, obs::Vector{FiniteAxis})
    sizes = Tuple(length(a) for a in obs)
    table = zeros(Int, length(action), sizes...)
    for ci in CartesianIndices(sizes)
        z = ntuple(i -> obs[i].labels[ci[i]], length(obs))
        a = policy isa Symbol ? policy :
            policy isa AbstractArray ? policy[ci] :
            policy isa AbstractDict ?
            policy[length(z) == 1 && !haskey(policy, z) ?
                   z[1] : z] : policy(z...)
        i = findfirst(==(Symbol(a)), action.labels)
        i === nothing &&
            throw(ArgumentError("the policy chooses `$a`, which is not a label of " *
                                "the action wire `$(action.name)`"))
        table[i, Tuple(ci)...] = 1
    end
    return table
end

"""
    bind_policy(p::DecisionPipeline, bindings::Pair...) -> DecisionPipeline

Give policies to policy boxes (`:box => policy`). A policy may be

- a table `P(a | observations)` with the action axis first (a stochastic policy);
- an action label (the same action whatever is observed);
- an array of action labels, one per joint observation;
- a dictionary from observation labels (a label, or a tuple of labels) to action
  labels;
- a function of the observation labels returning an action label.

`:box => nothing` opens the box again.
"""
function bind_policy(p::DecisionPipeline, bindings::Pair...)
    for (box, policy) in bindings
        p = _replace_spec(p, Symbol(box),
                          function (s)
                              s.kind === :policy ||
                                  throw(PipelineStructureError("box `$(s.name)` is a " *
                                                               "$(s.kind) box, not a " *
                                                               "policy box"))
                              table = policy === nothing ? nothing :
                                      _policy_table(policy, _axis(p, s.out),
                                                    FiniteAxis[_axis(p, w) for w in s.ins])
                              return _BoxSpec(s.name, s.kind, s.ins, s.out, table, s.error)
                          end)
    end
    return p
end

"""
    replace_box(p::DecisionPipeline, box, table; error=nothing) -> DecisionPipeline

The same pipeline with the table of `box` replaced, for example a submodel by an
emulator of it. The new table must have the same shape. `error` states how far the
new table is from the one it stands for (the largest total-variation distance over
its inputs, [`kernel_distance`](@ref)); when it is left out the error already
recorded for the box is kept.
"""
function replace_box(p::DecisionPipeline, box, table; error=nothing)
    return _replace_spec(p, Symbol(box),
                         s -> _BoxSpec(s.name, s.kind, s.ins, s.out,
                                       s.kind === :belief ?
                                       _as_belief(table,
                                                  _axis(p, s.out)) :
                                       table, error === nothing ? s.error : error))
end

"""
    with_error(p::DecisionPipeline, errors::Pair...) -> DecisionPipeline

The same pipeline with stated fidelity errors on boxes (`:box => ε`): for a
channel, consequence or bound policy box the largest total-variation distance, over
its inputs, between its table and the true kernel; for a belief box the
total-variation distance between the belief and the true one. See
[`fidelity_bound`](@ref).
"""
function with_error(p::DecisionPipeline, errors::Pair...)
    for (box, ε) in errors
        p = _replace_spec(p, Symbol(box),
                          s -> _BoxSpec(s.name, s.kind, s.ins, s.out, s.table, ε))
    end
    return p
end

"""
    box_errors(p::DecisionPipeline) -> Dict{Symbol,Any}

The stated fidelity error of every box that has one.
"""
box_errors(p::DecisionPipeline) = copy(p.errors)

"""
    intervene(p::DecisionPipeline, settings::Pair...) -> DecisionPipeline

Intervention as substitution on a wire (`:wire => value`). The value is a label
(the wire is set to it), a probability vector over the wire's labels, or a belief of
DecisionAnalysis. If the wire is an input of the pipeline, the value is plugged into
it and the wire is no longer an input. If a box produces the wire, that box is cut
out and replaced by the value: the `do` operation of a causal model, which removes
the mechanism and keeps everything downstream. The new box is a Belief box named
`do_<wire>`.

Setting the action wire of an open model to each of its labels in turn gives the
rows of the payoff table, which is how [`decision_problem`](@ref) reads a pipeline
whose action is an input wire.
"""
function intervene(p::DecisionPipeline, settings::Pair...)
    for (wire, value) in settings
        w = Symbol(wire)
        axis = _axis(p, w)
        specs = filter(s -> s.out != w, _specs(p))
        push!(specs,
              _BoxSpec(Symbol(:do_, w), :belief, Symbol[], w, _as_belief(value, axis), 0))
        p = _assemble(_axes(p), specs, filter(!=(w), p.inputs), p.outputs)
    end
    return p
end

# Enumeration
# -----------

# The factor of a bound box as an array over (output, inputs...), or (inputs...) for a
# utility.
function _factor(s::_BoxSpec, axis::FiniteAxis, operation::Symbol)
    s.table === nothing && throw(UnboundBoxError(s.name, s.kind, operation))
    s.kind === :belief || return s.table
    b = s.table
    b isa FiniteBelief && return b.probabilities
    b isa PointBelief && return [l == b.state ? 1 : 0 for l in axis.labels]
    throw(MonadMismatchError(operation, DistributionMonad(), belief_monad(b),
                             "the belief box `$(s.name)` holds a " *
                             "$(nameof(typeof(b))), which is not a single " *
                             "distribution"))
end

# Sum over every joint assignment of the wires. Boxes in `skip` contribute no factor
# (their output wire is then free). Returns the probability mass and the
# probability-weighted utility accumulated over the wires in `keep`.
function _accumulate(p::DecisionPipeline, keep::Vector{Symbol}, skip, operation::Symbol)
    axes = _axes(p)
    index = Dict(a.name => i for (i, a) in enumerate(axes))
    specs = [s for s in _specs(p) if !(s.name in skip)]
    chance = [(s.kind === :belief ? Int[index[s.out]] :
               Int[index[s.out], (index[w] for w in s.ins)...],
               _factor(s, axes[index[s.out]], operation))
              for s in specs if s.kind !== :utility]
    utility = [(Int[index[w] for w in s.ins], _factor(s, axes[1], operation))
               for s in specs if s.kind === :utility]
    T = mapreduce(f -> eltype(f[2]), promote_type, vcat(chance, utility); init=Int)
    keep_idx = Int[index[w] for w in keep]
    sizes = Tuple(length(a) for a in axes)
    shape = Tuple(sizes[i] for i in keep_idx)
    mass, reward = zeros(T, shape), zeros(T, shape)
    for ci in CartesianIndices(sizes)
        w = one(T)
        for (scope, table) in chance
            w *= table[(ci[i] for i in scope)...]
            iszero(w) && break
        end
        iszero(w) && continue
        r = zero(T)
        for (scope, table) in utility
            r += table[(ci[i] for i in scope)...]
        end
        at = (ci[i] for i in keep_idx)
        mass[at...] += w
        reward[at...] += w * r
    end
    return mass, reward
end

# Valued kernels
# --------------

"""
    ValuedKernel(kernel::FiniteKernel, reward::AbstractArray)

A morphism of the expectation-semiring kernel category with entries of any real
type: what a [`DecisionPipeline`](@ref) with bound policies means. `kernel` is the
`FiniteKernel` `K` from the pipeline's inputs to its outputs, and `reward` is a
table `W` of the same shape, `W[y..., x...]` being the expectation, given the input
`x`, of the utility collected inside the pipeline times the indicator that the
output is `y`. Summed over the outputs it is the expected utility given `x`.

It is the `RewardKernel` of CategoricalInfluenceDiagrams without the restriction to
`Float64`, so a pipeline with rational tables is evaluated exactly;
[`reward_kernel`](@ref) converts. `compose` and `otimes` are those of that package,
`(K₁K₂, W₁K₂ + K₁W₂)` and `(K₁ ⊗ K₂, W₁ ⊗ K₂ + K₁ ⊗ W₂)`, computed with
`compose_kernel` and `tensor_kernel` of FiniteKernels.
"""
struct ValuedKernel{T<:Real}
    kernel::FiniteKernel
    reward::Array{T}
    function ValuedKernel(kernel::FiniteKernel, reward::AbstractArray{<:Real})
        size(reward) == size(kernel.table) ||
            throw(ArgumentError("the reward table has size $(size(reward)) and the " *
                                "kernel table $(size(kernel.table))"))
        T = promote_type(eltype(kernel), eltype(reward))
        return new{T}(kernel, convert(Array{T}, collect(reward)))
    end
end

dom(v::ValuedKernel) = v.kernel.dom
codom(v::ValuedKernel) = v.kernel.codom
Base.:(==)(a::ValuedKernel, b::ValuedKernel) = a.kernel == b.kernel && a.reward == b.reward
Base.hash(v::ValuedKernel, h::UInt) = hash(v.reward, hash(v.kernel, hash(:ValuedKernel, h)))

"""
    isapprox(a::ValuedKernel, b::ValuedKernel; kwargs...)

Whether two valued kernels have the same spaces and approximately equal kernels and
reward tables.
"""
function Base.isapprox(a::ValuedKernel, b::ValuedKernel; kwargs...)
    return isapprox(a.kernel, b.kernel; kwargs...) && size(a.reward) == size(b.reward) &&
           isapprox(a.reward, b.reward; kwargs...)
end

function Base.show(io::IO, v::ValuedKernel)
    return print(io, "ValuedKernel(", axis_names(dom(v)), " → ", axis_names(codom(v)), ")")
end

_unchecked(v::ValuedKernel) = FiniteKernel(dom(v), codom(v), v.reward; check=false)

function compose(a::ValuedKernel, b::ValuedKernel)
    K = compose_kernel(a.kernel, b.kernel)
    W = compose_kernel(_unchecked(a), b.kernel).table +
        compose_kernel(a.kernel, _unchecked(b)).table
    return ValuedKernel(K, W)
end
function compose(a::ValuedKernel, b::ValuedKernel, c::ValuedKernel, cs::ValuedKernel...)
    return compose(compose(a, b), c, cs...)
end

function otimes(a::ValuedKernel, b::ValuedKernel)
    K = tensor_kernel(a.kernel, b.kernel)
    W = tensor_kernel(_unchecked(a), b.kernel).table +
        tensor_kernel(a.kernel, _unchecked(b)).table
    return ValuedKernel(K, W)
end
function otimes(a::ValuedKernel, b::ValuedKernel, c::ValuedKernel, cs::ValuedKernel...)
    return otimes(otimes(a, b), c, cs...)
end

"""
    reward_matrices(v::ValuedKernel) -> (K, W)

The kernel and the reward table as `length(codom) × length(dom)` matrices, rows and
columns in `joint_states` order.
"""
function reward_matrices(v::ValuedKernel)
    K = kernel_matrix(v.kernel)
    return K, reshape(v.reward, size(K))
end

function reward_kernel(v::ValuedKernel)
    K = FiniteKernel(dom(v), codom(v), Float64.(v.kernel.table))
    return RewardKernel(K, Float64.(v.reward))
end

function value_pullback(v::ValuedKernel, u::AbstractVector{<:Real})
    K, W = reward_matrices(v)
    return vec(sum(W; dims=1)) .+ transpose(K) * u
end

function _bound(p::DecisionPipeline, policies)
    policies === nothing && return p
    return bind_policy(p, (policies isa Pair ? (policies,) : pairs(policies))...)
end

"""
    evaluate(p::DecisionPipeline; policies=nothing) -> ValuedKernel

The meaning of a pipeline for fixed policies: the [`ValuedKernel`](@ref) `(K, W)`
from its inputs to its outputs, with `K(y | x)` the probability of the outputs given
the inputs and `W[y, x]` the expected utility collected, both obtained by summing
over every joint value of the wires (exact for rational tables). `policies` binds
open policy boxes for this evaluation (`:box => policy` pairs or a dictionary; see
[`bind_policy`](@ref)); an open box that is left unbound throws
[`UnboundBoxError`](@ref), and a belief that is not a single distribution throws
[`MonadMismatchError`](@ref).

This is a method of the `evaluate` of MarkovCategories and Catlab, and it is the
same kind of map: a structure-preserving interpretation of a diagram.
**Evaluation is compositional**,

    evaluate(compose(p, q)) == compose(evaluate(p), evaluate(q))
    evaluate(otimes(p, q))  == otimes(evaluate(p), evaluate(q))
    evaluate(identity_pipeline(X)) == the identity on X with zero reward,

so a submodel can be replaced without re-deriving the rest, and it agrees with
`interpret` of CategoricalInfluenceDiagrams on the same diagram
([`open_influence_diagram`](@ref)). Optimisation is **not** compositional in this
sense: the best policy of a part depends on what the rest of the diagram does with
its outputs, and the package offers no operation that optimises parts separately and
composes the results.
"""
function evaluate(p::DecisionPipeline; policies=nothing)
    q = _bound(p, policies)
    mass, reward = _accumulate(q, vcat(q.outputs, q.inputs), (), :evaluate)
    T = eltype(mass)
    K = FiniteKernel(dom(q), codom(q), mass; atol=_exact(T) ? 0 : 1e-8)
    return ValuedKernel(K, reward)
end

"""
    pipeline_value(p::DecisionPipeline; policies=nothing)

The expected utility of a pipeline with no input wires under fixed policies: the
total of the reward table of [`evaluate`](@ref evaluate(::DecisionPipeline)).
"""
function pipeline_value(p::DecisionPipeline; policies=nothing)
    isempty(p.inputs) ||
        throw(PipelineStructureError("the pipeline has input wires $(p.inputs); plug " *
                                     "values into them (`intervene`) or use `evaluate`"))
    return sum(evaluate(p; policies).reward)
end

# Into DecisionAnalysis
# ---------------------

function _open_policies(p::DecisionPipeline)
    return [s for s in _specs(p) if s.kind === :policy && s.table === nothing]
end
_belief_boxes(p::DecisionPipeline) = [s for s in _specs(p) if s.kind === :belief]

function _joint_labels(axes::Vector{FiniteAxis})
    length(axes) == 1 && return copy(only(axes).labels)
    X = FiniteSpace(axes)
    return [Symbol(join(s, "_")) for s in joint_states(X)]
end

# The pieces of the normal form of a pipeline with one decision: the action wire, the
# policy box (or `nothing` when the action is an input wire), the observed wires, the
# belief boxes and the boxes to leave out of the enumeration.
function _normal_form_parts(p::DecisionPipeline, action, operation::Symbol)
    open = _open_policies(p)
    length(open) <= 1 ||
        throw(PipelineStructureError("`$operation` reads a pipeline with one decision; " *
                                     "this one has $(length(open)) open policy boxes " *
                                     "($([s.name for s in open])). Bind all but one, or " *
                                     "use `strategy_program`"))
    beliefs = _belief_boxes(p)
    isempty(beliefs) &&
        throw(PipelineStructureError("`$operation` needs a belief box: the states of " *
                                     "the payoff table are the wires of the belief boxes"))
    if length(open) == 1
        policy = only(open)
        (action === nothing || Symbol(action) == policy.out) ||
            throw(PipelineStructureError("the open policy box sets `$(policy.out)`, not " *
                                         "`$action`"))
        isempty(p.inputs) ||
            throw(PipelineStructureError("`$operation`: the pipeline has input wires " *
                                         "$(p.inputs); plug values into them first"))
        return (; action=policy.out, policy, observed=policy.ins, beliefs,
                skip=vcat([b.name for b in beliefs], [policy.name]))
    end
    a = action === nothing ? (length(p.inputs) == 1 ? only(p.inputs) : nothing) :
        Symbol(action)
    (a !== nothing && p.inputs == [a]) ||
        throw(PipelineStructureError("`$operation` needs one decision: an open policy " *
                                     "box, or the action as the only input wire (inputs " *
                                     "are $(p.inputs))"))
    return (; action=a, policy=nothing, observed=Symbol[], beliefs,
            skip=[b.name for b in beliefs])
end

function _joint_belief(p::DecisionPipeline, beliefs)
    length(beliefs) == 1 && return only(beliefs).table
    vectors = map(beliefs) do s
        s.table isa Union{FiniteBelief,PointBelief} ||
            throw(MonadMismatchError(:decision_problem, DistributionMonad(),
                                     belief_monad(s.table),
                                     "with several belief boxes each must be a single " *
                                     "distribution (their joint is the product)"))
        return _factor(s, _axis(p, s.out), :decision_problem)
    end
    joint = reduce((a, b) -> vec(a .* permutedims(b)), vectors)
    return FiniteBelief(_joint_labels(FiniteAxis[_axis(p, s.out) for s in beliefs]), joint)
end

"""
    decision_problem(p::DecisionPipeline; action=nothing, baseline=nothing, feasible=nothing)
        -> DecisionProblem

The pipeline read as a payoff table and a belief: the interpreter into
DecisionAnalysis for a pipeline with **one decision**. The decision is the one open
policy box, or, when there is none, the action given as the only input wire of an
open model. The states are the wires of the belief boxes (their joint, labelled
`a_b`, when there are several, with the product belief), and

    Q[a, θ] = E[ Σ utilities | do(action = a), state = θ ],

computed by cutting the policy and belief boxes and summing over every other wire.
What the policy box observes plays no part here: it is read by
[`observation_experiment`](@ref). The belief is the belief box's own, whatever its
form, so a credal or scenario belief gives a problem for the robust rules.
`baseline` names the no-intervention action and `feasible` filters the actions, as
in `DecisionProblem`.
"""
function decision_problem(p::DecisionPipeline; action=nothing, baseline=nothing,
                          feasible=nothing)
    nf = _normal_form_parts(p, action, :decision_problem)
    state_wires = Symbol[b.out for b in nf.beliefs]
    mass, reward = _accumulate(p, vcat([nf.action], state_wires), nf.skip,
                               :decision_problem)
    all(isone, mass) ||
        throw(PipelineStructureError("the pipeline is not a normalised model given " *
                                     "the action and the states"))
    action_axis = _axis(p, nf.action)
    Q = reshape(reward, length(action_axis), :)
    states = _joint_labels(FiniteAxis[_axis(p, w) for w in state_wires])
    payoff = PayoffTable(action_axis.labels, states, Q)
    return DecisionProblem(payoff, _joint_belief(p, nf.beliefs); baseline, feasible)
end

"""
    observation_experiment(p::DecisionPipeline; action=nothing) -> Experiment

What the decision of a one-decision pipeline observes, as an experiment on the
states: `L[z, θ] = P(observations = z | state = θ)`, with the states those of
[`decision_problem`](@ref) and the signals the joint values of the wires that the
open policy box reads. A policy box that reads nothing gives the experiment with one
uninformative signal.

The pair `(decision_problem(p), observation_experiment(p))` is the normal form of
the pipeline, and it is a faithful summary only when the observation matters to the
payoff through the states alone. The function checks this (the expected utility
given action, state and observation must not depend on the observation) and throws
[`PipelineStructureError`](@ref) otherwise: the hidden wire that the observation
informs about should then be a belief box.
"""
function observation_experiment(p::DecisionPipeline; action=nothing)
    nf = _normal_form_parts(p, action, :observation_experiment)
    state_wires = Symbol[b.out for b in nf.beliefs]
    states = _joint_labels(FiniteAxis[_axis(p, w) for w in state_wires])
    if isempty(nf.observed)
        return Experiment(ones(Int, 1, length(states)); signals=[:nothing_observed], states)
    end
    keep = vcat(nf.observed, state_wires, [nf.action])
    mass, reward = _accumulate(p, keep, nf.skip, :observation_experiment)
    nz = prod(length(_axis(p, w)) for w in nf.observed)
    na = length(_axis(p, nf.action))
    M = reshape(mass, nz, length(states), na)
    R = reshape(reward, nz, length(states), na)
    L = M[:, :, 1]
    all(a -> M[:, :, a] == L, 1:na) ||
        throw(PipelineStructureError("the observation depends on the action that is " *
                                     "chosen after it"))
    for a in 1:na, θ in axes(L, 2)
        values = [R[z, θ, a] / L[z, θ] for z in 1:nz if !iszero(L[z, θ])]
        all(v -> isapprox(v, first(values); atol=_default_atol(eltype(values)) * 1000),
            values) ||
            throw(PipelineStructureError("the observation carries payoff-relevant " *
                                         "information beyond the states: make the " *
                                         "hidden wire it informs about a belief box"))
    end
    signals = _joint_labels(FiniteAxis[_axis(p, w) for w in nf.observed])
    return Experiment(L; signals, states)
end

decide(p::DecisionPipeline, rule; kw...) = decide(decision_problem(p), rule; kw...)
regret_table(p::DecisionPipeline) = regret_table(decision_problem(p))
act_now_value(p::DecisionPipeline) = act_now_value(decision_problem(p))
evpi(p::DecisionPipeline) = evpi(decision_problem(p))
evsi(p::DecisionPipeline) = evsi(decision_problem(p), observation_experiment(p))
evsi(p::DecisionPipeline, e::Experiment) = evsi(decision_problem(p), e)
function value_with_information(p::DecisionPipeline)
    return value_with_information(decision_problem(p), observation_experiment(p))
end
select(r::RuleSelection, p::DecisionPipeline; kw...) = select(r, decision_problem(p); kw...)

"""
    value_of_information(p::DecisionPipeline) -> NamedTuple

The value-of-information interpreter of a one-decision pipeline with a single prior:
`(act_now, informed, evsi, perfect, evpi)`, where `act_now` is the best expected
utility with no observation, `informed` the value of deciding on what the policy box
observes, `evsi = informed − act_now`, `perfect` the value with the state known and
`evpi = perfect − act_now`. All are DecisionAnalysis's quantities on
[`decision_problem`](@ref) and [`observation_experiment`](@ref), so
`0 ≤ evsi ≤ evpi`. `informed` is the optimum of the pipeline over its policies, the
number that `contextual_optimize` of CategoricalInfluenceDiagrams and the compiled
programme ([`policy_program`](@ref)) return.
"""
function value_of_information(p::DecisionPipeline)
    problem = decision_problem(p)
    v0 = act_now_value(problem)
    informed = value_with_information(problem, observation_experiment(p))
    perfect = v0 + evpi(problem)
    return (; act_now=v0, informed, evsi=informed - v0, perfect, evpi=perfect - v0)
end

# Provenance
# ----------

function _ancestors(specs::Vector{_BoxSpec}, targets::Vector{Symbol})
    producer = Dict(s.out => s for s in specs if s.out !== nothing)
    byname = Dict(s.name => s for s in specs)
    seen = Set{Symbol}()
    function visit(s::_BoxSpec)
        s.name in seen && return nothing
        push!(seen, s.name)
        for w in s.ins
            haskey(producer, w) && visit(producer[w])
        end
        return nothing
    end
    for t in targets
        haskey(byname, t) ? visit(byname[t]) :
        haskey(producer, t) ? visit(producer[t]) : nothing
    end
    return seen
end

"""
    box_provenance(p::DecisionPipeline, [target]) -> Vector{NamedTuple}

The provenance interpreter: the boxes that a number depends on. `target` is a box
name or a wire name, and the result lists that box (or the box producing that wire)
and every box upstream of it, in an order in which each box comes after the ones it
reads, each as `(name, kind, inputs, output, bound, error)`. Without `target` the
targets are the utility boxes, so the result is everything the expected utility
depends on: the boxes whose errors enter [`fidelity_bound`](@ref).
"""
function box_provenance(p::DecisionPipeline, target=nothing)
    specs = _specs(p)
    targets = target === nothing ? Symbol[s.name for s in specs if s.kind === :utility] :
              Symbol[Symbol(target)]
    if target !== nothing
        known = any(s -> s.name == targets[1], specs) ||
                any(a -> a.name == targets[1], _axes(p))
        known || throw(PipelineStructureError("the pipeline has no box or wire `$target`"))
    end
    seen = _ancestors(specs, targets)
    boxes = pipeline_boxes(p)
    return [boxes[i] for i in _topological(specs) if specs[i].name in seen]
end

# Conversion to CategoricalInfluenceDiagrams
# ------------------------------------------

"""
    open_influence_diagram(p::DecisionPipeline) -> NamedTuple

The pipeline as an open influence diagram of CategoricalInfluenceDiagrams:
`(diagram, kernels, utilities, strategy)`, where `diagram` is an
`OpenInfluenceDiagram` with one variable per wire, a mechanism per belief, channel
and consequence box, a decision per policy box (its information set the wires it
reads) and a utility per utility box; `kernels` and `utilities` are the dictionaries
of tables that `interpret` and `contextual_optimize` take (`Float64`); and
`strategy` holds the deterministic policies of the bound policy boxes.

The pipeline's inputs and outputs are the diagram's interfaces; an input wire that a
policy box reads is declared observed. A belief that is not a single distribution
throws [`MonadMismatchError`](@ref), and a bound policy that is not deterministic
throws `ArgumentError`. The test suite uses this conversion to hold
[`evaluate`](@ref evaluate(::DecisionPipeline)) to `interpret` and the optimum of a
pipeline to `contextual_optimize`.
"""
function open_influence_diagram(p::DecisionPipeline)
    axes = _axes(p)
    axis = Dict(a.name => a for a in axes)
    specs = _specs(p)
    mechanisms = Pair{Symbol,Any}[]
    decisions = Pair{Symbol,Any}[]
    utility_scopes = Pair{Symbol,Any}[]
    kernels = Dict{Symbol,FiniteKernel}()
    utilities = Dict{Symbol,IDs.AbstractUtility}()
    policies = Dict{Symbol,IDs.AbstractPolicy}()
    for s in specs
        ins = FiniteAxis[axis[w] for w in s.ins]
        if s.kind === :utility
            push!(utility_scopes, s.name => Tuple(s.ins))
            utilities[s.name] = IDs.TabularUtility(ins, Float64.(s.table))
        elseif s.kind === :policy
            push!(decisions, s.out => Tuple(s.ins))
            s.table === nothing && continue
            all(x -> iszero(x) || isone(x), s.table) ||
                throw(ArgumentError("the policy of box `$(s.name)` is not " *
                                    "deterministic; only deterministic policies are " *
                                    "converted"))
            labels = [axis[s.out].labels[findfirst(isone,
                                                   view(s.table, :, Tuple(ci)...))]
                      for ci in CartesianIndices(Tuple(length(a) for a in ins))]
            policies[s.out] = IDs.DeterministicPolicy(s.out, ins, axis[s.out], labels)
        else
            push!(mechanisms, s.out => Tuple(s.ins))
            table = Float64.(_factor(s, axis[s.out], :open_influence_diagram))
            shape = (length(axis[s.out]), (length(a) for a in ins)...)
            kernels[s.out] = FiniteKernel(FiniteSpace(ins), FiniteSpace(axis[s.out]),
                                          reshape(table, shape))
        end
    end
    id = IDs.influence_diagram((a.name => a.labels for a in axes)...; mechanisms,
                               decisions, utilities=utility_scopes, closed=false)
    read = Set(w for s in specs if s.kind === :policy for w in s.ins)
    diagram = Open(id; inputs=p.inputs, outputs=p.outputs,
                   observed=(; inputs=[w for w in p.inputs if w in read]))
    return (; diagram, kernels, utilities, strategy=IDs.Strategy(policies))
end
