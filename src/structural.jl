# A structural value-of-information criterion on diagrams (revision "new 11" of the
# plan; after van Merwijk, Carey and Everitt 2022, in its single-decision form): decide
# from the graph alone whether observing a wire can have positive value, before
# computing anything.

"""
    with_observation(p::DecisionPipeline, box, wires...) -> DecisionPipeline

The same pipeline with the policy box `box` reading the given wires as well: the
decision is then made knowing them. A bound policy is opened again, since its table
no longer has the right shape. A wire that is downstream of the decision would make
a cycle and throws [`PipelineStructureError`](@ref). Comparing the optimum with and
without the extra wire ([`solve_policy_program`](@ref)) is the value of observing
it.
"""
function with_observation(p::DecisionPipeline, box, wires...)
    extra = Symbol[_wire_name(w) for w in wires]
    return _replace_spec(p, Symbol(box),
                         function (s)
                             s.kind === :policy ||
                                 throw(PipelineStructureError("box `$(s.name)` is a " *
                                                              "$(s.kind) box, not a " *
                                                              "policy box"))
                             return _BoxSpec(s.name, s.kind, unique(vcat(s.ins, extra)),
                                             s.out,
                                             nothing, s.error)
                         end)
end

# d-separation of the node sets `xs` and `ys` given `zs` in the graph with the given
# parent lists, by the moralised ancestral graph.
function _d_separated(parents::Dict{Symbol,Vector{Symbol}}, xs, ys, zs)
    relevant = Set{Symbol}()
    stack = collect(Symbol, union(xs, ys, zs))
    while !isempty(stack)
        n = pop!(stack)
        n in relevant && continue
        push!(relevant, n)
        append!(stack, get(parents, n, Symbol[]))
    end
    neighbours = Dict(n => Set{Symbol}() for n in relevant)
    link(a, b) = (push!(neighbours[a], b); push!(neighbours[b], a))
    for n in relevant
        ps = get(parents, n, Symbol[])
        foreach(q -> link(n, q), ps)
        for a in ps, b in ps
            a == b || link(a, b)
        end
    end
    blocked = Set(zs)
    seen = Set{Symbol}()
    stack = [x for x in xs if !(x in blocked)]
    while !isempty(stack)
        n = pop!(stack)
        n in seen && continue
        push!(seen, n)
        n in ys && return false
        append!(stack, [m for m in neighbours[n] if !(m in blocked)])
    end
    return true
end

"""
    observation_can_matter(p::DecisionPipeline, wire; box=nothing) -> Bool

A structural test, from the shape of the diagram alone: whether letting the open
policy box of a one-decision pipeline observe `wire` **can** change the best expected
utility, for some choice of the tables. It is `false` when the wire is downstream of
the decision (it is not available when deciding), when the policy already reads it,
or when the wire is d-separated from every utility downstream of the decision given
what the policy already reads and its action (van Merwijk, Carey and Everitt 2022,
single-decision case; Lauritzen and Nilsson's requisite information).

`false` is a guarantee: whatever the tables, observing the wire is worth exactly
nothing, and no value of information needs computing (a structural zero, as opposed
to a numerical one). `true` is a possibility, not a promise: particular tables can
still make the value zero. The test suite checks the guarantee on random tables by
computing the value with [`with_observation`](@ref). `box` names the policy box when
the pipeline has several open ones.
"""
function observation_can_matter(p::DecisionPipeline, wire; box=nothing)
    w = _wire_name(wire)
    _wire_index(p, w)
    open = _open_policies(p)
    policy = if box === nothing
        length(open) == 1 ||
            throw(PipelineStructureError("`observation_can_matter` needs one open policy " *
                                         "box, or `box` to name one; the pipeline has " *
                                         "$(length(open))"))
        only(open)
    else
        _spec(p, Symbol(box))
    end
    policy.kind === :policy ||
        throw(PipelineStructureError("box `$(policy.name)` is not a policy box"))
    w in policy.ins && return false
    specs = _specs(p)
    parents = Dict{Symbol,Vector{Symbol}}()
    for s in specs
        node = s.kind === :utility ? Symbol("utility:", s.name) : s.out
        parents[node] = copy(s.ins)
    end
    # descendants of the action
    children = Dict{Symbol,Vector{Symbol}}()
    for (n, ps) in parents, q in ps
        push!(get!(children, q, Symbol[]), n)
    end
    downstream = Set{Symbol}()
    stack = [policy.out]
    while !isempty(stack)
        n = pop!(stack)
        n in downstream && continue
        push!(downstream, n)
        append!(stack, get(children, n, Symbol[]))
    end
    w in downstream && return false
    utilities = [Symbol("utility:", s.name)
                 for s in specs
                 if s.kind === :utility && Symbol("utility:", s.name) in downstream]
    isempty(utilities) && return false
    return !_d_separated(parents, [w], utilities, vcat(policy.ins, [policy.out]))
end
