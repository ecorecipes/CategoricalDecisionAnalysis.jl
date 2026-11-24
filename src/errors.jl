# Exceptions of CategoricalDecisionAnalysis (ADR 0013). Every exception the package
# defines lives in this file, with its `showerror` method, and subtypes the root
# `CategoricalDecisionAnalysisError`.
#
# - Library code never calls a bare `error("...")`.
# - Invalid arguments and keywords raise `ArgumentError`, not a type from this file.
# - A typed error from DecisionAnalysis, FiniteKernels or CategoricalInfluenceDiagrams
#   passes through unchanged.

"""
    CategoricalDecisionAnalysisError

Abstract supertype of every exception that CategoricalDecisionAnalysis defines:
[`MonadMismatchError`](@ref), [`BackwardInductionError`](@ref),
[`PipelineStructureError`](@ref), [`WireMismatchError`](@ref),
[`UnboundBoxError`](@ref) and [`CompilationError`](@ref). It marks the package that
introduced an error, not a kind of failure. Invalid arguments and keywords raise
Base's `ArgumentError` instead, and the errors of DecisionAnalysis (under
`DecisionAnalysisError`) and of FiniteKernels pass through unchanged.
"""
abstract type CategoricalDecisionAnalysisError <: Exception end

"""
    MonadMismatchError(operation, expected, got, msg)

Thrown when two pieces that must live in the same uncertainty monad do not, and no
monad morphism connects them: composing Kleisli maps of two monads, applying a
structure map to a value of another monad, or pairing a belief with an aggregator
that cannot read it (a credal set with the expectation algebra, say: there is no
monad morphism from the credal monad to the distribution monad). Fields: `operation`
(a `Symbol`), `expected` and `got` (the monads) and `msg`.
"""
struct MonadMismatchError <: CategoricalDecisionAnalysisError
    operation::Symbol
    expected::Any
    got::Any
    msg::String
end

function Base.showerror(io::IO, e::MonadMismatchError)
    return print(io, "MonadMismatchError: `", e.operation, "` expected ", e.expected,
                 " and got ", e.got, ": ", e.msg)
end

"""
    BackwardInductionError(criterion, reason)

Thrown by [`backward_induction`](@ref) when solving stage by stage would not give a
best policy for the criterion applied to the whole problem, and the caller did not
ask for what it does give. `criterion` is its name and `reason` says why. For a
criterion that is monotone but not an Eilenberg-Moore algebra (conditional value at
risk, say) backward induction solves the nested rule, a different rule: pass
`nested = true` to get that, labelled. For minimax regret pass `heuristic = true`
to get the stage-by-stage answer, labelled as a heuristic.
[`policy_search`](@ref) is exact for every criterion.
"""
struct BackwardInductionError <: CategoricalDecisionAnalysisError
    criterion::Symbol
    reason::String
end

function Base.showerror(io::IO, e::BackwardInductionError)
    return print(io, "BackwardInductionError: `", e.criterion,
                 "` does not admit backward induction: ", e.reason,
                 ". Use `policy_search` for the exact optimum of the criterion applied " *
                 "to the whole problem.")
end

"""
    PipelineStructureError(msg)

Thrown when a [`DecisionPipeline`](@ref) is not well formed: a wire produced by two
boxes, a box reading a wire that does not exist, a cycle, a utility box with an output
wire, or an interpreter asked for something the diagram's shape does not provide (a
payoff table from a pipeline with two policy boxes, say).
"""
struct PipelineStructureError <: CategoricalDecisionAnalysisError
    msg::String
end

function Base.showerror(io::IO, e::PipelineStructureError)
    return print(io, "PipelineStructureError: ", e.msg)
end

"""
    WireMismatchError(operation, wire, expected, got)

Thrown when two pipelines are joined along wires that do not match: a different
name, or the same name with different labels. Fields: `operation` (`:compose` or
`:otimes`), `wire` (the wire name, or `nothing` when the lists of names differ) and
the two things that should have been equal.
"""
struct WireMismatchError <: CategoricalDecisionAnalysisError
    operation::Symbol
    wire::Union{Nothing,Symbol}
    expected::Any
    got::Any
end

function Base.showerror(io::IO, e::WireMismatchError)
    what = e.wire === nothing ? "the interfaces" : "wire `$(e.wire)`"
    return print(io, "WireMismatchError: `", e.operation, "` cannot join ", what,
                 ": expected ", e.expected, ", got ", e.got)
end

"""
    UnboundBoxError(box, kind, operation)

Thrown when an interpreter needs the table of a box that has none: evaluating a
pipeline whose policy box is still open (no policy was given), or reading a payoff
table from a pipeline with an unbound channel. Fields: the box name, its kind and the
operation that needed it.
"""
struct UnboundBoxError <: CategoricalDecisionAnalysisError
    box::Symbol
    kind::Symbol
    operation::Symbol
end

function Base.showerror(io::IO, e::UnboundBoxError)
    return print(io, "UnboundBoxError: `", e.operation, "` needs a table for the ",
                 e.kind, " box `", e.box, "`, which has none")
end

"""
    CompilationError(msg)

Thrown by the diagram-to-programme compiler ([`policy_program`](@ref),
[`strategy_program`](@ref), [`solve_strategy_program`](@ref)) when a pipeline cannot
be compiled as asked: more than one policy box for the linear programme, a constraint
over a wire the pipeline does not have, or a strategy programme too large to
enumerate without an optimiser.
"""
struct CompilationError <: CategoricalDecisionAnalysisError
    msg::String
end

function Base.showerror(io::IO, e::CompilationError)
    return print(io, "CompilationError: ", e.msg)
end
