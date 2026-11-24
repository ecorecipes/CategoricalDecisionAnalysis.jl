# The exception hierarchy (ADR 0013).

@testset "errors" begin
    types = (MonadMismatchError, BackwardInductionError, PipelineStructureError,
             WireMismatchError, UnboundBoxError, CompilationError)
    for T in types
        @test T <: CategoricalDecisionAnalysisError <: Exception
        @test !(T <: DecisionAnalysisError)
    end
    @test isabstracttype(CategoricalDecisionAnalysisError)
    # every concrete error of the package is under the root, and is listed above
    defined = [getfield(CDA, n)
               for n in names(CDA; all=true)
               if isdefined(CDA, n) && getfield(CDA, n) isa DataType &&
                  getfield(CDA, n) <: Exception && parentmodule(getfield(CDA, n)) === CDA]
    @test Set(filter(!isabstracttype, defined)) == Set(types)
    messages = [MonadMismatchError(:op, DistributionMonad(), CredalMonad(), "no morphism"),
                BackwardInductionError(:CVaR, "it is not an algebra"),
                PipelineStructureError("a cycle"),
                WireMismatchError(:compose, :state, [:a], [:b]),
                WireMismatchError(:compose, nothing, 1, 2),
                UnboundBoxError(:m, :policy, :evaluate),
                CompilationError("too large")]
    for e in messages
        text = sprint(showerror, e)
        @test startswith(text, string(nameof(typeof(e))))
        @test !occursin("#undef", text)
    end
    @test occursin("policy_search", sprint(showerror, messages[2]))
    @test occursin("wire `state`", sprint(showerror, messages[4]))
    @test occursin("the interfaces", sprint(showerror, messages[5]))
    # the package never calls a bare error()
    for file in readdir(joinpath(dirname(@__DIR__), "src"); join=true)
        code = join(filter(l -> !startswith(lstrip(l), "#"), readlines(file)), "\n")
        @test !occursin(r"(?<![a-z_])error\(\"", code)
    end
end
