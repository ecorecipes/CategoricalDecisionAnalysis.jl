using Test
using CategoricalDecisionAnalysis
using Random: Xoshiro
using FiniteKernels: FiniteKernels, FiniteAxis, FiniteKernel, FiniteSpace, compose_kernel,
                     kernel_matrix, random_kernel, tensor_kernel
using CategoricalInfluenceDiagrams: CategoricalInfluenceDiagrams, RewardKernel,
                                    contextual_optimize, continuation_value, interpret
using JuMP: JuMP
using CDDLib: CDDLib
using HiGHS: HiGHS

const CDA = CategoricalDecisionAnalysis
const CID = CategoricalInfluenceDiagrams

include("helpers.jl")

@testset "CategoricalDecisionAnalysis" begin
    include("test_monads.jl")
    include("test_effects.jl")
    include("test_conditionals.jl")
    include("test_selection.jl")
    include("test_sequential.jl")
    include("test_information.jl")
    include("test_pipelines.jl")
    include("test_fidelity.jl")
    include("test_compile.jl")
    include("test_structural.jl")
    include("test_bridges.jl")
    include("test_validation.jl")
    include("test_certificates.jl")
    include("test_errors.jl")
    include("test_docstrings.jl")
    include("test_aqua.jl")
end
