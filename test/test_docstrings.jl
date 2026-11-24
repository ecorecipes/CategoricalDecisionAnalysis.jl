# Every exported name this package owns has a docstring; the core is re-exported whole;
# and no new export shadows a name of Catlab, of the core or of the packages under them
# with another meaning.

using Catlab: Catlab
using DecisionAnalysis: DecisionAnalysis
using ACSets: ACSets
using MarkovCategories: MarkovCategories
using InfluenceDiagrams: InfluenceDiagrams
using CategoricalBayesianNetworks: CategoricalBayesianNetworks

function owned_undocumented(M)
    return filter(n -> Base.which(M, n) === M, Base.Docs.undocumented_names(M))
end

# Every name exported by a module or by any module nested in it.
function all_exports(M::Module, seen=Set{Module}())
    M in seen && return Set{Symbol}()
    push!(seen, M)
    found = Set{Symbol}(names(M))
    for n in names(M; all=true)
        isdefined(M, n) || continue
        v = getfield(M, n)
        v isa Module && v !== M && parentmodule(v) === M &&
            union!(found, all_exports(v, seen))
    end
    return found
end

@testset "exports" begin
    exported = Set(names(CDA))

    @testset "docstrings on every exported name" begin
        @test isempty(owned_undocumented(CDA))
    end

    @testset "the core is re-exported, with its own bindings" begin
        for name in names(DecisionAnalysis)
            name === :DecisionAnalysis && continue
            @test name in exported
            @test getfield(CDA, name) === getfield(DecisionAnalysis, name)
        end
    end

    owned = Set(n
                for n in exported
                if n !== :CategoricalDecisionAnalysis &&
                   Base.which(CDA, n) === CDA)

    @testset "no export shadows a name of Catlab, the core or the stack below" begin
        # The Catlab generics this package gives methods to are Catlab's own bindings.
        for name in (:compose, :otimes, :dom, :codom)
            @test getfield(CDA, name) === getfield(Catlab.Theories, name)
        end
        @test CDA.evaluate === MarkovCategories.evaluate
        @test MarkovCategories.evaluate === Catlab.evaluate
        others = union(all_exports(Catlab), all_exports(ACSets),
                       all_exports(MarkovCategories),
                       Set(names(DecisionAnalysis)), Set(names(FiniteKernels)),
                       Set(names(CategoricalInfluenceDiagrams)),
                       Set(names(InfluenceDiagrams)),
                       Set(names(CategoricalBayesianNetworks)), Set(names(JuMP)))
        clashes = intersect(owned, others)
        @test isempty(clashes)
        # nor a name that Base exports
        @test isempty(filter(n -> Base.isexported(Base, n), owned))
    end

    @testset "names that must never be exported" begin
        @test !(:regrets in exported) && !(:regret in exported)
        for name in (:id, :mcopy, :delete, :braid, :munit)
            @test !(name in owned)
        end
    end
end
