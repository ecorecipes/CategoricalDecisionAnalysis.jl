using Documenter
using CategoricalDecisionAnalysis

DocMeta.setdocmeta!(CategoricalDecisionAnalysis, :DocTestSetup,
                    :(using CategoricalDecisionAnalysis); recursive=true)

# Tutorials are rendered quarto vignettes copied into docs/src/tutorials by
# scripts/sync_vignettes.jl. The page list is built from the files on disk so
# it never has to be maintained by hand.
function tutorial_pages()
    dir = joinpath(@__DIR__, "src", "tutorials")
    isdir(dir) || return Pair{String,String}[]
    files = sort(filter(f -> endswith(f, ".md"), readdir(dir)))
    map(files) do f
        title = f
        for line in eachline(joinpath(dir, f))
            m = match(r"^#\s+(.*)", line)
            if m !== nothing
                title = String(strip(m.captures[1]))
                break
            end
        end
        return title => "tutorials/" * f
    end
end

pages = Any["Home" => "index.md", "Scope and prior art" => "scope.md",
            "Theorem map" => "theorems.md", "Certificates" => "certificates.md",
            "API Reference" => ["Uncertainty monads and algebras" => "api/monads.md",
                                "Value pullback and conditionals" => "api/effects.md",
                                "Selection functions and sequential problems" => "api/selection.md",
                                "Information" => "api/information.md",
                                "Decision pipelines" => "api/pipelines.md",
                                "Programmes, fidelity, certificates and exceptions" => "api/programmes.md"]]
tutorials = tutorial_pages()
isempty(tutorials) || push!(pages, "Tutorials" => tutorials)

# Source links need a commit to point at. A checkout without commits (a fresh
# scaffold, a tarball) builds without them instead of failing.
has_commit = success(pipeline(`git -C $(@__DIR__) rev-parse HEAD`; stderr=devnull,
                              stdout=devnull))
remote_kw = has_commit ?
            (; repo=Remotes.GitHub("ecorecipes", "CategoricalDecisionAnalysis.jl")) :
            (; remotes=nothing)

# Strict: no `warnonly`, so a docstring left out of the manual, a broken `@ref` or a
# failing doctest fails the build.
makedocs(;
         remote_kw...,
         modules=[CategoricalDecisionAnalysis],
         sitename="CategoricalDecisionAnalysis.jl",
         authors="Simon Frost",
         format=Documenter.HTML(;
                                prettyurls=get(ENV, "CI", "false") == "true",
                                canonical="https://ecorecipes.github.io/CategoricalDecisionAnalysis.jl",
                                repolink="https://github.com/ecorecipes/CategoricalDecisionAnalysis.jl",
                                edit_link="main"),
         pages=pages)

"--no-deploy" in ARGS ||
    deploydocs(; repo="github.com/ecorecipes/CategoricalDecisionAnalysis.jl.git",
               devbranch="main")
