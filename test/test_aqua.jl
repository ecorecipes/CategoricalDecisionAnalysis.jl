using Aqua: Aqua

@testset "Aqua" begin
    # The org's packages are found through `[sources]`, and every transitive sibling has
    # to be listed in `[deps]` for that (none is registered), so those that the code does
    # not load directly are not stale.
    # On Windows the Graphviz binary that Catlab's Graphviz extension runs while
    # precompiling cannot write its configuration file, so the subprocess that Aqua starts
    # for the persistent-task check fails before it measures anything.
    Aqua.test_all(CDA; persistent_tasks=!Sys.iswindows(),
                  stale_deps=(;
                              ignore=[:ACSets, :BayesianNetworkFormats,
                                      :BayesianNetworkInference, :BayesianNetworks,
                                      :CategoricalBayesianNetworks,
                                      :StructuredPopulationCore]))
end
