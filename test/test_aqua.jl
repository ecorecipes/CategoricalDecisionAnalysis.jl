using Aqua: Aqua

@testset "Aqua" begin
    # The org's packages are found through `[sources]`, and every transitive sibling has
    # to be listed in `[deps]` for that (none is registered), so those that the code does
    # not load directly are not stale.
    Aqua.test_all(CDA;
                  stale_deps=(;
                              ignore=[:ACSets, :BayesianNetworkFormats,
                                      :BayesianNetworkInference, :BayesianNetworks,
                                      :CategoricalBayesianNetworks,
                                      :StructuredPopulationCore]))
end
