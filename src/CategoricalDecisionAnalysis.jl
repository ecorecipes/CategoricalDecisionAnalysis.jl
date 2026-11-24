"""
    CategoricalDecisionAnalysis

The applied-category-theory layer over DecisionAnalysis.jl: the structure of a
decision analysis made explicit enough to compose and to check. It re-exports every
name of DecisionAnalysis and gives the same numbers; what it adds is structure.

  - **Uncertainty monads and their algebras** (`src/monads.jl`): no uncertainty,
    finite distributions, non-empty sets of possibilities and credal sets
    ([`IdentityMonad`](@ref), [`DistributionMonad`](@ref), [`PowersetMonad`](@ref),
    [`CredalMonad`](@ref)), the structure maps that summarise an uncertain number
    ([`StructureMap`](@ref): expectation, worst case, lower expectation, ...), which
    of them are Eilenberg-Moore algebras ([`is_algebra`](@ref)), and the monad
    morphisms between the monads ([`monad_morphism`](@ref)).
  - **Effects and value pullback** (`src/effects.jl`): [`value_pullback`](@ref),
    implemented once for every monad and algebra, and the
    [`interchange_gap`](@ref) whose instances are the values of information.
  - **Conditionals** (`src/conditionals.jl`): [`bayesian_inverse`](@ref), through
    sub-stochastic kernels and normalisation, so that evidence of probability zero
    is a value and not an exception.
  - **Selection functions** (`src/selection.jl`): [`SelectionFunction`](@ref),
    [`selection_product`](@ref), every rule of DecisionAnalysis as a selection
    function ([`rule_selection`](@ref)), and finite sequential problems solved by
    [`backward_induction`](@ref), which refuses criteria that do not admit it, and by
    [`policy_search`](@ref).
  - **Information preorders** (`src/information.jl`): experiments under garbling
    and partitions under refinement ([`is_garbling`](@ref), [`refines`](@ref)), value
    as a monotone map ([`information_value`](@ref)), and the regret transform under
    coarsening ([`regret_coarsening`](@ref)).
  - **Decision pipelines** (`src/pipelines.jl`): [`DecisionPipeline`](@ref), typed
    diagrams of Belief, Channel, Policy, Consequence and Utility boxes whose shape is
    an ACSet, composed with Catlab's `compose` and `otimes`, and their interpreters
    into DecisionAnalysis ([`evaluate`](@ref evaluate(::DecisionPipeline)),
    [`decision_problem`](@ref), [`value_of_information`](@ref),
    [`box_provenance`](@ref)).
  - **Compositional fidelity** (`src/fidelity.jl`): [`kernel_distance`](@ref) and
    the decision-loss bound read off a diagram, [`fidelity_bound`](@ref).
  - **Diagrams compiled to programmes** (`src/compile.jl`):
    [`policy_program`](@ref) (a linear programme for one decision) and
    [`strategy_program`](@ref) (a mixed-integer programme for several), as JuMP
    models, with budget and chance constraints.
  - **A structural value-of-information test** (`src/structural.jl`):
    [`observation_can_matter`](@ref), from the graph alone.
  - **Certificates** (`src/certificates.jl`): [`export_policy_certificate`](@ref)
    and [`export_fidelity_chain_certificate`](@ref), JSON documents that the Lean
    checker in `proofs/` decides.
  - **Kernel bridges** (`src/bridges.jl`): [`finite_kernel`](@ref).

What the package does not claim: optimisation does not compose in general (only
evaluation does, and compiled programmes); credal kernels compose in sequence only
and have no string diagrams here; and the constructions are known ones, cited where
they are documented.
"""
module CategoricalDecisionAnalysis

using Catlab: @present, @acset_type, FreeSchema, add_part!, nparts, parts, subpart,
              incident
using DecisionAnalysis
using FiniteKernels: FiniteKernels, FiniteAxis, FiniteKernel, FiniteSpace, axis_names,
                     compose_kernel, factors, joint_states, kernel_matrix, tensor_kernel
using MarkovCategories: MarkovCategories
using CategoricalInfluenceDiagrams: CategoricalInfluenceDiagrams, Open, RewardKernel,
                                    kernel, reward_matrix
using InfluenceDiagrams: InfluenceDiagrams
using JuMP: JuMP
using ResilienceCore: ResilienceCore

const IDs = InfluenceDiagrams

import Catlab.Theories: compose, otimes, dom, codom
import MarkovCategories: evaluate
import DecisionAnalysis: decide, regret_table, act_now_value, evpi, evsi,
                         value_with_information

# Every exported name of DecisionAnalysis is re-exported (ADR 0009), so that
# `using CategoricalDecisionAnalysis` is a superset of `using DecisionAnalysis`.
for name in setdiff(names(DecisionAnalysis), [nameof(DecisionAnalysis)])
    @eval export $name
end

# The Catlab generics this package gives methods to.
export compose, otimes, dom, codom, evaluate
# errors.jl
export CategoricalDecisionAnalysisError, MonadMismatchError, BackwardInductionError,
       PipelineStructureError, WireMismatchError, UnboundBoxError, CompilationError
# monads.jl
export UncertaintyMonad, IdentityMonad, DistributionMonad, PowersetMonad, CredalMonad,
       RewardMonad, FiniteDistribution, FiniteSubset, CredalHull, probability_of,
       monad_unit, monad_bind, monad_map, monad_join, in_hull, same_hull,
       prune_generators, StructureMap, IdentityAlgebra, ExpectationAlgebra,
       InfimumAlgebra, SupremumAlgebra, LowerExpectationAlgebra, UpperExpectationAlgebra,
       TotalRewardAlgebra, TransportedAlgebra, HurwiczMap, LaplaceMap, CVaRMap,
       QuantileMap, AlphaMaxminMap, RestrictedMap, monad_of, is_algebra, is_monotone,
       is_translation_equivariant, admits_backward_induction, algebra_unit_defect,
       algebra_multiplication_defect, MonadMorphism, monad_morphism, has_monad_morphism,
       restrict_algebra, structure_map, belief_monad, belief_value, KleisliMap,
       kleisli_identity, kleisli_compose, change_monad, kleisli_map, stochastic_matrix
# effects.jl
export default_algebra, value_pullback, reward_kernel, interchange_gap,
       expectation_rewrite
# conditionals.jl
export normalize_mass, BayesianInverse, bayesian_inverse, posterior, inverse_compose
# selection.jl
export SelectionFunction, select, quantifier, argmax_selection, argmin_selection,
       constant_selection, selection_product, RuleSelection, rule_selection, rule_scores,
       pareto_selection, backward_induction_class, nested_value, DecisionStage, ChanceStage,
       SequentialProblem,
       SequentialSolution, policy_law, policy_value, policy_search, backward_induction,
       optimal_plays
# information.jl
export is_garbling, refines, partition_experiment, information_value,
       posterior_distribution, posterior_mean, value_at_posteriors, posterior_payoff,
       information_distance, value_gap_bound, RegretCoarsening, regret_coarsening,
       coarsening_is_lossless
# pipelines.jl
export PipelineGraph, BOX_KINDS, DecisionPipeline, pipeline_graph, pipeline_boxes,
       pipeline_wires, belief_box, channel_box, consequence_box, policy_box, utility_box,
       decision_pipeline, identity_pipeline, rename_wires, rename_boxes, bind_policy,
       replace_box,
       with_error, box_errors, intervene, ValuedKernel, reward_matrices, pipeline_value,
       decision_problem, observation_experiment, value_of_information, box_provenance,
       open_influence_diagram
# fidelity.jl
export jensen_shannon_distance, kernel_distance, utility_range, total_error,
       fidelity_bound
# compile.jl
export ExpectationConstraint, expectation_constraint, chance_constraint, policy_program,
       PolicySolution, solve_policy_program, StrategyProgram, strategy_program,
       open_strategy_program, StrategySolution, solve_strategy_program
# structural.jl
export with_observation, observation_can_matter
# certificates.jl
export POLICY_CERTIFICATE_SCHEMA, FIDELITY_CHAIN_CERTIFICATE_SCHEMA,
       export_policy_certificate, export_fidelity_chain_certificate
# bridges.jl
export finite_kernel

include("errors.jl")
include("monads.jl")
include("effects.jl")
include("conditionals.jl")
include("selection.jl")
include("information.jl")
include("pipelines.jl")
include("fidelity.jl")
include("compile.jl")
include("structural.jl")
include("certificates.jl")
include("bridges.jl")

end # module
