# Vignettes

Seven vignettes, ordered from basic to advanced, that together cover the package. Each lives in its own
directory `NN_name/NN_name.qmd` and is rendered to GitHub-flavoured Markdown (`NN_name.md` plus any figures
in `NN_name_files/`), self-contained HTML (`NN_name.html`) and PDF (`NN_name.pdf`). All rendered files are
kept next to the `.qmd` and committed.

| | Vignette | Covers |
|---|---|---|
| 01 | [A decision as a diagram](01_first_pipeline/01_first_pipeline.md) | `belief_box`, `consequence_box`, `utility_box`, `policy_box`, `channel_box`, `decision_pipeline`, `decision_problem`, the forwarded `decide`, `evpi`, `act_now_value`, `value_of_information`, `solve_policy_program`, `pipeline_value`, `intervene`, `box_provenance`. Written for a reader who knows no category theory |
| 02 | [Five rules from one pipeline](02_five_rules_one_pipeline/02_five_rules_one_pipeline.md) | the monads and `belief_monad`, `FiniteDistribution`, `FiniteSubset`, the algebras, `rule_selection`, `select`, `rule_scores`, `replace_box` with a `CredalSet`, `has_monad_morphism`, `MonadMismatchError`, `algebra_multiplication_defect`, `is_algebra`, `interchange_gap`, `regret_coarsening`, `coarsening_is_lossless` |
| 03 | [Chains of observation](03_observation_chains/03_observation_chains.md) | `compose` of channel boxes, `evaluate`, `reward_matrices`, `with_observation`, `observation_experiment`, `is_garbling`, `information_value`, `observation_can_matter`, `bayesian_inverse`, `posterior`, `inverse_compose`, `posterior_distribution`, `posterior_mean`, `value_gap_bound`, `refines`, `partition_experiment` |
| 04 | [Replacing a submodel by an emulator](04_emulators_and_fidelity/04_emulators_and_fidelity.md) | `compose` of pipelines and of `ValuedKernel`s, `kernel_distance`, `replace_box`, `with_error`, `utility_range`, `total_error`, `fidelity_bound`, `finite_kernel`, `export_fidelity_chain_certificate` |
| 05 | [Selection functions and backward induction](05_selection_functions_and_backward_induction/05_selection_functions_and_backward_induction.md) | `argmax_selection`, `argmin_selection`, `constant_selection`, `quantifier`, `selection_product`, `SequentialProblem`, `backward_induction`, `policy_search`, `policy_value`, `nested_value`, `backward_induction_class`, `admits_backward_induction`, `BackwardInductionError`, `optimal_plays` |
| 06 | [Compiling a diagram to an optimisation programme](06_compiling_to_a_programme/06_compiling_to_a_programme.md) | `policy_program`, `solve_program` by the exact simplex, CDDLib and HiGHS, `solve_policy_program`, `expectation_constraint`, `chance_constraint`, `strategy_program`, `open_strategy_program`, `compose` of programmes, `solve_strategy_program`, `export_policy_certificate` |
| 07 | [Bd epizootic response as a pipeline](07_bd_epizootic_response_as_a_pipeline/07_bd_epizootic_response_as_a_pipeline.md) | The cached Drawert et al. (2017) table of `Chytridiomycosis.jl` through `conditional_problem`, the pipeline reproducing the core's numbers, a survey as a chain, a handling limit as a constraint, the fidelity bound for an error in the weights |

## Conventions of the examples

- **Utility is counted in individuals**: the number of animals (or flowering spikes) of the focal species.
  No example here has a published valuation in money, so none uses money, and no cost is invented.
- **Every vignette has a no-intervention action** and reports gains over it.
- **Examples are ecological and every number is labelled illustrative.** In vignette 07 the numbers read
  from the cached table of runs are labelled *from the cached table*; the model is that of Drawert et al.
  (2017), the runs are not the authors', and nothing is presented as a published result.
- Problems are stated with rational numbers where practical, so results are exact.

## Rendering

```sh
julia scripts/render_vignettes.jl           # every vignette
julia scripts/render_vignettes.jl 03 06     # only those whose name starts so
julia scripts/render_vignettes.jl --no-execute   # redo HTML and PDF from the Markdown on disk
julia scripts/sync_vignettes.jl             # copy the Markdown into docs/src/tutorials
```

The code runs once: Quarto executes it for GitHub-flavoured Markdown only, and pandoc (the one bundled
with Quarto) makes the HTML and the PDF from that Markdown, so the three formats show the same numbers.
Quarto and a TeX distribution with `lualatex` are needed (`quarto install tinytex`). The environment is
`vignettes/Project.toml`; it finds this package, `DecisionAnalysis.jl`, `FiniteKernels.jl` and
`Chytridiomycosis.jl` by path in sibling directories. Do not add `html` or `pdf` to `_quarto.yml` or to a
vignette's front matter: Quarto would run the code once per format.
