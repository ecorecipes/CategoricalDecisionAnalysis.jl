# Certificates

Two JSON documents that this package exports and that the Lean checker in `proofs/`
decides with proved checkers:

```sh
cd proofs && lake exe check_certificate FILE.json
```

The exit code is 0 when the checker accepts, 1 when it rejects and 2 when the document is
malformed. The schemas are a contract with the Lean development: a change of meaning needs
a new schema string. The conventions are those of the certificates of DecisionAnalysis:
every number is a JSON string `"n/d"` or `"n"` (a JSON integer is also accepted, a decimal
is not), and matrices are arrays of rows. Nothing is written unless the claim has first
been verified in Julia in exact arithmetic.

## `"policy-certificate/1"`

Written by [`export_policy_certificate`](@ref): the one-decision programme of a pipeline
`Belief ; Channel ; Policy ; Utility`, an optimal policy, and a dual vector that proves it
optimal.

| Field | Type | Meaning |
|:--|:--|:--|
| `schema` | string | `"policy-certificate/1"` |
| `payoff` | matrix, actions × states | `payoff[a][θ] = u(a, θ)`, feasible actions only |
| `prior` | vector, states | `prior[θ] = p(θ)` |
| `likelihood` | matrix, signals × states | `likelihood[z][θ] = P(z | θ)` |
| `policy` | matrix, actions × signals | `policy[a][z] = P(a | z)`; column-stochastic |
| `dual` | vector, signals | one dual value per signal |
| `value` | number | the claimed optimum |

The checker accepts when there is at least one action, the shapes agree, every entry of
`policy` is nonnegative and every column sums to one, `dual[z] ≥ Σ_θ prior[θ] ·
likelihood[z][θ] · payoff[a][θ]` for every signal and action, and both the policy's
objective and `Σ_z dual[z]` equal `value`. Then (theorem
`Certificate.RawPolicy.accepts_sound`) `value` is DecisionAnalysis's
`value_with_information(problem, experiment)` and no column-stochastic policy has a larger
objective. The dual is the column maxima of the objective coefficients
(`policy_certificate_sound`), so no solver is asked for duals.

## `"fidelity-chain-certificate/1"`

Written by [`export_fidelity_chain_certificate`](@ref): a chain of boxes on one finite
state space, each replaced by an approximation with a stated error, and the loss bound.

| Field | Type | Meaning |
|:--|:--|:--|
| `schema` | string | `"fidelity-chain-certificate/1"` |
| `boxes` | array, first box first | each `{ "exact", "approx", "error" }` |
| `boxes[i].exact` | matrix, n × n | `exact[y][x] = P(y | x)`; column-stochastic |
| `boxes[i].approx` | matrix, n × n | the approximation, same layout; column-stochastic |
| `boxes[i].error` | number | a bound on the total variation (half the ℓ¹ distance) between corresponding columns |
| `range` | number | `B`, at least the largest spread of one action's payoffs across states |
| `bound` | number | the claimed loss bound |

The checker accepts when every matrix is `n × n` and column-stochastic, every stated error
is at least the distance it bounds, `range ≥ 0` and `bound = 2 · range · Σ_i error_i`.
Then (theorem `Certificate.RawFidelity.accepts_sound`) for every payoff table on the `n`
states whose rows have range at most `range`, every prior on the input of the first box,
and every action that is Bayes for the belief pushed through the approximate chain, the
expected utility of that action under the belief pushed through the exact chain is within
`bound` of the best.

Not covered by this schema: boxes with different input and output types, tensors, and an
error on the prior. The theorems `decision_loss_comp_le`, `decision_loss_tensor_le` and
`decision_loss_chain_le` cover them; [`fidelity_bound`](@ref) computes the bound for a
general pipeline, with no certificate.

## Checking from Julia

`test/test_certificates.jl` exports both documents, compares them with the hand-written
fixtures of `proofs/certificate-fixtures/`, and, with
`CATEGORICALDECISIONANALYSIS_LEAN=1`, `lake` on the path and `proofs/` built, runs the
Lean checker on the exported files and on tampered copies, which must be refused.
