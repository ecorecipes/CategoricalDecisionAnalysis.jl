# Expected outcomes of `check_certificate` on the fixtures

Run from `proofs/`: `make check-fixtures` (or `lake exe check_certificate FILE.json`).
The exit code is 0 when the proved checker accepts, 1 when it rejects, 2 when the file cannot
be decoded. The prefix of the file name fixes the expected code, and
`scripts/check_fixtures.sh` enforces it.

All fixtures are **written by hand**. The schemas are documented in `../../docs/src/certificates.md`;
the package writes them with `export_policy_certificate` and `export_fidelity_chain_certificate`,
and its Lean-gated test checks that exported files are accepted.

## `policy-certificate/1`

Two actions that pay `1` when they match the state, prior `(3/5, 2/5)`, a two-signal
experiment; the objective coefficients are `12/25, 1/10` after the first signal and
`3/25, 3/10` after the second, so the optimum is `39/50`.

| File | Content | Expected |
|:--|:--|:--|
| `policy_two_signals.json` | the deterministic optimal policy, dual `(12/25, 3/10)` | accepted (exit 0) |
| `policy_randomised_tie.json` | three actions, two of them identical; a randomised optimal policy | accepted (exit 0) |
| `reject_policy_suboptimal.json` | a feasible policy worth `59/100`, claimed `39/50` | rejected (exit 1) |
| `reject_policy_wrong_value.json` | `value` is `4/5` | rejected (exit 1) |
| `reject_policy_dual_infeasible.json` | dual `(9/25, 21/50)` sums to `39/50` but `9/25 < 12/25` | rejected (exit 1) |
| `reject_policy_not_stochastic.json` | a policy column sums to two | rejected (exit 1) |
| `malformed_policy_ragged.json` | second policy row has one entry | malformed (exit 2) |
| `malformed_policy_decimal.json` | `value` is `"0.78"` | malformed (exit 2) |

## `fidelity-chain-certificate/1`

Two boxes on two states, each with total-variation error `1/10`; range `10`; bound
`2 · 10 · (1/10 + 1/10) = 4`.

| File | Content | Expected |
|:--|:--|:--|
| `fidelity_two_boxes.json` | as described | accepted (exit 0) |
| `reject_fidelity_error_understated.json` | first error claimed `1/20`, bound `3` | rejected (exit 1) |
| `reject_fidelity_wrong_bound.json` | bound `3` | rejected (exit 1) |
| `reject_fidelity_not_stochastic.json` | a column of an approximate kernel sums to `11/10` | rejected (exit 1) |
| `reject_fidelity_negative_range.json` | range `-10`, bound `-4` | rejected (exit 1) |
| `malformed_fidelity_not_square.json` | an approximate kernel is `2 × 3` | malformed (exit 2) |
