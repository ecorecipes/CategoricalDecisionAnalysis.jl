/-
`lake exe check_certificate FILE.json`

Reads one JSON document, parses it with `Lean.Json.parse`, and dispatches on its `"schema"`:

* `"policy-certificate/1"`: `{"payoff", "prior", "likelihood", "policy", "dual", "value"}`, the
  payoff table (rows are actions, columns are states), the prior, the likelihood (rows are
  signals, columns are states), the policy `policy[a][z] = P(a | z)` (rows are actions,
  columns are signals), the dual vector (one entry per signal) and the claimed optimum of the
  one-decision programme; decided by `Certificate.checkPolicy`
  (`CategoricalDecisionAnalysisProofs/Certificate/Policy.lean`, theorem
  `RawPolicy.accepts_sound`: the value is `valueWithInformation` and the policy is optimal).
* `"fidelity-chain-certificate/1"`: `{"boxes", "range", "bound"}` with each box
  `{"exact", "approx", "error"}`, two square column-stochastic matrices `M[y][x] = P(y | x)`
  and a bound on the total variation between their columns; decided by
  `Certificate.checkFidelity` (`Certificate/Fidelity.lean`, theorem
  `RawFidelity.accepts_sound`: the decision loss is at most `bound = 2 · range · Σ error`).

Every number is a JSON string `"n/d"` or `"n"` (a JSON integer is also accepted). The exit
code is 0 exactly when the document is well formed and the proved checker accepts it; 1 when
it is rejected; 2 when the file cannot be read or decoded (wrong schema, missing field, a
number that is not a rational, a ragged or wrongly sized matrix).

The parse, the decoding into `Raw*` structures and the printing below are trusted, not proved.
The verdict is the value of the proved checker; the other lines are `decide`s of its
conjuncts. The schemas are proposals (`SCHEMAS-PROPOSED.md`): no Julia exporter writes them
yet.
-/
import CategoricalDecisionAnalysisProofs.Certificate.Policy
import CategoricalDecisionAnalysisProofs.Certificate.Fidelity
import Lean.Data.Json.Parser

open Lean DecisionAnalysisProofs DecisionAnalysisProofs.Certificate
  CategoricalDecisionAnalysisProofs CategoricalDecisionAnalysisProofs.Certificate

def verdict (b : Bool) : String := if b then "ok" else "FAIL"

/-- `"n/d"` or `"n"` as a rational. -/
def parseRat (s : String) : Except String ℚ :=
  match s.splitOn "/" with
  | [n] =>
    match n.toInt? with
    | some i => pure (i : ℚ)
    | none => throw s!"not a rational: {s.quote}"
  | [n, d] =>
    match n.toInt?, d.toNat? with
    | some i, some k =>
      if k = 0 then throw s!"zero denominator: {s.quote}" else pure ((i : ℚ) / (k : ℚ))
    | _, _ => throw s!"not a rational: {s.quote}"
  | _ => throw s!"not a rational: {s.quote}"

def ratOfJson : Json → Except String ℚ
  | .str s => parseRat s
  | .num n => if n.exponent = 0 then pure (n.mantissa : ℚ) else throw "numbers must be exact"
  | _ => throw "expected a rational as a string"

def ratList (j : Json) : Except String (List ℚ) := do
  let arr ← j.getArr?
  arr.toList.mapM ratOfJson

def ratMatrix (j : Json) : Except String (List (List ℚ)) := do
  let arr ← j.getArr?
  arr.toList.mapM ratList

def field (j : Json) (k : String) : Except String Json :=
  match j.getObjVal? k with
  | .ok v => pure v
  | .error _ => throw s!"missing field {k.quote}"

def requireRect (what : String) (rows : List (List ℚ)) (n m : ℕ) : Except String Unit :=
  if rect rows n m then pure () else throw s!"{what} is not a {n} by {m} matrix"

def decodePolicy (j : Json) : Except String RawPolicy := do
  let payoff ← ratMatrix (← field j "payoff")
  let prior ← ratList (← field j "prior")
  let likelihood ← ratMatrix (← field j "likelihood")
  let policy ← ratMatrix (← field j "policy")
  let dual ← ratList (← field j "dual")
  let value ← ratOfJson (← field j "value")
  requireRect "payoff" payoff payoff.length prior.length
  requireRect "likelihood" likelihood likelihood.length prior.length
  requireRect "policy" policy payoff.length likelihood.length
  if dual.length ≠ likelihood.length then
    throw s!"dual has {dual.length} entries for {likelihood.length} signals"
  pure { payoff, prior, likelihood, policy, dual, value }

def decodeBox (n : ℕ) (j : Json) : Except String RawBox := do
  let exact ← ratMatrix (← field j "exact")
  let approx ← ratMatrix (← field j "approx")
  let error ← ratOfJson (← field j "error")
  requireRect "exact" exact n n
  requireRect "approx" approx n n
  pure { exact, approx, error }

def decodeFidelity (j : Json) : Except String RawFidelity := do
  let arr ← (← field j "boxes").getArr?
  let first ← match arr.toList with
    | [] => throw "no boxes"
    | b :: _ => ratMatrix (← field b "exact")
  let n := first.length
  let boxes ← arr.toList.mapM (decodeBox n)
  let range ← ratOfJson (← field j "range")
  let bound ← ratOfJson (← field j "bound")
  pure { nStates := n, boxes, range, bound }

def runPolicy (j : Json) : IO UInt32 := do
  match decodePolicy j with
  | .error e => IO.eprintln s!"malformed policy certificate: {e}"; return 2
  | .ok r =>
    IO.println s!"schema: policy-certificate/1"
    IO.println s!"actions: {r.payoff.length}, states: {r.prior.length}, signals: {r.likelihood.length}"
    IO.println s!"policy column-stochastic: {verdict (decide (StochasticKernel r.π))}"
    IO.println s!"dual feasible: {verdict (decide (DualFeasible r.u r.p r.e r.v))}"
    IO.println s!"policy objective = value: {verdict (decide (policyValue r.u r.p r.e r.π = r.value))}"
    IO.println s!"dual objective = value: {verdict (decide (∑ z, r.v z = r.value))}"
    let ok := checkPolicy r
    IO.println s!"accepted: {if ok then "yes" else "no"}"
    if ok then
      IO.println "theorem Certificate.RawPolicy.accepts_sound: applies"
      return 0
    else
      return 1

def runFidelity (j : Json) : IO UInt32 := do
  match decodeFidelity j with
  | .error e => IO.eprintln s!"malformed fidelity certificate: {e}"; return 2
  | .ok r =>
    IO.println s!"schema: fidelity-chain-certificate/1"
    IO.println s!"states: {r.nStates}, boxes: {r.boxes.length}"
    let stochastic := decide (∀ t ∈ r.triples, StochasticKernel t.1 ∧ StochasticKernel t.2.1)
    IO.println s!"kernels column-stochastic: {verdict stochastic}"
    let errors := decide (∀ t ∈ r.triples, ∀ x, totalVariation (t.1 x) (t.2.1 x) ≤ t.2.2)
    IO.println s!"errors bound the total variation: {verdict errors}"
    IO.println s!"range nonnegative: {verdict (decide (0 ≤ r.range))}"
    let total := decide (r.bound = 2 * r.range * (r.triples.map fun t => t.2.2).sum)
    IO.println s!"bound = 2 * range * sum of errors: {verdict total}"
    let ok := checkFidelity r
    IO.println s!"accepted: {if ok then "yes" else "no"}"
    if ok then
      IO.println "theorem Certificate.RawFidelity.accepts_sound: applies"
      return 0
    else
      return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    match ← (IO.FS.readFile path).toBaseIO with
    | .error e => IO.eprintln s!"cannot read {path}: {e}"; return 2
    | .ok text =>
      match Json.parse text with
      | .error e => IO.eprintln s!"not JSON: {e}"; return 2
      | .ok j =>
        match (field j "schema").bind fun s => s.getStr? with
        | .ok "policy-certificate/1" => runPolicy j
        | .ok "fidelity-chain-certificate/1" => runFidelity j
        | .ok s => IO.eprintln s!"unknown schema {s.quote}"; return 2
        | .error e => IO.eprintln s!"malformed document: {e}"; return 2
  | _ =>
    IO.eprintln "usage: check_certificate FILE.json"
    return 2
