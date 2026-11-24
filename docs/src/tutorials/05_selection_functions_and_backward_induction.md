# Selection functions and backward induction
Simon Frost

- [Motivation](#motivation)
- [Selection functions](#selection-functions)
  - [The product: one stage after
    another](#the-product-one-stage-after-another)
- [A two-season problem](#a-two-season-problem)
  - [The expected count](#the-expected-count)
  - [The worst case](#the-worst-case)
- [Which rules can be solved
  backwards](#which-rules-can-be-solved-backwards)
  - [Conditional value at risk](#conditional-value-at-risk)
  - [Minimax regret](#minimax-regret)
- [Every best plan, for problems without
  chance](#every-best-plan-for-problems-without-chance)
- [Summary](#summary)

## Motivation

Most management is done in stages: act, see what happens, act again. The
textbook way to solve such a problem is to work backwards from the last
stage. That works for the expected count and for the worst case. It does
**not** work for every rule, and when it fails it fails silently: the
recursion returns a policy and a number, and both are wrong for the
question that was asked.

This vignette introduces the object that makes the difference visible,
the selection function, solves a two-season problem with it, and then
shows the package refusing to work backwards for conditional value at
risk and for minimax regret, with the two examples that justify the
refusal.

**All numbers are illustrative.** Counts are of flowering spikes of a
fen orchid, and every result is compared with no intervention.

``` julia
using CategoricalDecisionAnalysis
include(joinpath("..", "_common.jl"))
```

    Main.Notebook.voi_table

## Selection functions

A decision rule answers one question: given what each option is worth,
which option? An object that answers it is a *selection function*. The
plainest is “an option where the worth is largest”.

``` julia
options = [:no_intervention, :mow, :graze]
worth = Dict(:no_intervention => 40, :mow => 65, :graze => 65)
best = argmax_selection(options)
(chosen=select(best, a -> worth[a]), its_worth=quantifier(best, a -> worth[a]))
```

    (chosen = :mow, its_worth = 65)

Ties go to the first option in the list; nothing is random. The
set-valued variant returns every best option:

``` julia
select(argmax_selection(options; monad=PowersetMonad(), ties=:all), a -> worth[a])
```

    FiniteSubset(mow, graze)

Nature is a selection function too, one that does not look at the
worths. Given a distribution over seasons it “selects” the distribution,
and the worth of that is the expectation.

``` julia
season = FiniteDistribution([:dry_summer, :wet_summer], [2 // 5, 3 // 5])
nature = constant_selection([:dry_summer, :wet_summer], season)
spikes = Dict(:dry_summer => 20, :wet_summer => 90)
quantifier(nature, s -> spikes[s])
```

    62//1

### The product: one stage after another

Two selection functions in sequence combine into one on pairs. For each
first move the second stage selects; the first move is then valued by
what the second stage achieves; and the first stage selects against
those values. That is backward induction, as an operation on rules.

The first example is a familiar rule. “Choose the action whose worst
outcome is best” is the product of “pick the best action” with “pick the
worst state”:

``` julia
actions = [:no_intervention, :mow, :graze]
states = [:dry_summer, :wet_summer]
table = PayoffTable(actions, states, [20 90; 45 70; 35 85])
maximin = selection_product(argmax_selection(actions), argmin_selection(states))
cell(pair) = table.Q[findfirst(==(pair[1]), actions), findfirst(==(pair[2]), states)]
(play=select(maximin, cell), value=quantifier(maximin, cell),
 core=decide(DecisionProblem(table, ScenarioSet(states)), Maximin()).chosen)
```

    (play = (:mow, :dry_summer), value = 45, core = [:mow])

## A two-season problem

A fen meadow holds a population of fen orchid. In each of two years the
manager can leave the meadow or mow it in late summer. Mowing costs some
spikes in the year it is done and helps in the next. Between the years
the summer is dry or wet.

``` julia
function spikes_after(history)
    first_action, summer1, second_action, summer2 = history
    n = 60
    n += first_action === :mow ? -10 : 0
    n += summer1 === :wet_summer ? 20 : -25
    n += first_action === :mow ? 30 : 0                 # last year's mowing pays off
    n += second_action === :mow ? -10 : 0
    n += summer2 === :wet_summer ? 20 : -25
    n += (second_action === :mow && summer1 === :dry_summer) ? 35 : 0   # mowing helps most after drought
    n += second_action === :mow ? 5 : 0
    return max(n, 0)
end
meadow = SequentialProblem([DecisionStage(:first_year, [:no_intervention, :mow]),
                            ChanceStage(:first_summer, [:dry_summer, :wet_summer], season),
                            DecisionStage(:second_year, [:no_intervention, :mow]),
                            ChanceStage(:second_summer, [:dry_summer, :wet_summer], season)],
                           spikes_after)
```

    SequentialProblem(DistributionMonad, decide first_year → chance first_summer → decide second_year → chance second_summer)

Every earlier move is known at every stage, so the second decision can
depend on the first summer. A policy says what to do at each point where
there is a choice.

### The expected count

``` julia
by_stages = backward_induction(meadow, MaxExpectedUtility())
by_search = policy_search(meadow, MaxExpectedUtility())
(backward_induction=by_stages.value, every_policy_examined=by_search.value,
 policies=by_search.policies, label=by_stages.label)
```

    (backward_induction = 96//1, every_policy_examined = 96//1, policies = 32, label = :optimal)

Working backwards and examining every policy agree, as they must for the
expectation.

``` julia
describe(policy) = [(after=isempty(h) ? "the start" : join(String.(h), ", "), do_this=policy[h])
                    for h in sort(collect(keys(policy)); by=length)]
describe(by_stages.policy)
```

    5-element Vector{@NamedTuple{after::String, do_this::Symbol}}:
     (after = "the start", do_this = :mow)
     (after = "no_intervention, wet_summer", do_this = :no_intervention)
     (after = "no_intervention, dry_summer", do_this = :mow)
     (after = "mow, wet_summer", do_this = :no_intervention)
     (after = "mow, dry_summer", do_this = :mow)

Against never intervening:

``` julia
never = Dict{Tuple,Symbol}(h => :no_intervention for h in keys(by_stages.policy))
baseline = policy_value(meadow, never, Expectation())
(no_intervention=baseline, best_policy=by_stages.value, gain=by_stages.value - baseline)
```

    (no_intervention = 64//1, best_policy = 96//1, gain = 32//1)

### The worst case

With the summers given as a set of possibilities and no probabilities,
the same function works backwards for the worst case.

``` julia
either = FiniteSubset([:dry_summer, :wet_summer])
meadow_sets = SequentialProblem(PowersetMonad(),
                                [DecisionStage(:first_year, [:no_intervention, :mow]),
                                 ChanceStage(:first_summer, [:dry_summer, :wet_summer], either),
                                 DecisionStage(:second_year, [:no_intervention, :mow]),
                                 ChanceStage(:second_summer, [:dry_summer, :wet_summer], either)],
                                spikes_after)
cautious = backward_induction(meadow_sets, Maximin())
(backward_induction=cautious.value, every_policy_examined=policy_search(meadow_sets, Maximin()).value,
 no_intervention=policy_value(meadow_sets, never, WorstCase()))
```

    (backward_induction = 60, every_policy_examined = 60, no_intervention = 10)

## Which rules can be solved backwards

Working backwards replaces “summarise the whole uncertain future” by
“summarise the next step, then the step before”. That is the same thing
only for summaries that give the same answer in stages as in one go.

``` julia
rules = ["expected count" => MaxExpectedUtility(), "worst case" => Maximin(), "best case" => Maximax(),
         "lower expectation over a set of priors" => GammaMaximin(),
         "CVaR, worst quarter" => DecisionRule(CVaR(1 // 4)),
         "median" => DecisionRule(Quantile(1 // 2)), "Hurwicz" => DecisionRule(Hurwicz(1 // 2)),
         "minimax regret" => MinimaxRegret()]
md_table(["rule", "class", "solved backwards by default"],
         [[name, String(backward_induction_class(r)), admits_backward_induction(r)]
          for (name, r) in rules])
```

| rule                                   |  class | solved backwards by default |
|:---------------------------------------|-------:|----------------------------:|
| expected count                         |   flat |                         yes |
| worst case                             |   flat |                         yes |
| best case                              |   flat |                         yes |
| lower expectation over a set of priors |   flat |                         yes |
| CVaR, worst quarter                    | nested |                          \- |
| median                                 | nested |                          \- |
| Hurwicz                                | nested |                          \- |
| minimax regret                         |   none |                          \- |

- `flat`: working backwards gives the best policy for the rule.
- `nested`: working backwards gives the best policy for a **different
  rule**, the one that applies the summary at every stage. It is a
  legitimate rule; it is not the one named.
- `none`: no stage-by-stage form is offered.

### Conditional value at risk

CVaR at level 3/4 is the mean of the worst three quarters of the
outcomes. Take a problem small enough to check by hand. The first summer
adds no spikes or ten, with equal chances. Then the manager chooses
between a safe action that adds one spike and a risky one that adds none
or four, with equal chances.

``` julia
coin1 = FiniteDistribution([:poor, :good], [1 // 2, 1 // 2])
coin2 = FiniteDistribution([:fails, :works], [1 // 2, 1 // 2])
first_gain = Dict(:poor => 0, :good => 10)
second_gain(a, c) = a === :safe ? 1 : (c === :works ? 4 : 0)
small = SequentialProblem([ChanceStage(:first_summer, [:poor, :good], coin1),
                           DecisionStage(:act, [:safe, :risky]),
                           ChanceStage(:second_summer, [:fails, :works], coin2)],
                          h -> first_gain[h[1]] + second_gain(h[2], h[3]))
rule = DecisionRule(CVaR(3 // 4))
try
    backward_induction(small, rule)
catch err
    sprint(showerror, err)
end
```

    "BackwardInductionError: `CVaR` does not admit backward induction: it is not an Eilenberg-Moore algebra of the problem's monad, so applying it stage by stage is a different rule (the nested one) from applying it to the whole problem; pass `nested = true` to solve the nested rule. Use `policy_search` for the exact optimum of the criterion applied to the whole problem."

The package refuses. Asked explicitly for the stage-by-stage answer, it
gives it with a label:

``` julia
staged = backward_induction(small, rule; nested=true)
searched = policy_search(small, rule)
md_table(["", "after a poor summer", "after a good summer", "CVaR of the outcome", "label"],
         [["working backwards", staged.policy[(:poor,)], staged.policy[(:good,)], staged.value,
           String(staged.label)],
          ["every policy examined", searched.policy[(:poor,)], searched.policy[(:good,)], searched.value,
           String(searched.label)]])
```

|  | after a poor summer | after a good summer | CVaR of the outcome | label |
|:---|---:|---:|---:|---:|
| working backwards | `risky` | `risky` | 4.67 | nested |
| every policy examined | `risky` | `safe` | 5 | optimal |

Looked at from the second stage alone, the risky action has the better
CVaR whatever the first summer was, so the recursion always takes it.
But the worst three quarters of the *whole* distribution contain all of
the poor-summer branch and only the worse half of the good-summer
branch, where the safe action is better. The recursion cannot see that,
because what counts as the bad tail is decided by the other branch.

The stage-by-stage policy is the best one for the nested rule, which is
why the label is `nested` and not `wrong`:

``` julia
(nested_value_of_the_staged_policy=nested_value(small, staged.policy, rule),
 nested_value_of_the_other_policy=nested_value(small, searched.policy, rule))
```

    (nested_value_of_the_staged_policy = 14//3, nested_value_of_the_other_policy = 41//9)

### Minimax regret

Regret compares each plan with the best plan for the state that occurs.
The stage-by- stage version compares each continuation with the best
*continuation*, which is a different menu.

A manager can stop a restoration scheme after the first year or go on,
and if going on choose between two designs. The spikes under two
possible futures:

``` julia
plans = PayoffTable([:stop, :design_b, :design_c], [:future_1, :future_2], [0 9; 10 0; 6 3])
```

**PayoffTable{Int64}: 3 actions × 2 states**

| action     | `future_1` | `future_2` |
|:-----------|-----------:|-----------:|
| `stop`     |          0 |          9 |
| `design_b` |         10 |          0 |
| `design_c` |          6 |          3 |

``` julia
design = Dict(:design_b => (10, 0), :design_c => (6, 3))
payoff(h) = h[1] === :stop ? (h[3] === :future_1 ? 0 : 9) : design[h[2]][h[3] === :future_1 ? 1 : 2]
scheme = SequentialProblem(PowersetMonad(),
                           [DecisionStage(:first, [:stop, :go_on]),
                            DecisionStage(:second, [:design_b, :design_c]),
                            ChanceStage(:future, [:future_1, :future_2],
                                        FiniteSubset([:future_1, :future_2]))], payoff)
try
    backward_induction(scheme, MinimaxRegret())
catch err
    sprint(showerror, err)
end
```

    "BackwardInductionError: `MinimaxRegret` does not admit backward induction: regret is measured against the best action of a menu, and the menu of a subproblem is not the menu of the whole problem. Use `policy_search` for the exact optimum of the criterion applied to the whole problem."

``` julia
staged = backward_induction(scheme, MinimaxRegret(); heuristic=true)
searched = policy_search(scheme, MinimaxRegret())
md_table(["", "first", "if going on", "largest regret", "label"],
         [["working backwards", staged.policy[()], staged.policy[(:go_on,)], staged.value,
           String(staged.label)],
          ["every policy examined", searched.policy[()], searched.policy[(:go_on,)], searched.value,
           String(searched.label)]])
```

|                       |   first | if going on | largest regret |     label |
|:----------------------|--------:|------------:|---------------:|----------:|
| working backwards     | `go_on` |  `design_b` |              9 | heuristic |
| every policy examined | `go_on` |  `design_c` |              6 |   optimal |

At the second stage, with stopping no longer on the menu, design b has
the smaller regret. With stopping on the menu, design b’s regret in the
second future is measured against the nine spikes that stopping would
have kept, and design c is better. The table of all three plans gives
the same answer as examining every policy:

``` julia
whole_menu = decide(DecisionProblem(plans, ScenarioSet([:future_1, :future_2])), MinimaxRegret())
(chosen=whole_menu.chosen, largest_regrets=whole_menu.scores)
```

    (chosen = [:design_c], largest_regrets = [10, 9, 6])

Both small examples are theorems of the Lean development that
accompanies the package (`cvar_backward_induction_suboptimal` and
`minimaxRegret_backward_induction_suboptimal`).

## Every best plan, for problems without chance

For a problem with decisions only, the product of set-valued selection
functions returns every best plan.

``` julia
yield(h) = Dict((:mow, :mow) => 70, (:mow, :graze) => 85, (:graze, :mow) => 85, (:graze, :graze) => 60,
                (:no_intervention, :mow) => 55, (:no_intervention, :graze) => 50,
                (:mow, :no_intervention) => 60, (:graze, :no_intervention) => 45,
                (:no_intervention, :no_intervention) => 40)[h]
rotation = SequentialProblem([DecisionStage(:year_1, [:no_intervention, :mow, :graze]),
                              DecisionStage(:year_2, [:no_intervention, :mow, :graze])], yield)
(best_plans=optimal_plays(rotation), gain_over_no_intervention=85 - 40)
```

    (best_plans = FiniteSubset((:mow, :graze), (:graze, :mow)), gain_over_no_intervention = 45)

This is offered for problems without chance stages only. With chance in
the product the set it returns is too small, and for several
decision-makers set-valued products are known to be wrong.

## Summary

- A rule is a selection function; stages combine by the product; the
  product is backward induction.
- The product gives the best policy when the summary is the same in
  stages as in one go: expectation, worst case, best case, lower
  expectation.
- For CVaR, quantiles and Hurwicz it solves a different (nested) rule,
  and the package says so. For minimax regret it is a heuristic,
  labelled as one.
- `policy_search` is exact for every rule, at the cost of examining
  every policy.
