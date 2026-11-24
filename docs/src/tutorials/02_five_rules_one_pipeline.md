# Five rules from one pipeline
Simon Frost

- [Motivation](#motivation)
- [Kinds of uncertainty](#kinds-of-uncertainty)
- [Five rules by swapping two boxes](#five-rules-by-swapping-two-boxes)
- [A sixth rule needs a different belief
  box](#a-sixth-rule-needs-a-different-belief-box)
  - [Beliefs and rules must match](#beliefs-and-rules-must-match)
- [Which summaries can be taken in
  stages](#which-summaries-can-be-taken-in-stages)
- [The value of information is a gap between two orders of doing
  things](#the-value-of-information-is-a-gap-between-two-orders-of-doing-things)
- [Regret when states are merged](#regret-when-states-are-merged)
- [Summary](#summary)

## Motivation

Maximising the expected count is one way to choose. A cautious manager
looks at the worst case, a manager who fears hindsight looks at regret,
and a manager who does not trust a single probability works with a set
of them. In a spreadsheet each of these is a different calculation. Here
they are one calculation with two parts swapped:

- the **algebra box**: how an uncertain count is summarised as one
  number;
- the **selection box**: how an action is picked from the summaries.

The diagram of the problem, built in the [first
vignette](01_first_pipeline.md), is not touched.

**All numbers are illustrative**; counts are of water voles, and every
result is compared with no intervention.

``` julia
using CategoricalDecisionAnalysis
include(joinpath("..", "_common.jl"))

mink = :mink_pressure => [:low, :high]
action = :action => [:no_intervention, :trap_mink, :restore_banks]
colony = :colony => [:lost, :reduced, :thriving]
model = zeros(Rational{Int}, 3, 3, 2)
model[:, 1, 1] = [1 // 10, 3 // 10, 6 // 10]
model[:, 1, 2] = [7 // 10, 2 // 10, 1 // 10]
model[:, 2, 1] = [1 // 10, 2 // 10, 7 // 10]
model[:, 2, 2] = [2 // 10, 4 // 10, 4 // 10]
model[:, 3, 1] = [0 // 10, 2 // 10, 8 // 10]
model[:, 3, 2] = [5 // 10, 3 // 10, 2 // 10]
reach = decision_pipeline(belief_box(:what_we_believe, mink, [3 // 5, 2 // 5]),
                          policy_box(:manager, (), action),
                          consequence_box(:colony_model, (action, mink), colony, model),
                          utility_box(:voles_next_spring, colony, [0, 40, 120]))
problem = decision_problem(reach; baseline=:no_intervention)
problem.payoff
```

**PayoffTable{Rational{Int64}}: 3 actions × 2 states**

| action            | `low` | `high` |
|:------------------|------:|-------:|
| `no_intervention` |    84 |     20 |
| `trap_mink`       |    92 |     64 |
| `restore_banks`   |   104 |     36 |

## Kinds of uncertainty

The belief box above holds a probability for each state. That is one
kind of uncertain value. The package has four, and calls each a *monad*,
which here means no more than “a kind of uncertain value, with a rule
for chaining two uncertain steps”.

| kind | an uncertain state is | in the package |
|:---|:---|:---|
| none | one state | `IdentityMonad`, a `PointBelief` |
| probabilities | a distribution over states | `DistributionMonad`, a `FiniteBelief` |
| possibilities | a set of states that could hold | `PowersetMonad`, a `ScenarioSet` |
| candidate probabilities | a set of distributions | `CredalMonad`, a `CredalSet` |

``` julia
belief_monad(problem.belief)
```

    DistributionMonad()

Each kind has its own ways of turning an uncertain count into one
number. The package calls such a map a *structure map*.

``` julia
uncertain_count = FiniteDistribution([84, 20], [3 // 5, 2 // 5])   # no intervention
possible_counts = FiniteSubset([84, 20])
(expectation=ExpectationAlgebra()(uncertain_count), worst=InfimumAlgebra()(possible_counts),
 best=SupremumAlgebra()(possible_counts))
```

    (expectation = 292//5, worst = 20, best = 84)

## Five rules by swapping two boxes

`rule_selection` assembles a rule from its two boxes. The first rule is
the expected count, maximised.

``` julia
expected = rule_selection(; algebra=ExpectationAlgebra(), name=:expected_count)
select(expected, reach)
```

    1-element Vector{Symbol}:
     :trap_mink

The others change the algebra box, the selection box, or both. The
diagram `reach` is the same object throughout.

``` julia
rules = ["expected count" => rule_selection(; algebra=ExpectationAlgebra()),
         "worst case (maximin)" => rule_selection(; algebra=InfimumAlgebra()),
         "best case (maximax)" => rule_selection(; algebra=SupremumAlgebra()),
         "minimax regret" => rule_selection(; algebra=InfimumAlgebra(), transform=:regret),
         "good enough: at least 75 voles expected" =>
             rule_selection(; algebra=ExpectationAlgebra(), selector=(:threshold, 75))]
actions = feasible_actions(problem)
md_table(vcat("rule", String.(actions), "chosen"),
         [vcat(name, rule_scores(rule, problem), [select(rule, reach)])
          for (name, rule) in rules])
```

| rule | no_intervention | trap_mink | restore_banks | chosen |
|:---|---:|---:|---:|---:|
| expected count | 58.4 | 80.8 | 76.8 | `trap_mink` |
| worst case (maximin) | 20 | 64 | 36 | `trap_mink` |
| best case (maximax) | 84 | 92 | 104 | `restore_banks` |
| minimax regret | 44 | 12 | 28 | `trap_mink` |
| good enough: at least 75 voles expected | 58.4 | 80.8 | 76.8 | `trap_mink`, `restore_banks` |

The scores of minimax regret are losses (lower is better); the others
are counts. With the regret transform the worst case is read on the side
of losses: the worst case of a regret is the largest regret.

Each row is the corresponding rule of `DecisionAnalysis`, and gives the
same answer:

``` julia
core = [MaxExpectedUtility(), Maximin(), Maximax(), MinimaxRegret(), Satisfice(75)]
all(select(rule, reach) == decide(problem, c).chosen for ((_, rule), c) in zip(rules, core))
```

    true

In every row the comparison with doing nothing is the same table of
gains; the rules differ in how they read it.

``` julia
gain_over_baseline(problem)
```

**PayoffTable{Rational{Int64}}: 3 actions × 2 states**

| action            | `low` | `high` |
|:------------------|------:|-------:|
| `no_intervention` |     0 |      0 |
| `trap_mink`       |     8 |     44 |
| `restore_banks`   |    20 |     16 |

## A sixth rule needs a different belief box

The fifth kind of rule works with a set of candidate probabilities. That
is a change to the belief box, and the diagram says so: `replace_box`
swaps the belief.

``` julia
candidates = CredalSet([:low, :high], [[3 // 5, 2 // 5], [4 // 5, 1 // 5], [3 // 10, 7 // 10]])
ambiguous = replace_box(reach, :what_we_believe, candidates)
cautious = rule_selection(; algebra=LowerExpectationAlgebra(), name=:gamma_maximin)
(chosen=select(cautious, ambiguous), lower_expected_counts=rule_scores(cautious, decision_problem(ambiguous)),
 same_as_core=select(cautious, ambiguous) == decide(ambiguous, GammaMaximin()).chosen)
```

    (chosen = [:trap_mink], lower_expected_counts = Rational{Int64}[196//5, 362//5, 282//5], same_as_core = true)

``` julia
expected_gain_over_baseline(decision_problem(ambiguous; baseline=:no_intervention))
```

    (lower = Rational{Int64}[0, 76//5, 86//5], upper = Rational{Int64}[0, 166//5, 96//5])

Under a set of candidate probabilities the gain over no intervention is
a range, one pair of numbers for each action.

### Beliefs and rules must match

A rule reads the belief in its own kind of uncertainty. Where the belief
is of another kind, there has to be a way of carrying one to the other.
Some exist:

``` julia
[(from=nameof(typeof(a)), to=nameof(typeof(b)), exists=has_monad_morphism(a, b))
 for (a, b) in ((DistributionMonad(), CredalMonad()), (PowersetMonad(), CredalMonad()),
                (DistributionMonad(), PowersetMonad()), (CredalMonad(), DistributionMonad()),
                (PowersetMonad(), DistributionMonad()))]
```

    5-element Vector{@NamedTuple{from::Symbol, to::Symbol, exists::Bool}}:
     (from = :DistributionMonad, to = :CredalMonad, exists = 1)
     (from = :PowersetMonad, to = :CredalMonad, exists = 1)
     (from = :DistributionMonad, to = :PowersetMonad, exists = 1)
     (from = :CredalMonad, to = :DistributionMonad, exists = 0)
     (from = :PowersetMonad, to = :DistributionMonad, exists = 0)

A single distribution is a set with one member; a set of possible states
is every distribution on them. Nothing turns a set back into one
distribution, so the expected count of an ambiguous belief is refused
and not guessed:

``` julia
try
    select(expected, ambiguous)
catch err
    sprint(showerror, err)
end
```

    "MonadMismatchError: `belief_value` expected CategoricalDecisionAnalysis.CredalMonad() and got CategoricalDecisionAnalysis.DistributionMonad(): there is no monad morphism from the belief's monad to the one asked for"

## Which summaries can be taken in stages

Some summaries give the same number whether an uncertain count is
summarised in one go or in two stages (first within each branch, then
across branches). The expectation does: the mean of the means is the
mean. So do the worst and the best case. Others do not. The package
records which, because it decides whether a rule can be used in a
problem with several stages ([a later
vignette](05_selection_functions_and_backward_induction.md)).

``` julia
branch1 = FiniteDistribution([0, 10], [1 // 2, 1 // 2])
branch2 = FiniteDistribution([4], [1])
two_stage = FiniteDistribution([branch1, branch2], [1 // 2, 1 // 2])
md_table(["summary", "in one go minus in two stages", "the same in stages"],
         [[String(nameof(typeof(s))), algebra_multiplication_defect(s, two_stage), is_algebra(s)]
          for s in (ExpectationAlgebra(), CVaRMap(1 // 2), QuantileMap(1 // 2))])
```

| summary            | in one go minus in two stages | the same in stages |
|:-------------------|------------------------------:|-------------------:|
| ExpectationAlgebra |                             0 |                yes |
| CVaRMap            |                             2 |                 \- |
| QuantileMap        |                             4 |                 \- |

`CVaRMap(1 // 2)` is the mean of the worse half of the outcomes. Taken
in two stages it gives a different number, which is why it cannot be
optimised stage by stage.

## The value of information is a gap between two orders of doing things

“Take the best action in each state, then average” and “average, then
take the best action” differ, and the first is never smaller. The
difference is the expected value of perfect information.

``` julia
(interchange_gap=interchange_gap(problem), evpi=evpi(problem))
```

    (interchange_gap = 36//5, evpi = 36//5)

The same gap with the worst case in place of the average is the
difference between choosing after and before nature moves:

``` julia
scenario = replace_box(reach, :what_we_believe, ScenarioSet([:low, :high]))
interchange_gap(decision_problem(scenario))
```

    0//1

## Regret when states are merged

Regret compares each action with the best action for the state. If two
states are merged (the manager will never tell them apart), the regret
of the merged problem is smaller than the merged regret, by the same
amount for every action. The amount is the value of perfect information
that the merging gives up.

``` julia
three = DecisionProblem(PayoffTable([:no_intervention, :trap_mink, :restore_banks],
                                    [:low, :medium, :high], [84 50 20; 92 80 64; 104 70 36]),
                        [1 // 2, 1 // 4, 1 // 4]; baseline=:no_intervention)
merged = regret_coarsening(three, [:low, :not_low, :not_low])
md_table(["cell", "probability", "gap (voles)"],
         [[String(c), merged.mass[i], merged.gap[i]] for (i, c) in enumerate(merged.cells)])
```

| cell    | probability | gap (voles) |
|:--------|------------:|------------:|
| low     |         0.5 |           0 |
| not_low |         0.5 |           0 |

``` julia
(sum_of_gaps=sum(merged.gap), evpi_minus_evppi=evpi(three) - evppi(three, [:low, :not_low, :not_low]),
 nothing_lost=coarsening_is_lossless(three, [:low, :not_low, :not_low]))
```

    (sum_of_gaps = 0//1, evpi_minus_evppi = 0//1, nothing_lost = true)

The gap is zero in a cell exactly when one action is best at every state
of the cell; then merging its states loses nothing for this decision.

## Summary

One diagram, six rules. Each rule is a pair (algebra box, selection
box), and a rule that needs another kind of belief says so. The package
reproduces the rules of `DecisionAnalysis` and does not add new ones;
what it adds is that the rule is a piece of data that can be swapped,
inspected and classified.
