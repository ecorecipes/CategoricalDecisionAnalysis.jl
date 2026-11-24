# A decision as a diagram
Simon Frost

- [Motivation](#motivation)
- [The problem](#the-problem)
- [Wires](#wires)
- [Boxes](#boxes)
- [The diagram](#the-diagram)
- [Reading the payoff table off the
  diagram](#reading-the-payoff-table-off-the-diagram)
- [Adding an observation](#adding-an-observation)
- [Evaluating a fixed policy](#evaluating-a-fixed-policy)
- [Trying a different world](#trying-a-different-world)
- [What a number depends on](#what-a-number-depends-on)
- [What the diagram bought](#what-the-diagram-bought)

## Motivation

A decision analysis has a small number of moving parts: what is believed
about the world, what can be observed before acting, what is done, what
follows from it, and what is counted in the end. In a spreadsheet these
are mixed together in one table. This vignette keeps them apart, as
boxes joined by wires, and then reads the usual answers (the payoff
table, the best action, the gain over doing nothing, the value of a
survey) off the diagram.

No category theory is needed to follow it. The diagram is a picture of
who needs to know what, and each answer is a function applied to the
picture.

The currency is individuals: outcomes are counted as animals of the
focal species.

## The problem

Water voles live in colonies along a lowland river. American mink, where
they are present in numbers, can remove a colony in a season. The
manager can leave the reach alone, trap mink, or restore the bank
vegetation that gives voles cover. What is not known is the mink
pressure on the reach this year: low or high.

**All numbers in this vignette are illustrative.** They were chosen to
make the arithmetic easy to follow. They are not data and they are not
estimates for any real river.

``` julia
using CategoricalDecisionAnalysis
include(joinpath("..", "_common.jl"))   # plot defaults and small tables, no analysis
```

    Main.Notebook.voi_table

`CategoricalDecisionAnalysis` re-exports everything in
`DecisionAnalysis`, so the one `using` line is enough.

## Wires

A wire is a variable with a finite list of values. It is written
`name => labels`.

``` julia
mink = :mink_pressure => [:low, :high]
action = :action => [:no_intervention, :trap_mink, :restore_banks]
colony = :colony => [:lost, :reduced, :thriving]
```

    :colony => [:lost, :reduced, :thriving]

## Boxes

There are five kinds of box. Three are needed for a first analysis.

A **belief box** says what is believed about a state. Here mink pressure
is low with probability 3/5.

``` julia
prior = belief_box(:what_we_believe, mink, [3 // 5, 2 // 5])
```

    DecisionPipeline: 1 box, inputs Symbol[], outputs [:mink_pressure]
      belief      what_we_believe : I → mink_pressure

A **consequence box** is the model: for every action and every state,
the probability of each outcome. The table has the outcome first, then
the inputs in the order they are listed, so `model[:, a, m]` is the
distribution of the colony’s fate under action `a` and mink pressure
`m`.

``` julia
model = zeros(Rational{Int}, 3, 3, 2)
#                          lost    reduced  thriving
model[:, 1, 1] = [1 // 10, 3 // 10, 6 // 10]   # no intervention, low mink pressure
model[:, 1, 2] = [7 // 10, 2 // 10, 1 // 10]   # no intervention, high
model[:, 2, 1] = [1 // 10, 2 // 10, 7 // 10]   # trapping, low
model[:, 2, 2] = [2 // 10, 4 // 10, 4 // 10]   # trapping, high
model[:, 3, 1] = [0 // 10, 2 // 10, 8 // 10]   # bank restoration, low
model[:, 3, 2] = [5 // 10, 3 // 10, 2 // 10]   # bank restoration, high
outcome = consequence_box(:colony_model, (action, mink), colony, model)
```

    DecisionPipeline: 1 box, inputs [:action, :mink_pressure], outputs [:colony]
      consequence colony_model : action ⊗ mink_pressure → colony

A **utility box** says what is counted: the number of voles on the reach
next spring, for each fate of the colony.

``` julia
voles = utility_box(:voles_next_spring, colony, [0, 40, 120])
```

    DecisionPipeline: 1 box, inputs [:colony], outputs Symbol[]
      utility     voles_next_spring : colony → ℝ

A **policy box** is the decision. It is left open: nothing has been
chosen yet. The empty pair of brackets says that the manager observes
nothing before choosing.

``` julia
manager = policy_box(:manager, (), action)
```

    DecisionPipeline: 1 box, inputs Symbol[], outputs [:action]
      policy      manager : I → action   (open)

## The diagram

`decision_pipeline` joins the boxes by the names of their wires: the
belief feeds the model, the policy feeds the model, the model feeds the
count.

``` julia
reach = decision_pipeline(prior, manager, outcome, voles)
```

    DecisionPipeline: 4 boxes, inputs Symbol[], outputs Symbol[]
      belief      what_we_believe : I → mink_pressure
      policy      manager : I → action   (open)
      consequence colony_model : action ⊗ mink_pressure → colony
      utility     voles_next_spring : colony → ℝ

The printout lists each box with the wires it reads and the wire it
writes. `I` means “nothing” (a belief has no input) and `ℝ` means “a
number” (a utility has no output wire).

## Reading the payoff table off the diagram

The payoff table of a decision analysis has one row per action and one
column per state, and in each cell the expected count. It is not typed
in here; it is computed from the model and the count.

``` julia
problem = decision_problem(reach; baseline=:no_intervention)
problem.payoff
```

**PayoffTable{Rational{Int64}}: 3 actions × 2 states**

| action            | `low` | `high` |
|:------------------|------:|-------:|
| `no_intervention` |    84 |     20 |
| `trap_mink`       |    92 |     64 |
| `restore_banks`   |   104 |     36 |

Each cell is the model’s distribution of fates under that action and
that state, weighted by the voles counted for each fate. For example
trapping under high mink pressure gives 0.2 × 0 + 0.4 × 40 + 0.4 × 120 =
64 voles.

What `decision_problem` returns is an ordinary `DecisionProblem` of
`DecisionAnalysis`, so everything in that package applies to it.

``` julia
expected = decide(problem, MaxExpectedUtility())
```

**DecisionResult: MaxExpectedUtility (higher is better)**

| action            | score | chosen |
|:------------------|------:|-------:|
| `no_intervention` |  58.4 |     \- |
| `trap_mink`       |  80.8 |    yes |
| `restore_banks`   |  76.8 |     \- |

First choice: trap_mink

``` julia
gain_over_baseline(problem)
```

**PayoffTable{Rational{Int64}}: 3 actions × 2 states**

| action            | `low` | `high` |
|:------------------|------:|-------:|
| `no_intervention` |     0 |      0 |
| `trap_mink`       |     8 |     44 |
| `restore_banks`   |    20 |     16 |

``` julia
expected_gain_over_baseline(problem)
```

    3-element Vector{Rational{Int64}}:
        0
     112//5
      92//5

Under this belief trapping gains about 22 voles over no intervention and
bank restoration about 18.

The same functions also take the diagram directly:

``` julia
(best=first_choice(decide(reach, MaxExpectedUtility())), value=act_now_value(reach),
 value_of_knowing_the_mink_pressure=evpi(reach))
```

    (best = :trap_mink, value = 404//5, value_of_knowing_the_mink_pressure = 36//5)

Knowing the mink pressure before choosing would be worth about seven
voles: with low pressure the manager would restore the banks, with high
pressure trap.

## Adding an observation

A footprint raft left on the reach for a fortnight records mink tracks.
It is not perfect: it misses mink that are there one time in four, and
records a passing animal one time in ten when pressure is low. An
observation process is a **channel box**.

``` julia
raft = :raft => [:no_tracks, :tracks]
survey = channel_box(:footprint_raft, mink, raft, [9//10 1//4; 1//10 3//4])
```

    DecisionPipeline: 1 box, inputs [:mink_pressure], outputs [:raft]
      channel     footprint_raft : mink_pressure → raft

The manager now reads the raft before choosing. Only the policy box
changes: it gains an input wire.

``` julia
informed_manager = policy_box(:manager, raft, action)
surveyed = decision_pipeline(prior, survey, informed_manager, outcome, voles)
```

    DecisionPipeline: 5 boxes, inputs Symbol[], outputs Symbol[]
      belief      what_we_believe : I → mink_pressure
      channel     footprint_raft : mink_pressure → raft
      policy      manager : raft → action   (open)
      consequence colony_model : action ⊗ mink_pressure → colony
      utility     voles_next_spring : colony → ℝ

``` julia
value_of_information(surveyed)
```

    (act_now = 404//5, informed = 2112//25, evsi = 92//25, perfect = 88//1, evpi = 36//5)

`act_now` is the best expected count with no observation, `informed` the
best expected count when the manager can act on the raft, and `evsi`
their difference: the raft is worth about 3.7 voles here, out of the 7.2
that perfect knowledge would be worth.

What the best policy is can be read from the compiled form of the
diagram (a later vignette is about that):

``` julia
best = solve_policy_program(surveyed)
md_table(vcat("after the raft shows", String.(best.observations)),
         [vcat(String(a), [Float64(best.policy[i, z]) for z in eachindex(best.observations)])
          for (i, a) in enumerate(best.actions)])
```

| after the raft shows | no_tracks | tracks |
|:---------------------|----------:|-------:|
| no_intervention      |         0 |      0 |
| trap_mink            |         0 |      1 |
| restore_banks        |         1 |      0 |

Restore the banks if the raft is clean, trap if it shows tracks.

## Evaluating a fixed policy

A policy can also be fixed and the diagram simply evaluated. A policy is
given as a rule from what is observed to what is done.

``` julia
by_the_raft = Dict(:no_tracks => :restore_banks, :tracks => :trap_mink)
always_trap = Dict(:no_tracks => :trap_mink, :tracks => :trap_mink)
never = Dict(:no_tracks => :no_intervention, :tracks => :no_intervention)
value(policy) = pipeline_value(surveyed; policies=(:manager => policy))
md_table(["policy", "expected voles", "gain over no intervention"],
         [["no intervention", value(never), 0],
          ["always trap", value(always_trap), value(always_trap) - value(never)],
          ["restore if clean, trap if tracks", value(by_the_raft),
           value(by_the_raft) - value(never)]])
```

| policy                           | expected voles | gain over no intervention |
|:---------------------------------|---------------:|--------------------------:|
| no intervention                  |           58.4 |                         0 |
| always trap                      |           80.8 |                      22.4 |
| restore if clean, trap if tracks |          84.48 |                     26.08 |

The numbers are exact fractions because the inputs were: the package
does not turn rational inputs into floating point.

## Trying a different world

Because the action is a wire, an action can be imposed and the
consequences read off, without a policy. `intervene` sets a wire to a
value. Setting a wire that a box produces removes that box: the wire no
longer depends on what it used to depend on.

``` julia
trapped = intervene(surveyed, :action => :trap_mink)
(expected_voles=pipeline_value(trapped),
 if_mink_pressure_were_high=pipeline_value(intervene(trapped, :mink_pressure => :high)))
```

    (expected_voles = 404//5, if_mink_pressure_were_high = 64//1)

## What a number depends on

Every answer above came from the boxes. `box_provenance` lists the boxes
that a number depends on, in the order in which they feed each other.

``` julia
md_table(["box", "kind", "reads", "writes"],
         [[String(b.name), String(b.kind), isempty(b.inputs) ? "nothing" : join(b.inputs, ", "),
           b.output === nothing ? "a count" : String(b.output)] for b in box_provenance(surveyed)])
```

| box               |        kind |                 reads |        writes |
|:------------------|------------:|----------------------:|--------------:|
| what*we*believe   |      belief |               nothing | mink_pressure |
| footprint_raft    |     channel |         mink_pressure |          raft |
| manager           |      policy |                  raft |        action |
| colony_model      | consequence | action, mink_pressure |        colony |
| voles*next*spring |     utility |                colony |       a count |

## What the diagram bought

- The payoff table was computed, not typed: change the model and the
  table follows.
- The observation was added by adding one box and one wire. Nothing else
  was edited.
- The same diagram was read in several ways: as a payoff table, as a
  value of information, under a fixed policy, under an imposed action.

The [next
vignette](../02_five_rules_one_pipeline/02_five_rules_one_pipeline.md)
keeps this diagram and changes the rule by which the manager chooses.
