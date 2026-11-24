# Compiling a diagram to an optimisation programme
Simon Frost

- [Motivation](#motivation)
- [The diagram](#the-diagram)
- [One decision: a linear programme](#one-decision-a-linear-programme)
- [A budget](#a-budget)
- [A cap on a probability](#a-cap-on-a-probability)
- [Several decisions: a mixed-integer
  programme](#several-decisions-a-mixed-integer-programme)
  - [Programmes compose; solutions do
    not](#programmes-compose-solutions-do-not)
- [A certificate](#a-certificate)
- [Summary](#summary)

## Motivation

The diagrams of the earlier vignettes were solved by looking at every
policy. That stops being possible quickly, and it cannot handle a side
condition such as “the field team can treat at most so many ponds”. This
vignette compiles a decision diagram to an optimisation programme,
stated as a JuMP model: the decision box becomes the variables, the
chance boxes the coefficients, the utility boxes the objective, and a
side condition one more constraint. Any solver that JuMP knows can then
be used; none is required, because the package carries an exact solver
for small problems.

**All numbers are illustrative.** Counts are of frogs, and every result
is compared with no intervention.

``` julia
using CategoricalDecisionAnalysis
using JuMP: JuMP
using HiGHS: HiGHS
using CDDLib: CDDLib
include(joinpath("..", "_common.jl"))
```

    Main.Notebook.voi_table

## The diagram

A chytrid fungus may be present in a pond that holds a frog population.
A swab survey gives a low or a high count of infected animals. The
manager can do nothing or treat the frogs with an antifungal bath, which
loses a few animals to handling.

``` julia
pond = :pond => [:clear, :light_infection, :heavy_infection]
swabs = :swabs => [:low, :high]
action = :action => [:no_intervention, :treat]
frogs = [100 60 15       # no intervention: frogs alive next year, by state of the pond
         88 85 55]       # treat
prior = [1 // 2, 3 // 10, 1 // 5]
survey = [9//10 1//2 1//10; 1//10 1//2 9//10]
diagram = decision_pipeline(belief_box(:prior, pond, prior),
                            channel_box(:swab_survey, pond, swabs, survey),
                            policy_box(:manager, swabs, action),
                            utility_box(:frogs, (action, pond), frogs))
value_of_information(diagram)
```

    (act_now = 161//2, informed = 1627//20, evsi = 17//20, perfect = 173//2, evpi = 6//1)

## One decision: a linear programme

`policy_program` compiles the diagram. The variables `π[a, z]` are the
probability of taking action `a` after survey result `z`.

``` julia
program = policy_program(diagram)
print(program.model)
```

    Max 543//10 π[1,1] + 167//10 π[1,2] + 1069//20 π[2,1] + 541//20 π[2,2]
    Subject to
     π[1,1] + π[2,1] = 1//1
     π[1,2] + π[2,2] = 1//1
     π[1,1] ≥ 0//1
     π[2,1] ≥ 0//1
     π[1,2] ≥ 0//1
     π[2,2] ≥ 0//1

The objective coefficients are the expected frogs of each action jointly
with each survey result; the two equality constraints say that after
each result some action is taken. The model has rational coefficients,
because the diagram did.

``` julia
solution = solve_program(program)
(status=solution.status, frogs=solution.objective, exact=solution.exact, route=solution.route)
```

    (status = :optimal, frogs = 1627//20, exact = true, route = :internal)

The optimum equals the value read off the diagram, and the best policy
takes one action after each result: for one decision the linear
programme is exact, and no integer variables are needed (a theorem of
the accompanying Lean development, `policyProgramme_optimum`).

``` julia
best = solve_policy_program(diagram)
no_intervention = pipeline_value(diagram; policies=(:manager => :no_intervention))
(policy=Dict(z => best.actions[findfirst(isone, best.policy[:, i])]
             for (i, z) in enumerate(best.observations)),
 frogs=best.value, gain_over_no_intervention=best.value - no_intervention,
 same_as_the_diagram=best.value == value_with_information(diagram))
```

    (policy = Dict(:high => :treat, :low => :no_intervention), frogs = 1627//20, gain_over_no_intervention = 207//20, same_as_the_diagram = true)

The same model by two other solvers. An exact solver works on the
rational model directly; a floating-point solver’s answer is rounded and
then verified exactly.

``` julia
by_cdd = solve_program(policy_program(diagram); optimizer=CDDLib.Optimizer{Rational{BigInt}})
by_highs = solve_program(policy_program(diagram); optimizer=HiGHS.Optimizer)
[(route=s.route, frogs=s.objective, exact=s.exact) for s in (solution, by_cdd, by_highs)]
```

    3-element Vector{@NamedTuple{route::Symbol, frogs::Rational{BigInt}, exact::Bool}}:
     (route = :internal, frogs = 1627//20, exact = 1)
     (route = :exact_optimizer, frogs = 1627//20, exact = 1)
     (route = :float_optimizer, frogs = 1627//20, exact = 1)

## A budget

Suppose this is one of many similar ponds and the field team can treat,
on average, one pond in five. That is a bound on the expected value of a
quantity: one for a treated pond, nothing otherwise.

``` julia
capacity = expectation_constraint(:field_team, action, [0, 1]; at_most=1 // 5)
limited = solve_policy_program(diagram; constraints=[capacity])
md_table(vcat("after the survey shows", String.(limited.observations)),
         [vcat(String(a), [limited.policy[i, z] for z in eachindex(limited.observations)])
          for (i, a) in enumerate(limited.actions)])
```

| after the survey shows | low | high |
|:-----------------------|----:|-----:|
| no_intervention        |   1 | 0.47 |
| treat                  |   0 | 0.53 |

``` julia
(frogs_with_the_budget=limited.value, frogs_without=best.value,
 gain_over_no_intervention=limited.value - no_intervention,
 deterministic=limited.deterministic)
```

    (frogs_with_the_budget = 2905//38, frogs_without = 1627//20, gain_over_no_intervention = 207//38, deterministic = false)

With the budget the best policy randomises: after a high count, treat
with the probability that just uses the capacity. A solver that searches
over deterministic policies, as the influence-diagram solvers of the
ecosystem do, cannot return it, and has no way to be told about the
budget in the first place. Restricting to deterministic policies under
the same budget does worse:

``` julia
deterministic = solve_strategy_program(strategy_program(diagram; constraints=[capacity]))
(frogs=deterministic.value, policy=deterministic.policies[:manager])
```

    (frogs = 71//1, policy = [:no_intervention, :no_intervention])

## A cap on a probability

A side condition can also bound the chance of an event. An infected pond
that is left untreated is a source of infection for its neighbours.
Suppose the regional plan accepts a probability of at most one in ten
that this pond is left as a source. The event is a statement about two
wires, the action and the state of the pond, and its probability is
linear in the policy.

``` julia
left_as_source(a, s) = a === :no_intervention && s !== :clear
few_sources = chance_constraint(:left_as_a_source, (action, pond), left_as_source; at_most=1 // 10)
cautious = solve_policy_program(diagram; constraints=[few_sources])
md_table(vcat("after the survey shows", String.(cautious.observations)),
         [vcat(String(a), [cautious.policy[i, z] for z in eachindex(cautious.observations)])
          for (i, a) in enumerate(cautious.actions)])
```

| after the survey shows |  low | high |
|:-----------------------|-----:|-----:|
| no_intervention        | 0.59 |    0 |
| treat                  | 0.41 |    1 |

``` julia
(frogs=cautious.value, gain_over_no_intervention=cautious.value - no_intervention)
```

    (frogs = 81//1, gain_over_no_intervention = 10//1)

## Several decisions: a mixed-integer programme

With more than one decision the expected count is no longer linear in
the policies, because the probability of reaching the second decision
depends on the first. The standard remedy, used by
DecisionProgramming.jl, is a programme with one binary variable for each
local choice and one flow variable for each path through the diagram.

Add a second decision: a second team visits later, sees its own survey
but not the first one or what was done, and can remove infected animals.

``` julia
second_look = :second_look => [:low, :high]
follow_up = :follow_up => [:leave, :remove_infected]
extra = zeros(Int, 2, 2, 3)                    # extra frogs alive: [action, follow_up, pond]
extra[1, 2, :] = [-6, 20, 60]                  # removal after no treatment
extra[2, 2, :] = [-6, -5, 2]                   # removal after treatment
first_visit = decision_pipeline(belief_box(:prior, pond, prior),
                                channel_box(:swab_survey, pond, swabs, survey),
                                policy_box(:manager, swabs, action),
                                utility_box(:frogs, (action, pond), frogs);
                                outputs=[:pond, :action])
second_visit = decision_pipeline(channel_box(:second_survey, pond, second_look, survey),
                                 policy_box(:second_team, second_look, follow_up),
                                 utility_box(:extra_frogs, (action, follow_up, pond), extra);
                                 inputs=[:pond, :action])
both = compose(first_visit, second_visit)
program2 = strategy_program(both)
```

    StrategyProgram(1 part, 56 variables, 2 decisions)

``` julia
solved = solve_strategy_program(program2)
(frogs=solved.value, manager=solved.policies[:manager], second_team=solved.policies[:second_team],
 strategies_examined=solved.strategies, gain_over_no_intervention=solved.value - no_intervention)
```

    (frogs = 86//1, manager = [:no_intervention, :no_intervention], second_team = [:remove_infected, :remove_infected], strategies_examined = 16, gain_over_no_intervention = 15//1)

Without a solver the package enumerates the strategies exactly. With a
mixed-integer solver the model is solved in floating point, and the
strategy it returns is then evaluated on the diagram in exact
arithmetic:

``` julia
by_solver = solve_strategy_program(program2; optimizer=HiGHS.Optimizer)
(frogs=by_solver.value, route=by_solver.route, same=by_solver.value == solved.value)
```

    (frogs = 86//1, route = :optimizer, same = true)

### Programmes compose; solutions do not

The two visits were built as two diagrams and joined. Their programmes
join in the same way: the probability of each joint value of the shared
wires is a quantity that both programmes mention, and the objectives
add.

``` julia
joined = compose(strategy_program(first_visit), open_strategy_program(second_visit))
(parts=length(joined.parts), frogs=solve_strategy_program(joined).value,
 same_as_the_glued_diagram=solve_strategy_program(joined).value == solved.value)
```

    (parts = 2, frogs = 86//1, same_as_the_glued_diagram = true)

What is composed is the *statement* of the problem. It is still solved
as one problem: the best policy of the first visit depends on what the
second team will do with what it leaves behind. Optimising the first
visit alone gives a different policy for it:

``` julia
alone = solve_strategy_program(strategy_program(first_visit))
(first_visit_alone=alone.policies[:manager], first_visit_in_context=solved.policies[:manager])
```

    (first_visit_alone = [:no_intervention, :treat], first_visit_in_context = [:no_intervention, :no_intervention])

## A certificate

For one decision, the optimum can be exported as a document that a
proved checker verifies without trusting any solver: the problem, a best
policy, and one number per survey result (the best expected count after
that result) that proves that no policy does better.

``` julia
io = IOBuffer()
export_policy_certificate(io, diagram)
print(String(take!(io)))
```

    {
      "schema": "policy-certificate/1",
      "payoff": [["100", "60", "15"], ["88", "85", "55"]],
      "prior": ["1/2", "3/10", "1/5"],
      "likelihood": [["9/10", "1/2", "1/10"], ["1/10", "1/2", "9/10"]],
      "policy": [["1", "0"], ["0", "1"]],
      "dual": ["543/10", "541/20"],
      "value": "1627/20"
    }

## Summary

|  | one decision | several decisions |
|:---|:---|:---|
| programme | linear (`policy_program`) | mixed-integer (`strategy_program`) |
| policies | may randomise | deterministic |
| solved by | exact simplex, or any JuMP solver | exact enumeration, or any mixed-integer solver |
| side conditions | budgets and chance constraints | the same |
| composes |  | programmes of parts, not their solutions |

Prior art: the path formulation for several decisions is that of Salo,
Andelmin and Oliveira (2022), implemented in DecisionProgramming.jl;
joining programmes along shared variables follows the open optimisation
problems of Hanks and co-authors (2024), implemented in
AlgebraicOptimization.jl. Neither package is a dependency.
