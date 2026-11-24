# Chains of observation: sampling, assay, reporting
Simon Frost

- [Motivation](#motivation)
- [The decision](#the-decision)
- [Three observation processes](#three-observation-processes)
- [The value falls along the chain](#the-value-falls-along-the-chain)
- [The graph alone can say that an observation is
  worthless](#the-graph-alone-can-say-that-an-observation-is-worthless)
- [Updating the belief, with a report that never
  comes](#updating-the-belief-with-a-report-that-never-comes)
- [An experiment as a spread of
  beliefs](#an-experiment-as-a-spread-of-beliefs)
- [Surveys that cannot be ranked, and how far apart they
  are](#surveys-that-cannot-be-ranked-and-how-far-apart-they-are)
- [Partitions](#partitions)
- [Summary](#summary)

## Motivation

What a manager reads is rarely the state of the world. It is a report of
a laboratory result on a sample taken in the field, and each step can
lose information. This vignette builds such a chain as three boxes in a
row, shows that the value of the information can only fall along it, and
uses the same machinery to say when one survey is at least as good as
another for every decision.

**All numbers are illustrative.** Counts are of great crested newts, and
every result is compared with no intervention.

``` julia
using CategoricalDecisionAnalysis
include(joinpath("..", "_common.jl"))
```

    Main.Notebook.voi_table

## The decision

A pond is to be affected by drainage works. If newts are present and
nothing is done, most are lost. The manager can do nothing, or fence the
pond and move the newts to a receptor pond, which loses some animals to
handling and is wasted effort if the pond is empty (a few animals from
the receptor population are disturbed).

``` julia
pond = :pond => [:unoccupied, :small_population, :large_population]
action = :action => [:no_intervention, :fence_and_move]
newts = [0 3 12       # no intervention: newts alive after the works, by state
         -8 16 70]    # fence and move: animals moved and alive, less those disturbed
prior = [7 // 10, 1 // 5, 1 // 10]
base = decision_pipeline(belief_box(:occupancy, pond, prior), policy_box(:manager, (), action),
                         utility_box(:newts, (action, pond), newts))
problem = decision_problem(base; baseline=:no_intervention)
problem.payoff
```

**PayoffTable{Int64}: 2 actions × 3 states**

| action            | `unoccupied` | `small_population` | `large_population` |
|:------------------|-------------:|-------------------:|-------------------:|
| `no_intervention` |            0 |                  3 |                 12 |
| `fence_and_move`  |           -8 |                 16 |                 70 |

``` julia
(best_now=first_choice(decide(base, MaxExpectedUtility())),
 expected_gain_over_no_intervention=expected_gain_over_baseline(problem), evpi=evpi(base))
```

    (best_now = :fence_and_move, expected_gain_over_no_intervention = Rational{Int64}[0, 14//5], evpi = 28//5)

## Three observation processes

An environmental DNA survey has three steps.

1.  **Sampling.** Water is taken from the pond. Whether newt DNA is in
    the bottle depends on how many newts there are.
2.  **Assay.** The laboratory runs a qPCR on the bottle, with its own
    false negatives and false positives.
3.  **Reporting.** The laboratory reports “clear” or “flagged”. This
    laboratory flags only strong positives and never issues the third
    thing its form allows, “inconclusive”.

Each is a channel box: a table of the probability of each output for
each input.

``` julia
bottle = :bottle => [:no_dna, :dna]
qpcr = :qpcr => [:negative, :weak_positive, :strong_positive]
report = :report => [:clear, :flagged, :inconclusive]

sampling = channel_box(:sampling, pond, bottle, [1 3//10 1//20; 0 7//10 19//20])
assay = channel_box(:assay, bottle, qpcr, [9//10 1//10; 2//25 3//10; 1//50 3//5])
reporting = channel_box(:reporting, qpcr, report, [1 1//2 0; 0 1//2 1; 0 0 0])
```

    DecisionPipeline: 1 box, inputs [:qpcr], outputs [:report]
      channel     reporting : qpcr → report

Boxes in a row are joined with `compose`, and the chain is a channel in
its own right. Its table is the product of the three tables, which
`evaluate` computes:

``` julia
chain = compose(sampling, assay, reporting)
first(reward_matrices(evaluate(chain)))
```

    3×3 Matrix{Rational{Int64}}:
     47//50  457//1000   569//2000
      3//50  543//1000  1431//2000
       0        0           0

Rows are the three reports, columns the three states of the pond. The
last row is zero: “inconclusive” never happens.

## The value falls along the chain

The manager can be given the bottle (as if the DNA could be seen), the
qPCR result, or the report. Each is the same diagram with the policy box
reading a different wire.

``` julia
whole = decision_pipeline(base, sampling, assay, reporting)
reading(wire) = with_observation(whole, :manager, wire)
stages = [:pond, :bottle, :qpcr, :report]
values = [value_of_information(reading(w)) for w in stages]
md_table(["the manager reads", "expected newts", "gain over no intervention",
          "value of the information"],
         [[String(w), v.informed, v.informed - pipeline_value(base; policies=(:manager => :no_intervention)),
           v.evsi] for (w, v) in zip(stages, values)])
```

| the manager reads | expected newts | gain over no intervention | value of the information |
|:---|---:|---:|---:|
| pond | 10.2 | 8.4 | 5.6 |
| bottle | 9.13 | 7.33 | 4.53 |
| qpcr | 7.94 | 6.14 | 3.34 |
| report | 7.03 | 5.23 | 2.43 |

Reading the pond itself is perfect information. Each later stage is
worth no more than the one before it. This is not a feature of these
numbers: each stage is the previous one passed through a noisy channel,
a *garbling*, and a garbling is never worth more to any decision-maker
with a single prior (Blackwell’s theorem).

``` julia
experiment(wire) = observation_experiment(reading(wire))
at_bottle, at_qpcr, at_report = experiment(:bottle), experiment(:qpcr), experiment(:report)
(report_is_a_garbling_of_qpcr=is_garbling(at_report, at_qpcr),
 qpcr_is_a_garbling_of_bottle=is_garbling(at_qpcr, at_bottle),
 bottle_is_a_garbling_of_report=is_garbling(at_bottle, at_report))
```

    (report_is_a_garbling_of_qpcr = true, qpcr_is_a_garbling_of_bottle = true, bottle_is_a_garbling_of_report = false)

The order is a preorder on experiments, and the value of a fixed problem
is a monotone map out of it. The package checks the property on random
problems in its tests; here it is on this one:

``` julia
issorted([information_value(problem, e) for e in (at_report, at_qpcr, at_bottle)])
```

    true

## The graph alone can say that an observation is worthless

Once the manager reads the qPCR result, the report adds nothing:
everything the report says about the pond it says through the qPCR. That
follows from the shape of the diagram, with no arithmetic.

``` julia
(report_can_matter_given_nothing=observation_can_matter(whole, :report),
 report_can_matter_given_the_qpcr=observation_can_matter(reading(:qpcr), :report),
 qpcr_can_matter_given_the_report=observation_can_matter(reading(:report), :qpcr))
```

    (report_can_matter_given_nothing = true, report_can_matter_given_the_qpcr = false, qpcr_can_matter_given_the_report = true)

A `false` is a guarantee for any tables whatever. A `true` only says
that the value can be positive.

## Updating the belief, with a report that never comes

Bayes’ rule turns the chain round: from a report to a belief about the
pond. `bayesian_inverse` computes it in two steps, the joint probability
of state and report first and the division second, and does the division
only where there is something to divide by.

``` julia
inverse = bayesian_inverse(problem.belief, at_report)
md_table(["report", "probability", "P(unoccupied)", "P(small)", "P(large)"],
         [vcat(String(z), inverse.evidence[i], inverse.inverse[:, i])
          for (i, z) in enumerate(inverse.signals)])
```

| report       | probability | P(unoccupied) | P(small) | P(large) |
|:-------------|------------:|--------------:|---------:|---------:|
| clear        |        0.78 |          0.85 |     0.12 |     0.04 |
| flagged      |        0.22 |          0.19 |     0.49 |     0.32 |
| inconclusive |           0 |             0 |        0 |        0 |

The “inconclusive” report has probability zero, and its column is zero:
no posterior is invented for it and nothing fails. `posterior` says the
same in words:

``` julia
(after_flagged=posterior(inverse, :flagged), after_inconclusive=posterior(inverse, :inconclusive))
```

    (after_flagged = Rational{Int64}[280//1481, 724//1481, 477//1481], after_inconclusive = nothing)

Inverting the whole chain is the same as inverting its steps and
composing the inversions, at every report including the one that never
comes:

``` julia
K(box) = first(reward_matrices(evaluate(box)))
first_step = bayesian_inverse(prior, K(compose(sampling, assay)))
second_step = bayesian_inverse(first_step.evidence, K(reporting))
inverse_compose(first_step, second_step) == inverse.inverse
```

    true

## An experiment as a spread of beliefs

Another way to see why the report is worth less: look at the beliefs the
manager can end up with. A better experiment spreads them further from
the prior.

``` julia
function beliefs_after(e)
    μ = posterior_distribution(problem.belief, e)
    return [(probability=Float64(p), P_unoccupied=round(Float64(π[1]); digits=3),
             P_large=round(Float64(π[3]); digits=3)) for (π, p) in zip(μ.outcomes, μ.probabilities)]
end
(after_the_qpcr=beliefs_after(at_qpcr), after_the_report=beliefs_after(at_report))
```

    (after_the_qpcr = [(probability = 0.712, P_unoccupied = 0.885, P_large = 0.02), (probability = 0.1317, P_unoccupied = 0.425, P_large = 0.219), (probability = 0.1563, P_unoccupied = 0.09, P_large = 0.365)], after_the_report = [(probability = 0.77785, P_unoccupied = 0.846, P_large = 0.037), (probability = 0.22215, P_unoccupied = 0.189, P_large = 0.322)])

The beliefs after the report are averages of the beliefs after the qPCR,
so they lie closer together. Both average back to the prior:

``` julia
posterior_mean(posterior_distribution(problem.belief, at_report)) == prior
```

    true

## Surveys that cannot be ranked, and how far apart they are

A second laboratory uses a cheaper assay but reports all three qPCR
classes. Neither report is a garbling of the other, so which is better
depends on the decision.

``` julia
cheap_assay = channel_box(:assay, bottle, qpcr, [4//5 1//5; 3//20 2//5; 1//20 2//5])
other = decision_pipeline(base, sampling, cheap_assay)
at_other = observation_experiment(with_observation(other, :manager, :qpcr))
(other_from_report=is_garbling(at_other, at_report), report_from_other=is_garbling(at_report, at_other))
```

    (other_from_report = false, report_from_other = false)

The deficiency measures how far one experiment is from being able to
imitate the other, and bounds how much more the other can be worth in
this problem:

``` julia
(value_of_report=information_value(problem, at_report),
 value_of_other=information_value(problem, at_other),
 other_can_exceed_report_by_at_most=value_gap_bound(problem, at_report, at_other),
 report_can_exceed_other_by_at_most=value_gap_bound(problem, at_other, at_report))
```

    (value_of_report = 70257//10000, value_of_other = 3379//500, other_can_exceed_report_by_at_most = 6612//12245, report_can_exceed_other_by_at_most = 53447//10750)

## Partitions

Learning which group a state belongs to is a special experiment. Finer
groups are worth at least as much. Here knowing only whether the pond is
occupied is already worth as much as knowing the size of the population,
because the best action is the same for a small and a large population.

``` julia
occupied_or_not = [:unoccupied, :occupied, :occupied]
exactly = [:unoccupied, :small, :large]
(finer=refines(exactly, occupied_or_not),
 value_of_knowing_occupancy=evppi(problem, occupied_or_not),
 the_same_as_an_experiment=evsi(problem, partition_experiment(occupied_or_not)),
 value_of_knowing_exactly=evppi(problem, exactly))
```

    (finer = true, value_of_knowing_occupancy = 28//5, the_same_as_an_experiment = 28//5, value_of_knowing_exactly = 28//5)

## Summary

A chain of observation processes is boxes in a row. The value of what is
read at the end of the chain is at most the value of what is read
earlier, for every decision, and the diagram says so before any number
is computed. The package adds no new measure of information: the values
are those of `DecisionAnalysis`, read off the diagram.
