# Cross-language fixtures. `test/fixtures/validation/programs_reference.json` is written
# by `validation/programs_reference.py` (Python, scipy `linprog` and `milp`, and exact
# enumeration with `fractions.Fraction`); this file only reads it, so the suite needs no
# Python. Never edit the fixture by hand: re-run the script.

using JSON: JSON

function parse_rational(s::AbstractString)
    return occursin('/', s) ?
           parse(Int, first(split(s, '/'))) // parse(Int, last(split(s, '/'))) :
           parse(Int, s) // 1
end
parse_rational(v::AbstractVector) = [parse_rational(x) for x in v]
rational_matrix(rows) = permutedims(reduce(hcat, [parse_rational(r) for r in rows]))

@testset "validation against Python (scipy)" begin
    fixture = JSON.parsefile(joinpath(@__DIR__, "fixtures", "validation",
                                      "programs_reference.json"))
    @test fixture["provenance"]["script"] == "validation/programs_reference.py"
    state = :state => [:t1, :t2, :t3]
    signal = :signal => [:z1, :z2]
    action = :action => [:none, :treat]

    @testset "the one-decision programme, with and without a budget" begin
        @test length(fixture["policy_programs"]) == 25
        for case in fixture["policy_programs"]
            prior = parse_rational(case["prior"])
            L = rational_matrix(case["likelihood"])
            Q = rational_matrix(case["payoff"])
            budget = parse_rational(case["budget"])
            p = decision_pipeline(belief_box(:prior, state, prior),
                                  channel_box(:survey, state, signal, L),
                                  policy_box(:manager, signal, action),
                                  utility_box(:animals, (action, state), Q))
            cap = expectation_constraint(:capacity, action, [0, 1]; at_most=budget)
            free = solve_policy_program(p)
            @test free.value == parse_rational(case["optimum"])
            @test Float64(free.value) ≈ case["optimum_linprog"] atol = 1e-7
            capped = solve_policy_program(p; constraints=[cap])
            @test Float64(capped.value) ≈ case["budget_optimum_linprog"] atol = 1e-7
            det = solve_strategy_program(strategy_program(p; constraints=[cap]))
            @test det.value == parse_rational(case["budget_deterministic_optimum"])
            @test Float64(det.value) ≈ case["budget_optimum_milp"] atol = 1e-6
            highs = solve_strategy_program(strategy_program(p; constraints=[cap]);
                                           optimizer=HiGHS.Optimizer)
            @test highs.value == det.value
        end
    end

    @testset "decision trees by brute force" begin
        @test length(fixture["trees"]) == 25
        for case in fixture["trees"]
            p1, p2 = parse_rational(case["first"]), parse_rational(case["second"])
            first_, actions, second = [:x, :y], [:l, :r], [:u, :v]
            payoff = Dict((a, b, c) => parse_rational(case["payoff"][i][j][k])
                          for (i, a) in enumerate(first_), (j, b) in enumerate(actions),
                              (k, c) in enumerate(second))
            tree = SequentialProblem([ChanceStage(:first, first_,
                                                  FiniteDistribution(first_, p1)),
                                      DecisionStage(:act, actions),
                                      ChanceStage(:second, second,
                                                  FiniteDistribution(second, p2))],
                                     h -> payoff[h])
            @test backward_induction(tree, MaxExpectedUtility()).value ==
                  parse_rational(case["expectation"])
            @test policy_search(tree, MaxExpectedUtility()).value ==
                  parse_rational(case["expectation"])
            sets = SequentialProblem(PowersetMonad(),
                                     [ChanceStage(:first, first_, FiniteSubset(first_)),
                                      DecisionStage(:act, actions),
                                      ChanceStage(:second, second, FiniteSubset(second))],
                                     h -> payoff[h])
            @test backward_induction(sets, Maximin()).value ==
                  parse_rational(case["worst_case"])
        end
    end
end
