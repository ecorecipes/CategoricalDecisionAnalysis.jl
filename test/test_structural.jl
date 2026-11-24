# The structural value-of-information criterion: a `false` is a guarantee.

@testset "structural value of information" begin
    rng = Xoshiro(20261203)
    st = :state => [:s1, :s2]
    other = :weather => [:w1, :w2]
    sig = :signal => [:z1, :z2]
    noise = :noise => [:n1, :n2]
    late = :outcome => [:y1, :y2]
    act = :action => [:none, :treat]
    k(m, n) = rational_kernel(rng, m, n)

    function build()
        return decision_pipeline(belief_box(:prior, st, rational_probabilities(rng, 2)),
                                 belief_box(:sky, other, rational_probabilities(rng, 2)),
                                 channel_box(:survey, st, sig, k(2, 2)),
                                 channel_box(:static, other, noise, k(2, 2)),
                                 policy_box(:manager, (), act),
                                 consequence_box(:model, (act, st), late,
                                                 reshape(reduce(hcat,
                                                                [rational_probabilities(rng,
                                                                                        2)
                                                                 for _ in 1:4]), 2, 2, 2)),
                                 utility_box(:animals, late, rand(rng, 0:30, 2)))
    end
    gain(p, wire) = solve_policy_program(with_observation(p, :manager, wire)).value -
                    solve_policy_program(p).value

    p = build()
    @test observation_can_matter(p, :state)        # the state drives the outcome
    @test observation_can_matter(p, :signal)       # and the survey informs about it
    @test !observation_can_matter(p, :weather)     # independent of everything that pays
    @test !observation_can_matter(p, :noise)
    @test !observation_can_matter(p, :outcome)     # downstream of the decision
    @test !observation_can_matter(p, :action)
    @test !observation_can_matter(with_observation(p, :manager, :signal), :signal)
    # once the state itself is observed, the survey adds nothing
    @test !observation_can_matter(with_observation(p, :manager, :state), :signal)
    @test observation_can_matter(with_observation(p, :manager, :signal), :state)

    @testset "a structural zero is a numerical zero, whatever the tables" begin
        for _ in 1:25
            q = build()
            for wire in (:weather, :noise)
                @test !observation_can_matter(q, wire)
                @test gain(q, wire) == 0
            end
            informed = with_observation(q, :manager, :state)
            @test !observation_can_matter(informed, :signal)
            @test gain(informed, :signal) == 0
            @test gain(q, :signal) >= 0 && gain(q, :state) >= gain(q, :signal)
            # the gain of the survey is the EVSI of the pipeline that reads it
            @test gain(q, :signal) == evsi(with_observation(q, :manager, :signal))
        end
    end

    @testset "true is a possibility, not a promise" begin
        flat = decision_pipeline(belief_box(:prior, st, [1 // 2, 1 // 2]),
                                 policy_box(:manager, (), act),
                                 utility_box(:animals, (act, st), [5 5; 3 3]))
        @test observation_can_matter(flat, :state)
        @test gain(flat, :state) == 0                # one action is best in every state
    end

    @testset "explaining away: a collider opened by what is already observed" begin
        # signal = f(state, weather): once the signal is read, the weather tells about
        # the state.
        joint = reshape(reduce(hcat, [rational_probabilities(rng, 2) for _ in 1:4]), 2, 2,
                        2)
        q = decision_pipeline(belief_box(:prior, st, [1 // 2, 1 // 2]),
                              belief_box(:sky, other, [1 // 2, 1 // 2]),
                              channel_box(:survey, (st, other), sig, joint),
                              policy_box(:manager, sig, act),
                              utility_box(:animals, (act, st), [10 0; 4 4]))
        @test observation_can_matter(q, :weather)
        @test gain(q, :weather) >= 0
        # without the signal the weather is separated from the payoff by the collider
        blind = decision_pipeline(belief_box(:prior, st, [1 // 2, 1 // 2]),
                                  belief_box(:sky, other, [1 // 2, 1 // 2]),
                                  channel_box(:survey, (st, other), sig, joint),
                                  policy_box(:manager, (), act),
                                  utility_box(:animals, (act, st), [10 0; 4 4]))
        @test !observation_can_matter(blind, :weather)
        @test gain(blind, :weather) == 0
    end

    @testset "errors" begin
        @test_throws PipelineStructureError observation_can_matter(p, :nowhere)
        @test_throws PipelineStructureError observation_can_matter(bind_policy(p,
                                                                               :manager => :none),
                                                                   :state)
        @test_throws PipelineStructureError observation_can_matter(p, :state; box=:survey)
        @test observation_can_matter(p, :state; box=:manager)
        @test_throws PipelineStructureError with_observation(p, :survey, :state)
        @test_throws PipelineStructureError with_observation(p, :manager, :outcome)
        bound = with_observation(bind_policy(p, :manager => :none), :manager, :signal)
        @test !pipeline_boxes(bound)[5].bound
    end
end
