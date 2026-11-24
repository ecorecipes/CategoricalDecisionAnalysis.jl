# Certificates for the Lean checker in `proofs/`.

lean_available() = get(ENV, "CATEGORICALDECISIONANALYSIS_LEAN", "") == "1"

@testset "certificates" begin
    rng = Xoshiro(20261202)
    problem = DecisionProblem(PayoffTable([1 0; 0 1]), [3 // 5, 2 // 5])
    experiment = Experiment([4//5 1//4; 1//5 3//4])
    fixtures = joinpath(dirname(@__DIR__), "proofs", "certificate-fixtures")
    strip_space(s) = replace(s, r"\s" => "")

    @testset "policy certificate" begin
        io = IOBuffer()
        @test export_policy_certificate(io, problem, experiment) === nothing
        text = String(take!(io))
        doc = JSON.parse(text)
        @test doc["schema"] == POLICY_CERTIFICATE_SCHEMA == "policy-certificate/1"
        @test doc["value"] == "39/50" && doc["dual"] == ["12/25", "3/10"]
        @test doc["policy"] == [["1", "0"], ["0", "1"]]
        # the document is the hand-written fixture of the Lean development
        hand = joinpath(fixtures, "policy_two_signals.json")
        isfile(hand) && @test JSON.parse(text) == JSON.parsefile(hand)
        # the claim is re-derived here: value = Σ dual = objective of the policy = the core's
        for _ in 1:25
            x = random_pieces(rng)
            p = closed_pipeline(x)
            io = IOBuffer()
            export_policy_certificate(io, p)
            doc = JSON.parse(String(take!(io)))
            value = parse_rational(doc["value"])
            @test value == value_with_information(p)
            @test sum(parse_rational(doc["dual"])) == value
            π = rational_matrix(doc["policy"])
            @test all(isone, sum(π; dims=1))
            c = [sum(x.prior[θ] * x.L[z, θ] * oracle_payoff(x)[a, θ] for θ in 1:3)
                 for a in 1:2, z in 1:2]
            @test sum(π .* c) == value
            @test all(parse_rational(doc["dual"])[z] >= c[a, z] for a in 1:2, z in 1:2)
            # the policy found by the linear programme is accepted as well
            sol = solve_policy_program(p)
            @test export_policy_certificate(IOBuffer(), p; policy=sol.policy) === nothing
        end
        # nothing is written for a claim that does not verify
        io = IOBuffer()
        @test_throws WitnessError export_policy_certificate(io, problem, experiment;
                                                            policy=[0 1; 1 0])
        @test isempty(take!(io))
        @test_throws WitnessError export_policy_certificate(IOBuffer(), problem, experiment;
                                                            policy=[1 1; 1 0])
        @test_throws WitnessError export_policy_certificate(IOBuffer(), problem, experiment;
                                                            policy=[1 0 0; 0 1 1])
        float_problem = DecisionProblem(PayoffTable([1.0 0.0; 0.0 1.0]), [0.6, 0.4])
        @test_throws InexactCertificateError export_policy_certificate(IOBuffer(),
                                                                       float_problem,
                                                                       experiment)
        @test_throws InexactCertificateError export_policy_certificate(IOBuffer(), problem,
                                                                       Experiment([0.8 0.25;
                                                                                   0.2 0.75]))
        credal = DecisionProblem(PayoffTable([1 0; 0 1]), CredalSet([[1, 0], [0, 1]]))
        @test_throws BeliefFormError export_policy_certificate(IOBuffer(), credal,
                                                               experiment)
        @test_throws ArgumentError export_policy_certificate(IOBuffer(), problem,
                                                             Experiment([1 0 0; 0 1 1]))
    end

    @testset "fidelity-chain certificate" begin
        exact = [[9//10 1//5; 1//10 4//5], [1//2 1//2; 1//2 1//2]]
        approx = [[4//5 1//5; 1//5 4//5], [3//5 1//2; 2//5 1//2]]
        io = IOBuffer()
        @test export_fidelity_chain_certificate(io, exact, approx; range=10) === nothing
        text = String(take!(io))
        doc = JSON.parse(text)
        @test doc["schema"] == FIDELITY_CHAIN_CERTIFICATE_SCHEMA ==
              "fidelity-chain-certificate/1"
        @test doc["bound"] == "4" && doc["range"] == "10"
        @test [b["error"] for b in doc["boxes"]] == ["1/10", "1/10"]
        hand = joinpath(fixtures, "fidelity_two_boxes.json")
        isfile(hand) && @test doc == JSON.parsefile(hand)
        # the claim holds: decide through the approximate chain, pay through the exact one
        for _ in 1:25
            n = 3
            Ks = [rational_kernel(rng, n, n) for _ in 1:2]
            Ks′ = [(9 .* K .+ rational_kernel(rng, n, n)) .// 10 for K in Ks]
            t = random_payoff_table(rng, 3, n; T=Rational{Int})
            B = largest_action_range(t)
            io = IOBuffer()
            export_fidelity_chain_certificate(io, Ks, Ks′; range=B)
            bound = parse_rational(JSON.parse(String(take!(io)))["bound"])
            @test bound == 2 * B * sum(kernel_distance(K, K′) for (K, K′) in zip(Ks, Ks′))
            prior = rational_probabilities(rng, n)
            truth, approximate = Ks[2] * Ks[1] * prior, Ks′[2] * Ks′[1] * prior
            chosen = argmax(t.Q * approximate)
            @test maximum(t.Q * truth) - (t.Q * truth)[chosen] <= bound
        end
        # larger stated errors are allowed, smaller ones are refused
        @test export_fidelity_chain_certificate(IOBuffer(), exact, approx; range=10,
                                                errors=[1 // 5, 1 // 10]) === nothing
        io = IOBuffer()
        @test_throws WitnessError export_fidelity_chain_certificate(io, exact, approx;
                                                                    range=10,
                                                                    errors=[1 // 20,
                                                                            1 // 10])
        @test isempty(take!(io))
        # an emulator that is not normalised is refused
        truncated = [[4//5 1//5; 1//10 4//5], approx[2]]
        @test_throws WitnessError export_fidelity_chain_certificate(IOBuffer(), exact,
                                                                    truncated;
                                                                    range=10)
        @test_throws WitnessError export_fidelity_chain_certificate(IOBuffer(), exact,
                                                                    [approx[1],
                                                                     [1 0 0; 0 1 0; 0 0 1]];
                                                                    range=10)
        @test_throws InexactCertificateError export_fidelity_chain_certificate(IOBuffer(),
                                                                               [[0.9 0.2;
                                                                                 0.1 0.8]],
                                                                               [[0.8 0.2;
                                                                                 0.2 0.8]];
                                                                               range=10)
        @test_throws ArgumentError export_fidelity_chain_certificate(IOBuffer(), exact,
                                                                     approx[1:1];
                                                                     range=10)
        @test_throws ArgumentError export_fidelity_chain_certificate(IOBuffer(), exact,
                                                                     approx;
                                                                     range=-1)
        @test_throws ArgumentError export_fidelity_chain_certificate(IOBuffer(), exact,
                                                                     approx;
                                                                     range=10,
                                                                     errors=[1 // 5])
    end

    @testset "files, and the Lean checker" begin
        exact = [[9//10 1//5; 1//10 4//5], [1//2 1//2; 1//2 1//2]]
        approx = [[4//5 1//5; 1//5 4//5], [3//5 1//2; 2//5 1//2]]
        mktempdir() do dir
            files = Dict("policy" => joinpath(dir, "policy.json"),
                         "fidelity" => joinpath(dir, "fidelity.json"))
            export_policy_certificate(files["policy"], problem, experiment)
            export_fidelity_chain_certificate(files["fidelity"], exact, approx; range=10)
            @test JSON.parsefile(files["policy"])["value"] == "39/50"
            @test JSON.parsefile(files["fidelity"])["bound"] == "4"
            proofs = joinpath(dirname(@__DIR__), "proofs")
            built = isdir(joinpath(proofs, ".lake", "build"))
            if !(lean_available() && Sys.which("lake") !== nothing && built)
                @info "Lean certificate check skipped: set CATEGORICALDECISIONANALYSIS_LEAN=1, " *
                      "with `lake` on the PATH and `proofs/` built (`cd proofs && lake build`), " *
                      "to run `lake exe check_certificate` on exported files."
            else
                function exit_code(file)
                    return run(Cmd(ignorestatus(`lake exe check_certificate $file`);
                                   dir=proofs)).exitcode
                end
                for (kind, file) in files
                    @testset "$kind accepted" begin
                        @test exit_code(file) == 0
                    end
                end
                # a tampered copy of each must be refused
                tampered = Dict("policy" => ("\"value\": \"39/50\"" => "\"value\": \"4/5\""),
                                "fidelity" => ("\"bound\": \"4\"" => "\"bound\": \"3\""))
                for (kind, change) in tampered
                    text = read(files[kind], String)
                    @test occursin(first(change), text)
                    bad = joinpath(dir, "tampered_$kind.json")
                    write(bad, replace(text, change))
                    @testset "tampered $kind refused" begin
                        @test exit_code(bad) == 1
                    end
                end
                # certificates of random pipelines
                for i in 1:5
                    file = joinpath(dir, "random_$i.json")
                    export_policy_certificate(file, closed_pipeline(random_pieces(rng)))
                    @test exit_code(file) == 0
                end
            end
        end
    end
end
