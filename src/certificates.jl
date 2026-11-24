# Certificates: documents that the Lean checker in `proofs/` decides
# (`lake exe check_certificate FILE.json`). The schemas are a contract with the Lean
# development and are written down in `docs/src/certificates.md`. Every number is a
# JSON string "n/d" or "n"; matrices are arrays of rows. Nothing is written unless
# the claim has been verified here in exact arithmetic.

"""
    POLICY_CERTIFICATE_SCHEMA

The schema identifier of [`export_policy_certificate`](@ref),
`"policy-certificate/1"`.
"""
const POLICY_CERTIFICATE_SCHEMA = "policy-certificate/1"

"""
    FIDELITY_CHAIN_CERTIFICATE_SCHEMA

The schema identifier of [`export_fidelity_chain_certificate`](@ref),
`"fidelity-chain-certificate/1"`.
"""
const FIDELITY_CHAIN_CERTIFICATE_SCHEMA = "fidelity-chain-certificate/1"

_cert_number(x::Integer) = string('"', x, '"')
function _cert_number(x::Rational)
    return isone(denominator(x)) ? string('"', numerator(x), '"') :
           string('"', numerator(x), '/', denominator(x), '"')
end
_cert_vector(v::AbstractVector) = "[" * join((_cert_number(x) for x in v), ", ") * "]"
function _cert_matrix(M::AbstractMatrix)
    return "[" * join((_cert_vector(M[i, :]) for i in axes(M, 1)), ", ") * "]"
end

function _require_exact_entries(what::AbstractString, A)
    T = A isa AbstractArray ? eltype(A) : typeof(A)
    _exact(T) || throw(InexactCertificateError(what, T))
    return nothing
end

_write_text(io::IO, text::AbstractString) = (print(io, text); nothing)
function _write_text(path::AbstractString, text::AbstractString)
    open(io -> print(io, text), path, "w")
    return nothing
end

"""
    export_policy_certificate(io_or_path, problem::DecisionProblem, experiment::Experiment; policy=nothing)
    export_policy_certificate(io_or_path, pipeline::DecisionPipeline; policy=nothing)

Write a `"policy-certificate/1"` document: a one-decision problem (payoff table of
the feasible actions, prior, likelihood), an optimal policy `policy[a, z] = P(a | z)`,
a dual vector with one entry per signal, and the optimal value. The Lean checker
(`lake exe check_certificate`, theorem `Certificate.RawPolicy.accepts_sound`)
accepts it exactly when the policy is column-stochastic, the dual dominates every
objective coefficient `c[a, z] = Σ_θ p(θ) L[z, θ] Q[a, θ]`, and the policy's
objective and the sum of the dual both equal the value; it then follows that the
value is `value_with_information(problem, experiment)` and that no policy does
better.

No solver is asked for duals: the dual is the column maxima of the coefficients
(Lean `policy_certificate_sound`). `policy` defaults to the deterministic policy
that takes the first best action after each signal; any optimal policy may be given
instead (a matrix, rows = feasible actions, columns = signals), for example the one
[`solve_policy_program`](@ref) found. For a pipeline the problem and the experiment
are its [`decision_problem`](@ref) and [`observation_experiment`](@ref).

The claim is verified in exact arithmetic before anything is written: a policy that
is not column-stochastic or not optimal throws `WitnessError`, and entries that are
not integers or rationals throw `InexactCertificateError` (both from
DecisionAnalysis). Needs a single finite prior.
"""
function export_policy_certificate(dest, problem::DecisionProblem, experiment::Experiment;
                                   policy=nothing)
    problem.belief isa FiniteBelief ||
        throw(BeliefFormError(:export_policy_certificate, nameof(typeof(problem.belief)),
                              "a certificate states exact numbers for a single finite " *
                              "prior"))
    Q = problem.payoff.Q[problem.feasible, :]
    p = problem.belief.probabilities
    L = experiment.likelihood
    size(L, 2) == length(p) ||
        throw(ArgumentError("the experiment has $(size(L, 2)) states and the problem " *
                            "$(length(p))"))
    _require_exact_entries("payoff", Q)
    _require_exact_entries("prior", p)
    _require_exact_entries("likelihood", L)
    c = (Q .// 1) * transpose(L .* permutedims(p))       # c[a, z]
    na, nz = size(c)
    dual = [maximum(view(c, :, z)) for z in 1:nz]
    π = if policy === nothing
        [a == findfirst(==(dual[z]), view(c, :, z)) ? 1 // 1 : 0 // 1
         for a in 1:na, z in 1:nz]
    else
        _require_exact_entries("policy", policy)
        size(policy) == (na, nz) ||
            throw(WitnessError("the policy is $(size(policy)); it needs one row per " *
                               "feasible action and one column per signal, ($na, $nz)"))
        policy .// 1
    end
    all(>=(0), π) && all(isone, sum(π; dims=1)) ||
        throw(WitnessError("the policy is not column-stochastic"))
    value = sum(dual)
    sum(π .* c) == value ||
        throw(WitnessError("the policy is not optimal: its objective is $(sum(π .* c)) " *
                           "and the optimum is $value"))
    text = string("{\n  \"schema\": \"", POLICY_CERTIFICATE_SCHEMA, "\",\n  \"payoff\": ",
                  _cert_matrix(Q), ",\n  \"prior\": ", _cert_vector(p),
                  ",\n  \"likelihood\": ", _cert_matrix(L), ",\n  \"policy\": ",
                  _cert_matrix(π), ",\n  \"dual\": ", _cert_vector(dual),
                  ",\n  \"value\": ", _cert_number(value), "\n}\n")
    return _write_text(dest, text)
end

function export_policy_certificate(dest, p::DecisionPipeline; policy=nothing)
    return export_policy_certificate(dest, decision_problem(p), observation_experiment(p);
                                     policy)
end

"""
    export_fidelity_chain_certificate(io_or_path, exact, approx; range, errors=nothing)

Write a `"fidelity-chain-certificate/1"` document: a chain of boxes on one finite
state space, each given as its exact kernel and the approximation that replaces it
(`exact` and `approx` are vectors of square column-stochastic matrices
`K[y, x] = P(y | x)`, first box first), a stated error for each box, the range `B`
of the payoffs and the loss bound `2 · B · Σ errors`.

The Lean checker accepts it exactly when every matrix is square of the same size
and column-stochastic, every stated error is at least the total-variation distance
between corresponding columns, the range is nonnegative and the bound is as stated.
Then (theorem `Certificate.RawFidelity.accepts_sound`) for every payoff table on
those states whose rows have range at most `B` and every prior on the input of the
first box, an action that is best for the belief pushed through the approximate
chain is within the bound of the best for the belief pushed through the exact
chain.

`errors` defaults to the exact distances ([`kernel_distance`](@ref)); larger stated
errors are allowed, smaller ones throw `WitnessError`. The matrices must be
normalised: a truncated emulator whose columns do not sum to one is refused, because
the additive bound is not the one proved for it. Entries that are not integers or
rationals throw `InexactCertificateError`. The schema covers chains on one state
space only; the bound that [`fidelity_bound`](@ref) reads off a general pipeline has
no certificate yet.
"""
function export_fidelity_chain_certificate(dest, exact::AbstractVector,
                                           approx::AbstractVector; range::Real,
                                           errors=nothing)
    length(exact) == length(approx) && !isempty(exact) ||
        throw(ArgumentError("give one approximate kernel per exact kernel, at least one"))
    n = size(first(exact), 1)
    for (what, Ks) in (("exact", exact), ("approximate", approx)), K in Ks
        _require_exact_entries("$what kernel", K)
        size(K) == (n, n) ||
            throw(WitnessError("every kernel of the chain must be $n × $n; one is " *
                               "$(size(K))"))
        all(>=(0), K) && all(isone, sum(K; dims=1)) ||
            throw(WitnessError("an $what kernel of the chain is not column-stochastic " *
                               "(the bound needs normalised boxes)"))
    end
    _require_exact_entries("range", range)
    range >= 0 || throw(ArgumentError("the range must be nonnegative, got $range"))
    actual = [kernel_distance(K, K′) for (K, K′) in zip(exact, approx)]
    stated = errors === nothing ? actual : collect(errors)
    length(stated) == length(actual) ||
        throw(ArgumentError("$(length(stated)) errors for $(length(actual)) boxes"))
    foreach(e -> _require_exact_entries("error", e), stated)
    all(stated .>= actual) ||
        throw(WitnessError("a stated error is smaller than the distance between the " *
                           "exact and the approximate kernel: $stated against $actual"))
    bound = decision_loss_bound(range, sum(stated))
    boxes = join(("    {\"exact\": " * _cert_matrix(K) * ",\n     \"approx\": " *
                  _cert_matrix(K′) * ",\n     \"error\": " * _cert_number(e) * "}"
                  for (K, K′, e) in zip(exact, approx, stated)), ",\n")
    text = string("{\n  \"schema\": \"", FIDELITY_CHAIN_CERTIFICATE_SCHEMA,
                  "\",\n  \"boxes\": [\n", boxes, "\n  ],\n  \"range\": ",
                  _cert_number(range), ",\n  \"bound\": ", _cert_number(bound), "\n}\n")
    return _write_text(dest, text)
end
