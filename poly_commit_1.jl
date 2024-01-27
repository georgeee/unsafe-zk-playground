using Random
using Test
include("fft.jl")
include("fnv.jl")
include("polynomial.jl")

# Implements polynomial commitment scheme as described in Zk Mooc class
# A.k.a. Shockwave (originally introduced by 2021/1043 eprint, GLSTW'21)

# max_coefs_pw = pw * 2 + 1

coefs_matrix_pw = pw - 2
coefs_matrix_side = 2^(coefs_matrix_pw)
coefs_matrix_N = coefs_matrix_side * coefs_matrix_side
powers_sq_fst = 1:coefs_matrix_side
powers_sq_snd = coefs_matrix_side * Vector(0:coefs_matrix_side-1) .+ 1

function test_sq_matrix_eval()
    # Test evaluating polynomial via a squared-size matrix:
    coefs = [rand(0:F-1) for _ = 1:coefs_matrix_N]
    plain_calc = dot_mod(coefs, ws[(0:(coefs_matrix_N-1)).%length(ws).+1], F)
    coefs_sq = reshape(coefs, (coefs_matrix_side, coefs_matrix_side))
    first_mul = [dot_mod(ws[powers_sq_fst], Vector(c), F) for c in eachcol(coefs_sq)]
    sq_calc = dot_mod(first_mul, ws[(powers_sq_snd.-1).%length(ws).+1], F)
    (sq_calc == plain_calc)
end

test_sq_matrix_eval()

function apply_fft_per_row(c)
    fft(vcat(c, zeros(Int64, 3 * coefs_matrix_side)), ws)
end

# Proof doesn't include base index and root as they're assumed
# to be provided independently 
function merkle_proof_ixs(ix::Int)
    ix = ix + N - 1
    ixs = []
    while ix != 1
        append!(ixs, ix ⊻ 1)
        ix >>= 1
    end
    reverse!(ixs)
end

function merkle_rebuild_root(ix::Int64, el::Int64, proof::Vector{Int64})
    ix = ix + N - 1
    for sibling in reverse(proof)
        if ix & 1 > 0
            el = fnv1a(sibling, el)
        else
            el = fnv1a(el, sibling)
        end
        ix >>= 1
    end
    el
end

# merkle_rebuild_root(N, column_merkle[length(column_merkle)], column_merkle[merkle_proof_ixs(N)])==commitment

struct PolyCommit1Proof
    # commitment fields
    commitment::Int64 # merkle root of a commitment to vector of columns
    r_evaluated::Vector{Int64} # multiplication of a random vector and coeficient matrix
    columns::Matrix{Int64} # select codeword matrix columns
    column_proofs::Vector{Vector{Int64}} # merkle proofs of columns above

    # evaluation at a random point
    random_point_evaluated::Vector{Int64}

    # evaluation at auxiliary points
    auxiliary_points_evaluated::Vector{Vector{Int64}}
end

function simulate_poly_commit_1(columns_to_check::Int)
    coefs = rand(0:F-1, coefs_matrix_N)
    coefs_sq = reshape(coefs, (coefs_matrix_side, coefs_matrix_side))
    codeword_matrix = transpose(hcat(apply_fft_per_row.(eachrow(coefs_sq))...))
    column_merkle = fnv1a_merkle(fnv1a.(eachcol(codeword_matrix)))

    # Prover sends
    commitment = column_merkle[1]

    # Verifier sends
    r = rand(0:F-1, coefs_matrix_side)

    # Prover computes
    r_evaluated = [dot_mod(r, Vector(c), F) for c in eachcol(coefs_sq)]

    # Verifier sends
    col_ixs = rand(1:N, columns_to_check)

    # Prover sends
    col_proofs = map(ixs -> column_merkle[ixs], merkle_proof_ixs.(col_ixs))
    cols = codeword_matrix[:, col_ixs]

    # Verifier computes
    for (ix, col, proof) in zip(col_ixs, eachcol(cols), col_proofs)
        assumed_root = merkle_rebuild_root(ix, fnv1a(col), proof)
        if assumed_root != commitment
            error("wrong merkle proof")
        end
    end
    r_evaluated_ver = fft(vcat(r_evaluated, zeros(Int64, 3 * coefs_matrix_side)), ws)
    if r_evaluated_ver[col_ixs] != [dot_mod(r, Vector(c), F) for c in eachcol(cols)]
        error("wrong codeword-based evaluation")
    end

    # At this point we verified commitment to the polynomial, time to evaluate at some point?
    some_point = rand(0:F-1)

    # Verifier sends

    some_point

    # Prover computes
    some_point_powers = [powermod(some_point, i, F) for i = 0:coefs_matrix_N-1]

    # Prover sends
    some_point_pre_eval = [dot_mod(some_point_powers[powers_sq_fst], Vector(c), F) for c in eachcol(coefs_sq)]

    # Verifier computes
    some_point_pre_eval_fft = fft(vcat(some_point_pre_eval, zeros(Int64, 3 * coefs_matrix_side)), ws)
    if some_point_pre_eval_fft[col_ixs] != [dot_mod(some_point_powers[powers_sq_fst], Vector(c), F) for c in eachcol(cols)]
        error("wrong codeword-based evaluation of the point")
    end

    some_point_eval = dot_mod(some_point_pre_eval, some_point_powers[powers_sq_snd], F)

    some_point_eval == dot_mod(some_point_powers, coefs, F)
end

@test simulate_poly_commit_1(4)

function poly_commit_1_preevaluate(point::Int64, matrix::Matrix{Int64})
    point_powers = [powermod(point, i, F) for i = 0:(size(matrix, 2)-1)]
    [dot_mod(point_powers, Vector(c), F) for c in eachcol(matrix)]
end

function seed_of_fiat_shamir(fiat_shamir_state)
    Random.Xoshiro(abs(fiat_shamir_state))
end

function extend_fiat_shamir(fiat_shamir_state :: Int64, new_data :: Vector{Int64})
    fnv1a(new_data, fiat_shamir_state)
end

function poly_commit_1_prove(coefs::Vector{Int64}, columns_to_check::Int, fiat_shamir_state :: Int64, handler)
    coefs_sq = reshape(coefs, (coefs_matrix_side, coefs_matrix_side))
    codeword_matrix = transpose(hcat(apply_fft_per_row.(eachrow(coefs_sq))...))
    column_merkle = fnv1a_merkle(fnv1a.(eachcol(codeword_matrix)))

    # Prover sends
    commitment = column_merkle[1]

    fiat_shamir_state = extend_fiat_shamir(fiat_shamir_state, [commitment])

    # Verifier sends
    r = rand(seed_of_fiat_shamir(fiat_shamir_state), 0:F-1, coefs_matrix_side)

    # Prover computes
    r_evaluated = [dot_mod(r, Vector(c), F) for c in eachcol(coefs_sq)]

    fiat_shamir_state = extend_fiat_shamir(fiat_shamir_state, vcat(r, r_evaluated))

    # Verifier sends
    col_ixs = rand(seed_of_fiat_shamir(fiat_shamir_state), 1:N, columns_to_check)

    # Prover sends
    col_proofs = map(ixs -> column_merkle[ixs], merkle_proof_ixs.(col_ixs))
    cols = codeword_matrix[:, col_ixs]

    # Verifier computes some stuff...

    fiat_shamir_state = extend_fiat_shamir(fiat_shamir_state, vcat(col_ixs, reduce(vcat, cols), reduce(vcat, col_proofs)))

    fiat_shamir_state, subproof, aux_points = handler(fiat_shamir_state)

    # Verifier sends
    rand_point = rand(seed_of_fiat_shamir(fiat_shamir_state), 0:F-1)

    # Prover sends
    rand_point_preeval = poly_commit_1_preevaluate(rand_point, coefs_sq)
    aux_point_preevals = Vector{Vector{Int64}}([poly_commit_1_preevaluate(p, coefs_sq) for p in aux_points])

    logs = vcat([rand_point], rand_point_preeval, reduce(vcat, aux_point_preevals; init=Vector{Int64}([])))

    fiat_shamir_state = extend_fiat_shamir(fiat_shamir_state, logs)

    PolyCommit1Proof(commitment, r_evaluated, cols, col_proofs, rand_point_preeval, aux_point_preevals), subproof, fiat_shamir_state
end


function poly_commit_1_evaluate(col_ixs, cols, p, preeval)
    powers = [powermod(p, i, F) for i = 0:(coefs_matrix_N-1)]
    preeval_fft = fft(vcat(preeval, zeros(Int64, 3 * coefs_matrix_side)), ws)
    if preeval_fft[col_ixs] != [dot_mod(powers[powers_sq_fst], Vector(c), F) for c in eachcol(cols)]
        error("wrong codeword-based evaluation of the point")
    end
    dot_mod(preeval, powers[powers_sq_snd], F)
end

# Verifies poly-commit-1 proof and extracts the evaluation
function poly_commit_1_verify(proof :: PolyCommit1Proof, columns_to_check::Int, fiat_shamir_state :: Int64, subproof, handler)
    # Prover sends
    commitment = proof.commitment

    fiat_shamir_state = extend_fiat_shamir(fiat_shamir_state, [commitment])
    # Verifier sends
    r = rand(seed_of_fiat_shamir(fiat_shamir_state), 0:F-1, coefs_matrix_side)

    # Prover computes
    r_evaluated = proof.r_evaluated

    fiat_shamir_state = extend_fiat_shamir(fiat_shamir_state, vcat(r, r_evaluated))
    # Verifier sends
    col_ixs = rand(seed_of_fiat_shamir(fiat_shamir_state), 1:N, columns_to_check)

    # Prover sends
    col_proofs = proof.column_proofs
    cols = proof.columns

    # Verifier computes
    for (ix, col, proof) in zip(col_ixs, eachcol(cols), col_proofs)
        assumed_root = merkle_rebuild_root(ix, fnv1a(col), proof)
        if assumed_root != commitment
            error("wrong merkle proof")
        end
    end
    r_evaluated_ver = fft(vcat(r_evaluated, zeros(Int64, 3 * coefs_matrix_side)), ws)
    if r_evaluated_ver[col_ixs] != [dot_mod(r, Vector(c), F) for c in eachcol(cols)]
        error("wrong codeword-based evaluation")
    end

    fiat_shamir_state = extend_fiat_shamir(fiat_shamir_state, vcat(col_ixs, reduce(vcat, cols), reduce(vcat, col_proofs)))

    fiat_shamir_state, subresult, aux_points = handler(subproof, fiat_shamir_state)

    # Verifier sends
    rand_point = rand(seed_of_fiat_shamir(fiat_shamir_state), 0:F-1)

    logs = vcat([rand_point], proof.random_point_evaluated, reduce(vcat, proof.auxiliary_points_evaluated; init=Vector{Int64}([])))
    fiat_shamir_state = extend_fiat_shamir(fiat_shamir_state, logs)

    # Prover sends
    rand_eval = poly_commit_1_evaluate(col_ixs, cols, rand_point, proof.random_point_evaluated)
    aux_evals = map((p, pr) -> poly_commit_1_evaluate(col_ixs, cols, p, pr), aux_points, proof.auxiliary_points_evaluated)

    # Verifier computes
    rand_point, rand_eval, aux_evals, subresult, fiat_shamir_state
end

function poly_commit_1_prove_(coefs::Vector{Int64}, columns_to_check::Int)
    poly_commit_1_prove(coefs, columns_to_check, 0, (fss) -> (fss, nothing, []))
end

function poly_commit_1_verify_(proof :: PolyCommit1Proof, columns_to_check::Int)
    poly_commit_1_verify(proof, columns_to_check, 0, nothing, (subproof, fss) -> (fss, nothing, []))
end

function poly_commit_1_proof_verify_check(coefs::Vector{Int64}, columns_to_check::Int)
    point = rand(0:F-1)
    eval = eval_poly(coefs, point, F)
    proof, subproof, fss = poly_commit_1_prove(coefs, columns_to_check, 0, (fss) -> (fss, nothing, [point]))
    _, _, evaluated, _ = poly_commit_1_verify(proof, columns_to_check, 0, subproof, (subproof, fss) -> (fss, nothing, [point]))
    evaluated == [eval]
end

@test poly_commit_1_proof_verify_check(rand(0:F-1, coefs_matrix_N), 4)