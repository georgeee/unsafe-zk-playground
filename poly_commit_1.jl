using Random
using Test
include("fft.jl")
include("fnv.jl")
include("polynomial.jl")

# Implements polynomial commitment scheme as described in Zk Mooc class
# A.k.a. Shockwave (originally introduced by 2021/1043 eprint, GLSTW'21)

# max_coefs_pw = pw * 2 + 1

# How many field elements are added as part of Reed-Solomon code to each field element of the message
# For value `x`, `2^x - 1` is the number of added elements
rs_blowup_pw = 2
rs_blowup = 2^rs_blowup_pw - 1

coefs_matrix_pw = 6
coefs_matrix_side = 2^(coefs_matrix_pw)
coefs_matrix_N = coefs_matrix_side * coefs_matrix_side
powers_sq_fst = 1:coefs_matrix_side
powers_sq_snd = coefs_matrix_side * Vector(0:coefs_matrix_side-1) .+ 1

p1c_ws = ws[1:(2^(pw - coefs_matrix_pw - rs_blowup_pw)):end]

function test_sq_matrix_eval()
    # Test evaluating polynomial via a squared-size matrix:
    coefs = [rand(0:F-1) for _ = 1:coefs_matrix_N]
    plain_calc = dot_mod(coefs, p1c_ws[(0:(coefs_matrix_N-1)).%length(p1c_ws).+1], F)
    coefs_sq = reshape(coefs, (coefs_matrix_side, coefs_matrix_side))
    first_mul = [dot_mod(p1c_ws[powers_sq_fst], Vector(c), F) for c in eachcol(coefs_sq)]
    sq_calc = dot_mod(first_mul, p1c_ws[(powers_sq_snd.-1).%length(p1c_ws).+1], F)
    (sq_calc == plain_calc)
end

@test test_sq_matrix_eval()

# Proof doesn't include base index and root as they're assumed
# to be provided independently 
function merkle_proof_ixs(ix::Int)
    ix = ix + length(p1c_ws) - 1
    ixs = []
    while ix != 1
        append!(ixs, ix ⊻ 1)
        ix >>= 1
    end
    reverse!(ixs)
end

function merkle_rebuild_root(ix::Int64, el::Int64, proof::Vector{Int64})
    ix = ix + length(p1c_ws) - 1
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

struct PolyCommit1Proof
    # commitment fields
    commitment::Int64 # merkle root of a commitment to vector of columns
    r_evaluated::Vector{Int64} # multiplication of a random vector and coeficient matrix
    columns::Matrix{Int64} # select codeword matrix columns
    column_proofs::Vector{Vector{Int64}} # merkle proofs of columns above

    # pre-evaluation at points
    points_preevaluated::Vector{Vector{Int64}}
end

# TODO consider replacing use of reduce(vcat, ...) with a safer approach (e.g. a foldl/foldr)

function simulate_poly_commit_1(columns_to_check::Int)
    coefs = rand(0:F-1, coefs_matrix_N)
    coefs_sq = reshape(coefs, (coefs_matrix_side, coefs_matrix_side))

    apply_fft_per_row = (c) -> fft(vcat(c, zeros(Int64, rs_blowup * coefs_matrix_side)), p1c_ws)
    codeword_matrix = transpose(hcat(apply_fft_per_row.(eachrow(coefs_sq))...))
    column_merkle = fnv1a_merkle(fnv1a.(eachcol(codeword_matrix)))

    # Prover sends
    commitment = column_merkle[1]

    # Verifier sends
    r = rand(0:F-1, coefs_matrix_side)

    # Prover computes
    r_evaluated = [dot_mod(r, Vector(c), F) for c in eachcol(coefs_sq)]

    # Verifier sends
    col_ixs = rand(1:length(p1c_ws), columns_to_check)

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
    r_evaluated_ver = fft(vcat(r_evaluated, zeros(Int64, 3 * coefs_matrix_side)), p1c_ws)
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
    some_point_pre_eval_fft = fft(vcat(some_point_pre_eval, zeros(Int64, 3 * coefs_matrix_side)), p1c_ws)
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

function poly_commit_1_prove(coefs::Vector{Int64}, columns_to_check::Int, fiat_shamir_state :: Int64, sub_prove)
    coefs = vcat(coefs, zeros(Int64, coefs_matrix_N - length(coefs)))
    coefs_sq = reshape(coefs, (coefs_matrix_side, coefs_matrix_side))
    
    apply_fft_per_row = (c) -> fft(vcat(c, zeros(Int64, rs_blowup * coefs_matrix_side)), p1c_ws)
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
    col_ixs = rand(seed_of_fiat_shamir(fiat_shamir_state), 1:length(p1c_ws), columns_to_check)

    # Prover sends
    col_proofs = map(ixs -> column_merkle[ixs], merkle_proof_ixs.(col_ixs))
    cols = codeword_matrix[:, col_ixs]

    # Verifier computes some stuff...

    fiat_shamir_state = extend_fiat_shamir(fiat_shamir_state, vcat(col_ixs, reduce(vcat, cols), reduce(vcat, col_proofs)))

    fiat_shamir_state, subproof, points = sub_prove(fiat_shamir_state)

    # Verifier sent points 

    # Prover sends
    point_preevals = Vector{Vector{Int64}}([poly_commit_1_preevaluate(p, coefs_sq) for p in points])

    logs = reduce(vcat, point_preevals; init=Vector{Int64}([]))
    fiat_shamir_state = extend_fiat_shamir(fiat_shamir_state, logs)

    fiat_shamir_state, (PolyCommit1Proof(commitment, r_evaluated, cols, col_proofs, point_preevals), subproof), points
end


function poly_commit_1_evaluate(col_ixs, cols, p, preeval)
    powers = [powermod(p, i, F) for i = 0:(coefs_matrix_N-1)]
    preeval_fft = fft(vcat(preeval, zeros(Int64, 3 * coefs_matrix_side)), p1c_ws)
    if preeval_fft[col_ixs] != [dot_mod(powers[powers_sq_fst], Vector(c), F) for c in eachcol(cols)]
        error("wrong codeword-based evaluation of the point")
    end
    dot_mod(preeval, powers[powers_sq_snd], F)
end

# Verifies poly-commit-1 proof and extracts the evaluation
function poly_commit_1_verify(proof :: PolyCommit1Proof, columns_to_check::Int, fiat_shamir_state :: Int64, sub_verify)
    # Prover sends
    commitment = proof.commitment

    fiat_shamir_state = extend_fiat_shamir(fiat_shamir_state, [commitment])
    # Verifier sends
    r = rand(seed_of_fiat_shamir(fiat_shamir_state), 0:F-1, coefs_matrix_side)

    # Prover computes
    r_evaluated = proof.r_evaluated

    fiat_shamir_state = extend_fiat_shamir(fiat_shamir_state, vcat(r, r_evaluated))
    # Verifier sends
    col_ixs = rand(seed_of_fiat_shamir(fiat_shamir_state), 1:length(p1c_ws), columns_to_check)

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
    r_evaluated_ver = fft(vcat(r_evaluated, zeros(Int64, 3 * coefs_matrix_side)), p1c_ws)
    if r_evaluated_ver[col_ixs] != [dot_mod(r, Vector(c), F) for c in eachcol(cols)]
        error("wrong codeword-based evaluation")
    end

    fiat_shamir_state = extend_fiat_shamir(fiat_shamir_state, vcat(col_ixs, reduce(vcat, cols), reduce(vcat, col_proofs)))

    fiat_shamir_state, subresult, points = sub_verify(fiat_shamir_state)

    # Verifier sent points 

    logs = reduce(vcat, proof.points_preevaluated; init=Vector{Int64}([]))
    fiat_shamir_state = extend_fiat_shamir(fiat_shamir_state, logs)

    # Prover sends
    evals = map((p, pr) -> poly_commit_1_evaluate(col_ixs, cols, p, pr), points, proof.points_preevaluated)

    # Verifier computes
    fiat_shamir_state, (evals, subresult), points
end

function fss_rand_point(fiat_shamir_state, aux_points = [])
    rand_point = rand(seed_of_fiat_shamir(fiat_shamir_state), 0:F-1)
    points = [rand_point]
    append!(points, aux_points)
    fiat_shamir_state = extend_fiat_shamir(fiat_shamir_state, points)
    (fiat_shamir_state, nothing, points)
end

# TODO document the nested commit convention (e.g. that the points are returned)
# Points are append to the end of the list and removed subsequently. The first point is always a random field element.

function poly_commit_1_proof_verify_check(coefs::Vector{Int64}, columns_to_check::Int)
    point = rand(0:F-1)
    eval = eval_poly(coefs, point, F)
    _, (proof, _), _ = poly_commit_1_prove(coefs, columns_to_check, point, (fss) -> fss_rand_point(fss, [point]))
    _, (evaluated, _), _ = poly_commit_1_verify(proof, columns_to_check, point, (fss) -> fss_rand_point(fss, [point]))
    evaluated[2] == eval
end

@test poly_commit_1_proof_verify_check(rand(0:F-1, coefs_matrix_N), 4)