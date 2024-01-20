# max_coefs_pw = pw * 2 + 1

coefs_matrix_pw = pw-2
coefs_matrix_side = 2^(coefs_matrix_pw)
coefs_matrix_N = coefs_matrix_side * coefs_matrix_side

coefs = [rand(0:F-1) for i = 1:coefs_matrix_N]

# Test evaluating polynomial via a squared-size matrix:
powers_sq_fst = 1:coefs_matrix_side
plain_calc = dot_mod(coefs, ws[(0:(coefs_matrix_N-1)).%length(ws).+1], F)
coefs_sq = reshape(coefs, (coefs_matrix_side, coefs_matrix_side))
first_mul = [dot_mod(ws[powers_sq_fst], Vector(c), F) for c in eachcol(coefs_sq)]
powers_sq_snd = coefs_matrix_side*Vector(0:coefs_matrix_side-1).+1
sq_calc = dot_mod(first_mul, ws[(powers_sq_snd.-1).%length(ws).+1], F)
println(sq_calc == plain_calc)


function apply_fft_per_row(c)
    fft_(vcat(c, zeros(Int64, 3 * coefs_matrix_side)), ws)
end

codeword_matrix = transpose(hcat(apply_fft_per_row.(eachrow(coefs_sq))...))
column_merkle = fnv1a_merkle(fnv1a.(eachcol(codeword_matrix)))

# Proof doesn't include base index and root as they're assumed
# to be provided independently 
function merkle_proof(ix :: Int)
    ix = ix + N - 1
    ixs = []
    while ix != 1
        append!(ixs, ix ⊻ 1)
        ix >>= 1
    end
    reverse!(ixs)
    column_merkle[ixs]
end

function merkle_rebuild_root(ix :: Int64, el :: Int64, proof :: Vector{Int64})
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

merkle_rebuild_root(N, column_merkle[length(column_merkle)], merkle_proof(N))==commitment

# Prover sends
commitment = column_merkle[1]

# Verifier sends
r = [rand(0:F-1) for i = 1:coefs_matrix_side]

# Prover computes

# r_evaluated = [dot_mod(r, Vector(c), F) for c in eachcol(codeword_matrix)]
# r_evaluated_preimage = fft_(r_evaluated, iws) .* powermod(N, F-2, F) .% F
# println(r_evaluated_preimage[coefs_matrix_side+1:N]==zeros(Int64, coefs_matrix_side*3))
# r_evaluated_preimage = r_evaluated_preimage[1:coefs_matrix_side]
r_evaluated_preimage = [dot_mod(r, Vector(c), F) for c in eachcol(coefs_sq)]

# Verifier sends
col_ixs = [rand(1:N) for i=1:4]

# Prover sends
col_proofs = merkle_proof.(col_ixs)
cols = codeword_matrix[:,col_ixs]

# Verifier computes
for (ix, col, proof) in zip(col_ixs, eachcol(cols), col_proofs)
    assumed_root = merkle_rebuild_root(ix, fnv1a(col), proof)
    if assumed_root != commitment
        error("wrong merkle proof")
    end
end
r_evaluated_ver = fft_(vcat(r_evaluated_preimage, zeros(Int64, 3*coefs_matrix_side)), ws)
if r_evaluated_ver[col_ixs] != [dot_mod(r, Vector(c), F) for c in eachcol(cols)]
    error("wrong codeword-based evaluation")
end

# At this point we verified commitment to the polynomial, time to evaluate at some point?
some_point = rand(0:F-1)
some_point_powers = [powermod(some_point, i, F) for i = 0:coefs_matrix_N-1]
some_point_eval_expected = dot_mod(some_point_powers, coefs, F)

# Verifier sends

some_point

# Prover sends

some_point_pre_eval = [dot_mod(some_point_powers[powers_sq_fst], Vector(c), F) for c in eachcol(coefs_sq)]

# Verifier computes
some_point_pre_eval_fft = fft_(vcat(r_evaluated_preimage, zeros(Int64, 3*coefs_matrix_side)), ws)
if some_point_pre_eval_fft[col_ixs] != [dot_mod(r, Vector(c), F) for c in eachcol(cols)]
    error("wrong codeword-based evaluation of the point")
end

some_point_eval = dot_mod(some_point_pre_eval, some_point_powers[powers_sq_snd], F)

print(some_point_eval == some_point_eval_expected)