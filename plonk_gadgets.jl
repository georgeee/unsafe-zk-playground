include("polynomial.jl")
include("lagrange.jl")
include("poly_commit_1.jl")

plonk_p1c_columns_to_check = 4

const QuotinentExistenceProof = PolyCommit1Proof # commitment to quotient polynomial
const QuotinentExistenceResult = Int64 # computed evaluation of dividend polynomial at a random point

function quotient_existence_prove(dividend::Vector{Int64}, divisor::Vector{Int64}, fiat_shamir_state::Int64, sub_prove)
    quotient = poly_div(dividend, divisor)
    remainder = poly_sub(dividend, poly_mul(quotient, divisor))
    if remainder != []
        error("Remainder is not zero")
    end
    poly_commit_1_prove(quotient, plonk_p1c_columns_to_check, fiat_shamir_state, sub_prove)
end

function quotient_existence_verify(proof, divisor::Vector{Int64}, fiat_shamir_state::Int64, sub_verify)
    fss, (rand_eval, _, subres), rand_point = poly_commit_1_verify(proof, plonk_p1c_columns_to_check, fiat_shamir_state, sub_verify)
    computed_dividend_eval = rand_eval * eval_poly(divisor, rand_point, F) % F
    fss, (computed_dividend_eval, subres), PolyCommitPoints(rand_point, [])
end

function quotient_existence_with_dividend_commit_prove(dividend::Vector{Int64}, divisor::Vector{Int64}, fss::Int64, sub_prove)
    fss, (p1cp, (qp, subp)), ps = poly_commit_1_prove(dividend, plonk_p1c_columns_to_check, fss, (fss) -> begin
        quotient_existence_prove(dividend, divisor, fss, sub_prove)
    end)
    fss, ((p1cp, qp)::Tuple{PolyCommit1Proof,QuotinentExistenceProof}, subp), ps
end

# Commits to dividend and proves that quotient exists (dividend = quotient * divisor)
# Returns evaluation of the dividend polynomial at a random point
function quotient_existence_with_dividend_commit_verify(proof::Tuple{PolyCommit1Proof,QuotinentExistenceProof}, divisor::Vector{Int64}, fss::Int64, sub_verify)
    p1c_proof, qproof = proof
    fss, (rand_eval, _, (computed_eval, subresult)), rand_point = poly_commit_1_verify(p1c_proof, plonk_p1c_columns_to_check, fss, (fss) -> begin
        quotient_existence_verify(qproof, divisor, fss, sub_verify)
    end)
    if rand_eval != computed_eval
        error("wasn't able to verify quotient existence proof")
    end
    fss, (rand_eval, subresult), PolyCommitPoints(rand_point, [])
end

function quotient_existence_prove_verify_test(divisor, quotient)
    dividend = poly_mul(divisor, quotient)
    _, (proof, nothing), _ = quotient_existence_with_dividend_commit_prove(dividend, divisor, 0, fss_rand_point)
    _, (_, nothing), _ = quotient_existence_with_dividend_commit_verify(proof, divisor, 0, fss_rand_point)
    return true
end

@test quotient_existence_prove_verify_test(rand(0:F-1, div(N_halved, 4)), rand(0:F-1, 3 * div(N_halved, 4)))

# TODO zero-test on all points in ws
# TODO zero-test on certain points
# TODO zero-test on nearly all points in ws (minus a small subset)


const ProductOfFractionProof = Tuple{PolyCommit1Proof,PolyCommit1Proof,PolyCommit1Proof,Tuple{PolyCommit1Proof,QuotinentExistenceProof}}

# Product check
#
# For dividend polynomial `f` and divisor polynomial `g`, prove that `∏(f(x)/g(x))` over all `x` in roots of unity group `lws`
# equals to `1`.
# Commits to `f` and `g` as part of the proof.
function product_of_fraction_prove(f::Vector{Int64}, g::Vector{Int64}, fss::Int64, sub_prove)
    t_eval_acc_f = (acc, lwi) -> begin
        acc_ = 1
        if length(acc) > 0
            acc_ = last(acc)
        end
        num = eval_poly(f, lwi, F)
        den = eval_poly(g, lwi, F)
        val = acc_ * (num * invmod(den, F) % F) % F
        append!(acc, val)
    end
    # Build the t(x) polynomial
    t_evals = foldl(t_eval_acc_f, lws; init=Vector{Int64}())
    if last(t_evals) != 1
        error("Product of fractions is not equal to 1")
    end
    t = lagrange_interpolate(lagrange_polys, t_evals)
    t2 = poly_mul(scale_x(t, lws[2]), scale_x(g, lws[2]))
    t3 = poly_mul(t, scale_x(f, lws[2]))
    t1 = poly_sub(t2, t3)
    lw = lws[2]

    fss, (fproof, (gproof, (tproof, (t1proof, subp)))), ps = poly_commit_1_prove(f, plonk_p1c_columns_to_check, fss, (fss) -> begin
        fss, gproof, ps = poly_commit_1_prove(g, plonk_p1c_columns_to_check, fss, (fss) -> begin
            fss, tproof, ps = poly_commit_1_prove(t, plonk_p1c_columns_to_check, fss, (fss) -> begin
                fss, t1proof, ps = quotient_existence_with_dividend_commit_prove(t1, l_vanishing, fss, sub_prove)
                fss, t1proof, append_aux!(ps, r -> [lws[end], r * lw % F])
            end)
            fss, tproof, append_aux!(ps, r -> [r * lw % F])
        end)
        fss, gproof, append_aux!(ps, r -> [r * lw % F])
    end)
    fss, ((fproof, gproof, tproof, t1proof)::ProductOfFractionProof, subp), ps
end

function product_of_fraction_verify(proof::ProductOfFractionProof, fss::Int64, sub_verify)
    (fproof, gproof, tproof, t1proof) = proof
    lw = lws[2]
    # fiat_shamir_state, (rand_eval, aux_evals, subresult), points.rand_point
    fss, (f_at_r, f_evals, (g_evals, t_evals, subres)), r = poly_commit_1_verify(fproof, plonk_p1c_columns_to_check, fss, (fss) -> begin
        fss, (g_at_r, g_evals, (t_evals, subres)), r = poly_commit_1_verify(gproof, plonk_p1c_columns_to_check, fss, (fss) -> begin
            fss, (t_at_r, t_aux_evals, (t1_eval_at_r, subres)), r = poly_commit_1_verify(tproof, plonk_p1c_columns_to_check, fss, (fss) -> begin
                fss, (t1_eval_at_r, subres), ps = quotient_existence_with_dividend_commit_verify(t1proof, l_vanishing, fss, sub_verify)
                fss, (t1_eval_at_r, subres), append_aux!(ps, r -> [lws[end], r * lw % F])
            end)
            t_at_last_lw, t_at_r_lw = t_aux_evals[1], t_aux_evals[2]
            if t_at_last_lw != 1
                error("t(w^{k-1}) != 1")
            end
            fss, ((t_at_r, t_at_r_lw, t1_eval_at_r), subres), PolyCommitPoints(r, [r * lw % F])
        end)
        g_at_r_lw = g_evals[1]
        fss, ((g_at_r, g_at_r_lw), t_evals, subres), PolyCommitPoints(r, [r * lw % F])
    end) 
    f_at_r_lw = f_evals[1]
    (g_at_r, g_at_r_lw), (t_at_r, t_at_r_lw, t1_eval_at_r) = g_evals, t_evals
    t1_at_r_computed = (t_at_r_lw * g_at_r_lw % F - t_at_r * f_at_r_lw % F + F) % F
    if t1_at_r_computed != t1_eval_at_r
        error("t1(r) != t(wr)g(wr)-t(r)f(wr)")
    end
    fss, (f_at_r * invmod(g_at_r, F) % F, subres), r
end


function product_of_fraction_verify_check()
    n = div(N_halved, 16)
    g, g_evals = [], [0]
    while !isnothing(findfirst(x -> x == 0, g_evals))
        g = rand(0:F-1, n)
        g_evals = [eval_poly(g, lwi, F) for lwi in lws]
    end
    f_evals = shuffle(g_evals)
    f = lagrange_interpolate(lagrange_polys, f_evals)
    _, (proof, nothing), _ = product_of_fraction_prove(f, g, 0, fss_rand_point)
    _, (_, nothing), _ = product_of_fraction_verify(proof, 0, fss_rand_point)
    return true
end

@test product_of_fraction_verify_check()

# Prescribed permutation check