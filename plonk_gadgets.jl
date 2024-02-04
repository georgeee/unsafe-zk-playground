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
    fss, (evals, subres), points = poly_commit_1_verify(proof, plonk_p1c_columns_to_check, fiat_shamir_state, sub_verify)
    computed_dividend_eval = evals[1] * eval_poly(divisor, points[1], F) % F
    fss, (computed_dividend_eval, subres), points
end

function quotient_existence_with_dividend_commit_prove(dividend::Vector{Int64}, divisor::Vector{Int64}, fss::Int64, sub_prove)
    fss, (p1cp, (qp, subp)), ps = poly_commit_1_prove(dividend, plonk_p1c_columns_to_check, fss, (fss) -> begin
        quotient_existence_prove(dividend, divisor, fss, sub_prove)
    end)
    fss, ((p1cp, qp)::Tuple{PolyCommit1Proof,QuotinentExistenceProof}, subp), ps
end

# Commits to dividend and proves that quotient exists (dividend = quotient * divisor)
# Returns evaluations of the dividend polynomial at points specified by the `sub_verify`
function quotient_existence_with_dividend_commit_verify(proof::Tuple{PolyCommit1Proof,QuotinentExistenceProof}, divisor::Vector{Int64}, fss::Int64, sub_verify)
    p1c_proof, qproof = proof
    fss, (evals, (computed_eval, subresult)), points = poly_commit_1_verify(p1c_proof, plonk_p1c_columns_to_check, fss, (fss) -> begin
        quotient_existence_verify(qproof, divisor, fss, sub_verify)
    end)
    if evals[1] != computed_eval
        error("wasn't able to verify quotient existence proof")
    end
    fss, (evals, subresult), points
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


# for product check lagrange interpolation is required

# Product check
#
# For dividend polynomial `f` and divisor polynomial `g`, prove that `∏(f(x)/g(x))` over all `x` in roots of unity group `lws`
# equals to `1`.
# Commits to `f` and `g` as part of the proof.
function product_of_fraction_prove(f::Vector{Int64}, g::Vector{Int64}, fss::Int64, sub_prove)
    t_eval_acc_f = (acc, lwi) -> begin
        num = eval_poly(f, lwi, F)
        den = eval_poly(g, lwi, F)
        acc * (num * invmod(den, F) % F) % F
    end
    # Build the t(x) polynomial
    t_evals = foldl(t_eval_acc_f, lws; init=1)
    t = lagrange_interpolate(lagrange_polys, t_evals)
    t2 = poly_mul(scale_x(t, lws[2]), scale_x(g, lws[2]))
    t3 = poly_mul(t, scale_x(f, lws[2]))
    t1 = poly_div(t2, t3)
    lw = lws[2]

    poly_commit_1_prove(f, plonk_p1c_columns_to_check, fss, (fss) -> begin
        fss, gproof, ps = poly_commit_1_prove(g, plonk_p1c_columns_to_check, fss, (fss) -> begin
            fss, tproof, ps = poly_commit_1_prove(t, plonk_p1c_columns_to_check, fss, (fss) -> begin
                fss, t1proof, ps = quotient_existence_with_dividend_commit_prove(t1, l_vanishing, fss, sub_prove)
                fss, t1proof, vcat(ps, [lws[end], ps[1] * lw % F])
            end)
            fss, tproof, vcat(ps, [ps[1] * lw % F])
        end)
        fss, gproof, vcat(ps, [ps[1] * lw % F])
    end)
end

function product_of_fraction_verify(proof, fss, sub_verify)
    (fproof, (gproof, (tproof, (t1proof, subp)))) = proof
    

# return evaluation of f(r)/g(r) at random r    
end

# Prescribed permutation check