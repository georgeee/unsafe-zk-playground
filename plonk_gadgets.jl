# Zero Test

function quotient_existence_prove(dividend::Vector{Int64}, divisor::Vector{Int64}, fiat_shamir_state::Int64, random_point::Int64)
    quotient = poly_div(dividend, divisor)
    remainder = poly_sub(dividend, poly_mul(quotient, divisor))
    if remainder != []
        error("Remainder is not zero")
    end
    proof, _, fiat_shamir_state = poly_commit_1_prove(quotient, 4, fiat_shamir_state, (fss) -> (fss, nothing, [random_point]))
    proof, fiat_shamir_state
end

function quotient_existence_verify(proof, divisor::Vector{Int64}, fiat_shamir_state::Int64, random_point::Int64)
    evals, _, fiat_shamir_state = poly_commit_1_verify(proof, 4, fiat_shamir_state, (fss) -> (fss, nothing, [random_point]))
    computed_dividend_eval = evals[1] * eval_poly(divisor, random_point, F) % F
    computed_dividend_eval, fiat_shamir_state
end

function quotient_existence_prove_verify_test(divisor, quotient)
    dividend = poly_mul(divisor, quotient)
    proof, subproof, _ = poly_commit_1_prove(dividend, 4, 0, function (fss)
        rand_point = rand(seed_of_fiat_shamir(fss), 0:F-1)
        fss = extend_fiat_shamir(fss, [rand_point])
        subproof, fss = quotient_existence_prove(dividend, divisor, fss, rand_point)
        (fss, subproof, [rand_point])
    end)
    evals, computed_eval, _ = poly_commit_1_verify(proof, 4, 0, function (fss)
        rand_point = rand(seed_of_fiat_shamir(fss), 0:F-1)
        fss = extend_fiat_shamir(fss, [rand_point])
        eval, fss = quotient_existence_verify(subproof, divisor, fss, rand_point)
        (fss, eval, [rand_point])
    end)
    evals == [computed_eval]
end

@test quotient_existence_prove_verify_test(rand(0:F-1, div(N_halved, 4)), rand(0:F-1, 3*div(N_halved, 4)))

# TODO zero-test on all points in ws
# TODO zero-test on certain points
# TODO zero-test on nearly all points in ws (minus a small subset)


# for product check lagrange interpolation is required

# Product check
#
# For dividend polynomial `f` and divisor polynomial `g`, prove that `∏(f(x)/g(x))` over all `x` in group induced by k-th root of unity `w`
# equals to `1`
function product_of_division_check_prove(dividend::Vector{Int64}, divisor::Vector{Int64}, w :: Int64, k :: Int, fiat_shamir_state::Int64, random_point::Int64) {
    # Build the t(x) polynomial
    
}

# Prescribed permutation check