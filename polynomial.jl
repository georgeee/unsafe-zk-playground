include("field.jl")
include("fft.jl")
using Test

# Polynomial division in field F

# TODO for polynomials: multiplication, division, multiplication of 'x' by a constant factor

function eval_poly(poly::Vector{Int64}, point::Int64, F::Int64)
    dot_mod(poly, [powermod(point, i, F) for i = 0:(length(poly)-1)], F)
end

@test eval_poly([1, 2, 3], 11, 23) == 18

# Ensures highest-order coefficient is not zero
function ensure_nonzero_lead(a::Vector{Int64})
    # Cut trailing zeros using dropwhile and reverse
    r = collect(Iterators.dropwhile((x) -> x == 0, reverse(a)))
    reverse!(r)
end

@test ensure_nonzero_lead([1, 2, 3, 0, 0, 0]) == [1, 2, 3]

# Polynomial coefs are given from least significant to most significant,
# i.e. a[0] is the constant term 
function poly_mul(a::Vector{Int64}, b::Vector{Int64})
    if length(a) > N_halved || length(b) > N_halved
        error("wrong length of input polynomials")
    end

    a = vcat(a, zeros(Int64, N - length(a)))
    b = vcat(b, zeros(Int64, N - length(b)))

    a_fft = fft(a, ws)
    b_fft = fft(b, ws)
    r = fft(a_fft .* b_fft .% F, iws) .* invmod(N, F) .% F
    ensure_nonzero_lead(r)
end

coefs_a = rand(0:F-1, div(N, 4))
coefs_b = rand(0:F-1, div(N, 4))
coefs_c = poly_mul(coefs_a, coefs_b)
r = rand(0:F-1)
@test eval_poly(coefs_c, r, F) == (eval_poly(coefs_a, r, F) * eval_poly(coefs_b, r, F)) % F

function poly_add(a::Vector{Int64}, b::Vector{Int64})
    n = max(length(a), length(b))
    a = vcat(a, zeros(Int64, n - length(a)))
    b = vcat(b, zeros(Int64, n - length(b)))

    ensure_nonzero_lead((a .+ b) .% F)
end

function poly_sub(a::Vector{Int64}, b::Vector{Int64})
    n = max(length(a), length(b))
    a = vcat(a, zeros(Int64, n - length(a)))
    b = vcat(b, zeros(Int64, n - length(b)))

    ensure_nonzero_lead((a .- b .+ F) .% F)
end

# For a polynomial a of degree n = 2^k - 1 (i.e. length(a) = 2^k = n + 1)
# compute polynomial b such that b = floor(x^2n / a)
function poly_reciprocal(a::Vector{Int64})
    # Source: https://web.archive.org/web/20210404041913/https://web.cs.iastate.edu/%7Ecs577/handouts/polydivide.pdf

    if a[end] == 0
        error("leading coefficient is zero")
    end

    # Assuming that a's length is a power of 2
    if length(a) == 1
        return [invmod(a[1], F)]
    end

    n_halved = div(length(a), 2)

    # compute reciprocal of a polynomial of half the degree
    q = poly_reciprocal(a[n_halved+1:end])

    q_doubled = vcat(zeros(Int64, 3n_halved - 2), q .* 2 .% F)
    r = poly_sub(q_doubled, poly_mul(poly_mul(q, q), a))
    r[length(a)-1:end]
end

coefs_x = rand(0:F-1, 8)
recip = poly_reciprocal(coefs_x)
# recip * coefs_x / x^8 == x^6
@test poly_mul(recip, coefs_x)[9:end] == vcat(zeros(Int64, 6), [1])

function poly_div(a::Vector{Int64}, b::Vector{Int64})
    a = ensure_nonzero_lead(a)
    b = ensure_nonzero_lead(b)

    if length(a) < length(b)
        return []
    end

    # calculate power of two that is greater or equal to length(a)
    n = nextpow(2, length(b))

    common_multiplier = n - length(b)

    a = vcat(zeros(Int64, common_multiplier), a)
    b = vcat(zeros(Int64, common_multiplier), b)

    m = length(a) - 1 # degree of a
    n = length(b) - 1 # degree of b

    b_recip = poly_reciprocal(b)
    q = poly_mul(a, b_recip)
    q = q[2n+1:end]

    if m > 2 * n
        b_recip_mod = poly_sub(vcat(zeros(Int64, 2n), [1]), poly_mul(b_recip, b))
        p = poly_mul(a, b_recip_mod)
        p = p[2n+1:end]
        q2 = poly_div(p, b)
        poly_add(q, q2)
    else
        q
    end
end

@test poly_div([1, 2, 3, 4, 5, 6, 7, 8], [1, 2, 3, 4, 5, 6, 7, 8]) == [1]
@test poly_div(coefs_c, coefs_b) == coefs_a

coefs_y = rand(0:F-1, N_halved - 5)
y_div_a = poly_div(coefs_y, coefs_a)
y_mod_a = poly_sub(coefs_y, poly_mul(y_div_a, coefs_a))

# y = y/a * a + y%a
@test poly_add(poly_mul(y_div_a, coefs_a), y_mod_a) == coefs_y

# Scales free variable of a polynomial by a constant factor
function scale_x(a::Vector{Int64}, x::Int64)
    # powers of x modulo F
    x_powers = [powermod(x, i, F) for i = 0:(length(a)-1)]
    a .* x_powers .% F
end

# Divides a polynomial by a monomial of form `x + c`
#
# Precondition: monomial divides the polynomial
function poly_div_monomial(dividend::Vector{Int64}, c::Int64)
    if c == 0
        if dividend[1] != 0
            error("monomial does not divide the polynomial")
        end
        return dividend[2:end]
    end
    result = zeros(Int64, length(dividend) - 1)
    c_inv = invmod(c, F)
    result[1] = dividend[1] * c_inv % F
    for i = 2:length(dividend)-1
        result[i] = (dividend[i] + F - result[i-1]) % F * c_inv % F
    end
    if dividend[end] != result[end]
        error("monomial does not divide the polynomial")
    end
    result
end

# Multiplies a polynomial by a monomial of form `x + c`
function poly_mul_monomial(a::Vector{Int64}, c::Int64)
    (vcat(a .* c .% F, zeros(Int64, 1)) .+ vcat(zeros(Int64, 1), a)) .% F
end