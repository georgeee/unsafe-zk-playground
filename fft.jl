include("./field.jl")

using LinearAlgebra
using Test

# FFT implemented over a small field

# FFT calculates a vector of n values, one for each power of root of unity
# each value is evaluation of polynomial p(x) = a0 + a1*x + .. + an-1 * x^(n-1)
function fft(coefs::Vector{Int64}, ws::Vector{Int64})
    if length(coefs) == 1
        return Vector{Int}([coefs[1]])
    end
    even_ixs = 2 * (1:div(length(coefs), 2))
    ws2 = ws[even_ixs.-1] # squares of roots of unity
    even = fft(coefs[even_ixs], ws2)
    odd = fft(coefs[even_ixs.-1], ws2)
    append!(odd, odd)
    append!(even, even)
    (odd + (ws .* even) .% F) .% F
end

function dummy_multiplication(coefs::Vector{Int64}, ws::Vector{Int64})
    map((i) -> summod(coefs .* ws[[1 + (j * i) % N for j = 0:N-1]] .% F, F), 0:N-1)
end

# Test fft ∘ inverse fft = identity
fft_coefs_ = vcat([rand(0:F-1) for i = 1:div(N, 2)], zeros(Int64, div(N, 2)))
ffted = fft(fft_coefs_, ws)
fft_inverse = fft(ffted, iws) .* invmod(N, F) .% F
@test fft_coefs_ == fft_inverse

# It's possible to check that fft gives the same result as dummy_multiplication 