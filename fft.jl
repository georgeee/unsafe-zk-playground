# FFT implemented over a small field

using Primes
using LinearAlgebra

ps = Primes.primes(1000, 13000)
pw, ix = findmax(map((p) -> Primes.factor(p - 1)[2], ps))

F = ps[ix] # field order
N = 2^pw

println("F: ", F, " N: ", 2^pw)

w = 1 # w is N-th primitive root of unity in the field
while powermod(w, 2^(pw - 1), F) == 1
    global w
    w = powermod(rand(2:F-1), div(F - 1, N), F)
end

ws = [powermod(w, i, F) for i = 0:N-1]

iw = powermod(w, F - 2, F)

iws = [powermod(iw, i, F) for i = 0:N-1]

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

function summod(vs::AbstractArray{Int64}, m::Int64)
    reduce((a, b) -> (a + b) % m, vs)
end

function dummy_multiplication(coefs::Vector{Int64}, ws::Vector{Int64})
    map((i) -> summod(coefs .* ws[[1 + (j * i) % N for j = 0:N-1]] .% F, F), 0:N-1)
end

function dot_mod(a::Vector{Int64}, b::Vector{Int64}, F::Int64)
    summod(a .* b .% F, F)
end

# Test fft ∘ inverse fft = identity
fft_coefs = [rand(0:F-1) for i = 1:div(N, 2)]
fft_coefs_ = vcat(fft_coefs, zeros(Int64, div(N, 2)))

ffted = fft(fft_coefs_, ws)
fft_inverse = fft(ffted, iws) .* powermod(N, F - 2, F) .% F
println(fft_coefs_ == fft_inverse)

# It's possible to check that fft gives the same result as dummy_multiplication 