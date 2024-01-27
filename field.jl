using Primes

function summod(vs::AbstractArray{Int64}, m::Int64)
    reduce((a, b) -> (a + b) % m, vs)
end

function dot_mod(a::Vector{Int64}, b::Vector{Int64}, F::Int64)
    summod(a .* b .% F, F)
end

function inv_mod(x :: Int64, F :: Int64)
    powermod(x, F - 2, F)
end

function div_mod(x :: Int64, y :: Int64, F :: Int64)
    x * inv_mod(y, F) % F
end

ps = Primes.primes(1000, 13000)
pw, ix = findmax(map((p) -> Primes.factor(p - 1)[2], ps))

F = ps[ix] # field order
N = 2^pw
N_halved = 2^(pw-1)

println("F: ", F, " N: ", N)

w = 1 # w is N-th primitive root of unity in the field
while powermod(w, N_halved, F) == 1
    global w
    w = powermod(rand(2:F-1), div(F - 1, N), F)
end
ws = [powermod(w, i, F) for i = 0:N-1]

iw = inv_mod(w, F)
iws = [powermod(iw, i, F) for i = 0:N-1]