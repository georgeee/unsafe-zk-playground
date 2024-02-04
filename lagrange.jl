include("field.jl")
include("polynomial.jl")

function lagrange_poly(lws, l_vanishing, i :: Int)
    a = repeat([lws[i]], length(lws)-1)
    b = vcat(lws[1:i-1], lws[i+1:end])
    denominator_inv = inv_mod(prodmod(a .- b .+ F .% F, F), F)
    numerator = poly_div_monomial(l_vanishing, F-lws[i])
    numerator .* denominator_inv .% F
end

function lagrange_interpolate(lagrange_polys :: Vector{Vector{Int64}}, ys :: Vector{Int64})
    reduce((a, b) -> (a .+ b) .% F, [ys[i] .* lagrange_polys[i] .% F for i = 1:length(ys)])
end

function test_lagrange_interpolate(lws, lagrange_polys)
    ys = rand(0:F-1, length(lws))
    p = lagrange_interpolate(lagrange_polys, ys)
    [eval_poly(p, lws[i], F) for i = eachindex(lws)] == ys
end

lws = ws[1:4:end]
l_vanishing = vcat([F-1], zeros(Int64, length(lws)-1), [1])

lagrange_polys = [lagrange_poly(lws, l_vanishing, i) for i = eachindex(lws)]
@test test_lagrange_interpolate(lws, lagrange_polys)