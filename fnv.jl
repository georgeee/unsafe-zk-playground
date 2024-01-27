# FNV-1a hash implementation
# This is a highly insecure hash, used in lieu of crtyptographic hash
# in various constructions implemented in the repository


fnv_prime = 1099511628211::Int64
fnv_basis = (-5472609002491880229)::Int64

function fnv1a(data::Int64, h=fnv_basis)
    h = h ⊻ (data & 255)
    h = h * fnv_prime
    h = h ⊻ ((data >> 8) & 255)
    h = h * fnv_prime
    h = h ⊻ ((data >> 16) & 255)
    h = h * fnv_prime
    h = h ⊻ ((data >> 24) & 255)
    h = h * fnv_prime
    h = h ⊻ ((data >> 32) & 255)
    h = h * fnv_prime
    h = h ⊻ ((data >> 40) & 255)
    h = h * fnv_prime
    h = h ⊻ ((data >> 48) & 255)
    h = h * fnv_prime
    h = h ⊻ ((data >> 56))
    h * fnv_prime
end

function fnv1a(data::AbstractArray{Int64,1}, h=fnv_basis)
    init = fnv1a(length(data)::Int64, h)
    foldr(fnv1a, data; init)
end

"""
Calculate merkle tree of a vector of size 2^w

A vector representing the merkle tree will be returned with
the first element is the root.
"""
function fnv1a_merkle(data::AbstractArray{Int64,1})
    result = zeros(Int64, length(data) - 1)
    append!(result, data)
    for i in (length(data)-1:-1:1)
        j = i << 1
        # result[i] = result[j]+result[j+1]
        result[i] = fnv1a(result[j], result[j+1])
    end
    result
end

# fnv1a_merkle(Vector(1:8))

