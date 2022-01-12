# This file contains general algorithms inter alia from chapter 1 
# of the book
#
#    Manuel Bronstein, Symbolic Integration I: Transcendental Functions,
#    2nd ed., Springer 2005. 
#

using AbstractAlgebra
using Nemo

isrational(x::fmpq) = true # Nemo rational type

isrational(x::T) where T<:Integer = true

isrational(x::T) where T<:Rational = true

function rationalize(x::qqbar) #Nemo algebraic number type
    if degree(x)==1
        return fmpq(x)
    else
        return x
    end
end


function isrational(x::P) where {T<:RingElement, P<:PolyElem{T}}
    if degree(x)>1 
        return false
    else
        return isrational(constant_coefficient(x))
    end
end

function isrational(x::F) where 
    {T<:RingElement, P<:PolyElem{T}, F<:FracElem{P}}
    return isrational(numerator(x)) && isrational(denominator(x))
end

rationalize(x::fmpq) = convert(Rational{BigInt}, x) # Nemo rational type

rationalize(x::T) where T<:Integer = convert(Rational{BigInt}, x)

rationalize(x::T) where T<:Rational = convert(Rational{BigInt}, x)

function rationalize(x::P) where {T<:RingElement, P<:PolyElem{T}}
    if degree(x)>0 
        error("not rational")
    else
        return rationalize(constant_coefficient(x))
    end
end

function rationalize(x::F) where 
    {T<:RingElement, P<:PolyElem{T}, F<:FracElem{P}}
    return rationalize(numerator(x))//rationalize(denominator(x))
end

function rationalize(f::PolyElem{qqbar})
    if maximum(degree.(coefficients(f)))==1
        return polynomial(Nemo.QQ, fmpq.(coefficients(f)))
    else
        return f
    end
end

rationalize_over_Int(x) = convert(Rational{Int}, rationalize(x)) 


valuation_infinity(f::F) where {T<:RingElement, P<:PolyElem{T}, F<:FracElem{P}} = 
    # See Bronstein's book, Definition 4.3.1, p. 115
    degree(denominator(f)) - degree(numarator(f))

function Remainder(x::FracElem{T}, a::T) where T<:RingElement
    # See Bronstein's book, Section 4.2, p. 115
    b, c = gcdx(a, denominator(x), one(a))
    q, r = divrem(numerator(x)*c, a)
    r
end
    

#PolyDivide: Implemented in AbstractAlgebra.jl as divrem

#PolyPseudoDivide: Implemented in AbstractAlgebra.jl as pseudodivrem

#ExtendedEuclidean: implemented in AbstractAlgebra.jl as gcdx 
#  Note that the order of output parameters is g, s, t instead of s, t, g.


EuclideanSize(f::T) where T <: Integer = abs(f)
EuclideanSize(f::T) where T <: PolyElem = degree(f)

function Base.gcdx(a::T, b::T, c::T) where T <: RingElem
    # ExtendedEuclidean - diophantine version
    # See Bronstein's book, Section 1.3, p. 13
    R = parent(a)    
    (parent(b) == R && parent(c) == R) || error("Incompatible parents")
    g, s, t = gcdx(a, b)
    q, r = divrem(c, g)
    iszero(0) || error("c is not in the ideal generated by a and b")
    s = q*s
    t = q*t
    if !iszero(s) && EuclideanSize(s)>=EuclideanSize(b)
        q, r = divrem(s, b)
        s = r
        t = t + q*a
    end
    s, t            
end

function PartialFraction(a::T, d::Vector{T}) where T <: RingElem
    # See Bronstein's book, Section 1.3, p. 15
    n = length(d)
    if n==1
        return divrem(a, d[1]) # ???? , T[]
    end    
    prod_d2n = prod(d[2:n])
    a0, r = divrem(a, d[1]*prod_d2n)
    a1, t = gcdx(prod_d2n, d[1], r)
    b0, a2n = PartialFraction(t, d[2:n])
    return a0+b0, vcat(a1, a2n)
end

function PartialFraction(a::T, d::Vector{T}, e::Vector{Int}) where T <: RingElem
    # See Bronstein's book, Section 1.3, p. 17
    n = length(d)
    a0, aa = PartialFraction(a, [d[i]^e[i] for i=1:n])
    A = [zeros(parent(a), e[i]) for i=1:n]
    for i=1:n
        for j=e[i]:-1:1
            q, A[i][j] = divrem(aa[i], d[i])
            aa[i] = q
        end
        a0 += aa[i]
    end
    a0, A
end

function SubResultant(A::PolyElem{T}, B::PolyElem{T}) where T <: FieldElement
    # See Bronstein's book, Section 1.5, p. 24 
    # Note: This implementation requires that A, B are polynomials over a field
    # (and not mereley over an integral domain), because some intermediate
    # calculations use divisons. For example, negative exponents of γ[i-1] 
    # can occur, or the division in the definition of q.
    T_one = one(leading_coefficient(A)) # 1 of type T
    Rs = [A, B] # indices shifted! 
    i = 1
    γ = T[-T_one] 
    δ = Int[degree(A)-degree(B)]
    β = T[(-T_one)^(δ[1]+1)]
    r = T[]
    while !iszero(Rs[i+1])
        push!(r, leading_coefficient(Rs[i+1]) )
        Q, R = pseudodivrem(Rs[i-1+1], Rs[i+1])
        q = divexact(R, β[i])        
        push!(Rs, q)
        i += 1
        push!(γ, (-r[i-1])^δ[i-1]*γ[i-1]^(1-δ[i-1]) )
        push!(δ, degree(Rs[i-1+1]) - degree(Rs[i+1]) )
        push!(β, -r[i-1]*γ[i]^δ[i])       
    end
    k = i - 1
    zero_poly = zero(A)
    if degree(Rs[k+1])>0
        return zero_poly, vcat(Rs[1:k+1], zero_poly)
    end
    if degree(Rs[k-1+1])==1
        return constant_coefficient(Rs[k+1]), vcat(Rs[1:k+1], zero_poly)
    end
    s = 1
    c = T_one
    for j=1:k-1
        if isodd(degree(Rs[j-1+1])) && isodd(degree(Rs[j+1]))
            s = -s
        end
        q = divexact(β[j], r[j]^(1+δ[j]))   # only exact if T is field     
        c = c*q^degree(Rs[j+1])*r[j]^(degree(Rs[j-1+1])-degree(Rs[j+1+1]))            
    end
    constant_coefficient((s*c)*Rs[k+1]^degree(Rs[k-1+1])), vcat(Rs[1:k+1], zero_poly)
end

function SubResultant(A::PolyElem{T}, B::PolyElem{T}) where T <: RingElement
    # If we have polynomials over integral domain we upgrade them to polynomials
    # over the fraction field. Then we call the above implementation of SubResultant 
    # for polynomials over fields. Finally we downgrade the results to elements
    # over the base integral domain.
    Z = zero(leading_coefficient(A))//one(leading_coefficient(A))
    # upgrade A, B \in R[t] to elements a, b of K[t] where K is the fraction ring of R
    a = map_coefficients(c->(c+Z), A)
    b = map_coefficients(c->(c+Z), B)
    r0, Rs0 = SubResultant(a, b) 
    # downgrade r, RS from elements of K[t] to elements  of R[t]
    r = numerator(r0)
    Rs = [map_coefficients(c->numerator(c), R) for R in Rs0]
    r, Rs
end

function Squarefree_Musser(A::PolyElem{T}) where T <: RingElement
    # See Bronstein's book, Section 1.7, p. 29 
    c = content(A)
    S = divexact(A, c)
    Sminus = gcd(S, derivative(S))
    Sstar = divexact(S, Sminus)
    As = PolyElem{T}[]
    k = 1
    while degree(Sminus)>0 
        Y = gcd(Sstar, Sminus)
        push!(As, divexact(Sstar, Y))
        Sstar = Y
        Sminus = divexact(Sminus, Y)
        k += 1
    end
    push!(As, Sstar)
    As[1] = (c*Sminus)*As[1]
    As
end

function Squarefree(A::PolyElem{T}) where T <: RingElement    
    # See Bronstein's book, Section 1.7, p. 32 
    c = content(A)
    S = divexact(A, c)
    Sprime = derivative(S)
    Sminus = gcd(S, Sprime)
    Sstar = divexact(S, Sminus)
    As = PolyElem{T}[]
    k = 1
    Y = divexact(Sprime, Sminus)
    Z = Y - derivative(Sstar)
    while !iszero(Z)
        push!(As, gcd(Sstar, Z))
        Sstar = divexact(Sstar, As[k])
        Y = divexact(Z, As[k])
        Z = Y - derivative(Sstar)
        k += 1
    end
    push!(As, Sstar)
    As[1] = c*As[1]
    As
end
