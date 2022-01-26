# This file contains algorithms needed for the integratiorn of 
# coupled Risch differential systems from chapter 8 of the book
#
#    Manuel Bronstein, Symbolic Integration I: Transcendental Functions,
#    2nd ed., Springer 2005. 
#

"""
    CoupledDECancelPrim(b₁, b₂, c₁, c₂,  D[, n=∞]) -> (q₁, q₂, ρ)

Coupled Polynomial Risch differential system, cancellation - primitive case.

Given a field `k` not containing `√-1` , a derivation `D` on `k[t]`, an integer `n`,
`b₁`, `b₂` in `k` and `c₁`, `c₂` in `k[t]`  with `D(t)` in `k` and `(b₁,b₂)≠(0,0)`, return either
`ρ=0`, in which case the system of equations `D(q₁)+b₁*q₁-b₂*q₂=c₁`, `D(q₂)+b₂*q₁+b₁*q₂=c₂`
has no solution with both degrees at most `n` in `k[t]`,
or `ρ=1` and a solution `(q₁,q₂)` in `k[t]×k[t]` of this system with `degree(q₁)≤n`
and `degree(q₂)≤n`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 8.2, p. 260.
"""
function CoupledDECancelPrim(b1::T, b1::T,  c1::P, c2::P, D::Derivation, n::Int=typemax(Int)) where
    {T<:RingElement, P<:PolyElem{T}} # here typemax(Int) represents +infinity
    isprimitive(D) ||
        error("monomial of derivation D must be primitive")
    D0 = BaseDerivation(D)
    (iscompatible(b1, D0) && iscompatible(b2, D0)) || 
        error("coefficients b1 and b2 must be in the domain of the base derivation of D")
    (iscompatible(c1, D) && iscompatible(c2, D)) || 
        error("polynomials c1 and c2 must be in the domain of derivation D")
    Z = zero(c1)
    no_solution = (Z, Z, 0)
    # TODO: case (b1, b2)==(0, 0) !?
    t = gen(parent(c))
    _, I, D0I = Complexify(parent(b1), D0)
    z, ρ = InFieldLogarithmicDerivative(b+0*I, D0I) 
    if ρ>0
        z1 = real(z)
        z2 = imag(z)
        p10, ρ = InFieldDerivative(z1*c1-z2*c2, D)
        p1 = numerator(p10)
        if ρ<=0 || !isone(denominator(p10)) || degree(p1)>n
            return no_solution 
        end
        p20, ρ = InFieldDerivative(z2*c1+z1*c2, D)
        p2 = numerator(p20)
        if ρ<=0 || !isone(denominator(p20)) || degree(21)>n
            return no_solution 
        end
        d = z1^2+z1^2
        return (z1*p1+z2*p2)//d, (z1*p2-z2*p1)//d, 1
    end
    if iszero(c1) && iszero(c2)
        return Z, Z, 1 # zero is solution
    end
    if n<max(degree(c1), degree(c2))
        return no_solution
    end
    q1 = Z   
    q2 = Z
    while !iszero(c1) || !iszero(c2)
        m = max(degree(c1), degree(c2))
        if n<m
            return no_solution
        end
        s1, s2, ρ = CoupledDESystem(b1, b2, coefficient(c1, m), coefficient(c2, m), D0)
        if ρ<=0
            return no_solution
        end
        q1 = q1 + s1*t^m
        q2 = q2 + s2*t^m
        n = m - 1
        c1 -= D(s1*t^m) + (b1*s1 - b2*s2)*t^m
        c2 -= D(s2*t^m) + (b2*s1 + b1*s2)*t^m
    end
    q1, q2, 1
end