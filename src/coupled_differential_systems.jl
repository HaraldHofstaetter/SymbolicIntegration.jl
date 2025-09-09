# This file contains algorithms needed for the integratiorn of 
# coupled Risch differential systems from chapter 8 of the book
#
#    Manuel Bronstein, Symbolic Integration I: Transcendental Functions,
#    2nd ed., Springer 2005. 
#

"""
    CoupledDECancelPrim(b₁, b₂, c₁, c₂,  D[, n=∞]) -> (q₁, q₂, ρ)

Coupled Polynomial Risch differential system, cancellation - primitive case.

Given a field `k` not containing `√-1` , a derivation `D` on `k[t]` with `D(t)` in `k` , an integer `n`,
`b₁`, `b₂` in `k` with `(b₁,b₂)≠(0,0)` and `c₁`, `c₂` in `k[t]`, return either
`ρ=0`, in which case the system of equations `D(q₁)+b₁*q₁-b₂*q₂=c₁`, `D(q₂)+b₂*q₁+b₁*q₂=c₂`
has no solution `q₁`, `q₂` with both degrees at most `n` in `k[t]`,
or `ρ=1` and a solution `(q₁,q₂)` in `k[t]×k[t]` of this system with `degree(q₁)≤n`
and `degree(q₂)≤n`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 8.2, p. 260.
"""
function CoupledDECancelPrim(b1::T, b2::T,  c1::P, c2::P, D::Derivation, n::Int=typemax(Int)) where
    {T<:FieldElement, P<:PolyRingElem{T}} # here typemax(Int) represents +infinity
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
    t = gen(parent(c1))
    _, I, D0I = Complexify(parent(b1), D0)
    z, ρ = InFieldLogarithmicDerivative(b1 + b2*I, D0I) 
    if ρ>0
        z1 = real(z)
        z2 = imag(z)
        p10, ρ = InFieldDerivative(z1*c1 - z2*c2, D)
        p1 = numerator(p10)
        if ρ<=0 || !isone(denominator(p10)) || degree(p1)>n
            return no_solution 
        end
        p20, ρ = InFieldDerivative(z2*c1 + z1*c2, D)
        p2 = numerator(p20)
        if ρ<=0 || !isone(denominator(p20)) || degree(21)>n
            return no_solution 
        end
        d = z1^2 + z1^2
        return (z1*p1 + z2*p2)//d, (z1*p2 - z2*p1)//d, 1
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
        s1, s2, ρ = CoupledDESystem(b1, b2, coeff(c1, m), coeff(c2, m), D0)
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


"""
    CoupledDECancelExp(b₁, b₂, c₁, c₂,  D[, n=∞]) -> (q₁, q₂, ρ)

Coupled Polynomial Risch differential system, cancellation - hyperexponential case.

Given a field `k` not containing `√-1` , a derivation `D` on `k[t]` with `D(t)/t` in `k` , an integer `n`,
`b₁`, `b₂` in `k` with `(b₁,b₂)≠(0,0)` and `c₁`, `c₂` in `k[t]`, return either
`ρ=0`, in which case the system of equations `D(q₁)+b₁*q₁-b₂*q₂=c₁`, `D(q₂)+b₂*q₁+b₁*q₂=c₂`
has no solution `q₁`, `q₂` with both degrees at most `n` in `k[t]`,
or `ρ=1` and a solution `(q₁,q₂)` in `k[t]×k[t]` of this system with `degree(q₁)≤n`
and `degree(q₂)≤n`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 8.2, p. 262.
"""
function CoupledDECancelExp(b1::T, b2::T,  c1::P, c2::P, D::Derivation, n::Int=typemax(Int)) where
    {T<:FieldElement, P<:PolyRingElem{T}} # here typemax(Int) represents +infinity
    ishyperexponential(D) ||
        error("monomial of derivation D must be hyperexponential")
    D0 = BaseDerivation(D)
    (iscompatible(b1, D0) && iscompatible(b2, D0)) || 
        error("coefficients b1 and b2 must be in the domain of the base derivation of D")
    (iscompatible(c1, D) && iscompatible(c2, D)) || 
        error("polynomials c1 and c2 must be in the domain of derivation D")
    Z = zero(c1)
    no_solution = (Z, Z, 0)
    # TODO: case (b1, b2)==(0, 0) !?
    t = gen(parent(c1))
    _, I, D0I = Complexify(parent(b1), D0)
    H = MonomialDerivative(D)
    w = coeff(H,1) # = Dt/t for hyperexponentialm case
    n1, m, z, ρ = ParametricLogarithmicDerivative(b1 + b2*I, w + 0*I, D0I)
    if  ρ>0 && n1==1
        z1 = real(z)
        z2 = imag(z)                
        p1, ρ = InFieldDerivative((z1*c1 - z2*c2)*t^m, D)        
        if ρ<=0 || !isreduced(p1, D)
            return no_solution 
        end
        h = (t//1)^(-m)//(z1^2 + z2^2)
        q10 = (z1*p1 + z2*p2)*h
        q1 = numerator(q10)
        if !isone(denominator(q10)) || degree(q1)>n
            return no_solution
        end
        p2, ρ = InFieldDerivative((z2*c1 + z1*c2)*t^m, D)
        if ρ<=0 || !isreduced(p1, D)
            return no_solution 
        end
        q20 = (z1*p2 - z2*p1)*h
        q2 = numerator(q20)
        if !isone(denominator(q20)) || degree(q2)>n
            return no_solution
        end
        return q1, q2, 1
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
        s1, s2, ρ = CoupledDESystem(b1 + m*w, b2, coeff(c1, m), coeff(c2, m), D0)
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

"""
    CoupledDECancelTan(b₀, b₂, c₁, c₂,  D[, n=∞]) -> (q₁, q₂, ρ)

Coupled Polynomial Risch differential system, cancellation - hypertangent case.

Given a field `k` not containing `√-1` , a derivation `D` on `k[t]` with `D(t)/(t²+1)=η` in `k` , an integer `n`,
`b₀`, `b₂` in `k` with `(b₀,b₂)≠(0,0)` and `c₁`, `c₂` in `k[t]`, return either
`ρ=0`, in which case the system of equations `D(q₁)+(b₀-n*η*t)*q₁-b₂*q₂=c₁`, `D(q₂)+b₂*q₁+(b₀+n*η*t)*q₂=c₂`
has no solution `q₁`, `q₂` with both degrees at most `n` in `k[t]`,
or `ρ=1` and a solution `(q₁,q₂)` in `k[t]×k[t]` of this system with `degree(q₁)≤n`
and `degree(q₂)≤n`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 8.2, p. 262.
"""
function CoupledDECancelTan(b0::T, b2::T,  c1::P, c2::P, D::Derivation, n::Int=typemax(Int)) where
    {T<:FieldElement, P<:PolyRingElem{T}} # here typemax(Int) represents +infinity
    ishypertangent(D) ||
        error("monomial of derivation D must be hypertangent")
    D0 = BaseDerivation(D)
    (iscompatible(b0, D0) && iscompatible(b2, D0)) || 
        error("coefficients b0 and b2 must be in the domain of the base derivation of D")
    (iscompatible(c1, D) && iscompatible(c2, D)) || 
        error("polynomials c1 and c2 must be in the domain of derivation D")
    Z = zero(c1)
    no_solution = (Z, Z, 0)
    # TODO: case (b0, b2)==(0, 0) !?
    if n==0
        if degree(c1)<=0 && degree(c2)<=0
            q1, q2, ρ = CoupledDESystem(b0, b2, constant_coefficient(c1), constant_coefficient(c2), BaseDerivation(D))
            if ρ<=0
                return no_solution
            end
            return q1 + Z, q2 + Z, 1
        end
        return no_solution
    end
    t = gen(parent(c1))
    H = MonomialDerivative(D)
    η = constant_coefficient(divexact(H, t^2 + 1))
    ktI, I, DI = Complexify(fraction_field(parent(c1)), D) # k(t)(√-1)    
    p = t - I    
    z = c1(I) + c2(I)*I
    z1 = real(z)
    @assert isone(denominator(z1)) && degree(numerator(z1))<=0
    z1 = constant_coefficient(numerator(z1))  # real(z) in k(t), z1 in k
    z2 = imag(z)
    @assert isone(denominator(z2)) && degree(numerator(z2))<=0
    z2 = constant_coefficient(numerator(z2))  # imag(z) in k(t), z2 in k
    s1, s2, ρ = CoupledDESystem(b0, b2 - n*η, z1, z2, BaseDerivation(D))
    if ρ<=0
        return no_solution
    end
    c = (c1 - z1 + n*η*(s1*t + s2) + (c2 - z2 + n*η*(s2*t - s1))*I)//p
    d1 = real(c)
    @assert isone(denominator(d1))
    d1 = numerator(d1)
    d2 = imag(c)
    @assert isone(denominator(d2))
    d2 = numerator(d2)
    h1, h2, ρ = CoupledDECancelTan(b0, b2 + η, d1, d2, D, n - 1)
    if ρ<=0
        return no_solution
    end
    h1*t + h2 + s1, h2*t - h1 + s2, 1
end


function CoupledDESystem(f1::F, f2::F, g1::F, g2::F, D::Derivation) where 
    {P<:PolyRingElem, F<:FracElem{P}}
    iscompatible(f1, D) && iscompatible(f2, D) && iscompatible(g1, D) && iscompatible(g2, D)|| 
        error("rational functions f1. f2. g1, g2 must be in the domain of derivation D")
    #if iszero(f1) && iszero(f2)  
    #    return InFieldDerivative ...
    #end
 
    no_solution = zero(f1), zero(f1), 0

    t0 = gen(parent(numerator(f1)))
    ktI, I0, DI0 = Complexify(parent(f1), D) # k(t)(√-1)        
    kIt, t, I, DI =  switch_t_i(ktI, DI0) # k(√-1)(t)

    f = transform(f1 + I0*f2, t, I)
    g = transform(g1 + I0*g2, t, I)

    Z = zero(f)
    h0 = WeakNormalizer(f, DI)

    f = f - DI(h0)//h0
    g = h0*g
    a, b, c, h1, ρ = RdeNormalDenominator(f, g, DI)    
    ρ>=1 || return no_solution

    a, b, c, h2 = RdeSpecialDenominator(a, b, c, DI)

    n = RdeBoundDegree(a, b, c, DI)

    b, c, n, α, β, ρ = SPDE(a, b, c, DI, n)
    ρ>=1 || return no_solution

    z, ρ = PolyRischDE(b, c, DI, n)
    if ρ<=0 
        return no_solution
    elseif ρ==1
        y = backtransform((α*z + β)//(h0*h1*h2), t0, I0)
        return real(y), imag(y), 1
    end
    
    @assert ρ>=100
    n = ρ - 101

    #TODO: case b1=0 and b2=0: in-field integration algorithm. see p. 259
    c = backtransform(z + Z, t0, I0)
    c1 = real(c)
    c2 = imag(c)
    @assert isone(denominator(c1)) && isone(denominator(c2))
    c1 = numerator(c1)
    c2 = numerator(c2)
    b = backtransform(b + Z, t0, I0)
    b1 = real(b)
    b2 = imag(b)
    @assert isone(denominator(b1)) && isone(denominator(b2))
    b1 = numerator(b1)
    b2 = numerator(b2)
    if isprimitive(D)
        @assert degree(b1)<=0 && degree(b2)<=0
        z1, z2, ρ = CoupledDECancelPrim(constant_coefficient(b1), constant_coefficient(b2), c1, c2,  D, n)
        ρ>=1 || return no_solution
    elseif ishyperexponential(D)
        @assert degree(b1)<=0 && degree(b2)<=0
        z1, z2, ρ = CoupledDECancelExp(constant_coefficient(b1), constant_coefficient(b2), c1, c2,  D, n)
        ρ>=1 || return no_solution
    elseif ishypertangent(D)             
        η = divexact(MonomialDerivative(D), t0^2+1)
        b0 = b1 + n*t0*η
        @assert degree(b0)<=0 && degree(b2)<=0
        z1, z2, ρ = CoupledDECancelTan(constant_coefficient(b0), constant_coefficient(b2), c1, c2,  D, n)
        ρ>=1 || return no_solution
    else
        H = MonomialDerivative(D)
        throw(NotImplementedError("CoupledDESystem: cancellation case, monomial derivative $H\n@ $(@__FILE__):$(@__LINE__)")) 
    end

    # Note: α, β, h0, h1, h2 are in k(√-1)(t) or k(√-1)[t]
    α = backtransform(α + Z, t0, I0) 
    β = backtransform(β + Z, t0, I0) 
    h = backtransform(h0*h1*h2 + Z, t0, I0) 
    y = (α*(z1+z2*I0)+β)//h
    real(y), imag(y), 1
end

