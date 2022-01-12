# This file contains algorithms needed for the solution of 
# the Risch differential equation from chapter 6 of the book
#
#    Manuel Bronstein, Symbolic Integration I: Transcendental Functions,
#    2nd ed., Springer 2005. 
#


function WeakNormalizer(f::F, D::Derivation) where 
    {T<:RingElement, P<:PolyElem{T}, F<:FracElem{P}}
    # See Bronstein's book, Section 6.1, p. 183
    dn, ds = SplitFactor(denominator(f), D)
    g = gcd(dn, derivative(dn))
    dstar = divexact(dn, g)
    d1 = divexact(dstar, gcd(dstar, g))
    a, b = gcdx(divexact(denominator(f), d1), d1, numerator(f))
    kz, z = PolynomialRing(base_ring(a), :ζ)    
    kzt, t = PolynomialRing(kz, var(parent(a)))
    dd1 = D(d1)
    r = resultant(d1(t), a(t)-z*dd1(t)) 
    ns = [numerator(rationalize_over_Int(x)) for x in roots(r) if 
            isrational(x) && isone(denominator(x)) && x>0] # roots needs Nemo
    if isempty(ns)
        return one(numerator(f))
    end
    prod([gcd(a - n*dd1, d1)^n for n in ns])
end

function RdeNormalDenominator(f::F, g::F, D::Derivation) where 
    {T<:RingElement, P<:PolyElem{T}, F<:FracElem{P}}
    # See Bronstein's book, Section 6.1, p. 185
    (dn, ds) = SplitFactor(denominator(f), D)
    (en, es) = SplitFactor(denominator(g), D)
    p = gcd(dn, en)
    h = divexact(gcd(en, derivative(en)), gcd(p, derivative(p)))
    if !iszero(rem(dn*h^2, en))
        return zero(h), zero(f), zero(f), zero(h), 0
    end
    dn*h, dn*h*f-dn*D(h), dn*h^2*g, h, 1
end

function one_times_n_solve(A::Vector{T}, B::Vector{T}) where T<:RingElement
    if length(A)!=length(B) || length(A)==0 
        return T[] # no solution
    end
    eqfound = false
    c = 0
    for i=1:length(A)
        a = A[i]
        b = B[i]
        if iszero(b) 
            if !iszero(a)
                return T[] # no solution 
            end
        elseif eqfound 
            if c!=a//b
                return T[] # no solution
            end
        else
            c = a//b
            eqfound = true
        end
    end
    eqfound ? [c] : T[]
end

function ParametricLogarithmicDerivative(f::F, w::F, D::Derivation) where F<:FieldElement
    # base case f,w \in constant field, D must be the null derivation
    v = one(parent(f))
    q = rationalize_over_Int(f//w)
    m = numerator(q)
    n = denominator(q)
    n, m, v, 1
end

function ParametricLogarithmicDerivative(f::F, w::F, D::Derivation) where 
    {T<:RingElement, P<:PolyElem{T}, F<:FracElem{P}}
    # See Bronstein's book, Section 7.3, p. 253
    if degree(numerator(f))<=0 && degree(denominator(f))<=0 &&
        degree(numerator(w))<=0 && degree(denominator(w))<=0 
        #f, w \in k(t) are actually in k, so search solution not in k(t) but in k
        n, m, v, β = ParametricLogarithmicDerivative(
            constant_coefficient(numerator(f)),
            constant_coefficient(numerator(w)),
            BaseDerivation(D))
        return n, m, v + zero(f), β # make v \in k an element of k(t)
    end
    d = denominator(f)
    e = denominator(w)
    p, a = divrem(numerator(f), d)
    q, b = divrem(numerator(w), d)
    t = gen(parent(d))
    B = max(0, degree(D(t))-1)
    C = max(degree(q), degree(p))
    if degree(q)>B
        ss = one_times_n_solve([coeff(p, i) for i=B+1:C], [coeff(q, i) for i=B+1:C])
        if isempty(ss) || !isrational(ss[1])
            return 0, 0, zero(f), 0 # no solution
        end
        s = rationalize_over_Int(ss[1])
        N = numerator(s)
        M = denominator(s)
        Q, v, β = InFieldLogarithmicDerivativeOfRadical(N*f - M*w, D)
        if β<0
            return 0, 0, zero(f), β # failure 
        elseif β==1 && !iszero(Q) && !iszero(v) 
            return Q*N, Q*M, v, 1
        else
            return 0, 0, zero(f), 0 # no solution
        end
    end
    if degree(p)>B
        return 0, 0, zero(f), 0 # no solution
    end
    l = lcm(d, e)
    ln, ls = SplitFactor(l, D)
    z = ls*gcd(ln, derivative(ln))
    if degree(z)<=0 # z \in k
        return  0, 0, zero(f), -1 # failed
    end
    u1, r1 = divrem(numerator(l*f), z)
    u2, r2 = divrem(numerator(l*w), z)
    ss = one_times_n_solve([coeff(r1, i) for i=0:(degree(z)-1)], [coeff(r2, i) for i=0:(degree(z)-1)])
    if isempty(ss) || !isrational(ss[1])
        return 0, 0, zero(f), 0 # no solution
    end
    s = rationalize_over_Int(ss[1])
    M = numerator(s)
    N = denominator(s)
    Q, v, β = InFieldLogarithmicDerivativeOfRadical(N*f - M*w, D)
    if β<0
        return 0, 0, zero(f), β # failure 
    elseif β==1 && !iszero(Q) && !iszero(v) 
        return Q*N, Q*M, v, 1
    else
        return 0, 0, zero(f), 0 # no solution
    end
end

function RdeSpecialDenomExp(a::P, b::F, c::F, D::Derivation) where
    {T<:RingElement, P<:PolyElem{T}, F<:FracElem{P}}
    # See Bronstein's book, Section 6.2, p. 190
    t = gen(parent(a))
    p = t
    nb = valuation(b, p)
    nc = valuation(c, p)
    n = min(0, nc - min(0,nb))
    if nb==0 
        α = Remainder(-b//a, p)
        w = coeff(MonomialDerivative(D), 1)
        n0, m, z, β = ParametricLogarithmicDerivative(constant_coefficient(α), w, BaseDerivation(D))
        if β<0
            error("ParametricLogarithmicDerivative failed")
        end
        if  β>0 && n0==1
            n = min(n,m)
        end
    end
    N = max(0, -nb, n-nc)
    a*p^N, (b+n*a*divexact(D(p), p))*p^N, c*p^(N-n), p^(-n)
end

function RdeBoundDegreeBase(a::P, b::P, c::P, D::Derivation) where
    {T<:RingElement, P<:PolyElem{T}}
    # See Bronstein's book, Section 6.3, p. 199
    da = degree(a)
    db = degree(b)
    dc = degree(c)
    n = max(0, dc - max(db, da - 1))
    if db==da-1
        m = -leading_coefficient(b)//leading_coefficient(a)
        if is_rational(m)
            m = rationalize_over_Int(m)
            if isone(denominator(m))
                n = max(0, numerator(m), dc-db)
            end
        end
    end
    return n
end

function RdeBoundDegreeExp(a::P, b::P, c::P, D::Derivation) where
    {T<:RingElement, P<:PolyElem{T}}
    # See Bronstein's book, Section 6.3, p. 200
    da = degree(a)
    db = degree(b)
    dc = degree(c)
    n = max(0, dc - max(db, da))
    if da==db
        α = -leading_coefficient(b)//leading_coefficient(a)
        w = coeff(MonomialDerivative(D), 1)
        n0, m, z, β = ParametricLogarithmicDerivative(α, w, BaseDerivation(D))
        if β<0
            error("ParametricLogarithmicDerivative failed")
        end
        if  β>0 && n0==1
            n = max(n,m)
        end
    end
    n
end

function RdeBoundDegreeNonLinear(a::P, b::P, c::P, D::Derivation) where
    {T<:RingElement, P<:PolyElem{T}}
    # See Bronstein's book, Section 6.3, p. 201
    da = degree(a)
    db = degree(b)
    dc = degree(c)
    H = MonomialDerivative(D)
    δ = degree(H)
    λ = leading_coefficient(H)
    n = max(0, dc - max(da + δ - 1, db))
    if db==da+δ-1
        m = -leading_coefficient(b)/(λ*leading_coefficient(a))
        if is_rational(m)
            m = rationalize_over_Int(m)
            if isone(denominator(m))
                n = max(0, numerator(m), dc-db)
            end
        end
    end
    n
end

function SPDE(a::P, b::P, c::P, D::Derivation, n::Int) where
    {T<:RingElement, P<:PolyElem{T}}
    # See Bronstein's book, Section 6.4, p. 203
    ZP = zero(a)
    if n<0
        if iszero(c)
            return ZP, ZP, 0, ZP, ZP, 1 
        else
            return ZP, ZP, 0, ZP, ZP, 0 # no solution
        end
    end
    g = gcd(a, b)
    if !iszero(rem(c, g))
        return ZP, ZP, ZP, 0, ZP, 0 # no solution
    end
    a = divexact(a, g)
    b = divexact(b, g)
    c = divexact(c, g)
    if degree(a)==0
        return divexact(b, a), divexact(c, a), n, one(a), zero(a), 1
    end
    r, z = gcdx(b, a, c)
    u = SPDE(a, b + D(a), z - D(r), D, n - degree(a))
    if u[6]==0
        return u
    end
    b1, c1, m, α, β, _ = u
    b1, c1, m, a*α, a*β+r, 1
end

function PolyRischDENoCancel1(b::P, c::P, D::Derivation, n::Int=typemax(Int)) where
    {T<:RingElement, P<:PolyElem{T}} # here typemax(Int) represents +infinity
    # See Bronstein's book, Section 6.5, p. 208
    t = gen(parent(b))
    q = zero(b)
    while !iszero(c)
        m = degree(c)-degree(b)
        if n<0 || m<0 || m>n 
            return zero(b), 0 # no solution
        end
        p = (leading_coefficient(c)//leading_coefficient(b))*t^m
        q += p
        n = m - 1
        c -= D(p)+b*p
    end
    q, 1
end

function PolyRischDENoCancel2(b::P, c::P, D::Derivation, n::Int=typemax(Int)) where
    {T<:RingElement, P<:PolyElem{T}} # here typemax(Int) represents +infinity
    # See Bronstein's book, Section 6.5, p. 209
    t = gen(parent(b))
    H = MonomialDerivative(D)
    δ = degree(H)
    λ = leading_coefficient(H)
    q = zero(b)
    while !iszero(c)
        if n==0
            m=0
        else
            m = degree(c) - δ + 1
        end
        if n<0 || m<0 || m>n 
            return zero(b), zero(λ), zero(λ), 0 # no solution
        end
        if m>0
            p = (leading_coefficient(c)//(m*λ))*t^m
        else
            if degree(b)!=degree(c)
                return zero(b), zero(λ), zero(λ), 0 # no solution
            end
            if degree(b)==0
                return q, constant_coefficient(b), constant_coefficient(c), 2  
            end
            p = (leading_coefficient(c)//leading_coefficient(b)) + zero(b) #make p\in k an element of k(t)
        end
        q += p
        n = m - 1
        c -= D(p)+b*p
    end
    q, zero(λ), zero(λ), 1
end

function PolyRischDENoCancel3(b::P, c::P, D::Derivation, n::Int=typemax(Int)) where
    {T<:RingElement, P<:PolyElem{T}} # here typemax(Int) represents +infinity
    # See Bronstein's book, Section 6.4, p. 210
    t = gen(parent(b))
    H = MonomialDerivative(D)
    δ = degree(H)
    λ = leading_coefficient(H)
    M = -1
    h = -leading_coefficient(b)//λ
    if isrational(h) 
        h = rationalize_over_Int(h)
        if isone(denominator(h)) &&  h>0
            M = numerator(h)
        end
    end
    q = zero(b)
    while !iszero(c)
        m = max(M, degree(c)-δ+1)
        if n<0 || m<0 || m>n
            return zero(b), 0, zero(b), 0 # no solution
        end
        u = m*λ + leading_coefficient(b)
        if iszero(u)
            return q, m, c, 2
        end
        if m>0
            p = (leading_coefficient(c)//u)*t^m
        else
            if degree(c)!=δ-1
                return zero(b), 0, zero(b), 0 # no solution
            end
            p = (leading_coefficient(c)//leading_coefficient(b)) + zero(b) #make p\in k an element of k(t)
        end
        q += p
        n = m - 1
        c -= D(p)+b*p
    end
    q, 0, zero(b), 1
end

function PolyRischDECancelPrim(b::T, c::P, D::Derivation, n::Int=typemax(Int)) where
    {T<:RingElement, P<:PolyElem{T}} # here typemax(Int) represents +infinity
    # See Bronstein's book, Section 6.6, p. 212
    if b==0
        q0, β = InFieldDerivative(c//one(c), D) # make poly c a rational function
        q = numerator(p0)
        if β>0 && isone(denominator(q0)) && degree(q)<=n
            return q, 1
        else
            return zero(q), 0 # no solution
        end
    end
    t = gen(parent(b))
    z, β = InFieldLogarithmicDerivative(b, BaseDerivation(D)) # not yet implemented
    if β>0
        p0, β = InFieldDerivative(z*c, D)
        p = numerator(p0)
        if β>0 && isone(denominator(p0)) && degree(p)<=n
            return p//z, 1
        else
            return zero(c), 0 # no solution
        end
    end
    if iszero(c)
        return zero(c), 1 # zero is solution
    end
    if n<degree(c)
        return zero(c), 0 # no solution
    end
    q = zero(c)
    while !iszero(c)
        m = degree(c)
        if n<m
            return zero(c), 0 # no solution
        end
        s, β = RischDE(b, leading_coefficient(c), BaseDerivation(D))
        if β<=0
            return zero(c), 0 # no solution
        end
        q += s*t^m
        n = m - 1
        c -= b*s*t^m + D(s*t^m)
    end
    q, 1
end

function PolyRischDECancelExp(b::T, c::P, D::Derivation, n::Int=typemax(Int)) where
    {T<:RingElement, P<:PolyElem{T}} # here typemax(Int) represents +infinity
    # See Bronstein's book, Section 6.6, p. 213
    if b==0
        q0, β = InFieldDerivative(c//one(c), D) # make poly c a rational function
        q = numerator(p0)
        if β>0 && isone(denominator(q0)) && degree(q)<=n
            return q, 1
        else
            return zero(q), 0 # no solution
        end
    end
    t = gen(parent(b))
    H = MonomialDerivative(D)
    w = coeff(H,1) # = Dt/t for hyperexponentialm case
    n, m, z, β = ParametricLogarithmicDerivative(b, w, BaseDerivation(D))
    if β<0
        error("ParametricLogarithmicDerivative failed")
    end
    if  β>0 && n==1
        p, β = InFieldDerivative(c*z*t^m, D)
        if β<=0
            return zero(c), 0 # no solution
        end
        if !(degree(p)==0 || (degree(p)==1 && iszero(constant_coefficient(p))))
            # p not reduced
            return zero(c), 0 # no solution
        end
        q0 = p//(z*t^m)
        q = numerator(q0)
        if isone(denominator(q0)) && degree(q)<=n
            return q, 1
        else
            return zero(c), 0
        end
    end
    if iszero(c)
        return zero(c), 1 # zero is solution
    end
    if n<degree(c)
        return zero(c), 0 # no solution
    end
    q = zero(c)
    while !iszero(c)
        m = degree(c)
        if n<m
            return zero(c), 0 # no solution
        end
        s, β = RischDE(b+m*w, leading_coefficient(c), BaseDerivation(D))
        if β<=0
            return zero(c), 0 # no solution
        end
        q += s*t^m
        n = m - 1
        c -= b*s*t^m + D(s*t^m)
    end
    q, 1
end




function RischDE(f::F, g::F, D::Derivation) where 
    {T<:RingElement, P<:PolyElem{T}, F<:FracElem{P}}
    H = MonomialDerivative(D)
    δ = degree(H)
    is_d_over_dt = isa(BaseDerivation(D), BasicDerivation) #D=d/dt ?
    primitive_case = degree(H)==0  # includes D=D/dt case
    hyperexponential_case = degree(H)==1 && izero(constant_coefficient(H))
    #hypertangent_case = ... TODO
    #if !(primitive_case || hyperexponential_case || hypertangent_case )
    if !(hyperexponential_case)
        error("RischDE not implemented for Dt=$H")
    end
    q = WeakNormalizer(f, D)
    f1 = f - D(q)//q
    g1 = q*g
    a, b, c, h, success = RdeNormalDenominator(f1, g1, D)
    success>=1 || return zero(f), zero(f), 0
    if primitive_case
        a1 = a
        b1 = numerator(b)
        c1 = numerator(c)
        h1 = one(c1)
        if is_d_over_dt
            n = RdeBoundDegreeBase(a1, b1, c1) 
        else
            n = RdeBoundDegreePrim(a1, b1, c1, D) # not yet implemented
        end
    elseif hyperexponential_case
        a1, b1, c1, h1 =  RdeSpecialDenomExp(a, b, c, D)
        n = RdeBoundDegreeExp(a1, b1, c1, D) 
    elseif  hypertangent_case
        a1, b1, c1, h1  =  RdeSpecialDenomTan(a, b, c, D) # not yet implemented
        n = RdeBoundDegreeNonLinear(a1, b1, c1, D)
    end
    b2, c2, α, β, success = SPDE(a1, b1, c1, D, n)
    success>=1 || return zero(f), zero(f), 0
    if  is_d_over_dt || degree(b2)>max(0, δ-1)
        z, success = PolyRischDENoCancel1(b2, c2, D, n)
    elseif degree(b2)<δ-1 && (is_d_over_dt || δ>=2)
        z, b3, c3, success = PolyRischDENoCancel2(b2, c2, D, n)
        if success==2
            z1, success = RischDE(b3, c3, BaseDerivation(D))
            success>=1 || return zero(f), zero(f), success
            z = z1 - z
        end
    elseif δ>=2 && degree(b2)==δ-1
        z, m, c3, success = PolyRischDENoCancel3(b2, c2, D, n) 
        # TODO: handle case success == 2
    elseif primitive_case
        z, success = PolyRischDECancelPrim(constant_coefficient(b2), c2, D, n)
    elseif hyperexponential_case
        z, success = PolyRischDECancelExp(constant_coefficient(b2), c2, D, n) 
    elseif hypertangent_case
            # TODO....
    end
    success>=1 || return zero(f), zero(f), success
    (α*z+β)//(q*h*h1), 1
end

