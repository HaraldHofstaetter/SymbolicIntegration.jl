using Nemo

isrational(x::fmpq) = true # Nemo rational type

isrational(x::T) where T<:Integer = true

isrational(x::T) where T<:Rational = true

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
    ns = [numerator(rationalize(x)) for x in roots(r) if 
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
        return zero(h), zero(f), zero(f), zero(h), false
    end
    dn*h, dn*h*f-dn*D(h), dn*h^2*g, h, true
end


function Remainder(x::FracElem{T}, a::T) where T<:RingElement
    # See Bronstein's book, Section 4.2, p. 115
    b, c = gcdx(a, denominator(x), one(a))
    q, r = divrem(numerator(x)*c, a)
    r
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

function LogarithmicDerivativeOfRadical(f::F, D::Derivation) where 
    {T<:RingElement, P<:PolyElem{T}, F<:FracElem{P}}
    # See Bronstein's book, Section 5.12, p. 177
    RS, β = ResidueReduce(f, D)
    # as ... roots of the RS[i].R which are rationals 
    as = [rationalize(-constant_coefficient(RS[i].R)//leading_coefficient(RS[i].R)) for i = length(RS)]
    m = gcd(denominator.(as))
    gs = [map_coefficients(c->c(as[i]), RS[i].S) for i=1:length(RS)]
    dg = sum([as[i]*D(gs[i])//gs[i] for i=1:length(RS)])
    v = prod([ gs[i]^numerator(m*as[1]) for i=1:length(RS)])
    p = f - dg
    if iszero(p)
        return m, v, 1
    end
    H = MonomialDerivative(D)
    if degree(H) <= 0 # basic derivation or primitive case
        # p \in k, p0 = p as element of k
        p0 = constant_coefficient(numerator(p))
        n, u, success = LogarithmicDerivativeOfRadical(p0, BaseDerivation(D))
        if success<=0
            return 0, zero(f), success
        end
        N = lcm(n, m)
        U = v^div(N, m)*u^div(N, n)
        return N, U, 1
    end
    if degree(H)==1 && iszero(constant_coeffizient(H)) # hyperexponential case
        # p \in k, p0 = p as element of k
        p0 = constant_coefficient(numerator(p))
        w = coefficient(H, 1)
        n, e, u, success = ParametricLogarithmicDerivative(p0, w, BaseDerivation(D))  
        if success<=0
            return 0, zero(f), success
        end
        N = lcm(n, m)
        t = gen(parent(numerator(f)))
        U = v^div(N, m)*u^div(N, n)*t^div(e*N, n)
        return N, U, 1
    end
    # TODO: hypertangent case 
    0, zero(f), -1 # failure, not implemented for given monomial 
end

function ParametricLogarithmicDerivative(f::F, w::F, D::Derivation) where F<:FieldElement
    # base case f,w \in constant field, D must be the null derivation
    v = one(parent(f))
    q = convert(Rational{BigInt}, f//w)
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
        n, m, v, success = ParametricLogarithmicDerivative(
            constant_coefficient(numerator(f)),
            constant_coefficient(numerator(w)),
            BaseDerivation(D))
        return n, m, v + zero(f), success # make v \in k an element of k(t)
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
        s = rationalize(ss[1])
        N = numerator(s)
        M = denominator(s)
        Q, v, success = LogarithmicDerivativeOfRadical(N*f - M*w, D)
        if success<0
            return 0, 0, zero(f), success # failure 
        elseif success==1 && !iszero(Q) && !iszero(v) 
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
    s = rationalize(ss[1])
    M = numerator(s)
    N = denominator(s)
    Q, v, success = LogarithmicDerivativeOfRadical(N*f - M*w, D)
    if success<0
        return 0, 0, zero(f), success # failure 
    elseif success==1 && !iszero(Q) && !iszero(v) 
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
        if is_rational(m) && isone(denominator(rationalize(m)))
            n = max(0, m, dc-db)
        end
    end
    n
end


