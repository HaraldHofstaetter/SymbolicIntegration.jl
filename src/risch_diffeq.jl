# This file contains algorithms needed for the solution of 
# the Risch differential equation from chapter 6 of the book
#
#    Manuel Bronstein, Symbolic Integration I: Transcendental Functions,
#    2nd ed., Springer 2005. 
#


using Logging


function WeakNormalizer(f::F, D::Derivation) where 
    {P<:PolyElem, F<:FracElem{P}}
    # See Bronstein's book, Section 6.1, p. 183
    iscompatible(f, D) || error("rational function f must be in the domain of derivation D")
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
    {P<:PolyElem, F<:FracElem{P}}
    # See Bronstein's book, Section 6.1, p. 185
    iscompatible(f, D) && iscompatible(g, D) || 
        error("rational functions f and g must be in the domain of derivation D")
    # Note: f must be weakly normalized which we do not check. It is recommended
    # to use this function only for rational functions f which were computed by WeakNormalizer. 
    (dn, ds) = SplitFactor(denominator(f), D)
    (en, es) = SplitFactor(denominator(g), D)
    p = gcd(dn, en)
    h = divexact(gcd(en, derivative(en)), gcd(p, derivative(p)))
    if !iszero(rem(dn*h^2, en))
        @info "RdeNormalDenominator: no solution"
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
    {P<:PolyElem, F<:FracElem{P}}
    # See Bronstein's book, Section 7.3, p. 253
    Z = zero(f)
    if degree(numerator(f))<=0 && degree(denominator(f))<=0 &&
        degree(numerator(w))<=0 && degree(denominator(w))<=0 
        #f, w \in k(t) are actually in k, so search solution not in k(t) but in k
        n, m, v, β = ParametricLogarithmicDerivative(
            constant_coefficient(numerator(f)),
            constant_coefficient(numerator(w)),
            BaseDerivation(D))
        return n, m, v + Z, β # make v \in k an element of k(t)
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
        if isempty(ss) 
            @info "ParametricLogarithmicDerivative: no solution, one_times_n_solve returned no solution"
            return 0, 0, Z, 0 
        end
        if !isrational(ss[1])
            @info "ParametricLogarithmicDerivative: no solution, solution returned by one_times_n_solve was not rational"
            return 0, 0, Z, 0 
        end
        s = rationalize_over_Int(ss[1])
        N = numerator(s)
        M = denominator(s)
        Q, v, β = InFieldLogarithmicDerivativeOfRadical(N*f - M*w, D)
        if β>=1 && !iszero(Q) && !iszero(v) 
            return Q*N, Q*M, v, 1
        else
            @info "ParametricLogarithmicDerivative: no solution, no nonzero solution v∈k(t) of Q*(N*f-M*w)==D(v)//v found for any nonzero integer Q"
            return 0, 0, Z, min(β, 0)  
        end
    end
    if degree(p)>B
        @info "ParametricLogarithmicDerivative: no solution, degree(p) was > B"
        return 0, 0, Z, 0 
    end
    l = lcm(d, e)
    ln, ls = SplitFactor(l, D)
    z = ls*gcd(ln, derivative(ln))
    if degree(z)<=0 # z \in k
        @error "ParametricLogarithmicDerivative: failed, z was not ∈k"
        return  0, 0, Z, -1 
    end
    u1, r1 = divrem(numerator(l*f), z)
    u2, r2 = divrem(numerator(l*w), z)
    ss = one_times_n_solve([coeff(r1, i) for i=0:(degree(z)-1)], [coeff(r2, i) for i=0:(degree(z)-1)])
    if isempty(ss) 
        @info "ParametricLogarithmicDerivative: no solution, one_times_n_solve returned no solution"
        return 0, 0, Z, 0 
    end
    if !isrational(ss[1])
        @info "ParametricLogarithmicDerivative: no solution, solution returned by one_times_n_solve was not rational"
        return 0, 0, Z, 0 
    end
    s = rationalize_over_Int(ss[1])
    M = numerator(s)
    N = denominator(s)
    Q, v, β = InFieldLogarithmicDerivativeOfRadical(N*f - M*w, D)
    if β>=1 && !iszero(Q) && !iszero(v) 
        return Q*N, Q*M, v, 1
    else
        @info "ParametricLogarithmicDerivative: no solution, no nonzero solution v∈k(t) of Q*(N*f-M*w)==D(v)//v found for any nonzero integer Q"
        return 0, 0, Z, min(β, 0)  
    end
end

function RdeSpecialDenomExp(a::P, b::F, c::F, D::Derivation) where
    {P<:PolyElem, F<:FracElem{P}}
    # See Bronstein's book, Section 6.2, p. 190
    ishyperexponential(D) ||
        error("monomial of derivation D must be hyperexponential")
    iscompatible(a, D) && iscompatible(b, D) && iscompatible(c, D) || 
        error("polynomial a and rational functions b and c must be in the domain of derivation D")
    isreduced(b, D) && isreduced(c, D) || 
        error("rational functions b and c must be reduced with respect to derivation D")
    t = gen(parent(a))
    degree(gcd(t, a))==0 || error("gcd(a, t) must be == 1")
    p = t
    nb = valuation(b, p)
    nc = valuation(c, p)
    n = min(0, nc - min(0, nb))
    if nb==0 
        α = Remainder(-b//a, p)
        w = coeff(MonomialDerivative(D), 1)
        n0, m, z, β = ParametricLogarithmicDerivative(constant_coefficient(α), w, BaseDerivation(D))
        if β<0
            error("ParametricLogarithmicDerivative failed")
        end
        if  β>0 && n0==1 && !iszero(z)
            n = min(n, m)
        end
    end
    N = max(0, -nb, n-nc)
    p_power_N = p^N
    a*p_power_N, (b+n*a*divexact(D(p), p))*p_power_N, c*p^(N-n), p^(-n)
end

function RdeBoundDegreePrim(a::P, b::P, c::P, D::Derivation) where P<:PolyElem
    # See Bronstein's book, Section 6.3, p. 200
    isprimitive(D) ||
        error("monomial of derivation D must be primitive")
    iscompatible(a, D) && iscompatible(b, D) && iscompatible(c, D) || 
        error("polynomials a, b, and c must be in the domain of derivation D")
    !iszero(a) || error("polynomial a must be nonzero")
    da = degree(a)
    db = degree(b)
    dc = degree(c)
    if db>da 
        n = max(0, dc-db)
    else
        n = max(0, dc-da+1)
    end
    if db==da-1
        α = -leading_coefficient(b)//leading_coefficient(a)
        z, m0, ρ = LimitedIntegrate(α, leading_coefficient(D), BaseDerivative(D)) # not yet implemented
        if ρ>0 && is_rational(m0)
            m = rationalize_over_Int(m0)
            if denominator(m)==1
                n = max(n, numerator(m))
            end
        end
    end
    D0 = BaseDerivative(D)
    if db==da
        α = -leading_coefficient(b)//leading_coefficient(a)
        z, ρ = InFieldDerivative(α)
        if ρ>0 && !iszero(z)
            β = -leading_coefficient(a*D0(z)+b*z)//(z*leading_coefficient(a))
            w, m0, ρ = LimitedIntegrate(β, leading_coefficient(D), D0) # not yet implemented
            if ρ>0 && is_rational(m0)
                m = rationalize_over_Int(m0)
                if denominator(m)==1
                    n = max(n, numerator(m))
                end
            end
        end
    end
    n
end

function RdeBoundDegreeBase(a::P, b::P, c::P) where P<:PolyElem
    # See Bronstein's book, Section 6.3, p. 199
    !iszero(a) || error("polynomial a must be nonzero")
    da = degree(a)
    db = degree(b)
    dc = degree(c)
    n = max(0, dc - max(db, da - 1))
    if db==da-1
        m0 = -leading_coefficient(b)//leading_coefficient(a)
        if is_rational(m0)
            m = rationalize_over_Int(m0)
            if isone(denominator(m))
                n = max(0, numerator(m), dc - db)
            end
        end
    end
    return n
end

function RdeBoundDegreeExp(a::P, b::P, c::P, D::Derivation) where P<:PolyElem
    # See Bronstein's book, Section 6.3, p. 200
    ishyperexponential(D) ||
        error("monomial of derivation D must be hyperexponential")
    iscompatible(a, D) && iscompatible(b, D) && iscompatible(c, D) || 
        error("polynomials a, b, and c must be in the domain of derivation D")
    !iszero(a) || error("polynomial a must be nonzero")
    da = degree(a)
    db = degree(b)
    dc = degree(c)
    n = max(0, dc - max(db, da))
    if da==db
        α = -leading_coefficient(b)//leading_coefficient(a)
        w = coeff(MonomialDerivative(D), 1)
        n0, m, z, ρ = ParametricLogarithmicDerivative(α, w, BaseDerivation(D))
        if ρ<0
            error("ParametricLogarithmicDerivative failed")
        end
        if  ρ>0 && n0==1 && !iszero(z)
            n = max(n, m)
        end
    end
    n
end

function RdeBoundDegreeNonLinear(a::P, b::P, c::P, D::Derivation) where P<:PolyElem
    # See Bronstein's book, Section 6.3, p. 201
    isnonlinear(D) ||
        error("monomial of derivation D must be nonlinear")
    iscompatible(a, D) && iscompatible(b, D) && iscompatible(c, D) || 
        error("polynomials a, b, and c must be in the domain of derivation D")
    !iszero(a) || error("polynomial a must be nonzero")
    da = degree(a)
    db = degree(b)
    dc = degree(c)
    δ = degree(D)
    λ = leading_coefficient(D)
    n = max(0, dc - max(da + δ - 1, db))
    if db==da+δ-1
        m0 = -leading_coefficient(b)/(λ*leading_coefficient(a))
        if is_rational(m0)
            m = rationalize_over_Int(m0)
            if isone(denominator(m))
                n = max(0, numerator(m), dc - db)
            end
        end
    end
    n
end

function SPDE(a::P, b::P, c::P, D::Derivation, n::Int) where P<:PolyElem
    # See Bronstein's book, Section 6.4, p. 203
    iscompatible(a, D) && iscompatible(b, D) && iscompatible(c, D) || 
        error("polynomials a, b, and c must be in the domain of derivation D")
    !iszero(a) || error("polynomial a must be nonzero")
    Z = zero(a)
    if n<0
        if iszero(c)
            return Z, Z, 0, Z, Z, 1 
        else
            @info "SPDE: no solution, n was < 0 but c != 0"
            return Z, Z, 0, Z, Z, 0 
        end
    end
    g = gcd(a, b)
    if !iszero(rem(c, g))
        @info "SPDE: no solution, c was not divisible by g"
        return Z, Z, Z, 0, Z, 0 
    end
    a = divexact(a, g)
    b = divexact(b, g)
    c = divexact(c, g)
    if degree(a)==0
        return divexact(b, a), divexact(c, a), n, one(a), Z, 1
    end
    r, z = gcdx(b, a, c)
    u = SPDE(a, b + D(a), z - D(r), D, n - degree(a))
    if u[6]==0
        @info "SPDE: no solution, recursive call of itself returned no solution"
        return u
    end
    b1, c1, m, α, β, _ = u
    b1, c1, m, a*α, a*β+r, 1
end

function PolyRischDENoCancel1(b::P, c::P, D::Derivation, n::Int=typemax(Int)) where
    P<:PolyElem # here typemax(Int) represents +infinity
    # See Bronstein's book, Section 6.5, p. 208
    iscompatible(b, D) && iscompatible(c, D) || 
        error("polynomials b and c must be in the domain of derivation D")
    !iszero(b) || error("polynomial b must be nonzero")
    isbasic(D) || degree(b)>max(0, degree(D)-1) || 
        error("either derivation D must be basic or degree(b)>max(0, degree(D)-1)")
    Z  = zero(b)
    t = gen(parent(b))
    q = Z 
    while !iszero(c)
        m = degree(c)-degree(b)
        if n<0 || m<0 || m>n 
            @info "PolyRischDENoCancel1: no solution"
            return Z, 0 # no solution
        end
        p = (leading_coefficient(c)//leading_coefficient(b))*t^m
        q += p
        n = m - 1
        c -= D(p)+b*p
    end
    q, 1
end

function PolyRischDENoCancel2(b::P, c::P, D::Derivation, n::Int=typemax(Int)) where
    P<:PolyElem # here typemax(Int) represents +infinity
    # See Bronstein's book, Section 6.5, p. 209
    iscompatible(b, D) && iscompatible(c, D) || 
        error("polynomials b and c must be in the domain of derivation D")
    δ = degree(D)
    iszero(b) || degree(b)<δ-1 || error("degree(b)<degree(D)-1 must hold")
    # Note: In Bronstein's book the convention degree(0)=-infinity is used,
    # but in AbstractAlgebra we have degree(0)=-1, so we have to explicitly
    # include the clause iszero(b) in the above condition.
    isbasic(D) || δ>=2 || 
        error("either derivation D must be basic or degree(D)>=2")
    t = gen(parent(b))
    λ = leading_coefficient(D)
    Z  = zero(b)
    Z0 = zero(λ)
    q = Z
    while !iszero(c)
        if n==0
            m=0
        else
            m = degree(c) - δ + 1
        end
        if n<0 || m<0 || m>n 
            @info "PolyRischDENoCancel2: no solution"
            return Z, Z0, Z0, 0 
        end
        if m>0
            p = (leading_coefficient(c)//(m*λ))*t^m
        else
            if degree(b)!=degree(c)
                @info "PolyRischDENoCancel2: no solution"
                return Z, Z0, Z0, 0 
            end
            if degree(b)==0
                return q, constant_coefficient(b), constant_coefficient(c), 2  
            end
            p = (leading_coefficient(c)//leading_coefficient(b)) + Z #make p\in k an element of k(t)
        end
        q += p
        n = m - 1
        c -= D(p)+b*p
    end
    q, Z0, Z0, 1
end

function PolyRischDENoCancel3(b::P, c::P, D::Derivation, n::Int=typemax(Int)) where
    P<:PolyElem # here typemax(Int) represents +infinity
    # See Bronstein's book, Section 6.4, p. 210
    iscompatible(b, D) && iscompatible(c, D) || 
        error("polynomials b and c must be in the domain of derivation D")
    δ = degree(D)
    δ>=2 || error("degree(D) must be >= 2")
    degree(b)==δ-1 || error("degree(b)==degree(D)-1 must hold")
    Z = zero(b)
    t = gen(parent(b))
    λ = leading_coefficient(D)
    M = -1
    h = -leading_coefficient(b)//λ
    if isrational(h) 
        h = rationalize_over_Int(h)
        if isone(denominator(h)) &&  h>0
            M = numerator(h)
        end
    end
    q = Z
    while !iszero(c)
        m = max(M, degree(c)-δ+1)
        if n<0 || m<0 || m>n
            @info "PolyRischDENoCancel3: no solution"
            return Z, 0, Z, 0 
        end
        u = m*λ + leading_coefficient(b)
        if iszero(u)
            return q, m, c, 2
        end
        if m>0
            p = (leading_coefficient(c)//u)*t^m
        else
            if degree(c)!=δ-1
                @info "PolyRischDENoCancel3: no solution"
                return Z, 0, Z, 0 
            end
            p = (leading_coefficient(c)//leading_coefficient(b)) + Z #make p\in k an element of k[t]
        end
        q += p
        n = m - 1
        c -= D(p)+b*p
    end
    q, 0, Z, 1
end

function PolyRischDECancelPrim(b::T, c::P, D::Derivation, n::Int=typemax(Int)) where
    {T<:RingElement, P<:PolyElem{T}} # here typemax(Int) represents +infinity
    # See Bronstein's book, Section 6.6, p. 212
    isprimitive(D) ||
        error("monomial of derivation D must be primitive")
    D0 = BaseDerivation(D)
    iscompatible(b, D0) || 
        error("coefficient b must be in the domain of the base derivation of D")
    iscompatible(c, D) || 
        error("polynomial c must be in the domain of derivation D")
    Z = zero(c)
    if b==0
        q0, β = InFieldDerivative(c//one(c), D) # make poly c a rational function
        q = numerator(p0)
        if β<=0 || !isone(denominator(q0)) || degree(q)>n
            @info "PolyRischDECancelPrim: no solution"
            return Z, 0 
        end
        return q, 1
    end
    t = gen(parent(c))
    z, β = InFieldLogarithmicDerivative(b, D0) 
    if β>0
        p0, β = InFieldDerivative(z*c, D)
        p = numerator(p0)
        if β<=0 || !isone(denominator(p0)) || degree(p)>n
            @info "PolyRischDECancelPrim: no solution"
            return Z, 0 
        end
        return p//z, 1
    end
    if iszero(c)
        return Z, 1 # zero is solution
    end
    if n<degree(c)
        @info "PolyRischDECancelPrim: no solution"
        return Z, 0 
    end
    q = Z
    while !iszero(c)
        m = degree(c)
        if n<m
            @info "PolyRischDECancelPrim: no solution"
            return Z, 0 # no solution
        end
        s, β = RischDE(b, leading_coefficient(c), D0)
        if β<=0
            @info "PolyRischDECancelPrim: no solution"
            return Z, 0 
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
    ishyperexponential(D) ||
        error("monomial of derivation D must be hyperexponential")
    D0 = BaseDerivation(D)
    iscompatible(b, D0) || 
        error("coefficient b must be in the domain of the base derivation of D")
    iscompatible(c, D) || 
        error("polynomial c must be in the domain of derivation D")
    Z = zero(c)
    if b==0
        q0, β = InFieldDerivative(c//one(c), D) # make poly c a rational function
        q = numerator(q0)
        if β<=0 || !isone(denominator(q0)) || degree(q)>n
            @info "PolyRischDECancelExp: no solution"
            return Z, 0 
        end
        return q, 1
    end
    t = gen(parent(c))
    H = MonomialDerivative(D)
    w = coeff(H,1) # = Dt/t for hyperexponentialm case
    n, m, z, β = ParametricLogarithmicDerivative(b, w, D0)
    if β<0
        error("ParametricLogarithmicDerivative failed")
    end
    if  β>0 && n==1
        p, β = InFieldDerivative(c*z*t^m, D)
        if β<=0
            @info "PolyRischDECancelExp: no solution"
            return Z, 0 
        end
        if !isreduced(p, D)
            @info "PolyRischDECancelExp: no solution"
            return Z, 0 
        end
        q0 = p//(z*t^m)
        q = numerator(q0)
        if isone(denominator(q0)) && degree(q)<=n
            return q, 1
        else
            @info "PolyRischDECancelExp: no solution"
            return Z, 0
        end
    end
    if iszero(c)
        return Z, 1 # zero is solution
    end
    if n<degree(c)
        @info "PolyRischDECancelExp: no solution"
        return Z, 0 
    end
    q = Z
    while !iszero(c)
        m = degree(c)
        if n<m
            @info "PolyRischDECancelExp: no solution"
            return Z, 0 # no solution
        end
        s, β = RischDE(b+m*w, leading_coefficient(c), D0)
        if β<=0
            @info "PolyRischDECancelExp: no solution"
            return Z, 0 # no solution
        end
        q += s*t^m
        n = m - 1
        c -= b*s*t^m + D(s*t^m)
    end
    q, 1
end


function RischDE(f::F, g::F, D::NullDerivation) where F<:FieldElem
     #base case => pure algebra problem ...
     iscompatible(f, D) && iscompatible(g,D) || 
        error("coefficients f and g must be in the domain of the base derivation of D") 
    if iszero(f)
        if iszero(g)
            return zero(parent(f)), 1
        else
            @info "RischDE, base case: no solution, f was == 0 and g != 0"
            return zero(parent(f)), 0
        end
    else
        return g//f, 1
    end
 end

function RischDE(f::F, g::F, D::Derivation) where 
    {P<:PolyElem, F<:FracElem{P}}
    iscompatible(f, D) && iscompatible(g, D) || 
        error("rational functions f and g must be in the domain of derivation D")
    t = gen(base_ring(parent(f)))
    Z = zero(f)
    H = MonomialDerivative(D)
    δ = degree(D)
    basic_case = isbasic(D) 
    primitive_case = isprimitive(D)  
    hyperexponential_case = ishyperexponential(D)
    hypertangent_case = ishypertangent(D)  
    #if !(primitive_case || hyperexponential_case || hypertangent_case )
    if !(hyperexponential_case)
        error("RischDE not implemented for Dt=$H")
    end
    q = WeakNormalizer(f, D)
    f = f - D(q)//q
    g = q*g
    a, b, c, h, success = RdeNormalDenominator(f, g, D)
    success>=1 || return Z, Z, 0
    if primitive_case
        b = numerator(b)
        c = numerator(c)
        h1 = one(b)
        if basic_case
            n = RdeBoundDegreeBase(a, b, c) 
        else
            n = RdeBoundDegreePrim(a, b, c, D)
        end
    elseif hyperexponential_case
        d = gcd(a, t)
        if !isone(d)
            a = divexact(a, d)
            b = b//d
            c = c//d
        end
        a, b, c, h1 =  RdeSpecialDenomExp(a, b, c, D)
        n = RdeBoundDegreeExp(a, b, c, D) 
    elseif hypertangent_case
        # TODO
        a, b, c, h  =  RdeSpecialDenomTan(a, b, c, D) # not yet implemented
        n = RdeBoundDegreeNonLinear(a, b, c, D)
    else
        @assert false # never reach this point
    end
    b, c, α, β, success = SPDE(a, b, c, D, n)
    success>=1 || return Z, Z, 0
    if !iszero(b) && (basic_case || degree(b)>max(0, δ-1))
        z, success = PolyRischDENoCancel1(b, c, D, n)
    elseif (iszero(b) || degree(b)<δ-1) && (basic_case || δ>=2)
        z, b, c, success = PolyRischDENoCancel2(b, c, D, n)
        if success==2
            z1, success = RischDE(b, c, BaseDerivation(D))
            success>=1 || return Z, Z, success
            z = z1 - z
        end
    elseif δ>=2 && degree(b)==δ-1
        z, m, c, success = PolyRischDENoCancel3(b, c, D, n) 
        if success==2
            if hypertangent_case
            #  ... = PolyRischDECancelTan(...) TODO!
            end
        else
            @assert false # never reach this point
        end 
    # At this point only δ<=1, D!=d/dt is possible;
    # this is compatible with primitive and hyperexponential only.
    elseif primitive_case
        z, success = PolyRischDECancelPrim(constant_coefficient(b), c, D, n)
    elseif hyperexponential_case
        z, success = PolyRischDECancelExp(constant_coefficient(b), c, D, n) 
    else
        @assert false # never reach this point
    end
    success>=1 || return Z, Z, success
    (α*z+β)//(q*h*h1), 1
end

