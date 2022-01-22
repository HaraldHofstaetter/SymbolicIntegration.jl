# This file contains algorithms needed for the solution of 
# the Risch differential equation from chapter 6 of the book
#
#    Manuel Bronstein, Symbolic Integration I: Transcendental Functions,
#    2nd ed., Springer 2005. 
#

using Logging


"""
    WeakNormalizer(f, D) -> q

Weak normalization.

Given a field `k`, a derivation `D` on `k[t]` and `f` in `k(t)`, return
`q` in `k[t]` such that `f-D(q)/q` is weakly normalized with respect to D.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.1, p. 183.
"""
function WeakNormalizer(f::F, D::Derivation) where 
    {P<:PolyElem, F<:FracElem{P}}
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
    D1 = CoefficientLiftingDerivation(kz, BaseDerivation(D)) # dummy derivation compatible with r
    ns = [numerator(rationalize_over_Int(x)) for x in constant_roots(r, D1) if
            isrational(x) && isone(denominator(x)) && x>0]
    if isempty(ns)
        return one(numerator(f))
    end
    prod([gcd(a - n*dd1, d1)^n for n in ns])
end

"""
    RdeNormalDenominator(f, g, D) -> (a, b, c, h, ρ)

Normal part of the denomninator.

Given a field `k`, a derivation `D` on `k[t]`, `f`, `g` in `k(t)`
with `f` weakly normalized with respect to `t`, return 
either `ρ=0`, in which case the equation `D(y)+f*y=g` has no solution in `k⟨t⟩`,
or `ρ=1`, `a`, `h` in `k[t]` and `b`, `c` in `k⟨t⟩`, such that for any  solution `y`
in `k(t)` of `D(y)+f*y=g`, `q=y*h` in `k⟨t⟩` satisfies `a*D(q)+b*q=c`.

(Here, `k⟨t⟩` denotes the elements of `k(t)` which are reduced w.r.t. `D`.)

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.1, p. 185.
"""
function RdeNormalDenominator(f::F, g::F, D::Derivation) where 
    {P<:PolyElem, F<:FracElem{P}}
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

"""
    ParametricLogarithmicDerivative(f, w, D) -> (n, m, v, ρ)

Parametric logarithmic derivative heuristic.

Given a field `k`, a derivation `D` on `k[t]`, `f` in `k(t)` and `w=D(θ)/θ` in `k` such that `θ` 
is a hyperexponential monomial over `k(t)`, return either `ρ=-1`, in which case the algoithm 
failed, or `ρ=0`, in which case `n*f=D(v)/v+m*D(θ)/θ` has no solution `v≠0` in `k(t)` and 
integers `n≠0` and `m`, or `ρ=1` and a solution `n`, `m`, `v` of that equation.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 7.3, p. 253.
"""
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

"""
    RdeSpecialDenomExp(a, b, c, D) -> (A, B, C, h)

Special part of the denominator - hyperexponential case.

Given a field `k`, a derivation `D` on `k[t]`, `a` in `k[t]`, `b`, `c` in `k⟨t⟩`
with `D(t)/t` in `k`, `a≠0` and `gcd(a,t)=1`, return  `A`, `B`, `C`, `h` in `k[t]` such that
for any solution `q` in `k⟨t⟩` of `a*D(q)+b*q=c`, `r=q*h` in `k[t]` satisfies `A*D(r)+B*r=C`.     

(Here, `k⟨t⟩` denotes the elements of `k(t)` which are reduced w.r.t. `D`.)

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.2, p. 190.
"""
function RdeSpecialDenomExp(a::P, b::F, c::F, D::Derivation) where
    {P<:PolyElem, F<:FracElem{P}}    
    !iszero(a) || error("a must be != 0")
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
    b1 = (b+n*a*divexact(D(p), p))*p_power_N
    @assert isone(denominator(b1))
    c1 = c*p^(N-n)
    @assert isone(denominator(c1))
    a*p_power_N, numerator(b1), numerator(c1), p^(-n)
end

"""
    RdeSpecialDenominator(a, b, c, D) -> (A, B, C, h)

Special part of the denominator.

Given a field `k`, a derivation `D` on `k[t]`, `a` in `k[t]`, `b`, `c` in `k⟨t⟩`
with `a≠0` return  `A`, `B`, `C`, `h` in `k[t]` such that
for any solution `q` in `k⟨t⟩` of `a*D(q)+b*q=c`, `r=q*h` in `k[t]` satisfies `A*D(r)+B*r=C`.     

(Here, `k⟨t⟩` denotes the elements of `k(t)` which are reduced w.r.t. `D`.)

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.2, p. 186.
"""
function RdeSpecialDenominator(a::P, b::F, c::F, D::Derivation) where
    {P<:PolyElem, F<:FracElem{P}}
    !iszero(a) || error("a must be != 0")
    iscompatible(a, D) && iscompatible(b, D) && iscompatible(c, D) || 
        error("polynomial a and rational functions b and c must be in the domain of derivation D")
    isreduced(b, D) && isreduced(c, D) || 
        error("rational functions b and c must be reduced with respect to derivation D")        
    if isprimitive(D)
        @assert isone(denominator(b))
        @assert isone(denominator(c))
        return a, numerator(b), numerator(c), one(b)
    elseif ishyperexponential(D)
        t = gen(parent(a))
        d = gcd(a, t)
        t = gen(parent(a))
        a = divexact(a, d)
        b = b//d
        c = c//d
        return  RdeSpecialDenomExp(a, b, c, D)
    elseif ishypertangent(D)
        @error "not implemented"        
        throw(ErrorException)
        #return RdeSpecialDenomTan(a, b, c, D) # not yet implemented
    else
        @error "not implemented"        
        throw(ErrorException)
    end    
end

"""
    RdeBoundDegreePrim(a, b, c, D) -> n

Bound on polynomial solutions - primitive case.

Given a field `k`, a derivation `D` on `k[t]` and `a`, `b`, `c` in `k[t]`  
with `D(t)` in `k` and `a≠0`, return integer `n` such that `degree(q)≤n`
for any solution `q` in `k[t]` of `a*D(q)+b*q=c`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.3, p. 198.
"""
function RdeBoundDegreePrim(a::P, b::P, c::P, D::Derivation) where P<:PolyElem
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
    D0 = BaseDerivation(D)
    if db==da
        α = -leading_coefficient(b)//leading_coefficient(a)
        z, ρ = InFieldDerivative(α, D0)
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

"""
    RdeBoundDegreeBase(a, b, c) -> n

Bound on polynomial solutions - base case.

Given a field `k` and  `a`, `b`, `c` in `k[t]`  with `a≠0`, return integer `n`
such that `degree(q)≤n` for any solution `q` in `k[t]` of `a*(d/dt)(q)+b*q=c`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.3, p. 199.
"""
function RdeBoundDegreeBase(a::P, b::P, c::P) where P<:PolyElem
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

"""
    RdeBoundDegreeExp(a, b, c, D) -> n

Bound on polynomial solutions - hyperexponential case.

Given a field `k`, a derivation `D` on `k[t]` and `a`, `b`, `c` in `k[t]`  
with `D(t)/t` in `k` and `a≠0`, return integer `n` such that `degree(q)≤n`
for any solution `q` in `k[t]` of `a*D(q)+b*q=c`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.3, p. 200.
"""
function RdeBoundDegreeExp(a::P, b::P, c::P, D::Derivation) where P<:PolyElem    
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

"""
    RdeBoundDegreeNonLinear(a, b, c, D) -> n

Bound on polynomial solutions - nonlinear case.

Given a field `k`, a derivation `D` on `k[t]` and `a`, `b`, `c` in `k[t]`  
with `degree(D(t))≥2` and `a≠0`, return integer `n` such that `degree(q)≤n`
for any solution `q` in `k[t]` of `a*D(q)+b*q=c`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.3, p. 201.
"""
function RdeBoundDegreeNonLinear(a::P, b::P, c::P, D::Derivation) where P<:PolyElem
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

"""
    RdeBoundDegree(a, b, c, D) -> n

Bound on polynomial solutions.

Given a field `k`, a derivation `D` on `k[t]` and `a`, `b`, `c` in `k[t]`  
with `a≠0`, return integer `n` such that `degree(q)≤n`
for any solution `q` in `k[t]` of `a*D(q)+b*q=c`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.3, p. 193.
"""
function RdeBoundDegree(a::P, b::P, c::P, D::Derivation) where P<:PolyElem
    iscompatible(a, D) && iscompatible(b, D) && iscompatible(c, D) || 
        error("polynomials a, b, and c must be in the domain of derivation D")
    !iszero(a) || error("polynomial a must be nonzero")
    if isbasic(D) || (isprimitive(D) && isone(MonomialDerivative(D)))
        return RdeBoundDegreeBase(a, b, c) 
    elseif isprimitive(D)
        return RdeBoundDegreePrim(a, b, c, D)
    elseif ishyperexponential(D)
        return RdeBoundDegreeExp(a, b, c, D) 
    elseif isnonlinear(D)
        return RdeBoundDegreeNonLinear(a, b, c, D)
    else
        @error "not implemented"
        throw(ErrorException)
    end
end

"""
    SPDE(a, b, c, D, n) -> (B, C, m, α, β, ρ)

Rothstein's Special Polynomial Differential Equation algorithm.

Given a field `k`, a derivation `D` on `k[t]`, an integer `n`
and `a`, `b`, `c` in `k[t]`  with `a≠0`, return either
`ρ=0`, in which case the equation `a*D(q)+b*q=c` has no solution of degree at most `n` in `k[t]`,
or `ρ=1`, `B`, `C`, `α`, `β` in `k[t]` and an integer `m`, such that any solution `q` in `k[t]`
of `a*D(q)+b*q=c` must be of the form `q=α*h+β`, where `h` is in `k[t]`, `degree(h)≤m` and
`D(h)+B*h=C`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.4, p. 204.
"""
function SPDE(a::P, b::P, c::P, D::Derivation, n::Int) where P<:PolyElem
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

"""
    PolyRischDENoCancel1(b, c, D[, n=∞]) -> (q, ρ)

Polynomial Risch differential equation - no cancellation.

Given a field `k`, a derivation `D` on `k[t]`, an integer `n`
and `b`, `c` in `k[t]`  with `b≠0` and either `D=d/dt`or 
`degree(b)>max(0, degree(D(t))-1)`, return either
`ρ=0`, in which case the equation `D(q)+b*q=c` has no solution of degree at most `n` in `k[t]`,
or `ρ=1` and a solution `q` in `k[t]` of this equation with `degree(q)≤n`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.5, p. 208.
"""
function PolyRischDENoCancel1(b::P, c::P, D::Derivation, n::Int=typemax(Int)) where
    P<:PolyElem # here typemax(Int) represents +infinity
    iscompatible(b, D) && iscompatible(c, D) || 
        error("polynomials b and c must be in the domain of derivation D")
    !iszero(b) || error("polynomial b must be nonzero")
    isbasic(D) || degree(b)>max(0, degree(D)-1) || 
        error("either derivation D must be basic or degree(b)>max(0, degree(D)-1)")
    @info "PolyRischDENoCancel1(b,c,D,n)\nb=$b\nc=$c\nn=$n"
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

"""
    PolyRischDENoCancel2(b, c, D[, n=∞]) -> (q, B, C, ρ)

Polynomial Risch differential equation - no cancellation.

Given a field `k`, a derivation `D` on `k[t]`, an integer `n`
and `b`, `c` in `k[t]` with `degree(b)<degree(D(t))-1` and either
`D=d/dt` or `degree(D(t))≥2`, return either
`ρ=0`, in which case the equation `D(q)+b*q=c` has no solution of degree at most `n` in `k[t]`,
or `ρ=1` and a solution `q` in `k[t]` of this equation with `degree(q)≤n`, 
or `ρ=2` and `q`, `A`, `B` in `k[t]` such that for any solution `y` in `k[t]` 
of degree at most `n` of `D(y)+b*y=c`, `z=y-q` is a solution of `D(z)+B*z=C`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.5, p. 209.
"""
function PolyRischDENoCancel2(b::P, c::P, D::Derivation, n::Int=typemax(Int)) where
    P<:PolyElem # here typemax(Int) represents +infinity
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

"""
    PolyRischDENoCancel3(b, c, D[, n=∞]) -> (q, m, C, ρ)

Polynomial Risch differential equation - no cancellation.

Given a field `k`, a derivation `D` on `k[t]`, an integer `n`
and `b`, `c` in `k[t]` with `degree(D(t))≥2` and `degree(b)=degree(D(t))-1`, 
return either `ρ=0`, in which case the equation `D(q)+b*q=c` has no solution of degree at most `n` in `k[t]`,
or `ρ=1` and a solution `q` in `k[t]` of this equation with `degree(q)≤n`, 
or `ρ=2`, `q`, `C` in `k[t]` and an integer `m`such that for any solution `y` in `k[t]` 
of degree at most `n` of `D(y)+b*y=c`, `z=y-q` is a solution in `k[t]` 
of degree at most `m` of `D(z)+b*z=C`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.5, p. 210.
"""
function PolyRischDENoCancel3(b::P, c::P, D::Derivation, n::Int=typemax(Int)) where
    P<:PolyElem # here typemax(Int) represents +infinity    
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

"""
    PolyRischDECancelPrim(b, c, D[, n=∞]) -> (q, ρ)

Polynomial Risch differential equation, cancellation - primitive case.

Given a field `k`, a derivation `D` on `k[t]`, an integer `n`,
`b` in `k` and `c` in `k[t]`  with `D(t)` in `k` and `b≠0`, return either
`ρ=0`, in which case the equation `D(q)+b*q=c` has no solution of degree at most `n` in `k[t]`,
or `ρ=1` and a solution `q` in `k[t]` of this equation with `degree(q)≤n`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.6, p. 212.
"""
function PolyRischDECancelPrim(b::T, c::P, D::Derivation, n::Int=typemax(Int)) where
    {T<:RingElement, P<:PolyElem{T}} # here typemax(Int) represents +infinity
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

"""
    PolyRischDECancelExp(b, c, D[, n=∞]) -> (q, ρ)

Polynomial Risch differential equation, cancellation - hyperexponential case.

Given a field `k`, a derivation `D` on `k[t]`, an integer `n`,
`b` in `k` and `c` in `k[t]`  with `D(t)/t` in `k` and `b≠0`, return either
`ρ=0`, in which case the equation `D(q)+b*q=c` has no solution of degree at most `n` in `k[t]`,
or `ρ=1` and a solution `q` in `k[t]` of this equation with `degree(q)≤n`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.6, p. 213.
"""
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

"""
    PolyRischDE(b, c, D[, n=∞]) -> (q, ρ)

Polynomial Risch differential equation.

Given a field `k`, a derivation `D` on `k[t]`, an integer `n` and 
`b`, `c` in `k[t]`, return either
`ρ=0`, in which case the equation `D(q)+b*q=c` has no solution of degree at most `n` in `k[t]`,
or `ρ=1` and a solution `q` in `k[t]` of this equation with `degree(q)≤n`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Sections 6.6 and 6.7, p_power_N. 206-216.
"""
function PolyRischDE(b::P, c::P, D::Derivation, n::Int=typemax(Int)) where
    P<:PolyElem # here typemax(Int) represents +infinity
    iscompatible(b, D) && iscompatible(c, D) || 
        error("polynomials b and c must be in the domain of derivation D")
    δ = degree(D)
    Z = zero(parent(b))
    if !iszero(b) && isbasic(D) || degree(b)>max(0, δ-1)
        @info "case: NoCancel1"
        return PolyRischDENoCancel1(b, c, D, n)
    elseif (iszero(b) || degree(b)<δ-1) && (isbasic(D) || δ>=2)
        @info "case: NoCancel2"
        q, b, c, ρ = PolyRischDENoCancel2(b, c, D, n)
        if ρ==2
            q1, ρ = RischDE(b, c, BaseDerivation(D))
            ρ>=1 || return Z, ρ
            q = q1 - q
        end
        return q, 1
    elseif δ>=2 && degree(b)==δ-1
        @info "case: NoCancel3"
        q, m, c, ρ = PolyRischDENoCancel3(b, c, D, n) 
        if ρ<=0
            return Z, 0
        elseif ρ==1
            return q, 1
        elseif ρ==2
            if ishypertangent(D)
                @error "not implemented"
                throw(ErrorException)                        
                #  ... = PolyRischDECancelTan(...) TODO!
            else
                @error "not implemented"
                throw(ErrorException)
            end
        else
            @error "not implemented"
            throw(ErrorException)    
        end 
    # At this point only δ<=1, D!=d/dt is possible;
    # this is only compatible with primitive or"" hyperexponential.
    elseif isprimitive(D)
        @info "case: CancelPrim"
        return PolyRischDECancelPrim(constant_coefficient(b), c, D, n)
    elseif ishyperexponential(D)
        @info "case: CancelExp"
        return PolyRischDECancelExp(constant_coefficient(b), c, D, n) 
    else
        @error "not implemented"
        throw(ErrorException)
    end
end

"""
    RischDE(f, g, D) -> (y, ρ)

Risch differential equation.

Given a field `K`, a derivation `D` on `K` and  `f`, `g` in `K`, return
either `ρ=0`, in which case the equation `D(y)+f*q=g` has no solution in `K`,
or `ρ=1` and a solution `y` in `K` of this equation.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Chapter 6, p. 181.
"""
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
    Z = zero(f)

    h0 = WeakNormalizer(f, D)
    @info "weak normalizer h0=$h0"

    f = f - D(h0)//h0
    g = h0*g
    a, b, c, h1, ρ = RdeNormalDenominator(f, g, D)    
    ρ>=1 || return Z, ρ
    @info "normal denominator h1=$h1"

    a, b, c, h2 = RdeSpecialDenominator(a, b, c, D)
    @info "special denominator h2=$h2"

    n = RdeBoundDegree(a, b, c, D)
    @info "degree bound n=$n"

    b, c, n, α, β, ρ = SPDE(a, b, c, D, n)
    ρ>=1 || return Z, ρ

    z, ρ = PolyRischDE(b, c, D, n)
    ρ>=1 || return Z, ρ

    (α*z+β)//(h0*h1*h2), 1
end

