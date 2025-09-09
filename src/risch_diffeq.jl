# This file contains algorithms needed for the solution of 
# the Risch differential equation from chapter 6 of the book
#
#    Manuel Bronstein, Symbolic Integration I: Transcendental Functions,
#    2nd ed., Springer 2005. 
#


"""
    WeakNormalizer(f, D) -> q

Weak normalization.

Given a field `k`, a derivation `D` on `k[t]` and `f` in `k(t)`, return
`q` in `k[t]` such that `f-D(q)/q` is weakly normalized with respect to D.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.1, p. 183.
"""
function WeakNormalizer(f::F, D::Derivation) where 
    {T<:FieldElement, P<:PolyRingElem{T}, F<:FracElem{P}}
    iscompatible(f, D) || error("rational function f must be in the domain of derivation D")    
    dn, ds = SplitFactor(denominator(f), D)
    g = gcd(dn, derivative(dn))
    dstar = divexact(dn, g)
    d1 = divexact(dstar, gcd(dstar, g))
    a, b = gcdx(divexact(denominator(f), d1), d1, numerator(f))
    kz, z = polynomial_ring(base_ring(a), :ζ)    
    kzt, t = polynomial_ring(kz, var(parent(a)))
    dd1 = D(d1)
    r = resultant(d1(t), a(t)-z*dd1(t))
    if iszero(r)
        return one(parent(a))
    end
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
    {T<:FieldElement, P<:PolyRingElem{T}, F<:FracElem{P}}
    iscompatible(f, D) && iscompatible(g, D) || 
        error("rational functions f and g must be in the domain of derivation D")
    # Note: f must be weakly normalized which we do not check. It is recommended
    # to use this function only for rational functions f which were computed by WeakNormalizer. 
    (dn, ds) = SplitFactor(denominator(f), D)
    (en, es) = SplitFactor(denominator(g), D)
    p = gcd(dn, en)
    h = divexact(gcd(en, derivative(en)), gcd(p, derivative(p)))
    if !iszero(rem(dn*h^2, en))
        return zero(h), zero(f), zero(f), zero(h), 0 # no solution
    end
    dn*h, dn*h*f-dn*D(h), dn*h^2*g, h, 1
end

function one_times_n_solve(A::Vector{T}, B::Vector{T}) where T<:FieldElement
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
is a hyperexponential monomial over `k(t)`, return either `ρ=0`, in which case 
`n*f=D(v)/v+m*D(θ)/θ` has no solution `v≠0` in `k(t)` and 
integers `n≠0` and `m`, or `ρ=1` and a solution `n`, `m`, `v` of that equation.

This function may throw exception `AlgorithmFailedError`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 7.3, p. 253.
"""
function ParametricLogarithmicDerivative(f::F, w::F, D::Derivation) where F<:FieldElement
    # base case f,w \in constant field, D must be the null derivation
    iszero(D) || error("base case only for null derivations")
    v = one(parent(f))
    q = f//w
    if !isrational(q) # could be complex for example
        return 0, 0, zero(parent(f)), 0
    end
    q = rationalize_over_Int(f//w)
    m = numerator(q)
    n = denominator(q)
    n, m, v, 1
end

function ParametricLogarithmicDerivative(f::F, w::F, D::Derivation) where 
    {T<:FieldElement, P<:PolyRingElem{T}, F<:FracElem{P}}
    # See Bronstein's book, Section 7.3, p. 253
    Z = zero(f)
    no_solution = (0, 0, Z, 0)
    if degree(numerator(f))<=0 && degree(denominator(f))<=0 &&
        degree(numerator(w))<=0 && degree(denominator(w))<=0 
        #f, w \in k(t) are actually in k, so search solution not in k(t) but in k
        n, m, v, ρ = ParametricLogarithmicDerivative(
            constant_coefficient(numerator(f)),
            constant_coefficient(numerator(w)),
            BaseDerivation(D))
        return n, m, v + Z, ρ # make v \in k an element of k(t)
    end
    d = denominator(f)
    e = denominator(w)
    p, a = divrem(numerator(f), d)
    q, b = divrem(numerator(w), e)
    t = gen(parent(d))
    B = max(0, degree(D(t))-1)
    C = max(degree(q), degree(p))
    if degree(q)>B
        ss = one_times_n_solve([coeff(p, i) for i=B+1:C], [coeff(q, i) for i=B+1:C])
        if isempty(ss) 
            return no_solution
        end
        if !isrational(ss[1])
            return no_solution
        end
        s = rationalize_over_Int(ss[1])
        M = numerator(s)  # In Bronstein's book, M and N are switched, this is the first and so far only bug I found there
        N = denominator(s)
        Q, v, ρ = InFieldLogarithmicDerivativeOfRadical(N*f - M*w, D)
        if ρ>=1 && !iszero(Q) && !iszero(v) 
            return Q*N, Q*M, v, 1
        else
            return no_solution
        end
    end
    if degree(p)>B
        return no_solution 
    end
    l = lcm(d, e)
    ln, ls = SplitFactor(l, D)
    z = ls*gcd(ln, derivative(ln))
    if degree(z)<=0 # z \in k
        throw(AlgorithmFailedError("ParametricLogarithmicDerivative\n@ $(@__FILE__):$(@__LINE__)"))  
    end
    u1, r1 = divrem(numerator(l*f), z)
    u2, r2 = divrem(numerator(l*w), z)
    ss = one_times_n_solve([coeff(r1, i) for i=0:(degree(z)-1)], [coeff(r2, i) for i=0:(degree(z)-1)])
    if isempty(ss) 
        return no_solution 
    end
    if !isrational(ss[1])
        return no_solution
    end
    s = rationalize_over_Int(ss[1])
    M = numerator(s)
    N = denominator(s)
    Q, v, ρ = InFieldLogarithmicDerivativeOfRadical(N*f - M*w, D)
    if ρ>=1 && !iszero(Q) && !iszero(v) 
        return Q*N, Q*M, v, 1
    else
        return no_solution
    end
end

"""
    RdeSpecialDenomExp(a, b, c, D) -> (A, B, C, h)

Special part of the denominator - hyperexponential case.

Given a field `k`, a derivation `D` on `k[t]` with `D(t)/t` in `k`, 
`a≠0` in `k[t]` with `gcd(a,t)=1`, and `b`, `c` in `k⟨t⟩`
return  `A`, `B`, `C`, `h` in `k[t]` such that
for any solution `q` in `k⟨t⟩` of `a*D(q)+b*q=c`, `r=q*h` in `k[t]` satisfies `A*D(r)+B*r=C`.     

(Here, `k⟨t⟩` denotes the elements of `k(t)` which are reduced w.r.t. `D`.)

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.2, p. 190.
"""
function RdeSpecialDenomExp(a::P, b::F, c::F, D::Derivation) where
    {T<:FieldElement, P<:PolyRingElem{T}, F<:FracElem{P}}    
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
    nb = iszero(b) ? typemax(Int) : valuation(b, p)
    nc = iszero(c) ? typemax(Int) : valuation(c, p)
    n = min(0, nc - min(0, nb))
    if nb==0 
        α = constant_coefficient(Remainder(-b//a, p))
        w = coeff(MonomialDerivative(D), 1)
        n0, m, z, ρ = ParametricLogarithmicDerivative(α, w, BaseDerivation(D))
        if  ρ>0 && n0==1 && !iszero(z)
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
    RdeSpecialDenomTan(a, b, c, D) -> (A, B, C, h)

Special part of the denominator - hypertangent case.

Given a field `k` not containing `√-1`, a derivation `D` on `k[t]` with `D(t)/(t^2+1)` in `k`, 
`a≠0` in `k[t]` with `gcd(a,t^2+1)=1`, and `b`, `c` in `k⟨t⟩`,
return  `A`, `B`, `C`, `h` in `k[t]` such that
for any solution `q` in `k⟨t⟩` of `a*D(q)+b*q=c`, `r=q*h` in `k[t]` satisfies `A*D(r)+B*r=C`.     

(Here, `k⟨t⟩` denotes the elements of `k(t)` which are reduced w.r.t. `D`.)

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.2, p. 192.
"""
function RdeSpecialDenomTan(a::P, b::F, c::F, D::Derivation) where
    {T<:FieldElement, P<:PolyRingElem{T}, F<:FracElem{P}}    
    !iszero(a) || error("a must be != 0")
    ishypertangent(D) ||
        error("monomial of derivation D must be hypertangent")
    iscompatible(a, D) && iscompatible(b, D) && iscompatible(c, D) || 
        error("polynomial a and rational functions b and c must be in the domain of derivation D")
    isreduced(b, D) && isreduced(c, D) || 
        error("rational functions b and c must be reduced with respect to derivation D")
    t = gen(parent(a))
    p = t^2+1
    degree(gcd(a, p))==0 || error("gcd(a, t^2+1) must be == 1")
    nb = iszero(b) ? typemax(Int) : valuation(b, p)
    nc = iszero(c) ? typemax(Int) : valuation(c, p)
    n = min(0, nc - min(0, nb))
    if nb==0         
        αI_plus_β = Remainder(-b//a, p)
        α = coeff(αI_plus_β, 1)
        β = coeff(αI_plus_β, 0)
        η = constant_coefficient(divexact(MonomialDerivative(D), p))
        D0 = BaseDerivation(D)
        v, ρ = InFieldDerivative(2*β, D0)
        if ρ>0 && !iszero(v)
            _, I, D0I = Complexify(parent(η), D0)
            n0, m, v, ρ = ParametricLogarithmicDerivative(α*I+β, 2*η*I, D0I)
            if  ρ>0 && n0==1 && !iszero(v)
                n = min(n, m)
            end
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
    RdeSpecialDenomTanI(a, b, c, D) -> (A, B, C, h)

Special part of the denominator - hypertangent case, field contains I=√-1.

Given a field `k` containing `√-1`, a derivation `D` on `k[t]` with `D(t)/(t^2+1)` in `k`, 
`a≠0` in `k[t]` with `gcd(a,t^2+1)=1`, and `b`, `c` in `k⟨t⟩`,
return  `A`, `B`, `C`, `h` in `k[t]` such that
for any solution `q` in `k⟨t⟩` of `a*D(q)+b*q=c`, `r=q*h` in `k[t]` satisfies `A*D(r)+B*r=C`.     

(Here, `k⟨t⟩` denotes the elements of `k(t)` which are reduced w.r.t. `D`.)

The implementation is  analogous to `RdeSpecialDenomPrim` and `RdeSpecialDenomTan`, 
but now with `p=t-√-1` instead of `p=t` resp. `p=t^2+1`, 
see [Bronstein's book](https://link.springer.com/book/10.1007/b138171), last sentence
before algorithm `RdeSpecialDenomTan` in Section 6.2, p. 192 and Exercise 6.1, p. 216.
"""
function RdeSpecialDenomTanI(a::P, b::F, c::F, D::Derivation) where
    {T<:FieldElement, P<:PolyRingElem{T}, F<:FracElem{P}}    
    !iszero(a) || error("a must be != 0")
    ishypertangent(D) ||
        error("monomial of derivation D must be hypertangent")
    iscompatible(a, D) && iscompatible(b, D) && iscompatible(c, D) || 
        error("polynomial a and rational functions b and c must be in the domain of derivation D")
    isreduced(b, D) && isreduced(c, D) || 
        error("rational functions b and c must be reduced with respect to derivation D")
    t = gen(parent(a))    
    degree(gcd(a, t^2 + 1))==0 || error("gcd(a, t^2+1) must be == 1")
    contains_I(parent(a)) || error("field k must contain I=sqrt(-1)")
    I = get_I(base_ring(parent(a)))
    p = t-I
    nb = iszero(b) ? typemax(Int) : valuation(b, p) 
    nc = iszero(c) ? typemax(Int) : valuation(c, p)
    n = min(0, nc - min(0, nb))
    if nb==0         
        α = constant_coefficient(Remainder(-b//a, p))
        η = constant_coefficient(divexact(MonomialDerivative(D), t^2 + 1))
        n0, m, v, ρ = ParametricLogarithmicDerivative(α, 2*η*I, BaseDerivation(D))
        if  ρ>0 && n0==1 && !iszero(v)
            n = min(n, m)
        end
    end
    N = max(0, -nb, n-nc)
    pp = t^2 + 1
    pp_power_N = pp^N
    b1 = (b+n*a*divexact(D(pp), pp))*pp_power_N
    @assert isone(denominator(b1))
    c1 = c*pp^(N-n)
    @assert isone(denominator(c1))
    a*pp_power_N, numerator(b1), numerator(c1), pp^(-n)   
end

"""
    RdeSpecialDenominator(a, b, c, D) -> (A, B, C, h)

Special part of the denominator.

Given a field `k`, a derivation `D` on `k[t]`, `a≠0` in `k[t]`, and `b`, `c` in `k⟨t⟩`,
return  `A`, `B`, `C`, `h` in `k[t]` such that
for any solution `q` in `k⟨t⟩` of `a*D(q)+b*q=c`, `r=q*h` in `k[t]` satisfies `A*D(r)+B*r=C`.     

(Here, `k⟨t⟩` denotes the elements of `k(t)` which are reduced w.r.t. `D`.)

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.2, p. 186.
"""
function RdeSpecialDenominator(a::P, b::F, c::F, D::Derivation) where
    {T<:FieldElement, P<:PolyRingElem{T}, F<:FracElem{P}}
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
        a = divexact(a, d)
        b = b//d
        c = c//d
        return  RdeSpecialDenomExp(a, b, c, D)
    elseif ishypertangent(D)        
        t = gen(parent(a))
        p = t^2 + 1
        d = gcd(a, p)
        a = divexact(a, d)
        b = b//d
        c = c//d
        if contains_I(parent(a))
            return RdeSpecialDenomTanI(a, b, c, D) #case √-1 in k
        else
            return RdeSpecialDenomTan(a, b, c, D) 
        end
    else
        H = MonomialDerivative(D)
        throw(NotImplementedError("RdeSpecialDenominator: monomial derivative $H\n@ $(@__FILE__):$(@__LINE__)"))
    end    
end

"""
    RdeBoundDegreePrim(a, b, c, D) -> n

Bound on polynomial solutions - primitive case.

Given a field `k`, a derivation `D` on `k[t]` with `D(t)` in `k`, and `a`, `b`, `c` in `k[t]`  
with `a≠0`, return integer `n` such that `degree(q)≤n` for any solution `q` in `k[t]` of `a*D(q)+b*q=c`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.3, p. 198.
"""
function RdeBoundDegreePrim(a::P, b::P, c::P, D::Derivation) where 
    {T<:FieldElement, P<:PolyRingElem{T}}
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
        z, m0, ρ = LimitedIntegrate(α, leading_coefficient(D), BaseDerivative(D))
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
            w, m0, ρ = LimitedIntegrate(β, leading_coefficient(D), D0)
            if ρ>0 && isrational(m0)
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

Given a field `k` and  `a`, `b`, `c` in `k[t]` with `a≠0`, return integer `n`
such that `degree(q)≤n` for any solution `q` in `k[t]` of `a*(d/dt)(q)+b*q=c`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.3, p. 199.
"""
function RdeBoundDegreeBase(a::P, b::P, c::P) where 
    {T<:FieldElement, P<:PolyRingElem{T}}
    !iszero(a) || error("polynomial a must be nonzero")
    da = degree(a)
    db = degree(b)
    dc = degree(c)
    n = max(0, dc - max(db, da - 1))
    if db==da-1
        m0 = -leading_coefficient(b)//leading_coefficient(a)
        if isrational(m0)
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

Given a field `k`, a derivation `D` on `k[t]` with `D(t)/t` in `k`, and `a`, `b`, `c` in `k[t]`  
with`a≠0`, return integer `n` such that `degree(q)≤n` for any solution `q` in `k[t]` of `a*D(q)+b*q=c`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.3, p. 200.
"""
function RdeBoundDegreeExp(a::P, b::P, c::P, D::Derivation) where 
    {T<:FieldElement, P<:PolyRingElem{T}}
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
        if  ρ>0 && n0==1 && !iszero(z)
            n = max(n, m)
        end
    end
    n
end

"""
    RdeBoundDegreeNonLinear(a, b, c, D) -> n

Bound on polynomial solutions - nonlinear case.

Given a field `k`, a derivation `D` on `k[t]` with `degree(D(t))≥2`, and `a`, `b`, `c` in `k[t]`  
with `a≠0`, return integer `n` such that `degree(q)≤n` for any solution `q` in `k[t]` of `a*D(q)+b*q=c`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.3, p. 201.
"""
function RdeBoundDegreeNonLinear(a::P, b::P, c::P, D::Derivation) where 
    {T<:FieldElement, P<:PolyRingElem{T}}
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
        m0 = -leading_coefficient(b)//(λ*leading_coefficient(a))
        if isrational(m0)
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
function RdeBoundDegree(a::P, b::P, c::P, D::Derivation) where 
    {T<:FieldElement, P<:PolyRingElem{T}}
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
        H = MonomialDerivative(D)
        throw(NotImplementedError("RdeBoundDegree: monomial derivative $H\n@ $(@__FILE__):$(@__LINE__)"))                        
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
function SPDE(a::P, b::P, c::P, D::Derivation, n::Int) where 
    {T<:FieldElement, P<:PolyRingElem{T}}
    iscompatible(a, D) && iscompatible(b, D) && iscompatible(c, D) || 
        error("polynomials a, b, and c must be in the domain of derivation D")
    !iszero(a) || error("polynomial a must be nonzero")
    Z = zero(a)
    no_solution = (Z, Z, 0, Z, Z, 0)
    if n<0
        if iszero(c)
            return Z, Z, 0, Z, Z, 1 
        else
            return no_solution 
        end
    end
    g = gcd(a, b)
    if !iszero(rem(c, g))
        return no_solution
    end
    a = divexact(a, g)
    b = divexact(b, g)
    c = divexact(c, g)
    if degree(a)==0
        return divexact(b, a), divexact(c, a), n, one(a), Z, 1
    end
    r, z = gcdx(b, a, c)
    u = SPDE(a, b + D(a), z - D(r), D, n - degree(a))
    if u[6]==0 # no solution of recursive call of SPDE
        return no_solution
    end
    b1, c1, m, α, β, _ = u
    b1, c1, m, a*α, a*β+r, 1
end

"""
    PolyRischDENoCancel1(b, c, D[, n=∞]) -> (q, ρ)

Polynomial Risch differential equation - no cancellation.

Given a field `k`, a derivation `D` on `k[t]`, an integer `n`
and `b`, `c` in `k[t]`  with `b≠0` such that either `D=d/dt`or 
`degree(b)>max(0, degree(D(t))-1)`, return either
`ρ=0`, in which case the equation `D(q)+b*q=c` has no solution of degree at most `n` in `k[t]`,
or `ρ=1` and a solution `q` in `k[t]` of this equation with `degree(q)≤n`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.5, p. 208.
"""
function PolyRischDENoCancel1(b::P, c::P, D::Derivation, n::Int=typemax(Int)) where
    {T<:FieldElement, P<:PolyRingElem{T}}      # here typemax(Int) represents +infinity
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
and `b`, `c` in `k[t]` such that `degree(b)<degree(D(t))-1` and either
`D=d/dt` or `degree(D(t))≥2`, return either
`ρ=0`, in which case the equation `D(q)+b*q=c` has no solution of degree at most `n` in `k[t]`,
or `ρ=1` and a solution `q` in `k[t]` of this equation with `degree(q)≤n`, 
or `ρ=2` and `q`, `A`, `B` in `k[t]` such that for any solution `y` in `k[t]` 
of degree at most `n` of `D(y)+b*y=c`, `z=y-q` is a solution of `D(z)+B*z=C`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.5, p. 209.
"""
function PolyRischDENoCancel2(b::P, c::P, D::Derivation, n::Int=typemax(Int)) where
    {T<:FieldElement, P<:PolyRingElem{T}}      # here typemax(Int) represents +infinity
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
    no_solution = (Z, Z0, Z0, 0)
    q = Z
    while !iszero(c)
        if n==0
            m=0
        else
            m = degree(c) - δ + 1
        end
        if n<0 || m<0 || m>n 
            return no_solution
        end
        if m>0
            p = (leading_coefficient(c)//(m*λ))*t^m
        else
            if degree(b)!=degree(c)
                return no_solution 
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
and `b`, `c` in `k[t]` such that `degree(D(t))≥2` and `degree(b)=degree(D(t))-1`, 
return either `ρ=0`, in which case the equation `D(q)+b*q=c` has no solution of degree at most `n` in `k[t]`,
or `ρ=1` and a solution `q` in `k[t]` of this equation with `degree(q)≤n`, 
or `ρ=2`, `q`, `C` in `k[t]` and an integer `m`such that for any solution `y` in `k[t]` 
of degree at most `n` of `D(y)+b*y=c`, `z=y-q` is a solution in `k[t]` 
of degree at most `m` of `D(z)+b*z=C`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.5, p. 210.
"""
function PolyRischDENoCancel3(b::P, c::P, D::Derivation, n::Int=typemax(Int)) where
    {T<:FieldElement, P<:PolyRingElem{T}}      # here typemax(Int) represents +infinity    
    iscompatible(b, D) && iscompatible(c, D) || 
        error("polynomials b and c must be in the domain of derivation D")
    δ = degree(D)
    δ>=2 || error("degree(D) must be >= 2")
    degree(b)==δ-1 || error("degree(b)==degree(D)-1 must hold")
    Z = zero(b)
    no_solution = (Z, 0, Z, 0)
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
            return no_solution
        end
        u = m*λ + leading_coefficient(b)
        if iszero(u)
            return q, m, c, 2
        end
        if m>0
            p = (leading_coefficient(c)//u)*t^m
        else
            if degree(c)!=δ-1
                return no_solution
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

Given a field `k`, a derivation `D` on `k[t]` with `D(t)` in `k`, an integer `n`,
`b≠0` in `k` and `c` in `k[t]`, return either
`ρ=0`, in which case the equation `D(q)+b*q=c` has no solution of degree at most `n` in `k[t]`,
or `ρ=1` and a solution `q` in `k[t]` of this equation with `degree(q)≤n`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.6, p. 212.
"""
function PolyRischDECancelPrim(b::T, c::P, D::Derivation, n::Int=typemax(Int)) where
    {T<:FieldElement, P<:PolyRingElem{T}}       # here typemax(Int) represents +infinity
    isprimitive(D) ||
        error("monomial of derivation D must be primitive")
    D0 = BaseDerivation(D)
    iscompatible(b, D0) || 
        error("coefficient b must be in the domain of the base derivation of D")
    iscompatible(c, D) || 
        error("polynomial c must be in the domain of derivation D")
    Z = zero(c)
    no_solution = (Z, 0)
    if b==0  #Note: case b==0 allowed, TODO: test this and update docstring
        q0, ρ = InFieldDerivative(c//1, D) # make poly c a rational function
        q = numerator(q0)
        if ρ<=0 || !isone(denominator(q0)) || degree(q)>n
            return no_solution 
        end
        return q, 1
    end
    t = gen(parent(c))
    z, ρ = InFieldLogarithmicDerivative(b, D0) 
    if ρ>0
        p0, ρ = InFieldDerivative(z*c, D)
        p = numerator(p0)
        if ρ<=0 || !isone(denominator(p0)) || degree(p)>n
            return no_solution 
        end
        return p//z, 1
    end
    if iszero(c)
        return Z, 1 # zero is solution
    end
    if n<degree(c)
        return no_solution
    end
    q = Z
    while !iszero(c)
        m = degree(c)
        if n<m
            return no_solution
        end
        s, ρ = RischDE(b, leading_coefficient(c), D0)
        if ρ<=0
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

Given a field `k`, a derivation `D` on `k[t]` with `D(t)/t` in `k`, an integer `n`,
`b≠0` in `k` and `c` in `k[t]`, return either
`ρ=0`, in which case the equation `D(q)+b*q=c` has no solution of degree at most `n` in `k[t]`,
or `ρ=1` and a solution `q` in `k[t]` of this equation with `degree(q)≤n`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.6, p. 213.
"""
function PolyRischDECancelExp(b::T, c::P, D::Derivation, n::Int=typemax(Int)) where
    {T<:FieldElement, P<:PolyRingElem{T}}      # here typemax(Int) represents +infinity
    ishyperexponential(D) ||
        error("monomial of derivation D must be hyperexponential")
    D0 = BaseDerivation(D)
    iscompatible(b, D0) || 
        error("coefficient b must be in the domain of the base derivation of D")
    iscompatible(c, D) || 
        error("polynomial c must be in the domain of derivation D")
    Z = zero(c)
    no_solution = (Z, 0)
    if b==0
        q0, ρ = InFieldDerivative(c//1, D) # make poly c a rational function
        q = numerator(q0)
        if ρ<=0 || !isone(denominator(q0)) || degree(q)>n
            return no_solution 
        end
        return q, 1
    end
    t = gen(parent(c))
    H = MonomialDerivative(D)
    w = coeff(H,1) # = Dt/t for hyperexponentialm case
    n1, m, z, ρ = ParametricLogarithmicDerivative(b, w, D0)
    if  ρ>0 && n1==1
        p, ρ = InFieldDerivative(c*z*(t//1)^m, D) # t//1 in k(t) 
        if ρ<=0 || !isreduced(p, D)
            return no_solution             
        end
        q0 = p//(z*(t//1)^m) # t((1 in k(t)))
        q = numerator(q0)
        if isone(denominator(q0)) && degree(q)<=n
            return q, 1
        else
            return no_solution             
        end
    end
    if iszero(c)
        return Z, 1 # zero is solution
    end
    if n<degree(c)
        return no_solution         
    end
    q = Z
    while !iszero(c)
        m = degree(c)
        if n<m
            return no_solution             
        end
        s, ρ = RischDE(b+m*w, leading_coefficient(c), D0)
        if ρ<=0
            return no_solution             
        end
        q += s*t^m
        n = m - 1
        c -= b*s*t^m + D(s*t^m)
    end
    q, 1
end

"""
    PolyRischDECancelTan(b₀, c, D[, n=∞]) -> (q, ρ)

Polynomial Risch differential equation, cancellation - hypertangent case.

Given a field `k` not containing `√-1`, a derivation `D` on `k[t]` with `D(t)/(t^2+1)` in `k`, an integer `n`,
`b₀` in `k` and `c` in `k[t]`, return either
`ρ=0`, in which case the equation `D(q)+(b₀-n*t*D(t)/(t^2+1))*q=c` has no solution of degree at most `n` in `k[t]`,
or `ρ=1` and a solution `q` in `k[t]` of this equation with `degree(q)≤n`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 6.6, p. 215.
"""
function PolyRischDECancelTan(b0::T, c::P, D::Derivation, n::Int=typemax(Int)) where
    {T<:FieldElement, P<:PolyRingElem{T}}      # here typemax(Int) represents +infinity
    ishypertangent(D) ||
        error("monomial of derivation D must be hypertangent")
    D0 = BaseDerivation(D)
    iscompatible(b0, D0) || 
        error("coefficient b0 must be in the domain of the base derivation of D")
    iscompatible(c, D) || 
        error("polynomial c must be in the domain of derivation D")
    Z = zero(c)
    no_solution = (Z, 0)
    if n==0
        if degree(c)<=0
            if !iszero(b0)
                q, ρ = RischDE(b0, constant_coefficient(c), BaseDerivation(D))
                if ρ<=0
                    return no_solution
                else
                    return q + Z, 1
                end
            end
            q, ρ = InFieldDerivative(constant_coefficient(c), BaseDerivation(D))
            if ρ<=0 
                return no_solution
            else
                return q + Z, 1
            end
        end
    end
    t = gen(parent(c))
    p = t^2 + 1
    η = constant_coefficient(divexact(MonomialDerivative(D), p))
    r = rem(c, p)
    c0 = coeff(r, 0)
    c1 = coeff(r, 1)
    u, v, ρ   = CoupledDESystem(b0, -n*η, c0, c1, BaseDerivation(D))
    if ρ<=0
        return no_solution
    end
    r = u + v*t
    if n==1
        return r, 1
    end
    c = divexact(c - D(r) - (b0 - n*η*t)*r, p)
    h, ρ = PolyRischDECancelTan(b0, c, D, n-2)
    if ρ<=0
        return no_solution
    end
    p*h + r, 1
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
    {T<:FieldElement, P<:PolyRingElem{T}} # here typemax(Int) represents +infinity
    iscompatible(b, D) && iscompatible(c, D) || 
        error("polynomials b and c must be in the domain of derivation D")
    δ = degree(D)
    Z = zero(parent(b))
    if !iszero(b) && isbasic(D) || degree(b)>max(0, δ-1)
        return PolyRischDENoCancel1(b, c, D, n)
    elseif (iszero(b) || degree(b)<δ-1) && (isbasic(D) || δ>=2)
        q, b, c, ρ = PolyRischDENoCancel2(b, c, D, n)
        if ρ==2
            q1, ρ = RischDE(b, c, BaseDerivation(D))
            ρ>=1 || return Z, ρ
            q = q1 - q
        end
        return q, 1
    elseif δ>=2 && degree(b)==δ-1
        q, m, c, ρ = PolyRischDENoCancel3(b, c, D, n) 
        if ρ<=0
            return Z, 0
        elseif ρ==1
            return q, 1
        elseif ρ==2
            if ishypertangent(D)       
                if contains_I(parent(b))  
                    # Seems that PolyRischDE was called by CoupledDESystem,
                    # this case should be handled by CoupledDESystem.
                    return c, 101 + max(-1, m) # return new c, m
                else
                    t = gen(parent(b))
                    η = divexact(MonomialDerivative(D), t^2+1)
                    b0 = b + n*t*η
                    @assert degree(b0)<=0
                    return PolyRischDECancelTan(constant_coefficient(b0), c, D, n)
                end                
            else
                H = MonomialDerivative(D)
                throw(NotImplementedError("PolyRischDE: no cancellation, degree(b)==δ-1, monomial derivative $H\n@ $(@__FILE__):$(@__LINE__)"))                        
            end
        else
            @assert false # never reach this point
        end 
    # At this point only the cancellation case δ<=1, D!=d/dt is possible;
    # this is only compatible with primitive or hyperexponential.
    elseif contains_I(parent(b))
        # Seems that PolyRischDE was called by CoupledDESystem,
        # this case should be handled by CoupledDESystem.
        return c, 101 + max(-1, n) # return original c, n
    elseif isprimitive(D)
        return PolyRischDECancelPrim(constant_coefficient(b), c, D, n)
    elseif ishyperexponential(D)
        return PolyRischDECancelExp(constant_coefficient(b), c, D, n) 
    else
        H = MonomialDerivative(D)
        throw(NotImplementedError("PolyRischDE: cancellation case, monomial derivative $H\n@ $(@__FILE__):$(@__LINE__)"))  
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
function RischDE(f::F, g::F, D::Derivation) where F<:FieldElement
    iszero(D) || error("base case only for null derivations")
    #base case => pure algebra problem ...
    iscompatible(f, D) && iscompatible(g,D) || 
        error("coefficients f and g must be in the domain of the base derivation of D") 
    if iszero(f)
        if iszero(g)
            return zero(parent(f)), 1
        else
            return zero(parent(f)), 0 # no solution
        end
    else
        return g//f, 1
    end
 end

function RischDE(f::F, g::F, D::Derivation) where 
    {T<:FieldElement, P<:PolyRingElem{T}, F<:FracElem{P}}
    iscompatible(f, D) && iscompatible(g, D) || 
        error("rational functions f and g must be in the domain of derivation D")
    if iszero(f)
        return InFieldDerivative(g::F, D::Derivation)
    end
    
    Z = zero(f)
    h0 = WeakNormalizer(f, D)

    f = f - D(h0)//h0
    g = h0*g
    a, b, c, h1, ρ = RdeNormalDenominator(f, g, D)    
    ρ>=1 || return Z, ρ

    a, b, c, h2 = RdeSpecialDenominator(a, b, c, D)

    n = RdeBoundDegree(a, b, c, D)

    b, c, n, α, β, ρ = SPDE(a, b, c, D, n)
    ρ>=1 || return Z, ρ

    z, ρ = PolyRischDE(b, c, D, n)
    ρ>=1 || return Z, ρ

    (α*z+β)//(h0*h1*h2), 1
end

