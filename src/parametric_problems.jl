# This file contains algorithms needed for the solution of 
# the parametric Risch differential equation from chapter 7 of the book
#
#    Manuel Bronstein, Symbolic Integration I: Transcendental Functions,
#    2nd ed., Springer 2005. 
#


using Logging


function Base.lcm(as::Vector{T}) where T<:RingElement
    m = length(as)
    if m==0
        error("array as must not be empty")
    elseif m==1
        return as[1]
    else
        y = as[1]
        for i=2:m
            y = lcm(y, as[i])
        end
        return y
    end
end

"""
    ParamRdeNormalDenominator(f, gs, D) -> (a, b, Gs, h)

Normal part of the denominator.

Given a field `k`, a derivation `D` on `k[t]`, `f` in `k(t)`, `gs=[g₁,...,gₘ]`, `g₁`,...,`gₘ` in `k(t)`
with `f` weakly normalized with respect to `t`, return `a`, `b`, `Gs=[G₁,...,Gₘ]`, `h` 
such that `a`, `h` in `k[t]`, `b` in `k⟨t⟩`, `G₁`,...,`Gₘ` in `k(t)`, 
and for any solution `c₁`,...,`cₘ` in `Const(k)` and `y` in `k(t)`
of `D(y)+f*y=∑ᵢcᵢ*gᵢ`, `q=y*h` in `k⟨t⟩` satisfies `a*D(q)+b*q=∑ᵢcᵢ*Gᵢ`.     

(Here, `k⟨t⟩` denotes the elements of `k(t)` which are reduced w.r.t. `D`.)

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 7.1, p. 219.
"""
function ParamRdeNormalDenominator(f::F, gs::Vector{F}, D::Derivation) where 
    {P<:PolyElem, F<:FracElem{P}}
    iscompatible(f, D) && all(iscompatible(g, D) for g in gs) || 
        error("rational functions f and g_i must be in the domain of derivation D")
    # Note: f must be weakly normalized which we do not check. It is recommended
    # to use this function only for rational functions f which were computed by WeakNormalizer. 
    (dn, ds) = SplitFactor(denominator(f), D)
    (en, es) = SplitFactor(lcm([denominator(g) for g in gs]), D)
    p = gcd(dn, en)
    h = divexact(gcd(en, derivative(en)), gcd(p, derivative(p)))
    dnh2 = dn*h^2
    dn*h, dn*h*f-dn*D(h), [dnh2*g for g in gs], h
end

"""
    ParamRdeSpecialDenomExp(a, b, gs, D) -> (A, B, Gs, h)

Special part of the denominator - hyperexponential case.

Given a field `k`, a derivation `D` on `k[t]`, `a` in `k[t]`, `b` in `k⟨t⟩`, `gs=[g₁,...,gₘ]`,
`g₁`,...,`gₘ` in `k(t)` with `D(t)/t` in `k`, `a≠0` and `gcd(a,t)=1`, return  
`A`, `B`, `Gs=[G₁,...,Gₘ]`, `h` such that `A`, `B`, `h` in `k[t]`,
`G₁`,...,`Gₘ` in `k(t)`, and for any solution `c₁`,...,`cₘ` in `Const(k)` and `q` in `k⟨t⟩`
of `a*D(q)+b*q=∑ᵢcᵢ*gᵢ`, `r=q*h` in `k[t]` satisfies `A*D(r)+B*r=∑ᵢcᵢ*Gᵢ`.     

(Here, `k⟨t⟩` denotes the elements of `k(t)` which are reduced w.r.t. `D`.)

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 7.1, p. 221.
"""
function ParamRdeSpecialDenomExp(a::P, b::F, gs::Vector{F}, D::Derivation) where
    {P<:PolyElem, F<:FracElem{P}}
    ishyperexponential(D) ||
        error("monomial of derivation D must be hyperexponential")
    iscompatible(a, D) && iscompatible(b, D) && all([iscompatible(g, D) for g in gs]) || 
        error("polynomial a and rational functions b and g_i must be in the domain of derivation D")
    !iszero(a) || error("a must be != 0")
    isreduced(b, D) || 
        error("rational function b must be reduced with respect to derivation D")
    t = gen(parent(a))
    degree(gcd(t, a))==0 || error("gcd(a, t) must be == 1")
    p = t
    nb = valuation(b, p)
    nc = minimum([valuation(g, p) for g in gs])
    n = min(0, nc - min(0, nb))
    if nb==0 
        α = constant_coefficient(Remainder(-b//a, p))
        w = coeff(MonomialDerivative(D), 1)
        n0, s, z, ρ = ParametricLogarithmicDerivative(α, w, BaseDerivation(D))
        if ρ<0
            error("ParametricLogarithmicDerivative failed")
        end
        if  ρ>0 && n0==1 && !iszero(z)
            n = min(n, s)
        end
    end
    N = max(0, -nb)
    p_power_N = p^N
    p_power_N_minus_n = p^(N-n)
    b1 = (b+n*a*divexact(D(p), p))*p_power_N
    @assert isone(denominator(b1))
    a*p_power_N, numerator(b1), [g*p_power_N_minus_n for g in gs], p^(-n) 
end

"""
    ParamRdeSpecialDenominator(a, b, gs, D) -> (A, B, Gs, h)

Special part of the denominator.

Given a field `k`, a derivation `D` on `k[t]`, `a` in `k[t]`, `b` in `k⟨t⟩`, `gs=[g₁,...,gₘ]`,
`g₁`,...,`gₘ` in `k(t)` with `a≠0`, return  
`A`, `B`, `Gs=[G₁,...,Gₘ]`, `h` such that `A`, `B`, `h` in `k[t]`,
`G₁`,...,`Gₘ` in `k(t)`, and for any solution `c₁`,...,`cₘ` in `Const(k)` and `q` in `k⟨t⟩`
of `a*D(q)+b*q=∑ᵢcᵢ*gᵢ`, `r=q*h` in `k[t]` satisfies `A*D(r)+B*r=∑ᵢcᵢ*Gᵢ`.     

(Here, `k⟨t⟩` denotes the elements of `k(t)` which are reduced w.r.t. `D`.)

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 7.1, p. 221.
"""
function ParamRdeSpecialDenominator(a::P, b::F, gs::Vector{F}, D::Derivation) where
    {P<:PolyElem, F<:FracElem{P}}
    iscompatible(a, D) && iscompatible(b, D) && all([iscompatible(g, D) for g in gs]) || 
        error("polynomial a and rational functions b and g_i must be in the domain of derivation D")
    !iszero(a) || error("a must be != 0")
    isreduced(b, D) || 
        error("rational function b must be reduced with respect to derivation D")
    if isprimitive(D)
        @assert isone(denominator(b))
        return a, numerator(b), gs, one(b)
    elseif ishyperexponential(D)
        t = gen(parent(a))
        d = gcd(a, t)
        a = divexact(a, d)
        b = b//d
        gs = [g//d for g in gs]
        return ParamRdeSpecialDenomExp(a, b, gs, D)
    elseif ishypertangent(D)
        error("not implemented")
        #return ParamRdeSpecialDenomTan(a, b, gs, D) # not yet implemented
    else
        error("not implemented")
    end
end

"""
    LinearConstraints(a, b, gs, D) -> (qs, M)

Generate linear constraints on the constants.

Given a field `k`, a derivation `D` on `k[t]`, `a`, `b` in `k[t]` and `gs=[g₁,...,gₘ]`,
`g₁`,...,`gₘ` in `k(t)`, return `qs=[q₁,...,qₘ]`, `q₁`,...,`qₘ` in `k[t]`
and a matrix `M` with entries in `k` sucht that for any solution 
`c₁`,...,`cₘ` in `Const(k)` and `p` in `k[t]` of  `a*D(p)+b*p=∑ᵢcᵢ*gᵢ`,
`x=[c₁,...,cₘ]` is a solution of `M*x=0`, and `p` and the `cᵢ` satisfy
 `a*D(p)+b*p=∑ᵢcᵢ*qᵢ`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 7.1, p. 223.
"""
function LinearConstraints(a::P, b::P, gs::Vector{F}, D::Derivation) where
    {P<:PolyElem, F<:FracElem{P}}
    iscompatible(a, D) && iscompatible(b, D) && all([iscompatible(g, D) for g in gs]) || 
        error("polynomials a and b and rational functions g_i must be in the domain of derivation D")
    d = lcm([denominator(g) for g in gs])
    qrs = [divrem(numerator(d*g), d) for g in gs]
    qs = [q for (q, r) in qrs]
    rs = [r for (q, r) in qrs]
    if all([iszero(r) for r in rs])
        N = -1
    else
        N = maximum([degree(r) for r in rs])
    end
    M = [coeff(r, i) for i=0:N, r in rs]
    return qs, M
end

RowEchelon(A::Matrix{T}; cut_zero_rows::Bool=true) where T<:FieldElement = RowEchelon(A, T[], cut_zero_rows=cut_zero_rows)

function RowEchelon(A::Matrix{T}, u::Vector{T}; cut_zero_rows::Bool=true) where T<:FieldElement
    # based on https://github.com/blegat/RowEchelon.jl/blob/master/src/RowEchelon.jl
    # Note: input arguments A, u are changed on output
    nr, nc = size(A)
    uzero = length(u)==0
    i = 1
    j = 1
    while i <= nr && j <= nc        
        p = findfirst(x->!iszero(x), A[i:nr,j])
        if p===nothing
            j += 1
        else
            p = p + i - 1
            for k=j:nc
                A[i, k], A[p, k] = A[p, k], A[i, k]
            end
            if !uzero
                u[i], u[p] = u[p], u[i]
            end
            d = A[i,j]
            for k = j:nc
                A[i,k] //= d
            end
            if !uzero
                u[i] //= d
            end
            for k = 1:nr
                if k != i
                    d = A[k,j]
                    for l = j:nc
                        A[k,l] -= d*A[i,l]
                    end
                    if !uzero
                        u[k] -= d*u[i]
                    end
                end
            end
            i += 1
            j += 1
        end
    end
    if cut_zero_rows
        A = A[1:i-1,:]
    end
    if uzero
        return A
    else
        A, u
    end
end

"""
    ConstantSystem(A[, u], D) -> (B[, v])

Generate a system for the constant solutions

Given a field `K`, a derivation `D` on `K` with constant field `C`, a matrix `A`
with entries in `K` and optionally a vector `u` with coefficients in `K`,
return a matrix `B` with entries in `C` and, in the case that `u` is provided,
a vector `v` with coefficients in `K`. If no `u` is provided, or all entries
of the returned `v` are actually elements of `C`, then the solutions in `C`
of `A*x=u` (resp. `A*x=0` if no `u` is provided) are exactly all the solutions
of `B*x=v` (resp. `B*x=0`). Otherwise, if `v` has a nonconstant coefficient,
`A*x=u` has no constant solution.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 7.1, p. 225.
"""
ConstantSystem(A::Matrix{T}, D::Derivation) where T<:FieldElement =
    ConstantSystem(A, T[], D)

function ConstantSystem(A::Matrix{T}, u::Vector{T}, D::Derivation) where T<:FieldElement
    # check compatibility
    # check dimensions
    # Note: input arguments A, u are changed on output
    uzero = length(u)==0
    if uzero
        A = RowEchelon(A)
    else
        A, u = RowEchelon(A, u)
    end
    m, n = size(A)
    j = 1 
    while j<=n
        i = findfirst(x->!isconstant(x, D), A[:,j])
        if i===nothing
            j += 1
            continue
        end       
        # enlarge A by one row and u by one entry
        A = vcat(A, [zero(A[1,1]) for l=1:1, k=1:n])
        if !uzero
            push!(u, zero(A[1,1]))
        end
        Daij = D(A[i,j])
        for k=1:n
            A[m+1, k] =  D(A[i, k])//Daij
        end
        if !uzero
            u[m+1] = D(u[i])//Daij
        end
        for s=1:m
            asj = A[s,j]
            for k=1:n
                A[s, k] -= asj*A[m+1, k]
            end
            if !uzero
                u[s] -= asj*u[m+1]
            end
        end
        j += 1
        m += 1
    end
    # return only nonzero rows 
    nz = [i for i=1:size(A,1) if !(all([iszero(A[i,j]) for j=1:size(A,2)]) && (uzero || iszero(u[i])))]
    CT = typeof(zero(constant_field(D))) # ensure B has eltype of constant field, even if it is empty
    B = CT[constantize(A[i,j], D) for i in nz, j=1:n]
    if uzero
        return B
    else
        B, u[nz]
    end
end

"""
    ParamRdeBoundDegreePrim(a, b, qs, D) -> n

Bound on polynomial solutions - primitive case.

Given a field `k`, a derivation `D` on `k[t]`, `a`, `b` in `k[t]` and `qs=[q₁,...,qₘ]`,
`q₁`,...,`qₘ` in `k[t]` with `D(t)` in `k` and `a≠0`, return integer `n`
such that `degree(q)≤n` for any solution  `c₁`,...,`cₘ` in `Const(k)` 
and `q` in `k[t]` of  `a*D(q)+b*q=∑ᵢcᵢ*qᵢ`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 7.1, p. 228.
"""
function ParamRdeBoundDegreePrim(a::P, b::P, qs::Vector{P}, D::Derivation) where P<:PolyElem
    isprimitive(D) ||
        error("monomial of derivation D must be primitive")
    iscompatible(a, D) && iscompatible(b, D) && all([iscompatible(q, D) for q in qs]) || 
        error("polynomial a and rational functions b and q_i must be in the domain of derivation D")
    !iszero(a) || error("polynomial a must be nonzero")
    da = degree(a)
    db = degree(b)
    dc = maximum([degree(q) for q in qs])
    if db>da 
        n = max(0, dc-db)
    else
        n = max(0, dc-da+1)
    end
    D0 = BaseDerivation(D)
    if db==da-1
        α = -leading_coefficient(b)//leading_coefficient(a)
        z, s0, ρ = LimitedIntegrate(α, leading_coefficient(D), D0) # not yet implemented
        if ρ>0 && isrational(s0)
            s = rationalize_over_Int(s0)
            if denominator(s)==1
                n = max(n, numerator(s))
            end
        end
    end
    if db==da
        α = -leading_coefficient(b)//leading_coefficient(a)
        z, ρ = InFieldDerivative(α, D0)
        if ρ>0 && !iszero(z)
            β = -leading_coefficient(a*D0(z)+b*z)//(z*leading_coefficient(a))
            w, s0, ρ = LimitedIntegrate(β, leading_coefficient(D), D0) # not yet implemented
            if ρ>0 && isrational(s0)
                m = rationalize_over_Int(s0)
                if denominator(s)==1
                    n = max(n, numerator(s))
                end
            end
        end
    end
    n
end

"""
    ParamRdeBoundDegreeBase(a, b, qs) -> n

Bound on polynomial solutions - base case.

Given a field `k`, `a`, `b` in `k[t]` and `qs=[q₁,...,qₘ]`,
`q₁`,...,`qₘ` in `k[t]` with `a≠0`, return integer `n`
such that `degree(q)≤n` for any solution  `c₁`,...,`cₘ` in `Const(k)` 
and `q` in `k[t]` of `a*(d/dt)(q)+b*q=∑ᵢcᵢ*qᵢ`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 7.1, p. 228.
"""
function ParamRdeBoundDegreeBase(a::P, b::P, qs::Vector{P}) where P<:PolyElem
    !iszero(a) || error("polynomial a must be nonzero")
    da = degree(a)
    db = degree(b)
    dc = maximum([degree(q) for q in qs])
    n = max(0, dc - max(db, da - 1))
    if db==da-1
        s0 = -leading_coefficient(b)//leading_coefficient(a)
        if isrational(s0)
            s = rationalize_over_Int(s0)
            if isone(denominator(s))
                n = max(0, numerator(s), dc - db)
            end
        end
    end
    return n
end

"""
    ParamRdeBoundDegreeExp(a, b, qs, D) -> n

Bound on polynomial solutions - hyperexponential case.

Given a field `k`, a derivation `D` on `k[t]`, `a`, `b` in `k[t]` and `qs=[q₁,...,qₘ]`,
`q₁`,...,`qₘ` in `k[t]` with `D(t)/t` in `k` and `a≠0`, return integer `n`
such that `degree(q)≤n` for any solution  `c₁`,...,`cₘ` in `Const(k)` 
and `q` in `k[t]` of  `a*D(q)+b*q=∑ᵢcᵢ*qᵢ`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 7.1, p. 229.
"""
function ParamRdeBoundDegreeExp(a::P, b::P, qs::Vector{P}, D::Derivation) where P<:PolyElem
    ishyperexponential(D) ||
        error("monomial of derivation D must be hyperexponential")
    iscompatible(a, D) && iscompatible(b, D) && all([iscompatible(q, D) for q in qs]) || 
        error("polynomial a and rational functions b and q_i must be in the domain of derivation D")
    !iszero(a) || error("polynomial a must be nonzero")
    da = degree(a)
    db = degree(b)
    dc = maximum([degree(q) for q in qs])
    n = max(0, dc - max(db, da))
    if da==db
        α = -leading_coefficient(b)//leading_coefficient(a)
        w = coeff(MonomialDerivative(D), 1)
        n0, s, z, ρ = ParametricLogarithmicDerivative(α, w, BaseDerivation(D))
        if ρ<0
            error("ParametricLogarithmicDerivative failed")
        end
        if  ρ>0 && n0==1 && !iszero(z)
            n = max(n, s)
        end
    end
    n
end

"""
    ParamRdeBoundDegreeNonLinear(a, b, qs, D) -> n

Bound on polynomial solutions - nonlinear case.

Given a  field `k`, a derivation `D` on `k[t]`, `a`, `b` in `k[t]` and `qs=[q₁,...,qₘ]`,
`q₁`,...,`qₘ` in `k[t]` with `degree(D(t))≥2` and `a≠0`, return integer `n`
such that `degree(q)≤n` for any solution `c₁`,...,`cₘ` in `Const(k)` 
and `q` in `k[t]` of `a*D(q)+b*q=∑ᵢcᵢ*qᵢ`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 7.1, p. 230.
"""
function ParamRdeBoundDegreeNonLinear(a::P, b::P, qs::Vector{P}, D::Derivation) where P<:PolyElem
    isnonlinear(D) ||
        error("monomial of derivation D must be nonlinear")
    iscompatible(a, D) && iscompatible(b, D) && all([iscompatible(q, D) for q in qs]) || 
        error("polynomial a and rational functions b and q_i must be in the domain of derivation D")
    !iszero(a) || error("polynomial a must be nonzero")
    da = degree(a)
    db = degree(b)
    dc = maximum([degree(q) for q in qs])
    δ = degree(D)
    λ = leading_coefficient(D)
    n = max(0, dc - max(da + δ - 1, db))
    if db==da+δ-1
        s0 = -leading_coefficient(b)/(λ*leading_coefficient(a))
        if isrational(s0)
            s = rationalize_over_Int(s0)
            if isone(denominator(s))
                n = max(0, numerator(s), dc - db)
            end
        end
    end
    n
end

"""
    ParamRdeBoundDegree(a, b, qs, D) -> n

Bound on polynomial solutions.

Given a  field `k`, a derivation `D` on `k[t]`, `a`, `b` in `k[t]` and `qs=[q₁,...,qₘ]`,
`q₁`,...,`qₘ` in `k[t]` with `a≠0`, return integer `n`
such that `degree(q)≤n` for any solution `c₁`,...,`cₘ` in `Const(k)` 
and `q` in `k[t]` of  `a*D(q)+b*q=∑ᵢcᵢ*qᵢ`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 7.1, p. 227.
"""
function ParamRdeBoundDegree(a::P, b::P, qs::Vector{P}, D::Derivation) where P<:PolyElem
    iscompatible(a, D) && iscompatible(b, D) && all([iscompatible(q, D) for q in qs]) || 
        error("polynomial a and rational functions b and q_i must be in the domain of derivation D")
    !iszero(a) || error("polynomial a must be nonzero")
    if isbasic(D) || (isprimitive(D) && isone(MonomialDerivative(D)))
        return ParamRdeBoundDegreeBase(a, b, qs) 
    elseif isprimitive(D)
        return ParamRdeBoundDegreePrim(a, b, qs, D)
    elseif ishyperexponential(D)
        return ParamRdeBoundDegreeExp(a, b, qs, D) 
    elseif isnonlinear(D)
        return ParamRdeBoundDegreeNonLinear(a, b, qs, D)
    else
        error("not implemented")
    end
end

"""
    ParSPDE(a, b, qs, D, n) -> (A, B, Qs, rs, N)

Parametric Special Polynomial Differential Equation algorithm.

Given a field `k`, a derivation `D` on `k[t]`, `a`, `b` in `k[t]`, `qs=[q₁,...,qₘ]`,
`q₁`,...,`qₘ` in `k[t]` and an integer `n` with `degree(a)>0` and `gcd(a,b)=1`, return `A`, `B`,
`Qs=[Q₁,...,Qₘ]` and `N` such that for any solution `c₁`,...,`cₘ` in `Const(k)` 
and `q` in `k[t]` of degree at most `n` of `a*D(q)+b*q=∑ᵢcᵢ*qᵢ`, `p=(q-∑ᵢcᵢ*rᵢ)/a`
has degree at most `N` and satisfies `A*D(p)+B*p=∑ᵢcᵢ*Qᵢ`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 7.1, p. 231.
"""
function ParSPDE(a::P, b::P, qs::Vector{P}, D::Derivation, n::Int) where P<:PolyElem
    iscompatible(a, D) && iscompatible(b, D) && all([iscompatible(q, D) for q in qs]) || 
        error("polynomial a and rational functions b and q_i must be in the domain of derivation D")
    degree(a)>0 || error("degree(a) must be > 0")
    degree(gcd(a, b))<=0 || error("gcd(a,b) must be 1")
    rzs = [gcdx(b, a, q) for q in qs]
    a, b + D(a), [z-D(r) for (r, z) in rzs], [r for (r, z) in rzs], n-degree(a)
end

"""
    ParamPolyRischDENoCancel1(b, qs, D, n) -> (hs, A)

Parametric polynomial Risch differential equation - no cancellation.

Given a field `k`, a derivation `D` on `k[t]`, `b` in `k[t]`, `qs=[q₁,...,qₘ]`,
`q₁`,...,`qₘ` in `k[t]` and an integer `n` with `b≠0` and either
`D=d/dt` or `degree(b)>max(0, degree(D(t))-1)`, return `hs=[h₁,...,hᵣ]`,
`h₁`,...,`hᵣ` in `k[t]` and  a matrix `A` with entries in `Const(k)` such that
if `c₁`,...,`cₘ` in `Const(k)` and `q` in `k[t]` satisfy `degree(q)<=n` and
`D(q)+b*q=∑ᵢcᵢ*qᵢ` then `q=∑ⱼdⱼ*hⱼ` where `d₁`,...,`dᵣ` are in `Const(k)` and
`A*[c₁,...,cₘ,d₁,...,dᵣ]=0`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 7.1, p. 234.
"""
function ParamPolyRischDENoCancel1(b::P, qs::Vector{P}, D::Derivation, n::Int) where P<:PolyElem 
    # Note: this implementation changes the input parameters qs!
    iscompatible(b, D) && all([iscompatible(q, D) for q in qs]) || 
        error("polynomials a and q_i must be in the domain of derivation D")
    !iszero(b) || error("polynomial b must be nonzero")
    isbasic(D) || degree(b)>max(0, degree(D)-1) || 
        error("either derivation D must be basic or degree(b)>max(0, degree(D)-1)")
    t = gen(parent(b))
    db = degree(b)
    bd = leading_coefficient(b)
    m = length(qs)
    hs = [zero(b) for i=1:m]
    ss = [zero(bd) for i=1:m]
    while n>=0
        for i=1:m
            ss[i] = coeff(qs[i], n + db)//bd
            sitn = ss[i]*t^n
            hs[i] += sitn
            qs[i] -= D(sitn) + b*sitn
        end
        n -= 1
    end
    if all([iszero(q) for q in qs])
        dc = -1
    else
        dc = maximum([degree(q) for q in qs])
    end    
    M = [coeff(q, i) for i=0:dc, q in qs]
    A = ConstantSystem(M, BaseDerivation(D))
    C = constant_field(D)
    neq = size(A, 1)
    A = vcat(hcat(A, zeros(C, neq, m)), zeros(C, m, 2*m))
    for i=1:m
        A[i+neq, i] = one(C)
        A[i+neq, m+i] = -one(C)
    end
    hs, A
end

"""
    ParamPolyRischDENoCancel2(b, qs, D, n) -> (hs, A)

Parametric polynomial Risch differential equation - no cancellation.

Given a field `k`, a derivation `D` on `k[t]`, `b` in `k[t]`, `qs=[q₁,...,qₘ]`,
`q₁`,...,`qₘ` in `k[t]` and an integer `n` with `degree(b)<degree(D(t)-1)` and either
`D=d/dt` or `degree(D(t))≥2`, return `hs=[h₁,...,hᵣ]`,
`h₁`,...,`hᵣ` in `k[t]` and  a matrix `A` with entries in `Const(k)` such that
if `c₁`,...,`cₘ` in `Const(k)` and `q` in `k[t]` satisfy `degree(q)≤n` and
`D(q)+b*q=∑ᵢcᵢ*qᵢ` then `q=∑ⱼdⱼ*hⱼ` where `d₁`,...,`dᵣ` are in `Const(k)` and
`A*[c₁,...,cₘ,d₁,...,dᵣ]=0`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 7.1, p. 238.
"""
function ParamPolyRischDENoCancel2(b::P,  qs::Vector{P}, D::Derivation, n::Int) where P<:PolyElem 
    iscompatible(b, D) && all([iscompatible(q, D) for q in qs]) || 
        error("polynomials a and q_i must be in the domain of derivation D")
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
    m = length(qs)
    hs = [zero(b) for i=1:m]
    ss = [zero(λ) for i=1:m]
    while n>0
        nλ = n*λ
        for i=1:m
            ss[i] = coeff(qs[i], n + δ -1)//(nλ)
            sitn = ss[i]*t^n
            hs[i] += sitn
            qs[i] -= D(sitn) + b*sitn
        end
        n -= 1
    end
    C = constant_field(D)
    if degree(b)>0
        for i=1:m
            ss[i] = coeff(qs[i], degree(b))//leading_coefficient(b)
            hs[i] += ss[i]
            qs[i] -= D(ss[i]) + b*ss[i]
        end
        if all([iszero(q) for q in qs])
            dc = -1
        else
            dc = maximum([degree(q) for q in qs])
        end
        M = [coeff(q, i) for i=0:dc, q in qs]
        A = ConstantSystem(M, BaseDerivation(D))
        neq = size(A, 1)
        A = vcat(hcat(A, zeros(C, neq, m)), zeros(C, m, 2*m))
        for i=1:m
            A[i+neq, i] = one(C)
            A[i+neq, m+i] = -one(C)
        end
        return hs, A
    else
        D0 = BaseDerivation(D)
        b0 = constant_coefficient(b) # b \in k
        fs, B = ParamRischDE(b0, [constant_coefficient(q) for q in qs], D0)
        if all([iszero(q) for q in qs])
            if all([iszero(D0(f)+b0*f) for f in fs])
                dc = -1
            else
                dc = 0
            end
        else
            dc = maximum([degree(q) for q in qs])
        end
        r = length(fs)
        M = zeros(parent(b0), dc+1, m+r)
        for i=0:dc
            for j = 1:m
                M[i+1,j] = coeff(qs[j], i)
            end
        end
        if dc>=0
            for j=1:r
                M[1,j+m] = -D0(fs[j]) - b0*fs[j]
            end
        end
        A = ConstantSystem(M, D0)
        A = vcat(A, B)
        neq = size(A, 1)
        A = vcat(hcat(A, zeros(C, neq, m)), zeros(C, m, 2*m+r))
        for i=1:m
            A[i+neq, i] = one(C)
            A[i+neq, m+r+i] = -one(C)
        end
        return vcat(fs .+ zero(b), hs), A
    end
end

"""
    ParamPolyRischDECancelLiouvillian(b, qs, D, n) -> (hs, A)

Parametric polynomial Risch differential equation - no cancellation.

Given a field `k`, a derivation `D` on `k[t]`, `b` in `k`, `qs=[q₁,...,qₘ]`,
`q₁`,...,`qₘ` in `k[t]` and an integer `n` with `D≠d/dt` and `D(t)` in `k`
or `D(t)/t` in `k`, return `hs=[h₁,...,hᵣ]`,
`h₁`,...,`hᵣ` in `k[t]` and  a matrix `A` with entries in `Const(k)` such that
if `c₁`,...,`cₘ` in `Const(k)` and `q` in `k[t]` satisfy `degree(q)≤n` and
`D(q)+b*q=∑ᵢcᵢ*qᵢ` then `q=∑ⱼdⱼ*hⱼ` where `d₁`,...,`dᵣ` are in `Const(k)` and
`A*[c₁,...,cₘ,d₁,...,dᵣ]=0`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 7.1, p. 241.
"""
function ParamPolyRischDECancelLiouvillian(b::T,  qs::Vector{P}, D::Derivation, n::Int) where 
    {T<:RingElement, P<:PolyElem{T}} 
    isprimitive(D) || ishyperexponential(D) ||
    error("monomial of derivation D must be primitive or hyperexponential")
    D0 = BaseDerivation(D)
    iscompatible(b, D0) || 
        error("coefficient b must be in the domain of the base derivation of D") 
    all([iscompatible(q, D) for q in qs]) || 
        error("polynomials q_i must be in the domain of derivation D")
    H = MonomialDerivative(D)
    C = constant_field(D)
    if ishyperexponential(D)
        w = coeff(H, 1)
    else
        w = zero(parent(b))
    end
    t = gen(parent(H))
    m = length(qs)
    first = true
    qns = copy(qs)
    hs = []
    while n>=0
        @info "m=$m\nlength(qns)=$(length(qns))"
        @assert length(qns)==m
        fns, An = ParamRischDE(b + n*w, [coeff(q, n) for q in qns], D0) 
        @assert length(fns)+m==size(An,2)
        hns = [f*t^n for f in fns]
        qns = vcat(qns, [D(h) - b*h for h in hns])
        r = length(fns)
        if first
            A = An
            hs = hns
            first = false
        else
            @info "m=$m\nr=$r\nsize(A)=$(size(A))\nsize(An)=$(size(An))"
            A = vcat(hcat(An,                               zeros(C, size(An,1), size(A,2)-m)), 
                     hcat(A[:,1:m], zeros(C, size(A,1), r), A[:,(m+1):end]))
            hs = vcat(hns, hs)
        end
        m = m + r
        n -= 1
    end
    r = length(hs)
    Dhbhs = [D(h)+b*h for h in hs]
    if all([iszero(q) for q in qs]) && all([iszero(Dhbh) for Dhbh in Dhbhs])        
        dc = -1
    else
        dc = max( maximum([degree(q) for q in qs]), maximum([degree(Dhbh) for Dhbh in Dhbhs]))
    end
    M = zeros(parent(b), dc+1, m+r)
    for i=0:dc
        for j = 1:m
            M[i+1,j] = coeff(qs[j], i)
        end
        for j=1:r
            M[i,j+m] = -coeff(Dhbhs[j], i)
        end
    end
    A0 = ConstantSystem(M, D0)
    A = vcat(A0, A)
    hs, A
end

"""
    ParamPolyRischDE(b, qs, D, n) -> (hs, A)

Parametric polynomial Risch differential equation.

Given a field `k`, a derivation `D` on `k[t]`, `b` in `k[t]`, `qs=[q₁,...,qₘ]`,
`q₁`,...,`qₘ` in `k[t]` and an integer `n`, return `hs=[h₁,...,hᵣ]`,
`h₁`,...,`hᵣ` in `k[t]` and  a matrix `A` with entries in `Const(k)` such that
if `c₁`,...,`cₘ` in `Const(k)` and `q` in `k[t]` satisfy `degree(q)≤n` and
`D(q)+b*q=∑ᵢcᵢ*qᵢ` then `q=∑ⱼdⱼ*hⱼ` where `d₁`,...,`dᵣ` are in `Const(k)` and
`A*[c₁,...,cₘ,d₁,...,dᵣ]=0`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 7.1, p. 241.
"""
function ParamPolyRischDE(b::P,  qs::Vector{P}, D::Derivation, n::Int) where P<:PolyElem
    iscompatible(b, D) || all([iscompatible(q, D) for q in qs]) ||
        error("coefficient b and polynomials q_i must be in the domain of derivation D")
    basic_case = isbasic(D) || (isprimitive(D) && isone(H))
    δ = degree(D)
    if !iszero(b) && (isbasic(D) || degree(b)>max(0, δ-1))
        @info "case: NoCancel1"
        return ParamPolyRischDENoCancel1(b, qs, D, n)
    elseif (iszero(b) || degree(b)<δ-1) && (isbasic(D) || δ>=2)
        @info "case: NoCancel2"
        return ParamPolyRischDENoCancel2(b, qs, D, n)
    elseif δ>=2 && degree(b)==δ-1
        error("not implemented")
        # TODO: implement this case
    elseif isprimitive(D) || ishyperexponential(D)
        @info "case: CancelLiouville"
        @assert δ<=1 && degree(b)<=0 && !basic_case
        return ParamPolyRischDECancelLiouvillian(constant_coefficient(b), qs, D, n)
    else
        error("not implemented")
    end
end

"""
    ParamPolyCoeffsRischDE(a, b, gs, D) -> (hs, A)

Parametric Risch differential equation with polynomial coefficients.

Given a field `k`, a derivation `D` on `k[t]`, `a`, `b` in `k[t]` and `gs=[g₁,...,gₘ]`,
`g₁`,...,`gₘ` in `k(t)` with `a!=0`, return `hs=[h₁,...,hᵣ]`,
`h₁`,...,`hᵣ` in `k(t)` and  a matrix `A` with entries in `Const(k)` such that
`c₁`,...,`cₘ` in `Const(k)` and `q` in `k[t]` is a solution of 
`a*D(q)+b*q=∑ᵢcᵢ*gᵢ` if and only if `y=∑ⱼdⱼ*hⱼ` for `d₁`,...,`dᵣ` in `Const(k)` with
`A*[c₁,...,cₘ,d₁,...,dᵣ]=0`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 7.1, p. 222.
"""
function ParamPolyCoeffsRischDE(a::P, b::P, gs::Vector{F}, D::Derivation; n::Int=-123456789) where
    {P<:PolyElem, F<:FracElem{P}}
    iscompatible(a, D) && iscompatible(b, D) && all([iscompatible(g, D) for g in gs]) || 
        error("polynomials a and b and rational functions g_i must be in the domain of derivation D")
        m = length(gs)
    d = gcd(a, b)
    a = divexact(a, d)
    b = divexact(b, d)
    gs = [g//d for g in gs]
    qs, M = LinearConstraints(a, b, gs, D)
    A = ConstantSystem(M, BaseDerivation(D))
    if n==-123456789
        n  = ParamRdeBoundDegree(a, b, qs, D)
    end
    @info "degree bound n=$n"
    aprod = one(parent(a))
    Rs = zeros(parent(a//one(a)), m)
    while n>=0 && degree(a)>0
        a, b, qs, rs, n = ParSPDE(a, b, qs, D, n)
        d = gcd(a, b)
        a = divexact(a, d)
        b = divexact(b, d)
        gs = [q//d for q in qs]
        qs, M = LinearConstraints(a, b, gs, D)
        A = vcat(A, ConstantSystem(M, BaseDerivation(D)))
        aprod *= a
        for i=1:m
            Rs[i] = (Rs[i] + rs[i])//a
        end
    end
    C = constant_field(D)
    if n<0
        @info "case: n<0"
        hs = F[]
        A = vcat(A, ConstantSystem(RowEchelon([q//1 for i=1:1, q in qs]), D))
    else
        a = constant_coefficient(a)
        b = divexact(b, a)
        qs = [divexact(q, a) for q in qs]
        hs, A1 = ParamPolyRischDE(b, qs, D, n)
        A = vcat(hcat(A, zeros(C, size(A, 1), length(hs))), A1)
    end
    r = length(hs)
    s = sum([1 for R in Rs if !iszero(R)])
    hs = vcat([aprod*h//1 for h in hs], [aprod*R for R in Rs if !iszero(R)])    
    neq = size(A, 1)
    A = vcat(hcat(A, zeros(C, neq, s)), zeros(C, s, m+r+s))
    i1 = 0
    for i=1:m
        if !iszero(Rs[i])
            i1 += 1
            A[neq+i1, i] = one(C)
            A[neq+i1, m+r+i1] = -one(C)
        end
    end
    hs, A
end

"""
    ParamRischDE(f, gs, D) -> (hs, A)

Parametric Risch differential equation.

Given a field `K`, a derivation `D` on `K`, `f` in `K`, `gs=[g₁,...,gₘ]`,
`g₁`,...,`gₘ` in `K`, return `hs=[h₁,...,hᵣ]`,
`h₁`,...,`hᵣ` in `K` and  a matrix `A` with entries in `Const(K)` such that
 `c₁`,...,`cₘ` in `Const(K)` and `y` in `K` is a solution of 
`D(y)+f*y=∑ᵢcᵢ*gᵢ` if and only if `y=∑ⱼdⱼ*hⱼ` for `d₁`,...,`dᵣ` in `Const(K)` with
`A*[c₁,...,cₘ,d₁,...,dᵣ]=0`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 7.1, p. 217.
"""
function ParamRischDE(f::F, gs::Vector{F}, D::NullDerivation) where F<:FieldElem
    #base case => pure (linear) algebra problem ...
    iscompatible(f, D) && all(iscompatible(g, D) for g in gs) || 
        error("rational functions f and g_i must be in the domain of derivation D")
    m = length(gs)
    C = parent(f)
    if iszero(f)
        qz = [i for i=1:m if iszero(gs[i])]
        r = length(qz)
        A = zeros(C, r + (r<m ? 1 : 0) , m+r) 
        for i=1:r
            A[i, qz[i]] = one(C)
            A[i, m+i] = -one(C)
        end
        hs = [one(C) for i=1:r]
        if r<m
            qnz = [i for i=1:m if !iszero(gs[i])]
            for i=1:m
                if !iszero(gs[i])
                    A[r+1, i] = gs[i]
                end
            end
        end
    else
        A = zeros(C, m , 2*m) 
        for i=1:m
            A[i, i] = one(C)
            A[i, m+i] = -one(C)
        end
        hs = [gs[i]//f for i=1:m]
    end
    hs, A
end

function ParamRischDE(f::F, gs::Vector{F}, D::Derivation) where 
    {P<:PolyElem, F<:FracElem{P}}
    iscompatible(f, D) && all(iscompatible(g, D) for g in gs) || 
        error("rational functions f and g_i must be in the domain of derivation D")

    h0 = WeakNormalizer(f, D)
    @info "weak normalizer h0=$h0"

    f1 = f - D(h0)//h0
    gs = [h0*g for g in gs]
    a, b, gs, h1 = ParamRdeNormalDenominator(f1, gs, D)
    @info "normal denominator h1=$h1"

    a, b, gs, h2 =  ParamRdeSpecialDenominator(a, b, gs, D)
    @info "special denominator h2=$h2"

    hs, A = ParamPolyCoeffsRischDE(a, b, gs, D)

    h012 = h0*h1*h2
    [h//h012 for h in hs], RowEchelon(A)
end
    
"""
    LimitedIntegrateReduce(f, ws, D) -> (a, b, h, N, g, vs)

Reduction to a polynomial problem.

Given a field `k`, a derivation `D` on `k[t]`, `f` in `k(t)`, `ws=[w₁,...,wₘ]`,
`w₁`,...,`wₘ` in `k(t)`, return `a`, `b`, `h`, `N`, `g`, `vs=[v₁,...,vₘ]` such that 
`a`, `b`, `h` are in `k[t]`, `N` is an integer, `g`, `v₁`,...,`vₘ` are in `k(t)`
and for any solution `v` in `k(t)`, `c_1`,...,`cₘ` in Const(k) of `f = D(v)+∑ᵢcᵢ*wᵢ`, 
`p=v*h` is in `k⟨t⟩` and `p` and the `c_i` satisfy `a*D(p)+b*p=g+∑ᵢcᵢ*vᵢ`.
(Here, `k⟨t⟩` denotes the elements of `k(t)` which are reduced w.r.t. `D`.)

Furthermore, if `S₁ⁱʳʳ==Sⁱʳʳ`, which is indicated by `is_Sirr1_eq_Sirr(D)==true`,
then `p` is in `k[t]`, and if `t` is nonlinear or Liouvillian over `k`, then `degree(p)<=N`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 7.1, p. 248.
"""
function LimitedIntegrateReduce(f::F, ws::Vector{F}, D::Derivation) where 
    {P<:PolyElem, F<:FracElem{P}}
    iscompatible(f, D) && all(iscompatible(w, D) for w in ws) || 
        error("rational functions f and w_i must be in the domain of derivation D")
    dn, ds = SplitFactor(denominator(f), D)
    eness = [SplitFactor(denominator(w), D) for w in ws]
    c = lcm(vcat(dn, [en for (en, es) in eness]))
    hn = gcd(c, derivative(c))
    a = hn
    b = -D(hn)
    N = 0
    if is_Sirr1_eq_Sirr(D)
       hn = lcm(vcat(ds, [es for (en, es) in eness]))
       a = hn*hs
       b = -D(hn)-divexact(hn*D(hs),hs)
       μ = min(valuation_infinity(f), minimum([valuation(w) for w in ws]))
       N = degree(hn) + degree(hs)+max(0, 1 - degree(D) - μ)
    end
    ahn = a*hn
    a, b, a, N, ahn*f, [-ahn*w for w in ws] 
end

function LimitedIntegrate(f::F, ws::Vector{F}, D::Derivation) where 
    {P<:PolyElem, F<:FracElem{P}}
    iscompatible(f, D) && all(iscompatible(w, D) for w in ws) || 
        error("rational functions f and w_i must be in the domain of derivation D")
        (a, b, h, N, g, vs) = LimitedIntegrateReduce(f, ws, D)
    if isSiir1_eq_Sirr(D)

    else
    end
end




