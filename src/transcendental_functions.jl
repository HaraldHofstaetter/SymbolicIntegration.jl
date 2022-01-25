# This file contains algorithms needed for the integratiorn of 
# transcendental functions from chapter 5 of the book
#
#    Manuel Bronstein, Symbolic Integration I: Transcendental Functions,
#    2nd ed., Springer 2005. 
#


"""
    HermiteReduce(f, D) -> (g, h, r)

Hermite reduction - quadratic version.

Given a field `k`, a derivation `D` on `k(t)` and `f` in `k(t)`, return `g`, `h`, `r` in `k(t)`
such that `f=D(g)+h+r`, `h` is simple and `r` is reduced.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 5.4, p. 139.
"""
function HermiteReduce(f::FracElem{P}, D::Derivation) where {T<:FieldElement, P<:PolyElem{T}}    
    iscompatible(f, D) || error("rational function f must be in the domain of derivation D")
    fp, fs, fn = CanonicalRepresentation(f, D)
    a = numerator(fn)
    d = denominator(fn)
    ds = Squarefree(d)
    g = zero(f)
    for i=2:length(ds)
        if degree(ds[i])>0
            v = ds[i]
            u = divexact(d, v^i)
            for j=i-1:-1:1
                b, c = gcdx(u*D(v), v, -1//j*a)
                g += b//v^j
                a = -j*c - u*D(b)
            end
            d = u*v
        end
    end
    q, r = divrem(a, d)
    g, r//d, q + fp + fs
end

"""
    PolynomialReduce(p, D) -> (q, r)

Polynomial reduction.

Given a field `k`, a derivation `D` on `k(t)` and `p` in `k[t]` where `t` is a nonlinear
monomial over `k`, return `q`, `r` in `k[t]`
such that `p=D(q)+r` and `degree(r)<degree(D(t))`. 

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 5.4, p. 141.
"""
function PolynomialReduce(p::P, D::Derivation) where {T<:FieldElement, P<:PolyElem{T}}
    iscompatible(p, D) || error("polynomial p must be in the domain of derivation D")
    isnonlinear(D) || error("monomial of derivation D must be nonlinear")
    δ = degree(D)
    λ = leading_coefficient(D)
    t = gen(domain(D))
    if degree(p)<δ
        return (0, p)
    end
    m = degree(p) - δ +1
    q0 = (leading_coefficient(p)//(m*λ))*t^m
    q, r = PolynomialReduce(p - D(q0), D)
    q0 + q, r
end

"""
    ResidueReduce(f, D) -> (ss, Ss, ρ)

Polynomial reduction.

Given a field `k`, a derivation `D` on `k(t)` and `f` in `k(t)`, return either `ρ=1`
and `ss=[s₁,...,sₘ]`, `sᵢ` in `k[z]`, `Ss=[S₁,...Sₘ]`, `Sᵢ` in `k[z,t]` where
`z` is a new indeterminate over `k` such that `f-D(g)` is in `k[t]` where
`g=∑ᵢ∑_{α:sᵢ(α)=0}α*log(Sᵢ(α,t))`, or `ρ=0` and such `ss` and `Ss` such that
`f+h` and `f+h-D(g)` do not have an elementary integral over `k(t)` for any
`h` in `k⟨t⟩`.

(Here, `k⟨t⟩` denotes the elements of `k(t)` which are reduced w.r.t. `D`.)

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 5.6, p. 153.
"""
function ResidueReduce(f::F, D::Derivation; symbol=:α) where 
    {T<:RingElement, P<:PolyElem{T}, F<:FracElem{P}}
    iscompatible(f, D) || error("rational function f must be in the domain of derivation D")
    issimple(f, D) || error("rational function f must be simple with respect to derivation D")
    d = denominator(f)
    (p,a) = divrem(numerator(f), d)
    # For SubResultant with respect to t we have to construct the 
    # polynomial ring k[z][t] with z, t in this order (!)
    kz, z = PolynomialRing(base_ring(d), symbol)
    kzt, t = PolynomialRing(kz, var(parent(d)))
    if degree(D(d))<=degree(d)
        r, Rs = SubResultant(d(t), a(t) - z*D(d)(t))
    else
        r, Rs = SubResultant(a(t) - z*D(d)(t), d(t))
    end
    κD = CoefficientLiftingDerivation(kz, BaseDerivation(D))
    ns, ss = SplitSquarefreeFactor(r, κD)    
    ds = degree.(ss)
    ss = [ss[i] for i=1:length(ss) if ds[i]>0]
    Ss = typeof(t)[] 
    ii = 1
    for i=1:length(ds)
        if ds[i]>0
            if i==degree(d)
                S = d(t)
            else
                m = findfirst(z->z==i, degree.(Rs))
                S =  Rs[m]
                As = Squarefree(leading_coefficient(S))
                for j=1:length(As)
                    S = divexact(S, gcd(As[j],ss[ii])^j)
                end
            end
            push!(Ss, S)
            ii+=1                          
        end
    end
    b = degree(prod(ns))==0
    ss, Ss, b
end


"""
    ConstantPart(ss, Ss, D) -> (αs, gs, ss1, Ss1)

Given the output `ss=[s₁,...,sₘ]`, `sᵢ` in `k[z]`, `Ss=[S₁,...Sₘ]`, `Sᵢ` in `k[z,t]` 
of `ResidueReduce` and the derivation D on k(t) which was used by `ResidueReduce`
return  `αs=[α₁,...,αᵣ]` consisting of the roots of those `sᵢ` that have all its roots in `Const(k)` and the corresponding
`gs=[g₁,...,gᵣ]` where `gⱼ` in `k[t]` and`gⱼ(t) = Sᵢ(αⱼ,t)`. The remaining `sᵢ` that have at least one root not in `Const(k)`
and the corresponding `Sᵢ` are returned in `ss1` and `Ss1`.
"""
function ConstantPart(ss::Vector{P}, Ss::Vector{PP}, D::Derivation) where  {P<:PolyElem, PP<:PolyElem{P}}
    length(ss)==length(Ss) || error("lengths must match")
    if isempty(ss)
        return [], [], ss, Ss
    end
    Ss1 = eltype(Ss)[]
    ss1 = eltype(ss)[]    
    αs = zeros(constant_field(D), 0)
    gs = P[]
    D1 = CoefficientLiftingDerivation(parent(ss[1]), BaseDerivation(D))
    for i=1:length(ss)        
        rs = constant_roots(ss[1], D1)
        if length(rs)==degree(ss[i]) # all roots found
            for α in rs                
                push!(αs, α)                
                g = map_coefficients(c->c(α), Ss[i])
                push!(gs, g)
            end
        else
            push!(Ss1, Ss[i])
            push!(ss1, ss[i])
        end
    end
    αs, gs, ss1, Ss1
end


"""
    IntegratePrimitivePolynomial(p, D) -> (q, ρ)

Integration of polynomials in a primitive extension.

Given a field `k`, a derivation `D` on `k(t)` such that `t` is a primitive monomial over `k`
and `p` in `k[t]`, return either `ρ=1` and `q` in `k[t]` such that `p-D(q)` is in `k`, or
`ρ=0` and  `q` in `k[t]` such that `p-D(q)` does not have an elementary integral over
`k(t)`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 5.8, p. 158.
"""
function IntegratePrimitivePolynomial(p::P, D::Derivation) where 
    {T<:RingElement, P<:PolyElem{T}}
    iscompatible(p, D) || error("rational function p must be in the domain of derivation D")
    isprimitive(D) || error("monomial of derivation D must be primitive")
    if degree(p)<=0
        return zero(p), 1
    end
    a = leading_coefficient(p)
    b, c, β = LimitedIntegrate(a, leading_coefficient(D), BaseDerivation(D))
    if β<=0 
        return zero(p, 0)
    end
    m = degree(p)
    t = gen(parent(p))
    q0 = (c//(m+1))*t^(m+1) + b*t^m
    q, β = IntegratePrimitivePolynomial(p-D(q0), D)
    return q+q0, β
end

"""
    IntegrateHyperexponentialPolynomial(p, D) -> (q, ρ)

Integration of hyperexponential polynomials.

Given a field `k`, a derivation `D` on `k(t)` such that `t` is a hyperexponential monomial over `k`
and `p` in `k⟨t⟩=k[t,t⁻¹]`, return either `ρ=1` and `q` in `k[t,t⁻¹]` such that `p-D(q)` is in `k`, or
`ρ=0` and  `q` in `k[t,t⁻¹]` such that `p-D(q)` does not have an elementary integral over
`k(t)`.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 5.9, p. 162.
"""
function IntegrateHyperexponentialPolynomial(p::F, D::Derivation) where 
    {T<:RingElement, P<:PolyElem{T}, F<:FracElem{P}}
    iscompatible(p, D) || error("rational function p must be in the domain of derivation D")
    ishyperexponential(D) || error("monomial of derivation D must be hyperexponential")
    isreduced(p, D) || error("raional function p must be reduced.")
    q = zero(p)
    ρ = 1
    if iszero(p) 
        # Note: with the conventions in Bronstein's book the for loop below would
        # run from i=+infinity to i=-infinity for p=0, i.e., not at all.
        # But it's cleaner to handle the case p=0 separately.
        return q, ρ
    end
    t = gen(base_ring(parent(p)))
    w = coeff(MonomialDerivative(D), 1) # Dt/t
    for i=valuation(p, t):-valuation_infinity(p)
        if i!=0
            a = coeff(numerator(p), i) - coeff(denominator(p), i)
            v, ρ1 = RischDE(i*w, a, BaseDerivation(D))
            if ρ1==0
                ρ = 0
            else 
                q += v*t^i
            end
        end
    end
    q, ρ
end

"""
    InFieldDerivative(f, D) -> (u, ρ)

Given a field `K`, a derivation `D` on `K` and `f` in `K`, return either `ρ=0`, in which case
the equation `D(u)=f` does not have a solution `u` in `K`, or `ρ=1` and a solution `u` in `K`
of that equation.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 5.12, p. 175.
"""
function InFieldDerivative(f::F, D::Derivation) where F<:FieldElement
    # base case f \in constant field, D must be the null derivation
    iscompatible(f, D) || error("field element f must be in the domain of derivation D")
    iszero(D) || error("base case only for null derivations")
    if iszero(f)
        return zero(f), 1
    else
        return zero(f), 0 
    end
end

function InFieldDerivative(f::F, D::Derivation) where 
    {T<:RingElement, P<:PolyElem{T}, F<:FracElem{P}}
    # See Bronstein's book, Section 5.12, p. 175
    iscompatible(f, D) || error("rational function f must be in the domain of derivation D")
    Z = zero(f)
    no_solution = (Z, 0)
    g, h, r = HermiteReduce(f, D)
    if !isone(denominator(h))
        # no solution, h returned by HermiteReduce not a polynomial
        return no_solution
    end
    p = h + r # reduced 
    @assert isreduced(p, D)
    if isprimitive(D)
        # p reduced => polynomial in this case
        p = numerator(p)
        q, ρ = IntegratePrimitivePolynomial(p, D)
        if ρ<=0
            return no_solution
        end
        a0 = p-D(q)
        @assert degree(a0)<=0 # p-D(q) ∈ k
        a = constant_coefficient(a0)        
        v, c, ρ = LimitedIntegrate(a, leading_coefficient(D), BaseDerivation(D)) 
        if ρ<=0
            return no_solution
        end
        return g + q + v + c*MonomialDerivative(D), 1
    else # nonlinear case  # TODO: minor modification mentioned near the top of p.176
        if ishyperexponential(D)
            q, ρ = IntegrateHyperexponentialPolynomial(p, D)
            if ρ<=0
                return no_solution
            end
        elseif ishyperexponential(D)
            throw(NotImplemented("InFieldDerivative: hypertangent case"))
        else
            H = MonomialDerivative(D)
            throw(NotImplemented("InFieldDerivative: monomial deivative =$H"))
        end
        a0 = p-D(q)
        @assert isone(denominator(a0)) && degree(numerator(a0))<=0 # p-D(q) ∈ k
        a = constant_coefficient(numerator(a0))
        v, ρ = InFieldDerivative(a, BaseDerivation(D))
        if ρ<=0
            return no_solution
        end
        return g + q + v, 1
    end
end

"""
    InFieldLogarithmicDerivative(f, D) -> (u, ρ)

Given a field `K`, a derivation `D` on `K` and `f` in `K`, return either `ρ=0`, in which case
the equation `D(u)/u=f` does not have a nonzero  solution `u` in `K`, or `ρ=1` and a nonzero 
solution `u` in `K` of that equation.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 5.12, p. 176.
"""
function InFieldLogarithmicDerivative(f::F, D::Derivation) where F<:FieldElement 
    n, v, β = InFieldLogarithmicDerivativeOfRadical(f, D, expect_one=true)
    @assert β<=0 || n==1
    v, β
end

"""
    InFieldLogarithmicDerivativeOfRadical(f, D) -> (n, u, ρ)

Given a field `K`, a derivation `D` on `K` and `f` in `K`, return either `ρ=0`, in which case
the equation `D(u)/u=n*f` does not have a solution `u≠0` in `K` and integer `n≠0`, or `ρ=1` and a solution 
`u` and `n` of that equation.

See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 5.12, p. 177.
"""
function InFieldLogarithmicDerivativeOfRadical(f::F, D::Derivation; expect_one::Bool=false) where F<:FieldElement
    # base case f \in constant field, D must be the null derivation
    iscompatible(f, D) || error("field element f must be in the domain of derivation D")
    iszero(D) || error("base case only for null derivations")
    if iszero(f)
        return 1, one(f), 1
    else
        return 0, zero(f), 0 # no solution (n must be !=0)
    end
end

function InFieldLogarithmicDerivativeOfRadical(f::F, D::Derivation; expect_one::Bool=false) where 
    {T<:RingElement, P<:PolyElem{T}, F<:FracElem{P}}
    iscompatible(f, D) || error("rational function f must be in the domain of derivation D")
    if iszero(f)
        return 1, one(f), 1
    end
    Z = zero(f)
    no_solution = (0, Z, 0)
    if !issimple(f, D)
        return no_solution 
    end
    if isone(denominator(f))
        m = 1
        Dg = Z 
        v = one(f)
    else
        Rs, Gs, β = ResidueReduce(f, D)
        if length(Rs)==0
            m = 1
            Dg = Z 
            v = one(f)
        else
            if !all([all(isrational.(coefficients(R))) for R in Rs])
                # no solution, Rothstein-Trager resultant has non-rational coefficients
                return no_solution
            end
            Rs1 = [map_coefficients(c->convert(fmpq, rationalize(c)), R) for R in Rs]
            As1 = [roots(R) for R in Rs1]
            if !(all([length(As1[i])==degree(Rs1[i]) for i=1:length(As1)]) &&
                all([all(isrational.(As1[i])) for i=1:length(As1)]) )
                # no solution, not all roots of the Rothstein-Trager resultant are rational
                return no_solution
            end
            As = [[rationalize_over_Int(a) for a in as] for as in As1]
            if expect_one 
                if !all([all([isone(denominator(a)) for a in as]) for as in As])
                    # no solution, not all roots of the Rothstein-Trager resultant are integers"
                    return no_solution
                end
                m = 1
            else
                m = gcd([gcd(denominator.(as)) for as in As])
            end
            Dg = Z
            v = one(f)
            for i=1:length(As)
                for a in As[i]
                    lc = leading_coefficient(Gs[i])(a) # make monic (!!!)
                    g = map_coefficients(c->c(a)//lc, Gs[i]) 
                    Dg += a*D(g)//g
                    # Make g = g+Z an element of the field k(t),
                    # otherwise exponentiation with negative numbers would not work.
                    v *= (g+Z)^numerator(m*a)
                end
            end
        end
    end
    p = f - Dg
    if iszero(p)
        if expect_one && m!=1
            # no solution, m not == 1 as expected"
            return no_solution
        end
        return m, v, 1
    end
    if !(isone(denominator(p)))
        # no solution, p=f-Dg not a polynomial
        return no_solution
    end
    if !(degree(numerator(p))<max(1,degree(D)))
        return no_solution
    end
    H = MonomialDerivative(D)
    if isprimitive(D)
        p0 = constant_coefficient(numerator(p))
        n, u, ρ = InFieldLogarithmicDerivativeOfRadical(p0, BaseDerivation(D))
        if ρ<=0
            return no_solution
        end
        if expect_one && n!=1
            # no solution, n not == 1 as expected
            return no_solution
        end
        N = lcm(n, m)
        # Make u = u + Z an element of the field k(t),
        # otherwise exponentiation with negative numbers would not work.
        U = v^div(N, m)*(u+Z)^div(N, n)
        return N, U, 1
    elseif ishyperexponential(D)        
        p0 = constant_coefficient(numerator(p))
        w = coeff(H, 1)
        n, e, u, ρ = ParametricLogarithmicDerivative(p0, w, BaseDerivation(D))  
        if ρ<=0
            return no_solution
        end
        if expect_one && n!=1
            # no solution, m not == 1 as expected"
            return no_solution
        end
        N = lcm(n, m)
        t = gen(parent(numerator(f)))
        # Make u = u + Z, t = t + Z elements of the field k(t),
        # otherwise exponentiation with negative numbers would not work.
        U = v^div(N, m)*(u+Z)^div(N, n)*(t+Z)^div(e*N, n)
        return N, U, 1
    elseif ishypertangent(D)        
        throw(NotImplemented("InFieldLogarithmicDerivativeOfRadical: hypertangent case"))        
    else
        throw(NotImplemented("InFieldLogarithmicDerivativeOfRadical: monomial derivative $H"))        
    end
end

