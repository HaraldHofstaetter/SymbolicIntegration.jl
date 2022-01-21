# This file contains algorithms needed for the integratiorn of 
# transcendental functions from chapter 5 of the book
#
#    Manuel Bronstein, Symbolic Integration I: Transcendental Functions,
#    2nd ed., Springer 2005. 
#


using Logging


function HermiteReduce(f::FracElem{P}, D::Derivation) where {T<:FieldElement, P<:PolyElem{T}}
    # See Bronstein's book, Section 5.3, p. 139
    iscompatible(f, D) || error("rational function f must be in the domain of derivation D")
    fp, fs, fn = CanonicalRepresentation(f, D)
    a = numerator(f)
    d = denominator(f)
    ds = Squarefree(d)
    g = zero(f)
    for i=2:length(ds)
        if degree(ds[i])>0
            v = ds[i]
            u = divexact(d, v^i)
            for j=i-1:-1:1
                b, c = gcdx(u*D(v), v, -1//j*a)
                g += b//v^j
                a = -j*c-u*D(b)
            end
            d = u*v
        end
    end
    q, r = divrem(a, d)
    g, r//d, q+fp+fs
end

function PolynomialReduce(p::P, D::Derivation) where {T<:FieldElement, P<:PolyElem{T}}
    # See Bronstein's book, Section 5.4, p. 141
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
    q, r = PolynomialReduce(p-D(q0), D)
    q0+q, r
end

function ResidueReduce(f::F, D::Derivation; symbol=:α) where 
    {T<:RingElement, P<:PolyElem{T}, F<:FracElem{P}}
    # See Bronstein's book, Section 5.6, p. 151
    iscompatible(f, D) || error("rational function f must be in the domain of derivation D")
    issimple(f, D) || error("rational function f must be simple with respect to derivation D")
    d = denominator(f)
    (p,a) = divrem(numerator(f), d)
    # For SubResultant with respect to t we have to construct the 
    # polynomial ring k[z][t] with z, t in this order (!)
    kz, z = PolynomialRing(base_ring(d), symbol)
    kzt, t = PolynomialRing(kz, var(parent(d)))
    if degree(D(d))<=degree(d)
        r, Rs = SubResultant(d(t), a(t)-z*D(d)(t))
    else
        r, Rs = SubResultant(a(t)-z*D(d)(t), d(t))
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

function IntegratePrimitivePolynomial(p::P, D::Derivation) where 
    {T<:RingElement, P<:PolyElem{T}}
    # See Bronstein's book, Section 5.9, p. 158 
    iscompatible(p, D) || error("rational function p must be in the domain of derivation D")
    isprimitive(D) || error("monomial of derivation D must be primitive")
    if degree(p)<=0
        return zero(p), 1
    end
    a = leading_coefficient(p)
    b, c, β = LimitedIntegrate(a, MonomialDerivative(D), D)
    if β<=0 
        @info "IntegratePrimitivePolynomial: no solution, LimitedIntegrate returned no solution"
        return zero(p, 0)
    end
    m = degree(p)
    q0 = c*t^(m+1)//((m+1) + b*t^m)
    q, β = IntegratePrimitivePolynomial(p-D(q0), D)
    if β<=0 
        @info "IntegratePrimitivePolynomial: no solution, recursive call of itself returned no solution"
    end
    return q+q0, β
end

function IntegrateHyperexponentialPolynomial(p::F, D::Derivation) where 
    {T<:RingElement, P<:PolyElem{T}, F<:FracElem{P}}
    # See Bronstein's book, Section 5.9, p. 162
    iscompatible(p, D) || error("rational function p must be in the domain of derivation D")
    ishyperexponential(D) || error("monomial of derivation D must be hyperexponential")
    @info "p=$p"
    q = zero(p)
    β = 1
    if iszero(p) 
        # Note: with the conventions in Bronstein's book the for loop below would
        # run from i=+infinity to i=-infinity for p=0, i.e., not at all.
        # But it's cleaner to handle the case p=0 separartely.
        return q, β
    end
    t = gen(base_ring(parent(p)))
    w = coeff(MonomialDerivative(D), 1) # Dt/t
    for i=valuation(p, t):-valuation_infinity(p)
        if i!=0
            a = coeff(p, i)
            v, β1 = RischDE(i*w, a, BaseDerivation(D))
            if β1==0
                @info "IntegrateHyperexponentialPolynomial: no solution, RischDE returned no solution"
                β = 0
            else 
                q += v*t^i
            end
        end
    end
    q, β
end

function InFieldDerivative(f::F, D::Derivation) where F<:FieldElement
    # base case f \in constant field, D must be the null derivation
    iscompatible(f, D) || error("field element f must be in the domain of derivation D")
    if iszero(f)
        return one(f), 1
    else
        @info "InFieldDerivative (basecase): no solution, f was nonzero in basecase (where D=Null derivation)"
        return zero(f), 0 
    end
end

function InFieldDerivative(f::F, D::Derivation) where 
    {T<:RingElement, P<:PolyElem{T}, F<:FracElem{P}}
    # See Bronstein's book, Section 5.12, p. 175
    iscompatible(f, D) || error("rational function f must be in the domain of derivation D")
    Z = zero(f)
    g, h, r = HermiteReduce(f, D)
    if !isone(denominator(h))
        @info "InFieldDerivative: no solution, h returned by HermiteReduce was not a polynomial"
        return Z, 0 # no solution
    end
    p = h + r # reduced 
    @assert isreduced(p, D)
    if isprimitive(D)
        # p reduced => polynomial in this case
        p = numerator(p)
        q, β = IntegratePrimitivePolynomial(p, D)
        if β<=0
            @info "InFieldDerivative: no solution, IntegratePrimitivePolynomialial returned no solution"
            return Z, β
        end
        a0 = p-D(q)
        @assert isone(denominator(a0)) && degree(numerator(a0))<=0 # p-D(q) ∈ k
        a = constant_coefficient(numerator(a0))        
        v, c, β = LimitedIntegrate(a, leading_coefficient(D), BaseDerivation(D)) # not yet implemented
        if β<=0
            @info "InFieldDerivative: no solution, LimitedIntegrate returned no solution"
            return Z, β
        end
        return g + q + v + c*H, 1
    else # nonlinear case  # TODO: minor modification mentioned near the top of p.176
        if ishyperexponential(D)
            q, β = IntegrateHyperexponentialPolynomial(p, D)
            if β<=0
                @info "InFieldDerivative: no solution, IntegrateHyperexponentialPolynomialial returned no solution"
                return Z, β
            end
        else
            @error "InFieldLogarithmicDerivativeOfRadical: something not implemented for given monomial"
            return Z, -1
        end
        a0 = p-D(q)
        @assert isone(denominator(a0)) && degree(numerator(a0))<=0 # p-D(q) ∈ k
        a = constant_coefficient(numerator(a0))
        v, β = InFieldDerivative(a, BaseDerivation(D))
        if β<=0
            @info "InFieldDerivative: no solution, recurisve call of itself returned no solution"
            return Z, β
        end
        return g + q + v, 1
    end
end

function InFieldLogarithmicDerivative(f::F, D::Derivation) where F<:FieldElement 
    n, v, β = InFieldLogarithmicDerivativeOfRadical(f, D, expect_one=true)
    @assert β<=0 || n==1
    v, β
end

function InFieldLogarithmicDerivativeOfRadical(f::F, D::Derivation; expect_one::Bool=false) where F<:FieldElement
    # base case f \in constant field, D must be the null derivation
    iscompatible(f, D) || error("field element f must be in the domain of derivation D")
    if iszero(f)
        return 1, one(f), 1
    else
        @info "InFieldLogarithmicDerivativeOfRadical (basecase): no solution, f was nonzero in basecase (where D=Null derivation)"
        return 0, zero(f), 0 # no solution (n must be !=0)
    end
end

function InFieldLogarithmicDerivativeOfRadical(f::F, D::Derivation; expect_one::Bool=false) where 
    {T<:RingElement, P<:PolyElem{T}, F<:FracElem{P}}
    # See Bronstein's book, Section 5.12, p. 177
    iscompatible(f, D) || error("rational function f must be in the domain of derivation D")
    if iszero(f)
        return 1, one(f), 1
    end
    Z = zero(f)
    if !issimple(f, D)
        @info "InFieldLogarithmicDerivativeOfRadical: no solution,  f was not simple"
        return 0, Z, 0 
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
                @info "InFieldLogarithmicDerivativeOfRadical: no solution, Rothstein-Trager resultant did not have rational coefficients"
                return 0, Z, 0
            end
            Rs1 = [map_coefficients(c->convert(fmpq, rationalize(c)), R) for R in Rs]
            As1 = [roots(R) for R in Rs1]
            if !(all([length(As1[i])==degree(Rs1[i]) for i=1:length(As1)]) &&
                all([all(isrational.(As1[i])) for i=1:length(As1)]) )
                @info "InFieldLogarithmicDerivativeOfRadical: no solution, not all roots of the Rothstein-Trager resultant were rational"
                return 0, Z, 0
            end
            As = [[rationalize_over_Int(a) for a in as] for as in As1]
            if expect_one 
                if !all([all([isone(denominator(a)) for a in as]) for as in As])
                    @info "InFieldLogarithmicDerivativeOfRadical(...,expect_one=1): no solution, not all roots of the Rothstein-Trager resultant were integers"
                    return 0, Z, 0
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
            @info "InFieldLogarithmicDerivativeOfRadical(...,expect_one=1): no solution, m!=1"
            return 0, Z, 0
        end
        return m, v, 1
    end
    if !(isone(denominator(p)))
        @info "InFieldLogarithmicDerivativeOfRadical: no solution, p=f-Dg was not a polynomial"
        return 0, Z, 0
    end
    if !(degree(numerator(p))<max(1,degree(D)))
        @info "InFieldLogarithmicDerivativeOfRadical: no solution, degree(p) was not < max(1,degree(D))"
        return 0, Z, 0
    end
    H = MonomialDerivative(D)
    if isprimitive(D)
        p0 = constant_coefficient(numerator(p))
        n, u, success = InFieldLogarithmicDerivativeOfRadical(p0, BaseDerivation(D))
        if success<=0
            @info "InFieldLogarithmicDerivativeOfRadical: no solution, recursive call of itself returned success=$(success)"
            return 0, Z, success
        end
        if expect_one && n!=1
            @info "InFieldLogarithmicDerivativeOfRadical(...,expect_one=1): no solution, m!=1"
            return 0, Z, 0
        end
        N = lcm(n, m)
        # Make u = u + Z an element of the field k(t),
        # otherwise exponentiation with negative numbers would not work.
        U = v^div(N, m)*(u+Z)^div(N, n)
        return N, U, 1
    elseif ishyperexponential(D)        
        p0 = constant_coefficient(numerator(p))
        w = coeff(H, 1)
        n, e, u, success = ParametricLogarithmicDerivative(p0, w, BaseDerivation(D))  
        if success<=0
            @info "InFieldLogarithmicDerivativeOfRadical: no solution, ParametricLogarithmicDerivative(p0, w, D) 
 with p0=$p0, w=$w returned success=$(success)"
            return 0, Z, success
        end
        if expect_one && n!=1
            @info "InFieldLogarithmicDerivativeOfRadical(...,expect_one=1): no solution, m!=1"
            return 0, Z, 0
        end
        N = lcm(n, m)
        t = gen(parent(numerator(f)))
        # Make u = u + Z, t = t + Z elements of the field k(t),
        # otherwise exponentiation with negative numbers would not work.
        U = v^div(N, m)*(u+Z)^div(N, n)*(t+Z)^div(e*N, n)
        return N, U, 1
    else
        # TODO: hypertangent case 
        @error "InFieldLogarithmicDerivativeOfRadical: something not implemented for given monomial"
        return 0, Z, -1 
    end
end

