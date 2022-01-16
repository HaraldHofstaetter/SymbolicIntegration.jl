# This file contains algorithms needed for the solution of 
# the parametric Risch differential equation from chapter 7 of the book
#
#    Manuel Bronstein, Symbolic Integration I: Transcendental Functions,
#    2nd ed., Springer 2005. 
#


using Logging


function ParamRdeNormalDenominator(f::F, gs::Vector{F}, D::Derivation) where 
    {P<:PolyElem, F<:FracElem{P}}
    # See Bronstein's book, Section 7.1, p. 219
    iscompatible(f, D) && all(iscompatible(g, D) for g in gs) || 
        error("rational functions f and g_i must be in the domain of derivation D")
    # Note: f must be weakly normalized which we do not check. It is recommended
    # to use this function only for rational functions f which were computed by WeakNormalizer. 
    (dn, ds) = SplitFactor(denominator(f), D)
    (en, es) = SplitFactor(lcm([denominator(g) for g in gs]), D)
    p = gcd(dn, en)
    h = divexact(gcd(en, derivative(en)), gcd(p, derivative(p)))
    dnh2 = dn*h^2
    dn*h, dn*h*f-dn*D(h), [dnh2*g for g in gs], h, 1
end

function ParamRdeSpecialDenomExp(a::P, b::F, gs::Vector{F}, D::Derivation) where
    {P<:PolyElem, F<:FracElem{P}}
    # See Bronstein's book, Section 7.1, p. 221 
    ishyperexponential(D) ||
        error("monomial of derivation D must be hyperexponential")
    iscompatible(a, D) && iscompatible(b, D) && all([iscompatible(g, D) for g in gs]) || 
        error("polynomial a and rational functions b and g_i must be in the domain of derivation D")
    isreduced(b, D) || 
        error("rational function b must be reduced with respect to derivation D")
    t = gen(parent(a))
    degree(gcd(t, a))==0 || error("gcd(a, t) must be == 1")
    p = t
    nb = valuation(b, p)
    nc = minimum([valuation(g, p) for g in gs])
    n = min(0, nc - min(0, nb))
    if nb==0 
        α = Remainder(-b//a, p)
        w = coeff(MonomialDerivative(D), 1)
        n0, s, z, β = ParametricLogarithmicDerivative(constant_coefficient(α), w, BaseDerivation(D))
        if β<0
            error("ParametricLogarithmicDerivative failed")
        end
        if  β>0 && n0==1 && !iszero(z)
            n = min(n, s)
        end
    end
    N = max(0, -nb)
    p_power_N = p^N
    p_power_N_minus_n = p^(N-n)
    a*p_power_N, (b+n*a*divexact(D(p), p))*p_power_N, [p_power_N_minus_n fot g in gs], p^(-n)
end

function LinearConstraints(a::P, b::P, gs::Vector{F}, D::Derivation) where
    {P<:PolyElem, F<:FracElem{P}}
    # See Bronstein's book, Section 7.1, p. 223
    iscompatible(a, D) && iscompatible(b, D) && all([iscompatible(g, D) for g in gs]) || 
        error("polynomial a and rational functions b and g_i must be in the domain of derivation D")
    d = lcm([denominator(g) for g in gs])
    qrs = [divrem(numerator(d*gs[i]), d)]
    qs = [q for (q, r) in qrs]
    rs = [r for (q, r) in qrs]
    M = [coefficient(r, i) for i=0:N, r in rs]
    return qs, M
end

RowEchelon(A::Matrix{T}) where T<:FieldElement = RowEchelon(A, T[])

function RowEchelon(A::Matrix{T}, u::Vector{T}) where T<:FieldElement
    # based on https://github.com/blegat/RowEchelon.jl/blob/master/src/RowEchelon.jl
    # Note: input arguments A, u are changed on output
    nr, nc = size(A)
    uzero = length(u)==0
    i = j = 1
    while i <= nr && j <= nc        
        p = findfirst(x->!iszero(x), A[i:nr,j])
        if p==nothing
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
    if uzero
        return A
    else
        A, u
    end
end

ConstantSystem(A::Matrix{T}, D::Derivation) where T<:FieldElement =
    ConstantSystem(A, T[], D)

function ConstantSystem(A::Matrix{T}, u::Vector{T}, D::Derivation) where T<:FieldElement
    # See Bronstein's book, Section 7.1, p. 225
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
        if i==nothing
            j += 1
            continue
        end       
        # enlarge A by one row and u by one entry
        A = vcat(A, [zero(A[1,1]) for l=1:1, k=1:n])
        push!(u, zero(A[1,1]))
        Daij = D(A[i,j])
        for k=1:n
            A[m+1, k] =  D(A[i, k])//Daij
        end
        if !uzero
            u[m+1] = D(u[i])//Daij
        end
        for s=1:m
            for k=1:n
                A[s, k] -= A[s,j]*A[m+1, k]
            end
            if !uzero
                u[s] -= A[s,j]*u[m+1]
            end
        end
        j += 1
        m += 1
    end
    B = [constantize(A[i,j], D) for i=1:m, j=1:n]
    if uzero
        return B
    else
        B, u
    end
end

function ParamRdeBoundDegreePrim(a::P, b::P, qs::Vector{P}, D::Derivation) where P<:PolyElem
    # See Bronstein's book, Section 7.1, p. 228
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
    if db==da-1
        α = -leading_coefficient(b)//leading_coefficient(a)
        z, s0, ρ = LimitedIntegrate(α, leading_coefficient(D), BaseDerivative(D)) # not yet implemented
        if ρ>0 && is_rational(s0)
            s = rationalize_over_Int(s0)
            if denominator(s)==1
                n = max(n, numerator(s))
            end
        end
    end
    D0 = BaseDerivative(D)
    if db==da
        α = -leading_coefficient(b)//leading_coefficient(a)
        z, ρ = InFieldDerivative(α)
        if ρ>0 && !iszero(z)
            β = -leading_coefficient(a*D0(z)+b*z)//(z*leading_coefficient(a))
            w, s0, ρ = LimitedIntegrate(β, leading_coefficient(D), D0) # not yet implemented
            if ρ>0 && is_rational(s0)
                m = rationalize_over_Int(s0)
                if denominator(s)==1
                    n = max(n, numerator(s))
                end
            end
        end
    end
    n
end

function ParamRdeBoundDegreeBase(a::P, b::P, qs::Vector{P}) where P<:PolyElem
    # See Bronstein's book, Section 7.1, p. 228
    !iszero(a) || error("polynomial a must be nonzero")
    da = degree(a)
    db = degree(b)
    dc = maximum([degree(q) for q in qs])
    n = max(0, dc - max(db, da - 1))
    if db==da-1
        s0 = -leading_coefficient(b)//leading_coefficient(a)
        if is_rational(s0)
            s = rationalize_over_Int(s0)
            if isone(denominator(s))
                n = max(0, numerator(s), dc - db)
            end
        end
    end
    return n
end

function ParamRdeBoundDegreeExp(a::P, b::P, qs::Vector{P}, D::Derivation) where P<:PolyElem
    # See Bronstein's book, Section 7.1, p. 229
    ishyperexponential(D) ||
        error("monomial of derivation D must be hyperexponential")
    iscompatible(a, D) && iscompatible(b, D) && all([iscompatible(q, D) for q in gs]) || 
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

function ParamRdeBoundDegreeNonLinear(a::P, b::P, qs::Vector{P}, D::Derivation) where P<:PolyElem
    # See Bronstein's book, Section 7.1, p. 231
    isnonlinear(D) ||
        error("monomial of derivation D must be nonlinear")
    iscompatible(a, D) && iscompatible(b, D) && all([iscompatible(q, D) for q in gs]) || 
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
        if is_rational(s0)
            s = rationalize_over_Int(s0)
            if isone(denominator(s))
                n = max(0, numerator(s), dc - db)
            end
        end
    end
    n
end

function ParSPDE(a::P, b::P, qs::Vector{P}, D::Derivation, n::Int) where P<:PolyElem
    # See Bronstein's book, Section 7.1, p. 231
    iscompatible(a, D) && iscompatible(b, D) && all([iscompatible(q, D) for q in gs]) || 
        error("polynomial a and rational functions b and q_i must be in the domain of derivation D")
    degree(a)>0 || error("degree(a) must be > 0")
    degree(gcd(a, b))<=0 || error("gcd(a,b) must be 1")
    rzs = [gcd(b, a, q) for q in qs]
    a, b + D(a), [z-D(r) for (r, z) in rzs], [r for (r, z) in rzs], n-degree(a)
end

function ParamPolyRischDENoCancel1(b::P, qs::Vector{P}, D::Derivation, n::Int) where P<:PolyElem 
    # See Bronstein's book, Section 7.1, p. 234
    # Note: this implementation changes the input parameters qs!
    iscompatible(b, D) && all([iscompatible(q, D) for q in gs]) || 
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
    M = [coeffizient(q, i) for i=0:dc, q in qs]
    A, u = ConstantSystem(M, [zero(bd) for i=0:dc])
    C = constant_field(D)
    neq = dim(A, 1)
    A = vcat(A, [zero(C) for i=1:m, i=1:2*m])
    for i=1:m
        A[i+neq, i] = one(C)
        A[i+neq, m+i] = -one(C)
    end
    hs, A
end

function PolyRischDENoCancel2(b::P,  qs::Vector{P}, D::Derivation, n::Int) where P<:PolyElem 
    # See Bronstein's book, Section 7.1, p. 238
    iscompatible(b, D) && all([iscompatible(q, D) for q in gs]) || 
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
    hs = [zero(b) for i=1:m]
    ss = [zero(λ) for i=1:m]
    while n>=0
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
        M = [coeffizient(q, i) for i=0:dc, q in qs]
        A, u = ConstantSystem(M, [zero(λ) for i=0:dc], D)
        neq = dim(A, 1)
        A = vcat(A, [zero(C) for i=1:m, i=1:2*m])
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
            if all([iszero(D(f)+b0*f) for f in fs])
                dc = -1
            else
                dc = 0
            end
        else
            dc = maximum([degree(q) for q in qs])
        end
        M = [coeffizient(q, i) for i=0:dc, q in qs]
        for j=1:length(f)
            M[1,j+m] = -D0(f[j]) - b0*f[j]
        end
        A, u = ConstantSystem(M, [zero(C) for i=0:dc])
        A = vcat(A, B)
        neq = dim(A, 1)
        A = vcat(A, [zero(C) for i=1:m, i=1:2*m])
        for i=1:m
            A[i+neq, i] = one(C)
            A[i+neq, m+i] = -one(C)
        end
        return vcat(fs .+ zero(b), hs), A
    end
end


function ParamRischDE(f::F, gs::Vector{F}, D::Derivation) where 
    {P<:PolyElem, F<:FracElem{P}}
    iscompatible(f, D) && all(iscompatible(g, D) for g in gs) || 
        error("rational functions f and g_i must be in the domain of derivation D")
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
    f1 = f - D(q)//q
    gs = [q*g for g in gs]
    a, b, gs, h, = ParamdRdeNormalDenominator(f1, gs, D)
    if primitive_case
        b = numerator(b)
        h1 = one(b)
    elseif hyperexponential_case
        d = gcd(a, t)
        if !isone(d)
            a = divexact(a, d)
            b = b//d
            gs = [g//d for g in gs]
        end
        a, b, gs, h1 =  ParamRdeSpecialDenomExp(a, b, gs, D)
    elseif hypertangent_case
        # TODO
        a, b, gs, h1  =  ParamRdeSpecialDenomTan(a, b, gs, D) # not yet implemented
    else
        @assert false # never reach this point
    end
    d = gcd(a, b)
    if !isone(d)
        a = divexact(a, d)
        b = divexact(b, d)
        gs = [q//d for q in gs]
    end
    qs, M = LinearConstraint(a, b, gs, D)
    A, u = ConstantSystem(M, [Z for i=1:dim(M,2)], D)
    #TODO do something with qs (linear combs ...) , see bottom of p.226 
    if primitive_case
        if basic_case
            n = ParamRdeBoundDegreeBase(a, b, qs) 
        else
            n = ParamRdeBoundDegreePrim(a, b, qs, D)
        end
    elseif hyperexponential_case
        n = ParamRdeBoundDegreeExp(a, b, qs, D) 
    elseif hypertangent_case
        n = ParamRdeBoundDegreeNonLinear(a, b, qs, D)
    else
        @assert false # never reach this point
    end
    while true
        a, b, qs, rs, n = ParSPDE(a, b, qs, D, n)
        if degree(a)==0
            break
        end
        d = gcd(a, b)
        if !isone(d)
            a = divexact(a, d)
            b = divexact(b, d)
            gs = [q//d for q in gs]
            qs, M = LinearConstraint(a, b, gs, D)
            A, u = ConstantSystem(M, [Z for i=1:dim(M,2)], D)
            #TODO do something with qs (linear combs ...) , see bottom of p.226 
        end
    end
    b = divexact(b, a)
    qs = [divexact(q, a) for q in qs]
    if !iszero(b) && (basic_case || degree(b)>max(0, δ-1))
        hs, A = ParamPolyRischDENoCancel1(b, qs, D, n)
    elseif (iszero(b2) || degree(b2)<δ-1) && (basic_case || δ>=2)
        fs , hs, A = ParamPolyRischDENoCancel2(b, qs, D, n)
        if success==2
            z1, success = RischDE(b, c, BaseDerivation(D))
            success>=1 || return Z, Z, success
            z = z1 - z
        end
    elseif δ>=2 && degree(b2)==δ-1
    end

 ####################
# to be continued



end
    



