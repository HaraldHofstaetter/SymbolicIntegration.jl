using SymbolicUtils
using Logging

export integrate

"""
    TowerOfDifferentialFields(Hs) -> K, gs, D

Construct tower of differential fields.

Given `Hs = [H₁,...,Hₙ]` with `Hᵢ` in `C(x,t₁,...,tₙ)` (i.e., they are fractions
of multivariate polynomials in variables `x, t₁,...,tₙ` over a field `C`) 
such that `Hᵢ` can be represented as a polynomial in `tᵢ` with coefficients  in `C(x, t₁,...,tᵢ₋₁)` (in particular, `Hᵢ` does not depend on `tᵢ₊₁,...,tₙ`),
return a field `K = C(x)(t₁)...(tₙ)` isomorphic to `C(x, t₁,...,tₙ)` and a derivation `D` on `K` such that
`K` is constructed by iteratively adjoining the indeterminates `x`, `t₁`,...,`tₙ`, `C` is the constant field
of `D`, `D` is `d/dx` on `C(x)`, and `D` is iteratively extended from `C(x)(t₁)...(tᵢ₋₁)` to `C(x)(t₁)...(tᵢ)`
such that `tᵢ` is monomial over `C(x)(t₁)...(tᵢ₋₁)` with `D(tᵢ)=Hᵢ=Hᵢ(x, t₁,....,tᵢ)`.
The generators `x` of C(x) over C and `tᵢ` of `C(x)(t₁)...(tᵢ)` over `C(x)(t₁)...(tᵢ₋₁)` are returned
as `gs=[x, t₁,...,tₙ]`. (Note that these generators, although here denoted by the same symbols for simplicity, are isomorphic but not identical to 
the generators `x, t₁,...,tₙ` of `C(x,t₁,...,tₙ)` given implicitely as the variables of the rational functions `Hᵢ`.)

# Example  
```julia
R, (x, t1, t2) = PolynomialRing(QQ, [:x, :t1, :t2])
Z = zero(R)//1 # zero element of the fraction field of R
K, gs, D = TowerOfDifferentialFields([t1//x, (t2^2+1)*x*t1 + Z])
```
(Note: by adding `Z` to a polynomial we explicitely transform it to an element of the fraction field.)
"""
function TowerOfDifferentialFields(Hs::Vector{F})  where 
    {T<:FieldElement, P<:MPolyElem{T}, F<:FracElem{P}}
    n = length(Hs)
    n>0 || error("height extension tower must be >= 1")
    MF = parent(Hs[1])
    MR = base_ring(MF)
    nvars(MR) == n + 1 || error("number of monmials must be number of variables - 1")
    syms = symbols(MR)
    K = base_ring(MR)
    gs = Any[zero(K) for i=1:n+1]    
    Kt, gs[1] = PolynomialRing(K, syms[1])    
    D = BasicDerivation(Kt)
    K = FractionField(Kt)       
    for i=1:n
        Kt, gs[i+1] = PolynomialRing(K, syms[i+1])        
        p = numerator(Hs[i])
        q = denominator(Hs[i])
        maximum(vcat(0, var_index.(vars(p)), var_index.(vars(q)))) <=i+1 ||
            error("Hs[$(i)] may only depend on $(gens(MR)[1:i+1]))")
        H = p(gs...)//q(gs...) 
        isone(denominator(H)) ||
            error("Hs[$(i)] must be a polynomial in $(gens(MR[i+1]))")
        H = numerator(H)
        D = ExtensionDerivation(Kt, D, H)
        K = FractionField(Kt)       
    end
    K, gs, D
end

"""
    transform_mpoly_to_tower(f, gs) -> f1

Transform elements of `C(x,t₁,...,tₙ)` to elements of `C(x)(t₁)...(tₙ)`.

Given `f` in `C(x,t₁,...,tₙ)` and the generators `gs=[x, t₁,...,tₙ]` as returned by 
`TowerOfDifferentialFields`, return the corresponding element `f1` in `C(x)(t₁)...(tₙ)`,

# Example
```
R, (x, t1, t2) = PolynomialRing(QQ, [:x, :t1, :t2])
Z = zero(R)//1 # zero element of the fraction field of R
K, gs, D = TowerOfDifferentialFields([t1//x, (t2^2+1)*x*t1 + Z])
f = (x+t1)//(x+t2)     # element of FractionField(R)
f1 = transform_mpoly_to_tower(f, gs)  # element of K
```
"""
function transform_mpoly_to_tower(f::F, gs::Vector) where 
    {T<:FieldElement, P<:MPolyElem{T}, F<:FracElem{P}}
    numerator(f)(gs...)//denominator(f)(gs...)
end

@syms Root(x::qqbar)

to_symb(t::Number) = t

function to_symb(t::Rational)
    if isone(denominator(t))
        return numerator(t)
    else
        return t
    end
end

to_symb(t::fmpq) = to_symb(Rational(t))

function to_symb(t::qqbar)
    if degree(t)==1 
        return to_symb(fmpq(t))
    end
    kx, _ = PolynomialRing(Nemo.QQ, :x)
    f = minpoly(kx, t)
    if degree(f)==2 && iszero(coeff(f,1))
        y = to_symb(-coeff(f,0)//coeff(f, 2))
        if y>=0
            if t==maximum(conjugates(t))
                return SymbolicUtils.Term(sqrt,y)
            else
                return -SymbolicUtils.Term(sqrt,y)
            end
        else
            if imag(t)==maximum(imag.(conjugates(t)))
                return SymbolicUtils.Term(sqrt,-y)*1im
            else
                return -SymbolicUtils.Term(sqrt,-y)*1im
            end
        end
    elseif degree(f)==2 # coeff(f,1)!=0
        s = coeff(f, 1)//(2*coeff(f,2))
        return to_symb(t + s) - to_symb(s)
    else
        return Root(t)
    end    
end

function height(K::F) where F<:AbstractAlgebra.Field
    0
end

function height(K::F) where
    {T<:FieldElement, P<:PolyElem{T}, F<:FracField{P}}
    height(base_ring(base_ring(K)))+1
end

function height(R::P) where
    {T<:FieldElement, P<:PolyRing{T}}
    height(base_ring(R))+1
end

subst_tower(t::Number, subs::Vector, h::Int=0) = to_symb(t)  

subst_tower(t::fmpq, subs::Vector, h::Int=0) = to_symb(t)

subst_tower(t::qqbar, subs::Vector, h::Int=0) = to_symb(t)

function subst_tower(f::F, vars::Vector, h::Int) where
    {T<:FieldElement, P<:PolyElem{T}, F<:FracElem{P}}
    if isone(denominator(f))
        subst_tower(numerator(f), vars, h)
    else
        subst_tower(numerator(f), vars, h)//subst_tower(denominator(f), vars, h)
    end
end

function subst_tower(p::P, vars::Vector, h::Int) where
    {T<:FieldElement, P<:PolyElem{T}}
    if iszero(p)
        return zero(vars[1])
    end
    c = collect(coefficients(p))        
    sum([subst_tower(c[i], vars, h - 1)*vars[h]^(i-1) for i=1:length(c)])
end

function subst_tower(f::F, vars::Vector) where
    {T<:FieldElement, P<:PolyElem{T}, F<:FracElem{P}}
    h = height(parent(f))
    subst_tower(f, vars, h)
end

function subst_tower(p::P, vars::Vector) where
    {T<:FieldElement, P<:PolyElem{T}}
    h = height(parent(p))
    subst_tower(p, vars, h)
end

function subst_tower(t::IdTerm, subs::Vector)
    subst_tower(t.arg, subs)
end

function subst_tower(t::FunctionTerm, subs::Vector)
    subst_tower(t.coeff, subs)*t.op(subst_tower(t.arg, subs))
end

function subst_tower(ts::Vector{Term}, subs::Vector)
    if isempty(ts)
        return 0
    end
    sum([subst_tower(t, subs) for t in ts])
end


function analyze_expr(f, x::SymbolicUtils.Sym)
    funs = Any[x]
    vars = SymbolicUtils.Sym[x]
    args = Any[x]
    p = analyze_expr(f, funs, vars, args)
    p, funs, vars, args
end

function analyze_expr(f::SymbolicUtils.Sym , funs::Vector, vars::Vector{SymbolicUtils.Sym}, args::Vector)
    if hash(f) != hash(funs[1])
        throw(NotImplementedError(("integrand contains symbol $f not equal to the integration variable $(funs[1])\n@ $(@__FILE__):$(@__LINE__)")))
    end
    return f
end

function analyze_expr(f::Number , funs::Vector, vars::Vector{SymbolicUtils.Sym}, args::Vector)
    # TODO distinguish types of number (rational, real,  complex, etc. )
    return f
end

function analyze_expr(f::Union{SymbolicUtils.Add, SymbolicUtils.Mul, SymbolicUtils.Div}, funs::Vector, vars::Vector{SymbolicUtils.Sym}, args::Vector)
    as = arguments(f)
    ps = [analyze_expr(a, funs, vars, args) for a in as]
    operation(f)(ps...) # apply f
end

function analyze_expr(f::SymbolicUtils.Pow, funs::Vector, vars::Vector{SymbolicUtils.Sym}, args::Vector)
    as = arguments(f)
    p1 = analyze_expr(as[1], funs, vars, args)
    p2 = analyze_expr(as[2], funs, vars, args)
    if isa(p2, Integer)
        return p1^p2
    elseif isa(p2, Number)        
        throw(NotImplementedError(("integrand contains not allowed exponent $p2\n@ $(@__FILE__):$(@__LINE__)")))
    end
    exp(p2*log(p1))    
end

function analyze_expr(f::SymbolicUtils.Term , funs::Vector, vars::Vector{SymbolicUtils.Sym}, args::Vector)    
    op = operation(f)
    a = arguments(f)[1]
    if op == sinh
        f = 1//2*(exp(a) - 1/exp(a))
        return analyze_expr(f, funs, vars, args)
    elseif op == cosh
        f = 1//2*(exp(a) + 1/exp(a))
        return analyze_expr(f, funs, vars, args)
    elseif op == csch # 1/sinh
        f = 2/(exp(a) - 1/exp(a))
        return analyze_expr(f, funs, vars, args)
    elseif op == sech
        f = 2/(exp(a) + 1/exp(a))
        return analyze_expr(f, funs, vars, args)
    elseif op == tanh
        f = (exp(a) - 1/exp(a))/(exp(a) + 1/exp(a))
        return analyze_expr(f, funs, vars, args)
    elseif op == coth
        f = (exp(a) + 1/exp(a))/(exp(a) - 1/exp(a))
        return analyze_expr(f, funs, vars, args)        
    elseif op == sin # transform to half angle format
        f = 2*tan(1//2*a)/(1 + tan(1//2*a)^2)
        return analyze_expr(f, funs, vars, args)
    elseif op == cos
        f = (1 - tan(1//2*a)^2)/(1 + tan(1//2*a)^2)
        return analyze_expr(f, funs, vars, args)
    elseif op == csc # 1/sin
        f = 1//2*(1 + tan(1//2*a)^2)/tan(1//2*a)
        return analyze_expr(f, funs, vars, args)
    elseif op == sec # 1/cos
        f = (1 + tan(1//2*a)^2)/(1 - tan(1//2*a)^2)
        return analyze_expr(f, funs, vars, args)
    elseif op == cot
        f = 1/tan(a)
        return analyze_expr(f, funs, vars, args)
    end
    i = findfirst(x -> hash(x)==hash(f), funs) 
    if i !== nothing
        return vars[i]
    end    
    op in [exp, log, atan, tan] ||        
        throw(NotImplementedError(("integrand contains function $op\n@ $(@__FILE__):$(@__LINE__)")))
    p = analyze_expr(a, funs, vars, args)
    tname = Symbol(:t, length(vars)) 
    t = SymbolicUtils.Sym{Number, Nothing}(tname, nothing)
    push!(funs, f)
    push!(vars, t)
    push!(args, p)
    t
end

function transform_symtree_to_mpoly(f::SymbolicUtils.Sym, vars::Vector, vars_mpoly::Vector)
    i = findfirst(x -> hash(x)==hash(f), vars)
    @assert i!== nothing 
    vars_mpoly[i]
end

transform_symtree_to_mpoly(f::Number, vars::Vector, vars_mpoly::Vector) = f

(F::CalciumQQBarField)(x::Rational) = F(fmpq(x))
Base.promote(x::fmpq, y::MPolyElem{Nemo.qqbar}) = promote(qqbar(x), y)
Base.promote(x::MPolyElem{Nemo.qqbar}, y::fmpq) = promote(x, qqbar(y))

transform_symtree_to_mpoly(f::SymbolicUtils.Add, vars::Vector, vars_mpoly::Vector) =
    sum([transform_symtree_to_mpoly(a, vars, vars_mpoly) for a in arguments(f)])

transform_symtree_to_mpoly(f::SymbolicUtils.Mul, vars::Vector, vars_mpoly::Vector) =
    prod([transform_symtree_to_mpoly(a, vars, vars_mpoly) for a in arguments(f)])

function transform_symtree_to_mpoly(f::SymbolicUtils.Div, vars::Vector, vars_mpoly::Vector) 
    as = arguments(f)
    transform_symtree_to_mpoly(as[1], vars, vars_mpoly)//transform_symtree_to_mpoly(as[2], vars, vars_mpoly)
end

function transform_symtree_to_mpoly(f::SymbolicUtils.Pow, vars::Vector, vars_mpoly::Vector) 
    as = arguments(f)
    @assert isa(as[2], Integer)
    if as[2]>=0
        return transform_symtree_to_mpoly(as[1], vars, vars_mpoly)^as[2]
    else
        return 1//transform_symtree_to_mpoly(as[1], vars, vars_mpoly)^(-as[2])
    end
end



function TowerOfDifferentialFields(terms::Vector{Term})  where 
    {T<:FieldElement, P<:MPolyElem{T}, F<:FracElem{P}}
    n = length(terms)
    MF = parent(terms[1].arg)
    MR = base_ring(MF)
    nvars(MR) == n || error("number of args must be number of variables")
    syms = symbols(MR)
    K = base_ring(MR)
    gs = Any[zero(K) for i=1:n]    
    Kt, gs[1] = PolynomialRing(K, syms[1])    
    D = BasicDerivation(Kt)
    K = FractionField(Kt)       
    for i=2:n
        f = transform_mpoly_to_tower(terms[i].arg, gs) # needs old gs
        Kt, gs[i] = PolynomialRing(K, syms[i])  
        t = gs[i]

        op = terms[i].op
        if op == exp
            H = t*D(f)
        elseif op == log
            H = D(f)//f + 0*t
        elseif op == tan
            H = (t^2+1)*D(f)
        elseif op == atan
            H = D(f)//(f^2+1) + 0*t
        else
            @assert false # never reach this point
        end

        if op==log || op==atan
            u, ρ = InFieldDerivative(constant_coefficient(H), D)
            if ρ>0
                #TODO: For this case there is always a remedy
                throw(NotImplementedError("TowerOfDifferentialFields: D($t) is derviative of element of k for primitive $t over k\n@ $(@__FILE__):$(@__LINE__)"))
            end
        elseif op == exp
            m, u, ρ = InFieldLogarithmicDerivativeOfRadical(coeff(H, 1), D)
            if ρ>0
                #TODO: For this case there is a remedy if m=1 or m=-1
                throw(NotImplementedError("TowerOfDifferentialFields: D($t)/$t is logarithmic derviative of k-radical for hyperexponential $t over k\n@ $(@__FILE__):$(@__LINE__)"))
            end
        elseif op == tan
            #TODO
        else
            @assert false # never reach this point
        end

        D = ExtensionDerivation(Kt, D, H)
        K = FractionField(Kt)       
    end
    K, gs, D
end


@syms ∫(f, x)

struct AlgebraicNumbersInvolved <: Exception end

function integrate(f::SymbolicUtils.Symbolic, x::SymbolicUtils.Sym; useQQBar=false,
    catchNotImplementedError::Bool=true, catchAlgorithmFailedError::Bool=true)
    try
        p, funs, vars, args = analyze_expr(f, x)    
        if useQQBar
            F = Nemo.QQBar
        else
            F = Nemo.QQ
        end
        R, vars_mpoly = PolynomialRing(F, Symbol.(vars))
        Z = zero(R)//one(R)
        args_mpoly = typeof(Z)[transform_symtree_to_mpoly(a, vars, vars_mpoly) + Z for a in args]    
        terms = vcat(IdTerm(args_mpoly[1]), Term[FunctionTerm(operation(funs[i]), 1, args_mpoly[i]) for i=2:length(funs)])
        p_mpoly = transform_symtree_to_mpoly(p, vars, vars_mpoly)           
        _, gs, D = TowerOfDifferentialFields(terms)
        p = transform_mpoly_to_tower(p_mpoly + Z, gs)   
        try 
            g, r, ρ = Integrate(p, D)
            if ρ<=0
                return subst_tower(g, funs) + ∫(subst_tower(r, funs), x)
            else
                return subst_tower(g, funs)
            end
        catch e
            if e isa AlgebraicNumbersInvolved
                # try again now with algebraic numbers enabled
                return integrate(f, x, useQQBar=true, 
                    catchNotImplementedError=catchNotImplementedError, 
                    catchAlgorithmFailedError=catchAlgorithmFailedError)
            end
            rethrow(e)
        end
    catch e
        if e isa NotImplementedError
            if catchNotImplementedError
                @warn "NotImplementedError: $(e.msg)"
                return ∫(f, x)
            end
        elseif e isa AlgorithmFailedError
            if catchAlgorithmFailedError
                @warn "AlgorithmFailedError: $(e.msg)"
                return ∫(f, x)
            end
        end
        rethrow(e)        
    end
end
