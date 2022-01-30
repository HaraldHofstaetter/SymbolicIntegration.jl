using SymbolicUtils


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
    transform_mpoly_to _tower(f, gs) -> f1

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


function analyze_expr(f, x::SymbolicUtils.Sym)
    funs = Any[x]
    vars = SymbolicUtils.Sym[x]
    args = Any[x]
    p = analyze_expr(f, funs, vars, args)
    p, funs, vars, args
end

function analyze_expr(f::SymbolicUtils.Sym , funs::Vector, vars::Vector{SymbolicUtils.Sym}, args::Vector)
    if hash(f) != hash(funs[1])
        error("symbol $f!=$(funs[1]) not allowed")
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
        error("proper rational exponent")
    end
    exp(p2*log(p1))    
end

function analyze_expr(f::SymbolicUtils.Term , funs::Vector, vars::Vector{SymbolicUtils.Sym}, args::Vector)    
    op = operation(f)
    a = arguments(f)[1]
    if op == sin # transform to half angle format
        f = 2*tan(a/2)/(1 + tan(a/2)^2)
        return analyze_expr(f, funs, vars, args)
    elseif op == cos
        f = (1 - tan(a/2)^2)/(1 + tan(a/2)^2)
        return analyze_expr(f, funs, vars, args)
    end
    i = findfirst(x -> hash(x)==hash(f), funs) 
    if i !== nothing
        return vars[i]
    end    
    op in [exp, log, atan, tan] ||
        error("operation $op not implemented")
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

transform_symtree_to_mpoly(f::SymbolicUtils.Add, vars::Vector, vars_mpoly::Vector) =
    sum([transform_symtree_to_mpoly(a, vars, vars_mpoly) for a in arguments(f)])

transform_symtree_to_mpoly(f::SymbolicUtils.Mul, vars::Vector, vars_mpoly::Vector) =
    prod([transform_symtree_to_mpoly(a, vars, vars_mpoly) for a in arguments(f)])

function transform_symtree_to_mpoly(f::SymbolicUtils.Div, vars::Vector, vars_mpoly::Vector) 
    as = arguments(f)
    transform_symtree_to_mpoly(as[1], vars, vars_mpoly)//transform_symtree_to_mpoly(as[2], vars, vars_mpoly::Vector)
end

function transform_symtree_to_mpoly(f::SymbolicUtils.Pow, vars::Vector, vars_mpoly::Vector) 
    as = arguments(f)
    @assert isa(as[2], Integer)
    transform_symtree_to_mpoly(as[1], vars, vars_mpoly)^as[2]
end

function TowerOfDifferentialFields(Hs::Vector{Function}, args::Vector{F})  where 
    {T<:FieldElement, P<:MPolyElem{T}, F<:FracElem{P}}
    n = length(args)
    n == length(Hs) || error("number of Hs must be equal number of args")    
    MF = parent(args[1])
    MR = base_ring(MF)
    nvars(MR) == n || error("number of args must be number of variables")
    syms = symbols(MR)
    K = base_ring(MR)
    gs = Any[zero(K) for i=1:n]    
    Kt, gs[1] = PolynomialRing(K, syms[1])    
    D = BasicDerivation(Kt)
    K = FractionField(Kt)       
    for i=2:n
        f = transform_mpoly_to_tower(args[i], gs) # needs old gs
        Kt, gs[i] = PolynomialRing(K, syms[i])  
        t = gs[i]
        Z = 0*t
        H = Hs[i](t, f, D) + Z     
        D = ExtensionDerivation(Kt, D, H)
        K = FractionField(Kt)       
    end
    K, gs, D
end

function get_H(fun::SymbolicUtils.Sym)
    return  (t, f, D::Derivation) -> 1
end        

function get_H(fun::SymbolicUtils.Term)
    op = operation(fun)
    if op == exp
        return  (t, f, D::Derivation) -> t*D(f)        
    elseif op == log
        return  (t, f, D::Derivation) -> D(f)//f 
    elseif op == tan
        return  (t, f, D::Derivation) -> (t^2+1)*D(f)
    elseif op == atan
        return  (t, f, D::Derivation) -> D(f)//(f^2+1)
    else
        @assert false # never reach this point
    end
end

function TowerOfDifferentialFields(f, x::SymbolicUtils.Sym)
    p, funs, vars, args = analyze_expr(f, x)    
    R, vars_mpoly = PolynomialRing(Nemo.QQ, Symbol.(vars))
    Z = zero(R)//one(R)
    args_mpoly = typeof(Z)[transform_symtree_to_mpoly(a, vars, vars_mpoly) + Z for a in args]    
    p_mpoly = transform_symtree_to_mpoly(p, vars, vars_mpoly)           
    Hs = [get_H(fun) for fun in funs]
    K, gs, D = TowerOfDifferentialFields(Hs, args_mpoly)
    p = transform_mpoly_to_tower(p_mpoly + Z, gs)
    K, gs, D, p
end
