export Derivation, NullDerivation, BasicDerivation, ExtensionDerivation,
   CoefficientLiftingDerivation, TowerOfDifferentialFields,
   BaseDerivation, MonomialDerivative, domain, constant_field,
   isbasic, isprimitive, ishyperexponential, isnonlinear, ishypertangent,
   iscompatible, isnormal, isspecial, issimple, isreduced, is_Sirr1_eq_Sirr


abstract type Derivation end

domain(D::Derivation) = D.domain
iscompatible(p::RingElement, D::Derivation) = parent(p)==domain(D)
iscompatible(f::FracElem, D::Derivation) =
    base_ring(parent(f))==D.domain

is_Sirr1_eq_Sirr(D::Derivation) = true
# For the time being it is assumed that S₁ⁱʳʳ==Sⁱʳʳ for all derivations
# to be considered.
# See Bronstein's book, Theorems 5.1.1, 5.1.2, 5.10.1 .


struct NullDerivation <: Derivation
    domain #::Ring does not work ... :(
end

NullDerivation(domain::FracField{T}) where T<:RingElement = NullDerivation(base_ring(domain))

function (D::NullDerivation)(p::RingElement)
    parent(p)==D.domain || error("p not in domain of D")
    zero(p)
end

function (D::NullDerivation)(f::FracElem{T}) where {T<:RingElement}
    base_ring(parent(f))==D.domain || error("f not in domain of D")
    zero(f)
end

function constant_field(D::NullDerivation) 
    R = D.domain
    if isa(R, AbstractAlgebra.Field)
        return R
    else
        return FractionField(R)
    end
end


Base.show(io::IO, D::NullDerivation) = print(io, "Null derivation D=0 on ", domain(D))



struct BasicDerivation{T<:RingElement} <: Derivation
    domain::PolyRing{T}
end

BasicDerivation(domain::FracField{P}) where P<:PolyElem = BasicDerivation(base_ring(domain))

function (D::BasicDerivation{T})(p::PolyElem{T}) where T<:RingElement 
    iscompatible(p, D) || error("p not in domain of D")
    derivative(p)
end

function (D::BasicDerivation{T})(f::FracElem{P}) where {T<:RingElement, P<:PolyElem{T}}
    iscompatible(f, D) || error("f not in domain of D")
    derivative(f)
end

BaseDerivation(D::BasicDerivation) = NullDerivation(base_ring(D.domain))
MonomialDerivative(D::BasicDerivation) = one(D.domain)
function constant_field(D::BasicDerivation) 
    R = base_ring(D.domain)
    if isa(R, AbstractAlgebra.Field)
        return R
    else
        return FractionField(R)
    end
end

Base.show(io::IO, D::BasicDerivation) = print(io, "Basic derivation D=d/d", gen(domain(D)), " on ", domain(D))


struct ExtensionDerivation{T<:RingElement} <: Derivation
    domain::PolyRing{T}
    D::Derivation
    H::PolyElem{T}
    function ExtensionDerivation(domain::PolyRing{R}, D::Derivation, H::PolyElem{R}) where R<:RingElement
        base_ring(domain)==D.domain || error("base ring of domain must be domain of D")
        new{R}(domain, D, H)
    end

    function ExtensionDerivation(domain::PolyRing{F}, D::Derivation, H::PolyElem{F}) where 
        {R<:RingElement, F<:FracElem{R}}
        base_ring(base_ring(domain))==D.domain || error("base ring of domain must be domain of D")
        new{F}(domain, D, H)
    end
end

function ExtensionDerivation(domain::FracField{P}, D::Derivation, H::P) where {T<:RingElement, P<:PolyElem{T}}
    ExtensionDerivation(base_ring(domain), D, H)
end

function CoefficientLiftingDerivation(domain::PolyRing{T}, D::Derivation) where T<:RingElement
    ExtensionDerivation(domain, D, zero(domain))
end

function CoefficientLiftingDerivation(domain::FracField{T}, D::Derivation) where T<:RingElement
    ExtensionDerivation(base_ring(domain), D, zero(base_ring(domain)))
end

function (D::ExtensionDerivation{T})(p::PolyElem{T}) where T<:RingElement
    iscompatible(p, D) || error("p not in domain of D")
    if iszero(D.H)
        return map_coefficients(c->D.D(c), p)
    else
        return map_coefficients(c->D.D(c), p) + D.H*derivative(p)
    end
end

function (D::ExtensionDerivation{T})(f::FracElem{P}) where {T<:RingElement, P<:PolyElem{T}}
    iscompatible(f, D) || error("f not in domain of D")
    a = numerator(f)
    b = denominator(f)
    if isone(b)
        if iszero(D.H)
            return map_coefficients(c->D.D(c), a) + zero(f)
        else
            return map_coefficients(c->D.D(c), a) + D.H*derivative(a) + zero(f)
        end
    else
        if iszero(D.H)
            da = map_coefficients(c->D.D(c), a) 
            db = map_coefficients(c->D.D(c), b) 
        else
            da = map_coefficients(c->D.D(c), a) + D.H*derivative(a)
            db = map_coefficients(c->D.D(c), b) + D.H*derivative(b)
        end
        return (b*da - a*db)//b^2
    end
end


BaseDerivation(D::ExtensionDerivation) = D.D 
MonomialDerivative(D::ExtensionDerivation) = D.H 
constant_field(D::ExtensionDerivation) = constant_field(D.D)

Base.show(io::IO, D::ExtensionDerivation) = print(io, "Extension by D", 
    gen(domain(D))," = ", MonomialDerivative(D),
    " of ", BaseDerivation(D), " on ", domain(D))


AbstractAlgebra.degree(D::Derivation) = 
    degree(MonomialDerivative(D)) # \delta(t), see Def. 3.4.1
AbstractAlgebra.leading_coefficient(D::Derivation) = 
leading_coefficient(MonomialDerivative(D)) # \lambda(t), see Def. 3.4.1
Base.iszero(D::Derivation) = false
Base.iszero(D::NullDerivation) = true
isbasic(D::Derivation) = false
isbasic(D::BasicDerivation) = true
isbasic(D::ExtensionDerivation) = 
    iszero(BaseDerivation(D)) && isone(MonomialDerivative(D))
isprimitive(D::Derivation) = degree(D)==0 # see Def. 5.1.1 
ishyperexponential(D::Derivation) = # see Def, 5.1.1
    degree(D)==1 && iszero(constant_coefficient(MonomialDerivative(D)))
isnonlinear(D::Derivation) = degree(D)>=2 # see Def. 3.4.1  

function ishypertangent(D::Derivation) 
    # see Def. 5.10.1
    isnonlinear(D) || return false
    t = gen(domain(D))
    q, r = divrem(MonomialDerivative(D), t^2+1)
    iszero(r) && degree(q)<=0
end


isnormal(p::PolyElem, D::Derivation) =
    # see Def. 3.4.2
    iscompatible(p, D) && degree(gcd(p, MonomialDerivative(D)))==0

isspecial(p::PolyElem, D::Derivation) =
    # see Def. 3.4.2
    iscompatible(p, D) && iszero(rem(MonomialDerivative(D),p))

issimple(f::FracElem{P}, D::Derivation) where P<:PolyElem =
    #see Def. 3.5.2.
    iscompatible(f, D) && isnormal(denominator(f), D)

isreduced(f::FracElem{P}, D::Derivation) where P<:PolyElem =
    #see Def. 3.5.2.
    iscompatible(f, D) && isspecial(denominator(f), D)


function isconstant(x::T, D::NullDerivation) where T<:RingElement 
    @assert iscompatible(x, D)
    true
end

function isconstant(x::F, D::NullDerivation) where {P<:PolyElem, F<:FracElem{P}}
    #this version for disambiguation
    @assert iscompatible(x, D)
    true
end
    
function isconstant(x::T, D::Derivation) where T<:RingElement 
    @assert iscompatible(x, D)
    false
end

function isconstant(x::P, D::BasicDerivation) where P<:PolyElem 
    @assert iscompatible(x, D)
    degree(x)<=0
end

function isconstant(x::P, D::ExtensionDerivation) where P<:PolyElem
    @assert iscompatible(x, D)
    if degree(x)>0 
        return false
    else
        return isconstant(constant_coefficient(x), BaseDerivation(D))
    end
end

function isconstant(x::F, D::Derivation) where {P<:PolyElem, F<:FracElem{P}}
    @assert iscompatible(x, D)
    isone(denominator(x)) && isconstant(numerator(x), D) 
end


function constantize(x::T, D::NullDerivation) where T<:RingElement 
    @assert iscompatible(x, D)
    x
end

function constantize(x::F, D::NullDerivation) where {P<:PolyElem, F<:FracElem{P}}
    #this version for disambiguation
    @assert iscompatible(x, D)
    x
end

function constantize(x::T, D::Derivation) where T<:RingElement 
    @assert iscompatible(x, D)
    error("not a constant")
end

function constantize(x::P, D::BasicDerivation) where P<:PolyElem 
    @assert iscompatible(x, D)
    degree(x)<=0 || error("not a constant")
    constant_coefficient(x)
end

function constantize(x::P, D::ExtensionDerivation) where P<:PolyElem
    @assert iscompatible(x, D)
    degree(x)<=0 || error("not a constant")
    constantize(constant_coefficient(x), BaseDerivation(D))
end

function constantize(x::F, D::Derivation) where {P<:PolyElem, F<:FracElem{P}}
    @assert iscompatible(x, D)
    isone(denominator(x)) || error("not a constant")
    constantize(numerator(x), D)
end

function constant_roots(f::PolyElem{T}, D::Derivation; useQQBar::Bool=false) where T<:FieldElement
    @assert iscompatible(f, D)
    p = map_coefficients(c->constantize(c, BaseDerivation(D)), constant_factors(f)) 
    if useQQBar
        return roots(p, QQBar) 
    else
        return roots(p)
    end
end

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
as `gs=[x, t₁,...,tₙ]`. (Note that these returned generators `x, t₁,...,tₙ` are isomorphic but not identical to the variables 
of the rational functions `Hᵢ`.)

# Example  
```julia
R, (x, t1, t2) = PolynomialRing(QQ, [:x, :t1, :t2])
Z = zero(R)//1 # zero element of the fraction field of R
K, (X, T1, T2), D = TowerOfDifferentialFields([t1//x, (t2^2+1)*x*t1 + Z])
```
(Note: by adding `Z` to a polynomial we explicitely transform it to an element of the fraction field.)
"""
function TowerOfDifferentialFields(Hs::Vector{F})  where 
    {T<:FieldElement, P<:MPolyElem{T}, F<:FracElem{P}}
    n = length(Hs)
    n>0 || error("height extension tower must be >= 1")
    MF = parent(Hs[1])
    MR = base_ring(MF)
    nvars(MR) == n + 1 || error("number of monmials must be number of variables + 1")
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
    transform(f, gs) -> f1

Given `f` in `C(x,t₁,...,tₙ)` and the generators `gs=[x, t₁,...,tₙ]` as returned by 
`TowerOfDifferentialFields`, return the corresponding element `f1` in `C(x)(t₁)...(tₙ)`,

# Example
```
R, (x, t1, t2) = PolynomialRing(QQ, [:x, :t1, :t2])
Z = zero(R)//1 # zero element of the fraction field of R
K, gs, D = TowerOfDifferentialFields([t1//x, (t2^2+1)*x*t1 + Z])
f = (x+t1)//(x+t2)     # element of FractionField(R)
f1 = transform(f, gs)  # element of K
```
"""
function transform(f::F, gs::Vector) where 
    {T<:FieldElement, P<:MPolyElem{T}, F<:FracElem{P}}
    numerator(f)(gs...)//denominator(f)(gs...)
end


"""
    SplitFactor(p, D) -> (pₙ, pₛ)

Splitting factorization.
    
Given a field `k`, a derivation `D` on `k[t]` and `p` in `k[t]`, return
`pₙ`, `pₛ` in `k[t]` such that `p=pₙ*pₛ`, `pₛ` is special, and each squarefree 
factor of `pₙ` is normal.
    
See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 3.5, p. 100.
"""
function SplitFactor(p::PolyElem{T}, D::Derivation) where T<:FieldElement
    iscompatible(p, D) || error("polynomial p must be in the domain of derivation D")
    S = divexact(gcd(p, D(p)), gcd(p, derivative(p)))
    if degree(S)==0
        return(p, one(p))
    end
    (qn, qs) = SplitFactor(divexact(p, S), D)
    qn, S*qs
end

"""
    SplitSquarefreeFactor(p, D) -> (Ns, Ss)

Splitting squarefree factorization.
    
Given a field `k`, a derivation `D` on `k[t]` and `p` in `k[t]`, return
`Ns=[N₁,...,Nₘ]`, `Ss=[S₁,...,Sₘ]` with  `Nᵢ`, `Sᵢ` in `k[t]` such that
`p=(N₁*N₂²*...*Nₘᵐ)*(S₁*S₂²*...*Sₘᵐ)` is a splitting factorization of `p`
and the `Nᵢ` and `Sᵢ` are squarefree and coprime.
    
See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 3.5, p. 102.
"""
function SplitSquarefreeFactor(p::PolyElem{T}, D::Derivation) where T<:FieldElement    
    iscompatible(p, D) || error("polynomial p must be in the domain of derivation D")
    ps = Squarefree(p)
    Ss = [gcd(ps[i], D(ps[i])) for i=1:length(ps)]
    Ns = [divexact(ps[i], Ss[i]) for i=1:length(ps)]
    return Ns, Ss
end

"""
CanonicalRepresentation(f, D) -> (fₚ, fₛ, fₙ)

Canonical representation.

Given a field `k`, a derivation `D` on `k[t]` and `f` in `k(t)`, return
fₚ, fₛ, fₙ in `k(t)` such that `f=fₚ+fₛ+fₙ` is the canonical representation
of `f`.
    
See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 3.5, p. 103.
"""
function CanonicalRepresentation(f::FracElem{P}, D::Derivation) where {T<:FieldElement, P<:PolyElem{T}}
    # See Bronstein's book, Section 3.5, p. 103
    iscompatible(f, D) || error("rational function f must be in the domain of derivation D")
    a = numerator(f)
    d = denominator(f)
    q, r = divrem(a, d)
    dn, ds = SplitFactor(d, D)
    b, c = gcdx(dn, ds, r)
    q, b//ds, c//dn
end

