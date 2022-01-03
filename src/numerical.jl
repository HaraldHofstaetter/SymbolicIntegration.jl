using LinearAlgebra

struct NumericalPolynomial{T<:Number}
    coeffs::Vector{T}
    var::String
end


function NumericalPolynomial(f::PolyElem{T}; var::String="") where T<: FieldElement 
    if isempty(var)
        var = string(symbols(parent(f))[1])
    end
    NumericalPolynomial(BigFloat.(collect(coefficients(f))), var)
end

(f::NumericalPolynomial)(x) = evalpoly(x, f.coeffs)

using Printf

myiszero(x, eps) = abs(x)<eps
myisone(x, eps) = abs(x-1)<eps

function myprintnumber(io::IO, x::T, isfactor::Bool, printplus::Bool) where T<:Real
    if x<0
        print(io, "-")
    elseif printplus
        print(io, "+")
    end
    @printf(io, "%g", abs(x))
end

function myprintnumber(io::IO, x::T, isfactor::Bool, printplus::Bool) where T<:Complex
    if myiszero(x, 1e-13)
        if printplus
            print(io, "+")
        end
        print(io, "0")
        return
    end
    a, b = real(x), imag(x)
    if myiszero(b, 1e-13)
        if a<0
            print(io, "-")
        elseif printplus
            print(io, "+")
        end
        @printf(io, "%g", abs(a))
        return
    end
    if myiszero(a, 1e-13)
        if b<0
            print(io, "-")
        elseif printplus
            print(io, "+")
        end
        @printf(io, "%gim", abs(b))
        return
    end
    if isfactor
        if printplus
            print(io, "+")
        end
        print(io, "(")
    end
    @printf(io, "%g", a)
    if b<0
        print(io, "-")
    else
        print(io, "+")
    end
    @printf(io, "%gim", abs(b))
    if isfactor
        print(io, ")")
    end
end

function Base.show(io::IO, f::NumericalPolynomial) 
    n = length(f.coeffs)
    first = true
    for i=n-1:-1:0
        c = f.coeffs[i+1]
        if !myiszero(c, 1e-13)
            if !myisone(c, 1e-13) || i==0
                myprintnumber(io, c, i>0, !first)
                if i>0
                    print(io, "*")
                end
            elseif !first
                print(io, "+")
            end
            if i>0
                print(io, f.var)
                if i>1
                    print(io, "^", i)
                end
            end
        end
        if first
            first = false
        end
    end
end

function Base.show(io::IO, t::FunctionTerm{T}) where T<:Number
    if myiszero(t.coeff, 1e-13)
        print(io, 0)
        return
    end
    if !myisone(t.coeff, 1e-13)
        myprintnumber(io, t.coeff, true, false)
        print(io, "*")
    end
    print(io, t.fun, "(")
    show(io, t.arg)
    print(io, ")")
end

function improve_zero(z0::S, f::NumericalPolynomial{T}, fd::NumericalPolynomial{T}; tol::Float64=-1.0) where {S<:Real, T<:Real}
    if tol<=0
        tol = Float64(1000*eps(T))
    end
    z = T(z0)
    res = f(z)
    k = 0
    while abs(res) > tol
        if k>100
            println(stderr, "WARNING: improve_zero did not converge after 100 steps, res=$(Float64(abs(res))), tol=$tol")
            break
        end
        z -= res/fd(z)
        res = f(z)
        k+=1
    end
    z
end

function improve_zero(z0::S, f::NumericalPolynomial{T}, fd::NumericalPolynomial{T}; tol::Float64=-1.0) where {S<:Complex, T<:Real}
    if tol<=0
        tol = Float64(1000*eps(T))
    end
    z = Complex{T}(z0)
    res = f(z)
    k = 0
    while abs(res) > tol
        if k>100
            println(stderr, "WARNING: improve_zero did not converge after 100 steps, res=$(Float64(abs(res))), tol=$tol")
            break
        end
        z -= res/fd(z)
        res = f(z)
        k+=1
    end
    z
end

function NumericalZeros(f::PolyElem{T}; tol::Float64=-1.0) where T <: FieldElement
    cs = collect(coefficients(f))
    d = length(cs)-1
    comp = diagm(-1 => ones(d-1)) # companion matrix
    comp[1,:] = reverse(Float64.(-cs[1:d] ./ cs[d+1]))
    zs = eigvals(comp)
    f10 = divexact(f, gcd(f, derivative(f))) # f10 = squarefree kernel of f
    f1  = NumericalPolynomial(f10)
    f1d = NumericalPolynomial(derivative(f10))
    [improve_zero(z, f1, f1d, tol=tol) for z in zs]
end


function NumericalEval(t::SumOfLogTerms; real_output::Bool=true, tol::Float64=-1.0)
    var = string(symbols(parent(t.S))[1])
    as = NumericalZeros(t.R, tol=tol)
    if !isa(as, Vector{<:Complex})
        return [FunctionTerm("log", a, NumericalPolynomial(BigFloat[c(a) 
                    for c in coefficients(t.S)], var)) for a in as]
    end
    if !real_output
        return [FunctionTerm("log", a, NumericalPolynomial(Complex{BigFloat}[NumericalPolynomial(c)(a) 
                    for c in coefficients(t.S)], var)) for a in as]
    end
    r = LogToReal(t)
    out = FunctionTerm[]
    for a in as
        u, v = real(a), imag(a)
        if iszero(v)
            push!(out, FunctionTerm("log", u,
            NumericalPolynomial(BigFloat[c(u) for c in coefficients(r.S)], var)))
        elseif v>0
            if !iszero(u)
                push!(out, FunctionTerm("log", u,
                NumericalPolynomial(BigFloat[numerator(c)(u, v)/denominator(c)(u, v) for c in coefficients(r.LT)], var)))
            end
            for AT in r.ATs
                push!(out, FunctionTerm("atan", AT.coeff*v, 
                NumericalPolynomial(BigFloat[numerator(c)(u, v)/denominator(c)(u, v) for c in coefficients(AT.arg)], var)))
            end
        end
    end
    out
end

function integrate0(f::FracElem{P}; real_output::Bool=true, tol::Float64=-1.0) where {T<:FieldElement, P<:PolyElem{T}}
    h = IntegrateRationalFunction(f)
    out = Any[]
    if !iszero(h[1])
        push!(out, h[1])
    end
    if !iszero(h[2])
        push!(out, h[2])
    end
    for i=3:length(h)
        push!(out, NumericalEval(h[i], real_output=real_output, tol=tol)...)
    end
    out    
end

