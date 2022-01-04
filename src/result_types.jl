using AbstractAlgebra

abstract type Term end

struct IdTerm{T<:RingElement} <: Term
    arg::Union{PolyElem{T}, FracElem{<:PolyElem{T}}}
end

struct LogTerm{T<:RingElement} <: Term
    coeff
    arg::Union{PolyElem{T}, FracElem{<:PolyElem{T}}}
end

struct AtanTerm{T<:RingElement} <: Term
    coeff
    arg::Union{PolyElem{T}, FracElem{<:PolyElem{T}}}
end

function show_function_term(io::IO, coeff, fun::String, arg)
    if iszero(coeff)
        print("0")
        return
    end
    if iszero(coeff+one(coeff))
        print(io, "-")
    elseif !isone(coeff)
        s = string(coeff)
        if findnext("+", s, 2)!=nothing || findnext("-", s, 2)!=nothing        
            print(io, "(", s, ")")
        else
            print(io, s)
        end
        print(io,*)
    end
    print(io, fun, "(")
    show(io, arg)
    print(io, ")")
end

Base.show(io::IO, t::IdTerm) = show(io, t.arg)
Base.show(io::IO, t::LogTerm) = show_function_term(io, t.coeff, "log", t.arg)
Base.show(io::IO, t::AtanTerm) = show_function_term(io, t.coeff, "atan", t.arg)


