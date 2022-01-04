export integrate

using Nemo

rationalize(x) = x

function rationalize(x::qqbar)
    if degree(x)==1
        return fmpq(x)
    else
        return x
    end
end

function rationalize(f::PolyElem{qqbar})
    if maximum(degree.(coefficients(f)))==1
        return polynomial(Nemo.QQ, fmpq.(coefficients(f)))
    else
        return f
    end
end

function positive_constant_coefficient(f::PolyElem)
    if constant_coefficient(f)<0
        return -f
    else
        return f
    end
end
    

function Eval(t::SumOfLogTerms; real_output::Bool=true)
    var = string(symbols(parent(t.S))[1])
    F = base_ring(t.R)
    as = roots(t.R)
    if length(as)==degree(t.R)    
        return [LogTerm(a, positive_constant_coefficient(
            polynomial(F, [c(a) for c in coefficients(t.S)], var))) for a in as]
    end
    
    as = roots(t.R, QQBar)  
    us = real.(as)
    vs = imag.(as)
    if iszero(vs) || !real_output
        return [LogTerm(a, positive_constant_coefficient(
            polynomial(QQBar, [c(a) for c in coefficients(t.S)], var))) for a in as]
    end
    r = LogToReal(t)
    result = Term[]
    for i = 1:length(as)
        a = as[i]
        u, v = us[i], vs[i]
        if iszero(v)
            push!(result, LogTerm(rationalize(u), rationalize(positive_constant_coefficient(
            polynomial(QQBar, [c(u) for c in coefficients(r.S)], var)))))
        elseif v>0
            if !iszero(u)
                push!(result, LogTerm(rationalize(r.LT.coeff*u), rationalize(positive_constant_coefficient(
                polynomial(QQBar, [numerator(c)(u, v)//denominator(c)(u, v) for c in coefficients(r.LT.arg)], var)))))
            end
            for AT in r.ATs
                push!(result, AtanTerm(rationalize(AT.coeff*v), rationalize(
                polynomial(QQBar, [numerator(c)(u, v)//denominator(c)(u, v) for c in coefficients(AT.arg)], var))))
            end
        end
    end
    result
end


function integrate(f::FracElem{P}; real_output::Bool=true) where {T<:FieldElement, P<:PolyElem{T}}
    h = SymbolicIntegration.IntegrateRationalFunction(f)
    result = Term[]
    if !iszero(h[1].arg)
        push!(result, h[1])
    end
    if !iszero(h[2].arg)
        push!(result, h[2])
    end
    for i=3:length(h)
        push!(result, Eval(h[i], real_output=real_output)...)
    end
    Result(result)
end

