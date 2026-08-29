"""A full-dimensional triangular transport with one quadratic active coupling."""
struct RankOnePolynomialTransport{T<:AbstractFloat,V<:AbstractVector{T}}
    mean::V
    input_direction::V
    output_direction::V
    input_scale::T
    residual_scale::T
    intercept::T
    linear::T
    quadratic::T
end

"""Fit a cheap rank-one quadratic transport from column-oriented warmup samples.

The output direction is the leading covariance direction. The input direction
is the strongest direction of the output-weighted second moment after
projecting out the output. A three-parameter least-squares regression then
models the conditional output displacement.
"""
function fit_rank_one_polynomial_transport(samples::AbstractMatrix{T};
        ridge::T=sqrt(eps(T))) where {T<:AbstractFloat}
    d, n = size(samples)
    d >= 2 || throw(ArgumentError("rank-one transport needs dimension at least two"))
    n >= max(20, 2d) || throw(ArgumentError("insufficient warmup samples"))
    all(isfinite, samples) || throw(ArgumentError("warmup samples must be finite"))
    isfinite(ridge) && ridge > zero(T) || throw(ArgumentError(
        "ridge must be finite and positive"))

    μ = vec(sum(samples; dims=2)) ./ T(n)
    centered = samples .- μ
    covariance = Symmetric(centered * transpose(centered) / T(n))
    covariance_eigen = eigen(covariance)
    output = Vector{T}(covariance_eigen.vectors[:, end])

    output_coordinate = vec(transpose(output) * centered)
    weighted_second = zeros(T, d, d)
    for index in axes(centered, 2)
        x = @view centered[:, index]
        weighted_second .+= output_coordinate[index] .* (x * transpose(x))
    end
    weighted_second ./= T(n)
    projector = Matrix{T}(I, d, d) - output * transpose(output)
    active_moment = Symmetric(projector * weighted_second * projector)
    active_eigen = eigen(active_moment)
    active_index = argmax(abs.(active_eigen.values))
    input = Vector{T}(active_eigen.vectors[:, active_index])
    input .-= output .* dot(output, input)
    input_norm = norm(input)
    input_norm > ridge || throw(ArgumentError(
        "warmup samples do not identify a rank-one nonlinear direction"))
    input ./= input_norm

    active = vec(transpose(input) * centered)
    design = hcat(ones(T, n), active, active .^ 2)
    gram = transpose(design) * design + ridge * Matrix{T}(I, 3, 3)
    coefficients = gram \ (transpose(design) * output_coordinate)
    residual = output_coordinate - design * coefficients
    input_scale = sqrt(sum(abs2, active) / T(n))
    residual_scale = sqrt(sum(abs2, residual) / T(n))
    input_scale > ridge || throw(ArgumentError("degenerate active scale"))
    residual_scale > ridge || throw(ArgumentError("degenerate residual scale"))

    RankOnePolynomialTransport(Vector{T}(μ), input, output, input_scale,
        residual_scale, coefficients[1], coefficients[2], coefficients[3])
end

@inline function _rank_one_polynomial(map::RankOnePolynomialTransport, active)
    map.intercept + map.linear * active + map.quadratic * active^2
end

@inline function _rank_one_polynomial_derivative(
        map::RankOnePolynomialTransport, active)
    map.linear + 2map.quadratic * active
end

function transport_forward(map::RankOnePolynomialTransport{T},
        latent::AbstractVector{T}) where {T}
    length(latent) == length(map.mean) || throw(DimensionMismatch("transport state"))
    latent_input = dot(map.input_direction, latent)
    latent_output = dot(map.output_direction, latent)
    complement = latent - map.input_direction .* latent_input -
        map.output_direction .* latent_output
    active = map.input_scale * latent_input
    output = _rank_one_polynomial(map, active) +
        map.residual_scale * latent_output
    map.mean + complement + map.input_direction .* active +
        map.output_direction .* output
end

function transport_inverse(map::RankOnePolynomialTransport{T},
        position::AbstractVector{T}) where {T}
    length(position) == length(map.mean) || throw(DimensionMismatch("transport state"))
    centered = position - map.mean
    active = dot(map.input_direction, centered)
    output = dot(map.output_direction, centered)
    complement = centered - map.input_direction .* active -
        map.output_direction .* output
    latent_input = active / map.input_scale
    latent_output = (output - _rank_one_polynomial(map, active)) /
        map.residual_scale
    complement + map.input_direction .* latent_input +
        map.output_direction .* latent_output
end

function transport_pullback(map::RankOnePolynomialTransport{T},
        latent::AbstractVector{T}, value::AbstractVector{T}) where {T}
    length(latent) == length(value) == length(map.mean) ||
        throw(DimensionMismatch("transport pullback"))
    latent_input = dot(map.input_direction, latent)
    active = map.input_scale * latent_input
    input_value = dot(map.input_direction, value)
    output_value = dot(map.output_direction, value)
    complement = value - map.input_direction .* input_value -
        map.output_direction .* output_value
    complement + map.input_direction .* (map.input_scale *
        (input_value + _rank_one_polynomial_derivative(map, active) * output_value)) +
        map.output_direction .* (map.residual_scale * output_value)
end

transport_logabsdetjac(map::RankOnePolynomialTransport, latent) =
    log(map.input_scale) + log(map.residual_scale)

transport_grad_logabsdetjac(map::RankOnePolynomialTransport{T}, latent) where {T} =
    zeros(T, length(map.mean))
