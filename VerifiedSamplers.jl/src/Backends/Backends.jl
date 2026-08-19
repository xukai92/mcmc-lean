"""Backend capabilities and execution-evidence declarations.

Capabilities answer whether an operation can run. Evidence classes answer how
strongly that backend is connected to the verified Reference semantics. They
are intentionally separate: availability never implies verification.
"""
module Backends

using Random

export EvidenceKind, ExecutionClass, BackendCapabilities, BackendDescriptor,
    REFERENCE_BACKEND, OPTIMIZED_BACKEND, PARALLEL_CPU_BACKEND,
    HOST_BATCH_BACKEND, BROADCAST_ACCELERATOR_BACKEND,
    BROADCAST_ACCELERATOR, backend_registry,
    supports, require_capability,
    AbstractBatchBackend, HostBatchBackend, AcceleratorBatchBackend,
    BroadcastAcceleratorBackend,
    descriptor, supported_operations, supports_operation, step_batch,
    gaussian_rwmh_batch, run_chains

@enum EvidenceKind begin
    Proved
    GeneratedCheckable
    Tested
    DocumentedBoundary
end

@enum ExecutionClass begin
    ReferenceInterpreted
    VerifiedTransformed
    IndependentOptimized
    ParallelExecutor
    AcceleratorAdapter
end

"""Execution features explicitly supported by a backend."""
struct BackendCapabilities
    scalar::Bool
    vector::Bool
    deterministic_trace::Bool
    independent_chains::Bool
    within_chain_parallelism::Bool
    accelerator::Bool
end

"""One maintained backend and the evidence attached to its implementation."""
struct BackendDescriptor
    name::Symbol
    execution::ExecutionClass
    evidence::EvidenceKind
    capabilities::BackendCapabilities
    note::String
end

const REFERENCE_BACKEND = BackendDescriptor(:reference, ReferenceInterpreted,
    Tested,
    BackendCapabilities(true, true, true, false, false, false),
    "Julia interpreter for the canonical Lean-emitted artifact")

const OPTIMIZED_BACKEND = BackendDescriptor(:optimized, IndependentOptimized,
    Tested,
    BackendCapabilities(true, true, true, false, false, false),
    "independent Julia implementation checked by replay and statistical tests")

const PARALLEL_CPU_BACKEND = BackendDescriptor(:parallel_cpu,
    ParallelExecutor, Tested,
    BackendCapabilities(true, true, true, true, false, false),
    "deterministic independent-chain scheduling over Julia threads")

const HOST_BATCH_BACKEND = BackendDescriptor(:host_batch,
    ParallelExecutor, Tested,
    BackendCapabilities(true, true, true, true, false, false),
    "backend-neutral batched-transition reference on ordinary Julia arrays")

const BROADCAST_ACCELERATOR_BACKEND = BackendDescriptor(
    :broadcast_accelerator, AcceleratorAdapter, Tested,
    BackendCapabilities(true, false, true, true, false, true),
    "accelerator-ready explicit-event Gaussian RWMH broadcast; host conformance tested")

"""The maintained execution backends. Planned backends are not advertised."""
backend_registry() =
    (REFERENCE_BACKEND, OPTIMIZED_BACKEND, PARALLEL_CPU_BACKEND,
        HOST_BATCH_BACKEND, BROADCAST_ACCELERATOR_BACKEND)

function supports(capabilities::BackendCapabilities, capability::Symbol)
    capability in fieldnames(BackendCapabilities) || return false
    getfield(capabilities, capability)
end

supports(backend::BackendDescriptor, capability::Symbol) =
    supports(backend.capabilities, capability)

"""Fail closed when a backend does not advertise the requested capability."""
function require_capability(backend::BackendDescriptor, capability::Symbol)
    supports(backend, capability) || throw(ArgumentError(
        "backend $(backend.name) does not support capability $capability"))
    backend
end

abstract type AbstractBatchBackend end

"""Maintained host implementation of the batched-transition protocol."""
struct HostBatchBackend <: AbstractBatchBackend
    operations::Set{Symbol}
end

HostBatchBackend() = HostBatchBackend(
    Set([:scalar_transition, :vector_transition]))
HostBatchBackend(operations::Union{Tuple,AbstractVector}) =
    HostBatchBackend(Set(Symbol.(operations)))

"""Maintained explicit-event broadcast backend for scoped accelerator use."""
struct BroadcastAcceleratorBackend <: AbstractBatchBackend
    operations::Set{Symbol}
end

const BROADCAST_ACCELERATOR = BroadcastAcceleratorBackend(
    Set([:gaussian_rwmh]))

"""Adapter supplied by an accelerator package or package extension.

The launcher owns device transfer, device RNG/reduction behavior, and result
materialization. Registering an adapter grants no numerical assurance: its
descriptor and operation set remain explicit and conformance must be tested.
"""
struct AcceleratorBatchBackend{F} <: AbstractBatchBackend
    backend::BackendDescriptor
    operations::Set{Symbol}
    launch::F
    function AcceleratorBatchBackend(name::Symbol, operations, launch;
            evidence::EvidenceKind=DocumentedBoundary,
            note::AbstractString="")
        backend = BackendDescriptor(name, AcceleratorAdapter, evidence,
            BackendCapabilities(true, true, false, true, false, true),
            isempty(note) ? "external accelerator batch adapter" : String(note))
        new{typeof(launch)}(backend, Set(Symbol.(operations)), launch)
    end
end

descriptor(::HostBatchBackend) = HOST_BATCH_BACKEND
descriptor(::BroadcastAcceleratorBackend) = BROADCAST_ACCELERATOR_BACKEND
descriptor(backend::AcceleratorBatchBackend) = backend.backend
supported_operations(backend::AbstractBatchBackend) = copy(backend.operations)
supports_operation(backend::AbstractBatchBackend, operation::Symbol) =
    operation in backend.operations

function require_operation(backend::AbstractBatchBackend, operation::Symbol)
    supports_operation(backend, operation) || throw(ArgumentError(
        "backend $(descriptor(backend).name) does not support operation $operation"))
end

function validate_batch(seeds, states)
    isempty(seeds) && throw(ArgumentError("a transition batch cannot be empty"))
    length(seeds) == length(states) || throw(DimensionMismatch(
        "one explicit seed is required for every initial state"))
end

"""Execute independent transitions with explicit per-state seeds."""
function step_batch(backend::HostBatchBackend, operation::Symbol,
        seeds::AbstractVector{<:Integer}, states, transition)
    require_operation(backend, operation)
    validate_batch(seeds, states)
    [transition(MersenneTwister(seed), state)
        for (seed, state) in zip(seeds, states)]
end

function step_batch(backend::AcceleratorBatchBackend, operation::Symbol,
        seeds::AbstractVector{<:Integer}, states, transition)
    require_capability(descriptor(backend), :accelerator)
    require_operation(backend, operation)
    validate_batch(seeds, states)
    backend.launch(operation, collect(seeds), states, transition)
end

"""Batched Gaussian-RWMH transition over any broadcast-compatible arrays.

Random events are explicit inputs, so an accelerator adapter need not silently
substitute a device RNG convention. The maintained conformance test runs this
operation on host arrays against scalar Reference replay. Device compilation,
transfer, and arithmetic behavior belong to the selected array backend.
"""
function gaussian_rwmh_batch(backend::BroadcastAcceleratorBackend,
        current, noise, uniform, logdensity, scale::Real)
    require_operation(backend, :gaussian_rwmh)
    axes(current) == axes(noise) == axes(uniform) || throw(DimensionMismatch(
        "current states, Gaussian noises, and uniforms must align"))
    isfinite(scale) && scale > 0 || throw(ArgumentError(
        "proposal scale must be finite and positive"))
    all(isfinite, uniform) && all(value -> 0 <= value < 1, uniform) ||
        throw(ArgumentError("uniform events must lie in [0,1)"))
    proposed = @. current + scale * noise
    current_logdensity = logdensity.(current)
    proposed_logdensity = logdensity.(proposed)
    threshold = @. exp(min(zero(eltype(proposed_logdensity)),
        proposed_logdensity - current_logdensity))
    ifelse.(uniform .< threshold, proposed, current)
end

gaussian_rwmh_batch(current, noise, uniform, logdensity, scale::Real) =
    gaussian_rwmh_batch(BROADCAST_ACCELERATOR, current, noise, uniform,
        logdensity, scale)

"""Run independent chains from explicit seeds in stable input order.

`run_chain(rng, index)` owns all mutable state for one chain. Parallel and
sequential executions therefore receive identical RNG streams and must return
the same ordered results when the callback itself is deterministic.
"""
function run_chains(run_chain, seeds::AbstractVector{<:Integer};
        backend::BackendDescriptor=PARALLEL_CPU_BACKEND)
    isempty(seeds) && throw(ArgumentError("at least one chain seed is required"))
    require_capability(backend, :independent_chains)
    tasks = map(enumerate(seeds)) do (index, seed)
        Threads.@spawn run_chain(MersenneTwister(seed), index)
    end
    fetch.(tasks)
end

run_chains(seeds::AbstractVector{<:Integer}, run_chain; kwargs...) =
    run_chains(run_chain, seeds; kwargs...)

end
