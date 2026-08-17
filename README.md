# verified-samplers

**[Documentation](https://xukai92.github.io/mcmc-lean/)**

`verified-samplers` formalizes Markov chain Monte Carlo algorithms and coupling
arguments in Lean 4 and is developing an auditable Julia reference and runtime
layer. The mathematical development uses mathlib's measure and
`ProbabilityTheory.Kernel` interfaces.

The two paper targets are:

- Xu et al., [“Couplings for Multinomial Hamiltonian Monte Carlo”](https://proceedings.mlr.press/v130/xu21i.html)
  (AISTATS 2021): [coverage audit](docs/xu21-coverage.md) and
  [roadmap](docs/xu21-roadmap.md);
- Xu and Ge, [“Practical Hamiltonian Monte Carlo on Riemannian Manifolds via
  Relativity Theory”](https://proceedings.mlr.press/v235/xu24i.html)
  (ICML 2024): [coverage audit](docs/xu24-coverage.md) and
  [roadmap](docs/xu24-roadmap.md).

The expanded composable-inference target is Ge, Xu, and Ghahramani,
[*Turing: A Language for Flexible Probabilistic Inference*](https://proceedings.mlr.press/v84/ge18b.html):
see its [coverage audit](docs/ge18-coverage.md). Its formal core is composition
of target-preserving full-state operators; systems and empirical claims remain
separately classified. The concrete mixed Boolean/Gaussian PG--GR-HMC client
also has a visibly target-refresh-augmented form with setwise convergence from
every initial probability law; no such convergence is inferred from
stationarity of the unaugmented composition alone.

The algorithms are defined as mathlib kernels rather than assumed through
opaque interfaces. Any corrected, conditional, obstructed, or empirical paper
statement is classified in its corresponding coverage audit.

The [overall project roadmap](docs/project-roadmap.md) integrates these paper
targets with executable work and the broader
[algorithm scope review](docs/algorithm-scope-review.md). Finite Gibbs,
two-temperature tempering, finite pseudo-marginal MH, executable Xu et al.
coupling, and general-state MALA correctness are complete. A bounded-weight
independence-MH minorization, exact regenerative representation, and explicit
`(1 - 1 / M)^n` eventwise convergence bound are also proved. The pre-Xu
foundation also has a finite adaptive-MCMC counterexample: state-dependent
selection can destroy stationarity even when every frozen kernel preserves
the target. A finite-horizon homogeneous Feynman--Kac/SMC expectation theorem
and its time-inhomogeneous finite-sequence extension are also complete. The
finite law is now realized over explicit ancestry and population histories and
feeds an exact pseudo-marginal client whose complete fixed-horizon schedule may
depend on the proposed state. A history-weighted uniformly selected terminal
particle is also proved to have the normalized Feynman--Kac terminal marginal;
stored ancestry now extracts a correctly sized full genealogy with proved
initial/terminal endpoints. Its full path-observable many-to-one law, complete
finite PIMH stationary exactness, and their dependency chain are now proved;
finite PMMH is also proved when the initial law, every potential, and every
transition kernel depend on the parameter at a common finite horizon. Finite
conditional SMC is implemented by a recursive forced-lineage sampler and
proved equal to the exact conditional selected-particle law on positive
supported paths; composing it with terminal-index refresh gives stationary
finite particle Gibbs. Under primitive finite full support and every fixed
`N ≥ 2`, Lean now constructs an explicit forced-lineage minorization
coefficient and geometric total-variation bound; obtaining one sharp
count-uniform aggregate-history coefficient from primitive model constants
remains separate. Lean already identifies the required aggregate exactly as
the conditional expected fraction of terminal indices carrying the proposed
genealogy.
Julia exposes the matching exact-integer finite-HMM
particle-Gibbs runner with Reference/Optimized trace-replay tests. Corrected
Xu--Ge execution is available directly for
constant diagonal metrics and through an explicit certificate-gated
position-dependent interface. The [Phase I release audit](docs/core-release-audit.md)
records the evidence and remaining numerical boundary.
The [project completion status](docs/project-status.md) reconciles the expanded
Lean, Julia, paper, refinement, and optional-breadth workstreams in one matrix.

For the zero-horizon particle-Gibbs specialization, Lean proves the exact
kernel `N⁻¹ I + (1-N⁻¹) Π` and the exact `N⁻ᵏ` total-variation contraction
factor. The Ge et al. layer also includes finite `assume`/`observe` posterior
semantics and a carefully scoped stationary theorem for static candidate
mixtures. Dynamic selection now has a separate certified-tree theorem:
root inclusion plus equality of the completed candidate `Finset` after every
admissible reroot imply reversible and stationary target-weighted selection.
Lean provides an executable checker whose successful result constructs that
proof-bearing tree, and Julia checks the same completed-tree conditions on
runtime candidate rows. Variable-depth stopped doubling trees and canonical
finite-orbit partitions at declared barrier edges instantiate it in both
languages. A particular numerical U-turn/subtree-exclusion detector must still
justify the barriers it supplies; root-dependent first-stop output is not
silently accepted.

The implicit-solver foundation now includes a fixed-step, smooth,
momentum-even nonseparable example `H(q,p) = a q √(1+p²)`. Lean proves the
step-size contraction condition, exact uniqueness, iteration convergence,
measurability, and momentum-flip reversal. Lean now derives bijectivity from
the opposite-step exact solver and proves that a differentiable unit-Jacobian
certificate implies preservation of product phase volume. The generic smooth
test step retains that explicit certificate premise; the bounded
Riemannian-metric solver instantiated below discharges the full Jacobian and
phase-volume endpoint.

The bilinear implicit stress model additionally has a closed-form exact step,
and Lean proves directly in every finite dimension that its reciprocal
position/momentum scalings preserve product phase volume. The repository
contains positive nonconstant scalar and diagonal SoftAbs metric families and
now a canonical smooth factor `1 + ‖q‖²`, with exact factor-volume
compatibility and complete-Hamiltonian measurability. What remains is to
close the contraction and phase-volume analysis for its generalized-leapfrog
solve. Its actual position and momentum derivatives are now connected to the
complete GR Hamiltonian by machine-checked Equations (12) and (13), rather
than supplied as unrelated callbacks.

The exact solver client uses the bounded nonconstant factor `2 + sin(q)` and
compensating potential `log(2 + sin(q))`; its complete GR Hamiltonian reduces
to `√(1 + ((2 + sin q)p)²)`. Lean proves the callbacks are its derivatives,
both implicit maps globally contract when `3|ε|/2 < 1`, and the selected solve
is unique, measurable, approached by the finite loops, and momentum-flip
reversible. Its Banach-selected half-momentum, next-position, and full-step
maps are also continuous as functions of the incoming state. Phase-volume
preservation is now unconditional under the same step bound. Lean factors the
step into four triangular stages, constructs both continuous global Banach
inverses, proves them differentiable by the inverse-function theorem, computes
all four `2×2` determinant factors, cancels them using the checked mixed-
partial identity, transports the result to `PhaseSpace Unit`, and applies the
Haar change-of-variables theorem.

The optional breadth layer now includes an executable finite integer slice
sampler. Lean builds its finite under-the-graph law, alternates exact
conditionals through the collapsed-kernel construction, and proves the
normalized integer-weight target stationary. Julia supplies independent
Reference and Optimized implementations with exhaustive trace tests. The
reversible-jump layer also has a zero-to-two-dimensional planar birth/death
client: the product transport `(u₁,u₂) ↦ (2u₁,2u₂)` carries the checked inverse
determinant factor and yields a complete tagged-target invariance theorem. A
genuinely nonlinear version shears that output to
`(2u₁+8u₂³,2u₂)`; Julia exposes it as `ShearedBirthDeathRJ`, with matching
Reference/Optimized traces, curved-strip checks, moment diagnostics, and
seeded reproducibility tests. The recursively composed three-dimensional
product transport is executable as `SpatialBirthDeathRJ`; its independent
Reference/Optimized implementations, exact trace behavior, coordinate support
and moments, deterministic death, and reproducibility are tested against the
corresponding complete Lean invariance client.

Completed dynamic-trajectory candidate sets now also have a recursive binary
barrier-tree representation. Lean proves their reroot certificate and
target-weighted stationarity; Julia mirrors the aggregation and exposes a
checked target-weighted selector that refuses invalid row families. A total
safe wrapper instead falls back to the identity transition, which Lean also
proves stationary for arbitrary rows. Julia's `CertifiedDynamicHMC` now makes
this branch end-to-end executable: it constructs a randomized-origin leapfrog
orbit, applies the Lean-mirrored all-scales U-turn barriers, and performs stable
Boltzmann selection inside the certified component. Reference/Optimized
selectors have exact trace conformance and the public sampler has seeded
reproducibility coverage. This is a usable conservative dynamic-tree HMC
transition. Julia now also exposes `CheckedFirstStopDynamicHMC`: it builds
root-dependent first-endpoint-U-turn rows on the complete orbit, runs the
Lean-mirrored global reroot check, selects only when that certificate succeeds,
and otherwise performs the proved-safe identity fallback without consuming a
selection draw. This makes the standard-like first-stop boundary directly
executable and diagnostic, but is not yet an equivalence proof for recursive
doubling/subtree-exclusion NUTS. Separately, the finite mathematical layer now
assembles a complete state-dependent completed-tree sampler: it normalizes the
joint target/tree weight on each C.4-admissible root subtype, runs the proved
rooted transition, lifts it to the common phase state, and proves the collapsed
kernel reversible and stationary. Its explicit support hypotheses still have
to be connected to the Julia tree/slice generator. The discrete representative
step is now generated as IR policy `eligible-count-streaming`: Lean proves its
normalized retained-endpoint law, while Julia Reference and Optimized exercise
independent recursive and flattened implementations. Floating-point phase,
slice, and U-turn callback refinement remains explicit. A bounded refinement
layer now certifies slice/divergence comparisons and both endpoint U-turn dot
products whenever their computed values strictly clear supplied absolute-error
bands; Lean proves these local decisions reproduce the complete ideal recursive
flag trace. Vector U-turn bounds are derived coordinatewise through endpoint
subtraction, multiplication, and summation, with the backend separately
bounding the final floating-point reduction. Julia exposes the same composed
certificate and returns `nothing` for an ambiguous decision. Supplying
trustworthy trajectory-generation and slice-energy bounds remains the backend
obligation.
For example:

```julia
sampler = CertifiedDynamicHMC(q -> -sum(abs2, q) / 2, q -> q, 0.12, 8)
draws = sample(MersenneTwister(42), sampler, zeros(2), 1_000)

checked = CheckedFirstStopDynamicHMC(
    q -> -sum(abs2, q) / 2, q -> q, 0.12, 8)
checked_draws = sample(MersenneTwister(42), checked, zeros(2), 1_000)
```

Continuous-time samplers now begin in a separate `Mcmc.PDMP` namespace.
Generator invariance, rate-biased jump-flux balance, and finite reversible-rate
generator balance are formalized, with a symmetric two-velocity switching
client. Bounded finite rates now also produce an exact uniformization kernel;
rate reversibility implies detailed balance and stationarity of that embedded
chain, and uniformizing the velocity client at its switch rate gives the
deterministic flip kernel. The finite branch now also constructs the exact
real-time transition kernel as a Poisson mixture of embedded-chain iterates,
proves its series formula, normalization, zero-time identity, and stationarity,
and instantiates it for velocity switching. Poisson convolution and additive
kernel iteration now prove the Chapman--Kolmogorov law, so these kernels form
an exact stationary finite-state semigroup. The finite event-skeleton layer
also constructs the complete state-vector law after every fixed event count,
proves its terminal marginal is the corresponding kernel iterate, and shows
that Poisson mixing recovers the real-time transition kernel. Finite skeletons
now also carry ordered real event schedules: Lean proves monotone event counts,
right-local constancy, locally constant left limits, endpoint evaluation,
translation compatibility, and the probability status of independent
positive-rate exponential waiting-time products. At every fixed event count,
the state skeleton and exponential waits now have a joint probability measure
with both marginals proved exact. The same Poisson mixture is also constructed
directly for arbitrary mathlib Markov kernels: it is proved Markov, preserves
every invariant probability target, satisfies the zero-time and full
Chapman--Kolmogorov laws, and has an almost-surely finite event count on finite
horizons. Bounded state-dependent pure-jump rates now also
have a general uniformization kernel: each homogeneous clock event takes the
real jump with probability `rate(x)/clockRate` and otherwise self-loops. Lean
proves the embedded and real-time kernels Markov, transports any proved
rate-biased balanced-flux certificate through the embedded chain and
Poissonization to real-time target invariance, and records finite-count
nonexplosion. The flow-driven bounded-rate path construction described below
now supplies the dependent all-count schedule and fixed-horizon transition;
unbounded clocks remain open in general; the concrete one-dimensional Gaussian
Zig-Zag/BPS exception is described below.

The deterministic PDMP branch now has a measurable-semiflow interface. Every
elapsed time yields a deterministic Markov kernel, the exact semigroup law is
proved, and measure-preserving flows give invariant kernels. For Zig-Zag, Lean
checks the one-dimensional two-velocity generator cancellation and derives
mean-zero generator expectation from explicit integrability and weighted
integration-by-parts premises. For BPS, the finite-dimensional reflection is
proved involutive, kinetic-norm preserving, and reversing the normal velocity
component. The process API now also provides full independent velocity
refreshment, proves it Markov, proves it preserves every compatible
position–velocity product target, and proves that it leaves measurable
position events unchanged. The multidimensional bounce algebra also proves
the signed flux identity `λ(v) - λ(Rv) = ⟨v,∇U⟩` and its paired
jump-generator form, isolating the exact pointwise cancellation used after a
reflection-invariant velocity change of variables. Reflection is packaged as
a measurable involutive equivalence, and a measure-level theorem proves that
any velocity law preserved by it turns the integrated bounce term into minus
the normal transport-flux term. The coordinate bounce is identified with an
orthogonal hyperplane reflection and proved to preserve the canonical standard
Gaussian momentum law exactly. Lean now also integrates the full
position-dependent phase-space generator and reduces mean-zero exactly to an
explicit multidimensional spatial integration-by-parts premise; the public
specialization uses the same canonical `standardMomentumMeasure` as HMC, so
clients no longer need to rewrite through the transported Gaussian law. A
second specialization reconstructs directional derivatives from coordinate
partials and proves that the spatial premise follows from one scalar
integration-by-parts identity per coordinate, with all finite-sum integrability
conditions checked explicitly. For compactly supported `C¹` phase observables,
Lean now derives those scalar identities automatically: a measure-preserving
coordinate split reduces the finite Gaussian product to a scalar Gaussian
slice, the one-dimensional Stein theorem applies, and Fubini reconstructs the
phase identity. This is
infinitesimal balance, not process stationarity or convergence. For globally bounded bounce intensities, Lean now
also constructs the exact positive-horizon Poisson/ordered-time thinning
kernel and the practical refresh-then-bounce composition. The latter preserves
a product target conditional on the still-explicit bounce-horizon spatial-flux
proof. These are not yet unbounded-rate BPS stationarity, nonexplosion, or
convergence theorems in general dimension. For finite-dimensional
standard-Gaussian BPS, Lean additionally has the exact affine integrated
hazard and its closed-form partial inverse clock. Bounces are proved to
preserve speed, and linear flight plus Cauchy--Schwarz gives an explicit
finite-flight rate envelope. Turning that envelope and the iid exponential
marks into pathwise finite-horizon nonexplosion is now complete: Lean uses the
finite potential “remaining time × current envelope” to pay every accepted
hazard, while iid exponential prefix sums exceed every finite bound almost
surely. A measurable first-completed-prefix selector now totalizes the exact
endpoint, its fallback is proved null, and the resulting finite-horizon
transition is a Markov kernel. Its exact semigroup law is also proved. The
compact `C¹` generator tests form a checked finite-regular determining core;
target-started scalar weak-forward uniqueness, target stationarity, and
convergence remain open in general dimension. Moreover, convergence from
arbitrary states is false for the bounce-only process in general: Lean proves
that every flight, bounce, finite replay prefix, completed endpoint, and
finite-horizon kernel preserves each antisymmetric coordinate
`qᵢvⱼ-qⱼvᵢ`, with the corresponding level set receiving transition
probability one. Any multidimensional ergodicity milestone must therefore add
an explicit velocity-refresh clock (or restrict its claim to invariant
components); stationarity of the Gaussian mixture remains meaningful without
refreshment.
The completed endpoint is also packaged as a kernel jointly measurable in the
initial state and elapsed time. A generic scheduled-refresh layer integrates
that family over a Poisson count and ordered uniform event times, evolves
between refreshes, and fills the residual horizon. Consequently the concrete
Gaussian BPS client now has both a discrete refresh-before-horizon skeleton
and a genuine homogeneous-Poisson velocity-refresh horizon kernel. Both are
Markov and, conditional on the same remaining scalar weak-forward uniqueness
premise, preserve the canonical product-Gaussian target. A semigroup theorem
for the refreshed family and refreshed ergodicity/convergence remain open.

In one dimension at unit speed,
Lean now proves that Gaussian BPS reflection, rate, and flow coincide with the
Gaussian Zig-Zag representation. Consequently the exact unbounded-rate
horizon kernel and almost-sure nonexplosion theorem transfer to this concrete
BPS client. Its target stationarity is now unconditional: the regenerative
suspension proof described below applies to every nonnegative horizon. Fixed finite event
schedules can now be executed as general-state Markov kernels by alternating
the semiflow with jumps; schedule concatenation and conditional invariance are
proved. Concrete one-dimensional Zig-Zag and finite-dimensional BPS clients
instantiate the linear flows, event kernels, rates, and scheduled execution.
For the standard-Gaussian Zig-Zag client, Lean additionally constructs an
exact genuine-event kernel: it draws a unit exponential hazard, applies the
closed-form inverse integrated clock, flows, and flips velocity. The draw law
is normalized, zero hazard has measure zero, and the integrated-hazard equation
holds almost surely; every fixed genuine-event iterate is Markov. This bypasses
a nonexistent global bound on the Gaussian rate. The exact post-event
signed-position recurrence is also proved, yielding a fresh `sqrt(2E)` lower
bound on every wait after the first. Lean constructs the infinite i.i.d.
hazard product law, uses second Borel--Cantelli to prove infinitely many hazards
exceed one, and concludes that cumulative event time tends to infinity almost
surely. This proves nonexplosion of the exact event sequence. A finite-horizon
transition is now constructed by a measurable first-crossing search over
cumulative event times, followed by exact residual flow. Lean proves the
totalized endpoint jointly measurable, its fallback unused almost surely, and
the resulting general-state kernel Markov. Lean now proves this exact stopped
kernel preserves the Gaussian-position/equal-velocity target at every
nonnegative horizon. The proof constructs an invariant regenerative event
environment, proves its suspension nonexplosive from the divergent
`sqrt(2E)` lower bound, proves the general suspension occupation theorem, and
checks both the Palm decoder law and the pathwise commuting equation with the
actual stopped executor. Signed-coordinate invariance transfers through the
proved involution to the physical Zig-Zag kernel and hence to unit-speed
one-dimensional Gaussian BPS. The semigroup law and convergence remain open.

An independent forward-equation API remains available: it proves invariance of every
finite-time kernel when all measurable-set transported masses are
differentiable on nonnegative time with zero derivative. The Gaussian
Zig-Zag family is connected to this theorem, but this is now an alternate
analytic route rather than a premise of the regenerative stationarity result.
Arbitrary velocity-dependent observables can now enter this analytic layer
through a `GaussianSteinTest` certificate, which records the two required
integrability facts and the Gaussian integration-by-parts identity and yields
mean-zero generator expectation. Lean now also proves the derivative of the
standard-Gaussian density and a general improper integration-by-parts theorem:
ordinary differentiability, weighted integrability, and Gaussian boundary
decay construct the Stein certificate without assuming its identity. Deriving
these side conditions is automatic for compactly supported `C¹` velocity
differences, giving a genuine smooth core with a direct generator-cancellation
theorem. Deriving the setwise forward equation from this certified core remains
open. A new regular-measure bridge now shows that it is enough instead to prove
the forward equation for every compactly supported continuous expectation;
the exact Gaussian Zig-Zag horizon family is connected to this more natural
compact-test certificate, with regularity of its finite transported measures
discharged automatically from the state-space topology.
The weak-forward route is also explicit and domain-correct: a concrete
compactly supported `C¹` Zig-Zag test type includes full phase-generator
integrability, and Lean proves zero generator expectation under the actual
Gaussian×equal-velocity target. A generic theorem shows that weak-forward
uniqueness for this test domain implies exact stationarity. That uniqueness
theorem remains open as an independent well-posedness result, but is no longer
needed for target preservation of the constructed stopped path.
For the measure-determination half, the API now uses the mathematically
minimal regular-measure notion: a general Riesz bridge automatically proves
determination whenever the generator test family represents every compactly
supported continuous function. Target-started Gaussian Zig-Zag and unit-speed
BPS stationarity consumers use a finite-regular specialization matching their
probability marginals. Lean now proves this determination premise: compact
continuous real-line tests are uniformly approximated by compact `C¹` tests,
those tests determine each velocity fiber, and the two fibers reconstruct the
joint measure. Weak-forward solutions now
carry their semantically required probability-law certificate at every time;
on the Gaussian Polish state space this discharges regularity of both candidate
and transported curves automatically. Target-started scalar weak-expectation
uniqueness remains the only premise of this optional weak-forward route.
The normalized Gaussian-position/equal-velocity target is now explicit and
proved a probability measure, and the stopped horizon family is proved exactly
the identity kernel at time zero; these parts no longer remain premises of the
forward-equation certificate.
The Julia inverse clock now uses the Lean-proved cancellation-free quotient on
the positive-signed branch, avoiding `sqrt(a²+2E)-a` underflow for large `a`;
an extreme-scale regression test protects this executable refinement.
An additional constant-rate telegraph client gives a nontrivial flow-driven
stationarity instance. Lean proves that every linear flow and rate-matched
velocity flip preserves equal velocity mass times Lebesgue position, lifts
this through every fixed padded schedule, and concludes stationarity of the
actual arbitrary-count horizon kernel driven by its Poisson count and
continuous ordered event times. Its target is sigma-finite, so this is not a
convergence theorem.
For globally bounded measurable rates, an exact one-candidate thinning kernel
draws an exponential homogeneous-clock wait, flows for that random duration,
and then accepts the real jump with probability `rate/clockRate` or takes a
virtual event. Fixed candidate-count iterates are Markov and compose by
addition. For supplied candidate waits, a fixed-horizon executor consumes only
candidates within the remaining time and fills the residual interval by exact
flow; the associated bounded-clock Poisson count is almost surely finite.
The unconditional executable path kernel for arbitrary candidate counts is
constructed below; unbounded-rate nonexplosion remains open.
The conditional continuous-time ingredient is now present: for every positive
horizon and fixed candidate count, Lean constructs the iid uniform timestamp
product measure and proves it is a probability law. The remaining ordering
obligation is exposed through the certificate described next.
Measurable sorting is proved for every finite real tuple by gluing coordinate
permutations across their measurable monotonicity regions. The resulting
all-count certificate proves monotonicity and preservation up to permutation;
the two-candidate `min/max` network is also checked directly. Every certified
ordering induces probability laws for ordered timestamps and inter-candidate
waits. The one-candidate case is
fully integrated as a Markov kernel: sample its uniform conditional timestamp,
flow, thin the event, and flow through the residual horizon.
Lean now constructs the unconditional dependent joint law of the Poisson count
and its padded ordered-wait sequence, proves it is a probability measure, and
proves its count marginal is exactly the original Poisson law.
That law is now connected to arbitrary-count execution. Lean builds measurable
flow/jump steps retaining the padded schedule, iterates exactly the runtime
count, flows through the residual horizon, and glues the count-indexed kernels
into one Markov kernel. Consequently every globally bounded thinning simulator
has a complete positive-horizon transition kernel driven by the exact
homogeneous Poisson schedule. This proves construction and Markov validity,
not stationary-target preservation or convergence for BPS/Zig-Zag. In the
stronger special case where flow and uniformized events separately preserve a
target, Lean proves invariance of the entire scheduled mixture and uses it for
the telegraph process. Lean
proves its exact transported-law decomposition into Poisson-weighted,
fixed-count, ordered-time averages. An adjacent-count flux certificate now
formalizes the required cancellation: each transported and target count
stratum shares a core while residual flux shifts by one count, and equality of
the total flux proves horizon invariance. The adjacent Poisson weights satisfy
the required exact recurrence `(n+1)p(n+1) = intensity·p(n)`. The infinite
flux-shift equality is now derived automatically from the client-facing
count-zero boundary condition, so a concrete client only supplies its two
finite-stratum spatial decompositions and zero initial flux. Zig-Zag/BPS
clients must still construct those spatial identities; neither deterministic
schedules nor individual count components are incorrectly assumed invariant.

For positive-horizon particle Gibbs, the finite library now proves a concrete
arbitrary-horizon result: with any finite particle index type containing at
least two particles, positive initial mass, and
full-support propagation at every Feynman--Kac step, the trajectory kernel
converges in total variation from every initial trajectory law. The proof
constructs two simultaneous genealogies for every pair of trajectories and
then applies the checked Doeblin layer. Its coefficient is deliberately
conservative. The same theorem is now exposed directly with labels
`Fin (extra+1)`: every `extra > 0` constructs a positive refresh certificate,
an explicit geometric bound using its finite-matrix rate, and TV convergence.
For the separate bounded-potential certificate, the closed-form coefficient
`((N-1)/(N-1+B))^T` and its time-varying finite-product analogue are monotone
in particle count and now proved to tend to one as `N → ∞`; every fixed-
positive-iteration geometric factor consequently tends to zero. Establishing
the model-specific minorization remains distinct from this asymptotic algebra.
Here `B` denotes the supplied PG penalty, not merely a raw potential ratio.
Primitive finite full-support models now construct a proved count-uniform
schedule directly. At each propagation it uses the oscillation constant of the
full remaining backward Feynman--Kac potential, with factor
`(N-1)/(N-2+2Bback)`, plus the terminal `(N-1)/N` factor. This yields geometric
TV convergence for every `N ≥ 2` and, at every fixed positive iteration count,
convergence of the actual PG output law to its trajectory target as
`N → ∞`. A smaller schedule obtained by substituting only each raw current
potential's oscillation remains a candidate and is not claimed by the proved
cumulative theorem.

For dynamic HMC trajectories, Julia also exposes
`first_stop_endpoint_uturn_candidates`. It builds root-dependent first-stop
rows and immediately checks the reroot condition consumed by the verified
finite-orbit selection theorem. Certified traces may use that theorem;
rejected traces remain useful diagnostics but carry no stationarity claim.
The root-independent adjacent and all-scales partitions remain the
conservative always-certified alternatives. Recursive completed-tree barriers
and `certified_dynamic_select` make accepted certificates directly executable
with target-weighted selection.

The Julia layer also exposes bounded warmup-only tuning for Gaussian RWMH.
`WarmupGaussianRWMH` uses diminishing `1/√n` Robbins--Monro log-scale updates,
clamps the proposal scale, and returns a frozen `GaussianRWMH` for retained
sampling. The warmup trajectory is explicitly not advertised as stationary;
the existing Lean adaptive-MCMC results describe the mathematical conditions,
while cross-language refinement of this particular floating-point tuner
remains separate.

The executable breadth layer now also includes categorical discontinuous HMC.
`CategoricalDHMC` uses Laplace momentum and the paper's exact
crossing-or-reflection update on a cyclic categorical embedding; Reference and
Optimized implementations pass deterministic trace and stationary-frequency
tests. Lean proves the corresponding scalar Hamiltonian is preserved exactly.
It also proves that exponentially refreshed Laplace kinetic energy gives
exactly the usual Metropolis acceptance probability and derives stationarity
of the positive symmetric finite one-step kernel. This does not yet claim the
full discontinuous-HMC correctness theorem:
almost-everywhere volume preservation, distributional reversibility of random
coordinate orders, and phase-kernel invariance remain to be formalized.

Betancourt's [*A Conceptual Introduction to Hamiltonian Monte
Carlo*](https://arxiv.org/abs/1701.02434) is used as a foundational HMC
reference. Its lift--evolve--project correctness spine and the boundary between
invariance, convergence, and conceptual guidance are mapped in the
[foundation coverage note](docs/betancourt17-coverage.md).
Neal's [*MCMC using Hamiltonian
dynamics*](https://arxiv.org/abs/1206.1901) additionally informs the endpoint
Metropolis, momentum-transition, partial-refreshment, and windowed-HMC
boundaries recorded in its [foundation coverage note](docs/neal12-coverage.md).

## Current status

The repository now contains machine-checked implementations and proofs for:

- general-state Metropolis--Hastings, Gaussian RWMH, and coupled Gaussian
  RWMH as mathlib Markov kernels;
- general-state independence MH with the classical bounded-density-ratio
  `1 / M` target minorization, exact Doeblin residual decomposition, and
  two-sided eventwise convergence rate `(1 - 1 / M)^n` for `M > 1`;
- finite-dimensional state-dependent Gaussian proposals, with ULA proved
  Markov but not target-exact and MALA proved reversible and target-invariant;
- general-state two-block auxiliary Gibbs/data augmentation, including a
  slice-sampling interface whose correctness is reduced to an explicit
  vertical/horizontal joint-factorization equation, plus a within-conditional
  theorem for current-state-dependent horizontal updates that preserve the
  auxiliary-first under-graph joint law;
- a concrete measurable vertical slice-height Markov kernel and proof that
  its lifted weighted target is exactly Lebesgue measure under the target
  graph, plus a measurable horizontal conditional obtained by standard-Borel
  disintegration and an exact target-invariance theorem for the resulting
  general-state slice sampler, instantiated for the uniform law on `(-2,2]`;
  on real-valued targets with measurable interval superlevel sets, Lean also
  constructs the horizontal kernel explicitly, handles null empty-level and
  endpoint rows, and proves weighted-Lebesgue invariance. A joint trace-space
  theorem now reduces practical stepping-out/shrinkage correctness to a
  measure-preserving deterministic trace reversal, allowing the reverse run
  to transform its random trace. Its guarded form proves that a
  measure-preserving successful reversal can be totalized by identity on a
  measurable failure/exhaustion branch; the concrete Julia success-branch
  reversal remains an explicit obligation;
  Julia additionally exposes a bounded-interval rejection implementation with
  Reference/Optimized trace replay and uniform moment tests, while its callback,
  Float64 RNG, and finite retry guard remain outside the ideal refinement theorem;
- tagged two-model reversible-jump MH with a common reference measure,
  transport-density certificate, cross-model accepted-flow symmetry, and
  Markov/reversibility/invariance theorems, including a zero-to-one-dimensional
  Euclidean birth/death client whose `y = 2u` transport has a checked
  inverse-Jacobian density. Coordinate certificates now compose over an
  arbitrary finite homogeneous product, with iterated product measures,
  transports, densities, and probability-law instances generated recursively;
- finite iid particle clouds whose average nonnegative importance weight is
  proved unbiased, with exact distinct-coordinate factorization and the
  finite identity `MSE(average) = variance / particle-count`, together with
  a finite Chebyshev deviation bound, mean-square and in-probability
  consistency as the explicit count tends to infinity, and the resulting
  pseudo-marginal MH extended stationarity and exact target marginal;
- unbiased multinomial ancestor resampling, heterogeneous propagation, and a
  one-step bootstrap resample--propagate expectation identity, lifted to an
  arbitrary finite-horizon homogeneous Feynman--Kac expectation theorem for
  strictly positive potentials and to time-varying finite sequences; the
  recursively generated bootstrap population law now also has an explicit
  finite-horizon `C/N` MSE bound around the exact normalized Feynman--Kac law
  and converges in mean square and probability for every fixed horizon as the
  particle count tends to infinity;
- a normalized finite distribution over complete SMC population/ancestry
  histories, an exact product-weight expectation theorem, and the resulting
  explicit-history pseudo-marginal kernel with exact stationary state marginal,
  including state-indexed potentials and transitions at a common horizon;
- the normalized history-weighted selected-particle target and exact
  observable/eventwise identification of its Feynman--Kac terminal marginal;
- backward tracing through stored ancestor maps, producing a selected genealogy
  of the correct length with machine-checked initial and terminal endpoints;
- the one-transition many-to-one identity for arbitrary parent--child
  observables, both conditional on the current cloud and after iid initialization;
- the arbitrary-horizon labeled many-to-one theorem, equality of propagated
  path prefixes with backward genealogy tracing, and finite PIMH with exact
  extended-target stationarity and selected-path Feynman--Kac expectations;
- finite PMMH with parameter-indexed initial laws and fixed-horizon schedules,
  exact extended-target stationarity, requested parameter marginal, and joint
  parameter/selected-path expectation;
- reusable finite identity, composition, mixture, and coordinate-lift
  combinators; finite one-site, random-scan, and systematic-scan Gibbs;
- finite state-dependent kernel selection and a checked counterexample showing
  that common invariance of all frozen kernels does not imply invariance after
  state-dependent selection;
- predetermined nonhomogeneous finite-chain evolution, preservation under a
  common stationary target, finite row total variation, and deterministic
  diminishing-schedule vocabulary;
- finite random parameter adaptation as an augmented Markov kernel, with the
  probability of successive kernel changes and a convergence-in-probability
  Diminishing Adaptation definition;
- finite distribution total variation, uniform mixing-by-horizon,
  adaptive mixing-failure probabilities, Containment, and the theorem that
  simultaneous uniform mixing implies Containment;
- total-variation triangle/contraction lemmas, one-step uniform kernel
  perturbation, and a telescoping finite-window schedule comparison bound;
- state and parameter marginals of random adaptive laws, the exact mixed
  next-state law, and a law-weighted row-to-target TV bound;
- the finite Roberts--Rosenthal adaptive-MCMC theorem: Diminishing Adaptation
  plus Containment implies total-variation convergence of the deterministic
  state-marginal laws, without an almost-sure or rate claim;
- general-state Ionescu--Tulcea semantics for adaptive selectors that inspect
  the entire finite history, with infinite path laws, finite coordinate
  marginals, and exact reduction to homogeneous kernel powers under constant
  parameter selection. Lean now also proves an exact frozen-tail factorization:
  after arbitrary finite history-dependent burn-in, eventual constant
  parameter selection gives ordinary powers of the frozen kernel applied to
  the actual burn-in marginal. A common positive Doeblin minorization and
  invariance certificate then yield two-sided geometric event bounds and
  setwise convergence. For a predetermined general-state schedule that may
  change forever, a shared positive Doeblin component and common invariant
  target now give an exact nonhomogeneous regenerative decomposition,
  two-sided geometric event bounds, and setwise convergence. A separate proxy
  certificate closes the general measure-level approximation-plus-containment
  argument for actual history-adaptive marginals. Deriving that certificate
  from state- or history-dependent Diminishing Adaptation remains open;
- two-temperature parallel tempering with an MH-corrected swap, product-target
  stationarity, and an exact cold-marginal theorem;
- finite pseudo-marginal MH with a nonnegative unbiased estimator, including
  zero estimator values, exact extended-target stationarity, and the desired
  target marginal;
- reversible-jump MH on tagged model spaces, including scalar and product
  birth/death transports and a genuinely nonlinear non-product triangular
  shear whose curved-strip density and complete tagged-target invariance are
  proved;
- a general lift--evolve--project invariance theorem for auxiliary-variable
  MCMC, including a deterministic measure-preserving-flow specialization;
- a phase-space lifting theorem for arbitrary invariant momentum transitions,
  with full independent refreshment as a specialization;
- finite-dimensional leapfrog dynamics and full multinomial HMC, including
  momentum refresh, randomized trajectory origin, multinomial selection, and
  target invariance;
- corrected relativistic and Riemannian momentum measures, the diagonal
  SoftAbs Hamiltonian and its derivatives, and endpoint and multinomial
  GR-HMC target-invariance theorems; a Gaussian-plus-sinusoidal potential now
  supplies an actual nonconstant SoftAbs Hessian, including its removable zero
  branch and complete Equation (12) certificate; a separate explicitly
  refresh-augmented Gaussian SoftAbs client has geometric eventwise bounds and
  setwise convergence from every initial probability law;
- maximal and optimal-transport trajectory-index couplings, with exact HMC
  marginals;
- a measurable finite optimal-transport selector with proved optimality;
- the coupled multinomial-HMC/Gaussian-RWMH mixture and its invariant
  single-chain marginal;
- exact-meeting and relaxed-meeting path events, drift interfaces, and
  geometric tail theorems;
- the finite lagged telescoping estimator, its exact marginal-expectation
  identity, and an infinite stopped estimator which is `L¹`, unbiased for
  bounded observables under kernel-level faithfulness, and in `L²` under a
  geometric meeting tail, together with finite expected correction count and
  almost-surely finite pathwise correction work, plus
  a stationary-start invariant-expectation specialization; a uniform
  higher-moment theorem also proves unbiasedness and finite variance for
  unbounded observables, while its stationary form requires only one
  target-space `MemLp` certificate;
- Xu et al.'s regularity and local-strong-convexity assumptions;
- compact-uniform exact-flow and leapfrog contraction estimates;
- total-variation and relative centered-energy estimates for multinomial
  trajectory weights;
- general `C²` locally uniform `o(|ε|)` control of the phase derivative of
  one leapfrog energy defect;
- cutoff-wise maximal-coupling contraction and one-step relaxed accessibility
  of the implemented shared-momentum HMC kernel;
- composition of that accessibility result with Xu's drift assumptions to
  obtain a geometric relaxed-meeting tail for the concrete HMC/RWMH mixture;
  and
- a finite-data `L²`-regularized logistic-regression potential with its exact
  leapfrog gradient, explicit global smoothness constant, strong convexity,
  and concrete coupled-HMC relaxed-accessibility window.

There is also a fully instantiated standard-Gaussian result in every nonempty
finite dimension: for the verified multinomial-HMC/Gaussian-RWMH mixture,
Lean proves a geometric exact lag-one meeting tail from deterministic
initialization. This includes a proved affine drift inequality for the actual
selected HMC transition at `ε = √2`, `L = 1`.
For bounded observables, a concrete wrapper additionally proves estimator
unbiasedness and finite variance conditional on the explicitly stated
Dirac-start marginal-expectation convergence obligation.

The finite-data `L²`-regularized logistic target is also fully instantiated:
at any cancellation step `ε²λ = 2` with `L = 1`, Lean proves HMC drift,
compact energy geometry, and a geometric exact lag-one meeting tail for the
concrete sticky HMC/RWMH mixture in every nonempty finite dimension.
It has the analogous bounded-observable estimator wrapper with marginal
expectation convergence left explicit.

### Executable finite samplers

The finite executable vertical slice is operational. Lean proves that the
cumulative natural-weight selector has exactly its normalized PMF. For any
strictly positive target weights and positive-total proposal rows on `Fin n`,
Lean proves that the generic executable MH step has the same row PMF as the
existing verified finite MH kernel, including asymmetric and zero proposal
edges. A compiled Lean binary is the conformance oracle. Lean also emits the
versioned sampler IR consumed by the maintained Julia reference interpreter,
which is exercised against the oracle and an independent optimized
implementation on exhaustive small finite traces. Universal trace-refinement
theorems prove that the Lean IR interpreter agrees with the established
categorical and MH replay semantics for every valid finite configuration and
trace.

The public Julia interface uses positional RNG dispatch:

```julia
using VerifiedSamplers, Random

target = FiniteWeights([1, 0, 2])
samples = sample(MersenneTwister(1), target, 100)
chain = sample(MersenneTwister(2), TwoStateMH(), false, 100)

proposal = FiniteKernelWeights([
    [1, 2, 1],
    [1, 1, 1],
    [0, 2, 1],
])
sampler = FiniteMH(FiniteWeights([1, 2, 3]), proposal)
generic_chain = sample(MersenneTwister(3), sampler, 1, 100)
```

The no-RNG methods delegate to `Random.default_rng()`. Julia indices are
one-based at the public categorical API; the reference interpreter and Lean `Fin`
encoding are zero-based.

### Continuous executable boundary

The continuous executable layer uses typed ideal primitives for bounded
natural draws, a standard normal, and a unit uniform. Lean identifies the
standard-normal denotation with mathlib's exact Gaussian density measure and
validates kind-tagged mathematical traces. The versioned sampler artifact now
contains an inspectable Gaussian RWMH program interpreted by Julia Reference;
Optimized remains an independent tested `Float64` implementation:

```julia
sampler = GaussianRWMH(x -> -x^2 / 2, 1.0)
chain = sample(MersenneTwister(4), sampler, 0.0, 10_000)
```

The typed first-order Lean IR now has exact kernel and trace interpretations,
and the canonical scalar program is proved to have the full
proposal/accept-or-retain trace behavior for arbitrary real log densities and
scales. For measurable log densities and positive scales, its exact kernel
semantics equals the existing verified Gaussian RWMH construction and preserves
the density `exp ∘ logdensity`; explicit normalization makes that target a
stationary probability measure. Public Julia sampling routes through the
serialized IR interpreter. No theorem equates its finite-precision law with
the exact Lean kernel; the explicit boundary is deliberate:
mathlib `ℝ`, `gaussianReal`, and `Measure` are semantic objects, whereas Julia
uses `Float64` and the selected `AbstractRNG` implementation.

Lean records the missing backend theorem as
`NumericalRefinement`: an explicit hypothesis-bearing contract with no Julia
or Float64 witness. Thus downstream work can name the deferred obligation
without silently assuming that it has already been proved.

Lean now also provides a bounded refinement layer. It composes absolute error
bounds for the affine proposal, callback log ratio, clamping, exponential
threshold, and uniform draw. The Float64 and ideal executions provably take
the same branch whenever the ideal uniform-to-threshold margin exceeds the
combined threshold and uniform errors; any branch disagreement is confined to
that explicit boundary band. Concrete Julia/libm/RNG error certificates are
still inputs to this theorem rather than assumed facts.

| Layer | Current guarantee |
|---|---|
| Ideal trace | Proved for arbitrary scalar log densities and real scales |
| Exact kernel | Proved for measurable log densities and positive scales |
| Stationarity | Proved for the normalized `exp ∘ logdensity` target |
| Julia Reference | Interprets the committed version-14 sampler IR |
| Julia Optimized | Independently implemented and differentially tested |
| Bounded numeric refinement | Proved composition and decision-stability theorems, conditional on concrete operation-error certificates |
| Julia execution certificates | Per-run checked RWMH/HMC decision witnesses with explicit callback, libm, and RNG bounds |
| Universal Float64/RNG theorem | Not claimed; still requires a formal Julia/LLVM/libm/RNG semantics and callback specifications |

See the [continuous executable contract](docs/continuous-executable-contract.md)
for the exact theorem and runtime boundaries, and the
[executable roadmap](docs/executable-roadmap.md) for prioritized next steps.

The executable HMC slice is also operational: scalar and vector-valued, unit-mass,
endpoint-corrected HMC with any positive finite number of leapfrog steps. Lean
proves its ideal trace formula, identifies its deterministic update with the
established `leapfrogN` map for every trajectory length, and proves exact
phase-volume preservation and Boltzmann-target invariance of the corresponding
phase kernel. The complete refresh–evolve–project position kernel is also
defined and proved invariant for every compatible position target. The
version-14 artifact is interpreted by Julia Reference and
differentially tested against Optimized, including energy, reversibility,
numerical-volume, Gaussian-moment, and non-Gaussian quartic-moment tests:

```julia
sampler = ScalarHMC(x -> -x^4 / 4, x -> x^3, 0.15, 6)
chain = sample(MersenneTwister(7), sampler, 0.0, 10_000)

vector_sampler = VectorHMC(q -> -sum(abs2, q) / 2, identity, 0.18, 6)
# Columns are successive two-dimensional states.
vector_chain = sample(MersenneTwister(8), vector_sampler, [0.0, 0.0], 10_000)
```

The vector program draws one normal momentum per coordinate and is generated
from the typed Lean command IR. Lean proves that its list-valued integrator is
extensionally the existing `Position (Fin n)` leapfrog map, and the generic
exact endpoint kernel is invariant in every finite dimension. Reference and
Optimized agree on fixed traces, and the public sampler is tested on a
two-dimensional Gaussian.

Constant-metric execution is also available through `MetricHMC` with either
`DiagonalMetric` or symmetric positive-definite `DenseMetric`:

```julia
Σ = [1.0 0.8; 0.8 2.0]
precision = inv(Σ)
sampler = MetricHMC(q -> -dot(q, precision * q) / 2,
    q -> precision * q, DenseMetric(Σ), 0.15, 6)
chain = sample(MersenneTwister(9), sampler, zeros(2), 10_000)
```

Lean defines the corresponding diagonal and dense inverse-mass velocity maps,
proves exact time reversal, endpoint-proposal involution, phase-volume
preservation, Boltzmann phase invariance, and refreshed position invariance.
The version-14 artifact retains the type-indexed diagonal and dense commands
introduced in version 6, so Julia Reference executes both through the
generated IR. Lean also proves the
linear/Cholesky Gaussian pushforward law and its determinant-normalized
quadratic kinetic density using mathlib's matrix change-of-variables theorem.

The Xu et al. coupled HMC/RWMH mixture is exposed through the version-14 IR:

```julia
sampler = Xu21CoupledSampler(q -> -sum(abs2, q) / 2, identity,
    0.15, 4, 0.6, 0.9)
coupled = sample(MersenneTwister(21), sampler,
    ([0.0, 0.0], [2.0, -1.0]), 1_000)
findfirst(coupled.met)
```

The interpreter uses shared momentum and trajectory origin, maximal coupling
of multinomial indices, maximal Gaussian proposals, shared accept/reject
uniforms, and a shared mixture decision. Lean proves that the ideal command
has the verified single-chain mixture on both marginals; `met` records exact
replay-level equality. As elsewhere, concrete Float64 execution is separated
from the ideal-real theorem by the numerical-refinement boundary.

Backend-facing Lean certificates now compose proposal, callback, endpoint
energy, `exp`, and RNG bounds into the RWMH/HMC decision-stability theorems.
Julia exposes matching per-run checked witnesses through
`VerifiedSamplers.Certificates`. These certify branch agreement only when the
supplied ideal values and primitive bounds are valid and the comparison lies
outside their uncertainty band; they are not a universal proof of arbitrary
Julia callbacks or platform `libm` behavior.
For generated restricted target expressions, Lean additionally propagates
primitive rounding errors through the complete value and symbolic-gradient
trees. A proved mean-value bound derives exponential argument transport from
only the backend's local libm error, using the finite adaptive factor
`exp(max(computed, ideal))`.
IR version 13 adds portable sine and cosine nodes. Lean proves their symbolic
derivatives and uses the global one-Lipschitz bounds for `sin` and `cos` to
compose backend-local libm errors with input error. The generated
`x²/2-sin(x)` artifact is proved to denote the nonconstant SoftAbs client's
potential and force, and Julia decodes and evaluates that generated tree.
For the generated polynomial Gaussian target, Julia now also emits an exact
dyadic execution certificate: finite Float64 inputs and outputs are converted
to mathematical `Rational{BigInt}` values, so the value and derivative errors
against `x²/2` and `x` are exact and require neither BigFloat nor libm. Lean
checks the serialized rational artifact through `mcmc_oracle` and proves that
every accepted record satisfies the corresponding value and derivative
approximation statements. This checks each submitted artifact, not the Julia
compiler or serializer implementation itself.

Executable randomized-origin multinomial HMC is available separately from
endpoint-corrected HMC:

```julia
sampler = MultinomialHMC(q -> -sum(abs2, q) / 2, identity, 0.2, 6)
chain = sample(MersenneTwister(10), sampler, zeros(2), 10_000)
```

Lean proves that the ideal origin/index choice program has exactly the
existing `randomizedMultinomialLeapfrogPMF` law, identifies its measure with
the verified kernel row, and assigns the complete refresh–evolve–project
command the proved invariant position kernel. Julia Reference interprets the
generated version-14 command; Optimized independently builds the re-rooted
trajectory. Float64 Boltzmann weights and categorical boundary decisions
retain the explicit numerical-refinement qualification.

The same algorithm is available with diagonal or dense constant metrics via
`MetricMultinomialHMC`. Lean proves orbit-kernel phase and refreshed-position
invariance, including the Cholesky-refreshed specialization. The artifact
contains separate metric-kind-correct commands.

Corrected relativistic multinomial HMC was introduced in IR version 10 and is
retained in the current version 16 artifact. The
constant diagonal-metric client is directly executable:

```julia
sampler = RelativisticMultinomialHMC(
    q -> -sum(abs2, q) / 2,
    identity,
    DiagonalMetric([1.0, 4.0]),
    1.0,  # relativistic mass
    0.1,  # step size
    6)
chain = sample(MersenneTwister(12), sampler, zeros(2), 1_000)
```

Its momentum generator uses the dimension-correct radial Jacobian, a uniform
spherical direction obtained by normalizing a Gaussian vector, and the
corrected inverse-factor transport `p = A⁻¹z`. Reference and Optimized are
differentially tested on replay traces.

`CertifiedRelativisticMultinomialHMC` is the position-dependent interface. Its
integrator must return an `ImplicitSolveCertificate`; execution refuses a
positive residual tolerance or missing uniqueness, reversibility, or
volume-preservation witness. These witnesses remain explicit backend
assumptions. They do not turn an arbitrary callback into a machine-checked
implementation of the Lean generalized-leapfrog map.

## What “HMC” means here

The paper's main results concern multinomial HMC. Accordingly, the formalized
transition contains:

1. Gaussian momentum refresh;
2. forward and backward leapfrog trajectory generation;
3. randomized placement of the current state in the trajectory; and
4. multinomial state selection using Hamiltonian weights.

Endpoint-only Metropolis HMC is a different comparison algorithm and is not
silently substituted for multinomial HMC.

The coupled HMC kernels are separately proved to have the verified
single-chain multinomial-HMC kernel as both marginals. Likewise, the coupled
RWMH kernel has the verified RWMH kernel as both marginals.

## Paper-statement audit

The README records only the headline qualifications. Each paper has a
consistently named coverage audit with the exact claims, Lean artifacts,
corrections, and remaining conditions.

### Xu et al. (2021): Couplings for Multinomial HMC

- Printed Condition 1 cannot hold on a nontrivial region under quantifiers
  reaching zero integration time; the proved replacement uses a positive
  integration-time window and, where needed, a fixed kinetic cutoff.
- The unconditional exponent-two contraction route is obstructed in the
  audited short-time regime; the completed meeting proof instead uses the
  repaired first-moment maximal-coupling route and an explicit drift premise.

See the [2021 coverage audit](docs/xu21-coverage.md) and
[2021 roadmap](docs/xu21-roadmap.md).

### Xu and Ge (2024): Relativistic Riemannian HMC

- Algorithm 1 needs `r^(d-1)`, a genuinely uniform spherical direction, and
  inverse-factor transport under the paper's factor convention.
- Equation (9) needs the momentum gradient and a corrected anisotropic bound.
- Momentum symmetry alone does not establish kernel validity.
- Six fixed-point iterations are only approximate in general; exact kernel
  correctness remains conditional on the explicit integrator certificate.

See the [2024 coverage audit](docs/xu24-coverage.md) and
[2024 roadmap](docs/xu24-roadmap.md).

## Main theorem boundary

The general theorem surface now has the following dependency chain:

```text
RegularPotential + LocalStrongConvexity
  → cutoff-wise maximal multinomial-HMC contraction
  → relaxed accessibility of the implemented coupled HMC kernel

XuTheorem41DriftAssumptions for the same selected HMC/RWMH kernels
  + relaxed accessibility
  → geometric relaxed-meeting tail for the concrete coupled mixture
```

The exact lag-one theorem uses the faithful sticky mixture and the localized
Gaussian-RWMH exact-meeting small set. Its abstract and finite-dimensional
standard-Gaussian forms are proved.

For a general target, the remaining analytic input is a compatible
Foster--Lyapunov drift certificate for at least one `ε,L` pair selected by the
local-convexity window. Such a drift condition is an explicit hypothesis of
the paper's meeting-time result; it does not follow from local strong
convexity alone. For the separate one-dimensional Gaussian SoftAbs GR-HMC
validation target at `ε = 1`, `L = 1`, the exponential affine drift
certificate is now proved for the actual bare multinomial kernel. Its pending
local accessibility input is now also closed: a positive finite-step skeleton
minorizes normalized central Lebesgue measure on every bounded band and has a
faithful exact-meeting coupling there. A uniform geometric allowance bound now
also constructs the compatible paired threshold and enclosing band, yielding
an unconditional geometric meeting-drift certificate. Setwise convergence of
the resulting positive skeleton is now unconditional: Lean proves the required
exponential moment of the normalized one-dimensional Gaussian target. Bounded-
observable convergence, Chapman--Kolmogorov, and a finite residue-class lemma
then lift the result from the skeleton to every unthinned time index. Thus the
actual bare `ε = 1`, `L = 1` chain converges setwise from every point mass.
Higher-dimensional or non-Gaussian validated instances must still provide
their own target-specific drift analysis.

For regularized logistic regression, the local regularity, convexity, and HMC
accessibility obligations are proved. For the cancellation step size
`ε² λ = 2`, Lean also proves exact leapfrog position and momentum formulas
and a one-step Hamiltonian-defect envelope with the strict coercive term
`-(λ/8)‖q‖²`. The capped-retention envelope is integrated against refreshed
Gaussian momentum, yielding a finite explicit allowance and a strict affine
drift theorem for the actual `L = 1` multinomial-HMC kernel. The remaining
compact energy geometry is also proved, culminating in a fully instantiated
exact lag-one geometric meeting-tail theorem for the concrete sticky
regularized-logistic HMC/RWMH mixture in every nonempty finite dimension. The
posterior is normalized explicitly and has finite distance-Lyapunov moment.
One selected mixture supplies both the lag-one and stationary-target meeting
tails, so bounded marginal expectations converge to the posterior integral
and the stopped estimator is unbiased for that same integral with finite
variance.

Floating-point refinement and reproduction of the paper's experiments are
separate goals and are not claimed as machine-checked results.

## Mathematical boundaries

These implications must not be conflated:

```text
kernel validity
  < target invariance
  < convergence from arbitrary initial states
  < geometric meeting tails
  < finite-variance unbiased estimation
```

Detailed balance implies invariance, not convergence. A coupled kernel having
the correct marginals does not imply that the chains meet. Geometric tails
require drift and small-set or accessibility arguments in addition to local
HMC contraction.

## Build

The repository pins Lean and mathlib. From the repository root:

```sh
cd formal
lake update
lake exe cache get
lake build
```

For a narrow check while editing the main analytic module:

```sh
cd formal
lake env lean Mcmc/Hamiltonian/LocalContractivity.lean
```

From the repository root, `make formal`, `make julia`, and `make test` provide
the corresponding aggregate entry points. `make oracle` compiles the Lean
conformance oracle, `make generate` explicitly regenerates the committed Julia
reference IR artifact consumed by the maintained Julia interpreter,
and `make check-generated` checks freshness without modifying the tree.
`make docs` regenerates the Lean-owned architecture graphs and builds the
Documenter site locally in `docs/build/`; `make check-docs-generated` verifies
that the committed graph page is current.
The [testing strategy](docs/testing.md) records the exact, differential,
statistical, robustness, and performance layers; no registered Julia testset
is currently skipped.

## Repository guide

- [`formal/`](formal/): pinned Lean project containing the `Mcmc` library.
- [`VerifiedSamplers.jl/`](VerifiedSamplers.jl/): Julia package, with
  interpreted reference and maintained optimized implementations in separate
  internal submodules.
- [`docs/`](docs/): architecture notes, coverage audits, roadmaps, and the
  development log.

## License

See [`LICENSE`](LICENSE).
