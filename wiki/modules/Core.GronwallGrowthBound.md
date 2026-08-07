# Module: SHSLib.Core.GronwallGrowthBound

**File:** `SHSLib/Core/GronwallGrowthBound.lean`
**Layer:** Core
**Status:** ✅ 0 sorries

## What it proves

Completes Hespanha (2005), Lemma 1 / Eq. (35) — the sample-path growth bound
that underlies Assumption 2(ii) — in the *time-varying-rate* form the paper
states, and extends it from a single flow segment to a full hybrid sample path
with resets.

`SHSLib.Core.Generator` already contains

* `SHS.lemma1_linear_growth_bound_false` — a machine-checked certificate that
  the literal formalization of Eq. (35) is false (its `c_f / γ_f(t₀)` term
  degenerates when `γ_f(t₀) = 0`), and
* `SHS.lemma1_linear_growth_bound` — a corrected bound for a *constant* rate
  `K`, obtained from Mathlib's `gronwallBound`.

Mathlib's Grönwall API only covers a constant rate, so the time-varying case
needed a new inequality, proved here from scratch.

## Key theorems

| Theorem | Statement (informal) |
|---------|----------------------|
| `gronwall_varying_rate` | Grönwall's inequality with a time-varying nonnegative rate, integral form: `u t ≤ δ + ∫_a^t (γ u + c)` on `[a,b]` implies `u t ≤ (δ + c(t−a))·e^{∫_a^t γ}` |
| `continuous_setIntegral_Icc_left` | The primitive `s ↦ ∫_{[a,s]} f` of a continuous function is continuous |
| `SHS.HasGlobalFlow.continuous_flow` | The flow is continuous in time when the drift along the trajectory is |
| `SHS.le_growthEnvelope` | The envelope dominates its own initial value |
| `SHS.continuous_growthEnvelope` | The envelope is a continuous function of time (Assumption 2(ii): “bounded by a continuous function”) |
| `SHS.growthEnvelope_monotoneOn` | The envelope is nondecreasing on `[t₀, ∞)` |
| `SHS.growthEnvelope_restart` | Restarting the envelope at an intermediate time never exceeds the envelope at a later time |
| `SHS.flow_norm_le_growthEnvelope` | Flow-segment bound: `‖φ(t;t₀,q₀,x₀)‖ ≤ (‖x₀‖ + c_f(t−t₀))·e^{∫_{t₀}^{t} γ_f}` |
| `SHS.lemma1_linear_growth_bound_varying_rate` | Lemma 1 (Eq. 35), corrected sum form with time-varying rate, for the flow from an initial condition `z₀` |
| `SHS.flow_eq_of_lipschitz` | Forward uniqueness: two continuous solutions of the flow integral equation with a Lipschitz drift and the same initial value coincide for `t ≥ t₀` |
| `SHS.HasGlobalFlow.flow_eq_of_lipschitz` | Consequently any two global flows of the same SHS agree forward in time |
| `SHS.hybrid_path_growth_bound` | Lemma 1 for the whole hybrid sample path: with resets satisfying `‖φ_ℓ(q,x,t)‖ ≤ max ‖x‖ c_φ`, every segment stays below the single envelope started at `max ‖x₀‖ c_φ` |

## Key definitions

| Definition | Description |
|------------|-------------|
| `SHS.growthEnvelope γ_f c_f A t₀ s` | The Grönwall envelope `(A + c_f·(s − t₀))·exp(∫_{t₀}^{s} γ_f)` |

## Proof sketch

*Grönwall with a variable rate.* Put `v t = δ + ∫_a^t (γ u + c)`, so `u ≤ v`
and `v' = γ u + c ≤ γ v + c` by the fundamental theorem of calculus. With
`G t = e^{−∫_a^t γ}` the function `H t = δ + c(t − a) − G t · v t` has
derivative `c(1 − G) + γ G (v − u) ≥ 0`, so `H` is monotone on `[a,b]` and
`H a = 0`; dividing by `G t > 0` gives the bound.

*Lemma 1.* Along the flow, `‖f(q₀, x(s), s)‖ ≤ γ_f(s)‖x(s)‖ + c_f`, so the
integral form of the flow equation (`HasGlobalFlow.flow_ode`) gives exactly the
hypothesis of the Grönwall inequality with `u = ‖x‖`, `δ = ‖x₀‖`, `c = c_f`.

*Flow uniqueness.* For two solutions `y, z` the difference obeys
`‖y(t) − z(t)‖ ≤ ∫_{t₀}^{t} L‖y − z‖`, so the same Grönwall inequality with
`δ = c = 0` forces `‖y(t) − z(t)‖ ≤ 0`.

*Hybrid paths.* Induct over the transition index. At a transition,
`‖x(τ⁺)‖ ≤ max ‖x(τ⁻)‖ c_φ`, and the envelope started at `max ‖x₀‖ c_φ`
dominates `c_φ`; between transitions the segment bound applies, and
`growthEnvelope_restart` shows that restarting the envelope at the transition
time loses nothing.

## Hypotheses worth noting

* `hf_cont`: the drift evaluated along the trajectory is continuous in time.
  This is what allows the integral form of the flow equation to be
  differentiated; without some such regularity the flow map recorded in
  `HasGlobalFlow` is not tied to a differentiable trajectory.
* The rate `γ_f` is assumed continuous and nonnegative and `c_f ≥ 0`, as in the
  paper.
* Only the drift governs the continuous flow, so the reset constant `c_φ`
  appears only in `SHS.hybrid_path_growth_bound`.

## Depends on

- [[Core.Generator]] (hence [[Core.Basic]])

## Open gaps / sorries

None.
