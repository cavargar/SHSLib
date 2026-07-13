# Module: SHSLib.Foundations.DavisCh2

**File:** `SHSLib/Foundations/DavisCh2.lean`
**Layer:** Foundations
**Status:** ⚠️ Has sorries

## What it proves

Formalizes Davis's Piecewise-Deterministic Markov Process (PDMP/PDP) theory from Chapters 2 and 24–25 of *Markov Models and Optimization*. Covers: exponential memorylessness, survivor/hazard functions, Poisson process properties, renewal equations, ODE theory (global existence, flow bijectivity, group property, chain rule), the deterministic Dynkin formula, linear ODE solutions (variation of constants), Gronwall uniqueness, inverse-transform sampling, and the full PDP structure with its Markov/strong-Markov properties, compensator martingale, extended generator characterization, and boundary conditions.

## Key theorems

| Theorem | Statement (informal) |
|---------|----------------------|
| `exponential_memoryless` | Memoryless property of exponential distribution |
| `survivor_from_hazard` | Survivor function from cumulative hazard |
| `poisson_markov_property` | Poisson process Markov/Chapman–Kolmogorov property |
| `renewal_equation` | Renewal integral equation |
| `flow_group_property` | `φ(t+s, x) = φ(t, φ(s, x))` |
| `flow_chain_rule` | Chain rule along deterministic flow |
| `deterministic_dynkin` | Dynkin formula for deterministic systems |
| `gronwall_uniqueness` | Gronwall-type uniqueness for ODEs |
| `pdp_simple_markov` / `pdp_strong_markov` | PDP (strong) Markov property |
| `compensator_is_local_martingale` | Compensated PDP is a local martingale |
| `pdp_extended_generator_characterization` | Extended generator domain characterization |
| `pdp_generator_bounded_true_martingale` | Bounded generator ⟹ true martingale |

## Key definitions

| Definition | Description |
|------------|-------------|
| `PDP` | PDP structure: deterministic flow, jump rate, transition kernel |
| `PDPStandard` | PDP with boundary, non-explosion, absolute continuity |
| `pdpGenerator` | PDP extended generator `Af(x) = Xf(x) + λ(x)(Qf(x) − f(x))` |
| `pdpSurvivorFunction` | Survivor function for inter-jump times |

## Depends on

- Mathlib, [[Foundations.DavisCh1]] (implicitly, via shared definitions)

## Used by

- [[Core.Generator]]

## Open gaps / sorries

- 9 `by sorry` remain (down from 14). The rest are the deep measure-theoretic PDP
  results (Markov / strong-Markov properties, compensator/martingale
  representation, Feller / Borel-right-process properties) that require the full
  probabilistic PDMP construction, or stubs whose statement is not yet faithfully
  tied to the process (e.g. `pdp_filtration_right_continuous`,
  `pdp_generator_boundary_condition_necessary`).

### Recently closed (Aristotle — PDP semigroup construction)

- **Built the PDP semigroup** `pdpSemigroup` from first principles as the limit of
  the survivor-weighted operator `pdpSemigroupOp` and its iterates, closing 5
  sorries (14→9). New reusable infrastructure (all `sorry`-free, standard axioms
  only): survivor-function facts (`pdpSurvivorFunction_zero`/`_pos`/`_ge_exp`,
  `pdp_survivor_normalization`, `pdpSurvivorFunction_continuous_state`,
  `pdpSurvivorFunction_tendsto_one`); the operator and its bounds
  (`pdpSemigroupOp`, `pdpSemigroupOp_abs_le`, the contraction estimates
  `pdpSemigroupOp_dist_le`/`_dist_le_horizon`, measurability
  `pdpSemigroupOp_measurable` + `pdp_transitionMeasure_integral_measurable`,
  integrability `pdpSemigroupOp_integrand_integrableOn`); the iterates
  (`pdpSemigroupOp_iterate_measurable`/`_abs_le`/`_dist_le`/`_nonneg`,
  slice-continuity `pdpSemigroupOp_iterate_slice_continuous`, Cauchy tail bound
  `pdpSemigroup_sub_iterate_le`); and the semigroup laws
  (`pdpSemigroup_zero`/`_nonneg`/`_const`, additivity `pdpSemigroup_add` via
  `pdpSemigroupOp_add_step`/`pdpSemigroupOp_iterate_add`). Also
  `pdp_generator_bounded_true_martingale` (bounded generator ⟹ true martingale).

### Recently closed (Aristotle, earlier session)

- **`simulation_from_uniform` (23.4) and `realize_measure_real_from_uniform`
  (23.1, measure form).** Any probability measure `nu` on `EuclideanSpace ℝ (Fin d)`
  is the pushforward of Lebesgue measure on `[0,1]` under a measurable map.
  Proof structure: (i) a new self-contained 1D lemma
  `realize_measure_real_from_uniform` realizes *any* probability measure on `ℝ`
  as the pushforward of `volume.restrict [0,1]` under the quantile
  `β u = sInf {t | u ≤ cdf μ t}`, proved from the in-file
  `inverse_transform_sampling` together with `ProbabilityTheory.ofReal_cdf`,
  `monotone_cdf`, `tendsto_cdf_atBot/atTop`, right-continuity of the CDF
  Stieltjes function, and `Measure.ext_of_Iic`; (ii) the general case is reduced
  to the 1D case by the Borel-isomorphism embedding
  `MeasureTheory.exists_measurableEmbedding_real` into `ℝ` together with a
  measurable total left inverse from `MeasurableEmbedding.exists_measurable_extend`
  (with `g = id`), so `psi = h ∘ β` and `map psi vol = map (h ∘ g) nu = nu`
  (no a.e. handling needed). Standard axioms only.
- **`semigroup_iterate` (27.2–27.3).** The recursion `G^[n+1] ψ = G (G^[n] ψ)`
  for the PDP semigroup operator `G`, proved by `Function.iterate_succ_apply'`.
  Standard axioms only.

- **`flow_group_property` (22.3) — one-parameter group law of the flow**
  `φ(t+s, x) = φ(t, φ(s, x))`. A global Lipschitz hypothesis `hg : LipschitzWith K g`
  was added to the skeleton statement (it is genuinely required: the group law is
  an ODE-uniqueness statement and uniqueness fails without a Lipschitz condition).
  Proof: for fixed `s, x`, both `r ↦ φ(r+s, x)` and `r ↦ φ(r, φ(s, x))` solve
  `y' = g(y)` with the same value `φ(s, x)` at `r = 0`; `ode_gronwall_dist` then
  forces `dist = 0`, i.e. equality. Standard axioms only.

- **`ode_global_existence` (22.1) — global existence of the flow of a globally
  Lipschitz autonomous vector field.** For `g : ℝᵈ → ℝᵈ` globally `K`-Lipschitz,
  there is a flow `φ : ℝ → ℝᵈ → ℝᵈ` with `φ(0,x) = x`, `∂ₜφ(t,x) = g(φ(t,x))`
  for all `t`, and `φ` jointly continuous in `(t,x)`. Proved from Mathlib's
  *local* Picard–Lindelöf theorem by building solutions on ever-larger symmetric
  intervals and gluing them. New reusable infrastructure (all `sorry`-free,
  standard axioms only):
  - `ode_local_fwd` / `ode_local_bwd` — local existence on `[a,a+h]` / `[a-h,a]`
    for interval length `h < 1/K`, via `IsPicardLindelof.of_time_independent`
    (the ball radius is chosen large enough that the sub-linear growth bound
    `(‖g y‖ + K·R)·h ≤ R` holds, possible exactly because `K·h < 1`).
  - `ode_glue` — the piecewise concatenation of two ODE solutions on adjacent
    closed intervals sharing an endpoint value again solves the ODE (junction
    handled by `HasDerivWithinAt.union`).
  - `ode_pieces` — by induction on `n`, a solution on every `[-(n·h), n·h]`
    with value `x₀` at `0`.
  - `ode_within_unique` — two solutions on `[-r,r]` agreeing at `0` agree on all
    of `[-r,r]` (two-sided uniqueness, from `ODE_solution_unique` forward plus a
    time-reflected application backward).
  - `ode_gronwall_dist` — the exponential Grönwall bound
    `dist (α t) (β t) ≤ dist (α 0) (β 0)·exp(K|t|)` between two global solutions
    (`dist_le_of_trajectories_ODE`, both time directions).
  - `ode_global_solution_single` — a per-initial-point global solution
    (`ode_pieces` glued across scales by `ode_within_unique`).
  - `ode_flow_joint_continuous` — joint continuity of the assembled flow, from
    the Grönwall bound (Lipschitz in the initial datum, locally uniformly in
    time) together with continuity in time.

- `inverse_transform_sampling` (23.1) — for a monotone, right-continuous `F` with limits `0` at `-∞` and `1` at `+∞`, the generalized inverse `β(u) = sInf {t ∣ u ≤ F t}` transforms `U[0,1]` into a variable with CDF `F`: `volume {u ∈ [0,1] ∣ β(u) ≤ t} = F t`. New reusable infrastructure: `cdf_mem_Icc` (values of such an `F` lie in `[0,1]`), `quantile_le_iff` (the Galois equivalence `sInf {s ∣ u ≤ F s} ≤ t ↔ u ≤ F t` for `0<u<1`, via right-continuity + the up-set structure of `{s ∣ u ≤ F s}`), and `quantile_preimage_ae` (the preimage set equals `[0,F t]` up to the null endpoints `{0,1}`).
- `boundary_hitting_time_measurable` (27.1) — with the state space taken as `Set.univ`, `interior Set.univ = Set.univ`, so the indexing predicate `flow t x ∉ interior Set.univ` is never satisfied and `tStar ≡ ⊤` is constant, hence measurable (`measurable_const`).
- `renewal_equation` (21.8) — the conclusion is the defining hypothesis.
- `flow_bijective` (22.2) — inverse `φ(-t)` from the group law and `φ(0,·)=id`.
- `poisson_markov_property` (21.5) — termwise identification of the two `tsum`s after unfolding `poissonTransitionProb`.

### Corrected statement (was false as originally formalized)

- `linear_ode_solution` (22.9): the original `ExistsUnique x : ℝ → ℝ` is false — the fixed-point equation only constrains `x` on `[0,T]`, so uniqueness as a function on all of `ℝ` never holds. Original preserved (commented); corrected form `linear_ode_solution_unique_on` states uniqueness on the interval `[0,T]` (still `sorry`, blocked on the ODE existence/`gronwall_uniqueness` machinery).

### Recently closed (earlier session)

- `exponential_memoryless` (21.1) — `Real.exp` algebra.
- `flow_chain_rule` (22.4) — chain rule along the flow via
  `HasFDerivAt.comp_hasDerivAt`.
- `deterministic_dynkin` (22.5) — deterministic Dynkin/FTC formula. Two
  minimal, faithful hypotheses were added: `hphi0` (flow initial condition
  `φ(0,·) = id`) and `hXf_int` (interval-integrability of the integrand),
both required for the fundamental theorem of calculus.
- `pdp_generator_no_jumps` / `pdp_generator_pure_jump` (26.18) — the two
  degenerate cases of `pdpGenerator`.
- **`pdp_extended_generator_characterization` (Theorem 26.14, the main §26
  theorem)** — proved in a *faithful reformulated* form. The original
  statement is preserved (commented) but was not faithful: the sample path
  `X` had no hypothesis tying it to `pdp`. The proved version adds, as
  explicit foundational hypotheses, the two genuine sub-results of Davis's
  proof — the deterministic flow decomposition `hdecomp` (§22.4–22.5) and the
  compensated-jump martingale `hjump_mart` (§26.7/§26.12) — plus a localizing
  sequence, and derives the local-martingale characterization. The
  probabilistic content (compensator = local martingale) and the PDMP
  construction remain `sorry` and are entered as `hjump_mart`; see
  `plan_davis_theorem.md`.

### Recently closed (this session — §21.3 / §22.9-22.10 ODE & hazard cluster)

The entire linear-ODE / Gronwall / hazard analysis cluster is now proved from
first principles, using Mathlib's absolute-continuity FTC
(`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`) plus new reusable
infrastructure. All depend only on `propext`, `Classical.choice`, `Quot.sound`.

- `gronwall_uniqueness` (22.9) — `z t = ∫₀ᵗ a·z` with `z` continuous implies
  `z ≡ 0`. Proved by the Picard iterate bound `|z t| ≤ M·F(t)ⁿ/n!` (with
  `F = ∫₀·|a|`) letting `n → ∞`. Supporting helpers:
  `gronwall_abs_primitive_continuousOn` (continuity of the primitive) and
  `gronwall_abs_primitive_substitution` (the FTC substitution
  `∫₀ᵗ |a|·Fⁿ = F(t)ⁿ⁺¹/(n+1)`).
- `linear_ode_variation_of_constants` (22.10) — the variation-of-constants
  formula satisfies the linear integral equation. Proved via AC-FTC on
  `Φ s = exp(A s)·(x₀ + ∫₀ˢ exp(−A)·b)`.
- `linear_ode_solution_unique_on` (22.9, corrected) — existence (variation of
  constants) + uniqueness among continuous solutions (via `gronwall_uniqueness`).
- `survivor_from_hazard` (21.3) — `Ψ(t) = exp(−∫₀ᵗ ψ/Ψ)` from `Ψ(t)=∫_{(t,∞)}ψ`,
  proved by differentiating `log Ψ` (AC-FTC).
- New reusable helpers: `absCont_comp_lipschitzOnWith` (AC composed with a
  function Lipschitz on the range is AC) and `absCont_rexp_comp` (`exp∘AC` is AC).

### Statement corrections (this session)

- `linear_ode_solution_unique_on` and `linear_ode_variation_of_constants` had an
  operator-**precedence** bug: `x₀ + ∫ u in s, a u * x u + ∫ u in s, b u` parses
  with the `∫ b` term nested *inside* the first integral (integral notation
  binds maximally to the right), yielding a false statement (verified). Both are
  now parenthesized as `x₀ + (∫ a·x) + (∫ b)`. Originals preserved (commented).
  Uniqueness was additionally restricted to continuous solutions (the witness is
  continuous), matching Davis's ODE setting; over arbitrary non-measurable `y`
  the Bochner junk-value convention makes the claim ill-posed.

## Notes

This is the most sorry-heavy module in the library, reflecting the depth of Davis's PDP theory. The `PDPStandard` structure bundles non-explosion conditions, filtration properties, and absolute continuity of the jump-time distribution — all needed for the extended generator to be well-defined. The Gronwall uniqueness and ODE comparison results here are also used by `TransientBounds`.
