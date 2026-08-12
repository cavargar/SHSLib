-- SHSLib v2: Formal library for Stochastic Hybrid Systems
--
-- Public mirror of the research repository: the general stochastic-modeling theory
-- layers only -- Core/, Foundations/, Gardiner/, Ullah/, FPK/ and Bujorianu2006/.
-- Their import closure never reaches an Examples/, Applications/, MomentAnalysis/
-- or Tactics/ module, which is what makes this subset self-contained; the
-- domain-specific models and the tactic front-end stay in the research repository.

import SHSLib.Core.Basic       -- SHS structure, assumptions, flow (Section 2)
import SHSLib.Core.Generator   -- Extended generator, Theorems 1–2, Lemmas 1–2,
import SHSLib.Core.GronwallGrowthBound -- Grönwall with time-varying rate; Lemma 1 / Eq. (35)
import SHSLib.Foundations.DavisCh1  -- Ch1: Analysis, Probability, Stochastic Processes
import SHSLib.Foundations.DavisCh2  -- Ch2: Piecewise-Deterministic Markov Processes
import SHSLib.Foundations.DavisCh2FiniteKernel          -- Finite-kernel PDP transition operator
import SHSLib.Foundations.DavisCh2FiniteKernelSemigroup -- Finite-kernel semigroup properties
import SHSLib.Foundations.DavisCh2FiniteProcess         -- Finite-activity PDP process construction
import SHSLib.Core.GeneratorDefs      -- Shared TestFunction / extendedGenerator defs (breaks import cycle)
import SHSLib.Core.DavisBridge        -- Bridge: SHS instance ↦ Davis PDP
import SHSLib.Core.DavisConstruction  -- Concrete Davis process construction for an SHS
import SHSLib.Core.DavisMartingale    -- Compensated-generator martingale for the constructed process
import SHSLib.Core.DavisNaturalStopping -- Observable jump-time localization
import SHSLib.Core.DavisObservableCounter -- Mode-level observable jump counters
import SHSLib.Core.DavisCounterAugmentation -- Canonical counter-augmented models
import SHSLib.Core.DavisPreJumpHistory -- Finite histories and their discrete filtration
import SHSLib.Core.DavisHazardLaw -- Integrated hazards and conditional holding-time laws
import SHSLib.Core.DavisChannelLaw -- Pre-channel information and normalized channel laws
import SHSLib.Core.DavisOneStepLaw -- Joint one-step law and reset-compensator algebra
import SHSLib.Core.DavisFiniteCompensator -- Finite centered reset sums and bounds
import SHSLib.Core.DavisFiniteCompensatorMeasurable -- Measurability for finite centered reset sums
import SHSLib.Core.DavisFiniteCompensatorBounds -- Uniform bounds and integrability of finite reset sums
import SHSLib.Core.DavisConditionalChannelIntegral -- Finite channel-test integral bridge
import SHSLib.Core.DavisConditionalChannelExpectation -- Conditional expectations of finite channel tests
import SHSLib.Core.DavisConditionalResetExpectation -- Conditional mean-zero centered reset increments
import SHSLib.Core.DavisFiniteResetMartingale -- Discrete martingale of finite centered reset sums
import SHSLib.Core.DavisStoppedResetSum -- Elapsed-time reset sums with bounded jump localization
import SHSLib.Core.DavisElapsedResetSum -- Full elapsed-time reset sums via integrable jump counts
import SHSLib.Core.DavisResetDecomposition -- Pathwise reset/flow telescoping identities
import SHSLib.Core.DavisSegmentCompensator -- Segmentwise flow/reset compensator decomposition
import SHSLib.Core.DavisHazardDensity -- Holding-time hazard-density calculus
import SHSLib.Core.DavisConditionalHoldingIntegral -- Conditional threshold-step holding-time integration
import SHSLib.Core.DavisConditionalHoldingMonotone -- Monotone limits of holding-time threshold tests
import SHSLib.Core.DavisOneSegmentResetCompensation -- One-segment reset-density algebra and bounds
import SHSLib.Core.DavisResetCompensatorBounds -- Integrated and finite-cap reset-compensator bounds
import SHSLib.Core.DavisConditionalHoldingApproximation -- Reusable monotone holding-time approximation interface
import SHSLib.Core.DavisResetOccupationBridge -- Raw occupied-time reset density and survivor bridge
import SHSLib.Core.DavisConditionalHoldingSignedStep -- Signed finite holding-time threshold integration
import SHSLib.Core.DavisConditionalHoldingSignedApproximation -- Signed approximation limits for holding-time integrals
import SHSLib.Core.DavisResetOccupationRegular -- Regularity interface for reset occupation along segments
import SHSLib.Core.DavisHoldingThresholdData -- Packaged monotone holding-time approximation data
import SHSLib.Core.DavisHoldingSignedThresholdData -- Packaged signed holding-time approximation data
import SHSLib.Core.DavisResetOccupationConditional -- Conditional capped reset occupation identity
import SHSLib.Core.DavisConditionalHoldingHistoryStep -- Holding thresholds localized by pre-jump history
import SHSLib.Core.DavisHoldingHistoryThresholdData -- Monotone history-localized threshold data
import SHSLib.Core.DavisHoldingSignedHistoryThresholdData -- Signed history-localized threshold data
import SHSLib.Core.DavisResetOccupationConditionalHistory -- History-dependent capped occupation identity
import SHSLib.Core.DavisHoldingHistoryRectangularApproximation -- Rectangular history/time occupation approximations
import SHSLib.Core.DavisResetOccupationIntegrable -- Integrability bounds for capped reset occupation
import SHSLib.Core.DavisResetOccupationRectangular -- Conditional occupation from rectangular variation data
import SHSLib.Core.DavisFiniteResetOccupation -- Finite sums of capped reset occupations
import SHSLib.Core.DavisFiniteResetOccupationBridge -- Full-segment occupation and centered decomposition
import SHSLib.Core.DavisElapsedResetOccupation -- Fixed-time occupied reset compensator
import SHSLib.Core.DavisFiniteOccupationCentered -- Finite capped occupation-centered reset sums
import SHSLib.Core.DavisFiniteOccupationCapRemoval -- Removing finite duration caps
import SHSLib.Core.DavisFiniteOccupationEnvelope -- Integrable envelopes for capped occupation sums
import SHSLib.Core.DavisFiniteOccupationL1CapRemoval -- Finite L1 duration-cap removal
import SHSLib.Core.DavisNaturalDurationCaps -- Concrete natural-number duration caps
import SHSLib.Core.DavisStoppedElapsedOccupation -- Jump-capped elapsed occupation sums
import SHSLib.Core.DavisStoppedElapsedOccupationMeasurable -- Measurability of stopped elapsed occupation
import SHSLib.Core.DavisStoppedElapsedOccupationEnvelope -- Common stopped elapsed occupation envelope
import SHSLib.Core.DavisElapsedOccupationCentering -- Full fixed-time occupation centering
import SHSLib.Core.DavisElapsedOccupationEnvelopeIntegrable -- Concrete elapsed envelope integrability
import SHSLib.Core.DavisElapsedOccupationEnvelopeMeasurable -- Measurability of the full elapsed envelope
import SHSLib.Core.DavisElapsedOccupationEventCentering -- Event-localized elapsed occupation centering
import SHSLib.Core.DavisElapsedOccupationIncrement -- Fixed-time increments of elapsed occupation centering
import SHSLib.Core.DavisElapsedOccupationIncrementCentering -- Event-centered fixed-time increments
import SHSLib.Core.DavisAgeClockModel -- Age-dependent clocks
import SHSLib.Core.DavisAgeClockTestFunction -- Test functions of the age for an age clock
import SHSLib.Core.DavisAgeCounterAgeTest -- Test functions of the age on the multi-channel age–counter clock
import SHSLib.Core.DavisAgeCounterJointTest -- Joint test functions of the age and the counter
import SHSLib.Core.DavisAgeCounterMixedTest -- Test functions of the age and the counter together
import SHSLib.Core.DavisAgeCounterModel -- An age clock with several reset channels
import SHSLib.Core.DavisBoundedHazardVacuity -- A uniformly bounded accumulated hazard forces the zero measure
import SHSLib.Core.DavisConditionalChannelWeighted -- The weighted channel identity and the conditional mean of a reset
import SHSLib.Core.DavisConditionalHoldingDensity -- The density form of the conditional holding-time law
import SHSLib.Core.DavisConditionalHoldingDensityRandomWindow -- The density law at a history-measurable window length
import SHSLib.Core.DavisConditionalHoldingRandomThreshold -- The conditional holding-time law at a history-measurable threshold
import SHSLib.Core.DavisConditionalHoldingWeighted -- The weighted survivor identity
import SHSLib.Core.DavisConditionalHoldingWindow -- The window law of the holding time
import SHSLib.Core.DavisCoordinateNoise -- Independent holding times from the coordinates of a product measure
import SHSLib.Core.DavisElapsedAccumulatedHazardMeasurable -- Measurability of the accumulated hazard
import SHSLib.Core.DavisElapsedBoundedRegime -- The bounded regime: uniform envelopes with no extra probabilistic input
import SHSLib.Core.DavisElapsedGeneratorMartingale -- Generator bridge for the elapsed occupation martingale
import SHSLib.Core.DavisElapsedOccupationCappedMartingale -- The deterministic-cap increment law as a capped martingale property
import SHSLib.Core.DavisElapsedOccupationConditionalIncrement -- Conditional cap removal for elapsed occupation increments
import SHSLib.Core.DavisElapsedOccupationCurrentStateInstances -- Instances of current-state observability
import SHSLib.Core.DavisElapsedOccupationEnvelopeCriterion -- Envelope integrability from bounded tests, and fully concrete martingales
import SHSLib.Core.DavisElapsedOccupationFullObservability -- Discharging observability for the full-information filtration
import SHSLib.Core.DavisElapsedOccupationMartingale -- Martingale packaging for the elapsed occupation-centered reset process
import SHSLib.Core.DavisElapsedOccupationMinimalFiltration -- The minimal observability filtration
import SHSLib.Core.DavisElapsedOccupationObservability -- Filtration-level observability of elapsed reset occupation
import SHSLib.Core.DavisElapsedOccupationPathFiltration -- Observability for the natural state-path filtration
import SHSLib.Core.DavisElapsedOccupationProcessIntegrable -- Integrability constructors for the elapsed occupation process
import SHSLib.Core.DavisElapsedOccupationProcessMeasurable -- Measurability and full-filtration adaptedness
import SHSLib.Core.DavisElapsedOccupationSegmentwise -- Segmentwise decomposition of the capped martingale property
import SHSLib.Core.DavisElapsedPathwiseProducts -- Discharging the product hypotheses of the path-level regime
import SHSLib.Core.DavisElapsedPathwiseSquareIntegrability -- Square integrability of the path-level quantities
import SHSLib.Core.DavisElapsedPathwiseTestBound -- Path-level bounds on the test function
import SHSLib.Core.DavisElapsedRelaxedRegime -- The relaxed regime: random path-level envelopes
import SHSLib.Core.DavisElapsedSquareIntegrableInstances -- Model classes satisfying the square-integrability conditions
import SHSLib.Core.DavisHoldingDensityHorizon -- The density form of the holding-time law below an age horizon
import SHSLib.Core.DavisMarkedCoordinateNoise -- Independent holding times *and* marks from the coordinates of a product
import SHSLib.Core.DavisMarkedJumpAdapted -- Observability of a segment contribution, and the step law in full
import SHSLib.Core.DavisMarkedJumpBoundedIntensity -- The model-level statements under a bounded intensity
import SHSLib.Core.DavisMarkedJumpFiltration -- The observation filtration of the marked jump history
import SHSLib.Core.DavisMarkedJumpGeneratorMartingale -- The generator martingale for the marked jump filtration
import SHSLib.Core.DavisMarkedJumpHorizonStepLaw -- The conditional step law under a horizon-dependent profile bound
import SHSLib.Core.DavisMarkedJumpObservable -- Observability of the elapsed occupation for the marked jump filtration
import SHSLib.Core.DavisMarkedJumpRelaxedRegime -- The model-level statements with a random lower bound on the holding times
import SHSLib.Core.DavisMarkedJumpSegmentMartingale -- The conditional step law, the one-segment martingale, and the increment
import SHSLib.Core.DavisMarkedJumpStepLaw -- The conditional step law for the marked jump filtration
import SHSLib.Core.DavisNoiseBlockMeasurable -- Histories are measurable for any σ-algebra carrying the noise used so far
import SHSLib.Core.DavisNonExplosiveLowerBound -- Non-explosion from a deterministic dead time
import SHSLib.Core.DavisOccupationRegularCriterion -- A criterion for the regularity of the reset occupation
import SHSLib.Core.DavisOneSegmentConditionalStep -- The conditional step of the one-segment martingale
import SHSLib.Core.DavisOneSegmentTruncatedCompensation -- Truncated one-segment reset compensation
import SHSLib.Core.DavisPoissonClockModel -- A concrete Davis model: the constant-rate clock
import SHSLib.Core.DavisPoissonClockNoise -- A concrete noise satisfying the conditional laws
import SHSLib.Core.DavisProfileLinearGrowth -- Linear growth of the centered reset profile in the age
import SHSLib.Core.DavisProfileTruncation -- Truncating a profile at an age horizon
import SHSLib.Core.DavisProfileTruncationCore -- Truncating a profile at an age horizon: the core transfer
import SHSLib.Core.DavisRampedClockMartingale -- The Dynkin identity and the martingale property on a concrete model
import SHSLib.Core.DavisRampedClockModel -- The ramped refractory clock
import SHSLib.Core.DavisRampedClockNoise -- The noise of the ramped refractory clock
import SHSLib.Core.DavisRefractoryClockModel -- A concrete refractory Davis model
import SHSLib.Core.DavisRefractoryClockNoise -- A refractory instance with holding times bounded below
import SHSLib.Core.DavisRefractoryHazard -- What a lower bound on the holding times costs
import SHSLib.Core.DavisSegmentActiveConditional -- The conditional law of the active part
import SHSLib.Core.DavisSegmentCompletedConditional -- The conditional law of the completed part
import SHSLib.Core.DavisSegmentConditionalRandomWindow -- The two segment laws at a history-measurable start age
import SHSLib.Core.DavisSegmentFreshCentering -- Centering of a segment observed from its start
import SHSLib.Core.DavisSegmentHazardRiemann -- Riemann approximation of a hazard average over an age window
import SHSLib.Core.DavisSegmentProfileRegularity -- Instances of the centered reset profile regularity
import SHSLib.Core.DavisStoppedElapsedOccupationIncrement -- Deterministic-cap increments of elapsed reset occupation
import SHSLib.Core.DavisStoppedElapsedOccupationIncrementLaw -- Conditional law interface for stopped elapsed occupation increments
import SHSLib.Core.DavisTwoChannelAgeTest -- An age test function on the two-channel refractory clock
import SHSLib.Core.DavisTwoChannelCharacteristic -- The characteristic family on the two-channel refractory clock
import SHSLib.Core.DavisTwoChannelClock -- A two-channel refractory clock, and its Dynkin identity
import SHSLib.Core.DavisTwoChannelJointCharacteristic -- The joint characteristic family on the two-channel refractory clock
import SHSLib.Core.DavisTwoChannelJointTest -- A joint test function on the two-channel refractory clock
import SHSLib.Core.DavisTwoChannelMixedTest -- A mixed test function on the two-channel refractory clock
import SHSLib.Foundations.BetaBinomial -- The `i`-th term of the binomial upper tail, with `n = j+m+1`
import SHSLib.Foundations.BetaBinomialMeasure -- The upper-tail event `{i ≥ j+1}` among the `n+1` possible counts of successes in `n` Bernoulli 
import SHSLib.Foundations.BetaConcentration -- The deviation set of the Beta law is measurable
import SHSLib.Foundations.BetaDistribution -- The **Beta density** with shape parameters `a, b`: `betaPDF a b t = t^{a−1}(1−t)^{b−1}/B(a,b)`.
import SHSLib.Foundations.BetaExpectation -- The real-valued form of the Beta density: the truncation of `betaPDF` to `(0,1)`
import SHSLib.Foundations.BetaInverseTransform -- Outside `[0,1]` the quantile takes its junk value `0`
import SHSLib.Foundations.BetaMeasure -- The Beta density as an `ℝ≥0∞`-valued function, supported on `(0,1)`
import SHSLib.Foundations.BetaPowerLaw -- The distribution function of `Beta(a,1)` and `Beta(1,b)`
import SHSLib.Foundations.BetaQuantile -- The Euler integrand is continuous at every interior point of `(0,1)`
import SHSLib.Foundations.BetaQuantileContinuity -- **The Beta quantile is continuous on `[0,1]`.** The CDF is a continuous bijection from the comp
import SHSLib.Foundations.BetaQuantileFunction -- The **Beta quantile function**: the inverse of the Beta CDF. For `p ∈ [0,1]` and `a, b > 0` it 
import SHSLib.Foundations.BetaRecurrence -- The antiderivative `F(t) = t^a (1−t)^b` used in the recurrence
import SHSLib.Foundations.BetaVariance -- The Beta law gives no mass to the complement of `(0,1)`
import SHSLib.Foundations.ClopperPearson -- Monotonicity of the Beta CDF in its parameters
import SHSLib.Foundations.ClopperPearsonCoverage -- The mirror of the quantile/CDF adjunction
import SHSLib.Foundations.ClopperPearsonMonotone -- **Moving one unit from the second parameter to the first increases the quantile.** Equivalently
import SHSLib.Foundations.Digamma -- Termwise differentiation of the digamma series
import SHSLib.Foundations.DigammaAsymptotics -- The mean value estimate
import SHSLib.Foundations.DigammaEuler -- The value `ψ(1) = −γ`
import SHSLib.Foundations.DigammaReflection -- The reflection formula for `ψ`
import SHSLib.Foundations.DigammaSharpBound -- An elementary logarithmic inequality
import SHSLib.Foundations.IncompleteBeta -- The Euler integrand `t^{a−1}(1−t)^{b−1}` of the Beta integral
import SHSLib.Foundations.OrderStatisticTransform -- Sorting commutes with a monotone map
import SHSLib.Foundations.Polygamma -- Summability of the shifted `m`-th power series
import SHSLib.Foundations.PolygammaAsymptotics -- Bracketing the trigamma function
import SHSLib.Foundations.StirlingBeta -- The real Beta function `B(x,y) = Γ(x)Γ(y)/Γ(x+y)`
import SHSLib.Foundations.StirlingBetaAsymptotics -- The Stirling main term for `log B(x,y)`
import SHSLib.Foundations.StirlingBetaIntegral -- Mathlib's complex Beta integral at real arguments is the coercion of the real interval integral
import SHSLib.Foundations.StirlingBetaReflection -- **Euler's reflection formula in Beta form**: `B(x, 1−x) = π/sin(πx)`
import SHSLib.Foundations.StirlingBinet -- The Binet auxiliary function
import SHSLib.Foundations.StirlingBinetSecond -- The second-order Binet auxiliary function
import SHSLib.Foundations.StirlingBinetThird -- The third-order Binet auxiliary function
import SHSLib.Foundations.StirlingBounds -- The two-sided bound on the Stirling defect
import SHSLib.Foundations.StirlingCatalan -- Catalan numbers
import SHSLib.Foundations.StirlingCentralBinom -- The logarithm of the central binomial coefficient
import SHSLib.Foundations.StirlingConstant -- **Stirling's formula for `log Γ`**: the Stirling defect tends to `½ log (2π)`
import SHSLib.Foundations.StirlingGautschi -- **Gautschi's inequality**: `x^{1−s} ≤ Γ(x+1)/Γ(x+s) ≤ (x+s)^{1−s}` for `x > 0` and `0 < s < 1`
import SHSLib.Foundations.StirlingHalfInteger -- The closed form at half-integers
import SHSLib.Foundations.StirlingLogGamma -- A quadratic lower bound for the logarithm
import SHSLib.Foundations.StirlingPi -- **Explicit two-sided approximation of `π`** by the central binomial coefficient: for `n ≥ 1`, `
import SHSLib.Foundations.StirlingShift -- The exact decomposition of the shifted log-Gamma difference
import SHSLib.Foundations.StirlingShiftRatio -- The logarithm of the shifted Gamma ratio is exactly the quantity bounded in batch 165
import SHSLib.Foundations.StirlingWallis -- The central binomial bracket to fifth order
import SHSLib.Foundations.Tetragamma -- The tetragamma function `ψ'' = (log Γ)'''
import SHSLib.Foundations.TetragammaReflection -- **Reflection formula at third order**: for `x ∈ (0,1)`, `ψ''(x) − ψ''(1−x) = −2π³ cos(π x)/sin(
import SHSLib.Foundations.Trigamma -- Smoothness of `Γ` and of `log Γ` on the positive half-line
import SHSLib.Foundations.TrigammaSeries -- Regularity, the recurrence and the duplication formula, restated
import SHSLib.Foundations.TrigammaSharpBracket -- The two limits
import SHSLib.Foundations.UniformOrderStatistic -- The uniform law and its product
import SHSLib.Foundations.UniformOrderStatisticLaw -- One-dimensional marginals of the product measure
import SHSLib.Foundations.UniformOrderStatisticMoments -- The `(j+1)`-st order statistic of a sample of `n = j+m+1` uniforms, as a random variable on the
import SHSLib.Foundations.DavisCh2StrongMarkov -- Strong Markov property under countable-range stopping times

-- Flow existence and regularity; Beta order statistics
import SHSLib.Core.DavisModeBlind -- Theorem 1 for systems whose resets only move the discrete mode
import SHSLib.Core.DavisTransitionFree -- The transition-free SHS as a Davis process: Theorem 1 without assumptions
import SHSLib.Core.EnvelopeIntensityBounds -- Discharging the hypotheses of Lemma 2 from a growth envelope
import SHSLib.Core.EnvelopeSharpness -- Sharpness of the linear-growth envelope
import SHSLib.Core.ExplicitFlows -- Explicit flows for the two simplest drifts
import SHSLib.Core.FlowDynkin -- The deterministic Dynkin identity along the SHS flow
import SHSLib.Core.FlowInitialStateDependence -- Dependence of the flow on the initial state
import SHSLib.Core.FlowRegularity -- Regularity of the flow of an SHS with a Lipschitz drift
import SHSLib.Core.FlowRegularityLinearGrowth -- Regularity of the flow for drifts that are only locally Lipschitz
import SHSLib.Core.GlobalFlowExistence -- Global existence of the flow of an SHS with a Lipschitz drift
import SHSLib.Core.GlobalFlowLinearGrowth -- Global existence of the flow under local Lipschitz continuity and linear growth
import SHSLib.Core.GlobalFlowVaryingGrowth -- Global flow under a linear growth condition with time-varying coefficients
import SHSLib.Core.LinearGrowthCriteria -- Convenient criteria for the hypotheses of the linear-growth existence theorem
import SHSLib.Foundations.BetaOrderStatisticConcentration -- Concentration of an order statistic of a Beta sample
import SHSLib.Foundations.BetaOrderStatisticGeneralLipschitz -- The variance of an order statistic under a Lipschitz parent quantile
import SHSLib.Foundations.BetaOrderStatisticInteger -- Order statistics of a sample of powers of uniforms
import SHSLib.Foundations.BetaOrderStatisticLipschitz -- A variance bound and localization for the sample quantile of powers of uniforms
import SHSLib.Foundations.BetaOrderStatisticMoments -- Moments of an order statistic of a Beta sample
import SHSLib.Foundations.BetaOrderStatisticMomentsPower -- Moments of an order statistic of a power-law (`Beta(a,1)`) sample
import SHSLib.Foundations.DavisCh2ProcessLinks -- Process-level links for Davis Chapter 2

-- Gardiner, Handbook of Stochastic Methods: the differential Chapman-Kolmogorov equation
import SHSLib.Gardiner.Backward -- Backward differential Chapman-Kolmogorov equation
import SHSLib.Gardiner.Basic -- State space R^n, partial derivatives, Taylor remainder, conditions (i)-(iii)
import SHSLib.Gardiner.HigherMoments -- Vanishing of third and higher conditional moments
import SHSLib.Gardiner.Special -- Master equation, Fokker-Planck, Liouville; Gaussian solution
import SHSLib.Gardiner.Strong -- Integration by parts (3.4.19) and the strong form (3.4.22)
import SHSLib.Gardiner.Taylor -- Uniform second-order Taylor estimate (3.4.11)
import SHSLib.Gardiner.WeakForm -- Weak form of the dCKE (3.4.16) against test functions
import SHSLib.Gardiner -- Index + (3.4.x)/(3.5.x) correspondence table

-- Ullah & Wolkenhauer, Stochastic Approaches for Systems Biology, section 8.2
import SHSLib.Ullah.Basic -- Time difference quotient (8.4), gain-loss flux (8.5), splitting (8.6)
import SHSLib.Ullah.DCKE -- The dCKE (8.13), derived from the density without integration by parts
import SHSLib.Ullah.Limits -- Limits (8.11) and (8.12) of the near and far regions
import SHSLib.Ullah.Near -- Near region: change of variables (8.7), Taylor expansion, conditional moments
import SHSLib.Ullah -- Index + (8.x) correspondence table

-- Bect (2010): the unifying Fokker-Planck-Kolmogorov equation for general SHS
import SHSLib.FPK.AdjointUniqueness -- Eq. (15) and Definition 7(d) of Bect (2010): the adjoint `L*μ` and the FPK equation
import SHSLib.FPK.AppendixB42 -- Appendix B of Bect (2010): Eqs. (42) and (43)
import SHSLib.FPK.AppendixC1 -- Appendix C.1 of Bect (2010): Eqs. (46) and (47), the computation of `L*μ_t`
import SHSLib.FPK.AppendixC1Box -- Appendix C.1 of Bect (2010) on a box: Eq. (46) proved from the divergence theorem
import SHSLib.FPK.AppendixC1BoxExample -- A worked instance of Eq. (46) on a box
import SHSLib.FPK.AppendixE -- Appendix E of Bect (2010): proof of Theorem 13
import SHSLib.FPK.BoundaryGeometry -- Section 5.1 of Bect (2010): the surface measure and the boundary conditions (19)
import SHSLib.FPK.DensityEvolution -- Section 5.3 and Appendix D of Bect (2010): from measures to densities
import SHSLib.FPK.DiffusionGenerator -- Eq. (4) and Eq. (16) of Bect (2010): the differential generator and the probability
import SHSLib.FPK.DivergenceTheorem -- Appendix A of Bect (2010): the divergence theorem
import SHSLib.FPK.DualKernelMeasure -- Eq. (24) of Bect (2010): Assumption 14 as an equality of measures on `E × E`
import SHSLib.FPK.DynkinFormula -- From the generalized Itô formula to the generalized Dynkin formula (Section 4.1)
import SHSLib.FPK.ForcedJumps -- Section 6.2 of Bect (2010): a class of models with forced jumps
import SHSLib.FPK.GeneralizedFPK -- The generalized Fokker–Planck–Kolmogorov equation (Section 4 of Bect, 2010)
import SHSLib.FPK.HespanhaBridge -- The Hespanha SHS as a GSHS with spontaneous jumps (Example 18 of Bect, 2010)
import SHSLib.FPK.HespanhaDynkin -- Eq. (12) for a concrete stochastic hybrid system
import SHSLib.FPK.HespanhaFPK -- Example 18 of Bect (2010): Hespanha's generalized FPK equation, Eq. (33)
import SHSLib.FPK.HespanhaResetJacobian -- Example 18 of Bect (2010): deterministic reset maps and their Jacobians
import SHSLib.FPK.HespanhaResetKernel -- The reset kernel of a Hespanha SHS as a Markov kernel
import SHSLib.FPK.HybridStateSpace -- Section 2.1 and Appendix A of Bect (2010): the hybrid state space
import SHSLib.FPK.JumpDiscontinuity -- Section 6.2 of Bect (2010): the jump discontinuity of the density across `H`
import SHSLib.FPK.LevySystemIntensity -- Eq. (8) from the Lévy system: the mean jump intensity of spontaneous jumps
import SHSLib.FPK.LevySystemProcess -- Eqs. (6) and (7) of Bect (2010): the Lévy-system process `H` and the jump measure `R`
import SHSLib.FPK.MarkovChain -- Purely discrete modes: the forward Kolmogorov equation
import SHSLib.FPK.MasterEquation -- Example 16 of Bect (2010): the master equation
import SHSLib.FPK.MeanJumpIntensity -- Mean jump intensity of a general stochastic hybrid system
import SHSLib.FPK.PathwiseIto -- Eq. (3) of Bect (2010): the pathwise content of the generalized Itô formula
import SHSLib.FPK.ProbabilityCurrent -- Section 4.2 and Appendix C of Bect (2010): the probability current
import SHSLib.FPK.ProbabilityFlow -- Section 4.2 of Bect (2010): the "physical" interpretation of the jump term
import SHSLib.FPK.SawtoothExample -- Section 3.2 of Bect (2010): where the initial law comes into play
import SHSLib.FPK.SawtoothSolution -- The sawtooth process with uniform initial law solves the generalized FPK equation
import SHSLib.FPK.SpontaneousJumps -- Section 6.1 of Bect (2010): models with spontaneous jumps only
import SHSLib.FPK.SwitchingDiffusions -- Example 17 of Bect (2010): switching diffusions
import SHSLib.FPK.TotalVariationBounds -- Appendix B of Bect (2010): the total-variation bounds (39) and (41)
import SHSLib.FPK.TwoStateChain -- A concrete solution of the generalized FPK equation: the symmetric two-state chain
import SHSLib.FPK -- Index + Bect equation/definition correspondence table

-- Bujorianu & Lygeros (2006): general stochastic hybrid systems
import SHSLib.Bujorianu2006.GSHSProperties -- Properties of GSHS: executions, sojourn times and the renewal kernel
import SHSLib.Bujorianu2006.Generator -- The extended generator of a General Stochastic Hybrid System
import SHSLib.Bujorianu2006.HybridSpace -- The hybrid state space of a General Stochastic Hybrid System
import SHSLib.Bujorianu2006.JumpMeasure -- The jump counting measures `p`, `p*` of a Markov string
import SHSLib.Bujorianu2006.MarkovString -- Markov strings: jump times, translations, càdlàg paths, Markov property
import SHSLib.Bujorianu2006.Martingale -- The strong generator and Dynkin's formula
import SHSLib.Bujorianu2006.Resolvent -- Semigroup, resolvent and `p`-excessive functions
import SHSLib.Bujorianu2006.TerminalTimes -- Additive and multiplicative functionals, terminal times
