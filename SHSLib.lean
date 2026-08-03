-- SHSLib v2: Formal library for Stochastic Hybrid Systems (Core)
import SHSLib.Core.Basic       -- SHS structure, assumptions, flow
import SHSLib.Core.Generator   -- Extended generator and Fokker–Planck equation
import SHSLib.Foundations.DavisCh1  -- Analysis, Probability, Stochastic Processes
import SHSLib.Foundations.DavisCh2  -- Piecewise-Deterministic Markov Processes
import SHSLib.Foundations.DavisCh2FiniteKernel          -- Finite-state PDP transition kernel
import SHSLib.Foundations.DavisCh2FiniteKernelSemigroup -- Finite-state kernel semigroup laws
import SHSLib.Foundations.DavisCh2FiniteProcess         -- Finite-state (strong) Markov property

-- Davis-to-SHS generator bridge (connects Davis PDMP foundations to the Hespanha Core)
import SHSLib.Core.GeneratorDefs      -- Shared TestFunction / extendedGenerator defs
import SHSLib.Core.DavisBridge        -- SHS ↦ Davis PDP: PDP generator = extended generator
import SHSLib.Core.DavisConstruction  -- Concrete time-augmented Davis PDP of an SHS
import SHSLib.Core.DavisMartingale    -- Compensated-generator martingale; Hespanha Theorem 2

-- Davis reset-compensation / occupation-martingale development
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
