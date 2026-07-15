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
