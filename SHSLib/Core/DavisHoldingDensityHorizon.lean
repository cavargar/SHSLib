import SHSLib.Core.DavisProfileTruncationCore

/-! # The density form of the holding-time law below an age horizon

The two horizon-localized forms of the density identity — for a deterministic
window length and for a history-measurable one — were originally stated here.
They are consumed by the conditional law of the completed part, which sits
below this module in the import order, so they have been moved upstream, to
`SHSLib.Core.DavisProfileTruncationCore`, together with the truncation
machinery they rest on.  This module is kept as a pointer and re-exports them.

* `SHS.DavisJumpNoise.ConditionalHoldingTimeLaw.setIntegral_holdingTime_density_of_age_le`
* `SHS.DavisJumpNoise.ConditionalHoldingTimeLaw.setIntegral_holdingTime_density_randomWindow_of_age_le`
-/
