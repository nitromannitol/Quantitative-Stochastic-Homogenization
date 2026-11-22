import QuantitativeStochasticHomogenization.AppA.OsNotation

/-!
# Stretched-exponential moments from tail bounds

Moved from einstein-relation-lean c97689e `EinsteinFull/Homogenization/StretchedExponentialTail.lean`.

The two results of the source file, `lintegral_ofReal_exp_le_two_of_tail` and `osBound_of_tail`
(if `P[X ≥ t A] ≤ exp(-t^q)` for every `t ≥ 1` and `0 < s ≤ q`, then `X ≤ O_s(8^(1/s) A)`,
Appendix A, (A.1)), are stated and proved in `QuantitativeStochasticHomogenization.AppA.OsNotation`,
which this module imports.
-/
