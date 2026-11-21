import QuantitativeStochasticHomogenization.Front.Assumptions
import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.CoefficientSigma
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel
import QuantitativeStochasticHomogenization.Ch03.Sec04.WeakDivergenceZero
import QuantitativeStochasticHomogenization.Ch04.Sec01.QuadraticEntryBounds

/-!
# Square integrability of coefficient entries

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Environment/AKMReconstructionAgreement.lean`.

The entries of a coefficient field satisfying (0.6) are square integrable on compact sets.
-/

open MeasureTheory

noncomputable section

namespace QSH

/-- The normalized ellipticity hypotheses bound every raw matrix entry
in local L²; spatial measurability follows from local integrability. -/
theorem coefficient_entry_memLp_on_compact {d : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (a : CoefficientField d K) (i j : Fin d) (S : Set (Vec d)) (hS : IsCompact S) :
    MemLp (fun x => a.field x i j) 2 (volume.restrict S) := by
  let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS.measure_ne_top
  apply MemLp.of_bound (a.locally_integrable i j).aestronglyMeasurable.restrict K
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs]
    have hn (ξ : Vec d) : 0 ≤ euclideanSq ξ := by
      unfold euclideanSq dot
      exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
    exact abs_entry_le_of_quadratic_bounds hK (a.field x) (a.symmetric x)
      (fun ξ => (hn ξ).trans (a.elliptic x ξ).1) (fun ξ => (a.elliptic x ξ).2) i j

end QSH
