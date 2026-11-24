import QuantitativeStochasticHomogenization.AppC.GehringLevelSet
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integration of the level set estimate in the proof of Gehring's lemma

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma C.4: the layer cake formula turns the level set estimate (C.10) into an
inequality between the truncated integrals `Ψ(σ) = ∫_{B_{σR}} f² (|f| ∧ m)^ε`:
`Ψ(σ) ≤ λ₀^ε ∫_{B_{σR}} f² + 8^d (8K)^{2+ε} ε/(2 + ε - q) Ψ(τ) + 8^d (8K)^{2+ε} ∫_{B_{τR}} |g|^{2+ε}`.

As in the standard proofs (and correcting the display after (C.10) in the book, where the
truncation is applied to `‖f_m‖_{L^{2+ε}}` instead of `∫ f² f_m^ε`), the truncated quantity is
weighted by `f²`; the level set integral of `|f|^q` is then bounded through the pointwise
inequality `|f|^q ((8K|f|) ∧ m)^{2+ε-q} ≤ (8K)^{2+ε-q} f² (|f| ∧ m)^ε`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The layer cake formula for a weighted integral over a set:
`∫_B w φ^p = p ∫_0^∞ (∫_{B ∩ {φ > t}} w) t^{p-1} dt`. -/
theorem setLIntegral_mul_ofReal_rpow_eq {B : Set (Vec d)} {w : Vec d → ℝ≥0∞}
    (hw : Measurable w) {φ : Vec d → ℝ} (hφ : Measurable φ) (hφ0 : ∀ x, 0 ≤ φ x) {p : ℝ}
    (hp : 0 < p) :
    ∫⁻ x in B, w x * ENNReal.ofReal (φ x ^ p) =
      ENNReal.ofReal p * ∫⁻ t in Ioi 0, (∫⁻ x in B ∩ {x | t < φ x}, w x) *
        ENNReal.ofReal (t ^ (p - 1)) := by
  have h := lintegral_rpow_eq_lintegral_meas_lt_mul ((volume.restrict B).withDensity w)
    (Eventually.of_forall hφ0) hφ.aemeasurable hp
  have hmeas : Measurable fun x => ENNReal.ofReal (φ x ^ p) :=
    ENNReal.measurable_ofReal.comp (hφ.pow_const p)
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hmeas] at h
  have hset : ∀ t : ℝ, (volume.restrict B).withDensity w {a | t < φ a} =
      ∫⁻ x in B ∩ {x | t < φ x}, w x := by
    intro t
    rw [withDensity_apply _ (measurableSet_lt measurable_const hφ),
      Measure.restrict_restrict (measurableSet_lt measurable_const hφ), inter_comm]
  simp_rw [hset, Pi.mul_apply] at h
  exact h

theorem ofReal_mul_lintegral_Ioc_rpow {ε L : ℝ} (hε : 0 < ε) (hL : 0 ≤ L) :
    ENNReal.ofReal ε * ∫⁻ t in Ioc 0 L, ENNReal.ofReal (t ^ (ε - 1)) = ENNReal.ofReal (L ^ ε) := by
  have hint : IntegrableOn (fun t : ℝ => t ^ (ε - 1)) (Ioc 0 L) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < ε - 1)).1
  rw [← ofReal_integral_eq_lintegral_ofReal hint (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact Real.rpow_nonneg ht.1.le _),
    ← intervalIntegral.integral_of_le hL, integral_rpow (Or.inl (by linarith)), sub_add_cancel,
    Real.zero_rpow hε.ne', sub_zero, ← ENNReal.ofReal_mul hε.le]
  congr 1
  field_simp

theorem measurable_setLIntegral_levelSet {B : Set (Vec d)} {w : Vec d → ℝ≥0∞}
    {φ : Vec d → ℝ} :
    Measurable fun t : ℝ => ∫⁻ x in B ∩ {x | t < φ x}, w x := by
  refine Antitone.measurable fun s t hst => lintegral_mono_set ?_
  intro x ⟨hxB, hx⟩
  exact ⟨hxB, lt_of_le_of_lt hst hx⟩

/-- The pointwise inequality `a^q ((8K a) ∧ m)^{2+ε-q} ≤ (8K)^{2+ε-q} a² (a ∧ m)^ε`. -/
theorem rpow_mul_min_rpow_le {a K m q ε : ℝ} (ha : 0 ≤ a) (hK : 1 ≤ 8 * K) (hm : 0 ≤ m)
    (hq : q < 2) (hε : 0 < ε) :
    a ^ q * min (8 * K * a) m ^ (2 + ε - q) ≤
      (8 * K) ^ (2 + ε - q) * (a ^ (2 : ℝ) * min a m ^ ε) := by
  have hp : 0 < 2 + ε - q := by linarith
  have hmin0 : 0 ≤ min a m := le_min ha hm
  have hminK : min (8 * K * a) m ≤ 8 * K * min a m := by
    rcases le_total a m with ham | ham
    · rw [min_eq_left ham]
      exact min_le_left _ _
    · rw [min_eq_right ham]
      calc min (8 * K * a) m ≤ m := min_le_right _ _
        _ ≤ 8 * K * m := le_mul_of_one_le_left hm hK
  have h1 : min (8 * K * a) m ^ (2 + ε - q) ≤ (8 * K) ^ (2 + ε - q) * min a m ^ (2 + ε - q) := by
    rw [← Real.mul_rpow (by linarith) hmin0]
    exact Real.rpow_le_rpow (le_min (by positivity) hm) hminK hp.le
  have h2 : min a m ^ (2 + ε - q) = min a m ^ (2 - q) * min a m ^ ε := by
    rw [← Real.rpow_add' hmin0 (by linarith)]
    ring_nf
  have h3 : min a m ^ (2 - q) ≤ a ^ (2 - q) :=
    Real.rpow_le_rpow hmin0 (min_le_left _ _) (by linarith)
  have h4 : a ^ q * a ^ (2 - q) = a ^ (2 : ℝ) := by
    rw [← Real.rpow_add' ha (by norm_num)]
    ring_nf
  have hq0 : 0 ≤ a ^ q := Real.rpow_nonneg ha _
  calc a ^ q * min (8 * K * a) m ^ (2 + ε - q)
      ≤ a ^ q * ((8 * K) ^ (2 + ε - q) * min a m ^ (2 + ε - q)) :=
        mul_le_mul_of_nonneg_left h1 hq0
    _ = (8 * K) ^ (2 + ε - q) * (a ^ q * min a m ^ (2 - q) * min a m ^ ε) := by
        rw [h2]; ring
    _ ≤ (8 * K) ^ (2 + ε - q) * (a ^ q * a ^ (2 - q) * min a m ^ ε) := by
        gcongr
    _ = (8 * K) ^ (2 + ε - q) * (a ^ (2 : ℝ) * min a m ^ ε) := by rw [h4]

end QSH
