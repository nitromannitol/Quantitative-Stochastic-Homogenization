import QuantitativeStochasticHomogenization.Ch02.Sec01.Lemma22

/-!
# Lemma 2.12: the additivity defect controls the maximizers on two scales

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.2, Lemma 2.12, (2.32): for a partition `{U₁, …, U_k}` of `U` up to a null set and the
maximizers `v = v(·, U, p, q)` and `vⱼ = v(·, Uⱼ, p, q)` of (2.9),
`Σⱼ |Uⱼ|/|U| ½ ‖a^{1/2}(∇v - ∇vⱼ)‖²_{L̲²(Uⱼ)} = Σⱼ |Uⱼ|/|U| J(Uⱼ, p, q) - J(U, p, q)`
(`lemma_2_12`), with `½ ‖a^{1/2} X‖²_{L̲²(Uⱼ)} = ⨍_{Uⱼ} ½ X·aX`.

The proof is the book's: the quadratic response (2.17) in each `Uⱼ`, tested with the restriction of
`v` (`IsAHarmonic.mono`), summed with the weights `|Uⱼ|/|U|`; the functional of (2.9) is additive
over the partition (`defectTrialEnergy_eq_sum_of_partition`). The book states the lemma for
Lipschitz domains; here `U` is bounded and open and the pieces are open sets, with the maximizers
given (they exist for convex sets, `exists_isDefectMaximizer`).
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- **The functional (2.9) is additive over a partition**:
`⨍_U φ(g) = Σₖ |Qₖ|/|U| ⨍_{Qₖ} φ(g)` for a partition of `U`, up to a null set, by pairwise disjoint
open sets. -/
theorem defectTrialEnergy_eq_sum_of_partition (a : CoefficientField d Λ) {ι : Type*} [Fintype ι]
    {U : Set (Vec d)} (hU : volume U ≠ ⊤) {Q : ι → Set (Vec d)} (hQo : ∀ k, IsOpen (Q k))
    (hdisj : Pairwise (Function.onFun Disjoint Q)) (hsub : ∀ k, Q k ⊆ U)
    (hcover : volume (U \ ⋃ k, Q k) = 0) (p q : Vec d) {g : Vec d → Vec d}
    (hg : MemLp g 2 (volume.restrict U)) :
    defectTrialEnergy a U p q g =
      ∑ k, (volume.real (Q k) / volume.real U) * defectTrialEnergy a (Q k) p q g := by
  have hint := integrable_defectIntegrand a hU p q hg
  have hae : U =ᵐ[volume] ⋃ k, Q k := by
    refine ae_eq_set.mpr ⟨hcover, ?_⟩
    rw [sdiff_eq_empty.mpr (iUnion_subset hsub), measure_empty]
  have hsplit : ∫ x in U, (-(1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x)) -
      dot p ((a x).mulVec (g x)) + dot q (g x)) =
      ∑ k, ∫ x in Q k, (-(1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x)) -
        dot p ((a x).mulVec (g x)) + dot q (g x)) := by
    rw [setIntegral_congr_set hae, integral_iUnion_fintype (fun k => (hQo k).measurableSet) hdisj
      fun k => IntegrableOn.mono_set hint (hsub k)]
  rw [defectTrialEnergy, setAverage_eq, smul_eq_mul, hsplit, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hQ : volume (Q k) ≠ ⊤ := ne_top_of_le_ne_top hU (measure_mono (hsub k))
  rw [defectTrialEnergy, setAverage_eq, smul_eq_mul]
  rcases eq_or_ne (volume (Q k)) 0 with h0 | h0
  · rw [Measure.restrict_eq_zero.mpr h0, integral_zero_measure]
    simp [Measure.real, h0]
  · have hpos : 0 < volume.real (Q k) := ENNReal.toReal_pos h0 hQ
    field_simp

/-- **Lemma 2.12.** For a bounded open set `U`, a partition `Q₁, …, Q_k` of `U`, up to a null set,
by pairwise disjoint open sets, and the maximizers `v = v(·, U, p, q)` (gradient `g`) and
`vⱼ = v(·, Qⱼ, p, q)` (gradients `hⱼ`) of (2.9),
`Σⱼ |Qⱼ|/|U| ⨍_{Qⱼ} ½ (g - hⱼ)·a(g - hⱼ) = Σⱼ |Qⱼ|/|U| J(Qⱼ, p, q) - J(U, p, q)` (2.32). -/
theorem lemma_2_12 (a : CoefficientField d Λ) {ι : Type*} [Fintype ι] {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) {Q : ι → Set (Vec d)} (hQo : ∀ k, IsOpen (Q k))
    (hdisj : Pairwise (Function.onFun Disjoint Q)) (hsub : ∀ k, Q k ⊆ U)
    (hcover : volume (U \ ⋃ k, Q k) = 0) (p q : Vec d) {v : Vec d → ℝ} {g : Vec d → Vec d}
    (hv : IsDefectMaximizer a U p q v g) {w : ι → Vec d → ℝ} {h : ι → Vec d → Vec d}
    (hw : ∀ k, IsDefectMaximizer a (Q k) p q (w k) (h k)) :
    ∑ k, (volume.real (Q k) / volume.real U) *
        ⨍ x in Q k, (1 / 2 : ℝ) * dot (g x - h k x) ((a x).mulVec (g x - h k x)) =
      ∑ k, (volume.real (Q k) / volume.real U) * dualityDefect a (Q k) p q -
        dualityDefect a U p q := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  rw [← hv.2, defectTrialEnergy_eq_sum_of_partition a hU hQo hdisj hsub hcover p q hv.1.1.2.1,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases eq_or_ne (volume (Q k)) 0 with h0 | h0
  · simp [Measure.real, h0]
  · rw [(hw k).setAverage_sub_eq (hUb.subset (hsub k)) h0 (hv.1.mono (hsub k))]
    ring

end QSH
