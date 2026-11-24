import QuantitativeStochasticHomogenization.Ch02.Sec01.DualEnergy

/-!
# Measurability of `μ*(U, q)`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.1: the dual quantity `μ*(U, q)` of (2.1) is a measurable function of the coefficient
field (`measurable_dualEnergy`), as for the Dirichlet energy (`measurable_dirichletEnergy`), for the
σ-algebra F of (0.8); the F(U)-measurability, the analogue of (1.29), is not proved here. It is the supremum of the
functional of (2.1) over a countable set of fields of `L²(U)` that does not depend on the
coefficient field (`exists_countable_dualEnergy_eq_iSup`): a countable dense subset of the
gradients of `H¹(U)`, along which the functional is continuous, uniformly in the coefficient field.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- The functional of (2.1) at an element `F` of `L²(U)`. -/
def lpDualTrialEnergy (a : CoefficientField d Λ) (U : Set (Vec d)) (q : Vec d)
    (F : Lp (Vec d) 2 (volume.restrict U)) : ℝ :=
  -lpTrialEnergy a U 0 F + ⨍ x in U, dot q (F x) ∂volume

/-- The gradients of the functions of `H¹(U)`, as elements of `L²(U)`. -/
def h1GradientSet (U : Set (Vec d)) : Set (Lp (Vec d) 2 (volume.restrict U)) :=
  {F | ∃ (u : Vec d → ℝ) (g : Vec d → Vec d) (h : H1 U u g), F = h.2.1.toLp g}

theorem lpDualTrialEnergy_toLp (a : CoefficientField d Λ) {U : Set (Vec d)} (hU : volume U ≠ ⊤)
    (q : Vec d) {g : Vec d → Vec d} (hg : MemLp g 2 (volume.restrict U)) :
    lpDualTrialEnergy a U q (hg.toLp g) = dualTrialEnergy a U q g := by
  have := isFiniteMeasure_restrict.mpr hU
  unfold lpDualTrialEnergy
  rw [lpTrialEnergy_toLp a 0 hg]
  have e : ⨍ x in U, dot q ((hg.toLp g) x) ∂volume = ⨍ x in U, dot q (g x) ∂volume := by
    refine average_congr ?_
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx]
  rw [e]
  have i1 := (integrable_dot_mulVec a U hg).const_mul (1 / 2 : ℝ)
  have i2 := integrable_dot_left_of_memLp hU hg q
  have i1n : Integrable (fun x => -(1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x)))
      (volume.restrict U) := (integrable_dot_mulVec a U hg).const_mul _
  simp only [dualTrialEnergy, setAverage_eq, smul_eq_mul, zero_add]
  rw [integral_add i1n i2]
  have e2 : ∫ x in U, -(1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x)) =
      -∫ x in U, (1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x)) := by
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  rw [e2]
  ring

theorem dualEnergy_eq_sSup_lpDualTrialEnergy (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hU : volume U ≠ ⊤) (q : Vec d) :
    dualEnergy a U q = sSup (lpDualTrialEnergy a U q '' h1GradientSet U) := by
  unfold dualEnergy
  congr 1
  ext E
  constructor
  · rintro ⟨u, g, h, rfl⟩
    exact ⟨h.2.1.toLp g, ⟨u, g, h, rfl⟩, lpDualTrialEnergy_toLp a hU q h.2.1⟩
  · rintro ⟨F, ⟨u, g, h, rfl⟩, rfl⟩
    exact ⟨u, g, h, lpDualTrialEnergy_toLp a hU q h.2.1⟩

theorem measurable_lpDualTrialEnergy (U : Set (Vec d)) (q : Vec d)
    (F : Lp (Vec d) 2 (volume.restrict U)) :
    Measurable (fun a : CoefficientField d Λ => lpDualTrialEnergy a U q F) :=
  (measurable_lpTrialEnergy U 0 F).neg.add_const _

/-- `2|q·v| ≤ s|q|² + s⁻¹|v|²` for `s > 0`. -/
theorem two_mul_abs_dot_le {s : ℝ} (hs : 0 < s) (q v : Vec d) :
    2 * |dot q v| ≤ s * euclideanSq q + s⁻¹ * euclideanSq v := by
  have hsq : ∀ w : Vec d, euclideanSq (s • w) = s ^ 2 * euclideanSq w := fun w => by
    simp only [euclideanSq, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hd : ∀ w : Vec d, dot (s • q) w = s * dot q w := fun w => by
    simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  have h1 := two_mul_dot_le (s • q) v
  have h2 := two_mul_dot_le (s • q) (-v)
  have hn : dot q (-v) = -dot q v := by
    simp only [dot, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  have hv : euclideanSq (-v) = euclideanSq v := by
    simp only [euclideanSq, dot, Pi.neg_apply, neg_mul_neg]
  rw [hsq, hd] at h1 h2
  rw [hn, hv] at h2
  have key : s * (2 * |dot q v|) ≤ s * (s * euclideanSq q + s⁻¹ * euclideanSq v) := by
    have e : s * (s * euclideanSq q + s⁻¹ * euclideanSq v) = s ^ 2 * euclideanSq q +
        euclideanSq v := by field_simp
    rw [e]
    rcases abs_cases (dot q v) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith
  exact le_of_mul_le_mul_left key hs

/-- **The linear part of (2.1) is continuous on `L²(U)`**:
`|⨍_U q·F' - ⨍_U q·F| ≤ s|q|² + s⁻¹ d |U|⁻¹ ‖F' - F‖²` for `s > 0`. -/
theorem abs_setAverage_dot_sub_le {U : Set (Vec d)} (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤)
    (q : Vec d) (F F' : Lp (Vec d) 2 (volume.restrict U)) {s : ℝ} (hs : 0 < s) :
    |(⨍ x in U, dot q (F' x) ∂volume) - ⨍ x in U, dot q (F x) ∂volume| ≤
      s * euclideanSq q + s⁻¹ * (d * (volume.real U)⁻¹ * ‖F' - F‖ ^ 2) := by
  have := isFiniteMeasure_restrict.mpr hU
  have hV : 0 < volume.real U := ENNReal.toReal_pos hU0 hU
  have hW : MemLp (fun x => F' x - F x) 2 (volume.restrict U) := (Lp.memLp F').sub (Lp.memLp F)
  have i1 := integrable_dot_left_of_memLp hU (Lp.memLp F') q
  have i2 := integrable_dot_left_of_memLp hU (Lp.memLp F) q
  have i3 := integrable_dot_left_of_memLp hU hW q
  have iS := integrable_euclideanSq_of_memLp hW
  have hsq : ∫ x in U, euclideanSq (F' x - F x) ≤ d * ‖F' - F‖ ^ 2 := by
    have h := integral_euclideanSq_le_card_mul_norm_sq (F' - F)
    refine le_of_eq_of_le (integral_congr_ae ?_) h
    filter_upwards [Lp.coeFn_sub F' F] with x hx
    rw [hx]
    rfl
  have hdiff : (∫ x in U, dot q (F' x)) - ∫ x in U, dot q (F x) =
      ∫ x in U, dot q (F' x - F x) := by
    rw [← integral_sub i1 i2]
    exact integral_congr_ae (Eventually.of_forall fun x => (dot_sub_right_eq q _ _).symm)
  have habs : |∫ x in U, dot q (F' x - F x)| ≤
      (1 / 2 : ℝ) * (s * euclideanSq q * volume.real U + s⁻¹ * ∫ x in U, euclideanSq (F' x - F x)) := by
    refine (abs_integral_le_integral_abs).trans ?_
    have iR : Integrable (fun x => (1 / 2 : ℝ) * (s * euclideanSq q + s⁻¹ * euclideanSq (F' x - F x)))
        (volume.restrict U) := ((integrable_const _).add (iS.const_mul _)).const_mul _
    refine (integral_mono i3.abs iR fun x => ?_).trans (le_of_eq ?_)
    · have := two_mul_abs_dot_le hs q (F' x - F x)
      simp only
      linarith
    · rw [integral_const_mul, integral_add (integrable_const _) (iS.const_mul _),
        integral_const_mul s⁻¹, setIntegral_const, smul_eq_mul]
      ring
  rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul, ← mul_sub, hdiff, abs_mul,
    abs_of_pos (inv_pos.mpr hV)]
  have hq := euclideanSq_nonneg q
  calc (volume.real U)⁻¹ * |∫ x in U, dot q (F' x - F x)|
      ≤ (volume.real U)⁻¹ * ((1 / 2 : ℝ) *
          (s * euclideanSq q * volume.real U + s⁻¹ * ∫ x in U, euclideanSq (F' x - F x))) :=
        mul_le_mul_of_nonneg_left habs (inv_nonneg.mpr hV.le)
    _ ≤ (volume.real U)⁻¹ * ((1 / 2 : ℝ) *
          (s * euclideanSq q * volume.real U + s⁻¹ * (d * ‖F' - F‖ ^ 2))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by norm_num))
          (inv_nonneg.mpr hV.le)
        linarith [mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr hs.le)]
    _ ≤ s * euclideanSq q + s⁻¹ * (d * (volume.real U)⁻¹ * ‖F' - F‖ ^ 2) := by
        have hn : 0 ≤ s⁻¹ * (d * (volume.real U)⁻¹ * ‖F' - F‖ ^ 2) := by positivity
        have e : (volume.real U)⁻¹ * ((1 / 2 : ℝ) *
            (s * euclideanSq q * volume.real U + s⁻¹ * (d * ‖F' - F‖ ^ 2))) =
            (1 / 2 : ℝ) * (s * euclideanSq q + s⁻¹ * (d * (volume.real U)⁻¹ * ‖F' - F‖ ^ 2)) := by
          field_simp
        rw [e]
        have : 0 ≤ s * euclideanSq q := mul_nonneg hs.le hq
        linarith

/-- **`μ*(U, q)` is a countable supremum of functionals of fixed fields**: there is a countable
nonempty set `T` of gradients of `H¹(U)`, independent of the coefficient field, with
`μ*(U, q) = sup_{F ∈ T} ⨍_U (-½ F·aF + q·F)`. -/
theorem exists_countable_dualEnergy_eq_iSup {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hU : volume U ≠ ⊤) (hΛ : 0 ≤ Λ) (q : Vec d) :
    ∃ T : Set (Lp (Vec d) 2 (volume.restrict U)), T.Countable ∧ T.Nonempty ∧ T ⊆ h1GradientSet U ∧
      ∀ a : CoefficientField d Λ, dualEnergy a U q = ⨆ F : T, lpDualTrialEnergy a U q F := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩
  obtain ⟨T, hTc, hTH, hHT⟩ := TopologicalSpace.exists_countable_dense_subset (h1GradientSet U)
  have h0 : (H1_zero U).2.1.toLp (fun _ => (0 : Vec d)) ∈ h1GradientSet U :=
    ⟨_, _, H1_zero U, rfl⟩
  have hTne : T.Nonempty := by
    by_contra hT
    rw [Set.not_nonempty_iff_eq_empty] at hT
    have := hHT h0
    rw [hT, closure_empty] at this
    exact this
  have : Countable T := hTc.to_subtype
  have : Nonempty T := hTne.to_subtype
  refine ⟨T, hTc, hTne, hTH, fun a => ?_⟩
  have hle : ∀ F ∈ h1GradientSet U, lpDualTrialEnergy a U q F ≤ (1 / 2 : ℝ) * euclideanSq q := by
    rintro _ ⟨u, g, h, rfl⟩
    rw [lpDualTrialEnergy_toLp a hU q h.2.1]
    exact dualTrialEnergy_le a hU0 hU q g
  have hbddT : BddAbove (Set.range fun F : T => lpDualTrialEnergy a U q F) :=
    ⟨(1 / 2 : ℝ) * euclideanSq q, by rintro _ ⟨F, rfl⟩; exact hle F (hTH F.2)⟩
  have hbdd : BddAbove (lpDualTrialEnergy a U q '' h1GradientSet U) :=
    ⟨(1 / 2 : ℝ) * euclideanSq q, by rintro _ ⟨F, hF, rfl⟩; exact hle F hF⟩
  rw [dualEnergy_eq_sSup_lpDualTrialEnergy a hU q]
  refine le_antisymm ?_ (ciSup_le fun F => le_csSup hbdd ⟨F, hTH F.2, rfl⟩)
  refine csSup_le (Set.Nonempty.image _ ⟨_, h0⟩) ?_
  rintro _ ⟨F, hF, rfl⟩
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨E0, hE0⟩ : ∃ E0, E0 = lpTrialEnergy a U 0 F := ⟨_, rfl⟩
  have hE0n : 0 ≤ E0 := hE0 ▸ lpTrialEnergy_nonneg a U 0 F
  have hq := euclideanSq_nonneg q
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = η / (4 * (E0 + 1)) := ⟨_, rfl⟩
  have ht : 0 < t := by rw [htdef]; positivity
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = η / (4 * (euclideanSq q + 1)) := ⟨_, rfl⟩
  have hs : 0 < s := by rw [hsdef]; positivity
  have hVi : 0 ≤ (volume.real U)⁻¹ := inv_nonneg.mpr measureReal_nonneg
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = (1 + t⁻¹) * ((1 / 2) * Λ * d * (volume.real U)⁻¹) +
    s⁻¹ * (d * (volume.real U)⁻¹) := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hKdef]; positivity
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min 1 (η / (4 * (K + 1))) := ⟨_, rfl⟩
  have hδ : 0 < δ := hδdef ▸ lt_min one_pos (by positivity)
  obtain ⟨F', hF'T, hdist⟩ := Metric.mem_closure_iff.1 (hHT hF) δ hδ
  have hnorm : ‖F' - F‖ ≤ δ := by
    rw [← dist_eq_norm, dist_comm]
    exact hdist.le
  have h1 : ‖F' - F‖ ^ 2 ≤ δ := by
    have hδ1 : δ ≤ 1 := hδdef ▸ min_le_left _ _
    have hn0 := norm_nonneg (F' - F)
    nlinarith
  have h2 : K * δ ≤ η / 4 := by
    have hδ2 : δ ≤ η / (4 * (K + 1)) := hδdef ▸ min_le_right _ _
    calc K * δ ≤ K * (η / (4 * (K + 1))) := mul_le_mul_of_nonneg_left hδ2 hK
      _ ≤ (K + 1) * (η / (4 * (K + 1))) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = η / 4 := by field_simp
  have h3 : t * E0 ≤ η / 4 := by
    rw [htdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h4 : s * euclideanSq q ≤ η / 4 := by
    rw [hsdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hE := lpTrialEnergy_le a hU hΛ 0 F F' ht
  have hL := abs_setAverage_dot_sub_le hU0 hU q F F' hs
  have hT' : lpDualTrialEnergy a U q F' ≤ ⨆ G : T, lpDualTrialEnergy a U q G :=
    le_ciSup hbddT ⟨F', hF'T⟩
  have hKn : (1 + t⁻¹) * ((1 / 2) * Λ * d * (volume.real U)⁻¹ * ‖F' - F‖ ^ 2) +
      s⁻¹ * (d * (volume.real U)⁻¹ * ‖F' - F‖ ^ 2) = K * ‖F' - F‖ ^ 2 := by
    rw [hKdef]
    ring
  have h5 : K * ‖F' - F‖ ^ 2 ≤ K * δ := mul_le_mul_of_nonneg_left h1 hK
  have hab := (abs_le.mp hL).1
  rw [← hE0] at hE
  unfold lpDualTrialEnergy at hT' ⊢
  rw [← hE0]
  linarith only [hT', hE, hab, hKn, h5, h2, h3, h4, hη]

/-- **`μ*(U, q)` is measurable** in the coefficient field, for a set `U` of positive finite
volume. -/
theorem measurable_dualEnergy {U : Set (Vec d)} (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤)
    (hΛ : 0 ≤ Λ) (q : Vec d) : Measurable (fun a : CoefficientField d Λ => dualEnergy a U q) := by
  obtain ⟨T, hTc, hTne, -, key⟩ := exists_countable_dualEnergy_eq_iSup (Λ := Λ) hU0 hU hΛ q
  have : Countable T := hTc.to_subtype
  rw [funext key]
  exact Measurable.iSup fun F => measurable_lpDualTrialEnergy U q F

end QSH
