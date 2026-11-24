import QuantitativeStochasticHomogenization.Ch01.Sec02.DirichletEnergyBounds
import QuantitativeStochasticHomogenization.Front.Assumptions.MeasurableVersion

/-!
# Measurability of the Dirichlet energy `μ(U, e)`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.2, the Dirichlet energy (1.7) as a random variable.

For a set `U` of finite volume, `a ↦ μ(U, e)` is measurable (`measurable_dirichletEnergy`). The
infimum (1.7) runs over the gradients of `H¹₀(U)`, which lie in the separable space `L²(U)`; a
countable subset `T` of them is dense among them. For `t > 0` the energy of `e + G + W` is at most
`(1 + t)` times that of `e + G` plus `(1 + t⁻¹) ½ Λ ∫ |W|²` (`lpTrialEnergy_le`), so the infimum over
`T` is the infimum (1.7) for every coefficient field. The energy of each element of `T` is
measurable, being the integral of a jointly measurable function of `(a, x)` once `a` is replaced by
its jointly measurable version (`coefficientVersion`).
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## A pointwise inequality -/

/-- `(G + W)·A(G + W) ≤ (1 + t) G·AG + (1 + t⁻¹) W·AW` for a symmetric nonnegative `A` and
`t > 0`. -/
theorem dot_add_mulVec_add_le {A : Mat d} (hA : A.transpose = A)
    (hpos : ∀ v : Vec d, 0 ≤ dot v (A.mulVec v)) {t : ℝ} (ht : 0 < t) (G W : Vec d) :
    dot (G + W) (A.mulVec (G + W)) ≤
      (1 + t) * dot G (A.mulVec G) + (1 + t⁻¹) * dot W (A.mulVec W) := by
  have h0 := hpos (t • G - W)
  have hc := dot_mulVec_comm hA G W
  have e1 : dot (t • G - W) (A.mulVec (t • G - W)) = t * t * dot G (A.mulVec G) -
      t * dot G (A.mulVec W) - t * dot W (A.mulVec G) + dot W (A.mulVec W) := by
    simp only [dot_eq_dotProduct, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub,
      sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  have e2 : dot (G + W) (A.mulVec (G + W)) = dot G (A.mulVec G) + dot G (A.mulVec W) +
      dot W (A.mulVec G) + dot W (A.mulVec W) := by
    simp only [dot_eq_dotProduct, Matrix.mulVec_add, dotProduct_add, add_dotProduct]
    ring
  rw [e2]
  rw [e1] at h0
  have key : t * (2 * dot G (A.mulVec W)) ≤
      t * (t * dot G (A.mulVec G) + t⁻¹ * dot W (A.mulVec W)) := by
    rw [mul_add, ← mul_assoc t t⁻¹, mul_inv_cancel₀ ht.ne', one_mul]
    nlinarith
  have h2 := le_of_mul_le_mul_left key ht
  nlinarith

private theorem euclideanSq_le_card_mul_sq_norm (u : Vec d) : euclideanSq u ≤ d * ‖u‖ ^ 2 := by
  unfold euclideanSq dot
  calc ∑ i, u i * u i ≤ ∑ _i : Fin d, ‖u‖ ^ 2 := Finset.sum_le_sum fun i _ => by
        have h := norm_le_pi_norm u i
        rw [Real.norm_eq_abs] at h
        nlinarith [abs_nonneg (u i), abs_mul_abs_self (u i)]
    _ = d * ‖u‖ ^ 2 := by simp

/-- `∫ |F|² ≤ d ‖F‖²_{L²}`. -/
theorem integral_euclideanSq_le_card_mul_norm_sq {μ : Measure (Vec d)}
    (F : Lp (Vec d) 2 μ) : ∫ x, euclideanSq (F x) ∂μ ≤ d * ‖F‖ ^ 2 := by
  have hF := Lp.memLp F
  have hnorm : ‖F‖ ^ 2 = ∫ x, ‖F x‖ ^ (2 : ℝ) ∂μ := by
    rw [Lp.norm_def, hF.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
    have h0 : 0 ≤ ∫ x, ‖F x‖ ^ (2 : ℝ≥0∞).toReal ∂μ :=
      integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg h0 _)]
    simp only [ENNReal.toReal_ofNat]
    exact Real.rpow_inv_natCast_pow (n := 2) (by simpa using h0) two_ne_zero
  have hint : Integrable (fun x => ‖F x‖ ^ (2 : ℝ)) μ := by
    simpa using hF.integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
  rw [hnorm, ← integral_const_mul]
  refine integral_mono (integrable_euclideanSq_of_memLp hF) (hint.const_mul _) fun x => ?_
  have := euclideanSq_le_card_mul_sq_norm (F x)
  simpa [Real.rpow_two] using this

/-! ## The energy of an element of `L²(U)` -/

/-- The energy `⨍_U ½ (e + F)·a(e + F)` of an element `F` of `L²(U)`. -/
def lpTrialEnergy (a : CoefficientField d Λ) (U : Set (Vec d)) (e : Vec d)
    (F : Lp (Vec d) 2 (volume.restrict U)) : ℝ :=
  ⨍ x in U, (1 / 2 : ℝ) * dot (e + F x) ((a x).mulVec (e + F x)) ∂volume

theorem lpTrialEnergy_nonneg (a : CoefficientField d Λ) (U : Set (Vec d)) (e : Vec d)
    (F : Lp (Vec d) 2 (volume.restrict U)) : 0 ≤ lpTrialEnergy a U e F :=
  setAverage_nonneg_of_nonneg fun x => energyDensity_nonneg a e (F x) x

theorem continuous_dot_mulVec_self :
    Continuous (fun p : Mat d × Vec d => dot p.2 (p.1.mulVec p.2)) :=
  continuous_snd.dotProduct (continuous_fst.matrix_mulVec continuous_snd)

theorem aestronglyMeasurable_dot_mulVec (a : CoefficientField d Λ) (U : Set (Vec d))
    {v : Vec d → Vec d} (hv : AEStronglyMeasurable v (volume.restrict U)) :
    AEStronglyMeasurable (fun x => dot (v x) ((a x).mulVec (v x))) (volume.restrict U) := by
  have hm : Measurable (fun x => dot (hv.mk v x) ((coefficientVersion a x).mulVec (hv.mk v x))) :=
    continuous_dot_mulVec_self.measurable.comp
      ((measurable_coefficientVersion.comp measurable_prodMk_left).prodMk hv.measurable_mk)
  refine hm.aestronglyMeasurable.congr ?_
  filter_upwards [ae_restrict_of_ae (ae_coefficientVersion_eq a), hv.ae_eq_mk] with x hx hvx
  simp only [hx, hvx]

theorem integrable_dot_mulVec (a : CoefficientField d Λ) (U : Set (Vec d))
    {v : Vec d → Vec d} (hv : MemLp v 2 (volume.restrict U)) :
    Integrable (fun x => dot (v x) ((a x).mulVec (v x))) (volume.restrict U) := by
  refine ((integrable_euclideanSq_of_memLp hv).const_mul Λ).mono'
    (aestronglyMeasurable_dot_mulVec a U hv.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  have h := a.elliptic x (v x)
  rw [Real.norm_eq_abs, abs_of_nonneg ((euclideanSq_nonneg _).trans h.1)]
  exact h.2

/-- **Comparison of energies**: for `t > 0`,
`E(F') ≤ (1 + t) E(F) + (1 + t⁻¹) ½ Λ d |U|⁻¹ ‖F' - F‖²`. -/
theorem lpTrialEnergy_le (a : CoefficientField d Λ) {U : Set (Vec d)} (hU : volume U ≠ ⊤)
    (hΛ : 0 ≤ Λ) (e : Vec d) (F F' : Lp (Vec d) 2 (volume.restrict U)) {t : ℝ} (ht : 0 < t) :
    lpTrialEnergy a U e F' ≤ (1 + t) * lpTrialEnergy a U e F +
      (1 + t⁻¹) * ((1 / 2) * Λ * d * (volume.real U)⁻¹ * ‖F' - F‖ ^ 2) := by
  have := isFiniteMeasure_restrict.mpr hU
  have hc : MemLp (fun _ : Vec d => e) 2 (volume.restrict U) := memLp_const e
  have hG : MemLp (fun x => e + F x) 2 (volume.restrict U) := hc.add (Lp.memLp F)
  have hG' : MemLp (fun x => e + F' x) 2 (volume.restrict U) := hc.add (Lp.memLp F')
  have hW : MemLp (fun x => F' x - F x) 2 (volume.restrict U) := (Lp.memLp F').sub (Lp.memLp F)
  have hi1 := integrable_dot_mulVec a U hG
  have hi2 := integrable_dot_mulVec a U hG'
  have hi3 := integrable_dot_mulVec a U hW
  have hpt : ∀ x, (1 / 2 : ℝ) * dot (e + F' x) ((a x).mulVec (e + F' x)) ≤
      (1 + t) * ((1 / 2 : ℝ) * dot (e + F x) ((a x).mulVec (e + F x))) +
        (1 + t⁻¹) * ((1 / 2 : ℝ) * dot (F' x - F x) ((a x).mulVec (F' x - F x))) := by
    intro x
    have h := dot_add_mulVec_add_le (a.symmetric x)
      (fun v => (euclideanSq_nonneg v).trans (a.elliptic x v).1) ht (e + F x) (F' x - F x)
    rw [show e + F x + (F' x - F x) = e + F' x by abel] at h
    linarith
  have hint : ∫ x, (1 / 2 : ℝ) * dot (e + F' x) ((a x).mulVec (e + F' x)) ∂(volume.restrict U) ≤
      (1 + t) * ∫ x, (1 / 2 : ℝ) * dot (e + F x) ((a x).mulVec (e + F x)) ∂(volume.restrict U) +
        (1 + t⁻¹) * ((1 / 2) * Λ * ∫ x, euclideanSq (F' x - F x) ∂(volume.restrict U)) := by
    have hW2 : ∫ x, (1 / 2 : ℝ) * dot (F' x - F x) ((a x).mulVec (F' x - F x)) ∂(volume.restrict U) ≤
        (1 / 2) * Λ * ∫ x, euclideanSq (F' x - F x) ∂(volume.restrict U) := by
      rw [← integral_const_mul]
      refine integral_mono (hi3.const_mul _) ((integrable_euclideanSq_of_memLp hW).const_mul _)
        fun x => ?_
      have := (a.elliptic x (F' x - F x)).2
      change (1 / 2 : ℝ) * dot (F' x - F x) ((a x).mulVec (F' x - F x)) ≤
        (1 / 2) * Λ * euclideanSq (F' x - F x)
      nlinarith
    calc ∫ x, (1 / 2 : ℝ) * dot (e + F' x) ((a x).mulVec (e + F' x)) ∂(volume.restrict U)
        ≤ ∫ x, ((1 + t) * ((1 / 2 : ℝ) * dot (e + F x) ((a x).mulVec (e + F x))) +
            (1 + t⁻¹) * ((1 / 2 : ℝ) * dot (F' x - F x) ((a x).mulVec (F' x - F x)))) ∂(volume.restrict U) :=
          integral_mono (hi2.const_mul _) (((hi1.const_mul _).const_mul _).add
            ((hi3.const_mul _).const_mul _)) hpt
      _ = (1 + t) * ∫ x, (1 / 2 : ℝ) * dot (e + F x) ((a x).mulVec (e + F x)) ∂(volume.restrict U) +
            (1 + t⁻¹) * ∫ x, (1 / 2 : ℝ) * dot (F' x - F x) ((a x).mulVec (F' x - F x)) ∂(volume.restrict U) := by
          rw [integral_add ((hi1.const_mul _).const_mul _) ((hi3.const_mul _).const_mul _),
            integral_const_mul (1 + t), integral_const_mul (1 + t⁻¹)]
      _ ≤ _ := by
          have ht' : 0 ≤ 1 + t⁻¹ := by positivity
          linarith [mul_le_mul_of_nonneg_left hW2 ht']
  have hsq : ∫ x, euclideanSq (F' x - F x) ∂(volume.restrict U) ≤ d * ‖F' - F‖ ^ 2 := by
    have h := integral_euclideanSq_le_card_mul_norm_sq (F' - F)
    refine le_of_eq_of_le (integral_congr_ae ?_) h
    filter_upwards [Lp.coeFn_sub F' F] with x hx
    rw [hx]
    rfl
  have hV : 0 ≤ (volume.real U)⁻¹ := inv_nonneg.mpr measureReal_nonneg
  unfold lpTrialEnergy
  rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul]
  have h1 : (1 + t⁻¹) * ((1 / 2) * Λ * ∫ x, euclideanSq (F' x - F x) ∂(volume.restrict U)) ≤
      (1 + t⁻¹) * ((1 / 2) * Λ * (d * ‖F' - F‖ ^ 2)) := by
    have ht' : 0 ≤ 1 + t⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (by positivity)) ht'
  calc (volume.real U)⁻¹ * ∫ x in U, (1 / 2 : ℝ) * dot (e + F' x) ((a x).mulVec (e + F' x))
      ≤ (volume.real U)⁻¹ * ((1 + t) * ∫ x, (1 / 2 : ℝ) * dot (e + F x) ((a x).mulVec (e + F x)) ∂(volume.restrict U) +
          (1 + t⁻¹) * ((1 / 2) * Λ * (d * ‖F' - F‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left (hint.trans (by linarith)) hV
    _ = _ := by ring

/-! ## The infimum over a countable dense set -/

/-- The gradients of the functions of `H¹₀(U)`, as elements of `L²(U)`. -/
def h01GradientSet (U : Set (Vec d)) : Set (Lp (Vec d) 2 (volume.restrict U)) :=
  {F | ∃ (u : Vec d → ℝ) (g : Vec d → Vec d) (h : H01 U u g), F = h.2.1.toLp g}

theorem lpTrialEnergy_toLp (a : CoefficientField d Λ) {U : Set (Vec d)} (e : Vec d)
    {g : Vec d → Vec d} (hg : MemLp g 2 (volume.restrict U)) :
    lpTrialEnergy a U e (hg.toLp g) =
      ⨍ x in U, (1 / 2 : ℝ) * dot (e + g x) ((a x).mulVec (e + g x)) ∂volume := by
  unfold lpTrialEnergy
  refine average_congr ?_
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx]

theorem dirichletEnergy_eq_sInf_lpTrialEnergy (a : CoefficientField d Λ) (U : Set (Vec d))
    (e : Vec d) :
    dirichletEnergy a U e = sInf (lpTrialEnergy a U e '' h01GradientSet U) := by
  unfold dirichletEnergy
  congr 1
  ext E
  constructor
  · rintro ⟨u, g, h, rfl⟩
    exact ⟨h.2.1.toLp g, ⟨u, g, h, rfl⟩, lpTrialEnergy_toLp a e h.2.1⟩
  · rintro ⟨F, ⟨u, g, h, rfl⟩, rfl⟩
    exact ⟨u, g, h, lpTrialEnergy_toLp a e h.2.1⟩

theorem measurable_lpTrialEnergy (U : Set (Vec d)) (e : Vec d)
    (F : Lp (Vec d) 2 (volume.restrict U)) :
    Measurable (fun a : CoefficientField d Λ => lpTrialEnergy a U e F) := by
  have hfun : (fun a : CoefficientField d Λ => lpTrialEnergy a U e F) = fun a =>
      (volume.real U)⁻¹ * ∫ x in U, (1 / 2 : ℝ) *
        dot (e + F x) ((coefficientVersion a x).mulVec (e + F x)) := by
    funext a
    unfold lpTrialEnergy
    rw [setAverage_eq, smul_eq_mul]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (ae_coefficientVersion_eq a)] with x hx
    rw [hx]
  rw [hfun]
  have hm : Measurable (fun p : CoefficientField d Λ × Vec d => (1 / 2 : ℝ) *
      dot (e + F p.2) ((coefficientVersion p.1 p.2).mulVec (e + F p.2))) := by
    refine measurable_const.mul ?_
    exact continuous_dot_mulVec_self.measurable.comp (measurable_coefficientVersion.prodMk
      (measurable_const.add ((Lp.stronglyMeasurable F).measurable.comp measurable_snd)))
  exact measurable_const.mul
    (hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict U)).measurable

/-- **The Dirichlet energy is a countable infimum of energies of fixed fields**: there is a
countable nonempty set `T` of gradients of `H¹₀(U)`, independent of the coefficient field, with
`μ(U, e) = inf_{F ∈ T} ⨍_U ½ (e + F)·a(e + F)`. -/
theorem exists_countable_dirichletEnergy_eq_iInf {U : Set (Vec d)} (hU : volume U ≠ ⊤)
    (hΛ : 0 ≤ Λ) (e : Vec d) :
    ∃ T : Set (Lp (Vec d) 2 (volume.restrict U)), T.Countable ∧ T.Nonempty ∧
      ∀ a : CoefficientField d Λ, dirichletEnergy a U e = ⨅ F : T, lpTrialEnergy a U e F := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩
  obtain ⟨T, hTc, hTH, hHT⟩ := TopologicalSpace.exists_countable_dense_subset (h01GradientSet U)
  have h0 : (H01_zero U).2.1.toLp (fun _ => (0 : Vec d)) ∈ h01GradientSet U :=
    ⟨_, _, H01_zero U, rfl⟩
  have hTne : T.Nonempty := by
    by_contra hT
    rw [Set.not_nonempty_iff_eq_empty] at hT
    have := hHT h0
    rw [hT, closure_empty] at this
    exact this
  have : Countable T := hTc.to_subtype
  have : Nonempty T := hTne.to_subtype
  have key : ∀ a : CoefficientField d Λ,
      dirichletEnergy a U e = ⨅ F : T, lpTrialEnergy a U e F := by
    intro a
    rw [dirichletEnergy_eq_sInf_lpTrialEnergy]
    have hbdd : BddBelow (lpTrialEnergy a U e '' h01GradientSet U) :=
      ⟨0, by rintro _ ⟨F, -, rfl⟩; exact lpTrialEnergy_nonneg a U e F⟩
    have hbddT : BddBelow (Set.range fun F : T => lpTrialEnergy a U e F) :=
      ⟨0, by rintro _ ⟨F, rfl⟩; exact lpTrialEnergy_nonneg a U e F⟩
    refine le_antisymm (le_ciInf fun F => csInf_le hbdd ⟨F, hTH F.2, rfl⟩) ?_
    refine le_csInf (Set.Nonempty.image _ ⟨_, h0⟩) ?_
    rintro _ ⟨F, hF, rfl⟩
    refine le_of_forall_pos_le_add fun η hη => ?_
    set E0 := lpTrialEnergy a U e F with hE0
    have hE0n : 0 ≤ E0 := lpTrialEnergy_nonneg a U e F
    set t : ℝ := η / (2 * (E0 + 1)) with htdef
    have ht : 0 < t := by positivity
    set K : ℝ := (1 + t⁻¹) * ((1 / 2) * Λ * d * (volume.real U)⁻¹) with hKdef
    have hK : 0 ≤ K := by
      have : 0 ≤ (volume.real U)⁻¹ := inv_nonneg.mpr measureReal_nonneg
      positivity
    set δ : ℝ := min 1 (η / (2 * (K + 1))) with hδdef
    have hδ : 0 < δ := lt_min one_pos (by positivity)
    obtain ⟨F', hF'T, hdist⟩ := Metric.mem_closure_iff.1 (hHT hF) δ hδ
    have hnorm : ‖F' - F‖ ≤ δ := by
      rw [← dist_eq_norm, dist_comm]
      exact hdist.le
    have hle := lpTrialEnergy_le a hU hΛ e F F' ht
    have h1 : ‖F' - F‖ ^ 2 ≤ δ := by
      have hδ1 : δ ≤ 1 := min_le_left _ _
      have hn0 := norm_nonneg (F' - F)
      nlinarith
    have h2 : K * δ ≤ η / 2 := by
      have hδ2 : δ ≤ η / (2 * (K + 1)) := min_le_right _ _
      calc K * δ ≤ K * (η / (2 * (K + 1))) := mul_le_mul_of_nonneg_left hδ2 hK
        _ ≤ (K + 1) * (η / (2 * (K + 1))) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = η / 2 := by field_simp
    have h3 : t * E0 ≤ η / 2 := by
      rw [htdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hT' : ⨅ G : T, lpTrialEnergy a U e G ≤ lpTrialEnergy a U e F' :=
      ciInf_le hbddT ⟨F', hF'T⟩
    have h4 : (1 + t⁻¹) * ((1 / 2) * Λ * d * (volume.real U)⁻¹ * ‖F' - F‖ ^ 2) =
        K * ‖F' - F‖ ^ 2 := by
      rw [hKdef]
      ring
    rw [h4] at hle
    have h5 : K * ‖F' - F‖ ^ 2 ≤ K * δ := mul_le_mul_of_nonneg_left h1 hK
    linarith
  exact ⟨T, hTc, hTne, key⟩

/-- **The Dirichlet energy is measurable** for a set `U` of finite volume. -/
theorem measurable_dirichletEnergy {U : Set (Vec d)} (hU : volume U ≠ ⊤) (hΛ : 0 ≤ Λ)
    (e : Vec d) : Measurable (fun a : CoefficientField d Λ => dirichletEnergy a U e) := by
  obtain ⟨T, hTc, hTne, key⟩ := exists_countable_dirichletEnergy_eq_iInf (Λ := Λ) hU hΛ e
  have : Countable T := hTc.to_subtype
  have : Nonempty T := hTne.to_subtype
  rw [funext key]
  exact Measurable.iInf fun F => measurable_lpTrialEnergy U e F

end QSH
