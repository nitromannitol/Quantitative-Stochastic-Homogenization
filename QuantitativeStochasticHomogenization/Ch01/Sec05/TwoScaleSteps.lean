import QuantitativeStochasticHomogenization.Ch01.Sec05.TwoScaleHat

/-!
# Steps 2–4 of the proof of Theorem 1.17

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.5, Steps 2, 3 and 4 of the proof of Theorem 1.17, for fixed data: from the bound (1.64)
with constant `K₁` (`stepOneConstant`), the energy estimate of Lemma C.8 (`lemma_C_8_energy`)
applied to `u^ε - w^ε ∈ H¹₀(U)` gives (1.66), `‖∇u^ε - ∇w^ε‖_{L̲²(U)} ≤ C K₁`; with the
Poincaré inequality, the bounds `‖G_j Φ_j‖_{L²(U)} ≤ M ‖Φ_j‖_{L²(U)}` of the corrector part of
`w^ε` and the multiplier estimate on `Ĥ⁻¹(U)`, there is `C(U, d, Λ)` with
`‖u^ε - u‖_{L̲²(U)} + ‖∇u^ε - ∇u‖_{Ĥ̲⁻¹(U)} + ‖a(·/ε)∇u^ε - ā∇u‖_{Ĥ̲⁻¹(U)} ≤
C (K₁ + M ∑_j ‖Φ_j‖_{L²(U)})` (`exists_twoScale_steps`). The book bounds `‖u^ε - u‖_{L̲²(U)}` by
Lemma 1.13; here it follows from the Poincaré inequality for `u^ε - w^ε` and the bound of
`w^ε - u`.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

namespace TwoScale

variable {d : ℕ} {Λ : ℝ}

/-- The constant `K₁` of (1.64), see `abs_integral_twoScaleGrad_le`. -/
def stepOneConstant (U V : Set (Vec d)) (b : CoefficientField d Λ) (A : Mat d)
    (η : Vec d → ℝ) (g : Vec d → Vec d) (G Φ : Fin d → Vec d → ℝ) (M : ℝ)
    (N : Fin d → Fin d → ℝ) : ℝ :=
  ∑ k, l2 U (fun x => ((1 - η x) • ((b x).mulVec (g x) - A.mulVec (g x))) k) +
    ∑ j, ∑ k, l2 U (fun x => (b x).mulVec (Φ j x • gradient (G j) x) k) +
    (volume V).toReal ^ (1 / 2 : ℝ) * ((1 + d) * M) * ∑ j, ∑ i, N j i

theorem H01.finsetSum {U : Set (Vec d)} {ι : Type*} (s : Finset ι) {f : ι → Vec d → ℝ}
    {F : ι → Vec d → Vec d} (h : ∀ j ∈ s, H01 U (f j) (F j)) :
    H01 U (fun x => ∑ j ∈ s, f j x) (fun x => ∑ j ∈ s, F j x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using H01_zero U
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    refine (h1.linearCombination h2 1 1).congr (fun x => ?_) (fun x => ?_)
    · rw [Finset.sum_insert ha]; ring
    · rw [Finset.sum_insert ha, one_smul, one_smul]

theorem l2_sum_le {U : Set (Vec d)} {ι : Type*} (s : Finset ι) {f : ι → Vec d → ℝ}
    (hf : ∀ j ∈ s, MemLp (f j) 2 (volume.restrict U)) :
    l2 U (fun x => ∑ j ∈ s, f j x) ≤ ∑ j ∈ s, l2 U (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l2]
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 : ∀ j ∈ s, MemLp (f j) 2 (volume.restrict U) := fun j hj =>
      hf j (Finset.mem_insert_of_mem hj)
    have hm : MemLp (fun x => ∑ j ∈ s, f j x) 2 (volume.restrict U) := memLp_finsetSum _ h2
    have e : (fun x => ∑ j ∈ insert a s, f j x) = fun x => f a x + ∑ j ∈ s, f j x := by
      funext x; rw [Finset.sum_insert ha]
    rw [e, Finset.sum_insert ha]
    exact (l2_add_le h1 hm).trans (add_le_add le_rfl (ih h2))

theorem hatNegativeSobolevNorm_finsetSum_le {U : Set (Vec d)} {ι : Type*} (s : Finset ι)
    {f : ι → Vec d → ℝ} (hf : ∀ j ∈ s, MemLp (f j) 2 (volume.restrict U)) :
    hatNegativeSobolevNorm U (fun x => ∑ j ∈ s, f j x) ≤ ∑ j ∈ s, hatNegativeSobolevNorm U (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine (hatNegativeSobolevNorm_le_ofReal (B := 0) fun v G _ _ => by simp).trans ?_
    simp
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 : ∀ j ∈ s, MemLp (f j) 2 (volume.restrict U) := fun j hj =>
      hf j (Finset.mem_insert_of_mem hj)
    have e : (fun x => ∑ j ∈ insert a s, f j x) = fun x => f a x + ∑ j ∈ s, f j x := by
      funext x; rw [Finset.sum_insert ha]
    rw [e, Finset.sum_insert ha]
    exact (hatNegativeSobolevNorm_add_le h1 (memLp_finsetSum _ h2)).trans
      (add_le_add le_rfl (ih h2))

theorem scalarRms_apply_le_vectorRms {U : Set (Vec d)} (hUt : volume U ≠ ⊤) (hU0 : volume U ≠ 0)
    {G : Vec d → Vec d} (hG : ∀ i, MemLp (fun x => G x i) 2 (volume.restrict U)) (k : Fin d) :
    scalarRms volume U (fun x => G x k) ≤ vectorRms volume U G := by
  have h1 := l2_apply_le_sqrt_mul_vectorRms hUt hG k
  rw [l2_eq_sqrt_mul_scalarRms hUt (hG k)] at h1
  have hV : 0 < (volume U).toReal := ENNReal.toReal_pos hU0 hUt
  exact le_of_mul_le_mul_left h1 (Real.rpow_pos_of_pos hV _)

theorem scalarRms_eq_inv_mul_l2 {U : Set (Vec d)} (hUt : volume U ≠ ⊤) (hU0 : volume U ≠ 0)
    {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict U)) :
    scalarRms volume U f = ((volume U).toReal ^ (1 / 2 : ℝ))⁻¹ * l2 U f := by
  have hV : 0 < (volume U).toReal := ENNReal.toReal_pos hU0 hUt
  rw [l2_eq_sqrt_mul_scalarRms hUt hf, ← mul_assoc,
    inv_mul_cancel₀ (Real.rpow_pos_of_pos hV _).ne', one_mul]

theorem hatNegativeSobolevNorm_le_rms' {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hUt : volume U ≠ ⊤) {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict U)) {B : ℝ}
    (hB : scalarRms volume U f ≤ B) :
    hatNegativeSobolevNorm U f ≤ ENNReal.ofReal ((volume U).toReal ^ ((1 : ℝ) / d) * B) :=
  (hatNegativeSobolevNorm_le_rms hU0 hUt hf).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg ENNReal.toReal_nonneg _)))

theorem scalarRms_le_of_setIntegral_sq_le {U : Set (Vec d)} {f : Vec d → ℝ} {G : Vec d → Vec d}
    {C : ℝ} (hC : 0 ≤ C) (h : ∫ x in U, f x ^ 2 ≤ C * ∫ x in U, euclideanSq (G x)) :
    scalarRms volume U f ≤ Real.sqrt C * vectorRms volume U G := by
  unfold scalarRms vectorRms
  rw [← Real.sqrt_mul hC]
  refine Real.sqrt_le_sqrt ?_
  rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul]
  have h0 : 0 ≤ (volume.real U)⁻¹ := inv_nonneg.2 measureReal_nonneg
  nlinarith [mul_le_mul_of_nonneg_left h h0]

theorem vectorRms_mulVec_le {U : Set (Vec d)} (hΛ : 0 ≤ Λ) (b : CoefficientField d Λ)
    {h : Vec d → Vec d} (hh : ∀ i, MemLp (fun x => h x i) 2 (volume.restrict U))
    (hUt : volume U ≠ ⊤) :
    vectorRms volume U (fun x => (b x).mulVec (h x)) ≤ Λ * vectorRms volume U h := by
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUt
  have hpt : ∀ x, euclideanSq ((b x).mulVec (h x)) ≤ Λ ^ 2 * euclideanSq (h x) := fun x =>
    euclideanSq_mulVec_le_of_dot_le (b.symmetric x) (fun v => by
      have := (b.elliptic x v).1
      have h0 : 0 ≤ euclideanSq v := by
        unfold euclideanSq dot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
      linarith) (fun v => (b.elliptic x v).2) (h x)
  have hint : ∀ {Q : Vec d → Vec d}, (∀ i, MemLp (fun x => Q x i) 2 (volume.restrict U)) →
      Integrable (fun x => euclideanSq (Q x)) (volume.restrict U) := fun {Q} hQ => by
    have h' : Integrable (fun x => ∑ i, Q x i ^ 2) (volume.restrict U) :=
      integrable_finsetSum _ fun i _ => (hQ i).integrable_sq
    refine h'.congr (Eventually.of_forall fun x => ?_)
    simp [euclideanSq, dot, sq]
  have hbh : ∀ i, MemLp (fun x => (b x).mulVec (h x) i) 2 (volume.restrict U) := fun i =>
    memLp_coefficient_mulVec_apply b (memLp_pi_iff.2 hh) i
  unfold vectorRms
  rw [show Λ * Real.sqrt (⨍ x in U, euclideanSq (h x) ∂volume) =
      Real.sqrt (Λ ^ 2 * ⨍ x in U, euclideanSq (h x) ∂volume) by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hΛ]]
  refine Real.sqrt_le_sqrt ?_
  calc ⨍ x in U, euclideanSq ((b x).mulVec (h x)) ∂volume
      = (volume.real U)⁻¹ * ∫ x in U, euclideanSq ((b x).mulVec (h x)) := by
        rw [setAverage_eq, smul_eq_mul]
    _ ≤ (volume.real U)⁻¹ * ∫ x in U, Λ ^ 2 * euclideanSq (h x) :=
        mul_le_mul_of_nonneg_left (setIntegral_mono (hint hbh) ((hint hh).const_mul _) hpt)
          (inv_nonneg.2 measureReal_nonneg)
    _ = Λ ^ 2 * ⨍ x in U, euclideanSq (h x) ∂volume := by
        rw [integral_const_mul, setAverage_eq, smul_eq_mul]; ring

variable {U : Set (Vec d)}

/-- The bound of `‖∇u^ε - ∇u‖_{Ĥ̲⁻¹(U)}` in Step 4. -/
theorem vectorHat_grad_le (hU0 : volume U ≠ 0) (hUt : volume U ≠ ⊤)
    {g gε DW h : Vec d → Vec d} {W : Vec d → ℝ} (hW : H01 U W DW)
    (hh : ∀ i, MemLp (fun x => h x i) 2 (volume.restrict U))
    (hgg : ∀ x, gε x - g x = h x + DW x) {Y Z : ℝ} (hY : vectorRms volume U h ≤ Y)
    (hZ : scalarRms volume U W ≤ Z) :
    vectorHatNegativeSobolevNorm U (fun x => gε x - g x) ≤
      ENNReal.ofReal (d * ((volume U).toReal ^ ((1 : ℝ) / d) * Y + Z)) := by
  have hY0 : 0 ≤ Y := (Real.sqrt_nonneg _).trans hY
  have hZ0 : 0 ≤ Z := (Real.sqrt_nonneg _).trans hZ
  unfold vectorHatNegativeSobolevNorm
  have hk : ∀ k, hatNegativeSobolevNorm U (fun x => (gε x - g x) k) ≤
      ENNReal.ofReal ((volume U).toReal ^ ((1 : ℝ) / d) * Y + Z) := by
    intro k
    have e : (fun x => (gε x - g x) k) = fun x => h x k + DW x k := by
      funext x; rw [hgg x]; rfl
    rw [e, ENNReal.ofReal_add (by positivity) hZ0]
    refine (hatNegativeSobolevNorm_add_le (hh k) (hW.2.1.eval k)).trans (add_le_add ?_ ?_)
    · exact hatNegativeSobolevNorm_le_rms' hU0 hUt (hh k)
        ((scalarRms_apply_le_vectorRms hUt hU0 hh k).trans hY)
    · exact (hatNegativeSobolevNorm_grad_le_of_H01 hUt hW k).trans (ENNReal.ofReal_le_ofReal hZ)
  refine (Finset.sum_le_sum fun k _ => hk k).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg d)]

/-- The bound of `‖a(·/ε)∇u^ε - ā∇u‖_{Ĥ̲⁻¹(U)}` in Step 4. -/
theorem vectorHat_flux_le (hΛ : 1 ≤ Λ) (hU : PDE.IsOpenBoundedConvexDomain U)
    (hU0 : volume U ≠ 0) {V : Set (Vec d)} (hUV : U ⊆ V) (hV1 : 1 ≤ (volume V).toReal)
    (hVt : volume V ≠ ⊤) {b : CoefficientField d Λ} {A : Mat d} {η : Vec d → ℝ}
    {g gε h : Vec d → Vec d} {G Φ : Fin d → Vec d → ℝ} {DΦ : Fin d → Vec d → Vec d}
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U))
    (hh : ∀ i, MemLp (fun x => h x i) 2 (volume.restrict U))
    (hη : Continuous η) (hη01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (hG : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (G j)) (hGc : ∀ j, HasCompactSupport (G j))
    (hGU : ∀ j, tsupport (G j) ⊆ U)
    (hGη : ∀ᵐ x ∂(volume.restrict U), (fun j => G j x) = η x • g x)
    (hΦ : ∀ j, MemLp (Φ j) 2 (volume.restrict U))
    (hDΦ : ∀ j i, MemLp (fun x => DΦ j x i) 2 (volume.restrict U))
    (hhw : ∀ x, h x = gε x - twoScaleGrad g G Φ DΦ x)
    {M : ℝ} (hM : 0 ≤ M) (hM0 : ∀ j x, |G j x| ≤ M)
    (hM1 : ∀ j i x, |coordinateDerivative i (G j) x| ≤ M)
    {N : Fin d → Fin d → ℝ} (hN0 : ∀ j i, 0 ≤ N j i)
    (hN : ∀ j i, negativeSobolevOneNorm 2 V
      (fun x => ((b x).mulVec (unitVector j + DΦ j x) - A.mulVec (unitVector j)) i) 0 ≤
        ENNReal.ofReal (N j i))
    {Y : ℝ} (hY : vectorRms volume U h ≤ Y) :
    vectorHatNegativeSobolevNorm U (fun x => (b x).mulVec (gε x) - A.mulVec (g x)) ≤
      ENNReal.ofReal (d * (volume U).toReal ^ ((1 : ℝ) / d) * (Λ * Y) +
        (volume U).toReal ^ ((1 : ℝ) / d) * ((volume U).toReal ^ (1 / 2 : ℝ))⁻¹ *
          (∑ k, l2 U (fun x => ((1 - η x) • ((b x).mulVec (g x) - A.mulVec (g x))) k) +
            ∑ j, ∑ k, l2 U (fun x => (b x).mulVec (Φ j x • gradient (G j) x) k)) +
        ((volume U).toReal ^ (1 / 2 : ℝ))⁻¹ * ((volume V).toReal ^ (1 / 2 : ℝ) *
          (M * ∑ j, ∑ i, N j i)) * ((1 + d) * (volume U).toReal ^ ((1 : ℝ) / d) + d)) := by
  have hUt : volume U ≠ ⊤ := (volume_lt_top_of_isBoundedDomain hU.2.1).ne
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUt
  have hΛ0 : 0 ≤ Λ := by linarith
  have hY0 : 0 ≤ Y := (Real.sqrt_nonneg _).trans hY
  set R := (volume U).toReal ^ ((1 : ℝ) / d) with hR
  set s := (volume U).toReal ^ (1 / 2 : ℝ) with hs
  have hR0 : 0 ≤ R := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hs0 : 0 ≤ s⁻¹ := inv_nonneg.2 (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  have hV0 : 0 ≤ (volume V).toReal ^ (1 / 2 : ℝ) := Real.rpow_nonneg ENNReal.toReal_nonneg _
  -- the memberships
  have hbM : ∀ {Q : Vec d → Vec d}, (∀ i, MemLp (fun x => Q x i) 2 (volume.restrict U)) →
      ∀ i, MemLp (fun x => (b x).mulVec (Q x) i) 2 (volume.restrict U) := fun hQ i =>
    memLp_coefficient_mulVec_apply b (memLp_pi_iff.2 hQ) i
  have hDe : ∀ j i, MemLp (fun x => (unitVector j + DΦ j x) i) 2 (volume.restrict U) :=
    fun j i => (memLp_const (unitVector (d := d) j i)).add (hDΦ j i)
  have hF : ∀ j i, MemLp (fun x => ((b x).mulVec (unitVector j + DΦ j x) -
      A.mulVec (unitVector j)) i) 2 (volume.restrict U) := fun j i =>
    (hbM (hDe j) i).sub (memLp_const _)
  have hΦG : ∀ j i, MemLp (fun x => (Φ j x • gradient (G j) x) i) 2 (volume.restrict U) :=
    fun j i => by
      have h := memLp_continuous_mul (continuous_gradient_apply (hG j) i)
        (hasCompactSupport_gradient_apply (hGc j) i) (hΦ j)
      refine h.ae_eq (Eventually.of_forall fun x => ?_)
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  have hΨ1 : ∀ k, MemLp (fun x => ((1 - η x) • ((b x).mulVec (g x) - A.mulVec (g x))) k) 2
      (volume.restrict U) := fun k => by
    have h1 : MemLp (fun x => 1 - η x) ⊤ (volume.restrict U) :=
      memLp_top_of_bound (continuous_const.sub hη).aestronglyMeasurable 1
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hη01 x])
    have h2 := MemLp.mul (r := 2) h1 ((hbM hg k).sub (memLp_const_mulVec A hg k))
    refine h2.ae_eq (Eventually.of_forall fun x => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.sub_apply]
  have hGF : ∀ j k, MemLp (fun x => G j x * ((b x).mulVec (unitVector j + DΦ j x) -
      A.mulVec (unitVector j)) k) 2 (volume.restrict U) := fun j k =>
    memLp_continuous_mul (hG j).continuous (hGc j) (hF j k)
  have hT4 : ∀ j k, 0 ≤ s⁻¹ * ((volume V).toReal ^ (1 / 2 : ℝ) * N j k) *
      ((M + d * M) * R + d * M) := fun j k =>
    mul_nonneg (mul_nonneg hs0 (mul_nonneg hV0 (hN0 j k)))
      (add_nonneg (mul_nonneg (add_nonneg hM (mul_nonneg (Nat.cast_nonneg d) hM)) hR0)
        (mul_nonneg (Nat.cast_nonneg d) hM))
  -- the decomposition of the flux
  have hdec : ∀ k, (fun x => ((b x).mulVec (gε x) - A.mulVec (g x)) k) =ᵐ[volume.restrict U]
      fun x => ((b x).mulVec (h x) k + ((1 - η x) • ((b x).mulVec (g x) - A.mulVec (g x))) k) +
        ∑ j, (b x).mulVec (Φ j x • gradient (G j) x) k +
        ∑ j, G j x * ((b x).mulVec (unitVector j + DΦ j x) - A.mulVec (unitVector j)) k := by
    intro k
    filter_upwards [hGη] with x hx
    have key := mulVec_twoScaleGrad_eq (b x) A (g x) (η x) (fun j => G j x) (fun j => Φ j x)
      (fun j => DΦ j x) (fun j => gradient (G j) x) hx
    have e1 : (b x).mulVec (gε x) = (b x).mulVec (h x) + (b x).mulVec (twoScaleGrad g G Φ DΦ x) := by
      rw [hhw x, Matrix.mulVec_sub, sub_add_cancel]
    rw [e1, twoScaleGrad, key]
    simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    ring
  -- the bound of each component
  have hk : ∀ k, hatNegativeSobolevNorm U (fun x => ((b x).mulVec (gε x) - A.mulVec (g x)) k) ≤
      ENNReal.ofReal (R * (Λ * Y) + R * s⁻¹ * l2 U (fun x =>
        ((1 - η x) • ((b x).mulVec (g x) - A.mulVec (g x))) k) +
        ∑ j, R * s⁻¹ * l2 U (fun x => (b x).mulVec (Φ j x • gradient (G j) x) k) +
        ∑ j, s⁻¹ * ((volume V).toReal ^ (1 / 2 : ℝ) * N j k) *
          ((M + d * M) * R + d * M)) := by
    intro k
    rw [hatNegativeSobolevNorm_congr_ae (hdec k)]
    have m1 : MemLp (fun x => (b x).mulVec (h x) k +
        ((1 - η x) • ((b x).mulVec (g x) - A.mulVec (g x))) k) 2 (volume.restrict U) :=
      (hbM hh k).add (hΨ1 k)
    have m2 : MemLp (fun x => ∑ j, (b x).mulVec (Φ j x • gradient (G j) x) k) 2
        (volume.restrict U) := memLp_finsetSum _ fun j _ => hbM (hΦG j) k
    have m3 : MemLp (fun x => ∑ j, G j x * ((b x).mulVec (unitVector j + DΦ j x) -
        A.mulVec (unitVector j)) k) 2 (volume.restrict U) := memLp_finsetSum _ fun j _ => hGF j k
    refine (hatNegativeSobolevNorm_add_le (m1.add m2) m3).trans ?_
    refine (add_le_add (hatNegativeSobolevNorm_add_le m1 m2) le_rfl).trans ?_
    refine (add_le_add (add_le_add (hatNegativeSobolevNorm_add_le (hbM hh k) (hΨ1 k))
      (hatNegativeSobolevNorm_finsetSum_le _ fun j _ => hbM (hΦG j) k))
      (hatNegativeSobolevNorm_finsetSum_le _ fun j _ => hGF j k)).trans ?_
    have b1 : hatNegativeSobolevNorm U (fun x => (b x).mulVec (h x) k) ≤
        ENNReal.ofReal (R * (Λ * Y)) :=
      hatNegativeSobolevNorm_le_rms' hU0 hUt (hbM hh k)
        ((scalarRms_apply_le_vectorRms hUt hU0 (hbM hh) k).trans
          ((vectorRms_mulVec_le hΛ0 b hh hUt).trans (mul_le_mul_of_nonneg_left hY hΛ0)))
    have b2 : hatNegativeSobolevNorm U (fun x =>
        ((1 - η x) • ((b x).mulVec (g x) - A.mulVec (g x))) k) ≤
        ENNReal.ofReal (R * s⁻¹ * l2 U (fun x =>
          ((1 - η x) • ((b x).mulVec (g x) - A.mulVec (g x))) k)) := by
      rw [mul_assoc]
      exact hatNegativeSobolevNorm_le_rms' hU0 hUt (hΨ1 k)
        (scalarRms_eq_inv_mul_l2 hUt hU0 (hΨ1 k)).le
    have b3 : ∀ j, hatNegativeSobolevNorm U (fun x => (b x).mulVec (Φ j x • gradient (G j) x) k)
        ≤ ENNReal.ofReal (R * s⁻¹ * l2 U (fun x => (b x).mulVec (Φ j x • gradient (G j) x) k)) :=
      fun j => by
        rw [mul_assoc]
        exact hatNegativeSobolevNorm_le_rms' hU0 hUt (hbM (hΦG j) k)
          (scalarRms_eq_inv_mul_l2 hUt hU0 (hbM (hΦG j) k)).le
    have b4 : ∀ j, hatNegativeSobolevNorm U (fun x => G j x *
        ((b x).mulVec (unitVector j + DΦ j x) - A.mulVec (unitVector j)) k) ≤
        ENNReal.ofReal (s⁻¹ * ((volume V).toReal ^ (1 / 2 : ℝ) * N j k) *
          ((M + d * M) * R + d * M)) := fun j =>
      hatNegativeSobolevNorm_mul_le hU hUV hV1 hVt (hG j) (hGc j) (hGU j) hM hM (hM0 j)
        (fun i x => hM1 j i x) (hF j k) (hN0 j k) (hN j k)
    have hl : ∀ f : Vec d → ℝ, 0 ≤ l2 U f := l2_nonneg U
    have p1 : 0 ≤ R * (Λ * Y) := mul_nonneg hR0 (mul_nonneg hΛ0 hY0)
    have p2 := mul_nonneg (mul_nonneg hR0 hs0) (hl (fun x =>
      ((1 - η x) • ((b x).mulVec (g x) - A.mulVec (g x))) k))
    have p3 : 0 ≤ ∑ j, R * s⁻¹ * l2 U (fun x => (b x).mulVec (Φ j x • gradient (G j) x) k) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg hR0 hs0) (hl _)
    rw [ENNReal.ofReal_add (add_nonneg (add_nonneg p1 p2) p3)
        (Finset.sum_nonneg fun j _ => hT4 j k),
      ENNReal.ofReal_add (add_nonneg p1 p2) p3, ENNReal.ofReal_add p1 p2,
      ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (mul_nonneg hR0 hs0) (hl _)),
      ENNReal.ofReal_sum_of_nonneg (fun j _ => hT4 j k)]
    exact add_le_add (add_le_add (add_le_add b1 b2) (Finset.sum_le_sum fun j _ => b3 j))
      (Finset.sum_le_sum fun j _ => b4 j)
  unfold vectorHatNegativeSobolevNorm
  refine (Finset.sum_le_sum fun k _ => hk k).trans ?_
  have hl : ∀ f : Vec d → ℝ, 0 ≤ l2 U f := l2_nonneg U
  rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => by
    refine add_nonneg (add_nonneg (add_nonneg (mul_nonneg hR0 (mul_nonneg hΛ0 hY0))
      (mul_nonneg (mul_nonneg hR0 hs0) (hl _)))
      (Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg hR0 hs0) (hl _)))
      (Finset.sum_nonneg fun j _ => hT4 j k)]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [Finset.sum_comm (f := fun k j => R * s⁻¹ * l2 U (fun x =>
      (b x).mulVec (Φ j x • gradient (G j) x) k)),
    Finset.sum_comm (f := fun k j => s⁻¹ * ((volume V).toReal ^ (1 / 2 : ℝ) * N j k) *
      ((M + d * M) * R + d * M))]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  have hNs : 0 ≤ ∑ j, ∑ i, N j i := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ =>
    hN0 j i
  have e : (M + d * M) * R + d * M = M * ((1 + d) * R + d) := by ring
  rw [e]
  have : s⁻¹ * ((volume V).toReal ^ (1 / 2 : ℝ) * ∑ j, ∑ i, N j i) * (M * ((1 + d) * R + d)) =
      s⁻¹ * ((volume V).toReal ^ (1 / 2 : ℝ) * (M * ∑ j, ∑ i, N j i)) * ((1 + d) * R + d) := by
    ring
  linarith

end TwoScale

end QSH
