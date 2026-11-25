import QuantitativeStochasticHomogenization.Ch08.Sec01.ParabolicCutoff

/-!
# The right-hand side of the parabolic Caccioppoli inequality on a time slice

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 8.1, proof of Lemma 8.1, the bound of the pairing of `u* = ∇·F` with the test function
`η² u` at a fixed time: for `w ∈ H¹(U)` and a smooth cutoff `0 ≤ φ ≤ 1` with compact support in
`U` and `|∇φ| ≤ K`,
`|∫_U F · ∇(φ² w)| ≤ 4d² |U| ‖∇·F‖²_{H̲⁻¹(U)} + (ρ + 2dK)²/(8d²) ∫_U w² + 1/8 ∫_U φ² |∇w|²`
with `ρ = |U|^{-1/d}`. It follows from `|∫_U F · ∇v| ≤ |U| ‖∇·F‖_{H̲⁻¹(U)} ‖v‖_{H̲¹(U)}` for
`v = φ² w ∈ H¹₀(U)` and Young's inequality.

Also: the flux `a∇u + F` of a weak solution is square integrable.
-/

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

/-- Young's inequality in the form used for the pairing bound. -/
theorem young_pairing_aux {V H h y xx A D : ℝ} (hV : 0 ≤ V) (hH : 0 ≤ H) (hD : 0 < D)
    (hh : h ≤ A * y + D * xx) :
    V * (H * h) ≤ 4 * D ^ 2 * V * H ^ 2 + A ^ 2 / (8 * D ^ 2) * (V * y ^ 2) +
      1 / 8 * (V * xx ^ 2) := by
  set S := A * y + D * xx with hS
  have h1 : H * h ≤ H * S := mul_le_mul_of_nonneg_left hh hH
  have e : 4 * D ^ 2 * H ^ 2 + S ^ 2 / (16 * D ^ 2) - H * S = (2 * D * H - S / (4 * D)) ^ 2 := by
    field_simp
    ring
  have h2 : H * S ≤ 4 * D ^ 2 * H ^ 2 + S ^ 2 / (16 * D ^ 2) := by
    nlinarith [sq_nonneg (2 * D * H - S / (4 * D))]
  have h3 : S ^ 2 ≤ 2 * A ^ 2 * y ^ 2 + 2 * D ^ 2 * xx ^ 2 := by
    rw [hS]
    nlinarith [sq_nonneg (A * y - D * xx)]
  have h4 : S ^ 2 / (16 * D ^ 2) ≤ A ^ 2 / (8 * D ^ 2) * y ^ 2 + 1 / 8 * xx ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have e2 : (A ^ 2 / (8 * D ^ 2) * y ^ 2 + 1 / 8 * xx ^ 2) * (16 * D ^ 2) =
        2 * A ^ 2 * y ^ 2 + 2 * D ^ 2 * xx ^ 2 := by
      field_simp
      ring
    rw [e2]
    exact h3
  have h5 : H * h ≤ 4 * D ^ 2 * H ^ 2 + (A ^ 2 / (8 * D ^ 2) * y ^ 2 + 1 / 8 * xx ^ 2) := by
    linarith
  have h6 := mul_le_mul_of_nonneg_left h5 hV
  nlinarith [h6]

/-- **The pairing bound on a time slice.** -/
theorem slicePairing_le (hd : 0 < d) {U : Set (Vec d)} (hU : PDE.IsOpenBoundedConvexDomain U)
    (hU0 : volume U ≠ 0) (hUfin : volume U ≠ ⊤) (w : PDE.H1Function U) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) {K : ℝ} (hK : 0 ≤ K)
    (hgφ : ∀ x, PDE.vecNormSq (PDE.classicalGradient φ x) ≤ K ^ 2) {F : Vec d → Vec d}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict U)) :
    ENNReal.ofReal |∫ x in U, ∑ i, F x i *
        (φ x ^ 2 * w.grad x i + 2 * φ x * w x * PDE.classicalGradient φ x i)| ≤
      ENNReal.ofReal (4 * d ^ 2 * volume.real U) *
          negativeSobolevOneNorm 2 U (fun _ => 0) F ^ 2 +
        ENNReal.ofReal (((volume U).toReal ^ (-(1 : ℝ) / d) + 2 * d * K) ^ 2 / (8 * d ^ 2) *
            (∫ x in U, w x ^ 2) +
          1 / 8 * ∫ x in U, φ x ^ 2 * PDE.vecNormSq (w.grad x)) := by
  have hUpos : 0 < volume.real U :=
    ENNReal.toReal_pos hU0 hUfin
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set N := negativeSobolevOneNorm 2 U (fun _ => 0) F with hNdef
  by_cases hNtop : N = ⊤
  · rw [hNtop, ENNReal.top_pow two_ne_zero,
      ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by positivity)).ne', top_add]
    exact le_top
  set H := N.toReal with hHdef
  have hH0 : 0 ≤ H := ENNReal.toReal_nonneg
  have hHeq : N = ENNReal.ofReal H := (ENNReal.ofReal_toReal hNtop).symm
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUfin
  obtain ⟨v, hvfun, hvgrad⟩ := exists_h10_cutoff_sq_test hU w 0 hφ hφc hφU
  simp only [sub_zero] at hvfun hvgrad
  have hpair := abs_integral_pairing_le_of_h10 hUfin (f := fun _ => 0) MemLp.zero hF hH0
    hHeq.le v
  have hP : ∫ x in U, ∑ i, F x i *
      (φ x ^ 2 * w.grad x i + 2 * φ x * w x * PDE.classicalGradient φ x i) =
      ∫ x in U, PDE.vecDot (F x) (v.toH1Function.grad x) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hvgrad x, PDE.vecDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [zero_mul, integral_zero, zero_sub, abs_neg] at hpair
  rw [← hP] at hpair
  -- the normalized norms of the test function
  have hw : MemLp (fun x => w x) 2 (volume.restrict U) := w.memL2
  have hg' : PDE.MemVectorL2On U w.grad := w.gradMemL2
  have hw_int : IntegrableOn (fun x => w x ^ 2) U := hw.integrable_sq
  have hφcont : Continuous φ := hφ.continuous
  have hgsq_int : IntegrableOn (fun x => PDE.vecNormSq (w.grad x)) U :=
    PDE.integrableOn_vecDot_of_memVectorL2On hg' hg'
  have hφ2E_int : IntegrableOn (fun x => φ x ^ 2 * PDE.vecNormSq (w.grad x)) U := by
    refine hgsq_int.bdd_mul (c := 1) (hφcont.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (hφ0 x) (hφ1 x)
  have havg0 : 0 ≤ ⨍ x in U, w x ^ 2 ∂volume := by
    rw [setAverage_eq, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr measureReal_nonneg) (integral_nonneg fun x => sq_nonneg _)
  have havg1 : 0 ≤ ⨍ x in U, φ x ^ 2 * PDE.vecNormSq (w.grad x) ∂volume := by
    rw [setAverage_eq, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr measureReal_nonneg)
      (integral_nonneg fun x => mul_nonneg (sq_nonneg _) (PDE.vecNormSq_nonneg _))
  set y := Real.sqrt (⨍ x in U, w x ^ 2 ∂volume) with hydef
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hy2 : volume.real U * y ^ 2 = ∫ x in U, w x ^ 2 := by
    rw [hydef, Real.sq_sqrt havg0, setAverage_eq, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ hUpos.ne', one_mul]
  set xx := Real.sqrt (⨍ x in U, φ x ^ 2 * PDE.vecNormSq (w.grad x) ∂volume) with hxxdef
  have hxx0 : 0 ≤ xx := Real.sqrt_nonneg _
  have hxx2 : volume.real U * xx ^ 2 = ∫ x in U, φ x ^ 2 * PDE.vecNormSq (w.grad x) := by
    rw [hxxdef, Real.sq_sqrt havg1, setAverage_eq, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ hUpos.ne', one_mul]
  have hvmeas : AEStronglyMeasurable (fun x => v.toH1Function x) (volume.restrict U) :=
    v.toH1Function.memL2.aestronglyMeasurable
  have hT0 : (PDE.eLpMeanNormOn U 2 v.toH1Function.toFun).toReal ≤ y := by
    have hpt0 : ∀ x, (v.toH1Function x) ^ 2 ≤ w x ^ 2 := by
      intro x
      rw [hvfun x, show φ x * (φ x * w x) = (φ x * φ x) * w x by ring, mul_pow]
      have h2 : (φ x * φ x) ^ 2 ≤ 1 :=
        pow_le_one₀ (mul_nonneg (hφ0 x) (hφ0 x))
          ((mul_le_of_le_one_left (hφ0 x) (hφ1 x)).trans (hφ1 x))
      exact mul_le_of_le_one_left (sq_nonneg _) h2
    have h := eLpMeanNormOn_two_le_ofReal_sqrt hU0 hvmeas hw_int (Eventually.of_forall hpt0)
    exact ENNReal.toReal_le_of_le_ofReal hy0 h
  have hgφ_cont : ∀ i, Continuous fun x => PDE.classicalGradient φ x i := fun i =>
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hTi : ∀ i : Fin d,
      (PDE.eLpMeanNormOn U 2 (fun x => v.toH1Function.grad x i)).toReal ≤ xx + 2 * K * y := by
    intro i
    have hsplit : (fun x => v.toH1Function.grad x i) =
        (fun x => φ x ^ 2 * w.grad x i) +
          fun x => 2 * φ x * w x * PDE.classicalGradient φ x i := by
      funext x
      rw [hvgrad x]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hm1 : AEStronglyMeasurable (fun x => φ x ^ 2 * w.grad x i) (volume.restrict U) :=
      (hφcont.pow 2).aestronglyMeasurable.mul (w.gradMemL2 i).aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (fun x => 2 * φ x * w x * PDE.classicalGradient φ x i)
        (volume.restrict U) :=
      ((continuous_const.mul hφcont).aestronglyMeasurable.mul hw.aestronglyMeasurable).mul
        (hgφ_cont i).aestronglyMeasurable
    have hpt1 : ∀ x, (φ x ^ 2 * w.grad x i) ^ 2 ≤ φ x ^ 2 * PDE.vecNormSq (w.grad x) := by
      intro x
      have hgi := sq_apply_le_vecNormSq (w.grad x) i
      have hp : φ x ^ 2 ≤ 1 := pow_le_one₀ (hφ0 x) (hφ1 x)
      have hp0 : 0 ≤ φ x ^ 2 := sq_nonneg _
      calc (φ x ^ 2 * w.grad x i) ^ 2 = φ x ^ 2 * (φ x ^ 2 * w.grad x i ^ 2) := by ring
        _ ≤ φ x ^ 2 * (1 * PDE.vecNormSq (w.grad x)) := by
          refine mul_le_mul_of_nonneg_left ?_ hp0
          exact mul_le_mul hp hgi (sq_nonneg _) zero_le_one
        _ = φ x ^ 2 * PDE.vecNormSq (w.grad x) := by ring
    have hpt2 : ∀ x, (2 * φ x * w x * PDE.classicalGradient φ x i) ^ 2 ≤ 4 * K ^ 2 * w x ^ 2 := by
      intro x
      have hgi := (sq_apply_le_vecNormSq (PDE.classicalGradient φ x) i).trans (hgφ x)
      have hp : φ x ^ 2 ≤ 1 := pow_le_one₀ (hφ0 x) (hφ1 x)
      calc (2 * φ x * w x * PDE.classicalGradient φ x i) ^ 2 =
          4 * w x ^ 2 * (φ x ^ 2 * PDE.classicalGradient φ x i ^ 2) := by ring
        _ ≤ 4 * w x ^ 2 * (1 * K ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul hp hgi (sq_nonneg _) zero_le_one
        _ = 4 * K ^ 2 * w x ^ 2 := by ring
    have h1 := eLpMeanNormOn_two_le_ofReal_sqrt hU0 hm1 hφ2E_int (Eventually.of_forall hpt1)
    have h4int : IntegrableOn (fun x => 4 * K ^ 2 * w x ^ 2) U := hw_int.const_mul _
    have h2 := eLpMeanNormOn_two_le_ofReal_sqrt hU0 hm2 h4int (Eventually.of_forall hpt2)
    have hKyeq : Real.sqrt (⨍ x in U, 4 * K ^ 2 * w x ^ 2 ∂volume) = 2 * K * y := by
      rw [setAverage_eq, smul_eq_mul, integral_const_mul, hydef, setAverage_eq,
        smul_eq_mul, mul_left_comm, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
        Real.sqrt_sq hK, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← hxxdef] at h1
    rw [hKyeq] at h2
    have hsum : PDE.eLpMeanNormOn U 2 (fun x => v.toH1Function.grad x i) ≤
        ENNReal.ofReal xx + ENNReal.ofReal (2 * K * y) := by
      rw [hsplit]
      exact (eLpNorm_add_le (by norm_num)).trans (add_le_add h1 h2)
    rw [← ENNReal.ofReal_add hxx0 (by positivity)] at hsum
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hsum
  set ρ := (volume U).toReal ^ (-(1 : ℝ) / d) with hρdef
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hT : h10TestNorm U v ≤ (ρ + 2 * d * K) * y + d * xx := by
    unfold h10TestNorm
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hTi i
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have := mul_le_mul_of_nonneg_left hT0 hρ0
    nlinarith
  have hmain := young_pairing_aux (V := volume.real U) measureReal_nonneg hH0 hdR hT
  rw [hy2, hxx2] at hmain
  have hfinal := hpair.trans hmain
  have hR0 : 0 ≤ (ρ + 2 * d * K) ^ 2 / (8 * d ^ 2) * (∫ x in U, w x ^ 2) +
      1 / 8 * ∫ x in U, φ x ^ 2 * PDE.vecNormSq (w.grad x) := by
    have h1 : 0 ≤ ∫ x in U, w x ^ 2 := integral_nonneg fun x => sq_nonneg _
    have h2 : 0 ≤ ∫ x in U, φ x ^ 2 * PDE.vecNormSq (w.grad x) :=
      integral_nonneg fun x => mul_nonneg (sq_nonneg _) (PDE.vecNormSq_nonneg _)
    positivity
  calc ENNReal.ofReal |∫ x in U, ∑ i, F x i *
        (φ x ^ 2 * w.grad x i + 2 * φ x * w x * PDE.classicalGradient φ x i)|
      ≤ ENNReal.ofReal (4 * d ^ 2 * volume.real U * H ^ 2 +
          ((ρ + 2 * d * K) ^ 2 / (8 * d ^ 2) * (∫ x in U, w x ^ 2) +
            1 / 8 * ∫ x in U, φ x ^ 2 * PDE.vecNormSq (w.grad x))) := by
        exact ENNReal.ofReal_le_ofReal (hfinal.trans_eq (add_assoc _ _ _))
    _ = ENNReal.ofReal (4 * d ^ 2 * volume.real U) * N ^ 2 +
        ENNReal.ofReal ((ρ + 2 * d * K) ^ 2 / (8 * d ^ 2) * (∫ x in U, w x ^ 2) +
          1 / 8 * ∫ x in U, φ x ^ 2 * PDE.vecNormSq (w.grad x)) := by
        rw [ENNReal.ofReal_add (by positivity) hR0, ENNReal.ofReal_mul (by positivity), hHeq,
          ENNReal.ofReal_pow hH0]

end QSH
