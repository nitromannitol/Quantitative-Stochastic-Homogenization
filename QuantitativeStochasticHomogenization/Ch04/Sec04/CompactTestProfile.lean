import QuantitativeStochasticHomogenization.Ch04.Sec04.CompactTestPairing
import HCPoly.Geometry.OperatorOrder

/-!
# The compact profile adapted to the homogenized matrix

The compact profile `ρ` and its partner `χ` of the finite-ball estimate (consultant note T22, (2))
of the proof of Lemma 4.21 in Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization
and Large-Scale Regularity*.

The base pair is `χ₀(y) = -S(1 - |y|²)` and `ρ₀(y) = 2 S'(1 - |y|²)` with the smooth transition
`S`, so that `∇χ₀(y) = y ρ₀(y)`, both vanish for `|y| > 1`, and `ρ₀ ≥ 0` with `∫ ρ₀ > 0`.
For a symmetric matrix `D` with `|ξ|² ≤ ξ·Dξ ≤ K|ξ|²` and a frame `A` with `D Aᵀ A = 1`
(`ProfileFrame`), the adapted pair is `ρ(y) = c ρ₀(A' y)`, `χ(y) = r² c χ₀(A' y)` with
`A' = r⁻¹ A`, `r = 1/(2√K)` and `c = |det A'| / ∫ ρ₀`: then `D∇χ = y ρ`, `∫ ρ = 1`, and both vanish
outside `B_{1/2}`. Differentiating `D∇χ = yρ` gives
`∑ᵢⱼ Dᵢⱼ ∂ᵢ∂ⱼχ = d ρ + y · ∇ρ`, and applying `∂^α` gives the identity
`∑ᵢⱼ Dᵢⱼ ∂ᵢ∂ⱼ ∂^αχ = (d + |α|) ∂^αρ + y · ∇∂^αρ` (`ScaleIdentity`), which is
`∂_b ρ_b = b L χ_b` for `ρ_b = b^{-d} ρ(·/b)` and its derivatives. The bounds of all derivatives
of `ρ` and `χ` depend only on `d`, `K` and the order.
-/

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace QSH

variable {d : ℕ}

/-! ## The base pair -/

/-- The base partner `χ₀(y) = -S(1 - |y|²)`. -/
def baseChi (y : Vec d) : ℝ := -Real.smoothTransition (1 - euclideanSq y)

/-- The base profile `ρ₀(y) = 2 S'(1 - |y|²)`. -/
def baseRho (y : Vec d) : ℝ := 2 * deriv Real.smoothTransition (1 - euclideanSq y)

theorem contDiff_euclideanSq : ContDiff ℝ ∞ (euclideanSq : Vec d → ℝ) := by
  unfold euclideanSq dot
  fun_prop

theorem contDiff_deriv_smoothTransition : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
  (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2

theorem contDiff_baseChi : ContDiff ℝ ∞ (baseChi : Vec d → ℝ) :=
  (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_euclideanSq)).neg

theorem contDiff_baseRho : ContDiff ℝ ∞ (baseRho : Vec d → ℝ) :=
  contDiff_const.mul (contDiff_deriv_smoothTransition.comp (contDiff_const.sub contDiff_euclideanSq))

theorem baseChi_eq_zero {y : Vec d} (hy : 1 ≤ euclideanSq y) : baseChi y = 0 := by
  rw [baseChi, Real.smoothTransition.zero_of_nonpos (by linarith), neg_zero]

theorem deriv_smoothTransition_eq_zero {x : ℝ} (hx : x < 0) : deriv Real.smoothTransition x = 0 := by
  have h : Real.smoothTransition =ᶠ[nhds x] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
  rw [h.deriv_eq, deriv_const]

theorem baseRho_eq_zero {y : Vec d} (hy : 1 < euclideanSq y) : baseRho y = 0 := by
  rw [baseRho, deriv_smoothTransition_eq_zero (by linarith), mul_zero]

theorem isCompact_euclideanSq_le (r : ℝ) : IsCompact {y : Vec d | euclideanSq y ≤ r} := by
  have hc : Continuous (euclideanSq : Vec d → ℝ) := contDiff_euclideanSq.continuous
  refine (isCompact_closedBall (0 : Vec d) (|r| + 1)).of_isClosed_subset
    (isClosed_le hc continuous_const) fun y hy => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (norm_le_euclideanNorm' y).trans ?_
  have h1 : euclideanSq y ≤ |r| + 1 := le_trans (Set.mem_ofPred_eq ▸ hy) (by
    linarith [le_abs_self r])
  calc euclideanNorm y = Real.sqrt (euclideanSq y) := rfl
    _ ≤ Real.sqrt ((|r| + 1) ^ 2) := Real.sqrt_le_sqrt (h1.trans (by
        nlinarith [abs_nonneg r]))
    _ = |r| + 1 := Real.sqrt_sq (by positivity)

theorem hasCompactSupport_baseChi : HasCompactSupport (baseChi : Vec d → ℝ) :=
  HasCompactSupport.intro (isCompact_euclideanSq_le 1) fun _ hy =>
    baseChi_eq_zero (le_of_lt (not_le.mp hy))

theorem hasCompactSupport_baseRho : HasCompactSupport (baseRho : Vec d → ℝ) :=
  HasCompactSupport.intro (isCompact_euclideanSq_le 1) fun _ hy => baseRho_eq_zero (not_le.mp hy)

theorem euclideanSq_unitVector' (i : Fin d) : euclideanSq (unitVector i : Vec d) = 1 := by
  simp [euclideanSq, dot, unitVector, Pi.single_apply]

theorem euclideanSq_smul' (c : ℝ) (v : Vec d) : euclideanSq (c • v) = c ^ 2 * euclideanSq v := by
  simp only [euclideanSq, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem coordinateDerivative_coord (i l : Fin d) (y : Vec d) :
    coordinateDerivative i (fun y : Vec d => y l) y = if l = i then 1 else 0 := by
  unfold coordinateDerivative
  rw [(hasFDerivAt_apply (𝕜 := ℝ) l y).fderiv]
  change (unitVector i : Vec d) l = _
  simp [unitVector, Pi.single_apply]

theorem coordinateDerivative_mul_coord {f : Vec d → ℝ} (hf : Differentiable ℝ f) (i l : Fin d)
    (y : Vec d) :
    coordinateDerivative i (fun y => y l * f y) y =
      (if l = i then f y else 0) + y l * coordinateDerivative i f y := by
  have h1 : HasFDerivAt (fun y : Vec d => y l) (ContinuousLinearMap.proj l : Vec d →L[ℝ] ℝ) y :=
    hasFDerivAt_apply l y
  have h : HasFDerivAt (fun y => y l * f y)
      (y l • fderiv ℝ f y + f y • (ContinuousLinearMap.proj l : Vec d →L[ℝ] ℝ)) y :=
    h1.mul (hf y).hasFDerivAt
  unfold coordinateDerivative
  rw [h.fderiv]
  change y l * fderiv ℝ f y (unitVector i) + f y * (unitVector i : Vec d) l = _
  by_cases hli : l = i
  · subst hli
    simp [unitVector]
    ring
  · simp [unitVector, hli]

theorem coordinateDerivative_add' {F G : Vec d → ℝ} (hF : Differentiable ℝ F)
    (hG : Differentiable ℝ G) (i : Fin d) (y : Vec d) :
    coordinateDerivative i (fun y => F y + G y) y =
      coordinateDerivative i F y + coordinateDerivative i G y := by
  unfold coordinateDerivative
  rw [fderiv_fun_add (hF y) (hG y)]
  rfl

theorem coordinateDerivative_finset_sum' {ι : Type*} (s : Finset ι) {G : ι → Vec d → ℝ}
    (hG : ∀ l, Differentiable ℝ (G l)) (i : Fin d) (y : Vec d) :
    coordinateDerivative i (fun y => ∑ l ∈ s, G l y) y =
      ∑ l ∈ s, coordinateDerivative i (G l) y := by
  have h := coordinateDerivative_sum_const_mul s (fun _ => (1 : ℝ)) hG i y
  simpa using h

/-- The chain rule for `y ↦ g(q(y))` with a scalar `g`. -/
theorem coordinateDerivative_comp_real {g : ℝ → ℝ} {g' : ℝ} {q : Vec d → ℝ} {y : Vec d}
    (hg : HasDerivAt g g' (q y)) (hq : DifferentiableAt ℝ q y) (i : Fin d) :
    coordinateDerivative i (fun y => g (q y)) y = g' * coordinateDerivative i q y := by
  unfold coordinateDerivative
  change fderiv ℝ (g ∘ q) y (unitVector i) = _
  rw [(hg.comp_hasFDerivAt y hq.hasFDerivAt).fderiv]
  rfl

theorem coordinateDerivative_euclideanSq (i : Fin d) (y : Vec d) :
    coordinateDerivative i euclideanSq y = 2 * y i := by
  have e : (euclideanSq : Vec d → ℝ) = fun y => ∑ l, y l * (fun y : Vec d => y l) y := rfl
  have hd : ∀ l : Fin d, Differentiable ℝ (fun y : Vec d => y l * (fun y : Vec d => y l) y) :=
    fun l => (differentiable_apply l).mul (differentiable_apply l)
  rw [e, coordinateDerivative_finset_sum' _ hd]
  simp only [coordinateDerivative_mul_coord (differentiable_apply _), coordinateDerivative_coord]
  simp [Finset.sum_add_distrib, Finset.sum_ite_eq']
  ring

theorem coordinateDerivative_baseChi (i : Fin d) (y : Vec d) :
    coordinateDerivative i baseChi y = y i * baseRho y := by
  have hS : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (1 - euclideanSq y))
      (1 - euclideanSq y) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
  have hg : HasDerivAt (fun r : ℝ => -Real.smoothTransition (1 - r))
      (deriv Real.smoothTransition (1 - euclideanSq y)) (euclideanSq y) := by
    have h1 : HasDerivAt (fun r : ℝ => 1 - r) (-1) (euclideanSq y) := by
      simpa using (hasDerivAt_id (euclideanSq y)).const_sub 1
    have h2 : HasDerivAt (fun r : ℝ => -Real.smoothTransition (1 - r))
        (-(deriv Real.smoothTransition (1 - euclideanSq y) * -1)) (euclideanSq y) :=
      (hS.comp (euclideanSq y) h1).neg
    convert h2 using 1
    ring
  have e : (baseChi : Vec d → ℝ) = fun y => (fun r : ℝ => -Real.smoothTransition (1 - r))
      (euclideanSq y) := rfl
  rw [e, coordinateDerivative_comp_real hg
    (contDiff_euclideanSq.differentiable (by simp) y), coordinateDerivative_euclideanSq, baseRho]
  ring

theorem baseRho_nonneg (y : Vec d) : 0 ≤ baseRho y :=
  mul_nonneg zero_le_two Real.smoothTransition.monotone.deriv_nonneg

theorem exists_deriv_smoothTransition_pos :
    ∃ c ∈ Set.Ioo (0 : ℝ) 1, 0 < deriv Real.smoothTransition c := by
  obtain ⟨c, hc, hd⟩ := exists_deriv_eq_slope Real.smoothTransition zero_lt_one
    Real.smoothTransition.continuous.continuousOn
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero).differentiableOn
  refine ⟨c, hc, ?_⟩
  rw [hd, Real.smoothTransition.one_of_one_le le_rfl, Real.smoothTransition.zero_of_nonpos le_rfl]
  norm_num

theorem integral_baseRho_pos (hd : 0 < d) : 0 < ∫ y : Vec d, baseRho y := by
  obtain ⟨c, hc, hpos⟩ := exists_deriv_smoothTransition_pos
  set y : Vec d := Real.sqrt (1 - c) • unitVector ⟨0, hd⟩ with hy
  have hq : euclideanSq y = 1 - c := by
    have h1 : euclideanSq (unitVector (⟨0, hd⟩ : Fin d)) = 1 := euclideanSq_unitVector' _
    have : euclideanSq y = Real.sqrt (1 - c) ^ 2 * euclideanSq (unitVector (⟨0, hd⟩ : Fin d)) := by
      simp only [hy, euclideanSq, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, h1, mul_one, Real.sq_sqrt (by linarith [hc.2])]
  refine contDiff_baseRho.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    hasCompactSupport_baseRho baseRho_nonneg (x := y) ?_
  rw [baseRho, hq, show 1 - (1 - c) = c by ring]
  exact (mul_pos zero_lt_two hpos).ne'

/-! ## Frames of a symmetric matrix -/

/-- A frame `A` of the symmetric matrix `D`: `D Aᵀ A = 1`, the entries of `A` lie in `[-1, 1]`,
and `|y|² ≤ K |A y|²`. -/
structure ProfileFrame (D A : Mat d) (K : ℝ) : Prop where
  det_ne : A.det ≠ 0
  inv : ∀ y, D.mulVec (A.transpose.mulVec (A.mulVec y)) = y
  entry : ∀ l i, |A l i| ≤ 1
  norm : ∀ y, euclideanSq y ≤ K * euclideanSq (A.mulVec y)

theorem dot_mulVec_left' (M : Mat d) (u v : Vec d) :
    dot (M.mulVec u) v = dot u (M.transpose.mulVec v) := by
  change dotProduct (M.mulVec u) v = dotProduct u (M.transpose.mulVec v)
  rw [Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]

/-- **A frame from the square root**: `A = (√D)⁻¹`. -/
theorem exists_profileFrame {D : Mat d} (hDs : D.transpose = D) {K : ℝ}
    (hlow : ∀ ξ : Vec d, euclideanSq ξ ≤ dot ξ (D.mulVec ξ))
    (hup : ∀ ξ : Vec d, dot ξ (D.mulVec ξ) ≤ K * euclideanSq ξ) : ∃ A, ProfileFrame D A K := by
  have hpd : D.PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨by rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hDs],
      fun x hx => ?_⟩
    have h1 := hlow x
    have h2 : 0 < euclideanSq x := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
      have : 0 < x i * x i := mul_self_pos.mpr hi
      unfold euclideanSq dot
      exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun j => x j * x j)
        (fun j _ => mul_self_nonneg _) (Finset.mem_univ i))
    have e : dotProduct (star x) (D.mulVec x) = dot x (D.mulVec x) := rfl
    rw [e]
    linarith
  obtain ⟨hMpsd, hMM⟩ := Homogenization.HighContrast.matSqrt_spec hpd.posSemidef
  set M := Homogenization.HighContrast.matSqrt D with hMdef
  have hMu : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).mp
    (Homogenization.HighContrast.isUnit_matSqrt hpd)
  have hMT : M.transpose = M := by
    have h := hMpsd.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  set A := M⁻¹ with hAdef
  have hMA : M * A = 1 := Matrix.mul_nonsing_inv M hMu
  have hAM : A * M = 1 := Matrix.nonsing_inv_mul M hMu
  have hAT : A.transpose = A := by rw [hAdef, Matrix.transpose_nonsing_inv, hMT]
  have hMAv : ∀ y, M.mulVec (A.mulVec y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, hMA, Matrix.one_mulVec]
  have hdotM : ∀ w, euclideanSq (M.mulVec w) = dot w (D.mulVec w) := fun w => by
    unfold euclideanSq
    rw [dot_mulVec_left', hMT, Matrix.mulVec_mulVec, hMM]
  have hAsq : ∀ x, euclideanSq (A.mulVec x) ≤ euclideanSq x := fun x => by
    have := hlow (A.mulVec x)
    rw [← hdotM, hMAv] at this
    exact this
  refine ⟨A, ?_, fun y => ?_, fun l i => ?_, fun y => ?_⟩
  · have h : A.det * M.det = 1 := by rw [← Matrix.det_mul, hAM, Matrix.det_one]
    exact left_ne_zero_of_mul_eq_one h
  · rw [hAT, ← hMM, ← Matrix.mulVec_mulVec, hMAv, hMAv]
  · have h1 : (A.mulVec (unitVector i)) l = A l i := by
      simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply]
    rw [← h1]
    refine (abs_apply_le_euclideanNorm _ l).trans ?_
    have h2 := hAsq (unitVector i)
    rw [euclideanSq_unitVector'] at h2
    calc euclideanNorm (A.mulVec (unitVector i)) = Real.sqrt (euclideanSq (A.mulVec (unitVector i))) :=
          rfl
      _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h2
      _ = 1 := Real.sqrt_one
  · have := hup (A.mulVec y)
    rw [← hdotM, hMAv] at this
    exact this

/-! ## The adapted pair -/

/-- The radius `r = 1/(2√K)` of the base profile in the frame. -/
def frameRadius (K : ℝ) : ℝ := (2 * Real.sqrt K)⁻¹

/-- The rescaled frame `A' = r⁻¹ A`. -/
def frameMatrix (A : Mat d) (K : ℝ) : Mat d := (frameRadius K)⁻¹ • A

/-- The normalizing constant `c = |det A'| / ∫ ρ₀`. -/
def frameConst (A : Mat d) (K : ℝ) : ℝ := |(frameMatrix A K).det| / ∫ y : Vec d, baseRho y

/-- **The adapted profile** `ρ(y) = c ρ₀(A' y)`. -/
def adaptedRho (A : Mat d) (K : ℝ) (y : Vec d) : ℝ :=
  frameConst A K * baseRho ((frameMatrix A K).mulVec y)

/-- **The adapted partner** `χ(y) = r² c χ₀(A' y)`. -/
def adaptedChi (A : Mat d) (K : ℝ) (y : Vec d) : ℝ :=
  frameRadius K ^ 2 * frameConst A K * baseChi ((frameMatrix A K).mulVec y)

variable {D A : Mat d} {K : ℝ}

theorem frameRadius_pos (hK : 0 < K) : 0 < frameRadius K := by
  unfold frameRadius
  have := Real.sqrt_pos.mpr hK
  positivity

theorem frameMatrix_det_ne (hA : ProfileFrame D A K) (hK : 0 < K) : (frameMatrix A K).det ≠ 0 := by
  unfold frameMatrix
  rw [Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (frameRadius_pos hK).ne')) hA.det_ne

theorem contDiff_adaptedRho (A : Mat d) (K : ℝ) : ContDiff ℝ ∞ (adaptedRho A K) :=
  contDiff_const.mul (contDiff_comp_mulVec contDiff_baseRho _)

theorem contDiff_adaptedChi (A : Mat d) (K : ℝ) : ContDiff ℝ ∞ (adaptedChi A K) :=
  contDiff_const.mul (contDiff_comp_mulVec contDiff_baseChi _)

theorem one_lt_euclideanSq_frameMatrix (hA : ProfileFrame D A K) (hK : 0 < K) {y : Vec d}
    (hy : 1 / 4 < euclideanSq y) : 1 < euclideanSq ((frameMatrix A K).mulVec y) := by
  have e : euclideanSq ((frameMatrix A K).mulVec y) = 4 * K * euclideanSq (A.mulVec y) := by
    rw [frameMatrix, Matrix.smul_mulVec, euclideanSq_smul', frameRadius, inv_inv, mul_pow,
      Real.sq_sqrt hK.le]
    ring
  rw [e]
  have := hA.norm y
  nlinarith

theorem adaptedRho_eq_zero (hA : ProfileFrame D A K) (hK : 0 < K) {y : Vec d}
    (hy : 1 / 4 < euclideanSq y) : adaptedRho A K y = 0 := by
  rw [adaptedRho, baseRho_eq_zero (one_lt_euclideanSq_frameMatrix hA hK hy), mul_zero]

theorem adaptedChi_eq_zero (hA : ProfileFrame D A K) (hK : 0 < K) {y : Vec d}
    (hy : 1 / 4 < euclideanSq y) : adaptedChi A K y = 0 := by
  rw [adaptedChi, baseChi_eq_zero (one_lt_euclideanSq_frameMatrix hA hK hy).le, mul_zero]

theorem hasCompactSupport_adaptedRho (hA : ProfileFrame D A K) (hK : 0 < K) :
    HasCompactSupport (adaptedRho A K) :=
  HasCompactSupport.intro (isCompact_euclideanSq_le (1 / 4)) fun _ hy =>
    adaptedRho_eq_zero hA hK (not_le.mp hy)

theorem hasCompactSupport_adaptedChi (hA : ProfileFrame D A K) (hK : 0 < K) :
    HasCompactSupport (adaptedChi A K) :=
  HasCompactSupport.intro (isCompact_euclideanSq_le (1 / 4)) fun _ hy =>
    adaptedChi_eq_zero hA hK (not_le.mp hy)

/-- **The gradient identity** `D ∇χ = y ρ`. -/
theorem sum_mul_coordinateDerivative_adaptedChi (hA : ProfileFrame D A K) (hK : 0 < K)
    (i : Fin d) (y : Vec d) :
    ∑ j, D i j * coordinateDerivative j (adaptedChi A K) y = y i * adaptedRho A K y := by
  set A' := frameMatrix A K with hA'
  set r := frameRadius K with hr
  set c := frameConst A K with hc
  have hr0 := frameRadius_pos hK
  have hdet := frameMatrix_det_ne hA hK
  have hgrad : ∀ j, coordinateDerivative j (adaptedChi A K) y =
      c * (A.transpose.mulVec (A.mulVec y)) j * baseRho (A'.mulVec y) := fun j => by
    have e : adaptedChi A K = fun y => r ^ 2 * c * baseChi (A'.mulVec y) := rfl
    rw [e, coordinateDerivative_const_mul'
      ((contDiff_comp_mulVec contDiff_baseChi A').differentiable (by simp)),
      coordinateDerivative_comp_mulVec' hdet]
    simp only [coordinateDerivative_baseChi]
    have e1 : ∀ l, A' l j = r⁻¹ * A l j := fun l => by
      simp only [hA', frameMatrix, ← hr, Matrix.smul_apply, smul_eq_mul]
    have e2 : ∀ l, (A'.mulVec y) l = r⁻¹ * (A.mulVec y) l := fun l => by
      simp only [hA', frameMatrix, ← hr, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
    have e3 : (A.transpose.mulVec (A.mulVec y)) j = ∑ l, A l j * (A.mulVec y) l := by
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    have hsum : ∑ l, A' l j * ((A'.mulVec y) l * baseRho (A'.mulVec y)) =
        r⁻¹ ^ 2 * (A.transpose.mulVec (A.mulVec y)) j * baseRho (A'.mulVec y) := by
      rw [e3, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [e1 l, e2 l]
      ring
    rw [hsum]
    have hrne : r ≠ 0 := by rw [hr]; exact hr0.ne'
    field_simp
  have e2 : ∑ j, D i j * (c * (A.transpose.mulVec (A.mulVec y)) j * baseRho (A'.mulVec y)) =
      c * baseRho (A'.mulVec y) * (D.mulVec (A.transpose.mulVec (A.mulVec y))) i := by
    have e4 : (D.mulVec (A.transpose.mulVec (A.mulVec y))) i =
        ∑ j, D i j * (A.transpose.mulVec (A.mulVec y)) j := rfl
    rw [e4, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [Finset.sum_congr rfl fun j _ => by rw [hgrad j], e2, hA.inv y, adaptedRho]
  ring

/-- **The base scale identity** `∑ᵢⱼ Dᵢⱼ ∂ᵢ∂ⱼχ = d ρ + y · ∇ρ`. -/
def ScaleIdentity (D : Mat d) (c : ℕ) (f g : Vec d → ℝ) : Prop :=
  ∀ y, ∑ i, ∑ j, D i j * coordinateDerivative i (coordinateDerivative j g) y = eulerOp c f y

theorem scaleIdentity_adapted (hA : ProfileFrame D A K) (hK : 0 < K) :
    ScaleIdentity D d (adaptedRho A K) (adaptedChi A K) := by
  intro y
  have hχ := contDiff_adaptedChi A K
  have hρ := contDiff_adaptedRho A K
  have h1 : ∀ i, ∑ j, D i j * coordinateDerivative i (coordinateDerivative j (adaptedChi A K)) y =
      adaptedRho A K y + y i * coordinateDerivative i (adaptedRho A K) y := fun i => by
    have hfun : (fun y => ∑ j, D i j * coordinateDerivative j (adaptedChi A K) y) =
        fun y => y i * adaptedRho A K y := by
      funext y
      exact sum_mul_coordinateDerivative_adaptedChi hA hK i y
    have h2 : coordinateDerivative i (fun y => ∑ j, D i j * coordinateDerivative j
        (adaptedChi A K) y) y = coordinateDerivative i (fun y => y i * adaptedRho A K y) y := by
      rw [hfun]
    have h3 := coordinateDerivative_sum_const_mul Finset.univ (fun j => D i j)
      (fun j => (contDiff_coordinateDerivative hχ j).differentiable (by simp)) i y
    have h4 := coordinateDerivative_mul_coord (hρ.differentiable (by simp)) i i y
    rw [h3, h4] at h2
    simpa only [eq_self_iff_true, ↓reduceIte] using h2
  calc ∑ i, ∑ j, D i j * coordinateDerivative i (coordinateDerivative j (adaptedChi A K)) y
      = ∑ i, (adaptedRho A K y + y i * coordinateDerivative i (adaptedRho A K) y) :=
        Finset.sum_congr rfl fun i _ => h1 i
    _ = eulerOp d (adaptedRho A K) y := by
        rw [Finset.sum_add_distrib, eulerOp]
        simp

theorem coordinateDerivative_eulerOp {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℕ) (m : Fin d)
    (y : Vec d) :
    coordinateDerivative m (eulerOp c f) y = eulerOp (c + 1) (coordinateDerivative m f) y := by
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hgd : ∀ l, Differentiable ℝ (coordinateDerivative l f) := fun l =>
    (contDiff_coordinateDerivative hf l).differentiable (by simp)
  have hG : ∀ l, Differentiable ℝ (fun y : Vec d => y l * coordinateDerivative l f y) :=
    fun l => (differentiable_apply l).mul (hgd l)
  have hadd := coordinateDerivative_add' (F := fun y => (c : ℝ) * f y)
    (G := fun y => ∑ l, y l * coordinateDerivative l f y) (hfd.const_mul _)
    (Differentiable.fun_sum fun l _ => hG l) m y
  have hsum := coordinateDerivative_finset_sum' Finset.univ hG m y
  have hcm := congrFun (coordinateDerivative_const_mul' hfd (c : ℝ) m) y
  have e : eulerOp c f = fun y => (c : ℝ) * f y + ∑ l, y l * coordinateDerivative l f y := rfl
  rw [e, hadd, hcm, hsum]
  have hterm : ∀ l, coordinateDerivative m (fun y : Vec d => y l * coordinateDerivative l f y) y =
      (if l = m then coordinateDerivative l f y else 0) +
        y l * coordinateDerivative l (coordinateDerivative m f) y := fun l => by
    rw [coordinateDerivative_mul_coord (hgd l),
      coordinateDerivative_comm_of_contDiff_two (hf.of_le (by simp)) m l y]
  rw [Finset.sum_congr rfl fun l _ => hterm l, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ↓reduceIte, eulerOp]
  push_cast
  ring

/-- **The scale identity passes to derivatives**: if `(f, g)` satisfy it with `c`, then
`(∂ₘ f, ∂ₘ g)` satisfy it with `c + 1`. -/
theorem ScaleIdentity.coordinateDerivative {D : Mat d} {c : ℕ} {f g : Vec d → ℝ}
    (h : ScaleIdentity D c f g) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (m : Fin d) :
    ScaleIdentity D (c + 1) (coordinateDerivative m f) (coordinateDerivative m g) := by
  intro y
  have hgij : ∀ i j, ContDiff ℝ ∞ (QSH.coordinateDerivative i (QSH.coordinateDerivative j g)) :=
    fun i j => contDiff_coordinateDerivative (contDiff_coordinateDerivative hg j) i
  have hrow : ∀ i, Differentiable ℝ (fun y => ∑ j, D i j * QSH.coordinateDerivative i
      (QSH.coordinateDerivative j g) y) := fun i =>
    Differentiable.fun_sum fun j _ => ((hgij i j).differentiable (by simp)).const_mul _
  have hfun : (fun y => ∑ i, ∑ j, D i j * QSH.coordinateDerivative i
      (QSH.coordinateDerivative j g) y) = eulerOp c f := funext h
  have hd : QSH.coordinateDerivative m (fun y => ∑ i, ∑ j, D i j * QSH.coordinateDerivative i
      (QSH.coordinateDerivative j g) y) y = QSH.coordinateDerivative m (eulerOp c f) y := by
    rw [hfun]
  rw [coordinateDerivative_finset_sum' Finset.univ hrow, coordinateDerivative_eulerOp hf] at hd
  rw [← hd]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coordinateDerivative_sum_const_mul Finset.univ (fun j => D i j)
    (fun j => (hgij i j).differentiable (by simp))]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have h1 : QSH.coordinateDerivative m (QSH.coordinateDerivative i (QSH.coordinateDerivative j g)) y =
      QSH.coordinateDerivative i (QSH.coordinateDerivative m (QSH.coordinateDerivative j g)) y :=
    coordinateDerivative_comm_of_contDiff_two
      ((contDiff_coordinateDerivative hg j).of_le (by simp)) m i y
  have h2 : QSH.coordinateDerivative m (QSH.coordinateDerivative j g) =
      QSH.coordinateDerivative j (QSH.coordinateDerivative m g) := funext fun y =>
    coordinateDerivative_comm_of_contDiff_two (hg.of_le (by simp)) m j y
  rw [h1, h2]

/-- **The scale identity for all derivatives**: `(∂^α f, ∂^α g)` satisfy it with `c + |α|`. -/
theorem ScaleIdentity.iterDeriv {D : Mat d} {c : ℕ} {f g : Vec d → ℝ}
    (h : ScaleIdentity D c f g) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {j : ℕ}
    (α : Fin j → Fin d) : ScaleIdentity D (c + j) (QSH.iterDeriv α f) (QSH.iterDeriv α g) := by
  induction j generalizing c f g with
  | zero => simpa using h
  | succ j ih =>
    rw [iterDeriv_succ, iterDeriv_succ]
    have := ih (h.coordinateDerivative hf hg (α 0)) (contDiff_coordinateDerivative hf _)
      (contDiff_coordinateDerivative hg _) (Fin.tail α)
    rwa [show c + 1 + j = c + (j + 1) by ring] at this

end QSH
