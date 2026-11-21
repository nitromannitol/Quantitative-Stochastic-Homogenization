import QuantitativeStochasticHomogenization.Ch04.Sec03.MatrixPerturbation

/-!
# The polarization vectors at a good scale and the inverse of `ā`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, Lemma 4.13 (a deterministic step of the proof used here).

At a good scale with error `ε ≤ 1/4`, `√d ε ≤ 1/2`, the vector `2 m(0, eᵢ/2)` (the averaged
gradient `P A⁻¹ Pᵀ eᵢ` of the maximizer at the load `(0, eᵢ)`) is within `(9 + √d) ε` of
`ā⁻¹ eᵢ` (`polarizationVector_near_inverse`).
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

section Near

variable {P : Measure (CoefficientField d Λ)}

/-- The energy matrix at a good scale: `(1 - 2ε)|ξ|² ≤ ξ·Aξ ≤ (Λ + 2ε)|ξ|²`,
`|ξ·(A - ā)ξ| ≤ 2ε|ξ|²`, and `A` is invertible. -/
theorem energyMatrix_bounds_of_averages (S : HomogenizationData P) (a : CoefficientField d Λ)
    (hA : HomogenizedMatrixBounds S.homogenized Λ) (y : Vec d) (r : ℝ) {ε : ℝ}
    (hε : ε ≤ 1 / 4)
    (havg : GaussianAverageBounds a S.homogenized (correctedField S a) y r ε) :
    (∀ ξ, (1 - 2 * ε) * euclideanSq ξ ≤
      dot ξ ((energyMatrix a (heatKernel y r) (correctedCoordinate S a)).mulVec ξ)) ∧
    (∀ ξ, |dot ξ ((energyMatrix a (heatKernel y r) (correctedCoordinate S a)).mulVec ξ) -
      dot ξ (S.homogenized.mulVec ξ)| ≤ 2 * ε * euclideanSq ξ) ∧
    IsUnit (energyMatrix a (heatKernel y r) (correctedCoordinate S a)).det := by
  have hW := integrableFamily_of_averages S a y r ε havg
  have hclose : ∀ ξ, |dot ξ ((energyMatrix a (heatKernel y r) (correctedCoordinate S a)).mulVec ξ) -
      dot ξ (S.homogenized.mulVec ξ)| ≤ 2 * ε * euclideanSq ξ := by
    intro ξ
    rw [dot_energyMatrix_eq_integral a _ _ hW ξ, ← euclideanNorm_sq]
    exact (havg ξ).2.2.2.2.2
  have hlow : ∀ ξ, (1 - 2 * ε) * euclideanSq ξ ≤
      dot ξ ((energyMatrix a (heatKernel y r) (correctedCoordinate S a)).mulVec ξ) := by
    intro ξ
    have h := (abs_le.mp (hclose ξ)).1
    have h1 := (hA ξ).1
    nlinarith
  refine ⟨hlow, hclose, ?_⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h1 := hlow v
  rw [hv, dot_eq_dotProduct, dotProduct_zero] at h1
  have h2 : euclideanSq v ≤ 0 := by nlinarith [euclideanSq_nonneg v]
  exact hv0 (eq_zero_of_euclideanSq_le_zero h2)

/-- **`2 m(0, eᵢ/2)` is close to `ā⁻¹ eᵢ` at a good scale.** -/
theorem polarizationVector_near_inverse (S : HomogenizationData P) (a : CoefficientField d Λ)
    (hA : HomogenizedMatrixBounds S.homogenized Λ) (hspan : GradientsOfA1AreCorrected S a)
    (y : Vec d) (r : ℝ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) (hεd : Real.sqrt d * ε ≤ 1 / 2)
    (havg : GaussianAverageBounds a S.homogenized (correctedField S a) y r ε) (i : Fin d) :
    euclideanNorm ((2 : ℝ) • polarizationVector a y r 0 ((1 / 2 : ℝ) • unitVector i) -
      S.homogenized⁻¹.mulVec (unitVector i)) ≤ (9 + Real.sqrt d) * ε := by
  set W := correctedCoordinate S a with hWdef
  set mask := heatKernel y r with hmask
  have hW := integrableFamily_of_averages S a y r ε havg
  obtain ⟨hlow, hclose, hdet⟩ := energyMatrix_bounds_of_averages S a hA y r hε havg
  set A := energyMatrix a mask W with hAdef
  set D := S.homogenized with hD
  have hAsymm : A.transpose = A := energyMatrix_transpose a mask W
  have hpsd : ∀ ξ, 0 ≤ dot ξ (A.mulVec ξ) := fun ξ =>
    (mul_nonneg (by linarith) (euclideanSq_nonneg ξ)).trans (hlow ξ)
  -- the polarization vector is the gradient average of the maximizer
  set Pm := gradientMatrix mask W with hPmdef
  have hPm : ∀ v, Pm.mulVec v = ∫ x, mask x • fieldOf W v x := gradientMatrix_mulVec mask W hW.grad
  have hPclose : ∀ v, euclideanNorm (Pm.mulVec v - v) ≤ ε * euclideanNorm v := fun v => by
    rw [hPm]; exact (havg v).2.2.2.1
  have hB : (2 : ℝ) • polarizationVector a y r 0 ((1 / 2 : ℝ) • unitVector i) =
      Pm.mulVec (maximizerSlope a mask W 0 (unitVector i)) := by
    have h := integral_maximizer_eq_polarizationVector S a hA hspan y r hε havg 0
      ((1 / 2 : ℝ) • unitVector i)
    have hhalf : maximizerSlope a mask W 0 (unitVector i) =
        (2 : ℝ) • maximizerSlope a mask W 0 ((1 / 2 : ℝ) • unitVector i) := by
      rw [← maximizerSlope_smul]
      congr 1
      · simp
      · rw [smul_smul]; norm_num
    rw [hhalf, Matrix.mulVec_smul, hPm]
    exact (congrArg (fun v => (2 : ℝ) • v) h).symm
  have hslope : maximizerSlope a mask W 0 (unitVector i) = A⁻¹.mulVec (Pm.transpose.mulVec
      (unitVector i)) := by
    show (energyMatrix a mask W)⁻¹.mulVec (loadVector a mask W 0 (unitVector i)) = _
    rw [loadVector_zero_left]
  rw [hB, hslope]
  -- the pieces
  set u := Pm.transpose.mulVec (unitVector i) with hu
  set w := A⁻¹.mulVec u with hw
  have hui : euclideanNorm (u - unitVector i) ≤ Real.sqrt d * ε := by
    have := euclideanNorm_transpose_mulVec_sub_le hε0 hPclose (unitVector i)
    rwa [euclideanNorm_unitVector, mul_one] at this
  have hun : euclideanNorm u ≤ 3 / 2 := by
    have := euclideanNorm_add_le (u - unitVector i) (unitVector i)
    rw [sub_add_cancel, euclideanNorm_unitVector] at this
    linarith
  have hwn : euclideanNorm w ≤ 2 * euclideanNorm u := by
    have hcoer : ∀ ξ : Vec d, (1 / 2 : ℝ) * euclideanSq ξ ≤ dot ξ (A.mulVec ξ) := fun ξ =>
      (mul_le_mul_of_nonneg_right (by linarith) (euclideanSq_nonneg ξ)).trans (hlow ξ)
    have := euclideanNorm_inv_mulVec_le_of_coercive (by norm_num) hcoer u
    norm_num at this
    linarith
  have hDsymm : D.transpose = D := S.symmetric
  have hDdet : IsUnit D.det := isUnit_det_of_coercive fun ξ => (hA ξ).1
  have hAD : ∀ z, euclideanNorm ((A - D).mulVec z) ≤ 2 * ε * euclideanNorm z := by
    have hsym : (A - D).transpose = A - D := by rw [Matrix.transpose_sub, hAsymm, hDsymm]
    refine euclideanNorm_mulVec_le_of_abs_dot_le hsym (by positivity) fun z => ?_
    have := hclose z
    rwa [Matrix.sub_mulVec, dot_eq_dotProduct, dotProduct_sub, ← dot_eq_dotProduct,
      ← dot_eq_dotProduct]
  have hDinv : ∀ z, euclideanNorm (D⁻¹.mulVec z) ≤ euclideanNorm z :=
    euclideanNorm_inv_mulVec_le fun ξ => (hA ξ).1
  have hAinv : ∀ z, euclideanNorm (A⁻¹.mulVec z) ≤ 2 * euclideanNorm z := by
    have hcoer : ∀ ξ : Vec d, (1 / 2 : ℝ) * euclideanSq ξ ≤ dot ξ (A.mulVec ξ) := fun ξ =>
      (mul_le_mul_of_nonneg_right (by linarith) (euclideanSq_nonneg ξ)).trans (hlow ξ)
    intro z
    have := euclideanNorm_inv_mulVec_le_of_coercive (by norm_num) hcoer z
    norm_num at this
    linarith
  -- the decomposition
  have hdec : Pm.mulVec w - D⁻¹.mulVec (unitVector i) =
      (Pm.mulVec w - w) + A⁻¹.mulVec ((D - A).mulVec (D⁻¹.mulVec u)) +
        D⁻¹.mulVec (u - unitVector i) := by
    have h1 : A⁻¹.mulVec ((D - A).mulVec (D⁻¹.mulVec u)) = w - D⁻¹.mulVec u := by
      rw [Matrix.sub_mulVec, Matrix.mulVec_sub]
      simp only [Matrix.mulVec_mulVec]
      rw [Matrix.mul_nonsing_inv D hDdet, mul_one, ← mul_assoc, Matrix.nonsing_inv_mul A hdet,
        one_mul]
    rw [h1, Matrix.mulVec_sub]
    abel
  rw [hdec]
  have t1 : euclideanNorm (Pm.mulVec w - w) ≤ ε * (2 * (3 / 2)) := by
    refine (hPclose w).trans (mul_le_mul_of_nonneg_left (by linarith) hε0)
  have t2 : euclideanNorm (A⁻¹.mulVec ((D - A).mulVec (D⁻¹.mulVec u))) ≤ 2 * (2 * ε * (3 / 2)) := by
    refine (hAinv _).trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    have h1 : (D - A) = -(A - D) := by abel
    rw [h1, Matrix.neg_mulVec, euclideanNorm_neg]
    refine (hAD _).trans (mul_le_mul_of_nonneg_left ((hDinv u).trans hun) (by positivity))
  have t3 : euclideanNorm (D⁻¹.mulVec (u - unitVector i)) ≤ Real.sqrt d * ε :=
    (hDinv _).trans hui
  have hsum := euclideanNorm_add_le ((Pm.mulVec w - w) + A⁻¹.mulVec ((D - A).mulVec (D⁻¹.mulVec u)))
    (D⁻¹.mulVec (u - unitVector i))
  have hsum2 := euclideanNorm_add_le (Pm.mulVec w - w) (A⁻¹.mulVec ((D - A).mulVec (D⁻¹.mulVec u)))
  nlinarith

end Near

end QSH
