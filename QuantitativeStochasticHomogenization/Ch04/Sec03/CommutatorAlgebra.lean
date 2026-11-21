import QuantitativeStochasticHomogenization.Ch04.Sec03.FluxPolarization

/-!
# The gradient and flux averages of the corrected coordinates from those of maximizers

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, Lemma 4.13 (the deterministic step of the proof used here).

At a good scale, the averaged gradient and flux of a corrected coordinate `eⱼ + ∇φ_{eⱼ}` are
combinations, with coefficients `q` bounded by `2 √d (Λ + 1)`, of the averaged gradients and fluxes
of the maximizers `v(·, Φ_{y,r}, 0, eᵢ/2)`, that is of the polarization vectors of `J₁` at the loads
`(0, eᵢ/2)` (`corrected_averages_eq_sum`): the slope `c(0, q) = A⁻¹ Pᵀ q` of the maximizer equals
`eⱼ` for `q = (Pᵀ)⁻¹ A eⱼ`, where `P` is the matrix of the gradient averages and `A` the energy
matrix.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- The matrix of the gradient averages, with columns `∫ Ψ Wⱼ`. -/
def gradientMatrix (mask : Vec d → ℝ) (W : Fin d → Vec d → Vec d) : Mat d :=
  Matrix.of fun i j => (∫ x, mask x • W j x) i

theorem integral_fieldOf (mask : Vec d → ℝ) (W : Fin d → Vec d → Vec d)
    (hW : ∀ j, Integrable fun x => mask x • W j x) (v : Vec d) :
    (∫ x, mask x • fieldOf W v x) = ∑ j, v j • ∫ x, mask x • W j x := by
  have hint : ∀ j, Integrable fun x => v j • (mask x • W j x) := fun j => (hW j).smul (v j)
  have : (fun x => mask x • fieldOf W v x) = fun x => ∑ j, v j • (mask x • W j x) := by
    funext x
    simp only [fieldOf, Finset.smul_sum, smul_comm (mask x)]
  rw [this, integral_finsetSum _ fun j _ => hint j]
  exact Finset.sum_congr rfl fun j _ => integral_smul _ _

theorem integral_flux_fieldOf (a : CoefficientField d Λ) (mask : Vec d → ℝ)
    (W : Fin d → Vec d → Vec d) (hW : ∀ j, Integrable fun x => mask x • (a x).mulVec (W j x))
    (v : Vec d) :
    (∫ x, mask x • (a x).mulVec (fieldOf W v x)) =
      ∑ j, v j • ∫ x, mask x • (a x).mulVec (W j x) := by
  have hint : ∀ j, Integrable fun x => v j • (mask x • (a x).mulVec (W j x)) := fun j =>
    (hW j).smul (v j)
  have : (fun x => mask x • (a x).mulVec (fieldOf W v x)) =
      fun x => ∑ j, v j • (mask x • (a x).mulVec (W j x)) := by
    funext x
    simp only [fieldOf, Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.smul_sum, smul_comm (mask x)]
  rw [this, integral_finsetSum _ fun j _ => hint j]
  exact Finset.sum_congr rfl fun j _ => integral_smul _ _

theorem gradientMatrix_mulVec (mask : Vec d → ℝ) (W : Fin d → Vec d → Vec d)
    (hW : ∀ j, Integrable fun x => mask x • W j x) (v : Vec d) :
    (gradientMatrix mask W).mulVec v = ∫ x, mask x • fieldOf W v x := by
  rw [integral_fieldOf mask W hW v]
  funext i
  simp only [Matrix.mulVec, dotProduct, gradientMatrix, Matrix.of_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem loadVector_zero_left (a : CoefficientField d Λ) (mask : Vec d → ℝ)
    (W : Fin d → Vec d → Vec d) (q : Vec d) :
    loadVector a mask W 0 q = (gradientMatrix mask W).transpose.mulVec q := by
  have h0 : ∀ v : Vec d, dot 0 v = 0 := fun v => by simp [dot]
  funext j
  simp only [loadVector, h0, neg_zero, zero_add]
  simp only [dot, Matrix.mulVec, dotProduct, Matrix.transpose_apply, gradientMatrix, Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem maximizerSlope_zero_left_sum (a : CoefficientField d Λ) (mask : Vec d → ℝ)
    (W : Fin d → Vec d → Vec d) (q : Vec d) :
    maximizerSlope a mask W 0 q = ∑ i, q i • maximizerSlope a mask W 0 (unitVector i) := by
  have hq : q = ∑ i, q i • (unitVector i : Vec d) := by
    funext k; simp [unitVector, Pi.single_apply, Finset.sum_apply]
  simp only [maximizerSlope, loadVector_zero_left]
  conv_lhs => rw [hq]
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul]

/-- The matrix of the flux averages, with columns `∫ Ψ aWⱼ`. -/
def fluxMatrix (a : CoefficientField d Λ) (mask : Vec d → ℝ) (W : Fin d → Vec d → Vec d) :
    Mat d :=
  Matrix.of fun i j => (∫ x, mask x • (a x).mulVec (W j x)) i

theorem fluxMatrix_mulVec (a : CoefficientField d Λ) (mask : Vec d → ℝ)
    (W : Fin d → Vec d → Vec d) (hW : ∀ j, Integrable fun x => mask x • (a x).mulVec (W j x))
    (v : Vec d) :
    (fluxMatrix a mask W).mulVec v = ∫ x, mask x • (a x).mulVec (fieldOf W v x) := by
  rw [integral_flux_fieldOf a mask W hW v]
  funext i
  simp only [Matrix.mulVec, dotProduct, fluxMatrix, Matrix.of_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The `Φ_{y,r}`-average of the flux of the corrected field of slope `ξ`. -/
def fluxAverage {P : Measure (CoefficientField d Λ)} (S : HomogenizationData P)
    (a : CoefficientField d Λ) (y : Vec d) (r : ℝ) (ξ : Vec d) : Vec d :=
  ∫ x, heatKernel y r x • (a x).mulVec (correctedField S a ξ x)

theorem dot_unitVector (k : Fin d) (v : Vec d) : dot (unitVector k) v = v k := by
  simp [dot_eq_dotProduct, unitVector]

section Inversion

variable {P : Measure (CoefficientField d Λ)}

/-- **The corrected coordinates through the maximizers**: at a good scale with
`ε ≤ 1/4` and `√d ε ≤ 1/2`, the averaged gradient and flux of `eⱼ + ∇φ_{eⱼ}` are
`∑ᵢ qᵢ · 2 m(0, eᵢ/2)` and `∑ᵢ qᵢ · 2 f(0, eᵢ/2)` with `|q| ≤ 2 √d (Λ + 1)`, where `m` and `f` are
the polarization vectors of `J₁` and of its flux. -/
theorem corrected_averages_eq_sum (S : HomogenizationData P) (a : CoefficientField d Λ)
    (hΛ : 0 ≤ Λ) (hA : HomogenizedMatrixBounds S.homogenized Λ)
    (hspan : GradientsOfA1AreCorrected S a) (y : Vec d) (r : ℝ) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 4) (hεd : Real.sqrt d * ε ≤ 1 / 2)
    (havg : GaussianAverageBounds a S.homogenized (correctedField S a) y r ε) (j : Fin d) :
    ∃ q : Vec d, euclideanNorm q ≤ 2 * (Real.sqrt d * (Λ + 1)) ∧
      gradientAverage S a y r (unitVector j) =
        ∑ i, q i • ((2 : ℝ) • polarizationVector a y r 0 ((1 / 2 : ℝ) • unitVector i)) ∧
      fluxAverage S a y r (unitVector j) =
        ∑ i, q i • ((2 : ℝ) • fluxPolarizationVector a y r 0 ((1 / 2 : ℝ) • unitVector i)) := by
  set W := correctedCoordinate S a with hWdef
  set mask := heatKernel y r with hmask
  have hW := integrableFamily_of_averages S a y r ε havg
  set A := energyMatrix a mask W with hAdef
  have hAsymm : A.transpose = A := energyMatrix_transpose a mask W
  have hAξ : ∀ ξ, (1 - 2 * ε) * euclideanSq ξ ≤ dot ξ (A.mulVec ξ) ∧
      dot ξ (A.mulVec ξ) ≤ (Λ + 2 * ε) * euclideanSq ξ := by
    intro ξ
    rw [dot_energyMatrix_eq_integral a mask W hW ξ]
    have h0 : |(∫ x, mask x * dot (fieldOf W ξ x) ((a x).mulVec (fieldOf W ξ x))) -
        dot ξ (S.homogenized.mulVec ξ)| ≤ 2 * ε * euclideanNorm ξ ^ 2 := (havg ξ).2.2.2.2.2
    have h := abs_le.mp h0
    obtain ⟨h1, h2⟩ := hA ξ
    rw [euclideanNorm_sq] at h
    constructor <;> nlinarith [h.1, h.2]
  have hpos : ∀ ξ, ξ ≠ 0 → 0 < dot ξ (A.mulVec ξ) := by
    intro ξ hξ
    have h1 := (hAξ ξ).1
    have h2 : 0 < euclideanSq ξ := by
      rcases (euclideanSq_nonneg ξ).lt_or_eq with h | h
      · exact h
      · exact absurd (eq_zero_of_euclideanSq_le_zero h.symm.le) hξ
    nlinarith
  have hdet : IsUnit A.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have := hpos v hv0
    rw [hv, dot_eq_dotProduct, dotProduct_zero] at this
    exact lt_irrefl _ this
  have hpsd : ∀ ξ, 0 ≤ dot ξ (A.mulVec ξ) := fun ξ =>
    (mul_nonneg (by linarith) (euclideanSq_nonneg ξ)).trans (hAξ ξ).1
  -- the matrix of the gradient averages
  set Pm := gradientMatrix mask W with hPmdef
  have hPm : ∀ v, Pm.mulVec v = ∫ x, mask x • fieldOf W v x := gradientMatrix_mulVec mask W hW.grad
  have hPclose : ∀ v, euclideanNorm (Pm.mulVec v - v) ≤ ε * euclideanNorm v := fun v => by
    rw [hPm]; exact (havg v).2.2.2.1
  have hPinj : ∀ v, Pm.mulVec v = 0 → v = 0 := by
    intro v hv
    have h := hPclose v
    rw [hv, zero_sub, euclideanNorm_neg] at h
    have h0 := euclideanNorm_nonneg v
    have : euclideanNorm v = 0 := by nlinarith
    exact eq_zero_of_euclideanSq_le_zero (by rw [← euclideanNorm_sq, this]; norm_num)
  have hPdet : IsUnit Pm.transpose.det := by
    rw [Matrix.det_transpose, isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    exact hv0 (hPinj v hv)
  -- the coefficients
  set b : Vec d := A.mulVec (unitVector j) with hb
  set q : Vec d := Pm.transpose⁻¹.mulVec b with hqdef
  have hq : Pm.transpose.mulVec q = b := mulVec_inv_mulVec hPdet b
  have hslope : maximizerSlope a mask W 0 q = unitVector j := by
    simp only [maximizerSlope, loadVector_zero_left, ← hPmdef, hq, hb, Matrix.mulVec_mulVec]
    rw [Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  -- the bound on the coefficients
  have hbk : ∀ k, |b k| ≤ Λ + 1 := by
    intro k
    have h2A : (2 • A).transpose = 2 • A := by rw [Matrix.transpose_smul, hAsymm]
    have hcoer : ∀ ξ : Vec d, euclideanSq ξ ≤ dot ξ ((2 • A).mulVec ξ) := fun ξ => by
      have := (hAξ ξ).1
      have h0 := euclideanSq_nonneg ξ
      rw [Matrix.smul_mulVec, dot_eq_dotProduct, dotProduct_smul, two_smul, ← dot_eq_dotProduct]
      nlinarith
    have hcs := dot_mulVec_sq_le h2A hcoer (unitVector k) (unitVector j)
    simp only [dot_eq_dotProduct, two_smul, Matrix.add_mulVec, dotProduct_add] at hcs
    have hk := (hAξ (unitVector k)).2
    have hj := (hAξ (unitVector j)).2
    have hek : euclideanSq (unitVector k : Vec d) = 1 := by
      rw [← euclideanNorm_sq, euclideanNorm_unitVector]; norm_num
    have hej : euclideanSq (unitVector j : Vec d) = 1 := by
      rw [← euclideanNorm_sq, euclideanNorm_unitVector]; norm_num
    rw [hek] at hk
    rw [hej] at hj
    have hbkv : b k = unitVector k ⬝ᵥ A.mulVec (unitVector j) := by
      rw [hb, ← dot_eq_dotProduct, dot_unitVector]
    have hkk0 := hpsd (unitVector k)
    have hjj0 := hpsd (unitVector j)
    simp only [dot_eq_dotProduct] at hk hj hkk0 hjj0
    rw [hbkv]
    apply abs_le_of_sq_le_sq _ (by linarith)
    have hyz := mul_le_mul (by linarith : unitVector k ⬝ᵥ A.mulVec (unitVector k) ≤ Λ + 1)
      (by linarith : unitVector j ⬝ᵥ A.mulVec (unitVector j) ≤ Λ + 1) hjj0 (by linarith)
    nlinarith
  have hbn : euclideanNorm b ≤ Real.sqrt d * (Λ + 1) := by
    have h := euclideanSq_le_of_abs_le hbk
    rw [euclideanNorm, show Real.sqrt d * (Λ + 1) = Real.sqrt (d * (Λ + 1) ^ 2) by
      rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (by linarith)]]
    exact Real.sqrt_le_sqrt h
  have hqn : euclideanNorm q ≤ 2 * (Real.sqrt d * (Λ + 1)) := by
    have hcomp : ∀ k, |(Pm.transpose.mulVec q - q) k| ≤ euclideanNorm q * ε := by
      intro k
      have e : (Pm.transpose.mulVec q - q) k = dot q (Pm.mulVec (unitVector k) - unitVector k) := by
        simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, dot,
          unitVector, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true]
        simp only [mul_sub, Finset.sum_sub_distrib]
        congr 1
        · exact Finset.sum_congr rfl fun i _ => by ring
        · simp
      rw [e]
      refine (abs_dot_le _ _).trans ?_
      have := hPclose (unitVector k)
      rw [euclideanNorm_unitVector, mul_one] at this
      exact mul_le_mul_of_nonneg_left this (euclideanNorm_nonneg q)
    have h1 := euclideanSq_le_of_abs_le hcomp
    have h2 : euclideanNorm (Pm.transpose.mulVec q - q) ≤ Real.sqrt d * (euclideanNorm q * ε) := by
      rw [euclideanNorm, show Real.sqrt d * (euclideanNorm q * ε) =
          Real.sqrt (d * (euclideanNorm q * ε) ^ 2) by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq
          (mul_nonneg (euclideanNorm_nonneg q) hε0)]]
      exact Real.sqrt_le_sqrt h1
    have h3 := euclideanNorm_sub_le (Pm.transpose.mulVec q) (Pm.transpose.mulVec q - q)
    rw [sub_sub_cancel] at h3
    have hb' : euclideanNorm (Pm.transpose.mulVec q) = euclideanNorm b := by rw [hq]
    have hq0 := euclideanNorm_nonneg q
    have h4 := mul_le_mul_of_nonneg_right hεd hq0
    linarith
  have hhalf : ∀ i, maximizerSlope a mask W 0 (unitVector i) =
      (2 : ℝ) • maximizerSlope a mask W 0 ((1 / 2 : ℝ) • unitVector i) := by
    intro i
    rw [← maximizerSlope_smul]
    congr 1
    · simp
    · rw [smul_smul]; norm_num
  set Fm := fluxMatrix a mask W with hFmdef
  have hFm : ∀ v, Fm.mulVec v = ∫ x, mask x • (a x).mulVec (fieldOf W v x) :=
    fluxMatrix_mulVec a mask W hW.flux
  have hci : ∀ i, Pm.mulVec (maximizerSlope a mask W 0 (unitVector i)) =
      (2 : ℝ) • polarizationVector a y r 0 ((1 / 2 : ℝ) • unitVector i) := by
    intro i
    have h := integral_maximizer_eq_polarizationVector S a hA hspan y r hε havg 0
      ((1 / 2 : ℝ) • unitVector i)
    rw [hhalf i, Matrix.mulVec_smul, hPm]
    exact congrArg (fun v => (2 : ℝ) • v) h
  have hfi : ∀ i, Fm.mulVec (maximizerSlope a mask W 0 (unitVector i)) =
      (2 : ℝ) • fluxPolarizationVector a y r 0 ((1 / 2 : ℝ) • unitVector i) := by
    intro i
    have h := integral_flux_maximizer_eq_fluxPolarizationVector S a hA hspan y r hε havg 0
      ((1 / 2 : ℝ) • unitVector i)
    rw [hhalf i, Matrix.mulVec_smul, hFm]
    exact congrArg (fun v => (2 : ℝ) • v) h
  refine ⟨q, hqn, ?_, ?_⟩
  · calc gradientAverage S a y r (unitVector j) = Pm.mulVec (unitVector j) := (hPm _).symm
      _ = Pm.mulVec (maximizerSlope a mask W 0 q) := by rw [hslope]
      _ = ∑ i, q i • Pm.mulVec (maximizerSlope a mask W 0 (unitVector i)) := by
          rw [maximizerSlope_zero_left_sum, Matrix.mulVec_sum]
          simp only [Matrix.mulVec_smul]
      _ = _ := by simp only [hci]
  · calc fluxAverage S a y r (unitVector j) = Fm.mulVec (unitVector j) := (hFm _).symm
      _ = Fm.mulVec (maximizerSlope a mask W 0 q) := by rw [hslope]
      _ = ∑ i, q i • Fm.mulVec (maximizerSlope a mask W 0 (unitVector i)) := by
          rw [maximizerSlope_zero_left_sum, Matrix.mulVec_sum]
          simp only [Matrix.mulVec_smul]
      _ = _ := by simp only [hfi]

end Inversion

end QSH
