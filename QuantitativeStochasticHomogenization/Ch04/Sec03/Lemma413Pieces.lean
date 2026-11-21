import QuantitativeStochasticHomogenization.Ch04.Sec03.GaussianJensen

/-!
# Pieces of the proof of Lemma 4.13

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, Lemma 4.13: bounds used in the probabilistic step of the proof here.

* `abs_fluxPolarizationVector_le`: the flux polarization vector is bounded by `8 (Λ + 1)`
  componentwise, for loads in the open unit ball;
* `isUnit_det_of_near_inverse`: a matrix `B` with `|(B - ā⁻¹) v| ≤ η |v|` and `Λ η ≤ 1/2` is
  invertible with `|B⁻¹ w| ≤ 2Λ |w|`, when `|ā z| ≤ Λ |z|`;
* `euclideanNorm_homogenized_mulVec_le`: `|ā z| ≤ Λ |z|` from `ξ·āξ ≤ Λ|ξ|²` and the symmetry.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

theorem abs_fluxPolarizationVector_le (a : CoefficientField d Λ) (hΛ : 0 ≤ Λ) (y : Vec d)
    {r : ℝ} (hr : 0 < r) {p q : Vec d} (hp : euclideanNorm p < 1) (hq : euclideanNorm q < 1)
    (i : Fin d) : |fluxPolarizationVector a y r p q i| ≤ 8 * (Λ + 1) := by
  have hb : ∀ p' q' : Vec d, euclideanNorm p' ≤ 1 → euclideanNorm q' ≤ 1 →
      0 ≤ J1Heat a y r p' q' ∧ J1Heat a y r p' q' ≤ Λ + 1 := by
    intro p' q' hp' hq'
    obtain ⟨h0, h1⟩ := J1Heat_nonneg_le a y hr p' q'
    have hp2 : euclideanSq p' ≤ 1 := by
      rw [← euclideanNorm_sq]; nlinarith [euclideanNorm_nonneg p']
    have hq2 : euclideanSq q' ≤ 1 := by
      rw [← euclideanNorm_sq]; nlinarith [euclideanNorm_nonneg q']
    exact ⟨h0, by nlinarith [euclideanSq_nonneg p']⟩
  have hhalf : ∀ v : Vec d, euclideanNorm v ≤ 2 → euclideanNorm ((1 / 2 : ℝ) • v) ≤ 1 := by
    intro v hv
    rw [euclideanNorm_smul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have hpe : euclideanNorm (p + unitVector i) ≤ 2 :=
    (euclideanNorm_add_le p (unitVector i)).trans (by rw [euclideanNorm_unitVector]; linarith)
  have he : euclideanNorm (unitVector i : Vec d) ≤ 2 := by rw [euclideanNorm_unitVector]; norm_num
  have h00 : euclideanNorm (0 : Vec d) ≤ 1 := by simp [euclideanNorm, euclideanSq, dot]
  obtain ⟨h1a, h1b⟩ := hb ((1 / 2 : ℝ) • (p + unitVector i)) ((1 / 2 : ℝ) • q)
    (hhalf _ hpe) (hhalf q (by linarith))
  obtain ⟨h2a, h2b⟩ := hb ((1 / 2 : ℝ) • p) ((1 / 2 : ℝ) • q) (hhalf p (by linarith))
    (hhalf q (by linarith))
  obtain ⟨h3a, h3b⟩ := hb ((1 / 2 : ℝ) • unitVector i) 0 (hhalf _ he) h00
  simp only [fluxPolarizationVector]
  rw [abs_le]
  constructor <;> nlinarith

/-- `|ā z| ≤ Λ |z|` for a symmetric `ā` with `0 ≤ ξ·āξ ≤ Λ|ξ|²`. -/
theorem euclideanNorm_homogenized_mulVec_le {A : Mat d} (hAsymm : A.transpose = A)
    (hA : HomogenizedMatrixBounds A Λ) (hΛ : 0 ≤ Λ) (z : Vec d) :
    euclideanNorm (A.mulVec z) ≤ Λ * euclideanNorm z := by
  refine euclideanNorm_mulVec_le_of_abs_dot_le hAsymm hΛ (fun u => ?_) z
  obtain ⟨h1, h2⟩ := hA u
  rw [abs_of_nonneg ((euclideanSq_nonneg u).trans h1)]
  exact h2

/-- **A perturbation of `ā⁻¹` is invertible**: if `|(B - ā⁻¹) v| ≤ η |v|` for all `v`, with
`|ā z| ≤ Λ |z|`, `Λ > 0` and `Λ η ≤ 1/2`, then `B` is invertible and `|B⁻¹ w| ≤ 2Λ |w|`. -/
theorem isUnit_det_of_near_inverse {A B : Mat d} (hAdet : IsUnit A.det) (hΛ : 0 < Λ)
    (hAop : ∀ z, euclideanNorm (A.mulVec z) ≤ Λ * euclideanNorm z) {η : ℝ}
    (hη : Λ * η ≤ 1 / 2) (hB : ∀ v, euclideanNorm ((B - A⁻¹).mulVec v) ≤ η * euclideanNorm v) :
    IsUnit B.det ∧ ∀ w, euclideanNorm (B⁻¹.mulVec w) ≤ 2 * Λ * euclideanNorm w := by
  -- `|B v| ≥ |v| / (2Λ)`
  have hlow : ∀ v, euclideanNorm v ≤ 2 * Λ * euclideanNorm (B.mulVec v) := by
    intro v
    have h1 : euclideanNorm v ≤ Λ * euclideanNorm (A⁻¹.mulVec v) := by
      have := hAop (A⁻¹.mulVec v)
      rwa [mulVec_inv_mulVec hAdet v] at this
    have h2 : euclideanNorm (A⁻¹.mulVec v) ≤ euclideanNorm (B.mulVec v) + η * euclideanNorm v := by
      have := euclideanNorm_sub_le (B.mulVec v) ((B - A⁻¹).mulVec v)
      have hBv := hB v
      rw [Matrix.sub_mulVec] at this hBv
      rw [sub_sub_cancel] at this
      linarith
    have h3 := euclideanNorm_nonneg v
    nlinarith
  have hinj : ∀ v, B.mulVec v = 0 → v = 0 := by
    intro v hv
    have h := hlow v
    rw [hv] at h
    have h0 : euclideanNorm (0 : Vec d) = 0 := by simp [euclideanNorm, euclideanSq, dot]
    rw [h0, mul_zero] at h
    exact eq_zero_of_euclideanSq_le_zero (by
      rw [← euclideanNorm_sq]; nlinarith [euclideanNorm_nonneg v])
  have hdet : IsUnit B.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    exact hv0 (hinj v hv)
  refine ⟨hdet, fun w => ?_⟩
  have := hlow (B⁻¹.mulVec w)
  rwa [mulVec_inv_mulVec hdet w] at this

end QSH
