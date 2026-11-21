import QuantitativeStochasticHomogenization.Ch05.Sec03.Lemma524
import QuantitativeStochasticHomogenization.Frozen.CoarsenedCoefficientEstimates

/-!
# Lemma 5.24 with `s = 1`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 5.3, Lemma 5.24, (5.63)–(5.64), with `s = 1`, in the form of
`QSH.Frozen.coarsenedCoefficientEstimates`, from:

* the estimate (5.58) of `J₁` (Theorem 4.6 (ii)–(iii)) with a constant `C₀(d, Λ)`
  (`EnergyEstimate`);
* the structure (4.12) of `A₁` against every mask `Φ_{z,r}`, almost surely (`LinearA1Gradients`);
* the almost sure measurability of `J₁(Φ_{z,r}, p, q)` and of the flux defect of (5.64).

The matrix `ā` enters through its symmetry only: the bound `|ā| ≤ 2Λd²` is a consequence of (5.58)
and of `0 ≤ J₁(Φ, p, 0) ≤ Λ|p|²` (`norm_toEuclideanCLM_le_of_energyEstimate`).
-/

open MeasureTheory Filter
open scoped InnerProduct InnerProductSpace Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- **(5.58) with `s = 1`** for the matrix `A`: `|J₁(Φ_{z,r}, p, q) - (½ p·Ap + ½ q·A⁻¹q - p·q)|`
is `O_1(C₀ r^{-d/2})` for `r ≥ 1` and `|p|, |q| < 1`. -/
def EnergyEstimate (P : Measure (CoefficientField d Λ)) (A : Mat d) (C₀ : ℝ) : Prop :=
  ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d, euclideanNorm p < 1 → euclideanNorm q < 1 →
    AEOsBound P (fun a => |J1Heat a z r p q - homogenizedJ1 A p q|) 1 (C₀ * r ^ (-(d : ℝ) / 2))

/-! ## Euclidean facts -/

theorem euclideanNorm_smul (c : ℝ) (v : Vec d) :
    euclideanNorm (c • v) = |c| * euclideanNorm v := by
  have h : euclideanSq (c • v) = c ^ 2 * euclideanSq v := by
    simp only [euclideanSq, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [euclideanNorm, h, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, euclideanNorm]

theorem euclideanSq_unitVector (j : Fin d) : euclideanSq (unitVector j) = 1 := by
  have h := dot_unitVector_mulVec (1 : Mat d) j j
  rw [Matrix.one_mulVec, Matrix.one_apply_eq] at h
  exact h

theorem euclideanNorm_unitVector (j : Fin d) : euclideanNorm (unitVector j) = 1 := by
  rw [euclideanNorm, euclideanSq_unitVector, Real.sqrt_one]

theorem euclideanNorm_mulVec_unitVector_le (A : Mat d) {δ : ℝ}
    (hδ : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ δ) (j : Fin d) :
    euclideanNorm (A.mulVec (unitVector j)) ≤ δ := by
  rw [← norm_toLp, ← Matrix.toEuclideanCLM_toLp]
  calc ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (WithLp.toLp 2 (unitVector j))‖
      ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ * ‖(WithLp.toLp 2 (unitVector j) :
          EuclideanSpace ℝ (Fin d))‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ δ * 1 := by
        rw [norm_toLp, euclideanNorm_unitVector]
        exact mul_le_mul_of_nonneg_right hδ zero_le_one
    _ = δ := mul_one δ

/-! ## The bound on `ā` from (5.58) -/

theorem le_zero_of_forall_le_rpow (hd : 0 < d) {η C₀ : ℝ}
    (h : ∀ r : ℝ, 1 ≤ r → η ≤ C₀ * r ^ (-(d : ℝ) / 2)) : η ≤ 0 := by
  by_contra hη
  push_neg at hη
  have hlim : Tendsto (fun r : ℝ => C₀ * r ^ (-((d : ℝ) / 2))) atTop (𝓝 (C₀ * 0)) :=
    (tendsto_rpow_neg_atTop (by positivity)).const_mul C₀
  rw [mul_zero] at hlim
  obtain ⟨r, hr1, hr2⟩ := ((hlim.eventually (gt_mem_nhds hη)).and (eventually_ge_atTop 1)).exists
  have := h r hr2
  rw [neg_div] at this
  linarith

theorem homogenizedJ1_zero_right (A : Mat d) (p : Vec d) :
    homogenizedJ1 A p 0 = (1 / 2 : ℝ) * dot p (A.mulVec p) := by
  simp only [homogenizedJ1, dot_eq_dotProduct, Matrix.mulVec_zero, dotProduct_zero]
  ring

/-- `0 ≤ p·Ap ≤ 2Λ|p|²` for `|p| < 1` from (5.58) and `0 ≤ J₁(Φ, p, 0) ≤ Λ|p|²`. -/
theorem form_bounds_of_energyEstimate {P : Measure (CoefficientField d Λ)}
    [IsProbabilityMeasure P] (hd : 0 < d) {A : Mat d} {C₀ : ℝ} (h558 : EnergyEstimate P A C₀)
    (p : Vec d) (hp : euclideanNorm p < 1) :
    0 ≤ dot p (A.mulVec p) ∧ dot p (A.mulVec p) ≤ 2 * Λ * euclideanSq p := by
  have h0 : euclideanNorm (0 : Vec d) < 1 := by
    simp [euclideanNorm, euclideanSq, dot]
  have hJ : ∀ (r : ℝ), 1 ≤ r → ∀ a : CoefficientField d Λ,
      0 ≤ J1Heat a 0 r p 0 ∧ J1Heat a 0 r p 0 ≤ Λ * euclideanSq p := fun r hr a => by
    have hr0 : 0 < r := by linarith
    have h1 := J1_nonneg a (heatKernel_nonneg 0 r) (integrable_heatKernel 0 hr0)
      (integral_heatKernel 0 hr0).le p 0
    have h2 := J1_le a (heatKernel_nonneg 0 r) (integrable_heatKernel 0 hr0)
      (integral_heatKernel 0 hr0).le p 0
    have h3 : euclideanSq (0 : Vec d) = 0 := by simp [euclideanSq, dot]
    rw [h3, add_zero] at h2
    exact ⟨h1, h2⟩
  constructor
  · have hle := le_zero_of_forall_le_rpow hd (η := -((1 / 2 : ℝ) * dot p (A.mulVec p)))
      (C₀ := C₀) fun r hr => (h558 0 r hr p 0 hp h0).le_of_le_ae
        (Eventually.of_forall fun a => by
          rw [homogenizedJ1_zero_right]
          have := (hJ r hr a).1
          exact (by linarith : _ ≤ J1Heat a 0 r p 0 - _).trans (le_abs_self _))
    linarith
  · have hle := le_zero_of_forall_le_rpow hd
      (η := (1 / 2 : ℝ) * dot p (A.mulVec p) - Λ * euclideanSq p)
      (C₀ := C₀) fun r hr => (h558 0 r hr p 0 hp h0).le_of_le_ae
        (Eventually.of_forall fun a => by
          rw [homogenizedJ1_zero_right]
          have := (hJ r hr a).2
          exact (by linarith : _ ≤ -(J1Heat a 0 r p 0 - _)).trans (neg_le_abs _))
    linarith

/-- **`|ā| ≤ 2Λd²`** from (5.58), for a symmetric `ā`. -/
theorem norm_toEuclideanCLM_le_of_energyEstimate {P : Measure (CoefficientField d Λ)}
    [IsProbabilityMeasure P] (hd : 0 < d) (hΛ0 : 0 ≤ Λ) {A : Mat d} (hA : A.transpose = A)
    {C₀ : ℝ} (h558 : EnergyEstimate P A C₀) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ 2 * Λ * d ^ 2 := by
  have hentry : ∀ j k : Fin d, |A j k| ≤ 2 * Λ := by
    intro j k
    set vp := (1 / 4 : ℝ) • (unitVector j + unitVector k) with hvp
    set vm := (1 / 4 : ℝ) • (unitVector j - unitVector k) with hvm
    have hnp : euclideanNorm vp ≤ 1 / 2 := by
      rw [hvp, euclideanNorm_smul]
      have := euclideanNorm_add_le (unitVector j) (unitVector k)
      rw [euclideanNorm_unitVector, euclideanNorm_unitVector] at this
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
      linarith
    have hnm : euclideanNorm vm ≤ 1 / 2 := by
      rw [hvm, euclideanNorm_smul]
      have := euclideanNorm_sub_le (unitVector j) (unitVector k)
      rw [euclideanNorm_unitVector, euclideanNorm_unitVector] at this
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
      linarith
    have hsp : euclideanSq vp ≤ 1 / 4 := by
      rw [← euclideanNorm_sq]
      have := euclideanNorm_nonneg vp
      nlinarith
    have hsm : euclideanSq vm ≤ 1 / 4 := by
      rw [← euclideanNorm_sq]
      have := euclideanNorm_nonneg vm
      nlinarith
    have hp := form_bounds_of_energyEstimate hd h558 vp (by linarith)
    have hm := form_bounds_of_energyEstimate hd h558 vm (by linarith)
    have hpol : A j k = 4 * (dot vp (A.mulVec vp) - dot vm (A.mulVec vm)) := by
      have hs := dot_mulVec_comm hA (unitVector j) (unitVector k)
      rw [dot_unitVector_mulVec, dot_unitVector_mulVec] at hs
      have h1 := dot_unitVector_mulVec A j j
      have h2 := dot_unitVector_mulVec A k k
      have h3 := dot_unitVector_mulVec A j k
      have h4 := dot_unitVector_mulVec A k j
      simp only [hvp, hvm, dot_eq_dotProduct, Matrix.mulVec_smul, Matrix.mulVec_add,
        Matrix.mulVec_sub, dotProduct_smul, smul_dotProduct, dotProduct_add, add_dotProduct,
        dotProduct_sub, sub_dotProduct, smul_eq_mul] at h1 h2 h3 h4 ⊢
      linarith
    rw [hpol, abs_le]
    constructor <;> nlinarith [hp.1, hp.2, hm.1, hm.2]
  refine (opNorm_le_sum_abs_inner (EuclideanSpace.basisFun (Fin d) ℝ) _).trans ?_
  simp only [← toLp_unitVector, Matrix.toEuclideanCLM_toLp, inner_toLp_toLp_eq_dot,
    dot_unitVector_mulVec]
  calc ∑ j : Fin d, ∑ k : Fin d, |A j k| ≤ ∑ _j : Fin d, ∑ _k : Fin d, 2 * Λ :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hentry j k
    _ = 2 * Λ * d ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end QSH
