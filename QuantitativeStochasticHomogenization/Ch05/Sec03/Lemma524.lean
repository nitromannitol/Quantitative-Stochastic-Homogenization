import QuantitativeStochasticHomogenization.Ch05.Sec03.CoarsenedCoefficientGram
import QuantitativeStochasticHomogenization.AppA.AlmostSureOsBound

/-!
# Lemma 5.24

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 5.3, Lemma 5.24, (5.63)–(5.64), with `s = 1`, from the estimate (5.58) of `J₁` and the
structure (4.12) of `A₁`, by finite-dimensional polarization.

On the Gram space of `A₁` (`Ch04/Sec01/GramSpace.lean`), `J₁ = ½ ‖U^* q - V^* p‖²` and `b_r(z)` is the
matrix of `b = V V^* - ā U V^*`. The entries of `b` and of `U V^* - I` are combinations of the errors
`J₁ - (½ p·āp + ½ q·ā⁻¹q - p·q)` at finitely many loads, rescaled into the unit ball by the
homogeneity of both sides. This gives `‖b‖ + ‖U V^* - I‖ ≤ C Y` for a finite sum `Y` of errors of
(5.58), and the factorization of `V - (ā + b) U` gives the flux defect `≤ C Y²`.

This file proves the deterministic part, for one coefficient field (`polarization_bounds`).
-/

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## The homogenized energy -/

theorem homogenizedJ1_smul (A : Mat d) (t : ℝ) (p q : Vec d) :
    homogenizedJ1 A (t • p) (t • q) = t ^ 2 * homogenizedJ1 A p q := by
  simp only [homogenizedJ1, dot_eq_dotProduct, Matrix.mulVec_smul, dotProduct_smul,
    smul_dotProduct, smul_eq_mul]
  ring

/-- The homogenized energy gives zero in (5.62). -/
theorem homogenizedJ1_add_sub_sub {A : Mat d} (hA : A.transpose = A) (p k : Vec d) :
    homogenizedJ1 A (p + k) (A.mulVec p) - homogenizedJ1 A (p - k) (A.mulVec p) = 0 := by
  have hs := dot_mulVec_comm hA p k
  simp only [dot_eq_dotProduct] at hs
  have hc : k ⬝ᵥ A.mulVec p = A.mulVec p ⬝ᵥ k := dotProduct_comm _ _
  simp only [homogenizedJ1, dot_eq_dotProduct, Matrix.mulVec_add, Matrix.mulVec_sub,
    dotProduct_add, add_dotProduct, dotProduct_sub, sub_dotProduct]
  linarith

/-- The mixed part of the homogenized energy. -/
theorem homogenizedJ1_mixed (A : Mat d) (p q : Vec d) :
    homogenizedJ1 A p 0 + homogenizedJ1 A 0 q - homogenizedJ1 A p q = dot p q := by
  simp only [homogenizedJ1, dot_eq_dotProduct, Matrix.mulVec_zero, dotProduct_zero,
    zero_dotProduct]
  ring

/-! ## The errors of (5.58) at the loads of the polarization -/

/-- `|J₁(Φ_{z,r}, p, q) - (½ p·āp + ½ q·ā⁻¹q - p·q)|`, the error in (5.58). -/
def energyError (a : CoefficientField d Λ) (A : Mat d) (z : Vec d) (r : ℝ) (p q : Vec d) : ℝ :=
  |J1Heat a z r p q - homogenizedJ1 A p q|

theorem energyError_nonneg (a : CoefficientField d Λ) (A : Mat d) (z : Vec d) (r : ℝ)
    (p q : Vec d) : 0 ≤ energyError a A z r p q :=
  abs_nonneg _

/-- The five errors used for the entry `(j, k)`, at loads scaled by `t`. -/
def polarizationTerm (a : CoefficientField d Λ) (A : Mat d) (z : Vec d) (r t : ℝ)
    (j k : Fin d) : ℝ :=
  energyError a A z r (t • (unitVector j + unitVector k)) (t • A.mulVec (unitVector j)) +
    energyError a A z r (t • (unitVector j - unitVector k)) (t • A.mulVec (unitVector j)) +
    energyError a A z r (t • unitVector k) (t • unitVector j) +
    energyError a A z r (t • unitVector k) 0 +
    energyError a A z r 0 (t • unitVector j)

/-- The sum `Y` of the errors of (5.58) used by the polarization. -/
def polarizationError (a : CoefficientField d Λ) (A : Mat d) (z : Vec d) (r t : ℝ) : ℝ :=
  ∑ j : Fin d, ∑ k : Fin d, polarizationTerm a A z r t j k

theorem polarizationTerm_nonneg (a : CoefficientField d Λ) (A : Mat d) (z : Vec d) (r t : ℝ)
    (j k : Fin d) : 0 ≤ polarizationTerm a A z r t j k := by
  unfold polarizationTerm
  have h := energyError_nonneg a A z r
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (h _ _) (h _ _)) (h _ _)) (h _ _)) (h _ _)

theorem polarizationError_nonneg (a : CoefficientField d Λ) (A : Mat d) (z : Vec d)
    (r t : ℝ) : 0 ≤ polarizationError a A z r t :=
  Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => polarizationTerm_nonneg a A z r t j k

theorem matrixSize_le_sum_abs (M : Mat d) : matrixSize M ≤ ∑ j, ∑ k, |M j k| := by
  unfold matrixSize
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  calc ∑ j : Fin d, ∑ k : Fin d, M j k ^ 2 ≤ ∑ j : Fin d, (∑ k : Fin d, |M j k|) ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        calc ∑ k : Fin d, M j k ^ 2 = ∑ k : Fin d, |M j k| ^ 2 := by simp only [sq_abs]
          _ ≤ (∑ k : Fin d, |M j k|) ^ 2 :=
            Finset.sum_sq_le_sq_sum_of_nonneg fun k _ => abs_nonneg _
    _ ≤ (∑ j : Fin d, ∑ k : Fin d, |M j k|) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => Finset.sum_nonneg fun k _ => abs_nonneg _

/-! ## The deterministic estimate -/

section Heat

variable (a : CoefficientField d Λ) (A : Mat d) (z : Vec d) {r : ℝ} (hr : 0 < r)
  (G : Vec d →ₗ[ℝ] Vec d → Vec d)
  (hspan : ∀ w : HarmonicA1 a, ∃ ξ, w.grad =ᵐ[volume] G ξ)
  (hreal : ∀ ξ, ∃ w : HarmonicA1 a, w.grad =ᵐ[volume] G ξ)
  (hG2 : ∀ ξ, Integrable (fun x => heatKernel z r x * euclideanSq (G ξ x)))

include hr hspan hreal hG2

theorem J1Heat_smul (t : ℝ) (p q : Vec d) :
    J1Heat a z r (t • p) (t • q) = t ^ 2 * J1Heat a z r p q := by
  rw [J1Heat_eq_gramEnergy a z hr G hspan hreal hG2, J1Heat_eq_gramEnergy a z hr G hspan hreal hG2,
    WithLp.toLp_smul, WithLp.toLp_smul, gramEnergy_smul]

theorem energyError_eq_smul {t : ℝ} (ht : t ≠ 0) (p q : Vec d) :
    energyError a A z r p q = (t ^ 2)⁻¹ * energyError a A z r (t • p) (t • q) := by
  have ht2 : 0 < t ^ 2 := by positivity
  rw [energyError, energyError, J1Heat_smul a z hr G hspan hreal hG2, homogenizedJ1_smul, ← mul_sub,
    abs_mul, abs_of_pos ht2, ← mul_assoc, inv_mul_cancel₀ ht2.ne', one_mul]

theorem abs_coarsenedCoefficient_le (hA : A.transpose = A) {t : ℝ} (ht : t ≠ 0) (j k : Fin d) :
    |coarsenedCoefficient a A z r j k| ≤ (t ^ 2)⁻¹ * polarizationTerm a A z r t j k := by
  have hQ := homogenizedJ1_add_sub_sub hA (unitVector j) (unitVector k)
  have h1 := energyError_eq_smul a A z hr G hspan hreal hG2 ht (unitVector j + unitVector k)
    (A.mulVec (unitVector j))
  have h2 := energyError_eq_smul a A z hr G hspan hreal hG2 ht (unitVector j - unitVector k)
    (A.mulVec (unitVector j))
  have hcc : coarsenedCoefficient a A z r j k =
      ((J1Heat a z r (unitVector j + unitVector k) (A.mulVec (unitVector j)) -
          homogenizedJ1 A (unitVector j + unitVector k) (A.mulVec (unitVector j))) -
        (J1Heat a z r (unitVector j - unitVector k) (A.mulVec (unitVector j)) -
          homogenizedJ1 A (unitVector j - unitVector k) (A.mulVec (unitVector j)))) / 2 := by
    rw [coarsenedCoefficient]
    linarith
  have hti : 0 ≤ (t ^ 2)⁻¹ := by positivity
  have hE := energyError_nonneg a A z r
  have hrest : 0 ≤ (t ^ 2)⁻¹ *
      (energyError a A z r (t • unitVector k) (t • unitVector j) +
        energyError a A z r (t • unitVector k) 0 + energyError a A z r 0 (t • unitVector j)) :=
    mul_nonneg hti (add_nonneg (add_nonneg (hE _ _) (hE _ _)) (hE _ _))
  rw [hcc, abs_div, abs_two]
  have htri := abs_sub _ _ |>.trans_eq (congrArg₂ (· + ·) rfl rfl) |>.trans
    (le_refl (|J1Heat a z r (unitVector j + unitVector k) (A.mulVec (unitVector j)) -
          homogenizedJ1 A (unitVector j + unitVector k) (A.mulVec (unitVector j))| +
      |J1Heat a z r (unitVector j - unitVector k) (A.mulVec (unitVector j)) -
          homogenizedJ1 A (unitVector j - unitVector k) (A.mulVec (unitVector j))|))
  rw [← energyError, ← energyError, h1, h2] at htri
  have hE1 := energyError_nonneg a A z r (t • (unitVector j + unitVector k))
    (t • A.mulVec (unitVector j))
  have hE2 := energyError_nonneg a A z r (t • (unitVector j - unitVector k))
    (t • A.mulVec (unitVector j))
  unfold polarizationTerm
  nlinarith

theorem abs_inner_mixed_le {t : ℝ} (ht : t ≠ 0) (j k : Fin d) :
    |⟪(WithLp.toLp 2 (unitVector j) : EuclideanSpace ℝ (Fin d)),
        ((heatGramFamily a z hr G hreal hG2).U ∘L ((heatGramFamily a z hr G hreal hG2).V)† - 1)
          (WithLp.toLp 2 (unitVector k))⟫_ℝ| ≤
      (t ^ 2)⁻¹ * polarizationTerm a A z r t j k := by
  set F := heatGramFamily a z hr G hreal hG2 with hF
  have hJ1 : J1Heat a z r (unitVector k) 0 = gramEnergy F.U F.V (WithLp.toLp 2 (unitVector k)) 0 := by
    rw [J1Heat_eq_gramEnergy a z hr G hspan hreal hG2, WithLp.toLp_zero]
  have hJ2 : J1Heat a z r 0 (unitVector j) = gramEnergy F.U F.V 0 (WithLp.toLp 2 (unitVector j)) := by
    rw [J1Heat_eq_gramEnergy a z hr G hspan hreal hG2, WithLp.toLp_zero]
  have hJ3 : J1Heat a z r (unitVector k) (unitVector j) =
      gramEnergy F.U F.V (WithLp.toLp 2 (unitVector k)) (WithLp.toLp 2 (unitVector j)) :=
    J1Heat_eq_gramEnergy a z hr G hspan hreal hG2 _ _
  have hentry : ⟪(WithLp.toLp 2 (unitVector j) : EuclideanSpace ℝ (Fin d)),
      (F.U ∘L (F.V)† - 1) (WithLp.toLp 2 (unitVector k))⟫_ℝ =
      (J1Heat a z r (unitVector k) 0 - homogenizedJ1 A (unitVector k) 0) +
        (J1Heat a z r 0 (unitVector j) - homogenizedJ1 A 0 (unitVector j)) -
        (J1Heat a z r (unitVector k) (unitVector j) -
          homogenizedJ1 A (unitVector k) (unitVector j)) := by
    rw [sub_apply, one_apply_eq_self, inner_sub_right,
      inner_comp_adjoint_eq_gramEnergy, inner_toLp_toLp_eq_dot, hJ1, hJ2, hJ3]
    have hQ := homogenizedJ1_mixed A (unitVector k) (unitVector j)
    have hc : dot (unitVector j) (unitVector k) = dot (unitVector k) (unitVector j) :=
      dotProduct_comm _ _
    linarith
  have h1 := energyError_eq_smul a A z hr G hspan hreal hG2 ht (unitVector k) 0
  have h2 := energyError_eq_smul a A z hr G hspan hreal hG2 ht 0 (unitVector j)
  have h3 := energyError_eq_smul a A z hr G hspan hreal hG2 ht (unitVector k) (unitVector j)
  rw [smul_zero] at h1 h2
  rw [hentry]
  have htri : |(J1Heat a z r (unitVector k) 0 - homogenizedJ1 A (unitVector k) 0) +
        (J1Heat a z r 0 (unitVector j) - homogenizedJ1 A 0 (unitVector j)) -
        (J1Heat a z r (unitVector k) (unitVector j) -
          homogenizedJ1 A (unitVector k) (unitVector j))| ≤
      energyError a A z r (unitVector k) 0 + energyError a A z r 0 (unitVector j) +
        energyError a A z r (unitVector k) (unitVector j) :=
    (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  rw [h1, h2, h3] at htri
  have hE := energyError_nonneg a A z r
  have hti : 0 ≤ (t ^ 2)⁻¹ := by positivity
  have hE12 : 0 ≤ (t ^ 2)⁻¹ * (energyError a A z r (t • (unitVector j + unitVector k))
      (t • A.mulVec (unitVector j)) + energyError a A z r (t • (unitVector j - unitVector k))
      (t • A.mulVec (unitVector j))) := mul_nonneg hti (add_nonneg (hE _ _) (hE _ _))
  unfold polarizationTerm
  nlinarith

/-- **The deterministic Lemma 5.24**: on a coefficient field for which the gradients of `A₁` form
a linear family, `|b_r(z)| ≤ t⁻² Y` and the flux defect is at most `C Y²`, where `Y` is the sum of
the errors of (5.58) at the loads scaled by `t`. -/
theorem polarization_bounds (hA : A.transpose = A) {t δ : ℝ} (ht : t ≠ 0)
    (hδ : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ δ) :
    matrixSize (coarsenedCoefficient a A z r) ≤ (t ^ 2)⁻¹ * polarizationError a A z r t ∧
      coarseFluxDefect a A z r ≤
        Real.sqrt |Λ| * (4 * (1 + |Λ| + δ)) * (2 * ((t ^ 2)⁻¹ * polarizationError a A z r t)) ^ 2 := by
  set F := heatGramFamily a z hr G hreal hG2 with hF
  set Y := polarizationError a A z r t with hY
  set D := Matrix.toEuclideanCLM (𝕜 := ℝ) A with hD
  have hY0 : 0 ≤ Y := polarizationError_nonneg a A z r t
  have hti : 0 ≤ (t ^ 2)⁻¹ := by positivity
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hcc : ∑ j : Fin d, ∑ k : Fin d, |coarsenedCoefficient a A z r j k| ≤ (t ^ 2)⁻¹ * Y := by
    rw [hY, polarizationError, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ =>
      abs_coarsenedCoefficient_le a A z hr G hspan hreal hG2 hA ht j k
  have hmix : ∑ j : Fin d, ∑ k : Fin d,
      |⟪(WithLp.toLp 2 (unitVector j) : EuclideanSpace ℝ (Fin d)),
        (F.U ∘L (F.V)† - 1) (WithLp.toLp 2 (unitVector k))⟫_ℝ| ≤ (t ^ 2)⁻¹ * Y := by
    rw [hY, polarizationError, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => abs_inner_mixed_le a A z hr G hspan hreal hG2 ht j k
  have hb : ‖coarsenedOperator F.U F.V D‖ ≤ (t ^ 2)⁻¹ * Y := by
    refine (opNorm_le_sum_abs_inner (EuclideanSpace.basisFun (Fin d) ℝ) _).trans ?_
    simp only [← toLp_unitVector]
    refine le_of_eq_of_le ?_ hcc
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [coarsenedCoefficient_eq_inner a A z hr G hspan hreal hG2 hA]
  have hC : ‖F.U ∘L (F.V)† - 1‖ ≤ (t ^ 2)⁻¹ * Y := by
    refine (opNorm_le_sum_abs_inner (EuclideanSpace.basisFun (Fin d) ℝ) _).trans ?_
    simp only [← toLp_unitVector]
    exact hmix
  have hdim : Module.finrank ℝ F.H ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) := by
    rw [finrank_euclideanSpace_fin]
    exact F.finrank_H_le
  have hsq := norm_sub_add_coarsenedOperator_comp_le_sq hdim F.norm_U_le F.norm_V_le hδ
  have hdef := coarseFluxDefect_le a A z hr G hspan hreal hG2 hA
  refine ⟨(matrixSize_le_sum_abs _).trans hcc, hdef.trans ?_⟩
  have hT : ‖coarsenedOperator F.U F.V D‖ + ‖F.U ∘L (F.V)† - 1‖ ≤ 2 * ((t ^ 2)⁻¹ * Y) := by
    linarith
  have hT0 : 0 ≤ ‖coarsenedOperator F.U F.V D‖ + ‖F.U ∘L (F.V)† - 1‖ := by positivity
  have hT2 : (‖coarsenedOperator F.U F.V D‖ + ‖F.U ∘L (F.V)† - 1‖) ^ 2 ≤
      (2 * ((t ^ 2)⁻¹ * Y)) ^ 2 := pow_le_pow_left₀ hT0 hT 2
  have hK : 0 ≤ 4 * (1 + |Λ| + δ * 1) := by positivity
  calc ‖F.V - (D + coarsenedOperator F.U F.V D) ∘L F.U‖ * Real.sqrt |Λ|
      ≤ 4 * (1 + |Λ| + δ * 1) * (‖coarsenedOperator F.U F.V D‖ + ‖F.U ∘L (F.V)† - 1‖) ^ 2 *
          Real.sqrt |Λ| := mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg _)
    _ ≤ 4 * (1 + |Λ| + δ * 1) * (2 * ((t ^ 2)⁻¹ * Y)) ^ 2 * Real.sqrt |Λ| := by
        gcongr
    _ = Real.sqrt |Λ| * (4 * (1 + |Λ| + δ)) * (2 * ((t ^ 2)⁻¹ * Y)) ^ 2 := by ring

end Heat

end QSH
