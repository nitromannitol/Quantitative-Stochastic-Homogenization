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

end QSH
