import QuantitativeStochasticHomogenization.Ch04.Sec03.PolarizationNearInverse

/-!
# Fluctuations of random vectors with controlled components

A random vector `V` whose components satisfy `|Vₖ - E Vₖ| ≤ c Tₖ` with `Tₖ ≤ O_s(θ)` has
`|V - E V|² ≤ O_{s/2}((2·2^{2/s})^d c² θ²)` and `E|V - E V|² ≤ d c² K θ²`
(`fluctuation_of_components`). Used for the polarization vectors of `J₁` and of its flux in the
proof of Lemma 4.13 here.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ}

open BaseExponent

section Components

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Fluctuations of a random vector from those of its components.** -/
theorem fluctuation_of_components [IsProbabilityMeasure P] {V : Ω → Vec d}
    {T : Fin d → Ω → ℝ} {s θ c : ℝ} (hs : 0 < s) (hθ : 0 < θ) (hc : 0 < c)
    (hVm : ∀ k, Measurable fun ω => V ω k)
    (hT : ∀ k, OsBound P (T k) s θ) (hT0 : ∀ k ω, 0 ≤ T k ω)
    (hle : ∀ k ω, |V ω k - ∫ ω', V ω' k ∂P| ≤ c * T k ω) :
    OsBound P (fun ω => euclideanSq (V ω - fun k => ∫ ω', V ω' k ∂P)) (s / 2)
      ((2 * (2 : ℝ) ^ (s / 2)⁻¹) ^ d * (c ^ 2 * θ ^ 2)) ∧
    Integrable (fun ω => euclideanSq (V ω - fun k => ∫ ω', V ω' k ∂P)) P ∧
    ∫ ω, euclideanSq (V ω - fun k => ∫ ω', V ω' k ∂P) ∂P ≤
      d * (c ^ 2 * (momentConstant (s / 2) * θ ^ 2)) := by
  have hcomp : ∀ k ω, (V ω - fun k => ∫ ω', V ω' k ∂P) k ^ 2 ≤ c ^ 2 * T k ω ^ 2 := by
    intro k ω
    have h := hle k ω
    have h0 := abs_nonneg (V ω k - ∫ ω', V ω' k ∂P)
    simp only [Pi.sub_apply]
    rw [← sq_abs (V ω k - ∫ ω', V ω' k ∂P), ← mul_pow]
    exact pow_le_pow_left₀ h0 h 2
  have hbound : ∀ ω, euclideanSq (V ω - fun k => ∫ ω', V ω' k ∂P) ≤ ∑ k, c ^ 2 * T k ω ^ 2 := by
    intro ω
    simp only [euclideanSq, dot, ← sq]
    exact Finset.sum_le_sum fun k _ => hcomp k ω
  have hYm : Measurable fun ω => euclideanSq (V ω - fun k => ∫ ω', V ω' k ∂P) := by
    simp only [euclideanSq, dot, Pi.sub_apply]
    exact Finset.measurable_sum _ fun k _ =>
      ((hVm k).sub measurable_const).mul ((hVm k).sub measurable_const)
  have hsq : ∀ k, OsBound P (fun ω => c ^ 2 * T k ω ^ 2) (s / 2) (c ^ 2 * θ ^ 2) := fun k =>
    ((hT k).sq (hT0 k)).const_mul (by positivity)
  have hsum := osBound_finset_sum_of_pos (P := P) Finset.univ (by positivity) (by positivity)
    fun k _ => hsq k
  rw [Finset.card_univ, Fintype.card_fin] at hsum
  have hmom : ∀ k, Integrable (fun ω => T k ω ^ 2) P ∧
      ∫ ω, T k ω ^ 2 ∂P ≤ momentConstant (s / 2) * θ ^ 2 := fun k =>
    (hT k).integral_sq_le (hT0 k)
  have hsumi : Integrable (fun ω => ∑ k, c ^ 2 * T k ω ^ 2) P :=
    integrable_finsetSum _ fun k _ => (hmom k).1.const_mul _
  have hYi : Integrable (fun ω => euclideanSq (V ω - fun k => ∫ ω', V ω' k ∂P)) P :=
    hsumi.mono' hYm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (euclideanSq_nonneg _)]
      exact hbound ω)
  refine ⟨hsum.of_le hYm hbound, hYi, ?_⟩
  calc ∫ ω, euclideanSq (V ω - fun k => ∫ ω', V ω' k ∂P) ∂P
      ≤ ∫ ω, ∑ k, c ^ 2 * T k ω ^ 2 ∂P :=
        integral_mono_ae hYi hsumi (Filter.Eventually.of_forall hbound)
    _ = ∑ k, c ^ 2 * ∫ ω, T k ω ^ 2 ∂P := by
        rw [integral_finsetSum _ fun k _ => (hmom k).1.const_mul _]
        exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _
    _ ≤ ∑ _k : Fin d, c ^ 2 * (momentConstant (s / 2) * θ ^ 2) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hmom k).2 (sq_nonneg c)
    _ = d * (c ^ 2 * (momentConstant (s / 2) * θ ^ 2)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Components

end QSH
