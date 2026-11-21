import QuantitativeStochasticHomogenization.Ch01.Sec02SubadditiveQuantity
import QuantitativeStochasticHomogenization.Ch04.Sec01.Proposition43

/-!
# Bounds on the Dirichlet energy `μ(U, e)`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.2, the bounds `½|e|² ≤ μ(U, e) ≤ ½Λ|e|²` of the Dirichlet energy (1.7) (used in
Lemma 1.1 and Definition 1.2).

For a measurable set `U` of finite positive volume:

* `dirichletEnergy_le`: `μ(U, e) ≤ ½Λ|e|²`, from the trial `u = 0`;
* `le_dirichletEnergy`: `½|e|² ≤ μ(U, e)`, from `a ≥ I`, Jensen's inequality and the vanishing of
  the mean of the gradient of a function of `H¹₀(U)` (`setIntegral_eq_zero_of_H01`), which
  follows from the approximation by smooth compactly supported functions and
  `∫ ∂ᵢφ = 0` (`integral_coordinateDerivative_eq_zero`).
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- The integral of a partial derivative of a smooth compactly supported function vanishes. -/
theorem integral_coordinateDerivative_eq_zero {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hφ : IsSpatialTest U φ) (i : Fin d) : ∫ x, coordinateDerivative i φ x = 0 := by
  obtain ⟨hs, hc, -⟩ := hφ
  have hdiff : Differentiable ℝ φ := hs.differentiable (by simp)
  have hcont : Continuous fun x => fderiv ℝ φ x (unitVector i) :=
    (hs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hint : Integrable fun x => fderiv ℝ φ x (unitVector i) :=
    hcont.integrable_of_hasCompactSupport (hc.fderiv_apply ℝ (unitVector i))
  have h : ∫ x, (fun _ : Vec d => (1 : ℝ)) x * fderiv ℝ φ x (unitVector i) =
      -∫ x, fderiv ℝ (fun _ : Vec d => (1 : ℝ)) x (unitVector i) * φ x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (by simp) (by simpa using hint)
      (by simpa using hs.continuous.integrable_of_hasCompactSupport hc)
      (fun x _ => differentiableAt_const _) (fun x _ => hdiff x)
  simpa [coordinateDerivative] using h

theorem integrable_euclideanSq_of_memLp {μ : Measure (Vec d)} {g : Vec d → Vec d}
    (hg : MemLp g 2 μ) : Integrable (fun x => euclideanSq (g x)) μ := by
  simp only [euclideanSq, dot, ← sq]
  exact integrable_finsetSum _ fun i _ => (MemLp.eval hg i).integrable_sq

/-- **The mean of the gradient of a function of `H¹₀(U)` vanishes.** -/
theorem setIntegral_eq_zero_of_H01 {U : Set (Vec d)} (hUm : MeasurableSet U)
    (hU : volume U ≠ ⊤) {u : Vec d → ℝ} {g : Vec d → Vec d} (hu : H01 U u g) (i : Fin d) :
    ∫ x in U, g x i = 0 := by
  obtain ⟨-, hg, -, v, hv, -, hconv⟩ := hu
  have hfin : IsFiniteMeasure (volume.restrict U) := ⟨by rw [Measure.restrict_apply_univ]; exact hU.lt_top⟩
  have hgi : Integrable (fun x => g x i) (volume.restrict U) := (MemLp.eval hg i).integrable one_le_two
  -- the approximants have mean zero
  have hgradv : ∀ n, Continuous (gradient (v n)) := fun n =>
    continuous_pi fun l => ((hv n).1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgradvc : ∀ n, HasCompactSupport (gradient (v n)) := fun n => by
    refine (hv n).2.1.mono' fun x hx => ?_
    by_contra hxs
    exact hx (by
      have h : fderiv ℝ (v n) x = 0 := fderiv_of_notMem_tsupport ℝ hxs
      funext l
      simp [gradient, coordinateDerivative, h])
  have hvint : ∀ n, Integrable (fun x => coordinateDerivative i (v n) x) (volume.restrict U) :=
    fun n => ((continuous_apply i).comp (hgradv n)).integrable_of_hasCompactSupport
      ((hgradvc n).comp_left (g := fun w : Vec d => w i) rfl) |>.restrict
  have hvi : ∀ n, ∫ x in U, coordinateDerivative i (v n) x = 0 := by
    intro n
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact integral_coordinateDerivative_eq_zero (hv n) i
    · intro x hx
      have hxs : x ∉ tsupport (v n) := fun h => hx ((hv n).2.2 h)
      have h : fderiv ℝ (v n) x = 0 := fderiv_of_notMem_tsupport ℝ hxs
      simp [coordinateDerivative, h]
  -- the energies of the differences
  have hEint : ∀ n, Integrable (fun x => euclideanSq (gradient (v n) x - g x)) (volume.restrict U) := by
    intro n
    have hm : MemLp (gradient (v n)) 2 (volume.restrict U) :=
      ((hgradv n).memLp_of_hasCompactSupport (hgradvc n)).restrict U
    exact integrable_euclideanSq_of_memLp (hm.sub hg)
  set V : ℝ := (volume U).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have key : ∀ δ : ℝ, 0 < δ → |∫ x in U, g x i| ≤ δ / 2 * V := by
    intro δ hδ
    have hbound : ∀ n, |∫ x in U, g x i| ≤ δ / 2 * V +
        1 / (2 * δ) * ∫ x in U, euclideanSq (gradient (v n) x - g x) := by
      intro n
      have hdiff : (∫ x in U, g x i) = ∫ x in U, (g x i - coordinateDerivative i (v n) x) := by
        rw [integral_sub hgi (hvint n), hvi n, sub_zero]
      rw [hdiff]
      refine (abs_integral_le_integral_abs).trans ?_
      have hpt : ∀ x, |g x i - coordinateDerivative i (v n) x| ≤
          δ / 2 + 1 / (2 * δ) * euclideanSq (gradient (v n) x - g x) := by
        intro x
        have hc : (g x i - coordinateDerivative i (v n) x) ^ 2 ≤
            euclideanSq (gradient (v n) x - g x) := by
          have : (g x i - coordinateDerivative i (v n) x) ^ 2 =
              (gradient (v n) x - g x) i * (gradient (v n) x - g x) i := by
            simp only [Pi.sub_apply, gradient]; ring
          rw [this]
          exact Finset.single_le_sum (f := fun l => (gradient (v n) x - g x) l *
            (gradient (v n) x - g x) l) (fun l _ => mul_self_nonneg _) (Finset.mem_univ i)
        have h1 : |g x i - coordinateDerivative i (v n) x| ≤
            δ / 2 + 1 / (2 * δ) * (g x i - coordinateDerivative i (v n) x) ^ 2 := by
          have hkey : δ / 2 + 1 / (2 * δ) * (g x i - coordinateDerivative i (v n) x) ^ 2 -
              |g x i - coordinateDerivative i (v n) x| =
              (|g x i - coordinateDerivative i (v n) x| - δ) ^ 2 / (2 * δ) := by
            rw [← sq_abs (g x i - coordinateDerivative i (v n) x)]
            field_simp
            ring
          have : 0 ≤ (|g x i - coordinateDerivative i (v n) x| - δ) ^ 2 / (2 * δ) := by positivity
          linarith
        have h2 : 1 / (2 * δ) * (g x i - coordinateDerivative i (v n) x) ^ 2 ≤
            1 / (2 * δ) * euclideanSq (gradient (v n) x - g x) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
        linarith
      calc ∫ x in U, |g x i - coordinateDerivative i (v n) x|
          ≤ ∫ x in U, (δ / 2 + 1 / (2 * δ) * euclideanSq (gradient (v n) x - g x)) :=
            integral_mono_ae (hgi.sub (hvint n)).abs ((integrable_const _).add
              ((hEint n).const_mul _)) (Filter.Eventually.of_forall hpt)
        _ = δ / 2 * V + 1 / (2 * δ) * ∫ x in U, euclideanSq (gradient (v n) x - g x) := by
            rw [integral_add (integrable_const _) ((hEint n).const_mul _), integral_const,
              integral_const_mul, smul_eq_mul, Measure.real, Measure.restrict_apply_univ, hV]
            ring
    have hlim : Tendsto (fun n => δ / 2 * V +
        1 / (2 * δ) * ∫ x in U, euclideanSq (gradient (v n) x - g x)) atTop (𝓝 (δ / 2 * V)) := by
      have := (hconv.const_mul (1 / (2 * δ))).const_add (δ / 2 * V)
      simpa using this
    exact ge_of_tendsto' hlim hbound
  by_contra hne
  have hpos : 0 < |∫ x in U, g x i| := abs_pos.mpr hne
  rcases hV0.lt_or_eq with hVp | hV0'
  · have : |∫ x in U, g x i| ≤ |∫ x in U, g x i| / 2 := by
      calc |∫ x in U, g x i| ≤ |∫ x in U, g x i| / V / 2 * V := key _ (div_pos hpos hVp)
        _ = |∫ x in U, g x i| / 2 := by field_simp
    linarith
  · have := key 1 one_pos
    rw [← hV0', mul_zero] at this
    linarith

end QSH
