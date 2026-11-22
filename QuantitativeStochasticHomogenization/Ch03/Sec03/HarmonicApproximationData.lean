import QuantitativeStochasticHomogenization.Ch03.Sec03.CorrectorTensorIdentity
import QuantitativeStochasticHomogenization.Ch03.Sec03.EllipsoidSmoothTransfer

/-!
# The data of the harmonic approximation

For an element `w` of `A₁` and a corrected affine function `ℓ = c + p · x + ∑ᵢ pᵢ φᵢ` of a
`SublinearCorrectorFamily`, the difference `v = w - ℓ` has the weak gradient
`∇w - (p + ∑ᵢ pᵢ ∇φᵢ)` on the whole space and is `a`-harmonic, since
`a (p + ∑ᵢ pᵢ ∇φᵢ) = ∑ᵢ pᵢ a(eᵢ + ∇φᵢ)`. Recentering the correctors by constants, with skew
constants for the flux correctors, keeps their weak gradients, their equations and the skew
symmetry. The entries of a coefficient field are bounded by `Λ`.
-/

open MeasureTheory Filter Set

noncomputable section

namespace QSH

variable {d : ℕ}

theorem HasWeakDivergence.mono_univ {U : Set (Vec d)} {F : Vec d → Vec d} {h : Vec d → ℝ}
    (H : HasWeakDivergence Set.univ F h) : HasWeakDivergence U F h := by
  refine ⟨fun i => (H.1 i).mono_set (Set.subset_univ _), H.2.1.mono_set (Set.subset_univ _),
    fun ψ hψ => ?_⟩
  have htest : IsSpatialTest Set.univ ψ := ⟨hψ.1, hψ.2.1, Set.subset_univ _⟩
  have h1 := H.2.2 ψ htest
  simp only [Measure.restrict_univ] at h1
  rw [setIntegral_eq_integral_of_tsupport_subset hψ.2.2]
  have e : ∫ x in U, dot (F x) (gradient ψ x) = ∫ x, dot (F x) (gradient ψ x) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have hx' : x ∉ tsupport ψ := fun h => hx (hψ.2.2 h)
    unfold dot gradient
    exact Finset.sum_eq_zero fun k _ => by
      rw [coordinateDerivative_eq_zero_of_notMem_tsupport hx' k, mul_zero]
  rw [e, h1]

theorem hasWeakDivergence_const_field (c : Vec d) :
    HasWeakDivergence Set.univ (fun _ => c) (fun _ => 0) := by
  refine ⟨fun k => locallyIntegrableOn_const _, locallyIntegrableOn_zero, fun ψ hψ => ?_⟩
  simp only [Measure.restrict_univ, zero_mul, integral_zero, neg_zero]
  have hint : ∀ k, Integrable (fun x => c k * coordinateDerivative k ψ x) := fun k =>
    ((isSpatialTest_coordinateDerivative hψ k).1.continuous.integrable_of_hasCompactSupport
      (isSpatialTest_coordinateDerivative hψ k).2.1).const_mul _
  change ∫ x, ∑ k, c k * coordinateDerivative k ψ x = 0
  rw [integral_finsetSum _ fun k _ => hint k]
  exact Finset.sum_eq_zero fun k _ => by
    rw [integral_const_mul, integral_coordinateDerivative_univ_eq_zero hψ k, mul_zero]

theorem HasWeakGradient.const_mul {U : Set (Vec d)} {f : Vec d → ℝ} {g : Vec d → Vec d}
    (h : HasWeakGradient U f g) (c : ℝ) :
    HasWeakGradient U (fun x => c * f x) (fun x => c • g x) := fun i =>
  hasWeakPartialDerivative_const_mul (h i) c

/-- The entries of a coefficient field are bounded by `Λ`. -/
theorem abs_coefficient_entry_le {Λ : ℝ} (a : CoefficientField d Λ) (x : Vec d) (j k : Fin d) :
    |a x j k| ≤ Λ := by
  have hs : a x k j = a x j k := by
    have h := congrFun (congrFun (a.symmetric x) j) k
    simpa [Matrix.transpose_apply] using h
  have quad : ∀ ξ : Vec d, dot ξ ((a x).mulVec ξ) = ∑ i, ∑ l, ξ i * a x i l * ξ l := by
    intro ξ
    unfold dot
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  have hsq : ∀ ξ : Vec d, euclideanSq ξ = ∑ i, ξ i * ξ i := fun ξ => rfl
  by_cases hjk : j = k
  · subst hjk
    have h1 := (a.elliptic x (unitVector j)).1
    have h2 := (a.elliptic x (unitVector j)).2
    rw [quad, hsq] at h1 h2
    simp [unitVector, Pi.single_apply] at h1 h2
    rw [abs_of_nonneg (by linarith)]
    exact h2
  · have hp := (a.elliptic x (unitVector j + unitVector k)).2
    have hm := (a.elliptic x (unitVector j + unitVector k)).1
    have hjj := (a.elliptic x (unitVector j)).1
    have hkk := (a.elliptic x (unitVector k)).1
    have hjj' := (a.elliptic x (unitVector j)).2
    have hkk' := (a.elliptic x (unitVector k)).2
    rw [quad, hsq] at hp hm hjj hkk hjj' hkk'
    simp only [unitVector, Pi.add_apply, Pi.single_apply] at hp hm hjj hkk hjj' hkk'
    simp only [mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, Finset.sum_add_distrib, add_mul, mul_add] at hp hm hjj hkk hjj' hkk'
    have hkj : k ≠ j := fun h => hjk h.symm
    simp only [hjk, hkj, ite_false, add_zero, zero_add] at hp hm hjj hkk hjj' hkk'
    rw [hs] at hp hm
    rw [abs_le]
    constructor <;> nlinarith

/-- `((a ξ)ⱼ)² ≤ d Λ² |ξ|²`. -/
theorem sq_coefficient_mulVec_le {Λ : ℝ} (a : CoefficientField d Λ) (x ξ : Vec d) (j : Fin d) :
    (a x).mulVec ξ j ^ 2 ≤ d * Λ ^ 2 * euclideanSq ξ := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => a x j k) ξ
  have e1 : (a x).mulVec ξ j = ∑ k, a x j k * ξ k := rfl
  have e2 : euclideanSq ξ = ∑ k, ξ k ^ 2 := by
    unfold euclideanSq dot
    exact Finset.sum_congr rfl fun k _ => by ring
  have hb : ∑ k, a x j k ^ 2 ≤ d * Λ ^ 2 := by
    calc ∑ k, a x j k ^ 2 ≤ ∑ _k : Fin d, Λ ^ 2 := Finset.sum_le_sum fun k _ => by
          have := abs_coefficient_entry_le a x j k
          nlinarith [abs_nonneg (a x j k), sq_abs (a x j k)]
      _ = d * Λ ^ 2 := by simp
  rw [e1, e2]
  refine h.trans ?_
  exact mul_le_mul_of_nonneg_right hb (Finset.sum_nonneg fun k _ => sq_nonneg _)

variable {Λ μ C₁ R₀ : ℝ} {a : CoefficientField d Λ} {D : Mat d}

/-- The gradient of `w - (c + p · x + ∑ᵢ pᵢ φᵢ)`. -/
def residualGrad (F : SublinearCorrectorFamily a D μ C₁ R₀) (w : HarmonicA1 a) (p : Vec d)
    (x : Vec d) : Vec d :=
  w.grad x + (-1 : ℝ) • ((0 + p) + ∑ i, p i • F.gφ i x)

theorem hasWeakGradient_residual (F : SublinearCorrectorFamily a D μ C₁ R₀) (w : HarmonicA1 a)
    (c : ℝ) (p : Vec d) :
    HasWeakGradient Set.univ (fun x => w.potential x - correctedAffineOf F.φ c p x)
      (residualGrad F w p) := by
  have hl := hasWeakGradient_add (hasWeakGradient_add (hasWeakGradient_const c)
    (hasWeakGradient_dot p)) (hasWeakGradient_finset_sum_const_mul Finset.univ p
      (fun i _ => F.weak_gradient_φ i))
  have h := hasWeakGradient_add w.weak_gradient (hl.const_mul (-1))
  have e : (fun x => w.potential x - correctedAffineOf F.φ c p x) =
      fun x => w.potential x + (-1) * (c + dot p x + ∑ i, p i * F.φ i x) := by
    funext x
    unfold correctedAffineOf
    ring
  rw [e]
  exact h

theorem coefficient_mulVec_residualGrad (F : SublinearCorrectorFamily a D μ C₁ R₀)
    (w : HarmonicA1 a) (p x : Vec d) :
    (a x).mulVec (residualGrad F w p x) =
      (a x).mulVec (w.grad x) + ∑ i, (-p i) • (a x).mulVec (unitVector i + F.gφ i x) := by
  have hp : p = ∑ i, p i • unitVector i := by
    funext j
    simp [unitVector, Pi.single_apply, Finset.sum_apply]
  have hsum : (0 + p) + ∑ i, p i • F.gφ i x = ∑ i, p i • (unitVector i + F.gφ i x) := by
    simp_rw [smul_add]
    rw [Finset.sum_add_distrib, zero_add, ← hp]
  unfold residualGrad
  rw [hsum, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sum, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_smul, smul_smul]
  congr 1
  ring

theorem hasWeakDivergence_residual (F : SublinearCorrectorFamily a D μ C₁ R₀)
    (w : HarmonicA1 a) (p : Vec d) :
    HasWeakDivergence Set.univ (fun x => (a x).mulVec (residualGrad F w p x)) (fun _ => 0) := by
  have h1 := hasWeakDivergence_finset_sum Finset.univ (F := fun i x =>
    (-p i) • (a x).mulVec (unitVector i + F.gφ i x)) fun i _ => by
      have := hasWeakDivergence_const_smul (F.harmonic i) (-p i)
      simpa using this
  have h := hasWeakDivergence_add w.harmonic h1
  have e : (fun x => (a x).mulVec (residualGrad F w p x)) =
      fun x => (a x).mulVec (w.grad x) + ∑ i, (-p i) • (a x).mulVec (unitVector i + F.gφ i x) := by
    funext x
    exact coefficient_mulVec_residualGrad F w p x
  rw [e]
  simpa using h

theorem memLp_residual_ball (F : SublinearCorrectorFamily a D μ C₁ R₀) (w : HarmonicA1 a)
    (c : ℝ) (p : Vec d) {R : ℝ} (hR : 0 < R) :
    MemLp (fun x => w.potential x - correctedAffineOf F.φ c p x) 2
      (volume.restrict (ball (0 : Vec d) R)) :=
  (w.local_energy R hR).1.sub (memLp_correctedAffineOf_ball F c p hR)

theorem memLp_grad_component_of_norm {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : MemLp (fun x => euclideanNorm (g x)) 2 (volume.restrict U))
    {i : Fin d} (hm : AEStronglyMeasurable (fun x => g x i) (volume.restrict U)) :
    MemLp (fun x => g x i) 2 (volume.restrict U) := by
  refine hg.of_le_mul (c := 1) hm
    (Eventually.of_forall fun x => ?_)
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ euclideanNorm (g x) from Real.sqrt_nonneg _)]
  exact coordinate_abs_le_euclideanNorm (g x) i

end QSH
