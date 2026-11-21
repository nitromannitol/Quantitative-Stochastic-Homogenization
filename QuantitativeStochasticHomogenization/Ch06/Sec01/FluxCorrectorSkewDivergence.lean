import QuantitativeStochasticHomogenization.Ch06.Sec01.FluxCorrectorDivergenceProof
import QuantitativeStochasticHomogenization.Ch06.Sec01.FluxCorrectorSkew
import QuantitativeStochasticHomogenization.Ch03.Sec03.CorrectedAffine

/-!
# The skew part of the flux corrector

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 6.1, (6.5)–(6.6). Since `S_{jk} + S_{kj}` is almost everywhere constant, the skew part
`(S_{jk} - S_{kj}) / 2` differs from `S_{jk}` by a constant. It is skew symmetric at every point,
its weak gradient is `(∇S_{jk} - ∇S_{kj}) / 2`, and its rows have the same weak divergence
`(a(e + ∇φ_e))_j - D_j` as the rows of `S`.
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ}

/-- If the rows of `σ` have weak divergence `f j` and every `σ_{jk} + σ_{kj}` is almost
everywhere constant, then the rows of the skew part `(σ - σᵀ) / 2` have the same divergence. -/
theorem hasWeakDivergence_skew_row {σ : Vec d → Mat d} {f : Fin d → Vec d → ℝ}
    (hdiv : ∀ j, HasWeakDivergence Set.univ (fun x k => σ x j k) (f j))
    (hsym : ∀ j k, ∃ c : ℝ, ∀ᵐ x ∂(volume : Measure (Vec d)), σ x j k + σ x k j = c)
    (j : Fin d) :
    HasWeakDivergence Set.univ (fun x k => (σ x j k - σ x k j) / 2) (f j) := by
  choose c hc using hsym j
  have hall : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ k, σ x j k + σ x k j = c k :=
    ae_all_iff.2 hc
  have h1 := hasWeakDivergence_add (hdiv j)
    (hasWeakDivergence_const (-((1 / 2 : ℝ) • (fun k => c k))))
  refine h1.congr_ae ?_ (Eventually.of_forall fun x => by simp)
  filter_upwards [hall] with x hx
  funext k
  have hk := hx k
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  linarith

/-- The weak gradient of the skew part `(σ_{jk} - σ_{kj}) / 2`. -/
theorem hasWeakGradient_skew {σ : Vec d → Mat d} {G : Fin d → Fin d → Vec d → Vec d}
    (hσ : ∀ j k, HasWeakGradient Set.univ (fun x => σ x j k) (G j k)) (j k : Fin d) :
    HasWeakGradient Set.univ (fun x => (σ x j k - σ x k j) / 2)
      (fun x => (1 / 2 : ℝ) • (G j k x - G k j x)) := by
  intro i
  have h := hasWeakPartialDerivative_add (hasWeakPartialDerivative_const_mul (hσ j k i) (1 / 2))
    (hasWeakPartialDerivative_const_mul (hσ k j i) (-(1 / 2)))
  convert h using 1
  · funext x
    ring
  · funext x
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring

/-- **Lemma 6.1, (6.5)–(6.6), the skew flux corrector.** For every flux corrector `S` there is a
constant vector `D` such that, almost surely, the skew part `(S_{jk} - S_{kj}) / 2` has weak
gradient `(∇S_{jk} - ∇S_{kj}) / 2` and rows of weak divergence `(a(e + ∇φ_e))_j - D_j`. -/
theorem FluxCorrector.exists_skew_divergence {Λ : ℝ} {P : Measure (CoefficientField d Λ)}
    (hd : 2 ≤ d) (hΛ : 1 < Λ) (hP : LawHypotheses P) {e : Vec d} (he : euclideanNorm e = 1)
    {φ : Corrector P e} (S : FluxCorrector φ) :
    ∃ D : Vec d, ∀ᵐ a ∂P, ∀ j,
      HasWeakDivergence Set.univ (fun x k => (S.potential a x j k - S.potential a x k j) / 2)
        (fun x => ((a x).mulVec (e + φ.grad a x)) j - D j) ∧
      ∀ k, HasWeakGradient Set.univ (fun x => (S.potential a x j k - S.potential a x k j) / 2)
        (fun x => (1 / 2 : ℝ) • (S.grad a j k x - S.grad a k j x)) := by
  obtain ⟨D, hD⟩ := fluxCorrectorDivergence d hd Λ hΛ P hP e he φ S
  refine ⟨D, ?_⟩
  filter_upwards [hD, S.ae_add_transpose_eq_const, S.weak_gradient] with a ha hsym hw
  intro j
  exact ⟨hasWeakDivergence_skew_row
    (f := fun j x => ((a x).mulVec (e + φ.grad a x)) j - D j) ha hsym j,
    fun k => hasWeakGradient_skew hw j k⟩

end QSH
