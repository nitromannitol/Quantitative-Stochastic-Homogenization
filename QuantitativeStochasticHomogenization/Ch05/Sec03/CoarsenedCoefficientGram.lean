import QuantitativeStochasticHomogenization.Ch04.Sec01.GramSpace
import QuantitativeStochasticHomogenization.Ch04.Sec05.GaussianMasses
import QuantitativeStochasticHomogenization.Ch05.Sec03HeuristicScalingLimit
import QuantitativeStochasticHomogenization.Ch04.Sec04.CorrectedSpanEnergy

/-!
# Section 5.3: the coarsened coefficients on the Gram space

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 5.3, Definition 5.23 and Lemma 5.24, for one coefficient field.

Suppose that the gradients of `A₁` are, up to null sets, exactly the fields `G ξ` of a linear family
with `∫ Φ_{z,r} |G ξ|² < ∞` ((4.12)). On the Gram space `H` of this family, with the maps `U` and `V`
of the averages of the gradient and of the flux, `J₁(Φ_{z,r}, p, q) = ½ ‖U^* q - V^* p‖²`. Then:

* the coarsened coefficient `b_r(z)` of (5.62) is the matrix of `b = V V^* - ā U V^*`
  (`toEuclideanCLM_coarsenedCoefficient`), and (5.62) holds for all `p, p'`
  (`dot_coarsenedCoefficient_mulVec`);
* the flux defect of (5.64) is at most `√Λ ‖V - (ā + b) U‖` (`coarseFluxDefect_le`).
-/

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- **The gradients of `A₁` form a linear family** ((4.12), Theorem 3.8 with `k = 1`): there is a
linear family `ξ ↦ G ξ` such that every element of `A₁` has gradient `G ξ` for some `ξ`, every
`G ξ` is the gradient of an element of `A₁`, up to null sets, and `∫ Ψ |G ξ|² < ∞`. -/
def LinearA1Gradients (a : CoefficientField d Λ) (mask : Vec d → ℝ) : Prop :=
  ∃ G : Vec d →ₗ[ℝ] Vec d → Vec d,
    (∀ w : HarmonicA1 a, ∃ ξ, w.grad =ᵐ[volume] G ξ) ∧
    (∀ ξ, ∃ w : HarmonicA1 a, w.grad =ᵐ[volume] G ξ) ∧
    ∀ ξ, Integrable (fun x => mask x * euclideanSq (G ξ x))

/-- The Gram family of a linear family of gradients of `A₁` against `Φ_{z,r}`. -/
def heatGramFamily (a : CoefficientField d Λ) (z : Vec d) {r : ℝ} (hr : 0 < r)
    (G : Vec d →ₗ[ℝ] Vec d → Vec d) (hreal : ∀ ξ, ∃ w : HarmonicA1 a, w.grad =ᵐ[volume] G ξ)
    (hG2 : ∀ ξ, Integrable (fun x => heatKernel z r x * euclideanSq (G ξ x))) :
    GramFamily d Λ where
  coeff := a
  mask := heatKernel z r
  field := G
  mask_nonneg := heatKernel_nonneg z r
  integrable_mask := integrable_heatKernel z hr
  integral_mask_le := (integral_heatKernel z hr).le
  aemeasurable_field ξ := by
    obtain ⟨w, hw⟩ := hreal ξ
    exact w.aemeasurable_grad.congr hw
  integrable_sq := hG2

/-! ## The matrix `ā` as an operator -/

theorem inner_toEuclideanCLM_symm {A : Mat d} (hA : A.transpose = A)
    (x y : EuclideanSpace ℝ (Fin d)) :
    ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A y⟫_ℝ = ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) A x, y⟫_ℝ := by
  rw [← WithLp.toLp_ofLp (p := 2) x, ← WithLp.toLp_ofLp (p := 2) y, Matrix.toEuclideanCLM_toLp,
    Matrix.toEuclideanCLM_toLp, inner_toLp_toLp_eq_dot, inner_toLp_toLp_eq_dot,
    dot_mulVec_comm hA, dot_eq_dotProduct, dot_eq_dotProduct, dotProduct_comm]

theorem toLp_unitVector (j : Fin d) :
    (WithLp.toLp 2 (unitVector j) : EuclideanSpace ℝ (Fin d)) =
      EuclideanSpace.basisFun (Fin d) ℝ j := by
  rw [EuclideanSpace.basisFun_apply, unitVector, PiLp.toLp_single]

theorem dot_unitVector_mulVec (M : Mat d) (j k : Fin d) :
    dot (unitVector j) (M.mulVec (unitVector k)) = M j k := by
  rw [dot_eq_dotProduct, unitVector, unitVector, Matrix.mulVec_single, single_dotProduct]
  simp

section Heat

variable (a : CoefficientField d Λ) (A : Mat d) (z : Vec d) {r : ℝ} (hr : 0 < r)
  (G : Vec d →ₗ[ℝ] Vec d → Vec d)
  (hspan : ∀ w : HarmonicA1 a, ∃ ξ, w.grad =ᵐ[volume] G ξ)
  (hreal : ∀ ξ, ∃ w : HarmonicA1 a, w.grad =ᵐ[volume] G ξ)
  (hG2 : ∀ ξ, Integrable (fun x => heatKernel z r x * euclideanSq (G ξ x)))

include hspan in
theorem J1Heat_eq_gramEnergy (p q : Vec d) :
    J1Heat a z r p q = gramEnergy (heatGramFamily a z hr G hreal hG2).U
      (heatGramFamily a z hr G hreal hG2).V (WithLp.toLp 2 p) (WithLp.toLp 2 q) :=
  GramFamily.J1_eq_gramEnergy (heatGramFamily a z hr G hreal hG2) hspan hreal p q

include hspan in
/-- The entries of `b_r(z)` are the matrix entries of `b = V V^* - ā U V^*`, (5.62). -/
theorem coarsenedCoefficient_eq_inner (hA : A.transpose = A) (j k : Fin d) :
    coarsenedCoefficient a A z r j k =
      ⟪(WithLp.toLp 2 (unitVector j) : EuclideanSpace ℝ (Fin d)),
        coarsenedOperator (heatGramFamily a z hr G hreal hG2).U
          (heatGramFamily a z hr G hreal hG2).V (Matrix.toEuclideanCLM (𝕜 := ℝ) A)
          (WithLp.toLp 2 (unitVector k))⟫_ℝ := by
  rw [inner_coarsenedOperator_eq_gramEnergy _ _ (inner_toEuclideanCLM_symm hA),
    Matrix.toEuclideanCLM_toLp, ← WithLp.toLp_add, ← WithLp.toLp_sub,
    ← J1Heat_eq_gramEnergy a z hr G hspan hreal hG2,
    ← J1Heat_eq_gramEnergy a z hr G hspan hreal hG2]
  rfl

include hspan in
/-- **`b_r(z)` is the matrix of `b`.** -/
theorem toEuclideanCLM_coarsenedCoefficient (hA : A.transpose = A) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (coarsenedCoefficient a A z r) =
      coarsenedOperator (heatGramFamily a z hr G hreal hG2).U
        (heatGramFamily a z hr G hreal hG2).V (Matrix.toEuclideanCLM (𝕜 := ℝ) A) := by
  refine ContinuousLinearMap.coe_injective
    ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis.ext fun k => ?_)
  refine InnerProductSpace.ext_inner_left_basis (EuclideanSpace.basisFun (Fin d) ℝ).toBasis fun j => ?_
  simp only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe]
  rw [← toLp_unitVector, ← toLp_unitVector, Matrix.toEuclideanCLM_toLp, inner_toLp_toLp_eq_dot,
    dot_unitVector_mulVec, coarsenedCoefficient_eq_inner a A z hr G hspan hreal hG2 hA]

include hr hspan hreal hG2 in
/-- **The identity (5.62) of Definition 5.23 for all `p, p'`**:
`p · b_r(z) p' = ½ (J₁(Φ_{z,r}, p + p', ā p) - J₁(Φ_{z,r}, p - p', ā p))`. -/
theorem dot_coarsenedCoefficient_mulVec (hA : A.transpose = A) (p p' : Vec d) :
    dot p ((coarsenedCoefficient a A z r).mulVec p') =
      (J1Heat a z r (p + p') (A.mulVec p) - J1Heat a z r (p - p') (A.mulVec p)) / 2 := by
  rw [← inner_toLp_toLp_eq_dot, ← Matrix.toEuclideanCLM_toLp,
    toEuclideanCLM_coarsenedCoefficient a A z hr G hspan hreal hG2 hA,
    inner_coarsenedOperator_eq_gramEnergy _ _ (inner_toEuclideanCLM_symm hA),
    Matrix.toEuclideanCLM_toLp, ← WithLp.toLp_add, ← WithLp.toLp_sub,
    ← J1Heat_eq_gramEnergy a z hr G hspan hreal hG2,
    ← J1Heat_eq_gramEnergy a z hr G hspan hreal hG2]

include hspan in
/-- The defect of a normalized element of `A₁` is the norm of the operator `V - (ā + b) U`
applied to its class. -/
theorem coarseFluxDefect_le (hA : A.transpose = A) :
    coarseFluxDefect a A z r ≤
      ‖(heatGramFamily a z hr G hreal hG2).V -
          (Matrix.toEuclideanCLM (𝕜 := ℝ) A +
            coarsenedOperator (heatGramFamily a z hr G hreal hG2).U
              (heatGramFamily a z hr G hreal hG2).V (Matrix.toEuclideanCLM (𝕜 := ℝ) A)) ∘L
            (heatGramFamily a z hr G hreal hG2).U‖ * Real.sqrt |Λ| := by
  set F := heatGramFamily a z hr G hreal hG2 with hF
  set M := F.V - (Matrix.toEuclideanCLM (𝕜 := ℝ) A +
    coarsenedOperator F.U F.V (Matrix.toEuclideanCLM (𝕜 := ℝ) A)) ∘L F.U with hM
  have hne : Set.Nonempty {e : ℝ | ∃ w : HarmonicA1 a,
      Integrable (fun x => heatKernel z r x * euclideanNorm (w.grad x) ^ 2) ∧
      Real.sqrt (∫ x, heatKernel z r x * euclideanNorm (w.grad x) ^ 2) ≤ 1 ∧
      e = euclideanNorm ((∫ x, heatKernel z r x • (a x).mulVec (w.grad x)) -
        (A + coarsenedCoefficient a A z r).mulVec (∫ x, heatKernel z r x • w.grad x))} := by
    refine ⟨_, zeroHarmonicA1 a, ?_, ?_, rfl⟩
    · simp [zeroHarmonicA1, euclideanNorm, euclideanSq, dot]
    · simp [zeroHarmonicA1, euclideanNorm, euclideanSq, dot]
  refine csSup_le hne ?_
  rintro e ⟨w, hint, hnorm, rfl⟩
  obtain ⟨ξ, hξ⟩ := hspan w
  have hgrad : (∫ x, heatKernel z r x • w.grad x) = ∫ x, F.mask x • F.field ξ x :=
    integral_congr_ae (hξ.mono fun x hx => by dsimp only; rw [hx]; rfl)
  have hflux : (∫ x, heatKernel z r x • (a x).mulVec (w.grad x)) =
      ∫ x, F.mask x • (F.coeff x).mulVec (F.field ξ x) :=
    integral_congr_ae (hξ.mono fun x hx => by dsimp only; rw [hx]; rfl)
  have henergy : (∫ x, heatKernel z r x * euclideanNorm (w.grad x) ^ 2) =
      ∫ x, F.mask x * euclideanSq (F.field ξ x) :=
    integral_congr_ae (hξ.mono fun x hx => by dsimp only; rw [hx, euclideanNorm_sq]; rfl)
  have hval : euclideanNorm ((∫ x, heatKernel z r x • (a x).mulVec (w.grad x)) -
      (A + coarsenedCoefficient a A z r).mulVec (∫ x, heatKernel z r x • w.grad x)) =
      ‖M (F.toH ξ)‖ := by
    rw [← norm_toLp, hgrad, hflux, hM, sub_apply,
      ContinuousLinearMap.comp_apply, F.U_toH, F.V_toH, WithLp.toLp_sub, Matrix.add_mulVec,
      WithLp.toLp_add, ← Matrix.toEuclideanCLM_toLp, ← Matrix.toEuclideanCLM_toLp,
      toEuclideanCLM_coarsenedCoefficient a A z hr G hspan hreal hG2 hA,
      add_apply]
  rw [hval]
  have hE0 : 0 ≤ ∫ x, F.mask x * euclideanSq (F.field ξ x) :=
    integral_nonneg fun x => mul_nonneg (F.mask_nonneg x) (euclideanSq_nonneg _)
  have hE1 : ∫ x, F.mask x * euclideanSq (F.field ξ x) ≤ 1 := by
    rw [← henergy]
    exact Real.sqrt_le_one.mp hnorm
  have hh : ‖F.toH ξ‖ ≤ Real.sqrt |Λ| := by
    rw [← Real.sqrt_sq (norm_nonneg _), F.norm_toH_sq]
    refine Real.sqrt_le_sqrt ((F.form_le_energy ξ).trans ?_)
    calc Λ * ∫ x, F.mask x * euclideanSq (F.field ξ x)
        ≤ |Λ| * ∫ x, F.mask x * euclideanSq (F.field ξ x) :=
          mul_le_mul_of_nonneg_right (le_abs_self Λ) hE0
      _ ≤ |Λ| * 1 := mul_le_mul_of_nonneg_left hE1 (abs_nonneg Λ)
      _ = |Λ| := mul_one _
  calc ‖M (F.toH ξ)‖ ≤ ‖M‖ * ‖F.toH ξ‖ := M.le_opNorm _
    _ ≤ ‖M‖ * Real.sqrt |Λ| := mul_le_mul_of_nonneg_left hh (norm_nonneg M)

end Heat

end QSH
