import QuantitativeStochasticHomogenization.Ch04.Sec01.J1HeatFormula
import QuantitativeStochasticHomogenization.Ch04.Sec01.J1HeatSharpBound
import QuantitativeStochasticHomogenization.Ch04.Sec01.EnergyQuantityBounds
import QuantitativeStochasticHomogenization.Ch04.Sec01.Proposition43
import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicApproximationProof
import QuantitativeStochasticHomogenization.Ch03.Sec03.DimensionA1
import QuantitativeStochasticHomogenization.Ch01.Sec04.FluxAverage
import QuantitativeStochasticHomogenization.Ch01.Sec03.DirichletEnergyCorrectorBounds
import QuantitativeStochasticHomogenization.Ch04.Sec01.HomogenizedBoundsFromMeasurability

/-!
# Definition 4.2 and Lemma 4.4: basic properties of `J₁`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.1. For a mask `Ψ ≥ 0` with `∫ Ψ = 1` such that `∇A₁` is a `d`-dimensional subspace of
`L²(Ψ)` (`J1Mask`; this holds almost surely for the heat kernel masks `Φ_{z,r}`,
`ae_j1Mask_heatKernel`), almost surely the quantity `J₁(Ψ, p, q)` of (4.8) and its maximizers
`v(·, Ψ, p, q)` in `A₁` (`IsJ1Maximizer`) satisfy (`lemma_4_4`):

* a maximizer exists, it is characterized by the first variation (4.13), and its gradient is
  unique (`exists_isJ1Maximizer`, `isJ1Maximizer_iff_firstVariation`, `IsJ1Maximizer.grad_ae_eq`);
* (4.14) `J₁ = ∫_Ψ ½ ∇v·a∇v` (`IsJ1Maximizer.J1_eq_integral`);
* linearity of `∇v` in `(p, q)`, homogeneity of `J₁` and the bounds (4.15)
  (`IsJ1Maximizer.grad_add`, `IsJ1Maximizer.grad_smul`, `J1_smul_smul`, `IsJ1Maximizer.bounds`);
* the polarization (4.16) (`IsJ1Maximizer.J1_add_add`);
* the uniform convexity (4.17)–(4.18) when `J₁` is nondegenerate at `Ψ` in the sense of
  Definition 4.2 (`J1Nondegenerate`, `uniformConvexity_left`, `uniformConvexity_right`);
* the second variation (4.19) (`IsJ1Maximizer.secondVariation`);
* the derivatives (4.20)–(4.21) (`IsJ1Maximizer.hasFDerivAt_left`,
  `IsJ1Maximizer.hasFDerivAt_right`).

The book obtains the maximizer from `∇A₁` being a `d`-dimensional subspace of `L²(Ψ)` (Theorem 3.8).
Here, almost surely, `A₁` is the set of corrected affine functions `ℓ_c + φ_c` (the first-order
Liouville theorem `firstOrderLiouville`, `J1Structure`), and the objective of (4.8) at the slope
`c` is `b·c - ½ c·Mc` with the Gram matrix `M_{ij} = ∫ Ψ Wᵢ·a Wⱼ` and the load
`bᵢ = ∫ Ψ (-p·a Wᵢ + q·Wᵢ)`, `Wᵢ = eᵢ + ∇φ_{eᵢ}` (`J1Objective_eq_quadratic`). That `∇A₁` is
`d`-dimensional in `L²(Ψ)` is the invertibility of `M`; the maximizers are the elements of `A₁` of
slope `M⁻¹ b` (`J1Slope`), and every property is an identity for the quadratic `b·c - ½ c·Mc`,
whose maximum is `½ b·M⁻¹ b` (`J1_eq_half_dot_slope`).

In the left inequality of (4.15) the book has `‖∇v‖²_{L²(Ψ)} ≤ J₁(Ψ, p, q)`; it holds with the
factor `½`, `½ ‖∇v‖²_{L²(Ψ)} ≤ J₁(Ψ, p, q)`, which follows from (4.14) and `a ≥ 1` (for `a = 1`
the elements of `A₁` are the affine functions, `J₁(Ψ, p, q) = ½ |q - p|²` and `∇v = q - p`).
-/

open MeasureTheory Filter Set Asymptotics
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent


section Algebra

/-- The completed square of the slope quadratic: for `M` symmetric and invertible,
`b·c - ½ c·Mc = ½ b·M⁻¹b - ½ (c - M⁻¹b)·M(c - M⁻¹b)`. -/
theorem slopeQuadratic_eq (M : Mat d) (hsym : M.transpose = M) (hunit : IsUnit M) (b c : Vec d) :
    dot b c - (1 / 2 : ℝ) * dot c (M.mulVec c) = (1 / 2 : ℝ) * dot b (M⁻¹.mulVec b) -
      (1 / 2 : ℝ) * dot (c - M⁻¹.mulVec b) (M.mulVec (c - M⁻¹.mulVec b)) := by
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hunit
  have hMM : M.mulVec (M⁻¹.mulVec b) = b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hs := dot_mulVec_comm_of_symm hsym (M⁻¹.mulVec b) c
  rw [hMM] at hs
  simp only [dot_eq_dotProduct] at hs
  simp only [dot_eq_dotProduct, Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, hMM]
  have e1 : c ⬝ᵥ b = b ⬝ᵥ c := dotProduct_comm _ _
  have e2 : (M⁻¹.mulVec b) ⬝ᵥ b = b ⬝ᵥ (M⁻¹.mulVec b) := dotProduct_comm _ _
  linarith

/-- At the maximum, `Mc = b`. -/
theorem mulVec_eq_of_slopeQuadratic_eq (M : Mat d) (hsym : M.transpose = M)
    (hpsd : ∀ c, 0 ≤ dot c (M.mulVec c)) (hunit : IsUnit M) {b c : Vec d}
    (h : dot b c - (1 / 2 : ℝ) * dot c (M.mulVec c) = (1 / 2 : ℝ) * dot b (M⁻¹.mulVec b)) :
    M.mulVec c = b := by
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hunit
  rw [slopeQuadratic_eq M hsym hunit b c] at h
  set e := c - M⁻¹.mulVec b with he
  have h0 : dot e (M.mulVec e) = 0 := by linarith
  have hz : M.mulVec e = 0 := by
    funext i
    have hcs := sq_dot_mulVec_le hsym hpsd e (unitVector i)
    rw [h0, mul_zero] at hcs
    have : dot (unitVector i) (M.mulVec e) = 0 := by
      nlinarith [sq_nonneg (dot (unitVector i) (M.mulVec e))]
    simpa [dot, unitVector, Pi.single_apply] using this
  have hMM : M.mulVec (M⁻¹.mulVec b) = b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have : M.mulVec c = M.mulVec e + M.mulVec (M⁻¹.mulVec b) := by
    rw [← Matrix.mulVec_add, he, sub_add_cancel]
  rw [this, hz, hMM, zero_add]

end Algebra

section Basic

variable {P : Measure (CoefficientField d Λ)}

/-- The almost sure description of `A₁` used for `J₁`: every element of `A₁` has, up to a null
set, the gradient of a corrected affine function, and the corrected affine functions belong to
`A₁`. -/
structure J1Structure (S : HomogenizationData P) (a : CoefficientField d Λ) : Prop where
  liouville : ∀ w : HarmonicA1 a, ∃ c : Vec d,
    ∀ᵐ x ∂(volume : Measure (Vec d)), w.grad x = correctedAffineGrad S a c x
  exists_affine : ∀ c : Vec d, ∃ w : HarmonicA1 a, w.grad = correctedAffineGrad S a c

/-- The description of `A₁` holds almost surely (Theorem 3.8 for `k = 1`). -/
theorem ae_j1Structure (hd : 2 ≤ d) (hΛ : 1 < Λ) (hP : LawHypotheses P)
    (S : HomogenizationData P) : ∀ᵐ a ∂P, J1Structure S a := by
  filter_upwards [firstOrderLiouville d hd Λ hΛ P hP S, ae_exists_harmonicA1_correctedAffine S]
    with a hL hex
  refine ⟨fun w => ?_, fun c => ?_⟩
  · obtain ⟨-, c, -, hc⟩ := hL w
    exact ⟨c, hc⟩
  · obtain ⟨w, -, hw⟩ := hex c
    exact ⟨w, hw⟩

/-- A mask of (4.8): `Ψ ≥ 0`, `Ψ ∈ L¹`, `∫ Ψ = 1`, and `∇A₁` is a `d`-dimensional subspace of
`L²(Ψ)`: the corrector columns `Wᵢ = eᵢ + ∇φ_{eᵢ}` belong to `L²(Ψ)` and their Gram matrix
`∫ Ψ Wᵢ·a Wⱼ` is invertible. -/
structure J1Mask (S : HomogenizationData P) (a : CoefficientField d Λ) (Ψ : Vec d → ℝ) :
    Prop where
  nonneg : ∀ x, 0 ≤ Ψ x
  integrable : Integrable Ψ
  integral_eq_one : ∫ x, Ψ x = 1
  energy : ∀ i : Fin d, Integrable (fun x => Ψ x * euclideanSq (correctorColumn S a i x))
  gram_isUnit : IsUnit (J1Gram S a Ψ)

/-- Almost surely, every heat kernel mask `Φ_{z,r}` is a mask of (4.8). -/
theorem ae_j1Mask_heatKernel (hd : 2 ≤ d) (hΛ : 1 < Λ) (hP : LawHypotheses P)
    (S : HomogenizationData P) :
    ∀ᵐ a ∂P, ∀ (z : Vec d) (r : ℝ), 0 < r → J1Mask S a (heatKernel z r) := by
  filter_upwards [ae_integrable_heatKernel_mul_euclideanSq_correctorColumn hd hΛ hP S,
    ae_J1Heat_eq_half_dot_inv firstOrderLiouville hd hΛ hP S] with a hW hJ
  intro z r hr
  refine ⟨fun x => euclideanHeatKernel_nonneg (sq_nonneg r) (x - z),
    (integrable_euclideanHeatKernel (sq_pos_of_pos hr)).comp_sub_right z, ?_,
    fun i => hW i z r hr, (hJ z r hr 0 0).1⟩
  unfold heatKernel
  rw [integral_sub_right_eq_self, integral_euclideanHeatKernel (sq_pos_of_pos hr)]

/-- `v ∈ A₁` is a maximizer of `J₁(Ψ, p, q)`: the objective of (4.8) at `∇v` is `J₁(Ψ, p, q)`. -/
def IsJ1Maximizer (a : CoefficientField d Λ) (Ψ : Vec d → ℝ) (p q : Vec d) (v : HarmonicA1 a) :
    Prop :=
  j1Functional a Ψ p q v.grad = J1 a Ψ p q

/-- Definition 4.2: `J₁` is nondegenerate at `Ψ` if `J₁(Ψ, p, 0) ≥ ¼ p·āp` and
`J₁(Ψ, 0, q) ≥ ¼ q·ā⁻¹q` for all `p, q`. -/
def J1Nondegenerate (S : HomogenizationData P) (a : CoefficientField d Λ) (Ψ : Vec d → ℝ) :
    Prop :=
  ∀ p q : Vec d, (1 / 4 : ℝ) * dot p (S.homogenized.mulVec p) ≤ J1 a Ψ p 0 ∧
    (1 / 4 : ℝ) * dot q (S.homogenized⁻¹.mulVec q) ≤ J1 a Ψ 0 q

/-- The slope `M⁻¹ b` of the maximizers of `J₁(Ψ, p, q)`. -/
def J1Slope (S : HomogenizationData P) (a : CoefficientField d Λ) (Ψ : Vec d → ℝ) (p q : Vec d) :
    Vec d :=
  (J1Gram S a Ψ)⁻¹.mulVec (J1Load S a Ψ p q)

/-- The linear form `h ↦ g·h`. -/
def dotContinuousLinearMap (g : Vec d) : Vec d →L[ℝ] ℝ :=
  ∑ i, g i • ContinuousLinearMap.proj i

theorem dotContinuousLinearMap_apply (g h : Vec d) : dotContinuousLinearMap g h = dot g h := by
  simp [dotContinuousLinearMap, dot]

end Basic

section CorrectedAffine

variable {P : Measure (CoefficientField d Λ)}

theorem correctedAffineGrad_add (S : HomogenizationData P) (a : CoefficientField d Λ)
    (c c' x : Vec d) :
    correctedAffineGrad S a (c + c') x =
      correctedAffineGrad S a c x + correctedAffineGrad S a c' x := by
  simp only [correctedAffineGrad, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  abel

theorem measurable_correctedAffineGrad (S : HomogenizationData P) (a : CoefficientField d Λ)
    (c : Vec d) : Measurable (correctedAffineGrad S a c) := by
  have e : correctedAffineGrad S a c = fun x => ∑ i, c i • correctorColumn S a i x :=
    funext fun x => correctedAffineGrad_eq_sum S a c x
  rw [e]
  exact Finset.measurable_sum _ fun i _ => (measurable_correctorColumn S a i).const_smul (c i)

theorem integral_sub_sub_of_integrable {f g h : Vec d → ℝ} (hf : Integrable f) (hg : Integrable g)
    (hh : Integrable h) : ∫ x, (f x - g x - h x) = (∫ x, f x) - (∫ x, g x) - ∫ x, h x := by
  have hfg : Integrable (fun x => f x - g x) := hf.sub hg
  rw [integral_sub hfg hh, integral_sub hf hg]

theorem correctedAffineGrad_smul (S : HomogenizationData P) (a : CoefficientField d Λ) (t : ℝ)
    (c x : Vec d) : correctedAffineGrad S a (t • c) x = t • correctedAffineGrad S a c x := by
  simp only [correctedAffineGrad, Pi.smul_apply, smul_eq_mul, smul_add, Finset.smul_sum,
    mul_smul]

end CorrectedAffine

section Mask

variable {P : Measure (CoefficientField d Λ)} {S : HomogenizationData P} {a : CoefficientField d Λ}
  {Ψ : Vec d → ℝ}

theorem J1Mask.integrable_gram (hΨ : J1Mask S a Ψ) (i j : Fin d) :
    Integrable (fun x => Ψ x *
      dot (correctorColumn S a i x) ((a x).mulVec (correctorColumn S a j x))) := by
  have hWm := measurable_correctorColumn S a
  refine (((hΨ.energy i).add (hΨ.energy j)).const_mul Λ).mono'
    (hΨ.integrable.aestronglyMeasurable.mul
      (aestronglyMeasurable_dot_mulVec_of_measurable a (hWm i) (hWm j)))
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hΨ.nonneg x)]
  calc Ψ x * |dot (correctorColumn S a i x) ((a x).mulVec (correctorColumn S a j x))|
      ≤ Ψ x * (Λ * (euclideanSq (correctorColumn S a i x) +
          euclideanSq (correctorColumn S a j x))) :=
        mul_le_mul_of_nonneg_left (abs_dot_mulVec_le_mul_euclideanSq_add a x _ _) (hΨ.nonneg x)
    _ = Λ * (Ψ x * euclideanSq (correctorColumn S a i x) +
          Ψ x * euclideanSq (correctorColumn S a j x)) := by ring

theorem J1Mask.integrable_load (hΨ : J1Mask S a Ψ) (p q : Vec d) (i : Fin d) :
    Integrable (fun x => Ψ x *
      (-dot p ((a x).mulVec (correctorColumn S a i x)) + dot q (correctorColumn S a i x))) := by
  have hWm := measurable_correctorColumn S a
  have hconst : Integrable (fun x => Ψ x * (Λ * euclideanSq p + euclideanSq q)) :=
    hΨ.integrable.mul_const _
  have hdotq : AEStronglyMeasurable (fun x => dot q (correctorColumn S a i x)) volume := by
    have hc : Continuous fun v : Vec d => dot q v := by unfold dot; fun_prop
    exact (hc.measurable.comp (hWm i)).aestronglyMeasurable
  have hdotp := aestronglyMeasurable_dot_mulVec_of_measurable a (u := fun _ => p)
    measurable_const (hWm i)
  refine (hconst.add ((hΨ.energy i).const_mul (Λ + 1))).mono'
    (hΨ.integrable.aestronglyMeasurable.mul (hdotp.neg.add hdotq))
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hΨ.nonneg x)]
  have h1 := abs_dot_mulVec_le_mul_euclideanSq_add a x p (correctorColumn S a i x)
  have h2 := abs_dot_le_euclideanSq_add q (correctorColumn S a i x)
  have h3 : |(-dot p ((a x).mulVec (correctorColumn S a i x)) +
      dot q (correctorColumn S a i x))| ≤
      Λ * euclideanSq p + euclideanSq q + (Λ + 1) * euclideanSq (correctorColumn S a i x) := by
    calc _ ≤ |dot p ((a x).mulVec (correctorColumn S a i x))| +
          |dot q (correctorColumn S a i x)| := by
          simpa using abs_add_le (-dot p ((a x).mulVec (correctorColumn S a i x)))
            (dot q (correctorColumn S a i x))
      _ ≤ _ := by linarith [h1, h2]
  calc Ψ x * |(-dot p ((a x).mulVec (correctorColumn S a i x)) +
        dot q (correctorColumn S a i x))|
      ≤ Ψ x * (Λ * euclideanSq p + euclideanSq q +
          (Λ + 1) * euclideanSq (correctorColumn S a i x)) :=
        mul_le_mul_of_nonneg_left h3 (hΨ.nonneg x)
    _ = Ψ x * (Λ * euclideanSq p + euclideanSq q) +
          (Λ + 1) * (Ψ x * euclideanSq (correctorColumn S a i x)) := by ring

/-- **The bilinear form of the Gram matrix**: `∫ Ψ W_{c'}·a W_c = c'·Mc`. -/
theorem J1Mask.integral_dot_eq (hΨ : J1Mask S a Ψ) (c c' : Vec d) :
    Integrable (fun x => Ψ x * dot (correctedAffineGrad S a c' x)
      ((a x).mulVec (correctedAffineGrad S a c x))) ∧
    ∫ x, Ψ x * dot (correctedAffineGrad S a c' x) ((a x).mulVec (correctedAffineGrad S a c x)) =
      dot c' ((J1Gram S a Ψ).mulVec c) := by
  have hM := hΨ.integrable_gram
  obtain ⟨i1, e1⟩ := dot_J1Gram_mulVec_eq_integral S a _ hM c
  obtain ⟨i2, e2⟩ := dot_J1Gram_mulVec_eq_integral S a _ hM c'
  obtain ⟨i3, e3⟩ := dot_J1Gram_mulVec_eq_integral S a _ hM (c' + c)
  have hpt : ∀ x, Ψ x * dot (correctedAffineGrad S a c' x)
      ((a x).mulVec (correctedAffineGrad S a c x)) =
      (1 / 2 : ℝ) * (Ψ x * dot (correctedAffineGrad S a (c' + c) x)
        ((a x).mulVec (correctedAffineGrad S a (c' + c) x)) -
        Ψ x * dot (correctedAffineGrad S a c x) ((a x).mulVec (correctedAffineGrad S a c x)) -
        Ψ x * dot (correctedAffineGrad S a c' x)
          ((a x).mulVec (correctedAffineGrad S a c' x))) := fun x => by
    have hs := dot_mulVec_comm_of_symm (a.symmetric x) (correctedAffineGrad S a c x)
      (correctedAffineGrad S a c' x)
    rw [correctedAffineGrad_add]
    simp only [dot_eq_dotProduct, Matrix.mulVec_add, dotProduct_add, add_dotProduct] at hs ⊢
    change correctedAffineGrad S a c x ⬝ᵥ (a x).mulVec (correctedAffineGrad S a c' x) =
      correctedAffineGrad S a c' x ⬝ᵥ (a x).mulVec (correctedAffineGrad S a c x) at hs
    rw [hs]
    ring
  have hint : Integrable (fun x => (1 / 2 : ℝ) * (Ψ x * dot (correctedAffineGrad S a (c' + c) x)
        ((a x).mulVec (correctedAffineGrad S a (c' + c) x)) -
        Ψ x * dot (correctedAffineGrad S a c x) ((a x).mulVec (correctedAffineGrad S a c x)) -
        Ψ x * dot (correctedAffineGrad S a c' x)
          ((a x).mulVec (correctedAffineGrad S a c' x)))) := ((i3.sub i1).sub i2).const_mul _
  refine ⟨(funext hpt) ▸ hint, ?_⟩
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul,
    integral_sub_sub_of_integrable i3 i1 i2, ← e1, ← e2, ← e3]
  have hs := dot_mulVec_comm_of_symm (J1Gram_transpose S a Ψ) c c'
  simp only [dot_eq_dotProduct] at hs
  simp only [dot_eq_dotProduct, Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  linarith

/-- **The load**: `∫ Ψ (-p·a W_c + q·W_c) = b·c`. -/
theorem J1Mask.integral_load_eq (hΨ : J1Mask S a Ψ) (p q c : Vec d) :
    Integrable (fun x => Ψ x * (-dot p ((a x).mulVec (correctedAffineGrad S a c x)) +
      dot q (correctedAffineGrad S a c x))) ∧
    ∫ x, Ψ x * (-dot p ((a x).mulVec (correctedAffineGrad S a c x)) +
      dot q (correctedAffineGrad S a c x)) = dot (J1Load S a Ψ p q) c := by
  have hb := hΨ.integrable_load p q
  have hpt : ∀ x, Ψ x * (-dot p ((a x).mulVec (correctedAffineGrad S a c x)) +
      dot q (correctedAffineGrad S a c x)) = ∑ i, c i * (Ψ x *
        (-dot p ((a x).mulVec (correctorColumn S a i x)) + dot q (correctorColumn S a i x))) := by
    intro x
    rw [correctedAffineGrad_eq_sum]
    simp only [dot_eq_dotProduct, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum,
      dotProduct_smul, smul_eq_mul, Finset.mul_sum, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hint : Integrable (fun x => ∑ i, c i * (Ψ x *
      (-dot p ((a x).mulVec (correctorColumn S a i x)) + dot q (correctorColumn S a i x)))) :=
    integrable_finsetSum _ fun i _ => (hb i).const_mul _
  refine ⟨(funext hpt) ▸ hint, ?_⟩
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_finsetSum _ fun i _ => (hb i).const_mul _]
  simp only [integral_const_mul]
  simp only [dot, J1Load]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `∫ Ψ g·a g' = c·Mc'` for fields `g, g'` equal almost everywhere to the corrected affine
gradients of slopes `c, c'`. -/
theorem J1Mask.integral_grad_dot_eq (hΨ : J1Mask S a Ψ) {g g' : Vec d → Vec d} {c c' : Vec d}
    (hg : ∀ᵐ x ∂(volume : Measure (Vec d)), g x = correctedAffineGrad S a c x)
    (hg' : ∀ᵐ x ∂(volume : Measure (Vec d)), g' x = correctedAffineGrad S a c' x) :
    Integrable (fun x => Ψ x * dot (g x) ((a x).mulVec (g' x))) ∧
    ∫ x, Ψ x * dot (g x) ((a x).mulVec (g' x)) = dot c ((J1Gram S a Ψ).mulVec c') := by
  obtain ⟨hi, he⟩ := hΨ.integral_dot_eq c' c
  have hae : (fun x => Ψ x * dot (g x) ((a x).mulVec (g' x))) =ᵐ[volume]
      fun x => Ψ x * dot (correctedAffineGrad S a c x)
        ((a x).mulVec (correctedAffineGrad S a c' x)) := by
    filter_upwards [hg, hg'] with x hx hy
    rw [hx, hy]
  exact ⟨hi.congr hae.symm, (integral_congr_ae hae).trans he⟩

/-- `∫ Ψ (-p·a g + q·g) = b·c` for a field `g` equal almost everywhere to the corrected affine
gradient of slope `c`. -/
theorem J1Mask.integral_load_grad_eq (hΨ : J1Mask S a Ψ) (p q : Vec d) {g : Vec d → Vec d}
    {c : Vec d} (hg : ∀ᵐ x ∂(volume : Measure (Vec d)), g x = correctedAffineGrad S a c x) :
    Integrable (fun x => Ψ x * (-dot p ((a x).mulVec (g x)) + dot q (g x))) ∧
    ∫ x, Ψ x * (-dot p ((a x).mulVec (g x)) + dot q (g x)) = dot (J1Load S a Ψ p q) c := by
  obtain ⟨hi, he⟩ := hΨ.integral_load_eq p q c
  have hae : (fun x => Ψ x * (-dot p ((a x).mulVec (g x)) + dot q (g x))) =ᵐ[volume]
      fun x => Ψ x * (-dot p ((a x).mulVec (correctedAffineGrad S a c x)) +
        dot q (correctedAffineGrad S a c x)) := by
    filter_upwards [hg] with x hx
    rw [hx]
  exact ⟨hi.congr hae.symm, (integral_congr_ae hae).trans he⟩

/-- The objective of (4.8) at a field equal almost everywhere to the corrected affine gradient of
slope `c` is integrable and equals `b·c - ½ c·Mc`. -/
theorem J1Mask.j1Functional_eq (hΨ : J1Mask S a Ψ) (p q : Vec d) {g : Vec d → Vec d}
    {c : Vec d} (hg : ∀ᵐ x ∂(volume : Measure (Vec d)), g x = correctedAffineGrad S a c x) :
    Integrable (fun x => Ψ x * (-(1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x)) -
      dot p ((a x).mulVec (g x)) + dot q (g x))) ∧
    j1Functional a Ψ p q g =
      dot (J1Load S a Ψ p q) c - (1 / 2 : ℝ) * dot c ((J1Gram S a Ψ).mulVec c) := by
  obtain ⟨i1, -⟩ := hΨ.integral_grad_dot_eq hg hg
  obtain ⟨i2, -⟩ := hΨ.integral_load_grad_eq p q hg
  have hpt : (fun x => Ψ x * (-(1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x)) -
      dot p ((a x).mulVec (g x)) + dot q (g x))) = fun x =>
      -(1 / 2 : ℝ) * (Ψ x * dot (g x) ((a x).mulVec (g x))) +
        Ψ x * (-dot p ((a x).mulVec (g x)) + dot q (g x)) := funext fun x => by ring
  refine ⟨hpt ▸ (i1.const_mul _).add i2, ?_⟩
  rw [j1Functional_congr_ae a _ p q hg,
    ← J1Objective_eq_quadratic S a _ p q hΨ.integrable_gram (hΨ.integrable_load p q) c]
  rfl

/-- `J₁(Ψ, p, q)` is the supremum over the slopes of `b·c - ½ c·Mc`. -/
theorem J1Structure.J1_eq_sSup (hS : J1Structure S a) (hΨ : J1Mask S a Ψ) (p q : Vec d) :
    J1 a Ψ p q = sSup (Set.range fun c : Vec d =>
      dot (J1Load S a Ψ p q) c - (1 / 2 : ℝ) * dot c ((J1Gram S a Ψ).mulVec c)) := by
  rw [J1_eq_sSup_j1Functional]
  congr 1
  ext e
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨c, hc⟩ := hS.liouville w
    exact ⟨c, (hΨ.j1Functional_eq p q hc).2.symm⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨w, hw⟩ := hS.exists_affine c
    exact ⟨w, (hΨ.j1Functional_eq p q (Eventually.of_forall fun x => by rw [hw])).2.symm⟩

theorem J1Mask.mulVec_J1Slope (hΨ : J1Mask S a Ψ) (p q : Vec d) :
    (J1Gram S a Ψ).mulVec (J1Slope S a Ψ p q) = J1Load S a Ψ p q := by
  have hdet : IsUnit (J1Gram S a Ψ).det := (Matrix.isUnit_iff_isUnit_det _).mp hΨ.gram_isUnit
  rw [J1Slope, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

/-- **`J₁(Ψ, p, q) = ½ b·M⁻¹ b`.** -/
theorem J1Structure.J1_eq_half_dot_slope (hS : J1Structure S a) (hΨ : J1Mask S a Ψ)
    (p q : Vec d) :
    J1 a Ψ p q = (1 / 2 : ℝ) * dot (J1Load S a Ψ p q) (J1Slope S a Ψ p q) := by
  rw [hS.J1_eq_sSup hΨ p q]
  exact (isGreatest_quadratic _ _ _ (J1Gram_transpose S a _)
    (J1Gram_nonneg S a _ hΨ.nonneg hΨ.integrable_gram) (hΨ.mulVec_J1Slope p q)).csSup_eq

/-- The load is linear in `(p, q)`. -/
theorem J1Mask.J1Load_add_smul (hΨ : J1Mask S a Ψ) (s t : ℝ) (p q p' q' : Vec d) :
    J1Load S a Ψ (s • p + t • p') (s • q + t • q') =
      s • J1Load S a Ψ p q + t • J1Load S a Ψ p' q' := by
  funext i
  have hpt : (fun x => Ψ x * (-dot (s • p + t • p') ((a x).mulVec (correctorColumn S a i x)) +
      dot (s • q + t • q') (correctorColumn S a i x))) = fun x =>
      s * (Ψ x * (-dot p ((a x).mulVec (correctorColumn S a i x)) +
        dot q (correctorColumn S a i x))) +
      t * (Ψ x * (-dot p' ((a x).mulVec (correctorColumn S a i x)) +
        dot q' (correctorColumn S a i x))) := by
    funext x
    simp only [dot_eq_dotProduct, add_dotProduct, smul_dotProduct, smul_eq_mul]
    ring
  simp only [J1Load, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hpt, integral_add ((hΨ.integrable_load p q i).const_mul s)
    ((hΨ.integrable_load p' q' i).const_mul t), integral_const_mul, integral_const_mul]

theorem J1Mask.J1Load_add (hΨ : J1Mask S a Ψ) (p q p' q' : Vec d) :
    J1Load S a Ψ (p + p') (q + q') = J1Load S a Ψ p q + J1Load S a Ψ p' q' := by
  simpa using hΨ.J1Load_add_smul 1 1 p q p' q'

theorem J1Mask.J1Load_smul (hΨ : J1Mask S a Ψ) (t : ℝ) (p q : Vec d) :
    J1Load S a Ψ (t • p) (t • q) = t • J1Load S a Ψ p q := by
  simpa using hΨ.J1Load_add_smul t 0 p q 0 0

theorem J1Mask.J1Slope_add_smul (hΨ : J1Mask S a Ψ) (s t : ℝ) (p q p' q' : Vec d) :
    J1Slope S a Ψ (s • p + t • p') (s • q + t • q') =
      s • J1Slope S a Ψ p q + t • J1Slope S a Ψ p' q' := by
  rw [J1Slope, hΨ.J1Load_add_smul, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  rfl

theorem J1Gram_inv_transpose (S : HomogenizationData P) (a : CoefficientField d Λ)
    (Ψ : Vec d → ℝ) : ((J1Gram S a Ψ)⁻¹).transpose = (J1Gram S a Ψ)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, J1Gram_transpose]

end Mask

section Maximizer

variable {P : Measure (CoefficientField d Λ)} {S : HomogenizationData P} {a : CoefficientField d Λ}
  {Ψ : Vec d → ℝ}

/-- **The maximizers** of `J₁(Ψ, p, q)` are the elements of `A₁` of slope `M⁻¹ b`. -/
theorem J1Structure.isJ1Maximizer_iff (hS : J1Structure S a) (hΨ : J1Mask S a Ψ) {p q : Vec d}
    {v : HarmonicA1 a} {c : Vec d}
    (hv : ∀ᵐ x ∂(volume : Measure (Vec d)), v.grad x = correctedAffineGrad S a c x) :
    IsJ1Maximizer a Ψ p q v ↔ c = J1Slope S a Ψ p q := by
  have hdet : IsUnit (J1Gram S a Ψ).det := (Matrix.isUnit_iff_isUnit_det _).mp hΨ.gram_isUnit
  unfold IsJ1Maximizer
  rw [(hΨ.j1Functional_eq p q hv).2, hS.J1_eq_half_dot_slope hΨ p q, J1Slope]
  constructor
  · intro h
    have hM := mulVec_eq_of_slopeQuadratic_eq _ (J1Gram_transpose S a Ψ)
      (J1Gram_nonneg S a _ hΨ.nonneg hΨ.integrable_gram) hΨ.gram_isUnit h
    rw [← hM, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  · rintro rfl
    rw [slopeQuadratic_eq _ (J1Gram_transpose S a Ψ) hΨ.gram_isUnit, sub_self,
      Matrix.mulVec_zero]
    simp [dot]

/-- **Existence of the maximizer** `v(·, Ψ, p, q)`. -/
theorem J1Structure.exists_isJ1Maximizer (hS : J1Structure S a) (hΨ : J1Mask S a Ψ)
    (p q : Vec d) :
    ∃ v : HarmonicA1 a, IsJ1Maximizer a Ψ p q v ∧
      v.grad = correctedAffineGrad S a (J1Slope S a Ψ p q) := by
  obtain ⟨v, hv⟩ := hS.exists_affine (J1Slope S a Ψ p q)
  exact ⟨v, (hS.isJ1Maximizer_iff hΨ (Eventually.of_forall fun x => by rw [hv])).mpr rfl, hv⟩

/-- The gradient of a maximizer is the corrected affine gradient of slope `M⁻¹ b`. -/
theorem IsJ1Maximizer.grad_ae_eq {p q : Vec d} {v : HarmonicA1 a}
    (hv : IsJ1Maximizer a Ψ p q v) (hS : J1Structure S a) (hΨ : J1Mask S a Ψ) :
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      v.grad x = correctedAffineGrad S a (J1Slope S a Ψ p q) x := by
  obtain ⟨c, hc⟩ := hS.liouville v
  have h := (hS.isJ1Maximizer_iff hΨ hc).mp hv
  subst h
  exact hc

/-- **Uniqueness of the maximizer**: two maximizers have the same gradient. -/
theorem IsJ1Maximizer.grad_ae_eq_of_isJ1Maximizer {p q : Vec d} {v v' : HarmonicA1 a}
    (hv : IsJ1Maximizer a Ψ p q v) (hv' : IsJ1Maximizer a Ψ p q v') (hS : J1Structure S a)
    (hΨ : J1Mask S a Ψ) : v.grad =ᵐ[volume] v'.grad := by
  filter_upwards [hv.grad_ae_eq hS hΨ, hv'.grad_ae_eq hS hΨ] with x h1 h2
  rw [h1, h2]

/-- **First variation (4.13)**: `v ∈ A₁` maximizes `J₁(Ψ, p, q)` if and only if
`∫ Ψ ∇w·a∇v = ∫ Ψ (-p·a∇w + q·∇w)` for every `w ∈ A₁`; both integrands are integrable. -/
theorem J1Structure.isJ1Maximizer_iff_firstVariation (hS : J1Structure S a) (hΨ : J1Mask S a Ψ)
    (p q : Vec d) (v : HarmonicA1 a) :
    (∀ w : HarmonicA1 a, Integrable (fun x => Ψ x * dot (w.grad x) ((a x).mulVec (v.grad x))) ∧
      Integrable (fun x => Ψ x * (-dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x)))) ∧
    (IsJ1Maximizer a Ψ p q v ↔ ∀ w : HarmonicA1 a,
      ∫ x, Ψ x * dot (w.grad x) ((a x).mulVec (v.grad x)) =
        ∫ x, Ψ x * (-dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x))) := by
  have hdet : IsUnit (J1Gram S a Ψ).det := (Matrix.isUnit_iff_isUnit_det _).mp hΨ.gram_isUnit
  obtain ⟨cv, hcv⟩ := hS.liouville v
  refine ⟨fun w => ?_, ?_⟩
  · obtain ⟨cw, hcw⟩ := hS.liouville w
    exact ⟨(hΨ.integral_grad_dot_eq hcw hcv).1, (hΨ.integral_load_grad_eq p q hcw).1⟩
  have key : ∀ (w : HarmonicA1 a) (cw : Vec d),
      (∀ᵐ x ∂(volume : Measure (Vec d)), w.grad x = correctedAffineGrad S a cw x) →
      ((∫ x, Ψ x * dot (w.grad x) ((a x).mulVec (v.grad x)) =
        ∫ x, Ψ x * (-dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x))) ↔
        dot cw ((J1Gram S a Ψ).mulVec cv) = dot (J1Load S a Ψ p q) cw) := by
    intro w cw hcw
    rw [(hΨ.integral_grad_dot_eq hcw hcv).2, (hΨ.integral_load_grad_eq p q hcw).2]
  rw [hS.isJ1Maximizer_iff hΨ hcv]
  constructor
  · rintro rfl w
    obtain ⟨cw, hcw⟩ := hS.liouville w
    rw [key w cw hcw, hΨ.mulVec_J1Slope, dot_eq_dotProduct, dot_eq_dotProduct, dotProduct_comm]
  · intro h
    have hM : (J1Gram S a Ψ).mulVec cv = J1Load S a Ψ p q := by
      funext i
      obtain ⟨w, hw⟩ := hS.exists_affine (unitVector i)
      have h1 := (key w _ (Eventually.of_forall fun x => by rw [hw])).mp (h w)
      have e1 : ∀ y : Vec d, dot (unitVector i) y = y i := fun y => by
        unfold dot unitVector
        simp [Pi.single_apply]
      have e2 : ∀ y : Vec d, dot y (unitVector i) = y i := fun y => by
        unfold dot unitVector
        simp [Pi.single_apply]
      rwa [e1, e2] at h1
    rw [J1Slope, ← hM, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

/-- **(4.14)**: `J₁(Ψ, p, q) = ½ ∫ Ψ ∇v·a∇v` at a maximizer. -/
theorem IsJ1Maximizer.J1_eq_integral {p q : Vec d} {v : HarmonicA1 a}
    (hv : IsJ1Maximizer a Ψ p q v) (hS : J1Structure S a) (hΨ : J1Mask S a Ψ) :
    Integrable (fun x => Ψ x * dot (v.grad x) ((a x).mulVec (v.grad x))) ∧
    J1 a Ψ p q = (1 / 2 : ℝ) * ∫ x, Ψ x * dot (v.grad x) ((a x).mulVec (v.grad x)) := by
  have hg := hv.grad_ae_eq hS hΨ
  obtain ⟨hi, he⟩ := hΨ.integral_grad_dot_eq hg hg
  refine ⟨hi, ?_⟩
  rw [he, hΨ.mulVec_J1Slope, hS.J1_eq_half_dot_slope hΨ, dot_eq_dotProduct, dot_eq_dotProduct,
    dotProduct_comm]

/-- **(4.15)**: `½ ‖∇v‖²_{L²(Ψ)} ≤ J₁(Ψ, p, q) ≤ Λ |p|² + |q|²` at a maximizer. -/
theorem IsJ1Maximizer.bounds {p q : Vec d} {v : HarmonicA1 a} (hv : IsJ1Maximizer a Ψ p q v)
    (hS : J1Structure S a) (hΨ : J1Mask S a Ψ) :
    Integrable (fun x => Ψ x * euclideanSq (v.grad x)) ∧
    (1 / 2 : ℝ) * ∫ x, Ψ x * euclideanSq (v.grad x) ≤ J1 a Ψ p q ∧
    J1 a Ψ p q ≤ Λ * euclideanSq p + euclideanSq q := by
  obtain ⟨hi, hJ⟩ := hv.J1_eq_integral hS hΨ
  have hg := hv.grad_ae_eq hS hΨ
  have hc : Continuous fun u : Vec d => euclideanSq u := by unfold euclideanSq dot; fun_prop
  have hm : AEStronglyMeasurable (fun x => Ψ x * euclideanSq (v.grad x)) volume := by
    refine (hΨ.integrable.aestronglyMeasurable.mul
      (hc.measurable.comp
        (measurable_correctedAffineGrad S a (J1Slope S a Ψ p q))).aestronglyMeasurable).congr ?_
    filter_upwards [hg] with x hx
    simp only [Pi.mul_apply, Function.comp_apply, hx]
  have hle : ∀ x, Ψ x * euclideanSq (v.grad x) ≤
      Ψ x * dot (v.grad x) ((a x).mulVec (v.grad x)) :=
    fun x => mul_le_mul_of_nonneg_left (a.elliptic x (v.grad x)).1 (hΨ.nonneg x)
  have hnn : ∀ x, 0 ≤ Ψ x * euclideanSq (v.grad x) :=
    fun x => mul_nonneg (hΨ.nonneg x) (BaseExponent.euclideanSq_nonneg _)
  have hi2 : Integrable (fun x => Ψ x * euclideanSq (v.grad x)) :=
    hi.mono' hm (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)]
      exact hle x)
  refine ⟨hi2, ?_, J1_le a hΨ.nonneg hΨ.integrable hΨ.integral_eq_one.le p q⟩
  rw [hJ]
  have := integral_mono hi2 hi hle
  linarith

/-- **Linearity of `∇v` in `(p, q)`**:
`∇v(·, Ψ, p + p', q + q') = ∇v(·, Ψ, p, q) + ∇v(·, Ψ, p', q')`. -/
theorem IsJ1Maximizer.grad_add {p q p' q' : Vec d} {v₁ v₂ v₃ : HarmonicA1 a}
    (hv₁ : IsJ1Maximizer a Ψ p q v₁) (hv₂ : IsJ1Maximizer a Ψ p' q' v₂)
    (hv₃ : IsJ1Maximizer a Ψ (p + p') (q + q') v₃) (hS : J1Structure S a) (hΨ : J1Mask S a Ψ) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), v₃.grad x = v₁.grad x + v₂.grad x := by
  filter_upwards [hv₁.grad_ae_eq hS hΨ, hv₂.grad_ae_eq hS hΨ, hv₃.grad_ae_eq hS hΨ]
    with x h1 h2 h3
  rw [h1, h2, h3, ← correctedAffineGrad_add]
  congr 1
  simpa using hΨ.J1Slope_add_smul 1 1 p q p' q'

/-- **Linearity of `∇v` in `(p, q)`**: `∇v(·, Ψ, t p, t q) = t ∇v(·, Ψ, p, q)`. -/
theorem IsJ1Maximizer.grad_smul {p q : Vec d} {t : ℝ} {v v' : HarmonicA1 a}
    (hv : IsJ1Maximizer a Ψ p q v) (hv' : IsJ1Maximizer a Ψ (t • p) (t • q) v')
    (hS : J1Structure S a) (hΨ : J1Mask S a Ψ) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), v'.grad x = t • v.grad x := by
  filter_upwards [hv.grad_ae_eq hS hΨ, hv'.grad_ae_eq hS hΨ] with x h1 h2
  rw [h1, h2, ← correctedAffineGrad_smul]
  congr 1
  simpa using hΨ.J1Slope_add_smul t 0 p q 0 0

/-- **`J₁` is quadratic**: `J₁(Ψ, t p, t q) = t² J₁(Ψ, p, q)`. -/
theorem J1Structure.J1_smul_smul (hS : J1Structure S a) (hΨ : J1Mask S a Ψ) (t : ℝ)
    (p q : Vec d) : J1 a Ψ (t • p) (t • q) = t ^ 2 * J1 a Ψ p q := by
  have hs : J1Slope S a Ψ (t • p) (t • q) = t • J1Slope S a Ψ p q := by
    simpa using hΨ.J1Slope_add_smul t 0 p q 0 0
  rw [hS.J1_eq_half_dot_slope hΨ, hS.J1_eq_half_dot_slope hΨ, hs, hΨ.J1Load_smul]
  simp only [dot_eq_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- **Polarization (4.16)**:
`J₁(Ψ, p + p', q + q') = J₁(Ψ, p, q) + J₁(Ψ, p', q') + ∫ Ψ (-a p' + q')·∇v(·, Ψ, p, q)`. -/
theorem IsJ1Maximizer.J1_add_add {p q : Vec d} {v : HarmonicA1 a} (hv : IsJ1Maximizer a Ψ p q v)
    (hS : J1Structure S a) (hΨ : J1Mask S a Ψ) (p' q' : Vec d) :
    Integrable (fun x => Ψ x * dot (-(a x).mulVec p' + q') (v.grad x)) ∧
    J1 a Ψ (p + p') (q + q') = J1 a Ψ p q + J1 a Ψ p' q' +
      ∫ x, Ψ x * dot (-(a x).mulVec p' + q') (v.grad x) := by
  have hg := hv.grad_ae_eq hS hΨ
  obtain ⟨hi, he⟩ := hΨ.integral_load_grad_eq p' q' hg
  have hpt : (fun x => Ψ x * dot (-(a x).mulVec p' + q') (v.grad x)) =
      fun x => Ψ x * (-dot p' ((a x).mulVec (v.grad x)) + dot q' (v.grad x)) := by
    funext x
    have hs := dot_mulVec_comm_of_symm (a.symmetric x) p' (v.grad x)
    simp only [dot_eq_dotProduct] at hs ⊢
    rw [add_dotProduct, neg_dotProduct, dotProduct_comm ((a x).mulVec p'), ← hs]
  rw [hpt]
  refine ⟨hi, ?_⟩
  have hadd : J1Slope S a Ψ (p + p') (q + q') = J1Slope S a Ψ p q + J1Slope S a Ψ p' q' := by
    simpa using hΨ.J1Slope_add_smul 1 1 p q p' q'
  have hsym : dot (J1Load S a Ψ p q) (J1Slope S a Ψ p' q') =
      dot (J1Load S a Ψ p' q') (J1Slope S a Ψ p q) := by
    unfold J1Slope
    exact dot_mulVec_comm_of_symm (J1Gram_inv_transpose S a Ψ) _ _
  rw [he, hS.J1_eq_half_dot_slope hΨ, hS.J1_eq_half_dot_slope hΨ p q,
    hS.J1_eq_half_dot_slope hΨ p' q', hΨ.J1Load_add, hadd]
  simp only [dot_eq_dotProduct, add_dotProduct, dotProduct_add] at hsym ⊢
  linarith

/-- **Second variation (4.19)**: for every `w ∈ A₁`,
`½ ∫ Ψ (∇w - ∇v)·a(∇w - ∇v) = J₁(Ψ, p, q) - ∫ Ψ (-½ ∇w·a∇w - p·a∇w + q·∇w)`. -/
theorem IsJ1Maximizer.secondVariation {p q : Vec d} {v : HarmonicA1 a}
    (hv : IsJ1Maximizer a Ψ p q v) (hS : J1Structure S a) (hΨ : J1Mask S a Ψ)
    (w : HarmonicA1 a) :
    Integrable (fun x => Ψ x * dot (w.grad x - v.grad x) ((a x).mulVec (w.grad x - v.grad x))) ∧
    Integrable (fun x => Ψ x * (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
      dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x))) ∧
    (1 / 2 : ℝ) * ∫ x, Ψ x * dot (w.grad x - v.grad x) ((a x).mulVec (w.grad x - v.grad x)) =
      J1 a Ψ p q - j1Functional a Ψ p q w.grad := by
  have hg := hv.grad_ae_eq hS hΨ
  obtain ⟨cw, hcw⟩ := hS.liouville w
  have hd : ∀ᵐ x ∂(volume : Measure (Vec d)), w.grad x - v.grad x =
      correctedAffineGrad S a (cw - J1Slope S a Ψ p q) x := by
    filter_upwards [hg, hcw] with x h1 h2
    rw [h1, h2, correctedAffineGrad_sub]
  obtain ⟨i1, e1⟩ := hΨ.integral_grad_dot_eq (g := fun x => w.grad x - v.grad x)
    (g' := fun x => w.grad x - v.grad x) hd hd
  obtain ⟨i2, e2⟩ := hΨ.j1Functional_eq p q hcw
  refine ⟨i1, i2, ?_⟩
  rw [e1, e2, hS.J1_eq_half_dot_slope hΨ,
    slopeQuadratic_eq _ (J1Gram_transpose S a Ψ) hΨ.gram_isUnit]
  unfold J1Slope
  ring

/-- `|h|² ≤ d ‖h‖²` for the sup norm. -/
private theorem euclideanSq_le_card_mul_sq_norm (u : Vec d) : euclideanSq u ≤ d * ‖u‖ ^ 2 := by
  unfold euclideanSq dot
  calc ∑ i, u i * u i ≤ ∑ _i : Fin d, ‖u‖ ^ 2 := Finset.sum_le_sum fun i _ => by
        have h := norm_le_pi_norm u i
        rw [Real.norm_eq_abs] at h
        nlinarith [abs_nonneg (u i), abs_mul_abs_self (u i)]
    _ = d * ‖u‖ ^ 2 := by simp

/-- **(4.20)**: `D_p J₁(Ψ, p, q) = -∫ Ψ a∇v(·, Ψ, p, q)`. -/
theorem IsJ1Maximizer.hasFDerivAt_left {p q : Vec d} {v : HarmonicA1 a}
    (hv : IsJ1Maximizer a Ψ p q v) (hS : J1Structure S a) (hΨ : J1Mask S a Ψ) (hΛ : 0 ≤ Λ) :
    (∀ i, Integrable (fun x => Ψ x * ((a x).mulVec (v.grad x)) i)) ∧
    HasFDerivAt (fun p' => J1 a Ψ p' q)
      (dotContinuousLinearMap fun i => -∫ x, Ψ x * ((a x).mulVec (v.grad x)) i) p := by
  have hg := hv.grad_ae_eq hS hΨ
  have hint : ∀ i, Integrable (fun x => Ψ x * ((a x).mulVec (v.grad x)) i) := fun i => by
    have e : ∀ y z : Vec d, -dot (-unitVector i) y + dot 0 z = y i := fun y z => by
      have h1 : dot (unitVector i) y = y i := by
        unfold dot unitVector
        simp [Pi.single_apply]
      rw [dot_eq_dotProduct, dot_eq_dotProduct, neg_dotProduct, zero_dotProduct, neg_neg,
        add_zero, ← dot_eq_dotProduct, h1]
    refine (hΨ.integral_load_grad_eq (-unitVector i) 0 hg).1.congr
      (Eventually.of_forall fun x => ?_)
    simp only [e]
  refine ⟨hint, ?_⟩
  set g : Vec d := fun i => -∫ x, Ψ x * ((a x).mulVec (v.grad x)) i with hgdef
  have hpol : ∀ h : Vec d, J1 a Ψ (p + h) q = J1 a Ψ p q + J1 a Ψ h 0 + dot g h := by
    intro h
    obtain ⟨-, e⟩ := hv.J1_add_add hS hΨ h 0
    rw [add_zero] at e
    rw [e]
    congr 1
    have hpt : ∀ x, Ψ x * dot (-(a x).mulVec h + 0) (v.grad x) =
        ∑ i, h i * -(Ψ x * ((a x).mulVec (v.grad x)) i) := by
      intro x
      have hs := dot_mulVec_comm_of_symm (a.symmetric x) h (v.grad x)
      rw [add_zero]
      simp only [dot_eq_dotProduct] at hs ⊢
      rw [neg_dotProduct, dotProduct_comm ((a x).mulVec h), ← hs, dotProduct,
        ← Finset.sum_neg_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_finsetSum]
    · simp only [integral_const_mul, integral_neg, hgdef, dot]
      exact Finset.sum_congr rfl fun i _ => by ring
    · exact fun i _ => ((hint i).neg).const_mul (h i)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hrem : (fun h => J1 a Ψ (p + h) q - J1 a Ψ p q - dotContinuousLinearMap g h) =
      fun h => J1 a Ψ h 0 := by
    funext h
    rw [hpol h, dotContinuousLinearMap_apply]
    ring
  rw [hrem]
  refine IsBigO.trans_isLittleO (IsBigO.of_bound (Λ * d) (Eventually.of_forall fun h => ?_))
    (isLittleO_norm_pow_id one_lt_two)
  rw [Real.norm_eq_abs, abs_of_nonneg
    (J1_nonneg a hΨ.nonneg hΨ.integrable hΨ.integral_eq_one.le h 0), norm_pow, norm_norm]
  have h1 := J1_le a hΨ.nonneg hΨ.integrable hΨ.integral_eq_one.le h 0
  have h0 : euclideanSq (0 : Vec d) = 0 := by simp [euclideanSq, dot]
  rw [h0, add_zero] at h1
  calc J1 a Ψ h 0 ≤ Λ * euclideanSq h := h1
    _ ≤ Λ * (d * ‖h‖ ^ 2) := mul_le_mul_of_nonneg_left (euclideanSq_le_card_mul_sq_norm h) hΛ
    _ = Λ * d * ‖h‖ ^ 2 := by ring

/-- **(4.21)**: `D_q J₁(Ψ, p, q) = ∫ Ψ ∇v(·, Ψ, p, q)`. -/
theorem IsJ1Maximizer.hasFDerivAt_right {p q : Vec d} {v : HarmonicA1 a}
    (hv : IsJ1Maximizer a Ψ p q v) (hS : J1Structure S a) (hΨ : J1Mask S a Ψ) :
    (∀ i, Integrable (fun x => Ψ x * v.grad x i)) ∧
    HasFDerivAt (fun q' => J1 a Ψ p q')
      (dotContinuousLinearMap fun i => ∫ x, Ψ x * v.grad x i) q := by
  have hg := hv.grad_ae_eq hS hΨ
  have hint : ∀ i, Integrable (fun x => Ψ x * v.grad x i) := fun i => by
    have e : ∀ y z : Vec d, -dot 0 y + dot (unitVector i) z = z i := fun y z => by
      have h1 : dot (unitVector i) z = z i := by
        unfold dot unitVector
        simp [Pi.single_apply]
      rw [h1, dot_eq_dotProduct, zero_dotProduct, neg_zero, zero_add]
    refine (hΨ.integral_load_grad_eq 0 (unitVector i) hg).1.congr
      (Eventually.of_forall fun x => ?_)
    simp only [e]
  refine ⟨hint, ?_⟩
  set g : Vec d := fun i => ∫ x, Ψ x * v.grad x i with hgdef
  have hpol : ∀ h : Vec d, J1 a Ψ p (q + h) = J1 a Ψ p q + J1 a Ψ 0 h + dot g h := by
    intro h
    obtain ⟨-, e⟩ := hv.J1_add_add hS hΨ 0 h
    rw [add_zero] at e
    rw [e]
    congr 1
    have hpt : ∀ x, Ψ x * dot (-(a x).mulVec 0 + h) (v.grad x) =
        ∑ i, h i * (Ψ x * v.grad x i) := by
      intro x
      rw [Matrix.mulVec_zero, neg_zero, zero_add, dot, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_finsetSum]
    · simp only [integral_const_mul, hgdef, dot]
      exact Finset.sum_congr rfl fun i _ => by ring
    · exact fun i _ => (hint i).const_mul (h i)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hrem : (fun h => J1 a Ψ p (q + h) - J1 a Ψ p q - dotContinuousLinearMap g h) =
      fun h => J1 a Ψ 0 h := by
    funext h
    rw [hpol h, dotContinuousLinearMap_apply]
    ring
  rw [hrem]
  refine IsBigO.trans_isLittleO (IsBigO.of_bound (d : ℝ) (Eventually.of_forall fun h => ?_))
    (isLittleO_norm_pow_id one_lt_two)
  rw [Real.norm_eq_abs, abs_of_nonneg
    (J1_nonneg a hΨ.nonneg hΨ.integrable hΨ.integral_eq_one.le 0 h), norm_pow, norm_norm]
  have h1 := J1_le a hΨ.nonneg hΨ.integrable hΨ.integral_eq_one.le 0 h
  have h0 : euclideanSq (0 : Vec d) = 0 := by simp [euclideanSq, dot]
  rw [h0, mul_zero, zero_add] at h1
  exact h1.trans (euclideanSq_le_card_mul_sq_norm h)

/-- The midpoint identity of the quadratic `J₁`:
`½ J₁(Ψ, p₁, q₁) + ½ J₁(Ψ, p₂, q₂) - J₁(Ψ, ½(p₁ + p₂), ½(q₁ + q₂)) = ¼ J₁(Ψ, p₁ - p₂, q₁ - q₂)`. -/
theorem J1Structure.J1_midpoint (hS : J1Structure S a) (hΨ : J1Mask S a Ψ)
    (p₁ q₁ p₂ q₂ : Vec d) :
    (1 / 2 : ℝ) * J1 a Ψ p₁ q₁ + (1 / 2 : ℝ) * J1 a Ψ p₂ q₂ -
      J1 a Ψ ((1 / 2 : ℝ) • (p₁ + p₂)) ((1 / 2 : ℝ) • (q₁ + q₂)) =
      (1 / 4 : ℝ) * J1 a Ψ (p₁ - p₂) (q₁ - q₂) := by
  have hm : ∀ u w : Vec d, (1 / 2 : ℝ) • (u + w) = (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • w :=
    fun u w => smul_add _ _ _
  have hs : ∀ u w : Vec d, u - w = (1 : ℝ) • u + (-1 : ℝ) • w := fun u w => by
    rw [one_smul, neg_one_smul, sub_eq_add_neg]
  have hsym : dot (J1Load S a Ψ p₁ q₁) (J1Slope S a Ψ p₂ q₂) =
      dot (J1Load S a Ψ p₂ q₂) (J1Slope S a Ψ p₁ q₁) := by
    unfold J1Slope
    exact dot_mulVec_comm_of_symm (J1Gram_inv_transpose S a Ψ) _ _
  rw [hS.J1_eq_half_dot_slope hΨ p₁ q₁, hS.J1_eq_half_dot_slope hΨ p₂ q₂,
    hS.J1_eq_half_dot_slope hΨ, hS.J1_eq_half_dot_slope hΨ, hm p₁ p₂, hm q₁ q₂, hs p₁ p₂,
    hs q₁ q₂, hΨ.J1Load_add_smul, hΨ.J1Load_add_smul, hΨ.J1Slope_add_smul,
    hΨ.J1Slope_add_smul]
  simp only [dot_eq_dotProduct, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul] at hsym ⊢
  linarith

/-- `|q|² ≤ Λ q·A⁻¹q` for a symmetric matrix with `1 ≤ A ≤ Λ`. -/
theorem euclideanSq_le_mul_dot_inv_mulVec {A : Mat d} (hA : HomogenizedMatrixBounds A Λ)
    (hsym : A.transpose = A) (hΛ : 0 ≤ Λ) (q : Vec d) :
    euclideanSq q ≤ Λ * dot q (A⁻¹.mulVec q) := by
  have hcoer : ∀ ξ, euclideanSq ξ ≤ dot ξ (A.mulVec ξ) := fun ξ => (hA ξ).1
  have hy : A.mulVec (A⁻¹.mulVec q) = q := mulVec_inv_mulVec (isUnit_det_of_coercive hcoer) q
  have hpsd : ∀ u, 0 ≤ dot u (A.mulVec u) := fun u =>
    (BaseExponent.euclideanSq_nonneg u).trans (hcoer u)
  have hcs := sq_dot_mulVec_le hsym hpsd (A⁻¹.mulVec q) q
  rw [hy] at hcs
  have e1 : dot (A⁻¹.mulVec q) q = dot q (A⁻¹.mulVec q) := by
    rw [dot_eq_dotProduct, dot_eq_dotProduct, dotProduct_comm]
  rw [e1] at hcs
  have hX := (dot_inv_mulVec_nonneg_le hcoer q).1
  have hE : 0 ≤ euclideanSq q := BaseExponent.euclideanSq_nonneg q
  have hup := (hA q).2
  change euclideanSq q ^ 2 ≤ _ at hcs
  rcases hE.eq_or_lt with h0 | hpos
  · rw [← h0]
    exact mul_nonneg hΛ hX
  · have h1 : euclideanSq q * euclideanSq q ≤ euclideanSq q * (Λ * dot q (A⁻¹.mulVec q)) := by
      nlinarith [mul_le_mul_of_nonneg_right hup hX]
    exact le_of_mul_le_mul_left h1 hpos

/-- **Uniform convexity in `p` (4.17)** for `J₁` nondegenerate at `Ψ`:
`(1/16) |p₁ - p₂|² ≤ ½ J₁(Ψ, p₁, q) + ½ J₁(Ψ, p₂, q) - J₁(Ψ, ½ p₁ + ½ p₂, q)`. -/
theorem J1Structure.uniformConvexity_left (hS : J1Structure S a) (hΨ : J1Mask S a Ψ)
    (hA : HomogenizedMatrixBounds S.homogenized Λ) (hnd : J1Nondegenerate S a Ψ)
    (p₁ p₂ q : Vec d) :
    (1 / 16 : ℝ) * euclideanSq (p₁ - p₂) ≤
      (1 / 2 : ℝ) * J1 a Ψ p₁ q + (1 / 2 : ℝ) * J1 a Ψ p₂ q -
        J1 a Ψ ((1 / 2 : ℝ) • (p₁ + p₂)) q := by
  have h := hS.J1_midpoint hΨ p₁ q p₂ q
  have hq : (1 / 2 : ℝ) • (q + q) = q := by
    rw [← two_smul ℝ q, smul_smul]
    norm_num
  rw [hq, sub_self] at h
  rw [h]
  have h1 := (hnd (p₁ - p₂) 0).1
  have h2 := (hA (p₁ - p₂)).1
  linarith

/-- **Uniform convexity in `q` (4.18)** for `J₁` nondegenerate at `Ψ`:
`(1/(16Λ)) |q₁ - q₂|² ≤ ½ J₁(Ψ, p, q₁) + ½ J₁(Ψ, p, q₂) - J₁(Ψ, p, ½ q₁ + ½ q₂)`. -/
theorem J1Structure.uniformConvexity_right (hS : J1Structure S a) (hΨ : J1Mask S a Ψ)
    (hΛ : 0 < Λ) (hA : HomogenizedMatrixBounds S.homogenized Λ) (hnd : J1Nondegenerate S a Ψ)
    (q₁ q₂ p : Vec d) :
    1 / (16 * Λ) * euclideanSq (q₁ - q₂) ≤
      (1 / 2 : ℝ) * J1 a Ψ p q₁ + (1 / 2 : ℝ) * J1 a Ψ p q₂ -
        J1 a Ψ p ((1 / 2 : ℝ) • (q₁ + q₂)) := by
  have h := hS.J1_midpoint hΨ p q₁ p q₂
  have hp : (1 / 2 : ℝ) • (p + p) = p := by
    rw [← two_smul ℝ p, smul_smul]
    norm_num
  rw [hp, sub_self] at h
  rw [h]
  have h1 := (hnd 0 (q₁ - q₂)).2
  have h2 := euclideanSq_le_mul_dot_inv_mulVec hA S.symmetric hΛ.le (q₁ - q₂)
  have h3 : 1 / (16 * Λ) * euclideanSq (q₁ - q₂) ≤
      1 / (16 * Λ) * (Λ * dot (q₁ - q₂) (S.homogenized⁻¹.mulVec (q₁ - q₂))) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : 1 / (16 * Λ) * (Λ * dot (q₁ - q₂) (S.homogenized⁻¹.mulVec (q₁ - q₂))) =
      1 / 16 * dot (q₁ - q₂) (S.homogenized⁻¹.mulVec (q₁ - q₂)) := by
    field_simp
  linarith

end Maximizer

section Lemma44

variable {P : Measure (CoefficientField d Λ)}

/-- **Lemma 4.4 (basic properties of `J₁`).** Almost surely, for every mask `Ψ` of (4.8):
a maximizer `v(·, Ψ, p, q) ∈ A₁` exists and is characterized by the first variation (4.13), its
gradient is unique, (4.14), (4.15), the polarization (4.16), the second variation (4.19) and the
derivatives (4.20)–(4.21) hold at it, `(p, q) ↦ ∇v(·, Ψ, p, q)` is linear and `J₁` is quadratic,
and if `J₁` is nondegenerate at `Ψ` then the uniform convexity (4.17)–(4.18) holds with the
constants `16` and `16 Λ`. -/
theorem lemma_4_4 (hd : 2 ≤ d) (hΛ : 1 < Λ) (hP : LawHypotheses P) (S : HomogenizationData P) :
    ∀ᵐ a ∂P, ∀ Ψ : Vec d → ℝ, J1Mask S a Ψ →
      (∀ p q : Vec d, ∃ v : HarmonicA1 a, IsJ1Maximizer a Ψ p q v) ∧
      (∀ (p q : Vec d) (v : HarmonicA1 a),
        (∀ w : HarmonicA1 a,
          Integrable (fun x => Ψ x * dot (w.grad x) ((a x).mulVec (v.grad x))) ∧
          Integrable (fun x => Ψ x * (-dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x)))) ∧
        (IsJ1Maximizer a Ψ p q v ↔ ∀ w : HarmonicA1 a,
          ∫ x, Ψ x * dot (w.grad x) ((a x).mulVec (v.grad x)) =
            ∫ x, Ψ x * (-dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x)))) ∧
      (∀ (p q : Vec d) (v v' : HarmonicA1 a), IsJ1Maximizer a Ψ p q v →
        IsJ1Maximizer a Ψ p q v' → v.grad =ᵐ[volume] v'.grad) ∧
      (∀ (p q : Vec d) (v : HarmonicA1 a), IsJ1Maximizer a Ψ p q v →
        (Integrable (fun x => Ψ x * dot (v.grad x) ((a x).mulVec (v.grad x))) ∧
          J1 a Ψ p q = (1 / 2 : ℝ) * ∫ x, Ψ x * dot (v.grad x) ((a x).mulVec (v.grad x))) ∧
        (Integrable (fun x => Ψ x * euclideanSq (v.grad x)) ∧
          (1 / 2 : ℝ) * ∫ x, Ψ x * euclideanSq (v.grad x) ≤ J1 a Ψ p q ∧
          J1 a Ψ p q ≤ Λ * euclideanSq p + euclideanSq q) ∧
        (∀ p' q' : Vec d, Integrable (fun x => Ψ x * dot (-(a x).mulVec p' + q') (v.grad x)) ∧
          J1 a Ψ (p + p') (q + q') = J1 a Ψ p q + J1 a Ψ p' q' +
            ∫ x, Ψ x * dot (-(a x).mulVec p' + q') (v.grad x)) ∧
        (∀ w : HarmonicA1 a,
          Integrable (fun x => Ψ x * dot (w.grad x - v.grad x)
            ((a x).mulVec (w.grad x - v.grad x))) ∧
          Integrable (fun x => Ψ x * (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
            dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x))) ∧
          (1 / 2 : ℝ) * ∫ x, Ψ x * dot (w.grad x - v.grad x)
            ((a x).mulVec (w.grad x - v.grad x)) = J1 a Ψ p q - j1Functional a Ψ p q w.grad) ∧
        ((∀ i, Integrable (fun x => Ψ x * ((a x).mulVec (v.grad x)) i)) ∧
          HasFDerivAt (fun p' => J1 a Ψ p' q)
            (dotContinuousLinearMap fun i => -∫ x, Ψ x * ((a x).mulVec (v.grad x)) i) p) ∧
        ((∀ i, Integrable (fun x => Ψ x * v.grad x i)) ∧
          HasFDerivAt (fun q' => J1 a Ψ p q')
            (dotContinuousLinearMap fun i => ∫ x, Ψ x * v.grad x i) q)) ∧
      (∀ (p q p' q' : Vec d) (v₁ v₂ v₃ : HarmonicA1 a), IsJ1Maximizer a Ψ p q v₁ →
        IsJ1Maximizer a Ψ p' q' v₂ → IsJ1Maximizer a Ψ (p + p') (q + q') v₃ →
        ∀ᵐ x ∂(volume : Measure (Vec d)), v₃.grad x = v₁.grad x + v₂.grad x) ∧
      (∀ (t : ℝ) (p q : Vec d) (v v' : HarmonicA1 a), IsJ1Maximizer a Ψ p q v →
        IsJ1Maximizer a Ψ (t • p) (t • q) v' →
        ∀ᵐ x ∂(volume : Measure (Vec d)), v'.grad x = t • v.grad x) ∧
      (∀ (t : ℝ) (p q : Vec d), J1 a Ψ (t • p) (t • q) = t ^ 2 * J1 a Ψ p q) ∧
      (J1Nondegenerate S a Ψ →
        (∀ p₁ p₂ q : Vec d, (1 / 16 : ℝ) * euclideanSq (p₁ - p₂) ≤
          (1 / 2 : ℝ) * J1 a Ψ p₁ q + (1 / 2 : ℝ) * J1 a Ψ p₂ q -
            J1 a Ψ ((1 / 2 : ℝ) • (p₁ + p₂)) q) ∧
        ∀ q₁ q₂ p : Vec d, 1 / (16 * Λ) * euclideanSq (q₁ - q₂) ≤
          (1 / 2 : ℝ) * J1 a Ψ p q₁ + (1 / 2 : ℝ) * J1 a Ψ p q₂ -
            J1 a Ψ p ((1 / 2 : ℝ) • (q₁ + q₂))) := by
  have hP1 : IsProbabilityMeasure P := hP.1
  have hA := S.homogenizedMatrixBounds (by linarith : (0 : ℝ) ≤ Λ)
  filter_upwards [ae_j1Structure hd hΛ hP S] with a hS
  intro Ψ hΨ
  refine ⟨fun p q => ?_, fun p q v => hS.isJ1Maximizer_iff_firstVariation hΨ p q v,
    fun p q v v' hv hv' => hv.grad_ae_eq_of_isJ1Maximizer hv' hS hΨ,
    fun p q v hv => ⟨hv.J1_eq_integral hS hΨ, hv.bounds hS hΨ, hv.J1_add_add hS hΨ,
      hv.secondVariation hS hΨ, hv.hasFDerivAt_left hS hΨ (by linarith),
      hv.hasFDerivAt_right hS hΨ⟩,
    fun p q p' q' v₁ v₂ v₃ h1 h2 h3 => h1.grad_add h2 h3 hS hΨ,
    fun t p q v v' hv hv' => hv.grad_smul hv' hS hΨ,
    fun t p q => hS.J1_smul_smul hΨ t p q,
    fun hnd => ⟨hS.uniformConvexity_left hΨ hA hnd,
      hS.uniformConvexity_right hΨ (by linarith) hA hnd⟩⟩
  obtain ⟨v, hv, -⟩ := hS.exists_isJ1Maximizer hΨ p q
  exact ⟨v, hv⟩

end Lemma44

end QSH
