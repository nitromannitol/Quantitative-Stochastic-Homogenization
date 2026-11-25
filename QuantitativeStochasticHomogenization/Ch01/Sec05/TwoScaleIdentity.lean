import QuantitativeStochasticHomogenization.Ch01.Sec05.CorrectorScaling
import QuantitativeStochasticHomogenization.Ch01.Sec05.HomogenizedInterior
import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicApproximationData
import QuantitativeStochasticHomogenization.Ch03.Sec04.CutoffTestIdentity

/-!
# The equation of the two-scale expansion

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.5, Step 1 of the proof of Theorem 1.17. Let `u ∈ H¹(U)` solve `-∇·(ā∇u) = 0`, let
`G_j` (in the book `η_r ∂_{x_j} u`) be smooth with compact support in `U` and
`∑_j G_j e_j = η ∇u` almost everywhere, and let `Φ_j = ε φ_{e_j}(·/ε)` be the rescaled correctors,
with gradients `DΦ_j` and divergence-free fluxes `b(e_j + DΦ_j)`, `b = a(·/ε)`. For the two-scale
expansion `w = u + ∑_j G_j Φ_j`, with gradient `∇u + ∑_j (G_j DΦ_j + Φ_j ∇G_j)`, and every test
`ψ`,
`∫_U b∇w · ∇ψ = ∫_U (1 - η)(b - ā)∇u · ∇ψ
  - ∑_j ∫_U ψ (b(e_j + DΦ_j) - ā e_j) · ∇G_j + ∑_j ∫_U b(Φ_j ∇G_j) · ∇ψ`
(`integral_twoScaleGrad_eq`): the three terms `T₂`, `T₁` and `T₃` of the book. The coefficient
field `a(·/ε)` is `rescaledCoefficientField a ε`.
-/

open MeasureTheory Filter Set

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- The rescaled coefficient field `x ↦ a(x/ε)`. -/
def rescaledCoefficientField (a : CoefficientField d Λ) {ε : ℝ} (hε : ε ≠ 0) :
    CoefficientField d Λ where
  field := fun x => a (ε⁻¹ • x)
  locally_integrable := fun i j => by
    have hm : AEStronglyMeasurable (fun x => a.field x i j) volume :=
      (a.locally_integrable i j).aestronglyMeasurable
    have hq := Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d)) (inv_ne_zero hε)
    have hm' : AEStronglyMeasurable (fun x => a.field (ε⁻¹ • x) i j) volume :=
      hm.comp_quasiMeasurePreserving hq
    refine (locallyIntegrable_const Λ).mono hm' (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (abs_coefficient_entry_le a _ i j).trans (le_abs_self Λ)
  symmetric := fun x => a.symmetric _
  elliptic := fun x => a.elliptic _

theorem rescaledCoefficientField_apply (a : CoefficientField d Λ) {ε : ℝ} (hε : ε ≠ 0)
    (x : Vec d) : rescaledCoefficientField a hε x = a (ε⁻¹ • x) := rfl

namespace TwoScale

/-! ## Vector algebra -/

theorem dot_eq_dotProduct (x y : Vec d) : dot x y = dotProduct x y := rfl

theorem sum_smul_unitVector (v : Vec d) : ∑ j, v j • unitVector (d := d) j = v := by
  funext i
  simp [unitVector, Finset.sum_apply, Pi.single_apply]

theorem mulVec_finset_sum (B : Mat d) {ι : Type*} (s : Finset ι) (v : ι → Vec d) :
    B.mulVec (∑ j ∈ s, v j) = ∑ j ∈ s, B.mulVec (v j) := by
  have h := map_sum (Matrix.mulVecLin B) v s
  simp only [Matrix.mulVecLin_apply] at h
  exact h

/-- The vector identity behind Step 1. -/
theorem mulVec_twoScaleGrad_eq (B A : Mat d) (gx : Vec d) (ηx : ℝ) (Gx Φx : Fin d → ℝ)
    (DΦx DGx : Fin d → Vec d) (hΓ : Gx = ηx • gx) :
    B.mulVec (gx + ∑ j, (Gx j • DΦx j + Φx j • DGx j)) =
      (1 - ηx) • (B.mulVec gx - A.mulVec gx) + A.mulVec gx + ∑ j, B.mulVec (Φx j • DGx j) +
        ∑ j, Gx j • (B.mulVec (unitVector j + DΦx j) - A.mulVec (unitVector j)) := by
  have hB : ∑ j, Gx j • B.mulVec (unitVector j) = ηx • B.mulVec gx := by
    simp_rw [← Matrix.mulVec_smul]
    rw [← mulVec_finset_sum, sum_smul_unitVector, hΓ, Matrix.mulVec_smul]
  have hA : ∑ j, Gx j • A.mulVec (unitVector j) = ηx • A.mulVec gx := by
    simp_rw [← Matrix.mulVec_smul]
    rw [← mulVec_finset_sum, sum_smul_unitVector, hΓ, Matrix.mulVec_smul]
  simp only [Matrix.mulVec_add, mulVec_finset_sum, Matrix.mulVec_smul, smul_sub, smul_add,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, hB, hA]
  module

theorem gradient_mul_of_differentiable {f h : Vec d → ℝ} (hf : Differentiable ℝ f)
    (hh : Differentiable ℝ h) (x : Vec d) :
    gradient (fun y => f y * h y) x = h x • gradient f x + f x • gradient h x := by
  funext i
  simp only [gradient, coordinateDerivative, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [fderiv_fun_mul (hf x) (hh x)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

/-! ## Integrability -/

theorem memLp_two_of_continuous_hasCompactSupport {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) : MemLp f 2 (volume.restrict U) :=
  (hf.memLp_of_hasCompactSupport hfc).restrict U

theorem memLp_continuous_mul {U : Set (Vec d)} {φ f : Vec d → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hf : MemLp f 2 (volume.restrict U)) :
    MemLp (fun x => φ x * f x) 2 (volume.restrict U) :=
  (hφ.memLp_top_of_hasCompactSupport hφc _).mul hf

theorem continuous_gradient_apply {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin d) :
    Continuous (fun x => gradient f x i) :=
  continuous_coordinateDerivative (hf.of_le (by simp)) i

theorem hasCompactSupport_gradient_apply {f : Vec d → ℝ} (hfc : HasCompactSupport f)
    (i : Fin d) : HasCompactSupport (fun x => gradient f x i) :=
  hfc.fderiv_apply (𝕜 := ℝ) (unitVector i)

theorem integrable_dot_of_memLp {U : Set (Vec d)} {P Q : Vec d → Vec d}
    (hP : ∀ i, MemLp (fun x => P x i) 2 (volume.restrict U))
    (hQ : ∀ i, MemLp (fun x => Q x i) 2 (volume.restrict U)) :
    Integrable (fun x => dot (P x) (Q x)) (volume.restrict U) :=
  integrable_finsetSum _ fun i _ => integrable_mul_of_memLp_two (hP i) (hQ i)

theorem memLp_const_mulVec {U : Set (Vec d)} (A : Mat d) {Q : Vec d → Vec d}
    (hQ : ∀ i, MemLp (fun x => Q x i) 2 (volume.restrict U)) (i : Fin d) :
    MemLp (fun x => A.mulVec (Q x) i) 2 (volume.restrict U) := by
  have h : MemLp (fun x => ∑ k, A i k * Q x k) 2 (volume.restrict U) :=
    memLp_finsetSum _ fun k _ => (hQ k).const_mul (A i k)
  exact h.ae_eq (Eventually.of_forall fun x => by simp [Matrix.mulVec, dotProduct])

theorem dot_add_left' (x y p : Vec d) : dot (x + y) p = dot x p + dot y p := by
  simp only [dot_eq_dotProduct, add_dotProduct]

theorem dot_sub_left' (x y p : Vec d) : dot (x - y) p = dot x p - dot y p := by
  simp only [dot_eq_dotProduct, sub_dotProduct]

theorem dot_smul_left' (c : ℝ) (x p : Vec d) : dot (c • x) p = c * dot x p := by
  simp only [dot_eq_dotProduct, smul_dotProduct, smul_eq_mul]

theorem dot_add_right' (p x y : Vec d) : dot p (x + y) = dot p x + dot p y := by
  simp only [dot_eq_dotProduct, dotProduct_add]

theorem dot_smul_right' (c : ℝ) (p x : Vec d) : dot p (c • x) = c * dot p x := by
  simp only [dot_eq_dotProduct, dotProduct_smul, smul_eq_mul]

theorem dot_sum_left' {ι : Type*} (s : Finset ι) (v : ι → Vec d) (p : Vec d) :
    dot (∑ j ∈ s, v j) p = ∑ j ∈ s, dot (v j) p := by
  unfold dot
  simp only [Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem setIntegral_dot_const_gradient_eq_zero {U : Set (Vec d)} (c : Vec d) {φ : Vec d → ℝ}
    (hφ : IsSpatialTest U φ) : ∫ x in U, dot c (gradient φ x) = 0 := by
  have hφu : IsSpatialTest Set.univ φ := ⟨hφ.1, hφ.2.1, Set.subset_univ _⟩
  have h := (hasWeakDivergence_const_field c).2.2 φ hφu
  simp only [Measure.restrict_univ, zero_mul, integral_zero, neg_zero] at h
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_]
  · exact h
  · have hx' : x ∉ tsupport φ := fun h' => hx (hφ.2.2 h')
    unfold dot gradient
    exact Finset.sum_eq_zero fun k _ => by
      rw [coordinateDerivative_eq_zero_of_notMem_tsupport hx' k, mul_zero]

/-! ## The identity -/

variable {U : Set (Vec d)} {b : CoefficientField d Λ} {A : Mat d} {η : Vec d → ℝ}
  {g : Vec d → Vec d} {G Φ : Fin d → Vec d → ℝ} {DΦ : Fin d → Vec d → Vec d}

/-- The gradient `∇u + ∑_j (G_j DΦ_j + Φ_j ∇G_j)` of the two-scale expansion. -/
def twoScaleGrad (g : Vec d → Vec d) (G Φ : Fin d → Vec d → ℝ) (DΦ : Fin d → Vec d → Vec d) :
    Vec d → Vec d :=
  fun x => g x + ∑ j, (G j x • DΦ j x + Φ j x • gradient (G j) x)

/-- **The equation of the two-scale expansion** (Step 1 of the proof of Theorem 1.17). -/
theorem integral_twoScaleGrad_eq (hUt : volume U ≠ ⊤)
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U))
    (hu : HasWeakDivergence U (fun x => A.mulVec (g x)) (fun _ => 0))
    (hη : Continuous η)
    (hG : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (G j)) (hGc : ∀ j, HasCompactSupport (G j))
    (hGη : ∀ᵐ x ∂(volume.restrict U), (fun j => G j x) = η x • g x)
    (hΦ : ∀ j, MemLp (Φ j) 2 (volume.restrict U))
    (hDΦ : ∀ j i, MemLp (fun x => DΦ j x i) 2 (volume.restrict U))
    (hflux : ∀ j, HasWeakDivergence U (fun x => (b x).mulVec (unitVector j + DΦ j x))
      (fun _ => 0))
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest U ψ) :
    ∫ x in U, dot ((b x).mulVec (twoScaleGrad g G Φ DΦ x)) (gradient ψ x) =
      (∫ x in U, dot ((1 - η x) • ((b x).mulVec (g x) - A.mulVec (g x))) (gradient ψ x)) -
        ∑ j, (∫ x in U, dot ((b x).mulVec (unitVector j + DΦ j x) - A.mulVec (unitVector j))
          (ψ x • gradient (G j) x)) +
        ∑ j, ∫ x in U, dot ((b x).mulVec (Φ j x • gradient (G j) x)) (gradient ψ x) := by
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUt
  have hψd : Differentiable ℝ ψ := hψ.1.differentiable (by simp)
  have hGd : ∀ j, Differentiable ℝ (G j) := fun j => (hG j).differentiable (by simp)
  -- the tests `G_j ψ` and their gradients
  have hGψ : ∀ j, IsSpatialTest U (fun x => G j x * ψ x) := fun j =>
    ⟨(hG j).mul hψ.1, hψ.2.1.mul_left, (tsupport_mul_subset_right).trans hψ.2.2⟩
  have hgradGψ : ∀ j x, gradient (fun y => G j y * ψ y) x =
      ψ x • gradient (G j) x + G j x • gradient ψ x := fun j x =>
    gradient_mul_of_differentiable (hGd j) hψd x
  -- `L²` memberships
  have hψg : ∀ i, MemLp (fun x => gradient ψ x i) 2 (volume.restrict U) := fun i =>
    memLp_two_of_continuous_hasCompactSupport (continuous_gradient_apply hψ.1 i)
      (hasCompactSupport_gradient_apply hψ.2.1 i)
  have hGψg : ∀ j i, MemLp (fun x => gradient (fun y => G j y * ψ y) x i) 2
      (volume.restrict U) := fun j i =>
    memLp_two_of_continuous_hasCompactSupport (continuous_gradient_apply (hGψ j).1 i)
      (hasCompactSupport_gradient_apply (hGψ j).2.1 i)
  have hψGg : ∀ j i, MemLp (fun x => (ψ x • gradient (G j) x) i) 2 (volume.restrict U) :=
    fun j i => memLp_two_of_continuous_hasCompactSupport
      (hψ.1.continuous.mul (continuous_gradient_apply (hG j) i))
      ((hasCompactSupport_gradient_apply (hGc j) i).mul_left)
  have hηψg : ∀ i, MemLp (fun x => ((1 - η x) • gradient ψ x) i) 2 (volume.restrict U) :=
    fun i => memLp_two_of_continuous_hasCompactSupport
      ((continuous_const.sub hη).mul (continuous_gradient_apply hψ.1 i))
      ((hasCompactSupport_gradient_apply hψ.2.1 i).mul_left)
  have hbM : ∀ {Q : Vec d → Vec d}, (∀ i, MemLp (fun x => Q x i) 2 (volume.restrict U)) →
      ∀ i, MemLp (fun x => (b x).mulVec (Q x) i) 2 (volume.restrict U) := fun hQ i =>
    memLp_coefficient_mulVec_apply b (memLp_pi_iff.2 hQ) i
  have hDe : ∀ j i, MemLp (fun x => (unitVector j + DΦ j x) i) 2 (volume.restrict U) :=
    fun j i => (memLp_const (unitVector (d := d) j i)).add (hDΦ j i)
  have hΦG : ∀ j i, MemLp (fun x => (Φ j x • gradient (G j) x) i) 2 (volume.restrict U) :=
    fun j i => by
      have h := memLp_continuous_mul (continuous_gradient_apply (hG j) i)
        (hasCompactSupport_gradient_apply (hGc j) i) (hΦ j)
      refine h.ae_eq (Eventually.of_forall fun x => ?_)
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  have hF : ∀ j i, MemLp (fun x => ((b x).mulVec (unitVector j + DΦ j x) -
      A.mulVec (unitVector j)) i) 2 (volume.restrict U) := fun j i =>
    (hbM (hDe j) i).sub (memLp_const _)
  have hgA : ∀ i, MemLp (fun x => ((b x).mulVec (g x) - A.mulVec (g x)) i) 2
      (volume.restrict U) := fun i => (hbM hg i).sub (memLp_const_mulVec A hg i)
  -- the pointwise identity
  have hpt : ∀ᵐ x ∂(volume.restrict U),
      dot ((b x).mulVec (twoScaleGrad g G Φ DΦ x)) (gradient ψ x) =
        dot ((b x).mulVec (g x) - A.mulVec (g x)) ((1 - η x) • gradient ψ x) +
          dot (A.mulVec (g x)) (gradient ψ x) +
          ∑ j, dot ((b x).mulVec (Φ j x • gradient (G j) x)) (gradient ψ x) +
          ∑ j, (dot ((b x).mulVec (unitVector j + DΦ j x))
              (gradient (fun y => G j y * ψ y) x) -
            dot (A.mulVec (unitVector j)) (gradient (fun y => G j y * ψ y) x) -
            dot ((b x).mulVec (unitVector j + DΦ j x) - A.mulVec (unitVector j))
              (ψ x • gradient (G j) x)) := by
    filter_upwards [hGη] with x hx
    have key := mulVec_twoScaleGrad_eq (b x) A (g x) (η x) (fun j => G j x) (fun j => Φ j x)
      (fun j => DΦ j x) (fun j => gradient (G j) x) hx
    have hj : ∀ j, dot ((b x).mulVec (unitVector j + DΦ j x))
          (gradient (fun y => G j y * ψ y) x) -
        dot (A.mulVec (unitVector j)) (gradient (fun y => G j y * ψ y) x) -
        dot ((b x).mulVec (unitVector j + DΦ j x) - A.mulVec (unitVector j))
          (ψ x • gradient (G j) x) =
        dot (G j x • ((b x).mulVec (unitVector j + DΦ j x) - A.mulVec (unitVector j)))
          (gradient ψ x) := by
      intro j
      rw [hgradGψ]
      simp only [dot_add_right', dot_smul_right', dot_smul_left', dot_sub_left']
      ring
    simp only [hj]
    rw [twoScaleGrad, key]
    simp only [dot_add_left', dot_sum_left', dot_smul_left', dot_smul_right']
  rw [integral_congr_ae hpt]
  -- integrability of the pieces
  have i1 : Integrable (fun x => dot ((b x).mulVec (g x) - A.mulVec (g x))
      ((1 - η x) • gradient ψ x)) (volume.restrict U) := integrable_dot_of_memLp hgA hηψg
  have i2 : Integrable (fun x => dot (A.mulVec (g x)) (gradient ψ x)) (volume.restrict U) :=
    integrable_dot_of_memLp (memLp_const_mulVec A hg) hψg
  have i3 : ∀ j, Integrable (fun x => dot ((b x).mulVec (Φ j x • gradient (G j) x))
      (gradient ψ x)) (volume.restrict U) := fun j =>
    integrable_dot_of_memLp (hbM (hΦG j)) hψg
  have i4 : ∀ j, Integrable (fun x => dot ((b x).mulVec (unitVector j + DΦ j x))
      (gradient (fun y => G j y * ψ y) x)) (volume.restrict U) := fun j =>
    integrable_dot_of_memLp (hbM (hDe j)) (hGψg j)
  have i5 : ∀ j, Integrable (fun x => dot (A.mulVec (unitVector j))
      (gradient (fun y => G j y * ψ y) x)) (volume.restrict U) := fun j =>
    integrable_dot_of_memLp (fun i => memLp_const _) (hGψg j)
  have i6 : ∀ j, Integrable (fun x => dot ((b x).mulVec (unitVector j + DΦ j x) -
      A.mulVec (unitVector j)) (ψ x • gradient (G j) x)) (volume.restrict U) := fun j =>
    integrable_dot_of_memLp (hF j) (hψGg j)
  -- the vanishing integrals
  have z2 : ∫ x in U, dot (A.mulVec (g x)) (gradient ψ x) = 0 := by
    have h := hu.2.2 ψ hψ
    simpa using h
  have z4 : ∀ j, ∫ x in U, dot ((b x).mulVec (unitVector j + DΦ j x))
      (gradient (fun y => G j y * ψ y) x) = 0 := fun j => by
    have h := (hflux j).2.2 _ (hGψ j)
    simpa using h
  have z5 : ∀ j, ∫ x in U, dot (A.mulVec (unitVector j))
      (gradient (fun y => G j y * ψ y) x) = 0 := fun j =>
    setIntegral_dot_const_gradient_eq_zero _ (hGψ j)
  have e1 : ∫ x in U, dot ((1 - η x) • ((b x).mulVec (g x) - A.mulVec (g x))) (gradient ψ x) =
      ∫ x in U, dot ((b x).mulVec (g x) - A.mulVec (g x)) ((1 - η x) • gradient ψ x) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [dot_smul_left', dot_smul_right']
  have e2 : ∀ j, ∫ x in U, (dot ((b x).mulVec (unitVector j + DΦ j x))
        (gradient (fun y => G j y * ψ y) x) -
      dot (A.mulVec (unitVector j)) (gradient (fun y => G j y * ψ y) x) -
      dot ((b x).mulVec (unitVector j + DΦ j x) - A.mulVec (unitVector j))
        (ψ x • gradient (G j) x)) =
      -∫ x in U, dot ((b x).mulVec (unitVector j + DΦ j x) - A.mulVec (unitVector j))
        (ψ x • gradient (G j) x) := fun j => by
    have h1 : ∫ x in U, (dot ((b x).mulVec (unitVector j + DΦ j x))
          (gradient (fun y => G j y * ψ y) x) -
        dot (A.mulVec (unitVector j)) (gradient (fun y => G j y * ψ y) x) -
        dot ((b x).mulVec (unitVector j + DΦ j x) - A.mulVec (unitVector j))
          (ψ x • gradient (G j) x)) =
        (∫ x in U, (dot ((b x).mulVec (unitVector j + DΦ j x))
          (gradient (fun y => G j y * ψ y) x) -
        dot (A.mulVec (unitVector j)) (gradient (fun y => G j y * ψ y) x))) -
        ∫ x in U, dot ((b x).mulVec (unitVector j + DΦ j x) - A.mulVec (unitVector j))
          (ψ x • gradient (G j) x) := integral_sub ((i4 j).sub (i5 j)) (i6 j)
    have h2 : ∫ x in U, (dot ((b x).mulVec (unitVector j + DΦ j x))
          (gradient (fun y => G j y * ψ y) x) -
        dot (A.mulVec (unitVector j)) (gradient (fun y => G j y * ψ y) x)) =
        (∫ x in U, dot ((b x).mulVec (unitVector j + DΦ j x))
          (gradient (fun y => G j y * ψ y) x)) -
        ∫ x in U, dot (A.mulVec (unitVector j)) (gradient (fun y => G j y * ψ y) x) :=
      integral_sub (i4 j) (i5 j)
    rw [h1, h2, z4 j, z5 j]
    ring
  have hsplit : ∫ x in U, (dot ((b x).mulVec (g x) - A.mulVec (g x)) ((1 - η x) • gradient ψ x) +
          dot (A.mulVec (g x)) (gradient ψ x) +
          ∑ j, dot ((b x).mulVec (Φ j x • gradient (G j) x)) (gradient ψ x) +
          ∑ j, (dot ((b x).mulVec (unitVector j + DΦ j x))
              (gradient (fun y => G j y * ψ y) x) -
            dot (A.mulVec (unitVector j)) (gradient (fun y => G j y * ψ y) x) -
            dot ((b x).mulVec (unitVector j + DΦ j x) - A.mulVec (unitVector j))
              (ψ x • gradient (G j) x))) =
      (∫ x in U, dot ((b x).mulVec (g x) - A.mulVec (g x)) ((1 - η x) • gradient ψ x)) +
        (∫ x in U, dot (A.mulVec (g x)) (gradient ψ x)) +
        ∑ j, (∫ x in U, dot ((b x).mulVec (Φ j x • gradient (G j) x)) (gradient ψ x)) +
        ∑ j, ∫ x in U, (dot ((b x).mulVec (unitVector j + DΦ j x))
              (gradient (fun y => G j y * ψ y) x) -
            dot (A.mulVec (unitVector j)) (gradient (fun y => G j y * ψ y) x) -
            dot ((b x).mulVec (unitVector j + DΦ j x) - A.mulVec (unitVector j))
              (ψ x • gradient (G j) x)) := by
    have s3 := integral_finsetSum (μ := volume.restrict U) Finset.univ fun j _ => i3 j
    have s4 := integral_finsetSum (μ := volume.restrict U) Finset.univ
      fun j _ => ((i4 j).sub (i5 j)).sub (i6 j)
    have a1 := integral_add (μ := volume.restrict U)
      ((i1.add i2).add (integrable_finsetSum Finset.univ fun j _ => i3 j))
      (integrable_finsetSum Finset.univ fun j _ => ((i4 j).sub (i5 j)).sub (i6 j))
    have a2 := integral_add (μ := volume.restrict U) (i1.add i2)
      (integrable_finsetSum Finset.univ fun j _ => i3 j)
    have a3 := integral_add (μ := volume.restrict U) i1 i2
    simp only [Pi.add_apply, Pi.sub_apply] at a1 a2 a3 s3 s4
    rw [a1, a2, a3, s3, s4]
  rw [hsplit, e1, z2]
  simp only [e2, Finset.sum_neg_distrib]
  ring

end TwoScale

end QSH
