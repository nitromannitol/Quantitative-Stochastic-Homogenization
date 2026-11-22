import QuantitativeStochasticHomogenization.Ch03.Sec03.WeakGradientH10
import QuantitativeStochasticHomogenization.Ch03.Sec03.LaplacianPairing
import QuantitativeStochasticHomogenization.Ch03.Sec04.SpatialWeakProduct
import QuantitativeStochasticHomogenization.Ch03.Sec03.WeakRestriction

/-!
# The tensor identity of the harmonic approximation

Let `v` be `a`-harmonic in `H¹(E)` on an ellipsoid `E`, let `φᵢ` be correctors with `xᵢ + φᵢ`
`a`-harmonic, and let `σᵢ` be pointwise skew flux correctors in `H¹(E)` with
`∑ₖ ∂ₖ σᵢⱼₖ = (a(eᵢ + ∇φᵢ))ⱼ - (D eᵢ)ⱼ`. For every test `ψ` in `E`, with `Hᵢⱼ = ∂ⱼ∂ᵢψ`,
`∫ v ∑ᵢⱼ (D eᵢ)ⱼ Hᵢⱼ = ∑ᵢⱼₖ ∫ σᵢⱼₖ ∂ₖv Hᵢⱼ + ∑ᵢⱼ ∫ φᵢ (a∇v)ⱼ Hᵢⱼ`.

The proof tests the equation of `xᵢ + φᵢ` with `v ∂ᵢψ`, the equation of `v` with `φᵢ ∂ᵢψ` and
with `ψ`, and the weak derivative of `σᵢⱼₖ` with the `H¹₀` function `v Hᵢⱼ`; the third derivatives
of `ψ` drop out against the skew `σᵢ`, and the symmetry of `a` exchanges `a(eᵢ + ∇φᵢ) · ∇v` with
`(eᵢ + ∇φᵢ) · a∇v`. This is step 1 of the harmonic approximation (2), in the form of
Armstrong–Kuusi–Mourrat, Section 3.3 (the identity `((a - Dᵀ)∇v)ᵢ = ∂ₖAᵢₖ`) tested with `∂ᵢψ`.
-/

open MeasureTheory Filter Set

noncomputable section

namespace QSH

variable {d : ℕ}

theorem memLp_mul_isSpatialTest {U : Set (Vec d)} {f ψ : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (hψ : IsSpatialTest U ψ) :
    MemLp (fun x => f x * ψ x) 2 (volume.restrict U) := by
  obtain ⟨C, hC⟩ := hψ.2.1.exists_bound_of_continuous hψ.1.continuous
  refine hf.of_le_mul (c := C) (hf.aestronglyMeasurable.mul hψ.1.continuous.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

theorem memLp_isSpatialTest_mul {U : Set (Vec d)} {f ψ : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (hψ : IsSpatialTest U ψ) :
    MemLp (fun x => ψ x * f x) 2 (volume.restrict U) :=
  (memLp_mul_isSpatialTest hf hψ).ae_eq (Eventually.of_forall fun _ => mul_comm _ _)

theorem memLp_isSpatialTest {U : Set (Vec d)} {ψ : Vec d → ℝ} (hψ : IsSpatialTest U ψ) :
    MemLp ψ 2 (volume.restrict U) :=
  memLp_of_continuous_hasCompactSupport hψ.1.continuous hψ.2.1 U

theorem integrable_mul_mul_isSpatialTest {U : Set (Vec d)} {f g ψ : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U))
    (hψ : IsSpatialTest U ψ) :
    Integrable (fun x => f x * g x * ψ x) (volume.restrict U) := by
  have h := integrable_mul_of_memLp_two hf (memLp_mul_isSpatialTest hg hψ)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only
  ring

theorem integrable_isSpatialTest_mul_dot {U : Set (Vec d)} {F G : Vec d → Vec d}
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest U ψ) (hF : ∀ l, MemLp (fun x => F x l) 2 (volume.restrict U))
    (hG : ∀ l, MemLp (fun x => G x l) 2 (volume.restrict U)) :
    Integrable (fun x => ψ x * dot (F x) (G x)) (volume.restrict U) := by
  have h := integrable_finsetSum (Finset.univ : Finset (Fin d)) fun l _ =>
    integrable_mul_mul_isSpatialTest (hF l) (hG l) hψ
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [dot, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem integrable_mul_sum_mul_isSpatialTest {U : Set (Vec d)} {v : Vec d → ℝ}
    {F H : Fin d → Vec d → ℝ} (hv : MemLp v 2 (volume.restrict U))
    (hF : ∀ j, MemLp (F j) 2 (volume.restrict U)) (hH : ∀ j, IsSpatialTest U (H j)) :
    Integrable (fun x => v x * ∑ j, F j x * H j x) (volume.restrict U) := by
  have h := integrable_finsetSum (Finset.univ : Finset (Fin d)) fun j _ =>
    integrable_mul_mul_isSpatialTest hv (hF j) (hH j)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem dot_smul_add_smul (F g h : Vec d) (s t : ℝ) :
    dot F (s • g + t • h) = s * dot F g + t * dot F h := by
  unfold dot
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem dot_unitVector_left (i : Fin d) (q : Vec d) : dot (unitVector i) q = q i := by
  unfold dot unitVector
  simp [Pi.single_apply]

theorem dot_add_left (ξ η ζ : Vec d) : dot (ξ + η) ζ = dot ξ ζ + dot η ζ := by
  unfold dot
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem dot_comm' (ξ η : Vec d) : dot ξ η = dot η ξ := by
  unfold dot
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem memLp_coefficient_mulVec {Λ : ℝ} (hΛ : 1 ≤ Λ) (a : CoefficientField d Λ)
    {U : Set (Vec d)} (hU : MeasurableSet U) {g : Vec d → Vec d}
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U)) (j : Fin d) :
    MemLp (fun x => (a x).mulVec (g x) j) 2 (volume.restrict U) := by
  have h := PDE.memVectorL2On_matVecMul_of_isEllipticFieldOn
    (isEllipticFieldOn_ellipticFieldOf hΛ a hU) hg j
  refine h.ae_eq ?_
  filter_upwards [ae_restrict_of_ae (ellipticFieldOf_ae_eq hΛ a)] with x hx
  rw [hx]
  rfl

theorem dot_coefficient_mulVec_comm {Λ : ℝ} (a : CoefficientField d Λ) (x ξ η : Vec d) :
    dot ((a x).mulVec ξ) η = dot ξ ((a x).mulVec η) := by
  have hs : ∀ i j, a x i j = a x j i := fun i j => by
    have h := congrFun (congrFun (a.symmetric x) j) i
    simpa [Matrix.transpose_apply] using h
  unfold dot
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hs i j]
  ring

/-- A field whose components have weak gradients has the sum of the diagonal derivatives as
weak divergence. -/
theorem hasWeakDivergence_of_hasWeakGradient {U : Set (Vec d)} {F : Vec d → Vec d}
    {G : Fin d → Vec d → Vec d} (hF : ∀ k, HasWeakGradient U (fun x => F x k) (G k)) :
    HasWeakDivergence U F (fun x => ∑ k, G k x k) := by
  refine ⟨fun k => (hF k k).1, ?_, fun ψ hψ => ?_⟩
  · have key : ∀ s : Finset (Fin d),
        LocallyIntegrableOn (fun x => ∑ k ∈ s, G k x k) U volume := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using (locallyIntegrableOn_zero : LocallyIntegrableOn
          (fun _ : Vec d => (0 : ℝ)) U volume)
      | insert k s hk ih =>
        convert (hF k k).2.1.add ih using 1
        funext x
        simp [Finset.sum_insert hk]
    exact key Finset.univ
  · have h1 : ∀ k, IntegrableOn (fun x => F x k * coordinateDerivative k ψ x) U :=
      fun k => integrableOn_mul_spatialTest (hF k k).1 (isSpatialTest_coordinateDerivative hψ k)
    have h2 : ∀ k, IntegrableOn (fun x => G k x k * ψ x) U :=
      fun k => integrableOn_mul_spatialTest (hF k k).2.1 hψ
    have e1 : ∫ x in U, dot (F x) (gradient ψ x) =
        ∑ k, ∫ x in U, F x k * coordinateDerivative k ψ x := by
      rw [← integral_finsetSum _ fun k _ => h1 k]
      rfl
    have e2 : ∫ x in U, (∑ k, G k x k) * ψ x = ∑ k, ∫ x in U, G k x k * ψ x := by
      rw [← integral_finsetSum _ fun k _ => h2 k]
      simp only [Finset.sum_mul]
    rw [e1, e2, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => (hF k k).2.2 ψ hψ

/-- The third derivatives of a test drop out against a skew family. -/
theorem sum_sum_skew_mul_symm_eq_zero {σ : Fin d → Fin d → ℝ} {T : Fin d → Fin d → ℝ}
    (hσ : ∀ j k, σ j k = -σ k j) (hT : ∀ j k, T j k = T k j) :
    ∑ j, ∑ k, σ j k * T j k = 0 := by
  have h : ∑ j, ∑ k, σ j k * T j k = -∑ j, ∑ k, σ j k * T j k := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hσ k j, hT k j]
    ring
  linarith

/-- **The tensor identity of the harmonic approximation** (step 1 of (2)). -/
theorem integral_mul_secondOrder_eq_tensor {Λ : ℝ} (hΛ : 1 ≤ Λ) (a : CoefficientField d Λ)
    {M : Mat d} (hdet : M.det ≠ 0) {R : ℝ} (hR : 0 < R) (D : Mat d)
    {v : Vec d → ℝ} {gv : Vec d → Vec d}
    (hv : MemLp v 2 (volume.restrict (matrixEllipsoid M R)))
    (hgv : ∀ i, MemLp (fun x => gv x i) 2 (volume.restrict (matrixEllipsoid M R)))
    (hwv : HasWeakGradient (matrixEllipsoid M R) v gv)
    (hdiv : HasWeakDivergence (matrixEllipsoid M R) (fun x => (a x).mulVec (gv x)) (fun _ => 0))
    {φ : Fin d → Vec d → ℝ} {gφ : Fin d → Vec d → Vec d}
    (hφ : ∀ i, MemLp (φ i) 2 (volume.restrict (matrixEllipsoid M R)))
    (hgφ : ∀ i l, MemLp (fun x => gφ i x l) 2 (volume.restrict (matrixEllipsoid M R)))
    (hwφ : ∀ i, HasWeakGradient (matrixEllipsoid M R) (φ i) (gφ i))
    (hc : ∀ i, MemLp (fun x => x i + φ i x) 2 (volume.restrict (matrixEllipsoid M R)))
    (hgc : ∀ i l, MemLp (fun x => (unitVector i + gφ i x) l) 2
      (volume.restrict (matrixEllipsoid M R)))
    (hwc : ∀ i, HasWeakGradient (matrixEllipsoid M R) (fun x => x i + φ i x)
      (fun x => unitVector i + gφ i x))
    (hdivc : ∀ i, HasWeakDivergence (matrixEllipsoid M R)
      (fun x => (a x).mulVec (unitVector i + gφ i x)) (fun _ => 0))
    {σ : Fin d → Vec d → Mat d} {gσ : Fin d → Fin d → Fin d → Vec d → Vec d}
    (hσ : ∀ i j k, MemLp (fun x => σ i x j k) 2 (volume.restrict (matrixEllipsoid M R)))
    (hgσ : ∀ i j k l, MemLp (fun x => gσ i j k x l) 2 (volume.restrict (matrixEllipsoid M R)))
    (hwσ : ∀ i j k, HasWeakGradient (matrixEllipsoid M R) (fun x => σ i x j k) (gσ i j k))
    (hskew : ∀ i x j k, σ i x j k = -σ i x k j)
    (hflux : ∀ i j, HasWeakDivergence (matrixEllipsoid M R) (fun x k => σ i x j k)
      (fun x => (a x).mulVec (unitVector i + gφ i x) j - D.mulVec (unitVector i) j))
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest (matrixEllipsoid M R) ψ) :
    ∫ x in matrixEllipsoid M R, v x * ∑ i, ∑ j, D.mulVec (unitVector i) j *
        coordinateDerivative j (coordinateDerivative i ψ) x =
      (∑ i, ∑ j, ∑ k, ∫ x in matrixEllipsoid M R, σ i x j k * gv x k *
          coordinateDerivative j (coordinateDerivative i ψ) x) +
        ∑ i, ∑ j, ∫ x in matrixEllipsoid M R, φ i x * (a x).mulVec (gv x) j *
          coordinateDerivative j (coordinateDerivative i ψ) x := by
  classical
  set E := matrixEllipsoid M R with hEdef
  set μ : Measure (Vec d) := volume.restrict E with hμdef
  have hU := isOpenBoundedConvexDomain_matrixEllipsoid hdet hR
  have hEo : IsOpen E := hU.1
  have hEm : MeasurableSet E := hEo.measurableSet
  set P : Fin d → Vec d → ℝ := fun i => coordinateDerivative i ψ with hPdef
  set H : Fin d → Fin d → Vec d → ℝ := fun i j => coordinateDerivative j (P i) with hHdef
  set T : Fin d → Fin d → Fin d → Vec d → ℝ := fun i j k => coordinateDerivative k (H i j)
    with hTdef
  have hP : ∀ i, IsSpatialTest E (P i) := fun i => isSpatialTest_coordinateDerivative hψ i
  have hH : ∀ i j, IsSpatialTest E (H i j) := fun i j => isSpatialTest_coordinateDerivative (hP i) j
  have hT : ∀ i j k, IsSpatialTest E (T i j k) := fun i j k =>
    isSpatialTest_coordinateDerivative (hH i j) k
  have hTsymm : ∀ i j k x, T i j k x = T i k j x := fun i j k x =>
    coordinateDerivative_comm_of_contDiff_two ((hP i).1.of_le (by simp)) k j x
  set F : Fin d → Vec d → Vec d := fun i x => (a x).mulVec (unitVector i + gφ i x) with hFdef
  set q : Vec d → Vec d := fun x => (a x).mulVec (gv x) with hqdef
  have hF : ∀ i j, MemLp (fun x => F i x j) 2 μ := fun i j =>
    memLp_coefficient_mulVec hΛ a hEm (hgc i) j
  have hq : ∀ j, MemLp (fun x => q x j) 2 μ := fun j => memLp_coefficient_mulVec hΛ a hEm hgv j
  set Dc : Fin d → Fin d → ℝ := fun i j => D.mulVec (unitVector i) j with hDcdef
  -- the flux identity almost everywhere
  have hdivae : ∀ i j, ∀ᵐ x ∂μ, ∑ k, gσ i j k x k = F i x j - Dc i j := by
    intro i j
    have H₂ := hasWeakDivergence_of_hasWeakGradient (hwσ i j)
    have h := HasWeakDivergence.ae_eq hEo (hflux i j) H₂
    exact (ae_restrict_iff' hEm).2 (h.mono fun x hx hxE => (hx hxE).symm)
  -- testing the flux corrector with `v Hᵢⱼ`
  have hσpart : ∀ i j, ∫ x in E, v x * (F i x j - Dc i j) * H i j x =
      -(∑ k, ∫ x in E, σ i x j k * gv x k * H i j x) -
        ∫ x in E, v x * ∑ k, σ i x j k * T i j k x := by
    intro i j
    set Θ := (toH1FunctionOn hv hgv hwv).mulContDiffHasCompactSupportToH10 hU (hH i j).1
      (hH i j).2.1 (hH i j).2.2 with hΘdef
    have hΘf : Θ.toH1Function.toFun = fun x => H i j x * v x :=
      PDE.H1Function.mulContDiffHasCompactSupportToH10_toFun _ hU _ _ _
    have hΘg : Θ.toH1Function.grad = fun x => H i j x • gv x + v x • PDE.classicalGradient (H i j) x :=
      PDE.H1Function.mulContDiffHasCompactSupportToH10_grad _ hU _ _ _
    have hk : ∀ k, ∫ x in E, gσ i j k x k * (H i j x * v x) =
        -(∫ x in E, σ i x j k * gv x k * H i j x) - ∫ x in E, σ i x j k * (v x * T i j k x) := by
      intro k
      have h := integral_grad_mul_h10 (hσ i j k) (hgσ i j k) (hwσ i j k) Θ k
      rw [hΘf, hΘg] at h
      rw [h]
      have e : (fun x => σ i x j k * ((H i j x • gv x + v x • PDE.classicalGradient (H i j) x) k)) =
          fun x => σ i x j k * gv x k * H i j x + σ i x j k * (v x * T i j k x) := by
        funext x
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        change σ i x j k * (H i j x * gv x k + v x * coordinateDerivative k (H i j) x) = _
        ring
      simp only [e]
      rw [integral_add (integrable_mul_mul_isSpatialTest (hσ i j k) (hgv k) (hH i j))
        (integrable_mul_of_memLp_two (hσ i j k) (memLp_mul_isSpatialTest hv (hT i j k)))]
      ring
    have hsum : ∫ x in E, v x * (F i x j - Dc i j) * H i j x =
        ∑ k, ∫ x in E, gσ i j k x k * (H i j x * v x) := by
      rw [← integral_finsetSum _ fun k _ =>
        integrable_mul_of_memLp_two (hgσ i j k k) (memLp_isSpatialTest_mul hv (hH i j))]
      refine integral_congr_ae ?_
      filter_upwards [hdivae i j] with x hx
      try dsimp only
      rw [← Finset.sum_mul, hx]
      ring
    rw [hsum, Finset.sum_congr rfl fun k _ => hk k, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib]
    congr 1
    rw [← integral_finsetSum _ fun k _ =>
      integrable_mul_of_memLp_two (hσ i j k) (memLp_mul_isSpatialTest hv (hT i j k))]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    try dsimp only
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hthird : ∀ i, ∑ j, ∫ x in E, v x * ∑ k, σ i x j k * T i j k x = 0 := by
    intro i
    rw [← integral_finsetSum _ fun j _ => integrable_mul_sum_mul_isSpatialTest hv
      (fun k => hσ i j k) (fun k => hT i j k)]
    have hz : ∀ x, ∑ j, v x * ∑ k, σ i x j k * T i j k x = 0 := by
      intro x
      rw [← Finset.mul_sum, sum_sum_skew_mul_symm_eq_zero (fun j k => hskew i x j k)
        (fun j k => hTsymm i j k x), mul_zero]
    simp only [hz, integral_zero]
  -- testing the equation of `xᵢ + φᵢ` with `v ∂ᵢψ`
  have hPtest : ∀ i, (∫ x in E, P i x * dot (F i x) (gv x)) +
      ∫ x in E, v x * ∑ j, F i x j * H i j x = 0 := by
    intro i
    have h := integral_flux_dot_mul_test_eq_zero hΛ a hdet hR (hc i) (hgc i) (hwc i) (hdivc i)
      hv hgv hwv (hP i)
    rw [← integral_add (integrable_isSpatialTest_mul_dot (hP i) (hF i) hgv)
      (integrable_mul_sum_mul_isSpatialTest hv (hF i) (hH i))]
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    try dsimp only
    rw [dot_smul_add_smul]
    rfl
  -- testing the equation of `v` with `φᵢ ∂ᵢψ`
  have hQtest : ∀ i, (∫ x in E, P i x * dot (q x) (gφ i x)) +
      ∫ x in E, φ i x * ∑ j, q x j * H i j x = 0 := by
    intro i
    have h := integral_flux_dot_mul_test_eq_zero hΛ a hdet hR hv hgv hwv hdiv (hφ i) (hgφ i)
      (hwφ i) (hP i)
    rw [← integral_add (integrable_isSpatialTest_mul_dot (hP i) hq (hgφ i))
      (integrable_mul_sum_mul_isSpatialTest (hφ i) hq (hH i))]
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    try dsimp only
    rw [dot_smul_add_smul]
    rfl
  -- testing the equation of `v` with `ψ`
  have hRtest : ∑ i, ∫ x in E, P i x * q x i = 0 := by
    have h := hdiv.2.2 ψ hψ
    simp only [zero_mul, integral_zero, neg_zero] at h
    rw [← integral_finsetSum _ fun i _ =>
      integrable_mul_of_memLp_two (memLp_isSpatialTest (hP i)) (hq i), ← h]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    try dsimp only
    unfold dot
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  -- the symmetry of `a`
  have hsymm : ∀ i x, dot (F i x) (gv x) = q x i + dot (q x) (gφ i x) := by
    intro i x
    change dot ((a x).mulVec (unitVector i + gφ i x)) (gv x) = _
    rw [dot_coefficient_mulVec_comm, dot_add_left, dot_unitVector_left, dot_comm' (gφ i x)]
  have hfin : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.2 (volume_matrixEllipsoid_lt_top M R).ne
  have key : ∀ i, ∫ x in E, v x * ∑ j, Dc i j * H i j x =
      -(∫ x in E, P i x * q x i) + (∑ j, ∫ x in E, φ i x * q x j * H i j x) +
        ∑ j, ∑ k, ∫ x in E, σ i x j k * gv x k * H i j x := by
    intro i
    have hFD : ∀ j, MemLp (fun x => F i x j - Dc i j) 2 μ := fun j => (hF i j).sub (memLp_const _)
    have e1 : (∫ x in E, v x * ∑ j, Dc i j * H i j x) +
        ∑ j, ∫ x in E, v x * (F i x j - Dc i j) * H i j x =
          ∫ x in E, v x * ∑ j, F i x j * H i j x := by
      rw [← integral_finsetSum _ fun j _ => integrable_mul_mul_isSpatialTest hv (hFD j) (hH i j),
        ← integral_add (integrable_mul_sum_mul_isSpatialTest hv (fun j => memLp_const (Dc i j))
          (hH i))
          (integrable_finsetSum _ fun j _ => integrable_mul_mul_isSpatialTest hv (hFD j) (hH i j))]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      try dsimp only
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have e3 : ∫ x in E, P i x * dot (F i x) (gv x) =
        (∫ x in E, P i x * q x i) + ∫ x in E, P i x * dot (q x) (gφ i x) := by
      rw [← integral_add (integrable_mul_of_memLp_two (memLp_isSpatialTest (hP i)) (hq i))
        (integrable_isSpatialTest_mul_dot (hP i) hq (hgφ i))]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      try dsimp only
      rw [hsymm]
      ring
    have e5 : ∫ x in E, φ i x * ∑ j, q x j * H i j x = ∑ j, ∫ x in E, φ i x * q x j * H i j x := by
      rw [← integral_finsetSum _ fun j _ => integrable_mul_mul_isSpatialTest (hφ i) (hq j) (hH i j)]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      try dsimp only
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have e6 : ∑ j, ∫ x in E, v x * (F i x j - Dc i j) * H i j x =
        -(∑ j, ∑ k, ∫ x in E, σ i x j k * gv x k * H i j x) -
          ∑ j, ∫ x in E, v x * ∑ k, σ i x j k * T i j k x := by
      rw [Finset.sum_congr rfl fun j _ => hσpart i j, Finset.sum_sub_distrib,
        Finset.sum_neg_distrib]
    have h7 := hthird i
    have h2 := hPtest i
    have h4 := hQtest i
    linarith
  have hsplit : ∫ x in E, v x * ∑ i, ∑ j, Dc i j * H i j x =
      ∑ i, ∫ x in E, v x * ∑ j, Dc i j * H i j x := by
    rw [← integral_finsetSum _ fun i _ => integrable_mul_sum_mul_isSpatialTest hv
      (fun j => memLp_const (Dc i j)) (hH i)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    try dsimp only
    rw [Finset.mul_sum]
  change ∫ x in E, v x * ∑ i, ∑ j, Dc i j * H i j x = _
  rw [hsplit, Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, hRtest, neg_zero, zero_add, add_comm]

end QSH
