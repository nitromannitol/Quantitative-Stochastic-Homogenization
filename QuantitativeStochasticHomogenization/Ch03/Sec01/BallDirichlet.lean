import QuantitativeStochasticHomogenization.Ch03.Sec01.BallScaling
import EllipticRegularity.Ch4.GreenDecay.Dirichlet

/-!
# The Dirichlet problem for a constant matrix on a ball

For a constant symmetric matrix `A` with `Id ≤ A ≤ Λ Id`, a ball `B_r` and `F ∈ L²(B_r)`, there is
`w ∈ H¹₀(B_r)` with `-∇·(A(∇w + F)) = 0` in `B_r` (`exists_ballDirichlet`); for `F = ∇f` this is the
solution `f + w ∈ f + H¹₀(B_r)` of the Dirichlet problem used in the proof of Proposition 3.2. It is
the existence theorem of the elliptic regularity library
(`PDE.Ch4GreenDecay.exists_dirichlet_solution`), with the conversion of its `H¹₀` functions and
weak solutions (`H01_of_h10Function`, `hasWeakGradient_of_pdeHasWeakGradientOn`).
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The weak gradient of the elliptic regularity library is a weak gradient. -/
theorem hasWeakGradient_of_pdeHasWeakGradientOn {U : Set (Vec d)} {u : Vec d → ℝ}
    {G : Vec d → Vec d} (h : PDE.HasWeakGradientOn U u G) (hu : LocallyIntegrableOn u U volume)
    (hG : ∀ i, LocallyIntegrableOn (fun x => G x i) U volume) : HasWeakGradient U u G := fun i =>
  ⟨hu, hG i, fun φ hφ => by
    simpa only [coordinateDerivative, unitVector, PDE.basisVec] using h i φ hφ.1 hφ.2.1 hφ.2.2⟩

theorem tendsto_integral_sq_of_tendsto_eLpNorm_two {μ : Measure (Vec d)} {F : ℕ → Vec d → ℝ}
    (hF : ∀ n, MemLp (F n) 2 μ) (h : Tendsto (fun n => eLpNorm (F n) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, F n x ^ 2 ∂μ) atTop (𝓝 0) := by
  have e : ∀ n, ∫ x, F n x ^ 2 ∂μ = ((eLpNorm (F n) 2 μ).toReal) ^ 2 := by
    intro n
    have h0 : 0 ≤ ∫ x, F n x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    rw [(hF n).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofNat]
    have e2 : ∫ x, ‖F n x‖ ^ (2 : ℝ) ∂μ = ∫ x, F n x ^ 2 ∂μ := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      change ‖F n x‖ ^ (2 : ℝ) = F n x ^ 2
      rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
    rw [e2, ← Real.rpow_natCast, ← Real.rpow_mul h0]
    norm_num
  simp_rw [e]
  have h2 : Tendsto (fun n => (eLpNorm (F n) 2 μ).toReal) atTop (𝓝 0) := by
    have h3 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    rw [ENNReal.toReal_zero] at h3
    exact h3
  simpa using h2.pow 2

/-- An `H¹₀(U)` function of the elliptic regularity library is in `H¹₀(U)`. -/
theorem H01_of_h10Function {U : Set (Vec d)} (hUt : volume U ≠ ⊤) (v : PDE.H10Function U) :
    H01 U v.toH1Function.toFun v.toH1Function.grad := by
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUt
  have hv : MemLp v.toH1Function.toFun 2 (volume.restrict U) := v.toH1Function.memL2
  have hg : ∀ i, MemLp (fun x => v.toH1Function.grad x i) 2 (volume.restrict U) :=
    fun i => v.toH1Function.gradMemL2 i
  have htest : ∀ n, IsSpatialTest U (v.approx n) := fun n =>
    ⟨v.approx_smooth n, v.approx_hasCompactSupport n, v.approx_support_subset n⟩
  refine ⟨hv, memLp_pi_iff.2 hg, hasWeakGradient_of_pdeHasWeakGradientOn
    v.toH1Function.hasWeakGradient (IntegrableOn.locallyIntegrableOn (hv.integrable one_le_two))
    (fun i => IntegrableOn.locallyIntegrableOn ((hg i).integrable one_le_two)),
    v.approx, htest, ?_, ?_⟩
  · exact tendsto_integral_sq_of_tendsto_eLpNorm_two
      (fun n => ((htest n).memLp_two _).sub hv) v.tendsto_approx
  · have hi : ∀ i, Tendsto (fun n => ∫ x in U, (gradient (v.approx n) x - v.toH1Function.grad x) i ^ 2)
        atTop (𝓝 0) := fun i =>
      tendsto_integral_sq_of_tendsto_eLpNorm_two
        (fun n => (MemLp.eval ((htest n).memLp_gradient _) i).sub (hg i))
        (v.tendsto_approx_grad i)
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun i _ => hi i
    simp only [Finset.sum_const_zero] at h
    refine h.congr fun n => ?_
    have hint : ∀ i ∈ (Finset.univ : Finset (Fin d)), Integrable
        (fun x => (gradient (v.approx n) x - v.toH1Function.grad x) i ^ 2)
        (volume.restrict U) := fun i _ =>
      (MemLp.eval (((htest n).memLp_gradient _).sub (memLp_pi_iff.2 hg)) i).integrable_sq
    rw [← integral_finsetSum Finset.univ hint]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [euclideanSq, dot, sq]

/-- **The Dirichlet problem for a constant matrix on a ball**: for `F ∈ L²(B_r)` there is
`w ∈ H¹₀(B_r)` of gradient `∇w` with `-∇·(A(∇w + F)) = 0` in `B_r`. -/
theorem exists_ballDirichlet {Λ : ℝ} (hΛ : 1 ≤ Λ) (hd : 0 < d) {r : ℝ} (hr : 0 < r) (A : Mat d)
    (hAt : A.transpose = A) (hA1 : ∀ ξ, euclideanSq ξ ≤ dot ξ (A.mulVec ξ))
    (hA2 : ∀ ξ, dot ξ (A.mulVec ξ) ≤ Λ * euclideanSq ξ) {F : Vec d → Vec d}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict (ball 0 r))) :
    ∃ (w : Vec d → ℝ) (gw : Vec d → Vec d), H01 (ball 0 r) w gw ∧
      HasWeakDivergence (ball 0 r) (fun x => A.mulVec (gw x + F x)) (fun _ => 0) := by
  classical
  set a : CoefficientField d Λ := constantCoefficientField A hAt hA1 hA2 with ha
  have hball : ball (0 : Vec d) r = PDE.euclideanBall 0 r := ball_eq_euclideanBall 0 hr
  rw [hball] at hF ⊢
  set U := PDE.euclideanBall (0 : Vec d) r with hU
  have hUm : MeasurableSet U := PDE.measurableSet_euclideanBall 0 r
  have hUt : volume U ≠ ⊤ := by
    rw [← hball]; exact volume_ball_ne_top' 0 r
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUt
  have hb := isEllipticFieldOn_ellipticFieldOf hΛ a hUm
  have hbA : ∀ᵐ x ∂(volume : Measure (Vec d)), ellipticFieldOf a x = A :=
    ellipticFieldOf_ae_eq hΛ a
  have hAF : ∀ i, MemLp (fun x => A.mulVec (F x) i) 2 (volume.restrict U) := fun i =>
    TwoScale.memLp_const_mulVec A hF i
  obtain ⟨v, hv⟩ := PDE.Ch4GreenDecay.exists_dirichlet_solution hd hr (b := ellipticFieldOf a)
    (fun i j => by
      have hm : Measurable (fun x => if x ∈ U then ellipticFieldOf a x i j else 0) :=
        (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hb.1)
      refine hm.aemeasurable.congr ?_
      filter_upwards [ae_restrict_mem hUm] with x hx
      exact (ite_eq_left_iff).2 fun h => absurd hx h)
    (fun x hx => hb.2 x hx) (g := fun _ => 0) (F := fun x => A.mulVec (F x))
    (memLp_const 0) (fun i => hAF i)
  have hH := H01_of_h10Function hUt v
  refine ⟨v.toH1Function.toFun, v.toH1Function.grad, hH, ?_, locallyIntegrableOn_zero, ?_⟩
  · intro i
    have h1 : MemLp (fun x => A.mulVec (v.toH1Function.grad x + F x) i) 2 (volume.restrict U) :=
      TwoScale.memLp_const_mulVec A (fun j => (MemLp.eval hH.2.1 j).add (hF j)) i
    exact IntegrableOn.locallyIntegrableOn (h1.integrable one_le_two)
  intro φ hφ
  have hφH := hφ.h01
  obtain ⟨-, hsol⟩ := hv hφH.toH10Function
  have hgφ : ∀ i, MemLp (fun x => gradient φ x i) 2 (volume.restrict U) := fun i =>
    MemLp.eval hφH.2.1 i
  have hA1' : ∀ i, MemLp (fun x => A.mulVec (v.toH1Function.grad x) i) 2 (volume.restrict U) :=
    fun i => TwoScale.memLp_const_mulVec A (fun j => MemLp.eval hH.2.1 j) i
  have hae : (fun x => PDE.vecDot (PDE.matVecMul (ellipticFieldOf a x) (v.toH1Function.grad x))
      (hφH.toH10Function.toH1Function.grad x)) =ᵐ[volume.restrict U]
      fun x => dot (A.mulVec (v.toH1Function.grad x)) (gradient φ x) := by
    filter_upwards [ae_restrict_of_ae hbA] with x hx
    change dot ((ellipticFieldOf a x).mulVec (v.toH1Function.grad x)) (gradient φ x) = _
    rw [hx]
  have hF' : (fun x => PDE.vecDot (A.mulVec (F x)) (hφH.toH10Function.toH1Function.grad x)) =
      fun x => dot (A.mulVec (F x)) (gradient φ x) := rfl
  rw [integral_congr_ae hae, hF'] at hsol
  simp only [zero_mul, integral_zero, zero_sub] at hsol
  have i1 := TwoScale.integrable_dot_of_memLp hA1' hgφ
  have i2 := TwoScale.integrable_dot_of_memLp hAF hgφ
  have hsplit : ∫ x in U, dot (A.mulVec (v.toH1Function.grad x + F x)) (gradient φ x) =
      (∫ x in U, dot (A.mulVec (v.toH1Function.grad x)) (gradient φ x)) +
        ∫ x in U, dot (A.mulVec (F x)) (gradient φ x) := by
    rw [← integral_add i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Matrix.mulVec_add, dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [hsplit, hsol, hU]
  simp only [zero_mul, integral_zero, neg_zero, neg_add_cancel]

end QSH
