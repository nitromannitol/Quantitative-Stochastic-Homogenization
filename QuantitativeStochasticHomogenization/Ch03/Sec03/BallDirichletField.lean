import QuantitativeStochasticHomogenization.Ch03.Sec01.BallDirichlet
import QuantitativeStochasticHomogenization.AppC.GlobalMeyers

/-!
# Dirichlet problems in balls for a coefficient field

For a coefficient field `a` with `1 ≤ a ≤ Λ` and `F ∈ L²(B_r)`, there is `w ∈ H¹₀(B_r)` with
`-∇·(a(∇w + F)) = 0` in `B_r` (`exists_ballDirichlet_field`), from the existence theorem of the
elliptic regularity library; the constant-coefficient case is `exists_ballDirichlet`.
-/

open MeasureTheory Filter Set

noncomputable section

namespace QSH

variable {d : ℕ}

/-- **The Dirichlet problem in `B_r` for a coefficient field.** -/
theorem exists_ballDirichlet_field {Λ : ℝ} (hΛ : 1 ≤ Λ) (hd : 0 < d) {r : ℝ} (hr : 0 < r)
    (a : CoefficientField d Λ) {F : Vec d → Vec d}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict (ball 0 r))) :
    ∃ (w : Vec d → ℝ) (gw : Vec d → Vec d), H01 (ball 0 r) w gw ∧
      HasWeakDivergence (ball 0 r) (fun x => (a x).mulVec (gw x + F x)) (fun _ => 0) := by
  classical
  have hball : ball (0 : Vec d) r = PDE.euclideanBall 0 r := ball_eq_euclideanBall 0 hr
  rw [hball] at hF ⊢
  set U := PDE.euclideanBall (0 : Vec d) r with hU
  have hUm : MeasurableSet U := PDE.measurableSet_euclideanBall 0 r
  have hUt : volume U ≠ ⊤ := by
    rw [← hball]; exact volume_ball_ne_top' 0 r
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUt
  have hb := isEllipticFieldOn_ellipticFieldOf hΛ a hUm
  have hbA : ∀ᵐ x ∂(volume : Measure (Vec d)), ellipticFieldOf a x = a x :=
    ellipticFieldOf_ae_eq hΛ a
  have hΛ0 : (0 : ℝ) ≤ Λ := by linarith
  have hAF : ∀ i, MemLp (fun x => (a x).mulVec (F x) i) 2 (volume.restrict U) := fun i =>
    memLp_coefficient_mulVec_apply_of_coord hΛ0 a hF i
  obtain ⟨v, hv⟩ := PDE.Ch4GreenDecay.exists_dirichlet_solution hd hr (b := ellipticFieldOf a)
    (fun i j => by
      have hm : Measurable (fun x => if x ∈ U then ellipticFieldOf a x i j else 0) :=
        (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hb.1)
      refine hm.aemeasurable.congr ?_
      filter_upwards [ae_restrict_mem hUm] with x hx
      exact (ite_eq_left_iff).2 fun h => absurd hx h)
    (fun x hx => hb.2 x hx) (g := fun _ => 0) (F := fun x => (a x).mulVec (F x))
    (memLp_const 0) (fun i => hAF i)
  have hH := H01_of_h10Function hUt v
  refine ⟨v.toH1Function.toFun, v.toH1Function.grad, hH, ?_, locallyIntegrableOn_zero, ?_⟩
  · intro i
    have h1 : MemLp (fun x => (a x).mulVec (v.toH1Function.grad x + F x) i) 2
        (volume.restrict U) :=
      memLp_coefficient_mulVec_apply_of_coord hΛ0 a (fun j => (MemLp.eval hH.2.1 j).add (hF j)) i
    exact IntegrableOn.locallyIntegrableOn (h1.integrable one_le_two)
  intro φ hφ
  have hφH := hφ.h01
  obtain ⟨-, hsol⟩ := hv hφH.toH10Function
  have hgφ : ∀ i, MemLp (fun x => gradient φ x i) 2 (volume.restrict U) := fun i =>
    MemLp.eval hφH.2.1 i
  have hA1' : ∀ i, MemLp (fun x => (a x).mulVec (v.toH1Function.grad x) i) 2
      (volume.restrict U) :=
    fun i => memLp_coefficient_mulVec_apply_of_coord hΛ0 a (fun j => MemLp.eval hH.2.1 j) i
  have hae : (fun x => PDE.vecDot (PDE.matVecMul (ellipticFieldOf a x) (v.toH1Function.grad x))
      (hφH.toH10Function.toH1Function.grad x)) =ᵐ[volume.restrict U]
      fun x => dot ((a x).mulVec (v.toH1Function.grad x)) (gradient φ x) := by
    filter_upwards [ae_restrict_of_ae hbA] with x hx
    change dot ((ellipticFieldOf a x).mulVec (v.toH1Function.grad x)) (gradient φ x) = _
    rw [hx]
  have hF' : (fun x => PDE.vecDot ((a x).mulVec (F x)) (hφH.toH10Function.toH1Function.grad x)) =
      fun x => dot ((a x).mulVec (F x)) (gradient φ x) := rfl
  rw [integral_congr_ae hae, hF'] at hsol
  simp only [zero_mul, integral_zero, zero_sub] at hsol
  have i1 := TwoScale.integrable_dot_of_memLp hA1' hgφ
  have i2 := TwoScale.integrable_dot_of_memLp hAF hgφ
  have hsplit : ∫ x in U, dot ((a x).mulVec (v.toH1Function.grad x + F x)) (gradient φ x) =
      (∫ x in U, dot ((a x).mulVec (v.toH1Function.grad x)) (gradient φ x)) +
        ∫ x in U, dot ((a x).mulVec (F x)) (gradient φ x) := by
    rw [← integral_add i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Matrix.mulVec_add, dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [hsplit, hsol, hU]
  simp only [zero_mul, integral_zero, neg_zero, neg_add_cancel]

end QSH
