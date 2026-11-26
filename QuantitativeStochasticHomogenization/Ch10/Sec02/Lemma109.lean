import QuantitativeStochasticHomogenization.Ch10.Sec02.QuantitiesBridge
import QuantitativeStochasticHomogenization.AppC.GlobalCaccioppoli
import QuantitativeStochasticHomogenization.Ch03.Sec04.CutoffTestIdentity

/-!
# Lemma 10.9: `S(U)` in terms of solutions of the equation and of its adjoint

Armstrong–Kuusi–Mourrat, Chapter 10, Section 10.2. With `A(U)` the solutions of
`-∇·(a∇u) = 0` and `A*(U)` the solutions of the adjoint equation `-∇·(aᵗ∇u*) = 0` (10.36),
Lemma 10.9 states `S(U) = {(∇u + ∇u*, a∇u - aᵗ∇u*) : u ∈ A(U), u* ∈ A*(U)}` (10.37).

`A(U)` and `A*(U)` are `IsSolutionOn (fun x => a x) U` and `IsSolutionOn (fun x => (a x)ᵀ) U`:
`u ∈ H¹(U)` with `∫_U ∇w·M∇u = 0` for every `w ∈ H¹₀(U)` (for `M = aᵗ` this is the book's
`∫_U ∇u*·a∇w = 0`). The elements of `S(U)` are pairs of fields up to null sets, so (10.37) is
stated with a.e. equalities. The proof is the characterization of the doubled response space of
the coarse-graining library (Armstrong and Kuusi, `DoubledResponseTheory.response_space_by_solutions`),
on a bounded open convex domain; this file also gives the passage between `H¹₀(U)` of this library
(`H01`) and that of the coarse-graining library (`Homogenization.H10Function`), used to identify
the solutions.
-/

open MeasureTheory Filter
open scoped Topology

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- `u ∈ H¹(U)` with gradient `G` solves `-∇·(M∇u) = 0` in `U`: `∫_U ∇w·M∇u = 0` for every
`w ∈ H¹₀(U)`. -/
def IsSolutionOn (M : Vec d → Mat d) (U : Set (Vec d)) (u : Vec d → ℝ) (G : Vec d → Vec d) : Prop :=
  H1 U u G ∧ IsNegDivergenceOn U (fun x => (M x).mulVec (G x)) (fun _ _ => 0)

/-! ### `H¹₀(U)` in the two libraries -/

/-- The `H¹₀(U)` function of the coarse-graining library given by `H01` data. -/
noncomputable def H01.toCGH10Function {U : Set (Vec d)} {u : Vec d → ℝ} {g : Vec d → Vec d}
    (h : H01 U u g) : _root_.Homogenization.H10Function U where
  toH1Function := H1.toH1Function' ⟨h.1, h.2.1, h.2.2.1⟩
  approx := Classical.choose h.2.2.2
  approx_smooth n := ((Classical.choose_spec h.2.2.2).1 n).1
  approx_hasCompactSupport n := ((Classical.choose_spec h.2.2.2).1 n).2.1
  approx_support_subset n := ((Classical.choose_spec h.2.2.2).1 n).2.2
  tendsto_approx := by
    obtain ⟨hv, hconv, -⟩ := Classical.choose_spec h.2.2.2
    exact tendsto_eLpNorm_two_of_tendsto_integral_sq
      (fun n => ((hv n).memLp_two _).sub h.1) hconv
  tendsto_approx_grad := by
    intro i
    obtain ⟨hv, -, hgconv⟩ := Classical.choose_spec h.2.2.2
    refine tendsto_eLpNorm_two_of_tendsto_integral_sq
      (fun n => (MemLp.eval ((hv n).memLp_gradient _) i).sub (MemLp.eval h.2.1 i)) ?_
    refine squeeze_zero (fun n => integral_nonneg fun x => sq_nonneg _) (fun n => ?_) hgconv
    refine integral_mono
      ((MemLp.eval (((hv n).memLp_gradient _).sub h.2.1) i).integrable_sq) ?_ fun x => ?_
    · exact integrable_euclideanSq_of_memLp (((hv n).memLp_gradient _).sub h.2.1)
    · change (coordinateDerivative i (Classical.choose h.2.2.2 n) x - g x i) ^ 2 ≤ _
      have e : coordinateDerivative i (Classical.choose h.2.2.2 n) x - g x i =
          (gradient (Classical.choose h.2.2.2 n) x - g x) i := rfl
      rw [e]
      exact sq_apply_le_vecNormSq _ i

@[simp] theorem H01.toCGH10Function_grad {U : Set (Vec d)} {u : Vec d → ℝ} {g : Vec d → Vec d}
    (h : H01 U u g) : h.toCGH10Function.toH1Function.grad = g := rfl

/-- An `H¹₀(U)` function of the coarse-graining library, on a set of finite measure, is in `H¹₀(U)`. -/
theorem H01.ofCGH10Function {U : Set (Vec d)} (hU : volume U ≠ ⊤)
    (φ : _root_.Homogenization.H10Function U) :
    H01 U φ.toH1Function.toFun φ.toH1Function.grad := by
  have hH1 := H1.ofH1Function hU φ.toH1Function
  have hv : ∀ n, IsSpatialTest U (φ.approx n) := fun n =>
    ⟨φ.approx_smooth n, φ.approx_hasCompactSupport n, φ.approx_support_subset n⟩
  refine ⟨hH1.1, hH1.2.1, hH1.2.2, φ.approx, hv, ?_, ?_⟩
  · exact tendsto_integral_sq_of_eLpNorm (fun n => ((hv n).memLp_two _).sub hH1.1) φ.tendsto_approx
  · have hcoord : ∀ i : Fin d, Tendsto (fun n => ∫ x in U,
        (coordinateDerivative i (φ.approx n) x - φ.toH1Function.grad x i) ^ 2) atTop (𝓝 0) :=
      fun i => tendsto_integral_sq_of_eLpNorm
        (fun n => (MemLp.eval ((hv n).memLp_gradient _) i).sub (MemLp.eval hH1.2.1 i))
        (φ.tendsto_approx_grad i)
    have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun i _ => hcoord i
    simp only [Finset.sum_const_zero] at hsum
    refine hsum.congr fun n => ?_
    have hint : ∀ i : Fin d, Integrable (fun x =>
        (coordinateDerivative i (φ.approx n) x - φ.toH1Function.grad x i) ^ 2) (volume.restrict U) :=
      fun i => (MemLp.eval (((hv n).memLp_gradient _).sub hH1.2.1) i).integrable_sq
    rw [← integral_finsetSum _ fun i _ => hint i]
    congr 1
    funext x
    simp only [euclideanSq, dot, gradient, Pi.sub_apply]
    exact Finset.sum_congr rfl fun i _ => sq _

/-! ### Solutions in the two libraries -/

theorem volume_ne_top_of_domain (D : _root_.Homogenization.Book.Ch02.Domain d) :
    volume (D : Set (Vec d)) ≠ ⊤ := by
  have h := measure_lt_top (_root_.Homogenization.volumeMeasureOn (D : Set (Vec d))) Set.univ
  rw [_root_.Homogenization.volumeMeasureOn, Measure.restrict_apply_univ] at h
  exact h.ne

/-- A solution of the coarse-graining library solves the equation in the sense of `IsSolutionOn`. -/
theorem isSolutionOn_of_aHarmonic {D : _root_.Homogenization.Book.Ch02.Domain d}
    {b : _root_.Homogenization.CoeffField d}
    (v : _root_.Homogenization.AHarmonicFunction b (D : Set (Vec d))) :
    IsSolutionOn b D v.toH1.toFun v.toH1.grad := by
  refine ⟨H1.ofH1Function (volume_ne_top_of_domain D) v.toH1, fun φ Φ hφ => ?_⟩
  show ∫ x in (D : Set (Vec d)), dot (Φ x) ((b x).mulVec (v.toH1.grad x)) = 0
  have h := v.isHarmonic.2 hφ.toCGH10Function
  rw [H01.toCGH10Function_grad] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  change dot (Φ x) ((b x).mulVec (v.toH1.grad x)) =
    _root_.Homogenization.vecDot (_root_.Homogenization.matVecMul (b x) (v.toH1.grad x)) (Φ x)
  exact dotProduct_comm _ _

/-- A solution in the sense of `IsSolutionOn` is a solution of the coarse-graining library. -/
noncomputable def IsSolutionOn.toAHarmonic {D : _root_.Homogenization.Book.Ch02.Domain d}
    {b : _root_.Homogenization.CoeffField d} {u : Vec d → ℝ} {G : Vec d → Vec d}
    (h : IsSolutionOn b D u G) : _root_.Homogenization.AHarmonicFunction b (D : Set (Vec d)) where
  toH1 := H1.toH1Function' h.1
  isHarmonic := by
    refine ⟨⟨H1.toH1Function' h.1, rfl⟩, fun φ => ?_⟩
    have h2 : ∫ x in (D : Set (Vec d)), dot (φ.toH1Function.grad x) ((b x).mulVec (G x)) = 0 :=
      h.2 _ _ (H01.ofCGH10Function (volume_ne_top_of_domain D) φ)
    refine Eq.trans (integral_congr_ae (Eventually.of_forall fun x => ?_)) h2
    change _root_.Homogenization.vecDot (_root_.Homogenization.matVecMul (b x) (G x))
      (φ.toH1Function.grad x) = dot (φ.toH1Function.grad x) ((b x).mulVec (G x))
    exact dotProduct_comm _ _

@[simp] theorem IsSolutionOn.toAHarmonic_grad {D : _root_.Homogenization.Book.Ch02.Domain d}
    {b : _root_.Homogenization.CoeffField d} {u : Vec d → ℝ} {G : Vec d → Vec d}
    (h : IsSolutionOn b D u G) : h.toAHarmonic.toH1.grad = G := rfl

namespace GeneralCoefficientField

variable (a : GeneralCoefficientField d Λ)

/-- **Lemma 10.9**, (10.37): on a bounded open convex domain `D`, `S = (S₁, S₂) ∈ S(D)` if and only
if `S = (∇u + ∇u*, a∇u - aᵗ∇u*)` a.e. in `D` for some `u ∈ A(D)` and `u* ∈ A*(D)`. -/
theorem lemma_10_9 (D : _root_.Homogenization.Book.Ch02.Domain d) (S₁ S₂ : Vec d → Vec d) :
    a.IsResponseField D S₁ S₂ ↔
      ∃ (u : Vec d → ℝ) (G : Vec d → Vec d) (u' : Vec d → ℝ) (G' : Vec d → Vec d),
        IsSolutionOn (fun x => a x) D u G ∧ IsSolutionOn (fun x => (a x).transpose) D u' G' ∧
        S₁ =ᵐ[volume.restrict D] (fun x => G x + G' x) ∧
        S₂ =ᵐ[volume.restrict D] (fun x => (a x).mulVec (G x) - (a x).transpose.mulVec (G' x)) := by
  rw [a.isResponseField_iff D,
    (_root_.Homogenization.Book.Ch02.doubledResponseTheory D (a.toCGCoeffOn D)).response_space_by_solutions]
  constructor
  · rintro ⟨v, vStar, h1, h2⟩
    refine ⟨v.toH1.toFun, v.toH1.grad, vStar.toH1.toFun, vStar.toH1.grad,
      isSolutionOn_of_aHarmonic v, isSolutionOn_of_aHarmonic vStar, h1, h2⟩
  · rintro ⟨u, G, u', G', hu, hu', h1, h2⟩
    exact ⟨hu.toAHarmonic, hu'.toAHarmonic, h1, h2⟩

end GeneralCoefficientField

end QSH
