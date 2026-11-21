import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicExpansionBall
import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicOrthogonality
import PDEFoundation.PDE.HarmonicPointwiseProof

/-!
# Proof of the harmonic expansion on balls

A function of `H¹(B_b)` that is weakly harmonic has a smooth harmonic representative `v`
(Weyl's lemma), with `|∇v(0)| ≤ C b⁻¹ ‖u‖_{L̲²(B_b)}`. For `t < r < b` the first-order Taylor
remainder satisfies `⨍_{B_t} (v - v(0) - Dv(0) y)² ≤ (t/r)⁴ ⨍_{B_r} v² ≤ (t/r)⁴ (b/r)^d ⨍_{B_b} v²`,
and `r → b` gives the constant `(t/b)⁴`.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ}

theorem ball_zero_eq_pdeEuclideanBall {b : ℝ} (hb : 0 < b) :
    ball (0 : Vec d) b = PDE.euclideanBall 0 b := by
  ext x
  rw [PDE.mem_euclideanBall_zero_iff]
  change euclideanNorm (x - 0) < b ↔ _
  rw [sub_zero, euclideanNorm, Real.sqrt_lt' hb]
  rfl

/-- The `H¹` function of the weak data. -/
def toH1Function {b : ℝ} (hb : 0 < b) {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict (ball 0 b)))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 b)))
    (hw : HasWeakGradient (ball 0 b) u g) : PDE.H1Function (PDE.euclideanBall (0 : Vec d) b) where
  toFun := u
  grad := g
  memL2 := by
    change MemLp u 2 (volume.restrict (PDE.euclideanBall (0 : Vec d) b))
    rw [← ball_zero_eq_pdeEuclideanBall hb]
    exact hu
  gradMemL2 := fun i => by
    change MemLp (fun x => g x i) 2 (volume.restrict (PDE.euclideanBall (0 : Vec d) b))
    rw [← ball_zero_eq_pdeEuclideanBall hb]
    exact hg i
  hasWeakGradient := fun i φ h1 h2 h3 => by
    rw [← ball_zero_eq_pdeEuclideanBall hb] at h3 ⊢
    exact (hw i).2.2 φ ⟨h1, h2, h3⟩

theorem isWeakDivergenceFormSolutionOn_toH1Function {b : ℝ} (hb : 0 < b) {u : Vec d → ℝ}
    {g : Vec d → Vec d} (hu : MemLp u 2 (volume.restrict (ball 0 b)))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 b)))
    (hw : HasWeakGradient (ball 0 b) u g)
    (hdiv : HasWeakDivergence (ball 0 b) (fun x => (1 : Mat d).mulVec (g x)) (fun _ => 0)) :
    PDE.IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat d)) (PDE.euclideanBall 0 b)
      (toH1Function hb hu hg hw) 0 0 := by
  intro φ
  have hdata : PDE.DivergenceFormL2DataOn (fun _ => (1 : Mat d)) (PDE.euclideanBall 0 b)
      (toH1Function hb hu hg hw) 0 0 := by
    refine ⟨fun i => ?_, ?_, fun i => ?_⟩
    · have h := (toH1Function hb hu hg hw).gradMemL2 i
      refine h.ae_eq (Eventually.of_forall fun x => ?_)
      simp [PDE.matVecMul, Matrix.one_apply, toH1Function]
    · exact MemLp.zero
    · exact MemLp.zero
  refine ⟨hdata.testable φ, ?_⟩
  have htest : IsSpatialTest (ball 0 b) φ.toFun :=
    ⟨φ.contDiff, φ.hasCompactSupport, by rw [ball_zero_eq_pdeEuclideanBall hb]; exact φ.tsupport_subset⟩
  have h := hdiv.2.2 φ.toFun htest
  rw [ball_zero_eq_pdeEuclideanBall hb] at h
  simp only [zero_mul, integral_zero, neg_zero] at h
  simp only [Pi.zero_apply, zero_mul, integral_zero]
  have e : ∫ x in PDE.euclideanBall (0 : Vec d) b,
      PDE.vecDot (PDE.matVecMul ((fun _ => (1 : Mat d)) x) ((toH1Function hb hu hg hw).grad x))
        (φ.grad x) =
      ∫ x in PDE.euclideanBall (0 : Vec d) b, dot ((1 : Mat d).mulVec (g x)) (gradient φ.toFun x) :=
    rfl
  have h' : ∫ x in PDE.euclideanBall (0 : Vec d) b,
      dot ((1 : Mat d).mulVec (g x)) (gradient φ.toFun x) = 0 := by simpa using h
  rw [e, h']
  simp [PDE.vecDot]

end QSH
