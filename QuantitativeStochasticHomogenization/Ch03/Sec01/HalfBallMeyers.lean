import QuantitativeStochasticHomogenization.Ch03.Sec01.BallScaling
import QuantitativeStochasticHomogenization.Ch03.Sec02.Lemma34
import QuantitativeStochasticHomogenization.Ch03.Sec03.ExcessIteration
import QuantitativeStochasticHomogenization.Ch01.Sec05.ConvexMeyers

/-!
# The Meyers estimate (3.14) on half balls

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 3.1, (3.14) in the proof of Proposition 3.2: there are `δ(d, Λ) > 0` and `C(d, Λ)` such
that every weak solution `u ∈ H¹(B_R)` of `-∇·(a∇u) = 0` in `B_R` has
`‖∇u‖_{L̲^{2+δ}(B_{R/2})} ≤ C R⁻¹ ‖u - (u)_{B_R}‖_{L̲²(B_R)}` (`meyers_halfBall`).

The book refers to Theorem C.1, which bounds `‖∇u‖_{L̲^{2+δ}(B_{r/2})}` by `‖∇u‖_{L̲²(B_r)}`; with the
Caccioppoli inequality (Lemma C.2) this gives (3.14) on a smaller ball. Here `B_{R/2}` is covered by
the balls `B_{R/16}(c)` with centers `c` on a grid of step `R/(16√d)`; on each, Theorem C.1 for the
translated coefficient field (`interiorMeyers_center`) and Lemma C.2 on `B_{R/4}(c) ⊆ B_R` give
the bound, and the number of balls depends only on `d`.
-/

open MeasureTheory Filter Set
open scoped ENNReal Pointwise

noncomputable section

namespace QSH

variable {d : ℕ}

theorem aestronglyMeasurable_euclideanNorm_normalizedVolumeOn {S T : Set (Vec d)} (hST : S ⊆ T)
    {g : Vec d → Vec d} (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict T)) :
    AEStronglyMeasurable (fun x => euclideanNorm (g x)) (PDE.normalizedVolumeOn S) :=
  ((memLp_euclideanNorm_of_coord hg).aestronglyMeasurable.mono_measure
    (Measure.restrict_mono hST le_rfl)).smul_measure _

/-- **The interior Meyers estimate at every center**: Theorem C.1 for `B_r(z)`, from Theorem C.1
on `B_r` for the translated coefficient field. -/
theorem interiorMeyers_center (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ (z : Vec d) (r : ℝ), 0 < r → ∀ (a : CoefficientField d Λ)
      (u : Vec d → ℝ) (g : Vec d → Vec d),
      MemLp u 2 (volume.restrict (ball z r)) →
      (∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball z r))) →
      HasWeakGradient (ball z r) u g →
      HasWeakDivergence (ball z r) (fun x => (a x).mulVec (g x)) (fun _ => 0) →
      PDE.eLpMeanNormOn (ball z (r / 2)) (ENNReal.ofReal (2 + δ)) (fun x => euclideanNorm (g x)) ≤
        ENNReal.ofReal C * PDE.eLpMeanNormOn (ball z r) 2 (fun x => euclideanNorm (g x)) := by
  obtain ⟨δ, C, hδ, hC, h1⟩ := theorem_C_1 hd hΛ
  refine ⟨δ, C, hδ, hC, fun z r hr a u g hu hg hug hdiv => ?_⟩
  have hpre : (fun x : Vec d => x + z) ⁻¹' ball z r = ball (0 : Vec d) r :=
    preimage_add_right_ball z r
  have hT : MeasurePreserving (fun x : Vec d => x + z) (volume.restrict (ball 0 r))
      (volume.restrict (ball z r)) := by
    rw [← hpre]
    exact (measurePreserving_add_right volume z).restrict_preimage (measurableSet_ball' z r)
  have hu' : MemLp (fun x => u (x + z)) 2 (volume.restrict (ball 0 r)) :=
    hu.comp_measurePreserving hT
  have hg' : ∀ i, MemLp (fun x => g (x + z) i) 2 (volume.restrict (ball 0 r)) := fun i =>
    (hg i).comp_measurePreserving hT
  have hmap : ∀ x ∈ ball (0 : Vec d) r, (1 : ℝ) • x + z ∈ ball z r := fun x hx => by
    rw [one_smul]
    have h : x ∈ (fun x : Vec d => x + z) ⁻¹' ball z r := by rw [hpre]; exact hx
    exact h
  have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) r)) :=
    isFiniteMeasure_restrict.mpr (volume_ball_ne_top' 0 r)
  have hug' : HasWeakGradient (ball 0 r) (fun x => u (x + z)) (fun x => g (x + z)) := by
    have h := hasWeakGradientOn_comp_smul_add one_pos z hmap hug
    simp only [inv_one, one_mul, one_smul] at h
    exact hasWeakGradient_of_hasWeakGradientOn' h
      (IntegrableOn.locallyIntegrableOn (hu'.integrable one_le_two))
      fun i => IntegrableOn.locallyIntegrableOn ((hg' i).integrable one_le_two)
  have hfl : ∀ i, MemLp (fun x => ((translate z a) x).mulVec (g (x + z)) i) 2
      (volume.restrict (ball 0 r)) := fun i =>
    memLp_coefficient_mulVec_apply (translate z a) (memLp_pi_iff.2 hg') i
  have hdiv' : HasWeakDivergence (ball 0 r) (fun x => ((translate z a) x).mulVec (g (x + z)))
      (fun _ => 0) := by
    have h := TwoScale.hasWeakDivergence_comp_smul_add one_pos z hmap hdiv (fun i => by
      simp only [one_smul]
      have e : (fun x => (a (x + z)).mulVec (g (x + z)) i) =
          fun x => ((translate z a) x).mulVec (g (x + z)) i := by
        funext x; show (a (x + z)).mulVec (g (x + z)) i = (a (z + x)).mulVec (g (x + z)) i
        rw [add_comm z x]
      rw [e]
      exact IntegrableOn.locallyIntegrableOn ((hfl i).integrable one_le_two))
    convert h using 2 with x
    simp only [one_smul]
    show ((translate z a) x).mulVec (g (x + z)) = (a (x + z)).mulVec (g (x + z))
    show (a (z + x)).mulVec (g (x + z)) = (a (x + z)).mulVec (g (x + z))
    rw [add_comm z x]
  have key := h1 (2 + δ) r (by linarith) hr (translate z a) (fun x => u (x + z))
    (fun x => g (x + z)) (fun _ => 0) (fun _ => 0) hu' hg' hug' (memLp_const 0)
    (fun _ => memLp_const 0) (by rw [negativeSobolevOneNorm_zero_zero]; exact ENNReal.zero_ne_top)
    (by simpa only [add_zero, neg_zero] using hdiv')
  rw [min_self, negativeSobolevOneNorm_zero_zero, add_zero] at key
  have hl : PDE.eLpMeanNormOn (ball (0 : Vec d) (r / 2)) (ENNReal.ofReal (2 + δ))
      (fun x => euclideanNorm (g (x + z))) =
        PDE.eLpMeanNormOn (ball z (r / 2)) (ENNReal.ofReal (2 + δ))
          (fun x => euclideanNorm (g x)) := by
    rw [← preimage_add_right_ball z (r / 2)]
    exact eLpMeanNormOn_comp_add z (measurableSet_ball' z (r / 2)) _
      (aestronglyMeasurable_euclideanNorm_normalizedVolumeOn
        (fun x hx => by
          show euclideanNorm (x - z) < r
          have : euclideanNorm (x - z) < r / 2 := hx
          linarith) hg)
  have hr' : PDE.eLpMeanNormOn (ball (0 : Vec d) r) 2 (fun x => euclideanNorm (g (x + z))) =
      PDE.eLpMeanNormOn (ball z r) 2 (fun x => euclideanNorm (g x)) := by
    rw [← preimage_add_right_ball z r]
    exact eLpMeanNormOn_comp_add z (measurableSet_ball' z r) _
      (aestronglyMeasurable_euclideanNorm_normalizedVolumeOn le_rfl hg)
  rw [← hl, ← hr']
  exact key

end QSH
