import QuantitativeStochasticHomogenization.AppB.SobolevSpaces
import SobolevStatements.Sobolev

/-!
# Theorem B.8: the global Sobolev inequality

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix B, Theorem B.8 for `k = 1`: for `p ∈ [1, d)` there is `C(p, d)` such that every
`v ∈ W^{1,p}(ℝ^d)` satisfies `‖v‖_{L^{dp/(d-p)}(ℝ^d)} ≤ C ‖v‖_{W^{1,p}(ℝ^d)}` (B.6).

The proof is the Gagliardo–Nirenberg–Sobolev inequality `‖v‖_{L^{dp/(d-p)}} ≤ C ‖∇v‖_{L^p}`
(Evans, Section 5.6.1) of the elliptic regularity library, `PDE.exists_sobolev_constant`, together
with `|∇v| ≤ ∑_i |∂_{x_i} v|`. The range `p ∈ [1, d)` is empty unless `d ≥ 2`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

theorem euclideanNorm_eq_vecEuclideanNorm (x : Vec d) : euclideanNorm x = PDE.vecEuclideanNorm x :=
  rfl

/-- The `L^p` norm of `|g|` is at most the sum of the `L^p` norms of the coordinates of `g`. -/
theorem eLpNorm_euclideanNorm_le_sum {μ : Measure (Vec d)} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {g : Vec d → Vec d} (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun x => euclideanNorm (g x)) p μ ≤ ∑ i, eLpNorm (fun x => g x i) p μ := by
  have hm : AEStronglyMeasurable (fun x => euclideanNorm (g x)) μ :=
    PDE.continuous_vecEuclideanNorm.comp_aestronglyMeasurable hg
  calc eLpNorm (fun x => euclideanNorm (g x)) p μ
      ≤ eLpNorm (∑ i, fun x => ‖g x i‖) p μ := by
        refine eLpNorm_mono hm fun x => ?_
        rw [Real.norm_of_nonneg (show 0 ≤ euclideanNorm (g x) from Real.sqrt_nonneg _), Finset.sum_apply,
          Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)]
        simp only [Real.norm_eq_abs]
        exact PDE.vecEuclideanNorm_le_sum_abs (g x)
    _ ≤ ∑ i, eLpNorm (fun x => ‖g x i‖) p μ := eLpNorm_sum_le hp
    _ = ∑ i, eLpNorm (fun x => g x i) p μ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact eLpNorm_norm _ ((continuous_apply i).comp_aestronglyMeasurable hg)

/-- The `L^p(U)` norm of `|g|` for `g` the weak gradient of `u ∈ W^{1,p}(U)` is at most the norm
(B.1). -/
theorem IsW1p.eLpNorm_euclideanNorm_le_w1pNorm {U : Set (Vec d)} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : Vec d → ℝ} {g : Vec d → Vec d} (h : IsW1p U p u g) :
    eLpNorm (fun x => euclideanNorm (g x)) p (volume.restrict U) ≤ w1pNorm U p u g :=
  (eLpNorm_euclideanNorm_le_sum hp h.2.1.aestronglyMeasurable).trans le_add_self

/-- **Theorem B.8** (global Sobolev inequality), `k = 1`: for `p ∈ [1, d)` there is `C(p, d)`
with `‖v‖_{L^{dp/(d-p)}(ℝ^d)} ≤ C ‖v‖_{W^{1,p}(ℝ^d)}` for every `v ∈ W^{1,p}(ℝ^d)`, (B.6). -/
theorem theorem_B_8_one (p : ℝ) (hp : 1 ≤ p) (hpd : p < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Vec d → ℝ) (g : Vec d → Vec d),
      IsW1p Set.univ (ENNReal.ofReal p) v g →
        eLpNorm v (ENNReal.ofReal (d * p / (d - p))) volume ≤
          ENNReal.ofReal C * w1pNorm Set.univ (ENNReal.ofReal p) v g := by
  have hd : 2 ≤ d := by
    have : 1 < d := by exact_mod_cast (show (1 : ℝ) < d by linarith)
    omega
  obtain ⟨Cs, hCs, hS⟩ := PDE.exists_sobolev_constant d hd
  have hγ : 0 < p * ((d : ℝ) - 1) / ((d : ℝ) - p) :=
    div_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  refine ⟨Cs * (p * ((d : ℝ) - 1) / ((d : ℝ) - p)), mul_pos hCs hγ, fun v g hv => ?_⟩
  have hp1 : 1 ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have h := (hS p hp hpd).1 hv.toW1pFunction
  have hg := hv.eLpNorm_euclideanNorm_le_w1pNorm hp1
  rw [Measure.restrict_univ] at hg
  exact h.trans (mul_le_mul' le_rfl hg)

end QSH
