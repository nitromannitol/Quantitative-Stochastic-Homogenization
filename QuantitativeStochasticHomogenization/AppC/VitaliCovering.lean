import QuantitativeStochasticHomogenization.Ch04.Sec05.CubeDecomposition
import Mathlib.MeasureTheory.Covering.Vitali

/-!
# The Vitali covering lemma

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix C, Lemma C.5: a family of Euclidean balls `B_{r_α}(x_α)` in `ℝ^d` with uniformly bounded
radii has a countable, pairwise disjoint subfamily `{B_{r_β}(x_β)}_{β ∈ J}` with
`⋃_α B_{r_α}(x_α) ⊆ ⋃_{β ∈ J} B_{5 r_β}(x_β)`.

The proof is the Vitali selection of Mathlib, `Vitali.exists_disjoint_subfamily_covering_enlargement`,
with enlargement factor `τ = 2`, for the balls of positive radius: a ball `B_{r_α}(x_α)` meeting a
selected ball `B_{r_β}(x_β)` with `r_α ≤ 2 r_β` lies in `B_{r_β + 2 r_α}(x_β) ⊆ B_{5 r_β}(x_β)`.
Countability holds because pairwise disjoint nonempty open sets in the separable space `ℝ^d` form a
countable family.
-/

open MeasureTheory

namespace QSH

variable {d : ℕ}

theorem isOpen_ball_vitali (z : Vec d) (r : ℝ) : IsOpen (ball z r) := by
  have hc : Continuous fun y : Vec d => euclideanNorm (y - z) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  exact isOpen_lt hc continuous_const

theorem mem_ball_self_of_pos (z : Vec d) {r : ℝ} (hr : 0 < r) : z ∈ ball z r := by
  change euclideanNorm (z - z) < r
  rw [sub_self, euclideanNorm, euclideanSq, Real.sqrt_eq_zero'.mpr]
  · exact hr
  · simp [dot]

/-- **Lemma C.5 (Vitali covering lemma).** A family of balls `B_{r_α}(x_α)` in `ℝ^d` with radii
bounded by `R` has a countable, pairwise disjoint subfamily `{B_{r_β}(x_β)}_{β ∈ J}` such that
`⋃_α B_{r_α}(x_α) ⊆ ⋃_{β ∈ J} B_{5 r_β}(x_β)`. -/
theorem lemma_C_5 {ι : Type*} (x : ι → Vec d) (r : ι → ℝ) (R : ℝ) (hR : ∀ α, r α ≤ R) :
    ∃ J : Set ι, J.Countable ∧ J.PairwiseDisjoint (fun β => ball (x β) (r β)) ∧
      (⋃ α, ball (x α) (r α)) ⊆ ⋃ β ∈ J, ball (x β) (5 * r β) := by
  obtain ⟨J, hJt, hJdisj, hJcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun α => ball (x α) (r α)) {α | 0 < r α} r 2 (by norm_num)
    (fun α hα => le_of_lt hα) R (fun α _ => hR α)
    (fun α hα => ⟨x α, mem_ball_self_of_pos (x α) hα⟩)
  refine ⟨J, ?_, hJdisj, ?_⟩
  · exact hJdisj.countable_of_isOpen (fun β _ => isOpen_ball_vitali (x β) (r β))
      (fun β hβ => ⟨x β, mem_ball_self_of_pos (x β) (hJt hβ)⟩)
  · intro y hy
    obtain ⟨α, hyα⟩ := Set.mem_iUnion.mp hy
    have hrα : 0 < r α := by
      by_contra h
      have h0 : r α ≤ 0 := not_lt.mp h
      have := euclideanNorm_nonneg' (y - x α)
      change euclideanNorm (y - x α) < r α at hyα
      linarith
    obtain ⟨β, hβJ, ⟨w, hwα, hwβ⟩, hrαβ⟩ := hJcov α hrα
    refine Set.mem_biUnion hβJ ?_
    change euclideanNorm (y - x α) < r α at hyα
    change euclideanNorm (w - x α) < r α at hwα
    change euclideanNorm (w - x β) < r β at hwβ
    change euclideanNorm (y - x β) < 5 * r β
    have h1 := euclideanNorm_sub_le_add y (x α) (x β)
    have h2 := euclideanNorm_sub_le_add (x α) w (x β)
    have h3 := euclideanNorm_sub_comm' (x α) w
    linarith

end QSH
