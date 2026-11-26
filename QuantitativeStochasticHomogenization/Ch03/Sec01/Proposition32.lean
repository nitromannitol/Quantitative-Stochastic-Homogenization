import QuantitativeStochasticHomogenization.Ch03.Sec01.HalfBallMeyers
import QuantitativeStochasticHomogenization.Ch03.Sec01.BallDirichlet
import QuantitativeStochasticHomogenization.AppB.TheoremB9

/-!
# Proposition 3.2: harmonic approximation

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 3.1, Proposition 3.2, for `d ≥ 2` and `Λ > 1`: there is `α(d, Λ) > 0` such that for every
`s ∈ (0, d)` there is `C(s, d, Λ)` with, for every law satisfying the assumptions, a random
variable `X_s ≥ 1` with `X_s ≤ O_s(C)`, (3.11), such that for almost every coefficient field, every
`R ≥ X_s` and every weak solution `u ∈ H¹(B_R)` of `-∇·(a∇u) = 0` in `B_R`, there is `ū ∈ H¹(B_{R/2})`
with `-∇·(ā∇ū) = 0` in `B_{R/2}` and
`‖u - ū‖_{L̲²(B_{R/2})} ≤ C R^{-α(d-s)} ‖u - (u)_{B_R}‖_{L̲²(B_R)}`, (3.13) (`proposition_3_2`).

The proof is the book's: the Meyers estimate (3.14) on `B_{R/2}` (`meyers_halfBall`), Theorem 2.18
on `B_{1/2} ⊆ □_0` for `x ↦ u(Rx)` with `ε = 1/R` and `(s + d)/2` in place of `s`, where `ū(R ·)` is
the solution of the homogenized Dirichlet problem with the boundary values of `u(R ·)`
(`exists_ballDirichlet`), and `X_s = max(X_{(s+d)/2}^{1/s}, 1)`. The exponent `2 + δ` of
Theorem 2.18 is the Meyers exponent, reduced to at most `2 + 1/d` so that `u ∈ L^{2+δ}(B_{R/2})`
by the Sobolev inequality (Theorem B.9). Departures from the book: `d ≥ 2` and `Λ > 1`, the
hypotheses of Theorem 2.18; the estimate holds for almost every coefficient field, as Theorem 2.18;
the norms are the normalized norms.
-/

open MeasureTheory Filter Set
open scoped ENNReal Pointwise

noncomputable section

namespace QSH

variable {d : ℕ}

theorem HasWeakGradient.const_mul' {U : Set (Vec d)} {u : Vec d → ℝ} {g : Vec d → Vec d}
    (h : HasWeakGradient U u g) (c : ℝ) :
    HasWeakGradient U (fun x => c * u x) (fun x => c • g x) := fun i => by
  obtain ⟨hu, hg, hint⟩ := h i
  refine ⟨(hu.smul c : _), (hg.smul c : _), fun φ hφ => ?_⟩
  have e1 : ∫ x in U, c * u x * coordinateDerivative i φ x =
      c * ∫ x in U, u x * coordinateDerivative i φ x := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  have e2 : ∫ x in U, (c • g x) i * φ x = c * ∫ x in U, g x i * φ x := by
    rw [← integral_const_mul]; congr 1; funext x; simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [e1, e2, hint φ hφ]
  ring

theorem HasWeakDivergence.const_smul' {U : Set (Vec d)} {F : Vec d → Vec d}
    (h : HasWeakDivergence U F (fun _ => 0)) (c : ℝ) :
    HasWeakDivergence U (fun x => c • F x) (fun _ => 0) := by
  obtain ⟨hF, h0, hint⟩ := h
  refine ⟨fun i => ((hF i).smul c : _), h0, fun φ hφ => ?_⟩
  have e : ∫ x in U, dot (c • F x) (gradient φ x) = c * ∫ x in U, dot (F x) (gradient φ x) := by
    rw [← integral_const_mul]; congr 1; funext x
    simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; ring_nf
  rw [e, hint φ hφ]
  simp

/-- `u ∈ H¹(B_r)` is in `L^{2+1/d}(B_r)`, by the Sobolev inequality (Theorem B.9) with exponent
`p = 2d/(d+1)`. -/
theorem memLp_two_add_inv_of_h1_ball (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r) {u : Vec d → ℝ}
    {g : Vec d → Vec d} (hu : MemLp u 2 (volume.restrict (ball 0 r)))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 r)))
    (hug : HasWeakGradient (ball 0 r) u g) :
    MemLp u (ENNReal.ofReal (2 + 1 / d)) (volume.restrict (ball 0 r)) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = 2 * d / (d + 1) := ⟨_, rfl⟩
  have hp1 : 1 ≤ p := by rw [hp, le_div_iff₀ (by linarith)]; linarith
  have hpd : p < d := by rw [hp, div_lt_iff₀ (by linarith)]; nlinarith
  have hp2 : ENNReal.ofReal p ≤ 2 := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
    exact ENNReal.ofReal_le_ofReal (by rw [hp, div_le_iff₀ (by linarith)]; linarith)
  have hq : 2 + 1 / (d : ℝ) ≤ d * p / (d - p) := by
    have e : d * p / (d - p) = 2 * d / (d - 1) := by
      rw [hp]; field_simp; ring
    have h1 : (2 : ℝ) + 1 / d = (2 * d + 1) / d := by field_simp
    rw [e, h1, div_le_div_iff₀ hd0 (by linarith)]
    nlinarith
  have hU0 : volume (ball (0 : Vec d) r) ≠ 0 := volume_ball_ne_zero' 0 hr
  have hUt : volume (ball (0 : Vec d) r) ≠ ⊤ := volume_ball_ne_top' 0 r
  have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) r)) := isFiniteMeasure_restrict.mpr hUt
  obtain ⟨C, hC, hB⟩ := theorem_B_9_one (d := d) p hp1 hpd
  have hW : IsW1p (ball 0 r) (ENNReal.ofReal p) u g :=
    ⟨hu.mono_exponent hp2, (memLp_pi_iff.2 hg).mono_exponent hp2, hug⟩
  have h := (hB 0 r hr u g).1 hW
  have hfin : ENNReal.ofReal (C * r) * PDE.eLpMeanNormOn (ball 0 r) (ENNReal.ofReal p)
      (fun x => euclideanNorm (g x)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (eLpMeanNormOn_ne_top_of_memLp hU0 hUt
      ((memLp_euclideanNorm_of_coord hg).mono_exponent hp2))
  obtain ⟨w, hw⟩ := iInf_lt_iff.1 (lt_of_le_of_lt h (lt_top_iff_ne_top.2 hfin))
  have hmw : MemLp (fun x => u x - w) (ENNReal.ofReal (d * p / (d - p)))
      (volume.restrict (ball 0 r)) := memLp_of_eLpMeanNormOn_ne_top hU0 hUt hw.ne
  have hmu : MemLp u (ENNReal.ofReal (d * p / (d - p))) (volume.restrict (ball 0 r)) := by
    have e : (fun x => u x - w) + (fun _ => w) = u := by funext x; simp
    rw [← e]; exact hmw.add (memLp_const w)
  exact hmu.mono_exponent (ENNReal.ofReal_le_ofReal hq)

end QSH
