import QuantitativeStochasticHomogenization.Ch02.Sec01.Lemma22
import QuantitativeStochasticHomogenization.Ch03.Sec03.WeakGradientH10

/-!
# A bound of `J(U, p, q)` by a primal and a dual trial field

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.1, toward Theorem 2.4. For a primal trial `E = p + h_E` with `h_E` the gradient of a
function of `H¹₀(U)` and a dual trial `F ∈ L²(U)` with `∫_U (F - q)·∇w = 0` for every
`w ∈ A(U) ∩ H¹(U)`,
`J(U, p, q) ≤ ½ ⨍_U |aE - F|²` (`dualityDefect_le_of_trials`).

By (2.9), `J(U, p, q)` is the supremum over `w ∈ A(U)` of `⨍_U (-½ ∇w·a∇w - p·a∇w + q·∇w)`; in it
`q·∇w` may be replaced by `F·∇w`, and `p·a∇w` by `aE·∇w`, since `∫_U ∇w·a h_E = 0`
(`IsAHarmonic.setIntegral_dot_eq_zero`); then `-½ ∇w·a∇w + (F - aE)·∇w ≤ ½ |F - aE|²` pointwise,
by `a ≥ Id`. This is the inequality `2J + ‖∇w‖² ≤ ‖aE - F‖²_{a⁻¹}` of the finite-cube argument for
(2.21) from first-order correctors, with `a⁻¹ ≤ Id`.

The dual trial `F = q + div Θ` (row divergence) of a skew family `Θ` of functions of `H¹₀(U)` is
admissible (`dualityDefect_le_of_skew`), by the skew identity `Σⱼₖ ∫_U ∂ⱼw ∂ₖΘⱼₖ = 0`
(`sum_integral_grad_mul_skew_h10`).
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

theorem integrable_dot_of_memLp {U : Set (Vec d)} {F G : Vec d → Vec d}
    (hF : MemLp F 2 (volume.restrict U)) (hG : MemLp G 2 (volume.restrict U)) :
    Integrable (fun x => dot (F x) (G x)) (volume.restrict U) := by
  simp only [dot]
  refine integrable_finsetSum _ fun i _ => ?_
  exact (L2.integrable_inner (𝕜 := ℝ) ((hF.eval i).toLp _) ((hG.eval i).toLp _)).congr (by
    filter_upwards [(hF.eval i).coeFn_toLp, (hG.eval i).coeFn_toLp] with x h1 h2
    rw [h1, h2]
    simp [mul_comm])

theorem memLp_mulVec_of_memLp (a : CoefficientField d Λ) {U : Set (Vec d)} {G : Vec d → Vec d}
    (hG : MemLp G 2 (volume.restrict U)) :
    MemLp (fun x => (a x).mulVec (G x)) 2 (volume.restrict U) :=
  memLp_pi_iff.mpr fun i => memLp_coefficient_mulVec_apply a hG i

/-- **The bound of `J` by a primal and a dual trial**: for `u ∈ H¹₀(U)` of weak gradient `h_E` and
`F ∈ L²(U)` with `∫_U (F - q)·∇w = 0` for every `w ∈ A(U) ∩ H¹(U)`,
`J(U, p, q) ≤ ½ ⨍_U |a(p + h_E) - F|²`. -/
theorem dualityDefect_le_of_trials [NeZero d] (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty)
    (p q : Vec d) {u : Vec d → ℝ} {hE : Vec d → Vec d} (hu : H01 U u hE) {F : Vec d → Vec d}
    (hF : MemLp F 2 (volume.restrict U))
    (horth : ∀ (w : Vec d → ℝ) (h : Vec d → Vec d), IsAHarmonic a U w h →
      ∫ x in U, dot (F x - q) (h x) = 0) :
    dualityDefect a U p q ≤
      (1 / 2 : ℝ) * ⨍ x in U, euclideanSq ((a x).mulVec (p + hE x) - F x) := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  have := isFiniteMeasure_restrict.mpr hU
  have hV : 0 < volume.real U := ENNReal.toReal_pos hU0 hU
  set X : Vec d → Vec d := fun x => (a x).mulVec (p + hE x) - F x with hX
  have hpE : MemLp (fun x => p + hE x) 2 (volume.restrict U) := (memLp_const p).add hu.2.1
  have hXm : MemLp X 2 (volume.restrict U) := (memLp_mulVec_of_memLp a hpE).sub hF
  rw [(lemma_2_1 a hUo hUb hUc hne p q).1.1]
  refine csSup_le ⟨_, _, _, ⟨H1_zero U, ?_⟩, rfl⟩ ?_
  · refine hasWeakDivergence_of_setIntegral_dot_eq_zero a hU MemLp.zero fun _ _ _ => ?_
    simp [dot]
  rintro E ⟨w, h, hw, rfl⟩
  have hh := hw.1.2.1
  -- `∫ q·h = ∫ F·h`
  have e1 : ∫ x in U, dot q (h x) = ∫ x in U, dot (F x) (h x) := by
    have h0 := horth w h hw
    have i1 := integrable_dot_of_memLp hF hh
    have i2 := integrable_dot_left_of_memLp hU hh q
    have e : (fun x => dot (F x - q) (h x)) = fun x => dot (F x) (h x) - dot q (h x) := by
      funext x
      simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    rw [e, integral_sub i1 i2] at h0
    linarith
  -- `∫ p·ah = ∫ a(p + h_E)·h`
  have e2 : ∫ x in U, dot p ((a x).mulVec (h x)) =
      ∫ x in U, dot ((a x).mulVec (p + hE x)) (h x) := by
    have h0 := hw.setIntegral_dot_eq_zero hu
    have i1 := integrable_dot_mulVec_const_left a hU hh p
    have i2 := integrable_dot_mulVec_of_memLp a hu.2.1 hh
    have e : (fun x => dot ((a x).mulVec (p + hE x)) (h x)) = fun x =>
        dot p ((a x).mulVec (h x)) + dot (hE x) ((a x).mulVec (h x)) := by
      funext x
      rw [dot_comm', ← dot_mulVec_comm_of_symm (a.symmetric x)]
      simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    rw [e, integral_add i1 i2, h0, add_zero]
  -- the pointwise bound
  have iA := (integrable_dot_mulVec a U hh).const_mul (-(1 / 2 : ℝ))
  have iX : Integrable (fun x => dot (X x) (h x)) (volume.restrict U) := integrable_dot_of_memLp hXm hh
  have iS := (integrable_euclideanSq_of_memLp hXm).const_mul (1 / 2 : ℝ)
  have key : ∫ x in U, (-(1 / 2 : ℝ) * dot (h x) ((a x).mulVec (h x)) -
      dot p ((a x).mulVec (h x)) + dot q (h x)) =
      ∫ x in U, (-(1 / 2 : ℝ) * dot (h x) ((a x).mulVec (h x)) - dot (X x) (h x)) := by
    have i2 := integrable_dot_mulVec_const_left a hU hh p
    have i3 := integrable_dot_left_of_memLp hU hh q
    have i12 : Integrable (fun x => -(1 / 2 : ℝ) * dot (h x) ((a x).mulVec (h x)) -
        dot p ((a x).mulVec (h x))) (volume.restrict U) := iA.sub i2
    have iF := integrable_dot_of_memLp hF hh
    have iAE := integrable_dot_of_memLp (memLp_mulVec_of_memLp a hpE) hh
    have eX : (fun x => dot (X x) (h x)) = fun x =>
        dot ((a x).mulVec (p + hE x)) (h x) - dot (F x) (h x) := by
      funext x
      simp only [hX, dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    rw [integral_add i12 i3, integral_sub iA i2, integral_sub iA iX, eX, integral_sub iAE iF, e1, e2]
    ring
  have hle : ∫ x in U, (-(1 / 2 : ℝ) * dot (h x) ((a x).mulVec (h x)) - dot (X x) (h x)) ≤
      ∫ x in U, (1 / 2 : ℝ) * euclideanSq (X x) := by
    refine integral_mono (iA.sub iX) iS fun x => ?_
    have h1 := (a.elliptic x (h x)).1
    have h2 := two_mul_dot_le (-X x) (h x)
    have e3 : dot (-X x) (h x) = -dot (X x) (h x) := by
      simp only [dot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    have e4 : euclideanSq (-X x) = euclideanSq (X x) := by
      simp only [euclideanSq, dot, Pi.neg_apply, neg_mul_neg]
    rw [e3, e4] at h2
    simp only
    linarith
  rw [defectTrialEnergy, setAverage_eq, smul_eq_mul, key, setAverage_eq, smul_eq_mul]
  have h3 := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hV.le)
  rw [integral_const_mul] at h3
  linarith


/-- **The bound of `J` by a primal trial and the divergence of a skew family**: for
`u ∈ H¹₀(U)` of weak gradient `h_E` and functions `Θⱼₖ ∈ H¹₀(U)` with `∇Θₖⱼ = -∇Θⱼₖ`,
`J(U, p, q) ≤ ½ ⨍_U |a(p + h_E) - (q + div Θ)|²`, `(div Θ)ⱼ = Σₖ ∂ₖΘⱼₖ`. -/
theorem dualityDefect_le_of_skew [NeZero d] (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty)
    (p q : Vec d) {u : Vec d → ℝ} {hE : Vec d → Vec d} (hu : H01 U u hE)
    (Θ : Fin d → Fin d → PDE.H10Function U)
    (hskew : ∀ j k x, (Θ k j).toH1Function.grad x = -(Θ j k).toH1Function.grad x) :
    dualityDefect a U p q ≤ (1 / 2 : ℝ) * ⨍ x in U, euclideanSq ((a x).mulVec (p + hE x) -
      (q + fun j => ∑ k, (Θ j k).toH1Function.grad x k)) := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have := isFiniteMeasure_restrict.mpr hU
  have hΘ : ∀ j k, MemLp (fun x => (Θ j k).toH1Function.grad x k) 2 (volume.restrict U) :=
    fun j k => (Θ j k).toH1Function.gradMemL2 k
  have hF : MemLp (fun x => q + fun j => ∑ k, (Θ j k).toH1Function.grad x k) 2
      (volume.restrict U) :=
    (memLp_const q).add (memLp_pi_iff.mpr fun j => memLp_finsetSum _ fun k _ => hΘ j k)
  refine dualityDefect_le_of_trials a hUo hUb hUc hne p q hu hF fun w h hw => ?_
  have hh : ∀ i, MemLp (fun x => h x i) 2 (volume.restrict U) := fun i => hw.1.2.1.eval i
  have hz := sum_integral_grad_mul_skew_h10 hh hw.1.2.2 Θ hskew
  have hint : ∀ j k, Integrable (fun x => h x j * (Θ j k).toH1Function.grad x k)
      (volume.restrict U) := fun j k => integrable_mul_of_memLp_two (hh j) (hΘ j k)
  have e : (fun x => dot ((q + fun j => ∑ k, (Θ j k).toH1Function.grad x k) - q) (h x)) =
      fun x => ∑ j, ∑ k, h x j * (Θ j k).toH1Function.grad x k := by
    funext x
    simp only [dot, add_sub_cancel_left, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [e, integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint j k]
  rw [← hz]
  exact Finset.sum_congr rfl fun j _ => integral_finsetSum _ fun k _ => hint j k

end QSH
