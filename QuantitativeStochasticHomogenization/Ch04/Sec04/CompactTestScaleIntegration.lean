import Mathlib

/-!
# Integration in the scale

Two elementary facts for the integration in the scale of the finite-ball estimate with compact
tests of the proof of Lemma 4.21 in Armstrong–Kuusi–Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*: a function whose derivative is dominated by the
derivative of `g` on `[a, b]` changes by at most `g b - g a`, and the power `t^e / e` is an
antiderivative of `t^{e-1}` for `e ≠ 0`, `t > 0`.
-/

noncomputable section

namespace QSH

/-- **Comparison with a majorant of the derivative**: if `|f'| ≤ g'` on `[a, b]`, then
`|f b - f a| ≤ g b - g a`. -/
theorem abs_sub_le_of_abs_deriv_le {f f' g g' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hg : ∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t)
    (hle : ∀ t ∈ Set.Icc a b, |f' t| ≤ g' t) : |f b - f a| ≤ g b - g a := by
  have hmono : ∀ σ : ℝ, |σ| ≤ 1 → MonotoneOn (fun t => g t - σ * f t) (Set.Icc a b) := by
    intro σ hσ
    have hd : ∀ t ∈ Set.Icc a b, HasDerivAt (fun t => g t - σ * f t) (g' t - σ * f' t) t :=
      fun t ht => (hg t ht).sub ((hf t ht).const_mul σ)
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => ?_)
    rw [(hd t (interior_subset ht)).deriv]
    have h1 := hle t (interior_subset ht)
    have h2 : σ * f' t ≤ |f' t| := by
      calc σ * f' t ≤ |σ * f' t| := le_abs_self _
        _ = |σ| * |f' t| := abs_mul _ _
        _ ≤ 1 * |f' t| := mul_le_mul_of_nonneg_right hσ (abs_nonneg _)
        _ = |f' t| := one_mul _
    linarith
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have h1 := hmono 1 (by norm_num) ha hb hab
  have h2 := hmono (-1) (by norm_num) ha hb hab
  simp only [one_mul, neg_mul, sub_neg_eq_add] at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- The power `t^e / e` is an antiderivative of `t^{e-1}`. -/
theorem hasDerivAt_rpow_div {e t : ℝ} (he : e ≠ 0) (ht : 0 < t) :
    HasDerivAt (fun t => t ^ e / e) (t ^ (e - 1)) t := by
  have h := (Real.hasDerivAt_rpow_const (p := e) (Or.inl ht.ne')).div_const e
  convert h using 1
  field_simp

end QSH
