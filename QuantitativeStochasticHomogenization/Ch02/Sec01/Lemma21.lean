import QuantitativeStochasticHomogenization.Ch02.Sec01.DualMaximizer

/-!
# Lemma 2.1: the variational formula for `J`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.1, Lemma 2.1: for every `p, q ∈ ℝ^d`,
`J(U, p, q) = sup_{w ∈ A(U)} ⨍_U (-½ ∇w·a∇w - p·a∇w + q·∇w)` (2.9), and the maximizer
`v(·, U, p, q)` is the difference between the maximizer of `μ*(U, q)` in (2.1) and the minimizer
`v(·, U, p) = ℓ_p + u` of `μ(U, p)` in (1.7) (`lemma_2_1`).

The book states the lemma for bounded Lipschitz domains. Here `U` is a bounded open convex
nonempty set: the existence of the maximizer of (2.1), which the book calls routine, comes from the
coarse-graining library for convex domains (`exists_isDualMaximizer`). The supremum is over
`A(U) ∩ H¹(U)` (`IsAHarmonic`), where the integrals of (2.9) are defined.

The proof is the book's: the identity (2.10) (`dualTrialEnergy_add_eq`) gives `≤` in (2.9) for
every `w ∈ A(U)` (`defectTrialEnergy_le_dualityDefect`) and the value `J(U, p, q)` at the
difference of the two optimizers (`IsDualMaximizer.isDefectMaximizer_sub`).
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

theorem bddAbove_defectSet (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) (hU0 : volume U ≠ 0) (p q : Vec d) :
    BddAbove {E : ℝ | ∃ (w : Vec d → ℝ) (h : Vec d → Vec d), IsAHarmonic a U w h ∧
      E = defectTrialEnergy a U p q h} :=
  ⟨dualityDefect a U p q, by
    rintro E ⟨w, h, hw, rfl⟩
    exact defectTrialEnergy_le_dualityDefect a hUb hU0 hw p q⟩

/-- **Existence of the maximizer `v(·, U, p, q)` of (2.9).** -/
theorem exists_isDefectMaximizer [NeZero d] (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty)
    (p q : Vec d) : ∃ (v : Vec d → ℝ) (g : Vec d → Vec d), IsDefectMaximizer a U p q v g := by
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  obtain ⟨uN, gN, hN⟩ := exists_isDualMaximizer a hUo hUb hUc hne q
  obtain ⟨u, g, hD⟩ := exists_isDirichletMinimizer a hUb hU0 p
  exact ⟨_, _, hN.isDefectMaximizer_sub hUb hU0 hD⟩

/-- **Lemma 2.1.** For a bounded open convex nonempty set `U ⊆ ℝ^d` and `p, q ∈ ℝ^d`:

* (2.9): `J(U, p, q) = sup_{w ∈ A(U)} ⨍_U (-½ ∇w·a∇w - p·a∇w + q·∇w)`, a supremum of a set
  bounded above;
* the maximizer of `μ*(U, q)` in (2.1) exists, and for every such maximizer `(u_*, g_*)` and every
  minimizer `v(·, U, p) = ℓ_p + u` of `μ(U, p)` in (1.7) (of gradient `p + g`), the difference
  `u_* - ℓ_p - u` is a maximizer of (2.9). -/
theorem lemma_2_1 [NeZero d] (a : CoefficientField d Λ) {U : Set (Vec d)} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty) (p q : Vec d) :
    (dualityDefect a U p q = sSup {E : ℝ | ∃ (w : Vec d → ℝ) (h : Vec d → Vec d),
        IsAHarmonic a U w h ∧ E = defectTrialEnergy a U p q h} ∧
      BddAbove {E : ℝ | ∃ (w : Vec d → ℝ) (h : Vec d → Vec d), IsAHarmonic a U w h ∧
        E = defectTrialEnergy a U p q h}) ∧
    (∃ (u : Vec d → ℝ) (g : Vec d → Vec d), IsDualMaximizer a U q u g) ∧
    ∀ (uN : Vec d → ℝ) (gN : Vec d → Vec d) (u : Vec d → ℝ) (g : Vec d → Vec d),
      IsDualMaximizer a U q uN gN → IsDirichletMinimizer a U p u g →
      IsDefectMaximizer a U p q (fun x => uN x - (dot p x + u x)) (fun x => gN x - (p + g x)) := by
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  have hbdd := bddAbove_defectSet a hUb hU0 p q
  obtain ⟨v, g, hM⟩ := exists_isDefectMaximizer a hUo hUb hUc hne p q
  refine ⟨⟨le_antisymm (le_csSup hbdd ⟨v, g, hM.1, hM.2.symm⟩) (csSup_le ⟨_, v, g, hM.1, rfl⟩
    fun E ⟨w, h, hw, hE⟩ => hE ▸ defectTrialEnergy_le_dualityDefect a hUb hU0 hw p q), hbdd⟩,
    exists_isDualMaximizer a hUo hUb hUc hne q, fun uN gN u g hN hD =>
      hN.isDefectMaximizer_sub hUb hU0 hD⟩

end QSH
