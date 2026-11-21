import Mathlib

/-!
# Perturbation of the supremum of a concave quadratic energy

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 4.22, the principle of its proof: "if we compute the minimum of a uniformly convex function
on a finite-dimensional subspace and then perturb this subspace by `h` and recompute the minimum,
we find that the minimum is perturbed by at most `O(h)`".

For an energy `E(g) = -½ B(g, g) + ℓ(g)` on a normed space, with `B` symmetric, bounded by `Λ`
and bounded below by the square of the norm, and `ℓ` bounded by `L`, the near maximizers of `E`
over a set containing `0` have norm at most `2L + 1`. Consequently, if every element of norm at
most `2L + 1` of each of two sets containing `0` is within `η` of the other set, the suprema of
`E` over the two sets differ by at most `(Λ (2(2L + 1) + η) / 2 + L) η`.
-/

noncomputable section

namespace QSH

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The structure of a concave quadratic energy `E(g) = -½ B(g, g) + ℓ(g)`. -/
structure IsConcaveEnergy (B : H → H → ℝ) (ℓ : H → ℝ) (Λ L : ℝ) : Prop where
  add_left : ∀ g g' h, B (g + g') h = B g h + B g' h
  smul_left : ∀ (c : ℝ) g h, B (c • g) h = c * B g h
  symm : ∀ g h, B g h = B h g
  coercive : ∀ g, ‖g‖ ^ 2 ≤ B g g
  bound : ∀ g h, |B g h| ≤ Λ * (‖g‖ * ‖h‖)
  linear_sub : ∀ g h, ℓ g - ℓ h = ℓ (g - h)
  linear_bound : ∀ g, |ℓ g| ≤ L * ‖g‖
  L_nonneg : 0 ≤ L
  Λ_nonneg : 0 ≤ Λ

namespace IsConcaveEnergy

variable {B : H → H → ℝ} {ℓ : H → ℝ} {Λ L : ℝ}

theorem sub_left (hE : IsConcaveEnergy B ℓ Λ L) (g g' h : H) :
    B (g - g') h = B g h - B g' h := by
  rw [sub_eq_add_neg, hE.add_left, ← neg_one_smul ℝ g', hE.smul_left]; ring

theorem energy_le (hE : IsConcaveEnergy B ℓ Λ L) (g : H) :
    -(1 / 2 : ℝ) * B g g + ℓ g ≤ L ^ 2 / 2 := by
  have h1 := hE.coercive g
  have h2 := (le_abs_self _).trans (hE.linear_bound g)
  nlinarith [sq_nonneg (‖g‖ - L), norm_nonneg g]

/-- Near maximizers have bounded norm. -/
theorem norm_le_of_energy_ge (hE : IsConcaveEnergy B ℓ Λ L) {g : H}
    (hg : -(1 / 2 : ℝ) ≤ -(1 / 2 : ℝ) * B g g + ℓ g) : ‖g‖ ≤ 2 * L + 1 := by
  have h1 := hE.coercive g
  have h2 := (le_abs_self _).trans (hE.linear_bound g)
  have hL := hE.L_nonneg
  by_contra hcon
  push Not at hcon
  have hn : 0 ≤ ‖g‖ := norm_nonneg g
  nlinarith [mul_le_mul_of_nonneg_left hcon.le hn]

/-- The Lipschitz estimate of the energy. -/
theorem abs_energy_sub_le (hE : IsConcaveEnergy B ℓ Λ L) (g h : H) :
    |(-(1 / 2 : ℝ) * B g g + ℓ g) - (-(1 / 2 : ℝ) * B h h + ℓ h)| ≤
      (Λ * (‖g‖ + ‖h‖) / 2 + L) * ‖g - h‖ := by
  have hB : B g g - B h h = B (g - h) (g + h) := by
    have e1 : B (g - h) (g + h) = B g (g + h) - B h (g + h) := hE.sub_left g h (g + h)
    have e2 : ∀ x, B x (g + h) = B x g + B x h := fun x => by
      rw [hE.symm x (g + h), hE.add_left, hE.symm g x, hE.symm h x]
    rw [e1, e2, e2, hE.symm h g]
    ring
  have hrw : (-(1 / 2 : ℝ) * B g g + ℓ g) - (-(1 / 2 : ℝ) * B h h + ℓ h) =
      -(1 / 2 : ℝ) * B (g - h) (g + h) + ℓ (g - h) := by
    rw [← hB, ← hE.linear_sub]; ring
  rw [hrw]
  have h1 := hE.bound (g - h) (g + h)
  have h2 := hE.linear_bound (g - h)
  have h3 : ‖g + h‖ ≤ ‖g‖ + ‖h‖ := norm_add_le g h
  have hΛ := hE.Λ_nonneg
  have hd := norm_nonneg (g - h)
  have h4 : Λ * (‖g - h‖ * ‖g + h‖) ≤ Λ * (‖g - h‖ * (‖g‖ + ‖h‖)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hd) hΛ
  calc |-(1 / 2 : ℝ) * B (g - h) (g + h) + ℓ (g - h)|
      ≤ |-(1 / 2 : ℝ) * B (g - h) (g + h)| + |ℓ (g - h)| := abs_add_le _ _
    _ = (1 / 2 : ℝ) * |B (g - h) (g + h)| + |ℓ (g - h)| := by
        rw [abs_mul]; norm_num
    _ ≤ (Λ * (‖g‖ + ‖h‖) / 2 + L) * ‖g - h‖ := by nlinarith

theorem map_zero (hE : IsConcaveEnergy B ℓ Λ L) : -(1 / 2 : ℝ) * B 0 0 + ℓ 0 = 0 := by
  have h1 : B 0 0 = 0 := by
    have := hE.smul_left 0 0 0
    simpa using this
  have h2 : ℓ 0 = 0 := by
    have := hE.linear_sub 0 0
    simpa using this.symm
  rw [h1, h2]; ring

/-- One side of the perturbation estimate. -/
theorem sSup_le_sSup_add (hE : IsConcaveEnergy B ℓ Λ L) {A V : Set H} (hA0 : (0 : H) ∈ A)
    {η : ℝ} (hη : 0 ≤ η)
    (hAV : ∀ g ∈ A, ‖g‖ ≤ 2 * L + 1 → ∃ h ∈ V, ‖g - h‖ ≤ η) :
    sSup ((fun g => -(1 / 2 : ℝ) * B g g + ℓ g) '' A) ≤
      sSup ((fun g => -(1 / 2 : ℝ) * B g g + ℓ g) '' V) +
        (Λ * (2 * (2 * L + 1) + η) / 2 + L) * η := by
  set E : H → ℝ := fun g => -(1 / 2 : ℝ) * B g g + ℓ g
  have hbdd : ∀ S : Set H, BddAbove (E '' S) := fun S =>
    ⟨L ^ 2 / 2, by rintro _ ⟨g, -, rfl⟩; exact hE.energy_le g⟩
  have hneA : (E '' A).Nonempty := ⟨E 0, 0, hA0, rfl⟩
  have hE0 : E 0 = 0 := hE.map_zero
  have hsupA : 0 ≤ sSup (E '' A) := hE0 ▸ le_csSup (hbdd A) ⟨0, hA0, rfl⟩
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set ε' := min ε (1 / 2)
  have hε' : 0 < ε' := lt_min hε (by norm_num)
  obtain ⟨_, ⟨g, hgA, rfl⟩, hg⟩ := exists_lt_of_lt_csSup hneA
    (show sSup (E '' A) - ε' < sSup (E '' A) by linarith)
  have hgE : -(1 / 2 : ℝ) ≤ E g := by
    have : ε' ≤ 1 / 2 := min_le_right _ _
    linarith
  have hgn := hE.norm_le_of_energy_ge hgE
  obtain ⟨h, hhV, hgh⟩ := hAV g hgA hgn
  have hhn : ‖h‖ ≤ 2 * L + 1 + η := by
    have := norm_sub_norm_le h g
    rw [norm_sub_rev] at hgh
    have h' : ‖h‖ ≤ ‖g‖ + ‖h - g‖ := by
      have := norm_add_le g (h - g)
      rwa [add_sub_cancel] at this
    linarith
  have hlip : |E g - E h| ≤ (Λ * (‖g‖ + ‖h‖) / 2 + L) * ‖g - h‖ := hE.abs_energy_sub_le g h
  have hK : (Λ * (‖g‖ + ‖h‖) / 2 + L) * ‖g - h‖ ≤ (Λ * (2 * (2 * L + 1) + η) / 2 + L) * η := by
    have hΛ := hE.Λ_nonneg
    have hL := hE.L_nonneg
    apply mul_le_mul _ hgh (norm_nonneg _) (by positivity)
    have : ‖g‖ + ‖h‖ ≤ 2 * (2 * L + 1) + η := by linarith
    have := mul_le_mul_of_nonneg_left this hΛ
    linarith
  have hEh : E h ≤ sSup (E '' V) := le_csSup (hbdd V) ⟨h, hhV, rfl⟩
  have habs := (abs_le.1 (hlip.trans hK)).2
  have : ε' ≤ ε := min_le_left _ _
  show sSup (E '' A) < _
  linarith

/-- **Lemma 4.22, deterministic core**: the suprema of a concave quadratic energy over two sets
containing `0`, each of which approximates the bounded part of the other within `η`, differ by
`O(η)`. -/
theorem abs_sSup_sub_sSup_le (hE : IsConcaveEnergy B ℓ Λ L) {A V : Set H} (hA0 : (0 : H) ∈ A)
    (hV0 : (0 : H) ∈ V) {η : ℝ} (hη : 0 ≤ η)
    (hAV : ∀ g ∈ A, ‖g‖ ≤ 2 * L + 1 → ∃ h ∈ V, ‖g - h‖ ≤ η)
    (hVA : ∀ h ∈ V, ‖h‖ ≤ 2 * L + 1 → ∃ g ∈ A, ‖h - g‖ ≤ η) :
    |sSup ((fun g => -(1 / 2 : ℝ) * B g g + ℓ g) '' A) -
        sSup ((fun g => -(1 / 2 : ℝ) * B g g + ℓ g) '' V)| ≤
      (Λ * (2 * (2 * L + 1) + η) / 2 + L) * η := by
  rw [abs_sub_le_iff]
  constructor
  · have := hE.sSup_le_sSup_add hA0 hη hAV
    linarith
  · have := hE.sSup_le_sSup_add hV0 hη hVA
    linarith

end IsConcaveEnergy

end QSH
