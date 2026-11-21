import QuantitativeStochasticHomogenization.Ch04.Sec05.FluctuationPieces

/-!
# Sums of blocks over separated cubes in the proof of Proposition 4.12

Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, Section 4.5, Step 2. Under the induction hypothesis `A(R₁, C)` (`BlockBound`):

* the blocks over the `2^d` cubes of side `R/2` at mutual distance `R'` are independent, since the
  neighbourhoods of radius `r₁^{1+δ}` of these cubes are at distance larger than one; by Lemma A.11
  with equal scales their sum is `𝒪_s(C R^{-β})` after normalization by `R^{-d}`, because
  `β ≤ d/2` (`centeredOsBound_sum_bigCubes`);
* the blocks over cells of side `R'` with lattice centers, coloured by residues modulo `4`, have a
  sum `𝒪_s((2 · 4^d)^{1/2} |T|^{1/2} R'^{d-β} C)` (`centeredOsBound_sum_cells`, Lemma A.12).
-/

open MeasureTheory ProbabilityTheory

namespace QSH

variable {d : ℕ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {F : Set (Vec d) → MeasurableSpace Ω}
  {s δ α : ℝ}

theorem centeredOsBound_of_rpow_neg_mul {V : Ω → ℝ} {R θ : ℝ} (hR : 0 < R)
    (h : CenteredOsBound P (fun a => R ^ (-(d : ℝ)) * V a) s θ) :
    CenteredOsBound P V s (R ^ d * θ) := by
  have h2 := h.const_mul (pow_pos hR d)
  convert h2 using 1
  funext a
  rw [← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hR, add_neg_cancel, Real.rpow_zero,
    one_mul]

/-- The `2^d` large cubes of side `R/2` around `z`. -/
noncomputable def bigCubeAt (z : Vec d) (R R' : ℝ) (σ : Fin d → Bool) : Set (Vec d) :=
  closedCube (z + bigCubeCenter R R' σ) (R / 2)

theorem sub_mem_bigCube_of_mem_bigCubeAt {z : Vec d} {R R' : ℝ} {σ : Fin d → Bool} {y : Vec d}
    (hy : y ∈ bigCubeAt z R R' σ) : y - z ∈ bigCube R R' σ := by
  intro i
  have := hy i
  simp only [Pi.sub_apply, Pi.add_apply] at this ⊢
  rwa [show y i - z i - bigCubeCenter R R' σ i = y i - (z i + bigCubeCenter R R' σ i) by ring]

theorem scale_bigCubes_le {R C β : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hβ : β ≤ (d : ℝ) / 2) :
    R ^ (-(d : ℝ)) * (Real.sqrt ((Fintype.card (Fin d → Bool) : ℕ) : ℝ) *
      ((R / 2) ^ d * (C * (R / 2) ^ (-β)))) ≤ C * R ^ (-β) := by
  have hcard : ((Fintype.card (Fin d → Bool) : ℕ) : ℝ) = (2 : ℝ) ^ (d : ℝ) := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Real.rpow_natCast]
    push_cast
    ring
  have hsqrt : Real.sqrt ((2 : ℝ) ^ (d : ℝ)) = (2 : ℝ) ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
    ring_nf
  have h2 : (0 : ℝ) < 2 := two_pos
  have e1 : (R / 2) ^ d = R ^ (d : ℝ) * (2 : ℝ) ^ (-(d : ℝ)) := by
    rw [← Real.rpow_natCast, Real.div_rpow hR.le h2.le, Real.rpow_neg h2.le, div_eq_mul_inv]
  have e2 : (R / 2) ^ (-β) = R ^ (-β) * (2 : ℝ) ^ β := by
    rw [Real.div_rpow hR.le h2.le, Real.rpow_neg h2.le, div_eq_mul_inv, inv_inv]
  rw [hcard, hsqrt, e1, e2]
  have hk : (2 : ℝ) ^ ((d : ℝ) / 2) * (2 : ℝ) ^ (-(d : ℝ)) * (2 : ℝ) ^ β ≤ 1 := by
    rw [← Real.rpow_add h2, ← Real.rpow_add h2]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hRd : R ^ (-(d : ℝ)) * R ^ (d : ℝ) = 1 := by
    rw [← Real.rpow_add hR, neg_add_cancel, Real.rpow_zero]
  have hCR : 0 ≤ C * R ^ (-β) := mul_nonneg hC (Real.rpow_nonneg hR.le _)
  calc R ^ (-(d : ℝ)) * ((2 : ℝ) ^ ((d : ℝ) / 2) *
        (R ^ (d : ℝ) * (2 : ℝ) ^ (-(d : ℝ)) * (C * (R ^ (-β) * (2 : ℝ) ^ β))))
      = (R ^ (-(d : ℝ)) * R ^ (d : ℝ)) * ((2 : ℝ) ^ ((d : ℝ) / 2) * (2 : ℝ) ^ (-(d : ℝ)) *
          (2 : ℝ) ^ β) * (C * R ^ (-β)) := by ring
    _ ≤ 1 * 1 * (C * R ^ (-β)) := by
        rw [hRd]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk zero_le_one) hCR
    _ = C * R ^ (-β) := by ring

/-- **The `2^d` large cubes** (Step 2 of the proof of Proposition 4.12). -/
theorem centeredOsBound_sum_bigCubes [IsProbabilityMeasure P] (hF : HasUnitRange P F)
    (hmono : Monotone F) (X : CenteredLocalFields P F s δ α) {η₁ η₂ β R₁ C : ℝ}
    (hA : BlockBound X η₁ η₂ β R₁ C) (hβ : β ≤ (d : ℝ) / 2) (hC : 0 ≤ C) {R R' r₁ : ℝ}
    (hR2 : 1 ≤ R / 2) (hRR₁ : R / 2 ≤ R₁) (hr₁ : 1 ≤ r₁) (hr₁lo : (R / 2) ^ η₁ ≤ r₁)
    (hr₁hi : r₁ ≤ (R / 2) ^ η₂) (hsep : 1 < R' - 2 * r₁ ^ (1 + δ)) (z : Vec d)
    {g : Vec d → ℝ} (hg : Measurable g) (hg1 : ∀ y, |g y| ≤ 1) :
    CenteredOsBound P (fun a => R ^ (-(d : ℝ)) * ∑ σ : Fin d → Bool,
      ∫ y, (bigCubeAt z R R' σ).indicator g y * X.field r₁ a y) s (C * R ^ (-β)) := by
  classical
  have hR0 : 0 < R := by linarith
  set V : (Fin d → Bool) → Ω → ℝ :=
    fun σ a => ∫ y, (bigCubeAt z R R' σ).indicator g y * X.field r₁ a y with hVdef
  have hQm : ∀ σ, MeasurableSet (bigCubeAt z R R' σ) := fun σ => measurableSet_closedCube _ _
  have hgQ : ∀ σ, Measurable ((bigCubeAt z R R' σ).indicator g) := fun σ => hg.indicator (hQm σ)
  have hgQ1 : ∀ σ y, |(bigCubeAt z R R' σ).indicator g y| ≤ 1 := by
    intro σ y
    by_cases hy : y ∈ bigCubeAt z R R' σ
    · rw [Set.indicator_of_mem hy]; exact hg1 y
    · rw [Set.indicator_of_notMem hy, abs_zero]; exact zero_le_one
  have hgQz : ∀ σ y, y ∉ bigCubeAt z R R' σ → (bigCubeAt z R R' σ).indicator g y = 0 :=
    fun σ y hy => Set.indicator_of_notMem hy _
  have hV : ∀ σ, CenteredOsBound P (V σ) s ((R / 2) ^ d * (C * (R / 2) ^ (-β))) := by
    intro σ
    exact centeredOsBound_of_rpow_neg_mul (by linarith)
      (hA (R / 2) hR2 hRR₁ r₁ hr₁lo hr₁hi _ _ (hgQ σ) (hgQ1 σ) (hgQz σ))
  have hloc : ∀ σ, Measurable[F (euclideanThickening (r₁ ^ (1 + δ)) (bigCubeAt z R R' σ))]
      (V σ) := fun σ =>
    measurable_integral_mul_local (X.isLocal r₁ hr₁ _ (hQm σ)) (hgQ σ) (hgQz σ)
  have hsepσ : Pairwise fun σ σ' : Fin d → Bool =>
      SeparatedByUnit (euclideanThickening (r₁ ^ (1 + δ)) (bigCubeAt z R R' σ))
        (euclideanThickening (r₁ ^ (1 + δ)) (bigCubeAt z R R' σ')) := by
    intro σ σ' hσσ
    refine separatedByUnit_euclideanThickening hsep fun u hu w hw => ?_
    obtain ⟨i, hi⟩ := exists_le_abs_sub_of_mem_bigCube hσσ (sub_mem_bigCube_of_mem_bigCubeAt hu)
      (sub_mem_bigCube_of_mem_bigCubeAt hw)
    refine ⟨i, ?_⟩
    simpa only [Pi.sub_apply, sub_sub_sub_cancel_right] using hi
  have hind : iIndepFun V P :=
    iIndepFun_of_separated hF hmono (fun σ => measurableSet_euclideanThickening _ _) hsepσ hloc
  have hsum := centeredOsBound_sum_of_eq_scale hind hV
  have h2 := hsum.const_mul (Real.rpow_pos_of_pos hR0 (-(d : ℝ)))
  exact h2.mono_scale (scale_bigCubes_le hR0 hC hβ)

/-- **The cells of side `R'`** (Step 2 of the proof of Proposition 4.12, Lemma A.12): blocks with
weights supported in the cells `closedCube (z + R' k) R'`, `k ∈ T`, have a sum
`𝒪_s((2 · 4^d)^{1/2} |T|^{1/2} R'^d C R'^{-β})`. -/
theorem centeredOsBound_sum_cells [IsProbabilityMeasure P] (hF : HasUnitRange P F)
    (hmono : Monotone F) (X : CenteredLocalFields P F s δ α) {η₁ η₂ β R₁ C : ℝ}
    (hA : BlockBound X η₁ η₂ β R₁ C) (hC : 0 ≤ C) {R' r₁ : ℝ} (hR'1 : 1 ≤ R') (hR'R₁ : R' ≤ R₁)
    (hr₁ : 1 ≤ r₁) (hr₁lo : R' ^ η₁ ≤ r₁) (hr₁hi : r₁ ≤ R' ^ η₂) (hρ : r₁ ^ (1 + δ) ≤ R' / 2)
    (z : Vec d) (T : Finset (LatticeIndex d)) (hT : T.Nonempty) {g : LatticeIndex d → Vec d → ℝ}
    (hg : ∀ k, Measurable (g k)) (hg1 : ∀ k y, |g k y| ≤ 1)
    (hgz : ∀ k y, y ∉ closedCube (z + R' • latticeShift k) R' → g k y = 0) :
    CenteredOsBound P (fun a => ∑ k ∈ T, ∫ y, g k y * X.field r₁ a y) s
      (Real.sqrt (2 * 4 ^ d) * (Real.sqrt T.card * (R' ^ d * (C * R' ^ (-β))))) := by
  classical
  have hR'0 : 0 < R' := zero_lt_one.trans_le hR'1
  set θ : ℝ := R' ^ d * (C * R' ^ (-β)) with hθdef
  have hθ : 0 ≤ θ := by positivity
  set U : LatticeIndex d → Set (Vec d) :=
    fun k => euclideanThickening (r₁ ^ (1 + δ)) (closedCube (z + R' • latticeShift k) R')
    with hUdef
  have hW : ∀ k, CenteredOsBound P (fun a => ∫ y, g k y * X.field r₁ a y) s θ := fun k =>
    centeredOsBound_of_rpow_neg_mul hR'0
      (hA R' hR'1 hR'R₁ r₁ hr₁lo hr₁hi _ _ (hg k) (hg1 k) (hgz k))
  have hloc : ∀ k, Measurable[F (U k)] (fun a => ∫ y, g k y * X.field r₁ a y) := fun k =>
    measurable_integral_mul_local (X.isLocal r₁ hr₁ _ (measurableSet_closedCube _ _)) (hg k)
      (hgz k)
  have hcell : ∀ k, ∀ x, x + z ∈ U k → ∀ i, |x i - R' * k i| < R' := by
    intro k x hx i
    have h := abs_sub_lt_of_mem_euclideanThickening_closedCube hx i
    simp only [Pi.add_apply, Pi.smul_apply, latticeShift, smul_eq_mul] at h
    rw [show x i + z i - (z i + R' * k i) = x i - R' * k i by ring] at h
    linarith
  have hsep : ∀ k k' : T, k ≠ k' → latticeResidue k.1 = latticeResidue k'.1 →
      SeparatedByUnit (U k.1) (U k'.1) := by
    intro k k' hkk hres
    obtain ⟨t, ht, hsep'⟩ := separatedByUnit_of_latticeResidue hR'1
      (fun h => hkk (Subtype.ext h)) hres (U := {x | x + z ∈ U k.1}) (W := {x | x + z ∈ U k'.1})
      (fun x hx => hcell k.1 x hx) (fun x hx => hcell k'.1 x hx)
    refine ⟨t, ht, fun x hx y hy => ?_⟩
    have h := hsep' (x - z) (by simpa using hx) (y - z) (by simpa using hy)
    simpa only [sub_sub_sub_cancel_right] using h
  have : Nonempty T := hT.coe_sort
  have h := centeredOsBound_sum_of_colouring hF hmono (ι := T) (κ := Fin d → ZMod 4)
    (fun k => latticeResidue k.1) (U := fun k => U k.1)
    (fun k => measurableSet_euclideanThickening _ _) hsep
    (X := fun k a => ∫ y, g k.1 y * X.field r₁ a y) (θ := fun _ => θ) (fun k => hloc k.1)
    (fun k => hW k.1)
  have hcard : (Fintype.card (Fin d → ZMod 4) : ℝ) = 4 ^ d := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    push_cast
    ring
  have hsumθ : Real.sqrt (∑ _k : T, θ ^ 2) = Real.sqrt T.card * θ := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
      Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hθ]
  have e : (fun a => ∑ k : T, ∫ y, g k.1 y * X.field r₁ a y) =
      fun a => ∑ k ∈ T, ∫ y, g k y * X.field r₁ a y :=
    funext fun a => Finset.sum_coe_sort T (fun k => ∫ y, g k y * X.field r₁ a y)
  rw [hcard, hsumθ, e] at h
  exact h

end QSH
