/-
Moved from einstein-relation-lean (https://github.com/nitromannitol/einstein-relation-lean),
commit 9ff210bd4ddf435139a6c8db07a1547e2bcb7eb6, files
`EinsteinFull/Homogenization/AKMAdditiveStructure.lean` and
`EinsteinFull/Homogenization/AKMLocalizedFields.lean`.
Changes: the namespace is `QSH`, the docstrings cite the book directly, and the vocabulary is that
of `Front/Notation.lean`, `Ch04/Opening.lean` and `AppA/OsNotation.lean`.
-/
import QuantitativeStochasticHomogenization.AppA.OsNotation
import QuantitativeStochasticHomogenization.Ch04.Opening

/-!
# Section 4.2: The Additive Structure of J₁

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Chapter 4 (Quantitative Description of First-Order Correctors), Section 4.2. Numbered results of
this section: Theorem 4.6; Propositions 4.10–4.12; Definitions 4.7–4.9.

The optimal estimates of Theorem 4.6 for the energy quantity `J₁(Φ_{z,r}, p, q)` are proved by a
bootstrap on the exponent `α` in three statements about a random field `J(a, z, r, p, q)`:
additivity `Add(s, α)` (Definition 4.7), fluctuations `Fluc(s, α)` (Definition 4.8) and
localization `Loc(s, δ, α)` (Definition 4.9). Propositions 4.10, 4.11 and 4.12 relate them, and
Proposition 4.3 supplies a first exponent.

Defined here, for an arbitrary field `J` and an arbitrary family `F` of local σ-algebras:
`FlucEstimate`, `AddEstimate` and `LocEstimate` (Definitions 4.7–4.9), and the conclusions of
Propositions 4.10–4.12 (`ImprovementOfAdditivity`, `LocalizationEstimates`,
`FluctuationEstimates`).

Proved here: the three propositions together with a positive initial exponent give
`Fluc(s, d/2)`, `Add(s/2, d)` and `Loc(s, δ, (d/2 (1+δ) + δ) ∧ d/s - η)` for every `s ∈ (0, 2)`,
that is, statements (iii), (i) and (iv) of Theorem 4.6 (`additiveStructure_of_bootstrap`). The
argument is the proof of Theorem 4.6 in this section. Proposition 4.12 is stated for
`s ∈ (1, 2]`, so the first two steps are run for `s ∈ (1, 2)` and the exponents `s ≤ 1` are
reached by `OsBound.mono_exponent`. In the third step the auxiliary exponent is
`α = d/2 - δ/(2(1+δ))`, for which `α(1+δ) + δ = d/2 (1+δ) + δ/2` exceeds `d/2 (1+δ)`, as
Proposition 4.12 requires for `β = d/2`.

The derivation is also stated for an arbitrary localization statement `L s δ α` that is monotone
in `α` (`additiveStructure_of_bootstrapFor`), since the proof of Proposition 4.12 integrates the
localized variables in space and needs them as a measurable family: `LocFieldEstimate` states
localization by a jointly measurable field, and implies `LocEstimate`.

The spatial integral in `AddEstimate` is a Bochner integral, and its integrability is part of
the statement; so is the integrability of `J` in `FlucEstimate`.
-/

open MeasureTheory

noncomputable section

namespace QSH

/-! ## Definitions 4.7–4.9 and Theorem 4.6 -/

section Bootstrap

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}

/-- **`Fluc(s, α)`**, Definition 4.8: `J(z, r, p, q) = E[J(z, r, p, q)] + O_s(C r^{-α})`
for every `z`, `r ≥ 1` and `p, q` in the open unit ball. -/
def FlucEstimate (J : Ω → Vec d → ℝ → Vec d → Vec d → ℝ) (s α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
    euclideanNorm p < 1 → euclideanNorm q < 1 →
    Integrable (fun a => J a z r p q) P ∧
    OsBound P (fun a => |J a z r p q - ∫ a', J a' z r p q ∂P|) s (C * r ^ (-α))

/-- **`Add(s, α)`**, Definition 4.7: `J(z, R, p, q)` is the `Φ_{z,√(R²-r²)}` average of
`x ↦ J(x, r, p, q)` up to `O_s(C r^{-α})`, for `1 ≤ r < R`. -/
def AddEstimate (J : Ω → Vec d → ℝ → Vec d → Vec d → ℝ) (s α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (z : Vec d) (r R : ℝ), 1 ≤ r → r < R → ∀ p q : Vec d,
    euclideanNorm p < 1 → euclideanNorm q < 1 →
    (∀ᵐ a ∂P, Integrable (fun x => heatKernel z (Real.sqrt (R ^ 2 - r ^ 2)) x * J a x r p q)) ∧
    OsBound P (fun a => |J a z R p q -
      ∫ x, heatKernel z (Real.sqrt (R ^ 2 - r ^ 2)) x * J a x r p q|) s (C * r ^ (-α))

/-- **`Loc(s, δ, α)`**, Definition 4.9: for every `z`, `r ≥ 1` and `p, q` there is an
`F(B_{r^{1+δ}}(z))`-measurable random variable within `O_s(C r^{-α})` of `J(z, r, p, q)`. -/
def LocEstimate (F : Set (Vec d) → MeasurableSpace Ω)
    (J : Ω → Vec d → ℝ → Vec d → Vec d → ℝ) (s δ α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
    euclideanNorm p < 1 → euclideanNorm q < 1 →
    ∃ Jδ : Ω → ℝ, @Measurable Ω ℝ (F (ball z (r ^ (1 + δ)))) _ Jδ ∧
      OsBound P (fun a => |J a z r p q - Jδ a|) s (C * r ^ (-α))

/-- The conclusion of Proposition 4.10 (improvement of additivity): for every `s ∈ (0, 2)`
there is `η > 0` with `Fluc(s, α) ⟹ Add(s, α + η) ∧ Add(s/2, 2α)` for `α ∈ (0, d/2]`. -/
def ImprovementOfAdditivity (J : Ω → Vec d → ℝ → Vec d → Vec d → ℝ) : Prop :=
  ∀ s : ℝ, 0 < s → s < 2 → ∃ η : ℝ, 0 < η ∧ ∀ α : ℝ, 0 < α → α ≤ (d : ℝ) / 2 →
    FlucEstimate P J s α → AddEstimate P J s (α + η) ∧ AddEstimate P J (s / 2) (2 * α)

/-- The conclusion of Proposition 4.11 (localization) for a localization statement
`L s δ α`: for `s > 0`, `α ∈ (0, d/s)` and `δ, η > 0`,
`Fluc(s, α) ⟹ L(s, δ, (α(1+δ) + δ) ∧ d/s - η)`. -/
def LocalizationEstimatesFor (J : Ω → Vec d → ℝ → Vec d → Vec d → ℝ)
    (L : ℝ → ℝ → ℝ → Prop) : Prop :=
  ∀ s α δ η : ℝ, 0 < s → 0 < α → α < (d : ℝ) / s → 0 < δ → 0 < η →
    FlucEstimate P J s α → L s δ (min (α * (1 + δ) + δ) ((d : ℝ) / s) - η)

/-- The conclusion of Proposition 4.12 (fluctuations) for a localization statement
`L s δ α`: for `s ∈ (1, 2]`, `β ∈ (0, d/2]` and `α, δ > 0` with `α > β(1+δ)`,
`Add(s, α) ∧ L(s, δ, α) ⟹ Fluc(s, β)`. -/
def FluctuationEstimatesFor (J : Ω → Vec d → ℝ → Vec d → Vec d → ℝ)
    (L : ℝ → ℝ → ℝ → Prop) : Prop :=
  ∀ s β α δ : ℝ, 1 < s → s ≤ 2 → 0 < β → β ≤ (d : ℝ) / 2 → 0 < δ → β * (1 + δ) < α →
    AddEstimate P J s α → L s δ α → FlucEstimate P J s β

/-- The conclusion of Proposition 4.11 with the localization `Loc(s, δ, α)` of
Definition 4.9. -/
def LocalizationEstimates (F : Set (Vec d) → MeasurableSpace Ω)
    (J : Ω → Vec d → ℝ → Vec d → Vec d → ℝ) : Prop :=
  LocalizationEstimatesFor P J (LocEstimate P F J)

/-- The conclusion of Proposition 4.12 with the localization `Loc(s, δ, α)` of
Definition 4.9. -/
def FluctuationEstimates (F : Set (Vec d) → MeasurableSpace Ω)
    (J : Ω → Vec d → ℝ → Vec d → Vec d → ℝ) : Prop :=
  FluctuationEstimatesFor P J (LocEstimate P F J)

variable {P}
variable {F : Set (Vec d) → MeasurableSpace Ω} {J : Ω → Vec d → ℝ → Vec d → Vec d → ℝ}
variable {L : ℝ → ℝ → ℝ → Prop}

theorem rpow_neg_le_rpow_neg {r α α' : ℝ} (hr : 1 ≤ r) (hα : α' ≤ α) :
    r ^ (-α) ≤ r ^ (-α') :=
  Real.rpow_le_rpow_of_exponent_le hr (neg_le_neg hα)

theorem FlucEstimate.mono {s α α' : ℝ} (h : FlucEstimate P J s α) (hα : α' ≤ α) :
    FlucEstimate P J s α' := by
  obtain ⟨C, hC, hJ⟩ := h
  refine ⟨C, hC, fun z r hr p q hp hq => ?_⟩
  obtain ⟨hi, hb⟩ := hJ z r hr p q hp hq
  exact ⟨hi, hb.mono_scale (mul_le_mul_of_nonneg_left (rpow_neg_le_rpow_neg hr hα) hC.le)⟩

/-- `Fluc(s, α) ⟹ Fluc(s', α)` for `0 < s' ≤ s`. -/
theorem FlucEstimate.mono_exponent [IsProbabilityMeasure P] {s s' α : ℝ}
    (h : FlucEstimate P J s α) (hs' : 0 < s') (hss : s' ≤ s) : FlucEstimate P J s' α := by
  obtain ⟨C, hC, hJ⟩ := h
  have hκ : 0 < (2 * Real.exp 1 - 1) ^ s'⁻¹ :=
    Real.rpow_pos_of_pos (by linarith [Real.add_one_le_exp (1 : ℝ)]) _
  refine ⟨(2 * Real.exp 1 - 1) ^ s'⁻¹ * C, mul_pos hκ hC, fun z r hr p q hp hq => ?_⟩
  obtain ⟨hi, hb⟩ := hJ z r hr p q hp hq
  refine ⟨hi, ?_⟩
  simpa only [mul_assoc] using hb.mono_exponent hs' hss

theorem AddEstimate.mono {s α α' : ℝ} (h : AddEstimate P J s α) (hα : α' ≤ α) :
    AddEstimate P J s α' := by
  obtain ⟨C, hC, hJ⟩ := h
  refine ⟨C, hC, fun z r R hr hrR p q hp hq => ?_⟩
  obtain ⟨hi, hb⟩ := hJ z r R hr hrR p q hp hq
  exact ⟨hi, hb.mono_scale (mul_le_mul_of_nonneg_left (rpow_neg_le_rpow_neg hr hα) hC.le)⟩

theorem LocEstimate.mono {s δ α α' : ℝ} (h : LocEstimate P F J s δ α) (hα : α' ≤ α) :
    LocEstimate P F J s δ α' := by
  obtain ⟨C, hC, hJ⟩ := h
  refine ⟨C, hC, fun z r hr p q hp hq => ?_⟩
  obtain ⟨Jδ, hm, hb⟩ := hJ z r hr p q hp hq
  exact ⟨Jδ, hm, hb.mono_scale (mul_le_mul_of_nonneg_left (rpow_neg_le_rpow_neg hr hα) hC.le)⟩

theorem half_dim_lt_dim_div {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 < s) (hs2 : s < 2) :
    (d : ℝ) / 2 < (d : ℝ) / s :=
  div_lt_div_of_pos_left (by exact_mod_cast hd) hs0 hs2

/-- **Step 1 of the proof of Theorem 4.6.** For `s ∈ (1, 2)` and `ε > 0` there is `τ > 0`
such that `Fluc(s, α) ⟹ Fluc(s, α + τ)` for every `α ∈ (0, d/2 - ε]`. -/
theorem exists_flucEstimate_improvement (hd : 1 ≤ d) (h410 : ImprovementOfAdditivity P J)
    (hL : ∀ s δ α α' : ℝ, L s δ α → α' ≤ α → L s δ α')
    (h411 : LocalizationEstimatesFor P J L) (h412 : FluctuationEstimatesFor P J L) {s ε : ℝ}
    (hs1 : 1 < s) (hs2 : s < 2) (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ α : ℝ, 0 < α → α ≤ (d : ℝ) / 2 - ε →
      FlucEstimate P J s α → FlucEstimate P J s (α + τ) := by
  obtain ⟨η₀, hη₀, hadd⟩ := h410 s (by linarith) hs2
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set η : ℝ := min η₀ (ε / 2) with hηdef
  have hη : 0 < η := lt_min hη₀ (by linarith)
  have hηη₀ : η ≤ η₀ := min_le_left _ _
  have hηε : η ≤ ε / 2 := min_le_right _ _
  set δ : ℝ := η / (1 + (d : ℝ) / 2) with hδdef
  have hδ : 0 < δ := div_pos hη (by positivity)
  have hδη : δ * (1 + (d : ℝ) / 2) = η := by
    rw [hδdef]
    field_simp
  set τ : ℝ := δ / (4 + 4 * δ) with hτdef
  have hτ : 0 < τ := div_pos hδ (by positivity)
  have hτδ : τ * (1 + δ) = δ / 4 := by
    rw [hτdef]
    field_simp
  have hτle : τ ≤ δ / 4 := by
    rw [hτdef]
    exact div_le_div_of_nonneg_left hδ.le (by norm_num) (by linarith)
  have hδle : δ ≤ η := by
    rw [hδdef]
    exact div_le_self hη.le (by linarith [div_nonneg hd0 (by norm_num : (0 : ℝ) ≤ 2)])
  refine ⟨τ, hτ, fun α hα hαle hF => ?_⟩
  have hαd : α ≤ (d : ℝ) / 2 := by linarith
  have key : α * (1 + δ) + δ ≤ α + η := by
    have : δ * (α + 1) ≤ δ * ((d : ℝ) / 2 + 1) := mul_le_mul_of_nonneg_left (by linarith) hδ.le
    nlinarith [hδη]
  have hlt : α * (1 + δ) + δ < (d : ℝ) / s := by
    have := half_dim_lt_dim_div hd (by linarith) hs2
    linarith
  have hαs : α < (d : ℝ) / s := by nlinarith
  have hAdd : AddEstimate P J s (α * (1 + δ) + δ / 2) :=
    (hadd α hα hαd hF).1.mono (by linarith)
  have hLoc0 := h411 s α δ (δ / 2) (by linarith) hα hαs hδ (by linarith) hF
  rw [min_eq_left hlt.le] at hLoc0
  have hLoc : L s δ (α * (1 + δ) + δ / 2) := hL _ _ _ _ hLoc0 (by linarith)
  refine h412 s (α + τ) (α * (1 + δ) + δ / 2) δ hs1 hs2.le (by linarith) (by linarith) hδ ?_
    hAdd hLoc
  nlinarith [hτδ]

/-- **Step 2 of the proof of Theorem 4.6.** For `s ∈ (1, 2)`, `Fluc(s, α)` holds for every
`α < d/2`. -/
theorem flucEstimate_of_lt_half_dim (hd : 1 ≤ d) (h410 : ImprovementOfAdditivity P J)
    (hL : ∀ s δ α α' : ℝ, L s δ α → α' ≤ α → L s δ α')
    (h411 : LocalizationEstimatesFor P J L) (h412 : FluctuationEstimatesFor P J L)
    (hbase : ∀ s : ℝ, 1 < s → s < 2 → ∃ α₀ : ℝ, 0 < α₀ ∧ FlucEstimate P J s α₀) {s α : ℝ}
    (hs1 : 1 < s) (hs2 : s < 2) (hα : α < (d : ℝ) / 2) : FlucEstimate P J s α := by
  obtain ⟨α₀, hα₀, hF₀⟩ := hbase s hs1 hs2
  rcases le_or_gt α 0 with hα0 | hα0
  · exact hF₀.mono (by linarith)
  set ε : ℝ := (d : ℝ) / 2 - α with hεdef
  have hε : 0 < ε := by linarith
  obtain ⟨τ, hτ, hstep⟩ := exists_flucEstimate_improvement hd h410 hL h411 h412 hs1 hs2 hε
  set a₀ : ℝ := min α₀ ((d : ℝ) / 2 - ε) with ha₀def
  have ha₀ : 0 < a₀ := lt_min hα₀ (by linarith)
  have hind : ∀ n : ℕ, FlucEstimate P J s (min (a₀ + n * τ) ((d : ℝ) / 2 - ε)) := by
    intro n
    induction n with
    | zero =>
      simp only [Nat.cast_zero, zero_mul, add_zero]
      exact hF₀.mono ((min_le_left _ _).trans (min_le_left _ _))
    | succ n ih =>
      have hb0 : 0 < min (a₀ + n * τ) ((d : ℝ) / 2 - ε) :=
        lt_min (by positivity) (by linarith)
      have h1 := hstep _ hb0 (min_le_right _ _) ih
      refine h1.mono ?_
      have hc : (a₀ + ((n + 1 : ℕ) : ℝ) * τ) = a₀ + n * τ + τ := by push_cast; ring
      rw [hc]
      rcases le_total (a₀ + n * τ) ((d : ℝ) / 2 - ε) with h | h
      · rw [min_eq_left h]
        exact min_le_left _ _
      · rw [min_eq_right h]
        exact (min_le_right _ _).trans (by linarith)
  obtain ⟨n, hn⟩ := exists_nat_gt (((d : ℝ) / 2 - ε - a₀) / τ)
  have hn' : (d : ℝ) / 2 - ε ≤ a₀ + n * τ := by
    rw [div_lt_iff₀ hτ] at hn
    linarith
  have := hind n
  rw [min_eq_right hn'] at this
  simpa [hεdef] using this

/-- **Step 3 of the proof of Theorem 4.6.** For `s ∈ (1, 2)`, `Fluc(s, d/2)` holds. -/
theorem flucEstimate_half_dim_of_one_lt (hd : 1 ≤ d) (h410 : ImprovementOfAdditivity P J)
    (hL : ∀ s δ α α' : ℝ, L s δ α → α' ≤ α → L s δ α')
    (h411 : LocalizationEstimatesFor P J L) (h412 : FluctuationEstimatesFor P J L)
    (hbase : ∀ s : ℝ, 1 < s → s < 2 → ∃ α₀ : ℝ, 0 < α₀ ∧ FlucEstimate P J s α₀) {s : ℝ}
    (hs1 : 1 < s) (hs2 : s < 2) : FlucEstimate P J s ((d : ℝ) / 2) := by
  obtain ⟨η, hη, hadd⟩ := h410 s (by linarith) hs2
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  set δ : ℝ := min (2 * η / ((d : ℝ) + 2)) ((d : ℝ) * (2 - s) / (s * ((d : ℝ) + 1)))
    with hδdef
  have hδ : 0 < δ := lt_min (by positivity)
    (div_pos (mul_pos (by linarith) (by linarith)) (by positivity))
  have hδη : δ * ((d : ℝ) + 2) ≤ 2 * η := by
    have := min_le_left (2 * η / ((d : ℝ) + 2)) ((d : ℝ) * (2 - s) / (s * ((d : ℝ) + 1)))
    rw [← hδdef, le_div_iff₀ (by linarith)] at this
    exact this
  have hδs : δ * (s * ((d : ℝ) + 1)) ≤ (d : ℝ) * (2 - s) := by
    have := min_le_right (2 * η / ((d : ℝ) + 2)) ((d : ℝ) * (2 - s) / (s * ((d : ℝ) + 1)))
    rw [← hδdef, le_div_iff₀ (by positivity)] at this
    exact this
  set αF : ℝ := (d : ℝ) / 2 - δ / (2 * (1 + δ)) with hαFdef
  have hq : 0 < δ / (2 * (1 + δ)) := div_pos hδ (by positivity)
  have hq' : δ / (2 * (1 + δ)) ≤ δ / 2 :=
    div_le_div_of_nonneg_left hδ.le (by norm_num) (by linarith)
  have hq'' : δ / (2 * (1 + δ)) < 1 / 2 := by
    rw [div_lt_iff₀ (by positivity)]
    linarith
  have hαF0 : 0 < αF := by linarith
  have hαFlt : αF < (d : ℝ) / 2 := by linarith
  have hF := flucEstimate_of_lt_half_dim hd h410 hL h411 h412 hbase hs1 hs2 hαFlt
  set α' : ℝ := (d : ℝ) / 2 * (1 + δ) + δ / 2 with hα'def
  have hαF' : αF * (1 + δ) + δ = α' := by
    rw [hαFdef, hα'def]
    field_simp
    ring
  have hα'add : α' ≤ αF + η := by
    rw [hα'def, hαFdef]
    nlinarith
  have hα's : α' ≤ (d : ℝ) / s := by
    rw [hα'def, le_div_iff₀ hs0]
    nlinarith
  have hαFs : αF < (d : ℝ) / s := by
    have := half_dim_lt_dim_div hd hs0 hs2
    linarith
  have hAdd : AddEstimate P J s (α' - δ / 4) :=
    (hadd αF hαF0 hαFlt.le hF).1.mono (by linarith)
  have hLoc0 := h411 s αF δ (δ / 4) hs0 hαF0 hαFs hδ (by positivity) hF
  rw [hαF', min_eq_left hα's] at hLoc0
  refine h412 s ((d : ℝ) / 2) (α' - δ / 4) δ hs1 hs2.le (by positivity) le_rfl hδ ?_ hAdd hLoc0
  rw [hα'def]
  linarith

/-- **Theorem 4.6 (i), (iii), (iv) from Propositions 4.10, 4.11 and 4.12**, for any
localization statement `L` that is monotone in its exponent. If the
conclusions of the three propositions hold for a field `J` and, for each `s ∈ (1, 2)`,
`Fluc(s, α₀)` holds for some `α₀ > 0` (Proposition 4.3), then for every `s ∈ (0, 2)`:
`Fluc(s, d/2)`, `Add(s/2, d)` and `L(s, δ, (d/2 (1+δ) + δ) ∧ d/s - η)` for all `δ, η > 0`. -/
theorem additiveStructure_of_bootstrapFor [IsProbabilityMeasure P] (hd : 1 ≤ d)
    (h410 : ImprovementOfAdditivity P J) (hL : ∀ s δ α α' : ℝ, L s δ α → α' ≤ α → L s δ α')
    (h411 : LocalizationEstimatesFor P J L) (h412 : FluctuationEstimatesFor P J L)
    (hbase : ∀ s : ℝ, 1 < s → s < 2 → ∃ α₀ : ℝ, 0 < α₀ ∧ FlucEstimate P J s α₀)
    {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    FlucEstimate P J s ((d : ℝ) / 2) ∧ AddEstimate P J (s / 2) d ∧
      ∀ δ η : ℝ, 0 < δ → 0 < η →
        L s δ (min ((d : ℝ) / 2 * (1 + δ) + δ) ((d : ℝ) / s) - η) := by
  have hF : FlucEstimate P J s ((d : ℝ) / 2) := by
    rcases lt_or_ge 1 s with hs1 | hs1
    · exact flucEstimate_half_dim_of_one_lt hd h410 hL h411 h412 hbase hs1 hs2
    · exact (flucEstimate_half_dim_of_one_lt hd h410 hL h411 h412 hbase (s := 3 / 2)
        (by norm_num) (by norm_num)).mono_exponent hs0 (by linarith)
  have hd2 : (0 : ℝ) < (d : ℝ) / 2 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨η, -, hadd⟩ := h410 s hs0 hs2
  refine ⟨hF, ?_, fun δ η' hδ hη' => ?_⟩
  · have := (hadd ((d : ℝ) / 2) hd2 le_rfl hF).2
    rwa [mul_div_cancel₀ _ (two_ne_zero : (2 : ℝ) ≠ 0)] at this
  · exact h411 s ((d : ℝ) / 2) δ η' hs0 hd2 (half_dim_lt_dim_div hd hs0 hs2) hδ hη' hF

/-- **Theorem 4.6 (i), (iii), (iv) from Propositions 4.10, 4.11 and 4.12** with the
localization `Loc(s, δ, α)` of Definition 4.9. -/
theorem additiveStructure_of_bootstrap [IsProbabilityMeasure P] (hd : 1 ≤ d)
    (h410 : ImprovementOfAdditivity P J) (h411 : LocalizationEstimates P F J)
    (h412 : FluctuationEstimates P F J)
    (hbase : ∀ s : ℝ, 1 < s → s < 2 → ∃ α₀ : ℝ, 0 < α₀ ∧ FlucEstimate P J s α₀)
    {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    FlucEstimate P J s ((d : ℝ) / 2) ∧ AddEstimate P J (s / 2) d ∧
      ∀ δ η : ℝ, 0 < δ → 0 < η →
        LocEstimate P F J s δ (min ((d : ℝ) / 2 * (1 + δ) + δ) ((d : ℝ) / s) - η) :=
  additiveStructure_of_bootstrapFor (L := LocEstimate P F J) hd h410 (fun _ _ _ _ h hα => h.mono hα)
    h411 h412 hbase hs0 hs2

end Bootstrap

/-! ## Localization by measurable fields

The proof of Proposition 4.12 integrates the localized quantities `x ↦ J₁^{(δ)}(x, r, p, q)` over
boxes and uses that the integrals over boxes at distance larger than one are independent.
Definition 4.9 provides one `F(B_{r^{1+δ}}(z))`-measurable random variable for each center `z`;
the argument needs a family that is jointly measurable in the coefficients and the center, with
the coefficients restricted to the `r^{1+δ}`-neighbourhood of the set of centers.
`LocFieldEstimate` states this, and implies `LocEstimate`. -/

section LocalizedFields

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}

/-- The open Euclidean `ρ`-neighbourhood of a set. -/
def euclideanThickening (ρ : ℝ) (U : Set (Vec d)) : Set (Vec d) :=
  {y | ∃ x ∈ U, euclideanNorm (y - x) < ρ}

theorem euclideanThickening_singleton (ρ : ℝ) (z : Vec d) :
    euclideanThickening ρ {z} = ball z ρ := by
  ext y
  simp [euclideanThickening, ball]

/-- **Localization by a measurable field**: for every `r ≥ 1` and `p, q` there is a family
`J^δ(a, x)` such that, for every measurable set `U` of centers, `(a, x) ↦ 1_U(x) J^δ(a, x)` is
measurable for the coefficients in the `r^{1+δ}`-neighbourhood of `U` and the Borel sets of the
centers, and `|J(z, r, p, q) - J^δ(·, z)| ≤ O_s(C r^{-α})` for every `z`. -/
def LocFieldEstimate (F : Set (Vec d) → MeasurableSpace Ω)
    (J : Ω → Vec d → ℝ → Vec d → Vec d → ℝ) (s δ α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r → ∀ p q : Vec d,
    euclideanNorm p < 1 → euclideanNorm q < 1 →
    ∃ Jδ : Ω → Vec d → ℝ,
      (∀ U : Set (Vec d), MeasurableSet U →
        @Measurable (Ω × Vec d) ℝ
          (@Prod.instMeasurableSpace Ω (Vec d) (F (euclideanThickening (r ^ (1 + δ)) U)) _) _
          (fun w => U.indicator (Jδ w.1) w.2)) ∧
      ∀ z : Vec d, OsBound P (fun a => |J a z r p q - Jδ a z|) s (C * r ^ (-α))

variable {P}
variable {F : Set (Vec d) → MeasurableSpace Ω} {J : Ω → Vec d → ℝ → Vec d → Vec d → ℝ}

theorem LocFieldEstimate.mono {s δ α α' : ℝ} (h : LocFieldEstimate P F J s δ α)
    (hα : α' ≤ α) : LocFieldEstimate P F J s δ α' := by
  obtain ⟨C, hC, hJ⟩ := h
  refine ⟨C, hC, fun r hr p q hp hq => ?_⟩
  obtain ⟨Jδ, hm, hb⟩ := hJ r hr p q hp hq
  exact ⟨Jδ, hm, fun z => (hb z).mono_scale
    (mul_le_mul_of_nonneg_left (rpow_neg_le_rpow_neg hr hα) hC.le)⟩

/-- A measurable localized field gives the localization of Definition 4.9 at every center. -/
theorem LocFieldEstimate.locEstimate {s δ α : ℝ} (h : LocFieldEstimate P F J s δ α) :
    LocEstimate P F J s δ α := by
  obtain ⟨C, hC, hJ⟩ := h
  refine ⟨C, hC, fun z r hr p q hp hq => ?_⟩
  obtain ⟨Jδ, hm, hb⟩ := hJ r hr p q hp hq
  refine ⟨fun a => Jδ a z, ?_, hb z⟩
  have hmz := hm {z} (measurableSet_singleton z)
  rw [euclideanThickening_singleton] at hmz
  have hpair : @Measurable Ω (Ω × Vec d) (F (ball z (r ^ (1 + δ))))
      (@Prod.instMeasurableSpace Ω (Vec d) (F (ball z (r ^ (1 + δ)))) _) (fun a => (a, z)) :=
    @measurable_prodMk_right Ω (Vec d) (F (ball z (r ^ (1 + δ)))) _ z
  have := hmz.comp hpair
  simpa [Function.comp_def, Set.indicator_of_mem (Set.mem_singleton z)] using this

end LocalizedFields

end QSH
