import QuantitativeStochasticHomogenization.Ch04.Sec02AdditiveStructureOfJ1
import Mathlib.Analysis.MeanInequalities

/-!
# The bootstrap of Theorem 4.6 with constants chosen before the law

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.2, proof of Theorem 4.6. The constants of Theorem 4.6 depend only on `s`, `d` and `Λ`.
In the proof this is the statement that the implications of Propositions 4.10, 4.11 and 4.12 hold
with an output constant that depends on the input constant and the exponents, but not on the law.

Defined here: Definitions 4.7–4.9 with the numerical witness exposed (`AddEstimateAt`,
`FlucEstimateAt`, `LocFieldEstimateAt`), so that `FlucEstimate P J s α ↔ ∃ C > 0,
FlucEstimateAt P J s α C`, and similarly for the other two.

Proved here:
* `OsBound.mono_exponent_sharp`: `X ≤ O_u(θ)` implies `X ≤ O_s((log 2)^{1/u - 1/s} θ)` for
  `0 < s ≤ u`, by the weighted arithmetic–geometric mean inequality and the convexity of the
  exponential;
* `fluctuation_endpoint_of_steps`: a fixed positive increment reaches the endpoint `d/2` in
  finitely many steps;
* `uniform_flucEstimate_half_dim`: for a family of laws and fields with a common initial
  constant, and the three implications with output constants chosen before the member of the
  family, one constant `C` gives `Fluc(u, d/2)` for every member, and `Fluc(s, d/2)` with the
  constant `(log 2)^{1/u - 1/s} C` for every `0 < s ≤ u`.

The localization parameter is the same at every step of the induction,
`δ = min(ν, d/u - d/2)/(1 + d/2)`, with the loss `δ/4` in Proposition 4.11. The exponents are
`a_n = min(d/2, a₀ + n h)` with `h = δ/(2(1+δ))`, and Proposition 4.12 is applied at the rate
`a_n (1+δ) + 3δ/4`; this also covers the last step, where the book's choice
`α = (d - δ)/(2(1+δ))` does not satisfy the hypothesis `α(1+δ) + δ > d/2 (1+δ)` of Proposition 4.12.
-/

open MeasureTheory

noncomputable section

namespace QSH

/-! ## The scale multiplier when lowering the stochastic exponent -/

/-- **`O_u(θ) ⊂ O_s((log 2)^{1/u - 1/s} θ)` for `0 < s ≤ u`.** The multiplier is attained by a
constant random variable. -/
theorem OsBound.mono_exponent_sharp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} {u s θ : ℝ} (hX : OsBound P X u θ)
    (hs : 0 < s) (hsu : s ≤ u) :
    OsBound P X s ((Real.log 2) ^ (u⁻¹ - s⁻¹) * θ) := by
  obtain ⟨hm, hu, hθ, hfi, hE⟩ := osBound_iff_ogammaLE.mp hX
  let t := s / u
  let k := (Real.log 2) ^ (u⁻¹ - s⁻¹)
  have ht : 0 ≤ t := (div_pos hs hu).le
  have ht' : 0 ≤ 1 - t := sub_nonneg.mpr ((div_le_one hu).mpr hsu)
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hk : 0 < k := Real.rpow_pos_of_pos hl _
  have hkt : (k⁻¹) ^ s = (Real.log 2) ^ (1 - t) := by
    dsimp [k, t]
    rw [← Real.rpow_neg hl.le, ← Real.rpow_mul hl.le]
    congr 1
    field_simp
    ring
  let f (ω : Ω) := Real.exp ((θ⁻¹ * max (X ω) 0) ^ u)
  let g (ω : Ω) := Real.exp (((k * θ)⁻¹ * max (X ω) 0) ^ s)
  have hpt (ω : Ω) : g ω ≤ (1 - t) * 2 + t * f ω := by
    let y := θ⁻¹ * max (X ω) 0
    have hy : 0 ≤ y := mul_nonneg (inv_nonneg.mpr hθ.le) (le_max_right _ _)
    have hpow : (((k * θ)⁻¹ * max (X ω) 0) ^ s) =
        (Real.log 2) ^ (1 - t) * (y ^ u) ^ t := by
      rw [mul_inv, mul_assoc, Real.mul_rpow (inv_nonneg.mpr hk.le) hy, hkt,
        ← Real.rpow_mul hy, show u * t = s by dsimp [t]; field_simp]
    have harith := Real.geom_mean_le_arith_mean2_weighted ht' ht hl.le
      (Real.rpow_nonneg hy u) (by ring)
    have hexp : Real.exp ((1 - t) * Real.log 2 + t * y ^ u) ≤
        (1 - t) * Real.exp (Real.log 2) + t * Real.exp (y ^ u) :=
      convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) ht' ht (by ring)
    dsimp only [g]
    rw [hpow]
    exact (Real.exp_le_exp.mpr harith).trans (by simpa only [Real.exp_log two_pos] using hexp)
  have hI : Integrable (fun ω => (1 - t) * 2 + t * f ω) P :=
    (integrable_const _).add (hfi.const_mul t)
  have hg : Integrable g P := hI.mono' (measurable_osIntegrand hm s _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hpt ω)
  refine osBound_iff_ogammaLE.mpr ⟨hm, hs, mul_pos hk hθ, hg, ?_⟩
  calc ∫ ω, g ω ∂P ≤ ∫ ω, ((1 - t) * 2 + t * f ω) ∂P := integral_mono hg hI hpt
    _ = (1 - t) * 2 + t * ∫ ω, f ω ∂P := by
      rw [integral_add (integrable_const _) (hfi.const_mul t), integral_const_mul t f]
      simp
    _ ≤ (1 - t) * 2 + t * 2 := add_le_add_right (mul_le_mul_of_nonneg_left hE ht) _
    _ = 2 := by ring

/-! ## Definitions 4.7–4.9 with the numerical witness -/

section Witnesses

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- **`Fluc(s, α)` with constant `C`**, Definition 4.8. -/
def FlucEstimateAt (P : Measure Ω) (J : Ω → Vec d → ℝ → Vec d → Vec d → ℝ) (s α C : ℝ) :
    Prop :=
  ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
    euclideanNorm p < 1 → euclideanNorm q < 1 →
    Integrable (fun a => J a z r p q) P ∧
    OsBound P (fun a => |J a z r p q - ∫ a', J a' z r p q ∂P|) s (C * r ^ (-α))

/-- **`Add(s, α)` with constant `C`**, Definition 4.7. -/
def AddEstimateAt (P : Measure Ω) (J : Ω → Vec d → ℝ → Vec d → Vec d → ℝ) (s α C : ℝ) :
    Prop :=
  ∀ (z : Vec d) (r R : ℝ), 1 ≤ r → r < R → ∀ p q : Vec d,
    euclideanNorm p < 1 → euclideanNorm q < 1 →
    (∀ᵐ a ∂P, Integrable fun x => heatKernel z (Real.sqrt (R ^ 2 - r ^ 2)) x * J a x r p q) ∧
    OsBound P (fun a => |J a z R p q -
      ∫ x, heatKernel z (Real.sqrt (R ^ 2 - r ^ 2)) x * J a x r p q|) s (C * r ^ (-α))

/-- **`Loc(s, δ, α)` by a measurable field with constant `C`**, Definition 4.9 in the form
`LocFieldEstimate`. -/
def LocFieldEstimateAt (P : Measure Ω) (F : Set (Vec d) → MeasurableSpace Ω)
    (J : Ω → Vec d → ℝ → Vec d → Vec d → ℝ) (s δ α C : ℝ) : Prop :=
  ∀ r : ℝ, 1 ≤ r → ∀ p q : Vec d, euclideanNorm p < 1 → euclideanNorm q < 1 →
    ∃ Jδ : Ω → Vec d → ℝ,
      (∀ U : Set (Vec d), MeasurableSet U →
        @Measurable (Ω × Vec d) ℝ
          (@Prod.instMeasurableSpace Ω (Vec d) (F (euclideanThickening (r ^ (1 + δ)) U)) _) _
          (fun w => U.indicator (Jδ w.1) w.2)) ∧
      ∀ z : Vec d, OsBound P (fun a => |J a z r p q - Jδ a z|) s (C * r ^ (-α))

variable {P : Measure Ω} {F : Set (Vec d) → MeasurableSpace Ω}
  {J : Ω → Vec d → ℝ → Vec d → Vec d → ℝ}

theorem flucEstimate_iff_exists_at (s α : ℝ) :
    FlucEstimate P J s α ↔ ∃ C > 0, FlucEstimateAt P J s α C := Iff.rfl

theorem addEstimate_iff_exists_at (s α : ℝ) :
    AddEstimate P J s α ↔ ∃ C > 0, AddEstimateAt P J s α C := Iff.rfl

theorem locFieldEstimate_iff_exists_at (s δ α : ℝ) :
    LocFieldEstimate P F J s δ α ↔ ∃ C > 0, LocFieldEstimateAt P F J s δ α C := Iff.rfl

theorem FlucEstimateAt.mono_rate {s α β C : ℝ} (h : FlucEstimateAt P J s α C) (hC : 0 ≤ C)
    (hβα : β ≤ α) : FlucEstimateAt P J s β C := by
  intro z r hr p q hp hq
  obtain ⟨hi, hb⟩ := h z r hr p q hp hq
  exact ⟨hi, hb.mono_scale (mul_le_mul_of_nonneg_left (rpow_neg_le_rpow_neg hr hβα) hC)⟩

theorem AddEstimateAt.mono_rate {s α β C : ℝ} (h : AddEstimateAt P J s α C) (hC : 0 ≤ C)
    (hβα : β ≤ α) : AddEstimateAt P J s β C := by
  intro z r R hr hrR p q hp hq
  obtain ⟨hi, hb⟩ := h z r R hr hrR p q hp hq
  exact ⟨hi, hb.mono_scale (mul_le_mul_of_nonneg_left (rpow_neg_le_rpow_neg hr hβα) hC)⟩

theorem AddEstimateAt.mono_const {s α C C' : ℝ} (h : AddEstimateAt P J s α C) (hCC : C ≤ C') :
    AddEstimateAt P J s α C' := by
  intro z r R hr hrR p q hp hq
  obtain ⟨hi, hb⟩ := h z r R hr hrR p q hp hq
  exact ⟨hi, hb.mono_scale (mul_le_mul_of_nonneg_right hCC
    (Real.rpow_nonneg (zero_le_one.trans hr) _))⟩

theorem LocFieldEstimateAt.mono_rate {s δ α β C : ℝ} (h : LocFieldEstimateAt P F J s δ α C)
    (hC : 0 ≤ C) (hβα : β ≤ α) : LocFieldEstimateAt P F J s δ β C := by
  intro r hr p q hp hq
  obtain ⟨Jδ, hm, hb⟩ := h r hr p q hp hq
  exact ⟨Jδ, hm, fun z => (hb z).mono_scale
    (mul_le_mul_of_nonneg_left (rpow_neg_le_rpow_neg hr hβα) hC)⟩

theorem FlucEstimateAt.mono_exponent_sharp [IsProbabilityMeasure P] {u s α C : ℝ}
    (h : FlucEstimateAt P J u α C) (hs : 0 < s) (hsu : s ≤ u) :
    FlucEstimateAt P J s α ((Real.log 2) ^ (u⁻¹ - s⁻¹) * C) := by
  intro z r hr p q hp hq
  obtain ⟨hi, hF⟩ := h z r hr p q hp hq
  exact ⟨hi, by simpa only [mul_assoc] using hF.mono_exponent_sharp hs hsu⟩

end Witnesses

/-! ## The finite induction -/

/-- A fixed positive increment reaches the closed endpoint after finitely many steps. -/
theorem fluctuation_endpoint_of_steps (F : ℝ → Prop) {a₀ b h : ℝ}
    (ha₀ : 0 < a₀) (hab : a₀ ≤ b) (hh : 0 < h) (hbase : F a₀)
    (hstep : ∀ a β, 0 < a → a ≤ β → β ≤ b → β ≤ a + h → F a → F β) :
    F b := by
  have hb := ha₀.trans_le hab
  let a (n : ℕ) := min b (a₀ + (n : ℝ) * h)
  have hpos (n : ℕ) : 0 < a n := lt_min hb (by positivity)
  have hle (n : ℕ) : a n ≤ b := min_le_left _ _
  have hmono (n : ℕ) : a n ≤ a (n + 1) :=
    min_le_min le_rfl (by push_cast; linarith)
  have hinc (n : ℕ) : a (n + 1) ≤ a n + h := by
    dsimp only [a]
    rw [← min_add_add_right]
    exact min_le_min (by linarith) (by push_cast; linarith)
  have hind (n : ℕ) : F (a n) := by
    induction n with
    | zero => simpa [a, min_eq_right hab] using hbase
    | succ n ih => exact hstep _ _ (hpos n) (hmono n) (hle _) (hinc n) ih
  obtain ⟨n, hn⟩ := exists_nat_ge ((b - a₀) / h)
  have hend : b ≤ a₀ + (n : ℝ) * h := by
    rw [div_le_iff₀ hh] at hn
    linarith
  simpa only [a, min_eq_left hend] using hind n

/-- The localization parameter `min(ν, cap - b)/(1 + b)` used at every step of the induction. -/
def fluctuationBootstrapDelta (b ν cap : ℝ) : ℝ := min ν (cap - b) / (1 + b)

theorem fluctuationBootstrapDelta_pos {b ν cap : ℝ} (hb : 0 ≤ b) (hν : 0 < ν) (hcap : b < cap) :
    0 < fluctuationBootstrapDelta b ν cap :=
  div_pos (lt_min hν (sub_pos.mpr hcap)) (by linarith)

/-- **The bootstrap of Theorem 4.6 with constants chosen before the law.** For a family of laws
`P i` and fields `J i`, a common constant in `Fluc(u, a₀)`, and the implications of
Propositions 4.10, 4.11 and 4.12 with output constants chosen before `i`, there is one constant
`C` with `Fluc(u, d/2)` for every `i`, and `Fluc(s, d/2)` with constant `(log 2)^{1/u - 1/s} C`
for every `0 < s ≤ u`. The localization parameter is
`δ = fluctuationBootstrapDelta (d/2) ν (d/u)` with the loss `δ/4`. -/
theorem uniform_flucEstimate_half_dim {ι Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : ι → Measure Ω) [∀ i, IsProbabilityMeasure (P i)]
    (σ : Set (Vec d) → MeasurableSpace Ω) (J : ι → Ω → Vec d → ℝ → Vec d → Vec d → ℝ)
    {u a₀ ν : ℝ} (hd : 1 ≤ d) (hu₁ : 1 < u) (hu₂ : u < 2)
    (ha₀ : 0 < a₀) (hab : a₀ ≤ (d : ℝ) / 2) (hν : 0 < ν)
    (hbase : ∃ C > 0, ∀ i, FlucEstimateAt (P i) (J i) u a₀ C)
    (hadd : ∀ a C, 0 < a → a ≤ (d : ℝ) / 2 → 0 < C → ∃ D > 0,
      ∀ i, FlucEstimateAt (P i) (J i) u a C → AddEstimateAt (P i) (J i) u (a + ν) D)
    (hloc : ∀ a C, 0 < a → a ≤ (d : ℝ) / 2 → 0 < C → ∃ D > 0, ∀ i,
      FlucEstimateAt (P i) (J i) u a C →
        LocFieldEstimateAt (P i) σ (J i) u (fluctuationBootstrapDelta ((d : ℝ) / 2) ν ((d : ℝ) / u))
          (min (a * (1 + fluctuationBootstrapDelta ((d : ℝ) / 2) ν ((d : ℝ) / u)) +
              fluctuationBootstrapDelta ((d : ℝ) / 2) ν ((d : ℝ) / u)) ((d : ℝ) / u) -
            fluctuationBootstrapDelta ((d : ℝ) / 2) ν ((d : ℝ) / u) / 4) D)
    (hfluc : ∀ β B C D, 0 < β → β ≤ (d : ℝ) / 2 →
      β * (1 + fluctuationBootstrapDelta ((d : ℝ) / 2) ν ((d : ℝ) / u)) < B → 0 < C → 0 < D →
        ∃ K > 0, ∀ i, AddEstimateAt (P i) (J i) u B C →
          LocFieldEstimateAt (P i) σ (J i) u (fluctuationBootstrapDelta ((d : ℝ) / 2) ν ((d : ℝ) / u))
            B D → FlucEstimateAt (P i) (J i) u β K) :
    ∃ C > 0, ∀ i, FlucEstimateAt (P i) (J i) u ((d : ℝ) / 2) C ∧
      ∀ s, 0 < s → s ≤ u →
        FlucEstimateAt (P i) (J i) s ((d : ℝ) / 2) ((Real.log 2) ^ (u⁻¹ - s⁻¹) * C) := by
  set b : ℝ := (d : ℝ) / 2 with hbdef
  set cap : ℝ := (d : ℝ) / u with hcapdef
  set δ : ℝ := fluctuationBootstrapDelta b ν cap with hδdef
  let w := min ν (cap - b)
  have hb : 0 < b := ha₀.trans_le hab
  have hcap : b < cap := half_dim_lt_dim_div hd (zero_lt_one.trans hu₁) hu₂
  have hw : 0 < w := lt_min hν (sub_pos.mpr hcap)
  have hδ : 0 < δ := div_pos hw (by linarith)
  have hwδ : (1 + b) * δ = w := mul_div_cancel₀ _ (by linarith : 1 + b ≠ 0)
  let h := δ / (2 * (1 + δ))
  have hh : 0 < h := div_pos hδ (by positivity)
  have hhδ : h * (1 + δ) = δ / 2 := by dsimp [h]; field_simp
  let F a := ∃ C > 0, ∀ i, FlucEstimateAt (P i) (J i) u a C
  have hend : F b := by
    apply fluctuation_endpoint_of_steps F ha₀ hab hh hbase
    rintro a β ha haβ hβb hinc ⟨C, hC, hF⟩
    let B := a * (1 + δ) + 3 * δ / 4
    have hab' : a ≤ b := haβ.trans hβb
    have hslack := mul_le_mul_of_nonneg_right hab' hδ.le
    have hA : B ≤ a + ν := by
      dsimp only [B]
      nlinarith only [hslack, hwδ, hδ, show w ≤ ν from min_le_left _ _]
    have hcap' : a * (1 + δ) + δ ≤ cap := by
      nlinarith only [hab', hslack, hwδ, show w ≤ cap - b from min_le_right _ _]
    have hgap : β * (1 + δ) < B := by
      dsimp [B]
      nlinarith [mul_le_mul_of_nonneg_right hinc (by positivity : 0 ≤ 1 + δ)]
    obtain ⟨CA, hCA, hAdd⟩ := hadd a C ha hab' hC
    obtain ⟨CL, hCL, hLoc⟩ := hloc a C ha hab' hC
    obtain ⟨K, hK, hFluc⟩ := hfluc β B CA CL (ha.trans_le haβ) hβb hgap hCA hCL
    refine ⟨K, hK, fun i => hFluc i ((hAdd i (hF i)).mono_rate hCA.le hA) ?_⟩
    have hrate : min (a * (1 + δ) + δ) cap - δ / 4 = B := by
      rw [min_eq_left hcap']
      dsimp [B]
      ring
    exact hrate ▸ hLoc i (hF i)
  obtain ⟨C, hC, hF⟩ := hend
  exact ⟨C, hC, fun i => ⟨hF i, fun _ hs hsu => (hF i).mono_exponent_sharp hs hsu⟩⟩

end QSH
