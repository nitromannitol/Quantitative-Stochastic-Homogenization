import QuantitativeStochasticHomogenization.Ch04.Sec02.UniformAdditivity
import QuantitativeStochasticHomogenization.Ch04.Sec02.UniformBootstrap
import QuantitativeStochasticHomogenization.Ch04.Sec05.Proposition412
import QuantitativeStochasticHomogenization.Ch05.Sec04.BlockEstimates
import QuantitativeStochasticHomogenization.Ch05.Sec04.JointHeatVersion

/-!
# Theorem 4.6 (i) and (iii) with constants chosen before the law

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Theorem 4.6 (i) and (iii) with `C(s, d, Λ)`, from the bootstrap of Section 4.2.

The quantity `J₁(Φ_{z,r}, p, q)` is identified with its finite-dimensional form (4.12) only almost
surely, so the bootstrap is run on a version of it. `IsBoundedJointVersion P J` states that `J` is
jointly measurable in the coefficients and the four parameters, bounded by `|Λ| + 1` for `p, q` in
the open unit ball (at every real radius), and almost surely equal to `J₁` at all parameters
simultaneously. Such a version exists for every law with a jointly measurable version of `J₁`
(`HasJointHeatVersion.exists_isBoundedJointVersion`), in particular for every law with
homogenization data (`hasJointHeatVersion_of_lawHypotheses`). All its stochastic statements are
those of `J₁`, with `AEOsBound` in place of `OsBound`.

The three inputs of the bootstrap with constants chosen before the law are stated for all such
versions: `UniformBaseFluctuation` (Proposition 4.3), `UniformImprovementOfAdditivity`
(Proposition 4.10, both conclusions) and `UniformLocalizationEstimates` (Proposition 4.11, with
the localization by measurable fields). Proposition 4.12 with constants chosen before the law is
`exists_flucEstimateAt_of_add_local`, applied with the local σ-algebras `F(U)` of (0.9).

Proved here: `exists_uniform_flucEstimateAt_half_dim`, `Fluc(s, d/2)` with one constant for all
laws and versions, from the bootstrap at the exponent `u = 1 + s/2` (`uniform_flucEstimate_half_dim`)
and the conversion `O_u ⊂ O_s`; Theorem 4.6 (iii) uniform in the law, `uniformFluctuationJ1_of_bootstrap`;
and Theorem 4.6 (i) uniform in the law, `uniformAdditivityJ1_of_bootstrap`, which is the statement
`UniformAdditivityJ1` from the second conclusion of Proposition 4.10 at `α = d/2`.
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## Bounded jointly measurable versions of `J₁` -/

/-- `|J₁(Φ_{z,r}, p, q)| ≤ |Λ| + 1` for `p, q` in the open unit ball and every real `r`
(`Φ_{z,r} = Φ_{z,|r|}`, and `Φ_{z,0} = 0`). -/
theorem abs_J1Heat_le_of_norm_lt_one (hd : 0 < d) (a : CoefficientField d Λ) (z : Vec d)
    (r : ℝ) {p q : Vec d} (hp : euclideanNorm p < 1) (hq : euclideanNorm q < 1) :
    |J1Heat a z r p q| ≤ |Λ| + 1 := by
  have hm : Integrable (heatKernel z r) ∧ (∫ x, heatKernel z r x) ≤ 1 := by
    by_cases hr : r = 0
    · subst r
      have hzero : heatKernel z 0 = 0 := funext (heatKernel_at_zero_radius hd z)
      simp [hzero]
    · have hpos := abs_pos.mpr hr
      have he : heatKernel z r = heatKernel z |r| := by funext x; simp [heatKernel]
      rw [he]
      exact ⟨integrable_heatKernel z hpos, (integral_heatKernel z hpos).le⟩
  have h0 := J1_nonneg a (heatKernel_nonneg z r) hm.1 hm.2 p q
  have h1 := J1_le a (heatKernel_nonneg z r) hm.1 hm.2 p q
  have hp' : euclideanSq p ≤ 1 := by
    rw [← euclideanNorm_sq]; nlinarith [euclideanNorm_nonneg p]
  have hq' : euclideanSq q ≤ 1 := by
    rw [← euclideanNorm_sq]; nlinarith [euclideanNorm_nonneg q]
  change |J1 a (heatKernel z r) p q| ≤ _
  rw [abs_of_nonneg h0]
  exact h1.trans (add_le_add
    ((mul_le_mul_of_nonneg_right (le_abs_self Λ) (euclideanSq_nonneg p)).trans
      (by simpa using mul_le_mul_of_nonneg_left hp' (abs_nonneg Λ))) hq')

/-- **A bounded jointly measurable version of `J₁`**: `J` is jointly measurable in the
coefficients and the parameters `(z, r, p, q)`, bounded by `|Λ| + 1` for `p, q` in the open unit
ball, and almost surely equal to `J₁(Φ_{z,r}, p, q)` at all parameters. -/
def IsBoundedJointVersion (P : Measure (CoefficientField d Λ))
    (J : CoefficientField d Λ → Vec d → ℝ → Vec d → Vec d → ℝ) : Prop :=
  Measurable (fun w : CoefficientField d Λ × HeatObservationIndex d =>
      J w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2) ∧
    (∀ a z r p q, euclideanNorm p < 1 → euclideanNorm q < 1 → |J a z r p q| ≤ |Λ| + 1) ∧
    ∀ᵐ a ∂P, ∀ z r p q, J a z r p q = J1Heat a z r p q

theorem IsBoundedJointVersion.measurable_slice {P : Measure (CoefficientField d Λ)}
    {J : CoefficientField d Λ → Vec d → ℝ → Vec d → Vec d → ℝ} (hJ : IsBoundedJointVersion P J)
    (r : ℝ) (p q : Vec d) :
    Measurable fun w : CoefficientField d Λ × Vec d => J w.1 w.2 r p q := by
  have hg : Measurable fun w : CoefficientField d Λ × Vec d =>
      ((w.1, (w.2, r, p, q)) : CoefficientField d Λ × HeatObservationIndex d) :=
    measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
  exact hJ.1.comp hg

/-- A jointly measurable version of `J₁` can be chosen bounded by `|Λ| + 1` everywhere. -/
theorem HasJointHeatVersion.exists_isBoundedJointVersion (hd : 0 < d)
    {P : Measure (CoefficientField d Λ)} (hV : HasJointHeatVersion P) :
    ∃ J, IsBoundedJointVersion P J := by
  let Q := fun (_ : CoefficientField d Λ) (V : HeatObservationIndex d → ℝ) =>
    ∀ z r p q, euclideanNorm p < 1 → euclideanNorm q < 1 → |V (z, r, p, q)| ≤ |Λ| + 1
  have hzero : ∀ a, Q a 0 := by
    intro a z r p q _ _
    simpa using add_nonneg (abs_nonneg Λ) zero_le_one
  obtain ⟨V, hVm, hEq, hB⟩ := hV.with_pathwise_property Q hzero
    (ae_of_all _ fun a z r p q hp hq => abs_J1Heat_le_of_norm_lt_one hd a z r hp hq)
  refine ⟨fun a z r p q => V a (z, r, p, q), hVm, fun a z r p q hp hq => hB a z r p q hp hq, ?_⟩
  filter_upwards [hEq] with a ha
  exact fun z r p q => ha (z, r, p, q)

/-- `OsBound` passes to an almost surely equal random variable as `AEOsBound`. -/
theorem OsBound.aeOsBound_congr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → ℝ}
    {s θ : ℝ} (h : OsBound P X s θ) (hXY : X =ᵐ[P] Y) : AEOsBound P Y s θ := by
  obtain ⟨hm, hs, hθ, hE⟩ := h
  refine ⟨hm.aemeasurable.congr hXY, hs, hθ, ?_⟩
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp ((θ⁻¹ * max (Y ω) 0) ^ s)) ∂P
      = ∫⁻ ω, ENNReal.ofReal (Real.exp ((θ⁻¹ * max (X ω) 0) ^ s)) ∂P :=
        lintegral_congr_ae (by
          filter_upwards [hXY] with ω h
          rw [h])
    _ ≤ 2 := hE

/-- `Fluc(s, α)` for a version gives `Fluc(s, α)` for `J₁` with `AEOsBound`. -/
theorem FlucEstimateAt.of_version {P : Measure (CoefficientField d Λ)}
    {J : CoefficientField d Λ → Vec d → ℝ → Vec d → Vec d → ℝ}
    (hJ : ∀ᵐ a ∂P, ∀ z r p q, J a z r p q = J1Heat a z r p q) {s α C : ℝ}
    (h : FlucEstimateAt P J s α C) (z : Vec d) (r : ℝ) (hr : 1 ≤ r) (p q : Vec d)
    (hp : euclideanNorm p < 1) (hq : euclideanNorm q < 1) :
    Integrable (fun a => J1Heat a z r p q) P ∧
      AEOsBound P (fun a => |J1Heat a z r p q - ∫ a', J1Heat a' z r p q ∂P|) s (C * r ^ (-α)) := by
  obtain ⟨hi, hb⟩ := h z r hr p q hp hq
  have he : (fun a => J a z r p q) =ᵐ[P] fun a => J1Heat a z r p q :=
    hJ.mono fun a ha => ha z r p q
  have hint : ∫ a', J a' z r p q ∂P = ∫ a', J1Heat a' z r p q ∂P := integral_congr_ae he
  refine ⟨hi.congr he, hb.aeOsBound_congr ?_⟩
  filter_upwards [hJ] with a ha
  rw [ha z r p q, hint]

/-- `Add(s, α)` for a version gives `Add(s, α)` for `J₁` with `AEOsBound`. -/
theorem AddEstimateAt.of_version {P : Measure (CoefficientField d Λ)}
    {J : CoefficientField d Λ → Vec d → ℝ → Vec d → Vec d → ℝ}
    (hJ : ∀ᵐ a ∂P, ∀ z r p q, J a z r p q = J1Heat a z r p q) {s α C : ℝ}
    (h : AddEstimateAt P J s α C) (z : Vec d) (r R : ℝ) (hr : 1 ≤ r) (hrR : r < R)
    (p q : Vec d) (hp : euclideanNorm p < 1) (hq : euclideanNorm q < 1) :
    (∀ᵐ a ∂P, Integrable
        (fun x => heatKernel z (Real.sqrt (R ^ 2 - r ^ 2)) x * J1Heat a x r p q)) ∧
      AEOsBound P (fun a => |J1Heat a z R p q -
        ∫ x, heatKernel z (Real.sqrt (R ^ 2 - r ^ 2)) x * J1Heat a x r p q|) s (C * r ^ (-α)) := by
  obtain ⟨hi, hb⟩ := h z r R hr hrR p q hp hq
  have hfun : ∀ᵐ a ∂P, (fun x => heatKernel z (Real.sqrt (R ^ 2 - r ^ 2)) x * J a x r p q) =
      fun x => heatKernel z (Real.sqrt (R ^ 2 - r ^ 2)) x * J1Heat a x r p q := by
    filter_upwards [hJ] with a ha
    funext x
    rw [ha x r p q]
  refine ⟨?_, hb.aeOsBound_congr ?_⟩
  · filter_upwards [hi, hfun] with a ha hf
    rwa [← hf]
  · filter_upwards [hJ, hfun] with a ha hf
    rw [ha z R p q, hf]

/-! ## The three inputs with constants chosen before the law -/

/-- **Proposition 4.3 with constants chosen before the law**: for every `u ∈ (1, 2)` there are
`a₀ > 0` and `C > 0` such that `Fluc(u, a₀)` holds with constant `C` for every bounded jointly
measurable version of `J₁`, under every law satisfying the assumptions. -/
def UniformBaseFluctuation (d : ℕ) (Λ : ℝ) : Prop :=
  ∀ u : ℝ, 1 < u → u < 2 → ∃ a₀ C : ℝ, 0 < a₀ ∧ 0 < C ∧
    ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∀ J, IsBoundedJointVersion P J → FlucEstimateAt P J u a₀ C

/-- **Proposition 4.10 with constants chosen before the law**: for every `s ∈ (0, 2)` there is
`η > 0` such that for `α ∈ (0, d/2]` and every constant `C` there is `D` with
`Fluc(s, α) ⟹ Add(s, α + η) ∧ Add(s/2, 2α)`, from constant `C` to constant `D`, for every bounded
jointly measurable version of `J₁` under every law satisfying the assumptions. -/
def UniformImprovementOfAdditivity (d : ℕ) (Λ : ℝ) : Prop :=
  ∀ s : ℝ, 0 < s → s < 2 → ∃ η : ℝ, 0 < η ∧ ∀ α C : ℝ, 0 < α → α ≤ (d : ℝ) / 2 → 0 < C →
    ∃ D : ℝ, 0 < D ∧ ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∀ J, IsBoundedJointVersion P J → FlucEstimateAt P J s α C →
        AddEstimateAt P J s (α + η) D ∧ AddEstimateAt P J (s / 2) (2 * α) D

/-- **Proposition 4.11 with constants chosen before the law**, with the localization by
measurable fields and the local σ-algebras of (0.9), at the stochastic exponents `s ∈ (1, 2)` and
the spatial exponents `α ∈ (0, d/2]` used by the bootstrap: for `δ, η > 0` and every constant `C`
there is `D` with `Fluc(s, α) ⟹ Loc(s, δ, (α(1+δ) + δ) ∧ d/s - η)`, from constant `C` to constant
`D`, for every bounded jointly measurable version of `J₁` under every law satisfying the
assumptions. -/
def UniformLocalizationEstimates (d : ℕ) (Λ : ℝ) : Prop :=
  ∀ s α δ η C : ℝ, 1 < s → s < 2 → 0 < α → α ≤ (d : ℝ) / 2 → 0 < δ → 0 < η → 0 < C →
    ∃ D : ℝ, 0 < D ∧ ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∀ J, IsBoundedJointVersion P J → FlucEstimateAt P J s α C →
        LocFieldEstimateAt P localSigma J s δ (min (α * (1 + δ) + δ) ((d : ℝ) / s) - η) D

/-! ## The bootstrap -/

/-- **Theorem 4.6 (iii) for the versions, with one constant for all laws**: for `s ∈ (0, 2)`
there is `C` with `Fluc(s, d/2)` with constant `C` for every bounded jointly measurable version of
`J₁` under every law satisfying the assumptions. -/
theorem exists_uniform_flucEstimateAt_half_dim (hd : 2 ≤ d)
    (hbase : UniformBaseFluctuation d Λ) (h410 : UniformImprovementOfAdditivity d Λ)
    (h411 : UniformLocalizationEstimates d Λ) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∀ J, IsBoundedJointVersion P J → FlucEstimateAt P J s ((d : ℝ) / 2) C := by
  set u : ℝ := 1 + s / 2 with hu
  have hu1 : 1 < u := by linarith
  have hu2 : u < 2 := by linarith
  have hsu : s ≤ u := by linarith
  have hd1 : 1 ≤ d := by omega
  have hb2 : 0 < (d : ℝ) / 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hcap : (d : ℝ) / 2 < (d : ℝ) / u := half_dim_lt_dim_div hd1 (by linarith) hu2
  let ι := {x : Measure (CoefficientField d Λ) ×
    (CoefficientField d Λ → Vec d → ℝ → Vec d → Vec d → ℝ) //
      LawHypotheses x.1 ∧ IsBoundedJointVersion x.1 x.2}
  have hprob : ∀ i : ι, IsProbabilityMeasure i.1.1 := fun i => i.2.1.1
  obtain ⟨a₁, C₀, ha₁, hC₀, hb⟩ := hbase u hu1 hu2
  obtain ⟨ν, hν, hadd⟩ := h410 u (by linarith) hu2
  have hδ : 0 < fluctuationBootstrapDelta ((d : ℝ) / 2) ν ((d : ℝ) / u) :=
    fluctuationBootstrapDelta_pos hb2.le hν hcap
  obtain ⟨C, hC, hF⟩ := uniform_flucEstimate_half_dim (ι := ι) (fun i => i.1.1) localSigma
    (fun i => i.1.2) hd1 hu1 hu2 (lt_min ha₁ hb2) (min_le_right _ _) hν
    ⟨C₀, hC₀, fun i => (hb i.1.1 i.2.1 i.1.2 i.2.2).mono_rate hC₀.le (min_le_left _ _)⟩
    (fun a C ha hab hC => by
      obtain ⟨D, hD, h⟩ := hadd a C ha hab hC
      exact ⟨D, hD, fun i hi => (h i.1.1 i.2.1 i.1.2 i.2.2 hi).1⟩)
    (fun a C ha hab hC => by
      obtain ⟨D, hD, h⟩ := h411 u a (fluctuationBootstrapDelta ((d : ℝ) / 2) ν ((d : ℝ) / u))
        (fluctuationBootstrapDelta ((d : ℝ) / 2) ν ((d : ℝ) / u) / 4) C hu1 hu2 ha hab hδ
        (by positivity) hC
      exact ⟨D, hD, fun i hi => h i.1.1 i.2.1 i.1.2 i.2.2 hi⟩)
    (fun β B C D hβ hβd hgap hC hD => by
      obtain ⟨K, hK, h⟩ := exists_flucEstimateAt_of_add_local (Ω := CoefficientField d Λ)
        (F := localSigma) (M := |Λ| + 1) hd1 localSigma_mono localSigma_le hC hD hu1 hu2.le hβ
        hβd hδ hgap
      exact ⟨K, hK, fun i hA hL => h i.1.1 (hasUnitRange_of_lawHypotheses i.2.1) i.1.2
        i.2.2.2.1 i.2.2.measurable_slice hA hL⟩)
  refine ⟨Real.log 2 ^ (u⁻¹ - s⁻¹) * C, mul_pos (Real.rpow_pos_of_pos
    (Real.log_pos one_lt_two) _) hC, fun P hP J hJ => ?_⟩
  exact (hF ⟨(P, J), hP, hJ⟩).2 s hs0 hsu

/-- **Theorem 4.6 (iii) with constants chosen before the law**: for every `s ∈ (0, 2)` there is
`C(s, d, Λ)` with `|J₁(Φ_{z,r}, p, q) - E[J₁(Φ_{z,r}, p, q)]| ≤ O_s(C r^{-d/2})` for every law
satisfying the assumptions, `z`, `r ≥ 1` and `p, q` in the open unit ball. -/
def UniformFluctuationJ1 : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ Λ s : ℝ, 1 < Λ → 0 < s → s < 2 → ∃ C : ℝ, 0 < C ∧
    ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
    ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
      euclideanNorm p < 1 → euclideanNorm q < 1 →
      Integrable (fun a => J1Heat a z r p q) P ∧
      AEOsBound P (fun a => |J1Heat a z r p q - ∫ a', J1Heat a' z r p q ∂P|) s
        (C * r ^ (-((d : ℝ) / 2)))

/-- **Theorem 4.6 (iii) with constants chosen before the law** from Propositions 4.3, 4.10 and
4.11 with constants chosen before the law and a jointly measurable version of `J₁` for every
law. -/
theorem uniformFluctuationJ1_of_bootstrap
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → UniformBaseFluctuation d Λ ∧
      UniformImprovementOfAdditivity d Λ ∧ UniformLocalizationEstimates d Λ)
    (hV : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ P : Measure (CoefficientField d Λ),
      LawHypotheses P → HasJointHeatVersion P) :
    UniformFluctuationJ1 := by
  intro d hd Λ s hΛ hs0 hs2
  obtain ⟨hbase, h410, h411⟩ := h d hd Λ hΛ
  obtain ⟨C, hC, hF⟩ := exists_uniform_flucEstimateAt_half_dim hd hbase h410 h411 hs0 hs2
  refine ⟨C, hC, fun P hP => ?_⟩
  obtain ⟨J, hJ⟩ := (hV d hd Λ hΛ P hP).exists_isBoundedJointVersion (by omega)
  exact (hF P hP J hJ).of_version hJ.2.2

/-- **Theorem 4.6 (i) with constants chosen before the law** (`UniformAdditivityJ1`) from
Propositions 4.3, 4.10 and 4.11 with constants chosen before the law and a jointly measurable
version of `J₁` for every law: the second conclusion of Proposition 4.10 at `α = d/2`. -/
theorem uniformAdditivityJ1_of_bootstrap
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → UniformBaseFluctuation d Λ ∧
      UniformImprovementOfAdditivity d Λ ∧ UniformLocalizationEstimates d Λ)
    (hV : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ P : Measure (CoefficientField d Λ),
      LawHypotheses P → HasJointHeatVersion P) :
    UniformAdditivityJ1 := by
  intro d hd Λ s hΛ hs0 hs2
  obtain ⟨hbase, h410, h411⟩ := h d hd Λ hΛ
  have hb2 : 0 < (d : ℝ) / 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨C, hC, hF⟩ := exists_uniform_flucEstimateAt_half_dim hd hbase h410 h411 hs0 hs2
  obtain ⟨η, -, hadd⟩ := h410 s hs0 hs2
  obtain ⟨D, hD, hA⟩ := hadd ((d : ℝ) / 2) C hb2 le_rfl hC
  refine ⟨D, hD, fun P hP z r R hr hrR p q hp hq => ?_⟩
  obtain ⟨J, hJ⟩ := (hV d hd Λ hΛ P hP).exists_isBoundedJointVersion (by omega)
  have hAd := (hA P hP J hJ (hF P hP J hJ)).2
  rw [show 2 * ((d : ℝ) / 2) = d by ring] at hAd
  exact hAd.of_version hJ.2.2 z r R hr hrR p q hp hq

end QSH
