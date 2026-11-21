import QuantitativeStochasticHomogenization.AppA.OsNotation

/-!
# Appendix A: `O_s` bounds for almost surely measurable random variables

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix A, (A.1), with the convention of Remark 5.17: `AEOsBound P X s θ` holds if and only if
`X` agrees almost surely with a measurable `Y` satisfying `Y ≤ O_s(θ)`
(`aeOsBound_iff_exists_osBound`). The rules of `O_s` used for Lemma 5.24 follow: monotonicity,
homogeneity, finite sums for `s ≥ 1`, squares, and the fact that a deterministic lower bound of
an `O_1(θ)` variable is at most `θ`.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem OsBound.aeOsBound_of_ae_eq {X Y : Ω → ℝ} {s θ : ℝ} (h : OsBound P Y s θ)
    (hXY : X =ᵐ[P] Y) : AEOsBound P X s θ := by
  refine ⟨⟨Y, h.1, hXY⟩, h.2.1, h.2.2.1, ?_⟩
  calc (∫⁻ ω, ENNReal.ofReal (Real.exp ((θ⁻¹ * max (X ω) 0) ^ s)) ∂P)
      = ∫⁻ ω, ENNReal.ofReal (Real.exp ((θ⁻¹ * max (Y ω) 0) ^ s)) ∂P :=
        lintegral_congr_ae (hXY.mono fun ω hω => by simp only [hω])
    _ ≤ 2 := h.2.2.2

theorem AEOsBound.exists_osBound {X : Ω → ℝ} {s θ : ℝ} (h : AEOsBound P X s θ) :
    ∃ Y : Ω → ℝ, X =ᵐ[P] Y ∧ OsBound P Y s θ := by
  refine ⟨h.1.mk X, h.1.ae_eq_mk, h.1.measurable_mk, h.2.1, h.2.2.1, ?_⟩
  calc (∫⁻ ω, ENNReal.ofReal (Real.exp ((θ⁻¹ * max (h.1.mk X ω) 0) ^ s)) ∂P)
      = ∫⁻ ω, ENNReal.ofReal (Real.exp ((θ⁻¹ * max (X ω) 0) ^ s)) ∂P :=
        lintegral_congr_ae (h.1.ae_eq_mk.mono fun ω hω => by simp only [hω])
    _ ≤ 2 := h.2.2.2

theorem aeOsBound_iff_exists_osBound {X : Ω → ℝ} {s θ : ℝ} :
    AEOsBound P X s θ ↔ ∃ Y : Ω → ℝ, X =ᵐ[P] Y ∧ OsBound P Y s θ :=
  ⟨AEOsBound.exists_osBound, fun ⟨_, hXY, hY⟩ => hY.aeOsBound_of_ae_eq hXY⟩

theorem AEOsBound.mono_scale {X : Ω → ℝ} {s θ θ' : ℝ} (h : AEOsBound P X s θ) (hθ : θ ≤ θ') :
    AEOsBound P X s θ' := by
  obtain ⟨Y, hXY, hY⟩ := h.exists_osBound
  exact (hY.mono_scale hθ).aeOsBound_of_ae_eq hXY

theorem AEOsBound.of_le_ae {X Y : Ω → ℝ} {s θ : ℝ} (h : AEOsBound P X s θ)
    (hY : AEMeasurable Y P) (hle : ∀ᵐ ω ∂P, Y ω ≤ X ω) : AEOsBound P Y s θ := by
  obtain ⟨X', hXX', hX'⟩ := h.exists_osBound
  have hle' : ∀ᵐ ω ∂P, hY.mk Y ω ≤ X' ω := by
    filter_upwards [hle, hXX', hY.ae_eq_mk] with ω h1 h2 h3
    rw [← h2, ← h3]
    exact h1
  exact (hX'.of_le_ae hY.measurable_mk hle').aeOsBound_of_ae_eq hY.ae_eq_mk

theorem AEOsBound.const_mul {X : Ω → ℝ} {s θ c : ℝ} (h : AEOsBound P X s θ) (hc : 0 < c) :
    AEOsBound P (fun ω => c * X ω) s (c * θ) := by
  obtain ⟨Y, hXY, hY⟩ := h.exists_osBound
  exact (hY.const_mul hc).aeOsBound_of_ae_eq (hXY.mono fun ω hω => by simp only [hω])

theorem aeOsBound_finset_sum {ι : Type*} (I : Finset ι) (hI : I.Nonempty) {X : ι → Ω → ℝ}
    {s : ℝ} {θ : ι → ℝ} (hs : 1 ≤ s) (hX : ∀ i ∈ I, AEOsBound P (X i) s (θ i)) :
    AEOsBound P (fun ω => ∑ i ∈ I, X i ω) s (∑ i ∈ I, θ i) := by
  classical
  have hY : ∀ i, ∃ Y : Ω → ℝ, i ∈ I → X i =ᵐ[P] Y ∧ OsBound P Y s (θ i) := fun i => by
    by_cases hi : i ∈ I
    · obtain ⟨Y, h1, h2⟩ := (hX i hi).exists_osBound
      exact ⟨Y, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose Y hY using hY
  have hsum := osBound_finset_sum I hI hs fun i hi => (hY i hi).2
  refine hsum.aeOsBound_of_ae_eq ?_
  have hae : ∀ᵐ ω ∂P, ∀ i ∈ I, X i ω = Y i ω :=
    (Filter.eventually_all_finset I).mpr fun i hi => (hY i hi).1
  filter_upwards [hae] with ω hω
  exact Finset.sum_congr rfl hω

/-- `X ≤ O_1(θ)` and `X ≥ 0` give `X² ≤ O_{1/2}(θ²)`. -/
theorem AEOsBound.sq {X : Ω → ℝ} {θ : ℝ} (h : AEOsBound P X 1 θ) (hX0 : ∀ᵐ ω ∂P, 0 ≤ X ω) :
    AEOsBound P (fun ω => X ω ^ 2) (1 / 2) (θ ^ 2) := by
  obtain ⟨Y, hXY, hY⟩ := h.exists_osBound
  have hY' : OsBound P (fun ω => max (Y ω) 0) 1 θ := by
    refine ⟨hY.1.max measurable_const, hY.2.1, hY.2.2.1, ?_⟩
    calc (∫⁻ ω, ENNReal.ofReal (Real.exp ((θ⁻¹ * max (max (Y ω) 0) 0) ^ (1 : ℝ))) ∂P)
        = ∫⁻ ω, ENNReal.ofReal (Real.exp ((θ⁻¹ * max (Y ω) 0) ^ (1 : ℝ))) ∂P := by
          simp only [max_eq_left (le_max_right _ (0 : ℝ))]
      _ ≤ 2 := hY.2.2.2
  have h2 := hY'.rpow (fun ω => le_max_right _ _) (t := 2) two_pos
  have hθ : θ ^ (2 : ℝ) = θ ^ 2 := Real.rpow_natCast θ 2
  rw [hθ] at h2
  refine h2.aeOsBound_of_ae_eq ?_
  filter_upwards [hXY, hX0] with ω h1 h2'
  rw [← h1, max_eq_left h2', show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- A deterministic lower bound `η` of an `O_1(θ)` variable is at most `θ`. -/
theorem AEOsBound.le_of_le_ae [IsProbabilityMeasure P] {X : Ω → ℝ} {θ η : ℝ}
    (h : AEOsBound P X 1 θ) (hle : ∀ᵐ ω ∂P, η ≤ X ω) : η ≤ θ := by
  have hθ := h.2.2.1
  have hint : ENNReal.ofReal (Real.exp (θ⁻¹ * η)) ≤ 2 := by
    calc ENNReal.ofReal (Real.exp (θ⁻¹ * η))
        = ∫⁻ _, ENNReal.ofReal (Real.exp (θ⁻¹ * η)) ∂P := by
          rw [lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp ((θ⁻¹ * max (X ω) 0) ^ (1 : ℝ))) ∂P := by
          refine lintegral_mono_ae (hle.mono fun ω hω => ?_)
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
          rw [Real.rpow_one]
          exact mul_le_mul_of_nonneg_left (hω.trans (le_max_left _ _)) (inv_nonneg.mpr hθ.le)
      _ ≤ 2 := h.2.2.2
  have h2 : Real.exp (θ⁻¹ * η) ≤ 2 := by
    have := (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 2)).mp
      (by simpa using hint)
    exact this
  have h3 : θ⁻¹ * η < 1 := by
    have hlog : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    have := Real.log_le_log (Real.exp_pos _) h2
    rw [Real.log_exp] at this
    linarith
  have h4 : η < θ := by
    rw [inv_mul_lt_iff₀ hθ, mul_one] at h3
    exact h3
  exact h4.le

end QSH
