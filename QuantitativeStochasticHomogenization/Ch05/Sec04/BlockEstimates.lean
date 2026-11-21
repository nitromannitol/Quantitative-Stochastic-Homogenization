import QuantitativeStochasticHomogenization.Ch05.Sec04.Lemma529Clt
import QuantitativeStochasticHomogenization.Frozen.BlockCLT
import QuantitativeStochasticHomogenization.Ch04.Sec06.HeatScaleSummation

/-!
# Lemma 5.29 for the localized energy

Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, Lemma 5.29, for the localized energy `J₁^{(δ)}` of Section 4.4 (`familyJ1`). The
statements of Section 5.4 use two properties of `J₁^{(δ)}` beyond (5.85):

* `LocalizedFieldInput`: `J₁^{(δ)}(·, ·, r, p, q)` is bounded and, restricted to a set of centers,
  measurable for the coefficients in the `r^{1+δ}`-neighbourhood of that set (the construction of
  Section 4.4 gives a jointly measurable family; the book uses it when it integrates
  `x ↦ J₁^{(δ)}(x, r)` over cubes);
* `LocalizedAdditivityInput`: the additivity (5.88), deduced in the book from `Add(s, α)` for `J₁`
  (5.87) and the localization (5.85).

From them, the centered localized energies are centered local additive fields
(`CenteredLocalFields`), and Lemma 5.29 (i) is `QSH.Frozen.blockCLT` (`blockCLT_of_inputs`).
-/

open MeasureTheory ProbabilityTheory

namespace QSH

variable {d : ℕ} {Λ : ℝ}

theorem localSigma_mono : Monotone (localSigma (d := d) (Λ := Λ)) := by
  intro U V hUV
  unfold localSigma
  refine iSup_le fun u => ?_
  exact le_iSup_of_le ⟨u.1, u.2.trans hUV⟩ le_rfl

theorem localSigma_le (U : Set (Vec d)) :
    localSigma (Λ := Λ) U ≤ (inferInstance : MeasurableSpace (CoefficientField d Λ)) := by
  unfold localSigma
  refine iSup_le fun u => ?_
  exact le_iSup_of_le u.1 le_rfl

theorem hasUnitRange_of_lawHypotheses {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P) :
    HasUnitRange P (localSigma (d := d) (Λ := Λ)) :=
  fun U W hU hW hsep => hP.2.2 U W hU hW hsep

theorem clampAt_of_abs_le {M v : ℝ} (hv : |v| ≤ M) : clampAt M v = v := by
  unfold clampAt
  rw [abs_le] at hv
  rw [min_eq_right hv.2, max_eq_right hv.1]

theorem familyJ1_of_lt_two {Λ δ γ α σ θ C₀ : ℝ} (W : LocalizedFamily d Λ δ γ α σ θ C₀)
    (a : CoefficientField d Λ) (z : Vec d) {r : ℝ} (hr : r < 2) (p q : Vec d) :
    familyJ1 W a z r p q = 0 := by
  simp only [familyJ1, not_le.mpr hr, ↓reduceDIte]

/-- **Boundedness and joint locality of the localized energy** (Section 4.4). -/
def LocalizedFieldInput : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ Λ s δ γ η : ℝ, 1 < Λ → BlockWindow d s δ γ η →
  ∀ α σ θ C₀ C' : ℝ, LocalizationConstants d δ γ α σ θ C₀ C' →
  ∃ M : ℝ, 0 < M ∧ ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
  ∀ W : LocalizedFamily d Λ δ γ α σ θ C₀, IsLocalization P s δ γ α σ θ C₀ C' W →
  ∀ r : ℝ, 2 ≤ r → ∀ p q : Vec d, euclideanNorm p < 1 → euclideanNorm q < 1 →
    (∀ a z, |familyJ1 W a z r p q| ≤ M) ∧
    ∀ U : Set (Vec d), MeasurableSet U →
      @Measurable (CoefficientField d Λ × Vec d) ℝ
        (@Prod.instMeasurableSpace (CoefficientField d Λ) (Vec d)
          (localSigma (euclideanThickening (r ^ (1 + δ)) U)) _) _
        (fun w => U.indicator (fun x => familyJ1 W w.1 x r p q) w.2)

/-- **The additivity (5.88) of the localized energy** at the exponent `γ`. -/
def LocalizedAdditivityInput : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ Λ s δ γ η : ℝ, 1 < Λ → BlockWindow d s δ γ η →
  ∀ α σ θ C₀ C' : ℝ, LocalizationConstants d δ γ α σ θ C₀ C' →
  ∃ CA : ℝ, 0 < CA ∧ ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
  ∀ W : LocalizedFamily d Λ δ γ α σ θ C₀, IsLocalization P s δ γ α σ θ C₀ C' W →
  ∀ (z : Vec d) (r₁ r : ℝ), 2 ≤ r₁ → r₁ < r → ∀ p q : Vec d,
    euclideanNorm p < 1 → euclideanNorm q < 1 →
    OsBound P (fun a => |familyJ1 W a z r p q -
      ∫ y, heatKernel z (Real.sqrt (r ^ 2 - r₁ ^ 2)) y * familyJ1 W a y r₁ p q|) s (CA * r₁ ^ (-γ))

/-- **The centered localized energy as centered local additive fields**: for a law satisfying
(P1)-(P2) and a localization satisfying the two inputs, the centered truncations of
`r ↦ J₁^{(δ)}(·, ·, r, p, q)` are centered local fields with constants depending only on the
structural constants. -/
theorem exists_centeredLocalFields_familyJ1 (hloc : LocalizedFieldInput)
    (hadd : LocalizedAdditivityInput) {d : ℕ} (hd : 2 ≤ d) {Λ s δ γ η : ℝ} (hΛ : 1 < Λ)
    (hw : BlockWindow d s δ γ η) {α σ θ C₀ C' : ℝ} (hc : LocalizationConstants d δ γ α σ θ C₀ C') :
    ∃ M A : ℝ, 0 < M ∧ 0 < A ∧ ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∀ W : LocalizedFamily d Λ δ γ α σ θ C₀, IsLocalization P s δ γ α σ θ C₀ C' W →
      ∀ p q : Vec d, euclideanNorm p < 1 → euclideanNorm q < 1 →
      ∃ X : @CenteredLocalFields d (CoefficientField d Λ) _ P localSigma s δ γ (2 * M) A,
        ∀ r : ℝ, 1 ≤ r → ∀ a x, X.field r a x =
          familyJ1 W a x r p q - ∫ a', familyJ1 W a' x r p q ∂P := by
  obtain ⟨M, hM, hfield⟩ := hloc d hd Λ s δ γ η hΛ hw α σ θ C₀ C' hc
  obtain ⟨CA, hCA, hAdd⟩ := hadd d hd Λ s δ γ η hΛ hw α σ θ C₀ C' hc
  obtain ⟨hs1, hs2, hδ, hγ1, hγ2, hη1, hηγ, hη2⟩ := hw
  have hγ : 0 < γ := by
    have : 0 < (d : ℝ) / 2 * (1 + δ) := by positivity
    linarith
  obtain ⟨C₁, C₂, hC₁, hC₂, hT⟩ := exists_additive_truncatedField
    (Ω := CoefficientField d Λ) (d := d) hs1 hs2.le
  have hl2 : 0 < Real.log 2 ^ s⁻¹ := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _
  set CA' : ℝ := max CA (2 ^ γ * (M / Real.log 2 ^ s⁻¹)) with hCA'def
  have hCA' : 0 < CA' := hCA.trans_le (le_max_left _ _)
  set A : ℝ := C₁ * (1 + CA') + C₂ * 1 with hAdef
  refine ⟨M, A, hM, by positivity, fun P hP W hW p q hp hq => ?_⟩
  have : IsProbabilityMeasure P := hP.1
  set Jδ : ℝ → CoefficientField d Λ → Vec d → ℝ := fun r a x => familyJ1 W a x r p q with hJδdef
  have hJb : ∀ a z r, |familyJ1 W a z r p q| ≤ M := by
    intro a z r
    by_cases hr : 2 ≤ r
    · exact (hfield P hP W hW r hr p q hp hq).1 a z
    · rw [familyJ1_of_lt_two W a z (not_le.mp hr), abs_zero]
      exact hM.le
  have hJδloc : ∀ r, 1 ≤ r → ∀ U : Set (Vec d), MeasurableSet U →
      @Measurable (CoefficientField d Λ × Vec d) ℝ
        (@Prod.instMeasurableSpace (CoefficientField d Λ) (Vec d)
          (localSigma (euclideanThickening (r ^ (1 + δ)) U)) _) _
        (fun w => U.indicator (Jδ r w.1) w.2) := by
    intro r _ U hU
    by_cases hr : 2 ≤ r
    · exact (hfield P hP W hW r hr p q hp hq).2 U hU
    · have e : (fun w : CoefficientField d Λ × Vec d => U.indicator (Jδ r w.1) w.2) =
          fun _ => 0 := by
        funext w
        simp only [hJδdef, familyJ1_of_lt_two W _ _ (not_le.mp hr)]
        by_cases h : w.2 ∈ U <;> simp [h]
      rw [e]
      exact measurable_const
  have hJm : ∀ r, Measurable fun w : CoefficientField d Λ × Vec d => familyJ1 W w.1 w.2 r p q := by
    intro r
    by_cases hr : 1 ≤ r
    · have h := hJδloc r hr Set.univ MeasurableSet.univ
      simp only [Set.indicator_univ] at h
      exact measurable_prod_of_le (localSigma_le _) h
    · have e : (fun w : CoefficientField d Λ × Vec d => familyJ1 W w.1 w.2 r p q) = fun _ => 0 := by
        funext w
        exact familyJ1_of_lt_two W _ _ (by linarith [not_le.mp hr]) p q
      rw [e]
      exact measurable_const
  have hJδm : ∀ r, 1 ≤ r → Measurable fun w : CoefficientField d Λ × Vec d => Jδ r w.1 w.2 :=
    fun r _ => hJm r
  have hcl : ∀ r, 1 ≤ r → ∀ z, OsBound P (fun a => |familyJ1 W a z r p q - Jδ r a z|) s
      (1 * r ^ (-γ)) := by
    intro r hr z
    have h0 := osBound_zero (P := P) (by linarith : (0 : ℝ) < s)
      (by positivity : (0 : ℝ) < 1 * r ^ (-γ))
    have e : (fun a => |familyJ1 W a z r p q - Jδ r a z|) = fun _ => (0 : ℝ) := by
      funext a
      simp [hJδdef]
    rw [e]
    exact h0
  have hadd' : ∀ (z : Vec d) (r₁ r : ℝ), 1 ≤ r₁ → r₁ < r → OsBound P (fun a =>
      |familyJ1 W a z r p q - ∫ y, heatKernel z (Real.sqrt (r ^ 2 - r₁ ^ 2)) y *
        familyJ1 W a y r₁ p q|) s (CA' * r₁ ^ (-γ)) := by
    intro z r₁ r hr₁ hr
    by_cases h2 : 2 ≤ r₁
    · exact (hAdd P hP W hW z r₁ r h2 hr p q hp hq).mono_scale
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _))
    · have hr₁2 : r₁ < 2 := not_le.mp h2
      have e : (fun a => |familyJ1 W a z r p q - ∫ y, heatKernel z (Real.sqrt (r ^ 2 - r₁ ^ 2)) y *
          familyJ1 W a y r₁ p q|) = fun a => |familyJ1 W a z r p q| := by
        funext a
        simp only [familyJ1_of_lt_two W a _ hr₁2, mul_zero, integral_zero, sub_zero]
      rw [e]
      have hb := osBound_of_le_const (P := P) (continuous_abs.measurable.comp
        ((hJm r).comp (measurable_id.prodMk measurable_const))) (by linarith : (0 : ℝ) < s) hM
        (Filter.Eventually.of_forall fun a => hJb a z r)
      refine hb.mono_scale ?_
      have hr₁γ : (2 : ℝ) ^ (-γ) ≤ r₁ ^ (-γ) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) hr₁2.le (by linarith)
      have h22 : (2 : ℝ) ^ γ * (2 : ℝ) ^ (-γ) = 1 := by
        rw [← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero]
      calc M / Real.log 2 ^ s⁻¹ = (2 ^ γ * (M / Real.log 2 ^ s⁻¹)) * (2 : ℝ) ^ (-γ) := by
            rw [mul_comm (2 ^ γ), mul_assoc, h22, mul_one]
        _ ≤ CA' * r₁ ^ (-γ) := mul_le_mul (le_max_right _ _) hr₁γ (by positivity) hCA'.le
  let X : @CenteredLocalFields d (CoefficientField d Λ) _ P localSigma s δ γ (2 * M) A :=
    { field := truncatedField P M Jδ
      abs_le := abs_truncatedField_le hM.le Jδ
      measurable := measurable_truncatedField hJδm
      isLocal := isLocal_truncatedField hM.le hJδloc hJδm
      centered := integral_truncatedField hM.le hJδm
      additive := hT P (fun a z r _ _ => familyJ1 W a z r p q) hM.le p q Jδ hγ.le one_pos hCA'
        (fun a z r => hJb a z r) (fun r => hJm r) hJδm hcl hadd' }
  refine ⟨X, fun r hr a x => ?_⟩
  show truncatedField P M Jδ r a x = _
  rw [truncatedField_of_one_le hr, clampAt_of_abs_le (hJb a x r)]
  simp only [hJδdef, clampAt_of_abs_le (hJb _ x r)]

theorem centeredBlock_eq_integral_indicator {d : ℕ} {Λ : ℝ} (P : Measure (CoefficientField d Λ))
    (J : CoefficientField d Λ → Vec d → ℝ → Vec d → Vec d → ℝ) (a : CoefficientField d Λ)
    (z : Vec d) (R r : ℝ) (f : Vec d → ℝ) (p q : Vec d) :
    centeredBlock P J a z R r f p q = R ^ (-(d : ℝ)) *
      ∫ x, (cube z R).indicator f x * (J a x r p q - ∫ a', J a' x r p q ∂P) := by
  unfold centeredBlock
  congr 1
  rw [← integral_indicator (measurableSet_cube z R)]
  congr 1
  funext x
  by_cases hx : x ∈ cube z R
  · simp only [Set.indicator_of_mem hx]
  · simp only [Set.indicator_of_notMem hx, zero_mul]

theorem BlockWindow.exists_eta₂ {d : ℕ} {s δ γ η : ℝ} (hw : BlockWindow d s δ γ η) :
    ∃ η₂ : ℝ, η < η₂ ∧ η₂ * (1 + δ) < 1 := by
  obtain ⟨-, -, hδ, -, -, -, -, hη2⟩ := hw
  refine ⟨(η + (1 + δ)⁻¹) / 2, by linarith, ?_⟩
  have h := mul_lt_mul_of_pos_right (show (η + (1 + δ)⁻¹) / 2 < (1 + δ)⁻¹ by linarith)
    (show (0 : ℝ) < 1 + δ by linarith)
  rwa [inv_mul_cancel₀ (by linarith)] at h

/-- **Lemma 5.29 (i)** for the localized energy (`QSH.Frozen.blockCLT`), from the two properties
`LocalizedFieldInput` and `LocalizedAdditivityInput` of the localization. -/
theorem blockCLT_of_inputs (hloc : LocalizedFieldInput) (hadd : LocalizedAdditivityInput) :
    QSH.Frozen.blockCLT := by
  intro d hd Λ s δ γ η hΛ hw α σ θ C₀ C' hc
  obtain ⟨M, A, hM, hA, hX⟩ := exists_centeredLocalFields_familyJ1 hloc hadd hd hΛ hw hc
  obtain ⟨η₂, hηη₂, hη₂⟩ := hw.exists_eta₂
  obtain ⟨hs1, hs2, hδ, hγ1, -, hη1, hηγ, -⟩ := hw
  have hd1 : 1 ≤ d := by omega
  have hη0 : 0 < η := by linarith
  obtain ⟨Cb, hCb, hblk⟩ := exists_blockBound_all_scales (Ω := CoefficientField d Λ)
    (F := localSigma) (δ := δ) (α := γ) (B := 2 * M) (A := A) hd1 localSigma_mono hs1 hs2.le
    (by positivity) hA (β := (d : ℝ) / 2) (by positivity) le_rfl hδ hη0 hηη₂ hη₂ hηγ
  refine ⟨(8 : ℝ) ^ s⁻¹ * (4 * Cb), by positivity,
    fun P hP W hW R r hR hr2 hRr hrR z p q hp hq f hf hf1 => ?_⟩
  have : IsProbabilityMeasure P := hP.1
  obtain ⟨X, hXeq⟩ := hX P hP W hW p q hp hq
  have hf' : Measurable ((cube z R).indicator f) := hf.indicator (measurableSet_cube z R)
  have hf1' : ∀ x, |(cube z R).indicator f x| ≤ 1 := by
    intro x
    by_cases hx : x ∈ cube z R
    · rw [Set.indicator_of_mem hx]; exact hf1 x
    · rw [Set.indicator_of_notMem hx, abs_zero]; exact zero_le_one
  have hfz : ∀ x ∉ closedCube z R, (cube z R).indicator f x = 0 := fun x hx =>
    Set.indicator_of_notMem (fun h => hx (cube_subset_closedCube z R h)) _
  have h := (hblk P (hasUnitRange_of_lawHypotheses hP) X R hR r hRr hrR z _ hf' hf1' hfz).osBound_abs
  have e : (fun a => |centeredBlock P (familyJ1 W) a z R r f p q|) = fun a =>
      |R ^ (-(d : ℝ)) * ∫ x, (cube z R).indicator f x * X.field r a x| := by
    funext a
    rw [centeredBlock_eq_integral_indicator]
    congr 3
    funext x
    rw [hXeq r (by linarith) a x]
  rw [e]
  refine h.mono_scale (le_of_eq ?_)
  rw [neg_div]
  ring

end QSH
