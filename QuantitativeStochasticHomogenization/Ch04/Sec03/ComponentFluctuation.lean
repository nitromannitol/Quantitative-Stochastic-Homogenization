import QuantitativeStochasticHomogenization.Ch04.Sec03.PolarizationNearInverse

/-!
# Fluctuations of random vectors with controlled components

A random vector `V` whose components satisfy `|Vₖ - E Vₖ| ≤ c Tₖ` with `Tₖ ≤ O_s(θ)` has
`|V - E V|² ≤ O_{s/2}((2·2^{2/s})^d c² θ²)` and `E|V - E V|² ≤ d c² K θ²`
(`fluctuation_of_components`). Used for the polarization vectors of `J₁` and of its flux in the
proof of Lemma 4.13 here.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ}

open BaseExponent

section Components

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Fluctuations of a random vector from those of its components.** -/
theorem fluctuation_of_components [IsProbabilityMeasure P] {V : Ω → Vec d}
    {T : Fin d → Ω → ℝ} {s θ c : ℝ} (hs : 0 < s) (hθ : 0 < θ) (hc : 0 < c)
    (hVm : ∀ k, Measurable fun ω => V ω k)
    (hT : ∀ k, OsBound P (T k) s θ) (hT0 : ∀ k ω, 0 ≤ T k ω)
    (hle : ∀ k ω, |V ω k - ∫ ω', V ω' k ∂P| ≤ c * T k ω) :
    OsBound P (fun ω => euclideanSq (V ω - fun k => ∫ ω', V ω' k ∂P)) (s / 2)
      ((2 * (2 : ℝ) ^ (s / 2)⁻¹) ^ d * (c ^ 2 * θ ^ 2)) ∧
    Integrable (fun ω => euclideanSq (V ω - fun k => ∫ ω', V ω' k ∂P)) P ∧
    ∫ ω, euclideanSq (V ω - fun k => ∫ ω', V ω' k ∂P) ∂P ≤
      d * (c ^ 2 * (momentConstant (s / 2) * θ ^ 2)) := by
  have hcomp : ∀ k ω, (V ω - fun k => ∫ ω', V ω' k ∂P) k ^ 2 ≤ c ^ 2 * T k ω ^ 2 := by
    intro k ω
    have h := hle k ω
    have h0 := abs_nonneg (V ω k - ∫ ω', V ω' k ∂P)
    simp only [Pi.sub_apply]
    rw [← sq_abs (V ω k - ∫ ω', V ω' k ∂P), ← mul_pow]
    exact pow_le_pow_left₀ h0 h 2
  have hbound : ∀ ω, euclideanSq (V ω - fun k => ∫ ω', V ω' k ∂P) ≤ ∑ k, c ^ 2 * T k ω ^ 2 := by
    intro ω
    simp only [euclideanSq, dot, ← sq]
    exact Finset.sum_le_sum fun k _ => hcomp k ω
  have hYm : Measurable fun ω => euclideanSq (V ω - fun k => ∫ ω', V ω' k ∂P) := by
    simp only [euclideanSq, dot, Pi.sub_apply]
    exact Finset.measurable_sum _ fun k _ =>
      ((hVm k).sub measurable_const).mul ((hVm k).sub measurable_const)
  have hsq : ∀ k, OsBound P (fun ω => c ^ 2 * T k ω ^ 2) (s / 2) (c ^ 2 * θ ^ 2) := fun k =>
    ((hT k).sq (hT0 k)).const_mul (by positivity)
  have hsum := osBound_finset_sum_of_pos (P := P) Finset.univ (by positivity) (by positivity)
    fun k _ => hsq k
  rw [Finset.card_univ, Fintype.card_fin] at hsum
  have hmom : ∀ k, Integrable (fun ω => T k ω ^ 2) P ∧
      ∫ ω, T k ω ^ 2 ∂P ≤ momentConstant (s / 2) * θ ^ 2 := fun k =>
    (hT k).integral_sq_le (hT0 k)
  have hsumi : Integrable (fun ω => ∑ k, c ^ 2 * T k ω ^ 2) P :=
    integrable_finsetSum _ fun k _ => (hmom k).1.const_mul _
  have hYi : Integrable (fun ω => euclideanSq (V ω - fun k => ∫ ω', V ω' k ∂P)) P :=
    hsumi.mono' hYm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (euclideanSq_nonneg _)]
      exact hbound ω)
  refine ⟨hsum.of_le hYm hbound, hYi, ?_⟩
  calc ∫ ω, euclideanSq (V ω - fun k => ∫ ω', V ω' k ∂P) ∂P
      ≤ ∫ ω, ∑ k, c ^ 2 * T k ω ^ 2 ∂P :=
        integral_mono_ae hYi hsumi (Filter.Eventually.of_forall hbound)
    _ = ∑ k, c ^ 2 * ∫ ω, T k ω ^ 2 ∂P := by
        rw [integral_finsetSum _ fun k _ => (hmom k).1.const_mul _]
        exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _
    _ ≤ ∑ _k : Fin d, c ^ 2 * (momentConstant (s / 2) * θ ^ 2) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hmom k).2 (sq_nonneg c)
    _ = d * (c ^ 2 * (momentConstant (s / 2) * θ ^ 2)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Components

section ThreeLoads

variable {Λ : ℝ} {P : Measure (CoefficientField d Λ)}

/-- **Fluctuations of combinations of `J₁` at three loads per component**: if
`Vₖ = c (J₁(L₁ₖ) - J₁(L₂ₖ) - J₁(L₃ₖ))` with all loads in the open unit ball, then `Fluc(s, α)`
gives `|V - E V|² ≤ O_{s/2}(…)` with mean `≤ d c² K ((2·2^{1/s})² C_F r^{-α})²`. -/
theorem threeLoad_fluctuation [IsProbabilityMeasure P] {s α CF : ℝ} (hs0 : 0 < s)
    (hCF : 0 < CF)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J1Heat w.1 w.2 r p q)
    (hF : ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
      euclideanNorm p < 1 → euclideanNorm q < 1 →
      Integrable (fun a => J1Heat a z r p q) P ∧
      OsBound P (fun a => |J1Heat a z r p q - ∫ a', J1Heat a' z r p q ∂P|) s (CF * r ^ (-α)))
    (y : Vec d) {r : ℝ} (hr : 1 ≤ r) (L₁ L₂ L₃ : Fin d → Vec d × Vec d)
    (hL₁ : ∀ k, euclideanNorm (L₁ k).1 < 1 ∧ euclideanNorm (L₁ k).2 < 1)
    (hL₂ : ∀ k, euclideanNorm (L₂ k).1 < 1 ∧ euclideanNorm (L₂ k).2 < 1)
    (hL₃ : ∀ k, euclideanNorm (L₃ k).1 < 1 ∧ euclideanNorm (L₃ k).2 < 1)
    {c : ℝ} (hc : 0 < c) (V : CoefficientField d Λ → Vec d)
    (hV : ∀ a k, V a k = c * (J1Heat a y r (L₁ k).1 (L₁ k).2 - J1Heat a y r (L₂ k).1 (L₂ k).2 -
      J1Heat a y r (L₃ k).1 (L₃ k).2)) :
    OsBound P (fun a => euclideanSq (V a - fun k => ∫ a', V a' k ∂P)) (s / 2)
      ((2 * (2 : ℝ) ^ (s / 2)⁻¹) ^ d * (c ^ 2 * ((2 * (2 : ℝ) ^ s⁻¹) ^ 2 * (CF * r ^ (-α))) ^ 2)) ∧
    Integrable (fun a => euclideanSq (V a - fun k => ∫ a', V a' k ∂P)) P ∧
    ∫ a, euclideanSq (V a - fun k => ∫ a', V a' k ∂P) ∂P ≤
      d * (c ^ 2 * (momentConstant (s / 2) * ((2 * (2 : ℝ) ^ s⁻¹) ^ 2 * (CF * r ^ (-α))) ^ 2)) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  set θ : ℝ := CF * r ^ (-α) with hθ
  have hθ0 : 0 < θ := mul_pos hCF (Real.rpow_pos_of_pos hr0 _)
  set cs : ℝ := 2 * (2 : ℝ) ^ s⁻¹ with hcs
  have hcs1 : 1 ≤ cs := by
    have : 1 ≤ (2 : ℝ) ^ s⁻¹ := Real.one_le_rpow (by norm_num) (inv_nonneg.mpr hs0.le)
    linarith
  have hJm : ∀ p q : Vec d, Measurable fun a : CoefficientField d Λ => J1Heat a y r p q :=
    fun p q => (hmeasJ r p q).comp (measurable_id.prodMk measurable_const)
  set J : (Vec d × Vec d) → CoefficientField d Λ → ℝ := fun L a => J1Heat a y r L.1 L.2 with hJ
  have hFL : ∀ L : Vec d × Vec d, euclideanNorm L.1 < 1 ∧ euclideanNorm L.2 < 1 →
      Integrable (J L) P ∧ OsBound P (fun a => |J L a - ∫ a', J L a' ∂P|) s θ := fun L hL =>
    hF y r hr L.1 L.2 hL.1 hL.2
  set T : Fin d → CoefficientField d Λ → ℝ := fun k a =>
    |J (L₁ k) a - ∫ a', J (L₁ k) a' ∂P| + |J (L₂ k) a - ∫ a', J (L₂ k) a' ∂P| +
      |J (L₃ k) a - ∫ a', J (L₃ k) a' ∂P| with hT
  have hT0 : ∀ k a, 0 ≤ T k a := fun k a => by positivity
  have hTos : ∀ k, OsBound P (T k) s (cs ^ 2 * θ) := by
    intro k
    have h12 := osBound_add_of_pos (hFL _ (hL₁ k)).2 (hFL _ (hL₂ k)).2
    have h123 := osBound_add_of_pos h12 (hFL _ (hL₃ k)).2
    refine h123.mono_scale (le_of_eq ?_)
    have e1 : (2 : ℝ) * ((2 : ℝ) ^ s⁻¹ * max θ θ) = cs * θ := by rw [max_self, hcs]; ring
    rw [e1, max_eq_left (le_mul_of_one_le_left hθ0.le hcs1), hcs]
    ring
  have hmean : ∀ k, ∫ a', V a' k ∂P =
      c * ((∫ a', J (L₁ k) a' ∂P) - (∫ a', J (L₂ k) a' ∂P) - ∫ a', J (L₃ k) a' ∂P) := by
    intro k
    have i12 : Integrable (fun a => J (L₁ k) a - J (L₂ k) a) P :=
      (hFL _ (hL₁ k)).1.sub (hFL _ (hL₂ k)).1
    have e : (fun a' => V a' k) = fun a' => c * (J (L₁ k) a' - J (L₂ k) a' - J (L₃ k) a') :=
      funext fun a' => hV a' k
    rw [e, integral_const_mul, integral_sub i12 (hFL _ (hL₃ k)).1,
      integral_sub (hFL _ (hL₁ k)).1 (hFL _ (hL₂ k)).1]
  have hle : ∀ k a, |V a k - ∫ a', V a' k ∂P| ≤ c * T k a := by
    intro k a
    rw [hmean k, hV a k]
    have e : c * (J1Heat a y r (L₁ k).1 (L₁ k).2 - J1Heat a y r (L₂ k).1 (L₂ k).2 -
        J1Heat a y r (L₃ k).1 (L₃ k).2) -
        c * ((∫ a', J (L₁ k) a' ∂P) - (∫ a', J (L₂ k) a' ∂P) - ∫ a', J (L₃ k) a' ∂P) =
        c * ((J (L₁ k) a - ∫ a', J (L₁ k) a' ∂P) - (J (L₂ k) a - ∫ a', J (L₂ k) a' ∂P) -
          (J (L₃ k) a - ∫ a', J (L₃ k) a' ∂P)) := by
      simp only [hJ]; ring
    rw [e, abs_mul, abs_of_pos hc]
    refine mul_le_mul_of_nonneg_left ?_ hc.le
    have h1 := abs_sub (J (L₁ k) a - ∫ a', J (L₁ k) a' ∂P - (J (L₂ k) a - ∫ a', J (L₂ k) a' ∂P))
      (J (L₃ k) a - ∫ a', J (L₃ k) a' ∂P)
    have h2 := abs_sub (J (L₁ k) a - ∫ a', J (L₁ k) a' ∂P) (J (L₂ k) a - ∫ a', J (L₂ k) a' ∂P)
    simp only [hT]
    linarith
  have hVm : ∀ k, Measurable fun a => V a k := fun k => by
    have : (fun a => V a k) = fun a => c * (J1Heat a y r (L₁ k).1 (L₁ k).2 -
        J1Heat a y r (L₂ k).1 (L₂ k).2 - J1Heat a y r (L₃ k).1 (L₃ k).2) := funext fun a => hV a k
    rw [this]
    exact measurable_const.mul (((hJm _ _).sub (hJm _ _)).sub (hJm _ _))
  exact fluctuation_of_components hs0 (by positivity) hc hVm hTos hT0 hle

end ThreeLoads

end QSH
