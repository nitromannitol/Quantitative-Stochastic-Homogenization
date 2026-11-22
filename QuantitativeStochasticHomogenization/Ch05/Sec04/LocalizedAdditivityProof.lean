import QuantitativeStochasticHomogenization.Ch05.Sec04.LocalizedFieldInputProof
import QuantitativeStochasticHomogenization.Ch05.Sec04.JointHeatVersion
import QuantitativeStochasticHomogenization.Ch05.Sec04.BlockEstimatesBoundary
import QuantitativeStochasticHomogenization.Ch04.Sec02.UniformAdditivity
import QuantitativeStochasticHomogenization.AppA.AlmostSureOsBound

/-!
# The additivity (5.88) of the localized energy from Theorem 4.6 (i)

Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, (5.87)-(5.88): the additivity of the localized energy `J₁^{(δ)}` at the exponent `γ`
follows from the additivity of `J₁` (Theorem 4.6 (i)) and the two localization errors (5.85).

Write `F_r(x) = J₁^{(δ)}(x, r, p, q)` and `H` for the average against `Φ_{z,√(R²-r²)}`. For
`2 ≤ r < R`, `|F_R(z) - H F_r| ≤ |F_R(z) - J_R(z)| + |J_R(z) - H J_r| + H |J_r - F_r|`, and the
three terms are bounded by the localization at the outer center, by Theorem 4.6 (i) and by the
localization at every inner center integrated against `H` (`osBound_transfer_average`). Here `J`
is a bounded jointly measurable version of `J₁`, which makes the inner error jointly measurable
and turns the almost surely measurable localization errors into measurable ones.

Theorem 4.6 (i) gives `O_t(C_t r^{-d})` at `t = sγ/d < 1`, where `C_t` depends only on `t`, `d`
and `Λ`; since the defect lies in `[0, Λ + 1]`, it is also `O_s((Λ + 1)^{1-γ/d} C_t^{γ/d} r^{-γ})`
(`osBound_increase_exponent_of_bounded`, `jointVersionAdditivity`). The constant
`2C' + (Λ + 1)^{1-γ/d} C_t^{γ/d}` is chosen before the law (`localizedAdditivityInput_of_uniform`).
With `localizedFieldInput`, the block estimates `QSH.Frozen.blockCLT`, `QSH.Frozen.blockBoundary`
and `QSH.Frozen.blockChange` follow from `UniformAdditivityJ1` and the existence of
homogenization data for each law.
-/

open MeasureTheory

namespace QSH

/-- A nonnegative variable bounded by `B` with `X ≤ O_t(c)` satisfies `X ≤ O_{t/v}(B^{1-v} c^v)`
for `0 < v ≤ 1`, since `X ≤ B^{1-v} X^v`. -/
theorem osBound_increase_exponent_of_bounded {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {t c B v : ℝ} (h : OsBound P X t c)
    (hx : ∀ a, 0 ≤ X a) (hB : 0 < B) (hb : ∀ a, X a ≤ B)
    (hv : 0 < v) (hv₁ : v ≤ 1) :
    OsBound P X (t / v) (B ^ (1-v) * c ^ v) := by
  apply ((h.rpow hx hv).const_mul (Real.rpow_pos_of_pos hB (1-v))).of_le h.1
  intro a
  calc X a = (X a) ^ (1-v) * (X a) ^ v := by
         rw [← Real.rpow_add_of_nonneg (hx a) (sub_nonneg.mpr hv₁) hv.le,
           sub_add_cancel, Real.rpow_one]
       _ ≤ B ^ (1-v) * (X a) ^ v :=
         mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (hx a) (hb a) (sub_nonneg.mpr hv₁))
           (Real.rpow_nonneg (hx a) v)

/-- **Transfer of an uncentered additivity defect through a probability average**:
`|F - ∫ f dμ| ≤ |F - J| + |J - ∫ g dμ| + ∫ |g - f| dμ`, with the last term bounded by Jensen's
inequality from the bounds at every point. -/
theorem osBound_transfer_average {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} [SFinite P] {μ : Measure E} [IsProbabilityMeasure μ]
    {f g : E → Ω → ℝ} {F J : Ω → ℝ} {s cF cJ ci : ℝ} (hs : 1 ≤ s) (hci : 0 < ci)
    (hm : Measurable (Function.uncurry (fun y a => |g y a - f y a|)))
    (hmF : Measurable (fun a => |F a - ∫ y, f y a ∂μ|))
    (hf : ∀ᵐ a ∂P, Integrable (fun y => f y a) μ)
    (hg : ∀ᵐ a ∂P, Integrable (fun y => g y a) μ)
    (hF : OsBound P (fun a => |F a - J a|) s cF)
    (hJ : OsBound P (fun a => |J a - ∫ y, g y a ∂μ|) s cJ)
    (hi : ∀ y, OsBound P (fun a => |g y a - f y a|) s ci) :
    OsBound P (fun a => |F a - ∫ y, f y a ∂μ|) s (cF + cJ + ci) := by
  have hscale : (∫ _y : E, ci ∂μ) = ci := by simp
  obtain ⟨_, hmean⟩ := osBound_integral (μ := μ) (θ := fun _ => ci)
    hs hm (fun _ _ => abs_nonneg _) measurable_const (integrable_const _)
    (by simpa only [hscale] using hci) hi
  rw [hscale] at hmean
  refine (osBound_add (osBound_add hF hJ hs) hmean hs).of_le_ae hmF ?_
  filter_upwards [hf, hg] with a ha hb
  have hlast : |(∫ y, g y a ∂μ) - ∫ y, f y a ∂μ| ≤ ∫ y, |g y a - f y a| ∂μ := by
    rw [← integral_sub hb ha]
    exact abs_integral_le_integral_abs
  change |F a - ∫ y, f y a ∂μ| ≤
    |F a - J a| + |J a - ∫ y, g y a ∂μ| + ∫ y, |g y a - f y a| ∂μ
  linarith only [abs_sub_le (F a) (J a) (∫ y, f y a ∂μ),
    abs_sub_le (J a) (∫ y, g y a ∂μ) (∫ y, f y a ∂μ), hlast]

private theorem measurable_swapped_error {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {g f : Ω → E → ℝ} (hg : Measurable (Function.uncurry g))
    (hf : Measurable (Function.uncurry f)) :
    Measurable (Function.uncurry (fun y a => |g a y - f a y|)) := by
  have he : Measurable (fun u : Ω × E => |g u.1 u.2 - f u.1 u.2|) :=
    continuous_abs.measurable.comp (hg.sub hf)
  exact he.comp (measurable_swap : Measurable (Prod.swap : E × Ω → Ω × E))

/-- **The additivity (5.87) for a bounded jointly measurable version of `J₁`** at the stochastic
exponent `s` and the spatial exponent `γ` of the block window, with a constant chosen before
the law. -/
def JointVersionAdditivity : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ Λ s δ γ η : ℝ, 1 < Λ → BlockWindow d s δ γ η →
    ∃ K : ℝ, 0 < K ∧ ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∀ p q : Vec d, euclideanNorm p < 1 → euclideanNorm q < 1 →
      ∃ J : ℝ → CoefficientField d Λ → Vec d → ℝ,
        (∀ t : ℝ, 2 ≤ t → Measurable fun w : CoefficientField d Λ × Vec d => J t w.1 w.2) ∧
        (∀ t : ℝ, 2 ≤ t → ∀ a y, |J t a y| ≤ Λ + 1) ∧
        (∀ t : ℝ, 2 ≤ t → ∀ y, (fun a => J t a y) =ᵐ[P] fun a => J1Heat a y t p q) ∧
        ∀ (z : Vec d) (r R : ℝ), 2 ≤ r → r < R →
          OsBound P (fun a => |J R a z - ∫ y, heatKernel z (Real.sqrt (R^2-r^2)) y * J r a y|)
            s (K * r ^ (-γ))

/-- **The localized additivity (5.88) from the additivity of a version of `J₁`**: the
localization errors at the outer center and at the inner centers, and the additivity of the
version, give `LocalizedAdditivityInput` with the constant `2C' + K`. -/
theorem localizedAdditivityInput_of_uniform_global (hfield : LocalizedFieldInput)
    (hglobal : JointVersionAdditivity) : LocalizedAdditivityInput := by
  intro d hd Λ s δ γ η hΛ hw α σ θ C₀ C' hc
  obtain ⟨K, hK, hK'⟩ := hglobal d hd Λ s δ γ η hΛ hw
  obtain ⟨M, _, hM⟩ := hfield d hd Λ s δ γ η hΛ hw α σ θ C₀ C' hc
  obtain ⟨_, _, _, _, _, _, _, _, hC'⟩ := hc
  obtain ⟨hs, _, hδ, hγlo, _⟩ := hw
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hγ : 0 < γ := lt_trans (by positivity) hγlo
  refine ⟨2 * C' + K, by positivity, ?_⟩
  intro P hP W hW z r R hr hrR p q hp hq
  let : IsProbabilityMeasure P := hP.1
  obtain ⟨J, hJm, hJb, hJe, hJadd⟩ := hK' P hP p q hp hq
  let F : ℝ → CoefficientField d Λ → Vec d → ℝ := fun t a y => familyJ1 W a y t p q
  have hFm (t : ℝ) (ht : 2 ≤ t) :
      Measurable fun w : CoefficientField d Λ × Vec d => F t w.1 w.2 := by
    have h := (hM P hP W hW t ht p q hp hq).2 Set.univ MeasurableSet.univ
    simp only [Set.indicator_univ] at h
    exact measurable_prod_of_le (localSigma_le _) h
  have hpiece (t : ℝ) (ht : 2 ≤ t) (y : Vec d) :
      OsBound P (fun a => |J t a y - F t a y|) s (C' * t ^ (-γ)) := by
    obtain ⟨Y, he, hY⟩ := (hW y t ht p q hp hq).2.exists_osBound
    apply hY.of_le_ae (continuous_abs.measurable.comp
      (((hJm t ht).comp measurable_prodMk_right).sub ((hFm t ht).comp measurable_prodMk_right)))
    filter_upwards [he, hJe t ht y] with a h₁ h₂
    change |J t a y - familyJ1 W a y t p q| ≤ Y a
    rw [h₂, familyJ1, dite_eq_left ht]
    exact h₁.le
  let ρ := Real.sqrt (R^2-r^2)
  have hr0 : 0 < r := by linarith
  have hR : 2 ≤ R := hr.trans hrR.le
  have hρ : 0 < ρ := Real.sqrt_pos.2 (sub_pos.mpr (sq_lt_sq' (by linarith) hrR))
  let : Fact (0 < ρ) := ⟨hρ⟩
  set μ := heatMeasure z ρ with hμ
  let : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have hfi (a) : Integrable (F r a) μ :=
    Integrable.of_bound ((hFm r hr).comp measurable_prodMk_left).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact (hM P hP W hW r hr p q hp hq).1 a y)
  have hgi (a) : Integrable (J r a) μ :=
    Integrable.of_bound ((hJm r hr).comp measurable_prodMk_left).aestronglyMeasurable (Λ + 1)
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hJb r hr a y)
  have hOuter : OsBound P (fun a => |F R a z - J R a z|) s (C' * R ^ (-γ)) := by
    simpa only [abs_sub_comm] using hpiece R hR z
  have hGlobal : OsBound P (fun a => |J R a z - ∫ y, J r a y ∂μ|) s (K * r ^ (-γ)) := by
    simpa only [hμ, integral_heatMeasure, ρ] using hJadd z r R hr hrR
  have hme : Measurable (Function.uncurry
      (fun (y : Vec d) (a : CoefficientField d Λ) => |J r a y - F r a y|)) :=
    measurable_swapped_error (g := J r) (f := F r) (hJm r hr) (hFm r hr)
  have havg : Measurable (fun a => ∫ y, F r a y ∂μ) :=
    ((hFm r hr).stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  have htarget : Measurable (fun a => |F R a z - ∫ y, F r a y ∂μ|) :=
    continuous_abs.measurable.comp (((hFm R hR).comp measurable_prodMk_right).sub havg)
  have h : OsBound P (fun a => |F R a z - ∫ y, F r a y ∂μ|) s
      (C' * R ^ (-γ) + K * r ^ (-γ) + C' * r ^ (-γ)) :=
    osBound_transfer_average (Ω := CoefficientField d Λ) (E := Vec d) (P := P) (μ := μ)
      (F := fun a => F R a z) (J := fun a => J R a z)
      (f := fun y a => F r a y) (g := fun y a => J r a y)
      (cF := C' * R ^ (-γ)) (cJ := K * r ^ (-γ)) (ci := C' * r ^ (-γ)) hs.le
      (mul_pos hC' (Real.rpow_pos_of_pos hr0 _)) hme htarget
      (Filter.Eventually.of_forall hfi) (Filter.Eventually.of_forall hgi)
      hOuter hGlobal (hpiece r hr)
  have hrate := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hr0 hrR.le (neg_nonpos.mpr hγ.le)) hC'.le
  have hscale : C' * R ^ (-γ) + K * r ^ (-γ) + C' * r ^ (-γ) ≤ (2 * C' + K) * r ^ (-γ) := by
    linarith only [hrate]
  simpa only [hμ, integral_heatMeasure, ρ, F] using h.mono_scale hscale

open BaseExponent in
/-- **The additivity of a bounded version of `J₁` from Theorem 4.6 (i)**: Theorem 4.6 (i) at the
stochastic exponent `t = sγ/d < 1` gives the defect of the version as `O_t(C_t r^{-d})`; it lies
in `[0, Λ + 1]`, hence it is `O_s((Λ + 1)^{1-γ/d} C_t^{γ/d} r^{-γ})`. -/
theorem jointVersionAdditivity (hU : UniformAdditivityJ1)
    (hV : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ P : Measure (CoefficientField d Λ),
      LawHypotheses P → HasJointHeatVersion P) : JointVersionAdditivity := by
  intro d hd Λ s δ γ η hΛ hw
  obtain ⟨hs1, -, hδ, hγlo, hγhi, -⟩ := hw
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hγ : 0 < γ := lt_trans (by positivity) hγlo
  have hsγ : γ * s < d := (lt_div_iff₀ (by linarith)).mp (lt_of_lt_of_le hγhi (min_le_left _ _))
  set v : ℝ := γ / d with hv
  have hv0 : 0 < v := div_pos hγ hd0
  have hv1 : v ≤ 1 := (div_le_one hd0).mpr (by nlinarith)
  have hsv : s * v < 1 := by
    rw [hv, ← mul_div_assoc, div_lt_one hd0]
    linarith [mul_comm γ s]
  have hsv0 : 0 < s * v := mul_pos (by linarith) hv0
  obtain ⟨C, hC, hCP⟩ := hU d hd Λ (2 * (s * v)) hΛ (by linarith) (by linarith)
  have hB : (0 : ℝ) < Λ + 1 := by linarith
  refine ⟨(Λ + 1) ^ (1 - v) * C ^ v,
    mul_pos (Real.rpow_pos_of_pos hB _) (Real.rpow_pos_of_pos hC _), ?_⟩
  intro P hP p q hp hq
  let Q : CoefficientField d Λ → (HeatObservationIndex d → ℝ) → Prop := fun _ V =>
    ∀ (z : Vec d) (r : ℝ) (p q : Vec d), 0 < r → euclideanNorm p < 1 → euclideanNorm q < 1 →
      0 ≤ V (z, r, p, q) ∧ V (z, r, p, q) ≤ Λ + 1
  have hzero : ∀ a, Q a 0 := by
    intro a z r p q _ _ _
    simp only [Pi.zero_apply]
    exact ⟨le_rfl, hB.le⟩
  have hQ : ∀ᵐ a ∂P, Q a (fun i => J1Heat a i.1 i.2.1 i.2.2.1 i.2.2.2) := by
    refine Filter.Eventually.of_forall fun a z r p q hr hp hq => ?_
    obtain ⟨h0, h1⟩ := J1Heat_nonneg_le a z hr p q
    have hp' : euclideanSq p ≤ 1 := by
      rw [← euclideanNorm_sq]; nlinarith [euclideanNorm_nonneg p]
    have hq' : euclideanSq q ≤ 1 := by
      rw [← euclideanNorm_sq]; nlinarith [euclideanNorm_nonneg q]
    refine ⟨h0, h1.trans ?_⟩
    nlinarith [euclideanSq_nonneg p]
  obtain ⟨V, hVm, hEq, hVQ⟩ := (hV d hd Λ hΛ P hP).with_pathwise_property Q hzero hQ
  have hslice (t : ℝ) :
      Measurable fun w : CoefficientField d Λ × Vec d => V w.1 (w.2, t, p, q) :=
    hVm.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  refine ⟨fun t a y => V a (y, t, p, q), fun t _ => hslice t, ?_, ?_, ?_⟩
  · intro t ht a y
    obtain ⟨h0, h1⟩ := hVQ a y t p q (by linarith) hp hq
    rw [abs_of_nonneg h0]
    exact h1
  · intro t _ y
    filter_upwards [hEq] with a ha
    exact ha (y, t, p, q)
  · intro z r R hr hrR
    have hρ : 0 < Real.sqrt (R ^ 2 - r ^ 2) :=
      Real.sqrt_pos.2 (sub_pos.mpr (sq_lt_sq' (by linarith) hrR))
    obtain ⟨-, hD⟩ := hCP P hP z r R (by linarith) hrR p q hp hq
    rw [show 2 * (s * v) / 2 = s * v by ring] at hD
    let D : CoefficientField d Λ → ℝ := fun a => |V a (z, R, p, q) -
      ∫ x, heatKernel z (Real.sqrt (R ^ 2 - r ^ 2)) x * V a (x, r, p, q)|
    have hDeq : D =ᵐ[P] fun a => |J1Heat a z R p q -
        ∫ x, heatKernel z (Real.sqrt (R ^ 2 - r ^ 2)) x * J1Heat a x r p q| := by
      filter_upwards [hEq] with a ha
      simp only [D, ha]
    have hDm : Measurable D := by
      have h1 : Measurable fun a => V a (z, R, p, q) :=
        hVm.comp (measurable_id.prodMk measurable_const)
      have h2 : Measurable (fun w : CoefficientField d Λ × Vec d =>
          heatKernel z (Real.sqrt (R ^ 2 - r ^ 2)) w.2 * V w.1 (w.2, r, p, q)) :=
        ((measurable_heatKernel_right z _).comp measurable_snd).mul (hslice r)
      exact continuous_abs.measurable.comp
        (h1.sub h2.stronglyMeasurable.integral_prod_right'.measurable)
    have hDos : OsBound P D (s * v) (C * r ^ (-(d : ℝ))) := by
      obtain ⟨Y, hY, hYb⟩ := hD.exists_osBound
      exact (hYb.aeOsBound_of_ae_eq (hDeq.trans hY)).osBound_of_measurable hDm
    have hDB : ∀ a, D a ≤ Λ + 1 := by
      intro a
      have hx := hVQ a z R p q (by linarith) hp hq
      have hin (x : Vec d) := hVQ a x r p q (by linarith) hp hq
      have hint0 : 0 ≤ ∫ x, heatKernel z (Real.sqrt (R ^ 2 - r ^ 2)) x * V a (x, r, p, q) :=
        integral_nonneg fun x => mul_nonneg (heatKernel_nonneg _ _ x) (hin x).1
      have hint1 : ∫ x, heatKernel z (Real.sqrt (R ^ 2 - r ^ 2)) x * V a (x, r, p, q) ≤
          Λ + 1 := by
        calc ∫ x, heatKernel z (Real.sqrt (R ^ 2 - r ^ 2)) x * V a (x, r, p, q)
            ≤ ∫ x, heatKernel z (Real.sqrt (R ^ 2 - r ^ 2)) x * (Λ + 1) :=
              integral_mono_of_nonneg
                (Filter.Eventually.of_forall fun x =>
                  mul_nonneg (heatKernel_nonneg _ _ x) (hin x).1)
                ((integrable_heatKernel z hρ).mul_const _)
                (Filter.Eventually.of_forall fun x =>
                  mul_le_mul_of_nonneg_left (hin x).2 (heatKernel_nonneg _ _ x))
          _ = Λ + 1 := by rw [integral_mul_const, integral_heatKernel z hρ, one_mul]
      exact abs_sub_le_iff.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have h := osBound_increase_exponent_of_bounded hDos (fun a => abs_nonneg _) hB hDB hv0 hv1
    have e1 : s * v / v = s := mul_div_cancel_right₀ s hv0.ne'
    have e2 : (C * r ^ (-(d : ℝ))) ^ v = C ^ v * r ^ (-γ) := by
      have hdv : -(d : ℝ) * v = -γ := by
        rw [hv]
        field_simp
      rw [Real.mul_rpow hC.le (Real.rpow_nonneg (by linarith) _), ← Real.rpow_mul (by linarith),
        hdv]
    rw [e1, e2, ← mul_assoc] at h
    exact h

/-- **The localized additivity (5.88) from Theorem 4.6 (i)** and a jointly measurable version of
`J₁` for every law satisfying the assumptions. -/
theorem localizedAdditivityInput_of_uniform (hU : UniformAdditivityJ1)
    (hV : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ P : Measure (CoefficientField d Λ),
      LawHypotheses P → HasJointHeatVersion P) : LocalizedAdditivityInput :=
  localizedAdditivityInput_of_uniform_global localizedFieldInput (jointVersionAdditivity hU hV)

/-- **The localized additivity (5.88) from Theorem 4.6 (i)** and the existence of
homogenization data for every law satisfying the assumptions. -/
theorem localizedAdditivityInput_of_uniformAdditivityJ1 (hU : UniformAdditivityJ1)
    (hS : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ P : Measure (CoefficientField d Λ),
      LawHypotheses P → Nonempty (HomogenizationData P)) : LocalizedAdditivityInput :=
  localizedAdditivityInput_of_uniform hU fun d hd Λ hΛ P hP =>
    hasJointHeatVersion_of_lawHypotheses hd hΛ hP (hS d hd Λ hΛ P hP).some

/-- **Lemma 5.29 (i)** (`QSH.Frozen.blockCLT`) from Theorem 4.6 (i) with constants uniform over
the laws and the existence of homogenization data. -/
theorem blockCLT_of_uniformAdditivityJ1 (hU : UniformAdditivityJ1)
    (hS : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ P : Measure (CoefficientField d Λ),
      LawHypotheses P → Nonempty (HomogenizationData P)) : QSH.Frozen.blockCLT :=
  blockCLT_of_inputs localizedFieldInput (localizedAdditivityInput_of_uniformAdditivityJ1 hU hS)

/-- **Lemma 5.29 (ii)** (`QSH.Frozen.blockBoundary`) from Theorem 4.6 (i) with constants uniform
over the laws and the existence of homogenization data. -/
theorem blockBoundary_of_uniformAdditivityJ1 (hU : UniformAdditivityJ1)
    (hS : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ P : Measure (CoefficientField d Λ),
      LawHypotheses P → Nonempty (HomogenizationData P)) : QSH.Frozen.blockBoundary :=
  blockBoundary_of_inputs localizedFieldInput
    (localizedAdditivityInput_of_uniformAdditivityJ1 hU hS)

/-- **Lemma 5.29 (iii)** (`QSH.Frozen.blockChange`) from Theorem 4.6 (i) with constants uniform
over the laws and the existence of homogenization data. -/
theorem blockChange_of_uniformAdditivityJ1 (hU : UniformAdditivityJ1)
    (hS : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ P : Measure (CoefficientField d Λ),
      LawHypotheses P → Nonempty (HomogenizationData P)) : QSH.Frozen.blockChange :=
  blockChange_of_inputs localizedFieldInput
    (localizedAdditivityInput_of_uniformAdditivityJ1 hU hS)

end QSH
