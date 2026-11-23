import QuantitativeStochasticHomogenization.Ch04.Sec04.ObservationFromFiniteBall

/-!
# Proof of the observation estimate from the finite-ball observation

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.21 (consultant note S9, step 2). With `S = r^{1+δ-ε}` and `T = r^{1+δ}` one has
`S/T = r^{-ε}`; for `k ≥ d + 1 + β(1+δ)/ε` the absorbed outer term
`(S/T)^{2k} (T/S)^{2d} T²` is at most `S² (S^{-β})²`, and for large `r` the absorption
condition and `L₀ S ≤ T` hold. Hence `FiniteBallObservation` and
`SmoothedCorrectorObservation` give `LocalizationObservationEstimate` for every cap `C₀` above
the energy bound of the corrected coordinates of Lemma 3.17.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

theorem rpow_sub_div_rpow {r a b : ℝ} (hr : 0 < r) : r ^ a / r ^ b = r ^ (a - b) :=
  (Real.rpow_sub hr a b).symm

/-- **The absorbed outer term is below the fluctuation scale.** -/
theorem observation_error_le {r δ ε β k : ℝ} (hr : 1 ≤ r) (hε : 0 < ε)
    (hβ : 0 ≤ β) (hk : (d : ℝ) + 1 + β * (1 + δ) / ε ≤ k) :
    (r ^ (1 + δ - ε) / r ^ (1 + δ)) ^ (2 * k) * (r ^ (1 + δ) / r ^ (1 + δ - ε)) ^ (2 * d) *
        (r ^ (1 + δ)) ^ 2 ≤
      (r ^ (1 + δ - ε)) ^ 2 * ((r ^ (1 + δ - ε)) ^ (-β)) ^ 2 := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  rw [rpow_sub_div_rpow hr0, rpow_sub_div_rpow hr0, ← Real.rpow_mul hr0.le,
    ← Real.rpow_mul_natCast hr0.le, ← Real.rpow_mul_natCast hr0.le,
    ← Real.rpow_mul hr0.le, ← Real.rpow_mul_natCast hr0.le, ← Real.rpow_mul_natCast hr0.le,
    ← Real.rpow_add hr0, ← Real.rpow_add hr0, ← Real.rpow_add hr0]
  apply Real.rpow_le_rpow_of_exponent_le hr
  have hk' : ((d : ℝ) + 1) * ε + β * (1 + δ) ≤ k * ε := by
    have := mul_le_mul_of_nonneg_right hk hε.le
    rw [add_mul, div_mul_cancel₀ _ hε.ne'] at this
    linarith
  have hβε : β * (1 + δ - ε) ≤ β * (1 + δ) := mul_le_mul_of_nonneg_left (by linarith) hβ
  push_cast
  nlinarith

/-- **The absorption condition and `L₀ S ≤ T` hold for large `r`.** -/
theorem eventually_observation_conditions {δ ε k L₀ CD : ℝ} (hε : 0 < ε) (hk : (d : ℝ) < 2 * k) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ r : ℝ, R₀ ≤ r →
      L₀ * r ^ (1 + δ - ε) ≤ r ^ (1 + δ) ∧
      CD * (r ^ (1 + δ - ε) / r ^ (1 + δ)) ^ (2 * k) *
        (2 * (r ^ (1 + δ) / r ^ (1 + δ - ε)) ^ d) ≤ 1 / 2 := by
  have h1 : Tendsto (fun r : ℝ => r ^ ε) atTop atTop := tendsto_rpow_atTop hε
  have hpos : 0 < ε * (2 * k - d) := mul_pos hε (by linarith)
  have h2 : Tendsto (fun r : ℝ => 2 * CD * r ^ (-(ε * (2 * k - d)))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop hpos).const_mul (2 * CD)
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.1 (h1.eventually_ge_atTop L₀)
  obtain ⟨R₂, hR₂⟩ := eventually_atTop.1 ((tendsto_order.1 h2).2 (1 / 2) (by norm_num))
  refine ⟨max (max R₁ R₂) 1, le_max_right _ _, fun r hr => ?_⟩
  have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hr
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  have hrR₁ : R₁ ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hr
  have hrR₂ : R₂ ≤ r := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hr
  constructor
  · have h := hR₁ r hrR₁
    have e : r ^ (1 + δ) = r ^ ε * r ^ (1 + δ - ε) := by
      rw [← Real.rpow_add hr0]; congr 1; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hr0.le _)
  · have h := (hR₂ r hrR₂).le
    rw [rpow_sub_div_rpow hr0, rpow_sub_div_rpow hr0, ← Real.rpow_mul hr0.le,
      ← Real.rpow_mul_natCast hr0.le]
    have e : r ^ ((1 + δ - ε - (1 + δ)) * (2 * k)) * r ^ ((1 + δ - (1 + δ - ε)) * d) =
        r ^ (-(ε * (2 * k - d))) := by
      rw [← Real.rpow_add hr0]; congr 1; ring
    calc CD * r ^ ((1 + δ - ε - (1 + δ)) * (2 * k)) * (2 * r ^ ((1 + δ - (1 + δ - ε)) * d))
        = 2 * CD * (r ^ ((1 + δ - ε - (1 + δ)) * (2 * k)) *
            r ^ ((1 + δ - (1 + δ - ε)) * d)) := by ring
      _ = 2 * CD * r ^ (-(ε * (2 * k - d))) := by rw [e]
      _ ≤ 1 / 2 := h

theorem vectorRms_le_of_integral_le {z : Vec d} {T A : ℝ} (hT : 0 < T)
    {G : Vec d → Vec d} (h : ∫ x in ball z T, euclideanSq (G x) ≤ A * volume.real (ball z T)) :
    vectorRms volume (ball z T) G ≤ Real.sqrt A := by
  unfold vectorRms
  refine Real.sqrt_le_sqrt ?_
  have hB := volume_real_ball_pos z hT
  rw [setAverage_eq, smul_eq_mul, inv_mul_le_iff₀ hB]
  linarith

set_option maxHeartbeats 400000 in
/-- **The observation estimate** from the finite-ball observation and the observation of the
smoothed correctors, for every cap `C₀` above the energy bound of Lemma 3.17. -/
theorem localizationObservationEstimate_of_finiteBall (hd : 2 ≤ d) (hΛ : 1 < Λ)
    {s δ γ α σ θ β k : ℝ} (hs : 1 ≤ s) (hδ : 0 < δ) (hα : 0 < α)
    (hαγ : γ < α * (1 + δ) + δ) (hγ : 0 < γ) (hγs : s * γ < d) (hβ : 0 < β) (hσ : 0 < σ)
    (hk : (d : ℝ) + 1 + β * (1 + δ) / localizationEpsilon δ α γ ≤ k)
    (hD : FiniteBallObservation d Λ σ θ k)
    (hG : ∃ μ C : ℝ, 0 < μ ∧ 0 < C ∧ ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∃ S : HomogenizationData P, SmoothedCorrectorObservation S s δ γ α σ θ β μ C) :
    ∃ C₀min : ℝ, 0 < C₀min ∧ ∀ C₀ : ℝ, C₀min ≤ C₀ →
      LocalizationObservationEstimate d Λ s δ γ α σ θ C₀ β := by
  obtain ⟨βE, CE, hβE, hCE, hE8⟩ := exists_translated_corrector_bounds hd hΛ
  have hAE : 0 < 2 ^ (d + 1) * (1 + CE ^ 2) := by positivity
  refine ⟨Real.sqrt (2 ^ (d + 1) * (1 + CE ^ 2)), Real.sqrt_pos.2 hAE, fun C₀ hC₀ => ?_⟩
  have hC₀0 : 0 < C₀ := lt_of_lt_of_le (Real.sqrt_pos.2 hAE) hC₀
  obtain ⟨L₀, CD, hL₀, hCD, hDτ⟩ := hD
  have hs0 : 0 < s := by linarith
  have hsγ : 0 < s * γ := mul_pos hs0 hγ
  obtain ⟨CDτ, hCDτ, hDP⟩ := hDτ (s * γ) hsγ hγs
  obtain ⟨Cs, hCs, hE8P⟩ := hE8 (s * γ) hsγ hγs
  obtain ⟨μG, CG, hμG, hCG, hGP⟩ := hG
  have hε : 0 < localizationEpsilon δ α γ := localizationEpsilon_pos hδ hα hαγ
  have hεδ : localizationEpsilon δ α γ ≤ δ := (min_le_right _ _).trans (by linarith)
  have hkd : (d : ℝ) < 2 * k := by
    have : 0 ≤ β * (1 + δ) / localizationEpsilon δ α γ :=
      div_nonneg (mul_nonneg hβ.le (by linarith)) hε.le
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨R₀, hR₀1, hR₀⟩ := eventually_observation_conditions (d := d) (δ := δ) (L₀ := L₀)
    (CD := CD) hε hkd
  set KE : ℝ := 24 * CD * (2 ^ d * 2) ^ 2 * C₀ ^ 2 with hKE
  have hKE0 : 0 < KE := by positivity
  have hl2 : 0 < Real.log 2 ^ s⁻¹ := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _
  have h8 : 0 < Real.sqrt (8 * CD) := Real.sqrt_pos.2 (by positivity)
  have hsK : 0 < Real.sqrt KE := Real.sqrt_pos.2 hKE0
  have hRγ : 0 < R₀ ^ γ := Real.rpow_pos_of_pos (by linarith) _
  have h1d : (0 : ℝ) < (1 + d) ^ γ := Real.rpow_pos_of_pos (by positivity) _
  have hCDγ : 0 < CDτ ^ γ := Real.rpow_pos_of_pos hCDτ _
  have hCsγ : 0 < Cs ^ γ := Real.rpow_pos_of_pos hCs _
  set C₁ : ℝ := CG + CDτ ^ γ + (1 + d) ^ γ * Cs ^ γ + R₀ ^ γ / Real.log 2 ^ s⁻¹ +
    Real.sqrt (8 * CD) * CG + Real.sqrt KE / Real.log 2 ^ s⁻¹ + Real.sqrt KE with hC₁
  have hC₁pos : 0 < C₁ := by positivity
  refine ⟨min μG β, C₁, lt_min hμG hβ, hC₁pos, fun P hP => ?_⟩
  have : IsProbabilityMeasure P := hP.1
  obtain ⟨S, hS⟩ := hGP P hP
  refine ⟨S, fun W z r hr => ?_⟩
  obtain ⟨XG, YG, hXG0, hYG0, hXGos, hYGos, hGae⟩ := hS z r hr
  obtain ⟨XD, hXDm, hXDos, hXD1, hDae⟩ := hDP P hP z
  obtain ⟨XE, hXEm, hXEos, hXE1, hE8ae⟩ := hE8P P hP S z
  have hr0 : 0 < r := by linarith
  have hr1 : 1 ≤ r := by linarith
  set Sr := localizationIntermediateRadius δ α γ r with hSrdef
  set Tr := localizationOuterRadius δ r with hTrdef
  have hrS : r ≤ Sr := le_localizationIntermediateRadius hδ hr1
  have hS0 : 0 < Sr := lt_of_lt_of_le hr0 hrS
  have hST : Sr ≤ Tr := localizationIntermediateRadius_le_outer hδ hα hαγ hr1
  have hSβ : 0 < Sr ^ (-β) := Real.rpow_pos_of_pos hS0 _
  have hXD0 : ∀ a, 0 ≤ XD a := fun a => zero_le_one.trans (hXD1 a)
  have hXE0 : ∀ a, 0 ≤ XE a := fun a => zero_le_one.trans (hXE1 a)
  refine ⟨fun a => max (max (max (XG a) (XD a)) ((1 + d) * XE a)) R₀,
    fun a => Real.sqrt (8 * CD) * YG a + Real.sqrt KE * Sr ^ (-β),
    fun a => le_trans (hXG0 a) ((le_max_left _ _).trans ((le_max_left _ _).trans
      (le_max_left _ _))),
    fun a => add_nonneg (mul_nonneg h8.le (hYG0 a)) (mul_nonneg hsK.le hSβ.le), ?_, ?_, ?_⟩
  · -- the radius
    have hpow : ∀ a, max (max (max (XG a) (XD a)) ((1 + d) * XE a)) R₀ ^ γ =
        max (max (max (XG a ^ γ) (XD a ^ γ)) ((1 + d) ^ γ * XE a ^ γ)) (R₀ ^ γ) := fun a => by
      have h1 : 0 ≤ max (XG a) (XD a) := le_max_of_le_left (hXG0 a)
      have h2 : 0 ≤ (1 + d) * XE a := mul_nonneg (by positivity) (hXE0 a)
      rw [rpow_max_of_nonneg (le_max_of_le_left h1) (by linarith) hγ.le,
        rpow_max_of_nonneg h1 h2 hγ.le, rpow_max_of_nonneg (hXG0 a) (hXD0 a) hγ.le,
        Real.mul_rpow (by positivity) (hXE0 a)]
    have hDγ : AEOsBound P (fun a => XD a ^ γ) s (CDτ ^ γ) := by
      have h1 := hXDos.rpow hXD0 hγ
      rw [show s * γ / γ = s by field_simp] at h1
      exact h1.aeOsBound_of_ae_eq EventuallyEq.rfl
    have hEγ : AEOsBound P (fun a => (1 + d) ^ γ * XE a ^ γ) s ((1 + d) ^ γ * Cs ^ γ) := by
      have h1 := hXEos.rpow hXE0 hγ
      rw [show s * γ / γ = s by field_simp] at h1
      exact (h1.aeOsBound_of_ae_eq EventuallyEq.rfl).const_mul h1d
    have hconst : AEOsBound P (fun _ => R₀ ^ γ) s (R₀ ^ γ / Real.log 2 ^ s⁻¹) :=
      (osBound_of_le_const measurable_const hs0 hRγ
        (Eventually.of_forall fun _ => le_rfl)).aeOsBound_of_ae_eq EventuallyEq.rfl
    have hsum := ((hXGos.add hDγ hs).add hEγ hs).add hconst hs
    refine (hsum.mono_scale ?_).of_le_ae ?_ (Eventually.of_forall fun a => ?_)
    · have := mul_pos h8 hCG; have := div_pos hsK hl2; rw [hC₁]; linarith
    · have hm : AEMeasurable (fun a => max (max (max (XG a ^ γ) (XD a ^ γ))
          ((1 + d) ^ γ * XE a ^ γ)) (R₀ ^ γ)) P :=
        ((hXGos.1.max hDγ.1).max hEγ.1).max aemeasurable_const
      exact hm.congr (Eventually.of_forall fun a => (hpow a).symm)
    · rw [hpow a]
      have h1 := Real.rpow_nonneg (hXG0 a) γ
      have h2 := Real.rpow_nonneg (hXD0 a) γ
      have h3 : 0 ≤ (1 + d) ^ γ * XE a ^ γ := mul_nonneg h1d.le (Real.rpow_nonneg (hXE0 a) γ)
      simp only [max_le_iff]
      refine ⟨⟨⟨by linarith, by linarith⟩, by linarith⟩, by linarith⟩
  · -- the observation scale
    have h1 := hYGos.const_mul h8
    have hconst : AEOsBound P (fun _ => Real.sqrt KE * Sr ^ (-β)) s
        (Real.sqrt KE * Sr ^ (-β) / Real.log 2 ^ s⁻¹) :=
      (osBound_of_le_const measurable_const hs0 (mul_pos hsK hSβ)
        (Eventually.of_forall fun _ => le_rfl)).aeOsBound_of_ae_eq EventuallyEq.rfl
    refine (h1.add hconst hs).mono_scale ?_
    have e : Real.sqrt (8 * CD) * (CG * Sr ^ (-β)) + Real.sqrt KE * Sr ^ (-β) /
        Real.log 2 ^ s⁻¹ = (Real.sqrt (8 * CD) * CG + Real.sqrt KE / Real.log 2 ^ s⁻¹) *
          Sr ^ (-β) := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ hSβ.le
    have := div_pos hRγ hl2
    have := mul_pos h1d hCsγ
    rw [hC₁]
    linarith
  · -- the pathwise estimate
    filter_upwards [hGae, hDae, hE8ae,
      ae_all_iff.2 fun i : Fin d => (S.corrector (unitVector i)).weak_gradient,
      ae_all_iff.2 fun i : Fin d => (S.corrector (unitVector i)).locally_square_integrable,
      ae_all_iff.2 fun i : Fin d => (S.corrector (unitVector i)).harmonic]
      with a hGa hDa hE8a hwg hloc harm hXr
    simp only [max_le_iff] at hXr
    obtain ⟨⟨⟨hXGr, hXDr⟩, hXEr⟩, hR₀r⟩ := hXr
    obtain ⟨hYsmall, hobs⟩ := hGa hXGr
    have hμr : r ^ (-min μG β) ≥ r ^ (-μG) :=
      Real.rpow_le_rpow_of_exponent_le hr1 (by linarith [min_le_left μG β])
    have hμr' : r ^ (-min μG β) ≥ r ^ (-β) :=
      Real.rpow_le_rpow_of_exponent_le hr1 (by linarith [min_le_right μG β])
    have hSβr : Sr ^ (-β) ≤ r ^ (-β) :=
      Real.rpow_le_rpow_of_nonpos hr0 hrS (by linarith)
    refine ⟨?_, fun i => ?_⟩
    · have h1 : Real.sqrt (8 * CD) * YG a ≤ Real.sqrt (8 * CD) * CG * r ^ (-min μG β) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hYsmall.trans
          (mul_le_mul_of_nonneg_left hμr hCG.le)) h8.le
      have h2 : Real.sqrt KE * Sr ^ (-β) ≤ Real.sqrt KE * r ^ (-min μG β) :=
        mul_le_mul_of_nonneg_left (hSβr.trans hμr') hsK.le
      have hrμ : 0 ≤ r ^ (-min μG β) := Real.rpow_nonneg hr0.le _
      have h3 : (Real.sqrt (8 * CD) * CG + Real.sqrt KE) * r ^ (-min μG β) ≤
          C₁ * r ^ (-min μG β) := by
        refine mul_le_mul_of_nonneg_right ?_ hrμ
        have := div_pos hRγ hl2; have := div_pos hsK hl2; have := mul_pos h1d hCsγ
        rw [hC₁]; linarith
      show Real.sqrt (8 * CD) * YG a + Real.sqrt KE * Sr ^ (-β) ≤ C₁ * r ^ (-min μG β)
      calc Real.sqrt (8 * CD) * YG a + Real.sqrt KE * Sr ^ (-β)
          ≤ Real.sqrt (8 * CD) * CG * r ^ (-min μG β) + Real.sqrt KE * r ^ (-min μG β) :=
            add_le_add h1 h2
        _ = (Real.sqrt (8 * CD) * CG + Real.sqrt KE) * r ^ (-min μG β) := by ring
        _ ≤ C₁ * r ^ (-min μG β) := h3
    · obtain ⟨c, hc⟩ := hobs i
      have hRr : R₀ ≤ r := hR₀r
      obtain ⟨hLST, habs⟩ := hR₀ r hRr
      have hXE' : XE a + d ≤ Tr := by
        have h1 := mul_le_mul_of_nonneg_left (hXE1 a) (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
        have e : (1 + (d : ℝ)) * XE a = XE a + d * XE a := by ring
        linarith
      have henergy := (hE8a i Tr hXE').2
      have hadm : vectorRms volume (ball z Tr) (fun x => unitVector i +
          (S.corrector (unitVector i)).grad a x) ≤ C₀ :=
        (vectorRms_le_of_integral_le (lt_of_lt_of_le hS0 hST) henergy).trans hC₀
      have hDa' := hDa Sr Tr (hXDr.trans hrS) hLST
      have hmain := selected_observation_le hS0 hST (mul_pos hσ hS0).ne' hC₀0.le hCD.le hDa'
        habs ((W a z r hr).coordinate i) ((W a z r hr).selected i).1 (hwg i) (hloc i) (harm i)
        c hadm hc
      refine ⟨-c, hmain.trans ?_⟩
      have herr := observation_error_le hr1 hε hβ.le hk
      have hq0 : 0 ≤ (Sr / Tr) ^ (2 * k) := Real.rpow_nonneg (div_nonneg hS0.le
        (hS0.le.trans hST)) _
      have hE : 24 * CD * (Sr / Tr) ^ (2 * k) * (Tr / Sr) ^ (2 * d) * (2 ^ d * (2 * Tr)) ^ 2 *
          C₀ ^ 2 ≤ KE * (Sr ^ 2 * (Sr ^ (-β)) ^ 2) := by
        have e : 24 * CD * (Sr / Tr) ^ (2 * k) * (Tr / Sr) ^ (2 * d) * (2 ^ d * (2 * Tr)) ^ 2 *
            C₀ ^ 2 = KE * ((Sr / Tr) ^ (2 * k) * (Tr / Sr) ^ (2 * d) * Tr ^ 2) := by
          rw [hKE]; ring
        rw [e]
        exact mul_le_mul_of_nonneg_left herr hKE0.le
      have hYa : 0 ≤ YG a := hYG0 a
      have hB : 0 ≤ volume.real (ball z Sr) := measureReal_nonneg
      have hsq8 : Real.sqrt (8 * CD) ^ 2 = 8 * CD := Real.sq_sqrt (by positivity)
      have hsqK : Real.sqrt KE ^ 2 = KE := Real.sq_sqrt hKE0.le
      have hcross : 0 ≤ 2 * (Real.sqrt (8 * CD) * YG a) * (Real.sqrt KE * Sr ^ (-β)) :=
        mul_nonneg (mul_nonneg zero_le_two (mul_nonneg h8.le hYa))
          (mul_nonneg hsK.le hSβ.le)
      have hfin : 8 * CD * (Sr * YG a) ^ 2 + KE * (Sr ^ 2 * (Sr ^ (-β)) ^ 2) ≤
          (Sr * (Real.sqrt (8 * CD) * YG a + Real.sqrt KE * Sr ^ (-β))) ^ 2 := by
        have e : (Sr * (Real.sqrt (8 * CD) * YG a + Real.sqrt KE * Sr ^ (-β))) ^ 2 =
            Sr ^ 2 * (Real.sqrt (8 * CD) ^ 2 * YG a ^ 2 + Real.sqrt KE ^ 2 * (Sr ^ (-β)) ^ 2 +
              2 * (Real.sqrt (8 * CD) * YG a) * (Real.sqrt KE * Sr ^ (-β))) := by ring
        rw [e, hsq8, hsqK]
        calc 8 * CD * (Sr * YG a) ^ 2 + KE * (Sr ^ 2 * (Sr ^ (-β)) ^ 2)
            = Sr ^ 2 * (8 * CD * YG a ^ 2 + KE * (Sr ^ (-β)) ^ 2) := by ring
          _ ≤ Sr ^ 2 * (8 * CD * YG a ^ 2 + KE * (Sr ^ (-β)) ^ 2 +
              2 * (Real.sqrt (8 * CD) * YG a) * (Real.sqrt KE * Sr ^ (-β))) :=
            mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg Sr)
      calc volume.real (ball z Sr) * (8 * CD * (Sr * YG a) ^ 2 +
            24 * CD * (Sr / Tr) ^ (2 * k) * (Tr / Sr) ^ (2 * d) * (2 ^ d * (2 * Tr)) ^ 2 *
              C₀ ^ 2)
          ≤ volume.real (ball z Sr) * (8 * CD * (Sr * YG a) ^ 2 +
              KE * (Sr ^ 2 * (Sr ^ (-β)) ^ 2)) := by
            exact mul_le_mul_of_nonneg_left (by linarith) hB
        _ ≤ volume.real (ball z Sr) *
              (Sr * (Real.sqrt (8 * CD) * YG a + Real.sqrt KE * Sr ^ (-β))) ^ 2 :=
            mul_le_mul_of_nonneg_left hfin hB
        _ = (Sr * (Real.sqrt (8 * CD) * YG a + Real.sqrt KE * Sr ^ (-β))) ^ 2 *
              volume.real (ball z Sr) := by ring

/-- **(5.85) from the finite-ball observation and the observation of the smoothed
correctors.** If for every `k > 0` some `σ, θ ∈ (0, 1/2]` carry the finite-ball observation, and
for every window, construction exponent and `σ, θ > 0` the smoothed correctors are observed at
the fluctuation exponent `d/2`, then `QSH.Frozen.localizedEnergy` holds. -/
theorem localizedEnergy_of_finiteBall_smoothed
    (hD : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ k : ℝ, 0 < k →
      ∃ σ θ : ℝ, 0 < σ ∧ σ ≤ 1 / 2 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ FiniteBallObservation d Λ σ θ k)
    (hG : ∀ (d : ℕ), 2 ≤ d → ∀ Λ s δ γ : ℝ,
      1 < Λ → 1 < s → s < 2 → 0 < δ →
      (d : ℝ) / 2 * (1 + δ) < γ →
      γ < min ((d : ℝ) / s) ((d : ℝ) / 2 * (1 + δ) + δ) →
      ∀ α : ℝ, 0 < α → α ≤ (d : ℝ) / 2 → γ < α * (1 + δ) + δ → ∀ σ θ : ℝ, 0 < σ → 0 < θ →
      ∃ μ C : ℝ, 0 < μ ∧ 0 < C ∧ ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
        ∃ S : HomogenizationData P, SmoothedCorrectorObservation S s δ γ α σ θ ((d : ℝ) / 2) μ C) :
    QSH.Frozen.localizedEnergy := by
  refine localizedEnergy_of_observation fun d hd Λ s δ γ hΛ hs1 hs2 hδ hγ1 hγ2 α hα hαd hαγ => ?_
  have hε : 0 < localizationEpsilon δ α γ := localizationEpsilon_pos hδ hα hαγ
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hβ : 0 < (d : ℝ) / 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set k : ℝ := (d : ℝ) + 1 + (d : ℝ) / 2 * (1 + δ) / localizationEpsilon δ α γ with hk
  have hk0 : 0 < k := by
    have : 0 ≤ (d : ℝ) / 2 * (1 + δ) / localizationEpsilon δ α γ :=
      div_nonneg (mul_nonneg hβ.le (by linarith)) hε.le
    linarith
  obtain ⟨σ, θ, hσ, hσ2, hθ, hθ2, hDσ⟩ := hD d hd Λ hΛ k hk0
  have hs0 : 0 < s := by linarith
  have hγ0 : 0 < γ := lt_of_le_of_lt (mul_nonneg hβ.le (by linarith)) hγ1
  have hγs : s * γ < d := by
    have h1 : γ < (d : ℝ) / s := lt_of_lt_of_le hγ2 (min_le_left _ _)
    rw [lt_div_iff₀ hs0] at h1
    linarith
  obtain ⟨C₀, hC₀, hobs⟩ := localizationObservationEstimate_of_finiteBall hd hΛ hs1.le hδ hα hαγ
    hγ0 hγs hβ hσ le_rfl hDσ (hG d hd Λ s δ γ hΛ hs1 hs2 hδ hγ1 hγ2 α hα hαd hαγ σ θ hσ hθ)
  exact ⟨σ, θ, C₀, hσ, hσ2, hθ, hθ2, hC₀, hobs C₀ le_rfl⟩

end QSH
