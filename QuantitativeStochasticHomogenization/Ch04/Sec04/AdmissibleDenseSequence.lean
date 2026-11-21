import QuantitativeStochasticHomogenization.Ch04.Sec04.EnergyProjection

/-!
# A measurable dense sequence in the admissible class, and measurability of `J₁^{(δ)}`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.4, p. 156: `J₁^{(δ)}(z, r, p, q)` is `F(B_{r^{1+δ}}(z))`-measurable.

Fix a dense sequence `v_n` of gradient pairs and a dense sequence `t_m` of the closed span `T₀` of
the test pairs. The energy projection `P_a v_n` is the unique minimizer over `T₀` of the energy
`B_a(v_n - t, v_n - t)`, which is measurable in `a` at every `t_m`; hence `a ↦ P_a v_n` is
measurable. The harmonic extensions `v_n - P_a v_n`, rescaled into the gradient bound of the
admissible class, are dense in it. The least-norm coordinate minimizers are therefore
measurable, and so is the localized energy.
-/

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ} {z : Vec d} {T : ℝ}

/-- A nonempty set in a second countable space contains a sequence dense in it. -/
theorem exists_seq_dense_in {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    {s : Set X} (hs : s.Nonempty) :
    ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧ s ⊆ closure (Set.range u) := by
  have : Nonempty s := hs.to_subtype
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq s
  refine ⟨fun n => u n, fun n => (u n).2, fun y hy => ?_⟩
  have hy' : (⟨y, hy⟩ : s) ∈ closure (Set.range u) := by
    rw [hu.closure_range]; exact Set.mem_univ _
  exact map_mem_closure continuous_subtype_val hy' (by rintro _ ⟨n, rfl⟩; exact ⟨n, rfl⟩)

/-- The energy projection `P_a v`. -/
def energyProj (a : CoefficientField d Λ) (hΛ : 0 ≤ Λ) (hT : 0 < T) (v : PairSpace d z T) :
    PairSpace d z T :=
  Classical.choose (exists_energyProjection a hΛ hT v)

theorem energyProj_mem (a : CoefficientField d Λ) (hΛ : 0 ≤ Λ) (hT : 0 < T)
    (v : PairSpace d z T) : energyProj a hΛ hT v ∈ testPairClosure d z T :=
  (Classical.choose_spec (exists_energyProjection a hΛ hT v)).1

theorem energyProj_min (a : CoefficientField d Λ) (hΛ : 0 ≤ Λ) (hT : 0 < T)
    (v : PairSpace d z T) :
    ∀ t' ∈ (testPairClosure d z T : Set (PairSpace d z T)),
      energyForm a (v - energyProj a hΛ hT v) (v - energyProj a hΛ hT v) ≤
        energyForm a (v - t') (v - t') :=
  (Classical.choose_spec (exists_energyProjection a hΛ hT v)).2

/-- **The energy projection is measurable in the coefficients.** -/
theorem measurable_energyProj (hΛ : 0 ≤ Λ) (hT : 0 < T) (v : PairSpace d z T) :
    @Measurable (CoefficientField d Λ) _ (localSigma (ball z T)) _
      fun a => energyProj a hΛ hT v := by
  obtain ⟨ts, hts, htsd⟩ := exists_seq_dense_in
    (⟨0, (testPairClosure d z T).zero_mem⟩ : (testPairClosure d z T : Set (PairSpace d z T)).Nonempty)
  exact measurable_lexicographic_minimizer_param (mΩ := localSigma (ball z T))
    isQuadraticGauge_pairGauge ((continuous_fst.norm.pow 2).add continuous_pairGradEnergy)
    (K := fun _ => (testPairClosure d z T : Set (PairSpace d z T)))
    (fun _ => isClosed_testPairClosure)
    (F := fun a t => energyForm a (v - t) (v - t)) (G := fun _ _ => (0 : ℝ))
    (fun a => continuous_energyForm_sub a hΛ v)
    (fun a => (convexOn_energyForm_sub a v).subset (Set.subset_univ _)
      (testPairClosure d z T).convex)
    (fun a t _ => energyForm_self_nonneg a _) (fun _ => continuous_const)
    (fun _ => convexOn_const 0 (testPairClosure d z T).convex) (fun _ _ _ => le_rfl)
    (fun a s => bddAbove_pairGauge_energy_sublevel a hT v s)
    (fun n _ => ts n) (fun n => measurable_const) (fun n _ => hts n)
    (fun n => measurable_energyForm _ _) (fun n => measurable_const) (fun _ => htsd)
    (fun a => energyProj a hΛ hT v) (fun a => energyProj_mem a hΛ hT v)
    (fun a => energyProj_min a hΛ hT v) (fun _ _ _ _ => le_rfl)
    (fun a y hy hmin _ => eq_of_isEnergyMinimizer a hT hy (energyProj_mem a hΛ hT v) hmin
      (energyProj_min a hΛ hT v))

/-! ## Rescaling into the gradient bound -/

/-- The rescaling `F ↦ (R / max(R, ‖F_g‖)) F` into the gradient bound `‖F_g‖ ≤ R`. -/
def clipPair (R : ℝ) (F : PairSpace d z T) : PairSpace d z T :=
  (R / max R (Real.sqrt (pairGradEnergy F))) • F

theorem continuous_clipPair {R : ℝ} (hR : 0 < R) :
    Continuous (clipPair R : PairSpace d z T → PairSpace d z T) := by
  have h1 : Continuous fun F : PairSpace d z T => R / max R (Real.sqrt (pairGradEnergy F)) :=
    continuous_const.div (continuous_const.max
      (Real.continuous_sqrt.comp continuous_pairGradEnergy))
      (fun F => (lt_of_lt_of_le hR (le_max_left _ _)).ne')
  exact h1.smul continuous_id

theorem pairGradEnergy_smul (c : ℝ) (F : PairSpace d z T) :
    pairGradEnergy (c • F) = c ^ 2 * pairGradEnergy F := by
  simp only [pairGradEnergy, Prod.smul_snd, Pi.smul_apply, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, Finset.mul_sum]

theorem clipPair_eq_self {R : ℝ} (hR : 0 < R) {F : PairSpace d z T}
    (hF : pairGradEnergy F ≤ R ^ 2) : clipPair R F = F := by
  have h : Real.sqrt (pairGradEnergy F) ≤ R := (Real.sqrt_le_left hR.le).2 hF
  rw [clipPair, max_eq_left h, div_self hR.ne', one_smul]

theorem pairGradEnergy_clipPair_le {R : ℝ} (hR : 0 < R) (F : PairSpace d z T) :
    pairGradEnergy (clipPair R F) ≤ R ^ 2 := by
  rw [clipPair, pairGradEnergy_smul]
  by_cases h : Real.sqrt (pairGradEnergy F) ≤ R
  · rw [max_eq_left h, div_self hR.ne', one_pow, one_mul]
    exact (Real.sqrt_le_left hR.le).1 h
  · push Not at h
    have hpos : 0 < Real.sqrt (pairGradEnergy F) := hR.trans h
    rw [max_eq_right h.le, div_pow, Real.sq_sqrt (pairGradEnergy_nonneg F),
      div_mul_cancel₀ _ (by rw [← Real.sq_sqrt (pairGradEnergy_nonneg F)]; positivity)]

theorem IsHarmonicPair.smul' {a : CoefficientField d Λ} {F : PairSpace d z T}
    (hF : IsHarmonicPair a F) (c : ℝ) : IsHarmonicPair a (c • F) :=
  ⟨fun φ hφ i => by rw [gradConstraint_smul, hF.1 φ hφ i, mul_zero],
    fun φ hφ => by rw [harmConstraint_smul, hF.2 φ hφ, mul_zero]⟩

/-! ## The dense sequence -/

/-- The admissible gradient bound radius `R = C |B_T(z)|^{1/2}`. -/
def admissibleRadius (z : Vec d) (T C : ℝ) : ℝ := C * Real.sqrt (volume.real (ball z T))

theorem admissibleRadius_pos (hT : 0 < T) {C : ℝ} (hC : 0 < C) : 0 < admissibleRadius z T C :=
  mul_pos hC (Real.sqrt_pos.2 (volume_real_ball_pos z hT))

theorem admissibleRadius_sq (z : Vec d) (T C : ℝ) :
    admissibleRadius z T C ^ 2 = C ^ 2 * volume.real (ball z T) := by
  rw [admissibleRadius, mul_pow, Real.sq_sqrt measureReal_nonneg]

/-- **A measurable dense sequence in the admissible class.** -/
theorem exists_measurable_dense_admissible (hΛ : 0 ≤ Λ) (hT : 0 < T) {C : ℝ} (hC : 0 < C) :
    ∃ h : ℕ → CoefficientField d Λ → PairSpace d z T,
      (∀ n, @Measurable _ _ (localSigma (ball z T)) _ (h n)) ∧
      (∀ n a, h n a ∈ admissiblePairs a z T C) ∧
      ∀ a, admissiblePairs a z T C ⊆ closure (Set.range fun n => h n a) := by
  obtain ⟨vs, hvs, hvsd⟩ := exists_seq_dense_in
    (⟨0, isGradientPair_zero⟩ : {F : PairSpace d z T | IsGradientPair F}.Nonempty)
  set R := admissibleRadius z T C
  have hR : 0 < R := admissibleRadius_pos hT hC
  refine ⟨fun n a => clipPair R (vs n - energyProj a hΛ hT (vs n)), fun n => ?_,
    fun n a => ?_, fun a F hF => ?_⟩
  · let _ : MeasurableSpace (CoefficientField d Λ) := localSigma (ball z T)
    exact ((continuous_clipPair hR).comp (continuous_const.sub continuous_id)).measurable.comp
      (measurable_energyProj hΛ hT (vs n))
  · refine ⟨(isHarmonicPair_sub_of_isEnergyMinimizer a (hvs n) (energyProj_mem a hΛ hT (vs n))
      (energyProj_min a hΛ hT (vs n))).smul' _, ?_⟩
    rw [← admissibleRadius_sq]
    exact pairGradEnergy_clipPair_le hR _
  · rw [Metric.mem_closure_iff]
    intro ε hε
    have hcont := (continuous_clipPair (d := d) (z := z) (T := T) hR).continuousAt (x := F)
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨δ, hδ, hδε⟩ := hcont ε hε
    have hFR : pairGradEnergy F ≤ R ^ 2 := by rw [admissibleRadius_sq]; exact hF.2
    rw [clipPair_eq_self hR hFR] at hδε
    set K := (ballPoincareConstant d T + 1) * ((d : ℝ) ^ 2 * Λ)
    have hK : 0 ≤ K := mul_nonneg (by linarith [ballPoincareConstant_nonneg d T])
      (mul_nonneg (sq_nonneg _) hΛ)
    set η := δ / (2 * (1 + Real.sqrt K))
    have hη : 0 < η := div_pos hδ (by positivity)
    obtain ⟨n, hn⟩ := Metric.mem_closure_range_iff.1 (hvsd hF.1.1) η hη
    refine ⟨_, ⟨n, rfl⟩, ?_⟩
    rw [dist_comm]
    refine hδε ?_
    set P := energyProj a hΛ hT (vs n)
    have hPg := pairGauge_le_of_isEnergyMinimizer a hΛ hT (energyProj_mem a hΛ hT (vs n))
      (energyProj_min a hΛ hT (vs n)) hF.1
    have hPn : ‖P‖ ≤ Real.sqrt K * ‖vs n - F‖ := by
      have h1 := (isQuadraticGauge_pairGauge.norm_sq_le P).trans hPg
      have h2 : ‖P‖ ^ 2 ≤ (Real.sqrt K * ‖vs n - F‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hK]; linarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
    have hvF : ‖vs n - F‖ < η := by rw [← dist_eq_norm, dist_comm]; exact hn
    rw [dist_eq_norm]
    calc ‖vs n - P - F‖ = ‖(vs n - F) - P‖ := by rw [sub_right_comm]
      _ ≤ ‖vs n - F‖ + ‖P‖ := norm_sub_le _ _
      _ ≤ (1 + Real.sqrt K) * ‖vs n - F‖ := by linarith
      _ ≤ (1 + Real.sqrt K) * η := mul_le_mul_of_nonneg_left hvF.le (by positivity)
      _ < δ := by
          rw [show (1 + Real.sqrt K) * η = δ / 2 by
            simp only [η]; field_simp]
          linarith

/-- **Measurability of the localized energy** (p. 156): for every family of localized bases,
`a ↦ J₁^{(δ)}` is measurable for the local σ-algebra of the outer ball. -/
theorem measurable_localizedJ1_of_basis (hΛ : 0 ≤ Λ) (hT : 0 < T) {S σ θ C : ℝ}
    (hσS : σ * S ≠ 0) (hSθ : 0 < S / θ) (hC : 0 < C) {r : ℝ} (hr : r ≠ 0) (p q : Vec d)
    (W : ∀ a : CoefficientField d Λ, LocalizedBasis a z T S σ θ C) :
    @Measurable _ ℝ (localSigma (ball z T)) _ fun a => localizedJ1 (W a) r p q := by
  obtain ⟨h, hh, hmem, hdense⟩ := exists_measurable_dense_admissible (z := z) hΛ hT hC
  exact measurable_localizedJ1 hΛ hr p q W fun i =>
    measurable_toPair_of_denseSeq hT hσS hSθ hC.le i h hh hmem hdense
      (fun a => (W a).coordinate i) (fun a => (W a).selected i)

end QSH
