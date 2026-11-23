import QuantitativeStochasticHomogenization.Ch04.Sec01.GaussianCorrectorRealization
import QuantitativeStochasticHomogenization.Ch04.Sec01.HomogenizedFluxIdentification
import QuantitativeStochasticHomogenization.Ch03.Sec04.CorrectorMeasurability
import QuantitativeStochasticHomogenization.Ch04.Sec03.CellMeanTools

/-!
# Proposition 3.21 with constants chosen before the law

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Proposition 3.21, for `d ≥ 2` and `Λ > 1`: there are `C(τ)`, `μ(τ) > 0`, `0 < τ < d`, such that
every law satisfying (P1)–(P2) has homogenization data `S` with `GaussianCorrectorRate P S τ C(τ)
μ(τ)` (`uniformGaussianCorrectorRate`).

The homogenization data is any one given by `homogenizationDataExists`. Almost surely its
coordinate corrected fields satisfy the bounds on the masks `Φ_{x₀,r}`, `|x₀| ≤ r`,
`r ≥ Y = B X` (`X` the homogenization scale of Armstrong, Kuusi and Loher), with error
`C (Y/r)^θ` and the homogenized matrix `ā` of that theorem (`exists_ae_gaussianBasisBounds`);
`ā` is the homogenized matrix of `S` (`homogenized_eq_of_basisBounds`). For a center `z` the
bounds are transported from the lattice point `k` nearest to `z` by stationarity, and the scale is
`X(a, z) = max(Y(T_k a), √d)^p`, `p = 2d/(d + τ)`, which is `O_τ(C)` and gives the rate
`μ = θ (d - τ)/(2d)`.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-! ## Monotonicity and translation of the bounds (3.101)–(3.103) -/

theorem GaussianAverageBounds.mono {a : CoefficientField d Λ} {A : Mat d}
    {G : Vec d → Vec d → Vec d} {z : Vec d} {r ε ε' : ℝ} (h : GaussianAverageBounds a A G z r ε)
    (hε : ε ≤ ε') : GaussianAverageBounds a A G z r ε' := by
  intro ξ
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h ξ
  have hξ : 0 ≤ euclideanNorm ξ := Real.sqrt_nonneg _
  refine ⟨h1, h2, h3, h4.trans (by gcongr), h5.trans (by gcongr), h6.trans ?_⟩
  have : 0 ≤ euclideanNorm ξ ^ 2 := sq_nonneg _
  nlinarith

theorem heatKernel_add_eq (z k : Vec d) (r : ℝ) (x : Vec d) :
    heatKernel z r (x + k) = heatKernel (z - k) r x := by
  unfold heatKernel
  congr 1
  abel

/-- **Translating a Gaussian average.** -/
theorem integrable_and_integral_heatKernel_translate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F F' : Vec d → E} (k : Vec d) (hF : ∀ᵐ x, F (x + k) = F' x)
    {z : Vec d} {r : ℝ} (hi : Integrable fun x => heatKernel (z - k) r x • F' x) :
    Integrable (fun x => heatKernel z r x • F x) ∧
      ∫ x, heatKernel z r x • F x = ∫ x, heatKernel (z - k) r x • F' x := by
  have hi' : Integrable fun x => heatKernel (z - k) r x • F (x + k) := by
    refine hi.congr ?_
    filter_upwards [hF] with x hx
    rw [hx]
  have hfun : (fun x => heatKernel z r x • F x) =
      fun x => heatKernel (z - k) r (x - k) • F (x - k + k) := by
    funext x
    rw [← heatKernel_add_eq, sub_add_cancel]
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hi'.comp_sub_right k
  · rw [hfun, integral_sub_right_eq_self (fun x => heatKernel (z - k) r x • F (x + k)) k]
    refine integral_congr_ae ?_
    filter_upwards [hF] with x hx
    rw [hx]

theorem translate_field_apply (k : Vec d) (a : CoefficientField d Λ) (x : Vec d) :
    (translate k a) x = a (x + k) := by
  show a.field (k + x) = a.field (x + k)
  rw [add_comm]

/-- **The bounds (3.101)–(3.103) transported along a translation.** -/
theorem gaussianAverageBounds_of_translate {a : CoefficientField d Λ} {A : Mat d}
    {G G' : Vec d → Vec d → Vec d} (k : Vec d) (hG : ∀ ξ, ∀ᵐ x, G ξ (x + k) = G' ξ x)
    {z : Vec d} {r ε : ℝ} (h : GaussianAverageBounds (translate k a) A G' (z - k) r ε) :
    GaussianAverageBounds a A G z r ε := by
  intro ξ
  obtain ⟨i1, i2, i3, b1, b2, b3⟩ := h ξ
  have t1 := integrable_and_integral_heatKernel_translate k (hG ξ) i1
  have hq : ∀ᵐ x, (a (x + k)).mulVec (G ξ (x + k)) = ((translate k a) x).mulVec (G' ξ x) := by
    filter_upwards [hG ξ] with x hx
    rw [hx, translate_field_apply]
  have t2 := integrable_and_integral_heatKernel_translate (F := fun x => (a x).mulVec (G ξ x)) k
    hq i2
  have hE : ∀ᵐ x, dot (G ξ (x + k)) ((a (x + k)).mulVec (G ξ (x + k))) =
      dot (G' ξ x) (((translate k a) x).mulVec (G' ξ x)) := by
    filter_upwards [hG ξ] with x hx
    rw [hx, translate_field_apply]
  have i3' : Integrable fun x => heatKernel (z - k) r x •
      dot (G' ξ x) (((translate k a) x).mulVec (G' ξ x)) := by
    simpa only [smul_eq_mul] using i3
  have t3 := integrable_and_integral_heatKernel_translate
    (F := fun x => dot (G ξ x) ((a x).mulVec (G ξ x))) k hE i3'
  simp only [smul_eq_mul] at t3
  refine ⟨t1.1, t2.1, t3.1, ?_, ?_, ?_⟩
  · rw [t1.2]; exact b1
  · rw [t2.2]; exact b2
  · rw [t3.2]; exact b3

/-! ## The nearest lattice point -/

/-- The lattice point `⌊z + 1/2⌋` nearest to `z`. -/
def latticeRound (z : Vec d) : LatticeIndex d := fun i => ⌊z i + 1 / 2⌋

theorem measurable_latticeRound : Measurable (latticeRound (d := d)) :=
  measurable_pi_iff.mpr fun i => Int.measurable_floor.comp ((measurable_pi_apply i).add_const _)

theorem euclideanNorm_sub_latticeRound_le (z : Vec d) :
    euclideanNorm (z - latticeShift (latticeRound z)) ≤ Real.sqrt d := by
  have h : ∀ i, |(z - latticeShift (latticeRound z)) i| ≤ 1 := by
    intro i
    simp only [Pi.sub_apply, latticeShift, latticeRound]
    have h1 := Int.floor_le (z i + 1 / 2)
    have h2 := Int.lt_floor_add_one (z i + 1 / 2)
    rw [abs_le]
    constructor <;> linarith
  have := euclideanNorm_le_sqrt_mul_of_abs_le h
  rwa [mul_one] at this

/-- The corrected fields are stationary in the sense of `gaussianAverageBounds_of_translate`. -/
theorem ae_correctedField_add_latticeShift_all {P : Measure (CoefficientField d Λ)}
    (S : HomogenizationData P) (n : LatticeIndex d) :
    ∀ᵐ a ∂P, ∀ ξ : Vec d, ∀ᵐ x, correctedField S a ξ (x + latticeShift n) =
      correctedField S (translate (latticeShift n) a) ξ x := by
  have h : ∀ᵐ a ∂P, ∀ i : Fin d, ∀ᵐ x,
      (S.corrector (unitVector i)).grad a (x + latticeShift n) =
        (S.corrector (unitVector i)).grad (translate (latticeShift n) a) x :=
    ae_all_iff.mpr fun i => (S.corrector (unitVector i)).stationary n
  filter_upwards [h] with a ha ξ
  filter_upwards [ae_all_iff.mpr ha] with x hx
  unfold correctedField correctedCoordinate
  exact Finset.sum_congr rfl fun i _ => by rw [hx i]

/-! ## Proposition 3.21 -/

theorem max_rpow_eq {u v p : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hp : 0 ≤ p) :
    max u v ^ p = max (u ^ p) (v ^ p) := by
  rcases le_total u v with h | h
  · rw [max_eq_right h, max_eq_right (Real.rpow_le_rpow hu h hp)]
  · rw [max_eq_left h, max_eq_left (Real.rpow_le_rpow hv h hp)]

/-- The exponent `p = 2d/(d + τ)` of the scale at the exponent `τ`. -/
def ratePower (d : ℕ) (τ : ℝ) : ℝ := 2 * d / (d + τ)

theorem one_lt_ratePower {d : ℕ} {τ : ℝ} (hτ : 0 < τ) (hτd : τ < d) : 1 < ratePower d τ := by
  unfold ratePower
  rw [lt_div_iff₀ (by linarith)]
  linarith

theorem le_div_ratePower {d : ℕ} {τ : ℝ} (hτ : 0 < τ) (hτd : τ < d) : τ ≤ (d : ℝ) / ratePower d τ := by
  have hd0 : (0 : ℝ) < d := hτ.trans hτd
  unfold ratePower
  rw [div_div_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith

/-- **Proposition 3.21 from the coordinate bounds above a scale.** If `Y ≥ 1` is measurable,
`max(Y, √d)^p ≤ O_τ(C₁)` for `p = 2d/(d + τ)`, and almost surely the coordinate fields satisfy the
bounds with the homogenized matrix of `S` above `Y` at every mask `Φ_{x₀,r}`, `|x₀| ≤ r`, with error
`C (Y/r)^θ`, then `GaussianCorrectorRate P S τ (max C₁ (d² C)) (θ (1 - 1/p))`. -/
theorem gaussianCorrectorRate_of_basisBounds {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (S : HomogenizationData P) {Y : CoefficientField d Λ → ℝ}
    (hYm : Measurable Y) (hY1 : ∀ a, 1 ≤ Y a) {τ C₁ Cε θ : ℝ} (hτ : 0 < τ) (hτd : τ < d)
    (hCε : 0 ≤ Cε) (hθ : 0 < θ)
    (hos : OsBound P (fun a => max (Y a) (Real.sqrt d) ^ ratePower d τ) τ C₁)
    (hB : ∀ᵐ a ∂P, ∀ (r : ℝ) (x₀ : Vec d), Y a ≤ r → euclideanNorm x₀ ≤ r →
      GaussianBasisBounds a S.homogenized (correctedCoordinate S a) x₀ r (Cε * (Y a / r) ^ θ)) :
    GaussianCorrectorRate P S τ (max C₁ ((d : ℝ) ^ 2 * Cε)) (θ * (1 - (ratePower d τ)⁻¹)) := by
  set p := ratePower d τ with hp
  have hp1 : 1 < p := one_lt_ratePower hτ hτd
  have hp0 : 0 < p := zero_lt_one.trans hp1
  have hY0 : ∀ a, 0 ≤ Y a := fun a => zero_le_one.trans (hY1 a)
  have hW0 : ∀ a, 0 ≤ max (Y a) (Real.sqrt d) := fun a => (hY0 a).trans (le_max_left _ _)
  have hWm : Measurable fun a => max (Y a) (Real.sqrt d) := hYm.max measurable_const
  have hTmp : ∀ k : LatticeIndex d,
      MeasurePreserving (translate (latticeShift k)) P P := fun k =>
    ⟨measurable_translateCoefficient _, hP.2.1 k⟩
  refine ⟨fun a z => max (Y (translate (latticeShift (latticeRound z)) a)) (Real.sqrt d) ^ p,
    ?_, fun z => ⟨?_, ?_⟩⟩
  · -- joint measurability
    have hg : Measurable fun q : CoefficientField d Λ × LatticeIndex d =>
        max (Y (translate (latticeShift q.2) q.1)) (Real.sqrt d) ^ p :=
      measurable_from_prod_countable_left
        (f := fun q : CoefficientField d Λ × LatticeIndex d =>
          max (Y (translate (latticeShift q.2) q.1)) (Real.sqrt d) ^ p) fun k =>
        (hWm.comp (measurable_translateCoefficient (latticeShift k))).pow_const p
    exact hg.comp (measurable_fst.prodMk (measurable_latticeRound.comp measurable_snd))
  · -- the stochastic integrability of the scale
    exact (hos.comp_measurePreserving (hTmp (latticeRound z))).mono_scale (le_max_left _ _)
  · -- the bounds
    set k := latticeRound z with hk
    filter_upwards [(hTmp k).quasiMeasurePreserving.ae hB,
      ae_correctedField_add_latticeShift_all S k] with a ha hst
    intro r hr1 hXr
    set a' := translate (latticeShift k) a with ha'
    have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
    have hWr : max (Y a') (Real.sqrt d) ≤ r ^ p⁻¹ := by
      have h := Real.rpow_le_rpow (Real.rpow_nonneg (hW0 a') _) hXr (inv_nonneg.mpr hp0.le)
      rwa [Real.rpow_rpow_inv (hW0 a') hp0.ne'] at h
    have hrr : r ^ p⁻¹ ≤ r := by
      have h := Real.rpow_le_rpow_of_exponent_le hr1 (inv_le_one_of_one_le₀ hp1.le)
      rwa [Real.rpow_one] at h
    have hYr : Y a' ≤ r ^ p⁻¹ := (le_max_left _ _).trans hWr
    have hx : euclideanNorm (z - latticeShift k) ≤ r :=
      (euclideanNorm_sub_latticeRound_le z).trans (((le_max_right _ _).trans hWr).trans hrr)
    have hb := ha r (z - latticeShift k) (hYr.trans hrr) hx
    have hεpos : 0 ≤ Cε * (Y a' / r) ^ θ :=
      mul_nonneg hCε (Real.rpow_nonneg (div_nonneg (hY0 a') hr0.le) _)
    have hg := gaussianAverageBounds_of_basis hεpos hb
    have htr := gaussianAverageBounds_of_translate (G := correctedField S a)
      (G' := correctedField S a') (latticeShift k) hst hg
    refine htr.mono ?_
    have hpow : (Y a' / r) ^ θ ≤ r ^ (-(θ * (1 - p⁻¹))) := by
      have h1 : Y a' / r ≤ r ^ p⁻¹ / r := div_le_div_of_nonneg_right hYr hr0.le
      have h2 : r ^ p⁻¹ / r = r ^ (p⁻¹ - 1) := by
        rw [Real.rpow_sub hr0, Real.rpow_one]
      have h3 : (r ^ (p⁻¹ - 1)) ^ θ = r ^ (-(θ * (1 - p⁻¹))) := by
        rw [← Real.rpow_mul hr0.le]
        congr 1
        ring
      calc (Y a' / r) ^ θ ≤ (r ^ p⁻¹ / r) ^ θ :=
            Real.rpow_le_rpow (div_nonneg (hY0 a') hr0.le) h1 hθ.le
        _ = r ^ (-(θ * (1 - p⁻¹))) := by rw [h2, h3]
    have hr' : 0 ≤ r ^ (-(θ * (1 - p⁻¹))) := Real.rpow_nonneg hr0.le _
    calc (d : ℝ) ^ 2 * (Cε * (Y a' / r) ^ θ)
        ≤ (d : ℝ) ^ 2 * (Cε * r ^ (-(θ * (1 - p⁻¹)))) := by gcongr
      _ = ((d : ℝ) ^ 2 * Cε) * r ^ (-(θ * (1 - p⁻¹))) := by ring
      _ ≤ max C₁ ((d : ℝ) ^ 2 * Cε) * r ^ (-(θ * (1 - p⁻¹))) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hr'

/-- The scale constant at the exponent `τ`. -/
def rateScaleConst (d : ℕ) (A τ : ℝ) : ℝ :=
  (2 : ℝ) ^ τ⁻¹ * max ((8 : ℝ) ^ τ⁻¹ * A ^ ratePower d τ)
    (Real.sqrt d ^ ratePower d τ / Real.log 2 ^ τ⁻¹)

/-- **Proposition 3.21 with constants chosen before the law.** -/
theorem uniformGaussianCorrectorRate (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 < Λ) :
    ∃ C μ : ℝ → ℝ, (∀ τ : ℝ, 0 < τ → τ < d → 0 < C τ ∧ 0 < μ τ) ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∃ S : HomogenizationData P,
        ∀ τ : ℝ, 0 < τ → τ < d → GaussianCorrectorRate P S τ (C τ) (μ τ) := by
  obtain ⟨κ, C₀, hκ, hC₀, hpk⟩ := exists_highContrastCorrectorPackage d hd
  obtain ⟨B, Cε, θ', Cφ, θ, hB1, hCε, hθ', -, -, hθ, hθ1, hmain⟩ :=
    exists_ae_gaussianBasisBounds d hd Λ hΛ hκ hC₀.le
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hK2 : (0 : ℝ) < 2 + Λ / 1 := by linarith
  have hc₁0 : 0 < C₀ * (2 + Λ / 1) ^ C₀ := mul_pos hC₀ (Real.rpow_pos_of_pos hK2 _)
  have hB0 : 0 < B := lt_of_lt_of_le one_pos hB1
  have hA0 : 0 < B * (C₀ * (2 + Λ / 1) ^ C₀) := mul_pos hB0 hc₁0
  refine ⟨fun τ => max (rateScaleConst d (B * (C₀ * (2 + Λ / 1) ^ C₀)) τ) ((d : ℝ) ^ 2 * Cε),
    fun τ => θ' * (1 - (ratePower d τ)⁻¹), ?_, ?_⟩
  · intro τ hτ hτd
    have hp1 := one_lt_ratePower hτ hτd
    refine ⟨lt_max_of_lt_left ?_, mul_pos hθ' ?_⟩
    · unfold rateScaleConst
      exact mul_pos (by positivity) (lt_max_of_lt_left (mul_pos (by positivity)
        (Real.rpow_pos_of_pos hA0 _)))
    · have : (ratePower d τ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
      linarith
  intro P hP
  have : IsProbabilityMeasure P := hP.1
  obtain ⟨pk⟩ := hpk Λ hΛ.le P hP
  obtain ⟨S⟩ := homogenizationDataExists d hd Λ hΛ P hP
  obtain ⟨hbasis, hosc⟩ := hmain P pk hP S
  obtain ⟨Y, hYdef⟩ : ∃ Y : CoefficientField d Λ → ℝ,
      Y = fun a => B * pk.X (toHighContrast hΛ.le a) := ⟨_, rfl⟩
  have hYm : Measurable Y := by
    rw [hYdef]
    exact (pk.measurable_X.comp (measurable_toHighContrast hΛ.le)).const_mul B
  have hY1 : ∀ a, 1 ≤ Y a := fun a => by
    rw [hYdef]
    exact one_le_mul_of_one_le_of_one_le hB1 (pk.one_le_X _)
  have hY0 : ∀ a, 0 ≤ Y a := fun a => zero_le_one.trans (hY1 a)
  have hbasis' : ∀ᵐ a ∂P, ∀ (r : ℝ) (x₀ : Vec d), Y a ≤ r → euclideanNorm x₀ ≤ r →
      GaussianBasisBounds a pk.abar (correctedCoordinate S a) x₀ r (Cε * (Y a / r) ^ θ') := by
    rw [hYdef]
    exact hbasis
  have hosc' : ∀ i : Fin d, ∀ᵐ a ∂P, ∀ ρ : ℝ, Y a ≤ ρ →
      Real.sqrt (⨍ x in ball 0 ρ, |(S.corrector (unitVector i)).potential a x -
        ⨍ y in ball 0 ρ, (S.corrector (unitVector i)).potential a y| ^ 2) ≤
          Cφ * ρ ^ (1 - θ) * Y a ^ θ := by
    rw [hYdef]
    exact hosc
  -- the tail of `Y^q`
  have hYos : ∀ q : ℝ, 0 < q → ∀ s : ℝ, 0 < s → s ≤ (d : ℝ) / q →
      OsBound P (fun a => Y a ^ q) s ((8 : ℝ) ^ s⁻¹ * (B * (C₀ * (2 + Λ / 1) ^ C₀)) ^ q) := by
    intro q hq s hs hsq
    rw [hYdef]
    exact osBound_of_tail (hYm.pow_const q |> fun _ =>
      ((pk.measurable_X.comp (measurable_toHighContrast hΛ.le)).const_mul B).pow_const q) hs hsq
      (Real.rpow_pos_of_pos hA0 q) fun t ht => pk.measure_scaledX_le hP hB0 hq hC₀.le ht
  have hYmom : ∀ m : ℕ, Integrable (fun a => Y a ^ m) P := by
    intro m
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp
    · have hmR : (0 : ℝ) < m := by exact_mod_cast hm
      have h := hYos m hmR (1 / m) (by positivity)
        (div_le_div_of_nonneg_right (by exact_mod_cast hd1) hmR.le)
      refine (h.integrable_of_nonneg fun a => Real.rpow_nonneg (hY0 a) _).congr
        (Eventually.of_forall fun a => ?_)
      simp only [Real.rpow_natCast]
  -- the identification of the homogenized matrix
  have hid : S.homogenized = pk.abar :=
    homogenized_eq_of_basisBounds hd1 hΛ.le hP S hYm hY1 hYmom hCε hθ' hbasis' hθ hθ1 hosc'
  refine ⟨S, fun τ hτ hτd => ?_⟩
  have hp1 := one_lt_ratePower hτ hτd
  have hp0 : 0 < ratePower d τ := zero_lt_one.trans hp1
  -- the scale `max(Y, √d)^p`
  have hos : OsBound P (fun a => max (Y a) (Real.sqrt d) ^ ratePower d τ) τ
      (rateScaleConst d (B * (C₀ * (2 + Λ / 1) ^ C₀)) τ) := by
    have h1 := hYos (ratePower d τ) hp0 τ hτ (le_div_ratePower hτ hτd)
    have h2 : OsBound P (fun _ : CoefficientField d Λ => Real.sqrt d ^ ratePower d τ) τ
        (Real.sqrt d ^ ratePower d τ / Real.log 2 ^ τ⁻¹) :=
      osBound_of_le_const measurable_const hτ (Real.rpow_pos_of_pos (Real.sqrt_pos.mpr hdpos) _)
        (Eventually.of_forall fun _ => le_rfl)
    exact (osBound_max h1 h2).of_le ((hYm.max measurable_const).pow_const _) fun a =>
      le_of_eq (max_rpow_eq (hY0 a) (Real.sqrt_nonneg _) hp0.le)
  rw [← hid] at hbasis'
  exact gaussianCorrectorRate_of_basisBounds hP S hYm hY1 hτ hτd hCε hθ' hos hbasis'

end QSH
