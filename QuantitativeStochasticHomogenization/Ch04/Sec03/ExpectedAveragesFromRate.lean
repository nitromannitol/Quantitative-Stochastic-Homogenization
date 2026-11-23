import QuantitativeStochasticHomogenization.Ch04.Sec03.ExpectedDensities
import QuantitativeStochasticHomogenization.Ch04.Sec01.EuclideanLipschitz
import QuantitativeStochasticHomogenization.Ch04.Sec03.EstimateWitnesses

/-!
# The expectations (1) from Proposition 3.21 and stationarity

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, the expectations (1) of the route of Proposition 4.10 (in the book, Lemma 3.23 and
(3.92)–(3.93)).

`expectedAveragesEstimate_of_energy_and_rate`: for a law satisfying the assumptions (0.10)–(0.11),
the energy bound below the scale (`GaussianEnergyBound`) and Proposition 3.21 at one exponent with
a positive rate (`GaussianCorrectorRate`) give `ExpectedAveragesEstimate P S β` for every `β > 0`.
The three densities `G ξ`, `a G ξ`, `G ξ · a G ξ` are stationary; their Gaussian averages are
dominated by `|ξ|(1 + C(1 + X^d))/2`, `Λ|ξ|(1 + C(1 + X^d))/2`, `C(1 + X^d)|ξ|²` (from
`|v| ≤ (t + t⁻¹ v·av)/2` at `t = |ξ|`), and by Proposition 3.21 their averages at the origin
converge almost surely to `ξ`, `āξ`, `ξ·āξ`. The expectation of each average is therefore within
the periodization error of these limits, and the periodization error is `O(r^{-β})` for every `β`.

`expectedAveragesEstimate_of_rate`: the same from Proposition 3.21 alone, the energy bound being
supplied by `gaussianEnergyBound_of_rate`.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

open BaseExponent

variable {d : ℕ} {Λ : ℝ}

/-! ## Envelopes -/

theorem eq_zero_of_euclideanNorm_eq_zero {ξ : Vec d} (h : euclideanNorm ξ = 0) : ξ = 0 := by
  have h2 : euclideanSq ξ = 0 := by
    rw [← euclideanNorm_sq, h]; ring
  unfold euclideanSq dot at h2
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_self_nonneg (ξ j)).mp h2 i
    (Finset.mem_univ i)
  simpa using this

theorem euclideanNorm_le_half_add_inv_mul_energy (a : CoefficientField d Λ) {t : ℝ} (ht : 0 < t)
    (x v : Vec d) : euclideanNorm v ≤ (t + t⁻¹ * dot v ((a x).mulVec v)) / 2 := by
  set e := euclideanNorm v with hedef
  have h2 := (a.elliptic x v).1
  have h3 : e ^ 2 = euclideanSq v := euclideanNorm_sq v
  have h4 : 2 * t * e ≤ t ^ 2 + e ^ 2 := by nlinarith [sq_nonneg (t - e)]
  have h5 : e ≤ (t + t⁻¹ * e ^ 2) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have : t + t⁻¹ * e ^ 2 = (t ^ 2 + e ^ 2) / t := by field_simp
    rw [this, le_div_iff₀ ht]
    linarith
  have h6 : t⁻¹ * e ^ 2 ≤ t⁻¹ * dot v ((a x).mulVec v) :=
    mul_le_mul_of_nonneg_left (h3 ▸ h2) (inv_nonneg.mpr ht.le)
  linarith

theorem integral_heatKernel_mul_half_add (z : Vec d) {r : ℝ} (hr : 0 < r) (t : ℝ)
    {E : Vec d → ℝ} (hE : Integrable fun x => heatKernel z r x * E x) :
    Integrable (fun x => heatKernel z r x * ((t + t⁻¹ * E x) / 2)) ∧
      ∫ x, heatKernel z r x * ((t + t⁻¹ * E x) / 2) =
        (t + t⁻¹ * ∫ x, heatKernel z r x * E x) / 2 := by
  have hΦ := integrable_heatKernel z hr
  have he : (fun x => heatKernel z r x * ((t + t⁻¹ * E x) / 2)) =
      fun x => t / 2 * heatKernel z r x + t⁻¹ / 2 * (heatKernel z r x * E x) := by
    funext x; ring
  rw [he]
  refine ⟨(hΦ.const_mul _).add (hE.const_mul _), ?_⟩
  rw [integral_add (hΦ.const_mul _) (hE.const_mul _), integral_const_mul, integral_const_mul,
    integral_heatKernel z hr]
  ring

theorem correctedField_zero {P : Measure (CoefficientField d Λ)} (S : HomogenizationData P)
    (a : CoefficientField d Λ) (x : Vec d) : correctedField S a 0 x = 0 := by
  simp [correctedField]

section Envelopes

variable {P : Measure (CoefficientField d Λ)}

/-- **The envelopes of the gradient and flux averages**: if `∫ Φ_{z,r} Gξ·aGξ ≤ B |ξ|²`, then
`∫ Φ_{z,r} |Gξ| ≤ |ξ|(1 + B)/2` and `∫ Φ_{z,r} |aGξ| ≤ Λ|ξ|(1 + B)/2`. -/
theorem gradient_flux_envelope (hΛ : 0 ≤ Λ) (S : HomogenizationData P) (ξ : Vec d)
    (a : CoefficientField d Λ) (z : Vec d) {r : ℝ} (hr : 0 < r) {B : ℝ}
    (hEi : Integrable fun x => heatKernel z r x *
      dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x)))
    (hEb : ∫ x, heatKernel z r x *
      dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x)) ≤ B * euclideanSq ξ) :
    (Integrable (fun x => heatKernel z r x * ‖correctedField S a ξ x‖) ∧
      ∫ x, heatKernel z r x * ‖correctedField S a ξ x‖ ≤ euclideanNorm ξ / 2 * (1 + B)) ∧
    (Integrable (fun x => heatKernel z r x * ‖fluxDensity S ξ a x‖) ∧
      ∫ x, heatKernel z r x * ‖fluxDensity S ξ a x‖ ≤ Λ * (euclideanNorm ξ / 2 * (1 + B))) := by
  have hGm : AEStronglyMeasurable (fun x => correctedField S a ξ x) volume :=
    ((measurable_correctedField S ξ).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  obtain ⟨h1, h2⟩ := integrable_averages_of_energy a hΛ z hr hGm hEi
  have hΦ0 := heatKernel_nonneg z r
  have hI1 : Integrable (fun x => heatKernel z r x * ‖correctedField S a ξ x‖) :=
    h1.norm.congr (Eventually.of_forall fun x => by
      simp only [norm_smul, Real.norm_of_nonneg (hΦ0 x)])
  have hI2 : Integrable (fun x => heatKernel z r x * ‖fluxDensity S ξ a x‖) :=
    h2.norm.congr (by
      filter_upwards [ae_fluxDensity_eq S ξ a] with x hx
      rw [hx, norm_smul, Real.norm_of_nonneg (hΦ0 x)])
  rcases eq_or_lt_of_le (euclideanNorm_nonneg ξ) with h0 | hpos
  · have hξ := eq_zero_of_euclideanNorm_eq_zero h0.symm
    rw [← h0]
    subst hξ
    simp [correctedField_zero, fluxDensity]
  set t := euclideanNorm ξ with htdef
  obtain ⟨hJ, hJe⟩ := integral_heatKernel_mul_half_add z hr t hEi
  have hmain : (t + t⁻¹ * ∫ x, heatKernel z r x *
      dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) / 2 ≤ t / 2 * (1 + B) := by
    have h3 : t⁻¹ * (∫ x, heatKernel z r x *
        dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) ≤
        t⁻¹ * (B * euclideanSq ξ) := mul_le_mul_of_nonneg_left hEb (inv_nonneg.mpr hpos.le)
    have h4 : t⁻¹ * (B * euclideanSq ξ) = B * t := by
      rw [← euclideanNorm_sq, ← htdef]; field_simp
    have h5 : (t + B * t) / 2 = t / 2 * (1 + B) := by ring
    linarith
  refine ⟨⟨hI1, ?_⟩, ⟨hI2, ?_⟩⟩
  · have hpt : ∀ x, heatKernel z r x * ‖correctedField S a ξ x‖ ≤ heatKernel z r x *
        ((t + t⁻¹ * dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) / 2) :=
      fun x => mul_le_mul_of_nonneg_left ((norm_le_euclideanNorm _).trans
        (euclideanNorm_le_half_add_inv_mul_energy a hpos x _)) (hΦ0 x)
    exact (integral_mono hI1 hJ hpt).trans (hJe.le.trans hmain)
  · have hpt : ∀ᵐ x, heatKernel z r x * ‖fluxDensity S ξ a x‖ ≤ Λ * (heatKernel z r x *
        ((t + t⁻¹ * dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) / 2)) := by
      filter_upwards [ae_fluxDensity_eq S ξ a] with x hx
      rw [hx]
      have h6 := (norm_le_euclideanNorm _).trans (euclideanNorm_coefficient_mulVec_le a hΛ x
        (correctedField S a ξ x))
      have h7 := euclideanNorm_le_half_add_inv_mul_energy a hpos x (correctedField S a ξ x)
      calc heatKernel z r x * ‖(a x).mulVec (correctedField S a ξ x)‖
          ≤ heatKernel z r x * (Λ * ((t + t⁻¹ * dot (correctedField S a ξ x)
            ((a x).mulVec (correctedField S a ξ x))) / 2)) :=
            mul_le_mul_of_nonneg_left (h6.trans (mul_le_mul_of_nonneg_left h7 hΛ)) (hΦ0 x)
        _ = _ := by ring
    calc ∫ x, heatKernel z r x * ‖fluxDensity S ξ a x‖
        ≤ ∫ x, Λ * (heatKernel z r x *
          ((t + t⁻¹ * dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) / 2)) :=
          integral_mono_ae hI2 (hJ.const_mul Λ) hpt
      _ = Λ * ((t + t⁻¹ * ∫ x, heatKernel z r x *
          dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) / 2) := by
          rw [integral_const_mul, hJe]
      _ ≤ Λ * (t / 2 * (1 + B)) := mul_le_mul_of_nonneg_left hmain hΛ

/-- **The envelope of the energy averages**: `∫ Φ_{z,r} |Gξ·aGξ| = ∫ Φ_{z,r} Gξ·aGξ`. -/
theorem energy_envelope (S : HomogenizationData P) (ξ : Vec d) (a : CoefficientField d Λ)
    (z : Vec d) (r : ℝ)
    (hEi : Integrable fun x => heatKernel z r x *
      dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) :
    Integrable (fun x => heatKernel z r x * ‖energyDensity S ξ a x‖) ∧
      ∫ x, heatKernel z r x * ‖energyDensity S ξ a x‖ =
        ∫ x, heatKernel z r x *
          dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x)) := by
  have he : (fun x => heatKernel z r x * ‖energyDensity S ξ a x‖) =ᵐ[volume] fun x =>
      heatKernel z r x * dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x)) := by
    filter_upwards [ae_energyDensity_eq S ξ a] with x hx
    rw [hx, Real.norm_of_nonneg ((euclideanSq_nonneg _).trans (a.elliptic x _).1)]
  exact ⟨hEi.congr he.symm, integral_congr_ae he⟩

end Envelopes

/-! ## Almost sure limits from Proposition 3.21 -/

theorem tendsto_of_eventually_norm_sub_le {E : Type*} [SeminormedAddCommGroup E] {f : ℕ → E}
    {c : E} {b : ℕ → ℝ} (hb : Tendsto b atTop (𝓝 0)) (h : ∀ᶠ n in atTop, ‖f n - c‖ ≤ b n) :
    Tendsto f atTop (𝓝 c) :=
  tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) h hb)

theorem tendsto_const_mul_rpow_neg_nat (K : ℝ) {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun n : ℕ => K * ((n : ℝ) + 1) ^ (-μ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h2 := ((tendsto_rpow_neg_atTop hμ).comp h1).const_mul K
  simpa using h2

theorem eventually_le_natCast_add_one (X : ℝ) : ∀ᶠ n : ℕ in atTop, X ≤ (n : ℝ) + 1 :=
  eventually_atTop.mpr ⟨⌈X⌉₊, fun n hn => by
    have h1 := Nat.le_ceil X
    have h2 : (⌈X⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
    linarith⟩

/-- **Almost sure limits of the averages at the origin**, from Proposition 3.21 with a positive
rate. -/
theorem ae_tendsto_averages_of_rate {P : Measure (CoefficientField d Λ)} (S : HomogenizationData P)
    {τ C μ : ℝ} (hμ : 0 < μ) (hrate : GaussianCorrectorRate P S τ C μ) (ξ : Vec d) :
    ∀ᵐ a ∂P,
      Tendsto (fun n : ℕ => ∫ x, heatKernel 0 ((n : ℝ) + 1) x • correctedField S a ξ x) atTop
        (𝓝 ξ) ∧
      Tendsto (fun n : ℕ => ∫ x, heatKernel 0 ((n : ℝ) + 1) x • fluxDensity S ξ a x) atTop
        (𝓝 (S.homogenized.mulVec ξ)) ∧
      Tendsto (fun n : ℕ => ∫ x, heatKernel 0 ((n : ℝ) + 1) x • energyDensity S ξ a x) atTop
        (𝓝 (dot ξ (S.homogenized.mulVec ξ))) := by
  obtain ⟨X, -, hX⟩ := hrate
  filter_upwards [(hX 0).2] with a ha
  have hev : ∀ᶠ n : ℕ in atTop, GaussianAverageBounds a S.homogenized (correctedField S a) 0
      ((n : ℝ) + 1) (C * ((n : ℝ) + 1) ^ (-μ)) := by
    filter_upwards [eventually_le_natCast_add_one (X a 0)] with n hn
    exact ha _ (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) hn
  refine ⟨?_, ?_, ?_⟩
  · refine tendsto_of_eventually_norm_sub_le (tendsto_const_mul_rpow_neg_nat
      (C * euclideanNorm ξ) hμ) ?_
    filter_upwards [hev] with n hn
    exact (norm_le_euclideanNorm _).trans ((hn ξ).2.2.2.1.trans (le_of_eq (by ring)))
  · refine tendsto_of_eventually_norm_sub_le (tendsto_const_mul_rpow_neg_nat
      (C * euclideanNorm ξ) hμ) ?_
    filter_upwards [hev] with n hn
    rw [integral_heatKernel_smul_fluxDensity]
    exact (norm_le_euclideanNorm _).trans ((hn ξ).2.2.2.2.1.trans (le_of_eq (by ring)))
  · refine tendsto_of_eventually_norm_sub_le (tendsto_const_mul_rpow_neg_nat
      (2 * C * euclideanNorm ξ ^ 2) hμ) ?_
    filter_upwards [hev] with n hn
    rw [integral_heatKernel_smul_energyDensity, Real.norm_eq_abs]
    exact (hn ξ).2.2.2.2.2.trans (le_of_eq (by ring))

/-! ## The expectations (1) -/

/-- **The expectations (1) of the Gaussian averages with an explicit constant**, from scales `X`
of the energy bound below the scale, Proposition 3.21 at one exponent with a positive rate and a
bound `C_β r^{-β}` of the periodization error: the constant is
`(d + 1) C_β c⁻¹ (Λ + 1) (1 + C_N (1 + E[X(0)^d]))` with `c = cellHeatLower d`. -/
theorem expectedAveragesEstimateAt_of_scales {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (S : HomogenizationData P) (hΛ : 0 ≤ Λ) {τ CN : ℝ}
    (X : CoefficientField d Λ → Vec d → ℝ) (hX1 : ∀ a z, 1 ≤ X a z)
    (hXos : ∀ z, OsBound P (fun a => X a z) τ CN)
    (hXb : ∀ z : Vec d, ∀ᵐ a ∂P, ∀ r : ℝ, 1 ≤ r → ∀ ξ : Vec d,
      Integrable (fun x => heatKernel z r x *
        dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) ∧
      (∫ x, heatKernel z r x * dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) ≤
        CN * (1 + (X a z / r) ^ d) * euclideanSq ξ)
    {τ' C μ : ℝ} (hμ : 0 < μ) (hrate : GaussianCorrectorRate P S τ' C μ) {β Cβ : ℝ}
    (hCβ : 0 < Cβ) (hCβb : ∀ r : ℝ, 1 ≤ r → (1 + thetaError (r ^ 2)) ^ d - 1 ≤ Cβ * r ^ (-β)) :
    ExpectedAveragesEstimateAt P S β (((d : ℝ) + 1) * Cβ * (cellHeatLower d)⁻¹ * (Λ + 1) *
      (1 + CN * (1 + ∫ a, X a 0 ^ d ∂P))) := by
  have : IsProbabilityMeasure P := hP.1
  have hinv := hP.2.1
  have hCN : 0 < CN := (hXos 0).scale_pos
  have hX0 : ∀ a z, 0 ≤ X a z := fun a z => zero_le_one.trans (hX1 a z)
  have hXd : ∀ z, Integrable (fun a => X a z ^ d) P := by
    intro z
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      simp only [pow_zero]
      exact integrable_const 1
    · have h := ((hXos z).rpow (fun a => hX0 a z) (Nat.cast_pos.mpr hd :
        (0 : ℝ) < d)).integrable_of_nonneg (fun a => Real.rpow_nonneg (hX0 a z) _)
      simpa only [Real.rpow_natCast] using h
  have hE0 : 0 ≤ ∫ a, X a 0 ^ d ∂P := integral_nonneg fun a => pow_nonneg (hX0 a 0) d
  have hM : 0 < 1 + CN * (1 + ∫ a, X a 0 ^ d ∂P) := by positivity
  have hc0 : 0 < (cellHeatLower d)⁻¹ := inv_pos.mpr (cellHeatLower_pos d)
  intro z r hr ξ
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hBint : ∀ z, Integrable (fun a => CN * (1 + X a z ^ d)) P := fun z =>
    ((integrable_const 1).add (hXd z)).const_mul CN
  have hIB : ∫ a, CN * (1 + X a 0 ^ d) ∂P = CN * (1 + ∫ a, X a 0 ^ d ∂P) := by
    rw [integral_const_mul, integral_add (integrable_const _) (hXd 0)]
    simp
  have hEB : ∀ z, ∀ᵐ a ∂P, ∀ r : ℝ, 1 ≤ r →
      (Integrable fun x => heatKernel z r x *
        dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) ∧
      ∫ x, heatKernel z r x * dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))
        ≤ CN * (1 + X a z ^ d) * euclideanSq ξ := by
    intro z
    filter_upwards [hXb z] with a ha r hr
    obtain ⟨h1, h2⟩ := ha r hr ξ
    refine ⟨h1, h2.trans ?_⟩
    have hXr : (X a z / r) ^ d ≤ X a z ^ d :=
      pow_le_pow_left₀ (div_nonneg (hX0 a z) (zero_le_one.trans hr))
        (div_le_self (hX0 a z) hr) d
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hCN.le)
      (euclideanSq_nonneg ξ)
  have hlim := ae_tendsto_averages_of_rate S hμ hrate ξ
  have hn := euclideanNorm_nonneg ξ
  have hρ : 0 < r ^ (-β) := Real.rpow_pos_of_pos hr0 _
  have hε0 := periodizationError_nonneg (d := d) hr0
  have hε := hCβb r hr
  -- the gradient
  obtain ⟨hIG, hbG⟩ := norm_expectation_average_sub_le hinv
    (H := fun a x => correctedField S a ξ x) (measurable_correctedField S ξ).stronglyMeasurable
    (ae_correctedField_add_latticeShift S ξ)
    (fun z a => euclideanNorm ξ / 2 * (1 + CN * (1 + X a z ^ d)))
    (fun z => ((integrable_const 1).add (hBint z)).const_mul _)
    (fun z => by
      filter_upwards [hEB z] with a ha r hr
      obtain ⟨h1, h2⟩ := ha r hr
      exact (gradient_flux_envelope hΛ S ξ a z (zero_lt_one.trans_le hr) h1 h2).1)
    (by filter_upwards [hlim] with a ha; exact ha.1) z hr
  -- the flux
  obtain ⟨hIF, hbF⟩ := norm_expectation_average_sub_le hinv
    (H := fluxDensity S ξ) (measurable_fluxDensity S ξ).stronglyMeasurable
    (ae_fluxDensity_add_latticeShift S ξ)
    (fun z a => Λ * (euclideanNorm ξ / 2 * (1 + CN * (1 + X a z ^ d))))
    (fun z => (((integrable_const 1).add (hBint z)).const_mul _).const_mul _)
    (fun z => by
      filter_upwards [hEB z] with a ha r hr
      obtain ⟨h1, h2⟩ := ha r hr
      exact (gradient_flux_envelope hΛ S ξ a z (zero_lt_one.trans_le hr) h1 h2).2)
    (by filter_upwards [hlim] with a ha; exact ha.2.1) z hr
  -- the energy
  obtain ⟨hIW, hbW⟩ := norm_expectation_average_sub_le hinv
    (H := energyDensity S ξ) (measurable_energyDensity S ξ).stronglyMeasurable
    (ae_energyDensity_add_latticeShift S ξ)
    (fun z a => CN * (1 + X a z ^ d) * euclideanSq ξ)
    (fun z => (hBint z).mul_const _)
    (fun z => by
      filter_upwards [hEB z] with a ha r hr
      obtain ⟨h1, h2⟩ := ha r hr
      obtain ⟨h3, h4⟩ := energy_envelope S ξ a z r h1
      exact ⟨h3, h4.le.trans h2⟩)
    (by filter_upwards [hlim] with a ha; exact ha.2.2) z hr
  have hfF : (fun a => ∫ x, heatKernel z r x • fluxDensity S ξ a x) =
      fun a => ∫ x, heatKernel z r x • (a x).mulVec (correctedField S a ξ x) :=
    funext fun a => integral_heatKernel_smul_fluxDensity S ξ a z r
  have hfW : (fun a => ∫ x, heatKernel z r x • energyDensity S ξ a x) =
      fun a => ∫ x, heatKernel z r x *
        dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x)) :=
    funext fun a => integral_heatKernel_smul_energyDensity S ξ a z r
  rw [hfF] at hIF hbF
  rw [hfW] at hIW hbW
  have hYG : ∫ a, euclideanNorm ξ / 2 * (1 + CN * (1 + X a 0 ^ d)) ∂P =
      euclideanNorm ξ / 2 * (1 + CN * (1 + ∫ a, X a 0 ^ d ∂P)) := by
    rw [integral_const_mul, integral_add (integrable_const _) (hBint 0), hIB]
    simp
  have hYF : ∫ a, Λ * (euclideanNorm ξ / 2 * (1 + CN * (1 + X a 0 ^ d))) ∂P =
      Λ * (euclideanNorm ξ / 2 * (1 + CN * (1 + ∫ a, X a 0 ^ d ∂P))) := by
    rw [integral_const_mul, hYG]
  have hYW : ∫ a, CN * (1 + X a 0 ^ d) * euclideanSq ξ ∂P =
      CN * (1 + ∫ a, X a 0 ^ d ∂P) * euclideanSq ξ := by
    rw [integral_mul_const, hIB]
  rw [hYG] at hbG
  rw [hYF] at hbF
  rw [hYW] at hbW
  set M := 1 + CN * (1 + ∫ a, X a 0 ^ d ∂P) with hMdef
  set ε := (1 + thetaError (r ^ 2)) ^ d - 1 with hεdef
  set c0 := (cellHeatLower d)⁻¹ with hc0def
  set ρ := r ^ (-β) with hρdef
  have hd1 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hεc : ε * c0 ≤ Cβ * ρ * c0 := mul_le_mul_of_nonneg_right hε hc0.le
  refine ⟨hIG, hIF, hIW, ?_, ?_, ?_⟩
  · calc euclideanNorm ((∫ a, (∫ x, heatKernel z r x • correctedField S a ξ x) ∂P) - ξ)
        ≤ ((d : ℝ) + 1) * ‖(∫ a, (∫ x, heatKernel z r x • correctedField S a ξ x) ∂P) - ξ‖ :=
          euclideanNorm_le_dimension_mul_norm _
      _ ≤ ((d : ℝ) + 1) * (ε * (c0 * (euclideanNorm ξ / 2 * M))) :=
          mul_le_mul_of_nonneg_left hbG (by positivity)
      _ = ((d : ℝ) + 1) * (ε * c0) * M * euclideanNorm ξ * (1 / 2) := by ring
      _ ≤ ((d : ℝ) + 1) * (Cβ * ρ * c0) * M * euclideanNorm ξ * (Λ + 1) := by
          gcongr
          linarith
      _ = ((d : ℝ) + 1) * Cβ * c0 * (Λ + 1) * M * euclideanNorm ξ * ρ := by ring
  · calc euclideanNorm ((∫ a, (∫ x, heatKernel z r x • (a x).mulVec (correctedField S a ξ x)) ∂P) -
          S.homogenized.mulVec ξ)
        ≤ ((d : ℝ) + 1) * ‖(∫ a, (∫ x, heatKernel z r x • (a x).mulVec
          (correctedField S a ξ x)) ∂P) - S.homogenized.mulVec ξ‖ :=
          euclideanNorm_le_dimension_mul_norm _
      _ ≤ ((d : ℝ) + 1) * (ε * (c0 * (Λ * (euclideanNorm ξ / 2 * M)))) :=
          mul_le_mul_of_nonneg_left hbF (by positivity)
      _ = ((d : ℝ) + 1) * (ε * c0) * M * euclideanNorm ξ * (Λ / 2) := by ring
      _ ≤ ((d : ℝ) + 1) * (Cβ * ρ * c0) * M * euclideanNorm ξ * (Λ + 1) := by
          gcongr
          linarith
      _ = ((d : ℝ) + 1) * Cβ * c0 * (Λ + 1) * M * euclideanNorm ξ * ρ := by ring
  · have hsq := euclideanSq_nonneg ξ
    have hCNM : CN * (1 + ∫ a, X a 0 ^ d ∂P) ≤ M := by rw [hMdef]; linarith
    rw [← Real.norm_eq_abs]
    calc ‖(∫ a, (∫ x, heatKernel z r x *
            dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) ∂P) -
          dot ξ (S.homogenized.mulVec ξ)‖
        ≤ ε * (c0 * (CN * (1 + ∫ a, X a 0 ^ d ∂P) * euclideanSq ξ)) := hbW
      _ = (ε * c0) * (CN * (1 + ∫ a, X a 0 ^ d ∂P)) * euclideanSq ξ * 1 := by ring
      _ ≤ (Cβ * ρ * c0) * M * euclideanSq ξ * (((d : ℝ) + 1) * (Λ + 1)) := by
          gcongr
          nlinarith
      _ = ((d : ℝ) + 1) * Cβ * c0 * (Λ + 1) * M * euclideanSq ξ * ρ := by ring

/-- **The expectations (1) of the Gaussian averages** for every `β > 0`, from the energy bound
below the scale and Proposition 3.21 at one exponent with a positive rate, for a law satisfying
(0.10)–(0.11). -/
theorem expectedAveragesEstimate_of_energy_and_rate {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (S : HomogenizationData P) (hΛ : 0 ≤ Λ) {τ CN : ℝ}
    (hN : GaussianEnergyBound P S τ CN) {τ' C μ : ℝ} (hμ : 0 < μ)
    (hrate : GaussianCorrectorRate P S τ' C μ) {β : ℝ} (hβ : 0 < β) :
    ExpectedAveragesEstimate P S β := by
  have : IsProbabilityMeasure P := hP.1
  obtain ⟨X, -, hX1, hXos, hXb⟩ := hN
  obtain ⟨Cβ, hCβ, hCβb⟩ := periodizationError_le_rpow (d := d) hβ
  have hCN : 0 < CN := (hXos 0).scale_pos
  have hE0 : 0 ≤ ∫ a, X a 0 ^ d ∂P :=
    integral_nonneg fun a => pow_nonneg (zero_le_one.trans (hX1 a 0)) d
  have hc0 : 0 < (cellHeatLower d)⁻¹ := inv_pos.mpr (cellHeatLower_pos d)
  exact ⟨_, by positivity,
    expectedAveragesEstimateAt_of_scales hP S hΛ X hX1 hXos hXb hμ hrate hCβ hCβb⟩

/-- **The expectations (1) with a constant chosen before the law**: for `d ≥ 1`, the energy bound
below the scale at the exponent `τ` with constant `C_N`, Proposition 3.21 at one exponent with a
positive rate and a bound `C_β r^{-β}` of the periodization error give the expectations (1) with
the constant `(d + 1) C_β c⁻¹ (Λ + 1) (1 + C_N (1 + K C_N^d))`, `K = momentConstant (τ/d)`,
which depends only on `d, Λ, τ, C_N, C_β`. -/
theorem expectedAveragesEstimateAt_of_energy_and_rate {P : Measure (CoefficientField d Λ)}
    (hd : 0 < d) (hP : LawHypotheses P) (S : HomogenizationData P) (hΛ : 0 ≤ Λ) {τ CN : ℝ}
    (hN : GaussianEnergyBound P S τ CN) {τ' C μ : ℝ} (hμ : 0 < μ)
    (hrate : GaussianCorrectorRate P S τ' C μ) {β Cβ : ℝ} (hCβ : 0 < Cβ)
    (hCβb : ∀ r : ℝ, 1 ≤ r → (1 + thetaError (r ^ 2)) ^ d - 1 ≤ Cβ * r ^ (-β)) :
    ExpectedAveragesEstimateAt P S β (((d : ℝ) + 1) * Cβ * (cellHeatLower d)⁻¹ * (Λ + 1) *
      (1 + CN * (1 + momentConstant (τ / d) * CN ^ (d : ℝ)))) := by
  have : IsProbabilityMeasure P := hP.1
  obtain ⟨X, -, hX1, hXos, hXb⟩ := hN
  have hCN : 0 < CN := (hXos 0).scale_pos
  have hX0 : ∀ a, 0 ≤ X a 0 := fun a => zero_le_one.trans (hX1 a 0)
  have hdr : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  obtain ⟨-, hm⟩ := ((hXos 0).rpow hX0 hdr).integral_le_factorial_mul fun a =>
    Real.rpow_nonneg (hX0 a) _
  have hEX : ∫ a, X a 0 ^ d ∂P ≤ momentConstant (τ / d) * CN ^ (d : ℝ) := by
    simpa only [Real.rpow_natCast, momentConstant] using hm
  have hc0 : 0 < (cellHeatLower d)⁻¹ := inv_pos.mpr (cellHeatLower_pos d)
  refine (expectedAveragesEstimateAt_of_scales hP S hΛ X hX1 hXos hXb hμ hrate hCβ hCβb).mono_const
    ?_
  have hK : 0 ≤ ((d : ℝ) + 1) * Cβ * (cellHeatLower d)⁻¹ * (Λ + 1) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hK
  have := mul_le_mul_of_nonneg_left (add_le_add_left hEX 1) hCN.le
  linarith

/-- **The expectations (1) from Proposition 3.21 alone**: for a law satisfying (0.10)–(0.11),
Proposition 3.21 at one exponent with a positive rate gives `ExpectedAveragesEstimate P S β` for
every `β > 0`. -/
theorem expectedAveragesEstimate_of_rate {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (S : HomogenizationData P) (hΛ : 0 ≤ Λ) {τ C μ : ℝ} (hτ : 0 < τ)
    (hμ : 0 < μ) (hrate : GaussianCorrectorRate P S τ C μ) {β : ℝ} (hβ : 0 < β) :
    ExpectedAveragesEstimate P S β := by
  have : IsProbabilityMeasure P := hP.1
  obtain ⟨K, hK⟩ := exists_dot_mulVec_le S.homogenized
  obtain ⟨CN, -, hN⟩ := gaussianEnergyBound_of_rate S hK hτ hμ.le hrate
  exact expectedAveragesEstimate_of_energy_and_rate hP S hΛ hN hμ hrate hβ

end QSH
