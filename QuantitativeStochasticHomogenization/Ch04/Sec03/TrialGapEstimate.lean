import QuantitativeStochasticHomogenization.Ch04.Sec03.TrialGapCore

/-!
# The trial gap estimate under `Fluc(s, α)`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, Proposition 4.10: Step 2 of the route used here.

`trialGapEstimate_of_linearAverages`: under `Fluc(s, α)`, the linear estimate of Step 1
(`LinearAverageEstimate`), the expectation of the trial at deterministic slopes
(`TrialObjectiveExpectation` at the rate `2α`), the energy bound below the scale
(`GaussianEnergyBound`), Proposition 3.21 at an exponent `τ > s d/2`, the structure (4.12) of `A₁`
and the measurability of `J₁` and of the trial, the gap to the trial at the homogenized slope is
`O_{s/2}(C r^{-2α})` at every center (`TrialGapEstimate P S (s/2) (2α)`).

The proof compares the expectations of the gaps at the deterministic slopes `m₀ = E[m]` and `c*`,
where `m` is the polarization vector: `E[J₁] ≥ E[L(c*)] ≥ J_hom - C r^{-2α}`, while
`E[J₁] = E[L(m₀)] + E[gap(m₀)] ≤ J_hom - ½|m₀ - c*|² + C r^{-2α}`, so `|m₀ - c*|² ≤ C r^{-2α}`.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

theorem euclideanNorm_sub_comm_sq (u v : Vec d) :
    euclideanNorm (u - v) ^ 2 = euclideanSq (v - u) := by
  rw [euclideanNorm_sq, ← neg_sub, show euclideanSq (-(v - u)) = euclideanSq (v - u) by
    simp only [euclideanSq, dot, Pi.neg_apply, neg_mul_neg]]

section Estimate

variable {P : Measure (CoefficientField d Λ)}

/-- **The expectation step**: from the pointwise bounds of the gaps and the expectations of the
trials at `m₀` and `c*`, `|m₀ - c*|² ≤ 2 (e₁ + e₂ + e₃)`. -/
theorem sq_dist_le_of_expectations {EJ ELm ELc Eg Jh hm hc e₁ e₂ e₃ δ : ℝ}
    (h1 : ELc ≤ EJ) (h2 : hc - e₁ ≤ ELc) (h3 : hc = Jh) (h4 : EJ = ELm + Eg)
    (h5 : ELm ≤ hm + e₂) (h6 : hm ≤ Jh - 1 / 2 * δ) (h7 : Eg ≤ e₃) : δ ≤ 2 * (e₁ + e₂ + e₃) := by
  linarith

theorem abs_polarizationVector_le (a : CoefficientField d Λ) (hΛ : 0 ≤ Λ) (y : Vec d) {r : ℝ}
    (hr : 0 < r) {p q : Vec d} (hp : euclideanNorm p < 1) (hq : euclideanNorm q < 1) (i : Fin d) :
    |polarizationVector a y r p q i| ≤ 8 * (Λ + 1) := by
  have hb : ∀ p' q' : Vec d, euclideanNorm p' ≤ 1 → euclideanNorm q' ≤ 1 →
      0 ≤ J1Heat a y r p' q' ∧ J1Heat a y r p' q' ≤ Λ + 1 := by
    intro p' q' hp' hq'
    obtain ⟨h0, h1⟩ := J1Heat_nonneg_le a y hr p' q'
    have hp2 : euclideanSq p' ≤ 1 := by
      rw [← euclideanNorm_sq]; nlinarith [euclideanNorm_nonneg p']
    have hq2 : euclideanSq q' ≤ 1 := by
      rw [← euclideanNorm_sq]; nlinarith [euclideanNorm_nonneg q']
    exact ⟨h0, by nlinarith [euclideanSq_nonneg p']⟩
  have hhalf : ∀ v : Vec d, euclideanNorm v ≤ 2 → euclideanNorm ((1 / 2 : ℝ) • v) ≤ 1 := by
    intro v hv
    rw [euclideanNorm_smul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have hqe : euclideanNorm (q + unitVector i) ≤ 2 :=
    (euclideanNorm_add_le q (unitVector i)).trans (by rw [euclideanNorm_unitVector]; linarith)
  have he : euclideanNorm (unitVector i : Vec d) ≤ 2 := by rw [euclideanNorm_unitVector]; norm_num
  have h00 : euclideanNorm (0 : Vec d) ≤ 1 := by simp [euclideanNorm, euclideanSq, dot]
  obtain ⟨h1a, h1b⟩ := hb ((1 / 2 : ℝ) • p) ((1 / 2 : ℝ) • (q + unitVector i))
    (hhalf p (by linarith)) (hhalf _ hqe)
  obtain ⟨h2a, h2b⟩ := hb ((1 / 2 : ℝ) • p) ((1 / 2 : ℝ) • q) (hhalf p (by linarith))
    (hhalf q (by linarith))
  obtain ⟨h3a, h3b⟩ := hb 0 ((1 / 2 : ℝ) • unitVector i) h00 (hhalf _ he)
  simp only [polarizationVector]
  rw [abs_le]
  constructor <;> nlinarith

theorem euclideanSq_le_of_abs_le {v : Vec d} {c : ℝ} (h : ∀ i, |v i| ≤ c) :
    euclideanSq v ≤ d * c ^ 2 := by
  simp only [euclideanSq, dot]
  calc ∑ i, v i * v i ≤ ∑ _i : Fin d, c ^ 2 := Finset.sum_le_sum fun i _ => by
        have := h i
        have h0 := abs_nonneg (v i)
        nlinarith [abs_mul_abs_self (v i)]
    _ = d * c ^ 2 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem sq_scale_le {C4 nk r α ρ B Q1 : ℝ} (hC4 : 0 < C4) (hnk0 : 0 ≤ nk)
    (hnk : nk ≤ Real.sqrt B) (hQ1 : Q1 = C4 * (1 + Real.sqrt B))
    (hsq : (r ^ (-α)) ^ 2 = ρ) : (C4 * (1 + nk) * r ^ (-α)) ^ 2 ≤ Q1 ^ 2 * ρ := by
  have h1 : C4 * (1 + nk) ≤ Q1 := by rw [hQ1]; exact mul_le_mul_of_nonneg_left (by linarith) hC4.le
  have h2 : 0 ≤ C4 * (1 + nk) := mul_nonneg hC4.le (by linarith)
  rw [mul_pow, hsq]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h2 h1 2) (hsq ▸ sq_nonneg _)

/-- **The expectation step** for random variables: if `L(c*) ≤ J` almost surely,
`J = L(m₀) + g` with `g ≤ U` almost surely, and the expectations of `L(c*)`, `L(m₀)` and `U` are
controlled, then `δ ≤ 2 (e₁ + e₂ + e₃)`. -/
theorem le_of_expectations {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {J L₀ Lc g U : Ω → ℝ} {Jh hm hc e₁ e₂ e₃ δ : ℝ} (hJ : Integrable J P) (hL₀ : Integrable L₀ P)
    (hLc : Integrable Lc P) (hU : Integrable U P) (hJL : ∀ ω, J ω = L₀ ω + g ω)
    (hcJ : ∀ᵐ ω ∂P, Lc ω ≤ J ω) (hgU : ∀ᵐ ω ∂P, g ω ≤ U ω) (hUe : ∫ ω, U ω ∂P ≤ e₃)
    (hL₀e : ∫ ω, L₀ ω ∂P ≤ hm + e₂) (hLce : hc - e₁ ≤ ∫ ω, Lc ω ∂P) (hhc : hc = Jh)
    (hhm : hm ≤ Jh - 1 / 2 * δ) : δ ≤ 2 * (e₁ + e₂ + e₃) := by
  have hg : Integrable g P := by
    have : g = fun ω => J ω - L₀ ω := funext fun ω => by rw [hJL]; ring
    rw [this]; exact hJ.sub hL₀
  have h1 : ∫ ω, Lc ω ∂P ≤ ∫ ω, J ω ∂P := integral_mono_ae hLc hJ hcJ
  have h2 : ∫ ω, J ω ∂P = (∫ ω, L₀ ω ∂P) + ∫ ω, g ω ∂P := by
    rw [← integral_add hL₀ hg]; exact integral_congr_ae (Filter.Eventually.of_forall hJL)
  have h3 : ∫ ω, g ω ∂P ≤ ∫ ω, U ω ∂P := integral_mono_ae hg hU hgU
  linarith

/-- **The final sum of stochastic bounds**: a variable almost surely below
`3κ ((A₁ + A₂) + A₃) + K A₄`, with `A₁ ≤ O_t(a₁ ρ)`, `A₃ ≤ O_t(a₃ ρ)`, `A₄ ≤ O_t(a₄ ρ)` and a
constant `0 ≤ A₂ ≤ a₂ ρ`, is `O_t(c (3κ (c (c (a₁ + a₂/L) + a₃)) + K a₄) ρ)` with
`c = 2·2^{1/t}` and `L = (log 2)^{1/t}`. -/
theorem osBound_of_four {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X A₁ A₃ A₄ : Ω → ℝ} {A₂ t κ K a₁ a₂ a₃ a₄ ρ : ℝ} (hκ : 0 < κ) (hK : 0 < K)
    (hX : Measurable X) (h1 : OsBound P A₁ t (a₁ * ρ)) (h2 : A₂ ≤ a₂ * ρ) (ha₂ : 0 < a₂ * ρ)
    (h3 : OsBound P A₃ t (a₃ * ρ)) (h4 : OsBound P A₄ t (a₄ * ρ))
    (hle : ∀ᵐ ω ∂P, X ω ≤ 3 * κ * ((A₁ ω + A₂) + A₃ ω) + K * A₄ ω) :
    OsBound P X t ((2 * (2 : ℝ) ^ t⁻¹) * (3 * κ * ((2 * (2 : ℝ) ^ t⁻¹) *
      ((2 * (2 : ℝ) ^ t⁻¹) * (a₁ + a₂ / Real.log 2 ^ t⁻¹) + a₃)) + K * a₄) * ρ) := by
  have ht := h1.exponent_pos
  have hL : 0 < Real.log 2 ^ t⁻¹ := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _
  have hc2 : OsBound P (fun _ => A₂) t (a₂ * ρ / Real.log 2 ^ t⁻¹) :=
    osBound_of_le_const measurable_const ht ha₂ (Filter.Eventually.of_forall fun _ => h2)
  have h12 := osBound_add_le_sum h1 hc2
  have h123 := osBound_add_le_sum h12 h3
  have h123' := h123.const_mul (by positivity : (0 : ℝ) < 3 * κ)
  have h4' := h4.const_mul hK
  have hall := osBound_add_le_sum h123' h4'
  refine (hall.of_le_ae hX hle).mono_scale (le_of_eq ?_)
  field_simp

/-- The functional of (4.8) at the corrected field of slope `k`, at the mask `Φ_{y,r}`. -/
def trialValue {P : Measure (CoefficientField d Λ)} (S : HomogenizationData P)
    (a : CoefficientField d Λ) (y : Vec d) (r : ℝ) (p q k : Vec d) : ℝ :=
  j1Functional a (heatKernel y r) p q (correctedField S a k)

/-- The `Φ_{y,r}`-average of the corrected field of slope `k`. -/
def gradientAverage {P : Measure (CoefficientField d Λ)} (S : HomogenizationData P)
    (a : CoefficientField d Λ) (y : Vec d) (r : ℝ) (k : Vec d) : Vec d :=
  ∫ x, heatKernel y r x • correctedField S a k x

set_option maxHeartbeats 400000 in
/-- **The trial gap estimate at one center**, from the bounds on the pieces: the expectation step
gives `|m₀ - c*|² ≤ G₂ ρ` and the pointwise bound then gives the stochastic bound. -/
theorem trialGap_osBound_at [IsProbabilityMeasure P] (S : HomogenizationData P)
    (hA : HomogenizedMatrixBounds S.homogenized Λ)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J1Heat w.1 w.2 r p q)
    {s r ρ κ K B Ks Q1 Apol Epol E4 O4 CE G₁ G₂ L₂ ct Cf α : ℝ} {y p q m₀ cst : Vec d}
    {M : CoefficientField d Λ → Vec d → ℝ} (hr0 : 0 < r)
    (hρ : ρ = r ^ (-(2 * α))) (hρ0 : 0 < ρ) (hκ' : 0 < κ) (hK' : 0 < K)
    (hcst : cst = homogenizedSlope S.homogenized p q) (hc4 : euclideanSq cst ≤ 4)
    (hm₀B : euclideanSq m₀ ≤ B) (hcB : euclideanSq cst ≤ B)
    (hA1 : ∀ k : Vec d, euclideanSq k ≤ B →
      OsBound P (fun a => euclideanNorm (gradientAverage S a y r k - k) ^ 2) (s / 2) (Q1 ^ 2 * ρ) ∧
      Integrable (fun a => euclideanNorm (gradientAverage S a y r k - k) ^ 2) P ∧
      ∫ a, euclideanNorm (gradientAverage S a y r k - k) ^ 2 ∂P ≤ Ks * Q1 ^ 2 * ρ)
    (hA4 : OsBound P (fun a => (M a y / r) ^ d) (s / 2) (O4 * ρ))
    (hA4i : Integrable (fun a => (M a y / r) ^ d) P)
    (hA4E : ∫ a, (M a y / r) ^ d ∂P ≤ E4 * ρ)
    (hpos : OsBound P (fun a => euclideanSq (polarizationVector a y r p q - m₀)) (s / 2) (Apol * ρ))
    (hpi : Integrable (fun a => euclideanSq (polarizationVector a y r p q - m₀)) P)
    (hpint : ∫ a, euclideanSq (polarizationVector a y r p q - m₀) ∂P ≤ Epol * ρ)
    (hcomm : ∀ a : CoefficientField d Λ, euclideanNorm (m₀ - polarizationVector a y r p q) ^ 2 =
      euclideanSq (polarizationVector a y r p q - m₀))
    (hpt' : ∀ᵐ a ∂P, ∀ k : Vec d, euclideanSq k ≤ B →
        J1Heat a y r p q - trialValue S a y r p q k ≤
          κ * euclideanNorm (gradientAverage S a y r k - polarizationVector a y r p q) ^ 2 +
            K * (M a y / r) ^ d)
    (hE' : ∀ k : Vec d,
      Integrable (fun a => j1Functional a (heatKernel y r) p q (correctedField S a k)) P ∧
      |(∫ a, j1Functional a (heatKernel y r) p q (correctedField S a k) ∂P) -
          homogenizedJ1Objective S.homogenized p q k| ≤ CE * (1 + euclideanSq k) * r ^ (-(2 * α)))
    (hG₁ : G₁ = κ * (2 * (Ks * Q1 ^ 2 + Epol)) + K * E4)
    (hG₂ : G₂ = 2 * (CE * (1 + 4) + CE * (1 + B) + G₁))
    (hL₂ : L₂ = Real.log 2 ^ (s / 2)⁻¹) (hct : ct = 2 * (2 : ℝ) ^ (s / 2)⁻¹)
    (hCf : Cf = ct * (3 * κ * (ct * (ct * (Q1 ^ 2 + G₂ / L₂) + Apol)) + K * O4))
    (hG₂0 : 0 < G₂) (hCE' : 0 < CE)
    (hmeasG : Measurable (Function.uncurry fun (y : Vec d) (a : CoefficientField d Λ) =>
      max (trialGap S a y r p q) 0)) :
    OsBound P (fun a => max (trialGap S a y r p q) 0) (s / 2) ((Cf + 1) * ρ) := by
  have hκ : 0 ≤ κ := hκ'.le
  have hK : 0 ≤ K := hK'.le
  have hCE : 0 ≤ CE := hCE'.le
  -- the gaps and their expectations
  have hJm : Measurable fun a : CoefficientField d Λ => J1Heat a y r p q :=
    (hmeasJ r p q).comp (measurable_id.prodMk measurable_const)
  have hJi : Integrable (fun a => J1Heat a y r p q) P := by
    refine Integrable.of_bound hJm.aestronglyMeasurable (Λ * euclideanSq p + euclideanSq q)
      (Filter.Eventually.of_forall fun a => ?_)
    obtain ⟨h0, h1⟩ := J1Heat_nonneg_le a y hr0 p q
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  obtain ⟨hL₀i, hL₀e⟩ := hE' m₀
  obtain ⟨hLci, hLce⟩ := hE' cst
  obtain ⟨-, hA1mi, hA1me⟩ := hA1 m₀ hm₀B
  have hUi : Integrable (fun a => κ * (2 * (euclideanNorm (gradientAverage S a y r m₀ - m₀) ^ 2 +
      euclideanSq (polarizationVector a y r p q - m₀))) + K * (M a y / r) ^ d) P :=
    (((hA1mi.add hpi).const_mul 2).const_mul κ).add (hA4i.const_mul K)
  have hgU : ∀ᵐ a ∂P, J1Heat a y r p q - trialValue S a y r p q m₀ ≤
      κ * (2 * (euclideanNorm (gradientAverage S a y r m₀ - m₀) ^ 2 +
        euclideanSq (polarizationVector a y r p q - m₀))) + K * (M a y / r) ^ d := by
    filter_upwards [hpt'] with a ha
    have h1 := ha m₀ hm₀B
    have h2 := euclideanNorm_sub_sq_le_two (gradientAverage S a y r m₀) m₀
      (polarizationVector a y r p q)
    rw [hcomm] at h2
    have h3 := mul_le_mul_of_nonneg_left h2 hκ
    linarith
  have hUe : ∫ a, (κ * (2 * (euclideanNorm (gradientAverage S a y r m₀ - m₀) ^ 2 +
      euclideanSq (polarizationVector a y r p q - m₀))) + K * (M a y / r) ^ d) ∂P ≤ G₁ * ρ := by
    have i3 : Integrable (fun a => euclideanNorm (gradientAverage S a y r m₀ - m₀) ^ 2 +
        euclideanSq (polarizationVector a y r p q - m₀)) P := hA1mi.add hpi
    have i1 : Integrable (fun a => κ * (2 * (euclideanNorm (gradientAverage S a y r m₀ - m₀) ^ 2 +
        euclideanSq (polarizationVector a y r p q - m₀)))) P := (i3.const_mul 2).const_mul κ
    have i2 : Integrable (fun a => K * (M a y / r) ^ d) P := hA4i.const_mul K
    rw [integral_add i1 i2, integral_const_mul, integral_const_mul, integral_add hA1mi hpi,
      integral_const_mul, hG₁]
    have h1 := mul_le_mul_of_nonneg_left hA4E hK
    have h2 := mul_le_mul_of_nonneg_left (add_le_add hA1me hpint) (by norm_num : (0 : ℝ) ≤ 2)
    have h3 := mul_le_mul_of_nonneg_left h2 hκ
    linarith
  have hcJ : ∀ᵐ a ∂P, trialValue S a y r p q cst ≤ J1Heat a y r p q := by
    filter_upwards [hspan] with a hsa
    exact j1Functional_correctedField_le_J1Heat S a hsa y hr0 p q cst
  have hdet : IsUnit S.homogenized.det := isUnit_det_of_coercive fun ξ => (hA ξ).1
  have hhc : homogenizedJ1Objective S.homogenized p q cst = homogenizedJ1 S.homogenized p q := by
    rw [homogenizedJ1Objective_eq S.symmetric hdet, hcst]
    simp [homogenizedSlope, dot]
  have hhm : homogenizedJ1Objective S.homogenized p q m₀ ≤
      homogenizedJ1 S.homogenized p q - 1 / 2 * euclideanSq (m₀ - cst) := by
    rw [homogenizedJ1Objective_eq S.symmetric hdet, hcst]
    have := (hA (m₀ - homogenizedSlope S.homogenized p q)).1
    simp only [homogenizedSlope] at this ⊢
    linarith
  have hL₀e' : ∫ a, trialValue S a y r p q m₀ ∂P ≤
      homogenizedJ1Objective S.homogenized p q m₀ + CE * (1 + B) * ρ := by
    have h := (abs_le.mp hL₀e).2
    rw [← hρ] at h
    have : CE * (1 + euclideanSq m₀) * ρ ≤ CE * (1 + B) * ρ := by
      have := mul_le_mul_of_nonneg_left (by linarith : 1 + euclideanSq m₀ ≤ 1 + B) hCE
      exact mul_le_mul_of_nonneg_right this hρ0.le
    unfold trialValue; linarith
  have hLce' : homogenizedJ1Objective S.homogenized p q cst - CE * (1 + 4) * ρ ≤
      ∫ a, trialValue S a y r p q cst ∂P := by
    have h := (abs_le.mp hLce).1
    rw [← hρ] at h
    have : CE * (1 + euclideanSq cst) * ρ ≤ CE * (1 + 4) * ρ := by
      have := mul_le_mul_of_nonneg_left (by linarith : 1 + euclideanSq cst ≤ 1 + 4) hCE
      exact mul_le_mul_of_nonneg_right this hρ0.le
    unfold trialValue; linarith
  have hδ := le_of_expectations hJi hL₀i hLci hUi
    (g := fun a => J1Heat a y r p q - trialValue S a y r p q m₀)
    (fun a => (add_sub_cancel _ _).symm) hcJ hgU hUe
    hL₀e' hLce' hhc hhm
  have hδ' : euclideanSq (m₀ - cst) ≤ G₂ * ρ := by rw [hG₂]; linarith
  -- the final bound
  have hA2 : euclideanNorm (cst - m₀) ^ 2 ≤ G₂ * ρ := by rw [euclideanNorm_sub_comm_sq]; exact hδ'
  obtain ⟨hA1c, -, -⟩ := hA1 cst hcB
  have hXm : Measurable fun a : CoefficientField d Λ => max (trialGap S a y r p q) 0 :=
    hmeasG.comp (measurable_const.prodMk measurable_id)
  have hpos' : OsBound P (fun a => euclideanNorm (m₀ - polarizationVector a y r p q) ^ 2) (s / 2)
      (Apol * ρ) := by
    simpa only [hcomm] using hpos
  have hfin := osBound_of_four (X := fun a => max (trialGap S a y r p q) 0)
    (A₂ := euclideanNorm (cst - m₀) ^ 2) hκ' hK' hXm hA1c hA2 (mul_pos hG₂0 hρ0) hpos' hA4
    (by
      filter_upwards [hpt', hspan] with a ha hsa
      have h1 := ha cst hcB
      have h0 : 0 ≤ trialGap S a y r p q := by
        rw [← hcst] at *
        exact sub_nonneg.mpr (j1Functional_correctedField_le_J1Heat S a hsa y hr0 p q _)
      rw [max_eq_left h0]
      have h2 := euclideanNorm_sub_sq_le_three (gradientAverage S a y r cst) cst m₀
        (polarizationVector a y r p q)
      have h3 := mul_le_mul_of_nonneg_left h2 hκ
      have e : trialGap S a y r p q = J1Heat a y r p q - trialValue S a y r p q cst := by
        rw [hcst]; rfl
      rw [e]
      linarith)
  refine hfin.mono_scale ?_
  rw [← hct, ← hL₂, ← hCf]
  exact mul_le_mul_of_nonneg_right (by linarith) hρ0.le


set_option maxHeartbeats 400000 in
/-- **The trial gap estimate from the pointwise bound** (the probabilistic part of Step 2):
if almost surely, for every slope `k` with `|k|² ≤ B`,
`J₁(Φ_{y,r}, p, q) - L(k) ≤ κ |∫ Φ_{y,r} G k - m|² + K (M(y)/r)^d` with `m` the polarization
vector and `M` a jointly measurable family of scales `1 ≤ M(·, y) ≤ O_τ(C_M)`, `τ > s d/2`, then
`Fluc(s, α)`, the linear estimate of Step 1 and the expectation of the trial give the trial gap
estimate `O_{s/2}(C r^{-2α})`. -/
theorem trialGapEstimate_of_pointwise [IsProbabilityMeasure P] (S : HomogenizationData P)
    (hΛ : 0 ≤ Λ) (hA : HomogenizedMatrixBounds S.homogenized Λ)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J1Heat w.1 w.2 r p q)
    (hmeasL : ∀ (r : ℝ) (p q k : Vec d),
      Measurable fun w : Vec d × CoefficientField d Λ => trialValue S w.2 w.1 r p q k)
    {s α τ CM κ K B : ℝ} (hd : 1 ≤ d) (hs0 : 0 < s) (hα : α ≤ (d : ℝ) / 2)
    (hτ : s * ((d : ℝ) / 2) < τ) (hCM : 0 < CM) (hκ' : 0 < κ) (hK' : 0 < K)
    (hB : max ((d : ℝ) * (8 * (Λ + 1)) ^ 2) 4 ≤ B)
    (M : CoefficientField d Λ → Vec d → ℝ)
    (hM1 : ∀ a y, 1 ≤ M a y) (hMos : ∀ y, OsBound P (fun a => M a y) τ CM)
    (hpt : ∀ (r : ℝ), 1 ≤ r → ∀ p q : Vec d, euclideanNorm p < 1 → euclideanNorm q < 1 →
      ∀ y : Vec d, ∀ᵐ a ∂P, ∀ k : Vec d, euclideanSq k ≤ B →
        J1Heat a y r p q - trialValue S a y r p q k ≤
          κ * euclideanNorm (gradientAverage S a y r k - polarizationVector a y r p q) ^ 2 +
            K * (M a y / r) ^ d)
    (hF : FlucJ1 P s α) (h4 : LinearAverageEstimate P S s α)
    (hE : TrialObjectiveExpectation P S (2 * α)) :
    TrialGapEstimate P S (s / 2) (2 * α) := by
  obtain ⟨CF, hCF, hF⟩ := hF
  obtain ⟨C4, hC4, h4⟩ := h4
  obtain ⟨CE, hCE, hE⟩ := hE
  have hκ : 0 ≤ κ := hκ'.le
  have hK : 0 ≤ K := hK'.le
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hτ0 : 0 < τ := lt_of_le_of_lt (by positivity) hτ
  have hs2 : 0 < s / 2 := by positivity
  have hB4 : 4 ≤ B := (le_max_right _ _).trans hB
  have hBm : (d : ℝ) * (8 * (Λ + 1)) ^ 2 ≤ B := (le_max_left _ _).trans hB
  have hB0 : 0 ≤ B := by linarith
  obtain ⟨cs, hcs⟩ : ∃ c : ℝ, c = 2 * (2 : ℝ) ^ s⁻¹ := ⟨_, rfl⟩
  obtain ⟨ct, hct⟩ : ∃ c : ℝ, c = 2 * (2 : ℝ) ^ (s / 2)⁻¹ := ⟨_, rfl⟩
  have hct0 : 0 < ct := by rw [hct]; positivity
  obtain ⟨Ks, hKs⟩ : ∃ c : ℝ, c = momentConstant (s / 2) := ⟨_, rfl⟩
  have hKs0 : 0 < Ks := hKs ▸ momentConstant_pos _
  obtain ⟨Q1, hQ1⟩ : ∃ c : ℝ, c = C4 * (1 + Real.sqrt B) := ⟨_, rfl⟩
  have hQ10 : 0 < Q1 := by rw [hQ1]; positivity
  obtain ⟨Apol, hApol⟩ : ∃ c : ℝ, c = ct ^ d * (16 * (cs ^ 2 * CF) ^ 2) := ⟨_, rfl⟩
  have hApol0 : 0 ≤ Apol := by rw [hApol]; positivity
  obtain ⟨Epol, hEpol⟩ : ∃ c : ℝ, c = d * (16 * (Ks * (cs ^ 2 * CF) ^ 2)) := ⟨_, rfl⟩
  have hEpol0 : 0 ≤ Epol := by rw [hEpol]; positivity
  obtain ⟨E4, hE4⟩ : ∃ c : ℝ, c = momentConstant (τ / d) * CM ^ d := ⟨_, rfl⟩
  have hE40 : 0 < E4 := by rw [hE4]; exact mul_pos (momentConstant_pos _) (pow_pos hCM _)
  have he1 : 0 ≤ 2 * Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  obtain ⟨O4, hO4⟩ : ∃ c : ℝ, c = (2 * Real.exp 1 - 1) ^ (s / 2)⁻¹ * CM ^ d := ⟨_, rfl⟩
  have hO40 : 0 ≤ O4 := by rw [hO4]; exact mul_nonneg (Real.rpow_nonneg he1 _) (by positivity)
  obtain ⟨G₁, hG₁⟩ : ∃ c : ℝ, c = κ * (2 * (Ks * Q1 ^ 2 + Epol)) + K * E4 := ⟨_, rfl⟩
  have hG₁0 : 0 ≤ G₁ := by rw [hG₁]; positivity
  obtain ⟨G₂, hG₂⟩ : ∃ c : ℝ, c = 2 * (CE * (1 + 4) + CE * (1 + B) + G₁) := ⟨_, rfl⟩
  have hG₂0 : 0 < G₂ := by rw [hG₂]; positivity
  obtain ⟨L₂, hL₂⟩ : ∃ c : ℝ, c = Real.log 2 ^ (s / 2)⁻¹ := ⟨_, rfl⟩
  have hL₂0 : 0 < L₂ := by rw [hL₂]; exact Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _
  obtain ⟨Cf, hCf⟩ : ∃ c : ℝ,
      c = ct * (3 * κ * (ct * (ct * (Q1 ^ 2 + G₂ / L₂) + Apol)) + K * O4) := ⟨_, rfl⟩
  have hCf0 : 0 ≤ Cf := by rw [hCf]; positivity
  refine ⟨Cf + 1, by linarith, ?_⟩
  intro r hr p q hp hq
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  obtain ⟨ρ, hρ⟩ : ∃ c : ℝ, c = r ^ (-(2 * α)) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; exact Real.rpow_pos_of_pos hr0 _
  have hrd : r ^ (-(d : ℝ)) ≤ ρ := by rw [hρ]; exact rpow_neg_le_rpow_neg hr (by linarith)
  have hsq : (r ^ (-α)) ^ 2 = ρ := by
    rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul hr0.le]; congr 1; push_cast; ring
  have hmeasG : Measurable (Function.uncurry fun (y : Vec d) (a : CoefficientField d Λ) =>
      max (trialGap S a y r p q) 0) :=
    (((hmeasJ r p q).comp measurable_swap).sub
      (hmeasL r p q (homogenizedSlope S.homogenized p q))).max measurable_const
  refine ⟨hmeasG, fun y => ?_⟩
  -- the slopes
  obtain ⟨cst, hcst⟩ : ∃ c : Vec d, c = homogenizedSlope S.homogenized p q := ⟨_, rfl⟩
  have hc4 : euclideanSq cst ≤ 4 := by
    rw [hcst]; exact euclideanSq_homogenizedSlope_le (fun ξ => (hA ξ).1) hp.le hq.le
  obtain ⟨m₀, hm₀⟩ : ∃ m : Vec d, m = fun i => ∫ a, polarizationVector a y r p q i ∂P :=
    ⟨_, rfl⟩
  have hm₀B : euclideanSq m₀ ≤ B := by
    refine (euclideanSq_le_of_abs_le (c := 8 * (Λ + 1)) fun i => ?_).trans hBm
    rw [hm₀]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ a, |polarizationVector a y r p q i| ∂P ≤ ∫ _a, 8 * (Λ + 1) ∂P :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall fun a =>
              abs_polarizationVector_le a hΛ y hr0 hp hq i)
      _ = 8 * (Λ + 1) := by simp
  have hcB : euclideanSq cst ≤ B := hc4.trans hB4
  have hnorm : ∀ k : Vec d, euclideanSq k ≤ B → euclideanNorm k ≤ Real.sqrt B := fun k hk =>
    Real.sqrt_le_sqrt hk
  -- the linear estimate at the two slopes
  have hA1 : ∀ k : Vec d, euclideanSq k ≤ B →
      OsBound P (fun a => euclideanNorm (gradientAverage S a y r k - k) ^ 2) (s / 2) (Q1 ^ 2 * ρ) ∧
      Integrable (fun a => euclideanNorm (gradientAverage S a y r k - k) ^ 2) P ∧
      ∫ a, euclideanNorm (gradientAverage S a y r k - k) ^ 2 ∂P ≤ Ks * Q1 ^ 2 * ρ := by
    intro k hk
    have h := h4 y r hr k
    have hsc : (C4 * (1 + euclideanNorm k) * r ^ (-α)) ^ 2 ≤ Q1 ^ 2 * ρ :=
      sq_scale_le hC4 (euclideanNorm_nonneg k) (hnorm k hk) hQ1 hsq
    obtain ⟨hi, hint⟩ := h.integral_sq_le fun a => euclideanNorm_nonneg _
    refine ⟨(h.sq fun a => euclideanNorm_nonneg _).mono_scale hsc, hi, ?_⟩
    rw [← hKs] at hint
    calc _ ≤ Ks * (C4 * (1 + euclideanNorm k) * r ^ (-α)) ^ 2 := hint
      _ ≤ Ks * (Q1 ^ 2 * ρ) := mul_le_mul_of_nonneg_left hsc hKs0.le
      _ = Ks * Q1 ^ 2 * ρ := by ring
  -- the scale term
  have hA4os : OsBound P (fun a => (M a y / r) ^ d) (τ / d) ((CM / r) ^ d) :=
    (hMos y).div_pow (fun a => zero_le_one.trans (hM1 a y)) hr0 hd
  have hCMr : (CM / r) ^ d = CM ^ d * r ^ (-(d : ℝ)) := by
    rw [div_pow, Real.rpow_neg hr0.le, Real.rpow_natCast, div_eq_mul_inv]
  have hA4 : OsBound P (fun a => (M a y / r) ^ d) (s / 2) (O4 * ρ) := by
    refine (hA4os.mono_exponent hs2 (by rw [le_div_iff₀ hd0]; nlinarith)).mono_scale ?_
    rw [hCMr, hO4, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hrd (by positivity)
  obtain ⟨hA4i, hA4int⟩ := hA4os.integral_le_factorial_mul fun a =>
    pow_nonneg (div_nonneg (zero_le_one.trans (hM1 a y)) hr0.le) _
  have hA4E : ∫ a, (M a y / r) ^ d ∂P ≤ E4 * ρ := by
    refine hA4int.trans ?_
    rw [hCMr, hE4, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hrd (by positivity)
  -- the polarization vector
  obtain ⟨hpos, hpi, hpint⟩ := polarizationVector_fluctuation hs0 hCF hmeasJ hF y hr hp hq
  rw [← hm₀] at hpos hpi hpint
  have hpolsc : ct ^ d * (16 * ((2 * (2 : ℝ) ^ s⁻¹) ^ 2 * (CF * r ^ (-α))) ^ 2) = Apol * ρ := by
    rw [hApol, ← hsq, ← hcs]; ring
  have hpolE : (d : ℝ) * (16 * (momentConstant (s / 2) *
      ((2 * (2 : ℝ) ^ s⁻¹) ^ 2 * (CF * r ^ (-α))) ^ 2)) = Epol * ρ := by
    rw [hEpol, ← hsq, ← hcs, ← hKs]; ring
  rw [← hct, hpolsc] at hpos
  rw [hpolE] at hpint
  have hcomm : ∀ a : CoefficientField d Λ, euclideanNorm (m₀ - polarizationVector a y r p q) ^ 2 =
      euclideanSq (polarizationVector a y r p q - m₀) := fun a => euclideanNorm_sub_comm_sq _ _
  have hE' := fun k => hE y r hr p q hp hq k
  rw [← hρ]
  exact trialGap_osBound_at S hA hspan hmeasJ hr0 hρ hρ0 hκ' hK' hcst hc4
    hm₀B hcB hA1 hA4 hA4i hA4E hpos hpi hpint hcomm (hpt r hr p q hp hq y) hE' hG₁ hG₂ hL₂
    hct hCf hG₂0 hCE hmeasG

/-- **The trial gap estimate under `Fluc(s, α)`** from the linear estimate of Step 1, the
expectation of the trial, the energy bound below the scale and Proposition 3.21 at an exponent
`τ > s d/2` (Step 2 of the proof of Proposition 4.10 used here). -/
theorem trialGapEstimate_of_linearAverages [IsProbabilityMeasure P] (S : HomogenizationData P)
    (hΛ : 0 ≤ Λ) (hA : HomogenizedMatrixBounds S.homogenized Λ)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J1Heat w.1 w.2 r p q)
    (hmeasL : ∀ (r : ℝ) (p q k : Vec d),
      Measurable fun w : Vec d × CoefficientField d Λ => trialValue S w.2 w.1 r p q k)
    {s α τ C μ CN : ℝ} (hd : 1 ≤ d) (hs0 : 0 < s) (hα : α ≤ (d : ℝ) / 2)
    (hτ : s * ((d : ℝ) / 2) < τ) (hC : 0 < C) (hμ : 0 < μ) (hCN : 0 < CN)
    (hrate : GaussianCorrectorRate P S τ C μ) (hN : GaussianEnergyBound P S τ CN)
    (hF : FlucJ1 P s α) (h4 : LinearAverageEstimate P S s α)
    (hE : TrialObjectiveExpectation P S (2 * α)) :
    TrialGapEstimate P S (s / 2) (2 * α) := by
  obtain ⟨Xg, hXgm, hXg⟩ := hrate
  obtain ⟨XN, hXNm, hXN1, hXNos, hXNb⟩ := hN
  have hτ0 : 0 < τ := lt_of_le_of_lt (by positivity) hτ
  obtain ⟨r₀, hr₀⟩ : ∃ c : ℝ, c = max 1 ((4 * C) ^ μ⁻¹) := ⟨_, rfl⟩
  have hr₀1 : 1 ≤ r₀ := hr₀ ▸ le_max_left _ _
  obtain ⟨M, hM⟩ : ∃ M : CoefficientField d Λ → Vec d → ℝ,
      M = fun a y => max (max (Xg a y) r₀) (XN a y) := ⟨_, rfl⟩
  have hM1 : ∀ a y, 1 ≤ M a y := fun a y => by
    rw [hM]; exact hr₀1.trans ((le_max_right _ _).trans (le_max_left _ _))
  have hLτ0 : 0 < Real.log 2 ^ τ⁻¹ := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _
  obtain ⟨CM, hCM⟩ : ∃ c : ℝ,
      c = (2 : ℝ) ^ τ⁻¹ * max ((2 : ℝ) ^ τ⁻¹ * max C (r₀ / Real.log 2 ^ τ⁻¹)) CN := ⟨_, rfl⟩
  have hCM0 : 0 < CM := by
    rw [hCM]; exact mul_pos (Real.rpow_pos_of_pos two_pos _) (lt_max_of_lt_right hCN)
  have hMos : ∀ y, OsBound P (fun a => M a y) τ CM := fun y => by
    rw [hM, hCM]
    exact osBound_max (osBound_max (hXg y).1 (osBound_of_le_const measurable_const hτ0
      (zero_lt_one.trans_le hr₀1) (Filter.Eventually.of_forall fun _ => le_rfl))) (hXNos y)
  obtain ⟨B, hB⟩ : ∃ c : ℝ, c = max ((d : ℝ) * (8 * (Λ + 1)) ^ 2) 4 := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; exact le_max_of_le_right (by norm_num)
  refine trialGapEstimate_of_pointwise S hΛ hA hspan hmeasJ hmeasL (κ := 8 / 9 * (Λ + 1 / 2))
    (K := 2 * (Λ + 1) + 2 * CN * B) (B := B) hd hs0 hα hτ hCM0 (by positivity)
    (by nlinarith [mul_nonneg hCN.le hB0]) hB.ge M hM1 hMos ?_ hF h4 hE
  intro r hr p q hp hq y
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  filter_upwards [hspan, (hXg y).2, hXNb] with a hsa hga hNa
  intro k hk
  have hgood : max (Xg a y) r₀ ≤ r →
      GaussianAverageBounds a S.homogenized (correctedField S a) y r (min (C * r ^ (-μ)) (1 / 4)) := by
    intro h
    have hr₀r : r₀ ≤ r := (le_max_right _ _).trans h
    have h4C : 4 * C ≤ r ^ μ := by
      have h1 : (4 * C) ^ μ⁻¹ ≤ r := (hr₀ ▸ le_max_right 1 ((4 * C) ^ μ⁻¹)).trans hr₀r
      have h2 := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) h1 hμ.le
      rwa [Real.rpow_inv_rpow (by positivity) hμ.ne'] at h2
    have hε : C * r ^ (-μ) ≤ 1 / 4 := by
      rw [Real.rpow_neg hr0.le, ← div_eq_mul_inv, div_le_iff₀ (Real.rpow_pos_of_pos hr0 _)]
      linarith
    rw [min_eq_left hε]
    exact hga r hr ((le_max_left _ _).trans h)
  have hMa : M a y = max (max (Xg a y) r₀) (XN a y) := by rw [hM]
  have h := trialGap_pos_le S a hΛ hA hsa y hr (min_le_right _ _) hgood
    (hMa ▸ le_max_left _ _) (hMa ▸ le_max_right _ _) (zero_le_one.trans (hXN1 a y)) hCN.le
    hp.le hq.le k (hNa y r hr k).1 (hNa y r hr k).2
  have hMd : 0 ≤ (M a y / r) ^ d :=
    pow_nonneg (div_nonneg (zero_le_one.trans (hM1 a y)) hr0.le) _
  have hK : (2 * (Λ + 1) + 2 * CN * euclideanSq k) * (M a y / r) ^ d ≤
      (2 * (Λ + 1) + 2 * CN * B) * (M a y / r) ^ d :=
    mul_le_mul_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left hk hCN.le]) hMd
  have := le_max_left (J1Heat a y r p q - j1Functional a (heatKernel y r) p q
    (correctedField S a k)) 0
  unfold trialValue gradientAverage
  linarith

end Estimate

end QSH
