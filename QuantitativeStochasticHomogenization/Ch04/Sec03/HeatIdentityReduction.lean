import QuantitativeStochasticHomogenization.Ch04.Sec03.Lemma413Statement

/-!
# From Lemma 4.13 to the linear estimate, given the heat identity

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, Lemma 4.13 and the linear estimate (4) of Step 1 of the route of Proposition 4.10
used here.

The heat identity (H) of the route writes `∫ Φ_{z,r} ∇φ_{eᵢ}`, for `r ≥ 2`, as a time integral of
Hessians of anisotropic Gaussians against the commutator `(a - ā)(eᵢ + ∇φ_{eᵢ})`; after the semigroup
splitting and the limit `T → ∞` it gives the bound recorded in `HeatIdentityBound`: almost surely
`|P eᵢ - eᵢ| ≤ ∫_{u > r²/2} ∫ k_r(u, x) |commutator at (z - x, √u)| dx du`, with a positive kernel of
mass `∫ k_r(u, ·) ≤ C_k / u`.

`gradient_sub_osBound_of_heat`: from this bound and the commutator estimate of Lemma 4.13,
Minkowski's inequality for `O_s` (Lemma A.4) on the product of the time and space measures gives
`|P eᵢ - eᵢ| ≤ O_s(κ_s C C_k (r²/2)^{-α/2} / (α/2))`.
-/

open MeasureTheory Filter Set

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

section Heat

variable {P : Measure (CoefficientField d Λ)}

/-- The norm of the commutator `∫ Φ_{y,ρ} (a - ā)(eᵢ + ∇φ_{eᵢ})`. -/
def commutatorNorm (S : HomogenizationData P) (a : CoefficientField d Λ) (y : Vec d) (ρ : ℝ)
    (i : Fin d) : ℝ :=
  euclideanNorm (fluxAverage S a y ρ (unitVector i) -
    S.homogenized.mulVec (gradientAverage S a y ρ (unitVector i)))

/-- The constant of Minkowski's inequality for `O_s` (Lemma A.4) at every exponent. -/
def minkowskiConstant (s : ℝ) : ℝ := max 1 ((1 + (1 - s) / (s * Real.log 2)) ^ s⁻¹)

/-- **The bound from the heat identity (H)**: a jointly measurable positive kernel `k r u x` with
`∫ k r u ≤ C_k / u` for `u ≥ 1`, such that for `r ≥ 2` almost surely
`|P eᵢ - eᵢ| ≤ ∫_{u > r²/2} ∫ k r u x |commutator at (z - x, √u)| dx du`. -/
def HeatIdentityBound (P : Measure (CoefficientField d Λ)) (S : HomogenizationData P)
    (Ck : ℝ) : Prop :=
  ∃ k : ℝ → ℝ → Vec d → ℝ, (∀ r, Measurable (Function.uncurry (k r))) ∧
    (∀ r u x, 0 < k r u x) ∧
    (∀ r u, 1 ≤ u → Integrable (k r u) ∧ ∫ x, k r u x ≤ Ck * u⁻¹) ∧
    ∀ (z : Vec d) (r : ℝ), 2 ≤ r → ∀ i : Fin d, ∀ᵐ a ∂P,
      euclideanNorm (gradientAverage S a z r (unitVector i) - unitVector i) ≤
        ∫ u in Ioi (r ^ 2 / 2), ∫ x, k r u x * commutatorNorm S a (z - x) (Real.sqrt u) i

theorem integral_Ioi_rpow_neg_one_sub {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    ∫ u in Ioi c, u ^ (-1 - β) = c ^ (-β) / β := by
  rw [integral_Ioi_rpow_of_lt (by linarith) hc, show -1 - β + 1 = -β by ring, neg_div_neg_eq]

theorem sqrt_rpow_neg_mul_inv {u α : ℝ} (hu : 0 < u) :
    u⁻¹ * Real.sqrt u ^ (-α) = u ^ (-1 - α / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hu.le, ← Real.rpow_neg_one, ← Real.rpow_add hu]
  ring_nf

/-- **`|P eᵢ - eᵢ|` from the commutator estimate and the heat identity** (Minkowski for `O_s`). -/
theorem gradient_sub_osBound_of_heat [IsProbabilityMeasure P] (S : HomogenizationData P)
    {s α CC Ck : ℝ} (hα0 : 0 < α) (hCC : 0 < CC)
    (hC : ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ j : Fin d,
      OsBound P (fun a => commutatorNorm S a z r j) s (CC * r ^ (-α)))
    (k : ℝ → ℝ → Vec d → ℝ) (hkm : ∀ r, Measurable (Function.uncurry (k r)))
    (hk0 : ∀ r u x, 0 < k r u x)
    (hki : ∀ r u, 1 ≤ u → Integrable (k r u) ∧ ∫ x, k r u x ≤ Ck * u⁻¹)
    (hmeasC : ∀ i, Measurable fun w : (Vec d × ℝ) × CoefficientField d Λ =>
      commutatorNorm S w.2 w.1.1 w.1.2 i)
    (z : Vec d) {r : ℝ} (hr : 2 ≤ r) (i : Fin d)
    (hH : ∀ᵐ a ∂P, euclideanNorm (gradientAverage S a z r (unitVector i) - unitVector i) ≤
      ∫ u in Ioi (r ^ 2 / 2), ∫ x, k r u x * commutatorNorm S a (z - x) (Real.sqrt u) i)
    (hPm : Measurable fun a => gradientAverage S a z r (unitVector i)) :
    OsBound P (fun a => euclideanNorm (gradientAverage S a z r (unitVector i) - unitVector i)) s
      (minkowskiConstant s * (Ck * CC * ((r ^ 2 / 2) ^ (-(α / 2)) / (α / 2)))) := by
  set c : ℝ := r ^ 2 / 2 with hcdef
  have hc2 : 2 ≤ c := by rw [hcdef]; nlinarith
  have hc0 : 0 < c := by linarith
  set μ : Measure (ℝ × Vec d) := (volume.restrict (Ioi c)).prod volume with hμdef
  set X : ℝ × Vec d → CoefficientField d Λ → ℝ := fun w a =>
    k r w.1 w.2 * commutatorNorm S a (z - w.2) (Real.sqrt (max w.1 1)) i with hXdef
  set θ : ℝ × Vec d → ℝ := fun w => k r w.1 w.2 * (CC * Real.sqrt (max w.1 1) ^ (-α)) with hθdef
  have hρ1 : ∀ u : ℝ, 1 ≤ Real.sqrt (max u 1) := fun u => Real.one_le_sqrt.mpr (le_max_right _ _)
  have hθpos : ∀ w, 0 < θ w := fun w =>
    mul_pos (hk0 _ _ _) (mul_pos hCC (Real.rpow_pos_of_pos (zero_lt_one.trans_le (hρ1 _)) _))
  have hX : ∀ w, OsBound P (X w) s (θ w) := fun w =>
    (hC (z - w.2) _ (hρ1 w.1) i).const_mul (hk0 _ _ _)
  have hXm : Measurable (Function.uncurry X) := by
    have hg : Measurable fun w : (ℝ × Vec d) × CoefficientField d Λ =>
        ((z - w.1.2, Real.sqrt (max w.1.1 1)), w.2) :=
      ((measurable_const.sub (measurable_snd.comp measurable_fst)).prodMk
        ((measurable_fst.comp measurable_fst).max measurable_const).sqrt).prodMk measurable_snd
    have h2 : Measurable fun w : (ℝ × Vec d) × CoefficientField d Λ => k r w.1.1 w.1.2 :=
      (hkm r).comp measurable_fst
    have h3 := (hmeasC i).comp hg
    exact h2.mul h3
  have hX0 : ∀ w a, 0 ≤ X w a := fun w a => mul_nonneg (hk0 _ _ _).le (euclideanNorm_nonneg _)
  have hθm : Measurable θ := by
    have h2 : Measurable fun w : ℝ × Vec d => k r w.1 w.2 := hkm r
    have h3 : Measurable fun w : ℝ × Vec d => CC * Real.sqrt (max w.1 1) ^ (-α) :=
      measurable_const.mul ((measurable_fst.max measurable_const).sqrt.pow_const _)
    exact h2.mul h3
  -- the time slices
  have hθu : ∀ u : ℝ, 1 ≤ u → Integrable (fun x => θ (u, x)) ∧
      ∫ x, θ (u, x) ≤ Ck * CC * u ^ (-1 - α / 2) := by
    intro u hu
    have hu0 : 0 < u := zero_lt_one.trans_le hu
    obtain ⟨hki1, hki2⟩ := hki r u hu
    have hm : max u 1 = u := max_eq_left hu
    simp only [hθdef, hm]
    refine ⟨hki1.mul_const _, ?_⟩
    rw [integral_mul_const]
    have hp : 0 ≤ CC * Real.sqrt u ^ (-α) :=
      mul_nonneg hCC.le (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
    calc (∫ x, k r u x) * (CC * Real.sqrt u ^ (-α)) ≤ Ck * u⁻¹ * (CC * Real.sqrt u ^ (-α)) :=
          mul_le_mul_of_nonneg_right hki2 hp
      _ = Ck * CC * (u⁻¹ * Real.sqrt u ^ (-α)) := by ring
      _ = Ck * CC * u ^ (-1 - α / 2) := by rw [sqrt_rpow_neg_mul_inv hu0]
  have hgi : IntegrableOn (fun u : ℝ => Ck * CC * u ^ (-1 - α / 2)) (Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hc0).const_mul _
  have hIoi : ∀ u ∈ Ioi c, 1 ≤ u := fun u hu => by
    have : c < u := hu
    linarith
  have hθi : Integrable θ μ := by
    rw [hμdef, integrable_prod_iff hθm.aestronglyMeasurable]
    refine ⟨(ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu =>
      (hθu u (hIoi u hu)).1), ?_⟩
    refine hgi.mono' (hθm.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    have hn : (fun x => ‖θ (u, x)‖) = fun x => θ (u, x) := funext fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (hθpos _)]
    rw [hn, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => (hθpos _).le)]
    exact (hθu u (hIoi u hu)).2
  have hθint : ∫ w, θ w ∂μ ≤ Ck * CC * (c ^ (-(α / 2)) / (α / 2)) := by
    rw [hμdef, integral_prod θ hθi, ← integral_Ioi_rpow_neg_one_sub (by linarith) hc0,
      ← integral_const_mul]
    exact setIntegral_mono_on hθi.integral_prod_left hgi measurableSet_Ioi fun u hu =>
      (hθu u (hIoi u hu)).2
  have hμ0 : μ univ ≠ 0 := by
    rw [hμdef, ← univ_prod_univ, Measure.prod_prod, Measure.restrict_apply MeasurableSet.univ,
      univ_inter, Real.volume_Ioi]
    exact mul_ne_zero ENNReal.top_ne_zero (Measure.measure_univ_ne_zero.mpr (NeZero.ne _))
  have hθ0 : 0 < ∫ w, θ w ∂μ := by
    rw [integral_pos_iff_support_of_nonneg (fun w => (hθpos w).le) hθi]
    have : Function.support θ = univ := eq_univ_of_forall fun w => (hθpos w).ne'
    rw [this]
    exact pos_iff_ne_zero.mpr hμ0
  -- Minkowski for `O_s`
  obtain ⟨hXi, hos⟩ : (∀ᵐ a ∂P, Integrable (fun w => X w a) μ) ∧
      OsBound P (fun a => ∫ w, X w a ∂μ) s (minkowskiConstant s * ∫ w, θ w ∂μ) := by
    by_cases hs1 : 1 ≤ s
    · obtain ⟨h1, h2⟩ := osBound_integral hs1 hXm hX0 hθm hθi hθ0 hX
      exact ⟨h1, h2.mono_scale (le_mul_of_one_le_left hθ0.le (le_max_left _ _))⟩
    · obtain ⟨h1, h2⟩ := osBound_integral_of_lt_one (not_le.mp hs1) hXm hX0 hθm hθi hθ0 hX
      exact ⟨h1, h2.mono_scale (mul_le_mul_of_nonneg_right (le_max_right _ _) hθ0.le)⟩
  have hNm : Measurable fun a =>
      euclideanNorm (gradientAverage S a z r (unitVector i) - unitVector i) := by
    have hc' : Measurable fun a => gradientAverage S a z r (unitVector i) - unitVector i :=
      hPm.sub measurable_const
    simp only [euclideanNorm, euclideanSq, dot]
    exact (Finset.measurable_sum _ fun k _ =>
      ((measurable_pi_apply k).comp hc').mul ((measurable_pi_apply k).comp hc')).sqrt
  refine (hos.of_le_ae hNm ?_).mono_scale
    (mul_le_mul_of_nonneg_left hθint (zero_le_one.trans (le_max_left _ _)))
  filter_upwards [hH, hXi] with a ha hai
  refine ha.trans (le_of_eq ?_)
  rw [hμdef, integral_prod (fun w => X w a) hai]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  simp only [hXdef, max_eq_left (hIoi u hu)]

/-- The gradient average of the corrected field is linear in the slope. -/
theorem gradientAverage_eq_sum (S : HomogenizationData P) (a : CoefficientField d Λ) (z : Vec d)
    (r : ℝ) (ξ : Vec d)
    (hi : ∀ i, Integrable (fun x => heatKernel z r x • correctedField S a (unitVector i) x)) :
    gradientAverage S a z r ξ = ∑ i, ξ i • gradientAverage S a z r (unitVector i) := by
  have hcf : ∀ i x, correctedField S a (unitVector i) x = correctedCoordinate S a i x := by
    intro i x
    simp only [correctedField, unitVector]
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj])
      (by simp)]
    simp
  have hi' : ∀ i, Integrable (fun x => heatKernel z r x • correctedCoordinate S a i x) := fun i => by
    simpa only [hcf] using hi i
  unfold gradientAverage
  simp only [hcf]
  have hfun : (fun x => heatKernel z r x • correctedField S a ξ x) =
      fun x => ∑ i, ξ i • (heatKernel z r x • correctedCoordinate S a i x) := by
    funext x
    simp only [correctedField, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  rw [hfun, integral_finsetSum]
  · simp only [integral_smul]
  · intro i _
    exact (hi' i).smul (ξ i)

theorem sum_smul_unitVector (ξ : Vec d) : ∑ i, ξ i • (unitVector i : Vec d) = ξ := by
  funext k
  simp [unitVector, Pi.single_apply]

theorem rpow_sq_div_two {r α : ℝ} (hr : 0 < r) :
    (r ^ 2 / 2) ^ (-(α / 2)) = 2 ^ (α / 2) * r ^ (-α) := by
  rw [Real.div_rpow (sq_nonneg r) zero_le_two, ← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le,
    Real.rpow_neg zero_le_two]
  push_cast
  rw [show (2 : ℝ) * -(α / 2) = -α by ring, div_inv_eq_mul, mul_comm]

/-- **`|P eᵢ - eᵢ| ≤ O_s(C r^{-α})` at every scale** from the commutator estimate and the heat
identity (`r ≥ 2`), and from the energy bound below the scale (`1 ≤ r < 2`). -/
theorem gradient_sub_osBound [IsProbabilityMeasure P] (hd : 1 ≤ d) (S : HomogenizationData P)
    (hΛ : 0 ≤ Λ) {s α Ck : ℝ} (hs0 : 0 < s) (hα0 : 0 < α) (hC : CommutatorEstimate P S s α)
    (hH : HeatIdentityBound P S Ck)
    (hmeasC : ∀ i, Measurable fun w : (Vec d × ℝ) × CoefficientField d Λ =>
      commutatorNorm S w.2 w.1.1 w.1.2 i)
    (hmeasA : ∀ (z : Vec d) (r : ℝ) (ξ : Vec d), Measurable (fun a => gradientAverage S a z r ξ))
    {τ CN : ℝ} (hN : GaussianEnergyBound P S τ CN) (hτs : s ≤ τ / ((d : ℝ) / 2))
    (hint : AveragesIntegrable P S) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ i : Fin d,
      OsBound P (fun a => euclideanNorm (gradientAverage S a z r (unitVector i) - unitVector i)) s
        (C₁ * r ^ (-α)) := by
  obtain ⟨CC, hCC, hCo⟩ := hC
  obtain ⟨k, hkm, hk0, hki, hHb⟩ := hH
  obtain ⟨XN, -, hXN1, hXNos, hXNe⟩ := hN
  have hCN : 0 < CN := (hXNos 0).scale_pos
  set K : ℝ := minkowskiConstant s * (Ck * CC * (2 ^ (α / 2) / (α / 2))) with hK
  set θ₁ : ℝ := 2 * (2 : ℝ) ^ s⁻¹ * (Real.sqrt CN * (2 * (2 : ℝ) ^ s⁻¹ * (1 / Real.log 2 ^ s⁻¹ +
    (2 * Real.exp 1 - 1) ^ s⁻¹ * CN ^ ((d : ℝ) / 2))) + 1 / Real.log 2 ^ s⁻¹) with hθ₁
  have hl : 0 < Real.log 2 ^ s⁻¹ := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _
  have h1 : OsBound P (fun _ : CoefficientField d Λ => (1 : ℝ)) s (1 / Real.log 2 ^ s⁻¹) :=
    osBound_of_le_const measurable_const hs0 one_pos (Eventually.of_forall fun _ => le_rfl)
  have hθ₁0 : 0 < θ₁ := by
    have := (osBound_add_le_sum (size_bound (P := P) hd hs0 hCN (fun a => XN a 0)
      (fun a => hXN1 a 0) hτs (hXNos 0)) h1).scale_pos
    simpa only [hθ₁] using this
  refine ⟨max K (θ₁ * 2 ^ α), lt_max_of_lt_right (mul_pos hθ₁0 (by positivity)),
    fun z r hr i => ?_⟩
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hρ : 0 ≤ r ^ (-α) := Real.rpow_nonneg hr0.le _
  have hNm : Measurable fun a =>
      euclideanNorm (gradientAverage S a z r (unitVector i) - unitVector i) := by
    have hc' : Measurable fun a => gradientAverage S a z r (unitVector i) - unitVector i :=
      (hmeasA z r _).sub measurable_const
    simp only [euclideanNorm, euclideanSq, dot]
    exact (Finset.measurable_sum _ fun k _ =>
      ((measurable_pi_apply k).comp hc').mul ((measurable_pi_apply k).comp hc')).sqrt
  by_cases hr2 : 2 ≤ r
  · have hG := gradient_sub_osBound_of_heat S hα0 hCC hCo k hkm hk0 hki hmeasC z hr2 i
      (hHb z r hr2 i) (hmeasA z r _)
    rw [rpow_sq_div_two hr0] at hG
    refine hG.mono_scale ?_
    calc minkowskiConstant s * (Ck * CC * (2 ^ (α / 2) * r ^ (-α) / (α / 2)))
        = K * r ^ (-α) := by rw [hK]; ring
      _ ≤ max K (θ₁ * 2 ^ α) * r ^ (-α) := mul_le_mul_of_nonneg_right (le_max_left _ _) hρ
  · have hsz := osBound_add_le_sum (size_bound (P := P) hd hs0 hCN (fun a => XN a z)
      (fun a => hXN1 a z) hτs (hXNos z)) h1
    refine (hsz.of_le_ae hNm ?_).mono_scale ?_
    · filter_upwards [hint, hXNe] with a ha hb
      have hX0 : 0 ≤ XN a z := zero_le_one.trans (hXN1 a z)
      obtain ⟨hP, -⟩ := averages_le_of_energy S a hΛ z hr0 hCN.le hX0 i (ha z r hr (unitVector i))
        (hb z r hr (unitVector i)).2
      have h3 : (XN a z / r) ^ ((d : ℝ) / 2) ≤ XN a z ^ ((d : ℝ) / 2) :=
        Real.rpow_le_rpow (div_nonneg hX0 hr0.le) (div_le_self hX0 hr) (by positivity)
      have h5 : Real.sqrt CN * (1 + (XN a z / r) ^ ((d : ℝ) / 2)) ≤
          Real.sqrt CN * (1 + XN a z ^ ((d : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
      calc euclideanNorm (gradientAverage S a z r (unitVector i) - unitVector i)
          ≤ euclideanNorm (gradientAverage S a z r (unitVector i)) +
              euclideanNorm (unitVector i : Vec d) := euclideanNorm_sub_le _ _
        _ ≤ Real.sqrt CN * (1 + XN a z ^ ((d : ℝ) / 2)) + 1 := by
          rw [euclideanNorm_unitVector]; linarith
    · have hr2' : r ≤ 2 := (not_le.mp hr2).le
      have hq : 1 ≤ 2 ^ α * r ^ (-α) := by
        rw [Real.rpow_neg hr0.le, ← div_eq_mul_inv, ← Real.div_rpow zero_le_two hr0.le]
        exact Real.one_le_rpow ((one_le_div hr0).mpr hr2') hα0.le
      calc 2 * (2 : ℝ) ^ s⁻¹ * (Real.sqrt CN * (2 * (2 : ℝ) ^ s⁻¹ * (1 / Real.log 2 ^ s⁻¹ +
            (2 * Real.exp 1 - 1) ^ s⁻¹ * CN ^ ((d : ℝ) / 2))) + 1 / Real.log 2 ^ s⁻¹)
          = θ₁ := by rw [hθ₁]
        _ ≤ θ₁ * (2 ^ α * r ^ (-α)) := le_mul_of_one_le_right hθ₁0.le hq
        _ = θ₁ * 2 ^ α * r ^ (-α) := by ring
        _ ≤ max K (θ₁ * 2 ^ α) * r ^ (-α) := mul_le_mul_of_nonneg_right (le_max_right _ _) hρ

/-- **The linear estimate (4) of Step 1** from the commutator estimate of Lemma 4.13, the bound
from the heat identity (H) and the energy bound below the scale. -/
theorem linearAverageEstimate_of_heat [IsProbabilityMeasure P] (hd : 1 ≤ d)
    (S : HomogenizationData P) (hΛ : 0 ≤ Λ) {s α Ck : ℝ} (hs0 : 0 < s) (hα0 : 0 < α)
    (hC : CommutatorEstimate P S s α) (hH : HeatIdentityBound P S Ck)
    (hmeasC : ∀ i, Measurable fun w : (Vec d × ℝ) × CoefficientField d Λ =>
      commutatorNorm S w.2 w.1.1 w.1.2 i)
    (hmeasA : ∀ (z : Vec d) (r : ℝ) (ξ : Vec d), Measurable (fun a => gradientAverage S a z r ξ))
    {τ CN : ℝ} (hN : GaussianEnergyBound P S τ CN) (hτs : s ≤ τ / ((d : ℝ) / 2))
    (hint : AveragesIntegrable P S) : LinearAverageEstimate P S s α := by
  obtain ⟨C₁, hC₁, hb⟩ := gradient_sub_osBound hd S hΛ hs0 hα0 hC hH hmeasC hmeasA hN hτs hint
  refine ⟨(2 * (2 : ℝ) ^ s⁻¹) ^ d * C₁, by positivity, fun z r hr ξ => ?_⟩
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hsum := osBound_finset_sum_of_pos Finset.univ hs0
    (mul_pos hC₁ (Real.rpow_pos_of_pos hr0 _)) fun i _ => hb z r hr i
  rw [Finset.card_univ, Fintype.card_fin] at hsum
  have hξ : 0 < 1 + euclideanNorm ξ := by linarith [euclideanNorm_nonneg ξ]
  have hm : Measurable fun a => euclideanNorm (gradientAverage S a z r ξ - ξ) := by
    have hc' : Measurable fun a => gradientAverage S a z r ξ - ξ :=
      (hmeasA z r ξ).sub measurable_const
    simp only [euclideanNorm, euclideanSq, dot]
    exact (Finset.measurable_sum _ fun k _ =>
      ((measurable_pi_apply k).comp hc').mul ((measurable_pi_apply k).comp hc')).sqrt
  refine ((hsum.const_mul hξ).of_le_ae hm ?_).mono_scale (le_of_eq (by ring))
  filter_upwards [hint] with a ha
  have hlin := gradientAverage_eq_sum S a z r ξ fun i => (ha z r hr (unitVector i)).1
  have e : ∑ i, ξ i • (gradientAverage S a z r (unitVector i) - unitVector i) =
      (∑ i, ξ i • gradientAverage S a z r (unitVector i)) - ξ := by
    simp only [smul_sub, Finset.sum_sub_distrib, sum_smul_unitVector]
  rw [hlin, ← e]
  refine (euclideanNorm_finset_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [euclideanNorm_smul]
  refine mul_le_mul_of_nonneg_right ?_ (euclideanNorm_nonneg _)
  linarith [abs_apply_le_euclideanNorm ξ i]

end Heat

end QSH
