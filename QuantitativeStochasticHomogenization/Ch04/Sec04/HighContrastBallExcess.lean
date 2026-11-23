import QuantitativeStochasticHomogenization.Ch04.Sec04.AffineHighContrastTransport
import QuantitativeStochasticHomogenization.Ch04.Sec04.HighContrastExcessPackage
import QuantitativeStochasticHomogenization.Ch06.Sec01.CorrectorIdentification
import QuantitativeStochasticHomogenization.Ch06.Sec01.HighContrastDivCurl

/-!
# The excess decay of one slope on balls with an arbitrary center

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.21, the zoom from the intermediate scale to the scale `r` (consultant note S9,
step 3). Theorem C of Armstrong, Kuusi and Loher, *Homogenization at a polynomial scale in high
contrast*, gives for the dilated law, above the homogenization scale `X`, one slope `e` for every
solution on the ellipsoid `E_R` of the homogenized matrix with
`‖∇u - (e + ∇φ_e)‖_{E_ρ} ≤ C_ϑ (ρ/R)^ϑ ‖∇u‖_{E_R}` for `X ≤ ρ ≤ R`, in coefficient-weighted
normalized norms (`HighContrastExcessPackage`). This file transfers the clause to the balls
`B_t(z)` of an arbitrary center.

For `z` take the even lattice point `y = 2m` with `|z - y| ≤ 2d` and the translated dilated
coefficient `b' = T_m b`, `b'(x) = a(2x + y)`. An `a`-harmonic `v` on `B_{LR}(z)`, `L = 2Λ + 4`,
gives `u(x) = v(2x + y)/2` in `H¹_a(E_R)` (smooth approximation on a Euclidean ball containing
`E_R`, and the skew part of `b'` vanishes), solving the equation of `b'` on `E_R`. The bounds
`|ξ|² ≤ ξ · s̄ ξ ≤ Λ² |ξ|²` of the homogenized matrix give `B_ρ ⊆ E_ρ ⊆ B̄_{Λρ}`; the
weighted norms are comparable to normalized `L²` norms by ellipticity; the high-contrast
corrected gradients `e + ∇φ_e(b')` are `∑_j e_j W_j(2x + y)` by stationarity, linearity and the
identification of correctors. With `ρ = t/2 + d` this gives, for `max(2X, 2d) ≤ t ≤ R`,
`∫_{B_t(z)} |∇v - ∑_j e_j W_j|² ≤ C_ϑ² Λ (t/R)^{2ϑ + d} ∫_{B_{LR}(z)} |∇v|²`, and the
Gram lower bound of the corrected gradients bounds `|e|`. The result is `BallExcessDecay`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

open _root_.Homogenization hiding euclideanBall Vec Mat

open _root_.Homogenization.HighContrast

variable {d : ℕ}

/-! ## Matrix and ellipsoid bounds -/

theorem matVecMul_smul_one_eq (t : ℝ) (x : Vec d) : matVecMul (t • (1 : Mat d)) x = t • x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq, mul_comm]

theorem vecDot_smul_right_self (t : ℝ) (x : Vec d) : vecDot x (t • x) = t * vecNormSq x := by
  simp only [vecDot, vecNormSq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- From `|ξ|² ≤ ξ · S ξ ≤ K² |ξ|²` for a symmetric `S`: `x · S⁻¹ x ≤ |x|²`. -/
theorem vecDot_inv_le_vecNormSq {S : Mat d} (hS : S.PosDef)
    (hlow : ∀ e : Vec d, vecNormSq e ≤ vecDot e (matVecMul S e)) (x : Vec d) :
    vecDot x (matVecMul S⁻¹ x) ≤ vecNormSq x := by
  have hu : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit
  set e := matVecMul S⁻¹ x with he
  have hse : matVecMul S e = x := by
    rw [he, matVecMul_mul, Matrix.mul_nonsing_inv _ hu, _root_.Homogenization.matVecMul_one]
  have hq : vecDot x e = vecDot e (matVecMul S e) := by
    conv_lhs => rw [← hse]
    exact vecDot_comm _ _
  have hcs : vecDot x e ^ 2 ≤ vecNormSq e * vecNormSq x := by
    have h := dot_sq_le_euclideanSq_mul e x
    have e1 : vecDot x e = dot e x := by
      simp only [vecDot, dot]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1]
    exact h
  have hle : vecNormSq e ≤ vecDot x e := by rw [hq]; exact hlow e
  have hx0 : 0 ≤ vecNormSq x := vecNormSq_nonneg x
  have he0 : 0 ≤ vecNormSq e := vecNormSq_nonneg e
  show vecDot x e ≤ vecNormSq x
  rcases eq_or_lt_of_le (he0.trans hle) with h0 | hpos
  · rw [← h0]; exact hx0
  · have h1 : vecDot x e * vecDot x e ≤ vecDot x e * vecNormSq x := by
      calc vecDot x e * vecDot x e = vecDot x e ^ 2 := (sq _).symm
        _ ≤ vecNormSq e * vecNormSq x := hcs
        _ ≤ vecDot x e * vecNormSq x := mul_le_mul_of_nonneg_right hle hx0
    exact le_of_mul_le_mul_left h1 hpos

/-- **The ellipsoid lies in the Euclidean ball of radius `K R`** when
`|ξ|² ≤ ξ · s̄ ξ ≤ K² |ξ|²`. -/
theorem vecNormSq_le_of_mem_ellipsoid_of_bounds {abar : Mat d} {K : ℝ}
    (hpd : ∀ x : Vec d, x ≠ 0 → 0 < vecDot x (matVecMul (symmPart abar) x))
    (hb : ∀ e : Vec d, vecNormSq e ≤ vecDot e (matVecMul (symmPart abar) e) ∧
      vecDot e (matVecMul (symmPart abar) e) ≤ K ^ 2 * vecNormSq e)
    {R : ℝ} {x : Vec d} (hx : x ∈ ellipsoid abar R) : vecNormSq x ≤ K ^ 2 * R ^ 2 := by
  have hS : (symmPart abar).PosDef := posDef_symmPart_of_vecDot_pos hpd
  have h1 := vecNormSq_le_of_mem_ellipsoid hS hx
  have hsb : specBound (symmPart abar) ≤ K ^ 2 := by
    refine specBound_le (by positivity) fun x => ?_
    rw [matVecMul_smul_one_eq, vecDot_smul_right_self]
    linarith [(hb x).2]
  have hsbi : specBound ((symmPart abar)⁻¹) ≤ 1 := by
    refine specBound_le zero_le_one fun x => ?_
    rw [matVecMul_smul_one_eq, vecDot_smul_right_self, one_mul]
    linarith [vecDot_inv_le_vecNormSq hS (fun e => (hb e).1) x]
  have h0 := specBound_nonneg ((symmPart abar)⁻¹)
  have h0' := specBound_nonneg (symmPart abar)
  calc vecNormSq x ≤ specBound ((symmPart abar)⁻¹) * R ^ 2 * specBound (symmPart abar) := h1
    _ ≤ 1 * R ^ 2 * K ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hsbi (sq_nonneg R)) hsb h0' (by positivity)
    _ = K ^ 2 * R ^ 2 := by ring

theorem euclideanNorm_lt_of_vecNormSq_lt {x : Vec d} {r : ℝ} (hr : 0 ≤ r)
    (h : vecNormSq x < r ^ 2) : euclideanNorm x < r := by
  have h' : euclideanSq x < r ^ 2 := h
  have h0 := zero_le_euclideanSq x
  have hr0 : 0 < r := by
    rcases eq_or_lt_of_le hr with h1 | h1
    · rw [← h1] at h'
      norm_num at h'
      linarith
    · exact h1
  rw [euclideanNorm, Real.sqrt_lt' hr0]
  exact h'

theorem vecNormSq_lt_of_euclideanNorm_lt {x : Vec d} {r : ℝ} (h : euclideanNorm x < r) :
    vecNormSq x < r ^ 2 := by
  have h0 := zero_le_euclideanNorm x
  have : euclideanSq x = euclideanNorm x ^ 2 := by
    rw [euclideanNorm, Real.sq_sqrt (zero_le_euclideanSq x)]
  show euclideanSq x < r ^ 2
  rw [this]
  exact pow_lt_pow_left₀ h h0 two_ne_zero

/-! ## Weighted gradient norms and normalized `L²` norms -/

theorem weightedGradNorm_rpow_two (b : CoeffField d) (V : Set (Vec d)) (F : Vec d → Vec d) :
    weightedGradNorm b V F ^ (2 : ℝ) =
      eVolumeAverage V fun x =>
        ENNReal.ofReal (vecDot (F x) (matVecMul (symmPart (b x)) (F x))) := by
  rw [weightedGradNorm, ← ENNReal.rpow_mul]
  norm_num

theorem eVolumeAverage_ofReal_eq {V : Set (Vec d)} {f : Vec d → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hf : IntegrableOn f V) (hV0 : volume V ≠ 0) (hVt : volume V ≠ ⊤) :
    eVolumeAverage V (fun x => ENNReal.ofReal (f x)) =
      ENNReal.ofReal ((∫ x in V, f x) / volume.real V) := by
  rw [eVolumeAverage, ← ofReal_integral_eq_lintegral_ofReal hf
    (Eventually.of_forall fun x => hf0 x)]
  have hVr : 0 < volume.real V := ENNReal.toReal_pos hV0 hVt
  rw [ENNReal.ofReal_div_of_pos hVr, measureReal_def, ENNReal.ofReal_toReal hVt]

/-- **From the weighted excess inequality to integrals.** If
`‖F₁‖_{V₁} ≤ c ‖F₂‖_{V₂}` in coefficient-weighted normalized norms, with
`|F₁|² ≤ F₁ · s F₁` on `V₁` and `F₂ · s F₂ ≤ Λ |F₂|²` on `V₂`, then
`(∫_{V₁} |F₁|²) |V₂| ≤ c² Λ (∫_{V₂} |F₂|²) |V₁|`. -/
theorem integral_sq_mul_le_of_weightedGradNorm_le {b : CoeffField d} {V₁ V₂ : Set (Vec d)}
    {F₁ F₂ : Vec d → Vec d} {c Λ : ℝ} (hc : 0 ≤ c) (hΛ : 0 ≤ Λ)
    (h₁0 : volume V₁ ≠ 0) (h₁t : volume V₁ ≠ ⊤) (h₂0 : volume V₂ ≠ 0) (h₂t : volume V₂ ≠ ⊤)
    (hF₁ : IntegrableOn (fun x => euclideanSq (F₁ x)) V₁)
    (hF₂ : IntegrableOn (fun x => euclideanSq (F₂ x)) V₂)
    (hlow : ∀ᵐ x ∂volume.restrict V₁,
      euclideanSq (F₁ x) ≤ vecDot (F₁ x) (matVecMul (symmPart (b x)) (F₁ x)))
    (hup : ∀ᵐ x ∂volume.restrict V₂,
      vecDot (F₂ x) (matVecMul (symmPart (b x)) (F₂ x)) ≤ Λ * euclideanSq (F₂ x))
    (h : weightedGradNorm b V₁ F₁ ≤ ENNReal.ofReal c * weightedGradNorm b V₂ F₂) :
    (∫ x in V₁, euclideanSq (F₁ x)) * volume.real V₂ ≤
      c ^ 2 * Λ * (∫ x in V₂, euclideanSq (F₂ x)) * volume.real V₁ := by
  have h2 := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), weightedGradNorm_rpow_two,
    weightedGradNorm_rpow_two] at h2
  have hL : ENNReal.ofReal ((∫ x in V₁, euclideanSq (F₁ x)) / volume.real V₁) ≤
      eVolumeAverage V₁ fun x =>
        ENNReal.ofReal (vecDot (F₁ x) (matVecMul (symmPart (b x)) (F₁ x))) := by
    rw [← eVolumeAverage_ofReal_eq (fun x => zero_le_euclideanSq _) hF₁ h₁0 h₁t]
    refine ENNReal.div_le_div_right (lintegral_mono_ae ?_) _
    filter_upwards [hlow] with x hx
    exact ENNReal.ofReal_le_ofReal hx
  have hR : (eVolumeAverage V₂ fun x =>
      ENNReal.ofReal (vecDot (F₂ x) (matVecMul (symmPart (b x)) (F₂ x)))) ≤
      ENNReal.ofReal (Λ * ((∫ x in V₂, euclideanSq (F₂ x)) / volume.real V₂)) := by
    have hint : IntegrableOn (fun x => Λ * euclideanSq (F₂ x)) V₂ := hF₂.const_mul Λ
    rw [show Λ * ((∫ x in V₂, euclideanSq (F₂ x)) / volume.real V₂) =
      (∫ x in V₂, Λ * euclideanSq (F₂ x)) / volume.real V₂ by rw [integral_const_mul]; ring,
      ← eVolumeAverage_ofReal_eq (fun x => mul_nonneg hΛ (zero_le_euclideanSq _)) hint h₂0 h₂t]
    refine ENNReal.div_le_div_right (lintegral_mono_ae ?_) _
    filter_upwards [hup] with x hx
    exact ENNReal.ofReal_le_ofReal hx
  have hchain := hL.trans (h2.trans (mul_le_mul_of_nonneg_left hR zero_le))
  have hI₂ : 0 ≤ ∫ x in V₂, euclideanSq (F₂ x) :=
    integral_nonneg_of_ae (Eventually.of_forall fun x => zero_le_euclideanSq (F₂ x))
  rw [ENNReal.ofReal_rpow_of_nonneg hc (by norm_num),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hc _),
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.rpow_nonneg hc _)
      (mul_nonneg hΛ (div_nonneg hI₂ measureReal_nonneg)))] at hchain
  have hV₁ : 0 < volume.real V₁ := ENNReal.toReal_pos h₁0 h₁t
  have hV₂ : 0 < volume.real V₂ := ENNReal.toReal_pos h₂0 h₂t
  rw [div_le_iff₀ hV₁] at hchain
  rw [Real.rpow_two] at hchain
  have := mul_le_mul_of_nonneg_right hchain hV₂.le
  calc (∫ x in V₁, euclideanSq (F₁ x)) * volume.real V₂
      ≤ c ^ 2 * (Λ * ((∫ x in V₂, euclideanSq (F₂ x)) / volume.real V₂)) * volume.real V₁ *
          volume.real V₂ := this
    _ = c ^ 2 * Λ * (∫ x in V₂, euclideanSq (F₂ x)) * volume.real V₁ := by
        have hV₂' := hV₂.ne'
        field_simp

/-! ## Membership in `H¹_a` of the ellipsoid -/

theorem skewFluxDualNorm_eq_zero_of_ae {b : CoeffField d} {V : Set (Vec d)}
    (hb : ∀ᵐ x ∂volume.restrict V, skewPart (b x) = 0) (F : Vec d → Vec d) :
    skewFluxDualNorm b V F = 0 := by
  refine le_antisymm (iSup_le fun φ => le_of_eq ?_) zero_le
  have hzero : (fun x => vecDot (smoothGrad φ.1 x) (matVecMul (skewPart (b x)) (F x)))
      =ᵐ[volume.restrict V] fun _ => (0 : ℝ) := by
    filter_upwards [hb] with x hx
    rw [hx]
    simp [vecDot, matVecMul]
  have hI : IntegrableOn
      (fun x => vecDot (smoothGrad φ.1 x) (matVecMul (skewPart (b x)) (F x))) V volume :=
    (integrable_zero _ _ _).congr hzero.symm
  simp only [skewFluxPairing, hI, ↓reduceIte, integral_congr_ae hzero, integral_zero,
    ENNReal.ofReal_zero]

theorem skewPart_eq_zero_of_transpose_eq {B : Mat d} (h : B.transpose = B) : skewPart B = 0 := by
  funext i j
  have : B j i = B i j := by
    have := congrFun (congrFun h i) j
    simpa [Matrix.transpose_apply] using this
  simp [skewPart, this]

theorem symmPart_eq_of_transpose_eq {B : Mat d} (h : B.transpose = B) : symmPart B = B := by
  funext i j
  have : B j i = B i j := by
    have := congrFun (congrFun h i) j
    simpa [Matrix.transpose_apply] using this
  simp only [symmPart, this]
  ring

/-- **The transported solution lies in `H¹_a(V)`** for every measurable `V` inside a Euclidean
ball `U'` mapped by `x ↦ 2x + y` into the domain of `v`. -/
theorem memH1a_comp_two_smul_add {Λ : ℝ} (hΛ : 1 ≤ Λ) (a : CoefficientField d Λ) [NeZero d]
    {U V : Set (Vec d)} (hU : MeasurableSet U) {r' : ℝ} (hr' : 0 < r')
    (hVU' : V ⊆ euclideanBallAt (0 : Vec d) r') (y : Vec d)
    (hU'U : ∀ x ∈ euclideanBallAt (0 : Vec d) r', (2 : ℝ) • x + y ∈ U)
    {v : Vec d → ℝ} {g : Vec d → Vec d} (hv : MemLp v 2 (volume.restrict U))
    (hg : ∀ k, MemLp (fun x => g x k) 2 (volume.restrict U)) (hw : HasWeakGradient U v g)
    {b : CoeffField d} (hb : ∀ᵐ x ∂volume, b x = a.field ((2 : ℝ) • x + y)) :
    MemH1a b V (fun x => 2⁻¹ * v ((2 : ℝ) • x + y)) (fun x => g ((2 : ℝ) • x + y)) := by
  set U' := euclideanBallAt (0 : Vec d) r' with hU'def
  have hU'conv : IsOpenBoundedConvexDomain U' := isOpenBoundedConvexDomain_euclideanBallAt 0 hr'
  have hU'm : MeasurableSet U' := hU'conv.isOpen.measurableSet
  have hvU' : MemLp (fun x => 2⁻¹ * v ((2 : ℝ) • x + y)) 2 (volume.restrict U') :=
    (MemLp.comp_smul_add_restrict hU hU'm two_ne_zero y hU'U hv).const_mul _
  have hgU' : ∀ k, MemLp (fun x => g ((2 : ℝ) • x + y) k) 2 (volume.restrict U') := fun k =>
    MemLp.comp_smul_add_restrict hU hU'm two_ne_zero y hU'U (hg k)
  have hweakU' := hasWeakGradientOn_comp_smul_add two_pos y hU'U hw
  let u : H1Function U' := ⟨_, _, hvU', hgU', hweakU'⟩
  have hdpos' : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hball : Metric.closedBall (0 : Vec d) (r' / (2 * d)) ⊆ U' := by
    intro x hx
    have hx' : ‖x‖ ≤ r' / (2 * d) := by simpa using hx
    have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    have hcoord : ∀ i, x i ^ 2 ≤ (r' / (2 * d)) ^ 2 := fun i => by
      have h1 : |x i| ≤ r' / (2 * d) := by
        have := norm_le_pi_norm x i
        rw [Real.norm_eq_abs] at this
        linarith
      have h2 := abs_nonneg (x i)
      nlinarith [sq_abs (x i)]
    show vecNormSq (x - 0) < r' ^ 2
    rw [sub_zero]
    have hsum : vecNormSq x ≤ d * (r' / (2 * d)) ^ 2 := by
      calc vecNormSq x = ∑ i, x i ^ 2 := by
            simp only [vecNormSq, vecDot]; exact Finset.sum_congr rfl fun i _ => by ring
        _ ≤ ∑ _i : Fin d, (r' / (2 * d)) ^ 2 := Finset.sum_le_sum fun i _ => hcoord i
        _ = d * (r' / (2 * d)) ^ 2 := by simp
    have : (d : ℝ) * (r' / (2 * d)) ^ 2 < r' ^ 2 := by
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
      field_simp
      nlinarith [sq_pos_of_pos hr']
    linarith
  obtain ⟨w, hw', hlim⟩ :=
    exists_contDiff_tendsto_h1NormSqOnUnweighted_sub hU'conv u hball (div_pos hr' (by linarith))
  have hell : ∀ᵐ x ∂volume.restrict V, IsEllipticMatrix 1 Λ (b x) := by
    refine ae_restrict_of_ae ?_
    filter_upwards [hb] with x hx
    rw [hx]
    exact coefficientField_isEllipticMatrix a hΛ le_rfl _
  refine ⟨⟨(hvU'.mono_measure (Measure.restrict_mono hVU' le_rfl)).aestronglyMeasurable,
      fun i => ((hgU' i).mono_measure (Measure.restrict_mono hVU' le_rfl)).aestronglyMeasurable⟩,
    hasWeakGradientOn_comp_smul_add two_pos y (fun x hx => hU'U x (hVU' hx)) hw, w, hw', ?_, ?_⟩
  · rw [tendsto_h1sNormSqOn_sub_zero_iff_restrict (Lam := Λ) one_pos hell]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) (fun k => h1NormSqOnUnweighted_mono hVU' _ _)
  · have hskew : ∀ᵐ x ∂volume.restrict V, skewPart (b x) = 0 := by
      refine ae_restrict_of_ae ?_
      filter_upwards [hb] with x hx
      rw [hx]
      exact skewPart_eq_zero_of_transpose_eq (a.symmetric _)
    simp only [skewFluxDualNorm_eq_zero_of_ae hskew]
    exact tendsto_const_nhds

/-! ## The high-contrast corrected gradients -/

/-- The corrector gradients of the package are linear combinations of the coordinate ones. -/
theorem HighContrastExcessPackage.gradPhi_ae_eq_sum {K : ℝ} {hK : 1 ≤ K}
    {P : Measure (CoefficientField d K)} {κ C : ℝ} {C₁ : ℝ → ℝ}
    (pk : HighContrastExcessPackage hK P κ C C₁) (b : CoeffSpace d) (e : Vec d) :
    pk.gradPhi e b =ᵐ[volume] fun x => ∑ j, e j • pk.gradPhi (unitVector j) b x := by
  classical
  have hzero : pk.gradPhi 0 b =ᵐ[volume] fun _ => 0 := by
    have h := pk.linear (-1) 0 0 b
    simp only [smul_zero, add_zero] at h
    filter_upwards [h] with x hx
    rw [hx, neg_one_smul, neg_add_cancel]
  have hsum : ∀ s : Finset (Fin d), pk.gradPhi (∑ j ∈ s, e j • unitVector j) b =ᵐ[volume]
      fun x => ∑ j ∈ s, e j • pk.gradPhi (unitVector j) b x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert j s hj ih =>
      rw [Finset.sum_insert hj]
      filter_upwards [pk.linear (e j) (unitVector j) (∑ i ∈ s, e i • unitVector i) b, ih]
        with x hx1 hx2
      rw [hx1, hx2, Finset.sum_insert hj]
  have he : (∑ j, e j • unitVector j : Vec d) = e := by
    funext k
    simp [unitVector, Pi.single_apply]
  have h := hsum Finset.univ
  rwa [he] at h

theorem two_smul_add_intTranslation (m : Fin d → ℤ) (x : Vec d) :
    (2 : ℝ) • (x + Source.AKL.intTranslation m) = (2 : ℝ) • x + latticeShift (2 • m) := by
  funext i
  simp only [latticeShift, Source.AKL.intTranslation, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast [nsmul_eq_mul]
  ring

/-- **The corrected gradients of the translated dilated coefficient**: if the dilated gradients
`x ↦ G_j(2x)` are the high-contrast corrector gradients of `b`, then
`e + ∇φ_e(T_m b)(x) = ∑_j e_j (e_j + G_j(2x + 2m))`. -/
theorem HighContrastExcessPackage.ae_add_gradPhi_translateCoeff_eq {K : ℝ} {hK : 1 ≤ K}
    {P : Measure (CoefficientField d K)} {κ C : ℝ} {C₁ : ℝ → ℝ}
    (pk : HighContrastExcessPackage hK P κ C C₁) (b : CoeffSpace d) (m : Fin d → ℤ)
    (G : Fin d → Vec d → Vec d)
    (hid : ∀ j, dilatedGradient (G j) =ᵐ[volume] pk.gradPhi (unitVector j) b) (e : Vec d) :
    (fun x => e + pk.gradPhi e (translateCoeff m b) x) =ᵐ[volume]
      fun x => ∑ j, e j • (unitVector j + G j ((2 : ℝ) • x + latticeShift (2 • m))) := by
  have hT := (measurePreserving_add_right (volume : Measure (Vec d))
    (Source.AKL.intTranslation m)).quasiMeasurePreserving
  have h3 : ∀ j, (fun x => pk.gradPhi (unitVector j) b (x + Source.AKL.intTranslation m)) =ᵐ[volume]
      fun x => dilatedGradient (G j) (x + Source.AKL.intTranslation m) := fun j =>
    hT.ae_eq_comp (hid j).symm
  have he : (∑ j, e j • unitVector j : Vec d) = e := by
    funext k
    simp [unitVector, Pi.single_apply]
  filter_upwards [pk.gradPhi_ae_eq_sum (translateCoeff m b) e,
    ae_all_iff.2 fun j => pk.stationary m (unitVector j) b, ae_all_iff.2 h3]
    with x hx1 hx2 hx3
  rw [hx1]
  simp only [hx2, hx3, dilatedGradient, two_smul_add_intTranslation]
  simp only [smul_add, Finset.sum_add_distrib, he]

/-! ## Changes of variables on preimages -/

theorem measurable_two_smul_add (y : Vec d) : Measurable fun x : Vec d => (2 : ℝ) • x + y :=
  ((continuous_const_smul (2 : ℝ)).add continuous_const).measurable

theorem setIntegral_preimage_two_smul_add {S : Set (Vec d)} (hS : MeasurableSet S)
    (F : Vec d → ℝ) (y : Vec d) :
    ∫ x in (fun x => (2 : ℝ) • x + y) ⁻¹' S, F ((2 : ℝ) • x + y) =
      ((2 : ℝ) ^ d)⁻¹ * ∫ x in S, F x := by
  rw [← integral_indicator (hS.preimage (measurable_two_smul_add y)), ← integral_indicator hS]
  have h : (Set.indicator ((fun x => (2 : ℝ) • x + y) ⁻¹' S) fun x => F ((2 : ℝ) • x + y)) =
      fun x => Set.indicator S F ((2 : ℝ) • x + y) := by
    funext x
    exact Set.indicator_comp_right (fun x => (2 : ℝ) • x + y)
  rw [h, integral_comp_smul_add, abs_of_pos (by positivity)]

theorem integrableOn_euclideanSq_of_memLp {V : Set (Vec d)} {F : Vec d → Vec d}
    (hF : ∀ k, MemLp (fun x => F x k) 2 (volume.restrict V)) :
    IntegrableOn (fun x => euclideanSq (F x)) V :=
  (integrable_finsetSum Finset.univ fun k _ => (hF k).integrable_sq).congr
    (Eventually.of_forall fun x => by simp only [euclideanSq, dot, sq])

end QSH
