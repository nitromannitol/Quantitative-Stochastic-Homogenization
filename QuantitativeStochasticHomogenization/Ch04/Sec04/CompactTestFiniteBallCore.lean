import QuantitativeStochasticHomogenization.Ch04.Sec04.CompactTestScaleDerivative
import QuantitativeStochasticHomogenization.Ch04.Sec04.CompactTestTranslation
import QuantitativeStochasticHomogenization.Ch04.Sec04.CompactTestScaleIntegration
import QuantitativeStochasticHomogenization.Ch04.Sec04.FiniteBallObservationAbsorption

/-!
# The finite-ball estimate with compact tests (deterministic core)

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.21, through a finite-ball estimate with compact tests.

Let `F` be a family of first-order and skew flux correctors for the coefficient field `a` with
homogenized matrix `D`, centered at the origin, whose oscillations on `B_r`, `r ≥ R₀`, are at most
`C₁ r^{1-μ}`, and let `ρ`, `χ` be the compact profile and partner adapted to the symmetric part of
`D`. For `u` `a`-harmonic on `B_T` write `U_t = ρ_{λt} * u` and `M_t` for the root mean square of
`u` on `B_t`. Then:

* (3), first part: `|∂_t ∂^α U_t(x)| ≤ K C₁ t^{-|α|-1-μ} M_{4t}` for `|x| < t`, `R₀ ≤ 2t`, `4t ≤ T`
  (`abs_deriv_profileAverage_le`), from the scale identity and the tensor identity;
* (3), second part: `M_t(u - U_t) ≤ 32 √Λ 2^d λ M_{4t}` (`scalarRms_sub_profileAverage_le`), from
  the translation estimate and the Caccioppoli inequality.

Integrating the first bound from `s` outwards for the derivatives of order `j < n = ⌈k⌉` and from
`T/4` inwards for those of order `n`, the iterated mean value inequality bounds
`Y = sup_{s ≤ t ≤ T} (s/t)^k M_t` by
`(1/4 + C s^{-μ'}) Y + J_s + C (s/T)^k M_T` with `J_s = ∑_{j<n} s^j ∑_α |∂^α U_s(0)|`, for `λ` chosen
from `k`, `d` and `Λ`; above a threshold for `s` this gives `Y ≤ 2 J_s + C (s/T)^k M_T`, and the
observations `∂^α U_s(0)` are pairings of `u` with fixed multiples of the rescaled tests
`(∂^α ρ)(-·/λ)` (`compactTest_finiteBall_core`).
-/

open MeasureTheory Filter Set
open scoped ContDiff

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The averages `∂^α (ρ_{λt} * F)(x)`. -/
def profileAverage (ρ : Vec d → ℝ) (lam : ℝ) {j : ℕ} (α : Fin j → Fin d) (F : Vec d → ℝ)
    (t : ℝ) (x : Vec d) : ℝ :=
  kernelPairing (scaledKernel (d + j) (lam * t) (iterDeriv α ρ)) F x

variable {Λ μ C₁ R₀ : ℝ} {a : CoefficientField d Λ} {D : Mat d} {ρ χ : Vec d → ℝ}

theorem hasDerivAt_profileAverage (hd : 0 < d) (P : CompactProfilePair D ρ χ)
    {lam : ℝ} (hlam : 0 < lam) {j : ℕ} (α : Fin j → Fin d) {F : Vec d → ℝ} (hF : Integrable F)
    (x : Vec d) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => profileAverage ρ lam α F t x)
      (lam * (-((lam * t)⁻¹) ^ (d + j + 1) * kernelPairing
        (fun z => eulerOp (d + j) (iterDeriv α ρ) ((lam * t)⁻¹ • z)) F x)) t := by
  have hf := contDiff_iterDeriv α P.smooth_rho
  have hfc := hasCompactSupport_iterDeriv α P.hasCompactSupport_rho
  have h0 : ∀ m : ℕ, 1 ≤ m → HasDerivAt (fun t => kernelPairing (scaledKernel m (lam * t)
      (iterDeriv α ρ)) F x) (lam * (-((lam * t)⁻¹) ^ (m + 1) * kernelPairing
        (fun z => eulerOp m (iterDeriv α ρ) ((lam * t)⁻¹ • z)) F x)) t := by
    intro m hm
    obtain ⟨c, rfl⟩ : ∃ c, m = c + 1 := ⟨m - 1, by omega⟩
    have h1 := hasDerivAt_kernelPairing_scaledKernel hf hfc c hF x (mul_pos hlam ht)
    have h2 : HasDerivAt (fun t : ℝ => lam * t) lam t := by
      simpa using (hasDerivAt_id t).const_mul lam
    refine (h1.comp t h2).congr_deriv ?_
    ring
  exact h0 (d + j) (by omega)

/-- **The Caccioppoli inequality on `B_{2t} ⊂ B_{4t}`** in root form. -/
theorem sqrt_integral_grad_le_caccioppoli (hΛ : 1 ≤ Λ) {T t : ℝ} (ht : 0 < t) (hT : 4 * t ≤ T)
    (u : LocalHarmonic a 0 T) :
    Real.sqrt (∫ x in ball 0 (2 * t), euclideanSq (u.grad x)) ≤
      2 * Real.sqrt Λ * (16 / t) * Real.sqrt (∫ x in ball 0 (4 * t), u.potential x ^ 2) := by
  have hsub : ball (0 : Vec d) (4 * t) ⊆ ball 0 T := fun x hx => lt_of_lt_of_le hx hT
  have h := caccioppoli_ball hΛ a (z := 0) (r := 2 * t) (R := 4 * t) (by positivity) (by linarith)
    (memLp_mono_set u.square_integrable hsub) (fun i => memLp_mono_set (u.memLp_grad i) hsub)
    (hasWeakGradient_mono hsub u.weak_gradient) (u.harmonic.mono' hsub) 0
  simp only [sub_zero] at h
  have e : 4 * Λ * (32 / (4 * t - 2 * t)) ^ 2 = (2 * Real.sqrt Λ * (16 / t)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith)]
    field_simp
    ring
  rw [e] at h
  calc Real.sqrt (∫ x in ball 0 (2 * t), euclideanSq (u.grad x))
      ≤ Real.sqrt ((2 * Real.sqrt Λ * (16 / t)) ^ 2 * ∫ x in ball 0 (4 * t), u.potential x ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = 2 * Real.sqrt Λ * (16 / t) * Real.sqrt (∫ x in ball 0 (4 * t), u.potential x ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

/-- **The scale derivative of the compact averages**, explicit form. -/
theorem abs_deriv_profileAverage_le (F : SublinearCorrectorFamily a D μ C₁ R₀) (hΛ : 1 ≤ Λ)
    (hC₁ : 0 ≤ C₁) (P : CompactProfilePair D ρ χ) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    {j : ℕ} (α : Fin j → Fin d) {S₂ : ℝ} (hS₂0 : 0 ≤ S₂)
    (hS₂ : ∀ i l y, |coordinateDerivative l (coordinateDerivative i (iterDeriv α χ)) y| ≤ S₂)
    {T t : ℝ} (ht : 0 < t) (hR₀ : R₀ ≤ 2 * t) (hT : 4 * t ≤ T) (u : LocalHarmonic a 0 T)
    {x : Vec d} (hx : euclideanNorm x < t) :
    |lam * (-((lam * t)⁻¹) ^ (d + j + 1) * kernelPairing
        (fun z => eulerOp (d + j) (iterDeriv α ρ) ((lam * t)⁻¹ • z))
        ((ball 0 T).indicator u.potential) x)| ≤
      lam * ((lam * t)⁻¹) ^ (d + j + 1) * (S₂ * ((d ^ 3 + d ^ 2 * Real.sqrt d * Λ) *
        (Real.sqrt (volume.real (ball (0 : Vec d) (2 * t))) * (C₁ * (2 * t) ^ (1 - μ))) *
        (2 * Real.sqrt Λ * (16 / t) * Real.sqrt (∫ x in ball 0 (4 * t), u.potential x ^ 2)))) := by
  have hb : 0 < lam * t := mul_pos hlam0 ht
  have hx' : euclideanNorm x + lam * t / 2 < 2 * t := by nlinarith
  have hkp := abs_kernelPairing_eulerOp_le F hΛ hC₁ P α hS₂0 hS₂ hb (by positivity : (0 : ℝ) < 2 * t)
    hR₀ (by linarith) hx' u
  have hcac := sqrt_integral_grad_le_caccioppoli hΛ ht hT u
  have e : |lam * (-((lam * t)⁻¹) ^ (d + j + 1) * kernelPairing
      (fun z => eulerOp (d + j) (iterDeriv α ρ) ((lam * t)⁻¹ • z))
      ((ball 0 T).indicator u.potential) x)| = lam * ((lam * t)⁻¹) ^ (d + j + 1) *
        |kernelPairing (fun z => eulerOp (d + j) (iterDeriv α ρ) ((lam * t)⁻¹ • z))
          ((ball 0 T).indicator u.potential) x| := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos hlam0, abs_pow, abs_of_pos (inv_pos.2 hb)]
    ring
  rw [e]
  refine mul_le_mul_of_nonneg_left (hkp.trans ?_) (by positivity)
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcac ?_) hS₂0
  exact mul_nonneg (by positivity) (mul_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg hC₁ (Real.rpow_nonneg (by positivity) _)))

/-- The constant of the scale derivative bound for derivatives of order `j`. -/
def derivConst (d : ℕ) (Λ lam S₂ : ℝ) (j : ℕ) : ℝ :=
  64 * (lam⁻¹) ^ (d + j) * S₂ * (d ^ 3 + d ^ 2 * Real.sqrt d * Λ) * Real.sqrt Λ *
    Real.sqrt (8 ^ d) * volume.real (ball (0 : Vec d) 1)

theorem derivConst_nonneg {Λ lam S₂ : ℝ} (hΛ : 0 ≤ Λ) (hlam : 0 < lam) (hS₂ : 0 ≤ S₂) (j : ℕ) :
    0 ≤ derivConst d Λ lam S₂ j := by
  unfold derivConst
  have := measureReal_nonneg (μ := volume) (s := ball (0 : Vec d) 1)
  positivity

theorem sqrt_integral_sq_eq_mul_scalarRms {r : ℝ} (hr : 0 < r) (f : Vec d → ℝ) :
    Real.sqrt (∫ x in ball 0 r, f x ^ 2) =
      Real.sqrt (volume.real (ball (0 : Vec d) r)) * scalarRms volume (ball 0 r) f := by
  have hV := volume_real_ball_pos (0 : Vec d) hr
  unfold scalarRms
  rw [setAverage_eq, smul_eq_mul, ← Real.sqrt_mul hV.le, ← mul_assoc, mul_inv_cancel₀ hV.ne',
    one_mul]

/-- **The scale derivative bound** (3), first part:
`|∂_t ∂^α U_t(x)| ≤ K C₁ t^{-|α|-1-μ} M_{4t}` for `|x| < t`. -/
theorem abs_deriv_profileAverage_le_rpow (F : SublinearCorrectorFamily a D μ C₁ R₀)
    (hΛ : 1 ≤ Λ) (hμ : 0 ≤ μ) (hC₁ : 0 ≤ C₁) (P : CompactProfilePair D ρ χ) {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) {j : ℕ} (α : Fin j → Fin d) {S₂ : ℝ} (hS₂0 : 0 ≤ S₂)
    (hS₂ : ∀ i l y, |coordinateDerivative l (coordinateDerivative i (iterDeriv α χ)) y| ≤ S₂)
    {T t : ℝ} (ht : 1 ≤ t) (hR₀ : R₀ ≤ 2 * t) (hT : 4 * t ≤ T) (u : LocalHarmonic a 0 T)
    {x : Vec d} (hx : euclideanNorm x < t) :
    |lam * (-((lam * t)⁻¹) ^ (d + j + 1) * kernelPairing
        (fun z => eulerOp (d + j) (iterDeriv α ρ) ((lam * t)⁻¹ • z))
        ((ball 0 T).indicator u.potential) x)| ≤
      derivConst d Λ lam S₂ j * C₁ * t ^ (-((j : ℝ) + 1) - μ) *
        scalarRms volume (ball 0 (4 * t)) u.potential := by
  have ht0 : 0 < t := by linarith
  refine (abs_deriv_profileAverage_le F hΛ hC₁ P hlam0 hlam1 α hS₂0 hS₂ ht0 hR₀ hT u hx).trans
    (le_of_le_of_eq ?_ rfl)
  set M := scalarRms volume (ball 0 (4 * t)) u.potential with hM
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  set V₁ := volume.real (ball (0 : Vec d) 1) with hV₁
  have hV₁0 : 0 ≤ V₁ := measureReal_nonneg
  rw [sqrt_integral_sq_eq_mul_scalarRms (by positivity : (0 : ℝ) < 4 * t), ← hM]
  have hB2 : volume.real (ball (0 : Vec d) (2 * t)) = (2 * t) ^ d * V₁ :=
    volume_real_ball_eq_mul 0 (by positivity)
  have hB4 : volume.real (ball (0 : Vec d) (4 * t)) = (4 * t) ^ d * V₁ :=
    volume_real_ball_eq_mul 0 (by positivity)
  have hsq : Real.sqrt (volume.real (ball (0 : Vec d) (2 * t))) *
      Real.sqrt (volume.real (ball (0 : Vec d) (4 * t))) = Real.sqrt (8 ^ d) * t ^ d * V₁ := by
    rw [← Real.sqrt_mul (by rw [hB2]; positivity), hB2, hB4]
    have e : (2 * t) ^ d * V₁ * ((4 * t) ^ d * V₁) = 8 ^ d * (t ^ d * V₁) ^ 2 := by
      rw [mul_pow, mul_pow, show (8 : ℝ) ^ d = 2 ^ d * 4 ^ d by
        rw [← mul_pow]; norm_num]
      ring
    rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    ring
  have h2t : (2 * t) ^ (1 - μ) ≤ 2 * t ^ (1 - μ) := by
    rw [Real.mul_rpow (by norm_num) ht0.le]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg ht0.le _)
    calc (2 : ℝ) ^ (1 - μ) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have hpow : lam * ((lam * t)⁻¹) ^ (d + j + 1) * t ^ d * (16 / t) * t ^ (1 - μ) =
      16 * (lam⁻¹) ^ (d + j) * t ^ (-((j : ℝ) + 1) - μ) := by
    have e1 : t ^ (-((j : ℝ) + 1) - μ) = t ^ (1 - μ) * ((t⁻¹) ^ (j + 2)) := by
      rw [show -((j : ℝ) + 1) - μ = (1 - μ) + (-((j + 2 : ℕ) : ℝ)) by push_cast; ring,
        Real.rpow_add ht0, Real.rpow_neg ht0.le, Real.rpow_natCast, inv_pow]
    rw [e1, mul_inv, mul_pow]
    have hlam' : lam ≠ 0 := hlam0.ne'
    have ht' : t ≠ 0 := ht0.ne'
    simp only [inv_pow]
    field_simp
    ring
  calc lam * ((lam * t)⁻¹) ^ (d + j + 1) * (S₂ * ((d ^ 3 + d ^ 2 * Real.sqrt d * Λ) *
        (Real.sqrt (volume.real (ball (0 : Vec d) (2 * t))) * (C₁ * (2 * t) ^ (1 - μ))) *
        (2 * Real.sqrt Λ * (16 / t) * (Real.sqrt (volume.real (ball (0 : Vec d) (4 * t))) * M))))
      = (lam * ((lam * t)⁻¹) ^ (d + j + 1) * (16 / t)) *
          (Real.sqrt (volume.real (ball (0 : Vec d) (2 * t))) *
            Real.sqrt (volume.real (ball (0 : Vec d) (4 * t)))) *
          (2 * S₂ * (d ^ 3 + d ^ 2 * Real.sqrt d * Λ) * C₁ * Real.sqrt Λ * M) *
          (2 * t) ^ (1 - μ) := by ring
    _ ≤ (lam * ((lam * t)⁻¹) ^ (d + j + 1) * (16 / t)) * (Real.sqrt (8 ^ d) * t ^ d * V₁) *
          (2 * S₂ * (d ^ 3 + d ^ 2 * Real.sqrt d * Λ) * C₁ * Real.sqrt Λ * M) *
          (2 * t ^ (1 - μ)) := by
        rw [hsq]
        refine mul_le_mul_of_nonneg_left h2t ?_
        have := Real.sqrt_nonneg (8 ^ d)
        positivity
    _ = (lam * ((lam * t)⁻¹) ^ (d + j + 1) * t ^ d * (16 / t) * t ^ (1 - μ)) *
          (4 * Real.sqrt (8 ^ d) * V₁ * S₂ * (d ^ 3 + d ^ 2 * Real.sqrt d * Λ) * C₁ *
            Real.sqrt Λ * M) := by ring
    _ = (16 * (lam⁻¹) ^ (d + j) * t ^ (-((j : ℝ) + 1) - μ)) *
          (4 * Real.sqrt (8 ^ d) * V₁ * S₂ * (d ^ 3 + d ^ 2 * Real.sqrt d * Λ) * C₁ *
            Real.sqrt Λ * M) := by rw [hpow]
    _ = derivConst d Λ lam S₂ j * C₁ * t ^ (-((j : ℝ) + 1) - μ) * M := by
        rw [derivConst, ← hV₁]
        ring

theorem scalarRms_le_of_integral_sq_le {B : Set (Vec d)} (hB : 0 < volume.real B) {f : Vec d → ℝ}
    {c : ℝ} (hc : 0 ≤ c) (h : ∫ x in B, f x ^ 2 ≤ c ^ 2 * volume.real B) :
    scalarRms volume B f ≤ c := by
  unfold scalarRms
  rw [setAverage_eq, smul_eq_mul]
  calc Real.sqrt ((volume.real B)⁻¹ * ∫ x in B, f x ^ 2) ≤ Real.sqrt (c ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [inv_mul_le_iff₀ hB]
        linarith
    _ = c := Real.sqrt_sq hc

/-- The scaled kernel `ρ_b` is a probability density vanishing outside `B_b`. -/
theorem CompactProfilePair.scaledKernel_props (P : CompactProfilePair D ρ χ) {b : ℝ} (hb : 0 < b) :
    Continuous (scaledKernel d b ρ) ∧ (∀ z, 0 ≤ scaledKernel d b ρ z) ∧
      (∀ z, b ≤ euclideanNorm z → scaledKernel d b ρ z = 0) ∧ ∫ z, scaledKernel d b ρ z = 1 := by
  refine ⟨(contDiff_scaledKernel P.smooth_rho d b).continuous, fun z => ?_, fun z hz => ?_, ?_⟩
  · exact mul_nonneg (pow_nonneg (inv_nonneg.2 hb.le) _) (P.nonneg _)
  · unfold scaledKernel
    rw [P.vanish_rho _ ?_, mul_zero]
    rw [euclideanSq_smul_eq]
    have h1 : b ^ 2 ≤ euclideanSq z := by
      rw [← Real.sq_sqrt (zero_le_euclideanSq z)]
      exact pow_le_pow_left₀ hb.le hz 2
    have h2 : 1 ≤ (b⁻¹) ^ 2 * euclideanSq z := by
      rw [inv_pow, inv_mul_eq_div, le_div_iff₀ (by positivity)]
      linarith
    linarith
  · unfold scaledKernel
    rw [integral_const_mul, MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg _ _ hb.le,
      Module.finrank_fin_fun, P.integral_eq_one, smul_eq_mul, mul_one, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero _ hb.ne')]

/-- The average `U_t = ρ_{λt} * F`. -/
def profileSmooth (ρ : Vec d → ℝ) (lam : ℝ) (F : Vec d → ℝ) (t : ℝ) (x : Vec d) : ℝ :=
  kernelPairing (scaledKernel d (lam * t) ρ) F x

/-- **The translation bound** (3), second part: `M_t(u - U_t) ≤ 32 √Λ 2^d λ M_{4t}`. -/
theorem scalarRms_sub_profileSmooth_le (hΛ : 1 ≤ Λ) (P : CompactProfilePair D ρ χ) {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) {T t : ℝ} (ht : 0 < t) (hT : 4 * t ≤ T)
    (u : LocalHarmonic a 0 T) :
    scalarRms volume (ball 0 t) (fun x => u.potential x -
        profileSmooth ρ lam ((ball 0 T).indicator u.potential) t x) ≤
      32 * Real.sqrt Λ * 2 ^ d * lam * scalarRms volume (ball 0 (4 * t)) u.potential := by
  have hb : 0 < lam * t := mul_pos hlam0 ht
  obtain ⟨hκc, hκ0, hκs, hκ1⟩ := P.scaledKernel_props hb
  have htT : t + lam * t ≤ T := by nlinarith
  have h1 := integral_sq_sub_kernelPairing_le hb.le htT u.square_integrable u.memLp_grad
    u.weak_gradient hκc hκ0 hκs hκ1
  have hsub4 : ball (0 : Vec d) (4 * t) ⊆ ball 0 T := fun x hx => lt_of_lt_of_le hx hT
  have hcac := caccioppoli_ball hΛ a (z := 0) (r := 2 * t) (R := 4 * t) (by positivity)
    (by linarith) (memLp_mono_set u.square_integrable hsub4)
    (fun i => memLp_mono_set (u.memLp_grad i) hsub4) (hasWeakGradient_mono hsub4 u.weak_gradient)
    (u.harmonic.mono' hsub4) 0
  simp only [sub_zero] at hcac
  have hgint : IntegrableOn (fun x => euclideanSq (u.grad x)) (ball (0 : Vec d) (2 * t)) := by
    have hsub : ball (0 : Vec d) (2 * t) ⊆ ball 0 T := fun x (hx : x ∈ ball (0 : Vec d) (2 * t)) =>
      show euclideanNorm (x - 0) < T from lt_of_lt_of_le hx (by linarith)
    have := integrable_finsetSum (Finset.univ : Finset (Fin d)) fun i _ =>
      (memLp_mono_set (u.memLp_grad i) hsub).integrable_sq
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp [euclideanSq, dot, sq]
  have hmono : ∫ x in ball 0 (t + lam * t), euclideanSq (u.grad x) ≤
      ∫ x in ball 0 (2 * t), euclideanSq (u.grad x) :=
    setIntegral_mono_set hgint (Eventually.of_forall fun _ => zero_le_euclideanSq _)
      (Eventually.of_forall fun y (hy : y ∈ ball (0 : Vec d) (t + lam * t)) =>
        show euclideanNorm (y - 0) < 2 * t from lt_of_lt_of_le hy (by nlinarith))
  set M := scalarRms volume (ball 0 (4 * t)) u.potential with hM
  have hB4 : ∫ x in ball 0 (4 * t), u.potential x ^ 2 =
      volume.real (ball (0 : Vec d) (4 * t)) * M ^ 2 := by
    have := sqrt_integral_sq_eq_mul_scalarRms (by positivity : (0 : ℝ) < 4 * t) u.potential
    rw [← hM] at this
    have h0 : 0 ≤ ∫ x in ball 0 (4 * t), u.potential x ^ 2 := integral_nonneg fun _ => sq_nonneg _
    rw [← Real.sq_sqrt h0, this, mul_pow, Real.sq_sqrt measureReal_nonneg]
  have hV : volume.real (ball (0 : Vec d) (4 * t)) = 4 ^ d * volume.real (ball (0 : Vec d) t) := by
    rw [volume_real_ball_eq_mul 0 (by positivity), volume_real_ball_eq_mul 0 ht, mul_pow]
    ring
  refine scalarRms_le_of_integral_sq_le (volume_real_ball_pos 0 ht)
    (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) ?_
  unfold profileSmooth
  refine h1.trans ?_
  calc (lam * t) ^ 2 * ∫ x in ball 0 (t + lam * t), euclideanSq (u.grad x)
      ≤ (lam * t) ^ 2 * (4 * Λ * (32 / (4 * t - 2 * t)) ^ 2 *
          ∫ x in ball 0 (4 * t), u.potential x ^ 2) :=
        mul_le_mul_of_nonneg_left (hmono.trans hcac) (sq_nonneg _)
    _ = (32 * Real.sqrt Λ * 2 ^ d * lam * M) ^ 2 * volume.real (ball (0 : Vec d) t) := by
        have hsq : (32 * Real.sqrt Λ * 2 ^ d * lam * M) ^ 2 = 1024 * Λ * 4 ^ d * lam ^ 2 * M ^ 2 := by
          rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by linarith),
            show ((2 : ℝ) ^ d) ^ 2 = 4 ^ d by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
          ring
        rw [hB4, hV, hsq, show 4 * t - 2 * t = 2 * t by ring]
        have ht' : t ≠ 0 := ht.ne'
        field_simp
        ring

/-- **The majorant of the scale derivative** under the growth bound `M_r ≤ (r/s)^k Y` on
`[s, T]`: `|∂_t ∂^α U_t(x)| ≤ K C₁ 4^k s^{-k} Y t^{k-|α|-1-μ'}`. -/
theorem abs_deriv_profileAverage_le_majorant (F : SublinearCorrectorFamily a D μ C₁ R₀)
    (hΛ : 1 ≤ Λ) (hμ : 0 ≤ μ) (hC₁ : 0 ≤ C₁) (P : CompactProfilePair D ρ χ) {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) {j : ℕ} (α : Fin j → Fin d) {S₂ : ℝ} (hS₂0 : 0 ≤ S₂)
    (hS₂ : ∀ i l y, |coordinateDerivative l (coordinateDerivative i (iterDeriv α χ)) y| ≤ S₂)
    {k μ' s T : ℝ} (hμ' : μ' ≤ μ) (hs : 0 < s) {Y : ℝ}
    (u : LocalHarmonic a 0 T)
    (hY : ∀ r ∈ Set.Icc s T, scalarRms volume (ball 0 r) u.potential ≤ (r / s) ^ k * Y)
    {t : ℝ} (ht : 1 ≤ t) (hst : s ≤ 4 * t) (hR₀ : R₀ ≤ 2 * t) (hT : 4 * t ≤ T) {x : Vec d}
    (hx : euclideanNorm x < t) :
    |lam * (-((lam * t)⁻¹) ^ (d + j + 1) * kernelPairing
        (fun z => eulerOp (d + j) (iterDeriv α ρ) ((lam * t)⁻¹ • z))
        ((ball 0 T).indicator u.potential) x)| ≤
      derivConst d Λ lam S₂ j * C₁ * 4 ^ k * s ^ (-k) * Y * t ^ (k - j - μ' - 1) := by
  have ht0 : 0 < t := by linarith
  refine (abs_deriv_profileAverage_le_rpow F hΛ hμ hC₁ P hlam0 hlam1 α hS₂0 hS₂ ht hR₀ hT u
    hx).trans ?_
  have hK0 := derivConst_nonneg (d := d) (by linarith : (0 : ℝ) ≤ Λ) hlam0 hS₂0 j
  have hM := hY (4 * t) ⟨hst, hT⟩
  have hpow : t ^ (-((j : ℝ) + 1) - μ) ≤ t ^ (-((j : ℝ) + 1) - μ') :=
    Real.rpow_le_rpow_of_exponent_le ht (by linarith)
  have e : t ^ (-((j : ℝ) + 1) - μ') * ((4 * t / s) ^ k * Y) =
      4 ^ k * s ^ (-k) * Y * t ^ (k - j - μ' - 1) := by
    rw [Real.div_rpow (by positivity) hs.le, Real.mul_rpow (by norm_num) ht0.le,
      Real.rpow_neg hs.le]
    have e2 : t ^ (k - j - μ' - 1) = t ^ (-((j : ℝ) + 1) - μ') * t ^ k := by
      rw [← Real.rpow_add ht0]; congr 1; ring
    rw [e2]
    field_simp
  calc derivConst d Λ lam S₂ j * C₁ * t ^ (-((j : ℝ) + 1) - μ) *
        scalarRms volume (ball 0 (4 * t)) u.potential
      ≤ derivConst d Λ lam S₂ j * C₁ * t ^ (-((j : ℝ) + 1) - μ') * ((4 * t / s) ^ k * Y) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hpow (mul_nonneg hK0 hC₁)) hM
          (Real.sqrt_nonneg _) (by positivity)
    _ = derivConst d Λ lam S₂ j * C₁ * (t ^ (-((j : ℝ) + 1) - μ') * ((4 * t / s) ^ k * Y)) := by
        ring
    _ = derivConst d Λ lam S₂ j * C₁ * 4 ^ k * s ^ (-k) * Y * t ^ (k - j - μ' - 1) := by
        rw [e]; ring

theorem integrable_indicator_potential {T : ℝ} (u : LocalHarmonic a 0 T) :
    Integrable ((ball 0 T).indicator u.potential) :=
  (integrable_indicator_iff (measurableSet_ball _ _)).mpr
    (u.square_integrable.integrable one_le_two (μ := volume.restrict (ball 0 T)))

/-- `(s/t)^k t^j ≤ s^j` for `0 < s ≤ t` and `j ≤ k`. -/
theorem div_rpow_mul_pow_le {s t k : ℝ} (hs : 0 < s) (hst : s ≤ t) {j : ℕ} (hjk : (j : ℝ) ≤ k) :
    (s / t) ^ k * t ^ j ≤ s ^ j := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have e : (s / t) ^ k * t ^ j = (s / t) ^ (k - j) * s ^ j := by
    rw [show k = (k - j) + (j : ℝ) by ring, Real.rpow_add (div_pos hs ht), Real.rpow_natCast,
      div_pow]
    field_simp
    ring_nf
  rw [e]
  refine mul_le_of_le_one_left (pow_nonneg hs.le _) ?_
  exact Real.rpow_le_one (div_pos hs ht).le ((div_le_one ht).2 hst) (by linarith)

/-- `(s/t)^k t^j (s^{-k} t^{k-j-μ'}) = t^{-μ'} ≤ s^{-μ'}`. -/
theorem div_rpow_mul_pow_mul_rpow_le {s t k μ' : ℝ} (hs : 0 < s) (hst : s ≤ t) (hμ' : 0 ≤ μ')
    (j : ℕ) : (s / t) ^ k * t ^ j * (s ^ (-k) * t ^ (k - j - μ')) ≤ s ^ (-μ') := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have e : (s / t) ^ k * t ^ j * (s ^ (-k) * t ^ (k - j - μ')) = t ^ (-μ') := by
    rw [Real.div_rpow hs.le ht.le, ← Real.rpow_natCast t j]
    have h1 : t ^ (-μ') = t ^ (k - j - μ') * t ^ (j : ℝ) * (t ^ k)⁻¹ := by
      rw [← Real.rpow_neg ht.le, ← Real.rpow_add ht, ← Real.rpow_add ht]
      congr 1; ring
    rw [h1, Real.rpow_neg hs.le]
    have : 0 < s ^ k := Real.rpow_pos_of_pos hs k
    field_simp
  rw [e]
  exact Real.rpow_le_rpow_of_nonpos hs hst (by linarith)

/-- **Outward integration** of the derivatives of order `j < k` from `s` to `t`. -/
theorem outward_profileAverage_le (hd : 0 < d) (F : SublinearCorrectorFamily a D μ C₁ R₀)
    (hΛ : 1 ≤ Λ) (hμ : 0 ≤ μ) (hC₁ : 0 ≤ C₁) (P : CompactProfilePair D ρ χ) {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) {j : ℕ} (α : Fin j → Fin d) {S₂ : ℝ} (hS₂0 : 0 ≤ S₂)
    (hS₂ : ∀ i l y, |coordinateDerivative l (coordinateDerivative i (iterDeriv α χ)) y| ≤ S₂)
    {k μ' s T : ℝ} (hμ'0 : 0 ≤ μ') (hμ' : μ' ≤ μ) (hjk : (j : ℝ) + μ' < k)
    (hs1 : 1 ≤ s) (hR₀ : R₀ ≤ 2 * s) {Y : ℝ} (hY0 : 0 ≤ Y) (u : LocalHarmonic a 0 T)
    (hY : ∀ r ∈ Set.Icc s T, scalarRms volume (ball 0 r) u.potential ≤ (r / s) ^ k * Y)
    {t : ℝ} (hst : s ≤ t) (hT : 4 * t ≤ T) :
    (s / t) ^ k * t ^ j * |profileAverage ρ lam α ((ball 0 T).indicator u.potential) t 0| ≤
      s ^ j * |profileAverage ρ lam α ((ball 0 T).indicator u.potential) s 0| +
        derivConst d Λ lam S₂ j * C₁ * 4 ^ k * Y * s ^ (-μ') / (k - j - μ') := by
  have hs0 : 0 < s := by linarith
  set F₀ := (ball (0 : Vec d) T).indicator u.potential with hF₀
  have hF := integrable_indicator_potential u
  set e := k - j - μ' with he
  have he0 : 0 < e := by rw [he]; linarith
  have hK0 := derivConst_nonneg (d := d) (by linarith : (0 : ℝ) ≤ Λ) hlam0 hS₂0 j
  set Kc := derivConst d Λ lam S₂ j * C₁ * 4 ^ k * s ^ (-k) * Y with hKc
  have hKc0 : 0 ≤ Kc := by
    have := Real.rpow_nonneg hs0.le (-k)
    positivity
  have hmain := abs_sub_le_of_abs_deriv_le hst
    (f := fun t => profileAverage ρ lam α F₀ t 0)
    (g := fun t' => Kc * (t' ^ e / e)) (g' := fun t' => Kc * t' ^ (e - 1))
    (fun t' ht' => hasDerivAt_profileAverage hd P hlam0 α hF 0 (by linarith [ht'.1]))
    (fun t' ht' => (hasDerivAt_rpow_div he0.ne' (by linarith [ht'.1])).const_mul Kc)
    (fun t' ht' => by
      have h := abs_deriv_profileAverage_le_majorant F hΛ hμ hC₁ P hlam0 hlam1 α hS₂0 hS₂
        hμ' hs0 u hY (t := t') (by linarith [ht'.1]) (by linarith [ht'.1])
        (by linarith [ht'.1]) (by linarith [ht'.2]) (x := 0)
        (by simpa [euclideanNorm, euclideanSq, dot] using (by linarith [ht'.1] : (0 : ℝ) < t'))
      refine h.trans (le_of_eq ?_)
      rw [hKc, he])
  have hg0 : 0 ≤ Kc * (s ^ e / e) := mul_nonneg hKc0 (div_nonneg (Real.rpow_nonneg hs0.le _) he0.le)
  have hV : |profileAverage ρ lam α F₀ t 0| ≤
      |profileAverage ρ lam α F₀ s 0| + Kc * (t ^ e / e) := by
    have := abs_sub_abs_le_abs_sub (profileAverage ρ lam α F₀ t 0) (profileAverage ρ lam α F₀ s 0)
    linarith
  have h1 := div_rpow_mul_pow_le hs0 hst (j := j) (k := k) (by linarith)
  have h2 := div_rpow_mul_pow_mul_rpow_le hs0 hst hμ'0 j (k := k)
  have hst0 : 0 ≤ (s / t) ^ k * t ^ j := by
    have := Real.rpow_nonneg (div_pos hs0 (lt_of_lt_of_le hs0 hst)).le k
    have := pow_nonneg (lt_of_lt_of_le hs0 hst).le j
    positivity
  calc (s / t) ^ k * t ^ j * |profileAverage ρ lam α F₀ t 0|
      ≤ (s / t) ^ k * t ^ j * (|profileAverage ρ lam α F₀ s 0| + Kc * (t ^ e / e)) :=
        mul_le_mul_of_nonneg_left hV hst0
    _ = (s / t) ^ k * t ^ j * |profileAverage ρ lam α F₀ s 0| +
          derivConst d Λ lam S₂ j * C₁ * 4 ^ k * Y / e *
            ((s / t) ^ k * t ^ j * (s ^ (-k) * t ^ e)) := by
        rw [hKc]; ring
    _ ≤ s ^ j * |profileAverage ρ lam α F₀ s 0| +
          derivConst d Λ lam S₂ j * C₁ * 4 ^ k * Y / e * s ^ (-μ') := by
        refine add_le_add (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (by rw [he]; exact h2) (by positivity))
    _ = s ^ j * |profileAverage ρ lam α F₀ s 0| +
          derivConst d Λ lam S₂ j * C₁ * 4 ^ k * Y * s ^ (-μ') / (k - j - μ') := by
        rw [he]; ring

/-- `∫_{B_T} |u| ≤ |B_T| M_T`. -/
theorem integral_abs_indicator_le {T : ℝ} (hT : 0 < T) (u : LocalHarmonic a 0 T) :
    ∫ w, |(ball 0 T).indicator u.potential w| ≤
      volume.real (ball (0 : Vec d) T) * scalarRms volume (ball 0 T) u.potential := by
  have e : ∫ w, |(ball 0 T).indicator u.potential w| = ∫ w in ball 0 T, |u.potential w| := by
    rw [← integral_indicator (measurableSet_ball _ _)]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    by_cases hw : w ∈ ball (0 : Vec d) T <;> simp [hw]
  rw [e]
  have hCS := sq_setIntegral_abs_le (volume_ball_lt_top (0 : Vec d) T).ne u.square_integrable
  have h0 : 0 ≤ ∫ w in ball 0 T, |u.potential w| := integral_nonneg fun _ => abs_nonneg _
  have hV := volume_real_ball_pos (0 : Vec d) hT
  have hrms := sqrt_integral_sq_eq_mul_scalarRms hT u.potential
  have hI0 : 0 ≤ ∫ w in ball 0 T, u.potential w ^ 2 := integral_nonneg fun _ => sq_nonneg _
  calc ∫ w in ball 0 T, |u.potential w|
      = Real.sqrt ((∫ w in ball 0 T, |u.potential w|) ^ 2) := (Real.sqrt_sq h0).symm
    _ ≤ Real.sqrt (volume.real (ball (0 : Vec d) T) * ∫ w in ball 0 T, u.potential w ^ 2) :=
        Real.sqrt_le_sqrt hCS
    _ = Real.sqrt (volume.real (ball (0 : Vec d) T)) *
          Real.sqrt (∫ w in ball 0 T, u.potential w ^ 2) := Real.sqrt_mul hV.le _
    _ = volume.real (ball (0 : Vec d) T) * scalarRms volume (ball 0 T) u.potential := by
        rw [hrms, ← mul_assoc, Real.mul_self_sqrt hV.le]

/-- **Inward integration** of the derivatives of order `n ≥ k` from `T/4` to `t`, at a point of
`B_t`. -/
theorem inward_profileAverage_le (hd : 0 < d) (F : SublinearCorrectorFamily a D μ C₁ R₀)
    (hΛ : 1 ≤ Λ) (hμ : 0 ≤ μ) (hC₁ : 0 ≤ C₁) (P : CompactProfilePair D ρ χ) {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) {n : ℕ} (β : Fin n → Fin d) {S₂ Kρ : ℝ} (hS₂0 : 0 ≤ S₂)
    (hS₂ : ∀ i l y, |coordinateDerivative l (coordinateDerivative i (iterDeriv β χ)) y| ≤ S₂)
    (hKρ : ∀ y, |iterDeriv β ρ y| ≤ Kρ)
    {k μ' s T : ℝ} (hμ'0 : 0 < μ') (hμ' : μ' ≤ μ) (hnk : k ≤ n)
    (hs1 : 1 ≤ s) (hR₀ : R₀ ≤ 2 * s) {Y : ℝ} (hY0 : 0 ≤ Y) (u : LocalHarmonic a 0 T)
    (hY : ∀ r ∈ Set.Icc s T, scalarRms volume (ball 0 r) u.potential ≤ (r / s) ^ k * Y)
    {t : ℝ} (hst : s ≤ t) (hT : 4 * t ≤ T) {y : Vec d} (hy : euclideanNorm y < t) :
    (s / t) ^ k * t ^ n * |profileAverage ρ lam β ((ball 0 T).indicator u.potential) t y| ≤
      (s / T) ^ k * ((4 / lam) ^ (d + n) * Kρ * volume.real (ball (0 : Vec d) 1) *
        scalarRms volume (ball 0 T) u.potential) +
        derivConst d Λ lam S₂ n * C₁ * 4 ^ k * Y * s ^ (-μ') / (n - k + μ') := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hT0 : 0 < T := by linarith
  set F₀ := (ball (0 : Vec d) T).indicator u.potential with hF₀
  have hF := integrable_indicator_potential u
  set e := k - n - μ' with he
  have he0 : e < 0 := by rw [he]; linarith
  have hK0 := derivConst_nonneg (d := d) (by linarith : (0 : ℝ) ≤ Λ) hlam0 hS₂0 n
  set Kc := derivConst d Λ lam S₂ n * C₁ * 4 ^ k * s ^ (-k) * Y with hKc
  have hKc0 : 0 ≤ Kc := by
    have := Real.rpow_nonneg hs0.le (-k)
    positivity
  have htT4 : t ≤ T / 4 := by linarith
  have hmain := abs_sub_le_of_abs_deriv_le htT4
    (f := fun t => profileAverage ρ lam β F₀ t y)
    (g := fun t' => Kc * (t' ^ e / e)) (g' := fun t' => Kc * t' ^ (e - 1))
    (fun t' ht' => hasDerivAt_profileAverage hd P hlam0 β hF y (by linarith [ht'.1]))
    (fun t' ht' => (hasDerivAt_rpow_div he0.ne (by linarith [ht'.1])).const_mul Kc)
    (fun t' ht' => by
      have h := abs_deriv_profileAverage_le_majorant F hΛ hμ hC₁ P hlam0 hlam1 β hS₂0 hS₂
        hμ' hs0 u hY (t := t') (by linarith [ht'.1]) (by linarith [ht'.1])
        (by linarith [ht'.1]) (by linarith [ht'.2]) (lt_of_lt_of_le hy ht'.1)
      refine h.trans (le_of_eq ?_)
      rw [hKc, he])
  have hgT : Kc * ((T / 4) ^ e / e) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hKc0 (div_nonpos_of_nonneg_of_nonpos
      (Real.rpow_nonneg (by positivity) _) he0.le)
  -- the outer value
  have hout : |profileAverage ρ lam β F₀ (T / 4) y| ≤
      (4 / lam) ^ (d + n) * Kρ * volume.real (ball (0 : Vec d) 1) *
        scalarRms volume (ball 0 T) u.potential * (T⁻¹) ^ n := by
    have hb : 0 < lam * (T / 4) := by positivity
    have hKρ0 : 0 ≤ Kρ := (abs_nonneg _).trans (hKρ 0)
    have hker : ∀ z, |scaledKernel (d + n) (lam * (T / 4)) (iterDeriv β ρ) z| ≤
        ((lam * (T / 4))⁻¹) ^ (d + n) * Kρ := fun z => by
      unfold scaledKernel
      rw [abs_mul, abs_pow, abs_of_pos (inv_pos.2 hb)]
      exact mul_le_mul_of_nonneg_left (hKρ _) (by positivity)
    refine (abs_kernelPairing_le hF hker y).trans ?_
    have hI := integral_abs_indicator_le hT0 u
    rw [volume_real_ball_eq_mul 0 hT0] at hI
    calc ((lam * (T / 4))⁻¹) ^ (d + n) * Kρ * ∫ w, |F₀ w|
        ≤ ((lam * (T / 4))⁻¹) ^ (d + n) * Kρ * (T ^ d * volume.real (ball (0 : Vec d) 1) *
            scalarRms volume (ball 0 T) u.potential) :=
          mul_le_mul_of_nonneg_left hI (by positivity)
      _ = (4 / lam) ^ (d + n) * Kρ * volume.real (ball (0 : Vec d) 1) *
            scalarRms volume (ball 0 T) u.potential * (T⁻¹) ^ n := by
          have hlam' : lam ≠ 0 := hlam0.ne'
          have hT' : T ≠ 0 := hT0.ne'
          have e : (lam * (T / 4))⁻¹ = (4 / lam) * T⁻¹ := by field_simp
          have hTd : (T⁻¹) ^ d * T ^ d = 1 := by
            rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hT')]
          rw [e, mul_pow, pow_add (T⁻¹)]
          linear_combination ((4 / lam) ^ (d + n) * (T⁻¹) ^ n * Kρ *
            volume.real (ball (0 : Vec d) 1) * scalarRms volume (ball 0 T) u.potential) * hTd
  have hV : |profileAverage ρ lam β F₀ t y| ≤
      |profileAverage ρ lam β F₀ (T / 4) y| + Kc * (t ^ e / (-e)) := by
    have := abs_sub_abs_le_abs_sub (profileAverage ρ lam β F₀ t y)
      (profileAverage ρ lam β F₀ (T / 4) y)
    rw [abs_sub_comm] at this
    have e2 : Kc * (t ^ e / (-e)) = -(Kc * (t ^ e / e)) := by
      rw [div_neg, mul_neg]
    linarith
  have hst0 : 0 ≤ (s / t) ^ k * t ^ n := by
    have := Real.rpow_nonneg (div_pos hs0 ht0).le k
    positivity
  -- `(s/t)^k t^n T^{-n} ≤ (s/T)^k`
  have hfar : (s / t) ^ k * t ^ n * (T⁻¹) ^ n ≤ (s / T) ^ k := by
    have e1 : (s / t) ^ k * t ^ n * (T⁻¹) ^ n = (s / T) ^ k * (t / T) ^ ((n : ℝ) - k) := by
      rw [Real.div_rpow hs0.le ht0.le, Real.div_rpow hs0.le hT0.le,
        Real.div_rpow ht0.le hT0.le, Real.rpow_sub ht0, Real.rpow_sub hT0, Real.rpow_natCast,
        Real.rpow_natCast, inv_pow]
      have : 0 < t ^ k := Real.rpow_pos_of_pos ht0 k
      have : 0 < T ^ k := Real.rpow_pos_of_pos hT0 k
      have : 0 < T ^ n := pow_pos hT0 n
      field_simp
    rw [e1]
    refine mul_le_of_le_one_right (Real.rpow_nonneg (div_pos hs0 hT0).le _) ?_
    exact Real.rpow_le_one (div_pos ht0 hT0).le ((div_le_one hT0).2 (by linarith)) (by linarith)
  have h2 := div_rpow_mul_pow_mul_rpow_le hs0 hst hμ'0.le n (k := k)
  have hen : -e = n - k + μ' := by rw [he]; ring
  calc (s / t) ^ k * t ^ n * |profileAverage ρ lam β F₀ t y|
      ≤ (s / t) ^ k * t ^ n * (|profileAverage ρ lam β F₀ (T / 4) y| + Kc * (t ^ e / (-e))) :=
        mul_le_mul_of_nonneg_left hV hst0
    _ ≤ (s / t) ^ k * t ^ n * ((4 / lam) ^ (d + n) * Kρ * volume.real (ball (0 : Vec d) 1) *
          scalarRms volume (ball 0 T) u.potential * (T⁻¹) ^ n) +
          derivConst d Λ lam S₂ n * C₁ * 4 ^ k * Y / (-e) *
            ((s / t) ^ k * t ^ n * (s ^ (-k) * t ^ (k - n - μ'))) := by
        rw [mul_add]
        refine add_le_add (mul_le_mul_of_nonneg_left hout hst0) (le_of_eq ?_)
        rw [hKc, he]; ring
    _ ≤ (s / T) ^ k * ((4 / lam) ^ (d + n) * Kρ * volume.real (ball (0 : Vec d) 1) *
          scalarRms volume (ball 0 T) u.potential) +
          derivConst d Λ lam S₂ n * C₁ * 4 ^ k * Y / (-e) * s ^ (-μ') := by
        have hA0 : 0 ≤ (4 / lam) ^ (d + n) * Kρ * volume.real (ball (0 : Vec d) 1) *
            scalarRms volume (ball 0 T) u.potential := by
          have := (abs_nonneg _).trans (hKρ 0)
          have := measureReal_nonneg (μ := volume) (s := ball (0 : Vec d) 1)
          have := Real.sqrt_nonneg (⨍ x in ball 0 T, u.potential x ^ 2)
          positivity
        refine add_le_add ?_ (mul_le_mul_of_nonneg_left h2
          (div_nonneg (by positivity) (by linarith)))
        calc (s / t) ^ k * t ^ n * ((4 / lam) ^ (d + n) * Kρ *
              volume.real (ball (0 : Vec d) 1) * scalarRms volume (ball 0 T) u.potential *
              (T⁻¹) ^ n)
            = ((s / t) ^ k * t ^ n * (T⁻¹) ^ n) * ((4 / lam) ^ (d + n) * Kρ *
              volume.real (ball (0 : Vec d) 1) * scalarRms volume (ball 0 T) u.potential) := by
              ring
          _ ≤ (s / T) ^ k * ((4 / lam) ^ (d + n) * Kρ *
              volume.real (ball (0 : Vec d) 1) * scalarRms volume (ball 0 T) u.potential) :=
              mul_le_mul_of_nonneg_right hfar hA0
    _ = _ := by rw [hen]; ring

theorem iterDeriv_profileSmooth (P : CompactProfilePair D ρ χ) {lam t : ℝ} (hb : 0 < lam * t)
    {F : Vec d → ℝ} (hF : Integrable F) {j : ℕ} (α : Fin j → Fin d) :
    iterDeriv α (profileSmooth ρ lam F t) = profileAverage ρ lam α F t := by
  funext x
  unfold profileSmooth profileAverage
  rw [iterDeriv_kernelPairing α (contDiff_scaledKernel P.smooth_rho d _)
    (hasCompactSupport_scaledKernel P.hasCompactSupport_rho d hb.ne') hF.locallyIntegrable,
    iterDeriv_scaledKernel α P.smooth_rho]

theorem contDiff_profileSmooth (P : CompactProfilePair D ρ χ) {lam t : ℝ} (hb : 0 < lam * t)
    {F : Vec d → ℝ} (hF : Integrable F) : ContDiff ℝ ∞ (profileSmooth ρ lam F t) :=
  contDiff_kernelPairing (contDiff_scaledKernel P.smooth_rho d _)
    (hasCompactSupport_scaledKernel P.hasCompactSupport_rho d hb.ne') hF.locallyIntegrable

theorem integrableOn_ball_zero_of_continuous {f : Vec d → ℝ} (hf : Continuous f) (r : ℝ) :
    IntegrableOn f (ball (0 : Vec d) r) :=
  (hf.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Vec d) r)).mono_set fun x hx => by
    have hx' : euclideanNorm x < r := by simpa [ball] using hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact ((norm_le_euclideanNorm' x).trans hx'.le)

/-- The observation `J_s = ∑_{j<n} s^j ∑_α |∂^α U_s(0)|`. -/
def observationSum (ρ : Vec d → ℝ) (lam : ℝ) (n : ℕ) (F : Vec d → ℝ) (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, s ^ j * ∑ α : Fin j → Fin d, |profileAverage ρ lam α F s 0|

/-- The constant `C_A` of the scale integrals. -/
def scaleConst (d : ℕ) (Λ lam S₂ C₁ k μ' : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, (d : ℝ) ^ j * (derivConst d Λ lam S₂ j * C₁ * 4 ^ k / (k - j - μ')) +
    (d : ℝ) ^ n * (derivConst d Λ lam S₂ n * C₁ * 4 ^ k / (n - k + μ'))

/-- The constant `C_B` of the outer term. -/
def outerConst (d : ℕ) (lam Kρ : ℝ) (n : ℕ) : ℝ :=
  (d : ℝ) ^ n * ((4 / lam) ^ (d + n) * Kρ * volume.real (ball (0 : Vec d) 1))

theorem sum_const_fin_fun (j : ℕ) (c : ℝ) : ∑ _α : Fin j → Fin d, c = (d : ℝ) ^ j * c := by
  simp [Finset.sum_const, Finset.card_univ]

/-- **The Taylor bound for `U_t`**: for `s ≤ t`, `4t ≤ T`,
`(s/t)^k M_t(U_t) ≤ J_s + C_A s^{-μ'} Y + C_B (s/T)^k M_T`. -/
theorem scalarRms_profileSmooth_le (hd : 0 < d) (F : SublinearCorrectorFamily a D μ C₁ R₀)
    (hΛ : 1 ≤ Λ) (hμ : 0 ≤ μ) (hC₁ : 0 ≤ C₁) (P : CompactProfilePair D ρ χ) {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) {n : ℕ} {S₂ Kρ : ℝ} (hS₂0 : 0 ≤ S₂)
    (hS₂ : ∀ j ≤ n, ∀ (α : Fin j → Fin d) i l y,
      |coordinateDerivative l (coordinateDerivative i (iterDeriv α χ)) y| ≤ S₂)
    (hKρ : ∀ (β : Fin n → Fin d) y, |iterDeriv β ρ y| ≤ Kρ)
    {k μ' s T : ℝ} (hμ'0 : 0 < μ') (hμ' : μ' ≤ μ) (hnk : k ≤ n)
    (hnk' : (n : ℝ) - 1 + μ' < k)
    (hs1 : 1 ≤ s) (hR₀ : R₀ ≤ 2 * s) {Y : ℝ} (hY0 : 0 ≤ Y) (u : LocalHarmonic a 0 T)
    (hY : ∀ r ∈ Set.Icc s T, scalarRms volume (ball 0 r) u.potential ≤ (r / s) ^ k * Y)
    {t : ℝ} (hst : s ≤ t) (hT : 4 * t ≤ T) :
    (s / t) ^ k * scalarRms volume (ball 0 t)
        (profileSmooth ρ lam ((ball 0 T).indicator u.potential) t) ≤
      observationSum ρ lam n ((ball 0 T).indicator u.potential) s +
        scaleConst d Λ lam S₂ C₁ k μ' n * s ^ (-μ') * Y +
        outerConst d lam Kρ n * (s / T) ^ k * scalarRms volume (ball 0 T) u.potential := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  set F₀ := (ball (0 : Vec d) T).indicator u.potential with hF₀
  have hF := integrable_indicator_potential u
  have hb : 0 < lam * t := mul_pos hlam0 ht0
  set U := profileSmooth ρ lam F₀ t with hU
  set c := (s / t) ^ k with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos (div_pos hs0 ht0) k
  have htn0 : 0 < t ^ n := pow_pos ht0 n
  -- the bound of the top derivatives on `B_t`
  set Bn := (s / T) ^ k * ((4 / lam) ^ (d + n) * Kρ * volume.real (ball (0 : Vec d) 1) *
      scalarRms volume (ball 0 T) u.potential) +
      derivConst d Λ lam S₂ n * C₁ * 4 ^ k * Y * s ^ (-μ') / (n - k + μ') with hBn
  have htop : ∀ (β : Fin n → Fin d) (y : Vec d), euclideanNorm y < t →
      |iterDeriv β U y| ≤ Bn / (c * t ^ n) := fun β y hy => by
    rw [hU, iterDeriv_profileSmooth P hb hF β, le_div_iff₀ (mul_pos hc0 htn0), mul_comm]
    exact inward_profileAverage_le hd F hΛ hμ hC₁ P hlam0 hlam1 β hS₂0 (hS₂ n le_rfl β)
      (hKρ β) hμ'0 hμ' hnk hs1 hR₀ hY0 u hY hst hT hy
  -- the lower derivatives at the origin
  have hlow : ∀ j ∈ Finset.range n, c * (t ^ j * ∑ α : Fin j → Fin d, |iterDeriv α U 0|) ≤
      s ^ j * ∑ α : Fin j → Fin d, |profileAverage ρ lam α F₀ s 0| +
        (d : ℝ) ^ j * (derivConst d Λ lam S₂ j * C₁ * 4 ^ k / (k - j - μ')) * s ^ (-μ') * Y := by
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have hjk : (j : ℝ) + μ' < k := by
      have : (j : ℝ) ≤ n - 1 := by
        have : (j : ℝ) + 1 ≤ n := by exact_mod_cast hjn
        linarith
      linarith
    have hconv : ∀ α : Fin j → Fin d, iterDeriv α U 0 = profileAverage ρ lam α F₀ t 0 :=
      fun α => by rw [hU, iterDeriv_profileSmooth P hb hF α]
    simp only [hconv]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    have h := fun α : Fin j → Fin d => outward_profileAverage_le hd F hΛ hμ hC₁ P hlam0 hlam1 α
      hS₂0 (hS₂ j hjn.le α) hμ'0.le hμ' hjk hs1 hR₀ hY0 u hY hst hT
    calc ∑ α : Fin j → Fin d, c * (t ^ j * |profileAverage ρ lam α F₀ t 0|)
        ≤ ∑ α : Fin j → Fin d, (s ^ j * |profileAverage ρ lam α F₀ s 0| +
            derivConst d Λ lam S₂ j * C₁ * 4 ^ k * Y * s ^ (-μ') / (k - j - μ')) :=
          Finset.sum_le_sum fun α _ => by rw [← mul_assoc]; exact h α
      _ = _ := by
          rw [Finset.sum_add_distrib, sum_const_fin_fun]
          ring
  -- the Taylor bound at each point of `B_t`
  have hpt : ∀ x ∈ ball (0 : Vec d) t, c * |U x| ≤
      observationSum ρ lam n F₀ s + scaleConst d Λ lam S₂ C₁ k μ' n * s ^ (-μ') * Y +
        outerConst d lam Kρ n * (s / T) ^ k * scalarRms volume (ball 0 T) u.potential := by
    intro x hx
    have hx' : euclideanNorm x < t := by simpa [ball] using hx
    have hT1 := abs_le_of_iterDeriv_le (contDiff_profileSmooth P hb hF) n htop hx'
    have e1 : c * (t ^ n * ∑ _β : Fin n → Fin d, Bn / (c * t ^ n)) = (d : ℝ) ^ n * Bn := by
      rw [sum_const_fin_fun]
      field_simp
    calc c * |U x| ≤ c * (∑ j ∈ Finset.range n, t ^ j * ∑ α : Fin j → Fin d, |iterDeriv α U 0| +
          t ^ n * ∑ _β : Fin n → Fin d, Bn / (c * t ^ n)) := mul_le_mul_of_nonneg_left hT1 hc0.le
      _ = ∑ j ∈ Finset.range n, c * (t ^ j * ∑ α : Fin j → Fin d, |iterDeriv α U 0|) +
          (d : ℝ) ^ n * Bn := by rw [mul_add, Finset.mul_sum, e1]
      _ ≤ ∑ j ∈ Finset.range n, (s ^ j * ∑ α : Fin j → Fin d, |profileAverage ρ lam α F₀ s 0| +
            (d : ℝ) ^ j * (derivConst d Λ lam S₂ j * C₁ * 4 ^ k / (k - j - μ')) * s ^ (-μ') * Y) +
          (d : ℝ) ^ n * Bn := add_le_add_left (Finset.sum_le_sum hlow) _
      _ = _ := by
          rw [Finset.sum_add_distrib, hBn, observationSum, scaleConst, outerConst]
          have hs : ∑ j ∈ Finset.range n, (d : ℝ) ^ j * (derivConst d Λ lam S₂ j * C₁ * 4 ^ k /
              (k - j - μ')) * s ^ (-μ') * Y = (∑ j ∈ Finset.range n, (d : ℝ) ^ j *
                (derivConst d Λ lam S₂ j * C₁ * 4 ^ k / (k - j - μ'))) * s ^ (-μ') * Y := by
            rw [Finset.sum_mul, Finset.sum_mul]
          rw [hs]
          ring
  -- the root mean square
  set B := observationSum ρ lam n F₀ s + scaleConst d Λ lam S₂ C₁ k μ' n * s ^ (-μ') * Y +
      outerConst d lam Kρ n * (s / T) ^ k * scalarRms volume (ball 0 T) u.potential with hBdef
  have hB0 : 0 ≤ B := le_trans (mul_nonneg hc0.le (abs_nonneg _)) (hpt 0 (by
    simpa [ball, euclideanNorm, euclideanSq, dot] using ht0))
  have hrms : scalarRms volume (ball 0 t) U ≤ B / c := by
    refine scalarRms_le_of_integral_sq_le (volume_real_ball_pos 0 ht0) (div_nonneg hB0 hc0.le) ?_
    have hbd : ∀ x ∈ ball (0 : Vec d) t, U x ^ 2 ≤ (B / c) ^ 2 := fun x hx => by
      have h1 : |U x| ≤ B / c := by rw [le_div_iff₀ hc0, mul_comm]; exact hpt x hx
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    calc ∫ x in ball 0 t, U x ^ 2 ≤ ∫ x in ball (0 : Vec d) t, (B / c) ^ 2 :=
          setIntegral_mono_on (integrableOn_ball_zero_of_continuous
            ((contDiff_profileSmooth P hb hF).continuous.pow 2) t)
            (integrableOn_const (volume_ball_lt_top _ _).ne) (measurableSet_ball _ _) hbd
      _ = (B / c) ^ 2 * volume.real (ball (0 : Vec d) t) := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]
  calc c * scalarRms volume (ball 0 t) U ≤ c * (B / c) := mul_le_mul_of_nonneg_left hrms hc0.le
    _ = B := by field_simp

theorem scalarRms_ball_le_of_le {T t : ℝ} (ht : 0 < t) (htT : t ≤ T) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (ball 0 T))) :
    scalarRms volume (ball 0 t) f ≤ Real.sqrt ((T / t) ^ d) * scalarRms volume (ball 0 T) f := by
  have hT : 0 < T := lt_of_lt_of_le ht htT
  have hVt := volume_real_ball_pos (0 : Vec d) ht
  have hVT := volume_real_ball_pos (0 : Vec d) hT
  have hsub : ball (0 : Vec d) t ⊆ ball 0 T := fun x hx => lt_of_lt_of_le hx htT
  have hI : ∫ x in ball 0 t, f x ^ 2 ≤ ∫ x in ball 0 T, f x ^ 2 :=
    setIntegral_mono_set hf.integrable_sq (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall hsub)
  have hratio : volume.real (ball (0 : Vec d) T) = (T / t) ^ d * volume.real (ball (0 : Vec d) t) :=
    volume_real_ball_eq_rpow 0 ht hT |>.trans (by rw [Real.rpow_natCast])
  unfold scalarRms
  rw [← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul, hratio]
  have hq : 0 < (T / t) ^ d := by positivity
  calc (volume.real (ball (0 : Vec d) t))⁻¹ * ∫ x in ball 0 t, f x ^ 2
      ≤ (volume.real (ball (0 : Vec d) t))⁻¹ * ∫ x in ball 0 T, f x ^ 2 :=
        mul_le_mul_of_nonneg_left hI (inv_nonneg.2 hVt.le)
    _ = (T / t) ^ d * (((T / t) ^ d * volume.real (ball (0 : Vec d) t))⁻¹ *
          ∫ x in ball 0 T, f x ^ 2) := by
        field_simp

theorem memLp_two_ball_of_continuous {f : Vec d → ℝ} (hf : Continuous f) (r : ℝ) :
    MemLp f 2 (volume.restrict (ball (0 : Vec d) r)) :=
  (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
    (integrableOn_ball_zero_of_continuous (hf.pow 2) r)

/-- **The finite-ball estimate with compact tests**, deterministic core: under the absorption
conditions on `λ` and `s`, every `t ∈ [s, T]` has
`M_t ≤ 2 (t/s)^k (J_s + (C_B + 4^k 2^d) (s/T)^k M_T)`. -/
theorem compactTest_core (hd : 0 < d) (F : SublinearCorrectorFamily a D μ C₁ R₀)
    (hΛ : 1 ≤ Λ) (hμ : 0 ≤ μ) (hC₁ : 0 ≤ C₁) (P : CompactProfilePair D ρ χ) {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) {n : ℕ} {S₂ Kρ : ℝ} (hS₂0 : 0 ≤ S₂)
    (hS₂ : ∀ j ≤ n, ∀ (α : Fin j → Fin d) i l y,
      |coordinateDerivative l (coordinateDerivative i (iterDeriv α χ)) y| ≤ S₂)
    (hKρ : ∀ (β : Fin n → Fin d) y, |iterDeriv β ρ y| ≤ Kρ)
    {k μ' : ℝ} (hk : 0 ≤ k) (hμ'0 : 0 < μ') (hμ' : μ' ≤ μ) (hnk : k ≤ n)
    (hnk' : (n : ℝ) - 1 + μ' < k)
    (hlam : 32 * Real.sqrt Λ * 2 ^ d * lam * 4 ^ k ≤ 1 / 4)
    {s T : ℝ} (hs1 : 1 ≤ s) (hR₀ : R₀ ≤ 2 * s)
    (hsA : scaleConst d Λ lam S₂ C₁ k μ' n * s ^ (-μ') ≤ 1 / 4) (hsT : s ≤ T)
    (u : LocalHarmonic a 0 T) {t : ℝ} (hst : s ≤ t) (htT : t ≤ T) :
    scalarRms volume (ball 0 t) u.potential ≤ (t / s) ^ k * (2 *
      (observationSum ρ lam n ((ball 0 T).indicator u.potential) s +
        (outerConst d lam Kρ n + 4 ^ k * 2 ^ d) * (s / T) ^ k *
          scalarRms volume (ball 0 T) u.potential)) := by
  have hs0 : 0 < s := by linarith
  have hT0 : 0 < T := by linarith
  set F₀ := (ball (0 : Vec d) T).indicator u.potential with hF₀
  set M : ℝ → ℝ := fun r => scalarRms volume (ball 0 r) u.potential with hMdef
  have hM0 : ∀ r, 0 ≤ M r := fun r => Real.sqrt_nonneg _
  set B := observationSum ρ lam n F₀ s + (outerConst d lam Kρ n + 4 ^ k * 2 ^ d) * (s / T) ^ k *
    M T with hBdef
  set S := (fun r => (s / r) ^ k * M r) '' Set.Icc s T with hSdef
  have hSne : S.Nonempty := ⟨_, Set.mem_image_of_mem _ ⟨le_rfl, hsT⟩⟩
  have hSbdd : BddAbove S := by
    refine ⟨Real.sqrt ((T / s) ^ d) * M T, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    have hr0 : 0 < r := lt_of_lt_of_le hs0 hr.1
    have h1 : (s / r) ^ k ≤ 1 :=
      Real.rpow_le_one (div_pos hs0 hr0).le ((div_le_one hr0).2 hr.1) hk
    have h2 := scalarRms_ball_le_of_le hr0 hr.2 u.square_integrable
    have h3 : Real.sqrt ((T / r) ^ d) ≤ Real.sqrt ((T / s) ^ d) :=
      Real.sqrt_le_sqrt (pow_le_pow_left₀ (div_pos hT0 hr0).le
        (div_le_div_of_nonneg_left hT0.le hs0 hr.1) d)
    calc (s / r) ^ k * M r ≤ 1 * M r := mul_le_mul_of_nonneg_right h1 (hM0 r)
      _ = M r := one_mul _
      _ ≤ Real.sqrt ((T / r) ^ d) * M T := h2
      _ ≤ Real.sqrt ((T / s) ^ d) * M T := mul_le_mul_of_nonneg_right h3 (hM0 T)
  set Y := sSup S with hYdef
  have hYge : ∀ r ∈ Set.Icc s T, (s / r) ^ k * M r ≤ Y := fun r hr =>
    le_csSup hSbdd (Set.mem_image_of_mem _ hr)
  have hY0 : 0 ≤ Y := (mul_nonneg (Real.rpow_nonneg (div_pos hs0 hs0).le _) (hM0 s)).trans
    (hYge s ⟨le_rfl, hsT⟩)
  have hY : ∀ r ∈ Set.Icc s T, M r ≤ (r / s) ^ k * Y := fun r hr => by
    have hr0 : 0 < r := lt_of_lt_of_le hs0 hr.1
    have h := hYge r hr
    have e : (r / s) ^ k * (s / r) ^ k = 1 := by
      rw [← Real.mul_rpow (div_pos hr0 hs0).le (div_pos hs0 hr0).le,
        show r / s * (s / r) = 1 by field_simp, Real.one_rpow]
    calc M r = (r / s) ^ k * ((s / r) ^ k * M r) := by rw [← mul_assoc, e, one_mul]
      _ ≤ (r / s) ^ k * Y := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (div_pos hr0 hs0).le _)
  -- the bound at each scale
  have hstep : ∀ r ∈ Set.Icc s T, (s / r) ^ k * M r ≤ (1 / 2) * Y + B := by
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le hs0 hr.1
    have hc0 : 0 ≤ (s / r) ^ k := Real.rpow_nonneg (div_pos hs0 hr0).le _
    have hobs0 : 0 ≤ observationSum ρ lam n F₀ s :=
      Finset.sum_nonneg fun j _ => mul_nonneg (pow_nonneg hs0.le _)
        (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    have hout0 : 0 ≤ outerConst d lam Kρ n := by
      unfold outerConst
      have := (abs_nonneg _).trans (hKρ (fun _ => ⟨0, hd⟩) 0)
      have := measureReal_nonneg (μ := volume) (s := ball (0 : Vec d) 1)
      positivity
    have hsTk0 : 0 ≤ (s / T) ^ k := Real.rpow_nonneg (div_pos hs0 hT0).le _
    by_cases h4 : 4 * r ≤ T
    · have hb : 0 < lam * r := mul_pos hlam0 hr0
      set U := profileSmooth ρ lam F₀ r with hU
      have hUc : Continuous U := (contDiff_profileSmooth P hb (integrable_indicator_potential u)).continuous
      have htri : M r ≤ scalarRms volume (ball 0 r) (fun x => u.potential x - U x) +
          scalarRms volume (ball 0 r) U := by
        have h := scalarRms_add_le (f := fun x => u.potential x - U x) (g := U)
          ((memLp_mono_set u.square_integrable
          (fun x (hx : x ∈ ball (0 : Vec d) r) => lt_of_lt_of_le hx hr.2)).sub
            (memLp_two_ball_of_continuous hUc r)) (memLp_two_ball_of_continuous hUc r)
        have e : (fun x => u.potential x - U x + U x) = u.potential := funext fun x => by ring
        rw [e] at h
        exact h
      have h1 := scalarRms_sub_profileSmooth_le hΛ P hlam0 hlam1 hr0 h4 u
      have h2 := scalarRms_profileSmooth_le hd F hΛ hμ hC₁ P hlam0 hlam1 hS₂0 hS₂ hKρ hμ'0 hμ'
        hnk hnk' hs1 hR₀ hY0 u hY hr.1 h4
      have h4r : (s / r) ^ k * M (4 * r) ≤ 4 ^ k * Y := by
        have hM4 := hY (4 * r) ⟨by linarith [hr.1], h4⟩
        have e : (s / r) ^ k * (4 * r / s) ^ k = 4 ^ k := by
          rw [← Real.mul_rpow (div_pos hs0 hr0).le (by positivity)]
          congr 1
          field_simp
        calc (s / r) ^ k * M (4 * r) ≤ (s / r) ^ k * ((4 * r / s) ^ k * Y) :=
              mul_le_mul_of_nonneg_left hM4 hc0
          _ = 4 ^ k * Y := by rw [← mul_assoc, e]
      calc (s / r) ^ k * M r
          ≤ (s / r) ^ k * (32 * Real.sqrt Λ * 2 ^ d * lam * M (4 * r)) +
            (s / r) ^ k * scalarRms volume (ball 0 r) U := by
            rw [← mul_add]
            exact mul_le_mul_of_nonneg_left (htri.trans (add_le_add h1 le_rfl)) hc0
        _ ≤ 32 * Real.sqrt Λ * 2 ^ d * lam * (4 ^ k * Y) +
            (observationSum ρ lam n F₀ s + scaleConst d Λ lam S₂ C₁ k μ' n * s ^ (-μ') * Y +
              outerConst d lam Kρ n * (s / T) ^ k * M T) := by
            refine add_le_add ?_ h2
            calc (s / r) ^ k * (32 * Real.sqrt Λ * 2 ^ d * lam * M (4 * r))
                = 32 * Real.sqrt Λ * 2 ^ d * lam * ((s / r) ^ k * M (4 * r)) := by ring
              _ ≤ 32 * Real.sqrt Λ * 2 ^ d * lam * (4 ^ k * Y) :=
                  mul_le_mul_of_nonneg_left h4r (by positivity)
        _ ≤ (1 / 4) * Y + ((1 / 4) * Y + B) := by
            have hA : 32 * Real.sqrt Λ * 2 ^ d * lam * (4 ^ k * Y) ≤ (1 / 4) * Y := by
              rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hlam hY0
            have hBB : scaleConst d Λ lam S₂ C₁ k μ' n * s ^ (-μ') * Y ≤ (1 / 4) * Y :=
              mul_le_mul_of_nonneg_right hsA hY0
            have hC : outerConst d lam Kρ n * (s / T) ^ k * M T ≤
                (outerConst d lam Kρ n + 4 ^ k * 2 ^ d) * (s / T) ^ k * M T := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hsTk0) (hM0 T)
              have : (0 : ℝ) ≤ 4 ^ k * 2 ^ d := by positivity
              linarith
            rw [hBdef]
            linarith
        _ = (1 / 2) * Y + B := by ring
    · have h4' : T < 4 * r := not_le.mp h4
      have hMr : M r ≤ 2 ^ d * M T := by
        refine (scalarRms_ball_le_of_le hr0 hr.2 u.square_integrable).trans
          (mul_le_mul_of_nonneg_right ?_ (hM0 T))
        have h1 : (T / r) ^ d ≤ (4 : ℝ) ^ d :=
          pow_le_pow_left₀ (div_pos hT0 hr0).le ((div_le_iff₀ hr0).2 (by linarith)) d
        calc Real.sqrt ((T / r) ^ d) ≤ Real.sqrt (4 ^ d) := Real.sqrt_le_sqrt h1
          _ = 2 ^ d := by
            rw [show (4 : ℝ) ^ d = (2 ^ d) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
              Real.sqrt_sq (by positivity)]
      have hcr : (s / r) ^ k ≤ 4 ^ k * (s / T) ^ k := by
        rw [← Real.mul_rpow (by norm_num) (div_pos hs0 hT0).le]
        refine Real.rpow_le_rpow (div_pos hs0 hr0).le ?_ hk
        rw [div_le_iff₀ hr0, show 4 * (s / T) * r = 4 * s * r / T by ring, le_div_iff₀ hT0]
        nlinarith
      calc (s / r) ^ k * M r ≤ (4 ^ k * (s / T) ^ k) * (2 ^ d * M T) :=
            mul_le_mul hcr hMr (hM0 r) (by positivity)
        _ = 4 ^ k * 2 ^ d * (s / T) ^ k * M T := by ring
        _ ≤ B := by
            have hBe : B = observationSum ρ lam n F₀ s + outerConst d lam Kρ n * (s / T) ^ k * M T +
                4 ^ k * 2 ^ d * (s / T) ^ k * M T := by rw [hBdef]; ring
            have : 0 ≤ outerConst d lam Kρ n * (s / T) ^ k * M T :=
              mul_nonneg (mul_nonneg hout0 hsTk0) (hM0 T)
            linarith
        _ ≤ (1 / 2) * Y + B := by linarith
  have hYB : Y ≤ (1 / 2) * Y + B := csSup_le hSne (by
    rintro _ ⟨r, hr, rfl⟩
    exact hstep r hr)
  have hY2 : Y ≤ 2 * B := by linarith
  calc M t ≤ (t / s) ^ k * Y := hY t ⟨hst, htT⟩
    _ ≤ (t / s) ^ k * (2 * B) :=
        mul_le_mul_of_nonneg_left hY2 (Real.rpow_nonneg (div_pos (by linarith) hs0).le _)

end QSH
