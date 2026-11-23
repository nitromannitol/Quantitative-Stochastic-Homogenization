import QuantitativeStochasticHomogenization.Ch04.Sec04.SlopeLocalization
import QuantitativeStochasticHomogenization.Ch04.Sec05.GaussianMasses
import QuantitativeStochasticHomogenization.Ch04.Sec04.CorrectedGramLowerBound
import QuantitativeStochasticHomogenization.Ch04.Sec05.FluctuationPieces

/-!
# The finite-ball observation from an estimate with compact tests

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.21: the observation of a solution on the intermediate ball by its truncated
Gaussian averages (consultant notes SCOTT-localization, (D) and (4), and T22, (2)).

Let `u` be square integrable on `B_T(z)`, `S ≤ T`, and suppose that for every `t ∈ [S, T]`
`∫_{B_t(z)} u² ≤ G (t/S)^{2k} |B_t|` with
`G = C (∑_ℓ O_ℓ² + (S/T)^{2k} ⨍_{B_T(z)} u²)`, where `O_ℓ = |B_S|⁻¹ ∫_{B_T(z)} u ψ_ℓ((x - z)/S)` are
the pairings of `u` with finitely many Lipschitz tests `ψ_ℓ` supported in the unit ball. This is
the form of T22 (2), the tests being the derivatives of the compact profile at the inner scale.

Then `∫_{B_S(z)} u² ≤ C' (|B_S| I + (S/T)^{2k} ∫_{B_T(z)} u²)`, where `I` is the objective of the
coordinate minimization of Section 4.4, the truncated Gaussian observation at the scale `σ S` on
`B_{2S}(z)`, for every `σ ∈ (0, 1]` with `2 N C (L σ M)² ≤ 1/2`
(`integral_sq_ball_le_of_compactTests`). The proof is that of SCOTT-localization (4): the pairing
`O_ℓ` differs from the pairing of the Gaussian average of `1_{B_T} u` with `ψ_ℓ` by at most
`L σ M √G`, since a shift `x''` changes the rescaled test by at most `L |x''|/S` on
`B_{S + |x''|}(z)`, where `1_{B_T} u` has the growth of the hypothesis, and the Gaussian moments
of this bound are finite (`integral_heatKernel_mul_le_of_ball_growth_univ`); the pairing with the
Gaussian average is at most `L 2^{d/2} √I` by Cauchy–Schwarz; and the term `L σ M √G` is absorbed.

`CompactTestFiniteBall d Λ k` states the hypothesis above a random radius at every center for the
`a`-harmonic functions on `B_T(z)`, `T ≥ L₁ S`, with tests and constants chosen before the law; it
gives the finite-ball observation with `σ` chosen from the constants and `θ = 1/2`
(`finiteBallObservation_of_compactTests`).
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ}

/-! ## Tests supported in the unit ball -/

/-- A test profile on the unit ball: continuous, bounded by `L`, `L`-Lipschitz for the Euclidean
norm and zero outside the open unit ball. -/
structure IsUnitTest (ψ : Vec d → ℝ) (L : ℝ) : Prop where
  nonneg : 0 ≤ L
  continuous : Continuous ψ
  bound : ∀ x, |ψ x| ≤ L
  lipschitz : ∀ x y, |ψ x - ψ y| ≤ L * euclideanNorm (x - y)
  support : ∀ x, 1 ≤ euclideanNorm x → ψ x = 0

/-- The test `ψ` at the center `z` and the scale `S`: `x ↦ ψ((x - z)/S)`. -/
def scaledTest (ψ : Vec d → ℝ) (z : Vec d) (S : ℝ) (x : Vec d) : ℝ := ψ (S⁻¹ • (x - z))

namespace IsUnitTest

variable {ψ : Vec d → ℝ} {L : ℝ}

theorem continuous_scaled (h : IsUnitTest ψ L) (z : Vec d) (S : ℝ) :
    Continuous (scaledTest ψ z S) :=
  h.continuous.comp (by fun_prop)

theorem abs_scaled_le (h : IsUnitTest ψ L) (z : Vec d) (S : ℝ) (x : Vec d) :
    |scaledTest ψ z S x| ≤ L :=
  h.bound _

theorem scaled_eq_zero (h : IsUnitTest ψ L) {z : Vec d} {S : ℝ} (hS : 0 < S) {x : Vec d}
    (hx : x ∉ ball z S) : scaledTest ψ z S x = 0 := by
  apply h.support
  have hSx : S ≤ euclideanNorm (x - z) := not_lt.mp hx
  rw [euclideanNorm_smul_abs, abs_inv, abs_of_pos hS, le_inv_mul_iff₀ hS, mul_one]
  exact hSx

theorem abs_scaled_sub_le (h : IsUnitTest ψ L) {z : Vec d} {S : ℝ} (hS : 0 < S) (x y : Vec d) :
    |scaledTest ψ z S x - scaledTest ψ z S y| ≤ L / S * euclideanNorm (x - y) := by
  unfold scaledTest
  refine (h.lipschitz _ _).trans (le_of_eq ?_)
  rw [← smul_sub, sub_sub_sub_cancel_right, euclideanNorm_smul_abs, abs_inv, abs_of_pos hS]
  ring

end IsUnitTest

/-! ## Elementary bounds -/

/-- **Cauchy–Schwarz on a set of finite measure**: `(∫_s |f|)² ≤ |s| ∫_s f²`. -/
theorem sq_setIntegral_abs_le {s : Set (Vec d)} (hfin : volume s ≠ ⊤) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict s)) :
    (∫ x in s, |f x|) ^ 2 ≤ volume.real s * ∫ x in s, f x ^ 2 := by
  have : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.mpr hfin
  have hf1 : Integrable f (volume.restrict s) := hf.integrable one_le_two
  have hf2 : Integrable (fun x => f x ^ 2) (volume.restrict s) := hf.integrable_sq
  set I := ∫ x in s, |f x| with hI
  set J := ∫ x in s, f x ^ 2 with hJ
  set V := volume.real s with hV
  have hJ0 : 0 ≤ J := integral_nonneg fun x => sq_nonneg _
  rcases (measureReal_nonneg : 0 ≤ V).eq_or_lt with hV0 | hV0
  · have hz : volume.restrict s = 0 := by
      rw [Measure.restrict_eq_zero]
      have h0 : volume.real s = 0 := hV0.symm
      rwa [measureReal_eq_zero_iff hfin] at h0
    have hI0 : I = 0 := by rw [hI, hz, integral_zero_measure]
    rw [hI0, zero_pow two_ne_zero]
    exact mul_nonneg measureReal_nonneg hJ0
  · set m := I / V with hm
    have hexp : (fun x => (|f x| - m) ^ 2) = fun x => f x ^ 2 - 2 * m * |f x| + m ^ 2 := by
      funext x
      rw [sub_sq, sq_abs]
      ring
    have h0 : 0 ≤ ∫ x in s, (|f x| - m) ^ 2 := integral_nonneg fun x => sq_nonneg _
    have i1 : Integrable (fun x => f x ^ 2 - 2 * m * |f x|) (volume.restrict s) :=
      hf2.sub (hf1.abs.const_mul _)
    have e1 := integral_add (μ := volume.restrict s) i1 (integrable_const (m ^ 2))
    have e2 := integral_sub (μ := volume.restrict s) hf2 (hf1.abs.const_mul (2 * m))
    rw [hexp, e1, e2, integral_const_mul, setIntegral_const, smul_eq_mul] at h0
    have e : J - 2 * m * I + V * m ^ 2 = J - I ^ 2 / V := by
      rw [hm]
      field_simp
      ring
    rw [e] at h0
    have h1 : I ^ 2 / V ≤ J := by linarith
    rw [div_le_iff₀ hV0] at h1
    linarith

/-- The real volume of a ball as a power of the radius ratio. -/
theorem volume_real_ball_eq_rpow (z : Vec d) {S R : ℝ} (hS : 0 < S) (hR : 0 < R) :
    volume.real (ball z R) = (R / S) ^ (d : ℝ) * volume.real (ball z S) := by
  rw [volume_real_ball_eq_mul z hR, volume_real_ball_eq_mul z hS, Real.rpow_natCast, div_pow]
  field_simp

/-! ## The growth of the zero extension -/

section Growth

variable {z : Vec d} {S T k G : ℝ} {u : Vec d → ℝ}

theorem indicator_sq (s : Set (Vec d)) (u : Vec d → ℝ) (x : Vec d) :
    s.indicator u x ^ 2 = s.indicator (fun y => u y ^ 2) x := by
  by_cases hx : x ∈ s
  · simp [hx]
  · simp [hx]

/-- The zero extension of `u` keeps the growth of the hypothesis at every radius `R ≥ S`. -/
theorem setIntegral_indicator_sq_le (hS : 0 < S) (hST : S ≤ T) (hk : 0 ≤ k) (hG : 0 ≤ G)
    (hyp : ∀ t : ℝ, S ≤ t → t ≤ T →
      ∫ x in ball z t, u x ^ 2 ≤ G * ((t / S) ^ (2 * k) * volume.real (ball z t)))
    {R : ℝ} (hR : S ≤ R) :
    ∫ x in ball z R, (ball z T).indicator u x ^ 2 ≤
      G * ((R / S) ^ (2 * k) * volume.real (ball z R)) := by
  simp_rw [indicator_sq]
  rw [setIntegral_indicator (measurableSet_ball z T)]
  rcases le_total R T with hRT | hRT
  · have hsub : ball z R ∩ ball z T = ball z R :=
      Set.inter_eq_left.mpr fun x hx => lt_of_lt_of_le hx hRT
    rw [hsub]
    exact hyp R hR hRT
  · have hsub : ball z R ∩ ball z T = ball z T :=
      Set.inter_eq_right.mpr fun x hx => lt_of_lt_of_le hx hRT
    rw [hsub]
    refine (hyp T hST le_rfl).trans (mul_le_mul_of_nonneg_left ?_ hG)
    have hT0 : 0 < T := hS.trans_le hST
    refine mul_le_mul (Real.rpow_le_rpow (div_pos hT0 hS).le
      (div_le_div_of_nonneg_right hRT hS.le) (by linarith))
      (measureReal_mono (fun x hx => lt_of_lt_of_le hx hRT) (volume_ball_lt_top z R).ne)
      measureReal_nonneg (Real.rpow_nonneg (div_pos (hS.trans_le hR) hS).le _)

end Growth

/-! ## The Gaussian average of a rescaled test -/

section Pairing

variable {ψ : Vec d → ℝ} {L : ℝ}

/-- **The pairing with the Gaussian average** of `F` is the pairing of `F` with the Gaussian
average of the rescaled test (Fubini's theorem and translation). -/
theorem integral_scaledTest_mul_heat (hψ : IsUnitTest ψ L) (z : Vec d) (S : ℝ) {ρ : ℝ}
    (hρ : 0 < ρ) {F : Vec d → ℝ} (hF : Integrable F) :
    ∫ y, scaledTest ψ z S y * ∫ x, heatKernel y ρ x * F x =
      ∫ x, F x * ∫ x'', heatKernel 0 ρ x'' * scaledTest ψ z S (x - x'') := by
  set f : Vec d → Vec d → ℝ := fun y x => scaledTest ψ z S y * (heatKernel y ρ x * F x) with hf
  have hKF : AEStronglyMeasurable (fun p : Vec d × Vec d => heatKernel p.1 ρ p.2 * F p.2)
      (volume.prod volume) :=
    (continuous_heatKernel ρ).aestronglyMeasurable.mul hF.aestronglyMeasurable.comp_snd
  have hm : AEStronglyMeasurable (Function.uncurry f) (volume.prod volume) :=
    ((hψ.continuous_scaled z S).comp continuous_fst).aestronglyMeasurable.mul hKF
  have hint : Integrable (Function.uncurry f) (volume.prod volume) := by
    refine (integrable_prod_iff' hm).mpr ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · have h1 : Integrable (fun y => heatKernel y ρ x * F x) :=
        (integrable_heatKernel_center x hρ).mul_const _
      refine Integrable.mono' (h1.norm.const_mul L)
        (((hψ.continuous_scaled z S).aestronglyMeasurable).mul h1.aestronglyMeasurable)
        (Eventually.of_forall fun y => ?_)
      simp only [hf, Function.uncurry_apply_pair, norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hψ.abs_scaled_le z S y)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    · refine Integrable.mono' (hF.norm.const_mul L) hm.norm.prod_swap.integral_prod_right'
        (Eventually.of_forall fun x => ?_)
      have h1 : Integrable (fun y => heatKernel y ρ x * F x) :=
        (integrable_heatKernel_center x hρ).mul_const _
      have hle : ∫ y, ‖Function.uncurry f (y, x)‖ ≤ ∫ y, L * (heatKernel y ρ x * ‖F x‖) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _)
          (((integrable_heatKernel_center x hρ).mul_const _).const_mul L)
          (Eventually.of_forall fun y => ?_)
        simp only [hf, Function.uncurry_apply_pair, norm_mul, Real.norm_eq_abs]
        rw [abs_of_nonneg (heatKernel_nonneg y ρ x)]
        exact mul_le_mul_of_nonneg_right (hψ.abs_scaled_le z S y)
          (mul_nonneg (heatKernel_nonneg y ρ x) (abs_nonneg _))
      have hK : ∫ y, L * (heatKernel y ρ x * ‖F x‖) = L * ‖F x‖ := by
        rw [integral_const_mul, integral_mul_const, integral_heatKernel_center x hρ, one_mul]
      rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
      simpa only [Function.comp_apply, Prod.swap_prod_mk] using hle.trans hK.le
  have hL : ∫ y, scaledTest ψ z S y * ∫ x, heatKernel y ρ x * F x = ∫ y, ∫ x, f y x := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hf]
    rw [integral_const_mul]
  rw [hL, integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hf]
  have e1 : (fun y => scaledTest ψ z S y * (heatKernel y ρ x * F x)) =
      fun y => (scaledTest ψ z S y * heatKernel y ρ x) * F x := by
    funext y; ring
  rw [e1, integral_mul_const, mul_comm]
  congr 1
  rw [← integral_sub_left_eq_self (fun y => scaledTest ψ z S y * heatKernel y ρ x) volume x]
  refine integral_congr_ae (Eventually.of_forall fun x'' => ?_)
  simp only [heatKernel, sub_sub_cancel, sub_zero]
  ring

/-- **The difference of the pairing with `F` and with its Gaussian average** is controlled by the
Gaussian average of the pairings of `|F|` with the differences of the rescaled test and its
shifts. -/
theorem abs_pairing_sub_smoothed_le (hψ : IsUnitTest ψ L) (z : Vec d) {S : ℝ} {ρ : ℝ}
    (hρ : 0 < ρ) {F : Vec d → ℝ} (hF : Integrable F) :
    |(∫ x, F x * scaledTest ψ z S x) - ∫ y, scaledTest ψ z S y * ∫ x, heatKernel y ρ x * F x| ≤
      ∫ x'', heatKernel 0 ρ x'' *
        ∫ x, |F x| * |scaledTest ψ z S x - scaledTest ψ z S (x - x'')| := by
  rw [integral_scaledTest_mul_heat hψ z S hρ hF]
  have hE := integrable_heatKernel (0 : Vec d) hρ
  have hcs := hψ.continuous_scaled z S
  -- the integrand on the product space
  set g : Vec d × Vec d → ℝ := fun p =>
    |F p.1| * (heatKernel 0 ρ p.2 * |scaledTest ψ z S p.1 - scaledTest ψ z S (p.1 - p.2)|)
    with hg
  have hΔc : Continuous fun p : Vec d × Vec d =>
      |scaledTest ψ z S p.1 - scaledTest ψ z S (p.1 - p.2)| :=
    ((hcs.comp continuous_fst).sub (hcs.comp (continuous_fst.sub continuous_snd))).abs
  have hgm : AEStronglyMeasurable g (volume.prod volume) :=
    hF.aestronglyMeasurable.comp_fst.norm.mul
      (((continuous_heatKernel_right (0 : Vec d) ρ).comp continuous_snd).mul
        hΔc).aestronglyMeasurable
  have hgi : Integrable g (volume.prod volume) := by
    refine Integrable.mono' ((hF.norm.mul_prod hE).const_mul (2 * L)) hgm
      (Eventually.of_forall fun p => ?_)
    have hΔ : |scaledTest ψ z S p.1 - scaledTest ψ z S (p.1 - p.2)| ≤ 2 * L := by
      have h1 := hψ.abs_scaled_le z S p.1
      have h2 := hψ.abs_scaled_le z S (p.1 - p.2)
      exact (abs_sub _ _).trans (by linarith)
    have hK := heatKernel_nonneg (0 : Vec d) ρ p.2
    simp only [hg, norm_mul, Real.norm_eq_abs, abs_abs, abs_of_nonneg hK]
    calc |F p.1| * (heatKernel 0 ρ p.2 * |scaledTest ψ z S p.1 - scaledTest ψ z S (p.1 - p.2)|)
        ≤ |F p.1| * (heatKernel 0 ρ p.2 * (2 * L)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΔ hK) (abs_nonneg _)
      _ = 2 * L * (‖F p.1‖ * heatKernel 0 ρ p.2) := by rw [Real.norm_eq_abs]; ring
  have hshift : ∀ x, scaledTest ψ z S x =
      ∫ x'' : Vec d, heatKernel 0 ρ x'' * scaledTest ψ z S x := fun x => by
    rw [integral_mul_const, integral_heatKernel 0 hρ, one_mul]
  have hdiff : ∀ x, F x * scaledTest ψ z S x - F x * ∫ x'', heatKernel 0 ρ x'' *
      scaledTest ψ z S (x - x'') = F x * ∫ x'', heatKernel 0 ρ x'' *
        (scaledTest ψ z S x - scaledTest ψ z S (x - x'')) := fun x => by
    rw [← mul_sub]
    congr 1
    conv_lhs => rw [hshift x]
    rw [← integral_sub (hE.mul_const _)]
    · refine integral_congr_ae (Eventually.of_forall fun x'' => ?_)
      ring
    · refine Integrable.mono' (hE.const_mul L)
        (hE.aestronglyMeasurable.mul
          (hcs.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
        (Eventually.of_forall fun x'' => ?_)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (heatKernel_nonneg (0 : Vec d) ρ x''), mul_comm L]
      exact mul_le_mul_of_nonneg_left (hψ.abs_scaled_le z S _) (heatKernel_nonneg _ _ _)
  have hi1 : Integrable fun x => F x * scaledTest ψ z S x :=
    Integrable.mono' (hF.norm.mul_const L) (hF.aestronglyMeasurable.mul hcs.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hψ.abs_scaled_le z S x) (abs_nonneg _))
  have hi2 : Integrable fun x => F x * ∫ x'', heatKernel 0 ρ x'' * scaledTest ψ z S (x - x'') := by
    refine Integrable.mono' (hF.norm.mul_const L) (hF.aestronglyMeasurable.mul ?_)
      (Eventually.of_forall fun x => ?_)
    · have hm2 : AEStronglyMeasurable (fun p : Vec d × Vec d =>
          heatKernel 0 ρ p.2 * scaledTest ψ z S (p.1 - p.2)) (volume.prod volume) :=
        (((continuous_heatKernel_right (0 : Vec d) ρ).comp continuous_snd).mul
          (hcs.comp (continuous_fst.sub continuous_snd))).aestronglyMeasurable
      exact hm2.integral_prod_right'
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      calc |∫ x'', heatKernel 0 ρ x'' * scaledTest ψ z S (x - x'')|
          ≤ ∫ x'' : Vec d, heatKernel 0 ρ x'' * L := by
            refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
              (Eventually.of_forall fun _ => abs_nonneg _) (hE.mul_const L)
              (Eventually.of_forall fun x'' => ?_))
            dsimp only
            rw [abs_mul, abs_of_nonneg (heatKernel_nonneg (0 : Vec d) ρ x'')]
            exact mul_le_mul_of_nonneg_left (hψ.abs_scaled_le z S _) (heatKernel_nonneg _ _ _)
        _ = L := by rw [integral_mul_const, integral_heatKernel 0 hρ, one_mul]
  rw [← integral_sub hi1 hi2]
  simp_rw [hdiff]
  -- bound the absolute value and swap the integrals
  have hgx := hgi.integral_prod_left
  calc |∫ x, F x * ∫ x'', heatKernel 0 ρ x'' *
        (scaledTest ψ z S x - scaledTest ψ z S (x - x''))|
      ≤ ∫ x, ∫ x'', g (x, x'') := by
        refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
          (Eventually.of_forall fun _ => abs_nonneg _) hgx (Eventually.of_forall fun x => ?_))
        simp only [hg]
        rw [abs_mul, integral_const_mul]
        refine mul_le_mul_of_nonneg_left ((abs_integral_le_integral_abs).trans (le_of_eq ?_))
          (abs_nonneg _)
        refine integral_congr_ae (Eventually.of_forall fun x'' => ?_)
        dsimp only
        rw [abs_mul, abs_of_nonneg (heatKernel_nonneg (0 : Vec d) ρ x'')]
    _ = ∫ x'', ∫ x, g (x, x'') := integral_integral_swap (f := fun x x'' => g (x, x'')) hgi
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun x'' => ?_)
        simp only [hg]
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        ring

end Pairing

/-! ## A shift of the rescaled test -/

section Shift

variable {ψ : Vec d → ℝ} {L : ℝ} {z : Vec d} {S T k G : ℝ} {u : Vec d → ℝ}

/-- The `L¹` growth of the zero extension. -/
theorem setIntegral_abs_indicator_le (hS : 0 < S) (hST : S ≤ T) (hk : 0 ≤ k) (hG : 0 ≤ G)
    (hu : MemLp u 2 (volume.restrict (ball z T)))
    (hyp : ∀ t : ℝ, S ≤ t → t ≤ T →
      ∫ x in ball z t, u x ^ 2 ≤ G * ((t / S) ^ (2 * k) * volume.real (ball z t)))
    {R : ℝ} (hR : S ≤ R) :
    ∫ x in ball z R, |(ball z T).indicator u x| ≤
      volume.real (ball z R) * (Real.sqrt G * (R / S) ^ k) := by
  have hF : MemLp ((ball z T).indicator u) 2 volume :=
    (memLp_indicator_iff_restrict (measurableSet_ball z T)).mpr hu
  have hCS := sq_setIntegral_abs_le (volume_ball_lt_top z R).ne (hF.restrict (ball z R))
  have hgr := setIntegral_indicator_sq_le hS hST hk hG hyp hR
  have hRS : 0 ≤ R / S := (div_pos (hS.trans_le hR) hS).le
  have hV : 0 ≤ volume.real (ball z R) := measureReal_nonneg
  have hpow : (R / S) ^ (2 * k) = ((R / S) ^ k) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hRS]
    congr 1
    push_cast
    ring
  have hsq : (∫ x in ball z R, |(ball z T).indicator u x|) ^ 2 ≤
      (volume.real (ball z R) * (Real.sqrt G * (R / S) ^ k)) ^ 2 := by
    calc _ ≤ volume.real (ball z R) * ∫ x in ball z R, (ball z T).indicator u x ^ 2 := hCS
      _ ≤ volume.real (ball z R) * (G * ((R / S) ^ (2 * k) * volume.real (ball z R))) :=
          mul_le_mul_of_nonneg_left hgr hV
      _ = _ := by rw [hpow, mul_pow, mul_pow, Real.sq_sqrt hG]; ring
  have h0 : 0 ≤ ∫ x in ball z R, |(ball z T).indicator u x| :=
    integral_nonneg fun _ => abs_nonneg _
  exact (pow_le_pow_iff_left₀ h0 (mul_nonneg hV (mul_nonneg (Real.sqrt_nonneg _)
    (Real.rpow_nonneg hRS _))) two_ne_zero).mp hsq

/-- **A shift of the rescaled test**: the pairing of `|1_{B_T} u|` with the difference of the
rescaled test and its shift by `x''` is at most `L √G |B_S| (|x''|/S) (1 + |x''|/S)^{d + k}`. -/
theorem integral_abs_mul_shift_le (hψ : IsUnitTest ψ L) (hS : 0 < S) (hST : S ≤ T) (hk : 0 ≤ k)
    (hG : 0 ≤ G) (hu : MemLp u 2 (volume.restrict (ball z T)))
    (hyp : ∀ t : ℝ, S ≤ t → t ≤ T →
      ∫ x in ball z t, u x ^ 2 ≤ G * ((t / S) ^ (2 * k) * volume.real (ball z t)))
    (x'' : Vec d) :
    ∫ x, |(ball z T).indicator u x| * |scaledTest ψ z S x - scaledTest ψ z S (x - x'')| ≤
      L * Real.sqrt G * volume.real (ball z S) *
        (euclideanNorm x'' / S * (1 + euclideanNorm x'' / S) ^ ((d : ℝ) + k)) := by
  set F := (ball z T).indicator u with hFdef
  set n := euclideanNorm x'' with hn
  have hn0 : 0 ≤ n := Real.sqrt_nonneg _
  set R := S + n with hR
  have hSR : S ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  have hFi : Integrable F :=
    (integrable_indicator_iff (measurableSet_ball z T)).mpr
      (hu.integrable one_le_two (μ := volume.restrict (ball z T)))
  -- the pointwise majorant
  have hmaj : ∀ x, |F x| * |scaledTest ψ z S x - scaledTest ψ z S (x - x'')| ≤
      (ball z R).indicator (fun x => L / S * n * |F x|) x := by
    intro x
    by_cases hx : x ∈ ball z R
    · rw [Set.indicator_of_mem hx]
      have h := hψ.abs_scaled_sub_le (z := z) hS x (x - x'')
      rw [sub_sub_cancel, ← hn] at h
      calc |F x| * |scaledTest ψ z S x - scaledTest ψ z S (x - x'')|
          ≤ |F x| * (L / S * n) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
        _ = L / S * n * |F x| := by ring
    · rw [Set.indicator_of_notMem hx]
      have hx1 : x ∉ ball z S := fun h => hx (lt_of_lt_of_le h hSR)
      have hx2 : x - x'' ∉ ball z S := by
        intro h
        apply hx
        have h1 : euclideanNorm (x - z) ≤ euclideanNorm (x - x'' - z) + n := by
          have := euclideanNorm_add_le_add (x - x'' - z) x''
          rwa [show x - x'' - z + x'' = x - z by abel] at this
        show euclideanNorm (x - z) < R
        have h2 : euclideanNorm (x - x'' - z) < S := h
        linarith
      rw [hψ.scaled_eq_zero hS hx1, hψ.scaled_eq_zero hS hx2, sub_zero, abs_zero, mul_zero]
  have hcs := hψ.continuous_scaled z S
  have hint : Integrable fun x => |F x| * |scaledTest ψ z S x - scaledTest ψ z S (x - x'')| :=
    Integrable.mono' (hFi.norm.mul_const (2 * L))
      (hFi.aestronglyMeasurable.norm.mul
        ((hcs.sub (hcs.comp (continuous_id.sub continuous_const))).abs.aestronglyMeasurable))
      (Eventually.of_forall fun x => by
        have h1 := hψ.abs_scaled_le z S x
        have h2 := hψ.abs_scaled_le z S (x - x'')
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_abs, abs_abs]
        exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (by linarith)) (abs_nonneg _))
  have hmi : Integrable ((ball z R).indicator fun x => L / S * n * |F x|) :=
    (integrable_indicator_iff (measurableSet_ball z R)).mpr (hFi.norm.const_mul _).integrableOn
  have hgrow := setIntegral_abs_indicator_le hS hST hk hG hu hyp hSR
  have hVR := volume_real_ball_eq_rpow z hS hR0
  have hRS : R / S = 1 + n / S := by rw [hR, add_div, div_self hS.ne']
  have hRS0 : 0 < R / S := div_pos hR0 hS
  calc ∫ x, |F x| * |scaledTest ψ z S x - scaledTest ψ z S (x - x'')|
      ≤ ∫ x, (ball z R).indicator (fun x => L / S * n * |F x|) x :=
        integral_mono hint hmi hmaj
    _ = L / S * n * ∫ x in ball z R, |F x| := by
        rw [integral_indicator (measurableSet_ball z R), integral_const_mul]
    _ ≤ L / S * n * (volume.real (ball z R) * (Real.sqrt G * (R / S) ^ k)) :=
        mul_le_mul_of_nonneg_left hgrow
          (mul_nonneg (div_nonneg hψ.nonneg hS.le) hn0)
    _ = L * Real.sqrt G * volume.real (ball z S) *
          (n / S * ((R / S) ^ (d : ℝ) * (R / S) ^ k)) := by
        rw [hVR]; ring
    _ = _ := by
        rw [← Real.rpow_add hRS0, hRS]

end Shift

/-! ## The Gaussian moment -/

/-- The constant `2^{d+k} heatShellConstant d m`, `m = ⌈d + k⌉ + 1`, of the Gaussian moment of
the shift bound. -/
def absorptionMoment (d : ℕ) (k : ℝ) : ℝ :=
  2 ^ ((d : ℝ) + k) * heatShellConstant d (⌈(d : ℝ) + k⌉₊ + 1)

/-- **The Gaussian moment of the shift bound**: a nonnegative bounded function below
`B (|x|/S) (1 + |x|/S)^{d+k}` has Gaussian average at the scale `σ S` at most
`B σ absorptionMoment d k`, for `σ ≤ 1`. -/
theorem integral_heatKernel_mul_le_moment {S σ k B M₀ : ℝ} (hS : 0 < S) (hσ0 : 0 < σ)
    (hσ1 : σ ≤ 1) (hk : 0 ≤ k) (hB : 0 ≤ B) {g : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hgm : AEStronglyMeasurable g volume) (hgM : ∀ x, g x ≤ M₀)
    (hgb : ∀ x, g x ≤ B * (euclideanNorm x / S * (1 + euclideanNorm x / S) ^ ((d : ℝ) + k))) :
    ∫ x, heatKernel 0 (σ * S) x * g x ≤ B * σ * absorptionMoment d k := by
  set ρ := σ * S with hρ
  have hρ0 : 0 < ρ := mul_pos hσ0 hS
  set m : ℕ := ⌈(d : ℝ) + k⌉₊ + 1 with hm
  have hE := integrable_heatKernel (0 : Vec d) hρ0
  have hM0 : 0 ≤ M₀ := (hg0 0).trans (hgM 0)
  have hKf : Integrable fun x => heatKernel 0 ρ x * g x :=
    Integrable.mono' (hE.mul_const M₀)
      ((continuous_heatKernel_right (0 : Vec d) ρ).aestronglyMeasurable.mul hgm)
      (Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (heatKernel_nonneg _ _ _), abs_of_nonneg (hg0 x)]
        exact mul_le_mul_of_nonneg_left (hgM x) (heatKernel_nonneg _ _ _))
  have hfi : ∀ R : ℝ, IntegrableOn g (ball 0 R) := fun R => by
    have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
      isFiniteMeasure_restrict.mpr (volume_ball_lt_top 0 R).ne
    exact Integrable.mono' (integrable_const M₀) hgm.restrict
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]; exact hgM x)
  have h2 : (0 : ℝ) ≤ 2 ^ ((d : ℝ) + k) := Real.rpow_nonneg (by norm_num) _
  have hA : 0 ≤ B * σ * 2 ^ ((d : ℝ) + k) := mul_nonneg (mul_nonneg hB hσ0.le) h2
  have hgrowth : ∀ t : ℝ, ρ ≤ t → ∫ x in ball 0 t, g x ≤
      B * σ * 2 ^ ((d : ℝ) + k) * (t / ρ) ^ m * volume.real (ball (0 : Vec d) t) := by
    intro t ht
    have htρ : 1 ≤ t / ρ := (one_le_div hρ0).mpr ht
    have htS : t / S = σ * (t / ρ) := by
      rw [hρ]
      field_simp
    have hpt : ∀ x ∈ ball (0 : Vec d) t,
        g x ≤ B * σ * 2 ^ ((d : ℝ) + k) * (t / ρ) ^ m := by
      intro x hx
      have hxt : euclideanNorm x < t := by
        have h : euclideanNorm (x - 0) < t := hx
        rwa [sub_zero] at h
      have hn0 : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
      have hnS : 0 ≤ euclideanNorm x / S := div_nonneg hn0 hS.le
      have h1 : euclideanNorm x / S ≤ σ * (t / ρ) := by
        rw [← htS]
        exact div_le_div_of_nonneg_right hxt.le hS.le
      have h1' : euclideanNorm x / S ≤ t / ρ :=
        h1.trans (mul_le_of_le_one_left (by linarith) hσ1)
      have h3 : 1 + euclideanNorm x / S ≤ 2 * (t / ρ) := by linarith
      have hdk : 0 ≤ (d : ℝ) + k := by positivity
      have h4 : (1 + euclideanNorm x / S) ^ ((d : ℝ) + k) ≤
          2 ^ ((d : ℝ) + k) * (t / ρ) ^ ((d : ℝ) + k) := by
        rw [← Real.mul_rpow (by norm_num) (by linarith)]
        exact Real.rpow_le_rpow (by positivity) h3 hdk
      have h5 : (t / ρ) * (t / ρ) ^ ((d : ℝ) + k) ≤ (t / ρ) ^ m := by
        rw [← Real.rpow_one_add' (by linarith) (by positivity), ← Real.rpow_natCast]
        refine Real.rpow_le_rpow_of_exponent_le htρ ?_
        rw [hm]
        push_cast
        linarith [Nat.le_ceil ((d : ℝ) + k)]
      calc g x ≤ B * (euclideanNorm x / S * (1 + euclideanNorm x / S) ^ ((d : ℝ) + k)) :=
            hgb x
        _ ≤ B * (σ * (t / ρ) * (2 ^ ((d : ℝ) + k) * (t / ρ) ^ ((d : ℝ) + k))) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul h1 h4 (Real.rpow_nonneg (by linarith) _)
              (by positivity)) hB
        _ = B * σ * 2 ^ ((d : ℝ) + k) * ((t / ρ) * (t / ρ) ^ ((d : ℝ) + k)) := by ring
        _ ≤ B * σ * 2 ^ ((d : ℝ) + k) * (t / ρ) ^ m := mul_le_mul_of_nonneg_left h5 hA
    calc ∫ x in ball 0 t, g x
        ≤ ∫ x in ball (0 : Vec d) t, B * σ * 2 ^ ((d : ℝ) + k) * (t / ρ) ^ m := by
          have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) t)) :=
            isFiniteMeasure_restrict.mpr (volume_ball_lt_top 0 t).ne
          exact setIntegral_mono_on (hfi t) (integrable_const _) (measurableSet_ball 0 t) hpt
      _ = _ := by rw [setIntegral_const, smul_eq_mul]; ring
  have hmain := integral_heatKernel_mul_le_of_ball_growth_univ hg0 hρ0 hKf hfi hA m hgrowth
  calc ∫ x, heatKernel 0 ρ x * g x ≤ heatShellConstant d m * (B * σ * 2 ^ ((d : ℝ) + k)) :=
        hmain
    _ = B * σ * absorptionMoment d k := by rw [absorptionMoment, ← hm]; ring

/-! ## The absorption -/

/-- **The finite-ball observation from the estimate with compact tests** (SCOTT-localization (4)
from (D)): under the growth hypothesis of T22 (2) on `[S, T]`, the square integral of `u` on
`B_S(z)` is bounded by the truncated Gaussian observation at the scale `σ S` on `B_{2S}(z)` and
the outer term, for `σ ∈ (0, 1]` with `2 N C (L σ M)² ≤ 1/2`. -/
theorem integral_sq_ball_le_of_compactTests {z : Vec d} {S T k C L σ : ℝ} {N : ℕ}
    {ψ : Fin N → Vec d → ℝ} (hψ : ∀ ℓ, IsUnitTest (ψ ℓ) L)
    (hS : 0 < S) (hST : S ≤ T) (hk : 0 ≤ k) (hC : 0 ≤ C) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hσ : 2 * (N : ℝ) * C * (L * σ * absorptionMoment d k) ^ 2 ≤ 1 / 2)
    {u : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict (ball z T)))
    (hyp : ∀ t : ℝ, S ≤ t → t ≤ T → ∫ x in ball z t, u x ^ 2 ≤
      C * (∑ ℓ, ((volume.real (ball z S))⁻¹ *
          ∫ x in ball z T, u x * scaledTest (ψ ℓ) z S x) ^ 2 +
        (S / T) ^ (2 * k) * ((volume.real (ball z T))⁻¹ * ∫ x in ball z T, u x ^ 2)) *
        ((t / S) ^ (2 * k) * volume.real (ball z t))) :
    ∫ x in ball z S, u x ^ 2 ≤ (4 * C * N * L ^ 2 * 2 ^ d + 2 * C) *
      (volume.real (ball z S) * localizationObjective z T S σ (1 / 2) u +
        (S / T) ^ (2 * k) * ∫ x in ball z T, u x ^ 2) := by
  set V := volume.real (ball z S) with hV
  have hV0 : 0 < V := volume_real_ball_pos z hS
  have hT0 : 0 < T := hS.trans_le hST
  set VT := volume.real (ball z T) with hVT
  have hVT0 : 0 < VT := volume_real_ball_pos z hT0
  set M := absorptionMoment d k with hM
  set F := (ball z T).indicator u with hFdef
  have hFi : Integrable F :=
    (integrable_indicator_iff (measurableSet_ball z T)).mpr
      (hu.integrable one_le_two (μ := volume.restrict (ball z T)))
  set O : Fin N → ℝ := fun ℓ => V⁻¹ * ∫ x in ball z T, u x * scaledTest (ψ ℓ) z S x with hO
  set Rest := (S / T) ^ (2 * k) * (VT⁻¹ * ∫ x in ball z T, u x ^ 2) with hRest
  have hRest0 : 0 ≤ Rest :=
    mul_nonneg (Real.rpow_nonneg (div_pos hS hT0).le _)
      (mul_nonneg (inv_nonneg.mpr hVT0.le) (integral_nonneg fun _ => sq_nonneg _))
  set G := C * (∑ ℓ, O ℓ ^ 2 + Rest) with hGdef
  have hG0 : 0 ≤ G := mul_nonneg hC (add_nonneg (Finset.sum_nonneg fun ℓ _ => sq_nonneg _) hRest0)
  have hyp' : ∀ t : ℝ, S ≤ t → t ≤ T →
      ∫ x in ball z t, u x ^ 2 ≤ G * ((t / S) ^ (2 * k) * volume.real (ball z t)) := hyp
  set ρ := σ * S with hρ
  have hρ0 : 0 < ρ := mul_pos hσ0 hS
  set w : Vec d → ℝ := fun y => ∫ x, heatKernel y ρ x * F x with hw
  set I := localizationObjective z T S σ (1 / 2) u with hIdef
  -- the observation through `w`
  have hwT : ∀ y, ∫ x in ball z T, heatKernel y (σ * S) x * u x = w y := fun y => by
    rw [hw, ← integral_indicator (measurableSet_ball z T)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hFdef]
    by_cases hx : x ∈ ball z T
    · simp [hx, hρ]
    · simp [hx]
  have h2S : S / (1 / 2) = 2 * S := by ring
  have hV2 : volume.real (ball z (2 * S)) = 2 ^ d * V := by
    rw [volume_real_ball_eq_mul z (by positivity), hV, volume_real_ball_eq_mul z hS, mul_pow]
    ring
  have hI : ∫ y in ball z (2 * S), w y ^ 2 = 2 ^ d * V * I := by
    rw [hIdef, localizationObjective, h2S, setAverage_eq, smul_eq_mul, hV2]
    simp_rw [hwT]
    field_simp
  -- properties of `w`
  have hKF : AEStronglyMeasurable (fun p : Vec d × Vec d => heatKernel p.1 ρ p.2 * F p.2)
      (volume.prod volume) :=
    (continuous_heatKernel ρ).aestronglyMeasurable.mul hFi.aestronglyMeasurable.comp_snd
  have hwm : AEStronglyMeasurable w volume := hKF.integral_prod_right'
  set Mw := heatKernelPeak d ρ * ∫ x, |F x| with hMw
  have hwb : ∀ y, |w y| ≤ Mw := fun y => by
    refine (abs_integral_le_integral_abs).trans ?_
    rw [hMw, ← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
      (hFi.abs.const_mul _) (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [abs_mul, abs_of_nonneg (heatKernel_nonneg _ _ _)]
    exact mul_le_mul_of_nonneg_right (heatKernel_le_peak y hρ0.ne' x) (abs_nonneg _)
  have hwL2 : ∀ R : ℝ, MemLp w 2 (volume.restrict (ball z R)) := fun R => by
    have : IsFiniteMeasure (volume.restrict (ball z R)) :=
      isFiniteMeasure_restrict.mpr (volume_ball_lt_top z R).ne
    exact MemLp.of_bound hwm.restrict Mw
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hwb y)
  -- the bound for each test
  have hOℓ : ∀ ℓ, O ℓ ^ 2 ≤ 2 * (L ^ 2 * 2 ^ d * I) + 2 * ((L * σ * M) ^ 2 * G) := by
    intro ℓ
    have hψℓ := hψ ℓ
    have hL0 := hψℓ.nonneg
    set Oσ := V⁻¹ * ∫ y, scaledTest (ψ ℓ) z S y * w y with hOσ
    -- (a) the smoothed pairing
    have ha : Oσ ^ 2 ≤ L ^ 2 * 2 ^ d * I := by
      have hsupp : ∫ y in ball z S, scaledTest (ψ ℓ) z S y * w y =
          ∫ y, scaledTest (ψ ℓ) z S y * w y :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
          rw [hψℓ.scaled_eq_zero hS hy, zero_mul]
      have hwS := hwL2 S
      have hwi : IntegrableOn w (ball z S) := by
        have : IsFiniteMeasure (volume.restrict (ball z S)) :=
          isFiniteMeasure_restrict.mpr (volume_ball_lt_top z S).ne
        exact hwS.integrable one_le_two
      have h1 : |∫ y, scaledTest (ψ ℓ) z S y * w y| ≤ L * ∫ y in ball z S, |w y| := by
        rw [← hsupp, ← integral_const_mul]
        refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
          (Eventually.of_forall fun _ => abs_nonneg _) (hwi.abs.const_mul L)
          (Eventually.of_forall fun y => ?_))
        dsimp only
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hψℓ.abs_scaled_le z S y) (abs_nonneg _)
      have h2 := sq_setIntegral_abs_le (volume_ball_lt_top z S).ne hwS
      have h3 : ∫ y in ball z S, w y ^ 2 ≤ ∫ y in ball z (2 * S), w y ^ 2 := by
        refine setIntegral_mono_set ?_ (Eventually.of_forall fun _ => sq_nonneg _)
          (Eventually.of_forall fun y hy => ?_)
        · exact (hwL2 (2 * S)).integrable_sq
        · have hy' : euclideanNorm (y - z) < S := hy
          show euclideanNorm (y - z) < 2 * S
          linarith
      have h4 : (∫ y, scaledTest (ψ ℓ) z S y * w y) ^ 2 ≤ L ^ 2 * (V * (2 ^ d * V * I)) := by
        have h0 : 0 ≤ ∫ y in ball z S, |w y| := integral_nonneg fun _ => abs_nonneg _
        calc (∫ y, scaledTest (ψ ℓ) z S y * w y) ^ 2
            = |∫ y, scaledTest (ψ ℓ) z S y * w y| ^ 2 := (sq_abs _).symm
          _ ≤ (L * ∫ y in ball z S, |w y|) ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg _) h1 2
          _ = L ^ 2 * (∫ y in ball z S, |w y|) ^ 2 := by ring
          _ ≤ L ^ 2 * (V * ∫ y in ball z S, w y ^ 2) :=
              mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
          _ ≤ L ^ 2 * (V * (2 ^ d * V * I)) := by
              rw [← hI]
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hV0.le) (sq_nonneg _)
      have e : Oσ ^ 2 = (V⁻¹) ^ 2 * (∫ y, scaledTest (ψ ℓ) z S y * w y) ^ 2 := by
        rw [hOσ, mul_pow]
      rw [e]
      calc (V⁻¹) ^ 2 * (∫ y, scaledTest (ψ ℓ) z S y * w y) ^ 2
          ≤ (V⁻¹) ^ 2 * (L ^ 2 * (V * (2 ^ d * V * I))) :=
            mul_le_mul_of_nonneg_left h4 (sq_nonneg _)
        _ = L ^ 2 * 2 ^ d * I := by field_simp
    -- (b) the difference with the smoothed pairing
    have hb : |O ℓ - Oσ| ≤ L * σ * M * Real.sqrt G := by
      have hpair : V * O ℓ = ∫ x, F x * scaledTest (ψ ℓ) z S x := by
        rw [hO]
        simp only
        rw [← mul_assoc, mul_inv_cancel₀ hV0.ne', one_mul,
          ← integral_indicator (measurableSet_ball z T)]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [hFdef]
        by_cases hx : x ∈ ball z T
        · simp [hx]
        · simp [hx]
      have hσpair : V * Oσ = ∫ y, scaledTest (ψ ℓ) z S y * w y := by
        rw [hOσ, ← mul_assoc, mul_inv_cancel₀ hV0.ne', one_mul]
      have hdiff := abs_pairing_sub_smoothed_le hψℓ z (S := S) hρ0 hFi
      set h : Vec d → ℝ := fun x'' => ∫ x, |F x| *
        |scaledTest (ψ ℓ) z S x - scaledTest (ψ ℓ) z S (x - x'')| with hh
      have hcs := hψℓ.continuous_scaled z S
      have hhm : AEStronglyMeasurable h volume := by
        have hm : AEStronglyMeasurable (fun p : Vec d × Vec d =>
            |F p.1| * |scaledTest (ψ ℓ) z S p.1 - scaledTest (ψ ℓ) z S (p.1 - p.2)|)
            (volume.prod volume) :=
          hFi.aestronglyMeasurable.comp_fst.norm.mul
            ((hcs.comp continuous_fst).sub
              (hcs.comp (continuous_fst.sub continuous_snd))).abs.aestronglyMeasurable
        exact hm.prod_swap.integral_prod_right'
      have hh0 : ∀ x'', 0 ≤ h x'' := fun x'' =>
        integral_nonneg fun x => mul_nonneg (abs_nonneg _) (abs_nonneg _)
      have hhM : ∀ x'', h x'' ≤ 2 * L * ∫ x, |F x| := fun x'' => by
        rw [hh, ← integral_const_mul]
        refine integral_mono_of_nonneg (Eventually.of_forall fun x =>
          mul_nonneg (abs_nonneg _) (abs_nonneg _)) (hFi.abs.const_mul _)
          (Eventually.of_forall fun x => ?_)
        have h1 := hψℓ.abs_scaled_le z S x
        have h2 := hψℓ.abs_scaled_le z S (x - x'')
        calc |F x| * |scaledTest (ψ ℓ) z S x - scaledTest (ψ ℓ) z S (x - x'')|
            ≤ |F x| * (2 * L) :=
              mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (by linarith)) (abs_nonneg _)
          _ = 2 * L * |F x| := by ring
      have hhb := fun x'' => integral_abs_mul_shift_le hψℓ hS hST hk hG0 hu hyp' x''
      have hmom := integral_heatKernel_mul_le_moment hS hσ0 hσ1 hk
        (mul_nonneg (mul_nonneg hL0 (Real.sqrt_nonneg G)) hV0.le) hh0 hhm hhM hhb
      have hVdiff : V * |O ℓ - Oσ| ≤ V * (L * σ * M * Real.sqrt G) := by
        rw [← abs_of_pos hV0, ← abs_mul, mul_sub, hpair, hσpair, abs_of_pos hV0]
        calc _ ≤ _ := hdiff
          _ ≤ L * Real.sqrt G * V * σ * M := hmom
          _ = V * (L * σ * M * Real.sqrt G) := by ring
      exact le_of_mul_le_mul_left hVdiff hV0
    -- (c) combine
    have hc : (O ℓ - Oσ) ^ 2 ≤ (L * σ * M) ^ 2 * G := by
      have hM0 : 0 ≤ L * σ * M * Real.sqrt G := le_trans (abs_nonneg _) hb
      calc (O ℓ - Oσ) ^ 2 = |O ℓ - Oσ| ^ 2 := (sq_abs _).symm
        _ ≤ (L * σ * M * Real.sqrt G) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
        _ = (L * σ * M) ^ 2 * G := by rw [mul_pow, Real.sq_sqrt hG0]
    have e : O ℓ = Oσ + (O ℓ - Oσ) := by ring
    calc O ℓ ^ 2 = (Oσ + (O ℓ - Oσ)) ^ 2 := by rw [← e]
      _ ≤ 2 * Oσ ^ 2 + 2 * (O ℓ - Oσ) ^ 2 := by nlinarith [sq_nonneg (Oσ - (O ℓ - Oσ))]
      _ ≤ 2 * (L ^ 2 * 2 ^ d * I) + 2 * ((L * σ * M) ^ 2 * G) := by linarith
  -- the absorption
  set a := L ^ 2 * 2 ^ d * I with ha
  set b := (L * σ * M) ^ 2 with hb
  have hsum : ∑ ℓ, O ℓ ^ 2 ≤ N * (2 * a + 2 * (b * G)) := by
    calc ∑ ℓ, O ℓ ^ 2 ≤ ∑ _ℓ : Fin N, (2 * a + 2 * (b * G)) := Finset.sum_le_sum fun ℓ _ => hOℓ ℓ
      _ = N * (2 * a + 2 * (b * G)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hG1 : G ≤ C * (N * (2 * a + 2 * (b * G)) + Rest) :=
    mul_le_mul_of_nonneg_left (by linarith) hC
  have e1 : C * (N * (2 * a + 2 * (b * G)) + Rest) =
      2 * C * N * a + (2 * N * C * b) * G + C * Rest := by ring
  have hσ' : 2 * N * C * b * G ≤ 1 / 2 * G := mul_le_mul_of_nonneg_right hσ hG0
  have hG2 : G ≤ 4 * C * N * a + 2 * C * Rest := by linarith
  -- the conclusion
  have hS1 : ∫ x in ball z S, u x ^ 2 ≤ G * V := by
    have := hyp' S le_rfl hST
    rwa [div_self hS.ne', Real.one_rpow, one_mul] at this
  have hVVT : V ≤ VT := measureReal_mono (fun x hx => lt_of_lt_of_le hx hST)
    (volume_ball_lt_top z T).ne
  have hJ0 : 0 ≤ ∫ x in ball z T, u x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hpowST : 0 ≤ (S / T) ^ (2 * k) := Real.rpow_nonneg (div_pos hS hT0).le _
  have hI0 : 0 ≤ I := by
    rw [hIdef, localizationObjective, setAverage_eq, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr measureReal_nonneg) (integral_nonneg fun _ => sq_nonneg _)
  have hRestV : Rest * V ≤ (S / T) ^ (2 * k) * ∫ x in ball z T, u x ^ 2 := by
    rw [hRest]
    have : VT⁻¹ * V ≤ 1 := by rw [inv_mul_le_iff₀ hVT0, mul_one]; exact hVVT
    calc (S / T) ^ (2 * k) * (VT⁻¹ * ∫ x in ball z T, u x ^ 2) * V
        = (S / T) ^ (2 * k) * (∫ x in ball z T, u x ^ 2) * (VT⁻¹ * V) := by ring
      _ ≤ (S / T) ^ (2 * k) * (∫ x in ball z T, u x ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left this (mul_nonneg hpowST hJ0)
      _ = _ := mul_one _
  have hA0 : 0 ≤ 4 * C * N * L ^ 2 * 2 ^ d := by positivity
  calc ∫ x in ball z S, u x ^ 2 ≤ G * V := hS1
    _ ≤ (4 * C * N * a + 2 * C * Rest) * V := mul_le_mul_of_nonneg_right hG2 hV0.le
    _ = 4 * C * N * L ^ 2 * 2 ^ d * (V * I) + 2 * C * (Rest * V) := by rw [ha]; ring
    _ ≤ 4 * C * N * L ^ 2 * 2 ^ d * (V * I) +
          2 * C * ((S / T) ^ (2 * k) * ∫ x in ball z T, u x ^ 2) := by
        have := mul_le_mul_of_nonneg_left hRestV (by positivity : (0 : ℝ) ≤ 2 * C)
        linarith
    _ ≤ (4 * C * N * L ^ 2 * 2 ^ d + 2 * C) *
          (V * I + (S / T) ^ (2 * k) * ∫ x in ball z T, u x ^ 2) := by
        have h1 : 0 ≤ V * I := mul_nonneg hV0.le hI0
        have h2 : 0 ≤ (S / T) ^ (2 * k) * ∫ x in ball z T, u x ^ 2 := mul_nonneg hpowST hJ0
        nlinarith [mul_nonneg hA0 h2, mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * C) h1]

/-! ## Above a random radius at every center -/

/-- **The estimate with compact tests above a random radius at every center** (consultant T22,
(2), in the form of SCOTT-localization (D)): there are finitely many tests `ψ_ℓ` supported in the
unit ball, `L₁ ≥ 1` and `C ≥ 0` and, for every `τ < d`, a constant `C_τ` such that for every law
and center `z` there is a random radius `X ≥ 1` with `X ≤ O_τ(C_τ)` such that almost surely, for
`X ≤ S`, `L₁ S ≤ T`, every `a`-harmonic `u` on `B_T(z)` and every `t ∈ [S, T]`,
`∫_{B_t(z)} u² ≤ C (∑_ℓ O_ℓ² + (S/T)^{2k} ⨍_{B_T(z)} u²) (t/S)^{2k} |B_t|`, with
`O_ℓ = |B_S|⁻¹ ∫_{B_T(z)} u ψ_ℓ((x - z)/S)`. -/
def CompactTestFiniteBall (d : ℕ) (Λ k : ℝ) : Prop :=
  ∃ (N : ℕ) (ψ : Fin N → Vec d → ℝ) (L L₁ C : ℝ), 0 ≤ L ∧ (∀ ℓ, IsUnitTest (ψ ℓ) L) ∧
    1 ≤ L₁ ∧ 0 ≤ C ∧
    ∀ τ : ℝ, 0 < τ → τ < d → ∃ Cτ : ℝ, 0 < Cτ ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ z : Vec d,
        ∃ X : CoefficientField d Λ → ℝ, Measurable X ∧ OsBound P X τ Cτ ∧ (∀ a, 1 ≤ X a) ∧
          ∀ᵐ a ∂P, ∀ S T : ℝ, X a ≤ S → L₁ * S ≤ T → ∀ u : LocalHarmonic a z T,
            ∀ t : ℝ, S ≤ t → t ≤ T → ∫ x in ball z t, u.potential x ^ 2 ≤
              C * (∑ ℓ, ((volume.real (ball z S))⁻¹ *
                  ∫ x in ball z T, u.potential x * scaledTest (ψ ℓ) z S x) ^ 2 +
                (S / T) ^ (2 * k) * ((volume.real (ball z T))⁻¹ *
                  ∫ x in ball z T, u.potential x ^ 2)) *
                ((t / S) ^ (2 * k) * volume.real (ball z t))

/-- The smoothing fraction of the absorption: `σ = 1/(2 (1 + L M)(1 + N C))`. -/
theorem absorption_fraction {N : ℕ} {C L M : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hM : 0 ≤ M) :
    let σ := 1 / (2 * (1 + L * M) * (1 + N * C))
    0 < σ ∧ σ ≤ 1 / 2 ∧ 2 * (N : ℝ) * C * (L * σ * M) ^ 2 ≤ 1 / 2 := by
  intro σ
  have hLM : 0 ≤ L * M := mul_nonneg hL hM
  have hNC : 0 ≤ (N : ℝ) * C := mul_nonneg (Nat.cast_nonneg N) hC
  have hσ0 : 0 < σ := by positivity
  refine ⟨hσ0, ?_, ?_⟩
  · show 1 / (2 * (1 + L * M) * (1 + N * C)) ≤ 1 / 2
    refine one_div_le_one_div_of_le (by norm_num) ?_
    nlinarith
  · have e : L * σ * M = (L * M / (1 + L * M)) * (1 / (2 * (1 + N * C))) := by
      show L * (1 / (2 * (1 + L * M) * (1 + N * C))) * M = _
      field_simp
    have h1 : L * M / (1 + L * M) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    have h2 : L * σ * M ≤ 1 / (2 * (1 + N * C)) := by
      rw [e]
      exact mul_le_of_le_one_left (by positivity) h1
    have h3 : (L * σ * M) ^ 2 ≤ (1 / (2 * (1 + N * C))) ^ 2 :=
      pow_le_pow_left₀ (by rw [e]; positivity) h2 2
    have h4 : 2 * ((N : ℝ) * C) * (1 / (2 * (1 + N * C))) ^ 2 =
        (N * C) / (2 * (1 + N * C) ^ 2) := by
      field_simp
    have h5 : (N * C : ℝ) / (2 * (1 + N * C) ^ 2) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    calc 2 * (N : ℝ) * C * (L * σ * M) ^ 2 = 2 * ((N : ℝ) * C) * (L * σ * M) ^ 2 := by ring
      _ ≤ 2 * ((N : ℝ) * C) * (1 / (2 * (1 + N * C))) ^ 2 :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ 1 / 2 := by rw [h4]; exact h5

theorem absorptionMoment_nonneg (d : ℕ) (k : ℝ) : 0 ≤ absorptionMoment d k := by
  unfold absorptionMoment heatShellConstant heatShellSum
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (mul_nonneg (mul_nonneg (by positivity) measureReal_nonneg)
      (tsum_nonneg fun j => by positivity))

/-- **The finite-ball observation from the estimate with compact tests** (SCOTT-localization (4)):
`CompactTestFiniteBall d Λ k` gives `σ, θ ∈ (0, 1/2]` (`θ = 1/2`) and the finite-ball
observation `∫_{B_S(z)} u² ≤ C (|B_S| I + (S/T)^{2k} ∫_{B_T(z)} u²)` above the same random radius,
with `I = localizationObjective z T S σ θ u`. The statement is the body of `FiniteBallObservation`
of the observation estimate. -/
theorem finiteBallObservation_of_compactTests {Λ k : ℝ} (hk : 0 ≤ k)
    (h : CompactTestFiniteBall d Λ k) :
    ∃ σ θ : ℝ, 0 < σ ∧ σ ≤ 1 / 2 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧
      ∃ (L₀ C : ℝ), 1 ≤ L₀ ∧ 0 < C ∧ ∀ τ : ℝ, 0 < τ → τ < d → ∃ Cτ : ℝ, 0 < Cτ ∧
        ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ z : Vec d,
          ∃ X : CoefficientField d Λ → ℝ, Measurable X ∧ OsBound P X τ Cτ ∧ (∀ a, 1 ≤ X a) ∧
            ∀ᵐ a ∂P, ∀ S T : ℝ, X a ≤ S → L₀ * S ≤ T → ∀ u : LocalHarmonic a z T,
              ∫ x in ball z S, u.potential x ^ 2 ≤
                C * (volume.real (ball z S) * localizationObjective z T S σ θ u.potential +
                  (S / T) ^ (2 * k) * ∫ x in ball z T, u.potential x ^ 2) := by
  obtain ⟨N, ψ, L, L₁, C, hL, hψ, hL₁, hC, hmain⟩ := h
  obtain ⟨hσ0, hσ2, hσ⟩ := absorption_fraction (N := N) hC hL (absorptionMoment_nonneg d k)
  set σ := 1 / (2 * (1 + L * absorptionMoment d k) * (1 + N * C)) with hσdef
  refine ⟨σ, 1 / 2, hσ0, hσ2, by norm_num, le_rfl, L₁,
    max (4 * C * N * L ^ 2 * 2 ^ d + 2 * C) 1, hL₁, lt_max_of_lt_right one_pos,
    fun τ hτ0 hτd => ?_⟩
  obtain ⟨Cτ, hCτ, hP⟩ := hmain τ hτ0 hτd
  refine ⟨Cτ, hCτ, fun P hPl z => ?_⟩
  obtain ⟨X, hXm, hXos, hX1, hae⟩ := hP P hPl z
  refine ⟨X, hXm, hXos, hX1, ?_⟩
  filter_upwards [hae] with a ha
  intro S T hXS hST u
  have hS : 0 < S := lt_of_lt_of_le one_pos ((hX1 a).trans hXS)
  have hST' : S ≤ T := le_trans (le_mul_of_one_le_left hS.le hL₁) hST
  have hb := integral_sq_ball_le_of_compactTests hψ hS hST' hk hC hσ0 (by linarith) hσ
    u.square_integrable (ha S T hXS hST u)
  have hT0 : 0 < T := hS.trans_le hST'
  have hY : 0 ≤ volume.real (ball z S) * localizationObjective z T S σ (1 / 2) u.potential +
      (S / T) ^ (2 * k) * ∫ x in ball z T, u.potential x ^ 2 := by
    refine add_nonneg (mul_nonneg measureReal_nonneg ?_)
      (mul_nonneg (Real.rpow_nonneg (div_pos hS hT0).le _) (integral_nonneg fun _ => sq_nonneg _))
    rw [localizationObjective, setAverage_eq, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr measureReal_nonneg) (integral_nonneg fun _ => sq_nonneg _)
  exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hY)

end QSH
