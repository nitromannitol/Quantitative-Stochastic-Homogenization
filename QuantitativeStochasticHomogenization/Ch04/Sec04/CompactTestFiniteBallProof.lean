import QuantitativeStochasticHomogenization.Ch04.Sec04.CompactTestFiniteBallCore
import QuantitativeStochasticHomogenization.Ch04.Sec04.CompactTestAdaptedPair
import QuantitativeStochasticHomogenization.Ch04.Sec04.CompactTestCorrectorTranslation
import QuantitativeStochasticHomogenization.Ch04.Sec04.CompactTestRandomFamily

/-!
# The finite-ball estimate with compact tests above a random radius

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.21, through a finite-ball estimate with compact tests, at every
center and above a random radius, with the constants chosen before the law.

The compact tests are adapted to the homogenized matrix `ā` of the law: they are the rescaled
derivatives `ψ_α = (∂^α ρ)(-·/λ)`, `|α| < ⌈k⌉`, of the compact profile `ρ` of the symmetric part of
`ā`. Their number, their bounds and Lipschitz constants and the constant of the estimate are chosen
before the law (`CompactTestFiniteBallLaw`); the absorption into the truncated Gaussian observation
only uses these (`finiteBallObservation_of_compactTestsLaw`).

At a center `z`, the corrector families at the nearest lattice point `y` (above the random scale of
`exists_ae_sublinearCorrectorFamily`, transported by the stationarity of the law) are translated
by `z - y` to the field `a(z + ·)` (`SublinearCorrectorFamily.translate`), and the deterministic core
`compactTest_core` applies to the shifted solution; its observations are the pairings of `u` with
the rescaled tests (`compactTestFiniteBallLaw`).
-/

open MeasureTheory Filter Set
open scoped ContDiff

noncomputable section

namespace QSH

variable {d : ℕ}

/-- **The finite-ball estimate with compact tests chosen after the law**: as
`CompactTestFiniteBall d Λ k`, with the tests chosen for each law and their number, their bound
`L` and the constants `L₁`, `C` chosen before the law. -/
def CompactTestFiniteBallLaw (d : ℕ) (Λ k : ℝ) : Prop :=
  ∃ (N : ℕ) (L L₁ C : ℝ), 0 ≤ L ∧ 1 ≤ L₁ ∧ 0 ≤ C ∧
    ∀ τ : ℝ, 0 < τ → τ < d → ∃ Cτ : ℝ, 0 < Cτ ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
        ∃ ψ : Fin N → Vec d → ℝ, (∀ ℓ, IsUnitTest (ψ ℓ) L) ∧ ∀ z : Vec d,
        ∃ X : CoefficientField d Λ → ℝ, Measurable X ∧ OsBound P X τ Cτ ∧ (∀ a, 1 ≤ X a) ∧
          ∀ᵐ a ∂P, ∀ S T : ℝ, X a ≤ S → L₁ * S ≤ T → ∀ u : LocalHarmonic a z T,
            ∀ t : ℝ, S ≤ t → t ≤ T → ∫ x in ball z t, u.potential x ^ 2 ≤
              C * (∑ ℓ, ((volume.real (ball z S))⁻¹ *
                  ∫ x in ball z T, u.potential x * scaledTest (ψ ℓ) z S x) ^ 2 +
                (S / T) ^ (2 * k) * ((volume.real (ball z T))⁻¹ *
                  ∫ x in ball z T, u.potential x ^ 2)) *
                ((t / S) ^ (2 * k) * volume.real (ball z t))

/-- **The finite-ball observation from the estimate with compact tests chosen after the law**:
the absorption of `integral_sq_ball_le_of_compactTests` with `σ` chosen from `N`, `L` and `C`. -/
theorem finiteBallObservation_of_compactTestsLaw {Λ k : ℝ} (hk : 0 ≤ k)
    (h : CompactTestFiniteBallLaw d Λ k) :
    ∃ σ θ : ℝ, 0 < σ ∧ σ ≤ 1 / 2 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧
      ∃ (L₀ C : ℝ), 1 ≤ L₀ ∧ 0 < C ∧ ∀ τ : ℝ, 0 < τ → τ < d → ∃ Cτ : ℝ, 0 < Cτ ∧
        ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ z : Vec d,
          ∃ X : CoefficientField d Λ → ℝ, Measurable X ∧ OsBound P X τ Cτ ∧ (∀ a, 1 ≤ X a) ∧
            ∀ᵐ a ∂P, ∀ S T : ℝ, X a ≤ S → L₀ * S ≤ T → ∀ u : LocalHarmonic a z T,
              ∫ x in ball z S, u.potential x ^ 2 ≤
                C * (volume.real (ball z S) * localizationObjective z T S σ θ u.potential +
                  (S / T) ^ (2 * k) * ∫ x in ball z T, u.potential x ^ 2) := by
  obtain ⟨N, L, L₁, C, hL, hL₁, hC, hmain⟩ := h
  obtain ⟨hσ0, hσ2, hσ⟩ := absorption_fraction (N := N) hC hL (absorptionMoment_nonneg d k)
  set σ := 1 / (2 * (1 + L * absorptionMoment d k) * (1 + N * C)) with hσdef
  refine ⟨σ, 1 / 2, hσ0, hσ2, by norm_num, le_rfl, L₁,
    max (4 * C * N * L ^ 2 * 2 ^ d + 2 * C) 1, hL₁, lt_max_of_lt_right one_pos,
    fun τ hτ0 hτd => ?_⟩
  obtain ⟨Cτ, hCτ, hP⟩ := hmain τ hτ0 hτd
  refine ⟨Cτ, hCτ, fun P hPl z => ?_⟩
  obtain ⟨ψ, hψ, hz⟩ := hP P hPl
  obtain ⟨X, hXm, hXos, hX1, hae⟩ := hz z
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

/-! ## The rescaled compact tests -/

/-- The rescaled compact test `ψ_α = (∂^α ρ)(-·/λ)`. -/
def compactTestFn (ρ : Vec d → ℝ) (lam : ℝ) {j : ℕ} (α : Fin j → Fin d) : Vec d → ℝ :=
  dilate (-lam) (iterDeriv α ρ)

variable {D : Mat d} {ρ χ : Vec d → ℝ}

theorem coordinateDerivative_iterDeriv_eq_cons {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f) {j : ℕ}
    (α : Fin j → Fin d) (i : Fin d) :
    coordinateDerivative i (iterDeriv α f) = iterDeriv (Fin.cons i α : Fin (j + 1) → Fin d) f := by
  rw [coordinateDerivative_iterDeriv α hf i, iterDeriv_cons]

/-- **The rescaled compact tests are unit tests** with a bound depending only on the bounds of
the derivatives of `ρ` and on `λ`. -/
theorem isUnitTest_compactTestFn (P : CompactProfilePair D ρ χ) {lam : ℝ} (hlam0 : 0 < lam)
    (hlam1 : lam ≤ 1) {j : ℕ} (α : Fin j → Fin d) {K₀ K₁ L : ℝ} (hK₀0 : 0 ≤ K₀)
    (hK₀ : ∀ y, |iterDeriv α ρ y| ≤ K₀)
    (hK₁ : ∀ (β : Fin (j + 1) → Fin d) y, |iterDeriv β ρ y| ≤ K₁) (hL0 : K₀ ≤ L)
    (hL1 : (d : ℝ) * lam⁻¹ * K₁ ≤ L) : IsUnitTest (compactTestFn ρ lam α) L := by
  have hg := contDiff_iterDeriv α P.smooth_rho
  refine ⟨hK₀0.trans hL0, (contDiff_dilate hg _).continuous, fun x => (hK₀ _).trans hL0,
    fun x y => ?_, fun x hx => ?_⟩
  · have hB : ∀ i z, |coordinateDerivative i (compactTestFn ρ lam α) z| ≤ lam⁻¹ * K₁ := by
      intro i z
      unfold compactTestFn
      rw [coordinateDerivative_dilate (hg.differentiable (by simp))]
      simp only [dilate]
      rw [coordinateDerivative_iterDeriv_eq_cons P.smooth_rho, abs_mul, inv_neg, abs_neg,
        abs_inv, abs_of_pos hlam0]
      exact mul_le_mul_of_nonneg_left (hK₁ _ _) (inv_nonneg.2 hlam0.le)
    have h := abs_sub_le_of_forall_coordinateDerivative_le
      ((contDiff_dilate hg _).differentiable (by simp)) hB x y
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith [hL1, show (d : ℝ) * (lam⁻¹ * K₁) = (d : ℝ) * lam⁻¹ * K₁ by ring]
  · unfold compactTestFn dilate
    refine P.iterDeriv_rho_vanish α _ ?_
    rw [euclideanSq_smul', inv_neg, neg_sq]
    have hx1 : 1 ≤ euclideanSq x := by
      have h1 : (1 : ℝ) ≤ Real.sqrt (euclideanSq x) := hx
      have h2 := Real.le_sqrt (zero_le_one) (zero_le_euclideanSq x) |>.mp h1
      simpa using h2
    have hl : 1 ≤ (lam⁻¹) ^ 2 := one_le_pow₀ (one_le_inv₀ hlam0 |>.mpr hlam1)
    nlinarith

/-- **The observations of the compact averages** are pairings with the rescaled tests:
`s^j ∂^α U_s(0) = λ^{-d-j} |B_1| |B_s|⁻¹ ∫_{B_T} u ψ_α(·/s)`. -/
theorem pow_mul_profileAverage_eq {lam s : ℝ} (hlam0 : 0 < lam) (hs : 0 < s) {j : ℕ}
    (α : Fin j → Fin d) {T : ℝ} (u : Vec d → ℝ) :
    s ^ j * profileAverage ρ lam α ((ball 0 T).indicator u) s 0 =
      (lam⁻¹) ^ (d + j) * volume.real (ball (0 : Vec d) 1) *
        ((volume.real (ball (0 : Vec d) s))⁻¹ *
          ∫ x in ball 0 T, u x * scaledTest (compactTestFn ρ lam α) 0 s x) := by
  have hsm : ∀ w : Vec d, (lam * s)⁻¹ • (0 - w) = (-lam)⁻¹ • (s⁻¹ • (w - 0)) := fun w => by
    funext i
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, smul_eq_mul]
    field_simp
    ring
  have e1 : profileAverage ρ lam α ((ball 0 T).indicator u) s 0 =
      ((lam * s)⁻¹) ^ (d + j) * ∫ x in ball 0 T, u x * scaledTest (compactTestFn ρ lam α) 0 s x := by
    unfold profileAverage kernelPairing scaledKernel
    rw [← integral_const_mul, ← integral_indicator (measurableSet_ball _ _)]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    by_cases hw : w ∈ ball (0 : Vec d) T
    · simp only [Set.indicator_of_mem hw, scaledTest, compactTestFn, dilate, hsm w]
      ring
    · simp [Set.indicator_of_notMem hw]
  have hV := volume_real_ball_eq_mul (0 : Vec d) hs
  have hV1 : 0 < volume.real (ball (0 : Vec d) 1) := volume_real_ball_pos 0 one_pos
  rw [e1, hV, mul_inv, mul_pow, pow_add, pow_add]
  have hs' : s ≠ 0 := hs.ne'
  have hl' : lam ≠ 0 := hlam0.ne'
  simp only [inv_pow]
  field_simp

/-! ## Translation of the observations to the center `z` -/

theorem setIntegral_shift_sq {Λ : ℝ} {a b : CoefficientField d Λ} {z : Vec d} {T : ℝ}
    (u : LocalHarmonic a z T) (hb : ∀ x, b.field x = a.field (z + x)) (r : ℝ) :
    ∫ x in ball 0 r, (u.shift (z' := 0) hb (by simp)).potential x ^ 2 =
      ∫ x in ball z r, u.potential x ^ 2 :=
  setIntegral_ball_add (c := z) (z := z) (z' := 0) (by simp) r (fun x => u.potential x ^ 2)

theorem setIntegral_shift_mul_scaledTest {Λ : ℝ} {a b : CoefficientField d Λ} {z : Vec d}
    {T : ℝ} (u : LocalHarmonic a z T) (hb : ∀ x, b.field x = a.field (z + x)) (ψ : Vec d → ℝ)
    (s : ℝ) :
    ∫ x in ball 0 T, (u.shift (z' := 0) hb (by simp)).potential x * scaledTest ψ 0 s x =
      ∫ x in ball z T, u.potential x * scaledTest ψ z s x := by
  have h := setIntegral_ball_add (c := z) (z := z) (z' := 0) (by simp) T
    (fun x => u.potential x * scaledTest ψ z s x)
  rw [← h]
  refine setIntegral_congr_fun (measurableSet_ball _ _) fun x _ => ?_
  simp only [LocalHarmonic.shift_potential, scaledTest, add_sub_cancel_left, sub_zero]

theorem volume_real_ball_center (z : Vec d) (r : ℝ) :
    volume.real (ball (0 : Vec d) r) = volume.real (ball z r) := by
  rw [Measure.real, Measure.real, volume_ball_add (c := z) (z := z) (z' := 0) (by simp)]

theorem scalarRms_shift {Λ : ℝ} {a b : CoefficientField d Λ} {z : Vec d} {T : ℝ}
    (u : LocalHarmonic a z T) (hb : ∀ x, b.field x = a.field (z + x)) (r : ℝ) :
    scalarRms volume (ball 0 r) (u.shift (z' := 0) hb (by simp)).potential =
      Real.sqrt ((volume.real (ball z r))⁻¹ * ∫ x in ball z r, u.potential x ^ 2) := by
  unfold scalarRms
  rw [setAverage_eq, smul_eq_mul, setIntegral_shift_sq u hb r, volume_real_ball_center z r]

/-- `(Σ_ι |x_ι|)² ≤ |ι| Σ_ι x_ι²`. -/
theorem sq_sum_abs_le_card_mul {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    (∑ i, |x i|) ^ 2 ≤ Fintype.card ι * ∑ i, x i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun i => |x i|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    sq_abs] at h
  exact h

theorem dot_symmPart'_mulVec (D : Mat d) (ξ : Vec d) :
    dot ξ ((symmPart' D).mulVec ξ) = dot ξ (D.mulVec ξ) := by
  have h1 : dot ξ (D.transpose.mulVec ξ) = dot ξ (D.mulVec ξ) := by
    rw [← dot_mulVec_left' D ξ ξ]
    unfold dot
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h2 : dot ξ ((symmPart' D).mulVec ξ) =
      (1 / 2) * (dot ξ (D.mulVec ξ) + dot ξ (D.transpose.mulVec ξ)) := by
    unfold symmPart'
    rw [Matrix.smul_mulVec, Matrix.add_mulVec]
    simp only [dot, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h2, h1]
  ring

/-! ## The estimate above a random radius -/

/-- **The finite-ball estimate with compact tests above a random radius at every center**
(for the laws of AKM, with the tests chosen after the law). -/
theorem compactTestFiniteBallLaw (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) {k : ℝ} (hk : 0 < k) :
    CompactTestFiniteBallLaw d Λ k := by
  classical
  have hd0 : 0 < d := by omega
  have hΛ1 : 1 ≤ Λ := hΛ.le
  -- the order and the bounds of the adapted pairs
  set n : ℕ := ⌈k⌉₊ with hn
  have hnk : k ≤ n := Nat.le_ceil k
  have hnk1 : (n : ℝ) - 1 < k := by
    have := Nat.ceil_lt_add_one hk.le
    rw [← hn] at this
    linarith
  set K' : ℝ := Λ ^ 2 with hK'
  have hK'0 : 0 < K' := by positivity
  choose Kρf Kχf hKρf0 hKχf0 hKf using fun j => exists_adaptedPair_bounds (d := d) hK'0 j
  -- the smoothing fraction
  set lam : ℝ := min 1 (1 / (4 * (32 * Real.sqrt Λ * 2 ^ d * 4 ^ k))) with hlamdef
  have hc32 : 0 < 32 * Real.sqrt Λ * 2 ^ d * 4 ^ k := by
    have := Real.sqrt_pos.2 (by linarith : (0 : ℝ) < Λ)
    positivity
  have hlam0 : 0 < lam := lt_min one_pos (by positivity)
  have hlam1 : lam ≤ 1 := min_le_left _ _
  have hlam : 32 * Real.sqrt Λ * 2 ^ d * lam * 4 ^ k ≤ 1 / 4 := by
    have h := min_le_right 1 (1 / (4 * (32 * Real.sqrt Λ * 2 ^ d * 4 ^ k)))
    rw [← hlamdef] at h
    calc 32 * Real.sqrt Λ * 2 ^ d * lam * 4 ^ k = (32 * Real.sqrt Λ * 2 ^ d * 4 ^ k) * lam := by
          ring
      _ ≤ (32 * Real.sqrt Λ * 2 ^ d * 4 ^ k) * (1 / (4 * (32 * Real.sqrt Λ * 2 ^ d * 4 ^ k))) :=
          mul_le_mul_of_nonneg_left h hc32.le
      _ = 1 / 4 := by field_simp
  -- the constants of the estimate
  set S₂ : ℝ := ∑ j ∈ Finset.range (n + 1), Kχf (j + 2) with hS₂def
  have hS₂0 : 0 ≤ S₂ := Finset.sum_nonneg fun j _ => hKχf0 _
  set Kρ : ℝ := Kρf n with hKρdef
  set L : ℝ := ∑ j ∈ Finset.range (n + 1), (Kρf j + (d : ℝ) * lam⁻¹ * Kρf j) with hLdef
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun j _ => add_nonneg (hKρf0 j)
    (mul_nonneg (by positivity) (hKρf0 j))
  set ι := Σ j : Fin n, (Fin j → Fin d) with hι
  set N : ℕ := Fintype.card ι with hN
  set V₁ : ℝ := volume.real (ball (0 : Vec d) 1) with hV₁
  have hV₁0 : 0 < V₁ := volume_real_ball_pos 0 one_pos
  set Cobs : ℝ := (lam⁻¹) ^ (d + n) * V₁ with hCobs
  set C' : ℝ := outerConst d lam Kρ n + 4 ^ k * 2 ^ d with hC'
  set C : ℝ := 8 * (Cobs ^ 2 * N + C' ^ 2) with hCdef
  have hC0 : 0 ≤ C := by positivity
  obtain ⟨β, Cc, hβ, hCc, hfam⟩ := exists_ae_sublinearCorrectorFamily hd hΛ
  refine ⟨N, L, 1, C, hL0, le_rfl, hC0, fun τ hτ hτd => ?_⟩
  obtain ⟨CR, hCR, hfamτ⟩ := hfam τ hτ hτd
  -- the exponents and the threshold
  set μ : ℝ := β * ((d : ℝ) - τ) with hμ
  have hμ0 : 0 < μ := mul_pos hβ (by linarith)
  set μ' : ℝ := min μ ((k - (n - 1)) / 2) with hμ'
  have hμ'0 : 0 < μ' := lt_min hμ0 (by linarith)
  have hμ'μ : μ' ≤ μ := min_le_left _ _
  have hnk' : (n : ℝ) - 1 + μ' < k := by
    have := min_le_right μ ((k - (n - 1)) / 2)
    rw [← hμ'] at this
    linarith
  set C₁ : ℝ := 2 * Real.sqrt (2 ^ d) * ((1 + (d : ℝ) ^ 2) * Cc) with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  set sc : ℝ := scaleConst d Λ lam S₂ C₁ k μ' n with hsc
  set Xs : ℝ := (4 * |sc| + 1) ^ (1 / μ') with hXs
  have hXs1 : 1 ≤ Xs := Real.one_le_rpow (by linarith [abs_nonneg sc]) (by positivity)
  have hsA : ∀ s : ℝ, Xs ≤ s → sc * s ^ (-μ') ≤ 1 / 4 := fun s hs => by
    have hs0 : 0 < s := by linarith
    have h1 : s ^ (-μ') ≤ Xs ^ (-μ') :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hs (by linarith)
    have h2 : Xs ^ (-μ') = (4 * |sc| + 1)⁻¹ := by
      rw [hXs, ← Real.rpow_mul (by linarith [abs_nonneg sc]),
        show 1 / μ' * -μ' = -1 by field_simp, Real.rpow_neg_one]
    have h3 : 0 ≤ s ^ (-μ') := Real.rpow_nonneg hs0.le _
    calc sc * s ^ (-μ') ≤ |sc| * s ^ (-μ') := mul_le_mul_of_nonneg_right (le_abs_self _) h3
      _ ≤ |sc| * (4 * |sc| + 1)⁻¹ := by rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ ≤ 1 / 4 := by
          rw [mul_inv_le_iff₀ (by linarith [abs_nonneg sc])]
          linarith [abs_nonneg sc]
  set c₀ : ℝ := max Xs ((d : ℝ) + 1) with hc₀
  have hc₀0 : 0 < c₀ := lt_of_lt_of_le one_pos (hXs1.trans (le_max_left _ _))
  set Cτ : ℝ := (2 : ℝ) ^ τ⁻¹ * max (c₀ / Real.log 2 ^ τ⁻¹) CR with hCτ
  have hCτ0 : 0 < Cτ := by
    have h1 : 0 < c₀ / Real.log 2 ^ τ⁻¹ :=
      div_pos hc₀0 (Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _)
    have := Real.rpow_pos_of_pos (two_pos : (0 : ℝ) < 2) τ⁻¹
    exact mul_pos this (lt_max_of_lt_left h1)
  refine ⟨Cτ, hCτ0, fun P hP => ?_⟩
  have : IsProbabilityMeasure P := hP.1
  obtain ⟨D, R, hD, hRm, hRos, hR1, hRae⟩ := hfamτ P hP
  -- the frame and the tests of the law
  have hDs : ∀ ξ : Vec d, euclideanSq ξ ≤ dot ξ ((symmPart' D).mulVec ξ) ∧
      dot ξ ((symmPart' D).mulVec ξ) ≤ K' * euclideanSq ξ := fun ξ => by
    rw [dot_symmPart'_mulVec]
    exact hD ξ
  obtain ⟨A, hA⟩ := exists_profileFrame (symmPart'_transpose D) (fun ξ => (hDs ξ).1)
    (fun ξ => (hDs ξ).2)
  set ρ := adaptedRho A K' with hρ
  set χ := adaptedChi A K' with hχ
  have hPair : CompactProfilePair D ρ χ := compactProfilePair_adapted hd0 hA hK'0
  set e := Fintype.equivFin ι with he
  set ψ : Fin N → Vec d → ℝ := fun ℓ => compactTestFn ρ lam (e.symm ℓ).2 with hψdef
  have hLge : ∀ j ≤ n, Kρf j + (d : ℝ) * lam⁻¹ * Kρf j ≤ L := fun j hj =>
    Finset.single_le_sum (f := fun j => Kρf j + (d : ℝ) * lam⁻¹ * Kρf j)
      (fun i _ => add_nonneg (hKρf0 i) (mul_nonneg (by positivity) (hKρf0 i)))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  have hψ : ∀ ℓ, IsUnitTest (ψ ℓ) L := fun ℓ => by
    show IsUnitTest (compactTestFn ρ lam (e.symm ℓ).2) L
    generalize e.symm ℓ = p
    obtain ⟨j, α⟩ := p
    have hj : (j : ℕ) < n := j.2
    have h1 := hLge j hj.le
    have h2 := hLge (j + 1) hj
    have hK1 := hKρf0 ((j : ℕ) + 1)
    exact isUnitTest_compactTestFn hPair hlam0 hlam1 α (hKρf0 j) ((hKf j hA).1 α)
      ((hKf ((j : ℕ) + 1) hA).1) (by
        have : 0 ≤ (d : ℝ) * lam⁻¹ * Kρf j := mul_nonneg (by positivity) (hKρf0 j)
        linarith) (by linarith)
  have hχs : ContDiff ℝ ∞ χ := hPair.smooth_chi
  have hS₂ : ∀ j ≤ n, ∀ (α : Fin j → Fin d) i l y,
      |coordinateDerivative l (coordinateDerivative i (iterDeriv α χ)) y| ≤ S₂ := by
    intro j hj α i l y
    rw [coordinateDerivative_iterDeriv_eq_cons hχs α i,
      coordinateDerivative_iterDeriv_eq_cons hχs _ l]
    refine ((hKf (j + 2) hA).2 _ y).trans ?_
    exact Finset.single_le_sum (f := fun j => Kχf (j + 2)) (fun i _ => hKχf0 _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  have hKρ : ∀ (β : Fin n → Fin d) y, |iterDeriv β ρ y| ≤ Kρ := fun β y => (hKf n hA).1 β y
  refine ⟨ψ, hψ, fun z => ?_⟩
  -- the random radius at the center `z`
  obtain ⟨m, hm⟩ := exists_latticeShift_near z
  set y := latticeShift m with hy
  set w := z - y with hw
  have hT : MeasurePreserving (translate y) P P := ⟨measurable_translateCoefficient _, hP.2.1 m⟩
  set X : CoefficientField d Λ → ℝ := fun a => max c₀ (R (translate y a)) with hXdef
  have hc₀1 : 1 ≤ c₀ := hXs1.trans (le_max_left _ _)
  refine ⟨X, measurable_const.max (hRm.comp hT.measurable), ?_, fun a => ?_, ?_⟩
  · have h1 : OsBound P (fun _ => c₀) τ (c₀ / Real.log 2 ^ τ⁻¹) :=
      osBound_of_le_const measurable_const hτ hc₀0 (ae_of_all _ fun _ => le_rfl)
    have h2 : OsBound P (fun a => R (translate y a)) τ CR := hRos.comp_measurePreserving hT
    exact osBound_max h1 h2
  · exact hc₀1.trans (le_max_left _ _)
  · have hae := hT.quasiMeasurePreserving.ae hRae
    filter_upwards [hae] with a ha
    obtain ⟨Fc⟩ := ha
    intro S T hXS hST u t hSt htT
    set c := translate y a with hcdef
    set b := translate w c with hbdef
    have hbw : ∀ x, b.field x = c.field (w + x) := fun x => rfl
    have hbz : ∀ x, b.field x = a.field (z + x) := fun x => by
      show a.field (y + (w + x)) = a.field (z + x)
      congr 1
      rw [hw]
      abel
    have hwd : euclideanNorm w ≤ d := hm
    have hRc : 0 < R c := lt_of_lt_of_le one_pos (hR1 c)
    have hC₁c : 0 ≤ (1 + (d : ℝ) ^ 2) * Cc := by positivity
    let Fb := Fc.translate w hbw hwd hμ0.le hC₁c hRc
    have hXa : X a = max c₀ (R c) := rfl
    have hS1 : 1 ≤ S := hc₀1.trans ((le_max_left _ _).trans (hXa ▸ hXS))
    have hR₀S : max (R c) (d : ℝ) ≤ 2 * S := by
      have h1 : R c ≤ S := (le_max_right _ _).trans (hXa ▸ hXS)
      have h2 : (d : ℝ) + 1 ≤ S := (le_max_right _ _).trans ((le_max_left _ _).trans (hXa ▸ hXS))
      exact max_le (by linarith) (by linarith)
    have hsA' : sc * S ^ (-μ') ≤ 1 / 4 :=
      hsA S ((le_max_left _ _).trans ((le_max_left _ _).trans (hXa ▸ hXS)))
    have hST' : S ≤ T := by linarith
    set u' := u.shift (z' := 0) hbz (by simp) with hu'
    have hcore : scalarRms volume (ball 0 t) u'.potential ≤ (t / S) ^ k * (2 *
        (observationSum ρ lam n ((ball (0 : Vec d) T).indicator u'.potential) S +
          C' * (S / T) ^ k * scalarRms volume (ball 0 T) u'.potential)) :=
      compactTest_core hd0 Fb hΛ1 hμ0.le hC₁0 hPair hlam0 hlam1 hS₂0 hS₂ hKρ hk.le
        hμ'0 hμ'μ hnk hnk' hlam hS1 hR₀S hsA' hST' u' hSt htT
    -- the observations
    have hS0 : 0 < S := by linarith
    have hT0 : 0 < T := by linarith
    have ht0 : 0 < t := by linarith
    set O : ι → ℝ := fun p => (volume.real (ball z S))⁻¹ *
      ∫ x in ball z T, u.potential x * scaledTest (compactTestFn ρ lam p.2) z S x with hOdef
    have hobs : observationSum ρ lam n ((ball (0 : Vec d) T).indicator u'.potential) S ≤ Cobs * ∑ p : ι, |O p| := by
      have hterm : ∀ (j : ℕ) (α : Fin j → Fin d), j ≤ n →
          S ^ j * |profileAverage ρ lam α ((ball (0 : Vec d) T).indicator u'.potential) S 0| ≤
            Cobs * |(volume.real (ball z S))⁻¹ *
              ∫ x in ball z T, u.potential x * scaledTest (compactTestFn ρ lam α) z S x| := by
        intro j α hj
        have h := pow_mul_profileAverage_eq (ρ := ρ) hlam0 hS0 α (T := T) u'.potential
        rw [← abs_of_nonneg (pow_nonneg hS0.le j), ← abs_mul, h, setIntegral_shift_mul_scaledTest,
          volume_real_ball_center z S, abs_mul, abs_mul,
          abs_of_nonneg (pow_nonneg (inv_nonneg.2 hlam0.le) _), abs_of_nonneg hV₁0.le]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (one_le_inv₀ hlam0 |>.mpr hlam1)
          (by omega)) hV₁0.le
      calc observationSum ρ lam n ((ball (0 : Vec d) T).indicator u'.potential) S
          = ∑ j ∈ Finset.range n, ∑ α : Fin j → Fin d, S ^ j * |profileAverage ρ lam α ((ball (0 : Vec d) T).indicator u'.potential) S 0| := by
            unfold observationSum
            exact Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _
        _ ≤ ∑ j ∈ Finset.range n, ∑ α : Fin j → Fin d, Cobs *
            |(volume.real (ball z S))⁻¹ *
              ∫ x in ball z T, u.potential x * scaledTest (compactTestFn ρ lam α) z S x| :=
            Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun α _ =>
              hterm j α (Finset.mem_range.mp hj).le
        _ = Cobs * ∑ p : ι, |O p| := by
            rw [Finset.mul_sum, Fintype.sum_sigma, Finset.sum_range]
  -- the outer term and the root mean squares
    have hMT : scalarRms volume (ball 0 T) u'.potential ^ 2 =
        (volume.real (ball z T))⁻¹ * ∫ x in ball z T, u.potential x ^ 2 := by
      rw [scalarRms_shift u hbz T, Real.sq_sqrt (mul_nonneg (inv_nonneg.2 measureReal_nonneg)
        (integral_nonneg fun _ => sq_nonneg _))]
    have hMt : ∫ x in ball z t, u.potential x ^ 2 =
        volume.real (ball z t) * scalarRms volume (ball 0 t) u'.potential ^ 2 := by
      rw [scalarRms_shift u hbz t, Real.sq_sqrt (mul_nonneg (inv_nonneg.2 measureReal_nonneg)
        (integral_nonneg fun _ => sq_nonneg _)), ← mul_assoc,
        mul_inv_cancel₀ (volume_real_ball_pos z ht0).ne', one_mul]
    -- the final algebra
    have hJ0 : 0 ≤ observationSum ρ lam n ((ball (0 : Vec d) T).indicator u'.potential) S := Finset.sum_nonneg fun j _ =>
      mul_nonneg (pow_nonneg hS0.le _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    have hMT0 : 0 ≤ scalarRms volume (ball 0 T) u'.potential := Real.sqrt_nonneg _
    have hMt0 : 0 ≤ scalarRms volume (ball 0 t) u'.potential := Real.sqrt_nonneg _
    clear_value u'
    obtain ⟨J, hJ⟩ : ∃ J, J = observationSum ρ lam n ((ball (0 : Vec d) T).indicator u'.potential) S :=
      ⟨_, rfl⟩
    obtain ⟨MT, hMTe⟩ : ∃ MT, MT = scalarRms volume (ball 0 T) u'.potential := ⟨_, rfl⟩
    obtain ⟨Mt, hMte⟩ : ∃ Mt, Mt = scalarRms volume (ball 0 t) u'.potential := ⟨_, rfl⟩
    rw [← hJ, ← hMTe, ← hMte] at hcore
    rw [← hJ] at hobs hJ0
    rw [← hMTe] at hMT hMT0
    rw [← hMte] at hMt hMt0
    set Q2 := ∑ ℓ : Fin N, ((volume.real (ball z S))⁻¹ *
      ∫ x in ball z T, u.potential x * scaledTest (ψ ℓ) z S x) ^ 2 with hQ2
    have hQsum : ∑ p : ι, O p ^ 2 = Q2 := by
      rw [hQ2]
      exact (e.symm.sum_comp (fun p => O p ^ 2)).symm
    have hC'0 : 0 ≤ C' := by
      have : 0 ≤ outerConst d lam Kρ n := by
        unfold outerConst
        have := hKρf0 n
        positivity
      rw [hC']
      positivity
    have hq1 : 0 ≤ (t / S) ^ k := Real.rpow_nonneg (div_pos ht0 hS0).le _
    have hq2 : 0 ≤ (S / T) ^ k := Real.rpow_nonneg (div_pos hS0 hT0).le _
    have hsq1 : ((t / S) ^ k) ^ 2 = (t / S) ^ (2 * k) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (div_pos ht0 hS0).le]
      congr 1; push_cast; ring
    have hsq2 : ((S / T) ^ k) ^ 2 = (S / T) ^ (2 * k) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (div_pos hS0 hT0).le]
      congr 1; push_cast; ring
    have hJ2 : J ^ 2 ≤ Cobs ^ 2 * N * Q2 := by
      have h1 : J ^ 2 ≤ (Cobs * ∑ p : ι, |O p|) ^ 2 := pow_le_pow_left₀ hJ0 hobs 2
      have h2 := sq_sum_abs_le_card_mul O
      rw [hQsum] at h2
      calc J ^ 2 ≤ (Cobs * ∑ p : ι, |O p|) ^ 2 := h1
        _ = Cobs ^ 2 * (∑ p : ι, |O p|) ^ 2 := by ring
        _ ≤ Cobs ^ 2 * (N * Q2) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
        _ = Cobs ^ 2 * N * Q2 := by ring
    have hQ0' : 0 ≤ Q2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hQ0 : 0 ≤ MT ^ 2 := sq_nonneg _
    have hMt2 : Mt ^ 2 ≤ ((t / S) ^ k) ^ 2 * (4 * (J + C' * (S / T) ^ k * MT) ^ 2) := by
      have h := pow_le_pow_left₀ hMt0 hcore 2
      calc Mt ^ 2 ≤ ((t / S) ^ k * (2 * (J + C' * (S / T) ^ k * MT))) ^ 2 := h
        _ = ((t / S) ^ k) ^ 2 * (4 * (J + C' * (S / T) ^ k * MT) ^ 2) := by ring
    have hA2 : (J + C' * (S / T) ^ k * MT) ^ 2 ≤
        2 * (J ^ 2 + C' ^ 2 * ((S / T) ^ k) ^ 2 * MT ^ 2) := by
      have e : 2 * (J ^ 2 + C' ^ 2 * ((S / T) ^ k) ^ 2 * MT ^ 2) -
          (J + C' * (S / T) ^ k * MT) ^ 2 = (J - C' * (S / T) ^ k * MT) ^ 2 := by ring
      exact sub_nonneg.mp (by rw [e]; exact sq_nonneg _)
    rw [hMt, ← hMT]
    have hVt : 0 ≤ volume.real (ball z t) := measureReal_nonneg
    calc volume.real (ball z t) * Mt ^ 2
        ≤ volume.real (ball z t) * (((t / S) ^ k) ^ 2 *
            (4 * (2 * (J ^ 2 + C' ^ 2 * ((S / T) ^ k) ^ 2 * MT ^ 2)))) := by
          refine mul_le_mul_of_nonneg_left (hMt2.trans ?_) hVt
          exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
      _ ≤ volume.real (ball z t) * (((t / S) ^ k) ^ 2 *
            (8 * (Cobs ^ 2 * N * Q2 + C' ^ 2 * ((S / T) ^ k) ^ 2 * MT ^ 2))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)) hVt
          linarith [hJ2]
      _ ≤ C * (Q2 + ((S / T) ^ k) ^ 2 * MT ^ 2) * (((t / S) ^ k) ^ 2 *
            volume.real (ball z t)) := by
          have hCN : 8 * (Cobs ^ 2 * N) ≤ C := by
            rw [hCdef]; linarith [sq_nonneg C']
          have hCC : 8 * C' ^ 2 ≤ C := by
            rw [hCdef]
            have : 0 ≤ Cobs ^ 2 * (N : ℝ) := by positivity
            linarith
          have hq : 0 ≤ ((t / S) ^ k) ^ 2 * volume.real (ball z t) := by positivity
          have e1 : volume.real (ball z t) * (((t / S) ^ k) ^ 2 *
              (8 * (Cobs ^ 2 * N * Q2 + C' ^ 2 * ((S / T) ^ k) ^ 2 * MT ^ 2))) =
              (8 * (Cobs ^ 2 * N) * Q2 + 8 * C' ^ 2 * (((S / T) ^ k) ^ 2 * MT ^ 2)) *
                (((t / S) ^ k) ^ 2 * volume.real (ball z t)) := by ring
          rw [e1]
          refine mul_le_mul_of_nonneg_right ?_ hq
          have hX0 : 0 ≤ ((S / T) ^ k) ^ 2 * MT ^ 2 := by positivity
          have h := add_le_add (mul_le_mul_of_nonneg_right hCN hQ0')
            (mul_le_mul_of_nonneg_right hCC hX0)
          exact le_of_le_of_eq h (by ring)
      _ = _ := by rw [hsq2, hsq1]

/-- **The finite-ball observation of the proof of Lemma 4.21**, for every growth exponent `k > 0`:
`σ, θ ∈ (0, 1/2]` and constants chosen before the law, and at every center a random radius
`X ≤ O_τ(C_τ)`, `τ < d`, above which `∫_{B_S(z)} u² ≤ C (|B_S| I + (S/T)^{2k} ∫_{B_T(z)} u²)` for
the `a`-harmonic functions on `B_T(z)`, `T ≥ L₀ S`, with `I` the truncated Gaussian observation. -/
theorem finiteBallObservation_of_laws (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) {k : ℝ} (hk : 0 < k) :
    ∃ σ θ : ℝ, 0 < σ ∧ σ ≤ 1 / 2 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧
      ∃ (L₀ C : ℝ), 1 ≤ L₀ ∧ 0 < C ∧ ∀ τ : ℝ, 0 < τ → τ < d → ∃ Cτ : ℝ, 0 < Cτ ∧
        ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ z : Vec d,
          ∃ X : CoefficientField d Λ → ℝ, Measurable X ∧ OsBound P X τ Cτ ∧ (∀ a, 1 ≤ X a) ∧
            ∀ᵐ a ∂P, ∀ S T : ℝ, X a ≤ S → L₀ * S ≤ T → ∀ u : LocalHarmonic a z T,
              ∫ x in ball z S, u.potential x ^ 2 ≤
                C * (volume.real (ball z S) * localizationObjective z T S σ θ u.potential +
                  (S / T) ^ (2 * k) * ∫ x in ball z T, u.potential x ^ 2) :=
  finiteBallObservation_of_compactTestsLaw hk.le (compactTestFiniteBallLaw hd hΛ hk)

end QSH
