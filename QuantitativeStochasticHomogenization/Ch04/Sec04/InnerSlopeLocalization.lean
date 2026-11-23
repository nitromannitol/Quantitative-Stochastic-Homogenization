import QuantitativeStochasticHomogenization.Ch04.Sec04.BallGrowthLocalization
import QuantitativeStochasticHomogenization.Ch04.Sec04.CorrectedSpanEnergy

/-!
# Ball growth from the single-slope estimate below the intermediate scale

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.21. The ball-growth bounds
`∫_{B_T(z) ∩ B_t(z)} |∇w_i - W_i - ∑_j b_{ij} W_j|² ≤ A (t/r)^k |B_t|` for all `t ≥ r` follow
from two estimates:

* below a radius `S₁ ≤ T`, the single-slope estimate
  `∫_{B_t(z)} |∇w_i - W_i - ∑_j b_{ij} W_j|² ≤ K (t/r)² |B_t|` for `r ≤ t ≤ S₁` (the excess decay
  of the selected coordinate with one slope, as given by Theorem C of Armstrong, Kuusi and Loher);
* on `B_T(z)`, the total bound `3 (C₀² + E₁ + d² E₁ / 4) |B_T|`, from the admissibility cap
  `C₀` of the selected coordinates, `∫_{B_T(z)} |W_j|² ≤ E₁ |B_T|` and `∑ b_{ij}² ≤ 1/4`.

Above `S₁` the total bound costs the factor `M` of `T^d ≤ M (S₁/r)^k S₁^d`. With `S₁ = c S`,
`S = r^{1+δ-ε}`, `T = r^{1+δ}` and `k (δ - ε) ≥ 2γ + d ε`, one may take `M = c^{-(d+k)} r^{-2γ}`.
This reduces the frozen statement (5.85) to the single-slope estimate on a good event.
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ}

theorem euclideanSq_sub_add_le (u v w : Vec d) :
    euclideanSq (u - (v + w)) ≤ 3 * (euclideanSq u + euclideanSq v + euclideanSq w) := by
  simp only [euclideanSq, dot, Pi.sub_apply, Pi.add_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ => by
    nlinarith [sq_nonneg (u k + v k), sq_nonneg (u k + w k), sq_nonneg (v k - w k)]

/-- The admissibility cap bounds the energy: `∫_{B_T(z)} |∇w|² ≤ C² |B_T(z)|`. -/
theorem integral_euclideanSq_grad_le_of_admissible {Λ : ℝ} {a : CoefficientField d Λ}
    {z : Vec d} {T : ℝ} (hT : 0 < T) {C : ℝ} {w : LocalHarmonic a z T}
    (hw : IsLocalizationAdmissible C w) :
    ∫ x in ball z T, euclideanSq (w.grad x) ≤ C ^ 2 * volume.real (ball z T) := by
  have hV := volume_real_ball_pos z hT
  have havg : ⨍ x in ball z T, euclideanSq (w.grad x) ∂volume =
      (volume.real (ball z T))⁻¹ * ∫ x in ball z T, euclideanSq (w.grad x) := by
    rw [setAverage_eq, smul_eq_mul]
  have h0 : 0 ≤ ⨍ x in ball z T, euclideanSq (w.grad x) ∂volume := by
    rw [havg]
    exact mul_nonneg (inv_nonneg.mpr hV.le)
      (setIntegral_nonneg (measurableSet_ball z T) fun x _ => zero_le_euclideanSq _)
  have hle : ⨍ x in ball z T, euclideanSq (w.grad x) ∂volume ≤ C ^ 2 := by
    have h1 : Real.sqrt (⨍ x in ball z T, euclideanSq (w.grad x) ∂volume) ≤ C := hw
    rw [← Real.sq_sqrt h0]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  rw [havg] at hle
  have := mul_le_mul_of_nonneg_left hle hV.le
  rwa [← mul_assoc, mul_inv_cancel₀ hV.ne', one_mul, mul_comm] at this

/-- The pathwise hypotheses of Lemma 4.21 with the single-slope estimate below `S₁`: those of
`LocalizationBallGrowthData` with the ball-growth bounds replaced by
`∫_{B_t(z)} |∇w_i - W_i - ∑_j b_{ij} W_j|² ≤ K (t/r)² |B_t|` for `r ≤ t ≤ S₁`, together with the
energy bounds `∫_{B_T(z)} |W_j|² ≤ E₁ |B_T(z)|`. -/
def LocalizationInnerSlopeData {Λ : ℝ} (a : CoefficientField d Λ) (z : Vec d) (T S₁ r : ℝ)
    {S σ θ C : ℝ} (B : LocalizedBasis a z T S σ θ C) (E E₁ K : ℝ) : Prop :=
  ∃ (φ : Fin d → Vec d → ℝ) (g : Fin d → Vec d → Vec d),
    (∀ i, HasWeakGradient Set.univ (φ i) (g i)) ∧
    (∀ i, ∀ R : ℝ, 0 < R → MemLp (φ i) 2 (volume.restrict (ball 0 R)) ∧
      MemLp (g i) 2 (volume.restrict (ball 0 R))) ∧
    (∀ i, HasWeakDivergence Set.univ (fun x => (a x).mulVec (unitVector i + g i x))
      (fun _ => 0)) ∧
    (∃ (c : Fin d → ℝ) (ε : ℝ), (d : ℝ) * ε ^ 2 ≤ (1 / 4 : ℝ) ^ d / 16 ∧
      ∀ i, ∫ x in ball z r, (φ i x - c i) ^ 2 ≤ ε ^ 2 * r ^ 2 * volume.real (ball z r)) ∧
    (∀ i, Integrable (fun x => heatKernel z (Real.sqrt 2 * r) x *
      euclideanSq (unitVector i + g i x))) ∧
    (∀ i, ∫ x, heatKernel z (Real.sqrt 2 * r) x * euclideanSq (unitVector i + g i x) ≤ E) ∧
    (∀ i, ∫ x in ball z T, euclideanSq (unitVector i + g i x) ≤
      E₁ * volume.real (ball z T)) ∧
    (∀ w : HarmonicA1 a, ∃ ξ : Vec d,
      ∀ᵐ x, w.grad x = ∑ i, ξ i • (unitVector i + g i x)) ∧
    (∀ ξ : Vec d, ∃ w : HarmonicA1 a,
      ∀ᵐ x, w.grad x = ∑ i, ξ i • (unitVector i + g i x)) ∧
    ∃ b : Fin d → Fin d → ℝ, ∑ i, ∑ j, b i j ^ 2 ≤ 1 / 4 ∧
      ∀ i, ∀ t : ℝ, r ≤ t → t ≤ S₁ → ∫ x in ball z t,
        euclideanSq ((B.coordinate i).grad x -
          ((unitVector i + g i x) + ∑ j, b i j • (unitVector j + g j x))) ≤
            K * (t / r) ^ 2 * volume.real (ball z t)

theorem sq_le_of_sum_sum_sq_le {b : Fin d → Fin d → ℝ} {β : ℝ}
    (hb : ∑ i, ∑ j, b i j ^ 2 ≤ β) (i j : Fin d) : b i j ^ 2 ≤ β := by
  have h1 : b i j ^ 2 ≤ ∑ j', b i j' ^ 2 :=
    Finset.single_le_sum (f := fun j' => b i j' ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ j)
  have h2 : ∑ j', b i j' ^ 2 ≤ ∑ i', ∑ j', b i' j' ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', b i' j' ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  linarith

/-- **Ball growth from the single-slope estimate below `S₁` and the total bound on `B_T`.** -/
theorem LocalizationInnerSlopeData.toBallGrowthData {Λ : ℝ} {a : CoefficientField d Λ}
    {z : Vec d} {T S₁ r : ℝ} {S σ θ C : ℝ} {B : LocalizedBasis a z T S σ θ C} {E E₁ K : ℝ}
    (h : LocalizationInnerSlopeData a z T S₁ r B E E₁ K) (hr : 0 < r) (hS₁ : 0 < S₁)
    (hS₁T : S₁ ≤ T) (hK : 0 ≤ K) (hE₁ : 0 ≤ E₁) {k : ℕ} (hk : 2 ≤ k) {M : ℝ} (hM : 0 ≤ M)
    (hbudget : T ^ d ≤ M * (S₁ / r) ^ k * S₁ ^ d) :
    LocalizationBallGrowthData a z T r B k E
      (K + 3 * (C ^ 2 + E₁ + d * d * E₁ / 4) * M) := by
  obtain ⟨φ, g, hφg, hloc, harm, hosc, hW, hE, hE₁b, hrep, hWmem, b, hb, hinner⟩ := h
  refine ⟨φ, g, hφg, hloc, harm, hosc, hW, hE, hrep, hWmem, b, hb, fun i t hrt => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le hr hrt
  have hD0 : 0 ≤ 3 * (C ^ 2 + E₁ + d * d * E₁ / 4) * M := by positivity
  have hratio : 1 ≤ t / r := (one_le_div hr).mpr hrt
  have hpow : (t / r) ^ 2 ≤ (t / r) ^ k := pow_le_pow_right₀ hratio hk
  have hVt := volume_real_ball_pos z ht0
  have h3 : 0 ≤ 3 * (C ^ 2 + E₁ + d * d * E₁ / 4) * M * (t / r) ^ k *
      volume.real (ball z t) := by positivity
  have h4 : 0 ≤ K * (t / r) ^ k * volume.real (ball z t) := by positivity
  by_cases htS : t ≤ S₁
  · have hsub : ball z t ⊆ ball z T := fun x (hx : euclideanNorm (x - z) < t) =>
      (lt_of_lt_of_le hx (htS.trans hS₁T) : euclideanNorm (x - z) < T)
    rw [Set.inter_eq_right.mpr hsub]
    have h1 := hinner i t hrt htS
    have h2 : K * (t / r) ^ 2 * volume.real (ball z t) ≤
        K * (t / r) ^ k * volume.real (ball z t) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hK) hVt.le
    linarith
  · replace htS := not_le.mp htS
    have hT0 : 0 < T := lt_of_lt_of_le hS₁ hS₁T
    let uT := fun j => localCorrectedCoordinate a z T j 0 (φ j) (g j) (hφg j) (hloc j) (harm j)
    have hWk : ∀ j k', MemLp (fun x => (unitVector j + g j x) k') 2 (ballMeasure z T) :=
      fun j k' => (uT j).memLp_grad k'
    have hWi : ∀ j, IntegrableOn (fun x => euclideanSq (unitVector j + g j x)) (ball z T) :=
      fun j => (integrable_finsetSum Finset.univ fun k' _ => (hWk j k').integrable_sq).congr
        (Eventually.of_forall fun x => by simp only [euclideanSq, dot, sq])
    have hwi : IntegrableOn (fun x => euclideanSq ((B.coordinate i).grad x)) (ball z T) :=
      (integrable_finsetSum Finset.univ fun k' _ =>
        ((B.coordinate i).memLp_grad k').integrable_sq).congr
        (Eventually.of_forall fun x => by simp only [euclideanSq, dot, sq])
    have hGk : ∀ k', MemLp (fun x => ((B.coordinate i).grad x -
        ((unitVector i + g i x) + ∑ j, b i j • (unitVector j + g j x))) k') 2
          (ballMeasure z T) := by
      intro k'
      refine MemLp.ae_eq (Eventually.of_forall fun x => ?_)
        (((B.coordinate i).memLp_grad k').sub ((hWk i k').add
          (memLp_finsetSum Finset.univ fun j _ => (hWk j k').const_mul (b i j))))
      simp only [Pi.sub_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hfi : IntegrableOn (fun x => euclideanSq ((B.coordinate i).grad x -
        ((unitVector i + g i x) + ∑ j, b i j • (unitVector j + g j x)))) (ball z T) :=
      (integrable_finsetSum Finset.univ fun k' _ => (hGk k').integrable_sq).congr
        (Eventually.of_forall fun x => by simp only [euclideanSq, dot, sq])
    have hpt : ∀ x, euclideanSq ((B.coordinate i).grad x -
        ((unitVector i + g i x) + ∑ j, b i j • (unitVector j + g j x))) ≤
        3 * (euclideanSq ((B.coordinate i).grad x) + euclideanSq (unitVector i + g i x) +
          d * (1 / 4) * ∑ j, euclideanSq (unitVector j + g j x)) := by
      intro x
      have h1 := euclideanSq_sub_add_le ((B.coordinate i).grad x) (unitVector i + g i x)
        (∑ j, b i j • (unitVector j + g j x))
      have h2 : euclideanSq (∑ j, b i j • (unitVector j + g j x)) ≤
          d * ∑ j, b i j ^ 2 * euclideanSq (unitVector j + g j x) :=
        euclideanSq_sum_smul_le (b i) (fun j => unitVector j + g j x)
      have h5 : ∑ j, b i j ^ 2 * euclideanSq (unitVector j + g j x) ≤
          ∑ j, 1 / 4 * euclideanSq (unitVector j + g j x) :=
        Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (sq_le_of_sum_sum_sq_le hb i j) (zero_le_euclideanSq _)
      rw [← Finset.mul_sum] at h5
      have h6 := mul_le_mul_of_nonneg_left h5 (Nat.cast_nonneg (α := ℝ) d)
      linarith
    have hsumi : Integrable (fun x => ∑ j, euclideanSq (unitVector j + g j x))
        (volume.restrict (ball z T)) := integrable_finsetSum Finset.univ fun j _ => hWi j
    have hgi : Integrable (fun x => 3 * (euclideanSq ((B.coordinate i).grad x) +
        euclideanSq (unitVector i + g i x) +
          d * (1 / 4) * ∑ j, euclideanSq (unitVector j + g j x)))
        (volume.restrict (ball z T)) :=
      ((hwi.add (hWi i)).add (hsumi.const_mul _)).const_mul 3
    have hint_eq : ∫ x in ball z T, 3 * (euclideanSq ((B.coordinate i).grad x) +
        euclideanSq (unitVector i + g i x) +
          d * (1 / 4) * ∑ j, euclideanSq (unitVector j + g j x)) =
        3 * ((∫ x in ball z T, euclideanSq ((B.coordinate i).grad x)) +
          (∫ x in ball z T, euclideanSq (unitVector i + g i x)) +
          d * (1 / 4) * ∑ j, ∫ x in ball z T, euclideanSq (unitVector j + g j x)) := by
      have hab : Integrable (fun x => euclideanSq ((B.coordinate i).grad x) +
          euclideanSq (unitVector i + g i x)) (volume.restrict (ball z T)) := hwi.add (hWi i)
      have hc : Integrable (fun x => (d : ℝ) * (1 / 4) *
          ∑ j, euclideanSq (unitVector j + g j x)) (volume.restrict (ball z T)) :=
        hsumi.const_mul _
      rw [integral_const_mul, integral_add hab hc, integral_add hwi (hWi i), integral_const_mul,
        integral_finsetSum _ fun j _ => hWi j]
    have hwle := integral_euclideanSq_grad_le_of_admissible hT0 (B.selected i).1.1
    have hsumle : ∑ j, ∫ x in ball z T, euclideanSq (unitVector j + g j x) ≤
        d * (E₁ * volume.real (ball z T)) := by
      calc ∑ j, ∫ x in ball z T, euclideanSq (unitVector j + g j x)
          ≤ ∑ _j : Fin d, E₁ * volume.real (ball z T) := Finset.sum_le_sum fun j _ => hE₁b j
        _ = d * (E₁ * volume.real (ball z T)) := by simp
    have hd4 : (0 : ℝ) ≤ d * (1 / 4) := by positivity
    have houter : ∫ x in ball z T, euclideanSq ((B.coordinate i).grad x -
        ((unitVector i + g i x) + ∑ j, b i j • (unitVector j + g j x))) ≤
        3 * (C ^ 2 + E₁ + d * d * E₁ / 4) * volume.real (ball z T) := by
      have hmono := integral_mono_of_nonneg (Eventually.of_forall fun x =>
        zero_le_euclideanSq ((B.coordinate i).grad x -
          ((unitVector i + g i x) + ∑ j, b i j • (unitVector j + g j x)))) hgi
        (Eventually.of_forall hpt)
      rw [hint_eq] at hmono
      have h7 := mul_le_mul_of_nonneg_left hsumle hd4
      have h8 := hE₁b i
      linarith
    have hset : ∫ x in ball z T ∩ ball z t, euclideanSq ((B.coordinate i).grad x -
        ((unitVector i + g i x) + ∑ j, b i j • (unitVector j + g j x))) ≤
        ∫ x in ball z T, euclideanSq ((B.coordinate i).grad x -
          ((unitVector i + g i x) + ∑ j, b i j • (unitVector j + g j x))) :=
      setIntegral_mono_set hfi (Eventually.of_forall fun x => zero_le_euclideanSq _)
        (Set.inter_subset_left).eventuallyLE
    have hVT := volume_real_ball_eq_mul z hT0
    have hVt' := volume_real_ball_eq_mul z ht0
    have hV1 := volume_real_ball_pos (0 : Vec d) one_pos
    have hgrow : T ^ d ≤ M * (t / r) ^ k * t ^ d := by
      have h9 : (S₁ / r) ^ k ≤ (t / r) ^ k :=
        pow_le_pow_left₀ (div_nonneg hS₁.le hr.le)
          (div_le_div_of_nonneg_right htS.le hr.le) k
      have h10 : S₁ ^ d ≤ t ^ d := pow_le_pow_left₀ hS₁.le htS.le d
      calc T ^ d ≤ M * (S₁ / r) ^ k * S₁ ^ d := hbudget
        _ ≤ M * (t / r) ^ k * t ^ d := by gcongr
    have hfinal : 3 * (C ^ 2 + E₁ + d * d * E₁ / 4) * volume.real (ball z T) ≤
        3 * (C ^ 2 + E₁ + d * d * E₁ / 4) * M * (t / r) ^ k * volume.real (ball z t) := by
      have hc3 : 0 ≤ 3 * (C ^ 2 + E₁ + d * d * E₁ / 4) := by positivity
      rw [hVT, hVt']
      have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hgrow hV1.le) hc3
      linarith
    linarith

theorem LocalizationBallGrowthData.mono {Λ : ℝ} {a : CoefficientField d Λ} {z : Vec d}
    {T r : ℝ} {S σ θ C : ℝ} {B : LocalizedBasis a z T S σ θ C} {k : ℕ} {E A A' : ℝ}
    (h : LocalizationBallGrowthData a z T r B k E A) (hr : 0 < r) (hAA : A ≤ A') :
    LocalizationBallGrowthData a z T r B k E A' := by
  obtain ⟨φ, g, hφg, hloc, harm, hosc, hW, hE, hrep, hWmem, b, hb, hgrowth⟩ := h
  refine ⟨φ, g, hφg, hloc, harm, hosc, hW, hE, hrep, hWmem, b, hb, fun i t hrt => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le hr hrt
  have h0 : 0 ≤ (t / r) ^ k * volume.real (ball z t) :=
    mul_nonneg (pow_nonneg (div_nonneg ht0.le hr.le) k) measureReal_nonneg
  have := mul_le_mul_of_nonneg_right hAA h0
  calc _ ≤ A * (t / r) ^ k * volume.real (ball z t) := hgrowth i t hrt
    _ = A * ((t / r) ^ k * volume.real (ball z t)) := by ring
    _ ≤ A' * ((t / r) ^ k * volume.real (ball z t)) := this
    _ = A' * (t / r) ^ k * volume.real (ball z t) := by ring

/-- **The outer budget**: for `r ≥ 1`, `T = r^{1+δ}`, `S = r^{1+δ-ε}` and
`2γ + d ε ≤ k (δ - ε)`, `T^d ≤ r^{-2γ} (S/r)^k S^d`. -/
theorem localizationOuterRadius_pow_le {δ ε γ r : ℝ} (hr : 1 ≤ r) {k : ℕ}
    (hk : 2 * γ + d * ε ≤ k * (δ - ε)) :
    localizationOuterRadius δ r ^ d ≤
      (r ^ (-γ)) ^ 2 * (r ^ (1 + δ - ε) / r) ^ k * (r ^ (1 + δ - ε)) ^ d := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hSr : r ^ (1 + δ - ε) / r = r ^ (δ - ε) := by
    rw [← Real.rpow_sub_one hr0.ne']
    congr 1
    ring
  unfold localizationOuterRadius
  rw [hSr, ← Real.rpow_mul_natCast hr0.le, ← Real.rpow_mul_natCast hr0.le,
    ← Real.rpow_mul_natCast hr0.le, ← Real.rpow_mul_natCast hr0.le, ← Real.rpow_add hr0,
    ← Real.rpow_add hr0]
  apply Real.rpow_le_rpow_of_exponent_le hr
  push_cast
  nlinarith [hk]

/-- **The single-slope estimate of Lemma 4.21 on a good event** (the remaining analytic input of
(5.85) in this form): there are `c ∈ (0, 1]`, `E, E₁, K₁ ≥ 0` and `C₁ > 0` such that for every law,
every localized family, center and scale `r ≥ 2` there are nonnegative random variables `X` and
`Y` with `X^γ ≤ O_s(C₁)` and `Y ≤ O_s(C₁ r^{-γ})`, and almost surely, if `X ≤ r`, then
`LocalizationInnerSlopeData` holds at `T = r^{1+δ}` below `S₁ = c S`, `S = r^{1+δ-ε}`, with
Gaussian energy bound `E`, energy bound `E₁` on `B_T` and single-slope constant `K₁ Y²`. -/
def LocalizationInnerSlopeEstimate (d : ℕ) (Λ s δ γ α σ θ C₀ : ℝ) : Prop :=
  ∃ (c E E₁ K₁ C₁ : ℝ), 0 < c ∧ c ≤ 1 ∧ 0 ≤ E ∧ 0 ≤ E₁ ∧ 0 ≤ K₁ ∧ 0 < C₁ ∧
    ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∀ (W : LocalizedFamily d Λ δ γ α σ θ C₀) (z : Vec d) (r : ℝ) (hr : 2 ≤ r),
        ∃ X Y : CoefficientField d Λ → ℝ, (∀ a, 0 ≤ X a) ∧ (∀ a, 0 ≤ Y a) ∧
          AEOsBound P (fun a => X a ^ γ) s C₁ ∧ AEOsBound P Y s (C₁ * r ^ (-γ)) ∧
          ∀ᵐ a ∂P, X a ≤ r →
            LocalizationInnerSlopeData a z (localizationOuterRadius δ r)
              (c * localizationIntermediateRadius δ α γ r) r (W a z r hr) E E₁ (K₁ * Y a ^ 2)

/-- `LocalizationInnerSlopeEstimate` for the laws of a class `L`. -/
def LocalizationInnerSlopeEstimateOn {d : ℕ} {Λ : ℝ} (L : Measure (CoefficientField d Λ) → Prop)
    (s δ γ α σ θ C₀ : ℝ) : Prop :=
  ∃ (c E E₁ K₁ C₁ : ℝ), 0 < c ∧ c ≤ 1 ∧ 0 ≤ E ∧ 0 ≤ E₁ ∧ 0 ≤ K₁ ∧ 0 < C₁ ∧
    ∀ P : Measure (CoefficientField d Λ), L P →
      ∀ (W : LocalizedFamily d Λ δ γ α σ θ C₀) (z : Vec d) (r : ℝ) (hr : 2 ≤ r),
        ∃ X Y : CoefficientField d Λ → ℝ, (∀ a, 0 ≤ X a) ∧ (∀ a, 0 ≤ Y a) ∧
          AEOsBound P (fun a => X a ^ γ) s C₁ ∧ AEOsBound P Y s (C₁ * r ^ (-γ)) ∧
          ∀ᵐ a ∂P, X a ≤ r →
            LocalizationInnerSlopeData a z (localizationOuterRadius δ r)
              (c * localizationIntermediateRadius δ α γ r) r (W a z r hr) E E₁ (K₁ * Y a ^ 2)

theorem localizationEpsilon_pos {δ α γ : ℝ} (hδ : 0 < δ) (hα : 0 < α)
    (hαγ : γ < α * (1 + δ) + δ) : 0 < localizationEpsilon δ α γ :=
  lt_min (div_pos (by linarith) (by linarith)) (by linarith)

/-- **The ball-growth estimate from the single-slope estimate**, with
`k = max 2 ⌈(2γ + d ε)/(δ - ε)⌉` and `K = K₁ + 3 (C₀² + E₁ + d² E₁/4) c^{-(d+k)}`. -/
theorem localizationBallGrowthEstimateOn_of_innerSlopeOn {Λ s δ γ α σ θ C₀ : ℝ}
    {L : Measure (CoefficientField d Λ) → Prop} (hδ : 0 < δ)
    (hα : 0 < α) (hαγ : γ < α * (1 + δ) + δ)
    (h : LocalizationInnerSlopeEstimateOn L s δ γ α σ θ C₀) :
    LocalizationBallGrowthEstimateOn L s δ γ α σ θ C₀ := by
  obtain ⟨c, E, E₁, K₁, C₁, hc, hc1, hE, hE₁, hK₁, hC₁, hmain⟩ := h
  set ε := localizationEpsilon δ α γ with hε_def
  have hε0 : 0 < ε := localizationEpsilon_pos hδ hα hαγ
  have hεδ : ε ≤ δ / 2 := min_le_right _ _
  have hδε : 0 < δ - ε := by linarith
  set k : ℕ := max 2 ⌈(2 * γ + d * ε) / (δ - ε)⌉₊ with hk_def
  have hk2 : 2 ≤ k := le_max_left _ _
  have hkb : 2 * γ + d * ε ≤ k * (δ - ε) := by
    have h1 : (2 * γ + d * ε) / (δ - ε) ≤ k :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
    rwa [div_le_iff₀ hδε] at h1
  have hD0 : 0 ≤ 3 * (C₀ ^ 2 + E₁ + d * d * E₁ / 4) := by positivity
  have hck : 0 < c ^ (d + k) := pow_pos hc _
  refine ⟨k, E, K₁ + 3 * (C₀ ^ 2 + E₁ + d * d * E₁ / 4) * (c ^ (d + k))⁻¹, C₁, hE,
    by positivity, hC₁,
    fun P hP W z r hr => ?_⟩
  obtain ⟨X, Y, hX0, hY0, hXos, hYos, hae⟩ := hmain P hP W z r hr
  refine ⟨X, Y, hX0, hY0, hXos, hYos, ?_⟩
  filter_upwards [hae] with a ha hXr
  have hr0 : 0 < r := by linarith
  have hr1 : 1 ≤ r := by linarith
  set S := localizationIntermediateRadius δ α γ r with hS_def
  set T := localizationOuterRadius δ r with hT_def
  have hS0 : 0 < S := Real.rpow_pos_of_pos hr0 _
  have hST : S ≤ T := Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
  have hS₁T : c * S ≤ T := (mul_le_of_le_one_left hS0.le hc1).trans hST
  have hrγ : 0 ≤ r ^ (-γ) := (Real.rpow_pos_of_pos hr0 _).le
  have hM0 : 0 ≤ (c ^ (d + k))⁻¹ * (r ^ (-γ)) ^ 2 := by positivity
  have hbudget : T ^ d ≤ (c ^ (d + k))⁻¹ * (r ^ (-γ)) ^ 2 * (c * S / r) ^ k * (c * S) ^ d := by
    have hb := localizationOuterRadius_pow_le (d := d) (γ := γ) hr1 hkb
    have heq : (c ^ (d + k))⁻¹ * (r ^ (-γ)) ^ 2 * (c * S / r) ^ k * (c * S) ^ d =
        (r ^ (-γ)) ^ 2 * (S / r) ^ k * S ^ d := by
      rw [mul_div_assoc, mul_pow, mul_pow, pow_add]
      field_simp
    rw [heq]
    exact hb
  have hdat := (ha hXr).toBallGrowthData hr0 (mul_pos hc hS0) hS₁T
    (mul_nonneg hK₁ (sq_nonneg _)) hE₁ hk2 hM0 hbudget
  refine hdat.mono hr0 ?_
  have h1 : 0 ≤ K₁ * (r ^ (-γ)) ^ 2 := by positivity
  have h2 : 0 ≤ 3 * (C₀ ^ 2 + E₁ + d * d * E₁ / 4) * (c ^ (d + k))⁻¹ * Y a ^ 2 := by
    positivity
  have h3 : (K₁ + 3 * (C₀ ^ 2 + E₁ + d * d * E₁ / 4) * (c ^ (d + k))⁻¹) *
      (Y a ^ 2 + (r ^ (-γ)) ^ 2) =
      K₁ * Y a ^ 2 + 3 * (C₀ ^ 2 + E₁ + d * d * E₁ / 4) * ((c ^ (d + k))⁻¹ * (r ^ (-γ)) ^ 2) +
        (K₁ * (r ^ (-γ)) ^ 2 +
          3 * (C₀ ^ 2 + E₁ + d * d * E₁ / 4) * (c ^ (d + k))⁻¹ * Y a ^ 2) := by ring
  rw [h3]
  linarith

theorem localizationBallGrowthEstimate_of_innerSlope {Λ s δ γ α σ θ C₀ : ℝ} (hδ : 0 < δ)
    (hα : 0 < α) (hαγ : γ < α * (1 + δ) + δ)
    (h : LocalizationInnerSlopeEstimate d Λ s δ γ α σ θ C₀) :
    LocalizationBallGrowthEstimate d Λ s δ γ α σ θ C₀ :=
  localizationBallGrowthEstimateOn_of_innerSlopeOn (L := LawHypotheses) hδ hα hαγ h

/-- **(5.85) from the single-slope estimate of Lemma 4.21.** For every window of exponents, a
choice of the structural constants `α, σ, θ, C₀` with `LocalizationInnerSlopeEstimate` gives the
frozen statement `QSH.Frozen.localizedEnergy`. -/
theorem localizedEnergy_of_innerSlope
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ s δ γ : ℝ,
      1 < Λ → 1 < s → s < 2 → 0 < δ →
      (d : ℝ) / 2 * (1 + δ) < γ →
      γ < min ((d : ℝ) / s) ((d : ℝ) / 2 * (1 + δ) + δ) →
      ∃ α σ θ C₀ : ℝ, 0 < α ∧ α ≤ (d : ℝ) / 2 ∧ γ < α * (1 + δ) + δ ∧
        0 < σ ∧ σ ≤ 1 / 2 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ 0 < C₀ ∧
        LocalizationInnerSlopeEstimate d Λ s δ γ α σ θ C₀) :
    QSH.Frozen.localizedEnergy :=
  localizedEnergy_of_ballGrowth fun d hd Λ s δ γ hΛ hs1 hs2 hδ hγ1 hγ2 => by
    obtain ⟨α, σ, θ, C₀, hα, hαd, hαγ, hσ, hσ2, hθ, hθ2, hC₀, hest⟩ :=
      h d hd Λ s δ γ hΛ hs1 hs2 hδ hγ1 hγ2
    exact ⟨α, σ, θ, C₀, hα, hαd, hαγ, hσ, hσ2, hθ, hθ2, hC₀,
      localizationBallGrowthEstimate_of_innerSlope hδ hα hαγ hest⟩

end QSH
