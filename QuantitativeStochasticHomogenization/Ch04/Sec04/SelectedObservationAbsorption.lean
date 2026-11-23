import QuantitativeStochasticHomogenization.Ch04.Sec04.SlopeFromObservation
import QuantitativeStochasticHomogenization.Ch04.Sec04.CoordinateMinimizerCoercivity

/-!
# Absorption of the outer term in the finite-ball observation

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.21, the observation step. For an `a`-harmonic `u` on `B_T(z)` and
`0 < S ≤ T`, the mean `m` of `u` on `B_T` satisfies `|B_S| m² ≤ 2 ∫_{B_S} u² + 2 ∫_{B_T} (u - m)²`,
so the outer energy `∫_{B_T} u²` is at most `2 (|B_T|/|B_S|) ∫_{B_S} u²` plus a Poincaré term
`(1 + 2|B_T|/|B_S|) (2^d 2T)² ∫_{B_T} |∇u|²`. In a finite-ball observation estimate
`∫_{B_S} u² ≤ C (|B_S| I + q ∫_{B_T} u²)` with `2 C q |B_T|/|B_S| ≤ 1/2` the outer term is then
absorbed. The difference `w - h` of two local harmonic functions is a local harmonic function.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ} {a : CoefficientField d Λ} {z : Vec d} {T : ℝ}

/-- **The difference of two local harmonic functions.** -/
def LocalHarmonic.sub (w h : LocalHarmonic a z T) : LocalHarmonic a z T where
  potential := fun x => w.potential x - h.potential x
  grad := fun x => w.grad x - h.grad x
  square_integrable := w.square_integrable.sub h.square_integrable
  gradient_square_integrable := by
    refine (w.gradient_square_integrable.add h.gradient_square_integrable).of_le ?_
      (Eventually.of_forall fun x => ?_)
    · exact euclideanNorm_continuous.comp_aestronglyMeasurable
        ((AEMeasurable.of_eval (f := fun x => w.grad x)
            fun i => (w.memLp_grad i).aestronglyMeasurable.aemeasurable).sub
          (AEMeasurable.of_eval (f := fun x => h.grad x)
            fun i => (h.memLp_grad i).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
    · simp only [Real.norm_eq_abs, Pi.add_apply]
      rw [abs_of_nonneg (zero_le_euclideanNorm _),
        abs_of_nonneg (add_nonneg (zero_le_euclideanNorm _) (zero_le_euclideanNorm _))]
      have := euclideanNorm_add_le_add (w.grad x) (-h.grad x)
      rw [← sub_eq_add_neg] at this
      have hneg : euclideanNorm (-h.grad x) = euclideanNorm (h.grad x) := by
        unfold euclideanNorm euclideanSq dot
        congr 1
        exact Finset.sum_congr rfl fun i _ => by simp
      linarith
  weak_gradient := hasWeakGradient_sub w.weak_gradient h.weak_gradient
  harmonic := by
    have h1 := hasWeakDivergence_sub w.harmonic h.harmonic
    have e1 : (fun x => (a x).mulVec (w.grad x - h.grad x)) =
        fun x => (a x).mulVec (w.grad x) - (a x).mulVec (h.grad x) := by
      funext x
      rw [Matrix.mulVec_sub]
    have e2 : (fun _ : Vec d => (0 : ℝ)) = fun _ => (0 : ℝ) - 0 := by
      funext x
      ring
    rw [e1, e2]
    exact h1

/-- **Poincaré inequality for local harmonic functions** on `B_T(z)`. -/
theorem LocalHarmonic.integral_sub_average_sq_le (w : LocalHarmonic a z T) (hT : 0 < T) :
    ∫ x in ball z T, (w.potential x - ⨍ y in ball z T, w.potential y) ^ 2 ≤
      (2 ^ d * (2 * T)) ^ 2 * ∫ x in ball z T, euclideanSq (w.grad x) := by
  have h := _root_.QSH.integral_sub_average_sq_le w.toPair w.isHarmonicPair_toPair hT
  rw [← w.integral_euclideanSq_grad] at h
  have hav : (⨍ y in ball z T, w.toPair.1 y) = ⨍ y in ball z T, w.potential y := by
    simp only [setAverage_eq]
    rw [integral_congr_ae w.toPair_fst_ae]
  have hint : (∫ x in ball z T, (w.toPair.1 x - ⨍ y in ball z T, w.toPair.1 y) ^ 2) =
      ∫ x in ball z T, (w.potential x - ⨍ y in ball z T, w.potential y) ^ 2 := by
    rw [hav]
    refine integral_congr_ae ?_
    filter_upwards [w.toPair_fst_ae] with x hx
    rw [hx]
  rw [← hint]
  exact h

/-- **The outer energy from the inner energy and the mean oscillation.** -/
theorem integral_sq_le_of_inner {u : Vec d → ℝ} {S : ℝ} (hS : 0 < S) (hST : S ≤ T)
    (hu : MemLp u 2 (volume.restrict (ball z T))) :
    ∫ x in ball z T, u x ^ 2 ≤
      2 * (volume.real (ball z T) / volume.real (ball z S)) * (∫ x in ball z S, u x ^ 2) +
        (1 + 2 * (volume.real (ball z T) / volume.real (ball z S))) *
          ∫ x in ball z T, (u x - ⨍ y in ball z T, u y) ^ 2 := by
  have hT : 0 < T := lt_of_lt_of_le hS hST
  obtain ⟨m, hm⟩ : ∃ m, m = ⨍ y in ball z T, u y := ⟨_, rfl⟩
  rw [← hm]
  have hBT : 0 < volume.real (ball z T) := volume_real_ball_pos z hT
  have hBS : 0 < volume.real (ball z S) := volume_real_ball_pos z hS
  have hsub : ball z S ⊆ ball z T := fun x hx => lt_of_lt_of_le hx hST
  have hu1 : Integrable u (volume.restrict (ball z T)) := hu.integrable one_le_two
  have hu2 : Integrable (fun x => u x ^ 2) (volume.restrict (ball z T)) := hu.integrable_sq
  have hum : MemLp (fun x => u x - m) 2 (volume.restrict (ball z T)) := hu.sub (memLp_const m)
  have hum2 : Integrable (fun x => (u x - m) ^ 2) (volume.restrict (ball z T)) :=
    hum.integrable_sq
  have hmean : ∫ x in ball z T, u x = volume.real (ball z T) * m := by
    rw [hm, setAverage_eq, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hBT.ne', one_mul]
  have e : ∫ x in ball z T, (u x - m) ^ 2 =
      ∫ x in ball z T, (u x ^ 2 - 2 * m * u x + m ^ 2) :=
    integral_congr_ae (Eventually.of_forall fun x => by ring)
  have he2 : ∫ x in ball z T, (u x ^ 2 - 2 * m * u x + m ^ 2) =
      (∫ x in ball z T, u x ^ 2) - 2 * m * (∫ x in ball z T, u x) +
        volume.real (ball z T) * m ^ 2 := by
    have i3 : Integrable (fun x => 2 * m * u x) (volume.restrict (ball z T)) :=
      hu1.const_mul (2 * m)
    have i1 : Integrable (fun x => u x ^ 2 - 2 * m * u x) (volume.restrict (ball z T)) :=
      hu2.sub i3
    rw [integral_add i1 (integrable_const _), integral_sub hu2 i3, integral_const_mul,
      setIntegral_const, smul_eq_mul]
  rw [hmean] at he2
  have hvar : ∫ x in ball z T, u x ^ 2 =
      (∫ x in ball z T, (u x - m) ^ 2) + volume.real (ball z T) * m ^ 2 := by
    rw [e, he2]
    ring
  -- the mean from the inner ball
  have hS2 : Integrable (fun x => u x ^ 2) (volume.restrict (ball z S)) :=
    hu2.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hSm2 : Integrable (fun x => (u x - m) ^ 2) (volume.restrict (ball z S)) :=
    hum2.mono_measure (Measure.restrict_mono hsub le_rfl)
  have h1 : volume.real (ball z S) * m ^ 2 = ∫ x in ball z S, m ^ 2 := by
    rw [setIntegral_const, smul_eq_mul]
  have h2 : ∫ x in ball z S, m ^ 2 ≤ ∫ x in ball z S, (2 * u x ^ 2 + 2 * (u x - m) ^ 2) :=
    integral_mono (integrable_const _) ((hS2.const_mul 2).add (hSm2.const_mul 2))
      fun x => by nlinarith [sq_nonneg (2 * u x - m)]
  have h2' : ∫ x in ball z S, (2 * u x ^ 2 + 2 * (u x - m) ^ 2) =
      2 * (∫ x in ball z S, u x ^ 2) + 2 * ∫ x in ball z S, (u x - m) ^ 2 := by
    rw [integral_add (hS2.const_mul 2) (hSm2.const_mul 2), integral_const_mul,
      integral_const_mul]
  have h3 : ∫ x in ball z S, (u x - m) ^ 2 ≤ ∫ x in ball z T, (u x - m) ^ 2 :=
    setIntegral_mono_set hum2 (Eventually.of_forall fun x => sq_nonneg _) hsub.eventuallyLE
  have hmS : volume.real (ball z S) * m ^ 2 ≤
      2 * (∫ x in ball z S, u x ^ 2) + 2 * ∫ x in ball z T, (u x - m) ^ 2 := by
    rw [h1]
    linarith
  set X := volume.real (ball z T) / volume.real (ball z S) with hX
  have hX0 : 0 ≤ X := div_nonneg hBT.le hBS.le
  have hq := mul_le_mul_of_nonneg_left hmS hX0
  have e1 : X * (volume.real (ball z S) * m ^ 2) = volume.real (ball z T) * m ^ 2 := by
    rw [hX]; field_simp
  rw [e1] at hq
  rw [hvar]
  calc (∫ x in ball z T, (u x - m) ^ 2) + volume.real (ball z T) * m ^ 2
      ≤ (∫ x in ball z T, (u x - m) ^ 2) +
          X * (2 * (∫ x in ball z S, u x ^ 2) + 2 * ∫ x in ball z T, (u x - m) ^ 2) := by
        linarith
    _ = 2 * X * (∫ x in ball z S, u x ^ 2) + (1 + 2 * X) * ∫ x in ball z T, (u x - m) ^ 2 := by
        ring

end QSH
