import QuantitativeStochasticHomogenization.Ch03.Sec03.QuarterExcessStep
import QuantitativeStochasticHomogenization.Ch04.Sec04.TranslatedCorrectorBounds
import QuantitativeStochasticHomogenization.Ch04.Sec04.LocalizationTranslation
import QuantitativeStochasticHomogenization.Ch03.Sec03.ScalarRmsCalculus

/-!
# Translation of a family of correctors

A family of first-order and skew flux correctors for the coefficient field `c`, centered at the
origin, gives one for the translated field `b(x) = c(w + x)`: translate every corrector by `w`.
For `|w| ≤ R` the ball `B_R(w)` lies in `B_{2R}`, and the mean on `B_R` minimizes the square
deviation, so the oscillation on `B_R` of a translated corrector is at most `2^{d/2}` times its
oscillation on `B_{2R}`: the translated family has the oscillation bound `2^{d/2+1} C₁ R^{1-μ}` above
`max R₀ ρ₀` when `|w| ≤ ρ₀` (`SublinearCorrectorFamily.translate`). This moves the first-order
estimates of Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, Lemma 3.17 and Proposition 6.2, from a lattice point to a nearby center.
-/

open MeasureTheory Filter Set

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

theorem HasWeakGradient.comp_add_left {f : Vec d → ℝ} {G : Vec d → Vec d}
    (h : HasWeakGradient Set.univ f G) (w : Vec d) :
    HasWeakGradient Set.univ (fun x => f (w + x)) (fun x => G (w + x)) := by
  have h' := h.comp_sub (-w)
  have e1 : (fun x => f (x - -w)) = fun x => f (w + x) := by
    funext x; rw [sub_neg_eq_add, add_comm]
  have e2 : (fun x => G (x - -w)) = fun x => G (w + x) := by
    funext x; rw [sub_neg_eq_add, add_comm]
  rwa [e1, e2] at h'

theorem HasWeakDivergence.comp_add_left {G : Vec d → Vec d} {h : Vec d → ℝ}
    (H : HasWeakDivergence Set.univ G h) (w : Vec d) :
    HasWeakDivergence Set.univ (fun x => G (w + x)) (fun x => h (w + x)) := by
  obtain ⟨hG, hh, hibp⟩ := H
  have hloc : ∀ {f : Vec d → ℝ}, LocallyIntegrableOn f Set.univ volume →
      LocallyIntegrableOn (fun x => f (w + x)) Set.univ volume := fun {f} hf => by
    have := locallyIntegrable_comp_sub (locallyIntegrableOn_univ.mp hf) (-w)
    rw [locallyIntegrableOn_univ]
    refine this.congr ?_
    exact Eventually.of_forall fun x => by simp only [sub_neg_eq_add, add_comm]
  refine ⟨fun i => hloc (hG i), hloc hh, fun φ hφ => ?_⟩
  have htest : IsSpatialTest Set.univ (fun u => φ (u + -w)) := isSpatialTest_comp_add hφ (-w)
  have h1 := hibp _ htest
  simp only [Measure.restrict_univ] at h1 ⊢
  have hgrad : ∀ u, gradient (fun u => φ (u + -w)) u = gradient φ (u + -w) := fun u => by
    funext i
    exact coordinateDerivative_comp_add i φ (-w) u
  simp only [hgrad] at h1
  have e1 := integral_add_left_eq_self (μ := (volume : Measure (Vec d)))
    (fun u => dot (G u) (gradient φ (u + -w))) w
  have e2 := integral_add_left_eq_self (μ := (volume : Measure (Vec d)))
    (fun u => h u * φ (u + -w)) w
  simp only [add_neg_cancel_comm] at e1 e2
  rw [e1, e2, h1]

/-- **The oscillation of a translated function**: for `|w| ≤ R`, the oscillation on `B_R` of
`f(w + ·)` is at most `2^{d/2}` times the oscillation of `f` on `B_{2R}`. -/
theorem scalarRms_translate_le {f : Vec d → ℝ} {w : Vec d} {R : ℝ} (hR : 0 < R)
    (hwR : euclideanNorm w ≤ R) (hf : MemLp f 2 (volume.restrict (ball 0 (2 * R)))) :
    scalarRms volume (ball 0 R) (fun x => f (w + x) - ⨍ y in ball 0 R, f (w + y)) ≤
      Real.sqrt (2 ^ d) * scalarRms volume (ball 0 (2 * R))
        (fun x => f x - ⨍ y in ball 0 (2 * R), f y) := by
  have h2R : 0 < 2 * R := by positivity
  set m := ⨍ y in ball 0 (2 * R), f y with hm
  have hsub : ball w R ⊆ ball (0 : Vec d) (2 * R) := fun y hy => by
    have hy' : euclideanNorm (y - w) < R := hy
    show euclideanNorm (y - 0) < 2 * R
    have := euclideanNorm_add_le (y - w) w
    rw [sub_add_cancel] at this
    rw [sub_zero]
    linarith
  have hfw : MemLp (fun x => f (w + x)) 2 (volume.restrict (ball 0 R)) :=
    MemLp.ball_add (c := w) (z := w) (z' := 0) (by simp) ((hf.mono_measure (Measure.restrict_mono hsub le_rfl)))
  have hV0 : volume (ball (0 : Vec d) R) ≠ 0 := (volume_ball_zero_pos hR).ne'
  have hVt : volume (ball (0 : Vec d) R) ≠ ⊤ := (volume_ball_zero_lt_top R).ne
  have h1 := setAverage_sq_sub_setAverage_le hV0 hVt hfw m
  have hint : IntegrableOn (fun y => (f y - m) ^ 2) (ball (0 : Vec d) (2 * R)) :=
    (hf.sub (memLp_const m)).integrable_sq
  have hcv : ∫ x in ball 0 R, (f (w + x) - m) ^ 2 = ∫ y in ball w R, (f y - m) ^ 2 :=
    setIntegral_ball_add (c := w) (z := w) (z' := 0) (by simp) R (fun y => (f y - m) ^ 2)
  have hmono : ∫ y in ball w R, (f y - m) ^ 2 ≤ ∫ y in ball 0 (2 * R), (f y - m) ^ 2 :=
    setIntegral_mono_set hint (Eventually.of_forall fun _ => sq_nonneg _) hsub.eventuallyLE
  have hV : volume.real (ball (0 : Vec d) (2 * R)) = 2 ^ d * volume.real (ball (0 : Vec d) R) := by
    rw [volume_real_ball_eq_mul 0 h2R, volume_real_ball_eq_mul 0 hR, mul_pow]
    ring
  have hVR := volume_real_ball_pos (0 : Vec d) hR
  unfold scalarRms
  rw [← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt (h1.trans ?_)
  rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul, hcv, hV]
  rw [mul_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  exact mul_le_mul_of_nonneg_left hmono (inv_nonneg.2 hVR.le)

variable {c b : CoefficientField d Λ} {D : Mat d} {μ C₁ R₀ : ℝ}

/-- **The translated family of correctors** for `b(x) = c(w + x)`, `|w| ≤ ρ₀`. -/
def SublinearCorrectorFamily.translate (F : SublinearCorrectorFamily c D μ C₁ R₀) (w : Vec d)
    (hb : ∀ x, b.field x = c.field (w + x)) {ρ₀ : ℝ} (hw : euclideanNorm w ≤ ρ₀)
    (hμ : 0 ≤ μ) (hC₁ : 0 ≤ C₁) (hR₀ : 0 < R₀) :
    SublinearCorrectorFamily b D μ (2 * Real.sqrt (2 ^ d) * C₁) (max R₀ ρ₀) where
  φ := fun i x => F.φ i (w + x)
  gφ := fun i x => F.gφ i (w + x)
  σ := fun i x => F.σ i (w + x)
  gσ := fun i j k x => F.gσ i j k (w + x)
  weak_gradient_φ := fun i => (F.weak_gradient_φ i).comp_add_left w
  weak_gradient_σ := fun i j k => (F.weak_gradient_σ i j k).comp_add_left w
  memLp := fun i R hR => by
    have hsub : ball w R ⊆ ball (0 : Vec d) (R + euclideanNorm w) := fun y hy => by
      have hy' : euclideanNorm (y - w) < R := hy
      show euclideanNorm (y - 0) < _
      have := euclideanNorm_add_le (y - w) w
      rw [sub_add_cancel] at this
      rw [sub_zero]
      linarith
    have hR' : 0 < R + euclideanNorm w := by
      have : 0 ≤ euclideanNorm w := Real.sqrt_nonneg (euclideanSq w)
      linarith
    obtain ⟨h1, h2, h3⟩ := F.memLp i _ hR'
    have hz : w + (0 : Vec d) = w := by simp
    refine ⟨MemLp.ball_add hz ((h1.mono_measure (Measure.restrict_mono hsub le_rfl))),
      MemLp.ball_add hz (h2.mono_measure (Measure.restrict_mono hsub le_rfl)),
      fun j k => ⟨MemLp.ball_add hz (((h3 j k).1.mono_measure (Measure.restrict_mono hsub le_rfl))),
        MemLp.ball_add hz ((h3 j k).2.mono_measure (Measure.restrict_mono hsub le_rfl))⟩⟩
  harmonic := fun i => by
    have h := (F.harmonic i).comp_add_left w
    have e : (fun x => (b x).mulVec (unitVector i + F.gφ i (w + x))) =
        fun x => (c (w + x)).mulVec (unitVector i + F.gφ i (w + x)) := by
      funext x
      rw [show (b x) = b.field x from rfl, hb x]
    rw [e]
    exact h
  flux := fun i j => by
    have h := (F.flux i j).comp_add_left w
    have e : (fun x => (b x).mulVec (unitVector i + F.gφ i (w + x)) j - D.mulVec (unitVector i) j) =
        fun x => (c (w + x)).mulVec (unitVector i + F.gφ i (w + x)) j -
          D.mulVec (unitVector i) j := by
      funext x
      rw [show (b x) = b.field x from rfl, hb x]
    rw [e]
    exact h
  skew := fun i x j k => F.skew i (w + x) j k
  oscillation := fun i R hR => by
    have hR0 : 0 < R := lt_of_lt_of_le hR₀ ((le_max_left _ _).trans hR)
    have hwR : euclideanNorm w ≤ R := hw.trans ((le_max_right _ _).trans hR)
    have h2R : R₀ ≤ 2 * R := by
      have := (le_max_left R₀ ρ₀).trans hR
      linarith
    have hosc := F.oscillation i (2 * R) h2R
    obtain ⟨h1, -, h3⟩ := F.memLp i (2 * R) (by positivity)
    have hφ := scalarRms_translate_le hR0 hwR h1
    have hσ := fun j k => scalarRms_translate_le hR0 hwR (h3 j k).1
    have hsum : ∑ j, ∑ k, scalarRms volume (ball 0 R)
        (fun x => F.σ i (w + x) j k - ⨍ y in ball 0 R, F.σ i (w + y) j k) ≤
        Real.sqrt (2 ^ d) * ∑ j, ∑ k, scalarRms volume (ball 0 (2 * R))
          (fun x => F.σ i x j k - ⨍ y in ball 0 (2 * R), F.σ i y j k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun k _ => hσ j k
    have h2 : (2 * R) ^ (1 - μ) ≤ 2 * R ^ (1 - μ) := by
      rw [Real.mul_rpow (by norm_num) hR0.le]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hR0.le _)
      calc (2 : ℝ) ^ (1 - μ) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    change scalarRms volume (ball 0 R) (fun x => F.φ i (w + x) - ⨍ y in ball 0 R, F.φ i (w + y)) +
      ∑ j, ∑ k, scalarRms volume (ball 0 R)
        (fun x => F.σ i (w + x) j k - ⨍ y in ball 0 R, F.σ i (w + y) j k) ≤
      2 * Real.sqrt (2 ^ d) * C₁ * R ^ (1 - μ)
    calc _ ≤ Real.sqrt (2 ^ d) * (scalarRms volume (ball 0 (2 * R))
          (fun x => F.φ i x - ⨍ y in ball 0 (2 * R), F.φ i y) +
          ∑ j, ∑ k, scalarRms volume (ball 0 (2 * R))
            (fun x => F.σ i x j k - ⨍ y in ball 0 (2 * R), F.σ i y j k)) := by
          rw [mul_add]; exact add_le_add hφ hsum
      _ ≤ Real.sqrt (2 ^ d) * (C₁ * (2 * R) ^ (1 - μ)) :=
          mul_le_mul_of_nonneg_left hosc (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt (2 ^ d) * (C₁ * (2 * R ^ (1 - μ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hC₁) (Real.sqrt_nonneg _)
      _ = 2 * Real.sqrt (2 ^ d) * C₁ * R ^ (1 - μ) := by ring

end QSH
