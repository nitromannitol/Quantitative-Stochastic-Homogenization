import QuantitativeStochasticHomogenization.Ch03.Sec03.CorrectedAffine
import QuantitativeStochasticHomogenization.Ch03.Sec04.WeakGradientCentering
import QuantitativeStochasticHomogenization.Ch03.Sec04.BallMeanSquareScaling
import QuantitativeStochasticHomogenization.Ch03.Sec04.WeakGradientDilation

/-!
# Linear independence of the corrected affine gradients

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 3.4: almost surely, the gradients `p + ∑ᵢ pᵢ ∇φ_{eᵢ}` of the corrected affine functions
vanish only for `p = 0`. Testing the vanishing gradient against the dilations `ψ(·/R)` of a bump
function gives `p ∫ ψ(·/R) = ∑ᵢ pᵢ ∫ (φ_{eᵢ} - (φ_{eᵢ})_{B_{ρR}}) ∂ψ(·/R)`, whose right side is
`o(R^d)` by the sublinearity of the correctors. With `ae_exists_harmonicA1_correctedAffine` this
gives `dim A₁ = d + 1` once every element of `A₁` is corrected affine.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- `(∫_B |f|)² ≤ |B| ∫_B f²` in the form `∫_B |f| ≤ √(|B| ∫_B f²)`. -/
theorem setIntegral_abs_le_sqrt {B : Set (Vec d)} (hB : volume B < ⊤) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict B)) :
    ∫ x in B, |f x| ≤ Real.sqrt (volume.real B * ∫ x in B, f x ^ 2) := by
  have hfin : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hB.ne
  have hi1 : Integrable (fun x => |f x|) (volume.restrict B) :=
    (hf.integrable one_le_two).abs
  have hi2 : Integrable (fun x => f x ^ 2) (volume.restrict B) := hf.integrable_sq
  set I1 := ∫ x in B, |f x| with hI1
  set I2 := ∫ x in B, f x ^ 2 with hI2
  set V := volume.real B with hV
  have hV0 : 0 ≤ V := measureReal_nonneg
  have key : I1 ^ 2 ≤ V * I2 := by
    rcases hV0.lt_or_eq with hVpos | hVeq
    · have h := integral_nonneg (μ := volume.restrict B) (f := fun x => (|f x| * V - I1) ^ 2)
        fun x => sq_nonneg _
      have hexp : (fun x => (|f x| * V - I1) ^ 2) =
          fun x => V ^ 2 * f x ^ 2 - (2 * V * I1) * |f x| + I1 ^ 2 := by
        funext x
        rw [show (|f x| * V - I1) ^ 2 = V ^ 2 * |f x| ^ 2 - (2 * V * I1) * |f x| + I1 ^ 2 by ring,
          sq_abs]
      have hA : Integrable (fun x => V ^ 2 * f x ^ 2 - (2 * V * I1) * |f x|)
          (volume.restrict B) := (hi2.const_mul _).sub (hi1.const_mul _)
      rw [hexp, integral_add hA (integrable_const _),
        integral_sub (hi2.const_mul _) (hi1.const_mul _), integral_const_mul, integral_const_mul,
        setIntegral_const, smul_eq_mul] at h
      rw [← hV, ← hI1, ← hI2] at h
      nlinarith
    · have hVeq' : V = 0 := hVeq.symm
      have hB0 : volume B = 0 := by
        have h := hVeq'
        rw [hV, measureReal_def, ENNReal.toReal_eq_zero_iff] at h
        exact h.resolve_right hB.ne
      have : I1 = 0 := by
        rw [hI1, Measure.restrict_eq_zero.mpr hB0, integral_zero_measure]
      rw [this, hVeq']
      simp
  calc I1 ≤ |I1| := le_abs_self _
    _ = Real.sqrt (I1 ^ 2) := (Real.sqrt_sq_eq_abs I1).symm
    _ ≤ Real.sqrt (V * I2) := Real.sqrt_le_sqrt key

private theorem isSpatialTest_comp_inv_smul {ψ : Vec d → ℝ} (hψ : IsSpatialTest Set.univ ψ)
    {R : ℝ} (hR : 0 < R) : IsSpatialTest Set.univ (fun x => ψ (R⁻¹ • x)) :=
  ⟨hψ.1.comp (contDiff_const_smul R⁻¹), hψ.2.1.comp_smul (inv_ne_zero hR.ne'),
    Set.subset_univ _⟩

private theorem coordinateDerivative_comp_inv_smul {ψ : Vec d → ℝ} (hψ : Differentiable ℝ ψ)
    (R : ℝ) (j : Fin d) (x : Vec d) :
    coordinateDerivative j (fun x => ψ (R⁻¹ • x)) x = R⁻¹ * coordinateDerivative j ψ (R⁻¹ • x) := by
  simp only [coordinateDerivative]
  exact fderiv_comp_smul_apply hψ R⁻¹ x (unitVector j)

private theorem euclideanNorm_le_card_mul_norm' (v : Vec d) : euclideanNorm v ≤ d * ‖v‖ := by
  unfold euclideanNorm euclideanSq dot
  rw [Real.sqrt_le_left]
  · calc ∑ i, v i * v i ≤ ∑ _i : Fin d, ‖v‖ * ‖v‖ := Finset.sum_le_sum fun i _ => by
          have h := norm_le_pi_norm v i
          rw [Real.norm_eq_abs] at h
          nlinarith [abs_nonneg (v i), abs_mul_abs_self (v i)]
      _ = d * (‖v‖ * ‖v‖) := by simp
      _ ≤ (d * ‖v‖) ^ 2 := by
          rcases Nat.eq_zero_or_pos d with hd | hd
          · subst hd; simp
          · have : (1 : ℝ) ≤ d := by exact_mod_cast hd
            nlinarith [norm_nonneg v, mul_nonneg (norm_nonneg v) (norm_nonneg v)]
  · positivity

private theorem euclideanNorm_smul_of_nonneg {c : ℝ} (hc : 0 ≤ c) (v : Vec d) :
    euclideanNorm (c • v) = c * euclideanNorm v := by
  unfold euclideanNorm euclideanSq dot
  have : ∑ i, (c • v) i * (c • v) i = c ^ 2 * ∑ i, v i * v i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [this, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- **Linear independence of the corrected affine gradients.** Almost surely, if
`p + ∑ᵢ pᵢ ∇φ_{eᵢ} = 0` almost everywhere then `p = 0`. -/
theorem ae_eq_zero_of_correctedAffineGrad_ae_eq_zero {Λ : ℝ}
    {P : Measure (CoefficientField d Λ)} (S : HomogenizationData P) :
    ∀ᵐ a ∂P, ∀ c : Vec d,
      (∀ᵐ x ∂(volume : Measure (Vec d)), correctedAffineGrad S a c x = 0) → c = 0 := by
  have hall : ∀ᵐ a ∂P, ∀ i : Fin d,
      HasWeakGradient Set.univ ((S.corrector (unitVector i)).potential a)
        ((S.corrector (unitVector i)).grad a) ∧
      (∀ R : ℝ, 0 < R →
        MemLp ((S.corrector (unitVector i)).potential a) 2 (volume.restrict (ball 0 R))) ∧
      Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R,
        ((S.corrector (unitVector i)).potential a x -
          ⨍ y in ball 0 R, (S.corrector (unitVector i)).potential a y ∂volume) ^ 2 ∂volume))
        atTop (𝓝 0) := by
    rw [ae_all_iff]
    intro i
    filter_upwards [(S.corrector (unitVector i)).weak_gradient,
      (S.corrector (unitVector i)).locally_square_integrable,
      (S.corrector (unitVector i)).sublinear] with a h1 h2 h4
    exact ⟨h1, fun R hR => (h2 R hR).1, h4⟩
  filter_upwards [hall] with a ha c hc
  let ψb : ContDiffBump (0 : Vec d) := ⟨1, 2, one_pos, one_lt_two⟩
  have hψtest : IsSpatialTest Set.univ (ψb : Vec d → ℝ) :=
    ⟨ψb.contDiff, ψb.hasCompactSupport, Set.subset_univ _⟩
  have hψdiff : Differentiable ℝ (ψb : Vec d → ℝ) := (ψb.contDiff (n := 1)).differentiable one_ne_zero
  have hψint : 0 < ∫ x, (ψb : Vec d → ℝ) x := ψb.integral_pos
  set ρ : ℝ := 2 * d + 1 with hρ
  have hρ0 : 0 < ρ := by positivity
  set V₁ := volume.real (ball (0 : Vec d) 1) with hV₁
  have hV₁0 : 0 < V₁ := ball_volume_pos_finite d 1 one_pos
  funext j
  obtain ⟨A, hA⟩ := (isSpatialTest_coordinateDerivative hψtest j).1.continuous.bounded_above_of_compact_support
    (isSpatialTest_coordinateDerivative hψtest j).2.1
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hsupp : ∀ y : Vec d, ρ ≤ euclideanNorm y → coordinateDerivative j ψb y = 0 := by
    intro y hy
    have hnot : y ∉ tsupport (ψb : Vec d → ℝ) := by
      rw [ψb.tsupport_eq]
      intro hmem
      have h1 : ‖y‖ ≤ 2 := by simpa [Metric.mem_closedBall, dist_zero_right] using hmem
      have h2 := euclideanNorm_le_card_mul_norm' y
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      nlinarith
    simp [coordinateDerivative, fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot]
  -- the potentials, their means on `B_{ρR}` and the dilated test functions
  set φ := fun i : Fin d => (S.corrector (unitVector i)).potential a with hφ
  set g := fun i : Fin d => (S.corrector (unitVector i)).grad a with hg
  set m : Fin d → ℝ → ℝ := fun i R => ⨍ y in ball 0 (ρ * R), φ i y ∂volume with hm
  have hident : ∀ R : ℝ, 0 < R → c j * (R ^ d * ∫ x, (ψb : Vec d → ℝ) x) =
      ∑ i, c i * ∫ x, (φ i x - m i R) * coordinateDerivative j (fun x => ψb (R⁻¹ • x)) x := by
    intro R hR
    have htest := isSpatialTest_comp_inv_smul hψtest hR
    have hψR : Integrable (fun x => ψb (R⁻¹ • x)) :=
      htest.1.continuous.integrable_of_hasCompactSupport htest.2.1
    have hgint : ∀ i, Integrable (fun x => g i x j * ψb (R⁻¹ • x)) := fun i => by
      have h := integrableOn_mul_spatialTest ((ha i).1 j).2.1 htest
      rwa [integrableOn_univ] at h
    have hzero : ∫ x, correctedAffineGrad S a c x j * ψb (R⁻¹ • x) = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hc] with x hx
      simp [hx]
    have hexpand : (fun x => correctedAffineGrad S a c x j * ψb (R⁻¹ • x)) =
        fun x => c j * ψb (R⁻¹ • x) + ∑ i, c i * (g i x j * ψb (R⁻¹ • x)) := by
      funext x
      simp only [correctedAffineGrad, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        add_mul, Finset.sum_mul, hg]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hexpand, integral_add (hψR.const_mul _) (integrable_finsetSum _ fun i _ =>
      (hgint i).const_mul _), integral_const_mul,
      integral_finsetSum _ fun i _ => (hgint i).const_mul _] at hzero
    have hweak : ∀ i, ∫ x, (φ i x - m i R) * coordinateDerivative j (fun x => ψb (R⁻¹ • x)) x =
        -∫ x, g i x j * ψb (R⁻¹ • x) := by
      intro i
      have h := ((hasWeakGradient_sub_const Set.univ (ha i).1 (m i R)) j).2.2 _ htest
      simpa only [Measure.restrict_univ] using h
    have hscale : ∫ x, (ψb : Vec d → ℝ) (R⁻¹ • x) = R ^ d * ∫ x, (ψb : Vec d → ℝ) x := by
      rw [Measure.integral_comp_inv_smul_of_nonneg volume (ψb : Vec d → ℝ) hR.le,
        Module.finrank_fin_fun, smul_eq_mul]
    rw [← hscale]
    simp only [integral_const_mul] at hzero
    have : ∑ i, c i * ∫ x, (φ i x - m i R) * coordinateDerivative j (fun x => ψb (R⁻¹ • x)) x =
        -∑ i, c i * ∫ x, g i x j * ψb (R⁻¹ • x) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [hweak i]; ring
    rw [this]
    linarith
  have hbound : ∀ i, ∀ R : ℝ, 0 < R →
      |∫ x, (φ i x - m i R) * coordinateDerivative j (fun x => ψb (R⁻¹ • x)) x| ≤
        A * V₁ * ρ ^ (d + 1) * R ^ d * ((ρ * R)⁻¹ * Real.sqrt (⨍ x in ball 0 (ρ * R),
          (φ i x - m i R) ^ 2)) := by
    intro i R hR
    have hρR : 0 < ρ * R := mul_pos hρ0 hR
    set B := ball (0 : Vec d) (ρ * R) with hB
    have hBm : MeasurableSet B := by
      have hU : IsOpen B := by
        rw [hB]; unfold ball euclideanNorm euclideanSq dot
        exact isOpen_lt (by fun_prop) continuous_const
      exact hU.measurableSet
    have hVB : volume.real B = (ρ * R) ^ d * V₁ := volume_real_euclideanBall _ hρR
    have hVBpos : 0 < volume.real B := ball_volume_pos_finite d _ hρR
    have hBfin : volume B < ⊤ := by
      by_contra hcon
      rw [not_lt, top_le_iff] at hcon
      rw [measureReal_def, hcon, ENNReal.toReal_top] at hVBpos
      exact lt_irrefl 0 hVBpos
    have hmemB : MemLp (fun x => φ i x - m i R) 2 (volume.restrict B) := by
      have hfinB : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hBfin.ne
      exact ((ha i).2.1 (ρ * R) hρR).sub (memLp_const _)
    have hvanish : ∀ x ∉ B, (φ i x - m i R) * coordinateDerivative j (fun x => ψb (R⁻¹ • x)) x = 0 := by
      intro x hx
      rw [coordinateDerivative_comp_inv_smul hψdiff]
      have hxn : ρ * R ≤ euclideanNorm x := by
        simpa [hB, ball, not_lt] using hx
      have : ρ ≤ euclideanNorm (R⁻¹ • x) := by
        rw [euclideanNorm_smul_of_nonneg (inv_nonneg.mpr hR.le)]
        rw [le_inv_mul_iff₀ hR]
        linarith [mul_comm ρ R]
      rw [hsupp _ this]
      ring
    have hint : Integrable (fun x => (φ i x - m i R) * coordinateDerivative j (fun x => ψb (R⁻¹ • x)) x) := by
      have htest := isSpatialTest_coordinateDerivative (isSpatialTest_comp_inv_smul hψtest hR) j
      have hloc : LocallyIntegrableOn (fun x => φ i x - m i R) Set.univ volume :=
        ((ha i).1 j).1.sub (locallyIntegrableOn_const _)
      have h := integrableOn_mul_spatialTest hloc htest
      rwa [integrableOn_univ] at h
    calc |∫ x, (φ i x - m i R) * coordinateDerivative j (fun x => ψb (R⁻¹ • x)) x|
        = |∫ x in B, (φ i x - m i R) * coordinateDerivative j (fun x => ψb (R⁻¹ • x)) x| := by
          rw [setIntegral_eq_integral_of_forall_compl_eq_zero hvanish]
      _ ≤ ∫ x in B, |(φ i x - m i R) * coordinateDerivative j (fun x => ψb (R⁻¹ • x)) x| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ x in B, (R⁻¹ * A) * |φ i x - m i R| := by
          refine setIntegral_mono_on hint.abs.integrableOn
            ((hmemB.integrable one_le_two).abs.const_mul _) hBm fun x _ => ?_
          rw [abs_mul, coordinateDerivative_comp_inv_smul hψdiff, abs_mul,
            abs_of_nonneg (inv_nonneg.mpr hR.le)]
          have h := hA (R⁻¹ • x)
          rw [Real.norm_eq_abs] at h
          have hφ0 := abs_nonneg (φ i x - m i R)
          have hR0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
          calc |φ i x - m i R| * (R⁻¹ * |coordinateDerivative j (ψb : Vec d → ℝ) (R⁻¹ • x)|)
              ≤ |φ i x - m i R| * (R⁻¹ * A) := by gcongr
            _ = R⁻¹ * A * |φ i x - m i R| := by ring
      _ = R⁻¹ * A * ∫ x in B, |φ i x - m i R| := integral_const_mul _ _
      _ ≤ R⁻¹ * A * Real.sqrt (volume.real B * ∫ x in B, (φ i x - m i R) ^ 2) :=
          mul_le_mul_of_nonneg_left (setIntegral_abs_le_sqrt hBfin hmemB)
            (mul_nonneg (inv_nonneg.mpr hR.le) hA0)
      _ = A * V₁ * ρ ^ (d + 1) * R ^ d * ((ρ * R)⁻¹ * Real.sqrt (⨍ x in B,
            (φ i x - m i R) ^ 2)) := by
          have havg : ∫ x in B, (φ i x - m i R) ^ 2 =
              volume.real B * ⨍ x in B, (φ i x - m i R) ^ 2 := by
            rw [setAverage_eq, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hVBpos.ne', one_mul]
          have hX : 0 ≤ ⨍ x in B, (φ i x - m i R) ^ 2 := by
            rw [setAverage_eq, smul_eq_mul]
            exact mul_nonneg (inv_nonneg.mpr hVBpos.le) (integral_nonneg fun x => sq_nonneg _)
          rw [havg, ← mul_assoc, Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self hVBpos.le,
            hVB]
          generalize Real.sqrt (⨍ x in B, (φ i x - m i R) ^ 2) = Y
          have hR0 : R ≠ 0 := hR.ne'
          have hρne : ρ ≠ 0 := hρ0.ne'
          field_simp
          ring
  -- conclusion
  have hlim : Tendsto (fun R : ℝ => A * V₁ * ρ ^ (d + 1) * ∑ i, |c i| *
      ((ρ * R)⁻¹ * Real.sqrt (⨍ x in ball 0 (ρ * R), (φ i x - m i R) ^ 2))) atTop (𝓝 0) := by
    have hρR : Tendsto (fun R : ℝ => ρ * R) atTop atTop := tendsto_id.const_mul_atTop hρ0
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun i _ =>
      (((ha i).2.2.comp hρR).const_mul |c i|)
    have h2 := h.const_mul (A * V₁ * ρ ^ (d + 1))
    simpa [hm, Function.comp] using h2
  have hle : ∀ᶠ R in atTop, |c j| * ∫ x, (ψb : Vec d → ℝ) x ≤ A * V₁ * ρ ^ (d + 1) *
      ∑ i, |c i| * ((ρ * R)⁻¹ * Real.sqrt (⨍ x in ball 0 (ρ * R), (φ i x - m i R) ^ 2)) := by
    filter_upwards [eventually_gt_atTop 0] with R hR
    have hRd : 0 < R ^ d := pow_pos hR d
    have h1 := hident R hR
    have h2 : |c j| * (R ^ d * ∫ x, (ψb : Vec d → ℝ) x) ≤ ∑ i, |c i| *
        (A * V₁ * ρ ^ (d + 1) * R ^ d * ((ρ * R)⁻¹ * Real.sqrt (⨍ x in ball 0 (ρ * R),
          (φ i x - m i R) ^ 2))) := by
      calc |c j| * (R ^ d * ∫ x, (ψb : Vec d → ℝ) x) = |c j * (R ^ d * ∫ x, (ψb : Vec d → ℝ) x)| := by
            rw [abs_mul, abs_of_pos (mul_pos hRd hψint)]
        _ = |∑ i, c i * ∫ x, (φ i x - m i R) * coordinateDerivative j (fun x => ψb (R⁻¹ • x)) x| := by
            rw [h1]
        _ ≤ ∑ i, |c i * ∫ x, (φ i x - m i R) * coordinateDerivative j (fun x => ψb (R⁻¹ • x)) x| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := Finset.sum_le_sum fun i _ => by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hbound i R hR) (abs_nonneg _)
    have h3 : ∑ i, |c i| * (A * V₁ * ρ ^ (d + 1) * R ^ d * ((ρ * R)⁻¹ * Real.sqrt (⨍ x in ball 0 (ρ * R),
          (φ i x - m i R) ^ 2))) = R ^ d * (A * V₁ * ρ ^ (d + 1) *
        ∑ i, |c i| * ((ρ * R)⁻¹ * Real.sqrt (⨍ x in ball 0 (ρ * R), (φ i x - m i R) ^ 2))) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h3] at h2
    have h4 : R ^ d * (|c j| * ∫ x, (ψb : Vec d → ℝ) x) ≤ R ^ d * (A * V₁ * ρ ^ (d + 1) *
        ∑ i, |c i| * ((ρ * R)⁻¹ * Real.sqrt (⨍ x in ball 0 (ρ * R), (φ i x - m i R) ^ 2))) := by
      linarith [show |c j| * (R ^ d * ∫ x, (ψb : Vec d → ℝ) x) =
        R ^ d * (|c j| * ∫ x, (ψb : Vec d → ℝ) x) by ring]
    exact le_of_mul_le_mul_left h4 hRd
  have hfin := ge_of_tendsto hlim hle
  have h0 : |c j| * ∫ x, (ψb : Vec d → ℝ) x = 0 :=
    le_antisymm hfin (mul_nonneg (abs_nonneg _) hψint.le)
  rcases mul_eq_zero.mp h0 with h | h
  · exact abs_eq_zero.mp h
  · exact absurd h hψint.ne'

end QSH
