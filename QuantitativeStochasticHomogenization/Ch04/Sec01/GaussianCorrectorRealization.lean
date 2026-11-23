import QuantitativeStochasticHomogenization.Ch04.Sec01.GaussianAverageBasis
import QuantitativeStochasticHomogenization.Ch03.Sec04.GaussianCorrectorBounds
import QuantitativeStochasticHomogenization.Ch06.Sec01.FluxCorrectorExistence
import QuantitativeStochasticHomogenization.Ch06.Sec01.FluxCorrectorDivergenceProof
import QuantitativeStochasticHomogenization.Ch06.Sec01.CorrectorSublinear
import QuantitativeStochasticHomogenization.Ch04.Sec01.GramSpace

/-!
# Proposition 3.21 at one realization

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Proposition 3.21. At a coefficient field `a` whose `d` coordinate correctors `φᵢ` satisfy, above a
scale `Y`, the oscillation bound `C ρ^{1-θ} Y^θ` and the energy bound `C²`, and whose fluxes
`a(eᵢ + ∇φᵢ) - A eᵢ` satisfy a pairing bound above a scale `X₂`, the coordinate fields
`Gᵢ = eᵢ + ∇φᵢ` satisfy the bounds `GaussianBasisBounds` at every mask `Φ_{x₀,r}` with
`r ≥ max(Y, X₂)` and `|x₀| ≤ r`, with error `C' ((Y/r)^θ + (X₂/r)^κ)`
(`gaussianBasisBounds_of_realization`). The constants depend only on `d`, `Λ` and the constants
of the hypotheses.

`exists_ae_gaussianBasisBounds`: for the correctors of every law, almost surely these bounds hold
above `B X`, `X` the homogenization scale of Armstrong, Kuusi and Loher, with error
`C (B X / r)^θ'`; the constants `B`, `C`, `θ'` are chosen before the law.
-/

open MeasureTheory Filter Set

noncomputable section

namespace QSH

variable {d : ℕ}

theorem euclideanNorm_mulVec_sq_le {Λ : ℝ} (a : CoefficientField d Λ) (y v : Vec d) :
    euclideanNorm ((a.field y).mulVec v) ^ 2 ≤ Λ ^ 2 * euclideanNorm v ^ 2 := by
  rw [← euclideanSq_eq_euclideanNorm_sq, ← euclideanSq_eq_euclideanNorm_sq]
  exact euclideanSq_mulVec_le a y v

theorem euclideanNorm_unitVector_add_sq_le (i : Fin d) (w : Vec d) :
    euclideanNorm (unitVector i + w) ^ 2 ≤ 2 * (1 + euclideanNorm w ^ 2) := by
  have h1 := euclideanNorm_add_le (unitVector i) w
  rw [euclideanNorm_unitVector] at h1
  have h0 := euclideanNorm_nonneg (unitVector i + w)
  have hw := euclideanNorm_nonneg w
  nlinarith [sq_nonneg (euclideanNorm w - 1)]

theorem integrableOn_euclideanNorm_sq {R : ℝ} {g : Vec d → Vec d}
    (hg : MemLp g 2 (volume.restrict (ball 0 R))) :
    IntegrableOn (fun y => euclideanNorm (g y) ^ 2) (ball 0 R) := by
  have h : ∀ k, Integrable (fun y => g y k ^ 2) (volume.restrict (ball 0 R)) := fun k =>
    (memLp_pi_iff.mp hg k).integrable_sq
  refine (integrable_finsetSum Finset.univ fun k _ => h k).congr
    (Eventually.of_forall fun y => ?_)
  show ∑ i, g y i ^ 2 = euclideanNorm (g y) ^ 2
  rw [← euclideanSq_eq_euclideanNorm_sq]
  simp only [euclideanSq, dot, sq]

theorem sq_apply_le_euclideanNorm_sq (v : Vec d) (k : Fin d) : v k ^ 2 ≤ euclideanNorm v ^ 2 := by
  have h := abs_apply_le_euclideanNorm v k
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

/-- **Proposition 3.21 at one realization.** -/
theorem gaussianBasisBounds_of_realization {Λ : ℝ} (hΛ : 1 ≤ Λ) (a : CoefficientField d Λ)
    (A : Mat d) {u : Fin d → Vec d → ℝ} {g : Fin d → Vec d → Vec d}
    (hw : ∀ i, HasWeakGradient Set.univ (u i) (g i))
    (hL : ∀ i (R : ℝ), 0 < R →
      MemLp (u i) 2 (volume.restrict (ball 0 R)) ∧ MemLp (g i) 2 (volume.restrict (ball 0 R)))
    (hgm : ∀ i, Measurable (g i))
    (hharm : ∀ i, HasWeakDivergence Set.univ
      (fun x => (a x).mulVec (unitVector i + g i x)) (fun _ => 0))
    {Y X₂ Cφ θ κ Ap Ch : ℝ} (hY : 0 < Y) (hX₂ : 0 < X₂) (hCφ : 0 ≤ Cφ) (hθ : 0 ≤ θ)
    (hκ : 0 ≤ κ) (hAp : 0 ≤ Ap) (hCh0 : 0 ≤ Ch)
    (hosc : ∀ i (ρ : ℝ), Y ≤ ρ → Real.sqrt (⨍ x in ball 0 ρ,
      |u i x - ⨍ y in ball 0 ρ, u i y| ^ 2) ≤ Cφ * ρ ^ (1 - θ) * Y ^ θ)
    (hen : ∀ i (ρ : ℝ), Y ≤ ρ → Real.sqrt (⨍ x in ball 0 ρ, euclideanSq (g i x)) ≤ Cφ)
    (hpair : ∀ i k, HasScalePairingBound
      (fun y => ((coefficientRepresentative a y).mulVec (unitVector i + g i y)) k - A k i)
      X₂ Ap κ)
    (hCh : ∀ {F : Vec d → ℝ} {R₀ A' κ' : ℝ}, HasScalePairingBound F R₀ A' κ' →
      0 < R₀ → 0 ≤ A' → 0 ≤ κ' → Measurable F → HasGaussianMoments F →
      ∀ (r : ℝ) (x₀ : Vec d), R₀ ≤ r → euclideanNorm x₀ ≤ r →
        |∫ y, heatKernel x₀ r y * F y| ≤ Ch * A' * (R₀ / r) ^ κ')
    {r : ℝ} (hrY : Y ≤ r) (hrX : X₂ ≤ r) {x₀ : Vec d} (hx₀ : euclideanNorm x₀ ≤ r) :
    GaussianBasisBounds a A (fun i x => unitVector i + g i x) x₀ r
      ((gaussianGradConst d + gaussianCrossConst d *
          Real.sqrt (2 * Λ ^ 2 * (1 + Cφ ^ 2) * (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal)) * Cφ * (Y / r) ^ θ +
        Ch * Ap * (X₂ / r) ^ κ) := by
  have hr0 : 0 < r := hY.trans_le hrY
  have hΛ0 : 0 ≤ Λ := zero_le_one.trans hΛ
  have hω : 0 ≤ (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal := ENNReal.toReal_nonneg
  set Mq := 2 * Λ ^ 2 * (1 + Cφ ^ 2) * (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal with hMq
  have hMq0 : 0 ≤ Mq := by positivity
  -- the mask
  have hs : 0 < r ^ 2 := by positivity
  have hΦ : ∀ y, heatKernel x₀ r y = euclideanHeatKernel (r ^ 2) (y - x₀) := fun y => rfl
  have hΦ0 : ∀ y, 0 ≤ heatKernel x₀ r y := heatKernel_nonneg x₀ r
  have hΦi : Integrable (heatKernel x₀ r) := integrable_heatKernel x₀ hr0
  have hΦ1 : ∫ y, heatKernel x₀ r y = 1 := integral_heatKernel x₀ hr0
  have hxs : euclideanNorm x₀ ≤ Real.sqrt (r ^ 2) := by rwa [Real.sqrt_sq hr0.le]
  have hrr : r ^ 2 ≤ r ^ 2 := le_rfl
  have hcoef := coefficientRepresentative_ae_eq a
  -- Gaussian energies of the gradients
  have hgL : ∀ i (R : ℝ), 0 < R → ∀ k, MemLp (fun x => g i x k) 2 (volume.restrict (ball 0 R)) :=
    fun i R hR k => memLp_pi_iff.mp (hL i R hR).2 k
  have hgen : ∀ i, Integrable (fun y => heatKernel x₀ r y * euclideanNorm (g i y) ^ 2) := by
    intro i
    have hgrow : ∀ R : ℝ, r ≤ R → IntegrableOn (fun y => euclideanNorm (g i y) ^ 2) (ball 0 R) ∧
        ∫ y in ball 0 R, euclideanNorm (g i y) ^ 2 ≤ Cφ ^ 2 * (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal * R ^ (d + 0) := by
      intro R hR
      refine growth_of_energy hY (fun R hR => integrableOn_euclideanNorm_sq (hL i R hR).2)
        (fun ρ hρ => ?_) R (hrY.trans hR)
      have h := hen i ρ hρ
      have hA0 : 0 ≤ ⨍ x in ball 0 ρ, euclideanSq (g i x) :=
        setAverage_nonneg_of_nonneg fun x => euclideanSq_nonneg _
      have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
      rw [Real.sq_sqrt hA0] at h2
      simp only [← euclideanSq_eq_euclideanNorm_sq]
      exact h2
    exact (integral_heatKernel_mul_sq_le_of_growth 0
      (continuous_euclideanNorm_vec.measurable.comp (hgm i)).aestronglyMeasurable (by positivity)
      hr0 hgrow hrr hxs).1
  have hgk2 : ∀ i k, Integrable (fun y => euclideanHeatKernel (r ^ 2) (y - x₀) * g i y k ^ 2) := by
    intro i k
    refine (hgen i).mono' ((hΦi.aestronglyMeasurable).mul
      (((measurable_pi_apply k).comp (hgm i)).pow_const 2).aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (euclideanHeatKernel_nonneg hs.le _)
      (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (sq_apply_le_euclideanNorm_sq _ k) (hΦ0 y)
  have hgk : ∀ i k, Integrable (fun y => heatKernel x₀ r y * g i y k) := fun i k =>
    (integrable_and_abs_integral_heat_le hs x₀
      ((measurable_pi_apply k).comp (hgm i)).aestronglyMeasurable (hgk2 i k)).1
  -- the fluxes with the measurable representative
  set q' : Fin d → Vec d → Vec d := fun i y =>
    (coefficientRepresentative a y).mulVec (unitVector i + g i y) with hq'
  have hqq : ∀ i, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (a y).mulVec (unitVector i + g i y) = q' i y := by
    intro i
    filter_upwards [hcoef] with y hy
    simp only [hq']
    rw [hy]
  have hq'm : ∀ i k, Measurable fun y => q' i y k := by
    intro i k
    have h := measurable_flux a (hgm i) (unitVector i) 0 k
    simpa using h
  have hq'L : ∀ i (R : ℝ), 0 < R → ∀ k, MemLp (fun y => q' i y k) 2 (volume.restrict (ball 0 R)) := by
    intro i R _ k
    have h := memLp_flux hΛ a (hgm i) (fun R hR => (hL i R hR).2) (unitVector i) 0 k R
    simpa using h
  have hq'harm : ∀ i, HasWeakDivergence Set.univ (q' i) (fun _ => 0) := fun i =>
    (hharm i).congr_ae (hqq i) (Eventually.of_forall fun _ => rfl)
  have hq'bd : ∀ i, ∀ᵐ y ∂(volume : Measure (Vec d)),
      euclideanNorm (q' i y) ^ 2 ≤ 2 * Λ ^ 2 * (1 + euclideanNorm (g i y) ^ 2) := by
    intro i
    filter_upwards [hqq i] with y hy
    rw [← hy]
    calc euclideanNorm ((a y).mulVec (unitVector i + g i y)) ^ 2
        ≤ Λ ^ 2 * euclideanNorm (unitVector i + g i y) ^ 2 := euclideanNorm_mulVec_sq_le a y _
      _ ≤ Λ ^ 2 * (2 * (1 + euclideanNorm (g i y) ^ 2)) :=
          mul_le_mul_of_nonneg_left (euclideanNorm_unitVector_add_sq_le i _) (by positivity)
      _ = 2 * Λ ^ 2 * (1 + euclideanNorm (g i y) ^ 2) := by ring
  have hq'nm : ∀ i, Measurable fun y => euclideanNorm (q' i y) := fun i =>
    continuous_euclideanNorm_vec.measurable.comp (measurable_pi_iff.mpr (hq'm i))
  have hq'growth : ∀ i (R : ℝ), r ≤ R →
      IntegrableOn (fun y => euclideanNorm (q' i y) ^ 2) (ball 0 R) ∧
        ∫ y in ball 0 R, euclideanNorm (q' i y) ^ 2 ≤ Mq * R ^ (d + 0) := by
    intro i R hR
    have hR0 : 0 < R := hr0.trans_le hR
    have hfin : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
      isFiniteMeasure_restrict.mpr (volume_ball_ne_top hR0)
    have hq'in : IntegrableOn (fun y => euclideanNorm (q' i y) ^ 2) (ball 0 R) :=
      integrableOn_euclideanNorm_sq (memLp_pi_iff.mpr (hq'L i R hR0))
    have hgin := integrableOn_euclideanNorm_sq (hL i R hR0).2
    refine ⟨hq'in, ?_⟩
    have hgrowg : ∫ y in ball 0 R, euclideanNorm (g i y) ^ 2 ≤ Cφ ^ 2 * (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal * R ^ (d + 0) := by
      refine (growth_of_energy hY (fun R hR => integrableOn_euclideanNorm_sq (hL i R hR).2)
        (fun ρ hρ => ?_) R (hrY.trans hR)).2
      have h := hen i ρ hρ
      have hA0 : 0 ≤ ⨍ x in ball 0 ρ, euclideanSq (g i x) :=
        setAverage_nonneg_of_nonneg fun x => euclideanSq_nonneg _
      have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
      rw [Real.sq_sqrt hA0] at h2
      simp only [← euclideanSq_eq_euclideanNorm_sq]
      exact h2
    have hdomI : IntegrableOn (fun y => 2 * Λ ^ 2 * (1 + euclideanNorm (g i y) ^ 2)) (ball 0 R) :=
      ((integrable_const (1 : ℝ)).add hgin).const_mul _
    calc ∫ y in ball 0 R, euclideanNorm (q' i y) ^ 2
        ≤ ∫ y in ball 0 R, 2 * Λ ^ 2 * (1 + euclideanNorm (g i y) ^ 2) :=
          setIntegral_mono_ae_restrict hq'in hdomI (ae_restrict_of_ae (hq'bd i))
      _ = 2 * Λ ^ 2 * (volume.real (ball (0 : Vec d) R) +
            ∫ y in ball 0 R, euclideanNorm (g i y) ^ 2) := by
          rw [integral_const_mul, integral_add (integrable_const 1) hgin, setIntegral_const,
            smul_eq_mul, mul_one]
      _ ≤ 2 * Λ ^ 2 * (R ^ d * (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal + Cφ ^ 2 * (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal * R ^ (d + 0)) := by
          rw [volume_real_ball hR0]
          gcongr
      _ = Mq * R ^ (d + 0) := by rw [hMq, add_zero]; ring
  have hq'2 : ∀ i, Integrable (fun y => heatKernel x₀ r y * euclideanNorm (q' i y) ^ 2) := fun i =>
    (integral_heatKernel_mul_sq_le_of_growth 0 (hq'nm i).aestronglyMeasurable hMq0 hr0
      (hq'growth i) hrr hxs).1
  have hq'k2 : ∀ i k, Integrable (fun y => euclideanHeatKernel (r ^ 2) (y - x₀) * q' i y k ^ 2) := by
    intro i k
    refine (hq'2 i).mono' ((hΦi.aestronglyMeasurable).mul
      ((hq'm i k).pow_const 2).aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (euclideanHeatKernel_nonneg hs.le _)
      (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (sq_apply_le_euclideanNorm_sq _ k) (hΦ0 y)
  have hq'k : ∀ i k, Integrable (fun y => heatKernel x₀ r y * q' i y k) := fun i k =>
    (integrable_and_abs_integral_heat_le hs x₀ (hq'm i k).aestronglyMeasurable (hq'k2 i k)).1
  -- the cross terms
  have hcrossI : ∀ l i, Integrable (fun y => heatKernel x₀ r y * dot (q' i y) (g l y)) := by
    intro l i
    have h : ∀ k, Integrable (fun y => heatKernel x₀ r y * (q' i y k * g l y k)) := fun k =>
      (integrable_and_abs_integral_weight_mul_le hΦ0 hΦi.aestronglyMeasurable
        (hq'm i k).aestronglyMeasurable ((measurable_pi_apply k).comp (hgm l)).aestronglyMeasurable
        (hq'k2 i k) (hgk2 l k)).1
    refine (integrable_finsetSum Finset.univ fun k _ => h k).congr
      (Eventually.of_forall fun y => ?_)
    simp only [dot, Finset.mul_sum]
  have hcross : ∀ l i, |∫ y, heatKernel x₀ r y * dot (q' i y) (g l y)| ≤
      gaussianCrossConst d * Real.sqrt Mq * Cφ * (Y / r) ^ θ := fun l i =>
    abs_integral_heatKernel_dot_le (hq'harm i) (hq'L i) (hw l) (fun R hR => (hL l R hR).1)
      (hgL l) hY hθ hCφ hMq0 (hosc l) hrY hx₀ (hq'growth i) (hcrossI l i)
  -- the flux averages
  have hflux : ∀ i k, |(∫ y, heatKernel x₀ r y * q' i y k) - A k i| ≤
      Ch * Ap * (X₂ / r) ^ κ := by
    intro i k
    have hFm : Measurable fun y => q' i y k - A k i := (hq'm i k).sub_const _
    have hmom : HasGaussianMoments fun y => q' i y k - A k i := by
      have h := hasGaussianMoments_of_growth (measurable_flux a (hgm i) (unitVector i)
        (fun k => A k i) k)
        (M := 3 * (Λ ^ 2 * euclideanSq (unitVector i : Vec d) + Λ ^ 2 * Cφ ^ 2 +
          (A k i) ^ 2) * (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal)
        (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg (add_nonneg (mul_nonneg (sq_nonneg _)
          (euclideanSq_nonneg _)) (by positivity)) (sq_nonneg _))) ENNReal.toReal_nonneg) hY
        (fun R hR => lintegral_flux_sq_le hΛ a (hgm i) (fun R hR => (hL i R hR).2) hY (hen i)
          (unitVector i) (fun k => A k i) k R hR)
      exact h
    have h := hCh (hpair i k) hX₂ hAp hκ hFm hmom r x₀ hrX hx₀
    have heq : ∫ y, heatKernel x₀ r y * (q' i y k - A k i) =
        (∫ y, heatKernel x₀ r y * q' i y k) - A k i := by
      have : (fun y => heatKernel x₀ r y * (q' i y k - A k i)) =
          fun y => heatKernel x₀ r y * q' i y k - heatKernel x₀ r y * A k i := by
        funext y; ring
      rw [this, integral_sub (hq'k i k) (hΦi.mul_const _), integral_mul_const, hΦ1, one_mul]
    rw [← heq]
    exact h
  -- assembling
  have hGint : ∀ i k, Integrable fun x => heatKernel x₀ r x * (unitVector i + g i x) k := by
    intro i k
    refine ((hΦi.mul_const (unitVector i k : ℝ)).add (hgk i k)).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  have hqint : ∀ i k, Integrable fun x =>
      heatKernel x₀ r x * ((a x).mulVec (unitVector i + g i x)) k := by
    intro i k
    refine (hq'k i k).congr ?_
    filter_upwards [hqq i] with x hx
    rw [hx]
  have hEeq : ∀ l i, ∀ᵐ x ∂(volume : Measure (Vec d)),
      heatKernel x₀ r x * dot (unitVector l + g l x) ((a x).mulVec (unitVector i + g i x)) =
        heatKernel x₀ r x * q' i x l + heatKernel x₀ r x * dot (q' i x) (g l x) := by
    intro l i
    filter_upwards [hqq i] with x hx
    rw [hx]
    have h1 : dot (unitVector l + g l x) (q' i x) = q' i x l + dot (q' i x) (g l x) := by
      have hsplit : dot (unitVector l + g l x) (q' i x) =
          dot (unitVector l) (q' i x) + dot (g l x) (q' i x) := by
        simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      have hl : dot (unitVector l) (q' i x) = q' i x l := by
        unfold dot
        rw [Finset.sum_eq_single l]
        · simp [unitVector]
        · intro b _ hb
          simp [unitVector, hb]
        · simp
      have hc : dot (g l x) (q' i x) = dot (q' i x) (g l x) := by
        simp only [dot]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      rw [hsplit, hl, hc]
    rw [h1, mul_add]
  have hEint : ∀ l i, Integrable fun x => heatKernel x₀ r x *
      dot (unitVector l + g l x) ((a x).mulVec (unitVector i + g i x)) := fun l i =>
    ((hq'k i l).add (hcrossI l i)).congr (by
      filter_upwards [hEeq l i] with x hx
      rw [hx]
      rfl)
  have hYr : 0 ≤ (Y / r) ^ θ := Real.rpow_nonneg (div_nonneg hY.le hr0.le) _
  have hXr : 0 ≤ (X₂ / r) ^ κ := Real.rpow_nonneg (div_nonneg hX₂.le hr0.le) _
  have n1 : 0 ≤ gaussianGradConst d * Cφ * (Y / r) ^ θ := by
    have := gaussianGradConst_nonneg d
    positivity
  have n2 : 0 ≤ gaussianCrossConst d * Real.sqrt Mq * Cφ * (Y / r) ^ θ := by
    have := gaussianCrossConst_nonneg d
    positivity
  have n3 : 0 ≤ Ch * Ap * (X₂ / r) ^ κ := by positivity
  have hsplit : (gaussianGradConst d + gaussianCrossConst d * Real.sqrt Mq) * Cφ * (Y / r) ^ θ +
      Ch * Ap * (X₂ / r) ^ κ = gaussianGradConst d * Cφ * (Y / r) ^ θ +
        gaussianCrossConst d * Real.sqrt Mq * Cφ * (Y / r) ^ θ + Ch * Ap * (X₂ / r) ^ κ := by
    ring
  refine ⟨hGint, hqint, hEint, fun i k => ?_, fun i k => ?_, fun l i => ?_⟩
  · -- the averages
    show |(∫ x, heatKernel x₀ r x * (unitVector i + g i x) k) - unitVector i k| ≤ _
    have heq : (∫ x, heatKernel x₀ r x * (unitVector i + g i x) k) - unitVector i k =
        ∫ x, heatKernel x₀ r x * g i x k := by
      have : (fun x => heatKernel x₀ r x * (unitVector i + g i x) k) =
          fun x => heatKernel x₀ r x * unitVector i k + heatKernel x₀ r x * g i x k := by
        funext x; simp only [Pi.add_apply]; ring
      rw [this, integral_add (hΦi.mul_const _) (hgk i k), integral_mul_const, hΦ1, one_mul]
      ring
    rw [heq, hsplit]
    have h := abs_integral_heatKernel_grad_le (hw i) (fun R hR => (hL i R hR).1) hY hθ hCφ
      (hosc i) hrY hx₀ k (hgk i k)
    linarith
  · -- the fluxes
    show |(∫ x, heatKernel x₀ r x * ((a x).mulVec (unitVector i + g i x)) k) - A k i| ≤ _
    have heq : ∫ x, heatKernel x₀ r x * ((a x).mulVec (unitVector i + g i x)) k =
        ∫ x, heatKernel x₀ r x * q' i x k := by
      refine integral_congr_ae ?_
      filter_upwards [hqq i] with x hx
      rw [hx]
    rw [heq, hsplit]
    have h := hflux i k
    linarith
  · -- the energies
    show |(∫ x, heatKernel x₀ r x * dot (unitVector l + g l x)
      ((a x).mulVec (unitVector i + g i x))) - A l i| ≤ _
    have heq : ∫ x, heatKernel x₀ r x *
        dot (unitVector l + g l x) ((a x).mulVec (unitVector i + g i x)) =
        (∫ x, heatKernel x₀ r x * q' i x l) + ∫ x, heatKernel x₀ r x * dot (q' i x) (g l x) := by
      rw [integral_congr_ae (hEeq l i), integral_add (hq'k i l) (hcrossI l i)]
    rw [heq, hsplit]
    have h1 := hflux i l
    have h2 := hcross l i
    have h3 := abs_add_le ((∫ x, heatKernel x₀ r x * q' i x l) - A l i)
      (∫ x, heatKernel x₀ r x * dot (q' i x) (g l x))
    rw [show (∫ x, heatKernel x₀ r x * q' i x l) - A l i +
        ∫ x, heatKernel x₀ r x * dot (q' i x) (g l x) =
      (∫ x, heatKernel x₀ r x * q' i x l) + (∫ x, heatKernel x₀ r x * dot (q' i x) (g l x)) -
        A l i by ring] at h3
    linarith

theorem matVecMul_unitVector_apply (A : Mat d) (i k : Fin d) :
    (_root_.Homogenization.matVecMul A (unitVector i)) k = A k i := by
  show (A.mulVec (Pi.single i 1)) k = A k i
  simp [Matrix.mulVec_single]

theorem rpow_le_rpow_of_le_of_le_one {x y θ θ' : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy0 : 0 < y)
    (hy : y ≤ 1) (hθ' : 0 ≤ θ') (hθθ : θ' ≤ θ) : x ^ θ ≤ y ^ θ' :=
  (Real.rpow_le_rpow hx hxy (hθ'.trans hθθ)).trans
    (Real.rpow_le_rpow_of_exponent_ge hy0 hy hθθ)

/-- **Proposition 3.21 almost surely, with constants chosen before the law.** -/
theorem exists_ae_gaussianBasisBounds (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 < Λ) {κ C₀ : ℝ}
    (hκ : 0 < κ) (hC₀ : 0 ≤ C₀) :
    ∃ B Cε θ' Cφ θ : ℝ, 1 ≤ B ∧ 0 ≤ Cε ∧ 0 < θ' ∧ θ' ≤ 1 ∧ 0 ≤ Cφ ∧ 0 < θ ∧ θ ≤ 1 ∧
      ∀ (P : Measure (CoefficientField d Λ)) (pk : HighContrastCorrectorPackage hΛ.le P κ C₀),
        LawHypotheses P → ∀ S : HomogenizationData P,
          (∀ᵐ a ∂P, ∀ (r : ℝ) (x₀ : Vec d),
            B * pk.X (toHighContrast hΛ.le a) ≤ r → euclideanNorm x₀ ≤ r →
              GaussianBasisBounds a pk.abar (correctedCoordinate S a) x₀ r
                (Cε * (B * pk.X (toHighContrast hΛ.le a) / r) ^ θ')) ∧
          ∀ i : Fin d, ∀ᵐ a ∂P, ∀ ρ : ℝ, B * pk.X (toHighContrast hΛ.le a) ≤ ρ →
            Real.sqrt (⨍ x in ball 0 ρ, |(S.corrector (unitVector i)).potential a x -
              ⨍ y in ball 0 ρ, (S.corrector (unitVector i)).potential a y| ^ 2) ≤
                Cφ * ρ ^ (1 - θ) * (B * pk.X (toHighContrast hΛ.le a)) ^ θ := by
  obtain ⟨Cφ, θ, n₁, hCφ, hθ, hθ1, hφb⟩ := exists_corrector_scale_bounds d hd Λ hΛ.le hκ hC₀
  obtain ⟨Ap, Cab, hAp, -, hpair⟩ := exists_uniform_flux_pairing d hd Λ hΛ.le hκ hC₀
  obtain ⟨Ch, hCh0, hCh⟩ := exists_abs_integral_heatKernel_le_of_pairing d
  set Mq := 2 * Λ ^ 2 * (1 + Cφ ^ 2) * (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal with hMq
  set Cε := (gaussianGradConst d + gaussianCrossConst d * Real.sqrt Mq) * Cφ + Ch * Ap with hCε
  set B : ℝ := max ((3 : ℝ) ^ (n₁ + 1)) 2 with hB
  have hB1 : 1 ≤ B := le_trans (by norm_num) (le_max_right _ _)
  have hKg := gaussianGradConst_nonneg d
  have hKc := gaussianCrossConst_nonneg d
  refine ⟨B, Cε, min θ κ, Cφ, θ, hB1, by positivity, lt_min hθ hκ, (min_le_left _ _).trans hθ1,
    hCφ, hθ, hθ1, fun P pk hP S => ⟨?_, fun i => ?_⟩⟩
  swap
  · filter_upwards [hφb P pk hP (unitVector i) (euclideanNorm_unitVector i)
      (S.corrector (unitVector i))] with a ha ρ hρ
    have hX0 : 0 < pk.X (toHighContrast hΛ.le a) := zero_lt_one.trans_le (pk.one_le_X _)
    have hYB : (3 : ℝ) ^ (n₁ + 1) * pk.X (toHighContrast hΛ.le a) ≤
        B * pk.X (toHighContrast hΛ.le a) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hX0.le
    refine (ha ρ (hYB.trans hρ)).1.trans ?_
    have hρ0 : 0 ≤ ρ ^ (1 - θ) := by
      have : 0 < ρ := (mul_pos (zero_lt_one.trans_le hB1) hX0).trans_le hρ
      positivity
    gcongr
  filter_upwards [ae_all_iff.mpr fun i : Fin d => hφb P pk hP (unitVector i)
      (euclideanNorm_unitVector i) (S.corrector (unitVector i)),
    ae_all_iff.mpr fun i : Fin d => hpair P pk hP (unitVector i) (euclideanNorm_unitVector i)
      (S.corrector (unitVector i)),
    ae_all_iff.mpr fun i : Fin d => (S.corrector (unitVector i)).weak_gradient,
    ae_all_iff.mpr fun i : Fin d => (S.corrector (unitVector i)).locally_square_integrable,
    ae_all_iff.mpr fun i : Fin d => (S.corrector (unitVector i)).harmonic]
    with a h1 h2 h3 h4 h5
  intro r x₀ hr hx₀
  set X := pk.X (toHighContrast hΛ.le a) with hX
  have hX1 : 1 ≤ X := pk.one_le_X _
  have hX0 : 0 < X := zero_lt_one.trans_le hX1
  have h3n : (0 : ℝ) < (3 : ℝ) ^ (n₁ + 1) := by positivity
  have hY : 0 < (3 : ℝ) ^ (n₁ + 1) * X := mul_pos h3n hX0
  have hYB : (3 : ℝ) ^ (n₁ + 1) * X ≤ B * X :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hX0.le
  have hX2B : 2 * X ≤ B * X := mul_le_mul_of_nonneg_right (le_max_right _ _) hX0.le
  have hr0 : 0 < r := (mul_pos (zero_lt_one.trans_le hB1) hX0).trans_le hr
  have hgm : ∀ i : Fin d, Measurable ((S.corrector (unitVector i)).grad a) := fun i =>
    Measurable.of_uncurry_left (f := fun a y => (S.corrector (unitVector i)).grad a y)
      (S.corrector (unitVector i)).measurable_grad
  have hpair' : ∀ i k, HasScalePairingBound (fun y => ((coefficientRepresentative a y).mulVec
      (unitVector i + (S.corrector (unitVector i)).grad a y)) k - pk.abar k i) (2 * X) Ap κ := by
    intro i k
    have h := (h2 i).2.2 k
    simp only [matVecMul_unitVector_apply] at h
    exact h
  have hbase := gaussianBasisBounds_of_realization hΛ.le a pk.abar
    (u := fun i => (S.corrector (unitVector i)).potential a)
    (g := fun i => (S.corrector (unitVector i)).grad a) h3 h4 hgm h5 hY (by positivity) hCφ
    hθ.le hκ.le hAp hCh0 (fun i ρ hρ => (h1 i ρ hρ).1) (fun i ρ hρ => (h1 i ρ hρ).2) hpair'
    hCh (hYB.trans hr) (hX2B.trans hr) hx₀
  refine hbase.mono ?_
  have hBXr : B * X / r ≤ 1 := (div_le_one hr0).mpr hr
  have hθ' : 0 ≤ min θ κ := (lt_min hθ hκ).le
  have e1 : ((3 : ℝ) ^ (n₁ + 1) * X / r) ^ θ ≤ (B * X / r) ^ min θ κ :=
    rpow_le_rpow_of_le_of_le_one (by positivity) (div_le_div_of_nonneg_right hYB hr0.le)
      (by positivity) hBXr
      hθ' (min_le_left _ _)
  have e2 : (2 * X / r) ^ κ ≤ (B * X / r) ^ min θ κ :=
    rpow_le_rpow_of_le_of_le_one (by positivity) (div_le_div_of_nonneg_right hX2B hr0.le)
      (by positivity) hBXr
      hθ' (min_le_right _ _)
  have hM0 : 0 ≤ (gaussianGradConst d + gaussianCrossConst d * Real.sqrt Mq) * Cφ := by
    positivity
  calc (gaussianGradConst d + gaussianCrossConst d * Real.sqrt Mq) * Cφ *
        ((3 : ℝ) ^ (n₁ + 1) * X / r) ^ θ + Ch * Ap * (2 * X / r) ^ κ
      ≤ (gaussianGradConst d + gaussianCrossConst d * Real.sqrt Mq) * Cφ *
          (B * X / r) ^ min θ κ + Ch * Ap * (B * X / r) ^ min θ κ := by
        gcongr
    _ = Cε * (B * X / r) ^ min θ κ := by rw [hCε]; ring

end QSH
