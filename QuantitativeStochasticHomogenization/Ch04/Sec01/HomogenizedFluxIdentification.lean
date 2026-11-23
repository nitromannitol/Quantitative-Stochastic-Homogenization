import QuantitativeStochasticHomogenization.Ch04.Sec01.HomogenizedGaussianLimits
import QuantitativeStochasticHomogenization.Ch03.Sec04.CorrectorLinearCombination
import QuantitativeStochasticHomogenization.Ch03.Sec04.CubeOscillationPairing
import QuantitativeStochasticHomogenization.Ch03.Sec04.HighContrastLocalSobolev
import QuantitativeStochasticHomogenization.Ch06.Sec01.SmoothGradBounds
import QuantitativeStochasticHomogenization.Ch06.Sec01.HighContrastEnergyBounds
import QuantitativeStochasticHomogenization.Ch03.Sec04.GaussianCorrectorBounds

/-!
# The homogenized matrix is the matrix of the Gaussian averages

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Definition 1.2 and Section 3.4. Let `S` be homogenization data and suppose that almost surely its
coordinate corrected fields satisfy `GaussianBasisBounds` with a matrix `M` above a scale `Y`
with finite moments, and that its coordinate correctors are sublinear above `Y`. Then
`S.homogenized = M` (`homogenized_eq_of_basisBounds`).

For a slope `e` and `G = G e`:

* by the dual bound, `μ(□_n, e) ≥ ⨍_{□_n} (e · a G - ½ G · a G)`, whose expectation is the cell mean
  `½ e · M e` of a stationary density; hence `½ e · ā e ≥ ½ e · M e`;
* by the trial function `η (φ_e - c)`, with `η` the inner cutoff of `□_n` of relative width `τ`,
  `μ(□_n, e) ≤ (1 + t) ⨍_{□_n} ½ G · a G + (1 + t⁻¹) ½ Λ ⨍ |(1 - η) e + (φ_e - c) ∇η|²`; the
  expectation of the first average is `½ e · M e` and the second is at most
  `4 d τ |e|² + K ψ_n(Y)` with `E ψ_n(Y) → 0` by sublinearity; hence `½ e · ā e ≤ ½ e · M e`.

Both matrices are symmetric, so they are equal.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

open _root_.Homogenization hiding euclideanBall Vec Mat

variable {d : ℕ} {Λ : ℝ}

/-! ## Geometry of the triadic cubes -/

theorem isOpenBoundedConvexDomain_triadicCube (n : ℕ) :
    PDE.IsOpenBoundedConvexDomain (triadicCube d n) := by
  refine ⟨isOpen_triadicCube n, ⟨(3 : ℝ) ^ n / 2 + 1, by positivity, fun x hx i => ?_⟩, ?_⟩
  · have h := (mem_triadicCube_iff.mp hx) i
    linarith
  · exact convex_pi fun _ _ => convex_Ioo _ _

theorem triadicCube_subset_ball (hd : 1 ≤ d) (n : ℕ) :
    triadicCube d n ⊆ ball 0 (Real.sqrt d * (3 : ℝ) ^ n) := by
  intro x hx
  have hx' := mem_triadicCube_iff.mp hx
  show euclideanNorm (x - 0) < Real.sqrt d * (3 : ℝ) ^ n
  rw [sub_zero]
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hlt : euclideanSq x < d * ((3 : ℝ) ^ n) ^ 2 := by
    unfold euclideanSq dot
    calc ∑ i, x i * x i ≤ ∑ _i : Fin d, ((3 : ℝ) ^ n / 2) ^ 2 :=
          Finset.sum_le_sum fun i _ => by
            have h := hx' i
            have h2 : x i ^ 2 ≤ ((3 : ℝ) ^ n / 2) ^ 2 := by
              rw [← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) h.le 2
            nlinarith
      _ = d * (((3 : ℝ) ^ n) ^ 2 / 4) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ < d * ((3 : ℝ) ^ n) ^ 2 := by
          refine mul_lt_mul_of_pos_left ?_ hd0
          have : 0 < ((3 : ℝ) ^ n) ^ 2 := by positivity
          linarith
  unfold euclideanNorm
  calc Real.sqrt (euclideanSq x) < Real.sqrt (d * ((3 : ℝ) ^ n) ^ 2) :=
        Real.sqrt_lt_sqrt (euclideanSq_nonneg x) hlt
    _ = Real.sqrt d * (3 : ℝ) ^ n := by
        rw [Real.sqrt_mul hd0.le, Real.sqrt_sq h3.le]

theorem openCubeSet_originCube_eq_triadicCube (n : ℕ) :
    openCubeSet (originCube d (n : ℤ)) = triadicCube d n := by
  ext x
  rw [mem_openCubeSet_originCube_iff, mem_triadicCube_iff]

/-! ## The inner cutoff of a triadic cube -/

theorem tsupport_innerCubeCutoff_subset_triadicCube (n : ℕ) {τ : ℝ} (hτ : 0 < τ)
    (hτ' : τ ≤ 1 / 4) : tsupport (innerCubeCutoff (originCube d (n : ℤ)) τ) ⊆ triadicCube d n := by
  rw [← openCubeSet_originCube_eq_triadicCube]
  exact tsupport_innerCubeCutoff_subset _ hτ hτ'

theorem setAverage_sq_one_sub_innerCubeCutoff_le (n : ℕ) {τ : ℝ} (hτ : 0 < τ) (hτ' : τ ≤ 1 / 4) :
    ⨍ x in triadicCube d n, (1 - innerCubeCutoff (originCube d (n : ℤ)) τ x) ^ 2 ≤ 2 * d * τ := by
  have h := cubeAverage_sq_one_sub_innerCubeCutoff_le (originCube d (n : ℤ)) hτ hτ'
  rw [cubeAverage, cubeVolume_originCube_natCast] at h
  rw [setAverage_eq, smul_eq_mul, volumeReal_triadicCube,
    ← openCubeSet_originCube_eq_triadicCube, ← setIntegral_congr_set
      (cubeSet_ae_eq_openCubeSet (originCube d (n : ℤ)))]
  exact h

/-- The constant `d (4 d c)²` of the gradient of the inner cutoff, `c` the bound on the derivative of
the transition profile. -/
def cutoffGradConst (d : ℕ) : ℝ := d * (4 * d * smoothTransitionProfile.derivBound) ^ 2

theorem euclideanSq_gradient_innerCubeCutoff_le (n : ℕ) {τ : ℝ} (hτ : 0 < τ) (hτ' : τ ≤ 1 / 4)
    (x : Vec d) :
    euclideanSq (gradient (innerCubeCutoff (originCube d (n : ℤ)) τ) x) ≤
      cutoffGradConst d / τ ^ 2 / ((3 : ℝ) ^ n) ^ 2 := by
  have h1 := vecNormSq_smoothGrad_le (innerCubeCutoff (originCube d (n : ℤ)) τ) x
  have h2 := norm_fderiv_innerCubeCutoff_le (originCube d (n : ℤ)) hτ hτ' x
  rw [cubeScaleFactor_originCube] at h2
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have hgrad : euclideanSq (gradient (innerCubeCutoff (originCube d (n : ℤ)) τ) x) =
      vecNormSq (_root_.Homogenization.HighContrast.smoothGrad
        (innerCubeCutoff (originCube d (n : ℤ)) τ) x) := rfl
  rw [hgrad]
  refine h1.trans ((mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg d)).trans (le_of_eq ?_))
  unfold cutoffGradConst
  have h3n : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  field_simp

/-! ## Oscillation of the correctors on balls of every radius -/

/-- **Oscillation on every ball.** Under the oscillation bound above `Y ≥ 1`, the normalized
squared oscillation on `B_R` is at most `C² R² ((Y/R)^{2θ} + (Y/R)^{d+2})` for every `R > 0`. -/
theorem ballOscillation_le_of_osc {u : Vec d → ℝ}
    (hu : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R))) {Y Cφ θ : ℝ} (hY : 0 < Y)
    (hosc : ∀ ρ : ℝ, Y ≤ ρ → Real.sqrt (⨍ x in ball 0 ρ,
      |u x - ⨍ y in ball 0 ρ, u y| ^ 2) ≤ Cφ * ρ ^ (1 - θ) * Y ^ θ)
    {R : ℝ} (hR : 0 < R) :
    ballOscillation u R ≤ Cφ ^ 2 * R ^ 2 * ((Y / R) ^ (2 * θ) + (Y / R) ^ (d + 2)) := by
  have hsq : ∀ ρ : ℝ, Y ≤ ρ → ballOscillation u ρ ≤ Cφ ^ 2 * ρ ^ 2 * (Y / ρ) ^ (2 * θ) := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hY.trans_le hρ
    have h := hosc ρ hρ
    have heq : ⨍ x in ball 0 ρ, |u x - ⨍ y in ball 0 ρ, u y| ^ 2 = ballOscillation u ρ := by
      unfold ballOscillation
      simp only [sq_abs]
    rw [heq, mul_assoc, rpow_one_sub_mul_rpow_eq hρ0 hY.le] at h
    have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
    rw [Real.sq_sqrt (ballOscillation_nonneg u ρ)] at h2
    refine h2.trans (le_of_eq ?_)
    have e : (Y / ρ) ^ (2 * θ) = ((Y / ρ) ^ θ) ^ 2 := by
      rw [show 2 * θ = θ * ((2 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_mul_natCast (div_nonneg hY.le hρ0.le)]
    rw [e]
    ring
  have hpos1 : 0 ≤ (Y / R) ^ (2 * θ) := Real.rpow_nonneg (div_nonneg hY.le hR.le) _
  have hpos2 : 0 ≤ (Y / R) ^ (d + 2) := pow_nonneg (div_nonneg hY.le hR.le) _
  have hCR : 0 ≤ Cφ ^ 2 * R ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  rcases le_or_gt Y R with hYR | hRY
  · refine (hsq R hYR).trans ?_
    rw [mul_add]
    exact le_add_of_nonneg_right (mul_nonneg hCR hpos2)
  · -- small radii: compare with the ball `B_Y`
    set mY := ⨍ y in ball 0 Y, u y with hmY
    have hsub : ball (0 : Vec d) R ⊆ ball 0 Y := fun _ hx => lt_of_lt_of_le hx hRY.le
    have hfinR : volume (ball (0 : Vec d) R) ≠ ⊤ := volume_ball_ne_top hR
    have h1 : ballOscillation u R ≤ ⨍ x in ball 0 R, (u x - mY) ^ 2 :=
      setAverage_sq_sub_setAverage_le (volume_ball_ne_zero hR) hfinR (hu R hR) mY
    have hYmem := hu Y hY
    have h2 : ∫ x in ball (0 : Vec d) R, (u x - mY) ^ 2 ≤ ∫ x in ball (0 : Vec d) Y, (u x - mY) ^ 2 :=
      setIntegral_mono_set ((hYmem.sub (memLp_const _)).integrable_sq)
        (Eventually.of_forall fun x => sq_nonneg _) (Eventually.of_forall hsub)
    have hvR := volume_real_ball (d := d) hR
    have hvY := volume_real_ball (d := d) hY
    have hω : 0 < (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal :=
      ENNReal.toReal_pos (volume_euclideanBall_pos' one_pos).ne' (volume_euclideanBall_ne_top' 1)
    set ω := (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal
    have hY' := hsq Y le_rfl
    rw [div_self hY.ne', Real.one_rpow, mul_one] at hY'
    have hoscY : ballOscillation u Y =
        (Y ^ d * ω)⁻¹ * ∫ x in ball (0 : Vec d) Y, (u x - mY) ^ 2 := by
      unfold ballOscillation
      rw [setAverage_eq (f := fun x => (u x - mY) ^ 2), smul_eq_mul, hvY]
    have havgR : ⨍ x in ball 0 R, (u x - mY) ^ 2 =
        (R ^ d * ω)⁻¹ * ∫ x in ball (0 : Vec d) R, (u x - mY) ^ 2 := by
      rw [setAverage_eq (f := fun x => (u x - mY) ^ 2), smul_eq_mul, hvR]
    have hRd : 0 < R ^ d * ω := by positivity
    have hYd : 0 < Y ^ d * ω := by positivity
    have hIY : ∫ x in ball (0 : Vec d) Y, (u x - mY) ^ 2 ≤ Cφ ^ 2 * Y ^ 2 * (Y ^ d * ω) := by
      rw [hoscY, inv_mul_le_iff₀ hYd] at hY'
      linarith
    calc ballOscillation u R
        ≤ (R ^ d * ω)⁻¹ * ∫ x in ball (0 : Vec d) R, (u x - mY) ^ 2 := h1.trans (le_of_eq havgR)
      _ ≤ (R ^ d * ω)⁻¹ * (Cφ ^ 2 * Y ^ 2 * (Y ^ d * ω)) :=
          mul_le_mul_of_nonneg_left (h2.trans hIY) (inv_nonneg.mpr hRd.le)
      _ = Cφ ^ 2 * R ^ 2 * (Y / R) ^ (d + 2) := by
          rw [div_pow]
          field_simp
          ring
      _ ≤ _ := by
          rw [mul_add]
          exact le_add_of_nonneg_left (mul_nonneg hCR hpos1)

/-! ## The corrector of slope `e` -/

section Slope

variable {P : Measure (CoefficientField d Λ)}

theorem correctedField_eq_linearize (S : HomogenizationData P) (a : CoefficientField d Λ)
    (e x : Vec d) :
    correctedField S a e x = e + (S.linearize.corrector e).grad a x := by
  rw [HomogenizationData.linearize_grad]
  unfold correctedField correctedCoordinate
  simp only [smul_add, Finset.sum_add_distrib, sum_smul_unitVector_eq]

theorem linearize_potential (S : HomogenizationData P) (a : CoefficientField d Λ) (e x : Vec d) :
    (S.linearize.corrector e).potential a x =
      ∑ i, e i * (S.corrector (unitVector i)).potential a x := rfl

theorem euclideanSq_add_le_two (v w : Vec d) :
    euclideanSq (v + w) ≤ 2 * euclideanSq v + 2 * euclideanSq w := by
  unfold euclideanSq dot
  simp only [Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (v i - w i)]

theorem euclideanSq_smul_eq (c : ℝ) (v : Vec d) : euclideanSq (c • v) = c ^ 2 * euclideanSq v := by
  unfold euclideanSq dot
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The radius `√d 3ⁿ` of a ball containing `□_n`. -/
def cubeBallRadius (d n : ℕ) : ℝ := Real.sqrt d * (3 : ℝ) ^ n

theorem cubeBallRadius_pos (hd : 1 ≤ d) (n : ℕ) : 0 < cubeBallRadius d n := by
  unfold cubeBallRadius
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

/-- The sublinearity defect `(Y/R_n)^{2θ} + (Y/R_n)^{d+2}`. -/
def sublinearDefect (d n : ℕ) (θ y : ℝ) : ℝ :=
  (y / cubeBallRadius d n) ^ (2 * θ) + (y / cubeBallRadius d n) ^ (d + 2)

/-- **The dual bound almost surely.** -/
theorem ae_setIntegral_lowerDensity_le (hd : 1 ≤ d) (S : HomogenizationData P) (e : Vec d)
    (n : ℕ) :
    ∀ᵐ a ∂P, (volume.real (triadicCube d n))⁻¹ * ∫ x in triadicCube d n, lowerDensity S e a x ≤
      dirichletEnergy a (triadicCube d n) e := by
  filter_upwards [(S.linearize.corrector e).harmonic,
    (S.linearize.corrector e).locally_square_integrable] with a hh hl
  have hR := cubeBallRadius_pos hd n
  have hGeq : correctedField S a e = fun x => e + (S.linearize.corrector e).grad a x := by
    funext x
    exact correctedField_eq_linearize S a e x
  have hq : HasWeakDivergence Set.univ (fun x => (a x).mulVec (correctedField S a e x))
      (fun _ => 0) := by
    rw [hGeq]
    exact hh
  have hG : MemLp (correctedField S a e) 2 (volume.restrict (triadicCube d n)) := by
    rw [hGeq]
    exact ((memLp_const e).add (hl _ hR).2).mono_measure
      (Measure.restrict_mono (triadicCube_subset_ball hd n) le_rfl)
  have h := setAverage_flux_sub_energy_le_dirichletEnergy a (volume_triadicCube_ne_zero d n)
    (volume_triadicCube_ne_top d n) e hG hq
  refine le_of_eq_of_le ?_ h
  rw [setAverage_eq, smul_eq_mul]
  congr 1
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [ae_lowerDensity_eq S e a] with x hx
  rw [hx]

/-- **The upper bound almost surely.** -/
theorem ae_dirichletEnergy_le_energy (hd : 1 ≤ d) (hΛ : 1 ≤ Λ) (S : HomogenizationData P)
    {Y : CoefficientField d Λ → ℝ} (hY1 : ∀ a, 1 ≤ Y a) {Cφ θ : ℝ}
    (hosc : ∀ i : Fin d, ∀ᵐ a ∂P, ∀ ρ : ℝ, Y a ≤ ρ →
      Real.sqrt (⨍ x in ball 0 ρ, |(S.corrector (unitVector i)).potential a x -
        ⨍ y in ball 0 ρ, (S.corrector (unitVector i)).potential a y| ^ 2) ≤
          Cφ * ρ ^ (1 - θ) * Y a ^ θ)
    (e : Vec d) (n : ℕ) {τ : ℝ} (hτ : 0 < τ) (hτ' : τ ≤ 1 / 4) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ a ∂P, dirichletEnergy a (triadicCube d n) e ≤
      (1 + t) * ((volume.real (triadicCube d n))⁻¹ *
        ∫ x in triadicCube d n, (1 / 2 : ℝ) * energyDensity S e a x) +
      (1 + t⁻¹) * ((1 / 2) * Λ * (4 * d * τ * euclideanSq e +
        2 * (cutoffGradConst d / τ ^ 2) *
          (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal *
            Real.sqrt d ^ d * d * (d * euclideanSq e * Cφ ^ 2) *
              sublinearDefect d n θ (Y a))) := by
  filter_upwards [ae_all_iff.mpr hosc, (S.linearize.corrector e).weak_gradient,
    (S.linearize.corrector e).locally_square_integrable,
    ae_all_iff.mpr fun i : Fin d => (S.corrector (unitVector i)).locally_square_integrable]
    with a hosca hw hl hli
  set R := cubeBallRadius d n with hRdef
  have hR := cubeBallRadius_pos hd n
  set U := triadicCube d n with hU
  set pot := (S.linearize.corrector e).potential a with hpot
  set m := ⨍ y in ball 0 R, pot y with hm
  set u : Vec d → ℝ := fun x => pot x - m with hu
  set g := (S.linearize.corrector e).grad a with hg
  set η := innerCubeCutoff (originCube d (n : ℤ)) τ with hη
  set ω := (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal with hω
  have hω0 : 0 < ω :=
    ENNReal.toReal_pos (volume_euclideanBall_pos' one_pos).ne' (volume_euclideanBall_ne_top' 1)
  have hUB : U ⊆ ball 0 R := triadicCube_subset_ball hd n
  have hUfin : volume U ≠ ⊤ := volume_triadicCube_ne_top d n
  have hU0 : volume U ≠ 0 := volume_triadicCube_ne_zero d n
  have hVU : volume.real U = ((3 : ℝ) ^ n) ^ d := volumeReal_triadicCube n
  have hfinU : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUfin
  have huL : MemLp u 2 (volume.restrict U) :=
    (((hl R hR).1).sub (memLp_const m)).mono_measure (Measure.restrict_mono hUB le_rfl)
  have hgL : MemLp g 2 (volume.restrict U) :=
    ((hl R hR).2).mono_measure (Measure.restrict_mono hUB le_rfl)
  have hwU : HasWeakGradient U u g :=
    hasWeakGradient_sub_const U (hasWeakGradient_mono (Set.subset_univ _) hw) m
  have hηs := innerCubeCutoff_smooth (originCube d (n : ℤ)) hτ hτ'
  have hηc := innerCubeCutoff_hasCompactSupport (originCube d (n : ℤ)) hτ hτ'
  have hηU := tsupport_innerCubeCutoff_subset_triadicCube (d := d) n hτ hτ'
  have h := dirichletEnergy_le_of_cutoff a (isOpenBoundedConvexDomain_triadicCube n) hU0 e
    huL hgL hwU hηs hηc hηU (innerCubeCutoff_nonneg _ _) (innerCubeCutoff_le_one _ _) ht
  have ht' : 0 ≤ 1 + t⁻¹ := by have := inv_pos.mpr ht; linarith
  refine h.trans (add_le_add (le_of_eq ?_) (mul_le_mul_of_nonneg_left ?_ ht'))
  · -- the energy
    rw [setAverage_eq, smul_eq_mul]
    congr 2
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [ae_energyDensity_eq S e a] with x hx
    rw [hx, correctedField_eq_linearize]
  · -- the error
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) (zero_le_one.trans hΛ))
    have hgradη := euclideanSq_gradient_innerCubeCutoff_le (d := d) n hτ hτ'
    set Bη := cutoffGradConst d / τ ^ 2 / ((3 : ℝ) ^ n) ^ 2 with hBη
    have hBη0 : 0 ≤ Bη := by
      rw [hBη, cutoffGradConst]
      positivity
    have hpt : ∀ x, euclideanSq ((1 - η x) • e + u x • gradient η x) ≤
        2 * euclideanSq e * (1 - η x) ^ 2 + 2 * Bη * u x ^ 2 := by
      intro x
      refine (euclideanSq_add_le_two _ _).trans ?_
      rw [euclideanSq_smul_eq, euclideanSq_smul_eq]
      have h1 := hgradη x
      have hu2 := sq_nonneg (u x)
      have he := euclideanSq_nonneg e
      nlinarith
    have hcont : Continuous fun v : Vec d => euclideanSq v := by
      unfold euclideanSq dot
      fun_prop
    have hgc : Continuous (gradient η) :=
      continuous_pi fun k => (contDiff_coordinateDerivative_top hηs k).continuous
    have hZm : AEStronglyMeasurable (fun x => euclideanSq ((1 - η x) • e + u x • gradient η x))
        (volume.restrict U) :=
      hcont.comp_aestronglyMeasurable
        ((((continuous_const.sub hηs.continuous).smul continuous_const).aestronglyMeasurable).add
          (huL.aestronglyMeasurable.smul hgc.aestronglyMeasurable))
    have hη2 : Integrable (fun x => (1 - η x) ^ 2) (volume.restrict U) := by
      refine Integrable.of_bound (C := 1)
        ((continuous_const.sub hηs.continuous).pow 2).aestronglyMeasurable
        (Eventually.of_forall fun x => ?_)
      have h0 := innerCubeCutoff_nonneg (originCube d (n : ℤ)) τ x
      have h1 := innerCubeCutoff_le_one (originCube d (n : ℤ)) τ x
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      nlinarith
    have hu2 : Integrable (fun x => u x ^ 2) (volume.restrict U) := huL.integrable_sq
    have hdom : Integrable (fun x => 2 * euclideanSq e * (1 - η x) ^ 2 + 2 * Bη * u x ^ 2)
        (volume.restrict U) := (hη2.const_mul _).add (hu2.const_mul _)
    have hZi : Integrable (fun x => euclideanSq ((1 - η x) • e + u x • gradient η x))
        (volume.restrict U) :=
      hdom.mono' hZm (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (euclideanSq_nonneg _)]
        exact hpt x)
    have hVU0 : 0 < volume.real U := ENNReal.toReal_pos hU0 hUfin
    -- the average of `u²`
    have hR2 : R ^ 2 = d * ((3 : ℝ) ^ n) ^ 2 := by
      rw [hRdef, cubeBallRadius, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    have hRd : R ^ d = Real.sqrt d ^ d * ((3 : ℝ) ^ n) ^ d := by
      rw [hRdef, cubeBallRadius, mul_pow]
    have hint_u : ∫ x in U, u x ^ 2 ≤ ∫ x in ball (0 : Vec d) R, u x ^ 2 :=
      setIntegral_mono_set (((hl R hR).1.sub (memLp_const m)).integrable_sq)
        (Eventually.of_forall fun x => sq_nonneg _) (Eventually.of_forall hUB)
    have hballR : ∫ x in ball (0 : Vec d) R, u x ^ 2 = R ^ d * ω * ballOscillation pot R := by
      have hpos : 0 < R ^ d * ω := by positivity
      have h1 : ballOscillation pot R = (R ^ d * ω)⁻¹ * ∫ x in ball (0 : Vec d) R, u x ^ 2 := by
        unfold ballOscillation
        rw [setAverage_eq, smul_eq_mul, volume_real_ball hR]
      rw [h1, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
    have hosc_pot : ballOscillation pot R ≤ d * euclideanSq e * (Cφ ^ 2 * R ^ 2 *
        sublinearDefect d n θ (Y a)) := by
      have hsum := ballOscillation_finsetSum_le (f := fun i : Fin d =>
        (S.corrector (unitVector i)).potential a) e (R := R) fun i => (hli i R hR).1
      have hpot_eq : pot = fun x => ∑ i, e i * (S.corrector (unitVector i)).potential a x := by
        funext x
        exact linearize_potential S a e x
      rw [hpot_eq]
      refine hsum.trans ?_
      rw [Fintype.card_fin]
      have hY0 : 0 < Y a := lt_of_lt_of_le one_pos (hY1 a)
      have hi : ∀ i : Fin d, ballOscillation ((S.corrector (unitVector i)).potential a) R ≤
          Cφ ^ 2 * R ^ 2 * sublinearDefect d n θ (Y a) := fun i =>
        ballOscillation_le_of_osc (fun R hR => (hli i R hR).1) hY0 (hosca i) hR
      have hsq : ∑ i, e i ^ 2 = euclideanSq e := by
        unfold euclideanSq dot
        exact Finset.sum_congr rfl fun i _ => sq _
      calc (d : ℝ) * ∑ i, e i ^ 2 * ballOscillation ((S.corrector (unitVector i)).potential a) R
          ≤ d * ∑ i, e i ^ 2 * (Cφ ^ 2 * R ^ 2 * sublinearDefect d n θ (Y a)) := by
            gcongr with i
            exact hi i
        _ = d * euclideanSq e * (Cφ ^ 2 * R ^ 2 * sublinearDefect d n θ (Y a)) := by
            rw [← Finset.sum_mul, hsq]
            ring
    have havg_u : (volume.real U)⁻¹ * ∫ x in U, u x ^ 2 ≤
        Real.sqrt d ^ d * ω * (d * euclideanSq e * (Cφ ^ 2 * R ^ 2 *
          sublinearDefect d n θ (Y a))) := by
      rw [hVU]
      have h3 : (0 : ℝ) < ((3 : ℝ) ^ n) ^ d := by positivity
      rw [inv_mul_le_iff₀ h3]
      calc ∫ x in U, u x ^ 2 ≤ R ^ d * ω * ballOscillation pot R := hint_u.trans (le_of_eq hballR)
        _ ≤ R ^ d * ω * (d * euclideanSq e * (Cφ ^ 2 * R ^ 2 * sublinearDefect d n θ (Y a))) :=
            mul_le_mul_of_nonneg_left hosc_pot (by positivity)
        _ = _ := by rw [hRd]; ring
    have hη2avg := setAverage_sq_one_sub_innerCubeCutoff_le (d := d) n hτ hτ'
    rw [setAverage_eq, smul_eq_mul] at hη2avg
    rw [setAverage_eq, smul_eq_mul]
    calc (volume.real U)⁻¹ * ∫ x in U, euclideanSq ((1 - η x) • e + u x • gradient η x)
        ≤ (volume.real U)⁻¹ * ∫ x in U, (2 * euclideanSq e * (1 - η x) ^ 2 + 2 * Bη * u x ^ 2) :=
          mul_le_mul_of_nonneg_left (integral_mono hZi hdom hpt) (inv_nonneg.mpr hVU0.le)
      _ = 2 * euclideanSq e * ((volume.real U)⁻¹ * ∫ x in U, (1 - η x) ^ 2) +
            2 * Bη * ((volume.real U)⁻¹ * ∫ x in U, u x ^ 2) := by
          rw [integral_add (hη2.const_mul _) (hu2.const_mul _), integral_const_mul,
            integral_const_mul]
          ring
      _ ≤ 2 * euclideanSq e * (2 * d * τ) + 2 * Bη * (Real.sqrt d ^ d * ω *
            (d * euclideanSq e * (Cφ ^ 2 * R ^ 2 * sublinearDefect d n θ (Y a)))) := by
          have he := euclideanSq_nonneg e
          gcongr
      _ = 4 * d * τ * euclideanSq e + 2 * (cutoffGradConst d / τ ^ 2) * ω *
            Real.sqrt d ^ d * d * (d * euclideanSq e * Cφ ^ 2) *
              sublinearDefect d n θ (Y a) := by
          rw [hBη, hR2]
          have h3 : (0 : ℝ) < ((3 : ℝ) ^ n) ^ 2 := by positivity
          field_simp
          ring

theorem one_le_cubeBallRadius (hd : 1 ≤ d) (n : ℕ) : 1 ≤ cubeBallRadius d n := by
  unfold cubeBallRadius
  have h1 : (1 : ℝ) ≤ Real.sqrt d := Real.one_le_sqrt.mpr (by exact_mod_cast hd)
  have h2 : (1 : ℝ) ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  nlinarith

theorem sublinearDefect_nonneg (d n : ℕ) (θ : ℝ) {y : ℝ} (hy : 0 ≤ y) (hd : 1 ≤ d) :
    0 ≤ sublinearDefect d n θ y := by
  unfold sublinearDefect
  have h : 0 ≤ y / cubeBallRadius d n := div_nonneg hy (cubeBallRadius_pos hd n).le
  exact add_nonneg (Real.rpow_nonneg h _) (pow_nonneg h _)

theorem sublinearDefect_le (hd : 1 ≤ d) (n : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) {y : ℝ}
    (hy : 1 ≤ y) : sublinearDefect d n θ y ≤ y ^ 2 + y ^ (d + 2) := by
  unfold sublinearDefect
  have hR := one_le_cubeBallRadius hd n
  have hR0 : 0 < cubeBallRadius d n := lt_of_lt_of_le one_pos hR
  have hy0 : 0 ≤ y := le_trans zero_le_one hy
  have hq : y / cubeBallRadius d n ≤ y := div_le_self hy0 hR
  have hq0 : 0 ≤ y / cubeBallRadius d n := by positivity
  have h1 : (y / cubeBallRadius d n) ^ (2 * θ) ≤ y ^ 2 := by
    calc (y / cubeBallRadius d n) ^ (2 * θ) ≤ y ^ (2 * θ) :=
          Real.rpow_le_rpow hq0 hq (by positivity)
      _ ≤ y ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy (by linarith)
      _ = y ^ 2 := by norm_cast
  have h2 : (y / cubeBallRadius d n) ^ (d + 2) ≤ y ^ (d + 2) := pow_le_pow_left₀ hq0 hq _
  linarith

theorem tendsto_sublinearDefect (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 < θ) (y : ℝ) :
    Tendsto (fun n : ℕ => sublinearDefect d n θ y) atTop (𝓝 0) := by
  have hR : Tendsto (fun n : ℕ => cubeBallRadius d n) atTop atTop := by
    unfold cubeBallRadius
    have hs : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3)).const_mul_atTop hs
  have hq : Tendsto (fun n : ℕ => y / cubeBallRadius d n) atTop (𝓝 0) := by
    have := hR.inv_tendsto_atTop.const_mul y
    simpa [div_eq_mul_inv] using this
  have h1 : Tendsto (fun n : ℕ => (y / cubeBallRadius d n) ^ (2 * θ)) atTop (𝓝 0) := by
    have := hq.rpow_const (p := 2 * θ) (Or.inr (by positivity))
    rwa [Real.zero_rpow (by positivity)] at this
  have h2 : Tendsto (fun n : ℕ => (y / cubeBallRadius d n) ^ (d + 2)) atTop (𝓝 0) := by
    have := hq.pow (d + 2)
    rwa [zero_pow (by omega)] at this
  have := h1.add h2
  rw [add_zero] at this
  exact this

end Slope

/-! ## The identification -/

section Identification

variable {P : Measure (CoefficientField d Λ)}

/-- **The homogenized matrix is the matrix of the Gaussian averages.** -/
theorem homogenized_eq_of_basisBounds (hd : 1 ≤ d) (hΛ : 1 ≤ Λ) (hP : LawHypotheses P)
    (S : HomogenizationData P) {M : Mat d} {Y : CoefficientField d Λ → ℝ} (hYm : Measurable Y)
    (hY1 : ∀ a, 1 ≤ Y a) (hYmom : ∀ p : ℕ, Integrable (fun a => Y a ^ p) P) {Cε θB : ℝ}
    (hCε : 0 ≤ Cε) (hθB : 0 < θB)
    (hB : ∀ᵐ a ∂P, ∀ (r : ℝ) (x₀ : Vec d), Y a ≤ r → euclideanNorm x₀ ≤ r →
      GaussianBasisBounds a M (correctedCoordinate S a) x₀ r (Cε * (Y a / r) ^ θB))
    {Cφ θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hosc : ∀ i : Fin d, ∀ᵐ a ∂P, ∀ ρ : ℝ, Y a ≤ ρ →
      Real.sqrt (⨍ x in ball 0 ρ, |(S.corrector (unitVector i)).potential a x -
        ⨍ y in ball 0 ρ, (S.corrector (unitVector i)).potential a y| ^ 2) ≤
          Cφ * ρ ^ (1 - θ) * Y a ^ θ) :
    S.homogenized = M := by
  have : IsProbabilityMeasure P := hP.1
  have hY0 : ∀ a, 0 ≤ Y a := fun a => zero_le_one.trans (hY1 a)
  have hΛ0 : 0 ≤ Λ := zero_le_one.trans hΛ
  have hMsym := transpose_eq_of_basisBounds S hY0 hθB hB
  refine eq_of_forall_dot_mulVec_eq S.symmetric hMsym fun e => ?_
  have hlim := S.variational_limit e
  obtain ⟨hcE, hcL⟩ := setIntegral_cell_energy_lowerDensity_eq hP S (hYmom d) hCε hθB hY1 hB e
  set K := energyEnvelopeConst M Cε e with hK
  have hKint : Integrable (fun a => K * (1 + Y a ^ d)) P :=
    ((integrable_const 1).add (hYmom d)).const_mul _
  have hVn : ∀ n : ℕ, volume.real (triadicCube d n) = ((3 : ℝ) ^ n) ^ d := fun n =>
    volumeReal_triadicCube n
  have h3n : ∀ n : ℕ, (0 : ℝ) < ((3 : ℝ) ^ n) ^ d := fun n => by positivity
  -- the lower bound
  have hlow : ∀ n : ℕ, (1 / 2 : ℝ) * dot e (M.mulVec e) ≤
      ∫ a, dirichletEnergy a (triadicCube d n) e ∂P := by
    intro n
    obtain ⟨hint, heq⟩ := integral_setIntegral_triadicCube_eq hP.2.1
      (measurable_lowerDensity S e).stronglyMeasurable (ae_lowerDensity_add_latticeShift S e)
      ((integrable_const _).add hKint) (ae_lowerDensity_envelope S hCε hθB hY1 hB e) n
    rw [hcL] at heq
    calc (1 / 2 : ℝ) * dot e (M.mulVec e)
        = (volume.real (triadicCube d n))⁻¹ *
            ∫ a, (∫ x in triadicCube d n, lowerDensity S e a x) ∂P := by
          rw [heq, hVn, inv_mul_cancel_left₀ (h3n n).ne']
      _ = ∫ a, (volume.real (triadicCube d n))⁻¹ *
            (∫ x in triadicCube d n, lowerDensity S e a x) ∂P := (integral_const_mul _ _).symm
      _ ≤ ∫ a, dirichletEnergy a (triadicCube d n) e ∂P :=
          integral_mono_ae (hint.const_mul _) (integrable_dirichletEnergy_triadicCube hΛ0 n e)
            (ae_setIntegral_lowerDensity_le hd S e n)
  have hA1 : (1 / 2 : ℝ) * dot e (M.mulVec e) ≤
      (1 / 2 : ℝ) * dot e (S.homogenized.mulVec e) :=
    ge_of_tendsto hlim (Eventually.of_forall hlow)
  -- the upper bound for a cutoff width `τ` and a splitting parameter `t`
  set Q := (1 / 2 : ℝ) * Λ * (4 * d * euclideanSq e) with hQ
  have hup : ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 4 → ∀ t : ℝ, 0 < t →
      (1 / 2 : ℝ) * dot e (S.homogenized.mulVec e) ≤
        (1 + t) * ((1 / 2 : ℝ) * dot e (M.mulVec e)) + (1 + t⁻¹) * (Q * τ) := by
    intro τ hτ hτ' t ht
    set Kψ := 2 * (cutoffGradConst d / τ ^ 2) *
      (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal *
        Real.sqrt d ^ d * d * (d * euclideanSq e * Cφ ^ 2) with hKψ
    have hψm : ∀ n : ℕ, Measurable fun a => sublinearDefect d n θ (Y a) := by
      intro n
      unfold sublinearDefect
      exact ((hYm.div_const _).pow_const _).add ((hYm.div_const _).pow_const _)
    have hψi : ∀ n : ℕ, Integrable (fun a => sublinearDefect d n θ (Y a)) P := fun n =>
      ((hYmom 2).add (hYmom (d + 2))).mono' (hψm n).aestronglyMeasurable
        (Eventually.of_forall fun a => by
          rw [Real.norm_of_nonneg (sublinearDefect_nonneg d n θ (hY0 a) hd)]
          exact sublinearDefect_le hd n hθ.le hθ1 (hY1 a))
    have hψlim : Tendsto (fun n : ℕ => ∫ a, sublinearDefect d n θ (Y a) ∂P) atTop (𝓝 0) := by
      have h := tendsto_integral_of_dominated_convergence (fun a => Y a ^ 2 + Y a ^ (d + 2))
        (fun n => (hψm n).aestronglyMeasurable) ((hYmom 2).add (hYmom (d + 2)))
        (fun n => Eventually.of_forall fun a => by
          rw [Real.norm_of_nonneg (sublinearDefect_nonneg d n θ (hY0 a) hd)]
          exact sublinearDefect_le hd n hθ.le hθ1 (hY1 a))
        (Eventually.of_forall fun a => tendsto_sublinearDefect hd hθ (Y a))
      simpa using h
    have hstep : ∀ n : ℕ, ∫ a, dirichletEnergy a (triadicCube d n) e ∂P ≤
        (1 + t) * ((1 / 2 : ℝ) * dot e (M.mulVec e)) +
          (1 + t⁻¹) * ((1 / 2) * Λ * (4 * d * τ * euclideanSq e +
            Kψ * ∫ a, sublinearDefect d n θ (Y a) ∂P)) := by
      intro n
      obtain ⟨hint, heq⟩ := integral_setIntegral_triadicCube_eq hP.2.1
        (measurable_energyDensity S e).stronglyMeasurable (ae_energyDensity_add_latticeShift S e)
        hKint (ae_energy_envelope S hCε hθB hY1 hB e) n
      rw [hcE] at heq
      have hae := ae_dirichletEnergy_le_energy hd hΛ S hY1 hosc e n hτ hτ' ht
      have hhalf : ∀ a, (volume.real (triadicCube d n))⁻¹ *
          ∫ x in triadicCube d n, (1 / 2 : ℝ) * energyDensity S e a x =
            (1 / 2 : ℝ) * ((volume.real (triadicCube d n))⁻¹ *
              ∫ x in triadicCube d n, energyDensity S e a x) := fun a => by
        rw [integral_const_mul]
        ring
      simp only [hhalf] at hae
      have hRHSi : Integrable (fun a => (1 + t) * ((1 / 2 : ℝ) *
          ((volume.real (triadicCube d n))⁻¹ * ∫ x in triadicCube d n, energyDensity S e a x)) +
            (1 + t⁻¹) * ((1 / 2) * Λ * (4 * d * τ * euclideanSq e +
              Kψ * sublinearDefect d n θ (Y a)))) P :=
        (((hint.const_mul _).const_mul _).const_mul _).add
          ((((integrable_const _).add ((hψi n).const_mul _)).const_mul _).const_mul _)
      refine (integral_mono_ae (integrable_dirichletEnergy_triadicCube hΛ0 n e) hRHSi hae).trans
        (le_of_eq ?_)
      rw [integral_add (f := fun a => (1 + t) * ((1 / 2 : ℝ) *
          ((volume.real (triadicCube d n))⁻¹ * ∫ x in triadicCube d n, energyDensity S e a x)))
        (g := fun a => (1 + t⁻¹) * ((1 / 2) * Λ * (4 * d * τ * euclideanSq e +
          Kψ * sublinearDefect d n θ (Y a))))
        (((hint.const_mul _).const_mul _).const_mul _)
        ((((integrable_const _).add ((hψi n).const_mul _)).const_mul _).const_mul _),
        integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
        integral_const_mul, integral_add (f := fun _ => 4 * d * τ * euclideanSq e)
          (g := fun a => Kψ * sublinearDefect d n θ (Y a)) (integrable_const _)
          ((hψi n).const_mul _),
        integral_const, integral_const_mul, heq, hVn, inv_mul_cancel_left₀ (h3n n).ne']
      simp only [probReal_univ, one_smul]
    have hRHS : Tendsto (fun n : ℕ => (1 + t) * ((1 / 2 : ℝ) * dot e (M.mulVec e)) +
        (1 + t⁻¹) * ((1 / 2) * Λ * (4 * d * τ * euclideanSq e +
          Kψ * ∫ a, sublinearDefect d n θ (Y a) ∂P))) atTop
        (𝓝 ((1 + t) * ((1 / 2 : ℝ) * dot e (M.mulVec e)) + (1 + t⁻¹) * (Q * τ))) := by
      have h := ((((hψlim.const_mul Kψ).const_add (4 * d * τ * euclideanSq e)).const_mul
        ((1 / 2) * Λ)).const_mul (1 + t⁻¹)).const_add ((1 + t) * ((1 / 2 : ℝ) * dot e (M.mulVec e)))
      convert h using 2
      rw [hQ]
      ring
    exact le_of_tendsto_of_tendsto' hlim hRHS hstep
  -- letting `τ → 0` and then `t → 0`
  have hA2 : ∀ t : ℝ, 0 < t → (1 / 2 : ℝ) * dot e (S.homogenized.mulVec e) ≤
      (1 + t) * ((1 / 2 : ℝ) * dot e (M.mulVec e)) := by
    intro t ht
    have hT : Tendsto (fun τ : ℝ => (1 + t) * ((1 / 2 : ℝ) * dot e (M.mulVec e)) +
        (1 + t⁻¹) * (Q * τ)) (𝓝[>] 0) (𝓝 ((1 + t) * ((1 / 2 : ℝ) * dot e (M.mulVec e)))) := by
      have hc : Continuous (fun τ : ℝ => (1 + t) * ((1 / 2 : ℝ) * dot e (M.mulVec e)) +
          (1 + t⁻¹) * (Q * τ)) := by fun_prop
      have h := hc.tendsto 0
      simp only [mul_zero, add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hT ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with τ hτ
    exact hup τ hτ.1 hτ.2.le t ht
  have hT2 : Tendsto (fun t : ℝ => (1 + t) * ((1 / 2 : ℝ) * dot e (M.mulVec e))) (𝓝[>] 0)
      (𝓝 ((1 / 2 : ℝ) * dot e (M.mulVec e))) := by
    have hc : Continuous (fun t : ℝ => (1 + t) * ((1 / 2 : ℝ) * dot e (M.mulVec e))) := by
      fun_prop
    have h := hc.tendsto 0
    simp only [add_zero, one_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hA3 : (1 / 2 : ℝ) * dot e (S.homogenized.mulVec e) ≤ (1 / 2 : ℝ) * dot e (M.mulVec e) :=
    ge_of_tendsto hT2 (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hA2 t ht)
  linarith

end Identification


end QSH
