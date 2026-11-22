import QuantitativeStochasticHomogenization.Ch03.Sec03.ExcessIteration
import QuantitativeStochasticHomogenization.Ch03.Sec03HigherOrderRegularityAndLiouville
import QuantitativeStochasticHomogenization.Ch04.Sec01.J1HeatSharpBound
import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatSelectedFluxPotential
import QuantitativeStochasticHomogenization.Ch03.Sec04.CoefficientSigma
import QuantitativeStochasticHomogenization.Ch03.Sec04.CoordinateNormBound

/-!
# One step of the quadratic excess decay and the first-order Liouville theorem

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 3.3, the first-order proof of Theorem 3.8 for `k = 1`. A `SublinearCorrectorFamily`
of a coefficient field `a` consists of coordinate correctors `φᵢ` and pointwise skew flux
correctors `σᵢ` with `∇·σᵢ = a(eᵢ + ∇φᵢ) - D eᵢ`, both of oscillation `C₁ R^{1-μ}` on balls
`B_R`, `R ≥ R₀`. Let `M` be invertible with `M Mᵀ = ½(D + Dᵀ)` and `E_R = M B_R`.

`quarterExcessStepStatement` is the deterministic estimate (3) of the first-order proof: for
`R ≥ R₁`, every element of `A₁` minus a corrected affine function `ℓ` is approximated on
`E_{R/2}` by a corrected affine function up to `¼ (1 + C R^{-ν})` times its normalized `L²`
norm on `E_R`. Its proof combines the harmonic approximation (2) on nearly full ellipsoids with
the expansion of `½(D + Dᵀ)`-harmonic functions in homogeneous harmonic polynomials.

`exists_ae_eq_correctedAffineOf` derives from it that every element of `A₁` is a corrected
affine function, by the excess iteration on the ellipsoids `E_R`, which are increasing, cover the
space, and lie in balls `B_{LR}` of comparable volume.
-/

open MeasureTheory Filter Topology
open scoped Pointwise

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The corrected affine function `c + p · x + ∑ᵢ pᵢ φᵢ(x)` of a family of correctors. -/
def correctedAffineOf (φ : Fin d → Vec d → ℝ) (c : ℝ) (p : Vec d) (x : Vec d) : ℝ :=
  c + dot p x + ∑ i, p i * φ i x

/-- Coordinate correctors and skew flux correctors of a coefficient field `a`, with homogenized
matrix `D` and oscillation `C₁ R^{1-μ}` on the balls `B_R`, `R ≥ R₀`. -/
structure SublinearCorrectorFamily {Λ : ℝ} (a : CoefficientField d Λ) (D : Mat d)
    (μ C₁ R₀ : ℝ) where
  /-- The corrector potentials. -/
  φ : Fin d → Vec d → ℝ
  /-- The corrector gradients. -/
  gφ : Fin d → Vec d → Vec d
  /-- The flux correctors. -/
  σ : Fin d → Vec d → Mat d
  /-- The gradients of the flux correctors. -/
  gσ : Fin d → Fin d → Fin d → Vec d → Vec d
  weak_gradient_φ : ∀ i, HasWeakGradient Set.univ (φ i) (gφ i)
  weak_gradient_σ : ∀ i j k, HasWeakGradient Set.univ (fun x => σ i x j k) (gσ i j k)
  memLp : ∀ i (R : ℝ), 0 < R → MemLp (φ i) 2 (volume.restrict (ball 0 R)) ∧
    MemLp (gφ i) 2 (volume.restrict (ball 0 R)) ∧
    ∀ j k, MemLp (fun x => σ i x j k) 2 (volume.restrict (ball 0 R)) ∧
      MemLp (gσ i j k) 2 (volume.restrict (ball 0 R))
  harmonic : ∀ i, HasWeakDivergence Set.univ (fun x => (a x).mulVec (unitVector i + gφ i x))
    (fun _ => 0)
  flux : ∀ i j, HasWeakDivergence Set.univ (fun x k => σ i x j k)
    (fun x => ((a x).mulVec (unitVector i + gφ i x)) j - (D.mulVec (unitVector i)) j)
  skew : ∀ i x j k, σ i x j k = -σ i x k j
  oscillation : ∀ i (R : ℝ), R₀ ≤ R →
    scalarRms volume (ball 0 R) (fun x => φ i x - ⨍ y in ball 0 R, φ i y) +
      ∑ j, ∑ k, scalarRms volume (ball 0 R) (fun x => σ i x j k - ⨍ y in ball 0 R, σ i y j k) ≤
        C₁ * R ^ (1 - μ)

/-- The ellipsoid `E_R = M B_R`. -/
def matrixEllipsoid (M : Mat d) (R : ℝ) : Set (Vec d) := Matrix.toLin' M '' ball 0 R

/-- **One step of the quadratic excess decay**, (3) of the first-order proof of Theorem 3.8,
`k = 1` (deterministic). -/
def quarterExcessStepStatement : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ Λ μ C₁ : ℝ, 1 ≤ Λ → 0 < μ → μ ≤ 1 / 2 → 0 ≤ C₁ →
  ∀ D : Mat d, (∀ ξ : Vec d, ξ ≠ 0 → 0 < dot ξ (D.mulVec ξ)) →
  ∃ (M : Mat d) (C ν : ℝ), M.det ≠ 0 ∧ M * M.transpose = (1 / 2 : ℝ) • (D + D.transpose) ∧
    0 < ν ∧ ∀ R₀ : ℝ, 1 ≤ R₀ → ∃ R₁ : ℝ, R₀ ≤ R₁ ∧
    ∀ (a : CoefficientField d Λ) (F : SublinearCorrectorFamily a D μ C₁ R₀) (w : HarmonicA1 a),
    ∀ R : ℝ, R₁ ≤ R → ∀ (c : ℝ) (p : Vec d), ∃ (c' : ℝ) (p' : Vec d),
      scalarRms volume (matrixEllipsoid M (R / 2))
          (fun x => w.potential x - correctedAffineOf F.φ (c + c') (p + p') x) ≤
        1 / 4 * (1 + C * R ^ (-ν)) *
          scalarRms volume (matrixEllipsoid M R)
            (fun x => w.potential x - correctedAffineOf F.φ c p x)

/-- An operator bound for a matrix in the Euclidean norm. -/
theorem euclideanNorm_mulVec_le (M : Mat d) (y : Vec d) :
    euclideanNorm (M.mulVec y) ≤ Real.sqrt (∑ i, ∑ j, M i j ^ 2) * euclideanNorm y := by
  have hrow : ∀ i, (M.mulVec y i) ^ 2 ≤ (∑ j, M i j ^ 2) * euclideanSq y := by
    intro i
    have h := dot_sq_le_euclideanSq_mul (fun j => M i j) y
    have e1 : dot (fun j => M i j) y = M.mulVec y i := rfl
    have e2 : euclideanSq (fun j => M i j) = ∑ j, M i j ^ 2 := by
      unfold euclideanSq dot
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1, e2] at h
    exact h
  have hsq : euclideanSq (M.mulVec y) ≤ (∑ i, ∑ j, M i j ^ 2) * euclideanSq y := by
    calc euclideanSq (M.mulVec y) = ∑ i, (M.mulVec y i) ^ 2 := by
          unfold euclideanSq dot
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i, (∑ j, M i j ^ 2) * euclideanSq y := Finset.sum_le_sum fun i _ => hrow i
      _ = _ := by rw [Finset.sum_mul]
  have hS : 0 ≤ ∑ i, ∑ j, M i j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  calc euclideanNorm (M.mulVec y) = Real.sqrt (euclideanSq (M.mulVec y)) := rfl
    _ ≤ Real.sqrt ((∑ i, ∑ j, M i j ^ 2) * euclideanSq y) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (∑ i, ∑ j, M i j ^ 2) * euclideanNorm y := Real.sqrt_mul hS _

theorem ball_zero_mul_eq_smul {L : ℝ} (hL : 0 < L) (R : ℝ) :
    ball (0 : Vec d) (L * R) = L • ball (0 : Vec d) R := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hL.ne']
  change euclideanNorm (x - 0) < L * R ↔ euclideanNorm (L⁻¹ • x - 0) < R
  rw [sub_zero, sub_zero, euclideanNorm_smul_of_zero_le _ (inv_nonneg.2 hL.le), inv_mul_lt_iff₀ hL]

theorem volume_matrixEllipsoid (M : Mat d) (R : ℝ) :
    volume (matrixEllipsoid M R) = ENNReal.ofReal |M.det| * volume (ball (0 : Vec d) R) := by
  unfold matrixEllipsoid
  rw [MeasureTheory.Measure.addHaar_image_linearMap, LinearMap.det_toLin']

theorem volume_ball_zero_mul {L : ℝ} (hL : 0 < L) (R : ℝ) :
    volume (ball (0 : Vec d) (L * R)) = ENNReal.ofReal (L ^ d) * volume (ball (0 : Vec d) R) := by
  rw [ball_zero_mul_eq_smul hL, MeasureTheory.Measure.addHaar_smul, Module.finrank_fin_fun,
    abs_of_pos (pow_pos hL d)]

/-- **First-order Liouville theorem from one step of the quadratic excess decay**
(deterministic): every element of `A₁` is almost everywhere a corrected affine function. -/
theorem exists_ae_eq_correctedAffineOf (hstep : quarterExcessStepStatement) (hd : 2 ≤ d)
    {Λ μ C₁ R₀ : ℝ} (hΛ : 1 ≤ Λ) (hμ : 0 < μ) (hμ' : μ ≤ 1 / 2) (hC₁ : 0 ≤ C₁) (hR₀ : 1 ≤ R₀)
    {D : Mat d} (hD : ∀ ξ : Vec d, ξ ≠ 0 → 0 < dot ξ (D.mulVec ξ)) {a : CoefficientField d Λ}
    (F : SublinearCorrectorFamily a D μ C₁ R₀) (w : HarmonicA1 a) :
    ∃ (c : ℝ) (p : Vec d), ∀ᵐ x ∂(volume : Measure (Vec d)),
      w.potential x = correctedAffineOf F.φ c p x := by
  obtain ⟨M, C, ν, hdet, -, hν, hR⟩ := hstep d hd Λ μ C₁ hΛ hμ hμ' hC₁ D hD
  obtain ⟨R₁, hR₀₁, hone⟩ := hR R₀ hR₀
  have hR₁ : 0 < R₁ := by linarith
  set f : Option (Fin d) → Vec d → ℝ := fun o x => Option.elim o 1 (fun i => x i + F.φ i x)
    with hfdef
  have hsum : ∀ (coeff : Option (Fin d) → ℝ) (x : Vec d), ∑ o, coeff o * f o x =
      correctedAffineOf F.φ (coeff none) (fun i => coeff (some i)) x := by
    intro coeff x
    simp only [Fintype.sum_option, hfdef, Option.elim, correctedAffineOf, dot, mul_one, mul_add,
      Finset.sum_add_distrib]
    ring
  set L : ℝ := Real.sqrt (∑ i, ∑ j, M i j ^ 2) + 1 with hLdef
  have hL : 0 < L := by positivity
  set κ : ℝ := L ^ d / |M.det| with hκdef
  have hdet0 : 0 < |M.det| := abs_pos.2 hdet
  have hκ : 0 ≤ κ := by positivity
  have hmono : Monotone (matrixEllipsoid M) := by
    intro R R' hRR'
    refine Set.image_mono fun y hy => ?_
    change euclideanNorm (y - 0) < R'
    have : euclideanNorm (y - 0) < R := hy
    linarith
  have hcover : ∀ x, ∃ R, x ∈ matrixEllipsoid M R := by
    intro x
    refine ⟨euclideanNorm (M⁻¹.mulVec x) + 1, M⁻¹.mulVec x, ?_, ?_⟩
    · change euclideanNorm (M⁻¹.mulVec x - 0) < euclideanNorm (M⁻¹.mulVec x) + 1
      rw [sub_zero]
      linarith
    · rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]
  have hE0 : ∀ R, 0 < R → volume (matrixEllipsoid M R) ≠ 0 := by
    intro R hR
    rw [volume_matrixEllipsoid]
    exact mul_ne_zero (ENNReal.ofReal_pos.2 hdet0).ne' (volume_ball_zero_pos hR).ne'
  have hball : ∀ R, 0 < R → matrixEllipsoid M R ⊆ ball 0 (L * R) := by
    rintro R hR _ ⟨y, hy, rfl⟩
    have hy' : euclideanNorm (y - 0) < R := hy
    rw [sub_zero] at hy'
    change euclideanNorm (Matrix.toLin' M y - 0) < L * R
    rw [sub_zero, Matrix.toLin'_apply]
    have h1 := euclideanNorm_mulVec_le M y
    have h2 : 0 ≤ euclideanNorm y := Real.sqrt_nonneg _
    have h3 : 0 ≤ Real.sqrt (∑ i, ∑ j, M i j ^ 2) := Real.sqrt_nonneg _
    nlinarith
  have hvol : ∀ R, 0 < R →
      volume.real (ball (0 : Vec d) (L * R)) ≤ κ * volume.real (matrixEllipsoid M R) := by
    intro R hR
    apply le_of_eq
    simp only [measureReal_def, volume_matrixEllipsoid, volume_ball_zero_mul hL,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ L ^ d), hκdef]
    field_simp
  have hu : ∀ R, 0 < R → MemLp w.potential 2 (volume.restrict (ball 0 R)) := fun R hR =>
    (w.local_energy R hR).1
  have hf : ∀ R, 0 < R → ∀ o, MemLp (f o) 2 (volume.restrict (ball 0 R)) := by
    intro R hR o
    have hfin : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
      isFiniteMeasure_restrict.2 (volume_ball_zero_lt_top R).ne
    cases o with
    | none => exact memLp_const 1
    | some i =>
      have hcoord : MemLp (fun x : Vec d => x i) 2 (volume.restrict (ball 0 R)) := by
        refine MemLp.of_bound (continuous_apply i).aestronglyMeasurable R ?_
        filter_upwards [ae_restrict_mem (isOpen_ball_zero R).measurableSet] with x hx
        have hx' : euclideanNorm (x - 0) < R := hx
        rw [sub_zero] at hx'
        rw [Real.norm_eq_abs]
        exact (coordinate_abs_le_euclideanNorm x i).trans hx'.le
      exact hcoord.add (F.memLp i R hR).1
  have hstep' : ∀ R, R₁ ≤ R → ∀ coeff : Option (Fin d) → ℝ, ∃ coeff' : Option (Fin d) → ℝ,
      scalarRms volume (matrixEllipsoid M (R / 2))
          (fun x => w.potential x - ∑ o, (coeff + coeff') o * f o x) ≤
        1 / 4 * (1 + max C 0 * R ^ (-ν)) *
          scalarRms volume (matrixEllipsoid M R)
            (fun x => w.potential x - ∑ o, coeff o * f o x) := by
    intro R hR coeff
    obtain ⟨c', p', h⟩ := hone a F w R hR (coeff none) (fun i => coeff (some i))
    refine ⟨fun o => Option.elim o c' p', le_trans (le_of_eq ?_) (h.trans ?_)⟩
    · congr 1
      funext x
      rw [hsum]
      rfl
    · have e2 : (fun x => w.potential x - correctedAffineOf F.φ (coeff none)
          (fun i => coeff (some i)) x) = fun x => w.potential x - ∑ o, coeff o * f o x := by
        funext x
        rw [hsum]
      rw [e2]
      refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
      have hRpos : 0 < R := by linarith
      have : C * R ^ (-ν) ≤ max C 0 * R ^ (-ν) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hRpos.le _)
      linarith
  obtain ⟨coeff, hcoeff⟩ := ae_eq_sum_of_quarter_step (le_max_right C 0) hν hR₁ hL hκ hmono
    hcover hE0 hball hvol hu hf w.growth hstep'
  refine ⟨coeff none, fun i => coeff (some i), ?_⟩
  filter_upwards [hcoeff] with x hx
  rw [hx, hsum]

end QSH
