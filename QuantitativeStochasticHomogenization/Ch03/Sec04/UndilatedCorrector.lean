import QuantitativeStochasticHomogenization.Ch06.Sec01.CorrectorSublinear
import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicApproximationData

/-!
# The undilated high-contrast corrector

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 3.4, Lemma 3.16. The coefficient field `a` defines the high-contrast coefficient
`b(y) = a(2y)` of Armstrong, Kuusi and Loher, *Homogenization at a polynomial scale in high
contrast* (`toHighContrast`), whose Theorem C provides correctors `Φ_e` of `b`. Undoing the
dilation, `φ_e(x) = 2 Φ_e(x/2)` has gradient `∇Φ_e(x/2)`, and on the event of full probability of
that theorem:

* `hasWeakGradient_undilatedPotential`: `∇φ_e` is the weak gradient of `φ_e` in `ℝ^d`;
* `memLp_undilatedPotential_ball`, `memLp_undilatedGradient_ball`: both are in `L²(B_R)`;
* `hasWeakDivergence_undilated`: `-∇·a(e + ∇φ_e) = 0` weakly in `ℝ^d`;
* `tendsto_sublinear_undilatedPotential`: `r⁻¹ ‖φ_e - (φ_e)_{B_r}‖_{L̲²(B_r)} → 0`, from the
  oscillation bounds of the high-contrast correctors above the homogenization scale.
-/

open MeasureTheory Filter Set
open scoped Topology Pointwise

namespace QSH

open _root_.Homogenization hiding euclideanBall Vec Mat euclideanNorm

open _root_.Homogenization.HighContrast

variable {d : ℕ}

/-! ## Undilation -/

/-- The undilated potential `x ↦ 2 Φ(x/2)`, inverse to `dilatedPotential`. -/
noncomputable def undilatedPotential (Φ : Vec d → ℝ) (x : Vec d) : ℝ :=
  2 * Φ ((2 : ℝ)⁻¹ • x)

/-- The undilated gradient `x ↦ G(x/2)`, inverse to `dilatedGradient`. -/
noncomputable def undilatedGradient (G : Vec d → Vec d) (x : Vec d) : Vec d :=
  G ((2 : ℝ)⁻¹ • x)

theorem dilatedPotential_undilatedPotential (Φ : Vec d → ℝ) :
    dilatedPotential (undilatedPotential Φ) = Φ := by
  funext x
  simp only [dilatedPotential, undilatedPotential, inv_smul_smul₀ (two_ne_zero' ℝ)]
  ring

theorem dilatedGradient_undilatedGradient (G : Vec d → Vec d) :
    dilatedGradient (undilatedGradient G) = G := by
  funext x
  simp only [dilatedGradient, undilatedGradient, inv_smul_smul₀ (two_ne_zero' ℝ)]

theorem dilatedCorrectedAffine_undilatedPotential (e : Vec d) (Φ : Vec d → ℝ) (x : Vec d) :
    dilatedCorrectedAffine e (undilatedPotential Φ) x = vecDot e x + Φ x := by
  rw [dilatedCorrectedAffine, dilatedPotential_undilatedPotential]

theorem inv_two_smul_ball_subset (R : ℝ) :
    (2 : ℝ)⁻¹ • ball (0 : Vec d) R ⊆ ball (0 : Vec d) R := by
  rintro _ ⟨y, hy, rfl⟩
  have hy' : euclideanNorm (y - 0) < R := hy
  show euclideanNorm ((2 : ℝ)⁻¹ • y - 0) < R
  rw [sub_zero] at hy' ⊢
  rw [euclideanNorm_smul_of_zero_le _ (by norm_num)]
  have h0 : 0 ≤ euclideanNorm y := Real.sqrt_nonneg _
  linarith

theorem memLp_comp_inv_two_smul_ball {E : Type*} [NormedAddCommGroup E] {f : Vec d → E}
    {R : ℝ} (hf : MemLp f 2 (volume.restrict (ball 0 R))) :
    MemLp (fun x => f ((2 : ℝ)⁻¹ • x)) 2 (volume.restrict (ball 0 R)) :=
  MemLp.comp_smul_restrict (inv_ne_zero two_ne_zero) (measurableSet_ball_zero R)
    (hf.mono_measure (Measure.restrict_mono (inv_two_smul_ball_subset R) le_rfl))

/-- A function square integrable on every centered ball is locally integrable. -/
theorem locallyIntegrable_of_forall_memLp_ball {E : Type*} [NormedAddCommGroup E] {f : Vec d → E}
    (hf : ∀ R : ℝ, 0 < R → MemLp f 2 (volume.restrict (ball 0 R))) :
    LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨R, hR, hkR⟩ := exists_euclideanBall_superset_of_isCompact hk
  rw [← ball_zero_eq_euclideanBall hR] at hkR
  have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
    isFiniteMeasure_restrict.mpr (volume_ball_ne_top hR)
  exact IntegrableOn.mono_set ((hf R hR).integrable one_le_two) hkR

/-- The flux `a G` of a field `G` square integrable on balls is locally integrable. -/
theorem locallyIntegrable_flux_of_memLp_ball {Λ : ℝ} (a : CoefficientField d Λ)
    {G : Vec d → Vec d} (hG : ∀ R : ℝ, 0 < R → MemLp G 2 (volume.restrict (ball 0 R)))
    (k : Fin d) : LocallyIntegrable (fun x => ((a x).mulVec (G x)) k) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR, hKR⟩ := exists_euclideanBall_superset_of_isCompact hK
  rw [← ball_zero_eq_euclideanBall hR] at hKR
  have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
    isFiniteMeasure_restrict.mpr (volume_ball_ne_top hR)
  have hint : ∀ j, Integrable (fun x => G x j) (volume.restrict (ball 0 R)) := fun j =>
    (memLp_pi_iff.mp (hG R hR) j).integrable one_le_two
  refine IntegrableOn.mono_set ?_ hKR
  simp only [Matrix.mulVec, dotProduct]
  refine integrable_finsetSum _ fun j _ => ?_
  exact (hint j).bdd_mul (c := Λ) (a.locally_integrable k j).aestronglyMeasurable.restrict
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact abs_coefficient_entry_le a x k j)

/-! ## The undilated corrector on the event of full probability -/

section Package

variable {K : ℝ} {hK : 1 ≤ K} {P : Measure (CoefficientField d K)} {κ C : ℝ}

theorem memLp_Phi_euclideanBall [NeZero d] (pk : HighContrastCorrectorPackage hK P κ C)
    {b : CoeffSpace d} (hb : b ∈ pk.Ωend)
    (hbell : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 K (b.1 x)) (e : Vec d)
    {R : ℝ} (hR : 0 < R) : MemLp (pk.Phi e b) 2 (volume.restrict (euclideanBall d R)) := by
  have hv := ((pk.wholeSpaceSolution hb hbell e).locL2 R hR).1
  have hl := EllipticWholeSpaceSolution.memLp_euclideanBall_vecDot (d := d) e hR.le
  exact (hv.sub hl).ae_eq (Eventually.of_forall fun x => by
    simp [HighContrastCorrectorPackage.wholeSpaceSolution])

theorem memLp_gradPhi_euclideanBall [NeZero d] (pk : HighContrastCorrectorPackage hK P κ C)
    {b : CoeffSpace d} (hb : b ∈ pk.Ωend)
    (hbell : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 K (b.1 x)) (e : Vec d)
    {R : ℝ} (hR : 0 < R) : MemLp (pk.gradPhi e b) 2 (volume.restrict (euclideanBall d R)) := by
  have : IsFiniteMeasure (volume.restrict (euclideanBall d R)) :=
    isFiniteMeasure_restrict.mpr (volume_euclideanBall_ne_top' R)
  refine memLp_pi_iff.mpr fun i => ?_
  have hD := ((pk.wholeSpaceSolution hb hbell e).locL2 R hR).2 i
  exact (hD.sub (memLp_const (e i))).ae_eq (Eventually.of_forall fun x => by
    simp [HighContrastCorrectorPackage.wholeSpaceSolution])

theorem memLp_undilatedPotential_ball [NeZero d] (pk : HighContrastCorrectorPackage hK P κ C)
    {b : CoeffSpace d} (hb : b ∈ pk.Ωend)
    (hbell : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 K (b.1 x)) (e : Vec d)
    {R : ℝ} (hR : 0 < R) :
    MemLp (undilatedPotential (pk.Phi e b)) 2 (volume.restrict (ball 0 R)) := by
  have h := memLp_Phi_euclideanBall pk hb hbell e hR
  rw [← ball_zero_eq_euclideanBall hR] at h
  exact (memLp_comp_inv_two_smul_ball h).const_mul 2

theorem memLp_undilatedGradient_ball [NeZero d] (pk : HighContrastCorrectorPackage hK P κ C)
    {b : CoeffSpace d} (hb : b ∈ pk.Ωend)
    (hbell : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 K (b.1 x)) (e : Vec d)
    {R : ℝ} (hR : 0 < R) :
    MemLp (undilatedGradient (pk.gradPhi e b)) 2 (volume.restrict (ball 0 R)) := by
  have h := memLp_gradPhi_euclideanBall pk hb hbell e hR
  rw [← ball_zero_eq_euclideanBall hR] at h
  exact memLp_comp_inv_two_smul_ball h

/-- A weak gradient in the sense of the high-contrast theory, with locally integrable function
and gradient, is a weak gradient in the sense of (0.8). -/
theorem hasWeakGradient_of_hasWeakGradientOn_univ {u : Vec d → ℝ} {g : Vec d → Vec d}
    (h : _root_.Homogenization.HasWeakGradientOn Set.univ u g)
    (hu : LocallyIntegrable u volume) (hg : ∀ i, LocallyIntegrable (fun x => g x i) volume) :
    HasWeakGradient Set.univ u g := by
  intro i
  refine ⟨hu.locallyIntegrableOn _, (hg i).locallyIntegrableOn _, fun φ hφ => ?_⟩
  simpa only [coordinateDerivative, unitVector, _root_.Homogenization.basisVec] using
      h i φ hφ.1 hφ.2.1 hφ.2.2

theorem hasWeakGradient_undilatedPotential [NeZero d] (pk : HighContrastCorrectorPackage hK P κ C)
    {b : CoeffSpace d} (hb : b ∈ pk.Ωend)
    (hbell : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 K (b.1 x)) (e : Vec d) :
    HasWeakGradient Set.univ (undilatedPotential (pk.Phi e b))
      (undilatedGradient (pk.gradPhi e b)) := by
  have h := HasWeakGradientOn.univ_dilate (inv_pos.mpr two_pos) (pk.equation b hb e).1
  simp only [inv_inv] at h
  exact hasWeakGradient_of_hasWeakGradientOn_univ h
    (locallyIntegrable_of_forall_memLp_ball fun R hR =>
      memLp_undilatedPotential_ball pk hb hbell e hR)
    (fun i => locallyIntegrable_of_forall_memLp_ball fun R hR =>
      memLp_pi_iff.mp (memLp_undilatedGradient_ball pk hb hbell e hR) i)

/-- **The undilated corrector equation**: if `e + G` solves the equation of the dilated
coefficient, then `-∇·a(e + G(·/2)) = 0` weakly in `ℝ^d`. -/
theorem hasWeakDivergence_undilated (hK : 1 ≤ K) (a : CoefficientField d K) (e : Vec d)
    {G : Vec d → Vec d}
    (hsol : IsWeakSolutionOn (fun x => (toHighContrast hK a).1 x) Set.univ (fun x => e + G x))
    (hG : ∀ R : ℝ, 0 < R → MemLp (undilatedGradient G) 2 (volume.restrict (ball 0 R))) :
    HasWeakDivergence Set.univ (fun x => (a x).mulVec (e + undilatedGradient G x))
      (fun _ => 0) := by
  have hG' : ∀ R : ℝ, 0 < R →
      MemLp (fun x => e + undilatedGradient G x) 2 (volume.restrict (ball 0 R)) := by
    intro R hR
    have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
      isFiniteMeasure_restrict.mpr (volume_ball_ne_top hR)
    exact (memLp_const e).add (hG R hR)
  refine ⟨fun k => (locallyIntegrable_flux_of_memLp_ball a hG' k).locallyIntegrableOn _,
    locallyIntegrableOn_const _, fun φ hφ => ?_⟩
  simp only [zero_mul, integral_zero, neg_zero, Measure.restrict_univ]
  set χ : Vec d → ℝ := fun y => φ ((2 : ℝ) • y)
  have hφd : Differentiable ℝ φ := hφ.1.differentiable (by simp)
  have hχ : IsLocalTest Set.univ χ :=
    ⟨hφ.1.comp (contDiff_const_smul _), hφ.2.1.comp_smul two_ne_zero, Set.subset_univ _⟩
  obtain ⟨-, hzero⟩ := hsol χ hχ
  rw [Measure.restrict_univ] at hzero
  have hgradχ : ∀ y, smoothGrad χ y = (2 : ℝ) • gradient φ ((2 : ℝ) • y) := by
    intro y
    funext i
    simp only [smoothGrad, χ, gradient, coordinateDerivative, Pi.smul_apply, smul_eq_mul]
    rw [fderiv_comp_smul_apply hφd, unitVector, ← _root_.Homogenization.basisVec]
  set f : Vec d → ℝ := fun x => dot ((a x).mulVec (e + undilatedGradient G x)) (gradient φ x)
  have hcongr : (fun y => f ((2 : ℝ) • y)) =ᵐ[volume] fun y => (2 : ℝ)⁻¹ *
      vecDot (smoothGrad χ y) (matVecMul ((toHighContrast hK a).1 y) (e + G y)) := by
    filter_upwards [toHighContrast_ae_eq hK a] with y hy
    simp only [f, hgradχ, hy, undilatedGradient, inv_smul_smul₀ (two_ne_zero' ℝ)]
    simp only [dot, vecDot, matVecMul, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hscale := Measure.integral_comp_smul (volume : Measure (Vec d)) f (2 : ℝ)
  rw [Module.finrank_fin_fun, integral_congr_ae hcongr, integral_const_mul, hzero,
    mul_zero] at hscale
  have h2 : |((2 : ℝ) ^ d)⁻¹| ≠ 0 := by positivity
  rw [smul_eq_mul] at hscale
  exact (mul_eq_zero.mp hscale.symm).resolve_left h2

/-! ## Sublinearity -/

/-- **Oscillation of the undilated corrector above the homogenization scale.** -/
theorem exists_undilated_oscillation_bound (d : ℕ) (hd : 2 ≤ d) (K : ℝ) (hK : 1 ≤ K)
    {κ C₀ : ℝ} (hκ : 0 < κ) (hC₀ : 0 ≤ C₀) :
    ∃ (Cφ θ : ℝ) (n₁ : ℕ), 0 ≤ Cφ ∧ 0 < θ ∧ θ ≤ 1 ∧ ∀ (P : Measure (CoefficientField d K))
      (pk : HighContrastCorrectorPackage hK P κ C₀) {b : CoeffSpace d}, b ∈ pk.Ωend →
      (∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 K (b.1 x)) → ∀ (e : Vec d)
      (r : ℝ), (3 : ℝ) ^ (n₁ + 1) * pk.X b ≤ r →
        Real.sqrt (⨍ x in ball 0 r, |undilatedPotential (pk.Phi e b) x -
            ⨍ y in ball 0 r, undilatedPotential (pk.Phi e b) y| ^ 2) ≤
          Cφ * Real.sqrt (vecNormSq e) * r ^ (1 - θ) * ((3 : ℝ) ^ (n₁ + 1) * pk.X b) ^ θ := by
  have hd0 : NeZero d := ⟨by omega⟩
  obtain ⟨A, θ, n₁, hA, hθ, hq⟩ := exists_highContrast_quantitative_bounds d K hK hκ hC₀
  have hV := ballCubeRatio_nonneg d
  set V := ballCubeRatio d with hVdef
  refine ⟨2 * Real.sqrt V * (3 * A), min θ 1, n₁, by positivity, lt_min hθ one_pos,
    min_le_right _ _, ?_⟩
  intro P pk b hb hbell e r hBXr
  have hXb1 : 1 ≤ pk.X b := pk.one_le_X b
  have h3n : (1 : ℝ) ≤ (3 : ℝ) ^ (n₁ + 1) := one_le_pow₀ (by norm_num)
  have hBX1 : 1 ≤ (3 : ℝ) ^ (n₁ + 1) * pk.X b := one_le_mul_of_one_le_of_one_le h3n hXb1
  have hr0 : 0 < r := by linarith
  set w := Real.sqrt (vecNormSq e) with hw
  obtain ⟨N, hN1, hN2, -, hO⟩ := exists_cube_le_of_scale_bounds (d := d) hA hθ
    (Real.sqrt_nonneg (vecNormSq e)) hXb1
    (E := fun N => cubeAverage (originCube d (N : ℤ))
      (fun x => vecNormSq ((pk.wholeSpaceSolution hb hbell e).correctorGrad e x)))
    (O := fun N => cubeBesovOscillation (originCube d (N : ℤ)) 2
      ((pk.wholeSpaceSolution hb hbell e).corrector e))
    (fun n₀ L hX hn => hq P pk hb hbell e n₀ L hX hn) hBXr
  set ρ := r / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hr2 : 2 * ρ = r := by
    rw [hρ]
    ring
  have hρN : ρ ≤ (3 : ℝ) ^ N / 2 := by
    rw [hρ]
    linarith
  have hratio : ((3 : ℝ) ^ N) ^ d / volume.real (ball (0 : Vec d) ρ) ≤ V :=
    cube_div_ball_le hρ0 (by rw [hρ]; linarith)
  set Ob := 3 * A * w * r ^ (1 - min θ 1) * ((3 : ℝ) ^ (n₁ + 1) * pk.X b) ^ min θ 1 with hOb
  have hOb0 : 0 ≤ Ob := by positivity
  have hO0 : 0 ≤ cubeBesovOscillation (originCube d (N : ℤ)) 2
      ((pk.wholeSpaceSolution hb hbell e).corrector e) := ENNReal.toReal_nonneg
  have hc' : dilatedCorrectedAffine e (undilatedPotential (pk.Phi e b)) =ᵐ[volume]
      fun y => vecDot e y + (pk.wholeSpaceSolution hb hbell e).corrector e y + 0 :=
    Eventually.of_forall fun y => by
      simp only [dilatedCorrectedAffine_undilatedPotential,
        pk.wholeSpaceSolution_corrector hb hbell e, add_zero]
  have hu : MemLp (undilatedPotential (pk.Phi e b)) 2 (volume.restrict (ball 0 (2 * ρ))) :=
    memLp_undilatedPotential_ball pk hb hbell e (by positivity)
  have hOball : ⨍ x in ball 0 r, |undilatedPotential (pk.Phi e b) x -
      (⨍ y in ball 0 r, undilatedPotential (pk.Phi e b) y)| ^ 2 ≤
        (2 * Real.sqrt V * Ob) ^ 2 := by
    have h := setAverage_ball_two_mul_sq_le hρ0 e hu hc'
      (cubeAverage (originCube d (N : ℤ)) ((pk.wholeSpaceSolution hb hbell e).corrector e))
    rw [hr2] at h
    refine h.trans ?_
    calc 4 * ⨍ y in ball 0 ρ, ((pk.wholeSpaceSolution hb hbell e).corrector e y -
          cubeAverage (originCube d (N : ℤ)) ((pk.wholeSpaceSolution hb hbell e).corrector e)) ^ 2
        ≤ 4 * (((3 : ℝ) ^ N) ^ d / volume.real (ball (0 : Vec d) ρ) *
            cubeBesovOscillation (originCube d (N : ℤ)) 2
              ((pk.wholeSpaceSolution hb hbell e).corrector e) ^ 2) := by
          gcongr
          exact (pk.wholeSpaceSolution hb hbell e).setAverage_ball_sq_le e hρ0 hρN
      _ ≤ 4 * (V * Ob ^ 2) := by gcongr
      _ = (2 * Real.sqrt V * Ob) ^ 2 := by
          rw [show (2 * Real.sqrt V * Ob) ^ 2 = 4 * (Real.sqrt V ^ 2 * Ob ^ 2) by ring,
            Real.sq_sqrt hV]
  calc Real.sqrt (⨍ x in ball 0 r, |undilatedPotential (pk.Phi e b) x -
        (⨍ y in ball 0 r, undilatedPotential (pk.Phi e b) y)| ^ 2)
      ≤ Real.sqrt ((2 * Real.sqrt V * Ob) ^ 2) := Real.sqrt_le_sqrt hOball
    _ = 2 * Real.sqrt V * (3 * A) * w * r ^ (1 - min θ 1) *
          ((3 : ℝ) ^ (n₁ + 1) * pk.X b) ^ min θ 1 := by
        rw [Real.sqrt_sq (by positivity), hOb]
        ring

/-- **Sublinearity of the undilated corrector.** -/
theorem tendsto_sublinear_undilatedPotential (hd : 2 ≤ d) (hκ : 0 < κ) (hC : 0 ≤ C)
    (pk : HighContrastCorrectorPackage hK P κ C) {b : CoeffSpace d} (hb : b ∈ pk.Ωend)
    (hbell : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 K (b.1 x)) (e : Vec d) :
    Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R,
      (undilatedPotential (pk.Phi e b) x -
        ⨍ y in ball 0 R, undilatedPotential (pk.Phi e b) y ∂volume) ^ 2 ∂volume))
      atTop (𝓝 0) := by
  obtain ⟨Cφ, θ, n₁, hCφ, hθ, -, hbound⟩ := exists_undilated_oscillation_bound d hd K hK hκ hC
  set B := (3 : ℝ) ^ (n₁ + 1) * pk.X b
  have hB : 0 < B := by
    have := pk.one_le_X b
    positivity
  have hlim : Tendsto (fun R : ℝ => Cφ * Real.sqrt (vecNormSq e) * B ^ θ * R ^ (-θ)) atTop
      (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop hθ).const_mul (Cφ * Real.sqrt (vecNormSq e) * B ^ θ)
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact mul_nonneg (inv_nonneg.mpr hR.le) (Real.sqrt_nonneg _)
  · filter_upwards [eventually_ge_atTop B] with R hR
    have hR0 : 0 < R := lt_of_lt_of_le hB hR
    have h := hbound P pk hb hbell e R hR
    simp_rw [sq_abs] at h
    calc R⁻¹ * Real.sqrt (⨍ x in ball 0 R, (undilatedPotential (pk.Phi e b) x -
          ⨍ y in ball 0 R, undilatedPotential (pk.Phi e b) y) ^ 2)
        ≤ R⁻¹ * (Cφ * Real.sqrt (vecNormSq e) * R ^ (1 - θ) * B ^ θ) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hR0.le)
      _ = (R⁻¹ * R) * (Cφ * Real.sqrt (vecNormSq e) * B ^ θ * R ^ (-θ)) := by
          have h1 : R ^ (1 - θ) = R * R ^ (-θ) := by
            rw [sub_eq_add_neg, Real.rpow_add hR0, Real.rpow_one]
          rw [h1]
          ring
      _ = Cφ * Real.sqrt (vecNormSq e) * B ^ θ * R ^ (-θ) := by
          rw [inv_mul_cancel₀ hR0.ne', one_mul]

end Package

end QSH
