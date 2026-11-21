import QuantitativeStochasticHomogenization.Ch03.Sec03HigherOrderRegularityAndLiouville
import QuantitativeStochasticHomogenization.Ch03.Sec04FirstOrderCorrectors
import QuantitativeStochasticHomogenization.Ch03.Sec04.WeakGradientSub
import QuantitativeStochasticHomogenization.Ch03.Sec04.SpatialWeakLocalization
import QuantitativeStochasticHomogenization.Ch03.Sec04.UncenteredSublinearity
import QuantitativeStochasticHomogenization.Ch03.Sec04.CoordinateNormBound

/-!
# Corrected affine functions belong to `A₁`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 3.3, (3.38), and Section 3.4, Definitions 3.14–3.15: for almost every coefficient field,
every corrected affine function `p·x + ∑ᵢ pᵢ φ_{eᵢ}(x)`, built from the correctors in the
coordinate directions, is an element of the class `A₁` of whole-space `a`-harmonic functions with
subquadratic growth. This is the inclusion of the corrected affine functions in `A₁` in the
statement `dim A₁ = d + 1` of Theorem 3.8 for `k = 1`.

Also proved here: linearity of weak partial derivatives, weak gradients and weak divergences, and
the weak gradient of a linear function.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-! ## Linearity of weak derivatives -/

theorem hasWeakPartialDerivative_add {U : Set (Vec d)} {j : Fin d} {f₁ f₂ g₁ g₂ : Vec d → ℝ}
    (h₁ : HasWeakPartialDerivative U j f₁ g₁) (h₂ : HasWeakPartialDerivative U j f₂ g₂) :
    HasWeakPartialDerivative U j (fun x => f₁ x + f₂ x) (fun x => g₁ x + g₂ x) := by
  refine ⟨h₁.1.add h₂.1, h₁.2.1.add h₂.2.1, ?_⟩
  intro ψ hψ
  have hdψ := isSpatialTest_coordinateDerivative hψ j
  simp only [add_mul]
  rw [integral_add (integrableOn_mul_spatialTest h₁.1 hdψ)
      (integrableOn_mul_spatialTest h₂.1 hdψ),
    integral_add (integrableOn_mul_spatialTest h₁.2.1 hψ)
      (integrableOn_mul_spatialTest h₂.2.1 hψ), h₁.2.2 ψ hψ, h₂.2.2 ψ hψ]
  ring

theorem hasWeakPartialDerivative_const_mul {U : Set (Vec d)} {j : Fin d} {f g : Vec d → ℝ}
    (h : HasWeakPartialDerivative U j f g) (c : ℝ) :
    HasWeakPartialDerivative U j (fun x => c * f x) (fun x => c * g x) := by
  refine ⟨h.1.smul c, h.2.1.smul c, ?_⟩
  intro ψ hψ
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul, h.2.2 ψ hψ]
  ring

theorem hasWeakPartialDerivative_zero (U : Set (Vec d)) (j : Fin d) :
    HasWeakPartialDerivative U j (fun _ => 0) (fun _ => 0) := by
  refine ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, ?_⟩
  intro ψ _
  simp

theorem hasWeakPartialDerivative_finset_sum {U : Set (Vec d)} {j : Fin d} {ι : Type*}
    (s : Finset ι) {f g : ι → Vec d → ℝ}
    (h : ∀ k ∈ s, HasWeakPartialDerivative U j (f k) (g k)) :
    HasWeakPartialDerivative U j (fun x => ∑ k ∈ s, f k x) (fun x => ∑ k ∈ s, g k x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasWeakPartialDerivative_zero U j
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact hasWeakPartialDerivative_add (h k (Finset.mem_insert_self k s))
      (ih fun k' hk' => h k' (Finset.mem_insert_of_mem hk'))

theorem hasWeakGradient_add {U : Set (Vec d)} {f₁ f₂ : Vec d → ℝ} {g₁ g₂ : Vec d → Vec d}
    (h₁ : HasWeakGradient U f₁ g₁) (h₂ : HasWeakGradient U f₂ g₂) :
    HasWeakGradient U (fun x => f₁ x + f₂ x) (fun x => g₁ x + g₂ x) := fun i =>
  hasWeakPartialDerivative_add (h₁ i) (h₂ i)

theorem hasWeakGradient_finset_sum_const_mul {U : Set (Vec d)} {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) {f : ι → Vec d → ℝ} {g : ι → Vec d → Vec d}
    (h : ∀ k ∈ s, HasWeakGradient U (f k) (g k)) :
    HasWeakGradient U (fun x => ∑ k ∈ s, c k * f k x) (fun x => ∑ k ∈ s, c k • g k x) := by
  intro i
  have h' := hasWeakPartialDerivative_finset_sum (U := U) (j := i) s
    (f := fun k x => c k * f k x) (g := fun k x => c k * g k x i)
    (fun k hk => hasWeakPartialDerivative_const_mul (h k hk i) (c k))
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h'

/-- The weak gradient of the linear function `x ↦ p·x` is the constant `p`. -/
theorem hasWeakGradient_dot (p : Vec d) :
    HasWeakGradient Set.univ (fun x => dot p x) (fun _ => p) := by
  intro j
  have hcont : Continuous fun x : Vec d => dot p x := by unfold dot; fun_prop
  refine ⟨hcont.locallyIntegrable.locallyIntegrableOn _, locallyIntegrableOn_const _, ?_⟩
  intro ψ hψ
  have hL : ∀ x, HasFDerivAt (fun y : Vec d => dot p y)
      (∑ i, p i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) x := by
    intro x
    have h := HasFDerivAt.sum (u := Finset.univ)
      (fun i _ => (hasFDerivAt_apply (𝕜 := ℝ) i x).const_mul (p i))
    convert h using 1
    funext y
    simp [dot, Finset.sum_apply]
  have hderiv : ∀ x, fderiv ℝ (fun y : Vec d => dot p y) x (unitVector j) = p j := by
    intro x
    rw [(hL x).fderiv]
    simp [unitVector, Pi.single_apply]
  have hψc : Continuous ψ := hψ.1.continuous
  have hdψc : Continuous (coordinateDerivative j ψ) :=
    (isSpatialTest_coordinateDerivative hψ j).1.continuous
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (Vec d))) (f := fun y : Vec d => dot p y) (g := ψ) (v := unitVector j)
    (by
      simp only [hderiv]
      exact (hψc.integrable_of_hasCompactSupport hψ.2.1).const_mul (p j))
    (by
      exact (hcont.mul hdψc).integrable_of_hasCompactSupport
        (isSpatialTest_coordinateDerivative hψ j).2.1.mul_left)
    ((hcont.mul hψc).integrable_of_hasCompactSupport hψ.2.1.mul_left)
    (fun x _ => (hL x).differentiableAt)
    (fun x _ => hψ.1.differentiable (by simp) x)
  simp only [hderiv] at hibp
  simp only [Measure.restrict_univ, coordinateDerivative]
  exact hibp

theorem hasWeakDivergence_add {U : Set (Vec d)} {F₁ F₂ : Vec d → Vec d} {h₁ h₂ : Vec d → ℝ}
    (H₁ : HasWeakDivergence U F₁ h₁) (H₂ : HasWeakDivergence U F₂ h₂) :
    HasWeakDivergence U (fun x => F₁ x + F₂ x) (fun x => h₁ x + h₂ x) := by
  refine ⟨fun i => (H₁.1 i).add (H₂.1 i), H₁.2.1.add H₂.2.1, ?_⟩
  intro ψ hψ
  have hint : ∀ {F : Vec d → Vec d}, (∀ i, LocallyIntegrableOn (fun x => F x i) U volume) →
      IntegrableOn (fun x => dot (F x) (gradient ψ x)) U volume := by
    intro F hF
    unfold dot
    exact integrable_finsetSum _ fun i _ =>
      integrableOn_mul_spatialTest (hF i) (isSpatialTest_coordinateDerivative hψ i)
  have hsplit : (fun x => dot (F₁ x + F₂ x) (gradient ψ x)) =
      fun x => dot (F₁ x) (gradient ψ x) + dot (F₂ x) (gradient ψ x) := by
    funext x
    simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [hsplit, integral_add (hint H₁.1) (hint H₂.1), H₁.2.2 ψ hψ, H₂.2.2 ψ hψ]
  simp only [add_mul]
  rw [integral_add (integrableOn_mul_spatialTest H₁.2.1 hψ)
    (integrableOn_mul_spatialTest H₂.2.1 hψ)]
  ring

theorem hasWeakDivergence_const_smul {U : Set (Vec d)} {F : Vec d → Vec d} {h : Vec d → ℝ}
    (H : HasWeakDivergence U F h) (c : ℝ) :
    HasWeakDivergence U (fun x => c • F x) (fun x => c * h x) := by
  refine ⟨fun i => (H.1 i).smul c, H.2.1.smul c, ?_⟩
  intro ψ hψ
  have hsplit : (fun x => dot (c • F x) (gradient ψ x)) = fun x => c * dot (F x) (gradient ψ x) := by
    funext x
    simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [hsplit, integral_const_mul, H.2.2 ψ hψ]
  simp only [mul_assoc]
  rw [integral_const_mul]
  ring

theorem hasWeakDivergence_finset_sum {U : Set (Vec d)} {ι : Type*} (s : Finset ι)
    {F : ι → Vec d → Vec d} (H : ∀ k ∈ s, HasWeakDivergence U (F k) (fun _ => 0)) :
    HasWeakDivergence U (fun x => ∑ k ∈ s, F k x) (fun _ => 0) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => by simpa using (locallyIntegrableOn_zero : LocallyIntegrableOn
      (fun _ : Vec d => (0 : ℝ)) U volume), locallyIntegrableOn_zero, ?_⟩
    intro ψ _
    simp [dot]
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    have h := hasWeakDivergence_add (H k (Finset.mem_insert_self k s))
      (ih fun k' hk' => H k' (Finset.mem_insert_of_mem hk'))
    simpa only [add_zero] using h

/-! ## Corrected affine functions -/

/-- The corrected affine function `p·x + ∑ᵢ pᵢ φ_{eᵢ}(x)` of the coefficient field `a`. -/
def correctedAffine {Λ : ℝ} {P : Measure (CoefficientField d Λ)} (S : HomogenizationData P)
    (a : CoefficientField d Λ) (p : Vec d) (x : Vec d) : ℝ :=
  dot p x + ∑ i, p i * (S.corrector (unitVector i)).potential a x

/-- The gradient `p + ∑ᵢ pᵢ ∇φ_{eᵢ}(x)` of the corrected affine function. -/
def correctedAffineGrad {Λ : ℝ} {P : Measure (CoefficientField d Λ)} (S : HomogenizationData P)
    (a : CoefficientField d Λ) (p : Vec d) (x : Vec d) : Vec d :=
  p + ∑ i, p i • (S.corrector (unitVector i)).grad a x

private theorem measurableSet_ball_origin (R : ℝ) : MeasurableSet (ball (0 : Vec d) R) := by
  have hU : IsOpen (ball (0 : Vec d) R) := by
    unfold ball euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const
  exact hU.measurableSet

private theorem volume_ball_origin_lt_top (R : ℝ) : volume (ball (0 : Vec d) R) < ⊤ := by
  have hsub : ball (0 : Vec d) R ⊆ Set.pi Set.univ (fun _ => Set.Icc (-|R|) |R|) := by
    intro x hx i _
    have h1 := coordinate_abs_le_euclideanNorm x i
    have h2 : euclideanNorm x < R := by simpa [ball] using hx
    constructor <;> [linarith [abs_le.mp (h1.trans (h2.le.trans (le_abs_self R)))]; linarith
      [abs_le.mp (h1.trans (h2.le.trans (le_abs_self R)))]]
  calc volume (ball (0 : Vec d) R) ≤ volume (Set.pi Set.univ (fun _ : Fin d => Set.Icc (-|R|) |R|)) :=
        measure_mono hsub
    _ < ⊤ := (isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top

private instance isFiniteMeasure_restrict_ball_origin (R : ℝ) :
    IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
  isFiniteMeasure_restrict.mpr (volume_ball_origin_lt_top R).ne

private theorem abs_dot_le_of_mem_ball {p x : Vec d} {R : ℝ} (hx : x ∈ ball (0 : Vec d) R) :
    |dot p x| ≤ (∑ i, |p i|) * R := by
  have h2 : euclideanNorm x < R := by simpa [ball] using hx
  unfold dot
  calc |∑ i, p i * x i| ≤ ∑ i, |p i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |p i| * R := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          ((coordinate_abs_le_euclideanNorm x i).trans h2.le) (abs_nonneg _)
    _ = (∑ i, |p i|) * R := by rw [Finset.sum_mul]

private theorem euclideanNorm_le_card_mul_norm (v : Vec d) : euclideanNorm v ≤ d * ‖v‖ := by
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

private theorem sq_add_sum_le (u : ℝ) (t : Fin d → ℝ) :
    (u + ∑ i, t i) ^ 2 ≤ 2 * (d + 1) * (u ^ 2 + ∑ i, t i ^ 2) := by
  have h1 : (u + ∑ i, t i) ^ 2 ≤ 2 * u ^ 2 + 2 * (∑ i, t i) ^ 2 := by
    nlinarith [sq_nonneg (u - ∑ i, t i)]
  have h2 : (∑ i, t i) ^ 2 ≤ (d : ℝ) * ∑ i, t i ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := t)
    simpa using this
  have h3 : 0 ≤ ∑ i, t i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith [sq_nonneg u]

private theorem setAverage_ball_eq (R : ℝ) (f : Vec d → ℝ) :
    ⨍ x in ball (0 : Vec d) R, f x = (volume.real (ball (0 : Vec d) R))⁻¹ *
      ∫ x in ball (0 : Vec d) R, f x := by
  rw [setAverage_eq, smul_eq_mul]

/-- Growth of a corrected affine function from the uncentered sublinearity of its correctors. -/
private theorem correctedAffine_growth_aux (p : Vec d) (φ : Fin d → Vec d → ℝ) (f : Vec d → ℝ)
    (hf : ∀ x, f x = dot p x + ∑ i, p i * φ i x)
    (hmem : ∀ i R, 0 < R → MemLp (φ i) 2 (volume.restrict (ball 0 R)))
    (hsub : ∀ i, Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R, φ i x ^ 2))
      atTop (𝓝 0)) :
    Tendsto (fun R : ℝ => R ^ (-2 : ℤ) * Real.sqrt (⨍ x in ball 0 R, |f x| ^ 2)) atTop (𝓝 0) := by
  have hA0 : 0 ≤ ∑ i, |p i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hC₀0 : (0 : ℝ) ≤ 2 * (d + 1) := by positivity
  have h0 : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h1 := ((h0.pow 2).const_mul ((∑ i, |p i|) ^ 2)).add
    (tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun i _ =>
      ((h0.mul (hsub i)).pow 2).const_mul (p i ^ 2))
  have h2 := (h1.const_mul (2 * ((d : ℝ) + 1))).sqrt
  have hlim : Real.sqrt (2 * ((d : ℝ) + 1) * ((∑ i, |p i|) ^ 2 * (0 : ℝ) ^ 2 +
      ∑ i : Fin d, p i ^ 2 * ((0 : ℝ) * 0) ^ 2)) = 0 := by simp
  rw [hlim] at h2
  refine squeeze_zero' ?_ ?_ h2
  · filter_upwards [eventually_gt_atTop 0] with R hR
    exact mul_nonneg (zpow_nonneg hR.le _) (Real.sqrt_nonneg _)
  filter_upwards [eventually_gt_atTop 0] with R hR
  have hvol := ball_volume_pos_finite d R hR
  have hint : ∀ i, Integrable (fun x => φ i x ^ 2) (volume.restrict (ball 0 R)) := fun i =>
    (hmem i R hR).integrable_sq
  have hsq : ∀ i, Integrable (fun x => (p i * φ i x) ^ 2) (volume.restrict (ball 0 R)) :=
    fun i => ((hint i).const_mul (p i ^ 2)).congr (Eventually.of_forall fun x => by ring)
  have hupper : Integrable
      (fun x => 2 * ((d : ℝ) + 1) * (((∑ i, |p i|) * R) ^ 2 + ∑ i, (p i * φ i x) ^ 2))
      (volume.restrict (ball 0 R)) :=
    ((integrable_const _).add (integrable_finsetSum _ fun i _ => hsq i)).const_mul _
  have hpt : ∀ x ∈ ball (0 : Vec d) R, |f x| ^ 2 ≤
      2 * ((d : ℝ) + 1) * (((∑ i, |p i|) * R) ^ 2 + ∑ i, (p i * φ i x) ^ 2) := by
    intro x hx
    rw [sq_abs, hf x]
    have hdot : (dot p x) ^ 2 ≤ ((∑ i, |p i|) * R) ^ 2 := by
      have h := abs_dot_le_of_mem_ball (p := p) hx
      calc (dot p x) ^ 2 = |dot p x| ^ 2 := (sq_abs _).symm
        _ ≤ ((∑ i, |p i|) * R) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    calc (dot p x + ∑ i, p i * φ i x) ^ 2
        ≤ 2 * ((d : ℝ) + 1) * ((dot p x) ^ 2 + ∑ i, (p i * φ i x) ^ 2) :=
          sq_add_sum_le (dot p x) (fun i => p i * φ i x)
      _ ≤ 2 * ((d : ℝ) + 1) * (((∑ i, |p i|) * R) ^ 2 + ∑ i, (p i * φ i x) ^ 2) := by
          gcongr
  have hmono : ∫ x in ball (0 : Vec d) R, |f x| ^ 2 ≤
      ∫ x in ball (0 : Vec d) R,
        2 * ((d : ℝ) + 1) * (((∑ i, |p i|) * R) ^ 2 + ∑ i, (p i * φ i x) ^ 2) :=
    integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hupper
      ((ae_restrict_iff' (measurableSet_ball_origin R)).mpr (Eventually.of_forall hpt))
  have hterm : ∀ i, ∫ x in ball (0 : Vec d) R, (p i * φ i x) ^ 2 =
      p i ^ 2 * ∫ x in ball (0 : Vec d) R, φ i x ^ 2 := fun i => by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  have hcalc : ∫ x in ball (0 : Vec d) R,
      2 * ((d : ℝ) + 1) * (((∑ i, |p i|) * R) ^ 2 + ∑ i, (p i * φ i x) ^ 2) =
      2 * ((d : ℝ) + 1) * (volume.real (ball (0 : Vec d) R) * ((∑ i, |p i|) * R) ^ 2 +
        ∑ i, p i ^ 2 * ∫ x in ball (0 : Vec d) R, φ i x ^ 2) := by
    rw [integral_const_mul, integral_add (integrable_const _)
      (integrable_finsetSum _ fun i _ => hsq i), setIntegral_const,
      integral_finsetSum _ fun i _ => hsq i, smul_eq_mul]
    simp only [hterm]
  have hV0 : volume.real (ball (0 : Vec d) R) ≠ 0 := hvol.ne'
  have havg : ⨍ x in ball (0 : Vec d) R, |f x| ^ 2 ≤
      2 * ((d : ℝ) + 1) * (((∑ i, |p i|) * R) ^ 2 +
        ∑ i, p i ^ 2 * ⨍ x in ball (0 : Vec d) R, φ i x ^ 2) := by
    simp only [setAverage_ball_eq]
    have hsumV : (volume.real (ball (0 : Vec d) R))⁻¹ *
        ∑ i, p i ^ 2 * ∫ x in ball (0 : Vec d) R, φ i x ^ 2 =
        ∑ i, p i ^ 2 * ((volume.real (ball (0 : Vec d) R))⁻¹ *
          ∫ x in ball (0 : Vec d) R, φ i x ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    calc (volume.real (ball (0 : Vec d) R))⁻¹ * ∫ x in ball (0 : Vec d) R, |f x| ^ 2
        ≤ (volume.real (ball (0 : Vec d) R))⁻¹ * ∫ x in ball (0 : Vec d) R,
          2 * ((d : ℝ) + 1) * (((∑ i, |p i|) * R) ^ 2 + ∑ i, (p i * φ i x) ^ 2) :=
          mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr hvol.le)
      _ = 2 * ((d : ℝ) + 1) * (((∑ i, |p i|) * R) ^ 2 *
            ((volume.real (ball (0 : Vec d) R))⁻¹ * volume.real (ball (0 : Vec d) R)) +
          (volume.real (ball (0 : Vec d) R))⁻¹ *
            ∑ i, p i ^ 2 * ∫ x in ball (0 : Vec d) R, φ i x ^ 2) := by
          rw [hcalc]
          ring
      _ = _ := by rw [inv_mul_cancel₀ hV0, mul_one, hsumV]
  have hX : 0 ≤ ⨍ x in ball (0 : Vec d) R, |f x| ^ 2 := by
    rw [setAverage_ball_eq]
    exact mul_nonneg (inv_nonneg.mpr hvol.le) (integral_nonneg fun x => sq_nonneg _)
  have hY : ∀ i, 0 ≤ ⨍ x in ball (0 : Vec d) R, φ i x ^ 2 := fun i => by
    rw [setAverage_ball_eq]
    exact mul_nonneg (inv_nonneg.mpr hvol.le) (integral_nonneg fun x => sq_nonneg _)
  have hz : R ^ (-2 : ℤ) = Real.sqrt (R⁻¹ ^ 4) := by
    rw [show R⁻¹ ^ 4 = (R⁻¹ ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity), zpow_neg,
      zpow_ofNat, inv_pow]
  show R ^ (-2 : ℤ) * Real.sqrt (⨍ x in ball (0 : Vec d) R, |f x| ^ 2) ≤
    Real.sqrt (2 * ((d : ℝ) + 1) * ((∑ i, |p i|) ^ 2 * R⁻¹ ^ 2 +
      ∑ i, p i ^ 2 * (R⁻¹ * (R⁻¹ * Real.sqrt (⨍ x in ball (0 : Vec d) R, φ i x ^ 2))) ^ 2))
  rw [hz, ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  have hterm2 : ∀ i, p i ^ 2 * (R⁻¹ * (R⁻¹ * Real.sqrt (⨍ x in ball (0 : Vec d) R, φ i x ^ 2))) ^ 2
      = R⁻¹ ^ 4 * (p i ^ 2 * ⨍ x in ball (0 : Vec d) R, φ i x ^ 2) := fun i => by
    rw [mul_pow, mul_pow, Real.sq_sqrt (hY i)]
    ring
  simp only [hterm2]
  rw [← Finset.mul_sum]
  have hR2 : (∑ i, |p i|) ^ 2 * R⁻¹ ^ 2 = R⁻¹ ^ 4 * ((∑ i, |p i|) * R) ^ 2 := by
    field_simp
  rw [hR2]
  calc R⁻¹ ^ 4 * ⨍ x in ball (0 : Vec d) R, |f x| ^ 2
      ≤ R⁻¹ ^ 4 * (2 * ((d : ℝ) + 1) * (((∑ i, |p i|) * R) ^ 2 +
        ∑ i, p i ^ 2 * ⨍ x in ball (0 : Vec d) R, φ i x ^ 2)) :=
        mul_le_mul_of_nonneg_left havg (by positivity)
    _ = _ := by ring

/-- **Corrected affine functions belong to `A₁`.** For almost every coefficient field, for
every slope `p`, the corrected affine function `p·x + ∑ᵢ pᵢ φ_{eᵢ}` with gradient
`p + ∑ᵢ pᵢ ∇φ_{eᵢ}` is an element of `A₁`, (3.38). -/
theorem ae_exists_harmonicA1_correctedAffine {Λ : ℝ} {P : Measure (CoefficientField d Λ)}
    (S : HomogenizationData P) :
    ∀ᵐ a ∂P, ∀ p : Vec d, ∃ w : HarmonicA1 a,
      w.potential = correctedAffine S a p ∧ w.grad = correctedAffineGrad S a p := by
  have hall : ∀ᵐ a ∂P, ∀ i : Fin d,
      HasWeakGradient Set.univ ((S.corrector (unitVector i)).potential a)
        ((S.corrector (unitVector i)).grad a) ∧
      (∀ R : ℝ, 0 < R →
        MemLp ((S.corrector (unitVector i)).potential a) 2 (volume.restrict (ball 0 R)) ∧
        MemLp ((S.corrector (unitVector i)).grad a) 2 (volume.restrict (ball 0 R))) ∧
      HasWeakDivergence Set.univ
        (fun x => (a x).mulVec (unitVector i + (S.corrector (unitVector i)).grad a x))
        (fun _ => 0) ∧
      Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R,
        ((S.corrector (unitVector i)).potential a x -
          ⨍ y in ball 0 R, (S.corrector (unitVector i)).potential a y ∂volume) ^ 2 ∂volume))
        atTop (𝓝 0) := by
    rw [ae_all_iff]
    intro i
    filter_upwards [(S.corrector (unitVector i)).weak_gradient,
      (S.corrector (unitVector i)).locally_square_integrable,
      (S.corrector (unitVector i)).harmonic, (S.corrector (unitVector i)).sublinear]
      with a h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  filter_upwards [hall] with a ha p
  have hwg : HasWeakGradient Set.univ (correctedAffine S a p) (correctedAffineGrad S a p) :=
    hasWeakGradient_add (hasWeakGradient_dot p)
      (hasWeakGradient_finset_sum_const_mul Finset.univ p
        (f := fun i => (S.corrector (unitVector i)).potential a)
        (g := fun i => (S.corrector (unitVector i)).grad a) fun i _ => (ha i).1)
  have hpot : ∀ R : ℝ, 0 < R →
      MemLp (correctedAffine S a p) 2 (volume.restrict (ball 0 R)) := by
    intro R hR
    have hcont : Continuous fun x : Vec d => dot p x := by unfold dot; fun_prop
    have hlin : MemLp (fun x : Vec d => dot p x) 2 (volume.restrict (ball 0 R)) := by
      refine MemLp.of_bound hcont.aestronglyMeasurable ((∑ i, |p i|) * R) ?_
      filter_upwards [ae_restrict_mem (measurableSet_ball_origin R)] with x hx
      rw [Real.norm_eq_abs]
      exact abs_dot_le_of_mem_ball hx
    have hsum : MemLp (fun x => ∑ i, p i * (S.corrector (unitVector i)).potential a x) 2
        (volume.restrict (ball 0 R)) :=
      memLp_finsetSum _ fun i _ => ((ha i).2.1 R hR).1.const_mul (p i)
    exact hlin.add hsum
  have hgrad : ∀ R : ℝ, 0 < R → MemLp (fun x => euclideanNorm (correctedAffineGrad S a p x)) 2
      (volume.restrict (ball 0 R)) := by
    intro R hR
    have hG : MemLp (correctedAffineGrad S a p) 2 (volume.restrict (ball 0 R)) :=
      (memLp_const p).add
        (memLp_finsetSum _ fun i _ => ((ha i).2.1 R hR).2.const_smul (p i))
    have hcont : Continuous fun v : Vec d => euclideanNorm v := by
      unfold euclideanNorm euclideanSq dot; fun_prop
    refine hG.norm.of_le_mul (c := (d : ℝ))
      (hcont.comp_aestronglyMeasurable hG.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    have h0 : 0 ≤ euclideanNorm (correctedAffineGrad S a p x) := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg h0, norm_norm]
    exact euclideanNorm_le_card_mul_norm _
  have hharm : HasWeakDivergence Set.univ
      (fun x => (a x).mulVec (correctedAffineGrad S a p x)) (fun _ => 0) := by
    have hsum := hasWeakDivergence_finset_sum (U := Set.univ) Finset.univ
      (F := fun i x => p i • (a x).mulVec (unitVector i + (S.corrector (unitVector i)).grad a x))
      (fun i _ => by simpa only [mul_zero] using hasWeakDivergence_const_smul (ha i).2.2.1 (p i))
    have hp : (∑ i, p i • unitVector i : Vec d) = p := by
      funext k
      simp [unitVector, Pi.single_apply]
    have hfun : (fun x => (a x).mulVec (correctedAffineGrad S a p x)) =
        fun x => ∑ i, p i • (a x).mulVec (unitVector i + (S.corrector (unitVector i)).grad a x) := by
      funext x
      have hv : correctedAffineGrad S a p x =
          ∑ i, p i • (unitVector i + (S.corrector (unitVector i)).grad a x) := by
        simp only [correctedAffineGrad, smul_add, Finset.sum_add_distrib, hp]
      rw [hv, Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul]
    rw [hfun]
    exact hsum
  have hgrowth : Tendsto (fun R : ℝ => R ^ (-2 : ℤ) *
      Real.sqrt (⨍ x in ball 0 R, |correctedAffine S a p x| ^ 2)) atTop (𝓝 0) :=
    correctedAffine_growth_aux p (fun i => (S.corrector (unitVector i)).potential a)
      (correctedAffine S a p) (fun x => rfl) (fun i R hR => ((ha i).2.1 R hR).1)
      fun i => sublinear_uncentered_of_centered _ (fun R hR => ((ha i).2.1 R hR).1) (ha i).2.2.2
  exact ⟨{ potential := correctedAffine S a p
           grad := correctedAffineGrad S a p
           weak_gradient := hwg
           local_energy := fun R hR => ⟨hpot R hR, hgrad R hR⟩
           harmonic := hharm
           growth := hgrowth }, rfl, rfl⟩

end QSH
