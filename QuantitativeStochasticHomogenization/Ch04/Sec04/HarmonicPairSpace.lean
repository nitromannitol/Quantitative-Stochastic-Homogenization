import QuantitativeStochasticHomogenization.Ch04.Sec04LocalizationEstimates
import QuantitativeStochasticHomogenization.Ch04.Sec04.NestedConvexSets

/-!
# The Hilbert space of potential–gradient pairs on a ball

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.4, p. 155: the class `A(B_T(z))` of `a`-harmonic functions in `H¹(B_T(z))` and its
subclass `K` of functions with normalized gradient `L²` norm at most `C`.

A pair `(u, (g_i)_i)` of `L²(B_T(z))` functions is a *harmonic pair* for `a` if `g` is the weak
gradient of `u` in `B_T(z)` and `∇·(a g) = 0` weakly in `B_T(z)`. Both conditions are the vanishing
of continuous linear functionals (inner products with test functions, their derivatives, and the
coefficients times the derivatives), so the harmonic pairs form a closed subspace, and the pairs
with bounded gradient energy form a closed convex set. A harmonic pair is the same thing as an
element of `A(B_T(z))` up to the choice of representatives.
-/

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace QSH

variable {d : ℕ}

/-! ## Euclidean balls -/

theorem zero_le_euclideanSq (x : Vec d) : 0 ≤ euclideanSq x := by
  show 0 ≤ ∑ i, x i * x i
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

theorem zero_le_euclideanNorm (x : Vec d) : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _

theorem sq_euclideanNorm (x : Vec d) : euclideanNorm x ^ 2 = euclideanSq x :=
  Real.sq_sqrt (zero_le_euclideanSq x)

theorem continuous_euclideanSq : Continuous (euclideanSq : Vec d → ℝ) := by
  show Continuous fun x : Vec d => ∑ i, x i * x i
  fun_prop

theorem euclideanNorm_continuous : Continuous (euclideanNorm : Vec d → ℝ) :=
  Real.continuous_sqrt.comp continuous_euclideanSq

theorem abs_coord_le_euclideanNorm (x : Vec d) (i : Fin d) : |x i| ≤ euclideanNorm x := by
  refine Real.abs_le_sqrt ?_
  rw [sq]
  exact Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (x j))
    (Finset.mem_univ i)

/-- The Euclidean norm is the norm of `EuclideanSpace`. -/
theorem euclideanNorm_eq_euclideanSpace_norm (x : Vec d) :
    euclideanNorm x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold euclideanNorm euclideanSq dot
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Real.norm_eq_abs, sq]

theorem euclideanNorm_add_le_add (x y : Vec d) :
    euclideanNorm (x + y) ≤ euclideanNorm x + euclideanNorm y := by
  rw [euclideanNorm_eq_euclideanSpace_norm, euclideanNorm_eq_euclideanSpace_norm, euclideanNorm_eq_euclideanSpace_norm, WithLp.toLp_add]
  exact norm_add_le _ _

theorem euclideanNorm_sub_le_sub_add (x y z : Vec d) :
    euclideanNorm (x - y) ≤ euclideanNorm (x - z) + euclideanNorm (z - y) := by
  have h := euclideanNorm_add_le_add (x - z) (z - y)
  rwa [sub_add_sub_cancel] at h

theorem euclideanNorm_sub_comm (x y : Vec d) : euclideanNorm (x - y) = euclideanNorm (y - x) := by
  rw [euclideanNorm_eq_euclideanSpace_norm, euclideanNorm_eq_euclideanSpace_norm, ← norm_neg, ← WithLp.toLp_neg, neg_sub]

theorem isOpen_ball (z : Vec d) (T : ℝ) : IsOpen (ball z T) :=
  isOpen_lt (euclideanNorm_continuous.comp (continuous_id.sub continuous_const)) continuous_const

theorem measurableSet_ball (z : Vec d) (T : ℝ) : MeasurableSet (ball z T) :=
  (isOpen_ball z T).measurableSet

theorem ball_subset_closedBall (z : Vec d) (T : ℝ) : ball z T ⊆ Metric.closedBall z T := by
  intro y hy
  have hT : 0 ≤ T := (zero_le_euclideanNorm _).trans hy.le
  rw [Metric.mem_closedBall, dist_pi_le_iff hT]
  intro i
  rw [Real.dist_eq]
  have := abs_coord_le_euclideanNorm (y - z) i
  simp only [Pi.sub_apply] at this
  exact this.trans hy.le

theorem isBounded_ball (z : Vec d) (T : ℝ) : Bornology.IsBounded (ball z T) :=
  Metric.isBounded_closedBall.subset (ball_subset_closedBall z T)

theorem volume_ball_lt_top (z : Vec d) (T : ℝ) : volume (ball z T) < ∞ :=
  (measure_mono (ball_subset_closedBall z T)).trans_lt measure_closedBall_lt_top

theorem mem_ball_self (z : Vec d) {T : ℝ} (hT : 0 < T) : z ∈ ball z T := by
  simp [ball, euclideanNorm, euclideanSq, dot, hT]

theorem volume_ball_pos (z : Vec d) {T : ℝ} (hT : 0 < T) : 0 < volume (ball z T) :=
  (isOpen_ball z T).measure_pos volume ⟨z, mem_ball_self z hT⟩

theorem volume_real_ball_pos (z : Vec d) {T : ℝ} (hT : 0 < T) : 0 < volume.real (ball z T) :=
  ENNReal.toReal_pos (volume_ball_pos z hT).ne' (volume_ball_lt_top z T).ne

instance isFiniteMeasure_ballMeasure (z : Vec d) (T : ℝ) :
    IsFiniteMeasure (volume.restrict (ball z T)) :=
  isFiniteMeasure_restrict.2 (volume_ball_lt_top z T).ne

/-! ## Bounds on the coefficients -/

theorem dot_def_dotProduct (x y : Vec d) : dot x y = x ⬝ᵥ y := rfl

/-- The entries of a coefficient field are bounded by `Λ`. -/
theorem CoefficientField.abs_apply_le {Λ : ℝ} (a : CoefficientField d Λ) (x : Vec d)
    (k j : Fin d) : |a x k j| ≤ Λ := by
  set A := a.field x
  have hsymm : A j k = A k j := by
    have h := congrFun (congrFun (a.symmetric x) k) j
    simpa [Matrix.transpose_apply] using h
  have hq : ∀ u v : Vec d, dot u (A.mulVec v) = u ⬝ᵥ A.mulVec v := fun _ _ => rfl
  have hentry : ∀ k j : Fin d, Pi.single k (1 : ℝ) ⬝ᵥ A.mulVec (Pi.single j 1) = A k j := by
    intro k j
    rw [Matrix.mulVec_single_one, single_one_dotProduct]
    rfl
  set ek : Vec d := Pi.single k 1
  set ej : Vec d := Pi.single j 1
  have hplus := a.elliptic x (ek + ej)
  have hminus := a.elliptic x (ek - ej)
  have hsq : ∀ u : Vec d, euclideanSq u = u ⬝ᵥ u := fun _ => rfl
  have hek : ek ⬝ᵥ ek = 1 := by simp [ek]
  have hej : ej ⬝ᵥ ej = 1 := by simp [ej]
  have hekj : ek ⬝ᵥ ej = ej ⬝ᵥ ek := dotProduct_comm _ _
  have hcs : (ek ⬝ᵥ ej) ^ 2 ≤ 1 := by
    by_cases hkj : k = j
    · simp [ek, ej, hkj]
    · simp [ek, ej, hkj]
  have hplus_sq : euclideanSq (ek + ej) = 2 + 2 * (ek ⬝ᵥ ej) := by
    rw [hsq, add_dotProduct, dotProduct_add, dotProduct_add, hek, hej, ← hekj]; ring
  have hminus_sq : euclideanSq (ek - ej) = 2 - 2 * (ek ⬝ᵥ ej) := by
    rw [hsq, sub_dotProduct, dotProduct_sub, dotProduct_sub, hek, hej, ← hekj]; ring
  have hplus_q : dot (ek + ej) (A.mulVec (ek + ej)) = A k k + A j j + 2 * A k j := by
    rw [hq, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hentry, hentry,
      hentry, hentry, hsymm]; ring
  have hminus_q : dot (ek - ej) (A.mulVec (ek - ej)) = A k k + A j j - 2 * A k j := by
    rw [hq, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hentry, hentry,
      hentry, hentry, hsymm]; ring
  have hΛ : 0 ≤ Λ := by
    have h0 := a.elliptic x ek
    have : euclideanSq ek = 1 := by rw [hsq, hek]
    rw [this] at h0
    linarith [h0.1, h0.2]
  have hkj_le : |ek ⬝ᵥ ej| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]; exact hcs
  rw [abs_le]
  constructor
  · nlinarith [hplus.1, hplus.2, hminus.1, hminus.2, abs_le.1 hkj_le,
      zero_le_euclideanSq (ek + ej), zero_le_euclideanSq (ek - ej)]
  · nlinarith [hplus.1, hplus.2, hminus.1, hminus.2, abs_le.1 hkj_le,
      zero_le_euclideanSq (ek + ej), zero_le_euclideanSq (ek - ej)]

theorem CoefficientField.aestronglyMeasurable_apply {Λ : ℝ} (a : CoefficientField d Λ)
    (k j : Fin d) (μ : Measure (Vec d)) (hμ : μ ≪ volume) :
    AEStronglyMeasurable (fun x => a x k j) μ :=
  ((a.locally_integrable k j).aestronglyMeasurable).mono_ac hμ

/-! ## Test functions -/

section Tests

variable {U : Set (Vec d)} {φ : Vec d → ℝ}

theorem IsSpatialTest.continuous (hφ : IsSpatialTest U φ) : Continuous φ := hφ.1.continuous

theorem IsSpatialTest.continuous_coordinateDerivative (hφ : IsSpatialTest U φ) (i : Fin d) :
    Continuous (coordinateDerivative i φ) :=
  (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const

theorem IsSpatialTest.hasCompactSupport_coordinateDerivative (hφ : IsSpatialTest U φ)
    (i : Fin d) : HasCompactSupport (coordinateDerivative i φ) :=
  (hφ.2.1.fderiv ℝ).comp_left (g := fun L : Vec d →L[ℝ] ℝ => L (unitVector i)) (by simp)

theorem IsSpatialTest.exists_bound (hφ : IsSpatialTest U φ) : ∃ M, ∀ x, |φ x| ≤ M :=
  hφ.continuous.bounded_above_of_compact_support hφ.2.1

theorem IsSpatialTest.exists_bound_coordinateDerivative (hφ : IsSpatialTest U φ) (i : Fin d) :
    ∃ M, ∀ x, |coordinateDerivative i φ x| ≤ M :=
  (hφ.continuous_coordinateDerivative i).bounded_above_of_compact_support
    (hφ.hasCompactSupport_coordinateDerivative i)

end Tests

/-! ## The pair space -/

/-- The measure `volume` restricted to `B_T(z)`. -/
abbrev ballMeasure (z : Vec d) (T : ℝ) : Measure (Vec d) := volume.restrict (ball z T)

/-- Pairs of an `L²(B_T(z))` potential and `d` gradient components in `L²(B_T(z))`. -/
abbrev PairSpace (d : ℕ) (z : Vec d) (T : ℝ) : Type :=
  Lp ℝ 2 (ballMeasure z T) × (Fin d → Lp ℝ 2 (ballMeasure z T))

variable {z : Vec d} {T : ℝ}

/-- The gradient energy `∑_i ‖g_i‖²_{L²(B_T(z))}` of a pair. -/
def pairGradEnergy (F : PairSpace d z T) : ℝ := ∑ i, ‖F.2 i‖ ^ 2

/-- The quadratic gauge `‖u‖² + ∑_i ‖g_i‖²` of a pair. -/
def pairGauge (F : PairSpace d z T) : ℝ := ‖F.1‖ ^ 2 + pairGradEnergy F

theorem continuous_pairGradEnergy : Continuous (pairGradEnergy : PairSpace d z T → ℝ) :=
  continuous_finsetSum _ fun i _ => ((continuous_apply i).comp continuous_snd).norm.pow 2

theorem pairGradEnergy_nonneg (F : PairSpace d z T) : 0 ≤ pairGradEnergy F :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem isQuadraticGauge_pairGauge : IsQuadraticGauge (pairGauge : PairSpace d z T → ℝ) where
  nonneg F := add_nonneg (sq_nonneg _) (pairGradEnergy_nonneg F)
  parallelogram F G := by
    simp only [pairGauge, pairGradEnergy, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Pi.add_apply, Pi.sub_apply]
    have h1 := parallelogram_law_with_norm ℝ F.1 G.1
    have h2 : ∀ i, ‖F.2 i + G.2 i‖ ^ 2 + ‖F.2 i - G.2 i‖ ^ 2 = 2 * (‖F.2 i‖ ^ 2 + ‖G.2 i‖ ^ 2) :=
      fun i => parallelogram_law_with_norm ℝ (F.2 i) (G.2 i)
    have h3 : ∑ i, ‖F.2 i + G.2 i‖ ^ 2 + ∑ i, ‖F.2 i - G.2 i‖ ^ 2 =
        2 * ∑ i, ‖F.2 i‖ ^ 2 + 2 * ∑ i, ‖G.2 i‖ ^ 2 := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [h2 i]; ring
    linarith
  norm_sq_le F := by
    have hQ : 0 ≤ pairGauge F := add_nonneg (sq_nonneg _) (pairGradEnergy_nonneg F)
    have hle : ‖F‖ ≤ Real.sqrt (pairGauge F) := by
      rw [Prod.norm_def]
      refine max_le (Real.le_sqrt_of_sq_le ?_) ?_
      · exact le_add_of_nonneg_right (pairGradEnergy_nonneg F)
      · refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
        refine Real.le_sqrt_of_sq_le ?_
        refine le_add_of_nonneg_of_le (sq_nonneg _) ?_
        exact Finset.single_le_sum (f := fun j => ‖F.2 j‖ ^ 2) (fun j _ => sq_nonneg _)
          (Finset.mem_univ i)
    calc ‖F‖ ^ 2 ≤ Real.sqrt (pairGauge F) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = pairGauge F := Real.sq_sqrt hQ

/-! ## Inner products with fixed functions -/

theorem inner_toLp_left {μ : Measure (Vec d)} {ψ : Vec d → ℝ} (hψ : MemLp ψ 2 μ)
    (u : Lp ℝ 2 μ) : ⟪hψ.toLp ψ, u⟫_ℝ = ∫ x, u x * ψ x ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hψ.coeFn_toLp] with x hx
  simp [hx]

theorem inner_toLp_toLp {μ : Measure (Vec d)} {ψ u : Vec d → ℝ} (hψ : MemLp ψ 2 μ)
    (hu : MemLp u 2 μ) : ⟪hψ.toLp ψ, hu.toLp u⟫_ℝ = ∫ x, u x * ψ x ∂μ := by
  rw [inner_toLp_left]
  refine integral_congr_ae ?_
  filter_upwards [hu.coeFn_toLp] with x hx
  simp [hx]

theorem norm_sq_eq_integral {μ : Measure (Vec d)} (u : Lp ℝ 2 μ) :
    ‖u‖ ^ 2 = ∫ x, u x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [sq]

theorem norm_toLp_sq_eq_integral {μ : Measure (Vec d)} {u : Vec d → ℝ} (hu : MemLp u 2 μ) :
    ‖hu.toLp u‖ ^ 2 = ∫ x, u x ^ 2 ∂μ := by
  rw [norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [hu.coeFn_toLp] with x hx
  simp [hx]

/-! ## Test functions as `L²(B_T(z))` elements -/

theorem memLp_of_continuous_of_bound {μ : Measure (Vec d)} [IsFiniteMeasure μ]
    {f : Vec d → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) : MemLp f 2 μ :=
  MemLp.of_bound hf.aestronglyMeasurable M (Eventually.of_forall fun x => by simpa using hM x)

theorem IsSpatialTest.memLp {U : Set (Vec d)} {φ : Vec d → ℝ} (hφ : IsSpatialTest U φ)
    (μ : Measure (Vec d)) [IsFiniteMeasure μ] : MemLp φ 2 μ :=
  memLp_of_continuous_of_bound hφ.continuous (hφ.exists_bound.choose_spec)

theorem IsSpatialTest.memLp_coordinateDerivative {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hφ : IsSpatialTest U φ) (i : Fin d) (μ : Measure (Vec d)) [IsFiniteMeasure μ] :
    MemLp (coordinateDerivative i φ) 2 μ :=
  memLp_of_continuous_of_bound (hφ.continuous_coordinateDerivative i)
    ((hφ.exists_bound_coordinateDerivative i).choose_spec)

/-- The function `x ↦ ∑_k a_{kj}(x) ∂_k φ(x)`, for the weak form of `∇·(a g) = 0`. -/
def coefficientTest {Λ : ℝ} (a : CoefficientField d Λ) (φ : Vec d → ℝ) (j : Fin d)
    (x : Vec d) : ℝ :=
  ∑ k, a x k j * coordinateDerivative k φ x

theorem IsSpatialTest.memLp_coefficientTest {Λ : ℝ} (a : CoefficientField d Λ)
    {U : Set (Vec d)} {φ : Vec d → ℝ} (hφ : IsSpatialTest U φ) (j : Fin d)
    (μ : Measure (Vec d)) [IsFiniteMeasure μ] (hμ : μ ≪ volume) :
    MemLp (coefficientTest a φ j) 2 μ := by
  choose M hM using hφ.exists_bound_coordinateDerivative
  refine MemLp.of_bound ?_ (∑ k, Λ * M k) (Eventually.of_forall fun x => ?_)
  · refine Finset.aestronglyMeasurable_fun_sum _ fun k _ => ?_
    exact (a.aestronglyMeasurable_apply k j μ hμ).mul
      (hφ.continuous_coordinateDerivative k).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul]
    exact mul_le_mul (a.abs_apply_le x k j) (hM k x) (abs_nonneg _)
      ((abs_nonneg _).trans (a.abs_apply_le x k j))

/-- The pointwise identity `(a g)·∇φ = ∑_j g_j ∑_k a_{kj} ∂_k φ`. -/
theorem dot_mulVec_gradient {Λ : ℝ} (a : CoefficientField d Λ) (φ : Vec d → ℝ) (g : Vec d)
    (x : Vec d) :
    dot ((a x).mulVec g) (gradient φ x) = ∑ j, g j * coefficientTest a φ j x := by
  simp only [dot, Matrix.mulVec, dotProduct, gradient, coefficientTest, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ## The constraints -/

/-- The weak gradient constraint `⟨u, ∂_i φ⟩ + ⟨g_i, φ⟩ = 0`. -/
def gradConstraint {φ : Vec d → ℝ} (hφ : IsSpatialTest (ball z T) φ) (i : Fin d)
    (F : PairSpace d z T) : ℝ :=
  ⟪(hφ.memLp_coordinateDerivative i (ballMeasure z T)).toLp _, F.1⟫_ℝ +
    ⟪(hφ.memLp (ballMeasure z T)).toLp _, F.2 i⟫_ℝ

/-- The weak harmonicity constraint `⟨a g, ∇φ⟩ = 0`. -/
def harmConstraint {Λ : ℝ} (a : CoefficientField d Λ) {φ : Vec d → ℝ}
    (hφ : IsSpatialTest (ball z T) φ) (F : PairSpace d z T) : ℝ :=
  ∑ j, ⟪(hφ.memLp_coefficientTest a j (ballMeasure z T)
    Measure.restrict_le_self.absolutelyContinuous).toLp _, F.2 j⟫_ℝ

theorem continuous_gradConstraint {φ : Vec d → ℝ} (hφ : IsSpatialTest (ball z T) φ)
    (i : Fin d) : Continuous (gradConstraint hφ i : PairSpace d z T → ℝ) :=
  (continuous_const.inner continuous_fst).add
    (continuous_const.inner ((continuous_apply i).comp continuous_snd))

theorem continuous_harmConstraint {Λ : ℝ} (a : CoefficientField d Λ) {φ : Vec d → ℝ}
    (hφ : IsSpatialTest (ball z T) φ) :
    Continuous (harmConstraint a hφ : PairSpace d z T → ℝ) :=
  continuous_finsetSum _ fun j _ =>
    continuous_const.inner ((continuous_apply j).comp continuous_snd)

theorem gradConstraint_eq {φ : Vec d → ℝ} (hφ : IsSpatialTest (ball z T) φ) (i : Fin d)
    (F : PairSpace d z T) :
    gradConstraint hφ i F = (∫ x in ball z T, F.1 x * coordinateDerivative i φ x) +
      ∫ x in ball z T, F.2 i x * φ x := by
  rw [gradConstraint, inner_toLp_left, inner_toLp_left]

theorem harmConstraint_eq {Λ : ℝ} (a : CoefficientField d Λ) {φ : Vec d → ℝ}
    (hφ : IsSpatialTest (ball z T) φ) (F : PairSpace d z T) :
    harmConstraint a hφ F =
      ∫ x in ball z T, dot ((a x).mulVec (fun j => F.2 j x)) (gradient φ x) := by
  rw [harmConstraint]
  simp_rw [inner_toLp_left, dot_mulVec_gradient]
  rw [integral_finsetSum]
  intro j _
  exact (Lp.memLp (F.2 j)).integrable_mul (hφ.memLp_coefficientTest a j (ballMeasure z T)
    Measure.restrict_le_self.absolutelyContinuous)

theorem gradConstraint_add {φ : Vec d → ℝ} (hφ : IsSpatialTest (ball z T) φ) (i : Fin d)
    (F G : PairSpace d z T) :
    gradConstraint hφ i (F + G) = gradConstraint hφ i F + gradConstraint hφ i G := by
  simp only [gradConstraint, Prod.fst_add, Prod.snd_add, Pi.add_apply, inner_add_right]; ring

theorem gradConstraint_smul {φ : Vec d → ℝ} (hφ : IsSpatialTest (ball z T) φ) (i : Fin d)
    (c : ℝ) (F : PairSpace d z T) :
    gradConstraint hφ i (c • F) = c * gradConstraint hφ i F := by
  simp only [gradConstraint, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, real_inner_smul_right]
  ring

theorem harmConstraint_add {Λ : ℝ} (a : CoefficientField d Λ) {φ : Vec d → ℝ}
    (hφ : IsSpatialTest (ball z T) φ) (F G : PairSpace d z T) :
    harmConstraint a hφ (F + G) = harmConstraint a hφ F + harmConstraint a hφ G := by
  simp only [harmConstraint, Prod.snd_add, Pi.add_apply, inner_add_right,
    Finset.sum_add_distrib]

theorem harmConstraint_smul {Λ : ℝ} (a : CoefficientField d Λ) {φ : Vec d → ℝ}
    (hφ : IsSpatialTest (ball z T) φ) (c : ℝ) (F : PairSpace d z T) :
    harmConstraint a hφ (c • F) = c * harmConstraint a hφ F := by
  simp only [harmConstraint, Prod.smul_snd, Pi.smul_apply, real_inner_smul_right,
    Finset.mul_sum]

/-- A harmonic pair: `g` is the weak gradient of `u` and `∇·(a g) = 0` in `B_T(z)`. -/
def IsHarmonicPair {Λ : ℝ} (a : CoefficientField d Λ) (F : PairSpace d z T) : Prop :=
  (∀ (φ : Vec d → ℝ) (hφ : IsSpatialTest (ball z T) φ) (i : Fin d), gradConstraint hφ i F = 0) ∧
    ∀ (φ : Vec d → ℝ) (hφ : IsSpatialTest (ball z T) φ), harmConstraint a hφ F = 0

/-- The admissible pairs: harmonic pairs with gradient energy at most `C² |B_T(z)|`. -/
def admissiblePairs {Λ : ℝ} (a : CoefficientField d Λ) (z : Vec d) (T C : ℝ) :
    Set (PairSpace d z T) :=
  {F | IsHarmonicPair a F ∧ pairGradEnergy F ≤ C ^ 2 * volume.real (ball z T)}

theorem isClosed_admissiblePairs {Λ : ℝ} (a : CoefficientField d Λ) (z : Vec d) (T C : ℝ) :
    IsClosed (admissiblePairs a z T C) := by
  have h1 : IsClosed {F : PairSpace d z T | ∀ (φ : Vec d → ℝ) (hφ : IsSpatialTest (ball z T) φ)
      (i : Fin d), gradConstraint hφ i F = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun φ => isClosed_iInter fun hφ => isClosed_iInter fun i =>
      isClosed_eq (continuous_gradConstraint hφ i) continuous_const
  have h2 : IsClosed {F : PairSpace d z T | ∀ (φ : Vec d → ℝ)
      (hφ : IsSpatialTest (ball z T) φ), harmConstraint a hφ F = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun φ => isClosed_iInter fun hφ =>
      isClosed_eq (continuous_harmConstraint a hφ) continuous_const
  have h3 : IsClosed {F : PairSpace d z T | pairGradEnergy F ≤ C ^ 2 * volume.real (ball z T)} :=
    isClosed_le continuous_pairGradEnergy continuous_const
  exact (h1.inter h2).inter h3

theorem convexOn_pairGradEnergy :
    ConvexOn ℝ Set.univ (pairGradEnergy : PairSpace d z T → ℝ) := by
  refine ⟨convex_univ, fun F _ G _ s t hs ht hst => ?_⟩
  simp only [pairGradEnergy, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖s • F.2 i + t • G.2 i‖ ≤ s * ‖F.2 i‖ + t * ‖G.2 i‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]
  have h2 : ‖s • F.2 i + t • G.2 i‖ ^ 2 ≤ (s * ‖F.2 i‖ + t * ‖G.2 i‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : (s * ‖F.2 i‖ + t * ‖G.2 i‖) ^ 2 ≤ s * ‖F.2 i‖ ^ 2 + t * ‖G.2 i‖ ^ 2 := by
    have ht' : t = 1 - s := by linarith
    subst ht'
    nlinarith [sq_nonneg (‖F.2 i‖ - ‖G.2 i‖), mul_nonneg hs ht]
  linarith

theorem convex_admissiblePairs {Λ : ℝ} (a : CoefficientField d Λ) (z : Vec d) (T C : ℝ) :
    Convex ℝ (admissiblePairs a z T C) := by
  intro F hF G hG s t hs ht hst
  refine ⟨⟨fun φ hφ i => ?_, fun φ hφ => ?_⟩, ?_⟩
  · rw [gradConstraint_add, gradConstraint_smul, gradConstraint_smul, hF.1.1 φ hφ i,
      hG.1.1 φ hφ i]; ring
  · rw [harmConstraint_add, harmConstraint_smul, harmConstraint_smul, hF.1.2 φ hφ,
      hG.1.2 φ hφ]; ring
  · have h := convexOn_pairGradEnergy.2 (Set.mem_univ F) (Set.mem_univ G) hs ht hst
    calc pairGradEnergy (s • F + t • G) ≤ s • pairGradEnergy F + t • pairGradEnergy G := h
      _ ≤ s • (C ^ 2 * volume.real (ball z T)) + t • (C ^ 2 * volume.real (ball z T)) := by
          simp only [smul_eq_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left hF.2 hs) (mul_le_mul_of_nonneg_left hG.2 ht)
      _ = C ^ 2 * volume.real (ball z T) := by
          simp only [smul_eq_mul]; rw [← add_mul, hst, one_mul]

theorem zero_mem_admissiblePairs {Λ : ℝ} (a : CoefficientField d Λ) (z : Vec d) (T : ℝ)
    {C : ℝ} : (0 : PairSpace d z T) ∈ admissiblePairs a z T C := by
  refine ⟨⟨fun φ hφ i => ?_, fun φ hφ => ?_⟩, ?_⟩
  · simp [gradConstraint]
  · simp [harmConstraint]
  · simp only [pairGradEnergy, Prod.snd_zero, Pi.zero_apply, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    exact mul_nonneg (sq_nonneg C) measureReal_nonneg

/-! ## From local harmonic functions to pairs and back -/

variable {Λ : ℝ} {a : CoefficientField d Λ}

theorem LocalHarmonic.memLp_grad (w : LocalHarmonic a z T) (i : Fin d) :
    MemLp (fun x => w.grad x i) 2 (ballMeasure z T) :=
  w.gradient_square_integrable.of_le ((w.weak_gradient i).2.1.aestronglyMeasurable)
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (zero_le_euclideanNorm _)]
      exact abs_coord_le_euclideanNorm (w.grad x) i)

/-- The pair of `L²(B_T(z))` classes of a local harmonic function. -/
def LocalHarmonic.toPair (w : LocalHarmonic a z T) : PairSpace d z T :=
  (w.square_integrable.toLp _, fun i => (w.memLp_grad i).toLp _)

theorem LocalHarmonic.toPair_fst_ae (w : LocalHarmonic a z T) :
    (w.toPair.1 : Vec d → ℝ) =ᵐ[ballMeasure z T] w.potential :=
  w.square_integrable.coeFn_toLp

theorem LocalHarmonic.toPair_snd_ae (w : LocalHarmonic a z T) (i : Fin d) :
    (w.toPair.2 i : Vec d → ℝ) =ᵐ[ballMeasure z T] fun x => w.grad x i :=
  (w.memLp_grad i).coeFn_toLp

theorem LocalHarmonic.integral_euclideanSq_grad (w : LocalHarmonic a z T) :
    ∫ x in ball z T, euclideanSq (w.grad x) = pairGradEnergy w.toPair := by
  simp only [pairGradEnergy, LocalHarmonic.toPair, norm_toLp_sq_eq_integral]
  rw [← integral_finsetSum _ fun i _ => (w.memLp_grad i).integrable_sq]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [euclideanSq, dot, sq]

theorem LocalHarmonic.isHarmonicPair_toPair (w : LocalHarmonic a z T) :
    IsHarmonicPair a w.toPair := by
  refine ⟨fun φ hφ i => ?_, fun φ hφ => ?_⟩
  · rw [gradConstraint_eq]
    have h1 : (∫ x in ball z T, w.toPair.1 x * coordinateDerivative i φ x) =
        ∫ x in ball z T, w.potential x * coordinateDerivative i φ x := by
      refine integral_congr_ae ?_
      filter_upwards [w.toPair_fst_ae] with x hx
      rw [hx]
    have h2 : (∫ x in ball z T, w.toPair.2 i x * φ x) = ∫ x in ball z T, w.grad x i * φ x := by
      refine integral_congr_ae ?_
      filter_upwards [w.toPair_snd_ae i] with x hx
      rw [hx]
    rw [h1, h2, (w.weak_gradient i).2.2 φ hφ]
    ring
  · rw [harmConstraint_eq]
    have hae : ∀ᵐ x ∂ballMeasure z T, (fun j => w.toPair.2 j x) = w.grad x := by
      have := ae_all_iff.2 fun j => w.toPair_snd_ae j
      filter_upwards [this] with x hx
      funext j
      exact hx j
    have h1 : (∫ x in ball z T, dot ((a x).mulVec (fun j => w.toPair.2 j x)) (gradient φ x)) =
        ∫ x in ball z T, dot ((a x).mulVec (w.grad x)) (gradient φ x) := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [hx]
    rw [h1, w.harmonic.2.2 φ hφ]
    simp

theorem LocalHarmonic.admissible_iff (w : LocalHarmonic a z T) {C : ℝ} (hC : 0 ≤ C)
    (hT : 0 < T) :
    IsLocalizationAdmissible C w ↔ pairGradEnergy w.toPair ≤ C ^ 2 * volume.real (ball z T) := by
  rw [IsLocalizationAdmissible, vectorRms, Real.sqrt_le_left hC, setAverage_eq, smul_eq_mul,
    w.integral_euclideanSq_grad, inv_mul_le_iff₀ (volume_real_ball_pos z hT)]
  constructor <;> intro h <;> linarith

theorem LocalHarmonic.toPair_mem (w : LocalHarmonic a z T) {C : ℝ} (hC : 0 ≤ C) (hT : 0 < T)
    (hw : IsLocalizationAdmissible C w) : w.toPair ∈ admissiblePairs a z T C :=
  ⟨w.isHarmonicPair_toPair, (w.admissible_iff hC hT).1 hw⟩

theorem integrableOn_ball_of_Lp (u : Lp ℝ 2 (ballMeasure z T)) :
    IntegrableOn (u : Vec d → ℝ) (ball z T) volume :=
  (Lp.memLp u).integrable one_le_two

/-- The local harmonic function given by representatives of a harmonic pair. -/
def ofPair (a : CoefficientField d Λ) (F : PairSpace d z T) (hF : IsHarmonicPair a F) :
    LocalHarmonic a z T where
  potential := F.1
  grad := fun x i => F.2 i x
  square_integrable := Lp.memLp F.1
  gradient_square_integrable := by
    have hmeas : AEStronglyMeasurable (fun x => euclideanNorm fun i => (F.2 i : Vec d → ℝ) x)
        (ballMeasure z T) := by
      have h : AEStronglyMeasurable
          (fun x => ∑ i, (F.2 i : Vec d → ℝ) x * (F.2 i : Vec d → ℝ) x) (ballMeasure z T) :=
        Finset.aestronglyMeasurable_fun_sum _
          fun i _ => (Lp.aestronglyMeasurable (F.2 i)).mul (Lp.aestronglyMeasurable (F.2 i))
      exact Real.continuous_sqrt.comp_aestronglyMeasurable h
    refine (memLp_two_iff_integrable_sq hmeas).2 ?_
    have hsum : Integrable (fun x => ∑ i, (F.2 i : Vec d → ℝ) x ^ 2) (ballMeasure z T) :=
      integrable_finsetSum _ fun i _ => (Lp.memLp (F.2 i)).integrable_sq
    refine hsum.congr (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [sq_euclideanNorm]
    simp only [euclideanSq, dot, sq]
  weak_gradient := fun i => by
    refine ⟨(integrableOn_ball_of_Lp F.1).locallyIntegrableOn,
      (integrableOn_ball_of_Lp (F.2 i)).locallyIntegrableOn, fun φ hφ => ?_⟩
    have h := hF.1 φ hφ i
    rw [gradConstraint_eq] at h
    linarith
  harmonic := by
    refine ⟨fun k => ?_, locallyIntegrableOn_const 0, fun φ hφ => ?_⟩
    · refine IntegrableOn.locallyIntegrableOn ?_
      have : (fun x => ((a x).mulVec (fun i => (F.2 i : Vec d → ℝ) x)) k) =
          fun x => ∑ j, a x k j * (F.2 j : Vec d → ℝ) x := by
        funext x; simp [Matrix.mulVec, dotProduct]
      rw [this]
      refine integrable_finsetSum _ fun j _ => ?_
      refine Integrable.bdd_mul (c := Λ) (integrableOn_ball_of_Lp (F.2 j))
        (a.aestronglyMeasurable_apply k j _ Measure.restrict_le_self.absolutelyContinuous)
        (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs]
      exact a.abs_apply_le x k j
    · have h := hF.2 φ hφ
      rw [harmConstraint_eq] at h
      rw [h]
      simp

@[simp] theorem ofPair_potential (F : PairSpace d z T) (hF : IsHarmonicPair a F) :
    (ofPair a F hF).potential = F.1 := rfl

@[simp] theorem ofPair_grad (F : PairSpace d z T) (hF : IsHarmonicPair a F) (x : Vec d)
    (i : Fin d) : (ofPair a F hF).grad x i = F.2 i x := rfl

theorem toPair_ofPair (F : PairSpace d z T) (hF : IsHarmonicPair a F) :
    (ofPair a F hF).toPair = F := by
  ext1
  · exact Lp.toLp_coeFn F.1 (Lp.memLp F.1)
  · funext i
    exact Lp.toLp_coeFn (F.2 i) (Lp.memLp (F.2 i))

end QSH
