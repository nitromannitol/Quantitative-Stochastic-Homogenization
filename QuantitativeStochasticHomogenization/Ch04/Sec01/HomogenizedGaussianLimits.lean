import QuantitativeStochasticHomogenization.Ch04.Sec01.StationaryCubeAverages
import QuantitativeStochasticHomogenization.Ch04.Sec01.GaussianAverageBasis
import QuantitativeStochasticHomogenization.Ch01.Sec03.DirichletEnergyCorrectorBounds
import QuantitativeStochasticHomogenization.Ch04.Sec03.EnergyFromRate
import QuantitativeStochasticHomogenization.Ch03.Sec04.GaussianSublinearity

/-!
# Gaussian limits of the corrected fields

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.3 and Proposition 3.21. Suppose that almost surely the coordinate corrected fields of `S`
satisfy `GaussianBasisBounds` with a matrix `M` at every scale `r ≥ Y(a)`, with error
`C (Y(a)/r)^θ`, where `Y ≥ 1` has finite moments. Then:

* `transpose_eq_of_basisBounds`: `M` is symmetric;
* `ae_tendsto_energy` and `ae_tendsto_lowerDensity`: the Gaussian averages at the origin of the
  energy density `G e · a G e` and of `e · a G e - ½ G e · a G e` converge to `e · M e` and
  `½ e · M e`;
* `ae_energy_envelope`: the averages `∫ Φ_{0,r} G e · a G e`, `r ≥ 1`, are at most
  `K (1 + Y^d)`;
* `setIntegral_cell_energy_eq`, `setIntegral_cell_lowerDensity_eq`: the cell means of the two
  densities are `e · M e` and `½ e · M e`.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

theorem tendsto_div_rpow_atTop_zero {Y θ : ℝ} (hY : 0 ≤ Y) (hθ : 0 < θ) :
    Tendsto (fun r : ℝ => (Y / r) ^ θ) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop hθ).const_mul (Y ^ θ)
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  rw [Real.div_rpow hY hr.le, Real.rpow_neg hr.le, div_eq_mul_inv]

theorem tendsto_natCast_add_one_atTop :
    Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
  tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop

open Matrix in
theorem dot_unitVector_mulVec_unitVector (A : Mat d) (i j : Fin d) :
    dot (unitVector i) (A.mulVec (unitVector j)) = A i j := by
  show (Pi.single i 1 : Vec d) ⬝ᵥ (A *ᵥ Pi.single j 1) = A i j
  simp [Matrix.mulVec_single]

/-- **Matrices with the same quadratic form.** -/
theorem eq_of_forall_dot_mulVec_eq {A B : Mat d} (hA : A.transpose = A) (hB : B.transpose = B)
    (h : ∀ e : Vec d, dot e (A.mulVec e) = dot e (B.mulVec e)) : A = B := by
  have hpol : ∀ (C : Mat d), C.transpose = C → ∀ i j : Fin d,
      dot (unitVector i + unitVector j) (C.mulVec (unitVector i + unitVector j)) =
        C i i + 2 * C i j + C j j := by
    intro C hC i j
    have hs : C j i = C i j := by
      have := congrFun (congrFun hC i) j
      simpa [Matrix.transpose_apply] using this
    simp only [Matrix.mulVec_add, dot, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
    have e1 := dot_unitVector_mulVec_unitVector C i i
    have e2 := dot_unitVector_mulVec_unitVector C i j
    have e3 := dot_unitVector_mulVec_unitVector C j i
    have e4 := dot_unitVector_mulVec_unitVector C j j
    simp only [dot] at e1 e2 e3 e4
    rw [e1, e2, e3, e4, hs]
    ring
  ext i j
  have h1 := h (unitVector i + unitVector j)
  have h2 := h (unitVector i)
  have h3 := h (unitVector j)
  rw [hpol A hA, hpol B hB] at h1
  rw [dot_unitVector_mulVec_unitVector, dot_unitVector_mulVec_unitVector] at h2 h3
  linarith

variable {P : Measure (CoefficientField d Λ)}

/-- **The matrix of the basis bounds is symmetric.** -/
theorem transpose_eq_of_basisBounds [IsProbabilityMeasure P] (S : HomogenizationData P)
    {M : Mat d}
    {Y : CoefficientField d Λ → ℝ} (hY0 : ∀ a, 0 ≤ Y a) {Cε θ : ℝ} (hθ : 0 < θ)
    (hB : ∀ᵐ a ∂P, ∀ (r : ℝ) (x₀ : Vec d), Y a ≤ r → euclideanNorm x₀ ≤ r →
      GaussianBasisBounds a M (correctedCoordinate S a) x₀ r (Cε * (Y a / r) ^ θ)) :
    M.transpose = M := by
  obtain ⟨a, ha⟩ := hB.exists
  ext i l
  rw [Matrix.transpose_apply]
  have hbound : ∀ r : ℝ, max (Y a) 1 ≤ r → |M l i - M i l| ≤ 2 * (Cε * (Y a / r) ^ θ) := by
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hr)
    have hx : euclideanNorm (0 : Vec d) ≤ r := by
      simp [euclideanNorm, euclideanSq, dot, hr0.le]
    obtain ⟨-, -, -, -, -, hE⟩ := ha r 0 ((le_max_left _ _).trans hr) hx
    have h1 := hE l i
    have h2 := hE i l
    have hsym : ∫ x, heatKernel 0 r x * dot (correctedCoordinate S a l x)
        ((a x).mulVec (correctedCoordinate S a i x)) =
        ∫ x, heatKernel 0 r x * dot (correctedCoordinate S a i x)
          ((a x).mulVec (correctedCoordinate S a l x)) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [dot_mulVec_comm_of_symm (a.symmetric x)]
    rw [hsym] at h1
    calc |M l i - M i l| = |(M l i - ∫ x, heatKernel 0 r x * dot (correctedCoordinate S a i x)
          ((a x).mulVec (correctedCoordinate S a l x))) + ((∫ x, heatKernel 0 r x *
            dot (correctedCoordinate S a i x) ((a x).mulVec (correctedCoordinate S a l x))) -
              M i l)| := by rw [sub_add_sub_cancel]
      _ ≤ _ := (abs_add_le _ _).trans (by rw [abs_sub_comm] at h1; linarith)
  have hlim : Tendsto (fun r : ℝ => 2 * (Cε * (Y a / r) ^ θ)) atTop (𝓝 0) := by
    have := ((tendsto_div_rpow_atTop_zero (hY0 a) hθ).const_mul Cε).const_mul 2
    simpa using this
  have hle := ge_of_tendsto hlim ((eventually_ge_atTop (max (Y a) 1)).mono hbound)
  have := abs_nonneg (M l i - M i l)
  have h0 : M l i - M i l = 0 := abs_eq_zero.mp (le_antisymm hle this)
  linarith

theorem euclideanNorm_zero_le {r : ℝ} (hr : 0 ≤ r) : euclideanNorm (0 : Vec d) ≤ r := by
  simp [euclideanNorm, euclideanSq, dot, hr]

/-- The bounds (3.101)–(3.103) at the origin, from the basis bounds. -/
theorem ae_gaussianAverageBounds_origin (S : HomogenizationData P) {M : Mat d}
    {Y : CoefficientField d Λ → ℝ} {Cε θ : ℝ} (hCε : 0 ≤ Cε) (hY0 : ∀ a, 0 ≤ Y a)
    (hB : ∀ᵐ a ∂P, ∀ (r : ℝ) (x₀ : Vec d), Y a ≤ r → euclideanNorm x₀ ≤ r →
      GaussianBasisBounds a M (correctedCoordinate S a) x₀ r (Cε * (Y a / r) ^ θ)) :
    ∀ᵐ a ∂P, ∀ r : ℝ, Y a ≤ r →
      GaussianAverageBounds a M (correctedField S a) 0 r ((d : ℝ) ^ 2 * (Cε * (Y a / r) ^ θ)) := by
  filter_upwards [hB] with a ha r hr
  have hr0 : 0 ≤ r := (hY0 a).trans hr
  exact gaussianAverageBounds_of_basis
    (mul_nonneg hCε (Real.rpow_nonneg (div_nonneg (hY0 a) hr0) _))
    (ha r 0 hr (euclideanNorm_zero_le hr0))

theorem abs_dot_le_sum_mul (u v : Vec d) : |dot u v| ≤ d * euclideanNorm u * euclideanNorm v := by
  unfold dot
  calc |∑ k, u k * v k| ≤ ∑ k, |u k * v k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin d, euclideanNorm u * euclideanNorm v := Finset.sum_le_sum fun k _ => by
        rw [abs_mul]
        exact mul_le_mul (abs_apply_le_euclideanNorm u k) (abs_apply_le_euclideanNorm v k)
          (abs_nonneg _) (Real.sqrt_nonneg _)
    _ = d * euclideanNorm u * euclideanNorm v := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The density `e · a G e - ½ G e · a G e` of the dual bound. -/
def lowerDensity (S : HomogenizationData P) (e : Vec d) (a : CoefficientField d Λ) (x : Vec d) :
    ℝ :=
  dot e (fluxDensity S e a x) - (1 / 2 : ℝ) * energyDensity S e a x

theorem measurable_lowerDensity (S : HomogenizationData P) (e : Vec d) :
    Measurable fun p : CoefficientField d Λ × Vec d => lowerDensity S e p.1 p.2 := by
  unfold lowerDensity dot
  refine (Finset.measurable_sum _ fun k _ => ?_).sub
    ((measurable_energyDensity S e).const_mul _)
  exact measurable_const.mul ((measurable_pi_apply k).comp (measurable_fluxDensity S e))

theorem ae_lowerDensity_add_latticeShift (S : HomogenizationData P) (e : Vec d)
    (n : LatticeIndex d) :
    ∀ᵐ a ∂P, ∀ᵐ x, lowerDensity S e a (x + latticeShift n) =
      lowerDensity S e (translate (latticeShift n) a) x := by
  filter_upwards [ae_fluxDensity_add_latticeShift S e n,
    ae_energyDensity_add_latticeShift S e n] with a ha hb
  filter_upwards [ha, hb] with x hx1 hx2
  rw [lowerDensity, lowerDensity, hx1, hx2]

theorem ae_lowerDensity_eq (S : HomogenizationData P) (e : Vec d) (a : CoefficientField d Λ) :
    ∀ᵐ x, lowerDensity S e a x = dot e ((a x).mulVec (correctedField S a e x)) -
      (1 / 2 : ℝ) * dot (correctedField S a e x) ((a x).mulVec (correctedField S a e x)) := by
  filter_upwards [ae_fluxDensity_eq S e a, ae_energyDensity_eq S e a] with x h1 h2
  rw [lowerDensity, h1, h2]

theorem integrable_heatKernel_mul_dot {z : Vec d} {r : ℝ} {F : Vec d → Vec d} (e : Vec d)
    (hF : Integrable fun x => heatKernel z r x • F x) :
    Integrable fun x => heatKernel z r x * dot e (F x) := by
  have hk : ∀ k, Integrable fun x => heatKernel z r x * F x k := fun k =>
    (integrable_pi_iff.mp hF) k
  refine (integrable_finsetSum Finset.univ fun k _ => (hk k).const_mul (e k)).congr
    (Eventually.of_forall fun x => ?_)
  simp only [dot, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The Gaussian average of `e · a G` is `e` paired with the average of `a G`. -/
theorem integral_heatKernel_mul_dot_eq {z : Vec d} {r : ℝ} {F : Vec d → Vec d} (e : Vec d)
    (hF : Integrable fun x => heatKernel z r x • F x) :
    ∫ x, heatKernel z r x * dot e (F x) = dot e (∫ x, heatKernel z r x • F x) := by
  have hk : ∀ k, Integrable fun x => heatKernel z r x * F x k := fun k =>
    (integrable_pi_iff.mp hF) k
  have h1 : (fun x => heatKernel z r x * dot e (F x)) =
      fun x => ∑ k, e k * (heatKernel z r x * F x k) := by
    funext x
    unfold dot
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [h1, integral_finsetSum _ fun k _ => (hk k).const_mul _]
  unfold dot
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, eval_integral (integrable_pi_iff.mp hF) k]
  rfl

/-- **Gaussian limits of the energy density and of the dual density at the origin.** -/
theorem ae_tendsto_energy_lowerDensity (S : HomogenizationData P) {M : Mat d}
    {Y : CoefficientField d Λ → ℝ} {Cε θ : ℝ} (hCε : 0 ≤ Cε) (hθ : 0 < θ) (hY0 : ∀ a, 0 ≤ Y a)
    (hB : ∀ᵐ a ∂P, ∀ (r : ℝ) (x₀ : Vec d), Y a ≤ r → euclideanNorm x₀ ≤ r →
      GaussianBasisBounds a M (correctedCoordinate S a) x₀ r (Cε * (Y a / r) ^ θ)) (e : Vec d) :
    ∀ᵐ a ∂P,
      Tendsto (fun n : ℕ => ∫ x, heatKernel 0 ((n : ℝ) + 1) x • energyDensity S e a x) atTop
        (𝓝 (dot e (M.mulVec e))) ∧
      Tendsto (fun n : ℕ => ∫ x, heatKernel 0 ((n : ℝ) + 1) x • lowerDensity S e a x) atTop
        (𝓝 ((1 / 2 : ℝ) * dot e (M.mulVec e))) := by
  filter_upwards [ae_gaussianAverageBounds_origin S hCε hY0 hB] with a ha
  set ε : ℝ → ℝ := fun r => (d : ℝ) ^ 2 * (Cε * (Y a / r) ^ θ) with hε
  have hεlim : Tendsto (fun n : ℕ => ε ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have h := ((tendsto_div_rpow_atTop_zero (hY0 a) hθ).const_mul Cε).const_mul ((d : ℝ) ^ 2)
    simp only [mul_zero] at h
    exact h.comp tendsto_natCast_add_one_atTop
  have hev : ∀ᶠ n : ℕ in atTop, Y a ≤ (n : ℝ) + 1 :=
    tendsto_natCast_add_one_atTop.eventually_ge_atTop (Y a)
  have he2 : 0 ≤ euclideanNorm e := Real.sqrt_nonneg _
  constructor
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim2 : Tendsto (fun n : ℕ => 2 * ε ((n : ℝ) + 1) * euclideanNorm e ^ 2) atTop (𝓝 0) := by
      have := (hεlim.const_mul 2).mul_const (euclideanNorm e ^ 2)
      simpa using this
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hlim2
    filter_upwards [hev] with n hn
    obtain ⟨-, -, -, -, -, h3⟩ := ha _ hn e
    rw [integral_heatKernel_smul_energyDensity, Real.norm_eq_abs]
    exact h3
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim2 : Tendsto (fun n : ℕ => (d + 1) * ε ((n : ℝ) + 1) * euclideanNorm e ^ 2) atTop
        (𝓝 0) := by
      have := (hεlim.const_mul ((d : ℝ) + 1)).mul_const (euclideanNorm e ^ 2)
      simpa using this
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hlim2
    filter_upwards [hev] with n hn
    obtain ⟨-, h2i, h3i, -, h2, h3⟩ := ha _ hn e
    have hrep : ∫ x, heatKernel 0 ((n : ℝ) + 1) x • lowerDensity S e a x =
        dot e (∫ x, heatKernel 0 ((n : ℝ) + 1) x • (a x).mulVec (correctedField S a e x)) -
          (1 / 2 : ℝ) * ∫ x, heatKernel 0 ((n : ℝ) + 1) x *
            dot (correctedField S a e x) ((a x).mulVec (correctedField S a e x)) := by
      have hI1 := integrable_heatKernel_mul_dot e h2i
      rw [← integral_heatKernel_mul_dot_eq e h2i, ← integral_const_mul,
        ← integral_sub hI1 (h3i.const_mul _)]
      refine integral_congr_ae ?_
      filter_upwards [ae_lowerDensity_eq S e a] with x hx
      rw [hx, smul_eq_mul]
      ring
    rw [hrep, Real.norm_eq_abs]
    have hd := abs_dot_le_sum_mul e
      ((∫ x, heatKernel 0 ((n : ℝ) + 1) x • (a x).mulVec (correctedField S a e x)) - M.mulVec e)
    have hsplit : dot e (∫ x, heatKernel 0 ((n : ℝ) + 1) x • (a x).mulVec (correctedField S a e x)) -
        (1 / 2 : ℝ) * (∫ x, heatKernel 0 ((n : ℝ) + 1) x *
          dot (correctedField S a e x) ((a x).mulVec (correctedField S a e x))) -
        (1 / 2 : ℝ) * dot e (M.mulVec e) =
        dot e ((∫ x, heatKernel 0 ((n : ℝ) + 1) x • (a x).mulVec (correctedField S a e x)) -
          M.mulVec e) - (1 / 2 : ℝ) * ((∫ x, heatKernel 0 ((n : ℝ) + 1) x *
            dot (correctedField S a e x) ((a x).mulVec (correctedField S a e x))) -
              dot e (M.mulVec e)) := by
      simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [hsplit]
    have hε0 : 0 ≤ ε ((n : ℝ) + 1) := by
      simp only [hε]
      have : 0 ≤ Y a / ((n : ℝ) + 1) := div_nonneg (hY0 a) (by positivity)
      positivity
    calc |dot e ((∫ x, heatKernel 0 ((n : ℝ) + 1) x • (a x).mulVec (correctedField S a e x)) -
          M.mulVec e) - (1 / 2 : ℝ) * ((∫ x, heatKernel 0 ((n : ℝ) + 1) x *
            dot (correctedField S a e x) ((a x).mulVec (correctedField S a e x))) -
              dot e (M.mulVec e))|
        ≤ |dot e ((∫ x, heatKernel 0 ((n : ℝ) + 1) x • (a x).mulVec (correctedField S a e x)) -
          M.mulVec e)| + (1 / 2 : ℝ) * |(∫ x, heatKernel 0 ((n : ℝ) + 1) x *
            dot (correctedField S a e x) ((a x).mulVec (correctedField S a e x))) -
              dot e (M.mulVec e)| := by
          refine (abs_sub _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      _ ≤ d * euclideanNorm e * (ε ((n : ℝ) + 1) * euclideanNorm e) +
          (1 / 2 : ℝ) * (2 * ε ((n : ℝ) + 1) * euclideanNorm e ^ 2) := by
          refine add_le_add (hd.trans ?_) (mul_le_mul_of_nonneg_left h3 (by norm_num))
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (d + 1) * ε ((n : ℝ) + 1) * euclideanNorm e ^ 2 := by ring

theorem ae_energyDensity_nonneg (S : HomogenizationData P) (e : Vec d)
    (a : CoefficientField d Λ) : ∀ᵐ x, 0 ≤ energyDensity S e a x := by
  filter_upwards [ae_energyDensity_eq S e a] with x hx
  rw [hx]
  exact (euclideanSq_nonneg _).trans (a.elliptic x _).1

theorem abs_dot_mulVec_le_half (a : CoefficientField d Λ) (x : Vec d) (u v : Vec d) :
    |dot u ((a x).mulVec v)| ≤
      (1 / 2 : ℝ) * (dot u ((a x).mulVec u) + dot v ((a x).mulVec v)) := by
  have h1 := dot_mulVec_add_eq a x u v
  have h2 := dot_mulVec_add_eq a x u (-v)
  have hp := (euclideanSq_nonneg (u + v)).trans (a.elliptic x (u + v)).1
  have hm := (euclideanSq_nonneg (u + -v)).trans (a.elliptic x (u + -v)).1
  have hneg : dot u ((a x).mulVec (-v)) = -dot u ((a x).mulVec v) := by
    simp [dot, Matrix.mulVec_neg]
  have hvv : dot (-v) ((a x).mulVec (-v)) = dot v ((a x).mulVec v) := by
    simp [dot, Matrix.mulVec_neg]
  rw [hneg, hvv] at h2
  rw [abs_le]
  constructor <;> nlinarith

/-- The constant of the energy envelope. -/
def energyEnvelopeConst (M : Mat d) (Cε : ℝ) (e : Vec d) : ℝ :=
  |dot e (M.mulVec e)| + 2 * ((d : ℝ) ^ 2 * Cε) * euclideanNorm e ^ 2

/-- **The energy envelope**: `∫ Φ_{0,r} G e · a G e ≤ K (1 + Y^d)` for every `r ≥ 1`. -/
theorem ae_energy_envelope (S : HomogenizationData P) {M : Mat d}
    {Y : CoefficientField d Λ → ℝ} {Cε θ : ℝ} (hCε : 0 ≤ Cε) (hθ : 0 < θ) (hY1 : ∀ a, 1 ≤ Y a)
    (hB : ∀ᵐ a ∂P, ∀ (r : ℝ) (x₀ : Vec d), Y a ≤ r → euclideanNorm x₀ ≤ r →
      GaussianBasisBounds a M (correctedCoordinate S a) x₀ r (Cε * (Y a / r) ^ θ)) (e : Vec d) :
    ∀ᵐ a ∂P, ∀ r : ℝ, 1 ≤ r →
      Integrable (fun x => heatKernel 0 r x * ‖energyDensity S e a x‖) ∧
        ∫ x, heatKernel 0 r x * ‖energyDensity S e a x‖ ≤
          energyEnvelopeConst M Cε e * (1 + Y a ^ d) := by
  have hY0 : ∀ a, 0 ≤ Y a := fun a => zero_le_one.trans (hY1 a)
  filter_upwards [ae_gaussianAverageBounds_origin S hCε hY0 hB] with a ha
  set K := energyEnvelopeConst M Cε e with hK
  have hK0 : 0 ≤ K := by
    rw [hK, energyEnvelopeConst]
    positivity
  have hnorm : ∀ r : ℝ, (fun x => heatKernel 0 r x * ‖energyDensity S e a x‖) =ᵐ[volume]
      fun x => heatKernel 0 r x *
        dot (correctedField S a e x) ((a x).mulVec (correctedField S a e x)) := by
    intro r
    filter_upwards [ae_energyDensity_nonneg S e a, ae_energyDensity_eq S e a] with x h0 hx
    rw [Real.norm_of_nonneg h0, hx]
  have hbig : ∀ R : ℝ, Y a ≤ R →
      Integrable (fun x => heatKernel 0 R x * ‖energyDensity S e a x‖) ∧
        ∫ x, heatKernel 0 R x * ‖energyDensity S e a x‖ ≤ K := by
    intro R hR
    obtain ⟨-, -, h3i, -, -, h3⟩ := ha R hR e
    refine ⟨h3i.congr (hnorm R).symm, ?_⟩
    rw [integral_congr_ae (hnorm R)]
    have hR0 : 0 < R := lt_of_lt_of_le one_pos ((hY1 a).trans hR)
    have hYR : (Y a / R) ^ θ ≤ 1 :=
      Real.rpow_le_one (div_nonneg (hY0 a) hR0.le) ((div_le_one hR0).mpr hR) hθ.le
    have h4 := (abs_le.mp h3).2
    have h5 : 2 * ((d : ℝ) ^ 2 * (Cε * (Y a / R) ^ θ)) * euclideanNorm e ^ 2 ≤
        2 * ((d : ℝ) ^ 2 * Cε) * euclideanNorm e ^ 2 := by
      have : Cε * (Y a / R) ^ θ ≤ Cε := mul_le_of_le_one_right hCε hYR
      gcongr
    have h6 := le_abs_self (dot e (M.mulVec e))
    rw [hK, energyEnvelopeConst]
    linarith
  intro r hr
  have hYd : 0 ≤ Y a ^ d := pow_nonneg (hY0 a) d
  by_cases hrY : Y a ≤ r
  · obtain ⟨h1, h2⟩ := hbig r hrY
    refine ⟨h1, h2.trans ?_⟩
    nlinarith
  · push Not at hrY
    have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
    obtain ⟨h1, h2⟩ := hbig (Y a) le_rfl
    have hcmp : ∀ x, heatKernel 0 r x * ‖energyDensity S e a x‖ ≤
        Y a ^ d * (heatKernel 0 (Y a) x * ‖energyDensity S e a x‖) := by
      intro x
      have hk := heatKernel_le_mul 0 hr0 hrY.le x
      have hq : (Y a / r) ^ d ≤ Y a ^ d :=
        pow_le_pow_left₀ (div_nonneg (hY0 a) hr0.le) (div_le_self (hY0 a) hr) d
      have hk' : heatKernel 0 r x ≤ Y a ^ d * heatKernel 0 (Y a) x :=
        hk.trans (mul_le_mul_of_nonneg_right hq (heatKernel_nonneg _ _ _))
      calc heatKernel 0 r x * ‖energyDensity S e a x‖
          ≤ (Y a ^ d * heatKernel 0 (Y a) x) * ‖energyDensity S e a x‖ :=
            mul_le_mul_of_nonneg_right hk' (norm_nonneg _)
        _ = _ := by ring
    have hmeas : AEStronglyMeasurable (fun x => heatKernel 0 r x * ‖energyDensity S e a x‖)
        volume :=
      ((measurable_heatKernel_fixed 0 r).mul ((measurable_energyDensity S e).comp
        (measurable_const.prodMk measurable_id)).norm).aestronglyMeasurable
    have hint : Integrable (fun x => heatKernel 0 r x * ‖energyDensity S e a x‖) :=
      (h1.const_mul (Y a ^ d)).mono' hmeas (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (mul_nonneg (heatKernel_nonneg _ _ _) (norm_nonneg _))]
        exact hcmp x)
    refine ⟨hint, ?_⟩
    calc ∫ x, heatKernel 0 r x * ‖energyDensity S e a x‖
        ≤ ∫ x, Y a ^ d * (heatKernel 0 (Y a) x * ‖energyDensity S e a x‖) :=
          integral_mono hint (h1.const_mul _) hcmp
      _ = Y a ^ d * ∫ x, heatKernel 0 (Y a) x * ‖energyDensity S e a x‖ := integral_const_mul _ _
      _ ≤ Y a ^ d * K := mul_le_mul_of_nonneg_left h2 hYd
      _ ≤ K * (1 + Y a ^ d) := by nlinarith

/-- **The envelope of the dual density.** -/
theorem ae_lowerDensity_envelope (S : HomogenizationData P) {M : Mat d}
    {Y : CoefficientField d Λ → ℝ} {Cε θ : ℝ} (hCε : 0 ≤ Cε) (hθ : 0 < θ) (hY1 : ∀ a, 1 ≤ Y a)
    (hB : ∀ᵐ a ∂P, ∀ (r : ℝ) (x₀ : Vec d), Y a ≤ r → euclideanNorm x₀ ≤ r →
      GaussianBasisBounds a M (correctedCoordinate S a) x₀ r (Cε * (Y a / r) ^ θ)) (e : Vec d) :
    ∀ᵐ a ∂P, ∀ r : ℝ, 1 ≤ r →
      Integrable (fun x => heatKernel 0 r x * ‖lowerDensity S e a x‖) ∧
        ∫ x, heatKernel 0 r x * ‖lowerDensity S e a x‖ ≤
          (1 / 2 : ℝ) * Λ * euclideanNorm e ^ 2 + energyEnvelopeConst M Cε e * (1 + Y a ^ d) := by
  filter_upwards [ae_energy_envelope S hCε hθ hY1 hB e] with a ha r hr
  obtain ⟨h1, h2⟩ := ha r hr
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hpt : ∀ᵐ x ∂(volume : Measure (Vec d)), heatKernel 0 r x * ‖lowerDensity S e a x‖ ≤
      (1 / 2 : ℝ) * Λ * euclideanNorm e ^ 2 * heatKernel 0 r x +
        heatKernel 0 r x * ‖energyDensity S e a x‖ := by
    filter_upwards [ae_lowerDensity_eq S e a, ae_energyDensity_eq S e a,
      ae_energyDensity_nonneg S e a] with x hx hE hE0
    rw [hx, Real.norm_eq_abs, Real.norm_of_nonneg hE0, hE]
    set G := correctedField S a e x
    have hcs := abs_dot_mulVec_le_half a x e G
    have hee : dot e ((a x).mulVec e) ≤ Λ * euclideanNorm e ^ 2 := by
      rw [← euclideanSq_eq_euclideanNorm_sq]
      exact (a.elliptic x e).2
    have hGG : 0 ≤ dot G ((a x).mulVec G) := (euclideanSq_nonneg _).trans (a.elliptic x _).1
    have habs : |dot e ((a x).mulVec G) - (1 / 2 : ℝ) * dot G ((a x).mulVec G)| ≤
        (1 / 2 : ℝ) * Λ * euclideanNorm e ^ 2 + dot G ((a x).mulVec G) := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_nonneg hGG]
      linarith
    have hk := heatKernel_nonneg 0 r x
    nlinarith
  have hmeas : AEStronglyMeasurable (fun x => heatKernel 0 r x * ‖lowerDensity S e a x‖) volume :=
    ((measurable_heatKernel_fixed 0 r).mul ((measurable_lowerDensity S e).comp
      (measurable_const.prodMk measurable_id)).norm).aestronglyMeasurable
  have hdom : Integrable fun x => (1 / 2 : ℝ) * Λ * euclideanNorm e ^ 2 * heatKernel 0 r x +
      heatKernel 0 r x * ‖energyDensity S e a x‖ :=
    ((integrable_heatKernel 0 hr0).const_mul _).add h1
  have hint : Integrable (fun x => heatKernel 0 r x * ‖lowerDensity S e a x‖) :=
    hdom.mono' hmeas (by
      filter_upwards [hpt] with x hx
      rw [Real.norm_of_nonneg (mul_nonneg (heatKernel_nonneg _ _ _) (norm_nonneg _))]
      exact hx)
  refine ⟨hint, ?_⟩
  calc ∫ x, heatKernel 0 r x * ‖lowerDensity S e a x‖
      ≤ ∫ x, ((1 / 2 : ℝ) * Λ * euclideanNorm e ^ 2 * heatKernel 0 r x +
          heatKernel 0 r x * ‖energyDensity S e a x‖) := integral_mono_ae hint hdom hpt
    _ = (1 / 2 : ℝ) * Λ * euclideanNorm e ^ 2 +
          ∫ x, heatKernel 0 r x * ‖energyDensity S e a x‖ := by
        rw [integral_add ((integrable_heatKernel 0 hr0).const_mul _) h1, integral_const_mul,
          integral_heatKernel 0 hr0, mul_one]
    _ ≤ _ := by linarith

/-- **The cell means of the energy density and of the dual density.** -/
theorem setIntegral_cell_energy_lowerDensity_eq [IsProbabilityMeasure P] (hP : LawHypotheses P)
    (S : HomogenizationData P) {M : Mat d} {Y : CoefficientField d Λ → ℝ}
    (hYd : Integrable (fun a => Y a ^ d) P) {Cε θ : ℝ} (hCε : 0 ≤ Cε) (hθ : 0 < θ)
    (hY1 : ∀ a, 1 ≤ Y a)
    (hB : ∀ᵐ a ∂P, ∀ (r : ℝ) (x₀ : Vec d), Y a ≤ r → euclideanNorm x₀ ≤ r →
      GaussianBasisBounds a M (correctedCoordinate S a) x₀ r (Cε * (Y a / r) ^ θ)) (e : Vec d) :
    (∫ x in latticeCell 1 (0 : LatticeIndex d), ∫ a, energyDensity S e a x ∂P) =
        dot e (M.mulVec e) ∧
      (∫ x in latticeCell 1 (0 : LatticeIndex d), ∫ a, lowerDensity S e a x ∂P) =
        (1 / 2 : ℝ) * dot e (M.mulVec e) := by
  have hY0 : ∀ a, 0 ≤ Y a := fun a => zero_le_one.trans (hY1 a)
  have hlim := ae_tendsto_energy_lowerDensity S hCε hθ hY0 hB e
  have hK : Integrable (fun a => energyEnvelopeConst M Cε e * (1 + Y a ^ d)) P :=
    ((integrable_const 1).add hYd).const_mul _
  constructor
  · exact setIntegral_cell_expectation_eq_of_tendsto hP.2.1
      (measurable_energyDensity S e).stronglyMeasurable (ae_energyDensity_add_latticeShift S e) hK
      (ae_energy_envelope S hCε hθ hY1 hB e) (hlim.mono fun a ha => ha.1)
  · exact setIntegral_cell_expectation_eq_of_tendsto hP.2.1
      (measurable_lowerDensity S e).stronglyMeasurable (ae_lowerDensity_add_latticeShift S e)
      ((integrable_const _).add hK) (ae_lowerDensity_envelope S hCε hθ hY1 hB e)
      (hlim.mono fun a ha => ha.2)

end QSH
