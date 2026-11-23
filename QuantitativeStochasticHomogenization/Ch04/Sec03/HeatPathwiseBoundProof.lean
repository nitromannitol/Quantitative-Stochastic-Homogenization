import QuantitativeStochasticHomogenization.Ch04.Sec03.HeatIdentityDeterministic
import QuantitativeStochasticHomogenization.Ch04.Sec03.Estimate558Pathwise
import QuantitativeStochasticHomogenization.Ch04.Opening.Theorem41Energy
import QuantitativeStochasticHomogenization.Ch04.Sec01.HomogenizedBoundsFromMeasurability
import QuantitativeStochasticHomogenization.Ch04.Sec06.NegativeSobolevLinearEstimates
import QuantitativeStochasticHomogenization.Ch05.Sec03.CoarsenedCoefficientEstimatesLiouville
import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicApproximationProof

/-!
# The pathwise heat bound for every law, and (5.58) without it

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, the heat identity (H) of the route of Proposition 4.10, and (5.58).

The homogenized matrix `ā` of homogenization data is symmetric with `1 ≤ ā ≤ Λ`; the rows of the
transposed eigenvector matrix give an orthogonal `Q` with `Q ā = diag(λ) Q`, `1 ≤ λ_k ≤ Λ`
(`exists_eigenframe`). Almost surely the corrector `φ_{eᵢ}` has the weak gradient `∇φ_{eᵢ}`, the flux
`a(eᵢ + ∇φ_{eᵢ})` is divergence-free, the corrected coordinate has finite Gaussian energy, and `φ_{eᵢ}`
is sublinear; these give the integrability against heat kernels required by `heatIdentity_bound`.
Hence, for every law satisfying the assumptions and all homogenization data, `HeatPathwiseBound`
holds with the explicit kernel `k(r, u, x) = (8Λ + 1) v⁻¹ (4πv)^{-d/2} e^{-|x|²/(16Λv)}`,
`v = max(u, 1)`, of mass `(8Λ + 1)(4Λ)^{d/2}/u` for `u ≥ 1` (`heatPathwiseBound_of_lawHypotheses`),
the sharp kernel `u⁻¹(1 + ½ x·E⁻¹x)G_E(x)` has mass `(d + 1)/u` (`exists_heatPathwiseKernel`,
`heatIdentityBound_succ_of_rate`), and (5.58) follows from Proposition 3.21, the measurability of `J₁`
and Propositions 4.11 and 4.12 (`estimate558_of_law`).
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology Matrix

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-! ## The eigenframe of a symmetric matrix -/

/-- **An orthonormal eigenframe** of a symmetric matrix with `1 ≤ A ≤ Λ`. -/
theorem exists_eigenframe {A : Mat d} (hsymm : A.transpose = A) {Λ : ℝ}
    (hA : HomogenizedMatrixBounds A Λ) :
    ∃ (Q : Mat d) (lam : Fin d → ℝ), Q.transpose * Q = 1 ∧
      (∀ v, Q *ᵥ (A *ᵥ v) = fun m => lam m * (Q *ᵥ v) m) ∧ ∀ k, 1 ≤ lam k ∧ lam k ≤ Λ := by
  have hH : A.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hsymm
  set U : Mat d := (hH.eigenvectorUnitary : Mat d) with hU
  have hUU : U * U.transpose = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hUU' : U.transpose * U = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hrow : ∀ (m : Fin d) (x : Vec d), (U.transpose *ᵥ x) m =
      (⇑(hH.eigenvectorBasis m) : Fin d → ℝ) ⬝ᵥ x := by
    intro m x
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hU,
      Matrix.IsHermitian.eigenvectorUnitary_apply]
  have heig : ∀ (m : Fin d) (v : Vec d), (⇑(hH.eigenvectorBasis m) : Fin d → ℝ) ⬝ᵥ (A *ᵥ v) =
      hH.eigenvalues m * ((⇑(hH.eigenvectorBasis m) : Fin d → ℝ) ⬝ᵥ v) := by
    intro m v
    rw [Matrix.dotProduct_mulVec]
    have hv : (⇑(hH.eigenvectorBasis m) : Fin d → ℝ) ᵥ* A = A *ᵥ ⇑(hH.eigenvectorBasis m) := by
      funext j
      simp only [Matrix.vecMul, Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h := congrFun (congrFun hsymm i) j
      rw [Matrix.transpose_apply] at h
      rw [← h]
      ring
    rw [hv, Matrix.IsHermitian.mulVec_eigenvectorBasis, smul_dotProduct, smul_eq_mul]
  have hnorm : ∀ m : Fin d, (⇑(hH.eigenvectorBasis m) : Fin d → ℝ) ⬝ᵥ
      (⇑(hH.eigenvectorBasis m) : Fin d → ℝ) = 1 := by
    intro m
    have h := congrFun (congrFun hUU' m) m
    simpa [Matrix.mul_apply, Matrix.transpose_apply, hU, Matrix.one_apply_eq, dotProduct] using h
  refine ⟨U.transpose, hH.eigenvalues, by rw [Matrix.transpose_transpose]; exact hUU, ?_, ?_⟩
  · intro v
    funext m
    rw [hrow, hrow, heig]
  · intro k
    have h := hA (⇑(hH.eigenvectorBasis k) : Fin d → ℝ)
    have hsq : euclideanSq (⇑(hH.eigenvectorBasis k) : Fin d → ℝ) = 1 := hnorm k
    have hdot : dot (⇑(hH.eigenvectorBasis k) : Fin d → ℝ) (A *ᵥ ⇑(hH.eigenvectorBasis k)) =
        hH.eigenvalues k := by
      change (⇑(hH.eigenvectorBasis k) : Fin d → ℝ) ⬝ᵥ (A *ᵥ ⇑(hH.eigenvectorBasis k)) = _
      rw [heig, hnorm, mul_one]
    rw [hsq, hdot, mul_one] at h
    exact h

/-! ## The kernel -/

/-- The kernel of `HeatPathwiseBound`: `k(r, u, x) = (8Λ + 1) v⁻¹ (4πv)^{-d/2} e^{-|x|²/(16Λv)}`,
`v = max(u, 1)`. -/
def heatPathwiseKernel (d : ℕ) (Λ : ℝ) (_r u : ℝ) (x : Vec d) : ℝ :=
  heatIdentityKernel d Λ (max u 1) x

theorem heatIdentityKernel_eq {u : ℝ} (hΛ : 0 < Λ) (hu : 0 < u) (x : Vec d) :
    heatIdentityKernel d Λ u x =
      (8 * Λ + 1) * (4 * Λ) ^ ((d : ℝ) / 2) * u⁻¹ * euclideanHeatKernel (4 * Λ * u) x := by
  unfold heatIdentityKernel euclideanHeatKernel
  have h1 : (4 * Real.pi * (4 * Λ * u)) ^ (-(d : ℝ) / 2) =
      (4 * Λ) ^ (-(d : ℝ) / 2) * (4 * Real.pi * u) ^ (-(d : ℝ) / 2) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    ring
  have h2 : (4 * Λ) ^ ((d : ℝ) / 2) * (4 * Λ) ^ (-(d : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add (by positivity), show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring,
      Real.rpow_zero]
  have h4 : -euclideanSq x / (16 * Λ * u) = -euclideanSq x / (4 * (4 * Λ * u)) := by ring
  rw [h1, h4]
  calc _ = (8 * Λ + 1) * u⁻¹ * ((4 * Real.pi * u) ^ (-(d : ℝ) / 2) *
        Real.exp (-euclideanSq x / (4 * (4 * Λ * u)))) *
          ((4 * Λ) ^ ((d : ℝ) / 2) * (4 * Λ) ^ (-(d : ℝ) / 2)) := by rw [h2, mul_one]
    _ = _ := by ring

theorem measurable_heatPathwiseKernel_uncurry (r : ℝ) :
    Measurable (Function.uncurry (heatPathwiseKernel d Λ r)) := by
  unfold Function.uncurry heatPathwiseKernel heatIdentityKernel euclideanSq dot
  fun_prop

theorem heatPathwiseKernel_pos (hΛ : 0 < Λ) (r u : ℝ) (x : Vec d) :
    0 < heatPathwiseKernel d Λ r u x := by
  have hv : 0 < max u 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  unfold heatPathwiseKernel heatIdentityKernel
  have : 0 < 8 * Λ + 1 := by linarith
  positivity

theorem heatPathwiseKernel_mass (hΛ : 0 < Λ) (r : ℝ) {u : ℝ} (hu : 1 ≤ u) :
    Integrable (heatPathwiseKernel d Λ r u) ∧
      ∫ x, heatPathwiseKernel d Λ r u x ≤ (8 * Λ + 1) * (4 * Λ) ^ ((d : ℝ) / 2) * u⁻¹ := by
  have hu0 : 0 < u := lt_of_lt_of_le one_pos hu
  have hm : max u 1 = u := max_eq_left hu
  have hfun : heatPathwiseKernel d Λ r u = fun x =>
      (8 * Λ + 1) * (4 * Λ) ^ ((d : ℝ) / 2) * u⁻¹ * euclideanHeatKernel (4 * Λ * u) x := by
    funext x
    rw [heatPathwiseKernel, hm, heatIdentityKernel_eq hΛ hu0]
  rw [hfun]
  refine ⟨(integrable_euclideanHeatKernel (by positivity)).const_mul _, le_of_eq ?_⟩
  rw [integral_const_mul, integral_euclideanHeatKernel (by positivity), mul_one]

/-! ## The pathwise bound -/

theorem heatKernel_eq_euclideanHeatKernel_sub (w : Vec d) (ρ : ℝ) (y : Vec d) :
    heatKernel w ρ y = euclideanHeatKernel (ρ ^ 2) (w - y) := by
  rw [heatKernel, show y - w = -(w - y) by abel, euclideanHeatKernel_neg]

/-- The components of the Gaussian averages of a vector field. -/
theorem integral_heatKernel_smul_apply {f : Vec d → Vec d}
    (hf : ∀ k, GaussianIntegrable (fun y => f y k)) (w : Vec d) {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (fun y => heatKernel w ρ y • f y) ∧
      ∀ j, (∫ y, heatKernel w ρ y • f y) j =
        ∫ y, euclideanHeatKernel (ρ ^ 2) (w - y) * f y j := by
  have hc : ∀ k, Integrable (fun y => (heatKernel w ρ y • f y) k) := fun k => by
    simp only [Pi.smul_apply, smul_eq_mul, heatKernel_eq_euclideanHeatKernel_sub]
    exact (hf k).integrable_heatKernel_mul (by positivity) w
  refine ⟨Integrable.of_eval hc, fun j => ?_⟩
  rw [eval_integral hc j]
  simp only [Pi.smul_apply, smul_eq_mul, heatKernel_eq_euclideanHeatKernel_sub]

theorem abs_apply_le_euclideanSq_add (v : Vec d) (k : Fin d) :
    |v k| ≤ euclideanSq v + 1 := by
  have h1 := abs_component_le_euclideanNorm v k
  have h2 : euclideanNorm v ^ 2 = euclideanSq v := euclideanNorm_sq_eq v
  nlinarith [sq_nonneg (euclideanNorm v - 1), BaseExponent.euclideanNorm_nonneg v]

/-- **The pathwise heat bound** for every law satisfying the assumptions, all homogenization
data with an eigenframe `(Q, λ)` of `ā`, and every kernel that bounds the Hessian term. -/
theorem heatPathwiseBound_of_kernel (hd : 2 ≤ d) (hΛ : 1 < Λ)
    {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P) (S : HomogenizationData P)
    {Q : Mat d} (hQ : Q.transpose * Q = 1) {lam : Fin d → ℝ}
    (hA : ∀ v, Q *ᵥ (S.homogenized *ᵥ v) = fun m => lam m * (Q *ᵥ v) m)
    (hlam : ∀ k, 1 ≤ lam k ∧ lam k ≤ Λ) {k : ℝ → ℝ → Vec d → ℝ}
    (hk : ∀ r : ℝ, 2 ≤ r → ∀ u : ℝ, r ^ 2 / 2 < u → ∀ w : Vec d, euclideanNorm w = 1 →
      ∀ C : Vec d → Vec d,
      ENNReal.ofReal |-2 * ∫ x, ∑ k, ∑ m, (Q *ᵥ w) k * (Q *ᵥ C x) m *
        anisoKernel (fun k => r ^ 2 + 2 * (u - r ^ 2 / 2) * lam k - u)
          (Pi.single k 1 + Pi.single m 1) (Q *ᵥ x)| ≤
        ∫⁻ x, ENNReal.ofReal (k r u x * euclideanNorm (C x))) :
    HeatPathwiseBound P S k := by
  have : IsProbabilityMeasure P := hP.1
  have hΛ0 : 0 < Λ := by linarith
  have hen := hasGaussianCorrectorEnergy_of_lawHypotheses hd hΛ hP S
  intro z r hr i
  filter_upwards [hen, (S.corrector (unitVector i)).weak_gradient,
    (S.corrector (unitVector i)).harmonic, (S.corrector (unitVector i)).locally_square_integrable,
    (S.corrector (unitVector i)).sublinear] with a hen' hgrad hdiv hloc hsub
  have hd0 : 0 < d := by omega
  have hr0 : 0 < r := by linarith
  have hgm : Measurable ((S.corrector (unitVector i)).grad a) :=
    (S.corrector (unitVector i)).measurable_grad.comp measurable_prodMk_left
  have hsqc : Continuous fun v : Vec d => euclideanSq v := by
    unfold euclideanSq dot
    fun_prop
  -- Gaussian integrability
  have hE : GaussianIntegrable (fun y =>
      euclideanSq (unitVector i + (S.corrector (unitVector i)).grad a y)) := by
    refine ⟨(hsqc.measurable.comp (measurable_const.add hgm)).aestronglyMeasurable,
      fun s hs x => ?_⟩
    have h := hen' i x (Real.sqrt s) (Real.sqrt_pos.mpr hs)
    refine h.congr (Eventually.of_forall fun y => ?_)
    simp only
    rw [heatKernel_eq_euclideanHeatKernel_sub, Real.sq_sqrt hs.le,
      abs_of_nonneg (BaseExponent.euclideanSq_nonneg _)]
  have hgI : ∀ k, GaussianIntegrable (fun y => (S.corrector (unitVector i)).grad a y k) := by
    intro k
    refine (hE.add (GaussianIntegrable.const 3)).mono
      (measurable_pi_iff.mp hgm k).aestronglyMeasurable fun y => ?_
    have h1 := abs_apply_le_euclideanSq_add (unitVector i + (S.corrector (unitVector i)).grad a y) k
    have h2 : |(unitVector (d := d) i) k| ≤ 1 := by
      unfold unitVector
      rw [Pi.single_apply]
      split_ifs <;> simp
    have h3 : (S.corrector (unitVector i)).grad a y k =
        (unitVector i + (S.corrector (unitVector i)).grad a y) k - (unitVector (d := d) i) k := by
      simp
    rw [abs_of_nonneg (add_nonneg (BaseExponent.euclideanSq_nonneg _) (by norm_num) :
      (0 : ℝ) ≤ euclideanSq (unitVector i + (S.corrector (unitVector i)).grad a y) + 3), h3]
    calc |(unitVector i + (S.corrector (unitVector i)).grad a y) k - (unitVector (d := d) i) k|
        ≤ |(unitVector i + (S.corrector (unitVector i)).grad a y) k| +
            |(unitVector (d := d) i) k| := abs_sub _ _
      _ ≤ _ := by linarith
  have hfI : ∀ k, GaussianIntegrable (fun y =>
      (a y *ᵥ (unitVector i + (S.corrector (unitVector i)).grad a y)) k) := by
    intro k
    refine ((hE.add (GaussianIntegrable.const 1)).const_mul Λ).mono
      (locallyIntegrableOn_univ.mp (hdiv.1 k)).aestronglyMeasurable fun y => ?_
    set v := unitVector i + (S.corrector (unitVector i)).grad a y with hv
    have h1 := abs_component_le_euclideanNorm (a y *ᵥ v) k
    have h2 := euclideanNorm_mulVec_le_mul_of_bounds hΛ0.le (a.symmetric y) (a.elliptic y) v
    have h3 : euclideanNorm v ≤ euclideanSq v + 1 := by
      have h4 : euclideanNorm v ^ 2 = euclideanSq v := euclideanNorm_sq_eq v
      nlinarith [sq_nonneg (euclideanNorm v - 1), BaseExponent.euclideanNorm_nonneg v]
    rw [abs_of_nonneg (mul_nonneg hΛ0.le (add_nonneg (BaseExponent.euclideanSq_nonneg _)
      zero_le_one) : (0 : ℝ) ≤ Λ * (euclideanSq v + 1))]
    calc |(a y *ᵥ v) k| ≤ Λ * euclideanNorm v := h1.trans h2
      _ ≤ Λ * (euclideanSq v + 1) := mul_le_mul_of_nonneg_left h3 hΛ0.le
  have hφm : AEStronglyMeasurable ((S.corrector (unitVector i)).potential a) volume :=
    (locallyIntegrableOn_univ.mp (hgrad ⟨0, hd0⟩).1).aestronglyMeasurable
  have hloc' : ∀ R : ℝ, 0 < R →
      MemLp ((S.corrector (unitVector i)).potential a) 2 (volume.restrict (ball 0 R)) :=
    fun R hR => (hloc R hR).1
  have hφI : GaussianIntegrable ((S.corrector (unitVector i)).potential a) :=
    ⟨hφm, fun s hs x => integrable_heatKernel_mul_abs_of_sublinear hφm hloc' hsub hs x⟩
  have hsubl : ∀ ε : ℝ, 0 < ε → ∃ S' : ℝ, 0 < S' ∧ ∀ s : ℝ, S' ≤ s → ∀ x : Vec d,
      euclideanNorm x ≤ Real.sqrt s →
        ∫ y, euclideanHeatKernel s (x - y) * |(S.corrector (unitVector i)).potential a y| ≤
          ε * Real.sqrt s := by
    intro ε hε
    obtain ⟨S', hS0, hS⟩ := exists_integral_heatKernel_mul_abs_le_of_sublinear hφm hloc' hsub hε
    exact ⟨S', hS0, fun s hs x hx => (hS s hs x hx).2⟩
  have hmain := heatIdentity_bound_of_kernel hQ hA hΛ.le hlam hgrad hdiv hgI hfI hφI hsubl z hr0
    (hk r hr)
  -- the left side
  have hEg : ∀ k, GaussianIntegrable (fun y =>
      (unitVector i + (S.corrector (unitVector i)).grad a y) k) := fun k =>
    (GaussianIntegrable.const _).add (hgI k)
  have hga : ∀ w ρ, gradientAverage S a w ρ (unitVector i) =
      ∫ y, heatKernel w ρ y • (unitVector i + (S.corrector (unitVector i)).grad a y) := by
    intro w ρ
    unfold gradientAverage
    simp only [correctedField_unitVector]
  have hfa : ∀ w ρ, fluxAverage S a w ρ (unitVector i) =
      ∫ y, heatKernel w ρ y • (a y *ᵥ (unitVector i + (S.corrector (unitVector i)).grad a y)) := by
    intro w ρ
    unfold fluxAverage
    simp only [correctedField_unitVector]
  have hL : gradientAverage S a z r (unitVector i) - unitVector i =
      fun j => ∫ y, euclideanHeatKernel (r ^ 2) (z - y) *
        (S.corrector (unitVector i)).grad a y j := by
    funext j
    rw [Pi.sub_apply, hga, (integral_heatKernel_smul_apply hEg z hr0).2 j]
    have hΦi : Integrable (fun y => euclideanHeatKernel (r ^ 2) (z - y)) :=
      (integrable_euclideanHeatKernel (by positivity)).comp_sub_left z
    have hΦ1 : ∫ y, euclideanHeatKernel (r ^ 2) (z - y) = 1 := by
      rw [integral_sub_left_eq_self (fun y => euclideanHeatKernel (r ^ 2) y) volume z]
      exact integral_euclideanHeatKernel (by positivity)
    simp only [Pi.add_apply, mul_add]
    rw [integral_add (hΦi.mul_const _) ((hgI j).integrable_heatKernel_mul (by positivity) z),
      integral_mul_const, hΦ1, one_mul]
    ring
  -- the right side
  have hR : ∀ u ∈ Ioi (r ^ 2 / 2), ∀ x : Vec d,
      ENNReal.ofReal (k r u x * euclideanNorm (fun j => ∫ y,
        euclideanHeatKernel u (z - x - y) * (a y *ᵥ (unitVector i +
          (S.corrector (unitVector i)).grad a y) - S.homogenized *ᵥ (unitVector i +
            (S.corrector (unitVector i)).grad a y)) j)) =
      ENNReal.ofReal (k r u x * commutatorNorm S a (z - x) (Real.sqrt u) i) := by
    intro u hu x
    have hu1 : 1 ≤ u := by
      have : r ^ 2 / 2 < u := hu
      nlinarith
    have hu0 : 0 < u := lt_of_lt_of_le one_pos hu1
    have hρ : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
    have hsq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0.le
    rw [commutatorNorm, hfa, hga]
    congr 3
    funext j
    have hfj := (integral_heatKernel_smul_apply hfI (z - x) hρ).2 j
    have hgj := (integral_heatKernel_smul_apply hEg (z - x) hρ).2
    have hK : ∀ k, Integrable (fun y => euclideanHeatKernel u (z - x - y) *
        (unitVector i + (S.corrector (unitVector i)).grad a y) k) := fun k =>
      (hEg k).integrable_heatKernel_mul hu0 (z - x)
    have hgvec : (∫ y, heatKernel (z - x) (Real.sqrt u) y •
        (unitVector i + (S.corrector (unitVector i)).grad a y)) =
        fun l => ∫ y, euclideanHeatKernel u (z - x - y) *
          (unitVector i + (S.corrector (unitVector i)).grad a y) l := by
      funext l
      rw [hgj l, hsq]
    rw [Pi.sub_apply, hfj, hgvec, hsq, mulVec_integral_apply S.homogenized hK j,
      ← integral_sub ((hfI j).integrable_heatKernel_mul hu0 (z - x))
        ((gaussianIntegrable_mulVec S.homogenized hEg j).integrable_heatKernel_mul hu0 (z - x))]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply, mul_sub]
  rw [hL]
  refine hmain.trans (le_of_eq ?_)
  exact setLIntegral_congr_fun measurableSet_Ioi fun u hu =>
    lintegral_congr fun x => hR u hu x

/-- **The pathwise heat bound** for every law satisfying the assumptions and all homogenization
data, with the kernel `heatPathwiseKernel d Λ` chosen before the law. -/
theorem heatPathwiseBound_of_lawHypotheses (hd : 2 ≤ d) (hΛ : 1 < Λ)
    {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P) (S : HomogenizationData P) :
    HeatPathwiseBound P S (heatPathwiseKernel d Λ) := by
  have : IsProbabilityMeasure P := hP.1
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨Q, lam, hQ, hA, hlam⟩ :=
    exists_eigenframe S.symmetric (S.homogenizedMatrixBounds hΛ0.le)
  refine heatPathwiseBound_of_kernel hd hΛ hP S hQ hA hlam ?_
  intro r hr u hu w hw C
  have hu1 : 1 ≤ u := by nlinarith
  have hu0 : 0 < u := lt_of_lt_of_le one_pos hu1
  have h := ofReal_abs_hessian_integral_le hQ hΛ.le hu0 (E := fun k =>
    r ^ 2 + 2 * (u - r ^ 2 / 2) * lam k - u) (fun k => by
      have h1 := hlam k
      have h2 : 0 ≤ 2 * u - r ^ 2 := by linarith
      constructor <;> nlinarith) hw C
  refine h.trans (le_of_eq (lintegral_congr fun x => ?_))
  rw [heatPathwiseKernel, max_eq_left hu1]

/-! ## The sharp kernel -/

theorem measurable_sharpHeatKernel_uncurry (Q : Mat d) (lam : Fin d → ℝ) (r : ℝ) :
    Measurable (Function.uncurry (sharpHeatKernel Q lam r)) := by
  have hT : Measurable fun p : ℝ × Vec d => sharpTimes lam r (max p.1 1) := by
    refine measurable_pi_iff.mpr fun k => ?_
    unfold sharpTimes
    fun_prop
  have hQx : Measurable fun p : ℝ × Vec d => Q *ᵥ p.2 :=
    (continuous_mulVec Q).measurable.comp measurable_snd
  have h1 := (measurable_anisoKernel_uncurry (0 : Fin d → ℕ)).comp (hT.prodMk hQx)
  show Measurable fun p : ℝ × Vec d => sharpHeatKernel Q lam r p.1 p.2
  unfold sharpHeatKernel
  refine Measurable.mul (by fun_prop) (Measurable.mul ?_ h1)
  exact measurable_const.add (measurable_const.mul (Finset.measurable_sum _ fun k _ =>
    (((measurable_pi_apply k).comp hQx).pow_const 2).div ((measurable_pi_apply k).comp hT)))

theorem sharpHeatKernel_pos {Q : Mat d} {lam : Fin d → ℝ} (hlam : ∀ k, 1 ≤ lam k) (r u : ℝ)
    (x : Vec d) : 0 < sharpHeatKernel Q lam r u x := by
  have hv : 1 ≤ max u 1 := le_max_right _ _
  have hT : ∀ k, 0 < sharpTimes lam r (max u 1) k := fun k =>
    lt_of_lt_of_le (by linarith) (sharpTimes_ge hlam r (max u 1) k)
  unfold sharpHeatKernel
  have h1 : 0 ≤ ∑ k, (Q *ᵥ x) k ^ 2 / sharpTimes lam r (max u 1) k :=
    Finset.sum_nonneg fun k _ => div_nonneg (sq_nonneg _) (hT k).le
  have h2 := anisoKernel_zero_pos hT (Q *ᵥ x)
  have h3 : 0 < (max u 1)⁻¹ := inv_pos.mpr (by linarith)
  positivity

theorem sharpHeatKernel_mass {Q : Mat d} (hQ : Q.transpose * Q = 1) {lam : Fin d → ℝ}
    (hlam : ∀ k, 1 ≤ lam k) (r : ℝ) {u : ℝ} (hu : 1 ≤ u) :
    Integrable (sharpHeatKernel Q lam r u) ∧
      ∫ x, sharpHeatKernel Q lam r u x = ((d : ℝ) + 1) * u⁻¹ := by
  set T := sharpTimes lam r (max u 1) with hTdef
  have hT : ∀ k, 0 < T k := fun k =>
    lt_of_lt_of_le (by linarith [le_max_right u 1]) (sharpTimes_ge hlam r (max u 1) k)
  set G : Vec d → ℝ := fun x' => anisoKernel T 0 x' +
    ∑ k, 1 / 2 * (T k)⁻¹ * (x' k ^ 2 * anisoKernel T 0 x') with hG
  have hGi : Integrable G := by
    refine (integrable_anisoKernel_zero hT).add (integrable_finsetSum _ fun k _ =>
      (integrable_sq_mul_anisoKernel_zero hT k).const_mul _)
  have hGint : ∫ x', G x' = (d : ℝ) + 1 := by
    rw [hG, integral_add (integrable_anisoKernel_zero hT) (integrable_finsetSum _ fun k _ =>
      (integrable_sq_mul_anisoKernel_zero hT k).const_mul _), integral_anisoKernel_zero hT,
      integral_finsetSum _ fun k _ => (integrable_sq_mul_anisoKernel_zero hT k).const_mul _]
    have : ∀ k, ∫ x', 1 / 2 * (T k)⁻¹ * (x' k ^ 2 * anisoKernel T 0 x') = 1 := fun k => by
      rw [integral_const_mul, integral_sq_mul_anisoKernel_zero hT k]
      have := (hT k).ne'
      field_simp
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring
  have hpt : ∀ x, sharpHeatKernel Q lam r u x = (max u 1)⁻¹ * G (Q *ᵥ x) := by
    intro x
    simp only [sharpHeatKernel, hG, ← hTdef, Finset.mul_sum]
    congr 1
    rw [add_mul, one_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  have hmp := measurePreserving_mulVec_of_orthogonal hQ
  have hGQ : Integrable (fun x => G (Q *ᵥ x)) :=
    (hmp.integrable_comp_emb (orthogonalHomeomorph hQ).measurableEmbedding).mpr hGi
  have hfun : sharpHeatKernel Q lam r u = fun x => (max u 1)⁻¹ * G (Q *ᵥ x) := funext hpt
  rw [hfun]
  refine ⟨hGQ.const_mul _, ?_⟩
  rw [integral_const_mul, integral_comp_mulVec_of_orthogonal hQ G, hGint, max_eq_left hu]
  ring

/-- **The pathwise heat bound with a kernel of mass `(d + 1)/u`** for every law satisfying the
assumptions and all homogenization data. -/
theorem exists_heatPathwiseKernel :
    ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∀ S : HomogenizationData P, ∃ k : ℝ → ℝ → Vec d → ℝ,
        (∀ r, Measurable (Function.uncurry (k r))) ∧ (∀ r u x, 0 < k r u x) ∧
        (∀ r u, 1 ≤ u → Integrable (k r u) ∧ ∫ x, k r u x ≤ ((d : ℝ) + 1) * u⁻¹) ∧
        HeatPathwiseBound P S k := by
  intro d hd Λ hΛ P hP S
  have : IsProbabilityMeasure P := hP.1
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨Q, lam, hQ, hA, hlam⟩ :=
    exists_eigenframe S.symmetric (S.homogenizedMatrixBounds hΛ0.le)
  have hlam1 : ∀ k, 1 ≤ lam k := fun k => (hlam k).1
  refine ⟨sharpHeatKernel Q lam, measurable_sharpHeatKernel_uncurry Q lam,
    sharpHeatKernel_pos hlam1, fun r u hu => ?_, ?_⟩
  · obtain ⟨hi, he⟩ := sharpHeatKernel_mass hQ hlam1 r hu
    exact ⟨hi, he.le⟩
  · refine heatPathwiseBound_of_kernel hd hΛ hP S hQ hA hlam ?_
    intro r hr u hu w hw C
    exact ofReal_abs_hessian_integral_le_sharp hQ hlam1 hu (by nlinarith) hw C

/-! ## (5.58) without the pathwise heat bound -/

section Estimate558

open BaseExponent

/-- **`HeatIdentityBound` with the constant `d + 1`** for every law satisfying the assumptions and
all homogenization data, given Proposition 3.21 at one exponent with a positive rate. -/
theorem heatIdentityBound_succ_of_rate (hd : 2 ≤ d) (hΛ : 1 < Λ)
    {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P) (S : HomogenizationData P)
    {τ C μ : ℝ} (hτ : 0 < τ) (hμ : 0 < μ) (hrate : GaussianCorrectorRate P S τ C μ) :
    HeatIdentityBound P S ((d : ℝ) + 1) := by
  have : IsProbabilityMeasure P := hP.1
  obtain ⟨k, hkm, hk0, hki, hpath⟩ := exists_heatPathwiseKernel d hd Λ hΛ P hP S
  exact heatIdentityBound_of_pathwise_of_rate S (by linarith) hkm hk0 hki hpath hτ hμ hrate

/-- **(5.58) and Theorem 4.6 (ii)** for a law satisfying (0.10)–(0.11), from Proposition 3.21 at
every exponent in `(0, d)`, the measurability of `J₁` and the conclusions of Propositions 4.11 and
4.12; the heat identity (H) is `heatPathwiseBound_of_lawHypotheses` and (4.12) is the first-order
Liouville theorem. -/
theorem estimate558_of_law {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hd : 2 ≤ d) (S : HomogenizationData P) (hΛ : 1 < Λ)
    (hrate : ∀ τ : ℝ, 0 < τ → τ < d → ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧
      GaussianCorrectorRate P S τ C μ)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J1Heat w.1 w.2 r p q)
    (h411 : LocalizationEstimates P localSigma J1Heat)
    (h412 : FluctuationEstimates P localSigma J1Heat) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    ExpectationJ1Estimate P S.homogenized d ∧
      ∃ C : ℝ, 0 < C ∧ ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
        euclideanNorm p < 1 → euclideanNorm q < 1 →
        OsBound P (fun a => |J1Heat a z r p q - homogenizedJ1 S.homogenized p q|) s
          (C * r ^ (-((d : ℝ) / 2))) := by
  have hΛ0 : 0 < Λ := by linarith
  have hspan := ae_gradientsOfA1AreCorrected_of_liouville firstOrderLiouville hd hΛ hP S
  exact estimate558_of_pathwise_and_law hP hd S hΛ0 hspan hrate hmeasJ
    (measurable_heatPathwiseKernel_uncurry (d := d) (Λ := Λ))
    (heatPathwiseKernel_pos hΛ0) (fun r u hu => heatPathwiseKernel_mass hΛ0 r hu)
    (heatPathwiseBound_of_lawHypotheses hd hΛ hP S) h411 h412 hs0 hs2

end Estimate558

end QSH
