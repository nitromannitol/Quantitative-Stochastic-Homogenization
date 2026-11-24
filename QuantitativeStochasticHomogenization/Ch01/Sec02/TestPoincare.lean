import QuantitativeStochasticHomogenization.Ch01.Sec02.DirichletEnergyTests
import Homogenization.Sobolev.MatchedPair.ScaledPoincare

/-!
# The Poincaré inequality for the tests of a bounded set

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.2: the existence of the minimizer (1.8) and the proof of Proposition 1.8 use the
Poincaré inequality in `H¹₀`. For a smooth test `v` supported in the cube `□_R(z)`,
`∫ v² ≤ C R² ∫ |∇v|²` with `C` depending only on `d` (`integral_sq_le_of_isSpatialTest_cube`),
from the zero-trace Poincaré inequality on axis cubes of the coarse-graining library
(`Homogenization.scaled_dirichlet_poincare`). The inequality passes to the functions of `H¹₀(U)`
of (1.7) for `U ⊆ □_R(z)` (`setIntegral_sq_le_of_H01`).
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ}

open BaseExponent

/-- The cube `□_R(z)` is the axis cube with corner `z - R/2` and side `R`. -/
theorem cube_eq_axisCube (z : Vec d) (R : ℝ) :
    cube z R = _root_.Homogenization.axisCube (fun i => z i - R / 2) R := by
  ext x
  simp only [cube, _root_.Homogenization.axisCube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
    true_implies, Set.mem_Ioo, abs_lt]
  refine forall_congr' fun i => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem isOpen_cube (z : Vec d) (R : ℝ) : IsOpen (cube z R) := by
  rw [cube_eq_axisCube]
  exact _root_.Homogenization.isOpen_axisCube _ R

/-- The constant of the Poincaré inequality for the tests of a cube of side `1`. -/
def testPoincareConstant (d : ℕ) [NeZero d] : ℝ :=
  d * _root_.Homogenization.unitDirichletPoincareConst d ^ 2

theorem testPoincareConstant_nonneg (d : ℕ) [NeZero d] : 0 ≤ testPoincareConstant d := by
  unfold testPoincareConstant
  positivity

private theorem sq_toReal_eLpNorm_two {μ : Measure (Vec d)} {f : Vec d → ℝ} (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  have h1 : ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with x h1
    rw [h1]
    simp [pow_two]
  rw [← h1, Lp.norm_toLp]

/-- **The Poincaré inequality for the tests of a cube**: `∫ v² ≤ C R² ∫ |∇v|²` for a smooth test
`v` supported in `□_R(z)`. -/
theorem integral_sq_le_of_isSpatialTest_cube [NeZero d] (z : Vec d) {R : ℝ} (hR : 0 < R)
    {v : Vec d → ℝ} (hv : IsSpatialTest (cube z R) v) :
    ∫ x, v x ^ 2 ≤ testPoincareConstant d * R ^ 2 * ∫ x, euclideanSq (gradient v x) := by
  set c : Vec d := fun i => z i - R / 2
  set Q := _root_.Homogenization.axisCube c R
  have hQ : cube z R = Q := cube_eq_axisCube z R
  rw [hQ] at hv
  let w := _root_.Homogenization.H10Function.ofContDiff (_root_.Homogenization.isOpen_axisCube c R)
    hv.1 hv.2.1 hv.2.2
  have h := _root_.Homogenization.scaled_dirichlet_poincare c hR w
  set K := _root_.Homogenization.unitDirichletPoincareConst d
  have hK : 0 ≤ K := _root_.Homogenization.unitDirichletPoincareConst_nonneg d
  have hvQ : MemLp v 2 (volume.restrict Q) := hv.memLp_two _
  have hdQ : ∀ i, MemLp (fun x => coordinateDerivative i v x) 2 (volume.restrict Q) := fun i =>
    (MemLp.eval (hv.memLp_gradient (volume.restrict Q)) i)
  change (eLpNorm v 2 (volume.restrict Q)).toReal ≤ K * R *
    ∑ i : Fin d, (eLpNorm (fun x => coordinateDerivative i v x) 2 (volume.restrict Q)).toReal at h
  have hsupp : ∀ {f : Vec d → ℝ}, (∀ x, x ∉ Q → f x = 0) → ∫ x in Q, f x = ∫ x, f x :=
    fun hf => setIntegral_eq_integral_of_forall_compl_eq_zero hf
  have hv0 : ∀ x, x ∉ Q → v x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hv.2.2 h)
  have hdv0 : ∀ x, x ∉ Q → gradient v x = 0 := by
    intro x hx
    have hxs : x ∉ tsupport v := fun h => hx (hv.2.2 h)
    have h0 : fderiv ℝ v x = 0 := fderiv_of_notMem_tsupport ℝ hxs
    funext l
    simp [gradient, coordinateDerivative, h0]
  have hlhs : (eLpNorm v 2 (volume.restrict Q)).toReal ^ 2 = ∫ x, v x ^ 2 := by
    rw [sq_toReal_eLpNorm_two hvQ]
    exact hsupp fun x hx => by rw [hv0 x hx]; ring
  have hrhs : ∑ i : Fin d,
      (eLpNorm (fun x => coordinateDerivative i v x) 2 (volume.restrict Q)).toReal ^ 2 =
      ∫ x, euclideanSq (gradient v x) := by
    rw [Finset.sum_congr rfl fun i _ => sq_toReal_eLpNorm_two (hdQ i)]
    rw [← integral_finsetSum _ fun i _ => (hdQ i).integrable_sq]
    rw [hsupp fun x hx => by
      have hcd : ∀ i, coordinateDerivative i v x = 0 := fun i => congrFun (hdv0 x hx) i
      simp [hcd]]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [euclideanSq, dot, gradient, pow_two]
  set S := ∑ i : Fin d,
    (eLpNorm (fun x => coordinateDerivative i v x) 2 (volume.restrict Q)).toReal
  have hS : S ^ 2 ≤ d * ∑ i : Fin d,
      (eLpNorm (fun x => coordinateDerivative i v x) 2 (volume.restrict Q)).toReal ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
      (f := fun i => (eLpNorm (fun x => coordinateDerivative i v x) 2
        (volume.restrict Q)).toReal)
    simpa using this
  have h0 : 0 ≤ (eLpNorm v 2 (volume.restrict Q)).toReal := ENNReal.toReal_nonneg
  have hsq := pow_le_pow_left₀ h0 h 2
  rw [hlhs] at hsq
  rw [← hrhs]
  calc ∫ x, v x ^ 2 ≤ (K * R * S) ^ 2 := hsq
    _ = K ^ 2 * R ^ 2 * S ^ 2 := by ring
    _ ≤ K ^ 2 * R ^ 2 * (d * ∑ i : Fin d,
          (eLpNorm (fun x => coordinateDerivative i v x) 2 (volume.restrict Q)).toReal ^ 2) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = _ := by unfold testPoincareConstant; ring

/-- **The Poincaré inequality for the tests of a subset of a cube**. -/
theorem setIntegral_sq_le_of_isSpatialTest [NeZero d] {U : Set (Vec d)} (z : Vec d) {R : ℝ}
    (hR : 0 < R) (hU : U ⊆ cube z R) {v : Vec d → ℝ} (hv : IsSpatialTest U v) :
    ∫ x in U, v x ^ 2 ≤ testPoincareConstant d * R ^ 2 * ∫ x in U, euclideanSq (gradient v x) := by
  have hv' : IsSpatialTest (cube z R) v := ⟨hv.1, hv.2.1, hv.2.2.trans hU⟩
  have hv0 : ∀ x, x ∉ U → v x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hv.2.2 h)
  have hdv0 : ∀ x, x ∉ U → gradient v x = 0 := by
    intro x hx
    have hxs : x ∉ tsupport v := fun h => hx (hv.2.2 h)
    have h0 : fderiv ℝ v x = 0 := fderiv_of_notMem_tsupport ℝ hxs
    funext l
    simp [gradient, coordinateDerivative, h0]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hv0 x hx]; ring,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hdv0 x hx]; simp [euclideanSq, dot]]
  exact integral_sq_le_of_isSpatialTest_cube z hR hv'

/-- A bounded set lies in a cube centered at the origin. -/
theorem exists_subset_cube_of_isBounded {U : Set (Vec d)} (hU : Bornology.IsBounded U) :
    ∃ R : ℝ, 0 < R ∧ U ⊆ cube 0 R := by
  obtain ⟨r, hr⟩ := hU.subset_closedBall 0
  refine ⟨2 * (|r| + 1), by positivity, fun x hx i => ?_⟩
  have h1 : ‖x‖ ≤ r := by simpa using hr hx
  have h2 : |x i| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x i
  simp only [Pi.zero_apply, sub_zero]
  have : r ≤ |r| := le_abs_self r
  linarith

/-! ## Convergence of square integrals -/

/-- If `∫ (fₙ - f)² → 0` then `∫ fₙ² → ∫ f²`. -/
theorem tendsto_integral_sq_of_tendsto_integral_sq_sub {μ : Measure (Vec d)} {f : Vec d → ℝ}
    {F : ℕ → Vec d → ℝ} (hf : MemLp f 2 μ) (hF : ∀ n, MemLp (F n) 2 μ)
    (hlim : Tendsto (fun n => ∫ x, (F n x - f x) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, F n x ^ 2 ∂μ) atTop (𝓝 (∫ x, f x ^ 2 ∂μ)) := by
  have hnorm : ∀ {g : Vec d → ℝ} (hg : MemLp g 2 μ), ‖hg.toLp g‖ ^ 2 = ∫ x, g x ^ 2 ∂μ := by
    intro g hg
    rw [Lp.norm_toLp, sq_toReal_eLpNorm_two hg]
  have hconv : Tendsto (fun n => (hF n).toLp (F n)) atTop (𝓝 (hf.toLp f)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hd : ∀ n, ‖(hF n).toLp (F n) - hf.toLp f‖ =
        Real.sqrt (∫ x, (F n x - f x) ^ 2 ∂μ) := by
      intro n
      rw [← MemLp.toLp_sub]
      have h := hnorm ((hF n).sub hf)
      rw [← Real.sqrt_sq (norm_nonneg _), h]
      rfl
    simp_rw [hd]
    have := (Real.continuous_sqrt.tendsto 0).comp hlim
    rw [Real.sqrt_zero] at this
    exact this
  have h2 := (hconv.norm).pow 2
  rw [hnorm hf] at h2
  exact h2.congr fun n => hnorm (hF n)

/-- The `L²` distance of two square integrable functions. -/
theorem dist_toLp_eq_sqrt {μ : Measure (Vec d)} {f g : Vec d → ℝ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) :
    dist (hf.toLp f) (hg.toLp g) = Real.sqrt (∫ x, (f x - g x) ^ 2 ∂μ) := by
  rw [dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp, ← Real.sqrt_sq ENNReal.toReal_nonneg,
    sq_toReal_eLpNorm_two (hf.sub hg)]
  rfl

/-- **Completeness of `L²`**: if `∫ (Fₙ - Fₘ)² ≤ b N` for `n, m ≥ N` and `b N → 0`, there is
`f ∈ L²` with `∫ (Fₙ - f)² → 0`. -/
theorem exists_memLp_tendsto_integral_sq_sub {μ : Measure (Vec d)} {F : ℕ → Vec d → ℝ}
    (hF : ∀ n, MemLp (F n) 2 μ) (b : ℕ → ℝ)
    (hb : ∀ n m N, N ≤ n → N ≤ m → ∫ x, (F n x - F m x) ^ 2 ∂μ ≤ b N)
    (hb0 : Tendsto b atTop (𝓝 0)) :
    ∃ f : Vec d → ℝ, MemLp f 2 μ ∧ Tendsto (fun n => ∫ x, (F n x - f x) ^ 2 ∂μ) atTop (𝓝 0) := by
  set s : ℕ → Lp ℝ 2 μ := fun n => (hF n).toLp (F n)
  have hs : CauchySeq s := by
    refine cauchySeq_of_le_tendsto_0 (fun N => Real.sqrt (b N)) (fun n m N hn hm => ?_) ?_
    · rw [dist_toLp_eq_sqrt]
      exact Real.sqrt_le_sqrt (hb n m N hn hm)
    · have := (Real.continuous_sqrt.tendsto 0).comp hb0
      rw [Real.sqrt_zero] at this
      exact this
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hs
  refine ⟨L, Lp.memLp L, ?_⟩
  have hd : ∀ n, ∫ x, (F n x - L x) ^ 2 ∂μ = dist (s n) L ^ 2 := by
    intro n
    have h1 : (Lp.memLp L).toLp L = L := Lp.toLp_coeFn L (Lp.memLp L)
    have h2 : dist (s n) L = dist (s n) ((Lp.memLp L).toLp L) := by rw [h1]
    rw [h2, dist_toLp_eq_sqrt (hF n) (Lp.memLp L), Real.sq_sqrt (integral_nonneg fun x =>
      sq_nonneg _)]
  simp_rw [hd]
  have h2 := ((tendsto_iff_dist_tendsto_zero.mp hL).pow 2)
  rw [zero_pow two_ne_zero] at h2
  exact h2

/-- If `∫ (Fₙ - f)² → 0` then `∫ Fₙ h → ∫ f h` for `h ∈ L²`. -/
theorem tendsto_integral_mul_of_tendsto_integral_sq_sub {μ : Measure (Vec d)} {f h : Vec d → ℝ}
    {F : ℕ → Vec d → ℝ} (hf : MemLp f 2 μ) (hh : MemLp h 2 μ) (hF : ∀ n, MemLp (F n) 2 μ)
    (hlim : Tendsto (fun n => ∫ x, (F n x - f x) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, F n x * h x ∂μ) atTop (𝓝 (∫ x, f x * h x ∂μ)) := by
  have key : ∀ (g : Vec d → ℝ) (hg : MemLp g 2 μ),
      ∫ x, g x * h x ∂μ = inner ℝ (hg.toLp g) (hh.toLp h) := by
    intro g hg
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp, hh.coeFn_toLp] with x h1 h2
    rw [h1, h2]
    simp [mul_comm]
  have hconv : Tendsto (fun n => (hF n).toLp (F n)) atTop (𝓝 (hf.toLp f)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simp_rw [dist_toLp_eq_sqrt]
    have := (Real.continuous_sqrt.tendsto 0).comp hlim
    rw [Real.sqrt_zero] at this
    exact this
  have hlim' := Filter.Tendsto.inner (𝕜 := ℝ) hconv (tendsto_const_nhds (x := hh.toLp h))
  rw [← key f hf] at hlim'
  exact hlim'.congr fun n => (key (F n) (hF n)).symm

/-- **The Poincaré inequality in `H¹₀(U)`** for `U ⊆ □_R(z)`: `∫_U u² ≤ C R² ∫_U |∇u|²`. -/
theorem setIntegral_sq_le_of_H01 [NeZero d] {U : Set (Vec d)} (z : Vec d) {R : ℝ}
    (hR : 0 < R) (hU : U ⊆ cube z R) {u : Vec d → ℝ} {g : Vec d → Vec d} (hu : H01 U u g) :
    ∫ x in U, u x ^ 2 ≤ testPoincareConstant d * R ^ 2 * ∫ x in U, euclideanSq (g x) := by
  obtain ⟨hu2, hg2, -, v, hv, hconv, hgconv⟩ := hu
  have hvU : ∀ n, MemLp (v n) 2 (volume.restrict U) := fun n => (hv n).memLp_two _
  have hdvU : ∀ n, MemLp (gradient (v n)) 2 (volume.restrict U) := fun n =>
    (hv n).memLp_gradient _
  have t1 : Tendsto (fun n => ∫ x in U, v n x ^ 2) atTop (𝓝 (∫ x in U, u x ^ 2)) :=
    tendsto_integral_sq_of_tendsto_integral_sq_sub hu2 hvU hconv
  have hcoord : ∀ i, Tendsto (fun n => ∫ x in U, gradient (v n) x i ^ 2) atTop
      (𝓝 (∫ x in U, g x i ^ 2)) := by
    intro i
    refine tendsto_integral_sq_of_tendsto_integral_sq_sub (MemLp.eval hg2 i)
      (fun n => MemLp.eval (hdvU n) i) ?_
    refine squeeze_zero (fun n => integral_nonneg fun x => sq_nonneg _) (fun n => ?_) hgconv
    refine integral_mono ((MemLp.eval ((hdvU n).sub hg2) i).integrable_sq)
      (integrable_euclideanSq_of_memLp ((hdvU n).sub hg2)) fun x => ?_
    simp only [euclideanSq, dot]
    have := Finset.single_le_sum (f := fun j => (gradient (v n) x - g x) j *
      (gradient (v n) x - g x) j) (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
    simpa [pow_two] using this
  have hsum : ∀ (G : Vec d → Vec d), MemLp G 2 (volume.restrict U) →
      ∫ x in U, euclideanSq (G x) = ∑ i, ∫ x in U, G x i ^ 2 := by
    intro G hG
    rw [← integral_finsetSum _ fun i _ => (MemLp.eval hG i).integrable_sq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [euclideanSq, dot, pow_two]
  have t2 : Tendsto (fun n => ∫ x in U, euclideanSq (gradient (v n) x)) atTop
      (𝓝 (∫ x in U, euclideanSq (g x))) := by
    rw [hsum g hg2]
    refine (tendsto_finsetSum _ fun i _ => hcoord i).congr fun n => ?_
    rw [hsum _ (hdvU n)]
  exact le_of_tendsto_of_tendsto' t1 (t2.const_mul _) fun n =>
    setIntegral_sq_le_of_isSpatialTest z hR hU (hv n)

end QSH
