import QuantitativeStochasticHomogenization.Ch02.Sec02.SubcubeMeanGradient
import QuantitativeStochasticHomogenization.Ch02.Sec02.DualEnergyLocal
import QuantitativeStochasticHomogenization.Ch04.Sec04.LocalizationEstimateReduction

/-!
# The variance of a random vector and of averages over subcubes

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.2, the notation `var[X] = E|X - E[X]|²` for random vectors (`vecVariance`, with `E[X]`
taken componentwise) and Step 2 of the proof of Lemma 2.13:

* `var[X] ≤ E|X|²` (`vecVariance_le_integral_euclideanSq`) and, for `t > 0`,
  `var[X + Y] ≤ (1 + t) var[Y] + (1 + t⁻¹) var[X]` (`vecVariance_add_le`);
* for random vectors `Z_k` with `var[Z_k] = σ²`, `var[w Σ_k Z_k] ≤ w² N² σ²`, `N` the number of
  indices, and `var[w Σ_k Z_k] ≤ w² (N² - 2) σ²` if the components of two of them are independent
  (`vecVariance_smul_sum_le`, `vecVariance_smul_sum_le_of_indepFun`): the covariances are expanded as
  in the book, and each is at most `σ²`.
-/

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ}

section Variance

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The variance of a random vector**, `var[X] = E|X - E[X]|²`, with `E[X]` taken componentwise. -/
def vecVariance (P : Measure Ω) (X : Ω → Vec d) : ℝ :=
  ∑ i, ∫ ω, (X ω i - ∫ ω', X ω' i ∂P) ^ 2 ∂P

theorem vecVariance_nonneg (X : Ω → Vec d) : 0 ≤ vecVariance P X :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _

theorem sq_add_le_young (a b : ℝ) {t : ℝ} (ht : 0 < t) :
    (a + b) ^ 2 ≤ (1 + t) * b ^ 2 + (1 + t⁻¹) * a ^ 2 := by
  have h : 0 ≤ (a - t * b) ^ 2 := sq_nonneg _
  have e : (1 + t) * b ^ 2 + (1 + t⁻¹) * a ^ 2 - (a + b) ^ 2 = t⁻¹ * (a - t * b) ^ 2 := by
    field_simp
    ring
  have : 0 ≤ t⁻¹ * (a - t * b) ^ 2 := mul_nonneg (inv_nonneg.mpr ht.le) h
  linarith

variable [IsProbabilityMeasure P]

theorem memLp_two_of_bound {f : Ω → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ ω, f ω ^ 2 ≤ B) :
    MemLp f 2 P := by
  refine MemLp.of_bound hf.aestronglyMeasurable (Real.sqrt B) (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact Real.abs_le_sqrt (hB ω)

theorem integral_sq_sub_integral (f : Ω → ℝ) (hf : MemLp f 2 P) :
    ∫ ω, (f ω - ∫ ω', f ω' ∂P) ^ 2 ∂P = ∫ ω, f ω ^ 2 ∂P - (∫ ω, f ω ∂P) ^ 2 := by
  set m := ∫ ω, f ω ∂P with hm
  have hi : Integrable f P := hf.integrable one_le_two
  have hi2 : Integrable (fun ω => f ω ^ 2) P := hf.integrable_sq
  have e : (fun ω => (f ω - m) ^ 2) = fun ω => f ω ^ 2 + (-(2 * m) * f ω + m ^ 2) := by
    funext ω
    ring
  have i2 : Integrable (fun ω => -(2 * m) * f ω) P := hi.const_mul _
  have i1 : Integrable (fun ω => -(2 * m) * f ω + m ^ 2) P := i2.add (integrable_const _)
  rw [e, integral_add hi2 i1, integral_add i2 (integrable_const _), integral_const_mul,
    integral_const,
    probReal_univ, one_smul, ← hm]
  ring

/-- `var[X] ≤ E|X|²`. -/
theorem vecVariance_le_integral_euclideanSq {X : Ω → Vec d}
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 P) :
    vecVariance P X ≤ ∫ ω, euclideanSq (X ω) ∂P := by
  have e : ∫ ω, euclideanSq (X ω) ∂P = ∑ i, ∫ ω, X ω i ^ 2 ∂P := by
    simp only [euclideanSq, dot, ← sq]
    exact integral_finsetSum _ fun i _ => (hX i).integrable_sq
  rw [e]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [integral_sq_sub_integral _ (hX i)]
  linarith [sq_nonneg (∫ ω, X ω i ∂P)]

/-- **`var[X + Y] ≤ (1 + t) var[Y] + (1 + t⁻¹) var[X]`** for `t > 0`. -/
theorem vecVariance_add_le {X Y : Ω → Vec d} (hX : ∀ i, MemLp (fun ω => X ω i) 2 P)
    (hY : ∀ i, MemLp (fun ω => Y ω i) 2 P) {t : ℝ} (ht : 0 < t) :
    vecVariance P (fun ω => X ω + Y ω) ≤ (1 + t) * vecVariance P Y + (1 + t⁻¹) * vecVariance P X := by
  unfold vecVariance
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hXi : Integrable (fun ω => X ω i) P := (hX i).integrable one_le_two
  have hYi : Integrable (fun ω => Y ω i) P := (hY i).integrable one_le_two
  have hm : ∫ ω, (X ω + Y ω) i ∂P = ∫ ω, X ω i ∂P + ∫ ω, Y ω i ∂P := by
    simp only [Pi.add_apply]
    exact integral_add hXi hYi
  rw [hm]
  set mX := ∫ ω, X ω i ∂P
  set mY := ∫ ω, Y ω i ∂P
  have iX : Integrable (fun ω => (X ω i - mX) ^ 2) P := ((hX i).sub (memLp_const mX)).integrable_sq
  have iY : Integrable (fun ω => (Y ω i - mY) ^ 2) P := ((hY i).sub (memLp_const mY)).integrable_sq
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (iY.const_mul _) (iX.const_mul _)]
  refine integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
    ((iY.const_mul _).add (iX.const_mul _)) (Eventually.of_forall fun ω => ?_)
  have h := sq_add_le_young (X ω i - mX) (Y ω i - mY) ht
  simp only [Pi.add_apply]
  have e : X ω i + Y ω i - (mX + mY) = (X ω i - mX) + (Y ω i - mY) := by ring
  rw [e]
  exact h

/-- The covariance matrix trace `Σᵢ E[(Zᵢ - E Zᵢ)(Z'ᵢ - E Z'ᵢ)]` of two random vectors. -/
def vecCovariance (P : Measure Ω) (Z Z' : Ω → Vec d) : ℝ :=
  ∑ i, ∫ ω, (Z ω i - ∫ ω', Z ω' i ∂P) * (Z' ω i - ∫ ω', Z' ω' i ∂P) ∂P

theorem vecCovariance_le {Z Z' : Ω → Vec d} (hZ : ∀ i, MemLp (fun ω => Z ω i) 2 P)
    (hZ' : ∀ i, MemLp (fun ω => Z' ω i) 2 P) :
    vecCovariance P Z Z' ≤ (1 / 2 : ℝ) * vecVariance P Z + (1 / 2 : ℝ) * vecVariance P Z' := by
  unfold vecCovariance vecVariance
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  set m := ∫ ω, Z ω i ∂P
  set m' := ∫ ω, Z' ω i ∂P
  have h1 : MemLp (fun ω => Z ω i - m) 2 P := (hZ i).sub (memLp_const m)
  have h2 : MemLp (fun ω => Z' ω i - m') 2 P := (hZ' i).sub (memLp_const m')
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (h1.integrable_sq.const_mul _) (h2.integrable_sq.const_mul _)]
  refine integral_mono (h1.integrable_mul h2) ((h1.integrable_sq.const_mul _).add
    (h2.integrable_sq.const_mul _)) fun ω => ?_
  have := sq_nonneg ((Z ω i - m) - (Z' ω i - m'))
  show (Z ω i - m) * (Z' ω i - m') ≤
    (1 / 2 : ℝ) * (Z ω i - m) ^ 2 + (1 / 2 : ℝ) * (Z' ω i - m') ^ 2
  nlinarith

theorem vecCovariance_eq_zero_of_indepFun {Z Z' : Ω → Vec d}
    (hZm : ∀ i, Measurable fun ω => Z ω i) (hZ'm : ∀ i, Measurable fun ω => Z' ω i)
    (hZ : ∀ i, MemLp (fun ω => Z ω i) 2 P) (hZ' : ∀ i, MemLp (fun ω => Z' ω i) 2 P)
    (hind : ∀ i, IndepFun (fun ω => Z ω i) (fun ω => Z' ω i) P) :
    vecCovariance P Z Z' = 0 := by
  unfold vecCovariance
  refine Finset.sum_eq_zero fun i _ => ?_
  set m := ∫ ω, Z ω i ∂P
  set m' := ∫ ω, Z' ω i ∂P
  have hc : IndepFun (fun ω => Z ω i - m) (fun ω => Z' ω i - m') P :=
    (hind i).comp (measurable_id.sub_const m) (measurable_id.sub_const m')
  have h := hc.integral_mul_eq_mul_integral ((hZm i).sub_const m).aestronglyMeasurable
    ((hZ'm i).sub_const m').aestronglyMeasurable
  have h0 : ∫ ω, (Z ω i - m) ∂P = 0 := by
    rw [integral_sub ((hZ i).integrable one_le_two) (integrable_const m), integral_const,
      probReal_univ, one_smul, sub_self]
  simp only [Pi.mul_apply] at h
  rw [h, h0, zero_mul]

/-- `var[w Σ_k Z_k] = w² Σ_k Σ_l cov(Z_k, Z_l)`. -/
theorem vecVariance_smul_sum_eq {ι : Type*} [Fintype ι] {Z : ι → Ω → Vec d} (w : ℝ)
    (hZ : ∀ k i, MemLp (fun ω => Z k ω i) 2 P) :
    vecVariance P (fun ω => w • ∑ k, Z k ω) = w ^ 2 * ∑ k, ∑ l, vecCovariance P (Z k) (Z l) := by
  unfold vecVariance vecCovariance
  have hint : ∀ k i, Integrable (fun ω => Z k ω i) P := fun k i => (hZ k i).integrable one_le_two
  have hcomm : ∀ F : ι → ι → Fin d → ℝ, ∑ k, ∑ l, ∑ i, F k l i = ∑ i, ∑ k, ∑ l, F k l i :=
    fun F => by
      calc ∑ k, ∑ l, ∑ i, F k l i = ∑ k, ∑ i, ∑ l, F k l i :=
            Finset.sum_congr rfl fun k _ => Finset.sum_comm
        _ = ∑ i, ∑ k, ∑ l, F k l i := Finset.sum_comm
  rw [hcomm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hm : ∫ ω, (w • ∑ k, Z k ω) i ∂P = w * ∑ k, ∫ ω, Z k ω i ∂P := by
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [integral_const_mul, integral_finsetSum _ fun k _ => hint k i]
  rw [hm]
  have hc : ∀ k, MemLp (fun ω => Z k ω i - ∫ ω', Z k ω' i ∂P) 2 P := fun k =>
    (hZ k i).sub (memLp_const _)
  have hprod : ∀ k l, Integrable (fun ω => (Z k ω i - ∫ ω', Z k ω' i ∂P) *
      (Z l ω i - ∫ ω', Z l ω' i ∂P)) P := fun k l => (hc k).integrable_mul (hc l)
  have e : (fun ω => ((w • ∑ k, Z k ω) i - w * ∑ k, ∫ ω', Z k ω' i ∂P) ^ 2) = fun ω =>
      w ^ 2 * ∑ k, ∑ l, (Z k ω i - ∫ ω', Z k ω' i ∂P) * (Z l ω i - ∫ ω', Z l ω' i ∂P) := by
    funext ω
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [← mul_sub, ← Finset.sum_sub_distrib, mul_pow]
    congr 1
    rw [sq, Finset.sum_mul_sum]
  rw [e, integral_const_mul, integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
    hprod k l]
  congr 1
  exact Finset.sum_congr rfl fun k _ => integral_finsetSum _ fun l _ => hprod k l

/-- `var[w Σ_k Z_k] ≤ w² N² σ²` if `var[Z_k] = σ²` for every `k`. -/
theorem vecVariance_smul_sum_le {ι : Type*} [Fintype ι] {Z : ι → Ω → Vec d} (w : ℝ)
    (hZ : ∀ k i, MemLp (fun ω => Z k ω i) 2 P) {σ2 : ℝ} (hvar : ∀ k, vecVariance P (Z k) = σ2) :
    vecVariance P (fun ω => w • ∑ k, Z k ω) ≤ w ^ 2 * ((Fintype.card ι : ℝ) ^ 2 * σ2) := by
  rw [vecVariance_smul_sum_eq w hZ]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg w)
  have hb : ∀ k l, vecCovariance P (Z k) (Z l) ≤ σ2 := fun k l => by
    have := vecCovariance_le (hZ k) (hZ l)
    rw [hvar, hvar] at this
    linarith
  calc ∑ k, ∑ l, vecCovariance P (Z k) (Z l) ≤ ∑ _k : ι, ∑ _l : ι, σ2 :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hb k l
    _ = (Fintype.card ι : ℝ) ^ 2 * σ2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- `var[w Σ_k Z_k] ≤ w² (N² - 2) σ²` if `var[Z_k] = σ²` for every `k` and the components of
`Z_{k₀}` and `Z_{k₁}` are independent for some `k₀ ≠ k₁`. -/
theorem vecVariance_smul_sum_le_of_indepFun {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Z : ι → Ω → Vec d} (w : ℝ) (hZm : ∀ k i, Measurable fun ω => Z k ω i)
    (hZ : ∀ k i, MemLp (fun ω => Z k ω i) 2 P) {σ2 : ℝ} (hvar : ∀ k, vecVariance P (Z k) = σ2)
    {k₀ k₁ : ι} (hk : k₀ ≠ k₁) (hind : ∀ i, IndepFun (fun ω => Z k₀ ω i) (fun ω => Z k₁ ω i) P) :
    vecVariance P (fun ω => w • ∑ k, Z k ω) ≤ w ^ 2 * (((Fintype.card ι : ℝ) ^ 2 - 2) * σ2) := by
  rw [vecVariance_smul_sum_eq w hZ]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg w)
  set c : ι × ι → ℝ := fun kl => vecCovariance P (Z kl.1) (Z kl.2) with hcdef
  have hb : ∀ kl, c kl - σ2 ≤ 0 := fun kl => by
    have := vecCovariance_le (hZ kl.1) (hZ kl.2)
    rw [hvar, hvar] at this
    simp only [hcdef]
    linarith
  have h01 : c (k₀, k₁) = 0 :=
    vecCovariance_eq_zero_of_indepFun (hZm k₀) (hZm k₁) (hZ k₀) (hZ k₁) hind
  have h10 : c (k₁, k₀) = 0 :=
    vecCovariance_eq_zero_of_indepFun (hZm k₁) (hZm k₀) (hZ k₁) (hZ k₀) fun i => (hind i).symm
  set S : Finset (ι × ι) := {(k₀, k₁), (k₁, k₀)} with hS
  have hne : (k₀, k₁) ≠ (k₁, k₀) := fun h => hk (Prod.ext_iff.mp h).1
  have hSsum : ∑ kl ∈ S, (c kl - σ2) = -(2 * σ2) := by
    rw [hS, Finset.sum_pair hne, h01, h10]
    ring
  have hsplit := Finset.sum_sdiff (s₁ := S) (s₂ := Finset.univ) (f := fun kl => c kl - σ2)
    (Finset.subset_univ S)
  have hrest : ∑ kl ∈ Finset.univ \ S, (c kl - σ2) ≤ 0 := Finset.sum_nonpos fun kl _ => hb kl
  have htot : ∑ kl : ι × ι, (c kl - σ2) ≤ -(2 * σ2) := by
    rw [← hsplit, hSsum]
    linarith
  have hprod : ∑ k, ∑ l, vecCovariance P (Z k) (Z l) = ∑ kl : ι × ι, c kl := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
  rw [hprod]
  have e : ∑ kl : ι × ι, c kl = ∑ kl : ι × ι, (c kl - σ2) + (Fintype.card ι : ℝ) ^ 2 * σ2 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      nsmul_eq_mul]
    push_cast
    ring
  rw [e]
  linarith

end Variance

end QSH
