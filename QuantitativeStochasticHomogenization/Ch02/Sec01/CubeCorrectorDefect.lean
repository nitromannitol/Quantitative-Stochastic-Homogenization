import QuantitativeStochasticHomogenization.Ch02.Sec01.CorrectorTrials
import QuantitativeStochasticHomogenization.Ch01.Sec03.Proposition18
import QuantitativeStochasticHomogenization.Ch04.Sec01.HomogenizedFluxIdentification

/-!
# The duality defect on triadic cubes from a family of correctors

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
toward Theorem 2.4. Let `F` be a family of first-order correctors `φᵢ` and skew flux correctors
`σᵢ` with homogenized matrix `D` whose oscillations on `B_r` are at most `C₁ r^{1 - μ}` for
`r ≥ R₀`, and let `|Dv|² ≤ B |v|²`. If `R₀ ≤ √d 3ⁿ`, then for every `p`
`J(□_n, p, Dp) ≤ K |p|² 3^{-2μn/3}` with `K` depending only on `d`, `Λ`, `C₁` and `B`
(`dualityDefect_triadicCube_le_of_family`).

The proof applies `dualityDefect_le_of_correctors` to the corrector `φ = Σᵢ pᵢ φᵢ` and the skew
field `σ = Σᵢ pᵢ σᵢ`, centered at their means on the ball `B_{√d 3ⁿ}` around `□_n`, with the inner
cutoff of `□_n` of relative width `τ = 3^{-2μn/3}/4`: the cutoff layer contributes `C τ` and the
oscillations `C τ⁻² 3^{-2μn}`. The means on the cube are bounded by the means on the ball
(`setAverage_triadicCube_sq_sub_le`).
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- The ratio `(√d)^d |B₁|` of the volumes of `B_{√d 3ⁿ}` and `□_n`. -/
def cubeBallRatio (d : ℕ) : ℝ :=
  Real.sqrt d ^ d * (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal

theorem cubeBallRatio_nonneg (d : ℕ) : 0 ≤ cubeBallRatio d := by
  unfold cubeBallRatio
  positivity

/-- **The mean square on a cube by the oscillation on the ball around it**: for `f ∈ L²(B_R)`
with `R = √d 3ⁿ`, `⨍_{□_n} |f - (f)_R|² ≤ (√d)^d |B₁| ⨍_{B_R} |f - (f)_R|²`. -/
theorem setAverage_triadicCube_sq_sub_le (hd : 1 ≤ d) (n : ℕ) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (ball 0 (cubeBallRadius d n)))) :
    ⨍ x in triadicCube d n, (f x - ⨍ y in ball 0 (cubeBallRadius d n), f y) ^ 2 ≤
      cubeBallRatio d * ballOscillation f (cubeBallRadius d n) := by
  set R := cubeBallRadius d n with hRdef
  have hR := cubeBallRadius_pos hd n
  set m := ⨍ y in ball 0 R, f y with hm
  set ω := (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal with hω
  have hω0 : 0 < ω :=
    ENNReal.toReal_pos (volume_euclideanBall_pos' one_pos).ne' (volume_euclideanBall_ne_top' 1)
  have hUB : triadicCube d n ⊆ ball 0 R := triadicCube_subset_ball hd n
  have hint : ∫ x in triadicCube d n, (f x - m) ^ 2 ≤ ∫ x in ball (0 : Vec d) R, (f x - m) ^ 2 :=
    setIntegral_mono_set ((hf.sub (memLp_const m)).integrable_sq)
      (Eventually.of_forall fun x => sq_nonneg _) (Eventually.of_forall hUB)
  have hball : ∫ x in ball (0 : Vec d) R, (f x - m) ^ 2 = R ^ d * ω * ballOscillation f R := by
    have hpos : 0 < R ^ d * ω := by positivity
    have h1 : ballOscillation f R = (R ^ d * ω)⁻¹ * ∫ x in ball (0 : Vec d) R, (f x - m) ^ 2 := by
      unfold ballOscillation
      rw [setAverage_eq, smul_eq_mul, volume_real_ball hR]
    rw [h1, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
  have hRd : R ^ d = Real.sqrt d ^ d * ((3 : ℝ) ^ n) ^ d := by
    rw [hRdef, cubeBallRadius, mul_pow]
  rw [setAverage_eq, smul_eq_mul, volumeReal_triadicCube]
  have h3 : (0 : ℝ) < ((3 : ℝ) ^ n) ^ d := by positivity
  rw [inv_mul_le_iff₀ h3]
  calc ∫ x in triadicCube d n, (f x - m) ^ 2 ≤ R ^ d * ω * ballOscillation f R :=
        hint.trans hball.le
    _ = ((3 : ℝ) ^ n) ^ d * (cubeBallRatio d * ballOscillation f R) := by
        rw [hRd, cubeBallRatio]
        ring

theorem mulVec_apply_eq_sum_mul_unitVector (A : Mat d) (p : Vec d) (j : Fin d) :
    A.mulVec p j = ∑ i, p i * A.mulVec (unitVector i) j := by
  conv_lhs => rw [← sum_smul_unitVector_eq p]
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The square of an oscillation bound: if `0 ≤ x ≤ C₁ R^{1-μ}`, `C₁ ≥ 0`, `R ≥ 3ⁿ ≥ 1` and
`μ ≥ 0`, then `x² ≤ C₁² R² ρ⁶` with `ρ = (3ⁿ)^{-μ/3}`. -/
theorem sq_le_of_le_rpow_one_sub {x C₁ R μ : ℝ} {n : ℕ} (hx : 0 ≤ x) (hC₁ : 0 ≤ C₁)
    (hR : (3 : ℝ) ^ n ≤ R) (hμ : 0 ≤ μ) (h : x ≤ C₁ * R ^ (1 - μ)) :
    x ^ 2 ≤ C₁ ^ 2 * R ^ 2 * (((3 : ℝ) ^ n) ^ (-(μ / 3))) ^ 6 := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hR0 : 0 < R := h3.trans_le hR
  have hρ : (((3 : ℝ) ^ n) ^ (-(μ / 3))) ^ 3 = ((3 : ℝ) ^ n) ^ (-μ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h3.le]
    congr 1
    push_cast
    ring
  have hsplit : R ^ (1 - μ) = R * R ^ (-μ) := by
    rw [sub_eq_add_neg, Real.rpow_add hR0, Real.rpow_one]
  have hle : R ^ (-μ) ≤ ((3 : ℝ) ^ n) ^ (-μ) :=
    Real.rpow_le_rpow_of_nonpos h3 hR (by linarith)
  have hRμ0 : 0 ≤ R ^ (-μ) := Real.rpow_nonneg hR0.le _
  have hb : x ≤ C₁ * R * (((3 : ℝ) ^ n) ^ (-(μ / 3))) ^ 3 := by
    rw [hρ]
    calc x ≤ C₁ * R ^ (1 - μ) := h
      _ = C₁ * R * R ^ (-μ) := by rw [hsplit]; ring
      _ ≤ C₁ * R * ((3 : ℝ) ^ n) ^ (-μ) :=
          mul_le_mul_of_nonneg_left hle (mul_nonneg hC₁ hR0.le)
  calc x ^ 2 ≤ (C₁ * R * (((3 : ℝ) ^ n) ^ (-(μ / 3))) ^ 3) ^ 2 := pow_le_pow_left₀ hx hb 2
    _ = C₁ ^ 2 * R ^ 2 * (((3 : ℝ) ^ n) ^ (-(μ / 3))) ^ 6 := by ring

/-- The constant `K(d, Λ, C₁, B)` of `dualityDefect_triadicCube_le_of_family`. -/
def cubeCorrectorConst (d : ℕ) (Λ C₁ B : ℝ) : ℝ :=
  3 / 2 * (d * (Λ ^ 2 + B) +
    16 * (Λ ^ 2 + 1) * cutoffGradConst d * cubeBallRatio d * (d : ℝ) ^ 2 * C₁ ^ 2)

/-- **The duality defect on a triadic cube from a family of correctors**: if the family `F` has
homogenized matrix `D` with `|Dv|² ≤ B |v|²`, oscillations at most `C₁ r^{1 - μ}` on `B_r` for
`r ≥ R₀`, and `R₀ ≤ √d 3ⁿ`, then `J(□_n, p, Dp) ≤ K |p|² ((3ⁿ)^{-μ/3})²`. -/
theorem dualityDefect_triadicCube_le_of_family (hd : 1 ≤ d) (a : CoefficientField d Λ)
    {D : Mat d} {μ C₁ R₀ : ℝ} (F : SublinearCorrectorFamily a D μ C₁ R₀) (hμ : 0 < μ)
    (hC₁ : 0 ≤ C₁) {B : ℝ} (hB : ∀ v : Vec d, euclideanSq (D.mulVec v) ≤ B * euclideanSq v)
    {n : ℕ} (hn : R₀ ≤ cubeBallRadius d n) (p : Vec d) :
    dualityDefect a (triadicCube d n) p (D.mulVec p) ≤
      cubeCorrectorConst d Λ C₁ B * euclideanSq p * (((3 : ℝ) ^ n) ^ (-(μ / 3))) ^ 2 := by
  haveI : NeZero d := ⟨by omega⟩
  set R := cubeBallRadius d n with hRdef
  have hR := cubeBallRadius_pos hd n
  set U := triadicCube d n with hUdef
  have hU := isOpenBoundedConvexDomain_triadicCube (d := d) n
  have hUB : U ⊆ ball 0 R := triadicCube_subset_ball hd n
  have hUfin : volume U ≠ ⊤ := volume_triadicCube_ne_top d n
  haveI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUfin
  have hne : U.Nonempty := ⟨0, mem_triadicCube_iff.mpr fun i => by simp⟩
  have hΛ : 0 < Λ := zero_lt_one.trans_le (one_le_of_coefficientField a)
  -- the exponent and the width of the cutoff
  set ρ : ℝ := ((3 : ℝ) ^ n) ^ (-(μ / 3)) with hρdef
  have h3n : (1 : ℝ) ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have h3n0 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos h3n0 _
  have hρ1 : ρ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h3n (by linarith)
  set τ := ρ ^ 2 / 4 with hτdef
  have hτ : 0 < τ := by positivity
  have hτ' : τ ≤ 1 / 4 := by
    rw [hτdef]
    have : ρ ^ 2 ≤ 1 := pow_le_one₀ hρ0.le hρ1
    linarith
  set η := innerCubeCutoff (_root_.Homogenization.originCube d (n : ℤ)) τ with hη
  have hηs := innerCubeCutoff_smooth (_root_.Homogenization.originCube d (n : ℤ)) hτ hτ'
  have hηc := innerCubeCutoff_hasCompactSupport (_root_.Homogenization.originCube d (n : ℤ)) hτ hτ'
  have hηU := tsupport_innerCubeCutoff_subset_triadicCube (d := d) n hτ hτ'
  -- the combinations of the correctors
  set φ : Vec d → ℝ := fun x => ∑ i, p i * F.φ i x with hφdef
  set gφ : Vec d → Vec d := fun x => ∑ i, p i • F.gφ i x with hgφdef
  set σ : Fin d → Fin d → Vec d → ℝ := fun j k x => ∑ i, p i * F.σ i x j k with hσdef
  set gσ : Fin d → Fin d → Vec d → Vec d := fun j k x => ∑ i, p i • F.gσ i j k x with hgσdef
  set m := ⨍ y in ball 0 R, φ y with hm
  set c : Fin d → Fin d → ℝ := fun j k => ⨍ y in ball 0 R, σ j k y with hc
  have hl := fun i => F.memLp i R hR
  have hφB : MemLp φ 2 (volume.restrict (ball 0 R)) :=
    memLp_finsetSum _ fun i _ => (hl i).1.const_mul (p i)
  have hσB : ∀ j k, MemLp (σ j k) 2 (volume.restrict (ball 0 R)) := fun j k =>
    memLp_finsetSum _ fun i _ => ((hl i).2.2 j k).1.const_mul (p i)
  have hφU : MemLp φ 2 (volume.restrict U) := hφB.mono_measure (Measure.restrict_mono hUB le_rfl)
  have hσU : ∀ j k, MemLp (σ j k) 2 (volume.restrict U) := fun j k =>
    (hσB j k).mono_measure (Measure.restrict_mono hUB le_rfl)
  have hgφU : ∀ l, MemLp (fun x => gφ x l) 2 (volume.restrict U) := fun l => by
    have e : (fun x => gφ x l) = fun x => ∑ i, p i * F.gφ i x l := by
      funext x
      simp only [hgφdef, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact memLp_finsetSum _ fun i _ =>
      ((MemLp.eval (hl i).2.1 l).mono_measure (Measure.restrict_mono hUB le_rfl)).const_mul
        (p i)
  have hgσU : ∀ j k l, MemLp (fun x => gσ j k x l) 2 (volume.restrict U) := fun j k l => by
    have e : (fun x => gσ j k x l) = fun x => ∑ i, p i * F.gσ i j k x l := by
      funext x
      simp only [hgσdef, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact memLp_finsetSum _ fun i _ =>
      ((MemLp.eval ((hl i).2.2 j k).2 l).mono_measure
        (Measure.restrict_mono hUB le_rfl)).const_mul (p i)
  have hwφ : HasWeakGradient U φ gφ :=
    (HasWeakGradient.finsetSum Finset.univ p fun i _ => F.weak_gradient_φ i).mono_univ
  have hwσ : ∀ j k, HasWeakGradient U (σ j k) (gσ j k) := fun j k =>
    (HasWeakGradient.finsetSum Finset.univ p fun i _ => F.weak_gradient_σ i j k).mono_univ
  have hskew : ∀ j k x, σ k j x = -σ j k x := fun j k x => by
    simp only [hσdef, ← Finset.sum_neg_distrib, ← mul_neg]
    exact Finset.sum_congr rfl fun i _ => by rw [F.skew i x k j]
  have hcskew : ∀ j k, c k j = -c j k := fun j k => by
    simp only [hc]
    rw [← average_neg]
    congr 1
    funext y
    exact hskew j k y
  -- the row divergence of the skew field
  have hflux : ∀ j, ∀ᵐ x ∂(volume.restrict U),
      ∑ k, skewGrad gσ j k x k = (a x).mulVec (p + gφ x) j - D.mulVec p j := fun j => by
    have hi : ∀ i, ∀ᵐ x ∂(volume : Measure (Vec d)), ∑ k, skewGrad (F.gσ i) j k x k =
        (a x).mulVec (unitVector i + F.gφ i x) j - D.mulVec (unitVector i) j := fun i =>
      ae_sum_skewGrad_eq (σ := fun j k x => F.σ i x j k) (gσ := F.gσ i)
        (fun j k => F.weak_gradient_σ i j k) (fun j k x => F.skew i x k j)
        (f := fun j x => (a x).mulVec (unitVector i + F.gφ i x) j - D.mulVec (unitVector i) j)
        (fun j => F.flux i j) j
    filter_upwards [ae_restrict_of_ae (ae_all_iff.mpr hi)] with x hx
    have e1 : ∀ k, skewGrad gσ j k x k = ∑ i, p i * skewGrad (F.gσ i) j k x k := fun k => by
      simp only [skewGrad, hgσdef, Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul]
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : (a x).mulVec (gφ x) j = ∑ i, p i * (a x).mulVec (F.gφ i x) j := by
      simp only [hgφdef, Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
    calc ∑ k, skewGrad gσ j k x k = ∑ i, p i * ∑ k, skewGrad (F.gσ i) j k x k := by
          simp only [e1, Finset.mul_sum]
          exact Finset.sum_comm
      _ = ∑ i, p i * ((a x).mulVec (unitVector i + F.gφ i x) j - D.mulVec (unitVector i) j) :=
          Finset.sum_congr rfl fun i _ => by rw [hx i]
      _ = (a x).mulVec (p + gφ x) j - D.mulVec p j := by
          rw [Matrix.mulVec_add, Pi.add_apply, mulVec_apply_eq_sum_mul_unitVector (a x) p j,
            mulVec_apply_eq_sum_mul_unitVector D p j, e2, ← Finset.sum_add_distrib,
            ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Matrix.mulVec_add, Pi.add_apply]
          ring
  have hJ := dualityDefect_le_of_correctors a hU.1 (isBounded_triadicCube n) hU.2.2 hne hU D p
    hφU hgφU hwφ m hσU hgσU hwσ hskew c hcskew hflux hηs hηc hηU
  -- the bound of the trial error
  have hG := euclideanSq_gradient_innerCubeCutoff_le (d := d) n hτ hτ'
  set G := cutoffGradConst d / τ ^ 2 / ((3 : ℝ) ^ n) ^ 2 with hGdef
  have hG0 : 0 ≤ G := by
    rw [hGdef, cutoffGradConst]
    positivity
  have hT := setAverage_trialError_le a hUfin D p hφU m hσU c hηs.continuous
    (innerCubeCutoff_nonneg _ _) (innerCubeCutoff_le_one _ _) hG
  -- the cutoff layer
  have hA1 := setAverage_sq_one_sub_innerCubeCutoff_le (d := d) n hτ hτ'
  have hA10 : 0 ≤ ⨍ x in U, (1 - η x) ^ 2 := by
    rw [setAverage_eq, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr measureReal_nonneg) (integral_nonneg fun _ => sq_nonneg _)
  -- the oscillations
  have h3R : (3 : ℝ) ^ n ≤ R := by
    rw [hRdef, cubeBallRadius]
    exact le_mul_of_one_le_left h3n0.le (Real.one_le_sqrt.mpr (by exact_mod_cast hd))
  set q2 := C₁ ^ 2 * R ^ 2 * ρ ^ 6 with hq2def
  have hbo : ∀ f : Vec d → ℝ, ballOscillation f R =
      scalarRms volume (ball 0 R) (fun x => f x - ⨍ y in ball 0 R, f y) ^ 2 := fun f => by
    rw [show scalarRms volume (ball 0 R) (fun x => f x - ⨍ y in ball 0 R, f y) =
      Real.sqrt (ballOscillation f R) from rfl, Real.sq_sqrt (ballOscillation_nonneg f R)]
  have hosc := fun i => F.oscillation i R hn
  have hS0 : ∀ i, 0 ≤ ∑ j, ∑ k, scalarRms volume (ball 0 R)
      (fun x => F.σ i x j k - ⨍ y in ball 0 R, F.σ i y j k) := fun i =>
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => Real.sqrt_nonneg _
  have hφi : ∀ i, ballOscillation (F.φ i) R ≤ q2 := fun i => by
    rw [hbo]
    exact sq_le_of_le_rpow_one_sub (Real.sqrt_nonneg _) hC₁ h3R hμ.le
      ((le_add_of_nonneg_right (hS0 i)).trans (hosc i))
  have hσi : ∀ i, ∑ j, ∑ k, ballOscillation (fun x => F.σ i x j k) R ≤ q2 := fun i => by
    simp only [hbo]
    have hS := sq_le_of_le_rpow_one_sub (hS0 i) hC₁ h3R hμ.le
      ((le_add_of_nonneg_left (Real.sqrt_nonneg _)).trans (hosc i))
    refine le_trans ?_ hS
    refine (Finset.sum_le_sum fun j _ => Finset.sum_sq_le_sq_sum_of_nonneg
      fun k _ => Real.sqrt_nonneg _).trans ?_
    exact Finset.sum_sq_le_sq_sum_of_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => Real.sqrt_nonneg _
  have hpsq : ∑ i, p i ^ 2 = euclideanSq p := by
    unfold euclideanSq dot
    exact Finset.sum_congr rfl fun i _ => sq _
  have hp0 : 0 ≤ euclideanSq p := euclideanSq_nonneg p
  have hr0 := cubeBallRatio_nonneg d
  have hA2 : ⨍ x in U, (φ x - m) ^ 2 ≤ cubeBallRatio d * (d * euclideanSq p * q2) := by
    refine (setAverage_triadicCube_sq_sub_le hd n hφB).trans
      (mul_le_mul_of_nonneg_left ?_ hr0)
    refine (ballOscillation_finsetSum_le p fun i => (hl i).1).trans ?_
    rw [Fintype.card_fin, mul_assoc, ← hpsq, Finset.sum_mul]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hφi i) (sq_nonneg _)) (Nat.cast_nonneg d)
  have hσint : ∀ j k, Integrable (fun x => (σ j k x - c j k) ^ 2) (volume.restrict U) :=
    fun j k => ((hσU j k).sub (memLp_const (c j k))).integrable_sq
  have hA3 : ⨍ x in U, ∑ j, ∑ k, (σ j k x - c j k) ^ 2 ≤
      cubeBallRatio d * (d * euclideanSq p * q2) := by
    have hcube : ⨍ x in U, ∑ j, ∑ k, (σ j k x - c j k) ^ 2 ≤
        cubeBallRatio d * ∑ j, ∑ k, ballOscillation (σ j k) R := by
      rw [setAverage_eq, smul_eq_mul, integral_finsetSum _ fun j _ =>
        integrable_finsetSum _ fun k _ => hσint j k, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [integral_finsetSum _ fun k _ => hσint j k, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      have h := setAverage_triadicCube_sq_sub_le hd n (hσB j k)
      rw [setAverage_eq, smul_eq_mul] at h
      exact h
    refine hcube.trans (mul_le_mul_of_nonneg_left ?_ hr0)
    have hjk : ∀ j k, ballOscillation (σ j k) R ≤
        d * ∑ i, p i ^ 2 * ballOscillation (fun x => F.σ i x j k) R := fun j k => by
      have h := ballOscillation_finsetSum_le p (f := fun i x => F.σ i x j k)
        fun i => ((hl i).2.2 j k).1
      rw [Fintype.card_fin] at h
      exact h
    calc ∑ j, ∑ k, ballOscillation (σ j k) R
        ≤ ∑ j, ∑ k, (d * ∑ i, p i ^ 2 * ballOscillation (fun x => F.σ i x j k) R) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hjk j k
      _ = d * ∑ i, p i ^ 2 * ∑ j, ∑ k, ballOscillation (fun x => F.σ i x j k) R := by
          simp only [Finset.mul_sum]
          calc _ = ∑ j, ∑ i, ∑ k, (d : ℝ) * (p i ^ 2 *
                ballOscillation (fun x => F.σ i x j k) R) :=
                Finset.sum_congr rfl fun j _ => Finset.sum_comm
            _ = _ := Finset.sum_comm
      _ ≤ d * ∑ i, p i ^ 2 * q2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (hσi i) (sq_nonneg _)) (Nat.cast_nonneg d)
      _ = d * euclideanSq p * q2 := by rw [← Finset.sum_mul, hpsq, mul_assoc]
  -- the arithmetic of the exponents
  have hR2 : R ^ 2 = d * ((3 : ℝ) ^ n) ^ 2 := by
    rw [hRdef, cubeBallRadius, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  have hGq : G * q2 = 16 * cutoffGradConst d * C₁ ^ 2 * d * ρ ^ 2 := by
    rw [hGdef, hτdef, hq2def, hR2]
    field_simp
    ring
  have hDp := hB p
  have t1 : 2 * (Λ ^ 2 * euclideanSq p + euclideanSq (D.mulVec p)) * (⨍ x in U, (1 - η x) ^ 2) ≤
      2 * ((Λ ^ 2 + B) * euclideanSq p) * (2 * d * τ) := by
    refine mul_le_mul (by linarith) hA1 hA10 ?_
    have hB0 : 0 ≤ (Λ ^ 2 + B) * euclideanSq p := by
      have := euclideanSq_nonneg (D.mulVec p)
      nlinarith [sq_nonneg Λ]
    positivity
  have t2 := mul_le_mul_of_nonneg_left hA2 (by positivity : (0 : ℝ) ≤ Λ ^ 2 * G)
  have t3 := mul_le_mul_of_nonneg_left hA3 hG0
  calc dualityDefect a U p (D.mulVec p)
      ≤ (1 / 2 : ℝ) * (3 * (2 * (Λ ^ 2 * euclideanSq p + euclideanSq (D.mulVec p)) *
          (⨍ x in U, (1 - η x) ^ 2) + Λ ^ 2 * G * (⨍ x in U, (φ x - m) ^ 2) +
          G * ⨍ x in U, ∑ j, ∑ k, (σ j k x - c j k) ^ 2)) :=
        hJ.trans (mul_le_mul_of_nonneg_left hT (by norm_num))
    _ ≤ (1 / 2 : ℝ) * (3 * (2 * ((Λ ^ 2 + B) * euclideanSq p) * (2 * d * τ) +
          Λ ^ 2 * G * (cubeBallRatio d * (d * euclideanSq p * q2)) +
          G * (cubeBallRatio d * (d * euclideanSq p * q2)))) := by
        linarith [t1, t2, t3]
    _ = (1 / 2 : ℝ) * (3 * (2 * ((Λ ^ 2 + B) * euclideanSq p) * (2 * d * τ) +
          (Λ ^ 2 + 1) * cubeBallRatio d * d * euclideanSq p * (G * q2))) := by ring
    _ = cubeCorrectorConst d Λ C₁ B * euclideanSq p * ρ ^ 2 := by
        rw [hGq, hτdef, cubeCorrectorConst]
        ring

end QSH
