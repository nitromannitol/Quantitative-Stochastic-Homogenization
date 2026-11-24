import QuantitativeStochasticHomogenization.Ch02.Sec01.SkewCutoff

/-!
# The bound of `J(U, p, Dp)` by a corrector and a flux corrector

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
toward Theorem 2.4: the first step of the finite-cube argument for (2.21) from first-order
correctors. Let `φ ∈ H¹(U)` with gradient `∇φ`, and let `σ` be a skew field with entries in
`H¹(U)` whose antisymmetrized gradient has row divergence `a(p + ∇φ) - Dp` almost everywhere in
`U`. For a smooth cutoff `η` compactly supported in `U`, constants `m` and a skew matrix `c`, the
trials `E = p + ∇(η(φ - m))` and `F = Dp + div(η(σ - c))` give
`J(U, p, Dp) ≤ ½ ⨍_U |(1 - η)(a - D)p + (φ - m) a∇η - (σ - c)∇η|²` (`dualityDefect_le_of_correctors`).
For `|∇η|² ≤ G` the mean square is at most
`3 (2(Λ²|p|² + |Dp|²) ⨍_U (1 - η)² + Λ² G ⨍_U (φ - m)² + G ⨍_U Σⱼₖ (σⱼₖ - cⱼₖ)²)`
(`setAverage_trialError_le`).
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- **The bound of `J(U, p, Dp)` by a corrector `φ` and a flux corrector `σ`.** -/
theorem dualityDefect_le_of_correctors [NeZero d] (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty)
    (hU : PDE.IsOpenBoundedConvexDomain U) (D : Mat d) (p : Vec d)
    {φ : Vec d → ℝ} {gφ : Vec d → Vec d} (hφ : MemLp φ 2 (volume.restrict U))
    (hgφ : ∀ i, MemLp (fun x => gφ x i) 2 (volume.restrict U)) (hwφ : HasWeakGradient U φ gφ)
    (m : ℝ) {σ : Fin d → Fin d → Vec d → ℝ} {gσ : Fin d → Fin d → Vec d → Vec d}
    (hσ : ∀ j k, MemLp (σ j k) 2 (volume.restrict U))
    (hgσ : ∀ j k i, MemLp (fun x => gσ j k x i) 2 (volume.restrict U))
    (hwσ : ∀ j k, HasWeakGradient U (σ j k) (gσ j k)) (hskew : ∀ j k x, σ k j x = -σ j k x)
    (c : Fin d → Fin d → ℝ) (hc : ∀ j k, c k j = -c j k)
    (hflux : ∀ j, ∀ᵐ x ∂(volume.restrict U),
      ∑ k, skewGrad gσ j k x k = (a x).mulVec (p + gφ x) j - D.mulVec p j)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ U) :
    dualityDefect a U p (D.mulVec p) ≤ (1 / 2 : ℝ) * ⨍ x in U, euclideanSq (fun j =>
      (1 - η x) * ((a x).mulVec p j - D.mulVec p j) +
        (φ x - m) * (a x).mulVec (gradient η x) j - ∑ k, (σ j k x - c j k) * gradient η x k) := by
  have hum : MemLp (fun x => φ x - m) 2 (volume.restrict U) := by
    have := isFiniteMeasure_restrict.mpr (volume_lt_top_of_isBoundedDomain hU.2.1).ne
    exact hφ.sub (memLp_const m)
  have hu := h01_cutoff_mul hU hum hgφ (hasWeakGradient_sub_const U hwφ m) hη hηc hηU
  set Θ := skewCutoffFamily hU hσ hgσ hwσ hskew c hη hηc hηU with hΘ
  have hΘs : ∀ j k x, (Θ k j).toH1Function.grad x = -(Θ j k).toH1Function.grad x :=
    skewCutoffFamily_skew hU hσ hgσ hwσ hskew c hη hηc hηU hc
  refine (dualityDefect_le_of_skew a hUo hUb hUc hne p (D.mulVec p) hu Θ hΘs).trans (le_of_eq ?_)
  congr 1
  refine average_congr ?_
  filter_upwards [ae_all_iff.mpr hflux] with x hx
  congr 1
  funext j
  have hg : ∀ k, (Θ j k).toH1Function.grad x k =
      η x * skewGrad gσ j k x k + (σ j k x - c j k) * gradient η x k := fun k => by
    rw [hΘ, skewCutoffFamily_grad]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Pi.sub_apply, Pi.add_apply, hg, Finset.sum_add_distrib, ← Finset.mul_sum, hx j,
    Matrix.mulVec_add, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- The pointwise bound of the trial error. -/
theorem euclideanSq_trialError_le (A D : Mat d) {Λ : ℝ} (hA : ∀ v : Vec d,
    euclideanSq (A.mulVec v) ≤ Λ ^ 2 * euclideanSq v) (p : Vec d) (t s : ℝ) (S : Fin d → Fin d → ℝ)
    (g : Vec d) {G : ℝ} (hG : euclideanSq g ≤ G) :
    euclideanSq (fun j => t * (A.mulVec p j - D.mulVec p j) + s * A.mulVec g j -
      ∑ k, S j k * g k) ≤
      3 * (2 * (Λ ^ 2 * euclideanSq p + euclideanSq (D.mulVec p)) * t ^ 2 + Λ ^ 2 * G * s ^ 2 +
        G * ∑ j, ∑ k, S j k ^ 2) := by
  have h3 : ∀ x y z : ℝ, (x + y - z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := fun x y z => by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + z), sq_nonneg (y + z)]
  have hcs : ∀ j, (∑ k, S j k * g k) ^ 2 ≤ (∑ k, S j k ^ 2) * euclideanSq g := fun j => by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (S j) g
    simpa only [euclideanSq, dot, pow_two] using this
  have hAp := hA p
  have hAg := hA g
  have hsub : ∑ j, (A.mulVec p j - D.mulVec p j) ^ 2 ≤
      2 * (euclideanSq (A.mulVec p) + euclideanSq (D.mulVec p)) := by
    simp only [euclideanSq, dot, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => by nlinarith [sq_nonneg (A.mulVec p j + D.mulVec p j)]
  have hg0 : 0 ≤ euclideanSq g := euclideanSq_nonneg g
  have hG0 : 0 ≤ G := hg0.trans hG
  have hSS : 0 ≤ ∑ j, ∑ k, S j k ^ 2 :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hQ : ∑ j, A.mulVec g j ^ 2 = euclideanSq (A.mulVec g) := by
    simp only [euclideanSq, dot, sq]
  have hpt : euclideanSq (fun j => t * (A.mulVec p j - D.mulVec p j) + s * A.mulVec g j -
      ∑ k, S j k * g k) ≤ ∑ j, (3 * t ^ 2 * (A.mulVec p j - D.mulVec p j) ^ 2 +
        3 * s ^ 2 * A.mulVec g j ^ 2 + 3 * (∑ k, S j k * g k) ^ 2) := by
    simp only [euclideanSq, dot]
    exact Finset.sum_le_sum fun j _ => by
      have := h3 (t * (A.mulVec p j - D.mulVec p j)) (s * A.mulVec g j) (∑ k, S j k * g k)
      simp only [mul_pow] at this
      nlinarith
  have hsplit : ∑ j, (3 * t ^ 2 * (A.mulVec p j - D.mulVec p j) ^ 2 +
      3 * s ^ 2 * A.mulVec g j ^ 2 + 3 * (∑ k, S j k * g k) ^ 2) =
      3 * t ^ 2 * ∑ j, (A.mulVec p j - D.mulVec p j) ^ 2 + 3 * s ^ 2 * ∑ j, A.mulVec g j ^ 2 +
        3 * ∑ j, (∑ k, S j k * g k) ^ 2 := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have e3 : ∑ j, (∑ k, S j k * g k) ^ 2 ≤ G * ∑ j, ∑ k, S j k ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => (hcs j).trans (by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hG (Finset.sum_nonneg fun k _ => sq_nonneg _))
  have e1 := mul_le_mul_of_nonneg_left hsub (by positivity : (0 : ℝ) ≤ 3 * t ^ 2)
  have e2 := mul_le_mul_of_nonneg_left (hAg.trans (mul_le_mul_of_nonneg_left hG (sq_nonneg Λ)))
    (by positivity : (0 : ℝ) ≤ 3 * s ^ 2)
  have e4 := mul_le_mul_of_nonneg_left hAp (by positivity : (0 : ℝ) ≤ 2 * (3 * t ^ 2))
  rw [hsplit, hQ] at hpt
  nlinarith

/-- **The mean square of the trial error**: for `0 ≤ η ≤ 1` continuous with `|∇η|² ≤ G`,
`⨍_U |(1 - η)(a - D)p + (φ - m) a∇η - (σ - c)∇η|²` is at most
`3 (2(Λ²|p|² + |Dp|²) ⨍_U (1 - η)² + Λ² G ⨍_U (φ - m)² + G ⨍_U Σⱼₖ (σⱼₖ - cⱼₖ)²)`. -/
theorem setAverage_trialError_le (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hU : volume U ≠ ⊤) (D : Mat d) (p : Vec d) {φ : Vec d → ℝ}
    (hφ : MemLp φ 2 (volume.restrict U)) (m : ℝ) {σ : Fin d → Fin d → Vec d → ℝ}
    (hσ : ∀ j k, MemLp (σ j k) 2 (volume.restrict U)) (c : Fin d → Fin d → ℝ) {η : Vec d → ℝ}
    (hηc : Continuous η) (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1) {G : ℝ}
    (hG : ∀ x, euclideanSq (gradient η x) ≤ G) :
    ⨍ x in U, euclideanSq (fun j => (1 - η x) * ((a x).mulVec p j - D.mulVec p j) +
        (φ x - m) * (a x).mulVec (gradient η x) j - ∑ k, (σ j k x - c j k) * gradient η x k) ≤
      3 * (2 * (Λ ^ 2 * euclideanSq p + euclideanSq (D.mulVec p)) * (⨍ x in U, (1 - η x) ^ 2) +
        Λ ^ 2 * G * (⨍ x in U, (φ x - m) ^ 2) +
        G * ⨍ x in U, ∑ j, ∑ k, (σ j k x - c j k) ^ 2) := by
  have := isFiniteMeasure_restrict.mpr hU
  set K := 2 * (Λ ^ 2 * euclideanSq p + euclideanSq (D.mulVec p)) with hK
  have i1 : Integrable (fun x => (1 - η x) ^ 2) (volume.restrict U) := by
    refine Integrable.of_bound (C := 1) ((continuous_const.sub hηc).pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    have h0 := hη0 x
    have h1 := hη1 x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith
  have i2 : Integrable (fun x => (φ x - m) ^ 2) (volume.restrict U) :=
    (hφ.sub (memLp_const m)).integrable_sq
  have i3 : Integrable (fun x => ∑ j, ∑ k, (σ j k x - c j k) ^ 2) (volume.restrict U) :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      ((hσ j k).sub (memLp_const (c j k))).integrable_sq
  have i12 : Integrable (fun x => K * (1 - η x) ^ 2 + Λ ^ 2 * G * (φ x - m) ^ 2)
      (volume.restrict U) := (i1.const_mul _).add (i2.const_mul _)
  have i123 : Integrable (fun x => K * (1 - η x) ^ 2 + Λ ^ 2 * G * (φ x - m) ^ 2 +
      G * ∑ j, ∑ k, (σ j k x - c j k) ^ 2) (volume.restrict U) := i12.add (i3.const_mul _)
  have hpt : ∀ x, euclideanSq (fun j => (1 - η x) * ((a x).mulVec p j - D.mulVec p j) +
      (φ x - m) * (a x).mulVec (gradient η x) j - ∑ k, (σ j k x - c j k) * gradient η x k) ≤
      3 * (K * (1 - η x) ^ 2 + Λ ^ 2 * G * (φ x - m) ^ 2 +
        G * ∑ j, ∑ k, (σ j k x - c j k) ^ 2) := fun x =>
    euclideanSq_trialError_le (a x) D (euclideanSq_coefficient_mulVec_le_sq a x) p (1 - η x)
      (φ x - m) (fun j k => σ j k x - c j k) (gradient η x) (hG x)
  have hle := integral_mono_of_nonneg (Eventually.of_forall fun x => euclideanSq_nonneg _)
    (i123.const_mul 3) (Eventually.of_forall hpt)
  rw [integral_const_mul, integral_add i12 (i3.const_mul _), integral_add (i1.const_mul _)
    (i2.const_mul _), integral_const_mul, integral_const_mul, integral_const_mul] at hle
  simp only [setAverage_eq, smul_eq_mul]
  have hV : 0 ≤ (volume.real U)⁻¹ := inv_nonneg.mpr measureReal_nonneg
  have h := mul_le_mul_of_nonneg_left hle hV
  calc (volume.real U)⁻¹ * ∫ x in U, euclideanSq (fun j => (1 - η x) * ((a x).mulVec p j -
        D.mulVec p j) + (φ x - m) * (a x).mulVec (gradient η x) j -
        ∑ k, (σ j k x - c j k) * gradient η x k)
      ≤ (volume.real U)⁻¹ * (3 * (K * (∫ x in U, (1 - η x) ^ 2) +
          Λ ^ 2 * G * (∫ x in U, (φ x - m) ^ 2) +
          G * ∫ x in U, ∑ j, ∑ k, (σ j k x - c j k) ^ 2)) := h
    _ = _ := by ring

end QSH
