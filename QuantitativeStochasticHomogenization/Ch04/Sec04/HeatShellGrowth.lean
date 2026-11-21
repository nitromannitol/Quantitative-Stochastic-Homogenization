import QuantitativeStochasticHomogenization.Ch04.Sec04.LocalizationErrorDecay

/-!
# Gaussian averages from ball integrals with polynomial growth

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.21 (summation over Gaussian annuli). If a nonnegative function `f` on `B_T(z)`
satisfies `∫_{B_T(z) ∩ B_t(z)} f ≤ A (t/r)^k |B_t|` for every `t ≥ r`, then
`∫_{B_T(z)} Φ_{z,r} f ≤ (4π)^{-d/2} |B_1| S_{k+d} A`, with
`S_m = ∑_j exp(-j²/4) (j+1)^m`. The proof splits `B_T(z)` into the shells
`j r ≤ |x - z| < (j+1) r`, on which `Φ_{z,r}` is at most its peak times `exp(-j²/4)`.
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ} {z : Vec d} {T r : ℝ}

theorem summable_heatShell (m : ℕ) :
    Summable fun j : ℕ => Real.exp (-((j : ℝ) ^ 2) / 4) * ((j : ℝ) + 1) ^ m := by
  have hs : Summable fun n : ℕ => (n : ℝ) ^ m * Real.exp (-1 * n) :=
    Real.summable_pow_mul_exp_neg_nat_mul m one_pos
  have hs1 : Summable fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ m * Real.exp (-1 * ((j + 1 : ℕ) : ℝ)) :=
    (summable_nat_add_iff 1).mpr hs
  refine (hs1.mul_left (Real.exp 2)).of_nonneg_of_le (fun j => by positivity) fun j => ?_
  push_cast
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h1 : Real.exp (-((j : ℝ) ^ 2) / 4) ≤ Real.exp 2 * Real.exp (-1 * ((j : ℝ) + 1)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg ((j : ℝ) / 2 - 1)])
  calc Real.exp (-((j : ℝ) ^ 2) / 4) * ((j : ℝ) + 1) ^ m
      ≤ Real.exp 2 * Real.exp (-1 * ((j : ℝ) + 1)) * ((j : ℝ) + 1) ^ m := by gcongr
    _ = Real.exp 2 * (((j : ℝ) + 1) ^ m * Real.exp (-1 * ((j : ℝ) + 1))) := by ring

/-- The shell sum `S_m = ∑_j exp(-j²/4) (j+1)^m`. -/
def heatShellSum (m : ℕ) : ℝ := ∑' j : ℕ, Real.exp (-((j : ℝ) ^ 2) / 4) * ((j : ℝ) + 1) ^ m

/-- The constant `(4π)^{-d/2} |B_1| S_{k+d}` of `integral_heatKernel_mul_le_of_ball_growth`. -/
def heatShellConstant (d k : ℕ) : ℝ :=
  (4 * Real.pi) ^ (-(d : ℝ) / 2) * volume.real (ball (0 : Vec d) 1) * heatShellSum (k + d)

/-- On the shell `j r ≤ |x - z|`, the mask is at most its peak times `exp(-j²/4)`. -/
theorem heatKernel_le_peak_mul_exp_shell (z : Vec d) {r : ℝ} (hr : 0 < r) {x : Vec d} {j : ℕ}
    (hj : (j : ℝ) * r ≤ euclideanNorm (x - z)) :
    heatKernel z r x ≤ heatKernelPeak d r * Real.exp (-((j : ℝ) ^ 2) / 4) := by
  rw [heatKernel_eq_exp]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (heatKernelPeak_pos hr.ne').le
  have hsq : ((j : ℝ) * r) ^ 2 ≤ euclideanSq (x - z) := by
    rw [← sq_euclideanNorm]
    exact pow_le_pow_left₀ (by positivity) hj 2
  have h4 : 0 < 4 * r ^ 2 := by positivity
  have : (j : ℝ) ^ 2 / 4 ≤ 1 / (4 * r ^ 2) * euclideanSq (x - z) := by
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by norm_num) h4]
    nlinarith
  linarith [neg_div 4 ((j : ℝ) ^ 2)]

/-- **Gaussian averages from ball integrals with polynomial growth.** -/
theorem integral_heatKernel_mul_le_of_ball_growth {f : Vec d → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hfi : IntegrableOn f (ball z T)) (hr : 0 < r) {A : ℝ} (hA : 0 ≤ A) (k : ℕ)
    (hgrowth : ∀ t : ℝ, r ≤ t →
      ∫ x in ball z T ∩ ball z t, f x ≤ A * (t / r) ^ k * volume.real (ball z t)) :
    ∫ x in ball z T, heatKernel z r x * f x ≤ heatShellConstant d k * A := by
  set N : ℕ := ⌈T / r⌉₊ + 1 with hN
  set e : ℕ → ℝ := fun j => Real.exp (-((j : ℝ) ^ 2) / 4) with he
  set P := heatKernelPeak d r with hP
  have hP0 : 0 ≤ P := (heatKernelPeak_pos hr.ne').le
  -- the pointwise majorant on `B_T(z)`
  have hmaj : ∀ x ∈ ball z T, heatKernel z r x * f x ≤
      ∑ j ∈ Finset.range N, P * e j * (ball z ((j + 1) * r)).indicator f x := by
    intro x hx
    have hxT : euclideanNorm (x - z) < T := hx
    set j := ⌊euclideanNorm (x - z) / r⌋₊ with hj
    have hq0 : 0 ≤ euclideanNorm (x - z) / r := div_nonneg (zero_le_euclideanNorm _) hr.le
    have hjle : (j : ℝ) * r ≤ euclideanNorm (x - z) := by
      have := Nat.floor_le hq0
      rwa [le_div_iff₀ hr] at this
    have hjlt : euclideanNorm (x - z) < ((j : ℝ) + 1) * r := by
      have := Nat.lt_floor_add_one (euclideanNorm (x - z) / r)
      rwa [div_lt_iff₀ hr] at this
    have hjN : j ∈ Finset.range N := by
      rw [Finset.mem_range, hN]
      have h1 : j ≤ ⌈T / r⌉₊ := by
        refine Nat.floor_le_of_le ?_
        refine le_trans ?_ (Nat.le_ceil _)
        exact div_le_div_of_nonneg_right hxT.le hr.le
      omega
    have hxj : x ∈ ball z ((j + 1) * r) := by
      exact hjlt
    have hsingle : P * e j * (ball z ((j + 1) * r)).indicator f x ≤
        ∑ i ∈ Finset.range N, P * e i * (ball z ((i + 1) * r)).indicator f x :=
      Finset.single_le_sum (f := fun i => P * e i * (ball z ((i + 1) * r)).indicator f x)
        (fun i _ => mul_nonneg (mul_nonneg hP0 (Real.exp_pos _).le)
          (Set.indicator_nonneg (fun y _ => hf0 y) x)) hjN
    refine le_trans ?_ hsingle
    rw [Set.indicator_of_mem hxj]
    exact mul_le_mul_of_nonneg_right (heatKernel_le_peak_mul_exp_shell z hr hjle) (hf0 x)
  have hint_j : ∀ j : ℕ, IntegrableOn (fun x => P * e j * (ball z ((j + 1) * r)).indicator f x)
      (ball z T) := fun j =>
    ((hfi.indicator (measurableSet_ball z _)).const_mul (P * e j))
  have hint_sum : IntegrableOn
      (fun x => ∑ j ∈ Finset.range N, P * e j * (ball z ((j + 1) * r)).indicator f x)
      (ball z T) := integrable_finsetSum _ fun j _ => hint_j j
  have hKf : IntegrableOn (fun x => heatKernel z r x * f x) (ball z T) := by
    refine hfi.bdd_mul (c := P) (continuous_heatKernel_right z r).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_pos_of_ne z hr.ne' x).le]
    exact heatKernel_le_peak z hr.ne' x
  have step1 : ∫ x in ball z T, heatKernel z r x * f x ≤
      ∑ j ∈ Finset.range N, P * e j * ∫ x in ball z T ∩ ball z ((j + 1) * r), f x := by
    refine (setIntegral_mono_on hKf hint_sum (measurableSet_ball z T) hmaj).trans (le_of_eq ?_)
    rw [integral_finsetSum _ fun j _ => hint_j j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, setIntegral_indicator (measurableSet_ball z _)]
  have hV1 := volume_real_ball_pos (0 : Vec d) one_pos
  have step2 : ∀ j : ℕ, P * e j * ∫ x in ball z T ∩ ball z ((j + 1) * r), f x ≤
      (4 * Real.pi) ^ (-(d : ℝ) / 2) * volume.real (ball (0 : Vec d) 1) *
        (e j * ((j : ℝ) + 1) ^ (k + d)) * A := by
    intro j
    have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have ht : r ≤ ((j : ℝ) + 1) * r := le_mul_of_one_le_left hr.le (by linarith [Nat.cast_nonneg (α := ℝ) j])
    have hg := hgrowth (((j : ℝ) + 1) * r) ht
    have hvol := volume_real_ball_eq_mul z (mul_pos hj1 hr)
    have hpk := heatKernelPeak_mul_volume_real_ball z hr
    rw [volume_real_ball_eq_mul z hr] at hpk
    have hdiv : ((j : ℝ) + 1) * r / r = (j : ℝ) + 1 := by field_simp
    rw [hdiv, hvol] at hg
    have hPe : 0 ≤ P * e j := mul_nonneg hP0 (Real.exp_pos _).le
    calc P * e j * ∫ x in ball z T ∩ ball z ((j + 1) * r), f x
        ≤ P * e j * (A * ((j : ℝ) + 1) ^ k *
            ((((j : ℝ) + 1) * r) ^ d * volume.real (ball (0 : Vec d) 1))) := by
          exact mul_le_mul_of_nonneg_left hg hPe
      _ = (P * r ^ d * volume.real (ball (0 : Vec d) 1)) *
            (e j * ((j : ℝ) + 1) ^ (k + d)) * A := by
          rw [mul_pow, pow_add]
          ring
      _ = _ := by
          rw [show P * r ^ d * volume.real (ball (0 : Vec d) 1) =
            P * (r ^ d * volume.real (ball (0 : Vec d) 1)) by ring, hpk]
  have hsum_le : ∑ j ∈ Finset.range N, e j * ((j : ℝ) + 1) ^ (k + d) ≤ heatShellSum (k + d) :=
    (summable_heatShell (k + d)).sum_le_tsum _ fun j _ => by positivity
  have hc0 : 0 ≤ (4 * Real.pi) ^ (-(d : ℝ) / 2) * volume.real (ball (0 : Vec d) 1) :=
    mul_nonneg (by positivity) hV1.le
  calc ∫ x in ball z T, heatKernel z r x * f x
      ≤ ∑ j ∈ Finset.range N, P * e j * ∫ x in ball z T ∩ ball z ((j + 1) * r), f x := step1
    _ ≤ ∑ j ∈ Finset.range N, (4 * Real.pi) ^ (-(d : ℝ) / 2) *
          volume.real (ball (0 : Vec d) 1) * (e j * ((j : ℝ) + 1) ^ (k + d)) * A :=
        Finset.sum_le_sum fun j _ => step2 j
    _ = (4 * Real.pi) ^ (-(d : ℝ) / 2) * volume.real (ball (0 : Vec d) 1) *
          (∑ j ∈ Finset.range N, e j * ((j : ℝ) + 1) ^ (k + d)) * A := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ (4 * Real.pi) ^ (-(d : ℝ) / 2) * volume.real (ball (0 : Vec d) 1) *
          heatShellSum (k + d) * A :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum_le hc0) hA
    _ = heatShellConstant d k * A := rfl

/-- **Lemmas 4.21-4.22 at a coefficient field from first-order correctors and ball estimates**:
`abs_J1Heat_sub_localizedJ1_le_of_correctors` with the Gaussian closeness of the localized
coordinates to the corrected gradients `W_i + ∑_j b_{ij} W_j` replaced by ball estimates with
polynomial growth, `∫_{B_T ∩ B_t} |∇w_i - W_i - ∑_j b_{ij} W_j|² ≤ A (t/r)^k |B_t|` for `t ≥ r`;
then `ρ = (heatShellConstant d k · A)^{1/2}`. -/
theorem abs_J1Heat_sub_localizedJ1_le_of_ball_growth {Λ : ℝ} {a : CoefficientField d Λ}
    (hΛ : 0 ≤ Λ) (hd : 0 < d) (hr : 0 < r) (hrT : r ≤ T) {S σ θ C : ℝ}
    {B : LocalizedBasis a z T S σ θ C} {p q : Vec d} {E ε A : ℝ}
    (hsmall : linearCoefficient d Λ p q ^ 2 / 2 *
      ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2))) ≤ 1 / 4)
    (φ : Fin d → Vec d → ℝ) (g : Fin d → Vec d → Vec d)
    (hφg : ∀ i, HasWeakGradient Set.univ (φ i) (g i))
    (hloc : ∀ i, ∀ R : ℝ, 0 < R → MemLp (φ i) 2 (volume.restrict (ball 0 R)) ∧
      MemLp (g i) 2 (volume.restrict (ball 0 R)))
    (harm : ∀ i, HasWeakDivergence Set.univ (fun x => (a x).mulVec (unitVector i + g i x))
      (fun _ => 0))
    (c : Fin d → ℝ)
    (hosc : ∀ i, ∫ x in ball z r, (φ i x - c i) ^ 2 ≤ ε ^ 2 * r ^ 2 * volume.real (ball z r))
    (hε : (d : ℝ) * ε ^ 2 ≤ (1 / 4 : ℝ) ^ d / 16) (hE0 : 0 ≤ E)
    (hW : ∀ i, Integrable (fun x => heatKernel z (Real.sqrt 2 * r) x *
      euclideanSq (unitVector i + g i x)))
    (hE : ∀ i, ∫ x, heatKernel z (Real.sqrt 2 * r) x * euclideanSq (unitVector i + g i x) ≤ E)
    (hrep : ∀ w : HarmonicA1 a, ∃ ξ : Vec d,
      ∀ᵐ x, w.grad x = ∑ i, ξ i • (unitVector i + g i x))
    (hWmem : ∀ ξ : Vec d, ∃ w : HarmonicA1 a,
      ∀ᵐ x, w.grad x = ∑ i, ξ i • (unitVector i + g i x))
    (b : Fin d → Fin d → ℝ) (hb : ∑ i, ∑ j, b i j ^ 2 ≤ 1 / 4) (hA : 0 ≤ A) (k : ℕ)
    (hgrowth : ∀ i, ∀ t : ℝ, r ≤ t → ∫ x in ball z T ∩ ball z t,
      euclideanSq ((B.coordinate i).grad x -
        ((unitVector i + g i x) + ∑ j, b i j • (unitVector j + g j x))) ≤
          A * (t / r) ^ k * volume.real (ball z t))
    (hρ : Real.sqrt (heatShellConstant d k * A) ≤ Real.sqrt (heatGramConstant d / 4) / d / 2) :
    |J1Heat a z r p q - localizedJ1 B r p q| ≤
      localizationErrorBound d Λ p q
        (2 * (2 * linearCoefficient d Λ p q + 1) * Real.sqrt (heatShellConstant d k * A) /
          (Real.sqrt (heatGramConstant d / 4) / d))
        ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2)) *
          (d * E / heatGramConstant d)) T r := by
  let uT := fun i => localCorrectedCoordinate a z T i 0 (φ i) (g i) (hφg i) (hloc i) (harm i)
  have hWk : ∀ j k', MemLp (fun x => (unitVector j + g j x) k') 2 (ballMeasure z T) :=
    fun j k' => (uT j).memLp_grad k'
  have hGk : ∀ i k', MemLp (fun x => ((B.coordinate i).grad x -
      ((unitVector i + g i x) + ∑ j, b i j • (unitVector j + g j x))) k') 2
        (ballMeasure z T) := by
    intro i k'
    refine MemLp.ae_eq (Eventually.of_forall fun x => ?_)
      (((B.coordinate i).memLp_grad k').sub ((hWk i k').add
        (memLp_finsetSum Finset.univ fun j _ => (hWk j k').const_mul (b i j))))
    simp only [Pi.sub_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hfi : ∀ i, IntegrableOn (fun x => euclideanSq ((B.coordinate i).grad x -
      ((unitVector i + g i x) + ∑ j, b i j • (unitVector j + g j x)))) (ball z T) := by
    intro i
    refine (integrable_finsetSum Finset.univ fun k' _ => (hGk i k').integrable_sq).congr
      (Eventually.of_forall fun x => ?_)
    simp only [euclideanSq, dot, sq]
  have hclose : ∀ i, ∫ x in ball z T, heatKernel z r x *
      euclideanSq ((B.coordinate i).grad x -
        ((unitVector i + g i x) + ∑ j, b i j • (unitVector j + g j x))) ≤
        Real.sqrt (heatShellConstant d k * A) ^ 2 := by
    intro i
    have hc0 : 0 ≤ heatShellConstant d k := by
      unfold heatShellConstant heatShellSum
      exact mul_nonneg (mul_nonneg (by positivity) measureReal_nonneg)
        (tsum_nonneg fun j => by positivity)
    rw [Real.sq_sqrt (mul_nonneg hc0 hA)]
    exact integral_heatKernel_mul_le_of_ball_growth (fun x => zero_le_euclideanSq _) (hfi i) hr
      hA k (hgrowth i)
  exact abs_J1Heat_sub_localizedJ1_le_of_correctors hΛ hd hr hrT hsmall φ g hφg hloc harm c hosc
    hε hE0 hW hE hrep hWmem b hb (Real.sqrt_nonneg _) hclose hρ

end QSH
