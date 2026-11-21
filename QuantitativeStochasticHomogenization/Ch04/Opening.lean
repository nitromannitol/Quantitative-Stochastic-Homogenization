/-
Moved from einstein-relation-lean (https://github.com/nitromannitol/einstein-relation-lean),
commit 9ff210bd4ddf435139a6c8db07a1547e2bcb7eb6: the semigroup identity from the file
`EinsteinFull/Homogenization/HeatKernelSemigroup.lean`, and the product form of the heat kernel
(`euclideanHeatKernel_eq_prod`) from the file
`vendor/EinsteinRelation/EinsteinRelation/Correctors/HeatKernelConvolution.lean`.
Changes: the namespace is `QSH`, and the statements use the heat kernel `Φ` and the masks
`Φ_{z,r}` of (4.1) defined below.
-/
import QuantitativeStochasticHomogenization.Front.Notation

/-!
# Chapter 4, opening: Quantitative Description of First-Order Correctors

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Chapter 4, the text before Section 4.1. Numbered results: Theorem 4.1.

Defined here: the heat kernel masks `Φ_{z,r}` of (4.1).

Proved here: the semigroup property of the heat kernel, `Φ(t) ∗ Φ(s) = Φ(t + s)` for `t, s > 0`,
and its form `∫ Φ_{z,ρ}(y) Φ_{y,r}(w) dy = Φ_{z,√(ρ² + r²)}(w)` for the masks, which is the
identity `Φ_{z,R} = Φ_{z,√(R² - r²)} ∗ Φ_r` behind the additivity statements of Section 4.2. The
proof completes the square in each coordinate, uses the Gaussian integral, and Fubini's theorem
for the product structure of the kernel.
-/

noncomputable section

namespace QSH

/-- The heat kernel `(4πt)^{-d/2} exp(-|x|²/(4t))`. -/
def euclideanHeatKernel {d : ℕ} (t : ℝ) (x : Vec d) : ℝ :=
  (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-(euclideanSq x) / (4 * t))

/-- **The mask `Φ_{z,r}`**, (4.1): `Φ_{z,r}(x) = Φ(r², x - z)`. -/
def heatKernel {d : ℕ} (z : Vec d) (r : ℝ) (x : Vec d) : ℝ :=
  euclideanHeatKernel (r ^ 2) (x - z)

/-! ## The semigroup property -/

section Semigroup

open MeasureTheory

/-- The product form of the heat kernel. -/
theorem euclideanHeatKernel_eq_prod {d : ℕ} (t : ℝ) (z : Vec d) :
    euclideanHeatKernel t z =
      (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * ∏ i, Real.exp (-(z i * z i) / (4 * t)) := by
  unfold euclideanHeatKernel
  rw [← Real.exp_sum]
  congr 2
  simp only [euclideanSq, dot, neg_div, Finset.sum_div, Finset.sum_neg_distrib]


/-- The one-dimensional Gaussian convolution identity. -/
theorem integral_exp_sub_sq_mul_exp_sub_sq {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (a b : ℝ) :
    ∫ y : ℝ, Real.exp (-((a - y) * (a - y)) / (4 * t)) * Real.exp (-((y - b) * (y - b)) / (4 * s)) =
      Real.sqrt (Real.pi / ((t + s) / (4 * t * s))) *
        Real.exp (-((a - b) * (a - b)) / (4 * (t + s))) := by
  set u : ℝ := (t + s) / (4 * t * s) with hudef
  set c : ℝ := (s * a + t * b) / (t + s) with hcdef
  have hts : 0 < t + s := by linarith
  have key : ∀ y : ℝ, Real.exp (-((a - y) * (a - y)) / (4 * t)) *
      Real.exp (-((y - b) * (y - b)) / (4 * s)) =
      Real.exp (-((a - b) * (a - b)) / (4 * (t + s))) * Real.exp (-u * (y - c) ^ 2) := by
    intro y
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hudef, hcdef]
    field_simp
    ring
  simp only [key]
  rw [integral_const_mul, integral_sub_right_eq_self (fun y => Real.exp (-u * y ^ 2)) c,
    integral_gaussian, mul_comm]

/-- **The semigroup property of the Euclidean heat kernel.** -/
theorem integral_euclideanHeatKernel_mul {d : ℕ} {t s : ℝ} (ht : 0 < t) (hs : 0 < s)
    (x z : Vec d) :
    ∫ y, euclideanHeatKernel t (x - y) * euclideanHeatKernel s (y - z) =
      euclideanHeatKernel (t + s) (x - z) := by
  have hts : 0 < t + s := by linarith
  have hfac : ∀ y : Vec d, euclideanHeatKernel t (x - y) * euclideanHeatKernel s (y - z) =
      ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) * (4 * Real.pi * s) ^ (-(d : ℝ) / 2)) *
        ∏ i, (Real.exp (-((x i - y i) * (x i - y i)) / (4 * t)) *
          Real.exp (-((y i - z i) * (y i - z i)) / (4 * s))) := by
    intro y
    rw [euclideanHeatKernel_eq_prod, euclideanHeatKernel_eq_prod, Finset.prod_mul_distrib]
    simp only [Pi.sub_apply]
    ring
  simp only [hfac]
  rw [integral_const_mul, integral_fintype_prod_volume_eq_prod
    (fun (i : Fin d) (w : ℝ) => Real.exp (-((x i - w) * (x i - w)) / (4 * t)) *
      Real.exp (-((w - z i) * (w - z i)) / (4 * s)))]
  simp only [integral_exp_sub_sq_mul_exp_sub_sq ht hs, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [euclideanHeatKernel_eq_prod]
  simp only [Pi.sub_apply]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hA : 0 < 4 * Real.pi * t := by positivity
  have hB : 0 < 4 * Real.pi * s := by positivity
  have hC : 0 < 4 * Real.pi * (t + s) := by positivity
  have hrp : ∀ X : ℝ, 0 < X → X ^ (-(d : ℝ) / 2) = (Real.sqrt X ^ d)⁻¹ := by
    intro X hX
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hX.le, ← Real.rpow_neg hX.le]
    congr 1
    ring
  have hsq : Real.sqrt (Real.pi / ((t + s) / (4 * t * s))) =
      Real.sqrt (4 * Real.pi * t) * Real.sqrt (4 * Real.pi * s) /
        Real.sqrt (4 * Real.pi * (t + s)) := by
    rw [← Real.sqrt_mul hA.le, ← Real.sqrt_div (by positivity)]
    congr 1
    field_simp
  rw [hrp _ hA, hrp _ hB, hrp _ hC, hsq, div_pow, mul_pow]
  have h1 : 0 < Real.sqrt (4 * Real.pi * t) := Real.sqrt_pos.mpr hA
  have h2 : 0 < Real.sqrt (4 * Real.pi * s) := Real.sqrt_pos.mpr hB
  have h3 : 0 < Real.sqrt (4 * Real.pi * (t + s)) := Real.sqrt_pos.mpr hC
  field_simp

/-- **The semigroup property in the notation `Φ_{z,r}` of AKM (4.1)**:
`∫ Φ_{z,ρ}(y) Φ_{y,r}(w) dy = Φ_{z,√(ρ² + r²)}(w)` for `ρ, r > 0`. -/
theorem integral_heatKernel_mul_heatKernel {d : ℕ} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (z w : Vec d) :
    ∫ y, heatKernel z ρ y * heatKernel y r w = heatKernel z (Real.sqrt (ρ ^ 2 + r ^ 2)) w := by
  simp only [heatKernel]
  rw [Real.sq_sqrt (by positivity), add_comm (ρ ^ 2)]
  rw [← integral_euclideanHeatKernel_mul (pow_pos hr 2) (pow_pos hρ 2) w z]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => mul_comm _ _)

end Semigroup

end QSH
