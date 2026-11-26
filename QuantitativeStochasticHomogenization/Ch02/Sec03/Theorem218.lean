import QuantitativeStochasticHomogenization.Ch01.Sec05.TwoScaleDeviationBound
import QuantitativeStochasticHomogenization.Ch02.Sec03.CoarseDeviationRate
import QuantitativeStochasticHomogenization.Ch02.Sec03.HomogenizedInverse

/-!
# Theorem 2.18: quantitative homogenization of the Dirichlet problem

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.3, Theorem 2.18, for `d ≥ 2`, `Λ > 1` and a bounded open convex domain `U ⊆ □_0`: for
every `δ > 0` there is `β > 0` such that for every `s ∈ (0, d)` there is `C < ∞` with, for every
law satisfying the assumptions, a random variable `X_s ≤ O₁(C)` such that, for almost every
coefficient field, every `ε ∈ (0, 1]`, `f ∈ W^{1,2+δ}(U)` and the solutions `u^ε, u ∈ f + H¹₀(U)`
of (2.71), (2.72) holds:
`‖u^ε - u‖²_{L̲²(U)} + ‖∇u^ε - ∇u‖²_{Ĥ̲⁻¹(U)} + ‖a(·/ε)∇u^ε - ā∇u‖²_{Ĥ̲⁻¹(U)}
+ ‖½∇u^ε·a(·/ε)∇u^ε - ½∇u·ā∇u‖_{W̲^{-2,1}(U)} ≤ C ‖∇f‖²_{L̲^{2+δ}(U)} (ε^{β(d-s)} + X_s ε^s)`
(`theorem_2_18`).

The proof is the book's: Theorem 1.17, (1.57) and the bound `E(m) ≤ C` give the bound (2.73)
for every `r ∈ (0, 1)` (`exists_dirichlet_bound`); (2.68) with `(s + d)/2` in place of `s`, the
choice `r = 3^{-(m+1)α(d-s)/(4(4+d))}` and Lemma A.4 for the counting measure on `ℕ` give the
random variable `X_s` (`exists_random_rate`). The sum over the scales defining `X_s` is finite
almost surely, which is why the estimate holds for almost every coefficient field.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- `E(m) ≤ (9/4) C(d, Λ)`. -/
theorem coarseDeviation_le_structural [NeZero d] {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (m : ℕ) (a : CoefficientField d Λ) :
    coarseDeviation P m a ≤ 9 / 4 * structuralMatrixConst d Λ := by
  have hCs := structuralMatrixConst_nonneg d Λ
  have hgeo : ∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - n))⁻¹ ≤ 3 / 2 := by
    have e : ∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - n))⁻¹ =
        ∑ j ∈ Finset.range (m + 1), (1 / 3 : ℝ) ^ j := by
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      rw [show m - (m + 1 - 1 - j) = j by omega, one_div, inv_pow]
    rw [e]
    have hs : Summable (fun j : ℕ => (1 / 3 : ℝ) ^ j) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    calc ∑ j ∈ Finset.range (m + 1), (1 / 3 : ℝ) ^ j ≤ ∑' j : ℕ, (1 / 3 : ℝ) ^ j :=
          hs.sum_le_tsum _ (fun j _ => by positivity)
      _ = 3 / 2 := by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  have hsum : ∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - n))⁻¹ *
      Real.sqrt (subcubeDeviation P m n a) ≤ 3 / 2 * Real.sqrt (structuralMatrixConst d Λ) := by
    calc _ ≤ ∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - n))⁻¹ *
          Real.sqrt (structuralMatrixConst d Λ) :=
          Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left
            (Real.sqrt_le_sqrt (subcubeDeviation_le_structuralMatrixConst hP m n a))
            (by positivity)
      _ = (∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - n))⁻¹) *
          Real.sqrt (structuralMatrixConst d Λ) := by rw [Finset.sum_mul]
      _ ≤ 3 / 2 * Real.sqrt (structuralMatrixConst d Λ) :=
          mul_le_mul_of_nonneg_right hgeo (Real.sqrt_nonneg _)
  have h0 : 0 ≤ ∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - n))⁻¹ *
      Real.sqrt (subcubeDeviation P m n a) := Finset.sum_nonneg fun n _ => by positivity
  unfold coarseDeviation
  calc _ ≤ (3 / 2 * Real.sqrt (structuralMatrixConst d Λ)) ^ 2 := pow_le_pow_left₀ h0 hsum 2
    _ = 9 / 4 * structuralMatrixConst d Λ := by rw [mul_pow, Real.sq_sqrt hCs]; norm_num

/-- `x² + y² + z² ≤ (x + y + z)²` in `[0, ∞]`. -/
theorem sq_add_sq_add_sq_le (x y z : ℝ≥0∞) : x ^ 2 + y ^ 2 + z ^ 2 ≤ (x + y + z) ^ 2 := by
  have e : (x + y + z) ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 + (2 * x * y + 2 * x * z + 2 * y * z) := by
    ring
  rw [e]
  exact le_self_add

/-- The real inequality behind (2.73). -/
theorem dirichlet_bound_real {C₁ C₅₇ r β₁ x M : ℝ} (hC₁ : 0 ≤ C₁) (hC₅₇ : 0 ≤ C₅₇) (hr0 : 0 < r)
    (hr1 : r < 1) (hβ₁ : 0 ≤ β₁) (hxM : Real.sqrt x ≤ M) :
    C₁ ^ 2 * (r ^ β₁ + r ^ (-(2 + (d : ℝ) / 2)) * Real.sqrt (C₅₇ * x)) ^ 2 +
        C₁ * (r ^ β₁ + r ^ (-(2 + (d : ℝ) / 2)) * Real.sqrt (C₅₇ * x)) ≤
      (2 * C₁ ^ 2 + C₁) * r ^ (min β₁ 1) +
        (2 * C₁ ^ 2 * C₅₇ * M + C₁ * Real.sqrt C₅₇) * r ^ (-(4 + (d : ℝ))) * Real.sqrt x := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = r ^ β₁ := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = r ^ (-(2 + (d : ℝ) / 2)) := ⟨_, rfl⟩
  obtain ⟨R₂, hR₂⟩ : ∃ R₂ : ℝ, R₂ = r ^ (-(4 + (d : ℝ))) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = Real.sqrt x := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = r ^ (min β₁ 1) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = Real.sqrt C₅₇ := ⟨_, rfl⟩
  rw [← ha, ← hR, ← hR₂, ← hb, Real.sqrt_mul hC₅₇, ← hw, ← hc]
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have ha0 : 0 ≤ a := by rw [ha]; exact Real.rpow_nonneg hr0.le _
  have hab : a ≤ b := by
    rw [ha, hb]; exact Real.rpow_le_rpow_of_exponent_ge hr0 hr1.le (min_le_left _ _)
  have hb1 : b ≤ 1 := by
    rw [hb]; exact Real.rpow_le_one hr0.le hr1.le (le_min hβ₁ zero_le_one)
  have hw0 : 0 ≤ w := by rw [hw]; exact Real.sqrt_nonneg _
  have hwM : w ≤ M := by rw [hw]; exact hxM
  have hc0 : 0 ≤ c := by rw [hc]; exact Real.sqrt_nonneg _
  have hcc : c ^ 2 = C₅₇ := by rw [hc]; exact Real.sq_sqrt hC₅₇
  have hR1 : 1 ≤ R := by
    rw [hR]; exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr0 hr1.le (by linarith)
  have hRR : R ^ 2 = R₂ := by
    rw [hR, hR₂, ← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
    congr 1
    push_cast
    ring
  have hRR₂ : R ≤ R₂ := by
    rw [← hRR]
    nlinarith
  have hR₂0 : 0 ≤ R₂ := by rw [← hRR]; positivity
  have hw2 : w ^ 2 ≤ M * w := by
    rw [sq]; exact mul_le_mul_of_nonneg_right hwM hw0
  have ha2 : a ^ 2 ≤ b := by
    have : a ^ 2 ≤ a := by rw [sq]; exact mul_le_of_le_one_left ha0 (hab.trans hb1)
    linarith
  have hv : (R * (c * w)) ^ 2 = R ^ 2 * C₅₇ * w ^ 2 := by rw [← hcc]; ring
  have hY2 : (a + R * (c * w)) ^ 2 ≤ 2 * b + 2 * (R₂ * C₅₇ * M * w) := by
    have h1 := two_mul_le_add_sq a (R * (c * w))
    have h2 : R ^ 2 * C₅₇ * w ^ 2 ≤ R₂ * C₅₇ * M * w := by
      rw [hRR, mul_assoc (R₂ * C₅₇) M w]
      exact mul_le_mul_of_nonneg_left hw2 (mul_nonneg hR₂0 hC₅₇)
    nlinarith [h1, h2, hv, ha2]
  have hY1 : a + R * (c * w) ≤ b + R₂ * c * w := by
    have : R * (c * w) ≤ R₂ * (c * w) := mul_le_mul_of_nonneg_right hRR₂ (mul_nonneg hc0 hw0)
    linarith [mul_assoc R₂ c w]
  calc C₁ ^ 2 * (a + R * (c * w)) ^ 2 + C₁ * (a + R * (c * w)) ≤
        C₁ ^ 2 * (2 * b + 2 * (R₂ * C₅₇ * M * w)) + C₁ * (b + R₂ * c * w) :=
        add_le_add (mul_le_mul_of_nonneg_left hY2 (sq_nonneg C₁))
          (mul_le_mul_of_nonneg_left hY1 hC₁)
    _ = _ := by ring

set_option maxHeartbeats 400000 in
/-- **The bound (2.73)** for every `r ∈ (0, 1)`: from Theorem 1.17, (1.57) and `E(m) ≤ C`, there
are `β₁ ∈ (0, 1]` and `K₁, K₂` such that, with `m = m(ε)`, the left side of (2.72) is at most
`‖∇f‖²_{L̲^{2+δ}(U)} (K₁ r^{β₁} + K₂ r^{-4-d} (3^{-2m} + E(m))^{1/2})`. -/
theorem exists_dirichlet_bound (hd : 2 ≤ d) (hΛ : 1 ≤ Λ) {U : Set (Vec d)} (hUo : IsOpen U)
    (hUc : Convex ℝ U) (hUne : U.Nonempty) (hU : U ⊆ triadicCube d 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ β₁ K₁ K₂ : ℝ, 0 < β₁ ∧ β₁ ≤ 1 ∧ 0 ≤ K₁ ∧ 0 ≤ K₂ ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∀ (a : CoefficientField d Λ) (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ (f : Vec d → ℝ) (F : Vec d → Vec d), IsW1p U (ENNReal.ofReal (2 + δ)) f F →
      ∀ (uε u : Vec d → ℝ) (gε g : Vec d → Vec d),
      H01 U (fun x => uε x - f x) (fun x => gε x - F x) →
      HasWeakDivergence U (fun x => (a (ε⁻¹ • x)).mulVec (gε x)) (fun _ => 0) →
      H01 U (fun x => u x - f x) (fun x => g x - F x) →
      HasWeakDivergence U (fun x => (homogenizedMatrix P).mulVec (g x)) (fun _ => 0) →
      ∀ r : ℝ, 0 < r → r < 1 →
      ENNReal.ofReal (scalarRms volume U (fun x => uε x - u x)) ^ 2 +
          vectorHatNegativeSobolevNorm U (fun x => gε x - g x) ^ 2 +
          vectorHatNegativeSobolevNorm U
            (fun x => (a (ε⁻¹ • x)).mulVec (gε x) - (homogenizedMatrix P).mulVec (g x)) ^ 2 +
          negativeSobolevTwoNorm (ENNReal.ofReal 1) U (fun x =>
            (1 / 2 : ℝ) * dot (gε x) ((a (ε⁻¹ • x)).mulVec (gε x)) -
              (1 / 2 : ℝ) * dot (g x) ((homogenizedMatrix P).mulVec (g x))) ≤
        PDE.eLpMeanNormOn U (ENNReal.ofReal (2 + δ)) (fun x => euclideanNorm (F x)) ^ 2 *
          ENNReal.ofReal (K₁ * r ^ β₁ + K₂ * r ^ (-(4 + (d : ℝ))) *
            Real.sqrt (((3 : ℝ) ^ triadicScale ε)⁻¹ ^ 2 +
              coarseDeviation P (triadicScale ε) a)) := by
  have hd0 : 0 < d := by omega
  have : NeZero d := ⟨hd0.ne'⟩
  have hΛ0 : 0 ≤ Λ := by linarith
  obtain ⟨β, C₁, hβ, hC₁, h117⟩ := TwoScale.theorem_1_17 hd hΛ hUo hUc hUne hU hδ
  obtain ⟨C₅₇, hC₅₇, h57⟩ := TwoScale.twoScaleDeviation_le (d := d) (Λ := Λ) hd0
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = Real.sqrt (1 + 9 / 4 * structuralMatrixConst d Λ) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; exact Real.sqrt_nonneg _
  refine ⟨min β 1, 2 * C₁ ^ 2 + C₁, 2 * C₁ ^ 2 * C₅₇ * M + C₁ * Real.sqrt C₅₇, lt_min hβ one_pos,
    min_le_right _ _, add_nonneg (by positivity) hC₁,
    add_nonneg (mul_nonneg (mul_nonneg (by positivity) hC₅₇) hM0)
      (mul_nonneg hC₁ (Real.sqrt_nonneg _)),
    fun P hP a ε hε hε1 f F hf uε u gε g h1 h2 h3 h4 r hr0 hr1 => ?_⟩
  have hex : ∀ k : Fin d, ∃ (u' : Vec d → ℝ) (g' : Vec d → Vec d),
      IsDirichletMinimizer a (triadicCube d (triadicScale ε)) (unitVector k) u' g' := fun k =>
    exists_isDirichletMinimizer a (isBounded_triadicCube _) (volume_triadicCube_ne_zero d _) _
  choose φ Dφ hmin using hex
  obtain ⟨hA, hB⟩ := h117 a (homogenizedMatrix P) (homogenizedMatrix_transpose hP hΛ0)
    (euclideanSq_le_dot_homogenizedMatrix hP hΛ0) (fun ξ => (homogenizedMatrix_dot_bounds hP hΛ0 ξ).2)
    ε hε hε1 φ Dφ hmin f F hf uε u gε g h1 h2 h3 h4 r hr0 hr1
  have hE := h57 P hP a ε hε hε1 φ Dφ hmin
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = ((3 : ℝ) ^ triadicScale ε)⁻¹ ^ 2 +
      coarseDeviation P (triadicScale ε) a := ⟨_, rfl⟩
  rw [← hx] at hE ⊢
  have hq1 : ((3 : ℝ) ^ triadicScale ε)⁻¹ ^ 2 ≤ 1 := by
    have h : ((3 : ℝ) ^ triadicScale ε)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    nlinarith [inv_nonneg.2 (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (triadicScale ε))]
  have hE0 : 0 ≤ coarseDeviation P (triadicScale ε) a := sq_nonneg _
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hxM : Real.sqrt x ≤ M := by
    rw [hM]
    refine Real.sqrt_le_sqrt ?_
    rw [hx]
    linarith [coarseDeviation_le_structural hP (triadicScale ε) a]
  have hCx : 0 ≤ C₅₇ * x := mul_nonneg hC₅₇ hx0
  have hEs : TwoScale.twoScaleDeviation a (homogenizedMatrix P) ε φ Dφ ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (C₅₇ * x)) := by
    refine (ENNReal.rpow_le_rpow hE (by norm_num)).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg hCx (by norm_num), Real.sqrt_eq_rpow]
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = r ^ β + r ^ (-(2 + (d : ℝ) / 2)) * Real.sqrt (C₅₇ * x) :=
    ⟨_, rfl⟩
  have hR0 : 0 ≤ r ^ (-(2 + (d : ℝ) / 2)) := Real.rpow_nonneg hr0.le _
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hBr : ENNReal.ofReal (r ^ β) + ENNReal.ofReal (r ^ (-(2 + (d : ℝ) / 2))) *
      TwoScale.twoScaleDeviation a (homogenizedMatrix P) ε φ Dφ ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal Y := by
    rw [hY, ENNReal.ofReal_add (Real.rpow_nonneg hr0.le _) (mul_nonneg hR0 (Real.sqrt_nonneg _)),
      ENNReal.ofReal_mul hR0]
    exact add_le_add le_rfl (mul_le_mul_right hEs _)
  have hS := hA.trans (mul_le_mul_right hBr _)
  have hN := hB.trans (mul_le_mul_right hBr _)
  calc _ ≤ (ENNReal.ofReal (scalarRms volume U (fun x => uε x - u x)) +
          vectorHatNegativeSobolevNorm U (fun x => gε x - g x) +
          vectorHatNegativeSobolevNorm U
            (fun x => (a (ε⁻¹ • x)).mulVec (gε x) - (homogenizedMatrix P).mulVec (g x))) ^ 2 +
          negativeSobolevTwoNorm (ENNReal.ofReal 1) U (fun x =>
            (1 / 2 : ℝ) * dot (gε x) ((a (ε⁻¹ • x)).mulVec (gε x)) -
              (1 / 2 : ℝ) * dot (g x) ((homogenizedMatrix P).mulVec (g x))) :=
        add_le_add (sq_add_sq_add_sq_le _ _ _) le_rfl
    _ ≤ (ENNReal.ofReal C₁ *
          PDE.eLpMeanNormOn U (ENNReal.ofReal (2 + δ)) (fun x => euclideanNorm (F x)) *
            ENNReal.ofReal Y) ^ 2 + ENNReal.ofReal C₁ *
          PDE.eLpMeanNormOn U (ENNReal.ofReal (2 + δ)) (fun x => euclideanNorm (F x)) ^ 2 *
            ENNReal.ofReal Y := add_le_add (pow_le_pow_left₀ zero_le hS 2) hN
    _ = PDE.eLpMeanNormOn U (ENNReal.ofReal (2 + δ)) (fun x => euclideanNorm (F x)) ^ 2 *
          ENNReal.ofReal (C₁ ^ 2 * Y ^ 2 + C₁ * Y) := by
        rw [ENNReal.ofReal_add (by positivity) (mul_nonneg hC₁ hY0),
          ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow hC₁, ENNReal.ofReal_pow hY0,
          ENNReal.ofReal_mul hC₁]
        ring
    _ ≤ _ := by
        refine mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
        rw [hY]
        exact dirichlet_bound_real hC₁ hC₅₇ hr0 hr1 hβ.le hxM

end QSH
