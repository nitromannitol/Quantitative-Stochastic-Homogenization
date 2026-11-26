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

/-- Removing the negative part keeps the stochastic bound. -/
theorem OsBound.max_zero_right {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {s θ : ℝ} (h : OsBound P X s θ) : OsBound P (fun ω => max (X ω) 0) s θ := by
  obtain ⟨hX, hs, hθ, hint⟩ := h
  refine ⟨hX.max measurable_const, hs, hθ, ?_⟩
  simpa only [max_assoc, max_self] using hint

/-- `√(x² + E) ≤ x + √E` for `x, E ≥ 0`. -/
theorem sqrt_sq_add_le {x E : ℝ} (hx : 0 ≤ x) (hE : 0 ≤ E) :
    Real.sqrt (x ^ 2 + E) ≤ x + Real.sqrt E := by
  have h := Real.sq_sqrt hE
  calc Real.sqrt (x ^ 2 + E) ≤ Real.sqrt ((x + Real.sqrt E) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [Real.sqrt_nonneg E])
    _ = x + Real.sqrt E := Real.sqrt_sq (add_nonneg hx (Real.sqrt_nonneg E))

set_option maxHeartbeats 400000 in
/-- **The random variable of Theorem 2.18**: from (2.68) and Lemma A.4, for `β₁ ∈ (0, 1]` and
`K₁, K₂ ≥ 0` there is `β > 0` such that for every `s ∈ (0, d)` there is `C` with, for every law
satisfying the assumptions, a random variable `0 ≤ X ≤ O₁(C)` such that almost surely, for every
`m`, some `r ∈ (0, 1)` has `K₁ r^{β₁} + K₂ r^{-4-d} (3^{-2m} + E(m))^{1/2} ≤
C (3^{-mβ(d-s)} + 3^{-ms} X)`. -/
theorem exists_random_rate (hd : 2 ≤ d) (hΛ : 1 < Λ) {β₁ K₁ K₂ : ℝ} (hβ₁ : 0 < β₁)
    (hβ₁1 : β₁ ≤ 1) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) :
    ∃ β : ℝ, 0 < β ∧ ∀ s : ℝ, 0 < s → s < d → ∃ C : ℝ, 0 < C ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∃ X : CoefficientField d Λ → ℝ, OsBound P X 1 C ∧ (∀ a, 0 ≤ X a) ∧ ∀ᵐ a ∂P, ∀ m : ℕ,
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          K₁ * r ^ β₁ + K₂ * r ^ (-(4 + (d : ℝ))) *
              Real.sqrt (((3 : ℝ) ^ m)⁻¹ ^ 2 + coarseDeviation P m a) ≤
            C * ((3 : ℝ) ^ (-((m : ℝ) * (β * ((d : ℝ) - s)))) +
              (3 : ℝ) ^ (-((m : ℝ) * s)) * X a) := by
  obtain ⟨α, hα, hα1, h68⟩ := exists_sqrt_coarseDeviation_le hd hΛ
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h3 : (0 : ℝ) < 3 := by norm_num
  have h31 : (1 : ℝ) ≤ 3 := by norm_num
  have hαd : α * d ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hα1 (by linarith : (0 : ℝ) ≤ d)
    rwa [one_div, inv_mul_cancel₀ (by linarith)] at this
  have hk : (0 : ℝ) < 4 + d := by linarith
  refine ⟨β₁ * α / (4 * (4 + d)), by positivity, fun s hs hsd => ?_⟩
  have hds : 0 < (d : ℝ) - s := by linarith
  obtain ⟨C₆, hC₆, h6⟩ := h68 ((s + d) / 2) (by linarith) (by linarith)
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = α * ((d : ℝ) - s) / 4 := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hT]; positivity
  have hTd : T ≤ ((d : ℝ) - s) / 4 := by
    rw [hT]
    have : α * ((d : ℝ) - s) ≤ 1 * ((d : ℝ) - s) :=
      mul_le_mul_of_nonneg_right (hα1.trans (by
        rw [div_le_one (by linarith)]; linarith)) hds.le
    linarith
  have hT1 : T ≤ 1 / 4 := by
    rw [hT]
    have : α * ((d : ℝ) - s) ≤ α * d := mul_le_mul_of_nonneg_left (by linarith) hα.le
    linarith
  have hβT : β₁ * α / (4 * (4 + d)) * ((d : ℝ) - s) = β₁ * T / (4 + d) := by
    rw [hT]; field_simp
  have hβT' : β₁ * T / (4 + d) ≤ T := by
    rw [div_le_iff₀ hk]
    nlinarith
  -- the weights of the scales
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (3 : ℝ) ^ (-(((d : ℝ) - s) / 4)) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  have hρ1 : ρ < 1 := by
    rw [hρ]; exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hK₂1 : 0 < K₂ + 1 := by linarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (K₂ + 1) * C₆ * 3 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; exact mul_pos (mul_pos hK₂1 hC₆) h3
  have hρ' : 0 < (1 - ρ)⁻¹ := inv_pos.2 (by linarith)
  have hcρ : 0 < c * (1 - ρ)⁻¹ := mul_pos hc0 hρ'
  have hK : 0 ≤ K₁ + 3 * K₂ * (1 + C₆) := by
    have : 0 ≤ 3 * K₂ * (1 + C₆) := by positivity
    linarith
  refine ⟨K₁ + 3 * K₂ * (1 + C₆) + 1 + c * (1 - ρ)⁻¹, by linarith, fun P hP => ?_⟩
  have : IsProbabilityMeasure P := hP.1
  choose V hVos hVle using fun m => h6 P hP m
  obtain ⟨κ, hκ⟩ : ∃ κ : ℕ → ℝ, κ = fun m : ℕ =>
      (3 : ℝ) ^ ((m : ℝ) * s) * ((K₂ + 1) * (3 : ℝ) ^ (((m : ℝ) + 1) * T)) := ⟨_, rfl⟩
  have hκ0 : ∀ m, 0 < κ m := fun m => by rw [hκ]; positivity
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ → CoefficientField d Λ → ℝ, Y = fun m a => κ m * max (V m a) 0 :=
    ⟨_, rfl⟩
  have hY0 : ∀ m a, 0 ≤ Y m a := fun m a => by
    rw [hY]; exact mul_nonneg (hκ0 m).le (le_max_right _ _)
  have hYos : ∀ m, OsBound P (Y m) 1 (c * ρ ^ m) := by
    intro m
    have h := ((hVos m).max_zero_right).const_mul (hκ0 m)
    have hYm : Y m = fun a => κ m * max (V m a) 0 := by rw [hY]
    rw [hYm]
    refine h.mono_scale ?_
    have e1 : κ m * (C₆ * (3 : ℝ) ^ (-((m : ℝ) * ((s + d) / 2)))) = (K₂ + 1) * C₆ *
        (3 : ℝ) ^ ((m : ℝ) * s + ((m : ℝ) + 1) * T + -((m : ℝ) * ((s + d) / 2))) := by
      rw [hκ, Real.rpow_add h3, Real.rpow_add h3]
      ring
    have e2 : c * ρ ^ m = (K₂ + 1) * C₆ * (3 : ℝ) ^ (1 + -(((d : ℝ) - s) / 4) * m) := by
      rw [hc, hρ, ← Real.rpow_natCast, ← Real.rpow_mul h3.le, Real.rpow_add h3, Real.rpow_one]
      ring
    rw [e1, e2]
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h31 ?_)
      (mul_pos hK₂1 hC₆).le
    have := mul_le_mul_of_nonneg_left hTd (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    nlinarith
  have hYmeas : Measurable (Function.uncurry Y) :=
    (measurable_from_prod_countable_left (f := fun p : CoefficientField d Λ × ℕ => Y p.2 p.1)
      (fun m => (hYos m).1)).comp measurable_swap
  have hsumθ : Summable (fun m : ℕ => c * ρ ^ m) :=
    (summable_geometric_of_lt_one hρ0.le hρ1).mul_left c
  have hθi : Integrable (fun m : ℕ => c * ρ ^ m) Measure.count :=
    integrable_count_iff.2 (by simpa only [Real.norm_eq_abs] using hsumθ.abs)
  have hθint : ∫ m, c * ρ ^ m ∂Measure.count = c * (1 - ρ)⁻¹ := by
    rw [integral_countable hθi]
    simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0.le hρ1]
  obtain ⟨hint, hXos⟩ := osBound_integral (P := P) (μ := Measure.count) le_rfl hYmeas hY0
    measurable_from_nat hθi (by rw [hθint]; exact hcρ) hYos
  rw [hθint] at hXos
  refine ⟨fun a => ∫ m, Y m a ∂Measure.count, hXos.mono_scale (by linarith),
    fun a => integral_nonneg fun m => hY0 m a, ?_⟩
  filter_upwards [hint] with a ha m
  have hsumY : Summable (fun m => Y m a) := (integrable_count_iff.1 ha).of_norm
  have hXa : ∫ m, Y m a ∂Measure.count = ∑' m, Y m a := by
    rw [integral_countable ha]
    simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  have hYX : Y m a ≤ ∫ m, Y m a ∂Measure.count := by
    rw [hXa]; exact hsumY.le_tsum m (fun j _ => hY0 j a)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = coarseDeviation P m a := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hEdef]; exact sq_nonneg _
  rw [← hEdef]
  -- the choice of `r`
  refine ⟨(3 : ℝ) ^ (-(((m : ℝ) + 1) * (T / (4 + d)))), by positivity,
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos (by positivity)), ?_⟩
  have hrβ : ((3 : ℝ) ^ (-(((m : ℝ) + 1) * (T / (4 + d))))) ^ β₁ ≤
      (3 : ℝ) ^ (-((m : ℝ) * (β₁ * α / (4 * (4 + d)) * ((d : ℝ) - s)))) := by
    rw [← Real.rpow_mul h3.le, hβT]
    refine Real.rpow_le_rpow_of_exponent_le h31 ?_
    have : (m : ℝ) * (β₁ * T / (4 + d)) ≤ ((m : ℝ) + 1) * (T / (4 + d)) * β₁ := by
      rw [show ((m : ℝ) + 1) * (T / (4 + d)) * β₁ = (m : ℝ) * (β₁ * T / (4 + d)) +
        β₁ * T / (4 + d) by ring]
      have : 0 ≤ β₁ * T / (4 + d) := by positivity
      linarith
    linarith
  have hrk : ((3 : ℝ) ^ (-(((m : ℝ) + 1) * (T / (4 + d))))) ^ (-(4 + (d : ℝ))) =
      (3 : ℝ) ^ (((m : ℝ) + 1) * T) := by
    rw [← Real.rpow_mul h3.le]
    congr 1
    field_simp
  rw [hrk]
  -- the square root
  have hx3 : ((3 : ℝ) ^ m)⁻¹ = (3 : ℝ) ^ (-(m : ℝ)) := by
    rw [Real.rpow_neg h3.le, Real.rpow_natCast]
  have hsq := sqrt_sq_add_le (x := ((3 : ℝ) ^ m)⁻¹) (by positivity) hE0
  have hVa := hVle m a
  rw [← hEdef] at hVa
  have hexp : (3 : ℝ) ^ (-((m : ℝ) * α * ((d : ℝ) - (s + d) / 2))) =
      (3 : ℝ) ^ (-((m : ℝ) * (2 * T))) := by
    congr 1; rw [hT]; ring
  rw [hexp] at hVa
  have hm3 : ((3 : ℝ) ^ m)⁻¹ ≤ (3 : ℝ) ^ (-((m : ℝ) * (2 * T))) := by
    rw [hx3]
    refine Real.rpow_le_rpow_of_exponent_le h31 ?_
    have : (m : ℝ) * (2 * T) ≤ (m : ℝ) * 1 := mul_le_mul_of_nonneg_left (by linarith) hm0
    linarith
  have hZ : Real.sqrt (((3 : ℝ) ^ m)⁻¹ ^ 2 + E) ≤
      (1 + C₆) * (3 : ℝ) ^ (-((m : ℝ) * (2 * T))) + max (V m a) 0 := by
    have := le_max_left (V m a) 0
    nlinarith [hsq, hVa, hm3]
  -- the deterministic and random parts
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = (3 : ℝ) ^ (((m : ℝ) + 1) * T) := ⟨_, rfl⟩
  rw [← hR]
  have hR0 : 0 < R := by rw [hR]; positivity
  have h3T : (3 : ℝ) ^ T ≤ 3 := by
    calc (3 : ℝ) ^ T ≤ (3 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h31 (by linarith)
      _ = 3 := Real.rpow_one 3
  have hR3 : R * (3 : ℝ) ^ (-((m : ℝ) * (2 * T))) ≤
      3 * (3 : ℝ) ^ (-((m : ℝ) * (β₁ * α / (4 * (4 + d)) * ((d : ℝ) - s)))) := by
    rw [hR, ← Real.rpow_add h3, hβT]
    calc (3 : ℝ) ^ (((m : ℝ) + 1) * T + -((m : ℝ) * (2 * T))) =
          (3 : ℝ) ^ T * (3 : ℝ) ^ (-((m : ℝ) * T)) := by
          rw [← Real.rpow_add h3]; congr 1; ring
      _ ≤ 3 * (3 : ℝ) ^ (-((m : ℝ) * (β₁ * T / (4 + d)))) := by
          refine mul_le_mul h3T (Real.rpow_le_rpow_of_exponent_le h31 ?_) (by positivity)
            (by norm_num)
          have := mul_le_mul_of_nonneg_left hβT' hm0
          linarith
  -- the random part
  have hS : (3 : ℝ) ^ (-((m : ℝ) * s)) * (3 : ℝ) ^ ((m : ℝ) * s) = 1 := by
    rw [← Real.rpow_add h3, neg_add_cancel, Real.rpow_zero]
  have hYm : Y m a = (3 : ℝ) ^ ((m : ℝ) * s) * ((K₂ + 1) * R) * max (V m a) 0 := by
    rw [hY, hκ, hR]
  have hmx : 0 ≤ max (V m a) 0 := le_max_right _ _
  have h4 : K₂ * R * max (V m a) 0 ≤ (3 : ℝ) ^ (-((m : ℝ) * s)) * Y m a := by
    rw [hYm]
    calc K₂ * R * max (V m a) 0 ≤ (K₂ + 1) * R * max (V m a) 0 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hR0.le) hmx
      _ = ((3 : ℝ) ^ (-((m : ℝ) * s)) * (3 : ℝ) ^ ((m : ℝ) * s)) *
          ((K₂ + 1) * R * max (V m a) 0) := by rw [hS, one_mul]
      _ = _ := by ring
  have h5 : (3 : ℝ) ^ (-((m : ℝ) * s)) * Y m a ≤
      (3 : ℝ) ^ (-((m : ℝ) * s)) * ∫ m, Y m a ∂Measure.count :=
    mul_le_mul_of_nonneg_left hYX (by positivity)
  -- the square root
  have hZ : Real.sqrt (((3 : ℝ) ^ m)⁻¹ ^ 2 + E) ≤
      (1 + C₆) * (3 : ℝ) ^ (-((m : ℝ) * (2 * T))) + max (V m a) 0 := by
    calc Real.sqrt (((3 : ℝ) ^ m)⁻¹ ^ 2 + E) ≤ ((3 : ℝ) ^ m)⁻¹ + Real.sqrt E := hsq
      _ ≤ (3 : ℝ) ^ (-((m : ℝ) * (2 * T))) +
          (C₆ * (3 : ℝ) ^ (-((m : ℝ) * (2 * T))) + max (V m a) 0) :=
          add_le_add hm3 (hVa.trans (add_le_add le_rfl (le_max_left _ _)))
      _ = _ := by ring
  obtain ⟨D, hD⟩ : ∃ D : ℝ,
      D = (3 : ℝ) ^ (-((m : ℝ) * (β₁ * α / (4 * (4 + d)) * ((d : ℝ) - s)))) := ⟨_, rfl⟩
  rw [← hD] at hrβ hR3 ⊢
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hSX : 0 ≤ (3 : ℝ) ^ (-((m : ℝ) * s)) * ∫ m, Y m a ∂Measure.count :=
    mul_nonneg (by positivity) (integral_nonneg fun m => hY0 m a)
  have h2 : K₂ * R * Real.sqrt (((3 : ℝ) ^ m)⁻¹ ^ 2 + E) ≤
      K₂ * (1 + C₆) * (3 * D) + (3 : ℝ) ^ (-((m : ℝ) * s)) * ∫ m, Y m a ∂Measure.count := by
    calc K₂ * R * Real.sqrt (((3 : ℝ) ^ m)⁻¹ ^ 2 + E) ≤
          K₂ * R * ((1 + C₆) * (3 : ℝ) ^ (-((m : ℝ) * (2 * T))) + max (V m a) 0) :=
          mul_le_mul_of_nonneg_left hZ (mul_nonneg hK₂ hR0.le)
      _ = K₂ * (1 + C₆) * (R * (3 : ℝ) ^ (-((m : ℝ) * (2 * T)))) + K₂ * R * max (V m a) 0 := by
          ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hR3 (mul_nonneg hK₂ (by linarith)))
          (h4.trans h5)
  have h1 := mul_le_mul_of_nonneg_left hrβ hK₁
  have e : (K₁ + 3 * K₂ * (1 + C₆) + 1 + c * (1 - ρ)⁻¹) *
      (D + (3 : ℝ) ^ (-((m : ℝ) * s)) * ∫ m, Y m a ∂Measure.count) =
        K₁ * D + (K₂ * (1 + C₆) * (3 * D) +
          (3 : ℝ) ^ (-((m : ℝ) * s)) * ∫ m, Y m a ∂Measure.count) +
          ((1 + c * (1 - ρ)⁻¹) * D + (K₁ + 3 * K₂ * (1 + C₆) + c * (1 - ρ)⁻¹) *
            ((3 : ℝ) ^ (-((m : ℝ) * s)) * ∫ m, Y m a ∂Measure.count)) := by ring
  calc K₁ * ((3 : ℝ) ^ (-(((m : ℝ) + 1) * (T / (4 + d))))) ^ β₁ +
        K₂ * R * Real.sqrt (((3 : ℝ) ^ m)⁻¹ ^ 2 + E) ≤
        K₁ * D + (K₂ * (1 + C₆) * (3 * D) +
          (3 : ℝ) ^ (-((m : ℝ) * s)) * ∫ m, Y m a ∂Measure.count) := add_le_add h1 h2
    _ ≤ _ := by
        rw [e]
        exact le_add_of_nonneg_right (add_nonneg (mul_nonneg (by linarith) hD0)
          (mul_nonneg (by linarith) hSX))

end QSH
