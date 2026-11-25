import QuantitativeStochasticHomogenization.Ch01.Sec05.TwoScaleConstants
import QuantitativeStochasticHomogenization.Ch01.Sec05.SmoothCutoff

/-!
# The data of the two-scale expansion

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.5, the objects of the proof of Theorem 1.17:

* the multipliers `G_j = η_r ∂_j ũ` of the two-scale expansion, with the cutoff `η_r` of (1.60)
  and the smooth function `ũ` of the interior estimates (1.61), satisfy `∑_j G_j e_j = η_r ∇u`
  almost everywhere and `|∇^k G_j| ≤ K r^{-2-d/2} ‖∇u‖_{L²(U)}` for `k ≤ 2`
  (`exists_multipliers`);
* the cube `V = ε □_m`, `m = m(ε)`, contains `U ⊆ □_0` and `1 ≤ |V| ≤ 3^d`
  (`volume_smul_triadicCube_bounds`).
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal Pointwise

noncomputable section

namespace QSH

namespace TwoScale

variable {d : ℕ} {Λ : ℝ}

/-- An almost everywhere property near every point of `K` holds almost everywhere on `K`. -/
theorem ae_imp_of_forall_mem_exists {K : Set (Vec d)} {p : Vec d → Prop}
    (h : ∀ x ∈ K, ∃ V : Set (Vec d), IsOpen V ∧ x ∈ V ∧ ∀ᵐ y ∂(volume.restrict V), p y) :
    ∀ᵐ y ∂volume, y ∈ K → p y := by
  choose! V hVo hxV hVp using h
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun x : K => V x.1)
    (fun x => hVo x.1 x.2)
  have hae : ∀ᵐ y ∂(volume.restrict (⋃ i ∈ T, V i.1)), p y :=
    (ae_restrict_biUnion_iff (fun i : K => V i.1) hTc p).2 fun i _ => hVp i.1 i.2
  have hmeas : MeasurableSet (⋃ i ∈ T, V i.1) :=
    (isOpen_biUnion fun i _ => hVo i.1 i.2).measurableSet
  rw [ae_restrict_iff' hmeas] at hae
  filter_upwards [hae] with y hy hyK
  apply hy
  rw [hTU]
  exact mem_iUnion.2 ⟨⟨y, hyK⟩, hxV y hyK⟩

theorem euclideanNorm_le_of_norm {x : Vec d} : ‖x‖ ≤ euclideanNorm x := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  exact abs_apply_le_sqrt_euclideanSq x i

set_option maxHeartbeats 400000 in
/-- **The multipliers of the two-scale expansion.** -/
theorem exists_multipliers (hd : 0 < d) (hΛ : 1 ≤ Λ) {U : Set (Vec d)} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) {x₀ : Vec d} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : ∀ y, euclideanNorm (y - x₀) < ρ → y ∈ U) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (A : Mat d), A.transpose = A →
      (∀ ξ, euclideanSq ξ ≤ dot ξ (A.mulVec ξ)) →
      (∀ ξ, dot ξ (A.mulVec ξ) ≤ Λ * euclideanSq ξ) →
      ∀ (u : Vec d → ℝ) (g : Vec d → Vec d), MemLp u 2 (volume.restrict U) →
      MemLp g 2 (volume.restrict U) → HasWeakGradient U u g →
      HasWeakDivergence U (fun x => A.mulVec (g x)) (fun _ => 0) →
      ∀ r : ℝ, 0 < r → r < 1 → ∃ (η : Vec d → ℝ) (G : Fin d → Vec d → ℝ),
        Continuous η ∧ (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧
        volume.real {x ∈ U | η x ≠ 1} ≤ d * r * volume.real U ∧
        (∀ j, ContDiff ℝ (⊤ : ℕ∞) (G j)) ∧ (∀ j, HasCompactSupport (G j)) ∧
        (∀ j, tsupport (G j) ⊆ U) ∧
        (∀ᵐ x ∂(volume.restrict U), (fun j => G j x) = η x • g x) ∧
        (∀ j x, |G j x| ≤ K * r⁻¹ ^ 2 * Real.sqrt (r⁻¹ ^ d) *
          Real.sqrt (∫ x in U, euclideanSq (g x))) ∧
        (∀ j i x, |coordinateDerivative i (G j) x| ≤ K * r⁻¹ ^ 2 * Real.sqrt (r⁻¹ ^ d) *
          Real.sqrt (∫ x in U, euclideanSq (g x))) ∧
        (∀ j i k x, |coordinateDerivative k (coordinateDerivative i (G j)) x| ≤
          K * r⁻¹ ^ 2 * Real.sqrt (r⁻¹ ^ d) * Real.sqrt (∫ x in U, euclideanSq (g x))) := by
  obtain ⟨Cη, hCη, hcut⟩ := exists_cutoff_of_convex hUo hUb hUc hρ hball
  obtain ⟨CI, hCI, hint⟩ := exists_smooth_interior_bound_of_constant hd hΛ
  set q : ℝ := 4 / ρ with hq
  have hq0 : 0 ≤ q := by positivity
  set a : ℝ := Real.sqrt (q ^ d) with ha
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  refine ⟨CI * a * (1 + Cη + q + 2 * Cη * q + q ^ 2), by positivity,
    fun A hAt hA0 hA1 u g hu hg hw hdiv r hr hr1 => ?_⟩
  obtain ⟨η, hη, hηc, hηU, hη01, hηd, hηdd, hηvol⟩ := hcut r hr hr1
  have hρr : 0 < ρ * r / 4 := by positivity
  obtain ⟨ũ, hũ, hũb⟩ := hint A hAt hA0 hA1 U hUo u g hu hg hw hdiv (ρ * r / 4) hρr
  set Ng := Real.sqrt (∫ x in U, euclideanSq (g x)) with hNg
  have hNg0 : 0 ≤ Ng := Real.sqrt_nonneg _
  set t : ℝ := r⁻¹ with ht
  have ht1 : 1 ≤ t := by rw [ht]; exact one_le_inv_iff₀.2 ⟨hr, hr1.le⟩
  have ht0 : 0 ≤ t := by linarith
  set σ : ℝ := Real.sqrt (t ^ d) with hσ
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hρinv : (ρ * r / 4)⁻¹ = q * t := by rw [hq, ht]; field_simp
  have hsq : Real.sqrt ((ρ * r / 4)⁻¹ ^ d) = a * σ := by
    rw [hρinv, mul_pow, Real.sqrt_mul (pow_nonneg hq0 d)]
  -- the bounds of `ũ` on the support of the cutoff
  have hmem : ∀ x ∈ tsupport η, ∀ z, euclideanNorm (z - x) < ρ * r / 4 → z ∈ U := hηU
  set B₀ := CI * (a * σ) * Ng with hB₀
  set B₁ := CI * (q * t) * (a * σ) * Ng with hB₁
  set B₂ := CI * (q * t) ^ 2 * (a * σ) * Ng with hB₂
  have hB₀0 : 0 ≤ B₀ := by positivity
  have hB₁0 : 0 ≤ B₁ := by positivity
  have hB₂0 : 0 ≤ B₂ := by positivity
  have hE₁ : 0 ≤ Cη / r := by positivity
  have hE₂ : 0 ≤ Cη / r ^ 2 := by positivity
  set G : Fin d → Vec d → ℝ := fun j x => η x * coordinateDerivative j ũ x with hG
  have hGs : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (G j) := fun j =>
    hη.mul (contDiff_coordinateDerivative_top hũ j)
  have hmult : ∀ j, (∀ x, |G j x| ≤ B₀) ∧
      (∀ i x, |coordinateDerivative i (G j) x| ≤ Cη / r * B₀ + B₁) ∧
      (∀ i k x, |coordinateDerivative k (coordinateDerivative i (G j)) x| ≤
        Cη / r ^ 2 * B₀ + 2 * (Cη / r * B₁) + B₂) := fun j =>
    abs_multiplier_le hη (contDiff_coordinateDerivative_top hũ j) hE₁ hE₂ hB₀0 hB₁0 hB₂0
      (fun x => by rw [abs_le]; constructor <;> linarith [hη01 x])
      hηd hηdd
      (fun x hx => by
        have h := ((hũb x (hmem x hx)).2.1 j)
        rw [hsq] at h; exact h)
      (fun x hx i => by
        have h := ((hũb x (hmem x hx)).2.2.1 j i)
        rw [hsq, hρinv] at h; rw [hB₁]; linarith)
      (fun x hx i k => by
        have h := ((hũb x (hmem x hx)).2.2.2 j i k)
        rw [hsq, hρinv] at h; rw [hB₂]; linarith)
  -- the constants
  set Kt := CI * a * (1 + Cη + q + 2 * Cη * q + q ^ 2) * t ^ 2 * σ * Ng with hKt
  have hCηr : Cη / r = Cη * t := by rw [ht, div_eq_mul_inv]
  have hCηr2 : Cη / r ^ 2 = Cη * t ^ 2 := by rw [ht, inv_pow, div_eq_mul_inv]
  have ht2 : t ≤ t ^ 2 := by nlinarith
  set P := 1 + Cη + q + 2 * Cη * q + q ^ 2 with hP
  have hW0 : 0 ≤ CI * a * σ * Ng := by positivity
  have hKt2 : Kt = (CI * a * σ * Ng) * (P * t ^ 2) := by rw [hKt]; ring
  have ht2' : 1 ≤ t ^ 2 := one_le_pow₀ ht1
  have hP1 : 1 ≤ P := by
    rw [hP]
    have : 0 ≤ Cη + q + 2 * Cη * q + q ^ 2 := by positivity
    linarith
  have hb0 : B₀ ≤ Kt := by
    rw [hKt2, show B₀ = (CI * a * σ * Ng) * 1 by rw [hB₀]; ring]
    refine mul_le_mul_of_nonneg_left ?_ hW0
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ P * t ^ 2 := mul_le_mul hP1 ht2' zero_le_one (by linarith)
  have hb1 : Cη / r * B₀ + B₁ ≤ Kt := by
    rw [hKt2, show Cη / r * B₀ + B₁ = (CI * a * σ * Ng) * ((Cη + q) * t) by
      rw [hCηr, hB₀, hB₁]; ring]
    refine mul_le_mul_of_nonneg_left ?_ hW0
    have hCq : 0 ≤ Cη + q := by positivity
    have hle : Cη + q ≤ P := by
      rw [hP]; have : 0 ≤ 1 + 2 * Cη * q + q ^ 2 := by positivity
      linarith
    calc (Cη + q) * t ≤ (Cη + q) * t ^ 2 := mul_le_mul_of_nonneg_left ht2 hCq
      _ ≤ P * t ^ 2 := mul_le_mul_of_nonneg_right hle (by positivity)
  have hb2 : Cη / r ^ 2 * B₀ + 2 * (Cη / r * B₁) + B₂ ≤ Kt := by
    rw [hKt2, show Cη / r ^ 2 * B₀ + 2 * (Cη / r * B₁) + B₂ =
        (CI * a * σ * Ng) * ((Cη + 2 * Cη * q + q ^ 2) * t ^ 2) by
      rw [hCηr, hCηr2, hB₀, hB₁, hB₂]; ring]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (by positivity)) hW0
    rw [hP]; have : 0 ≤ 1 + q := by positivity
    linarith
  have hKt' : Kt = CI * a * (1 + Cη + q + 2 * Cη * q + q ^ 2) * r⁻¹ ^ 2 *
      Real.sqrt (r⁻¹ ^ d) * Real.sqrt (∫ x in U, euclideanSq (g x)) := by rw [hKt]
  -- the gradient of `ũ` on the support of `η`
  have hae : ∀ᵐ x ∂(volume.restrict U), (fun j => G j x) = η x • g x := by
    have h := ae_imp_of_forall_mem_exists (K := tsupport η)
      (p := fun y => gradient ũ y = g y) fun x hx => (hũb x (hmem x hx)).1
    refine ae_restrict_of_ae ?_
    filter_upwards [h] with x hx
    funext j
    by_cases hxη : x ∈ tsupport η
    · have := congrFun (hx hxη) j
      simp only [hG, Pi.smul_apply, smul_eq_mul]
      rw [← this]
      rfl
    · simp [hG, image_eq_zero_of_notMem_tsupport hxη]
  refine ⟨η, G, hη.continuous, hη01, hηvol, hGs, fun j => hηc.mul_right, fun j =>
    (tsupport_mul_subset_left).trans fun x hx => hmem x hx x (by
      simp [euclideanNorm, euclideanSq, dot, hρr]), hae, fun j x => ?_, fun j i x => ?_,
    fun j i k x => ?_⟩
  · exact ((hmult j).1 x).trans hb0
  · exact ((hmult j).2.1 i x).trans hb1
  · exact ((hmult j).2.2 i k x).trans hb2

/-- The cube `V = ε □_m`, `m = m(ε)`: `□_0 ⊆ V` and `1 ≤ |V| ≤ 3^d`. -/
theorem volume_smul_triadicCube_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    triadicCube d 0 ⊆ ε • triadicCube d (triadicScale ε) ∧
      1 ≤ (volume (ε • triadicCube d (triadicScale ε))).toReal ∧
      (volume (ε • triadicCube d (triadicScale ε))).toReal ≤ 3 ^ d := by
  obtain ⟨h1, h2⟩ := three_pow_triadicScale_bounds hε hε1
  set m := triadicScale ε
  refine ⟨fun x hx => ⟨ε⁻¹ • x, inv_smul_mem_triadicCube hε h1 hx, by
    show ε • ε⁻¹ • x = x
    rw [smul_inv_smul₀ hε.ne']⟩, ?_, ?_⟩ <;>
  · rw [Measure.addHaar_smul, volume_triadicCube, Module.finrank_fin_fun, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity),
      abs_of_pos (pow_pos hε d), ← mul_pow]
    have h3 : (0 : ℝ) < 3 ^ m := by positivity
    first
    | exact one_le_pow₀ (by rw [inv_le_iff_one_le_mul₀ h3] at h1; linarith [mul_comm ε (3 ^ m)])
    | refine pow_le_pow_left₀ (by positivity) ?_ d
      have := (lt_div_iff₀ h3).1 (by rw [div_eq_mul_inv]; linarith : ε < 3 / 3 ^ m) |>.le
      linarith [this]

end TwoScale

end QSH
