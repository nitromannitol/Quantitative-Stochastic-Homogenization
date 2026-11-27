import QuantitativeStochasticHomogenization.Ch03.Sec03.Implication346
import QuantitativeStochasticHomogenization.Ch03.Sec03.Equation352

/-!
# Statement `(ii)₁` of Theorem 3.8

Armstrong–Kuusi–Mourrat, Theorem 3.8, statement `(ii)_k` for `k = 1`, through (3.46): `(i)₀`,
`(ii)₀` and `(iii)₀` (Theorem 3.8 for `k = 0`, `theorem_3_8_zero`) and (3.52) give, above a random
scale `X ≤ O_s(C)` and for almost every coefficient field, for every `p ∈ Ā_1` some `u ∈ A_1` with
`‖u - p‖_{L̲²(B_R)} ≤ C R^{-δ} ‖p‖_{L̲²(B_R)}` for every `R ≥ X` (`theorem_3_8_ii_one`).
-/

open MeasureTheory Filter Set Topology

noncomputable section

namespace QSH

variable {d : ℕ}

theorem solutionGrowthSpace_mono {Λ : ℝ} {a : CoefficientField d Λ} {k k' : ℕ} (hkk : k ≤ k')
    {u : Vec d → ℝ} (hu : u ∈ solutionGrowthSpace a k) : u ∈ solutionGrowthSpace a k' := by
  refine ⟨hu.1, tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu.2 ?_ ?_⟩
  · filter_upwards [eventually_gt_atTop 0] with r hr
    exact mul_nonneg (by positivity) (scalarRms_nonneg _ _)
  · filter_upwards [eventually_ge_atTop 1] with r hr
    refine mul_le_mul_of_nonneg_right ?_ (scalarRms_nonneg _ _)
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hr (by omega))

/-- **Theorem 3.8 `(ii)₁`**, for `d ≥ 2`, `Λ > 1` and `s ∈ (0, d)`: there are `δ ∈ (0, ½]` and `C`
such that, for every law satisfying the assumptions, a random variable `X ≥ 1` with `X ≤ O_s(C)`
satisfies, for almost every coefficient field: for every `p ∈ Ā_1` there is `u ∈ A_1` with
`‖u - p‖_{L̲²(B_R)} ≤ C R^{-δ} ‖p‖_{L̲²(B_R)}` for every `R ≥ X`. -/
theorem theorem_3_8_ii_one (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) {s : ℝ} (hs : 0 < s)
    (hsd : s < d) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∃ C CX : ℝ, 0 ≤ C ∧ 0 < CX ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∃ X : CoefficientField d Λ → ℝ, OsBound P X s CX ∧ (∀ a, 1 ≤ X a) ∧ ∀ᵐ a ∂P,
        ∀ p ∈ harmonicPolys (homogenizedMatrix P) 1, ∃ u ∈ solutionGrowthSpace a 1,
          ∀ R : ℝ, X a ≤ R → scalarRms volume (ball 0 R) (fun x => u x - p x) ≤
            C * R ^ (-δ) * scalarRms volume (ball 0 R) p := by
  obtain ⟨C₀, hC₀, h380⟩ := theorem_3_8_zero hd hΛ hs hsd
  obtain ⟨γ, hγ, C52, CX52, hCX52, hC52, h352⟩ := equation_3_52 hd hΛ hs hsd
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min γ (1 / 2) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; exact lt_min hγ (by norm_num)
  have hδ2 : δ ≤ 1 / 2 := by rw [hδdef]; exact min_le_right _ _
  have hδγ : δ ≤ γ := by rw [hδdef]; exact min_le_left _ _
  obtain ⟨K, hK, h346⟩ := implication_346_homogeneous (d := d) (Λ := Λ) (k := 1) le_rfl hδ0
    (by linarith) (hC52 1) hC₀.le
  obtain ⟨C27, hC27, h27⟩ := scalarRms_homogeneousComponents_zero (d := d) 1
  refine ⟨δ, hδ0, hδ2, Real.sqrt (2 ^ d) * K * 2 * C27, (2 : ℝ) ^ s⁻¹ * max C₀ CX52,
    by positivity, by positivity, fun P hP => ?_⟩
  obtain ⟨X₀, hX₀os, hX₀1, hX₀ae⟩ := h380 P hP
  obtain ⟨X₅, hX₅os, hX₅1, hX₅ae⟩ := h352 P hP
  refine ⟨fun a => max (X₀ a) (X₅ a), osBound_max hX₀os hX₅os,
    fun a => le_max_of_le_left (hX₀1 a), ?_⟩
  filter_upwards [hX₀ae, hX₅ae] with a ha0 ha5
  obtain ⟨hi0, -, hiii0⟩ := ha0
  intro p hp
  obtain ⟨r₀, hr₀def⟩ : ∃ r₀, r₀ = max (X₀ a) (X₅ a) := ⟨_, rfl⟩
  have hr₀1 : 1 ≤ r₀ := by rw [hr₀def]; exact le_max_of_le_left (hX₀1 a)
  have hr₀ : 0 < r₀ := by linarith
  have hX₀r : X₀ a ≤ r₀ := by rw [hr₀def]; exact le_max_left _ _
  have hX₅r : X₅ a ≤ r₀ := by rw [hr₀def]; exact le_max_right _ _
  obtain ⟨⟨Q, hQ, hQe⟩, hph⟩ := hp
  -- the homogeneous parts of `p`
  have hℓA := homogeneousComponent_mem_harmonicPolys ⟨⟨Q, hQ, hQe⟩, hph⟩ hQ hQe 1
  have hℓ : ∀ t : ℝ, 0 < t → ∀ x, MvPolynomial.eval (t • x) (MvPolynomial.homogeneousComponent 1 Q) =
      t ^ 1 * MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 Q) := fun t _ x =>
    PDE.eval_smul_of_isHomogeneous (MvPolynomial.homogeneousComponent_isHomogeneous 1 Q) t x
  have hc0 : ∀ x, MvPolynomial.eval x (MvPolynomial.homogeneousComponent 0 Q) = Q.coeff 0 := fun x => by
    rw [MvPolynomial.homogeneousComponent_zero, MvPolynomial.eval_C]
  have hpdec : ∀ x, p x = Q.coeff 0 + MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 Q) :=
    fun x => by
      rw [hQe x, eval_eq_sum_homogeneousComponent hQ, Finset.sum_range_succ, Finset.sum_range_one,
        hc0]
  obtain ⟨uℓ, huℓ, hbℓ⟩ := h346 hΛ.le a (homogenizedMatrix P)
    (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 Q)) hℓA hℓ r₀ 0 hr₀ le_rfl
    (by simp)
    (fun r hr => by
      have hr1 : 1 ≤ r := hr₀1.trans hr
      obtain ⟨u, hu, hb⟩ := ha5 1 r (hX₅r.trans hr) _ hℓA
      refine ⟨u, hu, hb.trans ?_⟩
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (hC52 1))
        (scalarRms_nonneg _ _)
      exact Real.rpow_le_rpow_of_exponent_le hr1 (by linarith))
    (fun R hR w hw => by
      obtain ⟨hwL2, g, hg, hwg, hdiv⟩ := hw
      obtain ⟨φ, hφ, hb⟩ := hiii0 R (hX₀r.trans hR) w g hwL2 hg hwg hdiv
      refine ⟨φ, hφ, fun r hr hrR => (hb r (hX₀r.trans hr) hrR).trans ?_⟩
      have hR0 : 0 < R := lt_of_lt_of_le hr₀ hR
      have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
      have hx0 : 0 < r / R := div_pos hr0 hR0
      have hx1 : r / R ≤ 1 := (div_le_one hR0).2 hrR
      have hpow : r / R ≤ (r / R) ^ (((1 : ℕ) : ℝ) - δ / 2) := by
        conv_lhs => rw [← Real.rpow_one (r / R)]
        exact Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by push_cast; linarith)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC₀.le)
        (scalarRms_nonneg _ _))
    (fun φ hφ => by
      obtain ⟨q, hq, hφq⟩ := hi0 φ hφ
      refine ⟨q, hq, fun R hR => ?_⟩
      rw [zero_mul, zero_mul]
      have h0 : scalarRms volume (ball 0 R) (fun x => φ x - q x) =
          scalarRms volume (ball 0 R) (fun _ => (0 : ℝ)) :=
        scalarRms_congr_ae (ae_restrict_of_ae (by filter_upwards [hφq] with x hx; rw [hx, sub_self]))
      rw [h0]
      unfold scalarRms
      simp)
  -- the solution and the estimate
  have hcA : (fun _ : Vec d => Q.coeff 0) ∈ solutionGrowthSpace a 1 :=
    solutionGrowthSpace_mono (by norm_num) (const_mem_solutionGrowthSpace a _)
  refine ⟨fun x => uℓ x + Q.coeff 0, add_mem_solutionGrowthSpace huℓ hcA, fun R hR' => ?_⟩
  have hR : r₀ ≤ R := by rw [hr₀def]; exact hR'
  have hR0 : 0 < R := lt_of_lt_of_le hr₀ hR
  have e : (fun x => (uℓ x + Q.coeff 0) - p x) =
      fun x => uℓ x - MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 Q) := by
    funext x; rw [hpdec x]; ring
  rw [e]
  classical
  have hex : ∃ j : ℕ, R ≤ 2 ^ j * r₀ := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (R / r₀) (one_lt_two : (1 : ℝ) < 2)
    exact ⟨j, by rw [div_lt_iff₀ hr₀] at hj; linarith⟩
  obtain ⟨j, hjdef⟩ : ∃ j, j = Nat.find hex := ⟨_, rfl⟩
  have hj1 : R ≤ 2 ^ j * r₀ := by rw [hjdef]; exact Nat.find_spec hex
  have hj2 : 2 ^ j * r₀ ≤ 2 * R := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0, pow_zero, one_mul]; linarith
    · have h := Nat.find_min hex (show j - 1 < Nat.find hex by rw [← hjdef]; omega)
      push Not at h
      have e2 : (2 : ℝ) ^ j = 2 * 2 ^ (j - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hpos]
      rw [e2]; nlinarith
  have hρj : 0 < (2 : ℝ) ^ j * r₀ := by positivity
  have hmem : MemLp (fun x => uℓ x - MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 Q)) 2
      (volume.restrict (ball (0 : Vec d) (2 ^ j * r₀))) :=
    (huℓ.1 _ hρj).1.sub (hℓA.2 _ hρj).1
  have h1 := scalarRms_ball_le hR0 hj1 hmem
  have hratio : Real.sqrt ((2 ^ j * r₀ / R) ^ d) ≤ Real.sqrt (2 ^ d) :=
    Real.sqrt_le_sqrt (pow_le_pow_left₀ (by positivity) (by rw [div_le_iff₀ hR0]; linarith) d)
  have hpow : (2 ^ j * r₀ : ℝ) ^ (-δ) ≤ R ^ (-δ) :=
    Real.rpow_le_rpow_of_nonpos hR0 hj1 (by linarith)
  have hhom : scalarRms volume (ball 0 (2 ^ j * r₀))
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 Q)) ≤
      2 * scalarRms volume (ball 0 R)
        (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 Q)) := by
    have ht : 0 < 2 ^ j * r₀ / R := by positivity
    have h := scalarRms_ball_homogeneous (q := fun x =>
      MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 Q)) hℓ (r := R) ht
    rw [div_mul_cancel₀ _ hR0.ne', pow_one] at h
    rw [h]
    exact mul_le_mul_of_nonneg_right (by rw [div_le_iff₀ hR0]; linarith) (scalarRms_nonneg _ _)
  have hcomp : scalarRms volume (ball 0 R)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 Q)) ≤
      C27 * scalarRms volume (ball 0 R) p := by
    obtain ⟨h1', h2'⟩ := h27 Q hQ R hR0
    have hp : (fun x => MvPolynomial.eval x Q) = p := funext fun x => (hQe x).symm
    rw [hp] at h2'
    refine le_trans ?_ h2'
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    exact le_add_of_nonneg_left (scalarRms_nonneg _ _)
  have hs := Real.sqrt_nonneg ((2 : ℝ) ^ d)
  have hRδ : 0 ≤ R ^ (-δ) := Real.rpow_nonneg hR0.le _
  calc scalarRms volume (ball 0 R)
        (fun x => uℓ x - MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 Q))
      ≤ Real.sqrt (2 ^ d) * (K * (2 ^ j * r₀) ^ (-δ) * scalarRms volume (ball 0 (2 ^ j * r₀))
          (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 Q))) :=
        h1.trans (mul_le_mul hratio (hbℓ j) (scalarRms_nonneg _ _) hs)
    _ ≤ Real.sqrt (2 ^ d) * (K * R ^ (-δ) * (2 * (C27 * scalarRms volume (ball 0 R) p))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left hpow hK)
          (hhom.trans (mul_le_mul_of_nonneg_left hcomp (by norm_num))) (scalarRms_nonneg _ _)
          (mul_nonneg hK hRδ)) hs
    _ = Real.sqrt (2 ^ d) * K * 2 * C27 * R ^ (-δ) * scalarRms volume (ball 0 R) p := by ring

end QSH
