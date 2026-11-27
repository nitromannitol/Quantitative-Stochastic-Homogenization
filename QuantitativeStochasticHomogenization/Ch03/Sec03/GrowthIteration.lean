import QuantitativeStochasticHomogenization.Ch03.Sec03.LinearCoefficients

/-!
# One step of the growth iteration in the proof of (3.47) for `k = 1`

Armstrong–Kuusi–Mourrat, proof of (3.47) for `k = 1`, Steps 1–2. Along the radii `r_j = r₀ θ^{-j}`,
for a solution `u` in `ℝ^d` with `r^{-2} ‖u‖_{L̲²(B_r)} → 0` and `‖u‖_{L̲²(B_{r_j})} ≤ M r_j^β`
(`β ≤ 2`), the decay estimate (3.51) (polynomials of degree two) gives polynomials `p_j ∈ Ā_2` with
`‖u - p_j‖_{L̲²(B_{r_j})} ≤ K r_j^σ`, `σ = β - δ`, whose part of degree two is at most `K r_j^{σ-2}`
on the unit ball and whose parts of degree zero and one change from `j` to `j + 1` by at most
`K r_j^σ` and `K r_j^{σ-1}` (`growth_core`).
-/

open MeasureTheory Filter Set Topology

noncomputable section

namespace QSH

variable {d : ℕ}

theorem radius_rpow {θ r₀ : ℝ} (hθ0 : 0 < θ) (hr₀ : 0 < r₀) (γ : ℝ) (j : ℕ) :
    (r₀ / θ ^ j) ^ γ = r₀ ^ γ * (θ ^ (-γ)) ^ j := by
  rw [Real.div_rpow hr₀.le (pow_nonneg hθ0.le j), ← Real.rpow_natCast θ j, ← Real.rpow_mul hθ0.le,
    ← Real.rpow_natCast (θ ^ (-γ)) j, ← Real.rpow_mul hθ0.le, div_eq_mul_inv,
    ← Real.rpow_neg hθ0.le]
  congr 2
  ring

/-- Backward iteration of `y_j ≤ l y_{j+1} + K` under an a priori geometric bound. -/
theorem le_of_le_mul_succ_add {y : ℕ → ℝ} {l K B ρ : ℝ} (hl0 : 0 ≤ l) (hl1 : l < 1) (hK : 0 ≤ K)
    (hρ0 : 0 ≤ ρ) (hlρ : l * ρ < 1) (h : ∀ j, y j ≤ l * y (j + 1) + K)
    (hB : ∀ j, y j ≤ B * ρ ^ j) (j : ℕ) : y j ≤ K / (1 - l) := by
  have hiter : ∀ n : ℕ, y j ≤ l ^ n * y (j + n) + K * ∑ i ∈ Finset.range n, l ^ i := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := mul_le_mul_of_nonneg_left (h (j + n)) (pow_nonneg hl0 n)
      have e : l ^ n * (l * y (j + n + 1) + K) + K * ∑ i ∈ Finset.range n, l ^ i =
          l ^ (n + 1) * y (j + (n + 1)) + K * ∑ i ∈ Finset.range (n + 1), l ^ i := by
        rw [Finset.sum_range_succ, ← add_assoc]
        ring
      linarith
  have hsum : ∀ n : ℕ, ∑ i ∈ Finset.range n, l ^ i ≤ 1 / (1 - l) := by
    intro n
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hl0 hl1
    rw [pow_zero, ← Finset.range_eq_Ico] at h
    exact h
  have hbound : ∀ n : ℕ, y j ≤ B * ρ ^ j * (l * ρ) ^ n + K / (1 - l) := by
    intro n
    have h1 := hiter n
    have h2 : l ^ n * y (j + n) ≤ l ^ n * (B * ρ ^ (j + n)) :=
      mul_le_mul_of_nonneg_left (hB _) (pow_nonneg hl0 n)
    have h3 : K * ∑ i ∈ Finset.range n, l ^ i ≤ K * (1 / (1 - l)) :=
      mul_le_mul_of_nonneg_left (hsum n) hK
    have e : l ^ n * (B * ρ ^ (j + n)) = B * ρ ^ j * (l * ρ) ^ n := by
      rw [pow_add, mul_pow]
      ring
    rw [mul_one_div] at h3
    linarith
  have hlim : Tendsto (fun n : ℕ => B * ρ ^ j * (l * ρ) ^ n + K / (1 - l)) atTop
      (𝓝 (K / (1 - l))) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg hl0 hρ0) hlρ).const_mul (B * ρ ^ j)
    simpa using this.add_const (K / (1 - l))
  exact ge_of_tendsto hlim (Eventually.of_forall hbound)

/-- Forward iteration of `x_{j+1} ≤ x_j + A ρ^j` with `ρ > 1`. -/
theorem le_add_geom_of_succ_le {x : ℕ → ℝ} {A ρ : ℝ} (hA : 0 ≤ A) (hρ : 1 < ρ)
    (h : ∀ j, x (j + 1) ≤ x j + A * ρ ^ j) (m : ℕ) : x m ≤ x 0 + A * ρ ^ m / (ρ - 1) := by
  have hρ1 : 0 < ρ - 1 := by linarith
  induction m with
  | zero =>
    have : 0 ≤ A * ρ ^ 0 / (ρ - 1) := div_nonneg (by rw [pow_zero, mul_one]; exact hA) hρ1.le
    linarith
  | succ m ih =>
    have h1 := h m
    have e : A * ρ ^ m / (ρ - 1) + A * ρ ^ m = A * ρ ^ (m + 1) / (ρ - 1) := by
      field_simp
      ring
    linarith

theorem abs_scalarRms_sub_le {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U)) :
    |scalarRms volume U f - scalarRms volume U g| ≤ scalarRms volume U (fun x => f x - g x) := by
  have h1 := scalarRms_le_add_of_sub hf hg
  have h2 := scalarRms_le_add_of_sub hg hf
  have e : scalarRms volume U (fun x => g x - f x) = scalarRms volume U (fun x => f x - g x) := by
    have h := scalarRms_const_mul U (fun x => f x - g x) (-1)
    rw [abs_neg, abs_one, one_mul] at h
    rw [← h]
    congr 1
    funext x
    show g x - f x = -1 * (f x - g x)
    ring
  rw [e] at h2
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem scalarRms_ball_homogeneousComponent (m : ℕ) (Q : MvPolynomial (Fin d) ℝ) {r : ℝ}
    (hr : 0 < r) :
    scalarRms volume (ball 0 r)
        (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q)) =
      r ^ m * scalarRms volume (ball 0 1)
        (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q)) := by
  have h := scalarRms_ball_homogeneous
    (q := fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q))
    (fun t _ x => PDE.eval_smul_of_isHomogeneous
      (MvPolynomial.homogeneousComponent_isHomogeneous m Q) t x) (r := 1) hr
  rwa [mul_one] at h

theorem le_mul_rpow_sub_of_pow_mul_le {r N c σ : ℝ} {m : ℕ} (hr : 0 < r)
    (h : r ^ m * N ≤ c * r ^ σ) : N ≤ c * r ^ (σ - m) := by
  rw [Real.rpow_sub hr, Real.rpow_natCast, mul_div_assoc', le_div_iff₀ (pow_pos hr m)]
  linarith

theorem exists_lt_harmonicFlatness (A : Mat d) (k : ℕ) (u : Vec d → ℝ) (r : ℝ) {ε : ℝ}
    (hε : 0 < ε) : ∃ p ∈ harmonicPolys A k,
      scalarRms volume (ball 0 r) (fun x => u x - p x) < harmonicFlatness A k u r + ε := by
  have : Nonempty (harmonicPolys A k) := ⟨⟨_, zero_mem_harmonicPolys A k⟩⟩
  obtain ⟨⟨p, hp⟩, h⟩ := exists_lt_of_ciInf_lt (f := fun p : harmonicPolys A k =>
    scalarRms volume (ball 0 r) (fun x => u x - (p : Vec d → ℝ) x))
    (lt_add_of_pos_right _ hε)
  exact ⟨p, hp, h⟩

/-- (3.56)–(3.57) under a growth bound: `‖u - Ā_2‖_{L̲²(B_{r_j})} ≤ C r_j^{β-δ}`. -/
theorem flatness_le_of_growth {Λ : ℝ} {a : CoefficientField d Λ} {A : Mat d}
    {θ C₅ δ X r₀ M β : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hC₅ : 0 ≤ C₅) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hX1 : 1 ≤ X) (hXr : X ≤ r₀)
    (H50 : ∀ r : ℝ, X ≤ r → ∀ v, IsSolutionBall a r v →
      harmonicFlatness A 2 v (θ * r) ≤
        1 / 4 * θ ^ ((2 : ℝ) + 1 - δ / 2) * harmonicFlatness A 2 v r +
          C₅ * r ^ (-δ) * scalarRms volume (ball 0 r) v)
    {u : Vec d → ℝ} (hsol : ∀ R : ℝ, 0 < R → IsSolutionBall a R u) (hM : 0 ≤ M) (hβ2 : β ≤ 2)
    (hgrow : ∀ j : ℕ, scalarRms volume (ball 0 (r₀ / θ ^ j)) u ≤ M * (r₀ / θ ^ j) ^ β)
    (j : ℕ) :
    harmonicFlatness A 2 u (r₀ / θ ^ j) ≤
      4 / 3 * (C₅ * M * θ ^ (-(β - δ))) * (r₀ / θ ^ j) ^ (β - δ) := by
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = β - δ := ⟨_, rfl⟩
  rw [← hσ]
  have hr₀ : 0 < r₀ := by linarith
  have hr : ∀ j : ℕ, 0 < r₀ / θ ^ j := fun j => div_pos hr₀ (pow_pos hθ0 j)
  have hrX : ∀ j : ℕ, X ≤ r₀ / θ ^ j := fun j => by
    rw [le_div_iff₀ (pow_pos hθ0 j)]
    have : θ ^ j ≤ 1 := pow_le_one₀ hθ0.le hθ1.le
    nlinarith
  have hsucc : ∀ j : ℕ, θ * (r₀ / θ ^ (j + 1)) = r₀ / θ ^ j := fun j => by
    rw [pow_succ]
    field_simp
  have hrσ : ∀ j : ℕ, 0 < (r₀ / θ ^ j) ^ σ := fun j => Real.rpow_pos_of_pos (hr j) σ
  obtain ⟨y, hy⟩ : ∃ y : ℕ → ℝ, ∀ j, y j = harmonicFlatness A 2 u (r₀ / θ ^ j) / (r₀ / θ ^ j) ^ σ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = 1 / 4 * θ ^ ((2 : ℝ) + 1 - δ / 2 - σ) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = C₅ * M * θ ^ (-σ) := ⟨_, rfl⟩
  have hθe : ∀ e : ℝ, 0 ≤ e → θ ^ e ≤ 1 := fun e he => Real.rpow_le_one hθ0.le hθ1.le he
  have hl0 : 0 ≤ l := by rw [hl]; have := Real.rpow_nonneg hθ0.le ((2 : ℝ) + 1 - δ / 2 - σ); positivity
  have hl4 : l ≤ 1 / 4 := by
    have := hθe ((2 : ℝ) + 1 - δ / 2 - σ) (by rw [hσ]; linarith)
    rw [hl]
    linarith
  have hK0 : 0 ≤ K := by rw [hK]; exact mul_nonneg (mul_nonneg hC₅ hM) (Real.rpow_nonneg hθ0.le _)
  have hrec : ∀ j, y j ≤ l * y (j + 1) + K := by
    intro j
    have h1 := H50 (r₀ / θ ^ (j + 1)) (hrX (j + 1)) u (hsol _ (hr (j + 1)))
    rw [hsucc j] at h1
    have h2 : (r₀ / θ ^ (j + 1)) ^ (-δ) * scalarRms volume (ball 0 (r₀ / θ ^ (j + 1))) u ≤
        M * (r₀ / θ ^ (j + 1)) ^ σ := by
      calc _ ≤ (r₀ / θ ^ (j + 1)) ^ (-δ) * (M * (r₀ / θ ^ (j + 1)) ^ β) :=
            mul_le_mul_of_nonneg_left (hgrow (j + 1)) (Real.rpow_nonneg (hr _).le _)
        _ = M * (r₀ / θ ^ (j + 1)) ^ σ := by
            rw [hσ, sub_eq_neg_add, Real.rpow_add (hr _)]
            ring
    have e1 : (r₀ / θ ^ (j + 1)) ^ σ = (r₀ / θ ^ j) ^ σ * θ ^ (-σ) := by
      rw [radius_rpow hθ0 hr₀, radius_rpow hθ0 hr₀, pow_succ]
      ring
    have e2 : θ ^ ((2 : ℝ) + 1 - δ / 2) = θ ^ ((2 : ℝ) + 1 - δ / 2 - σ) * θ ^ σ := by
      rw [← Real.rpow_add hθ0]
      congr 1
      ring
    have e3 : harmonicFlatness A 2 u (r₀ / θ ^ (j + 1)) = y (j + 1) * (r₀ / θ ^ (j + 1)) ^ σ := by
      rw [hy, div_mul_cancel₀ _ (hrσ (j + 1)).ne']
    have e4 : θ ^ σ * θ ^ (-σ) = 1 := by
      rw [← Real.rpow_add hθ0, add_neg_cancel, Real.rpow_zero]
    rw [hy, div_le_iff₀ (hrσ j)]
    calc harmonicFlatness A 2 u (r₀ / θ ^ j)
        ≤ 1 / 4 * θ ^ ((2 : ℝ) + 1 - δ / 2) * harmonicFlatness A 2 u (r₀ / θ ^ (j + 1)) +
          C₅ * ((r₀ / θ ^ (j + 1)) ^ (-δ) * scalarRms volume (ball 0 (r₀ / θ ^ (j + 1))) u) := by
          rw [← mul_assoc C₅]; exact h1
      _ ≤ 1 / 4 * θ ^ ((2 : ℝ) + 1 - δ / 2) * harmonicFlatness A 2 u (r₀ / θ ^ (j + 1)) +
          C₅ * (M * (r₀ / θ ^ (j + 1)) ^ σ) :=
          add_le_add (le_refl _) (mul_le_mul_of_nonneg_left h2 hC₅)
      _ = (l * y (j + 1) + K) * (r₀ / θ ^ j) ^ σ := by
          rw [e3, e1, e2, hl, hK]
          linear_combination (1 / 4 * θ ^ ((2 : ℝ) + 1 - δ / 2 - σ) * y (j + 1) *
            (r₀ / θ ^ j) ^ σ) * e4
  have hflat0 : ∀ j, harmonicFlatness A 2 u (r₀ / θ ^ j) ≤
      scalarRms volume (ball 0 (r₀ / θ ^ j)) u := by
    intro j
    have := harmonicFlatness_le (A := A) (k := 2) u (r₀ / θ ^ j) (zero_mem_harmonicPolys A 2)
    simpa using this
  have hB : ∀ j, y j ≤ (M * r₀ ^ δ) * (θ ^ (-δ)) ^ j := by
    intro j
    rw [hy, div_le_iff₀ (hrσ j)]
    have e : (M * r₀ ^ δ) * (θ ^ (-δ)) ^ j * (r₀ / θ ^ j) ^ σ = M * (r₀ / θ ^ j) ^ β := by
      rw [mul_assoc M, ← radius_rpow hθ0 hr₀, mul_assoc, ← Real.rpow_add (hr j), hσ]
      congr 2
      ring
    rw [e]
    exact (hflat0 j).trans (hgrow j)
  have hlρ : l * θ ^ (-δ) < 1 := by
    have e : l * θ ^ (-δ) = 1 / 4 * θ ^ ((2 : ℝ) + 1 - δ / 2 - σ + -δ) := by
      rw [hl, mul_assoc, ← Real.rpow_add hθ0]
    rw [e]
    have := hθe ((2 : ℝ) + 1 - δ / 2 - σ + -δ) (by rw [hσ]; linarith)
    linarith
  have hyj := le_of_le_mul_succ_add hl0 (by linarith) hK0 (Real.rpow_nonneg hθ0.le _) hlρ hrec hB j
  have h43 : K / (1 - l) ≤ 4 / 3 * K := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hl4 hK0]
  rw [hy, div_le_iff₀ (hrσ j)] at hyj
  rw [← hK]
  calc _ ≤ K / (1 - l) * (r₀ / θ ^ j) ^ σ := hyj
    _ ≤ 4 / 3 * K * (r₀ / θ ^ j) ^ σ := mul_le_mul_of_nonneg_right h43 (hrσ j).le

/-- **One step of the growth iteration** (Steps 1–2 of the proof of (3.47), `k = 1`). -/
theorem growth_core {Λ : ℝ} {a : CoefficientField d Λ} {A : Mat d} {θ C₅ δ X r₀ M β : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hC₅ : 0 ≤ C₅) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hX1 : 1 ≤ X) (hXr : X ≤ r₀)
    (H50 : ∀ r : ℝ, X ≤ r → ∀ v, IsSolutionBall a r v →
      harmonicFlatness A 2 v (θ * r) ≤
        1 / 4 * θ ^ ((2 : ℝ) + 1 - δ / 2) * harmonicFlatness A 2 v r +
          C₅ * r ^ (-δ) * scalarRms volume (ball 0 r) v)
    {u : Vec d → ℝ} (hsol : ∀ R : ℝ, 0 < R → IsSolutionBall a R u)
    (hu2 : Tendsto (fun r : ℝ => (r ^ 2)⁻¹ * scalarRms volume (ball 0 r) u) atTop (𝓝 0))
    (hM : 0 ≤ M) (hβ2 : β ≤ 2)
    (hgrow : ∀ j : ℕ, scalarRms volume (ball 0 (r₀ / θ ^ j)) u ≤ M * (r₀ / θ ^ j) ^ β) :
    ∃ (P : ℕ → MvPolynomial (Fin d) ℝ) (K : ℝ), 0 ≤ K ∧ ∀ j : ℕ, (P j).totalDegree ≤ 2 ∧
      scalarRms volume (ball 0 (r₀ / θ ^ j)) (fun x => u x - MvPolynomial.eval x (P j)) ≤
        K * (r₀ / θ ^ j) ^ (β - δ) ∧
      scalarRms volume (ball 0 1)
          (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 2 (P j))) ≤
        K * (r₀ / θ ^ j) ^ (β - δ - 2) ∧
      scalarRms volume (ball 0 1)
          (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 0 (P j)) -
            MvPolynomial.eval x (MvPolynomial.homogeneousComponent 0 (P (j + 1)))) ≤
        K * (r₀ / θ ^ j) ^ (β - δ) ∧
      scalarRms volume (ball 0 1)
          (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 (P j)) -
            MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 (P (j + 1)))) ≤
        K * (r₀ / θ ^ j) ^ (β - δ - 1) := by
  have hr₀ : 0 < r₀ := by linarith
  have hr : ∀ j : ℕ, 0 < r₀ / θ ^ j := fun j => div_pos hr₀ (pow_pos hθ0 j)
  have hrmono : ∀ j : ℕ, r₀ / θ ^ j ≤ r₀ / θ ^ (j + 1) := fun j =>
    div_le_div_of_nonneg_left hr₀.le (pow_pos hθ0 (j + 1))
      (pow_le_pow_of_le_one hθ0.le hθ1.le (Nat.le_succ j))
  have hratio : ∀ j : ℕ, (r₀ / θ ^ (j + 1)) / (r₀ / θ ^ j) = θ⁻¹ := fun j => by
    rw [pow_succ]
    field_simp
  have hF := flatness_le_of_growth (A := A) hθ0 hθ1 hC₅ hδ0 hδ1 hX1 hXr H50 hsol hM hβ2 hgrow
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = β - δ := ⟨_, rfl⟩
  rw [← hσ]
  rw [← hσ] at hF
  have hσ2 : σ < 2 := by rw [hσ]; linarith
  obtain ⟨KF, hKF⟩ : ∃ KF, KF = 4 / 3 * (C₅ * M * θ ^ (-σ)) := ⟨_, rfl⟩
  have hKF0 : 0 ≤ KF := by
    rw [hKF]
    exact mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hC₅ hM) (Real.rpow_nonneg hθ0.le _))
  rw [← hKF] at hF
  -- near-minimizers in `Ā_2`
  have hex : ∀ j : ℕ, ∃ p ∈ harmonicPolys A 2, scalarRms volume (ball 0 (r₀ / θ ^ j))
      (fun x => u x - p x) < harmonicFlatness A 2 u (r₀ / θ ^ j) + (r₀ / θ ^ j) ^ σ :=
    fun j => exists_lt_harmonicFlatness A 2 u _ (Real.rpow_pos_of_pos (hr j) σ)
  choose p hpA hpe using hex
  choose P hPdeg hPe using fun j => (hpA j).1
  have hmemP : ∀ j (R : ℝ), MemLp (fun x => MvPolynomial.eval x (P j)) 2
      (volume.restrict (ball (0 : Vec d) R)) := fun j R => memLp_eval_ball (P j) R
  have hmemu : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball (0 : Vec d) R)) :=
    fun R hR => (hsol R hR).1
  have he : ∀ j : ℕ, scalarRms volume (ball 0 (r₀ / θ ^ j))
      (fun x => u x - MvPolynomial.eval x (P j)) ≤ (KF + 1) * (r₀ / θ ^ j) ^ σ := by
    intro j
    have e : (fun x => u x - MvPolynomial.eval x (P j)) = fun x => u x - p j x :=
      funext fun x => by rw [hPe j x]
    rw [e]
    have h1 := hpe j
    have h2 := hF j
    linarith
  -- increments of the polynomials
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = Real.sqrt ((θ⁻¹) ^ d) := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by rw [hκ]; exact Real.sqrt_nonneg _
  have hθσ : 0 ≤ θ ^ (-σ) := Real.rpow_nonneg hθ0.le _
  obtain ⟨KD, hKD⟩ : ∃ KD, KD = (KF + 1) * (1 + κ * θ ^ (-σ)) := ⟨_, rfl⟩
  have hKD0 : 0 ≤ KD := by
    rw [hKD]
    exact mul_nonneg (by linarith) (by have := mul_nonneg hκ0 hθσ; linarith)
  have hrσsucc : ∀ j : ℕ, (r₀ / θ ^ (j + 1)) ^ σ = (r₀ / θ ^ j) ^ σ * θ ^ (-σ) := fun j => by
    rw [radius_rpow hθ0 hr₀, radius_rpow hθ0 hr₀, pow_succ]
    ring
  have hdiff : ∀ j : ℕ, scalarRms volume (ball 0 (r₀ / θ ^ j))
      (fun x => MvPolynomial.eval x (P j) - MvPolynomial.eval x (P (j + 1))) ≤
        KD * (r₀ / θ ^ j) ^ σ := by
    intro j
    have h1 : scalarRms volume (ball 0 (r₀ / θ ^ j))
        (fun x => u x - MvPolynomial.eval x (P (j + 1))) ≤
        κ * scalarRms volume (ball 0 (r₀ / θ ^ (j + 1)))
          (fun x => u x - MvPolynomial.eval x (P (j + 1))) := by
      have h := scalarRms_ball_le (f := fun x => u x - MvPolynomial.eval x (P (j + 1))) (hr j)
        (hrmono j) ((hmemu _ (hr (j + 1))).sub (hmemP (j + 1) _))
      rwa [hratio j, ← hκ] at h
    have h2 : scalarRms volume (ball 0 (r₀ / θ ^ j))
        (fun x => MvPolynomial.eval x (P j) - MvPolynomial.eval x (P (j + 1))) ≤
        scalarRms volume (ball 0 (r₀ / θ ^ j)) (fun x => u x - MvPolynomial.eval x (P (j + 1))) +
        scalarRms volume (ball 0 (r₀ / θ ^ j)) (fun x => u x - MvPolynomial.eval x (P j)) := by
      calc _ = scalarRms volume (ball 0 (r₀ / θ ^ j))
            (fun x => (u x - MvPolynomial.eval x (P (j + 1))) -
              (u x - MvPolynomial.eval x (P j))) := by
            congr 1
            funext x
            ring
        _ ≤ _ := scalarRms_sub_le (f := fun x => u x - MvPolynomial.eval x (P (j + 1)))
            (g := fun x => u x - MvPolynomial.eval x (P j))
            ((hmemu _ (hr j)).sub (hmemP (j + 1) _)) ((hmemu _ (hr j)).sub (hmemP j _))
    have h4 := he (j + 1)
    rw [hrσsucc j] at h4
    have e : κ * ((KF + 1) * ((r₀ / θ ^ j) ^ σ * θ ^ (-σ))) + (KF + 1) * (r₀ / θ ^ j) ^ σ =
        KD * (r₀ / θ ^ j) ^ σ := by
      rw [hKD]
      ring
    calc _ ≤ _ := h2
      _ ≤ κ * ((KF + 1) * ((r₀ / θ ^ j) ^ σ * θ ^ (-σ))) + (KF + 1) * (r₀ / θ ^ j) ^ σ :=
          add_le_add (h1.trans (mul_le_mul_of_nonneg_left h4 hκ0)) (he j)
      _ = _ := e
  -- homogeneous parts of the increments, by (3.27)
  obtain ⟨C27, hC27, h27⟩ := scalarRms_homogeneousComponents_zero (d := d) 2
  have hcomp : ∀ j : ℕ, ∀ m ∈ Finset.range 3, (r₀ / θ ^ j) ^ m * scalarRms volume (ball 0 1)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m (P j)) -
        MvPolynomial.eval x (MvPolynomial.homogeneousComponent m (P (j + 1)))) ≤
        C27 * KD * (r₀ / θ ^ j) ^ σ := by
    intro j m hm
    have hD : (P j - P (j + 1)).totalDegree ≤ 2 :=
      (MvPolynomial.totalDegree_sub _ _).trans (max_le (hPdeg j) (hPdeg (j + 1)))
    have h2 := (h27 (P j - P (j + 1)) hD _ (hr j)).2
    have hsingle := Finset.single_le_sum (f := fun m => scalarRms volume (ball 0 (r₀ / θ ^ j))
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m (P j - P (j + 1)))))
      (fun i _ => scalarRms_nonneg _ _) hm
    beta_reduce at hsingle
    rw [scalarRms_ball_homogeneousComponent m _ (hr j)] at hsingle
    have e1 : (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m (P j - P (j + 1)))) =
        fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m (P j)) -
          MvPolynomial.eval x (MvPolynomial.homogeneousComponent m (P (j + 1))) := by
      funext x
      rw [map_sub, map_sub]
    have e2 : (fun x => MvPolynomial.eval x (P j - P (j + 1))) =
        fun x => MvPolynomial.eval x (P j) - MvPolynomial.eval x (P (j + 1)) := by
      funext x
      rw [map_sub]
    rw [e1] at hsingle
    rw [e2] at h2
    calc _ ≤ _ := hsingle
      _ ≤ C27 * scalarRms volume (ball 0 (r₀ / θ ^ j))
          (fun x => MvPolynomial.eval x (P j) - MvPolynomial.eval x (P (j + 1))) := h2
      _ ≤ C27 * (KD * (r₀ / θ ^ j) ^ σ) := mul_le_mul_of_nonneg_left (hdiff j) hC27
      _ = _ := by ring
  have hinc : ∀ m ∈ Finset.range 3, ∀ j : ℕ, scalarRms volume (ball 0 1)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m (P j)) -
        MvPolynomial.eval x (MvPolynomial.homogeneousComponent m (P (j + 1)))) ≤
        C27 * KD * (r₀ / θ ^ j) ^ (σ - m) :=
    fun m hm j => le_mul_rpow_sub_of_pow_mul_le (hr j) (hcomp j m hm)
  -- the part of degree two
  obtain ⟨aq, haq⟩ : ∃ aq : ℕ → ℝ, ∀ j, aq j = scalarRms volume (ball 0 1)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 2 (P j))) :=
    ⟨_, fun _ => rfl⟩
  have hmem1 : ∀ m j, MemLp (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m (P j)))
      2 (volume.restrict (ball (0 : Vec d) 1)) := fun m j => memLp_eval_ball _ 1
  have hθ2σ : θ ^ (2 - σ) < 1 := Real.rpow_lt_one hθ0.le hθ1 (by linarith)
  have hθ2σ0 : 0 ≤ θ ^ (2 - σ) := Real.rpow_nonneg hθ0.le _
  have hr2 : ∀ j : ℕ, (r₀ / θ ^ j) ^ (σ - 2) = r₀ ^ (σ - 2) * (θ ^ (2 - σ)) ^ j := fun j => by
    rw [radius_rpow hθ0 hr₀, neg_sub]
  have hdist : ∀ j, dist (aq j) (aq (j + 1)) ≤ (C27 * KD * r₀ ^ (σ - 2)) * (θ ^ (2 - σ)) ^ j := by
    intro j
    have h := hinc 2 (by simp) j
    simp only [Nat.cast_ofNat] at h
    rw [hr2] at h
    rw [Real.dist_eq, haq, haq]
    exact (abs_scalarRms_sub_le (hmem1 2 j) (hmem1 2 (j + 1))).trans (h.trans_eq (by ring))
  have hrtend : Tendsto (fun j : ℕ => r₀ / θ ^ j) atTop atTop := by
    have h := (tendsto_pow_atTop_atTop_of_one_lt ((one_lt_inv₀ hθ0).2 hθ1)).const_mul_atTop hr₀
    refine h.congr fun j => ?_
    rw [inv_pow, div_eq_mul_inv]
  have haq0 : Tendsto aq atTop (𝓝 0) := by
    have hup : ∀ j, aq j ≤ C27 * (((r₀ / θ ^ j) ^ 2)⁻¹ * scalarRms volume (ball 0 (r₀ / θ ^ j)) u) +
        C27 * (KF + 1) * r₀ ^ (σ - 2) * (θ ^ (2 - σ)) ^ j := by
      intro j
      have hD := (h27 (P j) (hPdeg j) _ (hr j)).2
      have hsingle := Finset.single_le_sum (f := fun m => scalarRms volume (ball 0 (r₀ / θ ^ j))
        (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m (P j))))
        (fun i _ => scalarRms_nonneg _ _) (by simp : 2 ∈ Finset.range 3)
      beta_reduce at hsingle
      rw [scalarRms_ball_homogeneousComponent 2 _ (hr j), ← haq j] at hsingle
      have hp := scalarRms_le_add_of_sub (hmemu _ (hr j)) (hmemP j (r₀ / θ ^ j))
      have h3 : (r₀ / θ ^ j) ^ 2 * aq j ≤
          C27 * (scalarRms volume (ball 0 (r₀ / θ ^ j)) u + (KF + 1) * (r₀ / θ ^ j) ^ σ) :=
        (hsingle.trans hD).trans (mul_le_mul_of_nonneg_left (hp.trans (add_le_add (le_refl _) (he j)))
          hC27)
      have hr2' : 0 < (r₀ / θ ^ j) ^ 2 := pow_pos (hr j) 2
      have e : (r₀ / θ ^ j) ^ σ / (r₀ / θ ^ j) ^ 2 = r₀ ^ (σ - 2) * (θ ^ (2 - σ)) ^ j := by
        rw [← hr2, Real.rpow_sub (hr j), Real.rpow_two]
      rw [← le_div_iff₀' hr2'] at h3
      calc aq j ≤ _ := h3
        _ = C27 * (((r₀ / θ ^ j) ^ 2)⁻¹ * scalarRms volume (ball 0 (r₀ / θ ^ j)) u) +
            C27 * (KF + 1) * ((r₀ / θ ^ j) ^ σ / (r₀ / θ ^ j) ^ 2) := by
          field_simp
        _ = _ := by rw [e]; ring
    have hlim : Tendsto (fun j : ℕ => C27 * (((r₀ / θ ^ j) ^ 2)⁻¹ *
        scalarRms volume (ball 0 (r₀ / θ ^ j)) u) +
        C27 * (KF + 1) * r₀ ^ (σ - 2) * (θ ^ (2 - σ)) ^ j) atTop (𝓝 0) := by
      have h1 := (hu2.comp hrtend).const_mul C27
      have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one hθ2σ0 hθ2σ).const_mul
        (C27 * (KF + 1) * r₀ ^ (σ - 2))
      simpa [Function.comp_def] using h1.add h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun j => ?_) hup
    rw [haq]
    exact scalarRms_nonneg _ _
  have htail : ∀ j, aq j ≤ C27 * KD / (1 - θ ^ (2 - σ)) * (r₀ / θ ^ j) ^ (σ - 2) := by
    intro j
    have h := dist_le_of_le_geometric_of_tendsto (θ ^ (2 - σ)) (C27 * KD * r₀ ^ (σ - 2)) hθ2σ
      hdist haq0 j
    rw [Real.dist_eq, sub_zero] at h
    rw [hr2]
    calc aq j ≤ |aq j| := le_abs_self _
      _ ≤ _ := h
      _ = _ := by ring
  -- the constant
  have h1θ : 0 < 1 - θ ^ (2 - σ) := by linarith
  refine ⟨P, (KF + 1) + C27 * KD + C27 * KD / (1 - θ ^ (2 - σ)),
    by have := mul_nonneg hC27 hKD0; have := div_nonneg this h1θ.le; linarith, fun j => ?_⟩
  have hc1 : KF + 1 ≤ (KF + 1) + C27 * KD + C27 * KD / (1 - θ ^ (2 - σ)) := by
    have := mul_nonneg hC27 hKD0; have := div_nonneg this h1θ.le; linarith
  have hc2 : C27 * KD ≤ (KF + 1) + C27 * KD + C27 * KD / (1 - θ ^ (2 - σ)) := by
    have := div_nonneg (mul_nonneg hC27 hKD0) h1θ.le; linarith
  have hc3 : C27 * KD / (1 - θ ^ (2 - σ)) ≤
      (KF + 1) + C27 * KD + C27 * KD / (1 - θ ^ (2 - σ)) := by
    have := mul_nonneg hC27 hKD0; linarith
  have hnn : ∀ e : ℝ, 0 ≤ (r₀ / θ ^ j) ^ e := fun e => Real.rpow_nonneg (hr j).le e
  refine ⟨hPdeg j, (he j).trans (mul_le_mul_of_nonneg_right hc1 (hnn _)), ?_, ?_, ?_⟩
  · rw [← haq]
    exact (htail j).trans (mul_le_mul_of_nonneg_right hc3 (hnn _))
  · have h := hinc 0 (by simp) j
    simp only [Nat.cast_zero, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right hc2 (hnn _))
  · have h := hinc 1 (by simp) j
    simp only [Nat.cast_one] at h
    exact h.trans (mul_le_mul_of_nonneg_right hc2 (hnn _))

theorem scalarRms_le_sum_homogeneous_two {Q : MvPolynomial (Fin d) ℝ} (hQ : Q.totalDegree ≤ 2)
    {r : ℝ} (hr : 0 < r) :
    scalarRms volume (ball 0 r) (fun x => MvPolynomial.eval x Q) ≤
      scalarRms volume (ball 0 1)
          (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 0 Q)) +
        r * scalarRms volume (ball 0 1)
          (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 Q)) +
        r ^ 2 * scalarRms volume (ball 0 1)
          (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 2 Q)) := by
  have hm : ∀ m, MemLp (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q)) 2
      (volume.restrict (ball (0 : Vec d) r)) := fun m => memLp_eval_ball _ r
  have e : (fun x => MvPolynomial.eval x Q) = fun x =>
      (MvPolynomial.eval x (MvPolynomial.homogeneousComponent 0 Q) +
        MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 Q)) +
        MvPolynomial.eval x (MvPolynomial.homogeneousComponent 2 Q) := by
    funext x
    rw [eval_eq_sum_homogeneousComponent hQ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one]
  rw [e]
  have h1 := scalarRms_add_le ((hm 0).add (hm 1)) (hm 2)
  have h2 := scalarRms_add_le (hm 0) (hm 1)
  have s0 := scalarRms_ball_homogeneousComponent 0 Q hr
  have s1 := scalarRms_ball_homogeneousComponent 1 Q hr
  have s2 := scalarRms_ball_homogeneousComponent 2 Q hr
  rw [pow_zero, one_mul] at s0
  rw [pow_one] at s1
  calc _ ≤ _ := h1
    _ ≤ _ := add_le_add_left h2 _
    _ = _ := by rw [s0, s1, s2]

/-- The growth iteration when `β - δ > 1`: the growth exponent improves from `β` to `β - δ`. -/
theorem growth_step_large {Λ : ℝ} {a : CoefficientField d Λ} {A : Mat d} {θ C₅ δ X r₀ M β : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hC₅ : 0 ≤ C₅) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hX1 : 1 ≤ X) (hXr : X ≤ r₀)
    (H50 : ∀ r : ℝ, X ≤ r → ∀ v, IsSolutionBall a r v →
      harmonicFlatness A 2 v (θ * r) ≤
        1 / 4 * θ ^ ((2 : ℝ) + 1 - δ / 2) * harmonicFlatness A 2 v r +
          C₅ * r ^ (-δ) * scalarRms volume (ball 0 r) v)
    {u : Vec d → ℝ} (hsol : ∀ R : ℝ, 0 < R → IsSolutionBall a R u)
    (hu2 : Tendsto (fun r : ℝ => (r ^ 2)⁻¹ * scalarRms volume (ball 0 r) u) atTop (𝓝 0))
    (hM : 0 ≤ M) (hβ2 : β ≤ 2) (hσ1 : 1 < β - δ)
    (hgrow : ∀ j : ℕ, scalarRms volume (ball 0 (r₀ / θ ^ j)) u ≤ M * (r₀ / θ ^ j) ^ β) :
    ∃ M' : ℝ, 0 ≤ M' ∧
      ∀ j : ℕ, scalarRms volume (ball 0 (r₀ / θ ^ j)) u ≤ M' * (r₀ / θ ^ j) ^ (β - δ) := by
  obtain ⟨P, K, hK, hP⟩ := growth_core (A := A) hθ0 hθ1 hC₅ hδ0 hδ1 hX1 hXr H50 hsol hu2 hM hβ2
    hgrow
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = β - δ := ⟨_, rfl⟩
  rw [← hσ] at hP hσ1 ⊢
  have hr₀ : 0 < r₀ := by linarith
  have hr : ∀ j : ℕ, 0 < r₀ / θ ^ j := fun j => div_pos hr₀ (pow_pos hθ0 j)
  have hr1 : ∀ j : ℕ, 1 ≤ r₀ / θ ^ j := fun j => by
    rw [le_div_iff₀ (pow_pos hθ0 j)]
    have : θ ^ j ≤ 1 := pow_le_one₀ hθ0.le hθ1.le
    nlinarith
  have hmem1 : ∀ m j, MemLp (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m (P j)))
      2 (volume.restrict (ball (0 : Vec d) 1)) := fun m j => memLp_eval_ball _ 1
  obtain ⟨x0, hx0⟩ : ∃ x0 : ℕ → ℝ, ∀ j, x0 j = scalarRms volume (ball 0 1)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 0 (P j))) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨x1, hx1⟩ : ∃ x1 : ℕ → ℝ, ∀ j, x1 j = scalarRms volume (ball 0 1)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 (P j))) :=
    ⟨_, fun _ => rfl⟩
  have hρ0 : 1 < θ ^ (-σ) := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hθ0 hθ1 (by linarith)
  have hρ1 : 1 < θ ^ (-(σ - 1)) := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hθ0 hθ1 (by linarith)
  have hstep0 : ∀ j, x0 (j + 1) ≤ x0 j + (K * r₀ ^ σ) * (θ ^ (-σ)) ^ j := by
    intro j
    rw [hx0, hx0]
    have h := scalarRms_le_add_of_sub (hmem1 0 j) (hmem1 0 (j + 1))
    have hb := (hP j).2.2.2.1
    rw [radius_rpow hθ0 hr₀] at hb
    linarith
  have hstep1 : ∀ j, x1 (j + 1) ≤ x1 j + (K * r₀ ^ (σ - 1)) * (θ ^ (-(σ - 1))) ^ j := by
    intro j
    rw [hx1, hx1]
    have h := scalarRms_le_add_of_sub (hmem1 1 j) (hmem1 1 (j + 1))
    have hb := (hP j).2.2.2.2
    rw [radius_rpow hθ0 hr₀] at hb
    linarith
  have hA0 : 0 ≤ K * r₀ ^ σ := mul_nonneg hK (Real.rpow_nonneg hr₀.le _)
  have hA1 : 0 ≤ K * r₀ ^ (σ - 1) := mul_nonneg hK (Real.rpow_nonneg hr₀.le _)
  have hx0b := le_add_geom_of_succ_le hA0 hρ0 hstep0
  have hx1b := le_add_geom_of_succ_le hA1 hρ1 hstep1
  have hx00 : 0 ≤ x0 0 := by rw [hx0]; exact scalarRms_nonneg _ _
  have hx10 : 0 ≤ x1 0 := by rw [hx1]; exact scalarRms_nonneg _ _
  have hd0 : 0 < θ ^ (-σ) - 1 := by linarith
  have hd1 : 0 < θ ^ (-(σ - 1)) - 1 := by linarith
  refine ⟨2 * K + K / (θ ^ (-σ) - 1) + K / (θ ^ (-(σ - 1)) - 1) + x0 0 + x1 0,
    by have := div_nonneg hK hd0.le; have := div_nonneg hK hd1.le; linarith, fun m => ?_⟩
  obtain ⟨hdeg, he, hq, -, -⟩ := hP m
  set r := r₀ / θ ^ m with hrdef
  have hrσ1 : 1 ≤ r ^ σ := Real.one_le_rpow (hr1 m) (by linarith)
  have hrσr : r ≤ r ^ σ := by
    calc r = r ^ (1 : ℝ) := (Real.rpow_one r).symm
      _ ≤ r ^ σ := Real.rpow_le_rpow_of_exponent_le (hr1 m) hσ1.le
  have hsum := scalarRms_le_sum_homogeneous_two hdeg (hr m)
  rw [← hx0, ← hx1] at hsum
  have hu : scalarRms volume (ball 0 r) u ≤
      scalarRms volume (ball 0 r) (fun x => u x - MvPolynomial.eval x (P m)) +
        scalarRms volume (ball 0 r) (fun x => MvPolynomial.eval x (P m)) := by
    calc scalarRms volume (ball 0 r) u = scalarRms volume (ball 0 r)
          (fun x => (u x - MvPolynomial.eval x (P m)) + MvPolynomial.eval x (P m)) := by
          congr 1
          funext x
          ring
      _ ≤ _ := scalarRms_add_le (f := fun x => u x - MvPolynomial.eval x (P m))
          (g := fun x => MvPolynomial.eval x (P m)) (((hsol r (hr m)).1).sub (memLp_eval_ball _ r))
          (memLp_eval_ball _ r)
  -- the three parts
  have b0 : x0 m ≤ x0 0 + K / (θ ^ (-σ) - 1) * r ^ σ := by
    have e : r ^ σ = r₀ ^ σ * (θ ^ (-σ)) ^ m := radius_rpow hθ0 hr₀ σ m
    rw [e]
    calc x0 m ≤ _ := hx0b m
      _ = _ := by ring
  have b1 : r * x1 m ≤ r * x1 0 + K / (θ ^ (-(σ - 1)) - 1) * r ^ σ := by
    have e : r ^ (σ - 1) = r₀ ^ (σ - 1) * (θ ^ (-(σ - 1))) ^ m := radius_rpow hθ0 hr₀ (σ - 1) m
    have e2 : r * r ^ (σ - 1) = r ^ σ := by
      rw [Real.rpow_sub_one (hr m).ne', mul_div_assoc', mul_div_cancel_left₀ _ (hr m).ne']
    have h := mul_le_mul_of_nonneg_left (hx1b m) (hr m).le
    calc r * x1 m ≤ _ := h
      _ = r * x1 0 + K / (θ ^ (-(σ - 1)) - 1) * (r * (r₀ ^ (σ - 1) * (θ ^ (-(σ - 1))) ^ m)) := by
          ring
      _ = _ := by rw [← e, e2]
  have b2 : r ^ 2 * scalarRms volume (ball 0 1)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 2 (P m))) ≤ K * r ^ σ := by
    have e2 : r ^ 2 * r ^ (σ - 2) = r ^ σ := by
      rw [Real.rpow_sub (hr m), Real.rpow_two, mul_div_assoc',
        mul_div_cancel_left₀ _ (pow_pos (hr m) 2).ne']
    calc _ ≤ r ^ 2 * (K * r ^ (σ - 2)) := mul_le_mul_of_nonneg_left hq (by positivity)
      _ = K * (r ^ 2 * r ^ (σ - 2)) := by ring
      _ = _ := by rw [e2]
  have hx00' : x0 0 ≤ x0 0 * r ^ σ := le_mul_of_one_le_right hx00 hrσ1
  have hx10' : r * x1 0 ≤ x1 0 * r ^ σ := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_left hrσr hx10
  nlinarith

theorem scalarRms_dot_ball (v : Vec d) {r : ℝ} (hr : 0 < r) :
    scalarRms volume (ball 0 r) (fun x => dot v x) =
      r * scalarRms volume (ball 0 1) (fun x => dot v x) := by
  have h := scalarRms_ball_homogeneous (q := fun x => dot v x)
    (fun t _ x => dot_smul_right' v x t) (r := 1) hr
  rwa [mul_one, pow_one] at h

/-- The growth iteration when `0 < β - δ < 1`: a linear function `x ↦ v·x` with
`‖u - v·x‖_{L̲²(B_{r_j})} ≤ M r_j^{β-δ}` (Step 3 of the proof of (3.47), `k = 1`). -/
theorem growth_step_final {Λ : ℝ} {a : CoefficientField d Λ} {A : Mat d} {θ C₅ δ X r₀ M β : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hC₅ : 0 ≤ C₅) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hX1 : 1 ≤ X) (hXr : X ≤ r₀)
    (H50 : ∀ r : ℝ, X ≤ r → ∀ v, IsSolutionBall a r v →
      harmonicFlatness A 2 v (θ * r) ≤
        1 / 4 * θ ^ ((2 : ℝ) + 1 - δ / 2) * harmonicFlatness A 2 v r +
          C₅ * r ^ (-δ) * scalarRms volume (ball 0 r) v)
    {u : Vec d → ℝ} (hsol : ∀ R : ℝ, 0 < R → IsSolutionBall a R u)
    (hu2 : Tendsto (fun r : ℝ => (r ^ 2)⁻¹ * scalarRms volume (ball 0 r) u) atTop (𝓝 0))
    (hM : 0 ≤ M) (hβ2 : β ≤ 2) (hσ0 : 0 < β - δ) (hσ1 : β - δ < 1)
    (hgrow : ∀ j : ℕ, scalarRms volume (ball 0 (r₀ / θ ^ j)) u ≤ M * (r₀ / θ ^ j) ^ β) :
    ∃ (v : Vec d) (M' : ℝ), 0 ≤ M' ∧ ∀ j : ℕ, scalarRms volume (ball 0 (r₀ / θ ^ j))
      (fun x => u x - dot v x) ≤ M' * (r₀ / θ ^ j) ^ (β - δ) := by
  obtain ⟨P, K, hK, hP⟩ := growth_core (A := A) hθ0 hθ1 hC₅ hδ0 hδ1 hX1 hXr H50 hsol hu2 hM hβ2
    hgrow
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = β - δ := ⟨_, rfl⟩
  rw [← hσ] at hP hσ0 hσ1 ⊢
  have hr₀ : 0 < r₀ := by linarith
  have hr : ∀ j : ℕ, 0 < r₀ / θ ^ j := fun j => div_pos hr₀ (pow_pos hθ0 j)
  have hr1 : ∀ j : ℕ, 1 ≤ r₀ / θ ^ j := fun j => by
    rw [le_div_iff₀ (pow_pos hθ0 j)]
    have : θ ^ j ≤ 1 := pow_le_one₀ hθ0.le hθ1.le
    nlinarith
  have hmem1 : ∀ m j, MemLp (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m (P j)))
      2 (volume.restrict (ball (0 : Vec d) 1)) := fun m j => memLp_eval_ball _ 1
  -- the part of degree zero
  obtain ⟨x0, hx0⟩ : ∃ x0 : ℕ → ℝ, ∀ j, x0 j = scalarRms volume (ball 0 1)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 0 (P j))) :=
    ⟨_, fun _ => rfl⟩
  have hρ0 : 1 < θ ^ (-σ) := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hθ0 hθ1 (by linarith)
  have hstep0 : ∀ j, x0 (j + 1) ≤ x0 j + (K * r₀ ^ σ) * (θ ^ (-σ)) ^ j := by
    intro j
    rw [hx0, hx0]
    have h := scalarRms_le_add_of_sub (hmem1 0 j) (hmem1 0 (j + 1))
    have hb := (hP j).2.2.2.1
    rw [radius_rpow hθ0 hr₀] at hb
    linarith
  have hA0 : 0 ≤ K * r₀ ^ σ := mul_nonneg hK (Real.rpow_nonneg hr₀.le _)
  have hx0b := le_add_geom_of_succ_le hA0 hρ0 hstep0
  have hx00 : 0 ≤ x0 0 := by rw [hx0]; exact scalarRms_nonneg _ _
  have hd0 : 0 < θ ^ (-σ) - 1 := by linarith
  -- the parts of degree one converge
  choose v hv using fun j => exists_dot_eq_homogeneousComponent_one (P j)
  obtain ⟨Ka, hKa, hnorm⟩ := exists_norm_le_scalarRms_dot (d := d)
  obtain ⟨Ca, hCa, hup⟩ := exists_scalarRms_dot_le (d := d)
  have hθ1σ : θ ^ (1 - σ) < 1 := Real.rpow_lt_one hθ0.le hθ1 (by linarith)
  have hdist : ∀ j, dist (v j) (v (j + 1)) ≤ (Ka * K * r₀ ^ (σ - 1)) * (θ ^ (1 - σ)) ^ j := by
    intro j
    rw [dist_eq_norm]
    have hb := (hP j).2.2.2.2
    rw [radius_rpow hθ0 hr₀, neg_sub] at hb
    have e : (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 (P j)) -
        MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 (P (j + 1)))) =
        fun x => dot (v j - v (j + 1)) x := by
      funext x
      rw [dot_sub_left, hv, hv]
    rw [e] at hb
    calc ‖v j - v (j + 1)‖ ≤ Ka * scalarRms volume (ball 0 1) (fun x => dot (v j - v (j + 1)) x) :=
          hnorm _
      _ ≤ Ka * (K * (r₀ ^ (σ - 1) * (θ ^ (1 - σ)) ^ j)) := mul_le_mul_of_nonneg_left hb hKa.le
      _ = _ := by ring
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric _ _ hθ1σ hdist)
  have hvw : ∀ j, ‖v j - w‖ ≤ Ka * K / (1 - θ ^ (1 - σ)) * (r₀ / θ ^ j) ^ (σ - 1) := by
    intro j
    have h := dist_le_of_le_geometric_of_tendsto _ _ hθ1σ hdist hw j
    rw [dist_eq_norm] at h
    rw [radius_rpow hθ0 hr₀, neg_sub]
    calc _ ≤ _ := h
      _ = _ := by ring
  have h1θ : 0 < 1 - θ ^ (1 - σ) := by linarith
  have hKw : 0 ≤ Ka * K / (1 - θ ^ (1 - σ)) := div_nonneg (mul_nonneg hKa.le hK) h1θ.le
  refine ⟨w, 2 * K + K / (θ ^ (-σ) - 1) + Ca * (Ka * K / (1 - θ ^ (1 - σ))) + x0 0,
    by have := div_nonneg hK hd0.le; have := mul_nonneg hCa hKw; linarith, fun m => ?_⟩
  obtain ⟨hdeg, he, hq, -, -⟩ := hP m
  set r := r₀ / θ ^ m with hrdef
  have hrσ1 : 1 ≤ r ^ σ := Real.one_le_rpow (hr1 m) hσ0.le
  -- the decomposition of `u - w·x`
  have hdec : (fun x => u x - dot w x) = fun x =>
      (((u x - MvPolynomial.eval x (P m)) +
        MvPolynomial.eval x (MvPolynomial.homogeneousComponent 0 (P m))) +
        dot (v m - w) x) + MvPolynomial.eval x (MvPolynomial.homogeneousComponent 2 (P m)) := by
    funext x
    rw [eval_eq_sum_homogeneousComponent hdeg, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one, hv, dot_sub_left]
    ring
  have hmu : MemLp (fun x => u x - MvPolynomial.eval x (P m)) 2
      (volume.restrict (ball (0 : Vec d) r)) := ((hsol r (hr m)).1).sub (memLp_eval_ball _ r)
  have hm0 := memLp_eval_ball (MvPolynomial.homogeneousComponent 0 (P m)) r
  have hm2 := memLp_eval_ball (MvPolynomial.homogeneousComponent 2 (P m)) r
  have hmd := memLp_dot_ball (v m - w) r
  have t1 := scalarRms_add_le (f := fun x => ((u x - MvPolynomial.eval x (P m)) +
      MvPolynomial.eval x (MvPolynomial.homogeneousComponent 0 (P m))) + dot (v m - w) x)
    (g := fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 2 (P m)))
    ((hmu.add hm0).add hmd) hm2
  have t2 := scalarRms_add_le (f := fun x => (u x - MvPolynomial.eval x (P m)) +
      MvPolynomial.eval x (MvPolynomial.homogeneousComponent 0 (P m)))
    (g := fun x => dot (v m - w) x) (hmu.add hm0) hmd
  have t3 := scalarRms_add_le (f := fun x => u x - MvPolynomial.eval x (P m))
    (g := fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 0 (P m))) hmu hm0
  have s0 := scalarRms_ball_homogeneousComponent 0 (P m) (hr m)
  have s2 := scalarRms_ball_homogeneousComponent 2 (P m) (hr m)
  rw [pow_zero, one_mul, ← hx0] at s0
  have sd := scalarRms_dot_ball (v m - w) (hr m)
  -- the bounds
  have b0 : x0 m ≤ x0 0 + K / (θ ^ (-σ) - 1) * r ^ σ := by
    have e : r ^ σ = r₀ ^ σ * (θ ^ (-σ)) ^ m := radius_rpow hθ0 hr₀ σ m
    rw [e]
    calc x0 m ≤ _ := hx0b m
      _ = _ := by ring
  have bd : r * scalarRms volume (ball 0 1) (fun x => dot (v m - w) x) ≤
      Ca * (Ka * K / (1 - θ ^ (1 - σ))) * r ^ σ := by
    have e2 : r * r ^ (σ - 1) = r ^ σ := by
      rw [Real.rpow_sub_one (hr m).ne', mul_div_assoc', mul_div_cancel_left₀ _ (hr m).ne']
    calc _ ≤ r * (Ca * (Ka * K / (1 - θ ^ (1 - σ)) * r ^ (σ - 1))) :=
          mul_le_mul_of_nonneg_left ((hup _).trans (mul_le_mul_of_nonneg_left (hvw m) hCa))
            (hr m).le
      _ = Ca * (Ka * K / (1 - θ ^ (1 - σ))) * (r * r ^ (σ - 1)) := by ring
      _ = _ := by rw [e2]
  have b2 : r ^ 2 * scalarRms volume (ball 0 1)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 2 (P m))) ≤ K * r ^ σ := by
    have e2 : r ^ 2 * r ^ (σ - 2) = r ^ σ := by
      rw [Real.rpow_sub (hr m), Real.rpow_two, mul_div_assoc',
        mul_div_cancel_left₀ _ (pow_pos (hr m) 2).ne']
    calc _ ≤ r ^ 2 * (K * r ^ (σ - 2)) := mul_le_mul_of_nonneg_left hq (by positivity)
      _ = K * (r ^ 2 * r ^ (σ - 2)) := by ring
      _ = _ := by rw [e2]
  have hx00' : x0 0 ≤ x0 0 * r ^ σ := le_mul_of_one_le_right hx00 hrσ1
  rw [hdec]
  linarith

/-- **The growth iteration**: `n` steps with `β - δ > 1` and a last one with `β - δ < 1`, for
`δ = 2/(2n+1)`, starting from `‖u‖_{L̲²(B_r)} = o(r²)`. -/
theorem exists_dot_growth {Λ : ℝ} {a : CoefficientField d Λ} {A : Mat d} {θ C₅ δ X r₀ : ℝ}
    {n : ℕ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hC₅ : 0 ≤ C₅) (hn : 1 ≤ n) (hδ : δ = 2 / (2 * n + 1))
    (hX1 : 1 ≤ X) (hXr : X ≤ r₀)
    (H50 : ∀ r : ℝ, X ≤ r → ∀ v, IsSolutionBall a r v →
      harmonicFlatness A 2 v (θ * r) ≤
        1 / 4 * θ ^ ((2 : ℝ) + 1 - δ / 2) * harmonicFlatness A 2 v r +
          C₅ * r ^ (-δ) * scalarRms volume (ball 0 r) v)
    {u : Vec d → ℝ} (hsol : ∀ R : ℝ, 0 < R → IsSolutionBall a R u)
    (hu2 : Tendsto (fun r : ℝ => (r ^ 2)⁻¹ * scalarRms volume (ball 0 r) u) atTop (𝓝 0)) :
    ∃ (v : Vec d) (M : ℝ), 0 ≤ M ∧ ∀ j : ℕ, scalarRms volume (ball 0 (r₀ / θ ^ j))
      (fun x => u x - dot v x) ≤ M * (r₀ / θ ^ j) ^ (2 - ((n : ℝ) + 1) * δ) := by
  have hr₀ : 0 < r₀ := by linarith
  have hr : ∀ j : ℕ, 0 < r₀ / θ ^ j := fun j => div_pos hr₀ (pow_pos hθ0 j)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2n : (0 : ℝ) < 2 * n + 1 := by positivity
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ1 : δ ≤ 1 := by rw [hδ, div_le_one h2n]; linarith
  have hnδ : (n : ℝ) * δ < 1 := by
    rw [hδ, mul_div_assoc', div_lt_one h2n]; linarith
  have hn1δ : 1 < ((n : ℝ) + 1) * δ := by
    rw [hδ, mul_div_assoc', one_lt_div h2n]; linarith
  have hn1δ2 : ((n : ℝ) + 1) * δ < 2 := by
    rw [hδ, mul_div_assoc', div_lt_iff₀ h2n]; linarith
  have hrtend : Tendsto (fun j : ℕ => r₀ / θ ^ j) atTop atTop := by
    have h := (tendsto_pow_atTop_atTop_of_one_lt ((one_lt_inv₀ hθ0).2 hθ1)).const_mul_atTop hr₀
    refine h.congr fun j => ?_
    rw [inv_pow, div_eq_mul_inv]
  obtain ⟨M₀, hM₀⟩ := (hu2.comp hrtend).bddAbove_range
  have hbase : ∀ j : ℕ, scalarRms volume (ball 0 (r₀ / θ ^ j)) u ≤
      M₀ * (r₀ / θ ^ j) ^ (2 - ((0 : ℕ) : ℝ) * δ) := by
    intro j
    have h := hM₀ ⟨j, rfl⟩
    simp only [Function.comp_apply] at h
    rw [inv_mul_le_iff₀ (pow_pos (hr j) 2)] at h
    rw [Nat.cast_zero, zero_mul, sub_zero, Real.rpow_two]
    linarith
  have hM₀0 : 0 ≤ M₀ :=
    (mul_nonneg (inv_nonneg.2 (pow_nonneg (hr 0).le 2)) (scalarRms_nonneg _ _)).trans
      (hM₀ ⟨0, rfl⟩)
  have hiter : ∀ i : ℕ, i ≤ n → ∃ M : ℝ, 0 ≤ M ∧ ∀ j : ℕ,
      scalarRms volume (ball 0 (r₀ / θ ^ j)) u ≤ M * (r₀ / θ ^ j) ^ (2 - (i : ℝ) * δ) := by
    intro i
    induction i with
    | zero => intro _; exact ⟨M₀, hM₀0, hbase⟩
    | succ i ih =>
      intro hi
      obtain ⟨M, hM, hgrow⟩ := ih (by omega)
      have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
      have hσ1 : 1 < 2 - (i : ℝ) * δ - δ := by
        have := mul_le_mul_of_nonneg_right hi' hδ0.le
        linarith
      obtain ⟨M', hM', h⟩ := growth_step_large (A := A) hθ0 hθ1 hC₅ hδ0 hδ1 hX1 hXr H50 hsol hu2
        hM (by have := mul_nonneg (Nat.cast_nonneg i) hδ0.le; linarith) hσ1 hgrow
      refine ⟨M', hM', fun j => ?_⟩
      have e : (2 : ℝ) - (i : ℝ) * δ - δ = 2 - ((i + 1 : ℕ) : ℝ) * δ := by push_cast; ring
      rw [← e]
      exact h j
  obtain ⟨M, hM, hgrow⟩ := hiter n le_rfl
  obtain ⟨v, M', hM', h⟩ := growth_step_final (A := A) hθ0 hθ1 hC₅ hδ0 hδ1 hX1 hXr H50 hsol hu2
    hM (by have := mul_nonneg (Nat.cast_nonneg n) hδ0.le; linarith) (by linarith) (by linarith)
    hgrow
  refine ⟨v, M', hM', fun j => ?_⟩
  have e : (2 : ℝ) - (n : ℝ) * δ - δ = 2 - ((n : ℝ) + 1) * δ := by ring
  rw [← e]
  exact h j

/-- From the radii `r_j = r₀ θ^{-j}` to every radius `r ≥ r₀`. -/
theorem scalarRms_le_of_radii {θ r₀ M σ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hr₀ : 0 < r₀)
    (hσ : 0 ≤ σ) (hM : 0 ≤ M) {f : Vec d → ℝ}
    (hf : ∀ R : ℝ, 0 < R → MemLp f 2 (volume.restrict (ball (0 : Vec d) R)))
    (h : ∀ j : ℕ, scalarRms volume (ball 0 (r₀ / θ ^ j)) f ≤ M * (r₀ / θ ^ j) ^ σ) {r : ℝ}
    (hr : r₀ ≤ r) :
    scalarRms volume (ball 0 r) f ≤ Real.sqrt ((θ⁻¹) ^ d) * M * θ ^ (-σ) * r ^ σ := by
  classical
  have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
  have hex : ∃ j : ℕ, r ≤ r₀ / θ ^ j := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (r / r₀) ((one_lt_inv₀ hθ0).2 hθ1)
    refine ⟨j, ?_⟩
    rw [inv_pow, div_lt_iff₀ hr₀, ← div_eq_inv_mul] at hj
    exact hj.le
  obtain ⟨j, hjdef⟩ : ∃ j, j = Nat.find hex := ⟨_, rfl⟩
  have hj1 : r ≤ r₀ / θ ^ j := by rw [hjdef]; exact Nat.find_spec hex
  have hj2 : r₀ / θ ^ j ≤ r / θ := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0, pow_zero, div_one, le_div_iff₀ hθ0]
      nlinarith
    · have hmin := Nat.find_min hex (show j - 1 < Nat.find hex by rw [← hjdef]; omega)
      push Not at hmin
      have e : r₀ / θ ^ j = r₀ / θ ^ (j - 1) / θ := by
        rw [div_div, ← pow_succ, Nat.sub_add_cancel hpos]
      rw [e]
      exact div_le_div_of_nonneg_right hmin.le hθ0.le
  have hrj : 0 < r₀ / θ ^ j := div_pos hr₀ (pow_pos hθ0 j)
  have h1 := scalarRms_ball_le hr0 hj1 (hf _ hrj)
  have hratio : Real.sqrt ((r₀ / θ ^ j / r) ^ d) ≤ Real.sqrt ((θ⁻¹) ^ d) := by
    refine Real.sqrt_le_sqrt (pow_le_pow_left₀ (by positivity) ?_ d)
    rw [div_le_iff₀ hr0]
    calc r₀ / θ ^ j ≤ r / θ := hj2
      _ = θ⁻¹ * r := by rw [div_eq_inv_mul]
  have hpow : (r₀ / θ ^ j) ^ σ ≤ θ ^ (-σ) * r ^ σ := by
    calc (r₀ / θ ^ j) ^ σ ≤ (r / θ) ^ σ := Real.rpow_le_rpow hrj.le hj2 hσ
      _ = θ ^ (-σ) * r ^ σ := by
        rw [Real.div_rpow hr0.le hθ0.le, Real.rpow_neg hθ0.le, div_eq_inv_mul]
  calc scalarRms volume (ball 0 r) f
      ≤ Real.sqrt ((r₀ / θ ^ j / r) ^ d) * scalarRms volume (ball 0 (r₀ / θ ^ j)) f := h1
    _ ≤ Real.sqrt ((θ⁻¹) ^ d) * (M * (θ ^ (-σ) * r ^ σ)) :=
        mul_le_mul hratio ((h j).trans (mul_le_mul_of_nonneg_left hpow hM)) (scalarRms_nonneg _ _)
          (Real.sqrt_nonneg _)
    _ = _ := by ring

end QSH
