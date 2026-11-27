import QuantitativeStochasticHomogenization.Ch03.Sec03.GrowthIteration

/-!
# Statement `(i)₁` of Theorem 3.8

Armstrong–Kuusi–Mourrat, Theorem 3.8, statement `(i)_k` for `k = 1`, through (3.47): (3.51), `(i)₀`
and `(ii)₁` give, above a random scale `X ≤ O_s(C)` and for almost every coefficient field, for every
`u ∈ A_1` some `p ∈ Ā_1` with `‖u - p‖_{L̲²(B_R)} ≤ C R^{-δ} ‖p‖_{L̲²(B_R)}` for every `R ≥ X`
(`theorem_3_8_i_one`). The growth iteration (`exists_dot_growth`) gives a linear function `q` with
`r^{-1} ‖u - q‖_{L̲²(B_r)} → 0`; with `φ_q ∈ A_1` from `(ii)₁`, `u - φ_q ∈ A_0` is a constant by
`(i)₀`, and `p = q + c`.
-/

open MeasureTheory Filter Set Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- **Theorem 3.8 `(i)₁`**, for `d ≥ 2`, `Λ > 1` and `s ∈ (0, d)`: there are `δ ∈ (0, ½]` and `C`
such that, for every law satisfying the assumptions, a random variable `X ≥ 1` with `X ≤ O_s(C)`
satisfies, for almost every coefficient field: for every `u ∈ A_1` there is `p ∈ Ā_1` with
`‖u - p‖_{L̲²(B_R)} ≤ C R^{-δ} ‖p‖_{L̲²(B_R)}` for every `R ≥ X`. -/
theorem theorem_3_8_i_one (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) {s : ℝ} (hs : 0 < s)
    (hsd : s < d) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∃ C CX : ℝ, 0 ≤ C ∧ 0 < CX ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∃ X : CoefficientField d Λ → ℝ, OsBound P X s CX ∧ (∀ a, 1 ≤ X a) ∧ ∀ᵐ a ∂P,
        ∀ u ∈ solutionGrowthSpace a 1, ∃ p ∈ harmonicPolys (homogenizedMatrix P) 1,
          ∀ R : ℝ, X a ≤ R → scalarRms volume (ball 0 R) (fun x => u x - p x) ≤
            C * R ^ (-δ) * scalarRms volume (ball 0 R) p := by
  obtain ⟨C₀, hC₀, h380⟩ := theorem_3_8_zero hd hΛ hs hsd
  obtain ⟨δ₂, hδ₂0, hδ₂2, C₂, CX₂, hC₂, hCX₂, h2⟩ := theorem_3_8_ii_one hd hΛ hs hsd
  obtain ⟨δ₀, hδ₀0, -, h50all⟩ := equation_3_50 hd hΛ hs hsd
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌈1 / δ₀⌉₊ := ⟨_, rfl⟩
  have hn1 : 1 ≤ n := by
    rw [hn]
    exact Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  have hn' : 1 / δ₀ ≤ n := by rw [hn]; exact Nat.le_ceil _
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 2 / (2 * n + 1) := ⟨_, rfl⟩
  have h2n : (0 : ℝ) < 2 * n + 1 := by positivity
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδδ₀ : δ ≤ δ₀ := by
    rw [hδ, div_le_iff₀ h2n]
    rw [div_le_iff₀ hδ₀0] at hn'
    nlinarith
  have hnδ : ((n : ℝ) + 1) * δ = (2 * n + 2) / (2 * n + 1) := by
    rw [hδ]
    field_simp
  have hσ0 : 0 ≤ 2 - ((n : ℝ) + 1) * δ := by
    rw [hnδ, sub_nonneg, div_le_iff₀ h2n]
    linarith
  have hσ1 : 2 - ((n : ℝ) + 1) * δ < 1 := by
    rw [hnδ, sub_lt_comm, lt_div_iff₀ h2n]
    linarith
  obtain ⟨θ, C5, CX5, hCX5, hθC, h50⟩ := h50all δ hδ0 hδδ₀
  obtain ⟨hθ0, hθ1, hC50⟩ := hθC 2
  obtain ⟨C27, hC27, h27⟩ := scalarRms_homogeneousComponents_zero (d := d) 1
  refine ⟨δ₂, hδ₂0, hδ₂2, C₂ * C27, (2 : ℝ) ^ s⁻¹ * max ((2 : ℝ) ^ s⁻¹ * max C₀ CX₂) CX5,
    mul_nonneg hC₂ hC27, by positivity, fun P hP => ?_⟩
  obtain ⟨X₀, hX₀os, hX₀1, hX₀ae⟩ := h380 P hP
  obtain ⟨X₂, hX₂os, hX₂1, hX₂ae⟩ := h2 P hP
  obtain ⟨X₅, hX₅os, hX₅1, hX₅ae⟩ := h50 P hP
  refine ⟨fun a => max (max (X₀ a) (X₂ a)) (X₅ a), osBound_max (osBound_max hX₀os hX₂os) hX₅os,
    fun a => le_max_of_le_left (le_max_of_le_left (hX₀1 a)), ?_⟩
  filter_upwards [hX₀ae, hX₂ae, hX₅ae] with a ha0 ha2 ha5
  intro u hu
  obtain ⟨hi0, -, -⟩ := ha0
  obtain ⟨r₀, hr₀def⟩ : ∃ r₀, r₀ = max (max (X₀ a) (X₂ a)) (X₅ a) := ⟨_, rfl⟩
  have hX₂r : X₂ a ≤ r₀ := by rw [hr₀def]; exact le_max_of_le_left (le_max_right _ _)
  have hX₅r : X₅ a ≤ r₀ := by rw [hr₀def]; exact le_max_right _ _
  have hr₀1 : 1 ≤ r₀ := (hX₅1 a).trans hX₅r
  have hr₀ : 0 < r₀ := by linarith
  have H50 : ∀ r : ℝ, X₅ a ≤ r → ∀ v, IsSolutionBall a r v →
      harmonicFlatness (homogenizedMatrix P) 2 v (θ 2 * r) ≤
        1 / 4 * θ 2 ^ ((2 : ℝ) + 1 - δ / 2) * harmonicFlatness (homogenizedMatrix P) 2 v r +
          C5 2 * r ^ (-δ) * scalarRms volume (ball 0 r) v := fun r hr v hv => by
    simpa only [Nat.cast_ofNat] using ha5 2 r hr v hv
  have hsol : ∀ R : ℝ, 0 < R → IsSolutionBall a R u := fun R hR =>
    isSolutionBall_of_mem_solutionGrowthSpace hu hR
  have hu2 : Tendsto (fun r : ℝ => (r ^ 2)⁻¹ * scalarRms volume (ball 0 r) u) atTop (𝓝 0) := hu.2
  obtain ⟨v, M, hM, hgrowth⟩ := exists_dot_growth (A := homogenizedMatrix P) hθ0 (by linarith)
    hC50.le hn1 hδ (hX₅1 a) hX₅r H50 hsol hu2
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = 2 - ((n : ℝ) + 1) * δ := ⟨_, rfl⟩
  rw [← hσ] at hgrowth hσ0 hσ1
  obtain ⟨φ, hφ, hφb⟩ := ha2 (fun x => dot v x) (dot_mem_harmonicPolys _ v)
  -- `u - φ ∈ A_0`
  obtain ⟨K0, hK0⟩ : ∃ K0, K0 = Real.sqrt ((θ 2)⁻¹ ^ d) * M * θ 2 ^ (-σ) := ⟨_, rfl⟩
  obtain ⟨nv, hnv⟩ : ∃ nv, nv = scalarRms volume (ball (0 : Vec d) 1) (fun x => dot v x) :=
    ⟨_, rfl⟩
  have hA0 : (fun x => u x - φ x) ∈ solutionGrowthSpace a 0 := by
    refine ⟨fun R hR => (hsol R hR).sub (isSolutionBall_of_mem_solutionGrowthSpace hφ hR), ?_⟩
    have hlim : Tendsto (fun r : ℝ => K0 * r ^ (-(1 - σ)) + C₂ * nv * r ^ (-δ₂)) atTop (𝓝 0) := by
      have := ((tendsto_rpow_neg_atTop (by linarith : 0 < 1 - σ)).const_mul K0).add
        ((tendsto_rpow_neg_atTop hδ₂0).const_mul (C₂ * nv))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with r hr
      exact mul_nonneg (by positivity) (scalarRms_nonneg _ _)
    · filter_upwards [eventually_ge_atTop r₀] with r hr
      have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
      have hr0' : r ≠ 0 := hr0.ne'
      have h1 : scalarRms volume (ball 0 r) (fun x => u x - dot v x) ≤ K0 * r ^ σ := by
        rw [hK0]
        exact scalarRms_le_of_radii hθ0 (by linarith) hr₀ hσ0 hM
          (fun R hR => (hsol R hR).1.sub (memLp_dot_ball v R)) hgrowth hr
      have h2 : scalarRms volume (ball 0 r) (fun x => φ x - dot v x) ≤ C₂ * nv * r ^ (-δ₂) * r := by
        have h := hφb r (hX₂r.trans hr)
        rw [scalarRms_dot_ball v hr0, ← hnv] at h
        calc _ ≤ _ := h
          _ = _ := by ring
      have h3 : scalarRms volume (ball 0 r) (fun x => u x - φ x) ≤
          scalarRms volume (ball 0 r) (fun x => u x - dot v x) +
            scalarRms volume (ball 0 r) (fun x => φ x - dot v x) := by
        calc _ = scalarRms volume (ball 0 r)
              (fun x => (u x - dot v x) - (φ x - dot v x)) := by
              congr 1
              funext x
              ring
          _ ≤ _ := scalarRms_sub_le (f := fun x => u x - dot v x) (g := fun x => φ x - dot v x)
              ((hsol r hr0).1.sub (memLp_dot_ball v r))
              ((hφ.1 r hr0).1.sub (memLp_dot_ball v r))
      have e1 : r⁻¹ * (K0 * r ^ σ) = K0 * r ^ (-(1 - σ)) := by
        rw [neg_sub, Real.rpow_sub_one hr0.ne']
        field_simp
      have e2 : r⁻¹ * (C₂ * nv * r ^ (-δ₂) * r) = C₂ * nv * r ^ (-δ₂) := by
        field_simp
      simp only [zero_add, pow_one]
      calc r⁻¹ * scalarRms volume (ball 0 r) (fun x => u x - φ x)
          ≤ r⁻¹ * (K0 * r ^ σ + C₂ * nv * r ^ (-δ₂) * r) :=
            mul_le_mul_of_nonneg_left (h3.trans (add_le_add h1 h2)) (inv_nonneg.2 hr0.le)
        _ = _ := by rw [mul_add, e1, e2]
  -- `(i)₀`: `u - φ` is a constant
  obtain ⟨c, ⟨⟨Pc, hPc, hPce⟩, -⟩, hce⟩ := hi0 _ hA0
  have hcconst : ∀ x, c x = Pc.coeff 0 := fun x => by
    rw [hPce x, eval_eq_sum_homogeneousComponent hPc, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, MvPolynomial.homogeneousComponent_zero, MvPolynomial.eval_C]
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ = Pc.coeff 0 := ⟨_, rfl⟩
  refine ⟨fun x => dot v x + c₀,
    add_mem_harmonicPolys (dot_mem_harmonicPolys _ v) (const_mem_harmonicPolys _ 1 c₀),
    fun R hR' => ?_⟩
  have hR : r₀ ≤ R := by rw [hr₀def]; exact hR'
  have hR0 : 0 < R := lt_of_lt_of_le hr₀ hR
  have hae : scalarRms volume (ball 0 R) (fun x => u x - (dot v x + c₀)) =
      scalarRms volume (ball 0 R) (fun x => φ x - dot v x) := by
    refine scalarRms_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hce] with x hx
    rw [hcconst, ← hc₀] at hx
    linarith
  -- (3.27) for `p = v·x + c₀`
  have hQ1 : MvPolynomial.homogeneousComponent 1
      ((∑ i, MvPolynomial.C (v i) * MvPolynomial.X i) + MvPolynomial.C c₀) =
      ∑ i, MvPolynomial.C (v i) * MvPolynomial.X i := by
    rw [map_add, MvPolynomial.homogeneousComponent_eq_self
      (MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => MvPolynomial.isHomogeneous_C_mul_X _ _),
      MvPolynomial.homogeneousComponent_eq_zero _ _ (by simp), add_zero]
  have hQdeg : ((∑ i, MvPolynomial.C (v i) * MvPolynomial.X i) +
      MvPolynomial.C c₀ : MvPolynomial (Fin d) ℝ).totalDegree ≤ 1 :=
    (MvPolynomial.totalDegree_add _ _).trans (max_le (totalDegree_sum_C_mul_X_le v) (by simp))
  have hcomp : scalarRms volume (ball 0 R) (fun x => dot v x) ≤
      C27 * scalarRms volume (ball 0 R) (fun x => dot v x + c₀) := by
    have h := (h27 _ hQdeg R hR0).2
    have hsingle := Finset.single_le_sum (f := fun m => scalarRms volume (ball 0 R)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m
        ((∑ i, MvPolynomial.C (v i) * MvPolynomial.X i) + MvPolynomial.C c₀))))
      (fun i _ => scalarRms_nonneg _ _) (by simp : 1 ∈ Finset.range (1 + 1))
    beta_reduce at hsingle
    simp only [hQ1, eval_sum_C_mul_X] at hsingle
    have e : (fun x => MvPolynomial.eval x
        ((∑ i, MvPolynomial.C (v i) * MvPolynomial.X i) + MvPolynomial.C c₀)) =
        fun x => dot v x + c₀ := by
      funext x
      rw [map_add, eval_sum_C_mul_X, MvPolynomial.eval_C]
    rw [e] at h
    exact hsingle.trans h
  rw [hae]
  calc scalarRms volume (ball 0 R) (fun x => φ x - dot v x)
      ≤ C₂ * R ^ (-δ₂) * scalarRms volume (ball 0 R) (fun x => dot v x) :=
        hφb R (hX₂r.trans hR)
    _ ≤ C₂ * R ^ (-δ₂) * (C27 * scalarRms volume (ball 0 R) (fun x => dot v x + c₀)) :=
        mul_le_mul_of_nonneg_left hcomp (mul_nonneg hC₂ (Real.rpow_nonneg hR0.le _))
    _ = _ := by ring

end QSH
