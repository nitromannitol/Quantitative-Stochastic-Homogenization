import QuantitativeStochasticHomogenization.Ch03.Sec03.GrowthIterationHigher
import QuantitativeStochasticHomogenization.Ch03.Sec03.Theorem38IITwo

/-!
# Statement `(i)₂` of Theorem 3.8

Armstrong–Kuusi–Mourrat, Theorem 3.8, statement `(i)_k` for `k = 2`, through (3.47): the implication
(3.47) for every `k ≥ 1`, deterministic (`implication_347`): (3.51), `(i)_{k-1}` and `(ii)_k` give
`(i)_k`. With `(i)₁` (`theorem_3_8_i_one`) and `(ii)₂` (`theorem_3_8_ii_two`), above a random scale
`X ≤ O_s(C)` and for almost every coefficient field, every `u ∈ A_2` has some `p ∈ Ā_2` with
`‖u - p‖_{L̲²(B_R)} ≤ C R^{-δ} ‖p‖_{L̲²(B_R)}` for every `R ≥ X` (`theorem_3_8_i_two`).
-/

open MeasureTheory Filter Set Topology

noncomputable section

namespace QSH

variable {d : ℕ}

theorem harmonicPolys_mono {A : Mat d} {k k' : ℕ} (hkk : k ≤ k') {p : Vec d → ℝ}
    (hp : p ∈ harmonicPolys A k) : p ∈ harmonicPolys A k' := by
  obtain ⟨⟨P, hP, hPe⟩, hph⟩ := hp
  exact ⟨⟨P, hP.trans hkk, hPe⟩, hph⟩

/-- **The implication (3.47)**, for every `k ≥ 1`, deterministic: the growth iteration (with (3.51)
above `X`), `(ii)_k` and `(i)_{k-1}` above `r₀` give `(i)_k` above `r₀`. -/
theorem implication_347 {Λ : ℝ} {a : CoefficientField d Λ} {A : Mat d}
    {θ C₅ δ X r₀ C₁ C₂ δ₁ δ₂ C27 : ℝ} {k n : ℕ} (hk : 1 ≤ k) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hC₅ : 0 ≤ C₅) (hn : 1 ≤ n) (hδ : δ = 2 / (2 * n + 1)) (hX1 : 1 ≤ X) (hXr : X ≤ r₀)
    (H50 : ∀ r : ℝ, X ≤ r → ∀ v, IsSolutionBall a r v →
      harmonicFlatness A (k + 1) v (θ * r) ≤
        1 / 4 * θ ^ (((k + 1 : ℕ) : ℝ) + 1 - δ / 2) * harmonicFlatness A (k + 1) v r +
          C₅ * r ^ (-δ) * scalarRms volume (ball 0 r) v)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hC27 : 0 ≤ C27)
    (h27 : ∀ Q : MvPolynomial (Fin d) ℝ, Q.totalDegree ≤ k → ∀ r : ℝ, 0 < r →
      scalarRms volume (ball 0 r)
          (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent k Q)) ≤
        C27 * scalarRms volume (ball 0 r) (fun x => MvPolynomial.eval x Q))
    (Hii : ∀ q ∈ harmonicPolys A k, ∃ φ ∈ solutionGrowthSpace a k, ∀ R : ℝ, r₀ ≤ R →
      scalarRms volume (ball 0 R) (fun x => φ x - q x) ≤
        C₂ * R ^ (-δ₂) * scalarRms volume (ball 0 R) q)
    (Hi : ∀ w ∈ solutionGrowthSpace a (k - 1), ∃ p ∈ harmonicPolys A (k - 1), ∀ R : ℝ, r₀ ≤ R →
      scalarRms volume (ball 0 R) (fun x => w x - p x) ≤
        C₁ * R ^ (-δ₁) * scalarRms volume (ball 0 R) p)
    {u : Vec d → ℝ} (hu : u ∈ solutionGrowthSpace a k) :
    ∃ p ∈ harmonicPolys A k, ∀ R : ℝ, r₀ ≤ R →
      scalarRms volume (ball 0 R) (fun x => u x - p x) ≤
        (C₂ * C27 + C₁ * (1 + C27)) * R ^ (-min δ₁ δ₂) * scalarRms volume (ball 0 R) p := by
  have hr₀1 : 1 ≤ r₀ := hX1.trans hXr
  have hr₀ : 0 < r₀ := by linarith
  have hsol : ∀ R : ℝ, 0 < R → IsSolutionBall a R u := fun R hR =>
    isSolutionBall_of_mem_solutionGrowthSpace hu hR
  obtain ⟨q, hq, M, hM, hgrowth⟩ := exists_homogeneous_growth (A := A) hθ0 hθ1 hC₅ hn hδ hX1 hXr
    H50 hsol hu.2
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h2n : (0 : ℝ) < 2 * n + 1 := by positivity
  have hnδ : ((n : ℝ) + 1) * δ = (2 * n + 2) / (2 * n + 1) := by
    rw [hδ]
    field_simp
  have hn1δ : 1 < ((n : ℝ) + 1) * δ := by
    rw [hnδ, one_lt_div h2n]; linarith
  have hn1δ2 : ((n : ℝ) + 1) * δ < 2 := by
    rw [hnδ, div_lt_iff₀ h2n]; linarith
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = (k : ℝ) + 1 - ((n : ℝ) + 1) * δ := ⟨_, rfl⟩
  rw [← hσ] at hgrowth
  have hσ0 : 0 ≤ σ := by rw [hσ]; linarith
  have hσ1 : σ < k := by rw [hσ]; linarith
  obtain ⟨φ, hφ, hφb⟩ := Hii q hq.1
  obtain ⟨K0, hK0⟩ : ∃ K0, K0 = Real.sqrt (θ⁻¹ ^ d) * M * θ ^ (-σ) := ⟨_, rfl⟩
  obtain ⟨nq, hnq⟩ : ∃ nq, nq = scalarRms volume (ball (0 : Vec d) 1) q := ⟨_, rfl⟩
  have hqball : ∀ r : ℝ, 0 < r → scalarRms volume (ball 0 r) q = r ^ k * nq := fun r hr => by
    have h := scalarRms_ball_homogeneous (k := k) (q := q) (fun t _ x => homogeneousHarmonic_smul hq t x)
      (r := 1) hr
    rwa [mul_one, ← hnq] at h
  -- `u - φ ∈ A_{k-1}`
  have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hA : (fun x => u x - φ x) ∈ solutionGrowthSpace a (k - 1) := by
    refine ⟨fun R hR => (hsol R hR).sub (isSolutionBall_of_mem_solutionGrowthSpace hφ hR), ?_⟩
    rw [hk1]
    have hlim : Tendsto (fun r : ℝ => K0 * r ^ (-((k : ℝ) - σ)) + C₂ * nq * r ^ (-δ₂)) atTop
        (𝓝 0) := by
      have := ((tendsto_rpow_neg_atTop (by linarith : 0 < (k : ℝ) - σ)).const_mul K0).add
        ((tendsto_rpow_neg_atTop hδ₂).const_mul (C₂ * nq))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with r hr
      exact mul_nonneg (by positivity) (scalarRms_nonneg _ _)
    · filter_upwards [eventually_ge_atTop r₀] with r hr
      have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
      have hr0' : r ≠ 0 := hr0.ne'
      have h1 : scalarRms volume (ball 0 r) (fun x => u x - q x) ≤ K0 * r ^ σ := by
        rw [hK0]
        exact scalarRms_le_of_radii hθ0 hθ1 hr₀ hσ0 hM
          (fun R hR => (hsol R hR).1.sub (memLp_of_mem_homogeneousHarmonic hq R)) hgrowth hr
      have h2 : scalarRms volume (ball 0 r) (fun x => φ x - q x) ≤ C₂ * nq * r ^ (-δ₂) * r ^ k := by
        have h := hφb r hr
        rw [hqball r hr0] at h
        calc _ ≤ _ := h
          _ = _ := by ring
      have h3 : scalarRms volume (ball 0 r) (fun x => u x - φ x) ≤
          scalarRms volume (ball 0 r) (fun x => u x - q x) +
            scalarRms volume (ball 0 r) (fun x => φ x - q x) := by
        calc _ = scalarRms volume (ball 0 r) (fun x => (u x - q x) - (φ x - q x)) := by
              congr 1
              funext x
              ring
          _ ≤ _ := scalarRms_sub_le (f := fun x => u x - q x) (g := fun x => φ x - q x)
              ((hsol r hr0).1.sub (memLp_of_mem_homogeneousHarmonic hq r))
              ((hφ.1 r hr0).1.sub (memLp_of_mem_homogeneousHarmonic hq r))
      have hrk : 0 < r ^ k := pow_pos hr0 k
      have e1 : (r ^ k)⁻¹ * (K0 * r ^ σ) = K0 * r ^ (-((k : ℝ) - σ)) := by
        rw [neg_sub, Real.rpow_sub hr0, Real.rpow_natCast]
        field_simp
      have e2 : (r ^ k)⁻¹ * (C₂ * nq * r ^ (-δ₂) * r ^ k) = C₂ * nq * r ^ (-δ₂) := by
        field_simp
      calc (r ^ k)⁻¹ * scalarRms volume (ball 0 r) (fun x => u x - φ x)
          ≤ (r ^ k)⁻¹ * (K0 * r ^ σ + C₂ * nq * r ^ (-δ₂) * r ^ k) :=
            mul_le_mul_of_nonneg_left (h3.trans (add_le_add h1 h2)) (inv_nonneg.2 hrk.le)
        _ = _ := by rw [mul_add, e1, e2]
  -- `(i)_{k-1}`
  obtain ⟨pt, hpt, hptb⟩ := Hi _ hA
  refine ⟨fun x => q x + pt x, add_mem_harmonicPolys hq.1 (harmonicPolys_mono (Nat.sub_le k 1) hpt),
    fun R hR => ?_⟩
  have hR0 : 0 < R := lt_of_lt_of_le hr₀ hR
  have hR1 : 1 ≤ R := hr₀1.trans hR
  -- (3.27): `‖q‖ ≤ C27 ‖p‖`
  obtain ⟨-, Pq, hPq, hqP⟩ := hq
  obtain ⟨⟨Pt, hPt, hptP⟩, -⟩ := hpt
  have hPqh : Pq.IsHomogeneous k := hPq
  have hQdeg : (Pq + Pt).totalDegree ≤ k :=
    (MvPolynomial.totalDegree_add _ _).trans (max_le hPqh.totalDegree_le (hPt.trans (Nat.sub_le k 1)))
  have hQk : MvPolynomial.homogeneousComponent k (Pq + Pt) = Pq := by
    rw [map_add, MvPolynomial.homogeneousComponent_eq_self hPqh,
      MvPolynomial.homogeneousComponent_eq_zero _ _ (by omega), add_zero]
  have hqp : scalarRms volume (ball 0 R) q ≤
      C27 * scalarRms volume (ball 0 R) (fun x => q x + pt x) := by
    have h := h27 (Pq + Pt) hQdeg R hR0
    rw [hQk] at h
    have e1 : (fun x => MvPolynomial.eval x Pq) = q := funext fun x => (hqP x).symm
    have e2 : (fun x => MvPolynomial.eval x (Pq + Pt)) = fun x => q x + pt x :=
      funext fun x => by rw [map_add, hqP, hptP]
    rwa [e1, e2] at h
  have hptp : scalarRms volume (ball 0 R) pt ≤
      (1 + C27) * scalarRms volume (ball 0 R) (fun x => q x + pt x) := by
    have hmq : MemLp q 2 (volume.restrict (ball (0 : Vec d) R)) := by
      rw [show q = fun x => MvPolynomial.eval x Pq from funext hqP]; exact memLp_eval_ball _ R
    have hmt : MemLp pt 2 (volume.restrict (ball (0 : Vec d) R)) := by
      rw [show pt = fun x => MvPolynomial.eval x Pt from funext hptP]; exact memLp_eval_ball _ R
    have h := scalarRms_le_add_of_sub (f := fun x => q x + pt x) (g := pt) (hmq.add hmt) hmt
    have e : (fun x => (q x + pt x) - pt x) = q := funext fun x => by ring
    rw [e] at h
    linarith
  -- the estimate
  have hm1 : R ^ (-δ₁) ≤ R ^ (-min δ₁ δ₂) :=
    Real.rpow_le_rpow_of_exponent_le hR1 (by have := min_le_left δ₁ δ₂; linarith)
  have hm2 : R ^ (-δ₂) ≤ R ^ (-min δ₁ δ₂) :=
    Real.rpow_le_rpow_of_exponent_le hR1 (by have := min_le_right δ₁ δ₂; linarith)
  have hφq := hφb R hR
  have hupt := hptb R hR
  have hmu : MemLp (fun x => u x - φ x - pt x) 2 (volume.restrict (ball (0 : Vec d) R)) :=
    (((hsol R hR0).1.sub (hφ.1 R hR0).1)).sub (by
      rw [show pt = fun x => MvPolynomial.eval x Pt from funext hptP]; exact memLp_eval_ball _ R)
  have hmφ : MemLp (fun x => φ x - q x) 2 (volume.restrict (ball (0 : Vec d) R)) :=
    ((hφ.1 R hR0).1).sub (by
      rw [show q = fun x => MvPolynomial.eval x Pq from funext hqP]; exact memLp_eval_ball _ R)
  have hsplit : scalarRms volume (ball 0 R) (fun x => u x - (q x + pt x)) ≤
      scalarRms volume (ball 0 R) (fun x => φ x - q x) +
        scalarRms volume (ball 0 R) (fun x => u x - φ x - pt x) := by
    calc _ = scalarRms volume (ball 0 R) (fun x => (φ x - q x) + (u x - φ x - pt x)) := by
          congr 1
          funext x
          ring
      _ ≤ _ := scalarRms_add_le (f := fun x => φ x - q x) (g := fun x => u x - φ x - pt x) hmφ hmu
  have hn0 := scalarRms_nonneg (ball (0 : Vec d) R) q
  have hn1 := scalarRms_nonneg (ball (0 : Vec d) R) pt
  have hRm : 0 ≤ R ^ (-min δ₁ δ₂) := Real.rpow_nonneg hR0.le _
  have hb1 : C₂ * R ^ (-δ₂) * scalarRms volume (ball 0 R) q ≤
      C₂ * R ^ (-min δ₁ δ₂) * (C27 * scalarRms volume (ball 0 R) (fun x => q x + pt x)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hm2 hC₂) hqp hn0 (mul_nonneg hC₂ hRm)
  have hb2 : C₁ * R ^ (-δ₁) * scalarRms volume (ball 0 R) pt ≤
      C₁ * R ^ (-min δ₁ δ₂) * ((1 + C27) * scalarRms volume (ball 0 R) (fun x => q x + pt x)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hm1 hC₁) hptp hn1 (mul_nonneg hC₁ hRm)
  calc _ ≤ _ := hsplit
    _ ≤ C₂ * R ^ (-δ₂) * scalarRms volume (ball 0 R) q +
        C₁ * R ^ (-δ₁) * scalarRms volume (ball 0 R) pt := add_le_add hφq hupt
    _ ≤ _ := add_le_add hb1 hb2
    _ = _ := by ring

/-- **Theorem 3.8 `(i)₂`**, for `d ≥ 2`, `Λ > 1` and `s ∈ (0, d)`: there are `δ ∈ (0, ½]` and `C`
such that, for every law satisfying the assumptions, a random variable `X ≥ 1` with `X ≤ O_s(C)`
satisfies, for almost every coefficient field: for every `u ∈ A_2` there is `p ∈ Ā_2` with
`‖u - p‖_{L̲²(B_R)} ≤ C R^{-δ} ‖p‖_{L̲²(B_R)}` for every `R ≥ X`. -/
theorem theorem_3_8_i_two (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) {s : ℝ} (hs : 0 < s)
    (hsd : s < d) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∃ C CX : ℝ, 0 ≤ C ∧ 0 < CX ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∃ X : CoefficientField d Λ → ℝ, OsBound P X s CX ∧ (∀ a, 1 ≤ X a) ∧ ∀ᵐ a ∂P,
        ∀ u ∈ solutionGrowthSpace a 2, ∃ p ∈ harmonicPolys (homogenizedMatrix P) 2,
          ∀ R : ℝ, X a ≤ R → scalarRms volume (ball 0 R) (fun x => u x - p x) ≤
            C * R ^ (-δ) * scalarRms volume (ball 0 R) p := by
  obtain ⟨δ₁, hδ₁0, hδ₁2, C₁, CX₁, hC₁, hCX₁, hi1⟩ := theorem_3_8_i_one hd hΛ hs hsd
  obtain ⟨δ₂, hδ₂0, -, C₂, CX₂, hC₂, hCX₂, hii2⟩ := theorem_3_8_ii_two hd hΛ hs hsd
  obtain ⟨δ₀, hδ₀0, -, h50all⟩ := equation_3_50 hd hΛ hs hsd
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌈1 / δ₀⌉₊ := ⟨_, rfl⟩
  have hn1 : 1 ≤ n := by
    rw [hn]
    exact Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  have hn' : 1 / δ₀ ≤ n := by rw [hn]; exact Nat.le_ceil _
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 2 / (2 * n + 1) := ⟨_, rfl⟩
  have h2n : (0 : ℝ) < 2 * n + 1 := by positivity
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδδ₀ : δ ≤ δ₀ := by
    rw [hδ, div_le_iff₀ h2n]
    rw [div_le_iff₀ hδ₀0] at hn'
    nlinarith
  obtain ⟨θ, C5, CX5, hCX5, hθC, h50⟩ := h50all δ hδ0 hδδ₀
  obtain ⟨hθ0, hθ1, hC50⟩ := hθC 3
  obtain ⟨C27, hC27, h27⟩ := scalarRms_homogeneousComponents_zero (d := d) 2
  have h27' : ∀ Q : MvPolynomial (Fin d) ℝ, Q.totalDegree ≤ 2 → ∀ r : ℝ, 0 < r →
      scalarRms volume (ball 0 r)
          (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 2 Q)) ≤
        C27 * scalarRms volume (ball 0 r) (fun x => MvPolynomial.eval x Q) := fun Q hQ r hr => by
    have h := (h27 Q hQ r hr).2
    have hs := Finset.single_le_sum (f := fun m => scalarRms volume (ball 0 r)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q)))
      (fun i _ => scalarRms_nonneg _ _) (by simp : 2 ∈ Finset.range (2 + 1))
    exact hs.trans h
  refine ⟨min δ₁ δ₂, lt_min hδ₁0 hδ₂0, (min_le_left _ _).trans hδ₁2, C₂ * C27 + C₁ * (1 + C27),
    (2 : ℝ) ^ s⁻¹ * max ((2 : ℝ) ^ s⁻¹ * max CX₁ CX₂) CX5, by positivity, by positivity,
    fun P hP => ?_⟩
  obtain ⟨X₁, hX₁os, hX₁1, hX₁ae⟩ := hi1 P hP
  obtain ⟨X₂, hX₂os, hX₂1, hX₂ae⟩ := hii2 P hP
  obtain ⟨X₅, hX₅os, hX₅1, hX₅ae⟩ := h50 P hP
  refine ⟨fun a => max (max (X₁ a) (X₂ a)) (X₅ a), osBound_max (osBound_max hX₁os hX₂os) hX₅os,
    fun a => le_max_of_le_left (le_max_of_le_left (hX₁1 a)), ?_⟩
  filter_upwards [hX₁ae, hX₂ae, hX₅ae] with a ha1 ha2 ha5
  intro u hu
  obtain ⟨r₀, hr₀def⟩ : ∃ r₀, r₀ = max (max (X₁ a) (X₂ a)) (X₅ a) := ⟨_, rfl⟩
  have hX₁r : X₁ a ≤ r₀ := by rw [hr₀def]; exact le_max_of_le_left (le_max_left _ _)
  have hX₂r : X₂ a ≤ r₀ := by rw [hr₀def]; exact le_max_of_le_left (le_max_right _ _)
  have hX₅r : X₅ a ≤ r₀ := by rw [hr₀def]; exact le_max_right _ _
  have hr₀1 : 1 ≤ r₀ := (hX₅1 a).trans hX₅r
  obtain ⟨p, hp, hpb⟩ := implication_347 (k := 2) (n := n) (A := homogenizedMatrix P) (by norm_num)
    hθ0 (by linarith) hC50.le hn1 hδ (hX₅1 a) hX₅r (fun r hr v hv => ha5 3 r hr v hv) hC₁ hC₂ hδ₁0
    hδ₂0 hC27 h27'
    (fun q hq => by
      obtain ⟨φ, hφ, hb⟩ := ha2 q hq
      exact ⟨φ, hφ, fun R hR => hb R (hX₂r.trans hR)⟩)
    (fun w hw => by
      obtain ⟨p', hp', hb⟩ := ha1 w hw
      exact ⟨p', hp', fun R hR => hb R (hX₁r.trans hR)⟩)
    hu
  refine ⟨p, hp, fun R hR => hpb R ?_⟩
  rw [hr₀def]
  exact hR

end QSH
