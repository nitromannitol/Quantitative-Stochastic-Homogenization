import QuantitativeStochasticHomogenization.Ch03.Sec03.Theorem38ITwo
import QuantitativeStochasticHomogenization.Ch03.Sec03.Theorem38IIIPrimeTwo

/-!
# Statement `(iii)₁` of Theorem 3.8

Armstrong–Kuusi–Mourrat, Theorem 3.8, statement `(iii)_k` for `k = 1`, through (3.49): the
implication (3.49) for every `k`, deterministic (`implication_349`): `(i)_{k+1}`, `(ii)_{k+1}` and
`(iii')_{k+1}` give `(iii)_k`, the estimate (3.41) with the exponent `k + 1`. With `(i)₂`
(`theorem_3_8_i_two`), `(ii)₂` (`theorem_3_8_ii_two`) and `(iii')₂` (`theorem_3_8_iii_prime_two`),
above a random scale `X ≤ O_s(C)` and for almost every coefficient field, for every `R ≥ X` and every
solution `u` in `B_R` some `φ ∈ A_1` satisfies `‖u - φ‖_{L̲²(B_r)} ≤ C (r/R)² ‖u‖_{L̲²(B_R)}` for every
`r ∈ [X, R]` (`theorem_3_8_iii_one`).
-/

open MeasureTheory Filter Set Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- **The implication (3.49)**, for every `k`, deterministic: `(iii')_{k+1}`, `(i)_{k+1}` and
`(ii)_{k+1}` above `X` (with the smallness `C₁ X^{-δ₁} ≤ ½` of the constant of `(i)_{k+1}`) give
`(iii)_k` above `X`. -/
theorem implication_349 {Λ : ℝ} {a : CoefficientField d Λ} {A : Mat d} {k : ℕ}
    {X C₁ C₂ C₃ δ₁ δ₂ δ₃ C27 : ℝ} (hX1 : 1 ≤ X) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hC27 : 0 ≤ C27) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : δ₃ ≤ 2)
    (hsmall : C₁ * X ^ (-δ₁) ≤ 1 / 2)
    (h27 : ∀ Q : MvPolynomial (Fin d) ℝ, Q.totalDegree ≤ k + 1 → ∀ r : ℝ, 0 < r →
      scalarRms volume (ball 0 r)
          (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent (k + 1) Q)) ≤
        C27 * scalarRms volume (ball 0 r) (fun x => MvPolynomial.eval x Q))
    (Hiii : ∀ R : ℝ, X ≤ R → ∀ u, IsSolutionBall a R u → ∃ ψ ∈ solutionGrowthSpace a (k + 1),
      ∀ r : ℝ, X ≤ r → r ≤ R → scalarRms volume (ball 0 r) (fun x => u x - ψ x) ≤
        C₃ * (r / R) ^ (((k + 1 : ℕ) : ℝ) + 1 - δ₃ / 2) * scalarRms volume (ball 0 R) u)
    (Hi : ∀ ψ ∈ solutionGrowthSpace a (k + 1), ∃ p ∈ harmonicPolys A (k + 1), ∀ r : ℝ, X ≤ r →
      scalarRms volume (ball 0 r) (fun x => ψ x - p x) ≤
        C₁ * r ^ (-δ₁) * scalarRms volume (ball 0 r) p)
    (Hii : ∀ q ∈ harmonicPolys A (k + 1), ∃ ψ ∈ solutionGrowthSpace a (k + 1), ∀ r : ℝ, X ≤ r →
      scalarRms volume (ball 0 r) (fun x => ψ x - q x) ≤
        C₂ * r ^ (-δ₂) * scalarRms volume (ball 0 r) q)
    {R : ℝ} (hR : X ≤ R) {u : Vec d → ℝ} (hu : IsSolutionBall a R u) :
    ∃ φ ∈ solutionGrowthSpace a k, ∀ r : ℝ, X ≤ r → r ≤ R →
      scalarRms volume (ball 0 r) (fun x => u x - φ x) ≤
        (C₃ + 2 * (1 + C₂) * C27 * (1 + C₃)) * (r / R) ^ (k + 1) *
          scalarRms volume (ball 0 R) u := by
  have hR1 : 1 ≤ R := hX1.trans hR
  have hR0 : 0 < R := by linarith
  have hX0 : 0 < X := by linarith
  obtain ⟨ψ, hψ, hψb⟩ := Hiii R hR u hu
  obtain ⟨p, hp, hpb⟩ := Hi ψ hψ
  obtain ⟨⟨Pp, hPp, hpP⟩, -⟩ := id hp
  have hqA := homogeneousComponent_mem_harmonicPolys hp hPp hpP (k + 1)
  obtain ⟨q, hqdef⟩ : ∃ q : Vec d → ℝ,
      q = fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent (k + 1) Pp) := ⟨_, rfl⟩
  rw [← hqdef] at hqA
  have hq : ∀ t : ℝ, 0 < t → ∀ x, q (t • x) = t ^ (k + 1) * q x := fun t _ x => by
    rw [hqdef]
    exact PDE.eval_smul_of_isHomogeneous
      (MvPolynomial.homogeneousComponent_isHomogeneous (k + 1) Pp) t x
  obtain ⟨ψt, hψt, hψtb⟩ := Hii q hqA
  have hpfun : p = fun x => MvPolynomial.eval x Pp := funext hpP
  have hmemψ : ∀ r : ℝ, 0 < r → MemLp ψ 2 (volume.restrict (ball (0 : Vec d) r)) :=
    fun r hr => (hψ.1 r hr).1
  have hmemψt : ∀ r : ℝ, 0 < r → MemLp ψt 2 (volume.restrict (ball (0 : Vec d) r)) :=
    fun r hr => (hψt.1 r hr).1
  have hmemp : ∀ r : ℝ, MemLp p 2 (volume.restrict (ball (0 : Vec d) r)) := fun r => by
    rw [hpfun]; exact memLp_eval_ball _ r
  have hmemq : ∀ r : ℝ, MemLp q 2 (volume.restrict (ball (0 : Vec d) r)) := fun r => by
    rw [hqdef]; exact memLp_eval_ball _ r
  -- the sizes at the scale `R`
  have hψR : scalarRms volume (ball 0 R) ψ ≤ (1 + C₃) * scalarRms volume (ball 0 R) u := by
    have h := hψb R hR le_rfl
    rw [div_self hR0.ne', Real.one_rpow, mul_one] at h
    have h2 := scalarRms_le_add_of_sub hu.1 (hmemψ R hR0)
    linarith
  have hpR : scalarRms volume (ball 0 R) p ≤ 2 * scalarRms volume (ball 0 R) ψ := by
    have h := hpb R hR
    have hs : C₁ * R ^ (-δ₁) ≤ 1 / 2 :=
      le_trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hX0 hR (by linarith)) hC₁) hsmall
    have h2 := scalarRms_le_add_of_sub (hmemψ R hR0) (hmemp R)
    have hn := scalarRms_nonneg (ball (0 : Vec d) R) p
    nlinarith
  have hqR : scalarRms volume (ball 0 R) q ≤ C27 * scalarRms volume (ball 0 R) p := by
    have h := h27 Pp hPp R hR0
    rw [← hqdef, ← hpfun] at h
    exact h
  have hqr : ∀ r : ℝ, 0 < r → scalarRms volume (ball 0 r) q =
      (r / R) ^ (k + 1) * scalarRms volume (ball 0 R) q := fun r hr => by
    have h := scalarRms_ball_homogeneous hq (r := R) (div_pos hr hR0)
    rwa [div_mul_cancel₀ _ hR0.ne'] at h
  have hψtr : ∀ r : ℝ, X ≤ r → scalarRms volume (ball 0 r) ψt ≤
      (1 + C₂) * scalarRms volume (ball 0 r) q := fun r hr => by
    have hr0 : 0 < r := by linarith
    have h := hψtb r hr
    have hpow : r ^ (-δ₂) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (hX1.trans hr) (by linarith)
    have h2 := abs_scalarRms_sub_le (hmemψt r hr0) (hmemq r)
    have hn := scalarRms_nonneg (ball (0 : Vec d) r) q
    have h3 : C₂ * r ^ (-δ₂) * scalarRms volume (ball 0 r) q ≤ C₂ * scalarRms volume (ball 0 r) q := by
      have := mul_le_mul_of_nonneg_right hpow hn
      nlinarith
    have h4 := (abs_le.1 h2).2
    linarith
  refine ⟨fun x => ψ x - ψt x, ⟨fun R' hR' => (isSolutionBall_of_mem_solutionGrowthSpace hψ hR').sub
    (isSolutionBall_of_mem_solutionGrowthSpace hψt hR'), ?_⟩, fun r hr hrR => ?_⟩
  · -- `ψ - ψt ∈ A_k`
    obtain ⟨Cg, hCg, hgrow⟩ := scalarRms_poly_growth (d := d) (k + 1)
    obtain ⟨Cg', hCg', hgrow'⟩ := scalarRms_poly_growth (d := d) k
    obtain ⟨Pk, hPk⟩ : ∃ Pk : MvPolynomial (Fin d) ℝ,
        Pk = ∑ m ∈ Finset.range (k + 1), MvPolynomial.homogeneousComponent m Pp := ⟨_, rfl⟩
    have hPkdeg : Pk.totalDegree ≤ k := by
      rw [hPk]
      refine MvPolynomial.totalDegree_finsetSum_le fun m hm => ?_
      exact (MvPolynomial.homogeneousComponent_isHomogeneous m Pp).totalDegree_le.trans
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm))
    have hpq : ∀ x, p x - q x = MvPolynomial.eval x Pk := fun x => by
      simp only [hqdef]
      rw [hpP, eval_eq_sum_homogeneousComponent hPp, Finset.sum_range_succ, hPk, map_sum]
      ring
    obtain ⟨n1, hn1⟩ : ∃ n1, n1 = scalarRms volume (ball (0 : Vec d) 1) p := ⟨_, rfl⟩
    obtain ⟨n2, hn2⟩ : ∃ n2, n2 = scalarRms volume (ball (0 : Vec d) 1) q := ⟨_, rfl⟩
    obtain ⟨n3, hn3⟩ : ∃ n3, n3 = scalarRms volume (ball (0 : Vec d) 1)
        (fun x => MvPolynomial.eval x Pk) := ⟨_, rfl⟩
    have hlim : Tendsto (fun r : ℝ => C₁ * (Cg * n1) * r ^ (-δ₁) + C₂ * n2 * r ^ (-δ₂) +
        Cg' * n3 * r ^ (-(1 : ℝ))) atTop (𝓝 0) := by
      have := (((tendsto_rpow_neg_atTop hδ₁).const_mul (C₁ * (Cg * n1))).add
        ((tendsto_rpow_neg_atTop hδ₂).const_mul (C₂ * n2))).add
        ((tendsto_rpow_neg_atTop one_pos).const_mul (Cg' * n3))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with r hr
      exact mul_nonneg (by positivity) (scalarRms_nonneg _ _)
    · filter_upwards [eventually_ge_atTop X] with r hr
      have hr1 : 1 ≤ r := hX1.trans hr
      have hr0 : 0 < r := by linarith
      have hr0' : r ≠ 0 := hr0.ne'
      have hrk : 0 < r ^ (k + 1) := pow_pos hr0 _
      have hb1 : scalarRms volume (ball 0 r) (fun x => ψ x - p x) ≤
          C₁ * (Cg * n1) * r ^ (-δ₁) * r ^ (k + 1) := by
        have h := hgrow Pp hPp 1 r one_pos hr1
        rw [div_one, ← hpfun, ← hn1] at h
        calc _ ≤ C₁ * r ^ (-δ₁) * scalarRms volume (ball 0 r) p := hpb r hr
          _ ≤ C₁ * r ^ (-δ₁) * (Cg * r ^ (k + 1) * n1) :=
              mul_le_mul_of_nonneg_left h (mul_nonneg hC₁ (Real.rpow_nonneg hr0.le _))
          _ = _ := by ring
      have hb2 : scalarRms volume (ball 0 r) (fun x => ψt x - q x) ≤
          C₂ * n2 * r ^ (-δ₂) * r ^ (k + 1) := by
        have h := scalarRms_ball_homogeneous hq (r := 1) hr0
        rw [mul_one, ← hn2] at h
        calc _ ≤ C₂ * r ^ (-δ₂) * scalarRms volume (ball 0 r) q := hψtb r hr
          _ = _ := by rw [h]; ring
      have hb3 : scalarRms volume (ball 0 r) (fun x => p x - q x) ≤
          Cg' * n3 * r ^ (-(1 : ℝ)) * r ^ (k + 1) := by
        have e : (fun x => p x - q x) = fun x => MvPolynomial.eval x Pk := funext hpq
        rw [e]
        have h := hgrow' Pk hPkdeg 1 r one_pos hr1
        rw [div_one, ← hn3] at h
        have e2 : r ^ (-(1 : ℝ)) * r ^ (k + 1) = r ^ k := by
          rw [Real.rpow_neg_one, pow_succ]
          field_simp
        calc _ ≤ Cg' * r ^ k * n3 := h
          _ = Cg' * n3 * (r ^ (-(1 : ℝ)) * r ^ (k + 1)) := by rw [e2]; ring
          _ = _ := by ring
      have hsplit : scalarRms volume (ball 0 r) (fun x => ψ x - ψt x) ≤
          scalarRms volume (ball 0 r) (fun x => ψ x - p x) +
            scalarRms volume (ball 0 r) (fun x => ψt x - q x) +
            scalarRms volume (ball 0 r) (fun x => p x - q x) := by
        have m1 : MemLp (fun x => ψ x - p x) 2 (volume.restrict (ball (0 : Vec d) r)) :=
          (hmemψ r hr0).sub (hmemp r)
        have m2 : MemLp (fun x => ψt x - q x) 2 (volume.restrict (ball (0 : Vec d) r)) :=
          (hmemψt r hr0).sub (hmemq r)
        have m3 : MemLp (fun x => p x - q x) 2 (volume.restrict (ball (0 : Vec d) r)) :=
          (hmemp r).sub (hmemq r)
        calc _ = scalarRms volume (ball 0 r)
              (fun x => ((ψ x - p x) - (ψt x - q x)) + (p x - q x)) := by
              congr 1
              funext x
              ring
          _ ≤ scalarRms volume (ball 0 r) (fun x => (ψ x - p x) - (ψt x - q x)) +
              scalarRms volume (ball 0 r) (fun x => p x - q x) :=
              scalarRms_add_le (f := fun x => (ψ x - p x) - (ψt x - q x))
                (g := fun x => p x - q x) (m1.sub m2) m3
          _ ≤ _ := by
              have := scalarRms_sub_le (f := fun x => ψ x - p x) (g := fun x => ψt x - q x) m1 m2
              linarith
      calc (r ^ (k + 1))⁻¹ * scalarRms volume (ball 0 r) (fun x => ψ x - ψt x)
          ≤ (r ^ (k + 1))⁻¹ * ((C₁ * (Cg * n1) * r ^ (-δ₁) + C₂ * n2 * r ^ (-δ₂) +
              Cg' * n3 * r ^ (-(1 : ℝ))) * r ^ (k + 1)) := by
            refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hrk.le)
            have := add_le_add (add_le_add hb1 hb2) hb3
            linarith
        _ = _ := by field_simp
  · -- the estimate
    have hr0 : 0 < r := by linarith
    have hx0 : 0 < r / R := div_pos hr0 hR0
    have hx1 : r / R ≤ 1 := (div_le_one hR0).2 hrR
    have hexp : (r / R) ^ (((k + 1 : ℕ) : ℝ) + 1 - δ₃ / 2) ≤ (r / R) ^ (k + 1) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by push_cast; linarith)
    have hu0 := scalarRms_nonneg (ball (0 : Vec d) R) u
    have hxk : 0 ≤ (r / R) ^ (k + 1) := pow_nonneg hx0.le _
    have h1 : scalarRms volume (ball 0 r) (fun x => u x - ψ x) ≤
        C₃ * (r / R) ^ (k + 1) * scalarRms volume (ball 0 R) u :=
      (hψb r hr hrR).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hC₃) hu0)
    have h2 : scalarRms volume (ball 0 r) ψt ≤
        2 * (1 + C₂) * C27 * (1 + C₃) * (r / R) ^ (k + 1) * scalarRms volume (ball 0 R) u := by
      have hq0 := scalarRms_nonneg (ball (0 : Vec d) R) q
      have hp0 := scalarRms_nonneg (ball (0 : Vec d) R) p
      have hψ0 := scalarRms_nonneg (ball (0 : Vec d) R) ψ
      calc scalarRms volume (ball 0 r) ψt ≤ (1 + C₂) * scalarRms volume (ball 0 r) q := hψtr r hr
        _ = (1 + C₂) * ((r / R) ^ (k + 1) * scalarRms volume (ball 0 R) q) := by rw [hqr r hr0]
        _ ≤ (1 + C₂) * ((r / R) ^ (k + 1) * (C27 * (2 * ((1 + C₃) *
              scalarRms volume (ball 0 R) u)))) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hxk) (by linarith)
            exact hqR.trans (mul_le_mul_of_nonneg_left (hpR.trans
              (mul_le_mul_of_nonneg_left hψR (by norm_num))) hC27)
        _ = _ := by ring
    have h3 : scalarRms volume (ball 0 r) (fun x => u x - (ψ x - ψt x)) ≤
        scalarRms volume (ball 0 r) (fun x => u x - ψ x) + scalarRms volume (ball 0 r) ψt := by
      calc _ = scalarRms volume (ball 0 r) (fun x => (u x - ψ x) + ψt x) := by
            congr 1
            funext x
            ring
        _ ≤ _ := scalarRms_add_le (f := fun x => u x - ψ x) (g := ψt)
            ((hu.1.mono_measure (Measure.restrict_mono (ball_zero_subset_ball_zero hrR) le_rfl)).sub
              (hmemψ r hr0)) (hmemψt r hr0)
    calc _ ≤ _ := h3
      _ ≤ C₃ * (r / R) ^ (k + 1) * scalarRms volume (ball 0 R) u +
          2 * (1 + C₂) * C27 * (1 + C₃) * (r / R) ^ (k + 1) * scalarRms volume (ball 0 R) u :=
          add_le_add h1 h2
      _ = _ := by ring

/-- **Theorem 3.8 `(iii)₁`**, for `d ≥ 2`, `Λ > 1` and `s ∈ (0, d)`: there is `C` such that, for every
law satisfying the assumptions, a random variable `X ≥ 1` with `X ≤ O_s(C)` satisfies, for almost
every coefficient field: for every `R ≥ X` and every solution `u` in `B_R` there is `φ ∈ A_1` with
`‖u - φ‖_{L̲²(B_r)} ≤ C (r/R)² ‖u‖_{L̲²(B_R)}` for every `r ∈ [X, R]`. -/
theorem theorem_3_8_iii_one (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) {s : ℝ} (hs : 0 < s)
    (hsd : s < d) :
    ∃ C CX : ℝ, 0 ≤ C ∧ 0 < CX ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∃ X : CoefficientField d Λ → ℝ, OsBound P X s CX ∧ (∀ a, 1 ≤ X a) ∧ ∀ᵐ a ∂P,
        ∀ R : ℝ, X a ≤ R → ∀ u, IsSolutionBall a R u → ∃ φ ∈ solutionGrowthSpace a 1,
          ∀ r : ℝ, X a ≤ r → r ≤ R → scalarRms volume (ball 0 r) (fun x => u x - φ x) ≤
            C * (r / R) ^ 2 * scalarRms volume (ball 0 R) u := by
  obtain ⟨δ₁, hδ₁0, -, C₁, CX₁, hC₁, hCX₁, hi2⟩ := theorem_3_8_i_two hd hΛ hs hsd
  obtain ⟨δ₂, hδ₂0, -, C₂, CX₂, hC₂, hCX₂, hii2⟩ := theorem_3_8_ii_two hd hΛ hs hsd
  obtain ⟨δ₃, -, hδ₃2, C₃, CX₃, hC₃, hCX₃, hiii2⟩ := theorem_3_8_iii_prime_two hd hΛ hs hsd
  obtain ⟨C27, hC27, h27⟩ := scalarRms_homogeneousComponents_zero (d := d) 2
  have h27' : ∀ Q : MvPolynomial (Fin d) ℝ, Q.totalDegree ≤ 1 + 1 → ∀ r : ℝ, 0 < r →
      scalarRms volume (ball 0 r)
          (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent (1 + 1) Q)) ≤
        C27 * scalarRms volume (ball 0 r) (fun x => MvPolynomial.eval x Q) := fun Q hQ r hr => by
    have h := (h27 Q hQ r hr).2
    have hs := Finset.single_le_sum (f := fun m => scalarRms volume (ball 0 r)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q)))
      (fun i _ => scalarRms_nonneg _ _) (by simp : 1 + 1 ∈ Finset.range (2 + 1))
    exact hs.trans h
  obtain ⟨H, hH1, hHs⟩ := exists_scale_rpow_le C₁ (by norm_num : (0 : ℝ) < 1 / 2) hδ₁0
  refine ⟨C₃ + 2 * (1 + C₂) * C27 * (1 + C₃),
    (2 : ℝ) ^ s⁻¹ * max ((2 : ℝ) ^ s⁻¹ * max ((2 : ℝ) ^ s⁻¹ * max CX₁ CX₂) CX₃)
      (H / Real.log 2 ^ s⁻¹), by positivity, by positivity, fun P hP => ?_⟩
  have : IsProbabilityMeasure P := hP.1
  obtain ⟨X₁, hX₁os, hX₁1, hX₁ae⟩ := hi2 P hP
  obtain ⟨X₂, hX₂os, hX₂1, hX₂ae⟩ := hii2 P hP
  obtain ⟨X₃, hX₃os, hX₃1, hX₃ae⟩ := hiii2 P hP
  have hHos : OsBound P (fun _ => H) s (H / Real.log 2 ^ s⁻¹) :=
    osBound_of_le_const measurable_const hs (by linarith) (Eventually.of_forall fun _ => le_rfl)
  refine ⟨fun a => max (max (max (X₁ a) (X₂ a)) (X₃ a)) H,
    osBound_max (osBound_max (osBound_max hX₁os hX₂os) hX₃os) hHos,
    fun a => le_max_of_le_right hH1, ?_⟩
  filter_upwards [hX₁ae, hX₂ae, hX₃ae] with a ha1 ha2 ha3
  intro R hR u hu
  obtain ⟨X, hXdef⟩ : ∃ X, X = max (max (max (X₁ a) (X₂ a)) (X₃ a)) H := ⟨_, rfl⟩
  rw [← hXdef] at hR ⊢
  have hX₁r : X₁ a ≤ X := by rw [hXdef]; exact le_max_of_le_left (le_max_of_le_left (le_max_left _ _))
  have hX₂r : X₂ a ≤ X := by
    rw [hXdef]; exact le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
  have hX₃r : X₃ a ≤ X := by rw [hXdef]; exact le_max_of_le_left (le_max_right _ _)
  have hHr : H ≤ X := by rw [hXdef]; exact le_max_right _ _
  have hX1 : 1 ≤ X := hH1.trans hHr
  have h := implication_349 (k := 1) (A := homogenizedMatrix P) (δ₃ := δ₃) hX1 hC₁ hC₂ hC₃ hC27
    hδ₁0 hδ₂0
    (by linarith) (hHs X hHr) h27'
    (fun R' hR' w hw => by
      obtain ⟨ψ, hψ, hb⟩ := ha3 R' (hX₃r.trans hR') w hw
      refine ⟨ψ, hψ, fun r hr hrR => ?_⟩
      have e : ((1 + 1 : ℕ) : ℝ) + 1 - δ₃ / 2 = 3 - δ₃ / 2 := by push_cast; ring
      rw [e]
      exact hb r (hX₃r.trans hr) hrR)
    (fun ψ hψ => by
      obtain ⟨p, hp, hb⟩ := ha1 ψ hψ
      exact ⟨p, hp, fun r hr => hb r (hX₁r.trans hr)⟩)
    (fun q hq => by
      obtain ⟨ψ, hψ, hb⟩ := ha2 q hq
      exact ⟨ψ, hψ, fun r hr => hb r (hX₂r.trans hr)⟩)
    hR hu
  exact h

end QSH
