import QuantitativeStochasticHomogenization.Ch03.Sec03.Theorem38IOne
import QuantitativeStochasticHomogenization.Ch03.Sec03.Theorem38IIIPrimeOne

/-!
# Statement `(ii)₂` of Theorem 3.8

Armstrong–Kuusi–Mourrat, Theorem 3.8, statement `(ii)_k` for `k = 2`, through (3.46): `(i)₁`
(`theorem_3_8_i_one`), `(iii')₁` (`theorem_3_8_iii_prime_one_le`) and (3.52) give, above a random
scale `X ≤ O_s(C)` and for almost every coefficient field, for every `p ∈ Ā_2` some `u ∈ A_2` with
`‖u - p‖_{L̲²(B_R)} ≤ C R^{-δ} ‖p‖_{L̲²(B_R)}` for every `R ≥ X` (`theorem_3_8_ii_two`). The part of
degree two of `p` is handled by (3.46) (`implication_346_homogeneous`), the part of degree at most one
by `(ii)₁`.
-/

open MeasureTheory Filter Set Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- **Theorem 3.8 `(ii)₂`**, for `d ≥ 2`, `Λ > 1` and `s ∈ (0, d)`: there are `δ ∈ (0, ½]` and `C`
such that, for every law satisfying the assumptions, a random variable `X ≥ 1` with `X ≤ O_s(C)`
satisfies, for almost every coefficient field: for every `p ∈ Ā_2` there is `u ∈ A_2` with
`‖u - p‖_{L̲²(B_R)} ≤ C R^{-δ} ‖p‖_{L̲²(B_R)}` for every `R ≥ X`. -/
theorem theorem_3_8_ii_two (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) {s : ℝ} (hs : 0 < s)
    (hsd : s < d) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∃ C CX : ℝ, 0 ≤ C ∧ 0 < CX ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∃ X : CoefficientField d Λ → ℝ, OsBound P X s CX ∧ (∀ a, 1 ≤ X a) ∧ ∀ᵐ a ∂P,
        ∀ p ∈ harmonicPolys (homogenizedMatrix P) 2, ∃ u ∈ solutionGrowthSpace a 2,
          ∀ R : ℝ, X a ≤ R → scalarRms volume (ball 0 R) (fun x => u x - p x) ≤
            C * R ^ (-δ) * scalarRms volume (ball 0 R) p := by
  obtain ⟨δ₁, hδ₁0, hδ₁2, C₁, CX₁, hC₁, hCX₁, hi1⟩ := theorem_3_8_i_one hd hΛ hs hsd
  obtain ⟨δ₂, hδ₂0, -, C₂, CX₂, hC₂, hCX₂, hii1⟩ := theorem_3_8_ii_one hd hΛ hs hsd
  obtain ⟨δ₃, hδ₃0, -, hiii⟩ := theorem_3_8_iii_prime_one_le hd hΛ hs hsd
  obtain ⟨γ, hγ, C52, CX52, hCX52, hC52, h352⟩ := equation_3_52 hd hΛ hs hsd
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min (min δ₁ δ₂) (min δ₃ γ) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; exact lt_min (lt_min hδ₁0 hδ₂0) (lt_min hδ₃0 hγ)
  have hδ1 : δ ≤ δ₁ := by rw [hδdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ δ₂ := by rw [hδdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : δ ≤ δ₃ := by rw [hδdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hδγ : δ ≤ γ := by rw [hδdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hδh : δ ≤ 1 / 2 := hδ1.trans hδ₁2
  obtain ⟨C₃, CX₃, hC₃, hCX₃, hiii3⟩ := hiii δ hδ0 hδ3
  obtain ⟨K, hK, h346⟩ := implication_346_homogeneous (d := d) (Λ := Λ) (k := 2) (by norm_num)
    hδ0 (by linarith) (hC52 2) hC₃
  obtain ⟨H, hH1, hHs⟩ := exists_scale_rpow_le C₁ (by norm_num : (0 : ℝ) < 1 / 2) hδ0
  obtain ⟨C27, hC27, h27⟩ := scalarRms_homogeneousComponents_zero (d := d) 2
  refine ⟨δ, hδ0, hδh, Real.sqrt (2 ^ d) * K * 4 * C27 + C₂ * C27,
    (2 : ℝ) ^ s⁻¹ * max ((2 : ℝ) ^ s⁻¹ * max ((2 : ℝ) ^ s⁻¹ * max CX₁ CX₂)
      ((2 : ℝ) ^ s⁻¹ * max CX₃ CX52)) (H / Real.log 2 ^ s⁻¹), by positivity, by positivity,
    fun P hP => ?_⟩
  have : IsProbabilityMeasure P := hP.1
  obtain ⟨X₁, hX₁os, hX₁1, hX₁ae⟩ := hi1 P hP
  obtain ⟨X₂, hX₂os, hX₂1, hX₂ae⟩ := hii1 P hP
  obtain ⟨X₃, hX₃os, hX₃1, hX₃ae⟩ := hiii3 P hP
  obtain ⟨X₅, hX₅os, hX₅1, hX₅ae⟩ := h352 P hP
  have hHos : OsBound P (fun _ => H) s (H / Real.log 2 ^ s⁻¹) :=
    osBound_of_le_const measurable_const hs (by linarith) (Eventually.of_forall fun _ => le_rfl)
  refine ⟨fun a => max (max (max (X₁ a) (X₂ a)) (max (X₃ a) (X₅ a))) H,
    osBound_max (osBound_max (osBound_max hX₁os hX₂os) (osBound_max hX₃os hX₅os)) hHos,
    fun a => le_max_of_le_right hH1, ?_⟩
  filter_upwards [hX₁ae, hX₂ae, hX₃ae, hX₅ae] with a ha1 ha2 ha3 ha5
  intro p hp
  obtain ⟨r₀, hr₀def⟩ : ∃ r₀, r₀ = max (max (max (X₁ a) (X₂ a)) (max (X₃ a) (X₅ a))) H :=
    ⟨_, rfl⟩
  have hX₁r : X₁ a ≤ r₀ := by
    rw [hr₀def]; exact le_max_of_le_left (le_max_of_le_left (le_max_left _ _))
  have hX₂r : X₂ a ≤ r₀ := by
    rw [hr₀def]; exact le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
  have hX₃r : X₃ a ≤ r₀ := by
    rw [hr₀def]; exact le_max_of_le_left (le_max_of_le_right (le_max_left _ _))
  have hX₅r : X₅ a ≤ r₀ := by
    rw [hr₀def]; exact le_max_of_le_left (le_max_of_le_right (le_max_right _ _))
  have hHr : H ≤ r₀ := by rw [hr₀def]; exact le_max_right _ _
  have hr₀1 : 1 ≤ r₀ := hH1.trans hHr
  have hr₀ : 0 < r₀ := by linarith
  obtain ⟨⟨Q, hQ, hQe⟩, hph⟩ := hp
  -- the homogeneous parts of `p`
  have hqA := homogeneousComponent_mem_harmonicPolys ⟨⟨Q, hQ, hQe⟩, hph⟩ hQ hQe 2
  have hℓA := homogeneousComponent_mem_harmonicPolys ⟨⟨Q, hQ, hQe⟩, hph⟩ hQ hQe 1
  have hq : ∀ t : ℝ, 0 < t → ∀ x, MvPolynomial.eval (t • x) (MvPolynomial.homogeneousComponent 2 Q) =
      t ^ 2 * MvPolynomial.eval x (MvPolynomial.homogeneousComponent 2 Q) := fun t _ x =>
    PDE.eval_smul_of_isHomogeneous (MvPolynomial.homogeneousComponent_isHomogeneous 2 Q) t x
  have hc0 : ∀ x, MvPolynomial.eval x (MvPolynomial.homogeneousComponent 0 Q) = Q.coeff 0 :=
    fun x => by rw [MvPolynomial.homogeneousComponent_zero, MvPolynomial.eval_C]
  have hpdec : ∀ x, p x = (Q.coeff 0 + MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 Q)) +
      MvPolynomial.eval x (MvPolynomial.homogeneousComponent 2 Q) := fun x => by
    rw [hQe x, eval_eq_sum_homogeneousComponent hQ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one, hc0]
  -- the part of degree two, by (3.46)
  obtain ⟨uq, huq, hbq⟩ := h346 hΛ.le a (homogenizedMatrix P)
    (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 2 Q)) hqA hq r₀ C₁ hr₀ hC₁
    (hHs r₀ hHr)
    (fun r hr => by
      obtain ⟨u, hu, hb⟩ := ha5 2 r (hX₅r.trans hr) _ hqA
      refine ⟨u, hu, hb.trans ?_⟩
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (hC52 2))
        (scalarRms_nonneg _ _)
      exact Real.rpow_le_rpow_of_exponent_le (hr₀1.trans hr) (by linarith))
    (fun R hR w hw => by
      obtain ⟨φ, hφ, hb⟩ := ha3 R (hX₃r.trans hR) w hw
      refine ⟨φ, hφ, fun r hr hrR => ?_⟩
      have h := hb r (hX₃r.trans hr) hrR
      simpa only [Nat.cast_ofNat] using h)
    (fun φ hφ => by
      obtain ⟨p', hp', hb⟩ := ha1 φ hφ
      refine ⟨p', hp', fun R hR => (hb R (hX₁r.trans hR)).trans ?_⟩
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC₁) (scalarRms_nonneg _ _)
      exact Real.rpow_le_rpow_of_exponent_le (hr₀1.trans hR) (by linarith))
  -- the part of degree at most one, by `(ii)₁`
  have hclA : (fun x => Q.coeff 0 + MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 Q)) ∈
      harmonicPolys (homogenizedMatrix P) 1 :=
    add_mem_harmonicPolys (const_mem_harmonicPolys _ 1 _) hℓA
  obtain ⟨v, hv, hbv⟩ := ha2 _ hclA
  refine ⟨fun x => uq x + v x,
    add_mem_solutionGrowthSpace huq (solutionGrowthSpace_mono (by norm_num) hv), fun R hR' => ?_⟩
  have hR : r₀ ≤ R := by rw [hr₀def]; exact hR'
  have hR0 : 0 < R := lt_of_lt_of_le hr₀ hR
  -- (3.27) for `p`
  obtain ⟨-, h27p⟩ := h27 Q hQ R hR0
  have hpfun : (fun x => MvPolynomial.eval x Q) = p := funext fun x => (hQe x).symm
  rw [hpfun, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at h27p
  have hc0fun : (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 0 Q)) =
      fun _ => Q.coeff 0 := funext hc0
  rw [hc0fun] at h27p
  have hn0 := scalarRms_nonneg (ball (0 : Vec d) R) (fun _ => Q.coeff 0)
  have hn1 := scalarRms_nonneg (ball (0 : Vec d) R)
    (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 Q))
  have hn2 := scalarRms_nonneg (ball (0 : Vec d) R)
    (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 2 Q))
  have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
    isFiniteMeasure_restrict.mpr (volume_ball_ne_top' 0 R)
  have hcl : scalarRms volume (ball 0 R)
      (fun x => Q.coeff 0 + MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 Q)) ≤
      C27 * scalarRms volume (ball 0 R) p :=
    (scalarRms_add_le (f := fun _ => Q.coeff 0)
      (g := fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 Q)) (memLp_const _)
      (memLp_eval_ball _ R)).trans (by linarith)
  have hq2 : scalarRms volume (ball 0 R)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 2 Q)) ≤
      C27 * scalarRms volume (ball 0 R) p := by linarith
  -- the part of degree two on `B_R`, from the dyadic radii
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
  have hmem : MemLp (fun x => uq x - MvPolynomial.eval x (MvPolynomial.homogeneousComponent 2 Q)) 2
      (volume.restrict (ball (0 : Vec d) (2 ^ j * r₀))) :=
    (huq.1 _ hρj).1.sub (hqA.2 _ hρj).1
  have h1 := scalarRms_ball_le hR0 hj1 hmem
  have hratio : Real.sqrt ((2 ^ j * r₀ / R) ^ d) ≤ Real.sqrt (2 ^ d) :=
    Real.sqrt_le_sqrt (pow_le_pow_left₀ (by positivity) (by rw [div_le_iff₀ hR0]; linarith) d)
  have hpow : (2 ^ j * r₀ : ℝ) ^ (-δ) ≤ R ^ (-δ) :=
    Real.rpow_le_rpow_of_nonpos hR0 hj1 (by linarith)
  have hhom : scalarRms volume (ball 0 (2 ^ j * r₀))
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 2 Q)) ≤
      4 * scalarRms volume (ball 0 R)
        (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 2 Q)) := by
    have ht : 0 < 2 ^ j * r₀ / R := by positivity
    have h := scalarRms_ball_homogeneous (q := fun x =>
      MvPolynomial.eval x (MvPolynomial.homogeneousComponent 2 Q)) hq (r := R) ht
    rw [div_mul_cancel₀ _ hR0.ne'] at h
    rw [h]
    have ht2 : 2 ^ j * r₀ / R ≤ 2 := by rw [div_le_iff₀ hR0]; linarith
    have ht4 : (2 ^ j * r₀ / R) ^ 2 ≤ 4 := by nlinarith
    exact mul_le_mul_of_nonneg_right ht4 (scalarRms_nonneg _ _)
  have hs := Real.sqrt_nonneg ((2 : ℝ) ^ d)
  have hRδ : 0 ≤ R ^ (-δ) := Real.rpow_nonneg hR0.le _
  have hbq' : scalarRms volume (ball 0 R)
      (fun x => uq x - MvPolynomial.eval x (MvPolynomial.homogeneousComponent 2 Q)) ≤
      Real.sqrt (2 ^ d) * K * 4 * C27 * R ^ (-δ) * scalarRms volume (ball 0 R) p :=
    calc _ ≤ Real.sqrt (2 ^ d) * (K * (2 ^ j * r₀) ^ (-δ) * scalarRms volume (ball 0 (2 ^ j * r₀))
            (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent 2 Q))) :=
          h1.trans (mul_le_mul hratio (hbq j) (scalarRms_nonneg _ _) hs)
      _ ≤ Real.sqrt (2 ^ d) * (K * R ^ (-δ) * (4 * (C27 * scalarRms volume (ball 0 R) p))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left hpow hK)
            (hhom.trans (mul_le_mul_of_nonneg_left hq2 (by norm_num))) (scalarRms_nonneg _ _)
            (mul_nonneg hK hRδ)) hs
      _ = _ := by ring
  -- the part of degree at most one
  have hbv' : scalarRms volume (ball 0 R) (fun x => v x -
      (Q.coeff 0 + MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 Q))) ≤
      C₂ * C27 * R ^ (-δ) * scalarRms volume (ball 0 R) p := by
    have hpow2 : R ^ (-δ₂) ≤ R ^ (-δ) :=
      Real.rpow_le_rpow_of_exponent_le (hr₀1.trans hR) (by linarith)
    calc _ ≤ C₂ * R ^ (-δ₂) * scalarRms volume (ball 0 R)
          (fun x => Q.coeff 0 + MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 Q)) :=
          hbv R (hX₂r.trans hR)
      _ ≤ C₂ * R ^ (-δ) * (C27 * scalarRms volume (ball 0 R) p) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow2 hC₂) hcl (scalarRms_nonneg _ _)
            (mul_nonneg hC₂ hRδ)
      _ = _ := by ring
  have e : (fun x => (uq x + v x) - p x) = fun x =>
      (uq x - MvPolynomial.eval x (MvPolynomial.homogeneousComponent 2 Q)) +
        (v x - (Q.coeff 0 + MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 Q))) := by
    funext x
    rw [hpdec x]
    ring
  rw [e]
  have hadd := scalarRms_add_le
    (f := fun x => uq x - MvPolynomial.eval x (MvPolynomial.homogeneousComponent 2 Q))
    (g := fun x => v x - (Q.coeff 0 + MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 Q)))
    ((huq.1 _ hR0).1.sub (hqA.2 _ hR0).1) ((hv.1 _ hR0).1.sub (hclA.2 _ hR0).1)
  calc _ ≤ _ := hadd
    _ ≤ Real.sqrt (2 ^ d) * K * 4 * C27 * R ^ (-δ) * scalarRms volume (ball 0 R) p +
        C₂ * C27 * R ^ (-δ) * scalarRms volume (ball 0 R) p := add_le_add hbq' hbv'
    _ = _ := by ring

end QSH
