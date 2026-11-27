import QuantitativeStochasticHomogenization.Ch03.Sec03.Theorem38IIIOne

/-!
# Theorem 3.8 for every `k`

Armstrong–Kuusi–Mourrat, Theorem 3.8, statements `(i)_k`, `(ii)_k` and `(iii)_k` for every `k`, by
induction over `k` (`theorem_3_8`): `(i)₀`, `(ii)₀` and `(iii')₀` from `theorem_3_8_zero`; for every
`k`, (3.46) with (3.52) gives `(ii)_{k+1}` from `(i)_k`, `(ii)_k` and `(iii')_k`
(`statementII_succ`), (3.48) gives `(iii')_{k+1}` (`iii_prime_of_ii`), (3.47) gives `(i)_{k+1}`
(`statementI_succ`), and (3.49) gives `(iii)_k` from the statements for `k + 1` (`statementIII_of`).
The exponent, the constants and the random scale depend on `k`.
-/

open MeasureTheory Filter Set Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- Statement `(i)_k` of Theorem 3.8 above a random scale. -/
def StatementI (d : ℕ) (Λ s : ℝ) (k : ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∃ C CX : ℝ, 0 ≤ C ∧ 0 < CX ∧
    ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
    ∃ X : CoefficientField d Λ → ℝ, OsBound P X s CX ∧ (∀ a, 1 ≤ X a) ∧ ∀ᵐ a ∂P,
      ∀ u ∈ solutionGrowthSpace a k, ∃ p ∈ harmonicPolys (homogenizedMatrix P) k,
        ∀ R : ℝ, X a ≤ R → scalarRms volume (ball 0 R) (fun x => u x - p x) ≤
          C * R ^ (-δ) * scalarRms volume (ball 0 R) p

/-- Statement `(ii)_k` of Theorem 3.8 above a random scale. -/
def StatementII (d : ℕ) (Λ s : ℝ) (k : ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∃ C CX : ℝ, 0 ≤ C ∧ 0 < CX ∧
    ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
    ∃ X : CoefficientField d Λ → ℝ, OsBound P X s CX ∧ (∀ a, 1 ≤ X a) ∧ ∀ᵐ a ∂P,
      ∀ p ∈ harmonicPolys (homogenizedMatrix P) k, ∃ u ∈ solutionGrowthSpace a k,
        ∀ R : ℝ, X a ≤ R → scalarRms volume (ball 0 R) (fun x => u x - p x) ≤
          C * R ^ (-δ) * scalarRms volume (ball 0 R) p

/-- The estimate `(iii')_k` of the proof of Theorem 3.8, for every exponent below a threshold. -/
def StatementIIIPrime (d : ℕ) (Λ s : ℝ) (k : ℕ) : Prop :=
  ∃ δ₁ : ℝ, 0 < δ₁ ∧ δ₁ ≤ 1 / 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ → ∃ C CX : ℝ, 0 ≤ C ∧ 0 < CX ∧
    ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
    ∃ X : CoefficientField d Λ → ℝ, OsBound P X s CX ∧ (∀ a, 1 ≤ X a) ∧ ∀ᵐ a ∂P,
      ∀ R : ℝ, X a ≤ R → ∀ u, IsSolutionBall a R u → ∃ φ ∈ solutionGrowthSpace a k,
        ∀ r : ℝ, X a ≤ r → r ≤ R → scalarRms volume (ball 0 r) (fun x => u x - φ x) ≤
          C * (r / R) ^ ((k : ℝ) + 1 - δ / 2) * scalarRms volume (ball 0 R) u

/-- Statement `(iii)_k` of Theorem 3.8 above a random scale, (3.41). -/
def StatementIII (d : ℕ) (Λ s : ℝ) (k : ℕ) : Prop :=
  ∃ C CX : ℝ, 0 ≤ C ∧ 0 < CX ∧
    ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
    ∃ X : CoefficientField d Λ → ℝ, OsBound P X s CX ∧ (∀ a, 1 ≤ X a) ∧ ∀ᵐ a ∂P,
      ∀ R : ℝ, X a ≤ R → ∀ u, IsSolutionBall a R u → ∃ φ ∈ solutionGrowthSpace a k,
        ∀ r : ℝ, X a ≤ r → r ≤ R → scalarRms volume (ball 0 r) (fun x => u x - φ x) ≤
          C * (r / R) ^ (k + 1) * scalarRms volume (ball 0 R) u

/-- The case `k = 0`, from `theorem_3_8_zero`. -/
theorem statements_zero (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) {s : ℝ} (hs : 0 < s) (hsd : s < d) :
    StatementI d Λ s 0 ∧ StatementII d Λ s 0 ∧ StatementIIIPrime d Λ s 0 := by
  obtain ⟨C₀, hC₀, h380⟩ := theorem_3_8_zero hd hΛ hs hsd
  have hzero : ∀ (U : Set (Vec d)) (f g : Vec d → ℝ), (∀ᵐ x ∂(volume : Measure (Vec d)), f x = g x) →
      scalarRms volume U (fun x => f x - g x) = 0 := fun U f g hfg => by
    have h0 : scalarRms volume U (fun x => f x - g x) = scalarRms volume U (fun _ => (0 : ℝ)) :=
      scalarRms_congr_ae (ae_restrict_of_ae (by filter_upwards [hfg] with x hx; rw [hx, sub_self]))
    rw [h0]
    unfold scalarRms
    simp
  refine ⟨⟨1 / 2, by norm_num, le_rfl, 0, C₀, le_rfl, hC₀, fun P hP => ?_⟩,
    ⟨1 / 2, by norm_num, le_rfl, 0, C₀, le_rfl, hC₀, fun P hP => ?_⟩,
    ⟨1 / 2, by norm_num, le_rfl, fun δ hδ0 hδ => ⟨C₀, C₀, hC₀.le, hC₀, fun P hP => ?_⟩⟩⟩
  · obtain ⟨X, hXos, hX1, hXae⟩ := h380 P hP
    refine ⟨X, hXos, hX1, ?_⟩
    filter_upwards [hXae] with a ha
    intro u hu
    obtain ⟨p, hp, hup⟩ := ha.1 u hu
    refine ⟨p, hp, fun R _ => ?_⟩
    rw [hzero _ _ _ hup, zero_mul, zero_mul]
  · obtain ⟨X, hXos, hX1, hXae⟩ := h380 P hP
    refine ⟨X, hXos, hX1, ?_⟩
    filter_upwards [hXae] with a ha
    intro p hp
    refine ⟨p, ha.2.1 hp, fun R _ => ?_⟩
    rw [hzero _ _ _ (Eventually.of_forall fun _ => rfl), zero_mul, zero_mul]
  · obtain ⟨X, hXos, hX1, hXae⟩ := h380 P hP
    refine ⟨X, hXos, hX1, ?_⟩
    filter_upwards [hXae] with a ha
    intro R hR u hu
    obtain ⟨hL2, g, hg, hgrad, hdiv⟩ := hu
    obtain ⟨φ, hφ, hb⟩ := ha.2.2 R hR u g hL2 hg hgrad hdiv
    refine ⟨φ, hφ, fun r hr hrR => (hb r hr hrR).trans ?_⟩
    have hr0 : 0 < r := lt_of_lt_of_le (lt_of_lt_of_le one_pos (hX1 a)) hr
    have hR0 : 0 < R := lt_of_lt_of_le hr0 hrR
    have hx0 : 0 < r / R := div_pos hr0 hR0
    have hx1 : r / R ≤ 1 := (div_le_one hR0).2 hrR
    have hpow : r / R ≤ (r / R) ^ (((0 : ℕ) : ℝ) + 1 - δ / 2) := by
      conv_lhs => rw [← Real.rpow_one (r / R)]
      exact Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by push_cast; linarith)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC₀.le) (scalarRms_nonneg _ _)

/-- **(3.46) above a random scale, for every `k`**: `(i)_k`, `(ii)_k` and `(iii')_k` give
`(ii)_{k+1}`. -/
theorem statementII_succ (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) {s : ℝ} (hs : 0 < s) (hsd : s < d)
    {k : ℕ} (hI : StatementI d Λ s k) (hII : StatementII d Λ s k)
    (hIII : StatementIIIPrime d Λ s k) : StatementII d Λ s (k + 1) := by
  obtain ⟨δ₁, hδ₁0, hδ₁2, C₁, CX₁, hC₁, hCX₁, hi1⟩ := hI
  obtain ⟨δ₂, hδ₂0, -, C₂, CX₂, hC₂, hCX₂, hii1⟩ := hII
  obtain ⟨δ₃, hδ₃0, -, hiii⟩ := hIII
  obtain ⟨γ, hγ, C52, CX52, hCX52, hC52, h352⟩ := equation_3_52 hd hΛ hs hsd
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min (min δ₁ δ₂) (min δ₃ γ) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; exact lt_min (lt_min hδ₁0 hδ₂0) (lt_min hδ₃0 hγ)
  have hδ1 : δ ≤ δ₁ := by rw [hδdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ δ₂ := by rw [hδdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : δ ≤ δ₃ := by rw [hδdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hδγ : δ ≤ γ := by rw [hδdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hδh : δ ≤ 1 / 2 := hδ1.trans hδ₁2
  obtain ⟨C₃, CX₃, hC₃, hCX₃, hiii3⟩ := hiii δ hδ0 hδ3
  obtain ⟨K, hK, h346⟩ := implication_346_homogeneous (d := d) (Λ := Λ) (k := k + 1) (by omega)
    hδ0 (by linarith) (hC52 (k + 1)) hC₃
  obtain ⟨H, hH1, hHs⟩ := exists_scale_rpow_le C₁ (by norm_num : (0 : ℝ) < 1 / 2) hδ0
  obtain ⟨C27, hC27, h27⟩ := scalarRms_homogeneousComponents_zero (d := d) (k + 1)
  refine ⟨δ, hδ0, hδh, Real.sqrt (2 ^ d) * K * 2 ^ (k + 1) * C27 + C₂ * (1 + C27),
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
  obtain ⟨⟨Q, hQ, hQe⟩, hph⟩ := id hp
  -- the parts of `p`
  have hqA := homogeneousComponent_mem_harmonicPolys hp hQ hQe (k + 1)
  have hq : ∀ t : ℝ, 0 < t → ∀ x,
      MvPolynomial.eval (t • x) (MvPolynomial.homogeneousComponent (k + 1) Q) =
        t ^ (k + 1) * MvPolynomial.eval x (MvPolynomial.homogeneousComponent (k + 1) Q) :=
    fun t _ x => PDE.eval_smul_of_isHomogeneous
      (MvPolynomial.homogeneousComponent_isHomogeneous (k + 1) Q) t x
  have hLA : (fun x => ∑ m ∈ Finset.range (k + 1),
      MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q)) ∈
      harmonicPolys (homogenizedMatrix P) k :=
    finset_sum_mem_harmonicPolys _ fun m hm => harmonicPolys_mono
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)) (homogeneousComponent_mem_harmonicPolys hp hQ hQe m)
  have hpdec : ∀ x, p x = (∑ m ∈ Finset.range (k + 1),
      MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q)) +
      MvPolynomial.eval x (MvPolynomial.homogeneousComponent (k + 1) Q) := fun x => by
    rw [hQe x, eval_eq_sum_homogeneousComponent hQ, Finset.sum_range_succ]
  -- the part of degree `k + 1`, by (3.46)
  obtain ⟨uq, huq, hbq⟩ := h346 hΛ.le a (homogenizedMatrix P)
    (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent (k + 1) Q)) hqA hq r₀ C₁ hr₀
    hC₁ (hHs r₀ hHr)
    (fun r hr => by
      obtain ⟨u, hu, hb⟩ := ha5 (k + 1) r (hX₅r.trans hr) _ hqA
      refine ⟨u, hu, hb.trans ?_⟩
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (hC52 (k + 1)))
        (scalarRms_nonneg _ _)
      exact Real.rpow_le_rpow_of_exponent_le (hr₀1.trans hr) (by linarith))
    (fun R hR w hw => by
      obtain ⟨φ, hφ, hb⟩ := ha3 R (hX₃r.trans hR) w hw
      refine ⟨φ, hφ, fun r hr hrR => ?_⟩
      have e : ((k + 1 : ℕ) : ℝ) - δ / 2 = (k : ℝ) + 1 - δ / 2 := by push_cast; ring
      rw [e]
      exact hb r (hX₃r.trans hr) hrR)
    (fun φ hφ => by
      obtain ⟨p', hp', hb⟩ := ha1 φ hφ
      refine ⟨p', hp', fun R hR => (hb R (hX₁r.trans hR)).trans ?_⟩
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC₁) (scalarRms_nonneg _ _)
      exact Real.rpow_le_rpow_of_exponent_le (hr₀1.trans hR) (by linarith))
  -- the part of degree at most `k`, by `(ii)_k`
  obtain ⟨v, hv, hbv⟩ := ha2 _ hLA
  refine ⟨fun x => uq x + v x,
    add_mem_solutionGrowthSpace huq (solutionGrowthSpace_mono (by omega) hv), fun R hR' => ?_⟩
  have hR : r₀ ≤ R := by rw [hr₀def]; exact hR'
  have hR0 : 0 < R := lt_of_lt_of_le hr₀ hR
  -- (3.27) for `p`
  have hmemp : MemLp p 2 (volume.restrict (ball (0 : Vec d) R)) := by
    rw [show p = fun x => MvPolynomial.eval x Q from funext hQe]; exact memLp_eval_ball _ R
  have hq2 : scalarRms volume (ball 0 R)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent (k + 1) Q)) ≤
      C27 * scalarRms volume (ball 0 R) p := by
    have h := (h27 Q hQ R hR0).2
    have hs1 := Finset.single_le_sum (f := fun m => scalarRms volume (ball 0 R)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q)))
      (fun i _ => scalarRms_nonneg _ _) (by simp : k + 1 ∈ Finset.range (k + 1 + 1))
    rw [show (fun x => MvPolynomial.eval x Q) = p from funext fun x => (hQe x).symm] at h
    exact hs1.trans h
  have hcl : scalarRms volume (ball 0 R) (fun x => ∑ m ∈ Finset.range (k + 1),
      MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q)) ≤
      (1 + C27) * scalarRms volume (ball 0 R) p := by
    have h' := scalarRms_le_add_of_sub (f := p)
      (g := fun x => ∑ m ∈ Finset.range (k + 1),
        MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q)) hmemp (hLA.2 R hR0).1
    have e2 : (fun x => p x - ∑ m ∈ Finset.range (k + 1),
        MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q)) =
        fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent (k + 1) Q) :=
      funext fun x => by rw [hpdec x]; ring
    rw [e2] at h'
    linarith
  -- the part of degree `k + 1` on `B_R`, from the dyadic radii
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
  have hmem : MemLp (fun x => uq x -
      MvPolynomial.eval x (MvPolynomial.homogeneousComponent (k + 1) Q)) 2
      (volume.restrict (ball (0 : Vec d) (2 ^ j * r₀))) :=
    (huq.1 _ hρj).1.sub (hqA.2 _ hρj).1
  have h1 := scalarRms_ball_le hR0 hj1 hmem
  have hratio : Real.sqrt ((2 ^ j * r₀ / R) ^ d) ≤ Real.sqrt (2 ^ d) :=
    Real.sqrt_le_sqrt (pow_le_pow_left₀ (by positivity) (by rw [div_le_iff₀ hR0]; linarith) d)
  have hpow : (2 ^ j * r₀ : ℝ) ^ (-δ) ≤ R ^ (-δ) :=
    Real.rpow_le_rpow_of_nonpos hR0 hj1 (by linarith)
  have hhom : scalarRms volume (ball 0 (2 ^ j * r₀))
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent (k + 1) Q)) ≤
      2 ^ (k + 1) * scalarRms volume (ball 0 R)
        (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent (k + 1) Q)) := by
    have ht : 0 < 2 ^ j * r₀ / R := by positivity
    have h := scalarRms_ball_homogeneous (q := fun x =>
      MvPolynomial.eval x (MvPolynomial.homogeneousComponent (k + 1) Q)) hq (r := R) ht
    rw [div_mul_cancel₀ _ hR0.ne'] at h
    rw [h]
    have ht2 : 2 ^ j * r₀ / R ≤ 2 := by rw [div_le_iff₀ hR0]; linarith
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht.le ht2 _) (scalarRms_nonneg _ _)
  have hs := Real.sqrt_nonneg ((2 : ℝ) ^ d)
  have hRδ : 0 ≤ R ^ (-δ) := Real.rpow_nonneg hR0.le _
  have hbq' : scalarRms volume (ball 0 R)
      (fun x => uq x - MvPolynomial.eval x (MvPolynomial.homogeneousComponent (k + 1) Q)) ≤
      Real.sqrt (2 ^ d) * K * 2 ^ (k + 1) * C27 * R ^ (-δ) * scalarRms volume (ball 0 R) p :=
    calc _ ≤ Real.sqrt (2 ^ d) * (K * (2 ^ j * r₀) ^ (-δ) * scalarRms volume (ball 0 (2 ^ j * r₀))
            (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent (k + 1) Q))) :=
          h1.trans (mul_le_mul hratio (hbq j) (scalarRms_nonneg _ _) hs)
      _ ≤ Real.sqrt (2 ^ d) * (K * R ^ (-δ) * (2 ^ (k + 1) *
            (C27 * scalarRms volume (ball 0 R) p))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left hpow hK)
            (hhom.trans (mul_le_mul_of_nonneg_left hq2 (by positivity))) (scalarRms_nonneg _ _)
            (mul_nonneg hK hRδ)) hs
      _ = _ := by ring
  -- the part of degree at most `k`
  have hbv' : scalarRms volume (ball 0 R) (fun x => v x - ∑ m ∈ Finset.range (k + 1),
      MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q)) ≤
      C₂ * (1 + C27) * R ^ (-δ) * scalarRms volume (ball 0 R) p := by
    have hpow2 : R ^ (-δ₂) ≤ R ^ (-δ) :=
      Real.rpow_le_rpow_of_exponent_le (hr₀1.trans hR) (by linarith)
    calc _ ≤ C₂ * R ^ (-δ₂) * scalarRms volume (ball 0 R) (fun x => ∑ m ∈ Finset.range (k + 1),
          MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q)) :=
          hbv R (hX₂r.trans hR)
      _ ≤ C₂ * R ^ (-δ) * ((1 + C27) * scalarRms volume (ball 0 R) p) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow2 hC₂) hcl (scalarRms_nonneg _ _)
            (mul_nonneg hC₂ hRδ)
      _ = _ := by ring
  have e : (fun x => (uq x + v x) - p x) = fun x =>
      (uq x - MvPolynomial.eval x (MvPolynomial.homogeneousComponent (k + 1) Q)) +
        (v x - ∑ m ∈ Finset.range (k + 1),
          MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q)) := by
    funext x
    rw [hpdec x]
    ring
  rw [e]
  have hadd := scalarRms_add_le
    (f := fun x => uq x - MvPolynomial.eval x (MvPolynomial.homogeneousComponent (k + 1) Q))
    (g := fun x => v x - ∑ m ∈ Finset.range (k + 1),
      MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q))
    ((huq.1 _ hR0).1.sub (hqA.2 _ hR0).1) ((hv.1 _ hR0).1.sub (hLA.2 _ hR0).1)
  calc _ ≤ _ := hadd
    _ ≤ Real.sqrt (2 ^ d) * K * 2 ^ (k + 1) * C27 * R ^ (-δ) * scalarRms volume (ball 0 R) p +
        C₂ * (1 + C27) * R ^ (-δ) * scalarRms volume (ball 0 R) p := add_le_add hbq' hbv'
    _ = _ := by ring

/-- **(3.47) above a random scale, for every `k`**: `(i)_k` and `(ii)_{k+1}` give `(i)_{k+1}`. -/
theorem statementI_succ (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) {s : ℝ} (hs : 0 < s) (hsd : s < d)
    {k : ℕ} (hI : StatementI d Λ s k) (hII : StatementII d Λ s (k + 1)) :
    StatementI d Λ s (k + 1) := by
  obtain ⟨δ₁, hδ₁0, hδ₁2, C₁, CX₁, hC₁, hCX₁, hi1⟩ := hI
  obtain ⟨δ₂, hδ₂0, -, C₂, CX₂, hC₂, hCX₂, hii2⟩ := hII
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
  obtain ⟨hθ0, hθ1, hC50⟩ := hθC (k + 1 + 1)
  obtain ⟨C27, hC27, h27⟩ := scalarRms_homogeneousComponents_zero (d := d) (k + 1)
  have h27' : ∀ Q : MvPolynomial (Fin d) ℝ, Q.totalDegree ≤ k + 1 → ∀ r : ℝ, 0 < r →
      scalarRms volume (ball 0 r)
          (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent (k + 1) Q)) ≤
        C27 * scalarRms volume (ball 0 r) (fun x => MvPolynomial.eval x Q) := fun Q hQ r hr => by
    have h := (h27 Q hQ r hr).2
    have hs1 := Finset.single_le_sum (f := fun m => scalarRms volume (ball 0 r)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q)))
      (fun i _ => scalarRms_nonneg _ _) (by simp : k + 1 ∈ Finset.range (k + 1 + 1))
    exact hs1.trans h
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
  obtain ⟨p, hp, hpb⟩ := implication_347 (k := k + 1) (n := n) (A := homogenizedMatrix P)
    (by omega) hθ0 (by linarith) hC50.le hn1 hδ (hX₅1 a) hX₅r
    (fun r hr v hv => ha5 (k + 1 + 1) r hr v hv) hC₁ hC₂ hδ₂0 h27'
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

/-- **(3.49) above a random scale, for every `k`**: `(i)_{k+1}`, `(ii)_{k+1}` and `(iii')_{k+1}`
give `(iii)_k`. -/
theorem statementIII_of {Λ : ℝ} {s : ℝ} (hs : 0 < s) {k : ℕ} (hI : StatementI d Λ s (k + 1)) (hII : StatementII d Λ s (k + 1))
    (hIII : StatementIIIPrime d Λ s (k + 1)) : StatementIII d Λ s k := by
  obtain ⟨δ₁, hδ₁0, -, C₁, CX₁, hC₁, hCX₁, hi2⟩ := hI
  obtain ⟨δ₂, hδ₂0, -, C₂, CX₂, hC₂, hCX₂, hii2⟩ := hII
  obtain ⟨δ₃, hδ₃0, hδ₃2, hiii⟩ := hIII
  obtain ⟨C₃, CX₃, hC₃, hCX₃, hiii2⟩ := hiii δ₃ hδ₃0 le_rfl
  obtain ⟨C27, hC27, h27⟩ := scalarRms_homogeneousComponents_zero (d := d) (k + 1)
  have h27' : ∀ Q : MvPolynomial (Fin d) ℝ, Q.totalDegree ≤ k + 1 → ∀ r : ℝ, 0 < r →
      scalarRms volume (ball 0 r)
          (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent (k + 1) Q)) ≤
        C27 * scalarRms volume (ball 0 r) (fun x => MvPolynomial.eval x Q) := fun Q hQ r hr => by
    have h := (h27 Q hQ r hr).2
    have hs1 := Finset.single_le_sum (f := fun m => scalarRms volume (ball 0 r)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q)))
      (fun i _ => scalarRms_nonneg _ _) (by simp : k + 1 ∈ Finset.range (k + 1 + 1))
    exact hs1.trans h
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
  have hX₁r : X₁ a ≤ X := by
    rw [hXdef]; exact le_max_of_le_left (le_max_of_le_left (le_max_left _ _))
  have hX₂r : X₂ a ≤ X := by
    rw [hXdef]; exact le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
  have hX₃r : X₃ a ≤ X := by rw [hXdef]; exact le_max_of_le_left (le_max_right _ _)
  have hHr : H ≤ X := by rw [hXdef]; exact le_max_right _ _
  have hX1 : 1 ≤ X := hH1.trans hHr
  exact implication_349 (k := k) (A := homogenizedMatrix P) (δ₃ := δ₃) hX1 hC₁ hC₂ hC₃ hC27
    hδ₁0 hδ₂0 (by linarith) (hHs X hHr) h27'
    (fun R' hR' w hw => by
      obtain ⟨ψ, hψ, hb⟩ := ha3 R' (hX₃r.trans hR') w hw
      exact ⟨ψ, hψ, fun r hr hrR => hb r (hX₃r.trans hr) hrR⟩)
    (fun ψ hψ => by
      obtain ⟨p, hp, hb⟩ := ha1 ψ hψ
      exact ⟨p, hp, fun r hr => hb r (hX₁r.trans hr)⟩)
    (fun q hq => by
      obtain ⟨ψ, hψ, hb⟩ := ha2 q hq
      exact ⟨ψ, hψ, fun r hr => hb r (hX₂r.trans hr)⟩)
    hR hu

/-- `(i)_k`, `(ii)_k` and `(iii')_k` for every `k`, by induction over `k`. -/
theorem statements_all (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) {s : ℝ} (hs : 0 < s) (hsd : s < d) :
    ∀ k : ℕ, StatementI d Λ s k ∧ StatementII d Λ s k ∧ StatementIIIPrime d Λ s k := by
  intro k
  induction k with
  | zero => exact statements_zero hd hΛ hs hsd
  | succ k ih =>
    obtain ⟨hI, hII, hIII⟩ := ih
    have hII' := statementII_succ hd hΛ hs hsd hI hII hIII
    exact ⟨statementI_succ hd hΛ hs hsd hI hII', hII', iii_prime_of_ii hd hΛ hs hsd (k + 1) hII'⟩

/-- **Theorem 3.8**, for `d ≥ 2`, `Λ > 1`, `s ∈ (0, d)` and every `k`: statements `(i)_k`, `(ii)_k`
and `(iii)_k` above a random scale `X ≤ O_s(C)` (depending on `k`), for almost every coefficient
field. -/
theorem theorem_3_8 (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) {s : ℝ} (hs : 0 < s) (hsd : s < d)
    (k : ℕ) : StatementI d Λ s k ∧ StatementII d Λ s k ∧ StatementIII d Λ s k := by
  obtain ⟨hI, hII, -⟩ := statements_all hd hΛ hs hsd k
  obtain ⟨hI', hII', hIII'⟩ := statements_all hd hΛ hs hsd (k + 1)
  exact ⟨hI, hII, statementIII_of hs hI' hII' hIII'⟩

end QSH
