import QuantitativeStochasticHomogenization.Ch03.Sec01.BallScaling
import QuantitativeStochasticHomogenization.Ch03.Sec02.Lemma34
import QuantitativeStochasticHomogenization.Ch03.Sec03.ExcessIteration
import QuantitativeStochasticHomogenization.Ch01.Sec05.ConvexMeyers
import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatKernelThirdDerivative

/-!
# The Meyers estimate (3.14) on half balls

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 3.1, (3.14) in the proof of Proposition 3.2: there are `δ(d, Λ) > 0` and `C(d, Λ)` such
that every weak solution `u ∈ H¹(B_R)` of `-∇·(a∇u) = 0` in `B_R` has
`‖∇u‖_{L̲^{2+δ}(B_{R/2})} ≤ C R⁻¹ ‖u - (u)_{B_R}‖_{L̲²(B_R)}` (`meyers_halfBall`).

The book refers to Theorem C.1, which bounds `‖∇u‖_{L̲^{2+δ}(B_{r/2})}` by `‖∇u‖_{L̲²(B_r)}`; with the
Caccioppoli inequality (Lemma C.2) this gives (3.14) on a smaller ball. Here `B_{R/2}` is covered by
the balls `B_{R/16}(c)` with centers `c` on a grid of step `R/(16√d)`; on each, Theorem C.1 for the
translated coefficient field (`interiorMeyers_center`) and Lemma C.2 on `B_{R/4}(c) ⊆ B_R` give
the bound, and the number of balls depends only on `d`.
-/

open MeasureTheory Filter Set
open scoped ENNReal Pointwise

noncomputable section

namespace QSH

variable {d : ℕ}

theorem aestronglyMeasurable_euclideanNorm_normalizedVolumeOn {S T : Set (Vec d)} (hST : S ⊆ T)
    {g : Vec d → Vec d} (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict T)) :
    AEStronglyMeasurable (fun x => euclideanNorm (g x)) (PDE.normalizedVolumeOn S) :=
  ((memLp_euclideanNorm_of_coord hg).aestronglyMeasurable.mono_measure
    (Measure.restrict_mono hST le_rfl)).smul_measure _

/-- **The interior Meyers estimate at every center**: Theorem C.1 for `B_r(z)`, from Theorem C.1
on `B_r` for the translated coefficient field. -/
theorem interiorMeyers_center (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ (z : Vec d) (r : ℝ), 0 < r → ∀ (a : CoefficientField d Λ)
      (u : Vec d → ℝ) (g : Vec d → Vec d),
      MemLp u 2 (volume.restrict (ball z r)) →
      (∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball z r))) →
      HasWeakGradient (ball z r) u g →
      HasWeakDivergence (ball z r) (fun x => (a x).mulVec (g x)) (fun _ => 0) →
      PDE.eLpMeanNormOn (ball z (r / 2)) (ENNReal.ofReal (2 + δ)) (fun x => euclideanNorm (g x)) ≤
        ENNReal.ofReal C * PDE.eLpMeanNormOn (ball z r) 2 (fun x => euclideanNorm (g x)) := by
  obtain ⟨δ, C, hδ, hC, h1⟩ := theorem_C_1 hd hΛ
  refine ⟨δ, C, hδ, hC, fun z r hr a u g hu hg hug hdiv => ?_⟩
  have hpre : (fun x : Vec d => x + z) ⁻¹' ball z r = ball (0 : Vec d) r :=
    preimage_add_right_ball z r
  have hT : MeasurePreserving (fun x : Vec d => x + z) (volume.restrict (ball 0 r))
      (volume.restrict (ball z r)) := by
    rw [← hpre]
    exact (measurePreserving_add_right volume z).restrict_preimage (measurableSet_ball' z r)
  have hu' : MemLp (fun x => u (x + z)) 2 (volume.restrict (ball 0 r)) :=
    hu.comp_measurePreserving hT
  have hg' : ∀ i, MemLp (fun x => g (x + z) i) 2 (volume.restrict (ball 0 r)) := fun i =>
    (hg i).comp_measurePreserving hT
  have hmap : ∀ x ∈ ball (0 : Vec d) r, (1 : ℝ) • x + z ∈ ball z r := fun x hx => by
    rw [one_smul]
    have h : x ∈ (fun x : Vec d => x + z) ⁻¹' ball z r := by rw [hpre]; exact hx
    exact h
  have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) r)) :=
    isFiniteMeasure_restrict.mpr (volume_ball_ne_top' 0 r)
  have hug' : HasWeakGradient (ball 0 r) (fun x => u (x + z)) (fun x => g (x + z)) := by
    have h := hasWeakGradientOn_comp_smul_add one_pos z hmap hug
    simp only [inv_one, one_mul, one_smul] at h
    exact hasWeakGradient_of_hasWeakGradientOn' h
      (IntegrableOn.locallyIntegrableOn (hu'.integrable one_le_two))
      fun i => IntegrableOn.locallyIntegrableOn ((hg' i).integrable one_le_two)
  have hfl : ∀ i, MemLp (fun x => ((translate z a) x).mulVec (g (x + z)) i) 2
      (volume.restrict (ball 0 r)) := fun i =>
    memLp_coefficient_mulVec_apply (translate z a) (memLp_pi_iff.2 hg') i
  have hdiv' : HasWeakDivergence (ball 0 r) (fun x => ((translate z a) x).mulVec (g (x + z)))
      (fun _ => 0) := by
    have h := TwoScale.hasWeakDivergence_comp_smul_add one_pos z hmap hdiv (fun i => by
      simp only [one_smul]
      have e : (fun x => (a (x + z)).mulVec (g (x + z)) i) =
          fun x => ((translate z a) x).mulVec (g (x + z)) i := by
        funext x; show (a (x + z)).mulVec (g (x + z)) i = (a (z + x)).mulVec (g (x + z)) i
        rw [add_comm z x]
      rw [e]
      exact IntegrableOn.locallyIntegrableOn ((hfl i).integrable one_le_two))
    convert h using 2 with x
    simp only [one_smul]
    show ((translate z a) x).mulVec (g (x + z)) = (a (x + z)).mulVec (g (x + z))
    show (a (z + x)).mulVec (g (x + z)) = (a (x + z)).mulVec (g (x + z))
    rw [add_comm z x]
  have key := h1 (2 + δ) r (by linarith) hr (translate z a) (fun x => u (x + z))
    (fun x => g (x + z)) (fun _ => 0) (fun _ => 0) hu' hg' hug' (memLp_const 0)
    (fun _ => memLp_const 0) (by rw [negativeSobolevOneNorm_zero_zero]; exact ENNReal.zero_ne_top)
    (by simpa only [add_zero, neg_zero] using hdiv')
  rw [min_self, negativeSobolevOneNorm_zero_zero, add_zero] at key
  have hl : PDE.eLpMeanNormOn (ball (0 : Vec d) (r / 2)) (ENNReal.ofReal (2 + δ))
      (fun x => euclideanNorm (g (x + z))) =
        PDE.eLpMeanNormOn (ball z (r / 2)) (ENNReal.ofReal (2 + δ))
          (fun x => euclideanNorm (g x)) := by
    rw [← preimage_add_right_ball z (r / 2)]
    exact eLpMeanNormOn_comp_add z (measurableSet_ball' z (r / 2)) _
      (aestronglyMeasurable_euclideanNorm_normalizedVolumeOn
        (fun x hx => by
          show euclideanNorm (x - z) < r
          have : euclideanNorm (x - z) < r / 2 := hx
          linarith) hg)
  have hr' : PDE.eLpMeanNormOn (ball (0 : Vec d) r) 2 (fun x => euclideanNorm (g (x + z))) =
      PDE.eLpMeanNormOn (ball z r) 2 (fun x => euclideanNorm (g x)) := by
    rw [← preimage_add_right_ball z r]
    exact eLpMeanNormOn_comp_add z (measurableSet_ball' z r) _
      (aestronglyMeasurable_euclideanNorm_normalizedVolumeOn le_rfl hg)
  rw [← hl, ← hr']
  exact key

theorem volume_ball_eq_zero_center (z : Vec d) (r : ℝ) : volume (ball z r) = volume (ball (0 : Vec d) r) := by
  rw [← preimage_add_right_ball z r, measure_preimage_add_right]

/-- **The bound on each small ball** of the cover: for `|c| < 5R/8`,
`‖∇u‖_{L̲^{2+δ}(B_{R/16}(c))} ≤ K R⁻¹ ‖u - (u)_{B_R}‖_{L̲²(B_R)}`. -/
theorem meyers_smallBall (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 ≤ K ∧ ∀ R : ℝ, 0 < R → ∀ (a : CoefficientField d Λ)
      (u : Vec d → ℝ) (g : Vec d → Vec d),
      MemLp u 2 (volume.restrict (ball 0 R)) →
      (∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 R))) →
      HasWeakGradient (ball 0 R) u g →
      HasWeakDivergence (ball 0 R) (fun x => (a x).mulVec (g x)) (fun _ => 0) →
      ∀ c : Vec d, euclideanNorm c < 5 * R / 8 →
      PDE.eLpMeanNormOn (ball c (R / 16)) (ENNReal.ofReal (2 + δ))
          (fun x => euclideanNorm (g x)) ≤
        ENNReal.ofReal (K * (R⁻¹ * scalarRms volume (ball 0 R)
          (fun x => u x - ⨍ y in ball 0 R, u y))) := by
  obtain ⟨δ, C₁, hδ, hC₁, hM⟩ := interiorMeyers_center hd hΛ
  obtain ⟨C₂, hC₂, hCac⟩ := interiorCaccioppoli (d := d) hΛ
  refine ⟨δ, C₁ * C₂ * (4 * Real.sqrt (4 ^ d)), hδ, by positivity,
    fun R hR a u g hu hg hug hdiv c hc => ?_⟩
  have hsub : ball c (R / 4) ⊆ ball (0 : Vec d) R := fun x hx => by
    have hx' : euclideanNorm (x - c) < R / 4 := hx
    show euclideanNorm (x - 0) < R
    rw [sub_zero]
    calc euclideanNorm x = euclideanNorm ((x - c) + c) := by rw [sub_add_cancel]
      _ ≤ euclideanNorm (x - c) + euclideanNorm c := euclideanNorm_add_le' _ _
      _ < R := by linarith
  have hsub8 : ball c (R / 8) ⊆ ball c (R / 4) := fun x hx => by
    have hx' : euclideanNorm (x - c) < R / 8 := hx
    show euclideanNorm (x - c) < R / 4
    linarith
  have hμ : ∀ {S : Set (Vec d)}, S ⊆ ball (0 : Vec d) R →
      volume.restrict S ≤ volume.restrict (ball 0 R) := fun hS => Measure.restrict_mono hS le_rfl
  have hu4 := hu.mono_measure (hμ hsub)
  have hg4 : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball c (R / 4))) := fun i =>
    (hg i).mono_measure (hμ hsub)
  have hug4 := HasWeakGradient.mono hsub hug
  have hdiv4 := TwoScale.hasWeakDivergence_mono hsub hdiv
  -- the Meyers estimate on `B_{R/8}(c)`
  have h1 := hM c (R / 8) (by positivity) a u g (hu4.mono_measure (Measure.restrict_mono hsub8
    le_rfl)) (fun i => (hg4 i).mono_measure (Measure.restrict_mono hsub8 le_rfl))
    (HasWeakGradient.mono hsub8 hug4) (TwoScale.hasWeakDivergence_mono hsub8 hdiv4)
  rw [show R / 8 / 2 = R / 16 by ring, eLpMeanNormOn_two_euclideanNorm_eq
    (volume_ball_ne_zero' c (by positivity))
    (fun i => (hg4 i).mono_measure (Measure.restrict_mono hsub8 le_rfl))] at h1
  -- the Caccioppoli inequality on `B_{R/4}(c)`
  have h2 := hCac c (R / 4) (by positivity) a u g (fun _ => 0) (fun _ => 0) hu4 hg4 hug4
    (memLp_const 0) (fun _ => memLp_const 0) (by simpa only [add_zero, neg_zero] using hdiv4)
  rw [negativeSobolevOneNorm_zero_zero, add_zero, show R / 4 / 2 = R / 8 by ring] at h2
  -- the oscillation on `B_{R/4}(c)` and on `B_R`
  have hR0 : volume (ball (0 : Vec d) R) ≠ ⊤ := volume_ball_ne_top' 0 R
  have h3 := scalarRms_sub_setAverage_le_sub_const (volume_ball_ne_top' c (R / 4)) hu4
    (⨍ y in ball 0 R, u y)
  have hvol : volume.real (ball (0 : Vec d) R) ≤ 4 ^ d * volume.real (ball c (R / 4)) := by
    rw [measureReal_def, measureReal_def, volume_ball_eq_zero_center c (R / 4),
      show R = 4 * (R / 4) by ring, volume_ball_mul 0 (by norm_num : (0 : ℝ) < 4) (by positivity),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), show 4 * (R / 4) / 4 = R / 4 by ring]
  have hint : IntegrableOn (fun x => (u x - ⨍ y in ball 0 R, u y) ^ 2) (ball 0 R) := by
    have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
      isFiniteMeasure_restrict.mpr hR0
    exact ((hu.sub (memLp_const _)).integrable_sq)
  have h4 := scalarRms_le_sqrt_mul_of_subset hsub (volume_ball_ne_zero' c (by positivity)) hR0 hvol
    (by positivity) hint
  -- combination
  have hfin : ENNReal.ofReal (vectorRms volume (ball c (R / 8)) g) ≤
      ENNReal.ofReal (C₂ * ((R / 4)⁻¹ * (Real.sqrt (4 ^ d) * scalarRms volume (ball 0 R)
        (fun x => u x - ⨍ y in ball 0 R, u y)))) := by
    refine h2.trans ?_
    rw [← ENNReal.ofReal_mul hC₂.le]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (h3.trans h4) (by positivity)) hC₂.le)
  refine h1.trans ((mul_le_mul_right hfin _).trans (le_of_eq ?_))
  rw [← ENNReal.ofReal_mul hC₁]
  congr 1
  field_simp

/-- A set integral over a finite union is at most the sum of the set integrals. -/
theorem lintegral_biUnion_finset_le {ι : Type*} (s : Finset ι) (S : ι → Set (Vec d))
    (F : Vec d → ℝ≥0∞) : ∫⁻ x in ⋃ k ∈ s, S k, F x ≤ ∑ k ∈ s, ∫⁻ x in S k, F x := by
  classical
  refine Finset.induction_on s (by simp) (fun j s hj ih => ?_)
  rw [Finset.set_biUnion_insert, Finset.sum_insert hj]
  exact (lintegral_union_le _ _ _).trans (add_le_add le_rfl ih)

set_option maxHeartbeats 400000 in
/-- **(3.14)**: `‖∇u‖_{L̲^{2+δ}(B_{R/2})} ≤ C R⁻¹ ‖u - (u)_{B_R}‖_{L̲²(B_R)}` for weak solutions of
`-∇·(a∇u) = 0` in `B_R`. -/
theorem meyers_halfBall (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∀ (a : CoefficientField d Λ)
      (u : Vec d → ℝ) (g : Vec d → Vec d),
      MemLp u 2 (volume.restrict (ball 0 R)) →
      (∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 R))) →
      HasWeakGradient (ball 0 R) u g →
      HasWeakDivergence (ball 0 R) (fun x => (a x).mulVec (g x)) (fun _ => 0) →
      PDE.eLpMeanNormOn (ball 0 (R / 2)) (ENNReal.ofReal (2 + δ))
          (fun x => euclideanNorm (g x)) ≤
        ENNReal.ofReal (C * (R⁻¹ * scalarRms volume (ball 0 R)
          (fun x => u x - ⨍ y in ball 0 R, u y))) := by
  have hd0 : 0 < d := by omega
  obtain ⟨δ, K, hδ, hK, hsm⟩ := meyers_smallBall hd hΛ
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = ⌈8 * Real.sqrt d⌉₊ + 1 := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = ((2 * L + 1 : ℕ) : ℝ) ^ d := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := by rw [hN]; exact one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * L + 1))
  refine ⟨δ, N * K, hδ, mul_nonneg (by linarith) hK, fun R hR a u g hu hg hug hdiv => ?_⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = K * (R⁻¹ * scalarRms volume (ball 0 R)
      (fun x => u x - ⨍ y in ball 0 R, u y)) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; exact mul_nonneg hK (mul_nonneg (inv_nonneg.2 hR.le)
    (Real.sqrt_nonneg _))
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd0)
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = R / (16 * Real.sqrt d) := ⟨_, rfl⟩
  have hh0 : 0 < h := by rw [hh]; positivity
  obtain ⟨c, hc⟩ : ∃ c : (Fin d → ℤ) → Vec d, c = fun k i => h * (k i : ℝ) := ⟨_, rfl⟩
  classical
  obtain ⟨I, hI⟩ : ∃ I : Finset (Fin d → ℤ), I = (Fintype.piFinset fun _ : Fin d =>
      Finset.Icc (-(L : ℤ)) L).filter (fun k => euclideanNorm (c k) < 5 * R / 8) := ⟨_, rfl⟩
  -- the cover of `B_{R/2}`
  have hcover : ball (0 : Vec d) (R / 2) ⊆ ⋃ k ∈ I, ball (c k) (R / 16) := by
    intro y hy
    have hy' : euclideanNorm y < R / 2 := mem_ball_zero_iff'.1 hy
    obtain ⟨k, hk⟩ : ∃ k : Fin d → ℤ, k = fun i => round (y i / h) := ⟨_, rfl⟩
    have hk1 : ∀ i, |(y - c k) i| ≤ h / 2 := fun i => by
      have h1 := abs_sub_round (y i / h)
      have e : (y - c k) i = h * (y i / h - (round (y i / h) : ℝ)) := by
        rw [hc, hk]; simp only [Pi.sub_apply]; field_simp
      rw [e, abs_mul, abs_of_pos hh0]
      nlinarith
    have hyc : euclideanNorm (y - c k) < R / 16 := by
      have h1 := euclideanNorm_le_sqrt_mul_of_abs_le hk1
      have e : Real.sqrt d * (h / 2) = R / 32 := by rw [hh]; field_simp; ring
      linarith
    have hkL : ∀ i, k i ∈ Finset.Icc (-(L : ℤ)) L := fun i => by
      have h1 := abs_sub_round (y i / h)
      have hyi : |y i| < R / 2 := (abs_coord_le_euclideanNorm y i).trans_lt hy'
      have ht : |y i / h| < 8 * Real.sqrt d := by
        rw [abs_div, abs_of_pos hh0, div_lt_iff₀ hh0, hh]
        have : 8 * Real.sqrt d * (R / (16 * Real.sqrt d)) = R / 2 := by field_simp; ring
        linarith
      have hr : |((round (y i / h) : ℤ) : ℝ)| < (L : ℝ) := by
        have h2 : |((round (y i / h) : ℤ) : ℝ)| ≤ |y i / h| + 1 / 2 := by
          have := abs_sub (y i / h) (y i / h - (round (y i / h) : ℝ))
          rw [sub_sub_cancel] at this
          linarith
        have h3 : 8 * Real.sqrt d ≤ (⌈8 * Real.sqrt d⌉₊ : ℝ) := Nat.le_ceil _
        rw [hL]; push_cast; linarith
      rw [hk, Finset.mem_Icc]
      rw [abs_lt] at hr
      constructor <;> [exact_mod_cast hr.1.le; exact_mod_cast hr.2.le]
    have hcn : euclideanNorm (c k) < 5 * R / 8 := by
      have := euclideanNorm_add_le' y (c k - y)
      rw [add_sub_cancel] at this
      have e : euclideanNorm (c k - y) = euclideanNorm (y - c k) := by
        unfold euclideanNorm euclideanSq dot
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.sub_apply]
        ring
      linarith
    have hkI : k ∈ I := by rw [hI]; exact Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 hkL, hcn⟩
    exact Set.mem_biUnion (Finset.mem_coe.2 hkI) hyc
  -- the integrals
  have hp0 : (0 : ℝ) < 2 + δ := by linarith
  have hmR : AEStronglyMeasurable (fun x => euclideanNorm (g x)) (volume.restrict (ball 0 R)) :=
    (memLp_euclideanNorm_of_coord hg).aestronglyMeasurable
  have hρ : ∀ k ∈ I, ∫⁻ x in ball (c k) (R / 16), ‖euclideanNorm (g x)‖ₑ ^ (2 + δ) ≤
      volume (ball (0 : Vec d) (R / 16)) * ENNReal.ofReal M ^ (2 + δ) := fun k hk => by
    have hcn : euclideanNorm (c k) < 5 * R / 8 := by
      rw [hI] at hk; exact (Finset.mem_filter.1 hk).2
    have hsub : ball (c k) (R / 16) ⊆ ball (0 : Vec d) R := fun x hx => by
      have hx' : euclideanNorm (x - c k) < R / 16 := hx
      show euclideanNorm (x - 0) < R
      rw [sub_zero]
      calc euclideanNorm x = euclideanNorm ((x - c k) + c k) := by rw [sub_add_cancel]
        _ ≤ euclideanNorm (x - c k) + euclideanNorm (c k) := euclideanNorm_add_le' _ _
        _ < R := by linarith
    have e := eLpMeanNormOn_rpow_eq hp0 (hmR.mono_measure (Measure.restrict_mono hsub le_rfl))
    have hv0 := volume_ball_ne_zero' (c k) (by positivity : (0 : ℝ) < R / 16)
    have hvt := volume_ball_ne_top' (c k) (R / 16)
    have e2 : ∫⁻ x in ball (c k) (R / 16), ‖euclideanNorm (g x)‖ₑ ^ (2 + δ) =
        volume (ball (c k) (R / 16)) * PDE.eLpMeanNormOn (ball (c k) (R / 16))
          (ENNReal.ofReal (2 + δ)) (fun x => euclideanNorm (g x)) ^ (2 + δ) := by
      rw [e, ← mul_assoc, ENNReal.mul_inv_cancel hv0 hvt, one_mul]
    rw [e2, volume_ball_eq_zero_center (c k) (R / 16), hM]
    exact mul_le_mul_right (ENNReal.rpow_le_rpow (hsm R hR a u g hu hg hug hdiv (c k) hcn)
      hp0.le) _
  have hcard : (I.card : ℝ≥0∞) ≤ ENNReal.ofReal N := by
    have h1 : I.card ≤ (2 * L + 1) ^ d := by
      rw [hI]
      refine (Finset.card_filter_le _ _).trans (le_of_eq ?_)
      rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Int.card_Icc]
      congr 1
      omega
    rw [hN, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast h1)
  have hsum : ∫⁻ x in ball (0 : Vec d) (R / 2), ‖euclideanNorm (g x)‖ₑ ^ (2 + δ) ≤
      ENNReal.ofReal N * (volume (ball (0 : Vec d) (R / 16)) * ENNReal.ofReal M ^ (2 + δ)) := by
    calc _ ≤ ∫⁻ x in ⋃ k ∈ I, ball (c k) (R / 16), ‖euclideanNorm (g x)‖ₑ ^ (2 + δ) :=
          lintegral_mono_set hcover
      _ ≤ ∑ k ∈ I, ∫⁻ x in ball (c k) (R / 16), ‖euclideanNorm (g x)‖ₑ ^ (2 + δ) :=
          lintegral_biUnion_finset_le _ _ _
      _ ≤ ∑ _k ∈ I, volume (ball (0 : Vec d) (R / 16)) * ENNReal.ofReal M ^ (2 + δ) :=
          Finset.sum_le_sum hρ
      _ = I.card * (volume (ball (0 : Vec d) (R / 16)) * ENNReal.ofReal M ^ (2 + δ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_left hcard _
  -- the normalized norm on `B_{R/2}`
  have hv2 : volume (ball (0 : Vec d) (R / 2)) =
      ENNReal.ofReal (8 ^ d) * volume (ball (0 : Vec d) (R / 16)) := by
    rw [show R / 2 = 8 * (R / 16) by ring, volume_ball_mul 0 (by norm_num) (by positivity)]
  have hv16 := volume_ball_ne_zero' (0 : Vec d) (by positivity : (0 : ℝ) < R / 16)
  have hv16t := volume_ball_ne_top' (0 : Vec d) (R / 16)
  have hratio : (volume (ball (0 : Vec d) (R / 2)))⁻¹ * volume (ball (0 : Vec d) (R / 16)) ≤ 1 := by
    rw [hv2, ENNReal.mul_inv (Or.inl (by simp)) (Or.inl ENNReal.ofReal_ne_top), mul_assoc,
      ENNReal.inv_mul_cancel hv16 hv16t, mul_one]
    exact ENNReal.inv_le_one.2 (by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by norm_num)))
  have hpow : PDE.eLpMeanNormOn (ball (0 : Vec d) (R / 2)) (ENNReal.ofReal (2 + δ))
      (fun x => euclideanNorm (g x)) ^ (2 + δ) ≤ ENNReal.ofReal (N * M) ^ (2 + δ) := by
    rw [eLpMeanNormOn_rpow_eq hp0 (hmR.mono_measure (Measure.restrict_mono
      (fun x hx => by
        have hx' : euclideanNorm (x - 0) < R / 2 := hx
        show euclideanNorm (x - 0) < R
        linarith) le_rfl))]
    calc _ ≤ (volume (ball (0 : Vec d) (R / 2)))⁻¹ *
          (ENNReal.ofReal N * (volume (ball (0 : Vec d) (R / 16)) * ENNReal.ofReal M ^ (2 + δ))) :=
          mul_le_mul_right hsum _
      _ = ENNReal.ofReal N * (((volume (ball (0 : Vec d) (R / 2)))⁻¹ *
          volume (ball (0 : Vec d) (R / 16))) * ENNReal.ofReal M ^ (2 + δ)) := by ring
      _ ≤ ENNReal.ofReal N * (1 * ENNReal.ofReal M ^ (2 + δ)) :=
          mul_le_mul_right (mul_le_mul_left hratio _) _
      _ ≤ ENNReal.ofReal N ^ (2 + δ) * ENNReal.ofReal M ^ (2 + δ) := by
          rw [one_mul]
          refine mul_le_mul_left ?_ _
          have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal N := by
            rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hN1
          calc ENNReal.ofReal N = ENNReal.ofReal N ^ (1 : ℝ) := (ENNReal.rpow_one _).symm
            _ ≤ _ := ENNReal.rpow_le_rpow_of_exponent_le h1 (by linarith)
      _ = _ := by
          rw [ENNReal.ofReal_mul (by linarith), ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
  have h := (ENNReal.rpow_le_rpow_iff hp0).1 hpow
  refine h.trans (le_of_eq ?_)
  rw [hM, mul_assoc]

end QSH
