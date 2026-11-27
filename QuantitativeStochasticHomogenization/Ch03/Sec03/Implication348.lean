import QuantitativeStochasticHomogenization.Ch03.Sec03.Theorem38Base
import QuantitativeStochasticHomogenization.Ch03.Sec03.HomogeneousParts

/-!
# The implication (3.48) of the proof of Theorem 3.8

Armstrong–Kuusi–Mourrat, Section 3.3, proof of (3.48): `(i)_k` and `(ii)_k` imply `(iii')_k`. The
statement here is deterministic, for one coefficient field `a`: from the estimate (3.50) on the
balls of radius at least `r₀` and from `(ii)_k` with a scale `r₀` large enough, every solution `u` in
`B_R`, `R ≥ r₀`, has some `φ ∈ A_k` with `‖u - φ‖_{L̲²(B_r)} ≤ C (r/R)^{k+1-δ/2} ‖u‖_{L̲²(B_R)}` for
`r ∈ [r₀, R]`. The proof is the book's: the correction `φ` is the sum of the elements of `A_k` given by
`(ii)_k` for the near-minimizers in `Ā_k` along the radii `θ^j R`, and the growth of these elements,
which the book takes from `(i)_k`, follows here from `(ii)_k` and (3.27).
-/

open MeasureTheory Filter Set Topology
open scoped Pointwise

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- `u ∈ H¹(B_R)` is a weak solution of `-∇·(a∇u) = 0` in `B_R` (the space `A(B_R)`). -/
def IsSolutionBall (a : CoefficientField d Λ) (R : ℝ) (u : Vec d → ℝ) : Prop :=
  MemLp u 2 (volume.restrict (ball 0 R)) ∧ ∃ g : Vec d → Vec d,
    (∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 R))) ∧ HasWeakGradient (ball 0 R) u g ∧
    HasWeakDivergence (ball 0 R) (fun x => (a x).mulVec (g x)) (fun _ => 0)

theorem IsSolutionBall.mono {a : CoefficientField d Λ} {r R : ℝ} {u : Vec d → ℝ}
    (hu : IsSolutionBall a R u) (hrR : r ≤ R) : IsSolutionBall a r u := by
  obtain ⟨hL2, g, hg, hgrad, hdiv⟩ := hu
  have hsub := ball_zero_subset_ball_zero (d := d) hrR
  exact ⟨hL2.mono_measure (Measure.restrict_mono hsub le_rfl), g,
    fun i => (hg i).mono_measure (Measure.restrict_mono hsub le_rfl), hgrad.mono hsub,
    hdiv.mono' hsub⟩

theorem IsSolutionBall.add {a : CoefficientField d Λ} {R : ℝ} {u v : Vec d → ℝ}
    (hu : IsSolutionBall a R u) (hv : IsSolutionBall a R v) :
    IsSolutionBall a R (fun x => u x + v x) := by
  obtain ⟨hu1, gu, hgu, hu2, hu3⟩ := hu
  obtain ⟨hv1, gv, hgv, hv2, hv3⟩ := hv
  refine ⟨hu1.add hv1, fun x => gu x + gv x, fun i => (hgu i).add (hgv i),
    hasWeakGradient_add hu2 hv2, ?_⟩
  have h := hasWeakDivergence_add hu3 hv3
  convert h using 1
  · funext x; rw [Matrix.mulVec_add]
  · funext x; simp

theorem IsSolutionBall.const_mul {a : CoefficientField d Λ} {R : ℝ} {u : Vec d → ℝ}
    (hu : IsSolutionBall a R u) (c : ℝ) : IsSolutionBall a R (fun x => c * u x) := by
  obtain ⟨hu1, gu, hgu, hu2, hu3⟩ := hu
  refine ⟨hu1.const_mul c, fun x => c • gu x, fun i => ?_, hu2.const_mul' c, ?_⟩
  · simpa only [Pi.smul_apply, smul_eq_mul] using (hgu i).const_mul c
  · convert hu3.const_smul' c using 2 with x
    rw [Matrix.mulVec_smul]

theorem IsSolutionBall.sub {a : CoefficientField d Λ} {R : ℝ} {u v : Vec d → ℝ}
    (hu : IsSolutionBall a R u) (hv : IsSolutionBall a R v) :
    IsSolutionBall a R (fun x => u x - v x) := by
  have h := hu.add (hv.const_mul (-1))
  convert h using 2 with x
  ring

theorem isSolutionBall_of_mem_solutionGrowthSpace {a : CoefficientField d Λ} {k : ℕ}
    {φ : Vec d → ℝ} (hφ : φ ∈ solutionGrowthSpace a k) {R : ℝ} (hR : 0 < R) :
    IsSolutionBall a R φ := hφ.1 R hR

theorem zero_mem_solutionGrowthSpace (a : CoefficientField d Λ) (k : ℕ) :
    (fun _ => (0 : ℝ)) ∈ solutionGrowthSpace a k := by
  refine ⟨fun R _ => ⟨MemLp.zero, fun _ => 0, fun _ => MemLp.zero,
    hasWeakGradient_mono (subset_univ _) (hasWeakGradient_const 0), ?_⟩, ?_⟩
  · simpa only [Matrix.mulVec_zero] using
      (hasWeakDivergence_const_field (0 : Vec d)).mono' (subset_univ (ball (0 : Vec d) R))
  · have h : (fun r : ℝ => (r ^ (k + 1))⁻¹ *
        scalarRms volume (ball (0 : Vec d) r) (fun _ => (0 : ℝ))) =
        fun _ => 0 := by
      funext r
      have : scalarRms volume (ball (0 : Vec d) r) (fun _ => (0 : ℝ)) = 0 := by
        unfold scalarRms; simp
      rw [this, mul_zero]
    rw [h]; exact tendsto_const_nhds

theorem add_mem_solutionGrowthSpace {a : CoefficientField d Λ} {k : ℕ} {φ ψ : Vec d → ℝ}
    (hφ : φ ∈ solutionGrowthSpace a k) (hψ : ψ ∈ solutionGrowthSpace a k) :
    (fun x => φ x + ψ x) ∈ solutionGrowthSpace a k := by
  refine ⟨fun R hR => (isSolutionBall_of_mem_solutionGrowthSpace hφ hR).add
    (isSolutionBall_of_mem_solutionGrowthSpace hψ hR), ?_⟩
  have hup := (hφ.2.add hψ.2)
  rw [add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with r hr
    exact mul_nonneg (by positivity) (scalarRms_nonneg _ _)
  · filter_upwards [eventually_gt_atTop 0] with r hr
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact scalarRms_add_le (hφ.1 r hr).1 (hψ.1 r hr).1

theorem sum_mem_solutionGrowthSpace {a : CoefficientField d Λ} {k : ℕ} (s : Finset ℕ)
    {Φ : ℕ → Vec d → ℝ} (hΦ : ∀ m ∈ s, Φ m ∈ solutionGrowthSpace a k) :
    (fun x => ∑ m ∈ s, Φ m x) ∈ solutionGrowthSpace a k := by
  induction s using Finset.induction_on with
  | empty => simpa using zero_mem_solutionGrowthSpace a k
  | insert m s hm ih =>
    have h := add_mem_solutionGrowthSpace (hΦ m (Finset.mem_insert_self m s))
      (ih fun m' hm' => hΦ m' (Finset.mem_insert_of_mem hm'))
    simpa only [Finset.sum_insert hm] using h

/-- **The iteration along the radii `θ^j R`**: if a solution in `B_{θ^j R}` can be corrected by a
good element of `A_k` with a gain `q` from `B_{θ^j R}` to `B_{θ^{j+1} R}` for `j < n`, then
`‖u - ∑_{m < j} Φ_m‖_{L̲²(B_{θ^j R})} ≤ q^j ‖u‖_{L̲²(B_R)}` for `j ≤ n`. -/
theorem exists_correction_iteration {a : CoefficientField d Λ} {k : ℕ} {θ q R : ℝ}
    (Good : (Vec d → ℝ) → Prop) (hGood : ∀ φ, Good φ → φ ∈ solutionGrowthSpace a k)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hR : 0 < R) (hq : 0 ≤ q) {u : Vec d → ℝ}
    (hu : IsSolutionBall a R u) (n : ℕ)
    (hstep : ∀ j < n, ∀ v, IsSolutionBall a (θ ^ j * R) v → ∃ φ, Good φ ∧
      scalarRms volume (ball 0 (θ ^ (j + 1) * R)) (fun x => v x - φ x) ≤
        q * scalarRms volume (ball 0 (θ ^ j * R)) v) :
    ∃ Φ : ℕ → Vec d → ℝ, (∀ m < n, Good (Φ m)) ∧ ∀ j ≤ n,
      scalarRms volume (ball 0 (θ ^ j * R)) (fun x => u x - ∑ m ∈ Finset.range j, Φ m x) ≤
        q ^ j * scalarRms volume (ball 0 R) u := by
  induction n with
  | zero =>
    refine ⟨fun _ _ => 0, fun m hm => absurd hm (Nat.not_lt_zero m), fun j hj => ?_⟩
    rw [Nat.le_zero.1 hj]
    simp
  | succ n ih =>
    obtain ⟨Φ, hΦ, hb⟩ := ih (fun j hj => hstep j (by omega))
    have hθn : θ ^ n * R ≤ R := by
      have : θ ^ n ≤ 1 := pow_le_one₀ hθ0.le hθ1
      nlinarith
    have hθpos : 0 < θ ^ n * R := by positivity
    have hsol : IsSolutionBall a (θ ^ n * R)
        (fun x => u x - ∑ m ∈ Finset.range n, Φ m x) :=
      (hu.mono hθn).sub (isSolutionBall_of_mem_solutionGrowthSpace
        (sum_mem_solutionGrowthSpace _ fun m hm => hGood _ (hΦ m (Finset.mem_range.1 hm))) hθpos)
    obtain ⟨φ, hφ, hbφ⟩ := hstep n (Nat.lt_succ_self n) _ hsol
    refine ⟨Function.update Φ n φ, fun m hm => ?_, fun j hj => ?_⟩
    · by_cases h : m = n
      · subst h; rw [Function.update_self]; exact hφ
      · rw [Function.update_of_ne h]; exact hΦ m (by omega)
    · have hsum : ∀ j ≤ n, ∀ x, ∑ m ∈ Finset.range j, Function.update Φ n φ m x =
          ∑ m ∈ Finset.range j, Φ m x := fun j hj x =>
        Finset.sum_congr rfl fun m hm => by
          rw [Function.update_of_ne (by have := Finset.mem_range.1 hm; omega)]
      rcases Nat.lt_or_ge j (n + 1) with hj' | hj'
      · simp_rw [hsum j (by omega)]
        exact hb j (by omega)
      · have hjn : j = n + 1 := by omega
        subst hjn
        have e : (fun x => u x - ∑ m ∈ Finset.range (n + 1), Function.update Φ n φ m x) =
            fun x => (u x - ∑ m ∈ Finset.range n, Φ m x) - φ x := by
          funext x
          rw [Finset.sum_range_succ, hsum n le_rfl x, Function.update_self]
          ring
        rw [e]
        refine hbφ.trans ?_
        rw [pow_succ, mul_comm (q ^ n) q, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hb n le_rfl) hq

/-- The growth of a polynomial of degree at most `k`, from (3.27):
`‖Q‖_{L̲²(B_s)} ≤ C (s/t)^k ‖Q‖_{L̲²(B_t)}` for `0 < t ≤ s`. -/
theorem scalarRms_poly_growth (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : MvPolynomial (Fin d) ℝ, Q.totalDegree ≤ k → ∀ t s : ℝ, 0 < t → t ≤ s →
      scalarRms volume (ball 0 s) (fun x => MvPolynomial.eval x Q) ≤
        C * (s / t) ^ k * scalarRms volume (ball 0 t) (fun x => MvPolynomial.eval x Q) := by
  obtain ⟨C, hC0, h27⟩ := scalarRms_homogeneousComponents_zero (d := d) k
  refine ⟨C, hC0, fun Q hQ t s ht hts => ?_⟩
  have hs : 0 < s := lt_of_lt_of_le ht hts
  have hc : 0 < s / t := div_pos hs ht
  have hc1 : 1 ≤ s / t := (one_le_div ht).2 hts
  have hscale : ∀ m, scalarRms volume (ball 0 s)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q)) =
      (s / t) ^ m * scalarRms volume (ball 0 t)
        (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q)) := fun m => by
    have hball : ball (0 : Vec d) s = (s / t) • ball 0 t := by
      rw [smul_ball_zero hc, div_mul_cancel₀ s ht.ne']
    have e := TwoScale.scalarRms_comp_smul hc (ball (0 : Vec d) t)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q))
    rw [← hball] at e
    rw [← e]
    have e2 : (fun y => MvPolynomial.eval ((s / t) • y) (MvPolynomial.homogeneousComponent m Q)) =
        fun y => (s / t) ^ m * MvPolynomial.eval y (MvPolynomial.homogeneousComponent m Q) := by
      funext y
      exact PDE.eval_smul_of_isHomogeneous (MvPolynomial.homogeneousComponent_isHomogeneous m Q) _ y
    rw [e2, scalarRms_const_mul, abs_of_pos (pow_pos hc m)]
  obtain ⟨h1, -⟩ := h27 Q hQ s hs
  obtain ⟨-, h2⟩ := h27 Q hQ t ht
  calc scalarRms volume (ball 0 s) (fun x => MvPolynomial.eval x Q)
      ≤ ∑ m ∈ Finset.range (k + 1), scalarRms volume (ball 0 s)
          (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q)) := h1
    _ ≤ ∑ m ∈ Finset.range (k + 1), (s / t) ^ k * scalarRms volume (ball 0 t)
          (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q)) := by
        refine Finset.sum_le_sum fun m hm => ?_
        rw [hscale m]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hc1 (by have := Finset.mem_range.1 hm; omega)) (scalarRms_nonneg _ _)
    _ = (s / t) ^ k * ∑ m ∈ Finset.range (k + 1), scalarRms volume (ball 0 t)
          (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q)) := by
        rw [Finset.mul_sum]
    _ ≤ (s / t) ^ k * (C * scalarRms volume (ball 0 t) (fun x => MvPolynomial.eval x Q)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

theorem scalarRms_le_add_of_sub {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U)) :
    scalarRms volume U g ≤ scalarRms volume U f + scalarRms volume U (fun x => f x - g x) := by
  have h := scalarRms_sub_le (f := f) (g := fun x => f x - g x) hf (hf.sub hg)
  have e : (fun x => f x - (f x - g x)) = g := by funext x; ring
  rwa [e] at h

/-- **One correction step of (3.48)**: from (3.50) and `(ii)_k`, with `r₀` large, a solution `v` in
`B_r`, `θ r ≥ r₀`, has `φ ∈ A_k` with `‖v - φ‖_{L̲²(B_{θr})} ≤ θ^{k+1-δ/2} ‖v‖_{L̲²(B_r)}`, and `φ`
grows like a polynomial of degree `k` above the scale `r₀`. -/
theorem exists_correction_step (k : ℕ) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ (a : CoefficientField d Λ) (A : Mat d) (r₀ θ δ C₅₀ C₂ : ℝ),
      0 < r₀ → 0 < θ → θ < 1 → 0 < δ → δ ≤ 1 → 0 ≤ C₂ →
      (∀ r : ℝ, r₀ ≤ r → ∀ v, IsSolutionBall a r v →
        harmonicFlatness A k v (θ * r) ≤
          1 / 4 * θ ^ ((k : ℝ) + 1 - δ / 2) * harmonicFlatness A k v r +
            C₅₀ * r ^ (-δ) * scalarRms volume (ball 0 r) v) →
      (∀ p ∈ harmonicPolys A k, ∃ φ ∈ solutionGrowthSpace a k, ∀ s : ℝ, r₀ ≤ s →
        scalarRms volume (ball 0 s) (fun x => φ x - p x) ≤
          C₂ * s ^ (-δ) * scalarRms volume (ball 0 s) p) →
      C₅₀ * r₀ ^ (-δ) ≤ 1 / 8 * θ ^ ((k : ℝ) + 1 - δ / 2) →
      C₂ * r₀ ^ (-δ) * (Real.sqrt ((1 / θ) ^ d) + 1) ≤ 1 / 2 * θ ^ ((k : ℝ) + 1 - δ / 2) →
      C₂ * r₀ ^ (-δ) ≤ 1 / 2 →
      ∀ r : ℝ, r₀ ≤ θ * r → ∀ v, IsSolutionBall a r v → ∃ φ,
        (φ ∈ solutionGrowthSpace a k ∧ ∀ t s : ℝ, r₀ ≤ t → t ≤ s →
          scalarRms volume (ball 0 s) φ ≤ Cg * (s / t) ^ k * scalarRms volume (ball 0 t) φ) ∧
        scalarRms volume (ball 0 (θ * r)) (fun x => v x - φ x) ≤
          θ ^ ((k : ℝ) + 1 - δ / 2) * scalarRms volume (ball 0 r) v := by
  obtain ⟨C₂₇, hC₂₇, hgrow⟩ := scalarRms_poly_growth (d := d) k
  refine ⟨4 * C₂₇, by positivity, ?_⟩
  intro a A r₀ θ δ C₅₀ C₂ hr₀ hθ0 hθ1 hδ hδ1 hC₂ H50 Hii hs50 hs2 hs2' r hθr v hv
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = (k : ℝ) + 1 - δ / 2 := ⟨_, rfl⟩
  rw [← hβ] at H50 hs50 hs2 ⊢
  have hr : 0 < r := by
    by_contra h; push Not at h; nlinarith
  have hθr0 : 0 < θ * r := mul_pos hθ0 hr
  have hθrr : θ * r ≤ r := by nlinarith
  have hr₀r : r₀ ≤ r := hθr.trans hθrr
  have hθβ0 : 0 < θ ^ β := Real.rpow_pos_of_pos hθ0 β
  have hsq : 0 ≤ Real.sqrt ((1 / θ) ^ d) := Real.sqrt_nonneg _
  have hrpow : ∀ x : ℝ, r₀ ≤ x → x ^ (-δ) ≤ r₀ ^ (-δ) := fun x hx =>
    Real.rpow_le_rpow_of_nonpos hr₀ hx (by linarith)
  -- the polynomial growth of a good correction
  have hgood : ∀ p ∈ harmonicPolys A k, ∀ φ, (∀ s : ℝ, r₀ ≤ s →
      scalarRms volume (ball 0 s) (fun x => φ x - p x) ≤
        C₂ * s ^ (-δ) * scalarRms volume (ball 0 s) p) → φ ∈ solutionGrowthSpace a k →
      ∀ t s : ℝ, r₀ ≤ t → t ≤ s →
        scalarRms volume (ball 0 s) φ ≤ 4 * C₂₇ * (s / t) ^ k * scalarRms volume (ball 0 t) φ := by
    intro p hp φ hφp hφ t s ht hts
    have ht0 : 0 < t := lt_of_lt_of_le hr₀ ht
    have hs0 : 0 < s := lt_of_lt_of_le ht0 hts
    obtain ⟨⟨P, hP, hPe⟩, hph⟩ := hp
    have hpP : p = fun x => MvPolynomial.eval x P := funext hPe
    have hpt0 := scalarRms_nonneg (d := d) (ball 0 t) p
    have hps0 := scalarRms_nonneg (d := d) (ball 0 s) p
    -- `‖p‖_t ≤ 2 ‖φ‖_t`
    have h1 : scalarRms volume (ball 0 t) p ≤ 2 * scalarRms volume (ball 0 t) φ := by
      have h := scalarRms_le_add_of_sub (hφ.1 t ht0).1 (hph t ht0).1
      have h' := hφp t ht
      have : C₂ * t ^ (-δ) ≤ 1 / 2 := (mul_le_mul_of_nonneg_left (hrpow t ht) hC₂).trans hs2'
      nlinarith
    -- `‖φ‖_s ≤ 2 ‖p‖_s`
    have h2 : scalarRms volume (ball 0 s) φ ≤ 2 * scalarRms volume (ball 0 s) p := by
      have h := scalarRms_le_add_of_sub (hph s hs0).1 (hφ.1 s hs0).1
      have e : (fun x => p x - φ x) = fun x => -1 * (φ x - p x) := by funext x; ring
      rw [e, scalarRms_const_mul, abs_neg, abs_one, one_mul] at h
      have h' := hφp s (ht.trans hts)
      have : C₂ * s ^ (-δ) ≤ 1 / 2 :=
        (mul_le_mul_of_nonneg_left (hrpow s (ht.trans hts)) hC₂).trans hs2'
      nlinarith
    have h3 := hgrow P hP t s ht0 hts
    rw [← hpP] at h3
    have hst : 0 ≤ (s / t) ^ k := by positivity
    calc scalarRms volume (ball 0 s) φ ≤ 2 * scalarRms volume (ball 0 s) p := h2
      _ ≤ 2 * (C₂₇ * (s / t) ^ k * scalarRms volume (ball 0 t) p) := by linarith
      _ ≤ 2 * (C₂₇ * (s / t) ^ k * (2 * scalarRms volume (ball 0 t) φ)) := by
          gcongr
      _ = 4 * C₂₇ * (s / t) ^ k * scalarRms volume (ball 0 t) φ := by ring
  have hvθ : MemLp v 2 (volume.restrict (ball (0 : Vec d) (θ * r))) :=
    hv.1.mono_measure (Measure.restrict_mono (ball_zero_subset_ball_zero hθrr) le_rfl)
  have hvball : scalarRms volume (ball 0 (θ * r)) v ≤
      Real.sqrt ((1 / θ) ^ d) * scalarRms volume (ball 0 r) v := by
    have h := scalarRms_ball_le hθr0 hθrr hv.1
    rwa [show r / (θ * r) = 1 / θ by field_simp] at h
  have hv0 := scalarRms_nonneg (d := d) (ball 0 r) v
  rcases hv0.eq_or_lt with hv00 | hvpos
  · refine ⟨fun _ => 0, ⟨zero_mem_solutionGrowthSpace a k, fun t s _ _ => ?_⟩, ?_⟩
    · have e : ∀ ρ : ℝ, scalarRms volume (ball (0 : Vec d) ρ) (fun _ => (0 : ℝ)) = 0 := fun ρ => by
        unfold scalarRms; simp
      rw [e, e, mul_zero]
    · simp only [sub_zero]
      rw [← hv00] at hvball ⊢
      rw [mul_zero] at hvball ⊢
      exact hvball
  -- a near-minimizer in `Ā_k`
  have hflat : harmonicFlatness A k v (θ * r) ≤ 3 / 8 * θ ^ β * scalarRms volume (ball 0 r) v := by
    have h1 := harmonicFlatness_le v r (zero_mem_harmonicPolys A k)
    simp only [sub_zero] at h1
    have h2 : C₅₀ * r ^ (-δ) ≤ 1 / 8 * θ ^ β := by
      rcases le_or_gt 0 C₅₀ with hC | hC
      · exact (mul_le_mul_of_nonneg_left (hrpow r hr₀r) hC).trans hs50
      · have : C₅₀ * r ^ (-δ) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hC.le (Real.rpow_nonneg hr.le _)
        linarith
    have h3 := H50 r hr₀r v hv
    nlinarith [harmonicFlatness_nonneg A k v r]
  have : Nonempty (harmonicPolys A k) := ⟨⟨_, zero_mem_harmonicPolys A k⟩⟩
  have hlt : harmonicFlatness A k v (θ * r) < 1 / 2 * θ ^ β * scalarRms volume (ball 0 r) v := by
    have : 3 / 8 * θ ^ β * scalarRms volume (ball 0 r) v <
        1 / 2 * θ ^ β * scalarRms volume (ball 0 r) v := by
      have := mul_pos hθβ0 hvpos
      nlinarith
    linarith
  obtain ⟨⟨p, hp⟩, hpb⟩ := exists_lt_of_ciInf_lt hlt
  simp only at hpb
  obtain ⟨φ, hφ, hφp⟩ := Hii p hp
  refine ⟨φ, ⟨hφ, hgood p hp φ hφp hφ⟩, ?_⟩
  have hpL2 := (hp.2 (θ * r) hθr0).1
  have hφL2 := (hφ.1 (θ * r) hθr0).1
  -- `‖p‖_{θr} ≤ (2^{d/2}θ^{-d/2} + ½θ^β) ‖v‖_r`
  have hpn : scalarRms volume (ball 0 (θ * r)) p ≤
      (Real.sqrt ((1 / θ) ^ d) + 1) * scalarRms volume (ball 0 r) v := by
    have h := scalarRms_le_add_of_sub hvθ hpL2
    have hθβ1 : θ ^ β ≤ 1 := Real.rpow_le_one hθ0.le hθ1.le (by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      rw [hβ]; linarith)
    nlinarith
  have hsplit : scalarRms volume (ball 0 (θ * r)) (fun x => v x - φ x) ≤
      scalarRms volume (ball 0 (θ * r)) (fun x => v x - p x) +
        scalarRms volume (ball 0 (θ * r)) (fun x => φ x - p x) := by
    have e : (fun x => v x - φ x) = fun x => (v x - p x) - (φ x - p x) := by funext x; ring
    rw [e]
    exact scalarRms_sub_le (hvθ.sub hpL2) (hφL2.sub hpL2)
  have hφb := hφp (θ * r) hθr
  have hC₂r : C₂ * (θ * r) ^ (-δ) ≤ C₂ * r₀ ^ (-δ) :=
    mul_le_mul_of_nonneg_left (hrpow _ hθr) hC₂
  calc scalarRms volume (ball 0 (θ * r)) (fun x => v x - φ x)
      ≤ 1 / 2 * θ ^ β * scalarRms volume (ball 0 r) v +
          C₂ * r₀ ^ (-δ) * ((Real.sqrt ((1 / θ) ^ d) + 1) * scalarRms volume (ball 0 r) v) := by
        refine hsplit.trans (add_le_add hpb.le (hφb.trans ?_))
        exact mul_le_mul hC₂r hpn (scalarRms_nonneg _ _) (by positivity)
    _ ≤ 1 / 2 * θ ^ β * scalarRms volume (ball 0 r) v +
          1 / 2 * θ ^ β * scalarRms volume (ball 0 r) v := by
        rw [← mul_assoc]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hs2 hv0)
    _ = θ ^ β * scalarRms volume (ball 0 r) v := by ring

theorem pow_mul_rpow_le_rpow {θ T γ : ℝ} (hθ0 : 0 < θ) (hT0 : 0 ≤ T) (hγ0 : 0 < γ) (k i : ℕ)
    (hi : θ ^ i ≤ T) : (θ ^ k) ^ i * (θ ^ γ) ^ i ≤ T ^ ((k : ℝ) + γ) := by
  have e : (θ ^ k) ^ i * (θ ^ γ) ^ i = (θ ^ i) ^ k * (θ ^ i) ^ γ := by
    rw [← pow_mul, mul_comm k i, pow_mul, ← Real.rpow_natCast (θ ^ γ) i,
      ← Real.rpow_mul hθ0.le, ← Real.rpow_natCast θ i, ← Real.rpow_mul hθ0.le, mul_comm γ]
  rw [e, Real.rpow_add' hT0 (add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) hγ0).ne',
    Real.rpow_natCast]
  exact mul_le_mul (pow_le_pow_left₀ (by positivity) hi k)
    (Real.rpow_le_rpow (by positivity) hi hγ0.le) (by positivity) (pow_nonneg hT0 k)

/-- The bound of one correction `φ_m = u_m - u_{m+1}` of (3.48) on `B_r`, `r ≥ θ^{m+1} R`. -/
theorem scalarRms_correction_le {θ R r r₀ Cg ρ U : ℝ} {k m : ℕ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hR0 : 0 < R) (hr₀ : 0 < r₀) (hCg : 0 ≤ Cg) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hU : 0 ≤ U)
    {um um1 φ : Vec d → ℝ} (eφ : φ = fun x => um x - um1 x)
    (hmem_m : MemLp um 2 (volume.restrict (ball (0 : Vec d) (θ ^ m * R))))
    (hmem_m1 : MemLp um1 2 (volume.restrict (ball (0 : Vec d) (θ ^ (m + 1) * R))))
    (hm1 : scalarRms volume (ball 0 (θ ^ m * R)) um ≤ (θ ^ k) ^ m * ρ ^ m * U)
    (hm2 : scalarRms volume (ball 0 (θ ^ (m + 1) * R)) um1 ≤
      (θ ^ k) ^ (m + 1) * ρ ^ (m + 1) * U)
    (hg : ∀ t s : ℝ, r₀ ≤ t → t ≤ s →
      scalarRms volume (ball 0 s) φ ≤ Cg * (s / t) ^ k * scalarRms volume (ball 0 t) φ)
    (ht1 : r₀ ≤ θ ^ (m + 1) * R) (ht2 : θ ^ (m + 1) * R ≤ r) :
    scalarRms volume (ball 0 r) φ ≤
      Cg * (Real.sqrt ((1 / θ) ^ d) + 1) * (r / (θ * R)) ^ k * ρ ^ m * U := by
  have hpos1 : 0 < θ ^ (m + 1) * R := lt_of_lt_of_le hr₀ ht1
  have hle : θ ^ (m + 1) * R ≤ θ ^ m * R := by
    have : θ ^ (m + 1) ≤ θ ^ m := pow_le_pow_of_le_one hθ0.le hθ1.le (Nat.le_succ m)
    nlinarith
  have hsq : 0 ≤ Real.sqrt ((1 / θ) ^ d) := Real.sqrt_nonneg _
  have hb1 := scalarRms_ball_le hpos1 hle hmem_m
  rw [show θ ^ m * R / (θ ^ (m + 1) * R) = 1 / θ by rw [pow_succ]; field_simp] at hb1
  have hθk1 : θ ^ k ≤ 1 := pow_le_one₀ hθ0.le hθ1.le
  have hρm : ρ ^ (m + 1) ≤ ρ ^ m := pow_le_pow_of_le_one hρ0 hρ1 (Nat.le_succ m)
  have hkm : (θ ^ k) ^ (m + 1) ≤ (θ ^ k) ^ m :=
    pow_le_pow_of_le_one (by positivity) hθk1 (Nat.le_succ m)
  have hm2' : scalarRms volume (ball 0 (θ ^ (m + 1) * R)) um1 ≤ (θ ^ k) ^ m * ρ ^ m * U :=
    hm2.trans (mul_le_mul_of_nonneg_right (mul_le_mul hkm hρm (by positivity) (by positivity)) hU)
  have hum : MemLp um 2 (volume.restrict (ball (0 : Vec d) (θ ^ (m + 1) * R))) :=
    hmem_m.mono_measure (Measure.restrict_mono (ball_zero_subset_ball_zero hle) le_rfl)
  have hΦm : scalarRms volume (ball 0 (θ ^ (m + 1) * R)) φ ≤
      (Real.sqrt ((1 / θ) ^ d) + 1) * ((θ ^ k) ^ m * ρ ^ m) * U := by
    rw [eφ]
    refine (scalarRms_sub_le hum hmem_m1).trans ?_
    calc _ ≤ Real.sqrt ((1 / θ) ^ d) * ((θ ^ k) ^ m * ρ ^ m * U) + (θ ^ k) ^ m * ρ ^ m * U :=
          add_le_add (hb1.trans (mul_le_mul_of_nonneg_left hm1 hsq)) hm2'
      _ = _ := by ring
  have hratio : (r / (θ ^ (m + 1) * R)) ^ k * (θ ^ k) ^ m = (r / (θ * R)) ^ k := by
    rw [← pow_mul, mul_comm k m, pow_mul, ← mul_pow]
    congr 1
    rw [pow_succ]
    field_simp
  calc scalarRms volume (ball 0 r) φ
      ≤ Cg * (r / (θ ^ (m + 1) * R)) ^ k *
          ((Real.sqrt ((1 / θ) ^ d) + 1) * ((θ ^ k) ^ m * ρ ^ m) * U) :=
        (hg _ _ ht1 ht2).trans (mul_le_mul_of_nonneg_left hΦm
          (mul_nonneg hCg (pow_nonneg (div_nonneg (hpos1.le.trans ht2) hpos1.le) k)))
    _ = Cg * (Real.sqrt ((1 / θ) ^ d) + 1) * ((r / (θ ^ (m + 1) * R)) ^ k * (θ ^ k) ^ m) *
          ρ ^ m * U := by ring
    _ = _ := by rw [hratio]

/-- The main term of (3.48): `‖u_j‖_{L̲²(B_r)} ≤ θ^{-d/2} (r/(θR))^{k+γ} U` for
`θ^{j+1} R < r ≤ θ^j R` and `‖u_j‖_{L̲²(B_{θ^j R})} ≤ (θ^k ρ)^j U`, `ρ = θ^γ`. -/
theorem scalarRms_main_term_le {θ R r γ U : ℝ} {k j : ℕ} (hθ0 : 0 < θ) (hR0 : 0 < R)
    (hr0 : 0 < r) (hγ0 : 0 < γ) (hU : 0 ≤ U) (hjspec : θ ^ (j + 1) * R < r) (hjup : r ≤ θ ^ j * R)
    {uj : Vec d → ℝ} (hmem : MemLp uj 2 (volume.restrict (ball (0 : Vec d) (θ ^ j * R))))
    (hb : scalarRms volume (ball 0 (θ ^ j * R)) uj ≤ (θ ^ k) ^ j * (θ ^ γ) ^ j * U) :
    scalarRms volume (ball 0 r) uj ≤
      Real.sqrt ((1 / θ) ^ d) * (r / (θ * R)) ^ ((k : ℝ) + γ) * U := by
  have hT0 : 0 ≤ r / (θ * R) := by positivity
  have hθjT : θ ^ j ≤ r / (θ * R) := by
    rw [le_div_iff₀ (by positivity)]
    rw [pow_succ] at hjspec
    nlinarith
  have h1 := scalarRms_ball_le hr0 hjup hmem
  have hratio : θ ^ j * R / r ≤ 1 / θ := by
    rw [div_le_div_iff₀ hr0 hθ0]
    rw [pow_succ] at hjspec
    nlinarith
  have h2 : Real.sqrt ((θ ^ j * R / r) ^ d) ≤ Real.sqrt ((1 / θ) ^ d) :=
    Real.sqrt_le_sqrt (pow_le_pow_left₀ (by positivity) hratio d)
  have hsq : 0 ≤ Real.sqrt ((1 / θ) ^ d) := Real.sqrt_nonneg _
  calc scalarRms volume (ball 0 r) uj
      ≤ Real.sqrt ((θ ^ j * R / r) ^ d) * scalarRms volume (ball 0 (θ ^ j * R)) uj := h1
    _ ≤ Real.sqrt ((1 / θ) ^ d) * ((θ ^ k) ^ j * (θ ^ γ) ^ j * U) :=
        mul_le_mul h2 hb (scalarRms_nonneg _ _) hsq
    _ ≤ Real.sqrt ((1 / θ) ^ d) * ((r / (θ * R)) ^ ((k : ℝ) + γ) * U) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (pow_mul_rpow_le_rpow hθ0 hT0 hγ0 k j hθjT) hU) hsq
    _ = _ := by ring

set_option maxHeartbeats 400000 in
/-- **The implication (3.48)**, deterministic form: for one coefficient field `a`, the estimate
(3.50) above the scale `r₀` and `(ii)_k` with `r₀` large give `(iii')_k`: every solution `u` in `B_R`,
`R ≥ r₀`, has some `φ ∈ A_k` with `‖u - φ‖_{L̲²(B_r)} ≤ C (r/R)^{k+1-δ/2} ‖u‖_{L̲²(B_R)}` for every
`r ∈ [r₀, R]`, with `C(θ, δ, k, d)`. -/
theorem implication_348 (k : ℕ) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ (a : CoefficientField d Λ) (A : Mat d) (r₀ θ δ C₅₀ C₂ : ℝ),
      0 < r₀ → 0 < θ → θ < 1 → 0 < δ → δ ≤ 1 → 0 ≤ C₂ →
      (∀ r : ℝ, r₀ ≤ r → ∀ v, IsSolutionBall a r v →
        harmonicFlatness A k v (θ * r) ≤
          1 / 4 * θ ^ ((k : ℝ) + 1 - δ / 2) * harmonicFlatness A k v r +
            C₅₀ * r ^ (-δ) * scalarRms volume (ball 0 r) v) →
      (∀ p ∈ harmonicPolys A k, ∃ φ ∈ solutionGrowthSpace a k, ∀ s : ℝ, r₀ ≤ s →
        scalarRms volume (ball 0 s) (fun x => φ x - p x) ≤
          C₂ * s ^ (-δ) * scalarRms volume (ball 0 s) p) →
      C₅₀ * r₀ ^ (-δ) ≤ 1 / 8 * θ ^ ((k : ℝ) + 1 - δ / 2) →
      C₂ * r₀ ^ (-δ) * (Real.sqrt ((1 / θ) ^ d) + 1) ≤ 1 / 2 * θ ^ ((k : ℝ) + 1 - δ / 2) →
      C₂ * r₀ ^ (-δ) ≤ 1 / 2 →
      ∀ R : ℝ, r₀ ≤ R → ∀ u, IsSolutionBall a R u → ∃ φ ∈ solutionGrowthSpace a k,
        ∀ r : ℝ, r₀ ≤ r → r ≤ R →
          scalarRms volume (ball 0 r) (fun x => u x - φ x) ≤
            (Real.sqrt ((1 / θ) ^ d) + Cg * (Real.sqrt ((1 / θ) ^ d) + 1) /
              (1 - θ ^ (1 - δ / 2))) * θ ^ (-((k : ℝ) + 1 - δ / 2)) *
              (r / R) ^ ((k : ℝ) + 1 - δ / 2) * scalarRms volume (ball 0 R) u := by
  obtain ⟨Cg, hCg, hstep⟩ := exists_correction_step (d := d) (Λ := Λ) k
  refine ⟨Cg, hCg, ?_⟩
  intro a A r₀ θ δ C₅₀ C₂ hr₀ hθ0 hθ1 hδ hδ1 hC₂ H50 Hii hs50 hs2 hs2' R hR u hu
  have hR0 : 0 < R := lt_of_lt_of_le hr₀ hR
  have hstep' := hstep a A r₀ θ δ C₅₀ C₂ hr₀ hθ0 hθ1 hδ hδ1 hC₂ H50 Hii hs50 hs2 hs2'
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = 1 - δ / 2 := ⟨_, rfl⟩
  have hβγ : (k : ℝ) + 1 - δ / 2 = k + γ := by rw [hγ]; ring
  rw [hβγ] at hstep' ⊢
  rw [← hγ]
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = θ ^ γ := ⟨_, rfl⟩
  have hρ0 : 0 ≤ ρ := by rw [hρ]; exact (Real.rpow_pos_of_pos hθ0 γ).le
  have hρ1 : ρ < 1 := by rw [hρ]; exact Real.rpow_lt_one hθ0.le hθ1 hγ0
  have hq : θ ^ ((k : ℝ) + γ) = θ ^ k * ρ := by
    rw [Real.rpow_add hθ0, Real.rpow_natCast, hρ]
  have hex : ∃ n : ℕ, θ ^ (n + 1) * R < r₀ := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hr₀ hR0) hθ1
    refine ⟨n, ?_⟩
    have : θ ^ (n + 1) ≤ θ ^ n := pow_le_pow_of_le_one hθ0.le hθ1.le (Nat.le_succ n)
    rw [lt_div_iff₀ hR0] at hn
    nlinarith [hR0]
  classical
  obtain ⟨N, hN⟩ : ∃ N, N = Nat.find hex := ⟨_, rfl⟩
  have hNspec : θ ^ (N + 1) * R < r₀ := by rw [hN]; exact Nat.find_spec hex
  have hNmin : ∀ m < N, r₀ ≤ θ ^ (m + 1) * R := fun m hm => by
    rw [hN] at hm; exact not_lt.1 (Nat.find_min hex hm)
  obtain ⟨Φ, hΦ, hb⟩ := exists_correction_iteration (a := a) (k := k)
    (fun φ => φ ∈ solutionGrowthSpace a k ∧ ∀ t s : ℝ, r₀ ≤ t → t ≤ s →
      scalarRms volume (ball 0 s) φ ≤ Cg * (s / t) ^ k * scalarRms volume (ball 0 t) φ)
    (fun φ hφ => hφ.1) hθ0 hθ1.le hR0 (Real.rpow_pos_of_pos hθ0 _).le hu N
    (fun j hj v hv => by
      have h := hstep' (θ ^ j * R) (by rw [← mul_assoc, ← pow_succ']; exact hNmin j hj) v hv
      rwa [← mul_assoc, ← pow_succ'] at h)
  simp only [hq, mul_pow] at hb
  have hU := scalarRms_nonneg (d := d) (ball 0 R) u
  have hsolj : ∀ j ≤ N, ∀ t : ℝ, 0 < t → t ≤ R →
      IsSolutionBall a t (fun x => u x - ∑ m ∈ Finset.range j, Φ m x) := fun j hj t ht htR =>
    (hu.mono htR).sub (isSolutionBall_of_mem_solutionGrowthSpace (sum_mem_solutionGrowthSpace _
      fun m hm => (hΦ m (by have := Finset.mem_range.1 hm; omega)).1) ht)
  have hθle : ∀ i : ℕ, θ ^ i * R ≤ R := fun i => by
    have : θ ^ i ≤ 1 := pow_le_one₀ hθ0.le hθ1.le
    nlinarith
  refine ⟨fun x => ∑ m ∈ Finset.range N, Φ m x,
    sum_mem_solutionGrowthSpace _ fun m hm => (hΦ m (Finset.mem_range.1 hm)).1, ?_⟩
  intro r hr₀r hrR
  have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr₀r
  have hexj : ∃ j : ℕ, θ ^ (j + 1) * R < r := ⟨N, lt_of_lt_of_le hNspec hr₀r⟩
  obtain ⟨j, hj⟩ : ∃ j, j = Nat.find hexj := ⟨_, rfl⟩
  have hjspec : θ ^ (j + 1) * R < r := by rw [hj]; exact Nat.find_spec hexj
  have hjN : j ≤ N := by rw [hj]; exact Nat.find_min' hexj (lt_of_lt_of_le hNspec hr₀r)
  have hjup : r ≤ θ ^ j * R := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0, pow_zero, one_mul]; exact hrR
    · have h := Nat.find_min hexj (show j - 1 < Nat.find hexj by rw [← hj]; omega)
      rw [not_lt, show j - 1 + 1 = j by omega] at h
      exact h
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = r / (θ * R) := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hsq : 0 ≤ Real.sqrt ((1 / θ) ^ d) := Real.sqrt_nonneg _
  have hmain := scalarRms_main_term_le (k := k) hθ0 hR0 hr0 hγ0 hU hjspec hjup
    (hsolj j hjN _ (by positivity) (hθle j)).1 (by rw [← hρ]; exact hb j hjN)
  rw [← hT] at hmain
  have htail : ∀ m ∈ Finset.Ico j N, scalarRms volume (ball 0 r) (Φ m) ≤
      Cg * (Real.sqrt ((1 / θ) ^ d) + 1) * T ^ k * ρ ^ m * scalarRms volume (ball 0 R) u := by
    intro m hm
    obtain ⟨hjm, hmN⟩ := Finset.mem_Ico.1 hm
    have ht1 : r₀ ≤ θ ^ (m + 1) * R := hNmin m hmN
    have ht2 : θ ^ (m + 1) * R ≤ r := by
      have : θ ^ (m + 1) ≤ θ ^ (j + 1) := pow_le_pow_of_le_one hθ0.le hθ1.le (by omega)
      nlinarith
    rw [hT]
    refine scalarRms_correction_le hθ0 hθ1 hR0 hr₀ hCg hρ0 hρ1.le hU
      (um := fun x => u x - ∑ i ∈ Finset.range m, Φ i x)
      (um1 := fun x => u x - ∑ i ∈ Finset.range (m + 1), Φ i x)
      (by funext x; rw [Finset.sum_range_succ]; ring)
      (hsolj m (by omega) _ (by positivity) (hθle m)).1
      (hsolj (m + 1) (by omega) _ (by positivity) (hθle (m + 1))).1
      (hb m (by omega)) (hb (m + 1) (by omega)) (hΦ m hmN).2 ht1 ht2
  have hmemr : ∀ m, MemLp (if m < N then Φ m else fun _ => (0 : ℝ)) 2
      (volume.restrict (ball (0 : Vec d) r)) := fun m => by
    by_cases h : m < N
    · simp only [h, if_true]; exact ((hΦ m h).1.1 r hr0).1
    · simp only [h, if_false]; exact MemLp.zero
  have hS := scalarRms_finset_sum_le (Finset.Ico j N) hmemr (fun _ => (1 : ℝ))
  have e1 : (fun x => ∑ m ∈ Finset.Ico j N, (1 : ℝ) * (if m < N then Φ m else fun _ => 0) x) =
      fun x => ∑ m ∈ Finset.Ico j N, Φ m x := by
    funext x
    refine Finset.sum_congr rfl fun m hm => ?_
    simp only [(Finset.mem_Ico.1 hm).2, if_true, one_mul]
  have e2 : ∀ m ∈ Finset.Ico j N, |(1 : ℝ)| * scalarRms volume (ball 0 r)
      (if m < N then Φ m else fun _ => 0) = scalarRms volume (ball 0 r) (Φ m) := fun m hm => by
    simp only [abs_one, one_mul, (Finset.mem_Ico.1 hm).2, if_true]
  rw [e1, Finset.sum_congr rfl e2] at hS
  have hsumb : scalarRms volume (ball 0 r) (fun x => ∑ m ∈ Finset.Ico j N, Φ m x) ≤
      Cg * (Real.sqrt ((1 / θ) ^ d) + 1) * T ^ k * (ρ ^ j / (1 - ρ)) *
        scalarRms volume (ball 0 R) u := by
    calc _ ≤ ∑ m ∈ Finset.Ico j N, scalarRms volume (ball 0 r) (Φ m) := hS
      _ ≤ ∑ m ∈ Finset.Ico j N, Cg * (Real.sqrt ((1 / θ) ^ d) + 1) * T ^ k * ρ ^ m *
            scalarRms volume (ball 0 R) u := Finset.sum_le_sum htail
      _ = Cg * (Real.sqrt ((1 / θ) ^ d) + 1) * T ^ k * (∑ m ∈ Finset.Ico j N, ρ ^ m) *
            scalarRms volume (ball 0 R) u := by
          rw [Finset.mul_sum, Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (geom_sum_Ico_le_of_lt_one hρ0 hρ1) (by positivity)) hU
  have hθjT : θ ^ j ≤ T := by
    rw [hT, le_div_iff₀ (by positivity)]
    rw [pow_succ] at hjspec
    nlinarith
  have hρj : T ^ k * ρ ^ j ≤ T ^ ((k : ℝ) + γ) := by
    have e : ρ ^ j = (θ ^ j) ^ γ := by
      rw [hρ, ← Real.rpow_natCast (θ ^ γ) j, ← Real.rpow_mul hθ0.le, ← Real.rpow_natCast θ j,
        ← Real.rpow_mul hθ0.le, mul_comm γ]
    rw [e, Real.rpow_add' hT0 (add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) hγ0).ne',
      Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hθjT hγ0.le)
      (pow_nonneg hT0 k)
  have hTβ : T ^ ((k : ℝ) + γ) = θ ^ (-((k : ℝ) + γ)) * (r / R) ^ ((k : ℝ) + γ) := by
    rw [hT, show r / (θ * R) = (r / R) / θ by field_simp, Real.div_rpow (by positivity) hθ0.le,
      Real.rpow_neg hθ0.le]
    ring
  have h1ρ : 0 < 1 - ρ := by linarith
  have hsplit : (fun x => u x - ∑ m ∈ Finset.range N, Φ m x) =
      fun x => (u x - ∑ m ∈ Finset.range j, Φ m x) - ∑ m ∈ Finset.Ico j N, Φ m x := by
    funext x
    rw [← Finset.sum_range_add_sum_Ico _ hjN]
    ring
  have hmemj := (hsolj j hjN r hr0 hrR).1
  have hmemsum : MemLp (fun x => ∑ m ∈ Finset.Ico j N, Φ m x) 2
      (volume.restrict (ball (0 : Vec d) r)) :=
    (isSolutionBall_of_mem_solutionGrowthSpace (sum_mem_solutionGrowthSpace _
      fun m hm => (hΦ m (Finset.mem_Ico.1 hm).2).1) hr0).1
  rw [hsplit, ← hρ]
  have hCgs : 0 ≤ Cg * (Real.sqrt ((1 / θ) ^ d) + 1) := by positivity
  calc scalarRms volume (ball 0 r) (fun x => (u x - ∑ m ∈ Finset.range j, Φ m x) -
        ∑ m ∈ Finset.Ico j N, Φ m x)
      ≤ Real.sqrt ((1 / θ) ^ d) * T ^ ((k : ℝ) + γ) * scalarRms volume (ball 0 R) u +
          Cg * (Real.sqrt ((1 / θ) ^ d) + 1) * T ^ k * (ρ ^ j / (1 - ρ)) *
            scalarRms volume (ball 0 R) u :=
        (scalarRms_sub_le hmemj hmemsum).trans (add_le_add hmain hsumb)
    _ ≤ Real.sqrt ((1 / θ) ^ d) * T ^ ((k : ℝ) + γ) * scalarRms volume (ball 0 R) u +
          Cg * (Real.sqrt ((1 / θ) ^ d) + 1) * (T ^ ((k : ℝ) + γ) / (1 - ρ)) *
            scalarRms volume (ball 0 R) u := by
        refine add_le_add le_rfl (mul_le_mul_of_nonneg_right ?_ hU)
        rw [mul_assoc (Cg * _), mul_div_assoc']
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hρj h1ρ.le) hCgs
    _ = _ := by
        rw [hTβ]
        field_simp

end QSH
