import QuantitativeStochasticHomogenization.Ch03.Sec02.Theorem33
import QuantitativeStochasticHomogenization.Ch03.Sec02.HarmonicGrowth

/-!
# Theorem 3.8 for `k = 0`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 3.3: "Theorem 3.3 is actually the base case" of Theorem 3.8. `solutionGrowthSpace a k` is the
space `A_k` of (3.38) for one coefficient field. For `d ≥ 2`, `Λ > 1` and `s ∈ (0, d)`, with the
random scale of Theorem 3.3 (`theorem_3_8_zero`):

* (i)₀ every `u ∈ A_0` agrees almost everywhere with a constant, an element of `Ā_0`, so (3.40)
  holds with any exponent;
* (ii)₀ `Ā_0 ⊆ A_0`;
* (iii)₀ for `R ≥ X_s` and a solution `u` in `B_R` there is a constant `φ ∈ A_0` with
  `‖u - φ‖_{L̲²(B_r)} ≤ C (r/R) ‖u‖_{L̲²(B_R)}` for every `r ∈ [X_s, R]`, (3.41) for `k = 0`.

The constant of (iii)₀ is `(u)_{B_{X_s}}`; the averages on `B_{X_s}` and `B_r` are compared with
(3.17) as in the proof of (3.18) (`scalarRms_sub_setAverage_scale_le`).
-/

open MeasureTheory Filter Set Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The space `A_k` of (3.38) for one coefficient field: the weak solutions of `-∇·(a∇u) = 0` on
`ℝ^d` (in `H¹(B_R)` for every `R`) with `r^{-(k+1)} ‖u‖_{L̲²(B_r)} → 0`. -/
def solutionGrowthSpace {Λ : ℝ} (a : CoefficientField d Λ) (k : ℕ) : Set (Vec d → ℝ) :=
  {u | (∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)) ∧ ∃ g : Vec d → Vec d,
      (∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 R))) ∧
      HasWeakGradient (ball 0 R) u g ∧
      HasWeakDivergence (ball 0 R) (fun x => (a x).mulVec (g x)) (fun _ => 0)) ∧
    Tendsto (fun r : ℝ => (r ^ (k + 1))⁻¹ * scalarRms volume (ball 0 r) u) atTop (𝓝 0)}

theorem ae_eq_zero_of_scalarRms_eq_zero {r : ℝ} (hr : 0 < r) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (ball (0 : Vec d) r)))
    (h0 : scalarRms volume (ball 0 r) f = 0) :
    ∀ᵐ x ∂(volume.restrict (ball (0 : Vec d) r)), f x = 0 := by
  have hv : 0 < volume.real (ball (0 : Vec d) r) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (volume_ball_ne_zero' 0 hr) (volume_ball_ne_top' 0 r)
  unfold scalarRms at h0
  rw [Real.sqrt_eq_zero', setAverage_eq, smul_eq_mul] at h0
  have hI0 : 0 ≤ ∫ x in ball (0 : Vec d) r, f x ^ 2 :=
    setIntegral_nonneg (measurableSet_ball' 0 r) fun x _ => sq_nonneg _
  have hI : ∫ x in ball (0 : Vec d) r, f x ^ 2 = 0 := by
    refine le_antisymm ?_ hI0
    have h1 : (volume.real (ball (0 : Vec d) r))⁻¹ * ∫ x in ball (0 : Vec d) r, f x ^ 2 ≤
        (volume.real (ball (0 : Vec d) r))⁻¹ * 0 := by rw [mul_zero]; exact h0
    exact le_of_mul_le_mul_left h1 (inv_pos.2 hv)
  have h2 := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (f x)) hf.integrable_sq).1 hI
  filter_upwards [h2] with x hx
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hx

/-- (3.41) for `k = 0` from (3.17): with `c = (u)_{B_X}`,
`‖u - c‖_{L̲²(B_r)} ≤ C (1 + 3 · 2^{d/2}) (r/R) ‖u‖_{L̲²(B_R)}` for `r ∈ [X, R]`. -/
theorem scalarRms_sub_setAverage_scale_le {X R C : ℝ} (hX : 0 < X) (hC : 0 ≤ C) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (ball (0 : Vec d) R)))
    (h317 : ∀ r : ℝ, X ≤ r → r ≤ R →
      1 / r * scalarRms volume (ball 0 r) (fun x => u x - ⨍ y in ball 0 r, u y) ≤
        C / R * scalarRms volume (ball 0 R) (fun x => u x - ⨍ y in ball 0 R, u y))
    {r : ℝ} (hXr : X ≤ r) (hrR : r ≤ R) :
    scalarRms volume (ball 0 r) (fun x => u x - ⨍ y in ball 0 X, u y) ≤
      C * (1 + 3 * Real.sqrt (2 ^ d)) * (r / R) * scalarRms volume (ball 0 R) u := by
  have hr : 0 < r := lt_of_lt_of_le hX hXr
  have hR : 0 < R := lt_of_lt_of_le hr hrR
  obtain ⟨oR, hoR⟩ : ∃ o : ℝ,
      o = scalarRms volume (ball 0 R) (fun x => u x - ⨍ y in ball 0 R, u y) := ⟨_, rfl⟩
  rw [← hoR] at h317
  have hoR0 : 0 ≤ oR := by rw [hoR]; exact scalarRms_nonneg _ _
  have hoRu : oR ≤ scalarRms volume (ball 0 R) u := by
    rw [hoR]
    refine (scalarRms_sub_setAverage_le_sub_const (volume_ball_ne_top' 0 R) hu 0).trans ?_
    simp only [sub_zero, le_refl]
  have hur : MemLp u 2 (volume.restrict (ball (0 : Vec d) r)) :=
    hu.mono_measure (Measure.restrict_mono (ball_zero_subset_ball_zero hrR) le_rfl)
  have hosc : ∀ ρ : ℝ, X ≤ ρ → ρ ≤ R →
      scalarRms volume (ball 0 ρ) (fun x => u x - ⨍ y in ball 0 ρ, u y) ≤ ρ / R * (C * oR) := by
    intro ρ h1 h2
    have hρ : 0 < ρ := lt_of_lt_of_le hX h1
    have h := h317 ρ h1 h2
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hρ] at h
    calc _ ≤ C / R * oR * ρ := h
      _ = ρ / R * (C * oR) := by ring
  have hdec : ∀ ρ : ℝ, X ≤ ρ → ρ ≤ r →
      scalarRms volume (ball 0 ρ) (fun x => u x - ⨍ y in ball 0 ρ, u y) ≤
        ρ / r * (r / R * (C * oR)) := fun ρ h1 h2 => by
    refine (hosc ρ h1 (h2.trans hrR)).trans (le_of_eq ?_)
    field_simp
  have havg := abs_setAverage_ball_sub_le_of_decay hX hur hdec le_rfl hXr
  have hsplit : scalarRms volume (ball 0 r) (fun x => u x - ⨍ y in ball 0 X, u y) ≤
      scalarRms volume (ball 0 r) (fun x => u x - ⨍ y in ball 0 r, u y) +
        |(⨍ y in ball 0 r, u y) - ⨍ y in ball 0 X, u y| := by
    have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) r)) :=
      isFiniteMeasure_restrict.mpr (volume_ball_ne_top' 0 r)
    have h := scalarRms_add_le (f := fun x => u x - ⨍ y in ball 0 r, u y)
      (g := fun _ => (⨍ y in ball 0 r, u y) - ⨍ y in ball 0 X, u y)
      (hur.sub (memLp_const _)) (memLp_const _)
    rw [scalarRms_const_ball hr] at h
    simpa only [sub_add_sub_cancel] using h
  rw [abs_sub_comm] at havg
  have hK : 0 ≤ Real.sqrt (2 ^ d) := Real.sqrt_nonneg _
  have hrR1 : 0 ≤ r / R := by positivity
  calc scalarRms volume (ball 0 r) (fun x => u x - ⨍ y in ball 0 X, u y)
      ≤ r / R * (C * oR) + 3 * Real.sqrt (2 ^ d) * (r / R * (C * oR)) :=
        hsplit.trans (add_le_add (hosc r hXr hrR) havg)
    _ = C * (1 + 3 * Real.sqrt (2 ^ d)) * (r / R) * oR := by ring
    _ ≤ C * (1 + 3 * Real.sqrt (2 ^ d)) * (r / R) * scalarRms volume (ball 0 R) u :=
        mul_le_mul_of_nonneg_left hoRu (by positivity)

theorem const_mem_harmonicPolys (A : Mat d) (k : ℕ) (c : ℝ) :
    (fun _ => c) ∈ harmonicPolys A k := by
  refine ⟨⟨MvPolynomial.C c, by simp, fun x => by simp⟩, fun ρ _ => ?_⟩
  have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) ρ)) :=
    isFiniteMeasure_restrict.mpr (volume_ball_ne_top' 0 ρ)
  refine ⟨memLp_const c, fun _ => 0, fun _ => MemLp.zero,
    hasWeakGradient_mono (subset_univ _) (hasWeakGradient_const c), ?_⟩
  simpa only [Matrix.mulVec_zero] using
    (hasWeakDivergence_const_field (0 : Vec d)).mono' (subset_univ (ball (0 : Vec d) ρ))

theorem const_mem_solutionGrowthSpace {Λ : ℝ} (a : CoefficientField d Λ) (c : ℝ) :
    (fun _ => c) ∈ solutionGrowthSpace a 0 := by
  refine ⟨fun R _ => ?_, ?_⟩
  · have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
      isFiniteMeasure_restrict.mpr (volume_ball_ne_top' 0 R)
    refine ⟨memLp_const c, fun _ => 0, fun _ => MemLp.zero,
      hasWeakGradient_mono (subset_univ _) (hasWeakGradient_const c), ?_⟩
    simpa only [Matrix.mulVec_zero] using
      (hasWeakDivergence_const_field (0 : Vec d)).mono' (subset_univ (ball (0 : Vec d) R))
  · have h : Tendsto (fun r : ℝ => r⁻¹ * |c|) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.mul_const |c|
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with r hr
    rw [scalarRms_const_ball hr, zero_add, pow_one]

/-- **Theorem 3.8 for `k = 0`**, for `d ≥ 2` and `Λ > 1` (the hypotheses of Theorem 3.3), with the
random scale of Theorem 3.3: (i)₀, (ii)₀ and (iii)₀. -/
theorem theorem_3_8_zero (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) {s : ℝ} (hs : 0 < s) (hsd : s < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∃ X : CoefficientField d Λ → ℝ, OsBound P X s C ∧ (∀ a, 1 ≤ X a) ∧ ∀ᵐ a ∂P,
        (∀ u ∈ solutionGrowthSpace a 0, ∃ p ∈ harmonicPolys (homogenizedMatrix P) 0,
          ∀ᵐ x ∂(volume : Measure (Vec d)), u x = p x) ∧
        harmonicPolys (homogenizedMatrix P) 0 ⊆ solutionGrowthSpace a 0 ∧
        ∀ R : ℝ, X a ≤ R → ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
          MemLp u 2 (volume.restrict (ball 0 R)) →
          (∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 R))) →
          HasWeakGradient (ball 0 R) u g →
          HasWeakDivergence (ball 0 R) (fun x => (a x).mulVec (g x)) (fun _ => 0) →
          ∃ φ ∈ solutionGrowthSpace a 0, ∀ r : ℝ, X a ≤ r → r ≤ R →
            scalarRms volume (ball 0 r) (fun x => u x - φ x) ≤
              C * (r / R) * scalarRms volume (ball 0 R) u := by
  obtain ⟨C₃, hC₃, h33⟩ := theorem_3_3 hd hΛ hs hsd
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = C₃ * (1 + 3 * Real.sqrt (2 ^ d)) := ⟨_, rfl⟩
  have hK : 0 ≤ Real.sqrt (2 ^ d) := Real.sqrt_nonneg _
  have hC₃C : C₃ ≤ C := by
    rw [hC]; nlinarith
  have hC0 : 0 < C := lt_of_lt_of_le hC₃ hC₃C
  refine ⟨C, hC0, fun P hP => ?_⟩
  obtain ⟨X, hXos, hX1, hXae⟩ := h33 P hP
  refine ⟨X, hXos.mono_scale hC₃C, hX1, ?_⟩
  filter_upwards [hXae] with a ha
  have hX0 : 0 < X a := lt_of_lt_of_le one_pos (hX1 a)
  -- (3.41) for `k = 0` with the constant `(u)_{B_X}`
  have h341 : ∀ R : ℝ, X a ≤ R → ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
      MemLp u 2 (volume.restrict (ball 0 R)) →
      (∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 R))) →
      HasWeakGradient (ball 0 R) u g →
      HasWeakDivergence (ball 0 R) (fun x => (a x).mulVec (g x)) (fun _ => 0) →
      ∀ r : ℝ, X a ≤ r → r ≤ R →
        scalarRms volume (ball 0 r) (fun x => u x - ⨍ y in ball 0 (X a), u y) ≤
          C * (r / R) * scalarRms volume (ball 0 R) u := by
    intro R hXR u g hu hg hug hdiv r hXr hrR
    have h := scalarRms_sub_setAverage_scale_le hX0 hC₃.le hu
      (fun ρ h1 h2 => (ha R hXR u g hu hg hug hdiv ρ h1 h2).1) hXr hrR
    rwa [← hC] at h
  refine ⟨fun u hu => ?_, fun p hp => ?_, fun R hXR u g hu hg hug hdiv =>
    ⟨fun _ => ⨍ y in ball 0 (X a), u y, const_mem_solutionGrowthSpace a _,
      h341 R hXR u g hu hg hug hdiv⟩⟩
  · obtain ⟨hu1, hgrow⟩ := hu
    refine ⟨fun _ => ⨍ y in ball 0 (X a), u y, const_mem_harmonicPolys _ 0 _, ?_⟩
    have hzero : ∀ r : ℝ, X a ≤ r →
        scalarRms volume (ball 0 r) (fun x => u x - ⨍ y in ball 0 (X a), u y) = 0 := by
      intro r hXr
      have hr : 0 < r := lt_of_lt_of_le hX0 hXr
      have hlim : Tendsto (fun R : ℝ => C * r * ((R ^ (0 + 1))⁻¹ * scalarRms volume (ball 0 R) u))
          atTop (𝓝 0) := by simpa using hgrow.const_mul (C * r)
      refine le_antisymm (ge_of_tendsto hlim ?_) (scalarRms_nonneg _ _)
      filter_upwards [eventually_ge_atTop r] with R hrR
      have hR : 0 < R := lt_of_lt_of_le hr hrR
      obtain ⟨huR, g, hg, hug, hdiv⟩ := hu1 R hR
      refine (h341 R (hXr.trans hrR) u g huR hg hug hdiv r hXr hrR).trans (le_of_eq ?_)
      rw [zero_add, pow_one]
      field_simp
    have hcover : (⋃ n : ℕ, ball (0 : Vec d) (X a + n)) = univ := by
      ext x
      simp only [mem_iUnion, mem_univ, iff_true]
      obtain ⟨n, hn⟩ := exists_nat_gt (euclideanNorm x)
      exact ⟨n, mem_ball_zero_iff'.2 (by linarith)⟩
    suffices hsuf : ∀ᵐ x ∂(volume.restrict (⋃ n : ℕ, ball (0 : Vec d) (X a + n))),
        u x = ⨍ y in ball 0 (X a), u y by
      rwa [hcover, Measure.restrict_univ] at hsuf
    rw [ae_restrict_iUnion_iff]
    intro n
    have hrn : X a ≤ X a + n := le_add_of_nonneg_right (Nat.cast_nonneg n)
    have hpos : 0 < X a + n := lt_of_lt_of_le hX0 hrn
    have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) (X a + n))) :=
      isFiniteMeasure_restrict.mpr (volume_ball_ne_top' 0 _)
    have h0 := ae_eq_zero_of_scalarRms_eq_zero hpos ((hu1 _ hpos).1.sub (memLp_const _))
      (hzero _ hrn)
    filter_upwards [h0] with x hx
    exact sub_eq_zero.1 hx
  · obtain ⟨⟨Q, hQ, hQe⟩, -⟩ := hp
    have hQC : Q = MvPolynomial.C (Q.coeff 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 hQ)
    have e : p = fun _ => Q.coeff 0 := by
      funext x
      rw [hQe x]
      nth_rewrite 1 [hQC]
      exact MvPolynomial.eval_C _
    rw [e]
    exact const_mem_solutionGrowthSpace a _

end QSH
