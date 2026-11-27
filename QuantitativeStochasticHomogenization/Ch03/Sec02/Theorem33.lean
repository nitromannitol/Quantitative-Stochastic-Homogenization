import QuantitativeStochasticHomogenization.Ch03.Sec01.Proposition32
import QuantitativeStochasticHomogenization.Ch03.Sec02.Lemma34
import QuantitativeStochasticHomogenization.Ch01.Sec04.Proposition112

/-!
# Theorem 3.3: the quenched `C^{0,1}`-type estimate

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 3.2, Theorem 3.3, for `d ≥ 2` and `Λ > 1`: for every `s ∈ (0, d)` there is `C(s, d, Λ)` with,
for every law satisfying the assumptions, a random variable `X_s ≥ 1` with `X_s ≤ O_s(C)`, (3.15),
such that for almost every coefficient field, every `R ≥ X_s` and every weak solution
`u ∈ H¹(B_R)` of `-∇·(a∇u) = 0` in `B_R`, (3.16), and every `r ∈ [X_s, R]`,

* (3.17) `r⁻¹ ‖u - (u)_{B_r}‖_{L̲²(B_r)} ≤ C R⁻¹ ‖u - (u)_{B_R}‖_{L̲²(B_R)}`;
* (3.18) `‖u‖_{L̲²(B_r)} ≤ C ‖u‖_{L̲²(B_R)}`.

The proof is the book's: (3.17) is Lemma 3.4 with the harmonic approximation of Proposition 3.2
(`lemma_3_4_halfBall`, since Proposition 3.2 gives the `ā`-harmonic approximation on `B_{r/2}`
only), with `X_s = 2X` for the random variable `X` of Proposition 3.2; (3.18) follows from (3.17)
by comparing the averages of `u` on the balls `B_ρ` and `B_{2ρ}` (`abs_setAverage_ball_sub_le`,
`abs_setAverage_ball_sub_le_of_decay`). As in Proposition 3.2, the statement holds for almost
every coefficient field, `X_s` is real valued, and `u ∈ H¹(B_R)` is given with its weak gradient.
-/

open MeasureTheory Filter Set

noncomputable section

namespace QSH

variable {d : ℕ}

section Theorem33

/-- `|(u)_{B_ρ} - (u)_{B_t}| ≤ (t/ρ)^{d/2} ‖u - (u)_{B_t}‖_{L̲²(B_t)}` for `0 < ρ ≤ t`. -/
theorem abs_setAverage_ball_sub_le {ρ t : ℝ} (hρ : 0 < ρ) (hρt : ρ ≤ t) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (ball (0 : Vec d) t))) :
    |(⨍ x in ball 0 ρ, u x) - ⨍ x in ball 0 t, u x| ≤
      Real.sqrt ((t / ρ) ^ d) *
        scalarRms volume (ball 0 t) (fun x => u x - ⨍ y in ball 0 t, u y) := by
  have huρ : MemLp u 2 (volume.restrict (ball (0 : Vec d) ρ)) :=
    hu.mono_measure (Measure.restrict_mono (ball_zero_subset_ball_zero hρt) le_rfl)
  have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) ρ)) :=
    isFiniteMeasure_restrict.mpr (volume_ball_ne_top' 0 ρ)
  have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) t)) :=
    isFiniteMeasure_restrict.mpr (volume_ball_ne_top' 0 t)
  have e : (⨍ x in ball 0 ρ, u x) - (⨍ x in ball 0 t, u x) =
      ⨍ x in ball 0 ρ, (u x - ⨍ y in ball 0 t, u y) := by
    have h := average_sub (μ := volume.restrict (ball (0 : Vec d) ρ))
      (huρ.integrable one_le_two) (integrable_const (⨍ y in ball 0 t, u y))
    rw [show (⨍ x in ball 0 ρ, (u x - ⨍ y in ball 0 t, u y)) =
        (⨍ x in ball 0 ρ, u x) - ⨍ _ in ball (0 : Vec d) ρ, (⨍ y in ball 0 t, u y) from h,
      setAverage_const (volume_ball_ne_zero' 0 hρ) (volume_ball_ne_top' 0 ρ)]
  rw [e]
  refine (abs_setAverage_le_scalarRms (f := fun x => u x - ⨍ y in ball 0 t, u y)
    (volume_ball_ne_zero' 0 hρ) (volume_ball_ne_top' 0 ρ) (huρ.sub (memLp_const _))).trans ?_
  exact scalarRms_ball_le (f := fun x => u x - ⨍ y in ball 0 t, u y) hρ hρt
    (hu.sub (memLp_const _))

/-- The averages of a function with decaying oscillation: if
`‖u - (u)_{B_ρ}‖_{L̲²(B_ρ)} ≤ (ρ/R) M` for every `ρ ∈ [r, R]`, then
`|(u)_{B_ρ} - (u)_{B_R}| ≤ 3 · 2^{d/2} M` for every `ρ ∈ [r, R]` (Step 3 of the proof of
Lemma 3.4, comparing the averages on `B_ρ` and `B_{2ρ}`). -/
theorem abs_setAverage_ball_sub_le_of_decay {r R M : ℝ} (hr : 0 < r) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (ball (0 : Vec d) R)))
    (hdec : ∀ ρ : ℝ, r ≤ ρ → ρ ≤ R →
      scalarRms volume (ball 0 ρ) (fun x => u x - ⨍ y in ball 0 ρ, u y) ≤ ρ / R * M)
    {ρ : ℝ} (hrρ : r ≤ ρ) (hρR : ρ ≤ R) :
    |(⨍ x in ball 0 ρ, u x) - ⨍ x in ball 0 R, u x| ≤ 3 * Real.sqrt (2 ^ d) * M := by
  have hR : 0 < R := by linarith
  have hM : 0 ≤ M := by
    have h := (scalarRms_nonneg (ball (0 : Vec d) R) _).trans (hdec R (hrρ.trans hρR) le_rfl)
    rwa [div_self hR.ne', one_mul] at h
  have hK : 0 ≤ Real.sqrt (2 ^ d) := Real.sqrt_nonneg _
  have key : ∀ n : ℕ, ∀ ρ : ℝ, r ≤ ρ → ρ ≤ R → R ≤ 2 ^ n * ρ →
      |(⨍ x in ball 0 ρ, u x) - ⨍ x in ball 0 R, u x| ≤
        Real.sqrt (2 ^ d) * (3 - 2 * ρ / R) * M := by
    intro n
    induction n with
    | zero =>
      intro ρ _ hρR hRρ
      rw [pow_zero, one_mul] at hRρ
      have e : ρ = R := le_antisymm hρR hRρ
      rw [e, sub_self, abs_zero, show 2 * R / R = 2 by field_simp]
      exact mul_nonneg (mul_nonneg hK (by norm_num)) hM
    | succ n ih =>
      intro ρ hrρ hρR hRρ
      have hρ : 0 < ρ := lt_of_lt_of_le hr hrρ
      by_cases h2 : 2 * ρ ≤ R
      · have h1 := ih (2 * ρ) (by linarith) h2 (by rw [pow_succ] at hRρ; linarith)
        have h3 := abs_setAverage_ball_sub_le hρ (by linarith : ρ ≤ 2 * ρ)
          (hu.mono_measure (Measure.restrict_mono (ball_zero_subset_ball_zero h2) le_rfl))
        rw [show 2 * ρ / ρ = 2 by field_simp] at h3
        have h4 := hdec (2 * ρ) (by linarith) h2
        calc |(⨍ x in ball 0 ρ, u x) - ⨍ x in ball 0 R, u x|
            ≤ |(⨍ x in ball 0 ρ, u x) - ⨍ x in ball 0 (2 * ρ), u x| +
              |(⨍ x in ball 0 (2 * ρ), u x) - ⨍ x in ball 0 R, u x| := abs_sub_le _ _ _
          _ ≤ Real.sqrt (2 ^ d) * (2 * ρ / R * M) +
              Real.sqrt (2 ^ d) * (3 - 2 * (2 * ρ) / R) * M :=
            add_le_add (h3.trans (mul_le_mul_of_nonneg_left h4 hK)) h1
          _ = Real.sqrt (2 ^ d) * (3 - 2 * ρ / R) * M := by ring
      · push Not at h2
        have h3 := abs_setAverage_ball_sub_le hρ hρR hu
        have h4 := hdec R (hrρ.trans hρR) le_rfl
        rw [div_self hR.ne', one_mul] at h4
        have h5 : Real.sqrt ((R / ρ) ^ d) ≤ Real.sqrt (2 ^ d) :=
          sqrt_pow_le_sqrt_pow (by positivity) (by rw [div_le_iff₀ hρ]; linarith)
        have h6 : 1 ≤ 3 - 2 * ρ / R := by
          have : ρ / R ≤ 1 := (div_le_one hR).2 hρR
          have e : 2 * ρ / R = 2 * (ρ / R) := by ring
          rw [e]
          linarith
        calc |(⨍ x in ball 0 ρ, u x) - ⨍ x in ball 0 R, u x|
            ≤ Real.sqrt ((R / ρ) ^ d) *
              scalarRms volume (ball 0 R) (fun x => u x - ⨍ y in ball 0 R, u y) := h3
          _ ≤ Real.sqrt (2 ^ d) * M := mul_le_mul h5 h4 (scalarRms_nonneg _ _) hK
          _ ≤ Real.sqrt (2 ^ d) * (3 - 2 * ρ / R) * M := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hM h6) hK
  have hρ : 0 < ρ := lt_of_lt_of_le hr hrρ
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (R / ρ) (by norm_num : (1 : ℝ) < 2)
  have h := key n ρ hrρ hρR (by rw [div_lt_iff₀ hρ] at hn; linarith)
  refine h.trans ?_
  have : 0 ≤ 2 * ρ / R := by positivity
  calc Real.sqrt (2 ^ d) * (3 - 2 * ρ / R) * M ≤ Real.sqrt (2 ^ d) * 3 * M :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hK) hM
    _ = 3 * Real.sqrt (2 ^ d) * M := by ring

/-- `‖c‖_{L̲²(B_ρ)} = |c|` for `ρ > 0`. -/
theorem scalarRms_const_ball {ρ : ℝ} (hρ : 0 < ρ) (c : ℝ) :
    scalarRms volume (ball (0 : Vec d) ρ) (fun _ => c) = |c| := by
  show Real.sqrt (⨍ _ in ball (0 : Vec d) ρ, c ^ 2) = |c|
  rw [setAverage_const (volume_ball_ne_zero' 0 hρ) (volume_ball_ne_top' 0 ρ), Real.sqrt_sq_eq_abs]

/-- (3.18) from (3.17): if `‖u - (u)_{B_ρ}‖_{L̲²(B_ρ)} ≤ (ρ/R) C ‖u - (u)_{B_R}‖_{L̲²(B_R)}` for every
`ρ ∈ [r, R]`, then `‖u‖_{L̲²(B_r)} ≤ (C (1 + 3 · 2^{d/2}) + 1) ‖u‖_{L̲²(B_R)}`. -/
theorem scalarRms_ball_le_of_decay {r R C : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hC : 0 ≤ C)
    {u : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict (ball (0 : Vec d) R)))
    (hdec : ∀ ρ : ℝ, r ≤ ρ → ρ ≤ R →
      scalarRms volume (ball 0 ρ) (fun x => u x - ⨍ y in ball 0 ρ, u y) ≤
        ρ / R * (C * scalarRms volume (ball 0 R) (fun x => u x - ⨍ y in ball 0 R, u y))) :
    scalarRms volume (ball 0 r) u ≤
      (C * (1 + 3 * Real.sqrt (2 ^ d)) + 1) * scalarRms volume (ball 0 R) u := by
  have hR : 0 < R := lt_of_lt_of_le hr hrR
  have hur : MemLp u 2 (volume.restrict (ball (0 : Vec d) r)) :=
    hu.mono_measure (Measure.restrict_mono (ball_zero_subset_ball_zero hrR) le_rfl)
  have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) r)) :=
    isFiniteMeasure_restrict.mpr (volume_ball_ne_top' 0 r)
  have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
    isFiniteMeasure_restrict.mpr (volume_ball_ne_top' 0 R)
  obtain ⟨oR, hoR⟩ : ∃ o : ℝ, o = scalarRms volume (ball 0 R) (fun x => u x - ⨍ y in ball 0 R, u y) :=
    ⟨_, rfl⟩
  rw [← hoR] at hdec
  have hoR_le : oR ≤ scalarRms volume (ball 0 R) u := by
    rw [hoR]
    refine (scalarRms_sub_setAverage_le_sub_const (volume_ball_ne_top' 0 R) hu 0).trans ?_
    simp only [sub_zero, le_refl]
  have havR : |⨍ x in ball 0 R, u x| ≤ scalarRms volume (ball 0 R) u :=
    abs_setAverage_le_scalarRms (volume_ball_ne_zero' 0 hR) (volume_ball_ne_top' 0 R) hu
  have hav := abs_setAverage_ball_sub_le_of_decay hr hu hdec le_rfl hrR
  have hosc := hdec r le_rfl hrR
  have hrR1 : r / R ≤ 1 := (div_le_one hR).2 hrR
  have hCo : 0 ≤ C * oR := mul_nonneg hC (hoR ▸ scalarRms_nonneg _ _)
  have hsplit : scalarRms volume (ball 0 r) u ≤
      scalarRms volume (ball 0 r) (fun x => u x - ⨍ y in ball 0 r, u y) +
        |⨍ x in ball 0 r, u x| := by
    have h := scalarRms_add_le (f := fun x => u x - ⨍ y in ball 0 r, u y)
      (g := fun _ => ⨍ y in ball 0 r, u y) (hur.sub (memLp_const (⨍ y in ball 0 r, u y)))
      (memLp_const (⨍ y in ball 0 r, u y))
    rw [scalarRms_const_ball hr] at h
    simpa only [sub_add_cancel] using h
  have hK : 0 ≤ Real.sqrt (2 ^ d) := Real.sqrt_nonneg _
  calc scalarRms volume (ball 0 r) u
      ≤ scalarRms volume (ball 0 r) (fun x => u x - ⨍ y in ball 0 r, u y) +
        |⨍ x in ball 0 r, u x| := hsplit
    _ ≤ C * oR + (3 * Real.sqrt (2 ^ d) * (C * oR) + scalarRms volume (ball 0 R) u) := by
        refine add_le_add (hosc.trans (mul_le_of_le_one_left hCo hrR1)) ?_
        calc |⨍ x in ball 0 r, u x|
            ≤ |(⨍ x in ball 0 r, u x) - ⨍ x in ball 0 R, u x| + |⨍ x in ball 0 R, u x| := by
              have := abs_add_le ((⨍ x in ball 0 r, u x) - ⨍ x in ball 0 R, u x)
                (⨍ x in ball 0 R, u x)
              rwa [sub_add_cancel] at this
          _ ≤ _ := add_le_add hav havR
    _ = C * (1 + 3 * Real.sqrt (2 ^ d)) * oR + scalarRms volume (ball 0 R) u := by ring
    _ ≤ C * (1 + 3 * Real.sqrt (2 ^ d)) * scalarRms volume (ball 0 R) u +
          scalarRms volume (ball 0 R) u :=
        add_le_add (mul_le_mul_of_nonneg_left hoR_le (by positivity)) le_rfl
    _ = _ := by ring

/-- **Theorem 3.3** (quenched `C^{0,1}`-type estimate), for `d ≥ 2` and `Λ > 1`. Fix `s ∈ (0, d)`.
There is `C(s, d, Λ)` such that, for every law `P` satisfying the assumptions, there is a random
variable `X_s ≥ 1` with `X_s ≤ O_s(C)`, (3.15), such that for almost every coefficient field `a`,
every `R ≥ X_s` and every weak solution `u ∈ H¹(B_R)` of `-∇·(a∇u) = 0` in `B_R`, (3.16), we have
for every `r ∈ [X_s, R]` the estimates (3.17)
`r⁻¹ ‖u - (u)_{B_r}‖_{L̲²(B_r)} ≤ C R⁻¹ ‖u - (u)_{B_R}‖_{L̲²(B_R)}` and (3.18)
`‖u‖_{L̲²(B_r)} ≤ C ‖u‖_{L̲²(B_R)}`.

Departures from the book, as in Proposition 3.2: the estimates hold for almost every coefficient
field (the book's `X_s` takes the value `∞` on the exceptional set); `X_s` is real valued; the
solution `u ∈ H¹(B_R)` is given with its weak gradient `g` (`u, g ∈ L²(B_R)`). -/
theorem theorem_3_3 (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) {s : ℝ} (hs : 0 < s) (hsd : s < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∃ X : CoefficientField d Λ → ℝ, OsBound P X s C ∧ (∀ a, 1 ≤ X a) ∧ ∀ᵐ a ∂P,
        ∀ R : ℝ, X a ≤ R → ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
        MemLp u 2 (volume.restrict (ball 0 R)) →
        (∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 R))) →
        HasWeakGradient (ball 0 R) u g →
        HasWeakDivergence (ball 0 R) (fun x => (a x).mulVec (g x)) (fun _ => 0) →
        ∀ r : ℝ, X a ≤ r → r ≤ R →
          1 / r * scalarRms volume (ball 0 r) (fun x => u x - ⨍ y in ball 0 r, u y) ≤
            C / R * scalarRms volume (ball 0 R) (fun x => u x - ⨍ y in ball 0 R, u y) ∧
          scalarRms volume (ball 0 r) u ≤ C * scalarRms volume (ball 0 R) u := by
  have hΛ0 : (0 : ℝ) ≤ Λ := by linarith
  obtain ⟨α, hα, hprop⟩ := proposition_3_2 hd hΛ
  obtain ⟨CP, hCP, hP⟩ := hprop s hs hsd
  have hds : 0 < (d : ℝ) - s := by linarith
  obtain ⟨C₄, hC₄, h34⟩ := lemma_3_4_halfBall hd hΛ.le (mul_pos hα hds) (le_max_right CP 1)
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ,
      C = max (2 * CP) (max C₄ (C₄ * (1 + 3 * Real.sqrt (2 ^ d)) + 1)) := ⟨_, rfl⟩
  have hC2 : 2 * CP ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hC4 : C₄ ≤ C := by rw [hCdef]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hC5 : C₄ * (1 + 3 * Real.sqrt (2 ^ d)) + 1 ≤ C := by
    rw [hCdef]; exact (le_max_right _ _).trans (le_max_right _ _)
  have hC0 : 0 < C := by
    have : 0 ≤ C₄ * (1 + 3 * Real.sqrt (2 ^ d)) := by positivity
    linarith
  refine ⟨C, hC0, fun P hPlaw => ?_⟩
  obtain ⟨X, hXos, hX1, hXae⟩ := hP P hPlaw
  refine ⟨fun a => 2 * X a, (hXos.const_mul two_pos).mono_scale hC2,
    fun a => by linarith [hX1 a], ?_⟩
  filter_upwards [hXae] with a ha
  intro R hXR u g hu hg hug hdiv r hXr hrR
  have hsym := homogenizedMatrix_transpose hPlaw hΛ0
  have hbd : HomogenizedMatrixBounds (homogenizedMatrix P) Λ := fun ξ =>
    ⟨euclideanSq_le_dot_homogenizedMatrix hPlaw hΛ0 ξ, (homogenizedMatrix_dot_bounds hPlaw hΛ0 ξ).2⟩
  have hX1a := hX1 a
  have hR : 0 < R := by linarith
  have hr : 0 < r := by linarith
  have h317 := h34 (homogenizedMatrix P) hsym hbd (X a) R hX1a hXR u hu (fun ρ h1 h2 => by
    have hρR : ρ ≤ R := by linarith
    have hsub : ball (0 : Vec d) ρ ⊆ ball 0 R := ball_zero_subset_ball_zero hρR
    obtain ⟨uh, gh, huh, hgh, hugh, hdivh, hbound⟩ := ha ρ h1 u g
      (hu.mono_measure (Measure.restrict_mono hsub le_rfl))
      (fun i => (hg i).mono_measure (Measure.restrict_mono hsub le_rfl)) (hug.mono hsub)
      (hdiv.mono' hsub)
    refine ⟨uh, ⟨huh, gh, hgh, hugh, hdivh⟩, hbound.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by linarith) _)) (scalarRms_nonneg _ _))
  have hdec : ∀ ρ : ℝ, r ≤ ρ → ρ ≤ R →
      scalarRms volume (ball 0 ρ) (fun x => u x - ⨍ y in ball 0 ρ, u y) ≤
        ρ / R * (C₄ * scalarRms volume (ball 0 R) (fun x => u x - ⨍ y in ball 0 R, u y)) := by
    intro ρ h1 h2
    have hρ : 0 < ρ := lt_of_lt_of_le hr h1
    have h := h317 ρ (by linarith) h2
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hρ] at h
    calc _ ≤ C₄ / R * scalarRms volume (ball 0 R) (fun x => u x - ⨍ y in ball 0 R, u y) * ρ := h
      _ = _ := by ring
  refine ⟨(h317 r (by linarith) hrR).trans ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hC4 hR.le) (scalarRms_nonneg _ _)
  · exact (scalarRms_ball_le_of_decay hr hrR hC₄ hu hdec).trans
      (mul_le_mul_of_nonneg_right hC5 (scalarRms_nonneg _ _))

end Theorem33

end QSH
