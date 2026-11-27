import QuantitativeStochasticHomogenization.Ch03.Sec02.HarmonicPolynomials

/-!
# Lemma 3.6 for every `k`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 3.2, Lemma 3.6: for a symmetric `A` with `1 ≤ A ≤ Λ`, `α > 0` and `k ∈ ℕ` there are
`θ(α, k, d, Λ) ∈ (0, ½)` and `C(α, k, d, Λ)` such that, if for every `r ∈ [X, R]` some `A`-harmonic
`w_r` in `B_{r/2}` satisfies (3.28), `‖u - w_r‖_{L̲²(B_{r/2})} ≤ K r^{-α} ‖u - (u)_{B_r}‖_{L̲²(B_r)}`,
then (3.29)
`inf_{p ∈ Ā_k} ‖u - p‖_{L̲²(B_{θr})} ≤ ¼ θ^{k+1-α/2} inf_{p ∈ Ā_k} ‖u - p‖_{L̲²(B_r)}
+ C K r^{-α} ‖u - (u)_{B_r}‖_{L̲²(B_r)}` for every `r ∈ [X, R]`. The proof is the book's, with the
approximation (3.24) of `exists_harmonicPoly_scalarRms_ball_le`.
-/

open MeasureTheory Filter Set

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- `inf_{p ∈ Ā_k} ‖u - p‖_{L̲²(B_r)}`, the distance of `u` to the `A`-harmonic polynomials of
degree at most `k` on `B_r`. -/
def harmonicFlatness (A : Mat d) (k : ℕ) (u : Vec d → ℝ) (r : ℝ) : ℝ :=
  ⨅ p : harmonicPolys A k, scalarRms volume (ball 0 r) (fun x => u x - (p : Vec d → ℝ) x)

theorem bddBelow_harmonicFlatness (A : Mat d) (k : ℕ) (u : Vec d → ℝ) (r : ℝ) :
    BddBelow (range fun p : harmonicPolys A k =>
      scalarRms volume (ball 0 r) (fun x => u x - (p : Vec d → ℝ) x)) :=
  ⟨0, by rintro _ ⟨p, rfl⟩; exact scalarRms_nonneg _ _⟩

theorem harmonicFlatness_le {A : Mat d} {k : ℕ} (u : Vec d → ℝ) (r : ℝ) {p : Vec d → ℝ}
    (hp : p ∈ harmonicPolys A k) :
    harmonicFlatness A k u r ≤ scalarRms volume (ball 0 r) (fun x => u x - p x) :=
  ciInf_le (bddBelow_harmonicFlatness A k u r) (⟨p, hp⟩ : harmonicPolys A k)

theorem harmonicFlatness_nonneg (A : Mat d) (k : ℕ) (u : Vec d → ℝ) (r : ℝ) :
    0 ≤ harmonicFlatness A k u r := by
  have : Nonempty (harmonicPolys A k) := ⟨⟨_, zero_mem_harmonicPolys A k⟩⟩
  exact le_ciInf fun _ => scalarRms_nonneg _ _

/-- **Lemma 3.6** (every `k`, `α > 0`). -/
theorem lemma_3_6 (hd : 2 ≤ d) (hΛ : 1 ≤ Λ) {α : ℝ} (hα : 0 < α) (k : ℕ) :
    ∃ θ C : ℝ, 0 < θ ∧ θ < 1 / 2 ∧ 0 ≤ C ∧
      ∀ A : Mat d, A.transpose = A → HomogenizedMatrixBounds A Λ →
      ∀ K X R : ℝ, 1 ≤ X → ∀ u : Vec d → ℝ, MemLp u 2 (volume.restrict (ball 0 R)) →
      (∀ r : ℝ, X ≤ r → r ≤ R → ∃ w : Vec d → ℝ, IsL2HarmonicOn A (ball 0 (r / 2)) w ∧
        scalarRms volume (ball 0 (r / 2)) (fun x => u x - w x) ≤
          K * r ^ (-α) * scalarRms volume (ball 0 r) (fun x => u x - ⨍ y in ball 0 r, u y)) →
      ∀ r : ℝ, X ≤ r → r ≤ R →
        harmonicFlatness A k u (θ * r) ≤
          1 / 4 * θ ^ ((k : ℝ) + 1 - α / 2) * harmonicFlatness A k u r +
            C * K * r ^ (-α) * scalarRms volume (ball 0 r) (fun x => u x - ⨍ y in ball 0 r, u y) := by
  obtain ⟨C₁, hC₁, happ⟩ := exists_harmonicPoly_scalarRms_ball_le hd hΛ k
  have hΛ0 : 0 < Λ := by linarith
  have hsΛ1 : 1 ≤ Real.sqrt Λ := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hΛ
  obtain ⟨s₂, hs₂⟩ : ∃ s : ℝ, s = Real.sqrt (2 ^ d) := ⟨_, rfl⟩
  have hs₂0 : 0 ≤ s₂ := by rw [hs₂]; exact Real.sqrt_nonneg _
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 4 * (C₁ + 1) * 2 ^ (k + 1) * s₂ := ⟨_, rfl⟩
  have hs₂1 : 1 ≤ s₂ := by
    rw [hs₂, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (one_le_pow₀ (by norm_num))
  have hB0 : 0 < B := by rw [hB]; positivity
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = min (1 / (8 * Real.sqrt Λ)) (B ^ (-(2 / α))) := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθdef]; exact lt_min (by positivity) (Real.rpow_pos_of_pos hB0 _)
  have hθ8 : θ ≤ 1 / (8 * Real.sqrt Λ) := by rw [hθdef]; exact min_le_left _ _
  have hθB : θ ≤ B ^ (-(2 / α)) := by rw [hθdef]; exact min_le_right _ _
  have h8Λ : 1 / (8 * Real.sqrt Λ) ≤ 1 / 8 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num); linarith
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = Real.sqrt ((1 / (2 * θ)) ^ d) + C₁ * (2 * θ) ^ (k + 1) :=
    ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  refine ⟨θ, C, hθ0, by linarith, hC0, ?_⟩
  -- the contraction factor
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = C₁ * (2 * θ) ^ (k + 1) * s₂ := ⟨_, rfl⟩
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hpow : θ ^ (α / 2) ≤ B⁻¹ := by
    have h1 : θ ^ (α / 2) ≤ (B ^ (-(2 / α))) ^ (α / 2) :=
      Real.rpow_le_rpow hθ0.le hθB (by positivity)
    rw [← Real.rpow_mul hB0.le] at h1
    have e : -(2 / α) * (α / 2) = -1 := by field_simp
    rwa [e, Real.rpow_neg_one] at h1
  have hθpos : 0 < θ ^ (α / 2) := Real.rpow_pos_of_pos hθ0 _
  have hYle : Y ≤ 1 / 4 * θ ^ ((k : ℝ) + 1 - α / 2) := by
    have hsplit : θ ^ (k + 1) = θ ^ (α / 2) * θ ^ ((k : ℝ) + 1 - α / 2) := by
      rw [← Real.rpow_add hθ0, show α / 2 + ((k : ℝ) + 1 - α / 2) = ((k + 1 : ℕ) : ℝ) by
        push_cast; ring, Real.rpow_natCast]
    have hθk : 0 ≤ θ ^ ((k : ℝ) + 1 - α / 2) := (Real.rpow_pos_of_pos hθ0 _).le
    have hBθ : B * θ ^ (α / 2) ≤ 1 := by
      calc B * θ ^ (α / 2) ≤ B * B⁻¹ := mul_le_mul_of_nonneg_left hpow hB0.le
        _ = 1 := mul_inv_cancel₀ hB0.ne'
    have hc : C₁ * 2 ^ (k + 1) * s₂ * θ ^ (α / 2) ≤ 1 / 4 := by
      have h2 : C₁ * 2 ^ (k + 1) * s₂ ≤ B / 4 := by
        rw [hB]
        have : 0 ≤ 2 ^ (k + 1) * s₂ := by positivity
        nlinarith
      calc C₁ * 2 ^ (k + 1) * s₂ * θ ^ (α / 2) ≤ B / 4 * θ ^ (α / 2) :=
            mul_le_mul_of_nonneg_right h2 hθpos.le
        _ ≤ 1 / 4 := by linarith
    calc Y = (C₁ * 2 ^ (k + 1) * s₂ * θ ^ (α / 2)) * θ ^ ((k : ℝ) + 1 - α / 2) := by
          rw [hY, mul_pow, hsplit]; ring
      _ ≤ 1 / 4 * θ ^ ((k : ℝ) + 1 - α / 2) := mul_le_mul_of_nonneg_right hc hθk
  intro A hsym hA K X R hX u hu hyp r hXr hrR
  have hr : 0 < r := by linarith
  have hr2 : 0 < r / 2 := half_pos hr
  have hθr : 0 < θ * r := mul_pos hθ0 hr
  have hθr2 : θ * r ≤ r / 2 := by nlinarith
  have hθr4 : θ * r ≤ r / 2 / (4 * Real.sqrt Λ) := by
    rw [div_div, show 2 * (4 * Real.sqrt Λ) = 8 * Real.sqrt Λ by ring, le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at hθ8
    nlinarith
  obtain ⟨w, hw, hη⟩ := hyp r hXr hrR
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ,
      η = K * r ^ (-α) * scalarRms volume (ball 0 r) (fun x => u x - ⨍ y in ball 0 r, u y) :=
    ⟨_, rfl⟩
  rw [← hηdef] at hη
  have huw0 : 0 ≤ η := (scalarRms_nonneg _ _).trans hη
  have hur : MemLp u 2 (volume.restrict (ball (0 : Vec d) r)) :=
    hu.mono_measure (Measure.restrict_mono (ball_zero_subset_ball_zero hrR) le_rfl)
  have hur2 : MemLp u 2 (volume.restrict (ball (0 : Vec d) (r / 2))) :=
    hur.mono_measure (Measure.restrict_mono (ball_zero_subset_ball_zero (by linarith)) le_rfl)
  have hkey : ∀ p ∈ harmonicPolys A k, harmonicFlatness A k u (θ * r) ≤
      Y * scalarRms volume (ball 0 r) (fun x => u x - p x) + C * η := by
    intro p hp
    have hpL2 : MemLp p 2 (volume.restrict (ball (0 : Vec d) r)) := (hp.2 r hr).1
    have hpL2' : MemLp p 2 (volume.restrict (ball (0 : Vec d) (r / 2))) := (hp.2 (r / 2) hr2).1
    obtain ⟨q, hq, hqb⟩ := happ A hsym hA (r / 2) hr2 (fun x => w x - p x)
      (hw.sub' (hp.2 (r / 2) hr2))
    have hqL2 : MemLp q 2 (volume.restrict (ball (0 : Vec d) (r / 2))) := (hq.2 (r / 2) hr2).1
    have hb1 := hqb (θ * r) hθr hθr4
    rw [show θ * r / (r / 2) = 2 * θ by field_simp] at hb1
    have hsub : ball (0 : Vec d) (θ * r) ⊆ ball 0 (r / 2) := ball_zero_subset_ball_zero hθr2
    have hm1 : MemLp (fun x => u x - w x) 2 (volume.restrict (ball (0 : Vec d) (r / 2))) :=
      hur2.sub hw.1
    have hm2 : MemLp (fun x => (w x - p x) - q x) 2 (volume.restrict (ball (0 : Vec d) (r / 2))) :=
      (hw.1.sub hpL2').sub hqL2
    have hE := harmonicFlatness_le u (θ * r) (add_mem_harmonicPolys hp hq)
    have hadd := scalarRms_add_le (hm1.mono_measure (Measure.restrict_mono hsub le_rfl))
      (hm2.mono_measure (Measure.restrict_mono hsub le_rfl))
    have e : (fun x => u x - (p x + q x)) = fun x => (u x - w x) + ((w x - p x) - q x) := by
      funext x; ring
    rw [e] at hE
    have h1 : scalarRms volume (ball 0 (θ * r)) (fun x => u x - w x) ≤
        Real.sqrt ((1 / (2 * θ)) ^ d) * η := by
      have h := scalarRms_ball_le hθr hθr2 hm1
      rw [show r / 2 / (θ * r) = 1 / (2 * θ) by field_simp] at h
      exact h.trans (mul_le_mul_of_nonneg_left hη (Real.sqrt_nonneg _))
    have h3 : scalarRms volume (ball 0 (r / 2)) (fun x => w x - p x) ≤
        s₂ * scalarRms volume (ball 0 r) (fun x => u x - p x) + η := by
      have e2 : (fun x => w x - p x) = fun x => (u x - p x) - (u x - w x) := by funext x; ring
      rw [e2]
      refine (scalarRms_sub_le (hur2.sub hpL2') hm1).trans (add_le_add ?_ hη)
      have h := scalarRms_ball_le hr2 (by linarith : r / 2 ≤ r) (hur.sub hpL2)
      rwa [show r / (r / 2) = 2 by field_simp, ← hs₂] at h
    have hC₁2 : 0 ≤ C₁ * (2 * θ) ^ (k + 1) := by positivity
    calc harmonicFlatness A k u (θ * r)
        ≤ Real.sqrt ((1 / (2 * θ)) ^ d) * η +
            C₁ * (2 * θ) ^ (k + 1) * (s₂ * scalarRms volume (ball 0 r) (fun x => u x - p x) + η) :=
          hE.trans (hadd.trans (add_le_add h1 (hb1.trans (mul_le_mul_of_nonneg_left h3 hC₁2))))
      _ = Y * scalarRms volume (ball 0 r) (fun x => u x - p x) + C * η := by
          rw [hY, hCdef]; ring
  have : Nonempty (harmonicPolys A k) := ⟨⟨_, zero_mem_harmonicPolys A k⟩⟩
  have hinf : harmonicFlatness A k u (θ * r) - C * η ≤ Y * harmonicFlatness A k u r := by
    have e : Y * harmonicFlatness A k u r = ⨅ p : harmonicPolys A k,
        Y * scalarRms volume (ball 0 r) (fun x => u x - (p : Vec d → ℝ) x) :=
      Real.mul_iInf_of_nonneg hY0 _
    rw [e]
    exact le_ciInf fun p => by linarith [hkey p.1 p.2]
  have hE0 := harmonicFlatness_nonneg A k u r
  calc harmonicFlatness A k u (θ * r) ≤ Y * harmonicFlatness A k u r + C * η := by linarith
    _ ≤ 1 / 4 * θ ^ ((k : ℝ) + 1 - α / 2) * harmonicFlatness A k u r + C * η :=
        add_le_add (mul_le_mul_of_nonneg_right hYle hE0) le_rfl
    _ = _ := by rw [hηdef]; ring

end QSH
