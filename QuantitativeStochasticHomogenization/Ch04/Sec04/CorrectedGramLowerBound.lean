import QuantitativeStochasticHomogenization.Ch04.Sec04.GaussianGramComparison

/-!
# A lower bound for the energies of combinations of corrected gradients on a ball

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.22, (4.104). Let `u_i` be functions on `B_R(z)` with weak gradients `W_i`,
which are close to the coordinates: `∫_{B_R(z)} (u_i - (x - z)_i - c_i)² ≤ ε² R² |B_R|` (for the
corrected coordinates `u_i = (x - z)_i + φ_{e_i}`, this is the sublinearity of the correctors
above their minimal scale). If `d ε² ≤ 4^{-d}/16`, then for every `ξ`,
`∫_{B_R(z)} |∑ ξ_i W_i|² ≥ 4^{-d} |ξ|² |B_R| / (16 (2^{d+1})²)`.

The proof applies the Poincaré inequality to `ℓ = ∑ ξ_i u_i`: its oscillation is at least that
of the linear function `ξ·(x - z)`, which is of order `|ξ| R` on one of two balls of radius
`R/4` inside `B_R(z)`, up to the oscillation of `∑ ξ_i (u_i - (x - z)_i)`.
-/

open MeasureTheory Filter
open scoped InnerProductSpace

noncomputable section

namespace QSH

variable {d : ℕ} {z : Vec d} {R : ℝ}

theorem dot_eq_inner_toLp (x y : Vec d) :
    dot x y = ⟪(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)), WithLp.toLp 2 y⟫_ℝ := by
  simp [dot, PiLp.inner_apply, mul_comm]

/-- The Cauchy–Schwarz inequality for `dot`. -/
theorem abs_dot_le_euclideanNorm_mul (x y : Vec d) :
    |dot x y| ≤ euclideanNorm x * euclideanNorm y := by
  rw [dot_eq_inner_toLp, euclideanNorm_eq_euclideanSpace_norm,
    euclideanNorm_eq_euclideanSpace_norm]
  exact abs_real_inner_le_norm _ _

theorem dot_add_smul_right (ξ v w : Vec d) (t : ℝ) :
    dot ξ (v + t • w) = dot ξ v + t * dot ξ w := by
  simp only [dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The volume of a ball is `ρ^d` times the volume of the unit ball. -/
theorem volume_real_ball_eq_mul (y : Vec d) {ρ : ℝ} (hρ : 0 < ρ) :
    volume.real (ball y ρ) = ρ ^ d * volume.real (ball (0 : Vec d) 1) := by
  rw [ball_eq_euclideanBall y hρ, ball_eq_euclideanBall 0 one_pos, measureReal_def,
    measureReal_def]
  exact PDE.volume_euclideanBall_toReal_eq_unit_mul_of_pos y hρ

theorem ball_subset_ball_of_add_le {y : Vec d} {ρ : ℝ} (h : euclideanNorm (y - z) + ρ ≤ R) :
    ball y ρ ⊆ ball z R := by
  intro x hx
  have hx' : euclideanNorm (x - y) < ρ := hx
  show euclideanNorm (x - z) < R
  have := euclideanNorm_sub_le_sub_add x z y
  linarith

theorem integrableOn_ball_of_continuous {f : Vec d → ℝ} (hf : Continuous f) (hR : 0 < R) :
    IntegrableOn f (ball z R) := by
  rw [ball_eq_euclideanBall z hR]
  exact (hf.continuousOn.integrableOn_compact (PDE.isCompact_euclideanClosedBall z hR.le)).mono_set
    (PDE.euclideanBall_subset_euclideanClosedBall z R)

/-- **The oscillation of a linear function on a ball**: for every constant `c`,
`∫_{B_R(z)} (ξ·(x - z) - c)² ≥ |ξ|² R²/4 · 4^{-d} |B_R|`. -/
theorem integral_dot_sub_sq_ge (z : Vec d) (hR : 0 < R) (ξ : Vec d) (c : ℝ) :
    euclideanSq ξ * R ^ 2 / 4 * ((1 / 4 : ℝ) ^ d * volume.real (ball z R)) ≤
      ∫ x in ball z R, (dot ξ (x - z) - c) ^ 2 := by
  have hcont : Continuous fun x : Vec d => (dot ξ (x - z) - c) ^ 2 := by
    unfold dot
    fun_prop
  have hint : IntegrableOn (fun x : Vec d => (dot ξ (x - z) - c) ^ 2) (ball z R) :=
    integrableOn_ball_of_continuous hcont hR
  by_cases hξ : euclideanSq ξ = 0
  · rw [hξ, zero_mul, zero_div, zero_mul]
    exact setIntegral_nonneg (measurableSet_ball z R) fun x _ => sq_nonneg _
  set n := euclideanNorm ξ with hn_def
  have hn2 : n ^ 2 = euclideanSq ξ := sq_euclideanNorm ξ
  have hn : 0 < n := by
    rcases (zero_le_euclideanNorm ξ).lt_or_eq with h | h
    · exact h
    · exfalso; apply hξ; rw [← hn2, show n = 0 from h.symm]; ring
  have hn0 : n ≠ 0 := hn.ne'
  obtain ⟨s, hs1, hsabs, hsc⟩ : ∃ s : ℝ, s ^ 2 = 1 ∧ |s| = 1 ∧ s * c ≤ 0 := by
    by_cases h : 0 ≤ c
    · exact ⟨-1, by norm_num, by norm_num, by linarith⟩
    · exact ⟨1, by norm_num, by norm_num, by linarith⟩
  set y : Vec d := z + (s * (3 * R / 4) / n) • ξ with hy
  have hyz : euclideanNorm (y - z) = 3 * R / 4 := by
    rw [hy, add_sub_cancel_left, euclideanNorm_eq_euclideanSpace_norm, WithLp.toLp_smul,
      norm_smul, ← euclideanNorm_eq_euclideanSpace_norm, ← hn_def, Real.norm_eq_abs, abs_div,
      abs_mul, hsabs, abs_of_pos hn, abs_of_pos (by positivity : (0 : ℝ) < 3 * R / 4)]
    field_simp
  have hsub : ball y (R / 4) ⊆ ball z R := ball_subset_ball_of_add_le (by rw [hyz]; linarith)
  have hpt : ∀ x ∈ ball y (R / 4), (n * R / 2) ^ 2 ≤ (dot ξ (x - z) - c) ^ 2 := by
    intro x hx
    have hx' : euclideanNorm (x - y) < R / 4 := hx
    have h1 : dot ξ (x - z) = dot ξ (x - y) + s * (3 * R / 4) * n := by
      have hxz : x - z = (x - y) + (s * (3 * R / 4) / n) • ξ := by
        rw [hy]; abel
      rw [hxz, dot_add_smul_right]
      have : dot ξ ξ = n ^ 2 := by rw [hn2]; rfl
      rw [this]
      field_simp
    have h2 : |dot ξ (x - y)| ≤ n * (R / 4) :=
      (abs_dot_le_euclideanNorm_mul ξ (x - y)).trans
        (mul_le_mul_of_nonneg_left hx'.le hn.le)
    have h3 : n * R / 2 ≤ s * (dot ξ (x - z) - c) := by
      rw [h1]
      have h4 : -(n * (R / 4)) ≤ s * dot ξ (x - y) := by
        have := neg_abs_le (s * dot ξ (x - y))
        rw [abs_mul, hsabs, one_mul] at this
        linarith
      have h7 : s * (s * (3 * R / 4) * n) = 3 * R / 4 * n := by
        have : s * (s * (3 * R / 4) * n) = s ^ 2 * (3 * R / 4 * n) := by ring
        rw [this, hs1, one_mul]
      rw [mul_sub, mul_add, h7]
      linarith
    have h5 : n * R / 2 ≤ |dot ξ (x - z) - c| := by
      refine h3.trans ((le_abs_self _).trans ?_)
      rw [abs_mul, hsabs, one_mul]
    have h6 : 0 ≤ n * R / 2 := by positivity
    calc (n * R / 2) ^ 2 ≤ |dot ξ (x - z) - c| ^ 2 := pow_le_pow_left₀ h6 h5 2
      _ = (dot ξ (x - z) - c) ^ 2 := sq_abs _
  have hvol : volume.real (ball y (R / 4)) = (1 / 4 : ℝ) ^ d * volume.real (ball z R) := by
    rw [volume_real_ball_eq_mul y (by positivity : (0 : ℝ) < R / 4), volume_real_ball_eq_mul z hR,
      div_eq_mul_one_div R 4, mul_pow]
    ring
  calc euclideanSq ξ * R ^ 2 / 4 * ((1 / 4 : ℝ) ^ d * volume.real (ball z R))
      = (n * R / 2) ^ 2 * volume.real (ball y (R / 4)) := by
        rw [hvol, ← hn2]; ring
    _ ≤ ∫ x in ball y (R / 4), (dot ξ (x - z) - c) ^ 2 :=
        setIntegral_ge_of_const_le_real (measurableSet_ball _ _) (volume_ball_lt_top _ _).ne hpt
          (hint.mono_set hsub)
    _ ≤ ∫ x in ball z R, (dot ξ (x - z) - c) ^ 2 :=
        setIntegral_mono_set hint (Eventually.of_forall fun x => sq_nonneg _)
          hsub.eventuallyLE

theorem memLp_coordinate_sub (z : Vec d) (R : ℝ) (i : Fin d) :
    MemLp (fun x : Vec d => (x - z) i) 2 (ballMeasure z R) := by
  refine MemLp.of_bound ((continuous_apply i).comp
    (continuous_id.sub continuous_const)).aestronglyMeasurable R ?_
  refine (ae_restrict_iff' (measurableSet_ball z R)).2 (Eventually.of_forall fun x hx => ?_)
  rw [Real.norm_eq_abs]
  exact (abs_coord_le_euclideanNorm (x - z) i).trans (le_of_lt hx)

/-- **The lower bound for the energies of combinations of corrected gradients on a ball.** -/
theorem gram_lower_bound_of_sublinear (hR : 0 < R) (u : Fin d → Vec d → ℝ)
    (W : Fin d → Vec d → Vec d) (hu : ∀ i, MemLp (u i) 2 (ballMeasure z R))
    (hW : ∀ i j, MemLp (fun x => W i x j) 2 (ballMeasure z R))
    (hgrad : ∀ i, HasWeakGradient (ball z R) (u i) (W i)) (c : Fin d → ℝ) {ε : ℝ}
    (hsub : ∀ i, ∫ x in ball z R, (u i x - (x - z) i - c i) ^ 2 ≤
      ε ^ 2 * R ^ 2 * volume.real (ball z R))
    (hε : (d : ℝ) * ε ^ 2 ≤ (1 / 4 : ℝ) ^ d / 16) (ξ : Vec d) :
    (1 / 4 : ℝ) ^ d / (16 * (2 ^ d * 2) ^ 2) * euclideanSq ξ * volume.real (ball z R) ≤
      ∫ x in ball z R, euclideanSq (∑ i, ξ i • W i x) := by
  let ℓ : Vec d → ℝ := fun x => ∑ i, ξ i * u i x
  have hℓ : MemLp ℓ 2 (ballMeasure z R) :=
    memLp_finsetSum _ fun i _ => (hu i).const_mul (ξ i)
  let v : Fin d → Vec d → ℝ := fun j x => ∑ i, ξ i * W i x j
  have hv : ∀ j, MemLp (v j) 2 (ballMeasure z R) := fun j =>
    memLp_finsetSum _ fun i _ => (hW i j).const_mul (ξ i)
  let F : PairSpace d z R := (hℓ.toLp ℓ, fun j => (hv j).toLp (v j))
  have hF : IsGradientPair F := by
    intro φ hφ j
    rw [gradConstraint_eq]
    have e1 : (∫ x in ball z R, F.1 x * coordinateDerivative j φ x) =
        ∫ x in ball z R, ℓ x * coordinateDerivative j φ x := by
      refine integral_congr_ae ?_
      filter_upwards [hℓ.coeFn_toLp] with x hx
      rw [hx]
    have e2 : (∫ x in ball z R, F.2 j x * φ x) = ∫ x in ball z R, v j x * φ x := by
      refine integral_congr_ae ?_
      filter_upwards [(hv j).coeFn_toLp] with x hx
      rw [hx]
    have e3 : (∫ x in ball z R, ℓ x * coordinateDerivative j φ x) =
        ∑ i, ξ i * ∫ x in ball z R, u i x * coordinateDerivative j φ x := by
      have : (fun x => ℓ x * coordinateDerivative j φ x) =
          fun x => ∑ i, ξ i * (u i x * coordinateDerivative j φ x) := by
        funext x
        simp only [ℓ, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [this, integral_finsetSum]
      · exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
      · intro i _
        exact ((hu i).integrable_mul
          (hφ.memLp_coordinateDerivative j (ballMeasure z R))).const_mul (ξ i)
    have e4 : (∫ x in ball z R, v j x * φ x) =
        ∑ i, ξ i * ∫ x in ball z R, W i x j * φ x := by
      have : (fun x => v j x * φ x) = fun x => ∑ i, ξ i * (W i x j * φ x) := by
        funext x
        simp only [v, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [this, integral_finsetSum]
      · exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
      · intro i _
        exact ((hW i j).integrable_mul (hφ.memLp (ballMeasure z R))).const_mul (ξ i)
    rw [e1, e2, e3, e4, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [(hgrad i j).2.2 φ hφ]
    ring
  have hP := integral_sub_average_sq_le_of_isGradientPair F hF hR
  have hE : pairGradEnergy F = ∫ x in ball z R, euclideanSq (∑ i, ξ i • W i x) := by
    simp only [pairGradEnergy, F, norm_toLp_sq_eq_integral]
    rw [← integral_finsetSum _ fun j _ => (hv j).integrable_sq]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [euclideanSq, dot, v, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sq]
  set m := ⨍ y in ball z R, ℓ y with hm
  have hosc : ∫ x in ball z R, (F.1 x - ⨍ y in ball z R, F.1 y) ^ 2 =
      ∫ x in ball z R, (ℓ x - m) ^ 2 := by
    have hav : (⨍ y in ball z R, F.1 y) = m := average_congr hℓ.coeFn_toLp
    rw [hav]
    refine integral_congr_ae ?_
    filter_upwards [hℓ.coeFn_toLp] with x hx
    rw [hx]
  set c' := m - ∑ i, ξ i * c i with hc'
  let A : Vec d → ℝ := fun x => dot ξ (x - z) - c'
  let B : Vec d → ℝ := fun x => ∑ i, ξ i * (u i x - (x - z) i - c i)
  have hAB : ∀ x, ℓ x - m = A x + B x := by
    intro x
    simp only [ℓ, A, B, hc', dot, mul_sub, Finset.sum_sub_distrib, Pi.sub_apply]
    ring
  have hmem : ∀ i, MemLp (fun x => u i x - (x - z) i - c i) 2 (ballMeasure z R) := fun i =>
    ((hu i).sub (memLp_coordinate_sub z R i)).sub (memLp_const (c i))
  have hB : MemLp B 2 (ballMeasure z R) :=
    memLp_finsetSum _ fun i _ => (hmem i).const_mul (ξ i)
  have hAcont : Continuous A := by
    simp only [A, dot]
    fun_prop
  have hA2 : IntegrableOn (fun x => A x ^ 2) (ball z R) :=
    integrableOn_ball_of_continuous (hAcont.pow 2) hR
  have hB2 : Integrable (fun x => B x ^ 2) (ballMeasure z R) := hB.integrable_sq
  have hl2 : Integrable (fun x => (ℓ x - m) ^ 2) (ballMeasure z R) :=
    (hℓ.sub (memLp_const m)).integrable_sq
  have hlow1 : (1 / 2) * (∫ x in ball z R, A x ^ 2) - ∫ x in ball z R, B x ^ 2 ≤
      ∫ x in ball z R, (ℓ x - m) ^ 2 := by
    rw [← integral_const_mul, ← integral_sub (hA2.const_mul _) hB2]
    refine integral_mono ((hA2.const_mul _).sub hB2) hl2 fun x => ?_
    show 1 / 2 * A x ^ 2 - B x ^ 2 ≤ (ℓ x - m) ^ 2
    rw [hAB x]
    nlinarith [sq_nonneg (A x + 2 * B x)]
  have h1 : euclideanSq ξ * R ^ 2 / 4 * ((1 / 4 : ℝ) ^ d * volume.real (ball z R)) ≤
      ∫ x in ball z R, A x ^ 2 := integral_dot_sub_sq_ge z hR ξ c'
  have hsq : ∑ i, ξ i ^ 2 = euclideanSq ξ := by simp only [euclideanSq, dot, sq]
  have h2 : ∫ x in ball z R, B x ^ 2 ≤
      (d : ℝ) * euclideanSq ξ * (ε ^ 2 * R ^ 2 * volume.real (ball z R)) := by
    have hpt : ∀ x, B x ^ 2 ≤ (d : ℝ) * ∑ i, ξ i ^ 2 * (u i x - (x - z) i - c i) ^ 2 := by
      intro x
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun i => ξ i * (u i x - (x - z) i - c i))
      simpa [B, mul_pow] using this
    have hint : ∀ i, Integrable (fun x => (u i x - (x - z) i - c i) ^ 2) (ballMeasure z R) :=
      fun i => (hmem i).integrable_sq
    calc ∫ x in ball z R, B x ^ 2
        ≤ ∫ x in ball z R, (d : ℝ) * ∑ i, ξ i ^ 2 * (u i x - (x - z) i - c i) ^ 2 :=
          integral_mono hB2
            ((integrable_finsetSum _ fun i _ => (hint i).const_mul _).const_mul _) hpt
      _ = (d : ℝ) * ∑ i, ξ i ^ 2 * ∫ x in ball z R, (u i x - (x - z) i - c i) ^ 2 := by
          rw [integral_const_mul, integral_finsetSum _ fun i _ => (hint i).const_mul _]
          congr 1
          exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
      _ ≤ (d : ℝ) * ∑ i, ξ i ^ 2 * (ε ^ 2 * R ^ 2 * volume.real (ball z R)) := by
          gcongr with i
          exact hsub i
      _ = _ := by
          rw [← Finset.sum_mul, hsq]
          ring
  have h3 : (d : ℝ) * euclideanSq ξ * (ε ^ 2 * R ^ 2 * volume.real (ball z R)) ≤
      (1 / 4 : ℝ) ^ d / 16 * euclideanSq ξ * R ^ 2 * volume.real (ball z R) := by
    have hX : 0 ≤ euclideanSq ξ * R ^ 2 * volume.real (ball z R) :=
      mul_nonneg (mul_nonneg (zero_le_euclideanSq ξ) (sq_nonneg R)) measureReal_nonneg
    calc (d : ℝ) * euclideanSq ξ * (ε ^ 2 * R ^ 2 * volume.real (ball z R))
        = ((d : ℝ) * ε ^ 2) * (euclideanSq ξ * R ^ 2 * volume.real (ball z R)) := by ring
      _ ≤ ((1 / 4 : ℝ) ^ d / 16) * (euclideanSq ξ * R ^ 2 * volume.real (ball z R)) :=
          mul_le_mul_of_nonneg_right hε hX
      _ = _ := by ring
  set G := ∫ x in ball z R, euclideanSq (∑ i, ξ i • W i x) with hG
  have hmain : (1 / 4 : ℝ) ^ d / 16 * euclideanSq ξ * R ^ 2 * volume.real (ball z R) ≤
      (2 ^ d * (2 * R)) ^ 2 * G := by
    calc (1 / 4 : ℝ) ^ d / 16 * euclideanSq ξ * R ^ 2 * volume.real (ball z R)
        ≤ (1 / 2) * (∫ x in ball z R, A x ^ 2) - ∫ x in ball z R, B x ^ 2 := by linarith
      _ ≤ ∫ x in ball z R, (ℓ x - m) ^ 2 := hlow1
      _ = ∫ x in ball z R, (F.1 x - ⨍ y in ball z R, F.1 y) ^ 2 := hosc.symm
      _ ≤ (2 ^ d * (2 * R)) ^ 2 * pairGradEnergy F := hP
      _ = (2 ^ d * (2 * R)) ^ 2 * G := by rw [hE]
  have hR2 : 0 < R ^ 2 := by positivity
  have hc : 0 < (2 ^ d * 2 : ℝ) ^ 2 := by positivity
  have hX : (1 / 4 : ℝ) ^ d / 16 * euclideanSq ξ * volume.real (ball z R) ≤
      (2 ^ d * 2) ^ 2 * G := by
    have h' : ((1 / 4 : ℝ) ^ d / 16 * euclideanSq ξ * volume.real (ball z R)) * R ^ 2 ≤
        ((2 ^ d * 2) ^ 2 * G) * R ^ 2 := by
      calc ((1 / 4 : ℝ) ^ d / 16 * euclideanSq ξ * volume.real (ball z R)) * R ^ 2
          = (1 / 4 : ℝ) ^ d / 16 * euclideanSq ξ * R ^ 2 * volume.real (ball z R) := by ring
        _ ≤ (2 ^ d * (2 * R)) ^ 2 * G := hmain
        _ = ((2 ^ d * 2) ^ 2 * G) * R ^ 2 := by ring
    exact le_of_mul_le_mul_right h' hR2
  calc (1 / 4 : ℝ) ^ d / (16 * (2 ^ d * 2) ^ 2) * euclideanSq ξ * volume.real (ball z R)
      = ((1 / 4 : ℝ) ^ d / 16 * euclideanSq ξ * volume.real (ball z R)) / (2 ^ d * 2) ^ 2 := by
        ring
    _ ≤ G := by
        rw [div_le_iff₀ hc]
        linarith

end QSH
