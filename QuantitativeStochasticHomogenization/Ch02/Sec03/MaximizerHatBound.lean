import QuantitativeStochasticHomogenization.Ch02.Sec03.HatNormAlgebra
import QuantitativeStochasticHomogenization.Ch02.Sec03.HomogenizedInverse
import QuantitativeStochasticHomogenization.Ch02.Sec01.Lemma21

/-!
# The deterministic bound in the proof of Theorem 2.17

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.3, the proof of Theorem 2.17 up to (2.67): there are `K₁, K₂ < ∞` depending on
`(d, Λ)` such that for every `m ∈ ℕ`, `p, q ∈ B₁` and every maximizer `v = v(·, □_m, p, q)` of
(2.9),
`‖∇v - (ā⁻¹q - p)‖_{Ĥ̲⁻¹(□_m)} + ‖a∇v - (q - āp)‖_{Ĥ̲⁻¹(□_m)} ≤
K₁ (1 + 3^m E(m)^{1/2}) + K₂ 3^m (|a(□_m) - ā| + |a*(□_m) - ā|)^{1/2}`
(`vectorHat_defectMaximizer_le`).

The proof is the book's: by Lemma 2.1, `-v(·, □_m, e, 0)` is the minimizer of `μ(□_m, e)`, so
Proposition 1.10 bounds its gradient and flux; by (2.18),
`v(·, □_m, p, q) = v(·, □_m, p, 0) + v(·, □_m, ā⁻¹q, q) - v(·, □_m, ā⁻¹q, 0)`; and
`3^{-m} ‖∇v(·, □_m, ā⁻¹q, q)‖_{Ĥ̲⁻¹(□_m)} ≤ C J(□_m, ā⁻¹q, q)^{1/2}` by (2.19), with
`J(□_m, ā⁻¹q, q) ≤ C (|a(□_m) - ā| + |a*(□_m) - ā|)` by (2.12).
-/

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- The subadditivity of `Ĥ⁻¹(U)` for `F = -G₁ + G₂ + G₃` almost everywhere in `U`. -/
theorem vectorHatNegativeSobolevNorm_le_of_ae_eq {U : Set (Vec d)} {F G₁ G₂ G₃ : Vec d → Vec d}
    (h₁ : MemLp G₁ 2 (volume.restrict U)) (h₂ : MemLp G₂ 2 (volume.restrict U))
    (h₃ : MemLp G₃ 2 (volume.restrict U))
    (hF : ∀ᵐ x ∂(volume.restrict U), F x = -G₁ x + G₂ x + G₃ x) :
    vectorHatNegativeSobolevNorm U F ≤ vectorHatNegativeSobolevNorm U G₁ +
      vectorHatNegativeSobolevNorm U G₂ + vectorHatNegativeSobolevNorm U G₃ := by
  unfold vectorHatNegativeSobolevNorm
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have hae : (fun x => F x j) =ᵐ[volume.restrict U] fun x => (-G₁ x j + G₂ x j) + G₃ x j :=
    hF.mono fun x hx => by
      simp only [hx, Pi.add_apply, Pi.neg_apply]
  rw [hatNegativeSobolevNorm_congr_ae hae]
  have m₁ := h₁.eval j
  have m₂ := h₂.eval j
  have m₃ := h₃.eval j
  calc hatNegativeSobolevNorm U (fun x => (-G₁ x j + G₂ x j) + G₃ x j)
      ≤ hatNegativeSobolevNorm U (fun x => -G₁ x j + G₂ x j) +
          hatNegativeSobolevNorm U (fun x => G₃ x j) :=
        hatNegativeSobolevNorm_add_le (m₁.neg.add m₂) m₃
    _ ≤ hatNegativeSobolevNorm U (fun x => -G₁ x j) + hatNegativeSobolevNorm U (fun x => G₂ x j) +
          hatNegativeSobolevNorm U (fun x => G₃ x j) := by
        gcongr
        exact hatNegativeSobolevNorm_add_le m₁.neg m₂
    _ = _ := by rw [hatNegativeSobolevNorm_neg U (fun x => G₁ x j)]

/-- `|□_m|^{1/d} = 3^m`. -/
theorem toReal_volume_triadicCube_rpow_one_div [NeZero d] (m : ℕ) :
    (volume (triadicCube d m)).toReal ^ ((1 : ℝ) / d) = (3 : ℝ) ^ m := by
  rw [← measureReal_def, volumeReal_triadicCube, one_div]
  exact Real.pow_rpow_inv_natCast (by positivity) (NeZero.ne d)

/-- `⨍_U |∇v|² ≤ 2 J(U, p, q)` for the maximizer `v = v(·, U, p, q)`, by (2.19). -/
theorem IsDefectMaximizer.setAverage_euclideanSq_le {a : CoefficientField d Λ}
    {U : Set (Vec d)} (hUb : Bornology.IsBounded U) (hU0 : volume U ≠ 0) {p q : Vec d}
    {v : Vec d → ℝ} {g : Vec d → Vec d} (hmax : IsDefectMaximizer a U p q v g) :
    ⨍ x in U, euclideanSq (g x) ≤ 2 * dualityDefect a U p q := by
  have hg := hmax.1.1.2.1
  rw [hmax.dualityDefect_eq hUb hU0, setAverage_eq, setAverage_eq, integral_const_mul,
    smul_eq_mul, smul_eq_mul]
  have h := setAverage_mono_of_integrableOn (integrable_euclideanSq_of_memLp hg)
    (integrable_dot_mulVec a U hg) (fun x => (a.elliptic x (g x)).1)
  rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul] at h
  linarith

/-- `⨍_U c f = c ⨍_U f`. -/
theorem setAverage_const_mul_eq (U : Set (Vec d)) (c : ℝ) (f : Vec d → ℝ) :
    ⨍ x in U, c * f x = c * ⨍ x in U, f x := by
  rw [setAverage_eq, setAverage_eq, integral_const_mul, smul_eq_mul, smul_eq_mul]
  ring

/-- **The `J` term**: `‖∇v‖_{Ĥ̲⁻¹(U)} + ‖a∇v‖_{Ĥ̲⁻¹(U)} ≤ d (1 + Λ) |U|^{1/d} (2 J(U, p, q))^{1/2}`
for the maximizer `v = v(·, U, p, q)`. -/
theorem IsDefectMaximizer.vectorHat_add_le {a : CoefficientField d Λ} {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) (hU0 : volume U ≠ 0) (hΛ : 0 ≤ Λ) {p q : Vec d}
    {v : Vec d → ℝ} {g : Vec d → Vec d} (hmax : IsDefectMaximizer a U p q v g) :
    vectorHatNegativeSobolevNorm U g +
        vectorHatNegativeSobolevNorm U (fun x => (a x).mulVec (g x)) ≤
      ENNReal.ofReal ((d : ℝ) * (1 + Λ) *
        ((volume U).toReal ^ ((1 : ℝ) / d) * √(2 * dualityDefect a U p q))) := by
  have hUt : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hg := hmax.1.1.2.1
  have hS := hmax.setAverage_euclideanSq_le hUb hU0
  have hS0 : 0 ≤ ⨍ x in U, euclideanSq (g x) :=
    setAverage_nonneg_of_nonneg fun x => euclideanSq_nonneg (g x)
  have hV0 : 0 ≤ (volume U).toReal ^ ((1 : ℝ) / d) := by positivity
  have hR0 : 0 ≤ √(2 * dualityDefect a U p q) := Real.sqrt_nonneg _
  have hIg := integrable_euclideanSq_of_memLp hg
  have hcomp : ∀ j, hatNegativeSobolevNorm U (fun x => g x j) ≤
      ENNReal.ofReal ((volume U).toReal ^ ((1 : ℝ) / d) * √(2 * dualityDefect a U p q)) := by
    intro j
    refine (hatNegativeSobolevNorm_le_rms hU0 hUt (hg.eval j)).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hV0))
    show √(⨍ x in U, (g x j) ^ 2) ≤ √(2 * dualityDefect a U p q)
    exact Real.sqrt_le_sqrt ((setAverage_mono_of_integrableOn ((hg.eval j).integrable_sq) hIg
      fun x => sq_apply_le_euclideanSq (g x) j).trans hS)
  have hflux : ∀ j, hatNegativeSobolevNorm U (fun x => (a x).mulVec (g x) j) ≤
      ENNReal.ofReal ((volume U).toReal ^ ((1 : ℝ) / d) *
        (Λ * √(2 * dualityDefect a U p q))) := by
    intro j
    have hm := memLp_coefficient_mulVec_apply a hg j
    refine (hatNegativeSobolevNorm_le_rms hU0 hUt hm).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hV0))
    have hpt : ∀ x, ((a x).mulVec (g x) j) ^ 2 ≤ Λ ^ 2 * euclideanSq (g x) := fun x =>
      (sq_apply_le_euclideanSq _ j).trans (euclideanSq_mulVec_le_of_dot_le (a.symmetric x)
        (fun ξ => (euclideanSq_nonneg ξ).trans (a.elliptic x ξ).1)
        (fun ξ => (a.elliptic x ξ).2) (g x))
    have h1 := setAverage_mono_of_integrableOn hm.integrable_sq (hIg.const_mul (Λ ^ 2)) hpt
    rw [setAverage_const_mul_eq] at h1
    have h2 : Λ ^ 2 * ⨍ x in U, euclideanSq (g x) ≤ (Λ * √(2 * dualityDefect a U p q)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith)]
      exact mul_le_mul_of_nonneg_left hS (sq_nonneg Λ)
    show √(⨍ x in U, ((a x).mulVec (g x) j) ^ 2) ≤ Λ * √(2 * dualityDefect a U p q)
    exact (Real.sqrt_le_sqrt (h1.trans h2)).trans_eq (Real.sqrt_sq (mul_nonneg hΛ hR0))
  unfold vectorHatNegativeSobolevNorm
  refine (add_le_add (Finset.sum_le_sum fun j _ => hcomp j)
    (Finset.sum_le_sum fun j _ => hflux j)).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- The bound of Proposition 1.10 without squares: from
`3^{-2m} X² + 3^{-2m} Y² ≤ C 3^{-2m} + C E`, `X + Y ≤ 2 C^{1/2} (1 + 3^m E^{1/2})`. -/
theorem add_le_of_proposition_1_10 {X Y : ℝ≥0∞} {C E : ℝ} (hC : 0 ≤ C) (hE : 0 ≤ E) (m : ℕ)
    (h : ENNReal.ofReal (((3 : ℝ) ^ m)⁻¹ ^ 2) * X ^ 2 +
        ENNReal.ofReal (((3 : ℝ) ^ m)⁻¹ ^ 2) * Y ^ 2 ≤
      ENNReal.ofReal (C * ((3 : ℝ) ^ m)⁻¹ ^ 2 + C * E)) :
    X + Y ≤ ENNReal.ofReal (2 * (√C * (1 + (3 : ℝ) ^ m * √E))) := by
  have ht : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hr : (0 : ℝ) < ((3 : ℝ) ^ m)⁻¹ ^ 2 := by positivity
  have hB : 0 ≤ C * ((3 : ℝ) ^ m)⁻¹ ^ 2 + C * E := by positivity
  have hX := le_ofReal_sqrt_of_mul_sq_le hr hB ((self_le_add_right _ _).trans h)
  have hY := le_ofReal_sqrt_of_mul_sq_le hr hB ((self_le_add_left _ _).trans h)
  have hb0 : 0 ≤ √C * (1 + (3 : ℝ) ^ m * √E) := by positivity
  have key : √((C * ((3 : ℝ) ^ m)⁻¹ ^ 2 + C * E) / ((3 : ℝ) ^ m)⁻¹ ^ 2) ≤
      √C * (1 + (3 : ℝ) ^ m * √E) := by
    refine (Real.sqrt_le_sqrt ?_).trans_eq (Real.sqrt_sq hb0)
    rw [div_le_iff₀ hr]
    have htt : (3 : ℝ) ^ m * ((3 : ℝ) ^ m)⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
    have e : (√C * (1 + (3 : ℝ) ^ m * √E)) ^ 2 * ((3 : ℝ) ^ m)⁻¹ ^ 2 =
        C * (((3 : ℝ) ^ m)⁻¹ ^ 2 + 2 * ((3 : ℝ) ^ m)⁻¹ * √E + E) := by
      calc (√C * (1 + (3 : ℝ) ^ m * √E)) ^ 2 * ((3 : ℝ) ^ m)⁻¹ ^ 2
          = √C ^ 2 * (((3 : ℝ) ^ m)⁻¹ + √E * ((3 : ℝ) ^ m * ((3 : ℝ) ^ m)⁻¹)) ^ 2 := by ring
        _ = C * (((3 : ℝ) ^ m)⁻¹ ^ 2 + 2 * ((3 : ℝ) ^ m)⁻¹ * √E + √E ^ 2) := by
          rw [Real.sq_sqrt hC, htt, mul_one]
          ring
        _ = _ := by rw [Real.sq_sqrt hE]
    rw [e]
    have : 0 ≤ C * (2 * ((3 : ℝ) ^ m)⁻¹ * √E) := by positivity
    nlinarith
  calc X + Y ≤ ENNReal.ofReal (√C * (1 + (3 : ℝ) ^ m * √E)) +
        ENNReal.ofReal (√C * (1 + (3 : ℝ) ^ m * √E)) :=
        add_le_add (hX.trans (ENNReal.ofReal_le_ofReal key))
          (hY.trans (ENNReal.ofReal_le_ofReal key))
    _ = _ := by rw [← ENNReal.ofReal_add hb0 hb0, two_mul]

/-- **The deterministic bound behind (2.67)**: there are `K₁, K₂ > 0` depending on `(d, Λ)`
such that for every law `P` satisfying the assumptions, `m ∈ ℕ`, `p, q ∈ B₁` and every maximizer
`v = v(·, □_m, p, q)` of (2.9) of gradient `g`,
`‖∇v - (ā⁻¹q - p)‖_{Ĥ̲⁻¹(□_m)} + ‖a∇v - (q - āp)‖_{Ĥ̲⁻¹(□_m)} ≤
K₁ (1 + 3^m E(m)^{1/2}) + K₂ 3^m (|a(□_m) - ā| + |a*(□_m) - ā|)^{1/2}`, with `E(m)` of (1.39). -/
theorem vectorHat_defectMaximizer_le [NeZero d] :
    ∃ K₁ K₂ : ℝ, 0 < K₁ ∧ 0 < K₂ ∧ ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∀ (m : ℕ) (a : CoefficientField d Λ) (p q : Vec d), p ∈ originBall d 1 →
        q ∈ originBall d 1 → ∀ (v : Vec d → ℝ) (g : Vec d → Vec d),
        IsDefectMaximizer a (triadicCube d m) p q v g →
        vectorHatNegativeSobolevNorm (triadicCube d m)
            (fun x => g x - ((homogenizedMatrix P)⁻¹.mulVec q - p)) +
          vectorHatNegativeSobolevNorm (triadicCube d m)
            (fun x => (a x).mulVec (g x) - (q - (homogenizedMatrix P).mulVec p)) ≤
        ENNReal.ofReal (K₁ * (1 + (3 : ℝ) ^ m * √(coarseDeviation P m a)) +
          K₂ * ((3 : ℝ) ^ m *
            √(frobeniusNorm (coarseMatrix a (triadicCube d m) - homogenizedMatrix P) +
              frobeniusNorm (coarseDualMatrix a (triadicCube d m) - homogenizedMatrix P)))) := by
  by_cases hΛ1 : 1 ≤ Λ
  swap
  · exact ⟨1, 1, one_pos, one_pos, fun P _ m a => absurd (one_le_of_coefficientField a) hΛ1⟩
  have hΛ : 0 ≤ Λ := zero_le_one.trans hΛ1
  obtain ⟨C, hC, h110⟩ := proposition_1_10 (d := d) (Λ := Λ)
  have hCst0 : 0 ≤ structuralMatrixConst d Λ := structuralMatrixConst_nonneg d Λ
  refine ⟨4 * √C + 1, (d : ℝ) * (1 + Λ) * √(1 + structuralMatrixConst d Λ) + 1, by positivity,
    by positivity, ?_⟩
  intro P hP m a p q hp hq v g hmax
  have hUo : IsOpen (triadicCube d m) := isOpen_triadicCube' m
  have hUb : Bornology.IsBounded (triadicCube d m) := isBounded_triadicCube m
  have hUc : Convex ℝ (triadicCube d m) := convex_triadicCube m
  have hne : (triadicCube d m).Nonempty := triadicCube_nonempty m
  have hU0 := volume_triadicCube_ne_zero d m
  have : IsFiniteMeasure (volume.restrict (triadicCube d m)) :=
    isFiniteMeasure_restrict.mpr (volume_triadicCube_ne_top d m)
  obtain ⟨q', hq'⟩ : ∃ q', q' = (homogenizedMatrix P)⁻¹.mulVec q := ⟨_, rfl⟩
  have hAq : (homogenizedMatrix P).mulVec q' = q := by
    rw [hq']
    exact homogenizedMatrix_mulVec_inv_mulVec hP hΛ q
  have hq'1 : q' ∈ originBall d 1 := by
    have h := euclideanSq_homogenizedMatrix_inv_mulVec_le hP hΛ q
    rw [← hq'] at h
    show √(euclideanSq q') < 1
    exact lt_of_le_of_lt (Real.sqrt_le_sqrt h) hq
  rw [← hq']
  subst hAq
  obtain ⟨u₁, gD₁, hD₁⟩ := exists_isDirichletMinimizer a hUb hU0 p
  obtain ⟨u₃, gD₃, hD₃⟩ := exists_isDirichletMinimizer a hUb hU0 q'
  have h₁ := (lemma_2_1 a hUo hUb hUc hne p 0).2.2 _ _ u₁ gD₁
    (isDualMaximizer_zero a hUo hUb hne) hD₁
  have h₃ := (lemma_2_1 a hUo hUb hUc hne q' 0).2.2 _ _ u₃ gD₃
    (isDualMaximizer_zero a hUo hUb hne) hD₃
  obtain ⟨v₂, g₂, h₂⟩ := exists_isDefectMaximizer a hUo hUb hUc hne q'
    ((homogenizedMatrix P).mulVec q')
  have h₁₂₃ := (h₁.linearCombination hUo hUb hUc hne h₂ 1 1).linearCombination hUo hUb hUc hne
    h₃ 1 (-1)
  have ep : (1 : ℝ) • ((1 : ℝ) • p + (1 : ℝ) • q') + (-1 : ℝ) • q' = p := by simp
  have eq : (1 : ℝ) • ((1 : ℝ) • (0 : Vec d) + (1 : ℝ) • (homogenizedMatrix P).mulVec q') +
      (-1 : ℝ) • (0 : Vec d) = (homogenizedMatrix P).mulVec q' := by simp
  rw [ep, eq] at h₁₂₃
  have hae := hmax.ae_eq hUb hU0 h₁₂₃
  have mD₁ : MemLp gD₁ 2 (volume.restrict (triadicCube d m)) := hD₁.1.2.1
  have mD₃ : MemLp gD₃ 2 (volume.restrict (triadicCube d m)) := hD₃.1.2.1
  have m₂ : MemLp g₂ 2 (volume.restrict (triadicCube d m)) := h₂.1.1.2.1
  have hgrad := vectorHatNegativeSobolevNorm_le_of_ae_eq
    (F := fun x => g x - (q' - p)) (G₁ := gD₁) (G₂ := gD₃) (G₃ := g₂) mD₁ mD₃ m₂ (by
      filter_upwards [hae] with x hx
      rw [hx]
      simp only [one_smul, neg_smul, zero_sub, neg_neg]
      abel)
  have hflux := vectorHatNegativeSobolevNorm_le_of_ae_eq
    (F := fun x => (a x).mulVec (g x) -
      ((homogenizedMatrix P).mulVec q' - (homogenizedMatrix P).mulVec p))
    (G₁ := fun x => (a x).mulVec (p + gD₁ x) - (homogenizedMatrix P).mulVec p)
    (G₂ := fun x => (a x).mulVec (q' + gD₃ x) - (homogenizedMatrix P).mulVec q')
    (G₃ := fun x => (a x).mulVec (g₂ x))
    ((memLp_mulVec_of_memLp a ((memLp_const p).add mD₁)).sub (memLp_const _))
    ((memLp_mulVec_of_memLp a ((memLp_const q').add mD₃)).sub (memLp_const _))
    (memLp_mulVec_of_memLp a m₂) (by
      filter_upwards [hae] with x hx
      rw [hx]
      simp only [one_smul, neg_smul, zero_sub, neg_neg, Matrix.mulVec_add, Matrix.mulVec_neg]
      abel)
  have hE0 : 0 ≤ coarseDeviation P m a := sq_nonneg _
  have hb₁ := add_le_of_proposition_1_10 hC hE0 m (h110 P hP m a p hp u₁ gD₁ hD₁)
  have hb₃ := add_le_of_proposition_1_10 hC hE0 m (h110 P hP m a q' hq'1 u₃ gD₃ hD₃)
  have hJ := h₂.vectorHat_add_le hUb hU0 hΛ
  rw [toReal_volume_triadicCube_rpow_one_div] at hJ
  have hJF := (dualityDefect_homogenizedMatrix_le hP a hUo hUb hUc hne hq'1).2
  set F := frobeniusNorm (coarseMatrix a (triadicCube d m) - homogenizedMatrix P) +
    frobeniusNorm (coarseDualMatrix a (triadicCube d m) - homogenizedMatrix P) with hF
  set J := dualityDefect a (triadicCube d m) q' ((homogenizedMatrix P).mulVec q') with hJdef
  have hF0 : 0 ≤ F := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have ht : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hsJ : √(2 * J) ≤ √(1 + structuralMatrixConst d Λ) * √F := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hX : (d : ℝ) * (1 + Λ) * ((3 : ℝ) ^ m * √(2 * J)) ≤
      ((d : ℝ) * (1 + Λ) * √(1 + structuralMatrixConst d Λ)) * ((3 : ℝ) ^ m * √F) := by
    calc (d : ℝ) * (1 + Λ) * ((3 : ℝ) ^ m * √(2 * J))
        = ((d : ℝ) * (1 + Λ) * (3 : ℝ) ^ m) * √(2 * J) := by ring
      _ ≤ ((d : ℝ) * (1 + Λ) * (3 : ℝ) ^ m) * (√(1 + structuralMatrixConst d Λ) * √F) :=
          mul_le_mul_of_nonneg_left hsJ (by positivity)
      _ = _ := by ring
  have hsE : 0 ≤ (3 : ℝ) ^ m * √(coarseDeviation P m a) := by positivity
  have hsF : 0 ≤ (3 : ℝ) ^ m * √F := by positivity
  calc _ ≤ (vectorHatNegativeSobolevNorm (triadicCube d m) gD₁ +
          vectorHatNegativeSobolevNorm (triadicCube d m) gD₃ +
          vectorHatNegativeSobolevNorm (triadicCube d m) g₂) +
        (vectorHatNegativeSobolevNorm (triadicCube d m)
            (fun x => (a x).mulVec (p + gD₁ x) - (homogenizedMatrix P).mulVec p) +
          vectorHatNegativeSobolevNorm (triadicCube d m)
            (fun x => (a x).mulVec (q' + gD₃ x) - (homogenizedMatrix P).mulVec q') +
          vectorHatNegativeSobolevNorm (triadicCube d m) (fun x => (a x).mulVec (g₂ x))) :=
        add_le_add hgrad hflux
    _ = (vectorHatNegativeSobolevNorm (triadicCube d m) gD₁ +
          vectorHatNegativeSobolevNorm (triadicCube d m)
            (fun x => (a x).mulVec (p + gD₁ x) - (homogenizedMatrix P).mulVec p)) +
        (vectorHatNegativeSobolevNorm (triadicCube d m) gD₃ +
          vectorHatNegativeSobolevNorm (triadicCube d m)
            (fun x => (a x).mulVec (q' + gD₃ x) - (homogenizedMatrix P).mulVec q')) +
        (vectorHatNegativeSobolevNorm (triadicCube d m) g₂ +
          vectorHatNegativeSobolevNorm (triadicCube d m) (fun x => (a x).mulVec (g₂ x))) := by
        ring
    _ ≤ ENNReal.ofReal (2 * (√C * (1 + (3 : ℝ) ^ m * √(coarseDeviation P m a)))) +
        ENNReal.ofReal (2 * (√C * (1 + (3 : ℝ) ^ m * √(coarseDeviation P m a)))) +
        ENNReal.ofReal ((d : ℝ) * (1 + Λ) * ((3 : ℝ) ^ m * √(2 * J))) :=
        add_le_add (add_le_add hb₁ hb₃) hJ
    _ = ENNReal.ofReal (2 * (√C * (1 + (3 : ℝ) ^ m * √(coarseDeviation P m a))) +
        2 * (√C * (1 + (3 : ℝ) ^ m * √(coarseDeviation P m a))) +
        (d : ℝ) * (1 + Λ) * ((3 : ℝ) ^ m * √(2 * J))) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith

end QSH
