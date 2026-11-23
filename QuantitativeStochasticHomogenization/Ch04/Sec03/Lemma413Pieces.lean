import QuantitativeStochasticHomogenization.Ch04.Sec03.GaussianJensen

/-!
# Pieces of the proof of Lemma 4.13

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, Lemma 4.13: bounds used in the probabilistic step of the proof here.

* `abs_fluxPolarizationVector_le`: the flux polarization vector is bounded by `8 (Λ + 1)`
  componentwise, for loads in the open unit ball;
* `isUnit_det_of_near_inverse`: a matrix `B` with `|(B - ā⁻¹) v| ≤ η |v|` and `Λ η ≤ 1/2` is
  invertible with `|B⁻¹ w| ≤ 2Λ |w|`, when `|ā z| ≤ Λ |z|`;
* `euclideanNorm_homogenized_mulVec_le`: `|ā z| ≤ Λ |z|` from `ξ·āξ ≤ Λ|ξ|²` and the symmetry.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

theorem abs_fluxPolarizationVector_le (a : CoefficientField d Λ) (hΛ : 0 ≤ Λ) (y : Vec d)
    {r : ℝ} (hr : 0 < r) {p q : Vec d} (hp : euclideanNorm p < 1) (hq : euclideanNorm q < 1)
    (i : Fin d) : |fluxPolarizationVector a y r p q i| ≤ 8 * (Λ + 1) := by
  have hb : ∀ p' q' : Vec d, euclideanNorm p' ≤ 1 → euclideanNorm q' ≤ 1 →
      0 ≤ J1Heat a y r p' q' ∧ J1Heat a y r p' q' ≤ Λ + 1 := by
    intro p' q' hp' hq'
    obtain ⟨h0, h1⟩ := J1Heat_nonneg_le a y hr p' q'
    have hp2 : euclideanSq p' ≤ 1 := by
      rw [← euclideanNorm_sq]; nlinarith [euclideanNorm_nonneg p']
    have hq2 : euclideanSq q' ≤ 1 := by
      rw [← euclideanNorm_sq]; nlinarith [euclideanNorm_nonneg q']
    exact ⟨h0, by nlinarith [euclideanSq_nonneg p']⟩
  have hhalf : ∀ v : Vec d, euclideanNorm v ≤ 2 → euclideanNorm ((1 / 2 : ℝ) • v) ≤ 1 := by
    intro v hv
    rw [euclideanNorm_smul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have hpe : euclideanNorm (p + unitVector i) ≤ 2 :=
    (euclideanNorm_add_le p (unitVector i)).trans (by rw [euclideanNorm_unitVector]; linarith)
  have he : euclideanNorm (unitVector i : Vec d) ≤ 2 := by rw [euclideanNorm_unitVector]; norm_num
  have h00 : euclideanNorm (0 : Vec d) ≤ 1 := by simp [euclideanNorm, euclideanSq, dot]
  obtain ⟨h1a, h1b⟩ := hb ((1 / 2 : ℝ) • (p + unitVector i)) ((1 / 2 : ℝ) • q)
    (hhalf _ hpe) (hhalf q (by linarith))
  obtain ⟨h2a, h2b⟩ := hb ((1 / 2 : ℝ) • p) ((1 / 2 : ℝ) • q) (hhalf p (by linarith))
    (hhalf q (by linarith))
  obtain ⟨h3a, h3b⟩ := hb ((1 / 2 : ℝ) • unitVector i) 0 (hhalf _ he) h00
  simp only [fluxPolarizationVector]
  rw [abs_le]
  constructor <;> nlinarith

/-- `|ā z| ≤ Λ |z|` for a symmetric `ā` with `0 ≤ ξ·āξ ≤ Λ|ξ|²`. -/
theorem euclideanNorm_homogenized_mulVec_le {A : Mat d} (hAsymm : A.transpose = A)
    (hA : HomogenizedMatrixBounds A Λ) (hΛ : 0 ≤ Λ) (z : Vec d) :
    euclideanNorm (A.mulVec z) ≤ Λ * euclideanNorm z := by
  refine euclideanNorm_mulVec_le_of_abs_dot_le hAsymm hΛ (fun u => ?_) z
  obtain ⟨h1, h2⟩ := hA u
  rw [abs_of_nonneg ((euclideanSq_nonneg u).trans h1)]
  exact h2

/-- **A perturbation of `ā⁻¹` is invertible**: if `|(B - ā⁻¹) v| ≤ η |v|` for all `v`, with
`|ā z| ≤ Λ |z|`, `Λ > 0` and `Λ η ≤ 1/2`, then `B` is invertible and `|B⁻¹ w| ≤ 2Λ |w|`. -/
theorem isUnit_det_of_near_inverse {A B : Mat d} (hAdet : IsUnit A.det) (hΛ : 0 < Λ)
    (hAop : ∀ z, euclideanNorm (A.mulVec z) ≤ Λ * euclideanNorm z) {η : ℝ}
    (hη : Λ * η ≤ 1 / 2) (hB : ∀ v, euclideanNorm ((B - A⁻¹).mulVec v) ≤ η * euclideanNorm v) :
    IsUnit B.det ∧ ∀ w, euclideanNorm (B⁻¹.mulVec w) ≤ 2 * Λ * euclideanNorm w := by
  -- `|B v| ≥ |v| / (2Λ)`
  have hlow : ∀ v, euclideanNorm v ≤ 2 * Λ * euclideanNorm (B.mulVec v) := by
    intro v
    have h1 : euclideanNorm v ≤ Λ * euclideanNorm (A⁻¹.mulVec v) := by
      have := hAop (A⁻¹.mulVec v)
      rwa [mulVec_inv_mulVec hAdet v] at this
    have h2 : euclideanNorm (A⁻¹.mulVec v) ≤ euclideanNorm (B.mulVec v) + η * euclideanNorm v := by
      have := euclideanNorm_sub_le (B.mulVec v) ((B - A⁻¹).mulVec v)
      have hBv := hB v
      rw [Matrix.sub_mulVec] at this hBv
      rw [sub_sub_cancel] at this
      linarith
    have h3 := euclideanNorm_nonneg v
    nlinarith
  have hinj : ∀ v, B.mulVec v = 0 → v = 0 := by
    intro v hv
    have h := hlow v
    rw [hv] at h
    have h0 : euclideanNorm (0 : Vec d) = 0 := by simp [euclideanNorm, euclideanSq, dot]
    rw [h0, mul_zero] at h
    exact eq_zero_of_euclideanSq_le_zero (by
      rw [← euclideanNorm_sq]; nlinarith [euclideanNorm_nonneg v])
  have hdet : IsUnit B.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    exact hv0 (hinj v hv)
  refine ⟨hdet, fun w => ?_⟩
  have := hlow (B⁻¹.mulVec w)
  rwa [mulVec_inv_mulVec hdet w] at this

theorem euclideanNorm_le_of_abs_le {v : Vec d} {c : ℝ} (hc : 0 ≤ c) (h : ∀ k, |v k| ≤ c) :
    euclideanNorm v ≤ Real.sqrt d * c := by
  rw [euclideanNorm, show Real.sqrt d * c = Real.sqrt (d * c ^ 2) by
    rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hc]]
  exact Real.sqrt_le_sqrt (euclideanSq_le_of_abs_le h)

section MeanNear

variable {P : Measure (CoefficientField d Λ)}

/-- **The mean of `2 m(0, eᵢ/2)` is close to `ā⁻¹ eᵢ`**: if at the center `y` and the scale `r` the
bounds (3.101)–(3.103) hold with error `ε` (`ε ≤ 1/4`, `√d ε ≤ 1/2`) outside a measurable bad set
`Bad`, then the mean is within `√d ((9 + √d) ε + (16 (Λ + 1) + 1) P(Bad))` of `ā⁻¹ eᵢ`. -/
theorem mean_polarization_near_inverse [IsProbabilityMeasure P] (S : HomogenizationData P)
    (hΛ : 0 ≤ Λ) (hA : HomogenizedMatrixBounds S.homogenized Λ)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (y : Vec d) {r : ℝ} (hr : 0 < r)
    (hmeasJ : ∀ p q : Vec d, AEStronglyMeasurable (fun a => J1Heat a y r p q) P)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (hεd : Real.sqrt d * ε ≤ 1 / 2) {Bad : Set (CoefficientField d Λ)} (hBad : MeasurableSet Bad)
    (hgood : ∀ᵐ a ∂P, a ∉ Bad →
      GaussianAverageBounds a S.homogenized (correctedField S a) y r ε) (i : Fin d) :
    euclideanNorm ((fun k => ∫ a, ((2 : ℝ) • polarizationVector a y r 0
        ((1 / 2 : ℝ) • unitVector i)) k ∂P) - S.homogenized⁻¹.mulVec (unitVector i)) ≤
      Real.sqrt d * ((9 + Real.sqrt d) * ε + (16 * (Λ + 1) + 1) * P.real Bad) := by
  set D := S.homogenized with hD
  set B : CoefficientField d Λ → Vec d :=
    fun a => (2 : ℝ) • polarizationVector a y r 0 ((1 / 2 : ℝ) • unitVector i) with hBdef
  have hnorm : euclideanNorm ((1 / 2 : ℝ) • (unitVector i : Vec d)) < 1 := by
    rw [euclideanNorm_smul, euclideanNorm_unitVector]; norm_num
  have h00 : euclideanNorm (0 : Vec d) < 1 := by simp [euclideanNorm, euclideanSq, dot]
  have hBk : ∀ a k, |B a k| ≤ 16 * (Λ + 1) := by
    intro a k
    have := abs_polarizationVector_le a hΛ y hr h00 hnorm k
    simp only [hBdef, Pi.smul_apply, smul_eq_mul, abs_mul, abs_two]
    linarith
  have hDe : euclideanNorm (D⁻¹.mulVec (unitVector i)) ≤ 1 := by
    have := euclideanNorm_inv_mulVec_le (fun ξ => (hA ξ).1) (unitVector i)
    rwa [euclideanNorm_unitVector] at this
  have hBm : ∀ k, AEStronglyMeasurable (fun a => B a k) P := fun k => by
    simp only [hBdef, Pi.smul_apply, smul_eq_mul, polarizationVector]
    exact ((((hmeasJ _ _).sub (hmeasJ _ _)).sub (hmeasJ _ _)).const_mul 4).const_mul 2
  have hBi : ∀ k, Integrable (fun a => B a k) P := fun k =>
    Integrable.of_bound (hBm k) (16 * (Λ + 1))
      (Filter.Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hBk a k)
  set c : ℝ := (9 + Real.sqrt d) * ε + (16 * (Λ + 1) + 1) * P.real Bad with hc
  have hc0 : 0 ≤ c := by positivity
  refine euclideanNorm_le_of_abs_le hc0 fun k => ?_
  simp only [Pi.sub_apply]
  have hdiff : (∫ a, B a k ∂P) - (D⁻¹.mulVec (unitVector i)) k =
      ∫ a, (B a k - (D⁻¹.mulVec (unitVector i)) k) ∂P := by
    rw [integral_sub (hBi k) (integrable_const _), integral_const, probReal_univ, one_smul]
  rw [hdiff]
  refine (abs_integral_le_integral_abs).trans ?_
  have hpt : ∀ᵐ a ∂P, |B a k - (D⁻¹.mulVec (unitVector i)) k| ≤
      (9 + Real.sqrt d) * ε + (16 * (Λ + 1) + 1) * Bad.indicator (fun _ => (1 : ℝ)) a := by
    filter_upwards [hgood, hspan] with a ha hsa
    by_cases hab : a ∈ Bad
    · rw [Set.indicator_of_mem hab, mul_one]
      have h1 := abs_sub (B a k) ((D⁻¹.mulVec (unitVector i)) k)
      have h2 := (abs_apply_le_euclideanNorm _ k).trans hDe
      have h3 := hBk a k
      have h4 : 0 ≤ (9 + Real.sqrt d) * ε := by positivity
      linarith
    · rw [Set.indicator_of_notMem hab, mul_zero, add_zero]
      have h := polarizationVector_near_inverse S a hA hsa y r hε0 hε hεd (ha hab) i
      have := abs_apply_le_euclideanNorm (B a - D⁻¹.mulVec (unitVector i)) k
      simp only [Pi.sub_apply] at this
      linarith
  have hint2 : Integrable (fun a => (9 + Real.sqrt d) * ε +
      (16 * (Λ + 1) + 1) * Bad.indicator (fun _ => (1 : ℝ)) a) P :=
    (integrable_const _).add (((integrable_const (1 : ℝ)).indicator hBad).const_mul _)
  calc ∫ a, |B a k - (D⁻¹.mulVec (unitVector i)) k| ∂P
      ≤ ∫ a, ((9 + Real.sqrt d) * ε + (16 * (Λ + 1) + 1) * Bad.indicator (fun _ => (1 : ℝ)) a) ∂P :=
        integral_mono_ae ((hBi k).sub (integrable_const _)).abs hint2 hpt
    _ = c := by
        rw [integral_add (integrable_const _) (((integrable_const (1 : ℝ)).indicator hBad).const_mul _),
          integral_const, probReal_univ, one_smul, integral_const_mul, integral_indicator hBad,
          setIntegral_const, smul_eq_mul, mul_one, hc]

end MeanNear

/-- `∑ |vᵢ| ≤ √d |v|`. -/
theorem sum_abs_le_sqrt_mul_euclideanNorm (v : Vec d) :
    ∑ i, |v i| ≤ Real.sqrt d * euclideanNorm v := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun i => |v i|)
  simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    one_mul, sq_abs] at h
  have h2 : (∑ i, v i ^ 2) = euclideanNorm v ^ 2 := by
    rw [euclideanNorm_sq]; simp only [euclideanSq, dot, sq]
  rw [h2] at h
  have h0 : 0 ≤ ∑ i, |v i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have h3 : 0 ≤ Real.sqrt d * euclideanNorm v :=
    mul_nonneg (Real.sqrt_nonneg _) (euclideanNorm_nonneg v)
  apply abs_le_of_sq_le_sq' _ h3 |>.2
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  exact h

/-- **Columns close imply operators close**: if `|B eᵢ - A eᵢ| ≤ δ` for all `i`, then
`|(B - A) v| ≤ √d δ |v|`. -/
theorem euclideanNorm_sub_mulVec_le_of_columns {A B : Mat d} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ i, euclideanNorm (B.mulVec (unitVector i) - A.mulVec (unitVector i)) ≤ δ) (v : Vec d) :
    euclideanNorm ((B - A).mulVec v) ≤ Real.sqrt d * δ * euclideanNorm v := by
  have hv : v = ∑ i, v i • (unitVector i : Vec d) := by
    funext k; simp [unitVector, Pi.single_apply, Finset.sum_apply]
  have hsum : (B - A).mulVec v = ∑ i, v i • (B.mulVec (unitVector i) - A.mulVec (unitVector i)) := by
    conv_lhs => rw [hv]
    rw [Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, Matrix.sub_mulVec]
  rw [hsum]
  have hnorm : ∀ (s : Finset (Fin d)) (w : Fin d → Vec d),
      euclideanNorm (∑ i ∈ s, w i) ≤ ∑ i ∈ s, euclideanNorm (w i) := by
    intro s w
    induction s using Finset.induction_on with
    | empty => simp [euclideanNorm, euclideanSq, dot]
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (euclideanNorm_add_le _ _).trans (by linarith)
  refine (hnorm _ _).trans ?_
  calc ∑ i, euclideanNorm (v i • (B.mulVec (unitVector i) - A.mulVec (unitVector i)))
      ≤ ∑ i, |v i| * δ := Finset.sum_le_sum fun i _ => by
        rw [euclideanNorm_smul]; exact mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)
    _ = (∑ i, |v i|) * δ := by rw [Finset.sum_mul]
    _ ≤ Real.sqrt d * euclideanNorm v * δ :=
        mul_le_mul_of_nonneg_right (sum_abs_le_sqrt_mul_euclideanNorm v) hδ
    _ = Real.sqrt d * δ * euclideanNorm v := by ring

theorem euclideanNorm_finset_sum_le (s : Finset (Fin d)) (w : Fin d → Vec d) :
    euclideanNorm (∑ i ∈ s, w i) ≤ ∑ i ∈ s, euclideanNorm (w i) := by
  induction s using Finset.induction_on with
  | empty => simp [euclideanNorm, euclideanSq, dot]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (euclideanNorm_add_le _ _).trans (by linarith)

section GoodCommutator

variable {P : Measure (CoefficientField d Λ)}

/-- **The commutator at a good scale against a matrix `D₀` matching the means**: if
`D₀ (E Bᵢ) = E Cᵢ` with `Bᵢ = 2 m(0, eᵢ/2)`, `Cᵢ = 2 f(0, eᵢ/2)`, and `|D₀ w| ≤ K₀ |w|`, then
`|F eⱼ - D₀ P eⱼ| ≤ 2 √d (Λ + 1) ∑ᵢ (|Cᵢ - E Cᵢ| + K₀ |Bᵢ - E Bᵢ|)`. -/
theorem commutator_good_le (S : HomogenizationData P) (a : CoefficientField d Λ)
    (hΛ : 0 ≤ Λ) (hA : HomogenizedMatrixBounds S.homogenized Λ)
    (hspan : GradientsOfA1AreCorrected S a) (y : Vec d) (r : ℝ) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 4) (hεd : Real.sqrt d * ε ≤ 1 / 2)
    (havg : GaussianAverageBounds a S.homogenized (correctedField S a) y r ε)
    (D₀ : Mat d) {K₀ : ℝ} (hK₀ : 0 ≤ K₀) (hD₀op : ∀ w, euclideanNorm (D₀.mulVec w) ≤ K₀ * euclideanNorm w)
    (mB mC : Fin d → Vec d) (hD₀m : ∀ i, D₀.mulVec (mB i) = mC i) (j : Fin d) :
    euclideanNorm (fluxAverage S a y r (unitVector j) -
        D₀.mulVec (gradientAverage S a y r (unitVector j))) ≤
      2 * (Real.sqrt d * (Λ + 1)) * ∑ i,
        (euclideanNorm ((2 : ℝ) • fluxPolarizationVector a y r 0 ((1 / 2 : ℝ) • unitVector i) - mC i) +
          K₀ * euclideanNorm ((2 : ℝ) • polarizationVector a y r 0 ((1 / 2 : ℝ) • unitVector i) -
            mB i)) := by
  obtain ⟨q, hq, hPj, hFj⟩ := corrected_averages_eq_sum S a hΛ hA hspan y r hε0 hε hεd havg j
  set Bv : Fin d → Vec d := fun i => (2 : ℝ) • polarizationVector a y r 0 ((1 / 2 : ℝ) • unitVector i)
  set Cv : Fin d → Vec d :=
    fun i => (2 : ℝ) • fluxPolarizationVector a y r 0 ((1 / 2 : ℝ) • unitVector i)
  rw [hPj, hFj]
  have hexp : (∑ i, q i • Cv i) - D₀.mulVec (∑ i, q i • Bv i) =
      ∑ i, q i • ((Cv i - mC i) - D₀.mulVec (Bv i - mB i)) := by
    rw [Matrix.mulVec_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hD₀m i, ← smul_sub]
    congr 1
    abel
  rw [hexp]
  refine (euclideanNorm_finset_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [euclideanNorm_smul]
  have h1 : |q i| ≤ 2 * (Real.sqrt d * (Λ + 1)) := (abs_apply_le_euclideanNorm q i).trans hq
  have h2 : euclideanNorm ((Cv i - mC i) - D₀.mulVec (Bv i - mB i)) ≤
      euclideanNorm (Cv i - mC i) + K₀ * euclideanNorm (Bv i - mB i) :=
    (euclideanNorm_sub_le _ _).trans (by linarith [hD₀op (Bv i - mB i)])
  have h3 : 0 ≤ euclideanNorm ((Cv i - mC i) - D₀.mulVec (Bv i - mB i)) := euclideanNorm_nonneg _
  have h4 : 0 ≤ euclideanNorm (Cv i - mC i) + K₀ * euclideanNorm (Bv i - mB i) :=
    add_nonneg (euclideanNorm_nonneg _) (mul_nonneg hK₀ (euclideanNorm_nonneg _))
  calc |q i| * euclideanNorm ((Cv i - mC i) - D₀.mulVec (Bv i - mB i))
      ≤ 2 * (Real.sqrt d * (Λ + 1)) * (euclideanNorm (Cv i - mC i) +
          K₀ * euclideanNorm (Bv i - mB i)) :=
        mul_le_mul h1 h2 h3 (by positivity)

end GoodCommutator

end QSH
