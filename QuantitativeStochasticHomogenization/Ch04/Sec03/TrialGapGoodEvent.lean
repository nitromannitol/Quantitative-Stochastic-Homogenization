import QuantitativeStochasticHomogenization.Ch04.Sec03.TrialGapAlgebra

/-!
# The trial gap above the scale of Proposition 3.21

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, the deterministic step of the proof of Proposition 4.10 used here.

At a mask `Φ_{y,r}` where the corrected fields satisfy the bounds (3.101)–(3.103) with an error
`ε ≤ 1/4` and the gradients of `A₁` are the corrected fields, the energy matrix is between
`(1 - 2ε)` and `Λ + 2ε`, the gradient average `P v = ∫ Φ_{y,r} G v` satisfies `|v| ≤ (4/3)|P v|`,
and the gap to the trial at a slope `k` is at most `(8/9)(Λ + 1/2) |P k - m|²`, where
`m = ∫ Φ_{y,r} G c` is the averaged gradient of the maximizer (`trialGap_le_of_averages`); by
(4.16), `h·m = J₁(p, q + h) - J₁(p, q) - J₁(0, h)` (`dot_maximizerAverage`).
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## Linearity of the family -/

theorem fieldOf_add (W : Fin d → Vec d → Vec d) (ξ η x : Vec d) :
    fieldOf W (ξ + η) x = fieldOf W ξ x + fieldOf W η x := by
  simp only [fieldOf, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem fieldOf_sub (W : Fin d → Vec d → Vec d) (ξ η x : Vec d) :
    fieldOf W (ξ - η) x = fieldOf W ξ x - fieldOf W η x := by
  simp only [fieldOf, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem fieldOf_unitVector (W : Fin d → Vec d → Vec d) (i : Fin d) (x : Vec d) :
    fieldOf W (unitVector i) x = W i x := by
  simp only [fieldOf, unitVector, Pi.single_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem dot_add_mulVec_add_sub {M : Mat d} (hM : M.transpose = M) (u v : Vec d) :
    dot (u + v) (M.mulVec (u + v)) - dot (u - v) (M.mulVec (u - v)) = 4 * dot u (M.mulVec v) := by
  have h := dot_mulVec_comm hM v u
  simp only [dot_eq_dotProduct, Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct, dotProduct_add,
    sub_dotProduct, dotProduct_sub] at h ⊢
  linarith

section GoodEvent

variable {P : Measure (CoefficientField d Λ)}

/-- The bounds (3.101)–(3.103) give the integrability of the corrected family. -/
theorem integrableFamily_of_averages (S : HomogenizationData P) (a : CoefficientField d Λ)
    (y : Vec d) (r ε : ℝ)
    (havg : GaussianAverageBounds a S.homogenized (correctedField S a) y r ε) :
    IntegrableFamily a (heatKernel y r) (correctedCoordinate S a) := by
  have hG : ∀ ξ, correctedField S a ξ = fieldOf (correctedCoordinate S a) ξ := fun ξ => rfl
  have hu : ∀ i, fieldOf (correctedCoordinate S a) (unitVector i) = correctedCoordinate S a i :=
    fun i => funext fun x => fieldOf_unitVector _ i x
  refine ⟨fun i => ?_, fun i => ?_, fun i j => ?_⟩
  · have := (havg (unitVector i)).1
    rwa [hG, hu] at this
  · have := (havg (unitVector i)).2.1
    rwa [hG, hu] at this
  · have h1 := (havg (unitVector i + unitVector j)).2.2.1
    have h2 := (havg (unitVector i - unitVector j)).2.2.1
    rw [hG] at h1 h2
    have := (h1.sub h2).const_mul (1 / 4 : ℝ)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    rw [fieldOf_add, fieldOf_sub, fieldOf_unitVector, fieldOf_unitVector, ← mul_sub,
      dot_add_mulVec_add_sub (a.symmetric x)]
    ring

/-- The quadratic form of the energy matrix is the `Ψ`-average of the energy density. -/
theorem dot_energyMatrix_eq_integral (a : CoefficientField d Λ) (mask : Vec d → ℝ)
    (W : Fin d → Vec d → Vec d) (hW : IntegrableFamily a mask W) (ξ : Vec d) :
    dot ξ ((energyMatrix a mask W).mulVec ξ) =
      ∫ x, mask x * dot (fieldOf W ξ x) ((a x).mulVec (fieldOf W ξ x)) := by
  have h := j1Functional_fieldOf a mask W hW 0 0 ξ
  have hl : loadVector a mask W 0 0 = 0 := by
    funext j; simp [loadVector, dot]
  rw [hl, show dot (0 : Vec d) ξ = 0 by simp [dot], add_zero] at h
  unfold j1Functional at h
  have e : (fun x => mask x * (-(1 / 2 : ℝ) * dot (fieldOf W ξ x) ((a x).mulVec (fieldOf W ξ x)) -
      dot 0 ((a x).mulVec (fieldOf W ξ x)) + dot 0 (fieldOf W ξ x))) =
      fun x => -(1 / 2 : ℝ) * (mask x * dot (fieldOf W ξ x) ((a x).mulVec (fieldOf W ξ x))) := by
    funext x; simp only [dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero]; ring
  rw [e, integral_const_mul] at h
  linarith

/-- **The trial gap at a good scale**: if the gradients of `A₁` are the corrected fields and the
bounds (3.101)–(3.103) hold at `Φ_{y,r}` with error `ε ≤ 1/4`, then for every slope `k`,
`J₁(Φ_{y,r}, p, q) - L(k) ≤ (8/9)(Λ + 1/2) |∫ Φ_{y,r} G k - ∫ Φ_{y,r} G c|²`, with `c` the
maximizing slope. -/
theorem trialGap_le_of_averages (S : HomogenizationData P) (a : CoefficientField d Λ)
    (hΛ : 0 ≤ Λ) (hA : HomogenizedMatrixBounds S.homogenized Λ)
    (hspan : GradientsOfA1AreCorrected S a) (y : Vec d) (r : ℝ) {ε : ℝ} (hε : ε ≤ 1 / 4)
    (havg : GaussianAverageBounds a S.homogenized (correctedField S a) y r ε) (p q k : Vec d) :
    J1Heat a y r p q - j1Functional a (heatKernel y r) p q (correctedField S a k) ≤
      8 / 9 * (Λ + 1 / 2) * euclideanNorm ((∫ x, heatKernel y r x • correctedField S a k x) -
        ∫ x, heatKernel y r x • correctedField S a
          (maximizerSlope a (heatKernel y r) (correctedCoordinate S a) p q) x) ^ 2 := by
  set W := correctedCoordinate S a with hWdef
  set mask := heatKernel y r with hmask
  have hW := integrableFamily_of_averages S a y r ε havg
  set A := energyMatrix a mask W with hAdef
  set c := maximizerSlope a mask W p q with hcdef
  -- the energy matrix is between `1 - 2ε` and `Λ + 2ε`
  have hAξ : ∀ ξ, (1 - 2 * ε) * euclideanSq ξ ≤ dot ξ (A.mulVec ξ) ∧
      dot ξ (A.mulVec ξ) ≤ (Λ + 2 * ε) * euclideanSq ξ := by
    intro ξ
    rw [dot_energyMatrix_eq_integral a mask W hW ξ]
    have h0 : |(∫ x, mask x * dot (fieldOf W ξ x) ((a x).mulVec (fieldOf W ξ x))) -
        dot ξ (S.homogenized.mulVec ξ)| ≤ 2 * ε * euclideanNorm ξ ^ 2 := (havg ξ).2.2.2.2.2
    have h := abs_le.mp h0
    obtain ⟨h1, h2⟩ := hA ξ
    rw [euclideanNorm_sq] at h
    constructor <;> nlinarith [h.1, h.2]
  have hpos : ∀ ξ, ξ ≠ 0 → 0 < dot ξ (A.mulVec ξ) := by
    intro ξ hξ
    have h1 := (hAξ ξ).1
    have h2 : 0 < euclideanSq ξ := by
      rcases (euclideanSq_nonneg ξ).lt_or_eq with h | h
      · exact h
      · exact absurd (eq_zero_of_euclideanSq_le_zero h.symm.le) hξ
    nlinarith
  have hdet : IsUnit A.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have := hpos v hv0
    rw [hv, dot_eq_dotProduct, dotProduct_zero] at this
    exact lt_irrefl _ this
  have hpsd : ∀ ξ, 0 ≤ dot ξ (A.mulVec ξ) := fun ξ =>
    (mul_nonneg (by linarith) (euclideanSq_nonneg ξ)).trans (hAξ ξ).1
  obtain ⟨-, hgap⟩ := J1_sub_j1Functional_fieldOf a mask W hW hspan.1 hspan.2 hdet hpsd p q
  have hg := hgap k
  -- the gradient averages
  set Pv : Vec d → Vec d := fun v => ∫ x, mask x • fieldOf W v x with hPv
  have hPsub : Pv (k - c) = Pv k - Pv c := by
    have hk : Integrable fun x => mask x • fieldOf W k x := (havg k).1
    have hc : Integrable fun x => mask x • fieldOf W c x := (havg c).1
    simp only [hPv]
    rw [← integral_sub hk hc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [fieldOf_sub, smul_sub]
  have hPclose : euclideanNorm (Pv (k - c) - (k - c)) ≤ ε * euclideanNorm (k - c) := (havg (k - c)).2.2.2.1
  have hvP : euclideanNorm (k - c) ≤ 4 / 3 * euclideanNorm (Pv (k - c)) := by
    have h1 : euclideanNorm (k - c) ≤ euclideanNorm (Pv (k - c)) + euclideanNorm (Pv (k - c) - (k - c)) := by
      have := euclideanNorm_sub_le (Pv (k - c)) (Pv (k - c) - (k - c))
      simpa using this
    have h2 := euclideanNorm_nonneg (k - c)
    nlinarith
  have hupper := (hAξ (k - c)).2
  rw [← euclideanNorm_sq] at hupper
  have hn0 := euclideanNorm_nonneg (k - c)
  have hPn0 := euclideanNorm_nonneg (Pv (k - c))
  have hsq : euclideanNorm (k - c) ^ 2 ≤ 16 / 9 * euclideanNorm (Pv (k - c)) ^ 2 := by
    nlinarith
  have hkc : 1 / 2 * dot (k - c) (A.mulVec (k - c)) ≤
      8 / 9 * (Λ + 1 / 2) * euclideanNorm (Pv (k - c)) ^ 2 := by
    have h1 : dot (k - c) (A.mulVec (k - c)) ≤ (Λ + 1 / 2) * euclideanNorm (k - c) ^ 2 := by
      have : (Λ + 2 * ε) * euclideanNorm (k - c) ^ 2 ≤ (Λ + 1 / 2) * euclideanNorm (k - c) ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      linarith
    have h2 : (Λ + 1 / 2) * euclideanNorm (k - c) ^ 2 ≤
        (Λ + 1 / 2) * (16 / 9 * euclideanNorm (Pv (k - c)) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (by linarith)
    nlinarith
  rw [hPsub] at hkc
  show J1 a mask p q - j1Functional a mask p q (fieldOf W k) ≤
    8 / 9 * (Λ + 1 / 2) * euclideanNorm (Pv k - Pv c) ^ 2
  rw [hg]
  exact hkc

end GoodEvent

end QSH
