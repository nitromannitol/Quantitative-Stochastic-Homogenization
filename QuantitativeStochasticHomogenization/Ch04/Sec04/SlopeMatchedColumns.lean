import QuantitativeStochasticHomogenization.Ch04.Sec04.MatchedColumnGaussian

/-!
# Matched columns from small slopes

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 4.21. The matched columns of `LocalizationApproximationAtUniform.of_matched` are taken of
the form `V_i = W_i + ∑_j b_{ij} W_j`, the corrected gradient of slope `e_i + b_i`, with
`∑_{ij} b_{ij}² ≤ 1/4`. Then `c ↦ (c_j + ∑_i c_i b_{ij})_j` is invertible and at least half of the
identity, so the combinations of the `V_i` are those of the `W_i`, and the Gaussian Gram bound of
the `V_i` is a quarter of that of the `W_i`. The almost sure hypotheses of Lemma 4.22 then reduce
to the properties of the corrected coordinates and to the closeness, in `L²(Φ_{z,r}, B_T(z))`, of
the gradient of each localized coordinate to the corrected gradient of slope `e_i + b_i`.
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ} {z : Vec d} {T r : ℝ}

theorem sum_smul_slopeColumn (W : Fin d → Vec d) (b : Fin d → Fin d → ℝ) (c : Vec d) :
    ∑ i, c i • (W i + ∑ j, b i j • W j) = ∑ j, (c j + ∑ i, c i * b i j) • W j := by
  simp only [smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul, add_smul,
    Finset.sum_smul]
  congr 1
  exact Finset.sum_comm

/-- The linear map `c ↦ (c_j + ∑_i c_i b_{ij})_j`. -/
def slopeMap (b : Fin d → Fin d → ℝ) : Vec d →ₗ[ℝ] Vec d where
  toFun c := fun j => c j + ∑ i, c i * b i j
  map_add' c c' := by
    funext j
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' t c := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_add]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

theorem slopeMap_apply (b : Fin d → Fin d → ℝ) (c : Vec d) (j : Fin d) :
    slopeMap b c j = c j + ∑ i, c i * b i j := rfl

theorem euclideanSq_eq_sum_coord_sq (v : Vec d) : euclideanSq v = ∑ j, v j ^ 2 := by
  simp only [euclideanSq, dot, sq]

/-- For small slopes, `slopeMap b` is at least half of the identity. -/
theorem euclideanSq_le_four_mul_slopeMap (b : Fin d → Fin d → ℝ)
    (hb : ∑ i, ∑ j, b i j ^ 2 ≤ 1 / 4) (c : Vec d) :
    euclideanSq c ≤ 4 * euclideanSq (slopeMap b c) := by
  have hβ : ∑ j, (∑ i, c i * b i j) ^ 2 ≤ (∑ i, c i ^ 2) / 4 := by
    calc ∑ j, (∑ i, c i * b i j) ^ 2 ≤ ∑ j, (∑ i, c i ^ 2) * ∑ i, b i j ^ 2 :=
          Finset.sum_le_sum fun j _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (∑ i, c i ^ 2) * ∑ j, ∑ i, b i j ^ 2 := by rw [Finset.mul_sum]
      _ = (∑ i, c i ^ 2) * ∑ i, ∑ j, b i j ^ 2 := by rw [Finset.sum_comm (s := Finset.univ)]
      _ ≤ (∑ i, c i ^ 2) * (1 / 4) :=
          mul_le_mul_of_nonneg_left hb (Finset.sum_nonneg fun i _ => sq_nonneg _)
      _ = (∑ i, c i ^ 2) / 4 := by ring
  have hpt : ∑ j, c j ^ 2 ≤
      ∑ j, (2 * (c j + ∑ i, c i * b i j) ^ 2 + 2 * (∑ i, c i * b i j) ^ 2) :=
    Finset.sum_le_sum fun j _ => by nlinarith [sq_nonneg (c j + 2 * ∑ i, c i * b i j)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hpt
  rw [euclideanSq_eq_sum_coord_sq, euclideanSq_eq_sum_coord_sq]
  simp only [slopeMap_apply]
  linarith

theorem slopeMap_surjective (b : Fin d → Fin d → ℝ) (hb : ∑ i, ∑ j, b i j ^ 2 ≤ 1 / 4) :
    Function.Surjective (slopeMap b) := by
  refine LinearMap.injective_iff_surjective.1 ?_
  refine (injective_iff_map_eq_zero (slopeMap b)).2 fun c hc => ?_
  have h := euclideanSq_le_four_mul_slopeMap b hb c
  rw [hc] at h
  have h0 : euclideanSq (0 : Vec d) = 0 := by simp [euclideanSq, dot]
  rw [h0, mul_zero, euclideanSq_eq_sum_coord_sq] at h
  funext j
  have hj : c j ^ 2 = 0 := by
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (c i))).1
      (le_antisymm h (Finset.sum_nonneg fun i _ => sq_nonneg _))
    exact hall j (Finset.mem_univ j)
  simpa using hj

/-- **The almost sure hypotheses of Lemma 4.22 from corrected coordinates and small slopes**:
the hypotheses of `LocalizationApproximationAtUniform.of_corrected`, the converse of the
representation of `A₁` (every combination of the `W_i` is the gradient of an element of `A₁`),
slopes `b` with `∑ b_{ij}² ≤ 1/4`, and the closeness in `L²(Φ_{z,r}, B_T(z))` of the gradient of
the `i`-th localized coordinate to `W_i + ∑_j b_{ij} W_j`. -/
theorem LocalizationApproximationAtUniform.of_slopes {Λ : ℝ} {a : CoefficientField d Λ}
    (hΛ : 0 ≤ Λ) (hd : 0 < d) (hr : 0 < r) (hrT : r ≤ T) {S σ θ C : ℝ}
    {B : LocalizedBasis a z T S σ θ C} {p q : Vec d} {η κ Zv E ε ρ : ℝ}
    (hsmall : linearCoefficient d Λ p q ^ 2 / 2 *
      ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2))) ≤ 1 / 4)
    (u : Fin d → Vec d → ℝ) (W : Fin d → Vec d → Vec d)
    (hu : ∀ i, MemLp (u i) 2 (ballMeasure z r))
    (hWT : ∀ i j, MemLp (fun x => W i x j) 2 (ballMeasure z T))
    (hgrad : ∀ i, HasWeakGradient (ball z r) (u i) (W i)) (c : Fin d → ℝ)
    (hsub : ∀ i, ∫ x in ball z r, (u i x - (x - z) i - c i) ^ 2 ≤
      ε ^ 2 * r ^ 2 * volume.real (ball z r))
    (hε : (d : ℝ) * ε ^ 2 ≤ (1 / 4 : ℝ) ^ d / 16) (hE0 : 0 ≤ E)
    (hW : ∀ i, Integrable (fun x => heatKernel z (Real.sqrt 2 * r) x * euclideanSq (W i x)))
    (hE : ∀ i, ∫ x, heatKernel z (Real.sqrt 2 * r) x * euclideanSq (W i x) ≤ E)
    (hκ : (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2)) *
      (d * E / heatGramConstant d) ≤ κ)
    (hrep : ∀ w : HarmonicA1 a, ∃ ξ : Vec d, ∀ᵐ x, w.grad x = ∑ i, ξ i • W i x)
    (hWmem : ∀ ξ : Vec d, ∃ w : HarmonicA1 a, ∀ᵐ x, w.grad x = ∑ i, ξ i • W i x)
    (b : Fin d → Fin d → ℝ) (hb : ∑ i, ∑ j, b i j ^ 2 ≤ 1 / 4) (hρ0 : 0 ≤ ρ)
    (hclose : ∀ i, ∫ x in ball z T, heatKernel z r x *
      euclideanSq ((B.coordinate i).grad x - (W i x + ∑ j, b i j • W j x)) ≤ ρ ^ 2)
    (hρ : ρ ≤ Real.sqrt (heatGramConstant d / 4) / d / 2)
    (hη : 2 * (2 * linearCoefficient d Λ p q + 1) * ρ /
      (Real.sqrt (heatGramConstant d / 4) / d) ≤ η)
    (hZ : (((d : ℝ) * Λ / 2 + linearCoefficient d Λ p q / 2) *
          (κ * (d * (2 * linearCoefficient d Λ p q + 1) ^ 2)) +
        linearCoefficient d Λ p q / 2 *
          ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2)))) +
      ((d : ℝ) ^ 2 * Λ * (2 * (2 * linearCoefficient d Λ p q + 1) + η) / 2 +
        linearCoefficient d Λ p q) * η ≤ Zv) :
    LocalizationApproximationAtUniform a z T r hr.ne' B p q η κ Zv := by
  let V : Fin d → Vec d → Vec d := fun i x => W i x + ∑ j, b i j • W j x
  have hVsum : ∀ (c' : Vec d) (x : Vec d),
      ∑ i, c' i • V i x = ∑ j, slopeMap b c' j • W j x := fun c' x =>
    sum_smul_slopeColumn (fun j => W j x) b c'
  have hV : ∀ i k, MemLp (fun x => V i x k) 2 (ballMeasure z T) := by
    intro i k
    refine MemLp.ae_eq (Eventually.of_forall fun x => ?_)
      ((hWT i k).add (memLp_finsetSum Finset.univ fun j _ => (hWT j k).const_mul (b i j)))
    simp only [V, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hlowW := heatGram_lower_bound hr hrT u W hu hWT hgrad c hsub hε
  have hm := heatGramConstant_pos d
  have hVlow : ∀ c' : Vec d, heatGramConstant d / 4 * euclideanSq c' ≤
      ∫ x in ball z T, heatKernel z r x * euclideanSq (∑ i, c' i • V i x) := by
    intro c'
    simp_rw [hVsum]
    refine le_trans ?_ (hlowW (slopeMap b c'))
    have := euclideanSq_le_four_mul_slopeMap b hb c'
    nlinarith
  have hsurj := slopeMap_surjective b hb
  refine LocalizationApproximationAtUniform.of_matched hΛ hd hr hrT hsmall u W hu hWT hgrad c
    hsub hε hE0 hW hE hκ hrep V hV (by positivity) hVlow (fun w => ?_) (fun c' => ?_) hρ0
    hclose hρ hη hZ
  · obtain ⟨ξ, hξ⟩ := hrep w
    obtain ⟨c', hc'⟩ := hsurj ξ
    refine ⟨c', ae_restrict_of_ae (hξ.mono fun x hx => ?_)⟩
    rw [hx, hVsum, hc']
  · obtain ⟨w, hw⟩ := hWmem (slopeMap b c')
    refine ⟨w, ae_restrict_of_ae (hw.mono fun x hx => ?_)⟩
    rw [hx, hVsum]

end QSH
