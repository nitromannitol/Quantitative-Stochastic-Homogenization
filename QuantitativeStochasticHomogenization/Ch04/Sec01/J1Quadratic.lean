import QuantitativeStochasticHomogenization.Ch04.Sec01.J1CorrectedAffine

/-!
# `J₁` as a quadratic maximization over the corrector columns

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.1, (4.8): on the corrected affine gradients `∑ᵢ cᵢ Wᵢ`, `Wᵢ = eᵢ + ∇φ_{eᵢ}`, the objective
of `J₁(Ψ, p, q)` is the concave quadratic `b·c - ½ c·M c` with the Gram matrix
`M_{ij} = ∫ Ψ Wᵢ·a Wⱼ` and the load `bᵢ = ∫ Ψ (-p·a Wᵢ + q·Wᵢ)`. Its supremum is `½ b·c₀` for every
solution `c₀` of `M c₀ = b`; in the notation of the book this is `J₁ = ½‖-V*p + U*q‖²` for the
weighted inner product `⟨v, w⟩ = ∫ Ψ v·a w`. Under the first-order Liouville theorem this
computes `J₁` itself.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The corrected coordinate gradient `Wᵢ = eᵢ + ∇φ_{eᵢ}`. -/
def correctorColumn {Λ : ℝ} {P : Measure (CoefficientField d Λ)} (S : HomogenizationData P)
    (a : CoefficientField d Λ) (i : Fin d) (x : Vec d) : Vec d :=
  unitVector i + (S.corrector (unitVector i)).grad a x

theorem correctedAffineGrad_eq_sum {Λ : ℝ} {P : Measure (CoefficientField d Λ)}
    (S : HomogenizationData P) (a : CoefficientField d Λ) (c x : Vec d) :
    correctedAffineGrad S a c x = ∑ i, c i • correctorColumn S a i x := by
  have hc : (∑ i, c i • unitVector i : Vec d) = c := by
    funext k
    simp [unitVector, Pi.single_apply]
  simp only [correctedAffineGrad, correctorColumn, smul_add, Finset.sum_add_distrib, hc]

/-- The Gram matrix `M_{ij} = ∫ Ψ Wᵢ·a Wⱼ`. -/
def J1Gram {Λ : ℝ} {P : Measure (CoefficientField d Λ)} (S : HomogenizationData P)
    (a : CoefficientField d Λ) (mask : Vec d → ℝ) : Mat d := fun i j =>
  ∫ x, mask x * dot (correctorColumn S a i x) ((a x).mulVec (correctorColumn S a j x))

/-- The load `bᵢ = ∫ Ψ (-p·a Wᵢ + q·Wᵢ)`. -/
def J1Load {Λ : ℝ} {P : Measure (CoefficientField d Λ)} (S : HomogenizationData P)
    (a : CoefficientField d Λ) (mask : Vec d → ℝ) (p q : Vec d) : Vec d := fun i =>
  ∫ x, mask x * (-dot p ((a x).mulVec (correctorColumn S a i x)) + dot q (correctorColumn S a i x))

private theorem dot_mulVec_sum (A : Mat d) (u c : Vec d) (W : Fin d → Vec d) :
    dot u (A.mulVec (∑ i, c i • W i)) = ∑ i, c i * dot u (A.mulVec (W i)) := by
  change dotProduct _ _ = ∑ i, c i * dotProduct _ _
  rw [Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]

private theorem dot_sum_mulVec_sum (A : Mat d) (c : Vec d) (W : Fin d → Vec d) :
    dot (∑ i, c i • W i) (A.mulVec (∑ j, c j • W j)) =
      ∑ i, ∑ j, c i * c j * dot (W i) (A.mulVec (W j)) := by
  change dotProduct (∑ i, c i • W i) _ = _
  rw [sum_dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_dotProduct, smul_eq_mul]
  have h := dot_mulVec_sum A (W i) c W
  change c i * dot (W i) (A.mulVec (∑ j, c j • W j)) = _
  rw [h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem dot_sum (u c : Vec d) (W : Fin d → Vec d) :
    dot u (∑ i, c i • W i) = ∑ i, c i * dot u (W i) := by
  change dotProduct _ _ = ∑ i, c i * dotProduct _ _
  simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul]

/-- **The objective of `J₁` is quadratic in the slope.** If the Gram and load integrands are
integrable, then the objective at the corrected affine gradient of slope `c` is
`b·c - ½ c·M c`. -/
theorem J1Objective_eq_quadratic {Λ : ℝ} {P : Measure (CoefficientField d Λ)}
    (S : HomogenizationData P) (a : CoefficientField d Λ) (mask : Vec d → ℝ) (p q : Vec d)
    (hM : ∀ i j, Integrable (fun x => mask x *
      dot (correctorColumn S a i x) ((a x).mulVec (correctorColumn S a j x))))
    (hb : ∀ i, Integrable (fun x => mask x * (-dot p ((a x).mulVec (correctorColumn S a i x)) +
      dot q (correctorColumn S a i x))))
    (c : Vec d) :
    J1Objective S a mask p q c =
      dot (J1Load S a mask p q) c - (1 / 2 : ℝ) * dot c ((J1Gram S a mask).mulVec c) := by
  have key : ∀ x, mask x * (-(1 / 2 : ℝ) * dot (correctedAffineGrad S a c x)
        ((a x).mulVec (correctedAffineGrad S a c x)) -
      dot p ((a x).mulVec (correctedAffineGrad S a c x)) + dot q (correctedAffineGrad S a c x)) =
      ∑ i, c i * (mask x * (-dot p ((a x).mulVec (correctorColumn S a i x)) +
        dot q (correctorColumn S a i x))) -
      (1 / 2 : ℝ) * ∑ i, ∑ j, c i * c j * (mask x *
        dot (correctorColumn S a i x) ((a x).mulVec (correctorColumn S a j x))) := by
    intro x
    rw [correctedAffineGrad_eq_sum, dot_sum_mulVec_sum, dot_mulVec_sum, dot_sum]
    have h1 : ∑ i, c i * (mask x * (-dot p ((a x).mulVec (correctorColumn S a i x)) +
          dot q (correctorColumn S a i x))) =
        mask x * (∑ i, c i * dot q (correctorColumn S a i x) -
          ∑ i, c i * dot p ((a x).mulVec (correctorColumn S a i x))) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h2 : ∑ i, ∑ j, c i * c j * (mask x *
          dot (correctorColumn S a i x) ((a x).mulVec (correctorColumn S a j x))) =
        mask x * ∑ i, ∑ j, c i * c j *
          dot (correctorColumn S a i x) ((a x).mulVec (correctorColumn S a j x)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h1, h2]
    ring
  have hlin : Integrable (fun x => ∑ i, c i * (mask x *
      (-dot p ((a x).mulVec (correctorColumn S a i x)) + dot q (correctorColumn S a i x)))) :=
    integrable_finsetSum _ fun i _ => (hb i).const_mul (c i)
  have hquad : Integrable (fun x => ∑ i, ∑ j, c i * c j * (mask x *
      dot (correctorColumn S a i x) ((a x).mulVec (correctorColumn S a j x)))) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hM i j).const_mul _
  have eL : ∫ x, ∑ i, c i * (mask x * (-dot p ((a x).mulVec (correctorColumn S a i x)) +
      dot q (correctorColumn S a i x))) = dot (J1Load S a mask p q) c := by
    rw [integral_finsetSum _ fun i _ => (hb i).const_mul (c i)]
    change _ = ∑ i, J1Load S a mask p q i * c i
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, mul_comm]
    rfl
  have eQ : ∫ x, ∑ i, ∑ j, c i * c j * (mask x *
      dot (correctorColumn S a i x) ((a x).mulVec (correctorColumn S a j x))) =
      dot c ((J1Gram S a mask).mulVec c) := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hM i j).const_mul _]
    change _ = ∑ i, c i * ∑ j, J1Gram S a mask i j * c j
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hM i j).const_mul _, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    simp only [J1Gram]
    ring
  unfold J1Objective
  simp only [key]
  rw [integral_sub hlin (hquad.const_mul _), integral_const_mul, eL, eQ]

/-- **The supremum of a concave quadratic.** For a symmetric positive semidefinite `M` and a
solution `c₀` of `M c₀ = b`, the supremum of `c ↦ b·c - ½ c·M c` is `½ b·c₀`, attained at `c₀`. -/
theorem isGreatest_quadratic (M : Mat d) (b c₀ : Vec d) (hsym : M.transpose = M)
    (hpsd : ∀ c, 0 ≤ dot c (M.mulVec c)) (hc₀ : M.mulVec c₀ = b) :
    IsGreatest (Set.range fun c => dot b c - (1 / 2 : ℝ) * dot c (M.mulVec c))
      ((1 / 2 : ℝ) * dot b c₀) := by
  have hcross : ∀ c, dot c₀ (M.mulVec c) = dot b c := by
    intro c
    change dotProduct c₀ (M.mulVec c) = dotProduct b c
    rw [Matrix.dotProduct_mulVec, ← hc₀, ← Matrix.vecMul_transpose, hsym]
  have hcross' : ∀ c, dot c (M.mulVec c₀) = dot b c := by
    intro c
    change dotProduct c (M.mulVec c₀) = dotProduct b c
    rw [hc₀, dotProduct_comm]
  have hexp : ∀ c, dot (c - c₀) (M.mulVec (c - c₀)) =
      dot c (M.mulVec c) - 2 * dot b c + dot b c₀ := by
    intro c
    have h1 := hcross c
    have h2 := hcross' c
    have h3 := hcross' c₀
    change dotProduct (c - c₀) (M.mulVec (c - c₀)) =
      dotProduct c (M.mulVec c) - 2 * dotProduct b c + dotProduct b c₀
    change dotProduct c₀ (M.mulVec c) = dotProduct b c at h1
    change dotProduct c (M.mulVec c₀) = dotProduct b c at h2
    change dotProduct c₀ (M.mulVec c₀) = dotProduct b c₀ at h3
    simp only [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub]
    rw [h1, h2, h3]
    ring
  refine ⟨⟨c₀, ?_⟩, ?_⟩
  · simp only
    rw [hcross' c₀]
    ring
  · rintro _ ⟨c, rfl⟩
    have h := hpsd (c - c₀)
    rw [hexp c] at h
    simp only
    linarith

/-- **`J₁ = ½ b·c₀`.** Under the first-order Liouville theorem, if the Gram and load integrands of
the mask are integrable, the Gram matrix is symmetric and positive semidefinite and `M c₀ = b`,
then `J₁(Ψ, p, q) = ½ b·c₀`, almost surely. -/
theorem ae_J1_eq_half_dot_load (hL : firstOrderLiouvilleStatement) (hd : 2 ≤ d) {Λ : ℝ}
    (hΛ : 1 < Λ) {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P)
    (S : HomogenizationData P) :
    ∀ᵐ a ∂P, ∀ (mask : Vec d → ℝ) (p q c₀ : Vec d),
      (∀ i j, Integrable (fun x => mask x *
        dot (correctorColumn S a i x) ((a x).mulVec (correctorColumn S a j x)))) →
      (∀ i, Integrable (fun x => mask x * (-dot p ((a x).mulVec (correctorColumn S a i x)) +
        dot q (correctorColumn S a i x)))) →
      (J1Gram S a mask).transpose = J1Gram S a mask →
      (∀ c, 0 ≤ dot c ((J1Gram S a mask).mulVec c)) →
      (J1Gram S a mask).mulVec c₀ = J1Load S a mask p q →
      J1 a mask p q = (1 / 2 : ℝ) * dot (J1Load S a mask p q) c₀ := by
  filter_upwards [ae_J1_eq_sSup_range_J1Objective_of_liouville hL hd hΛ hP S] with a ha
  intro mask p q c₀ hM hb hsym hpsd hc₀
  rw [ha mask p q]
  have hfun : J1Objective S a mask p q = fun c =>
      dot (J1Load S a mask p q) c - (1 / 2 : ℝ) * dot c ((J1Gram S a mask).mulVec c) := by
    funext c
    exact J1Objective_eq_quadratic S a mask p q hM hb c
  rw [hfun]
  exact (isGreatest_quadratic _ _ c₀ hsym hpsd hc₀).csSup_eq

end QSH
