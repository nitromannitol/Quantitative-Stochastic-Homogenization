import QuantitativeStochasticHomogenization.Ch04.Sec01.J1HeatGram
import QuantitativeStochasticHomogenization.Ch04.Sec01.QuadraticEntryBounds
import QuantitativeStochasticHomogenization.Ch03.Sec04.MeasurableRepresentative
import QuantitativeStochasticHomogenization.Ch06.Sec01.HighContrastFluxPairing
import QuantitativeStochasticHomogenization.Ch03.Sec03.CorrectorIndependence

/-!
# The formula for `J₁` at the heat kernel masks

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.1, (4.8): under the first-order Liouville theorem, almost surely, for every center `z`,
radius `r > 0` and loads `p, q`, `J₁(Φ_{z,r}, p, q) = ½ b·c₀` for every solution `c₀` of
`M c₀ = b`, where `M_{ij} = ∫ Φ_{z,r} Wᵢ·a Wⱼ` is the Gram matrix and `bᵢ = ∫ Φ_{z,r}(-p·a Wᵢ + q·Wᵢ)`
the load of the corrector columns `Wᵢ = eᵢ + ∇φ_{eᵢ}`; that is, `J₁ = ½‖-V*p + U*q‖²` for the
inner product `⟨v, w⟩ = ∫ Φ_{z,r} v·a w`.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ}

private theorem euclideanSq_nonneg' (v : Vec d) : 0 ≤ euclideanSq v := by
  unfold euclideanSq dot
  exact Finset.sum_nonneg fun l _ => mul_self_nonneg _

private theorem euclideanSq_add_add_sub (u v : Vec d) :
    euclideanSq (u + v) + euclideanSq (u - v) = 2 * euclideanSq u + 2 * euclideanSq v := by
  change dotProduct (u + v) (u + v) + dotProduct (u - v) (u - v) =
    2 * dotProduct u u + 2 * dotProduct v v
  simp only [add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub, dotProduct_comm v u]
  ring

/-- The bilinear form of a coefficient field is bounded by `Λ (|u|² + |v|²)`. -/
theorem abs_dot_mulVec_le {Λ : ℝ} (a : CoefficientField d Λ) (x u v : Vec d) :
    |dot u ((a x).mulVec v)| ≤ Λ * (euclideanSq u + euclideanSq v) := by
  have hpol := polarization_mulVec (a x) u v
  have hsym := dot_mulVec_comm_of_coefficientField a x v u
  change dotProduct v ((a x).mulVec u) = dotProduct u ((a x).mulVec v) at hsym
  rw [hsym] at hpol
  have h1 := a.elliptic x (u + v)
  have h2 := a.elliptic x (u - v)
  change euclideanSq (u + v) ≤ dotProduct (u + v) ((a x).mulVec (u + v)) ∧
    dotProduct (u + v) ((a x).mulVec (u + v)) ≤ Λ * euclideanSq (u + v) at h1
  change euclideanSq (u - v) ≤ dotProduct (u - v) ((a x).mulVec (u - v)) ∧
    dotProduct (u - v) ((a x).mulVec (u - v)) ≤ Λ * euclideanSq (u - v) at h2
  have hparΛ : Λ * euclideanSq (u + v) + Λ * euclideanSq (u - v) =
      2 * (Λ * euclideanSq u) + 2 * (Λ * euclideanSq v) := by
    rw [← mul_add, euclideanSq_add_add_sub]
    ring
  have hs1 := euclideanSq_nonneg' (u + v)
  have hs2 := euclideanSq_nonneg' (u - v)
  rw [abs_le, mul_add]
  change -(Λ * euclideanSq u + Λ * euclideanSq v) ≤ dotProduct u ((a x).mulVec v) ∧
    dotProduct u ((a x).mulVec v) ≤ Λ * euclideanSq u + Λ * euclideanSq v
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem abs_dot_le_euclideanSq_add (u v : Vec d) : |dot u v| ≤ euclideanSq u + euclideanSq v := by
  have h1 := euclideanSq_nonneg' (u + v)
  have h2 := euclideanSq_nonneg' (u - v)
  change 0 ≤ dotProduct (u + v) (u + v) at h1
  change 0 ≤ dotProduct (u - v) (u - v) at h2
  simp only [add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub,
    dotProduct_comm v u] at h1 h2
  rw [abs_le]
  change -(dotProduct u u + dotProduct v v) ≤ dotProduct u v ∧
    dotProduct u v ≤ dotProduct u u + dotProduct v v
  have hu : 0 ≤ dotProduct u u := euclideanSq_nonneg' u
  have hv : 0 ≤ dotProduct v v := euclideanSq_nonneg' v
  constructor <;> linarith

private theorem measurable_dot_rep_mulVec {Λ : ℝ} (a : CoefficientField d Λ) {u v : Vec d → Vec d}
    (hu : Measurable u) (hv : Measurable v) :
    Measurable fun x => dot (u x) ((coefficientRepresentative a x).mulVec (v x)) := by
  have hrep (k l : Fin d) : Measurable (fun y => coefficientRepresentative a y k l) :=
    Measurable.of_uncurry_left (f := fun a y => coefficientRepresentative a y k l)
      (measurable_coefficientRepresentative_apply k l)
  have hfun : (fun x => dot (u x) ((coefficientRepresentative a x).mulVec (v x))) =
      fun x => ∑ k, u x k * ∑ l, coefficientRepresentative a x k l * v x l := rfl
  rw [hfun]
  refine Finset.measurable_sum _ fun k _ => ?_
  refine ((measurable_pi_apply k).comp hu).mul (Finset.measurable_sum _ fun l _ => ?_)
  exact (hrep k l).mul ((measurable_pi_apply l).comp hv)

private theorem aestronglyMeasurable_dot_mulVec {Λ : ℝ} (a : CoefficientField d Λ)
    {u v : Vec d → Vec d} (hu : Measurable u) (hv : Measurable v) :
    AEStronglyMeasurable (fun x => dot (u x) ((a x).mulVec (v x))) volume := by
  refine (measurable_dot_rep_mulVec a hu hv).aestronglyMeasurable.congr ?_
  filter_upwards [coefficientRepresentative_ae_eq a] with x hx
  rw [hx]

theorem measurable_correctorColumn {Λ : ℝ} {P : Measure (CoefficientField d Λ)}
    (S : HomogenizationData P) (a : CoefficientField d Λ) (i : Fin d) :
    Measurable (correctorColumn S a i) :=
  measurable_const.add (Measurable.of_uncurry_left
    (f := fun a y => (S.corrector (unitVector i)).grad a y)
    (S.corrector (unitVector i)).measurable_grad)

/-- The Gram and load integrands are integrable when the corrector columns have finite energy
against the heat kernel mask. -/
theorem integrable_heatKernel_gram_load {Λ : ℝ} {P : Measure (CoefficientField d Λ)}
    (S : HomogenizationData P) (a : CoefficientField d Λ) (z : Vec d) {r : ℝ} (hr : 0 < r)
    (hW : ∀ i, Integrable (fun x => heatKernel z r x * euclideanSq (correctorColumn S a i x)))
    (p q : Vec d) :
    (∀ i j, Integrable (fun x => heatKernel z r x *
      dot (correctorColumn S a i x) ((a x).mulVec (correctorColumn S a j x)))) ∧
    (∀ i, Integrable (fun x => heatKernel z r x *
      (-dot p ((a x).mulVec (correctorColumn S a i x)) + dot q (correctorColumn S a i x)))) := by
  have hk : Integrable (heatKernel (d := d) z r) :=
    (integrable_euclideanHeatKernel (sq_pos_of_pos hr)).comp_sub_right z
  have hkm : Measurable (heatKernel (d := d) z r) :=
    ((continuous_euclideanHeatKernel (r ^ 2)).comp (continuous_id.sub continuous_const)).measurable
  have hk0 : ∀ x, 0 ≤ heatKernel z r x := fun x =>
    euclideanHeatKernel_nonneg (sq_nonneg r) (x - z)
  have hWm := measurable_correctorColumn S a
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · refine (((hW i).add (hW j)).const_mul Λ).mono'
      (hkm.aestronglyMeasurable.mul (aestronglyMeasurable_dot_mulVec a (hWm i) (hWm j)))
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hk0 x)]
    calc heatKernel z r x * |dot (correctorColumn S a i x) ((a x).mulVec (correctorColumn S a j x))|
        ≤ heatKernel z r x * (Λ * (euclideanSq (correctorColumn S a i x) +
            euclideanSq (correctorColumn S a j x))) :=
          mul_le_mul_of_nonneg_left (abs_dot_mulVec_le a x _ _) (hk0 x)
      _ = Λ * (heatKernel z r x * euclideanSq (correctorColumn S a i x) +
            heatKernel z r x * euclideanSq (correctorColumn S a j x)) := by ring
  · have hconst : Integrable (fun x => heatKernel z r x *
        (Λ * euclideanSq p + euclideanSq q)) := hk.mul_const _
    have hdotq : AEStronglyMeasurable (fun x => dot q (correctorColumn S a i x)) volume := by
      have hc : Continuous fun v : Vec d => dot q v := by unfold dot; fun_prop
      exact (hc.measurable.comp (hWm i)).aestronglyMeasurable
    have hdotp := aestronglyMeasurable_dot_mulVec a (u := fun _ => p) measurable_const (hWm i)
    refine (hconst.add ((hW i).const_mul (Λ + 1))).mono'
      (hkm.aestronglyMeasurable.mul (hdotp.neg.add hdotq))
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hk0 x)]
    have h1 := abs_dot_mulVec_le a x p (correctorColumn S a i x)
    have h2 := abs_dot_le_euclideanSq_add q (correctorColumn S a i x)
    have h3 : |(-dot p ((a x).mulVec (correctorColumn S a i x)) +
        dot q (correctorColumn S a i x))| ≤
        Λ * euclideanSq p + euclideanSq q + (Λ + 1) * euclideanSq (correctorColumn S a i x) := by
      calc _ ≤ |dot p ((a x).mulVec (correctorColumn S a i x))| +
            |dot q (correctorColumn S a i x)| := by
            simpa using abs_add_le (-dot p ((a x).mulVec (correctorColumn S a i x)))
              (dot q (correctorColumn S a i x))
        _ ≤ _ := by nlinarith [h1, h2]
    calc heatKernel z r x * |(-dot p ((a x).mulVec (correctorColumn S a i x)) +
          dot q (correctorColumn S a i x))|
        ≤ heatKernel z r x * (Λ * euclideanSq p + euclideanSq q +
            (Λ + 1) * euclideanSq (correctorColumn S a i x)) :=
          mul_le_mul_of_nonneg_left h3 (hk0 x)
      _ = heatKernel z r x * (Λ * euclideanSq p + euclideanSq q) +
            (Λ + 1) * (heatKernel z r x * euclideanSq (correctorColumn S a i x)) := by ring

/-- **`J₁(Φ_{z,r}, p, q) = ½ b·c₀`, (4.8).** Under the first-order Liouville theorem, almost
surely, for every center, radius `r > 0`, loads `p, q` and every solution `c₀` of the Gram
system `M c₀ = b` of the heat kernel mask, `J₁(Φ_{z,r}, p, q) = ½ b·c₀`. -/
theorem ae_J1Heat_eq_half_dot_load (hL : firstOrderLiouvilleStatement) (hd : 2 ≤ d) {Λ : ℝ}
    (hΛ : 1 < Λ) {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P)
    (S : HomogenizationData P) :
    ∀ᵐ a ∂P, ∀ (z : Vec d) (r : ℝ), 0 < r → ∀ p q c₀ : Vec d,
      (J1Gram S a (heatKernel z r)).mulVec c₀ = J1Load S a (heatKernel z r) p q →
      J1Heat a z r p q = (1 / 2 : ℝ) * dot (J1Load S a (heatKernel z r) p q) c₀ := by
  filter_upwards [ae_J1_eq_half_dot_load hL hd hΛ hP S,
    ae_integrable_heatKernel_mul_euclideanSq_correctorColumn hd hΛ hP S] with a hJ hW
  intro z r hr p q c₀ hc₀
  obtain ⟨hM, hb⟩ := integrable_heatKernel_gram_load S a z hr (fun i => hW i z r hr) p q
  have hk0 : ∀ x, 0 ≤ heatKernel z r x := fun x =>
    euclideanHeatKernel_nonneg (sq_nonneg r) (x - z)
  exact hJ (heatKernel z r) p q c₀ hM hb (J1Gram_transpose S a _)
    (J1Gram_nonneg S a _ hk0 hM) hc₀

private theorem dot_sum_mulVec_sum' (A : Mat d) (c : Vec d) (W : Fin d → Vec d) :
    dot (∑ i, c i • W i) (A.mulVec (∑ j, c j • W j)) =
      ∑ i, ∑ j, c i * c j * dot (W i) (A.mulVec (W j)) := by
  change dotProduct (∑ i, c i • W i) _ = _
  rw [sum_dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_dotProduct, smul_eq_mul]
  change c i * dotProduct (W i) (A.mulVec (∑ j, c j • W j)) = _
  rw [Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [show dot (W i) (A.mulVec (W j)) = dotProduct (W i) (A.mulVec (W j)) from rfl]
    ring

/-- The quadratic form of the Gram matrix is the weighted energy of the corrected affine
gradient. -/
theorem dot_J1Gram_mulVec_eq_integral {Λ : ℝ} {P : Measure (CoefficientField d Λ)}
    (S : HomogenizationData P) (a : CoefficientField d Λ) (mask : Vec d → ℝ)
    (hM : ∀ i j, Integrable (fun x => mask x *
      dot (correctorColumn S a i x) ((a x).mulVec (correctorColumn S a j x)))) (c : Vec d) :
    Integrable (fun x => mask x * dot (correctedAffineGrad S a c x)
      ((a x).mulVec (correctedAffineGrad S a c x))) ∧
    dot c ((J1Gram S a mask).mulVec c) = ∫ x, mask x * dot (correctedAffineGrad S a c x)
      ((a x).mulVec (correctedAffineGrad S a c x)) := by
  have hpt : ∀ x, mask x * dot (correctedAffineGrad S a c x)
      ((a x).mulVec (correctedAffineGrad S a c x)) =
      ∑ i, ∑ j, c i * c j * (mask x *
        dot (correctorColumn S a i x) ((a x).mulVec (correctorColumn S a j x))) := by
    intro x
    rw [correctedAffineGrad_eq_sum, dot_sum_mulVec_sum', Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hint : Integrable (fun x => ∑ i, ∑ j, c i * c j * (mask x *
      dot (correctorColumn S a i x) ((a x).mulVec (correctorColumn S a j x)))) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hM i j).const_mul _
  refine ⟨by simpa only [hpt] using hint, ?_⟩
  simp only [hpt]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hM i j).const_mul _]
  change ∑ i, c i * ∑ j, J1Gram S a mask i j * c j = _
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hM i j).const_mul _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  simp only [J1Gram]
  ring

/-- **`J₁(Φ_{z,r}, p, q) = ½ b·M⁻¹ b`, (4.8).** Under the first-order Liouville theorem, almost
surely, for every center, radius `r > 0` and loads `p, q`, the Gram matrix `M` of the heat kernel
mask is invertible and `J₁(Φ_{z,r}, p, q) = ½ b·M⁻¹ b` with the load `b`; this is
`J₁ = ½‖-V*p + U*q‖²` for the inner product `⟨v, w⟩ = ∫ Φ_{z,r} v·a w` on the corrected affine
gradients. -/
theorem ae_J1Heat_eq_half_dot_inv (hL : firstOrderLiouvilleStatement) (hd : 2 ≤ d) {Λ : ℝ}
    (hΛ : 1 < Λ) {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P)
    (S : HomogenizationData P) :
    ∀ᵐ a ∂P, ∀ (z : Vec d) (r : ℝ), 0 < r → ∀ p q : Vec d,
      IsUnit (J1Gram S a (heatKernel z r)) ∧
      J1Heat a z r p q = (1 / 2 : ℝ) * dot (J1Load S a (heatKernel z r) p q)
        ((J1Gram S a (heatKernel z r))⁻¹.mulVec (J1Load S a (heatKernel z r) p q)) := by
  filter_upwards [ae_J1Heat_eq_half_dot_load hL hd hΛ hP S,
    ae_integrable_heatKernel_mul_euclideanSq_correctorColumn hd hΛ hP S,
    ae_eq_zero_of_correctedAffineGrad_ae_eq_zero S] with a hJ hW hind
  intro z r hr p q
  obtain ⟨hM, -⟩ := integrable_heatKernel_gram_load S a z hr (fun i => hW i z r hr) p q
  have hk0 : ∀ x, 0 < heatKernel z r x := fun x => by
    unfold heatKernel euclideanHeatKernel
    positivity
  have hinj : Function.Injective (J1Gram S a (heatKernel z r)).mulVec := by
    intro c₁ c₂ h12
    have hc : (J1Gram S a (heatKernel z r)).mulVec (c₁ - c₂) = 0 := by
      rw [Matrix.mulVec_sub, h12, sub_self]
    obtain ⟨hint, heq⟩ := dot_J1Gram_mulVec_eq_integral S a (heatKernel z r) hM (c₁ - c₂)
    rw [hc] at heq
    have hzero : ∫ x, heatKernel z r x * dot (correctedAffineGrad S a (c₁ - c₂) x)
        ((a x).mulVec (correctedAffineGrad S a (c₁ - c₂) x)) = 0 := by
      rw [← heq]
      simp [dot]
    have hnn : ∀ x, 0 ≤ heatKernel z r x * dot (correctedAffineGrad S a (c₁ - c₂) x)
        ((a x).mulVec (correctedAffineGrad S a (c₁ - c₂) x)) := fun x =>
      mul_nonneg (hk0 x).le ((euclideanSq_nonneg' _).trans (a.elliptic x _).1)
    have hae := (integral_eq_zero_iff_of_nonneg hnn hint).mp hzero
    have hG : ∀ᵐ x ∂(volume : Measure (Vec d)), correctedAffineGrad S a (c₁ - c₂) x = 0 := by
      filter_upwards [hae] with x hx
      have h1 : dot (correctedAffineGrad S a (c₁ - c₂) x)
          ((a x).mulVec (correctedAffineGrad S a (c₁ - c₂) x)) = 0 := by
        rcases mul_eq_zero.mp hx with h | h
        · exact absurd h (hk0 x).ne'
        · exact h
      have h2 : euclideanSq (correctedAffineGrad S a (c₁ - c₂) x) = 0 :=
        le_antisymm ((a.elliptic x _).1.trans h1.le) (euclideanSq_nonneg' _)
      funext k
      have h2' : ∑ l, correctedAffineGrad S a (c₁ - c₂) x l *
          correctedAffineGrad S a (c₁ - c₂) x l = 0 := h2
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => mul_self_nonneg
        (correctedAffineGrad S a (c₁ - c₂) x l))).mp h2' k (Finset.mem_univ k)
      simpa using mul_self_eq_zero.mp h3
    exact sub_eq_zero.mp (hind (c₁ - c₂) hG)
  have hunit : IsUnit (J1Gram S a (heatKernel z r)) := Matrix.mulVec_injective_iff_isUnit.mp hinj
  refine ⟨hunit, hJ z r hr p q _ ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hunit),
    Matrix.one_mulVec]

end QSH
