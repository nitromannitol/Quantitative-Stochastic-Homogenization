import QuantitativeStochasticHomogenization.Ch04.Sec01.J1HeatGram
import QuantitativeStochasticHomogenization.Ch04.Sec01.QuadraticEntryBounds
import QuantitativeStochasticHomogenization.Ch03.Sec04.MeasurableRepresentative
import QuantitativeStochasticHomogenization.Ch06.Sec01.HighContrastFluxPairing

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

end QSH
