import QuantitativeStochasticHomogenization.Ch06.Sec01.FluxPotentialIdentification
import QuantitativeStochasticHomogenization.Ch03.Sec03.CorrectedAffine

/-!
# Skew symmetry of the flux corrector

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 6.1, (6.5): the flux corrector `S_e` selected by the heat formula (6.7) is skew-symmetric up
to a constant matrix. The density of (6.7) is antisymmetric in the two matrix indices, so the
selected gradients satisfy `∇S_{jk} = -∇S_{kj}` almost everywhere, and `S_{jk} + S_{kj}` is almost
everywhere constant.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ}

theorem heatGradientDensity_swap (g : Vec d → Vec d) (t : ℝ) (j k l : Fin d) (x y : Vec d) :
    heatGradientDensity g t k j l x y = -heatGradientDensity g t j k l x y := by
  unfold heatGradientDensity
  split_ifs <;> ring

theorem heatGradientSpaceIntegral_swap (g : Vec d → Vec d) (t : ℝ) (j k l : Fin d) (x : Vec d) :
    heatGradientSpaceIntegral g t k j l x = -heatGradientSpaceIntegral g t j k l x := by
  unfold heatGradientSpaceIntegral
  rw [← integral_neg]
  congr 1
  funext y
  exact heatGradientDensity_swap g t j k l x y

theorem iteratedHeatGradientTruncation_swap (g : Vec d → Vec d) (m n : ℕ) (j k l : Fin d)
    (x : Vec d) :
    iteratedHeatGradientTruncation g m n k j l x = -iteratedHeatGradientTruncation g m n j k l x := by
  unfold iteratedHeatGradientTruncation
  rw [← integral_neg]
  congr 1
  funext t
  exact heatGradientSpaceIntegral_swap g t j k l x

/-- The heat selection is compatible with exchanging the matrix indices. -/
theorem IsHeatSelectedFluxGradient.swap {g : Vec d → Vec d} {G : Fin d → Fin d → Vec d → Vec d}
    (h : IsHeatSelectedFluxGradient g G) :
    IsHeatSelectedFluxGradient g (fun j k x => -G k j x) := by
  intro j k l R
  obtain ⟨h1, h2, h3, h4⟩ := h k j l R
  refine ⟨fun m n => ?_, fun m n => ?_, ?_, ?_⟩
  · filter_upwards [h1 m n] with x hx
    refine ⟨?_, ?_⟩
    · filter_upwards [hx.1] with t ht
      have h' := ht.neg
      convert h' using 2 with y
      rw [heatGradientDensity_swap]
      rfl
    · have h' := hx.2.neg
      convert h' using 2 with t
      rw [heatGradientSpaceIntegral_swap]
      rfl
  · have h' := (h2 m n).neg
    convert h' using 2 with x
    rw [iteratedHeatGradientTruncation_swap]
    rfl
  · have h' := h3.neg
    convert h' using 1
  · convert h4 using 2 with mn
    rw [← eLpNorm_neg]
    congr 1
    funext x
    simp only [Pi.neg_apply]
    rw [iteratedHeatGradientTruncation_swap]
    ring

/-- The selected gradient is antisymmetric in the matrix indices. -/
theorem IsHeatSelectedFluxGradient.ae_antisymm {g : Vec d → Vec d}
    {G : Fin d → Fin d → Vec d → Vec d} (h : IsHeatSelectedFluxGradient g G) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j k l, G j k x l = -G k j x l :=
  isHeatSelectedFluxGradient_ae_unique h h.swap

/-- **Lemma 6.1, (6.5): skew symmetry up to a constant.** For every flux corrector `S`, almost
surely, every symmetric combination `S_{jk} + S_{kj}` is almost everywhere constant. -/
theorem FluxCorrector.ae_add_transpose_eq_const {K : ℝ} {P : Measure (CoefficientField d K)}
    {e : Vec d} {φ : Corrector P e} (S : FluxCorrector φ) :
    ∀ᵐ a ∂P, ∀ j k, ∃ c : ℝ, ∀ᵐ x ∂(volume : Measure (Vec d)),
      S.potential a x j k + S.potential a x k j = c := by
  filter_upwards [S.heat_selected, S.weak_gradient] with a hS hwS
  intro j k
  have hanti := hS.ae_antisymm
  have hweak := hasWeakGradient_add (hwS j k) (hwS k j)
  by_cases hd : d = 0
  · subst hd
    refine ⟨S.potential a 0 j k + S.potential a 0 k j, Filter.Eventually.of_forall fun x => ?_⟩
    have : x = 0 := Subsingleton.elim _ _
    rw [this]
  have hloc : LocallyIntegrable (fun x => S.potential a x j k + S.potential a x k j) volume :=
    locallyIntegrableOn_univ.mp (hweak ⟨0, Nat.pos_of_ne_zero hd⟩).1
  obtain ⟨c, hc⟩ := ae_eq_const_of_zero_weak_gradient hloc (fun l ψ hψ => by
    have h := (hweak l).2.2 ψ hψ
    have hzero : ∫ x, (S.grad a j k x + S.grad a k j x) l * ψ x = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hanti] with x hx
      simp only [Pi.add_apply, hx j k l, neg_add_cancel, zero_mul, Pi.zero_apply]
    simpa only [Measure.restrict_univ, hzero, neg_zero] using h)
  exact ⟨c, hc⟩

end QSH
