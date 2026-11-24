import QuantitativeStochasticHomogenization.Ch02.Sec02.Definition214
import QuantitativeStochasticHomogenization.Ch01.Sec03.LocalMeasurability

/-!
# The `F(U)`-measurability of `μ*(U, q)` and of `a*⁻¹(U)`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.2, the analogue for `μ*` of (1.29), used with the unit range of dependence in the proof
of Lemma 2.13: for an open set `U` of finite positive measure with nonempty complement, `μ*(U, q)`
is `F(U)`-measurable (`measurable_dualEnergy_localSigma`), and so are the entries of `a*⁻¹(U)`
(`measurable_coarseDualInvMatrix_apply_localSigma`). As for `μ` (`measurable_dirichletEnergy_localSigma`),
`μ*(U, q)` is the supremum of the functional of (2.1) over a countable set of gradients
(`exists_countable_dualEnergy_eq_iSup`), and the functional at a fixed gradient is an integral of
the coefficients against a fixed function of `L¹(U)`.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- **`μ*(U, q)` is `F(U)`-measurable** for an open set `U` of finite positive measure with
nonempty complement. -/
theorem measurable_dualEnergy_localSigma {U : Set (Vec d)} (hU : IsOpen U) (hUc : Uᶜ.Nonempty)
    (hU0 : volume U ≠ 0) (hUt : volume U ≠ ⊤) (hΛ : 0 ≤ Λ) (q : Vec d) :
    @Measurable (CoefficientField d Λ) ℝ (localSigma U) _ fun a => dualEnergy a U q := by
  obtain ⟨T, hTc, hTne, key⟩ := exists_countable_dualEnergy_eq_iSup (Λ := Λ) hU0 hUt hΛ q
  have : Countable T := hTc.to_subtype
  have : Nonempty T := hTne.to_subtype
  rw [funext key]
  refine Measurable.iSup fun F => ?_
  unfold lpDualTrialEnergy
  exact (measurable_lpTrialEnergy_localSigma hU hUc hUt 0 F).neg.add_const _

/-- **The entries of `a*⁻¹(U)` are `F(U)`-measurable.** -/
theorem measurable_coarseDualInvMatrix_apply_localSigma {U : Set (Vec d)} (hU : IsOpen U)
    (hUc : Uᶜ.Nonempty) (hU0 : volume U ≠ 0) (hUt : volume U ≠ ⊤) (hΛ : 0 ≤ Λ) (i j : Fin d) :
    @Measurable (CoefficientField d Λ) ℝ (localSigma U) _
      fun a => coarseDualInvMatrix a U i j := by
  unfold coarseDualInvMatrix polarizationMatrix polarization
  simp only [Matrix.of_apply]
  exact measurable_const.mul (((measurable_dualEnergy_localSigma hU hUc hU0 hUt hΛ _).sub
    (measurable_dualEnergy_localSigma hU hUc hU0 hUt hΛ _)).div_const 4)

end QSH
