import QuantitativeStochasticHomogenization.Ch02.Sec01.Lemma22

/-!
# (2.43): the mean gradient of the maximizer of `J(U, p, q)`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.2, (2.43) before its expectation: for a bounded open convex nonempty `U` and every
maximizer `v(·, U, p, q)` of (2.9), `⨍_U ∇v(·, U, p, q) = a*⁻¹(U) q - p`
(`IsDefectMaximizer.setAverage_grad_eq`). As in the book, `(p, q) ↦ v(·, U, p, q)` is linear
(`IsDefectMaximizer.linearCombination`), `⨍_U ∇v(·, U, 0, q) = a*⁻¹(U) q` by (2.14), and
`v(·, U, p, 0)` is minus the minimizer of `μ(U, p)` by Lemma 2.1, whose gradient has mean `p`.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- **(2.43)**: `⨍_U ∇v(·, U, p, q) = a*⁻¹(U) q - p` for every maximizer `v(·, U, p, q)` of (2.9). -/
theorem IsDefectMaximizer.setAverage_grad_eq [NeZero d] {a : CoefficientField d Λ}
    {U : Set (Vec d)} (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U)
    (hne : U.Nonempty) {p q : Vec d} {v : Vec d → ℝ} {g : Vec d → Vec d}
    (hmax : IsDefectMaximizer a U p q v g) :
    (fun i => ⨍ x in U, g x i) = (coarseDualInvMatrix a U).mulVec q - p := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hU
  have hV : volume.real U ≠ 0 := (ENNReal.toReal_pos hU0 hU).ne'
  -- the maximizer for `(0, q)`
  obtain ⟨v₀, g₀, h₀⟩ := exists_isDefectMaximizer a hUo hUb hUc hne 0 q
  have e₀ := coarseDualInvMatrix_mulVec_eq a hUo hUb hUc hne h₀
  -- the maximizer for `(p, 0)`
  obtain ⟨u, gD, hD⟩ := exists_isDirichletMinimizer a hUb hU0 p
  have h₁ := (lemma_2_1 a hUo hUb hUc hne p 0).2.2 _ _ u gD
    (isDualMaximizer_zero a hUo hUb hne) hD
  have hsum := h₁.linearCombination hUo hUb hUc hne h₀ 1 1
  have hpq : (1 : ℝ) • p + (1 : ℝ) • (0 : Vec d) = p := by simp
  have hqq : (1 : ℝ) • (0 : Vec d) + (1 : ℝ) • q = q := by simp
  rw [hpq, hqq] at hsum
  have hae := hmax.ae_eq hUb hU0 hsum
  have hgD : MemLp gD 2 (volume.restrict U) := hD.1.2.1
  have hg₀ : MemLp g₀ 2 (volume.restrict U) := h₀.1.1.2.1
  funext i
  have hmean := setIntegral_eq_zero_of_H01 hU hD.1 i
  have i0 : Integrable (fun x => g₀ x i) (volume.restrict U) := (MemLp.eval hg₀ i).integrable one_le_two
  have iD : Integrable (fun x => gD x i) (volume.restrict U) := (MemLp.eval hgD i).integrable one_le_two
  have hcongr : (⨍ x in U, g x i) = ⨍ x in U, (g₀ x i - gD x i - p i) := by
    refine average_congr ?_
    filter_upwards [hae] with x hx
    rw [hx]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, zero_sub,
      Pi.neg_apply]
    ring
  have e₀i : (coarseDualInvMatrix a U).mulVec q i = ⨍ x in U, g₀ x i := congrFun e₀ i
  have i0D : Integrable (fun x => g₀ x i - gD x i) (volume.restrict U) := i0.sub iD
  rw [hcongr, Pi.sub_apply, e₀i, setAverage_eq, setAverage_eq, integral_sub i0D
    (integrable_const _), integral_sub i0 iD, hmean, integral_const, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, measureReal_restrict_apply_univ]
  field_simp
  ring

end QSH
