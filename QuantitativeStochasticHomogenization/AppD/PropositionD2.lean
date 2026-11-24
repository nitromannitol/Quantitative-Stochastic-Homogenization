import QuantitativeStochasticHomogenization.AppD.LemmaD3

/-!
# Appendix D: Proposition D.2 for `q = 2` and `α ∈ ℕ`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix D, Proposition D.2, (D.3), in the case `q = 2` and `α ∈ ℕ`: for `k ∈ ℕ ∩ (α, ∞)` there is
`C(k, α, d)` such that for every `u ∈ H^α(ℝ^d)`,
`(∫_{ℝ^d} ∫_0^∞ (t^{(k-α)/2} |(∇^k Φ(t, ·) ∗ u)(x)|)² dt/t dx)^{1/2} ≤ C [u]_{H^α(ℝ^d)}`
(`propositionD2_two`). As the book remarks after Proposition D.2, for `q = 2` the left-hand side is
that of (D.5), by Tonelli's theorem, and the statement is Lemma D.3.
-/

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

/-- **Proposition D.2, (D.3), for `q = 2` and `α ∈ ℕ`.** -/
theorem propositionD2_two (α k : ℕ) (hαk : α < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Vec d → ℝ) (g : List (Fin d) → Vec d → ℝ),
      IsSobolevFamily α u g →
        (∫⁻ x, ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (k - α) / t) *
            ENNReal.ofReal (heatGradSq k t u x)) ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal C *
            (∫⁻ x, ENNReal.ofReal (∑ v : Fin α → Fin d, g (List.ofFn v) x ^ 2)) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := lemmaD3 (d := d) α k hαk
  refine ⟨C, hC0, fun u g hS => ?_⟩
  have hu : MemLp u 2 volume := hS.nil ▸ hS.memLp [] (by simp)
  obtain ⟨H, hHm, hH⟩ := exists_measurable_heatGradSq k hu.aestronglyMeasurable
  have hmeas : AEMeasurable (Function.uncurry fun (x : Vec d) (t : ℝ) =>
      ENNReal.ofReal (t ^ (k - α) / t) * ENNReal.ofReal (heatGradSq k t u x))
      (volume.prod (volume.restrict (Ioi 0))) := by
    have hm : Measurable (fun p : Vec d × ℝ =>
        ENNReal.ofReal (p.2 ^ (k - α) / p.2) * ENNReal.ofReal (H (p.2, p.1))) :=
      ((measurable_snd.pow_const _).div measurable_snd).ennreal_ofReal.mul
        (hHm.comp (measurable_snd.prodMk measurable_fst)).ennreal_ofReal
    refine hm.aemeasurable.congr ?_
    have hprod : (volume : Measure (Vec d)).prod (volume.restrict (Ioi (0 : ℝ))) =
        ((volume : Measure (Vec d)).prod (volume : Measure ℝ)).restrict (univ ×ˢ Ioi 0) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [hprod]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ioi)] with p hp
    simp only [Function.uncurry]
    rw [hH p.2 hp.2 p.1]
  rw [lintegral_lintegral_swap hmeas]
  have heq : ∫⁻ t in Ioi 0, ∫⁻ x, ENNReal.ofReal (t ^ (k - α) / t) *
      ENNReal.ofReal (heatGradSq k t u x) = ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (k - α) / t) *
      ∫⁻ x, ENNReal.ofReal (heatGradSq k t u x) :=
    lintegral_congr fun t => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [heq]
  exact hC u g hS

end QSH
