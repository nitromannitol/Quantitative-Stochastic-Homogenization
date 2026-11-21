import QuantitativeStochasticHomogenization.Ch04.Sec04.CoordinateMinimizerExistence

/-!
# Comparison of a coordinate minimizer with an admissible competitor

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.21, the first use of the minimality of the selected coordinates: if `h` is an
admissible `a`-harmonic function on `B_T(z)` (for instance a corrected coordinate
`x_i + φ_{e_i} - c`), then the smoothed difference between the coordinate minimizer `w_i` and `h`
is controlled by the smoothed distance from `h` to the coordinate function:
`I[w_i - h] ≤ 4 I[h - ℓ_i]`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ} {a : CoefficientField d Λ} {z : Vec d} {T S σ θ C : ℝ}

theorem integral_heatKernel_mul_sub_potential (hσS : σ * S ≠ 0) (y : Vec d)
    (w h : LocalHarmonic a z T) :
    (∫ x in ball z T, heatKernel y (σ * S) x * (w.potential x - h.potential x)) =
      ⟪heatLp z T y hσS, w.toPair.1 - h.toPair.1⟫_ℝ := by
  rw [inner_heatLp]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub w.toPair.1 h.toPair.1, w.toPair_fst_ae, h.toPair_fst_ae] with
    x h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]

/-- **The comparison of a coordinate minimizer with an admissible competitor.** -/
theorem IsCoordinateMinimizer.localizationObjective_sub_le (hσS : σ * S ≠ 0) {i : Fin d}
    {w h : LocalHarmonic a z T} (hw : IsCoordinateMinimizer S σ θ C i w)
    (hh : IsLocalizationAdmissible C h) :
    localizationObjective z T S σ θ (fun x => w.potential x - h.potential x) ≤
      4 * localizationObjective z T S σ θ (fun x => h.potential x - (x - z) i) := by
  have hmin := hw.2 h hh
  rw [w.objective_eq i, h.objective_eq i, pairObjective_eq hσS, pairObjective_eq hσS] at hmin
  rw [h.objective_eq i, pairObjective_eq hσS]
  unfold localizationObjective
  simp_rw [integral_heatKernel_mul_sub_potential hσS _ w h]
  set ℓ := coordinateLp z T i
  set u := w.toPair.1 - ℓ
  set v := h.toPair.1 - ℓ
  have huv : w.toPair.1 - h.toPair.1 = u - v := by simp only [u, v]; abel
  simp_rw [huv, inner_sub_right]
  rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul] at hmin ⊢
  have hint : ∀ f : Lp ℝ 2 (ballMeasure z T),
      IntegrableOn (fun y => ⟪heatLp z T y hσS, f⟫_ℝ ^ 2) (ball z (S / θ)) volume :=
    fun f => integrableOn_inner_heatLp_sq hσS (S / θ) f
  have hpt : ∀ y, (⟪heatLp z T y hσS, u⟫_ℝ - ⟪heatLp z T y hσS, v⟫_ℝ) ^ 2 ≤
      2 * ⟪heatLp z T y hσS, u⟫_ℝ ^ 2 + 2 * ⟪heatLp z T y hσS, v⟫_ℝ ^ 2 := fun y => by
    nlinarith [sq_nonneg (⟪heatLp z T y hσS, u⟫_ℝ + ⟪heatLp z T y hσS, v⟫_ℝ)]
  have hmono : ∫ y in ball z (S / θ), (⟪heatLp z T y hσS, u⟫_ℝ - ⟪heatLp z T y hσS, v⟫_ℝ) ^ 2 ≤
      ∫ y in ball z (S / θ), (2 * ⟪heatLp z T y hσS, u⟫_ℝ ^ 2 + 2 * ⟪heatLp z T y hσS, v⟫_ℝ ^ 2) := by
    refine setIntegral_mono_on ?_ (((hint u).const_mul 2).add ((hint v).const_mul 2))
      (measurableSet_ball z (S / θ)) fun y _ => hpt y
    have := hint (u - v)
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only [inner_sub_right]
  rw [integral_add ((hint u).const_mul 2) ((hint v).const_mul 2), integral_const_mul,
    integral_const_mul] at hmono
  have hvol : 0 ≤ (volume.real (ball z (S / θ)))⁻¹ := inv_nonneg.2 measureReal_nonneg
  have hmin' : (volume.real (ball z (S / θ)))⁻¹ *
      ∫ y in ball z (S / θ), ⟪heatLp z T y hσS, u⟫_ℝ ^ 2 ≤
      (volume.real (ball z (S / θ)))⁻¹ * ∫ y in ball z (S / θ), ⟪heatLp z T y hσS, v⟫_ℝ ^ 2 :=
    hmin
  calc (volume.real (ball z (S / θ)))⁻¹ * ∫ y in ball z (S / θ),
        (⟪heatLp z T y hσS, u⟫_ℝ - ⟪heatLp z T y hσS, v⟫_ℝ) ^ 2
      ≤ (volume.real (ball z (S / θ)))⁻¹ * (2 * (∫ y in ball z (S / θ),
          ⟪heatLp z T y hσS, u⟫_ℝ ^ 2) + 2 * ∫ y in ball z (S / θ),
          ⟪heatLp z T y hσS, v⟫_ℝ ^ 2) := mul_le_mul_of_nonneg_left hmono hvol
    _ ≤ 4 * ((volume.real (ball z (S / θ)))⁻¹ * ∫ y in ball z (S / θ),
          ⟪heatLp z T y hσS, v⟫_ℝ ^ 2) := by nlinarith

end QSH
