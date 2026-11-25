import QuantitativeStochasticHomogenization.AppB.TheoremB9

/-!
# Proposition B.11: the Sobolev–Poincaré–Wirtinger inequality

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix B, Proposition B.11 in the case `α = 1`, on bounded convex domains: for a bounded open
convex `U ⊆ ℝ^d` and `p ∈ [1, d)` there is `C(p, U, d)` such that every `u ∈ W^{1,p}(U)` satisfies
`‖u - (u)_U‖_{L^{p*}(U)} ≤ C ‖∇u‖_{L^p(U)}` with `p* = dp/(d-p)`.

The proof is the Sobolev–Poincaré inequality on bounded convex domains of the elliptic regularity
library, `PDE.exists_convexSobolevPoincare_constant` (Gilbarg–Trudinger, Lemma 7.16 and
Theorem 7.10), converted from normalized to unnormalized norms.
-/

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

theorem isOpenBoundedConvexDomain_of_isBounded {U : Set (Vec d)} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) : PDE.IsOpenBoundedConvexDomain U := by
  refine ⟨hUo, ?_, hUc⟩
  obtain ⟨R, hR⟩ := hUb.subset_closedBall 0
  refine ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x hx i => ?_⟩
  have hx' : ‖x‖ ≤ R := by simpa using hR hx
  have := norm_le_pi_norm x i
  rw [Real.norm_eq_abs] at this
  exact this.trans (hx'.trans (le_max_left _ _))

theorem exists_hasEuclideanDiameterLE {U : Set (Vec d)} (hUb : Bornology.IsBounded U) :
    ∃ D : ℝ, 0 < D ∧ PDE.HasEuclideanDiameterLE U D := by
  obtain ⟨R, hR⟩ := hUb.subset_closedBall 0
  refine ⟨Real.sqrt d * (2 * max R 0) + 1, by positivity, fun x hx y hy => ?_⟩
  have hx' : ‖x‖ ≤ max R 0 := (by simpa using hR hx : ‖x‖ ≤ R).trans (le_max_left _ _)
  have hy' : ‖y‖ ≤ max R 0 := (by simpa using hR hy : ‖y‖ ≤ R).trans (le_max_left _ _)
  calc PDE.vecEuclideanNorm (x - y) ≤ Real.sqrt d * ‖x - y‖ :=
        PDE.vecEuclideanNorm_le_sqrt_natCast_mul_norm _
    _ ≤ Real.sqrt d * (2 * max R 0) := by
        gcongr
        linarith [norm_sub_le x y]
    _ ≤ _ := by linarith

/-- **Proposition B.11** (Sobolev–Poincaré–Wirtinger inequality), the case `α = 1`, on bounded
convex domains: for a bounded open convex `U` and `p ∈ [1, d)` there is `C(p, U, d)` such that
`‖u - (u)_U‖_{L^{dp/(d-p)}(U)} ≤ C ‖∇u‖_{L^p(U)}` for every `u ∈ W^{1,p}(U)`. -/
theorem proposition_B_11_convex {U : Set (Vec d)} (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUc : Convex ℝ U) (p : ℝ) (hp : 1 ≤ p) (hpd : p < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
      IsW1p U (ENNReal.ofReal p) u g →
        eLpNorm (fun x => u x - ⨍ y in U, u y) (ENNReal.ofReal (d * p / (d - p)))
            (volume.restrict U) ≤
          ENNReal.ofReal C *
            eLpNorm (fun x => euclideanNorm (g x)) (ENNReal.ofReal p) (volume.restrict U) := by
  have hd : 2 ≤ d := by
    have : 1 < d := by exact_mod_cast (show (1 : ℝ) < d by linarith)
    omega
  have hp0 : 0 < p := by linarith
  rcases U.eq_empty_or_nonempty with hU | hUne
  · refine ⟨1, one_pos, fun u g _ => ?_⟩
    simp [hU]
  obtain ⟨C1, hC1, hP⟩ := PDE.exists_convexSobolevPoincare_constant d hd
  obtain ⟨D, hD, hDU⟩ := exists_hasEuclideanDiameterLE hUb
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hUne).ne'
  have hUt : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hv : 0 < (volume U).toReal := ENNReal.toReal_pos hU0 hUt
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℝ, γ = p * ((d : ℝ) - 1) / ((d : ℝ) - p) := ⟨_, rfl⟩
  have hγ : 0 < γ := by
    rw [hγdef]
    exact div_pos (mul_pos hp0 (by linarith)) (by linarith)
  refine ⟨C1 * γ * D * (volume U).toReal ^ (-(1 / (d : ℝ))), by positivity, fun u g hu => ?_⟩
  have hs := hP p hp hpd U D (isOpenBoundedConvexDomain_of_isBounded hUo hUb hUc) hUne hDU
    hu.toW1pFunction
  rw [← hγdef] at hs
  have havg : PDE.integralAverage U u = ⨍ y in U, u y ∂volume := by
    rw [PDE.integralAverage, setAverage_eq, smul_eq_mul, measureReal_def]
  change PDE.eLpMeanNormOn U (ENNReal.ofReal (PDE.sobolevConjugate d p))
      (fun x => u x - PDE.integralAverage U u) ≤
    ENNReal.ofReal (C1 * γ * D) *
      PDE.eLpMeanNormOn U (ENNReal.ofReal p) (fun x => euclideanNorm (g x)) at hs
  rw [havg] at hs
  have h1 := eLpNorm_le_of_eLpMeanNormOn_le hU0 hUt hp0 (PDE.sobolevConjugate_pos hp0 hpd)
    (one_div_sobolevConjugate hp0 hpd) hs
  refine h1.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (show 0 ≤ C1 * γ * D by positivity), ← ENNReal.ofReal_rpow_of_pos hv,
    ENNReal.ofReal_toReal hUt]

end QSH
