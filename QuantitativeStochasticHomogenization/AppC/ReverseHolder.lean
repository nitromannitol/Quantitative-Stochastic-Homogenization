import QuantitativeStochasticHomogenization.AppC.InteriorCaccioppoli
import SobolevStatements.ConvexSobolevPoincare

/-!
# The reverse Hölder inequality for gradients of solutions

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix C, Corollary C.3: under the assumptions of Lemma C.2,
`‖∇u‖_{L̲²(B_{r/2})} ≤ C (‖∇u‖_{L̲^{2_*}(B_r)} + ‖h‖_{H̲^{-1}(B_r)})` with `2_* = 2d/(d+2)` and `C(d, Λ)`.

The proof is the book's: the Sobolev–Poincaré inequality
`‖u - (u)_{B_r}‖_{L̲²(B_r)} ≤ C r ‖∇u‖_{L̲^{2_*}(B_r)}`, here the convex-domain Sobolev–Poincaré
inequality of the elliptic regularity library `PDE.exists_convexSobolevPoincare_constant` with
`p = 2_*` (whose Sobolev conjugate is `2`) and diameter `2r`, inserted into Lemma C.2. The
exponent `2_*` is at least `1` exactly when `d ≥ 2`, the book's setting.
-/

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The normalized `L²(U)` norm of an `L²(U)` function is its root mean square. -/
theorem eLpMeanNormOn_two_eq_ofReal_scalarRms {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    {w : Vec d → ℝ} (hw : MemLp w 2 (volume.restrict U)) :
    PDE.eLpMeanNormOn U 2 w = ENNReal.ofReal (scalarRms volume U w) := by
  set μ := PDE.normalizedVolumeOn U with hμ
  have hmem : MemLp w 2 μ := hw.smul_measure (ENNReal.inv_ne_top.mpr hU0)
  have havg : ⨍ x in U, w x ^ 2 ∂volume = ∫ x, w x ^ 2 ∂μ := by
    rw [hμ, PDE.integral_normalizedVolumeOn_eq_integralAverage, PDE.integralAverage,
      setAverage_eq, smul_eq_mul, measureReal_def]
  rw [PDE.eLpMeanNormOn, ← hμ, hmem.eLpNorm_eq_integral_rpow_norm two_ne_zero
    ENNReal.ofNat_ne_top, scalarRms, havg, Real.sqrt_eq_rpow, ENNReal.toReal_ofNat, ← one_div]
  congr 2
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  change ‖w x‖ ^ (2 : ℝ) = w x ^ 2
  rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]

/-- **Corollary C.3** on a ball `B_r(z)`, for `d ≥ 2`: under the assumptions of Lemma C.2,
`‖∇u‖_{L̲²(B_{r/2}(z))} ≤ C (‖∇u‖_{L̲^{2_*}(B_r(z))} + ‖h‖_{H̲^{-1}(B_r(z))})`, `2_* = 2d/(d+2)`. -/
theorem interiorReverseHolder (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : Vec d) (r : ℝ), 0 < r → ∀ (a : CoefficientField d Λ)
      (u : Vec d → ℝ) (g : Vec d → Vec d) (f : Vec d → ℝ) (F : Vec d → Vec d),
      MemLp u 2 (volume.restrict (ball z r)) →
      (∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball z r))) →
      HasWeakGradient (ball z r) u g →
      MemLp f 2 (volume.restrict (ball z r)) →
      (∀ i, MemLp (fun x => F x i) 2 (volume.restrict (ball z r))) →
      HasWeakDivergence (ball z r) (fun x => (a x).mulVec (g x) + F x) (fun x => -f x) →
      ENNReal.ofReal (vectorRms volume (ball z (r / 2)) g) ≤
        ENNReal.ofReal C * (PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal (2 * d / (d + 2)))
            (fun x => euclideanNorm (g x)) + negativeSobolevOneNorm 2 (ball z r) f F) := by
  obtain ⟨C₂, hC₂, hcacc⟩ := interiorCaccioppoli (d := d) hΛ
  obtain ⟨Cs, hCs, hsp⟩ := PDE.exists_convexSobolevPoincare_constant d hd
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨p, hpdef⟩ : ∃ p : ℝ, p = 2 * d / (d + 2) := ⟨_, rfl⟩
  have hp1 : 1 ≤ p := by
    rw [hpdef, le_div_iff₀ (by linarith)]
    linarith
  have hpd : p < d := by
    rw [hpdef, div_lt_iff₀ (by linarith)]
    nlinarith
  have hp2 : p ≤ 2 := by
    rw [hpdef, div_le_iff₀ (by linarith)]
    linarith
  have hconj : PDE.sobolevConjugate d p = 2 := by
    rw [PDE.sobolevConjugate, hpdef]
    have h1 : (d : ℝ) + 2 ≠ 0 := by linarith
    have h2 : (d : ℝ) - 2 * d / (d + 2) = d ^ 2 / (d + 2) := by
      field_simp
      ring
    rw [h2]
    have h3 : (d : ℝ) ^ 2 ≠ 0 := by positivity
    field_simp
  obtain ⟨k, hkdef⟩ : ∃ k : ℝ, k = p * ((d : ℝ) - 1) / ((d : ℝ) - p) := ⟨_, rfl⟩
  have hk : 0 ≤ k := by
    rw [hkdef]
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  refine ⟨C₂ * (2 * Cs * k + 1), by positivity, ?_⟩
  intro z r hr a u g f F hu hg hw hf hF hdiv
  have h2 := hcacc z r hr a u g f F hu hg hw hf hF hdiv
  have hUe : ball z r = PDE.euclideanBall z r := ball_eq_euclideanBall z hr
  have hconv : PDE.IsOpenBoundedConvexDomain (ball z r) := by
    rw [hUe]
    exact PDE.isOpenBoundedConvexDomain_euclideanBall z hr
  have hU0 : volume (ball z r) ≠ 0 := by
    rw [hUe]
    exact (PDE.volume_euclideanBall_pos z hr).ne'
  have hUfin : volume (ball z r) ≠ ⊤ := by
    rw [hUe]
    exact PDE.volume_euclideanBall_ne_top z hr.le
  have : IsFiniteMeasure (volume.restrict (ball z r)) := isFiniteMeasure_restrict.mpr hUfin
  have hne : (ball z r).Nonempty := by
    rw [hUe]
    exact PDE.euclideanBall_nonempty z hr
  have hdiam : PDE.HasEuclideanDiameterLE (ball z r) (2 * r) := by
    rw [hUe]
    exact PDE.hasEuclideanDiameterLE_euclideanBall z hr
  have hp2' : ENNReal.ofReal p ≤ 2 := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal hp2
  let uw : PDE.W1pFunction (ball z r) (ENNReal.ofReal p) :=
    { toFun := u
      grad := g
      memLp := hu.mono_exponent hp2'
      gradMemLp := fun i => (hg i).mono_exponent hp2'
      hasWeakGradient := (toH1FunctionOn hu hg hw).hasWeakGradient }
  have hs := hsp p hp1 hpd (ball z r) (2 * r) hconv hne hdiam uw
  change PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal (PDE.sobolevConjugate d p))
      (fun x => u x - PDE.integralAverage (ball z r) u) ≤
    ENNReal.ofReal (Cs * (p * ((d : ℝ) - 1) / ((d : ℝ) - p)) * (2 * r)) *
      PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal p) (fun x => euclideanNorm (g x)) at hs
  have havg : PDE.integralAverage (ball z r) u = ⨍ y in ball z r, u y ∂volume := by
    rw [PDE.integralAverage, setAverage_eq, smul_eq_mul, measureReal_def]
  rw [hconj, ENNReal.ofReal_ofNat, havg, ← hkdef] at hs
  have hwm : MemLp (fun x => u x - ⨍ y in ball z r, u y ∂volume) 2 (volume.restrict (ball z r)) :=
    hu.sub (memLp_const _)
  have hrms := eLpMeanNormOn_two_eq_ofReal_scalarRms hU0 hwm
  rw [← hpdef]
  set N := PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal p) (fun x => euclideanNorm (g x))
    with hN
  set Hn := negativeSobolevOneNorm 2 (ball z r) f F with hHn
  have hkey : ENNReal.ofReal (r⁻¹ * scalarRms volume (ball z r)
      (fun x => u x - ⨍ y in ball z r, u y ∂volume)) ≤ ENNReal.ofReal (2 * Cs * k) * N := by
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr hr.le), ← hrms]
    calc ENNReal.ofReal r⁻¹ * PDE.eLpMeanNormOn (ball z r) 2
          (fun x => u x - ⨍ y in ball z r, u y ∂volume)
        ≤ ENNReal.ofReal r⁻¹ * (ENNReal.ofReal (Cs * k * (2 * r)) * N) := by gcongr
      _ = ENNReal.ofReal (2 * Cs * k) * N := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
        congr 2
        field_simp
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * Cs * k + 1) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg hCs.le hk])
  have hle : ENNReal.ofReal (2 * Cs * k) ≤ ENNReal.ofReal (2 * Cs * k + 1) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  calc ENNReal.ofReal (vectorRms volume (ball z (r / 2)) g)
      ≤ ENNReal.ofReal C₂ * (ENNReal.ofReal (r⁻¹ * scalarRms volume (ball z r)
          (fun x => u x - ⨍ y in ball z r, u y ∂volume)) + Hn) := h2
    _ ≤ ENNReal.ofReal C₂ * (ENNReal.ofReal (2 * Cs * k + 1) * N +
          ENNReal.ofReal (2 * Cs * k + 1) * Hn) := by
        gcongr
        · exact hkey.trans (by gcongr)
        · calc Hn = 1 * Hn := (one_mul _).symm
            _ ≤ ENNReal.ofReal (2 * Cs * k + 1) * Hn := by gcongr
    _ = ENNReal.ofReal (C₂ * (2 * Cs * k + 1)) * (N + Hn) := by
        rw [← mul_add, ← mul_assoc, ← ENNReal.ofReal_mul hC₂.le]

/-- **Corollary C.3.** For `d ≥ 2`, under the assumptions of Lemma C.2 on `B_r`,
`‖∇u‖_{L̲²(B_{r/2})} ≤ C (‖∇u‖_{L̲^{2_*}(B_r)} + ‖h‖_{H̲^{-1}(B_r)})` with `2_* = 2d/(d+2)` and
`C(d, Λ)`. -/
theorem corollary_C_3 (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ), 0 < r → ∀ (a : CoefficientField d Λ)
      (u : Vec d → ℝ) (g : Vec d → Vec d) (f : Vec d → ℝ) (F : Vec d → Vec d),
      MemLp u 2 (volume.restrict (ball 0 r)) →
      (∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 r))) →
      HasWeakGradient (ball 0 r) u g →
      MemLp f 2 (volume.restrict (ball 0 r)) →
      (∀ i, MemLp (fun x => F x i) 2 (volume.restrict (ball 0 r))) →
      HasWeakDivergence (ball 0 r) (fun x => (a x).mulVec (g x) + F x) (fun x => -f x) →
      ENNReal.ofReal (vectorRms volume (ball 0 (r / 2)) g) ≤
        ENNReal.ofReal C * (PDE.eLpMeanNormOn (ball 0 r) (ENNReal.ofReal (2 * d / (d + 2)))
            (fun x => euclideanNorm (g x)) + negativeSobolevOneNorm 2 (ball 0 r) f F) := by
  obtain ⟨C, hC, h⟩ := interiorReverseHolder hd hΛ
  exact ⟨C, hC, fun r hr => h 0 r hr⟩

end QSH
