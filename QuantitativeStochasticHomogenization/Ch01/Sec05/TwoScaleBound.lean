import QuantitativeStochasticHomogenization.Ch01.Sec05.TwoScaleIdentity

/-!
# The bound (1.64) of the two-scale expansion

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.5, Step 1 of the proof of Theorem 1.17: in the identity `integral_twoScaleGrad_eq`, the
three terms are bounded by Hölder's inequality and by the definition of the `H^{-1}` norm on the
cube `V = ε □_m ⊇ U`:
`|∫_U a(·/ε)∇w · ∇ψ| ≤ (∑_k ‖(T₂)_k‖ + ∑_{j,k} ‖(T₃)_{j,k}‖ + |V|^{1/2} (1 + d) M ∑_{j,i} N_{j,i})
  (‖ψ‖ + ∑_k ‖∂_k ψ‖)` (`abs_integral_twoScaleGrad_le`), with unnormalized `L²(U)` norms
(`l2`), `M` a bound of the first and second derivatives of the multipliers `G_j` and `N_{j,i}` a
bound of `‖(a(·/ε)(e_j + DΦ_j) - ā e_j)_i‖_{H̲^{-1}(V)}`. The multiplier estimate
`|∫_U F χ| ≤ |V|^{1/2} N (‖χ‖ + ∑_k ‖∂_k χ‖)` for tests `χ` supported in `U` is
`abs_setIntegral_mul_le_of_negativeSobolevOneNorm`.
-/

open MeasureTheory Filter Set

noncomputable section

namespace QSH

namespace TwoScale

variable {d : ℕ} {Λ : ℝ}

/-! ## Unnormalized `L²` norms -/

/-- The unnormalized `L²(W)` norm. -/
def l2 (W : Set (Vec d)) (f : Vec d → ℝ) : ℝ := (eLpNorm f 2 (volume.restrict W)).toReal

theorem l2_nonneg (W : Set (Vec d)) (f : Vec d → ℝ) : 0 ≤ l2 W f := ENNReal.toReal_nonneg

theorem sqrt_setIntegral_sq_eq_l2 {W : Set (Vec d)} {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict W)) : Real.sqrt (∫ x in W, f x ^ 2) = l2 W f := by
  rw [← sq_toReal_eLpNorm_two_eq hf]
  exact Real.sqrt_sq ENNReal.toReal_nonneg

theorem abs_setIntegral_mul_le_l2 {W : Set (Vec d)} {f h : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict W)) (hh : MemLp h 2 (volume.restrict W)) :
    |∫ x in W, f x * h x| ≤ l2 W f * l2 W h := by
  have := abs_integral_mul_le_sqrt_mul_sqrt hf hh
  rwa [sqrt_setIntegral_sq_eq_l2 hf, sqrt_setIntegral_sq_eq_l2 hh] at this

theorem l2_add_le {W : Set (Vec d)} {f h : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict W))
    (hh : MemLp h 2 (volume.restrict W)) :
    l2 W (fun x => f x + h x) ≤ l2 W f + l2 W h :=
  ENNReal.toReal_le_add (eLpNorm_add_le (f := f) (g := h) (μ := volume.restrict W) (p := 2)
    one_le_two) hf.eLpNorm_ne_top hh.eLpNorm_ne_top

theorem l2_le_mul {W : Set (Vec d)} {f h : Vec d → ℝ} (hf : AEStronglyMeasurable f
    (volume.restrict W)) (hh : MemLp h 2 (volume.restrict W)) {M : ℝ} (hM : 0 ≤ M)
    (hfh : ∀ x, |f x| ≤ M * |h x|) : l2 W f ≤ M * l2 W h := by
  have h1 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (g := h) (c := M) hf
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hfh x) 2
  unfold l2
  rw [← ENNReal.toReal_ofReal hM, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hh.eLpNorm_ne_top) h1

theorem l2_eq_of_support {U V : Set (Vec d)} (hUV : U ⊆ V) {f : Vec d → ℝ}
    (hf : AEStronglyMeasurable f volume) (hsupp : ∀ x, x ∉ U → f x = 0) :
    l2 V f = l2 U f := by
  have hs : Function.support f ⊆ U := fun x hx => by
    by_contra h
    exact hx (hsupp x h)
  unfold l2
  rw [eLpNorm_restrict_eq_of_support_subset hf (hs.trans hUV),
    eLpNorm_restrict_eq_of_support_subset hf hs]

theorem toReal_eLpMeanNormOn_two_eq {W : Set (Vec d)} (hWt : volume W ≠ ⊤) (f : Vec d → ℝ) :
    (PDE.eLpMeanNormOn W 2 f).toReal = ((volume W).toReal ^ (1 / 2 : ℝ))⁻¹ * l2 W f := by
  rw [PDE.eLpMeanNormOn, PDE.normalizedVolumeOn,
    eLpNorm_smul_measure_of_ne_zero (ENNReal.inv_ne_zero.mpr hWt), smul_eq_mul,
    ENNReal.toReal_mul]
  congr 1
  rw [ENNReal.inv_rpow, ENNReal.toReal_inv, ENNReal.toReal_rpow]
  norm_num

theorem abs_setIntegral_dot_le {W : Set (Vec d)} {X Y : Vec d → Vec d}
    (hX : ∀ k, MemLp (fun x => X x k) 2 (volume.restrict W))
    (hY : ∀ k, MemLp (fun x => Y x k) 2 (volume.restrict W)) :
    |∫ x in W, dot (X x) (Y x)| ≤
      (∑ k, l2 W (fun x => X x k)) * ∑ k, l2 W (fun x => Y x k) := by
  have hint : ∀ k ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun x => X x k * Y x k) (volume.restrict W) := fun k _ =>
    integrable_mul_of_memLp_two (hX k) (hY k)
  change |∫ x in W, ∑ k, X x k * Y x k| ≤ _
  rw [integral_finsetSum _ hint, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  refine (abs_setIntegral_mul_le_l2 (hX k) (hY k)).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (l2_nonneg _ _)
  exact Finset.single_le_sum (f := fun k => l2 W (fun x => Y x k))
    (fun k _ => l2_nonneg _ _) (Finset.mem_univ k)

/-! ## The multiplier estimate -/

/-- **The `H^{-1}` multiplier estimate**: for a test `χ` supported in `U ⊆ V`, `|V| ≥ 1`, and
`‖F‖_{H̲^{-1}(V)} ≤ N`, `|∫_U F χ| ≤ |V|^{1/2} N (‖χ‖_{L²(U)} + ∑_k ‖∂_k χ‖_{L²(U)})`. -/
theorem abs_setIntegral_mul_le_of_negativeSobolevOneNorm {U V : Set (Vec d)} (hUV : U ⊆ V)
    (hV1 : 1 ≤ (volume V).toReal) (hVt : volume V ≠ ⊤) {F : Vec d → ℝ} {N : ℝ} (hN0 : 0 ≤ N)
    (hN : negativeSobolevOneNorm 2 V F 0 ≤ ENNReal.ofReal N) {χ : Vec d → ℝ}
    (hχ : IsSpatialTest U χ) :
    |∫ x in U, F x * χ x| ≤ (volume V).toReal ^ (1 / 2 : ℝ) * N *
      (l2 U χ + ∑ k, l2 U (coordinateDerivative k χ)) := by
  have hV0 : volume V ≠ 0 := by
    intro h
    rw [h, ENNReal.toReal_zero] at hV1
    linarith
  have hVpos : 0 < (volume V).toReal := by linarith
  have hχV : IsSpatialTest V χ := ⟨hχ.1, hχ.2.1, hχ.2.2.trans hUV⟩
  have hpair := abs_distributionPairing_le hN0 hN hχV
  have hq : ENNReal.ofReal ((2 : ℝ) / (2 - 1)) = 2 := by norm_num
  rw [hq] at hpair
  have hzero : ∀ x, x ∉ tsupport χ → F x * χ x = 0 := fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hUint : ∫ x in U, F x * χ x = ∫ x in V, F x * χ x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hzero x fun h => hx (hχ.2.2 h),
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
        hzero x fun h => hx (hUV (hχ.2.2 h))]
  have hdp : distributionPairing V F 0 χ = (volume V).toReal⁻¹ * ∫ x in V, F x * χ x := by
    simp [distributionPairing, dot, setAverage_eq, measureReal_def, smul_eq_mul]
  have hχm : ∀ f : Vec d → ℝ, Continuous f → (∀ x, x ∉ tsupport χ → f x = 0) →
      l2 V f = l2 U f := fun f hf hf0 =>
    l2_eq_of_support hUV hf.aestronglyMeasurable fun x hx => hf0 x fun h => hx (hχ.2.2 h)
  have hdχ : ∀ k x, x ∉ tsupport χ → coordinateDerivative k χ x = 0 := fun k x hx =>
    coordinateDerivative_eq_zero_of_notMem_tsupport hx k
  have hnorm : sobolevOneTestNorm 2 V χ ≤ ((volume V).toReal ^ (1 / 2 : ℝ))⁻¹ *
      (l2 U χ + ∑ k, l2 U (coordinateDerivative k χ)) := by
    unfold sobolevOneTestNorm
    rw [toReal_eLpMeanNormOn_two_eq hVt, hχm χ hχ.1.continuous
      (fun x hx => image_eq_zero_of_notMem_tsupport hx)]
    simp only [toReal_eLpMeanNormOn_two_eq hVt]
    rw [Finset.sum_congr rfl fun k _ => by
      rw [hχm _ (continuous_coordinateDerivative (hχ.1.of_le (by simp)) k) (hdχ k)], ← Finset.mul_sum,
      mul_add]
    have h1 : (volume V).toReal ^ ((-1 : ℝ) / d) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hV1 (div_nonpos_of_nonpos_of_nonneg (by norm_num)
        (Nat.cast_nonneg d))
    have h2 : 0 ≤ ((volume V).toReal ^ (1 / 2 : ℝ))⁻¹ * l2 U χ :=
      mul_nonneg (inv_nonneg.2 (by positivity)) (l2_nonneg _ _)
    nlinarith
  have hsq : (volume V).toReal * ((volume V).toReal ^ (1 / 2 : ℝ))⁻¹ =
      (volume V).toReal ^ (1 / 2 : ℝ) := by
    have h := Real.rpow_add hVpos (1 / 2 : ℝ) (1 / 2 : ℝ)
    norm_num at h
    have hs : 0 < (volume V).toReal ^ (1 / 2 : ℝ) := by positivity
    field_simp
    nlinarith [h]
  rw [hUint]
  have e : |∫ x in V, F x * χ x| = (volume V).toReal * |distributionPairing V F 0 χ| := by
    rw [hdp, abs_mul, abs_of_pos (inv_pos.2 hVpos), ← mul_assoc, mul_inv_cancel₀ hVpos.ne',
      one_mul]
  rw [e]
  calc (volume V).toReal * |distributionPairing V F 0 χ|
      ≤ (volume V).toReal * (N * (((volume V).toReal ^ (1 / 2 : ℝ))⁻¹ *
          (l2 U χ + ∑ k, l2 U (coordinateDerivative k χ)))) :=
        mul_le_mul_of_nonneg_left (hpair.trans (mul_le_mul_of_nonneg_left hnorm hN0)) hVpos.le
    _ = (volume V).toReal * ((volume V).toReal ^ (1 / 2 : ℝ))⁻¹ * N *
          (l2 U χ + ∑ k, l2 U (coordinateDerivative k χ)) := by ring
    _ = _ := by rw [hsq]

end TwoScale

end QSH
