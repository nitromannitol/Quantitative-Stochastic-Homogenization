import QuantitativeStochasticHomogenization.Ch01.Sec05.TwoScaleBound
import QuantitativeStochasticHomogenization.Ch02.Sec03.HatNormAlgebra
import QuantitativeStochasticHomogenization.AppC.GlobalCaccioppoli

/-!
# Negative Sobolev norms in the proof of Theorem 1.17

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.5, Steps 2 and 3 of the proof of Theorem 1.17:

* a bound `|∫_U F φ| ≤ K (‖φ‖ + ∑_k ‖∂_k φ‖)` on the tests of `U` holds on `H¹₀(U)`
  (`abs_setIntegral_mul_le_of_H01`);
* the multiplier estimate on `Ĥ⁻¹(U)`:
  `‖χ F‖_{Ĥ̲⁻¹(U)} ≤ |U|^{-1/2} |V|^{1/2} N ((M₀ + d M₁) |U|^{1/d} + d M₀)` for `χ` smooth with
  compact support in a convex `U ⊆ V`, `|χ| ≤ M₀`, `|∇χ| ≤ M₁` and `‖F‖_{H̲⁻¹(V)} ≤ N`
  (`hatNegativeSobolevNorm_mul_le`);
* `‖∂_k H‖_{Ĥ̲⁻¹(U)} ≤ ‖H‖_{L̲²(U)}` for `H ∈ H¹₀(U)`
  (`hatNegativeSobolevNorm_grad_le_of_H01`);
* the normalized form `‖∇·Φ‖_{H̲⁻¹(U)} ≤ |U|^{-1/2} (|U|^{1/d} + 1) K` of the bound (1.64)
  (`negativeSobolevOneNorm_le_of_abs_setIntegral_le`).
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

namespace TwoScale

variable {d : ℕ}

theorem tendsto_l2_of_tendsto_eLpNorm_sub {U : Set (Vec d)} {f : Vec d → ℝ}
    {fs : ℕ → Vec d → ℝ} (hf : MemLp f 2 (volume.restrict U))
    (hfs : ∀ n, MemLp (fs n) 2 (volume.restrict U))
    (h : Tendsto (fun n => eLpNorm (fun x => fs n x - f x) 2 (volume.restrict U)) atTop (𝓝 0)) :
    Tendsto (fun n => l2 U (fs n)) atTop (𝓝 (l2 U f)) := by
  have hLp : Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hf.toLp f)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fs hfs f hf).mpr h
  have hnorm := (continuous_norm.tendsto _).comp hLp
  simp only [Function.comp_def, Lp.norm_toLp] at hnorm
  exact hnorm

/-- **A bound on tests extends to `H¹₀(U)`.** -/
theorem abs_setIntegral_mul_le_of_H01 {U : Set (Vec d)} {F : Vec d → ℝ}
    (hF : MemLp F 2 (volume.restrict U)) {K : ℝ}
    (hbound : ∀ φ, IsSpatialTest U φ →
      |∫ x in U, F x * φ x| ≤ K * (l2 U φ + ∑ k, l2 U (coordinateDerivative k φ)))
    {w : Vec d → ℝ} {h : Vec d → Vec d} (hw : H01 U w h) :
    |∫ x in U, F x * w x| ≤ K * (l2 U w + ∑ k, l2 U (fun x => h x k)) := by
  obtain ⟨hw2, hh2, -, φ, hφ, hconv, hgconv⟩ := hw
  have hφm : ∀ n, MemLp (φ n) 2 (volume.restrict U) := fun n =>
    memLp_two_of_continuous_hasCompactSupport (hφ n).1.continuous (hφ n).2.1
  have hφg : ∀ n k, MemLp (coordinateDerivative k (φ n)) 2 (volume.restrict U) := fun n k =>
    memLp_two_of_continuous_hasCompactSupport (continuous_gradient_apply (hφ n).1 k)
      (hasCompactSupport_gradient_apply (hφ n).2.1 k)
  have t1 : Tendsto (fun n => eLpNorm (fun x => φ n x - w x) 2 (volume.restrict U)) atTop
      (𝓝 0) := tendsto_eLpNorm_two_of_tendsto_integral_sq (fun n => (hφm n).sub hw2) hconv
  have t2 : ∀ k, Tendsto (fun n => eLpNorm (fun x => coordinateDerivative k (φ n) x - h x k) 2
      (volume.restrict U)) atTop (𝓝 0) := by
    intro k
    refine tendsto_eLpNorm_two_of_tendsto_integral_sq (fun n => (hφg n k).sub (hh2.eval k)) ?_
    refine squeeze_zero (fun n => setIntegral_nonneg_of_ae (Eventually.of_forall fun x =>
      sq_nonneg _)) (fun n => ?_) hgconv
    have hint : Integrable (fun x => euclideanSq (gradient (φ n) x - h x)) (volume.restrict U) := by
      have h' : Integrable (fun x => ∑ i, (gradient (φ n) x - h x) i ^ 2) (volume.restrict U) :=
        integrable_finsetSum _ fun i _ => ((hφg n i).sub (hh2.eval i)).integrable_sq
      refine h'.congr (Eventually.of_forall fun x => ?_)
      simp [euclideanSq, dot, sq]
    exact setIntegral_mono ((hφg n k).sub (hh2.eval k)).integrable_sq hint fun x =>
      sq_apply_le_euclideanSq (gradient (φ n) x - h x) k
  have l1 := tendsto_l2_of_tendsto_eLpNorm_sub hw2 hφm t1
  have l2' : ∀ k, Tendsto (fun n => l2 U (coordinateDerivative k (φ n))) atTop
      (𝓝 (l2 U (fun x => h x k))) := fun k =>
    tendsto_l2_of_tendsto_eLpNorm_sub (hh2.eval k) (fun n => hφg n k) (t2 k)
  have i1 := (tendsto_integral_mul_of_eLpNorm_sub hF hw2 hφm t1).abs
  have r1 := (l1.add (tendsto_finsetSum Finset.univ fun k _ => l2' k)).const_mul K
  exact le_of_tendsto_of_tendsto' i1 r1 fun n => hbound (φ n) (hφ n)

theorem l2_eq_sqrt_mul_scalarRms {U : Set (Vec d)} (hUt : volume U ≠ ⊤) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) :
    l2 U f = (volume U).toReal ^ (1 / 2 : ℝ) * scalarRms volume U f := by
  rw [← sqrt_setIntegral_sq_eq_l2 hf, scalarRms, setAverage_eq, smul_eq_mul, measureReal_def,
    Real.sqrt_mul (inv_nonneg.2 ENNReal.toReal_nonneg), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    Real.inv_rpow ENNReal.toReal_nonneg]
  rcases eq_or_ne (volume U).toReal 0 with h0 | h0
  · have hz : volume.restrict U = 0 := by
      rw [Measure.restrict_eq_zero]
      rcases (ENNReal.toReal_eq_zero_iff _).1 h0 with h | h
      · exact h
      · exact absurd h hUt
    simp [hz]
  · have hpos : 0 < (volume U).toReal ^ (1 / 2 : ℝ) :=
      Real.rpow_pos_of_pos (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm h0)) _
    field_simp

theorem l2_apply_le_sqrt_mul_vectorRms {U : Set (Vec d)} (hUt : volume U ≠ ⊤) {G : Vec d → Vec d}
    (hG : ∀ i, MemLp (fun x => G x i) 2 (volume.restrict U)) (k : Fin d) :
    l2 U (fun x => G x k) ≤ (volume U).toReal ^ (1 / 2 : ℝ) * vectorRms volume U G := by
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUt
  have hint : Integrable (fun x => euclideanSq (G x)) (volume.restrict U) := by
    have h' : Integrable (fun x => ∑ i, G x i ^ 2) (volume.restrict U) :=
      integrable_finsetSum _ fun i _ => (hG i).integrable_sq
    refine h'.congr (Eventually.of_forall fun x => ?_)
    simp [euclideanSq, dot, sq]
  have h1 : ∫ x in U, G x k ^ 2 ≤ ∫ x in U, euclideanSq (G x) :=
    setIntegral_mono (hG k).integrable_sq hint fun x => sq_apply_le_euclideanSq (G x) k
  rw [← sqrt_setIntegral_sq_eq_l2 (hG k), vectorRms, setAverage_eq, smul_eq_mul, measureReal_def,
    Real.sqrt_mul (inv_nonneg.2 ENNReal.toReal_nonneg)]
  rcases eq_or_ne (volume U).toReal 0 with h0 | h0
  · have hz : volume.restrict U = 0 := by
      rw [Measure.restrict_eq_zero]
      rcases (ENNReal.toReal_eq_zero_iff _).1 h0 with h | h
      · exact h
      · exact absurd h hUt
    simp [hz]
  · have hV : 0 < (volume U).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm h0)
    rw [← mul_assoc, Real.sqrt_eq_rpow (volume U).toReal⁻¹, Real.inv_rpow hV.le,
      mul_inv_cancel₀ (Real.rpow_pos_of_pos hV _).ne', one_mul]
    exact Real.sqrt_le_sqrt h1

/-- **The `Ĥ⁻¹(U)` norm of a gradient of `H¹₀(U)`**: `‖∂_k H‖_{Ĥ̲⁻¹(U)} ≤ ‖H‖_{L̲²(U)}`. -/
theorem hatNegativeSobolevNorm_grad_le_of_H01 {U : Set (Vec d)} (hUt : volume U ≠ ⊤)
    {H : Vec d → ℝ} {DH : Vec d → Vec d} (hH : H01 U H DH) (k : Fin d) :
    hatNegativeSobolevNorm U (fun x => DH x k) ≤ ENNReal.ofReal (scalarRms volume U H) := by
  refine hatNegativeSobolevNorm_le_ofReal fun v G hv hn => ?_
  have hGi : ∀ i, MemLp (fun x => G x i) 2 (volume.restrict U) := fun i => hv.2.1.eval i
  have e := integral_grad_mul_h10 hv.1 hGi hv.2.2 hH.toH10Function k
  change ∫ x in U, G x k * H x = -∫ x in U, v x * DH x k at e
  have e' : ∫ x in U, DH x k * v x = -∫ x in U, G x k * H x := by
    rw [e, neg_neg]
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  have hUr := ENNReal.toReal_nonneg (a := volume U)
  rw [setAverage_eq, smul_eq_mul, measureReal_def, e', mul_neg, abs_neg, abs_mul,
    abs_of_nonneg (inv_nonneg.2 hUr)]
  have h1 := abs_setIntegral_mul_le_l2 (hGi k) hH.1
  have h2 := l2_apply_le_sqrt_mul_vectorRms hUt hGi k
  have h3 := l2_eq_sqrt_mul_scalarRms hUt hH.1
  have hvG : vectorRms volume U G ≤ 1 := by
    have := mul_nonneg (Real.rpow_nonneg hUr ((-1 : ℝ) / d)) (Real.sqrt_nonneg
      (⨍ x in U, (v x) ^ 2 ∂volume))
    unfold h1Norm at hn
    unfold scalarRms at hn
    linarith
  rcases eq_or_ne (volume U).toReal 0 with h0 | h0
  · rw [h0, inv_zero, zero_mul]
    exact Real.sqrt_nonneg _
  · have hV : 0 < (volume U).toReal := lt_of_le_of_ne hUr (Ne.symm h0)
    have hs : 0 < (volume U).toReal ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hV _
    have hss : (volume U).toReal ^ (1 / 2 : ℝ) * (volume U).toReal ^ (1 / 2 : ℝ) =
        (volume U).toReal := by
      rw [← Real.rpow_add hV]; norm_num
    have hr0 : 0 ≤ scalarRms volume U H := Real.sqrt_nonneg _
    calc (volume U).toReal⁻¹ * |∫ x in U, G x k * H x|
        ≤ (volume U).toReal⁻¹ * (l2 U (fun x => G x k) * l2 U H) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hUr)
      _ ≤ (volume U).toReal⁻¹ * (((volume U).toReal ^ (1 / 2 : ℝ) * 1) *
          ((volume U).toReal ^ (1 / 2 : ℝ) * scalarRms volume U H)) := by
          rw [h3]
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (h2.trans
            (mul_le_mul_of_nonneg_left hvG hs.le)) (by positivity)) (inv_nonneg.2 hUr)
      _ = (volume U).toReal⁻¹ * ((volume U).toReal ^ (1 / 2 : ℝ) *
          (volume U).toReal ^ (1 / 2 : ℝ)) * scalarRms volume U H := by ring
      _ = scalarRms volume U H := by rw [hss, inv_mul_cancel₀ hV.ne', one_mul]

/-- **The normalized form of (1.64)**: a bound `|∫_U Φ · ∇ψ| ≤ K (‖ψ‖ + ∑_k ‖∂_k ψ‖)` on the
tests gives `‖∇·Φ‖_{H̲⁻¹(U)} ≤ |U|^{-1/2} (|U|^{1/d} + 1) K`. -/
theorem negativeSobolevOneNorm_le_of_abs_setIntegral_le {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hUt : volume U ≠ ⊤) {Φ : Vec d → Vec d} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ ψ, IsSpatialTest U ψ →
      |∫ x in U, dot (Φ x) (gradient ψ x)| ≤ K * (l2 U ψ + ∑ k, l2 U (coordinateDerivative k ψ))) :
    negativeSobolevOneNorm 2 U 0 Φ ≤
      ENNReal.ofReal (((volume U).toReal ^ (1 / 2 : ℝ))⁻¹ *
        (((volume U).toReal ^ ((1 : ℝ) / d) + 1) * K)) := by
  have hV : 0 < (volume U).toReal := ENNReal.toReal_pos hU0 hUt
  have hs : 0 < (volume U).toReal ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hV _
  have hq : ENNReal.ofReal ((2 : ℝ) / (2 - 1)) = 2 := by norm_num
  refine iSup_le fun ⟨ψ, hψ, hψ1⟩ => ENNReal.ofReal_le_ofReal ?_
  rw [hq] at hψ1
  unfold sobolevOneTestNorm at hψ1
  simp only [toReal_eLpMeanNormOn_two_eq hUt] at hψ1
  have hdp : distributionPairing U 0 Φ ψ = -((volume U).toReal⁻¹ *
      ∫ x in U, dot (Φ x) (gradient ψ x)) := by
    simp [distributionPairing, setAverage_eq, measureReal_def, smul_eq_mul]
  rw [hdp, abs_neg, abs_mul, abs_of_pos (inv_pos.2 hV)]
  have hb := h ψ hψ
  have hl := l2_nonneg U ψ
  have hsum : 0 ≤ ∑ k, l2 U (coordinateDerivative k ψ) := Finset.sum_nonneg fun _ _ => l2_nonneg _ _
  have hd1 : (volume U).toReal ^ ((-1 : ℝ) / d) * (volume U).toReal ^ ((1 : ℝ) / d) = 1 := by
    rw [← Real.rpow_add hV, show (-1 : ℝ) / d + 1 / d = 0 by ring, Real.rpow_zero]
  have hdpos : 0 < (volume U).toReal ^ ((1 : ℝ) / d) := Real.rpow_pos_of_pos hV _
  have hdpos' : 0 < (volume U).toReal ^ ((-1 : ℝ) / d) := Real.rpow_pos_of_pos hV _
  -- from the test norm: `‖ψ‖ ≤ |U|^{1/2 + 1/d}` and `∑ ‖∂ψ‖ ≤ |U|^{1/2}`
  rw [← Finset.mul_sum] at hψ1
  have hA : (volume U).toReal ^ ((-1 : ℝ) / d) * ((volume U).toReal ^ (1 / 2 : ℝ))⁻¹ *
      l2 U ψ ≤ 1 := by
    have := mul_nonneg (inv_nonneg.2 hs.le) hsum
    nlinarith
  have hB : ((volume U).toReal ^ (1 / 2 : ℝ))⁻¹ * ∑ k, l2 U (coordinateDerivative k ψ) ≤ 1 := by
    have := mul_nonneg (mul_nonneg hdpos'.le (inv_nonneg.2 hs.le)) hl
    nlinarith
  have hA' : l2 U ψ ≤ (volume U).toReal ^ (1 / 2 : ℝ) * (volume U).toReal ^ ((1 : ℝ) / d) := by
    have h2 : (volume U).toReal ^ (1 / 2 : ℝ) * (volume U).toReal ^ ((1 : ℝ) / d) *
        ((volume U).toReal ^ ((-1 : ℝ) / d) * ((volume U).toReal ^ (1 / 2 : ℝ))⁻¹ * l2 U ψ) =
        l2 U ψ := by
      calc _ = ((volume U).toReal ^ (1 / 2 : ℝ) * ((volume U).toReal ^ (1 / 2 : ℝ))⁻¹) *
            ((volume U).toReal ^ ((-1 : ℝ) / d) * (volume U).toReal ^ ((1 : ℝ) / d)) *
              l2 U ψ := by ring
        _ = l2 U ψ := by rw [mul_inv_cancel₀ hs.ne', hd1, one_mul, one_mul]
    calc l2 U ψ = _ := h2.symm
      _ ≤ _ := mul_le_of_le_one_right (by positivity) hA
  have hB' : ∑ k, l2 U (coordinateDerivative k ψ) ≤ (volume U).toReal ^ (1 / 2 : ℝ) := by
    have h2 : ∑ k, l2 U (coordinateDerivative k ψ) = (volume U).toReal ^ (1 / 2 : ℝ) *
        (((volume U).toReal ^ (1 / 2 : ℝ))⁻¹ * ∑ k, l2 U (coordinateDerivative k ψ)) := by
      field_simp
    rw [h2]
    exact mul_le_of_le_one_right hs.le hB
  have hss : (volume U).toReal⁻¹ * (volume U).toReal ^ (1 / 2 : ℝ) =
      ((volume U).toReal ^ (1 / 2 : ℝ))⁻¹ := by
    have h := Real.rpow_add hV (1 / 2 : ℝ) (1 / 2 : ℝ)
    norm_num at h
    field_simp
    nlinarith [h]
  calc (volume U).toReal⁻¹ * |∫ x in U, dot (Φ x) (gradient ψ x)|
      ≤ (volume U).toReal⁻¹ * (K * ((volume U).toReal ^ (1 / 2 : ℝ) *
          (volume U).toReal ^ ((1 : ℝ) / d) + (volume U).toReal ^ (1 / 2 : ℝ))) := by
        refine mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left
          (add_le_add hA' hB') hK)) (inv_nonneg.2 hV.le)
    _ = ((volume U).toReal⁻¹ * (volume U).toReal ^ (1 / 2 : ℝ)) *
          (((volume U).toReal ^ ((1 : ℝ) / d) + 1) * K) := by ring
    _ = _ := by rw [hss]

/-- **The multiplier estimate on `Ĥ⁻¹(U)`.** -/
theorem hatNegativeSobolevNorm_mul_le {U V : Set (Vec d)} (hU : PDE.IsOpenBoundedConvexDomain U)
    (hUV : U ⊆ V) (hV1 : 1 ≤ (volume V).toReal) (hVt : volume V ≠ ⊤) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hχ0 : ∀ x, |χ x| ≤ M₀)
    (hχ1 : ∀ k x, |coordinateDerivative k χ x| ≤ M₁) {F : Vec d → ℝ}
    (hF : MemLp F 2 (volume.restrict U)) {N : ℝ} (hN0 : 0 ≤ N)
    (hN : negativeSobolevOneNorm 2 V F 0 ≤ ENNReal.ofReal N) :
    hatNegativeSobolevNorm U (fun x => χ x * F x) ≤
      ENNReal.ofReal (((volume U).toReal ^ (1 / 2 : ℝ))⁻¹ * ((volume V).toReal ^ (1 / 2 : ℝ) * N) *
        ((M₀ + d * M₁) * (volume U).toReal ^ ((1 : ℝ) / d) + d * M₀)) := by
  have hUt : volume U ≠ ⊤ := (volume_lt_top_of_isBoundedDomain hU.2.1).ne
  refine hatNegativeSobolevNorm_le_ofReal fun v G hv hn => ?_
  have hGi : ∀ i, MemLp (fun x => G x i) 2 (volume.restrict U) := fun i => hv.2.1.eval i
  have h01 := h01_cutoff_mul hU hv.1 hGi hv.2.2 hχ hχc hχU
  have hK : 0 ≤ (volume V).toReal ^ (1 / 2 : ℝ) * N := by positivity
  have hext := abs_setIntegral_mul_le_of_H01 hF (K := (volume V).toReal ^ (1 / 2 : ℝ) * N)
    (fun φ hφ => abs_setIntegral_mul_le_of_negativeSobolevOneNorm hUV hV1 hVt hN0 hN hφ) h01
  have hUr := ENNReal.toReal_nonneg (a := volume U)
  -- the norms of `χ v` and its gradient
  have hvm : MemLp v 2 (volume.restrict U) := hv.1
  have hcont1 : ∀ k, Continuous (coordinateDerivative k χ) := fun k =>
    continuous_coordinateDerivative (hχ.of_le (by simp)) k
  have n1 : l2 U (fun x => χ x * v x) ≤ M₀ * l2 U v :=
    l2_le_mul (hχ.continuous.aestronglyMeasurable.mul hvm.aestronglyMeasurable) hvm hM₀
      fun x => by
        show |χ x * v x| ≤ M₀ * |v x|
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hχ0 x) (abs_nonneg _)
  have n2 : ∀ k, l2 U (fun x => (χ x • G x + v x • gradient χ x) k) ≤
      M₀ * l2 U (fun x => G x k) + M₁ * l2 U v := by
    intro k
    have m1 : MemLp (fun x => χ x * G x k) 2 (volume.restrict U) :=
      MemLp.mul (r := 2) ((hχ.continuous.memLp_top_of_hasCompactSupport hχc _)) (hGi k)
    have m2 : MemLp (fun x => v x * coordinateDerivative k χ x) 2 (volume.restrict U) := by
      have := MemLp.mul (r := 2) ((hcont1 k).memLp_top_of_hasCompactSupport
        (hasCompactSupport_gradient_apply hχc k) (volume.restrict U)) hvm
      refine this.ae_eq (Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply]; ring
    have e : (fun x => (χ x • G x + v x • gradient χ x) k) =
        fun x => χ x * G x k + v x * coordinateDerivative k χ x := by
      funext x; simp [gradient, smul_eq_mul]
    rw [e]
    refine (l2_add_le m1 m2).trans (add_le_add ?_ ?_)
    · exact l2_le_mul m1.aestronglyMeasurable (hGi k) hM₀ fun x => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hχ0 x) (abs_nonneg _)
    · exact l2_le_mul m2.aestronglyMeasurable hvm hM₁ fun x => by
        rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hχ1 k x) (abs_nonneg _)
  -- `‖v‖ ≤ |U|^{1/2 + 1/d}` and `‖G_k‖ ≤ |U|^{1/2}`
  have hrms : (volume U).toReal ^ ((-1 : ℝ) / d) * scalarRms volume U v ≤ 1 := by
    have := Real.sqrt_nonneg (⨍ x in U, euclideanSq (G x) ∂volume)
    unfold h1Norm at hn
    unfold vectorRms at hn
    linarith
  have hvG : vectorRms volume U G ≤ 1 := by
    have := mul_nonneg (Real.rpow_nonneg hUr ((-1 : ℝ) / d)) (Real.sqrt_nonneg
      (⨍ x in U, (v x) ^ 2 ∂volume))
    unfold h1Norm at hn
    unfold scalarRms at hn
    linarith
  rcases eq_or_ne (volume U).toReal 0 with h0 | h0
  · rw [setAverage_eq, smul_eq_mul, measureReal_def, h0, inv_zero, zero_mul, abs_zero]
    have hs0 : (0 : ℝ) ^ (1 / 2 : ℝ) = 0 := Real.zero_rpow (by norm_num)
    rw [hs0, inv_zero, zero_mul, zero_mul]
  have hV : 0 < (volume U).toReal := lt_of_le_of_ne hUr (Ne.symm h0)
  have hs : 0 < (volume U).toReal ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hV _
  have hdpos : 0 < (volume U).toReal ^ ((1 : ℝ) / d) := Real.rpow_pos_of_pos hV _
  have hd1 : (volume U).toReal ^ ((-1 : ℝ) / d) * (volume U).toReal ^ ((1 : ℝ) / d) = 1 := by
    rw [← Real.rpow_add hV, show (-1 : ℝ) / d + 1 / d = 0 by ring, Real.rpow_zero]
  have hv' : l2 U v ≤ (volume U).toReal ^ (1 / 2 : ℝ) * (volume U).toReal ^ ((1 : ℝ) / d) := by
    rw [l2_eq_sqrt_mul_scalarRms hUt hvm]
    refine mul_le_mul_of_nonneg_left ?_ hs.le
    have : scalarRms volume U v = (volume U).toReal ^ ((1 : ℝ) / d) *
        ((volume U).toReal ^ ((-1 : ℝ) / d) * scalarRms volume U v) := by
      rw [← mul_assoc, mul_comm ((volume U).toReal ^ ((1 : ℝ) / d)), hd1, one_mul]
    rw [this]
    exact mul_le_of_le_one_right hdpos.le hrms
  have hG' : ∀ k, l2 U (fun x => G x k) ≤ (volume U).toReal ^ (1 / 2 : ℝ) := fun k =>
    (l2_apply_le_sqrt_mul_vectorRms hUt hGi k).trans (mul_le_of_le_one_right hs.le hvG)
  have hsum : l2 U (fun x => χ x * v x) + ∑ k, l2 U (fun x => (χ x • G x + v x • gradient χ x) k)
      ≤ (volume U).toReal ^ (1 / 2 : ℝ) *
        ((M₀ + d * M₁) * (volume U).toReal ^ ((1 : ℝ) / d) + d * M₀) := by
    have h2 := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => n2 k
    have h3 : ∑ k, (M₀ * l2 U (fun x => G x k) + M₁ * l2 U v) ≤
        d * (M₀ * (volume U).toReal ^ (1 / 2 : ℝ) + M₁ * ((volume U).toReal ^ (1 / 2 : ℝ) *
          (volume U).toReal ^ ((1 : ℝ) / d))) := by
      have := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) =>
        add_le_add (mul_le_mul_of_nonneg_left (hG' k) hM₀) (mul_le_mul_of_nonneg_left hv' hM₁)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      exact this
    have h4 := mul_le_mul_of_nonneg_left hv' hM₀
    nlinarith
  have e : ⨍ x in U, χ x * F x * v x ∂volume =
      (volume U).toReal⁻¹ * ∫ x in U, F x * (χ x * v x) := by
    rw [setAverage_eq, smul_eq_mul, measureReal_def]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  rw [e, abs_mul, abs_of_pos (inv_pos.2 hV)]
  have hss : (volume U).toReal⁻¹ * (volume U).toReal ^ (1 / 2 : ℝ) =
      ((volume U).toReal ^ (1 / 2 : ℝ))⁻¹ := by
    have h := Real.rpow_add hV (1 / 2 : ℝ) (1 / 2 : ℝ)
    norm_num at h
    field_simp
    nlinarith [h]
  calc (volume U).toReal⁻¹ * |∫ x in U, F x * (χ x * v x)|
      ≤ (volume U).toReal⁻¹ * (((volume V).toReal ^ (1 / 2 : ℝ) * N) *
          ((volume U).toReal ^ (1 / 2 : ℝ) *
            ((M₀ + d * M₁) * (volume U).toReal ^ ((1 : ℝ) / d) + d * M₀))) :=
        mul_le_mul_of_nonneg_left (hext.trans (mul_le_mul_of_nonneg_left hsum hK))
          (inv_nonneg.2 hV.le)
    _ = ((volume U).toReal⁻¹ * (volume U).toReal ^ (1 / 2 : ℝ)) *
          ((volume V).toReal ^ (1 / 2 : ℝ) * N) *
            ((M₀ + d * M₁) * (volume U).toReal ^ ((1 : ℝ) / d) + d * M₀) := by ring
    _ = _ := by rw [hss]

end TwoScale

end QSH
