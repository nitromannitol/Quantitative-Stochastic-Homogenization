import QuantitativeStochasticHomogenization.Ch01.Sec04.Proposition115

/-!
# Algebra of the normalized `Ĥ⁻¹(U)` norm

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
the norm (0.31) as used in the proof of Theorem 2.17: it depends on its argument only almost
everywhere in `U`, it is subadditive and symmetric on `L²(U)`, and
`‖f‖_{Ĥ̲⁻¹(U)} ≤ |U|^{1/d} ‖f‖_{L̲²(U)}`.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace QSH

variable {d : ℕ}

theorem hatNegativeSobolevNorm_congr_ae {U : Set (Vec d)} {f f' : Vec d → ℝ}
    (h : f =ᵐ[volume.restrict U] f') :
    hatNegativeSobolevNorm U f = hatNegativeSobolevNorm U f' := by
  unfold hatNegativeSobolevNorm
  refine iSup_congr fun v => ?_
  have e : ⨍ x in U, f x * v.1.1 x ∂volume = ⨍ x in U, f' x * v.1.1 x ∂volume := by
    rw [setAverage_eq, setAverage_eq]
    congr 1
    exact integral_congr_ae (h.mono fun x hx => by simp only [hx])
  rw [e]

theorem hatNegativeSobolevNorm_neg (U : Set (Vec d)) (f : Vec d → ℝ) :
    hatNegativeSobolevNorm U (fun x => -f x) = hatNegativeSobolevNorm U f := by
  unfold hatNegativeSobolevNorm
  refine iSup_congr fun v => ?_
  rw [setAverage_eq, setAverage_eq]
  simp only [neg_mul, integral_neg, smul_neg, abs_neg]

theorem hatNegativeSobolevNorm_add_le {U : Set (Vec d)} {f h : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (hh : MemLp h 2 (volume.restrict U)) :
    hatNegativeSobolevNorm U (fun x => f x + h x) ≤
      hatNegativeSobolevNorm U f + hatNegativeSobolevNorm U h := by
  refine iSup_le fun v => ?_
  have hv := v.2.1.1
  have e : ⨍ x in U, (f x + h x) * v.1.1 x ∂volume =
      (⨍ x in U, f x * v.1.1 x ∂volume) + ⨍ x in U, h x * v.1.1 x ∂volume := by
    rw [setAverage_eq, setAverage_eq, setAverage_eq, ← smul_add,
      ← integral_add (f := fun x => f x * v.1.1 x) (g := fun x => h x * v.1.1 x)
        (hf.integrable_mul hv) (hh.integrable_mul hv)]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  rw [e]
  calc ENNReal.ofReal |(⨍ x in U, f x * v.1.1 x ∂volume) + ⨍ x in U, h x * v.1.1 x ∂volume|
      ≤ ENNReal.ofReal (|⨍ x in U, f x * v.1.1 x ∂volume| + |⨍ x in U, h x * v.1.1 x ∂volume|) :=
        ENNReal.ofReal_le_ofReal (abs_add_le _ _)
    _ = ENNReal.ofReal |⨍ x in U, f x * v.1.1 x ∂volume| +
          ENNReal.ofReal |⨍ x in U, h x * v.1.1 x ∂volume| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ _ := add_le_add
        (le_iSup (fun v : {v : (Vec d → ℝ) × (Vec d → Vec d) // H1 U v.1 v.2 ∧
          h1Norm U v.1 v.2 ≤ 1} => ENNReal.ofReal |⨍ x in U, f x * v.1.1 x ∂volume|) v)
        (le_iSup (fun v : {v : (Vec d → ℝ) × (Vec d → Vec d) // H1 U v.1 v.2 ∧
          h1Norm U v.1 v.2 ≤ 1} => ENNReal.ofReal |⨍ x in U, h x * v.1.1 x ∂volume|) v)

/-- `‖f‖_{Ĥ̲⁻¹(U)} ≤ |U|^{1/d} ‖f‖_{L̲²(U)}`. -/
theorem hatNegativeSobolevNorm_le_rms {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hUt : volume U ≠ ⊤) {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict U)) :
    hatNegativeSobolevNorm U f ≤
      ENNReal.ofReal ((volume U).toReal ^ ((1 : ℝ) / d) * scalarRms volume U f) := by
  have hV : 0 < (volume U).toReal := ENNReal.toReal_pos hU0 hUt
  refine hatNegativeSobolevNorm_le_ofReal fun v G hv hn => ?_
  have h1 := abs_setAverage_mul_le (p := 2) (q := 2) hU0 hUt hf hv.1
  rw [eLpMeanNormOn_two_eq_ofReal_scalarRms hU0 hf, eLpMeanNormOn_two_eq_ofReal_scalarRms hU0 hv.1,
    ENNReal.toReal_ofReal (show 0 ≤ scalarRms volume U f from Real.sqrt_nonneg _),
    ENNReal.toReal_ofReal (show 0 ≤ scalarRms volume U v from Real.sqrt_nonneg _)] at h1
  have hrv : scalarRms volume U v ≤ (volume U).toReal ^ ((1 : ℝ) / d) := by
    have h2 : (volume U).toReal ^ ((-1 : ℝ) / d) * scalarRms volume U v ≤ 1 := by
      have := Real.sqrt_nonneg (⨍ x in U, euclideanSq (G x) ∂volume)
      unfold h1Norm at hn
      unfold vectorRms at hn
      linarith
    have h3 : (volume U).toReal ^ ((1 : ℝ) / d) * (volume U).toReal ^ ((-1 : ℝ) / d) = 1 := by
      rw [← Real.rpow_add hV]
      ring_nf
      exact Real.rpow_zero _
    calc scalarRms volume U v
        = (volume U).toReal ^ ((1 : ℝ) / d) *
            ((volume U).toReal ^ ((-1 : ℝ) / d) * scalarRms volume U v) := by
          rw [← mul_assoc, h3, one_mul]
      _ ≤ (volume U).toReal ^ ((1 : ℝ) / d) * 1 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := mul_one _
  calc |⨍ x in U, f x * v x ∂volume| ≤ scalarRms volume U f * scalarRms volume U v := h1
    _ ≤ scalarRms volume U f * (volume U).toReal ^ ((1 : ℝ) / d) :=
        mul_le_mul_of_nonneg_left hrv (Real.sqrt_nonneg _)
    _ = _ := mul_comm _ _

end QSH
