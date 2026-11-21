import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicExpansionBall
import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicOrthogonality
import PDEFoundation.PDE.HarmonicPointwiseProof

/-!
# Proof of the harmonic expansion on balls

A function of `H¹(B_b)` that is weakly harmonic has a smooth harmonic representative `v`
(Weyl's lemma), with `|∇v(0)| ≤ C b⁻¹ ‖u‖_{L̲²(B_b)}`. For `t < r < b` the first-order Taylor
remainder satisfies `⨍_{B_t} (v - v(0) - Dv(0) y)² ≤ (t/r)⁴ ⨍_{B_r} v² ≤ (t/r)⁴ (b/r)^d ⨍_{B_b} v²`,
and `r → b` gives the constant `(t/b)⁴`.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ}

theorem ball_zero_eq_pdeEuclideanBall {b : ℝ} (hb : 0 < b) :
    ball (0 : Vec d) b = PDE.euclideanBall 0 b := by
  ext x
  rw [PDE.mem_euclideanBall_zero_iff]
  change euclideanNorm (x - 0) < b ↔ _
  rw [sub_zero, euclideanNorm, Real.sqrt_lt' hb]
  rfl

/-- The `H¹` function of the weak data. -/
def toH1Function {b : ℝ} (hb : 0 < b) {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict (ball 0 b)))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 b)))
    (hw : HasWeakGradient (ball 0 b) u g) : PDE.H1Function (PDE.euclideanBall (0 : Vec d) b) where
  toFun := u
  grad := g
  memL2 := by
    change MemLp u 2 (volume.restrict (PDE.euclideanBall (0 : Vec d) b))
    rw [← ball_zero_eq_pdeEuclideanBall hb]
    exact hu
  gradMemL2 := fun i => by
    change MemLp (fun x => g x i) 2 (volume.restrict (PDE.euclideanBall (0 : Vec d) b))
    rw [← ball_zero_eq_pdeEuclideanBall hb]
    exact hg i
  hasWeakGradient := fun i φ h1 h2 h3 => by
    rw [← ball_zero_eq_pdeEuclideanBall hb] at h3 ⊢
    exact (hw i).2.2 φ ⟨h1, h2, h3⟩

theorem isWeakDivergenceFormSolutionOn_toH1Function {b : ℝ} (hb : 0 < b) {u : Vec d → ℝ}
    {g : Vec d → Vec d} (hu : MemLp u 2 (volume.restrict (ball 0 b)))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 b)))
    (hw : HasWeakGradient (ball 0 b) u g)
    (hdiv : HasWeakDivergence (ball 0 b) (fun x => (1 : Mat d).mulVec (g x)) (fun _ => 0)) :
    PDE.IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat d)) (PDE.euclideanBall 0 b)
      (toH1Function hb hu hg hw) 0 0 := by
  intro φ
  have hdata : PDE.DivergenceFormL2DataOn (fun _ => (1 : Mat d)) (PDE.euclideanBall 0 b)
      (toH1Function hb hu hg hw) 0 0 := by
    refine ⟨fun i => ?_, ?_, fun i => ?_⟩
    · have h := (toH1Function hb hu hg hw).gradMemL2 i
      refine h.ae_eq (Eventually.of_forall fun x => ?_)
      simp [PDE.matVecMul, Matrix.one_apply, toH1Function]
    · exact MemLp.zero
    · exact MemLp.zero
  refine ⟨hdata.testable φ, ?_⟩
  have htest : IsSpatialTest (ball 0 b) φ.toFun :=
    ⟨φ.contDiff, φ.hasCompactSupport, by rw [ball_zero_eq_pdeEuclideanBall hb]; exact φ.tsupport_subset⟩
  have h := hdiv.2.2 φ.toFun htest
  rw [ball_zero_eq_pdeEuclideanBall hb] at h
  simp only [zero_mul, integral_zero, neg_zero] at h
  simp only [Pi.zero_apply, zero_mul, integral_zero]
  have e : ∫ x in PDE.euclideanBall (0 : Vec d) b,
      PDE.vecDot (PDE.matVecMul ((fun _ => (1 : Mat d)) x) ((toH1Function hb hu hg hw).grad x))
        (φ.grad x) =
      ∫ x in PDE.euclideanBall (0 : Vec d) b, dot ((1 : Mat d).mulVec (g x)) (gradient φ.toFun x) :=
    rfl
  have h' : ∫ x in PDE.euclideanBall (0 : Vec d) b,
      dot ((1 : Mat d).mulVec (g x)) (gradient φ.toFun x) = 0 := by simpa using h
  rw [e, h']
  simp [PDE.vecDot]

theorem scalarRms_ball_eq_sqrt_integralAverage {s : ℝ} (hs : 0 < s) (f : Vec d → ℝ) :
    scalarRms volume (ball 0 s) f =
      Real.sqrt (PDE.integralAverage (PDE.euclideanBall (0 : Vec d) s) (fun x => f x ^ 2)) := by
  unfold scalarRms PDE.integralAverage
  rw [ball_zero_eq_pdeEuclideanBall hs, setAverage_eq, smul_eq_mul, measureReal_def]

/-- The variance is at most the second moment. -/
theorem integralAverage_sq_sub_le {U : Set (Vec d)} (hU : volume U ≠ ⊤) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict U)) :
    PDE.integralAverage U (fun x => (u x - PDE.integralAverage U u) ^ 2) ≤
      PDE.integralAverage U (fun x => u x ^ 2) := by
  have hfin : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.2 hU
  set V := (volume U).toReal with hV
  set m := PDE.integralAverage U u with hm
  have hu1 : Integrable u (volume.restrict U) := hu.integrable one_le_two
  have hu2 : Integrable (fun x => u x ^ 2) (volume.restrict U) := hu.integrable_sq
  have hexp : ∫ x in U, (u x - m) ^ 2 = (∫ x in U, u x ^ 2) - 2 * m * (∫ x in U, u x) + m ^ 2 * V := by
    have e : (fun x => (u x - m) ^ 2) = fun x => (u x ^ 2 - 2 * m * u x) + m ^ 2 := by
      funext x
      ring
    have i1 : Integrable (fun x => u x ^ 2 - 2 * m * u x) (volume.restrict U) :=
      hu2.sub (hu1.const_mul _)
    have i2 : Integrable (fun x => 2 * m * u x) (volume.restrict U) := hu1.const_mul _
    rw [e, integral_add i1 (integrable_const _), integral_sub hu2 i2, integral_const_mul,
      setIntegral_const, smul_eq_mul, measureReal_def]
    ring
  unfold PDE.integralAverage
  rw [← hV, hexp]
  by_cases hV0 : V = 0
  · simp [hV0]
  · have hmu : ∫ x in U, u x = V * m := by
      rw [hm]
      unfold PDE.integralAverage
      rw [← hV, ← mul_assoc, mul_inv_cancel₀ hV0, one_mul]
    rw [hmu]
    set I := ∫ x in U, u x ^ 2
    calc V⁻¹ * (I - 2 * m * (V * m) + m ^ 2 * V) = V⁻¹ * I - (V⁻¹ * V) * m ^ 2 := by ring
      _ = V⁻¹ * I - m ^ 2 := by rw [inv_mul_cancel₀ hV0, one_mul]
      _ ≤ V⁻¹ * I := by nlinarith [sq_nonneg m]

/-- **The harmonic expansion on balls.** -/
theorem harmonicExpansionBall : harmonicExpansionBallStatement := by
  intro d hd2
  have hd : 0 < d := by omega
  have : NeZero d := ⟨hd.ne'⟩
  refine ⟨PDE.harmonicPointwiseConst d, (PDE.harmonicPointwiseConst_pos hd).le,
    fun b hb u hu => ?_⟩
  obtain ⟨huL2, gu, hgL2, hgrad, hdiv⟩ := hu
  have hsol := isWeakDivergenceFormSolutionOn_toH1Function hb huL2 hgL2 hgrad hdiv
  obtain ⟨v, hvs, hvh, hvae, -⟩ :=
    PDE.exists_harmonicWeylRepresentative hd hb (toH1Function hb huL2 hgL2 hgrad) hsol
  obtain ⟨-, hbound⟩ :=
    PDE.harmonicPointwise_of_representative hd hb (toH1Function hb huL2 hgL2 hgrad) hvs hvh hvae
  have hvae' : ∀ᵐ x ∂(volume.restrict (PDE.euclideanBall (0 : Vec d) b)), v x = u x := hvae
  have hball := ball_zero_eq_pdeEuclideanBall (d := d) hb
  have huL2' : MemLp u 2 (volume.restrict (PDE.euclideanBall (0 : Vec d) b)) := by
    rw [← hball]; exact huL2
  have hvL2 : MemLp v 2 (volume.restrict (PDE.euclideanBall (0 : Vec d) b)) :=
    huL2'.ae_eq (by filter_upwards [hvae'] with x hx; exact hx.symm)
  have hvsq : IntegrableOn (fun x => v x ^ 2) (PDE.euclideanBall (0 : Vec d) b) := hvL2.integrable_sq
  have hω : 0 < (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal :=
    PDE.volume_euclideanBall_toReal_pos 0 one_pos
  have hsub : ∀ s : ℝ, 0 ≤ s → s ≤ b → PDE.euclideanBall (0 : Vec d) s ⊆ PDE.euclideanBall 0 b := by
    intro s hs0 hsb x hx
    rw [PDE.mem_euclideanBall_zero_iff] at hx ⊢
    exact hx.trans_le (pow_le_pow_left₀ hs0 hsb 2)
  have havgb : PDE.integralAverage (PDE.euclideanBall (0 : Vec d) b) (fun x => v x ^ 2) =
      PDE.integralAverage (PDE.euclideanBall (0 : Vec d) b) (fun x => u x ^ 2) := by
    unfold PDE.integralAverage
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hvae'] with x hx
    rw [hx]
  set L := fderiv ℝ v 0 with hL
  refine ⟨v 0, fun i => L (PDE.basisVec i), fun t ht htb => ?_, ?_⟩
  · rw [scalarRms_ball_eq_sqrt_integralAverage ht, scalarRms_ball_eq_sqrt_integralAverage hb]
    have hdot : ∀ y : Vec d, dot (fun i => L (PDE.basisVec i)) y = L y := by
      intro y
      rw [clm_apply_eq_sum L y]
      unfold dot
      exact Finset.sum_congr rfl fun i _ => by ring
    have havgt : PDE.integralAverage (PDE.euclideanBall (0 : Vec d) t)
        (fun x => (u x - (v 0 + dot (fun i => L (PDE.basisVec i)) x)) ^ 2) =
        PDE.integralAverage (PDE.euclideanBall (0 : Vec d) t)
          (fun x => (v x - (v 0 + fderiv ℝ v 0 x)) ^ 2) := by
      unfold PDE.integralAverage
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (hsub t ht.le htb.le) hvae'] with x hx
      rw [hx, hdot]
    rw [havgt, ← havgb]
    set A := PDE.integralAverage (PDE.euclideanBall (0 : Vec d) b) (fun x => v x ^ 2) with hA
    have hA0 : 0 ≤ A := by
      rw [hA]; unfold PDE.integralAverage
      exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
        (setIntegral_nonneg (PDE.isOpen_euclideanBall _ _).measurableSet fun x _ => sq_nonneg _)
    have hkey : ∀ r ∈ Ioo t b, PDE.integralAverage (PDE.euclideanBall (0 : Vec d) t)
        (fun x => (v x - (v 0 + fderiv ℝ v 0 x)) ^ 2) ≤ (t / r) ^ 4 * (b / r) ^ d * A := by
      intro r hr
      have hr0 : 0 < r := ht.trans hr.1
      have h1 := integralAverage_sq_taylorRemainder_le hd hvs hvh ht hr.1 hr.2
      have h2 : PDE.integralAverage (PDE.euclideanBall (0 : Vec d) r) (fun x => v x ^ 2) ≤
          (b / r) ^ d * A := by
        rw [hA]
        unfold PDE.integralAverage
        rw [PDE.volume_euclideanBall_toReal_eq_unit_mul_of_pos _ hr0,
          PDE.volume_euclideanBall_toReal_eq_unit_mul_of_pos _ hb]
        have hint : ∫ x in PDE.euclideanBall (0 : Vec d) r, v x ^ 2 ≤
            ∫ x in PDE.euclideanBall (0 : Vec d) b, v x ^ 2 :=
          setIntegral_mono_set hvsq (ae_of_all _ fun x => sq_nonneg _)
            (ae_of_all _ (hsub r hr0.le hr.2.le))
        have hI0 : 0 ≤ ∫ x in PDE.euclideanBall (0 : Vec d) b, v x ^ 2 :=
          setIntegral_nonneg (PDE.isOpen_euclideanBall _ _).measurableSet fun x _ => sq_nonneg _
        calc (r ^ d * (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal)⁻¹ *
              ∫ x in PDE.euclideanBall (0 : Vec d) r, v x ^ 2
            ≤ (r ^ d * (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal)⁻¹ *
              ∫ x in PDE.euclideanBall (0 : Vec d) b, v x ^ 2 :=
              mul_le_mul_of_nonneg_left hint (inv_nonneg.2 (by positivity))
          _ = (b / r) ^ d * ((b ^ d * (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal)⁻¹ *
              ∫ x in PDE.euclideanBall (0 : Vec d) b, v x ^ 2) := by
              rw [div_pow]
              field_simp
      calc _ ≤ (t / r) ^ 4 * PDE.integralAverage (PDE.euclideanBall (0 : Vec d) r)
            (fun x => v x ^ 2) := h1
        _ ≤ (t / r) ^ 4 * ((b / r) ^ d * A) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (t / r) ^ 4 * (b / r) ^ d * A := by ring
    have hlim : Tendsto (fun r : ℝ => (t / r) ^ 4 * (b / r) ^ d * A) (𝓝[<] b)
        (𝓝 ((t / b) ^ 4 * (b / b) ^ d * A)) := by
      refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      exact (((tendsto_const_nhds.div tendsto_id hb.ne').pow 4).mul
        ((tendsto_const_nhds.div tendsto_id hb.ne').pow d)).mul_const A
    have hle := ge_of_tendsto hlim
      (Filter.mem_of_superset (Ioo_mem_nhdsLT htb) fun r hr => hkey r hr)
    rw [div_self hb.ne', one_pow, mul_one] at hle
    have h4 : (t / b) ^ 4 = ((t / b) ^ 2) ^ 2 := by ring
    calc Real.sqrt (PDE.integralAverage (PDE.euclideanBall (0 : Vec d) t)
          (fun x => (v x - (v 0 + fderiv ℝ v 0 x)) ^ 2))
        ≤ Real.sqrt ((t / b) ^ 4 * A) := Real.sqrt_le_sqrt hle
      _ = (t / b) ^ 2 * Real.sqrt A := by
          rw [Real.sqrt_mul (by positivity), h4, Real.sqrt_sq (by positivity)]
  · have hb1 := hbound 1 le_rfl
    have hsum : ∑ ι : Fin 1 → Fin d, (iteratedFDeriv ℝ 1 v 0 (fun k => Pi.single (ι k) 1)) ^ 2 =
        ∑ i, (L (PDE.basisVec i)) ^ 2 := by
      refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin d)) _ _ fun ι => ?_
      rw [iteratedFDeriv_one_apply]
      rfl
    rw [hsum] at hb1
    have hvar := integralAverage_sq_sub_le (PDE.volume_euclideanBall_ne_top 0 hb.le) huL2'
    have hnorm : euclideanNorm (fun i => L (PDE.basisVec i)) =
        Real.sqrt (∑ i, (L (PDE.basisVec i)) ^ 2) := by
      unfold euclideanNorm euclideanSq dot
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hnorm, scalarRms_ball_eq_sqrt_integralAverage hb]
    refine hb1.trans ?_
    simp only [pow_one, Nat.cast_one, mul_one]
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_)
      (div_nonneg (PDE.harmonicPointwiseConst_pos hd).le hb.le)
    exact hvar

end QSH
