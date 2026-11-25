import QuantitativeStochasticHomogenization.AppC.ReverseHolder
import QuantitativeStochasticHomogenization.AppC.GehringLemma
import QuantitativeStochasticHomogenization.AppB.DivergenceRepresentation
import QuantitativeStochasticHomogenization.Ch03.Sec04.SpatialWeakLocalization
import QuantitativeStochasticHomogenization.Ch04.Sec04.CompactTestFluxBound
import EllipticRegularity.Meyers.RHBoundaryData

/-!
# The interior Meyers estimate

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix C, Theorem C.1: for `p ∈ (2, ∞)`, `h ∈ W^{-1,p}(B_r)` and `u ∈ H¹(B_r)` solving
`-∇·(a∇u) = h` in `B_r`, there are `δ(d, Λ) > 0` and `C(d, Λ) < ∞` with
`‖∇u‖_{L̲^{(2+δ)∧p}(B_{r/2})} ≤ C (‖∇u‖_{L̲²(B_r)} + ‖h‖_{W̲^{-1,(2+δ)∧p}(B_r)})`.

The book proves the theorem first for `h = ∇·H` with `H ∈ L^p(B_r; ℝ^d)`, where the estimate
reads `‖∇u‖_{L̲^{(2+δ)∧p}(B_{r/2})} ≤ C (‖∇u‖_{L̲²(B_r)} + ‖H‖_{L̲^{(2+δ)∧p}(B_r)})`, by
Corollary C.3 on every ball `B_ρ(z) ⊆ B_r` and Gehring's lemma (Lemma C.4) with `f = |∇u|`,
`g = |H|`; this is `theorem_C_1_divergence`. The book applies Lemma C.4 with `q = 2_* = 2d/(d+2)`;
for `d = 2` this is `q = 1`, outside the range `(1, 2)` of Lemma C.4, so the proof uses
`q = max 2_* (3/2)`, for which the reverse Hölder inequality follows by Hölder's inequality.
The general case is reduced in the book to this one by Proposition B.16, the solvability of the
Dirichlet problem for the Laplacian in `W^{1,p}`, which gives `h = ∇·H` with
`‖H‖_{L̲^s(B_r)} ≤ C ‖h‖_{W̲^{-1,s}(B_r)}`. Here the representation is that of Remark B.6 on balls
(`remark_B_6`, Riesz representation and the Poincaré inequality):
`theorem_C_1_of_divergenceRepresentation` is the reduction under the representation as a
hypothesis, `exists_divergenceRepresentation` discharges it, and `theorem_C_1` is the statement
of the book.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

theorem euclideanSq_nonneg' (x : Vec d) : 0 ≤ euclideanSq x := by
  unfold euclideanSq dot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

theorem abs_apply_le_euclideanNorm'' (v : Vec d) (i : Fin d) : |v i| ≤ euclideanNorm v := by
  rw [euclideanNorm]
  apply Real.abs_le_sqrt
  rw [euclideanSq, dot, sq]
  exact Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg _)
    (Finset.mem_univ i)

theorem memLp_euclideanNorm_of_coord {μ : Measure (Vec d)} {q : ℝ≥0∞} {G : Vec d → Vec d}
    (hG : ∀ i, MemLp (fun x => G x i) q μ) : MemLp (fun x => euclideanNorm (G x)) q μ :=
  PDE.MeyersRH.memLp_vecEuclideanNorm_of_coord hG

theorem eLpMeanNormOn_two_euclideanNorm_eq {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    {G : Vec d → Vec d} (hG : ∀ i, MemLp (fun x => G x i) 2 (volume.restrict U)) :
    PDE.eLpMeanNormOn U 2 (fun x => euclideanNorm (G x)) =
      ENNReal.ofReal (vectorRms volume U G) := by
  rw [eLpMeanNormOn_two_eq_ofReal_scalarRms hU0 (memLp_euclideanNorm_of_coord hG), scalarRms,
    vectorRms]
  simp_rw [euclideanNorm, Real.sq_sqrt (euclideanSq_nonneg' _)]

/-- The normalized `H^{-1}` norm of a divergence: `‖∇·F‖_{H̲^{-1}(U)} ≤ ‖F‖_{L̲²(U)}`. -/
theorem negativeSobolevOneNorm_two_zero_le {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    {F : Vec d → Vec d}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict U)) :
    negativeSobolevOneNorm 2 U (fun _ => 0) F ≤
      PDE.eLpMeanNormOn U 2 (fun x => euclideanNorm (F x)) := by
  set μ := PDE.normalizedVolumeOn U with hμ
  have hpos : 0 < volume U := pos_iff_ne_zero.mpr hU0
  have hq : ENNReal.ofReal ((2 : ℝ) / (2 - 1)) = 2 := by norm_num
  have hnF : MemLp (fun x => euclideanNorm (F x)) 2 (volume.restrict U) :=
    memLp_euclideanNorm_of_coord hF
  refine iSup_le fun ψ => ?_
  obtain ⟨ψ, htest, hT⟩ := ψ
  rw [hq] at hT
  have hgrad : ∀ i, Continuous fun x => coordinateDerivative i ψ x := by
    intro i
    exact (htest.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hav : distributionPairing U (fun _ => 0) F ψ =
      ∫ x, (0 * ψ x - dot (F x) (gradient ψ x)) ∂μ := by
    rw [distributionPairing, hμ, PDE.integral_normalizedVolumeOn_eq_integralAverage,
      PDE.integralAverage, setAverage_eq, smul_eq_mul, measureReal_def]
  rw [hav, ← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have hpt : ∀ x, ‖0 * ψ x - dot (F x) (gradient ψ x)‖ₑ ≤
      ∑ i, ‖euclideanNorm (F x)‖ₑ * ‖coordinateDerivative i ψ x‖ₑ := by
    intro x
    rw [zero_mul, zero_sub, enorm_neg, Real.enorm_eq_ofReal_abs]
    calc ENNReal.ofReal |dot (F x) (gradient ψ x)| ≤
        ENNReal.ofReal (∑ i, euclideanNorm (F x) * |coordinateDerivative i ψ x|) := by
          refine ENNReal.ofReal_le_ofReal ?_
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (abs_apply_le_euclideanNorm'' _ i) (abs_nonneg _)
      _ = ∑ i, ‖euclideanNorm (F x)‖ₑ * ‖coordinateDerivative i ψ x‖ₑ := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by
            have := euclideanNorm_nonneg' (F x); positivity)]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ENNReal.ofReal_mul (euclideanNorm_nonneg' _), Real.enorm_eq_ofReal_abs,
            Real.enorm_eq_ofReal_abs, abs_of_nonneg (euclideanNorm_nonneg' _)]
  have hFμ : AEStronglyMeasurable (fun x => euclideanNorm (F x)) μ :=
    (hnF.smul_measure (ENNReal.inv_ne_top.mpr hU0)).aestronglyMeasurable
  have hmF : AEMeasurable (fun x => ‖euclideanNorm (F x)‖ₑ) μ := hFμ.enorm
  have hholder : ∀ i, ∫⁻ x, ‖euclideanNorm (F x)‖ₑ * ‖coordinateDerivative i ψ x‖ₑ ∂μ ≤
      PDE.eLpMeanNormOn U 2 (fun x => euclideanNorm (F x)) *
        PDE.eLpMeanNormOn U 2 (coordinateDerivative i ψ) := by
    intro i
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hmF
      (hgrad i).aestronglyMeasurable.enorm
    have e1 : PDE.eLpMeanNormOn U 2 (fun x => euclideanNorm (F x)) =
        (∫⁻ x, ‖euclideanNorm (F x)‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
      rw [PDE.eLpMeanNormOn, ← hμ, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero
        ENNReal.ofNat_ne_top hFμ, ENNReal.toReal_ofNat]
    have e2 : PDE.eLpMeanNormOn U 2 (coordinateDerivative i ψ) =
        (∫⁻ x, ‖coordinateDerivative i ψ x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
      rw [PDE.eLpMeanNormOn, ← hμ, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero
        ENNReal.ofNat_ne_top (hgrad i).aestronglyMeasurable, ENNReal.toReal_ofNat]
    rw [e1, e2]
    exact h
  have hsumT : ∑ i, PDE.eLpMeanNormOn U 2 (coordinateDerivative i ψ) ≤ 1 := by
    let φ : PDE.WeakTestFunction U := ⟨ψ, htest.1, htest.2.1, htest.2.2⟩
    have hfin : ∀ i, PDE.eLpMeanNormOn U 2 (coordinateDerivative i ψ) ≠ ⊤ := fun i =>
      eLpMeanNormOn_ne_top hU0 (φ.grad_memVectorL2On i)
    have e : ∑ i, PDE.eLpMeanNormOn U 2 (coordinateDerivative i ψ) =
        ENNReal.ofReal (∑ i, (PDE.eLpMeanNormOn U 2 (coordinateDerivative i ψ)).toReal) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => ENNReal.toReal_nonneg)]
      exact Finset.sum_congr rfl fun i _ => (ENNReal.ofReal_toReal (hfin i)).symm
    rw [e, ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal (le_trans ?_ hT)
    unfold sobolevOneTestNorm
    have h0 : 0 ≤ (volume U).toReal ^ (-(1 : ℝ) / d) *
        (PDE.eLpMeanNormOn U 2 ψ).toReal :=
      mul_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _) ENNReal.toReal_nonneg
    linarith
  have hmeas : ∀ i ∈ Finset.univ, AEMeasurable
      (fun x => ‖euclideanNorm (F x)‖ₑ * ‖coordinateDerivative i ψ x‖ₑ) μ :=
    fun i _ => hmF.mul (hgrad i).aestronglyMeasurable.enorm
  calc ∫⁻ x, ‖0 * ψ x - dot (F x) (gradient ψ x)‖ₑ ∂μ
      ≤ ∫⁻ x, ∑ i, ‖euclideanNorm (F x)‖ₑ * ‖coordinateDerivative i ψ x‖ₑ ∂μ :=
        lintegral_mono hpt
    _ = ∑ i, ∫⁻ x, ‖euclideanNorm (F x)‖ₑ * ‖coordinateDerivative i ψ x‖ₑ ∂μ :=
        lintegral_finsetSum' _ hmeas
    _ ≤ ∑ i, PDE.eLpMeanNormOn U 2 (fun x => euclideanNorm (F x)) *
          PDE.eLpMeanNormOn U 2 (coordinateDerivative i ψ) :=
        Finset.sum_le_sum fun i _ => hholder i
    _ = PDE.eLpMeanNormOn U 2 (fun x => euclideanNorm (F x)) *
          ∑ i, PDE.eLpMeanNormOn U 2 (coordinateDerivative i ψ) := by
        rw [Finset.mul_sum]
    _ ≤ PDE.eLpMeanNormOn U 2 (fun x => euclideanNorm (F x)) * 1 := by gcongr
    _ = _ := mul_one _

/-- **Theorem C.1 for a right-hand side in divergence form.** For `d ≥ 2` there are
`δ(d, Λ) > 0` and `C(d, Λ) < ∞` such that, for `p ∈ (2, ∞)`, `r > 0`, `H ∈ L^p(B_r; ℝ^d)` and
`u ∈ H¹(B_r)` solving `-∇·(a∇u) = ∇·H` in `B_r`,
`‖∇u‖_{L̲^{(2+δ)∧p}(B_{r/2})} ≤ C (‖∇u‖_{L̲²(B_r)} + ‖H‖_{L̲^{(2+δ)∧p}(B_r)})`. -/
theorem theorem_C_1_divergence (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ δ C : ℝ, 0 < δ ∧ δ < 1 ∧ 0 ≤ C ∧ ∀ (p r : ℝ), 2 < p → 0 < r →
      ∀ (a : CoefficientField d Λ) (u : Vec d → ℝ) (g H : Vec d → Vec d),
      MemLp u 2 (volume.restrict (ball 0 r)) →
      (∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 r))) →
      HasWeakGradient (ball 0 r) u g →
      (∀ i, MemLp (fun x => H x i) (ENNReal.ofReal p) (volume.restrict (ball 0 r))) →
      HasWeakDivergence (ball 0 r) (fun x => (a x).mulVec (g x) + H x) (fun _ => 0) →
      PDE.eLpMeanNormOn (ball 0 (r / 2)) (ENNReal.ofReal (min (2 + δ) p))
          (fun x => euclideanNorm (g x)) ≤
        ENNReal.ofReal C * (PDE.eLpMeanNormOn (ball 0 r) 2 (fun x => euclideanNorm (g x)) +
          PDE.eLpMeanNormOn (ball 0 r) (ENNReal.ofReal (min (2 + δ) p))
            (fun x => euclideanNorm (H x))) := by
  obtain ⟨C₃, hC₃, h3⟩ := interiorReverseHolder hd hΛ
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set s : ℝ := 2 * d / (d + 2) with hs
  have hs2 : s < 2 := by
    rw [hs, div_lt_iff₀ (by linarith)]
    linarith
  set q₀ : ℝ := max s (3 / 2) with hq₀
  have hq01 : 1 < q₀ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hq02 : q₀ < 2 := max_lt hs2 (by norm_num)
  have hs0 : 0 < s := by rw [hs]; positivity
  obtain ⟨δ, C₄, hδ, hδ1, hC₄, hG⟩ := lemma_C_4 (d := d) hq01 hq02 (le_max_right C₃ 1)
  refine ⟨δ, C₄, hδ, hδ1, hC₄, fun p r hp hr a u g H hu hg hw hH hdiv => ?_⟩
  have hp2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal hp.le
  have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) r)) :=
    isFiniteMeasure_restrict.mpr (volume_ball_ne_top' 0 r)
  have hH2 : ∀ i, MemLp (fun x => H x i) 2 (volume.restrict (ball 0 r)) :=
    fun i => (hH i).mono_exponent hp2
  refine hG p r hp hr _ _ (memLp_euclideanNorm_of_coord hg) (memLp_euclideanNorm_of_coord hH) ?_
  intro z ρ hρ hsub
  have hres : volume.restrict (ball z ρ) ≤ volume.restrict (ball (0 : Vec d) r) :=
    Measure.restrict_mono hsub le_rfl
  have hu' := hu.mono_measure hres
  have hg' := fun i => (hg i).mono_measure hres
  have hH2' := fun i => (hH2 i).mono_measure hres
  have hw' := hasWeakGradient_mono hsub hw
  have hdiv' : HasWeakDivergence (ball z ρ) (fun x => (a x).mulVec (g x) + H x)
      (fun x => -(fun _ : Vec d => (0 : ℝ)) x) := by
    simpa using hdiv.mono' hsub
  have h := h3 z ρ hρ a u g (fun _ => 0) H hu' hg' hw' MemLp.zero hH2' hdiv'
  have hhalf : ball z (ρ / 2) ⊆ ball z ρ := by
    intro x hx
    have hx' : euclideanNorm (x - z) < ρ / 2 := hx
    change euclideanNorm (x - z) < ρ
    linarith
  have hg'' := fun i => (hg' i).mono_measure (Measure.restrict_mono hhalf le_rfl)
  rw [eLpMeanNormOn_two_euclideanNorm_eq (volume_ball_ne_zero' z (half_pos hρ)) hg'']
  have hpos : 0 < volume (ball z ρ) := pos_iff_ne_zero.mpr (volume_ball_ne_zero' z hρ)
  have : IsProbabilityMeasure (PDE.normalizedVolumeOn (ball z ρ)) :=
    PDE.isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top hpos (volume_ball_lt_top z ρ)
  have hmono : PDE.eLpMeanNormOn (ball z ρ) (ENNReal.ofReal (2 * d / (d + 2)))
      (fun x => euclideanNorm (g x)) ≤
      PDE.eLpMeanNormOn (ball z ρ) (ENNReal.ofReal q₀) (fun x => euclideanNorm (g x)) :=
    eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hneg := negativeSobolevOneNorm_two_zero_le (volume_ball_ne_zero' z hρ) hH2'
  calc ENNReal.ofReal (vectorRms volume (ball z (ρ / 2)) g)
      ≤ ENNReal.ofReal C₃ * (PDE.eLpMeanNormOn (ball z ρ) (ENNReal.ofReal (2 * d / (d + 2)))
          (fun x => euclideanNorm (g x)) + negativeSobolevOneNorm 2 (ball z ρ) (fun _ => 0) H) := h
    _ ≤ ENNReal.ofReal (max C₃ 1) * (PDE.eLpMeanNormOn (ball z ρ) (ENNReal.ofReal q₀)
          (fun x => euclideanNorm (g x)) +
          PDE.eLpMeanNormOn (ball z ρ) 2 (fun x => euclideanNorm (H x))) := by
        gcongr
        exact le_max_left _ _

theorem memLp_coordinateDerivative_of_isSpatialTest {U : Set (Vec d)} {ψ : Vec d → ℝ}
    (hψ : IsSpatialTest U ψ) (i : Fin d) (q : ℝ≥0∞) (μ : Measure (Vec d))
    [IsFiniteMeasureOnCompacts μ] : MemLp (coordinateDerivative i ψ) q μ :=
  ((hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
    (hψ.2.1.fderiv_apply (𝕜 := ℝ) (unitVector i))

theorem sobolevOneTestNorm_mono {U : Set (Vec d)} (hU0 : volume U ≠ 0) (hUt : volume U ≠ ⊤)
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest U ψ) {q₁ q₂ : ℝ≥0∞} (hq : q₁ ≤ q₂) :
    sobolevOneTestNorm q₁ U ψ ≤ sobolevOneTestNorm q₂ U ψ := by
  have hpos : 0 < volume U := pos_iff_ne_zero.mpr hU0
  have : IsProbabilityMeasure (PDE.normalizedVolumeOn U) :=
    PDE.isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top hpos hUt.lt_top
  have hfin : ∀ h : Vec d → ℝ, MemLp h q₂ (volume.restrict U) →
      PDE.eLpMeanNormOn U q₂ h ≠ ⊤ := fun h hh => eLpMeanNormOn_ne_top hU0 hh
  have hmono : ∀ h : Vec d → ℝ, MemLp h q₂ (volume.restrict U) →
      (PDE.eLpMeanNormOn U q₁ h).toReal ≤ (PDE.eLpMeanNormOn U q₂ h).toReal :=
    fun h hh => ENNReal.toReal_mono (hfin h hh) (eLpNorm_le_eLpNorm_of_exponent_le hq)
  unfold sobolevOneTestNorm
  have h0 := hmono ψ (hψ.1.continuous.memLp_of_hasCompactSupport hψ.2.1)
  have hi : ∀ i : Fin d, (PDE.eLpMeanNormOn U q₁ (coordinateDerivative i ψ)).toReal ≤
      (PDE.eLpMeanNormOn U q₂ (coordinateDerivative i ψ)).toReal :=
    fun i => hmono _ (memLp_coordinateDerivative_of_isSpatialTest hψ i q₂ _)
  exact add_le_add (mul_le_mul_of_nonneg_left h0 (Real.rpow_nonneg ENNReal.toReal_nonneg _))
    (Finset.sum_le_sum fun i _ => hi i)

/-- `‖h‖_{W̲^{-1,s}(U)} ≤ ‖h‖_{W̲^{-1,p}(U)}` for `1 < s ≤ p`. -/
theorem negativeSobolevOneNorm_mono_exponent {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hUt : volume U ≠ ⊤) {s p : ℝ} (hs : 1 < s) (hsp : s ≤ p) (f : Vec d → ℝ)
    (F : Vec d → Vec d) :
    negativeSobolevOneNorm s U f F ≤ negativeSobolevOneNorm p U f F := by
  refine iSup_le fun ψ => ?_
  obtain ⟨ψ, htest, hT⟩ := ψ
  have hexp : ENNReal.ofReal (p / (p - 1)) ≤ ENNReal.ofReal (s / (s - 1)) := by
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hT' := (sobolevOneTestNorm_mono hU0 hUt htest hexp).trans hT
  exact le_iSup (fun ψ : {ψ : Vec d → ℝ // IsSpatialTest U ψ ∧
      sobolevOneTestNorm (ENNReal.ofReal (p / (p - 1))) U ψ ≤ 1} =>
    ENNReal.ofReal |distributionPairing U f F ψ.1|) ⟨ψ, htest, hT'⟩

theorem integrableOn_dot_gradient {U : Set (Vec d)} (hUt : volume U ≠ ⊤) {s : ℝ≥0∞}
    (hs : 1 ≤ s) {X : Vec d → Vec d} (hX : ∀ i, MemLp (fun x => X x i) s (volume.restrict U))
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest U ψ) :
    IntegrableOn (fun x => dot (X x) (gradient ψ x)) U := by
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUt
  unfold dot
  refine integrable_finsetSum _ fun i _ => ?_
  have hc : Continuous fun x => coordinateDerivative i ψ x :=
    (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support (hψ.2.1.fderiv_apply (𝕜 := ℝ)
    (unitVector i))
  have h := ((hX i).integrable hs).mul_bdd (c := M) hc.aestronglyMeasurable
    (Eventually.of_forall hM)
  exact h

/-- The weak equation is unchanged when `f + ∇·F` is replaced by a representation `∇·H` with the
same pairings: `∇·(A + F) = -f` gives `∇·(A + H) = 0`. -/
theorem hasWeakDivergence_of_representation {U : Set (Vec d)} (hUt : volume U ≠ ⊤)
    {A F H : Vec d → Vec d} {f : Vec d → ℝ} {s : ℝ≥0∞} (hs : 1 ≤ s)
    (hA : ∀ i, MemLp (fun x => A x i) 2 (volume.restrict U))
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict U)) (hf : MemLp f 2 (volume.restrict U))
    (hH : ∀ i, MemLp (fun x => H x i) s (volume.restrict U))
    (hdiv : HasWeakDivergence U (fun x => A x + F x) (fun x => -f x))
    (hrep : ∀ ψ, IsSpatialTest U ψ → ∫ x in U, (f x * ψ x - dot (F x) (gradient ψ x)) =
      -∫ x in U, dot (H x) (gradient ψ x)) :
    HasWeakDivergence U (fun x => A x + H x) (fun _ => 0) := by
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUt
  refine ⟨fun i => ?_, locallyIntegrableOn_zero, fun ψ hψ => ?_⟩
  · have h : IntegrableOn (fun x => (A x + H x) i) U :=
      ((hA i).integrable one_le_two).add ((hH i).integrable hs)
    exact h.locallyIntegrableOn
  · have iA := integrableOn_dot_gradient hUt one_le_two hA hψ
    have iF := integrableOn_dot_gradient hUt one_le_two hF hψ
    have iH := integrableOn_dot_gradient hUt hs hH hψ
    have ifψ : IntegrableOn (fun x => f x * ψ x) U :=
      hf.integrable_mul (q := 2) (hψ.1.continuous.memLp_of_hasCompactSupport hψ.2.1)
    have hadd : ∀ X Y : Vec d → Vec d, ∀ x, dot (X x + Y x) (gradient ψ x) =
        dot (X x) (gradient ψ x) + dot (Y x) (gradient ψ x) := by
      intro X Y x
      simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    have h1 := hdiv.2.2 ψ hψ
    have h2 := hrep ψ hψ
    simp_rw [hadd] at h1 ⊢
    rw [integral_add iA iF] at h1
    rw [integral_add iA iH]
    rw [integral_sub ifψ iF] at h2
    have h3 : ∫ x in U, -f x * ψ x = -∫ x in U, f x * ψ x := by
      rw [← integral_neg]
      simp only [neg_mul]
    rw [h3] at h1
    simp only [zero_mul, integral_zero, neg_zero]
    linarith

/-- The representation of Remark B.6 and Proposition B.16 on centered balls, for exponents
`s ∈ [2, 3]` and a constant `C`: every `h = f + ∇·F ∈ W^{-1,s}(B_r)` with `f ∈ L²(B_r)` and
`F ∈ L²(B_r; ℝ^d)` is `∇·H` for some `H ∈ L^s(B_r; ℝ^d)` with the same pairings and
`‖H‖_{L̲^s(B_r)} ≤ C ‖h‖_{W̲^{-1,s}(B_r)}`. -/
def DivergenceRepresentation (d : ℕ) (C : ℝ) : Prop :=
  ∀ (s r : ℝ), 2 ≤ s → s ≤ 3 → 0 < r → ∀ (f : Vec d → ℝ) (F : Vec d → Vec d),
    MemLp f 2 (volume.restrict (ball 0 r)) →
    (∀ i, MemLp (fun x => F x i) 2 (volume.restrict (ball 0 r))) →
    negativeSobolevOneNorm s (ball 0 r) f F ≠ ⊤ →
    ∃ H : Vec d → Vec d,
      (∀ i, MemLp (fun x => H x i) (ENNReal.ofReal s) (volume.restrict (ball 0 r))) ∧
      (∀ ψ, IsSpatialTest (ball 0 r) ψ →
        ∫ x in ball 0 r, (f x * ψ x - dot (F x) (gradient ψ x)) =
          -∫ x in ball 0 r, dot (H x) (gradient ψ x)) ∧
      PDE.eLpMeanNormOn (ball 0 r) (ENNReal.ofReal s) (fun x => euclideanNorm (H x)) ≤
        ENNReal.ofReal C * negativeSobolevOneNorm s (ball 0 r) f F

/-- Theorem C.1 given the representation of Remark B.6 and Proposition B.16
(`DivergenceRepresentation`). For `d ≥ 2` there are `δ(d, Λ) > 0` and `C < ∞` (depending on `d`,
`Λ` and the representation constant) such that, for `p ∈ (2, ∞)`, `r > 0`,
`h = f + ∇·F ∈ W^{-1,p}(B_r)` and `u ∈ H¹(B_r)` solving `-∇·(a∇u) = h` in `B_r`,
`‖∇u‖_{L̲^{(2+δ)∧p}(B_{r/2})} ≤ C (‖∇u‖_{L̲²(B_r)} + ‖h‖_{W̲^{-1,(2+δ)∧p}(B_r)})`. -/
theorem theorem_C_1_of_divergenceRepresentation (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ) {CB : ℝ}
    (hB : DivergenceRepresentation d CB) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ (p r : ℝ), 2 < p → 0 < r → ∀ (a : CoefficientField d Λ)
      (u : Vec d → ℝ) (g : Vec d → Vec d) (f : Vec d → ℝ) (F : Vec d → Vec d),
      MemLp u 2 (volume.restrict (ball 0 r)) →
      (∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 r))) →
      HasWeakGradient (ball 0 r) u g →
      MemLp f 2 (volume.restrict (ball 0 r)) →
      (∀ i, MemLp (fun x => F x i) 2 (volume.restrict (ball 0 r))) →
      negativeSobolevOneNorm p (ball 0 r) f F ≠ ⊤ →
      HasWeakDivergence (ball 0 r) (fun x => (a x).mulVec (g x) + F x) (fun x => -f x) →
      PDE.eLpMeanNormOn (ball 0 (r / 2)) (ENNReal.ofReal (min (2 + δ) p))
          (fun x => euclideanNorm (g x)) ≤
        ENNReal.ofReal C * (PDE.eLpMeanNormOn (ball 0 r) 2 (fun x => euclideanNorm (g x)) +
          negativeSobolevOneNorm (min (2 + δ) p) (ball 0 r) f F) := by
  obtain ⟨δ, C₁, hδ, hδ1, hC₁, h1⟩ := theorem_C_1_divergence hd hΛ
  refine ⟨δ, C₁ * max CB 1, hδ, by positivity, ?_⟩
  intro p r hp hr a u g f F hu hg hw hf hF hfin hdiv
  set s := min (2 + δ) p with hsdef
  have hs2 : 2 < s := lt_min (by linarith) hp
  have hs3 : s ≤ 3 := (min_le_left _ _).trans (by linarith)
  have hsp : s ≤ p := min_le_right _ _
  have hU0 := volume_ball_ne_zero' (0 : Vec d) hr
  have hUt := volume_ball_ne_top' (0 : Vec d) r
  have hfin_s : negativeSobolevOneNorm s (ball 0 r) f F ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (negativeSobolevOneNorm_mono_exponent hU0 hUt (by linarith) hsp f F)
  obtain ⟨H, hHmem, hHpair, hHnorm⟩ := hB s r hs2.le hs3 hr f F hf hF hfin_s
  have hA : ∀ i, MemLp (fun x => (a x).mulVec (g x) i) 2 (volume.restrict (ball 0 r)) := by
    have hEll := isEllipticFieldOn_ellipticFieldOf hΛ a (measurableSet_ball (0 : Vec d) r)
    have h := PDE.memVectorL2On_matVecMul_of_isEllipticFieldOn hEll (f := g) hg
    intro i
    refine (h i).ae_eq ?_
    filter_upwards [ae_restrict_of_ae (ellipticFieldOf_ae_eq hΛ a)] with x hx
    change ((ellipticFieldOf a x).mulVec (g x)) i = _
    rw [hx]
  have hs1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal s := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hdivH := hasWeakDivergence_of_representation hUt hs1 hA hF hf hHmem hdiv hHpair
  have hmain := h1 s r hs2 hr a u g H hu hg hw hHmem hdivH
  rw [show min (2 + δ) s = s from min_eq_right (min_le_left _ _)] at hmain
  calc PDE.eLpMeanNormOn (ball 0 (r / 2)) (ENNReal.ofReal s) (fun x => euclideanNorm (g x))
      ≤ ENNReal.ofReal C₁ * (PDE.eLpMeanNormOn (ball 0 r) 2 (fun x => euclideanNorm (g x)) +
          PDE.eLpMeanNormOn (ball 0 r) (ENNReal.ofReal s) (fun x => euclideanNorm (H x))) :=
        hmain
    _ ≤ ENNReal.ofReal C₁ * (PDE.eLpMeanNormOn (ball 0 r) 2 (fun x => euclideanNorm (g x)) +
          ENNReal.ofReal (max CB 1) * negativeSobolevOneNorm s (ball 0 r) f F) := by
        gcongr
        exact hHnorm.trans (by gcongr; exact le_max_left _ _)
    _ ≤ ENNReal.ofReal C₁ * (ENNReal.ofReal (max CB 1) *
          PDE.eLpMeanNormOn (ball 0 r) 2 (fun x => euclideanNorm (g x)) +
          ENNReal.ofReal (max CB 1) * negativeSobolevOneNorm s (ball 0 r) f F) := by
        gcongr
        calc PDE.eLpMeanNormOn (ball 0 r) 2 (fun x => euclideanNorm (g x)) =
            1 * PDE.eLpMeanNormOn (ball 0 r) 2 (fun x => euclideanNorm (g x)) := (one_mul _).symm
          _ ≤ _ := by
            gcongr
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
    _ = ENNReal.ofReal (C₁ * max CB 1) *
          (PDE.eLpMeanNormOn (ball 0 r) 2 (fun x => euclideanNorm (g x)) +
            negativeSobolevOneNorm s (ball 0 r) f F) := by
        rw [← mul_add, ← mul_assoc, ← ENNReal.ofReal_mul hC₁]

/-- The representation `DivergenceRepresentation` holds for `d ≥ 1`, by Remark B.6 on balls
(`remark_B_6`). -/
theorem exists_divergenceRepresentation (hd : 0 < d) : ∃ C : ℝ, DivergenceRepresentation d C := by
  obtain ⟨C, -, hC⟩ := remark_B_6 hd
  refine ⟨C, fun s r hs2 _ hr f F hf hF hfin => ?_⟩
  have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) r)) :=
    isFiniteMeasure_restrict.mpr (volume_ball_ne_top' 0 r)
  obtain ⟨H, hH, hrep, -, hnorm⟩ := hC s (by linarith) 0 r hr f F (hf.integrable one_le_two)
    (fun i => (hF i).integrable one_le_two) hfin
  exact ⟨H, hH, hrep, hnorm⟩

/-- **Theorem C.1 (interior Meyers estimate).** For `d ≥ 2` there are `δ(d, Λ) > 0` and
`C(d, Λ) < ∞` such that, for `p ∈ (2, ∞)`, `r > 0`, `h = f + ∇·F ∈ W^{-1,p}(B_r)` with
`f ∈ L²(B_r)`, `F ∈ L²(B_r; ℝ^d)`, and `u ∈ H¹(B_r)` solving `-∇·(a∇u) = h` in `B_r`,
`‖∇u‖_{L̲^{(2+δ)∧p}(B_{r/2})} ≤ C (‖∇u‖_{L̲²(B_r)} + ‖h‖_{W̲^{-1,(2+δ)∧p}(B_r)})`. -/
theorem theorem_C_1 (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ (p r : ℝ), 2 < p → 0 < r → ∀ (a : CoefficientField d Λ)
      (u : Vec d → ℝ) (g : Vec d → Vec d) (f : Vec d → ℝ) (F : Vec d → Vec d),
      MemLp u 2 (volume.restrict (ball 0 r)) →
      (∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 r))) →
      HasWeakGradient (ball 0 r) u g →
      MemLp f 2 (volume.restrict (ball 0 r)) →
      (∀ i, MemLp (fun x => F x i) 2 (volume.restrict (ball 0 r))) →
      negativeSobolevOneNorm p (ball 0 r) f F ≠ ⊤ →
      HasWeakDivergence (ball 0 r) (fun x => (a x).mulVec (g x) + F x) (fun x => -f x) →
      PDE.eLpMeanNormOn (ball 0 (r / 2)) (ENNReal.ofReal (min (2 + δ) p))
          (fun x => euclideanNorm (g x)) ≤
        ENNReal.ofReal C * (PDE.eLpMeanNormOn (ball 0 r) 2 (fun x => euclideanNorm (g x)) +
          negativeSobolevOneNorm (min (2 + δ) p) (ball 0 r) f F) := by
  obtain ⟨CB, hB⟩ := exists_divergenceRepresentation (d := d) (by omega)
  exact theorem_C_1_of_divergenceRepresentation hd hΛ hB

end QSH
