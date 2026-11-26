import QuantitativeStochasticHomogenization.Ch01.Sec05.Theorem117

/-!
# The bound (1.57) of `E'(ε)`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.5, (1.57): there is `C(d, Λ)` such that, for `ε ∈ (0, 1]`, `m = m(ε)` and every choice
of the finite-volume correctors on `□_m`, `E'(ε) ≤ C (3^{-2m} + E(m))`, hence `≤ C (ε² + E(m))`
since `3^{-m} ≤ ε` (`twoScaleDeviation_le`). As in the book, this is Proposition 1.10 and
Lemma 1.13 rescaled by (0.30): the normalized `L²` and `H⁻¹` norms scale as
`‖ε φ(·/ε)‖_{L̲²(ε□_m)} = ε ‖φ‖_{L̲²(□_m)}` (`scalarRms_rescaled`) and
`‖f(·/ε)‖_{H̲⁻¹(ε□_m)} ≤ ε ‖f‖_{H̲⁻¹(□_m)}` (`negativeSobolevOneNorm_comp_inv_smul_le`).
Proposition 1.10 is stated for slopes in the open unit ball, so it is applied to the minimizer
`(φ_k/2, ∇φ_k/2)` for the slope `e_k/2` (`IsDirichletMinimizer.const_smul`).
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal Pointwise

noncomputable section

namespace QSH

namespace TwoScale

variable {d : ℕ} {Λ : ℝ}

/-- `|c W| = c^d |W|` for `c > 0`. -/
theorem measureReal_smul_eq {c : ℝ} (hc : 0 < c) (W : Set (Vec d)) :
    volume.real (c • W) = c ^ d * volume.real W := by
  rw [measureReal_def, measureReal_def, Measure.addHaar_smul, Module.finrank_fin_fun,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), abs_of_pos (pow_pos hc d)]

/-- Averages under the dilation `x ↦ c x`, `c > 0`. -/
theorem setAverage_smul_eq {c : ℝ} (hc : 0 < c) (W : Set (Vec d)) (g : Vec d → ℝ) :
    ⨍ x in c • W, g x = ⨍ y in W, g (c • y) := by
  rw [setAverage_eq, setAverage_eq, Measure.setIntegral_comp_smul_of_pos volume g W hc,
    Module.finrank_fin_fun, measureReal_smul_eq hc, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    mul_inv]
  ring

/-- Averages are linear. -/
theorem setAverage_const_mul' (U : Set (Vec d)) (a : ℝ) (g : Vec d → ℝ) :
    ⨍ x in U, a * g x = a * ⨍ x in U, g x := by
  rw [setAverage_eq, setAverage_eq, integral_const_mul, smul_eq_mul, smul_eq_mul]
  ring

theorem scalarRms_comp_smul {c : ℝ} (hc : 0 < c) (W : Set (Vec d)) (h : Vec d → ℝ) :
    scalarRms volume W (fun y => h (c • y)) = scalarRms volume (c • W) h := by
  unfold scalarRms
  rw [setAverage_smul_eq hc]

theorem scalarRms_const_mul (W : Set (Vec d)) (a : ℝ) (h : Vec d → ℝ) :
    scalarRms volume W (fun y => a * h y) = |a| * scalarRms volume W h := by
  unfold scalarRms
  simp_rw [mul_pow]
  rw [setAverage_const_mul', Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

/-- `‖ε φ(·/ε)‖_{L̲²(εW)} = ε ‖φ‖_{L̲²(W)}`. -/
theorem scalarRms_rescaled {ε : ℝ} (hε : 0 < ε) (W : Set (Vec d)) (φ : Vec d → ℝ) :
    scalarRms volume (ε • W) (fun x => ε * φ (ε⁻¹ • x)) = ε * scalarRms volume W φ := by
  rw [← scalarRms_comp_smul hε]
  simp only [inv_smul_smul₀ hε.ne']
  rw [scalarRms_const_mul, abs_of_pos hε]

theorem coordinateDerivative_const_mul_comp_smul {ψ : Vec d → ℝ} (hψ : Differentiable ℝ ψ)
    (a c : ℝ) (i : Fin d) (y : Vec d) :
    coordinateDerivative i (fun z => a * ψ (c • z)) y =
      a * (c * coordinateDerivative i ψ (c • y)) := by
  have h1 : HasFDerivAt (fun z : Vec d => c • z) (c • ContinuousLinearMap.id ℝ (Vec d)) y :=
    (hasFDerivAt_id (𝕜 := ℝ) y).const_smul c
  have h : HasFDerivAt (fun z => ψ (c • z))
      ((fderiv ℝ ψ (c • y)).comp (c • ContinuousLinearMap.id ℝ (Vec d))) y :=
    (hψ _).hasFDerivAt.comp y h1
  unfold coordinateDerivative
  rw [(h.const_mul a).fderiv]
  show a • ((fderiv ℝ ψ (c • y)).comp (c • ContinuousLinearMap.id ℝ (Vec d))) (unitVector i) =
    a * (c * fderiv ℝ ψ (c • y) (unitVector i))
  rw [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul, smul_eq_mul]

/-- **The scaling (0.30) of the normalized `H⁻¹` norm**: for `c > 0`,
`‖f(·/c)‖_{H̲⁻¹(cW)} ≤ c ‖f‖_{H̲⁻¹(W)}`. -/
theorem negativeSobolevOneNorm_comp_inv_smul_le (hd : 0 < d) {W : Set (Vec d)}
    (hW0 : volume W ≠ 0) {c : ℝ} (hc : 0 < c) (f : Vec d → ℝ) :
    negativeSobolevOneNorm 2 (c • W) (fun x => f (c⁻¹ • x)) 0 ≤
      ENNReal.ofReal c * negativeSobolevOneNorm 2 W f 0 := by
  have hq : ENNReal.ofReal ((2 : ℝ) / (2 - 1)) = 2 := by norm_num
  have hcW : volume (c • W) = ENNReal.ofReal (c ^ d) * volume W := by
    rw [Measure.addHaar_smul, Module.finrank_fin_fun, abs_of_pos (pow_pos hc d)]
  have hcW0 : volume (c • W) ≠ 0 := by
    rw [hcW]; exact mul_ne_zero (by simp; positivity) hW0
  refine iSup_le fun ⟨ψ, hψ, hψ1⟩ => ?_
  rw [hq] at hψ1
  obtain ⟨χ, hχdef⟩ : ∃ χ : Vec d → ℝ, χ = fun y => c⁻¹ * ψ (c • y) := ⟨_, rfl⟩
  have hψd : Differentiable ℝ ψ := hψ.1.differentiable (by simp)
  have hdχ : ∀ i, coordinateDerivative i χ = fun y => coordinateDerivative i ψ (c • y) :=
    fun i => by
      funext y
      rw [hχdef, coordinateDerivative_const_mul_comp_smul hψd, ← mul_assoc,
        inv_mul_cancel₀ hc.ne', one_mul]
  have hχc : ContDiff ℝ (⊤ : ℕ∞) χ := by
    rw [hχdef]; exact contDiff_const.mul (hψ.1.comp (contDiff_const_smul c))
  have hψcs : HasCompactSupport (fun y => ψ (c • y)) := hψ.2.1.comp_smul hc.ne'
  have hχs : HasCompactSupport χ := by
    rw [hχdef]; exact hψcs.mul_left (f := fun _ => c⁻¹)
  have hχU : tsupport χ ⊆ W := by
    intro y hy
    have hy' : y ∈ tsupport (fun y => ψ (c • y)) := by
      rw [hχdef] at hy; exact tsupport_mul_subset_right hy
    have h1 : c • y ∈ tsupport ψ :=
      tsupport_comp_subset_preimage ψ (f := fun y : Vec d => c • y) (continuous_const_smul c) hy'
    exact (Set.smul_mem_smul_set_iff₀ hc.ne' W y).1 (hψ.2.2 h1)
  have hχT : IsSpatialTest W χ := ⟨hχc, hχs, hχU⟩
  have hmem : ∀ (U : Set (Vec d)) (g : Vec d → ℝ), Continuous g → HasCompactSupport g →
      MemLp g 2 (volume.restrict U) := fun U g hg hgs =>
    memLp_two_of_continuous_hasCompactSupport hg hgs
  have hψi : ∀ i, Continuous (coordinateDerivative i ψ) := fun i =>
    continuous_gradient_apply hψ.1 i
  have hψis : ∀ i, HasCompactSupport (coordinateDerivative i ψ) := fun i =>
    hasCompactSupport_gradient_apply hψ.2.1 i
  have hnorm : sobolevOneTestNorm 2 W χ = sobolevOneTestNorm 2 (c • W) ψ := by
    unfold sobolevOneTestNorm
    have hsr : ∀ (U : Set (Vec d)) (h : Vec d → ℝ), 0 ≤ scalarRms volume U h := fun _ _ =>
      Real.sqrt_nonneg _
    rw [eLpMeanNormOn_two_eq_ofReal_scalarRms hW0 (hmem W χ hχc.continuous hχs),
      eLpMeanNormOn_two_eq_ofReal_scalarRms hcW0 (hmem _ ψ hψ.1.continuous hψ.2.1),
      ENNReal.toReal_ofReal (hsr _ _), ENNReal.toReal_ofReal (hsr _ _)]
    have e1 : ∀ i, (PDE.eLpMeanNormOn W 2 (coordinateDerivative i χ)).toReal =
        (PDE.eLpMeanNormOn (c • W) 2 (coordinateDerivative i ψ)).toReal := fun i => by
      rw [hdχ i, eLpMeanNormOn_two_eq_ofReal_scalarRms hW0
          (hmem W (fun y => coordinateDerivative i ψ (c • y))
            ((hψi i).comp (continuous_const_smul c)) ((hψis i).comp_smul hc.ne')),
        eLpMeanNormOn_two_eq_ofReal_scalarRms hcW0 (hmem _ _ (hψi i) (hψis i)),
        scalarRms_comp_smul hc]
    simp_rw [e1]
    congr 1
    rw [hχdef, scalarRms_const_mul, scalarRms_comp_smul hc, hcW, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), abs_of_pos (inv_pos.2 hc),
      Real.mul_rpow (by positivity) ENNReal.toReal_nonneg, ← Real.rpow_natCast,
      ← Real.rpow_mul hc.le]
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [show (d : ℝ) * (-1 / d) = -1 by field_simp, Real.rpow_neg_one]
    ring
  have hχ1 : sobolevOneTestNorm (ENNReal.ofReal ((2 : ℝ) / (2 - 1))) W χ ≤ 1 := by
    rw [hq, hnorm]; exact hψ1
  have hle : ENNReal.ofReal |distributionPairing W f 0 χ| ≤ negativeSobolevOneNorm 2 W f 0 :=
    le_iSup (fun ψ : {ψ : Vec d → ℝ // IsSpatialTest W ψ ∧
      sobolevOneTestNorm (ENNReal.ofReal ((2 : ℝ) / (2 - 1))) W ψ ≤ 1} =>
        ENNReal.ofReal |distributionPairing W f 0 ψ.1|) ⟨χ, hχT, hχ1⟩
  have heq : distributionPairing (c • W) (fun x => f (c⁻¹ • x)) 0 ψ =
      c * distributionPairing W f 0 χ := by
    unfold distributionPairing
    rw [setAverage_smul_eq hc, ← setAverage_const_mul']
    congr 1
    funext y
    have hc0 : c ≠ 0 := hc.ne'
    simp only [hχdef, Pi.zero_apply, inv_smul_smul₀ hc0, dot, zero_mul, Finset.sum_const_zero,
      sub_zero]
    field_simp
  show ENNReal.ofReal |distributionPairing (c • W) (fun x => f (c⁻¹ • x)) 0 ψ| ≤ _
  rw [heq, abs_mul, abs_of_pos hc, ENNReal.ofReal_mul hc.le]
  exact mul_le_mul_right hle _

/-- `‖c f‖_{Ĥ̲⁻¹(U)} ≤ |c| ‖f‖_{Ĥ̲⁻¹(U)}`. -/
theorem hatNegativeSobolevNorm_const_mul_le (U : Set (Vec d)) (c : ℝ) (f : Vec d → ℝ) :
    hatNegativeSobolevNorm U (fun x => c * f x) ≤
      ENNReal.ofReal |c| * hatNegativeSobolevNorm U f := by
  refine iSup_le fun v => ?_
  show ENNReal.ofReal |⨍ x in U, c * f x * v.1.1 x ∂volume| ≤ _
  have e : ⨍ x in U, c * f x * v.1.1 x ∂volume = c * ⨍ x in U, f x * v.1.1 x ∂volume := by
    simp_rw [mul_assoc]
    exact setAverage_const_mul' U c _
  rw [e, abs_mul, ENNReal.ofReal_mul (abs_nonneg c)]
  exact mul_le_mul_right (le_iSup (fun v : {v : (Vec d → ℝ) × (Vec d → Vec d) //
    H1 U v.1 v.2 ∧ h1Norm U v.1 v.2 ≤ 1} =>
      ENNReal.ofReal |⨍ x in U, f x * v.1.1 x ∂volume|) v) _

/-- The minimizer of (1.8) is linear in the slope: `(c u, c g)` is the minimizer for `c e`. -/
theorem _root_.QSH.IsDirichletMinimizer.const_smul {a : CoefficientField d Λ} {U : Set (Vec d)}
    (hU : volume U ≠ ⊤) {e : Vec d} {u : Vec d → ℝ} {g : Vec d → Vec d}
    (h : IsDirichletMinimizer a U e u g) (c : ℝ) :
    IsDirichletMinimizer a U (c • e) (fun x => c * u x) (fun x => c • g x) := by
  rw [isDirichletMinimizer_iff_solvesDirichletProblem a hU] at h
  rw [isDirichletMinimizer_iff_solvesDirichletProblem a hU]
  refine ⟨(h.1.linearCombination (H01_zero U) c 0).congr (fun x => by ring)
    (fun x => by simp), fun w k hw => ?_⟩
  have h0 := h.2 w k hw
  have e : ∀ x, dot (k x) ((a x).mulVec (c • e + c • g x)) =
      c * dot (k x) ((a x).mulVec (e + g x)) := fun x => by
    rw [← smul_add, Matrix.mulVec_smul, dot_smul_right']
  simp_rw [e]
  rw [integral_const_mul, h0, mul_zero]

/-- The real inequality of the proof of (1.57). -/
theorem term_bound_real {ε q H₁ H₂ C₁₀ C₁₃ E : ℝ} (hεq : ε ^ 2 ≤ 9 * q) (h10 : q * H₁ ^ 2 + q * H₂ ^ 2 ≤ C₁₀ * q + C₁₀ * E) :
    (2 * ε * C₁₃ * H₁ + 2 * ε * H₂) ^ 2 ≤ 72 * (C₁₃ ^ 2 + 1) * C₁₀ * (q + E) := by
  have h1 : (2 * ε * C₁₃ * H₁ + 2 * ε * H₂) ^ 2 ≤
      8 * ((C₁₃ ^ 2 + 1) * (ε ^ 2 * (H₁ ^ 2 + H₂ ^ 2))) := by
    nlinarith [mul_nonneg (sq_nonneg ε) (sq_nonneg (C₁₃ * H₁ - H₂)),
      mul_nonneg (sq_nonneg ε) (sq_nonneg (C₁₃ * H₂)), mul_nonneg (sq_nonneg ε) (sq_nonneg H₁)]
  have h2 : ε ^ 2 * (H₁ ^ 2 + H₂ ^ 2) ≤ 9 * (C₁₀ * (q + E)) := by
    nlinarith [mul_le_mul_of_nonneg_right hεq (add_nonneg (sq_nonneg H₁) (sq_nonneg H₂))]
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ C₁₃ ^ 2 + 1)
  nlinarith [h1, h3]

set_option maxHeartbeats 400000 in
/-- One term of `E'(ε)`, from the bounds of Proposition 1.10 for `(φ/2, ∇φ/2)` and of
Lemma 1.13 for `φ`. -/
theorem twoScaleDeviation_term_le (hd : 0 < d) {a : CoefficientField d Λ} {A : Mat d} {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (k : Fin d) {φ : Vec d → ℝ} {Dφ : Vec d → Vec d}
    {C₁₀ C₁₃ E : ℝ} (hC₁₀ : 0 ≤ C₁₀) (hC₁₃ : 0 ≤ C₁₃) (hE : 0 ≤ E)
    (h10 : ENNReal.ofReal (((3 : ℝ) ^ triadicScale ε)⁻¹ ^ 2) *
        vectorHatNegativeSobolevNorm (triadicCube d (triadicScale ε))
          (fun x => (1 / 2 : ℝ) • Dφ x) ^ 2 +
      ENNReal.ofReal (((3 : ℝ) ^ triadicScale ε)⁻¹ ^ 2) *
        vectorHatNegativeSobolevNorm (triadicCube d (triadicScale ε))
          (fun x => (a x).mulVec ((1 / 2 : ℝ) • unitVector k + (1 / 2 : ℝ) • Dφ x) -
            A.mulVec ((1 / 2 : ℝ) • unitVector k)) ^ 2 ≤
      ENNReal.ofReal (C₁₀ * ((3 : ℝ) ^ triadicScale ε)⁻¹ ^ 2 + C₁₀ * E))
    (h13 : ENNReal.ofReal (scalarRms volume (triadicCube d (triadicScale ε)) φ) ≤
      ENNReal.ofReal C₁₃ * vectorHatNegativeSobolevNorm (triadicCube d (triadicScale ε)) Dφ) :
    (ENNReal.ofReal (scalarRms volume (ε • triadicCube d (triadicScale ε))
        (fun x => ε * φ (ε⁻¹ • x))) +
      vectorNegativeSobolevOneNorm 2 (ε • triadicCube d (triadicScale ε))
        (fun x => (a (ε⁻¹ • x)).mulVec (unitVector k + Dφ (ε⁻¹ • x)) -
          A.mulVec (unitVector k))) ^ 2 ≤
      ENNReal.ofReal (72 * (C₁₃ ^ 2 + 1) * C₁₀ *
        (((3 : ℝ) ^ triadicScale ε)⁻¹ ^ 2 + E)) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = triadicScale ε := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Set (Vec d), T = triadicCube d m := ⟨_, rfl⟩
  rw [← hm, ← hT] at h10 h13 ⊢
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = ((3 : ℝ) ^ m)⁻¹ ^ 2 := ⟨_, rfl⟩
  rw [← hq] at h10 ⊢
  have hT0 : volume T ≠ 0 := by rw [hT]; exact volume_triadicCube_ne_zero d m
  have hTt : volume T ≠ ⊤ := by rw [hT]; exact volume_triadicCube_ne_top d m
  have h3m : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hq0 : 0 < q := by rw [hq]; positivity
  obtain ⟨hεl, hεu⟩ := three_pow_triadicScale_bounds hε hε1
  rw [← hm] at hεl hεu
  have hεq : ε ^ 2 ≤ 9 * q := by
    have hx : 0 ≤ ((3 : ℝ) ^ m)⁻¹ := by positivity
    rw [hq]
    nlinarith [hεu, hε.le, hx]
  -- the two norms of Proposition 1.10
  obtain ⟨h₁, hh₁⟩ : ∃ h₁ : ℝ≥0∞, h₁ = vectorHatNegativeSobolevNorm T
      (fun x => (1 / 2 : ℝ) • Dφ x) := ⟨_, rfl⟩
  obtain ⟨h₂, hh₂⟩ : ∃ h₂ : ℝ≥0∞, h₂ = vectorHatNegativeSobolevNorm T
      (fun x => (a x).mulVec ((1 / 2 : ℝ) • unitVector k + (1 / 2 : ℝ) • Dφ x) -
        A.mulVec ((1 / 2 : ℝ) • unitVector k)) := ⟨_, rfl⟩
  rw [← hh₁, ← hh₂] at h10
  have hfin : ENNReal.ofReal (C₁₀ * q + C₁₀ * E) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hq' : ENNReal.ofReal q ≠ 0 := by simp [hq0]
  have h₁t : h₁ ≠ ⊤ := by
    intro h
    rw [h] at h10
    simp [hq', ENNReal.mul_top] at h10
  have h₂t : h₂ ≠ ⊤ := by
    intro h
    rw [h] at h10
    simp [hq', ENNReal.mul_top] at h10
  have h10r : q * h₁.toReal ^ 2 + q * h₂.toReal ^ 2 ≤ C₁₀ * q + C₁₀ * E := by
    have h := ENNReal.toReal_mono hfin h10
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top h₁t))
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top h₂t)),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hq0.le] at h
    rwa [ENNReal.toReal_ofReal (add_nonneg (mul_nonneg hC₁₀ hq0.le) (mul_nonneg hC₁₀ hE))] at h
  -- `∇φ = 2 (∇φ/2)` and the flux of `φ` is twice that of `φ/2`
  have hD : vectorHatNegativeSobolevNorm T Dφ ≤ ENNReal.ofReal 2 * h₁ := by
    rw [hh₁]
    unfold vectorHatNegativeSobolevNorm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h := hatNegativeSobolevNorm_const_mul_le T 2 (fun x => ((1 / 2 : ℝ) • Dφ x) i)
    rw [abs_of_pos two_pos] at h
    refine le_trans (le_of_eq ?_) h
    congr 1
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hfl : ∀ x, (a x).mulVec (unitVector k + Dφ x) - A.mulVec (unitVector k) =
      (2 : ℝ) • ((a x).mulVec ((1 / 2 : ℝ) • unitVector k + (1 / 2 : ℝ) • Dφ x) -
        A.mulVec ((1 / 2 : ℝ) • unitVector k)) := fun x => by
    rw [← smul_add, Matrix.mulVec_smul, Matrix.mulVec_smul, ← smul_sub, smul_smul]
    norm_num
  have hF : vectorHatNegativeSobolevNorm T
      (fun x => (a x).mulVec (unitVector k + Dφ x) - A.mulVec (unitVector k)) ≤
        ENNReal.ofReal 2 * h₂ := by
    rw [hh₂]
    unfold vectorHatNegativeSobolevNorm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h := hatNegativeSobolevNorm_const_mul_le T 2 (fun x =>
      ((a x).mulVec ((1 / 2 : ℝ) • unitVector k + (1 / 2 : ℝ) • Dφ x) -
        A.mulVec ((1 / 2 : ℝ) • unitVector k)) i)
    rw [abs_of_pos two_pos] at h
    refine le_trans (le_of_eq ?_) h
    congr 1
    funext x
    dsimp only
    rw [hfl x, Pi.smul_apply, smul_eq_mul]
  -- the rescaled corrector
  have hR : scalarRms volume (ε • T) (fun x => ε * φ (ε⁻¹ • x)) ≤
      2 * ε * C₁₃ * h₁.toReal := by
    rw [scalarRms_rescaled hε]
    have h := h13.trans (mul_le_mul_right hD _)
    rw [← ENNReal.ofReal_toReal h₁t, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul hC₁₃, ENNReal.ofReal_le_ofReal_iff
        (mul_nonneg hC₁₃ (mul_nonneg zero_le_two ENNReal.toReal_nonneg))] at h
    calc ε * scalarRms volume T φ ≤ ε * (C₁₃ * (2 * h₁.toReal)) :=
          mul_le_mul_of_nonneg_left h hε.le
      _ = 2 * ε * C₁₃ * h₁.toReal := by ring
  -- the rescaled flux
  have hN : vectorNegativeSobolevOneNorm 2 (ε • T)
      (fun x => (a (ε⁻¹ • x)).mulVec (unitVector k + Dφ (ε⁻¹ • x)) - A.mulVec (unitVector k)) ≤
        ENNReal.ofReal (2 * ε * h₂.toReal) := by
    calc _ ≤ ∑ i : Fin d, ENNReal.ofReal ε * hatNegativeSobolevNorm T
          (fun x => ((a x).mulVec (unitVector k + Dφ x) - A.mulVec (unitVector k)) i) := by
          unfold vectorNegativeSobolevOneNorm
          refine Finset.sum_le_sum fun i _ => ?_
          exact (negativeSobolevOneNorm_comp_inv_smul_le hd hT0 hε
            (fun x => ((a x).mulVec (unitVector k + Dφ x) - A.mulVec (unitVector k)) i)).trans
            (mul_le_mul_right
              (negativeSobolevOneNorm_two_zero_le_hatNegativeSobolevNorm hT0 hTt _) _)
      _ = ENNReal.ofReal ε * vectorHatNegativeSobolevNorm T
          (fun x => (a x).mulVec (unitVector k + Dφ x) - A.mulVec (unitVector k)) := by
          rw [vectorHatNegativeSobolevNorm, Finset.mul_sum]
      _ ≤ ENNReal.ofReal ε * (ENNReal.ofReal 2 * h₂) := mul_le_mul_right hF _
      _ = ENNReal.ofReal (2 * ε * h₂.toReal) := by
          rw [← ENNReal.ofReal_toReal h₂t, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_mul hε.le, ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
          ring_nf
  calc _ ≤ (ENNReal.ofReal (2 * ε * C₁₃ * h₁.toReal) + ENNReal.ofReal (2 * ε * h₂.toReal)) ^ 2 :=
        pow_le_pow_left₀ (zero_le) (add_le_add (ENNReal.ofReal_le_ofReal hR) hN) 2
    _ = ENNReal.ofReal ((2 * ε * C₁₃ * h₁.toReal + 2 * ε * h₂.toReal) ^ 2) := by
        have hx0 : 0 ≤ 2 * ε * C₁₃ * h₁.toReal :=
          mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hε.le) hC₁₃) ENNReal.toReal_nonneg
        have hy0 : 0 ≤ 2 * ε * h₂.toReal :=
          mul_nonneg (mul_nonneg zero_le_two hε.le) ENNReal.toReal_nonneg
        rw [← ENNReal.ofReal_add hx0 hy0, ENNReal.ofReal_pow (add_nonneg hx0 hy0)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (term_bound_real hεq h10r)

/-- **(1.57)**: there is `C(d, Λ)` such that, for every law satisfying the assumptions,
`ε ∈ (0, 1]`, `m = m(ε)`, every coefficient field and every choice of the finite-volume
correctors `φ_k` on `□_m`, `E'(ε) ≤ C (3^{-2m} + E(m))`, where `E'(ε)` is computed with the
homogenized matrix; since `3^{-m} ≤ ε`, this gives `E'(ε) ≤ C (ε² + E(m))`. -/
theorem twoScaleDeviation_le (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : Measure (CoefficientField d Λ)), LawHypotheses P →
      ∀ (a : CoefficientField d Λ) (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ (φ : Fin d → Vec d → ℝ) (Dφ : Fin d → Vec d → Vec d),
      (∀ k, IsDirichletMinimizer a (triadicCube d (triadicScale ε)) (unitVector k) (φ k)
        (Dφ k)) →
      twoScaleDeviation a (homogenizedMatrix P) ε φ Dφ ≤
        ENNReal.ofReal (C * (((3 : ℝ) ^ triadicScale ε)⁻¹ ^ 2 +
          coarseDeviation P (triadicScale ε) a)) := by
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨C₁₀, hC₁₀, h10⟩ := proposition_1_10 (d := d) (Λ := Λ)
  obtain ⟨C₁₃, hC₁₃, h13⟩ := lemma_1_13 (d := d)
  refine ⟨d * (72 * (C₁₃ ^ 2 + 1) * C₁₀), mul_nonneg (Nat.cast_nonneg d)
    (mul_nonneg (by positivity) hC₁₀),
    fun P hP a ε hε hε1 φ Dφ hmin => ?_⟩
  have hhalf : ∀ k : Fin d, (1 / 2 : ℝ) • unitVector k ∈ originBall d 1 := fun k => by
    show euclideanNorm ((1 / 2 : ℝ) • unitVector k) < 1
    rw [euclideanNorm_smul, euclideanNorm_unitVector, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    norm_num
  have hTt := volume_triadicCube_ne_top d (triadicScale ε)
  have hterm : ∀ k, (ENNReal.ofReal (scalarRms volume (ε • triadicCube d (triadicScale ε))
        (fun x => ε * φ k (ε⁻¹ • x))) +
      vectorNegativeSobolevOneNorm 2 (ε • triadicCube d (triadicScale ε))
        (fun x => (a (ε⁻¹ • x)).mulVec (unitVector k + Dφ k (ε⁻¹ • x)) -
          (homogenizedMatrix P).mulVec (unitVector k))) ^ 2 ≤
      ENNReal.ofReal (72 * (C₁₃ ^ 2 + 1) * C₁₀ *
        (((3 : ℝ) ^ triadicScale ε)⁻¹ ^ 2 + coarseDeviation P (triadicScale ε) a)) := fun k =>
    twoScaleDeviation_term_le hd hε hε1 k hC₁₀ hC₁₃ (sq_nonneg _)
      (h10 P hP (triadicScale ε) a _ (hhalf k) _ _ ((hmin k).const_smul hTt (1 / 2)))
      ((h13 (triadicScale ε) (φ k) (Dφ k)).2 (hmin k).1)
  calc twoScaleDeviation a (homogenizedMatrix P) ε φ Dφ ≤ ∑ _k : Fin d,
        ENNReal.ofReal (72 * (C₁₃ ^ 2 + 1) * C₁₀ *
          (((3 : ℝ) ^ triadicScale ε)⁻¹ ^ 2 + coarseDeviation P (triadicScale ε) a)) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg d)]
        ring_nf

end TwoScale

end QSH
