import QuantitativeStochasticHomogenization.Ch05.Sec03.Lemma524
import QuantitativeStochasticHomogenization.Frozen.CoarsenedCoefficientEstimates

/-!
# Lemma 5.24 with `s = 1`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 5.3, Lemma 5.24, (5.63)–(5.64), with `s = 1`, in the form of
`QSH.Frozen.coarsenedCoefficientEstimates`, from:

* the estimate (5.58) of `J₁` (Theorem 4.6 (ii)–(iii)) with a constant `C₀(d, Λ)`
  (`EnergyEstimate`);
* the structure (4.12) of `A₁` against every mask `Φ_{z,r}`, almost surely (`LinearA1Gradients`);
* the almost sure measurability of `J₁(Φ_{z,r}, p, q)` and of the flux defect of (5.64).

The matrix `ā` enters through its symmetry only: the bound `|ā| ≤ 2Λd²` is a consequence of (5.58)
and of `0 ≤ J₁(Φ, p, 0) ≤ Λ|p|²` (`norm_toEuclideanCLM_le_of_energyEstimate`).
-/

open MeasureTheory Filter
open scoped InnerProduct InnerProductSpace Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- **(5.58) with `s = 1`** for the matrix `A`: `|J₁(Φ_{z,r}, p, q) - (½ p·Ap + ½ q·A⁻¹q - p·q)|`
is `O_1(C₀ r^{-d/2})` for `r ≥ 1` and `|p|, |q| < 1`. -/
def EnergyEstimate (P : Measure (CoefficientField d Λ)) (A : Mat d) (C₀ : ℝ) : Prop :=
  ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d, euclideanNorm p < 1 → euclideanNorm q < 1 →
    AEOsBound P (fun a => |J1Heat a z r p q - homogenizedJ1 A p q|) 1 (C₀ * r ^ (-(d : ℝ) / 2))

/-! ## Euclidean facts -/

theorem euclideanNorm_smul_eq_abs_mul (c : ℝ) (v : Vec d) :
    euclideanNorm (c • v) = |c| * euclideanNorm v := by
  have h : euclideanSq (c • v) = c ^ 2 * euclideanSq v := by
    simp only [euclideanSq, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [euclideanNorm, h, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, euclideanNorm]

theorem euclideanSq_unitVector_eq_one (j : Fin d) : euclideanSq (unitVector j) = 1 := by
  have h := dot_unitVector_mulVec (1 : Mat d) j j
  rw [Matrix.one_mulVec, Matrix.one_apply_eq] at h
  exact h

theorem euclideanNorm_unitVector (j : Fin d) : euclideanNorm (unitVector j) = 1 := by
  rw [euclideanNorm, euclideanSq_unitVector_eq_one, Real.sqrt_one]

theorem euclideanNorm_mulVec_unitVector_le (A : Mat d) {δ : ℝ}
    (hδ : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ δ) (j : Fin d) :
    euclideanNorm (A.mulVec (unitVector j)) ≤ δ := by
  rw [← norm_toLp, ← Matrix.toEuclideanCLM_toLp]
  calc ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (WithLp.toLp 2 (unitVector j))‖
      ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ * ‖(WithLp.toLp 2 (unitVector j) :
          EuclideanSpace ℝ (Fin d))‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ δ * 1 := by
        rw [norm_toLp, euclideanNorm_unitVector]
        exact mul_le_mul_of_nonneg_right hδ zero_le_one
    _ = δ := mul_one δ

/-! ## The bound on `ā` from (5.58) -/

theorem le_zero_of_forall_le_rpow (hd : 0 < d) {η C₀ : ℝ}
    (h : ∀ r : ℝ, 1 ≤ r → η ≤ C₀ * r ^ (-(d : ℝ) / 2)) : η ≤ 0 := by
  by_contra hη'
  have hη := not_le.mp hη'
  have hlim : Tendsto (fun r : ℝ => C₀ * r ^ (-((d : ℝ) / 2))) atTop (𝓝 (C₀ * 0)) :=
    (tendsto_rpow_neg_atTop (by positivity)).const_mul C₀
  rw [mul_zero] at hlim
  obtain ⟨r, hr1, hr2⟩ := ((hlim.eventually (gt_mem_nhds hη)).and (eventually_ge_atTop 1)).exists
  have := h r hr2
  rw [neg_div] at this
  linarith

theorem homogenizedJ1_zero_right (A : Mat d) (p : Vec d) :
    homogenizedJ1 A p 0 = (1 / 2 : ℝ) * dot p (A.mulVec p) := by
  simp only [homogenizedJ1, dot_eq_dotProduct, Matrix.mulVec_zero, dotProduct_zero]
  ring

/-- `0 ≤ p·Ap ≤ 2Λ|p|²` for `|p| < 1` from (5.58) and `0 ≤ J₁(Φ, p, 0) ≤ Λ|p|²`. -/
theorem form_bounds_of_energyEstimate {P : Measure (CoefficientField d Λ)}
    [IsProbabilityMeasure P] (hd : 0 < d) {A : Mat d} {C₀ : ℝ} (h558 : EnergyEstimate P A C₀)
    (p : Vec d) (hp : euclideanNorm p < 1) :
    0 ≤ dot p (A.mulVec p) ∧ dot p (A.mulVec p) ≤ 2 * Λ * euclideanSq p := by
  have h0 : euclideanNorm (0 : Vec d) < 1 := by
    simp [euclideanNorm, euclideanSq, dot]
  have hJ : ∀ (r : ℝ), 1 ≤ r → ∀ a : CoefficientField d Λ,
      0 ≤ J1Heat a 0 r p 0 ∧ J1Heat a 0 r p 0 ≤ Λ * euclideanSq p := fun r hr a => by
    have hr0 : 0 < r := by linarith
    have h1 := J1_nonneg a (heatKernel_nonneg 0 r) (integrable_heatKernel 0 hr0)
      (integral_heatKernel 0 hr0).le p 0
    have h2 := J1_le a (heatKernel_nonneg 0 r) (integrable_heatKernel 0 hr0)
      (integral_heatKernel 0 hr0).le p 0
    have h3 : euclideanSq (0 : Vec d) = 0 := by simp [euclideanSq, dot]
    rw [h3, add_zero] at h2
    exact ⟨h1, h2⟩
  constructor
  · have hle := le_zero_of_forall_le_rpow hd (η := -((1 / 2 : ℝ) * dot p (A.mulVec p)))
      (C₀ := C₀) fun r hr => (h558 0 r hr p 0 hp h0).le_of_le_ae
        (Eventually.of_forall fun a => by
          rw [homogenizedJ1_zero_right]
          have := (hJ r hr a).1
          exact (by linarith : _ ≤ J1Heat a 0 r p 0 - _).trans (le_abs_self _))
    linarith
  · have hle := le_zero_of_forall_le_rpow hd
      (η := (1 / 2 : ℝ) * dot p (A.mulVec p) - Λ * euclideanSq p)
      (C₀ := C₀) fun r hr => (h558 0 r hr p 0 hp h0).le_of_le_ae
        (Eventually.of_forall fun a => by
          rw [homogenizedJ1_zero_right]
          have := (hJ r hr a).2
          exact (by linarith : _ ≤ -(J1Heat a 0 r p 0 - _)).trans (neg_le_abs _))
    linarith

/-- **`|ā| ≤ 2Λd²`** from (5.58), for a symmetric `ā`. -/
theorem norm_toEuclideanCLM_le_of_energyEstimate {P : Measure (CoefficientField d Λ)}
    [IsProbabilityMeasure P] (hd : 0 < d) (hΛ0 : 0 ≤ Λ) {A : Mat d} (hA : A.transpose = A)
    {C₀ : ℝ} (h558 : EnergyEstimate P A C₀) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ 2 * Λ * d ^ 2 := by
  have hentry : ∀ j k : Fin d, |A j k| ≤ 2 * Λ := by
    intro j k
    set vp := (1 / 4 : ℝ) • (unitVector j + unitVector k) with hvp
    set vm := (1 / 4 : ℝ) • (unitVector j - unitVector k) with hvm
    have hnp : euclideanNorm vp ≤ 1 / 2 := by
      rw [hvp, euclideanNorm_smul_eq_abs_mul]
      have := euclideanNorm_add_le (unitVector j) (unitVector k)
      rw [euclideanNorm_unitVector, euclideanNorm_unitVector] at this
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
      linarith
    have hnm : euclideanNorm vm ≤ 1 / 2 := by
      rw [hvm, euclideanNorm_smul_eq_abs_mul]
      have := euclideanNorm_sub_le (unitVector j) (unitVector k)
      rw [euclideanNorm_unitVector, euclideanNorm_unitVector] at this
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
      linarith
    have hsp : euclideanSq vp ≤ 1 / 4 := by
      rw [← euclideanNorm_sq]
      have := euclideanNorm_nonneg vp
      nlinarith
    have hsm : euclideanSq vm ≤ 1 / 4 := by
      rw [← euclideanNorm_sq]
      have := euclideanNorm_nonneg vm
      nlinarith
    have hp := form_bounds_of_energyEstimate hd h558 vp (by linarith)
    have hm := form_bounds_of_energyEstimate hd h558 vm (by linarith)
    have hpol : A j k = 4 * (dot vp (A.mulVec vp) - dot vm (A.mulVec vm)) := by
      have hs := dot_mulVec_comm hA (unitVector j) (unitVector k)
      rw [dot_unitVector_mulVec, dot_unitVector_mulVec] at hs
      have h1 := dot_unitVector_mulVec A j j
      have h2 := dot_unitVector_mulVec A k k
      have h3 := dot_unitVector_mulVec A j k
      have h4 := dot_unitVector_mulVec A k j
      simp only [hvp, hvm, dot_eq_dotProduct, Matrix.mulVec_smul, Matrix.mulVec_add,
        Matrix.mulVec_sub, dotProduct_smul, smul_dotProduct, dotProduct_add, add_dotProduct,
        dotProduct_sub, sub_dotProduct, smul_eq_mul] at h1 h2 h3 h4 ⊢
      linarith
    rw [hpol, abs_le]
    constructor <;> nlinarith [hp.1, hp.2, hm.1, hm.2]
  refine (opNorm_le_sum_abs_inner (EuclideanSpace.basisFun (Fin d) ℝ) _).trans ?_
  simp only [← toLp_unitVector, Matrix.toEuclideanCLM_toLp, inner_toLp_toLp_eq_dot,
    dot_unitVector_mulVec]
  calc ∑ j : Fin d, ∑ k : Fin d, |A j k| ≤ ∑ _j : Fin d, ∑ _k : Fin d, 2 * Λ :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hentry j k
    _ = 2 * Λ * d ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ## Lemma 5.24 -/

/-- The bound `2Λd²` on `|ā|`. -/
def lemma524Delta (d : ℕ) (Λ : ℝ) : ℝ := 2 * Λ * d ^ 2

/-- The scale `t` of the polarization loads. -/
def lemma524Scale (d : ℕ) (Λ : ℝ) : ℝ := 1 / (4 + 2 * lemma524Delta d Λ)

/-- The constant `√Λ · 4 (1 + Λ + δ) · (2 t⁻²)²` of the quadratic bound. -/
def lemma524Quadratic (d : ℕ) (Λ : ℝ) : ℝ :=
  Real.sqrt Λ * (4 * (1 + Λ + lemma524Delta d Λ)) * (2 * (lemma524Scale d Λ ^ 2)⁻¹) ^ 2

/-- The constant of Lemma 5.24. -/
def lemma524Constant (d : ℕ) (Λ C₀ : ℝ) : ℝ :=
  (lemma524Scale d Λ ^ 2)⁻¹ * (5 * d ^ 2 * C₀) + lemma524Quadratic d Λ * (5 * d ^ 2 * C₀) ^ 2

theorem lemma524Constant_pos {d : ℕ} (hd : 0 < d) {Λ C₀ : ℝ} (hΛ : 0 ≤ Λ) (hC₀ : 0 < C₀) :
    0 < lemma524Constant d Λ C₀ := by
  have hδ : 0 ≤ lemma524Delta d Λ := by unfold lemma524Delta; positivity
  have ht : 0 < lemma524Scale d Λ := by unfold lemma524Scale; positivity
  have hK : 0 ≤ lemma524Quadratic d Λ := by unfold lemma524Quadratic; positivity
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  unfold lemma524Constant
  positivity

/-- **Lemma 5.24, (5.63)–(5.64), with `s = 1`**, for one law and one symmetric matrix `A`
satisfying (5.58). -/
theorem coarsenedCoefficient_aeOsBound (hd : 2 ≤ d) (hΛ : 1 < Λ)
    {P : Measure (CoefficientField d Λ)} [IsProbabilityMeasure P] {A : Mat d}
    (hA : A.transpose = A) {C₀ : ℝ} (hC₀ : 0 < C₀) (h558 : EnergyEstimate P A C₀)
    (hJm : ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
      AEMeasurable (fun a => J1Heat a z r p q) P)
    (hdim : ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ᵐ a ∂P, LinearA1Gradients a (heatKernel z r))
    (hDm : ∀ (z : Vec d) (r : ℝ), 1 ≤ r → AEMeasurable (fun a => coarseFluxDefect a A z r) P)
    (z : Vec d) (r : ℝ) (hr : 1 ≤ r) :
    AEOsBound P (fun a => matrixSize (coarsenedCoefficient a A z r)) 1
        (lemma524Constant d Λ C₀ * r ^ (-(d : ℝ) / 2)) ∧
      AEOsBound P (fun a => coarseFluxDefect a A z r) (1 / 2)
        (lemma524Constant d Λ C₀ * r ^ (-(d : ℝ))) := by
  have hd0 : 0 < d := by omega
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd0
  have hΛ0 : 0 ≤ Λ := by linarith
  have hr0 : 0 < r := by linarith
  set δ := lemma524Delta d Λ with hδdef
  set t := lemma524Scale d Λ with htdef
  set θ := C₀ * r ^ (-(d : ℝ) / 2) with hθdef
  have hδ : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ δ :=
    norm_toEuclideanCLM_le_of_energyEstimate hd0 hΛ0 hA h558
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have ht0 : 0 < t := by rw [htdef, lemma524Scale]; positivity
  have h2t : 2 * t < 1 := by
    rw [htdef, lemma524Scale, ← hδdef, mul_one_div, div_lt_one (by positivity)]
    linarith
  have htδ : t * δ < 1 := by
    rw [htdef, lemma524Scale, ← hδdef, one_div_mul_eq_div, div_lt_one (by positivity)]
    linarith
  have hθ0 : 0 < θ := by rw [hθdef]; positivity
  -- the loads of the polarization lie in the unit ball
  have hball : ∀ c : ℝ, 0 ≤ c → ∀ v : Vec d, c * euclideanNorm v < 1 →
      euclideanNorm (c • v) < 1 := fun c hc v hv => by
    rwa [euclideanNorm_smul_eq_abs_mul, abs_of_nonneg hc]
  have hsum2 : ∀ j k : Fin d, t * euclideanNorm (unitVector j + unitVector k) < 1 := fun j k => by
    have := euclideanNorm_add_le (unitVector j) (unitVector k)
    rw [euclideanNorm_unitVector, euclideanNorm_unitVector] at this
    nlinarith
  have hdiff2 : ∀ j k : Fin d, t * euclideanNorm (unitVector j - unitVector k) < 1 :=
    fun j k => by
      have := euclideanNorm_sub_le (unitVector j) (unitVector k)
      rw [euclideanNorm_unitVector, euclideanNorm_unitVector] at this
      nlinarith
  have hAj : ∀ j : Fin d, t * euclideanNorm (A.mulVec (unitVector j)) < 1 := fun j => by
    have := euclideanNorm_mulVec_unitVector_le A hδ j
    nlinarith
  have he : ∀ k : Fin d, t * euclideanNorm (unitVector k) < 1 := fun k => by
    rw [euclideanNorm_unitVector]; linarith
  have h0 : euclideanNorm (0 : Vec d) < 1 := by simp [euclideanNorm, euclideanSq, dot]
  -- the sum `Y` of the errors is `O_1(5 d² C₀ r^{-d/2})`
  have hterm : ∀ j k : Fin d,
      AEOsBound P (fun a => polarizationTerm a A z r t j k) 1 (5 * θ) := fun j k => by
    have e1 := h558 z r hr _ _ (hball t ht0.le _ (hsum2 j k)) (hball t ht0.le _ (hAj j))
    have e2 := h558 z r hr _ _ (hball t ht0.le _ (hdiff2 j k)) (hball t ht0.le _ (hAj j))
    have e3 := h558 z r hr _ _ (hball t ht0.le _ (he k)) (hball t ht0.le _ (he j))
    have e4 := h558 z r hr _ _ (hball t ht0.le _ (he k)) h0
    have e5 := h558 z r hr _ _ h0 (hball t ht0.le _ (he j))
    have hs := ((((e1.add e2 le_rfl).add e3 le_rfl).add e4 le_rfl).add e5 le_rfl)
    exact hs.mono_scale (le_of_eq (by ring))
  have hY : AEOsBound P (fun a => polarizationError a A z r t) 1 (5 * d ^ 2 * C₀ *
      r ^ (-(d : ℝ) / 2)) := by
    have hne : (Finset.univ : Finset (Fin d)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hd0⟩⟩
    have hinner : ∀ j ∈ (Finset.univ : Finset (Fin d)),
        AEOsBound P (fun a => ∑ k ∈ Finset.univ, polarizationTerm a A z r t j k) 1
          (∑ _k ∈ (Finset.univ : Finset (Fin d)), 5 * θ) := fun j _ =>
      aeOsBound_finset_sum _ hne le_rfl fun k _ => hterm j k
    have houter := aeOsBound_finset_sum _ hne le_rfl hinner
    refine houter.mono_scale (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hθdef]
    ring
  have hY0 : ∀ a : CoefficientField d Λ, 0 ≤ polarizationError a A z r t :=
    fun a => polarizationError_nonneg a A z r t
  -- the deterministic bounds hold almost surely
  have hdet : ∀ᵐ a ∂P, matrixSize (coarsenedCoefficient a A z r) ≤
        (t ^ 2)⁻¹ * polarizationError a A z r t ∧
      coarseFluxDefect a A z r ≤ lemma524Quadratic d Λ * polarizationError a A z r t ^ 2 := by
    filter_upwards [hdim z r hr] with a ⟨G, hspan, hreal, hG2⟩
    obtain ⟨h1, h2⟩ := polarization_bounds a A z hr0 G hspan hreal hG2 hA ht0.ne' hδ
    refine ⟨h1, h2.trans (le_of_eq ?_)⟩
    rw [abs_of_nonneg hΛ0, lemma524Quadratic, ← hδdef, ← htdef]
    ring
  have hcc : ∀ j k : Fin d, AEMeasurable (fun a => coarsenedCoefficient a A z r j k) P :=
    fun j k => ((hJm z r hr _ _).sub (hJm z r hr _ _)).div_const 2
  have hsize : AEMeasurable (fun a => matrixSize (coarsenedCoefficient a A z r)) P :=
    Real.continuous_sqrt.measurable.comp_aemeasurable (Finset.aemeasurable_fun_sum _ fun j _ =>
      Finset.aemeasurable_fun_sum _ fun k _ => (hcc j k).pow_const 2)
  have hrpow : (r ^ (-(d : ℝ) / 2)) ^ 2 = r ^ (-(d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
    norm_num
  have hC1 : (t ^ 2)⁻¹ * (5 * d ^ 2 * C₀) ≤ lemma524Constant d Λ C₀ := by
    have hK : 0 ≤ lemma524Quadratic d Λ * (5 * d ^ 2 * C₀) ^ 2 := by
      unfold lemma524Quadratic; positivity
    rw [lemma524Constant, ← htdef]
    linarith
  have hC2 : lemma524Quadratic d Λ * (5 * d ^ 2 * C₀) ^ 2 ≤ lemma524Constant d Λ C₀ := by
    have hK : 0 ≤ (t ^ 2)⁻¹ * (5 * d ^ 2 * C₀) := by positivity
    rw [lemma524Constant, ← htdef]
    linarith
  have hrp : 0 ≤ r ^ (-(d : ℝ) / 2) := Real.rpow_nonneg hr0.le _
  have hrp' : 0 ≤ r ^ (-(d : ℝ)) := Real.rpow_nonneg hr0.le _
  constructor
  · have h1 := (hY.const_mul (inv_pos.mpr (pow_pos ht0 2))).of_le_ae hsize
      (hdet.mono fun a ha => ha.1)
    refine h1.mono_scale ?_
    calc (t ^ 2)⁻¹ * (5 * d ^ 2 * C₀ * r ^ (-(d : ℝ) / 2))
        = (t ^ 2)⁻¹ * (5 * d ^ 2 * C₀) * r ^ (-(d : ℝ) / 2) := by ring
      _ ≤ lemma524Constant d Λ C₀ * r ^ (-(d : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hC1 hrp
  · have hK0 : 0 < lemma524Quadratic d Λ := by
      unfold lemma524Quadratic
      have : 0 < Real.sqrt Λ := Real.sqrt_pos.mpr (by linarith)
      have : 0 < lemma524Scale d Λ := ht0
      positivity
    have h2 := ((hY.sq (Eventually.of_forall hY0)).const_mul hK0).of_le_ae (hDm z r hr)
      (hdet.mono fun a ha => ha.2)
    refine h2.mono_scale ?_
    calc lemma524Quadratic d Λ * (5 * d ^ 2 * C₀ * r ^ (-(d : ℝ) / 2)) ^ 2
        = lemma524Quadratic d Λ * (5 * d ^ 2 * C₀) ^ 2 * (r ^ (-(d : ℝ) / 2)) ^ 2 := by ring
      _ = lemma524Quadratic d Λ * (5 * d ^ 2 * C₀) ^ 2 * r ^ (-(d : ℝ)) := by rw [hrpow]
      _ ≤ lemma524Constant d Λ C₀ * r ^ (-(d : ℝ)) := mul_le_mul_of_nonneg_right hC2 hrp'

/-- **`QSH.Frozen.coarsenedCoefficientEstimates`** (Lemma 5.24 with `s = 1`) from (5.58) with a
constant `C₀(d, Λ)`, the structure (4.12) of `A₁` against the masks `Φ_{z,r}`, and the almost sure
measurability of `J₁(Φ_{z,r}, p, q)` and of the flux defect. -/
theorem coarsenedCoefficientEstimates_of
    (h558 : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
        EnergyEstimate P S.homogenized C₀)
    (hJm : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ P : Measure (CoefficientField d Λ),
      LawHypotheses P → ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
        AEMeasurable (fun a => J1Heat a z r p q) P)
    (hdim : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ P : Measure (CoefficientField d Λ),
      LawHypotheses P → HomogenizationData P → ∀ (z : Vec d) (r : ℝ), 1 ≤ r →
        ∀ᵐ a ∂P, LinearA1Gradients a (heatKernel z r))
    (hDm : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ P : Measure (CoefficientField d Λ),
      LawHypotheses P → ∀ S : HomogenizationData P, ∀ (z : Vec d) (r : ℝ), 1 ≤ r →
        AEMeasurable (fun a => coarseFluxDefect a S.homogenized z r) P) :
    QSH.Frozen.coarsenedCoefficientEstimates := by
  intro d hd Λ hΛ
  obtain ⟨C₀, hC₀, hC⟩ := h558 d hd Λ hΛ
  refine ⟨lemma524Constant d Λ C₀, lemma524Constant_pos (by omega) (by linarith) hC₀, ?_⟩
  intro P hP S z r hr
  have := hP.1
  exact coarsenedCoefficient_aeOsBound hd hΛ S.symmetric hC₀ (hC P hP S)
    (hJm d hd Λ hΛ P hP) (hdim d hd Λ hΛ P hP S) (hDm d hd Λ hΛ P hP S) z r hr

end QSH
