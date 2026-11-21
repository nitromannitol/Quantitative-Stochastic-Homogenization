import QuantitativeStochasticHomogenization.Ch01.Sec02SubadditiveQuantity
import QuantitativeStochasticHomogenization.Ch04.Sec01.Proposition43

/-!
# Bounds on the Dirichlet energy `μ(U, e)`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.2, the bounds `½|e|² ≤ μ(U, e) ≤ ½Λ|e|²` of the Dirichlet energy (1.7) (used in
Lemma 1.1 and Definition 1.2).

For a measurable set `U` of finite positive volume:

* `dirichletEnergy_le`: `μ(U, e) ≤ ½Λ|e|²`, from the trial `u = 0`;
* `le_dirichletEnergy`: `½|e|² ≤ μ(U, e)`, from `a ≥ I`, Jensen's inequality and the vanishing of
  the mean of the gradient of a function of `H¹₀(U)` (`setIntegral_eq_zero_of_H01`), which
  follows from the approximation by smooth compactly supported functions and
  `∫ ∂ᵢφ = 0` (`integral_coordinateDerivative_eq_zero`).
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- The integral of a partial derivative of a smooth compactly supported function vanishes. -/
theorem integral_coordinateDerivative_eq_zero {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hφ : IsSpatialTest U φ) (i : Fin d) : ∫ x, coordinateDerivative i φ x = 0 := by
  obtain ⟨hs, hc, -⟩ := hφ
  have hdiff : Differentiable ℝ φ := hs.differentiable (by simp)
  have hcont : Continuous fun x => fderiv ℝ φ x (unitVector i) :=
    (hs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hint : Integrable fun x => fderiv ℝ φ x (unitVector i) :=
    hcont.integrable_of_hasCompactSupport (hc.fderiv_apply ℝ (unitVector i))
  have h : ∫ x, (fun _ : Vec d => (1 : ℝ)) x * fderiv ℝ φ x (unitVector i) =
      -∫ x, fderiv ℝ (fun _ : Vec d => (1 : ℝ)) x (unitVector i) * φ x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (by simp) (by simpa using hint)
      (by simpa using hs.continuous.integrable_of_hasCompactSupport hc)
      (fun x _ => differentiableAt_const _) (fun x _ => hdiff x)
  simpa [coordinateDerivative] using h

theorem integrable_euclideanSq_of_memLp {μ : Measure (Vec d)} {g : Vec d → Vec d}
    (hg : MemLp g 2 μ) : Integrable (fun x => euclideanSq (g x)) μ := by
  simp only [euclideanSq, dot, ← sq]
  exact integrable_finsetSum _ fun i _ => (MemLp.eval hg i).integrable_sq

/-- **The mean of the gradient of a function of `H¹₀(U)` vanishes.** -/
theorem setIntegral_eq_zero_of_H01 {U : Set (Vec d)} (hU : volume U ≠ ⊤) {u : Vec d → ℝ} {g : Vec d → Vec d} (hu : H01 U u g) (i : Fin d) :
    ∫ x in U, g x i = 0 := by
  obtain ⟨-, hg, -, v, hv, -, hconv⟩ := hu
  have hfin : IsFiniteMeasure (volume.restrict U) := ⟨by rw [Measure.restrict_apply_univ]; exact hU.lt_top⟩
  have hgi : Integrable (fun x => g x i) (volume.restrict U) := (MemLp.eval hg i).integrable one_le_two
  -- the approximants have mean zero
  have hgradv : ∀ n, Continuous (gradient (v n)) := fun n =>
    continuous_pi fun l => ((hv n).1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgradvc : ∀ n, HasCompactSupport (gradient (v n)) := fun n => by
    refine (hv n).2.1.mono' fun x hx => ?_
    by_contra hxs
    exact hx (by
      have h : fderiv ℝ (v n) x = 0 := fderiv_of_notMem_tsupport ℝ hxs
      funext l
      simp [gradient, coordinateDerivative, h])
  have hvint : ∀ n, Integrable (fun x => coordinateDerivative i (v n) x) (volume.restrict U) :=
    fun n => ((continuous_apply i).comp (hgradv n)).integrable_of_hasCompactSupport
      ((hgradvc n).comp_left (g := fun w : Vec d => w i) rfl) |>.restrict
  have hvi : ∀ n, ∫ x in U, coordinateDerivative i (v n) x = 0 := by
    intro n
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact integral_coordinateDerivative_eq_zero (hv n) i
    · intro x hx
      have hxs : x ∉ tsupport (v n) := fun h => hx ((hv n).2.2 h)
      have h : fderiv ℝ (v n) x = 0 := fderiv_of_notMem_tsupport ℝ hxs
      simp [coordinateDerivative, h]
  -- the energies of the differences
  have hEint : ∀ n, Integrable (fun x => euclideanSq (gradient (v n) x - g x)) (volume.restrict U) := by
    intro n
    have hm : MemLp (gradient (v n)) 2 (volume.restrict U) :=
      ((hgradv n).memLp_of_hasCompactSupport (hgradvc n)).restrict U
    exact integrable_euclideanSq_of_memLp (hm.sub hg)
  set V : ℝ := (volume U).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have key : ∀ δ : ℝ, 0 < δ → |∫ x in U, g x i| ≤ δ / 2 * V := by
    intro δ hδ
    have hbound : ∀ n, |∫ x in U, g x i| ≤ δ / 2 * V +
        1 / (2 * δ) * ∫ x in U, euclideanSq (gradient (v n) x - g x) := by
      intro n
      have hdiff : (∫ x in U, g x i) = ∫ x in U, (g x i - coordinateDerivative i (v n) x) := by
        rw [integral_sub hgi (hvint n), hvi n, sub_zero]
      rw [hdiff]
      refine (abs_integral_le_integral_abs).trans ?_
      have hpt : ∀ x, |g x i - coordinateDerivative i (v n) x| ≤
          δ / 2 + 1 / (2 * δ) * euclideanSq (gradient (v n) x - g x) := by
        intro x
        have hc : (g x i - coordinateDerivative i (v n) x) ^ 2 ≤
            euclideanSq (gradient (v n) x - g x) := by
          have : (g x i - coordinateDerivative i (v n) x) ^ 2 =
              (gradient (v n) x - g x) i * (gradient (v n) x - g x) i := by
            simp only [Pi.sub_apply, gradient]; ring
          rw [this]
          exact Finset.single_le_sum (f := fun l => (gradient (v n) x - g x) l *
            (gradient (v n) x - g x) l) (fun l _ => mul_self_nonneg _) (Finset.mem_univ i)
        have h1 : |g x i - coordinateDerivative i (v n) x| ≤
            δ / 2 + 1 / (2 * δ) * (g x i - coordinateDerivative i (v n) x) ^ 2 := by
          have hkey : δ / 2 + 1 / (2 * δ) * (g x i - coordinateDerivative i (v n) x) ^ 2 -
              |g x i - coordinateDerivative i (v n) x| =
              (|g x i - coordinateDerivative i (v n) x| - δ) ^ 2 / (2 * δ) := by
            rw [← sq_abs (g x i - coordinateDerivative i (v n) x)]
            field_simp
            ring
          have : 0 ≤ (|g x i - coordinateDerivative i (v n) x| - δ) ^ 2 / (2 * δ) := by positivity
          linarith
        have h2 : 1 / (2 * δ) * (g x i - coordinateDerivative i (v n) x) ^ 2 ≤
            1 / (2 * δ) * euclideanSq (gradient (v n) x - g x) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
        linarith
      calc ∫ x in U, |g x i - coordinateDerivative i (v n) x|
          ≤ ∫ x in U, (δ / 2 + 1 / (2 * δ) * euclideanSq (gradient (v n) x - g x)) :=
            integral_mono_ae (hgi.sub (hvint n)).abs ((integrable_const _).add
              ((hEint n).const_mul _)) (Filter.Eventually.of_forall hpt)
        _ = δ / 2 * V + 1 / (2 * δ) * ∫ x in U, euclideanSq (gradient (v n) x - g x) := by
            rw [integral_add (integrable_const _) ((hEint n).const_mul _), integral_const,
              integral_const_mul, smul_eq_mul, Measure.real, Measure.restrict_apply_univ, hV]
            ring
    have hlim : Tendsto (fun n => δ / 2 * V +
        1 / (2 * δ) * ∫ x in U, euclideanSq (gradient (v n) x - g x)) atTop (𝓝 (δ / 2 * V)) := by
      have := (hconv.const_mul (1 / (2 * δ))).const_add (δ / 2 * V)
      simpa using this
    exact ge_of_tendsto' hlim hbound
  by_contra hne
  have hpos : 0 < |∫ x in U, g x i| := abs_pos.mpr hne
  rcases hV0.lt_or_eq with hVp | hV0'
  · have : |∫ x in U, g x i| ≤ |∫ x in U, g x i| / 2 := by
      calc |∫ x in U, g x i| ≤ |∫ x in U, g x i| / V / 2 * V := key _ (div_pos hpos hVp)
        _ = |∫ x in U, g x i| / 2 := by field_simp
    linarith
  · have := key 1 one_pos
    rw [← hV0', mul_zero] at this
    linarith

/-! ## The bounds on `μ(U, e)` -/

theorem isSpatialTest_zero (U : Set (Vec d)) : IsSpatialTest U (fun _ => 0) :=
  ⟨contDiff_const, HasCompactSupport.zero, by simp⟩

theorem H01_zero (U : Set (Vec d)) : H01 U (fun _ => 0) (fun _ => 0) := by
  refine ⟨MemLp.zero, MemLp.zero, fun i => ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero,
    fun φ _ => by simp⟩, fun _ => fun _ => 0, fun _ => isSpatialTest_zero U, by simp, ?_⟩
  have h : ∀ x, gradient (fun _ : Vec d => (0 : ℝ)) x = 0 := fun x => by
    funext i; simp [gradient, coordinateDerivative]
  simp [h, euclideanSq, dot]

theorem setAverage_nonneg_of_nonneg {U : Set (Vec d)} {f : Vec d → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ ⨍ x in U, f x ∂volume := by
  rw [setAverage_eq, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr measureReal_nonneg) (integral_nonneg hf)

theorem energyDensity_nonneg (a : CoefficientField d Λ) (e g : Vec d) (x : Vec d) :
    0 ≤ (1 / 2 : ℝ) * dot (e + g) ((a x).mulVec (e + g)) :=
  mul_nonneg (by norm_num) ((euclideanSq_nonneg _).trans (a.elliptic x _).1)

theorem setAverage_le_of_le {U : Set (Vec d)} (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤)
    {f : Vec d → ℝ} {K : ℝ} (hK : 0 ≤ K) (hf : ∀ x, f x ≤ K) :
    ⨍ x in U, f x ∂volume ≤ K := by
  have hV : 0 < volume.real U := ENNReal.toReal_pos hU0 hU
  rw [setAverage_eq, smul_eq_mul]
  by_cases hint : IntegrableOn f U volume
  · have h1 : ∫ x in U, f x ≤ ∫ _x in U, K :=
      integral_mono hint (integrableOn_const hU) hf
    rw [setIntegral_const, smul_eq_mul] at h1
    calc (volume.real U)⁻¹ * ∫ x in U, f x ≤ (volume.real U)⁻¹ * (volume.real U * K) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hV.le)
      _ = K := by field_simp
  · rw [integral_undef hint, mul_zero]
    exact hK

/-- **`μ(U, e) ≤ ½Λ|e|²`**, from the trial `u = 0`. -/
theorem dirichletEnergy_le (a : CoefficientField d Λ) {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hU : volume U ≠ ⊤) (hΛ : 0 ≤ Λ) (e : Vec d) :
    dirichletEnergy a U e ≤ (1 / 2 : ℝ) * Λ * euclideanSq e := by
  have hmem : (⨍ x in U, (1 / 2 : ℝ) * dot (e + (fun _ : Vec d => (0 : Vec d)) x)
      ((a x).mulVec (e + (fun _ : Vec d => (0 : Vec d)) x)) ∂volume) ∈
      {E : ℝ | ∃ (u : Vec d → ℝ) (g : Vec d → Vec d), H01 U u g ∧
        E = ⨍ x in U, (1 / 2 : ℝ) * dot (e + g x) ((a x).mulVec (e + g x)) ∂volume} :=
    ⟨_, _, H01_zero U, rfl⟩
  have hbdd : BddBelow {E : ℝ | ∃ (u : Vec d → ℝ) (g : Vec d → Vec d), H01 U u g ∧
      E = ⨍ x in U, (1 / 2 : ℝ) * dot (e + g x) ((a x).mulVec (e + g x)) ∂volume} := by
    refine ⟨0, ?_⟩
    rintro E ⟨u, g, -, rfl⟩
    exact setAverage_nonneg_of_nonneg fun x => energyDensity_nonneg a e (g x) x
  refine (csInf_le hbdd hmem).trans ?_
  have hK : 0 ≤ (1 / 2 : ℝ) * Λ * euclideanSq e := by
    have := euclideanSq_nonneg e; positivity
  refine setAverage_le_of_le hU0 hU hK fun x => ?_
  have := (a.elliptic x e).2
  simp only [add_zero]
  nlinarith

/-- Jensen's inequality for set averages: `(⨍_U h)² ≤ ⨍_U h²`. -/
theorem sq_setAverage_le {U : Set (Vec d)} (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤)
    {h : Vec d → ℝ} (hh : IntegrableOn h U volume)
    (hh2 : IntegrableOn (fun x => h x ^ 2) U volume) :
    (⨍ x in U, h x ∂volume) ^ 2 ≤ ⨍ x in U, h x ^ 2 ∂volume := by
  have hV : 0 < volume.real U := ENNReal.toReal_pos hU0 hU
  set m := ⨍ x in U, h x ∂volume with hm
  have hmV : ∫ x in U, h x = volume.real U * m := by
    rw [hm, setAverage_eq, smul_eq_mul]; field_simp
  have hcI : IntegrableOn (fun _ : Vec d => m) U volume := integrableOn_const hU
  have hsq : IntegrableOn (fun x => (h x - m) ^ 2) U volume := by
    have : (fun x => (h x - m) ^ 2) = fun x => h x ^ 2 - 2 * m * h x + m ^ 2 := by
      funext x; ring
    rw [this]
    exact (hh2.sub (hh.const_mul _)).add (integrableOn_const hU)
  have h0 : 0 ≤ ∫ x in U, (h x - m) ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hexp : ∫ x in U, (h x - m) ^ 2 = (∫ x in U, h x ^ 2) - volume.real U * m ^ 2 := by
    have : (fun x => (h x - m) ^ 2) = fun x => h x ^ 2 - 2 * m * h x + m ^ 2 := by
      funext x; ring
    have i1 : IntegrableOn (fun x => h x ^ 2 - 2 * m * h x) U volume := hh2.sub (hh.const_mul _)
    have i2 : IntegrableOn (fun x => 2 * m * h x) U volume := hh.const_mul _
    have i3 : IntegrableOn (fun _ : Vec d => m ^ 2) U volume := integrableOn_const hU
    rw [this, integral_add i1 i3, integral_sub hh2 i2, integral_const_mul, hmV, setIntegral_const,
      smul_eq_mul]
    ring
  rw [setAverage_eq, smul_eq_mul]
  rw [hexp] at h0
  rw [le_inv_mul_iff₀ hV]
  linarith

/-- **`½|e|² ≤ μ(U, e)`**: from `a ≥ I`, Jensen's inequality and the vanishing of the mean of the
gradient of a function of `H¹₀(U)`. -/
theorem le_dirichletEnergy (a : CoefficientField d Λ) {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hU : volume U ≠ ⊤) (e : Vec d) :
    (1 / 2 : ℝ) * euclideanSq e ≤ dirichletEnergy a U e := by
  have hV : 0 < volume.real U := ENNReal.toReal_pos hU0 hU
  refine le_csInf ⟨_, _, _, H01_zero U, rfl⟩ ?_
  rintro E ⟨u, g, hu, rfl⟩
  have hfin : IsFiniteMeasure (volume.restrict U) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hU.lt_top⟩
  have hg : MemLp g 2 (volume.restrict U) := hu.2.1
  have hgi : ∀ i, IntegrableOn (fun x => g x i) U volume := fun i =>
    (MemLp.eval hg i).integrable one_le_two
  have hgi2 : ∀ i, IntegrableOn (fun x => g x i ^ 2) U volume := fun i =>
    (MemLp.eval hg i).integrable_sq
  have hmean : ∀ i, ⨍ x in U, g x i ∂volume = 0 := fun i => by
    rw [setAverage_eq, setIntegral_eq_zero_of_H01 hU hu i, smul_zero]
  -- the components of `e + g`
  have hci : ∀ i, IntegrableOn (fun x => (e + g x) i) U volume := fun i =>
    (integrableOn_const hU : IntegrableOn (fun _ : Vec d => e i) U volume).add (hgi i)
  have hci2 : ∀ i, IntegrableOn (fun x => (e + g x) i ^ 2) U volume := fun i => by
    have : (fun x => (e + g x) i ^ 2) = fun x => e i ^ 2 + 2 * e i * g x i + g x i ^ 2 := by
      funext x; simp only [Pi.add_apply]; ring
    rw [this]
    exact ((integrableOn_const hU : IntegrableOn (fun _ : Vec d => e i ^ 2) U volume).add
      ((hgi i).const_mul _)).add (hgi2 i)
  have hS : IntegrableOn (fun x => euclideanSq (e + g x)) U volume := by
    simp only [euclideanSq, dot, ← sq]
    exact integrable_finsetSum _ fun i _ => hci2 i
  -- the energy density is integrable
  have hgm : AEStronglyMeasurable g (volume.restrict U) := hg.aestronglyMeasurable
  have ham : ∀ i j, AEStronglyMeasurable (fun x => a.field x i j) (volume.restrict U) :=
    fun i j => (a.locally_integrable i j).aestronglyMeasurable.restrict
  have hfm : AEStronglyMeasurable
      (fun x => (1 / 2 : ℝ) * dot (e + g x) ((a x).mulVec (e + g x))) (volume.restrict U) := by
    have hcomp : ∀ i, AEStronglyMeasurable (fun x => (e + g x) i) (volume.restrict U) := fun i =>
      aestronglyMeasurable_const.add ((continuous_apply i).comp_aestronglyMeasurable hgm)
    simp only [dot, Matrix.mulVec, dotProduct]
    exact aestronglyMeasurable_const.mul (Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      (hcomp i).mul (Finset.aestronglyMeasurable_fun_sum _ fun j _ => (ham i j).mul (hcomp j)))
  have hfint : IntegrableOn (fun x => (1 / 2 : ℝ) * dot (e + g x) ((a x).mulVec (e + g x)))
      U volume := by
    refine (hS.const_mul ((1 / 2 : ℝ) * |Λ|)).mono' hfm (Filter.Eventually.of_forall fun x => ?_)
    have h1 := (a.elliptic x (e + g x)).2
    have h0 := energyDensity_nonneg a e (g x) x
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    have : Λ * euclideanSq (e + g x) ≤ |Λ| * euclideanSq (e + g x) :=
      mul_le_mul_of_nonneg_right (le_abs_self Λ) (euclideanSq_nonneg _)
    nlinarith
  -- the chain of inequalities
  have hlow : ⨍ x in U, (1 / 2 : ℝ) * euclideanSq (e + g x) ∂volume ≤
      ⨍ x in U, (1 / 2 : ℝ) * dot (e + g x) ((a x).mulVec (e + g x)) ∂volume := by
    rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul]
    refine mul_le_mul_of_nonneg_left (integral_mono (hS.const_mul _) hfint fun x => ?_)
      (inv_nonneg.mpr hV.le)
    have := (a.elliptic x (e + g x)).1
    simp only
    linarith
  have hjensen : (1 / 2 : ℝ) * euclideanSq e ≤
      ⨍ x in U, (1 / 2 : ℝ) * euclideanSq (e + g x) ∂volume := by
    have hsplit : ⨍ x in U, (1 / 2 : ℝ) * euclideanSq (e + g x) ∂volume =
        (1 / 2 : ℝ) * ∑ i, ⨍ x in U, (e + g x) i ^ 2 ∂volume := by
      simp only [setAverage_eq, smul_eq_mul, euclideanSq, dot, ← sq]
      rw [integral_const_mul, integral_finsetSum _ fun i _ => hci2 i]
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    simp only [euclideanSq, dot, ← sq]
    refine Finset.sum_le_sum fun i _ => ?_
    have hj := sq_setAverage_le hU0 hU (hci i) (hci2 i)
    have hav : ⨍ x in U, (e + g x) i ∂volume = e i := by
      simp only [Pi.add_apply]
      have ic : IntegrableOn (fun _ : Vec d => e i) U volume := integrableOn_const hU
      rw [setAverage_eq, smul_eq_mul, integral_add ic (hgi i), setIntegral_const, smul_eq_mul,
        setIntegral_eq_zero_of_H01 hU hu i, add_zero]
      field_simp
    rw [hav] at hj
    exact hj
  exact hjensen.trans hlow

end QSH
