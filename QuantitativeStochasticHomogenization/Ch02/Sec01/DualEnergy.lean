import QuantitativeStochasticHomogenization.Ch01.Sec02.Lemma11
import QuantitativeStochasticHomogenization.Ch01.Sec04.FluxAverage
import QuantitativeStochasticHomogenization.Ch03.Sec03.CorrectedAffine
import QuantitativeStochasticHomogenization.Ch03.Sec04.WeakGradientSub

/-!
# The dual subadditive quantity `μ*(U, q)` and the quantity `J(U, p, q)`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.1, (2.1), (2.4), (2.6) and (2.9).

* `IsAHarmonic a U u g`: `u ∈ A(U)` of (0.38) with `u ∈ H¹(U)`: `u ∈ H¹(U)` has weak gradient `g`
  and `a g` is weakly divergence-free in `U`. The suprema (2.3) and (2.9) are over these functions.
* `dualEnergy a U q`: the dual quantity `μ*(U, q)` of (2.1), a supremum over `H¹(U)` of
  `dualTrialEnergy a U q g = ⨍_U (-½ g·ag + q·g)`.
* `dualityDefect a U p q`: `J(U, p, q) = μ(U, p) + μ*(U, q) - p·q` of (2.6);
  `defectTrialEnergy a U p q g = ⨍_U (-½ g·ag - p·ag + q·g)` is the functional of (2.9).
* `dot_le_dirichletEnergy_add_dualEnergy`: the inequality (2.4), `μ(U, p) + μ*(U, q) ≥ p·q`.
* `IsAHarmonic.setIntegral_dot_eq_zero`: for `u ∈ A(U) ∩ H¹(U)` and `w ∈ H¹₀(U)`,
  `∫_U ∇w·a∇u = 0`; conversely `hasWeakDivergence_of_setIntegral_dot_eq_zero`.
* `defectTrialEnergy_add_smul` and `dualTrialEnergy_add_smul`: the expansion of the functionals
  along a line, used for the first variations.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## Definitions -/

/-- `u ∈ A(U)` of (0.38), with `u ∈ H¹(U)`: `u ∈ H¹(U)` has weak gradient `g` and the flux `a g`
is weakly divergence-free in `U`. -/
def IsAHarmonic (a : CoefficientField d Λ) (U : Set (Vec d)) (u : Vec d → ℝ)
    (g : Vec d → Vec d) : Prop :=
  H1 U u g ∧ HasWeakDivergence U (fun x => (a x).mulVec (g x)) (fun _ => 0)

/-- The functional `⨍_U (-½ ∇u·a∇u + q·∇u)` of (2.1), at a gradient `G`. -/
def dualTrialEnergy (a : CoefficientField d Λ) (U : Set (Vec d)) (q : Vec d)
    (G : Vec d → Vec d) : ℝ :=
  ⨍ x in U, (-(1 / 2 : ℝ) * dot (G x) ((a x).mulVec (G x)) + dot q (G x)) ∂volume

/-- **The dual subadditive quantity `μ*(U, q)`**, (2.1): a supremum over `H¹(U)`, with no
condition on the trace. -/
def dualEnergy (a : CoefficientField d Λ) (U : Set (Vec d)) (q : Vec d) : ℝ :=
  sSup {E : ℝ | ∃ (u : Vec d → ℝ) (g : Vec d → Vec d), H1 U u g ∧ E = dualTrialEnergy a U q g}

/-- `(u, g)` is a maximizer of (2.1): `u ∈ H¹(U)` has weak gradient `g` and
`⨍_U (-½ g·ag + q·g) = μ*(U, q)`. -/
def IsDualMaximizer (a : CoefficientField d Λ) (U : Set (Vec d)) (q : Vec d)
    (u : Vec d → ℝ) (g : Vec d → Vec d) : Prop :=
  H1 U u g ∧ dualTrialEnergy a U q g = dualEnergy a U q

/-- The functional `⨍_U (-½ ∇w·a∇w - p·a∇w + q·∇w)` of (2.9), at a gradient `G`. -/
def defectTrialEnergy (a : CoefficientField d Λ) (U : Set (Vec d)) (p q : Vec d)
    (G : Vec d → Vec d) : ℝ :=
  ⨍ x in U, (-(1 / 2 : ℝ) * dot (G x) ((a x).mulVec (G x)) - dot p ((a x).mulVec (G x)) +
    dot q (G x)) ∂volume

/-- **The quantity `J(U, p, q) = μ(U, p) + μ*(U, q) - p·q`**, (2.6). -/
def dualityDefect (a : CoefficientField d Λ) (U : Set (Vec d)) (p q : Vec d) : ℝ :=
  dirichletEnergy a U p + dualEnergy a U q - dot p q

/-- `(v, g)` is a maximizer of (2.9): `v ∈ A(U)` has weak gradient `g` and
`⨍_U (-½ g·ag - p·ag + q·g) = J(U, p, q)`. -/
def IsDefectMaximizer (a : CoefficientField d Λ) (U : Set (Vec d)) (p q : Vec d)
    (v : Vec d → ℝ) (g : Vec d → Vec d) : Prop :=
  IsAHarmonic a U v g ∧ defectTrialEnergy a U p q g = dualityDefect a U p q

/-! ## Elementary facts -/

theorem dot_comm' (x y : Vec d) : dot x y = dot y x := by
  simp only [dot, mul_comm]

theorem dot_zero_left' (y : Vec d) : dot 0 y = 0 := by
  simp [dot]

theorem two_mul_dot_le (x y : Vec d) : 2 * dot x y ≤ euclideanSq x + euclideanSq y := by
  have h : euclideanSq x + euclideanSq y - 2 * dot x y = ∑ i, (x i - y i) ^ 2 := by
    simp only [euclideanSq, dot, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h0 : 0 ≤ ∑ i, (x i - y i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

theorem H01.h1 {U : Set (Vec d)} {u : Vec d → ℝ} {g : Vec d → Vec d} (hu : H01 U u g) :
    H1 U u g :=
  ⟨hu.1, hu.2.1, hu.2.2.1⟩

theorem H1.add {U : Set (Vec d)} {u w : Vec d → ℝ} {g h : Vec d → Vec d} (hu : H1 U u g)
    (hw : H1 U w h) : H1 U (fun x => u x + w x) (fun x => g x + h x) :=
  ⟨hu.1.add hw.1, hu.2.1.add hw.2.1, hasWeakGradient_add hu.2.2 hw.2.2⟩

theorem H1.sub {U : Set (Vec d)} {u w : Vec d → ℝ} {g h : Vec d → Vec d} (hu : H1 U u g)
    (hw : H1 U w h) : H1 U (fun x => u x - w x) (fun x => g x - h x) :=
  ⟨hu.1.sub hw.1, hu.2.1.sub hw.2.1, hasWeakGradient_sub hu.2.2 hw.2.2⟩

theorem H1.add_smul {U : Set (Vec d)} {u w : Vec d → ℝ} {g h : Vec d → Vec d} (hu : H1 U u g)
    (hw : H1 U w h) (t : ℝ) : H1 U (fun x => u x + t * w x) (fun x => g x + t • h x) := by
  refine hu.add ⟨hw.1.const_mul t, hw.2.1.const_smul t, fun i => ?_⟩
  simpa only [Pi.smul_apply, smul_eq_mul] using hasWeakPartialDerivative_const_mul (hw.2.2 i) t

theorem H1.linearCombination {U : Set (Vec d)} {u w : Vec d → ℝ} {g h : Vec d → Vec d}
    (hu : H1 U u g) (hw : H1 U w h) (c₁ c₂ : ℝ) :
    H1 U (fun x => c₁ * u x + c₂ * w x) (fun x => c₁ • g x + c₂ • h x) := by
  have h1 : H1 U (fun x => c₁ * u x) (fun x => c₁ • g x) := by
    refine ⟨hu.1.const_mul c₁, hu.2.1.const_smul c₁, fun i => ?_⟩
    simpa only [Pi.smul_apply, smul_eq_mul] using hasWeakPartialDerivative_const_mul (hu.2.2 i) c₁
  have h2 : H1 U (fun x => c₂ * w x) (fun x => c₂ • h x) := by
    refine ⟨hw.1.const_mul c₂, hw.2.1.const_smul c₂, fun i => ?_⟩
    simpa only [Pi.smul_apply, smul_eq_mul] using hasWeakPartialDerivative_const_mul (hw.2.2 i) c₂
  exact h1.add h2

/-- **The linear function `ℓ_p(x) = p·x` lies in `H¹(U)`** for a bounded `U`, with gradient `p`. -/
theorem H1.linear {U : Set (Vec d)} (hU : Bornology.IsBounded U) (p : Vec d) :
    H1 U (fun x => dot p x) (fun _ => p) := by
  obtain ⟨R, hR⟩ := hU.subset_closedBall 0
  have hfin : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Vec d) R)) :=
    isFiniteMeasure_restrict.mpr measure_closedBall_lt_top.ne
  have hUfin : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr hU.measure_lt_top.ne
  have hcont : Continuous fun x : Vec d => dot p x := by unfold dot; fun_prop
  have hball : MemLp (fun x => dot p x) 2 (volume.restrict (Metric.closedBall (0 : Vec d) R)) := by
    refine MemLp.of_bound hcont.aestronglyMeasurable ((∑ i, |p i|) * R)
      ((ae_restrict_iff' measurableSet_closedBall).mpr (Eventually.of_forall fun x hx => ?_))
    rw [Real.norm_eq_abs]
    have hx : ‖x‖ ≤ R := by simpa using hx
    calc |dot p x| ≤ ∑ i, |p i * x i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |p i| * R := Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm x i).trans hx) (abs_nonneg _)
      _ = (∑ i, |p i|) * R := by rw [Finset.sum_mul]
  exact ⟨hball.mono_measure (Measure.restrict_mono hR le_rfl), memLp_const p,
    hasWeakGradient_mono (subset_univ U) (hasWeakGradient_dot p)⟩

theorem integrable_dot_left_of_memLp {U : Set (Vec d)} (hU : volume U ≠ ⊤) {G : Vec d → Vec d}
    (hG : MemLp G 2 (volume.restrict U)) (q : Vec d) :
    Integrable (fun x => dot q (G x)) (volume.restrict U) := by
  have := isFiniteMeasure_restrict.mpr hU
  simp only [dot]
  exact integrable_finsetSum _ fun i _ => ((hG.eval i).integrable one_le_two).const_mul (q i)

theorem integrable_dot_mulVec_const_left (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hU : volume U ≠ ⊤) {G : Vec d → Vec d} (hG : MemLp G 2 (volume.restrict U)) (p : Vec d) :
    Integrable (fun x => dot p ((a x).mulVec (G x))) (volume.restrict U) := by
  have := isFiniteMeasure_restrict.mpr hU
  exact integrable_dot_mulVec_of_memLp a (memLp_const p) hG

/-- The mean of `q·g` vanishes for the gradient `g` of a function of `H¹₀(U)`. -/
theorem setIntegral_dot_eq_zero_of_H01 {U : Set (Vec d)} (hU : volume U ≠ ⊤) {u : Vec d → ℝ}
    {g : Vec d → Vec d} (hu : H01 U u g) (q : Vec d) : ∫ x in U, dot q (g x) = 0 := by
  have := isFiniteMeasure_restrict.mpr hU
  simp only [dot]
  rw [integral_finsetSum _ fun i _ => ((hu.2.1.eval i).integrable one_le_two).const_mul (q i)]
  exact Finset.sum_eq_zero fun i _ => by
    rw [integral_const_mul, setIntegral_eq_zero_of_H01 hU hu i, mul_zero]

/-! ## `A(U)` and `H¹₀(U)` -/

/-- **`∫_U ∇w·a∇u = 0` for `u ∈ A(U) ∩ H¹(U)` and `w ∈ H¹₀(U)`**, by the density of the tests in
`H¹₀(U)`. -/
theorem IsAHarmonic.setIntegral_dot_eq_zero {a : CoefficientField d Λ} {U : Set (Vec d)}
    {w : Vec d → ℝ} {h : Vec d → Vec d} (hw : IsAHarmonic a U w h) {u : Vec d → ℝ}
    {g : Vec d → Vec d} (hu : H01 U u g) :
    ∫ x in U, dot (g x) ((a x).mulVec (h x)) = 0 := by
  obtain ⟨-, hg2, -, v, hv, -, hgconv⟩ := hu
  have hah : ∀ i, MemLp (fun x => (a x).mulVec (h x) i) 2 (volume.restrict U) := fun i =>
    memLp_coefficient_mulVec_apply a hw.1.2.1 i
  have hdv : ∀ n, MemLp (gradient (v n)) 2 (volume.restrict U) := fun n =>
    (hv n).memLp_gradient _
  have hint : ∀ (G : Vec d → Vec d), MemLp G 2 (volume.restrict U) → ∀ i,
      Integrable (fun x => G x i * (a x).mulVec (h x) i) (volume.restrict U) := fun G hG i =>
    (L2.integrable_inner (𝕜 := ℝ) ((hG.eval i).toLp _) ((hah i).toLp _)).congr (by
      filter_upwards [(hG.eval i).coeFn_toLp, (hah i).coeFn_toLp] with x h1 h2
      rw [h1, h2]
      simp [mul_comm])
  have hsplit : ∀ (G : Vec d → Vec d), MemLp G 2 (volume.restrict U) →
      ∫ x in U, dot (G x) ((a x).mulVec (h x)) =
        ∑ i, ∫ x in U, G x i * (a x).mulVec (h x) i := fun G hG => by
    simp only [dot]
    exact integral_finsetSum _ fun i _ => hint G hG i
  have hzero : ∀ n, ∫ x in U, dot (gradient (v n) x) ((a x).mulVec (h x)) = 0 := by
    intro n
    have e := hw.2.2.2 (v n) (hv n)
    simp only [zero_mul, integral_zero, neg_zero] at e
    rw [← e]
    exact integral_congr_ae (Eventually.of_forall fun x => dot_comm' _ _)
  have hlim : Tendsto (fun n => ∫ x in U, dot (gradient (v n) x) ((a x).mulVec (h x))) atTop
      (𝓝 (∫ x in U, dot (g x) ((a x).mulVec (h x)))) := by
    simp only [fun n => hsplit _ (hdv n), hsplit g hg2]
    refine tendsto_finsetSum _ fun i _ => ?_
    refine tendsto_integral_mul_of_tendsto_integral_sq_sub (hg2.eval i) (hah i)
      (fun n => (hdv n).eval i) ?_
    refine squeeze_zero (fun n => integral_nonneg fun x => sq_nonneg _) (fun n => ?_) hgconv
    refine integral_mono (((hdv n).eval i).sub (hg2.eval i)).integrable_sq
      (integrable_euclideanSq_of_memLp ((hdv n).sub hg2)) fun x => ?_
    exact sq_apply_le_euclideanSq (gradient (v n) x - g x) i
  simp only [hzero] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm

/-- **A field `g ∈ L²(U)` with `∫_U ∇w·ag = 0` for every `w ∈ H¹₀(U)` has `a g` weakly
divergence-free in `U`.** -/
theorem hasWeakDivergence_of_setIntegral_dot_eq_zero (a : CoefficientField d Λ)
    {U : Set (Vec d)} (hU : volume U ≠ ⊤) {g : Vec d → Vec d} (hg : MemLp g 2 (volume.restrict U))
    (h0 : ∀ (w : Vec d → ℝ) (h : Vec d → Vec d), H01 U w h →
      ∫ x in U, dot (h x) ((a x).mulVec (g x)) = 0) :
    HasWeakDivergence U (fun x => (a x).mulVec (g x)) (fun _ => 0) := by
  have := isFiniteMeasure_restrict.mpr hU
  refine ⟨fun i => IntegrableOn.locallyIntegrableOn
    ((memLp_coefficient_mulVec_apply a hg i).integrable one_le_two), locallyIntegrableOn_zero,
    fun φ hφ => ?_⟩
  simp only [zero_mul, integral_zero, neg_zero]
  rw [← h0 φ (gradient φ) hφ.h01]
  exact integral_congr_ae (Eventually.of_forall fun x => dot_comm' _ _)

theorem gradient_eq_zero_of_notMem_tsupport' {φ : Vec d → ℝ} {x : Vec d} (hx : x ∉ tsupport φ) :
    gradient φ x = 0 := by
  funext l
  simp [gradient, coordinateDerivative, fderiv_of_notMem_tsupport ℝ hx]

/-- **Restriction of `A(U)` to a smaller set.** -/
theorem IsAHarmonic.mono {a : CoefficientField d Λ} {U V : Set (Vec d)} (hVU : V ⊆ U)
    {u : Vec d → ℝ} {g : Vec d → Vec d} (hu : IsAHarmonic a U u g) : IsAHarmonic a V u g := by
  refine ⟨hu.1.mono hVU, fun i => (hu.2.1 i).mono_set hVU, hu.2.2.1.mono_set hVU, fun φ hφ => ?_⟩
  have hφU : IsSpatialTest U φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans hVU⟩
  have h1 := hu.2.2.2 φ hφU
  have e : ∀ W : Set (Vec d), tsupport φ ⊆ W →
      ∫ x in W, dot ((a x).mulVec (g x)) (gradient φ x) =
        ∫ x, dot ((a x).mulVec (g x)) (gradient φ x) := fun W hW =>
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [gradient_eq_zero_of_notMem_tsupport' fun h => hx (hW h)]
      simp [dot]
  rw [e V hφ.2.2, ← e U hφU.2.2, h1]
  simp

/-! ## Bounds for `μ*` and the inequality (2.4) -/

theorem dot_add_right_eq (v w₁ w₂ : Vec d) : dot v (w₁ + w₂) = dot v w₁ + dot v w₂ := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem dot_sub_right_eq (v w₁ w₂ : Vec d) : dot v (w₁ - w₂) = dot v w₁ - dot v w₂ := by
  simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem H1_zero (U : Set (Vec d)) : H1 U (fun _ => 0) (fun _ => 0) :=
  (H01_zero U).h1

/-- `⨍_U (-½ g·ag + q·g) ≤ ½|q|²`, from `a ≥ I` and Young's inequality. -/
theorem dualTrialEnergy_le (a : CoefficientField d Λ) {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hU : volume U ≠ ⊤) (q : Vec d) (G : Vec d → Vec d) :
    dualTrialEnergy a U q G ≤ (1 / 2 : ℝ) * euclideanSq q := by
  have hq := euclideanSq_nonneg q
  refine setAverage_le_of_le hU0 hU (by positivity) fun x => ?_
  have h1 := (a.elliptic x (G x)).1
  have h2 := two_mul_dot_le q (G x)
  linarith

theorem bddAbove_dualEnergySet (a : CoefficientField d Λ) {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hU : volume U ≠ ⊤) (q : Vec d) :
    BddAbove {E : ℝ | ∃ (u : Vec d → ℝ) (g : Vec d → Vec d), H1 U u g ∧
      E = dualTrialEnergy a U q g} :=
  ⟨(1 / 2 : ℝ) * euclideanSq q, by
    rintro E ⟨u, g, -, rfl⟩
    exact dualTrialEnergy_le a hU0 hU q g⟩

theorem dualTrialEnergy_le_dualEnergy (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤) (q : Vec d) {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : H1 U u g) : dualTrialEnergy a U q g ≤ dualEnergy a U q :=
  le_csSup (bddAbove_dualEnergySet a hU0 hU q) ⟨u, g, hu, rfl⟩

theorem dualTrialEnergy_zero (a : CoefficientField d Λ) (U : Set (Vec d)) (q : Vec d) :
    dualTrialEnergy a U q (fun _ => 0) = 0 := by
  simp [dualTrialEnergy, dot]

/-- `0 ≤ μ*(U, q)`. -/
theorem dualEnergy_nonneg (a : CoefficientField d Λ) {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hU : volume U ≠ ⊤) (q : Vec d) : 0 ≤ dualEnergy a U q := by
  have h := dualTrialEnergy_le_dualEnergy a hU0 hU q (H1_zero U)
  rwa [dualTrialEnergy_zero] at h

/-- `μ*(U, q) ≤ ½|q|²`. -/
theorem dualEnergy_le (a : CoefficientField d Λ) {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hU : volume U ≠ ⊤) (q : Vec d) : dualEnergy a U q ≤ (1 / 2 : ℝ) * euclideanSq q :=
  csSup_le ⟨_, _, _, H1_zero U, rfl⟩ fun _ ⟨_, g, _, hE⟩ => hE ▸ dualTrialEnergy_le a hU0 hU q g

/-- The value of (2.1) at `ℓ_p + u` for `u ∈ H¹₀(U)` of weak gradient `g`:
`⨍_U (-½ (p + g)·a(p + g) + q·(p + g)) = -⨍_U ½ (p + g)·a(p + g) + q·p`. -/
theorem dualTrialEnergy_add_const_eq (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤) {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : H01 U u g) (p q : Vec d) :
    dualTrialEnergy a U q (fun x => p + g x) = -trialEnergy a U p g + dot q p := by
  have := isFiniteMeasure_restrict.mpr hU
  have hV : 0 < volume.real U := ENNReal.toReal_pos hU0 hU
  have i1 := integrable_energyDensity a hU p hu.2.1
  have i2 := integrable_dot_left_of_memLp hU hu.2.1 q
  have e : (fun x => -(1 / 2 : ℝ) * dot (p + g x) ((a x).mulVec (p + g x)) + dot q (p + g x)) =
      fun x => -((1 / 2 : ℝ) * dot (p + g x) ((a x).mulVec (p + g x))) + dot q (g x) +
        dot q p := by
    funext x
    rw [dot_add_right_eq]
    ring
  simp only [dualTrialEnergy, trialEnergy_eq, setAverage_eq, smul_eq_mul]
  have i1n : Integrable (fun x => -((1 / 2 : ℝ) * dot (p + g x) ((a x).mulVec (p + g x))))
      (volume.restrict U) := i1.neg
  have i12 : Integrable (fun x => -((1 / 2 : ℝ) * dot (p + g x) ((a x).mulVec (p + g x))) +
      dot q (g x)) (volume.restrict U) := i1n.add i2
  rw [e, integral_add i12 (integrable_const _), integral_add i1n i2, integral_neg,
    setIntegral_dot_eq_zero_of_H01 hU hu q, setIntegral_const, smul_eq_mul]
  field_simp
  ring

/-- **(2.4)**: `μ(U, p) + μ*(U, q) ≥ p·q`, by testing (2.1) with the functions `ℓ_p + u`,
`u ∈ H¹₀(U)`. -/
theorem dot_le_dirichletEnergy_add_dualEnergy (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) (hU0 : volume U ≠ 0) (p q : Vec d) :
    dot p q ≤ dirichletEnergy a U p + dualEnergy a U q := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  suffices h : dot p q - dualEnergy a U q ≤ dirichletEnergy a U p by linarith
  refine le_csInf ⟨_, _, _, H01_zero U, rfl⟩ ?_
  rintro E ⟨u, g, hu, rfl⟩
  have hle := dualTrialEnergy_le_dualEnergy a hU0 hU q ((H1.linear hUb p).add hu.h1)
  rw [dualTrialEnergy_add_const_eq a hU0 hU hu p q, dot_comm' q p] at hle
  change _ ≤ trialEnergy a U p g
  linarith

/-! ## Expansion along a line -/

theorem eq_zero_of_forall_mul_le_mul_sq {A B : ℝ} (h : ∀ t : ℝ, B * t ≤ A * t ^ 2) : B = 0 := by
  have hq : ∀ t : ℝ, 0 ≤ A * (t * t) + (-B) * t + 0 := fun t => by
    have := h t
    nlinarith
  have hd := discrim_le_zero hq
  simp only [discrim] at hd
  nlinarith [sq_nonneg B]

theorem integrable_defectIntegrand (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hU : volume U ≠ ⊤) (p q : Vec d) {G : Vec d → Vec d} (hG : MemLp G 2 (volume.restrict U)) :
    Integrable (fun x => -(1 / 2 : ℝ) * dot (G x) ((a x).mulVec (G x)) -
      dot p ((a x).mulVec (G x)) + dot q (G x)) (volume.restrict U) :=
  (((integrable_dot_mulVec a U hG).const_mul _).sub
    (integrable_dot_mulVec_const_left a hU hG p)).add (integrable_dot_left_of_memLp hU hG q)

/-- **The expansion of (2.9) along a line**: for `G, H ∈ L²(U)` and `t ∈ ℝ`,
`∫_U φ(G + tH) = ∫_U φ(G) + t ∫_U (-H·aG - p·aH + q·H) - t² ∫_U ½ H·aH` for the integrand
`φ(V) = -½ V·aV - p·aV + q·V`. -/
theorem integral_defect_add_smul (a : CoefficientField d Λ) {U : Set (Vec d)} (hU : volume U ≠ ⊤)
    (p q : Vec d) {G H : Vec d → Vec d} (hG : MemLp G 2 (volume.restrict U))
    (hH : MemLp H 2 (volume.restrict U)) (t : ℝ) :
    ∫ x in U, (-(1 / 2 : ℝ) * dot (G x + t • H x) ((a x).mulVec (G x + t • H x)) -
        dot p ((a x).mulVec (G x + t • H x)) + dot q (G x + t • H x)) =
      (∫ x in U, (-(1 / 2 : ℝ) * dot (G x) ((a x).mulVec (G x)) - dot p ((a x).mulVec (G x)) +
        dot q (G x))) +
      t * (∫ x in U, (-dot (H x) ((a x).mulVec (G x)) - dot p ((a x).mulVec (H x)) +
        dot q (H x))) -
      t ^ 2 * ∫ x in U, (1 / 2 : ℝ) * dot (H x) ((a x).mulVec (H x)) := by
  have iF0 := integrable_defectIntegrand a hU p q hG
  have iF1 : Integrable (fun x => -dot (H x) ((a x).mulVec (G x)) - dot p ((a x).mulVec (H x)) +
      dot q (H x)) (volume.restrict U) :=
    ((integrable_dot_mulVec_of_memLp a hH hG).neg.sub
      (integrable_dot_mulVec_const_left a hU hH p)).add (integrable_dot_left_of_memLp hU hH q)
  have iF2 := (integrable_dot_mulVec a U hH).const_mul (1 / 2 : ℝ)
  have hpt : ∀ x, -(1 / 2 : ℝ) * dot (G x + t • H x) ((a x).mulVec (G x + t • H x)) -
      dot p ((a x).mulVec (G x + t • H x)) + dot q (G x + t • H x) =
      (-(1 / 2 : ℝ) * dot (G x) ((a x).mulVec (G x)) - dot p ((a x).mulVec (G x)) +
        dot q (G x)) +
      t * (-dot (H x) ((a x).mulVec (G x)) - dot p ((a x).mulVec (H x)) + dot q (H x)) -
      t ^ 2 * ((1 / 2 : ℝ) * dot (H x) ((a x).mulVec (H x))) := by
    intro x
    have hs := dot_mulVec_comm_of_symm (a.symmetric x) (G x) (H x)
    simp only [dot_eq_dotProduct, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
      add_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul] at hs ⊢
    linear_combination (-(1 / 2 : ℝ) * t) * hs
  have iA : Integrable (fun x => (-(1 / 2 : ℝ) * dot (G x) ((a x).mulVec (G x)) -
      dot p ((a x).mulVec (G x)) + dot q (G x)) +
      t * (-dot (H x) ((a x).mulVec (G x)) - dot p ((a x).mulVec (H x)) + dot q (H x)))
      (volume.restrict U) := iF0.add (iF1.const_mul t)
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_sub iA (iF2.const_mul _),
    integral_add iF0 (iF1.const_mul t), integral_const_mul, integral_const_mul]

/-- **The expansion of (2.9) along a line**, normalized. -/
theorem defectTrialEnergy_add_smul (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hU : volume U ≠ ⊤) (p q : Vec d) {G H : Vec d → Vec d} (hG : MemLp G 2 (volume.restrict U))
    (hH : MemLp H 2 (volume.restrict U)) (t : ℝ) :
    defectTrialEnergy a U p q (fun x => G x + t • H x) = defectTrialEnergy a U p q G +
      t * (⨍ x in U, (-dot (H x) ((a x).mulVec (G x)) - dot p ((a x).mulVec (H x)) +
        dot q (H x))) -
      t ^ 2 * ⨍ x in U, (1 / 2 : ℝ) * dot (H x) ((a x).mulVec (H x)) := by
  simp only [defectTrialEnergy, setAverage_eq, smul_eq_mul]
  rw [integral_defect_add_smul a hU p q hG hH t]
  ring

theorem defectTrialEnergy_zero_left (a : CoefficientField d Λ) (U : Set (Vec d)) (q : Vec d)
    (G : Vec d → Vec d) : defectTrialEnergy a U 0 q G = dualTrialEnergy a U q G := by
  simp only [defectTrialEnergy, dualTrialEnergy, dot_zero_left', sub_zero]

/-- A real number `B` with `B t ≤ C t²` for every `t` and `|U| > 0`: the first variations. -/
theorem setIntegral_eq_zero_of_setAverage {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hU : volume U ≠ ⊤) {f : Vec d → ℝ} (h : ⨍ x in U, f x = 0) : ∫ x in U, f x = 0 := by
  have hV : 0 < volume.real U := ENNReal.toReal_pos hU0 hU
  rw [setAverage_eq, smul_eq_mul] at h
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h (inv_ne_zero hV.ne')
  · exact h

/-- **The first variation of (2.1)**: a maximizer `(u, g)` of `μ*(U, q)` satisfies
`∫_U h·ag = ∫_U q·h` for every `w ∈ H¹(U)` of weak gradient `h`. -/
theorem IsDualMaximizer.setIntegral_dot_eq {a : CoefficientField d Λ} {U : Set (Vec d)}
    (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤) {q : Vec d} {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hmax : IsDualMaximizer a U q u g) {w : Vec d → ℝ} {h : Vec d → Vec d} (hw : H1 U w h) :
    ∫ x in U, dot (h x) ((a x).mulVec (g x)) = ∫ x in U, dot q (h x) := by
  have key : ∀ t : ℝ, (⨍ x in U, (-dot (h x) ((a x).mulVec (g x)) - dot 0 ((a x).mulVec (h x)) +
      dot q (h x))) * t ≤ (⨍ x in U, (1 / 2 : ℝ) * dot (h x) ((a x).mulVec (h x))) * t ^ 2 := by
    intro t
    have hle := dualTrialEnergy_le_dualEnergy a hU0 hU q (hmax.1.add_smul hw t)
    rw [← hmax.2, ← defectTrialEnergy_zero_left, ← defectTrialEnergy_zero_left,
      defectTrialEnergy_add_smul a hU 0 q hmax.1.2.1 hw.2.1 t] at hle
    linarith
  have h0 := setIntegral_eq_zero_of_setAverage hU0 hU (eq_zero_of_forall_mul_le_mul_sq key)
  simp only [dot_zero_left', sub_zero] at h0
  have := isFiniteMeasure_restrict.mpr hU
  have j1 : Integrable (fun x => -dot (h x) ((a x).mulVec (g x))) (volume.restrict U) :=
    (integrable_dot_mulVec_of_memLp a hw.2.1 hmax.1.2.1).neg
  rw [integral_add j1 (integrable_dot_left_of_memLp hU hw.2.1 q), integral_neg] at h0
  linarith

/-- **A maximizer of (2.1) lies in `A(U)`.** -/
theorem IsDualMaximizer.isAHarmonic {a : CoefficientField d Λ} {U : Set (Vec d)}
    (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤) {q : Vec d} {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hmax : IsDualMaximizer a U q u g) : IsAHarmonic a U u g :=
  ⟨hmax.1, hasWeakDivergence_of_setIntegral_dot_eq_zero a hU hmax.1.2.1 fun _ _ hw => by
    rw [hmax.setIntegral_dot_eq hU0 hU hw.h1, setIntegral_dot_eq_zero_of_H01 hU hw q]⟩

/-! ## The identity behind Lemma 2.1 -/

/-- **The identity (2.10)**: for `u ∈ H¹₀(U)` of weak gradient `g` and `w ∈ A(U) ∩ H¹(U)` of weak
gradient `h`, the value of (2.1) at `w + ℓ_p + u` is
`⨍_U (-½ h·ah - p·ah + q·h) - ⨍_U ½ (p + g)·a(p + g) + q·p`. -/
theorem dualTrialEnergy_add_eq (a : CoefficientField d Λ) {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hU : volume U ≠ ⊤) {u : Vec d → ℝ} {g : Vec d → Vec d} (hu : H01 U u g) {w : Vec d → ℝ}
    {h : Vec d → Vec d} (hw : IsAHarmonic a U w h) (p q : Vec d) :
    dualTrialEnergy a U q (fun x => h x + (p + g x)) =
      defectTrialEnergy a U p q h - trialEnergy a U p g + dot q p := by
  have := isFiniteMeasure_restrict.mpr hU
  have hV : 0 < volume.real U := ENNReal.toReal_pos hU0 hU
  have hg := hu.2.1
  have hh := hw.1.2.1
  have iF := integrable_defectIntegrand a hU p q hh
  have iE := integrable_energyDensity a hU p hg
  have iq := integrable_dot_left_of_memLp hU hg q
  have ig := integrable_dot_mulVec_of_memLp a hg hh
  have hpt : ∀ x, -(1 / 2 : ℝ) * dot (h x + (p + g x)) ((a x).mulVec (h x + (p + g x))) +
      dot q (h x + (p + g x)) =
      (-(1 / 2 : ℝ) * dot (h x) ((a x).mulVec (h x)) - dot p ((a x).mulVec (h x)) +
        dot q (h x)) - (1 / 2 : ℝ) * dot (p + g x) ((a x).mulVec (p + g x)) +
        dot q (g x) - dot (g x) ((a x).mulVec (h x)) + dot q p := by
    intro x
    have e1 : dot (h x + (p + g x)) ((a x).mulVec (h x + (p + g x))) =
        dot (p + g x) ((a x).mulVec (p + g x)) + 2 * dot (h x) ((a x).mulVec (p + g x)) +
          dot (h x) ((a x).mulVec (h x)) := by
      rw [add_comm (h x)]
      exact dot_add_mulVec_add_eq (a.symmetric x) _ _
    have e2 : dot (h x) ((a x).mulVec (p + g x)) =
        dot p ((a x).mulVec (h x)) + dot (g x) ((a x).mulVec (h x)) := by
      rw [Matrix.mulVec_add, dot_add_right_eq, dot_mulVec_comm_of_symm (a.symmetric x) (h x) p,
        dot_mulVec_comm_of_symm (a.symmetric x) (h x) (g x)]
    rw [e1, e2, dot_add_right_eq, dot_add_right_eq]
    ring
  simp only [dualTrialEnergy, defectTrialEnergy, trialEnergy_eq, setAverage_eq, smul_eq_mul]
  have k1 : Integrable (fun x => (-(1 / 2 : ℝ) * dot (h x) ((a x).mulVec (h x)) -
      dot p ((a x).mulVec (h x)) + dot q (h x)) -
      (1 / 2 : ℝ) * dot (p + g x) ((a x).mulVec (p + g x))) (volume.restrict U) := iF.sub iE
  have k2 : Integrable (fun x => (-(1 / 2 : ℝ) * dot (h x) ((a x).mulVec (h x)) -
      dot p ((a x).mulVec (h x)) + dot q (h x)) -
      (1 / 2 : ℝ) * dot (p + g x) ((a x).mulVec (p + g x)) + dot q (g x)) (volume.restrict U) :=
    k1.add iq
  have k3 : Integrable (fun x => (-(1 / 2 : ℝ) * dot (h x) ((a x).mulVec (h x)) -
      dot p ((a x).mulVec (h x)) + dot q (h x)) -
      (1 / 2 : ℝ) * dot (p + g x) ((a x).mulVec (p + g x)) + dot q (g x) -
      dot (g x) ((a x).mulVec (h x))) (volume.restrict U) := k2.sub ig
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_add k3 (integrable_const _),
    integral_sub k2 ig, integral_add k1 iq, integral_sub iF iE,
    setIntegral_dot_eq_zero_of_H01 hU hu q, hw.setIntegral_dot_eq_zero hu, setIntegral_const,
    smul_eq_mul]
  field_simp
  ring

/-- **The inequality `≤` of (2.9)**: every `w ∈ A(U) ∩ H¹(U)` has
`⨍_U (-½ ∇w·a∇w - p·a∇w + q·∇w) ≤ J(U, p, q)`. -/
theorem defectTrialEnergy_le_dualityDefect (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) (hU0 : volume U ≠ 0) {w : Vec d → ℝ} {h : Vec d → Vec d}
    (hw : IsAHarmonic a U w h) (p q : Vec d) :
    defectTrialEnergy a U p q h ≤ dualityDefect a U p q := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  unfold dualityDefect
  suffices hs : defectTrialEnergy a U p q h - dualEnergy a U q + dot p q ≤ dirichletEnergy a U p by
    linarith
  refine le_csInf ⟨_, _, _, H01_zero U, rfl⟩ ?_
  rintro E ⟨u, g, hu, rfl⟩
  have hle := dualTrialEnergy_le_dualEnergy a hU0 hU q (hw.1.add ((H1.linear hUb p).add hu.h1))
  rw [dualTrialEnergy_add_eq a hU0 hU hu hw p q, dot_comm' q p] at hle
  change _ ≤ trialEnergy a U p g
  linarith

/-- **The maximizer of (2.9) is the maximizer of (2.1) minus the minimizer of (1.7)**: for a
maximizer `(u_*, g_*)` of `μ*(U, q)` and the minimizer `v(·, U, p) = ℓ_p + u` of `μ(U, p)`, of
gradient `p + g`, the function `u_* - ℓ_p - u` is a maximizer of (2.9). -/
theorem IsDualMaximizer.isDefectMaximizer_sub {a : CoefficientField d Λ} {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) (hU0 : volume U ≠ 0) {p q : Vec d} {uN : Vec d → ℝ}
    {gN : Vec d → Vec d} (hN : IsDualMaximizer a U q uN gN) {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hD : IsDirichletMinimizer a U p u g) :
    IsDefectMaximizer a U p q (fun x => uN x - (dot p x + u x)) (fun x => gN x - (p + g x)) := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have := isFiniteMeasure_restrict.mpr hU
  have hH1 := hN.1.sub ((H1.linear hUb p).add hD.1.h1)
  have hA : IsAHarmonic a U (fun x => uN x - (dot p x + u x)) (fun x => gN x - (p + g x)) := by
    refine ⟨hH1, hasWeakDivergence_of_setIntegral_dot_eq_zero a hU hH1.2.1 fun w h hw => ?_⟩
    have e1 := hN.setIntegral_dot_eq hU0 hU hw.h1
    rw [setIntegral_dot_eq_zero_of_H01 hU hw q] at e1
    have e2 := hD.integral_dot_eq_zero hU hw
    have hpg : MemLp (fun x => p + g x) 2 (volume.restrict U) := (memLp_const p).add hD.1.2.1
    have i1 := integrable_dot_mulVec_of_memLp a hw.2.1 hN.1.2.1
    have i2 := integrable_dot_mulVec_of_memLp a hw.2.1 hpg
    have e : (fun x => dot (h x) ((a x).mulVec (gN x - (p + g x)))) =
        fun x => dot (h x) ((a x).mulVec (gN x)) - dot (h x) ((a x).mulVec (p + g x)) := by
      funext x
      rw [Matrix.mulVec_sub, dot_sub_right_eq]
    rw [e, integral_sub i1 i2, e1, e2, sub_zero]
  refine ⟨hA, ?_⟩
  have h := dualTrialEnergy_add_eq a hU0 hU hD.1 hA p q
  have hc : (fun x => gN x - (p + g x) + (p + g x)) = gN := funext fun x => sub_add_cancel _ _
  rw [hc, hN.2, hD.2] at h
  unfold dualityDefect
  rw [dot_comm' q p] at h
  linarith

end QSH
