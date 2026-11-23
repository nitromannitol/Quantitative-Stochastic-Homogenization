import QuantitativeStochasticHomogenization.Ch01.Sec02.DirichletEnergyMeasurability

/-!
# The Dirichlet energy over smooth tests

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.2, Lemma 1.1: the Dirichlet energy `μ(U, e)` of (1.7) is the infimum of the energies of
the smooth compactly supported tests of `U`, and it has the structural properties used in
Section 1.3.

* `dirichletEnergy_le_trialEnergy` and `exists_test_trialEnergy_lt`: the tests are admissible in
  (1.7) and approximate its infimum, since every function of `H¹₀(U)` is an `L²` limit of tests
  together with its gradient and the energy is continuous in `L²` (`trialEnergy_le_of_sub`).
* `dirichletEnergy_parallelogram`: `μ(U, e + f) + μ(U, e - f) = 2μ(U, e) + 2μ(U, f)`, the
  quadratic structure (1.10). The book obtains (1.10) from the linearity of the minimizer
  (1.15); here it follows from the parallelogram identity of the energy density, since the tests
  form a vector space.
* `dirichletEnergy_preimage_sub`: `μ(U + y, e)` for the field `a` is `μ(U, e)` for the translated
  field `T_y a`.
* `dirichletEnergy_le_sum_of_partition`: the subadditivity (1.11) for a partition of `W` by
  pairwise disjoint open sets up to a null set, by gluing tests.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- The energy `⨍_U ½ (e + G)·a(e + G)` of a trial gradient `G` in (1.7). -/
def trialEnergy (a : CoefficientField d Λ) (U : Set (Vec d)) (e : Vec d) (G : Vec d → Vec d) :
    ℝ :=
  ⨍ x in U, (1 / 2 : ℝ) * dot (e + G x) ((a x).mulVec (e + G x)) ∂volume

theorem trialEnergy_eq (a : CoefficientField d Λ) (U : Set (Vec d)) (e : Vec d)
    (G : Vec d → Vec d) : trialEnergy a U e G =
      (volume.real U)⁻¹ * ∫ x in U, (1 / 2 : ℝ) * dot (e + G x) ((a x).mulVec (e + G x)) := by
  rw [trialEnergy, setAverage_eq, smul_eq_mul]

theorem trialEnergy_nonneg (a : CoefficientField d Λ) (U : Set (Vec d)) (e : Vec d)
    (G : Vec d → Vec d) : 0 ≤ trialEnergy a U e G :=
  setAverage_nonneg_of_nonneg fun x => energyDensity_nonneg a e (G x) x

theorem bddBelow_dirichletEnergySet (a : CoefficientField d Λ) (U : Set (Vec d)) (e : Vec d) :
    BddBelow {E : ℝ | ∃ (u : Vec d → ℝ) (g : Vec d → Vec d), H01 U u g ∧
      E = ⨍ x in U, (1 / 2 : ℝ) * dot (e + g x) ((a x).mulVec (e + g x)) ∂volume} := by
  refine ⟨0, ?_⟩
  rintro E ⟨u, g, -, rfl⟩
  exact trialEnergy_nonneg a U e g

theorem dirichletEnergy_nonneg (a : CoefficientField d Λ) (U : Set (Vec d)) (e : Vec d) :
    0 ≤ dirichletEnergy a U e :=
  le_csInf ⟨_, _, _, H01_zero U, rfl⟩ fun _ ⟨_, g, _, hE⟩ => hE ▸ trialEnergy_nonneg a U e g

/-! ## Smooth tests -/

private theorem gradient_eq_zero_of_notMem_tsupport {v : Vec d → ℝ} {x : Vec d}
    (hx : x ∉ tsupport v) : gradient v x = 0 := by
  have h : fderiv ℝ v x = 0 := fderiv_of_notMem_tsupport ℝ hx
  funext l
  simp [gradient, coordinateDerivative, h]

namespace IsSpatialTest

variable {U : Set (Vec d)} {v w : Vec d → ℝ}

theorem differentiable (hv : IsSpatialTest U v) : Differentiable ℝ v :=
  hv.1.differentiable (by simp)

theorem continuous_gradient (hv : IsSpatialTest U v) : Continuous (gradient v) :=
  continuous_pi fun _ => (hv.1.continuous_fderiv (by simp)).clm_apply continuous_const

theorem hasCompactSupport_gradient (hv : IsSpatialTest U v) :
    HasCompactSupport (gradient v) :=
  hv.2.1.mono' fun x hx => by
    by_contra hxs
    exact hx (gradient_eq_zero_of_notMem_tsupport hxs)

theorem memLp_gradient (hv : IsSpatialTest U v) (μ : Measure (Vec d)) [IsFiniteMeasureOnCompacts μ] :
    MemLp (gradient v) 2 μ :=
  hv.continuous_gradient.memLp_of_hasCompactSupport hv.hasCompactSupport_gradient

theorem memLp_two (hv : IsSpatialTest U v) (μ : Measure (Vec d)) [IsFiniteMeasureOnCompacts μ] :
    MemLp v 2 μ :=
  hv.1.continuous.memLp_of_hasCompactSupport hv.2.1

theorem add (hv : IsSpatialTest U v) (hw : IsSpatialTest U w) :
    IsSpatialTest U (fun x => v x + w x) :=
  ⟨hv.1.add hw.1, hv.2.1.add hw.2.1, (tsupport_add v w).trans (union_subset hv.2.2 hw.2.2)⟩

theorem const_mul (hv : IsSpatialTest U v) (c : ℝ) : IsSpatialTest U (fun x => c * v x) :=
  ⟨contDiff_const.mul hv.1, hv.2.1.mul_left, tsupport_mul_subset_right.trans hv.2.2⟩

theorem sub (hv : IsSpatialTest U v) (hw : IsSpatialTest U w) :
    IsSpatialTest U (fun x => v x - w x) := by
  have h := hv.add (hw.const_mul (-1))
  simpa [sub_eq_add_neg] using h

theorem gradient_add (hv : IsSpatialTest U v) (hw : IsSpatialTest U w) (x : Vec d) :
    gradient (fun x => v x + w x) x = gradient v x + gradient w x := by
  funext l
  simp only [gradient, coordinateDerivative, Pi.add_apply]
  rw [fderiv_fun_add (hv.differentiable x) (hw.differentiable x)]
  rfl

theorem gradient_const_mul (hv : IsSpatialTest U v) (c : ℝ) (x : Vec d) :
    gradient (fun x => c * v x) x = c • gradient v x := by
  funext l
  simp only [gradient, coordinateDerivative, Pi.smul_apply, smul_eq_mul]
  rw [fderiv_const_mul (hv.differentiable x)]
  rfl

theorem gradient_sub (hv : IsSpatialTest U v) (hw : IsSpatialTest U w) (x : Vec d) :
    gradient (fun x => v x - w x) x = gradient v x - gradient w x := by
  funext l
  simp only [gradient, coordinateDerivative, Pi.sub_apply]
  rw [fderiv_fun_sub (hv.differentiable x) (hw.differentiable x)]
  rfl

theorem finsetSum {ι : Type*} (s : Finset ι) {v : ι → Vec d → ℝ}
    (hv : ∀ k ∈ s, IsSpatialTest U (v k)) : IsSpatialTest U (fun x => ∑ k ∈ s, v k x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isSpatialTest_zero U
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact (hv k (Finset.mem_insert_self k s)).add
      (ih fun k' hk' => hv k' (Finset.mem_insert_of_mem hk'))

theorem gradient_finsetSum {ι : Type*} (s : Finset ι) {v : ι → Vec d → ℝ}
    (hv : ∀ k ∈ s, IsSpatialTest U (v k)) (x : Vec d) :
    gradient (fun x => ∑ k ∈ s, v k x) x = ∑ k ∈ s, gradient (v k) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    funext l
    simp [gradient, coordinateDerivative]
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    have hk' := hv k (Finset.mem_insert_self k s)
    have hs : ∀ k' ∈ s, IsSpatialTest U (v k') := fun k' h => hv k' (Finset.mem_insert_of_mem h)
    rw [hk'.gradient_add (finsetSum s hs), ih hs]

theorem comp_sub (hv : IsSpatialTest U v) (y : Vec d) :
    IsSpatialTest {x | x - y ∈ U} (fun x => v (x - y)) := by
  refine ⟨hv.1.comp (contDiff_id.sub contDiff_const),
    hv.2.1.comp_homeomorph (Homeomorph.subRight y), ?_⟩
  have h : tsupport (fun x => v (x - y)) = (Homeomorph.subRight y) ⁻¹' tsupport v :=
    tsupport_comp_eq_preimage v (Homeomorph.subRight y)
  rw [h]
  intro x hx
  exact hv.2.2 hx

theorem gradient_comp_sub (v : Vec d → ℝ) (y x : Vec d) :
    gradient (fun x => v (x - y)) x = gradient v (x - y) := by
  funext l
  simp only [gradient, coordinateDerivative]
  rw [fderiv_comp_sub y]

/-- Two tests in `U` satisfy `∫_U v ∂ᵢφ = -∫_U ∂ᵢv φ`. -/
theorem integral_mul_coordinateDerivative (hv : IsSpatialTest U v) {φ : Vec d → ℝ}
    (hφ : IsSpatialTest U φ) (i : Fin d) :
    ∫ x in U, v x * coordinateDerivative i φ x =
      -∫ x in U, gradient v x i * φ x := by
  have hvc : Continuous v := hv.1.continuous
  have hφc : Continuous φ := hφ.1.continuous
  have hdv : Continuous fun x => fderiv ℝ v x (unitVector i) :=
    (hv.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφ : Continuous fun x => fderiv ℝ φ x (unitVector i) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have h1 : ∫ x in U, v x * coordinateDerivative i φ x =
      ∫ x, v x * fderiv ℝ φ x (unitVector i) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have hxs : x ∉ tsupport v := fun h => hx (hv.2.2 h)
    rw [image_eq_zero_of_notMem_tsupport hxs, zero_mul]
  have h2 : ∫ x in U, gradient v x i * φ x = ∫ x, fderiv ℝ v x (unitVector i) * φ x := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have hxs : x ∉ tsupport φ := fun h => hx (hφ.2.2 h)
    rw [image_eq_zero_of_notMem_tsupport hxs, mul_zero]
  rw [h1, h2]
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hdv.mul hφc).integrable_of_hasCompactSupport hφ.2.1.mul_left)
    ((hvc.mul hdφ).integrable_of_hasCompactSupport hv.2.1.mul_right)
    ((hvc.mul hφc).integrable_of_hasCompactSupport hv.2.1.mul_right)
    (fun x _ => hv.differentiable x) (fun x _ => hφ.differentiable x)

/-- **A test of `U` lies in `H¹₀(U)`**, with its classical gradient. -/
theorem h01 (hv : IsSpatialTest U v) : H01 U v (gradient v) := by
  refine ⟨hv.memLp_two _, hv.memLp_gradient _, fun i => ⟨?_, ?_, fun φ hφ => ?_⟩,
    fun _ => v, fun _ => hv, by simp, by simp [euclideanSq, dot]⟩
  · exact hv.1.continuous.locallyIntegrable.locallyIntegrableOn U
  · exact ((continuous_apply i).comp hv.continuous_gradient).locallyIntegrable.locallyIntegrableOn U
  · exact hv.integral_mul_coordinateDerivative hφ i

end IsSpatialTest

/-! ## The infimum over tests -/

/-- **The energy of a test bounds the Dirichlet energy from above.** -/
theorem dirichletEnergy_le_trialEnergy (a : CoefficientField d Λ) {U : Set (Vec d)} (e : Vec d)
    {v : Vec d → ℝ} (hv : IsSpatialTest U v) :
    dirichletEnergy a U e ≤ trialEnergy a U e (gradient v) :=
  csInf_le (bddBelow_dirichletEnergySet a U e) ⟨v, gradient v, hv.h01, rfl⟩

theorem integrable_energyDensity (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hU : volume U ≠ ⊤) (e : Vec d) {G : Vec d → Vec d} (hG : MemLp G 2 (volume.restrict U)) :
    Integrable (fun x => (1 / 2 : ℝ) * dot (e + G x) ((a x).mulVec (e + G x)))
      (volume.restrict U) := by
  have := isFiniteMeasure_restrict.mpr hU
  exact (integrable_dot_mulVec a U ((memLp_const e).add hG)).const_mul _

/-- **Continuity of the energy in `L²`**: for `t > 0`,
`E(G') ≤ (1 + t) E(G) + (1 + t⁻¹) ½ Λ ⨍_U |G' - G|²`. -/
theorem trialEnergy_le_of_sub (a : CoefficientField d Λ) {U : Set (Vec d)} (hU : volume U ≠ ⊤)
    (e : Vec d) {G G' : Vec d → Vec d} (hG : MemLp G 2 (volume.restrict U))
    (hG' : MemLp G' 2 (volume.restrict U)) {t : ℝ} (ht : 0 < t) :
    trialEnergy a U e G' ≤ (1 + t) * trialEnergy a U e G +
      (1 + t⁻¹) * ((1 / 2) * Λ * ((volume.real U)⁻¹ *
        ∫ x in U, euclideanSq (G' x - G x))) := by
  have := isFiniteMeasure_restrict.mpr hU
  have hW : Integrable (fun x => euclideanSq (G' x - G x)) (volume.restrict U) :=
    integrable_euclideanSq_of_memLp (hG'.sub hG)
  have hpt : ∀ x, (1 / 2 : ℝ) * dot (e + G' x) ((a x).mulVec (e + G' x)) ≤
      (1 + t) * ((1 / 2 : ℝ) * dot (e + G x) ((a x).mulVec (e + G x))) +
        (1 + t⁻¹) * ((1 / 2) * Λ) * euclideanSq (G' x - G x) := by
    intro x
    have hpos : ∀ v : Vec d, 0 ≤ dot v ((a x).mulVec v) := fun v =>
      (euclideanSq_nonneg v).trans (a.elliptic x v).1
    have h := dot_add_mulVec_add_le (a.symmetric x) hpos ht (e + G x) (G' x - G x)
    have hsum : e + G x + (G' x - G x) = e + G' x := by abel
    rw [hsum] at h
    have hΛW := (a.elliptic x (G' x - G x)).2
    have ht' : 0 ≤ 1 + t⁻¹ := by positivity
    nlinarith
  rw [trialEnergy_eq, trialEnergy_eq]
  have hV : 0 ≤ (volume.real U)⁻¹ := inv_nonneg.mpr measureReal_nonneg
  have i1 : Integrable (fun x => (1 + t) * ((1 / 2 : ℝ) * dot (e + G x) ((a x).mulVec (e + G x))))
      (volume.restrict U) := (integrable_energyDensity a hU e hG).const_mul (1 + t)
  have i2 : Integrable (fun x => (1 + t⁻¹) * ((1 / 2) * Λ) * euclideanSq (G' x - G x))
      (volume.restrict U) := hW.const_mul _
  have hint : ∫ x in U, (1 / 2 : ℝ) * dot (e + G' x) ((a x).mulVec (e + G' x)) ≤
      ∫ x in U, ((1 + t) * ((1 / 2 : ℝ) * dot (e + G x) ((a x).mulVec (e + G x))) +
        (1 + t⁻¹) * ((1 / 2) * Λ) * euclideanSq (G' x - G x)) :=
    integral_mono (integrable_energyDensity a hU e hG') (i1.add i2) hpt
  rw [integral_add i1 i2, integral_const_mul (1 + t),
    integral_const_mul ((1 + t⁻¹) * ((1 / 2) * Λ))] at hint
  calc (volume.real U)⁻¹ * ∫ x in U, (1 / 2 : ℝ) * dot (e + G' x) ((a x).mulVec (e + G' x))
      ≤ (volume.real U)⁻¹ * ((1 + t) * (∫ x in U, (1 / 2 : ℝ) * dot (e + G x)
          ((a x).mulVec (e + G x))) + (1 + t⁻¹) * ((1 / 2) * Λ) *
            ∫ x in U, euclideanSq (G' x - G x)) := mul_le_mul_of_nonneg_left hint hV
    _ = _ := by ring

/-- **The tests approximate the infimum (1.7).** -/
theorem exists_test_trialEnergy_lt (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hU : volume U ≠ ⊤) (e : Vec d) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : Vec d → ℝ, IsSpatialTest U v ∧
      trialEnergy a U e (gradient v) < dirichletEnergy a U e + ε := by
  obtain ⟨E, ⟨u, g, hu, rfl⟩, hE⟩ := exists_lt_of_csInf_lt
    (⟨_, _, _, H01_zero U, rfl⟩ : Set.Nonempty {E : ℝ | ∃ (u : Vec d → ℝ) (g : Vec d → Vec d),
      H01 U u g ∧ E = ⨍ x in U, (1 / 2 : ℝ) * dot (e + g x) ((a x).mulVec (e + g x)) ∂volume})
    (lt_add_of_pos_right (dirichletEnergy a U e) (half_pos hε))
  change trialEnergy a U e g < dirichletEnergy a U e + ε / 2 at hE
  obtain ⟨-, hg, -, v, hv, -, hconv⟩ := hu
  set T := trialEnergy a U e g
  have hT : 0 ≤ T := trialEnergy_nonneg a U e g
  set t : ℝ := ε / (4 * (T + 1)) with ht_def
  have ht : 0 < t := by positivity
  have htT : t * T ≤ ε / 4 := by
    rw [ht_def, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hlim : Tendsto (fun n => (1 + t⁻¹) * ((1 / 2) * Λ * ((volume.real U)⁻¹ *
      ∫ x in U, euclideanSq (gradient (v n) x - g x)))) atTop (𝓝 0) := by
    have := ((hconv.const_mul (volume.real U)⁻¹).const_mul ((1 / 2) * Λ)).const_mul (1 + t⁻¹)
    simpa using this
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 4))).exists
  refine ⟨v n, hv n, ?_⟩
  have h := trialEnergy_le_of_sub a hU e hg ((hv n).memLp_gradient _) ht
  have hexp : (1 + t) * T = T + t * T := by ring
  linarith

/-! ## The parallelogram identity -/

theorem dot_parallelogram (A : Mat d) (p q : Vec d) :
    dot (p + q) (A.mulVec (p + q)) + dot (p - q) (A.mulVec (p - q)) =
      2 * dot p (A.mulVec p) + 2 * dot q (A.mulVec q) := by
  simp only [dot_eq_dotProduct, Matrix.mulVec_add, Matrix.mulVec_sub, dotProduct_add,
    add_dotProduct, dotProduct_sub, sub_dotProduct]
  ring

theorem trialEnergy_parallelogram (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hU : volume U ≠ ⊤) (e f : Vec d) {G H : Vec d → Vec d}
    (hG : MemLp G 2 (volume.restrict U)) (hH : MemLp H 2 (volume.restrict U)) :
    trialEnergy a U (e + f) (fun x => G x + H x) + trialEnergy a U (e - f) (fun x => G x - H x) =
      2 * trialEnergy a U e G + 2 * trialEnergy a U f H := by
  have hGH : MemLp (fun x => G x + H x) 2 (volume.restrict U) := hG.add hH
  have hGH' : MemLp (fun x => G x - H x) 2 (volume.restrict U) := hG.sub hH
  have i1 := integrable_energyDensity a hU (e + f) hGH
  have i2 := integrable_energyDensity a hU (e - f) hGH'
  have i3 := (integrable_energyDensity a hU e hG).const_mul 2
  have i4 := (integrable_energyDensity a hU f hH).const_mul 2
  have key : (∫ x in U, (1 / 2 : ℝ) * dot (e + f + (G x + H x))
        ((a x).mulVec (e + f + (G x + H x)))) +
      ∫ x in U, (1 / 2 : ℝ) * dot (e - f + (G x - H x)) ((a x).mulVec (e - f + (G x - H x))) =
      2 * (∫ x in U, (1 / 2 : ℝ) * dot (e + G x) ((a x).mulVec (e + G x))) +
        2 * ∫ x in U, (1 / 2 : ℝ) * dot (f + H x) ((a x).mulVec (f + H x)) := by
    rw [← integral_add i1 i2, ← integral_const_mul, ← integral_const_mul, ← integral_add i3 i4]
    refine integral_congr_ae ?_
    filter_upwards with x
    have h := dot_parallelogram (a x) (e + G x) (f + H x)
    have e1 : e + G x + (f + H x) = e + f + (G x + H x) := by abel
    have e2 : e + G x - (f + H x) = e - f + (G x - H x) := by abel
    rw [e1, e2] at h
    linarith
  rw [trialEnergy_eq, trialEnergy_eq, trialEnergy_eq, trialEnergy_eq]
  linear_combination (volume.real U)⁻¹ * key

/-- **The parallelogram identity of the Dirichlet energy**, the quadratic structure (1.10). -/
theorem dirichletEnergy_parallelogram (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hU : volume U ≠ ⊤) (e f : Vec d) :
    dirichletEnergy a U (e + f) + dirichletEnergy a U (e - f) =
      2 * dirichletEnergy a U e + 2 * dirichletEnergy a U f := by
  refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_)
    (le_of_forall_pos_lt_add fun ε hε => ?_)
  · obtain ⟨v, hv, hv'⟩ := exists_test_trialEnergy_lt a hU e (by positivity : 0 < ε / 4)
    obtain ⟨w, hw, hw'⟩ := exists_test_trialEnergy_lt a hU f (by positivity : 0 < ε / 4)
    have h1 := dirichletEnergy_le_trialEnergy a (e + f) (hv.add hw)
    have h2 := dirichletEnergy_le_trialEnergy a (e - f) (hv.sub hw)
    have hgv : gradient (fun x => v x + w x) = fun x => gradient v x + gradient w x :=
      funext (hv.gradient_add hw)
    have hgw : gradient (fun x => v x - w x) = fun x => gradient v x - gradient w x :=
      funext (hv.gradient_sub hw)
    rw [hgv] at h1
    rw [hgw] at h2
    have h := trialEnergy_parallelogram a hU e f (hv.memLp_gradient (volume.restrict U))
      (hw.memLp_gradient (volume.restrict U))
    linarith
  · obtain ⟨v, hv, hv'⟩ := exists_test_trialEnergy_lt a hU (e + f)
      (by positivity : 0 < ε / 2)
    obtain ⟨w, hw, hw'⟩ := exists_test_trialEnergy_lt a hU (e - f)
      (by positivity : 0 < ε / 2)
    have hp := (hv.add hw).const_mul (1 / 2)
    have hm := (hv.sub hw).const_mul (1 / 2)
    have h1 := dirichletEnergy_le_trialEnergy a e hp
    have h2 := dirichletEnergy_le_trialEnergy a f hm
    have hgp : gradient (fun x => 1 / 2 * (v x + w x)) =
        fun x => (1 / 2 : ℝ) • (gradient v x + gradient w x) := by
      funext x
      rw [(hv.add hw).gradient_const_mul, hv.gradient_add hw]
    have hgm : gradient (fun x => 1 / 2 * (v x - w x)) =
        fun x => (1 / 2 : ℝ) • (gradient v x - gradient w x) := by
      funext x
      rw [(hv.sub hw).gradient_const_mul, hv.gradient_sub hw]
    rw [hgp] at h1
    rw [hgm] at h2
    have hGv := hv.memLp_gradient (volume.restrict U)
    have hGw := hw.memLp_gradient (volume.restrict U)
    have hGp : MemLp (fun x => (1 / 2 : ℝ) • (gradient v x + gradient w x)) 2
        (volume.restrict U) := (hGv.add hGw).const_smul (1 / 2 : ℝ)
    have hGm : MemLp (fun x => (1 / 2 : ℝ) • (gradient v x - gradient w x)) 2
        (volume.restrict U) := (hGv.sub hGw).const_smul (1 / 2 : ℝ)
    have h := trialEnergy_parallelogram a hU e f hGp hGm
    have hs1 : (fun x => (1 / 2 : ℝ) • (gradient v x + gradient w x) +
        (1 / 2 : ℝ) • (gradient v x - gradient w x)) = gradient v := by
      funext x
      rw [← smul_add, show gradient v x + gradient w x + (gradient v x - gradient w x) =
        (2 : ℝ) • gradient v x by rw [two_smul]; abel, smul_smul]
      norm_num
    have hs2 : (fun x => (1 / 2 : ℝ) • (gradient v x + gradient w x) -
        (1 / 2 : ℝ) • (gradient v x - gradient w x)) = gradient w := by
      funext x
      rw [← smul_sub, show gradient v x + gradient w x - (gradient v x - gradient w x) =
        (2 : ℝ) • gradient w x by rw [two_smul]; abel, smul_smul]
      norm_num
    rw [hs1, hs2] at h
    linarith

/-! ## Translations -/

theorem trialEnergy_preimage_sub (a : CoefficientField d Λ) (U : Set (Vec d)) (y e : Vec d)
    (G : Vec d → Vec d) :
    trialEnergy a {x | x - y ∈ U} e (fun x => G (x - y)) = trialEnergy (translate y a) U e G := by
  have hmp : MeasurePreserving (fun x : Vec d => x - y) volume volume :=
    measurePreserving_sub_right volume y
  have hemb : MeasurableEmbedding (fun x : Vec d => x - y) :=
    (MeasurableEquiv.subRight y).measurableEmbedding
  have hvol : volume.real {x | x - y ∈ U} = volume.real U := by
    simp only [Measure.real]
    rw [show {x | x - y ∈ U} = (fun x : Vec d => x - y) ⁻¹' U from rfl,
      hmp.measure_preimage_emb hemb]
  rw [trialEnergy_eq, trialEnergy_eq, hvol]
  congr 1
  have h := hmp.setIntegral_preimage_emb hemb
    (fun z => (1 / 2 : ℝ) * dot (e + G z) (((translate y a) z).mulVec (e + G z))) U
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards with x
  have hx : (translate y a) (x - y) = a x := by
    change a.field (y + (x - y)) = a.field x
    rw [add_sub_cancel]
  rw [hx]

/-- **Translation covariance of the Dirichlet energy**: `μ(U + y, e)` for `a` is `μ(U, e)` for
`T_y a`. -/
theorem dirichletEnergy_preimage_sub (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hU : volume U ≠ ⊤) (y e : Vec d) :
    dirichletEnergy a {x | x - y ∈ U} e = dirichletEnergy (translate y a) U e := by
  have hV : volume {x | x - y ∈ U} ≠ ⊤ := by
    rw [show {x | x - y ∈ U} = (fun x : Vec d => x - y) ⁻¹' U from rfl,
      (measurePreserving_sub_right volume y).measure_preimage_emb
        (MeasurableEquiv.subRight y).measurableEmbedding]
    exact hU
  refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_)
    (le_of_forall_pos_lt_add fun ε hε => ?_)
  · obtain ⟨v, hv, hv'⟩ := exists_test_trialEnergy_lt (translate y a) hU e hε
    have h := dirichletEnergy_le_trialEnergy a e (hv.comp_sub y)
    have hg : gradient (fun x => v (x - y)) = fun x => gradient v (x - y) :=
      funext (IsSpatialTest.gradient_comp_sub v y)
    rw [hg, trialEnergy_preimage_sub] at h
    linarith
  · obtain ⟨w, hw, hw'⟩ := exists_test_trialEnergy_lt a hV e hε
    have hw2 : IsSpatialTest U (fun x => w (x - -y)) := by
      have h := hw.comp_sub (-y)
      have hset : {x | x - -y ∈ {x | x - y ∈ U}} = U := by
        ext x
        simp
      rwa [hset] at h
    have h := dirichletEnergy_le_trialEnergy (translate y a) e hw2
    have hg : gradient (fun x => w (x - -y)) = fun x => gradient w (x - -y) :=
      funext (IsSpatialTest.gradient_comp_sub w (-y))
    rw [hg, ← trialEnergy_preimage_sub] at h
    have hcancel : (fun x => gradient w (x - y - -y)) = gradient w := by
      funext x
      rw [sub_neg_eq_add, sub_add_cancel]
    rw [hcancel] at h
    linarith

/-! ## Subadditivity -/

/-- **Subadditivity (1.11)** for a partition of `W`, up to a null set, by pairwise disjoint open
sets. -/
theorem dirichletEnergy_le_sum_of_partition (a : CoefficientField d Λ) {ι : Type*} [Fintype ι]
    {W : Set (Vec d)} {Q : ι → Set (Vec d)} (hW : volume W ≠ ⊤)
    (hQo : ∀ k, IsOpen (Q k)) (hdisj : Pairwise (Function.onFun Disjoint Q)) (hsub : ∀ k, Q k ⊆ W)
    (hcover : volume (W \ ⋃ k, Q k) = 0) (e : Vec d) :
    dirichletEnergy a W e ≤
      ∑ k, (volume.real (Q k) / volume.real W) * dirichletEnergy a (Q k) e := by
  classical
  have hQ : ∀ k, volume (Q k) ≠ ⊤ := fun k => ne_top_of_le_ne_top hW (measure_mono (hsub k))
  set c : ℝ := ∑ k, volume.real (Q k) / volume.real W with hc
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun k _ => div_nonneg measureReal_nonneg measureReal_nonneg
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hε : 0 < δ / (c + 1) := by positivity
  choose v hv hv' using fun k => exists_test_trialEnergy_lt a (hQ k) e hε
  have hvW : ∀ k, IsSpatialTest W (v k) := fun k =>
    ⟨(hv k).1, (hv k).2.1, (hv k).2.2.trans (hsub k)⟩
  have hw : IsSpatialTest W (fun x => ∑ k, v k x) :=
    IsSpatialTest.finsetSum Finset.univ fun k _ => hvW k
  have hgrad : ∀ k, ∀ x ∈ Q k, gradient (fun x => ∑ k, v k x) x = gradient (v k) x := by
    intro k x hx
    rw [IsSpatialTest.gradient_finsetSum Finset.univ (fun k _ => hvW k) x,
      Finset.sum_eq_single k]
    · intro j _ hjk
      refine gradient_eq_zero_of_notMem_tsupport fun hxj => ?_
      exact Set.disjoint_left.mp (hdisj hjk) ((hv j).2.2 hxj) hx
    · intro h
      exact absurd (Finset.mem_univ k) h
  have hle := dirichletEnergy_le_trialEnergy a e hw
  set F : Vec d → Vec d := gradient (fun x => ∑ k, v k x)
  have hF : MemLp F 2 (volume.restrict W) := hw.memLp_gradient _
  have hint : ∀ k, IntegrableOn (fun x => (1 / 2 : ℝ) * dot (e + F x) ((a x).mulVec (e + F x)))
      (Q k) volume := fun k =>
    integrable_energyDensity a (hQ k) e ((hw.memLp_gradient _))
  have hae : W =ᵐ[volume] ⋃ k, Q k := by
    refine (ae_eq_set.mpr ⟨hcover, ?_⟩)
    rw [sdiff_eq_empty.mpr (iUnion_subset hsub), measure_empty]
  have hsplit : ∫ x in W, (1 / 2 : ℝ) * dot (e + F x) ((a x).mulVec (e + F x)) =
      ∑ k, ∫ x in Q k, (1 / 2 : ℝ) * dot (e + gradient (v k) x)
        ((a x).mulVec (e + gradient (v k) x)) := by
    rw [setIntegral_congr_set hae, integral_iUnion_fintype (fun k => (hQo k).measurableSet)
      hdisj hint]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine setIntegral_congr_fun (hQo k).measurableSet fun x hx => ?_
    simp only [F, hgrad k x hx]
  rw [trialEnergy_eq, hsplit] at hle
  have hpiece : ∀ k, ∫ x in Q k, (1 / 2 : ℝ) * dot (e + gradient (v k) x)
      ((a x).mulVec (e + gradient (v k) x)) =
      volume.real (Q k) * trialEnergy a (Q k) e (gradient (v k)) := by
    intro k
    rw [trialEnergy_eq]
    rcases eq_or_ne (volume (Q k)) 0 with h0 | h0
    · rw [Measure.restrict_eq_zero.mpr h0, integral_zero_measure, Measure.real, h0]
      simp
    · have hpos : 0 < volume.real (Q k) := ENNReal.toReal_pos h0 (hQ k)
      rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
  simp only [hpiece, Finset.mul_sum] at hle
  calc dirichletEnergy a W e
      ≤ ∑ k, (volume.real W)⁻¹ * (volume.real (Q k) * trialEnergy a (Q k) e (gradient (v k))) :=
        hle
    _ ≤ ∑ k, (volume.real (Q k) / volume.real W) * (dirichletEnergy a (Q k) e + δ / (c + 1)) := by
        refine Finset.sum_le_sum fun k _ => ?_
        calc (volume.real W)⁻¹ * (volume.real (Q k) * trialEnergy a (Q k) e (gradient (v k)))
            = (volume.real (Q k) / volume.real W) * trialEnergy a (Q k) e (gradient (v k)) := by
              ring
          _ ≤ (volume.real (Q k) / volume.real W) * (dirichletEnergy a (Q k) e + δ / (c + 1)) :=
              mul_le_mul_of_nonneg_left (hv' k).le
                (div_nonneg measureReal_nonneg measureReal_nonneg)
    _ = ∑ k, (volume.real (Q k) / volume.real W) * dirichletEnergy a (Q k) e +
          c * (δ / (c + 1)) := by
        rw [hc, Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ ∑ k, (volume.real (Q k) / volume.real W) * dirichletEnergy a (Q k) e + δ := by
        have : c * (δ / (c + 1)) ≤ δ := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
        linarith

end QSH
