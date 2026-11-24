import QuantitativeStochasticHomogenization.Ch01.Sec02.DirichletEnergyMeasurability
import QuantitativeStochasticHomogenization.Ch04.Sec04.LocalCoefficientRepresentative

/-!
# `μ(U, p)` is `F(U)`-measurable, (1.29)

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.3, (1.29): for an open set `U` of finite measure (with nonempty complement), the Dirichlet
energy `a ↦ μ(U, p)` is measurable for the local σ-algebra `F(U)` of (0.8). The book observes that
`μ(U, p)` depends only on the restriction of `a` to `U`.

The averages of `a` against the smooth bumps of radius `1/(n+1)` centered at `x` are
`F(U)`-measurable as long as the bump lies in `U`; a continuous gate in `x`, built from the
distance to the complement of `U`, keeps only those, and the upper limit of the gated averages is a
representative of `a` on `U` that is jointly measurable for `Borel ⊗ F(U)` (the argument of
`Ch04/Sec04/LocalCoefficientRepresentative.lean` for balls). Hence `a ↦ ∫_U g a_{ij}` is
`F(U)`-measurable for integrable `g`, the energies of fixed fields are, and so is their countable
infimum `μ(U, p)` (`exists_countable_dirichletEnergy_eq_iInf`).
-/

open MeasureTheory Filter Topology Set

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- A continuous gate which vanishes unless the closed ball of radius `1/(n+1)` around `x` lies in
`U`. -/
def openGate (U : Set (Vec d)) (n : ℕ) (x : Vec d) : ℝ :=
  min 1 (max 0 (((n : ℝ) + 1) * Metric.infDist x Uᶜ - 2))

theorem continuous_openGate (U : Set (Vec d)) (n : ℕ) : Continuous (openGate U n) := by
  unfold openGate
  exact continuous_const.min (continuous_const.max
    ((continuous_const.mul (Metric.continuous_infDist_pt _)).sub continuous_const))

theorem closedBall_subset_of_openGate_ne_zero {U : Set (Vec d)} {n : ℕ} {x : Vec d}
    (h : openGate U n x ≠ 0) : Metric.closedBall x (1 / ((n : ℝ) + 1)) ⊆ U := by
  intro y hy
  by_contra hyU
  have h1 : Metric.infDist x Uᶜ ≤ dist x y := Metric.infDist_le_dist_of_mem hyU
  have h2 : dist x y ≤ 1 / ((n : ℝ) + 1) := by
    rw [dist_comm]
    exact Metric.mem_closedBall.mp hy
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h3 : ((n : ℝ) + 1) * Metric.infDist x Uᶜ - 2 ≤ 0 := by
    have h4 : ((n : ℝ) + 1) * Metric.infDist x Uᶜ ≤ ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (h1.trans h2) hn.le
    rw [mul_one_div_cancel hn.ne'] at h4
    linarith
  apply h
  unfold openGate
  rw [max_eq_left h3, min_eq_right zero_le_one]

theorem openGate_eventually_eq_one {U : Set (Vec d)} (hU : IsOpen U) (hUc : Uᶜ.Nonempty)
    {x : Vec d} (hx : x ∈ U) : ∀ᶠ n : ℕ in atTop, openGate U n x = 1 := by
  have hpos : 0 < Metric.infDist x Uᶜ :=
    (hU.isClosed_compl.notMem_iff_infDist_pos hUc).mp fun h => h hx
  obtain ⟨N, hN⟩ := exists_nat_gt (3 / Metric.infDist x Uᶜ)
  filter_upwards [eventually_ge_atTop N] with n hn
  have h3 : 3 ≤ ((n : ℝ) + 1) * Metric.infDist x Uᶜ := by
    have h1 : 3 / Metric.infDist x Uᶜ < (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
      linarith
    rw [div_lt_iff₀ hpos] at h1
    linarith
  unfold openGate
  rw [max_eq_right (by linarith), min_eq_left (by linarith)]

/-- The gated average of `a_{ij}` against the bump of radius `1/(n+1)` at `x`. -/
def openGatedObservation (U : Set (Vec d)) (i j : Fin d) (n : ℕ) (x : Vec d)
    (a : CoefficientField d Λ) : ℝ :=
  openGate U n x * testIntegral a (averagingTest x n) i j

/-- **The local representative** of `a_{ij}` on the open set `U`. -/
def openRepresentative (U : Set (Vec d)) (i j : Fin d) (a : CoefficientField d Λ) (x : Vec d) :
    ℝ :=
  limsup (fun n => openGatedObservation U i j n x a) atTop

theorem measurable_openGatedObservation (U : Set (Vec d)) (i j : Fin d) (n : ℕ) (x : Vec d) :
    @Measurable (CoefficientField d Λ) ℝ (localSigma U) _ (openGatedObservation U i j n x) := by
  by_cases hx : openGate U n x = 0
  · have : openGatedObservation (Λ := Λ) U i j n x = fun _ => 0 := by
      funext a; simp [openGatedObservation, hx]
    rw [this]
    exact @measurable_const _ _ _ (localSigma U) _
  · exact (measurable_testIntegral_localSigma (averagingTest x n)
      ((tsupport_averagingTest_subset x n).trans
        (closedBall_subset_of_openGate_ne_zero hx)) i j).const_mul _

theorem measurable_openRepresentative (U : Set (Vec d)) (i j : Fin d) :
    @Measurable (Vec d × CoefficientField d Λ) ℝ
      (@Prod.instMeasurableSpace _ _ _ (localSigma U)) _
      (fun p => openRepresentative U i j p.2 p.1) := by
  have h : ∀ n, @Measurable (Vec d × CoefficientField d Λ) ℝ
      (@Prod.instMeasurableSpace _ _ _ (localSigma U)) _
      (Function.uncurry (openGatedObservation U i j n)) := fun n =>
    measurable_uncurry_of_continuous_of_measurable (m := localSigma U)
      (fun a => (continuous_openGate U n).mul (continuous_averagingObservation n i j a))
      (fun x => measurable_openGatedObservation U i j n x)
  exact Measurable.limsup (mδ := @Prod.instMeasurableSpace _ _ _ (localSigma U)) h

theorem openRepresentative_ae_eq {U : Set (Vec d)} (hU : IsOpen U) (hUc : Uᶜ.Nonempty)
    (i j : Fin d) (a : CoefficientField d Λ) :
    ∀ᵐ x ∂(volume.restrict U), openRepresentative U i j a x = a x i j := by
  rw [ae_restrict_iff' hU.measurableSet]
  filter_upwards [ae_tendsto_averagingObservation a i j] with x hx hxU
  unfold openRepresentative
  rw [limsup_congr (f := atTop) (v := fun n => testIntegral a (averagingTest x n) i j)]
  · exact hx.limsup_eq
  · filter_upwards [openGate_eventually_eq_one hU hUc hxU] with n hn
    simp [openGatedObservation, hn]

/-- **Local test integrals against integrable functions are `F(U)`-measurable** for an open set
`U` with nonempty complement. -/
theorem measurable_setIntegral_mul_coefficient_of_isOpen {U : Set (Vec d)} (hU : IsOpen U)
    (hUc : Uᶜ.Nonempty) {g : Vec d → ℝ} (hg : Integrable g (volume.restrict U)) (i j : Fin d) :
    @Measurable (CoefficientField d Λ) ℝ (localSigma U) _
      fun a => ∫ x in U, g x * a x i j := by
  set g' := hg.aestronglyMeasurable.mk g
  have hg'm : StronglyMeasurable g' := hg.aestronglyMeasurable.stronglyMeasurable_mk
  have heq : (fun a : CoefficientField d Λ => ∫ x in U, g x * a x i j) =
      fun a => ∫ x, g' x * openRepresentative U i j a x ∂(volume.restrict U) := by
    funext a
    refine integral_congr_ae ?_
    filter_upwards [hg.aestronglyMeasurable.ae_eq_mk, openRepresentative_ae_eq hU hUc i j a] with
      x hx1 hx2
    rw [hx1, hx2]
  rw [heq]
  let : MeasurableSpace (CoefficientField d Λ) := localSigma U
  have hjoint : Measurable (fun p : Vec d × CoefficientField d Λ =>
      openRepresentative U i j p.2 p.1) := measurable_openRepresentative (Λ := Λ) U i j
  have hf : StronglyMeasurable
      (fun p : Vec d × CoefficientField d Λ => g' p.1 * openRepresentative U i j p.2 p.1) :=
    (hg'm.comp_measurable measurable_fst).mul hjoint.stronglyMeasurable
  exact hf.integral_prod_left'.measurable

private theorem dot_mulVec_eq_sum (A : Mat d) (v : Vec d) :
    dot v (A.mulVec v) = ∑ i, ∑ j, v i * v j * A i j := by
  simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The energy of a fixed field of `L²(U)` is `F(U)`-measurable. -/
theorem measurable_lpTrialEnergy_localSigma {U : Set (Vec d)} (hU : IsOpen U)
    (hUc : Uᶜ.Nonempty) (hUt : volume U ≠ ⊤) (e : Vec d)
    (F : Lp (Vec d) 2 (volume.restrict U)) :
    @Measurable (CoefficientField d Λ) ℝ (localSigma U) _ fun a => lpTrialEnergy a U e F := by
  have := isFiniteMeasure_restrict.mpr hUt
  have hEF : MemLp (fun x => e + F x) 2 (volume.restrict U) := (memLp_const e).add (Lp.memLp F)
  have hg : ∀ i j, Integrable (fun x => (1 / 2 : ℝ) * ((e + F x) i * (e + F x) j))
      (volume.restrict U) := fun i j =>
    ((MemLp.eval hEF i).integrable_mul (MemLp.eval hEF j)).const_mul _
  have hfun : (fun a : CoefficientField d Λ => lpTrialEnergy a U e F) = fun a =>
      (volume.real U)⁻¹ * ∑ i, ∑ j,
        ∫ x in U, (1 / 2 : ℝ) * ((e + F x) i * (e + F x) j) * a x i j := by
    funext a
    unfold lpTrialEnergy
    rw [setAverage_eq, smul_eq_mul]
    congr 1
    have hint : ∀ i j, Integrable (fun x => (1 / 2 : ℝ) * ((e + F x) i * (e + F x) j) * a x i j)
        (volume.restrict U) := by
      intro i j
      refine ((hg i j).norm.const_mul Λ).mono' ((hg i j).aestronglyMeasurable.mul
        (a.aestronglyMeasurable_apply i j _ Measure.restrict_le_self.absolutelyContinuous))
        (Eventually.of_forall fun x => ?_)
      rw [norm_mul, mul_comm Λ]
      exact mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact a.abs_apply_le x i j)
        (norm_nonneg _)
    have h1 : ∀ i, ∑ j, ∫ x in U, (1 / 2 : ℝ) * ((e + F x) i * (e + F x) j) * a x i j =
        ∫ x in U, ∑ j, (1 / 2 : ℝ) * ((e + F x) i * (e + F x) j) * a x i j := fun i =>
      (integral_finsetSum _ fun j _ => hint i j).symm
    rw [Finset.sum_congr rfl fun i _ => h1 i,
      ← integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [dot_mulVec_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hfun]
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _
    fun j _ => measurable_setIntegral_mul_coefficient_of_isOpen hU hUc (hg i j) i j)

/-- **(1.29)**: `μ(U, p)` is `F(U)`-measurable for an open set `U` of finite measure with nonempty
complement. -/
theorem measurable_dirichletEnergy_localSigma {U : Set (Vec d)} (hU : IsOpen U)
    (hUc : Uᶜ.Nonempty) (hUt : volume U ≠ ⊤) (hΛ : 0 ≤ Λ) (e : Vec d) :
    @Measurable (CoefficientField d Λ) ℝ (localSigma U) _ fun a => dirichletEnergy a U e := by
  obtain ⟨T, hTc, hTne, key⟩ := exists_countable_dirichletEnergy_eq_iInf (Λ := Λ) hUt hΛ e
  have : Countable T := hTc.to_subtype
  have : Nonempty T := hTne.to_subtype
  rw [funext key]
  exact Measurable.iInf fun F => measurable_lpTrialEnergy_localSigma hU hUc hUt e F

end QSH
