import QuantitativeStochasticHomogenization.Ch01.Sec02.DirichletEnergyTests
import QuantitativeStochasticHomogenization.Ch01.Sec02.DirichletEnergyMeasurability
import QuantitativeStochasticHomogenization.Ch03.Sec04.CutoffTestIdentity

/-!
# The Dirichlet energy of a cube and a corrected field

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.3 and Lemma 3.16: the energy `μ(U, e)` is compared with a corrected field `G` whose flux
`a G` is weakly divergence-free.

* `setAverage_flux_sub_energy_le_dirichletEnergy`: `⨍_U (e · a G - ½ G · a G) ≤ μ(U, e)`, the dual
  bound: `½ X · a X ≥ X · a G - ½ G · a G` and `∫_U ∇v · a G = 0` for every test `v`.
* `dirichletEnergy_le_of_cutoff`: for `G = e + ∇u` and a cutoff `η` with compact support in `U`,
  `μ(U, e) ≤ (1 + t) ⨍_U ½ G · a G + (1 + t⁻¹) ½ Λ ⨍_U |(1 - η) e + u ∇η|²`, from the trial
  function `η u ∈ H¹₀(U)`.
-/

open MeasureTheory Filter Set

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open Matrix in
theorem dot_mulVec_comm_of_symm {A : Mat d} (hA : A.transpose = A) (v w : Vec d) :
    dot v (A.mulVec w) = dot w (A.mulVec v) := by
  show v ⬝ᵥ (A *ᵥ w) = w ⬝ᵥ (A *ᵥ v)
  rw [Matrix.dotProduct_mulVec, ← hA, Matrix.vecMul_transpose, dotProduct_comm, hA]

theorem dot_mulVec_add_eq (a : CoefficientField d Λ) (x : Vec d) (v w : Vec d) :
    dot v ((a x).mulVec w) = (1 / 2 : ℝ) * (dot (v + w) ((a x).mulVec (v + w)) -
      dot v ((a x).mulVec v) - dot w ((a x).mulVec w)) := by
  have hs := dot_mulVec_comm_of_symm (a.symmetric x) v w
  have h : dot (v + w) ((a x).mulVec (v + w)) = dot v ((a x).mulVec v) +
      dot v ((a x).mulVec w) + dot w ((a x).mulVec v) + dot w ((a x).mulVec w) := by
    simp only [Matrix.mulVec_add, dot, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
    ring
  rw [h, ← hs]
  ring

theorem integrable_dot_mulVec_of_memLp (a : CoefficientField d Λ) {U : Set (Vec d)}
    {v w : Vec d → Vec d} (hv : MemLp v 2 (volume.restrict U)) (hw : MemLp w 2 (volume.restrict U)) :
    Integrable (fun x => dot (v x) ((a x).mulVec (w x))) (volume.restrict U) := by
  have h1 := integrable_dot_mulVec a U (hv.add hw)
  have h2 := integrable_dot_mulVec a U hv
  have h3 := integrable_dot_mulVec a U hw
  refine (((h1.sub h2).sub h3).const_mul (1 / 2 : ℝ)).congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply, Pi.sub_apply]
  exact (dot_mulVec_add_eq a x (v x) (w x)).symm

/-- **The dual bound.** For a field `G ∈ L²(U)` with `a G` weakly divergence-free,
`⨍_U (e · a G - ½ G · a G) ≤ μ(U, e)`. -/
theorem setAverage_flux_sub_energy_le_dirichletEnergy (a : CoefficientField d Λ)
    {U : Set (Vec d)} (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤) (e : Vec d)
    {G : Vec d → Vec d} (hG : MemLp G 2 (volume.restrict U))
    (hq : HasWeakDivergence Set.univ (fun x => (a x).mulVec (G x)) (fun _ => 0)) :
    ⨍ x in U, (dot e ((a x).mulVec (G x)) - (1 / 2 : ℝ) * dot (G x) ((a x).mulVec (G x))) ≤
      dirichletEnergy a U e := by
  have hfin : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hU
  have hV : 0 < volume.real U := ENNReal.toReal_pos hU0 hU
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨v, hv, hlt⟩ := exists_test_trialEnergy_lt a hU e hε
  refine lt_of_le_of_lt ?_ hlt
  have hdv : MemLp (gradient v) 2 (volume.restrict U) := hv.memLp_gradient _
  have he : MemLp (fun _ : Vec d => e) 2 (volume.restrict U) := memLp_const e
  have hX : MemLp (fun x => e + gradient v x) 2 (volume.restrict U) := he.add hdv
  -- the pieces
  have i1 : Integrable (fun x => (1 / 2 : ℝ) *
      dot (e + gradient v x - G x) ((a x).mulVec (e + gradient v x - G x)))
      (volume.restrict U) := (integrable_dot_mulVec a U (hX.sub hG)).const_mul _
  have i23 : Integrable (fun x => dot e ((a x).mulVec (G x)) -
      (1 / 2 : ℝ) * dot (G x) ((a x).mulVec (G x))) (volume.restrict U) :=
    (integrable_dot_mulVec_of_memLp a he hG).sub ((integrable_dot_mulVec a U hG).const_mul _)
  have i4 : Integrable (fun x => dot (gradient v x) ((a x).mulVec (G x)))
      (volume.restrict U) := integrable_dot_mulVec_of_memLp a hdv hG
  have hpt : ∀ x, (1 / 2 : ℝ) * dot (e + gradient v x) ((a x).mulVec (e + gradient v x)) =
      (1 / 2 : ℝ) * dot (e + gradient v x - G x) ((a x).mulVec (e + gradient v x - G x)) +
        (dot e ((a x).mulVec (G x)) - (1 / 2 : ℝ) * dot (G x) ((a x).mulVec (G x))) +
          dot (gradient v x) ((a x).mulVec (G x)) := by
    intro x
    have hs := dot_mulVec_comm_of_symm (a.symmetric x) (e + gradient v x) (G x)
    simp only [Matrix.mulVec_sub, Matrix.mulVec_add, dot, Pi.sub_apply, Pi.add_apply, sub_mul,
      mul_sub, add_mul, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hs ⊢
    linarith
  have hzero : ∫ x in U, dot (gradient v x) ((a x).mulVec (G x)) = 0 := by
    have h := hq.2.2 v ⟨hv.1, hv.2.1, Set.subset_univ _⟩
    simp only [Measure.restrict_univ, zero_mul, integral_zero, neg_zero] at h
    have hsupp : ∀ x ∉ U, dot (gradient v x) ((a x).mulVec (G x)) = 0 := by
      intro x hx
      rw [gradient_eq_zero_of_notMem_tsupport fun h' => hx (hv.2.2 h')]
      simp [dot]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hsupp, ← h]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [dot]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hnn : 0 ≤ ∫ x in U, (1 / 2 : ℝ) *
      dot (e + gradient v x - G x) ((a x).mulVec (e + gradient v x - G x)) :=
    integral_nonneg fun x => mul_nonneg (by norm_num)
      ((euclideanSq_nonneg _).trans (a.elliptic x _).1)
  rw [trialEnergy_eq, setAverage_eq, smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hV.le)
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_add (f := fun x => (1 / 2 : ℝ) *
      dot (e + gradient v x - G x) ((a x).mulVec (e + gradient v x - G x)) +
        (dot e ((a x).mulVec (G x)) - (1 / 2 : ℝ) * dot (G x) ((a x).mulVec (G x))))
      (i1.add i23) i4,
    integral_add i1 i23, hzero]
  linarith

/-- **The upper bound from a cutoff of a corrector.** For `u ∈ H¹(U)` with weak gradient `g` and a
smooth cutoff `0 ≤ η ≤ 1` with compact support in `U`, the trial function `η u` gives
`μ(U, e) ≤ (1 + t) ⨍_U ½ (e + g) · a (e + g) + (1 + t⁻¹) ½ Λ ⨍_U |(1 - η) e + u ∇η|²`. -/
theorem dirichletEnergy_le_of_cutoff (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hU : PDE.IsOpenBoundedConvexDomain U) (hU0 : volume U ≠ 0) (e : Vec d)
    {u : Vec d → ℝ} {g : Vec d → Vec d} (hu : MemLp u 2 (volume.restrict U))
    (hg : MemLp g 2 (volume.restrict U)) (hw : HasWeakGradient U u g) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U)
    (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1) {t : ℝ} (ht : 0 < t) :
    dirichletEnergy a U e ≤
      (1 + t) * (⨍ x in U, (1 / 2 : ℝ) * dot (e + g x) ((a x).mulVec (e + g x))) +
        (1 + t⁻¹) * ((1 / 2) * Λ * ⨍ x in U,
          euclideanSq ((1 - η x) • e + u x • gradient η x)) := by
  have hUt : volume U ≠ ⊤ := (volume_lt_top_of_isBoundedDomain hU.2.1).ne
  have hfin : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUt
  have hgk : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U) := memLp_pi_iff.mp hg
  have h01 := h01_cutoff_mul hU hu hgk hw hη hηc hηU
  set G' : Vec d → Vec d := fun x => η x • g x + u x • gradient η x with hG'
  set G : Vec d → Vec d := fun x => η x • (e + g x) - e with hGdef
  have hle1 : dirichletEnergy a U e ≤ trialEnergy a U e G' :=
    csInf_le (bddBelow_dirichletEnergySet a U e) ⟨_, _, h01, rfl⟩
  have hηb : ∀ x, ‖η x‖ ≤ 1 := fun x => by
    rw [Real.norm_of_nonneg (hη0 x)]
    exact hη1 x
  have hηm : AEStronglyMeasurable η (volume.restrict U) := hη.continuous.aestronglyMeasurable
  have hGm : MemLp G 2 (volume.restrict U) := by
    have h1 : MemLp (fun x => η x • (e + g x)) 2 (volume.restrict U) :=
      ((memLp_const e).add hg).of_le_mul (c := 1)
        (hηm.smul ((memLp_const e).add hg).aestronglyMeasurable)
        (Eventually.of_forall fun x => by
          rw [norm_smul, one_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (hηb x))
    exact h1.sub (memLp_const e)
  have hG'm : MemLp G' 2 (volume.restrict U) := by
    have h := (cutoffH10 hU hu hgk hw hη hηc hηU).toH1Function.gradMemL2
    rw [cutoffH10_grad] at h
    exact memLp_pi_iff.mpr h
  have hsub := trialEnergy_le_of_sub a hUt e hGm hG'm ht
  have hdiff : ∀ x, G' x - G x = (1 - η x) • e + u x • gradient η x := by
    intro x
    simp only [hG', hGdef, smul_add, sub_smul, one_smul]
    abel
  simp only [hdiff] at hsub
  have hG_le : trialEnergy a U e G ≤
      ⨍ x in U, (1 / 2 : ℝ) * dot (e + g x) ((a x).mulVec (e + g x)) := by
    have hVr : 0 < volume.real U := ENNReal.toReal_pos hU0 hUt
    rw [trialEnergy_eq, setAverage_eq, smul_eq_mul]
    refine mul_le_mul_of_nonneg_left (integral_mono (integrable_energyDensity a hUt e hGm)
      (integrable_energyDensity a hUt e hg) fun x => ?_) (inv_nonneg.mpr hVr.le)
    have heq : e + G x = η x • (e + g x) := by simp [hGdef]
    rw [heq, Matrix.mulVec_smul]
    have hq0 : 0 ≤ dot (e + g x) ((a x).mulVec (e + g x)) :=
      (euclideanSq_nonneg _).trans (a.elliptic x _).1
    have hdot : dot (η x • (e + g x)) (η x • (a x).mulVec (e + g x)) =
        η x ^ 2 * dot (e + g x) ((a x).mulVec (e + g x)) := by
      simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hdot]
    have hη2 : η x ^ 2 ≤ 1 := by nlinarith [hη0 x, hη1 x]
    nlinarith
  have hfinal : (1 + t) * trialEnergy a U e G ≤
      (1 + t) * (⨍ x in U, (1 / 2 : ℝ) * dot (e + g x) ((a x).mulVec (e + g x))) :=
    mul_le_mul_of_nonneg_left hG_le (by linarith)
  have havg : (volume.real U)⁻¹ * ∫ x in U, euclideanSq ((1 - η x) • e + u x • gradient η x) =
      ⨍ x in U, euclideanSq ((1 - η x) • e + u x • gradient η x) := by
    rw [setAverage_eq, smul_eq_mul]
  rw [havg] at hsub
  linarith

end QSH
