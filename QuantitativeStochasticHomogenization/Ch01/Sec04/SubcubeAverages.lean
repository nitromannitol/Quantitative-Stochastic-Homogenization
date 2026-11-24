import QuantitativeStochasticHomogenization.Ch01.Sec04.FluxAverage
import QuantitativeStochasticHomogenization.Ch01.Sec03.Proposition18

/-!
# The averages of the gradient and the flux of the minimizer on the subcubes

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.4, Step 2 of the proof of Proposition 1.10. For the minimizer `v = v(·, □_{n+r}, p)`
with gradient `p + g` and the subcubes `z + □_n` of `□_{n+r}`, with `Δ = |Z_n|⁻¹ Σ_z μ(z + □_n, p) -
μ(□_{n+r}, p)` (`subcube_averages_le`):

* `|Z_n|⁻¹ Σ_z |(∇v - p)_{z+□_n}|² ≤ 2Δ`;
* `|Z_n|⁻¹ Σ_z |(a∇v - Ā p)_{z+□_n}|² ≤ 3 |Z_n|⁻¹ Σ_z |(a(z + □_n) - Ā) p|² + 6Λ² Δ` for every
  matrix `Ā`.

The book glues the minimizers `v(·, z + □_n, p)` into `v_n ∈ ℓ_p + H¹₀(□_{n+r})` and uses
`(∇v_n)_{z+□_n} = p`, `(a∇v_n)_{z+□_n} = a(z + □_n)p` by (1.49), Jensen's inequality and (1.36).
Here tests `w_z` of `z + □_n` with `⨍_{z+□_n} |∇w_z - g_z|² ≤ δ` (`g_z` the gradient of the
minimizer of `z + □_n`) are glued into a test `w` of `□_{n+r}`: `(∇w)_{z+□_n} = 0`,
`(a(p + ∇w))_{z+□_n} = a(z + □_n)p + O(δ^{1/2})` by (1.49), the quadratic response (1.13) bounds
`⨍_{□_{n+r}} |g - ∇w|² ≤ 2Δ + Λδ`, and `δ → 0`.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- The vector `(F)_U = ⨍_U F` of the averages of the components of a vector field. -/
def vectorAverage (U : Set (Vec d)) (F : Vec d → Vec d) : Vec d := fun i => ⨍ x in U, F x i

theorem dot_unitVector_left_eq_apply (i : Fin d) (v : Vec d) : dot (unitVector i) v = v i := by
  simp [dot, unitVector, Pi.single_apply]

theorem setAverage_add_of_integrableOn {U : Set (Vec d)} {f h : Vec d → ℝ}
    (hf : IntegrableOn f U) (hh : IntegrableOn h U) :
    ⨍ x in U, (f x + h x) = (⨍ x in U, f x) + ⨍ x in U, h x := by
  simp only [setAverage_eq, smul_eq_mul, integral_add hf hh, mul_add]

/-- Jensen's inequality for vector fields: `|(F)_U|² ≤ ⨍_U |F|²`. -/
theorem euclideanSq_vectorAverage_le {U : Set (Vec d)} (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤)
    {F : Vec d → Vec d} (hF : MemLp F 2 (volume.restrict U)) :
    euclideanSq (vectorAverage U F) ≤ ⨍ x in U, euclideanSq (F x) := by
  have := isFiniteMeasure_restrict.mpr hU
  have hi : ∀ i, (⨍ x in U, F x i) ^ 2 ≤ ⨍ x in U, F x i ^ 2 := fun i =>
    sq_setAverage_le hU0 hU ((hF.eval i).integrable (by norm_num)) (hF.eval i).integrable_sq
  have hsum : ⨍ x in U, euclideanSq (F x) = ∑ i, ⨍ x in U, F x i ^ 2 := by
    simp only [setAverage_eq, smul_eq_mul, ← Finset.mul_sum]
    congr 1
    rw [← integral_finsetSum _ fun i _ => (hF.eval i).integrable_sq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [euclideanSq, dot, pow_two]
  rw [hsum]
  simp only [euclideanSq, dot, vectorAverage]
  exact Finset.sum_le_sum fun i _ => by rw [← pow_two]; exact hi i

/-- `|(aH)_U|² ≤ Λ² ⨍_U |H|²`. -/
theorem euclideanSq_vectorAverage_flux_le (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤) {H : Vec d → Vec d}
    (hH : MemLp H 2 (volume.restrict U)) :
    euclideanSq (vectorAverage U fun x => (a x).mulVec (H x)) ≤
      Λ ^ 2 * ⨍ x in U, euclideanSq (H x) := by
  have := isFiniteMeasure_restrict.mpr hU
  have hF : MemLp (fun x => (a x).mulVec (H x)) 2 (volume.restrict U) :=
    memLp_pi_iff.mpr fun i => memLp_coefficient_mulVec_apply a hH i
  refine (euclideanSq_vectorAverage_le hU0 hU hF).trans ?_
  have hV : 0 ≤ (volume.real U)⁻¹ := inv_nonneg.mpr measureReal_nonneg
  rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul]
  calc (volume.real U)⁻¹ * ∫ x in U, euclideanSq ((a x).mulVec (H x))
      ≤ (volume.real U)⁻¹ * ∫ x in U, Λ ^ 2 * euclideanSq (H x) :=
        mul_le_mul_of_nonneg_left (integral_mono (integrable_euclideanSq_of_memLp hF)
          ((integrable_euclideanSq_of_memLp hH).const_mul _)
          fun x => euclideanSq_coefficient_mulVec_le_sq a x (H x)) hV
    _ = Λ ^ 2 * ((volume.real U)⁻¹ * ∫ x in U, euclideanSq (H x)) := by
        rw [integral_const_mul]
        ring

theorem euclideanSq_add_add_le (x y z : Vec d) :
    euclideanSq (x + y + z) ≤ 3 * (euclideanSq x + euclideanSq y + euclideanSq z) := by
  simp only [euclideanSq, dot, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by
    nlinarith [sq_nonneg (x i - y i), sq_nonneg (y i - z i), sq_nonneg (x i - z i)]

/-- A function of `H¹₀(U)` is approximated in gradient by tests of `U`. -/
theorem H01.exists_test_lt {U : Set (Vec d)} {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : H01 U u g) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : Vec d → ℝ, IsSpatialTest U v ∧ ∫ x in U, euclideanSq (gradient v x - g x) < ε := by
  obtain ⟨-, -, -, v, hv, -, hconv⟩ := hu
  obtain ⟨n, hn⟩ := (hconv.eventually (gt_mem_nhds hε)).exists
  exact ⟨v n, hv n, hn⟩

/-- The average of the gradient of a test of `U` over `U` vanishes. -/
theorem setAverage_gradient_eq_zero {U : Set (Vec d)} {v : Vec d → ℝ} (hv : IsSpatialTest U v)
    (i : Fin d) : ⨍ x in U, gradient v x i = 0 := by
  have h0 : ∀ x, x ∉ U → gradient v x i = 0 := fun x hx => by
    have hxs : x ∉ tsupport v := fun h => hx (hv.2.2 h)
    simp [gradient, coordinateDerivative, fderiv_of_notMem_tsupport ℝ hxs]
  rw [setAverage_eq, smul_eq_mul, setIntegral_eq_integral_of_forall_compl_eq_zero h0]
  change (volume.real U)⁻¹ * ∫ x, coordinateDerivative i v x = 0
  rw [integral_coordinateDerivative_eq_zero hv i, mul_zero]

/-- The average `|Z|⁻¹ Σ_k F(k)` of a quantity over the `3^{dr}` subcubes of the partition. -/
def subcubeMean (r : ℕ) (F : (Fin d → Fin (3 ^ r)) → ℝ) : ℝ :=
  (1 / ((3 : ℝ) ^ r) ^ d) * ∑ k, F k

theorem subcubeMean_add (r : ℕ) (F G : (Fin d → Fin (3 ^ r)) → ℝ) :
    subcubeMean r (fun k => F k + G k) = subcubeMean r F + subcubeMean r G := by
  simp only [subcubeMean, Finset.sum_add_distrib, mul_add]

theorem subcubeMean_sub (r : ℕ) (F G : (Fin d → Fin (3 ^ r)) → ℝ) :
    subcubeMean r (fun k => F k - G k) = subcubeMean r F - subcubeMean r G := by
  simp only [subcubeMean, Finset.sum_sub_distrib, mul_sub]

theorem subcubeMean_const_mul (r : ℕ) (c : ℝ) (F : (Fin d → Fin (3 ^ r)) → ℝ) :
    subcubeMean r (fun k => c * F k) = c * subcubeMean r F := by
  simp only [subcubeMean, ← Finset.mul_sum]
  ring

theorem subcubeMean_const (r : ℕ) (c : ℝ) : subcubeMean (d := d) r (fun _ => c) = c := by
  simp only [subcubeMean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_partitionIndex]
  field_simp

theorem subcubeMean_le (r : ℕ) {F G : (Fin d → Fin (3 ^ r)) → ℝ} (h : ∀ k, F k ≤ G k) :
    subcubeMean r F ≤ subcubeMean r G :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => h k) (by positivity)

theorem subcubeMean_nonneg (r : ℕ) {F : (Fin d → Fin (3 ^ r)) → ℝ} (h : ∀ k, 0 ≤ F k) :
    0 ≤ subcubeMean r F :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => h k)

/-- **The subcube averages with an error `δ`.** -/
theorem subcube_averages_le_add [NeZero d] (a : CoefficientField d Λ) (n r : ℕ) {e : Vec d}
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hmin : IsDirichletMinimizer a (triadicCube d (n + r)) e u g) (Abar : Mat d) {δ : ℝ}
    (hδ : 0 < δ) :
    subcubeMean r (fun k => euclideanSq (vectorAverage (partitionCube n r k) g)) ≤
        2 * (subcubeMean r (fun k => dirichletEnergy a (partitionCube n r k) e) -
          dirichletEnergy a (triadicCube d (n + r)) e) + Λ * δ ∧
      subcubeMean r (fun k => euclideanSq (vectorAverage (partitionCube n r k)
          (fun x => (a x).mulVec (e + g x)) - Abar.mulVec e)) ≤
        3 * subcubeMean r
          (fun k => euclideanSq ((coarseMatrix a (partitionCube n r k) - Abar).mulVec e)) +
        3 * Λ ^ 2 * δ + 3 * Λ ^ 2 * (2 * (subcubeMean r
          (fun k => dirichletEnergy a (partitionCube n r k) e) -
            dirichletEnergy a (triadicCube d (n + r)) e) + Λ * δ) := by
  have hΛ : 0 ≤ Λ := zero_le_one.trans (one_le_of_coefficientField a)
  have hWt : volume (triadicCube d (n + r)) ≠ ⊤ := volume_triadicCube_ne_top d (n + r)
  have : IsFiniteMeasure (volume.restrict (triadicCube d (n + r))) :=
    isFiniteMeasure_restrict.mpr hWt
  have hQt : ∀ k : Fin d → Fin (3 ^ r), volume (partitionCube (d := d) n r k) ≠ ⊤ :=
    volume_partitionCube_ne_top n r
  have hQ0 : ∀ k : Fin d → Fin (3 ^ r), volume (partitionCube (d := d) n r k) ≠ 0 :=
    volume_partitionCube_ne_zero n r
  have hQW : ∀ k : Fin d → Fin (3 ^ r), partitionCube n r k ⊆ triadicCube d (n + r) :=
    partitionCube_subset n r
  have hVn : (0 : ℝ) < ((3 : ℝ) ^ n) ^ d := by positivity
  have hQV : ∀ k : Fin d → Fin (3 ^ r), volume.real (partitionCube (d := d) n r k) =
      ((3 : ℝ) ^ n) ^ d := volumeReal_partitionCube n r
  have hVm : volume.real (triadicCube d (n + r)) = ((3 : ℝ) ^ r) ^ d * ((3 : ℝ) ^ n) ^ d :=
    volumeReal_triadicCube_add n r
  -- the minimizers of the subcubes and tests close to them
  choose uk gk hmk using fun k : Fin d → Fin (3 ^ r) =>
    exists_isDirichletMinimizer a ((isBounded_triadicCube (n + r)).subset (hQW k)) (hQ0 k) e
  choose w hw hwδ using fun k : Fin d → Fin (3 ^ r) =>
    (hmk k).1.exists_test_lt (mul_pos hδ hVn)
  have hwδ' : ∀ k, ⨍ x in partitionCube n r k, euclideanSq (gradient (w k) x - gk k x) ≤ δ := by
    intro k
    rw [setAverage_eq, smul_eq_mul, hQV k, inv_mul_le_iff₀ hVn]
    have := hwδ k
    linarith
  have hwWt : IsSpatialTest (triadicCube d (n + r)) (fun x => ∑ k, w k x) :=
    IsSpatialTest.finsetSum Finset.univ fun k _ => ⟨(hw k).1, (hw k).2.1, (hw k).2.2.trans (hQW k)⟩
  -- the energy of the glued test
  have hEglue : trialEnergy a (triadicCube d (n + r)) e (gradient fun x => ∑ k, w k x) =
      subcubeMean r (fun k => trialEnergy a (partitionCube n r k) e (gradient (w k))) := by
    rw [trialEnergy_eq, setIntegral_triadicCube_eq_sum n r
      (integrable_energyDensity a hWt e (hwWt.memLp_gradient _)), subcubeMean, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [trialEnergy_eq, hQV k, setIntegral_congr_fun (isOpen_partitionCube n r k).measurableSet
      fun x hx => by rw [glue_gradient_eq_of_mem hw hx], hVm]
    field_simp
  have hEk : ∀ k, trialEnergy a (partitionCube n r k) e (gradient (w k)) ≤
      dirichletEnergy a (partitionCube n r k) e + Λ / 2 * δ := by
    intro k
    have h := ((hmk k).quadraticResponse (hQt k) (hw k).h01).2
    have := mul_le_mul_of_nonneg_left (hwδ' k) (by positivity : (0 : ℝ) ≤ Λ / 2)
    linarith
  -- the quadratic response on the cube
  have hgrad : ⨍ x in triadicCube d (n + r), euclideanSq (g x - gradient (fun x => ∑ k, w k x) x) ≤
      2 * (subcubeMean r (fun k => dirichletEnergy a (partitionCube n r k) e) -
        dirichletEnergy a (triadicCube d (n + r)) e) + Λ * δ := by
    have hqr := (hmin.quadraticResponse hWt hwWt.h01).1
    have hsum := subcubeMean_le r hEk
    simp only [subcubeMean_add, subcubeMean_const] at hsum
    have hcomm : ⨍ x in triadicCube d (n + r),
        euclideanSq (g x - gradient (fun x => ∑ k, w k x) x) =
        ⨍ x in triadicCube d (n + r), euclideanSq (gradient (fun x => ∑ k, w k x) x - g x) := by
      congr 1
      funext x
      exact euclideanSq_sub_comm _ _
    rw [hEglue] at hqr
    rw [hcomm]
    linarith
  -- the averages of the gradient
  have hgk : ∀ k, MemLp g 2 (volume.restrict (partitionCube n r k)) := fun k =>
    hmin.1.2.1.mono_measure (Measure.restrict_mono (hQW k) le_rfl)
  have hdist : ∀ k, ⨍ x in partitionCube n r k,
      euclideanSq (g x - gradient (fun x => ∑ k, w k x) x) =
      ⨍ x in partitionCube n r k, euclideanSq (g x - gradient (w k) x) := by
    intro k
    rw [setAverage_eq, setAverage_eq, setIntegral_congr_fun
      (isOpen_partitionCube n r k).measurableSet fun x hx => by
        rw [glue_gradient_eq_of_mem hw hx]]
  have hsumdist : subcubeMean r
      (fun k => ⨍ x in partitionCube n r k, euclideanSq (g x - gradient (w k) x)) =
      ⨍ x in triadicCube d (n + r), euclideanSq (g x - gradient (fun x => ∑ k, w k x) x) := by
    have hI : IntegrableOn (fun x => euclideanSq (g x - gradient (fun x => ∑ k, w k x) x))
        (triadicCube d (n + r)) :=
      integrable_euclideanSq_of_memLp (hmin.1.2.1.sub (hwWt.memLp_gradient _))
    rw [subcubeMean, Finset.sum_congr rfl fun k _ => (hdist k).symm, setAverage_eq, smul_eq_mul,
      setIntegral_triadicCube_eq_sum n r hI, Finset.mul_sum, Finset.mul_sum, hVm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [setAverage_eq, smul_eq_mul, hQV k]
    field_simp
  have hG : ∀ k, euclideanSq (vectorAverage (partitionCube n r k) g) ≤
      ⨍ x in partitionCube n r k, euclideanSq (g x - gradient (w k) x) := by
    intro k
    have : IsFiniteMeasure (volume.restrict (partitionCube (d := d) n r k)) :=
      isFiniteMeasure_restrict.mpr (hQt k)
    have hv : vectorAverage (partitionCube n r k) g =
        vectorAverage (partitionCube n r k) fun x => g x - gradient (w k) x := by
      funext i
      simp only [vectorAverage, Pi.sub_apply]
      have hi1 : IntegrableOn (fun x => g x i) (partitionCube n r k) :=
        ((hgk k).eval i).integrable (by norm_num)
      have hi2 : IntegrableOn (fun x => -gradient (w k) x i) (partitionCube n r k) :=
        ((((hw k).memLp_gradient (volume.restrict (partitionCube n r k))).eval i).integrable
          (by norm_num)).neg
      have h12 := setAverage_add_of_integrableOn hi1 hi2
      simp only [← sub_eq_add_neg] at h12
      have h0 := setAverage_gradient_eq_zero (hw k) i
      have hneg : ⨍ x in partitionCube n r k, -gradient (w k) x i = 0 := by
        rw [setAverage_eq, smul_eq_mul] at h0 ⊢
        rw [integral_neg, mul_neg, h0, neg_zero]
      rw [h12, hneg, add_zero]
    rw [hv]
    exact euclideanSq_vectorAverage_le (hQ0 k) (hQt k)
      ((hgk k).sub ((hw k).memLp_gradient _))
  refine ⟨?_, ?_⟩
  · calc subcubeMean r (fun k => euclideanSq (vectorAverage (partitionCube n r k) g))
        ≤ subcubeMean r
            (fun k => ⨍ x in partitionCube n r k, euclideanSq (g x - gradient (w k) x)) :=
          subcubeMean_le r hG
      _ ≤ _ := by rw [hsumdist]; exact hgrad
  · -- the averages of the flux
    have hflux : ∀ k, vectorAverage (partitionCube n r k) (fun x => (a x).mulVec (e + g x)) -
        Abar.mulVec e =
        (coarseMatrix a (partitionCube n r k) - Abar).mulVec e +
          vectorAverage (partitionCube n r k)
            (fun x => (a x).mulVec (gradient (w k) x - gk k x)) +
          vectorAverage (partitionCube n r k) (fun x => (a x).mulVec (g x - gradient (w k) x)) := by
      intro k
      funext i
      have : IsFiniteMeasure (volume.restrict (partitionCube (d := d) n r k)) :=
        isFiniteMeasure_restrict.mpr (hQt k)
      have hgkk := (hmk k).1.2.1
      have hwk := (hw k).memLp_gradient (volume.restrict (partitionCube n r k))
      have h1 : IntegrableOn (fun x => (a x).mulVec (e + gk k x) i) (partitionCube n r k) :=
        (memLp_coefficient_mulVec_apply a ((memLp_const e).add hgkk) i).integrable (by norm_num)
      have h2 : IntegrableOn (fun x => (a x).mulVec (gradient (w k) x - gk k x) i)
          (partitionCube n r k) :=
        (memLp_coefficient_mulVec_apply a (hwk.sub hgkk) i).integrable (by norm_num)
      have h3 : IntegrableOn (fun x => (a x).mulVec (g x - gradient (w k) x) i)
          (partitionCube n r k) :=
        (memLp_coefficient_mulVec_apply a ((hgk k).sub hwk) i).integrable (by norm_num)
      have h12 : IntegrableOn (fun x => (a x).mulVec (e + gk k x) i +
          (a x).mulVec (gradient (w k) x - gk k x) i) (partitionCube n r k) := h1.add h2
      have hpt : ∀ x, (a x).mulVec (e + g x) i = ((a x).mulVec (e + gk k x) i +
          (a x).mulVec (gradient (w k) x - gk k x) i) + (a x).mulVec (g x - gradient (w k) x) i := by
        intro x
        have hsum : e + g x = (e + gk k x) + (gradient (w k) x - gk k x) +
            (g x - gradient (w k) x) := by abel
        rw [hsum, Matrix.mulVec_add, Matrix.mulVec_add, Pi.add_apply, Pi.add_apply]
      have hsplit : ⨍ x in partitionCube n r k, (a x).mulVec (e + g x) i =
          ((⨍ x in partitionCube n r k, (a x).mulVec (e + gk k x) i) +
            ⨍ x in partitionCube n r k, (a x).mulVec (gradient (w k) x - gk k x) i) +
          ⨍ x in partitionCube n r k, (a x).mulVec (g x - gradient (w k) x) i := by
        simp_rw [hpt]
        rw [setAverage_add_of_integrableOn h12 h3, setAverage_add_of_integrableOn h1 h2]
      have h149 := (hmk k).setAverage_flux_eq (hQ0 k) (hQt k) (unitVector i)
      simp only [dot_unitVector_left_eq_apply] at h149
      simp only [vectorAverage, Pi.sub_apply, Pi.add_apply, Matrix.sub_mulVec]
      rw [hsplit, h149]
      ring
    have hX : ∀ k, euclideanSq (vectorAverage (partitionCube n r k)
        (fun x => (a x).mulVec (gradient (w k) x - gk k x))) ≤ Λ ^ 2 * δ := fun k =>
      (euclideanSq_vectorAverage_flux_le a (hQ0 k) (hQt k)
        (((hw k).memLp_gradient _).sub (hmk k).1.2.1)).trans
        (mul_le_mul_of_nonneg_left (hwδ' k) (sq_nonneg _))
    have hY : ∀ k, euclideanSq (vectorAverage (partitionCube n r k)
        (fun x => (a x).mulVec (g x - gradient (w k) x))) ≤
        Λ ^ 2 * ⨍ x in partitionCube n r k, euclideanSq (g x - gradient (w k) x) := fun k =>
      euclideanSq_vectorAverage_flux_le a (hQ0 k) (hQt k) ((hgk k).sub ((hw k).memLp_gradient _))
    have hterm : ∀ k, euclideanSq (vectorAverage (partitionCube n r k)
        (fun x => (a x).mulVec (e + g x)) - Abar.mulVec e) ≤
        3 * euclideanSq ((coarseMatrix a (partitionCube n r k) - Abar).mulVec e) +
          3 * Λ ^ 2 * δ +
          3 * Λ ^ 2 * ⨍ x in partitionCube n r k, euclideanSq (g x - gradient (w k) x) := by
      intro k
      rw [hflux k]
      have := euclideanSq_add_add_le ((coarseMatrix a (partitionCube n r k) - Abar).mulVec e)
        (vectorAverage (partitionCube n r k) (fun x => (a x).mulVec (gradient (w k) x - gk k x)))
        (vectorAverage (partitionCube n r k) (fun x => (a x).mulVec (g x - gradient (w k) x)))
      linarith [hX k, hY k]
    have hm := subcubeMean_le r hterm
    simp only [subcubeMean_add, subcubeMean_const_mul, subcubeMean_const] at hm
    rw [hsumdist] at hm
    have h3 : 0 ≤ 3 * Λ ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hgrad h3
    linarith

/-- **The subcube averages of the gradient and the flux of the minimizer**: with
`Δ = |Z_n|⁻¹ Σ_z μ(z + □_n, p) - μ(□_{n+r}, p)`, `|Z_n|⁻¹ Σ_z |(g)_{z+□_n}|² ≤ 2Δ` and
`|Z_n|⁻¹ Σ_z |(a(p + g))_{z+□_n} - Āp|² ≤ 3 |Z_n|⁻¹ Σ_z |(a(z + □_n) - Ā)p|² + 6Λ²Δ`. -/
theorem subcube_averages_le [NeZero d] (a : CoefficientField d Λ) (n r : ℕ) {e : Vec d}
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hmin : IsDirichletMinimizer a (triadicCube d (n + r)) e u g) (Abar : Mat d) :
    subcubeMean r (fun k => euclideanSq (vectorAverage (partitionCube n r k) g)) ≤
        2 * (subcubeMean r (fun k => dirichletEnergy a (partitionCube n r k) e) -
          dirichletEnergy a (triadicCube d (n + r)) e) ∧
      subcubeMean r (fun k => euclideanSq (vectorAverage (partitionCube n r k)
          (fun x => (a x).mulVec (e + g x)) - Abar.mulVec e)) ≤
        3 * subcubeMean r
          (fun k => euclideanSq ((coarseMatrix a (partitionCube n r k) - Abar).mulVec e)) +
        6 * Λ ^ 2 * (subcubeMean r (fun k => dirichletEnergy a (partitionCube n r k) e) -
          dirichletEnergy a (triadicCube d (n + r)) e) := by
  have hΛ : 0 ≤ Λ := zero_le_one.trans (one_le_of_coefficientField a)
  refine ⟨le_of_forall_pos_le_add fun ε hε => ?_, le_of_forall_pos_le_add fun ε hε => ?_⟩
  · have hδ : 0 < ε / (Λ + 1) := by positivity
    have h := (subcube_averages_le_add a n r hmin Abar hδ).1
    have : Λ * (ε / (Λ + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  · have hpos : 0 < 3 * Λ ^ 2 + 3 * Λ ^ 3 + 1 := by positivity
    have hδ : 0 < ε / (3 * Λ ^ 2 + 3 * Λ ^ 3 + 1) := by positivity
    have h := (subcube_averages_le_add a n r hmin Abar hδ).2
    have : 3 * Λ ^ 2 * (ε / (3 * Λ ^ 2 + 3 * Λ ^ 3 + 1)) +
        3 * Λ ^ 2 * (Λ * (ε / (3 * Λ ^ 2 + 3 * Λ ^ 3 + 1))) ≤ ε := by
      rw [show 3 * Λ ^ 2 * (ε / (3 * Λ ^ 2 + 3 * Λ ^ 3 + 1)) +
          3 * Λ ^ 2 * (Λ * (ε / (3 * Λ ^ 2 + 3 * Λ ^ 3 + 1))) =
          (3 * Λ ^ 2 + 3 * Λ ^ 3) * ε / (3 * Λ ^ 2 + 3 * Λ ^ 3 + 1) by ring,
        div_le_iff₀ hpos]
      nlinarith
    linarith

end QSH
