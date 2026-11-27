import QuantitativeStochasticHomogenization.Ch03.Sec03.Theorem38IIOne

/-!
# Linear functions in the proof of (3.47) for `k = 1`

Auxiliary facts for (3.47) with `k = 1` (Armstrong–Kuusi–Mourrat, proof of Theorem 3.8): the part of
degree one of a polynomial is a linear function `x ↦ v·x`; the coefficient vector `v` and
`‖x ↦ v·x‖_{L̲²(B_1)}` are comparable (equivalence of norms in finite dimension); linear functions
belong to `Ā_1` for every matrix.
-/

open MeasureTheory Filter Set Topology

noncomputable section

namespace QSH

variable {d : ℕ}

theorem exists_dot_eq_homogeneousComponent_one (Q : MvPolynomial (Fin d) ℝ) :
    ∃ v : Vec d, ∀ x, MvPolynomial.eval x (MvPolynomial.homogeneousComponent 1 Q) = dot v x := by
  have h : MvPolynomial.homogeneousComponent 1 Q ∈ MvPolynomial.homogeneousSubmodule (Fin d) ℝ 1 :=
    MvPolynomial.homogeneousComponent_mem 1 Q
  rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.mem_span_range_iff_exists_fun] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun x => ?_⟩
  rw [← hc, map_sum]
  simp [dot]

theorem eval_sum_C_mul_X (v x : Vec d) :
    MvPolynomial.eval x (∑ i, MvPolynomial.C (v i) * MvPolynomial.X i) = dot v x := by
  simp [dot]

theorem dot_smul_right' (v x : Vec d) (t : ℝ) : dot v (t • x) = t ^ 1 * dot v x := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, pow_one, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dot_sub_left (v w x : Vec d) : dot (v - w) x = dot v x - dot w x := by
  simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem totalDegree_sum_C_mul_X_le (v : Vec d) :
    (∑ i, MvPolynomial.C (v i) * MvPolynomial.X i : MvPolynomial (Fin d) ℝ).totalDegree ≤ 1 := by
  refine MvPolynomial.totalDegree_finsetSum_le fun i _ => ?_
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]

/-- Linear functions are `A`-harmonic polynomials of degree one. -/
theorem dot_mem_harmonicPolys (A : Mat d) (v : Vec d) : (fun x => dot v x) ∈ harmonicPolys A 1 := by
  refine ⟨⟨∑ i, MvPolynomial.C (v i) * MvPolynomial.X i, totalDegree_sum_C_mul_X_le v,
    fun x => (eval_sum_C_mul_X v x).symm⟩, fun ρ _ => ?_⟩
  have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) ρ)) :=
    isFiniteMeasure_restrict.mpr (volume_ball_ne_top' 0 ρ)
  refine ⟨memLp_dot_ball v ρ, fun _ => v, fun i => memLp_const _,
    hasWeakGradient_mono (subset_univ _) (hasWeakGradient_dot v), ?_⟩
  exact (hasWeakDivergence_const_field (A.mulVec v)).mono' (subset_univ (ball (0 : Vec d) ρ))

/-- `‖x ↦ v·x‖_{L̲²(B_1)} ≤ C |v|`. -/
theorem exists_scalarRms_dot_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Vec d,
      scalarRms volume (ball (0 : Vec d) 1) (fun x => dot v x) ≤ C * ‖v‖ := by
  have hm : ∀ i : Fin d, MemLp (fun x : Vec d => x i) 2 (volume.restrict (ball (0 : Vec d) 1)) :=
    fun i => by simpa using memLp_eval_ball (MvPolynomial.X i : MvPolynomial (Fin d) ℝ) 1
  refine ⟨∑ i, scalarRms volume (ball (0 : Vec d) 1) (fun x => x i),
    Finset.sum_nonneg fun i _ => scalarRms_nonneg _ _, fun v => ?_⟩
  have h := scalarRms_finset_sum_le Finset.univ (f := fun i (x : Vec d) => x i) hm v
  refine h.trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (scalarRms_nonneg _ _)
  simpa [Real.norm_eq_abs] using norm_le_pi_norm v i

/-- **Equivalence of norms for linear functions**: `|v| ≤ K ‖x ↦ v·x‖_{L̲²(B_1)}`. -/
theorem exists_norm_le_scalarRms_dot :
    ∃ K : ℝ, 0 < K ∧ ∀ v : Vec d,
      ‖v‖ ≤ K * scalarRms volume (ball (0 : Vec d) 1) (fun x => dot v x) := by
  classical
  set μ := volume.restrict (ball (0 : Vec d) 1) with hμ
  let f : Vec d →ₗ[ℝ] Lp ℝ 2 μ :=
    { toFun := fun v => (memLp_dot_ball v 1).toLp _
      map_add' := fun v w => by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ (Eventually.of_forall fun x => ?_)
        simp [dot, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ (Eventually.of_forall fun x => ?_)
        simp [dot, mul_assoc, Finset.mul_sum] }
  have hfv : ∀ v, f v = (memLp_dot_ball v 1).toLp _ := fun v => rfl
  have hb : ball (0 : Vec d) 1 = PDE.euclideanBall 0 1 := ball_zero_eq_pdeEuclideanBall one_pos
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have hae : (fun x => dot v x) =ᵐ[μ] fun _ => (0 : ℝ) := by
      have h1 := MemLp.coeFn_toLp (memLp_dot_ball v 1)
      rw [← hfv, hv] at h1
      exact h1.symm.trans (Lp.coeFn_zero _ _ _)
    have heq : EqOn (fun x => dot v x) (fun _ => (0 : ℝ)) (PDE.euclideanBall 0 1) := by
      refine Measure.eqOn_open_of_ae_eq (μ := (volume : Measure (Vec d))) ?_
        (PDE.isOpen_euclideanBall 0 1) ?_ continuousOn_const
      · rw [← hb]; exact hae
      · exact (by unfold dot; fun_prop : Continuous fun x : Vec d => dot v x).continuousOn
    funext i
    have hmem : (Pi.single i (1 / 2 : ℝ) : Vec d) ∈ PDE.euclideanBall (0 : Vec d) 1 := by
      rw [← hb, mem_ball_zero_iff']
      have hsq : euclideanSq (Pi.single i (1 / 2 : ℝ) : Vec d) = 1 / 4 := by
        unfold euclideanSq dot
        rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
        simp; norm_num
      unfold euclideanNorm
      rw [hsq, Real.sqrt_lt' one_pos]
      norm_num
    have h := heq hmem
    simp only [dot] at h
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)] at h
    simp only [Pi.single_eq_same] at h
    simp only [Pi.zero_apply]
    linarith
  obtain ⟨K, hK0, hK⟩ := f.exists_antilipschitzWith hker
  have hvol : 0 < volume.real (ball (0 : Vec d) 1) := volume_real_ball_pos 0 one_pos
  have hs : 0 < Real.sqrt (volume.real (ball (0 : Vec d) 1)) := Real.sqrt_pos.2 hvol
  refine ⟨K * Real.sqrt (volume.real (ball (0 : Vec d) 1)), mul_pos (NNReal.coe_pos.2 hK0) hs,
    fun v => ?_⟩
  have h1 : ‖v‖ ≤ K * ‖f v‖ := by
    have h := hK.le_mul_dist v 0
    rwa [map_zero, dist_zero_right, dist_zero_right] at h
  have h2 := scalarRms_eq_mul_norm_toLp (memLp_dot_ball v 1)
  have h3 : ‖f v‖ = Real.sqrt (volume.real (ball (0 : Vec d) 1)) *
      scalarRms volume (ball (0 : Vec d) 1) (fun x => dot v x) := by
    rw [h2, ← mul_assoc, ← Real.sqrt_mul hvol.le, mul_inv_cancel₀ hvol.ne', Real.sqrt_one, one_mul,
      hfv]
  rw [h3, ← mul_assoc] at h1
  exact h1

end QSH
