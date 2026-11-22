import QuantitativeStochasticHomogenization.Ch03.Sec03.EllipsoidCutoff
import QuantitativeStochasticHomogenization.Ch03.Sec03.EllipticRepresentative
import QuantitativeStochasticHomogenization.Ch03.Sec03.KernelSmoothing

/-!
# Smooth functions under the change of variables `x = M y`

For an invertible `M` and `B = M Mᵀ`, a smooth function `f` satisfies
`∑ᵢⱼ Bᵢⱼ ∂ⱼ∂ᵢ (f ∘ M⁻¹)(x) = Δf(M⁻¹ x)`. Hence a smooth function harmonic on the ball `B_b` gives,
after composition with `M⁻¹`, a function in `H¹(E_b)` that is weakly `B`-harmonic on the ellipsoid
`E_b = M B_b`; and the second derivatives of `χ ∘ M⁻¹` are bounded by those of `χ`.
-/

open MeasureTheory Filter Set

noncomputable section

namespace QSH

variable {d : ℕ}

theorem coordinateDerivative_sum_const_mul {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    {G : ι → Vec d → ℝ} (hG : ∀ l, Differentiable ℝ (G l)) (j : Fin d) (x : Vec d) :
    coordinateDerivative j (fun y => ∑ l ∈ s, c l * G l y) x =
      ∑ l ∈ s, c l * coordinateDerivative j (G l) x := by
  unfold coordinateDerivative
  rw [fderiv_fun_sum fun l _ => ((hG l) x).const_mul (c l)]
  simp only [FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [fderiv_const_mul ((hG l) x) (c l)]
  rfl

theorem contDiff_coordinateDerivative {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative i f) :=
  PDE.contDiff_euclideanCoordDeriv hf i

/-- The second-order chain rule for `y ↦ f (N y)`. -/
theorem coordinateDerivative_coordinateDerivative_comp_mulVec {N : Mat d} (hN : N.det ≠ 0)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i j : Fin d) (x : Vec d) :
    coordinateDerivative j (coordinateDerivative i (fun y => f (N.mulVec y))) x =
      ∑ l, ∑ k, N l i * N k j *
        coordinateDerivative k (coordinateDerivative l f) (N.mulVec x) := by
  have h1 : coordinateDerivative i (fun y => f (N.mulVec y)) =
      fun y => ∑ l, N l i * coordinateDerivative l f (N.mulVec y) := by
    funext y
    exact coordinateDerivative_comp_mulVec hN f i y
  rw [h1]
  have hd : ∀ l, Differentiable ℝ (fun y => coordinateDerivative l f (N.mulVec y)) := fun l =>
    ((contDiff_coordinateDerivative hf l).differentiable (by simp)).comp
      (matrixCLE N hN).differentiable
  rw [coordinateDerivative_sum_const_mul _ _ hd]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [coordinateDerivative_comp_mulVec hN, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem inv_mul_mul_transpose_mul {M : Mat d} (hdet : M.det ≠ 0) :
    M⁻¹ * (M * M.transpose) * M⁻¹.transpose = 1 := by
  have hu : IsUnit M.det := isUnit_iff_ne_zero.2 hdet
  calc M⁻¹ * (M * M.transpose) * M⁻¹.transpose = (M⁻¹ * M) * (M.transpose * M⁻¹.transpose) := by
        simp only [Matrix.mul_assoc]
    _ = 1 * (M⁻¹ * M).transpose := by rw [Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hu]
    _ = 1 := by rw [Matrix.nonsing_inv_mul _ hu, Matrix.transpose_one, Matrix.one_mul]

theorem sum4_comm (X : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ i, ∑ j, ∑ l, ∑ k, X i j l k = ∑ l, ∑ k, ∑ i, ∑ j, X i j l k := by
  calc ∑ i, ∑ j, ∑ l, ∑ k, X i j l k = ∑ i, ∑ l, ∑ j, ∑ k, X i j l k :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ l, ∑ i, ∑ j, ∑ k, X i j l k := Finset.sum_comm
    _ = ∑ l, ∑ i, ∑ k, ∑ j, X i j l k :=
        Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ l, ∑ k, ∑ i, ∑ j, X i j l k := Finset.sum_congr rfl fun l _ => Finset.sum_comm

/-- `∑ᵢⱼ (M Mᵀ)ᵢⱼ ∂ⱼ∂ᵢ (f ∘ M⁻¹)(x) = Δf(M⁻¹ x)`. -/
theorem sum_mul_secondDeriv_comp_inv {M : Mat d} (hdet : M.det ≠ 0) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec d) :
    ∑ i, ∑ j, (M * M.transpose) i j *
        coordinateDerivative j (coordinateDerivative i (fun y => f (M⁻¹.mulVec y))) x =
      PDE.euclideanCoordLaplacian f (M⁻¹.mulVec x) := by
  have hN : (M⁻¹).det ≠ 0 :=
    (Matrix.isUnit_nonsing_inv_det M (isUnit_iff_ne_zero.2 hdet)).ne_zero
  simp_rw [coordinateDerivative_coordinateDerivative_comp_mulVec hN hf, Finset.mul_sum]
  set N := M⁻¹ with hNdef
  set B := M * M.transpose with hBdef
  set S : Fin d → Fin d → ℝ := fun l k =>
    coordinateDerivative k (coordinateDerivative l f) (N.mulVec x) with hSdef
  have hI : ∀ l k, ∑ i, ∑ j, N l i * B i j * N k j = if l = k then 1 else 0 := by
    intro l k
    have h := congrFun (congrFun (inv_mul_mul_transpose_mul hdet) l) k
    rw [← hNdef, ← hBdef] at h
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul] at h
    rw [Matrix.one_apply] at h
    rw [← h, Finset.sum_comm]
  calc ∑ i, ∑ j, ∑ l, ∑ k, B i j * (N l i * N k j * S l k)
      = ∑ l, ∑ k, (∑ i, ∑ j, N l i * B i j * N k j) * S l k := by
        rw [sum4_comm]
        simp only [Finset.sum_mul]
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ l, S l l := by
        simp_rw [hI]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp
    _ = PDE.euclideanCoordLaplacian f (N.mulVec x) := rfl

/-- Classical integration by parts against a test: `∫_U G ∂ⱼψ = -∫_U ∂ⱼG ψ`. -/
theorem setIntegral_mul_coordinateDerivative_of_contDiff {U : Set (Vec d)} {G ψ : Vec d → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hψ : IsSpatialTest U ψ) (j : Fin d) :
    ∫ x in U, G x * coordinateDerivative j ψ x = -∫ x in U, coordinateDerivative j G x * ψ x := by
  have hGψ : IsSpatialTest Set.univ (fun x => G x * ψ x) :=
    ⟨hG.mul hψ.1, hψ.2.1.mul_left, Set.subset_univ _⟩
  have h0 := integral_coordinateDerivative_univ_eq_zero hGψ j
  have hprod : ∀ x, coordinateDerivative j (fun x => G x * ψ x) x =
      coordinateDerivative j G x * ψ x + G x * coordinateDerivative j ψ x := by
    intro x
    have h1 := (hG.differentiable (by simp)) x
    have h2 := (hψ.1.differentiable (by simp)) x
    unfold coordinateDerivative
    rw [fderiv_fun_mul h1 h2]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    ring
  have hzero1 : ∀ x, x ∉ U → G x * coordinateDerivative j ψ x = 0 := fun x hx => by
    rw [coordinateDerivative_eq_zero_of_notMem_tsupport (fun h => hx (hψ.2.2 h)) j, mul_zero]
  have hzero2 : ∀ x, x ∉ U → coordinateDerivative j G x * ψ x = 0 := fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hψ.2.2 h)), mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero1,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero2]
  have i1 : Integrable fun x => coordinateDerivative j G x * ψ x :=
    ((continuous_coordinateDerivative (hG.of_le (by simp)) j).mul hψ.1.continuous)
      |>.integrable_of_hasCompactSupport (hasCompactSupport_mul_of_right hψ.2.1)
  have i2 : Integrable fun x => G x * coordinateDerivative j ψ x :=
    (hG.continuous.mul (continuous_coordinateDerivative (hψ.1.of_le (by simp)) j))
      |>.integrable_of_hasCompactSupport (hasCompactSupport_mul_of_right
        (PDE.hasCompactSupport_euclideanCoordDeriv hψ.2.1 j))
  have h3 : ∫ x, coordinateDerivative j (fun x => G x * ψ x) x =
      (∫ x, coordinateDerivative j G x * ψ x) + ∫ x, G x * coordinateDerivative j ψ x := by
    rw [← integral_add i1 i2]
    exact integral_congr_ae (Eventually.of_forall hprod)
  linarith

theorem memLp_restrict_of_continuous {U : Set (Vec d)} {f : Vec d → ℝ} (hf : Continuous f)
    {K : Set (Vec d)} (hK : IsCompact K) (hUK : U ⊆ K) (hU : MeasurableSet U) :
    MemLp f 2 (volume.restrict U) := by
  have : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.2 (ne_top_of_le_ne_top hK.measure_lt_top.ne (measure_mono hUK))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem hU] with x hx
  exact hC x (hUK hx)

theorem mem_ball_of_mem_matrixEllipsoid {M : Mat d} (hdet : M.det ≠ 0) {b : ℝ} {x : Vec d}
    (hx : x ∈ matrixEllipsoid M b) : M⁻¹.mulVec x ∈ ball (0 : Vec d) b := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]
  exact hy

/-- **A smooth function harmonic on `B_b` gives an `M Mᵀ`-harmonic function on `E_b`.** -/
theorem isL2HarmonicOn_comp_inv {M : Mat d} (hdet : M.det ≠ 0) {b : ℝ} (hb : 0 < b)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hΔ : ∀ y ∈ PDE.euclideanBall (0 : Vec d) b, PDE.euclideanCoordLaplacian f y = 0) :
    IsL2HarmonicOn (M * M.transpose) (matrixEllipsoid M b) (fun x => f (M⁻¹.mulVec x)) := by
  set H : Vec d → ℝ := fun x => f (M⁻¹.mulVec x) with hHdef
  set B := M * M.transpose with hBdef
  have hN : (M⁻¹).det ≠ 0 :=
    (Matrix.isUnit_nonsing_inv_det M (isUnit_iff_ne_zero.2 hdet)).ne_zero
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := hf.comp (matrixCLE M⁻¹ hN).contDiff
  set E := matrixEllipsoid M b with hEdef
  have hEo : IsOpen E := (isOpenBoundedConvexDomain_matrixEllipsoid hdet hb).1
  have hEm : MeasurableSet E := hEo.measurableSet
  have hK : IsCompact (Metric.closedBall (0 : Vec d) (ellipsoidRadius M * b)) :=
    isCompact_closedBall _ _
  have hEK : E ⊆ Metric.closedBall (0 : Vec d) (ellipsoidRadius M * b) := by
    intro x hx
    have h := matrixEllipsoid_subset_ball M b hx
    have h' : euclideanNorm (x - 0) < ellipsoidRadius M * b := h
    rw [sub_zero] at h'
    rw [Metric.mem_closedBall, dist_zero_right]
    have hn : ‖x‖ ≤ euclideanNorm x := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
      rw [Real.norm_eq_abs]
      exact coordinate_abs_le_euclideanNorm x i
    linarith
  set g : Vec d → Vec d := fun x => gradient H x with hgdef
  have hgc : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => g x i) := fun i => by
    simp only [hgdef, gradient]
    exact contDiff_coordinateDerivative hH i
  refine ⟨memLp_restrict_of_continuous hH.continuous hK hEK hEm, g,
    fun i => memLp_restrict_of_continuous (hgc i).continuous hK hEK hEm, ?_, ?_⟩
  · intro i
    refine ⟨hH.continuous.locallyIntegrable.locallyIntegrableOn _,
      (hgc i).continuous.locallyIntegrable.locallyIntegrableOn _, fun ψ hψ => ?_⟩
    exact setIntegral_mul_coordinateDerivative_of_contDiff hH hψ i
  · have hFc : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun x => B.mulVec (g x) j) := fun j => by
      simp only [Matrix.mulVec, dotProduct]
      exact ContDiff.sum fun i _ => contDiff_const.mul (hgc i)
    refine ⟨fun j => (hFc j).continuous.locallyIntegrable.locallyIntegrableOn _,
      locallyIntegrableOn_const _, fun ψ hψ => ?_⟩
    simp only [zero_mul, integral_zero, neg_zero]
    have hdiv : ∀ x ∈ E, ∑ j, coordinateDerivative j (fun x => B.mulVec (g x) j) x = 0 := by
      intro x hx
      have hsymm : ∀ i j, B i j = B j i := fun i j => by
        rw [hBdef, ← Matrix.transpose_apply (M * M.transpose), Matrix.transpose_mul,
          Matrix.transpose_transpose]
      have e : ∀ j, coordinateDerivative j (fun x => B.mulVec (g x) j) x =
          ∑ i, B j i * coordinateDerivative j (fun x => g x i) x := by
        intro j
        have := coordinateDerivative_sum_const_mul Finset.univ (fun i => B j i)
          (G := fun i x => g x i) (fun i => (hgc i).differentiable (by simp)) j x
        simpa [Matrix.mulVec, dotProduct] using this
      simp_rw [e]
      rw [Finset.sum_comm]
      have h2 := sum_mul_secondDeriv_comp_inv hdet hf x
      have hx' : M⁻¹.mulVec x ∈ PDE.euclideanBall (0 : Vec d) b := by
        rw [← ball_zero_eq_pdeEuclideanBall hb]
        exact mem_ball_of_mem_matrixEllipsoid hdet hx
      rw [hΔ _ hx'] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hsymm j i]
      rfl
    have hsplit : ∫ x in E, dot (B.mulVec (g x)) (gradient ψ x) =
        ∑ j, ∫ x in E, B.mulVec (g x) j * coordinateDerivative j ψ x := by
      have hi : ∀ j, Integrable (fun x => B.mulVec (g x) j * coordinateDerivative j ψ x)
          (volume.restrict E) := fun j =>
        (((hFc j).continuous.mul (continuous_coordinateDerivative (hψ.1.of_le (by simp)) j))
          |>.integrable_of_hasCompactSupport (hasCompactSupport_mul_of_right
            (PDE.hasCompactSupport_euclideanCoordDeriv hψ.2.1 j))).integrableOn
      rw [← integral_finsetSum _ fun j _ => hi j]
      rfl
    rw [hsplit, Finset.sum_congr rfl fun j _ =>
      setIntegral_mul_coordinateDerivative_of_contDiff (hFc j) hψ j, Finset.sum_neg_distrib,
      neg_eq_zero]
    have i1 : ∀ j, Integrable (fun x => coordinateDerivative j (fun x => B.mulVec (g x) j) x * ψ x)
        (volume.restrict E) := fun j =>
      (((continuous_coordinateDerivative ((hFc j).of_le (by simp)) j).mul hψ.1.continuous)
        |>.integrable_of_hasCompactSupport (hasCompactSupport_mul_of_right hψ.2.1)).integrableOn
    rw [← integral_finsetSum _ fun j _ => i1 j]
    have hz : ∫ x in E, ∑ j, coordinateDerivative j (fun x => B.mulVec (g x) j) x * ψ x =
        ∫ x in E, (0 : ℝ) := by
      refine setIntegral_congr_fun hEm fun x hx => ?_
      rw [← Finset.sum_mul, hdiv x hx, zero_mul]
    rw [hz, integral_zero]

/-- The second derivatives of `χ ∘ M⁻¹` are bounded by those of `χ`. -/
theorem abs_secondDeriv_comp_inv_le {M : Mat d} (hdet : M.det ≠ 0) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) {S : ℝ}
    (hS : ∀ a b x, |PDE.euclideanCoordSecondDeriv a b χ x| ≤ S) (i j : Fin d) (x : Vec d) :
    |coordinateDerivative j (coordinateDerivative i (fun y => χ (M⁻¹.mulVec y))) x| ≤
      (∑ l, ∑ k, |M⁻¹ l i| * |M⁻¹ k j|) * S := by
  have hN : (M⁻¹).det ≠ 0 :=
    (Matrix.isUnit_nonsing_inv_det M (isUnit_iff_ne_zero.2 hdet)).ne_zero
  rw [coordinateDerivative_coordinateDerivative_comp_mulVec hN hχ, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  exact hS l k _

end QSH
