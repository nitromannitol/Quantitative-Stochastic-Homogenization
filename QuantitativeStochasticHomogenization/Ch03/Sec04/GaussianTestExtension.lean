import QuantitativeStochasticHomogenization.Ch03.Sec04.CutoffTestIdentity
import QuantitativeStochasticHomogenization.Ch03.Sec04.SpatialWeakLocalization
import QuantitativeStochasticHomogenization.Ch03.Sec04.SpatialWeakProduct

/-!
# Integration by parts against Gaussian tests

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Proposition 3.21: the Gaussian averages of `∇φ` and of `∇φ · a(e + ∇φ)` are written as
integrals of `φ - c` against `∇Φ`.

* `integral_identity_extend`: an identity `∫ (η A + F · ∇η) = 0` for all smooth compactly supported
  `η` extends to every smooth `Φ` with `Φ A`, `F · ∇Φ` and `Φ F` integrable, by cutting `Φ` off with
  the dilations `χ(·/R)` of a bump function and letting `R → ∞`.
* `integral_mul_grad_eq_neg`: `∫ Φ ∂ₖu = -∫ u ∂ₖΦ` for a weak gradient.
* `integral_mul_dot_grad_eq_neg`: `∫ Φ q · ∇u = -∫ u q · ∇Φ` for `q` weakly divergence-free and
  `u ∈ H¹_loc`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ}

theorem coordinateDerivative_mul' {f g : Vec d → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (k : Fin d) (y : Vec d) :
    coordinateDerivative k (fun z => f z * g z) y =
      f y * coordinateDerivative k g y + g y * coordinateDerivative k f y := by
  unfold coordinateDerivative
  show (fderiv ℝ (f * g) y) (unitVector k) = _
  rw [((hf y).hasFDerivAt.mul (hg y).hasFDerivAt).fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]

theorem coordinateDerivative_comp_smul {χ : Vec d → ℝ} (hχ : Differentiable ℝ χ) (c : ℝ)
    (k : Fin d) (y : Vec d) :
    coordinateDerivative k (fun y => χ (c • y)) y = c * coordinateDerivative k χ (c • y) := by
  unfold coordinateDerivative
  have h : HasFDerivAt (fun y : Vec d => χ (c • y))
      ((fderiv ℝ χ (c • y)).comp (c • ContinuousLinearMap.id ℝ (Vec d))) y :=
    (hχ (c • y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul c)
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

theorem abs_dot_le_sum_abs (u v : Vec d) : |dot u v| ≤ ∑ k, |u k| * |v k| := by
  unfold dot
  calc |∑ k, u k * v k| ≤ ∑ k, |u k * v k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |u k| * |v k| := Finset.sum_congr rfl fun k _ => abs_mul _ _

/-- **Extension of an integral identity from compactly supported tests to integrable ones.** -/
theorem integral_identity_extend {A : Vec d → ℝ} {F : Vec d → Vec d}
    (hid : ∀ η : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      ∫ x, (η x * A x + dot (F x) (gradient η x)) = 0)
    {Φ : Vec d → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hA : Integrable fun x => Φ x * A x)
    (hF : Integrable fun x => dot (F x) (gradient Φ x))
    (hF' : ∀ k, Integrable fun x => Φ x * F x k) :
    ∫ x, (Φ x * A x + dot (F x) (gradient Φ x)) = 0 := by
  let χb : ContDiffBump (0 : Vec d) := ⟨1, 2, one_pos, one_lt_two⟩
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (χb : Vec d → ℝ) := χb.contDiff
  have hχd : Differentiable ℝ (χb : Vec d → ℝ) :=
    (χb.contDiff (n := 1)).differentiable one_ne_zero
  have hΦd : Differentiable ℝ Φ := (hΦ.of_le (by simp)).differentiable one_ne_zero
  obtain ⟨B, hB0, hB⟩ : ∃ B, 0 ≤ B ∧ ∀ k y, |coordinateDerivative k (χb : Vec d → ℝ) y| ≤ B := by
    have h := fun k : Fin d =>
      (contDiff_coordinateDerivative_top hχ k).continuous.bounded_above_of_compact_support
        ((χb.hasCompactSupport).fderiv_apply ℝ (unitVector k))
    choose A hA using h
    refine ⟨∑ k, |A k|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun k y => ?_⟩
    have h1 := hA k y
    rw [Real.norm_eq_abs] at h1
    exact h1.trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun k => |A k|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ k)))
  set c : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹ with hc
  have hc0 : ∀ n, 0 < c n := fun n => by positivity
  have hc1 : ∀ n, c n ≤ 1 := fun n => inv_le_one_of_one_le₀ (by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)
  -- the integrand at the cutoff `χ(c • ·) Φ`
  set G : ℕ → Vec d → ℝ := fun n x => χb (c n • x) * (Φ x * A x + dot (F x) (gradient Φ x)) +
    Φ x * ∑ k, F x k * (c n * coordinateDerivative k (χb : Vec d → ℝ) (c n • x)) with hG
  have hcut : ∀ n, ∫ x, G n x = 0 := by
    intro n
    have hχc : ContDiff ℝ (⊤ : ℕ∞) (fun y => χb (c n • y)) := hχ.comp (contDiff_const_smul _)
    have hsm : Differentiable ℝ (fun y : Vec d => c n • y) :=
      (differentiable_id (𝕜 := ℝ) (E := Vec d)).const_smul (c n)
    have hχcd : Differentiable ℝ (fun y => χb (c n • y)) := hχd.comp hsm
    have h := hid (fun y => χb (c n • y) * Φ y) (hχc.mul hΦ)
      ((χb.hasCompactSupport.comp_smul (hc0 n).ne').mul_right)
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hG]
    have hgr : gradient (fun y => χb (c n • y) * Φ y) x =
        fun k => χb (c n • x) * coordinateDerivative k Φ x +
          Φ x * (c n * coordinateDerivative k (χb : Vec d → ℝ) (c n • x)) := by
      funext k
      show coordinateDerivative k _ x = _
      rw [coordinateDerivative_mul' hχcd hΦd, coordinateDerivative_comp_smul hχd]
    rw [hgr]
    have hsplit : dot (F x) (fun k => χb (c n • x) * coordinateDerivative k Φ x +
          Φ x * (c n * coordinateDerivative k (χb : Vec d → ℝ) (c n • x))) =
        χb (c n • x) * dot (F x) (gradient Φ x) +
          Φ x * ∑ k, F x k * (c n * coordinateDerivative k (χb : Vec d → ℝ) (c n • x)) := by
      unfold dot gradient
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hsplit]
    ring
  -- domination
  set H : Vec d → ℝ := fun x => |Φ x * A x| + |dot (F x) (gradient Φ x)| +
    B * ∑ k, |Φ x * F x k| with hH
  have hHint : Integrable H :=
    (hA.abs.add hF.abs).add ((integrable_finsetSum _ fun k _ => (hF' k).abs).const_mul B)
  have hχ01 : ∀ y, 0 ≤ χb y ∧ χb y ≤ 1 := fun y => ⟨χb.nonneg, χb.le_one⟩
  have hbound : ∀ n, ∀ x, ‖G n x‖ ≤ H x := by
    intro n x
    rw [Real.norm_eq_abs]
    simp only [hG, hH]
    have h1 : |χb (c n • x) * (Φ x * A x + dot (F x) (gradient Φ x))| ≤
        |Φ x * A x| + |dot (F x) (gradient Φ x)| := by
      rw [abs_mul, abs_of_nonneg (hχ01 _).1]
      calc χb (c n • x) * |Φ x * A x + dot (F x) (gradient Φ x)|
          ≤ 1 * |Φ x * A x + dot (F x) (gradient Φ x)| :=
            mul_le_mul_of_nonneg_right (hχ01 _).2 (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact abs_add_le _ _
    have h2 : |Φ x * ∑ k, F x k * (c n * coordinateDerivative k (χb : Vec d → ℝ) (c n • x))| ≤
        B * ∑ k, |Φ x * F x k| := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      have hk := hB k (c n • x)
      have hcD : |c n * coordinateDerivative k (χb : Vec d → ℝ) (c n • x)| ≤ B := by
        rw [abs_mul, abs_of_pos (hc0 n)]
        exact (mul_le_of_le_one_left (abs_nonneg _) (hc1 n)).trans hk
      rw [show Φ x * (F x k * (c n * coordinateDerivative k (χb : Vec d → ℝ) (c n • x))) =
        (Φ x * F x k) * (c n * coordinateDerivative k (χb : Vec d → ℝ) (c n • x)) by ring,
        abs_mul]
      calc |Φ x * F x k| * |c n * coordinateDerivative k (χb : Vec d → ℝ) (c n • x)|
          ≤ |Φ x * F x k| * B := mul_le_mul_of_nonneg_left hcD (abs_nonneg _)
        _ = B * |Φ x * F x k| := mul_comm _ _
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  have hmeas : ∀ n, AEStronglyMeasurable (G n) volume := by
    intro n
    have hχm : Continuous fun x => χb (c n • x) :=
      χb.continuous.comp (continuous_const_smul _)
    refine (hχm.aestronglyMeasurable.mul (hA.add hF).aestronglyMeasurable).add ?_
    · have hsum : AEStronglyMeasurable (fun x => ∑ k, (Φ x * F x k) *
          (c n * coordinateDerivative k (χb : Vec d → ℝ) (c n • x))) volume :=
        (Finset.aestronglyMeasurable_sum (f := fun k x => (Φ x * F x k) *
          (c n * coordinateDerivative k (χb : Vec d → ℝ) (c n • x))) Finset.univ
          fun k _ => (hF' k).aestronglyMeasurable.mul
            (continuous_const.mul ((contDiff_coordinateDerivative_top hχ k).continuous.comp
              (continuous_const_smul _))).aestronglyMeasurable).congr
          (Eventually.of_forall fun x => by simp only [Finset.sum_apply])
      refine hsum.congr (Eventually.of_forall fun x => ?_)
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
  -- pointwise limit
  have hlim : ∀ x, Tendsto (fun n => G n x) atTop
      (𝓝 (Φ x * A x + dot (F x) (gradient Φ x))) := by
    intro x
    have hc : Tendsto c atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n => by
      simp [hc]
    have hcx : Tendsto (fun n => c n • x) atTop (𝓝 0) := by
      have := hc.smul_const x
      rwa [zero_smul] at this
    have hχ1 : Tendsto (fun n => χb (c n • x)) atTop (𝓝 1) := by
      have h := (χb.continuous.tendsto 0).comp hcx
      have h0 : χb 0 = 1 := χb.one_of_mem_closedBall (by simp [χb.rIn_pos.le])
      rw [h0] at h
      exact h
    have hsum : Tendsto (fun n => Φ x * ∑ k, F x k *
        (c n * coordinateDerivative k (χb : Vec d → ℝ) (c n • x))) atTop (𝓝 0) := by
      have hk : ∀ k, Tendsto (fun n => F x k *
          (c n * coordinateDerivative k (χb : Vec d → ℝ) (c n • x))) atTop (𝓝 0) := by
        intro k
        have h1 : Tendsto (fun n => c n * coordinateDerivative k (χb : Vec d → ℝ) (c n • x))
            atTop (𝓝 0) := by
          have h2 := (hc.mul ((contDiff_coordinateDerivative_top hχ k).continuous.tendsto 0
            |>.comp hcx))
          rwa [zero_mul] at h2
        have h3 := h1.const_mul (F x k)
        rwa [mul_zero] at h3
      have h4 := (tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun k _ => hk k).const_mul
        (Φ x)
      simp only [Finset.sum_const_zero, mul_zero] at h4
      exact h4
    have h5 := (hχ1.mul_const (Φ x * A x + dot (F x) (gradient Φ x))).add hsum
    rw [one_mul, add_zero] at h5
    exact h5
  have hDCT := tendsto_integral_of_dominated_convergence H hmeas hHint
    (fun n => Eventually.of_forall (hbound n)) (Eventually.of_forall hlim)
  have hzero : Tendsto (fun n => ∫ x, G n x) atTop (𝓝 0) :=
    tendsto_const_nhds.congr fun n => (hcut n).symm
  exact tendsto_nhds_unique hDCT hzero

theorem dot_smul_unitVector (c : ℝ) (k : Fin d) (v : Vec d) :
    dot (c • unitVector k) v = c * v k := by
  unfold dot
  rw [Finset.sum_eq_single k]
  · simp [unitVector]
  · intro b _ hb
    simp [unitVector, hb]
  · simp

/-- **Weak gradients against integrable smooth tests**: `∫ Φ ∂ₖu = -∫ u ∂ₖΦ`. -/
theorem integral_mul_grad_eq_neg {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hw : HasWeakGradient Set.univ u g) (k : Fin d) {Φ : Vec d → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hA : Integrable fun x => Φ x * g x k)
    (hF : Integrable fun x => u x * coordinateDerivative k Φ x)
    (hF' : Integrable fun x => Φ x * u x) :
    ∫ x, Φ x * g x k = -∫ x, u x * coordinateDerivative k Φ x := by
  have hid : ∀ η : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      ∫ x, (η x * g x k + dot (u x • unitVector k) (gradient η x)) = 0 := by
    intro η hη hηc
    have htest : IsSpatialTest Set.univ η := ⟨hη, hηc, Set.subset_univ _⟩
    have h := (hw k).2.2 η htest
    simp only [Measure.restrict_univ] at h
    have h1 : Integrable fun x => g x k * η x :=
      integrableOn_univ.mp (integrableOn_mul_spatialTest (hw k).2.1 htest)
    have h2 : Integrable fun x => u x * coordinateDerivative k η x :=
      integrableOn_univ.mp
        (integrableOn_mul_spatialTest (hw k).1 (isSpatialTest_coordinateDerivative htest k))
    have heq : (fun x => η x * g x k + dot (u x • unitVector k) (gradient η x)) =
        fun x => g x k * η x + u x * coordinateDerivative k η x := by
      funext x
      rw [dot_smul_unitVector, mul_comm (η x)]
      rfl
    rw [heq, integral_add h1 h2, h]
    ring
  have hF2 : Integrable fun x => dot (u x • unitVector k) (gradient Φ x) := by
    refine hF.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [dot_smul_unitVector]
    rfl
  have hF3 : ∀ j, Integrable fun x => Φ x * (u x • unitVector k : Vec d) j := by
    intro j
    refine (hF'.mul_const (unitVector k j : ℝ)).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have h := integral_identity_extend hid hΦ hA hF2 hF3
  have heq : (fun x => Φ x * g x k + dot (u x • unitVector k) (gradient Φ x)) =
      fun x => Φ x * g x k + u x * coordinateDerivative k Φ x := by
    funext x
    rw [dot_smul_unitVector]
    rfl
  rw [heq, integral_add hA hF] at h
  linarith

/-- A compact set lies in a centered Euclidean ball. -/
theorem exists_ball_of_isCompact {K : Set (Vec d)} (hK : IsCompact K) :
    ∃ R : ℝ, 0 < R ∧ K ⊆ ball 0 R := by
  have hc : Continuous fun x : Vec d => euclideanNorm x := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  obtain ⟨B, hB⟩ := (hK.image hc).isBounded.bddAbove
  refine ⟨max B 0 + 1, by positivity, fun x hx => ?_⟩
  have h1 : euclideanNorm x ≤ B := hB ⟨x, hx, rfl⟩
  show euclideanNorm (x - 0) < max B 0 + 1
  rw [sub_zero]
  linarith [le_max_left B 0]

/-- **Divergence-free fields against cutoffs of `H¹_loc` functions, on `ℝ^d`**:
`∫ (η q · ∇u + u q · ∇η) = 0` for smooth compactly supported `η`. -/
theorem integral_cutoff_dot_eq_zero {q : Vec d → Vec d}
    (hq : HasWeakDivergence Set.univ q (fun _ => 0))
    (hqL : ∀ R : ℝ, 0 < R → ∀ i, MemLp (fun x => q x i) 2 (volume.restrict (ball 0 R)))
    {u : Vec d → ℝ} {g : Vec d → Vec d} (hw : HasWeakGradient Set.univ u g)
    (huL : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)))
    (hgL : ∀ R : ℝ, 0 < R → ∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 R)))
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η) :
    ∫ x, (η x * dot (q x) (g x) + dot (u x • q x) (gradient η x)) = 0 := by
  obtain ⟨R, hR, hKR⟩ := exists_ball_of_isCompact hηc
  set U := ball (0 : Vec d) R with hUdef
  have hU := isOpenBoundedConvexDomain_ball (0 : Vec d) hR
  have hwU : HasWeakGradient U u g := hasWeakGradient_mono (Set.subset_univ _) hw
  have h := sum_integral_cutoff_eq_zero hU (huL R hR) (hgL R hR) hwU hη hηc hKR hq (hqL R hR)
  have hint : ∀ i, Integrable (fun x => q x i * (η x * g x i + u x * coordinateDerivative i η x))
      (volume.restrict U) := fun i =>
    integrable_mul_of_memLp_two (hqL R hR i)
      (memLp_cutoff_grad hU (huL R hR) (hgL R hR) hwU hη hηc hKR i)
  rw [← integral_finsetSum _ fun i _ => hint i] at h
  have hpt : ∀ x, η x * dot (q x) (g x) + dot (u x • q x) (gradient η x) =
      ∑ i, q x i * (η x * g x i + u x * coordinateDerivative i η x) := by
    intro x
    unfold dot gradient
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hsupp : ∀ x ∉ U, η x * dot (q x) (g x) + dot (u x • q x) (gradient η x) = 0 := by
    intro x hx
    have hxη : x ∉ tsupport η := fun h' => hx (hKR h')
    rw [image_eq_zero_of_notMem_tsupport hxη, gradient_eq_zero_of_notMem_tsupport hxη]
    simp [dot]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
  rw [← h]
  exact integral_congr_ae (Eventually.of_forall hpt)

/-- **Divergence-free fields against integrable smooth tests**:
`∫ Φ q · ∇u = -∫ u q · ∇Φ`. -/
theorem integral_mul_dot_grad_eq_neg {q : Vec d → Vec d}
    (hq : HasWeakDivergence Set.univ q (fun _ => 0))
    (hqL : ∀ R : ℝ, 0 < R → ∀ i, MemLp (fun x => q x i) 2 (volume.restrict (ball 0 R)))
    {u : Vec d → ℝ} {g : Vec d → Vec d} (hw : HasWeakGradient Set.univ u g)
    (huL : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)))
    (hgL : ∀ R : ℝ, 0 < R → ∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 R)))
    {Φ : Vec d → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hA : Integrable fun x => Φ x * dot (q x) (g x))
    (hF : Integrable fun x => u x * dot (q x) (gradient Φ x))
    (hF' : ∀ k, Integrable fun x => Φ x * (u x * q x k)) :
    ∫ x, Φ x * dot (q x) (g x) = -∫ x, u x * dot (q x) (gradient Φ x) := by
  have hdot : ∀ x (v : Vec d), dot (u x • q x) v = u x * dot (q x) v := by
    intro x v
    unfold dot
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hid : ∀ η : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      ∫ x, (η x * dot (q x) (g x) + dot (u x • q x) (gradient η x)) = 0 :=
    fun η hη hηc => integral_cutoff_dot_eq_zero hq hqL hw huL hgL hη hηc
  have hF2 : Integrable fun x => dot (u x • q x) (gradient Φ x) :=
    hF.congr (Eventually.of_forall fun x => (hdot x _).symm)
  have hF3 : ∀ k, Integrable fun x => Φ x * (u x • q x) k := fun k => hF' k
  have h := integral_identity_extend hid hΦ hA hF2 hF3
  simp only [hdot] at h
  rw [integral_add hA hF] at h
  linarith

end QSH
