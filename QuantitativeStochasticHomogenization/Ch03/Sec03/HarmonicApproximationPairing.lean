import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicApproximationData

/-!
# The pairing of the residual with Laplacians of tests in ball coordinates

Let `v` be `a`-harmonic in `H¹(E_{r'})`, `E_{r'} = M B_{r'}`, with `M Mᵀ = ½(D + Dᵀ)`, and let the
centred correctors `φᵢ`, `σᵢ` satisfy the hypotheses of the tensor identity on `E_{r'}`, with
`∫ φᵢ² ≤ O²`, `∫ σᵢⱼₖ² ≤ O²` and `∫ |∇v|² ≤ G²` on `E_{r'}`. For a test `χ` in `B_{r'}` whose
second derivatives are bounded by `S`, the test `ψ = χ ∘ M⁻¹` satisfies
`∑ᵢⱼ (D eᵢ)ⱼ ∂ⱼ∂ᵢψ = (Δχ) ∘ M⁻¹`, and the tensor identity and Cauchy–Schwarz give
`|∫_{B_{r'}} (v ∘ M) Δχ| ≤ |det M|⁻¹ n² S (d³ + d² √d Λ) O G`, `n = ∑ₗₖ |(M⁻¹)ₗₖ|`.
-/

open MeasureTheory Filter Set

noncomputable section

namespace QSH

variable {d : ℕ}

/-- `|∫_U f g H| ≤ S ‖f‖_{L²(U)} ‖g‖_{L²(U)}` for a test `H` bounded by `S`. -/
theorem abs_integral_mul_mul_le {U : Set (Vec d)} {f g H : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U))
    (hH : IsSpatialTest U H) {S : ℝ} (hS0 : 0 ≤ S) (hS : ∀ x, |H x| ≤ S) :
    |∫ x in U, f x * g x * H x| ≤
      S * (Real.sqrt (∫ x in U, f x ^ 2) * Real.sqrt (∫ x in U, g x ^ 2)) := by
  have hgH := memLp_mul_isSpatialTest hg hH
  have e : (fun x => f x * g x * H x) = fun x => f x * (g x * H x) := by
    funext x
    ring
  rw [e]
  refine (abs_integral_mul_le_sqrt_mul_sqrt hf hgH).trans ?_
  have h2 : ∫ x in U, (g x * H x) ^ 2 ≤ S ^ 2 * ∫ x in U, g x ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono hgH.integrable_sq (hg.integrable_sq.const_mul _) fun x => ?_
    change (g x * H x) ^ 2 ≤ S ^ 2 * g x ^ 2
    rw [mul_pow, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hS x) 2
  calc Real.sqrt (∫ x in U, f x ^ 2) * Real.sqrt (∫ x in U, (g x * H x) ^ 2)
      ≤ Real.sqrt (∫ x in U, f x ^ 2) * Real.sqrt (S ^ 2 * ∫ x in U, g x ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _)
    _ = S * (Real.sqrt (∫ x in U, f x ^ 2) * Real.sqrt (∫ x in U, g x ^ 2)) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hS0]
        ring

/-- For symmetric `H`, `∑ᵢⱼ (½(D + Dᵀ))ᵢⱼ Hᵢⱼ = ∑ᵢⱼ (D eᵢ)ⱼ Hᵢⱼ`. -/
theorem sum_symmPart_mul_eq (D : Mat d) {H : Fin d → Fin d → ℝ} (hH : ∀ i j, H i j = H j i) :
    ∑ i, ∑ j, ((1 / 2 : ℝ) • (D + D.transpose)) i j * H i j =
      ∑ i, ∑ j, D.mulVec (unitVector i) j * H i j := by
  have hDe : ∀ i j, D.mulVec (unitVector i) j = D j i := by
    intro i j
    simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply]
  simp_rw [hDe]
  have hswap : ∑ i, ∑ j, D i j * H i j = ∑ i, ∑ j, D j i * H i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hH j i]
  have e : ∀ i j, ((1 / 2 : ℝ) • (D + D.transpose)) i j * H i j =
      (1 / 2) * (D i j * H i j) + (1 / 2) * (D j i * H i j) := by
    intro i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
    ring
  simp_rw [e, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hswap]
  ring

theorem sqrt_integral_sq_le {U : Set (Vec d)} {f : Vec d → ℝ} {O : ℝ} (hO : 0 ≤ O)
    (h : ∫ x in U, f x ^ 2 ≤ O ^ 2) : Real.sqrt (∫ x in U, f x ^ 2) ≤ O := by
  calc Real.sqrt (∫ x in U, f x ^ 2) ≤ Real.sqrt (O ^ 2) := Real.sqrt_le_sqrt h
    _ = O := Real.sqrt_sq hO

theorem integral_sq_component_le {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U)) (k : Fin d) :
    ∫ x in U, g x k ^ 2 ≤ ∫ x in U, euclideanSq (g x) := by
  have hint : Integrable (fun x => euclideanSq (g x)) (volume.restrict U) := by
    have := integrable_finsetSum (Finset.univ : Finset (Fin d)) fun l _ => (hg l).integrable_sq
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [euclideanSq, dot, pow_two]
  refine integral_mono (hg k).integrable_sq hint fun x => ?_
  change g x k ^ 2 ≤ ∑ l, g x l * g x l
  rw [pow_two]
  exact Finset.single_le_sum (f := fun l => g x l * g x l) (fun l _ => mul_self_nonneg _)
    (Finset.mem_univ k)

/-- **The pairing of the residual with Laplacians of tests** in ball coordinates. -/
theorem abs_integral_ball_mul_laplacian_le {Λ : ℝ} (hΛ : 1 ≤ Λ) (a : CoefficientField d Λ)
    {M D : Mat d} (hdet : M.det ≠ 0) (hMM : M * M.transpose = (1 / 2 : ℝ) • (D + D.transpose))
    {R : ℝ} (hR : 0 < R)
    {v : Vec d → ℝ} {gv : Vec d → Vec d}
    (hv : MemLp v 2 (volume.restrict (matrixEllipsoid M R)))
    (hgv : ∀ i, MemLp (fun x => gv x i) 2 (volume.restrict (matrixEllipsoid M R)))
    (hwv : HasWeakGradient (matrixEllipsoid M R) v gv)
    (hdiv : HasWeakDivergence (matrixEllipsoid M R) (fun x => (a x).mulVec (gv x)) (fun _ => 0))
    {φ : Fin d → Vec d → ℝ} {gφ : Fin d → Vec d → Vec d}
    (hφ : ∀ i, MemLp (φ i) 2 (volume.restrict (matrixEllipsoid M R)))
    (hgφ : ∀ i l, MemLp (fun x => gφ i x l) 2 (volume.restrict (matrixEllipsoid M R)))
    (hwφ : ∀ i, HasWeakGradient (matrixEllipsoid M R) (φ i) (gφ i))
    (hc : ∀ i, MemLp (fun x => x i + φ i x) 2 (volume.restrict (matrixEllipsoid M R)))
    (hgc : ∀ i l, MemLp (fun x => (unitVector i + gφ i x) l) 2
      (volume.restrict (matrixEllipsoid M R)))
    (hwc : ∀ i, HasWeakGradient (matrixEllipsoid M R) (fun x => x i + φ i x)
      (fun x => unitVector i + gφ i x))
    (hdivc : ∀ i, HasWeakDivergence (matrixEllipsoid M R)
      (fun x => (a x).mulVec (unitVector i + gφ i x)) (fun _ => 0))
    {σ : Fin d → Vec d → Mat d} {gσ : Fin d → Fin d → Fin d → Vec d → Vec d}
    (hσ : ∀ i j k, MemLp (fun x => σ i x j k) 2 (volume.restrict (matrixEllipsoid M R)))
    (hgσ : ∀ i j k l, MemLp (fun x => gσ i j k x l) 2 (volume.restrict (matrixEllipsoid M R)))
    (hwσ : ∀ i j k, HasWeakGradient (matrixEllipsoid M R) (fun x => σ i x j k) (gσ i j k))
    (hskew : ∀ i x j k, σ i x j k = -σ i x k j)
    (hflux : ∀ i j, HasWeakDivergence (matrixEllipsoid M R) (fun x k => σ i x j k)
      (fun x => (a x).mulVec (unitVector i + gφ i x) j - D.mulVec (unitVector i) j))
    {O G : ℝ} (hO0 : 0 ≤ O) (hG0 : 0 ≤ G)
    (hOφ : ∀ i, ∫ x in matrixEllipsoid M R, φ i x ^ 2 ≤ O ^ 2)
    (hOσ : ∀ i j k, ∫ x in matrixEllipsoid M R, σ i x j k ^ 2 ≤ O ^ 2)
    (hG : ∫ x in matrixEllipsoid M R, euclideanSq (gv x) ≤ G ^ 2)
    {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ PDE.euclideanBall 0 R) {S : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ a b x, |PDE.euclideanCoordSecondDeriv a b χ x| ≤ S) :
    |∫ y in PDE.euclideanBall 0 R, v (M.mulVec y) * PDE.euclideanCoordLaplacian χ y| ≤
      |M.det|⁻¹ * ((∑ l, ∑ k, |M⁻¹ l k|) ^ 2 * S) *
        ((d ^ 3 + d ^ 2 * Real.sqrt d * Λ) * O * G) := by
  classical
  set E := matrixEllipsoid M R with hEdef
  set N := M⁻¹ with hNdef
  set nM := ∑ l, ∑ k, |N l k| with hnMdef
  have hnM : 0 ≤ nM := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  set ψ : Vec d → ℝ := fun x => χ (N.mulVec x) with hψdef
  have hχB : IsSpatialTest (ball 0 R) χ :=
    ⟨hχ, hχc, by rw [ball_zero_eq_pdeEuclideanBall hR]; exact hχs⟩
  have hψ : IsSpatialTest E ψ := by
    have h := isSpatialTest_comp_symm hdet hχB
    have e : (χ ∘ (matrixCLE M hdet).symm) = ψ := by
      funext x
      simp only [Function.comp, matrixCLE_symm_apply, hψdef, hNdef]
    rwa [e] at h
  set H : Fin d → Fin d → Vec d → ℝ := fun i j => coordinateDerivative j (coordinateDerivative i ψ)
    with hHdef
  have hHt : ∀ i j, IsSpatialTest E (H i j) := fun i j =>
    isSpatialTest_coordinateDerivative (isSpatialTest_coordinateDerivative hψ i) j
  have hHb : ∀ i j x, |H i j x| ≤ nM ^ 2 * S := by
    intro i j x
    refine (abs_secondDeriv_comp_inv_le hdet hχ hS i j x).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hS0
    have h1 : ∑ l, ∑ k, |N l i| * |N k j| = (∑ l, |N l i|) * (∑ k, |N k j|) := by
      rw [Finset.sum_mul_sum]
    have h2 : ∀ m, ∑ l, |N l m| ≤ nM := fun m =>
      Finset.sum_le_sum fun l _ => Finset.single_le_sum (f := fun k => |N l k|)
        (fun k _ => abs_nonneg _) (Finset.mem_univ m)
    rw [h1, sq]
    exact mul_le_mul (h2 i) (h2 j) (Finset.sum_nonneg fun _ _ => abs_nonneg _) hnM
  have hcv : ∫ x in E, v x * PDE.euclideanCoordLaplacian χ (N.mulVec x) =
      |M.det| * ∫ y in ball 0 R, v (M.mulVec y) * PDE.euclideanCoordLaplacian χ y := by
    rw [setIntegral_matrixEllipsoid hdet R]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hNdef, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.2 hdet),
      Matrix.one_mulVec]
  have hlap : ∀ x, PDE.euclideanCoordLaplacian χ (N.mulVec x) =
      ∑ i, ∑ j, D.mulVec (unitVector i) j * H i j x := by
    intro x
    rw [← sum_mul_secondDeriv_comp_inv hdet hχ x, hMM]
    exact sum_symmPart_mul_eq D (H := fun i j => H i j x) fun i j =>
      coordinateDerivative_comm_of_contDiff_two (hψ.1.of_le (by simp)) j i x
  have hid := integral_mul_secondOrder_eq_tensor hΛ a hdet hR D hv hgv hwv hdiv hφ hgφ hwφ hc hgc
    hwc hdivc hσ hgσ hwσ hskew hflux hψ
  have hgvk : ∀ k, Real.sqrt (∫ x in E, gv x k ^ 2) ≤ G := fun k =>
    sqrt_integral_sq_le hG0 ((integral_sq_component_le hgv k).trans hG)
  have hq : ∀ j, MemLp (fun x => (a x).mulVec (gv x) j) 2 (volume.restrict E) := fun j =>
    memLp_coefficient_mulVec hΛ a (isOpenBoundedConvexDomain_matrixEllipsoid hdet hR).1.measurableSet
      hgv j
  have hqj : ∀ j, Real.sqrt (∫ x in E, (a x).mulVec (gv x) j ^ 2) ≤ Real.sqrt d * Λ * G := by
    intro j
    have hint : Integrable (fun x => euclideanSq (gv x)) (volume.restrict E) := by
      have := integrable_finsetSum (Finset.univ : Finset (Fin d)) fun l _ => (hgv l).integrable_sq
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only [euclideanSq, dot, pow_two]
    have h1 : ∫ x in E, (a x).mulVec (gv x) j ^ 2 ≤ (Real.sqrt d * Λ * G) ^ 2 := by
      calc ∫ x in E, (a x).mulVec (gv x) j ^ 2 ≤ ∫ x in E, d * Λ ^ 2 * euclideanSq (gv x) :=
            integral_mono (hq j).integrable_sq (hint.const_mul _) fun x =>
              sq_coefficient_mulVec_le a x (gv x) j
        _ = d * Λ ^ 2 * ∫ x in E, euclideanSq (gv x) := integral_const_mul _ _
        _ ≤ d * Λ ^ 2 * G ^ 2 := mul_le_mul_of_nonneg_left hG (by positivity)
        _ = (Real.sqrt d * Λ * G) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    exact sqrt_integral_sq_le (by positivity) h1
  have hσterm : ∀ i j k, |∫ x in E, σ i x j k * gv x k * H i j x| ≤ nM ^ 2 * S * (O * G) := by
    intro i j k
    refine (abs_integral_mul_mul_le (hσ i j k) (hgv k) (hHt i j) (by positivity) (hHb i j)).trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul (sqrt_integral_sq_le hO0 (hOσ i j k)) (hgvk k)
      (Real.sqrt_nonneg _) hO0) (by positivity)
  have hφterm : ∀ i j, |∫ x in E, φ i x * (a x).mulVec (gv x) j * H i j x| ≤
      nM ^ 2 * S * (O * (Real.sqrt d * Λ * G)) := by
    intro i j
    refine (abs_integral_mul_mul_le (hφ i) (hq j) (hHt i j) (by positivity) (hHb i j)).trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul (sqrt_integral_sq_le hO0 (hOφ i)) (hqj j)
      (Real.sqrt_nonneg _) hO0) (by positivity)
  have htotal : |∫ x in E, v x * PDE.euclideanCoordLaplacian χ (N.mulVec x)| ≤
      nM ^ 2 * S * ((d ^ 3 + d ^ 2 * Real.sqrt d * Λ) * O * G) := by
    have e : ∫ x in E, v x * PDE.euclideanCoordLaplacian χ (N.mulVec x) =
        ∫ x in E, v x * ∑ i, ∑ j, D.mulVec (unitVector i) j * H i j x :=
      integral_congr_ae (Eventually.of_forall fun x => by
        change v x * _ = v x * _
        rw [hlap x])
    rw [e, hid]
    have hs1 : |∑ i, ∑ j, ∑ k, ∫ x in E, σ i x j k * gv x k * H i j x| ≤
        d ^ 3 * (nM ^ 2 * S * (O * G)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i, |∑ j, ∑ k, ∫ x in E, σ i x j k * gv x k * H i j x|
          ≤ ∑ _i : Fin d, ∑ _j : Fin d, ∑ _k : Fin d, nM ^ 2 * S * (O * G) :=
            Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun j _ => (Finset.abs_sum_le_sum_abs _ _).trans
                (Finset.sum_le_sum fun k _ => hσterm i j k))
        _ = d ^ 3 * (nM ^ 2 * S * (O * G)) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    have hs2 : |∑ i, ∑ j, ∫ x in E, φ i x * (a x).mulVec (gv x) j * H i j x| ≤
        d ^ 2 * (nM ^ 2 * S * (O * (Real.sqrt d * Λ * G))) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i, |∑ j, ∫ x in E, φ i x * (a x).mulVec (gv x) j * H i j x|
          ≤ ∑ _i : Fin d, ∑ _j : Fin d, nM ^ 2 * S * (O * (Real.sqrt d * Λ * G)) :=
            Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun j _ => hφterm i j)
        _ = d ^ 2 * (nM ^ 2 * S * (O * (Real.sqrt d * Λ * G))) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    calc |(∑ i, ∑ j, ∑ k, ∫ x in E, σ i x j k * gv x k * H i j x) +
          ∑ i, ∑ j, ∫ x in E, φ i x * (a x).mulVec (gv x) j * H i j x|
        ≤ _ := abs_add_le _ _
      _ ≤ d ^ 3 * (nM ^ 2 * S * (O * G)) + d ^ 2 * (nM ^ 2 * S * (O * (Real.sqrt d * Λ * G))) :=
          add_le_add hs1 hs2
      _ = nM ^ 2 * S * ((d ^ 3 + d ^ 2 * Real.sqrt d * Λ) * O * G) := by ring
  have hdet0 : 0 < |M.det| := abs_pos.2 hdet
  rw [← ball_zero_eq_pdeEuclideanBall hR]
  rw [hcv, abs_mul, abs_of_pos hdet0] at htotal
  rw [mul_assoc]
  calc |∫ y in ball 0 R, v (M.mulVec y) * PDE.euclideanCoordLaplacian χ y|
      = |M.det|⁻¹ * (|M.det| * |∫ y in ball 0 R, v (M.mulVec y) *
          PDE.euclideanCoordLaplacian χ y|) := by
        rw [← mul_assoc, inv_mul_cancel₀ hdet0.ne', one_mul]
    _ ≤ |M.det|⁻¹ * (nM ^ 2 * S * ((d ^ 3 + d ^ 2 * Real.sqrt d * Λ) * O * G)) :=
        mul_le_mul_of_nonneg_left htotal (inv_nonneg.2 hdet0.le)

end QSH
