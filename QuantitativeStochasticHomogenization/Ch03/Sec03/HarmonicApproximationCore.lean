import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicApproximationPairing
import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicProjection

/-!
# The harmonic approximation at one scale

Let `v` be `a`-harmonic with `v, ∇v ∈ L²(E_R)`, `E_R = M B_R`, `M Mᵀ = ½(D + Dᵀ)`, and let the
centred correctors satisfy the hypotheses of the tensor identity with `L²(E_{r'})` norms at
most `O`, where `r' = (1 - η)R`, `r = (1 - 2η)R`, `b = (1 - 3η)R`, `ℓ = η²R`, `0 < η ≤ 1/8`. With the
Caccioppoli bound `G_v = (K_c ∫_{E_R} v²)^{1/2} / (ηR)` of `∇v` on `E_{r'}`, the function
`u = v ∘ M` has `|∫ u Δχ| ≤ ε ‖Δχ‖_{L²}` for tests `χ` in `B_r`, where
`ε = d ℓ (f/|det M|)^{1/2} G_v + |det M|⁻¹ n² (d³ + d² √d Λ) O G_v (C ℓ^{-d})^{1/2}`
(steps 1 and 2), and the projection (step 3) gives an `M Mᵀ`-harmonic `h` on `E_b` with
`∫_{B_b} (u - h ∘ M)² ≤ ε²`.
-/

open MeasureTheory Filter Set

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The Caccioppoli constant of the ellipsoids `E_r ⊆ E_R`, times `(R - r)²`. -/
def ellipsoidCaccioppoliConst (Λ : ℝ) (M : Mat d) : ℝ :=
  4 * Λ * (Real.sqrt (∑ i, ∑ j, (M⁻¹).transpose i j ^ 2) * 32) ^ 2

/-- `∑ₗₖ |(M⁻¹)ₗₖ|`. -/
def inverseEntrySum (M : Mat d) : ℝ := ∑ l, ∑ k, |M⁻¹ l k|

/-- `∑ᵢₖ Mₖᵢ²`. -/
def entrySqSum (M : Mat d) : ℝ := ∑ i, ∑ k, M k i ^ 2

theorem memLp_mono_set {U V : Set (Vec d)} {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict V))
    (hUV : U ⊆ V) : MemLp f 2 (volume.restrict U) :=
  hf.mono_measure (Measure.restrict_mono hUV le_rfl)

/-- **The harmonic approximation at one scale.** -/
theorem exists_harmonic_ball_sq_le {Λ : ℝ} (hd : 0 < d) (hΛ : 1 ≤ Λ) (a : CoefficientField d Λ)
    {M D : Mat d} (hdet : M.det ≠ 0) (hMM : M * M.transpose = (1 / 2 : ℝ) • (D + D.transpose))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ℓ : ℝ, 0 < ℓ → ∀ y : Vec d,
      PDE.harmonicKernelScaled ℓ y ≤ ℓ⁻¹ ^ d * C)
    {R η : ℝ} (hR : 0 < R) (hη : 0 < η) (hη8 : η ≤ 1 / 8)
    {v : Vec d → ℝ} {gv : Vec d → Vec d}
    (hv : MemLp v 2 (volume.restrict (matrixEllipsoid M R)))
    (hgv : ∀ i, MemLp (fun x => gv x i) 2 (volume.restrict (matrixEllipsoid M R)))
    (hwv : HasWeakGradient Set.univ v gv)
    (hdiv : HasWeakDivergence Set.univ (fun x => (a x).mulVec (gv x)) (fun _ => 0))
    {φ : Fin d → Vec d → ℝ} {gφ : Fin d → Vec d → Vec d}
    (hφ : ∀ i, MemLp (φ i) 2 (volume.restrict (matrixEllipsoid M ((1 - η) * R))))
    (hgφ : ∀ i l, MemLp (fun x => gφ i x l) 2 (volume.restrict (matrixEllipsoid M ((1 - η) * R))))
    (hwφ : ∀ i, HasWeakGradient Set.univ (φ i) (gφ i))
    (hc : ∀ i, MemLp (fun x => x i + φ i x) 2 (volume.restrict (matrixEllipsoid M ((1 - η) * R))))
    (hgc : ∀ i l, MemLp (fun x => (unitVector i + gφ i x) l) 2
      (volume.restrict (matrixEllipsoid M ((1 - η) * R))))
    (hwc : ∀ i, HasWeakGradient Set.univ (fun x => x i + φ i x) (fun x => unitVector i + gφ i x))
    (hdivc : ∀ i, HasWeakDivergence Set.univ
      (fun x => (a x).mulVec (unitVector i + gφ i x)) (fun _ => 0))
    {σ : Fin d → Vec d → Mat d} {gσ : Fin d → Fin d → Fin d → Vec d → Vec d}
    (hσ : ∀ i j k, MemLp (fun x => σ i x j k) 2
      (volume.restrict (matrixEllipsoid M ((1 - η) * R))))
    (hgσ : ∀ i j k l, MemLp (fun x => gσ i j k x l) 2
      (volume.restrict (matrixEllipsoid M ((1 - η) * R))))
    (hwσ : ∀ i j k, HasWeakGradient Set.univ (fun x => σ i x j k) (gσ i j k))
    (hskew : ∀ i x j k, σ i x j k = -σ i x k j)
    (hflux : ∀ i j, HasWeakDivergence Set.univ (fun x k => σ i x j k)
      (fun x => (a x).mulVec (unitVector i + gφ i x) j - D.mulVec (unitVector i) j))
    {O : ℝ} (hO0 : 0 ≤ O)
    (hOφ : ∀ i, ∫ x in matrixEllipsoid M ((1 - η) * R), φ i x ^ 2 ≤ O ^ 2)
    (hOσ : ∀ i j k, ∫ x in matrixEllipsoid M ((1 - η) * R), σ i x j k ^ 2 ≤ O ^ 2) :
    ∃ h : Vec d → ℝ,
      IsL2HarmonicOn (M * M.transpose) (matrixEllipsoid M ((1 - 3 * η) * R)) h ∧
      ∫ y in ball 0 ((1 - 3 * η) * R), (v (M.mulVec y) - h (M.mulVec y)) ^ 2 ≤
        (d * (η ^ 2 * R) * (Real.sqrt (entrySqSum M / |M.det|) *
            (Real.sqrt (ellipsoidCaccioppoliConst Λ M * ∫ x in matrixEllipsoid M R, v x ^ 2) /
              (η * R))) +
          |M.det|⁻¹ * inverseEntrySum M ^ 2 * ((d ^ 3 + d ^ 2 * Real.sqrt d * Λ) * O *
            (Real.sqrt (ellipsoidCaccioppoliConst Λ M * ∫ x in matrixEllipsoid M R, v x ^ 2) /
              (η * R))) * Real.sqrt ((η ^ 2 * R)⁻¹ ^ d * C)) ^ 2 := by
  classical
  set r' := (1 - η) * R with hr'def
  set r := (1 - 2 * η) * R with hrdef
  set b := (1 - 3 * η) * R with hbdef
  set ℓ := η ^ 2 * R with hℓdef
  have hr'0 : 0 < r' := by rw [hr'def]; nlinarith
  have hr0 : 0 < r := by rw [hrdef]; nlinarith
  have hb0 : 0 < b := by rw [hbdef]; nlinarith
  have hℓ0 : 0 < ℓ := by positivity
  have hr'R : r' < R := by rw [hr'def]; nlinarith
  have hrr' : r + ℓ ≤ r' := by
    rw [hrdef, hℓdef, hr'def]
    nlinarith
  have hbr : b < r := by rw [hbdef, hrdef]; nlinarith
  have hdet0 : 0 < |M.det| := abs_pos.2 hdet
  set E := matrixEllipsoid M R with hEdef
  set E' := matrixEllipsoid M r' with hE'def
  have hE'E : E' ⊆ E := matrixEllipsoid_mono M hr'R.le
  have hE'o : IsOpen E' := (isOpenBoundedConvexDomain_matrixEllipsoid hdet hr'0).1
  -- step 0: Caccioppoli
  set Kc := ellipsoidCaccioppoliConst Λ M with hKcdef
  set N2 := ∫ x in E, v x ^ 2 with hN2def
  have hN2 : 0 ≤ N2 := integral_nonneg fun x => sq_nonneg _
  have hKc : 0 ≤ Kc := by rw [hKcdef, ellipsoidCaccioppoliConst]; nlinarith [sq_nonneg (Real.sqrt
    (∑ i, ∑ j, (M⁻¹).transpose i j ^ 2) * 32)]
  set Gv := Real.sqrt (Kc * N2) / (η * R) with hGvdef
  have hGv0 : 0 ≤ Gv := by positivity
  have hcacc : ∫ x in E', euclideanSq (gv x) ≤ Gv ^ 2 := by
    have h := caccioppoli_matrixEllipsoid hΛ a hdet hr'0 hr'R hv hgv hwv.mono_univ hdiv.mono_univ 0
    simp only [sub_zero] at h
    have e : R - r' = η * R := by rw [hr'def]; ring
    rw [e, ← hN2def] at h
    refine h.trans (le_of_eq ?_)
    have hηR : η * R ≠ 0 := by positivity
    rw [hGvdef, div_pow, Real.sq_sqrt (mul_nonneg hKc hN2), hKcdef, ellipsoidCaccioppoliConst]
    field_simp
  -- step 1: the pairing in ball coordinates
  set nM := inverseEntrySum M with hnMdef
  set Ep := |M.det|⁻¹ * nM ^ 2 * ((d ^ 3 + d ^ 2 * Real.sqrt d * Λ) * O * Gv) with hEpdef
  have hpair : ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ PDE.euclideanBall 0 r' → ∀ S : ℝ, 0 ≤ S →
      (∀ a b x, |PDE.euclideanCoordSecondDeriv a b ψ x| ≤ S) →
      |∫ y in PDE.euclideanBall 0 r', v (M.mulVec y) * PDE.euclideanCoordLaplacian ψ y| ≤
        Ep * S := by
    intro ψ hψ hψc hψs S hS0 hS
    have h := abs_integral_ball_mul_laplacian_le hΛ a hdet hMM hr'0 (memLp_mono_set hv hE'E)
      (fun i => memLp_mono_set (hgv i) hE'E) hwv.mono_univ hdiv.mono_univ hφ hgφ
      (fun i => (hwφ i).mono_univ) hc hgc (fun i => (hwc i).mono_univ) (fun i => (hdivc i).mono_univ)
      hσ hgσ (fun i j k => (hwσ i j k).mono_univ) hskew (fun i j => (hflux i j).mono_univ) hO0
      hGv0 hOφ hOσ hcacc hψ hψc hψs hS0 hS
    refine h.trans (le_of_eq ?_)
    rw [hEpdef, hnMdef, inverseEntrySum]
    ring
  -- the function `u = v ∘ M` on `B_{r'}`
  set u : Vec d → ℝ := fun y => v (M.mulVec y) with hudef
  set gu : Vec d → Vec d := fun y => M.transpose.mulVec (gv (M.mulVec y)) with hgudef
  have hB' : ball (0 : Vec d) r' = PDE.euclideanBall 0 r' := ball_zero_eq_pdeEuclideanBall hr'0
  have hu : MemLp u 2 (volume.restrict (PDE.euclideanBall 0 r')) := by
    rw [← hB']
    refine MemLp.comp_matrixEllipsoid hdet ?_
    rw [← matrixEllipsoid_eq_image hdet]
    exact memLp_mono_set hv hE'E
  have hgvB : ∀ k, MemLp (fun y => gv (M.mulVec y) k) 2 (volume.restrict (ball (0 : Vec d) r')) :=
    fun k => by
      refine MemLp.comp_matrixEllipsoid hdet (h := fun x => gv x k) ?_
      rw [← matrixEllipsoid_eq_image hdet]
      exact memLp_mono_set (hgv k) hE'E
  have hguB : ∀ i, MemLp (fun y => gu y i) 2 (volume.restrict (ball (0 : Vec d) r')) := by
    intro i
    have h := memLp_finsetSum (Finset.univ : Finset (Fin d)) fun k _ => (hgvB k).const_mul (M k i)
    refine h.ae_eq (Eventually.of_forall fun y => ?_)
    simp only [hgudef, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  have hgu : ∀ i, MemLp (fun y => gu y i) 2 (volume.restrict (PDE.euclideanBall 0 r')) := by
    rw [← hB']
    exact hguB
  have hwu : HasWeakGradient (PDE.euclideanBall 0 r') u gu := by
    rw [← hB']
    exact (hwv.mono_univ (U := matrixEllipsoid M r')).comp_matrixEllipsoid hdet
  set G := Real.sqrt (entrySqSum M / |M.det|) * Gv with hGdef
  have hG0 : 0 ≤ G := by positivity
  have hfM : 0 ≤ entrySqSum M := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    sq_nonneg _
  have hGbound : ∀ i, ∫ y in PDE.euclideanBall 0 r', gu y i ^ 2 ≤ G ^ 2 := by
    intro i
    rw [← hB']
    have hint : Integrable (fun y => euclideanSq (gv (M.mulVec y))) (volume.restrict (ball 0 r')) := by
      have := integrable_finsetSum (Finset.univ : Finset (Fin d)) fun l _ => (hgvB l).integrable_sq
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only [euclideanSq, dot, pow_two]
    have hpt : ∀ y, gu y i ^ 2 ≤ entrySqSum M * euclideanSq (gv (M.mulVec y)) := by
      intro y
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => M k i) (gv (M.mulVec y))
      have e1 : gu y i = ∑ k, M k i * gv (M.mulVec y) k := by
        simp only [hgudef, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      have e2 : euclideanSq (gv (M.mulVec y)) = ∑ k, gv (M.mulVec y) k ^ 2 := by
        unfold euclideanSq dot
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [e1, e2]
      refine h.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      exact Finset.single_le_sum (f := fun i => ∑ k, M k i ^ 2)
        (fun i _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    have hcv := setIntegral_matrixEllipsoid hdet r' (fun x => euclideanSq (gv x))
    calc ∫ y in ball 0 r', gu y i ^ 2
        ≤ ∫ y in ball 0 r', entrySqSum M * euclideanSq (gv (M.mulVec y)) :=
          integral_mono (hguB i).integrable_sq (hint.const_mul _) hpt
      _ = entrySqSum M * |M.det|⁻¹ * ∫ x in E', euclideanSq (gv x) := by
          rw [integral_const_mul, hcv]
          field_simp
      _ ≤ entrySqSum M * |M.det|⁻¹ * Gv ^ 2 :=
          mul_le_mul_of_nonneg_left hcacc (by positivity)
      _ = G ^ 2 := by
          rw [hGdef, mul_pow, Real.sq_sqrt (by positivity), div_eq_mul_inv]
  -- step 2: the Laplacian pairing
  have hBE : ∀ χ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      tsupport χ ⊆ PDE.euclideanBall 0 r →
      |∫ x in PDE.euclideanBall 0 r, u x * PDE.euclideanCoordLaplacian χ x| ≤
        (d * ℓ * G + Ep * Real.sqrt (ℓ⁻¹ ^ d * C)) *
          Real.sqrt (∫ x in PDE.euclideanBall 0 r, PDE.euclideanCoordLaplacian χ x ^ 2) :=
    fun χ hχ hχc hχs =>
      abs_integral_mul_laplacian_le_of_hessian_pairing hr0 hℓ0 hrr' hG0 hC0 (hC ℓ hℓ0) hu hgu hwu
        hGbound hpair hχ hχc hχs
  -- step 3: projection
  have hε0 : 0 ≤ d * ℓ * G + Ep * Real.sqrt (ℓ⁻¹ ^ d * C) := by
    have : 0 ≤ Ep := by rw [hEpdef]; positivity
    positivity
  have hBr' : PDE.euclideanBall (0 : Vec d) r ⊆ PDE.euclideanBall 0 r' :=
    PDE.euclideanBall_mono hr0.le (by linarith)
  obtain ⟨w, hwc', hwΔ, hwsq⟩ := exists_harmonic_sub_sq_le_of_laplacian_pairing hd hb0 hbr hε0
    (memLp_mono_set hu hBr') hBE
  refine ⟨fun x => w (M⁻¹.mulVec x), isL2HarmonicOn_comp_inv hdet hb0 hwc' hwΔ, ?_⟩
  have e : ∀ y, w (M⁻¹.mulVec (M.mulVec y)) = w y := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.2 hdet),
      Matrix.one_mulVec]
  simp only [e]
  rw [ball_zero_eq_pdeEuclideanBall hb0]
  exact hwsq

end QSH
