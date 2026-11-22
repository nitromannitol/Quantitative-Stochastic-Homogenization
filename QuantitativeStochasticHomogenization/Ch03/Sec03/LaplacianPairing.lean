import QuantitativeStochasticHomogenization.Ch03.Sec03.KernelSmoothing

/-!
# The Laplacian pairing from a pairing against second derivatives

Let `u ∈ H¹(B_{r'})` and suppose that `|∫_{B_{r'}} u Δψ| ≤ E S` for every test `ψ` in `B_{r'}` whose
second derivatives are bounded by `S`. For a test `χ` in `B_r` with `r + ℓ ≤ r'` let
`χ̄ = χ * ρ_ℓ`. Then `|∫ u Δχ̄| ≤ E (C ℓ^{-d})^{1/2} ‖Δχ‖_{L²}` by the pointwise bound of the smoothed
second derivatives, and `∫ u Δ(χ - χ̄) = -∑ᵢ ∫ ∂ᵢu (∂ᵢχ - ∂ᵢχ̄)` is at most
`d ℓ ‖∇u‖ ‖Δχ‖_{L²}` by the mollification estimate. This is step 2 of the harmonic approximation
(2) in ball coordinates.
-/

open MeasureTheory Filter Set
open scoped Convolution Topology

noncomputable section

namespace QSH

variable {d : ℕ}

theorem tsupport_sub_subset' (f g : Vec d → ℝ) :
    tsupport (f - g) ⊆ tsupport f ∪ tsupport g :=
  closure_minimal ((Function.support_sub f g).trans (union_subset_union subset_closure
    subset_closure)) (isClosed_closure.union isClosed_closure)

theorem memLp_of_continuous_hasCompactSupport {f : Vec d → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (U : Set (Vec d)) : MemLp f 2 (volume.restrict U) :=
  (hf.memLp_of_hasCompactSupport (μ := volume) (p := 2) hfc).restrict U

/-- **The Laplacian pairing from a pairing against second derivatives** (step 2 of (2)). -/
theorem abs_integral_mul_laplacian_le_of_hessian_pairing {r r' ℓ E G C : ℝ} (hr : 0 < r)
    (hℓ : 0 < ℓ) (hrr : r + ℓ ≤ r') (hG0 : 0 ≤ G) (hC0 : 0 ≤ C)
    (hC : ∀ y : Vec d, PDE.harmonicKernelScaled ℓ y ≤ ℓ⁻¹ ^ d * C)
    {u : Vec d → ℝ} {gu : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict (PDE.euclideanBall 0 r')))
    (hgu : ∀ i, MemLp (fun x => gu x i) 2 (volume.restrict (PDE.euclideanBall 0 r')))
    (hw : HasWeakGradient (PDE.euclideanBall 0 r') u gu)
    (hG : ∀ i, ∫ x in PDE.euclideanBall 0 r', gu x i ^ 2 ≤ G ^ 2)
    (hpair : ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ PDE.euclideanBall 0 r' → ∀ S : ℝ, 0 ≤ S →
      (∀ a b x, |PDE.euclideanCoordSecondDeriv a b ψ x| ≤ S) →
      |∫ x in PDE.euclideanBall 0 r', u x * PDE.euclideanCoordLaplacian ψ x| ≤ E * S)
    {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ PDE.euclideanBall 0 r) :
    |∫ x in PDE.euclideanBall 0 r, u x * PDE.euclideanCoordLaplacian χ x| ≤
      (d * ℓ * G + E * Real.sqrt (ℓ⁻¹ ^ d * C)) *
        Real.sqrt (∫ x in PDE.euclideanBall 0 r, PDE.euclideanCoordLaplacian χ x ^ 2) := by
  classical
  set B := PDE.euclideanBall (0 : Vec d) r with hBdef
  set B' := PDE.euclideanBall (0 : Vec d) r' with hB'def
  have hr' : 0 < r' := by linarith
  have hBB : B ⊆ B' := PDE.euclideanBall_mono hr.le (by linarith)
  set Δχ := PDE.euclideanCoordLaplacian χ with hΔχdef
  set χb := kernelSmooth ℓ χ with hχbdef
  have hχb : ContDiff ℝ (⊤ : ℕ∞) χb := contDiff_kernelSmooth hχ hχc
  have hχbc : HasCompactSupport χb := hasCompactSupport_kernelSmooth hℓ hχc
  have hχbs : tsupport χb ⊆ B' :=
    (tsupport_kernelSmooth_subset hℓ hr hχc hχs).trans
      (PDE.euclideanBall_mono (by linarith) hrr)
  set L := Real.sqrt (∫ x, Δχ x ^ 2) with hLdef
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hΔzero : ∀ x, x ∉ B → Δχ x = 0 := fun x hx =>
    euclideanCoordLaplacian_eq_zero_of_notMem_tsupport fun h => hx (hχs h)
  have hLB : ∫ x in B, Δχ x ^ 2 = ∫ x, Δχ x ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hΔzero x hx]; ring
  have hUB : ∫ x in B, u x * Δχ x = ∫ x in B', u x * Δχ x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hΔzero x hx]; ring),
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [hΔzero x fun h => hx (hBB h)]; ring)]
  rw [hLB, hUB]
  -- the smoothed part
  set S := Real.sqrt (ℓ⁻¹ ^ d * C) * L with hSdef
  have hS0 : 0 ≤ S := by positivity
  have hsup : ∀ a b x, |PDE.euclideanCoordSecondDeriv a b χb x| ≤ S := by
    intro a b x
    rw [hχbdef, euclideanCoordSecondDeriv_kernelSmooth hχ hχc a b]
    have h1 := sq_kernelSmooth_le hℓ hC (contDiff_euclideanCoordSecondDeriv hχ a b).continuous
      (hasCompactSupport_euclideanCoordSecondDeriv hχc a b) x
    have h2 := integral_sq_secondDeriv_le hχ hχc a b
    rw [← Real.sqrt_sq_eq_abs]
    calc Real.sqrt (kernelSmooth ℓ (PDE.euclideanCoordSecondDeriv a b χ) x ^ 2)
        ≤ Real.sqrt (ℓ⁻¹ ^ d * C * ∫ y, PDE.euclideanCoordSecondDeriv a b χ y ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ ≤ Real.sqrt (ℓ⁻¹ ^ d * C * ∫ y, Δχ y ^ 2) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h2 (by positivity))
      _ = S := by rw [Real.sqrt_mul (by positivity)]
  have hbar := hpair χb hχb hχbc hχbs S hS0 hsup
  -- the difference
  set φ : Fin d → Vec d → ℝ := fun i =>
    PDE.euclideanCoordDeriv i χ - PDE.euclideanCoordDeriv i χb with hφdef
  have hφsmooth : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (φ i) := fun i =>
    (PDE.contDiff_euclideanCoordDeriv hχ i).sub (PDE.contDiff_euclideanCoordDeriv hχb i)
  have hφc : ∀ i, HasCompactSupport (φ i) := fun i =>
    (PDE.hasCompactSupport_euclideanCoordDeriv hχc i).sub
      (PDE.hasCompactSupport_euclideanCoordDeriv hχbc i)
  have hφs : ∀ i, tsupport (φ i) ⊆ B' := fun i =>
    (tsupport_sub_subset' _ _).trans (union_subset
      ((PDE.tsupport_euclideanCoordDeriv_subset_tsupport i χ).trans (hχs.trans hBB))
      ((PDE.tsupport_euclideanCoordDeriv_subset_tsupport i χb).trans hχbs))
  have hφtest : ∀ i, IsSpatialTest B' (φ i) := fun i => ⟨hφsmooth i, hφc i, hφs i⟩
  have hdφ : ∀ i x, coordinateDerivative i (φ i) x =
      PDE.euclideanCoordSecondDeriv i i χ x - PDE.euclideanCoordSecondDeriv i i χb x := by
    intro i x
    have h1 := ((PDE.contDiff_euclideanCoordDeriv hχ i).differentiable (by simp)) x
    have h2 := ((PDE.contDiff_euclideanCoordDeriv hχb i).differentiable (by simp)) x
    simp only [coordinateDerivative, hφdef, fderiv_sub h1 h2]
    rfl
  have hlap : ∀ x, Δχ x - PDE.euclideanCoordLaplacian χb x =
      ∑ i, coordinateDerivative i (φ i) x := by
    intro x
    simp only [hΔχdef, PDE.euclideanCoordLaplacian, hdφ, Finset.sum_sub_distrib]
  have hcontdφ : ∀ i, Continuous fun x => coordinateDerivative i (φ i) x := fun i =>
    continuous_coordinateDerivative ((hφsmooth i).of_le (by simp)) i
  have hcsdφ : ∀ i, HasCompactSupport fun x => coordinateDerivative i (φ i) x := fun i =>
    PDE.hasCompactSupport_euclideanCoordDeriv (hφc i) i
  have hmemdφ : ∀ i, MemLp (fun x => coordinateDerivative i (φ i) x) 2 (volume.restrict B') :=
    fun i => memLp_of_continuous_hasCompactSupport (hcontdφ i) (hcsdφ i) B'
  have hmemφ : ∀ i, MemLp (φ i) 2 (volume.restrict B') := fun i =>
    memLp_of_continuous_hasCompactSupport (hφsmooth i).continuous (hφc i) B'
  have hmemΔb : MemLp (PDE.euclideanCoordLaplacian χb) 2 (volume.restrict B') :=
    memLp_of_continuous_hasCompactSupport (continuous_euclideanCoordLaplacian hχb)
      (hasCompactSupport_euclideanCoordLaplacian hχbc) B'
  have hsplit : ∫ x in B', u x * Δχ x = (∫ x in B', u x * PDE.euclideanCoordLaplacian χb x) +
      ∑ i, ∫ x in B', u x * coordinateDerivative i (φ i) x := by
    have h1 : ∫ x in B', u x * Δχ x = ∫ x in B', (u x * PDE.euclideanCoordLaplacian χb x +
        ∑ i, u x * coordinateDerivative i (φ i) x) :=
      integral_congr_ae (Eventually.of_forall fun x => by
        change u x * Δχ x = u x * PDE.euclideanCoordLaplacian χb x +
          ∑ i, u x * coordinateDerivative i (φ i) x
        rw [← Finset.mul_sum, ← hlap x]
        ring)
    rw [h1, integral_add (integrable_mul_of_memLp_two hu hmemΔb)
        (integrable_finsetSum _ fun i _ => integrable_mul_of_memLp_two hu (hmemdφ i)),
      integral_finsetSum _ fun i _ => integrable_mul_of_memLp_two hu (hmemdφ i)]
  have hparts : ∀ i, ∫ x in B', u x * coordinateDerivative i (φ i) x =
      -∫ x in B', gu x i * φ i x := fun i => (hw i).2.2 (φ i) (hφtest i)
  -- the mollification estimate for each `∂ᵢχ`
  have hρbound : ∀ i, ∫ x, φ i x ^ 2 ≤ ℓ ^ 2 * L ^ 2 := by
    intro i
    have hφeq : ∀ x, φ i x = PDE.euclideanCoordDeriv i χ x -
        ∫ y, PDE.harmonicKernelScaled ℓ y * PDE.euclideanCoordDeriv i χ (x - y) := by
      intro x
      simp only [hφdef, Pi.sub_apply, hχbdef, euclideanCoordDeriv_kernelSmooth hχ hχc i,
        kernelSmooth_apply]
    have hmoll := integral_sq_sub_mollify_le (f := PDE.euclideanCoordDeriv i χ)
      ((PDE.contDiff_euclideanCoordDeriv hχ i).of_le (by simp))
      (PDE.hasCompactSupport_euclideanCoordDeriv hχc i)
      (PDE.harmonicKernelScaled_smooth ℓ).continuous (PDE.harmonicKernelScaled_hasCompactSupport hℓ)
      (PDE.harmonicKernelScaled_nonneg hℓ) (PDE.harmonicKernelScaled_integral_eq_one hℓ)
      (fun y hy => harmonicKernelScaled_ne_zero_imp hℓ hy)
    have hgrad : ∫ x, gradSq (PDE.euclideanCoordDeriv i χ) x ≤ L ^ 2 := by
      rw [hLdef, Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _),
        ← sum_integral_sq_secondDeriv_eq hχ hχc]
      have hint : ∀ j, Integrable fun x => PDE.euclideanCoordSecondDeriv i j χ x ^ 2 := by
        intro j
        refine ((contDiff_euclideanCoordSecondDeriv hχ i j).continuous.pow 2).integrable_of_hasCompactSupport ?_
        have h := (hasCompactSupport_euclideanCoordSecondDeriv hχc i j).mul_left
          (f := PDE.euclideanCoordSecondDeriv i j χ)
        convert h using 1
        funext x
        simp [pow_two]
      have e : ∫ x, gradSq (PDE.euclideanCoordDeriv i χ) x =
          ∑ j, ∫ x, PDE.euclideanCoordSecondDeriv i j χ x ^ 2 := by
        rw [← integral_finsetSum _ fun j _ => hint j]
        rfl
      rw [e]
      exact Finset.single_le_sum
        (f := fun i => ∑ j, ∫ x, PDE.euclideanCoordSecondDeriv i j χ x ^ 2)
        (fun i _ => Finset.sum_nonneg fun j _ => integral_nonneg fun x => sq_nonneg _)
        (Finset.mem_univ i)
    calc ∫ x, φ i x ^ 2
        = ∫ x, (PDE.euclideanCoordDeriv i χ x -
            ∫ y, PDE.harmonicKernelScaled ℓ y * PDE.euclideanCoordDeriv i χ (x - y)) ^ 2 :=
          integral_congr_ae (Eventually.of_forall fun x => by
            change φ i x ^ 2 = _
            rw [hφeq x])
      _ ≤ ℓ ^ 2 * ∫ x, gradSq (PDE.euclideanCoordDeriv i χ) x := hmoll
      _ ≤ ℓ ^ 2 * L ^ 2 := mul_le_mul_of_nonneg_left hgrad (sq_nonneg _)
  have hterm : ∀ i, |∫ x in B', gu x i * φ i x| ≤ G * (ℓ * L) := by
    intro i
    refine (abs_integral_mul_le_sqrt_mul_sqrt (hgu i) (hmemφ i)).trans ?_
    refine mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) hG0
    · calc Real.sqrt (∫ x in B', gu x i ^ 2) ≤ Real.sqrt (G ^ 2) := Real.sqrt_le_sqrt (hG i)
        _ = G := Real.sqrt_sq hG0
    · have hφ2 : Integrable fun x => φ i x ^ 2 := by
        refine ((hφsmooth i).continuous.pow 2).integrable_of_hasCompactSupport ?_
        have h := (hφc i).mul_left (f := φ i)
        convert h using 1
        funext x
        simp [pow_two]
      calc Real.sqrt (∫ x in B', φ i x ^ 2) ≤ Real.sqrt ((ℓ * L) ^ 2) := by
            refine Real.sqrt_le_sqrt ?_
            calc ∫ x in B', φ i x ^ 2 ≤ ∫ x, φ i x ^ 2 :=
                  setIntegral_le_integral hφ2 (Eventually.of_forall fun x => sq_nonneg _)
              _ ≤ ℓ ^ 2 * L ^ 2 := hρbound i
              _ = (ℓ * L) ^ 2 := by ring
        _ = ℓ * L := Real.sqrt_sq (by positivity)
  have hsum : |∑ i, ∫ x in B', u x * coordinateDerivative i (φ i) x| ≤ d * ℓ * G * L := by
    simp_rw [hparts]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |-∫ x in B', gu x i * φ i x| ≤ ∑ _i : Fin d, G * (ℓ * L) :=
          Finset.sum_le_sum fun i _ => by rw [abs_neg]; exact hterm i
      _ = d * ℓ * G * L := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  rw [hsplit]
  calc |(∫ x in B', u x * PDE.euclideanCoordLaplacian χb x) +
        ∑ i, ∫ x in B', u x * coordinateDerivative i (φ i) x|
      ≤ |∫ x in B', u x * PDE.euclideanCoordLaplacian χb x| +
          |∑ i, ∫ x in B', u x * coordinateDerivative i (φ i) x| := abs_add_le _ _
    _ ≤ E * S + d * ℓ * G * L := add_le_add hbar hsum
    _ = (d * ℓ * G + E * Real.sqrt (ℓ⁻¹ ^ d * C)) * L := by rw [hSdef]; ring

end QSH
