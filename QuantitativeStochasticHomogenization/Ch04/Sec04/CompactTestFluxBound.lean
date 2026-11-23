import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicApproximationProof
import QuantitativeStochasticHomogenization.Ch04.Sec04.BallCaccioppoli
import QuantitativeStochasticHomogenization.Ch04.Sec04.HarmonicPairSpace

/-!
# The pairing of a local solution with second derivatives of compact tests

The first-order estimate behind (3) of the finite-ball estimate of the
proof of Lemma 4.21 in Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*.

Let `v` be `a`-harmonic on `B_T`, and let `F` be a family of first-order correctors `φᵢ` and skew
flux correctors `σᵢ` with homogenized matrix `D` whose oscillations on `B_r`, `r ≥ R₀`, are at most
`C₁ r^{1-μ}`. For a test `ψ` in `B_r`, `r ≤ T`, with second derivatives bounded by `S`, the tensor
identity of the harmonic approximation (on the ball, with correctors centered on `B_r`) and
Cauchy–Schwarz give
`|∫_{B_r} v ∑ᵢⱼ (D eᵢ)ⱼ ∂ⱼ∂ᵢψ| ≤ S (d³ + d²√d Λ) |B_r|^{1/2} C₁ r^{1-μ} ‖∇v‖_{L²(B_r)}`.
The flux correctors take the place of a weak flux pairing.
-/

open MeasureTheory Filter Set

noncomputable section

namespace QSH

variable {d : ℕ}

theorem matrixEllipsoid_one (R : ℝ) : matrixEllipsoid (1 : Mat d) R = ball 0 R := by
  unfold matrixEllipsoid
  simp [Matrix.toLin'_one]

/-- Restriction of a weak divergence to a smaller domain. -/
theorem HasWeakDivergence.mono' {U V : Set (Vec d)} (hVU : V ⊆ U) {F : Vec d → Vec d}
    {h : Vec d → ℝ} (H : HasWeakDivergence U F h) : HasWeakDivergence V F h := by
  refine ⟨fun i => (H.1 i).mono_set hVU, H.2.1.mono_set hVU, fun ψ hψ => ?_⟩
  have hψU : IsSpatialTest U ψ := ⟨hψ.1, hψ.2.1, hψ.2.2.trans hVU⟩
  have h1 := H.2.2 ψ hψU
  have e : ∀ W : Set (Vec d), tsupport ψ ⊆ W →
      ∫ x in W, dot (F x) (gradient ψ x) = ∫ x, dot (F x) (gradient ψ x) := fun W hW => by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have hx' : x ∉ tsupport ψ := fun h => hx (hW h)
    unfold dot gradient
    exact Finset.sum_eq_zero fun k _ => by
      rw [coordinateDerivative_eq_zero_of_notMem_tsupport hx' k, mul_zero]
  rw [e V hψ.2.2, ← e U hψU.2.2, h1, setIntegral_eq_integral_of_tsupport_subset hψU.2.2,
    setIntegral_eq_integral_of_tsupport_subset hψ.2.2]

/-- **The pairing with second derivatives of a test on a ball**, from the tensor identity. -/
theorem abs_setIntegral_mul_secondOrder_le {Λ : ℝ} (hΛ : 1 ≤ Λ) (a : CoefficientField d Λ)
    (D : Mat d) {R : ℝ} (hR : 0 < R)
    {v : Vec d → ℝ} {gv : Vec d → Vec d}
    (hv : MemLp v 2 (volume.restrict (ball 0 R)))
    (hgv : ∀ i, MemLp (fun x => gv x i) 2 (volume.restrict (ball 0 R)))
    (hwv : HasWeakGradient (ball 0 R) v gv)
    (hdiv : HasWeakDivergence (ball 0 R) (fun x => (a x).mulVec (gv x)) (fun _ => 0))
    {φ : Fin d → Vec d → ℝ} {gφ : Fin d → Vec d → Vec d}
    (hφ : ∀ i, MemLp (φ i) 2 (volume.restrict (ball 0 R)))
    (hgφ : ∀ i l, MemLp (fun x => gφ i x l) 2 (volume.restrict (ball 0 R)))
    (hwφ : ∀ i, HasWeakGradient (ball 0 R) (φ i) (gφ i))
    (hc : ∀ i, MemLp (fun x => x i + φ i x) 2 (volume.restrict (ball 0 R)))
    (hgc : ∀ i l, MemLp (fun x => (unitVector i + gφ i x) l) 2 (volume.restrict (ball 0 R)))
    (hwc : ∀ i, HasWeakGradient (ball 0 R) (fun x => x i + φ i x)
      (fun x => unitVector i + gφ i x))
    (hdivc : ∀ i, HasWeakDivergence (ball 0 R)
      (fun x => (a x).mulVec (unitVector i + gφ i x)) (fun _ => 0))
    {σ : Fin d → Vec d → Mat d} {gσ : Fin d → Fin d → Fin d → Vec d → Vec d}
    (hσ : ∀ i j k, MemLp (fun x => σ i x j k) 2 (volume.restrict (ball 0 R)))
    (hgσ : ∀ i j k l, MemLp (fun x => gσ i j k x l) 2 (volume.restrict (ball 0 R)))
    (hwσ : ∀ i j k, HasWeakGradient (ball 0 R) (fun x => σ i x j k) (gσ i j k))
    (hskew : ∀ i x j k, σ i x j k = -σ i x k j)
    (hflux : ∀ i j, HasWeakDivergence (ball 0 R) (fun x k => σ i x j k)
      (fun x => (a x).mulVec (unitVector i + gφ i x) j - D.mulVec (unitVector i) j))
    {O G : ℝ} (hO0 : 0 ≤ O) (hG0 : 0 ≤ G)
    (hOφ : ∀ i, ∫ x in ball 0 R, φ i x ^ 2 ≤ O ^ 2)
    (hOσ : ∀ i j k, ∫ x in ball 0 R, σ i x j k ^ 2 ≤ O ^ 2)
    (hG : ∫ x in ball 0 R, euclideanSq (gv x) ≤ G ^ 2)
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest (ball 0 R) ψ) {S : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ i j x, |coordinateDerivative j (coordinateDerivative i ψ) x| ≤ S) :
    |∫ x in ball 0 R, v x * ∑ i, ∑ j, D.mulVec (unitVector i) j *
        coordinateDerivative j (coordinateDerivative i ψ) x| ≤
      S * ((d ^ 3 + d ^ 2 * Real.sqrt d * Λ) * O * G) := by
  classical
  have hdet : (1 : Mat d).det ≠ 0 := by simp
  have hE : matrixEllipsoid (1 : Mat d) R = ball 0 R := matrixEllipsoid_one R
  set E := ball (0 : Vec d) R with hEdef
  set H : Fin d → Fin d → Vec d → ℝ := fun i j => coordinateDerivative j (coordinateDerivative i ψ)
    with hHdef
  have hHt : ∀ i j, IsSpatialTest E (H i j) := fun i j =>
    isSpatialTest_coordinateDerivative (isSpatialTest_coordinateDerivative hψ i) j
  have hid := integral_mul_secondOrder_eq_tensor hΛ a hdet hR D (hE ▸ hv) (hE ▸ hgv) (hE ▸ hwv)
    (hE ▸ hdiv) (hE ▸ hφ) (hE ▸ hgφ) (hE ▸ hwφ) (hE ▸ hc) (hE ▸ hgc) (hE ▸ hwc) (hE ▸ hdivc)
    (hE ▸ hσ) (hE ▸ hgσ) (hE ▸ hwσ) hskew (hE ▸ hflux) (hE ▸ hψ)
  rw [hE] at hid
  have hgvk : ∀ k, Real.sqrt (∫ x in E, gv x k ^ 2) ≤ G := fun k =>
    sqrt_integral_sq_le hG0 ((integral_sq_component_le hgv k).trans hG)
  have hq : ∀ j, MemLp (fun x => (a x).mulVec (gv x) j) 2 (volume.restrict E) := fun j =>
    memLp_coefficient_mulVec hΛ a (measurableSet_ball 0 R) hgv j
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
  have hσterm : ∀ i j k, |∫ x in E, σ i x j k * gv x k * H i j x| ≤ S * (O * G) := by
    intro i j k
    refine (abs_integral_mul_mul_le (hσ i j k) (hgv k) (hHt i j) hS0 (hS i j)).trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul (sqrt_integral_sq_le hO0 (hOσ i j k)) (hgvk k)
      (Real.sqrt_nonneg _) hO0) hS0
  have hφterm : ∀ i j, |∫ x in E, φ i x * (a x).mulVec (gv x) j * H i j x| ≤
      S * (O * (Real.sqrt d * Λ * G)) := by
    intro i j
    refine (abs_integral_mul_mul_le (hφ i) (hq j) (hHt i j) hS0 (hS i j)).trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul (sqrt_integral_sq_le hO0 (hOφ i)) (hqj j)
      (Real.sqrt_nonneg _) hO0) hS0
  rw [hid]
  have hs1 : |∑ i, ∑ j, ∑ k, ∫ x in E, σ i x j k * gv x k * H i j x| ≤ d ^ 3 * (S * (O * G)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |∑ j, ∑ k, ∫ x in E, σ i x j k * gv x k * H i j x|
        ≤ ∑ _i : Fin d, ∑ _j : Fin d, ∑ _k : Fin d, S * (O * G) :=
          Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j _ => (Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun k _ => hσterm i j k))
      _ = d ^ 3 * (S * (O * G)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hs2 : |∑ i, ∑ j, ∫ x in E, φ i x * (a x).mulVec (gv x) j * H i j x| ≤
      d ^ 2 * (S * (O * (Real.sqrt d * Λ * G))) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |∑ j, ∫ x in E, φ i x * (a x).mulVec (gv x) j * H i j x|
        ≤ ∑ _i : Fin d, ∑ _j : Fin d, S * (O * (Real.sqrt d * Λ * G)) :=
          Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j _ => hφterm i j)
      _ = d ^ 2 * (S * (O * (Real.sqrt d * Λ * G))) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  calc |(∑ i, ∑ j, ∑ k, ∫ x in E, σ i x j k * gv x k * H i j x) +
        ∑ i, ∑ j, ∫ x in E, φ i x * (a x).mulVec (gv x) j * H i j x|
      ≤ _ := abs_add_le _ _
    _ ≤ d ^ 3 * (S * (O * G)) + d ^ 2 * (S * (O * (Real.sqrt d * Λ * G))) := add_le_add hs1 hs2
    _ = S * ((d ^ 3 + d ^ 2 * Real.sqrt d * Λ) * O * G) := by ring

variable {Λ μ C₁ R₀ : ℝ} {a : CoefficientField d Λ} {D : Mat d}

set_option maxHeartbeats 400000 in
/-- **The pairing of a local solution with second derivatives of a test** on `B_r`, `r ≥ R₀`, for a
family of first-order and flux correctors: the correctors are centered at their means on `B_r`. -/
theorem SublinearCorrectorFamily.abs_setIntegral_mul_secondOrder_le
    (F : SublinearCorrectorFamily a D μ C₁ R₀) (hΛ : 1 ≤ Λ) (hC₁ : 0 ≤ C₁) {T r : ℝ} (hr0 : 0 < r)
    (hR₀r : R₀ ≤ r) (hrT : r ≤ T) (w : LocalHarmonic a 0 T) {ψ : Vec d → ℝ}
    (hψ : IsSpatialTest (ball 0 r) ψ) {S : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ i j x, |coordinateDerivative j (coordinateDerivative i ψ) x| ≤ S) :
    |∫ x in ball 0 r, w.potential x * ∑ i, ∑ j, D.mulVec (unitVector i) j *
        coordinateDerivative j (coordinateDerivative i ψ) x| ≤
      S * ((d ^ 3 + d ^ 2 * Real.sqrt d * Λ) *
        (Real.sqrt (volume.real (ball (0 : Vec d) r)) * (C₁ * r ^ (1 - μ))) *
        Real.sqrt (∫ x in ball 0 r, euclideanSq (w.grad x))) := by
  have hBT : ball (0 : Vec d) r ⊆ ball 0 T := fun x hx => lt_of_lt_of_le hx hrT
  set m : Fin d → ℝ := fun i => ⨍ y in ball (0 : Vec d) r, F.φ i y with hmdef
  set mσ : Fin d → Mat d := fun i j k => ⨍ y in ball (0 : Vec d) r, F.σ i y j k with hmσdef
  set φ' : Fin d → Vec d → ℝ := fun i x => F.φ i x - m i with hφ'def
  set σ' : Fin d → Vec d → Mat d := fun i x j k => F.σ i x j k - mσ i j k with hσ'def
  have hφB : ∀ i, MemLp (φ' i) 2 (volume.restrict (ball (0 : Vec d) r)) := fun i =>
    (F.memLp i r hr0).1.sub (memLp_const (m i))
  have hσB : ∀ i j k, MemLp (fun x => σ' i x j k) 2 (volume.restrict (ball (0 : Vec d) r)) := fun i j k =>
    ((F.memLp i r hr0).2.2 j k).1.sub (memLp_const (mσ i j k))
  have hgφB : ∀ i l, MemLp (fun x => F.gφ i x l) 2 (volume.restrict (ball (0 : Vec d) r)) := fun i l =>
    memLp_component (F.memLp i r hr0).2.1 l
  have hwφ' : ∀ i, HasWeakGradient Set.univ (φ' i) (F.gφ i) := fun i =>
    (F.weak_gradient_φ i).sub_const (m i)
  have hwc' : ∀ i, HasWeakGradient Set.univ (fun x => x i + φ' i x)
      (fun x => unitVector i + F.gφ i x) := by
    intro i
    have h := hasWeakGradient_add (hasWeakGradient_dot (unitVector i)) (hwφ' i)
    have e : (fun x => dot (unitVector i) x + φ' i x) = fun x => x i + φ' i x := by
      funext x
      rw [dot_unitVector_left]
    rw [e] at h
    exact h
  have hmskew : ∀ i j k, mσ i j k = -mσ i k j := by
    intro i j k
    simp only [hmσdef, setAverage_eq, smul_eq_mul]
    rw [← mul_neg, ← integral_neg]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun y => F.skew i y j k)
  have hskew' : ∀ i x j k, σ' i x j k = -σ' i x k j := by
    intro i x j k
    simp only [hσ'def]
    rw [F.skew i x j k, hmskew i j k]
    ring
  have hflux' : ∀ i j, HasWeakDivergence Set.univ (fun x k => σ' i x j k)
      (fun x => (a x).mulVec (unitVector i + F.gφ i x) j - D.mulVec (unitVector i) j) :=
    fun i j => (F.flux i j).sub_const_field (fun k => mσ i j k)
  set O := Real.sqrt (volume.real (ball (0 : Vec d) r)) * (C₁ * r ^ (1 - μ)) with hOdef
  have hvolB0 : 0 < volume.real (ball (0 : Vec d) r) := volume_real_ball_pos 0 hr0
  have hO0 : 0 ≤ O := by positivity
  have hOsq : volume.real (ball (0 : Vec d) r) * (C₁ * r ^ (1 - μ)) ^ 2 = O ^ 2 := by
    rw [hOdef, mul_pow (Real.sqrt _), Real.sq_sqrt measureReal_nonneg]
  have hrmsnn : ∀ f : Vec d → ℝ, 0 ≤ scalarRms volume (ball (0 : Vec d) r) f := fun f => Real.sqrt_nonneg _
  have hOφ : ∀ i, ∫ x in ball (0 : Vec d) r, φ' i x ^ 2 ≤ O ^ 2 := by
    intro i
    have hosc := F.oscillation i r hR₀r
    have hsum : 0 ≤ ∑ j, ∑ k, scalarRms volume (ball 0 r)
        (fun x => F.σ i x j k - ⨍ y in ball 0 r, F.σ i y j k) :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => hrmsnn _
    have hrms : scalarRms volume (ball (0 : Vec d) r) (φ' i) ≤ C₁ * r ^ (1 - μ) := by
      change scalarRms volume (ball 0 r) (fun x => F.φ i x - ⨍ y in ball 0 r, F.φ i y) ≤ _
      linarith
    exact (integral_sq_le_of_scalarRms_le hvolB0 hrms).trans hOsq.le
  have hOσ : ∀ i j k, ∫ x in ball (0 : Vec d) r, σ' i x j k ^ 2 ≤ O ^ 2 := by
    intro i j k
    have hosc := F.oscillation i r hR₀r
    have h1 : scalarRms volume (ball 0 r)
        (fun x => F.σ i x j k - ⨍ y in ball 0 r, F.σ i y j k) ≤
        ∑ j, ∑ k, scalarRms volume (ball 0 r)
          (fun x => F.σ i x j k - ⨍ y in ball 0 r, F.σ i y j k) := by
      refine (Finset.single_le_sum (f := fun k => scalarRms volume (ball 0 r)
        (fun x => F.σ i x j k - ⨍ y in ball 0 r, F.σ i y j k))
        (fun k _ => hrmsnn _) (Finset.mem_univ k)).trans ?_
      exact Finset.single_le_sum (f := fun j => ∑ k, scalarRms volume (ball 0 r)
        (fun x => F.σ i x j k - ⨍ y in ball 0 r, F.σ i y j k))
        (fun j _ => Finset.sum_nonneg fun k _ => hrmsnn _) (Finset.mem_univ j)
    have hrms : scalarRms volume (ball (0 : Vec d) r) (fun x => σ' i x j k) ≤ C₁ * r ^ (1 - μ) := by
      change scalarRms volume (ball 0 r)
        (fun x => F.σ i x j k - ⨍ y in ball 0 r, F.σ i y j k) ≤ _
      linarith [hrmsnn (fun x => F.φ i x - ⨍ y in ball 0 r, F.φ i y)]
    exact (integral_sq_le_of_scalarRms_le hvolB0 hrms).trans hOsq.le
  have hGint : 0 ≤ ∫ x in ball (0 : Vec d) r, euclideanSq (w.grad x) :=
    integral_nonneg fun x => zero_le_euclideanSq _
  have hG : ∫ x in ball (0 : Vec d) r, euclideanSq (w.grad x) ≤
      Real.sqrt (∫ x in ball (0 : Vec d) r, euclideanSq (w.grad x)) ^ 2 := by
    rw [Real.sq_sqrt hGint]
  have hgv : ∀ i, MemLp (fun x => w.grad x i) 2 (volume.restrict (ball (0 : Vec d) r)) := fun i =>
    memLp_mono_set (w.memLp_grad i) hBT
  have hwσ' : ∀ i j k, HasWeakGradient (ball 0 r) (fun x => σ' i x j k) (F.gσ i j k) :=
    fun i j k => ((F.weak_gradient_σ i j k).sub_const (mσ i j k)).mono_univ
  clear_value φ' σ'
  refine _root_.QSH.abs_setIntegral_mul_secondOrder_le (v := w.potential) (gv := w.grad)
    (φ := φ') (gφ := F.gφ) (σ := σ') (gσ := F.gσ) (R := r) hΛ a D hr0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hψ hS0 hS
  · exact memLp_mono_set w.square_integrable hBT
  · exact hgv
  · exact hasWeakGradient_mono hBT w.weak_gradient
  · exact w.harmonic.mono' hBT
  · exact hφB
  · exact hgφB
  · exact fun i => (hwφ' i).mono_univ
  · intro i
    refine ((memLp_coordinate_ball r i).add (hφB i)).ae_eq (Eventually.of_forall fun x => ?_)
    rfl
  · intro i l
    refine ((memLp_const (unitVector i l)).add (hgφB i l)).ae_eq
      (Eventually.of_forall fun x => ?_)
    rfl
  · exact fun i => (hwc' i).mono_univ
  · exact fun i => (F.harmonic i).mono_univ
  · exact hσB
  · exact fun i j k l => memLp_component ((F.memLp i r hr0).2.2 j k).2 l
  · exact hwσ'
  · exact hskew'
  · exact fun i j => (hflux' i j).mono_univ
  · exact hO0
  · exact Real.sqrt_nonneg _
  · exact hOφ
  · exact hOσ
  · exact hG

end QSH
