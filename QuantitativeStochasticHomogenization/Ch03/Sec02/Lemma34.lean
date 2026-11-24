import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicExpansionBallProof
import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicExpansionRoot
import QuantitativeStochasticHomogenization.Ch03.Sec03.ScalarRmsCalculus
import QuantitativeStochasticHomogenization.Ch03.Sec03.ExcessIteration
import QuantitativeStochasticHomogenization.Ch03.Sec03.LinearChangeOfVariables
import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicApproximationData
import QuantitativeStochasticHomogenization.Ch03.Sec03.CorrectedAffine
import QuantitativeStochasticHomogenization.Ch03.Sec03.FirstOrderLiouvilleReduction
import QuantitativeStochasticHomogenization.Ch03.Sec03.QuarterExcessStepReduction
import QuantitativeStochasticHomogenization.Ch03.Sec04.SpatialWeakLocalization
import QuantitativeStochasticHomogenization.Ch04.Sec04.CompactTestFluxBound
import QuantitativeStochasticHomogenization.Ch04.Sec04.HarmonicPairSpace
import QuantitativeStochasticHomogenization.AppC.GehringBallEstimates
import QuantitativeStochasticHomogenization.Ch04.Sec01.Lemma44

/-!
# Lemmas 3.4 and 3.6: the `C^{0,1}`-type iteration

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 3.2. For a symmetric matrix `A` with `1 ≤ A ≤ Λ` (the homogenized matrix `ā`):

* the `A`-harmonic functions on a ball `B_ρ` are approximated by affine functions to second order
  on `B_t`, `t < ρ/√Λ`, with constants depending only on `d` and `Λ`
  (`exists_affine_scalarRms_ball_le`, the case `k = 1` of (3.24), from the harmonic expansion on
  balls `harmonicExpansionBall` and the change of variables `x = M y`, `M Mᵀ = A`);
* Lemma 3.6 for `k = 1` (`lemma_3_6_one`, and the form with a given affine function,
  `exists_affine_improvement`);
* Lemma 3.4 (`lemma_3_4`): if `u` has an `A`-harmonic approximation on every ball `B_r`,
  `r ∈ [X, R/2]`, with relative error `K r^{-α}` on `B_{r/2}`, then
  `r⁻¹ ‖u - (u)_{B_r}‖_{L̲²(B_r)} ≤ C R⁻¹ ‖u - (u)_{B_R}‖_{L̲²(B_R)}` for `r ∈ [X, R]`.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

section Geometry

theorem mem_matrixEllipsoid_iff {M : Mat d} (hdet : M.det ≠ 0) {t : ℝ} {x : Vec d} :
    x ∈ matrixEllipsoid M t ↔ euclideanNorm (M⁻¹.mulVec x) < t := by
  have hu : IsUnit M.det := isUnit_iff_ne_zero.2 hdet
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu,
      Matrix.one_mulVec]
    simpa [ball] using hy
  · intro h
    refine ⟨M⁻¹.mulVec x, by simpa [ball] using h, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
      Matrix.one_mulVec]

theorem euclideanSq_inv_mulVec_eq (M : Mat d) (x : Vec d) :
    euclideanSq (M⁻¹.mulVec x) = dot x ((M * M.transpose)⁻¹.mulVec x) := by
  rw [Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv, ← Matrix.mulVec_mulVec]
  unfold euclideanSq
  rw [dot_eq_dotProduct, dot_eq_dotProduct, Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose]

/-- For `M Mᵀ = A` with `1 ≤ A ≤ Λ`: `B_t ⊆ M B_t`. -/
theorem ball_subset_matrixEllipsoid {M : Mat d} (hdet : M.det ≠ 0)
    (hA : HomogenizedMatrixBounds (M * M.transpose) Λ) (t : ℝ) :
    ball 0 t ⊆ matrixEllipsoid M t := by
  intro x hx
  rw [mem_matrixEllipsoid_iff hdet]
  have hx' : euclideanNorm x < t := by simpa [ball] using hx
  have h1 := (dot_inv_mulVec_nonneg_le (fun ξ => (hA ξ).1) x).2
  rw [← euclideanSq_inv_mulVec_eq] at h1
  unfold euclideanNorm at hx' ⊢
  exact lt_of_le_of_lt (Real.sqrt_le_sqrt h1) hx'

/-- For `M Mᵀ = A` with `1 ≤ A ≤ Λ`: `M B_t ⊆ B_{√Λ t}`. -/
theorem matrixEllipsoid_subset_ball_sqrt {M : Mat d} (hdet : M.det ≠ 0) (hΛ : 0 < Λ)
    (hA : HomogenizedMatrixBounds (M * M.transpose) Λ) (hsym : (M * M.transpose).transpose =
      M * M.transpose) (t : ℝ) :
    matrixEllipsoid M t ⊆ ball 0 (Real.sqrt Λ * t) := by
  intro x hx
  rw [mem_matrixEllipsoid_iff hdet] at hx
  have h1 := euclideanSq_le_mul_dot_inv_mulVec hA hsym hΛ.le x
  rw [← euclideanSq_inv_mulVec_eq] at h1
  have ht : 0 < t := lt_of_le_of_lt (Real.sqrt_nonneg _) hx
  show euclideanNorm (x - 0) < Real.sqrt Λ * t
  rw [sub_zero]
  unfold euclideanNorm at hx ⊢
  have hs : euclideanSq (M⁻¹.mulVec x) < t ^ 2 := (Real.sqrt_lt' ht).mp hx
  have h2 : euclideanSq x < (Real.sqrt Λ * t) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hΛ.le]
    nlinarith
  exact (Real.sqrt_lt' (by positivity)).mpr h2

theorem volume_real_matrixEllipsoid (M : Mat d) (t : ℝ) :
    volume.real (matrixEllipsoid M t) = |M.det| * volume.real (ball (0 : Vec d) t) := by
  rw [measureReal_def, measureReal_def, volume_matrixEllipsoid, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _)]

theorem volume_real_ball_mul {L : ℝ} (hL : 0 < L) (t : ℝ) :
    volume.real (ball (0 : Vec d) (L * t)) = L ^ d * volume.real (ball (0 : Vec d) t) := by
  rw [measureReal_def, measureReal_def, volume_ball_zero_mul hL, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]

/-- `|det M| ≥ 1` when `M Mᵀ ≥ 1`. -/
theorem one_le_abs_det {M : Mat d} (hdet : M.det ≠ 0)
    (hA : HomogenizedMatrixBounds (M * M.transpose) Λ) : 1 ≤ |M.det| := by
  have hsub := ball_subset_matrixEllipsoid hdet hA 1
  have hle : volume.real (ball (0 : Vec d) 1) ≤ volume.real (matrixEllipsoid M 1) :=
    measureReal_mono hsub (volume_matrixEllipsoid_lt_top M 1).ne
  rw [volume_real_matrixEllipsoid] at hle
  have hpos := volume_real_ball_pos (0 : Vec d) one_pos
  nlinarith

end Geometry

section Expansion

/-- Restriction of a `B`-harmonic function to a smaller set. -/
theorem IsL2HarmonicOn.mono {B : Mat d} {U V : Set (Vec d)} (hVU : V ⊆ U) {h : Vec d → ℝ}
    (hh : IsL2HarmonicOn B U h) : IsL2HarmonicOn B V h := by
  obtain ⟨hL2, gh, hg, hw, hdiv⟩ := hh
  exact ⟨hL2.mono_measure (Measure.restrict_mono hVU le_rfl), gh,
    fun i => (hg i).mono_measure (Measure.restrict_mono hVU le_rfl), hasWeakGradient_mono hVU hw,
    hdiv.mono' hVU⟩

/-- The Frobenius norm of `M⁻¹ᵀ` is at most `√d` when `M Mᵀ ≥ 1`. -/
theorem sum_sq_inv_transpose_le {M : Mat d} (hA : HomogenizedMatrixBounds (M * M.transpose) Λ) :
    ∑ i, ∑ j, (M⁻¹).transpose i j ^ 2 ≤ d := by
  have hcol : ∀ i, ∑ j, (M⁻¹).transpose i j ^ 2 = euclideanSq (M⁻¹.mulVec (unitVector i)) := by
    intro i
    rw [unitVector, Matrix.mulVec_single_one]
    simp only [euclideanSq, dot, Matrix.transpose_apply, sq]
    exact Finset.sum_congr rfl fun j _ => rfl
  have hle : ∀ i, euclideanSq (M⁻¹.mulVec (unitVector i)) ≤ 1 := by
    intro i
    rw [euclideanSq_inv_mulVec_eq]
    have h1 := (dot_inv_mulVec_nonneg_le (fun ξ => (hA ξ).1) (unitVector i)).2
    have h2 : euclideanSq (unitVector i : Vec d) = 1 := by
      simp [euclideanSq, dot, unitVector, Pi.single_apply]
    linarith
  calc ∑ i, ∑ j, (M⁻¹).transpose i j ^ 2 = ∑ i, euclideanSq (M⁻¹.mulVec (unitVector i)) :=
        Finset.sum_congr rfl fun i _ => hcol i
    _ ≤ ∑ _i : Fin d, (1 : ℝ) := Finset.sum_le_sum fun i _ => hle i
    _ = d := by simp

/-- **The harmonic expansion of `A`-harmonic functions on balls** ((3.24) for `k = 1`): for a
symmetric `A` with `1 ≤ A ≤ Λ` and `h` `A`-harmonic in `B_ρ`, there is an affine function
`c + q·x` with `‖h - c - q·x‖_{L̲²(B_t)} ≤ C (t/ρ)² ‖h‖_{L̲²(B_ρ)}` for `t < ρ/√Λ` and
`|q| ≤ C ρ⁻¹ ‖h‖_{L̲²(B_ρ)}`, with `C` depending only on `d` and `Λ`. -/
theorem exists_affine_scalarRms_ball_le (hd : 2 ≤ d) (hΛ : 1 ≤ Λ) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ A : Mat d, A.transpose = A → HomogenizedMatrixBounds A Λ →
      ∀ ρ : ℝ, 0 < ρ → ∀ h : Vec d → ℝ, IsL2HarmonicOn A (ball 0 ρ) h →
      ∃ (c : ℝ) (q : Vec d),
        (∀ t : ℝ, 0 < t → t < ρ / Real.sqrt Λ →
          scalarRms volume (ball 0 t) (fun x => h x - (c + dot q x)) ≤
            C₁ * (t / ρ) ^ 2 * scalarRms volume (ball 0 ρ) h) ∧
        euclideanNorm q ≤ C₁ / ρ * scalarRms volume (ball 0 ρ) h := by
  obtain ⟨C, hC, hball⟩ := harmonicExpansionBall d hd
  have hΛ0 : 0 < Λ := by linarith
  have hsΛ : 0 < Real.sqrt Λ := Real.sqrt_pos.2 hΛ0
  set κ : ℝ := Real.sqrt (Real.sqrt Λ ^ d) with hκ
  have hκ0 : 0 ≤ κ := Real.sqrt_nonneg _
  refine ⟨(Λ + Real.sqrt d * C * Real.sqrt Λ) * κ, by positivity, ?_⟩
  intro A hsym hA ρ hρ h hh
  have hpos : ∀ ξ : Vec d, ξ ≠ 0 → 0 < dot ξ (A.mulVec ξ) := by
    intro ξ hξ
    have h1 := (hA ξ).1
    have h2 : 0 < euclideanSq ξ := by
      rcases (BaseExponent.euclideanSq_nonneg ξ).eq_or_lt with h0 | h0
      · exfalso
        apply hξ
        funext i
        have hsum : ∑ j, ξ j * ξ j = 0 := h0.symm
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (ξ j))).mp hsum i
          (Finset.mem_univ i)
        simpa using this
      · exact h0
    linarith
  obtain ⟨M, hdet, hMM⟩ := exists_mul_transpose_eq_symmPart hpos
  have hMA : M * M.transpose = A := by
    rw [hMM, hsym, ← two_smul ℝ A, smul_smul]
    norm_num
  have hA' : HomogenizedMatrixBounds (M * M.transpose) Λ := by rw [hMA]; exact hA
  have hsym' : (M * M.transpose).transpose = M * M.transpose := by rw [hMA]; exact hsym
  have hdet1 := one_le_abs_det hdet hA'
  have hdet0 : 0 < |M.det| := by linarith
  set b := ρ / Real.sqrt Λ with hbdef
  have hb : 0 < b := div_pos hρ hsΛ
  have hρb : Real.sqrt Λ * b = ρ := by rw [hbdef]; field_simp
  have hEB : matrixEllipsoid M b ⊆ ball 0 ρ := by
    have := matrixEllipsoid_subset_ball_sqrt hdet hΛ0 hA' hsym' b
    rwa [hρb] at this
  have hhA : IsL2HarmonicOn (M * M.transpose) (ball 0 ρ) h := by rw [hMA]; exact hh
  have hhE : IsL2HarmonicOn (M * M.transpose) (matrixEllipsoid M b) h := hhA.mono hEB
  have hL2 : MemLp h 2 (volume.restrict (ball 0 ρ)) := hh.1
  obtain ⟨c, q, hdec, hq⟩ := hball b hb _ (hhE.comp_matrixEllipsoid hdet)
  -- the ellipsoid `M B_b` against the ball `B_ρ`
  have hvolEB : volume.real (ball (0 : Vec d) ρ) ≤
      (Real.sqrt Λ ^ d / |M.det|) * volume.real (matrixEllipsoid M b) := by
    rw [volume_real_matrixEllipsoid, ← hρb, volume_real_ball_mul hsΛ b]
    apply le_of_eq
    field_simp
  have hEb : scalarRms volume (matrixEllipsoid M b) h ≤
      Real.sqrt (Real.sqrt Λ ^ d / |M.det|) * scalarRms volume (ball 0 ρ) h :=
    scalarRms_le_sqrt_mul_of_subset hEB (volume_matrixEllipsoid_ne_zero hdet hb)
      (volume_ball_ne_top' 0 ρ) hvolEB (by positivity) hL2.integrable_sq
  have hsq : Real.sqrt (Real.sqrt Λ ^ d / |M.det|) ≤ κ := by
    rw [hκ]
    apply Real.sqrt_le_sqrt
    exact div_le_self (by positivity) hdet1
  have hrms0 := scalarRms_nonneg (d := d) (ball 0 ρ) h
  refine ⟨c, (M⁻¹).transpose.mulVec q, fun t ht htb => ?_, ?_⟩
  · have htb' : t ≤ b := htb.le
    have hEtB : matrixEllipsoid M t ⊆ ball 0 ρ := (matrixEllipsoid_mono M htb').trans hEB
    have hmem : MemLp (fun x => h x - (c + dot ((M⁻¹).transpose.mulVec q) x)) 2
        (volume.restrict (matrixEllipsoid M t)) :=
      (hL2.sub (memLp_const c |>.add (memLp_dot_ball _ ρ))).mono_measure
        (Measure.restrict_mono hEtB le_rfl)
    have h1 : scalarRms volume (ball 0 t)
        (fun x => h x - (c + dot ((M⁻¹).transpose.mulVec q) x)) ≤
        Real.sqrt |M.det| * scalarRms volume (matrixEllipsoid M t)
          (fun x => h x - (c + dot ((M⁻¹).transpose.mulVec q) x)) :=
      scalarRms_le_sqrt_mul_of_subset (ball_subset_matrixEllipsoid hdet hA' t)
        (volume_ball_ne_zero' 0 ht) (volume_matrixEllipsoid_lt_top M t).ne
        (volume_real_matrixEllipsoid M t).le (abs_nonneg _) hmem.integrable_sq
    have h2 : scalarRms volume (matrixEllipsoid M t)
        (fun x => h x - (c + dot ((M⁻¹).transpose.mulVec q) x)) ≤
        (t / b) ^ 2 * scalarRms volume (matrixEllipsoid M b) h := by
      rw [scalarRms_matrixEllipsoid_eq hdet t, scalarRms_matrixEllipsoid_eq hdet b]
      have e : (fun y => h (M.mulVec y) - (c + dot ((M⁻¹).transpose.mulVec q) (M.mulVec y))) =
          fun y => h (M.mulVec y) - (c + dot q y) := by
        funext y
        rw [dot_inv_transpose_mulVec hdet]
      rw [e]
      exact hdec t ht htb
    have htb2 : (t / b) ^ 2 = Λ * (t / ρ) ^ 2 := by
      rw [hbdef, div_div_eq_mul_div, div_pow, mul_pow, Real.sq_sqrt hΛ0.le, div_pow]
      ring
    have hdetk : Real.sqrt |M.det| * Real.sqrt (Real.sqrt Λ ^ d / |M.det|) = κ := by
      rw [← Real.sqrt_mul (abs_nonneg _), hκ, mul_div_cancel₀ _ hdet0.ne']
    calc scalarRms volume (ball 0 t) (fun x => h x - (c + dot ((M⁻¹).transpose.mulVec q) x))
        ≤ Real.sqrt |M.det| * ((t / b) ^ 2 * scalarRms volume (matrixEllipsoid M b) h) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _))
      _ ≤ Real.sqrt |M.det| * ((t / b) ^ 2 *
            (Real.sqrt (Real.sqrt Λ ^ d / |M.det|) * scalarRms volume (ball 0 ρ) h)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEb (sq_nonneg _))
            (Real.sqrt_nonneg _)
      _ = Λ * κ * (t / ρ) ^ 2 * scalarRms volume (ball 0 ρ) h := by
          rw [htb2, ← hdetk]
          ring
      _ ≤ (Λ + Real.sqrt d * C * Real.sqrt Λ) * κ * (t / ρ) ^ 2 *
            scalarRms volume (ball 0 ρ) h := by
          gcongr
          have : 0 ≤ Real.sqrt d * C * Real.sqrt Λ := by positivity
          linarith
  · have hfro := sum_sq_inv_transpose_le hA'
    have hn := euclideanNorm_mulVec_le (M⁻¹).transpose q
    have hsd : Real.sqrt (∑ i, ∑ j, (M⁻¹).transpose i j ^ 2) ≤ Real.sqrt d :=
      Real.sqrt_le_sqrt hfro
    have hq' : euclideanNorm q ≤ C / b * scalarRms volume (matrixEllipsoid M b) h := by
      rw [scalarRms_matrixEllipsoid_eq hdet b]
      exact hq
    have hqn : 0 ≤ euclideanNorm q := Real.sqrt_nonneg _
    have hCb : C / b = C * Real.sqrt Λ / ρ := by rw [hbdef]; field_simp
    calc euclideanNorm ((M⁻¹).transpose.mulVec q)
        ≤ Real.sqrt d * euclideanNorm q := hn.trans (mul_le_mul_of_nonneg_right hsd hqn)
      _ ≤ Real.sqrt d * (C / b * (κ * scalarRms volume (ball 0 ρ) h)) := by
          refine mul_le_mul_of_nonneg_left (hq'.trans ?_) (Real.sqrt_nonneg _)
          refine mul_le_mul_of_nonneg_left (hEb.trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_right hsq hrms0
      _ = Real.sqrt d * C * Real.sqrt Λ * κ / ρ * scalarRms volume (ball 0 ρ) h := by
          rw [hCb]
          ring
      _ ≤ (Λ + Real.sqrt d * C * Real.sqrt Λ) * κ / ρ * scalarRms volume (ball 0 ρ) h := by
          gcongr
          linarith

end Expansion

end QSH
