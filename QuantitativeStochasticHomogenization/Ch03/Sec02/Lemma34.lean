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

section Improvement

theorem ball_zero_subset_ball_zero {r t : ℝ} (hrt : r ≤ t) : ball (0 : Vec d) r ⊆ ball 0 t :=
  fun _ hx => lt_of_lt_of_le hx hrt

theorem memLp_affine_ball (c : ℝ) (q : Vec d) (ρ : ℝ) :
    MemLp (fun x => c + dot q x) 2 (volume.restrict (ball (0 : Vec d) ρ)) :=
  (memLp_const c).add (memLp_dot_ball q ρ)

/-- An `A`-harmonic function minus an affine function is `A`-harmonic. -/
theorem IsL2HarmonicOn.sub_affine {A : Mat d} {ρ : ℝ} {w : Vec d → ℝ}
    (hw : IsL2HarmonicOn A (ball 0 ρ) w) (c : ℝ) (q : Vec d) :
    IsL2HarmonicOn A (ball 0 ρ) (fun x => w x - (c + dot q x)) := by
  obtain ⟨hL2, g, hg, hgrad, hdiv⟩ := hw
  refine ⟨hL2.sub (memLp_affine_ball c q ρ), fun x => g x - q, fun i => (hg i).sub (memLp_const _),
    ?_, ?_⟩
  · have h1 : HasWeakGradient (ball 0 ρ) (fun x => -c + dot (-q) x) (fun _ => 0 + -q) :=
      hasWeakGradient_mono (subset_univ _)
        (hasWeakGradient_add (hasWeakGradient_const (-c)) (hasWeakGradient_dot (-q)))
    have h2 := hasWeakGradient_add hgrad h1
    convert h2 using 1
    · funext x
      simp only [dot_eq_dotProduct, neg_dotProduct]
      ring
    · funext x
      simp only [zero_add, sub_eq_add_neg]
  · have h3 := hasWeakDivergence_add hdiv
      ((hasWeakDivergence_const_field (-(A.mulVec q))).mono' (subset_univ (ball (0 : Vec d) ρ)))
    convert h3 using 1
    · funext x
      rw [Matrix.mulVec_sub, sub_eq_add_neg]
    · funext x
      simp

/-- The mean minimizes the `L̲²` distance to constants. -/
theorem scalarRms_sub_setAverage_le {U : Set (Vec d)} (hU : volume U ≠ ⊤) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict U)) (m : ℝ) :
    scalarRms volume U (fun x => u x - ⨍ y in U, u y) ≤ scalarRms volume U (fun x => u x - m) := by
  by_cases h0 : volume U = 0
  · have hz : volume.restrict U = 0 := Measure.restrict_eq_zero.mpr h0
    unfold scalarRms
    simp only [hz, average_zero_measure, le_refl]
  have hfin : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.2 hU
  have hconv : ∀ f : Vec d → ℝ, PDE.integralAverage U f = ⨍ x in U, f x := fun f => by
    unfold PDE.integralAverage
    rw [setAverage_eq, smul_eq_mul, measureReal_def]
  have key := integralAverage_sq_sub_le hU (u := fun x => u x - m) (hu.sub (memLp_const m))
  have hV : (volume U).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨h0, hU⟩
  have hu1 : Integrable u (volume.restrict U) := hu.integrable one_le_two
  have hmean : PDE.integralAverage U (fun x => u x - m) = (⨍ y in U, u y) - m := by
    rw [hconv, setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul,
      integral_sub hu1 (integrable_const m), setIntegral_const, smul_eq_mul, measureReal_def]
    field_simp
  rw [hmean, hconv, hconv] at key
  have e : (fun x => (u x - m - ((⨍ y in U, u y) - m)) ^ 2) =
      fun x => (u x - ⨍ y in U, u y) ^ 2 := funext fun x => by ring
  rw [e] at key
  unfold scalarRms
  exact Real.sqrt_le_sqrt key

/-- Comparison of `L̲²` norms on nested balls. -/
theorem scalarRms_ball_le {r t : ℝ} (hr : 0 < r) (hrt : r ≤ t) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (ball (0 : Vec d) t))) :
    scalarRms volume (ball 0 r) f ≤ Real.sqrt ((t / r) ^ d) * scalarRms volume (ball 0 t) f := by
  have htr : t = t / r * r := by field_simp
  have hvol : volume.real (ball (0 : Vec d) t) ≤
      (t / r) ^ d * volume.real (ball (0 : Vec d) r) := by
    conv_lhs => rw [htr]
    rw [volume_real_ball_mul (div_pos (lt_of_lt_of_le hr hrt) hr)]
  exact scalarRms_le_sqrt_mul_of_subset (ball_zero_subset_ball_zero hrt)
    (volume_ball_ne_zero' 0 hr) (volume_ball_ne_top' 0 t) hvol
    (pow_nonneg (div_nonneg (hr.le.trans hrt) hr.le) d) hf.integrable_sq

/-- `‖q·x‖_{L̲²(B_r)} ≤ |q| r`. -/
theorem scalarRms_dot_ball_le (q : Vec d) {r : ℝ} (hr : 0 ≤ r) :
    scalarRms volume (ball (0 : Vec d) r) (fun x => dot q x) ≤ euclideanNorm q * r := by
  have hB : 0 ≤ euclideanNorm q * r := mul_nonneg (Real.sqrt_nonneg _) hr
  unfold scalarRms
  rw [← Real.sqrt_sq hB]
  apply Real.sqrt_le_sqrt
  by_cases h0 : volume (ball (0 : Vec d) r) = 0
  · have hz : volume.restrict (ball (0 : Vec d) r) = 0 := Measure.restrict_eq_zero.mpr h0
    simp only [hz, average_zero_measure]
    positivity
  have hfin : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) r)) :=
    isFiniteMeasure_restrict.2 (volume_ball_ne_top' 0 r)
  have hpt : ∀ x ∈ ball (0 : Vec d) r, (dot q x) ^ 2 ≤ (euclideanNorm q * r) ^ 2 := by
    intro x hx
    have hx' : euclideanNorm x < r := by simpa [ball] using hx
    have h1 := BaseExponent.abs_dot_le q x
    have h2 : |dot q x| ≤ euclideanNorm q * r :=
      h1.trans (mul_le_mul_of_nonneg_left hx'.le (Real.sqrt_nonneg _))
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  rw [setAverage_eq, smul_eq_mul]
  have hint : ∫ x in ball (0 : Vec d) r, (dot q x) ^ 2 ≤
      ∫ _x in ball (0 : Vec d) r, (euclideanNorm q * r) ^ 2 := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
      (integrable_const _) ?_
    exact (ae_restrict_iff' (measurableSet_ball 0 r)).2 (Eventually.of_forall hpt)
  rw [setIntegral_const, smul_eq_mul] at hint
  have hV : 0 < volume.real (ball (0 : Vec d) r) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos h0 (volume_ball_ne_top' 0 r)
  calc (volume.real (ball (0 : Vec d) r))⁻¹ * ∫ x in ball (0 : Vec d) r, (dot q x) ^ 2
      ≤ (volume.real (ball (0 : Vec d) r))⁻¹ *
          (volume.real (ball (0 : Vec d) r) * (euclideanNorm q * r) ^ 2) :=
        mul_le_mul_of_nonneg_left hint (inv_nonneg.2 hV.le)
    _ = (euclideanNorm q * r) ^ 2 := by field_simp

/-- **The improvement of flatness** ((3.29) for `k = 1`, for a given affine function): if `w` is
`A`-harmonic in `B_{r/2}`, then for every affine `ℓ = c + q·x` there is an affine `ℓ'` with
`‖u - ℓ'‖_{L̲²(B_{θr})} ≤ 4 C θ² 2^{d/2} ‖u - ℓ‖_{L̲²(B_r)}
+ ((2θ)^{-d/2} + 4 C θ²) ‖u - w‖_{L̲²(B_{r/2})}` and
`|∇ℓ' - ∇ℓ| ≤ 2 C r⁻¹ (‖u - w‖_{L̲²(B_{r/2})} + 2^{d/2} ‖u - ℓ‖_{L̲²(B_r)})`. -/
theorem exists_affine_improvement (hd : 2 ≤ d) (hΛ : 1 ≤ Λ) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ A : Mat d, A.transpose = A → HomogenizedMatrixBounds A Λ →
      ∀ θ : ℝ, 0 < θ → θ < 1 / (2 * Real.sqrt Λ) →
      ∀ r : ℝ, 0 < r → ∀ u w : Vec d → ℝ, MemLp u 2 (volume.restrict (ball 0 r)) →
      IsL2HarmonicOn A (ball 0 (r / 2)) w → ∀ (c : ℝ) (q : Vec d),
      ∃ (c' : ℝ) (q' : Vec d),
        scalarRms volume (ball 0 (θ * r)) (fun x => u x - (c' + dot q' x)) ≤
          4 * C₁ * θ ^ 2 * Real.sqrt (2 ^ d) *
              scalarRms volume (ball 0 r) (fun x => u x - (c + dot q x)) +
            (Real.sqrt ((1 / (2 * θ)) ^ d) + 4 * C₁ * θ ^ 2) *
              scalarRms volume (ball 0 (r / 2)) (fun x => u x - w x) ∧
        euclideanNorm (q' - q) ≤ 2 * C₁ / r *
          (scalarRms volume (ball 0 (r / 2)) (fun x => u x - w x) +
            Real.sqrt (2 ^ d) * scalarRms volume (ball 0 r) (fun x => u x - (c + dot q x))) := by
  obtain ⟨C₁, hC₁, hexp⟩ := exists_affine_scalarRms_ball_le hd hΛ
  refine ⟨C₁, hC₁, ?_⟩
  intro A hsym hA θ hθ hθΛ r hr u w hu hw c q
  have hΛ0 : 0 < Λ := by linarith
  have hsΛ1 : 1 ≤ Real.sqrt Λ := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hΛ
  have hr2 : 0 < r / 2 := by positivity
  obtain ⟨c₁, q₁, hdec, hq₁⟩ := hexp A hsym hA (r / 2) hr2 _ (hw.sub_affine c q)
  set η := scalarRms volume (ball 0 (r / 2)) (fun x => u x - w x) with hη
  set F := scalarRms volume (ball 0 r) (fun x => u x - (c + dot q x)) with hF
  have hθ2 : θ * (2 * Real.sqrt Λ) < 1 := (lt_div_iff₀ (by positivity)).mp hθΛ
  have htρ : θ * r < r / 2 / Real.sqrt Λ := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  have ht : 0 < θ * r := mul_pos hθ hr
  have hth : θ * r ≤ r / 2 := by
    have : r / 2 / Real.sqrt Λ ≤ r / 2 := div_le_self hr2.le hsΛ1
    linarith
  have hsub2 : ball (0 : Vec d) (r / 2) ⊆ ball 0 r := ball_zero_subset_ball_zero (by linarith)
  have hu2 : MemLp u 2 (volume.restrict (ball (0 : Vec d) (r / 2))) :=
    hu.mono_measure (Measure.restrict_mono hsub2 le_rfl)
  have hw2 : MemLp w 2 (volume.restrict (ball (0 : Vec d) (r / 2))) := hw.1
  have huw : MemLp (fun x => u x - w x) 2 (volume.restrict (ball (0 : Vec d) (r / 2))) :=
    hu2.sub hw2
  have hul : MemLp (fun x => u x - (c + dot q x)) 2 (volume.restrict (ball (0 : Vec d) (r / 2))) :=
    hu2.sub (memLp_affine_ball c q _)
  have hh2 : MemLp (fun x => (w x - (c + dot q x)) - (c₁ + dot q₁ x)) 2
      (volume.restrict (ball (0 : Vec d) (r / 2))) :=
    (hw2.sub (memLp_affine_ball c q _)).sub (memLp_affine_ball c₁ q₁ _)
  have hsubt : ball (0 : Vec d) (θ * r) ⊆ ball 0 (r / 2) := ball_zero_subset_ball_zero hth
  have hwl : scalarRms volume (ball 0 (r / 2)) (fun x => w x - (c + dot q x)) ≤
      η + Real.sqrt (2 ^ d) * F := by
    have e : (fun x => w x - (c + dot q x)) =
        fun x => (u x - (c + dot q x)) - (u x - w x) := funext fun x => by ring
    rw [e]
    refine (scalarRms_sub_le hul huw).trans ?_
    have hmr : MemLp (fun x => u x - (c + dot q x)) 2 (volume.restrict (ball (0 : Vec d) r)) :=
      hu.sub (memLp_affine_ball c q r)
    have h1 := scalarRms_ball_le hr2 (by linarith : r / 2 ≤ r) hmr
    have e2 : r / (r / 2) = 2 := by field_simp
    rw [e2, ← hF] at h1
    rw [← hη]
    linarith
  have hwl0 : 0 ≤ scalarRms volume (ball 0 (r / 2)) (fun x => w x - (c + dot q x)) :=
    scalarRms_nonneg _ _
  refine ⟨c + c₁, q + q₁, ?_, ?_⟩
  · have e : (fun x => u x - ((c + c₁) + dot (q + q₁) x)) =
        fun x => (u x - w x) + ((w x - (c + dot q x)) - (c₁ + dot q₁ x)) := by
      funext x
      simp only [dot_eq_dotProduct, add_dotProduct]
      ring
    rw [e]
    have hA1 := scalarRms_add_le (huw.mono_measure (Measure.restrict_mono hsubt le_rfl))
      (hh2.mono_measure (Measure.restrict_mono hsubt le_rfl))
    have hA2 := scalarRms_ball_le ht hth huw
    have e3 : r / 2 / (θ * r) = 1 / (2 * θ) := by field_simp
    rw [e3, ← hη] at hA2
    have hA3 := hdec (θ * r) ht htρ
    have e4 : (θ * r / (r / 2)) ^ 2 = 4 * θ ^ 2 := by field_simp; ring
    rw [e4] at hA3
    have hs0 : 0 ≤ Real.sqrt ((1 / (2 * θ)) ^ d) := Real.sqrt_nonneg _
    have hη0 : 0 ≤ η := scalarRms_nonneg _ _
    calc scalarRms volume (ball 0 (θ * r))
          (fun x => (u x - w x) + ((w x - (c + dot q x)) - (c₁ + dot q₁ x)))
        ≤ Real.sqrt ((1 / (2 * θ)) ^ d) * η +
            C₁ * (4 * θ ^ 2) * scalarRms volume (ball 0 (r / 2))
              (fun x => w x - (c + dot q x)) := by linarith
      _ ≤ Real.sqrt ((1 / (2 * θ)) ^ d) * η +
            C₁ * (4 * θ ^ 2) * (η + Real.sqrt (2 ^ d) * F) := by
          gcongr
      _ = 4 * C₁ * θ ^ 2 * Real.sqrt (2 ^ d) * F +
            (Real.sqrt ((1 / (2 * θ)) ^ d) + 4 * C₁ * θ ^ 2) * η := by ring
  · rw [add_sub_cancel_left]
    calc euclideanNorm q₁ ≤ C₁ / (r / 2) *
          scalarRms volume (ball 0 (r / 2)) (fun x => w x - (c + dot q x)) := hq₁
      _ ≤ C₁ / (r / 2) * (η + Real.sqrt (2 ^ d) * F) := by gcongr
      _ = 2 * C₁ / r * (η + Real.sqrt (2 ^ d) * F) := by field_simp

end Improvement

section Lemma36

/-- The flatness `inf_ℓ ‖u - ℓ‖_{L̲²(B_r)}` of `u` over the affine functions `ℓ` (the quantity of
(3.29) for `k = 1`, and `r E₁(r)` in (3.32)). -/
def affineFlatness (u : Vec d → ℝ) (r : ℝ) : ℝ :=
  ⨅ p : ℝ × Vec d, scalarRms volume (ball 0 r) (fun x => u x - (p.1 + dot p.2 x))

theorem bddBelow_affineFlatness (u : Vec d → ℝ) (r : ℝ) :
    BddBelow (Set.range fun p : ℝ × Vec d =>
      scalarRms volume (ball 0 r) (fun x => u x - (p.1 + dot p.2 x))) :=
  ⟨0, by rintro _ ⟨p, rfl⟩; exact scalarRms_nonneg _ _⟩

theorem affineFlatness_le (u : Vec d → ℝ) (r c : ℝ) (q : Vec d) :
    affineFlatness u r ≤ scalarRms volume (ball 0 r) (fun x => u x - (c + dot q x)) :=
  ciInf_le (bddBelow_affineFlatness u r) (c, q)

theorem affineFlatness_nonneg (u : Vec d → ℝ) (r : ℝ) : 0 ≤ affineFlatness u r :=
  le_ciInf fun _ => scalarRms_nonneg _ _

/-- **Lemma 3.6 for `k = 1`**: there are `θ(α, d, Λ) ∈ (0, ½)` and `C(α, d, Λ)` such that, if for
every `r ∈ [X, R]` some `A`-harmonic `w_r` in `B_{r/2}` satisfies (3.28),
`‖u - w_r‖_{L̲²(B_{r/2})} ≤ K r^{-α} ‖u - (u)_{B_r}‖_{L̲²(B_r)}`, then (3.29) holds:
`inf_ℓ ‖u - ℓ‖_{L̲²(B_{θr})} ≤ ¼ θ^{2-α/2} inf_ℓ ‖u - ℓ‖_{L̲²(B_r)}
+ C K r^{-α} ‖u - (u)_{B_r}‖_{L̲²(B_r)}` for every `r ∈ [X, R]`, the infima over the affine
functions `ℓ` (the `A`-harmonic polynomials of degree at most one). -/
theorem lemma_3_6_one (hd : 2 ≤ d) (hΛ : 1 ≤ Λ) {α : ℝ} (hα : 0 < α) :
    ∃ θ C : ℝ, 0 < θ ∧ θ < 1 / 2 ∧ 0 ≤ C ∧
      ∀ A : Mat d, A.transpose = A → HomogenizedMatrixBounds A Λ →
      ∀ K X R : ℝ, 1 ≤ X → ∀ u : Vec d → ℝ, MemLp u 2 (volume.restrict (ball 0 R)) →
      (∀ r : ℝ, X ≤ r → r ≤ R → ∃ w : Vec d → ℝ, IsL2HarmonicOn A (ball 0 (r / 2)) w ∧
        scalarRms volume (ball 0 (r / 2)) (fun x => u x - w x) ≤
          K * r ^ (-α) * scalarRms volume (ball 0 r) (fun x => u x - ⨍ y in ball 0 r, u y)) →
      ∀ r : ℝ, X ≤ r → r ≤ R →
        affineFlatness u (θ * r) ≤ 1 / 4 * θ ^ (2 - α / 2) * affineFlatness u r +
          C * K * r ^ (-α) * scalarRms volume (ball 0 r) (fun x => u x - ⨍ y in ball 0 r, u y) := by
  obtain ⟨C₁, hC₁, himp⟩ := exists_affine_improvement hd hΛ
  have hΛ0 : 0 < Λ := by linarith
  have hsΛ1 : 1 ≤ Real.sqrt Λ := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hΛ
  set s₂ : ℝ := Real.sqrt (2 ^ d) with hs₂
  have hs₂0 : 0 ≤ s₂ := Real.sqrt_nonneg _
  set B : ℝ := 16 * (C₁ + 1) * s₂ with hB
  have hs₂1 : 1 ≤ s₂ := by
    rw [hs₂, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (one_le_pow₀ (by norm_num))
  have hB0 : 0 < B := by positivity
  set θ : ℝ := min (1 / (4 * Real.sqrt Λ)) (B ^ (-(2 / α))) with hθdef
  have hθ0 : 0 < θ := lt_min (by positivity) (Real.rpow_pos_of_pos hB0 _)
  have hθ4 : θ ≤ 1 / (4 * Real.sqrt Λ) := min_le_left _ _
  have hθB : θ ≤ B ^ (-(2 / α)) := min_le_right _ _
  have h4Λ : 1 / (4 * Real.sqrt Λ) ≤ 1 / 4 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num); linarith
  have hθΛ : θ < 1 / (2 * Real.sqrt Λ) := by
    have : 1 / (4 * Real.sqrt Λ) < 1 / (2 * Real.sqrt Λ) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    linarith
  set C : ℝ := Real.sqrt ((1 / (2 * θ)) ^ d) + 4 * C₁ * θ ^ 2 with hCdef
  have hC0 : 0 ≤ C := by positivity
  refine ⟨θ, C, hθ0, by linarith, hC0, ?_⟩
  -- the contraction factor
  set a : ℝ := 4 * C₁ * θ ^ 2 * s₂ with ha
  have ha0 : 0 ≤ a := by positivity
  have hpow : θ ^ (α / 2) ≤ B⁻¹ := by
    have h1 : θ ^ (α / 2) ≤ (B ^ (-(2 / α))) ^ (α / 2) :=
      Real.rpow_le_rpow hθ0.le hθB (by positivity)
    rw [← Real.rpow_mul hB0.le] at h1
    have e : -(2 / α) * (α / 2) = -1 := by field_simp
    rwa [e, Real.rpow_neg_one] at h1
  have hθpos : 0 < θ ^ (α / 2) := Real.rpow_pos_of_pos hθ0 _
  have hrpow : θ ^ (2 - α / 2) = θ ^ 2 / θ ^ (α / 2) := by
    rw [Real.rpow_sub hθ0, Real.rpow_two]
  have hale : a ≤ 1 / 4 * θ ^ (2 - α / 2) := by
    rw [hrpow, ha]
    have hBθ : B * θ ^ (α / 2) ≤ 1 := by
      calc B * θ ^ (α / 2) ≤ B * B⁻¹ := mul_le_mul_of_nonneg_left hpow hB0.le
        _ = 1 := mul_inv_cancel₀ hB0.ne'
    rw [← mul_div_assoc, le_div_iff₀ hθpos]
    have hθ2 : 0 ≤ θ ^ 2 := sq_nonneg θ
    have : 4 * C₁ * s₂ * θ ^ (α / 2) ≤ 1 / 4 := by
      have h2 : 4 * C₁ * s₂ ≤ B / 4 := by rw [hB]; nlinarith
      calc 4 * C₁ * s₂ * θ ^ (α / 2) ≤ B / 4 * θ ^ (α / 2) :=
            mul_le_mul_of_nonneg_right h2 hθpos.le
        _ = (B * θ ^ (α / 2)) / 4 := by ring
        _ ≤ 1 / 4 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right this hθ2]
  intro A hsym hA K X R hX u hu hyp r hXr hrR
  have hr : 0 < r := by linarith
  obtain ⟨w, hw, hη⟩ := hyp r hXr hrR
  have hur : MemLp u 2 (volume.restrict (ball (0 : Vec d) r)) :=
    hu.mono_measure (Measure.restrict_mono (ball_zero_subset_ball_zero hrR) le_rfl)
  set η := scalarRms volume (ball 0 (r / 2)) (fun x => u x - w x) with hηdef
  have key : ∀ p : ℝ × Vec d, affineFlatness u (θ * r) - C * η ≤
      a * scalarRms volume (ball 0 r) (fun x => u x - (p.1 + dot p.2 x)) := by
    intro p
    obtain ⟨c', q', h1, -⟩ := himp A hsym hA θ hθ0 hθΛ r hr u w hur hw p.1 p.2
    have h2 := affineFlatness_le u (θ * r) c' q'
    rw [← hηdef] at h1
    linarith
  have hinf : affineFlatness u (θ * r) - C * η ≤ a * affineFlatness u r := by
    unfold affineFlatness
    rw [Real.mul_iInf_of_nonneg ha0]
    exact le_ciInf key
  have hF0 := affineFlatness_nonneg u r
  have h3 : C * η ≤ C * (K * r ^ (-α) *
      scalarRms volume (ball 0 r) (fun x => u x - ⨍ y in ball 0 r, u y)) :=
    mul_le_mul_of_nonneg_left hη hC0
  have h4 : a * affineFlatness u r ≤ 1 / 4 * θ ^ (2 - α / 2) * affineFlatness u r :=
    mul_le_mul_of_nonneg_right hale hF0
  nlinarith

end Lemma36

end QSH
