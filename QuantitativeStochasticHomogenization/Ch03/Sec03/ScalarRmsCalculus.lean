import QuantitativeStochasticHomogenization.Ch03.Sec03.QuarterExcessStep

/-!
# Calculus of normalized `L²` norms on ellipsoids

The normalized `L²(U)` norm `‖f‖_{L̲²(U)} = (⨍_U f²)^{1/2}` is homogeneous and satisfies the
triangle inequality for square-integrable functions. On the ellipsoids `E_t = M B_t`, with
`|E_s| = (s/t)^d |E_t|`, it satisfies `‖f‖_{L̲²(E_t)} ≤ (s/t)^{d/2} ‖f‖_{L̲²(E_s)}` for `t ≤ s`.
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ}

theorem scalarRms_nonneg (U : Set (Vec d)) (f : Vec d → ℝ) : 0 ≤ scalarRms volume U f :=
  Real.sqrt_nonneg _

theorem scalarRms_const_mul (U : Set (Vec d)) (f : Vec d → ℝ) (c : ℝ) :
    scalarRms volume U (fun x => c * f x) = |c| * scalarRms volume U f := by
  show Real.sqrt (⨍ x in U, (c * f x) ^ 2) = |c| * Real.sqrt (⨍ x in U, f x ^ 2)
  have h : (fun x => (c * f x) ^ 2) = fun x => c ^ 2 * f x ^ 2 := by
    funext x
    ring
  rw [h, setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul, integral_const_mul,
    show (volume.real U)⁻¹ * (c ^ 2 * ∫ x in U, f x ^ 2) =
      c ^ 2 * ((volume.real U)⁻¹ * ∫ x in U, f x ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- **Minkowski's inequality** for the normalized `L²` norm. -/
theorem scalarRms_add_le {U : Set (Vec d)} {f g : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict U))
    (hg : MemLp g 2 (volume.restrict U)) :
    scalarRms volume U (fun x => f x + g x) ≤ scalarRms volume U f + scalarRms volume U g := by
  have hfg : MemLp (fun x => f x + g x) 2 (volume.restrict U) := hf.add hg
  rw [scalarRms_eq_mul_norm_toLp hfg, scalarRms_eq_mul_norm_toLp hf,
    scalarRms_eq_mul_norm_toLp hg, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  have h : hfg.toLp (fun x => f x + g x) = hf.toLp f + hg.toLp g := MemLp.toLp_add hf hg
  rw [h]
  exact norm_add_le _ _

theorem scalarRms_sub_le {U : Set (Vec d)} {f g : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict U))
    (hg : MemLp g 2 (volume.restrict U)) :
    scalarRms volume U (fun x => f x - g x) ≤ scalarRms volume U f + scalarRms volume U g := by
  have h := scalarRms_add_le hf (hg.const_mul (-1))
  rw [scalarRms_const_mul, abs_neg, abs_one, one_mul] at h
  have e : (fun x => f x - g x) = fun x => f x + -1 * g x := by
    funext x
    ring
  rw [e]
  exact h

theorem scalarRms_finset_sum_le {ι : Type*} (s : Finset ι) {U : Set (Vec d)}
    {f : ι → Vec d → ℝ} (hf : ∀ i, MemLp (f i) 2 (volume.restrict U)) (c : ι → ℝ) :
    scalarRms volume U (fun x => ∑ i ∈ s, c i * f i x) ≤
      ∑ i ∈ s, |c i| * scalarRms volume U (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [scalarRms]
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    calc scalarRms volume U (fun x => c j * f j x + ∑ i ∈ s, c i * f i x)
        ≤ scalarRms volume U (fun x => c j * f j x) +
            scalarRms volume U (fun x => ∑ i ∈ s, c i * f i x) :=
          scalarRms_add_le ((hf j).const_mul _) (memLp_finsetSum _ fun i _ => (hf i).const_mul _)
      _ ≤ |c j| * scalarRms volume U (f j) + ∑ i ∈ s, |c i| * scalarRms volume U (f i) := by
          rw [scalarRms_const_mul]
          linarith [ih]

theorem matrixEllipsoid_mono (M : Mat d) : Monotone (matrixEllipsoid M) := by
  intro R R' hRR'
  refine Set.image_mono fun y hy => ?_
  change euclideanNorm (y - 0) < R'
  have : euclideanNorm (y - 0) < R := hy
  linarith

theorem volume_matrixEllipsoid_lt_top (M : Mat d) (R : ℝ) : volume (matrixEllipsoid M R) < ⊤ := by
  rw [volume_matrixEllipsoid]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (volume_ball_zero_lt_top R)

theorem volume_matrixEllipsoid_ne_zero {M : Mat d} (hdet : M.det ≠ 0) {R : ℝ} (hR : 0 < R) :
    volume (matrixEllipsoid M R) ≠ 0 := by
  rw [volume_matrixEllipsoid]
  exact mul_ne_zero (ENNReal.ofReal_pos.2 (abs_pos.2 hdet)).ne' (volume_ball_zero_pos hR).ne'

theorem volume_matrixEllipsoid_mul (M : Mat d) {L : ℝ} (hL : 0 < L) (R : ℝ) :
    volume (matrixEllipsoid M (L * R)) =
      ENNReal.ofReal (L ^ d) * volume (matrixEllipsoid M R) := by
  rw [volume_matrixEllipsoid, volume_matrixEllipsoid, volume_ball_zero_mul hL]
  ring

theorem sqrt_le_self_of_one_le {x : ℝ} (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  rw [Real.sqrt_le_iff]
  constructor
  · linarith
  · nlinarith

/-- Comparison of normalized `L²` norms on nested ellipsoids. -/
theorem scalarRms_matrixEllipsoid_le {M : Mat d} (hdet : M.det ≠ 0) {t s : ℝ} (ht : 0 < t)
    (hts : t ≤ s) {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict (matrixEllipsoid M s))) :
    scalarRms volume (matrixEllipsoid M t) f ≤
      (s / t) ^ d * scalarRms volume (matrixEllipsoid M s) f := by
  have hst : 1 ≤ s / t := by rw [le_div_iff₀ ht]; linarith
  have hE : volume (matrixEllipsoid M s) =
      ENNReal.ofReal ((s / t) ^ d) * volume (matrixEllipsoid M t) := by
    have h := volume_matrixEllipsoid_mul M (show 0 < s / t by positivity) t
    rwa [div_mul_cancel₀ s ht.ne'] at h
  have hvol : volume.real (matrixEllipsoid M s) ≤ (s / t) ^ d * volume.real (matrixEllipsoid M t) := by
    apply le_of_eq
    rw [measureReal_def, measureReal_def, hE, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
  have h := scalarRms_le_sqrt_mul_of_subset (matrixEllipsoid_mono M hts)
    (volume_matrixEllipsoid_ne_zero hdet ht) (volume_matrixEllipsoid_lt_top M s).ne hvol
    (by positivity) hf.integrable_sq
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (scalarRms_nonneg _ _))
  exact sqrt_le_self_of_one_le (one_le_pow₀ hst)

/-- Convexity bound `(1 + x)ⁿ ≤ 1 + (2ⁿ - 1) x` for `0 ≤ x ≤ 1`. -/
theorem one_add_pow_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    (1 + x) ^ n ≤ 1 + ((2 : ℝ) ^ n - 1) * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    calc (1 + x) ^ (n + 1) = (1 + x) * (1 + x) ^ n := by ring
      _ ≤ (1 + x) * (1 + ((2 : ℝ) ^ n - 1) * x) :=
          mul_le_mul_of_nonneg_left ih (by linarith)
      _ ≤ 1 + ((2 : ℝ) ^ (n + 1) - 1) * x := by
          rw [pow_succ]
          nlinarith [mul_nonneg hx0 (sub_nonneg.2 hx1), mul_nonneg (mul_nonneg hx0
            (sub_nonneg.2 hx1)) (sub_nonneg.2 h2)]

end QSH
