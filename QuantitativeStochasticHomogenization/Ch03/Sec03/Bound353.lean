import QuantitativeStochasticHomogenization.Ch03.Sec03.HomogeneousHarmonic
import QuantitativeStochasticHomogenization.Ch03.Sec03.Implication348

/-!
# The estimate (3.53) of the proof of (3.46)

Armstrong–Kuusi–Mourrat, Section 3.3, Step 1 of the proof of (3.46). For `q ∈ Ā_k` homogeneous of
degree `k ≥ 1` and the radii `r_m = 2^m r₀`, let `u_m` be solutions in `B_{r_m}` close to `q` as in
(3.52), `w_m = u_{m+1} - u_m`, `φ_m ∈ A_{k-1}` given by `(iii')_{k-1}` for `w_m`, and `p_m ∈ Ā_{k-1}`
given by `(i)_{k-1}` for `φ_m`. Then `v_n = u_n - ∑_{m<n} φ_m` satisfies (3.53),
`‖v_n - q‖_{L̲²(B_{r_j})} ≤ C r_j^{-δ} ‖q‖_{L̲²(B_{r_j})}` for `j ≤ n`, and its increments
`v_{n+1} - v_n = w_n - φ_n` are geometrically small on `B_{r_j}` (`bound_353`).
-/

open MeasureTheory Filter Set
open scoped Pointwise

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- The norm of a homogeneous function of degree `k` on dilated balls. -/
theorem scalarRms_ball_homogeneous {k : ℕ} {q : Vec d → ℝ}
    (hq : ∀ t : ℝ, 0 < t → ∀ x, q (t • x) = t ^ k * q x) {t r : ℝ} (ht : 0 < t) :
    scalarRms volume (ball 0 (t * r)) q = t ^ k * scalarRms volume (ball 0 r) q := by
  have e := TwoScale.scalarRms_comp_smul ht (ball (0 : Vec d) r) q
  rw [smul_ball_zero ht] at e
  rw [← e]
  have e2 : (fun y => q (t • y)) = fun y => t ^ k * q y := funext (hq t ht)
  rw [e2, scalarRms_const_mul, abs_of_pos (pow_pos ht k)]

theorem rpow_combine_one {t ρ k δ : ℝ} (ht : 0 < t) (hρ : 0 < ρ) :
    (ρ / (t * ρ)) ^ (k - δ / 2) * (t * ρ) ^ (-δ) * t ^ k = t ^ (-(δ / 2)) * ρ ^ (-δ) := by
  rw [show ρ / (t * ρ) = t⁻¹ by field_simp, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le,
    Real.mul_rpow ht.le hρ.le]
  have e : t ^ (-(k - δ / 2)) * t ^ (-δ) * t ^ k = t ^ (-(δ / 2)) := by
    rw [← Real.rpow_add ht, ← Real.rpow_add ht]; congr 1; ring
  calc t ^ (-(k - δ / 2)) * (t ^ (-δ) * ρ ^ (-δ)) * t ^ k
      = (t ^ (-(k - δ / 2)) * t ^ (-δ) * t ^ k) * ρ ^ (-δ) := by ring
    _ = _ := by rw [e]

/-- (B1): the increment `w_m = u_{m+1} - u_m` of two solutions close to a homogeneous `q`. -/
theorem scalarRms_increment_le {k : ℕ} {q : Vec d → ℝ}
    (hq : ∀ t : ℝ, 0 < t → ∀ x, q (t • x) = t ^ k * q x)
    (hqL2 : ∀ r : ℝ, 0 < r → MemLp q 2 (volume.restrict (ball (0 : Vec d) r)))
    {r C δ : ℝ} (hr : 0 < r) (hδ : 0 ≤ δ) (hC : 0 ≤ C) {u₀ u₁ : Vec d → ℝ}
    (hu₀ : MemLp u₀ 2 (volume.restrict (ball (0 : Vec d) r)))
    (hu₁ : MemLp u₁ 2 (volume.restrict (ball (0 : Vec d) (2 * r))))
    (hb₀ : scalarRms volume (ball 0 r) (fun x => u₀ x - q x) ≤
      C * r ^ (-δ) * scalarRms volume (ball 0 r) q)
    (hb₁ : scalarRms volume (ball 0 (2 * r)) (fun x => u₁ x - q x) ≤
      C * (2 * r) ^ (-δ) * scalarRms volume (ball 0 (2 * r)) q) :
    scalarRms volume (ball 0 r) (fun x => u₁ x - u₀ x) ≤
      C * (Real.sqrt (2 ^ d) * 2 ^ k + 1) * r ^ (-δ) * scalarRms volume (ball 0 r) q := by
  have h2r : r ≤ 2 * r := by linarith
  have hu₁r : MemLp u₁ 2 (volume.restrict (ball (0 : Vec d) r)) :=
    hu₁.mono_measure (Measure.restrict_mono (ball_zero_subset_ball_zero h2r) le_rfl)
  have hqr := hqL2 r hr
  have e : (fun x => u₁ x - u₀ x) = fun x => (u₁ x - q x) - (u₀ x - q x) := by funext x; ring
  rw [e]
  refine (scalarRms_sub_le (hu₁r.sub hqr) (hu₀.sub hqr)).trans ?_
  have h1 := scalarRms_ball_le hr h2r (hu₁.sub (hqL2 _ (by linarith)))
  rw [show 2 * r / r = 2 by field_simp] at h1
  rw [scalarRms_ball_homogeneous hq two_pos] at hb₁
  have hpow : (2 * r) ^ (-δ) ≤ r ^ (-δ) :=
    Real.rpow_le_rpow_of_nonpos hr h2r (by linarith)
  have hq0 := scalarRms_nonneg (d := d) (ball 0 r) q
  have hs := Real.sqrt_nonneg ((2 : ℝ) ^ d)
  calc scalarRms volume (ball 0 r) (fun x => u₁ x - q x) +
        scalarRms volume (ball 0 r) (fun x => u₀ x - q x)
      ≤ Real.sqrt (2 ^ d) * (C * (2 * r) ^ (-δ) * (2 ^ k * scalarRms volume (ball 0 r) q)) +
          C * r ^ (-δ) * scalarRms volume (ball 0 r) q :=
        add_le_add (h1.trans (mul_le_mul_of_nonneg_left hb₁ hs)) hb₀
    _ ≤ Real.sqrt (2 ^ d) * (C * r ^ (-δ) * (2 ^ k * scalarRms volume (ball 0 r) q)) +
          C * r ^ (-δ) * scalarRms volume (ball 0 r) q := by
        gcongr
    _ = _ := by ring

/-- (B2): the correction of `w` by `(iii')_{k-1}` on the smaller ball `B_ρ`, `ρ = R/t`. -/
theorem scalarRms_correction_small {k : ℕ} {q : Vec d → ℝ}
    (hq : ∀ t : ℝ, 0 < t → ∀ x, q (t • x) = t ^ k * q x) {ρ t C₃ K δ : ℝ} (hρ : 0 < ρ)
    (ht : 0 < t) (hC₃ : 0 ≤ C₃) {w φ : Vec d → ℝ}
    (hφ : scalarRms volume (ball 0 ρ) (fun x => w x - φ x) ≤
      C₃ * (ρ / (t * ρ)) ^ ((k : ℝ) - δ / 2) * scalarRms volume (ball 0 (t * ρ)) w)
    (hw : scalarRms volume (ball 0 (t * ρ)) w ≤
      K * (t * ρ) ^ (-δ) * scalarRms volume (ball 0 (t * ρ)) q) :
    scalarRms volume (ball 0 ρ) (fun x => w x - φ x) ≤
      C₃ * K * (t ^ (-(δ / 2)) * ρ ^ (-δ)) * scalarRms volume (ball 0 ρ) q := by
  rw [scalarRms_ball_homogeneous hq ht] at hw
  have hc : 0 ≤ C₃ * (ρ / (t * ρ)) ^ ((k : ℝ) - δ / 2) :=
    mul_nonneg hC₃ (Real.rpow_nonneg (by positivity) _)
  refine hφ.trans ((mul_le_mul_of_nonneg_left hw hc).trans (le_of_eq ?_))
  have e := rpow_combine_one (k := (k : ℝ)) (δ := δ) ht hρ
  rw [Real.rpow_natCast] at e
  calc C₃ * (ρ / (t * ρ)) ^ ((k : ℝ) - δ / 2) * (K * (t * ρ) ^ (-δ) *
        (t ^ k * scalarRms volume (ball 0 ρ) q))
      = C₃ * K * ((ρ / (t * ρ)) ^ ((k : ℝ) - δ / 2) * (t * ρ) ^ (-δ) * t ^ k) *
          scalarRms volume (ball 0 ρ) q := by ring
    _ = _ := by rw [e]

/-- (B4): the growth of a correction `φ` close to `p ∈ Ā_{k-1}` from `B_ρ` to `B_{tρ}`. -/
theorem scalarRms_correction_large {k : ℕ} (hk : 1 ≤ k) {q : Vec d → ℝ}
    (hq : ∀ t : ℝ, 0 < t → ∀ x, q (t • x) = t ^ k * q x)
    {ρ t r₀ C₁ C₂₇ C₃ K δ : ℝ} (hρ : 0 < ρ) (ht : 1 ≤ t) (hr₀ : 0 < r₀) (hr₀ρ : r₀ ≤ ρ)
    (hδ : 0 ≤ δ) (hC₁ : 0 ≤ C₁) (hsmall : C₁ * r₀ ^ (-δ) ≤ 1 / 2) (hC₂₇ : 0 ≤ C₂₇)
    (hC₃ : 0 ≤ C₃) {w φ p : Vec d → ℝ}
    (hwL2 : MemLp w 2 (volume.restrict (ball (0 : Vec d) ρ)))
    (hφL2 : ∀ r : ℝ, 0 < r → MemLp φ 2 (volume.restrict (ball (0 : Vec d) r)))
    (hpL2 : ∀ r : ℝ, 0 < r → MemLp p 2 (volume.restrict (ball (0 : Vec d) r)))
    (hφp : ∀ R : ℝ, r₀ ≤ R → scalarRms volume (ball 0 R) (fun x => φ x - p x) ≤
      C₁ * R ^ (-δ) * scalarRms volume (ball 0 R) p)
    (hgrow : scalarRms volume (ball 0 (t * ρ)) p ≤ C₂₇ * t ^ (k - 1) * scalarRms volume (ball 0 ρ) p)
    (hφw : scalarRms volume (ball 0 ρ) (fun x => w x - φ x) ≤ C₃ * scalarRms volume (ball 0 ρ) w)
    (hw : scalarRms volume (ball 0 ρ) w ≤ K * ρ ^ (-δ) * scalarRms volume (ball 0 ρ) q) :
    scalarRms volume (ball 0 (t * ρ)) φ ≤
      4 * C₂₇ * (1 + C₃) * K * (t ^ (δ - 1) * (t * ρ) ^ (-δ)) *
        scalarRms volume (ball 0 (t * ρ)) q := by
  have ht0 : 0 < t := by linarith
  have htρ : 0 < t * ρ := mul_pos ht0 hρ
  have hr₀tρ : r₀ ≤ t * ρ := hr₀ρ.trans (by nlinarith)
  have hsm : ∀ R : ℝ, r₀ ≤ R → C₁ * R ^ (-δ) ≤ 1 / 2 := fun R hR =>
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hr₀ hR (by linarith)) hC₁).trans
      hsmall
  -- `‖φ‖_{tρ} ≤ 2 ‖p‖_{tρ}` and `‖p‖_ρ ≤ 2 ‖φ‖_ρ`
  have h1 : scalarRms volume (ball 0 (t * ρ)) φ ≤ 2 * scalarRms volume (ball 0 (t * ρ)) p := by
    have h := scalarRms_le_add_of_sub (hpL2 _ htρ) (hφL2 _ htρ)
    have e : (fun x => p x - φ x) = fun x => -1 * (φ x - p x) := by funext x; ring
    rw [e, scalarRms_const_mul, abs_neg, abs_one, one_mul] at h
    have h' := hφp _ hr₀tρ
    have := hsm _ hr₀tρ
    have hp0 := scalarRms_nonneg (d := d) (ball 0 (t * ρ)) p
    nlinarith
  have h2 : scalarRms volume (ball 0 ρ) p ≤ 2 * scalarRms volume (ball 0 ρ) φ := by
    have h := scalarRms_le_add_of_sub (hφL2 _ hρ) (hpL2 _ hρ)
    have h' := hφp _ hr₀ρ
    have := hsm _ hr₀ρ
    have hp0 := scalarRms_nonneg (d := d) (ball 0 ρ) p
    nlinarith
  have h3 : scalarRms volume (ball 0 ρ) φ ≤ (1 + C₃) * scalarRms volume (ball 0 ρ) w := by
    have h := scalarRms_le_add_of_sub hwL2 (hφL2 _ hρ)
    linarith
  rw [scalarRms_ball_homogeneous hq ht0]
  have htk : t ^ (k - 1) * t = t ^ k := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
  have hpow : t ^ (k - 1) * ρ ^ (-δ) = t ^ (δ - 1) * (t * ρ) ^ (-δ) * t ^ k := by
    rw [Real.mul_rpow ht0.le hρ.le, ← htk]
    have e1 : t ^ (δ - 1) * t ^ (-δ) * t = 1 := by
      rw [← Real.rpow_add ht0, show δ - 1 + -δ = -1 by ring, Real.rpow_neg_one,
        inv_mul_cancel₀ ht0.ne']
    calc t ^ (k - 1) * ρ ^ (-δ) = t ^ (k - 1) * ρ ^ (-δ) * (t ^ (δ - 1) * t ^ (-δ) * t) := by
          rw [e1, mul_one]
      _ = _ := by ring
  have hw0 := scalarRms_nonneg (d := d) (ball 0 ρ) w
  calc scalarRms volume (ball 0 (t * ρ)) φ
      ≤ 2 * (C₂₇ * t ^ (k - 1) * (2 * ((1 + C₃) * (K * ρ ^ (-δ) *
          scalarRms volume (ball 0 ρ) q)))) := by
        refine h1.trans (mul_le_mul_of_nonneg_left (hgrow.trans ?_) (by norm_num))
        refine mul_le_mul_of_nonneg_left (h2.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_left hw (by linarith)))
          (by norm_num)
    _ = 4 * C₂₇ * (1 + C₃) * K * (t ^ (k - 1) * ρ ^ (-δ)) * scalarRms volume (ball 0 ρ) q := by
        ring
    _ = _ := by rw [hpow]; ring

theorem two_pow_rpow (i : ℕ) (y : ℝ) : ((2 : ℝ) ^ i) ^ y = ((2 : ℝ) ^ y) ^ i := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
    Real.rpow_natCast]

theorem two_pow_sub_mul {j n : ℕ} (hjn : j ≤ n) (r₀ : ℝ) :
    (2 : ℝ) ^ (n - j) * (2 ^ j * r₀) = 2 ^ n * r₀ := by
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hjn]

/-- **(3.53)** and the geometric smallness of the increments, for the sequences of the proof of
(3.46) on the radii `r_m = 2^m r₀`. -/
theorem bound_353 {a : CoefficientField d Λ} {A : Mat d} {k : ℕ} (hk : 1 ≤ k) {q : Vec d → ℝ}
    (hq : ∀ t : ℝ, 0 < t → ∀ x, q (t • x) = t ^ k * q x)
    (hqL2 : ∀ r : ℝ, 0 < r → MemLp q 2 (volume.restrict (ball (0 : Vec d) r)))
    {r₀ δ C₅₂ C₃ C₁ C₂₇ : ℝ} (hr₀ : 0 < r₀) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hC₅₂ : 0 ≤ C₅₂)
    (hC₃ : 0 ≤ C₃) (hC₁ : 0 ≤ C₁) (hC₂₇ : 0 ≤ C₂₇) (hsmall : C₁ * r₀ ^ (-δ) ≤ 1 / 2)
    (u φ p : ℕ → Vec d → ℝ)
    (hu : ∀ m, IsSolutionBall a (2 ^ m * r₀) (u m) ∧
      scalarRms volume (ball 0 (2 ^ m * r₀)) (fun x => u m x - q x) ≤
        C₅₂ * (2 ^ m * r₀) ^ (-δ) * scalarRms volume (ball 0 (2 ^ m * r₀)) q)
    (hφ : ∀ m, φ m ∈ solutionGrowthSpace a (k - 1) ∧ ∀ r : ℝ, r₀ ≤ r → r ≤ 2 ^ m * r₀ →
      scalarRms volume (ball 0 r) (fun x => (u (m + 1) x - u m x) - φ m x) ≤
        C₃ * (r / (2 ^ m * r₀)) ^ ((k : ℝ) - δ / 2) *
          scalarRms volume (ball 0 (2 ^ m * r₀)) (fun x => u (m + 1) x - u m x))
    (hp : ∀ m, p m ∈ harmonicPolys A (k - 1) ∧ ∀ R : ℝ, r₀ ≤ R →
      scalarRms volume (ball 0 R) (fun x => φ m x - p m x) ≤
        C₁ * R ^ (-δ) * scalarRms volume (ball 0 R) (p m))
    (hgrow : ∀ m (t ρ : ℝ), 0 < ρ → 1 ≤ t →
      scalarRms volume (ball 0 (t * ρ)) (p m) ≤ C₂₇ * t ^ (k - 1) * scalarRms volume (ball 0 ρ) (p m)) :
    (∀ j n, j ≤ n → scalarRms volume (ball 0 (2 ^ j * r₀))
        (fun x => (u n x - ∑ m ∈ Finset.range n, φ m x) - q x) ≤
      (C₅₂ + C₃ * (C₅₂ * (Real.sqrt (2 ^ d) * 2 ^ k + 1)) / (1 - (2 : ℝ) ^ (-(δ / 2))) +
        4 * C₂₇ * (1 + C₃) * (C₅₂ * (Real.sqrt (2 ^ d) * 2 ^ k + 1)) / (1 - (2 : ℝ) ^ (δ - 1))) *
        (2 ^ j * r₀) ^ (-δ) * scalarRms volume (ball 0 (2 ^ j * r₀)) q) ∧
    (∀ j n, j ≤ n → scalarRms volume (ball 0 (2 ^ j * r₀))
        (fun x => (u (n + 1) x - u n x) - φ n x) ≤
      C₃ * (C₅₂ * (Real.sqrt (2 ^ d) * 2 ^ k + 1)) * (((2 : ℝ) ^ (-(δ / 2))) ^ (n - j) *
        (2 ^ j * r₀) ^ (-δ)) * scalarRms volume (ball 0 (2 ^ j * r₀)) q) := by
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = C₅₂ * (Real.sqrt (2 ^ d) * 2 ^ k + 1) := ⟨_, rfl⟩
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  rw [← hK₁]
  have hρ : ∀ m : ℕ, 0 < (2 : ℝ) ^ m * r₀ := fun m => by positivity
  have hr₀ρ : ∀ m : ℕ, r₀ ≤ (2 : ℝ) ^ m * r₀ := fun m => by
    have : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    nlinarith
  have hρmono : ∀ m n : ℕ, m ≤ n → (2 : ℝ) ^ m * r₀ ≤ 2 ^ n * r₀ := fun m n h => by
    have : (2 : ℝ) ^ m ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) h
    nlinarith
  -- (B1)
  have hw : ∀ m, scalarRms volume (ball 0 (2 ^ m * r₀)) (fun x => u (m + 1) x - u m x) ≤
      K₁ * (2 ^ m * r₀) ^ (-δ) * scalarRms volume (ball 0 (2 ^ m * r₀)) q := fun m => by
    have h1 := (hu (m + 1)).2
    rw [pow_succ, mul_comm _ (2 : ℝ), mul_assoc] at h1
    have h := scalarRms_increment_le hq hqL2 (hρ m) hδ0.le hC₅₂ (hu m).1.1
      (by have := (hu (m + 1)).1.1; rwa [pow_succ, mul_comm _ (2 : ℝ), mul_assoc] at this)
      (hu m).2 h1
    rwa [← hK₁] at h
  -- (B2)
  have hB : ∀ j n, j ≤ n → scalarRms volume (ball 0 (2 ^ j * r₀))
      (fun x => (u (n + 1) x - u n x) - φ n x) ≤
      C₃ * K₁ * (((2 : ℝ) ^ (-(δ / 2))) ^ (n - j) * (2 ^ j * r₀) ^ (-δ)) *
        scalarRms volume (ball 0 (2 ^ j * r₀)) q := fun j n hjn => by
    have ht : (0 : ℝ) < 2 ^ (n - j) := by positivity
    have hφn := (hφ n).2 _ (hr₀ρ j) (hρmono j n hjn)
    rw [← two_pow_sub_mul hjn r₀] at hφn
    have hwn := hw n
    rw [← two_pow_sub_mul hjn r₀] at hwn
    have h := scalarRms_correction_small hq (hρ j) ht hC₃ hφn hwn
    rwa [two_pow_rpow] at h
  refine ⟨fun j n hjn => ?_, fun j n hjn => hB j n hjn⟩
  -- the decomposition of `v_n - q`
  have hdec : ∀ n, j ≤ n → ∀ x, (u n x - ∑ m ∈ Finset.range n, φ m x) - q x =
      (u j x - q x) + ∑ m ∈ Finset.Ico j n, ((u (m + 1) x - u m x) - φ m x) -
        ∑ m ∈ Finset.range j, φ m x := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => intro x; rw [Finset.Ico_self, Finset.sum_empty]; ring
    | succ n hjn ih =>
      intro x
      rw [Finset.sum_range_succ, Finset.sum_Ico_succ_top hjn]
      have := ih x
      linarith
  have hx1 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(δ / 2)) := (Real.rpow_pos_of_pos two_pos _).le
  have hx1' : (2 : ℝ) ^ (-(δ / 2)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hx2 : (0 : ℝ) ≤ (2 : ℝ) ^ (δ - 1) := (Real.rpow_pos_of_pos two_pos _).le
  have hx2' : (2 : ℝ) ^ (δ - 1) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hρj := hρ j
  have hqj := hqL2 _ hρj
  have hq0 := scalarRms_nonneg (d := d) (ball 0 (2 ^ j * r₀)) q
  have hρδ : 0 ≤ (2 ^ j * r₀ : ℝ) ^ (-δ) := Real.rpow_nonneg hρj.le _
  -- membership in `L²(B_{r_j})`
  have huL2 : ∀ m, j ≤ m → MemLp (u m) 2 (volume.restrict (ball (0 : Vec d) (2 ^ j * r₀))) :=
    fun m hm => (hu m).1.1.mono_measure (Measure.restrict_mono
      (ball_zero_subset_ball_zero (hρmono j m hm)) le_rfl)
  have hφL2 : ∀ m, MemLp (φ m) 2 (volume.restrict (ball (0 : Vec d) (2 ^ j * r₀))) := fun m =>
    ((hφ m).1.1 _ hρj).1
  classical
  set F : ℕ → Vec d → ℝ := fun m => if j ≤ m then fun x => (u (m + 1) x - u m x) - φ m x
    else fun _ => 0 with hFdef
  have hF : ∀ m, MemLp (F m) 2 (volume.restrict (ball (0 : Vec d) (2 ^ j * r₀))) := fun m => by
    by_cases h : j ≤ m
    · simp only [hFdef, h, ite_true]
      exact ((huL2 (m + 1) (by omega)).sub (huL2 m h)).sub (hφL2 m)
    · simp only [hFdef, h, ite_false]; exact MemLp.zero
  have hS1 := scalarRms_finset_sum_le (Finset.Ico j n) hF (fun _ => 1)
  have hS2 := scalarRms_finset_sum_le (Finset.range j) hφL2 (fun _ => 1)
  have eS1 : (fun x => ∑ m ∈ Finset.Ico j n, (1 : ℝ) * F m x) =
      fun x => ∑ m ∈ Finset.Ico j n, ((u (m + 1) x - u m x) - φ m x) := by
    funext x
    refine Finset.sum_congr rfl fun m hm => ?_
    simp only [hFdef, (Finset.mem_Ico.1 hm).1, ite_true, one_mul]
  have eS2 : (fun x => ∑ m ∈ Finset.range j, (1 : ℝ) * φ m x) =
      fun x => ∑ m ∈ Finset.range j, φ m x := by
    funext x; simp only [one_mul]
  rw [eS1] at hS1
  rw [eS2] at hS2
  -- the terms of the scales between `r_j` and `r_n`
  have hT1 : ∑ m ∈ Finset.Ico j n, |(1 : ℝ)| * scalarRms volume (ball 0 (2 ^ j * r₀)) (F m) ≤
      C₃ * K₁ / (1 - (2 : ℝ) ^ (-(δ / 2))) * (2 ^ j * r₀) ^ (-δ) *
        scalarRms volume (ball 0 (2 ^ j * r₀)) q := by
    have hterm : ∀ m ∈ Finset.Ico j n, |(1 : ℝ)| * scalarRms volume (ball 0 (2 ^ j * r₀)) (F m) ≤
        C₃ * K₁ * ((2 : ℝ) ^ (-(δ / 2))) ^ (m - j) * ((2 ^ j * r₀) ^ (-δ) *
          scalarRms volume (ball 0 (2 ^ j * r₀)) q) := fun m hm => by
      have hjm := (Finset.mem_Ico.1 hm).1
      simp only [abs_one, one_mul, hFdef, hjm, ite_true]
      refine (hB j m hjm).trans (le_of_eq ?_)
      ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    have hgeo : ∑ i ∈ Finset.range (n - j), ((2 : ℝ) ^ (-(δ / 2))) ^ i ≤
        1 / (1 - (2 : ℝ) ^ (-(δ / 2))) := by
      have h := geom_sum_Ico_le_of_lt_one hx1 hx1' (m := 0) (n := n - j)
      rwa [← Finset.range_eq_Ico, pow_zero] at h
    have hc : 0 ≤ C₃ * K₁ := mul_nonneg hC₃ hK₁0
    calc (C₃ * K₁ * ∑ i ∈ Finset.range (n - j), ((2 : ℝ) ^ (-(δ / 2))) ^ i) *
          ((2 ^ j * r₀) ^ (-δ) * scalarRms volume (ball 0 (2 ^ j * r₀)) q)
        ≤ (C₃ * K₁ * (1 / (1 - (2 : ℝ) ^ (-(δ / 2))))) *
          ((2 ^ j * r₀) ^ (-δ) * scalarRms volume (ball 0 (2 ^ j * r₀)) q) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgeo hc) (mul_nonneg hρδ hq0)
      _ = _ := by ring
  -- the corrections of the scales below `r_j`
  have hT2 : ∑ m ∈ Finset.range j, |(1 : ℝ)| * scalarRms volume (ball 0 (2 ^ j * r₀)) (φ m) ≤
      4 * C₂₇ * (1 + C₃) * K₁ / (1 - (2 : ℝ) ^ (δ - 1)) * (2 ^ j * r₀) ^ (-δ) *
        scalarRms volume (ball 0 (2 ^ j * r₀)) q := by
    have hterm : ∀ m ∈ Finset.range j, |(1 : ℝ)| * scalarRms volume (ball 0 (2 ^ j * r₀)) (φ m) ≤
        4 * C₂₇ * (1 + C₃) * K₁ * ((2 : ℝ) ^ (δ - 1)) ^ (j - m) * ((2 ^ j * r₀) ^ (-δ) *
          scalarRms volume (ball 0 (2 ^ j * r₀)) q) := fun m hm => by
      have hmj : m ≤ j := (Finset.mem_range.1 hm).le
      rw [abs_one, one_mul]
      have ht1 : (1 : ℝ) ≤ 2 ^ (j - m) := one_le_pow₀ (by norm_num)
      have hφw : scalarRms volume (ball 0 (2 ^ m * r₀)) (fun x => (u (m + 1) x - u m x) - φ m x) ≤
          C₃ * scalarRms volume (ball 0 (2 ^ m * r₀)) (fun x => u (m + 1) x - u m x) := by
        have h := (hφ m).2 _ (hr₀ρ m) le_rfl
        rwa [div_self (hρ m).ne', Real.one_rpow, mul_one] at h
      have hwL2 : MemLp (fun x => u (m + 1) x - u m x) 2
          (volume.restrict (ball (0 : Vec d) (2 ^ m * r₀))) :=
        ((hu (m + 1)).1.1.mono_measure (Measure.restrict_mono
          (ball_zero_subset_ball_zero (hρmono m (m + 1) (Nat.le_succ m))) le_rfl)).sub (hu m).1.1
      have h := scalarRms_correction_large hk hq (hρ m) ht1 hr₀ (hr₀ρ m) hδ0.le hC₁ hsmall hC₂₇ hC₃
        hwL2 (fun r hr => ((hφ m).1.1 r hr).1) (fun r hr => ((hp m).1.2 r hr).1) (hp m).2
        (hgrow m _ _ (hρ m) ht1) hφw (hw m)
      rw [two_pow_sub_mul hmj, two_pow_rpow] at h
      refine h.trans (le_of_eq ?_)
      ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    have hgeo : ∑ m ∈ Finset.range j, ((2 : ℝ) ^ (δ - 1)) ^ (j - m) ≤
        1 / (1 - (2 : ℝ) ^ (δ - 1)) := by
      rw [← Finset.sum_range_reflect]
      have e : ∀ i ∈ Finset.range j, ((2 : ℝ) ^ (δ - 1)) ^ (j - (j - 1 - i)) ≤
          ((2 : ℝ) ^ (δ - 1)) ^ i := fun i hi => by
        have hi' := Finset.mem_range.1 hi
        exact pow_le_pow_of_le_one hx2 hx2'.le (by omega)
      refine (Finset.sum_le_sum e).trans ?_
      have h := geom_sum_Ico_le_of_lt_one hx2 hx2' (m := 0) (n := j)
      rwa [← Finset.range_eq_Ico, pow_zero] at h
    have hc : 0 ≤ 4 * C₂₇ * (1 + C₃) * K₁ := by positivity
    calc (4 * C₂₇ * (1 + C₃) * K₁ * ∑ m ∈ Finset.range j, ((2 : ℝ) ^ (δ - 1)) ^ (j - m)) *
          ((2 ^ j * r₀) ^ (-δ) * scalarRms volume (ball 0 (2 ^ j * r₀)) q)
        ≤ (4 * C₂₇ * (1 + C₃) * K₁ * (1 / (1 - (2 : ℝ) ^ (δ - 1)))) *
          ((2 ^ j * r₀) ^ (-δ) * scalarRms volume (ball 0 (2 ^ j * r₀)) q) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgeo hc) (mul_nonneg hρδ hq0)
      _ = _ := by ring
  -- assembly
  rw [show (fun x => (u n x - ∑ m ∈ Finset.range n, φ m x) - q x) =
      fun x => ((u j x - q x) + ∑ m ∈ Finset.Ico j n, ((u (m + 1) x - u m x) - φ m x)) -
        ∑ m ∈ Finset.range j, φ m x from funext (hdec n hjn)]
  have hmemA : MemLp (fun x => u j x - q x) 2 (volume.restrict (ball (0 : Vec d) (2 ^ j * r₀))) :=
    (huL2 j le_rfl).sub hqj
  have hmemS1 : MemLp (fun x => ∑ m ∈ Finset.Ico j n, ((u (m + 1) x - u m x) - φ m x)) 2
      (volume.restrict (ball (0 : Vec d) (2 ^ j * r₀))) := by
    have h := memLp_finset_sum' (Finset.Ico j n) (fun m _ => hF m)
    have e : (∑ m ∈ Finset.Ico j n, F m) =
        fun x => ∑ m ∈ Finset.Ico j n, ((u (m + 1) x - u m x) - φ m x) := by
      funext x
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun m hm => ?_
      simp only [hFdef, (Finset.mem_Ico.1 hm).1, ite_true]
    rwa [e] at h
  have hmemS2 : MemLp (fun x => ∑ m ∈ Finset.range j, φ m x) 2
      (volume.restrict (ball (0 : Vec d) (2 ^ j * r₀))) := by
    have h := memLp_finset_sum' (Finset.range j) (fun m _ => hφL2 m)
    have e : (∑ m ∈ Finset.range j, φ m) = fun x => ∑ m ∈ Finset.range j, φ m x := by
      funext x; rw [Finset.sum_apply]
    rwa [e] at h
  calc scalarRms volume (ball 0 (2 ^ j * r₀))
        (fun x => ((u j x - q x) + ∑ m ∈ Finset.Ico j n, ((u (m + 1) x - u m x) - φ m x)) -
          ∑ m ∈ Finset.range j, φ m x)
      ≤ (scalarRms volume (ball 0 (2 ^ j * r₀)) (fun x => u j x - q x) +
          scalarRms volume (ball 0 (2 ^ j * r₀))
            (fun x => ∑ m ∈ Finset.Ico j n, ((u (m + 1) x - u m x) - φ m x))) +
          scalarRms volume (ball 0 (2 ^ j * r₀)) (fun x => ∑ m ∈ Finset.range j, φ m x) :=
        (scalarRms_sub_le (hmemA.add hmemS1) hmemS2).trans
          (add_le_add (scalarRms_add_le hmemA hmemS1) le_rfl)
    _ ≤ (C₅₂ * (2 ^ j * r₀) ^ (-δ) * scalarRms volume (ball 0 (2 ^ j * r₀)) q +
          C₃ * K₁ / (1 - (2 : ℝ) ^ (-(δ / 2))) * (2 ^ j * r₀) ^ (-δ) *
            scalarRms volume (ball 0 (2 ^ j * r₀)) q) +
          4 * C₂₇ * (1 + C₃) * K₁ / (1 - (2 : ℝ) ^ (δ - 1)) * (2 ^ j * r₀) ^ (-δ) *
            scalarRms volume (ball 0 (2 ^ j * r₀)) q :=
        add_le_add (add_le_add (hu j).2 (hS1.trans hT1)) (hS2.trans hT2)
    _ = _ := by ring

end QSH
