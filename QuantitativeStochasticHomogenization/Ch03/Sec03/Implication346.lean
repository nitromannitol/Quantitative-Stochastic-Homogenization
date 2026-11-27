import QuantitativeStochasticHomogenization.Ch03.Sec03.Bound353
import QuantitativeStochasticHomogenization.Ch03.Sec03.SolutionLimit

/-!
# The implication (3.46) for homogeneous polynomials

Armstrong–Kuusi–Mourrat, Section 3.3, proof of (3.46), Steps 1 and 2: for one coefficient field `a`
and a homogeneous `q ∈ Ā_k` of degree `k ≥ 1`, the estimate (3.52) above a scale `r₀`, `(iii')_{k-1}`
and `(i)_{k-1}` give `u ∈ A_k` with `‖u - q‖_{L̲²(B_R)} ≤ C R^{-δ} ‖q‖_{L̲²(B_R)}` for `R ≥ r₀`
(`implication_346_homogeneous`). The sequences of Step 1 are chosen as in the book on the radii
`2^m r₀`, (3.53) is `bound_353`, and the limit of Step 2 is `solution_limit`, without compactness.
-/

open MeasureTheory Filter Set Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

set_option maxHeartbeats 400000 in
/-- **(3.46) for homogeneous `q`**, deterministic. -/
theorem implication_346_homogeneous {k : ℕ} (hk : 1 ≤ k) {δ C₅₂ C₃ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hC₅₂ : 0 ≤ C₅₂) (hC₃ : 0 ≤ C₃) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (_ : 1 ≤ Λ) (a : CoefficientField d Λ) (A : Mat d) (q : Vec d → ℝ),
      q ∈ harmonicPolys A k → (∀ t : ℝ, 0 < t → ∀ x, q (t • x) = t ^ k * q x) →
      ∀ (r₀ C₁ : ℝ), 0 < r₀ → 0 ≤ C₁ → C₁ * r₀ ^ (-δ) ≤ 1 / 2 →
      (∀ r : ℝ, r₀ ≤ r → ∃ u, IsSolutionBall a r u ∧
        scalarRms volume (ball 0 r) (fun x => u x - q x) ≤
          C₅₂ * r ^ (-δ) * scalarRms volume (ball 0 r) q) →
      (∀ R : ℝ, r₀ ≤ R → ∀ w, IsSolutionBall a R w → ∃ φ ∈ solutionGrowthSpace a (k - 1),
        ∀ r : ℝ, r₀ ≤ r → r ≤ R → scalarRms volume (ball 0 r) (fun x => w x - φ x) ≤
          C₃ * (r / R) ^ ((k : ℝ) - δ / 2) * scalarRms volume (ball 0 R) w) →
      (∀ φ ∈ solutionGrowthSpace a (k - 1), ∃ p ∈ harmonicPolys A (k - 1), ∀ R : ℝ, r₀ ≤ R →
        scalarRms volume (ball 0 R) (fun x => φ x - p x) ≤
          C₁ * R ^ (-δ) * scalarRms volume (ball 0 R) p) →
      ∃ u ∈ solutionGrowthSpace a k, ∀ j : ℕ,
        scalarRms volume (ball 0 (2 ^ j * r₀)) (fun x => u x - q x) ≤
          C * (2 ^ j * r₀) ^ (-δ) * scalarRms volume (ball 0 (2 ^ j * r₀)) q := by
  obtain ⟨C₂₇, hC₂₇, hgrow0⟩ := scalarRms_poly_growth (d := d) (k - 1)
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = C₅₂ * (Real.sqrt (2 ^ d) * 2 ^ k + 1) := ⟨_, rfl⟩
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  obtain ⟨K₅₃, hK₅₃⟩ : ∃ K : ℝ, K = C₅₂ + C₃ * K₁ / (1 - (2 : ℝ) ^ (-(δ / 2))) +
      4 * C₂₇ * (1 + C₃) * K₁ / (1 - (2 : ℝ) ^ (δ - 1)) := ⟨_, rfl⟩
  have hx2' : (2 : ℝ) ^ (δ - 1) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hε1 : (2 : ℝ) ^ (-(δ / 2)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hK₅₃0 : 0 ≤ K₅₃ := by
    rw [hK₅₃]
    have h1 : 0 < 1 - (2 : ℝ) ^ (-(δ / 2)) := by linarith
    have h2 : 0 < 1 - (2 : ℝ) ^ (δ - 1) := by linarith
    positivity
  refine ⟨K₅₃, hK₅₃0, fun hΛ a A q hqA hq r₀ C₁ hr₀ hC₁ hsmall H52 Hiii Hi => ?_⟩
  have hρ : ∀ m : ℕ, 0 < (2 : ℝ) ^ m * r₀ := fun m => by positivity
  have hr₀ρ : ∀ m : ℕ, r₀ ≤ (2 : ℝ) ^ m * r₀ := fun m => by
    have : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    nlinarith
  have hρmono : ∀ m n : ℕ, m ≤ n → (2 : ℝ) ^ m * r₀ ≤ 2 ^ n * r₀ := fun m n h => by
    have : (2 : ℝ) ^ m ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) h
    nlinarith
  have hqL2 : ∀ r : ℝ, 0 < r → MemLp q 2 (volume.restrict (ball (0 : Vec d) r)) := fun r hr =>
    (hqA.2 r hr).1
  -- Step 1: the sequences
  choose u hu using fun m : ℕ => H52 _ (hr₀ρ m)
  have hw : ∀ m, IsSolutionBall a (2 ^ m * r₀) (fun x => u (m + 1) x - u m x) := fun m =>
    ((hu (m + 1)).1.mono (hρmono m (m + 1) (Nat.le_succ m))).sub (hu m).1
  choose φ hφA hφ using fun m : ℕ => Hiii _ (hr₀ρ m) _ (hw m)
  choose p hpA hp using fun m : ℕ => Hi (φ m) (hφA m)
  have hgrow : ∀ m (t ρ : ℝ), 0 < ρ → 1 ≤ t → scalarRms volume (ball 0 (t * ρ)) (p m) ≤
      C₂₇ * t ^ (k - 1) * scalarRms volume (ball 0 ρ) (p m) := fun m t ρ hρ0 ht => by
    obtain ⟨⟨P, hP, hPe⟩, -⟩ := hpA m
    have hpP : p m = fun x => MvPolynomial.eval x P := funext hPe
    have h := hgrow0 P hP ρ (t * ρ) hρ0 (by nlinarith)
    rw [← hpP, show t * ρ / ρ = t by field_simp] at h
    exact h
  obtain ⟨hA53, hB53⟩ := bound_353 (a := a) (A := A) hk hq hqL2 hr₀ hδ0 hδ1 hC₅₂ hC₃ hC₁ hC₂₇
    hsmall u φ p (fun m => hu m) (fun m => ⟨hφA m, hφ m⟩) (fun m => ⟨hpA m, hp m⟩) hgrow
  -- Step 2: the limit
  have hvsol : ∀ n, IsSolutionBall a (2 ^ n * r₀) (fun x => u n x - ∑ m ∈ Finset.range n, φ m x) :=
    fun n => (hu n).1.sub (isSolutionBall_of_mem_solutionGrowthSpace
      (sum_mem_solutionGrowthSpace _ fun m _ => hφA m) (hρ n))
  choose hvL2 gv hgv hvgrad hvdiv using hvsol
  have hε0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(δ / 2)) := (Real.rpow_pos_of_pos two_pos _).le
  obtain ⟨ul, hul, hlim⟩ := solution_limit hΛ a hr₀ hε0 hε1
    (fun n x => u n x - ∑ m ∈ Finset.range n, φ m x) gv
    (fun n => ⟨hvL2 n, hgv n, hvgrad n, hvdiv n⟩)
    (fun j => C₃ * K₁ * (2 ^ j * r₀) ^ (-δ) * scalarRms volume (ball 0 (2 ^ j * r₀)) q)
    (fun j => by
      have := Real.rpow_nonneg (hρ j).le (-δ)
      have := scalarRms_nonneg (d := d) (ball 0 (2 ^ j * r₀)) q
      positivity)
    (fun j n hjn => by
      have h := hB53 j n hjn
      rw [← hK₁] at h
      have e : (fun x => (u (n + 1) x - ∑ m ∈ Finset.range (n + 1), φ m x) -
          (u n x - ∑ m ∈ Finset.range n, φ m x)) = fun x => (u (n + 1) x - u n x) - φ n x := by
        funext x; rw [Finset.sum_range_succ]; ring
      rw [e]
      refine h.trans (le_of_eq ?_)
      ring)
  -- the estimate for the limit
  have hest : ∀ j : ℕ, scalarRms volume (ball 0 (2 ^ j * r₀)) (fun x => ul x - q x) ≤
      K₅₃ * (2 ^ j * r₀) ^ (-δ) * scalarRms volume (ball 0 (2 ^ j * r₀)) q := by
    intro j
    have hulL2 := (hul _ (hρ j)).1
    have hle : ∀ n, j ≤ n → scalarRms volume (ball 0 (2 ^ j * r₀)) (fun x => ul x - q x) ≤
        scalarRms volume (ball 0 (2 ^ j * r₀))
          (fun x => (u n x - ∑ m ∈ Finset.range n, φ m x) - ul x) +
        K₅₃ * (2 ^ j * r₀) ^ (-δ) * scalarRms volume (ball 0 (2 ^ j * r₀)) q := fun n hjn => by
      have hvj : MemLp (fun x => u n x - ∑ m ∈ Finset.range n, φ m x) 2
          (volume.restrict (ball (0 : Vec d) (2 ^ j * r₀))) :=
        (hvL2 n).mono_measure (Measure.restrict_mono
          (ball_zero_subset_ball_zero (hρmono j n hjn)) le_rfl)
      have e : (fun x => ul x - q x) = fun x => ((u n x - ∑ m ∈ Finset.range n, φ m x) - q x) -
          ((u n x - ∑ m ∈ Finset.range n, φ m x) - ul x) := by funext x; ring
      rw [e]
      refine (scalarRms_sub_le (f := fun x => (u n x - ∑ m ∈ Finset.range n, φ m x) - q x)
        (g := fun x => (u n x - ∑ m ∈ Finset.range n, φ m x) - ul x)
        (hvj.sub (hqL2 _ (hρ j))) (hvj.sub hulL2)).trans ?_
      have h := hA53 j n hjn
      rw [← hK₁, ← hK₅₃] at h
      linarith
    have hT := (hlim j).add_const (K₅₃ * (2 ^ j * r₀) ^ (-δ) *
      scalarRms volume (ball 0 (2 ^ j * r₀)) q)
    rw [zero_add] at hT
    refine ge_of_tendsto hT ?_
    filter_upwards [eventually_ge_atTop j] with n hn
    exact hle n hn
  -- the growth of the limit
  refine ⟨ul, ⟨hul, ?_⟩, hest⟩
  have hq1 : ∀ t : ℝ, 0 < t → scalarRms volume (ball 0 t) q =
      t ^ k * scalarRms volume (ball (0 : Vec d) 1) q := fun t ht => by
    have h := scalarRms_ball_homogeneous hq (r := 1) ht
    rwa [mul_one] at h
  obtain ⟨Cg, hCg⟩ : ∃ C : ℝ, C = (1 + Real.sqrt (2 ^ d) * K₅₃ * r₀ ^ (-δ) * 2 ^ k) *
      scalarRms volume (ball (0 : Vec d) 1) q := ⟨_, rfl⟩
  have hq10 := scalarRms_nonneg (d := d) (ball 0 1) q
  have hCg0 : 0 ≤ Cg := by
    rw [hCg]; have := Real.rpow_nonneg hr₀.le (-δ); positivity
  have hbound : ∀ r : ℝ, r₀ ≤ r → scalarRms volume (ball 0 r) ul ≤ Cg * r ^ k := by
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
    classical
    have hex : ∃ j : ℕ, r ≤ 2 ^ j * r₀ := by
      obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (r / r₀) (one_lt_two : (1 : ℝ) < 2)
      exact ⟨j, by rw [div_lt_iff₀ hr₀] at hj; linarith⟩
    obtain ⟨j, hjdef⟩ : ∃ j, j = Nat.find hex := ⟨_, rfl⟩
    have hj1 : r ≤ 2 ^ j * r₀ := by rw [hjdef]; exact Nat.find_spec hex
    have hj2 : 2 ^ j * r₀ ≤ 2 * r := by
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · rw [h0, pow_zero, one_mul]; linarith
      · have h := Nat.find_min hex (show j - 1 < Nat.find hex by rw [← hjdef]; omega)
        push Not at h
        have e : (2 : ℝ) ^ j = 2 * 2 ^ (j - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel hpos]
        rw [e]; nlinarith
    have hulr := (hul r hr0).1
    have hulj := (hul _ (hρ j)).1
    have hsplit : scalarRms volume (ball 0 r) ul ≤
        scalarRms volume (ball 0 r) q + scalarRms volume (ball 0 r) (fun x => ul x - q x) := by
      have h := scalarRms_add_le (f := q) (g := fun x => ul x - q x) (hqL2 r hr0)
        (hulr.sub (hqL2 r hr0))
      simpa only [add_sub_cancel] using h
    have h1 := scalarRms_ball_le hr0 hj1 (hulj.sub (hqL2 _ (hρ j)))
    have hratio : Real.sqrt ((2 ^ j * r₀ / r) ^ d) ≤ Real.sqrt (2 ^ d) :=
      Real.sqrt_le_sqrt (pow_le_pow_left₀ (by positivity) (by rw [div_le_iff₀ hr0]; linarith) d)
    have hpow : (2 ^ j * r₀ : ℝ) ^ (-δ) ≤ r₀ ^ (-δ) :=
      Real.rpow_le_rpow_of_nonpos hr₀ (hr₀ρ j) (by linarith)
    have hqj : scalarRms volume (ball 0 (2 ^ j * r₀)) q ≤ 2 ^ k * r ^ k *
        scalarRms volume (ball (0 : Vec d) 1) q := by
      rw [hq1 _ (hρ j), ← mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hρ j).le hj2 k) hq10
    have hs := Real.sqrt_nonneg ((2 : ℝ) ^ d)
    calc scalarRms volume (ball 0 r) ul
        ≤ r ^ k * scalarRms volume (ball (0 : Vec d) 1) q +
            Real.sqrt (2 ^ d) * (K₅₃ * r₀ ^ (-δ) * (2 ^ k * r ^ k *
              scalarRms volume (ball (0 : Vec d) 1) q)) := by
          rw [← hq1 r hr0]
          refine hsplit.trans (add_le_add le_rfl ?_)
          refine h1.trans (mul_le_mul hratio ((hest j).trans ?_) (scalarRms_nonneg _ _) hs)
          exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hK₅₃0) hqj (scalarRms_nonneg _ _)
            (mul_nonneg hK₅₃0 (Real.rpow_nonneg hr₀.le _))
      _ = Cg * r ^ k := by rw [hCg]; ring
  have hup : Tendsto (fun r : ℝ => Cg * r⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul Cg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with r hr
    exact mul_nonneg (by positivity) (scalarRms_nonneg _ _)
  · filter_upwards [eventually_ge_atTop r₀] with r hr
    have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
    calc (r ^ (k + 1))⁻¹ * scalarRms volume (ball 0 r) ul ≤ (r ^ (k + 1))⁻¹ * (Cg * r ^ k) :=
          mul_le_mul_of_nonneg_left (hbound r hr) (by positivity)
      _ = Cg * r⁻¹ := by field_simp; ring

end QSH
