import QuantitativeStochasticHomogenization.Ch03.Sec03.Implication348
import QuantitativeStochasticHomogenization.Ch03.Sec03.WeakGradientH10
import QuantitativeStochasticHomogenization.Ch03.Sec03.TestMollification
import QuantitativeStochasticHomogenization.AppD.HeatSmoothing

/-!
# Limits of solutions with geometrically small increments

Step 2 of the proof of (3.46) needs a solution on `ℝ^d` as the limit of solutions `v_n` in growing
balls. Here no compactness is used: the increments `v_{n+1} - v_n` are geometrically small in `L²` on
every ball, so `v_n` converges almost everywhere and in `L²` on every ball (`ae_limit_of_geometric`,
from the completeness of `L²` in Mathlib).
-/

open MeasureTheory Filter Set Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The `L²` norm on `U` is `|U|^{1/2}` times the normalized `L̲²` norm. -/
theorem eLpNorm_eq_ofReal_sqrt_mul_scalarRms {U : Set (Vec d)} (hU0 : 0 < volume.real U)
    {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict U)) :
    eLpNorm f 2 (volume.restrict U) =
      ENNReal.ofReal (Real.sqrt (volume.real U) * scalarRms volume U f) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  congr 1
  have e1 : (fun a => ‖f a‖ ^ (ENNReal.toReal 2)) = fun a => f a ^ 2 := by
    funext a
    rw [ENNReal.toReal_ofNat, Real.norm_eq_abs, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, sq_abs]
  rw [e1, ENNReal.toReal_ofNat, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  unfold scalarRms
  rw [setAverage_eq, smul_eq_mul, ← Real.sqrt_mul hU0.le, ← mul_assoc,
    mul_inv_cancel₀ hU0.ne', one_mul]

/-- **Limits of sequences with geometrically small increments in `L²`.** -/
theorem ae_limit_of_geometric {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : ℕ → α → ℝ} (hf : ∀ n, MemLp (f n) 2 μ) {c ε : ℝ} (hc : 0 ≤ c) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hinc : ∀ n, eLpNorm (f (n + 1) - f n) 2 μ ≤ ENNReal.ofReal (c * ε ^ n)) :
    (∀ᵐ x ∂μ, ∃ l, Tendsto (fun n => f n x) atTop (𝓝 l)) ∧
      ∀ F : α → ℝ, (∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (F x))) →
        MemLp F 2 μ ∧ Tendsto (fun n => eLpNorm (f n - F) 2 μ) atTop (𝓝 0) := by
  have h1ε : 0 < 1 - ε := by linarith
  -- telescoping
  have htel : ∀ n m, n ≤ m → eLpNorm (f m - f n) 2 μ ≤
      ENNReal.ofReal (c * ε ^ n / (1 - ε)) := by
    have hsum : ∀ n k, eLpNorm (f (n + k) - f n) 2 μ ≤
        ENNReal.ofReal (∑ i ∈ Finset.range k, c * ε ^ (n + i)) := by
      intro n k
      induction k with
      | zero => simp
      | succ k ih =>
        have e : f (n + (k + 1)) - f n = (f (n + k + 1) - f (n + k)) + (f (n + k) - f n) := by
          rw [← add_assoc]; abel
        rw [e, Finset.sum_range_succ, ENNReal.ofReal_add (Finset.sum_nonneg fun i _ => by positivity)
          (by positivity)]
        refine le_trans (eLpNorm_add_le (f := f (n + k + 1) - f (n + k)) (g := f (n + k) - f n)
          one_le_two) ?_
        rw [add_comm (ENNReal.ofReal _)]
        exact add_le_add (hinc (n + k)) ih
    intro n m hnm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    refine (hsum n k).trans (ENNReal.ofReal_le_ofReal ?_)
    have hgeo : ∑ i ∈ Finset.range k, ε ^ i ≤ 1 / (1 - ε) := by
      have h := geom_sum_Ico_le_of_lt_one hε0 hε1 (m := 0) (n := k)
      rwa [← Finset.range_eq_Ico, pow_zero] at h
    calc ∑ i ∈ Finset.range k, c * ε ^ (n + i) = c * ε ^ n * ∑ i ∈ Finset.range k, ε ^ i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [pow_add]; ring
      _ ≤ c * ε ^ n * (1 / (1 - ε)) := mul_le_mul_of_nonneg_left hgeo (by positivity)
      _ = c * ε ^ n / (1 - ε) := by ring
  -- the Cauchy bound
  obtain ⟨B, hB⟩ : ∃ B : ℕ → ENNReal, B = fun N => ENNReal.ofReal (c * ε ^ N / (1 - ε) + (1 / 2) ^ N) :=
    ⟨_, rfl⟩
  have hBs : Summable fun N : ℕ => c * ε ^ N / (1 - ε) + (1 / 2 : ℝ) ^ N :=
    (((summable_geometric_of_lt_one hε0 hε1).mul_left c).div_const _).add
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have hBt : ∑' N, B N ≠ ⊤ := by
    rw [hB, ← ENNReal.ofReal_tsum_of_nonneg (fun N => by positivity) hBs]
    exact ENNReal.ofReal_ne_top
  have hcau : ∀ N n m : ℕ, N ≤ n → N ≤ m → eLpNorm (f n - f m) 2 μ < B N := by
    intro N n m hn hm
    have key : ∀ n m, N ≤ n → n ≤ m → eLpNorm (f m - f n) 2 μ < B N := fun n m hn hnm => by
      refine (htel n m hnm).trans_lt ?_
      rw [hB, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
      have : c * ε ^ n / (1 - ε) ≤ c * ε ^ N / (1 - ε) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one hε0 hε1.le hn) hc) h1ε.le
      have : (0 : ℝ) < (1 / 2) ^ N := by positivity
      linarith
    rcases le_total n m with h | h
    · rw [eLpNorm_sub_comm]; exact key n m hn h
    · exact key m n hm h
  have hae := Lp.ae_tendsto_of_cauchy_eLpNorm (fun n => (hf n).aestronglyMeasurable) one_le_two
    hBt hcau
  refine ⟨hae, fun F hF => ?_⟩
  have hFm : AEStronglyMeasurable F μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hf n).aestronglyMeasurable) hF
  have ht := Lp.cauchy_tendsto_of_tendsto (fun n => (hf n).aestronglyMeasurable) F hBt hcau hF
  exact ⟨Lp.memLp_of_cauchy_tendsto one_le_two hf F ht, ht⟩

/-- The norm of a component is at most the norm of the vector field. -/
theorem scalarRms_coord_le_vectorRms {U : Set (Vec d)} {G : Vec d → Vec d}
    (hG : ∀ j, MemLp (fun x => G x j) 2 (volume.restrict U)) (i : Fin d) :
    scalarRms volume U (fun x => G x i) ≤ vectorRms volume U G := by
  unfold scalarRms vectorRms
  refine Real.sqrt_le_sqrt ?_
  rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 measureReal_nonneg)
  refine integral_mono (hG i).integrable_sq ?_ fun x => ?_
  · have h : (fun x => euclideanSq (G x)) = fun x => ∑ j, G x j ^ 2 := by
      funext x; simp only [euclideanSq, dot, sq]
    rw [h]
    exact integrable_finsetSum _ fun j _ => (hG j).integrable_sq
  · simp only [euclideanSq, dot]
    rw [sq]
    exact Finset.single_le_sum (f := fun j => G x j * G x j) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ i)

/-- The limit on one ball of a sequence with geometrically small increments in `L̲²`. -/
theorem limit_on_ball {f : ℕ → Vec d → ℝ} {ρ c ε : ℝ} (hρ : 0 < ρ) (hc : 0 ≤ c) (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) (hf : ∀ n, MemLp (f n) 2 (volume.restrict (ball (0 : Vec d) ρ)))
    (hinc : ∀ n, scalarRms volume (ball 0 ρ) (fun x => f (n + 1) x - f n x) ≤ c * ε ^ n) :
    (∀ᵐ x ∂(volume.restrict (ball (0 : Vec d) ρ)), ∃ l, Tendsto (fun n => f n x) atTop (𝓝 l)) ∧
      ∀ F : Vec d → ℝ, (∀ᵐ x ∂(volume.restrict (ball (0 : Vec d) ρ)),
        Tendsto (fun n => f n x) atTop (𝓝 (F x))) →
        MemLp F 2 (volume.restrict (ball (0 : Vec d) ρ)) ∧
          Tendsto (fun n => eLpNorm (f n - F) 2 (volume.restrict (ball (0 : Vec d) ρ))) atTop (𝓝 0) := by
  have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) ρ)) :=
    isFiniteMeasure_restrict.mpr (volume_ball_ne_top' 0 ρ)
  have hV : 0 < volume.real (ball (0 : Vec d) ρ) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (volume_ball_ne_zero' 0 hρ) (volume_ball_ne_top' 0 ρ)
  refine ae_limit_of_geometric hf (c := Real.sqrt (volume.real (ball (0 : Vec d) ρ)) * c)
    (by positivity) hε0 hε1 fun n => ?_
  rw [show f (n + 1) - f n = fun x => f (n + 1) x - f n x from rfl,
    eLpNorm_eq_ofReal_sqrt_mul_scalarRms (f := fun x => f (n + 1) x - f n x) hV
      ((hf (n + 1)).sub (hf n))]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hinc n) (Real.sqrt_nonneg _)

/-- The Caccioppoli inequality for the difference of two solutions with given gradients. -/
theorem vectorRms_grad_sub_le {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ Cc : ℝ, 0 < Cc ∧ ∀ (a : CoefficientField d Λ) (r : ℝ), 0 < r →
      ∀ (v w : Vec d → ℝ) (g h : Vec d → Vec d),
      MemLp v 2 (volume.restrict (ball 0 r)) → MemLp w 2 (volume.restrict (ball 0 r)) →
      (∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 r))) →
      (∀ i, MemLp (fun x => h x i) 2 (volume.restrict (ball 0 r))) →
      HasWeakGradient (ball 0 r) v g → HasWeakGradient (ball 0 r) w h →
      HasWeakDivergence (ball 0 r) (fun x => (a x).mulVec (g x)) (fun _ => 0) →
      HasWeakDivergence (ball 0 r) (fun x => (a x).mulVec (h x)) (fun _ => 0) →
      vectorRms volume (ball 0 (r / 2)) (fun x => g x - h x) ≤
        Cc * (r⁻¹ * scalarRms volume (ball 0 r) (fun x => v x - w x)) := by
  obtain ⟨C, hC, hcacc⟩ := interiorCaccioppoli (d := d) hΛ
  refine ⟨C, hC, fun a r hr v w g h hv hw hg hh hvg hwh hdg hdh => ?_⟩
  have hgrad : HasWeakGradient (ball 0 r) (fun x => v x - w x) (fun x => g x - h x) := by
    have h1 := hasWeakGradient_add hvg (hwh.const_mul' (-1))
    convert h1 using 1
    · funext x; ring
    · funext x; simp [sub_eq_add_neg]
  have hdiv : HasWeakDivergence (ball 0 r) (fun x => (a x).mulVec (g x - h x) + (fun _ => (0 : Vec d)) x)
      (fun x => -(fun _ => (0 : ℝ)) x) := by
    have h1 := hasWeakDivergence_add hdg (hdh.const_smul' (-1))
    convert h1 using 1
    · funext x; rw [Matrix.mulVec_sub, add_zero]; simp [sub_eq_add_neg]
    · funext x; simp
  have hb := hcacc 0 r hr a (fun x => v x - w x) (fun x => g x - h x) (fun _ => 0) (fun _ => 0)
    (hv.sub hw) (fun i => (hg i).sub (hh i)) hgrad MemLp.zero (fun _ => MemLp.zero) hdiv
  rw [negativeSobolevOneNorm_zero_zero, add_zero] at hb
  have hosc : scalarRms volume (ball 0 r) (fun x => (v x - w x) - ⨍ y in ball 0 r, (v y - w y)) ≤
      scalarRms volume (ball 0 r) (fun x => v x - w x) := by
    refine (scalarRms_sub_setAverage_le_sub_const (u := fun x => v x - w x)
      (volume_ball_ne_top' 0 r) (hv.sub hw) 0).trans ?_
    simp only [sub_zero, le_refl]
  have hnn : 0 ≤ r⁻¹ * scalarRms volume (ball 0 r) (fun x => (v x - w x) - ⨍ y in ball 0 r, (v y - w y)) :=
    mul_nonneg (inv_nonneg.2 hr.le) (scalarRms_nonneg _ _)
  rw [← ENNReal.ofReal_mul hC.le, ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC.le hnn)] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hosc (inv_nonneg.2 hr.le)) hC.le)

/-- The pairing `∫ (a h)·∇φ` as a sum of pairings of the components of `h`. -/
theorem dot_mulVec_gradient_eq {Λ : ℝ} (a : CoefficientField d Λ) (h : Vec d → Vec d)
    (φ : Vec d → ℝ) (x : Vec d) :
    dot ((a x).mulVec (h x)) (gradient φ x) =
      ∑ k, h x k * ∑ i, a x i k * coordinateDerivative i φ x := by
  simp only [dot, gradient, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring

/-- **Limits of solutions with geometrically small increments.** If `v_n` solves `-∇·(a∇v_n) = 0`
in `B_{2^n r₀}` with gradient `g_n`, and `‖v_{n+1} - v_n‖_{L̲²(B_{2^j r₀})} ≤ B_j ε^{n-j}` for
`j ≤ n` with `ε < 1`, then `v_n` converges in `L̲²(B_{2^j r₀})` for every `j` to a solution `u` in
every ball. -/
theorem solution_limit {Λ : ℝ} (hΛ : 1 ≤ Λ) (a : CoefficientField d Λ) {r₀ ε : ℝ} (hr₀ : 0 < r₀)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (v : ℕ → Vec d → ℝ) (g : ℕ → Vec d → Vec d)
    (hv : ∀ n, MemLp (v n) 2 (volume.restrict (ball 0 (2 ^ n * r₀))) ∧
      (∀ i, MemLp (fun x => g n x i) 2 (volume.restrict (ball 0 (2 ^ n * r₀)))) ∧
      HasWeakGradient (ball 0 (2 ^ n * r₀)) (v n) (g n) ∧
      HasWeakDivergence (ball 0 (2 ^ n * r₀)) (fun x => (a x).mulVec (g n x)) (fun _ => 0))
    (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hinc : ∀ j n, j ≤ n → scalarRms volume (ball 0 (2 ^ j * r₀))
      (fun x => v (n + 1) x - v n x) ≤ B j * ε ^ (n - j)) :
    ∃ u : Vec d → ℝ, (∀ R : ℝ, 0 < R → IsSolutionBall a R u) ∧
      ∀ j, Tendsto (fun n => scalarRms volume (ball 0 (2 ^ j * r₀)) (fun x => v n x - u x))
        atTop (𝓝 0) := by
  obtain ⟨Cc, hCc, hcacc⟩ := vectorRms_grad_sub_le (d := d) hΛ
  have hρ : ∀ j : ℕ, 0 < (2 : ℝ) ^ j * r₀ := fun j => by positivity
  have hρmono : ∀ m n : ℕ, m ≤ n → (2 : ℝ) ^ m * r₀ ≤ 2 ^ n * r₀ := fun m n h => by
    have : (2 : ℝ) ^ m ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) h
    nlinarith
  have hsub : ∀ m n : ℕ, m ≤ n → ball (0 : Vec d) (2 ^ m * r₀) ⊆ ball 0 (2 ^ n * r₀) :=
    fun m n h => ball_zero_subset_ball_zero (hρmono m n h)
  have hres : ∀ m n : ℕ, m ≤ n → volume.restrict (ball (0 : Vec d) (2 ^ m * r₀)) ≤
      volume.restrict (ball 0 (2 ^ n * r₀)) := fun m n h => Measure.restrict_mono (hsub m n h) le_rfl
  obtain ⟨u, hu⟩ : ∃ u : Vec d → ℝ, u = fun x => limUnder atTop (fun n => v n x) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : Vec d → Vec d, G = fun x i => limUnder atTop (fun n => g n x i) :=
    ⟨_, rfl⟩
  -- convergence of the values on every ball
  have hval : ∀ j, MemLp u 2 (volume.restrict (ball (0 : Vec d) (2 ^ j * r₀))) ∧
      Tendsto (fun n => eLpNorm (v (n + j) - u) 2 (volume.restrict (ball (0 : Vec d) (2 ^ j * r₀))))
        atTop (𝓝 0) := by
    intro j
    obtain ⟨hae, hlim⟩ := limit_on_ball (f := fun n => v (n + j)) (hρ j) (hB j) hε0 hε1
      (fun n => (hv (n + j)).1.mono_measure (hres j (n + j) (by omega)))
      (fun n => by
        have h := hinc j (n + j) (by omega)
        rwa [show n + j - j = n by omega, show n + j + 1 = n + 1 + j by omega] at h)
    refine hlim u ?_
    filter_upwards [hae] with x ⟨l, hl⟩
    have h1 : Tendsto (fun n => v n x) atTop (𝓝 l) := (Filter.tendsto_add_atTop_iff_nat j).1 hl
    have h2 : Tendsto (fun n => v n x) atTop (𝓝 (u x)) := by
      rw [hu]; exact tendsto_nhds_limUnder ⟨l, h1⟩
    exact (Filter.tendsto_add_atTop_iff_nat j).2 h2
  -- convergence of the gradients on every ball
  have hgrad : ∀ j i, MemLp (fun x => G x i) 2 (volume.restrict (ball (0 : Vec d) (2 ^ j * r₀))) ∧
      Tendsto (fun n => eLpNorm ((fun x => g (n + j + 1) x i) - fun x => G x i) 2
        (volume.restrict (ball (0 : Vec d) (2 ^ j * r₀)))) atTop (𝓝 0) := by
    intro j i
    have hρ2 : (2 : ℝ) ^ (j + 1) * r₀ / 2 = 2 ^ j * r₀ := by rw [pow_succ]; ring
    have hincg : ∀ n, scalarRms volume (ball 0 (2 ^ j * r₀))
        (fun x => g (n + 1 + j + 1) x i - g (n + j + 1) x i) ≤
          Cc * (((2 : ℝ) ^ (j + 1) * r₀)⁻¹ * B (j + 1)) * ε ^ n := fun n => by
      have hm1 : j + 1 ≤ n + j + 1 := by omega
      have hm2 : j + 1 ≤ n + 1 + j + 1 := by omega
      have hc := hcacc a _ (hρ (j + 1)) (v (n + 1 + j + 1)) (v (n + j + 1)) (g (n + 1 + j + 1))
        (g (n + j + 1)) ((hv _).1.mono_measure (hres _ _ hm2))
        ((hv _).1.mono_measure (hres _ _ hm1))
        (fun i => ((hv _).2.1 i).mono_measure (hres _ _ hm2))
        (fun i => ((hv _).2.1 i).mono_measure (hres _ _ hm1))
        ((hv _).2.2.1.mono (hsub _ _ hm2)) ((hv _).2.2.1.mono (hsub _ _ hm1))
        ((hv _).2.2.2.mono' (hsub _ _ hm2)) ((hv _).2.2.2.mono' (hsub _ _ hm1))
      rw [hρ2] at hc
      have hcomp := scalarRms_coord_le_vectorRms (U := ball (0 : Vec d) (2 ^ j * r₀))
        (G := fun x => g (n + 1 + j + 1) x - g (n + j + 1) x) (fun k =>
          (((hv _).2.1 k).mono_measure (hres _ _ (by omega))).sub
            (((hv _).2.1 k).mono_measure (hres _ _ (by omega)))) i
      have hi := hinc (j + 1) (n + j + 1) hm1
      rw [show n + j + 1 - (j + 1) = n by omega, show n + j + 1 + 1 = n + 1 + j + 1 by omega] at hi
      calc scalarRms volume (ball 0 (2 ^ j * r₀))
            (fun x => g (n + 1 + j + 1) x i - g (n + j + 1) x i)
          ≤ vectorRms volume (ball 0 (2 ^ j * r₀))
              (fun x => g (n + 1 + j + 1) x - g (n + j + 1) x) := hcomp
        _ ≤ Cc * (((2 : ℝ) ^ (j + 1) * r₀)⁻¹ *
              scalarRms volume (ball 0 (2 ^ (j + 1) * r₀))
                (fun x => v (n + 1 + j + 1) x - v (n + j + 1) x)) := hc
        _ ≤ Cc * (((2 : ℝ) ^ (j + 1) * r₀)⁻¹ * (B (j + 1) * ε ^ n)) := by
            gcongr
        _ = _ := by ring
    obtain ⟨hae, hlim⟩ := limit_on_ball (f := fun n => fun x => g (n + j + 1) x i) (hρ j)
      (by have := hB (j + 1); positivity) hε0 hε1
      (fun n => ((hv (n + j + 1)).2.1 i).mono_measure (hres j (n + j + 1) (by omega))) hincg
    refine hlim (fun x => G x i) ?_
    filter_upwards [hae] with x ⟨l, hl⟩
    have h1 : Tendsto (fun n => g n x i) atTop (𝓝 l) := (Filter.tendsto_add_atTop_iff_nat (j + 1)).1
      (by simpa only [add_assoc] using hl)
    have h2 : Tendsto (fun n => g n x i) atTop (𝓝 (G x i)) := by
      rw [hG]; exact tendsto_nhds_limUnder ⟨l, h1⟩
    have h3 := (Filter.tendsto_add_atTop_iff_nat (j + 1)).2 h2
    simpa only [add_assoc] using h3
  have hΛ0 : (0 : ℝ) ≤ Λ := by linarith
  refine ⟨u, fun R hR => ?_, fun j => ?_⟩
  · obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (R / r₀) (one_lt_two : (1 : ℝ) < 2)
    have hRj : R ≤ 2 ^ j * r₀ := by rw [div_lt_iff₀ hr₀] at hj; linarith
    have hsubR : ball (0 : Vec d) R ⊆ ball 0 (2 ^ j * r₀) := ball_zero_subset_ball_zero hRj
    have hresR : volume.restrict (ball (0 : Vec d) R) ≤ volume.restrict (ball 0 (2 ^ j * r₀)) :=
      Measure.restrict_mono hsubR le_rfl
    have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
      isFiniteMeasure_restrict.mpr (volume_ball_ne_top' 0 R)
    have huR : MemLp u 2 (volume.restrict (ball (0 : Vec d) R)) := (hval j).1.mono_measure hresR
    have hGR : ∀ k, MemLp (fun x => G x k) 2 (volume.restrict (ball (0 : Vec d) R)) := fun k =>
      (hgrad j k).1.mono_measure hresR
    have hsubn : ∀ n, ball (0 : Vec d) R ⊆ ball 0 (2 ^ (n + j + 1) * r₀) := fun n =>
      hsubR.trans (hsub _ _ (by omega))
    have hvR : ∀ n, MemLp (v (n + j + 1)) 2 (volume.restrict (ball (0 : Vec d) R)) := fun n =>
      (hv _).1.mono_measure (Measure.restrict_mono (hsubn n) le_rfl)
    have hgR : ∀ n k, MemLp (fun x => g (n + j + 1) x k) 2 (volume.restrict (ball (0 : Vec d) R)) :=
      fun n k => ((hv _).2.1 k).mono_measure (Measure.restrict_mono (hsubn n) le_rfl)
    have hvlim : Tendsto (fun n => eLpNorm (fun x => v (n + j + 1) x - u x) 2
        (volume.restrict (ball (0 : Vec d) R))) atTop (𝓝 0) := by
      have h := (Filter.tendsto_add_atTop_iff_nat 1).2 (hval j).2
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
        fun n => ?_
      rw [show n + 1 + j = n + j + 1 by omega]
      exact eLpNorm_mono_measure _ hresR
    have hglim : ∀ k, Tendsto (fun n => eLpNorm (fun x => g (n + j + 1) x k - G x k) 2
        (volume.restrict (ball (0 : Vec d) R))) atTop (𝓝 0) := fun k =>
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hgrad j k).2
        (fun _ => zero_le) fun n => eLpNorm_mono_measure _ hresR
    -- test functions are bounded
    have hbdd : ∀ ψ : Vec d → ℝ, Continuous ψ → HasCompactSupport ψ →
        MemLp ψ 2 (volume.restrict (ball (0 : Vec d) R)) := fun ψ hψ hψc => by
      obtain ⟨M, hM⟩ := hψ.bounded_above_of_compact_support hψc
      exact MemLp.of_bound hψ.aestronglyMeasurable M (Eventually.of_forall hM)
    refine ⟨huR, G, hGR, fun i => ⟨IntegrableOn.locallyIntegrableOn (huR.integrable one_le_two),
      IntegrableOn.locallyIntegrableOn ((hGR i).integrable one_le_two), fun φ hφ => ?_⟩, ?_⟩
    · have hdφ : MemLp (coordinateDerivative i φ) 2 (volume.restrict (ball (0 : Vec d) R)) :=
        hbdd _ (continuous_coordinateDerivative (hφ.1.of_le (by exact_mod_cast le_top)) i)
          (hasCompactSupport_coordinateDerivative hφ.2.1 i)
      have hφ2 : MemLp φ 2 (volume.restrict (ball (0 : Vec d) R)) :=
        hbdd _ hφ.1.continuous hφ.2.1
      have hL := tendsto_integral_mul_of_eLpNorm_sub hdφ huR hvR hvlim
      have hRt := (tendsto_integral_mul_of_eLpNorm_sub hφ2 (hGR i) (hgR · i) (hglim i)).neg
      have heq : ∀ n, ∫ x in ball 0 R, coordinateDerivative i φ x * v (n + j + 1) x =
          -∫ x in ball 0 R, φ x * g (n + j + 1) x i := fun n => by
        have h := (((hv (n + j + 1)).2.2.1.mono (hsubn n)) i).2.2 φ hφ
        simp only [mul_comm (coordinateDerivative i φ _), mul_comm (φ _)]
        exact h
      have h := tendsto_nhds_unique hL (hRt.congr fun n => (heq n).symm)
      simp only [mul_comm (coordinateDerivative i φ _), mul_comm (φ _)] at h
      exact h
    · refine ⟨fun i => IntegrableOn.locallyIntegrableOn
        ((memLp_coefficient_mulVec_apply_of_coord hΛ0 a hGR i).integrable one_le_two),
        locallyIntegrableOn_zero, fun φ hφ => ?_⟩
      simp only [zero_mul, integral_zero, neg_zero]
      -- the coefficients of the pairing
      have hdφc : ∀ i, Continuous (coordinateDerivative i φ) := fun i =>
        continuous_coordinateDerivative (hφ.1.of_le (by exact_mod_cast le_top)) i
      choose M hM using fun i => (hdφc i).bounded_above_of_compact_support
        (hasCompactSupport_coordinateDerivative hφ.2.1 i)
      have hψm : ∀ k, AEStronglyMeasurable (fun x => ∑ i, a x i k * coordinateDerivative i φ x)
          (volume.restrict (ball (0 : Vec d) R)) := fun k =>
        Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
          ((a.locally_integrable i k).aestronglyMeasurable.restrict).mul
            (hdφc i).aestronglyMeasurable
      have hψb : ∀ k x, ‖∑ i, a x i k * coordinateDerivative i φ x‖ ≤ ∑ i, Λ * M i := fun k x => by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul (abs_coefficient_entry_le a x i k) (hM i x) (norm_nonneg _) hΛ0
      have hψ2 : ∀ k, MemLp (fun x => ∑ i, a x i k * coordinateDerivative i φ x) 2
          (volume.restrict (ball (0 : Vec d) R)) := fun k =>
        MemLp.of_bound (hψm k) _ (Eventually.of_forall (hψb k))
      have hint : ∀ (h : Vec d → Vec d), (∀ k, MemLp (fun x => h x k) 2
          (volume.restrict (ball (0 : Vec d) R))) → ∀ k,
          Integrable (fun x => h x k * ∑ i, a x i k * coordinateDerivative i φ x)
            (volume.restrict (ball (0 : Vec d) R)) := fun h hh k =>
        Integrable.mono' (((hh k).integrable one_le_two).norm.mul_const (∑ i, Λ * M i))
          ((hh k).aestronglyMeasurable.mul (hψm k)) (Eventually.of_forall fun x => by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hψb k x) (norm_nonneg _))
      have hsplit : ∀ (h : Vec d → Vec d), (∀ k, MemLp (fun x => h x k) 2
          (volume.restrict (ball (0 : Vec d) R))) →
          ∫ x in ball 0 R, dot ((a x).mulVec (h x)) (gradient φ x) =
            ∑ k, ∫ x in ball 0 R, h x k * ∑ i, a x i k * coordinateDerivative i φ x := by
        intro h hh
        simp_rw [dot_mulVec_gradient_eq a h φ]
        exact integral_finsetSum _ fun k _ => hint h hh k
      have hzero : ∀ n, ∑ k, ∫ x in ball 0 R, g (n + j + 1) x k *
          ∑ i, a x i k * coordinateDerivative i φ x = 0 := fun n => by
        rw [← hsplit _ (hgR n)]
        have h := ((hv (n + j + 1)).2.2.2.mono' (hsubn n)).2.2 φ hφ
        simpa only [zero_mul, integral_zero, neg_zero] using h
      have hlimk : ∀ k, Tendsto (fun n => ∫ x in ball 0 R, g (n + j + 1) x k *
          ∑ i, a x i k * coordinateDerivative i φ x) atTop
          (𝓝 (∫ x in ball 0 R, G x k * ∑ i, a x i k * coordinateDerivative i φ x)) := fun k => by
        have h := tendsto_integral_mul_of_eLpNorm_sub (hψ2 k) (hGR k) (hgR · k) (hglim k)
        simp only [mul_comm (∑ i, a _ i k * coordinateDerivative i φ _)] at h
        exact h
      have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun k _ => hlimk k
      have h0 := tendsto_nhds_unique hsum (tendsto_const_nhds.congr fun n => (hzero n).symm)
      rw [hsplit G hGR]
      exact h0
  · have hV : 0 < volume.real (ball (0 : Vec d) (2 ^ j * r₀)) := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos (volume_ball_ne_zero' 0 (hρ j)) (volume_ball_ne_top' 0 _)
    have hsV : 0 < Real.sqrt (volume.real (ball (0 : Vec d) (2 ^ j * r₀))) := Real.sqrt_pos.2 hV
    have hconv : ∀ n, scalarRms volume (ball 0 (2 ^ j * r₀)) (fun x => v (n + j) x - u x) =
        (eLpNorm (v (n + j) - u) 2 (volume.restrict (ball (0 : Vec d) (2 ^ j * r₀)))).toReal /
          Real.sqrt (volume.real (ball (0 : Vec d) (2 ^ j * r₀))) := fun n => by
      rw [show v (n + j) - u = fun x => v (n + j) x - u x from rfl,
        eLpNorm_eq_ofReal_sqrt_mul_scalarRms (f := fun x => v (n + j) x - u x) hV
          (((hv (n + j)).1.mono_measure (hres j (n + j) (by omega))).sub (hval j).1),
        ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _) (scalarRms_nonneg _ _))]
      field_simp
    have h := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hval j).2).div_const
      (Real.sqrt (volume.real (ball (0 : Vec d) (2 ^ j * r₀))))
    rw [ENNReal.toReal_zero, zero_div] at h
    refine (Filter.tendsto_add_atTop_iff_nat j).1 ?_
    exact h.congr fun n => (hconv n).symm

end QSH
