import QuantitativeStochasticHomogenization.Ch03.Sec03.Implication348
import QuantitativeStochasticHomogenization.Ch03.Sec03.WeakGradientH10

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

end QSH
