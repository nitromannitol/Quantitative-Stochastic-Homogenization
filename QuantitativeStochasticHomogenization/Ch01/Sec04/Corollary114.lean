import QuantitativeStochasticHomogenization.Ch01.Sec04.Lemma113

/-!
# Corollary 1.14: the multiscale Poincaré inequality for the oscillation

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.4, Corollary 1.14, (1.46): there is `C(d) < ∞` such that, for every `m ∈ ℕ` and
`u ∈ H¹(□_m)`,
`‖u - (u)_{□_m}‖_{L̲²(□_m)} ≤ C ‖∇u‖_{L̲²(□_m)} +
C Σ_{n=0}^m 3^n (|Z_n|⁻¹ Σ_{y ∈ Z_n} |(∇u)_{y+□_n}|²)^{1/2}`,
from Lemma 1.13 and Proposition 1.12 for each component of `∇u`, as in the book.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

open BaseExponent

theorem scalarRms_apply_le_vectorRms {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : MemLp g 2 (volume.restrict U)) (i : Fin d) :
    scalarRms volume U (fun x => g x i) ≤ vectorRms volume U g := by
  rw [scalarRms, vectorRms]
  exact Real.sqrt_le_sqrt (setAverage_mono_of_integrableOn (hg.eval i).integrable_sq
    (integrable_euclideanSq_of_memLp hg) fun x => sq_apply_le_euclideanSq (g x) i)

/-- **Corollary 1.14**, (1.46). -/
theorem corollary_1_14 [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (u : Vec d → ℝ) (g : Vec d → Vec d), H1 (triadicCube d m) u g →
      scalarRms volume (triadicCube d m) (fun x => u x - ⨍ y in triadicCube d m, u y) ≤
        C * vectorRms volume (triadicCube d m) g +
          C * ∑ n ∈ Finset.range (m + 1), (3 : ℝ) ^ n *
            √(1 / ((3 : ℝ) ^ (m - n)) ^ d * ∑ k : Fin d → Fin (3 ^ (m - n)),
              euclideanSq (vectorAverage (partitionCube n (m - n) k) g)) := by
  obtain ⟨C₁₂, hC₁₂, h12⟩ := proposition_1_12 (d := d)
  obtain ⟨C₁₃, hC₁₃, h13⟩ := lemma_1_13_first (d := d)
  refine ⟨C₁₃ * (d * C₁₂), by positivity, fun m u g hu => ?_⟩
  set T := ∑ n ∈ Finset.range (m + 1), (3 : ℝ) ^ n *
    √(1 / ((3 : ℝ) ^ (m - n)) ^ d * ∑ k : Fin d → Fin (3 ^ (m - n)),
      euclideanSq (vectorAverage (partitionCube n (m - n) k) g)) with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hR0 : 0 ≤ vectorRms volume (triadicCube d m) g := Real.sqrt_nonneg _
  have hcomp : ∀ i, hatNegativeSobolevNorm (triadicCube d m) (fun x => g x i) ≤
      ENNReal.ofReal (C₁₂ * vectorRms volume (triadicCube d m) g + C₁₂ * T) := by
    intro i
    refine (h12 m (fun x => g x i) (hu.2.1.eval i)).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 := scalarRms_apply_le_vectorRms hu.2.1 i
    have h2 : ∑ n ∈ Finset.range m, (3 : ℝ) ^ n *
        √(1 / ((3 : ℝ) ^ (m - n)) ^ d * ∑ k : Fin d → Fin (3 ^ (m - n)),
          (⨍ x in partitionCube n (m - n) k, g x i) ^ 2) ≤ T := by
      rw [hT, Finset.sum_range_succ]
      have hlast : 0 ≤ (3 : ℝ) ^ m * √(1 / ((3 : ℝ) ^ (m - m)) ^ d *
          ∑ k : Fin d → Fin (3 ^ (m - m)),
            euclideanSq (vectorAverage (partitionCube m (m - m) k) g)) :=
        mul_nonneg (by positivity) (Real.sqrt_nonneg _)
      refine le_add_of_le_of_nonneg (Finset.sum_le_sum fun n _ => ?_) hlast
      refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) (by positivity)
      exact sq_apply_le_euclideanSq (vectorAverage (partitionCube n (m - n) k) g) i
    have := mul_le_mul_of_nonneg_left h1 hC₁₂
    have := mul_le_mul_of_nonneg_left h2 hC₁₂
    linarith
  have hb0 : 0 ≤ C₁₂ * vectorRms volume (triadicCube d m) g + C₁₂ * T :=
    add_nonneg (mul_nonneg hC₁₂ hR0) (mul_nonneg hC₁₂ hT0)
  have hvec : vectorHatNegativeSobolevNorm (triadicCube d m) g ≤
      ENNReal.ofReal (d * (C₁₂ * vectorRms volume (triadicCube d m) g + C₁₂ * T)) := by
    unfold vectorHatNegativeSobolevNorm
    calc ∑ j, hatNegativeSobolevNorm (triadicCube d m) (fun x => g x j)
        ≤ ∑ _j : Fin d, ENNReal.ofReal (C₁₂ * vectorRms volume (triadicCube d m) g + C₁₂ * T) :=
          Finset.sum_le_sum fun j _ => hcomp j
      _ = ENNReal.ofReal (d * (C₁₂ * vectorRms volume (triadicCube d m) g + C₁₂ * T)) := by
          rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
            (f := fun _ : Fin d => C₁₂ * vectorRms volume (triadicCube d m) g + C₁₂ * T)
            (fun j _ => hb0)]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h := (h13 m u g hu).trans (mul_le_mul' le_rfl hvec)
  rw [← ENNReal.ofReal_mul hC₁₃, ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hC₁₃ (mul_nonneg (Nat.cast_nonneg d) hb0))] at h
  calc scalarRms volume (triadicCube d m) (fun x => u x - ⨍ y in triadicCube d m, u y)
      ≤ C₁₃ * (d * (C₁₂ * vectorRms volume (triadicCube d m) g + C₁₂ * T)) := h
    _ = C₁₃ * (d * C₁₂) * vectorRms volume (triadicCube d m) g + C₁₃ * (d * C₁₂) * T := by ring

end QSH
