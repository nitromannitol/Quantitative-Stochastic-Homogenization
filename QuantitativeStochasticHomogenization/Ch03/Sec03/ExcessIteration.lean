import QuantitativeStochasticHomogenization.Ch03.Sec03.QuadraticHalving
import QuantitativeStochasticHomogenization.Ch03.Sec03.FiniteSpanApproximation
import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatFormulaLocal

/-!
# The excess iteration of the first-order Liouville theorem

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 3.3, the first-order proof of Theorem 3.8 for `k = 1`, abstract form. Let `E_R` be an
increasing family of sets covering the space, each inside the ball `B_{LR}` with comparable
volume, and let `E(R)` be the normalized `L²(E_R)` distance of `u` to the combinations of a finite
family `f`. If one step of the excess decay `E(R/2) ≤ ¼ (1 + C R^{-ν}) E(R)` holds at all large
scales and `u` grows subquadratically on balls, then `E` vanishes at all large scales by the sharp
quadratic halving, `u` is a combination of `f` on every `E_R`, and hence one combination of `f`
everywhere.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The normalized `L²(U)` distance of `u` to the combinations of `f`. -/
def spanExcess {ι : Type*} [Fintype ι] (U : Set (Vec d)) (f : ι → Vec d → ℝ)
    (u : Vec d → ℝ) : ℝ :=
  sInf (Set.range fun c : ι → ℝ => scalarRms volume U (fun x => u x - ∑ i, c i * f i x))

theorem spanExcess_nonneg {ι : Type*} [Fintype ι] (U : Set (Vec d)) (f : ι → Vec d → ℝ)
    (u : Vec d → ℝ) : 0 ≤ spanExcess U f u :=
  Real.sInf_nonneg (by rintro _ ⟨c, rfl⟩; exact Real.sqrt_nonneg _)

theorem spanExcess_le {ι : Type*} [Fintype ι] (U : Set (Vec d)) (f : ι → Vec d → ℝ)
    (u : Vec d → ℝ) (c : ι → ℝ) :
    spanExcess U f u ≤ scalarRms volume U (fun x => u x - ∑ i, c i * f i x) :=
  csInf_le ⟨0, by rintro _ ⟨c, rfl⟩; exact Real.sqrt_nonneg _⟩ ⟨c, rfl⟩

/-- One step of the excess decay passes to the distance to the span. -/
theorem spanExcess_le_mul {ι : Type*} [Fintype ι] {U V : Set (Vec d)} {f : ι → Vec d → ℝ}
    {u : Vec d → ℝ} {k : ℝ} (hk : 0 < k)
    (h : ∀ c : ι → ℝ, ∃ c' : ι → ℝ,
      scalarRms volume V (fun x => u x - ∑ i, (c + c') i * f i x) ≤
        k * scalarRms volume U (fun x => u x - ∑ i, c i * f i x)) :
    spanExcess V f u ≤ k * spanExcess U f u := by
  have h1 : spanExcess V f u / k ≤ spanExcess U f u := by
    refine le_csInf (Set.range_nonempty _) ?_
    rintro _ ⟨c, rfl⟩
    obtain ⟨c', hc'⟩ := h c
    rw [div_le_iff₀' hk]
    exact (spanExcess_le V f u (c + c')).trans hc'
  rwa [div_le_iff₀' hk] at h1

/-- Comparison of normalized `L²` norms on nested sets of comparable volume. -/
theorem scalarRms_le_sqrt_mul_of_subset {U V : Set (Vec d)} {g : Vec d → ℝ} {κ : ℝ}
    (hUV : U ⊆ V) (hU0 : volume U ≠ 0) (hVt : volume V ≠ ⊤)
    (hκ : volume.real V ≤ κ * volume.real U) (hκ0 : 0 ≤ κ)
    (hg : IntegrableOn (fun x => g x ^ 2) V) :
    scalarRms volume U g ≤ Real.sqrt κ * scalarRms volume V g := by
  unfold scalarRms
  rw [← Real.sqrt_mul hκ0]
  apply Real.sqrt_le_sqrt
  rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul]
  have hUt : volume U ≠ ⊤ := ne_top_of_le_ne_top hVt (measure_mono hUV)
  have hUr : 0 < volume.real U := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hU0 hUt
  have hVr : 0 < volume.real V := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (fun h => hU0 (measure_mono_null hUV h)) hVt
  have hint : ∫ x in U, g x ^ 2 ≤ ∫ x in V, g x ^ 2 :=
    setIntegral_mono_set hg (ae_of_all _ fun x => sq_nonneg _) (ae_of_all _ hUV)
  have hnn : 0 ≤ ∫ x in V, g x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have key : (volume.real U)⁻¹ ≤ κ * (volume.real V)⁻¹ := by
    have h1 : (volume.real U)⁻¹ * volume.real V ≤ κ := by
      rw [inv_mul_le_iff₀ hUr]
      linarith
    calc (volume.real U)⁻¹ = (volume.real U)⁻¹ * volume.real V * (volume.real V)⁻¹ := by
          field_simp
      _ ≤ κ * (volume.real V)⁻¹ := mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hVr.le)
  calc (volume.real U)⁻¹ * ∫ x in U, g x ^ 2
      ≤ (volume.real U)⁻¹ * ∫ x in V, g x ^ 2 :=
        mul_le_mul_of_nonneg_left hint (inv_nonneg.2 hUr.le)
    _ ≤ κ * (volume.real V)⁻¹ * ∫ x in V, g x ^ 2 := mul_le_mul_of_nonneg_right key hnn
    _ = κ * ((volume.real V)⁻¹ * ∫ x in V, g x ^ 2) := by ring

/-- **The excess iteration** (abstract form). -/
theorem ae_eq_sum_of_quarter_step {ι : Type*} [Fintype ι] {E : ℝ → Set (Vec d)}
    {f : ι → Vec d → ℝ} {u : Vec d → ℝ} {C ν R₁ L κ : ℝ}
    (hC : 0 ≤ C) (hν : 0 < ν) (hR₁ : 0 < R₁) (hL : 0 < L) (hκ : 0 ≤ κ)
    (hmono : Monotone E) (hcover : ∀ x, ∃ R, x ∈ E R)
    (hE0 : ∀ R, 0 < R → volume (E R) ≠ 0)
    (hball : ∀ R, 0 < R → E R ⊆ ball 0 (L * R))
    (hvol : ∀ R, 0 < R → volume.real (ball (0 : Vec d) (L * R)) ≤ κ * volume.real (E R))
    (hu : ∀ R, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)))
    (hf : ∀ R, 0 < R → ∀ i, MemLp (f i) 2 (volume.restrict (ball 0 R)))
    (hgrowth : Tendsto (fun R : ℝ => R ^ (-2 : ℤ) * Real.sqrt (⨍ x in ball 0 R, |u x| ^ 2))
      atTop (𝓝 0))
    (hstep : ∀ R, R₁ ≤ R → ∀ c : ι → ℝ, ∃ c' : ι → ℝ,
      scalarRms volume (E (R / 2)) (fun x => u x - ∑ i, (c + c') i * f i x) ≤
        1 / 4 * (1 + C * R ^ (-ν)) *
          scalarRms volume (E R) (fun x => u x - ∑ i, c i * f i x)) :
    ∃ c : ι → ℝ, ∀ᵐ x ∂(volume : Measure (Vec d)), u x = ∑ i, c i * f i x := by
  classical
  set Ex : ℝ → ℝ := fun R => spanExcess (E R) f u with hEx
  have hEx0 : ∀ R, 0 ≤ Ex R := fun R => spanExcess_nonneg _ _ _
  have hstepEx : ∀ R, R₁ ≤ R → Ex (R / 2) ≤ 1 / 4 * (1 + C * R ^ (-ν)) * Ex R := by
    intro R hR
    have hR0 : 0 < R := lt_of_lt_of_le hR₁ hR
    have hCR : 0 ≤ C * R ^ (-ν) := mul_nonneg hC (Real.rpow_nonneg hR0.le _)
    have hk : 0 < 1 / 4 * (1 + C * R ^ (-ν)) := by linarith
    exact spanExcess_le_mul hk (hstep R hR)
  have hgrowthEx : Tendsto (fun R => Ex R / R ^ 2) atTop (𝓝 0) := by
    have hcomp : Tendsto (fun R : ℝ => (L * R) ^ (-2 : ℤ) *
        Real.sqrt (⨍ x in ball 0 (L * R), |u x| ^ 2)) atTop (𝓝 0) :=
      hgrowth.comp (tendsto_id.const_mul_atTop hL)
    have hlim := hcomp.const_mul (Real.sqrt κ * L ^ 2)
    rw [mul_zero] at hlim
    refine squeeze_zero' (Eventually.of_forall fun R => div_nonneg (hEx0 R) (sq_nonneg R)) ?_
      hlim
    filter_upwards [eventually_gt_atTop 0] with R hR
    have hLR : 0 < L * R := mul_pos hL hR
    have h1 : Ex R ≤ scalarRms volume (E R) u := by
      have h := spanExcess_le (E R) f u 0
      simpa using h
    have h2 : scalarRms volume (E R) u ≤ Real.sqrt κ * scalarRms volume (ball 0 (L * R)) u :=
      scalarRms_le_sqrt_mul_of_subset (hball R hR) (hE0 R hR) (volume_ball_zero_lt_top _).ne
        (hvol R hR) hκ (hu _ hLR).integrable_sq
    have hrms : scalarRms volume (ball 0 (L * R)) u =
        Real.sqrt (⨍ x in ball 0 (L * R), |u x| ^ 2) := by
      unfold scalarRms
      simp only [sq_abs]
    rw [hrms] at h2
    have hR2 : 0 < R ^ 2 := by positivity
    have hL0 : L ≠ 0 := hL.ne'
    have hR0 : R ≠ 0 := hR.ne'
    calc Ex R / R ^ 2
        ≤ Real.sqrt κ * Real.sqrt (⨍ x in ball 0 (L * R), |u x| ^ 2) / R ^ 2 := by
          gcongr
          exact h1.trans h2
      _ = Real.sqrt κ * L ^ 2 * ((L * R) ^ (-2 : ℤ) *
            Real.sqrt (⨍ x in ball 0 (L * R), |u x| ^ 2)) := by
          rw [zpow_neg, zpow_two]
          field_simp
  have hzero := eq_zero_of_quarter_step hC hν hR₁ hEx0 hstepEx hgrowthEx
  have hloc : ∀ n : ℕ, ∃ c : ι → ℝ,
      ∀ᵐ x ∂(volume.restrict (E (R₁ + n))), u x = ∑ i, c i * f i x := by
    intro n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have ht : 0 < R₁ + n := by linarith
    have hEn : Ex (R₁ + n) = 0 := hzero _ (by linarith)
    have hsub := hball _ ht
    refine exists_ae_eq_sum_of_forall_scalarRms_lt (hE0 _ ht)
      (ne_top_of_le_ne_top (volume_ball_zero_lt_top _).ne (measure_mono hsub))
      ((hu _ (mul_pos hL ht)).mono_measure (Measure.restrict_mono hsub le_rfl))
      (fun i => (hf _ (mul_pos hL ht) i).mono_measure (Measure.restrict_mono hsub le_rfl)) ?_
    intro ε hε
    have hlt : sInf (Set.range fun c : ι → ℝ =>
        scalarRms volume (E (R₁ + n)) (fun x => u x - ∑ i, c i * f i x)) < ε := by
      have h := hEn
      simp only [hEx, spanExcess] at h
      rw [h]
      exact hε
    obtain ⟨_, ⟨c, rfl⟩, hc⟩ := exists_lt_of_csInf_lt (Set.range_nonempty _) hlt
    exact ⟨c, hc⟩
  have hmonoN : Monotone fun n : ℕ => E (R₁ + n) := by
    intro n m hnm
    have h : (n : ℝ) ≤ m := Nat.cast_le.2 hnm
    exact hmono (by linarith)
  have hcov : ⋃ n : ℕ, E (R₁ + n) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨R, hR⟩ := hcover x
    obtain ⟨n, hn⟩ := exists_nat_ge R
    exact Set.mem_iUnion.2 ⟨n, hmono (by linarith) hR⟩
  exact exists_ae_eq_sum_of_forall_restrict hmonoN hcov hloc

end QSH
