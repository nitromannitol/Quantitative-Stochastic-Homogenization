import QuantitativeStochasticHomogenization.Ch04.Sec04.CorrectedGramLowerBound

/-!
# The two directed distances of (4.91) from matched columns

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 4.21, (4.91), last step. Suppose that the rescaled gradients of `A₁` on `B_T(z)` are exactly
the combinations `∑ c_i G_i` of `d` tuples `G_i` (the rescaled corrected gradients matched with the
localized coordinates), that these combinations satisfy the lower bound
`μ ∑ |c_i| ≤ ‖∑ c_i G_i‖`, and that the rescaled gradient `Y_i` of the `i`-th localized coordinate
is within `ρ ≤ μ/2` of `G_i`. Then both directed distances between the rescaled gradients of `A₁`
and the span of the localized coordinates, restricted to elements of norm at most `L`, are at
most `2 L ρ / μ`. These are the approximation hypotheses of Lemma 4.22.
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

/-- **The directed distances from matched columns**, in a normed space. -/
theorem directedDistances_of_matched {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (A : Set E) (Y G : ι → E) {μ ρ L : ℝ} (hμ : 0 < μ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ μ / 2) (hspan : ∀ x ∈ A, ∃ c : ι → ℝ, x = ∑ i, c i • G i)
    (hmem : ∀ c : ι → ℝ, ∑ i, c i • G i ∈ A) (hclose : ∀ i, ‖Y i - G i‖ ≤ ρ)
    (hlow : ∀ c : ι → ℝ, μ * ∑ i, |c i| ≤ ‖∑ i, c i • G i‖) :
    (∀ x ∈ A, ‖x‖ ≤ L → ∃ c : ι → ℝ, ‖x - ∑ i, c i • Y i‖ ≤ 2 * L * ρ / μ) ∧
      (∀ c : ι → ℝ, ‖∑ i, c i • Y i‖ ≤ L →
        ∃ x ∈ A, ‖∑ i, c i • Y i - x‖ ≤ 2 * L * ρ / μ) := by
  have herr : ∀ c : ι → ℝ, ‖∑ i, c i • G i - ∑ i, c i • Y i‖ ≤ ρ * ∑ i, |c i| := by
    intro c
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (by rw [norm_sub_rev]; exact hclose i) (abs_nonneg _)
  have hs0 : ∀ c : ι → ℝ, 0 ≤ ∑ i, |c i| := fun c => Finset.sum_nonneg fun i _ => abs_nonneg _
  constructor
  · intro x hx hxL
    obtain ⟨c, rfl⟩ := hspan x hx
    refine ⟨c, (herr c).trans ?_⟩
    have h1 := (hlow c).trans hxL
    have hL : 0 ≤ L := le_trans (mul_nonneg hμ.le (hs0 c)) h1
    rw [le_div_iff₀ hμ]
    nlinarith [mul_le_mul_of_nonneg_left h1 hρ0]
  · intro c hcL
    refine ⟨∑ i, c i • G i, hmem c, ?_⟩
    rw [norm_sub_rev]
    refine (herr c).trans ?_
    have h1 : μ * ∑ i, |c i| ≤ L + ρ * ∑ i, |c i| := by
      have := norm_sub_norm_le (∑ i, c i • G i) (∑ i, c i • Y i)
      linarith [hlow c, herr c]
    have h2 : ρ * ∑ i, |c i| ≤ μ / 2 * ∑ i, |c i| := mul_le_mul_of_nonneg_right hρ (hs0 c)
    have h3 : μ * ∑ i, |c i| ≤ 2 * L := by linarith
    rw [le_div_iff₀ hμ]
    nlinarith [mul_le_mul_of_nonneg_left h3 hρ0]

variable {d : ℕ} {z : Vec d} {T r : ℝ}

theorem scaleLp_add (hr : r ≠ 0) (u v : Lp ℝ 2 (ballMeasure z T)) :
    scaleLp hr (u + v) = scaleLp hr u + scaleLp hr v := by
  refine Lp.ext ?_
  filter_upwards [scaleLp_ae hr (u + v), scaleLp_ae hr u, scaleLp_ae hr v, Lp.coeFn_add u v,
    Lp.coeFn_add (scaleLp hr u) (scaleLp hr v)] with x h1 h2 h3 h4 h5
  rw [h1, h4, h5]
  simp only [Pi.add_apply]
  rw [h2, h3, mul_add]

theorem scaleLp_smul (hr : r ≠ 0) (c : ℝ) (u : Lp ℝ 2 (ballMeasure z T)) :
    scaleLp hr (c • u) = c • scaleLp hr u := by
  refine Lp.ext ?_
  filter_upwards [scaleLp_ae hr (c • u), scaleLp_ae hr u, Lp.coeFn_smul c u,
    Lp.coeFn_smul c (scaleLp hr u)] with x h1 h2 h3 h4
  rw [h1, h3, h4]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h2]
  ring

theorem scaleLp_sum (hr : r ≠ 0) {ι : Type*} (s : Finset ι)
    (f : ι → Lp ℝ 2 (ballMeasure z T)) :
    scaleLp hr (∑ i ∈ s, f i) = ∑ i ∈ s, scaleLp hr (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [scaleLp_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, scaleLp_add, ih]

/-- The rescaled gradient of a combination of pairs is the combination of their rescaled
gradients. -/
theorem scaleLp_pairCombination (hr : r ≠ 0) (F : Fin d → PairSpace d z T) (c : Vec d) :
    (fun k => scaleLp hr (pairCombination F c k)) =
      ∑ i, c i • fun k => scaleLp hr ((F i).2 k) := by
  funext k
  simp only [pairCombination, scaleLp_sum, scaleLp_smul, Finset.sum_apply, Pi.smul_apply]

/-- **The approximation hypotheses of Lemma 4.22 from matched columns**: if the rescaled gradients
of `A₁` on `B_T(z)` are exactly the combinations of tuples `G_i` satisfying
`μ ∑ |c_i| ≤ ‖∑ c_i G_i‖`, and the rescaled gradient of the `i`-th localized coordinate is within
`ρ ≤ μ/2` of `G_i`, then both directed distances at norm `L` are at most `2 L ρ / μ`. -/
theorem localizationDistances_of_matched {Λ : ℝ} {a : CoefficientField d Λ} (hr : r ≠ 0)
    {S σ θ C : ℝ} (B : LocalizedBasis a z T S σ θ C)
    (G : Fin d → Fin d → Lp ℝ 2 (ballMeasure z T)) {μ ρ L : ℝ} (hμ : 0 < μ) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ μ / 2)
    (hspan : ∀ w : HarmonicA1 a, ∃ c : Vec d,
      (fun k => scaleLp hr (w.ballGrad z T k)) = ∑ i, c i • G i)
    (hmem : ∀ c : Vec d, ∃ w : HarmonicA1 a,
      (fun k => scaleLp hr (w.ballGrad z T k)) = ∑ i, c i • G i)
    (hclose : ∀ i, ‖(fun k => scaleLp hr ((B.coordinate i).toPair.2 k)) - G i‖ ≤ ρ)
    (hlow : ∀ c : Vec d, μ * ∑ i, |c i| ≤ ‖∑ i, c i • G i‖) :
    (∀ w : HarmonicA1 a, ‖(fun k => scaleLp hr (w.ballGrad z T k))‖ ≤ L →
      ∃ c : Vec d, ‖(fun k => scaleLp hr (w.ballGrad z T k)) -
        (fun k => scaleLp hr (pairCombination (fun i => (B.coordinate i).toPair) c k))‖ ≤
          2 * L * ρ / μ) ∧
    (∀ c : Vec d,
      ‖(fun k => scaleLp hr (pairCombination (fun i => (B.coordinate i).toPair) c k))‖ ≤ L →
      ∃ w : HarmonicA1 a,
        ‖(fun k => scaleLp hr (pairCombination (fun i => (B.coordinate i).toPair) c k)) -
          (fun k => scaleLp hr (w.ballGrad z T k))‖ ≤ 2 * L * ρ / μ) := by
  set A : Set (Fin d → Lp ℝ 2 (ballMeasure z T)) :=
    Set.range fun w : HarmonicA1 a => fun k => scaleLp hr (w.ballGrad z T k) with hA
  have h := directedDistances_of_matched (L := L) A
    (fun i k => scaleLp hr ((B.coordinate i).toPair.2 k)) G hμ hρ0 hρ
    (by rintro _ ⟨w, rfl⟩; exact hspan w)
    (fun c => by obtain ⟨w, hw⟩ := hmem c; exact ⟨w, hw⟩) hclose hlow
  have hcomb := scaleLp_pairCombination hr (fun i => (B.coordinate i).toPair)
  refine ⟨fun w hw => ?_, fun c hc => ?_⟩
  · obtain ⟨c, hc⟩ := h.1 _ ⟨w, rfl⟩ hw
    exact ⟨c, by rw [hcomb]; exact hc⟩
  · rw [hcomb] at hc
    obtain ⟨x, ⟨w, rfl⟩, hx⟩ := h.2 c hc
    exact ⟨w, by rw [hcomb]; exact hx⟩

end QSH
