import QuantitativeStochasticHomogenization.Ch04.Sec06.NegativeSobolevCorrector

/-!
# Section 4.6: summation of the heat scales

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
(4.126). If the `L²(B_1)` norms of the averages `Y_{β,s}` of a random field have measurable
majorants `O_1(c s^{-|β|/2 - d/4} ε^{d/2})` at every scale `s ∈ (0, 1]` (`HeatScaleEstimate`), then
for `n + 1 > d/2` the heat bracket of order `n + 1` has a measurable majorant
`O_1(C(d, n, c) ε^{d/2})` (`HeatScaleEstimate.osBound_heatBracket`): the scales are summed by the averaging
property of `O_1` against `s^n ds` on `(0, 1]`, which is integrable against `s^{-(n+1)/2 - d/4}`
exactly when `n + 1 > d/2`. With `negativeSobolevCorrector_of_heatBracket` this gives (4.126) from
the per-scale estimates (`negativeSobolevCorrector_of_heatScale`).
-/

open MeasureTheory Filter Set
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

theorem osBound_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {s θ : ℝ} (hs : 0 < s) (hθ : 0 < θ) : OsBound P (fun _ => 0) s θ := by
  refine ⟨measurable_const, hs, hθ, ?_⟩
  simp only [max_self, mul_zero, Real.zero_rpow hs.ne', Real.exp_zero, ENNReal.ofReal_one,
    lintegral_const, measure_univ, mul_one]
  norm_num

/-- **The per-scale estimate** of order `n + 1` for a random field `F`: measurable majorants
`Q k w s` of `‖Y_{β_w,s}(F)‖_{L²(B_1)}` for the words `w` of length `k ≤ n + 1`, which are
`O_1(c s^{-k/2 - d/4} ε^{d/2})` at every scale `s ∈ (0, 1]`, the majorization holding almost surely
at each scale. The norms are jointly measurable in the scale and the sample. -/
def HeatScaleEstimate {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ)
    (F : Ω → Vec d → ℝ) (c ε : ℝ) : Prop :=
  ∃ Q : ∀ k : ℕ, (Fin k → Fin d) → ℝ → Ω → ℝ,
    (∀ k w, Measurable (Function.uncurry (Q k w))) ∧ (∀ k w s a, 0 ≤ Q k w s a) ∧
    (∀ k (w : Fin k → Fin d), Measurable (fun p : ℝ × Ω =>
      eLpNorm (heatDerivativeAverage (countIndex w) p.1 (F p.2)) 2
        (volume.restrict (originBall d 1)))) ∧
    (∀ k (w : Fin k → Fin d), k ≤ n + 1 → ∀ s ∈ Ioc (0 : ℝ) 1,
      OsBound P (Q k w s) 1 (c * s ^ (-(k : ℝ) / 2 - (d : ℝ) / 4) * ε ^ ((d : ℝ) / 2))) ∧
    ∀ k (w : Fin k → Fin d), k ≤ n + 1 → ∀ s ∈ Ioc (0 : ℝ) 1, ∀ᵐ a ∂P,
      eLpNorm (heatDerivativeAverage (countIndex w) s (F a)) 2
        (volume.restrict (originBall d 1)) ≤ ENNReal.ofReal (Q k w s a)

/-- The constant `c (∑_{k ≤ n} d^k + d^{n+1} / ((n + 1)/2 - d/4))`. -/
def heatScaleConstant (d n : ℕ) (c : ℝ) : ℝ :=
  c * ((∑ k ∈ Finset.range (n + 1), (d : ℝ) ^ k) +
    (d : ℝ) ^ (n + 1) / (((n : ℝ) + 1) / 2 - (d : ℝ) / 4))

theorem heatScaleConstant_pos {n : ℕ} (hn : (d : ℝ) / 2 < n + 1) {c : ℝ} (hc : 0 < c) :
    0 < heatScaleConstant d n c := by
  have h1 : 0 < ((n : ℝ) + 1) / 2 - (d : ℝ) / 4 := by linarith
  have h2 : 0 < ∑ k ∈ Finset.range (n + 1), (d : ℝ) ^ k := by
    rw [Finset.sum_range_succ']
    simp only [pow_zero]
    have : 0 ≤ ∑ k ∈ Finset.range n, (d : ℝ) ^ (k + 1) :=
      Finset.sum_nonneg fun k _ => pow_nonneg (Nat.cast_nonneg d) _
    linarith
  unfold heatScaleConstant
  have h3 : 0 ≤ (d : ℝ) ^ (n + 1) / (((n : ℝ) + 1) / 2 - (d : ℝ) / 4) :=
    div_nonneg (pow_nonneg (Nat.cast_nonneg d) _) h1.le
  positivity

/-- **Summation of the heat scales.** -/
theorem HeatScaleEstimate.osBound_heatBracket {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (hd : 1 ≤ d) {n : ℕ} (hn : (d : ℝ) / 2 < n + 1)
    {F : Ω → Vec d → ℝ} {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (h : HeatScaleEstimate P n F c ε) :
    ∃ Z : Ω → ℝ, OsBound P Z 1 (heatScaleConstant d n c * ε ^ ((d : ℝ) / 2)) ∧
      ∀ᵐ a ∂P, heatBracket n (F a) ≤ ENNReal.ofReal (Z a) := by
  obtain ⟨Q, hQm, hQ0, hYm, hQ, hY⟩ := h
  have hY1 : ∀ᵐ a ∂P, ∀ k (w : Fin k → Fin d), k ≤ n + 1 →
      eLpNorm (heatDerivativeAverage (countIndex w) 1 (F a)) 2
        (volume.restrict (originBall d 1)) ≤ ENNReal.ofReal (Q k w 1 a) := by
    rw [ae_all_iff]
    intro k
    rw [ae_all_iff]
    intro w
    by_cases hk : k ≤ n + 1
    · filter_upwards [hY k w hk 1 ⟨one_pos, le_rfl⟩] with a ha
      exact fun _ => ha
    · exact Eventually.of_forall fun a h => absurd h hk
  have hY2 : ∀ᵐ a ∂P, ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) 1)), s ∈ Ioc (0 : ℝ) 1 →
      ∀ w : Fin (n + 1) → Fin d, eLpNorm (heatDerivativeAverage (countIndex w) s (F a)) 2
        (volume.restrict (originBall d 1)) ≤ ENNReal.ofReal (Q (n + 1) w s a) := by
    have hset : MeasurableSet {q : ℝ × Ω | q.1 ∈ Ioc (0 : ℝ) 1 →
        ∀ w : Fin (n + 1) → Fin d, eLpNorm (heatDerivativeAverage (countIndex w) q.1 (F q.2)) 2
          (volume.restrict (originBall d 1)) ≤ ENNReal.ofReal (Q (n + 1) w q.1 q.2)} := by
      have heq : {q : ℝ × Ω | q.1 ∈ Ioc (0 : ℝ) 1 →
          ∀ w : Fin (n + 1) → Fin d, eLpNorm (heatDerivativeAverage (countIndex w) q.1 (F q.2)) 2
            (volume.restrict (originBall d 1)) ≤ ENNReal.ofReal (Q (n + 1) w q.1 q.2)} =
          (Prod.fst ⁻¹' Ioc (0 : ℝ) 1)ᶜ ∪ ⋂ w : Fin (n + 1) → Fin d,
            {q : ℝ × Ω | eLpNorm (heatDerivativeAverage (countIndex w) q.1 (F q.2)) 2
              (volume.restrict (originBall d 1)) ≤ ENNReal.ofReal (Q (n + 1) w q.1 q.2)} := by
        ext q
        simp only [mem_setOf_eq, mem_union, mem_compl_iff, mem_preimage, mem_iInter]
        tauto
      rw [heq]
      exact (measurableSet_Ioc.preimage measurable_fst).compl.union
        (MeasurableSet.iInter fun w => measurableSet_le (hYm (n + 1) w)
          (ENNReal.measurable_ofReal.comp (hQm (n + 1) w)))
    refine (Measure.ae_ae_comm (μ := volume.restrict (Ioc (0 : ℝ) 1)) (ν := P) hset).mp ?_
    refine Eventually.of_forall fun s => ?_
    by_cases hs : s ∈ Ioc (0 : ℝ) 1
    · have h := ae_all_iff.mpr fun w : Fin (n + 1) → Fin d => hY (n + 1) w le_rfl s hs
      filter_upwards [h] with a ha
      exact fun _ => ha
    · exact Eventually.of_forall fun a h => absurd h hs
  set e := ε ^ ((d : ℝ) / 2) with he
  have he0 : 0 < e := Real.rpow_pos_of_pos hε _
  set α : ℝ := (n : ℝ) - ((n : ℝ) + 1) / 2 - (d : ℝ) / 4 with hα
  have hα1 : -1 < α := by rw [hα]; linarith
  have hα' : α + 1 = ((n : ℝ) + 1) / 2 - (d : ℝ) / 4 := by rw [hα]; ring
  have hne : ∀ k, (Finset.univ : Finset (Fin k → Fin d)).Nonempty := fun k =>
    Finset.univ_nonempty_iff.mpr ⟨fun _ => ⟨0, hd⟩⟩
  set Z₁ : Ω → ℝ := fun a => ∑ k ∈ Finset.range (n + 1), ∑ w : Fin k → Fin d, Q k w 1 a
    with hZ₁def
  have hZ₁ : OsBound P Z₁ 1 (∑ k ∈ Finset.range (n + 1), ∑ _w : Fin k → Fin d, c * e) := by
    refine osBound_finset_sum _ ⟨0, by simp⟩ le_rfl fun k hk => ?_
    refine osBound_finset_sum _ (hne k) le_rfl fun w _ => ?_
    have := hQ k w (by rw [Finset.mem_range] at hk; omega) 1 ⟨one_pos, le_rfl⟩
    simpa [Real.one_rpow] using this
  set X : ℝ → Ω → ℝ := fun s a => if s ∈ Ioc (0 : ℝ) 1 then
    s ^ n * ∑ w : Fin (n + 1) → Fin d, Q (n + 1) w s a else 0 with hXdef
  set θ : ℝ → ℝ := fun s => if s ∈ Ioc (0 : ℝ) 1 then
    s ^ n * ∑ _w : Fin (n + 1) → Fin d,
      c * s ^ (-((n + 1 : ℕ) : ℝ) / 2 - (d : ℝ) / 4) * e else 1 with hθdef
  have hXm : Measurable (Function.uncurry X) := by
    refine Measurable.ite (measurableSet_Ioc.preimage measurable_fst) ?_ measurable_const
    exact (measurable_fst.pow_const n).mul (Finset.measurable_sum _ fun w _ => hQm (n + 1) w)
  have hX0 : ∀ s a, 0 ≤ X s a := fun s a => by
    simp only [hXdef]
    split_ifs with hs
    · exact mul_nonneg (pow_nonneg hs.1.le n) (Finset.sum_nonneg fun w _ => hQ0 _ _ _ _)
    · exact le_rfl
  have hθm : Measurable θ := by
    refine Measurable.ite measurableSet_Ioc ?_ measurable_const
    fun_prop
  have hXos : ∀ s, OsBound P (X s) 1 (θ s) := fun s => by
    by_cases hs : s ∈ Ioc (0 : ℝ) 1
    · simp only [hXdef, hθdef, hs, ↓reduceIte]
      exact (osBound_finset_sum _ (hne (n + 1)) le_rfl fun w _ =>
        hQ (n + 1) w le_rfl s hs).const_mul (pow_pos hs.1 n)
    · simp only [hXdef, hθdef, hs, ↓reduceIte]
      exact osBound_zero one_pos one_pos
  have hθeq : ∀ s ∈ Ioc (0 : ℝ) 1, θ s = c * e * (d : ℝ) ^ (n + 1) * s ^ α := fun s hs => by
    simp only [hθdef, hs, ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, nsmul_eq_mul]
    have hsplit : α = (n : ℝ) + (-((n + 1 : ℕ) : ℝ) / 2 - (d : ℝ) / 4) := by
      rw [hα]; push_cast; ring
    rw [hsplit, Real.rpow_add hs.1, Real.rpow_natCast]
    push_cast
    ring
  have hθi : Integrable θ (volume.restrict (Ioc (0 : ℝ) 1)) := by
    have h1 : IntegrableOn (fun s : ℝ => c * e * (d : ℝ) ^ (n + 1) * s ^ α) (Ioc 0 1) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' hα1)).const_mul _
    exact h1.congr_fun (fun s hs => (hθeq s hs).symm) measurableSet_Ioc
  have hθint : ∫ s, θ s ∂(volume.restrict (Ioc (0 : ℝ) 1)) =
      c * e * (d : ℝ) ^ (n + 1) * (α + 1)⁻¹ := by
    rw [setIntegral_congr_fun measurableSet_Ioc hθeq, integral_const_mul,
      ← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl hα1), Real.one_rpow,
      Real.zero_rpow (by linarith : α + 1 ≠ 0)]
    ring
  have hθpos : 0 < ∫ s, θ s ∂(volume.restrict (Ioc (0 : ℝ) 1)) := by
    rw [hθint]
    have : 0 < α + 1 := by linarith
    have hdp : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  obtain ⟨hXint, hZ₂⟩ := osBound_integral le_rfl hXm hX0 hθm hθi hθpos hXos
  rw [hθint] at hZ₂
  refine ⟨fun a => Z₁ a + ∫ s, X s a ∂(volume.restrict (Ioc (0 : ℝ) 1)), ?_, ?_⟩
  · refine (osBound_add hZ₁ hZ₂ le_rfl).mono_scale (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul]
    unfold heatScaleConstant
    rw [hα']
    push_cast
    rw [← Finset.sum_mul, div_eq_mul_inv]
    ring
  · filter_upwards [hY1, hY2, hXint] with a ha ha2 hai
    unfold heatBracket
    have hT1 : (∑ k ∈ Finset.range (n + 1), ∑ w : Fin k → Fin d,
        eLpNorm (heatDerivativeAverage (countIndex w) 1 (F a)) 2
          (volume.restrict (originBall d 1))) ≤ ENNReal.ofReal (Z₁ a) := by
      simp only [hZ₁def]
      rw [ENNReal.ofReal_sum_of_nonneg fun k _ => Finset.sum_nonneg fun w _ => hQ0 _ _ _ _]
      refine Finset.sum_le_sum fun k hk => ?_
      rw [ENNReal.ofReal_sum_of_nonneg fun w _ => hQ0 _ _ _ _]
      exact Finset.sum_le_sum fun w _ =>
        ha k w (by rw [Finset.mem_range] at hk; omega)
    have hT2 : ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (s ^ n) * ∑ w : Fin (n + 1) → Fin d,
        eLpNorm (heatDerivativeAverage (countIndex w) s (F a)) 2
          (volume.restrict (originBall d 1)) ≤
        ENNReal.ofReal (∫ s, X s a ∂(volume.restrict (Ioc (0 : ℝ) 1))) := by
      rw [ofReal_integral_eq_lintegral_ofReal hai (Eventually.of_forall fun s => hX0 s a)]
      refine lintegral_mono_ae ?_
      filter_upwards [ha2, ae_restrict_mem measurableSet_Ioc] with s hs2 hs
      simp only [hXdef, hs, ↓reduceIte]
      rw [ENNReal.ofReal_mul (pow_nonneg hs.1.le n),
        ENNReal.ofReal_sum_of_nonneg fun w _ => hQ0 _ _ _ _]
      gcongr with w
      exact hs2 hs w
    have hZ₁0 : 0 ≤ Z₁ a := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun w _ => hQ0 _ _ _ _
    calc _ ≤ ENNReal.ofReal (Z₁ a) +
          ENNReal.ofReal (∫ s, X s a ∂(volume.restrict (Ioc (0 : ℝ) 1))) := add_le_add hT1 hT2
      _ = _ := (ENNReal.ofReal_add hZ₁0 (integral_nonneg fun s => hX0 s a)).symm

/-- **(4.126) from the per-scale estimates** for the components of `∇φ_e(·/ε)` and of
`a(·/ε)(e + ∇φ_e(·/ε)) - ā e`, together with their Gaussian moments. -/
theorem negativeSobolevCorrector_of_heatScale
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ m : ℕ, (d : ℝ) / 2 < m →
      ∃ c : ℝ, 0 < c ∧ ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
        ∃ S : HomogenizationData P, ∀ e : Vec d, euclideanNorm e < 1 →
          ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ j : Fin d,
            (∀ᵐ a ∂P, HasGaussianMoment (fun x => (S.corrector e).grad a (ε⁻¹ • x) j) ∧
              HasGaussianMoment (fun x => ((a (ε⁻¹ • x)).mulVec
                (e + (S.corrector e).grad a (ε⁻¹ • x)) - S.homogenized.mulVec e) j)) ∧
            HeatScaleEstimate P (m - 1) (fun a x => (S.corrector e).grad a (ε⁻¹ • x) j) c ε ∧
            HeatScaleEstimate P (m - 1) (fun a x => ((a (ε⁻¹ • x)).mulVec
              (e + (S.corrector e).grad a (ε⁻¹ • x)) - S.homogenized.mulVec e) j) c ε) :
    QSH.Frozen.negativeSobolevCorrector := by
  refine negativeSobolevCorrector_of_heatBracket fun d hd Λ hΛ m hm => ?_
  obtain ⟨c, hc, hP⟩ := h d hd Λ hΛ m hm
  have hm0 : 1 ≤ m := by
    have h0 : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm
    have h1 : 0 < m := by exact_mod_cast h0
    omega
  have hm1 : (d : ℝ) / 2 < ((m - 1 : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub hm0, Nat.cast_one, sub_add_cancel]
    exact hm
  refine ⟨heatScaleConstant d (m - 1) c, heatScaleConstant_pos hm1 hc, fun P hPl => ?_⟩
  have := hPl.1
  obtain ⟨S, hS⟩ := hP P hPl
  refine ⟨S, fun e he ε hε hε2 j => ?_⟩
  obtain ⟨hG, h1, h2⟩ := hS e he ε hε hε2 j
  obtain ⟨Z₁, hZ₁, hb₁⟩ := h1.osBound_heatBracket (by omega) hm1 hc hε
  obtain ⟨Z₂, hZ₂, hb₂⟩ := h2.osBound_heatBracket (by omega) hm1 hc hε
  refine ⟨Z₁, Z₂, hZ₁, hZ₂, ?_⟩
  filter_upwards [hG, hb₁, hb₂] with a ha h1 h2
  exact ⟨⟨ha.1, h1⟩, ⟨ha.2, h2⟩⟩

end QSH
