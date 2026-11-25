import QuantitativeStochasticHomogenization.Ch07.Sec01.GoodLambda
import QuantitativeStochasticHomogenization.AppC.GehringLemma

/-!
# Lemma 7.2

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 7.1, Lemma 7.2: for `p ∈ (2, ∞)`, `q ∈ (p, ∞]` and `A ≥ 1` there are `δ₀(p, q, A, d) > 0`
and `C(p, q, A, d) < ∞` such that, for every `δ ∈ (0, δ₀]`, if `f ∈ L²(B_1)`, `g ∈ L^p(B_1)` and,
on every ball, `f` is approximated by some `f_{x,r} ∈ L^q(B_r(x))` with
`‖f_{x,r}‖_{L̲^q(B_r(x))} ≤ A ‖g‖_{L̲²(B_{2r}(x))} + A ‖f‖_{L̲²(B_{2r}(x))}` (7.6) and
`‖f - f_{x,r}‖_{L̲²(B_r(x))} ≤ A ‖g‖_{L̲²(B_{2r}(x))} + δ ‖f‖_{L̲²(B_{2r}(x))}` (7.7), then
`f ∈ L^p(B_{1/2})` and `‖f‖_{L̲^p(B_{1/2})} ≤ C (‖f‖_{L̲²(B_1)} + ‖g‖_{L̲^p(B_1)})` (7.8).

The proof is the book's. With `G = ε⁻¹ g` and `η = εA + δ`, the good-λ inequality (7.10)
(`cz_goodLambda`) and the layer cake formula give, for the truncated quantities
`Ψ(s) = ∫_{B_{sR}} f² (|f| ∧ m)^{p-2}` and `1/2 ≤ s < t < 1`,
`Ψ(s) ≤ (M λ₀)^{p-2} ∫_{B_{sR}} f² + K (4M)^{p-2} (Ψ(t) + ∫_{B_{tR}} |G|^p)` (`cz_step`), where
`K = 16 · 8^d (2 (M/2)^{2-q} A^q + 6 η²)`. The choice of `M` (large, as `p < q`) and then of `ε`
and `δ₀` (small) makes `K (4M)^{p-2} ≤ 1/2`, so that Lemma C.6 bounds `Ψ(1/2)`, and the monotone
convergence theorem removes the truncation `m`. As in the proof of Lemma C.4, the truncated
quantity is `∫ f² (|f| ∧ m)^{p-2}`, which the display after (7.9) writes as `‖f_m‖^p_{L^p}`.

The book states the hypotheses (7.6) and (7.7) for `x ∈ B_{1/2}` and `r ∈ (0, 1/4)`, while its
proof applies them at the stopping balls `B_{5 r_x}(x)` with centers `x ∈ B_s`, `s` up to `1`. The
statement proved here (`lemma_7_2_ball`) takes them on every ball `B_r(x)` with `r < R/2` and
`B_{2r}(x) ⊆ B_R`, for every radius `R > 0`, with the conclusion on `B_{R/2}`; this is the form used in the proof
of Proposition 7.3. With `R = 1/2` the hypotheses of the book's statement suffice, and give the
conclusion on `B_{1/4}` (`lemma_7_2`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The `f`-part of the integrated good-λ inequality. -/
theorem cz_fterm {B : Set (Vec d)} {N ε m c : ℝ} (hN : 1 ≤ N) (hε : 0 < ε) (hm : 0 ≤ m)
    (hc : 0 ≤ c) {f : Vec d → ℝ} (hfm : Measurable f) :
    ENNReal.ofReal ε * ∫⁻ τ in Ioi 0, ENNReal.ofReal c *
        ((∫⁻ x in B ∩ {x | τ < min (N * |f x|) m}, ‖f x‖ₑ ^ (2 : ℝ)) *
          ENNReal.ofReal (τ ^ (ε - 1))) ≤
      ENNReal.ofReal (c * N ^ ε) *
        ∫⁻ x in B, ‖f x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (min |f x| m ^ ε) := by
  have hφm : Measurable fun x => min (N * |f x|) m :=
    (measurable_const.mul hfm.abs).min measurable_const
  have hlc := setLIntegral_mul_ofReal_rpow_eq (B := B) (hfm.enorm.pow_const (2 : ℝ)) hφm
    (fun x => le_min (mul_nonneg (by linarith) (abs_nonneg _)) hm) hε
  have hmeasT : Measurable fun τ : ℝ =>
      (∫⁻ x in B ∩ {x | τ < min (N * |f x|) m}, ‖f x‖ₑ ^ (2 : ℝ)) *
        ENNReal.ofReal (τ ^ (ε - 1)) :=
    measurable_setLIntegral_levelSet.mul
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))
  rw [lintegral_const_mul _ hmeasT, mul_left_comm, ← hlc]
  have hpt : ∀ x, ‖f x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (min (N * |f x|) m ^ ε) ≤
      ENNReal.ofReal (N ^ ε) * (‖f x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (min |f x| m ^ ε)) := by
    intro x
    rw [mul_left_comm, ← ENNReal.ofReal_mul (by positivity)]
    gcongr
    rw [← Real.mul_rpow (by linarith) (le_min (abs_nonneg _) hm)]
    refine Real.rpow_le_rpow (le_min (mul_nonneg (by linarith) (abs_nonneg _)) hm) ?_ hε.le
    rcases le_total |f x| m with h | h
    · rw [min_eq_left h]
      exact min_le_left _ _
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans (le_mul_of_one_le_left hm hN)
  calc ENNReal.ofReal c * ∫⁻ x in B, ‖f x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (min (N * |f x|) m ^ ε)
      ≤ ENNReal.ofReal c * ∫⁻ x in B, ENNReal.ofReal (N ^ ε) *
          (‖f x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (min |f x| m ^ ε)) :=
        mul_le_mul_of_nonneg_left (lintegral_mono fun x => hpt x) bot_le
    _ = _ := by
        have hmeas : Measurable fun x => ‖f x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (min |f x| m ^ ε) :=
          (hfm.enorm.pow_const _).mul
            (ENNReal.measurable_ofReal.comp ((hfm.abs.min measurable_const).pow_const _))
        rw [lintegral_const_mul _ hmeas, ← mul_assoc, ← ENNReal.ofReal_mul hc]

/-- The `G`-part of the integrated good-λ inequality. -/
theorem cz_gterm {B : Set (Vec d)} {N ε c : ℝ} (hN : 0 ≤ N) (hε : 0 < ε) (hc : 0 ≤ c)
    {g : Vec d → ℝ} (hgm : Measurable g) :
    ENNReal.ofReal ε * ∫⁻ τ in Ioi 0, ENNReal.ofReal c *
        ((∫⁻ x in B ∩ {x | τ < N * |g x|}, ‖g x‖ₑ ^ (2 : ℝ)) *
          ENNReal.ofReal (τ ^ (ε - 1))) ≤
      ENNReal.ofReal (c * N ^ ε) * ∫⁻ x in B, ‖g x‖ₑ ^ (2 + ε) := by
  have hφm : Measurable fun x => N * |g x| := measurable_const.mul hgm.abs
  have hlc := setLIntegral_mul_ofReal_rpow_eq (B := B) (hgm.enorm.pow_const (2 : ℝ)) hφm
    (fun x => mul_nonneg hN (abs_nonneg _)) hε
  have hmeasT : Measurable fun τ : ℝ =>
      (∫⁻ x in B ∩ {x | τ < N * |g x|}, ‖g x‖ₑ ^ (2 : ℝ)) * ENNReal.ofReal (τ ^ (ε - 1)) :=
    measurable_setLIntegral_levelSet.mul
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))
  rw [lintegral_const_mul _ hmeasT, mul_left_comm, ← hlc]
  have hpt : ∀ x, ‖g x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal ((N * |g x|) ^ ε) ≤
      ENNReal.ofReal (N ^ ε) * ‖g x‖ₑ ^ (2 + ε) := by
    intro x
    rw [enorm_rpow_eq_ofReal _ (by norm_num), enorm_rpow_eq_ofReal _ (by linarith),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [Real.mul_rpow hN (abs_nonneg _), Real.rpow_add' (abs_nonneg _) (by linarith)]
    ring
  calc ENNReal.ofReal c * ∫⁻ x in B, ‖g x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal ((N * |g x|) ^ ε)
      ≤ ENNReal.ofReal c * ∫⁻ x in B, ENNReal.ofReal (N ^ ε) * ‖g x‖ₑ ^ (2 + ε) :=
        mul_le_mul_of_nonneg_left (lintegral_mono fun x => hpt x) bot_le
    _ = ENNReal.ofReal (c * N ^ ε) * ∫⁻ x in B, ‖g x‖ₑ ^ (2 + ε) := by
        have hmeas : Measurable fun x => ‖g x‖ₑ ^ (2 + ε) := hgm.enorm.pow_const _
        rw [lintegral_const_mul _ hmeas, ← mul_assoc, ← ENNReal.ofReal_mul hc]

/-- **The integrated good-λ inequality (7.9) before absorption.** With
`Ψ(σ) = ∫_{B_{σR}} f² (|f| ∧ m)^ε`, `ε = p - 2`, and
`λ₀ = (128/(t - s))^{d/2} (‖f‖_{L̲²(B_R)} + ‖G‖_{L̲²(B_R)})`,
`Ψ(s) ≤ (M λ₀)^ε ∫_{B_{sR}} f² + K (4M)^ε (Ψ(t) + ∫_{B_{tR}} |G|^{2+ε})`. -/
theorem cz_step {R s t q A η M ε m : ℝ} (hR : 0 < R) (hs : 0 < s) (hst : s < t)
    (ht : t ≤ 1) (hq : 2 < q) (hA : 0 ≤ A) (hη : 0 ≤ η) (hM : 1 ≤ M) (hε : 0 < ε) (hm : 0 < m)
    {f G : Vec d → ℝ} (hfm : Measurable f) (hGm : Measurable G)
    (hfint : IntegrableOn f (ball 0 R))
    (happrox : ∀ (z : Vec d) (ρ : ℝ), 0 < ρ → 2 * ρ < R → ball z (2 * ρ) ⊆ ball 0 R →
      ∃ h : Vec d → ℝ, Measurable h ∧
        PDE.eLpMeanNormOn (ball z ρ) (ENNReal.ofReal q) h ≤ ENNReal.ofReal A *
          (PDE.eLpMeanNormOn (ball z (2 * ρ)) 2 G + PDE.eLpMeanNormOn (ball z (2 * ρ)) 2 f) ∧
        PDE.eLpMeanNormOn (ball z ρ) 2 (f - h) ≤ ENNReal.ofReal η *
          (PDE.eLpMeanNormOn (ball z (2 * ρ)) 2 G + PDE.eLpMeanNormOn (ball z (2 * ρ)) 2 f))
    (hfin : ENNReal.ofReal ((128 / (t - s)) ^ ((d : ℝ) / 2)) *
        (PDE.eLpMeanNormOn (ball 0 R) 2 f + PDE.eLpMeanNormOn (ball 0 R) 2 G) ≠ ⊤) :
    ∫⁻ x in ball 0 (s * R), ‖f x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (min |f x| m ^ ε) ≤
      (∫⁻ x in ball 0 (s * R), ‖f x‖ₑ ^ (2 : ℝ)) *
          ENNReal.ofReal ((M * (ENNReal.ofReal ((128 / (t - s)) ^ ((d : ℝ) / 2)) *
            (PDE.eLpMeanNormOn (ball 0 R) 2 f +
              PDE.eLpMeanNormOn (ball 0 R) 2 G)).toReal) ^ ε) +
        ENNReal.ofReal (16 * 8 ^ d * (2 * (M / 2) ^ (2 - q) * A ^ q + 6 * η ^ 2) *
            (4 * M) ^ ε) *
          (∫⁻ x in ball 0 (t * R), ‖f x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (min |f x| m ^ ε)) +
        ENNReal.ofReal (16 * 8 ^ d * (2 * (M / 2) ^ (2 - q) * A ^ q + 6 * η ^ 2) *
            (4 * M) ^ ε) *
          ∫⁻ x in ball 0 (t * R), ‖G x‖ₑ ^ (2 + ε) := by
  set lam₀ := ENNReal.ofReal ((128 / (t - s)) ^ ((d : ℝ) / 2)) *
    (PDE.eLpMeanNormOn (ball 0 R) 2 f + PDE.eLpMeanNormOn (ball 0 R) 2 G) with hlam₀
  set K : ℝ := 16 * 8 ^ d * (2 * (M / 2) ^ (2 - q) * A ^ q + 6 * η ^ 2) with hK
  have hK0 : 0 ≤ K := by positivity
  have hM0 : 0 < M := by linarith
  set L₀ := M * lam₀.toReal with hL₀def
  have hL₀ : 0 ≤ L₀ := mul_nonneg hM0.le ENNReal.toReal_nonneg
  have hlam₀eq : lam₀ = ENNReal.ofReal lam₀.toReal := (ENNReal.ofReal_toReal hfin).symm
  set V := ∫⁻ x in ball 0 (s * R), ‖f x‖ₑ ^ (2 : ℝ) with hV
  have hφm : Measurable fun x => min |f x| m := hfm.abs.min measurable_const
  rw [setLIntegral_mul_ofReal_rpow_eq (hfm.enorm.pow_const (2 : ℝ)) hφm
    (fun x => le_min (abs_nonneg _) hm.le) hε, ← Ioc_union_Ioi_eq_Ioi hL₀,
    lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same, mul_add]
  -- the levels below `M λ₀`
  have hP1 : ENNReal.ofReal ε * ∫⁻ τ in Ioc 0 L₀,
      (∫⁻ x in ball 0 (s * R) ∩ {x | τ < min |f x| m}, ‖f x‖ₑ ^ (2 : ℝ)) *
        ENNReal.ofReal (τ ^ (ε - 1)) ≤ V * ENNReal.ofReal (L₀ ^ ε) := by
    calc ENNReal.ofReal ε * ∫⁻ τ in Ioc 0 L₀,
          (∫⁻ x in ball 0 (s * R) ∩ {x | τ < min |f x| m}, ‖f x‖ₑ ^ (2 : ℝ)) *
            ENNReal.ofReal (τ ^ (ε - 1))
        ≤ ENNReal.ofReal ε * ∫⁻ τ in Ioc 0 L₀, V * ENNReal.ofReal (τ ^ (ε - 1)) := by
          gcongr with τ
          exact lintegral_mono_set inter_subset_left
      _ = V * (ENNReal.ofReal ε * ∫⁻ τ in Ioc 0 L₀, ENNReal.ofReal (τ ^ (ε - 1))) := by
          have hmeas : Measurable fun τ : ℝ => ENNReal.ofReal (τ ^ (ε - 1)) :=
            ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
          rw [lintegral_const_mul _ hmeas]
          ring
      _ = V * ENNReal.ofReal (L₀ ^ ε) := by rw [ofReal_mul_lintegral_Ioc_rpow hε hL₀]
  -- the levels above `M λ₀`
  have hpt : ∀ τ ∈ Ioi L₀,
      (∫⁻ x in ball 0 (s * R) ∩ {x | τ < min |f x| m}, ‖f x‖ₑ ^ (2 : ℝ)) *
        ENNReal.ofReal (τ ^ (ε - 1)) ≤
      ENNReal.ofReal K * ((∫⁻ x in ball 0 (t * R) ∩ {x | τ < min (4 * M * |f x|) m},
          ‖f x‖ₑ ^ (2 : ℝ)) * ENNReal.ofReal (τ ^ (ε - 1))) +
        ENNReal.ofReal K * ((∫⁻ x in ball 0 (t * R) ∩ {x | τ < 4 * M * |G x|},
          ‖G x‖ₑ ^ (2 : ℝ)) * ENNReal.ofReal (τ ^ (ε - 1))) := by
    intro τ hτ
    have hτpos : 0 < τ := lt_of_le_of_lt hL₀ hτ
    by_cases hτm : τ < m
    · set l := τ / M with hl
      have hlpos : 0 < l := div_pos hτpos hM0
      have hMl : M * l = τ := by rw [hl]; field_simp
      have hset : {x | τ < min |f x| m} = {x | M * l < |f x|} := by
        ext x
        simp only [mem_ofPred_eq, lt_min_iff, hMl]
        exact ⟨fun h => h.1, fun h => ⟨h, hτm⟩⟩
      have hset2 : {x | l / 4 < |f x|} = {x | τ < min (4 * M * |f x|) m} := by
        ext x
        simp only [mem_ofPred_eq, lt_min_iff, hl, div_div, div_lt_iff₀ (by positivity : 0 < M * 4)]
        constructor
        · intro h
          exact ⟨by linarith, hτm⟩
        · intro h
          linarith [h.1]
      have hset3 : {x | l / 4 < |G x|} = {x | τ < 4 * M * |G x|} := by
        ext x
        simp only [mem_ofPred_eq, hl, div_div, div_lt_iff₀ (by positivity : 0 < M * 4)]
        constructor <;> intro h <;> linarith
      have hl₀ : lam₀ < ENNReal.ofReal l := by
        rw [hlam₀eq]
        refine (ENNReal.ofReal_lt_ofReal_iff hlpos).mpr ?_
        rw [hl, lt_div_iff₀ hM0]
        have : M * lam₀.toReal < τ := hτ
        linarith
      have h10 := cz_goodLambda hR hs hst ht hq hA hη hM hlpos hfm hGm hfint happrox hl₀
      rw [hset2, hset3] at h10
      rw [hset]
      calc (∫⁻ x in ball 0 (s * R) ∩ {x | M * l < |f x|}, ‖f x‖ₑ ^ (2 : ℝ)) *
            ENNReal.ofReal (τ ^ (ε - 1))
          ≤ (ENNReal.ofReal K *
              ((∫⁻ x in ball 0 (t * R) ∩ {x | τ < min (4 * M * |f x|) m}, ‖f x‖ₑ ^ (2 : ℝ)) +
                ∫⁻ x in ball 0 (t * R) ∩ {x | τ < 4 * M * |G x|}, ‖G x‖ₑ ^ (2 : ℝ))) *
              ENNReal.ofReal (τ ^ (ε - 1)) := by gcongr
        _ = _ := by ring
    · have hempty : ball 0 (s * R) ∩ {x | τ < min |f x| m} = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        intro _ h
        exact hτm (h.trans_le (min_le_right _ _))
      rw [hempty, Measure.restrict_empty, lintegral_zero_measure, zero_mul]
      exact bot_le
  have hmeas2 : Measurable fun τ : ℝ => ENNReal.ofReal K *
      ((∫⁻ x in ball 0 (t * R) ∩ {x | τ < min (4 * M * |f x|) m}, ‖f x‖ₑ ^ (2 : ℝ)) *
        ENNReal.ofReal (τ ^ (ε - 1))) :=
    measurable_const.mul (measurable_setLIntegral_levelSet.mul
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)))
  have hP2 : ∫⁻ τ in Ioi L₀,
      (∫⁻ x in ball 0 (s * R) ∩ {x | τ < min |f x| m}, ‖f x‖ₑ ^ (2 : ℝ)) *
        ENNReal.ofReal (τ ^ (ε - 1)) ≤
      (∫⁻ τ in Ioi 0, ENNReal.ofReal K *
          ((∫⁻ x in ball 0 (t * R) ∩ {x | τ < min (4 * M * |f x|) m}, ‖f x‖ₑ ^ (2 : ℝ)) *
            ENNReal.ofReal (τ ^ (ε - 1)))) +
        ∫⁻ τ in Ioi 0, ENNReal.ofReal K *
          ((∫⁻ x in ball 0 (t * R) ∩ {x | τ < 4 * M * |G x|}, ‖G x‖ₑ ^ (2 : ℝ)) *
            ENNReal.ofReal (τ ^ (ε - 1))) := by
    rw [← lintegral_add_left hmeas2]
    exact (setLIntegral_mono' measurableSet_Ioi hpt).trans
      (lintegral_mono_set (Ioi_subset_Ioi hL₀))
  have hf2 := cz_fterm (B := ball 0 (t * R)) (N := 4 * M) (m := m) (c := K) (by linarith) hε
    hm.le hK0 hfm
  have hg2 := cz_gterm (B := ball 0 (t * R)) (N := 4 * M) (c := K) (by linarith) hε hK0 hGm
  have hfin2 : ENNReal.ofReal ε * ∫⁻ τ in Ioi L₀,
      (∫⁻ x in ball 0 (s * R) ∩ {x | τ < min |f x| m}, ‖f x‖ₑ ^ (2 : ℝ)) *
        ENNReal.ofReal (τ ^ (ε - 1)) ≤
      ENNReal.ofReal ε * (∫⁻ τ in Ioi 0, ENNReal.ofReal K *
          ((∫⁻ x in ball 0 (t * R) ∩ {x | τ < min (4 * M * |f x|) m}, ‖f x‖ₑ ^ (2 : ℝ)) *
            ENNReal.ofReal (τ ^ (ε - 1)))) +
        ENNReal.ofReal ε * ∫⁻ τ in Ioi 0, ENNReal.ofReal K *
          ((∫⁻ x in ball 0 (t * R) ∩ {x | τ < 4 * M * |G x|}, ‖G x‖ₑ ^ (2 : ℝ)) *
            ENNReal.ofReal (τ ^ (ε - 1))) := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left hP2 bot_le
  calc _ ≤ V * ENNReal.ofReal (L₀ ^ ε) + (ENNReal.ofReal ε * (∫⁻ τ in Ioi 0, ENNReal.ofReal K *
          ((∫⁻ x in ball 0 (t * R) ∩ {x | τ < min (4 * M * |f x|) m}, ‖f x‖ₑ ^ (2 : ℝ)) *
            ENNReal.ofReal (τ ^ (ε - 1)))) +
        ENNReal.ofReal ε * ∫⁻ τ in Ioi 0, ENNReal.ofReal K *
          ((∫⁻ x in ball 0 (t * R) ∩ {x | τ < 4 * M * |G x|}, ‖G x‖ₑ ^ (2 : ℝ)) *
            ENNReal.ofReal (τ ^ (ε - 1)))) := add_le_add hP1 hfin2
    _ ≤ V * ENNReal.ofReal (L₀ ^ ε) +
        (ENNReal.ofReal (K * (4 * M) ^ ε) *
            (∫⁻ x in ball 0 (t * R), ‖f x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (min |f x| m ^ ε)) +
          ENNReal.ofReal (K * (4 * M) ^ ε) * ∫⁻ x in ball 0 (t * R), ‖G x‖ₑ ^ (2 + ε)) :=
        add_le_add le_rfl (add_le_add hf2 hg2)
    _ = _ := by rw [add_assoc]

/-- The choice of the constants in the proof of Lemma 7.2: with `M = 2 N₀`, `N₀ ≥ 1` and
`N₀^{q-p} ≥ 8 κ A^q 8^{p-2}`, `κ = 16 · 8^d`, and `η ≤ 1/(24 κ (4M)^{p-2})`, `η ≤ 1`, the factor
`κ (2 (M/2)^{2-q} A^q + 6 η²) (4M)^{p-2}` of `Ψ(t)` is at most `1/2`. -/
theorem cz_constant_le_half {q A ε N₀ η : ℝ} (hA : 0 < A) (hN₀ : 1 ≤ N₀)
    (hX : 8 * (16 * 8 ^ d) * A ^ q * 8 ^ ε ≤ N₀ ^ (q - (2 + ε))) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hη : η ≤ 1 / (24 * (16 * 8 ^ d) * (4 * (2 * N₀)) ^ ε)) :
    16 * 8 ^ d * (2 * (2 * N₀ / 2) ^ (2 - q) * A ^ q + 6 * η ^ 2) * (4 * (2 * N₀)) ^ ε ≤
      1 / 2 := by
  set κ : ℝ := 16 * 8 ^ d with hκ
  have hκ0 : 0 < κ := by positivity
  have hN₀0 : 0 < N₀ := by linarith
  have hM2 : 2 * N₀ / 2 = N₀ := by ring
  have hpow : N₀ ^ (2 - q) * (4 * (2 * N₀)) ^ ε = 8 ^ ε * (N₀ ^ (q - (2 + ε)))⁻¹ := by
    rw [show 4 * (2 * N₀) = 8 * N₀ by ring, Real.mul_rpow (by norm_num) hN₀0.le,
      ← Real.rpow_neg hN₀0.le, show -(q - (2 + ε)) = (2 - q) + ε by ring,
      Real.rpow_add hN₀0]
    ring
  set X : ℝ := 8 * κ * A ^ q * 8 ^ ε with hXdef
  have hX0 : 0 < X := by positivity
  have h1 : κ * (2 * N₀ ^ (2 - q) * A ^ q) * (4 * (2 * N₀)) ^ ε ≤ 1 / 4 := by
    have e : κ * (2 * N₀ ^ (2 - q) * A ^ q) * (4 * (2 * N₀)) ^ ε =
        2 * κ * A ^ q * 8 ^ ε * (N₀ ^ (q - (2 + ε)))⁻¹ := by
      calc κ * (2 * N₀ ^ (2 - q) * A ^ q) * (4 * (2 * N₀)) ^ ε =
          2 * κ * A ^ q * (N₀ ^ (2 - q) * (4 * (2 * N₀)) ^ ε) := by ring
        _ = _ := by rw [hpow]; ring
    rw [e]
    have hinv : (N₀ ^ (q - (2 + ε)))⁻¹ ≤ X⁻¹ := inv_anti₀ hX0 hX
    have hA0 : A ^ q ≠ 0 := (Real.rpow_pos_of_pos hA q).ne'
    have h80 : (8 : ℝ) ^ ε ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) ε).ne'
    calc 2 * κ * A ^ q * 8 ^ ε * (N₀ ^ (q - (2 + ε)))⁻¹
        ≤ 2 * κ * A ^ q * 8 ^ ε * X⁻¹ := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 1 / 4 := by
          rw [hXdef]
          field_simp
          ring
  have h2 : κ * (6 * η ^ 2) * (4 * (2 * N₀)) ^ ε ≤ 1 / 4 := by
    have hηsq : η ^ 2 ≤ 1 / (24 * κ * (4 * (2 * N₀)) ^ ε) := by
      have : η ^ 2 ≤ η := by nlinarith
      exact this.trans hη
    have hc0 : 0 < κ * (4 * (2 * N₀)) ^ ε := by positivity
    calc κ * (6 * η ^ 2) * (4 * (2 * N₀)) ^ ε = 6 * (κ * (4 * (2 * N₀)) ^ ε) * η ^ 2 := by ring
      _ ≤ 6 * (κ * (4 * (2 * N₀)) ^ ε) * (1 / (24 * κ * (4 * (2 * N₀)) ^ ε)) :=
          mul_le_mul_of_nonneg_left hηsq (by positivity)
      _ = 1 / 4 := by
          rw [show 24 * κ * (4 * (2 * N₀)) ^ ε = 24 * (κ * (4 * (2 * N₀)) ^ ε) by ring]
          field_simp
          ring
  rw [hM2]
  have e : κ * (2 * N₀ ^ (2 - q) * A ^ q + 6 * η ^ 2) * (4 * (2 * N₀)) ^ ε =
      κ * (2 * N₀ ^ (2 - q) * A ^ q) * (4 * (2 * N₀)) ^ ε +
        κ * (6 * η ^ 2) * (4 * (2 * N₀)) ^ ε := by ring
  rw [e]
  linarith

theorem eLpMeanNormOn_const_smul (U : Set (Vec d)) (r : ℝ≥0∞) {c : ℝ} (hc : 0 ≤ c)
    (k : Vec d → ℝ) :
    PDE.eLpMeanNormOn U r (c • k) = ENNReal.ofReal c * PDE.eLpMeanNormOn U r k := by
  rw [PDE.eLpMeanNormOn, PDE.eLpMeanNormOn, eLpNorm_const_smul, Real.enorm_eq_ofReal hc]

set_option maxHeartbeats 400000 in
/-- **Lemma 7.2** for measurable `f`, `g` and approximants, with `q < ∞`. -/
theorem lemma_7_2_measurable {p q A : ℝ} (hp : 2 < p) (hpq : p < q) (hA : 1 ≤ A) :
    ∃ δ₀ C : ℝ, 0 < δ₀ ∧ 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : ℝ, 0 < R →
      ∀ f g : Vec d → ℝ, Measurable f → Measurable g →
      MemLp f 2 (volume.restrict (ball 0 R)) →
      MemLp g (ENNReal.ofReal p) (volume.restrict (ball 0 R)) →
      (∀ (x : Vec d) (r : ℝ), 0 < r → 2 * r < R → ball x (2 * r) ⊆ ball 0 R →
        ∃ h : Vec d → ℝ, Measurable h ∧
          PDE.eLpMeanNormOn (ball x r) (ENNReal.ofReal q) h ≤ ENNReal.ofReal A *
            (PDE.eLpMeanNormOn (ball x (2 * r)) 2 g + PDE.eLpMeanNormOn (ball x (2 * r)) 2 f) ∧
          PDE.eLpMeanNormOn (ball x r) 2 (f - h) ≤
            ENNReal.ofReal A * PDE.eLpMeanNormOn (ball x (2 * r)) 2 g +
              ENNReal.ofReal δ * PDE.eLpMeanNormOn (ball x (2 * r)) 2 f) →
      PDE.eLpMeanNormOn (ball 0 (R / 2)) (ENNReal.ofReal p) f ≤
        ENNReal.ofReal C * (PDE.eLpMeanNormOn (ball 0 R) 2 f +
          PDE.eLpMeanNormOn (ball 0 R) (ENNReal.ofReal p) g) := by
  obtain ⟨ε, hε0, rfl⟩ : ∃ ε : ℝ, 0 < ε ∧ p = 2 + ε := ⟨p - 2, by linarith, by ring⟩
  have hq2 : 2 < q := by linarith
  have hA0 : 0 < A := by linarith
  set N₀ : ℝ := max 1 ((8 * (16 * 8 ^ d) * A ^ q * 8 ^ ε) ^ (1 / (q - (2 + ε)))) with hN₀
  have hN₀1 : 1 ≤ N₀ := le_max_left _ _
  have hqp : 0 < q - (2 + ε) := by linarith
  have hX : 8 * (16 * 8 ^ d) * A ^ q * 8 ^ ε ≤ N₀ ^ (q - (2 + ε)) := by
    have h0 : (0 : ℝ) ≤ 8 * (16 * 8 ^ d) * A ^ q * 8 ^ ε := by positivity
    calc 8 * (16 * 8 ^ d) * A ^ q * 8 ^ ε
        = ((8 * (16 * 8 ^ d) * A ^ q * 8 ^ ε) ^ (1 / (q - (2 + ε)))) ^ (q - (2 + ε)) := by
          rw [← Real.rpow_mul h0, one_div_mul_cancel hqp.ne', Real.rpow_one]
      _ ≤ N₀ ^ (q - (2 + ε)) :=
          Real.rpow_le_rpow (by positivity) (le_max_right _ _) hqp.le
  set M : ℝ := 2 * N₀ with hMdef
  have hM : 1 ≤ M := by linarith
  have hM0 : 0 < M := by linarith
  set η₀ : ℝ := min 1 (1 / (24 * (16 * 8 ^ d) * (4 * M) ^ ε)) with hη₀
  have hη₀0 : 0 < η₀ := lt_min one_pos (by positivity)
  have hη₀1 : η₀ ≤ 1 := min_le_left _ _
  set e : ℝ := η₀ / (2 * A) with he
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 := by
    rw [he, div_le_one (by positivity)]
    linarith
  have heA : e * A = η₀ / 2 := by
    rw [he]
    field_simp
  set ξ : ℝ := (d : ℝ) * ε / 2 with hξ
  have hξ0 : 0 ≤ ξ := by positivity
  obtain ⟨C₆, hC₆⟩ := lemma_C_6 ξ
  set C₆' := max C₆ 0 with hC₆'
  set CA : ℝ := M ^ ε * 128 ^ ξ + 1 with hCA
  set C₁ : ℝ := max 1 (2 ^ d * C₆' * CA) with hC₁
  refine ⟨η₀ / 2, C₁ * e⁻¹, by positivity, by positivity, ?_⟩
  intro δ hδ hδ₀ R hR f g hfm hgm hf hg hhyp
  set η : ℝ := e * A + δ with hη
  have hη0 : 0 ≤ η := by positivity
  have hηη₀ : η ≤ η₀ := by linarith
  have hθ : 16 * 8 ^ d * (2 * (M / 2) ^ (2 - q) * A ^ q + 6 * η ^ 2) * (4 * M) ^ ε ≤ 1 / 2 :=
    cz_constant_le_half hA0 hN₀1 hX hη0 (hηη₀.trans hη₀1)
      (hηη₀.trans (min_le_right _ _))
  -- the function `G = e⁻¹ g`
  set G : Vec d → ℝ := e⁻¹ • g with hG
  have hGm : Measurable G := hgm.const_smul _
  have hgG : g = e • G := by rw [hG, smul_smul, mul_inv_cancel₀ he0.ne', one_smul]
  have hnormG : ∀ (U : Set (Vec d)) (r : ℝ≥0∞),
      PDE.eLpMeanNormOn U r g = ENNReal.ofReal e * PDE.eLpMeanNormOn U r G := by
    intro U r
    rw [hgG, eLpMeanNormOn_const_smul U r he0.le]
  have happrox : ∀ (z : Vec d) (ρ : ℝ), 0 < ρ → 2 * ρ < R → ball z (2 * ρ) ⊆ ball 0 R →
      ∃ h : Vec d → ℝ, Measurable h ∧
        PDE.eLpMeanNormOn (ball z ρ) (ENNReal.ofReal q) h ≤ ENNReal.ofReal A *
          (PDE.eLpMeanNormOn (ball z (2 * ρ)) 2 G + PDE.eLpMeanNormOn (ball z (2 * ρ)) 2 f) ∧
        PDE.eLpMeanNormOn (ball z ρ) 2 (f - h) ≤ ENNReal.ofReal η *
          (PDE.eLpMeanNormOn (ball z (2 * ρ)) 2 G + PDE.eLpMeanNormOn (ball z (2 * ρ)) 2 f) := by
    intro z ρ hρ hρR hsub
    obtain ⟨h, hhm, h1, h2⟩ := hhyp z ρ hρ hρR hsub
    refine ⟨h, hhm, h1.trans ?_, h2.trans ?_⟩
    · rw [hnormG]
      gcongr
      calc ENNReal.ofReal e * PDE.eLpMeanNormOn (ball z (2 * ρ)) 2 G
          ≤ 1 * PDE.eLpMeanNormOn (ball z (2 * ρ)) 2 G := by
            gcongr
            exact ENNReal.ofReal_le_one.mpr he1
        _ = _ := one_mul _
    · rw [hnormG, ← mul_assoc, ← ENNReal.ofReal_mul hA0.le, hη,
        ENNReal.ofReal_add (by positivity) hδ.le, add_mul, mul_add, mul_add, mul_comm A e]
      exact add_le_add le_self_add le_add_self
  -- norms and volumes
  have hR2 : 0 < R / 2 := half_pos hR
  have hvR0 := volume_ball_ne_zero' (0 : Vec d) hR
  have hvRt := volume_ball_ne_top' (0 : Vec d) R
  have hfinμ : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
    isFiniteMeasure_restrict.mpr hvRt
  have hGp : MemLp G (ENNReal.ofReal (2 + ε)) (volume.restrict (ball 0 R)) := hg.const_smul _
  have hG2 : MemLp G 2 (volume.restrict (ball 0 R)) :=
    hGp.mono_exponent (by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
      exact ENNReal.ofReal_le_ofReal (by linarith))
  have hfint : IntegrableOn f (ball 0 R) := hf.integrable one_le_two
  have hNf_ne := eLpMeanNormOn_ne_top hvR0 hf
  have hNG_ne := eLpMeanNormOn_ne_top hvR0 hG2
  have hNGp_ne := eLpMeanNormOn_ne_top hvR0 hGp
  obtain ⟨nf, hnf⟩ : ∃ x, x = (PDE.eLpMeanNormOn (ball 0 R) 2 f).toReal := ⟨_, rfl⟩
  obtain ⟨nG, hnG⟩ : ∃ x, x = (PDE.eLpMeanNormOn (ball 0 R) 2 G).toReal := ⟨_, rfl⟩
  obtain ⟨nGp, hnGp⟩ : ∃ x, x = (PDE.eLpMeanNormOn (ball 0 R) (ENNReal.ofReal (2 + ε)) G).toReal :=
    ⟨_, rfl⟩
  have hnf0 : 0 ≤ nf := hnf ▸ ENNReal.toReal_nonneg
  have hnG0 : 0 ≤ nG := hnG ▸ ENNReal.toReal_nonneg
  have hnGp0 : 0 ≤ nGp := hnGp ▸ ENNReal.toReal_nonneg
  have hNf_eq : PDE.eLpMeanNormOn (ball 0 R) 2 f = ENNReal.ofReal nf := by
    rw [hnf, ENNReal.ofReal_toReal hNf_ne]
  have hNG_eq : PDE.eLpMeanNormOn (ball 0 R) 2 G = ENNReal.ofReal nG := by
    rw [hnG, ENNReal.ofReal_toReal hNG_ne]
  have hNGp_eq : PDE.eLpMeanNormOn (ball 0 R) (ENNReal.ofReal (2 + ε)) G = ENNReal.ofReal nGp := by
    rw [hnGp, ENNReal.ofReal_toReal hNGp_ne]
  have hnG_le : nG ≤ nGp := by
    have hpos : 0 < volume (ball (0 : Vec d) R) := pos_iff_ne_zero.mpr hvR0
    have : IsProbabilityMeasure (PDE.normalizedVolumeOn (ball (0 : Vec d) R)) :=
      PDE.isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top hpos hvRt.lt_top
    rw [hnG, hnGp]
    refine ENNReal.toReal_mono hNGp_ne (eLpNorm_le_eLpNorm_of_exponent_le ?_)
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  obtain ⟨vRr, hvRrdef⟩ : ∃ x, x = (volume (ball (0 : Vec d) R)).toReal := ⟨_, rfl⟩
  have hvRr : 0 < vRr := hvRrdef ▸ ENNReal.toReal_pos hvR0 hvRt
  have hvR_eq : volume (ball (0 : Vec d) R) = ENNReal.ofReal vRr := by
    rw [hvRrdef, ENNReal.ofReal_toReal hvRt]
  set Ac : ℝ := M ^ ε * 128 ^ ξ * nf ^ 2 * (nf + nG) ^ ε + nGp ^ (2 + ε) with hAc
  have hAc0 : 0 ≤ Ac := by positivity
  -- the conclusion for each truncation level
  have hmain : ∀ m : ℝ, 0 < m →
      ∫⁻ x in ball 0 (R / 2), ENNReal.ofReal (min |f x| m ^ (2 + ε)) ≤
        ENNReal.ofReal (vRr * (C₆' * Ac)) := by
    intro m hm
    set Ψ : ℝ → ℝ≥0∞ := fun s => ∫⁻ x in ball 0 (s * R), ‖f x‖ₑ ^ (2 : ℝ) *
      ENNReal.ofReal (min |f x| m ^ ε) with hΨ
    have hsubR : ∀ u : ℝ, 0 < u → u ≤ 1 → ball (0 : Vec d) (u * R) ⊆ ball 0 R := by
      intro u hu hu1
      exact ball_subset_ball_of_norm (by
        rw [sub_zero, show euclideanNorm (0 : Vec d) = 0 by simp [euclideanNorm,
          euclideanSq, dot]]
        nlinarith)
    have hf2int : ∫⁻ x in ball 0 R, ‖f x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (vRr * nf ^ 2) := by
      have h2 := lintegral_ball_rpow_eq (d := d) hR two_pos hfm.aestronglyMeasurable
      rw [ENNReal.ofReal_ofNat] at h2
      rw [h2, hvR_eq, hNf_eq, ENNReal.ofReal_rpow_of_nonneg hnf0 (by norm_num),
        ← ENNReal.ofReal_mul hvRr.le, Real.rpow_two]
    have hΨle : ∀ s, 0 < s → s ≤ 1 → Ψ s ≤ ENNReal.ofReal (vRr * nf ^ 2 * m ^ ε) := by
      intro s hs hs1
      calc Ψ s ≤ ∫⁻ x in ball 0 R, ‖f x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (m ^ ε) := by
            refine (lintegral_mono_set (hsubR s hs hs1)).trans (lintegral_mono fun x => ?_)
            gcongr
            exact min_le_right _ _
        _ = ENNReal.ofReal (vRr * nf ^ 2 * m ^ ε) := by
            rw [lintegral_mul_const _ (hfm.enorm.pow_const _), hf2int,
              ← ENNReal.ofReal_mul (by positivity)]
    have hΨne : ∀ s, 0 < s → s ≤ 1 → Ψ s ≠ ⊤ := fun s hs hs1 =>
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hΨle s hs hs1)
    set ρ : ℝ → ℝ := fun s => (Ψ s).toReal / vRr with hρ
    have hρ0 : ∀ t ∈ Ico (1 / 2 : ℝ) 1, 0 ≤ ρ t := fun t _ =>
      div_nonneg ENNReal.toReal_nonneg hvRr.le
    have hρbdd : BddAbove ((fun t => (1 - t) ^ ξ * ρ t) '' Ico (1 / 2 : ℝ) 1) := by
      refine ⟨nf ^ 2 * m ^ ε, ?_⟩
      rintro y ⟨t, ⟨ht1, ht2⟩, rfl⟩
      have h1 : (1 - t) ^ ξ ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) hξ0
      have h2 : ρ t ≤ nf ^ 2 * m ^ ε := by
        rw [hρ, div_le_iff₀ hvRr]
        have := ENNReal.toReal_le_of_le_ofReal (by positivity) (hΨle t (by linarith) ht2.le)
        linarith
      calc (1 - t) ^ ξ * ρ t ≤ 1 * (nf ^ 2 * m ^ ε) :=
            mul_le_mul h1 h2 (hρ0 t ⟨ht1, ht2⟩) zero_le_one
        _ = nf ^ 2 * m ^ ε := one_mul _
    have hiter : ∀ s t : ℝ, 1 / 2 ≤ s → s < t → t < 1 →
        ρ s ≤ 1 / 2 * ρ t + (t - s) ^ (-ξ) * Ac := by
      intro s t hs hst ht
      have hs0 : 0 < s := by linarith
      have hts : 0 < t - s := by linarith
      have hstep := cz_step (d := d) hR hs0 hst ht.le hq2 hA0.le hη0 hM hε0 hm hfm hGm hfint
        happrox (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr
          ⟨hNf_ne, hNG_ne⟩))
      have hV : ∫⁻ x in ball 0 (s * R), ‖f x‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (vRr * nf ^ 2) :=
        (lintegral_mono_set (hsubR s hs0 (by linarith))).trans (le_of_eq hf2int)
      have hGint : ∫⁻ x in ball 0 (t * R), ‖G x‖ₑ ^ (2 + ε) ≤
          ENNReal.ofReal (vRr * nGp ^ (2 + ε)) := by
        refine (lintegral_mono_set (hsubR t (by linarith) ht.le)).trans (le_of_eq ?_)
        rw [lintegral_ball_rpow_eq hR (by linarith) hGm.aestronglyMeasurable, hvR_eq, hNGp_eq,
          ENNReal.ofReal_rpow_of_nonneg hnGp0 (by linarith), ← ENNReal.ofReal_mul hvRr.le]
      set L := M * ((128 / (t - s)) ^ ((d : ℝ) / 2) * (nf + nG)) with hL
      have hLeq : M * (ENNReal.ofReal ((128 / (t - s)) ^ ((d : ℝ) / 2)) *
          (PDE.eLpMeanNormOn (ball 0 R) 2 f + PDE.eLpMeanNormOn (ball 0 R) 2 G)).toReal = L := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
          ENNReal.toReal_add hNf_ne hNG_ne, ← hnf, ← hnG]
      have hΨt : Ψ t = ENNReal.ofReal (Ψ t).toReal :=
        (ENNReal.ofReal_toReal (hΨne t (by linarith) ht.le)).symm
      have hbig : Ψ s ≤ ENNReal.ofReal (vRr * nf ^ 2 * L ^ ε + 1 / 2 * (Ψ t).toReal +
          1 / 2 * (vRr * nGp ^ (2 + ε))) := by
        refine hstep.trans ?_
        rw [hLeq]
        have e1 := ENNReal.ofReal_le_ofReal hθ
        calc _ ≤ ENNReal.ofReal (vRr * nf ^ 2) * ENNReal.ofReal (L ^ ε) +
              ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Ψ t).toReal +
              ENNReal.ofReal (1 / 2) * ENNReal.ofReal (vRr * nGp ^ (2 + ε)) := by
              gcongr
              exact le_of_eq hΨt
          _ = _ := by
              rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num),
                ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
                  (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      have hψ := ENNReal.toReal_le_of_le_ofReal (by positivity) hbig
      have hLε : L ^ ε = (t - s) ^ (-ξ) * (M ^ ε * 128 ^ ξ * (nf + nG) ^ ε) := by
        rw [hL, Real.mul_rpow (x := M) hM0.le (by positivity),
          Real.mul_rpow (x := (128 / (t - s)) ^ ((d : ℝ) / 2)) (by positivity) (by positivity),
          ← Real.rpow_mul (x := 128 / (t - s)) (by positivity),
          Real.div_rpow (x := 128) (by norm_num) hts.le,
          Real.rpow_neg hts.le, hξ, show (d : ℝ) / 2 * ε = d * ε / 2 by ring, div_eq_mul_inv]
        ring
      have hone : 1 ≤ (t - s) ^ (-ξ) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hts (by linarith) (by linarith)
      have hρs : ρ s ≤ nf ^ 2 * L ^ ε + 1 / 2 * ρ t + 1 / 2 * nGp ^ (2 + ε) := by
        have h := div_le_div_of_nonneg_right hψ hvRr.le
        have e : (vRr * nf ^ 2 * L ^ ε + 1 / 2 * (Ψ t).toReal + 1 / 2 * (vRr * nGp ^ (2 + ε))) /
            vRr = nf ^ 2 * L ^ ε + 1 / 2 * ((Ψ t).toReal / vRr) + 1 / 2 * nGp ^ (2 + ε) := by
          field_simp
        rw [e] at h
        exact h
      rw [hLε] at hρs
      have hc0 : 1 / 2 * nGp ^ (2 + ε) ≤ (t - s) ^ (-ξ) * nGp ^ (2 + ε) := by
        have : nGp ^ (2 + ε) ≤ (t - s) ^ (-ξ) * nGp ^ (2 + ε) :=
          le_mul_of_one_le_left (by positivity) hone
        have h0 : 0 ≤ nGp ^ (2 + ε) := by positivity
        linarith
      have e : nf ^ 2 * ((t - s) ^ (-ξ) * (M ^ ε * 128 ^ ξ * (nf + nG) ^ ε)) =
          (t - s) ^ (-ξ) * (M ^ ε * 128 ^ ξ * nf ^ 2 * (nf + nG) ^ ε) := by ring
      rw [hAc, mul_add]
      linarith
    have hρhalf := hC₆ Ac hAc0 ρ hρ0 hρbdd hiter
    have hρhalf' : ρ (1 / 2) ≤ C₆' * Ac :=
      hρhalf.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hAc0)
    have hhalf : ball (0 : Vec d) (R / 2) = ball 0 (1 / 2 * R) := by
      congr 1
      ring
    have hΨhalf : Ψ (1 / 2) = ENNReal.ofReal (vRr * ρ (1 / 2)) := by
      rw [hρ]
      simp only
      rw [mul_div_cancel₀ _ hvRr.ne', ENNReal.ofReal_toReal (hΨne _ (by norm_num) (by norm_num))]
    calc ∫⁻ x in ball 0 (R / 2), ENNReal.ofReal (min |f x| m ^ (2 + ε))
        ≤ Ψ (1 / 2) := by
          rw [hΨ, hhalf]
          refine lintegral_mono fun x => ?_
          have hmin0 : 0 ≤ min |f x| m := le_min (abs_nonneg _) hm.le
          rw [enorm_rpow_eq_ofReal _ (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Real.rpow_add' hmin0 (by linarith)]
          exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hmin0 (min_le_left _ _)
            (by norm_num)) (Real.rpow_nonneg hmin0 _)
      _ = ENNReal.ofReal (vRr * ρ (1 / 2)) := hΨhalf
      _ ≤ ENNReal.ofReal (vRr * (C₆' * Ac)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hρhalf' hvRr.le)
  -- monotone convergence
  have hlim : ∫⁻ x in ball 0 (R / 2), ‖f x‖ₑ ^ (2 + ε) ≤ ENNReal.ofReal (vRr * (C₆' * Ac)) := by
    have hmeas : ∀ n : ℕ, Measurable fun x => ENNReal.ofReal (min |f x| ((n : ℝ) + 1) ^ (2 + ε)) :=
      fun n => ENNReal.measurable_ofReal.comp ((hfm.abs.min measurable_const).pow_const _)
    have hmono : Monotone fun (n : ℕ) (x : Vec d) =>
        ENNReal.ofReal (min |f x| ((n : ℝ) + 1) ^ (2 + ε)) := by
      intro n n' hnn' x
      refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (le_min (abs_nonneg _) (by positivity))
        (min_le_min le_rfl (by
          have : (n : ℝ) ≤ n' := by exact_mod_cast hnn'
          linarith)) (by linarith))
    calc ∫⁻ x in ball 0 (R / 2), ‖f x‖ₑ ^ (2 + ε)
        ≤ ∫⁻ x in ball 0 (R / 2), ⨆ n : ℕ, ENNReal.ofReal (min |f x| ((n : ℝ) + 1) ^ (2 + ε)) := by
          refine lintegral_mono fun x => ?_
          rw [enorm_rpow_eq_ofReal _ (by linarith)]
          refine le_iSup_of_le (Nat.ceil |f x|) (le_of_eq ?_)
          rw [min_eq_left]
          have := Nat.le_ceil |f x|
          linarith
      _ = ⨆ n : ℕ, ∫⁻ x in ball 0 (R / 2), ENNReal.ofReal (min |f x| ((n : ℝ) + 1) ^ (2 + ε)) :=
          lintegral_iSup hmeas hmono
      _ ≤ ENNReal.ofReal (vRr * (C₆' * Ac)) := iSup_le fun n => hmain _ (by positivity)
  -- the normalized norm
  set S : ℝ := nf + nGp with hS
  have hS0 : 0 ≤ S := by positivity
  have hAS : Ac ≤ CA * S ^ (2 + ε) := by
    have hnfS : nf ≤ S := by linarith
    have hsS : nf + nG ≤ S := by linarith
    have h1 : nf ^ 2 * (nf + nG) ^ ε ≤ S ^ (2 + ε) := by
      rw [Real.rpow_add' hS0 (by linarith), Real.rpow_two]
      exact mul_le_mul (pow_le_pow_left₀ hnf0 hnfS 2)
        (Real.rpow_le_rpow (by positivity) hsS hε0.le) (by positivity) (by positivity)
    have h2 : nGp ^ (2 + ε) ≤ S ^ (2 + ε) :=
      Real.rpow_le_rpow hnGp0 (by linarith) (by linarith)
    rw [hAc, hCA]
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ M ^ ε * 128 ^ ξ)
    nlinarith [h3, h2]
  have hvol2 : volume (ball (0 : Vec d) R) =
      ENNReal.ofReal (2 ^ d) * volume (ball (0 : Vec d) (R / 2)) := by
    rw [← volume_ball_mul 0 (by norm_num : (0 : ℝ) < 2) hR2]
    congr 1
    ring_nf
  have hpow : PDE.eLpMeanNormOn (ball 0 (R / 2)) (ENNReal.ofReal (2 + ε)) f ^ (2 + ε) ≤
      ENNReal.ofReal (2 ^ d * C₆' * CA * S ^ (2 + ε)) := by
    rw [eLpMeanNormOn_rpow_eq (by linarith) hfm.aestronglyMeasurable]
    calc (volume (ball (0 : Vec d) (R / 2)))⁻¹ * ∫⁻ x in ball 0 (R / 2), ‖f x‖ₑ ^ (2 + ε)
        ≤ (volume (ball (0 : Vec d) (R / 2)))⁻¹ * ENNReal.ofReal (vRr * (C₆' * Ac)) := by
          gcongr
      _ = ENNReal.ofReal (2 ^ d * (C₆' * Ac)) := by
          rw [ENNReal.ofReal_mul hvRr.le, ← hvR_eq, hvol2,
            ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 ^ d by positivity)]
          calc (volume (ball (0 : Vec d) (R / 2)))⁻¹ * (ENNReal.ofReal (2 ^ d) *
                volume (ball (0 : Vec d) (R / 2)) * ENNReal.ofReal (C₆' * Ac))
              = ENNReal.ofReal (2 ^ d) * ENNReal.ofReal (C₆' * Ac) *
                  ((volume (ball (0 : Vec d) (R / 2)))⁻¹ * volume (ball (0 : Vec d) (R / 2))) := by
                ring
            _ = ENNReal.ofReal (2 ^ d) * ENNReal.ofReal (C₆' * Ac) := by
                rw [ENNReal.inv_mul_cancel (volume_ball_ne_zero' 0 hR2) (volume_ball_ne_top' 0 _),
                  mul_one]
      _ ≤ ENNReal.ofReal (2 ^ d * C₆' * CA * S ^ (2 + ε)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have := mul_le_mul_of_nonneg_left hAS (by positivity : (0 : ℝ) ≤ 2 ^ d * C₆')
          calc 2 ^ d * (C₆' * Ac) = 2 ^ d * C₆' * Ac := by ring
            _ ≤ 2 ^ d * C₆' * (CA * S ^ (2 + ε)) := this
            _ = 2 ^ d * C₆' * CA * S ^ (2 + ε) := by ring
  have hY0 : 0 ≤ 2 ^ d * C₆' * CA := by positivity
  have hroot := ENNReal.rpow_le_rpow hpow (by positivity : (0 : ℝ) ≤ 1 / (2 + ε))
  rw [← ENNReal.rpow_mul, mul_one_div_cancel (by linarith), ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
    Real.mul_rpow hY0 (by positivity), ← Real.rpow_mul hS0, mul_one_div_cancel (by linarith),
    Real.rpow_one] at hroot
  have hYC : (2 ^ d * C₆' * CA) ^ (1 / (2 + ε)) ≤ C₁ := by
    have hY1 : 2 ^ d * C₆' * CA ≤ C₁ := le_max_right _ _
    calc (2 ^ d * C₆' * CA) ^ (1 / (2 + ε)) ≤ C₁ ^ (1 / (2 + ε)) :=
          Real.rpow_le_rpow hY0 hY1 (by positivity)
      _ ≤ C₁ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (le_max_left _ _)
          (by rw [div_le_one (by linarith)]; linarith)
      _ = C₁ := Real.rpow_one _
  have hNGp_g : PDE.eLpMeanNormOn (ball 0 R) (ENNReal.ofReal (2 + ε)) G =
      ENNReal.ofReal e⁻¹ * PDE.eLpMeanNormOn (ball 0 R) (ENNReal.ofReal (2 + ε)) g := by
    rw [hG, eLpMeanNormOn_const_smul _ _ (inv_nonneg.mpr he0.le)]
  have hei : 1 ≤ e⁻¹ := one_le_inv₀ he0 |>.mpr he1
  calc PDE.eLpMeanNormOn (ball 0 (R / 2)) (ENNReal.ofReal (2 + ε)) f
      ≤ ENNReal.ofReal ((2 ^ d * C₆' * CA) ^ (1 / (2 + ε)) * S) := hroot
    _ ≤ ENNReal.ofReal (C₁ * S) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hYC hS0)
    _ = ENNReal.ofReal C₁ * (PDE.eLpMeanNormOn (ball 0 R) 2 f +
          PDE.eLpMeanNormOn (ball 0 R) (ENNReal.ofReal (2 + ε)) G) := by
        rw [hNf_eq, hNGp_eq, ← ENNReal.ofReal_add hnf0 hnGp0, ← ENNReal.ofReal_mul
          (le_max_of_le_left zero_le_one)]
    _ ≤ ENNReal.ofReal C₁ * (ENNReal.ofReal e⁻¹ * PDE.eLpMeanNormOn (ball 0 R) 2 f +
          ENNReal.ofReal e⁻¹ * PDE.eLpMeanNormOn (ball 0 R) (ENNReal.ofReal (2 + ε)) g) := by
        rw [hNGp_g]
        gcongr
        calc PDE.eLpMeanNormOn (ball 0 R) 2 f = 1 * PDE.eLpMeanNormOn (ball 0 R) 2 f :=
              (one_mul _).symm
          _ ≤ _ := by
              gcongr
              rw [← ENNReal.ofReal_one]
              exact ENNReal.ofReal_le_ofReal hei
    _ = ENNReal.ofReal (C₁ * e⁻¹) * (PDE.eLpMeanNormOn (ball 0 R) 2 f +
          PDE.eLpMeanNormOn (ball 0 R) (ENNReal.ofReal (2 + ε)) g) := by
        rw [← mul_add, ← mul_assoc, ENNReal.ofReal_mul (le_max_of_le_left zero_le_one)]

theorem ball_subset_ball_two_mul (x : Vec d) {r : ℝ} (hr : 0 < r) :
    ball x r ⊆ ball x (2 * r) :=
  ball_subset_ball_of_norm (by
    rw [sub_self, show euclideanNorm (0 : Vec d) = 0 by simp [euclideanNorm, euclideanSq, dot]]
    linarith)

/-- **Lemma 7.2** on the balls `B_r(x)` with `r < R/2` and `B_{2r}(x) ⊆ B_R`. For `p ∈ (2, ∞)`,
`q ∈ (p, ∞]` and `A ≥ 1` there are `δ₀ > 0` and `C < ∞` such that, for every `δ ∈ (0, δ₀]` and `R > 0`, if
`f ∈ L²(B_R)`, `g ∈ L^p(B_R)` and every such ball `B_r(x)` carries some
`f_{x,r} ∈ L^q(B_r(x))` with (7.6) and (7.7), then `f ∈ L^p(B_{R/2})` and (7.8) holds:
`‖f‖_{L̲^p(B_{R/2})} ≤ C (‖f‖_{L̲²(B_R)} + ‖g‖_{L̲^p(B_R)})`. -/
theorem lemma_7_2_ball {p A : ℝ} {q : ℝ≥0∞} (hp : 2 < p) (hpq : ENNReal.ofReal p < q)
    (hA : 1 ≤ A) :
    ∃ δ₀ C : ℝ, 0 < δ₀ ∧ 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : ℝ, 0 < R →
      ∀ f g : Vec d → ℝ, MemLp f 2 (volume.restrict (ball 0 R)) →
      MemLp g (ENNReal.ofReal p) (volume.restrict (ball 0 R)) →
      (∀ (x : Vec d) (r : ℝ), 0 < r → 2 * r < R → ball x (2 * r) ⊆ ball 0 R →
        ∃ fxr : Vec d → ℝ, MemLp fxr q (volume.restrict (ball x r)) ∧
          PDE.eLpMeanNormOn (ball x r) q fxr ≤
            ENNReal.ofReal A * PDE.eLpMeanNormOn (ball x (2 * r)) 2 g +
              ENNReal.ofReal A * PDE.eLpMeanNormOn (ball x (2 * r)) 2 f ∧
          PDE.eLpMeanNormOn (ball x r) 2 (f - fxr) ≤
            ENNReal.ofReal A * PDE.eLpMeanNormOn (ball x (2 * r)) 2 g +
              ENNReal.ofReal δ * PDE.eLpMeanNormOn (ball x (2 * r)) 2 f) →
      MemLp f (ENNReal.ofReal p) (volume.restrict (ball 0 (R / 2))) ∧
        PDE.eLpMeanNormOn (ball 0 (R / 2)) (ENNReal.ofReal p) f ≤
          ENNReal.ofReal C * (PDE.eLpMeanNormOn (ball 0 R) 2 f +
            PDE.eLpMeanNormOn (ball 0 R) (ENNReal.ofReal p) g) := by
  obtain ⟨q', hpq', hq'q⟩ : ∃ q' : ℝ, p < q' ∧ ENNReal.ofReal q' ≤ q := by
    by_cases hq : q = ⊤
    · exact ⟨p + 1, by linarith, by rw [hq]; exact le_top⟩
    · refine ⟨q.toReal, ?_, by rw [ENNReal.ofReal_toReal hq]⟩
      exact (ENNReal.ofReal_lt_iff_lt_toReal (by linarith) hq).mp hpq
  obtain ⟨δ₀, C, hδ₀, hC, hmain⟩ := lemma_7_2_measurable (d := d) hp hpq' hA
  refine ⟨δ₀, C, hδ₀, hC, fun δ hδ hδδ₀ R hR f g hf hg hhyp => ?_⟩
  set f' := hf.aestronglyMeasurable.mk f with hf'
  set g' := hg.aestronglyMeasurable.mk g with hg'
  have hff' : f =ᵐ[volume.restrict (ball 0 R)] f' := hf.aestronglyMeasurable.ae_eq_mk
  have hgg' : g =ᵐ[volume.restrict (ball 0 R)] g' := hg.aestronglyMeasurable.ae_eq_mk
  have hF : ∀ {U : Set (Vec d)}, U ⊆ ball 0 R → ∀ s : ℝ≥0∞,
      PDE.eLpMeanNormOn U s f = PDE.eLpMeanNormOn U s f' :=
    fun hU s => eLpMeanNormOn_congr_of_subset hU hff'
  have hGg : ∀ {U : Set (Vec d)}, U ⊆ ball 0 R → ∀ s : ℝ≥0∞,
      PDE.eLpMeanNormOn U s g = PDE.eLpMeanNormOn U s g' :=
    fun hU s => eLpMeanNormOn_congr_of_subset hU hgg'
  have hR2 : 0 < R / 2 := half_pos hR
  have hhalf : ball (0 : Vec d) (R / 2) ⊆ ball 0 R :=
    (ball_subset_ball_two_mul 0 hR2).trans (by rw [show 2 * (R / 2) = R by ring])
  have hhyp' : ∀ (x : Vec d) (r : ℝ), 0 < r → 2 * r < R → ball x (2 * r) ⊆ ball 0 R →
      ∃ h : Vec d → ℝ, Measurable h ∧
        PDE.eLpMeanNormOn (ball x r) (ENNReal.ofReal q') h ≤ ENNReal.ofReal A *
          (PDE.eLpMeanNormOn (ball x (2 * r)) 2 g' + PDE.eLpMeanNormOn (ball x (2 * r)) 2 f') ∧
        PDE.eLpMeanNormOn (ball x r) 2 (f' - h) ≤
          ENNReal.ofReal A * PDE.eLpMeanNormOn (ball x (2 * r)) 2 g' +
            ENNReal.ofReal δ * PDE.eLpMeanNormOn (ball x (2 * r)) 2 f' := by
    intro x r hr hrR hsub
    have hsub1 : ball x r ⊆ ball 0 R := (ball_subset_ball_two_mul x hr).trans hsub
    obtain ⟨fxr, hmem, h1, h2⟩ := hhyp x r hr hrR hsub
    have hfxr : fxr =ᵐ[volume.restrict (ball x r)] hmem.aestronglyMeasurable.mk fxr :=
      hmem.aestronglyMeasurable.ae_eq_mk
    refine ⟨hmem.aestronglyMeasurable.mk fxr,
      hmem.aestronglyMeasurable.stronglyMeasurable_mk.measurable, ?_, ?_⟩
    · have : IsProbabilityMeasure (PDE.normalizedVolumeOn (ball x r)) :=
        PDE.isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top (volume_ball_pos x hr)
          (volume_ball_lt_top x r)
      rw [← eLpMeanNormOn_congr_of_subset subset_rfl hfxr, ← hGg hsub, ← hF hsub, mul_add]
      exact (eLpNorm_le_eLpNorm_of_exponent_le hq'q).trans h1
    · have hae : f' - hmem.aestronglyMeasurable.mk fxr =ᵐ[volume.restrict (ball x r)]
          f - fxr := by
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub1 hff', hfxr] with y hy1 hy2
        simp only [Pi.sub_apply, hy1, hy2]
      rw [eLpMeanNormOn_congr_of_subset subset_rfl hae, ← hGg hsub, ← hF hsub]
      exact h2
  have hmain' := hmain δ hδ hδδ₀ R hR f' g'
    hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
    hg.aestronglyMeasurable.stronglyMeasurable_mk.measurable (hf.ae_eq hff') (hg.ae_eq hgg')
    hhyp'
  have hbound : PDE.eLpMeanNormOn (ball 0 (R / 2)) (ENNReal.ofReal p) f ≤
      ENNReal.ofReal C * (PDE.eLpMeanNormOn (ball 0 R) 2 f +
        PDE.eLpMeanNormOn (ball 0 R) (ENNReal.ofReal p) g) := by
    rw [hF hhalf, hF subset_rfl, hGg subset_rfl]
    exact hmain'
  refine ⟨?_, hbound⟩
  have hfin : PDE.eLpMeanNormOn (ball 0 (R / 2)) (ENNReal.ofReal p) f ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr
      ⟨eLpMeanNormOn_ne_top (volume_ball_ne_zero' 0 hR) hf,
        eLpMeanNormOn_ne_top (volume_ball_ne_zero' 0 hR) hg⟩)) hbound
  rw [PDE.eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn (volume_ball_lt_top 0 _)] at hfin
  exact ENNReal.lt_top_of_mul_ne_top_right hfin
    (ENNReal.rpow_pos (ENNReal.inv_pos.2 (volume_ball_ne_top' 0 _))
      (ENNReal.inv_ne_top.2 (volume_ball_ne_zero' 0 hR2))).ne'

/-- **Lemma 7.2** under the hypotheses of the book's statement: for `p ∈ (2, ∞)`, `q ∈ (p, ∞]`
and `A ≥ 1` there are `δ₀ > 0` and `C < ∞` such that, for every `δ ∈ (0, δ₀]`, if `f ∈ L²(B_1)`,
`g ∈ L^p(B_1)` and every `x ∈ B_{1/2}` and `r ∈ (0, 1/4)` carry some `f_{x,r} ∈ L^q(B_r(x))` with
(7.6) and (7.7), then `f ∈ L^p(B_{1/4})` and
`‖f‖_{L̲^p(B_{1/4})} ≤ C (‖f‖_{L̲²(B_{1/2})} + ‖g‖_{L̲^p(B_{1/2})})`. The book concludes on
`B_{1/2}`; its proof uses the hypotheses at centers outside `B_{1/2}` (see the module docstring),
and with the hypotheses at all centers the conclusion on `B_{1/2}` is `lemma_7_2_ball`. -/
theorem lemma_7_2 {p A : ℝ} {q : ℝ≥0∞} (hp : 2 < p) (hpq : ENNReal.ofReal p < q)
    (hA : 1 ≤ A) :
    ∃ δ₀ C : ℝ, 0 < δ₀ ∧ 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ f g : Vec d → ℝ, MemLp f 2 (volume.restrict (ball 0 1)) →
      MemLp g (ENNReal.ofReal p) (volume.restrict (ball 0 1)) →
      (∀ x ∈ ball (0 : Vec d) (1 / 2), ∀ r ∈ Ioo (0 : ℝ) (1 / 4),
        ∃ fxr : Vec d → ℝ, MemLp fxr q (volume.restrict (ball x r)) ∧
          PDE.eLpMeanNormOn (ball x r) q fxr ≤
            ENNReal.ofReal A * PDE.eLpMeanNormOn (ball x (2 * r)) 2 g +
              ENNReal.ofReal A * PDE.eLpMeanNormOn (ball x (2 * r)) 2 f ∧
          PDE.eLpMeanNormOn (ball x r) 2 (f - fxr) ≤
            ENNReal.ofReal A * PDE.eLpMeanNormOn (ball x (2 * r)) 2 g +
              ENNReal.ofReal δ * PDE.eLpMeanNormOn (ball x (2 * r)) 2 f) →
      MemLp f (ENNReal.ofReal p) (volume.restrict (ball 0 (1 / 4))) ∧
        PDE.eLpMeanNormOn (ball 0 (1 / 4)) (ENNReal.ofReal p) f ≤
          ENNReal.ofReal C * (PDE.eLpMeanNormOn (ball 0 (1 / 2)) 2 f +
            PDE.eLpMeanNormOn (ball 0 (1 / 2)) (ENNReal.ofReal p) g) := by
  obtain ⟨δ₀, C, hδ₀, hC, hmain⟩ := lemma_7_2_ball (d := d) hp hpq hA
  refine ⟨δ₀, C, hδ₀, hC, fun δ hδ hδδ₀ f g hf hg hhyp => ?_⟩
  have hsub : ball (0 : Vec d) (1 / 2) ⊆ ball 0 1 :=
    (ball_subset_ball_two_mul 0 (by norm_num : (0 : ℝ) < 1 / 2)).trans
      (by rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num])
  have h := hmain δ hδ hδδ₀ (1 / 2) (by norm_num) f g (hf.mono_measure
    (Measure.restrict_mono hsub le_rfl)) (hg.mono_measure (Measure.restrict_mono hsub le_rfl))
    (fun x r hr hrR hball => by
      have hx : x ∈ ball (0 : Vec d) (1 / 2) := hball (mem_ball_self x (by linarith))
      exact hhyp x hx r ⟨hr, by linarith⟩)
  rw [show (1 : ℝ) / 2 / 2 = 1 / 4 by norm_num] at h
  exact h

end QSH
