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
statement proved here (`lemma_7_2_ball`) takes them on every ball `B_r(x)` with `B_{2r}(x) ⊆ B_R`,
for every radius `R > 0`, with the conclusion on `B_{R/2}`; this is the form used in the proof
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
    (happrox : ∀ (z : Vec d) (ρ : ℝ), 0 < ρ → ball z (2 * ρ) ⊆ ball 0 R →
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
        simp only [mem_setOf_eq, lt_min_iff, hMl]
        exact ⟨fun h => h.1, fun h => ⟨h, hτm⟩⟩
      have hset2 : {x | l / 4 < |f x|} = {x | τ < min (4 * M * |f x|) m} := by
        ext x
        simp only [mem_setOf_eq, lt_min_iff, hl, div_div, div_lt_iff₀ (by positivity : 0 < M * 4)]
        constructor
        · intro h
          exact ⟨by linarith, hτm⟩
        · intro h
          linarith [h.1]
      have hset3 : {x | l / 4 < |G x|} = {x | τ < 4 * M * |G x|} := by
        ext x
        simp only [mem_setOf_eq, hl, div_div, div_lt_iff₀ (by positivity : 0 < M * 4)]
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
        simp only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
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

end QSH
