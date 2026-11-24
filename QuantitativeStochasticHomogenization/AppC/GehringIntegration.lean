import QuantitativeStochasticHomogenization.AppC.GehringLevelSet
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integration of the level set estimate in the proof of Gehring's lemma

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma C.4: the layer cake formula turns the level set estimate (C.10) into an
inequality between the truncated integrals `Ψ(σ) = ∫_{B_{σR}} f² (|f| ∧ m)^ε`:
`Ψ(σ) ≤ λ₀^ε ∫_{B_{σR}} f² + 8^d (8K)^{2+ε} ε/(2 + ε - q) Ψ(τ) + 8^d (8K)^{2+ε} ∫_{B_{τR}} |g|^{2+ε}`.

As in the standard proofs (and correcting the display after (C.10) in the book, where the
truncation is applied to `‖f_m‖_{L^{2+ε}}` instead of `∫ f² f_m^ε`), the truncated quantity is
weighted by `f²`; the level set integral of `|f|^q` is then bounded through the pointwise
inequality `|f|^q ((8K|f|) ∧ m)^{2+ε-q} ≤ (8K)^{2+ε-q} f² (|f| ∧ m)^ε`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The layer cake formula for a weighted integral over a set:
`∫_B w φ^p = p ∫_0^∞ (∫_{B ∩ {φ > t}} w) t^{p-1} dt`. -/
theorem setLIntegral_mul_ofReal_rpow_eq {B : Set (Vec d)} {w : Vec d → ℝ≥0∞}
    (hw : Measurable w) {φ : Vec d → ℝ} (hφ : Measurable φ) (hφ0 : ∀ x, 0 ≤ φ x) {p : ℝ}
    (hp : 0 < p) :
    ∫⁻ x in B, w x * ENNReal.ofReal (φ x ^ p) =
      ENNReal.ofReal p * ∫⁻ t in Ioi 0, (∫⁻ x in B ∩ {x | t < φ x}, w x) *
        ENNReal.ofReal (t ^ (p - 1)) := by
  have h := lintegral_rpow_eq_lintegral_meas_lt_mul ((volume.restrict B).withDensity w)
    (Eventually.of_forall hφ0) hφ.aemeasurable hp
  have hmeas : Measurable fun x => ENNReal.ofReal (φ x ^ p) :=
    ENNReal.measurable_ofReal.comp (hφ.pow_const p)
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hmeas] at h
  have hset : ∀ t : ℝ, (volume.restrict B).withDensity w {a | t < φ a} =
      ∫⁻ x in B ∩ {x | t < φ x}, w x := by
    intro t
    rw [withDensity_apply _ (measurableSet_lt measurable_const hφ),
      Measure.restrict_restrict (measurableSet_lt measurable_const hφ), inter_comm]
  simp_rw [hset, Pi.mul_apply] at h
  exact h

theorem ofReal_mul_lintegral_Ioc_rpow {ε L : ℝ} (hε : 0 < ε) (hL : 0 ≤ L) :
    ENNReal.ofReal ε * ∫⁻ t in Ioc 0 L, ENNReal.ofReal (t ^ (ε - 1)) = ENNReal.ofReal (L ^ ε) := by
  have hint : IntegrableOn (fun t : ℝ => t ^ (ε - 1)) (Ioc 0 L) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < ε - 1)).1
  rw [← ofReal_integral_eq_lintegral_ofReal hint (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact Real.rpow_nonneg ht.1.le _),
    ← intervalIntegral.integral_of_le hL, integral_rpow (Or.inl (by linarith)), sub_add_cancel,
    Real.zero_rpow hε.ne', sub_zero, ← ENNReal.ofReal_mul hε.le]
  congr 1
  field_simp

theorem measurable_setLIntegral_levelSet {B : Set (Vec d)} {w : Vec d → ℝ≥0∞}
    {φ : Vec d → ℝ} :
    Measurable fun t : ℝ => ∫⁻ x in B ∩ {x | t < φ x}, w x := by
  refine Antitone.measurable fun s t hst => lintegral_mono_set ?_
  intro x ⟨hxB, hx⟩
  exact ⟨hxB, lt_of_le_of_lt hst hx⟩

/-- The pointwise inequality `a^q ((8K a) ∧ m)^{2+ε-q} ≤ (8K)^{2+ε-q} a² (a ∧ m)^ε`. -/
theorem rpow_mul_min_rpow_le {a K m q ε : ℝ} (ha : 0 ≤ a) (hK : 1 ≤ 8 * K) (hm : 0 ≤ m)
    (hq : q < 2) (hε : 0 < ε) :
    a ^ q * min (8 * K * a) m ^ (2 + ε - q) ≤
      (8 * K) ^ (2 + ε - q) * (a ^ (2 : ℝ) * min a m ^ ε) := by
  have hp : 0 < 2 + ε - q := by linarith
  have hmin0 : 0 ≤ min a m := le_min ha hm
  have hminK : min (8 * K * a) m ≤ 8 * K * min a m := by
    rcases le_total a m with ham | ham
    · rw [min_eq_left ham]
      exact min_le_left _ _
    · rw [min_eq_right ham]
      calc min (8 * K * a) m ≤ m := min_le_right _ _
        _ ≤ 8 * K * m := le_mul_of_one_le_left hm hK
  have h1 : min (8 * K * a) m ^ (2 + ε - q) ≤ (8 * K) ^ (2 + ε - q) * min a m ^ (2 + ε - q) := by
    rw [← Real.mul_rpow (by linarith) hmin0]
    exact Real.rpow_le_rpow (le_min (by positivity) hm) hminK hp.le
  have h2 : min a m ^ (2 + ε - q) = min a m ^ (2 - q) * min a m ^ ε := by
    rw [← Real.rpow_add' hmin0 (by linarith)]
    ring_nf
  have h3 : min a m ^ (2 - q) ≤ a ^ (2 - q) :=
    Real.rpow_le_rpow hmin0 (min_le_left _ _) (by linarith)
  have h4 : a ^ q * a ^ (2 - q) = a ^ (2 : ℝ) := by
    rw [← Real.rpow_add' ha (by norm_num)]
    ring_nf
  have hq0 : 0 ≤ a ^ q := Real.rpow_nonneg ha _
  calc a ^ q * min (8 * K * a) m ^ (2 + ε - q)
      ≤ a ^ q * ((8 * K) ^ (2 + ε - q) * min a m ^ (2 + ε - q)) :=
        mul_le_mul_of_nonneg_left h1 hq0
    _ = (8 * K) ^ (2 + ε - q) * (a ^ q * min a m ^ (2 - q) * min a m ^ ε) := by
        rw [h2]; ring
    _ ≤ (8 * K) ^ (2 + ε - q) * (a ^ q * a ^ (2 - q) * min a m ^ ε) := by
        gcongr
    _ = (8 * K) ^ (2 + ε - q) * (a ^ (2 : ℝ) * min a m ^ ε) := by rw [h4]

theorem enorm_rpow_eq_ofReal (x : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    ‖x‖ₑ ^ s = ENNReal.ofReal (|x| ^ s) := by
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hs]

/-- The `f`-part of the integrated level set estimate. -/
theorem gehring_fterm {B : Set (Vec d)} {K q ε m c : ℝ} (hK : 1 ≤ K) (hq0 : 0 ≤ q) (hq : q < 2)
    (hε : 0 < ε)
    (hm : 0 ≤ m) (hc : 0 ≤ c) {f : Vec d → ℝ} (hfm : Measurable f) :
    ENNReal.ofReal ε * ∫⁻ t in Ioi 0, ENNReal.ofReal c *
        ((∫⁻ x in B ∩ {x | t < min (8 * K * |f x|) m}, ‖f x‖ₑ ^ q) *
          ENNReal.ofReal (t ^ (2 + ε - q - 1))) ≤
      ENNReal.ofReal (ε / (2 + ε - q) * (c * (8 * K) ^ (2 + ε - q))) *
        ∫⁻ x in B, ‖f x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (min |f x| m ^ ε) := by
  have hp : 0 < 2 + ε - q := by linarith
  have hφm : Measurable fun x => min (8 * K * |f x|) m :=
    (measurable_const.mul hfm.abs).min measurable_const
  have hlc := setLIntegral_mul_ofReal_rpow_eq (B := B) (hfm.enorm.pow_const q) hφm
    (fun x => le_min (by have := abs_nonneg (f x); positivity) hm) hp
  have hmeasT : Measurable fun t : ℝ =>
      (∫⁻ x in B ∩ {x | t < min (8 * K * |f x|) m}, ‖f x‖ₑ ^ q) *
        ENNReal.ofReal (t ^ (2 + ε - q - 1)) :=
    measurable_setLIntegral_levelSet.mul (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))
  rw [lintegral_const_mul _ hmeasT]
  have hcoef : ENNReal.ofReal ε * ENNReal.ofReal c =
      ENNReal.ofReal (ε / (2 + ε - q) * c) * ENNReal.ofReal (2 + ε - q) := by
    rw [← ENNReal.ofReal_mul hε.le, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  rw [← mul_assoc, hcoef, mul_assoc, ← hlc]
  have hpt : ∀ x, ‖f x‖ₑ ^ q * ENNReal.ofReal (min (8 * K * |f x|) m ^ (2 + ε - q)) ≤
      ENNReal.ofReal ((8 * K) ^ (2 + ε - q)) *
        (‖f x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (min |f x| m ^ ε)) := by
    intro x
    rw [enorm_rpow_eq_ofReal _ hq0, enorm_rpow_eq_ofReal _ (by norm_num),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal
      (rpow_mul_min_rpow_le (abs_nonneg _) (by linarith) hm hq hε)
  calc ENNReal.ofReal (ε / (2 + ε - q) * c) *
        ∫⁻ x in B, ‖f x‖ₑ ^ q * ENNReal.ofReal (min (8 * K * |f x|) m ^ (2 + ε - q))
      ≤ ENNReal.ofReal (ε / (2 + ε - q) * c) * ∫⁻ x in B, ENNReal.ofReal ((8 * K) ^ (2 + ε - q)) *
          (‖f x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (min |f x| m ^ ε)) :=
        mul_le_mul_of_nonneg_left (lintegral_mono fun x => hpt x) bot_le
    _ = ENNReal.ofReal (ε / (2 + ε - q) * (c * (8 * K) ^ (2 + ε - q))) *
          ∫⁻ x in B, ‖f x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (min |f x| m ^ ε) := by
        have hmeas : Measurable fun x => ‖f x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (min |f x| m ^ ε) :=
          (hfm.enorm.pow_const _).mul
            (ENNReal.measurable_ofReal.comp ((hfm.abs.min measurable_const).pow_const _))
        rw [lintegral_const_mul _ hmeas, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

/-- The `g`-part of the integrated level set estimate. -/
theorem gehring_gterm {B : Set (Vec d)} {K ε c : ℝ} (hK : 1 ≤ K) (hε : 0 < ε) (hc : 0 ≤ c)
    {g : Vec d → ℝ} (hgm : Measurable g) :
    ENNReal.ofReal ε * ∫⁻ t in Ioi 0, ENNReal.ofReal c *
        ((∫⁻ x in B ∩ {x | t < 8 * K * |g x|}, ‖g x‖ₑ ^ (2 : ℝ)) *
          ENNReal.ofReal (t ^ (ε - 1))) ≤
      ENNReal.ofReal (c * (8 * K) ^ ε) * ∫⁻ x in B, ‖g x‖ₑ ^ (2 + ε) := by
  have hφm : Measurable fun x => 8 * K * |g x| := measurable_const.mul hgm.abs
  have hlc := setLIntegral_mul_ofReal_rpow_eq (B := B) (hgm.enorm.pow_const (2 : ℝ)) hφm
    (fun x => by have := abs_nonneg (g x); positivity) hε
  have hmeasT : Measurable fun t : ℝ =>
      (∫⁻ x in B ∩ {x | t < 8 * K * |g x|}, ‖g x‖ₑ ^ (2 : ℝ)) * ENNReal.ofReal (t ^ (ε - 1)) :=
    measurable_setLIntegral_levelSet.mul (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))
  rw [lintegral_const_mul _ hmeasT, mul_left_comm, ← hlc]
  have hpt : ∀ x, ‖g x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal ((8 * K * |g x|) ^ ε) ≤
      ENNReal.ofReal ((8 * K) ^ ε) * ‖g x‖ₑ ^ (2 + ε) := by
    intro x
    rw [enorm_rpow_eq_ofReal _ (by norm_num), enorm_rpow_eq_ofReal _ (by linarith),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [Real.mul_rpow (by linarith) (abs_nonneg _), Real.rpow_add' (abs_nonneg _) (by linarith)]
    ring
  calc ENNReal.ofReal c * ∫⁻ x in B, ‖g x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal ((8 * K * |g x|) ^ ε)
      ≤ ENNReal.ofReal c * ∫⁻ x in B, ENNReal.ofReal ((8 * K) ^ ε) * ‖g x‖ₑ ^ (2 + ε) :=
        mul_le_mul_of_nonneg_left (lintegral_mono fun x => hpt x) bot_le
    _ = ENNReal.ofReal (c * (8 * K) ^ ε) * ∫⁻ x in B, ‖g x‖ₑ ^ (2 + ε) := by
        have hmeas : Measurable fun x => ‖g x‖ₑ ^ (2 + ε) := hgm.enorm.pow_const _
        rw [lintegral_const_mul _ hmeas, ← mul_assoc,
          ← ENNReal.ofReal_mul hc]

theorem ofReal_mul_add_mul_ofReal {a b b' c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hb' : 0 ≤ b')
    (X Y : ℝ≥0∞) :
    ENNReal.ofReal a * (ENNReal.ofReal b * X + ENNReal.ofReal b' * Y) * ENNReal.ofReal c =
      ENNReal.ofReal (a * b * c) * X + ENNReal.ofReal (a * b' * c) * Y := by
  rw [ENNReal.ofReal_mul (mul_nonneg ha hb), ENNReal.ofReal_mul ha,
    ENNReal.ofReal_mul (mul_nonneg ha hb'), ENNReal.ofReal_mul ha]
  ring

/-- **The integrated level set estimate.** With `Ψ(σ) = ∫_{B_{σR}} f² (|f| ∧ m)^ε` and
`λ₀ = (160/(τ - σ))^{d/2} (‖f‖_{L̲²(B_R)} + ‖g‖_{L̲²(B_R)})`,
`Ψ(σ) ≤ λ₀^ε ∫_{B_{σR}} f² + 8^d (8K)^{2+ε} ε/(2+ε-q) Ψ(τ) + 8^d (8K)^{2+ε} ∫_{B_{τR}} |g|^{2+ε}`. -/
theorem gehring_step {R σ τ K q ε m : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hστ : σ < τ) (hτ : τ ≤ 1)
    (hK : 1 ≤ K) (hq1 : 1 ≤ q) (hq2 : q < 2) (hε : 0 < ε) (hm : 0 < m) {f g : Vec d → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (hfint : IntegrableOn f (ball 0 R))
    (hRH : ∀ (z : Vec d) (r : ℝ), 0 < r → ball z r ⊆ ball 0 R →
      PDE.eLpMeanNormOn (ball z (r / 2)) 2 f ≤ ENNReal.ofReal K *
        (PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal q) f + PDE.eLpMeanNormOn (ball z r) 2 g))
    (hfin : ENNReal.ofReal ((160 / (τ - σ)) ^ ((d : ℝ) / 2)) *
        (PDE.eLpMeanNormOn (ball 0 R) 2 f + PDE.eLpMeanNormOn (ball 0 R) 2 g) ≠ ⊤) :
    ∫⁻ x in ball 0 (σ * R), ‖f x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (min |f x| m ^ ε) ≤
      (∫⁻ x in ball 0 (σ * R), ‖f x‖ₑ ^ (2 : ℝ)) *
          ENNReal.ofReal ((ENNReal.ofReal ((160 / (τ - σ)) ^ ((d : ℝ) / 2)) *
            (PDE.eLpMeanNormOn (ball 0 R) 2 f + PDE.eLpMeanNormOn (ball 0 R) 2 g)).toReal ^ ε) +
        ENNReal.ofReal (ε / (2 + ε - q) * (8 ^ d * (8 * K) ^ q * (8 * K) ^ (2 + ε - q))) *
          (∫⁻ x in ball 0 (τ * R), ‖f x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (min |f x| m ^ ε)) +
        ENNReal.ofReal (8 ^ d * (8 * K) ^ 2 * (8 * K) ^ ε) *
          ∫⁻ x in ball 0 (τ * R), ‖g x‖ₑ ^ (2 + ε) := by
  set lam₀ := ENNReal.ofReal ((160 / (τ - σ)) ^ ((d : ℝ) / 2)) *
    (PDE.eLpMeanNormOn (ball 0 R) 2 f + PDE.eLpMeanNormOn (ball 0 R) 2 g) with hlam₀
  set L₀ := lam₀.toReal with hL₀def
  have hL₀ : 0 ≤ L₀ := ENNReal.toReal_nonneg
  have hlam₀eq : lam₀ = ENNReal.ofReal L₀ := (ENNReal.ofReal_toReal hfin).symm
  have h8K : 0 < 8 * K := by linarith
  set V := ∫⁻ x in ball 0 (σ * R), ‖f x‖ₑ ^ (2 : ℝ) with hV
  have hφm : Measurable fun x => min |f x| m := hfm.abs.min measurable_const
  rw [setLIntegral_mul_ofReal_rpow_eq (hfm.enorm.pow_const (2 : ℝ)) hφm
    (fun x => le_min (abs_nonneg _) hm.le) hε, ← Ioc_union_Ioi_eq_Ioi hL₀,
    lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same, mul_add]
  -- the levels below `λ₀`
  have hP1 : ENNReal.ofReal ε * ∫⁻ t in Ioc 0 L₀,
      (∫⁻ x in ball 0 (σ * R) ∩ {x | t < min |f x| m}, ‖f x‖ₑ ^ (2 : ℝ)) *
        ENNReal.ofReal (t ^ (ε - 1)) ≤ V * ENNReal.ofReal (L₀ ^ ε) := by
    calc ENNReal.ofReal ε * ∫⁻ t in Ioc 0 L₀,
          (∫⁻ x in ball 0 (σ * R) ∩ {x | t < min |f x| m}, ‖f x‖ₑ ^ (2 : ℝ)) *
            ENNReal.ofReal (t ^ (ε - 1))
        ≤ ENNReal.ofReal ε * ∫⁻ t in Ioc 0 L₀, V * ENNReal.ofReal (t ^ (ε - 1)) := by
          gcongr with t
          exact lintegral_mono_set inter_subset_left
      _ = V * (ENNReal.ofReal ε * ∫⁻ t in Ioc 0 L₀, ENNReal.ofReal (t ^ (ε - 1))) := by
          have hmeas : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (ε - 1)) :=
            ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
          rw [lintegral_const_mul _ hmeas]
          ring
      _ = V * ENNReal.ofReal (L₀ ^ ε) := by rw [ofReal_mul_lintegral_Ioc_rpow hε hL₀]
  -- the levels above `λ₀`
  set c₂ : ℝ := 8 ^ d * (8 * K) ^ q with hc₂
  set c₃ : ℝ := 8 ^ d * (8 * K) ^ 2 with hc₃
  have hpt : ∀ t ∈ Ioi L₀,
      (∫⁻ x in ball 0 (σ * R) ∩ {x | t < min |f x| m}, ‖f x‖ₑ ^ (2 : ℝ)) *
        ENNReal.ofReal (t ^ (ε - 1)) ≤
      ENNReal.ofReal c₂ * ((∫⁻ x in ball 0 (τ * R) ∩ {x | t < min (8 * K * |f x|) m},
          ‖f x‖ₑ ^ q) * ENNReal.ofReal (t ^ (2 + ε - q - 1))) +
        ENNReal.ofReal c₃ * ((∫⁻ x in ball 0 (τ * R) ∩ {x | t < 8 * K * |g x|},
          ‖g x‖ₑ ^ (2 : ℝ)) * ENNReal.ofReal (t ^ (ε - 1))) := by
    intro t ht
    have htpos : 0 < t := lt_of_le_of_lt hL₀ ht
    by_cases htm : t < m
    · have hset : {x | t < min |f x| m} = {x | t < |f x|} := by
        ext x
        simp only [mem_ofPred_eq, lt_min_iff]
        exact ⟨fun h => h.1, fun h => ⟨h, htm⟩⟩
      have hset2 : {x | t / (8 * K) < |f x|} = {x | t < min (8 * K * |f x|) m} := by
        ext x
        simp only [mem_ofPred_eq, lt_min_iff, div_lt_iff₀ h8K]
        exact ⟨fun h => ⟨by linarith, htm⟩, fun h => by linarith [h.1]⟩
      have hset3 : {x | t / (8 * K) < |g x|} = {x | t < 8 * K * |g x|} := by
        ext x
        simp only [mem_ofPred_eq, div_lt_iff₀ h8K]
        exact ⟨fun h => by linarith, fun h => by linarith⟩
      have h10 := levelSet_estimate hR hσ hστ hτ hK hq1 htpos hfm hgm hfint hRH (by
        rw [← hlam₀, hlam₀eq]
        exact (ENNReal.ofReal_lt_ofReal_iff htpos).mpr ht)
      rw [hset2, hset3] at h10
      rw [hset]
      set X := ∫⁻ x in ball 0 (τ * R) ∩ {x | t < min (8 * K * |f x|) m}, ‖f x‖ₑ ^ q
      set Y := ∫⁻ x in ball 0 (τ * R) ∩ {x | t < 8 * K * |g x|}, ‖g x‖ₑ ^ (2 : ℝ)
      have e1 : 8 ^ d * t ^ 2 * (8 * K / t) ^ q * t ^ (ε - 1) = c₂ * t ^ (2 + ε - q - 1) := by
        have h1 : t ^ (2 + ε - q - 1) = t ^ (2 : ℝ) * t ^ (ε - 1) * (t ^ q)⁻¹ := by
          rw [show (2 : ℝ) + ε - q - 1 = 2 + (ε - 1) + (-q) by ring, Real.rpow_add htpos,
            Real.rpow_add htpos, Real.rpow_neg htpos.le]
        rw [h1, hc₂, Real.div_rpow h8K.le htpos.le, Real.rpow_two]
        have : t ^ q ≠ 0 := (Real.rpow_pos_of_pos htpos q).ne'
        field_simp
      have e2 : 8 ^ d * t ^ 2 * (8 * K / t) ^ (2 : ℝ) * t ^ (ε - 1) = c₃ * t ^ (ε - 1) := by
        rw [hc₃, Real.rpow_two, div_pow]
        field_simp
      calc (∫⁻ x in ball 0 (σ * R) ∩ {x | t < |f x|}, ‖f x‖ₑ ^ (2 : ℝ)) *
            ENNReal.ofReal (t ^ (ε - 1))
          ≤ (ENNReal.ofReal (8 ^ d * t ^ 2) * (ENNReal.ofReal ((8 * K / t) ^ q) * X +
              ENNReal.ofReal ((8 * K / t) ^ (2 : ℝ)) * Y)) * ENNReal.ofReal (t ^ (ε - 1)) := by
            gcongr
        _ = ENNReal.ofReal (8 ^ d * t ^ 2 * (8 * K / t) ^ q * t ^ (ε - 1)) * X +
              ENNReal.ofReal (8 ^ d * t ^ 2 * (8 * K / t) ^ (2 : ℝ) * t ^ (ε - 1)) * Y :=
            ofReal_mul_add_mul_ofReal (by positivity) (by positivity) (by positivity) X Y
        _ = ENNReal.ofReal c₂ * (X * ENNReal.ofReal (t ^ (2 + ε - q - 1))) +
              ENNReal.ofReal c₃ * (Y * ENNReal.ofReal (t ^ (ε - 1))) := by
            rw [e1, e2, ENNReal.ofReal_mul (show 0 ≤ c₂ by positivity),
              ENNReal.ofReal_mul (show 0 ≤ c₃ by positivity)]
            ring
    · have hempty : ball 0 (σ * R) ∩ {x | t < min |f x| m} = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        intro _ h
        exact htm (h.trans_le (min_le_right _ _))
      rw [hempty, Measure.restrict_empty, lintegral_zero_measure, zero_mul]
      exact bot_le
  have hmeas2 : Measurable fun t : ℝ => ENNReal.ofReal c₂ *
      ((∫⁻ x in ball 0 (τ * R) ∩ {x | t < min (8 * K * |f x|) m}, ‖f x‖ₑ ^ q) *
        ENNReal.ofReal (t ^ (2 + ε - q - 1))) :=
    measurable_const.mul (measurable_setLIntegral_levelSet.mul
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)))
  have hP2 : ∫⁻ t in Ioi L₀,
      (∫⁻ x in ball 0 (σ * R) ∩ {x | t < min |f x| m}, ‖f x‖ₑ ^ (2 : ℝ)) *
        ENNReal.ofReal (t ^ (ε - 1)) ≤
      (∫⁻ t in Ioi 0, ENNReal.ofReal c₂ *
          ((∫⁻ x in ball 0 (τ * R) ∩ {x | t < min (8 * K * |f x|) m}, ‖f x‖ₑ ^ q) *
            ENNReal.ofReal (t ^ (2 + ε - q - 1)))) +
        ∫⁻ t in Ioi 0, ENNReal.ofReal c₃ *
          ((∫⁻ x in ball 0 (τ * R) ∩ {x | t < 8 * K * |g x|}, ‖g x‖ₑ ^ (2 : ℝ)) *
            ENNReal.ofReal (t ^ (ε - 1))) := by
    rw [← lintegral_add_left hmeas2]
    exact (setLIntegral_mono' measurableSet_Ioi hpt).trans
      (lintegral_mono_set (Ioi_subset_Ioi hL₀))
  have hf2 := gehring_fterm (B := ball 0 (τ * R)) (m := m) (c := c₂) hK (by linarith) hq2 hε
    hm.le (by positivity) hfm
  have hg2 := gehring_gterm (B := ball 0 (τ * R)) (c := c₃) hK hε (by positivity) hgm
  have hfin2 : ENNReal.ofReal ε * ∫⁻ t in Ioi L₀,
      (∫⁻ x in ball 0 (σ * R) ∩ {x | t < min |f x| m}, ‖f x‖ₑ ^ (2 : ℝ)) *
        ENNReal.ofReal (t ^ (ε - 1)) ≤
      ENNReal.ofReal ε * (∫⁻ t in Ioi 0, ENNReal.ofReal c₂ *
          ((∫⁻ x in ball 0 (τ * R) ∩ {x | t < min (8 * K * |f x|) m}, ‖f x‖ₑ ^ q) *
            ENNReal.ofReal (t ^ (2 + ε - q - 1)))) +
        ENNReal.ofReal ε * ∫⁻ t in Ioi 0, ENNReal.ofReal c₃ *
          ((∫⁻ x in ball 0 (τ * R) ∩ {x | t < 8 * K * |g x|}, ‖g x‖ₑ ^ (2 : ℝ)) *
            ENNReal.ofReal (t ^ (ε - 1))) := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left hP2 bot_le
  calc _ ≤ V * ENNReal.ofReal (L₀ ^ ε) + (ENNReal.ofReal ε * (∫⁻ t in Ioi 0, ENNReal.ofReal c₂ *
          ((∫⁻ x in ball 0 (τ * R) ∩ {x | t < min (8 * K * |f x|) m}, ‖f x‖ₑ ^ q) *
            ENNReal.ofReal (t ^ (2 + ε - q - 1)))) +
        ENNReal.ofReal ε * ∫⁻ t in Ioi 0, ENNReal.ofReal c₃ *
          ((∫⁻ x in ball 0 (τ * R) ∩ {x | t < 8 * K * |g x|}, ‖g x‖ₑ ^ (2 : ℝ)) *
            ENNReal.ofReal (t ^ (ε - 1)))) := add_le_add hP1 hfin2
    _ ≤ V * ENNReal.ofReal (L₀ ^ ε) +
        (ENNReal.ofReal (ε / (2 + ε - q) * (c₂ * (8 * K) ^ (2 + ε - q))) *
            (∫⁻ x in ball 0 (τ * R), ‖f x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (min |f x| m ^ ε)) +
          ENNReal.ofReal (c₃ * (8 * K) ^ ε) * ∫⁻ x in ball 0 (τ * R), ‖g x‖ₑ ^ (2 + ε)) :=
        add_le_add le_rfl (add_le_add hf2 hg2)
    _ = _ := by rw [add_assoc]

end QSH
