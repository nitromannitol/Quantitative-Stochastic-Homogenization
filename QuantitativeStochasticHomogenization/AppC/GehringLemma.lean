import QuantitativeStochasticHomogenization.AppC.GehringIntegration
import QuantitativeStochasticHomogenization.AppC.IterationLemma

/-!
# Gehring's lemma

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix C, Lemma C.4: fix `p ∈ (2, ∞)`, `q ∈ (1, 2)`, `K ≥ 1` and `R > 0`. If `f ∈ L²(B_R)`,
`g ∈ L^p(B_R)` and
`‖f‖_{L̲²(B_{r/2}(z))} ≤ K (‖f‖_{L̲^q(B_r(z))} + ‖g‖_{L̲²(B_r(z))})` whenever `B_r(z) ⊆ B_R`, then
`‖f‖_{L̲^{(2+δ)∧p}(B_{R/2})} ≤ C (‖f‖_{L̲²(B_R)} + ‖g‖_{L̲^{(2+δ)∧p}(B_R)})` with `δ(q, K, d) ∈ (0, 1)`
and `C(q, K, d) < ∞`.

The proof is the book's. With `ε = δ ∧ (p - 2)`, the integrated level set estimate
(`gehring_step`) gives, for `ρ(s) = |B_R|^{-1} ∫_{B_{sR}} f² (|f| ∧ m)^ε` and `1/2 ≤ s < t < 1`,
`ρ(s) ≤ ρ(t)/2 + (t - s)^{-dε/2} A` with `A = 160^{dε/2} ‖f‖²_{L̲²(B_R)} (‖f‖_{L̲²} + ‖g‖_{L̲²})^ε
  + 8^d (8K)^3 ‖g‖^{2+ε}_{L̲^{2+ε}(B_R)}`, because `δ = (1/2) ∧ (2 - q)/(2 · 8^d (8K)^3)` makes the
factor of `ρ(t)` at most `1/2`. Lemma C.6 (with a constant uniform in `dε/2 ∈ [0, d/2]`) bounds
`ρ(1/2)`, and the monotone convergence theorem removes the truncation `m`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

theorem eLpMeanNormOn_ne_top {U : Set (Vec d)} (hU0 : volume U ≠ 0) {p : ℝ≥0∞}
    {h : Vec d → ℝ} (hh : MemLp h p (volume.restrict U)) : PDE.eLpMeanNormOn U p h ≠ ⊤ :=
  (hh.smul_measure (ENNReal.inv_ne_top.mpr hU0)).eLpNorm_lt_top.ne

theorem lintegral_ball_rpow_eq {R : ℝ} (hR : 0 < R) {s : ℝ} (hs : 0 < s) {h : Vec d → ℝ}
    (hh : AEStronglyMeasurable h (volume.restrict (ball 0 R))) :
    ∫⁻ x in ball 0 R, ‖h x‖ₑ ^ s =
      volume (ball (0 : Vec d) R) * PDE.eLpMeanNormOn (ball 0 R) (ENNReal.ofReal s) h ^ s := by
  rw [eLpMeanNormOn_rpow_eq hs hh, ← mul_assoc,
    ENNReal.mul_inv_cancel (volume_ball_ne_zero' 0 hR) (volume_ball_ne_top' 0 R), one_mul]

set_option maxHeartbeats 400000 in
/-- **Gehring's lemma** for measurable `f, g`. -/
theorem gehring_measurable {q K : ℝ} (hq1 : 1 < q) (hq2 : q < 2) (hK : 1 ≤ K) :
    ∃ δ C : ℝ, 0 < δ ∧ δ < 1 ∧ 0 ≤ C ∧ ∀ (p R : ℝ), 2 < p → 0 < R → ∀ f g : Vec d → ℝ,
      Measurable f → Measurable g →
      MemLp f 2 (volume.restrict (ball 0 R)) →
      MemLp g (ENNReal.ofReal p) (volume.restrict (ball 0 R)) →
      (∀ (z : Vec d) (r : ℝ), 0 < r → ball z r ⊆ ball 0 R →
        PDE.eLpMeanNormOn (ball z (r / 2)) 2 f ≤ ENNReal.ofReal K *
          (PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal q) f +
            PDE.eLpMeanNormOn (ball z r) 2 g)) →
      PDE.eLpMeanNormOn (ball 0 (R / 2)) (ENNReal.ofReal (min (2 + δ) p)) f ≤
        ENNReal.ofReal C * (PDE.eLpMeanNormOn (ball 0 R) 2 f +
          PDE.eLpMeanNormOn (ball 0 R) (ENNReal.ofReal (min (2 + δ) p)) g) := by
  have h8K : 1 ≤ 8 * K := by linarith
  set c₀ : ℝ := 8 ^ d * (8 * K) ^ (3 : ℝ) with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  set δ : ℝ := min (1 / 2) ((2 - q) / (2 * c₀)) with hδdef
  have hδ0 : 0 < δ := lt_min (by norm_num) (div_pos (by linarith) (by positivity))
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  obtain ⟨C₆, hC₆⟩ := lemma_C_6_uniform ((d : ℝ) / 2)
  set C₆' := max C₆ 0 with hC₆'
  set CA : ℝ := (160 : ℝ) ^ ((d : ℝ) / 2) + c₀ with hCA
  set C : ℝ := max 1 (2 ^ d * C₆' * CA) with hCdef
  refine ⟨δ, C, hδ0, by linarith, le_max_of_le_left zero_le_one, ?_⟩
  intro p R hp hR f g hfm hgm hf hg hRH
  -- the exponent `2 + ε = (2 + δ) ∧ p`
  set ε : ℝ := min δ (p - 2) with hεdef
  have hε0 : 0 < ε := lt_min hδ0 (by linarith)
  have hεδ : ε ≤ δ := min_le_left _ _
  have hε1 : ε ≤ 1 / 2 := hεδ.trans hδ1
  have he : min (2 + δ) p = 2 + ε := by
    rw [hεdef]
    rcases le_total δ (p - 2) with h | h
    · rw [min_eq_left h, min_eq_left (by linarith)]
    · rw [min_eq_right h, min_eq_right (by linarith)]
      ring
  rw [he]
  have hep : 2 + ε ≤ p := by have := min_le_right δ (p - 2); linarith
  -- norms and volumes
  have hR2 : 0 < R / 2 := half_pos hR
  have hvR0 := volume_ball_ne_zero' (0 : Vec d) hR
  have hvRt := volume_ball_ne_top' (0 : Vec d) R
  have hfin : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
    isFiniteMeasure_restrict.mpr hvRt
  have hg2 : MemLp g 2 (volume.restrict (ball 0 R)) :=
    hg.mono_exponent (by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
      exact ENNReal.ofReal_le_ofReal (by linarith))
  have hge : MemLp g (ENNReal.ofReal (2 + ε)) (volume.restrict (ball 0 R)) :=
    hg.mono_exponent (ENNReal.ofReal_le_ofReal hep)
  have hfint : IntegrableOn f (ball 0 R) := hf.integrable one_le_two
  have hNf_ne := eLpMeanNormOn_ne_top hvR0 hf
  have hNg_ne := eLpMeanNormOn_ne_top hvR0 hg2
  have hNge_ne := eLpMeanNormOn_ne_top hvR0 hge
  obtain ⟨nf, hnf⟩ : ∃ x, x = (PDE.eLpMeanNormOn (ball 0 R) 2 f).toReal := ⟨_, rfl⟩
  obtain ⟨ng, hng⟩ : ∃ x, x = (PDE.eLpMeanNormOn (ball 0 R) 2 g).toReal := ⟨_, rfl⟩
  obtain ⟨nge, hnge⟩ : ∃ x, x = (PDE.eLpMeanNormOn (ball 0 R) (ENNReal.ofReal (2 + ε)) g).toReal :=
    ⟨_, rfl⟩
  have hnf0 : 0 ≤ nf := hnf ▸ ENNReal.toReal_nonneg
  have hng0 : 0 ≤ ng := hng ▸ ENNReal.toReal_nonneg
  have hnge0 : 0 ≤ nge := hnge ▸ ENNReal.toReal_nonneg
  have hNf_eq : PDE.eLpMeanNormOn (ball 0 R) 2 f = ENNReal.ofReal nf := by
    rw [hnf, ENNReal.ofReal_toReal hNf_ne]
  have hNg_eq : PDE.eLpMeanNormOn (ball 0 R) 2 g = ENNReal.ofReal ng := by
    rw [hng, ENNReal.ofReal_toReal hNg_ne]
  have hNge_eq : PDE.eLpMeanNormOn (ball 0 R) (ENNReal.ofReal (2 + ε)) g = ENNReal.ofReal nge := by
    rw [hnge, ENNReal.ofReal_toReal hNge_ne]
  have hng_le : ng ≤ nge := by
    have hpos : 0 < volume (ball (0 : Vec d) R) := pos_iff_ne_zero.mpr hvR0
    have : IsProbabilityMeasure (PDE.normalizedVolumeOn (ball (0 : Vec d) R)) :=
      PDE.isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top hpos hvRt.lt_top
    rw [hng, hnge]
    refine ENNReal.toReal_mono hNge_ne (eLpNorm_le_eLpNorm_of_exponent_le ?_)
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  obtain ⟨vRr, hvRrdef⟩ : ∃ x, x = (volume (ball (0 : Vec d) R)).toReal := ⟨_, rfl⟩
  have hvRr : 0 < vRr := hvRrdef ▸ ENNReal.toReal_pos hvR0 hvRt
  have hvR_eq : volume (ball (0 : Vec d) R) = ENNReal.ofReal vRr := by
    rw [hvRrdef, ENNReal.ofReal_toReal hvRt]
  set ξ : ℝ := (d : ℝ) * ε / 2 with hξ
  have hξ0 : 0 ≤ ξ := by positivity
  have hξd : ξ ≤ (d : ℝ) / 2 := by
    rw [hξ]
    have : (d : ℝ) * ε ≤ d * 1 := mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg d)
    linarith
  set A : ℝ := (160 : ℝ) ^ ξ * nf ^ 2 * (nf + ng) ^ ε + c₀ * nge ^ (2 + ε) with hA
  have hA0 : 0 ≤ A := by positivity
  -- the conclusion for each truncation level
  have hmain : ∀ m : ℝ, 0 < m →
      ∫⁻ x in ball 0 (R / 2), ENNReal.ofReal (min |f x| m ^ (2 + ε)) ≤
        ENNReal.ofReal (vRr * (C₆' * A)) := by
    intro m hm
    set Ψ : ℝ → ℝ≥0∞ := fun s => ∫⁻ x in ball 0 (s * R), ‖f x‖ₑ ^ (2 : ℝ) *
      ENNReal.ofReal (min |f x| m ^ ε) with hΨ
    have hΨle : ∀ s, 0 < s → s ≤ 1 → Ψ s ≤ ENNReal.ofReal (vRr * nf ^ 2 * m ^ ε) := by
      intro s hs hs1
      calc Ψ s ≤ ∫⁻ x in ball 0 R, ‖f x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (m ^ ε) := by
            refine (lintegral_mono_set ?_).trans (lintegral_mono fun x => ?_)
            · exact ball_subset_ball_of_norm (by
                rw [sub_zero, show euclideanNorm (0 : Vec d) = 0 by simp [euclideanNorm,
                  euclideanSq, dot]]
                nlinarith)
            · gcongr
              exact min_le_right _ _
        _ = ENNReal.ofReal (vRr * nf ^ 2 * m ^ ε) := by
            rw [lintegral_mul_const _ (hfm.enorm.pow_const _)]
            have h2 := lintegral_ball_rpow_eq (d := d) hR two_pos hfm.aestronglyMeasurable
            rw [ENNReal.ofReal_ofNat] at h2
            rw [h2, hvR_eq, hNf_eq, ENNReal.ofReal_rpow_of_nonneg hnf0 (by norm_num),
              ← ENNReal.ofReal_mul hvRr.le, ← ENNReal.ofReal_mul (by positivity), Real.rpow_two]
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
        ρ s ≤ 1 / 2 * ρ t + (t - s) ^ (-ξ) * A := by
      intro s t hs hst ht
      have hs0 : 0 < s := by linarith
      have hts : 0 < t - s := by linarith
      have hstep := gehring_step (d := d) hR hs0 hst ht.le hK hq1.le hq2 hε0 hm hfm hgm hfint hRH
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr ⟨hNf_ne, hNg_ne⟩))
      have hsubR : ∀ u : ℝ, 0 < u → u ≤ 1 → ball (0 : Vec d) (u * R) ⊆ ball 0 R := by
        intro u hu hu1
        exact ball_subset_ball_of_norm (by
          rw [sub_zero, show euclideanNorm (0 : Vec d) = 0 by simp [euclideanNorm, euclideanSq,
            dot]]
          nlinarith)
      have hV : ∫⁻ x in ball 0 (s * R), ‖f x‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (vRr * nf ^ 2) := by
        refine (lintegral_mono_set (hsubR s hs0 (by linarith))).trans (le_of_eq ?_)
        have h2 := lintegral_ball_rpow_eq (d := d) hR two_pos hfm.aestronglyMeasurable
        rw [ENNReal.ofReal_ofNat] at h2
        rw [h2, hvR_eq, hNf_eq, ENNReal.ofReal_rpow_of_nonneg hnf0 (by norm_num),
          ← ENNReal.ofReal_mul hvRr.le, Real.rpow_two]
      have hG : ∫⁻ x in ball 0 (t * R), ‖g x‖ₑ ^ (2 + ε) ≤
          ENNReal.ofReal (vRr * nge ^ (2 + ε)) := by
        refine (lintegral_mono_set (hsubR t (by linarith) ht.le)).trans (le_of_eq ?_)
        rw [lintegral_ball_rpow_eq hR (by linarith) hgm.aestronglyMeasurable, hvR_eq, hNge_eq,
          ENNReal.ofReal_rpow_of_nonneg hnge0 (by linarith), ← ENNReal.ofReal_mul hvRr.le]
      set L := (160 / (t - s)) ^ ((d : ℝ) / 2) * (nf + ng) with hL
      have hLeq : (ENNReal.ofReal ((160 / (t - s)) ^ ((d : ℝ) / 2)) *
          (PDE.eLpMeanNormOn (ball 0 R) 2 f + PDE.eLpMeanNormOn (ball 0 R) 2 g)).toReal = L := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
          ENNReal.toReal_add hNf_ne hNg_ne, ← hnf, ← hng]
      have h8Kpos : 0 < 8 * K := by linarith
      have hpow : (8 * K) ^ q * (8 * K) ^ (2 + ε - q) ≤ (8 * K) ^ (3 : ℝ) := by
        rw [← Real.rpow_add h8Kpos, show q + (2 + ε - q) = 2 + ε by ring]
        exact Real.rpow_le_rpow_of_exponent_le h8K (by linarith)
      have hθ : ε / (2 + ε - q) * (8 ^ d * (8 * K) ^ q * (8 * K) ^ (2 + ε - q)) ≤ 1 / 2 := by
        have h1 : ε / (2 + ε - q) ≤ 1 / (2 * c₀) := by
          calc ε / (2 + ε - q) ≤ δ / (2 - q) :=
                div_le_div₀ hδ0.le hεδ (by linarith) (by linarith)
            _ ≤ (2 - q) / (2 * c₀) / (2 - q) :=
                div_le_div_of_nonneg_right (min_le_right _ _) (by linarith)
            _ = 1 / (2 * c₀) := by
                have hq' : (2 : ℝ) - q ≠ 0 := by linarith
                field_simp
        have h2 : 8 ^ d * (8 * K) ^ q * (8 * K) ^ (2 + ε - q) ≤ c₀ := by
          rw [hc₀, mul_assoc]
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
        calc ε / (2 + ε - q) * (8 ^ d * (8 * K) ^ q * (8 * K) ^ (2 + ε - q))
            ≤ 1 / (2 * c₀) * c₀ := mul_le_mul h1 h2 (by positivity) (by positivity)
          _ = 1 / 2 := by field_simp
      have hcg : 8 ^ d * (8 * K) ^ 2 * (8 * K) ^ ε ≤ c₀ := by
        rw [hc₀, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← Real.rpow_natCast, ← Real.rpow_add h8Kpos]
        exact Real.rpow_le_rpow_of_exponent_le h8K (by push_cast; linarith)
      have hΨt : Ψ t = ENNReal.ofReal (Ψ t).toReal :=
        (ENNReal.ofReal_toReal (hΨne t (by linarith) ht.le)).symm
      have hbig : Ψ s ≤ ENNReal.ofReal (vRr * nf ^ 2 * L ^ ε + 1 / 2 * (Ψ t).toReal +
          c₀ * (vRr * nge ^ (2 + ε))) := by
        refine hstep.trans ?_
        rw [hLeq]
        have e1 := ENNReal.ofReal_le_ofReal hθ
        have e2 := ENNReal.ofReal_le_ofReal hcg
        calc _ ≤ ENNReal.ofReal (vRr * nf ^ 2) * ENNReal.ofReal (L ^ ε) +
              ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Ψ t).toReal +
              ENNReal.ofReal c₀ * ENNReal.ofReal (vRr * nge ^ (2 + ε)) := by
              gcongr
              exact le_of_eq hΨt
          _ = _ := by
              rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num),
                ← ENNReal.ofReal_mul hc₀pos.le, ← ENNReal.ofReal_add (by positivity)
                  (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      have hψ := ENNReal.toReal_le_of_le_ofReal (by positivity) hbig
      have hLε : L ^ ε = (t - s) ^ (-ξ) * ((160 : ℝ) ^ ξ * (nf + ng) ^ ε) := by
        rw [hL, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity),
          Real.div_rpow (by norm_num) hts.le, Real.rpow_neg hts.le, hξ]
        rw [show (d : ℝ) / 2 * ε = d * ε / 2 by ring]
        field_simp
      have hone : 1 ≤ (t - s) ^ (-ξ) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hts (by linarith) (by linarith)
      have hρs : ρ s ≤ nf ^ 2 * L ^ ε + 1 / 2 * ρ t + c₀ * nge ^ (2 + ε) := by
        have h := div_le_div_of_nonneg_right hψ hvRr.le
        have e : (vRr * nf ^ 2 * L ^ ε + 1 / 2 * (Ψ t).toReal + c₀ * (vRr * nge ^ (2 + ε))) /
            vRr = nf ^ 2 * L ^ ε + 1 / 2 * ((Ψ t).toReal / vRr) + c₀ * nge ^ (2 + ε) := by
          field_simp
        rw [e] at h
        exact h
      rw [hLε] at hρs
      have hc0nge : c₀ * nge ^ (2 + ε) ≤ (t - s) ^ (-ξ) * (c₀ * nge ^ (2 + ε)) :=
        le_mul_of_one_le_left (by positivity) hone
      have e : nf ^ 2 * ((t - s) ^ (-ξ) * ((160 : ℝ) ^ ξ * (nf + ng) ^ ε)) =
          (t - s) ^ (-ξ) * ((160 : ℝ) ^ ξ * nf ^ 2 * (nf + ng) ^ ε) := by ring
      rw [hA, mul_add]
      linarith
    have hρhalf := hC₆ ξ hξ0 hξd A hA0 ρ hρ0 hρbdd hiter
    have hρhalf' : ρ (1 / 2) ≤ C₆' * A :=
      hρhalf.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hA0)
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
      _ ≤ ENNReal.ofReal (vRr * (C₆' * A)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hρhalf' hvRr.le)
  -- monotone convergence
  have hlim : ∫⁻ x in ball 0 (R / 2), ‖f x‖ₑ ^ (2 + ε) ≤ ENNReal.ofReal (vRr * (C₆' * A)) := by
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
      _ ≤ ENNReal.ofReal (vRr * (C₆' * A)) := iSup_le fun n => hmain _ (by positivity)
  -- the normalized norm
  set S : ℝ := nf + nge with hS
  have hS0 : 0 ≤ S := by positivity
  have hAS : A ≤ CA * S ^ (2 + ε) := by
    have h160 : (160 : ℝ) ^ ξ ≤ 160 ^ ((d : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hξd
    have hnfS : nf ≤ S := by linarith
    have hsS : nf + ng ≤ S := by linarith
    have h1 : nf ^ 2 * (nf + ng) ^ ε ≤ S ^ (2 + ε) := by
      rw [Real.rpow_add' hS0 (by linarith), Real.rpow_two]
      exact mul_le_mul (pow_le_pow_left₀ hnf0 hnfS 2)
        (Real.rpow_le_rpow (by positivity) hsS hε0.le) (by positivity) (by positivity)
    have h2 : nge ^ (2 + ε) ≤ S ^ (2 + ε) :=
      Real.rpow_le_rpow hnge0 (by linarith) (by linarith)
    rw [hA, hCA]
    have h3 := mul_le_mul h160 h1 (by positivity) (by positivity)
    have h4 := mul_le_mul_of_nonneg_left h2 hc₀pos.le
    nlinarith [h3, h4]
  have hvol2 : volume (ball (0 : Vec d) R) =
      ENNReal.ofReal (2 ^ d) * volume (ball (0 : Vec d) (R / 2)) := by
    rw [← volume_ball_mul 0 (by norm_num : (0 : ℝ) < 2) hR2]
    congr 1
    ring
  have hpow : PDE.eLpMeanNormOn (ball 0 (R / 2)) (ENNReal.ofReal (2 + ε)) f ^ (2 + ε) ≤
      ENNReal.ofReal (2 ^ d * C₆' * CA * S ^ (2 + ε)) := by
    rw [eLpMeanNormOn_rpow_eq (by linarith) hfm.aestronglyMeasurable]
    calc (volume (ball (0 : Vec d) (R / 2)))⁻¹ * ∫⁻ x in ball 0 (R / 2), ‖f x‖ₑ ^ (2 + ε)
        ≤ (volume (ball (0 : Vec d) (R / 2)))⁻¹ * ENNReal.ofReal (vRr * (C₆' * A)) := by
          gcongr
      _ = ENNReal.ofReal (2 ^ d * (C₆' * A)) := by
          rw [ENNReal.ofReal_mul hvRr.le, ← hvR_eq, hvol2,
            ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 ^ d by positivity)]
          calc (volume (ball (0 : Vec d) (R / 2)))⁻¹ * (ENNReal.ofReal (2 ^ d) *
                volume (ball (0 : Vec d) (R / 2)) * ENNReal.ofReal (C₆' * A))
              = ENNReal.ofReal (2 ^ d) * ENNReal.ofReal (C₆' * A) *
                  ((volume (ball (0 : Vec d) (R / 2)))⁻¹ * volume (ball (0 : Vec d) (R / 2))) := by
                ring
            _ = ENNReal.ofReal (2 ^ d) * ENNReal.ofReal (C₆' * A) := by
                rw [ENNReal.inv_mul_cancel (volume_ball_ne_zero' 0 hR2) (volume_ball_ne_top' 0 _),
                  mul_one]
      _ ≤ ENNReal.ofReal (2 ^ d * C₆' * CA * S ^ (2 + ε)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have := mul_le_mul_of_nonneg_left hAS (by positivity : (0 : ℝ) ≤ 2 ^ d * C₆')
          calc 2 ^ d * (C₆' * A) = 2 ^ d * C₆' * A := by ring
            _ ≤ 2 ^ d * C₆' * (CA * S ^ (2 + ε)) := this
            _ = 2 ^ d * C₆' * CA * S ^ (2 + ε) := by ring
  have hY0 : 0 ≤ 2 ^ d * C₆' * CA := by positivity
  have hroot := ENNReal.rpow_le_rpow hpow (by positivity : (0 : ℝ) ≤ 1 / (2 + ε))
  rw [← ENNReal.rpow_mul, mul_one_div_cancel (by linarith), ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
    Real.mul_rpow hY0 (by positivity), ← Real.rpow_mul hS0, mul_one_div_cancel (by linarith),
    Real.rpow_one] at hroot
  have hYC : (2 ^ d * C₆' * CA) ^ (1 / (2 + ε)) ≤ C := by
    calc (2 ^ d * C₆' * CA) ^ (1 / (2 + ε)) ≤ C ^ (1 / (2 + ε)) :=
          Real.rpow_le_rpow hY0 (le_max_right _ _) (by positivity)
      _ ≤ C ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (le_max_left _ _)
          (by rw [div_le_one (by linarith)]; linarith)
      _ = C := Real.rpow_one _
  calc PDE.eLpMeanNormOn (ball 0 (R / 2)) (ENNReal.ofReal (2 + ε)) f
      ≤ ENNReal.ofReal ((2 ^ d * C₆' * CA) ^ (1 / (2 + ε)) * S) := hroot
    _ ≤ ENNReal.ofReal (C * S) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hYC hS0)
    _ = ENNReal.ofReal C * (PDE.eLpMeanNormOn (ball 0 R) 2 f +
          PDE.eLpMeanNormOn (ball 0 R) (ENNReal.ofReal (2 + ε)) g) := by
        rw [hNf_eq, hNge_eq, ← ENNReal.ofReal_add hnf0 hnge0, ← ENNReal.ofReal_mul
          (le_max_of_le_left zero_le_one)]

end QSH
