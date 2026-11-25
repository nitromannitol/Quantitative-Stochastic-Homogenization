import QuantitativeStochasticHomogenization.Ch01.Sec04.DivCurlBounds

/-!
# Lemma 1.16: the div-curl lemma

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 1.16: for `q ∈ [1, d/(d-1))`, `u₁, u₂ ∈ H¹(U)` and `g₁, g₂ ∈ L²_sol(U)`,
`‖∇u₁ · g₁ - ∇u₂ · g₂‖_{W^{-2,q}(U)} ≤ C (‖∇u₁‖_{L²(U)} ‖g₁ - g₂‖_{H^{-1}(U)} +
‖g₂‖_{L²(U)} ‖u₁ - u₂‖_{L²(U)})` with `C(U, q, d)`.

Here `U` is a bounded open convex domain and the norms are the volume-normalized ones of (0.29)
(`negativeSobolevTwoNorm`, `vectorNegativeSobolevOneNorm`, `PDE.eLpMeanNormOn`); the `H^{-1}` norm
of a vector field is the sum of the norms of its components. The quantitative form
`lemma_1_16_quantitative` gives `C = C(q, d, κ) D` for a domain of diameter at most `D` with
`|U| ≥ κ D^d`, the form used on the cubes `□_m` in Proposition 1.15.

The proof is the book's: with `p = q'` and `(u₁)_U = 0`,
`∫_U φ (∇u₁ · g₁ - ∇u₂ · g₂) = -∫_U ∇φ · (u₁ (g₁ - g₂) + (u₁ - u₂) g₂)`
(`setIntegral_mul_dot_eq_neg`); the first term is bounded by `‖g₁ - g₂‖_{H^{-1}} ‖u₁ ∇φ‖_{H¹}`, and
`‖u₁ ∇φ‖_{H¹} ≤ C D ‖∇u₁‖_{L̲²}` by Morrey's inequality for `∇φ` (`p > d`), Hölder's inequality and
the Sobolev–Poincaré inequality `‖u₁‖_{L̲^{2p/(p-2)}} ≤ C D ‖∇u₁‖_{L̲²}`; the second term is bounded
by `‖g₂‖_{L̲²} ‖u₁ - u₂‖_{L̲²} ‖∇φ‖_{L^∞}`.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-! ## Normalized norms of products -/

theorem toReal_eLpMeanNormOn_le_mul {U : Set (Vec d)} (hU0 : volume U ≠ 0) (hUt : volume U ≠ ⊤)
    {r : ℝ≥0∞} {f h : Vec d → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hf : AEStronglyMeasurable f (volume.restrict U)) (hh : MemLp h r (volume.restrict U))
    (hfh : ∀ x, |f x| ≤ M * |h x|) :
    (PDE.eLpMeanNormOn U r f).toReal ≤ M * (PDE.eLpMeanNormOn U r h).toReal := by
  have h1 : PDE.eLpMeanNormOn U r f ≤ ENNReal.ofReal M * PDE.eLpMeanNormOn U r h := by
    have he : PDE.eLpMeanNormOn U r (fun x => M * h x) =
        ENNReal.ofReal M * PDE.eLpMeanNormOn U r h := by
      change eLpNorm (M • h) r _ = _
      rw [eLpNorm_const_smul, Real.enorm_of_nonneg hM]
      rfl
    rw [← he]
    refine eLpNorm_mono (hf.smul_measure _) fun x => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hM]
    exact hfh x
  have hfin : ENNReal.ofReal M * PDE.eLpMeanNormOn U r h ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (eLpMeanNormOn_ne_top_of_memLp hU0 hUt hh)
  calc (PDE.eLpMeanNormOn U r f).toReal
      ≤ (ENNReal.ofReal M * PDE.eLpMeanNormOn U r h).toReal := ENNReal.toReal_mono hfin h1
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM]

theorem toReal_eLpMeanNormOn_mul_le {U : Set (Vec d)} (hU0 : volume U ≠ 0) (hUt : volume U ≠ ⊤)
    {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r] {f h : Vec d → ℝ}
    (hf : MemLp f p (volume.restrict U)) (hh : MemLp h q (volume.restrict U)) :
    (PDE.eLpMeanNormOn U r (fun x => f x * h x)).toReal ≤
      (PDE.eLpMeanNormOn U p f).toReal * (PDE.eLpMeanNormOn U q h).toReal := by
  rw [← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top (eLpMeanNormOn_ne_top_of_memLp hU0 hUt hf)
    (eLpMeanNormOn_ne_top_of_memLp hU0 hUt hh)) ?_
  exact eLpNorm_smul_le_mul_eLpNorm (hf.aestronglyMeasurable.smul_measure _)
    (hh.aestronglyMeasurable.smul_measure _)

theorem toReal_eLpMeanNormOn_add_le {U : Set (Vec d)} (hU0 : volume U ≠ 0) (hUt : volume U ≠ ⊤)
    {r : ℝ≥0∞} (hr : 1 ≤ r) {f h : Vec d → ℝ} (hf : MemLp f r (volume.restrict U))
    (hh : MemLp h r (volume.restrict U)) :
    (PDE.eLpMeanNormOn U r (fun x => f x + h x)).toReal ≤
      (PDE.eLpMeanNormOn U r f).toReal + (PDE.eLpMeanNormOn U r h).toReal := by
  have hf' := eLpMeanNormOn_ne_top_of_memLp hU0 hUt hf
  have hh' := eLpMeanNormOn_ne_top_of_memLp hU0 hUt hh
  rw [← ENNReal.toReal_add hf' hh']
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hf', hh'⟩) (eLpNorm_add_le hr)

theorem toReal_eLpMeanNormOn_mono_exponent {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hUt : volume U ≠ ⊤) {r r' : ℝ≥0∞} (hrr : r ≤ r') {f : Vec d → ℝ}
    (hf : MemLp f r' (volume.restrict U)) :
    (PDE.eLpMeanNormOn U r f).toReal ≤ (PDE.eLpMeanNormOn U r' f).toReal := by
  have : IsProbabilityMeasure (PDE.normalizedVolumeOn U) :=
    PDE.isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top (pos_iff_ne_zero.2 hU0)
      (lt_top_iff_ne_top.2 hUt)
  exact ENNReal.toReal_mono (eLpMeanNormOn_ne_top_of_memLp hU0 hUt hf)
    (eLpNorm_le_eLpNorm_of_exponent_le hrr)

theorem memLp_of_eLpMeanNormOn_ne_top {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hUt : volume U ≠ ⊤) {r : ℝ≥0∞} {f : Vec d → ℝ} (h : PDE.eLpMeanNormOn U r f ≠ ⊤) :
    MemLp f r (volume.restrict U) := by
  rw [PDE.eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn (lt_top_iff_ne_top.2 hUt)] at h
  exact ENNReal.lt_top_of_mul_ne_top_right h
    (ENNReal.rpow_pos (ENNReal.inv_pos.2 hUt) (ENNReal.inv_ne_top.2 hU0)).ne'

/-- Every second derivative of a test function is bounded by its `W̲^{2,p}(U)` norm. -/
theorem toReal_eLpMeanNormOn_second_le_of_contDiff (p : ℝ≥0∞) (U : Set (Vec d))
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i j : Fin d) :
    (PDE.eLpMeanNormOn U p (coordinateDerivative j (coordinateDerivative i φ))).toReal ≤
      sobolevTwoTestNorm p U φ := by
  rcases le_or_gt i j with hij | hij
  · exact toReal_eLpMeanNormOn_second_le p U φ hij
  · rw [coordinateDerivative_comm_of_contDiff hφ j i]
    exact toReal_eLpMeanNormOn_second_le p U φ hij.le

theorem integrable_mul_mul_of_isSpatialTest {U : Set (Vec d)} {f h ψ : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (hh : MemLp h 2 (volume.restrict U))
    (hψ : IsSpatialTest U ψ) :
    Integrable (fun x => f x * (ψ x * h x)) (volume.restrict U) := by
  obtain ⟨C, hC⟩ := exists_bound_of_isSpatialTest hψ
  refine ((hf.integrable_mul hh).bdd_mul hψ.1.continuous.aestronglyMeasurable
    (Eventually.of_forall hC)).congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply]
  ring

/-- `∫_U u ∇φ · g = ∑_i ∫_U g_i (∂_i φ u)`. -/
theorem setIntegral_mul_dot_gradient_eq_sum {U : Set (Vec d)} {u : Vec d → ℝ}
    {g : Vec d → Vec d} (hu : MemLp u 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U))
    {φ : Vec d → ℝ} (hφ : IsSpatialTest U φ) :
    ∫ x in U, u x * dot (gradient φ x) (g x) =
      ∑ i, ∫ x in U, g x i * (coordinateDerivative i φ x * u x) := by
  rw [← integral_finsetSum _ fun i _ => integrable_mul_mul_of_isSpatialTest (hg.eval i) hu
    (isSpatialTest_coordinateDerivative hφ i)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [dot, gradient, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The exponents of the proof of Lemma 1.16 for `q ∈ [1, d/(d-1))`: `p'` with `d < p' ≤ q'`, and
`t = 2q/(2-q)` with `1/t + 1/q' = 1/2`, `t = s* = ds/(d-s)` for some `s ∈ [1, 2]`, `s < d`. -/
theorem exists_divCurl_exponents (hd : 2 ≤ d) {q : ℝ} (hq : 1 ≤ q) (hqd : q < d / (d - 1)) :
    ∃ p' t s : ℝ, (d : ℝ) < p' ∧ ENNReal.ofReal p' ≤ (ENNReal.ofReal q).conjExponent ∧
      ENNReal.HolderTriple (ENNReal.ofReal t) (ENNReal.ofReal q).conjExponent 2 ∧ 2 ≤ t ∧
      1 ≤ s ∧ s ≤ 2 ∧ s < d ∧ PDE.sobolevConjugate d s = t := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < d - 1 := by linarith
  have hq0 : 0 < q := by linarith
  have hqd' : q * (d - 1) < d := by rwa [lt_div_iff₀ hd1] at hqd
  set a : ℝ := 1 - 1 / q with ha
  have ha0 : 0 ≤ a := by
    rw [ha, sub_nonneg, div_le_one hq0]
    exact hq
  have had : a < 1 / d := by
    rw [ha, sub_lt_iff_lt_add, div_add_div _ _ (by positivity) hq0.ne', lt_div_iff₀ (by positivity)]
    nlinarith
  have hd0 : (0 : ℝ) < d := by linarith
  have ha2 : a < 1 / 2 := had.trans_le (by rw [div_le_div_iff₀ hd0 (by norm_num)]; linarith)
  -- the conjugate exponent
  set p := (ENNReal.ofReal q).conjExponent with hp
  have hq1 : 1 ≤ ENNReal.ofReal q := by simpa using ENNReal.ofReal_le_ofReal hq
  have hconj := (ENNReal.HolderConjugate.conjExponent hq1).inv_add_inv_eq_inv
  rw [← hp, inv_one, ← ENNReal.ofReal_inv_of_pos hq0] at hconj
  have hpinv : p⁻¹ = ENNReal.ofReal a := by
    rw [ha, ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one, one_div, ← hconj,
      ENNReal.add_sub_cancel_left ENNReal.ofReal_ne_top]
  -- `p'`
  set p' : ℝ := 2 / (1 / d + a) with hp'
  have hden : 0 < 1 / (d : ℝ) + a := by positivity
  have hdp' : (d : ℝ) < p' := by
    rw [hp', lt_div_iff₀ hden]
    have : (d : ℝ) * (1 / d) = 1 := by field_simp
    nlinarith
  have hp'0 : 0 < p' := hd0.trans hdp'
  have hp'p : ENNReal.ofReal p' ≤ p := by
    rw [← ENNReal.inv_le_inv, hpinv, ← ENNReal.ofReal_inv_of_pos hp'0]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hp', inv_div]
    linarith
  -- `t`
  set t : ℝ := 1 / (1 / 2 - a) with ht
  have hb : 0 < 1 / 2 - a := by linarith
  have ht0 : 0 < t := by positivity
  have ht2 : 2 ≤ t := by
    rw [ht, le_div_iff₀ hb]
    linarith
  have hT : ENNReal.HolderTriple (ENNReal.ofReal t) p 2 := by
    refine ⟨?_⟩
    rw [hpinv, ← ENNReal.ofReal_inv_of_pos ht0, ht, inv_div, div_one,
      ← ENNReal.ofReal_add hb.le ha0, sub_add_cancel, show (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp]
  -- `s`
  set s : ℝ := d * t / (d + t) with hs
  have hdt : 0 < (d : ℝ) + t := by positivity
  have hs1 : 1 ≤ s := by
    rw [hs, le_div_iff₀ hdt]
    nlinarith [mul_le_mul (show (1 : ℝ) ≤ d - 1 by linarith) (show (1 : ℝ) ≤ t - 1 by linarith)
      zero_le_one (by linarith)]
  have hs2 : s ≤ 2 := by
    rw [hs, div_le_iff₀ hdt]
    have h0 : t * (1 / 2 - a) = 1 := by rw [ht, one_div_mul_cancel hb.ne']
    have h1 : (d : ℝ) * a ≤ 1 := by
      have := mul_le_mul_of_nonneg_left had.le hd0.le
      rwa [mul_one_div_cancel hd0.ne'] at this
    have h2 : (d : ℝ) * t = 2 * d + 2 * (t * (d * a)) := by linear_combination (2 * (d : ℝ)) * h0
    have h3 := mul_le_mul_of_nonneg_left h1 ht0.le
    linarith
  have hsd : s < d := by
    rw [hs, div_lt_iff₀ hdt]
    nlinarith
  have hst : PDE.sobolevConjugate d s = t := by
    rw [PDE.sobolevConjugate, div_eq_iff (sub_ne_zero.2 hsd.ne'), hs]
    field_simp
    ring
  exact ⟨p', t, s, hdp', hp'p, hT, ht2, hs1, hs2, hsd, hst⟩

/-- **Lemma 1.16** (div-curl lemma), quantitative form: for `d ≥ 2`, `q ∈ [1, d/(d-1))` and
`κ > 0` there is `C(q, d, κ)` such that, for every bounded open convex `U` whose points are at
distance at most `D` with `|U| ≥ κ D^d`, `u₁, u₂ ∈ H¹(U)` with gradients `G₁, G₂` and
`g₁, g₂ ∈ L²_sol(U)`,
`‖G₁ · g₁ - G₂ · g₂‖_{W̲^{-2,q}(U)} ≤ C D (‖G₁‖_{L̲²(U)} ‖g₁ - g₂‖_{H̲^{-1}(U)} +
‖g₂‖_{L̲²(U)} ‖u₁ - u₂‖_{L̲²(U)})`. -/
theorem lemma_1_16_quantitative (hd : 2 ≤ d) {q : ℝ} (hq : 1 ≤ q) (hqd : q < d / (d - 1))
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set (Vec d)) (D : ℝ), IsOpen U → Convex ℝ U → U.Nonempty → 0 < D →
      (∀ x ∈ U, ∀ y ∈ U, euclideanNorm (x - y) ≤ D) → ENNReal.ofReal (κ * D ^ d) ≤ volume U →
      ∀ (u₁ u₂ : Vec d → ℝ) (G₁ G₂ g₁ g₂ : Vec d → Vec d),
        H1 U u₁ G₁ → H1 U u₂ G₂ → IsL2Sol U g₁ → IsL2Sol U g₂ →
        negativeSobolevTwoNorm (ENNReal.ofReal q) U
            (fun x => dot (G₁ x) (g₁ x) - dot (G₂ x) (g₂ x)) ≤
          ENNReal.ofReal (C * D) *
            (PDE.eLpMeanNormOn U 2 (fun x => euclideanNorm (G₁ x)) *
                vectorNegativeSobolevOneNorm 2 U (fun x => g₁ x - g₂ x) +
              PDE.eLpMeanNormOn U 2 (fun x => euclideanNorm (g₂ x)) *
                PDE.eLpMeanNormOn U 2 (fun x => u₁ x - u₂ x)) := by
  have hd0 : 0 < d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨p', t, s, hdp', hp'p, hT, ht2, hs1, hs2, hsd, hst⟩ := exists_divCurl_exponents hd hq hqd
  set p := (ENNReal.ofReal q).conjExponent with hp
  have hp'0 : 0 < p' := by linarith
  have hp1 : 1 ≤ p :=
    le_trans (by simpa using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ p')) hp'p
  have ht2' : (2 : ℝ≥0∞) ≤ ENNReal.ofReal t := by
    simpa using ENNReal.ofReal_le_ofReal ht2
  obtain ⟨Cs, hCs, hSP⟩ := exists_sobolevPoincare_H1 hd hs1 hs2 hsd
  have hc' : 0 < 1 - (d : ℝ) / p' := by
    have : (d : ℝ) / p' < 1 := (div_lt_one hp'0).2 hdp'
    linarith
  obtain ⟨cM, hcMdef⟩ : ∃ cM : ℝ, cM = 8 * Real.sqrt d / (1 - d / p') := ⟨_, rfl⟩
  have hcM : 0 ≤ cM := by rw [hcMdef]; exact div_nonneg (by positivity) hc'.le
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ,
      K₁ = κ ^ (-(1 : ℝ) / d) * (2 * cM * d) * Cs + d * (2 * cM * d + Cs) := ⟨_, rfl⟩
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  refine ⟨K₁ + 2 * cM * d ^ 2 + 1, by positivity, ?_⟩
  intro U D hUo hUc hne hD0 hUD hvol u₁ u₂ G₁ G₂ g₁ g₂ hu₁ hu₂ hg₁ hg₂
  obtain ⟨z, hz⟩ := hne
  have hUB : U ⊆ ball z (2 * D) := fun y hy => by
    show euclideanNorm (y - z) < 2 * D
    linarith [hUD y hy z hz]
  have hUb : Bornology.IsBounded U := (isBounded_ball_of_pos z (by positivity)).subset hUB
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume ⟨z, hz⟩).ne'
  have hUt : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hUcv := isOpenBoundedConvexDomain_of_isBounded hUo hUb hUc
  have hV : 0 < (volume U).toReal := ENNReal.toReal_pos hU0 hUt
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUt
  -- `|U|^{-1/d} ≤ κ^{-1/d} D⁻¹`
  have hVd : (volume U).toReal ^ (-(1 : ℝ) / d) ≤ κ ^ (-(1 : ℝ) / d) * D⁻¹ := by
    have h1 : κ * D ^ d ≤ (volume U).toReal := by
      have := ENNReal.toReal_mono hUt hvol
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    have hneg : -(1 : ℝ) / d ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
    refine (Real.rpow_le_rpow_of_nonpos (by positivity) h1 hneg).trans (le_of_eq ?_)
    rw [Real.mul_rpow hκ.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hD0.le]
    have : (d : ℝ) * (-(1 : ℝ) / d) = -1 := by field_simp
    rw [this, Real.rpow_neg_one]
  -- the norms on the right
  set N1 := PDE.eLpMeanNormOn U 2 (fun x => euclideanNorm (G₁ x)) with hN1def
  set Ng := PDE.eLpMeanNormOn U 2 (fun x => euclideanNorm (g₂ x)) with hNgdef
  set Nu := PDE.eLpMeanNormOn U 2 (fun x => u₁ x - u₂ x) with hNudef
  have hN1 : N1 ≠ ⊤ := eLpMeanNormOn_ne_top_of_memLp hU0 hUt (memLp_two_euclideanNorm hu₁.2.1)
  have hNg : Ng ≠ ⊤ := eLpMeanNormOn_ne_top_of_memLp hU0 hUt (memLp_two_euclideanNorm hg₂.1)
  have hNu : Nu ≠ ⊤ := eLpMeanNormOn_ne_top_of_memLp hU0 hUt (hu₁.1.sub hu₂.1)
  have hgg : ∀ i, MemLp (fun x => g₁ x i - g₂ x i) 2 (volume.restrict U) :=
    fun i => (hg₁.1.eval i).sub (hg₂.1.eval i)
  set Hn : Fin d → ℝ≥0∞ := fun i => negativeSobolevOneNorm 2 U (fun x => g₁ x i - g₂ x i) 0
    with hHn
  have hHfin : ∀ i, Hn i ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (negativeSobolevOneNorm_two_le hU0 hUt (hgg i))
  have hvec : vectorNegativeSobolevOneNorm 2 U (fun x => g₁ x - g₂ x) = ∑ i, Hn i := rfl
  -- centering `u₁`
  set c₁ := PDE.integralAverage U u₁ with hc₁
  have hũ : H1 U (fun x => u₁ x - c₁) G₁ := hu₁.sub_const hUt c₁
  have hSPu : PDE.eLpMeanNormOn U (ENNReal.ofReal t) (fun x => u₁ x - c₁) ≤
      ENNReal.ofReal (Cs * D) * N1 := by
    have h := hSP U D hUo hUb hUc ⟨z, hz⟩ hUD u₁ G₁ hu₁
    rwa [hst] at h
  have hSPfin : ENNReal.ofReal (Cs * D) * N1 ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN1
  have hũt : MemLp (fun x => u₁ x - c₁) (ENNReal.ofReal t) (volume.restrict U) :=
    memLp_of_eLpMeanNormOn_ne_top hU0 hUt (ne_top_of_le_ne_top hSPfin hSPu)
  have hũtr : (PDE.eLpMeanNormOn U (ENNReal.ofReal t) (fun x => u₁ x - c₁)).toReal ≤
      Cs * D * N1.toReal := by
    have := ENNReal.toReal_mono hSPfin hSPu
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have hũ2 : (PDE.eLpMeanNormOn U 2 (fun x => u₁ x - c₁)).toReal ≤ Cs * D * N1.toReal :=
    (toReal_eLpMeanNormOn_mono_exponent hU0 hUt ht2' hũt).trans hũtr
  have hG1j : ∀ j, (PDE.eLpMeanNormOn U 2 (fun x => G₁ x j)).toReal ≤ N1.toReal := fun j =>
    ENNReal.toReal_mono hN1 (eLpMeanNormOn_apply_le_euclideanNorm U 2
      hu₁.2.1.aestronglyMeasurable j)
  have hg2j : ∀ j, (PDE.eLpMeanNormOn U 2 (fun x => g₂ x j)).toReal ≤ Ng.toReal := fun j =>
    ENNReal.toReal_mono hNg (eLpMeanNormOn_apply_le_euclideanNorm U 2
      hg₂.1.aestronglyMeasurable j)
  -- the bound for one test function
  set M : ℝ := cM * (2 * D) * d with hMdef
  have hM0 : 0 ≤ M := by positivity
  refine negativeSobolevTwoNorm_le fun φ hφ hφ1 => ?_
  rw [← hp] at hφ1
  have hφi := isSpatialTest_coordinateDerivative hφ
  have hM : ∀ i x, |coordinateDerivative i φ x| ≤ M := by
    intro i x
    have h1 := abs_le_of_isSpatialTest_of_subset_ball hd0 hdp' hU0 (by positivity : (0 : ℝ) < 2 * D)
      hUB (hφi i) x
    have hFm : MemLp (fun y => euclideanNorm (gradient (coordinateDerivative i φ) y)) p
        (volume.restrict U) :=
      ((PDE.continuous_vecEuclideanNorm.comp (continuous_gradient_of_contDiff
        ((hφi i).1.of_le (by exact_mod_cast le_top)))).memLp_of_hasCompactSupport
        ((hφi i).2.1.mono' support_euclideanNorm_gradient_subset)).restrict U
    have h2 := (toReal_eLpMeanNormOn_mono_exponent hU0 hUt hp'p hFm).trans
      (toReal_eLpMeanNormOn_gradient_coordinateDerivative_le hU0 hUt hp1 hφ i)
    rw [← hcMdef] at h1
    calc |coordinateDerivative i φ x|
        ≤ cM * (2 * D) * (PDE.eLpMeanNormOn U (ENNReal.ofReal p')
            (fun y => euclideanNorm (gradient (coordinateDerivative i φ) y))).toReal := h1
      _ ≤ cM * (2 * D) * (d * 1) :=
          mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left hφ1 (Nat.cast_nonneg d)))
            (by positivity)
      _ = M := by rw [hMdef]; ring
  have hsec : ∀ i j,
      (PDE.eLpMeanNormOn U p (coordinateDerivative j (coordinateDerivative i φ))).toReal ≤ 1 :=
    fun i j => (toReal_eLpMeanNormOn_second_le_of_contDiff p U hφ.1 i j).trans hφ1
  have hsecm : ∀ i j,
      MemLp (coordinateDerivative j (coordinateDerivative i φ)) p (volume.restrict U) :=
    fun i j => ((isSpatialTest_coordinateDerivative (hφi i) j).1.continuous.memLp_of_hasCompactSupport
      (isSpatialTest_coordinateDerivative (hφi i) j).2.1).restrict U
  have hbdd : ∀ i {h : Vec d → ℝ}, MemLp h 2 (volume.restrict U) →
      MemLp (fun x => coordinateDerivative i φ x * h x) 2 (volume.restrict U) := by
    intro i h hh
    refine (hh.const_mul M).of_le ((hφi i).1.continuous.aestronglyMeasurable.mul
      hh.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hM0]
    exact mul_le_mul_of_nonneg_right (hM i x) (abs_nonneg _)
  have hbddr : ∀ i {h : Vec d → ℝ}, MemLp h 2 (volume.restrict U) →
      (PDE.eLpMeanNormOn U 2 (fun x => coordinateDerivative i φ x * h x)).toReal ≤
        M * (PDE.eLpMeanNormOn U 2 h).toReal := by
    intro i h hh
    refine toReal_eLpMeanNormOn_le_mul hU0 hUt hM0 ((hφi i).1.continuous.aestronglyMeasurable.mul
      hh.aestronglyMeasurable) hh fun x => ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hM i x) (abs_nonneg _)
  -- the terms of the identity
  set a : Fin d → ℝ := fun i =>
    ∫ x in U, (g₁ x i - g₂ x i) * (coordinateDerivative i φ x * (u₁ x - c₁)) with ha
  set b : Fin d → ℝ := fun i =>
    ∫ x in U, (u₁ x - u₂ x) * (coordinateDerivative i φ x * g₂ x i) with hb
  have ha_le : ∀ i, |a i| ≤ (volume U).toReal * ((Hn i).toReal * (K₁ * D * N1.toReal)) := by
    intro i
    have hpair := abs_integral_pairing_le_of_h10 hUt (hgg i) (F := 0) (fun _ => MemLp.zero)
      ENNReal.toReal_nonneg (le_of_eq (ENNReal.ofReal_toReal (hHfin i)).symm)
      ((hũ.toPDEH1Function).mulContDiffHasCompactSupportToH10 hUcv (hφi i).1 (hφi i).2.1
        (hφi i).2.2)
    rw [PDE.H1Function.mulContDiffHasCompactSupportToH10_toH1Function] at hpair
    have hfun := PDE.H1Function.mulContDiffHasCompactSupport_toFun hũ.toPDEH1Function
      (hφi i).1 (hφi i).2.1
    have hgrad := PDE.H1Function.mulContDiffHasCompactSupport_grad hũ.toPDEH1Function
      (hφi i).1 (hφi i).2.1
    set v := hũ.toPDEH1Function.mulContDiffHasCompactSupport (hφi i).1 (hφi i).2.1 with hv
    have hI : (∫ x in U, (g₁ x i - g₂ x i) * v x) -
        ∫ x in U, PDE.vecDot ((0 : Vec d → Vec d) x) (v.grad x) = a i := by
      have h0 : ∫ x in U, PDE.vecDot ((0 : Vec d → Vec d) x) (v.grad x) = 0 := by
        simp [PDE.vecDot]
      rw [h0, sub_zero]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      show (g₁ x i - g₂ x i) * v.toFun x = _
      rw [hfun]
      rfl
    rw [hI] at hpair
    refine hpair.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_
      ENNReal.toReal_nonneg) hV.le)
    -- the `H¹` norm of `∂_i φ (u₁ - c₁)`
    unfold h10TestNorm
    rw [PDE.H1Function.mulContDiffHasCompactSupportToH10_toH1Function]
    change (volume U).toReal ^ (-(1 : ℝ) / d) * (PDE.eLpMeanNormOn U 2 v.toFun).toReal +
      ∑ j, (PDE.eLpMeanNormOn U 2 (fun x => v.grad x j)).toReal ≤ K₁ * D * N1.toReal
    rw [hfun, hgrad]
    have t1 : (PDE.eLpMeanNormOn U 2 (fun x => coordinateDerivative i φ x * (u₁ x - c₁))).toReal ≤
        M * (Cs * D * N1.toReal) :=
      (hbddr i hũ.1).trans (mul_le_mul_of_nonneg_left hũ2 hM0)
    have t2 : ∀ j, (PDE.eLpMeanNormOn U 2 (fun x => (coordinateDerivative i φ x • G₁ x +
        (u₁ x - c₁) • PDE.classicalGradient (coordinateDerivative i φ) x) j)).toReal ≤
        M * N1.toReal + Cs * D * N1.toReal := by
      intro j
      have e : (fun x => (coordinateDerivative i φ x • G₁ x +
          (u₁ x - c₁) • PDE.classicalGradient (coordinateDerivative i φ) x) j) =
          fun x => coordinateDerivative i φ x * G₁ x j +
            (u₁ x - c₁) * coordinateDerivative j (coordinateDerivative i φ) x := by
        funext x
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, PDE.classicalGradient]
        rfl
      rw [e]
      have := hT
      have hB := toReal_eLpMeanNormOn_mul_le (r := 2) hU0 hUt hũt (hsecm i j)
      refine (toReal_eLpMeanNormOn_add_le hU0 hUt one_le_two (hbdd i (hu₁.2.1.eval j))
        (hũt.mul (hsecm i j))).trans (add_le_add ((hbddr i (hu₁.2.1.eval j)).trans
          (mul_le_mul_of_nonneg_left (hG1j j) hM0)) (hB.trans ?_))
      calc (PDE.eLpMeanNormOn U (ENNReal.ofReal t) (fun x => u₁ x - c₁)).toReal *
            (PDE.eLpMeanNormOn U p (coordinateDerivative j (coordinateDerivative i φ))).toReal
          ≤ (Cs * D * N1.toReal) * 1 :=
            mul_le_mul hũtr (hsec i j) ENNReal.toReal_nonneg (by positivity)
        _ = Cs * D * N1.toReal := mul_one _
    calc (volume U).toReal ^ (-(1 : ℝ) / d) *
          (PDE.eLpMeanNormOn U 2 (fun x => coordinateDerivative i φ x * (u₁ x - c₁))).toReal +
        ∑ j, (PDE.eLpMeanNormOn U 2 (fun x => (coordinateDerivative i φ x • G₁ x +
          (u₁ x - c₁) • PDE.classicalGradient (coordinateDerivative i φ) x) j)).toReal
        ≤ κ ^ (-(1 : ℝ) / d) * D⁻¹ * (M * (Cs * D * N1.toReal)) +
            ∑ _j : Fin d, (M * N1.toReal + Cs * D * N1.toReal) :=
          add_le_add (mul_le_mul hVd t1 ENNReal.toReal_nonneg (by positivity))
            (Finset.sum_le_sum fun j _ => t2 j)
      _ = K₁ * D * N1.toReal := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hK₁, hMdef]
          field_simp
  have hb_le : ∀ i, |b i| ≤ (volume U).toReal * (Nu.toReal * (M * Ng.toReal)) := by
    intro i
    have h1 := abs_setAverage_mul_le hU0 hUt (hu₁.1.sub hu₂.1) (hbdd i (hg₂.1.eval i))
    have h2 := (hbddr i (hg₂.1.eval i)).trans (mul_le_mul_of_nonneg_left (hg2j i) hM0)
    have hbavg : b i = (volume U).toReal *
        ⨍ x in U, (u₁ x - u₂ x) * (coordinateDerivative i φ x * g₂ x i) := by
      rw [setAverage_eq, smul_eq_mul, measureReal_def, ← mul_assoc, mul_inv_cancel₀ hV.ne',
        one_mul]
    rw [hbavg, abs_mul, abs_of_pos hV]
    exact mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2
      ENNReal.toReal_nonneg)) hV.le
  -- the identity
  have hK1 := setIntegral_mul_dot_eq_neg hUcv hUt hũ hg₁ hφ
  have hK2 := setIntegral_mul_dot_eq_neg hUcv hUt hũ hg₂ hφ
  have hK3 := setIntegral_mul_dot_eq_neg hUcv hUt hu₁ hg₂ hφ
  have hK4 := setIntegral_mul_dot_eq_neg hUcv hUt hu₂ hg₂ hφ
  have hX1 := setIntegral_mul_dot_gradient_eq_sum hũ.1 hg₁.1 hφ
  have hX2 := setIntegral_mul_dot_gradient_eq_sum hũ.1 hg₂.1 hφ
  have hX3 := setIntegral_mul_dot_gradient_eq_sum hu₁.1 hg₂.1 hφ
  have hX4 := setIntegral_mul_dot_gradient_eq_sum hu₂.1 hg₂.1 hφ
  have ha_split : ∀ i, a i = (∫ x in U, g₁ x i * (coordinateDerivative i φ x * (u₁ x - c₁))) -
      ∫ x in U, g₂ x i * (coordinateDerivative i φ x * (u₁ x - c₁)) := by
    intro i
    rw [← integral_sub (integrable_mul_mul_of_isSpatialTest (hg₁.1.eval i) hũ.1 (hφi i))
      (integrable_mul_mul_of_isSpatialTest (hg₂.1.eval i) hũ.1 (hφi i))]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  have hb_split : ∀ i, b i = (∫ x in U, g₂ x i * (coordinateDerivative i φ x * u₁ x)) -
      ∫ x in U, g₂ x i * (coordinateDerivative i φ x * u₂ x) := by
    intro i
    rw [← integral_sub (integrable_mul_mul_of_isSpatialTest (hg₂.1.eval i) hu₁.1 (hφi i))
      (integrable_mul_mul_of_isSpatialTest (hg₂.1.eval i) hu₂.1 (hφi i))]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  obtain ⟨Cφ, hCφ⟩ := exists_bound_of_isSpatialTest hφ
  have hI1 : Integrable (fun x => φ x * dot (G₁ x) (g₁ x)) (volume.restrict U) :=
    (integrable_dot_of_memLp hu₁.2.1 hg₁.1).bdd_mul hφ.1.continuous.aestronglyMeasurable
      (Eventually.of_forall hCφ)
  have hI2 : Integrable (fun x => φ x * dot (G₂ x) (g₂ x)) (volume.restrict U) :=
    (integrable_dot_of_memLp hu₂.2.1 hg₂.1).bdd_mul hφ.1.continuous.aestronglyMeasurable
      (Eventually.of_forall hCφ)
  have hmain : ∫ x in U, (dot (G₁ x) (g₁ x) - dot (G₂ x) (g₂ x)) * φ x =
      -(∑ i, a i + ∑ i, b i) := by
    have hI : ∫ x in U, (dot (G₁ x) (g₁ x) - dot (G₂ x) (g₂ x)) * φ x =
        (∫ x in U, φ x * dot (G₁ x) (g₁ x)) - ∫ x in U, φ x * dot (G₂ x) (g₂ x) := by
      rw [← integral_sub hI1 hI2]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      ring
    have hsa : ∑ i, a i = (∫ x in U, (u₁ x - c₁) * dot (gradient φ x) (g₁ x)) -
        ∫ x in U, (u₁ x - c₁) * dot (gradient φ x) (g₂ x) := by
      rw [hX1, hX2, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => ha_split i
    have hsb : ∑ i, b i = (∫ x in U, u₁ x * dot (gradient φ x) (g₂ x)) -
        ∫ x in U, u₂ x * dot (gradient φ x) (g₂ x) := by
      rw [hX3, hX4, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => hb_split i
    rw [hI, hK1, hK4, hsa, hsb]
    linarith [hK2, hK3]
  -- conclusion
  have hsum : |∫ x in U, (dot (G₁ x) (g₁ x) - dot (G₂ x) (g₂ x)) * φ x| ≤
      (volume U).toReal * (K₁ * D * N1.toReal * ∑ i, (Hn i).toReal +
        d * (Nu.toReal * (M * Ng.toReal))) := by
    rw [hmain, abs_neg]
    refine (abs_add_le _ _).trans ?_
    have hA : |∑ i, a i| ≤ ∑ i, (volume U).toReal * ((Hn i).toReal * (K₁ * D * N1.toReal)) :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ha_le i)
    have hB : |∑ i, b i| ≤ ∑ _i : Fin d, (volume U).toReal * (Nu.toReal * (M * Ng.toReal)) :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hb_le i)
    refine (add_le_add hA hB).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum,
      Finset.mul_sum, Finset.mul_sum]
    rw [mul_add, Finset.mul_sum]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => by ring) (by ring)
  have hN1r := ENNReal.toReal_nonneg (a := N1)
  have hNgr := ENNReal.toReal_nonneg (a := Ng)
  have hNur := ENNReal.toReal_nonneg (a := Nu)
  have hHr : 0 ≤ ∑ i, (Hn i).toReal := Finset.sum_nonneg fun i _ => ENNReal.toReal_nonneg
  have hbound : |⨍ x in U, (dot (G₁ x) (g₁ x) - dot (G₂ x) (g₂ x)) * φ x| ≤
      (K₁ + 2 * cM * d ^ 2 + 1) * D * (N1.toReal * ∑ i, (Hn i).toReal + Ng.toReal * Nu.toReal) := by
    rw [setAverage_eq, smul_eq_mul, measureReal_def, abs_mul, abs_of_pos (inv_pos.2 hV)]
    calc (volume U).toReal⁻¹ * |∫ x in U, (dot (G₁ x) (g₁ x) - dot (G₂ x) (g₂ x)) * φ x|
        ≤ (volume U).toReal⁻¹ * ((volume U).toReal * (K₁ * D * N1.toReal * ∑ i, (Hn i).toReal +
            d * (Nu.toReal * (M * Ng.toReal)))) :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hV.le)
      _ = K₁ * D * N1.toReal * ∑ i, (Hn i).toReal + 2 * cM * d ^ 2 * D * (Ng.toReal * Nu.toReal) := by
          rw [← mul_assoc, inv_mul_cancel₀ hV.ne', one_mul, hMdef]
          ring
      _ ≤ (K₁ + 2 * cM * d ^ 2 + 1) * D * (N1.toReal * ∑ i, (Hn i).toReal +
            Ng.toReal * Nu.toReal) := by
          have h1 : 0 ≤ D * (N1.toReal * ∑ i, (Hn i).toReal) := by positivity
          have h2 : 0 ≤ D * (Ng.toReal * Nu.toReal) := by positivity
          have hc2 : (0 : ℝ) ≤ 2 * cM * d ^ 2 := by positivity
          nlinarith [mul_nonneg hK₁0 h2, mul_nonneg hc2 h1, h1, h2]
  calc ENNReal.ofReal |⨍ x in U, (dot (G₁ x) (g₁ x) - dot (G₂ x) (g₂ x)) * φ x|
      ≤ ENNReal.ofReal ((K₁ + 2 * cM * d ^ 2 + 1) * D *
          (N1.toReal * ∑ i, (Hn i).toReal + Ng.toReal * Nu.toReal)) :=
        ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal ((K₁ + 2 * cM * d ^ 2 + 1) * D) *
          (N1 * vectorNegativeSobolevOneNorm 2 U (fun x => g₁ x - g₂ x) + Ng * Nu) := by
        rw [ENNReal.ofReal_mul (by positivity), hvec, ENNReal.ofReal_add (by positivity)
          (by positivity), ENNReal.ofReal_mul hN1r, ENNReal.ofReal_mul hNgr,
          ENNReal.ofReal_toReal hN1, ENNReal.ofReal_toReal hNg, ENNReal.ofReal_toReal hNu,
          ENNReal.ofReal_sum_of_nonneg fun i _ => ENNReal.toReal_nonneg]
        congr 3
        exact Finset.sum_congr rfl fun i _ => ENNReal.ofReal_toReal (hHfin i)

/-- **Lemma 1.16** (div-curl lemma): for `d ≥ 2`, a bounded open convex `U` and
`q ∈ [1, d/(d-1))` there is `C(U, q, d)` such that for `u₁, u₂ ∈ H¹(U)` with gradients `G₁, G₂`
and `g₁, g₂ ∈ L²_sol(U)`,
`‖G₁ · g₁ - G₂ · g₂‖_{W̲^{-2,q}(U)} ≤ C (‖G₁‖_{L̲²(U)} ‖g₁ - g₂‖_{H̲^{-1}(U)} +
‖g₂‖_{L̲²(U)} ‖u₁ - u₂‖_{L̲²(U)})`, (1.54). -/
theorem lemma_1_16 (hd : 2 ≤ d) {U : Set (Vec d)} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) {q : ℝ} (hq : 1 ≤ q)
    (hqd : q < d / (d - 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u₁ u₂ : Vec d → ℝ) (G₁ G₂ g₁ g₂ : Vec d → Vec d),
      H1 U u₁ G₁ → H1 U u₂ G₂ → IsL2Sol U g₁ → IsL2Sol U g₂ →
      negativeSobolevTwoNorm (ENNReal.ofReal q) U
          (fun x => dot (G₁ x) (g₁ x) - dot (G₂ x) (g₂ x)) ≤
        ENNReal.ofReal C *
          (PDE.eLpMeanNormOn U 2 (fun x => euclideanNorm (G₁ x)) *
              vectorNegativeSobolevOneNorm 2 U (fun x => g₁ x - g₂ x) +
            PDE.eLpMeanNormOn U 2 (fun x => euclideanNorm (g₂ x)) *
              PDE.eLpMeanNormOn U 2 (fun x => u₁ x - u₂ x)) := by
  rcases U.eq_empty_or_nonempty with hU | hne
  · refine ⟨1, one_pos, fun u₁ u₂ G₁ G₂ g₁ g₂ _ _ _ _ => ?_⟩
    refine (negativeSobolevTwoNorm_le (B := 0) fun ψ _ _ => by simp [hU]).trans zero_le
  obtain ⟨D, hD, hDU⟩ := exists_hasEuclideanDiameterLE hUb
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  have hUt : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hV : 0 < (volume U).toReal := ENNReal.toReal_pos hU0 hUt
  obtain ⟨C, hC, h⟩ := lemma_1_16_quantitative hd hq hqd
    (κ := (volume U).toReal / D ^ d) (by positivity)
  refine ⟨C * D, mul_pos hC hD, fun u₁ u₂ G₁ G₂ g₁ g₂ hu₁ hu₂ hg₁ hg₂ => ?_⟩
  refine h U D hUo hUc hne hD hDU (le_of_eq ?_) u₁ u₂ G₁ G₂ g₁ g₂ hu₁ hu₂ hg₁ hg₂
  rw [div_mul_cancel₀ _ (by positivity), ENNReal.ofReal_toReal hUt]

end QSH
