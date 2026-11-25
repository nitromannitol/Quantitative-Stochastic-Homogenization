import QuantitativeStochasticHomogenization.AppD.PropositionD1Fractional

/-!
# Appendix D: Proposition D.1 for derivatives of `L^p` functions, and Proposition D.5

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix D, Proposition D.5: for `q ∈ (1, ∞)`, `k ∈ ℕ` and `α ∈ (0, ∞) \ ℕ` with `α < k`,
`‖u‖_{W^{α,q}(ℝ^d)} ≤ C ‖u‖_{L^q(ℝ^d)} + C (∫_0^1 (t^{(k-α)/2} ‖∇^k Φ(t, ·) ∗ u‖_{L^q(ℝ^d)})^q dt/t)^{1/q}`.

The book's proof applies the first inequality of (D.2) to the distribution `∇^k u ∈ W^{α-k,q}(ℝ^d)`
after the observation `‖u‖_{W^{α,q}} ≤ C ‖u‖_{L^q} + ‖∇^k u‖_{W^{α-k,q}}`, which it does not prove.

This file proves the first inequality of (D.2) for a derivative `∂^l u` of `u ∈ L^p(ℝ^d)`
(`propositionD1_fractional_foldr`), with the norm `sup |∫ u ∂^l g|` of `∂^l u` in
`W^{-(m+β),p}(ℝ^d)` (`negativeFractionalSobolevNormDeriv`): `propositionD1_fractional` is applied to
`v_ε = ∂^l Φ(ε, ·) ∗ u ∈ L^p`, for which `∫ v_ε g = ± ∫ u (Φ(ε) ∗ ∂^l g)` (the parity of the
derivatives of the heat kernel, `heatKernelDeriv_neg`) and `Φ(t) ∗ v_ε = Φ(ε) ∗ (∂^l Φ(t, ·) ∗ u)`
(`heatSmooth_kconv_heatKernelDeriv`), whose `L^p` norm is at most that of `∂^l Φ(t, ·) ∗ u`; then
`ε → 0` by dominated convergence (`tendsto_integral_mul_heatSmooth`). Proposition D.5 follows from
the book's observation, taken as a hypothesis (`propositionD5_fractional_of_lifting`).
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff Convolution Nat

noncomputable section

namespace QSH

variable {d : ℕ}

/-! ## The parity of the derivatives of the heat kernel -/

theorem coordinateDerivative_comp_neg {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin d)
    (z : Vec d) :
    coordinateDerivative i (fun y => f (-y)) z = -coordinateDerivative i f (-z) := by
  have h1 : HasFDerivAt (fun y : Vec d => -y) (-ContinuousLinearMap.id ℝ (Vec d)) z :=
    (hasFDerivAt_id z).neg
  have h2 : HasFDerivAt (fun y => f (-y))
      ((fderiv ℝ f (-z)).comp (-ContinuousLinearMap.id ℝ (Vec d))) z :=
    ((hf.differentiable (by simp) (-z)).hasFDerivAt).comp z h1
  unfold coordinateDerivative
  rw [h2.fderiv]
  simp

theorem coordinateDerivative_const_mul {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℝ) (i : Fin d)
    (z : Vec d) :
    coordinateDerivative i (fun y => c * f y) z = c * coordinateDerivative i f z := by
  unfold coordinateDerivative
  rw [fderiv_const_mul (hf.differentiable (by simp) z) c]
  simp

/-- `∂^l Φ(t, -z) = (-1)^{|l|} ∂^l Φ(t, z)`. -/
theorem heatKernelDeriv_neg (t : ℝ) (l : List (Fin d)) :
    (fun z => heatKernelDeriv t l (-z)) = fun z => (-1) ^ l.length * heatKernelDeriv t l z := by
  induction l with
  | nil =>
    funext z
    simp [heatKernelDeriv, euclideanHeatKernel_neg]
  | cons i l ih =>
    funext z
    have hs := contDiff_heatKernelDeriv (d := d) t l
    have h1 := coordinateDerivative_comp_neg hs i z
    rw [ih, coordinateDerivative_const_mul hs] at h1
    show coordinateDerivative i (heatKernelDeriv t l) (-z) =
      (-1) ^ (l.length + 1) * coordinateDerivative i (heatKernelDeriv t l) z
    rw [pow_succ]
    linear_combination h1

/-! ## The heat flow of `∂^l Φ(b, ·) ∗ u` -/

theorem abs_heatKernelDeriv_le_heatKernel {b : ℝ} (hb : 0 < b) (l : List (Fin d)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z, |heatKernelDeriv b l z| ≤ M * euclideanHeatKernel (2 * b) z := by
  obtain ⟨C, hC, h⟩ := abs_heatKernelDeriv_ofFn_le (d := d) l.get
  refine ⟨C * (Real.sqrt (2 * b))⁻¹ ^ l.length, by positivity, fun z => ?_⟩
  have := h b hb z
  rwa [List.ofFn_get] at this

theorem integrable_heatKernel_prod_of_memLp {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {p : ℝ}
    (hp : 1 ≤ p) {u : Vec d → ℝ} (hu : MemLp u (ENNReal.ofReal p) volume) (x : Vec d) :
    Integrable (fun q : Vec d × Vec d =>
      euclideanHeatKernel a (x - q.1) * (euclideanHeatKernel b (q.1 - q.2) * u q.2))
      (volume.prod volume) := by
  have hsg : ∀ z, euclideanHeatKernel (d := d) (a + b) (x - z) =
      ∫ y, euclideanHeatKernel a (x - y) * euclideanHeatKernel b (y - z) := fun z => by
    have h := foldr_euclideanHeatKernel_semigroup (d := d) ha hb [] x z
    simpa using h
  set F : Vec d × Vec d → ℝ := fun q =>
    euclideanHeatKernel a (x - q.1) * (euclideanHeatKernel b (q.1 - q.2) * u q.2) with hF
  have hm : AEStronglyMeasurable F (volume.prod volume) := by
    refine (((continuous_euclideanHeatKernel a).comp
      (continuous_const.sub continuous_fst)).aestronglyMeasurable).mul
      ((((continuous_euclideanHeatKernel b).comp
        (continuous_fst.sub continuous_snd)).aestronglyMeasurable).mul ?_)
    exact hu.aestronglyMeasurable.comp_snd
  refine ⟨hm, ?_⟩
  have hint := integrable_euclideanHeatKernel_mul_of_memLp (add_pos ha hb) hp hu x
  rw [HasFiniteIntegral, lintegral_prod_symm _ hm.enorm]
  have hz : ∀ z, ∫⁻ y, ‖F (y, z)‖ₑ = ENNReal.ofReal (euclideanHeatKernel (a + b) (x - z)) *
      ‖u z‖ₑ := fun z => by
    simp only [hF, enorm_mul]
    have hnn : ∀ w, ‖euclideanHeatKernel (d := d) a w‖ₑ = ENNReal.ofReal (euclideanHeatKernel a w) :=
      fun w => Real.enorm_of_nonneg (euclideanHeatKernel_nonneg ha.le w)
    have hnn' : ∀ w, ‖euclideanHeatKernel (d := d) b w‖ₑ = ENNReal.ofReal (euclideanHeatKernel b w) :=
      fun w => Real.enorm_of_nonneg (euclideanHeatKernel_nonneg hb.le w)
    simp_rw [hnn, hnn', ← mul_assoc]
    rw [lintegral_mul_const' _ _ enorm_ne_top, hsg z]
    congr 1
    rw [ofReal_integral_eq_lintegral_ofReal]
    · refine lintegral_congr fun y => ?_
      rw [ENNReal.ofReal_mul (euclideanHeatKernel_nonneg ha.le _)]
    · exact ((integrable_euclideanHeatKernel ha).comp_sub_left x).mul_of_top_left
        (memLp_top_of_bound ((continuous_euclideanHeatKernel b).comp
          (continuous_id.sub continuous_const)).aestronglyMeasurable
          ((4 * Real.pi * b) ^ (-(d : ℝ) / 2)) (Eventually.of_forall fun y => by
            rw [Real.norm_of_nonneg (euclideanHeatKernel_nonneg hb.le _)]
            exact euclideanHeatKernel_le_const hb _))
    · exact Eventually.of_forall fun y => mul_nonneg (euclideanHeatKernel_nonneg ha.le _)
        (euclideanHeatKernel_nonneg hb.le _)
  simp_rw [hz]
  have h2 := hint.hasFiniteIntegral
  rw [HasFiniteIntegral] at h2
  refine lt_of_eq_of_lt (lintegral_congr fun z => ?_) h2
  rw [enorm_mul, Real.enorm_of_nonneg (euclideanHeatKernel_nonneg (add_pos ha hb).le _)]

/-- **The semigroup property for the derivatives of the heat kernel on `L^p`**:
`Φ(a) ∗ (∂^l Φ(b, ·) ∗ u) = ∂^l Φ(a + b, ·) ∗ u`. -/
theorem heatSmooth_kconv_heatKernelDeriv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {p : ℝ} (hp : 1 ≤ p)
    {u : Vec d → ℝ} (hu : MemLp u (ENNReal.ofReal p) volume) (l : List (Fin d)) (x : Vec d) :
    heatSmooth a (kconv (heatKernelDeriv b l) u) x = kconv (heatKernelDeriv (a + b) l) u x := by
  have hsg : ∀ z, heatKernelDeriv (a + b) l (x - z) =
      ∫ y, euclideanHeatKernel a (x - y) * heatKernelDeriv b l (y - z) := fun z => by
    have h := foldr_euclideanHeatKernel_semigroup (d := d) hb ha l x z
    calc heatKernelDeriv (a + b) l (x - z)
        = ∫ y, l.foldr coordinateDerivative (euclideanHeatKernel (d := d) b) (x - y) *
            euclideanHeatKernel a (y - z) := by
          rw [add_comm a b]
          exact h
      _ = ∫ y, (fun y => l.foldr coordinateDerivative (euclideanHeatKernel (d := d) b) (x - y) *
            euclideanHeatKernel a (y - z)) (x + z - y) :=
          (integral_sub_left_eq_self _ volume (x + z)).symm
      _ = ∫ y, euclideanHeatKernel a (x - y) * heatKernelDeriv b l (y - z) := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          simp only [heatKernelDeriv]
          rw [mul_comm, show x - (x + z - y) = y - z by abel, show x + z - y - z = x - y by abel]
  obtain ⟨M, hM, hMb⟩ := abs_heatKernelDeriv_le_heatKernel hb l
  set F : Vec d × Vec d → ℝ := fun q =>
    euclideanHeatKernel a (x - q.1) * (heatKernelDeriv b l (q.1 - q.2) * u q.2) with hF
  have hFi : Integrable F (volume.prod volume) := by
    have hG := (integrable_heatKernel_prod_of_memLp ha (by positivity : (0 : ℝ) < 2 * b) hp
      hu.norm x).const_mul M
    refine hG.mono' ?_ (Eventually.of_forall fun q => ?_)
    · exact (((continuous_euclideanHeatKernel a).comp
        (continuous_const.sub continuous_fst)).aestronglyMeasurable).mul
        ((((continuous_heatKernelDeriv b l).comp
          (continuous_fst.sub continuous_snd)).aestronglyMeasurable).mul
          hu.aestronglyMeasurable.comp_snd)
    · simp only [hF]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (euclideanHeatKernel_nonneg ha.le _),
        ← Real.norm_eq_abs (u q.2)]
      have h0 := euclideanHeatKernel_nonneg (d := d) ha.le (x - q.1)
      calc euclideanHeatKernel a (x - q.1) * (|heatKernelDeriv b l (q.1 - q.2)| * ‖u q.2‖)
          ≤ euclideanHeatKernel a (x - q.1) *
              (M * euclideanHeatKernel (2 * b) (q.1 - q.2) * ‖u q.2‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hMb _) (norm_nonneg _)) h0
        _ = M * (euclideanHeatKernel a (x - q.1) *
              (euclideanHeatKernel (2 * b) (q.1 - q.2) * ‖u q.2‖)) := by ring
  rw [heatSmooth_eq_kconv, kconv_apply, kconv_apply]
  calc ∫ y, euclideanHeatKernel a (x - y) * kconv (heatKernelDeriv b l) u y
      = ∫ y, ∫ z, F (y, z) := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [hF]
        rw [kconv_apply, integral_const_mul]
    _ = ∫ z, ∫ y, F (y, z) := integral_integral_swap hFi
    _ = ∫ z, heatKernelDeriv (a + b) l (x - z) * u z := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only [hF]
        rw [hsg z, ← integral_mul_const]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only
        ring

theorem memLp_kconv_heatKernelDeriv {t : ℝ} (ht : 0 < t) {p : ℝ} (hp : 1 < p) {u : Vec d → ℝ}
    (hu : MemLp u (ENNReal.ofReal p) volume) (l : List (Fin d)) :
    MemLp (kconv (heatKernelDeriv t l) u) (ENNReal.ofReal p) volume :=
  (memLp_kconv_of_memLp hp (integrable_heatKernelDeriv ht l)
    (continuous_heatKernelDeriv t l).measurable hu).1

/-- `‖∂^l Φ(s + t, ·) ∗ u‖_{L^p} ≤ ‖∂^l Φ(t, ·) ∗ u‖_{L^p}`. -/
theorem lintegral_kconv_heatKernelDeriv_add_le {s t : ℝ} (hs : 0 < s) (ht : 0 < t) {p : ℝ}
    (hp : 1 < p) {u : Vec d → ℝ} (hu : MemLp u (ENNReal.ofReal p) volume) (l : List (Fin d)) :
    ∫⁻ x, ‖kconv (heatKernelDeriv (s + t) l) u x‖ₑ ^ p ≤
      ∫⁻ x, ‖kconv (heatKernelDeriv t l) u x‖ₑ ^ p := by
  have hp0 : 0 < p := by linarith
  have hp0' : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have h1 : kconv (heatKernelDeriv (s + t) l) u = heatSmooth s (kconv (heatKernelDeriv t l) u) :=
    funext fun x => (heatSmooth_kconv_heatKernelDeriv hs ht hp.le hu l x).symm
  have h2 := (memLp_heatSmooth_of_memLp hs hp (memLp_kconv_heatKernelDeriv ht hp hu l)).2
  rw [← h1, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0' ENNReal.ofReal_ne_top
      (memLp_kconv_heatKernelDeriv (add_pos hs ht) hp hu l).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0' ENNReal.ofReal_ne_top
      (memLp_kconv_heatKernelDeriv ht hp hu l).aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le] at h2
  exact (ENNReal.rpow_le_rpow_iff (by positivity)).mp h2

/-! ## The pairing with a derivative and the limit `ε → 0` -/

/-- `∫ u (Φ(ε) ∗ ∂^l g) = (-1)^{|l|} ∫ (∂^l Φ(ε, ·) ∗ u) g`. -/
theorem integral_mul_heatSmooth_foldr_eq {ε : ℝ} (hε : 0 < ε) {p : ℝ} (hp : 1 < p)
    {u : Vec d → ℝ} (hu : MemLp u (ENNReal.ofReal p) volume) {g : Vec d → ℝ}
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (l : List (Fin d)) :
    ∫ x, u x * heatSmooth ε (l.foldr coordinateDerivative g) x =
      (-1) ^ l.length * ∫ y, kconv (heatKernelDeriv ε l) u y * g y := by
  have h1 : heatSmooth ε (l.foldr coordinateDerivative g) =
      (l.reverse.foldr coordinateDerivative (euclideanHeatKernel ε)) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume] g :=
    convolution_foldr_coordinateDerivative hg hcg l (contDiff_euclideanHeatKernel ε)
  have hperm : l.reverse.foldr coordinateDerivative (euclideanHeatKernel (d := d) ε) =
      heatKernelDeriv ε l :=
    foldr_coordinateDerivative_perm (contDiff_euclideanHeatKernel ε) (List.reverse_perm l)
  rw [h1, integral_mul_convolution_eq hε l.reverse hu.aestronglyMeasurable
    (integrable_mul_euclideanHeatKernel_of_memLp (by positivity) hp.le hu) hg.continuous hcg,
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  have hpar : ∀ x : Vec d, heatKernelDeriv ε l (x - y) =
      (-1) ^ l.length * heatKernelDeriv ε l (y - x) := fun x => by
    have := congrFun (heatKernelDeriv_neg ε l) (y - x)
    simp only [neg_sub] at this
    exact this
  rw [hperm, kconv_apply]
  simp_rw [hpar]
  rw [show (fun x => u x * ((-1) ^ l.length * heatKernelDeriv ε l (y - x))) =
      fun x => (-1) ^ l.length * (heatKernelDeriv ε l (y - x) * u x) from
    funext fun x => by ring, integral_const_mul]
  ring

/-- `∫ u (Φ(ε) ∗ ψ) → ∫ u ψ` as `ε → 0⁺`, for `u ∈ L^p` and a test `ψ`. -/
theorem tendsto_integral_mul_heatSmooth {p : ℝ} (hp : 1 ≤ p) {u : Vec d → ℝ}
    (hu : MemLp u (ENNReal.ofReal p) volume) {ψ : Vec d → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) :
    Tendsto (fun ε => ∫ x, u x * heatSmooth ε ψ x) (𝓝[>] 0) (𝓝 (∫ x, u x * ψ x)) := by
  obtain ⟨R, hR⟩ := hcψ.isCompact.isBounded.exists_norm_le
  obtain ⟨M, hM'⟩ := hψ.continuous.bounded_above_of_compact_support hcψ
  have hM : ∀ z, |ψ z| ≤ M := fun z => by
    rw [← Real.norm_eq_abs]
    exact hM' z
  have hR0 : 0 ≤ max R 0 := le_max_right _ _
  have hsupp : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ max R 0 := fun z hz =>
    (hR z (subset_tsupport _ hz)).trans (le_max_left _ _)
  have hF := integrable_mul_exp_neg_norm_sq_of_memLp hp hu
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => ‖u x * Real.exp (-(‖x‖ ^ 2) / 16)‖ *
      (M * 2 ^ ((d : ℝ) / 2) * Real.exp (max R 0 ^ 2 / 8))) ?_ ?_ ?_ ?_
  · filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with ε hε
    exact (integrable_mul_heatSmooth_ball hR0 hu.aestronglyMeasurable hF hψ.continuous.measurable
      hM hsupp hε.1 hε.2).aestronglyMeasurable
  · filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with ε hε
    refine Eventually.of_forall fun x => ?_
    have h := abs_heatSmooth_le_exp_ball hR0 hε.1 hε.2 hM hsupp x
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |u x| * |heatSmooth ε ψ x|
        ≤ |u x| * (M * 2 ^ ((d : ℝ) / 2) * Real.exp (max R 0 ^ 2 / 8) *
            Real.exp (-(‖x‖ ^ 2) / 16)) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = _ := by ring
  · exact hF.norm.mul_const _
  · exact Eventually.of_forall fun x =>
      (tendsto_heatSmooth_zero hψ.continuous hcψ x).const_mul (u x)

/-! ## Proposition D.1 for `∂^l u` -/

/-- The norm of `∂^l u` in `W^{-(m+β),p}(ℝ^d)` for `u ∈ L^p(ℝ^d)`: the supremum of `|∫ u ∂^l g|`
over `g ∈ C_c^∞(ℝ^d)` with `‖g‖_{W^{m+β,p/(p-1)}(ℝ^d)} ≤ 1` (the pairing `⟨∂^l u, g⟩` is
`(-1)^{|l|} ∫ u ∂^l g`). -/
def negativeFractionalSobolevNormDeriv (m : ℕ) (β p : ℝ) (l : List (Fin d)) (u : Vec d → ℝ) :
    ℝ≥0∞ :=
  ⨆ g : {g : Vec d → ℝ // ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      fractionalSobolevNorm m β (p / (p - 1)) g ≤ 1},
    ENNReal.ofReal |∫ x, u x * l.foldr coordinateDerivative g.1 x|

/-- **Proposition D.1, the first inequality of (D.2), for `∂^l u`**: for `p ∈ (1, ∞)` and
`α = m + β`, `β ∈ (0, 1)`, there is `C` such that for every `u ∈ L^p(ℝ^d)` and every list of
coordinates `l`, `‖∂^l u‖_{W^{-α,p}(ℝ^d)} ≤ C (∫_0^1 (t^{α/2} ‖∂^l Φ(t, ·) ∗ u‖_{L^p})^p dt/t)^{1/p}`. -/
theorem propositionD1_fractional_foldr (m : ℕ) {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) {p : ℝ}
    (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (l : List (Fin d)) (u : Vec d → ℝ), MemLp u (ENNReal.ofReal p) volume →
      negativeFractionalSobolevNormDeriv m β p l u ≤ ENNReal.ofReal C *
        (∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (p * (m + β) / 2) / t) *
          ∫⁻ x, ‖kconv (heatKernelDeriv t l) u x‖ₑ ^ p) ^ (1 / p) := by
  obtain ⟨C, hC, hD1⟩ := propositionD1_fractional (d := d) m hβ hβ1 hp
  refine ⟨C, hC, fun l u hu => ?_⟩
  unfold negativeFractionalSobolevNormDeriv
  refine iSup_le ?_
  rintro ⟨g, hg, hcg, hgn⟩
  dsimp only
  have hψ := foldr_coordinateDerivative_contDiff hg l
  have hcψ := hasCompactSupport_foldr_coordinateDerivative hcg l
  have hlim := tendsto_integral_mul_heatSmooth hp.le hu hψ hcψ
  have hlim' : Tendsto (fun ε =>
      ENNReal.ofReal |∫ x, u x * heatSmooth ε (l.foldr coordinateDerivative g) x|) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal |∫ x, u x * l.foldr coordinateDerivative g x|)) :=
    (ENNReal.continuous_ofReal.tendsto _).comp ((continuous_abs.tendsto _).comp hlim)
  refine le_of_tendsto hlim' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : 0 < ε := hε
  have hv := memLp_kconv_heatKernelDeriv hε0 hp hu l
  rw [integral_mul_heatSmooth_foldr_eq hε0 hp hu hg hcg l, abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, one_mul]
  calc ENNReal.ofReal |∫ y, kconv (heatKernelDeriv ε l) u y * g y|
      ≤ negativeFractionalSobolevNorm m β p (kconv (heatKernelDeriv ε l) u) := by
        unfold negativeFractionalSobolevNorm
        exact le_iSup_of_le ⟨g, hg, hcg, hgn⟩ le_rfl
    _ ≤ ENNReal.ofReal C * (∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (p * (m + β) / 2) / t) *
          ∫⁻ x, ‖heatSmooth t (kconv (heatKernelDeriv ε l) u) x‖ₑ ^ p) ^ (1 / p) := hD1 _ hv
    _ ≤ _ := by
        refine mul_le_mul' le_rfl (ENNReal.rpow_le_rpow ?_ (one_div_nonneg.mpr (by linarith)))
        refine setLIntegral_mono' measurableSet_Ioc fun t ht => mul_le_mul' le_rfl ?_
        have h1 : heatSmooth t (kconv (heatKernelDeriv ε l) u) =
            kconv (heatKernelDeriv (ε + t) l) u := funext fun x => by
          rw [heatSmooth_kconv_heatKernelDeriv ht.1 hε0 hp.le hu l x, add_comm]
        rw [h1]
        exact lintegral_kconv_heatKernelDeriv_add_le hε0 ht.1 hp hu l

/-! ## Proposition D.5 -/

/-- The norm (B.3) of `W^{m+β,q}(ℝ^d)` of `u ∈ W^{m,q}(ℝ^d)` given with its weak derivatives `G`:
`∑_{j ≤ m} ∑_{|w| = j} ‖G w‖_{L^q(ℝ^d)} + ∑_{|w| = m} [G w]_{W^{β,q}(ℝ^d)}`. -/
def fractionalSobolevFamilyNorm (m : ℕ) (β q : ℝ) (G : List (Fin d) → Vec d → ℝ) : ℝ≥0∞ :=
  (∑ j ∈ Finset.range (m + 1), ∑ w : Fin j → Fin d,
      eLpNorm (G (List.ofFn w)) (ENNReal.ofReal q) volume) +
    fractionalSobolevSeminorm m β q G

/-- **Proposition D.5 for `α ∉ ℕ`, from the observation of its proof**: for `q ∈ (1, ∞)`,
`α = m + β` with `β ∈ (0, 1)` and `k ∈ ℕ` with `α < k`, if
`‖u‖_{W^{α,q}(ℝ^d)} ≤ C₀ (‖u‖_{L^q(ℝ^d)} + ∑_{|w| = k} ‖∂_w u‖_{W^{α-k,q}(ℝ^d)})` for every
`u ∈ W^{α,q}(ℝ^d)` (the book's observation, not proved in the book), then
`‖u‖_{W^{α,q}(ℝ^d)} ≤ C ‖u‖_{L^q(ℝ^d)} + C (∫_0^1 (t^{(k-α)/2} ‖∇^k Φ(t, ·) ∗ u‖_{L^q(ℝ^d)})^q dt/t)^{1/q}`. -/
theorem propositionD5_fractional_of_lifting (m : ℕ) {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) {k : ℕ}
    (hk : m < k) {q : ℝ} (hq : 1 < q)
    (hlift : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (u : Vec d → ℝ) (G : List (Fin d) → Vec d → ℝ),
      IsSobolevFamilyLp q m u G →
      fractionalSobolevFamilyNorm m β q G ≤ ENNReal.ofReal C₀ *
        (eLpNorm u (ENNReal.ofReal q) volume +
          ∑ w : Fin k → Fin d, negativeFractionalSobolevNormDeriv (k - m - 1) (1 - β) q
            (List.ofFn w) u)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Vec d → ℝ) (G : List (Fin d) → Vec d → ℝ),
      IsSobolevFamilyLp q m u G →
      fractionalSobolevFamilyNorm m β q G ≤ ENNReal.ofReal C * eLpNorm u (ENNReal.ofReal q) volume +
        ENNReal.ofReal C * (∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (q * (k - (m + β)) / 2) / t) *
          ∫⁻ x, ENNReal.ofReal (Real.sqrt (heatGradSq k t u x)) ^ q) ^ (1 / q) := by
  obtain ⟨C₀, hC₀, hl⟩ := hlift
  obtain ⟨C₁, hC₁, hD1⟩ := propositionD1_fractional_foldr (d := d) (k - m - 1) (sub_pos.mpr hβ1)
    (by linarith : 1 - β < 1) hq
  have hq0 : 0 < q := by linarith
  have hcast : ((k - m - 1 : ℕ) : ℝ) = (k : ℝ) - m - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k - m), Nat.cast_sub hk.le, Nat.cast_one]
  have hexp : ((k - m - 1 : ℕ) : ℝ) + (1 - β) = k - (m + β) := by
    rw [hcast]
    ring
  refine ⟨C₀ * (1 + (d : ℝ) ^ k * C₁), by positivity, fun u G hS => ?_⟩
  have hu : MemLp u (ENNReal.ofReal q) volume := by
    have h := hS.memLp [] (Nat.zero_le _)
    rwa [hS.nil] at h
  set Rr := (∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (q * (k - (m + β)) / 2) / t) *
    ∫⁻ x, ENNReal.ofReal (Real.sqrt (heatGradSq k t u x)) ^ q) ^ (1 / q) with hRr
  have hw : ∀ w : Fin k → Fin d,
      negativeFractionalSobolevNormDeriv (k - m - 1) (1 - β) q (List.ofFn w) u ≤
        ENNReal.ofReal C₁ * Rr := by
    intro w
    refine (hD1 (List.ofFn w) u hu).trans (mul_le_mul' le_rfl
      (ENNReal.rpow_le_rpow ?_ (one_div_nonneg.mpr hq0.le)))
    rw [hexp]
    refine setLIntegral_mono' measurableSet_Ioc fun t _ => mul_le_mul' le_rfl
      (lintegral_mono fun x => ENNReal.rpow_le_rpow ?_ hq0.le)
    rw [Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    have h := sq_kconv_heatKernelDeriv_le_heatGradSq t u (List.ofFn w) x
    rwa [List.length_ofFn] at h
  have hsum : ∑ _w : Fin k → Fin d, ENNReal.ofReal C₁ * Rr =
      (d : ℝ≥0∞) ^ k * (ENNReal.ofReal C₁ * Rr) := by
    simp [Finset.card_univ]
  have hle1 : C₀ ≤ C₀ * (1 + (d : ℝ) ^ k * C₁) :=
    le_mul_of_one_le_right hC₀ (le_add_of_nonneg_right (by positivity))
  have hle2 : C₀ * ((d : ℝ) ^ k * C₁) ≤ C₀ * (1 + (d : ℝ) ^ k * C₁) :=
    mul_le_mul_of_nonneg_left (by linarith) hC₀
  calc fractionalSobolevFamilyNorm m β q G
      ≤ ENNReal.ofReal C₀ * (eLpNorm u (ENNReal.ofReal q) volume +
          ∑ w : Fin k → Fin d, negativeFractionalSobolevNormDeriv (k - m - 1) (1 - β) q
            (List.ofFn w) u) := hl u G hS
    _ ≤ ENNReal.ofReal C₀ * (eLpNorm u (ENNReal.ofReal q) volume +
          ∑ _w : Fin k → Fin d, ENNReal.ofReal C₁ * Rr) :=
        mul_le_mul' le_rfl (add_le_add le_rfl (Finset.sum_le_sum fun w _ => hw w))
    _ = ENNReal.ofReal C₀ * eLpNorm u (ENNReal.ofReal q) volume +
          ENNReal.ofReal (C₀ * ((d : ℝ) ^ k * C₁)) * Rr := by
        rw [hsum, ENNReal.ofReal_mul hC₀, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_pow (Nat.cast_nonneg d), ENNReal.ofReal_natCast]
        ring
    _ ≤ _ := add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal hle1) le_rfl)
        (mul_le_mul' (ENNReal.ofReal_le_ofReal hle2) le_rfl)

end QSH
