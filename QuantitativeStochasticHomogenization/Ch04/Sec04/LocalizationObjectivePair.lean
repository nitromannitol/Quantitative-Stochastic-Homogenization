import QuantitativeStochasticHomogenization.Ch04.Sec04.HarmonicPairSpace

/-!
# The objective `I` of Section 4.4 on the pair space

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.4, p. 155: the objective
`I(w) = ⨍_{B_{S/θ}(z)} (∫_{B_T(z)} Φ(σ²S², x - y) (w(x) - (x - z)_i) dx)² dy`
of the `i`-th coordinate minimization.

The inner integral is the `L²(B_T(z))` inner product of `w - ℓ_i` with the Gaussian
`Φ(σ²S², · - y)`, so it is a continuous affine function of the pair, bounded uniformly in `y`
and continuous in `y`. Hence the objective is a continuous convex nonnegative function on the
pair space; it only depends on the class of the potential.
-/

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace QSH

variable {d : ℕ}

/-! ## The heat kernel -/

/-- The normalization `(4π t²)^{-d/2}` of the heat kernel `Φ(t², ·)`. -/
def heatKernelPeak (d : ℕ) (t : ℝ) : ℝ := (4 * Real.pi * t ^ 2) ^ (-(d : ℝ) / 2)

theorem heatKernel_eq (y : Vec d) (t : ℝ) (x : Vec d) :
    heatKernel y t x = heatKernelPeak d t * Real.exp (-(euclideanSq (x - y)) / (4 * t ^ 2)) :=
  rfl

theorem heatKernelPeak_pos {t : ℝ} (ht : t ≠ 0) : 0 < heatKernelPeak d t := by
  unfold heatKernelPeak
  exact Real.rpow_pos_of_pos (by positivity) _

theorem heatKernel_pos_of_ne (y : Vec d) {t : ℝ} (ht : t ≠ 0) (x : Vec d) : 0 < heatKernel y t x := by
  rw [heatKernel_eq]
  exact mul_pos (heatKernelPeak_pos ht) (Real.exp_pos _)

theorem heatKernel_le_peak (y : Vec d) {t : ℝ} (ht : t ≠ 0) (x : Vec d) :
    heatKernel y t x ≤ heatKernelPeak d t := by
  rw [heatKernel_eq]
  refine mul_le_of_le_one_right (heatKernelPeak_pos ht).le (Real.exp_le_one_iff.2 ?_)
  have := zero_le_euclideanSq (x - y)
  have : 0 < 4 * t ^ 2 := by positivity
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) this.le

theorem abs_heatKernel_le (y : Vec d) {t : ℝ} (ht : t ≠ 0) (x : Vec d) :
    |heatKernel y t x| ≤ heatKernelPeak d t := by
  rw [abs_of_pos (heatKernel_pos_of_ne y ht x)]
  exact heatKernel_le_peak y ht x

theorem heatKernel_ge (y : Vec d) {t : ℝ} (ht : t ≠ 0) {x : Vec d} {R : ℝ}
    (hR : euclideanNorm (x - y) ≤ R) :
    heatKernelPeak d t * Real.exp (-(R ^ 2) / (4 * t ^ 2)) ≤ heatKernel y t x := by
  rw [heatKernel_eq]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (heatKernelPeak_pos ht).le
  have h4 : 0 < 4 * t ^ 2 := by positivity
  rw [div_le_div_iff_of_pos_right h4, neg_le_neg_iff, ← sq_euclideanNorm]
  exact pow_le_pow_left₀ (zero_le_euclideanNorm _) hR 2

theorem continuous_heatKernel (t : ℝ) :
    Continuous fun p : Vec d × Vec d => heatKernel p.1 t p.2 := by
  simp only [heatKernel_eq]
  exact continuous_const.mul (Real.continuous_exp.comp
    (((continuous_euclideanSq.comp (continuous_snd.sub continuous_fst)).neg).div_const _))

theorem continuous_heatKernel_left (t : ℝ) (x : Vec d) :
    Continuous fun y : Vec d => heatKernel y t x :=
  (continuous_heatKernel t).comp (continuous_id.prodMk continuous_const)

theorem continuous_heatKernel_right (y : Vec d) (t : ℝ) :
    Continuous fun x : Vec d => heatKernel y t x :=
  (continuous_heatKernel t).comp (continuous_const.prodMk continuous_id)

/-! ## The Gaussian observation of a pair -/

variable {z : Vec d} {T : ℝ}

theorem memLp_heatKernel (y : Vec d) {t : ℝ} (ht : t ≠ 0) :
    MemLp (fun x => heatKernel y t x) 2 (ballMeasure z T) :=
  memLp_of_continuous_of_bound (continuous_heatKernel_right y t) (abs_heatKernel_le y ht)

/-- The Gaussian `Φ(t², · - y)` as an element of `L²(B_T(z))`. -/
def heatLp (z : Vec d) (T : ℝ) (y : Vec d) {t : ℝ} (ht : t ≠ 0) : Lp ℝ 2 (ballMeasure z T) :=
  (memLp_heatKernel (z := z) (T := T) y ht).toLp _

/-- The uniform bound `‖Φ(t², · - y)‖_{L²(B_T(z))} ≤ |B_T(z)|^{1/2} (4πt²)^{-d/2}`. -/
def heatLpBound (z : Vec d) (T t : ℝ) : ℝ :=
  (measureUnivNNReal (ballMeasure z T) : ℝ) ^ ((2 : ℝ≥0∞).toReal⁻¹) * heatKernelPeak d t

theorem norm_heatLp_le (y : Vec d) {t : ℝ} (ht : t ≠ 0) :
    ‖heatLp z T y ht‖ ≤ heatLpBound z T t := by
  refine Lp.norm_le_of_ae_bound (heatKernelPeak_pos ht).le ?_
  filter_upwards [(memLp_heatKernel (z := z) (T := T) y ht).coeFn_toLp] with x hx
  rw [heatLp, hx, Real.norm_eq_abs]
  exact abs_heatKernel_le y ht x

theorem heatLpBound_nonneg (z : Vec d) (T : ℝ) {t : ℝ} (ht : t ≠ 0) : 0 ≤ heatLpBound z T t :=
  mul_nonneg (by positivity) (heatKernelPeak_pos ht).le

theorem inner_heatLp (y : Vec d) {t : ℝ} (ht : t ≠ 0) (u : Lp ℝ 2 (ballMeasure z T)) :
    ⟪heatLp z T y ht, u⟫_ℝ = ∫ x in ball z T, heatKernel y t x * u x := by
  rw [heatLp, inner_toLp_left]
  exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

theorem abs_inner_heatLp_le (y : Vec d) {t : ℝ} (ht : t ≠ 0) (u : Lp ℝ 2 (ballMeasure z T)) :
    |⟪heatLp z T y ht, u⟫_ℝ| ≤ heatLpBound z T t * ‖u‖ :=
  (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_heatLp_le y ht) (norm_nonneg _))

theorem continuous_inner_heatLp {t : ℝ} (ht : t ≠ 0) (u : Lp ℝ 2 (ballMeasure z T)) :
    Continuous fun y : Vec d => ⟪heatLp z T y ht, u⟫_ℝ := by
  simp_rw [inner_heatLp]
  refine continuous_of_dominated (bound := fun x => heatKernelPeak d t * |u x|)
    (fun y => ((continuous_heatKernel_right y t).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable u)) (fun y => Eventually.of_forall fun x => ?_)
    ((integrableOn_ball_of_Lp u).abs.const_mul _)
    (Eventually.of_forall fun x => (continuous_heatKernel_left t x).mul continuous_const)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_heatKernel_le y ht x) (abs_nonneg _)

/-! ## The coordinate function `ℓ_i` -/

theorem memLp_coordinate (z : Vec d) (T : ℝ) (i : Fin d) :
    MemLp (fun x : Vec d => (x - z) i) 2 (ballMeasure z T) := by
  refine MemLp.of_bound ((continuous_apply i).comp (continuous_id.sub continuous_const)).aestronglyMeasurable
    T ?_
  filter_upwards [ae_restrict_mem (measurableSet_ball z T)] with x hx
  rw [Real.norm_eq_abs]
  exact (abs_coord_le_euclideanNorm (x - z) i).trans hx.le

/-- The coordinate function `ℓ_i(x) = (x - z)_i` as an element of `L²(B_T(z))`. -/
def coordinateLp (z : Vec d) (T : ℝ) (i : Fin d) : Lp ℝ 2 (ballMeasure z T) :=
  (memLp_coordinate z T i).toLp _

/-! ## The objective -/

variable {S σ θ : ℝ}

/-- The objective `I(u - ℓ_i)` of p. 155 at a pair, computed from the representative of `u`. -/
def pairObjective (z : Vec d) (T S σ θ : ℝ) (i : Fin d) (F : PairSpace d z T) : ℝ :=
  localizationObjective z T S σ θ (fun x => F.1 x - (x - z) i)

/-- The objective is congruent under almost everywhere equality on `B_T(z)`. -/
theorem localizationObjective_congr {w w' : Vec d → ℝ} (h : w =ᵐ[ballMeasure z T] w') :
    localizationObjective z T S σ θ w = localizationObjective z T S σ θ w' := by
  unfold localizationObjective
  congr 1
  funext y
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

theorem integral_heatKernel_mul_sub (y : Vec d) (hσS : σ * S ≠ 0) (i : Fin d)
    (F : PairSpace d z T) :
    (∫ x in ball z T, heatKernel y (σ * S) x * (F.1 x - (x - z) i)) =
      ⟪heatLp z T y hσS, F.1 - coordinateLp z T i⟫_ℝ := by
  rw [inner_heatLp]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub F.1 (coordinateLp z T i),
    (memLp_coordinate z T i).coeFn_toLp] with x hx hℓ
  have hℓ' : (coordinateLp z T i : Vec d → ℝ) x = (x - z) i := hℓ
  rw [hx]
  show _ = heatKernel y (σ * S) x * ((F.1 : Vec d → ℝ) x - (coordinateLp z T i : Vec d → ℝ) x)
  rw [hℓ']

theorem pairObjective_eq (hσS : σ * S ≠ 0) (i : Fin d) (F : PairSpace d z T) :
    pairObjective z T S σ θ i F =
      ⨍ y in ball z (S / θ), ⟪heatLp z T y hσS, F.1 - coordinateLp z T i⟫_ℝ ^ 2 := by
  unfold pairObjective localizationObjective
  simp_rw [integral_heatKernel_mul_sub _ hσS]

theorem pairObjective_nonneg (i : Fin d) (F : PairSpace d z T) :
    0 ≤ pairObjective z T S σ θ i F := by
  unfold pairObjective localizationObjective
  rw [setAverage_eq, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.2 measureReal_nonneg) (integral_nonneg fun y => sq_nonneg _)

theorem integrableOn_inner_heatLp_sq (hσS : σ * S ≠ 0) (R : ℝ) (v : Lp ℝ 2 (ballMeasure z T)) :
    IntegrableOn (fun y => ⟪heatLp z T y hσS, v⟫_ℝ ^ 2) (ball z R) volume := by
  have : IsFiniteMeasure (volume.restrict (ball z R)) := isFiniteMeasure_ballMeasure z R
  refine Integrable.of_bound (((continuous_inner_heatLp hσS v).pow 2).aestronglyMeasurable)
    ((heatLpBound z T (σ * S) * ‖v‖) ^ 2) (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_inner_heatLp_le y hσS v) 2

theorem continuous_pairObjective (hσS : σ * S ≠ 0) (i : Fin d) :
    Continuous (pairObjective z T S σ θ i : PairSpace d z T → ℝ) := by
  have heq : (pairObjective z T S σ θ i : PairSpace d z T → ℝ) = fun F =>
      (volume.real (ball z (S / θ)))⁻¹ *
        ∫ y in ball z (S / θ), ⟪heatLp z T y hσS, F.1 - coordinateLp z T i⟫_ℝ ^ 2 := by
    funext F
    rw [pairObjective_eq hσS, setAverage_eq, smul_eq_mul]
  rw [heq]
  refine continuous_const.mul (continuous_iff_continuousAt.2 fun F₀ => ?_)
  have : IsFiniteMeasure (volume.restrict (ball z (S / θ))) :=
    isFiniteMeasure_ballMeasure z (S / θ)
  set M := heatLpBound z T (σ * S)
  refine continuousAt_of_dominated (bound := fun _ => (M * (‖F₀.1 - coordinateLp z T i‖ + 1)) ^ 2)
    (Eventually.of_forall fun F =>
      ((continuous_inner_heatLp hσS _).pow 2).aestronglyMeasurable) ?_
    (integrable_const _) (Eventually.of_forall fun y => ?_)
  · filter_upwards [Metric.ball_mem_nhds F₀ one_pos] with F hF
    refine Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_pow]
    refine pow_le_pow_left₀ (abs_nonneg _) ((abs_inner_heatLp_le y hσS _).trans ?_) 2
    refine mul_le_mul_of_nonneg_left ?_ (heatLpBound_nonneg z T hσS)
    have h1 : ‖F.1 - F₀.1‖ ≤ ‖F - F₀‖ := by
      rw [← Prod.fst_sub]; exact norm_fst_le _
    have h2 : ‖F - F₀‖ < 1 := by rwa [← dist_eq_norm]
    calc ‖F.1 - coordinateLp z T i‖ = ‖(F.1 - F₀.1) + (F₀.1 - coordinateLp z T i)‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ ‖F.1 - F₀.1‖ + ‖F₀.1 - coordinateLp z T i‖ := norm_add_le _ _
      _ ≤ ‖F₀.1 - coordinateLp z T i‖ + 1 := by linarith
  · exact ((continuous_const.inner (continuous_fst.sub continuous_const)).pow 2).continuousAt

theorem convexOn_pairObjective (hσS : σ * S ≠ 0) (i : Fin d) :
    ConvexOn ℝ Set.univ (pairObjective z T S σ θ i : PairSpace d z T → ℝ) := by
  refine ⟨convex_univ, fun F _ G _ s t hs ht hst => ?_⟩
  simp only [pairObjective_eq hσS, setAverage_eq, smul_eq_mul]
  set ℓ := coordinateLp z T i
  have hlin : ∀ y, ⟪heatLp z T y hσS, (s • F + t • G).1 - ℓ⟫_ℝ =
      s * ⟪heatLp z T y hσS, F.1 - ℓ⟫_ℝ + t * ⟪heatLp z T y hσS, G.1 - ℓ⟫_ℝ := by
    intro y
    have : (s • F + t • G).1 - ℓ = s • (F.1 - ℓ) + t • (G.1 - ℓ) := by
      have hℓ : ℓ = s • ℓ + t • ℓ := by rw [← add_smul, hst, one_smul]
      calc (s • F + t • G).1 - ℓ = s • F.1 + t • G.1 - (s • ℓ + t • ℓ) := by rw [← hℓ]; rfl
        _ = s • (F.1 - ℓ) + t • (G.1 - ℓ) := by rw [smul_sub, smul_sub]; abel
    rw [this, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have hpt : ∀ y, ⟪heatLp z T y hσS, (s • F + t • G).1 - ℓ⟫_ℝ ^ 2 ≤
      s * ⟪heatLp z T y hσS, F.1 - ℓ⟫_ℝ ^ 2 + t * ⟪heatLp z T y hσS, G.1 - ℓ⟫_ℝ ^ 2 := by
    intro y
    rw [hlin y]
    have ht' : t = 1 - s := by linarith
    subst ht'
    nlinarith [sq_nonneg (⟪heatLp z T y hσS, F.1 - ℓ⟫_ℝ - ⟪heatLp z T y hσS, G.1 - ℓ⟫_ℝ),
      mul_nonneg hs ht]
  have hF := integrableOn_inner_heatLp_sq hσS (S / θ) (F.1 - ℓ)
  have hG := integrableOn_inner_heatLp_sq hσS (S / θ) (G.1 - ℓ)
  have hFG := integrableOn_inner_heatLp_sq hσS (S / θ) ((s • F + t • G).1 - ℓ)
  have hmono : ∫ y in ball z (S / θ), ⟪heatLp z T y hσS, (s • F + t • G).1 - ℓ⟫_ℝ ^ 2 ≤
      ∫ y in ball z (S / θ), (s * ⟪heatLp z T y hσS, F.1 - ℓ⟫_ℝ ^ 2 +
        t * ⟪heatLp z T y hσS, G.1 - ℓ⟫_ℝ ^ 2) :=
    setIntegral_mono hFG ((hF.const_mul s).add (hG.const_mul t)) hpt
  rw [integral_add (hF.const_mul s) (hG.const_mul t), integral_const_mul,
    integral_const_mul] at hmono
  have hinv : 0 ≤ (volume.real (ball z (S / θ)))⁻¹ := inv_nonneg.2 measureReal_nonneg
  calc (volume.real (ball z (S / θ)))⁻¹ *
        ∫ y in ball z (S / θ), ⟪heatLp z T y hσS, (s • F + t • G).1 - ℓ⟫_ℝ ^ 2
      ≤ (volume.real (ball z (S / θ)))⁻¹ *
        (s * (∫ y in ball z (S / θ), ⟪heatLp z T y hσS, F.1 - ℓ⟫_ℝ ^ 2) +
          t * (∫ y in ball z (S / θ), ⟪heatLp z T y hσS, G.1 - ℓ⟫_ℝ ^ 2)) :=
        mul_le_mul_of_nonneg_left hmono hinv
    _ = s * ((volume.real (ball z (S / θ)))⁻¹ *
          ∫ y in ball z (S / θ), ⟪heatLp z T y hσS, F.1 - ℓ⟫_ℝ ^ 2) +
        t * ((volume.real (ball z (S / θ)))⁻¹ *
          ∫ y in ball z (S / θ), ⟪heatLp z T y hσS, G.1 - ℓ⟫_ℝ ^ 2) := by ring

end QSH
