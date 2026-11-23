import QuantitativeStochasticHomogenization.Ch03.Sec04.UndilatedCorrector
import QuantitativeStochasticHomogenization.Ch03.Sec04.EuclideanNormToLp
import QuantitativeStochasticHomogenization.Ch04.Sec04.TranslatedCorrectorBounds
import QuantitativeStochasticHomogenization.Ch01.Sec03.SubadditiveLimit

/-!
# Existence of the first-order correctors and of the homogenized matrix

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 3.4, Lemma 3.16, and Section 1.3, Definition 1.2: every law satisfying (0.10)-(0.11) has
`HomogenizationData`, given a jointly measurable version of the corrector gradients.

The correctors are the undilated high-contrast correctors `φ_e(x) = 2 Φ_e(x/2)` of
`UndilatedCorrector`. Their gradients are stationary: for `z ∈ ℤ^d` the translate
`x ↦ φ_e(a)(x + z)` is a corrector of `T_z a` (weak gradient, `L²(B_R)`, harmonic, sublinear), and
the Liouville classification of the high-contrast theory on the event of full probability for
`T_z a` identifies its gradient with `∇φ_e(T_z a)` (the uniqueness argument of the proof of
Lemma 3.16). The homogenized matrix and the limit (1.22) are `exists_homogenizedMatrix`.

Definition 3.14 requires the stationary field to be jointly measurable in `(a, x)`; the proof of
Lemma 3.16 does not address this, and the high-contrast theorem exports no measurability of its
corrector gradients. It is the hypothesis `HighContrastCorrectorMeasurable`.
-/

open MeasureTheory Filter Set
open scoped Topology Pointwise

noncomputable section

namespace QSH

open _root_.Homogenization hiding euclideanBall Vec Mat euclideanNorm

open _root_.Homogenization.HighContrast

variable {d : ℕ}

/-- **The existence of homogenization data**: every law satisfying (0.10)-(0.11) has correctors
in every direction and a homogenized matrix with the limit (1.22). -/
def HomogenizationDataExists : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ P : Measure (CoefficientField d Λ),
    LawHypotheses P → Nonempty (HomogenizationData P)

/-- **Joint measurability of the corrector gradients**: for every law and every package of
correctors of the dilated law, the undilated corrector gradient `(a, x) ↦ ∇Φ_e(b)(x/2)`,
`b = a(2·)`, has a version which is measurable for the product of the σ-algebra (0.8) and the
Borel σ-algebra, as Definition 3.14 requires of a stationary random field. -/
def HighContrastCorrectorMeasurable : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (Λ : ℝ) (hΛ : 1 ≤ Λ) (P : Measure (CoefficientField d Λ)),
    LawHypotheses P → ∀ (κ C : ℝ) (pk : HighContrastCorrectorPackage hΛ P κ C) (e : Vec d),
      ∃ G : CoefficientField d Λ × Vec d → Vec d, Measurable G ∧
        ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)),
          G (a, x) = undilatedGradient (pk.gradPhi e (toHighContrast hΛ a)) x

/-! ## Identification of a corrector at one realization -/

/-- **Uniqueness of correctors** at one coefficient field on the event of full probability: the
dilated gradient of a sublinear corrector of slope `e` is the high-contrast corrector gradient. -/
theorem dilatedGradient_ae_eq_highContrast {K : ℝ} {hK : 1 ≤ K}
    {P : Measure (CoefficientField d K)} {κ C : ℝ} (hd : 2 ≤ d) (hκ : 0 < κ) (hC : 0 ≤ C)
    (pk : HighContrastCorrectorPackage hK P κ C) {a : CoefficientField d K}
    (hb : toHighContrast hK a ∈ pk.Ωend) {e : Vec d} {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hw : HasWeakGradient Set.univ u g)
    (hloc : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)) ∧
      MemLp g 2 (volume.restrict (ball 0 R)))
    (hharm : HasWeakDivergence Set.univ (fun x => (a x).mulVec (e + g x)) (fun _ => 0))
    (hsub : Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R,
      (u x - ⨍ y in ball 0 R, u y ∂volume) ^ 2 ∂volume)) atTop (𝓝 0)) :
    dilatedGradient g =ᵐ[volume] pk.gradPhi e (toHighContrast hK a) := by
  have : NeZero d := ⟨by omega⟩
  set b := toHighContrast hK a
  have hϑ : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hv := memLiouvilleClass_dilatedCorrectedAffine hK a e hw hloc hharm hsub
    (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨e', c, hvw⟩ := pk.liouville b hb (1 / 2) hϑ _ _ hv
  have hw' := pk.liouville_mem b hb (1 / 2) hϑ e' c
  have hbE : IsAELocallyUniformlyElliptic (fun x => b.1 x) := b.2
  have hgrad := gradient_ae_eq_of_memH1sLoc_of_value_ae hbE hv.1 hw'.1 hvw
  have hloc' : ∀ i, LocallyIntegrable (fun x => pk.gradPhi e' b x i) volume := by
    intro i
    rw [locallyIntegrable_iff]
    intro k hk
    have h1 := integrableOn_grad_isCompact_of_memH1sLoc_class hbE hw'.1 hk i
    have h2 : IntegrableOn (fun _ : Vec d => e' i) k volume :=
      integrableOn_const hk.measure_lt_top.ne
    refine (h1.sub h2).congr_fun (fun x _ => ?_) hk.measurableSet
    simp
  have hu2 : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)) :=
    fun R hR => (hloc R hR).1
  have hee : e = e' :=
    eq_slope_of_ae_eq_corrected (by omega) hκ hC pk hb (hasWeakGradientOn_dilated hw)
      (fun r hr => memLp_dilatedPotential_euclideanBall hu2 hr)
      (locallyIntegrable_dilatedGradient hw) hloc'
      (tendsto_normalizedL2Norm_dilatedPotential hu2
        (sublinear_uncentered_of_centered _ hu2 hsub)) hgrad
  rw [← hee] at hgrad
  filter_upwards [hgrad] with x hx
  exact add_left_cancel hx

/-! ## Translations -/

theorem memLp_comp_add_ball {E : Type*} [NormedAddCommGroup E] {f : Vec d → E}
    (hf : ∀ R : ℝ, 0 < R → MemLp f 2 (volume.restrict (ball 0 R))) (w : Vec d) {R : ℝ}
    (hR : 0 < R) : MemLp (fun x => f (x + w)) 2 (volume.restrict (ball 0 R)) := by
  have hmp : MeasurePreserving (fun x : Vec d => x + w) volume volume :=
    measurePreserving_add_right volume w
  have hemb : MeasurableEmbedding (fun x : Vec d => x + w) :=
    (MeasurableEquiv.addRight w).measurableEmbedding
  have hR' : 0 < R + euclideanNorm w := by
    have := Real.sqrt_nonneg (euclideanSq w)
    unfold euclideanNorm
    linarith
  have h := (hf _ hR').comp_measurePreserving (hmp.restrict_preimage_emb hemb _)
  refine h.mono_measure (Measure.restrict_mono (fun x hx => ?_) le_rfl)
  have hx' : euclideanNorm (x - 0) < R := hx
  show euclideanNorm (x + w - 0) < R + euclideanNorm w
  rw [sub_zero] at hx' ⊢
  exact lt_of_le_of_lt (QSH.euclideanNorm_add_le x w) (by linarith)

theorem hasWeakGradient_comp_add {u : Vec d → ℝ} {g : Vec d → Vec d}
    (h : HasWeakGradient Set.univ u g) (w : Vec d) :
    HasWeakGradient Set.univ (fun x => u (x + w)) (fun x => g (x + w)) := by
  have h' := h.comp_sub (-w)
  simpa only [sub_neg_eq_add] using h'

theorem hasWeakDivergence_comp_add {F : Vec d → Vec d}
    (h : HasWeakDivergence Set.univ F (fun _ => 0)) (w : Vec d) :
    HasWeakDivergence Set.univ (fun x => F (x + w)) (fun _ => 0) := by
  obtain ⟨hF, -, hibp⟩ := h
  refine ⟨fun k => ?_, locallyIntegrableOn_const _, fun ψ hψ => ?_⟩
  · have hk := locallyIntegrable_comp_sub (locallyIntegrableOn_univ.mp (hF k)) (-w)
    simp only [sub_neg_eq_add] at hk
    exact hk.locallyIntegrableOn _
  · have hψ' : IsSpatialTest Set.univ (fun u => ψ (u - w)) := by
      have h := isSpatialTest_comp_add hψ (-w)
      simpa only [sub_eq_add_neg] using h
    have h1 := hibp _ hψ'
    simp only [zero_mul, integral_zero, neg_zero, Measure.restrict_univ] at h1 ⊢
    have hgrad : ∀ x, gradient (fun u => ψ (u - w)) x = gradient ψ (x - w) := by
      intro x
      funext l
      simp only [gradient, coordinateDerivative]
      rw [fderiv_comp_sub w]
    simp only [hgrad] at h1
    have e1 := integral_add_right_eq_self (μ := (volume : Measure (Vec d)))
      (fun u => dot (F u) (gradient ψ (u - w))) w
    simp only [add_sub_cancel_right] at e1
    rw [e1]
    exact h1

private theorem measurableSet_ball_origin'' (R : ℝ) : MeasurableSet (ball (0 : Vec d) R) := by
  have hc : Continuous fun y : Vec d => euclideanNorm (y - 0) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp (by fun_prop)
  exact measurableSet_lt hc.measurable measurable_const

private theorem measurableSet_ball_center (w : Vec d) (R : ℝ) : MeasurableSet (ball w R) := by
  have hc : Continuous fun y : Vec d => euclideanNorm (y - w) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp (by fun_prop)
  exact measurableSet_lt hc.measurable measurable_const

/-- **Translations of sublinear functions are sublinear.** -/
theorem tendsto_sublinear_comp_add {u : Vec d → ℝ}
    (hu : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)))
    (hsub : Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R,
      (u x - ⨍ y in ball 0 R, u y ∂volume) ^ 2 ∂volume)) atTop (𝓝 0)) (w : Vec d) :
    Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R,
      (u (x + w) - ⨍ y in ball 0 R, u (y + w) ∂volume) ^ 2 ∂volume)) atTop (𝓝 0) := by
  set c : ℝ := 2 * Real.sqrt (2 ^ d)
  have hlim : Tendsto (fun R : ℝ => c * ((2 * R)⁻¹ * Real.sqrt (⨍ x in ball 0 (2 * R),
      (u x - ⨍ y in ball 0 (2 * R), u y ∂volume) ^ 2 ∂volume))) atTop (𝓝 0) := by
    have h2 := hsub.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    simpa using h2.const_mul c
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact mul_nonneg (inv_nonneg.mpr hR.le) (Real.sqrt_nonneg _)
  · filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (euclideanNorm w)]
      with R hR hRw
    have h2R : 0 < 2 * R := by positivity
    have hmp : MeasurePreserving (fun x : Vec d => x + w) volume volume :=
      measurePreserving_add_right volume w
    have hemb : MeasurableEmbedding (fun x : Vec d => x + w) :=
      (MeasurableEquiv.addRight w).measurableEmbedding
    set m := ⨍ y in ball 0 (2 * R), u y ∂volume
    have hψ : MemLp (fun x => u (x + w)) 2 (volume.restrict (ball 0 R)) :=
      memLp_comp_add_ball hu w hR
    -- the mean minimizes the square deviation
    have h1 := setAverage_sq_sub_setAverage_le (volume_ball_ne_zero hR) (volume_ball_ne_top hR)
      hψ m
    -- change of variables onto `B_R(w) ⊆ B_{2R}`
    have hpre : (fun x : Vec d => x + w) ⁻¹' ball w R = ball 0 R := by
      ext x
      simp only [mem_preimage, ball, mem_ofPred_eq, add_sub_cancel_right, sub_zero]
    have hsubset : ball w R ⊆ ball (0 : Vec d) (2 * R) := by
      intro y hy
      have hy' : euclideanNorm (y - w) < R := hy
      show euclideanNorm (y - 0) < 2 * R
      have := QSH.euclideanNorm_add_le (y - w) w
      rw [sub_add_cancel] at this
      rw [sub_zero]
      linarith
    have hint : IntegrableOn (fun y => (u y - m) ^ 2) (ball 0 (2 * R)) volume := by
      have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) (2 * R))) :=
        isFiniteMeasure_restrict.mpr (volume_ball_ne_top h2R)
      exact ((hu _ h2R).sub (memLp_const m)).integrable_sq
    have hcv : ∫ x in ball 0 R, (u (x + w) - m) ^ 2 = ∫ y in ball w R, (u y - m) ^ 2 := by
      rw [← hpre]
      exact hmp.setIntegral_preimage_emb hemb (fun y => (u y - m) ^ 2) (ball w R)
    have hmono : ∫ y in ball w R, (u y - m) ^ 2 ≤ ∫ y in ball 0 (2 * R), (u y - m) ^ 2 :=
      setIntegral_mono_set hint (Eventually.of_forall fun y => sq_nonneg _)
        (Eventually.of_forall hsubset)
    have hvol : volume.real (ball (0 : Vec d) (2 * R)) =
        2 ^ d * volume.real (ball (0 : Vec d) R) := by
      rw [volume_real_ball h2R, volume_real_ball hR, mul_pow]
      ring
    have hvR : 0 < volume.real (ball (0 : Vec d) R) :=
      ENNReal.toReal_pos (volume_ball_ne_zero hR) (volume_ball_ne_top hR)
    have hbound : ⨍ x in ball 0 R, (u (x + w) - ⨍ y in ball 0 R, u (y + w) ∂volume) ^ 2 ≤
        2 ^ d * ⨍ x in ball 0 (2 * R), (u x - m) ^ 2 := by
      refine h1.trans ?_
      have e1 : ⨍ x in ball 0 R, (u (x + w) - m) ^ 2 =
          (volume.real (ball (0 : Vec d) R))⁻¹ * ∫ y in ball w R, (u y - m) ^ 2 := by
        rw [setAverage_eq, smul_eq_mul, hcv]
      have e2 : 2 ^ d * ⨍ x in ball 0 (2 * R), (u x - m) ^ 2 =
          (volume.real (ball (0 : Vec d) R))⁻¹ * ∫ y in ball 0 (2 * R), (u y - m) ^ 2 := by
        have hV0 := hvR.ne'
        have h2d : (2 : ℝ) ^ d ≠ 0 := pow_ne_zero d two_ne_zero
        rw [setAverage_eq, smul_eq_mul, hvol]
        field_simp
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr hvR.le)
    calc R⁻¹ * Real.sqrt (⨍ x in ball 0 R,
          (u (x + w) - ⨍ y in ball 0 R, u (y + w) ∂volume) ^ 2 ∂volume)
        ≤ R⁻¹ * (Real.sqrt (2 ^ d) * Real.sqrt (⨍ x in ball 0 (2 * R), (u x - m) ^ 2)) := by
          rw [← Real.sqrt_mul (by positivity)]
          exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hbound) (inv_nonneg.mpr hR.le)
      _ = c * ((2 * R)⁻¹ * Real.sqrt (⨍ x in ball 0 (2 * R), (u x - m) ^ 2)) := by
          simp only [c]
          rw [mul_inv]
          ring

/-! ## Stationarity -/

section Package

variable {Λ : ℝ} {hΛ : 1 ≤ Λ} {P : Measure (CoefficientField d Λ)} {κ C : ℝ}

theorem translate_apply (w : Vec d) (a : CoefficientField d Λ) (x : Vec d) :
    (translate w a) x = a (x + w) := by
  change a.field (w + x) = a.field (x + w)
  rw [add_comm]

/-- **Stationarity of the corrector gradients**: on the events of full probability for `a` and
`T_w a`, `∇φ_e(T_w a)(x) = ∇φ_e(a)(x + w)` for almost every `x`. -/
theorem undilatedGradient_translate_ae_eq (hd : 2 ≤ d) (hκ : 0 < κ) (hC : 0 ≤ C)
    (pk : HighContrastCorrectorPackage hΛ P κ C) {a : CoefficientField d Λ}
    (hb : toHighContrast hΛ a ∈ pk.Ωend) (w : Vec d)
    (hb' : toHighContrast hΛ (translate w a) ∈ pk.Ωend) (e : Vec d) :
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      undilatedGradient (pk.gradPhi e (toHighContrast hΛ (translate w a))) x =
        undilatedGradient (pk.gradPhi e (toHighContrast hΛ a)) (x + w) := by
  have : NeZero d := ⟨by omega⟩
  set b := toHighContrast hΛ a
  have hbell := ae_isEllipticMatrix_toHighContrast hΛ a
  set u := undilatedPotential (pk.Phi e b)
  set g := undilatedGradient (pk.gradPhi e b)
  have hw := hasWeakGradient_undilatedPotential pk hb hbell e
  have hu : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)) :=
    fun R hR => memLp_undilatedPotential_ball pk hb hbell e hR
  have hg : ∀ R : ℝ, 0 < R → MemLp g 2 (volume.restrict (ball 0 R)) :=
    fun R hR => memLp_undilatedGradient_ball pk hb hbell e hR
  have hharm := hasWeakDivergence_undilated hΛ a e (pk.equation b hb e).2 hg
  have hsub := tendsto_sublinear_undilatedPotential hd hκ hC pk hb hbell e
  -- the translate is a corrector of `T_w a`
  have hharm' : HasWeakDivergence Set.univ
      (fun x => (translate w a x).mulVec (e + g (x + w))) (fun _ => 0) := by
    have h := hasWeakDivergence_comp_add hharm w
    simpa only [translate_apply] using h
  have hid := dilatedGradient_ae_eq_highContrast hd hκ hC pk hb' (e := e)
    (u := fun x => u (x + w)) (g := fun x => g (x + w)) (hasWeakGradient_comp_add hw w)
    (fun R hR => ⟨memLp_comp_add_ball hu w hR, memLp_comp_add_ball hg w hR⟩) hharm'
    (tendsto_sublinear_comp_add hu hsub w)
  have hq : Measure.QuasiMeasurePreserving (fun x : Vec d => (2 : ℝ)⁻¹ • x) volume volume :=
    Measure.quasiMeasurePreserving_smul volume (inv_ne_zero two_ne_zero)
  filter_upwards [hq.ae hid] with x hx
  simp only [dilatedGradient, smul_inv_smul₀ (two_ne_zero' ℝ)] at hx
  exact hx.symm

/-! ## The correctors and the homogenization data -/

/-- **The first-order corrector of slope `e`**, Lemma 3.16, from a jointly measurable version `G`
of the undilated high-contrast corrector gradient. -/
def correctorOfMeasurableVersion (hd : 2 ≤ d) (hκ : 0 < κ) (hC : 0 ≤ C) (hP : LawHypotheses P)
    (pk : HighContrastCorrectorPackage hΛ P κ C) (e : Vec d)
    (G : CoefficientField d Λ × Vec d → Vec d) (hG : Measurable G)
    (hGae : ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)),
      G (a, x) = undilatedGradient (pk.gradPhi e (toHighContrast hΛ a)) x) :
    Corrector P e where
  potential a := undilatedPotential (pk.Phi e (toHighContrast hΛ a))
  grad a x := G (a, x)
  measurable_grad := hG
  weak_gradient := by
    have : NeZero d := ⟨by omega⟩
    filter_upwards [ae_mem_Ωend hP pk, hGae] with a hb hGa
    refine hasWeakGradient_congr_ae isOpen_univ
      (hasWeakGradient_undilatedPotential pk hb (ae_isEllipticMatrix_toHighContrast hΛ a) e)
      (ae_eq_refl _) ?_
    rw [Measure.restrict_univ]
    filter_upwards [hGa] with x hx
    exact hx.symm
  locally_square_integrable := by
    have : NeZero d := ⟨by omega⟩
    filter_upwards [ae_mem_Ωend hP pk, hGae] with a hb hGa R hR
    have hbell := ae_isEllipticMatrix_toHighContrast hΛ a
    exact ⟨memLp_undilatedPotential_ball pk hb hbell e hR,
      (memLp_undilatedGradient_ball pk hb hbell e hR).ae_eq
        (ae_restrict_of_ae (hGa.mono fun x hx => hx.symm))⟩
  stationary := by
    intro z
    have : NeZero d := ⟨by omega⟩
    set w := latticeShift z
    have hT : AEMeasurable (translate (Λ := Λ) w) P :=
      (measurable_translateCoefficient w).aemeasurable
    have hmap : P.map (translate w) = P := hP.2.1 z
    have hb' : ∀ᵐ a ∂P, toHighContrast hΛ (translate w a) ∈ pk.Ωend :=
      ae_of_ae_map (p := fun y => toHighContrast hΛ y ∈ pk.Ωend) hT
        (by rw [hmap]; exact ae_mem_Ωend hP pk)
    have hGae' : ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)), G (translate w a, x) =
        undilatedGradient (pk.gradPhi e (toHighContrast hΛ (translate w a))) x :=
      ae_of_ae_map (p := fun y => ∀ᵐ x ∂(volume : Measure (Vec d)), G (y, x) =
        undilatedGradient (pk.gradPhi e (toHighContrast hΛ y)) x) hT (by rw [hmap]; exact hGae)
    filter_upwards [ae_mem_Ωend hP pk, hb', hGae, hGae'] with a hb hb'a hGa hGa'
    have hshift : ∀ᵐ x ∂(volume : Measure (Vec d)), G (a, x + w) =
        undilatedGradient (pk.gradPhi e (toHighContrast hΛ a)) (x + w) :=
      (measurePreserving_add_right volume w).quasiMeasurePreserving.ae hGa
    filter_upwards [hshift, hGa', undilatedGradient_translate_ae_eq hd hκ hC pk hb w hb'a e]
      with x h1 h2 h3
    rw [h1, h2, h3]
  harmonic := by
    filter_upwards [ae_mem_Ωend hP pk, hGae] with a hb hGa
    have hbell := ae_isEllipticMatrix_toHighContrast hΛ a
    have : NeZero d := ⟨by omega⟩
    refine HasWeakDivergence.congr_ae (hasWeakDivergence_undilated hΛ a e
      (pk.equation _ hb e).2 fun R hR => memLp_undilatedGradient_ball pk hb hbell e hR) ?_
      (ae_eq_refl _)
    filter_upwards [hGa] with x hx
    rw [hx]
  sublinear := by
    filter_upwards [ae_mem_Ωend hP pk] with a hb
    exact tendsto_sublinear_undilatedPotential hd hκ hC pk hb
      (ae_isEllipticMatrix_toHighContrast hΛ a) e

end Package

/-- **Existence of homogenization data**, given the joint measurability of the corrector
gradients: Lemma 3.16 (correctors in every direction) and Definition 1.2 (the homogenized matrix
with the limit (1.22)). -/
theorem homogenizationDataExists_of_measurable (hM : HighContrastCorrectorMeasurable) :
    HomogenizationDataExists := by
  intro d hd Λ hΛ P hP
  obtain ⟨κ, C, hκ, hC, hpk⟩ := exists_highContrastCorrectorPackage d hd
  obtain ⟨pk⟩ := hpk Λ hΛ.le P hP
  have hG := fun e => hM d hd Λ hΛ.le P hP κ C pk e
  obtain ⟨A, hA, hlim⟩ := exists_homogenizedMatrix hP (by linarith : (0 : ℝ) ≤ Λ)
  exact ⟨{
    corrector := fun e => correctorOfMeasurableVersion hd hκ hC.le hP pk e (hG e).choose
      (hG e).choose_spec.1 (hG e).choose_spec.2
    homogenized := A
    symmetric := hA
    variational_limit := hlim }⟩

end QSH
