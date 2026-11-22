import QuantitativeStochasticHomogenization.Ch04.Sec04.CorrectorSlopeLocalization
import QuantitativeStochasticHomogenization.Ch03.Sec04.ZeroWeakGradientConstant
import QuantitativeStochasticHomogenization.Ch03.Sec04.WeakGradientSub
import QuantitativeStochasticHomogenization.Ch03.Sec04.SpatialWeakCongruence
import QuantitativeStochasticHomogenization.Ch06.Sec01.HighContrastEnergyBounds
import QuantitativeStochasticHomogenization.Ch03.Sec04.CoefficientSigma

/-!
# Corrector bounds at an arbitrary center

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 3.17, (3.85)-(3.86), at the center `z` instead of the origin. Let `y` be a lattice point
with `|z - y| ≤ d`. The corrector gradients are stationary, `∇φ(a)(x + y) = ∇φ(T_y a)(x)`, so the
potentials agree up to a constant, `φ(a)(x) = φ(T_y a)(x - y) + c`, and the bounds of
`exists_corrector_bounds` for the translated field `T_y a` on `B_{2t}(0) ⊇ B_t(z - y)` give, for
`t ≥ X(T_y a) + d`,
`∫_{B_t(z)} (φ - c')² ≤ 2^d (C (2t)^{1-β(d-s)})² |B_t|` and
`∫_{B_t(z)} |e_i + ∇φ_{e_i}|² ≤ 2^{d+1} (1 + C²) |B_t|`. The law is invariant under `T_y`, so
the random radius `X ∘ T_y` has the same stochastic integrability as `X`.
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ}

/-! ## Translations -/

theorem mem_ball_sub_iff {z y x : Vec d} {r : ℝ} : x - y ∈ ball (z - y) r ↔ x ∈ ball z r := by
  show euclideanNorm (x - y - (z - y)) < r ↔ euclideanNorm (x - z) < r
  rw [sub_sub_sub_cancel_right]

theorem setIntegral_ball_comp_sub (F : Vec d → ℝ) (z y : Vec d) (r : ℝ) :
    ∫ x in ball z r, F (x - y) = ∫ u in ball (z - y) r, F u := by
  rw [← integral_indicator (measurableSet_ball z r),
    ← integral_indicator (measurableSet_ball (z - y) r)]
  have h := integral_sub_right_eq_self (μ := (volume : Measure (Vec d)))
    (fun u => (ball (z - y) r).indicator F u) y
  rw [← h]
  congr 1
  funext x
  by_cases hx : x ∈ ball z r
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (mem_ball_sub_iff.mpr hx)]
  · rw [Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (fun h => hx (mem_ball_sub_iff.mp h))]

theorem isSpatialTest_comp_add {ψ : Vec d → ℝ} (hψ : IsSpatialTest Set.univ ψ) (y : Vec d) :
    IsSpatialTest Set.univ (fun u => ψ (u + y)) :=
  ⟨hψ.1.comp (contDiff_id.add contDiff_const),
    hψ.2.1.comp_homeomorph (Homeomorph.addRight y), Set.subset_univ _⟩

theorem coordinateDerivative_comp_add (i : Fin d) (ψ : Vec d → ℝ) (y u : Vec d) :
    coordinateDerivative i (fun u => ψ (u + y)) u = coordinateDerivative i ψ (u + y) := by
  unfold coordinateDerivative
  rw [fderiv_comp_add_right]

theorem locallyIntegrable_comp_sub {f : Vec d → ℝ} (hf : LocallyIntegrable f volume)
    (y : Vec d) : LocallyIntegrable (fun x => f (x - y)) volume := by
  have hmap : Measure.map (Homeomorph.subRight y) (volume : Measure (Vec d)) = volume :=
    (measurePreserving_sub_right volume y).map_eq
  have hf' : LocallyIntegrable f (Measure.map (Homeomorph.subRight y) volume) := by
    rw [hmap]
    exact hf
  exact (locallyIntegrable_map_homeomorph (Homeomorph.subRight y)).1 hf'

theorem HasWeakPartialDerivative.comp_sub {i : Fin d} {f g : Vec d → ℝ}
    (h : HasWeakPartialDerivative Set.univ i f g) (y : Vec d) :
    HasWeakPartialDerivative Set.univ i (fun x => f (x - y)) (fun x => g (x - y)) := by
  obtain ⟨hf, hg, hibp⟩ := h
  refine ⟨locallyIntegrableOn_univ.mpr (locallyIntegrable_comp_sub
      (locallyIntegrableOn_univ.mp hf) y),
    locallyIntegrableOn_univ.mpr (locallyIntegrable_comp_sub
      (locallyIntegrableOn_univ.mp hg) y), fun ψ hψ => ?_⟩
  have h1 := hibp _ (isSpatialTest_comp_add hψ y)
  simp only [Measure.restrict_univ, coordinateDerivative_comp_add] at h1 ⊢
  have e1 := integral_sub_right_eq_self (μ := (volume : Measure (Vec d)))
    (fun u => f u * coordinateDerivative i ψ (u + y)) y
  have e2 := integral_sub_right_eq_self (μ := (volume : Measure (Vec d)))
    (fun u => g u * ψ (u + y)) y
  simp only [sub_add_cancel] at e1 e2
  rw [e1, e2, h1]

theorem HasWeakGradient.comp_sub {f : Vec d → ℝ} {G : Vec d → Vec d}
    (h : HasWeakGradient Set.univ f G) (y : Vec d) :
    HasWeakGradient Set.univ (fun x => f (x - y)) (fun x => G (x - y)) :=
  fun i => (h i).comp_sub y

/-- Two whole-space potentials whose weak gradients agree after a translation by `y` agree up to
a constant after the same translation. -/
theorem exists_ae_eq_comp_sub_add_const (hd : 0 < d) {f₁ f₂ : Vec d → ℝ}
    {G₁ G₂ : Vec d → Vec d} (h₁ : HasWeakGradient Set.univ f₁ G₁)
    (h₂ : HasWeakGradient Set.univ f₂ G₂) (y : Vec d) (hG : ∀ᵐ x, G₁ x = G₂ (x - y)) :
    ∃ c : ℝ, f₁ =ᵐ[volume] fun x => f₂ (x - y) + c := by
  have h₂' : HasWeakGradient Set.univ (fun x => f₂ (x - y)) G₁ := by
    apply hasWeakGradient_congr_ae isOpen_univ (h₂.comp_sub y) (ae_eq_refl _)
    rw [Measure.restrict_univ]
    filter_upwards [hG] with x hx
    exact hx.symm
  have hweak := hasWeakGradient_sub h₁ h₂'
  have hloc : LocallyIntegrable (fun x => f₁ x - f₂ (x - y)) volume :=
    locallyIntegrableOn_univ.mp (hweak ⟨0, hd⟩).1
  obtain ⟨c, hc⟩ := ae_eq_const_of_zero_weak_gradient hloc
    (fun l ψ hψ => by
      have h := (hweak l).2.2 ψ hψ
      simpa only [Measure.restrict_univ, Pi.sub_apply, sub_self, zero_mul,
        integral_zero, neg_zero] using h)
  refine ⟨c, ?_⟩
  filter_upwards [hc] with x hx
  change f₁ x - f₂ (x - y) = c at hx
  linarith

theorem exists_latticeShift_near (z : Vec d) :
    ∃ m : LatticeIndex d, euclideanNorm (z - latticeShift m) ≤ d := by
  refine ⟨fun i => round (z i), ?_⟩
  have h : ∀ i, (z - latticeShift (fun i => round (z i))) i *
      (z - latticeShift (fun i => round (z i))) i ≤ 1 / 4 := fun i => by
    have h1 : |(z - latticeShift (fun i => round (z i))) i| ≤ 1 / 2 := by
      simp only [Pi.sub_apply, latticeShift]
      exact abs_sub_round (z i)
    have h2 := abs_nonneg ((z - latticeShift (fun i => round (z i))) i)
    nlinarith [abs_mul_abs_self ((z - latticeShift (fun i => round (z i))) i)]
  have hsq : euclideanSq (z - latticeShift (fun i => round (z i))) ≤ (d : ℝ) ^ 2 := by
    calc euclideanSq (z - latticeShift (fun i => round (z i)))
        = ∑ i, (z - latticeShift (fun i => round (z i))) i *
            (z - latticeShift (fun i => round (z i))) i := rfl
      _ ≤ ∑ _i : Fin d, (1 / 4 : ℝ) := Finset.sum_le_sum fun i _ => h i
      _ = d / 4 := by simp [div_eq_mul_inv]
      _ ≤ (d : ℝ) ^ 2 := by
          rcases Nat.eq_zero_or_pos d with hd | hd
          · simp [hd]
          · have : (1 : ℝ) ≤ d := by exact_mod_cast hd
            nlinarith
  calc euclideanNorm (z - latticeShift (fun i => round (z i)))
      ≤ Real.sqrt ((d : ℝ) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = d := Real.sqrt_sq (Nat.cast_nonneg d)

/-! ## Deterministic transfer of the bounds -/

theorem ball_sub_subset_ball_zero {z y : Vec d} {t : ℝ} (hzy : euclideanNorm (z - y) ≤ t) :
    ball (z - y) t ⊆ ball 0 (2 * t) :=
  ball_subset_ball_of_add_le (by rw [sub_zero]; linarith)

theorem volume_real_ball_two_mul {z : Vec d} {t : ℝ} (ht : 0 < t) :
    volume.real (ball (0 : Vec d) (2 * t)) = 2 ^ d * volume.real (ball z t) := by
  rw [volume_real_ball_eq_mul 0 (by positivity), volume_real_ball_eq_mul z ht, mul_pow]
  ring

theorem setIntegral_le_mul_of_sqrt_setAverage_le {f : Vec d → ℝ} {t C : ℝ} (ht : 0 < t)
    (hf : Real.sqrt (⨍ x in ball (0 : Vec d) t, f x) ≤ C)
    (hf0 : 0 ≤ ⨍ x in ball (0 : Vec d) t, f x) :
    ∫ x in ball (0 : Vec d) t, f x ≤ C ^ 2 * volume.real (ball (0 : Vec d) t) := by
  have hV := volume_real_ball_pos (0 : Vec d) ht
  have hle : ⨍ x in ball (0 : Vec d) t, f x ≤ C ^ 2 := by
    rw [← Real.sq_sqrt hf0]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hf 2
  rw [setAverage_eq, smul_eq_mul] at hle
  have := mul_le_mul_of_nonneg_left hle hV.le
  rwa [← mul_assoc, mul_inv_cancel₀ hV.ne', one_mul, mul_comm] at this

/-- **The energy bound at the center `z`** from the bound at the origin for the translated
gradient. -/
theorem integral_ball_euclideanSq_unitVector_add_le {G G' : Vec d → Vec d} {y z : Vec d}
    (hG : ∀ᵐ x, G x = G' (x - y)) {t C : ℝ} (ht : 0 < t) (hzy : euclideanNorm (z - y) ≤ t)
    (hint : IntegrableOn (fun x => euclideanSq (G' x)) (ball 0 (2 * t)))
    (hE : Real.sqrt (⨍ x in ball (0 : Vec d) (2 * t), euclideanSq (G' x)) ≤ C) (i : Fin d) :
    ∫ x in ball z t, euclideanSq (unitVector i + G x) ≤
      2 ^ (d + 1) * (1 + C ^ 2) * volume.real (ball z t) := by
  have h1 : ∫ x in ball z t, euclideanSq (unitVector i + G x) =
      ∫ u in ball (z - y) t, euclideanSq (unitVector i + G' u) := by
    rw [← setIntegral_ball_comp_sub (fun u => euclideanSq (unitVector i + G' u)) z y t]
    refine setIntegral_congr_ae (measurableSet_ball z t) ?_
    filter_upwards [hG] with x hx _
    rw [hx]
  have hsub := ball_sub_subset_ball_zero hzy
  have hc2 : IntegrableOn (fun _ : Vec d => (2 : ℝ)) (ball (0 : Vec d) (2 * t)) :=
    integrableOn_const (volume_ball_lt_top _ _).ne
  have hint2 : IntegrableOn (fun u => 2 + 2 * euclideanSq (G' u)) (ball (0 : Vec d) (2 * t)) :=
    hc2.add (hint.const_mul 2)
  have h2 : ∫ u in ball (z - y) t, euclideanSq (unitVector i + G' u) ≤
      ∫ u in ball (z - y) t, (2 + 2 * euclideanSq (G' u)) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun u => zero_le_euclideanSq _)
      (hint2.mono_set hsub) (Eventually.of_forall fun u => ?_)
    have := euclideanSq_add_le (unitVector i) (G' u)
    rw [euclideanSq_unitVector] at this
    linarith
  have h3 : ∫ u in ball (z - y) t, (2 + 2 * euclideanSq (G' u)) ≤
      ∫ u in ball (0 : Vec d) (2 * t), (2 + 2 * euclideanSq (G' u)) :=
    setIntegral_mono_set hint2
      (Eventually.of_forall fun u => by
        show (0 : ℝ) ≤ 2 + 2 * euclideanSq (G' u)
        have := zero_le_euclideanSq (G' u)
        linarith)
      hsub.eventuallyLE
  have hav0 : 0 ≤ ⨍ x in ball (0 : Vec d) (2 * t), euclideanSq (G' x) :=
    setAverage_nonneg_of_nonneg fun x => zero_le_euclideanSq _
  have h4 := setIntegral_le_mul_of_sqrt_setAverage_le (by positivity) hE hav0
  have h5 : ∫ u in ball (0 : Vec d) (2 * t), (2 + 2 * euclideanSq (G' u)) =
      2 * volume.real (ball (0 : Vec d) (2 * t)) +
        2 * ∫ u in ball (0 : Vec d) (2 * t), euclideanSq (G' u) := by
    rw [integral_add hc2 (hint.const_mul 2),
      integral_const_mul, setIntegral_const, smul_eq_mul, mul_comm]
  have hV := volume_real_ball_two_mul (z := z) ht
  rw [h1]
  have hfin : 2 * volume.real (ball (0 : Vec d) (2 * t)) +
      2 * (C ^ 2 * volume.real (ball (0 : Vec d) (2 * t))) =
      2 ^ (d + 1) * (1 + C ^ 2) * volume.real (ball z t) := by
    rw [hV, pow_succ]
    ring
  linarith

/-- **The oscillation bound at the center `z`** from the bound at the origin for the translated
potential. -/
theorem integral_ball_sq_sub_le_of_translate {f f' : Vec d → ℝ} {y z : Vec d} {c : ℝ}
    (hf : f =ᵐ[volume] fun x => f' (x - y) + c) {t C : ℝ} (ht : 0 < t)
    (hzy : euclideanNorm (z - y) ≤ t) (hint : MemLp f' 2 (volume.restrict (ball 0 (2 * t))))
    (hosc : Real.sqrt (⨍ x in ball (0 : Vec d) (2 * t),
      |f' x - ⨍ u in ball (0 : Vec d) (2 * t), f' u| ^ 2) ≤ C) :
    ∫ x in ball z t, (f x - (c + ⨍ u in ball (0 : Vec d) (2 * t), f' u)) ^ 2 ≤
      2 ^ d * C ^ 2 * volume.real (ball z t) := by
  set m := ⨍ u in ball (0 : Vec d) (2 * t), f' u with hm
  have h1 : ∫ x in ball z t, (f x - (c + m)) ^ 2 = ∫ u in ball (z - y) t, (f' u - m) ^ 2 := by
    rw [← setIntegral_ball_comp_sub (fun u => (f' u - m) ^ 2) z y t]
    refine setIntegral_congr_ae (measurableSet_ball z t) ?_
    filter_upwards [hf] with x hx _
    rw [hx]
    ring
  have hsub := ball_sub_subset_ball_zero hzy
  have hint2 : IntegrableOn (fun u => (f' u - m) ^ 2) (ball (0 : Vec d) (2 * t)) :=
    (hint.sub (memLp_const m)).integrable_sq
  have h2 : ∫ u in ball (z - y) t, (f' u - m) ^ 2 ≤ ∫ u in ball (0 : Vec d) (2 * t), (f' u - m) ^ 2 :=
    setIntegral_mono_set hint2 (Eventually.of_forall fun u => sq_nonneg (f' u - m))
      hsub.eventuallyLE
  have hav0 : 0 ≤ ⨍ x in ball (0 : Vec d) (2 * t), |f' x - m| ^ 2 :=
    setAverage_nonneg_of_nonneg fun x => sq_nonneg _
  have h3 := setIntegral_le_mul_of_sqrt_setAverage_le (by positivity) hosc hav0
  simp only [sq_abs] at h3
  have hV := volume_real_ball_two_mul (z := z) ht
  rw [h1]
  rw [hV] at h3
  linarith

/-- **The corrector bounds of Lemma 3.17 at an arbitrary center.** There are `β, C > 0` such
that for every `s ∈ (0, d)` there is `C_s` with: for every law, homogenization data `S` and
center `z` there is a random radius `X ≥ 1` with `X ≤ O_s(C_s)` such that almost surely, for
every `i` and every `t ≥ X + d`, the corrector `φ_{e_i}` satisfies
`∫_{B_t(z)} (φ_{e_i} - c)² ≤ 2^d (C (2t)^{1-β(d-s)})² |B_t|` for some constant `c` and
`∫_{B_t(z)} |e_i + ∇φ_{e_i}|² ≤ 2^{d+1} (1 + C²) |B_t|`. -/
theorem exists_translated_corrector_bounds (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) :
    ∃ β C : ℝ, 0 < β ∧ 0 < C ∧ ∀ s : ℝ, 0 < s → s < d → ∃ Cs : ℝ, 0 < Cs ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
        ∀ z : Vec d, ∃ X : CoefficientField d Λ → ℝ, Measurable X ∧ OsBound P X s Cs ∧
          (∀ a, 1 ≤ X a) ∧ ∀ᵐ a ∂P, ∀ i : Fin d, ∀ t : ℝ, X a + d ≤ t →
            (∃ c : ℝ, ∫ x in ball z t, ((S.corrector (unitVector i)).potential a x - c) ^ 2 ≤
              2 ^ d * (C * (2 * t) ^ (1 - β * ((d : ℝ) - s))) ^ 2 * volume.real (ball z t)) ∧
            ∫ x in ball z t, euclideanSq (correctorColumn S a i x) ≤
              2 ^ (d + 1) * (1 + C ^ 2) * volume.real (ball z t) := by
  obtain ⟨β, C, hβ, hC, hE8⟩ := exists_corrector_bounds d hd Λ hΛ
  refine ⟨β, C, hβ, hC, fun s hs hsd => ?_⟩
  obtain ⟨Cs, hCs, hP8⟩ := hE8 s hs hsd
  refine ⟨Cs, hCs, fun P hP S z => ?_⟩
  obtain ⟨X, hXm, hXos, hX1, hXae⟩ := hP8 P hP
  obtain ⟨m, hm⟩ := exists_latticeShift_near z
  have hT : MeasurePreserving (translate (latticeShift m)) P P :=
    ⟨measurable_translateCoefficient _, hP.2.1 m⟩
  refine ⟨fun a => X (translate (latticeShift m) a), hXm.comp hT.measurable,
    hXos.comp_measurePreserving hT, fun a => hX1 _, ?_⟩
  have hunit : ∀ i : Fin d, euclideanNorm (unitVector i) = 1 := fun i => by
    rw [euclideanNorm, euclideanSq_unitVector, Real.sqrt_one]
  have h8 := hT.quasiMeasurePreserving.ae
    (ae_all_iff.2 fun i : Fin d => hXae (unitVector i) (hunit i) (S.corrector (unitVector i)))
  have hwgT := hT.quasiMeasurePreserving.ae
    (ae_all_iff.2 fun i : Fin d => (S.corrector (unitVector i)).weak_gradient)
  have hlocT := hT.quasiMeasurePreserving.ae
    (ae_all_iff.2 fun i : Fin d => (S.corrector (unitVector i)).locally_square_integrable)
  filter_upwards [h8, hwgT, hlocT,
    ae_all_iff.2 fun i : Fin d => (S.corrector (unitVector i)).weak_gradient,
    ae_all_iff.2 fun i : Fin d => (S.corrector (unitVector i)).stationary m]
    with a h8a hwgTa hlocTa hwga hsta
  intro i t ht
  set b := translate (latticeShift m) a with hb
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hX1a : 1 ≤ X b := hX1 b
  have ht0 : 0 < t := by linarith
  have hzy : euclideanNorm (z - latticeShift m) ≤ t := by linarith
  have h2t : X b ≤ 2 * t := by linarith
  obtain ⟨hosc8, hen8⟩ := h8a i (2 * t) h2t
  have hG : ∀ᵐ x, (S.corrector (unitVector i)).grad a x =
      (S.corrector (unitVector i)).grad b (x - latticeShift m) := by
    have := (measurePreserving_sub_right volume (latticeShift m)).quasiMeasurePreserving.ae
      (hsta i)
    filter_upwards [this] with x hx
    simpa only [sub_add_cancel] using hx
  obtain ⟨c, hc⟩ := exists_ae_eq_comp_sub_add_const hd0 (hwga i) (hwgTa i) (latticeShift m) hG
  have hloc2 := hlocTa i (2 * t) (by positivity)
  refine ⟨⟨_, integral_ball_sq_sub_le_of_translate hc ht0 hzy hloc2.1 hosc8⟩, ?_⟩
  have hint : IntegrableOn (fun x => euclideanSq ((S.corrector (unitVector i)).grad b x))
      (ball 0 (2 * t)) := by
    have hk : ∀ k, MemLp (fun x => (S.corrector (unitVector i)).grad b x k) 2
        (volume.restrict (ball 0 (2 * t))) := fun k =>
      hloc2.2.of_le (((measurable_pi_apply k).comp
        ((S.corrector (unitVector i)).measurable_grad.comp
          (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
        (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact norm_le_pi_norm ((S.corrector (unitVector i)).grad b x) k)
    exact (integrable_finsetSum Finset.univ fun k _ => (hk k).integrable_sq).congr
      (Eventually.of_forall fun x => by simp only [euclideanSq, dot, sq])
  exact integral_ball_euclideanSq_unitVector_add_le hG ht0 hzy hint hen8 i

end QSH
