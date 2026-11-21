import QuantitativeStochasticHomogenization.Ch04.Sec04.LocalizationTranslation

/-!
# Joint measurability of the localized energy in the coefficients and the center

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.5 (the proof of Proposition 4.12 integrates `x ↦ J₁^{(δ)}(x, r, p, q)` over boxes) and
Section 4.4. By the translation covariance of the construction,
`J₁^{(δ)}(a, x, r, p, q) = J₁^{(δ)}(T_x a, 0, r, p, q)`. The translation `(a, x) ↦ T_x a` is
measurable from `F(V) ⊗ Borel` on `{x ∈ U}` to `F(B_T(0))` as soon as `B_T(x) ⊆ V` for `x ∈ U`:
its test integrals are smooth averages of `a` against shifted tests, continuous in the shift and
`F(V)`-measurable for each shift in `U`. Hence `(a, x) ↦ 1_U(x) J₁^{(δ)}(a, x, r, p, q)` is
`F(V) ⊗ Borel`-measurable.
-/

open MeasureTheory Filter Topology
open scoped Convolution

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- The test `u(· - y)` shifted to `y`. -/
def shiftTest (u : SmoothCompactTest d) (y : Vec d) : SmoothCompactTest d :=
  ⟨fun x => u (x + -y), u.smooth.comp (contDiff_id.add contDiff_const),
    u.compact.comp_homeomorph (Homeomorph.addRight (-y))⟩

theorem tsupport_shiftTest_subset {u : SmoothCompactTest d} {T : ℝ}
    (hu : tsupport u.toFun ⊆ ball 0 T) (y : Vec d) :
    tsupport (shiftTest u y).toFun ⊆ ball y T := by
  have h := tsupport_comp_eq_preimage u.toFun (Homeomorph.addRight (-y))
  change tsupport (u.toFun ∘ (Homeomorph.addRight (-y))) ⊆ _
  rw [h]
  intro x hx
  have hx' : x + -y ∈ ball 0 T := hu hx
  show euclideanNorm (x - y) < T
  have e : x - y = (x + -y) - 0 := by abel
  rw [e]
  exact hx'

theorem testIntegral_translate (a : CoefficientField d Λ) (u : SmoothCompactTest d) (y : Vec d)
    (i j : Fin d) : testIntegral (translate y a) u i j = testIntegral a (shiftTest u y) i j := by
  unfold testIntegral
  have h := integral_add_left_eq_self (μ := (volume : Measure (Vec d)))
    (f := fun x => (shiftTest u y) x * a.field x i j) y
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show u x * a.field (y + x) i j = u (y + x + -y) * a.field (y + x) i j
  rw [add_neg_cancel_comm]

theorem continuous_testIntegral_shiftTest (a : CoefficientField d Λ) (u : SmoothCompactTest d)
    (i j : Fin d) : Continuous fun y => testIntegral a (shiftTest u y) i j := by
  set uRev : Vec d → ℝ := fun t => u (-t)
  have huRevc : Continuous uRev := u.smooth.continuous.comp continuous_neg
  have huRevs : HasCompactSupport uRev := u.compact.comp_homeomorph (Homeomorph.neg (Vec d))
  have h := huRevs.continuous_convolution_left (μ := (volume : Measure (Vec d)))
    (ContinuousLinearMap.lsmul ℝ ℝ) huRevc (a.locally_integrable i j)
  convert h using 1
  funext y
  rw [convolution_lsmul_swap]
  unfold testIntegral
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show u (x + -y) * a.field x i j = uRev (y - x) • a.field x i j
  simp only [uRev, smul_eq_mul, neg_sub]
  rw [sub_eq_add_neg]

/-- The translation `(a, x) ↦ T_{p(x)} a` along a measurable map `p` into `U`, where
`B_T(y) ⊆ V` for `y ∈ U`, is measurable from `F(V) ⊗ Borel` to `F(B_T(0))`. -/
theorem measurable_translate_comp {U V : Set (Vec d)} {T : ℝ}
    (hV : ∀ y ∈ U, ball y T ⊆ V) (π : Vec d → U) (hπ : Measurable π) :
    @Measurable (CoefficientField d Λ × Vec d) (CoefficientField d Λ)
      (@Prod.instMeasurableSpace _ _ (localSigma V) _) (localSigma (ball 0 T))
      (fun w => translate (π w.2 : Vec d) w.1) := by
  let _ : MeasurableSpace (CoefficientField d Λ) := localSigma V
  rw [measurable_iff_comap_le]
  unfold localSigma
  simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  refine iSup_le fun u => iSup_le fun i => iSup_le fun j => ?_
  refine Measurable.comap_le ?_
  have hjoint : Measurable (Function.uncurry fun (y : U) (a : CoefficientField d Λ) =>
      testIntegral a (shiftTest u.1 y) i j) := by
    refine measurable_uncurry_of_continuous_of_measurable (fun a => ?_) (fun y => ?_)
    · exact (continuous_testIntegral_shiftTest a u.1 i j).comp continuous_subtype_val
    · exact measurable_testIntegral_localSigma (shiftTest u.1 y)
        ((tsupport_shiftTest_subset u.2 y).trans (hV y y.2)) i j
  have hcomp := hjoint.comp ((hπ.comp measurable_snd).prodMk measurable_fst)
  have heq : ((fun a : CoefficientField d Λ => testIntegral a u.1 i j) ∘
      fun w : CoefficientField d Λ × Vec d => translate (π w.2 : Vec d) w.1) =
      (Function.uncurry fun (y : U) (a : CoefficientField d Λ) =>
        testIntegral a (shiftTest u.1 y) i j) ∘ fun w => ((π ∘ Prod.snd) w, w.1) := by
    funext w
    simp only [Function.comp_apply, Function.uncurry_apply_pair]
    exact testIntegral_translate w.1 u.1 (π w.2) i j
  rw [heq]
  exact hcomp

/-- **Translation covariance of the localized energy.** -/
theorem localizedJ1_eq_translate {δ γ α σ θ C₀ : ℝ} (hσ : 0 < σ) (hC₀ : 0 ≤ C₀)
    (W : LocalizedFamily d Λ δ γ α σ θ C₀) (a : CoefficientField d Λ) (x : Vec d) (r : ℝ)
    (hr : 2 ≤ r) (p q : Vec d) :
    localizedJ1 (W a x r hr) r p q = localizedJ1 (W (translate x a) 0 r hr) r p q := by
  have hr0 : 0 < r := by linarith
  have hb : ∀ y, (translate x a).field y = a.field (x + y) := fun y => rfl
  have hz : x + 0 = x := add_zero x
  rw [← localizedJ1_shift (W a x r hr) hb hz r p q]
  exact localizedJ1_eq_of_basis (Real.rpow_pos_of_pos hr0 _)
    (mul_pos hσ (Real.rpow_pos_of_pos hr0 _)).ne' hC₀ _ _ r p q

/-- **Joint measurability of the localized energy**: for every measurable set `U` of centers and
every `V` containing the balls `B_{r^{1+δ}}(x)`, `x ∈ U`, the map
`(a, x) ↦ 1_U(x) J₁^{(δ)}(a, x, r, p, q)` is `F(V) ⊗ Borel`-measurable. -/
theorem measurable_indicator_localizedJ1 (hΛ : 0 ≤ Λ) {δ γ α σ θ C₀ : ℝ} (hσ : 0 < σ)
    (hθ : 0 < θ) (hC₀ : 0 < C₀) (W : LocalizedFamily d Λ δ γ α σ θ C₀) (r : ℝ) (hr : 2 ≤ r)
    (p q : Vec d) {U V : Set (Vec d)} (hU : MeasurableSet U)
    (hV : ∀ x ∈ U, ball x (localizationOuterRadius δ r) ⊆ V) :
    @Measurable (CoefficientField d Λ × Vec d) ℝ
      (@Prod.instMeasurableSpace _ _ (localSigma V) _) _
      (fun w => U.indicator (fun x => localizedJ1 (W w.1 x r hr) r p q) w.2) := by
  let _ : MeasurableSpace (CoefficientField d Λ) := localSigma V
  rcases U.eq_empty_or_nonempty with hU0 | ⟨x₀, hx₀⟩
  · subst hU0
    simp only [Set.indicator_empty]
    exact measurable_const
  classical
  set π : Vec d → U := fun x => if hx : x ∈ U then ⟨x, hx⟩ else ⟨x₀, hx₀⟩
  have hπ : Measurable π :=
    Measurable.dite (f := fun y : U => y) measurable_id (g := fun _ => ⟨x₀, hx₀⟩)
      measurable_const hU
  have hJ := measurable_localizedJ1_of_localizedFamily hΛ hσ hθ hC₀ W 0 r hr p q
  have htr := measurable_translate_comp (Λ := Λ) hV π hπ
  have hcomp : Measurable fun w : CoefficientField d Λ × Vec d =>
      localizedJ1 (W (translate (π w.2 : Vec d) w.1) 0 r hr) r p q :=
    @Measurable.comp _ _ _ (@Prod.instMeasurableSpace _ _ (localSigma V) _)
      (localSigma (ball 0 (localizationOuterRadius δ r))) _ _ _ hJ htr
  have hmeasU : MeasurableSet {w : CoefficientField d Λ × Vec d | w.2 ∈ U} :=
    measurable_snd hU
  have heq : (fun w : CoefficientField d Λ × Vec d =>
      U.indicator (fun x => localizedJ1 (W w.1 x r hr) r p q) w.2) =
      {w : CoefficientField d Λ × Vec d | w.2 ∈ U}.indicator
        (fun w => localizedJ1 (W (translate (π w.2 : Vec d) w.1) 0 r hr) r p q) := by
    funext w
    by_cases hw : w.2 ∈ U
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem (show w ∈ {w : CoefficientField d Λ ×
        Vec d | w.2 ∈ U} from hw)]
      have hπw : (π w.2 : Vec d) = w.2 := by simp [π, hw]
      rw [hπw]
      exact localizedJ1_eq_translate hσ hC₀.le W w.1 w.2 r hr p q
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem (show w ∉ {w : CoefficientField d Λ ×
        Vec d | w.2 ∈ U} from hw)]
  rw [heq]
  exact hcomp.indicator hmeasU

/-- **Joint measurability of the extended localized energy** `familyJ1` (zero below `r = 2`), in
the form used by the proof of Proposition 4.12. -/
theorem measurable_indicator_familyJ1 (hΛ : 0 ≤ Λ) {δ γ α σ θ C₀ : ℝ} (hσ : 0 < σ)
    (hθ : 0 < θ) (hC₀ : 0 < C₀) (W : LocalizedFamily d Λ δ γ α σ θ C₀) (r : ℝ)
    (p q : Vec d) {U V : Set (Vec d)} (hU : MeasurableSet U)
    (hV : ∀ x ∈ U, ball x (localizationOuterRadius δ r) ⊆ V) :
    @Measurable (CoefficientField d Λ × Vec d) ℝ
      (@Prod.instMeasurableSpace _ _ (localSigma V) _) _
      (fun w => U.indicator (fun x => familyJ1 W w.1 x r p q) w.2) := by
  by_cases hr : 2 ≤ r
  · have h := measurable_indicator_localizedJ1 hΛ hσ hθ hC₀ W r hr p q hU hV
    have heq : (fun w : CoefficientField d Λ × Vec d =>
        U.indicator (fun x => familyJ1 W w.1 x r p q) w.2) =
        fun w => U.indicator (fun x => localizedJ1 (W w.1 x r hr) r p q) w.2 := by
      funext w
      simp [familyJ1, hr]
    rw [heq]
    exact h
  · have : (fun w : CoefficientField d Λ × Vec d =>
        U.indicator (fun x => familyJ1 W w.1 x r p q) w.2) = fun _ => 0 := by
      funext w
      simp [familyJ1, hr]
    rw [this]
    exact @measurable_const _ _ _ (@Prod.instMeasurableSpace _ _ (localSigma V) _) _

end QSH
