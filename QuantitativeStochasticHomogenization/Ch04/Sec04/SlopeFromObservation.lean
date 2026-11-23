import QuantitativeStochasticHomogenization.Ch04.Sec04.SlopeLocalization
import QuantitativeStochasticHomogenization.Ch04.Sec04.BallCaccioppoli
import QuantitativeStochasticHomogenization.Ch04.Sec04.CorrectedCoordinate
import QuantitativeStochasticHomogenization.Ch03.Sec04.WeakGradientSub
import QuantitativeStochasticHomogenization.Ch03.Sec04.SpatialWeakLocalization

/-!
# The single-slope estimate of Lemma 4.21 from the excess decay and the observation

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.21, in the form of the single slope: for the selected coordinate `w_i` put
`v_i = w_i - ((x - z)_i + φ_{e_i})`, an `a`-harmonic function on `B_T(z)` with gradient
`∇w_i - W_i`. Three estimates combine.

* The observation (`LocalizationObservationEstimate`): on a good event,
  `‖v_i - k_i‖_{L̲²(B_S(z))} ≤ S Y₀` with `Y₀ = O_s(C S^{-β})`, deterministically small.
* The Caccioppoli inequality (`caccioppoli_ball`) from `B_S(z)` to `B_{S/2}(z)`.
* The excess decay of one slope at the center `z` in ball form (`BallExcessDecay`, Theorem C of
  Armstrong, Kuusi and Loher): one slope `e_i` with
  `∫_{B_t(z)} |∇v_i - ∑_j e_{ij} W_j|² ≤ C_ϑ (t/R)^{2ϑ} |B_t| ⨍_{B_{LR}(z)} |∇v_i|²` for
  `X ≤ t ≤ R`, and `|e_i|² ≤ C_ϑ ⨍_{B_{LR}(z)} |∇v_i|²`.

With `R = S/(2L)` and `Y = (r/S)^ϑ Y₀` they give `LocalizationSlopeEstimate` when
`(r/S)^ϑ S^{-β} ≤ r^{-γ}`, the exponent budget of the consultant note S9, step 1.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-! ## Weak divergences on balls -/

theorem setIntegral_dot_gradient_eq_integral {U : Set (Vec d)} (F : Vec d → Vec d)
    {φ : Vec d → ℝ} (hφ : IsSpatialTest U φ) :
    ∫ x in U, dot (F x) (gradient φ x) = ∫ x, dot (F x) (gradient φ x) := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [gradient_eq_zero_of_notMem_tsupport (fun h => hx (hφ.2.2 h))]
  simp [dot]

theorem setIntegral_mul_spatialTest_eq_integral {U : Set (Vec d)} (f : Vec d → ℝ)
    {φ : Vec d → ℝ} (hφ : IsSpatialTest U φ) :
    ∫ x in U, f x * φ x = ∫ x, f x * φ x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.2.2 h)), mul_zero]

/-- A weak divergence restricts to a smaller domain. -/
theorem hasWeakDivergence_mono_set {U V : Set (Vec d)} (hVU : V ⊆ U) {F : Vec d → Vec d}
    {h : Vec d → ℝ} (hF : HasWeakDivergence U F h) : HasWeakDivergence V F h := by
  refine ⟨fun i => (hF.1 i).mono_set hVU, hF.2.1.mono_set hVU, fun φ hφ => ?_⟩
  have hφU : IsSpatialTest U φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans hVU⟩
  have heq := hF.2.2 φ hφU
  rw [setIntegral_dot_gradient_eq_integral F hφU, setIntegral_mul_spatialTest_eq_integral h hφU]
    at heq
  rwa [setIntegral_dot_gradient_eq_integral F hφ, setIntegral_mul_spatialTest_eq_integral h hφ]

theorem integrableOn_dot_gradient_of_locallyIntegrableOn {U : Set (Vec d)} {F : Vec d → Vec d}
    (hF : ∀ i, LocallyIntegrableOn (fun x => F x i) U volume) {φ : Vec d → ℝ}
    (hφ : IsSpatialTest U φ) : IntegrableOn (fun x => dot (F x) (gradient φ x)) U volume := by
  unfold dot
  exact integrable_finsetSum _ fun i _ =>
    integrableOn_mul_spatialTest (hF i) (isSpatialTest_coordinateDerivative hφ i)

/-- The weak divergence of a difference of fields. -/
theorem hasWeakDivergence_sub {U : Set (Vec d)} {F₁ F₂ : Vec d → Vec d} {h₁ h₂ : Vec d → ℝ}
    (H₁ : HasWeakDivergence U F₁ h₁) (H₂ : HasWeakDivergence U F₂ h₂) :
    HasWeakDivergence U (fun x => F₁ x - F₂ x) (fun x => h₁ x - h₂ x) := by
  refine ⟨fun i => (H₁.1 i).sub (H₂.1 i), H₁.2.1.sub H₂.2.1, fun φ hφ => ?_⟩
  beta_reduce
  have e1 : (fun x => dot (F₁ x - F₂ x) (gradient φ x)) =
      fun x => dot (F₁ x) (gradient φ x) - dot (F₂ x) (gradient φ x) := by
    funext x
    simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have e2 : (fun x => (h₁ x - h₂ x) * φ x) = fun x => h₁ x * φ x - h₂ x * φ x := by
    funext x
    ring
  rw [e1, e2, integral_sub (integrableOn_dot_gradient_of_locallyIntegrableOn H₁.1 hφ)
      (integrableOn_dot_gradient_of_locallyIntegrableOn H₂.1 hφ),
    integral_sub (integrableOn_mul_spatialTest H₁.2.1 hφ) (integrableOn_mul_spatialTest H₂.2.1 hφ),
    H₁.2.2 φ hφ, H₂.2.2 φ hφ]
  ring

/-! ## The difference of a selected and a corrected coordinate -/

variable {Λ : ℝ}

/-- The difference `v = w - ((x - z)_i + φ)` of a local harmonic function on `B_T(z)` and a
corrected coordinate is square integrable together with its gradient `∇w - (e_i + ∇φ)`, and
`a`-harmonic, on every ball `B_ρ(z)` with `ρ ≤ T`. -/
theorem selected_sub_corrected_props {a : CoefficientField d Λ} {z : Vec d} {T ρ : ℝ}
    (hρT : ρ ≤ T) (w : LocalHarmonic a z T) (i : Fin d) {φ : Vec d → ℝ} {g : Vec d → Vec d}
    (hφg : HasWeakGradient Set.univ φ g)
    (hloc : ∀ R : ℝ, 0 < R → MemLp φ 2 (volume.restrict (ball 0 R)) ∧
      MemLp g 2 (volume.restrict (ball 0 R)))
    (harm : HasWeakDivergence Set.univ (fun x => (a x).mulVec (unitVector i + g x))
      (fun _ => 0)) :
    MemLp (fun x => w.potential x - ((x - z) i + φ x)) 2 (volume.restrict (ball z ρ)) ∧
      (∀ k, MemLp (fun x => (w.grad x - (unitVector i + g x)) k) 2
        (volume.restrict (ball z ρ))) ∧
      HasWeakGradient (ball z ρ) (fun x => w.potential x - ((x - z) i + φ x))
        (fun x => w.grad x - (unitVector i + g x)) ∧
      HasWeakDivergence (ball z ρ) (fun x => (a x).mulVec (w.grad x - (unitVector i + g x)))
        (fun _ => 0) := by
  set h := localCorrectedCoordinate a z T i 0 φ g hφg hloc harm with hh
  have hpot : h.potential = fun x => (x - z) i + φ x := by
    funext x
    simp [hh, localCorrectedCoordinate]
  have hgrad : h.grad = fun x => unitVector i + g x := rfl
  have hsub : ball z ρ ⊆ ball z T := fun _ hx => lt_of_lt_of_le hx hρT
  have hmono : volume.restrict (ball z ρ) ≤ volume.restrict (ball z T) :=
    Measure.restrict_mono hsub le_rfl
  refine ⟨?_, fun k => ?_, ?_, ?_⟩
  · have h1 := w.square_integrable.sub h.square_integrable
    rw [hpot] at h1
    exact h1.mono_measure hmono
  · have h1 := (w.memLp_grad k).sub (h.memLp_grad k)
    rw [hgrad] at h1
    exact h1.mono_measure hmono
  · have h1 := hasWeakGradient_sub w.weak_gradient h.weak_gradient
    rw [hpot, hgrad] at h1
    exact hasWeakGradient_mono hsub h1
  · have h1 := hasWeakDivergence_sub w.harmonic h.harmonic
    rw [hgrad] at h1
    have h2 : HasWeakDivergence (ball z T)
        (fun x => (a x).mulVec (w.grad x - (unitVector i + g x))) (fun _ => 0) := by
      have e1 : (fun x => (a x).mulVec (w.grad x - (unitVector i + g x))) =
          fun x => (a x).mulVec (w.grad x) - (a x).mulVec (unitVector i + g x) := by
        funext x
        rw [Matrix.mulVec_sub]
      have e2 : (fun _ : Vec d => (0 : ℝ)) = fun _ => (0 : ℝ) - 0 := by
        funext x
        ring
      rw [e1, e2]
      exact h1
    exact hasWeakDivergence_mono_set hsub h2

/-- **Caccioppoli for the difference of a selected and a corrected coordinate**, from `B_S(z)` to
`B_{S/2}(z)`. -/
theorem integral_euclideanSq_selected_sub_corrected_le (hΛ : 1 ≤ Λ) {a : CoefficientField d Λ}
    {z : Vec d} {T S : ℝ} (hS : 0 < S) (hST : S ≤ T) (w : LocalHarmonic a z T) (i : Fin d)
    {φ : Vec d → ℝ} {g : Vec d → Vec d} (hφg : HasWeakGradient Set.univ φ g)
    (hloc : ∀ R : ℝ, 0 < R → MemLp φ 2 (volume.restrict (ball 0 R)) ∧
      MemLp g 2 (volume.restrict (ball 0 R)))
    (harm : HasWeakDivergence Set.univ (fun x => (a x).mulVec (unitVector i + g x))
      (fun _ => 0)) (k : ℝ) :
    ∫ x in ball z (S / 2), euclideanSq (w.grad x - (unitVector i + g x)) ≤
      4 * Λ * (64 / S) ^ 2 * ∫ x in ball z S, (w.potential x - (x - z) i - φ x - k) ^ 2 := by
  obtain ⟨hv, hg, hw, hdiv⟩ := selected_sub_corrected_props hST w i hφg hloc harm
  have h := caccioppoli_ball hΛ a (half_pos hS) (half_lt_self hS) hv hg hw hdiv k
  have e1 : (32 / (S - S / 2)) = 64 / S := by field_simp; ring
  have e2 : (fun x => (w.potential x - ((x - z) i + φ x) - k) ^ 2) =
      fun x => (w.potential x - (x - z) i - φ x - k) ^ 2 := by
    funext x
    ring
  rw [e1, e2] at h
  exact h

/-! ## The two analytic inputs and the combination -/

/-- **The excess decay of one slope at every center, in ball form** (Theorem C of
Armstrong–Kuusi–Loher on the balls `B_t(z)`): there are `L ≥ 1` and constants `C_ϑ` such that
for every `τ < d` there is `C_τ` with the following property. For every law, homogenization data
`S` and center `z` there is a random radius `X ≥ 1` with `X ≤ O_τ(C_τ)` such that almost surely,
for every `R ≥ X` and every `a`-harmonic `v` on `B_{LR}(z)` with gradient `g`, and every
`ϑ ∈ (0, 1)`, there is one slope `e` with `|e|² |B_{LR}| ≤ C_ϑ ∫_{B_{LR}(z)} |g|²` and
`∫_{B_t(z)} |g - ∑_j e_j W_j|² |B_{LR}| ≤ C_ϑ (t/R)^{2ϑ} |B_t| ∫_{B_{LR}(z)} |g|²` for
`X ≤ t ≤ R`, `W_j = correctorColumn S a j`. -/
def BallExcessDecay (d : ℕ) (Λ : ℝ) : Prop :=
  ∃ (L : ℝ) (Cϑ : ℝ → ℝ), 1 ≤ L ∧ (∀ ϑ, 0 < Cϑ ϑ) ∧
    ∀ τ : ℝ, 0 < τ → τ < d → ∃ Cτ : ℝ, 0 < Cτ ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
        ∀ z : Vec d, ∃ X : CoefficientField d Λ → ℝ, Measurable X ∧ OsBound P X τ Cτ ∧
          (∀ a, 1 ≤ X a) ∧ ∀ᵐ a ∂P, ∀ R : ℝ, X a ≤ R →
            ∀ (v : Vec d → ℝ) (g : Vec d → Vec d),
              MemLp v 2 (volume.restrict (ball z (L * R))) →
              (∀ k, MemLp (fun x => g x k) 2 (volume.restrict (ball z (L * R)))) →
              HasWeakGradient (ball z (L * R)) v g →
              HasWeakDivergence (ball z (L * R)) (fun x => (a x).mulVec (g x)) (fun _ => 0) →
              ∀ ϑ : ℝ, 0 < ϑ → ϑ < 1 → ∃ e : Vec d,
                euclideanSq e * volume.real (ball z (L * R)) ≤
                    Cϑ ϑ * ∫ x in ball z (L * R), euclideanSq (g x) ∧
                  ∀ t : ℝ, X a ≤ t → t ≤ R →
                    (∫ x in ball z t, euclideanSq (g x - ∑ j, e j • correctorColumn S a j x)) *
                        volume.real (ball z (L * R)) ≤
                      Cϑ ϑ * (t / R) ^ (2 * ϑ) * volume.real (ball z t) *
                        ∫ x in ball z (L * R), euclideanSq (g x)

/-- **The observation estimate for the selected coordinates** at the intermediate scale
`S = r^{1+δ-ε}`: there are `μ > 0` and `C₁` such that for every law there is a homogenization
data such that for every localized family, center and scale `r ≥ 2` there are nonnegative
`X, Y` with `X^γ ≤ O_s(C₁)` and `Y ≤ O_s(C₁ S^{-β})`, and almost surely, if `X ≤ r`, then
`Y ≤ C₁ r^{-μ}` and every `v_i = w_i - (x - z)_i - φ_{e_i}` has
`∫_{B_S(z)} (v_i - k_i)² ≤ (S Y)² |B_S|` for a constant `k_i`. -/
def LocalizationObservationEstimate (d : ℕ) (Λ s δ γ α σ θ C₀ β : ℝ) : Prop :=
  ∃ μ C₁ : ℝ, 0 < μ ∧ 0 < C₁ ∧
    ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∃ S : HomogenizationData P,
      ∀ (W : LocalizedFamily d Λ δ γ α σ θ C₀) (z : Vec d) (r : ℝ) (hr : 2 ≤ r),
        ∃ X Y : CoefficientField d Λ → ℝ, (∀ a, 0 ≤ X a) ∧ (∀ a, 0 ≤ Y a) ∧
          AEOsBound P (fun a => X a ^ γ) s C₁ ∧
          AEOsBound P Y s (C₁ * localizationIntermediateRadius δ α γ r ^ (-β)) ∧
          ∀ᵐ a ∂P, X a ≤ r → Y a ≤ C₁ * r ^ (-μ) ∧ ∀ i, ∃ k : ℝ,
            ∫ x in ball z (localizationIntermediateRadius δ α γ r),
                (((W a z r hr).coordinate i).potential x - (x - z) i -
                  (S.corrector (unitVector i)).potential a x - k) ^ 2 ≤
              (localizationIntermediateRadius δ α γ r * Y a) ^ 2 *
                volume.real (ball z (localizationIntermediateRadius δ α γ r))

/-- The observation estimate on a class `L` of laws: `LocalizationObservationEstimate` with the
laws restricted to `L` and the constants chosen before the law. -/
def LocalizationObservationEstimateOn {d : ℕ} {Λ : ℝ} (L : Measure (CoefficientField d Λ) → Prop)
    (s δ γ α σ θ C₀ β : ℝ) : Prop :=
  ∃ μ C₁ : ℝ, 0 < μ ∧ 0 < C₁ ∧
    ∀ P : Measure (CoefficientField d Λ), L P → ∃ S : HomogenizationData P,
      ∀ (W : LocalizedFamily d Λ δ γ α σ θ C₀) (z : Vec d) (r : ℝ) (hr : 2 ≤ r),
        ∃ X Y : CoefficientField d Λ → ℝ, (∀ a, 0 ≤ X a) ∧ (∀ a, 0 ≤ Y a) ∧
          AEOsBound P (fun a => X a ^ γ) s C₁ ∧
          AEOsBound P Y s (C₁ * localizationIntermediateRadius δ α γ r ^ (-β)) ∧
          ∀ᵐ a ∂P, X a ≤ r → Y a ≤ C₁ * r ^ (-μ) ∧ ∀ i, ∃ k : ℝ,
            ∫ x in ball z (localizationIntermediateRadius δ α γ r),
                (((W a z r hr).coordinate i).potential x - (x - z) i -
                  (S.corrector (unitVector i)).potential a x - k) ^ 2 ≤
              (localizationIntermediateRadius δ α γ r * Y a) ^ 2 *
                volume.real (ball z (localizationIntermediateRadius δ α γ r))

/-- **The single-slope estimate of Lemma 4.21 on a class `L` of laws**, with the constants chosen
before the law: `LocalizationSlopeEstimate` with the laws restricted to `L`. -/
def SlopeEstimateOnClass {d : ℕ} {Λ : ℝ} (L : Measure (CoefficientField d Λ) → Prop)
    (s δ γ α σ θ C₀ : ℝ) : Prop :=
  ∃ (c K₁ C₁ : ℝ), 0 < c ∧ c ≤ 1 ∧ 0 ≤ K₁ ∧ 0 < C₁ ∧
    ∀ P : Measure (CoefficientField d Λ), L P → ∃ S : HomogenizationData P,
      ∀ (W : LocalizedFamily d Λ δ γ α σ θ C₀) (z : Vec d) (r : ℝ) (hr : 2 ≤ r),
        ∃ X Y : CoefficientField d Λ → ℝ, (∀ a, 0 ≤ X a) ∧ (∀ a, 0 ≤ Y a) ∧
          AEOsBound P (fun a => X a ^ γ) s C₁ ∧ AEOsBound P Y s (C₁ * r ^ (-γ)) ∧
          ∀ᵐ a ∂P, X a ≤ r → ∃ b : Fin d → Fin d → ℝ, ∑ i, ∑ j, b i j ^ 2 ≤ 1 / 4 ∧
            ∀ i, ∀ t : ℝ, r ≤ t → t ≤ c * localizationIntermediateRadius δ α γ r →
              ∫ x in ball z t, euclideanSq (((W a z r hr).coordinate i).grad x -
                (correctorColumn S a i x + ∑ j, b i j • correctorColumn S a j x)) ≤
                  K₁ * Y a ^ 2 * (t / r) ^ 2 * volume.real (ball z t)

theorem le_localizationIntermediateRadius {δ α γ r : ℝ} (hδ : 0 < δ) (hr : 1 ≤ r) :
    r ≤ localizationIntermediateRadius δ α γ r := by
  have hε : localizationEpsilon δ α γ ≤ δ / 2 := min_le_right _ _
  unfold localizationIntermediateRadius
  calc r = r ^ (1 : ℝ) := (Real.rpow_one r).symm
    _ ≤ r ^ (1 + δ - localizationEpsilon δ α γ) :=
      Real.rpow_le_rpow_of_exponent_le hr (by linarith)

theorem localizationIntermediateRadius_le_outer {δ α γ r : ℝ} (hδ : 0 < δ) (hα : 0 < α)
    (hαγ : γ < α * (1 + δ) + δ) (hr : 1 ≤ r) :
    localizationIntermediateRadius δ α γ r ≤ localizationOuterRadius δ r := by
  have hε := localizationEpsilon_pos hδ hα hαγ
  unfold localizationIntermediateRadius localizationOuterRadius
  exact Real.rpow_le_rpow_of_exponent_le hr (by linarith)

theorem exists_rpow_neg_small {μ A : ℝ} (hμ : 0 < μ) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ r : ℝ, R ≤ r → A * r ^ (-μ) ≤ 1 / 4 := by
  have h1 : Tendsto (fun r : ℝ => A * r ^ (-μ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop hμ).const_mul A
  obtain ⟨R, hR⟩ := eventually_atTop.1 ((tendsto_order.1 h1).2 (1 / 4) (by norm_num))
  exact ⟨max R 1, le_max_right _ _, fun r hr => (hR r (le_trans (le_max_left _ _) hr)).le⟩

theorem rpow_le_sq_of_one_le {x ϑ : ℝ} (hx : 1 ≤ x) (hϑ : ϑ ≤ 1) : x ^ (2 * ϑ) ≤ x ^ 2 := by
  have h := Real.rpow_le_rpow_of_exponent_le hx (by linarith : 2 * ϑ ≤ (2 : ℝ))
  rwa [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h

/-- **The single-slope estimate of Lemma 4.21 from the excess decay of one slope and the
observation estimate**, for every exponent budget `(r/S)^ϑ S^{-β} ≤ r^{-γ}`. -/
theorem slopeEstimateOnClass_of_excess_observation (hΛ : 1 ≤ Λ)
    {Lw : Measure (CoefficientField d Λ) → Prop} (hLw : ∀ P, Lw P → LawHypotheses P)
    {s δ γ α σ θ C₀ β ϑ : ℝ} (hs : 1 ≤ s) (hδ : 0 < δ) (hα : 0 < α)
    (hαγ : γ < α * (1 + δ) + δ) (hγ : 0 < γ) (hγs : s * γ < d) (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1)
    (hexp : ∀ r : ℝ, 1 ≤ r → (r / localizationIntermediateRadius δ α γ r) ^ ϑ *
      localizationIntermediateRadius δ α γ r ^ (-β) ≤ r ^ (-γ))
    (hA : BallExcessDecay d Λ) (hC : LocalizationObservationEstimateOn Lw s δ γ α σ θ C₀ β) :
    SlopeEstimateOnClass Lw s δ γ α σ θ C₀ := by
  obtain ⟨L, Cϑ, hL, hCϑ, hAτ⟩ := hA
  have hs0 : 0 < s := by linarith
  obtain ⟨Cτ, hCτ, hAP⟩ := hAτ (s * γ) (by positivity) hγs
  obtain ⟨μ, C₁, hμ, hC₁, hCP⟩ := hC
  have hΛ0 : 0 < Λ := by linarith
  set A₀ : ℝ := Cϑ ϑ * (4 * Λ * 64 ^ 2 * 2 ^ d) with hA₀
  have hA₀0 : 0 < A₀ := mul_pos (hCϑ ϑ) (by positivity)
  obtain ⟨R₀, hR₀1, hR₀⟩ := exists_rpow_neg_small (A := d * A₀ * C₁ ^ 2) (by linarith : 0 < 2 * μ)
  have hL0 : 0 < L := by linarith
  have h2L : 1 ≤ 2 * L := by linarith
  have hl2 : 0 < Real.log 2 ^ s⁻¹ := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _
  have hRγ : 0 < R₀ ^ γ := Real.rpow_pos_of_pos (by linarith) _
  have h2Lγ : (0 : ℝ) < (2 * L) ^ γ := Real.rpow_pos_of_pos (by linarith) _
  have hCτγ : 0 < Cτ ^ γ := Real.rpow_pos_of_pos hCτ _
  refine ⟨1 / (2 * L), A₀ * (2 * L) ^ 2, C₁ + (2 * L) ^ γ * Cτ ^ γ + R₀ ^ γ / Real.log 2 ^ s⁻¹,
    div_pos one_pos (by linarith), by rw [div_le_one (by linarith)]; linarith,
    mul_nonneg hA₀0.le (sq_nonneg _),
    by have := div_pos hRγ hl2; have := mul_pos h2Lγ hCτγ; linarith, fun P hP => ?_⟩
  have hPl : LawHypotheses P := hLw P hP
  have : IsProbabilityMeasure P := hPl.1
  obtain ⟨S, hSobs⟩ := hCP P hP
  refine ⟨S, fun W z r hr => ?_⟩
  obtain ⟨X₁, Y₀, hX₁0, hY₀0, hX₁os, hY₀os, hCae⟩ := hSobs W z r hr
  obtain ⟨X₂, hX₂m, hX₂os, hX₂1, hAae⟩ := hAP P hPl S z
  have hr0 : 0 < r := by linarith
  have hr1 : 1 ≤ r := by linarith
  set Sr := localizationIntermediateRadius δ α γ r with hSr
  have hrS : r ≤ Sr := le_localizationIntermediateRadius hδ hr1
  have hS0 : 0 < Sr := lt_of_lt_of_le hr0 hrS
  have hST : Sr ≤ localizationOuterRadius δ r :=
    localizationIntermediateRadius_le_outer hδ hα hαγ hr1
  have hq0 : 0 < (r / Sr) ^ ϑ := Real.rpow_pos_of_pos (div_pos hr0 hS0) _
  have hX₂0 : ∀ a, 0 ≤ X₂ a := fun a => zero_le_one.trans (hX₂1 a)
  refine ⟨fun a => max (max (X₁ a) (2 * L * X₂ a)) R₀, fun a => (r / Sr) ^ ϑ * Y₀ a,
    fun a => le_trans (hX₁0 a) ((le_max_left _ _).trans (le_max_left _ _)),
    fun a => mul_nonneg hq0.le (hY₀0 a), ?_, ?_, ?_⟩
  · -- the stochastic integrability of the combined radius
    have hpow : ∀ a, max (max (X₁ a) (2 * L * X₂ a)) R₀ ^ γ =
        max (max (X₁ a ^ γ) ((2 * L) ^ γ * X₂ a ^ γ)) (R₀ ^ γ) := fun a => by
      rw [rpow_max_of_nonneg (le_max_of_le_left (hX₁0 a)) (by linarith) hγ.le,
        rpow_max_of_nonneg (hX₁0 a) (mul_nonneg (by linarith) (hX₂0 a)) hγ.le,
        Real.mul_rpow (by linarith) (hX₂0 a)]
    have hX₂γ : AEOsBound P (fun a => (2 * L) ^ γ * X₂ a ^ γ) s ((2 * L) ^ γ * Cτ ^ γ) := by
      have h1 := hX₂os.rpow hX₂0 hγ
      rw [show s * γ / γ = s by field_simp] at h1
      exact (h1.aeOsBound_of_ae_eq EventuallyEq.rfl).const_mul h2Lγ
    have hconst : AEOsBound P (fun _ => R₀ ^ γ) s (R₀ ^ γ / Real.log 2 ^ s⁻¹) :=
      (osBound_of_le_const measurable_const hs0 hRγ
        (Eventually.of_forall fun _ => le_rfl)).aeOsBound_of_ae_eq EventuallyEq.rfl
    have hsum := (hX₁os.add hX₂γ hs).add hconst hs
    refine hsum.of_le_ae ?_ (Eventually.of_forall fun a => ?_)
    · have hm : AEMeasurable (fun a => max (max (X₁ a ^ γ) ((2 * L) ^ γ * X₂ a ^ γ)) (R₀ ^ γ))
          P := (hX₁os.1.max hX₂γ.1).max aemeasurable_const
      exact hm.congr (Eventually.of_forall fun a => (hpow a).symm)
    · rw [hpow a]
      have h1 := Real.rpow_nonneg (hX₁0 a) γ
      have h2 : 0 ≤ (2 * L) ^ γ * X₂ a ^ γ := mul_nonneg h2Lγ.le (Real.rpow_nonneg (hX₂0 a) γ)
      simp only [max_le_iff]
      refine ⟨⟨by linarith, by linarith⟩, by linarith⟩
  · -- the stochastic integrability of the slope error
    refine (hY₀os.const_mul hq0).mono_scale ?_
    calc (r / Sr) ^ ϑ * (C₁ * Sr ^ (-β)) = C₁ * ((r / Sr) ^ ϑ * Sr ^ (-β)) := by ring
      _ ≤ C₁ * r ^ (-γ) := mul_le_mul_of_nonneg_left (hexp r hr1) hC₁.le
      _ ≤ (C₁ + (2 * L) ^ γ * Cτ ^ γ + R₀ ^ γ / Real.log 2 ^ s⁻¹) * r ^ (-γ) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hr0.le _)
          have := div_pos hRγ hl2; have := mul_pos h2Lγ hCτγ; linarith
  · -- the pathwise estimate on the good event
    filter_upwards [hCae, hAae,
      ae_all_iff.2 fun i : Fin d => (S.corrector (unitVector i)).weak_gradient,
      ae_all_iff.2 fun i : Fin d => (S.corrector (unitVector i)).locally_square_integrable,
      ae_all_iff.2 fun i : Fin d => (S.corrector (unitVector i)).harmonic]
      with a hCa hAa hwg hloc harm hXr
    simp only [max_le_iff] at hXr
    obtain ⟨⟨hX₁r, hX₂r⟩, hR₀r⟩ := hXr
    obtain ⟨hYsmall, hobs⟩ := hCa hX₁r
    set R := Sr / (2 * L) with hRdef
    have hL0' := hL0.ne'
    have hS0' := hS0.ne'
    have hr0' := hr0.ne'
    have hLR : L * R = Sr / 2 := by rw [hRdef]; field_simp
    have hX₂R : X₂ a ≤ R := by
      rw [hRdef, le_div_iff₀ (by linarith)]
      nlinarith
    have hX₂r' : X₂ a ≤ r := by nlinarith [hX₂1 a]
    have hBS2 : 0 < volume.real (ball z (Sr / 2)) := volume_real_ball_pos z (half_pos hS0)
    have hBS : volume.real (ball z Sr) = 2 ^ d * volume.real (ball z (Sr / 2)) := by
      rw [volume_real_ball_eq_mul z hS0, volume_real_ball_eq_mul z (half_pos hS0), div_pow]
      have h2d : (2 : ℝ) ^ d ≠ 0 := by positivity
      field_simp
    -- the energy of `∇v_i` on `B_{S/2}(z)`
    have hen : ∀ i : Fin d, ∫ x in ball z (Sr / 2),
        euclideanSq (((W a z r hr).coordinate i).grad x -
          (unitVector i + (S.corrector (unitVector i)).grad a x)) ≤
          4 * Λ * 64 ^ 2 * 2 ^ d * Y₀ a ^ 2 * volume.real (ball z (Sr / 2)) := by
      intro i
      obtain ⟨k, hk⟩ := hobs i
      have h1 := integral_euclideanSq_selected_sub_corrected_le hΛ hS0 hST
        ((W a z r hr).coordinate i) i (hwg i) (hloc i) (harm i) k
      refine h1.trans ?_
      calc 4 * Λ * (64 / Sr) ^ 2 * ∫ x in ball z Sr,
            (((W a z r hr).coordinate i).potential x - (x - z) i -
              (S.corrector (unitVector i)).potential a x - k) ^ 2
          ≤ 4 * Λ * (64 / Sr) ^ 2 * ((Sr * Y₀ a) ^ 2 * volume.real (ball z Sr)) :=
            mul_le_mul_of_nonneg_left hk (mul_nonneg (by linarith) (sq_nonneg _))
        _ = 4 * Λ * 64 ^ 2 * 2 ^ d * Y₀ a ^ 2 * volume.real (ball z (Sr / 2)) := by
            rw [hBS]
            have h64 : (64 / Sr) ^ 2 * Sr ^ 2 = 64 ^ 2 := by field_simp
            linear_combination (4 * Λ * Y₀ a ^ 2 * 2 ^ d * volume.real (ball z (Sr / 2))) * h64
    -- the excess decay at `R = S/(2L)`
    have hslope : ∀ i : Fin d, ∃ e : Vec d, euclideanSq e ≤ A₀ * Y₀ a ^ 2 ∧
        ∀ t : ℝ, X₂ a ≤ t → t ≤ R →
          ∫ x in ball z t, euclideanSq ((((W a z r hr).coordinate i).grad x -
            (unitVector i + (S.corrector (unitVector i)).grad a x)) -
              ∑ j, e j • correctorColumn S a j x) ≤
            A₀ * (t / R) ^ (2 * ϑ) * Y₀ a ^ 2 * volume.real (ball z t) := by
      intro i
      obtain ⟨hv, hg, hw, hdiv⟩ := selected_sub_corrected_props (ρ := L * R)
        (by rw [hLR]; linarith) ((W a z r hr).coordinate i) i (hwg i) (hloc i) (harm i)
      obtain ⟨e, he, hzoom⟩ := hAa R hX₂R _ _ hv hg hw hdiv ϑ hϑ0 hϑ1
      rw [hLR] at he hzoom
      refine ⟨e, ?_, fun t ht1 ht2 => ?_⟩
      · have h1 := he.trans (mul_le_mul_of_nonneg_left (hen i) (hCϑ ϑ).le)
        have h2 : euclideanSq e * volume.real (ball z (Sr / 2)) ≤
            (A₀ * Y₀ a ^ 2) * volume.real (ball z (Sr / 2)) := by
          rw [hA₀]; linarith
        exact le_of_mul_le_mul_right h2 hBS2
      · have hR0 : 0 < R := lt_of_lt_of_le (zero_lt_one.trans_le (hX₂1 a)) hX₂R
        have htR0 : 0 ≤ t / R := div_nonneg ((zero_le_one.trans (hX₂1 a)).trans ht1) hR0.le
        have h1 := (hzoom t ht1 ht2).trans (mul_le_mul_of_nonneg_left (hen i)
          (mul_nonneg (mul_nonneg (hCϑ ϑ).le (Real.rpow_nonneg htR0 _)) measureReal_nonneg))
        have h2 : (∫ x in ball z t, euclideanSq ((((W a z r hr).coordinate i).grad x -
            (unitVector i + (S.corrector (unitVector i)).grad a x)) -
              ∑ j, e j • correctorColumn S a j x)) * volume.real (ball z (Sr / 2)) ≤
            (A₀ * (t / R) ^ (2 * ϑ) * Y₀ a ^ 2 * volume.real (ball z t)) *
              volume.real (ball z (Sr / 2)) := by
          refine h1.trans (le_of_eq ?_)
          rw [hA₀]; ring
        exact le_of_mul_le_mul_right h2 hBS2
    choose e he hzoom using hslope
    refine ⟨fun i j => e i j, ?_, fun i t hrt htS => ?_⟩
    · -- the slopes are small on the good event
      have hY2 : Y₀ a ^ 2 ≤ (C₁ * r ^ (-μ)) ^ 2 :=
        pow_le_pow_left₀ (hY₀0 a) hYsmall 2
      have hsum : ∑ i, ∑ j, e i j ^ 2 ≤ ∑ _i : Fin d, A₀ * (C₁ * r ^ (-μ)) ^ 2 :=
        Finset.sum_le_sum fun i _ => by
          have := he i
          unfold euclideanSq dot at this
          simp only [← sq] at this
          nlinarith [mul_le_mul_of_nonneg_left hY2 hA₀0.le]
      have hrμ : (r ^ (-μ)) ^ 2 = r ^ (-(2 * μ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
        congr 1
        push_cast
        ring
      have h3 := hR₀ r hR₀r
      calc ∑ i, ∑ j, e i j ^ 2 ≤ ∑ _i : Fin d, A₀ * (C₁ * r ^ (-μ)) ^ 2 := hsum
        _ = d * A₀ * C₁ ^ 2 * r ^ (-(2 * μ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_pow, hrμ]
          ring
        _ ≤ 1 / 4 := h3
    · -- the slope estimate below `S/(2L)`
      have hX₂t : X₂ a ≤ t := hX₂r'.trans hrt
      have htR : t ≤ R := by
        rw [hRdef]
        calc t ≤ 1 / (2 * L) * Sr := htS
          _ = Sr / (2 * L) := by ring
      have h1 := hzoom i t hX₂t htR
      have hint : (fun x => euclideanSq ((((W a z r hr).coordinate i).grad x -
            (unitVector i + (S.corrector (unitVector i)).grad a x)) -
              ∑ j, e i j • correctorColumn S a j x)) =
          fun x => euclideanSq (((W a z r hr).coordinate i).grad x -
            (correctorColumn S a i x + ∑ j, e i j • correctorColumn S a j x)) := by
        funext x
        rw [sub_sub]
        rfl
      rw [hint] at h1
      refine h1.trans ?_
      have ht0 : 0 < t := lt_of_lt_of_le hr0 hrt
      have htr : 1 ≤ t / r := by rw [le_div_iff₀ hr0]; linarith
      have hsplit : t / R = (2 * L) * (t / r) * (r / Sr) := by
        rw [hRdef]
        field_simp
      have hpow : (t / R) ^ (2 * ϑ) ≤ (2 * L) ^ 2 * (t / r) ^ 2 * ((r / Sr) ^ ϑ) ^ 2 := by
        rw [hsplit, Real.mul_rpow (mul_nonneg (by linarith) (div_nonneg ht0.le hr0.le))
            (div_pos hr0 hS0).le,
          Real.mul_rpow (by linarith) (div_nonneg ht0.le hr0.le)]
        have e1 : (r / Sr) ^ (2 * ϑ) = ((r / Sr) ^ ϑ) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (div_pos hr0 hS0).le]
          congr 1
          push_cast
          ring
        rw [e1]
        have h2L' := rpow_le_sq_of_one_le h2L hϑ1.le
        have htr' := rpow_le_sq_of_one_le htr hϑ1.le
        have hq2 : 0 ≤ ((r / Sr) ^ ϑ) ^ 2 := sq_nonneg _
        exact mul_le_mul_of_nonneg_right (mul_le_mul h2L' htr' (Real.rpow_nonneg (by linarith) _)
          (by positivity)) hq2
      refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hA₀0.le) (sq_nonneg _)) measureReal_nonneg).trans
          (le_of_eq ?_)
      ring

/-- **The single-slope estimate of Lemma 4.21 from the excess decay of one slope and the
observation estimate**, for every exponent budget `(r/S)^ϑ S^{-β} ≤ r^{-γ}`. -/
theorem localizationSlopeEstimate_of_excess_observation (hΛ : 1 ≤ Λ)
    {s δ γ α σ θ C₀ β ϑ : ℝ} (hs : 1 ≤ s) (hδ : 0 < δ) (hα : 0 < α)
    (hαγ : γ < α * (1 + δ) + δ) (hγ : 0 < γ) (hγs : s * γ < d) (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1)
    (hexp : ∀ r : ℝ, 1 ≤ r → (r / localizationIntermediateRadius δ α γ r) ^ ϑ *
      localizationIntermediateRadius δ α γ r ^ (-β) ≤ r ^ (-γ))
    (hA : BallExcessDecay d Λ) (hC : LocalizationObservationEstimate d Λ s δ γ α σ θ C₀ β) :
    LocalizationSlopeEstimate d Λ s δ γ α σ θ C₀ :=
  slopeEstimateOnClass_of_excess_observation hΛ (Lw := LawHypotheses) (fun _ h => h) hs hδ hα
    hαγ hγ hγs hϑ0 hϑ1 hexp hA hC

end QSH
