import QuantitativeStochasticHomogenization.Ch04.Sec01.BaseExponent

/-!
# Averages of `J₁` over the heat semigroup

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3. The improvement of additivity (Proposition 4.10) compares `J₁(Φ_{z,R}, p, q)` with the
average `∫ Φ_{z,√(R²-r²)}(y) J₁(Φ_{y,r}, p, q) dy` of Definition 4.7. By the semigroup property
`∫ Φ_{z,ρ}(y) Φ_{y,r}(x) dy = Φ_{z,√(ρ²+r²)}(x)` and Fubini's theorem, the functional of (4.8) at a
fixed gradient field is the average of its values at the smaller masks
(`j1Functional_heatKernel_eq_integral`); since `J₁` is a supremum of these functionals, a
supremum of averages is at most the average of the suprema:
`J₁(Φ_{z,R}, p, q) ≤ ∫ Φ_{z,√(R²-r²)}(y) J₁(Φ_{y,r}, p, q) dy` (`J1Heat_le_integral_heatKernel_mul`).
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## The heat kernel masks -/

theorem continuous_heatKernel_uncurry (r : ℝ) :
    Continuous fun w : Vec d × Vec d => heatKernel w.1 r w.2 := by
  unfold heatKernel euclideanHeatKernel euclideanSq dot
  fun_prop

theorem heatKernel_pos (z : Vec d) {r : ℝ} (hr : 0 < r) (x : Vec d) : 0 < heatKernel z r x := by
  unfold heatKernel euclideanHeatKernel
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

theorem heatKernel_le (z : Vec d) {r : ℝ} (hr : 0 < r) (x : Vec d) :
    heatKernel z r x ≤ (4 * Real.pi * r ^ 2) ^ (-(d : ℝ) / 2) := by
  unfold heatKernel euclideanHeatKernel
  have h1 : Real.exp (-euclideanSq (x - z) / (4 * r ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (euclideanSq_nonneg _)) (by positivity)
  have h2 : 0 ≤ (4 * Real.pi * r ^ 2) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
  nlinarith

theorem sqrt_sq_sub_sq_pos {r R : ℝ} (hrR : r < R) (hr : 0 ≤ r) : 0 < Real.sqrt (R ^ 2 - r ^ 2) :=
  Real.sqrt_pos.mpr (by nlinarith)

theorem sqrt_sqrt_sq_sub_sq_add_sq {r R : ℝ} (hrR : r < R) (hr : 0 ≤ r) :
    Real.sqrt (Real.sqrt (R ^ 2 - r ^ 2) ^ 2 + r ^ 2) = R := by
  rw [Real.sq_sqrt (by nlinarith), sub_add_cancel, Real.sqrt_sq (by linarith)]

/-! ## Fubini for the heat semigroup -/

/-- **Heat semigroup and Fubini**: for `0 < r < R`, `ρ = √(R² - r²)` and `f` with `Φ_{z,R} f`
integrable, the functions `x ↦ Φ_{y,r}(x) f(x)` are integrable for almost every `y`,
`y ↦ Φ_{z,ρ}(y) ∫ Φ_{y,r} f` is integrable, and `∫ Φ_{z,R} f = ∫ Φ_{z,ρ}(y) (∫ Φ_{y,r} f) dy`. -/
theorem integral_heatKernel_mul_eq_integral_integral (z : Vec d) {r R : ℝ} (hr : 0 < r)
    (hrR : r < R) {f : Vec d → ℝ} (hI : Integrable fun x => heatKernel z R x * f x) :
    (∀ᵐ y ∂(volume : Measure (Vec d)), Integrable fun x => heatKernel y r x * f x) ∧
      (Integrable fun y => heatKernel z (Real.sqrt (R ^ 2 - r ^ 2)) y *
        ∫ x, heatKernel y r x * f x) ∧
      (∫ x, heatKernel z R x * f x) =
        ∫ y, heatKernel z (Real.sqrt (R ^ 2 - r ^ 2)) y * ∫ x, heatKernel y r x * f x := by
  set ρ := Real.sqrt (R ^ 2 - r ^ 2) with hρdef
  have hρ : 0 < ρ := sqrt_sq_sub_sq_pos hrR hr.le
  have hR : 0 < R := hr.trans hrR
  have hsemi : ∀ x, ∫ y, heatKernel z ρ y * heatKernel y r x = heatKernel z R x := by
    intro x
    rw [integral_heatKernel_mul_heatKernel hρ hr z x, hρdef, sqrt_sqrt_sq_sub_sq_add_sq hrR hr.le]
  -- measurability of `f`
  have hf : AEStronglyMeasurable f volume := by
    have h1 := hI.aestronglyMeasurable.mul
      (((continuous_heatKernel_uncurry R).comp
        (continuous_const.prodMk continuous_id)).inv₀ fun x =>
          (heatKernel_pos z hR x).ne').aestronglyMeasurable
    refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
    have hpos := (heatKernel_pos z hR x).ne'
    simp only [Function.comp_apply, Pi.mul_apply, Pi.inv_apply, id]
    field_simp
  -- the kernel on the product
  set K : Vec d × Vec d → ℝ := fun w => heatKernel z ρ w.2 * heatKernel w.2 r w.1 with hK
  have hKc : Continuous K :=
    ((continuous_heatKernel_uncurry ρ).comp (continuous_const.prodMk continuous_snd)).mul
      ((continuous_heatKernel_uncurry r).comp (continuous_snd.prodMk continuous_fst))
  set F : Vec d → Vec d → ℝ := fun x y => heatKernel z ρ y * heatKernel y r x * f x with hF
  have hFm : AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) := by
    have := hKc.aestronglyMeasurable.mul (hf.comp_fst (ν := volume))
    refine this.congr (Filter.Eventually.of_forall fun w => ?_)
    simp [hK, hF, Function.uncurry]
  have hslice : ∀ x, Integrable fun y => heatKernel z ρ y * heatKernel y r x := by
    intro x
    refine (integrable_heatKernel z hρ).mul_bdd
      ((continuous_heatKernel_uncurry r).comp
        (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      (c := (4 * Real.pi * r ^ 2) ^ (-(d : ℝ) / 2)) (Filter.Eventually.of_forall fun y => ?_)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (heatKernel_nonneg _ _ _)]
    exact heatKernel_le y hr x
  have hFint : Integrable (Function.uncurry F) (volume.prod volume) := by
    rw [integrable_prod_iff hFm]
    refine ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
    · exact (hslice x).mul_const (f x)
    · have : (fun x => ∫ y, ‖Function.uncurry F (x, y)‖) =
          fun x => ‖heatKernel z R x * f x‖ := by
        funext x
        simp only [Function.uncurry, hF, norm_mul, Real.norm_eq_abs,
          abs_of_nonneg (heatKernel_nonneg _ _ _)]
        rw [integral_mul_const, hsemi x]
      rw [this]
      exact hI.norm
  have hswap := integral_integral_swap hFint
  have hleft : (∫ x, heatKernel z R x * f x) = ∫ x, ∫ y, F x y := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hF]
    rw [integral_mul_const, hsemi x]
  have hright : ∀ y, (∫ x, F x y) = heatKernel z ρ y * ∫ x, heatKernel y r x * f x := by
    intro y
    simp only [hF, mul_assoc]
    exact integral_const_mul _ _
  have hint_right := hFint.integral_prod_right
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hFint.prod_left_ae] with y hy
    have hy' : Integrable fun x => heatKernel z ρ y * (heatKernel y r x * f x) := by
      simpa [Function.uncurry, hF, mul_assoc] using hy
    have hc : heatKernel z ρ y ≠ 0 := (heatKernel_pos z hρ y).ne'
    have := hy'.const_mul (heatKernel z ρ y)⁻¹
    simpa [← mul_assoc, inv_mul_cancel₀ hc] using this
  · refine hint_right.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Function.uncurry]
    exact hright y
  · rw [hleft, hswap]
    exact integral_congr_ae (Filter.Eventually.of_forall hright)

/-! ## The functional of (4.8) and `J₁` over the heat semigroup -/

/-- The integrand of the functional of (4.8) at a gradient field `g`. -/
def j1Integrand (a : CoefficientField d Λ) (p q : Vec d) (g : Vec d → Vec d) (x : Vec d) : ℝ :=
  -(1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x)) - dot p ((a x).mulVec (g x)) + dot q (g x)

theorem j1Functional_eq_integral_j1Integrand (a : CoefficientField d Λ) (mask : Vec d → ℝ)
    (p q : Vec d) (g : Vec d → Vec d) :
    j1Functional a mask p q g = ∫ x, mask x * j1Integrand a p q g x := rfl

/-- **The trial over the heat semigroup**: if the functional of (4.8) at `g` is defined by an
integrable integrand at `Φ_{z,R}`, it is the `Φ_{z,√(R²-r²)}`-average of its values at the masks
`Φ_{y,r}`. -/
theorem j1Functional_heatKernel_eq_integral (a : CoefficientField d Λ) (z : Vec d) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (p q : Vec d) (g : Vec d → Vec d)
    (hI : Integrable fun x => heatKernel z R x * j1Integrand a p q g x) :
    j1Functional a (heatKernel z R) p q g =
      ∫ y, heatKernel z (Real.sqrt (R ^ 2 - r ^ 2)) y * j1Functional a (heatKernel y r) p q g :=
  (integral_heatKernel_mul_eq_integral_integral z hr hrR hI).2.2

/-- **A supremum of averages is at most the average of the suprema**: for `0 < r < R`,
`J₁(Φ_{z,R}, p, q) ≤ ∫ Φ_{z,√(R²-r²)}(y) J₁(Φ_{y,r}, p, q) dy`, provided `y ↦ J₁(Φ_{y,r}, p, q)` is
almost everywhere strongly measurable. -/
theorem J1Heat_le_integral_heatKernel_mul (a : CoefficientField d Λ) (z : Vec d) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (p q : Vec d)
    (hJ : AEStronglyMeasurable (fun y => J1Heat a y r p q) volume) :
    J1Heat a z R p q ≤
      ∫ y, heatKernel z (Real.sqrt (R ^ 2 - r ^ 2)) y * J1Heat a y r p q := by
  set ρ := Real.sqrt (R ^ 2 - r ^ 2) with hρdef
  have hρ : 0 < ρ := sqrt_sq_sub_sq_pos hrR hr.le
  have hR : 0 < R := hr.trans hrR
  set M : ℝ := Λ * euclideanSq p + euclideanSq q with hM
  have hJb : ∀ y, 0 ≤ J1Heat a y r p q ∧ J1Heat a y r p q ≤ M := fun y =>
    J1Heat_nonneg_le a y hr p q
  have hint : Integrable fun y => heatKernel z ρ y * J1Heat a y r p q :=
    (integrable_heatKernel z hρ).mul_bdd hJ (c := M) (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hJb y).1]
      exact (hJb y).2)
  have hnonneg : 0 ≤ ∫ y, heatKernel z ρ y * J1Heat a y r p q :=
    integral_nonneg fun y => mul_nonneg (heatKernel_nonneg _ _ _) (hJb y).1
  unfold J1Heat
  rw [J1_eq_sSup_j1Functional]
  refine csSup_le ⟨0, zeroHarmonicA1 a, (j1Functional_zeroHarmonicA1 a _ p q).symm⟩ ?_
  rintro e ⟨w, rfl⟩
  rw [j1Functional_eq_integral_j1Integrand]
  by_cases hI : Integrable fun x => heatKernel z R x * j1Integrand a p q w.grad x
  · obtain ⟨-, hint2, heq⟩ := integral_heatKernel_mul_eq_integral_integral z hr hrR hI
    rw [heq]
    refine integral_mono_ae hint2 hint (Filter.Eventually.of_forall fun y => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (heatKernel_nonneg _ _ _)
    have hle : j1Functional a (heatKernel y r) p q w.grad ≤ J1Heat a y r p q := by
      unfold J1Heat
      rw [J1_eq_sSup_j1Functional]
      refine le_csSup ⟨M, ?_⟩ ⟨w, rfl⟩
      rintro e ⟨w', rfl⟩
      exact j1Functional_le a (heatKernel_nonneg y r) (integrable_heatKernel y hr)
        (integral_heatKernel y hr).le p q w'.grad
    exact hle
  · rw [integral_undef hI]
    exact hnonneg

end QSH
