import QuantitativeStochasticHomogenization.Ch01.Sec04.Proposition115
import QuantitativeStochasticHomogenization.Ch04.Sec04.AffineHighContrastTransport

/-!
# The rescaled finite-volume correctors

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.5, (1.55)–(1.56): for `ε > 0` and the minimizer `v(·, □_m, e) = ℓ_e + φ` of (1.8), with
`φ = φ_{m,e}` the finite-volume corrector (1.55) of gradient `Dφ`, the function
`x ↦ e·x + ε φ(x/ε)` solves `-∇·(a(·/ε)∇·) = 0` on `ε □_m`. On every set `V` mapped into `□_m` by
`x ↦ x/ε`, `ε φ(·/ε) ∈ H¹(V)` with gradient `Dφ(·/ε)` (`h1_rescaledCorrector`) and the flux
`a(·/ε)(e + Dφ(·/ε))` is weakly divergence free (`hasWeakDivergence_rescaledCorrector`). The
triadic scale `m(ε)` of (1.56) satisfies `3^{-m} ≤ ε < 3^{1-m}` (`triadicScale`), so that
`□_0 ⊆ ε □_m`.
-/

open MeasureTheory Filter Set

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- The triadic scale `m(ε) = ⌈|log ε| / log 3⌉` of (1.56). -/
def triadicScale (ε : ℝ) : ℕ := ⌈Real.logb 3 ε⁻¹⌉₊

namespace TwoScale

theorem three_pow_triadicScale_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((3 : ℝ) ^ triadicScale ε)⁻¹ ≤ ε ∧ ε < 3 * ((3 : ℝ) ^ triadicScale ε)⁻¹ := by
  have hl : 0 ≤ Real.logb 3 ε⁻¹ := Real.logb_nonneg (by norm_num) (one_le_inv_iff₀.2 ⟨hε, hε1⟩)
  set m := triadicScale ε with hm
  have h1 : Real.logb 3 ε⁻¹ ≤ m := Nat.le_ceil _
  have h2 : (m : ℝ) - 1 < Real.logb 3 ε⁻¹ := by
    have := Nat.ceil_lt_add_one hl
    rw [hm, triadicScale]
    linarith
  have h3 : (0 : ℝ) < 3 := by norm_num
  have h31 : (1 : ℝ) < 3 := by norm_num
  have hε' : 0 < ε⁻¹ := inv_pos.2 hε
  constructor
  · have : ε⁻¹ ≤ (3 : ℝ) ^ m := by
      rw [← Real.rpow_natCast, ← Real.logb_le_logb h31 hε' (by positivity), Real.logb_rpow h3
        (by norm_num)]
      exact h1
    rw [inv_le_comm₀ (by positivity) hε]
    exact this
  · have : (3 : ℝ) ^ ((m : ℝ) - 1) < ε⁻¹ := by
      rw [← Real.logb_lt_logb_iff h31 (by positivity) hε', Real.logb_rpow h3 (by norm_num)]
      exact h2
    rw [Real.rpow_sub h3, Real.rpow_natCast, Real.rpow_one] at this
    rw [lt_inv_comm₀ (by positivity) hε] at this
    calc ε < ((3 : ℝ) ^ m / 3)⁻¹ := this
      _ = 3 * ((3 : ℝ) ^ m)⁻¹ := by rw [inv_div]; ring

/-- `x ↦ x / ε` maps `□_0` into `□_m` when `3^{-m} ≤ ε`. -/
theorem inv_smul_mem_triadicCube {ε : ℝ} (hε : 0 < ε) {m : ℕ} (hm : ((3 : ℝ) ^ m)⁻¹ ≤ ε)
    {x : Vec d} (hx : x ∈ triadicCube d 0) : ε⁻¹ • x ∈ triadicCube d m := by
  simp only [triadicCube, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo, pow_zero] at hx ⊢
  intro i
  have h3 : (0 : ℝ) < 3 ^ m := by positivity
  have hinv : ε⁻¹ ≤ 3 ^ m := by
    rw [inv_le_comm₀ hε h3]
    exact hm
  obtain ⟨h1, h2⟩ := hx i
  simp only [Pi.smul_apply, smul_eq_mul]
  have hεi : 0 < ε⁻¹ := inv_pos.2 hε
  constructor
  · nlinarith
  · nlinarith

/-- **Weak divergence under `x ↦ c x + y`.** -/
theorem hasWeakDivergence_comp_smul_add {U V : Set (Vec d)} {F : Vec d → Vec d} {c : ℝ}
    (hc : 0 < c) (y : Vec d) (hV : ∀ x ∈ V, c • x + y ∈ U)
    (h : HasWeakDivergence U F (fun _ => 0))
    (hF : ∀ i, LocallyIntegrableOn (fun x => F (c • x + y) i) V volume) :
    HasWeakDivergence V (fun x => F (c • x + y)) (fun _ => 0) := by
  refine ⟨hF, locallyIntegrableOn_zero, fun φ hφl => ?_⟩
  obtain ⟨hφ, hcs, hsupp⟩ := hφl
  have hc0 : c ≠ 0 := hc.ne'
  set ψ : Vec d → ℝ := fun x' => φ (c⁻¹ • (x' - y)) with hψdef
  have hψ : IsSpatialTest U ψ := isSpatialTest_comp_affineInv hc0 y hV hφ hcs hsupp
  have hdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hgrad : ∀ x', gradient ψ x' = c⁻¹ • gradient φ (c⁻¹ • (x' - y)) := fun x' => by
    funext i
    simp only [gradient, Pi.smul_apply, smul_eq_mul]
    exact fderiv_comp_affineInv_apply hdiff c y x' _
  have hmain := h.2.2 ψ hψ
  simp only [zero_mul, integral_zero, neg_zero] at hmain ⊢
  have hzero : ∀ x, x ∉ tsupport ψ → dot (F x) (gradient ψ x) = 0 := fun x hx => by
    unfold dot gradient
    exact Finset.sum_eq_zero fun k _ => by
      rw [coordinateDerivative_eq_zero_of_notMem_tsupport hx k, mul_zero]
  rw [setIntegral_eq_integral_of_tsupport hψ.2.2 hzero] at hmain
  have hzero' : ∀ x, x ∉ tsupport φ → dot (F (c • x + y)) (gradient φ x) = 0 := fun x hx => by
    unfold dot gradient
    exact Finset.sum_eq_zero fun k _ => by
      rw [coordinateDerivative_eq_zero_of_notMem_tsupport hx k, mul_zero]
  rw [setIntegral_eq_integral_of_tsupport hsupp hzero']
  have e : ∫ x, dot (F (c • x + y)) (gradient φ x) =
      |c ^ d|⁻¹ * (c * ∫ x', dot (F x') (gradient ψ x')) := by
    rw [← integral_const_mul, ← integral_comp_smul_add _ c y]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hgrad, inv_smul_smul_add_sub hc0]
    unfold dot
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  rw [e, hmain, mul_zero, mul_zero]

/-- **The rescaled corrector is in `H¹`**: if `(φ, Dφ) ∈ H¹₀(□_m)` and `x ↦ x/ε` maps the
measurable set `V` of finite measure into `□_m`, then `ε φ(·/ε) ∈ H¹(V)` with gradient `Dφ(·/ε)`. -/
theorem h1_rescaledCorrector {m : ℕ} {φ : Vec d → ℝ} {Dφ : Vec d → Vec d}
    (hφ : H01 (triadicCube d m) φ Dφ) {ε : ℝ} (hε : 0 < ε) {V : Set (Vec d)}
    (hVm : MeasurableSet V) (hVt : volume V ≠ ⊤) (hV : ∀ x ∈ V, ε⁻¹ • x ∈ triadicCube d m) :
    MemLp (fun x => ε * φ (ε⁻¹ • x)) 2 (volume.restrict V) ∧
      (∀ i, MemLp (fun x => Dφ (ε⁻¹ • x) i) 2 (volume.restrict V)) ∧
      HasWeakGradient V (fun x => ε * φ (ε⁻¹ • x)) (fun x => Dφ (ε⁻¹ • x)) := by
  have hεi : ε⁻¹ ≠ 0 := inv_ne_zero hε.ne'
  have hV' : ∀ x ∈ V, ε⁻¹ • x + 0 ∈ triadicCube d m := fun x hx => by
    rw [add_zero]; exact hV x hx
  have hmeas : MeasurableSet (triadicCube d m) := (isOpen_triadicCube m).measurableSet
  have h1 : MemLp (fun x => φ (ε⁻¹ • x + 0)) 2 (volume.restrict V) :=
    MemLp.comp_smul_add_restrict hmeas hVm hεi 0 hV' hφ.1
  have h2 : ∀ i, MemLp (fun x => Dφ (ε⁻¹ • x + 0) i) 2 (volume.restrict V) := fun i =>
    MemLp.comp_smul_add_restrict (f := fun x => Dφ x i) hmeas hVm hεi 0 hV' (hφ.2.1.eval i)
  simp only [add_zero] at h1 h2
  have hw := hasWeakGradientOn_comp_smul_add (inv_pos.2 hε) 0 hV' hφ.2.2.1
  simp only [add_zero, inv_inv] at hw
  have := isFiniteMeasure_restrict.mpr hVt
  exact ⟨h1.const_mul ε, h2, hasWeakGradient_of_hasWeakGradientOn' hw
    (IntegrableOn.locallyIntegrableOn ((h1.const_mul ε).integrable one_le_two))
    fun i => IntegrableOn.locallyIntegrableOn ((h2 i).integrable one_le_two)⟩

/-- **The rescaled flux is weakly divergence free**: if `(φ, Dφ)` is the minimizer of (1.8) on
`□_m` for the slope `e` and `x ↦ x/ε` maps `V` into `□_m`, then `a(·/ε)(e + Dφ(·/ε))` is weakly
divergence free in `V`. -/
theorem hasWeakDivergence_rescaledCorrector {a : CoefficientField d Λ} {m : ℕ} {e : Vec d}
    {φ : Vec d → ℝ} {Dφ : Vec d → Vec d}
    (hmin : IsDirichletMinimizer a (triadicCube d m) e φ Dφ) {ε : ℝ} (hε : 0 < ε)
    {V : Set (Vec d)} (hVm : MeasurableSet V) (hVt : volume V ≠ ⊤)
    (hV : ∀ x ∈ V, ε⁻¹ • x ∈ triadicCube d m) :
    HasWeakDivergence V (fun x => (a (ε⁻¹ • x)).mulVec (e + Dφ (ε⁻¹ • x))) (fun _ => 0) := by
  have hεi : ε⁻¹ ≠ 0 := inv_ne_zero hε.ne'
  have hV' : ∀ x ∈ V, ε⁻¹ • x + 0 ∈ triadicCube d m := fun x hx => by
    rw [add_zero]; exact hV x hx
  have hmeas : MeasurableSet (triadicCube d m) := (isOpen_triadicCube m).measurableSet
  have hsol := hmin.isL2Sol (volume_triadicCube_ne_top d m)
  have hF : ∀ i, MemLp (fun x => (a (ε⁻¹ • x + 0)).mulVec (e + Dφ (ε⁻¹ • x + 0)) i) 2
      (volume.restrict V) := fun i =>
    MemLp.comp_smul_add_restrict (f := fun x => (a x).mulVec (e + Dφ x) i) hmeas hVm hεi 0 hV'
      (hsol.1.eval i)
  have := isFiniteMeasure_restrict.mpr hVt
  have h := hasWeakDivergence_comp_smul_add (inv_pos.2 hε) 0 hV' hsol.2 fun i =>
    IntegrableOn.locallyIntegrableOn ((hF i).integrable one_le_two)
  simpa only [add_zero] using h

end TwoScale

end QSH
