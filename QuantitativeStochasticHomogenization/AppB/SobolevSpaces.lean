import QuantitativeStochasticHomogenization.Front.Notation
import PDEFoundation.Sobolev.W1p.ZeroBoundary

/-!
# The Sobolev spaces `W^{1,p}(U)` and `W^{1,p}_0(U)`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix B, Definition B.2 for `k = 1`.

* `IsW1p U p u g`: `u ∈ W^{1,p}(U)` with weak gradient `g`: `u` and `g` are in `L^p(U)` and
  `∇u = g` weakly in `U`;
* `w1pNorm U p u g`: the norm (B.1) for `k = 1`, `‖u‖_{L^p(U)} + ∑_i ‖∂_{x_i} u‖_{L^p(U)}`, with
  values in `[0, ∞]`;
* `IsW01p U p u g`: `u ∈ W^{1,p}_0(U)`, the closure of `C^∞_c(U)` for the norm (B.1).

The bridges `IsW1p.toW1pFunction` and `IsW01p.hasSupportedSmoothApproximation` identify these
with the `W^{1,p}` functions and the zero-boundary class of the elliptic regularity library.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- `u ∈ W^{1,p}(U)` with weak gradient `g` (Definition B.2, `k = 1`). -/
def IsW1p (U : Set (Vec d)) (p : ℝ≥0∞) (u : Vec d → ℝ) (g : Vec d → Vec d) : Prop :=
  MemLp u p (volume.restrict U) ∧ MemLp g p (volume.restrict U) ∧ HasWeakGradient U u g

/-- The norm (B.1) of `W^{1,p}(U)`: `‖u‖_{L^p(U)} + ∑_i ‖g_i‖_{L^p(U)}`. -/
def w1pNorm (U : Set (Vec d)) (p : ℝ≥0∞) (u : Vec d → ℝ) (g : Vec d → Vec d) : ℝ≥0∞ :=
  eLpNorm u p (volume.restrict U) + ∑ i : Fin d, eLpNorm (fun x => g x i) p (volume.restrict U)

/-- `u ∈ W^{1,p}_0(U)` with weak gradient `g` (Definition B.2, `k = 1`): the closure of
`C^∞_c(U)` with respect to the norm (B.1). -/
def IsW01p (U : Set (Vec d)) (p : ℝ≥0∞) (u : Vec d → ℝ) (g : Vec d → Vec d) : Prop :=
  IsW1p U p u g ∧ ∃ φ : ℕ → Vec d → ℝ, (∀ n, IsSpatialTest U (φ n)) ∧
    Tendsto (fun n => w1pNorm U p (fun x => φ n x - u x) (fun x => gradient (φ n) x - g x))
      atTop (𝓝 0)

/-- A weak gradient in `U` is a weak gradient in every subset of `U`. -/
theorem HasWeakGradient.mono {U V : Set (Vec d)} (hVU : V ⊆ U) {u : Vec d → ℝ}
    {g : Vec d → Vec d} (hu : HasWeakGradient U u g) : HasWeakGradient V u g := by
  refine fun i => ⟨(hu i).1.mono_set hVU, (hu i).2.1.mono_set hVU, fun φ hφ => ?_⟩
  have hφU : IsSpatialTest U φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans hVU⟩
  have h := (hu i).2.2 φ hφU
  have hd0 : ∀ x, x ∉ tsupport φ → coordinateDerivative i φ x = 0 := fun x hx => by
    simp [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hx]
  have hφ0 : ∀ x, x ∉ tsupport φ → φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have e1 : ∫ x in V, u x * coordinateDerivative i φ x = ∫ x in U, u x * coordinateDerivative i φ x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [hd0 x fun h => hx (hφ.2.2 h), mul_zero],
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [hd0 x fun h => hx (hVU (hφ.2.2 h)), mul_zero]]
  have e2 : ∫ x in V, g x i * φ x = ∫ x in U, g x i * φ x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [hφ0 x fun h => hx (hφ.2.2 h), mul_zero],
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [hφ0 x fun h => hx (hVU (hφ.2.2 h)), mul_zero]]
  rw [e1, e2]
  exact h

/-- `W^{1,p}(U)` restricts to `W^{1,p}(V)` for `V ⊆ U`. -/
theorem IsW1p.mono {U V : Set (Vec d)} (hVU : V ⊆ U) {p : ℝ≥0∞} {u : Vec d → ℝ}
    {g : Vec d → Vec d} (hu : IsW1p U p u g) : IsW1p V p u g :=
  ⟨hu.1.mono_measure (Measure.restrict_mono hVU le_rfl),
    hu.2.1.mono_measure (Measure.restrict_mono hVU le_rfl), hu.2.2.mono hVU⟩

/-- The `W^{1,p}(U)` function of the elliptic regularity library with value `u` and weak
gradient `g`. -/
def IsW1p.toW1pFunction {U : Set (Vec d)} {p : ℝ≥0∞} {u : Vec d → ℝ} {g : Vec d → Vec d}
    (h : IsW1p U p u g) : PDE.W1pFunction U p where
  toFun := u
  grad := g
  memLp := h.1
  gradMemLp := fun i => h.2.1.eval i
  hasWeakGradient := fun i φ h1 h2 h3 => (h.2.2 i).2.2 φ ⟨h1, h2, h3⟩

@[simp]
theorem IsW1p.toW1pFunction_toFun {U : Set (Vec d)} {p : ℝ≥0∞} {u : Vec d → ℝ}
    {g : Vec d → Vec d} (h : IsW1p U p u g) : h.toW1pFunction.toFun = u := rfl

@[simp]
theorem IsW1p.toW1pFunction_grad {U : Set (Vec d)} {p : ℝ≥0∞} {u : Vec d → ℝ}
    {g : Vec d → Vec d} (h : IsW1p U p u g) : h.toW1pFunction.grad = g := rfl

/-- The summand `‖u‖_{L^p(U)}` of the norm (B.1). -/
theorem eLpNorm_le_w1pNorm (U : Set (Vec d)) (p : ℝ≥0∞) (u : Vec d → ℝ) (g : Vec d → Vec d) :
    eLpNorm u p (volume.restrict U) ≤ w1pNorm U p u g :=
  le_self_add

/-- The summand `‖g_i‖_{L^p(U)}` of the norm (B.1). -/
theorem eLpNorm_apply_le_w1pNorm (U : Set (Vec d)) (p : ℝ≥0∞) (u : Vec d → ℝ)
    (g : Vec d → Vec d) (i : Fin d) :
    eLpNorm (fun x => g x i) p (volume.restrict U) ≤ w1pNorm U p u g :=
  le_trans (Finset.single_le_sum (f := fun j => eLpNorm (fun x => g x j) p (volume.restrict U))
    (fun _ _ => zero_le) (Finset.mem_univ i)) le_add_self

/-- Functions of `W^{1,p}_0(U)` are limits of test functions in the sense of the elliptic
regularity library. -/
theorem IsW01p.hasSupportedSmoothApproximation {U : Set (Vec d)} {p : ℝ≥0∞} {u : Vec d → ℝ}
    {g : Vec d → Vec d} (h : IsW01p U p u g) :
    h.1.toW1pFunction.HasSupportedSmoothApproximation := by
  obtain ⟨φ, hφ, hlim⟩ := h.2
  refine ⟨{ approx := φ
            approx_smooth := fun n => (hφ n).1
            approx_hasCompactSupport := fun n => (hφ n).2.1
            approx_tsupport_subset := fun n => (hφ n).2.2
            tendsto_value := ?_
            tendsto_grad := ?_ }⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) (fun n => eLpNorm_le_w1pNorm U p (fun x => φ n x - u x)
        (fun x => gradient (φ n) x - g x))
  · intro i
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) (fun n => eLpNorm_apply_le_w1pNorm U p (fun x => φ n x - u x)
        (fun x => gradient (φ n) x - g x) i)

end QSH
