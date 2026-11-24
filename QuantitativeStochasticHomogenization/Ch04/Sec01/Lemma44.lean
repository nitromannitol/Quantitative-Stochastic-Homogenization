import QuantitativeStochasticHomogenization.Ch04.Sec01.J1HeatFormula
import QuantitativeStochasticHomogenization.Ch04.Sec01.J1HeatSharpBound
import QuantitativeStochasticHomogenization.Ch04.Sec01.EnergyQuantityBounds
import QuantitativeStochasticHomogenization.Ch04.Sec01.Proposition43
import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicApproximationProof

/-!
# Lemma 4.4: basic properties of `J₁` at the heat kernel masks

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.1, Lemma 4.4, for the masks `Ψ = Φ_{z,r}` used in Chapter 4: almost surely, for every
center `z`, radius `r > 0` and loads `p, q`, `J₁(Φ_{z,r}, p, q)` has a maximizer `v` in `A₁`
(`exists_isJ1Maximizer`), characterized by the first variation (4.13)
(`isJ1Maximizer_iff_firstVariation`), with `J₁ = ⨍ ½ ∇v·a∇v` (4.14), the second variation (4.19),
the bounds (4.15), the polarization (4.16) and the derivatives (4.20)–(4.21) (`lemma_4_4`).

The book obtains the maximizer from `∇A₁` being a `d`-dimensional subspace of `L²(Ψ)` (Theorem 3.8).
Here, almost surely, `A₁` is the set of corrected affine functions `ℓ_c + φ_c` (the first-order
Liouville theorem, `firstOrderLiouville`) and the objective at slope `c` is `b·c - ½ c·Mc` with the
Gram matrix `M_{ij} = ∫ Φ Wᵢ·a Wⱼ` and the load `bᵢ = ∫ Φ (-p·a Wᵢ + q·Wᵢ)`, `Wᵢ = eᵢ + ∇φ_{eᵢ}`
(`J1Objective_eq_quadratic`); `M` is invertible for the heat kernel masks
(`ae_J1Heat_eq_half_dot_inv`), and the maximizer has slope `M⁻¹ b`.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- The properties of a coefficient field used in this file, which hold almost surely: the
elements of `A₁` are the corrected affine functions, which belong to `A₁`, the corrector columns
have finite energy against the heat kernels, and the Gram matrices of the heat kernel masks are
invertible. -/
structure HeatJ1Structure {P : Measure (CoefficientField d Λ)} (S : HomogenizationData P)
    (a : CoefficientField d Λ) : Prop where
  liouville : ∀ w : HarmonicA1 a, ∃ c : Vec d,
    ∀ᵐ x ∂(volume : Measure (Vec d)), w.grad x = correctedAffineGrad S a c x
  exists_affine : ∀ c : Vec d, ∃ w : HarmonicA1 a, w.grad = correctedAffineGrad S a c
  energy : ∀ (i : Fin d) (z : Vec d) (r : ℝ), 0 < r →
    Integrable (fun x => heatKernel z r x * euclideanSq (correctorColumn S a i x))
  gram_unit : ∀ (z : Vec d) (r : ℝ), 0 < r → IsUnit (J1Gram S a (heatKernel z r))

theorem ae_heatJ1Structure (hd : 2 ≤ d) (hΛ : 1 < Λ) {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (S : HomogenizationData P) : ∀ᵐ a ∂P, HeatJ1Structure S a := by
  filter_upwards [firstOrderLiouville d hd Λ hΛ P hP S, ae_exists_harmonicA1_correctedAffine S,
    ae_integrable_heatKernel_mul_euclideanSq_correctorColumn hd hΛ hP S,
    ae_J1Heat_eq_half_dot_inv firstOrderLiouville hd hΛ hP S] with a hL hex hW hJ
  refine ⟨fun w => ?_, fun c => ?_, hW, fun z r hr => (hJ z r hr 0 0).1⟩
  · obtain ⟨-, c, -, hc⟩ := hL w
    exact ⟨c, hc⟩
  · obtain ⟨w, -, hw⟩ := hex c
    exact ⟨w, hw⟩

section Structure

variable {P : Measure (CoefficientField d Λ)} {S : HomogenizationData P} {a : CoefficientField d Λ}

/-- `v` is a maximizer of `J₁(Ψ, p, q)`: the objective of (4.8) at `∇v` is `J₁(Ψ, p, q)`. -/
def IsJ1Maximizer (a : CoefficientField d Λ) (mask : Vec d → ℝ) (p q : Vec d) (v : HarmonicA1 a) :
    Prop :=
  j1Functional a mask p q v.grad = J1 a mask p q

theorem HeatJ1Structure.integrable_gram_load (hS : HeatJ1Structure S a) (z : Vec d) {r : ℝ}
    (hr : 0 < r) (p q : Vec d) :
    (∀ i j, Integrable (fun x => heatKernel z r x *
      dot (correctorColumn S a i x) ((a x).mulVec (correctorColumn S a j x)))) ∧
    (∀ i, Integrable (fun x => heatKernel z r x *
      (-dot p ((a x).mulVec (correctorColumn S a i x)) + dot q (correctorColumn S a i x)))) :=
  integrable_heatKernel_gram_load S a z hr (fun i => hS.energy i z r hr) p q

/-- The objective at an element of `A₁` of slope `c` is `b·c - ½ c·Mc`. -/
theorem HeatJ1Structure.j1Functional_eq (hS : HeatJ1Structure S a) (z : Vec d) {r : ℝ}
    (hr : 0 < r) (p q : Vec d) {w : HarmonicA1 a} {c : Vec d}
    (hc : ∀ᵐ x ∂(volume : Measure (Vec d)), w.grad x = correctedAffineGrad S a c x) :
    j1Functional a (heatKernel z r) p q w.grad =
      dot (J1Load S a (heatKernel z r) p q) c -
        (1 / 2 : ℝ) * dot c ((J1Gram S a (heatKernel z r)).mulVec c) := by
  obtain ⟨hM, hb⟩ := hS.integrable_gram_load z hr p q
  rw [j1Functional_congr_ae a _ p q hc, ← J1Objective_eq_quadratic S a _ p q hM hb c]
  rfl

/-- `J₁(Φ_{z,r}, p, q)` is the supremum of the slope quadratic. -/
theorem HeatJ1Structure.J1_eq_sSup (hS : HeatJ1Structure S a) (z : Vec d) {r : ℝ} (hr : 0 < r)
    (p q : Vec d) :
    J1 a (heatKernel z r) p q = sSup (Set.range fun c : Vec d =>
      dot (J1Load S a (heatKernel z r) p q) c -
        (1 / 2 : ℝ) * dot c ((J1Gram S a (heatKernel z r)).mulVec c)) := by
  rw [J1_eq_sSup_j1Functional]
  congr 1
  ext e
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨c, hc⟩ := hS.liouville w
    exact ⟨c, (hS.j1Functional_eq z hr p q hc).symm⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨w, hw⟩ := hS.exists_affine c
    exact ⟨w, (hS.j1Functional_eq z hr p q (Eventually.of_forall fun x => by rw [hw])).symm⟩

end Structure

end QSH
