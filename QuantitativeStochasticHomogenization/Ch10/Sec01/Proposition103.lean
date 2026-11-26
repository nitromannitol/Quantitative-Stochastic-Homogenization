import QuantitativeStochasticHomogenization.Ch10.Sec01.GeneralCoefficients
import QuantitativeStochasticHomogenization.Ch01.Sec02SubadditiveQuantity
import QuantitativeStochasticHomogenization.Ch01.Sec02.DirichletEnergyBounds
import QuantitativeStochasticHomogenization.Ch01.Sec04.HatNegativeSobolev

/-!
# Proposition 10.3: the variational formulation of a nonsymmetric equation

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Chapter 10, Section 10.1. For `a` in the set `Ω` of (10.2), `u ∈ H¹(U)` with gradient `G` and a
right-hand side `u*`, the function `u` solves `-∇·(a∇u) = u*` if and only if
`0 = inf {∫_U (A(∇u, g, ·) - g·∇u) : g ∈ L²(U; ℝ^d), -∇·g = u*}` (10.12), and then the infimum
is attained at `g = a∇u`. Here `A` is the quadratic form (10.7) (`linearRepresentative`).

The right-hand side `u*` is given by its values `u*(φ)` on `H¹₀(U)` (pairs `(φ, ∇φ)`), and
`-∇·g = u*` means `∫_U ∇φ·g = u*(φ)` for every `φ ∈ H¹₀(U)`. No linearity or continuity of `u*`
is used, so `u*` may be any map; the set in (10.12) is then nonempty exactly when `u*` is of the
form `-∇·g` with `g ∈ L²`, which holds for every `u* ∈ H⁻¹(U)` on a bounded domain.
`proposition_10_3` states the equivalence with this nonemptiness as part of the right-hand side;
`proposition_10_3_of_nonempty` is the printed form, for `u*` in the range of `-∇·` on `L²(U)`.

The proof is the printed one, (10.10)–(10.11), with the direct method replaced by a minimizing
sequence: the integrand equals `½ (a∇u - g)·s⁻¹(a∇u - g) ≥ (2 max(Λ,1))⁻¹ |a∇u - g|²`, so a
minimizing sequence `g_n` converges to `a∇u` in `L²(U)` and the equation passes to the limit.
-/

open MeasureTheory Matrix Filter
open scoped Topology

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- `-∇·g = u*` in `U`, for `u*` given by its values on `H¹₀(U)`: `∫_U ∇φ·g = u*(φ, ∇φ)` for every
`φ ∈ H¹₀(U)` with gradient `∇φ`. -/
def IsNegDivergenceOn (U : Set (Vec d)) (g : Vec d → Vec d)
    (ustar : (Vec d → ℝ) → (Vec d → Vec d) → ℝ) : Prop :=
  ∀ φ Φ, H01 U φ Φ → ∫ x in U, dot (Φ x) (g x) = ustar φ Φ

theorem aestronglyMeasurable_mulVec_of_entries {μ : Measure (Vec d)} {M : Vec d → Mat d}
    {v : Vec d → Vec d} (hM : ∀ i j, AEStronglyMeasurable (fun x => M x i j) μ)
    (hv : AEStronglyMeasurable v μ) :
    AEStronglyMeasurable (fun x => (M x).mulVec (v x)) μ := by
  have hco : ∀ j, AEStronglyMeasurable (fun x => v x j) μ := fun j =>
    (aemeasurable_pi_iff.1 hv.aemeasurable j).aestronglyMeasurable
  refine (aemeasurable_pi_iff.2 fun i => ?_).aestronglyMeasurable
  have e : (fun x => (M x).mulVec (v x) i) = fun x => ∑ j, M x i j * v x j := by
    funext x
    simp [Matrix.mulVec, dotProduct]
  rw [e]
  exact (Finset.aestronglyMeasurable_fun_sum Finset.univ fun j _ =>
    (hM i j).mul (hco j)).aemeasurable

theorem aestronglyMeasurable_dot_of {μ : Measure (Vec d)} {v w : Vec d → Vec d}
    (hv : AEStronglyMeasurable v μ) (hw : AEStronglyMeasurable w μ) :
    AEStronglyMeasurable (fun x => dot (v x) (w x)) μ := by
  have hvc : ∀ j, AEStronglyMeasurable (fun x => v x j) μ := fun j =>
    (aemeasurable_pi_iff.1 hv.aemeasurable j).aestronglyMeasurable
  have hwc : ∀ j, AEStronglyMeasurable (fun x => w x j) μ := fun j =>
    (aemeasurable_pi_iff.1 hw.aemeasurable j).aestronglyMeasurable
  have e : (fun x => dot (v x) (w x)) = fun x => ∑ j, v x j * w x j := by
    funext x
    rfl
  rw [e]
  exact Finset.aestronglyMeasurable_fun_sum Finset.univ fun j _ => (hvc j).mul (hwc j)

namespace GeneralCoefficientField

variable (a : GeneralCoefficientField d Λ)

/-- The symmetric part of `a(x)` is positive definite. -/
theorem pos_dot_mulVec (x ξ : Vec d) (hξ : ξ ≠ 0) : 0 < dot ξ ((a x).mulVec ξ) :=
  lt_of_lt_of_le (euclideanSq_pos_of_ne_zero hξ) (a.elliptic x ξ).1

/-- The integrand of (10.12): `A(p, q, x) - q·p = ½ (a(x)p - q)·s(x)⁻¹(a(x)p - q)`. -/
theorem linearRepresentative_sub_dot_eq (x p q : Vec d) :
    linearRepresentative (a x) p q - dot q p =
      (1 / 2) * dot ((a x).mulVec p - q) ((symmetricPart (a x))⁻¹.mulVec ((a x).mulVec p - q)) := by
  rw [show dot q p = dot p q from dotProduct_comm _ _]
  exact linearRepresentative_sub_dot (a.pos_dot_mulVec x) p q

theorem linearRepresentative_sub_dot_nonneg (x p q : Vec d) :
    0 ≤ linearRepresentative (a x) p q - dot q p := by
  rw [a.linearRepresentative_sub_dot_eq]
  have h := (a.dot_inv_symmetricPart_bounds x ((a x).mulVec p - q)).1
  have h0 : 0 ≤ (max Λ 1)⁻¹ * euclideanSq ((a x).mulVec p - q) :=
    mul_nonneg (inv_nonneg.2 (le_trans zero_le_one (le_max_right _ _))) (euclideanSq_nonneg _)
  linarith

/-- The coercivity of the integrand: `(2 max(Λ,1))⁻¹ |a p - q|² ≤ A(p, q, x) - q·p`. -/
theorem euclideanSq_le_linearRepresentative_sub_dot (x p q : Vec d) :
    (2 * max Λ 1)⁻¹ * euclideanSq ((a x).mulVec p - q) ≤ linearRepresentative (a x) p q - dot q p := by
  rw [a.linearRepresentative_sub_dot_eq]
  have h := (a.dot_inv_symmetricPart_bounds x ((a x).mulVec p - q)).1
  have hm : 0 < max Λ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have : (2 * max Λ 1)⁻¹ = (1 / 2) * (max Λ 1)⁻¹ := by
    rw [mul_inv]; ring
  rw [this, mul_assoc]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

theorem linearRepresentative_sub_dot_le (x p q : Vec d) :
    linearRepresentative (a x) p q - dot q p ≤ (1 / 2) * euclideanSq ((a x).mulVec p - q) := by
  rw [a.linearRepresentative_sub_dot_eq]
  have h := (a.dot_inv_symmetricPart_bounds x ((a x).mulVec p - q)).2
  linarith

/-- (10.11): the integrand vanishes at `q = a(x) p`. -/
theorem linearRepresentative_mulVec_sub_dot (x p : Vec d) :
    linearRepresentative (a x) p ((a x).mulVec p) - dot ((a x).mulVec p) p = 0 := by
  rw [a.linearRepresentative_sub_dot_eq, sub_self]
  simp [dot]

/-- The flux `a∇u` of a field `G ∈ L²(U)` is in `L²(U)`. -/
theorem memLp_mulVec {U : Set (Vec d)} {G : Vec d → Vec d} (hG : MemLp G 2 (volume.restrict U)) :
    MemLp (fun x => (a x).mulVec (G x)) 2 (volume.restrict U) := by
  have hac : volume.restrict U ≪ volume := Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  refine memLp_pi_iff.2 fun i => ?_
  have hmeas : AEStronglyMeasurable (fun x => (a x).mulVec (G x) i) (volume.restrict U) :=
    (aemeasurable_pi_iff.1 (aestronglyMeasurable_mulVec_of_entries
      (fun i j => a.aestronglyMeasurable_apply hac i j) hG.aestronglyMeasurable).aemeasurable
        i).aestronglyMeasurable
  have hg : MemLp (fun x => |Λ| * ∑ j, ‖G x j‖) 2 (volume.restrict U) :=
    (memLp_finsetSum Finset.univ fun j _ => (hG.eval j).norm).const_mul |Λ|
  refine hg.of_le hmeas (Eventually.of_forall fun x => ?_)
  have hn : 0 ≤ |Λ| * ∑ j, ‖G x j‖ :=
    mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun j _ => norm_nonneg _)
  rw [Real.norm_of_nonneg hn, Real.norm_eq_abs]
  have e1 := abs_coord_le_euclideanNorm ((a x).mulVec (G x)) i
  have e2 : euclideanNorm ((a x).mulVec (G x)) ≤ |Λ| * euclideanNorm (G x) :=
    (a.elliptic x (G x)).2.trans
      (mul_le_mul_of_nonneg_right (le_abs_self Λ) (euclideanNorm_nonneg _))
  have e3 := euclideanNorm_le_sum_abs_apply (G x)
  simp only [Real.norm_eq_abs]
  calc |(a x).mulVec (G x) i| ≤ euclideanNorm ((a x).mulVec (G x)) := e1
    _ ≤ |Λ| * euclideanNorm (G x) := e2
    _ ≤ |Λ| * ∑ j, |G x j| := mul_le_mul_of_nonneg_left e3 (abs_nonneg _)

/-- The integrand of (10.12) is integrable for `∇u, g ∈ L²(U)`. -/
theorem integrable_linearRepresentative_sub_dot {U : Set (Vec d)} {G g : Vec d → Vec d}
    (hG : MemLp G 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U)) :
    Integrable (fun x => linearRepresentative (a x) (G x) (g x) - dot (g x) (G x))
      (volume.restrict U) := by
  have hac : volume.restrict U ≪ volume := Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  have hh : MemLp (fun x => (a x).mulVec (G x) - g x) 2 (volume.restrict U) :=
    (a.memLp_mulVec hG).sub hg
  have hmeas : AEStronglyMeasurable (fun x => (1 / 2 : ℝ) * dot ((a x).mulVec (G x) - g x)
      ((symmetricPart (a x))⁻¹.mulVec ((a x).mulVec (G x) - g x))) (volume.restrict U) :=
    (aestronglyMeasurable_dot_of hh.aestronglyMeasurable
      (aestronglyMeasurable_mulVec_of_entries
        (fun i j => a.aestronglyMeasurable_inv_symmetricPart_apply hac i j)
        hh.aestronglyMeasurable)).const_mul _
  have hmeas' : AEStronglyMeasurable
      (fun x => linearRepresentative (a x) (G x) (g x) - dot (g x) (G x)) (volume.restrict U) :=
    hmeas.congr (Eventually.of_forall fun x => (a.linearRepresentative_sub_dot_eq x (G x) (g x)).symm)
  refine ((integrable_euclideanSq_of_memLp hh).const_mul (1 / 2 : ℝ)).mono' hmeas'
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (a.linearRepresentative_sub_dot_nonneg x (G x) (g x))]
  exact a.linearRepresentative_sub_dot_le x (G x) (g x)

/-- The functional of (10.12): `∫_U (A(∇u, g, ·) - g·∇u)`. -/
noncomputable def representativeDefect (U : Set (Vec d)) (G g : Vec d → Vec d) : ℝ :=
  ∫ x in U, (linearRepresentative (a x) (G x) (g x) - dot (g x) (G x))

/-- The set whose infimum is taken in (10.12): the values of `representativeDefect` over
`g ∈ L²(U; ℝ^d)` with `-∇·g = u*`. -/
def representativeDefectSet (U : Set (Vec d)) (G : Vec d → Vec d)
    (ustar : (Vec d → ℝ) → (Vec d → Vec d) → ℝ) : Set ℝ :=
  {E | ∃ g : Vec d → Vec d, MemLp g 2 (volume.restrict U) ∧ IsNegDivergenceOn U g ustar ∧
    E = a.representativeDefect U G g}

theorem representativeDefect_nonneg (U : Set (Vec d)) (G g : Vec d → Vec d) :
    0 ≤ a.representativeDefect U G g :=
  setIntegral_nonneg_of_ae_restrict
    (Eventually.of_forall fun x => a.linearRepresentative_sub_dot_nonneg x (G x) (g x))

theorem representativeDefect_flux (U : Set (Vec d)) (G : Vec d → Vec d) :
    a.representativeDefect U G (fun x => (a x).mulVec (G x)) = 0 := by
  unfold representativeDefect
  simp only [a.linearRepresentative_mulVec_sub_dot, integral_zero]

/-- The `L²` distance to the flux is controlled by the functional:
`‖a∇u - g‖²_{L²(U)} ≤ 2 max(Λ,1) ∫_U (A(∇u, g, ·) - g·∇u)`. -/
theorem integral_euclideanSq_le_representativeDefect {U : Set (Vec d)} {G g : Vec d → Vec d}
    (hG : MemLp G 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U)) :
    ∫ x in U, euclideanSq ((a x).mulVec (G x) - g x) ≤
      2 * max Λ 1 * a.representativeDefect U G g := by
  have hm : 0 < max Λ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hh : MemLp (fun x => (a x).mulVec (G x) - g x) 2 (volume.restrict U) :=
    (a.memLp_mulVec hG).sub hg
  have hint := a.integrable_linearRepresentative_sub_dot hG hg
  have hpt : ∀ x, euclideanSq ((a x).mulVec (G x) - g x) ≤
      2 * max Λ 1 * (linearRepresentative (a x) (G x) (g x) - dot (g x) (G x)) := by
    intro x
    have h := a.euclideanSq_le_linearRepresentative_sub_dot x (G x) (g x)
    have h2 : 0 < 2 * max Λ 1 := by positivity
    rw [inv_mul_le_iff₀ h2] at h
    exact h
  unfold representativeDefect
  rw [← integral_const_mul]
  exact integral_mono (integrable_euclideanSq_of_memLp hh) (hint.const_mul _) hpt

/-- A field `g` with `-∇·g = u*` which is close to the flux in `L²` gives the equation up to an
error: `|∫_U ∇φ·a∇u - u*(φ)| ≤ (t/2) ∫|∇φ|² + (2t)⁻¹ ‖a∇u - g‖²`. -/
theorem abs_setIntegral_dot_flux_sub_le {U : Set (Vec d)} {G g Φ : Vec d → Vec d}
    (hG : MemLp G 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U))
    (hΦ : MemLp Φ 2 (volume.restrict U)) {t : ℝ} (ht : 0 < t) :
    |(∫ x in U, dot (Φ x) ((a x).mulVec (G x))) - ∫ x in U, dot (Φ x) (g x)| ≤
      t / 2 * (∫ x in U, euclideanSq (Φ x)) +
        (2 * t)⁻¹ * ∫ x in U, euclideanSq ((a x).mulVec (G x) - g x) := by
  have hF := a.memLp_mulVec hG
  have hh : MemLp (fun x => (a x).mulVec (G x) - g x) 2 (volume.restrict U) := hF.sub hg
  have i1 : Integrable (fun x => dot (Φ x) ((a x).mulVec (G x))) (volume.restrict U) :=
    integrable_finsetSum _ fun i _ => (hΦ.eval i).integrable_mul (hF.eval i)
  have i2 : Integrable (fun x => dot (Φ x) (g x)) (volume.restrict U) :=
    integrable_finsetSum _ fun i _ => (hΦ.eval i).integrable_mul (hg.eval i)
  have i3 : Integrable (fun x => dot (Φ x) ((a x).mulVec (G x) - g x)) (volume.restrict U) :=
    integrable_finsetSum _ fun i _ => (hΦ.eval i).integrable_mul (hh.eval i)
  have hsub : (∫ x in U, dot (Φ x) ((a x).mulVec (G x))) - ∫ x in U, dot (Φ x) (g x) =
      ∫ x in U, dot (Φ x) ((a x).mulVec (G x) - g x) := by
    rw [← integral_sub i1 i2]
    congr 1
    funext x
    simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [hsub]
  have hyoung : ∀ x, |dot (Φ x) ((a x).mulVec (G x) - g x)| ≤
      t / 2 * euclideanSq (Φ x) + (2 * t)⁻¹ * euclideanSq ((a x).mulVec (G x) - g x) := by
    intro x
    set v := Φ x
    set w := (a x).mulVec (G x) - g x
    have hcs := dot_le_euclideanNorm_mul v w
    have hcs' := dot_le_euclideanNorm_mul (-v) w
    have hneg : dot (-v) w = -dot v w := by simp [dot]
    rw [hneg] at hcs'
    have hnv : euclideanNorm (-v) = euclideanNorm v := by
      simp [euclideanNorm, euclideanSq, dot]
    rw [hnv] at hcs'
    have hprod : euclideanNorm v * euclideanNorm w ≤ t / 2 * euclideanSq v + (2 * t)⁻¹ * euclideanSq w := by
      rw [← euclideanNorm_mul_self v, ← euclideanNorm_mul_self w]
      have hnv0 := euclideanNorm_nonneg v
      have hnw0 := euclideanNorm_nonneg w
      have key : 0 ≤ (t * euclideanNorm v - euclideanNorm w) ^ 2 := sq_nonneg _
      have h2t : 0 < 2 * t := by positivity
      rw [show t / 2 * (euclideanNorm v * euclideanNorm v) + (2 * t)⁻¹ * (euclideanNorm w * euclideanNorm w)
          = ((t * euclideanNorm v) ^ 2 + euclideanNorm w ^ 2) / (2 * t) by field_simp]
      rw [le_div_iff₀ h2t]
      nlinarith
    rw [abs_le]
    constructor <;> linarith
  calc |∫ x in U, dot (Φ x) ((a x).mulVec (G x) - g x)|
      ≤ ∫ x in U, |dot (Φ x) ((a x).mulVec (G x) - g x)| := abs_integral_le_integral_abs
    _ ≤ ∫ x in U, (t / 2 * euclideanSq (Φ x) +
          (2 * t)⁻¹ * euclideanSq ((a x).mulVec (G x) - g x)) :=
        integral_mono i3.abs
          (((integrable_euclideanSq_of_memLp hΦ).const_mul _).add
            ((integrable_euclideanSq_of_memLp hh).const_mul _)) hyoung
    _ = t / 2 * (∫ x in U, euclideanSq (Φ x)) +
          (2 * t)⁻¹ * ∫ x in U, euclideanSq ((a x).mulVec (G x) - g x) := by
        rw [integral_add ((integrable_euclideanSq_of_memLp hΦ).const_mul _)
          ((integrable_euclideanSq_of_memLp hh).const_mul _), integral_const_mul,
          integral_const_mul]

/-- **Proposition 10.3, attainment**: if `u` solves `-∇·(a∇u) = u*`, then `g = a∇u` is admissible
in (10.12), the functional vanishes there, and this value is the infimum. -/
theorem proposition_10_3_attained (U : Set (Vec d)) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : H1 U u G) (ustar : (Vec d → ℝ) → (Vec d → Vec d) → ℝ)
    (hsol : IsNegDivergenceOn U (fun x => (a x).mulVec (G x)) ustar) :
    (0 : ℝ) ∈ a.representativeDefectSet U G ustar ∧
      a.representativeDefect U G (fun x => (a x).mulVec (G x)) = 0 ∧
      sInf (a.representativeDefectSet U G ustar) = 0 := by
  have hmem : (0 : ℝ) ∈ a.representativeDefectSet U G ustar :=
    ⟨fun x => (a x).mulVec (G x), a.memLp_mulVec hu.2.1, hsol,
      (a.representativeDefect_flux U G).symm⟩
  refine ⟨hmem, a.representativeDefect_flux U G, ?_⟩
  refine le_antisymm (csInf_le ⟨0, ?_⟩ hmem) (le_csInf ⟨0, hmem⟩ ?_)
  · rintro E ⟨g, -, -, rfl⟩
    exact a.representativeDefect_nonneg U G g
  · rintro E ⟨g, -, -, rfl⟩
    exact a.representativeDefect_nonneg U G g

/-- **Proposition 10.3**: `u ∈ H¹(U)` solves `-∇·(a∇u) = u*` in `U` if and only if the set of
(10.12) is nonempty and its infimum is `0`. In this case the infimum is attained at `g = a∇u`
(`proposition_10_3_attained`). -/
theorem proposition_10_3 (U : Set (Vec d)) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : H1 U u G) (ustar : (Vec d → ℝ) → (Vec d → Vec d) → ℝ) :
    IsNegDivergenceOn U (fun x => (a x).mulVec (G x)) ustar ↔
      ((a.representativeDefectSet U G ustar).Nonempty ∧
        sInf (a.representativeDefectSet U G ustar) = 0) := by
  constructor
  · intro hsol
    obtain ⟨hmem, -, hinf⟩ := a.proposition_10_3_attained U hu ustar hsol
    exact ⟨⟨0, hmem⟩, hinf⟩
  · rintro ⟨hne, hinf⟩ φ Φ hφ
    show ∫ x in U, dot (Φ x) ((a x).mulVec (G x)) = ustar φ Φ
    have hG := hu.2.1
    have hΦ := hφ.2.1
    have hm : 0 < max Λ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hbdd : BddBelow (a.representativeDefectSet U G ustar) := by
      refine ⟨0, ?_⟩
      rintro E ⟨g, -, -, rfl⟩
      exact a.representativeDefect_nonneg U G g
    obtain ⟨K, hKdef⟩ : ∃ K, K = ∫ x in U, euclideanSq (Φ x) := ⟨_, rfl⟩
    have hK : 0 ≤ K := by
      rw [hKdef]
      exact setIntegral_nonneg_of_ae_restrict (Eventually.of_forall fun x => euclideanSq_nonneg _)
    -- for every `t > 0` the defect of the equation is at most `t (K/2 + max(Λ,1))`
    have hsmall : ∀ t : ℝ, 0 < t →
        |(∫ x in U, dot (Φ x) ((a x).mulVec (G x))) - ustar φ Φ| ≤ t * (K / 2 + max Λ 1) := by
      intro t ht
      have hlt : sInf (a.representativeDefectSet U G ustar) < t ^ 2 := by
        rw [hinf]; positivity
      obtain ⟨E, ⟨g, hg, hdiv, rfl⟩, hE⟩ := exists_lt_of_csInf_lt hne hlt
      have hdist := a.integral_euclideanSq_le_representativeDefect hG hg
      have herr := a.abs_setIntegral_dot_flux_sub_le hG hg hΦ ht
      rw [hdiv φ Φ hφ, ← hKdef] at herr
      have h2t : 0 < 2 * t := by positivity
      have hbound : (2 * t)⁻¹ * ∫ x in U, euclideanSq ((a x).mulVec (G x) - g x) ≤
          t * max Λ 1 := by
        have hdef := a.representativeDefect_nonneg U G g
        calc (2 * t)⁻¹ * ∫ x in U, euclideanSq ((a x).mulVec (G x) - g x)
            ≤ (2 * t)⁻¹ * (2 * max Λ 1 * a.representativeDefect U G g) :=
              mul_le_mul_of_nonneg_left hdist (inv_nonneg.2 h2t.le)
          _ ≤ (2 * t)⁻¹ * (2 * max Λ 1 * t ^ 2) := by
              apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 h2t.le)
              exact mul_le_mul_of_nonneg_left hE.le (by positivity)
          _ = t * max Λ 1 := by field_simp
      calc |(∫ x in U, dot (Φ x) ((a x).mulVec (G x))) - ustar φ Φ|
          ≤ t / 2 * K + (2 * t)⁻¹ * ∫ x in U, euclideanSq ((a x).mulVec (G x) - g x) := herr
        _ ≤ t / 2 * K + t * max Λ 1 := by linarith
        _ = t * (K / 2 + max Λ 1) := by ring
    have hC : 0 < K / 2 + max Λ 1 := by positivity
    have habs : |(∫ x in U, dot (Φ x) ((a x).mulVec (G x))) - ustar φ Φ| = 0 := by
      refine le_antisymm ?_ (abs_nonneg _)
      by_contra hpos
      have hpos := not_le.mp hpos
      have h := hsmall (|(∫ x in U, dot (Φ x) ((a x).mulVec (G x))) - ustar φ Φ| /
        (2 * (K / 2 + max Λ 1))) (by positivity)
      have : |(∫ x in U, dot (Φ x) ((a x).mulVec (G x))) - ustar φ Φ| / (2 * (K / 2 + max Λ 1)) *
          (K / 2 + max Λ 1) = |(∫ x in U, dot (Φ x) ((a x).mulVec (G x))) - ustar φ Φ| / 2 := by
        field_simp
      linarith
    linarith [abs_eq_zero.mp habs]

/-- **Proposition 10.3, as printed**: when the set of (10.12) is nonempty (that is, `u* = -∇·g₀`
for some `g₀ ∈ L²(U)`, as for every `u* ∈ H⁻¹(U)` on a bounded domain), `u ∈ H¹(U)` solves
`-∇·(a∇u) = u*` if and only if the infimum in (10.12) is `0`. -/
theorem proposition_10_3_of_nonempty (U : Set (Vec d)) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : H1 U u G) (ustar : (Vec d → ℝ) → (Vec d → Vec d) → ℝ)
    (hne : (a.representativeDefectSet U G ustar).Nonempty) :
    IsNegDivergenceOn U (fun x => (a x).mulVec (G x)) ustar ↔
      0 = sInf (a.representativeDefectSet U G ustar) := by
  rw [a.proposition_10_3 U hu ustar]
  exact ⟨fun h => h.2.symm, fun h => ⟨hne, h.symm⟩⟩

end GeneralCoefficientField

end QSH
