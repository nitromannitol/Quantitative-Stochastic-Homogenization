import QuantitativeStochasticHomogenization.Ch04.Sec01EnergyQuantityJ1

/-!
# Proposition 4.3: evaluation of `J₁` through the corrected coordinates

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.1, Proposition 4.3, (4.10)–(4.12).

The proof of Proposition 4.3 writes `J₁(Ψ, p, q)` as a supremum over the corrected coordinates
`ξ + ∇φ_ξ`, whose gradients are exactly the gradients of `A₁` ((4.12), from Theorem 3.8 and
Lemma 3.6), and compares the functional of (4.8) at `ξ + ∇φ_ξ` with the homogenized objective
`-½ ξ·āξ - p·āξ + q·ξ` by (4.11), a consequence of Proposition 3.21. This file proves the
deterministic part of that argument, for a fixed coefficient field and a fixed mask `Ψ`:

* `abs_J1_sub_homogenizedJ1_le`: if the gradients of `A₁` are the fields `G ξ` of a family, up to
  null sets, and the functional of (4.8) at `G ξ` is within `ε (|ξ|² + |ξ| (|p| + |q|))` of the
  homogenized objective for every `ξ` (the bound (4.11)) with `ε ≤ 1/5`, then
  `|J₁(Ψ, p, q) - (½ p·āp + ½ q·ā⁻¹q - p·q)| ≤ 7 ε (|p|² + |q|²)`, which is (4.10);
* `abs_j1Functional_sub_le_of_averages`: the bound (4.11) at one `ξ` from the bounds
  (3.101)–(3.103) on the `Ψ`-averages of the gradient, the flux and the energy density of `G ξ`.

The matrix `ā` enters only through its symmetry and the lower bound `|ξ|² ≤ ξ·āξ`.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-! ## Euclidean and matrix facts -/

namespace BaseExponent

theorem dot_eq_dotProduct (x y : Vec d) : dot x y = x ⬝ᵥ y := rfl

theorem euclideanSq_nonneg (x : Vec d) : 0 ≤ euclideanSq x := by
  unfold euclideanSq dot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

theorem euclideanNorm_nonneg (x : Vec d) : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _

theorem euclideanNorm_sq (x : Vec d) : euclideanNorm x ^ 2 = euclideanSq x :=
  Real.sq_sqrt (euclideanSq_nonneg x)

theorem dot_sq_le (x y : Vec d) : dot x y ^ 2 ≤ euclideanSq x * euclideanSq y :=
  calc dot x y ^ 2 = (∑ i, x i * y i) ^ 2 := rfl
    _ ≤ (∑ i, x i ^ 2) * ∑ i, y i ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = euclideanSq x * euclideanSq y := by simp only [euclideanSq, dot, sq]

theorem abs_dot_le (x y : Vec d) : |dot x y| ≤ euclideanNorm x * euclideanNorm y := by
  rw [euclideanNorm, euclideanNorm, ← Real.sqrt_mul (euclideanSq_nonneg x)]
  exact Real.abs_le_sqrt (dot_sq_le x y)

theorem dot_le (x y : Vec d) : dot x y ≤ euclideanNorm x * euclideanNorm y :=
  (le_abs_self _).trans (abs_dot_le x y)

theorem euclideanSq_add (x y : Vec d) :
    euclideanSq (x + y) = euclideanSq x + 2 * dot x y + euclideanSq y := by
  simp only [euclideanSq, dot, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem euclideanNorm_add_le (x y : Vec d) :
    euclideanNorm (x + y) ≤ euclideanNorm x + euclideanNorm y := by
  have hx := euclideanNorm_nonneg x
  have hy := euclideanNorm_nonneg y
  calc euclideanNorm (x + y) = Real.sqrt (euclideanSq (x + y)) := rfl
    _ ≤ Real.sqrt ((euclideanNorm x + euclideanNorm y) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [euclideanSq_add, add_sq, euclideanNorm_sq, euclideanNorm_sq]
        nlinarith [dot_le x y]
    _ = euclideanNorm x + euclideanNorm y := Real.sqrt_sq (add_nonneg hx hy)

theorem euclideanNorm_neg (x : Vec d) : euclideanNorm (-x) = euclideanNorm x := by
  simp only [euclideanNorm, euclideanSq, dot, Pi.neg_apply, neg_mul_neg]

theorem euclideanNorm_sub_le (x y : Vec d) :
    euclideanNorm (x - y) ≤ euclideanNorm x + euclideanNorm y := by
  simpa [sub_eq_add_neg, euclideanNorm_neg] using euclideanNorm_add_le x (-y)

theorem eq_zero_of_euclideanSq_le_zero {x : Vec d} (hx : euclideanSq x ≤ 0) : x = 0 := by
  have hsum : ∑ j, x j * x j = 0 := le_antisymm hx (euclideanSq_nonneg x)
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (x j))).mp hsum i
    (Finset.mem_univ i)
  simpa using mul_self_eq_zero.mp this

/-- A matrix with `|ξ|² ≤ ξ·Aξ` is invertible. -/
theorem isUnit_det_of_coercive {A : Mat d}
    (hA : ∀ ξ : Vec d, euclideanSq ξ ≤ dot ξ (A.mulVec ξ)) : IsUnit A.det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h1 := hA v
  rw [hv, dot_eq_dotProduct, dotProduct_zero] at h1
  exact hv0 (eq_zero_of_euclideanSq_le_zero h1)

theorem dot_mulVec_comm {A : Mat d} (hA : A.transpose = A) (x y : Vec d) :
    dot x (A.mulVec y) = dot y (A.mulVec x) := by
  rw [dot_eq_dotProduct, dot_eq_dotProduct, Matrix.dotProduct_mulVec, ← hA,
    Matrix.vecMul_transpose, hA, dotProduct_comm]

theorem mulVec_inv_mulVec {A : Mat d} (hA : IsUnit A.det) (q : Vec d) :
    A.mulVec (A⁻¹.mulVec q) = q := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA, Matrix.one_mulVec]

/-- `|A⁻¹ q| ≤ |q|` when `|ξ|² ≤ ξ·Aξ`. -/
theorem euclideanNorm_inv_mulVec_le {A : Mat d}
    (hA : ∀ ξ : Vec d, euclideanSq ξ ≤ dot ξ (A.mulVec ξ)) (q : Vec d) :
    euclideanNorm (A⁻¹.mulVec q) ≤ euclideanNorm q := by
  set y := A⁻¹.mulVec q
  have hy : A.mulVec y = q := mulVec_inv_mulVec (isUnit_det_of_coercive hA) q
  have h1 := hA y
  rw [hy, ← euclideanNorm_sq] at h1
  have h2 := dot_le y q
  have hy0 := euclideanNorm_nonneg y
  have hq0 := euclideanNorm_nonneg q
  nlinarith

end BaseExponent

open BaseExponent

/-! ## The functional of (4.8) and the homogenized energy -/

/-- The functional `∫ Ψ (-½ ∇w·a∇w - p·a∇w + q·∇w)` maximized in (4.8), at a gradient field `g`. -/
def j1Functional (a : CoefficientField d Λ) (mask : Vec d → ℝ) (p q : Vec d)
    (g : Vec d → Vec d) : ℝ :=
  ∫ x, mask x * (-(1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x)) -
    dot p ((a x).mulVec (g x)) + dot q (g x))

theorem J1_eq_sSup_j1Functional (a : CoefficientField d Λ) (mask : Vec d → ℝ) (p q : Vec d) :
    J1 a mask p q = sSup {e : ℝ | ∃ w : HarmonicA1 a, e = j1Functional a mask p q w.grad} :=
  rfl

theorem j1Functional_congr_ae (a : CoefficientField d Λ) (mask : Vec d → ℝ) (p q : Vec d)
    {g g' : Vec d → Vec d} (h : g =ᵐ[volume] g') :
    j1Functional a mask p q g = j1Functional a mask p q g' := by
  unfold j1Functional
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

/-- The homogenized objective `-½ ξ·Aξ - p·Aξ + q·ξ` of the proof of Proposition 4.3. -/
def homogenizedJ1Objective (A : Mat d) (p q ξ : Vec d) : ℝ :=
  -(1 / 2 : ℝ) * dot ξ (A.mulVec ξ) - dot p (A.mulVec ξ) + dot q ξ

/-- The homogenized energy `½ p·Ap + ½ q·A⁻¹q - p·q` of (4.10). -/
def homogenizedJ1 (A : Mat d) (p q : Vec d) : ℝ :=
  (1 / 2 : ℝ) * dot p (A.mulVec p) + (1 / 2 : ℝ) * dot q (A⁻¹.mulVec q) - dot p q

/-- Completing the square: the homogenized objective is the homogenized energy minus
`½ (ξ - ξ*)·A(ξ - ξ*)`, with maximizer `ξ* = -p + A⁻¹q`. -/
theorem homogenizedJ1Objective_eq {A : Mat d} (hAsymm : A.transpose = A) (hA : IsUnit A.det)
    (p q ξ : Vec d) :
    homogenizedJ1Objective A p q ξ = homogenizedJ1 A p q -
      (1 / 2 : ℝ) * dot (ξ - (A⁻¹.mulVec q - p)) (A.mulVec (ξ - (A⁻¹.mulVec q - p))) := by
  set y := A⁻¹.mulVec q with hydef
  have hy : A.mulVec y = q := mulVec_inv_mulVec hA q
  have hs1 := dot_mulVec_comm hAsymm ξ p
  have hs2 := dot_mulVec_comm hAsymm y ξ
  have hs3 := dot_mulVec_comm hAsymm y p
  rw [hy] at hs2 hs3
  have hc1 : dot q ξ = dot ξ q := dotProduct_comm _ _
  have hc2 : dot q y = dot y q := dotProduct_comm _ _
  simp only [homogenizedJ1Objective, homogenizedJ1, ← hydef, Matrix.mulVec_sub, hy,
    dot_eq_dotProduct, sub_dotProduct, dotProduct_sub] at hs1 hs2 hs3 hc1 hc2 ⊢
  linarith

/-! ## The deterministic part of Proposition 4.3 -/

/-- **Proposition 4.3, deterministic part**, (4.10) from (4.11) and (4.12). Suppose that the
gradients of `A₁` are, up to null sets, exactly the fields `G ξ`, `ξ ∈ ℝ^d` ((4.12)), that `A` is
symmetric with `|ξ|² ≤ ξ·Aξ`, and that for every `ξ` the functional of (4.8) at `G ξ` is within
`ε (|ξ|² + |ξ| (|p| + |q|))` of `-½ ξ·Aξ - p·Aξ + q·ξ` ((4.11)), with `0 ≤ ε ≤ 1/5`. Then
`|J₁(Ψ, p, q) - (½ p·Ap + ½ q·A⁻¹q - p·q)| ≤ 7 ε (|p|² + |q|²)`. -/
theorem abs_J1_sub_homogenizedJ1_le (a : CoefficientField d Λ) (mask : Vec d → ℝ) (A : Mat d)
    (hAsymm : A.transpose = A) (hAcoer : ∀ ξ : Vec d, euclideanSq ξ ≤ dot ξ (A.mulVec ξ))
    (G : Vec d → Vec d → Vec d)
    (hspan : ∀ w : HarmonicA1 a, ∃ ξ : Vec d, w.grad =ᵐ[volume] G ξ)
    (hrealize : ∀ ξ : Vec d, ∃ w : HarmonicA1 a, w.grad =ᵐ[volume] G ξ)
    (p q : Vec d) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 5)
    (herr : ∀ ξ : Vec d,
      |j1Functional a mask p q (G ξ) - homogenizedJ1Objective A p q ξ| ≤
        ε * (euclideanNorm ξ ^ 2 + euclideanNorm ξ * (euclideanNorm p + euclideanNorm q))) :
    |J1 a mask p q - homogenizedJ1 A p q| ≤
      7 * ε * (euclideanNorm p ^ 2 + euclideanNorm q ^ 2) := by
  have hdet : IsUnit A.det := isUnit_det_of_coercive hAcoer
  set ξs : Vec d := A⁻¹.mulVec q - p with hξs
  set m : ℝ := euclideanNorm p + euclideanNorm q with hm
  set B : ℝ := euclideanNorm p ^ 2 + euclideanNorm q ^ 2 with hB
  have hp0 := euclideanNorm_nonneg p
  have hq0 := euclideanNorm_nonneg q
  have hm0 : 0 ≤ m := add_nonneg hp0 hq0
  have hm2 : m ^ 2 ≤ 2 * B := by
    rw [hm, hB]
    nlinarith [sq_nonneg (euclideanNorm p - euclideanNorm q)]
  have hξsm : euclideanNorm ξs ≤ m := by
    calc euclideanNorm ξs ≤ euclideanNorm (A⁻¹.mulVec q) + euclideanNorm p :=
          euclideanNorm_sub_le _ _
      _ ≤ euclideanNorm q + euclideanNorm p := by
          linarith [euclideanNorm_inv_mulVec_le hAcoer q]
      _ = m := by rw [hm]; ring
  -- the upper bound for every value of the functional on the family
  have hup : ∀ ξ : Vec d, j1Functional a mask p q (G ξ) ≤ homogenizedJ1 A p q + 7 * ε * B := by
    intro ξ
    have h1 := (abs_le.mp (herr ξ)).2
    have h2 := homogenizedJ1Objective_eq hAsymm hdet p q ξ
    rw [← hξs] at h2
    have h3 := hAcoer (ξ - ξs)
    rw [← euclideanNorm_sq] at h3
    set t := euclideanNorm (ξ - ξs)
    set n := euclideanNorm ξ
    have ht0 : 0 ≤ t := euclideanNorm_nonneg _
    have hn0 : 0 ≤ n := euclideanNorm_nonneg _
    have hnt : n ≤ t + m := by
      have := euclideanNorm_add_le (ξ - ξs) ξs
      rw [sub_add_cancel] at this
      linarith
    have e1 : n ^ 2 + n * m ≤ (t + m) ^ 2 + (t + m) * m := by
      have : n ^ 2 ≤ (t + m) ^ 2 := pow_le_pow_left₀ hn0 hnt 2
      nlinarith
    have e2 : (t + m) ^ 2 + (t + m) * m ≤ 5 / 2 * t ^ 2 + 7 / 2 * m ^ 2 := by
      nlinarith [sq_nonneg (t - m)]
    have e3 : ε * (n ^ 2 + n * m) ≤ ε * (5 / 2 * t ^ 2 + 7 / 2 * m ^ 2) :=
      mul_le_mul_of_nonneg_left (e1.trans e2) hε0
    have e4 : ε * (5 / 2 * t ^ 2) ≤ 1 / 2 * t ^ 2 := by nlinarith [sq_nonneg t]
    have e5 : ε * (7 / 2 * m ^ 2) ≤ 7 * ε * B := by nlinarith
    nlinarith
  -- the lower bound at the maximizer `ξ*`
  have hlow : homogenizedJ1 A p q - 7 * ε * B ≤ j1Functional a mask p q (G ξs) := by
    have h1 := (abs_le.mp (herr ξs)).1
    have h2 := homogenizedJ1Objective_eq hAsymm hdet p q ξs
    rw [← hξs, sub_self, Matrix.mulVec_zero, dot_eq_dotProduct, dotProduct_zero, mul_zero,
      sub_zero] at h2
    have hn0 := euclideanNorm_nonneg ξs
    have e1 : euclideanNorm ξs ^ 2 + euclideanNorm ξs * m ≤ 2 * m ^ 2 := by nlinarith
    have e2 : ε * (euclideanNorm ξs ^ 2 + euclideanNorm ξs * m) ≤ 7 * ε * B := by nlinarith
    linarith
  -- the supremum
  rw [J1_eq_sSup_j1Functional]
  set S : Set ℝ := {e : ℝ | ∃ w : HarmonicA1 a, e = j1Functional a mask p q w.grad}
  have hmemS : ∀ ξ : Vec d, j1Functional a mask p q (G ξ) ∈ S := by
    intro ξ
    obtain ⟨w, hw⟩ := hrealize ξ
    exact ⟨w, (j1Functional_congr_ae a mask p q hw).symm⟩
  have hbound : ∀ e ∈ S, e ≤ homogenizedJ1 A p q + 7 * ε * B := by
    rintro e ⟨w, rfl⟩
    obtain ⟨ξ, hξ⟩ := hspan w
    rw [j1Functional_congr_ae a mask p q hξ]
    exact hup ξ
  have hsup_le : sSup S ≤ homogenizedJ1 A p q + 7 * ε * B :=
    csSup_le ⟨_, hmemS ξs⟩ hbound
  have hle_sup : j1Functional a mask p q (G ξs) ≤ sSup S :=
    le_csSup ⟨_, hbound⟩ (hmemS ξs)
  rw [abs_le]
  constructor <;> linarith

/-! ## The bound (4.11) from the averages (3.101)–(3.103) -/

theorem dot_integral {X : Type*} [MeasurableSpace X] {μ : Measure X} (p : Vec d)
    {F : X → Vec d} (hF : Integrable F μ) :
    dot p (∫ x, F x ∂μ) = ∫ x, dot p (F x) ∂μ := by
  unfold dot
  rw [integral_finsetSum _ (fun i _ => (Integrable.eval hF i).const_mul (p i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_integral (Integrable.eval hF), integral_const_mul]

theorem integrable_dot_left {X : Type*} [MeasurableSpace X] {μ : Measure X} (p : Vec d)
    {F : X → Vec d} (hF : Integrable F μ) : Integrable (fun x => dot p (F x)) μ := by
  unfold dot
  exact integrable_finsetSum _ fun i _ => (Integrable.eval hF i).const_mul (p i)

/-- **(4.11) from (3.101)–(3.103)**: if the `Ψ`-averages of a gradient field `g`, of its flux
`a g` and of its energy density `g·ag` are within `ε|ξ|`, `ε|ξ|` and `2ε|ξ|²` of `ξ`, `Aξ` and
`ξ·Aξ`, then the functional of (4.8) at `g` is within `ε (|ξ|² + |ξ| (|p| + |q|))` of
`-½ ξ·Aξ - p·Aξ + q·ξ`. -/
theorem abs_j1Functional_sub_le_of_averages (a : CoefficientField d Λ) (mask : Vec d → ℝ)
    (A : Mat d) (p q ξ : Vec d) (g : Vec d → Vec d) {ε : ℝ}
    (hgrad : Integrable (fun x => mask x • g x))
    (hflux : Integrable (fun x => mask x • (a x).mulVec (g x)))
    (henergy : Integrable (fun x => mask x * dot (g x) ((a x).mulVec (g x))))
    (hP : euclideanNorm ((∫ x, mask x • g x) - ξ) ≤ ε * euclideanNorm ξ)
    (hQ : euclideanNorm ((∫ x, mask x • (a x).mulVec (g x)) - A.mulVec ξ) ≤
      ε * euclideanNorm ξ)
    (hE : |(∫ x, mask x * dot (g x) ((a x).mulVec (g x))) - dot ξ (A.mulVec ξ)| ≤
      2 * ε * euclideanNorm ξ ^ 2) :
    |j1Functional a mask p q g - homogenizedJ1Objective A p q ξ| ≤
      ε * (euclideanNorm ξ ^ 2 + euclideanNorm ξ * (euclideanNorm p + euclideanNorm q)) := by
  have hsplit : j1Functional a mask p q g =
      -(1 / 2 : ℝ) * (∫ x, mask x * dot (g x) ((a x).mulVec (g x))) -
        dot p (∫ x, mask x • (a x).mulVec (g x)) + dot q (∫ x, mask x • g x) := by
    have hfl := integrable_dot_left p hflux
    have hgr := integrable_dot_left q hgrad
    have hfun : (fun x => mask x * (-(1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x)) -
        dot p ((a x).mulVec (g x)) + dot q (g x))) = fun x =>
          -(1 / 2 : ℝ) * (mask x * dot (g x) ((a x).mulVec (g x))) -
            dot p (mask x • (a x).mulVec (g x)) + dot q (mask x • g x) := by
      funext x
      simp only [dot_eq_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    have hI : Integrable (fun x => -(1 / 2 : ℝ) * (mask x * dot (g x) ((a x).mulVec (g x))) -
        dot p (mask x • (a x).mulVec (g x))) := (henergy.const_mul _).sub hfl
    unfold j1Functional
    rw [hfun, integral_add hI hgr,
      integral_sub (henergy.const_mul _) hfl, integral_const_mul, dot_integral p hflux,
      dot_integral q hgrad]
  rw [hsplit]
  have hdiff : (-(1 / 2 : ℝ) * (∫ x, mask x * dot (g x) ((a x).mulVec (g x))) -
        dot p (∫ x, mask x • (a x).mulVec (g x)) + dot q (∫ x, mask x • g x)) -
      homogenizedJ1Objective A p q ξ =
      -(1 / 2 : ℝ) * ((∫ x, mask x * dot (g x) ((a x).mulVec (g x))) - dot ξ (A.mulVec ξ)) -
        dot p ((∫ x, mask x • (a x).mulVec (g x)) - A.mulVec ξ) +
        dot q ((∫ x, mask x • g x) - ξ) := by
    simp only [homogenizedJ1Objective, dot_eq_dotProduct, dotProduct_sub]
    ring
  rw [hdiff]
  have h1 := abs_dot_le p ((∫ x, mask x • (a x).mulVec (g x)) - A.mulVec ξ)
  have h2 := abs_dot_le q ((∫ x, mask x • g x) - ξ)
  have hp0 := euclideanNorm_nonneg p
  have hq0 := euclideanNorm_nonneg q
  have h1' : |dot p ((∫ x, mask x • (a x).mulVec (g x)) - A.mulVec ξ)| ≤
      euclideanNorm p * (ε * euclideanNorm ξ) :=
    h1.trans (mul_le_mul_of_nonneg_left hQ hp0)
  have h2' : |dot q ((∫ x, mask x • g x) - ξ)| ≤ euclideanNorm q * (ε * euclideanNorm ξ) :=
    h2.trans (mul_le_mul_of_nonneg_left hP hq0)
  obtain ⟨h1l, h1u⟩ := abs_le.mp h1'
  obtain ⟨h2l, h2u⟩ := abs_le.mp h2'
  obtain ⟨hEl, hEu⟩ := abs_le.mp hE
  rw [abs_le]
  constructor <;> nlinarith

end QSH
