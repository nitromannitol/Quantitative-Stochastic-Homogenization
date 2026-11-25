import QuantitativeStochasticHomogenization.Front.Notation

/-!
# Section 10.1: variational representations of monotone maps

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 10.1, Definition 10.2 (`VariationallyRepresents`): a convex `F : ℝ^d × ℝ^d → ℝ`
variationally represents `φ : ℝ^d → ℝ^d` if `F(p, q) ≥ p·q` with equality exactly when `q = φ(p)`.

For a matrix `a` with positive definite symmetric part `s = (a + aᵀ)/2` and antisymmetric part
`m = (a - aᵀ)/2`, the quadratic form of (10.7),
`A(p, q) = ½ p·s p + ½ (q - m p)·s⁻¹(q - m p)` (`linearRepresentative`), satisfies
`A(p, q) - p·q = ½ (a p - q)·s⁻¹(a p - q)` (`linearRepresentative_sub_dot`). Hence (10.10) and
(10.11) hold and `A` variationally represents `p ↦ a p`
(`variationallyRepresents_linearRepresentative`).
-/

open Matrix

noncomputable section

namespace QSH

variable {d : ℕ}

/-- **Definition 10.2**: `F : ℝ^d × ℝ^d → ℝ` variationally represents `φ : ℝ^d → ℝ^d` if `F` is
convex and `F(p, q) ≥ p·q` for all `p, q ∈ ℝ^d`, with equality if and only if `q = φ(p)`. -/
def VariationallyRepresents (F : Vec d → Vec d → ℝ) (φ : Vec d → Vec d) : Prop :=
  ConvexOn ℝ Set.univ (fun z : Vec d × Vec d => F z.1 z.2) ∧ (∀ p q, dot p q ≤ F p q) ∧
    ∀ p q, F p q = dot p q ↔ q = φ p

/-- The symmetric part `(a + aᵀ)/2` of a matrix. -/
def symmetricPart (a : Mat d) : Mat d := (1 / 2 : ℝ) • (a + a.transpose)

/-- The antisymmetric part `(a - aᵀ)/2` of a matrix. -/
def antisymmetricPart (a : Mat d) : Mat d := (1 / 2 : ℝ) • (a - a.transpose)

/-- **The quadratic form (10.7)**: `A(p, q) = ½ p·s p + ½ (q - m p)·s⁻¹(q - m p)`, with `s` and `m`
the symmetric and antisymmetric parts of `a`. -/
def linearRepresentative (a : Mat d) (p q : Vec d) : ℝ :=
  (1 / 2) * dot p ((symmetricPart a).mulVec p) +
    (1 / 2) * dot (q - (antisymmetricPart a).mulVec p)
      ((symmetricPart a)⁻¹.mulVec (q - (antisymmetricPart a).mulVec p))

private theorem dot_eq (x y : Vec d) : dot x y = x ⬝ᵥ y := rfl

theorem symmetricPart_transpose (a : Mat d) : (symmetricPart a).transpose = symmetricPart a := by
  unfold symmetricPart
  rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

theorem symmetricPart_add_antisymmetricPart (a : Mat d) :
    symmetricPart a + antisymmetricPart a = a := by
  unfold symmetricPart antisymmetricPart
  rw [← smul_add, add_add_sub_cancel, ← two_smul ℝ a, smul_smul]
  norm_num

theorem dotProduct_mulVec_transpose (M : Mat d) (u v : Vec d) :
    u ⬝ᵥ (M.transpose *ᵥ v) = (M *ᵥ u) ⬝ᵥ v := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem dotProduct_antisymmetricPart_self (a : Mat d) (p : Vec d) :
    p ⬝ᵥ (antisymmetricPart a *ᵥ p) = 0 := by
  unfold antisymmetricPart
  rw [Matrix.smul_mulVec, dotProduct_smul, Matrix.sub_mulVec, dotProduct_sub,
    dotProduct_mulVec_transpose, dotProduct_comm, sub_self, smul_zero]

theorem dotProduct_symmetricPart_self (a : Mat d) (p : Vec d) :
    p ⬝ᵥ (symmetricPart a *ᵥ p) = p ⬝ᵥ (a *ᵥ p) := by
  unfold symmetricPart
  rw [Matrix.smul_mulVec, dotProduct_smul, Matrix.add_mulVec, dotProduct_add,
    dotProduct_mulVec_transpose, dotProduct_comm (a *ᵥ p) p, smul_eq_mul]
  ring

/-- A matrix whose quadratic form is positive away from `0` has a nonzero determinant. -/
theorem isUnit_det_symmetricPart {a : Mat d} (ha : ∀ ξ : Vec d, ξ ≠ 0 → 0 < dot ξ (a.mulVec ξ)) :
    IsUnit (symmetricPart a).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, hsv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h := ha v hv
  rw [dot_eq, ← dotProduct_symmetricPart_self, hsv, dotProduct_zero] at h
  exact lt_irrefl 0 h

/-- **Convexity of a nonnegative quadratic form** with a symmetric matrix. -/
theorem convexOn_dotProduct_mulVec {M : Mat d} (hM : M.transpose = M)
    (hpos : ∀ x : Vec d, 0 ≤ x ⬝ᵥ (M *ᵥ x)) :
    ConvexOn ℝ Set.univ (fun x : Vec d => x ⬝ᵥ (M *ᵥ x)) := by
  refine ⟨convex_univ, fun x _ y _ s t hs ht hst => ?_⟩
  have hsym : y ⬝ᵥ (M *ᵥ x) = x ⬝ᵥ (M *ᵥ y) := by
    calc y ⬝ᵥ (M *ᵥ x) = (M *ᵥ y) ⬝ᵥ x := by rw [← dotProduct_mulVec_transpose, hM]
      _ = x ⬝ᵥ (M *ᵥ y) := dotProduct_comm _ _
  have h := hpos (x - y)
  simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct] at h
  simp only [smul_eq_mul, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct]
  rw [hsym] at h ⊢
  obtain rfl : t = 1 - s := by linarith
  nlinarith [mul_nonneg (mul_nonneg hs ht) h]

/-- **The identity behind (10.10)–(10.11)**: `A(p, q) - p·q = ½ (a p - q)·s⁻¹(a p - q)`. -/
theorem linearRepresentative_sub_dot {a : Mat d}
    (ha : ∀ ξ : Vec d, ξ ≠ 0 → 0 < dot ξ (a.mulVec ξ)) (p q : Vec d) :
    linearRepresentative a p q - dot p q =
      (1 / 2) * dot (a.mulVec p - q) ((symmetricPart a)⁻¹.mulVec (a.mulVec p - q)) := by
  obtain ⟨s, hs⟩ : ∃ s : Mat d, s = symmetricPart a := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : Mat d, m = antisymmetricPart a := ⟨_, rfl⟩
  have hdet : IsUnit s.det := by
    rw [hs]
    exact isUnit_det_symmetricPart ha
  have hsT : s.transpose = s := by
    rw [hs]
    exact symmetricPart_transpose a
  have hts : ∀ v : Vec d, s⁻¹ *ᵥ (s *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul s hdet, Matrix.one_mulVec]
  have hst : ∀ v : Vec d, s *ᵥ (s⁻¹ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv s hdet, Matrix.one_mulVec]
  have hsym : ∀ u v : Vec d, (s *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (s *ᵥ v) := fun u v => by
    rw [← dotProduct_mulVec_transpose, hsT]
  have hskew : p ⬝ᵥ (m *ᵥ p) = 0 := by
    rw [hm]
    exact dotProduct_antisymmetricPart_self a p
  have hap : a *ᵥ p = s *ᵥ p + m *ᵥ p := by
    rw [← Matrix.add_mulVec, hs, hm, symmetricPart_add_antisymmetricPart]
  unfold linearRepresentative
  rw [← hs, ← hm]
  simp only [dot_eq]
  obtain ⟨w, hw⟩ : ∃ w : Vec d, w = q - m *ᵥ p := ⟨_, rfl⟩
  rw [← hw]
  have hapq : a *ᵥ p - q = s *ᵥ p - w := by
    rw [hap, hw]
    abel
  have hpw : p ⬝ᵥ w = p ⬝ᵥ q := by
    rw [hw, dotProduct_sub, hskew, sub_zero]
  have h1 : (s *ᵥ p) ⬝ᵥ (s⁻¹ *ᵥ (s *ᵥ p)) = p ⬝ᵥ (s *ᵥ p) := by
    rw [hts, dotProduct_comm]
  have h2 : (s *ᵥ p) ⬝ᵥ (s⁻¹ *ᵥ w) = p ⬝ᵥ w := by
    rw [hsym, hst]
  have h3 : w ⬝ᵥ (s⁻¹ *ᵥ (s *ᵥ p)) = p ⬝ᵥ w := by
    rw [hts, dotProduct_comm]
  rw [hapq, Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, h1, h2, h3, hpw]
  ring

/-- **The quadratic form (10.7) variationally represents `p ↦ a p`**: it is convex,
`A(p, q) ≥ p·q` (10.10), and `A(p, q) = p·q` if and only if `q = a p` (10.11). -/
theorem variationallyRepresents_linearRepresentative {a : Mat d}
    (ha : ∀ ξ : Vec d, ξ ≠ 0 → 0 < dot ξ (a.mulVec ξ)) :
    VariationallyRepresents (linearRepresentative a) a.mulVec := by
  obtain ⟨s, hs⟩ : ∃ s : Mat d, s = symmetricPart a := ⟨_, rfl⟩
  have hdet : IsUnit s.det := by
    rw [hs]
    exact isUnit_det_symmetricPart ha
  have hsT : s.transpose = s := by
    rw [hs]
    exact symmetricPart_transpose a
  have hspos : ∀ x : Vec d, 0 ≤ x ⬝ᵥ (s *ᵥ x) := fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · rw [hs, dotProduct_symmetricPart_self]
      exact (ha x hx).le
  have hst : ∀ v : Vec d, s *ᵥ (s⁻¹ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv s hdet, Matrix.one_mulVec]
  have htT : (s⁻¹).transpose = s⁻¹ := by rw [Matrix.transpose_nonsing_inv, hsT]
  have htpos : ∀ x : Vec d, 0 ≤ x ⬝ᵥ (s⁻¹ *ᵥ x) := fun x => by
    have h := hspos (s⁻¹ *ᵥ x)
    rwa [hst, dotProduct_comm] at h
  have htpos' : ∀ x : Vec d, x ≠ 0 → 0 < x ⬝ᵥ (s⁻¹ *ᵥ x) := fun x hx => by
    have hy : s⁻¹ *ᵥ x ≠ 0 := fun h0 => hx (by rw [← hst x, h0, Matrix.mulVec_zero])
    have h := ha _ hy
    rwa [dot_eq, ← dotProduct_symmetricPart_self, ← hs, hst, dotProduct_comm] at h
  refine ⟨?_, fun p q => ?_, fun p q => ?_⟩
  · have hQs := (convexOn_dotProduct_mulVec hsT hspos).comp_linearMap
      (LinearMap.fst ℝ (Vec d) (Vec d))
    have hQt := (convexOn_dotProduct_mulVec htT htpos).comp_linearMap
      (LinearMap.snd ℝ (Vec d) (Vec d) -
        (Matrix.mulVecLin (antisymmetricPart a)).comp (LinearMap.fst ℝ (Vec d) (Vec d)))
    simp only [Set.preimage_univ] at hQs hQt
    have h := (hQs.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)).add
      (hQt.smul (by norm_num : (0 : ℝ) ≤ 1 / 2))
    refine h.congr fun z _ => ?_
    simp only [Function.comp_apply, Pi.add_apply, smul_eq_mul, LinearMap.sub_apply,
      LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.comp_apply, Matrix.mulVecLin_apply]
    rw [linearRepresentative, ← hs]
    rfl
  · have h := linearRepresentative_sub_dot ha p q
    simp only [dot_eq] at h ⊢
    rw [← hs] at h
    have := htpos (a *ᵥ p - q)
    linarith
  · have h := linearRepresentative_sub_dot ha p q
    constructor
    · intro hq
      rw [hq, sub_self] at h
      by_contra hne
      have := htpos' (a *ᵥ p - q) (sub_ne_zero.mpr (Ne.symm hne))
      simp only [dot_eq] at h
      rw [← hs] at h
      linarith
    · rintro rfl
      simp only [dot_eq] at h
      rw [sub_self, Matrix.mulVec_zero, dotProduct_zero, mul_zero] at h
      exact sub_eq_zero.mp h

end QSH
