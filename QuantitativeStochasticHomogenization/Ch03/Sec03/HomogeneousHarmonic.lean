import QuantitativeStochasticHomogenization.Ch03.Sec03.HomogeneousParts
import QuantitativeStochasticHomogenization.Ch03.Sec01.Proposition32

/-!
# The homogeneous components of an `A`-harmonic polynomial are `A`-harmonic

For `q ∈ Ā_k` and `t > 0` the dilate `x ↦ q(t x)` is in `Ā_k` (`dilate_mem_harmonicPolys`), and the
homogeneous component of degree `m` of `q` is a fixed linear combination of the dilates
`q(t_j ·)`, `t_j = (j + 1)/(k + 1)` (`exists_vandermonde_combination`), so it belongs to `Ā_m`
(`homogeneousComponent_mem_harmonicPolys`). This is the reduction to homogeneous `q` at the start of
the proof of (3.46).
-/

open MeasureTheory Filter Set

noncomputable section

namespace QSH

variable {d : ℕ}

theorem const_mul_mem_harmonicPolys {A : Mat d} {k : ℕ} {p : Vec d → ℝ}
    (hp : p ∈ harmonicPolys A k) (c : ℝ) : (fun x => c * p x) ∈ harmonicPolys A k := by
  obtain ⟨⟨P, hP, hPe⟩, hph⟩ := hp
  refine ⟨⟨MvPolynomial.C c * P, (MvPolynomial.totalDegree_mul _ _).trans (by
    rw [MvPolynomial.totalDegree_C, zero_add]; exact hP), fun x => ?_⟩,
    fun ρ hρ => (hph ρ hρ).const_mul'' c⟩
  show c * p x = _
  rw [hPe x, map_mul, MvPolynomial.eval_C]

theorem finset_sum_mem_harmonicPolys {A : Mat d} {k : ℕ} {ι : Type*} (s : Finset ι)
    {p : ι → Vec d → ℝ} (hp : ∀ i ∈ s, p i ∈ harmonicPolys A k) :
    (fun x => ∑ i ∈ s, p i x) ∈ harmonicPolys A k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_mem_harmonicPolys A k
  | insert i s hi ih =>
    have h := add_mem_harmonicPolys (hp i (Finset.mem_insert_self i s))
      (ih fun j hj => hp j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using h

/-- The dilate of an element of `Ā_k`. -/
theorem dilate_mem_harmonicPolys {A : Mat d} {k : ℕ} {p : Vec d → ℝ}
    (hp : p ∈ harmonicPolys A k) {t : ℝ} (ht : 0 < t) :
    (fun x => p (t • x)) ∈ harmonicPolys A k := by
  obtain ⟨⟨P, hP, hPe⟩, hph⟩ := hp
  obtain ⟨Q, hQ, hQe⟩ := exists_poly_comp_mulVec (t • (1 : Matrix (Fin d) (Fin d) ℝ)) P
  refine ⟨⟨Q, hQ.trans hP, fun x => ?_⟩, fun ρ hρ => ?_⟩
  · show p (t • x) = _
    rw [hQe, Matrix.smul_mulVec, Matrix.one_mulVec, hPe]
  · obtain ⟨hL2, g, hg, hgrad, hdiv⟩ := hph (t * ρ) (mul_pos ht hρ)
    have hU := measurableSet_ball' (0 : Vec d) (t * ρ)
    have hV := measurableSet_ball' (0 : Vec d) ρ
    have hVt := volume_ball_ne_top' (0 : Vec d) ρ
    have hmap : ∀ x ∈ ball (0 : Vec d) ρ, t • x ∈ ball (0 : Vec d) (t * ρ) := fun x hx => by
      rw [← smul_ball_zero ht]; exact Set.smul_mem_smul_set hx
    have hmap0 : ∀ x ∈ ball (0 : Vec d) ρ, t • x + 0 ∈ ball (0 : Vec d) (t * ρ) := fun x hx => by
      rw [add_zero]; exact hmap x hx
    have hgt : ∀ i, MemLp (fun x => g (t • x) i) 2 (volume.restrict (ball 0 ρ)) := fun i => by
      have h := MemLp.comp_smul_add_restrict (f := fun x => g x i) hU hV ht.ne' 0 hmap0 (hg i)
      simpa only [add_zero] using h
    have hloc : ∀ i, LocallyIntegrableOn (fun x => ((fun _ => A) (t • x)).mulVec (g (t • x)) i)
        (ball 0 ρ) volume := fun i => by
      have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) ρ)) :=
        isFiniteMeasure_restrict.mpr hVt
      exact IntegrableOn.locallyIntegrableOn
        ((TwoScale.memLp_const_mulVec A hgt i).integrable one_le_two)
    obtain ⟨h1, h2, h3, h4⟩ := rescale_h1_div hU hV hVt ht hmap (fun _ => A) hL2 hg hgrad hdiv hloc
    exact ⟨h1, fun x => t • g (t • x), h2, h3, h4⟩

/-- The homogeneous components of a polynomial of degree at most `k` are fixed combinations of its
dilates by `t_j ∈ (0, 1]`. -/
theorem exists_vandermonde_combination (k : ℕ) :
    ∃ (t : Fin (k + 1) → ℝ) (L : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ), (∀ j, 0 < t j) ∧
      ∀ Q : MvPolynomial (Fin d) ℝ, Q.totalDegree ≤ k → ∀ (m : Fin (k + 1)) (x : Vec d),
        MvPolynomial.eval x (MvPolynomial.homogeneousComponent (m : ℕ) Q) =
          ∑ j, L m j * MvPolynomial.eval (t j • x) Q := by
  obtain ⟨t, ht⟩ : ∃ t : Fin (k + 1) → ℝ, t = fun j : Fin (k + 1) => (((j : ℕ) : ℝ) + 1) / (k + 1) :=
    ⟨_, rfl⟩
  have ht0 : ∀ j, 0 < t j := fun j => by rw [ht]; positivity
  have hinj : Function.Injective t := fun i j hij => by
    rw [ht] at hij
    simp only at hij
    have h := (div_left_inj' (by positivity : ((k : ℝ) + 1) ≠ 0)).1 hij
    exact Fin.ext (by exact_mod_cast (add_right_cancel h))
  obtain ⟨L, hL⟩ : ∃ L : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ, L = (Matrix.vandermonde t)⁻¹ :=
    ⟨_, rfl⟩
  have hdet : (Matrix.vandermonde t).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.2 hinj
  have hLV : L * Matrix.vandermonde t = 1 := by
    rw [hL]; exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet)
  have hdelta : ∀ m i : Fin (k + 1), ∑ j, L m j * t j ^ (i : ℕ) = if m = i then 1 else 0 := by
    intro m i
    have h := congrFun (congrFun hLV m) i
    simp only [Matrix.mul_apply, Matrix.vandermonde_apply, Matrix.one_apply] at h
    exact h
  refine ⟨t, L, ht0, fun Q hQ m x => ?_⟩
  simp_rw [eval_smul_eq_sum hQ, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, hdelta]
  simp

/-- **The homogeneous components of an `A`-harmonic polynomial are `A`-harmonic.** -/
theorem homogeneousComponent_mem_harmonicPolys {A : Mat d} {k : ℕ} {p : Vec d → ℝ}
    (hp : p ∈ harmonicPolys A k) {P : MvPolynomial (Fin d) ℝ} (hP : P.totalDegree ≤ k)
    (hPe : ∀ x, p x = MvPolynomial.eval x P) (m : ℕ) :
    (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m P)) ∈ harmonicPolys A m := by
  have hdeg : (MvPolynomial.homogeneousComponent m P).totalDegree ≤ m :=
    (MvPolynomial.homogeneousComponent_isHomogeneous m P).totalDegree_le
  by_cases hmk : m ≤ k
  · obtain ⟨t, L, ht0, hcomb⟩ := exists_vandermonde_combination (d := d) k
    have hcomb' := hcomb P hP ⟨m, Nat.lt_succ_of_le hmk⟩
    simp only at hcomb'
    have hmem : (fun x => ∑ j, L ⟨m, Nat.lt_succ_of_le hmk⟩ j *
        MvPolynomial.eval (t j • x) P) ∈ harmonicPolys A k := by
      refine finset_sum_mem_harmonicPolys _ fun j _ => const_mul_mem_harmonicPolys ?_ _
      have h := dilate_mem_harmonicPolys hp (ht0 j)
      simpa only [hPe] using h
    refine ⟨⟨_, hdeg, fun x => rfl⟩, fun ρ hρ => ?_⟩
    have e : (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m P)) =
        fun x => ∑ j, L ⟨m, Nat.lt_succ_of_le hmk⟩ j * MvPolynomial.eval (t j • x) P :=
      funext hcomb'
    rw [e]
    exact hmem.2 ρ hρ
  · have h0 : MvPolynomial.homogeneousComponent m P = 0 :=
      MvPolynomial.homogeneousComponent_eq_zero _ _ (by omega)
    simp only [h0, map_zero]
    exact zero_mem_harmonicPolys A m

end QSH
