import QuantitativeStochasticHomogenization.Ch03.Sec02.HarmonicGrowth
import PDEFoundation.Monotonicity.Core.Homogeneous

/-!
# The norm equivalence (3.27)

Armstrong–Kuusi–Mourrat, Section 3.2, (3.26)–(3.27): for `p ∈ Ā_k`, a center `y` and `r > 0`,
`‖p‖_{L̲²(B_r(y))} ≤ ∑_{m ≤ k} ‖(π_{m,y} - π_{m-1,y}) p‖_{L̲²(B_r(y))} ≤ C_k ‖p‖_{L̲²(B_r(y))}`, where
`(π_{m,y} - π_{m-1,y}) p (x) = (1/m!) ∇^m p(y) (x - y)^{⊗m}` is the homogeneous part of degree `m` of the
Taylor expansion at `y`.

For a polynomial `p(x) = Q(x - y)` the homogeneous part of degree `m` at `y` is the homogeneous
component of degree `m` of `Q` (`eval_homogeneousComponent_eq_iteratedFDeriv`), and the inequality
holds for every polynomial of degree at most `k`, with `C(k, d)` (`scalarRms_homogeneousComponents`):
by homogeneity `Q(t v) = ∑_i t^i Q_i(v)`, so each component is a fixed combination of `Q(t_j ·)` for
`k + 1` distinct `t_j ∈ (0, 1]` (the inverse Vandermonde matrix), and `‖Q(t ·)‖_{L̲²(B_r)} ≤
t^{-d/2} ‖Q‖_{L̲²(B_r)}`. The book derives the second inequality for `ā`-harmonic polynomials from
(3.7); the proof here does not use harmonicity.
-/

open MeasureTheory Filter Set Topology
open scoped Pointwise

noncomputable section

namespace QSH

variable {d : ℕ}

theorem scalarRms_ball_translate (y : Vec d) (r : ℝ) (f : Vec d → ℝ) :
    scalarRms volume (ball y r) f = scalarRms volume (ball 0 r) (fun x => f (x + y)) := by
  unfold scalarRms
  congr 1
  rw [setAverage_eq, setAverage_eq, measureReal_def, measureReal_def,
    volume_ball_eq_zero_center y r]
  congr 1
  have h := (measurePreserving_add_right (volume : Measure (Vec d)) y).setIntegral_preimage_emb
    (measurableEmbedding_addRight y) (fun x => f x ^ 2) (ball y r)
  rw [preimage_add_right_ball] at h
  exact h.symm

theorem memLp_eval_ball (P : MvPolynomial (Fin d) ℝ) (r : ℝ) :
    MemLp (fun x => MvPolynomial.eval x P) 2 (volume.restrict (ball (0 : Vec d) r)) := by
  have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) r)) :=
    isFiniteMeasure_restrict.mpr (volume_ball_ne_top' 0 r)
  refine MemLp.of_bound (MvPolynomial.continuous_eval P).aestronglyMeasurable
    ((∑ s ∈ P.support, |P.coeff s|) * max r 1 ^ P.totalDegree) ?_
  refine (ae_restrict_iff' (measurableSet_ball' 0 r)).2 (Eventually.of_forall fun x hx => ?_)
  rw [Real.norm_eq_abs]
  exact abs_eval_mvPolynomial_le le_rfl (le_max_right r 1)
    ((mem_ball_zero_iff'.1 hx).le.trans (le_max_left r 1))

theorem eval_eq_sum_homogeneousComponent {Q : MvPolynomial (Fin d) ℝ} {k : ℕ}
    (hQ : Q.totalDegree ≤ k) (v : Vec d) :
    MvPolynomial.eval v Q =
      ∑ i ∈ Finset.range (k + 1), MvPolynomial.eval v (MvPolynomial.homogeneousComponent i Q) := by
  conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent Q]
  rw [map_sum]
  refine Finset.sum_subset (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega)
    fun i hi hni => ?_
  rw [MvPolynomial.homogeneousComponent_eq_zero, map_zero]
  simp only [Finset.mem_range] at hi hni
  omega

theorem eval_smul_eq_sum {Q : MvPolynomial (Fin d) ℝ} {k : ℕ} (hQ : Q.totalDegree ≤ k) (t : ℝ)
    (v : Vec d) :
    MvPolynomial.eval (t • v) Q = ∑ i ∈ Finset.range (k + 1),
      t ^ i * MvPolynomial.eval v (MvPolynomial.homogeneousComponent i Q) := by
  rw [eval_eq_sum_homogeneousComponent hQ]
  exact Finset.sum_congr rfl fun i _ => PDE.eval_smul_of_isHomogeneous
    (MvPolynomial.homogeneousComponent_isHomogeneous i Q) t v

/-- **(3.27) for polynomials, centered at the origin**: the homogeneous components of a polynomial
of degree at most `k` satisfy `‖Q‖ ≤ ∑_m ‖Q_m‖ ≤ C ‖Q‖` in `L̲²(B_r)`, with `C(k, d)`. -/
theorem scalarRms_homogeneousComponents_zero (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : MvPolynomial (Fin d) ℝ, Q.totalDegree ≤ k → ∀ r : ℝ, 0 < r →
      scalarRms volume (ball 0 r) (fun x => MvPolynomial.eval x Q) ≤
        ∑ m ∈ Finset.range (k + 1), scalarRms volume (ball 0 r)
          (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q)) ∧
      ∑ m ∈ Finset.range (k + 1), scalarRms volume (ball 0 r)
          (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q)) ≤
        C * scalarRms volume (ball 0 r) (fun x => MvPolynomial.eval x Q) := by
  -- the nodes `t_j = (j + 1)/(k + 1)` and the inverse Vandermonde matrix
  obtain ⟨t, ht⟩ : ∃ t : Fin (k + 1) → ℝ, t = fun j : Fin (k + 1) => (((j : ℕ) : ℝ) + 1) / (k + 1) :=
    ⟨_, rfl⟩
  have ht0 : ∀ j, 0 < t j := fun j => by rw [ht]; positivity
  have ht1 : ∀ j, t j ≤ 1 := fun j => by
    rw [ht, div_le_one (by positivity)]
    have := j.isLt
    have : ((j : ℕ) : ℝ) + 1 ≤ (k : ℝ) + 1 := by exact_mod_cast this
    linarith
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
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∑ m : Fin (k + 1), ∑ j : Fin (k + 1),
      |L m j| * Real.sqrt ((1 / t j) ^ d) := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  refine ⟨C, hC0, fun Q hQ r hr => ⟨?_, ?_⟩⟩
  · have e : (fun x => MvPolynomial.eval x Q) = fun x => ∑ m ∈ Finset.range (k + 1),
        (1 : ℝ) * MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q) := by
      funext x; rw [eval_eq_sum_homogeneousComponent hQ]; simp
    rw [e]
    refine (scalarRms_finset_sum_le _ (fun m => memLp_eval_ball _ r) _).trans (le_of_eq ?_)
    simp
  · -- each component is a combination of the dilates `Q(t_j ·)`
    have hcomp : ∀ m : Fin (k + 1), (fun x => MvPolynomial.eval x
        (MvPolynomial.homogeneousComponent (m : ℕ) Q)) =
        fun x => ∑ j ∈ Finset.univ, L m j * MvPolynomial.eval (t j • x) Q := by
      intro m
      funext x
      simp_rw [eval_smul_eq_sum hQ, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
      rw [Finset.sum_comm]
      simp_rw [← mul_assoc, ← Finset.sum_mul, hdelta]
      simp
    have hdil : ∀ j : Fin (k + 1), scalarRms volume (ball 0 r)
        (fun x => MvPolynomial.eval (t j • x) Q) ≤
        Real.sqrt ((1 / t j) ^ d) * scalarRms volume (ball 0 r) (fun x => MvPolynomial.eval x Q) := by
      intro j
      have e : scalarRms volume (ball 0 r) (fun x => MvPolynomial.eval (t j • x) Q) =
          scalarRms volume (t j • ball 0 r) (fun z => MvPolynomial.eval z Q) :=
        TwoScale.scalarRms_comp_smul (ht0 j) _ (fun z => MvPolynomial.eval z Q)
      rw [e, smul_ball_zero (ht0 j)]
      have h := scalarRms_ball_le (mul_pos (ht0 j) hr)
        (by nlinarith [ht1 j] : t j * r ≤ r) (memLp_eval_ball Q r)
      rwa [show r / (t j * r) = 1 / t j by field_simp] at h
    have hmem : ∀ j : Fin (k + 1), MemLp (fun x => MvPolynomial.eval (t j • x) Q) 2
        (volume.restrict (ball (0 : Vec d) r)) := fun j => by
      obtain ⟨Q', -, hQ'⟩ := exists_poly_comp_mulVec (t j • (1 : Matrix (Fin d) (Fin d) ℝ)) Q
      have e : (fun x => MvPolynomial.eval (t j • x) Q) = fun x => MvPolynomial.eval x Q' := by
        funext x; rw [hQ', Matrix.smul_mulVec, Matrix.one_mulVec]
      rw [e]; exact memLp_eval_ball Q' r
    rw [← Fin.sum_univ_eq_sum_range (fun m => scalarRms volume (ball 0 r)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q)))]
    calc ∑ m : Fin (k + 1), scalarRms volume (ball 0 r)
          (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent (m : ℕ) Q))
        ≤ ∑ m : Fin (k + 1), ∑ j : Fin (k + 1), |L m j| * (Real.sqrt ((1 / t j) ^ d) *
            scalarRms volume (ball 0 r) (fun x => MvPolynomial.eval x Q)) := by
          refine Finset.sum_le_sum fun m _ => ?_
          rw [hcomp m]
          refine (scalarRms_finset_sum_le _ hmem _).trans (Finset.sum_le_sum fun j _ => ?_)
          exact mul_le_mul_of_nonneg_left (hdil j) (abs_nonneg _)
      _ = C * scalarRms volume (ball 0 r) (fun x => MvPolynomial.eval x Q) := by
          rw [hC, Finset.sum_mul]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring

theorem deriv_iterate_polynomial_eval (G : Polynomial ℝ) (n : ℕ) :
    deriv^[n] (fun s => G.eval s) = fun s => (Polynomial.derivative^[n] G).eval s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    funext s
    exact Polynomial.deriv _

/-- The homogeneous component of degree `m` of a polynomial is its Taylor part of degree `m` at the
origin: `Q_m(v) = (1/m!) ∇^m Q(0) v^{⊗m}`. -/
theorem eval_homogeneousComponent_eq_iteratedFDeriv (Q : MvPolynomial (Fin d) ℝ) (m : ℕ)
    (v : Vec d) :
    MvPolynomial.eval v (MvPolynomial.homogeneousComponent m Q) =
      (m.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ m (fun x => MvPolynomial.eval x Q) 0 (fun _ => v) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = max m Q.totalDegree := ⟨_, rfl⟩
  have hQ : Q.totalDegree ≤ k := by rw [hk]; exact le_max_right _ _
  have hmk : m ≤ k := by rw [hk]; exact le_max_left _ _
  obtain ⟨G, hG⟩ : ∃ G : Polynomial ℝ, G = ∑ i ∈ Finset.range (k + 1),
      Polynomial.C (MvPolynomial.eval v (MvPolynomial.homogeneousComponent i Q)) *
        Polynomial.X ^ i := ⟨_, rfl⟩
  have hg : (fun s : ℝ => MvPolynomial.eval (s • v) Q) = fun s => G.eval s := by
    funext s
    rw [eval_smul_eq_sum hQ, hG, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    ring
  have hline := PDE.iteratedDeriv_line (U := univ) isOpen_univ
    (PDE.contDiff_eval_mvPolynomial Q).contDiffOn v m 0 (mem_univ _)
  rw [zero_smul, hg, iteratedDeriv_eq_iterate, deriv_iterate_polynomial_eval] at hline
  have hcoeff : (Polynomial.derivative^[m] G).eval 0 =
      (m.factorial : ℝ) * MvPolynomial.eval v (MvPolynomial.homogeneousComponent m Q) := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative, zero_add,
      Nat.descFactorial_self, nsmul_eq_mul, hG, Polynomial.finsetSum_coeff]
    congr 1
    rw [Finset.sum_eq_single m]
    · simp
    · intro i _ him
      simp [Ne.symm him]
    · intro hm
      exact absurd (Finset.mem_range.2 (by omega)) hm
  have hline' : (Polynomial.derivative^[m] G).eval 0 =
      iteratedFDeriv ℝ m (fun x => MvPolynomial.eval x Q) 0 (fun _ => v) := hline
  rw [hcoeff] at hline'
  have hfac : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  rw [← hline', inv_mul_cancel_left₀ hfac]

/-- **(3.27)**: for `p ∈ Ā_k`, a center `y` and `r > 0`, with the Taylor parts
`(π_{m,y} - π_{m-1,y}) p (x) = (1/m!) ∇^m p(y) (x - y)^{⊗m}`,
`‖p‖_{L̲²(B_r(y))} ≤ ∑_{m ≤ k} ‖(π_{m,y} - π_{m-1,y}) p‖_{L̲²(B_r(y))} ≤ C ‖p‖_{L̲²(B_r(y))}`, with
`C(k, d)`. -/
theorem equation_3_27 (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : Mat d), ∀ p ∈ harmonicPolys A k, ∀ (y : Vec d) (r : ℝ), 0 < r →
      scalarRms volume (ball y r) p ≤
        ∑ m ∈ Finset.range (k + 1), scalarRms volume (ball y r)
          (fun x => (m.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ m p y (fun _ => x - y)) ∧
      ∑ m ∈ Finset.range (k + 1), scalarRms volume (ball y r)
          (fun x => (m.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ m p y (fun _ => x - y)) ≤
        C * scalarRms volume (ball y r) p := by
  obtain ⟨C, hC0, hzero⟩ := scalarRms_homogeneousComponents_zero (d := d) k
  refine ⟨C, hC0, fun A p hp y r hr => ?_⟩
  obtain ⟨⟨P, hP, hPe⟩, -⟩ := hp
  have hpP : p = fun x => MvPolynomial.eval x P := funext hPe
  obtain ⟨Q, hQ⟩ : ∃ Q : MvPolynomial (Fin d) ℝ,
      Q = MvPolynomial.bind₁ (fun i => MvPolynomial.X i + MvPolynomial.C (y i)) P := ⟨_, rfl⟩
  have hQe : ∀ v, MvPolynomial.eval v Q = p (v + y) := fun v => by
    have e : (fun i => MvPolynomial.eval v (MvPolynomial.X i + MvPolynomial.C (y i))) = v + y := by
      funext i; simp
    rw [hQ, eval_bind₁', hPe, e]
  have hQdeg : Q.totalDegree ≤ k := by
    rw [hQ]
    refine (totalDegree_bind₁_le _ (fun i => ?_) P).trans hP
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · rw [MvPolynomial.totalDegree_X]
    · rw [MvPolynomial.totalDegree_C]; omega
  have hQfun : (fun x => MvPolynomial.eval x Q) = fun x => p (x + y) := funext hQe
  have hpart : ∀ m x, (m.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ m p y (fun _ => x + y - y) =
      MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q) := fun m x => by
    rw [eval_homogeneousComponent_eq_iteratedFDeriv, hQfun, iteratedFDeriv_comp_add_right,
      zero_add, add_sub_cancel_right]
  have hsum : ∀ m ∈ Finset.range (k + 1), scalarRms volume (ball y r)
      (fun x => (m.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ m p y (fun _ => x - y)) =
      scalarRms volume (ball 0 r)
        (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q)) := fun m _ => by
    rw [scalarRms_ball_translate]
    congr 1
    funext x
    exact hpart m x
  have hp0 : scalarRms volume (ball y r) p =
      scalarRms volume (ball 0 r) (fun x => MvPolynomial.eval x Q) := by
    rw [scalarRms_ball_translate, hQfun]
  rw [Finset.sum_congr rfl hsum, hp0]
  exact hzero Q hQdeg r hr

end QSH
