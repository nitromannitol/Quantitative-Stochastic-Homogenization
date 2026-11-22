import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import QuantitativeStochasticHomogenization.AppD.HeatKernelDerivatives

/-!
# The periodized Gaussian

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, the expectations (1) of the route of Proposition 4.10 (in the book, Lemma 3.23).

The sum of the integer translates of the one-dimensional heat kernel of variance `2t` is, by the
Poisson summation formula for Gaussians (`Complex.tsum_exp_neg_quadratic`), the Fourier series
`∑ₖ exp(-4π²tk²) e^{2πiky}`; hence it is within `thetaError t = ∑_{k ≠ 0} exp(-4π²tk²)` of `1`,
uniformly in `y`. The lattice periodization `∑_{n ∈ ℤ^d} Φ_{z,r}(x + n)` of the mask is the
product of the one-dimensional sums, so it is within `(1 + thetaError r²)^d - 1` of `1`.
-/

open Complex Filter

noncomputable section

namespace QSH

variable {d : ℕ}

/-! ## Summability -/

theorem summable_exp_neg_mul_int_sq {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => Real.exp (-(c * (n : ℝ) ^ 2)) := by
  have h := (summable_jacobiTheta₂_term_iff 0 (((c / Real.pi : ℝ) : ℂ) * I)).2
    (by rw [Complex.mul_I_im, Complex.ofReal_re]; positivity)
  refine h.norm.congr fun n => ?_
  rw [norm_jacobiTheta₂_term, Complex.mul_I_im, Complex.ofReal_re, Complex.zero_im]
  congr 1
  field_simp
  ring

theorem summable_heatKernel1_add_int {t : ℝ} (ht : 0 < t) (y : ℝ) :
    Summable fun n : ℤ => heatKernel1 t (y + n) := by
  have h := (summable_jacobiTheta₂_term_iff (((y / (4 * Real.pi * t) : ℝ) : ℂ) * I)
    (((1 / (4 * Real.pi * t) : ℝ) : ℂ) * I)).2
    (by rw [Complex.mul_I_im, Complex.ofReal_re]; positivity)
  have h2 := h.norm.mul_left ((4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * Real.exp (-(y * y) / (4 * t)))
  refine h2.congr fun n => ?_
  rw [norm_jacobiTheta₂_term, Complex.mul_I_im, Complex.ofReal_re, Complex.mul_I_im,
    Complex.ofReal_re]
  unfold heatKernel1
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  field_simp
  ring

/-! ## The Poisson summation formula -/

/-- **Poisson summation for the one-dimensional heat kernel**:
`∑ₙ Φ₁(t, y + n) = ∑ₖ exp(-4π²tk²) e^{2πiky}`. -/
theorem tsum_heatKernel1_add_int {t : ℝ} (ht : 0 < t) (y : ℝ) :
    ((∑' n : ℤ, heatKernel1 t (y + n) : ℝ) : ℂ) =
      ∑' k : ℤ, ((Real.exp (-(4 * Real.pi ^ 2 * t * (k : ℝ) ^ 2)) : ℝ) : ℂ) *
        cexp (2 * Real.pi * I * k * y) := by
  set c : ℝ := 4 * Real.pi * t with hcdef
  have hc : 0 < c := by positivity
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  set a : ℂ := ((1 / c : ℝ) : ℂ) with hadef
  set b : ℂ := ((-(y / c) : ℝ) : ℂ) with hbdef
  have ha : 0 < a.re := by rw [hadef, Complex.ofReal_re]; positivity
  have hP := Complex.tsum_exp_neg_quadratic ha b
  set K : ℝ := c ^ (-(1 : ℝ) / 2) * Real.exp (-(y * y) / (4 * t)) with hKdef
  have hL : ∀ n : ℤ, ((heatKernel1 t (y + n) : ℝ) : ℂ) =
      (K : ℂ) * cexp (-Real.pi * a * (n : ℂ) ^ 2 + 2 * Real.pi * b * n) := by
    intro n
    have he : Real.exp (-((y + n) * (y + n)) / (4 * t)) = Real.exp (-(y * y) / (4 * t)) *
        Real.exp (-(n : ℝ) ^ 2 / (4 * t) - y * n / (2 * t)) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    have hb : -Real.pi * a * (n : ℂ) ^ 2 + 2 * Real.pi * b * n =
        ((-(n : ℝ) ^ 2 / (4 * t) - y * n / (2 * t) : ℝ) : ℂ) := by
      rw [hadef, hbdef, hcdef]; push_cast; field_simp; ring
    rw [hb, ← Complex.ofReal_exp, ← Complex.ofReal_mul, hKdef]
    congr 1
    unfold heatKernel1
    rw [he, hcdef]
    ring
  have hR : ∀ k : ℤ, cexp (-Real.pi / a * ((k : ℂ) + I * b) ^ 2) =
      ((Real.exp (-(4 * Real.pi ^ 2 * t * (k : ℝ) ^ 2)) : ℝ) : ℂ) *
        cexp (2 * Real.pi * I * k * y) * ((Real.exp (y * y / (4 * t)) : ℝ) : ℂ) := by
    intro k
    rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [hadef, hbdef, hcdef]
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  have ha2 : (1 : ℂ) / a ^ (1 / 2 : ℂ) = ((c ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [hadef, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_one, ← Complex.ofReal_div]
    congr 1
    rw [Real.div_rpow zero_le_one hc.le, Real.one_rpow, one_div_one_div]
  rw [Complex.ofReal_tsum, tsum_congr hL, tsum_mul_left, hP, ha2, tsum_congr hR, tsum_mul_right]
  have hKc : (K : ℂ) * ((c ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ((Real.exp (y * y / (4 * t)) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
    congr 1
    rw [hKdef, mul_comm (c ^ (-(1 : ℝ) / 2)), mul_assoc, mul_assoc, ← mul_assoc (c ^ (-(1 : ℝ) / 2)),
      ← Real.rpow_add hc, show -(1 : ℝ) / 2 + 1 / 2 = 0 by ring, Real.rpow_zero, one_mul,
      ← Real.exp_add, show -(y * y) / (4 * t) + y * y / (4 * t) = 0 by ring, Real.exp_zero]
  calc (K : ℂ) * (((c ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ((∑' k : ℤ,
        ((Real.exp (-(4 * Real.pi ^ 2 * t * (k : ℝ) ^ 2)) : ℝ) : ℂ) *
          cexp (2 * Real.pi * I * k * y)) * ((Real.exp (y * y / (4 * t)) : ℝ) : ℂ)))
      = ((K : ℂ) * ((c ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ((Real.exp (y * y / (4 * t)) : ℝ) : ℂ)) *
        ∑' k : ℤ, ((Real.exp (-(4 * Real.pi ^ 2 * t * (k : ℝ) ^ 2)) : ℝ) : ℂ) *
          cexp (2 * Real.pi * I * k * y) := by ring
    _ = _ := by rw [hKc, one_mul]

/-! ## The error of the periodization -/

/-- `∑_{k ≠ 0} exp(-4π²tk²)`, written `∑ₖ exp(-4π²tk²) - 1`. -/
def thetaError (t : ℝ) : ℝ := (∑' k : ℤ, Real.exp (-(4 * Real.pi ^ 2 * t * (k : ℝ) ^ 2))) - 1

theorem summable_thetaTerm {t : ℝ} (ht : 0 < t) :
    Summable fun k : ℤ => Real.exp (-(4 * Real.pi ^ 2 * t * (k : ℝ) ^ 2)) := by
  have h := summable_exp_neg_mul_int_sq (show 0 < 4 * Real.pi ^ 2 * t by positivity)
  exact h

theorem thetaError_eq_tsum_ite {t : ℝ} (ht : 0 < t) :
    thetaError t = ∑' k : ℤ, if k = 0 then 0 else Real.exp (-(4 * Real.pi ^ 2 * t * (k : ℝ) ^ 2)) := by
  unfold thetaError
  rw [(summable_thetaTerm ht).tsum_eq_add_tsum_ite 0]
  simp

theorem thetaError_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ thetaError t := by
  rw [thetaError_eq_tsum_ite ht]
  exact tsum_nonneg fun k => by split_ifs; exacts [le_rfl, (Real.exp_pos _).le]

/-- **The periodized one-dimensional heat kernel is within `thetaError t` of `1`.** -/
theorem abs_tsum_heatKernel1_add_int_sub_one_le {t : ℝ} (ht : 0 < t) (y : ℝ) :
    |(∑' n : ℤ, heatKernel1 t (y + n)) - 1| ≤ thetaError t := by
  set g : ℤ → ℂ := fun k => ((Real.exp (-(4 * Real.pi ^ 2 * t * (k : ℝ) ^ 2)) : ℝ) : ℂ) *
    cexp (2 * Real.pi * I * k * y) with hgdef
  have hgn : ∀ k, ‖g k‖ = Real.exp (-(4 * Real.pi ^ 2 * t * (k : ℝ) ^ 2)) := by
    intro k
    rw [hgdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      show (2 * Real.pi * I * k * y : ℂ) = ((2 * Real.pi * k * y : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hgs : Summable fun k => ‖g k‖ := by
    simp_rw [hgn]; exact summable_thetaTerm ht
  have hg : Summable g := hgs.of_norm
  have hg0 : g 0 = 1 := by simp [hgdef]
  have hsplit := hg.tsum_eq_add_tsum_ite 0
  rw [hg0] at hsplit
  have hite : Summable fun k : ℤ => ‖if k = 0 then (0 : ℂ) else g k‖ := by
    refine hgs.of_nonneg_of_le (fun k => norm_nonneg _) fun k => ?_
    split_ifs <;> simp
  rw [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_sub, Complex.ofReal_one,
    tsum_heatKernel1_add_int ht y]
  change ‖(∑' k, g k) - 1‖ ≤ _
  rw [hsplit, add_sub_cancel_left, thetaError_eq_tsum_ite ht]
  refine (norm_tsum_le_tsum_norm hite).trans (le_of_eq (tsum_congr fun k => ?_))
  split_ifs <;> simp [hgn]

/-- For `t ≥ 1`, `thetaError t ≤ thetaError 1 · exp(-4π²(t - 1))`. -/
theorem thetaError_le_mul_exp {t : ℝ} (ht : 1 ≤ t) :
    thetaError t ≤ thetaError 1 * Real.exp (-(4 * Real.pi ^ 2 * (t - 1))) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  rw [thetaError_eq_tsum_ite ht0, thetaError_eq_tsum_ite one_pos, ← tsum_mul_right]
  have hs1 : Summable fun k : ℤ => (if k = 0 then 0 else
      Real.exp (-(4 * Real.pi ^ 2 * 1 * (k : ℝ) ^ 2))) * Real.exp (-(4 * Real.pi ^ 2 * (t - 1))) := by
    refine Summable.mul_right _ ?_
    refine (summable_thetaTerm one_pos).of_nonneg_of_le
      (fun k => by split_ifs; exacts [le_rfl, (Real.exp_pos _).le]) fun k => ?_
    split_ifs; exacts [(Real.exp_pos _).le, le_rfl]
  refine Summable.tsum_le_tsum (fun k => ?_) ?_ hs1
  · split_ifs with hk
    · simp
    · rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hk1 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by
        have : (1 : ℤ) ≤ k ^ 2 := by
          rcases lt_or_gt_of_ne hk with h | h <;> nlinarith
        exact_mod_cast this
      have hπ : 0 ≤ 4 * Real.pi ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hk1 (mul_nonneg hπ (sub_nonneg.mpr ht))]
  · refine (summable_thetaTerm ht0).of_nonneg_of_le
      (fun k => by split_ifs; exacts [le_rfl, (Real.exp_pos _).le]) fun k => ?_
    split_ifs; exacts [(Real.exp_pos _).le, le_rfl]

/-! ## Products over the lattice -/

/-- The sum over `ℤ^d` of a product of nonnegative summable one-dimensional families. -/
theorem hasSum_prod_pi_int :
    ∀ {d : ℕ} (f : Fin d → ℤ → ℝ) (s : Fin d → ℝ), (∀ i n, 0 ≤ f i n) →
      (∀ i, HasSum (f i) (s i)) → HasSum (fun n : Fin d → ℤ => ∏ i, f i (n i)) (∏ i, s i)
  | 0, f, s, _, _ => by
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    have : (fun _ : Fin 0 → ℤ => (1 : ℝ)) = fun n => if n = (fun i => Fin.elim0 i) then 1 else 0 := by
      funext n
      rw [Subsingleton.elim n (fun i => Fin.elim0 i)]
      simp
    rw [this]
    exact hasSum_ite_eq _ _
  | d + 1, f, s, hf0, hf => by
    have hIH := hasSum_prod_pi_int (fun i : Fin d => f i.succ) (fun i => s i.succ)
      (fun i n => hf0 i.succ n) (fun i => hf i.succ)
    have hnn : ∀ m : Fin d → ℤ, 0 ≤ ∏ i, f i.succ (m i) :=
      fun m => Finset.prod_nonneg fun i _ => hf0 _ _
    have hsum : Summable fun x : ℤ × (Fin d → ℤ) => f 0 x.1 * ∏ i, f i.succ (x.2 i) := by
      have h := summable_mul_of_summable_norm (f := f 0) (g := fun m : Fin d → ℤ => ∏ i, f i.succ (m i))
        ((hf 0).summable.congr fun n => (Real.norm_of_nonneg (hf0 0 n)).symm)
        (hIH.summable.congr fun m => (Real.norm_of_nonneg (hnn m)).symm)
      exact h
    have hmul := (hf 0).mul hIH hsum
    rw [Fin.prod_univ_succ]
    rw [← (Fin.consEquiv fun _ : Fin (d + 1) => ℤ).hasSum_iff]
    convert hmul using 1
    funext x
    simp [Fin.consEquiv, Fin.prod_univ_succ]

/-- `|∏ θᵢ - 1| ≤ (1 + E)^d - 1` when every `|θᵢ - 1| ≤ E`. -/
theorem abs_prod_sub_one_le {θ : Fin d → ℝ} {E : ℝ} (hθ : ∀ i, |θ i - 1| ≤ E) :
    |(∏ i, θ i) - 1| ≤ (1 + E) ^ d - 1 := by
  have key : ∀ s : Finset (Fin d), |(∏ i ∈ s, θ i) - 1| ≤ (1 + E) ^ s.card - 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.card_insert_of_notMem hj, pow_succ]
      have hE : 0 ≤ E := (abs_nonneg _).trans (hθ j)
      have hj1 : |θ j| ≤ 1 + E := by
        have := hθ j
        rw [abs_le] at this ⊢
        constructor <;> linarith [abs_nonneg (θ j)]
      have hP : |∏ i ∈ s, θ i| ≤ (1 + E) ^ s.card := by
        have := abs_sub_abs_le_abs_sub (∏ i ∈ s, θ i) 1
        rw [abs_one] at this
        linarith
      have h1 : θ j * ∏ i ∈ s, θ i - 1 = (θ j - 1) * ∏ i ∈ s, θ i + ((∏ i ∈ s, θ i) - 1) := by
        ring
      rw [h1]
      calc |(θ j - 1) * ∏ i ∈ s, θ i + ((∏ i ∈ s, θ i) - 1)|
          ≤ |θ j - 1| * |∏ i ∈ s, θ i| + |(∏ i ∈ s, θ i) - 1| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ E * (1 + E) ^ s.card + ((1 + E) ^ s.card - 1) := by
            gcongr
            · exact hθ j
        _ = (1 + E) ^ s.card * (1 + E) - 1 := by ring
  simpa using key Finset.univ

/-- **The lattice periodization of the mask** as a product of one-dimensional periodizations. -/
theorem hasSum_heatKernel_add_latticeShift (z x : Vec d) {r : ℝ} (hr : 0 < r) :
    HasSum (fun n : LatticeIndex d => heatKernel z r (x + latticeShift n))
      (∏ i, ∑' m : ℤ, heatKernel1 (r ^ 2) (x i - z i + m)) := by
  have hr2 : 0 < r ^ 2 := by positivity
  have h := hasSum_prod_pi_int (fun i (m : ℤ) => heatKernel1 (r ^ 2) (x i - z i + m))
    (fun i => ∑' m : ℤ, heatKernel1 (r ^ 2) (x i - z i + m))
    (fun i m => by unfold heatKernel1; positivity)
    (fun i => (summable_heatKernel1_add_int hr2 _).hasSum)
  convert h using 1
  funext n
  unfold heatKernel
  rw [euclideanHeatKernel_eq_prodFun hr2, prodFun]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  simp only [Pi.sub_apply, Pi.add_apply, latticeShift]
  ring

/-- **The periodized mask is within `(1 + thetaError r²)^d - 1` of `1`.** -/
theorem abs_tsum_heatKernel_add_latticeShift_sub_one_le (z x : Vec d) {r : ℝ} (hr : 0 < r) :
    |(∑' n : LatticeIndex d, heatKernel z r (x + latticeShift n)) - 1| ≤
      (1 + thetaError (r ^ 2)) ^ d - 1 := by
  rw [(hasSum_heatKernel_add_latticeShift z x hr).tsum_eq]
  exact abs_prod_sub_one_le fun i =>
    abs_tsum_heatKernel1_add_int_sub_one_le (by positivity) _

/-- For `r ≥ 1` the error of the periodization decays like `exp(-4π²(r² - 1))`. -/
theorem periodizationError_le {r : ℝ} (hr : 1 ≤ r) :
    (1 + thetaError (r ^ 2)) ^ d - 1 ≤
      d * (1 + thetaError 1) ^ d * thetaError 1 * Real.exp (-(4 * Real.pi ^ 2 * (r ^ 2 - 1))) := by
  have hr2 : 1 ≤ r ^ 2 := by nlinarith
  have hE0 := thetaError_nonneg (show 0 < r ^ 2 by positivity)
  have hE1 := thetaError_nonneg (t := 1) one_pos
  have hEle := thetaError_le_mul_exp hr2
  have hexp : Real.exp (-(4 * Real.pi ^ 2 * (r ^ 2 - 1))) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    have : 0 ≤ r ^ 2 - 1 := by linarith
    positivity
  have hEleE1 : thetaError (r ^ 2) ≤ thetaError 1 :=
    hEle.trans (mul_le_of_le_one_right hE1 hexp)
  -- mean value bound `(1 + E)^d - 1 ≤ d (1 + E)^(d-1) E ≤ d (1 + E₁)^d E`
  have hmv : ∀ n : ℕ, (1 + thetaError (r ^ 2)) ^ n - 1 ≤
      n * (1 + thetaError 1) ^ n * thetaError (r ^ 2) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : (1 : ℝ) ≤ (1 + thetaError (r ^ 2)) ^ n := one_le_pow₀ (by linarith)
      have h2 : (1 + thetaError (r ^ 2)) ^ n ≤ (1 + thetaError 1) ^ n :=
        pow_le_pow_left₀ (by linarith) (by linarith) n
      have h3 : (1 + thetaError 1) ^ n ≤ (1 + thetaError 1) ^ (n + 1) :=
        pow_le_pow_right₀ (by linarith) (Nat.le_succ n)
      have h4 : 0 ≤ (1 + thetaError 1) ^ n := by positivity
      push_cast
      rw [pow_succ]
      nlinarith [mul_le_mul_of_nonneg_right h2 hE0, mul_le_mul_of_nonneg_right h3 hE0,
        mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ n by positivity)]
  calc (1 + thetaError (r ^ 2)) ^ d - 1 ≤ d * (1 + thetaError 1) ^ d * thetaError (r ^ 2) := hmv d
    _ ≤ d * (1 + thetaError 1) ^ d *
        (thetaError 1 * Real.exp (-(4 * Real.pi ^ 2 * (r ^ 2 - 1)))) := by
        gcongr
    _ = _ := by ring

end QSH
