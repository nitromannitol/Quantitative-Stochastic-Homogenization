import QuantitativeStochasticHomogenization.Ch01.Sec04.CubePoincare

/-!
# The average flux of the minimizer

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.4, Step 1 of the proof of Proposition 1.10, (1.49): for the minimizer
`v(·, U, p) = ℓ_p + u` of (1.8), `⨍_U a∇v(·, U, p) = a(U) p`, tested against every `q ∈ ℝ^d`
(`IsDirichletMinimizer.setAverage_flux_eq`). The book polarizes
`⨍_U ∇v(·, U, q)·a∇v(·, U, p) = q·a(U)p` and uses the first variation. Here the gradient `g` of the
minimizer for `p` is a trial gradient for `p + tq`, so
`μ(U, p + tq) ≤ μ(U, p) + t ⨍_U q·a(p + g) + t² ⨍_U ½ q·aq` for every `t ∈ ℝ`; comparing with
`μ(U, p + tq) = ½ (p + tq)·a(U)(p + tq)` and letting `t → 0` gives the claim.

Also: `|a(x)ξ| ≤ Λ|ξ|` (`euclideanSq_coefficient_mulVec_le`), from the Cauchy–Schwarz inequality for
the form `ξ·a(x)η`, and the flux of an `L²` field is in `L²` (`memLp_coefficient_mulVec_apply`).
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- The Cauchy–Schwarz inequality `(w·Av)² ≤ (w·Aw)(v·Av)` for a symmetric positive semidefinite
matrix. -/
theorem sq_dot_mulVec_le {A : Mat d} (hA : A.transpose = A)
    (hpos : ∀ v : Vec d, 0 ≤ dot v (A.mulVec v)) (v w : Vec d) :
    dot w (A.mulVec v) ^ 2 ≤ dot w (A.mulVec w) * dot v (A.mulVec v) := by
  have hs := dot_mulVec_comm_of_symm hA v w
  have key : ∀ t : ℝ, 0 ≤ dot v (A.mulVec v) * (t * t) + (2 * dot w (A.mulVec v)) * t +
      dot w (A.mulVec w) := by
    intro t
    have h := hpos (w + t • v)
    rw [dot_add_mulVec_add_eq hA w (t • v)] at h
    simp only [dot_eq_dotProduct, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul] at h hs ⊢
    rw [hs] at h
    linarith
  have hd := discrim_le_zero key
  simp only [discrim] at hd
  nlinarith

/-- **`|a(x)ξ| ≤ Λ|ξ|`.** -/
theorem euclideanSq_coefficient_mulVec_le (a : CoefficientField d Λ) (x v : Vec d) :
    euclideanSq ((a x).mulVec v) ≤ Λ ^ 2 * euclideanSq v := by
  have hpos : ∀ u : Vec d, 0 ≤ dot u ((a x).mulVec u) := fun u =>
    (euclideanSq_nonneg u).trans (a.elliptic x u).1
  have hcs := sq_dot_mulVec_le (a.symmetric x) hpos v ((a x).mulVec v)
  change euclideanSq ((a x).mulVec v) ^ 2 ≤ _ at hcs
  have h1 := (a.elliptic x ((a x).mulVec v)).2
  have h2 := (a.elliptic x v).2
  have h3 := hpos ((a x).mulVec v)
  have h4 := hpos v
  have h5 : dot ((a x).mulVec v) ((a x).mulVec ((a x).mulVec v)) * dot v ((a x).mulVec v) ≤
      (Λ * euclideanSq ((a x).mulVec v)) * (Λ * euclideanSq v) :=
    mul_le_mul h1 h2 h4 (h3.trans h1)
  have hS : 0 ≤ euclideanSq ((a x).mulVec v) := euclideanSq_nonneg _
  rcases hS.eq_or_lt with h0 | hlt
  · rw [← h0]
    exact mul_nonneg (sq_nonneg _) (euclideanSq_nonneg _)
  · have h6 : euclideanSq ((a x).mulVec v) * euclideanSq ((a x).mulVec v) ≤
        (Λ ^ 2 * euclideanSq v) * euclideanSq ((a x).mulVec v) := by nlinarith
    exact le_of_mul_le_mul_right h6 hlt

theorem euclideanNorm_le_sum_abs (v : Vec d) : euclideanNorm v ≤ ∑ j, |v j| := by
  rw [euclideanNorm, Real.sqrt_le_iff]
  refine ⟨Finset.sum_nonneg fun j _ => abs_nonneg _, ?_⟩
  have h := sum_sq_le_sq_sum_of_nonneg Finset.univ (fun j => |v j|) fun j _ => abs_nonneg _
  simp only [sq_abs] at h
  simpa [euclideanSq, dot, pow_two] using h

/-- **The flux of an `L²` field is in `L²`.** -/
theorem memLp_coefficient_mulVec_apply (a : CoefficientField d Λ) {U : Set (Vec d)}
    {h : Vec d → Vec d} (hh : MemLp h 2 (volume.restrict U)) (i : Fin d) :
    MemLp (fun x => (a x).mulVec (h x) i) 2 (volume.restrict U) := by
  have hmeas : AEStronglyMeasurable (fun x => (a x).mulVec (h x) i) (volume.restrict U) := by
    have e : (fun x => (a x).mulVec (h x) i) = fun x => ∑ j, a x i j * h x j := by
      funext x
      simp [Matrix.mulVec, dotProduct]
    rw [e]
    exact Finset.aestronglyMeasurable_fun_sum Finset.univ fun j _ =>
      ((a.locally_integrable i j).aestronglyMeasurable.restrict).mul (hh.eval j).aestronglyMeasurable
  have hg : MemLp (fun x => |Λ| * ∑ j, ‖h x j‖) 2 (volume.restrict U) :=
    (memLp_finsetSum Finset.univ fun j _ => (hh.eval j).norm).const_mul |Λ|
  refine hg.of_le hmeas (Eventually.of_forall fun x => ?_)
  have hn : 0 ≤ |Λ| * ∑ j, ‖h x j‖ :=
    mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun j _ => norm_nonneg _)
  rw [Real.norm_of_nonneg hn, Real.norm_eq_abs]
  have e1 := abs_coord_le_euclideanNorm ((a x).mulVec (h x)) i
  have e2 : euclideanNorm ((a x).mulVec (h x)) ≤ |Λ| * euclideanNorm (h x) := by
    rw [euclideanNorm, euclideanNorm, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt (euclideanSq_coefficient_mulVec_le a x (h x))
  have e3 := euclideanNorm_le_sum_abs (h x)
  simp only [Real.norm_eq_abs]
  calc |(a x).mulVec (h x) i| ≤ euclideanNorm ((a x).mulVec (h x)) := e1
    _ ≤ |Λ| * euclideanNorm (h x) := e2
    _ ≤ |Λ| * ∑ j, |h x j| := mul_le_mul_of_nonneg_left e3 (abs_nonneg _)

/-- **(1.49)**: the average flux of the minimizer `v(·, U, p) = ℓ_p + u`,
`⨍_U q·a(p + g) = q·a(U)p` for every `q ∈ ℝ^d`. -/
theorem IsDirichletMinimizer.setAverage_flux_eq [NeZero d] {a : CoefficientField d Λ}
    {U : Set (Vec d)} (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤) {e : Vec d} {u : Vec d → ℝ}
    {g : Vec d → Vec d} (hmin : IsDirichletMinimizer a U e u g) (q : Vec d) :
    ⨍ x in U, dot q ((a x).mulVec (e + g x)) = dot q ((coarseMatrix a U).mulVec e) := by
  have hΛ : 0 ≤ Λ := zero_le_one.trans (one_le_of_coefficientField a)
  have := isFiniteMeasure_restrict.mpr hU
  have hV : 0 < volume.real U := ENNReal.toReal_pos hU0 hU
  have hAs : (coarseMatrix a U).transpose = coarseMatrix a U := coarseMatrix_transpose a hU
  have hI0 : ∫ x in U, (1 / 2 : ℝ) * dot (e + g x) ((a x).mulVec (e + g x)) =
      volume.real U * ((1 / 2 : ℝ) * dot e ((coarseMatrix a U).mulVec e)) := by
    have h := hmin.2
    rw [trialEnergy_eq, dirichletEnergy_eq_coarseMatrix a hU0 hU hΛ e] at h
    rw [← h, mul_inv_cancel_left₀ hV.ne']
  have key : ∀ t : ℝ, 0 ≤ ((∫ x in U, (1 / 2 : ℝ) * dot q ((a x).mulVec q)) -
      volume.real U * ((1 / 2 : ℝ) * dot q ((coarseMatrix a U).mulVec q))) * (t * t) +
      ((∫ x in U, dot q ((a x).mulVec (e + g x))) -
        volume.real U * dot q ((coarseMatrix a U).mulVec e)) * t + 0 := by
    intro t
    have hle := dirichletEnergy_le_of_H01 a (e + t • q) hmin.1
    rw [trialEnergy_eq, dirichletEnergy_eq_coarseMatrix a hU0 hU hΛ] at hle
    have hexp := integral_energy_add a hU e hmin.1.2.1
      (memLp_const (t • q) : MemLp (fun _ : Vec d => t • q) 2 (volume.restrict U))
    have e1 : ∫ x in U, (1 / 2 : ℝ) * dot (e + t • q + g x) ((a x).mulVec (e + t • q + g x)) =
        ∫ x in U, (1 / 2 : ℝ) * dot (e + (g x + t • q)) ((a x).mulVec (e + (g x + t • q))) := by
      congr 1
      funext x
      rw [show e + t • q + g x = e + (g x + t • q) by abel]
    have e2 : ∫ x in U, dot (t • q) ((a x).mulVec (e + g x)) =
        t * ∫ x in U, dot q ((a x).mulVec (e + g x)) := by
      rw [← integral_const_mul]
      congr 1
      funext x
      simp only [dot_eq_dotProduct, smul_dotProduct, smul_eq_mul]
    have e3 : ∫ x in U, (1 / 2 : ℝ) * dot (t • q) ((a x).mulVec (t • q)) =
        t * t * ∫ x in U, (1 / 2 : ℝ) * dot q ((a x).mulVec q) := by
      rw [← integral_const_mul]
      congr 1
      funext x
      simp only [dot_eq_dotProduct, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
        smul_eq_mul]
      ring
    have e4 : dot (e + t • q) ((coarseMatrix a U).mulVec (e + t • q)) =
        dot e ((coarseMatrix a U).mulVec e) + 2 * t * dot q ((coarseMatrix a U).mulVec e) +
          t * t * dot q ((coarseMatrix a U).mulVec q) := by
      rw [dot_add_mulVec_add_eq hAs e (t • q)]
      simp only [dot_eq_dotProduct, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
        smul_eq_mul]
      ring
    rw [e1, hexp, hI0, e2, e3, e4] at hle
    have h2 := mul_le_mul_of_nonneg_left hle hV.le
    rw [mul_inv_cancel_left₀ hV.ne'] at h2
    linarith
  have hd := discrim_le_zero key
  simp only [discrim] at hd
  have hz : (∫ x in U, dot q ((a x).mulVec (e + g x))) -
      volume.real U * dot q ((coarseMatrix a U).mulVec e) = 0 := by
    nlinarith [sq_nonneg ((∫ x in U, dot q ((a x).mulVec (e + g x))) -
      volume.real U * dot q ((coarseMatrix a U).mulVec e))]
  rw [setAverage_eq, smul_eq_mul, sub_eq_zero.mp hz, inv_mul_cancel_left₀ hV.ne']

end QSH
