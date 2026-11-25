import QuantitativeStochasticHomogenization.Ch01.Sec04.Lemma116
import QuantitativeStochasticHomogenization.Ch01.Sec04.Lemma113
import QuantitativeStochasticHomogenization.Ch02.Sec01.DualEnergy
import QuantitativeStochasticHomogenization.AppC.ReverseHolder

/-!
# Proposition 1.15: weak convergence of the energy densities

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Proposition 1.15: for `q ∈ [1, d/(d-1))` there is `C(q, d, Λ)` such that, for every `m ∈ ℕ` and
`p ∈ B₁`, the energy density of the minimizer `v(·, □_m, p)` satisfies
`3^{-2m} ‖½ ∇v · a∇v - ½ p · āp‖_{W̲^{-2,q}(□_m)} ≤ C (3^{-2m} + E(m))^{1/2}`.

The book prints the right side `C 3^{-2m} + C E(m)` in (1.53); its proof, Proposition 1.10,
Lemma 1.13 and Lemma 1.16 combined, gives the square root of that quantity, which is what is proved
here (see CORRESPONDENCE.md).

The proof applies the div-curl lemma (`lemma_1_16_quantitative`) on `□_m` (diameter `√d 3^m`,
`|□_m| = (√d)^{-d} (√d 3^m)^d`) to `u₁ = v = ℓ_p + u`, `g₁ = a∇v` (solenoidal by the first variation
(1.12)), `u₂ = ℓ_p`, `g₂ = āp`, and bounds `‖a∇v - āp‖_{H̲^{-1}(□_m)}` and
`‖v - ℓ_p‖_{L̲²(□_m)} ≤ C ‖∇v - p‖_{H̲^{-1}(□_m)}` by Proposition 1.10 and (1.45).
-/

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- `‖c f‖_{W̲^{-2,q}(U)} ≤ |c| ‖f‖_{W̲^{-2,q}(U)}`. -/
theorem negativeSobolevTwoNorm_const_mul_le (q : ℝ≥0∞) (U : Set (Vec d)) (f : Vec d → ℝ)
    (c : ℝ) :
    negativeSobolevTwoNorm q U (fun x => c * f x) ≤
      ENNReal.ofReal |c| * negativeSobolevTwoNorm q U f := by
  refine negativeSobolevTwoNorm_le fun ψ hψ hψ1 => ?_
  have hI : ∫ x in U, c * f x * ψ x = c * ∫ x in U, f x * ψ x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  have h : ⨍ x in U, c * f x * ψ x = c * ⨍ x in U, f x * ψ x := by
    rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul, hI]
    ring
  rw [h, abs_mul, ENNReal.ofReal_mul (abs_nonneg c)]
  exact mul_le_mul' le_rfl (ofReal_abs_setAverage_le_negativeSobolevTwoNorm hψ hψ1)

theorem euclideanSq_nonneg_of_vec (x : Vec d) : 0 ≤ euclideanSq x := by
  unfold euclideanSq dot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-- The normalized `L²(U)` norm of `|G|` is the root mean square `vectorRms`. -/
theorem eLpMeanNormOn_two_euclideanNorm_eq_vectorRms {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    {G : Vec d → Vec d} (hG : MemLp G 2 (volume.restrict U)) :
    PDE.eLpMeanNormOn U 2 (fun x => euclideanNorm (G x)) =
      ENNReal.ofReal (vectorRms volume U G) := by
  rw [eLpMeanNormOn_two_eq_ofReal_scalarRms hU0 (memLp_two_euclideanNorm hG), scalarRms, vectorRms]
  have h : ∀ x, euclideanNorm (G x) ^ 2 = euclideanSq (G x) := fun x =>
    Real.sq_sqrt (euclideanSq_nonneg_of_vec _)
  simp_rw [h]

/-- The normalized `H^{-1}(U)` norm is at most the normalized `Ĥ^{-1}(U)` norm, (0.32). -/
theorem negativeSobolevOneNorm_two_zero_le_hatNegativeSobolevNorm {U : Set (Vec d)}
    (hU0 : volume U ≠ 0) (hUt : volume U ≠ ⊤) (f : Vec d → ℝ) :
    negativeSobolevOneNorm 2 U f 0 ≤ hatNegativeSobolevNorm U f := by
  have hq : ENNReal.ofReal ((2 : ℝ) / (2 - 1)) = 2 := by norm_num
  refine iSup_le fun ⟨ψ, hψ, hψ1⟩ => ?_
  rw [hq] at hψ1
  have hH1 : H1 U ψ (gradient ψ) := hψ.h01.h1
  have hnorm : h1Norm U ψ (gradient ψ) ≤ 1 := by
    refine le_trans ?_ hψ1
    unfold h1Norm sobolevOneTestNorm
    have e1 : scalarRms volume U ψ = (PDE.eLpMeanNormOn U 2 ψ).toReal := by
      rw [eLpMeanNormOn_two_eq_ofReal_scalarRms hU0 hH1.1,
        ENNReal.toReal_ofReal (show 0 ≤ scalarRms volume U ψ from Real.sqrt_nonneg _)]
    have hfin : ∀ i, PDE.eLpMeanNormOn U 2 (coordinateDerivative i ψ) ≠ ⊤ := fun i =>
      eLpMeanNormOn_ne_top_of_memLp hU0 hUt (hH1.2.1.eval i)
    have e2 : vectorRms volume U (gradient ψ) ≤
        ∑ i, (PDE.eLpMeanNormOn U 2 (coordinateDerivative i ψ)).toReal := by
      have h := eLpMeanNormOn_two_euclideanNorm_eq_vectorRms hU0 hH1.2.1
      rw [← ENNReal.toReal_ofReal (show 0 ≤ vectorRms volume U (gradient ψ) from Real.sqrt_nonneg _),
        ← h,
        ← ENNReal.toReal_sum fun i _ => hfin i]
      exact ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun i _ => hfin i)
        (eLpNorm_euclideanNorm_le_sum one_le_two (hH1.2.1.aestronglyMeasurable.smul_measure _))
    rw [e1]
    linarith
  have hp : distributionPairing U f 0 ψ = ⨍ x in U, f x * ψ x := by
    unfold distributionPairing
    simp [dot]
  rw [hp]
  exact le_iSup (fun v : {v : (Vec d → ℝ) × (Vec d → Vec d) // H1 U v.1 v.2 ∧
      h1Norm U v.1 v.2 ≤ 1} => ENNReal.ofReal |⨍ x in U, f x * v.1.1 x ∂volume|)
    ⟨(ψ, gradient ψ), hH1, hnorm⟩

theorem vectorNegativeSobolevOneNorm_two_le_vectorHat {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hUt : volume U ≠ ⊤) (G : Vec d → Vec d) :
    vectorNegativeSobolevOneNorm 2 U G ≤ vectorHatNegativeSobolevNorm U G :=
  Finset.sum_le_sum fun _ _ =>
    negativeSobolevOneNorm_two_zero_le_hatNegativeSobolevNorm hU0 hUt _

/-- `|āv|² ≤ Λ² |v|²`. -/
theorem euclideanSq_homogenizedMatrix_mulVec_le {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hΛ : 0 ≤ Λ) (v : Vec d) :
    euclideanSq ((homogenizedMatrix P).mulVec v) ≤ Λ ^ 2 * euclideanSq v := by
  set A := homogenizedMatrix P
  have hpos : ∀ u : Vec d, 0 ≤ dot u (A.mulVec u) := fun u => by
    have h := limitDirichletEnergy_eq_homogenizedMatrix hP hΛ u
    have := limitDirichletEnergy_nonneg P u
    linarith
  have hup : ∀ u : Vec d, dot u (A.mulVec u) ≤ Λ * euclideanSq u := fun u => by
    have h := limitDirichletEnergy_eq_homogenizedMatrix hP hΛ u
    have := limitDirichletEnergy_le hP hΛ u
    linarith
  have hcs := sq_dot_mulVec_le (homogenizedMatrix_transpose hP hΛ) hpos v (A.mulVec v)
  change euclideanSq (A.mulVec v) ^ 2 ≤ _ at hcs
  have h1 := hup (A.mulVec v)
  have h2 := hup v
  have h3 := hpos (A.mulVec v)
  have h4 := hpos v
  have h5 : dot (A.mulVec v) (A.mulVec (A.mulVec v)) * dot v (A.mulVec v) ≤
      (Λ * euclideanSq (A.mulVec v)) * (Λ * euclideanSq v) :=
    mul_le_mul h1 h2 h4 (h3.trans h1)
  have hS : 0 ≤ euclideanSq (A.mulVec v) := euclideanSq_nonneg_of_vec _
  rcases hS.eq_or_lt with h0 | hlt
  · rw [← h0]
    exact mul_nonneg (sq_nonneg _) (euclideanSq_nonneg_of_vec _)
  · have h6 : euclideanSq (A.mulVec v) * euclideanSq (A.mulVec v) ≤
        (Λ ^ 2 * euclideanSq v) * euclideanSq (A.mulVec v) := by nlinarith
    exact le_of_mul_le_mul_right h6 hlt

/-- A constant field is solenoidal on a set of finite measure. -/
theorem isL2Sol_const {U : Set (Vec d)} (hU : volume U ≠ ⊤) (c : Vec d) :
    IsL2Sol U (fun _ => c) := by
  have := isFiniteMeasure_restrict.mpr hU
  refine ⟨memLp_const c, fun i => locallyIntegrableOn_const _, locallyIntegrableOn_zero,
    fun φ hφ => ?_⟩
  simp only [zero_mul, integral_zero, neg_zero]
  have hφ1 := hφ.h01
  simp only [dot]
  rw [integral_finsetSum _ fun i _ => ((hφ1.2.1.eval i).integrable one_le_two).const_mul (c i)]
  exact Finset.sum_eq_zero fun i _ => by
    rw [integral_const_mul, show (∫ x in U, gradient φ x i) = 0 from
      setIntegral_eq_zero_of_H01 hU hφ1 i, mul_zero]

/-- The flux `a(p + ∇u)` of a minimizer is solenoidal, by the first variation (1.12). -/
theorem IsDirichletMinimizer.isL2Sol {a : CoefficientField d Λ} {U : Set (Vec d)}
    (hU : volume U ≠ ⊤) {e : Vec d} {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hmin : IsDirichletMinimizer a U e u g) :
    IsL2Sol U (fun x => (a x).mulVec (e + g x)) := by
  have := isFiniteMeasure_restrict.mpr hU
  have hEG : MemLp (fun x => e + g x) 2 (volume.restrict U) := (memLp_const e).add hmin.1.2.1
  refine ⟨memLp_pi_iff.2 fun i => memLp_coefficient_mulVec_apply a hEG i,
    hasWeakDivergence_of_setIntegral_dot_eq_zero a hU hEG fun w h hw =>
      hmin.integral_dot_eq_zero hU hw⟩

/-- From `r X² ≤ B` with `r > 0`: `X ≤ √(B / r)`. -/
theorem le_ofReal_sqrt_of_mul_sq_le {X : ℝ≥0∞} {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    (h : ENNReal.ofReal r * X ^ 2 ≤ ENNReal.ofReal B) : X ≤ ENNReal.ofReal (Real.sqrt (B / r)) := by
  have hX : X ≠ ⊤ := by
    rintro rfl
    rw [ENNReal.top_pow two_ne_zero, ENNReal.mul_top (by simpa using hr)] at h
    exact ENNReal.ofReal_ne_top (top_le_iff.1 h)
  rw [← ENNReal.ofReal_toReal hX] at h ⊢
  rw [← ENNReal.ofReal_pow ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul hr.le,
    ENNReal.ofReal_le_ofReal_iff hB] at h
  refine ENNReal.ofReal_le_ofReal ((abs_of_nonneg ENNReal.toReal_nonneg).symm.le.trans (Real.abs_le_sqrt ?_))
  rw [le_div_iff₀ hr]
  linarith

/-- **Proposition 1.15**, in the form given by its proof: for `d ≥ 2` and `q ∈ [1, d/(d-1))`
there is `C(q, d, Λ)` such that, for every `m ∈ ℕ`, `p ∈ B₁` and minimizer
`v(·, □_m, p) = ℓ_p + u` of gradient `p + g`,
`3^{-2m} ‖½ ∇v · a∇v - ½ p · āp‖_{W̲^{-2,q}(□_m)} ≤ C (3^{-2m} + E(m))^{1/2}`, with `E(m)` of
(1.39). -/
theorem proposition_1_15 (hd : 2 ≤ d) {q : ℝ} (hq : 1 ≤ q) (hqd : q < d / (d - 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : Measure (CoefficientField d Λ)), LawHypotheses P →
      ∀ (m : ℕ) (a : CoefficientField d Λ) (e : Vec d), e ∈ originBall d 1 →
      ∀ (u : Vec d → ℝ) (g : Vec d → Vec d), IsDirichletMinimizer a (triadicCube d m) e u g →
        ENNReal.ofReal (((3 : ℝ) ^ m)⁻¹ ^ 2) *
            negativeSobolevTwoNorm (ENNReal.ofReal q) (triadicCube d m)
              (fun x => (1 / 2 : ℝ) * dot (e + g x) ((a x).mulVec (e + g x)) -
                (1 / 2 : ℝ) * dot e ((homogenizedMatrix P).mulVec e)) ≤
          ENNReal.ofReal (C * Real.sqrt (((3 : ℝ) ^ m)⁻¹ ^ 2 + coarseDeviation P m a)) := by
  have : NeZero d := ⟨by omega⟩
  by_cases hΛ1 : 1 ≤ Λ
  swap
  · exact ⟨0, le_rfl, fun P _ m a => absurd (one_le_of_coefficientField a) hΛ1⟩
  have hΛ : 0 ≤ Λ := zero_le_one.trans hΛ1
  have hd0 : (0 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt d := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; exact Real.sqrt_pos.2 hd0
  obtain ⟨C16, hC16, h16⟩ := lemma_1_16_quantitative hd hq hqd (κ := (s ^ d)⁻¹) (by positivity)
  obtain ⟨C10, hC10, h10⟩ := proposition_1_10 (d := d) (Λ := Λ)
  obtain ⟨C13, hC13, h13⟩ := lemma_1_13 (d := d)
  obtain ⟨K, hK⟩ : ∃ K : ℝ,
      K = C16 * s * Real.sqrt C10 * (Real.sqrt Λ + Λ * C13) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨1 / 2 * K, by positivity, fun P hP m a e he u g hmin => ?_⟩
  have hW0 := volume_triadicCube_ne_zero d m
  have hWt := volume_triadicCube_ne_top d m
  have : IsFiniteMeasure (volume.restrict (triadicCube d m)) := isFiniteMeasure_restrict.mpr hWt
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ((3 : ℝ) ^ m)⁻¹ ^ 2 := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr3 : r * ((3 : ℝ) ^ m) ^ 2 = 1 := by rw [hr, inv_pow, inv_mul_cancel₀ (by positivity)]
  set E := coarseDeviation P m a with hEdef
  have hE0 : 0 ≤ E := sq_nonneg _
  -- the geometry of `□_m`
  set D : ℝ := s * (3 : ℝ) ^ m with hD
  have hUo : IsOpen (triadicCube d m) := isOpen_triadicCube m
  have hUc : Convex ℝ (triadicCube d m) := by
    unfold triadicCube
    exact convex_pi fun _ _ => convex_Ioo _ _
  have hUb : Bornology.IsBounded (triadicCube d m) := by
    unfold triadicCube
    exact Bornology.IsBounded.pi fun _ => Metric.isBounded_Ioo _ _
  have hUne : (triadicCube d m).Nonempty := by
    refine ⟨0, ?_⟩
    unfold triadicCube
    exact fun i _ => ⟨by simp only [Pi.zero_apply]; linarith, by simp only [Pi.zero_apply]; linarith⟩
  have hUD : ∀ x ∈ triadicCube d m, ∀ y ∈ triadicCube d m, euclideanNorm (x - y) ≤ D := by
    intro x hx y hy
    rw [euclideanNorm_eq_vecEuclideanNorm, hD, hs]
    refine (PDE.vecEuclideanNorm_le_sqrt_natCast_mul_norm _).trans
      (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
    refine (pi_norm_le_iff_of_nonneg h3.le).2 fun i => ?_
    have h1 := hx i (Set.mem_univ i)
    have h2 := hy i (Set.mem_univ i)
    rw [Real.norm_eq_abs, Pi.sub_apply, abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hvol : ENNReal.ofReal ((s ^ d)⁻¹ * D ^ d) ≤ volume (triadicCube d m) := by
    rw [volume_triadicCube, ← ENNReal.ofReal_pow h3.le, hD, mul_pow, inv_mul_cancel_left₀
      (by positivity)]
  -- the div-curl lemma
  have hu1 : H1 (triadicCube d m) (fun x => dot e x + u x) (fun x => e + g x) :=
    (H1.linear hUb e).add hmin.1.h1
  have hu2 : H1 (triadicCube d m) (fun x => dot e x) (fun _ => e) := H1.linear hUb e
  have hL := h16 (triadicCube d m) D hUo hUc hUne (by positivity) hUD hvol _ _ _ _ _ _ hu1 hu2
    (hmin.isL2Sol hWt) (isL2Sol_const hWt ((homogenizedMatrix P).mulVec e))
  -- the bounds of Proposition 1.10 and (1.45)
  have h10' := h10 P hP m a e he u g hmin
  rw [← hr] at h10'
  set B := C10 * r + C10 * E with hB
  have hB0 : 0 ≤ B := by positivity
  have hsq : Real.sqrt (B / r) = (3 : ℝ) ^ m * (Real.sqrt C10 * Real.sqrt (r + E)) := by
    have : B / r = ((3 : ℝ) ^ m) ^ 2 * (C10 * (r + E)) := by
      rw [hB, div_eq_iff hr0.ne']
      linear_combination (-(C10 * (r + E))) * hr3
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq h3.le, Real.sqrt_mul hC10]
  set X : ℝ := (3 : ℝ) ^ m * (Real.sqrt C10 * Real.sqrt (r + E)) with hX
  have hX0 : 0 ≤ X := by positivity
  have hHg : vectorHatNegativeSobolevNorm (triadicCube d m) g ≤ ENNReal.ofReal X := by
    rw [← hsq]
    exact le_ofReal_sqrt_of_mul_sq_le hr0 hB0 (le_trans le_self_add h10')
  have hHf : vectorHatNegativeSobolevNorm (triadicCube d m)
      (fun x => (a x).mulVec (e + g x) - (homogenizedMatrix P).mulVec e) ≤ ENNReal.ofReal X := by
    rw [← hsq]
    exact le_ofReal_sqrt_of_mul_sq_le hr0 hB0 (le_trans le_add_self h10')
  have he1 := euclideanSq_le_one_of_mem_originBall he
  have hEG : MemLp (fun x => e + g x) 2 (volume.restrict (triadicCube d m)) :=
    (memLp_const e).add hmin.1.2.1
  have hN1 : PDE.eLpMeanNormOn (triadicCube d m) 2 (fun x => euclideanNorm (e + g x)) ≤
      ENNReal.ofReal (Real.sqrt Λ) := by
    rw [eLpMeanNormOn_two_euclideanNorm_eq_vectorRms hW0 hEG, vectorRms]
    refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_)
    exact (hmin.setAverage_euclideanSq_le hW0 hWt).trans (mul_le_of_le_one_right hΛ he1)
  have hNg : PDE.eLpMeanNormOn (triadicCube d m) 2
      (fun _ => euclideanNorm ((homogenizedMatrix P).mulVec e)) ≤ ENNReal.ofReal Λ := by
    rw [eLpMeanNormOn_two_euclideanNorm_eq_vectorRms hW0 (memLp_const _), vectorRms,
      setAverage_const hW0 hWt]
    refine ENNReal.ofReal_le_ofReal ((Real.sqrt_le_sqrt
      ((euclideanSq_homogenizedMatrix_mulVec_le hP hΛ e).trans
        (mul_le_of_le_one_right (sq_nonneg Λ) he1))).trans (le_of_eq (Real.sqrt_sq hΛ)))
  have hNu : PDE.eLpMeanNormOn (triadicCube d m) 2 (fun x => (dot e x + u x) - dot e x) ≤
      ENNReal.ofReal C13 * ENNReal.ofReal X := by
    have e1 : (fun x => (dot e x + u x) - dot e x) = u := by
      funext x
      ring
    rw [e1, eLpMeanNormOn_two_eq_ofReal_scalarRms hW0 hmin.1.1]
    exact ((h13 m u g).2 hmin.1).trans (mul_le_mul' le_rfl hHg)
  have hV := vectorNegativeSobolevOneNorm_two_le_vectorHat hW0 hWt
    (fun x => (a x).mulVec (e + g x) - (homogenizedMatrix P).mulVec e)
  have hf : negativeSobolevTwoNorm (ENNReal.ofReal q) (triadicCube d m)
      (fun x => dot (e + g x) ((a x).mulVec (e + g x)) -
        dot e ((homogenizedMatrix P).mulVec e)) ≤
      ENNReal.ofReal (C16 * D * (Real.sqrt Λ * X + Λ * (C13 * X))) := by
    refine hL.trans (le_trans (mul_le_mul' le_rfl (add_le_add (mul_le_mul' hN1 (hV.trans hHf))
      (mul_le_mul' hNg hNu))) (le_of_eq ?_))
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C16 * D),
      ENNReal.ofReal_add (mul_nonneg (Real.sqrt_nonneg Λ) hX0)
        (mul_nonneg hΛ (mul_nonneg hC13 hX0)),
      ENNReal.ofReal_mul (Real.sqrt_nonneg Λ), ENNReal.ofReal_mul hΛ, ENNReal.ofReal_mul hC13]
  have hw : (fun x => (1 / 2 : ℝ) * dot (e + g x) ((a x).mulVec (e + g x)) -
      (1 / 2 : ℝ) * dot e ((homogenizedMatrix P).mulVec e)) =
      fun x => (1 / 2 : ℝ) * (dot (e + g x) ((a x).mulVec (e + g x)) -
        dot e ((homogenizedMatrix P).mulVec e)) := by
    funext x
    ring
  rw [hw, ← hr]
  calc ENNReal.ofReal r * negativeSobolevTwoNorm (ENNReal.ofReal q) (triadicCube d m)
        (fun x => (1 / 2 : ℝ) * (dot (e + g x) ((a x).mulVec (e + g x)) -
          dot e ((homogenizedMatrix P).mulVec e)))
      ≤ ENNReal.ofReal r * (ENNReal.ofReal |1 / 2| *
          ENNReal.ofReal (C16 * D * (Real.sqrt Λ * X + Λ * (C13 * X)))) :=
        mul_le_mul' le_rfl ((negativeSobolevTwoNorm_const_mul_le _ _ _ _).trans
          (mul_le_mul' le_rfl hf))
    _ = ENNReal.ofReal (1 / 2 * K * Real.sqrt (r + E)) := by
        rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul hr0.le]
        congr 1
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), hK, hX, hD]
        have : r * ((3 : ℝ) ^ m * (3 : ℝ) ^ m) = 1 := by rw [← sq]; exact hr3
        linear_combination (1 / 2 * C16 * s * Real.sqrt C10 * (Real.sqrt Λ + Λ * C13) *
          Real.sqrt (r + E)) * this

end QSH
