import QuantitativeStochasticHomogenization.Ch04.Sec04.MinimizerComparison
import QuantitativeStochasticHomogenization.Ch04.Sec04.LocalCoefficientRepresentative

/-!
# Corrected coordinates as competitors in the coordinate minimization

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.21: the corrected coordinate `x ↦ (x - z)_i + φ_{e_i}(x) - c` restricted to
`B_T(z)` is an `a`-harmonic function on the ball, with gradient `e_i + ∇φ_{e_i}`. When its
normalized gradient norm on `B_T(z)` is at most `C₀` it is an admissible competitor, and the
selected coordinate minimizer `w_i` satisfies `I[w_i - h] ≤ 4 I[φ_{e_i} - c]`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

theorem ball_subset_originBall' (z : Vec d) (T : ℝ) :
    ball z T ⊆ ball 0 (euclideanNorm z + |T| + 1) := by
  intro y hy
  show euclideanNorm (y - 0) < _
  rw [sub_zero]
  have h1 := euclideanNorm_add_le (y - z) z
  rw [sub_add_cancel] at h1
  have h2 : euclideanNorm (y - z) < T := hy
  have h3 : T ≤ |T| := le_abs_self T
  linarith

theorem fderiv_coordinate_sub (z : Vec d) (i : Fin d) (c : ℝ) (x : Vec d) (k : Fin d) :
    (fderiv ℝ (fun x : Vec d => (x - z) i - c) x) (unitVector k) = unitVector k i := by
  have h : (fun x : Vec d => (x - z) i - c) =
      fun x => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) x - (z i + c) := by
    funext x; simp; ring
  rw [h, fderiv_sub_const, ContinuousLinearMap.fderiv]
  rfl

/-- **The corrected coordinate** `(x - z)_i + φ(x) - c` as a local `a`-harmonic function on
`B_T(z)`, for a whole-space solution `φ` of `-∇·a(e_i + ∇φ) = 0` with locally square integrable
potential and gradient. -/
def correctedCoordinate (a : CoefficientField d Λ) (z : Vec d) (T : ℝ) (i : Fin d) (c : ℝ)
    (φ : Vec d → ℝ) (g : Vec d → Vec d) (hφg : HasWeakGradient Set.univ φ g)
    (hloc : ∀ R : ℝ, 0 < R → MemLp φ 2 (volume.restrict (ball 0 R)) ∧
      MemLp g 2 (volume.restrict (ball 0 R)))
    (harm : HasWeakDivergence Set.univ (fun x => (a x).mulVec (unitVector i + g x))
      (fun _ => 0)) : LocalHarmonic a z T where
  potential := fun x => (x - z) i + φ x - c
  grad := fun x => unitVector i + g x
  square_integrable := by
    have hR : 0 < euclideanNorm z + |T| + 1 := by
      have := euclideanNorm_nonneg z; have := abs_nonneg T; linarith
    have hφ := (hloc _ hR).1.mono_measure
      (Measure.restrict_mono (ball_subset_originBall' z T) le_rfl)
    have hℓ := memLp_coordinate z T i
    exact (hℓ.add hφ).sub (memLp_const c)
  gradient_square_integrable := by
    have hR : 0 < euclideanNorm z + |T| + 1 := by
      have := euclideanNorm_nonneg z; have := abs_nonneg T; linarith
    have hg := (hloc _ hR).2.mono_measure
      (Measure.restrict_mono (ball_subset_originBall' z T) le_rfl)
    have hsum := (memLp_const (μ := ballMeasure z T) (p := 2) (unitVector i)).add hg
    have hmeas : AEStronglyMeasurable (fun x => euclideanNorm (unitVector i + g x))
        (ballMeasure z T) :=
      continuous_euclideanNorm.comp_aestronglyMeasurable hsum.aestronglyMeasurable
    refine (hsum.norm.const_mul (d : ℝ)).of_le hmeas (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (euclideanNorm_nonneg _),
      abs_mul, abs_of_nonneg (Nat.cast_nonneg d), abs_of_nonneg (norm_nonneg _)]
    exact euclideanNorm_le_mul_norm _
  weak_gradient := fun k => by
    have hR : 0 < euclideanNorm z + |T| + 1 := by
      have := euclideanNorm_nonneg z; have := abs_nonneg T; linarith
    have hφB := (hloc _ hR).1.mono_measure
      (Measure.restrict_mono (ball_subset_originBall' z T) le_rfl)
    have hgB := (hloc _ hR).2.mono_measure
      (Measure.restrict_mono (ball_subset_originBall' z T) le_rfl)
    have hpot : MemLp (fun x => (x - z) i + φ x - c) 2 (ballMeasure z T) :=
      ((memLp_coordinate z T i).add hφB).sub (memLp_const c)
    have hgk : MemLp (fun x => (unitVector i + g x) k) 2 (ballMeasure z T) := by
      have := ((memLp_const (μ := ballMeasure z T) (p := 2) (unitVector i)).add hgB)
      exact this.of_le ((continuous_apply k).comp_aestronglyMeasurable this.aestronglyMeasurable)
        (Eventually.of_forall fun x => norm_le_pi_norm _ k)
    refine ⟨IntegrableOn.locallyIntegrableOn (hpot.integrable one_le_two),
      IntegrableOn.locallyIntegrableOn (hgk.integrable one_le_two), fun ψ hψ => ?_⟩
    -- the affine part
    have hcd : ContDiff ℝ 1 (fun x : Vec d => (x - z) i - c) := by fun_prop
    have haff := PDE.HasWeakPartialDerivOn.of_contDiff (U := ball z T) (i := k) hcd ψ hψ.1
      hψ.2.1 hψ.2.2
    have haff' : (∫ x in ball z T, ((x - z) i - c) * coordinateDerivative k ψ x) =
        -∫ x in ball z T, unitVector k i * ψ x := by
      have e1 : (∫ x in ball z T, ((x - z) i - c) * coordinateDerivative k ψ x) =
          ∫ x in ball z T, ((x - z) i - c) * (fderiv ℝ ψ x) (PDE.basisVec k) := rfl
      rw [e1, haff]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      exact congrArg (· * ψ x) (fderiv_coordinate_sub z i c x k)
    -- the corrector part, from the whole-space identity
    have hφk := (hφg k).2.2 ψ ⟨hψ.1, hψ.2.1, Set.subset_univ _⟩
    have hsupp : ∀ x ∉ ball z T, x ∉ tsupport ψ := fun x hx hx' => hx (hψ.2.2 hx')
    have hφk' : (∫ x in ball z T, φ x * coordinateDerivative k ψ x) =
        -∫ x in ball z T, g x k * ψ x := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
          rw [show coordinateDerivative k ψ x = 0 by
            have hψ0 : ψ =ᶠ[𝓝 x] 0 := (isClosed_tsupport ψ).isOpen_compl.eventually_mem
              (hsupp x hx) |>.mono fun y hy => image_eq_zero_of_notMem_tsupport hy
            unfold coordinateDerivative
            rw [Filter.EventuallyEq.fderiv_eq hψ0]
            simp, mul_zero]),
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
          rw [image_eq_zero_of_notMem_tsupport (hsupp x hx), mul_zero])]
      simpa [Measure.restrict_univ] using hφk
    obtain ⟨M, hM⟩ := hψ.exists_bound
    obtain ⟨M', hM'⟩ := hψ.exists_bound_coordinateDerivative k
    have hdψm := (hψ.continuous_coordinateDerivative k).aestronglyMeasurable
      (μ := ballMeasure z T)
    have hψm := hψ.continuous.aestronglyMeasurable (μ := ballMeasure z T)
    have hint1 : Integrable (fun x => ((x - z) i - c) * coordinateDerivative k ψ x)
        (ballMeasure z T) := by
      have := Integrable.bdd_mul (c := M')
        (((memLp_coordinate z T i).sub (memLp_const c)).integrable one_le_two) hdψm
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hM' x)
      exact this.congr (Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)
    have hint2 : Integrable (fun x => φ x * coordinateDerivative k ψ x) (ballMeasure z T) := by
      have := Integrable.bdd_mul (c := M') (hφB.integrable one_le_two) hdψm
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hM' x)
      exact this.congr (Eventually.of_forall fun x => by simp only; ring)
    have hint3 : Integrable (fun x => unitVector k i * ψ x) (ballMeasure z T) :=
      (Integrable.of_bound hψm M (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hM x)).const_mul _
    have hint4 : Integrable (fun x => g x k * ψ x) (ballMeasure z T) := by
      have hgk' : MemLp (fun x => g x k) 2 (ballMeasure z T) :=
        hgB.of_le ((continuous_apply k).comp_aestronglyMeasurable hgB.aestronglyMeasurable)
          (Eventually.of_forall fun x => norm_le_pi_norm _ k)
      have := Integrable.bdd_mul (c := M) (hgk'.integrable one_le_two) hψm
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hM x)
      exact this.congr (Eventually.of_forall fun x => by simp only; ring)
    have e1 : (∫ x in ball z T, ((x - z) i + φ x - c) * coordinateDerivative k ψ x) =
        (∫ x in ball z T, ((x - z) i - c) * coordinateDerivative k ψ x) +
          ∫ x in ball z T, φ x * coordinateDerivative k ψ x := by
      rw [← integral_add hint1 hint2]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
    have e2 : (∫ x in ball z T, (unitVector i + g x) k * ψ x) =
        (∫ x in ball z T, unitVector k i * ψ x) + ∫ x in ball z T, g x k * ψ x := by
      rw [← integral_add hint3 hint4]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      have hsym : unitVector i k = unitVector k i := by
        simp only [unitVector, Pi.single_apply]
        by_cases h : k = i
        · subst h; simp
        · simp [h, Ne.symm h]
      simp only [Pi.add_apply, hsym]
      ring
    show (∫ x in ball z T, ((x - z) i + φ x - c) * coordinateDerivative k ψ x) =
      -∫ x in ball z T, (unitVector i + g x) k * ψ x
    rw [e1, e2, haff', hφk']
    ring
  harmonic := by
    refine ⟨fun k => (harm.1 k).mono_set (Set.subset_univ _), locallyIntegrableOn_const 0,
      fun ψ hψ => ?_⟩
    have h := harm.2.2 ψ ⟨hψ.1, hψ.2.1, Set.subset_univ _⟩
    have hsupp : ∀ x ∉ ball z T, x ∉ tsupport ψ := fun x hx hx' => hx (hψ.2.2 hx')
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hψ0 : ψ =ᶠ[𝓝 x] 0 := (isClosed_tsupport ψ).isOpen_compl.eventually_mem
        (hsupp x hx) |>.mono fun y hy => image_eq_zero_of_notMem_tsupport hy
      have hg0 : gradient ψ x = 0 := by
        funext k
        unfold gradient coordinateDerivative
        rw [Filter.EventuallyEq.fderiv_eq hψ0]
        simp
      rw [hg0]
      simp [dot])]
    simpa [Measure.restrict_univ] using h

@[simp] theorem correctedCoordinate_potential (a : CoefficientField d Λ) (z : Vec d) (T : ℝ)
    (i : Fin d) (c : ℝ) (φ : Vec d → ℝ) (g : Vec d → Vec d) (hφg hloc harm) (x : Vec d) :
    (correctedCoordinate a z T i c φ g hφg hloc harm).potential x = (x - z) i + φ x - c := rfl

@[simp] theorem correctedCoordinate_grad (a : CoefficientField d Λ) (z : Vec d) (T : ℝ)
    (i : Fin d) (c : ℝ) (φ : Vec d → ℝ) (g : Vec d → Vec d) (hφg hloc harm) (x : Vec d) :
    (correctedCoordinate a z T i c φ g hφg hloc harm).grad x = unitVector i + g x := rfl

/-- **The selected coordinate is close to every admissible corrected coordinate**:
`I[w_i - h] ≤ 4 I[φ - c]`. -/
theorem IsCoordinateMinimizer.localizationObjective_sub_corrected_le {a : CoefficientField d Λ}
    {z : Vec d} {T S σ θ C : ℝ} (hσS : σ * S ≠ 0) {i : Fin d} {w : LocalHarmonic a z T}
    (hw : IsCoordinateMinimizer S σ θ C i w) (c : ℝ) (φ : Vec d → ℝ) (g : Vec d → Vec d)
    (hφg : HasWeakGradient Set.univ φ g)
    (hloc : ∀ R : ℝ, 0 < R → MemLp φ 2 (volume.restrict (ball 0 R)) ∧
      MemLp g 2 (volume.restrict (ball 0 R)))
    (harm : HasWeakDivergence Set.univ (fun x => (a x).mulVec (unitVector i + g x))
      (fun _ => 0))
    (hadm : vectorRms volume (ball z T) (fun x => unitVector i + g x) ≤ C) :
    localizationObjective z T S σ θ
        (fun x => w.potential x - ((x - z) i + φ x - c)) ≤
      4 * localizationObjective z T S σ θ (fun x => φ x - c) := by
  have h := hw.localizationObjective_sub_le hσS
    (h := correctedCoordinate a z T i c φ g hφg hloc harm) hadm
  have e : (fun x => (correctedCoordinate a z T i c φ g hφg hloc harm).potential x - (x - z) i) =
      fun x => φ x - c := by
    funext x; simp only [correctedCoordinate_potential]; ring
  rw [e] at h
  exact h

end QSH
