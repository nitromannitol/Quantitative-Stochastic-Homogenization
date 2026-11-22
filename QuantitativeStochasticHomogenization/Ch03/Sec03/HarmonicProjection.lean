import QuantitativeStochasticHomogenization.Ch03.Sec03.VeryWeakHarmonic

/-!
# Harmonic approximation by orthogonal projection

Let `B` be a round ball and `u ∈ L²(B)` with `|∫_B u Δχ| ≤ ε ‖Δχ‖_{L²(B)}` for every smooth
compactly supported `χ` in `B`. The Laplacians of such `χ` form a subspace of `L²(B)`; the
orthogonal projection `p` of `u` onto its closure has norm at most `ε`, and `u - p` is orthogonal
to every `Δχ`, that is, very weakly harmonic. By the Weyl lemma it agrees almost everywhere with
a smooth harmonic function `v`, so `‖u - v‖_{L²(B)} ≤ ε`.
-/

open MeasureTheory Filter
open scoped InnerProductSpace

noncomputable section

namespace QSH

variable {d : ℕ}

theorem euclideanCoordDeriv_add {f g : Vec d → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (i : Fin d) :
    PDE.euclideanCoordDeriv i (f + g) =
      PDE.euclideanCoordDeriv i f + PDE.euclideanCoordDeriv i g := by
  funext x
  simp [PDE.euclideanCoordDeriv, fderiv_add (hf x) (hg x)]

theorem euclideanCoordDeriv_const_smul {f : Vec d → ℝ} (hf : Differentiable ℝ f) (c : ℝ)
    (i : Fin d) :
    PDE.euclideanCoordDeriv i (c • f) = c • PDE.euclideanCoordDeriv i f := by
  funext x
  simp [PDE.euclideanCoordDeriv, fderiv_const_smul (hf x) c]

theorem euclideanCoordLaplacian_add {f g : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    PDE.euclideanCoordLaplacian (f + g) =
      PDE.euclideanCoordLaplacian f + PDE.euclideanCoordLaplacian g := by
  funext x
  simp only [PDE.euclideanCoordLaplacian, PDE.euclideanCoordSecondDeriv, Pi.add_apply,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [euclideanCoordDeriv_add (hf.differentiable (by simp)) (hg.differentiable (by simp)) i]
  have h1 := ((PDE.contDiff_euclideanCoordDeriv hf i).differentiable (by simp)) x
  have h2 := ((PDE.contDiff_euclideanCoordDeriv hg i).differentiable (by simp)) x
  rw [fderiv_add h1 h2]
  rfl

theorem euclideanCoordLaplacian_const_smul {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (c : ℝ) :
    PDE.euclideanCoordLaplacian (c • f) = c • PDE.euclideanCoordLaplacian f := by
  funext x
  simp only [PDE.euclideanCoordLaplacian, PDE.euclideanCoordSecondDeriv, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [euclideanCoordDeriv_const_smul (hf.differentiable (by simp)) c i]
  have h1 := ((PDE.contDiff_euclideanCoordDeriv hf i).differentiable (by simp)) x
  rw [fderiv_const_smul h1 c]
  rfl

theorem euclideanCoordLaplacian_zero :
    PDE.euclideanCoordLaplacian (0 : Vec d → ℝ) = 0 := by
  have h0 : ∀ i : Fin d, PDE.euclideanCoordDeriv i (0 : Vec d → ℝ) = 0 := fun i => by
    funext y
    simp [PDE.euclideanCoordDeriv]
  funext x
  simp [PDE.euclideanCoordLaplacian, PDE.euclideanCoordSecondDeriv, h0]

theorem continuous_euclideanCoordLaplacian {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (PDE.euclideanCoordLaplacian f) := by
  unfold PDE.euclideanCoordLaplacian
  refine continuous_finsetSum _ fun i _ => ?_
  exact (PDE.contDiff_euclideanCoordDeriv (PDE.contDiff_euclideanCoordDeriv hf i) i).continuous

theorem hasCompactSupport_euclideanCoordLaplacian {f : Vec d → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (PDE.euclideanCoordLaplacian f) := by
  unfold PDE.euclideanCoordLaplacian
  have h : ∀ i : Fin d, HasCompactSupport (PDE.euclideanCoordSecondDeriv i i f) := fun i =>
    PDE.hasCompactSupport_euclideanCoordDeriv (PDE.hasCompactSupport_euclideanCoordDeriv hf i) i
  have hsum : HasCompactSupport (∑ i : Fin d, PDE.euclideanCoordSecondDeriv i i f) := by
    classical
    induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
    | empty => simpa using (HasCompactSupport.zero : HasCompactSupport (0 : Vec d → ℝ))
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a).add ih
  have heq : (fun x => ∑ i : Fin d, PDE.euclideanCoordSecondDeriv i i f x) =
      ∑ i : Fin d, PDE.euclideanCoordSecondDeriv i i f := by
    funext x
    simp
  rw [heq]
  exact hsum

/-- A projection bound: if `|⟪v, w⟫| ≤ e ‖w‖` on `S`, the projection of `v` onto `S` has norm
at most `e`. -/
theorem norm_starProjection_le_of_inner_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (S : Submodule ℝ E) [S.HasOrthogonalProjection] (v : E) {e : ℝ}
    (he : 0 ≤ e) (h : ∀ w ∈ S, |⟪v, w⟫_ℝ| ≤ e * ‖w‖) : ‖S.starProjection v‖ ≤ e := by
  set p := S.starProjection v
  have hp : p ∈ S := S.starProjection_apply_mem v
  have ho : ⟪v - p, p⟫_ℝ = 0 := S.starProjection_inner_eq_zero v p hp
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at ho
  have hpair := h p hp
  rw [sub_eq_zero.mp ho, abs_of_nonneg (sq_nonneg _)] at hpair
  by_cases h0 : p = 0
  · simpa [h0] using he
  · rw [pow_two] at hpair
    exact le_of_mul_le_mul_right hpair (norm_pos_iff.mpr h0)

/-- **Harmonic approximation by orthogonal projection** on a round ball. -/
theorem exists_harmonic_sub_sq_le_of_laplacian_pairing (hd : 0 < d) {x₀ : Vec d} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (PDE.euclideanBall x₀ r)))
    (hpair : ∀ χ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      tsupport χ ⊆ PDE.euclideanBall x₀ r →
      |∫ x in PDE.euclideanBall x₀ r, u x * PDE.euclideanCoordLaplacian χ x| ≤
        ε * Real.sqrt (∫ x in PDE.euclideanBall x₀ r, PDE.euclideanCoordLaplacian χ x ^ 2)) :
    ∃ v : Vec d → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) v (PDE.euclideanBall x₀ r) ∧
      (∀ y ∈ PDE.euclideanBall x₀ r, PDE.euclideanCoordLaplacian v y = 0) ∧
      MemLp (fun x => u x - v x) 2 (volume.restrict (PDE.euclideanBall x₀ r)) ∧
      ∫ x in PDE.euclideanBall x₀ r, (u x - v x) ^ 2 ≤ ε ^ 2 := by
  classical
  set B := PDE.euclideanBall x₀ r with hBdef
  set μ : Measure (Vec d) := volume.restrict B with hμdef
  have hBo : IsOpen B := PDE.isOpen_euclideanBall x₀ r
  have hBm : MeasurableSet B := hBo.measurableSet
  have hBfin : volume B ≠ ⊤ := PDE.volume_euclideanBall_ne_top x₀ hr.le
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 hBfin
  let IsTest : (Vec d → ℝ) → Prop := fun χ =>
    ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ B
  have hmem : ∀ χ, IsTest χ → MemLp (PDE.euclideanCoordLaplacian χ) 2 μ := fun χ hχ =>
    ((continuous_euclideanCoordLaplacian hχ.1).memLp_of_hasCompactSupport (μ := volume) (p := 2)
      (hasCompactSupport_euclideanCoordLaplacian hχ.2.1)).restrict B
  have key : ∀ (g : Vec d → ℝ) (hg : MemLp g 2 μ),
      ∫ x, u x * g x ∂μ = ⟪hu.toLp u, hg.toLp g⟫_ℝ := by
    intro g hg
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hu.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
    rw [h1, h2]
    simp [mul_comm]
  have hnorm : ∀ (g : Vec d → ℝ) (hg : MemLp g 2 μ),
      ‖hg.toLp g‖ = Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
    intro g hg
    have h1 : ‖hg.toLp g‖ ^ 2 = ∫ x, g x ^ 2 ∂μ := by
      rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hg.coeFn_toLp] with x h1
      rw [h1]
      simp [pow_two]
    rw [← h1, Real.sqrt_sq (norm_nonneg _)]
  let S₀ : Submodule ℝ (Lp ℝ 2 μ) :=
    { carrier := {f | ∃ χ, ∃ hχ : IsTest χ, f = (hmem χ hχ).toLp _}
      add_mem' := by
        rintro f₁ f₂ ⟨χ₁, hχ₁, rfl⟩ ⟨χ₂, hχ₂, rfl⟩
        have ht : IsTest (χ₁ + χ₂) := ⟨hχ₁.1.add hχ₂.1, hχ₁.2.1.add hχ₂.2.1,
          (closure_mono (Function.support_add _ _)).trans (by
            rw [closure_union]
            exact Set.union_subset hχ₁.2.2 hχ₂.2.2)⟩
        refine ⟨χ₁ + χ₂, ht, ?_⟩
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => by
          rw [euclideanCoordLaplacian_add hχ₁.1 hχ₂.1])
      zero_mem' := by
        have ht : IsTest (0 : Vec d → ℝ) := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
        refine ⟨0, ht, ?_⟩
        exact ((MemLp.toLp_congr (hmem 0 ht) MemLp.zero (Eventually.of_forall fun x => by
          simp [euclideanCoordLaplacian_zero])).trans (MemLp.toLp_zero _)).symm
      smul_mem' := by
        rintro c f ⟨χ, hχ, rfl⟩
        have ht : IsTest (c • χ) := ⟨hχ.1.const_smul c, hχ.2.1.smul_left,
          (closure_mono (Function.support_const_smul_subset c χ)).trans hχ.2.2⟩
        refine ⟨c • χ, ht, ?_⟩
        rw [← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => by
          rw [euclideanCoordLaplacian_const_smul hχ.1 c]) }
  let S : Submodule ℝ (Lp ℝ 2 μ) := S₀.topologicalClosure
  have : CompleteSpace S := S₀.isClosed_topologicalClosure.completeSpace_coe
  set U := hu.toLp u with hUdef
  have hbound₀ : ∀ f ∈ S₀, |⟪U, f⟫_ℝ| ≤ ε * ‖f‖ := by
    rintro f ⟨χ, hχ, rfl⟩
    rw [← key _ (hmem χ hχ), hnorm _ (hmem χ hχ)]
    exact hpair χ hχ.1 hχ.2.1 hχ.2.2
  have hbound : ∀ f ∈ S, |⟪U, f⟫_ℝ| ≤ ε * ‖f‖ := by
    have hclosed : IsClosed {f : Lp ℝ 2 μ | |⟪U, f⟫_ℝ| ≤ ε * ‖f‖} :=
      isClosed_le ((continuous_const.inner continuous_id).abs)
        (continuous_const.mul continuous_norm)
    intro f hf
    have hsub : closure (S₀ : Set (Lp ℝ 2 μ)) ⊆ {f | |⟪U, f⟫_ℝ| ≤ ε * ‖f‖} :=
      closure_minimal (fun f hf => hbound₀ f hf) hclosed
    have hf' : f ∈ closure (S₀ : Set (Lp ℝ 2 μ)) := by
      rw [← Submodule.topologicalClosure_coe]
      exact hf
    exact hsub hf'
  set P := S.starProjection U with hPdef
  have hP : ‖P‖ ≤ ε := norm_starProjection_le_of_inner_le S U hε hbound
  set H : Lp ℝ 2 μ := U - P with hHdef
  have horth : ∀ f ∈ S, ⟪H, f⟫_ℝ = 0 := fun f hf => S.starProjection_inner_eq_zero U f hf
  set h : Vec d → ℝ := (H : Vec d → ℝ) with hhdef
  have hhmem : MemLp h 2 μ := Lp.memLp H
  have hvw : IsVeryWeakHarmonicOn B h := by
    intro χ hχ hχc hχs
    have ht : IsTest χ := ⟨hχ, hχc, hχs⟩
    have h0 := horth _ (S₀.le_topologicalClosure ⟨χ, ht, rfl⟩)
    rw [MeasureTheory.L2.inner_def] at h0
    change ∫ x, h x * PDE.euclideanCoordLaplacian χ x ∂μ = 0
    rw [← h0]
    refine integral_congr_ae ?_
    filter_upwards [(hmem χ ht).coeFn_toLp] with x h1
    rw [h1]
    simp [hhdef, mul_comm]
  have hloc : LocallyIntegrable (B.indicator h) volume := by
    have hint : IntegrableOn h B volume := hhmem.integrable (by norm_num)
    exact ((integrable_indicator_iff hBm).2 hint).locallyIntegrable
  obtain ⟨v, hvs, hvh, hvae⟩ := exists_harmonic_ae_eq_of_isVeryWeakHarmonicOn hd hr hloc hvw
  have hdiff : (fun x => u x - v x) =ᵐ[μ] (P : Vec d → ℝ) := by
    have hsub := Lp.coeFn_sub U P
    have hUu := hu.coeFn_toLp
    filter_upwards [hsub, hUu, hvae] with x h1 h2 h3
    have h1' : h x = U x - P x := by
      simp only [hhdef, hHdef]
      exact h1
    rw [h3, h1', h2]
    ring
  refine ⟨v, hvs, hvh, (Lp.memLp P).ae_eq hdiff.symm, ?_⟩
  have hPsq : ∫ x, (u x - v x) ^ 2 ∂μ = ‖P‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hdiff] with x h1
    rw [h1]
    simp [pow_two]
  change ∫ x, (u x - v x) ^ 2 ∂μ ≤ ε ^ 2
  rw [hPsq]
  exact pow_le_pow_left₀ (norm_nonneg _) hP 2

end QSH
