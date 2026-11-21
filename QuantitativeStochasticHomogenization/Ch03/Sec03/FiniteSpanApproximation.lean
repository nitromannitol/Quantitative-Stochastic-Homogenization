import QuantitativeStochasticHomogenization.Front.Notation

/-!
# Normalized `L²` approximation by a finite family

If a square-integrable function `u` on a set `U` of positive finite volume can be approximated in
the normalized `L²(U)` norm by linear combinations of finitely many square-integrable functions
`fᵢ`, then `u` is almost everywhere on `U` equal to one of these combinations: the span of the
`fᵢ` in `L²(U)` is finite dimensional, hence closed. This is the step "`E(t) = 0` implies that
`u` is a corrected affine function on `E_t`" of the first-order proof of Theorem 3.8, `k = 1`.
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The normalized `L²(U)` norm through the norm of `L²(U)`. -/
theorem scalarRms_eq_mul_norm_toLp {U : Set (Vec d)} {g : Vec d → ℝ}
    (hg : MemLp g 2 (volume.restrict U)) :
    scalarRms volume U g = Real.sqrt (volume.real U)⁻¹ * ‖hg.toLp g‖ := by
  rw [Lp.norm_toLp, hg.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun x => by positivity) _)]
  unfold scalarRms
  rw [setAverage_eq, smul_eq_mul, Real.sqrt_mul (inv_nonneg.2 measureReal_nonneg)]
  congr 1
  rw [Real.sqrt_eq_rpow, ENNReal.toReal_ofNat, one_div]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs]

/-- **Closedness of a finite span in `L²(U)`.** -/
theorem exists_ae_eq_sum_of_forall_scalarRms_lt {ι : Type*} [Fintype ι] {U : Set (Vec d)}
    (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤) {u : Vec d → ℝ} {f : ι → Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict U)) (hf : ∀ i, MemLp (f i) 2 (volume.restrict U))
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ c : ι → ℝ,
      scalarRms volume U (fun x => u x - ∑ i, c i * f i x) < ε) :
    ∃ c : ι → ℝ, ∀ᵐ x ∂(volume.restrict U), u x = ∑ i, c i * f i x := by
  classical
  set μ := volume.restrict U with hμ
  set F : ι → Lp ℝ 2 μ := fun i => (hf i).toLp (f i) with hF
  set S : Submodule ℝ (Lp ℝ 2 μ) := Submodule.span ℝ (Set.range F) with hS
  have hfin : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (Set.finite_range F)
  have hSc : IsClosed (S : Set (Lp ℝ 2 μ)) := Submodule.closed_of_finiteDimensional S
  have hmem : ∀ c : ι → ℝ, MemLp (fun x => u x - ∑ i, c i * f i x) 2 μ := fun c =>
    hu.sub (memLp_finsetSum _ fun i _ => (hf i).const_mul (c i))
  have hcoe : ∀ c : ι → ℝ,
      ⇑(hu.toLp u - ∑ i, c i • F i) =ᵐ[μ] fun x => u x - ∑ i, c i * f i x := by
    intro c
    filter_upwards [Lp.coeFn_sub (hu.toLp u) (∑ i, c i • F i), hu.coeFn_toLp,
      Lp.coeFn_fun_finsetSum Finset.univ (fun i => c i • F i),
      ae_all_iff.2 fun i => Lp.coeFn_smul (c i) (F i),
      ae_all_iff.2 fun i => (hf i).coeFn_toLp] with x h1 h2 h3 h4 h5
    rw [h1, Pi.sub_apply, h2, h3]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h4 i, Pi.smul_apply, smul_eq_mul, hF]
    simp only
    rw [h5 i]
  have hvol : 0 < Real.sqrt (volume.real U)⁻¹ := by
    refine Real.sqrt_pos.2 (inv_pos.2 ?_)
    rw [measureReal_def]
    exact ENNReal.toReal_pos hU0 hU
  have hcl : hu.toLp u ∈ closure (S : Set (Lp ℝ 2 μ)) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨c, hc⟩ := happrox (Real.sqrt (volume.real U)⁻¹ * ε) (mul_pos hvol hε)
    refine ⟨∑ i, c i • F i, ?_, ?_⟩
    · exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [dist_eq_norm]
      have hn : ‖hu.toLp u - ∑ i, c i • F i‖ = ‖(hmem c).toLp _‖ := by
        rw [Lp.norm_def, Lp.norm_toLp, eLpNorm_congr_ae (hcoe c)]
      rw [hn]
      rw [scalarRms_eq_mul_norm_toLp (hmem c)] at hc
      exact lt_of_mul_lt_mul_left hc hvol.le
  have hin : hu.toLp u ∈ S := hSc.closure_subset hcl
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hin
  refine ⟨c, ?_⟩
  have h0 := hcoe c
  rw [hc, sub_self] at h0
  filter_upwards [h0, Lp.coeFn_zero ℝ 2 μ] with x hx hz
  rw [hz] at hx
  simp only [Pi.zero_apply] at hx
  linarith

end QSH
