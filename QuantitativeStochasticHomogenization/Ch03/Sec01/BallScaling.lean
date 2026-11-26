import QuantitativeStochasticHomogenization.Ch02.Sec03.Theorem218

/-!
# Dilations and translations of the normalized `L^p` norms

The normalized `L^p` norms of (0.29) are invariant under translations and dilations of the
domain: for `c > 0`, `‖f(c · + y)‖_{L̲^p(S)} = ‖f‖_{L̲^p(cS + y)}`
(`eLpMeanNormOn_comp_smul`, `eLpMeanNormOn_comp_add`), and the Euclidean balls satisfy
`c B_r = B_{cr}` and `B_r + y = B_r(y)` (`smul_ball_zero`, `preimage_add_right_ball`). These are the
changes of variables of the proof of Proposition 3.2.
-/

open MeasureTheory Filter Set
open scoped ENNReal Pointwise

noncomputable section

namespace QSH

variable {d : ℕ}

theorem mem_ball_zero_iff' {x : Vec d} {r : ℝ} : x ∈ ball (0 : Vec d) r ↔ euclideanNorm x < r := by
  show euclideanNorm (x - 0) < r ↔ _
  rw [sub_zero]

/-- `c B_r = B_{cr}` for `c > 0`. -/
theorem smul_ball_zero {c : ℝ} (hc : 0 < c) (r : ℝ) : c • ball (0 : Vec d) r = ball 0 (c * r) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne', mem_ball_zero_iff', mem_ball_zero_iff',
    euclideanNorm_smul, abs_of_pos (inv_pos.2 hc), inv_mul_lt_iff₀ hc]

/-- `(· + y)⁻¹' B_r(y) = B_r`. -/
theorem preimage_add_right_ball (y : Vec d) (r : ℝ) :
    (fun x => x + y) ⁻¹' ball y r = ball (0 : Vec d) r := by
  ext x
  show euclideanNorm (x + y - y) < r ↔ euclideanNorm (x - 0) < r
  rw [add_sub_cancel_right, sub_zero]

theorem measurableSet_ball' (z : Vec d) (r : ℝ) : MeasurableSet (ball z r) :=
  (isOpen_ball z r).measurableSet

/-- Dilations preserve the normalized volume measures: `c • ·` maps the normalized measure of
`S` to that of `cS`. -/
theorem measurePreserving_smul_normalizedVolumeOn {c : ℝ} (hc : 0 < c) (S : Set (Vec d)) :
    MeasurePreserving (fun x : Vec d => c • x) (PDE.normalizedVolumeOn S)
      (PDE.normalizedVolumeOn (c • S)) := by
  have hm : Measurable (fun x : Vec d => c • x) := measurable_const_smul c
  refine ⟨hm, ?_⟩
  have hemb : MeasurableEmbedding (fun x : Vec d => c • x) :=
    (Homeomorph.smulOfNeZero c hc.ne').isClosedEmbedding.measurableEmbedding
  have hpre : (fun x : Vec d => c • x) ⁻¹' (c • S) = S := by
    ext x
    exact Set.smul_mem_smul_set_iff₀ hc.ne' S x
  have hvol : volume (c • S) = ENNReal.ofReal (c ^ d) * volume S := by
    rw [Measure.addHaar_smul, Module.finrank_fin_fun, abs_of_pos (pow_pos hc d)]
  have hc0 : ENNReal.ofReal (c ^ d) ≠ 0 := by simp [pow_pos hc d]
  rw [PDE.normalizedVolumeOn, PDE.normalizedVolumeOn, Measure.map_smul]
  change (volume S)⁻¹ • Measure.map (fun x : Vec d => c • x) (volume.restrict S) =
    (volume (c • S))⁻¹ • volume.restrict (c • S)
  rw [← hpre, ← hemb.restrict_map, hpre, Measure.map_addHaar_smul volume hc.ne',
    Module.finrank_fin_fun, Measure.restrict_smul, smul_smul, hvol, ENNReal.mul_inv (Or.inl hc0)
    (Or.inl ENNReal.ofReal_ne_top), abs_inv, abs_of_pos (pow_pos hc d),
    ENNReal.ofReal_inv_of_pos (pow_pos hc d), mul_comm]
  exact hm.aemeasurable

/-- Translations preserve the normalized volume measures. -/
theorem measurePreserving_add_normalizedVolumeOn (y : Vec d) {S : Set (Vec d)}
    (hS : MeasurableSet S) :
    MeasurePreserving (fun x : Vec d => x + y)
      (PDE.normalizedVolumeOn ((fun x => x + y) ⁻¹' S)) (PDE.normalizedVolumeOn S) := by
  have hT : MeasurePreserving (fun x : Vec d => x + y)
      (volume.restrict ((fun x => x + y) ⁻¹' S)) (volume.restrict S) :=
    (measurePreserving_add_right volume y).restrict_preimage hS
  have hvol : volume ((fun x : Vec d => x + y) ⁻¹' S) = volume S :=
    measure_preimage_add_right volume y S
  refine ⟨hT.measurable, ?_⟩
  rw [PDE.normalizedVolumeOn, PDE.normalizedVolumeOn, Measure.map_smul, hvol]
  change (volume S)⁻¹ • Measure.map (fun x : Vec d => x + y)
      (volume.restrict ((fun x => x + y) ⁻¹' S)) = (volume S)⁻¹ • volume.restrict S
  rw [hT.map_eq]
  exact hT.measurable.aemeasurable

/-- `‖f(c ·)‖_{L̲^p(S)} = ‖f‖_{L̲^p(cS)}` for `c > 0`. -/
theorem eLpMeanNormOn_comp_smul {E : Type*} [NormedAddCommGroup E] {c : ℝ} (hc : 0 < c)
    (S : Set (Vec d)) (p : ℝ≥0∞) {f : Vec d → E}
    (hf : AEStronglyMeasurable f (PDE.normalizedVolumeOn (c • S))) :
    PDE.eLpMeanNormOn S p (fun x => f (c • x)) = PDE.eLpMeanNormOn (c • S) p f :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_smul_normalizedVolumeOn hc S)

/-- `‖f(· + y)‖_{L̲^p((· + y)⁻¹ S)} = ‖f‖_{L̲^p(S)}`. -/
theorem eLpMeanNormOn_comp_add {E : Type*} [NormedAddCommGroup E] (y : Vec d)
    {S : Set (Vec d)} (hS : MeasurableSet S) (p : ℝ≥0∞) {f : Vec d → E}
    (hf : AEStronglyMeasurable f (PDE.normalizedVolumeOn S)) :
    PDE.eLpMeanNormOn ((fun x => x + y) ⁻¹' S) p (fun x => f (x + y)) =
      PDE.eLpMeanNormOn S p f :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_add_normalizedVolumeOn y hS)

end QSH
