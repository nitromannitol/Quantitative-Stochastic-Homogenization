import QuantitativeStochasticHomogenization.AppC.ReverseHolderRatio

/-!
# The global reverse Hölder inequality

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix C, Corollary C.9: for `u ∈ H¹₀(U)` solving `-∇·(a∇u) = h`, extended by zero to `ℝ^d`,
`‖∇u‖_{L̲²(B_{r/2}(z))}` is bounded by `‖∇u‖_{L̲^{2_*}}` and `‖h‖_{H̲^{-1}}` on a larger ball.

The proof is the book's, for `h = ∇·H`. If `B_{ρ/4}(y) ⊆ U`, Corollary C.3 applies. Otherwise the
ball `B_{ρ/4}(y)`, which meets `U`, contains a point `z' ∈ ∂U`, and `B_{ρ/8}(y) ⊆ B_{3ρ/8}(z')`,
`B_{3ρ/4}(z') ⊆ B_ρ(y)`; Lemma C.8 on `B_{3ρ/4}(z')` (`boundaryCaccioppoli_of_density`) and the
Sobolev–Poincaré inequality for functions vanishing on `B_{3ρ/4}(z') \ U`, a set of measure at
least `c |B_{3ρ/4}|` (`sobolevPoincare_of_vanishing`), give the estimate from `B_{ρ/8}(y)` to
`B_ρ(y)`. The book states (C.19) from `B_{r/2}(z)` to `B_r(z) ∩ U`; its proof gives the right-hand
side on `B_{4r}(z') ∩ U`, and the form `B_{r/2}(z) ⊆ B_r(z)` needed for Lemma C.4 follows by the
covering argument of `reverseHolder_half_of_eighth`.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- A connected set meeting the open set `U` and not contained in it meets `∂U`. -/
theorem exists_mem_frontier_of_not_subset {U S : Set (Vec d)} (hUo : IsOpen U)
    (hS : IsPreconnected S) (h1 : (S ∩ U).Nonempty) (h2 : ¬ S ⊆ U) :
    ∃ z ∈ frontier U, z ∈ S := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hsub : S ⊆ U ∪ (closure U)ᶜ := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl hxU
    · right
      intro hxc
      exact hcon x ⟨hxc, by rwa [hUo.interior_eq]⟩ hx
  rcases hS.subset_or_subset hUo isClosed_closure.isOpen_compl
      (disjoint_compl_right_iff_subset.mpr subset_closure) hsub with h | h
  · exact h2 h
  · obtain ⟨x, hxS, hxU⟩ := h1
    exact h hxS (subset_closure hxU)

theorem isPreconnected_ball (z : Vec d) {r : ℝ} (hr : 0 < r) : IsPreconnected (ball z r) := by
  rw [ball_eq_euclideanBall z hr]
  exact (PDE.convex_euclideanBall z r).isPreconnected

/-- `‖f‖_{L̲^s(A)} ≤ M ‖f‖_{L̲^s(B)}` for `A ⊆ B` with `|B| ≤ M |A|`, `M ≥ 1`, `s ≥ 1`. -/
theorem eLpMeanNormOn_le_of_volume_le {A B : Set (Vec d)} (hAB : A ⊆ B) (hA0 : volume A ≠ 0)
    (hBt : volume B ≠ ⊤) {M : ℝ} (hM : 1 ≤ M) (hvol : volume B ≤ ENNReal.ofReal M * volume A)
    {s : ℝ≥0∞} (hs : 1 ≤ s) (f : Vec d → ℝ) :
    PDE.eLpMeanNormOn A s f ≤ ENNReal.ofReal M * PDE.eLpMeanNormOn B s f := by
  refine (eLpMeanNormOn_le_of_subset hAB hA0 hBt s f).trans ?_
  gcongr ?_ * _
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal M := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hM
  have ht : (1 / s).toReal ≤ 1 := by
    have : 1 / s ≤ 1 := by
      rw [one_div]
      exact ENNReal.inv_le_one.mpr hs
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
  calc (volume B / volume A) ^ (1 / s).toReal
      ≤ ENNReal.ofReal M ^ (1 / s).toReal :=
        ENNReal.rpow_le_rpow (ENNReal.div_le_of_le_mul hvol) ENNReal.toReal_nonneg
    _ ≤ ENNReal.ofReal M ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le h1 ht
    _ = ENNReal.ofReal M := ENNReal.rpow_one _

/-- `‖f‖_{L̲^s(B)} ≤ ‖f‖_{L̲^s(W)}` for `W ⊆ B` when `f = 0` on `B \ W`. -/
theorem eLpMeanNormOn_le_of_eq_zero_off {W B : Set (Vec d)} (hWB : W ⊆ B) (hWm : MeasurableSet W)
    (hBm : MeasurableSet B) (hBt : volume B ≠ ⊤) {f : Vec d → ℝ}
    (hf0 : ∀ x ∈ B \ W, f x = 0) (s : ℝ≥0∞) :
    PDE.eLpMeanNormOn B s f ≤ PDE.eLpMeanNormOn W s f := by
  have hWt : volume W ≠ ⊤ := ne_top_of_le_ne_top hBt (measure_mono hWB)
  rw [PDE.eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn hBt.lt_top,
    PDE.eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn hWt.lt_top]
  have e : PDE.eLpNormOn B s f = PDE.eLpNormOn W s f := by
    have h1 : f =ᵐ[volume.restrict B] W.indicator f := by
      refine (ae_restrict_iff' hBm).mpr (Eventually.of_forall fun x hx => ?_)
      by_cases hxW : x ∈ W
      · rw [indicator_of_mem hxW]
      · rw [indicator_of_notMem hxW, hf0 x ⟨hx, hxW⟩]
    rw [PDE.eLpNormOn, PDE.eLpNormOn, eLpNorm_congr_ae h1,
      eLpNorm_indicator_eq_eLpNorm_restrict hWm, Measure.restrict_restrict hWm,
      inter_eq_left.mpr hWB]
  rw [e]
  gcongr

/-- On a set inside `U`, the zero extension of `|g|` has the norms of `|g|`. -/
theorem eLpMeanNormOn_indicator_eq {A U : Set (Vec d)} (hAU : A ⊆ U) (hAm : MeasurableSet A)
    (g : Vec d → Vec d) (s : ℝ≥0∞) :
    PDE.eLpMeanNormOn A s (fun x => euclideanNorm (U.indicator g x)) =
      PDE.eLpMeanNormOn A s (fun x => euclideanNorm (g x)) := by
  refine eLpMeanNormOn_congr_of_subset subset_rfl ?_
  refine (ae_restrict_iff' hAm).mpr (Eventually.of_forall fun x hx => ?_)
  change euclideanNorm (U.indicator g x) = euclideanNorm (g x)
  rw [indicator_of_mem (hAU hx)]

theorem eLpMeanNormOn_indicator_eq' {A U : Set (Vec d)} (hAU : A ⊆ U) (hAm : MeasurableSet A)
    (u : Vec d → ℝ) (s : ℝ≥0∞) :
    PDE.eLpMeanNormOn A s (U.indicator u) = PDE.eLpMeanNormOn A s u := by
  refine eLpMeanNormOn_congr_of_subset subset_rfl ?_
  refine (ae_restrict_iff' hAm).mpr (Eventually.of_forall fun x hx => ?_)
  rw [indicator_of_mem (hAU hx)]

theorem euclideanNorm_indicator_of_notMem {U : Set (Vec d)} {g : Vec d → Vec d} {x : Vec d}
    (hx : x ∉ U) : euclideanNorm (U.indicator g x) = 0 := by
  rw [indicator_of_notMem hx]
  simp [euclideanNorm, euclideanSq, dot]

theorem volume_ball_le_mul (x z : Vec d) {ρ k : ℝ} (hρ : 0 < ρ) (hk : 0 < k) :
    volume (ball z (k * ρ)) = ENNReal.ofReal (k ^ d) * volume (ball x ρ) := by
  rw [volume_ball_mul z hk hρ, volume_ball_eq_of_radius z x hρ]

theorem volume_le_ofReal_mul_of_real {A B : Set (Vec d)} (hAt : volume A ≠ ⊤)
    (hBt : volume B ≠ ⊤) {M : ℝ} (hM : 0 ≤ M) (h : volume.real A ≤ M * volume.real B) :
    volume A ≤ ENNReal.ofReal M * volume B := by
  rw [← ENNReal.ofReal_toReal hAt, ← ENNReal.ofReal_toReal hBt, ← ENNReal.ofReal_mul hM]
  exact ENNReal.ofReal_le_ofReal h

/-- **Corollary C.9, from `B_{ρ/8}(y)` to `B_ρ(y)`.** For `d ≥ 2`, an open set `U` with boundary
density `c ∈ (0, 1]` up to the scale `R₀`, and `u ∈ H¹₀(U)` solving `-∇·(a∇u) = ∇·H` in `U` with
`H ∈ L²(U; ℝ^d)`, the zero extensions `|∇u|` and `|H|` of `|∇u|` and `|H|` satisfy, for every
ball `B_ρ(y)` with `ρ ≤ R₀`,
`‖∇u‖_{L̲²(B_{ρ/8}(y))} ≤ K (‖∇u‖_{L̲^{2_*}(B_ρ(y))} + ‖H‖_{L̲²(B_ρ(y))})` with `K(d, Λ, c)`. -/
theorem reverseHolder_eighth_global (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ) {U : Set (Vec d)}
    (hUo : IsOpen U) {c R₀ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hden : HasBoundaryDensity U c R₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ (a : CoefficientField d Λ) (u : Vec d → ℝ) (g H : Vec d → Vec d),
      H01 U u g → (∀ i, MemLp (fun x => H x i) 2 (volume.restrict U)) →
      HasWeakDivergence U (fun x => (a x).mulVec (g x) + H x) (fun _ => 0) →
      ∀ (y : Vec d) (ρ : ℝ), 0 < ρ → ρ ≤ R₀ →
        PDE.eLpMeanNormOn (ball y (ρ / 8)) 2 (fun x => euclideanNorm (U.indicator g x)) ≤
          ENNReal.ofReal K *
            (PDE.eLpMeanNormOn (ball y ρ) (ENNReal.ofReal (2 * d / (d + 2)))
                (fun x => euclideanNorm (U.indicator g x)) +
              PDE.eLpMeanNormOn (ball y ρ) 2 (fun x => euclideanNorm (U.indicator H x))) := by
  obtain ⟨C₃, hC₃, h3⟩ := interiorReverseHolder hd hΛ
  obtain ⟨Cv, hCv, hSP⟩ := sobolevPoincare_of_vanishing hd
  have hd0 : 0 < d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set Cb := boundaryCaccioppoliConstant d Λ c with hCbdef
  have hCb : 0 < Cb := boundaryCaccioppoliConstant_pos d hΛ hc
  have hcm : 0 ≤ c ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hc.le _
  have h2d : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  have h3d : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
  have h4d : (1 : ℝ) ≤ 4 ^ d := one_le_pow₀ (by norm_num)
  have hc1' : 1 ≤ 1 / c := by rw [le_div_iff₀ hc]; linarith
  have h2c : 1 ≤ 2 ^ d / c := by rw [le_div_iff₀ hc]; nlinarith
  set Mu := 1 / c * ((1 + c ^ (-(1 : ℝ) / 2)) * Cv) * 2 ^ d with hMu
  set MH := 2 ^ d / c with hMH
  have hMu0 : 0 ≤ Mu := by positivity
  have hMH0 : 0 ≤ MH := by positivity
  set K₁ := C₃ * 4 ^ d with hK₁
  set K₂ := 3 ^ d * Cb * (Mu + MH) with hK₂
  have hK₁0 : 0 < K₁ := by positivity
  have hK₂0 : 0 ≤ K₂ := by positivity
  refine ⟨K₁ + K₂, by positivity, fun a u g H hu hH hdiv y ρ hρ hρR => ?_⟩
  set P := ENNReal.ofReal (2 * d / (d + 2)) with hPdef
  have hP1 : (1 : ℝ≥0∞) ≤ P := by
    rw [hPdef, ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ (by linarith)]
    linarith
  set F₁ := fun x => euclideanNorm (U.indicator g x) with hF₁
  set G₁ := fun x => euclideanNorm (U.indicator H x) with hG₁
  set A := PDE.eLpMeanNormOn (ball y ρ) P F₁ with hAdef
  set Bn := PDE.eLpMeanNormOn (ball y ρ) 2 G₁ with hBndef
  have hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U) := fun i => MemLp.eval hu.2.1 i
  have hdivf : HasWeakDivergence U (fun x => (a x).mulVec (g x) + H x)
      (fun x => -(fun _ : Vec d => (0 : ℝ)) x) := by simpa using hdiv
  have hρ8 : 0 < ρ / 8 := by linarith
  have hρ4 : 0 < ρ / 4 := by linarith
  have hKle : ∀ X Y : ℝ≥0∞, ENNReal.ofReal K₁ * (X + Y) ≤ ENNReal.ofReal (K₁ + K₂) * (X + Y) ∧
      ENNReal.ofReal K₂ * (X + Y) ≤ ENNReal.ofReal (K₁ + K₂) * (X + Y) := fun X Y =>
    ⟨by gcongr; linarith, by gcongr; linarith⟩
  by_cases h0 : volume (ball y (ρ / 8) ∩ U) = 0
  · -- `|∇u|` vanishes almost everywhere on `B_{ρ/8}(y)`
    have hz : PDE.eLpMeanNormOn (ball y (ρ / 8)) 2 F₁ = 0 := by
      have hF1 : F₁ = U.indicator (fun x => euclideanNorm (g x)) := by
        funext x
        by_cases hx : x ∈ U
        · simp only [hF₁, indicator_of_mem hx]
        · show euclideanNorm (U.indicator g x) = U.indicator (fun x => euclideanNorm (g x)) x
          rw [euclideanNorm_indicator_of_notMem hx, indicator_of_notMem hx]
      rw [hF1, PDE.eLpMeanNormOn, eLpNorm_indicator_eq_eLpNorm_restrict hUo.measurableSet,
        PDE.normalizedVolumeOn, Measure.restrict_smul, Measure.restrict_restrict hUo.measurableSet,
        Measure.restrict_eq_zero.mpr (by rwa [inter_comm] at h0), smul_zero, eLpNorm_measure_zero]
    rw [hz]
    exact zero_le
  by_cases hI : ball y (ρ / 4) ⊆ U
  · -- interior balls: Corollary C.3
    have hB8U : ball y (ρ / 8) ⊆ U := (ball_subset_ball_of_norm (by
      have : euclideanNorm (y - y) = 0 := by simp [euclideanNorm, euclideanSq, dot]
      linarith)).trans hI
    have hres : volume.restrict (ball y (ρ / 4)) ≤ volume.restrict U :=
      Measure.restrict_mono hI le_rfl
    have h := h3 y (ρ / 4) hρ4 a u g (fun _ => 0) H (hu.1.mono_measure hres)
      (fun i => (hg i).mono_measure hres) (hasWeakGradient_mono hI hu.2.2.1) MemLp.zero
      (fun i => (hH i).mono_measure hres) (hdivf.mono' hI)
    rw [show ρ / 4 / 2 = ρ / 8 by ring] at h
    have hB8m : MeasurableSet (ball y (ρ / 8)) := (isOpen_ball' y hρ8).measurableSet
    have hB4m : MeasurableSet (ball y (ρ / 4)) := (isOpen_ball' y hρ4).measurableSet
    have hlhs : PDE.eLpMeanNormOn (ball y (ρ / 8)) 2 F₁ =
        ENNReal.ofReal (vectorRms volume (ball y (ρ / 8)) g) := by
      rw [hF₁, eLpMeanNormOn_indicator_eq hB8U hB8m g 2]
      exact eLpMeanNormOn_two_euclideanNorm_eq (volume_ball_ne_zero' y hρ8)
        fun i => (hg i).mono_measure (Measure.restrict_mono hB8U le_rfl)
    have hv4 : volume (ball y ρ) ≤ ENNReal.ofReal (4 ^ d) * volume (ball y (ρ / 4)) := by
      have e := volume_ball_le_mul y y hρ4 (by norm_num : (0 : ℝ) < 4)
      rw [show 4 * (ρ / 4) = ρ by ring] at e
      exact e.le
    have hsub4 : ball y (ρ / 4) ⊆ ball y ρ := ball_subset_ball_of_norm (by
      have : euclideanNorm (y - y) = 0 := by simp [euclideanNorm, euclideanSq, dot]
      linarith)
    have hgP : PDE.eLpMeanNormOn (ball y (ρ / 4)) P (fun x => euclideanNorm (g x)) ≤
        ENNReal.ofReal (4 ^ d) * A := by
      rw [← eLpMeanNormOn_indicator_eq hI hB4m g P]
      exact eLpMeanNormOn_le_of_volume_le hsub4 (volume_ball_ne_zero' y hρ4)
        (volume_ball_ne_top' y ρ) h4d hv4 hP1 _
    have hHn : negativeSobolevOneNorm 2 (ball y (ρ / 4)) (fun _ => 0) H ≤
        ENNReal.ofReal (4 ^ d) * Bn := by
      refine (negativeSobolevOneNorm_two_zero_le (volume_ball_ne_zero' y hρ4)
        fun i => (hH i).mono_measure hres).trans ?_
      rw [← eLpMeanNormOn_indicator_eq hI hB4m H 2]
      exact eLpMeanNormOn_le_of_volume_le hsub4 (volume_ball_ne_zero' y hρ4)
        (volume_ball_ne_top' y ρ) h4d hv4 one_le_two _
    rw [hlhs]
    refine h.trans ?_
    refine le_trans ?_ (hKle A Bn).1
    calc ENNReal.ofReal C₃ * (PDE.eLpMeanNormOn (ball y (ρ / 4)) P (fun x => euclideanNorm (g x)) +
          negativeSobolevOneNorm 2 (ball y (ρ / 4)) (fun _ => 0) H)
        ≤ ENNReal.ofReal C₃ * (ENNReal.ofReal (4 ^ d) * A + ENNReal.ofReal (4 ^ d) * Bn) := by
          gcongr
      _ = ENNReal.ofReal K₁ * (A + Bn) := by
          rw [hK₁, ENNReal.ofReal_mul hC₃.le]
          ring
  · -- boundary balls: Lemma C.8 at a boundary point
    have hne : (ball y (ρ / 4) ∩ U).Nonempty := by
      obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero h0
      exact ⟨x, (ball_subset_ball_of_norm (by
        have : euclideanNorm (y - y) = 0 := by simp [euclideanNorm, euclideanSq, dot]
        linarith) : ball y (ρ / 8) ⊆ ball y (ρ / 4)) hx.1, hx.2⟩
    obtain ⟨z', hz', hz'B⟩ := exists_mem_frontier_of_not_subset hUo (isPreconnected_ball y hρ4)
      hne hI
    have hzy : euclideanNorm (z' - y) < ρ / 4 := hz'B
    set r' := 3 * ρ / 4 with hr'def
    have hr' : 0 < r' := by positivity
    have hr'R : r' ≤ R₀ := by linarith
    have hr'2R : r' / 2 ≤ R₀ := by linarith
    obtain ⟨hcacc, hW0⟩ := boundaryCaccioppoli_of_density hd0 hΛ hUo a hu MemLp.zero hH hdivf
      hc hden hz' hr' hr'2R
    obtain ⟨hdenI, hdenE⟩ := hden z' hz' r' hr' hr'R
    have hVt : volume (ball z' r' ∩ U) ≠ ⊤ :=
      ne_top_of_le_ne_top (volume_ball_ne_top' z' r') (measure_mono inter_subset_left)
    have hBr'pos : 0 < volume.real (ball z' r') := by
      rw [volume_real_ball_eq z' hr']
      exact mul_pos (pow_pos hr' d) (PDE.volume_euclideanBall_toReal_pos 0 one_pos)
    have hV0 : volume (ball z' r' ∩ U) ≠ 0 := by
      intro h0'
      have : volume.real (ball z' r' ∩ U) = 0 := by rw [measureReal_def, h0', ENNReal.toReal_zero]
      nlinarith
    have hVU : ball z' r' ∩ U ⊆ U := inter_subset_right
    have hVm : MeasurableSet (ball z' r' ∩ U) := ((isOpen_ball' z' hr').inter hUo).measurableSet
    have hres : volume.restrict (ball z' r' ∩ U) ≤ volume.restrict U :=
      Measure.restrict_mono hVU le_rfl
    -- the balls
    have hsubB : ball z' r' ⊆ ball y ρ := ball_subset_ball_of_norm (by linarith)
    have hsub8 : ball y (ρ / 8) ⊆ ball z' (3 * (ρ / 8)) := ball_subset_ball_of_norm (by
      have := euclideanNorm_sub_comm' y z'
      linarith)
    have hr'half : 3 * (ρ / 8) = r' / 2 := by rw [hr'def]; ring
    -- (a) the left-hand side
    have hW'm : MeasurableSet (ball z' (r' / 2) ∩ U) :=
      ((isOpen_ball' z' (by linarith)).inter hUo).measurableSet
    have hlhs : PDE.eLpMeanNormOn (ball y (ρ / 8)) 2 F₁ ≤
        ENNReal.ofReal (3 ^ d) * ENNReal.ofReal (vectorRms volume (ball z' (r' / 2) ∩ U) g) := by
      have hv3 : volume (ball z' (3 * (ρ / 8))) ≤
          ENNReal.ofReal (3 ^ d) * volume (ball y (ρ / 8)) :=
        (volume_ball_le_mul y z' hρ8 (by norm_num : (0 : ℝ) < 3)).le
      refine (eLpMeanNormOn_le_of_volume_le hsub8 (volume_ball_ne_zero' y hρ8)
        (volume_ball_ne_top' z' _) h3d hv3 one_le_two F₁).trans ?_
      gcongr
      rw [hr'half]
      refine (eLpMeanNormOn_le_of_eq_zero_off inter_subset_left hW'm
        (isOpen_ball' z' (by linarith)).measurableSet (volume_ball_ne_top' z' _)
        (fun x hx => ?_) 2).trans ?_
      · exact euclideanNorm_indicator_of_notMem fun hxU => hx.2 ⟨hx.1, hxU⟩
      · rw [hF₁, eLpMeanNormOn_indicator_eq inter_subset_right hW'm g 2]
        exact (eLpMeanNormOn_two_euclideanNorm_eq hW0 fun i => (hg i).mono_measure
          (Measure.restrict_mono inter_subset_right le_rfl)).le
    -- (b) the term of `H`
    have hvH : volume (ball y ρ) ≤ ENNReal.ofReal MH * volume (ball z' r' ∩ U) := by
      refine volume_le_ofReal_mul_of_real (volume_ball_ne_top' y ρ) hVt hMH0 ?_
      rw [volume_real_ball_eq y hρ]
      rw [volume_real_ball_eq z' hr'] at hdenI
      have hω := PDE.volume_euclideanBall_toReal_pos (0 : Vec d) one_pos
      have hpow : ρ ^ d ≤ 2 ^ d * r' ^ d := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ hρ.le (by rw [hr'def]; linarith) d
      rw [hMH, div_mul_eq_mul_div, le_div_iff₀ hc]
      calc ρ ^ d * (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal * c
          ≤ 2 ^ d * r' ^ d * (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal * c := by
            gcongr
        _ = 2 ^ d * (c * (r' ^ d * (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal)) := by
            ring
        _ ≤ 2 ^ d * volume.real (ball z' r' ∩ U) := by gcongr
    have hHterm : negativeSobolevOneNorm 2 (ball z' r' ∩ U) (fun _ => 0) H ≤
        ENNReal.ofReal MH * Bn := by
      refine (negativeSobolevOneNorm_two_zero_le hV0 fun i => (hH i).mono_measure hres).trans ?_
      rw [← eLpMeanNormOn_indicator_eq hVU hVm H 2]
      exact eLpMeanNormOn_le_of_volume_le (inter_subset_left.trans hsubB) hV0
        (volume_ball_ne_top' y ρ) h2c hvH one_le_two _
    -- (c) the term of `u`
    have hv1c : volume (ball z' r') ≤ ENNReal.ofReal (1 / c) * volume (ball z' r' ∩ U) := by
      refine volume_le_ofReal_mul_of_real (M := 1 / c) (volume_ball_ne_top' z' r') hVt
        (by positivity) ?_
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc, mul_comm]
      exact hdenI
    have hv2 : volume (ball y ρ) ≤ ENNReal.ofReal (2 ^ d) * volume (ball z' r') := by
      have e := volume_ball_le_mul z' y hr' (by norm_num : (0 : ℝ) < 4 / 3)
      rw [show 4 / 3 * r' = ρ by rw [hr'def]; ring] at e
      rw [e]
      gcongr
      norm_num
    have hsp := hSP U hUo u g hu z' r' hr' c hc hdenE
    have huterm : ENNReal.ofReal (r'⁻¹ * scalarRms volume (ball z' r' ∩ U) u) ≤
        ENNReal.ofReal Mu * A := by
      rw [ENNReal.ofReal_mul (inv_nonneg.mpr hr'.le),
        ← eLpMeanNormOn_two_eq_ofReal_scalarRms hV0 (hu.1.mono_measure hres),
        ← eLpMeanNormOn_indicator_eq' hVU hVm u 2]
      have h1 := eLpMeanNormOn_le_of_volume_le inter_subset_left hV0 (volume_ball_ne_top' z' r')
        hc1' hv1c one_le_two (U.indicator u)
      have h2 := eLpMeanNormOn_le_of_volume_le hsubB (volume_ball_ne_zero' z' hr')
        (volume_ball_ne_top' y ρ) h2d hv2 hP1 F₁
      calc ENNReal.ofReal r'⁻¹ * PDE.eLpMeanNormOn (ball z' r' ∩ U) 2 (U.indicator u)
          ≤ ENNReal.ofReal r'⁻¹ * (ENNReal.ofReal (1 / c) * (ENNReal.ofReal
              ((1 + c ^ (-(1 : ℝ) / 2)) * Cv * r') * (ENNReal.ofReal (2 ^ d) * A))) := by
            exact mul_le_mul_right (h1.trans (mul_le_mul_right (hsp.trans
              (mul_le_mul_right h2 _)) _)) _
        _ = ENNReal.ofReal Mu * A := by
            rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), hMu]
            congr 2
            field_simp
    -- assembly
    refine hlhs.trans ?_
    refine le_trans ?_ (hKle A Bn).2
    calc ENNReal.ofReal (3 ^ d) * ENNReal.ofReal (vectorRms volume (ball z' (r' / 2) ∩ U) g)
        ≤ ENNReal.ofReal (3 ^ d) * (ENNReal.ofReal Cb *
            (ENNReal.ofReal Mu * A + ENNReal.ofReal MH * Bn)) := by
          gcongr
          exact hcacc.trans (by gcongr; exact hHterm)
      _ ≤ ENNReal.ofReal (3 ^ d) * (ENNReal.ofReal Cb *
            (ENNReal.ofReal (Mu + MH) * (A + Bn))) := by
          gcongr
          rw [ENNReal.ofReal_add hMu0 hMH0, add_mul, mul_add, mul_add]
          gcongr
          · exact le_self_add
          · exact le_add_self
      _ = ENNReal.ofReal K₂ * (A + Bn) := by
          rw [hK₂, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
          ring

end QSH
