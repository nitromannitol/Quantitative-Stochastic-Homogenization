import QuantitativeStochasticHomogenization.AppC.GlobalReverseHolder

/-!
# The global Meyers estimate

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix C, Theorem C.7: for `p ∈ (2, ∞)`, a bounded Lipschitz domain `U`, `h ∈ W^{-1,p}(U)`,
`f ∈ W^{1,p}(U)` and the solution `u ∈ f + H¹₀(U)` of `-∇·(a∇u) = h`, there are `δ(U, d, Λ) > 0`
and `C(U, d, Λ)` with
`‖∇u‖_{L̲^{(2+δ)∧p}(U)} ≤ C (‖∇f‖_{L̲^{(2+δ)∧p}(U)} + ‖h‖_{W̲^{-1,(2+δ)∧p}(U)})` (C.15).

The book reduces to `f = 0` and proves it from (C.17), Corollary C.9 and Lemma C.4 as Theorem C.1.
This file proves the case `f = 0` (`theorem_C_7_zero_of_boundaryDensity`) on a domain `U ⊆ B_R`
with boundary density `c` up to the scale `2R`, which bounded Lipschitz domains have:
* Remark B.6 on `U` writes `h = ∇·H` with `‖H‖_{L̲^s(U)} ≤ C ‖h‖_{W̲^{-1,s}(U)}`,
  `s = (2+δ) ∧ p`;
* the zero extensions of `|∇u|` and `|H|` satisfy the reverse Hölder inequality from
  `B_{ρ/8}(y)` to `B_ρ(y)` (`reverseHolder_eighth_global`), hence, by the covering argument
  `reverseHolder_half_of_eighth`, the hypothesis of Lemma C.4 on `B_{2R}`;
* Lemma C.4 on `B_{2R}`, (C.17) and the bound on `H` give the estimate on `U ⊆ B_R`.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- A ball inside a ball has the smaller radius. -/
theorem radius_le_of_ball_subset (hd : 0 < d) {y z : Vec d} {ρ R : ℝ} (hρ : 0 < ρ) (hR : 0 < R)
    (hsub : ball y ρ ⊆ ball z R) : ρ ≤ R := by
  have h := measureReal_mono hsub (volume_ball_ne_top' z R)
  rw [volume_real_ball_eq y hρ, volume_real_ball_eq z hR] at h
  have hω := PDE.volume_euclideanBall_toReal_pos (0 : Vec d) one_pos
  have h' : ρ ^ d ≤ R ^ d := le_of_mul_le_mul_right h hω
  exact (pow_le_pow_iff_left₀ hρ.le hR.le (by omega)).mp h'

theorem euclideanNorm_indicator_eq {U : Set (Vec d)} (g : Vec d → Vec d) :
    (fun x => euclideanNorm (U.indicator g x)) = U.indicator (fun x => euclideanNorm (g x)) := by
  funext x
  by_cases hx : x ∈ U
  · simp only [indicator_of_mem hx]
  · rw [euclideanNorm_indicator_of_notMem hx, indicator_of_notMem hx]

theorem memLp_euclideanNorm_indicator {U B : Set (Vec d)} (hUm : MeasurableSet U) (hUB : U ⊆ B)
    {s : ℝ≥0∞} {G : Vec d → Vec d} (hG : ∀ i, MemLp (fun x => G x i) s (volume.restrict U)) :
    MemLp (fun x => euclideanNorm (U.indicator G x)) s (volume.restrict B) := by
  rw [euclideanNorm_indicator_eq, memLp_indicator_iff_restrict hUm,
    Measure.restrict_restrict hUm, inter_eq_left.mpr hUB]
  exact memLp_euclideanNorm_of_coord hG

/-- **Theorem C.7 (global Meyers estimate) for zero boundary data**, on a domain with boundary
density. For `d ≥ 2`, an open set `U ⊆ B_R` of positive measure with boundary density
`c ∈ (0, 1]` up to the scale `2R`, there are `δ > 0` and `C < ∞` (depending on `d`, `Λ`, `U`)
such that, for `p ∈ (2, ∞)`, `h = f + ∇·F ∈ W^{-1,p}(U)` with `f ∈ L²(U)`, `F ∈ L²(U; ℝ^d)` and
`u ∈ H¹₀(U)` solving `-∇·(a∇u) = h` in `U`,
`‖∇u‖_{L̲^{(2+δ)∧p}(U)} ≤ C ‖h‖_{W̲^{-1,(2+δ)∧p}(U)}`. -/
theorem theorem_C_7_zero_of_boundaryDensity (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {U : Set (Vec d)} (hUo : IsOpen U) (hU0 : volume U ≠ 0) {R c : ℝ} (hR : 0 < R)
    (hUR : U ⊆ ball 0 R) (hc : 0 < c) (hc1 : c ≤ 1) (hden : HasBoundaryDensity U c (2 * R)) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ p : ℝ, 2 < p → ∀ (a : CoefficientField d Λ)
      (u : Vec d → ℝ) (g : Vec d → Vec d) (f : Vec d → ℝ) (F : Vec d → Vec d),
      H01 U u g → MemLp f 2 (volume.restrict U) →
      (∀ i, MemLp (fun x => F x i) 2 (volume.restrict U)) →
      negativeSobolevOneNorm p U f F ≠ ⊤ →
      HasWeakDivergence U (fun x => (a x).mulVec (g x) + F x) (fun x => -f x) →
      PDE.eLpMeanNormOn U (ENNReal.ofReal (min (2 + δ) p)) (fun x => euclideanNorm (g x)) ≤
        ENNReal.ofReal C * negativeSobolevOneNorm (min (2 + δ) p) U f F := by
  have hd0 : 0 < d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hUb : Bornology.IsBounded U := (isBounded_ball 0 R).subset hUR
  have hUt : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hUm : MeasurableSet U := hUo.measurableSet
  have hR2 : 0 < 2 * R := by linarith
  have hUR2 : U ⊆ ball 0 (2 * R) := hUR.trans (ball_subset_ball_of_norm (by
    have : euclideanNorm ((0 : Vec d) - 0) = 0 := by simp [euclideanNorm, euclideanSq, dot]
    linarith))
  obtain ⟨C₀, hC₀, h17⟩ := lemma_C_8_energy hΛ hUo hUb hU0
  obtain ⟨K₈, hK₈, h8⟩ := reverseHolder_eighth_global hd hΛ hUo hc hc1 hden
  set s₀ : ℝ := 2 * d / (d + 2) with hs₀
  have hs₀2 : s₀ < 2 := by
    rw [hs₀, div_lt_iff₀ (by linarith)]
    linarith
  set q₀ : ℝ := max s₀ (3 / 2) with hq₀
  have hq01 : 1 < q₀ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hq02 : q₀ < 2 := max_lt hs₀2 (by norm_num)
  set K := max (10 ^ d * 2 ^ d * K₈) 1 with hKdef
  obtain ⟨δ, C₄, hδ, hδ1, hC₄, hG⟩ := lemma_C_4 (d := d) hq01 hq02
    (le_max_right (10 ^ d * 2 ^ d * K₈) (1 : ℝ))
  set CB := boundedDivergenceRepresentationConstant d U R with hCBdef
  have hCB : 0 ≤ CB := boundedDivergenceRepresentationConstant_nonneg d U hR.le
  set M := max (volume.real (ball (0 : Vec d) R) / volume.real U) 1 with hMdef
  have hM1 : 1 ≤ M := le_max_right _ _
  refine ⟨δ, M * C₄ * (C₀ + CB), hδ, by positivity, ?_⟩
  intro p hp a u g f F hu hf hF hfin hdiv
  set s := min (2 + δ) p with hsdef
  have hs2 : 2 < s := lt_min (by linarith) hp
  have hsp : s ≤ p := min_le_right _ _
  have hs1 : 1 < s := by linarith
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUt
  have hfin_s : negativeSobolevOneNorm s U f F ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (negativeSobolevOneNorm_mono_exponent hU0 hUt hs1 hsp f F)
  -- Remark B.6 on `U`
  obtain ⟨H, hHmem, hHpair, -, hHnorm⟩ := remark_B_6_of_subset_ball hd0 hUo hU0 0 hR hUR hs1
    (hf.integrable one_le_two) (fun i => (hF i).integrable one_le_two) hfin_s
  have hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U) := fun i => MemLp.eval hu.2.1 i
  have hA : ∀ i, MemLp (fun x => (a x).mulVec (g x) i) 2 (volume.restrict U) := by
    have hEll := isEllipticFieldOn_ellipticFieldOf hΛ a hUm
    have h := PDE.memVectorL2On_matVecMul_of_isEllipticFieldOn hEll (f := g) hg
    intro i
    refine (h i).ae_eq ?_
    filter_upwards [ae_restrict_of_ae (ellipticFieldOf_ae_eq hΛ a)] with x hx
    change ((ellipticFieldOf a x).mulVec (g x)) i = _
    rw [hx]
  have hs1' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal s := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hs1.le
  have hs2' : (2 : ℝ≥0∞) ≤ ENNReal.ofReal s := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal hs2.le
  have hdivH := hasWeakDivergence_of_representation hUt hs1' hA hF hf hHmem hdiv hHpair
  have hH2 : ∀ i, MemLp (fun x => H x i) 2 (volume.restrict U) :=
    fun i => (hHmem i).mono_exponent hs2'
  -- the zero extensions
  set F₁ := fun x => euclideanNorm (U.indicator g x) with hF₁
  set G₁ := fun x => euclideanNorm (U.indicator H x) with hG₁
  have hF₁m : MemLp F₁ 2 (volume.restrict (ball 0 (2 * R))) :=
    memLp_euclideanNorm_indicator hUm hUR2 hg
  have hG₁m : MemLp G₁ (ENNReal.ofReal s) (volume.restrict (ball 0 (2 * R))) :=
    memLp_euclideanNorm_indicator hUm hUR2 hHmem
  have hF₁meas : AEStronglyMeasurable F₁ volume := by
    rw [hF₁, euclideanNorm_indicator_eq, aestronglyMeasurable_indicator_iff hUm]
    exact (memLp_euclideanNorm_of_coord hg).aestronglyMeasurable
  -- the reverse Hölder inequality on every ball of `B_{2R}`
  have hq0' : ENNReal.ofReal s₀ ≤ ENNReal.ofReal q₀ := ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have h8' : ∀ (y : Vec d) (ρ : ℝ), 0 < ρ → ball y ρ ⊆ ball 0 (2 * R) →
      PDE.eLpMeanNormOn (ball y (ρ / 8)) 2 F₁ ≤ ENNReal.ofReal K₈ *
        (PDE.eLpMeanNormOn (ball y ρ) (ENNReal.ofReal q₀) F₁ +
          PDE.eLpMeanNormOn (ball y ρ) 2 G₁) := by
    intro y ρ hρ hsub
    have hρR := radius_le_of_ball_subset hd0 hρ hR2 hsub
    refine (h8 a u g H hu hH2 hdivH y ρ hρ hρR).trans ?_
    have : IsProbabilityMeasure (PDE.normalizedVolumeOn (ball y ρ)) :=
      PDE.isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top
        (pos_iff_ne_zero.mpr (volume_ball_ne_zero' y hρ)) (volume_ball_lt_top y ρ)
    gcongr
    exact eLpNorm_le_eLpNorm_of_exponent_le hq0'
  have hRH := reverseHolder_half_of_eighth hK₈.le hq01.le hF₁meas h8'
  have hRH' : ∀ (z : Vec d) (r : ℝ), 0 < r → ball z r ⊆ ball 0 (2 * R) →
      PDE.eLpMeanNormOn (ball z (r / 2)) 2 F₁ ≤ ENNReal.ofReal K *
        (PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal q₀) F₁ +
          PDE.eLpMeanNormOn (ball z r) 2 G₁) := by
    intro z r hr hsub
    refine (hRH z r hr hsub).trans ?_
    gcongr
    exact le_max_left _ _
  -- Gehring's lemma on `B_{2R}`
  have hgeh := hG s (2 * R) hs2 hR2 F₁ G₁ hF₁m hG₁m hRH'
  rw [show min (2 + δ) s = s from min_eq_right (min_le_left _ _),
    show 2 * R / 2 = R by ring] at hgeh
  -- back to `U`
  have hvolU : volume (ball (0 : Vec d) R) ≤ ENNReal.ofReal M * volume U := by
    refine volume_le_ofReal_mul_of_real (volume_ball_ne_top' 0 R) hUt (by positivity) ?_
    have hUpos : 0 < volume.real U := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos hU0 hUt
    calc volume.real (ball (0 : Vec d) R)
        = volume.real (ball (0 : Vec d) R) / volume.real U * volume.real U := by
          field_simp
      _ ≤ M * volume.real U := by gcongr; exact le_max_left _ _
  have hs1'' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal s := hs1'
  have hlhs : PDE.eLpMeanNormOn U (ENNReal.ofReal s) (fun x => euclideanNorm (g x)) ≤
      ENNReal.ofReal M * PDE.eLpMeanNormOn (ball 0 R) (ENNReal.ofReal s) F₁ := by
    rw [← eLpMeanNormOn_indicator_eq subset_rfl hUm g]
    exact eLpMeanNormOn_le_of_volume_le hUR hU0 (volume_ball_ne_top' 0 R) hM1 hvolU hs1'' _
  have hB2m : MeasurableSet (ball (0 : Vec d) (2 * R)) := (isOpen_ball' 0 hR2).measurableSet
  have hF₁U : PDE.eLpMeanNormOn (ball 0 (2 * R)) 2 F₁ ≤
      ENNReal.ofReal C₀ * negativeSobolevOneNorm s U f F := by
    refine (eLpMeanNormOn_le_of_eq_zero_off hUR2 hUm hB2m (volume_ball_ne_top' 0 (2 * R))
      (fun x hx => euclideanNorm_indicator_of_notMem hx.2) 2).trans ?_
    rw [eLpMeanNormOn_indicator_eq subset_rfl hUm g 2,
      eLpMeanNormOn_two_euclideanNorm_eq hU0 hg]
    refine (h17 a u g f F hu hf hF hdiv).trans ?_
    gcongr
    exact negativeSobolevOneNorm_mono_exponent hU0 hUt one_lt_two hs2.le f F
  have hG₁U : PDE.eLpMeanNormOn (ball 0 (2 * R)) (ENNReal.ofReal s) G₁ ≤
      ENNReal.ofReal CB * negativeSobolevOneNorm s U f F := by
    refine (eLpMeanNormOn_le_of_eq_zero_off hUR2 hUm hB2m (volume_ball_ne_top' 0 (2 * R))
      (fun x hx => euclideanNorm_indicator_of_notMem hx.2) _).trans ?_
    rw [eLpMeanNormOn_indicator_eq subset_rfl hUm H]
    exact hHnorm
  calc PDE.eLpMeanNormOn U (ENNReal.ofReal s) (fun x => euclideanNorm (g x))
      ≤ ENNReal.ofReal M * PDE.eLpMeanNormOn (ball 0 R) (ENNReal.ofReal s) F₁ := hlhs
    _ ≤ ENNReal.ofReal M * (ENNReal.ofReal C₄ * (ENNReal.ofReal C₀ *
          negativeSobolevOneNorm s U f F + ENNReal.ofReal CB *
            negativeSobolevOneNorm s U f F)) := by
        gcongr
        exact hgeh.trans (by gcongr)
    _ = ENNReal.ofReal (M * C₄ * (C₀ + CB)) * negativeSobolevOneNorm s U f F := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_add hC₀.le hCB]
        ring
