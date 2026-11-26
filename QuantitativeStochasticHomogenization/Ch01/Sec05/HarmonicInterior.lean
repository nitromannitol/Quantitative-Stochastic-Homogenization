import QuantitativeStochasticHomogenization.Ch01.Sec05.LinearImage
import QuantitativeStochasticHomogenization.Ch03.Sec03.WeakRestriction
import QuantitativeStochasticHomogenization.AppB.SobolevSpaces
import PDEFoundation.PDE.HarmonicDerivativeBounds
import PDEFoundation.PDE.HarmonicBochner
import PDEFoundation.PDE.HarmonicWeylRepresentative
import PDEFoundation.PDE.HarmonicMollified

/-!
# Interior derivative bounds for harmonic functions of `H¹`

A square-integrable function `u` with square-integrable weak gradient `g` on an open set `S`
which is weakly harmonic has, for every `δ > 0`, the smooth mollification
`v = ρ_δ ⋆ 1_S u` (`PDE.harmonicMollify`), which is classically harmonic at the points `y` with
`B_δ(y) ⊆ S`. Its coordinate derivatives are the mollifications of the weak derivatives,
`∂_a v(z) = ∫_S g_a(y) ρ_δ(z - y) dy` (`euclideanCoordDeriv_harmonicMollify_eq`), so
`|∂_a v(z)| ≤ ‖ρ_δ‖_{L²} ‖g_a‖_{L²(S)} = δ^{-d/2} ‖ρ_1‖_{L²} ‖g_a‖_{L²(S)}`, and the derivative
bounds for harmonic functions of the elliptic regularity library
(`PDE.abs_iteratedCoordDeriv_le_of_harmonicOn`) applied to the harmonic function `∂_a v` give
`|∂^β ∂_a v(y₀)| ≤ C δ^{-|β| - d/2} ‖g‖_{L²(S)}` when `B_{4δ}(y₀) ⊆ S`. By Weyl's lemma
(`PDE.exists_harmonicWeylRepresentative`), `v = u` almost everywhere on `B_δ(y₀)`
(`exists_smooth_harmonic_interior_bound`). This is the case `ā = Id` of the interior estimate
(1.61) of the proof of Theorem 1.17.
-/

open MeasureTheory Filter Set
open scoped Convolution

noncomputable section

namespace QSH

namespace TwoScale

variable {d : ℕ}

theorem hasWeakDivergence_mono {U V : Set (Vec d)} (hVU : V ⊆ U) {F : Vec d → Vec d}
    {h : Vec d → ℝ} (H : HasWeakDivergence U F h) : HasWeakDivergence V F h := by
  refine ⟨fun i => (H.1 i).mono_set hVU, H.2.1.mono_set hVU, fun ψ hψ => ?_⟩
  have hψU : IsSpatialTest U ψ := ⟨hψ.1, hψ.2.1, hψ.2.2.trans hVU⟩
  have h1 := H.2.2 ψ hψU
  have e : ∀ W : Set (Vec d), tsupport ψ ⊆ W →
      ∫ x in W, dot (F x) (gradient ψ x) = ∫ x, dot (F x) (gradient ψ x) := fun W hW => by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have hx' : x ∉ tsupport ψ := fun h => hx (hW h)
    unfold dot gradient
    exact Finset.sum_eq_zero fun k _ => by
      rw [coordinateDerivative_eq_zero_of_notMem_tsupport hx' k, mul_zero]
  rw [e V hψ.2.2, ← e U hψU.2.2, h1, setIntegral_eq_integral_of_tsupport_subset hψU.2.2,
    setIntegral_eq_integral_of_tsupport_subset hψ.2.2]

theorem euclideanBall_subset_of_lt {x y : Vec d} {r R : ℝ} (hr : 0 < r)
    (h : PDE.vecEuclideanNorm (y - x) + r ≤ R) :
    PDE.euclideanBall y r ⊆ PDE.euclideanBall x R := by
  intro z hz
  have hR : 0 < R := by linarith [PDE.vecEuclideanNorm_nonneg (y - x)]
  rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr] at hz
  rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR]
  have := PDE.vecEuclideanNorm_add_le (z - y) (y - x)
  rw [sub_add_sub_cancel] at this
  linarith

theorem locallyIntegrable_indicator_of_memLp {S : Set (Vec d)} (hS : IsOpen S) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict S)) : LocallyIntegrable (S.indicator u) volume :=
  ((memLp_indicator_iff_restrict hS.measurableSet).2 hu).locallyIntegrable (by norm_num)

theorem isSpatialTest_reflected_harmonicKernelScaled {S : Set (Vec d)} {δ : ℝ} (hδ : 0 < δ)
    {z : Vec d} (hz : PDE.euclideanBall z δ ⊆ S) :
    IsSpatialTest S (fun y => PDE.harmonicKernelScaled δ (z - y)) := by
  refine ⟨(PDE.harmonicKernelScaled_smooth δ).comp (contDiff_const.sub contDiff_id), ?_,
    (PDE.tsupport_reflected_harmonicKernelScaled_subset hδ).trans hz⟩
  change HasCompactSupport (PDE.harmonicKernelScaled δ ∘ Homeomorph.subLeft z)
  exact (PDE.harmonicKernelScaled_hasCompactSupport hδ).comp_homeomorph _

/-- **The derivative of the mollification is the mollification of the weak derivative**:
`∂_a (ρ_δ ⋆ 1_S u)(z) = ∫_S g_a(y) ρ_δ(z - y) dy` when `B_δ(z) ⊆ S`. -/
theorem euclideanCoordDeriv_harmonicMollify_eq {S : Set (Vec d)} (hS : IsOpen S)
    {u : Vec d → ℝ} {g : Vec d → Vec d} (hu : MemLp u 2 (volume.restrict S))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict S)) (hw : HasWeakGradient S u g)
    {δ : ℝ} (hδ : 0 < δ) {z : Vec d} (hz : PDE.euclideanBall z δ ⊆ S) (a : Fin d) :
    PDE.euclideanCoordDeriv a (PDE.harmonicMollify (toH1FunctionOn hu hg hw) δ) z =
      ∫ y in S, g y a * PDE.harmonicKernelScaled δ (z - y) := by
  have hloc := locallyIntegrable_indicator_of_memLp hS hu
  unfold PDE.harmonicMollify
  change PDE.euclideanCoordDeriv a
    (PDE.harmonicKernelScaled δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] S.indicator u) z = _
  rw [PDE.euclideanCoordDeriv_convolution_left (PDE.harmonicKernelScaled_hasCompactSupport hδ)
    (PDE.harmonicKernelScaled_smooth δ) hloc a]
  rw [convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [PDE.integral_mul_indicator_const_sub_eq_setIntegral hS.measurableSet z]
  have hψ := isSpatialTest_reflected_harmonicKernelScaled hδ hz
  have hwk := (hw a).2.2 _ hψ
  have hder : ∀ y, coordinateDerivative a (fun y => PDE.harmonicKernelScaled δ (z - y)) y =
      -PDE.euclideanCoordDeriv a (PDE.harmonicKernelScaled δ) (z - y) := fun y =>
    PDE.euclideanCoordDeriv_comp_const_sub (PDE.harmonicKernelScaled_smooth δ) z a y
  simp only [hder, mul_neg, integral_neg] at hwk
  linarith

/-- `‖ρ_δ‖²_{L²} = δ^{-d} ‖ρ_1‖²_{L²}`. -/
theorem integral_sq_harmonicKernelScaled {δ : ℝ} (hδ : 0 < δ) :
    ∫ y, PDE.harmonicKernelScaled (d := d) δ y ^ 2 =
      δ⁻¹ ^ d * ∫ y, PDE.harmonicKernel (d := d) y ^ 2 := by
  have e : (fun y => PDE.harmonicKernelScaled (d := d) δ y ^ 2) =
      fun y => (δ⁻¹ ^ d) ^ 2 * PDE.harmonicKernel (d := d) (δ⁻¹ • y) ^ 2 := by
    funext y
    unfold PDE.harmonicKernelScaled
    ring
  rw [e, integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg volume (fun y => PDE.harmonicKernel (d := d) y ^ 2)
      hδ.le]
  have hdim : Module.finrank ℝ (Vec d) = d := by simp [Vec]
  rw [hdim, smul_eq_mul, inv_pow]
  field_simp

theorem memLp_reflected_harmonicKernelScaled {S : Set (Vec d)} {δ : ℝ} (hδ : 0 < δ)
    (z : Vec d) :
    MemLp (fun y => PDE.harmonicKernelScaled (d := d) δ (z - y)) 2 (volume.restrict S) := by
  have h : HasCompactSupport (fun y => PDE.harmonicKernelScaled (d := d) δ (z - y)) := by
    change HasCompactSupport (PDE.harmonicKernelScaled δ ∘ Homeomorph.subLeft z)
    exact (PDE.harmonicKernelScaled_hasCompactSupport hδ).comp_homeomorph _
  exact (((PDE.harmonicKernelScaled_smooth δ).comp
    (contDiff_const.sub contDiff_id)).continuous.memLp_of_hasCompactSupport h).restrict S

/-- `|∂_a (ρ_δ ⋆ 1_S u)(z)| ≤ (δ^{-d} ‖ρ_1‖²_{L²})^{1/2} ‖g_a‖_{L²(S)}` when `B_δ(z) ⊆ S`. -/
theorem abs_euclideanCoordDeriv_harmonicMollify_le {S : Set (Vec d)} (hS : IsOpen S)
    {u : Vec d → ℝ} {g : Vec d → Vec d} (hu : MemLp u 2 (volume.restrict S))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict S)) (hw : HasWeakGradient S u g)
    {δ : ℝ} (hδ : 0 < δ) {z : Vec d} (hz : PDE.euclideanBall z δ ⊆ S) (a : Fin d) :
    |PDE.euclideanCoordDeriv a (PDE.harmonicMollify (toH1FunctionOn hu hg hw) δ) z| ≤
      Real.sqrt (∫ y in S, g y a ^ 2) *
        Real.sqrt (δ⁻¹ ^ d * ∫ y, PDE.harmonicKernel (d := d) y ^ 2) := by
  rw [euclideanCoordDeriv_harmonicMollify_eq hS hu hg hw hδ hz a]
  refine (abs_integral_mul_le_sqrt_mul_sqrt (hg a)
    (memLp_reflected_harmonicKernelScaled hδ z)).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
  rw [← integral_sq_harmonicKernelScaled hδ]
  have hint : Integrable (fun y => PDE.harmonicKernelScaled (d := d) δ (z - y) ^ 2) := by
    have h := (memLp_reflected_harmonicKernelScaled (S := univ) hδ z).integrable_sq
    rwa [Measure.restrict_univ] at h
  calc ∫ y in S, PDE.harmonicKernelScaled (d := d) δ (z - y) ^ 2
      ≤ ∫ y, PDE.harmonicKernelScaled (d := d) δ (z - y) ^ 2 :=
        setIntegral_le_integral hint (Eventually.of_forall fun _ => sq_nonneg _)
    _ = ∫ y, PDE.harmonicKernelScaled (d := d) δ y ^ 2 :=
        integral_sub_left_eq_self (fun y => PDE.harmonicKernelScaled (d := d) δ y ^ 2) volume z

/-- The value of the mollification only depends on the function in `B_δ(y)`. -/
theorem harmonicMollify_eq_of_subset {S B : Set (Vec d)} (hBS : B ⊆ S) (H : PDE.H1Function S)
    (HB : PDE.H1Function B) (hHB : ∀ y ∈ B, HB.toFun y = H.toFun y) {δ : ℝ} (hδ : 0 < δ)
    {y : Vec d} (hy : PDE.euclideanBall y δ ⊆ B) :
    PDE.harmonicMollify HB δ y = PDE.harmonicMollify H δ y := by
  rw [PDE.harmonicMollify_eq_integral, PDE.harmonicMollify_eq_integral]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  by_cases ht : PDE.harmonicKernelScaled (d := d) δ t = 0
  · simp [ht]
  · have htb := PDE.harmonicKernelScaled_tsupport_subset hδ (subset_tsupport _ ht)
    rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hδ, sub_zero] at htb
    have hyt : y - t ∈ B := hy (by
      rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hδ, sub_sub_cancel_left,
        PDE.vecEuclideanNorm_neg]
      exact htb)
    change PDE.harmonicKernelScaled δ t * B.indicator HB.toFun (y - t) =
      PDE.harmonicKernelScaled δ t * S.indicator H.toFun (y - t)
    rw [Set.indicator_of_mem hyt, Set.indicator_of_mem (hBS hyt), hHB _ hyt]

/-- **Interior bounds for weakly harmonic functions of `H¹`.** For `d ≥ 1` there is `C(d)` such
that for every open `S`, every `u ∈ L²(S)` with weak gradient `g ∈ L²(S)` and `∇·g = 0` weakly
in `S`, and every `δ > 0`, there is a smooth `v` with: for every `y₀` with `B_{4δ}(y₀) ⊆ S`,
`v = u` almost everywhere on `B_δ(y₀)`, and for `n ≤ 2`, `a ∈ {1, …, d}` and every multi-index
`β` of length `n`, `|∂^β ∂_a v(y₀)| ≤ C δ^{-n} (δ^{-d})^{1/2} ‖g_a‖_{L²(S)}`. -/
theorem exists_smooth_harmonic_interior_bound (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Set (Vec d)), IsOpen S → ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
      MemLp u 2 (volume.restrict S) →
      (∀ i, MemLp (fun x => g x i) 2 (volume.restrict S)) →
      HasWeakGradient S u g →
      HasWeakDivergence S (fun x => (1 : Mat d).mulVec (g x)) (fun _ => 0) →
      ∀ δ : ℝ, 0 < δ → ∃ v : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧
        ∀ y₀ : Vec d, PDE.euclideanBall y₀ (4 * δ) ⊆ S →
          (∀ᵐ y ∂(volume.restrict (PDE.euclideanBall y₀ δ)), v y = u y) ∧
          ∀ (a : Fin d) (n : ℕ), n ≤ 2 → ∀ ι : Fin n → Fin d,
            |PDE.iteratedCoordDeriv n ι (PDE.euclideanCoordDeriv a v) y₀| ≤
              C * δ⁻¹ ^ n * Real.sqrt (δ⁻¹ ^ d) * Real.sqrt (∫ y in S, g y a ^ 2) := by
  set K := PDE.harmonicKernelDerivConst d with hK
  have hK0 : 0 ≤ K := PDE.harmonicKernelDerivConst_nonneg
  set cK := ∫ y, PDE.harmonicKernel (d := d) y ^ 2 with hcK
  have hcK0 : 0 ≤ cK := integral_nonneg fun _ => sq_nonneg _
  refine ⟨(1 + K + (2 * K) ^ 2) * Real.sqrt cK, by positivity,
    fun S hS u g hu hg hw hdiv δ hδ => ?_⟩
  set H := toH1FunctionOn hu hg hw with hH
  have hsol := isWeakDivergenceFormSolutionOn_toH1FunctionOn hu hg hw hdiv
  set v := PDE.harmonicMollify H δ with hv
  have hvs : ContDiff ℝ (⊤ : ℕ∞) v := PDE.contDiff_harmonicMollify hS H hδ
  refine ⟨v, hvs, fun y₀ hy₀ => ⟨?_, fun a n hn ι => ?_⟩⟩
  · -- Weyl's lemma on `B_{4δ}(y₀)`
    set B := PDE.euclideanBall y₀ (4 * δ) with hB
    have hBo : IsOpen B := PDE.isOpen_euclideanBall _ _
    have huB : MemLp u 2 (volume.restrict B) := hu.mono_measure (Measure.restrict_mono hy₀ le_rfl)
    have hgB : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict B) := fun i =>
      (hg i).mono_measure (Measure.restrict_mono hy₀ le_rfl)
    have hwB : HasWeakGradient B u g := HasWeakGradient.mono hy₀ hw
    have hdivB := hasWeakDivergence_mono hy₀ hdiv
    set HB := toH1FunctionOn huB hgB hwB with hHB
    have hsolB := isWeakDivergenceFormSolutionOn_toH1FunctionOn huB hgB hwB hdivB
    obtain ⟨w, -, -, hwae, hwm⟩ :=
      PDE.exists_harmonicWeylRepresentative hd (by positivity : 0 < 4 * δ) HB hsolB
    have hsmall : PDE.euclideanBall y₀ δ ⊆ B := PDE.euclideanBall_mono hδ.le (by linarith)
    have hvw : ∀ y ∈ PDE.euclideanBall y₀ δ, v y = w y := by
      intro y hy
      have hy' := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hδ).1 hy
      rw [hwm y (hsmall hy) δ hδ (by linarith)]
      exact (harmonicMollify_eq_of_subset hy₀ H HB (fun _ _ => rfl) hδ
        (euclideanBall_subset_of_lt hδ (by linarith))).symm
    have hwae' : ∀ᵐ y ∂(volume.restrict (PDE.euclideanBall y₀ δ)), w y = u y :=
      ae_restrict_of_ae_restrict_of_subset hsmall hwae
    filter_upwards [hwae', ae_restrict_mem (PDE.isOpen_euclideanBall y₀ δ).measurableSet]
      with y hy hyB
    rw [hvw y hyB, hy]
  · -- the derivative bounds
    have hball : ∀ z, PDE.vecEuclideanNorm (z - y₀) ≤ 3 * δ →
        PDE.euclideanBall z δ ⊆ S := fun z hz =>
      (euclideanBall_subset_of_lt hδ (by linarith)).trans hy₀
    have hM : ∀ z ∈ PDE.euclideanClosedBall y₀ δ,
        |PDE.euclideanCoordDeriv a v z| ≤
          Real.sqrt (∫ y in S, g y a ^ 2) * Real.sqrt (δ⁻¹ ^ d * cK) := by
      intro z hz
      rw [PDE.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hδ.le] at hz
      exact abs_euclideanCoordDeriv_harmonicMollify_le hS hu hg hw hδ (hball z (by linarith)) a
    have hsqrt : Real.sqrt (δ⁻¹ ^ d * cK) = Real.sqrt (δ⁻¹ ^ d) * Real.sqrt cK :=
      Real.sqrt_mul (by positivity) _
    set G := Real.sqrt (∫ y in S, g y a ^ 2) with hG
    have hG0 : 0 ≤ G := Real.sqrt_nonneg _
    have hδi : 0 ≤ δ⁻¹ := inv_nonneg.2 hδ.le
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      have h0 : PDE.vecEuclideanNorm (y₀ - y₀) = 0 := by
        rw [sub_self]
        change Real.sqrt (euclideanSq (0 : Vec d)) = 0
        simp [euclideanSq, dot]
      have h := hM y₀ (by
        rw [PDE.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hδ.le, h0]
        exact hδ.le)
      change |PDE.euclideanCoordDeriv a v y₀| ≤ _
      calc |PDE.euclideanCoordDeriv a v y₀|
          ≤ G * Real.sqrt (δ⁻¹ ^ d * cK) := h
        _ = 1 * (Real.sqrt cK * Real.sqrt (δ⁻¹ ^ d) * G) := by rw [hsqrt]; ring
        _ ≤ (1 + K + (2 * K) ^ 2) * (Real.sqrt cK * Real.sqrt (δ⁻¹ ^ d) * G) :=
            mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg K]) (by positivity)
        _ = (1 + K + (2 * K) ^ 2) * Real.sqrt cK * δ⁻¹ ^ 0 * Real.sqrt (δ⁻¹ ^ d) * G := by ring
    · have hharm : ∀ y ∈ PDE.euclideanBall y₀ (3 * δ), PDE.euclideanCoordLaplacian v y = 0 := by
        intro y hy
        rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)] at hy
        exact PDE.euclideanCoordLaplacian_harmonicMollify_eq_zero hS H hsol hδ
          (hball y hy.le)
      have hharm' : ∀ y ∈ PDE.euclideanBall y₀ (3 * δ),
          PDE.euclideanCoordLaplacian (PDE.euclideanCoordDeriv a v) y = 0 := fun y hy =>
        PDE.euclideanCoordLaplacian_euclideanCoordDeriv_eq_zero hvs
          (PDE.isOpen_euclideanBall _ _) hharm hy a
      have h := PDE.abs_iteratedCoordDeriv_le_of_harmonicOn hd
        (PDE.contDiff_euclideanCoordDeriv hvs a).contDiffOn hharm' hδ (by linarith) hM n hnpos ι
      refine h.trans ?_
      rw [hsqrt]
      have hn2 : (n : ℝ) ≤ 2 := by exact_mod_cast hn
      have hKn : (K * n / δ) ^ n ≤ (1 + K + (2 * K) ^ 2) * δ⁻¹ ^ n := by
        rw [div_eq_mul_inv, mul_pow]
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hδi n)
        interval_cases n
        · simp only [Nat.cast_one, mul_one, pow_one]
          nlinarith [sq_nonneg K]
        · simp only [Nat.cast_ofNat]
          nlinarith [sq_nonneg K]
      calc (K * n / δ) ^ n * (G * (Real.sqrt (δ⁻¹ ^ d) * Real.sqrt cK))
          ≤ (1 + K + (2 * K) ^ 2) * δ⁻¹ ^ n * (G * (Real.sqrt (δ⁻¹ ^ d) * Real.sqrt cK)) :=
            mul_le_mul_of_nonneg_right hKn (by positivity)
        _ = (1 + K + (2 * K) ^ 2) * Real.sqrt cK * δ⁻¹ ^ n * Real.sqrt (δ⁻¹ ^ d) * G := by ring

end TwoScale

end QSH
