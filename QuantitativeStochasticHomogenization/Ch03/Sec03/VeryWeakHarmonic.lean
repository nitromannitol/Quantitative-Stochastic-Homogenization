import PDEFoundation.PDE.HarmonicWeylRepresentative
import QuantitativeStochasticHomogenization.Front.Notation

/-!
# Weyl's lemma for very weak harmonic functions on balls

A function `g` on a round ball `B` whose zero extension is locally integrable and which satisfies
`∫_B g Δψ = 0` for every smooth compactly supported `ψ` in `B` has a smooth classically harmonic
representative. The mollifications of `g` with the normalized round kernel are classically
harmonic on interior balls; by the mean value property of these mollifications any two
sufficiently small scales give the same value at an interior point; and the mollifications
converge to `g` almost everywhere. This is the argument of the Weyl lemma for `H¹` functions in
the elliptic regularity library, with the `H¹` hypothesis replaced by the very weak equation.
-/

open MeasureTheory Filter
open scoped Convolution Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- `g` is very weakly harmonic in `U`: `∫_U g Δψ = 0` for smooth compactly supported `ψ` in `U`. -/
def IsVeryWeakHarmonicOn (U : Set (Vec d)) (g : Vec d → ℝ) : Prop :=
  ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
    ∫ x in U, g x * PDE.euclideanCoordLaplacian ψ x = 0

/-- The mollification of the zero extension of `g` from `U` with the round kernel of radius `δ`. -/
def veryWeakMollify (U : Set (Vec d)) (g : Vec d → ℝ) (δ : ℝ) : Vec d → ℝ :=
  PDE.harmonicKernelScaled δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U.indicator g

theorem contDiff_veryWeakMollify {U : Set (Vec d)} {g : Vec d → ℝ}
    (hg : LocallyIntegrable (U.indicator g) volume) {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ (⊤ : ℕ∞) (veryWeakMollify U g δ) :=
  HasCompactSupport.contDiff_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (PDE.harmonicKernelScaled_hasCompactSupport hδ) (PDE.harmonicKernelScaled_smooth δ) hg

/-- Testing the very weak equation with a reflected kernel: the Laplacian of the convolution of
the zero extension vanishes. -/
theorem euclideanCoordLaplacian_convolution_indicator_eq_zero_of_veryWeak {U : Set (Vec d)}
    (hU : MeasurableSet U) {g : Vec d → ℝ} (hg : LocallyIntegrable (U.indicator g) volume)
    (hzero : IsVeryWeakHarmonicOn U g) {K : Vec d → ℝ} (hK_supp : HasCompactSupport K)
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (A : Vec d)
    (hsub : tsupport (fun y : Vec d => K (A - y)) ⊆ U) :
    PDE.euclideanCoordLaplacian
      (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U.indicator g) A = 0 := by
  set ψ : Vec d → ℝ := fun y => K (A - y) with hψdef
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hK.comp (contDiff_const.sub contDiff_id)
  have hψ_supp : HasCompactSupport ψ := by
    show HasCompactSupport (K ∘ Homeomorph.subLeft A)
    simpa [ψ, Function.comp_def] using hK_supp.comp_homeomorph (Homeomorph.subLeft A)
  have hweak_zero := hzero ψ hψ hψ_supp hsub
  have hweak_zero' : ∫ y in U, g y * PDE.euclideanCoordLaplacian K (A - y) ∂volume = 0 := by
    refine Eq.trans ?_ hweak_zero
    refine MeasureTheory.setIntegral_congr_fun hU fun y _ => ?_
    congr 1
    exact (PDE.euclideanCoordLaplacian_comp_const_sub hK A y).symm
  rw [PDE.euclideanCoordLaplacian_convolution_left hK_supp hK hg, MeasureTheory.convolution_def]
  simpa using
    (PDE.integral_mul_indicator_const_sub_eq_setIntegral hU A (PDE.euclideanCoordLaplacian K)
      g).trans hweak_zero'

theorem euclideanCoordLaplacian_veryWeakMollify_eq_zero {U : Set (Vec d)} (hU : MeasurableSet U)
    {g : Vec d → ℝ} (hg : LocallyIntegrable (U.indicator g) volume)
    (hzero : IsVeryWeakHarmonicOn U g) {x : Vec d} {δ : ℝ} (hδ : 0 < δ)
    (hball : PDE.euclideanBall x δ ⊆ U) :
    PDE.euclideanCoordLaplacian (veryWeakMollify U g δ) x = 0 := by
  unfold veryWeakMollify
  apply euclideanCoordLaplacian_convolution_indicator_eq_zero_of_veryWeak hU hg hzero
    (PDE.harmonicKernelScaled_hasCompactSupport hδ) (PDE.harmonicKernelScaled_smooth δ) x
  exact (PDE.tsupport_reflected_harmonicKernelScaled_subset hδ).trans hball

theorem euclideanBall_subset_euclideanBall_of_margin {x₀ x y : Vec d} {r δ R : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hR : 0 < R) (hmargin : δ + R < r - PDE.vecEuclideanNorm (x - x₀))
    (hy : y ∈ PDE.euclideanBall x R) :
    PDE.euclideanBall y δ ⊆ PDE.euclideanBall x₀ r := by
  have hyx := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mp hy
  apply PDE.euclideanBall_subset_of_center_norm_add_le hδ hr
  have hdecomp : y - x₀ = (y - x) + (x - x₀) := by abel
  have hnorm : PDE.vecEuclideanNorm (y - x₀) ≤
      PDE.vecEuclideanNorm (y - x) + PDE.vecEuclideanNorm (x - x₀) := by
    rw [hdecomp]
    exact PDE.vecEuclideanNorm_add_le _ _
  linarith

/-- At an interior point, any two sufficiently small scales give the same mollification. -/
theorem veryWeakMollify_eq_of_scales (hd : 0 < d) {x₀ x : Vec d} {r δ ε : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hε : 0 < ε) {g : Vec d → ℝ}
    (hg : LocallyIntegrable ((PDE.euclideanBall x₀ r).indicator g) volume)
    (hzero : IsVeryWeakHarmonicOn (PDE.euclideanBall x₀ r) g)
    (hmargin : δ + ε < r - PDE.vecEuclideanNorm (x - x₀)) :
    veryWeakMollify (PDE.euclideanBall x₀ r) g δ x =
      veryWeakMollify (PDE.euclideanBall x₀ r) g ε x := by
  set U := PDE.euclideanBall x₀ r with hUdef
  let m : ℝ := r - PDE.vecEuclideanNorm (x - x₀)
  let Rδ : ℝ := (ε + (m - δ)) / 2
  let Rε : ℝ := (δ + (m - ε)) / 2
  have hRδ : 0 < Rδ := by dsimp [Rδ, m]; linarith
  have hRε : 0 < Rε := by dsimp [Rε, m]; linarith
  have hεRδ : ε < Rδ := by dsimp [Rδ, m]; linarith
  have hδRε : δ < Rε := by dsimp [Rε, m]; linarith
  have hδmargin : δ + Rδ < m := by dsimp [Rδ, m]; linarith
  have hεmargin : ε + Rε < m := by dsimp [Rε, m]; linarith
  have hUm : MeasurableSet U := (PDE.isOpen_euclideanBall x₀ r).measurableSet
  have hδsmooth := contDiff_veryWeakMollify hg hδ
  have hεsmooth := contDiff_veryWeakMollify hg hε
  have hδharm : ∀ y ∈ PDE.euclideanBall x Rδ,
      PDE.euclideanCoordLaplacian (veryWeakMollify U g δ) y = 0 := fun y hy =>
    euclideanCoordLaplacian_veryWeakMollify_eq_zero hUm hg hzero hδ
      (euclideanBall_subset_euclideanBall_of_margin hr hδ hRδ hδmargin hy)
  have hεharm : ∀ y ∈ PDE.euclideanBall x Rε,
      PDE.euclideanCoordLaplacian (veryWeakMollify U g ε) y = 0 := fun y hy =>
    euclideanCoordLaplacian_veryWeakMollify_eq_zero hUm hg hzero hε
      (euclideanBall_subset_euclideanBall_of_margin hr hε hRε hεmargin hy)
  have hrepδ :
      (PDE.harmonicKernelScaled ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        veryWeakMollify U g δ) x = veryWeakMollify U g δ x := by
    simpa [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply] using
      (PDE.integral_harmonicKernelScaled_mul_eq_of_harmonicOn hd
        hδsmooth.contDiffOn hδharm hε hεRδ)
  have hrepε :
      (PDE.harmonicKernelScaled δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        veryWeakMollify U g ε) x = veryWeakMollify U g ε x := by
    simpa [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply] using
      (PDE.integral_harmonicKernelScaled_mul_eq_of_harmonicOn hd
        hεsmooth.contDiffOn hεharm hδ hδRε)
  calc
    veryWeakMollify U g δ x =
        (PDE.harmonicKernelScaled ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          veryWeakMollify U g δ) x := hrepδ.symm
    _ = (PDE.harmonicKernelScaled δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          veryWeakMollify U g ε) x :=
        PDE.harmonicScalarConvolution_double_comm
          (PDE.harmonicKernelScaled_hasCompactSupport hε)
          (PDE.harmonicKernelScaled_smooth ε).continuous
          (PDE.harmonicKernelScaled_hasCompactSupport hδ)
          (PDE.harmonicKernelScaled_smooth δ).continuous hg x
    _ = veryWeakMollify U g ε x := hrepε

theorem euclideanCoordLaplacian_eq_of_eqOn_open {f g : Vec d → ℝ} {U : Set (Vec d)}
    (hU : IsOpen U) (hfg : Set.EqOn f g U) {x : Vec d} (hx : x ∈ U) :
    PDE.euclideanCoordLaplacian f x = PDE.euclideanCoordLaplacian g x := by
  unfold PDE.euclideanCoordLaplacian
  apply Finset.sum_congr rfl
  intro i _
  unfold PDE.euclideanCoordSecondDeriv
  have hderiv : Set.EqOn (PDE.euclideanCoordDeriv i f) (PDE.euclideanCoordDeriv i g) U := by
    intro y hy
    unfold PDE.euclideanCoordDeriv
    have hev : f =ᶠ[𝓝 y] g := by
      filter_upwards [hU.mem_nhds hy] with z hz
      exact hfg hz
    rw [hev.fderiv_eq]
  have hev : PDE.euclideanCoordDeriv i f =ᶠ[𝓝 x] PDE.euclideanCoordDeriv i g := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hderiv hy
  exact congrArg (fun L : Vec d →L[ℝ] ℝ => L (PDE.basisVec i)) hev.fderiv_eq

/-- **Weyl's lemma for very weak harmonic functions** on a round ball: a very weakly harmonic
function with locally integrable zero extension has a smooth classically harmonic
representative. -/
theorem exists_harmonic_ae_eq_of_isVeryWeakHarmonicOn (hd : 0 < d) {x₀ : Vec d} {r : ℝ}
    (hr : 0 < r) {g : Vec d → ℝ}
    (hg : LocallyIntegrable ((PDE.euclideanBall x₀ r).indicator g) volume)
    (hzero : IsVeryWeakHarmonicOn (PDE.euclideanBall x₀ r) g) :
    ∃ v : Vec d → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) v (PDE.euclideanBall x₀ r) ∧
      (∀ y ∈ PDE.euclideanBall x₀ r, PDE.euclideanCoordLaplacian v y = 0) ∧
      (∀ᵐ y ∂(volume.restrict (PDE.euclideanBall x₀ r)), v y = g y) ∧
      (∀ y ∈ PDE.euclideanBall x₀ r, ∀ δ : ℝ, 0 < δ →
        2 * δ < r - PDE.vecEuclideanNorm (y - x₀) →
        v y = veryWeakMollify (PDE.euclideanBall x₀ r) g δ y) := by
  classical
  let U := PDE.euclideanBall x₀ r
  let m : Vec d → ℝ := fun y => r - PDE.vecEuclideanNorm (y - x₀)
  let η : Vec d → ℝ := fun y => m y / 4
  let v : Vec d → ℝ := fun y => if y ∈ U then veryWeakMollify U g (η y) y else 0
  have hU : IsOpen U := PDE.isOpen_euclideanBall x₀ r
  have hmargin {y : Vec d} (hy : y ∈ U) : 0 < m y := by
    have hynorm := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp hy
    dsimp [m]
    linarith
  have hη {y : Vec d} (hy : y ∈ U) : 0 < η y := by
    dsimp [η]
    linarith [hmargin hy]
  have hvalue : ∀ y ∈ U, ∀ δ : ℝ, 0 < δ → 2 * δ < m y → v y = veryWeakMollify U g δ y := by
    intro y hy δ hδ hδm
    have hηm : η y + δ < m y := by
      dsimp [η]
      have hm := hmargin hy
      linarith
    simpa [v, hy] using (veryWeakMollify_eq_of_scales hd hr (hη hy) hδ hg hzero hηm)
  have hlocal (y : Vec d) (hy : y ∈ U) :
      ∃ ρ : ℝ, 0 < ρ ∧ Set.EqOn v (veryWeakMollify U g (η y)) (PDE.euclideanBall y ρ) := by
    let ρ : ℝ := m y / 8
    have hρ : 0 < ρ := by dsimp [ρ]; linarith [hmargin hy]
    refine ⟨ρ, hρ, ?_⟩
    intro z hz
    have hzy := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).mp hz
    have hdecomp : z - x₀ = (z - y) + (y - x₀) := by abel
    have hnorm : PDE.vecEuclideanNorm (z - x₀) ≤
        PDE.vecEuclideanNorm (z - y) + PDE.vecEuclideanNorm (y - x₀) := by
      rw [hdecomp]
      exact PDE.vecEuclideanNorm_add_le _ _
    have hmz : m y - ρ < m z := by dsimp [m]; linarith
    have hzU : z ∈ U := by
      apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mpr
      dsimp [m, ρ] at hmz ⊢
      linarith [hmargin hy]
    apply hvalue z hzU (η y) (hη hy)
    dsimp [η, ρ] at hmz ⊢
    linarith [hmargin hy]
  have hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) v U := by
    apply hU.contDiffOn_iff.mpr
    intro y hy
    obtain ⟨ρ, hρ, heq⟩ := hlocal y hy
    have hev : v =ᶠ[𝓝 y] veryWeakMollify U g (η y) := by
      filter_upwards [(PDE.isOpen_euclideanBall y ρ).mem_nhds
        (PDE.center_mem_euclideanBall y hρ)] with z hz
      exact heq hz
    exact ((contDiff_veryWeakMollify hg (hη hy)).contDiffAt).congr_of_eventuallyEq hev
  have hharm : ∀ y ∈ U, PDE.euclideanCoordLaplacian v y = 0 := by
    intro y hy
    obtain ⟨ρ, hρ, heq⟩ := hlocal y hy
    rw [euclideanCoordLaplacian_eq_of_eqOn_open (PDE.isOpen_euclideanBall y ρ) heq
      (PDE.center_mem_euclideanBall y hρ)]
    apply euclideanCoordLaplacian_veryWeakMollify_eq_zero hU.measurableSet hg hzero (hη hy)
    have hηbound : η y + η y ≤ m y := by
      dsimp [η]
      linarith [hmargin hy]
    apply PDE.euclideanBall_subset_of_center_norm_add_le (hη hy) hr
    dsimp [m] at hηbound ⊢
    linarith [hη hy]
  have hae := PDE.ae_tendsto_harmonicKernelScaled_convolution_of_locallyIntegrable hg
  have haeeq : ∀ᵐ y ∂(volume.restrict U), v y = g y := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hU.measurableSet] with y hlim hy
    have hevent : (fun δ : ℝ => veryWeakMollify U g δ y) =ᶠ[𝓝[>] 0] (fun _ => v y) := by
      have hthreshold : 0 < m y / 2 := by linarith [hmargin hy]
      have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < m y / 2 :=
        (tendsto_id.mono_left nhdsWithin_le_nhds).eventually (Iio_mem_nhds hthreshold)
      filter_upwards [self_mem_nhdsWithin, hsmall] with δ hδ hδsmall
      exact (hvalue y hy δ hδ (by linarith)).symm
    have hlimv : Tendsto (fun δ : ℝ => veryWeakMollify U g δ y) (𝓝[>] 0) (𝓝 (v y)) :=
      Tendsto.congr' hevent.symm tendsto_const_nhds
    have hlimu : Tendsto (fun δ : ℝ => veryWeakMollify U g δ y) (𝓝[>] 0)
        (𝓝 (Set.indicator U g y)) := by
      simpa only [veryWeakMollify] using hlim
    have hvu : v y = Set.indicator U g y := tendsto_nhds_unique hlimv hlimu
    simpa [Set.indicator_of_mem hy] using hvu
  exact ⟨v, hsmooth, hharm, haeeq, hvalue⟩

end QSH
