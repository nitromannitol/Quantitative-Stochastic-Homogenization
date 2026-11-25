import QuantitativeStochasticHomogenization.Ch08.Sec01.ParabolicSolutions
import EllipticRegularity.Parabolic.Energy.Conclusion

/-!
# The weak slice identity and the energy identity for `∂ₜu = ∇·G`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 8.1, the computations in the proof of Lemma 8.1. For `u ∈ H¹_par(I × U)` with
`∂ₜu = ∇·G` weakly and `G ∈ L²(U × I; ℝ^d)`:

* `fluxWeakSlice`: for `ζ ∈ C¹_c(U)` and `s < t` in `I`,
  `∫_U u(t) ζ - ∫_U u(s) ζ = -∫_s^t ∫_U G · ∇ζ`;
* `fluxEnergyIdentity`: for a cutoff `φ` with compact support in `U × I`,
  `½ ∫_U φ(t)² u(t)² - ½ ∫_U φ(s)² u(s)² = ∫_s^t ∫_U u² φ ∂ₜφ - ∫_s^t ∫_U G · ∇(φ² u)`.

These are Lemmas 5.5 and 5.6 of the parabolic part of the elliptic regularity library, which
treats the flux `G = a∇u`; its proof of the energy identity goes through an abstract identity
(`PDE.Parabolic.Energy.Data.energy_identity`) valid for any square-integrable flux, which is used
here with `G`. The weak slice identity follows the library's proof with `G` in place of `a∇u`.
-/

open MeasureTheory Set Filter Topology Metric
open PDE.Parabolic.WeakSlice PDE.Parabolic.Energy

noncomputable section

namespace QSH

variable {d : ℕ} {U : Set (Vec d)} {I : Set ℝ}

/-- A square-integrable flux paired with the gradient of a `C¹` function with compact support in
`U` is integrable on `U × J` for every `J ⊆ I` of finite measure. -/
theorem integrableOn_dot_spaceGradC1 {G : Vec d × ℝ → Vec d}
    (hG : ∀ i, MemLp (fun z => G z i) 2 (volume.restrict (U ×ˢ I))) (hU : MeasurableSet U)
    {ζ : Vec d → ℝ} (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ) (hζU : tsupport ζ ⊆ U)
    {J : Set ℝ} (hJI : J ⊆ I) (hJm : MeasurableSet J) (hJ : volume J < ⊤) :
    IntegrableOn (fun z : Vec d × ℝ => dot (G z) (PDE.spaceGradC1 ζ z.1)) (U ×ˢ J) := by
  obtain ⟨W, -, hW⟩ := spaceGradC1_bound hζ hζc
  have hKJ : volume (tsupport ζ ×ˢ J) < ⊤ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top (hζc : IsCompact (tsupport ζ)).measure_lt_top hJ
  haveI : IsFiniteMeasure (volume.restrict (tsupport ζ ×ˢ J)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hKJ⟩
  have hsub : tsupport ζ ×ˢ J ⊆ U ×ˢ I := prod_mono hζU hJI
  have hK : IntegrableOn (fun z : Vec d × ℝ => ∑ i, G z i * PDE.spaceGradC1 ζ z.1 i)
      (tsupport ζ ×ˢ J) := by
    refine integrable_finsetSum _ fun i _ => ?_
    have h1 : Integrable (fun z => G z i) (volume.restrict (tsupport ζ ×ˢ J)) :=
      ((hG i).mono_measure (Measure.restrict_mono hsub le_rfl)).integrable (by norm_num)
    refine h1.mul_bdd ((spaceGradC1_continuous hζ i).comp continuous_fst).aestronglyMeasurable
      (c := W) (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs]
    exact hW i z.1
  refine hK.of_forall_sdiff_eq_zero (hU.prod hJm) ?_
  rintro ⟨x, τ⟩ ⟨hz, hn⟩
  have hx : x ∉ tsupport ζ := fun hx => hn ⟨hx, hz.2⟩
  simp [spaceGradC1_eq_zero_of_notMem hx]

/-- The flux slice `τ ↦ ∫_U G(x, τ) · ∇ζ(x) dx`. -/
def fluxSlice (U : Set (Vec d)) (G : Vec d × ℝ → Vec d) (ζ : Vec d → ℝ) (τ : ℝ) : ℝ :=
  ∫ x in U, dot (G (x, τ)) (PDE.spaceGradC1 ζ x)

/-- The weak formulation of `∂ₜu = ∇·G` tested against `θ(τ) ζ(x)`, after Fubini. -/
theorem fluxWeakTestIdentity (hU : IsOpen U) (hI : I.OrdConnected) (u : PDE.ParH1Function U I)
    {G : Vec d × ℝ → Vec d} (hG : ∀ i, MemLp (fun z => G z i) 2 (volume.restrict (U ×ˢ I)))
    (hu : IsParabolicFluxSolution U I u G) {ζ : Vec d → ℝ} (hζ : ContDiff ℝ 1 ζ)
    (hζc : HasCompactSupport ζ) (hζU : tsupport ζ ⊆ U) {p q : ℝ} (hp : p ∈ I) (hq : q ∈ I)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    (hθs : tsupport θ ⊆ Ioo p q) :
    ∫ τ in Ioo p q, PDE.Parabolic.slicePairing u ζ τ * deriv θ τ =
      ∫ τ in Ioo p q, fluxSlice U G ζ τ * θ τ := by
  set F : Vec d × ℝ → ℝ := fun z => dot (G z) (PDE.spaceGradC1 ζ z.1) with hF
  have hIoo : Ioo p q ⊆ I := fun τ hτ => hI.out hp hq ⟨hτ.1.le, hτ.2.le⟩
  have hIoo' : Ioo p q ⊆ interior I := interior_maximal hIoo isOpen_Ioo
  have hFint : IntegrableOn F (U ×ˢ Icc p q) :=
    integrableOn_dot_spaceGradC1 hG hU.measurableSet hζ hζc hζU (hI.out hp hq) measurableSet_Icc
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
  let φ : PDE.ParTestFunction U (interior I) :=
    { toFun := fun w : Vec d × ℝ => θ w.2 * ζ w.1
      contDiff := contDiff_prod hθ hζ
      hasCompactSupport := hasCompactSupport_prod hθc hζc
      tsupport_subset := tsupport_prod_subset.trans (prod_mono hζU (hθs.trans hIoo')) }
  obtain ⟨hint, hzero⟩ := hu φ
  have hφ : ∀ z, -(u.toFun z * PDE.parTimeDeriv φ.toFun z) +
      dot (G z) (PDE.parSpaceGrad φ.toFun z) = -(u.toFun z * (deriv θ z.2 * ζ z.1)) + θ z.2 * F z := by
    intro z
    show -(u.toFun z * PDE.parTimeDeriv (fun w : Vec d × ℝ => θ w.2 * ζ w.1) z) +
      dot (G z) (PDE.parSpaceGrad (fun w : Vec d × ℝ => θ w.2 * ζ w.1) z) = _
    rw [parTimeDeriv_prod hθ hζ, parSpaceGrad_prod hθ hζ, hF]
    simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hθbdd : ∃ C, ∀ w : ℝ, ‖θ w‖ ≤ C := hθ.continuous.bounded_above_of_compact_support hθc
  have hFθ : IntegrableOn (fun z : Vec d × ℝ => θ z.2 * F z) (U ×ˢ I) := by
    have h1 : IntegrableOn (fun z : Vec d × ℝ => θ z.2 * F z) (U ×ˢ Icc p q) := by
      obtain ⟨C, hC⟩ := hθbdd
      exact hFint.bdd_mul (f := fun z : Vec d × ℝ => θ z.2) (c := C)
        (hθ.continuous.comp continuous_snd).aestronglyMeasurable
        (Eventually.of_forall fun z => hC z.2)
    refine h1.of_forall_sdiff_eq_zero (hU.measurableSet.prod hI.measurableSet) ?_
    rintro ⟨x, τ⟩ ⟨hz, hn⟩
    have : τ ∉ tsupport θ := fun h' => hn ⟨hz.1, (hθs h').1.le, (hθs h').2.le⟩
    simp [image_eq_zero_of_notMem_tsupport this]
  have hA : IntegrableOn (fun z : Vec d × ℝ => u.toFun z * (deriv θ z.2 * ζ z.1)) (U ×ˢ I) := by
    have : (fun z : Vec d × ℝ => u.toFun z * (deriv θ z.2 * ζ z.1)) = fun z => θ z.2 * F z -
        (-(u.toFun z * PDE.parTimeDeriv φ.toFun z) + dot (G z) (PDE.parSpaceGrad φ.toFun z)) := by
      funext z
      rw [hφ z]
      ring
    rw [this]
    exact hFθ.sub hint
  have heq : ∫ z in U ×ˢ I, u.toFun z * (deriv θ z.2 * ζ z.1) =
      ∫ z in U ×ˢ I, θ z.2 * F z := by
    have h0 := hzero
    simp_rw [hφ] at h0
    have hAn : IntegrableOn (fun z : Vec d × ℝ => -(u.toFun z * (deriv θ z.2 * ζ z.1)))
        (U ×ˢ I) := hA.neg
    rw [integral_add hAn hFθ, integral_neg] at h0
    linarith
  obtain ⟨_, hfa⟩ := integral_prod_slices hA
  obtain ⟨_, hfb⟩ := integral_prod_slices hFθ
  rw [hfa, hfb] at heq
  have e1 : ∀ τ, ∫ x in U, u.toFun (x, τ) * (deriv θ τ * ζ x) =
      PDE.Parabolic.slicePairing u ζ τ * deriv θ τ := by
    intro τ
    unfold PDE.Parabolic.slicePairing
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  have e2 : ∀ τ, ∫ x in U, θ τ * F (x, τ) = fluxSlice U G ζ τ * θ τ := by
    intro τ
    unfold fluxSlice
    rw [integral_const_mul, mul_comm]
  simp only [e1, e2] at heq
  have r1 : ∀ f : ℝ → ℝ, (∀ τ, τ ∉ Ioo p q → f τ = 0) →
      ∫ τ in I, f τ = ∫ τ in Ioo p q, f τ := fun f hf =>
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hI.measurableSet hIoo
      fun τ hτ => hf τ hτ.2
  have hz : ∀ τ, τ ∉ Ioo p q → deriv θ τ = 0 := fun τ hτ =>
    image_eq_zero_of_notMem_tsupport (fun h' => hτ (hθs (tsupport_deriv_subset h')))
  have hz' : ∀ τ, τ ∉ Ioo p q → θ τ = 0 := fun τ hτ =>
    image_eq_zero_of_notMem_tsupport (fun h' => hτ (hθs h'))
  rw [r1 _ (fun τ hτ => by rw [hz τ hτ, mul_zero]),
    r1 _ (fun τ hτ => by rw [hz' τ hτ, mul_zero])] at heq
  exact heq

/-- **The weak slice identity** for `∂ₜu = ∇·G`: for `ζ ∈ C¹_c(U)` and `s < t` in `I`,
`∫_U u(t) ζ - ∫_U u(s) ζ = -∫_s^t ∫_U G · ∇ζ`. -/
theorem fluxWeakSlice (hU : IsOpen U) (hI : I.OrdConnected) (u : PDE.ParH1Function U I)
    {G : Vec d × ℝ → Vec d} (hG : ∀ i, MemLp (fun z => G z i) 2 (volume.restrict (U ×ˢ I)))
    (hu : IsParabolicFluxSolution U I u G) {ζ : Vec d → ℝ} (hζ : ContDiff ℝ 1 ζ)
    (hζc : HasCompactSupport ζ) (hζU : tsupport ζ ⊆ U) {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I)
    (hst : s < t) :
    IntegrableOn (fun z : Vec d × ℝ => dot (G z) (PDE.spaceGradC1 ζ z.1)) (U ×ˢ Ioc s t) ∧
      (∫ x in U, u.toFun (x, t) * ζ x) - (∫ x in U, u.toFun (x, s) * ζ x) =
        -∫ z in U ×ˢ Ioc s t, dot (G z) (PDE.spaceGradC1 ζ z.1) := by
  have hFint : IntegrableOn (fun z : Vec d × ℝ => dot (G z) (PDE.spaceGradC1 ζ z.1))
      (U ×ˢ Icc s t) :=
    integrableOn_dot_spaceGradC1 hG hU.measurableSet hζ hζc hζU (hI.out hs ht) measurableSet_Icc
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
  have hFIoc : IntegrableOn (fun z : Vec d × ℝ => dot (G z) (PDE.spaceGradC1 ζ z.1))
      (U ×ˢ Ioc s t) := hFint.mono_set (prod_mono subset_rfl Ioc_subset_Icc_self)
  refine ⟨hFIoc, ?_⟩
  obtain ⟨_, hfub⟩ := integral_prod_slices hFIoc
  obtain ⟨hgIcc, _⟩ := integral_prod_slices hFint
  have hgIoo : IntegrableOn (fluxSlice U G ζ) (Ioo s t) := hgIcc.mono_set Ioo_subset_Icc_self
  have hmc := PDE.Parabolic.slicePairing_continuousOn u hζ hζc hζU
  have hSub : Icc s t ⊆ I := hI.out hs ht
  let m' : ℝ → ℝ := fun τ => PDE.Parabolic.slicePairing u ζ (projIcc s t hst.le τ)
  have hm' : Continuous m' :=
    (hmc.mono hSub).comp_continuous continuous_projIcc.subtype_val
      (fun τ => (projIcc s t hst.le τ).2)
  have hdbr := dubois_reymond hst m' (fluxSlice U G ζ) hm' hgIoo (fun θ h1 h2 h3 => by
    have := fluxWeakTestIdentity hU hI u hG hu hζ hζc hζU hs ht h1 h2 h3
    rw [← this]
    refine setIntegral_congr_fun measurableSet_Ioo fun τ hτ => ?_
    simp only [m', projIcc_of_mem _ (Ioo_subset_Icc_self hτ)])
  simp only [m', projIcc_left, projIcc_right] at hdbr
  rw [hfub, integral_Ioc_eq_integral_Ioo]
  change _ - _ = -∫ τ in Ioo s t, fluxSlice U G ζ τ
  unfold PDE.Parabolic.slicePairing at hdbr
  linarith [hdbr]

/-- The mollified weak slice identity for `∂ₜu = ∇·G`, in the form of the abstract energy data. -/
theorem fluxSliceIdentity (hU : IsOpen U) (hI : I.OrdConnected) (u : PDE.ParH1Function U I)
    {G : Vec d × ℝ → Vec d} (hG : ∀ i, MemLp (fun z => G z i) 2 (volume.restrict (U ×ˢ I)))
    (hu : IsParabolicFluxSolution U I u G) {K1 : Set (Vec d)} (hK1m : MeasurableSet K1)
    (hK1U : K1 ⊆ U) {a' : ℝ} (ha' : 0 < a') {x : Vec d} (hball : closedBall x a' ⊆ K1)
    {τ1 τ2 : ℝ} (h1 : τ1 ∈ I) (h2 : τ2 ∈ I) (h12 : τ1 ≤ τ2) {G' : Vec d × ℝ → Vec d}
    (hG' : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)), ∀ i, G' z i = G z i) :
    (∫ y in K1, kern a' (x - y) * u.toFun (y, τ2)) -
        (∫ y in K1, kern a' (x - y) * u.toFun (y, τ1)) =
      ∫ z in K1 ×ˢ Ioc τ1 τ2, ∑ i, G' z i * fderiv ℝ (kern a') (x - z.1) (PDE.basisVec i) := by
  rcases h12.eq_or_lt with rfl | hlt
  · simp
  · obtain ⟨_, hws⟩ := fluxWeakSlice hU hI u hG hu (zeta_contDiff_one a' x)
      (zeta_hasCompactSupport ha' x) (zeta_tsupport_subset_U ha' hball hK1U) h1 h2 hlt
    rw [setIntegral_pairing ha' hball hU hK1m hK1U (fun y => u.toFun (y, τ2)),
      setIntegral_pairing ha' hball hU hK1m hK1U (fun y => u.toFun (y, τ1))] at hws
    rw [hws]
    have hdz : ∀ z : Vec d × ℝ, dot (G z) (PDE.spaceGradC1 (zeta a' x) z.1) =
        -∑ i, G z i * fderiv ℝ (kern a') (x - z.1) (PDE.basisVec i) := by
      intro z
      simp only [dot, PDE.spaceGradC1, fderiv_zeta, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [hdz]
    rw [integral_neg, neg_neg]
    have hsub : K1 ×ˢ Ioc τ1 τ2 ⊆ U ×ˢ Ioc τ1 τ2 := prod_mono hK1U subset_rfl
    rw [← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hU.measurableSet.prod measurableSet_Ioc)
      hsub]
    · have hsubI : U ×ˢ Ioc τ1 τ2 ⊆ U ×ˢ I :=
        prod_mono subset_rfl (fun τ hτ => hI.out h1 h2 ⟨hτ.1.le, hτ.2⟩)
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hsubI hG'] with z hz
      exact Finset.sum_congr rfl fun i _ => by rw [hz i]
    · rintro ⟨y, τ⟩ ⟨hyU, hn⟩
      have hyK : y ∉ K1 := fun hy => hn ⟨hy, hyU.2⟩
      have hy : y ∉ closedBall x a' := fun h => hyK (hball h)
      simp [fderiv_kern_eq_zero_of_lt_norm ha' (lt_norm_of_notMem_closedBall hy)]

/-- Bundling of a weak solution of `∂ₜu = ∇·G` into the abstract energy data. -/
theorem exists_fluxData (hU : IsOpen U) (hI : I.OrdConnected) (u : PDE.ParH1Function U I)
    {G : Vec d × ℝ → Vec d} (hG : ∀ i, MemLp (fun z => G z i) 2 (volume.restrict (U ×ˢ I)))
    (hu : IsParabolicFluxSolution U I u G) (φ : PDE.ParCutoff U I) {s t : ℝ} (hs : s ∈ I)
    (ht : t ∈ I) (hst : s < t) :
    ∃ D : Data d, D.u = u.toFun ∧ D.φ = φ.toFun ∧ D.s = s ∧ D.t = t ∧ D.K ⊆ U ∧
      (∀ x ∈ U, x ∉ D.K → ∀ τ ∈ I, φ.toFun (x, τ) = 0) ∧
      ∀ᵐ z ∂(volume.restrict (U ×ˢ I)),
        (∀ i, D.G z i = G z i) ∧ ∀ i, D.Du z i = u.grad z i := by
  obtain ⟨K, δ0, hKc, hKU, hδ0, hδ1, hcU, hφ0⟩ := exists_collar hU φ
  have hIcc : Icc s t ⊆ I := hI.out hs ht
  have hDuM : ∀ i, AEStronglyMeasurable (fun z => u.grad z i) (volume.restrict (U ×ˢ I)) :=
    fun i => (u.gradMemL2 i).aestronglyMeasurable
  have hFM : ∀ i, AEStronglyMeasurable (fun z => G z i) (volume.restrict (U ×ˢ I)) :=
    fun i => (hG i).aestronglyMeasurable
  set Du : Vec d × ℝ → Vec d := fun z i => (hDuM i).mk _ z with hDu
  set G' : Vec d × ℝ → Vec d := fun z i => (hFM i).mk _ z with hG'
  have hae : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)), (∀ i, G' z i = G z i) ∧
      ∀ i, Du z i = u.grad z i := by
    have h1 : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)), ∀ i, G' z i = G z i := by
      rw [ae_all_iff]; intro i; exact (hFM i).ae_eq_mk.mono fun z hz => hz.symm
    have h2 : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)), ∀ i, Du z i = u.grad z i := by
      rw [ae_all_iff]; intro i; exact (hDuM i).ae_eq_mk.mono fun z hz => hz.symm
    filter_upwards [h1, h2] with z a1 a2 using ⟨a1, a2⟩
  have hK1U : cthickening δ0 K ⊆ U :=
    (cthickening_mono (by linarith) K).trans hcU
  have hslab : cthickening δ0 K ×ˢ Ioc s t ⊆ U ×ˢ I :=
    prod_mono hK1U ((Ioc_subset_Icc_self).trans hIcc)
  have hle : (volume.restrict (cthickening δ0 K ×ˢ Ioc s t)) ≤ volume.restrict (U ×ˢ I) :=
    Measure.restrict_mono hslab le_rfl
  have haeS : ∀ᵐ z ∂(volume.restrict (cthickening δ0 K ×ˢ Ioc s t)),
      (∀ i, G' z i = G z i) ∧ ∀ i, Du z i = u.grad z i :=
    ae_restrict_of_ae_restrict_of_subset hslab hae
  have hφK : ∀ x τ, τ ∈ Icc s t → x ∈ cthickening (2 * δ0) K → x ∉ K → φ.toFun (x, τ) = 0 := by
    intro x τ hτ hx hxK
    exact hφ0 x (hcU hx) hxK τ (hIcc hτ)
  have hus : ∀ τ ∈ Icc s t,
      MemLp (fun y => u.toFun (y, τ)) 2 (volume.restrict (cthickening δ0 K)) := by
    intro τ hτ
    exact u.sliceL2loc τ (hIcc hτ) _ hKc.cthickening hK1U
  have hwg : ∀ᵐ τ ∂(volume.restrict (Ioc s t)), ∀ a' : ℝ, 0 < a' → a' ≤ δ0 → ∀ x ∈ K, ∀ i,
      ∫ y in cthickening δ0 K, fderiv ℝ (kern a') (x - y) (PDE.basisVec i) * u.toFun (y, τ) =
        ∫ y in cthickening δ0 K, kern a' (x - y) * Du (y, τ) i := by
    have hIoc : Ioc s t ⊆ I := Ioc_subset_Icc_self.trans hIcc
    have hw1 : ∀ᵐ τ ∂(volume.restrict (Ioc s t)),
        PDE.HasWeakGradientOn U (PDE.parSlice u.toFun τ) (PDE.parSlice u.grad τ) :=
      ae_restrict_of_ae_restrict_of_subset hIoc u.sliceWeakGradient
    have hw2 : ∀ᵐ τ ∂(volume.restrict (Ioc s t)), ∀ i,
        (fun y => Du (y, τ) i) =ᵐ[volume.restrict U] fun y => u.grad (y, τ) i := by
      have h : ∀ᵐ z ∂((volume.restrict U).prod (volume.restrict I)), ∀ i, Du z i = u.grad z i := by
        rw [← volume_restrict_prod]; exact hae.mono fun z hz => hz.2
      have h' := ae_restrict_of_ae_restrict_of_subset hIoc (ae_ae_swap h)
      filter_upwards [h'] with τ hτ i
      exact hτ.mono fun y hy => hy i
    filter_upwards [hw1, hw2] with τ h1 h2 a' ha' haδ x hx i
    exact weakGrad_identity hU u isClosed_cthickening.measurableSet hK1U ha'
      ((closedBall_subset_cthickening hx a').trans (cthickening_mono haδ K)) h1 h2 i
  have hslice : ∀ a' : ℝ, 0 < a' → a' ≤ δ0 → ∀ x ∈ K, ∀ τ1 τ2 : ℝ, s ≤ τ1 → τ1 ≤ τ2 → τ2 ≤ t →
      (∫ y in cthickening δ0 K, kern a' (x - y) * u.toFun (y, τ2)) -
          (∫ y in cthickening δ0 K, kern a' (x - y) * u.toFun (y, τ1)) =
        ∫ z in cthickening δ0 K ×ˢ Ioc τ1 τ2,
          ∑ i, G' z i * fderiv ℝ (kern a') (x - z.1) (PDE.basisVec i) := by
    intro a' ha' haδ x hx τ1 τ2 h1 h12 h2
    exact fluxSliceIdentity hU hI u hG hu (isClosed_cthickening.measurableSet) hK1U ha'
      ((closedBall_subset_cthickening hx a').trans (cthickening_mono haδ K))
      (hIcc ⟨h1, h12.trans h2⟩) (hIcc ⟨h1.trans h12, h2⟩) h12
      (hae.mono fun z hz => hz.1)
  refine ⟨⟨K, hKc, δ0, hδ0, hδ1, s, t, hst, u.toFun, Du, G', φ.toFun, φ.contDiff, hφK,
    fun i => ((hDuM i).stronglyMeasurable_mk).measurable,
    fun i => ((hFM i).stronglyMeasurable_mk).measurable,
    u.memL2.mono_measure hle,
    fun i => ((u.gradMemL2 i).mono_measure hle).ae_eq (haeS.mono fun z hz => (hz.2 i).symm),
    fun i => ((hG i).mono_measure hle).ae_eq (haeS.mono fun z hz => (hz.1 i).symm),
    hus, hwg, hslice⟩, rfl, rfl, rfl, rfl, hKU, hφ0, hae⟩

/-- **The energy identity** for `∂ₜu = ∇·G` and a cutoff `φ`: for `s < t` in `I`,
`½ ∫_U φ(t)² u(t)² - ½ ∫_U φ(s)² u(s)² = ∫_s^t ∫_U u² φ ∂ₜφ - ∫_s^t ∫_U G · ∇(φ² u)`. -/
theorem fluxEnergyIdentity (hU : IsOpen U) (hI : I.OrdConnected) (u : PDE.ParH1Function U I)
    {G : Vec d × ℝ → Vec d} (hG : ∀ i, MemLp (fun z => G z i) 2 (volume.restrict (U ×ˢ I)))
    (hu : IsParabolicFluxSolution U I u G) (φ : PDE.ParCutoff U I) {s t : ℝ} (hs : s ∈ I)
    (ht : t ∈ I) (hst : s < t) :
    IntegrableOn (fun z => u.toFun z ^ 2 * φ.toFun z * PDE.parTimeDeriv φ.toFun z)
        (U ×ˢ Ioc s t) ∧
      IntegrableOn (fun z => ∑ i, G z i * (φ.toFun z ^ 2 * u.grad z i +
          2 * φ.toFun z * u.toFun z * PDE.parSpaceGrad φ.toFun z i)) (U ×ˢ Ioc s t) ∧
      ((1 / 2 : ℝ) * ∫ x in U, φ.toFun (x, t) ^ 2 * u.toFun (x, t) ^ 2) -
          (1 / 2 : ℝ) * ∫ x in U, φ.toFun (x, s) ^ 2 * u.toFun (x, s) ^ 2 =
        (∫ z in U ×ˢ Ioc s t, u.toFun z ^ 2 * φ.toFun z * PDE.parTimeDeriv φ.toFun z) -
          ∫ z in U ×ˢ Ioc s t, ∑ i, G z i * (φ.toFun z ^ 2 * u.grad z i +
            2 * φ.toFun z * u.toFun z * PDE.parSpaceGrad φ.toFun z i) := by
  obtain ⟨D, hDu, hDφ, hDs, hDt, hKU, hφ0, hae⟩ := exists_fluxData hU hI u hG hu φ hs ht hst
  have hIcc : Icc s t ⊆ I := hI.out hs ht
  have hIoc : Ioc s t ⊆ I := Ioc_subset_Icc_self.trans hIcc
  have key := D.energy_identity
  have hA := D.integrable_A
  have hB := D.integrable_B
  unfold Data.μP at key hA hB
  rw [hDu, hDφ, hDs, hDt] at key hA hB
  have hmeas : MeasurableSet (U ×ˢ Ioc s t) := hU.measurableSet.prod measurableSet_Ioc
  have hsub : D.K ×ˢ Ioc s t ⊆ U ×ˢ Ioc s t := prod_mono hKU subset_rfl
  have hvan : ∀ z ∈ U ×ˢ Ioc s t \ D.K ×ˢ Ioc s t, φ.toFun z = 0 := by
    rintro ⟨x, τ⟩ ⟨⟨hx, hτ⟩, hn⟩
    exact hφ0 x hx (fun h => hn ⟨h, hτ⟩) τ (hIoc hτ)
  have haeS : ∀ᵐ z ∂(volume.restrict (D.K ×ˢ Ioc s t)),
      ∑ i, D.G z i * (φ.toFun z ^ 2 * D.Du z i + 2 * φ.toFun z * u.toFun z *
        PDE.parSpaceGrad φ.toFun z i) =
      ∑ i, G z i * (φ.toFun z ^ 2 * u.grad z i +
        2 * φ.toFun z * u.toFun z * PDE.parSpaceGrad φ.toFun z i) := by
    have hsl : D.K ×ˢ Ioc s t ⊆ U ×ˢ I := prod_mono hKU hIoc
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsl hae] with z hz
    exact Finset.sum_congr rfl fun i _ => by rw [hz.1 i, hz.2 i]
  have hA1 : IntegrableOn (fun z => u.toFun z ^ 2 * φ.toFun z * PDE.parTimeDeriv φ.toFun z)
      (D.K ×ˢ Ioc s t) := hA
  have hA' : IntegrableOn (fun z => u.toFun z ^ 2 * φ.toFun z * PDE.parTimeDeriv φ.toFun z)
      (U ×ˢ Ioc s t) :=
    hA1.of_forall_sdiff_eq_zero hmeas fun z hz => by rw [hvan z hz]; ring
  have hB1 : IntegrableOn (fun z => ∑ i, G z i * (φ.toFun z ^ 2 * u.grad z i +
      2 * φ.toFun z * u.toFun z * PDE.parSpaceGrad φ.toFun z i)) (D.K ×ˢ Ioc s t) :=
    hB.congr haeS
  have hB' : IntegrableOn (fun z => ∑ i, G z i * (φ.toFun z ^ 2 * u.grad z i +
      2 * φ.toFun z * u.toFun z * PDE.parSpaceGrad φ.toFun z i)) (U ×ˢ Ioc s t) :=
    hB1.of_forall_sdiff_eq_zero hmeas fun z hz => by simp [hvan z hz]
  refine ⟨hA', hB', ?_⟩
  have e1 : ∀ τ ∈ I, ∫ x in U, φ.toFun (x, τ) ^ 2 * u.toFun (x, τ) ^ 2 =
      ∫ x in D.K, φ.toFun (x, τ) ^ 2 * u.toFun (x, τ) ^ 2 := by
    intro τ hτ
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hKU fun x hx => ?_
    rw [hφ0 x hx.1 hx.2 τ hτ]
    ring
  have e2 : ∫ z in U ×ˢ Ioc s t, u.toFun z ^ 2 * φ.toFun z * PDE.parTimeDeriv φ.toFun z =
      ∫ z in D.K ×ˢ Ioc s t, u.toFun z ^ 2 * φ.toFun z * PDE.parTimeDeriv φ.toFun z := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas hsub fun z hz => ?_
    rw [hvan z hz]
    ring
  have e3 : ∫ z in U ×ˢ Ioc s t, ∑ i, G z i * (φ.toFun z ^ 2 * u.grad z i +
        2 * φ.toFun z * u.toFun z * PDE.parSpaceGrad φ.toFun z i) =
      ∫ z in D.K ×ˢ Ioc s t, ∑ i, D.G z i * (φ.toFun z ^ 2 * D.Du z i + 2 * φ.toFun z *
        u.toFun z * PDE.parSpaceGrad φ.toFun z i) := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas hsub]
    · exact (integral_congr_ae haeS).symm
    · intro z hz
      simp [hvan z hz]
  rw [e1 t ht, e1 s hs, e2, e3]
  exact key

end QSH
