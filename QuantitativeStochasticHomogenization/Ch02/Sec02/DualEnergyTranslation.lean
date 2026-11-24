import QuantitativeStochasticHomogenization.Ch02.Sec01.Lemma22
import QuantitativeStochasticHomogenization.Ch01.Sec02.DirichletEnergyTests

/-!
# Translation covariance of `μ*`, `J` and `a*⁻¹(U)`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.2, the stationarity used in the proofs of Lemma 2.13 and (2.44): for an open set `U` and
`y ∈ ℝ^d`, `μ*(U + y, q)` for the field `a` is `μ*(U, q)` for the translated field `T_y a`
(`dualEnergy_preimage_sub`), and the same holds for `J(U, p, q)` (`dualityDefect_preimage_sub`) and
for `a*⁻¹(U)` (`coarseDualInvMatrix_preimage_sub`), as for `μ` (`dirichletEnergy_preimage_sub`).
The functions of `H¹(U + y)` are the translates of those of `H¹(U)`
(`H1.comp_sub_of_isOpen`).
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

section Translation

variable {U : Set (Vec d)} (y : Vec d)

theorem measurePreserving_sub_right_restrict (U : Set (Vec d)) (y : Vec d) :
    MeasurePreserving (fun x : Vec d => x - y) (volume.restrict {x | x - y ∈ U})
      (volume.restrict U) :=
  (measurePreserving_sub_right volume y).restrict_preimage_emb
    (MeasurableEquiv.subRight y).measurableEmbedding U

theorem memLp_comp_sub_restrict {E : Type*} [NormedAddCommGroup E] {f : Vec d → E}
    (hf : MemLp f 2 (volume.restrict U)) :
    MemLp (fun x => f (x - y)) 2 (volume.restrict {x | x - y ∈ U}) :=
  hf.comp_measurePreserving (measurePreserving_sub_right_restrict U y)

theorem isOpen_preimage_sub (hU : IsOpen U) : IsOpen {x : Vec d | x - y ∈ U} :=
  hU.preimage (continuous_sub_right y)

theorem locallyIntegrableOn_comp_sub_of_isOpen (hU : IsOpen U) {f : Vec d → ℝ}
    (hf : LocallyIntegrableOn f U volume) :
    LocallyIntegrableOn (fun x => f (x - y)) {x | x - y ∈ U} volume := by
  rw [locallyIntegrableOn_iff (isOpen_preimage_sub y hU).isLocallyClosed]
  rw [locallyIntegrableOn_iff hU.isLocallyClosed] at hf
  intro K hKU hK
  have hK' : IsCompact ((fun x : Vec d => x - y) '' K) := hK.image (continuous_sub_right y)
  have hsub : (fun x : Vec d => x - y) '' K ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact hKU hx
  have e : (fun x : Vec d => x - y) ⁻¹' ((fun x => x - y) '' K) = K :=
    Set.preimage_image_eq K sub_left_injective
  rw [← e]
  exact ((measurePreserving_sub_right volume y).integrableOn_comp_preimage
    (MeasurableEquiv.subRight y).measurableEmbedding).mpr (hf _ hsub hK')

theorem setIntegral_preimage_sub (U : Set (Vec d)) (F : Vec d → ℝ) :
    ∫ x in {x | x - y ∈ U}, F (x - y) = ∫ u in U, F u := by
  rw [show {x | x - y ∈ U} = (fun x : Vec d => x - y) ⁻¹' U from rfl]
  exact (measurePreserving_sub_right volume y).setIntegral_preimage_emb
    (MeasurableEquiv.subRight y).measurableEmbedding F U

theorem preimage_sub_neg_preimage_sub (U : Set (Vec d)) :
    {x | x - -y ∈ {x : Vec d | x - y ∈ U}} = U := by
  ext x
  simp

/-- **Translation of weak derivatives** on an open set. -/
theorem HasWeakPartialDerivative.comp_sub_of_isOpen (hU : IsOpen U) {i : Fin d}
    {f g : Vec d → ℝ} (h : HasWeakPartialDerivative U i f g) :
    HasWeakPartialDerivative {x | x - y ∈ U} i (fun x => f (x - y)) (fun x => g (x - y)) := by
  obtain ⟨hf, hg, hibp⟩ := h
  refine ⟨locallyIntegrableOn_comp_sub_of_isOpen y hU hf,
    locallyIntegrableOn_comp_sub_of_isOpen y hU hg, fun ψ hψ => ?_⟩
  have hψ' : IsSpatialTest U (fun u => ψ (u - -y)) := by
    have h := hψ.comp_sub (-y)
    rwa [preimage_sub_neg_preimage_sub] at h
  have h1 := hibp _ hψ'
  have hd : ∀ x, coordinateDerivative i (fun u => ψ (u - -y)) x =
      coordinateDerivative i ψ (x - -y) := fun x =>
    congrFun (IsSpatialTest.gradient_comp_sub ψ (-y) x) i
  simp only [hd] at h1
  have e1 := setIntegral_preimage_sub y U (fun u => f u * coordinateDerivative i ψ (u - -y))
  have e2 := setIntegral_preimage_sub y U (fun u => g u * ψ (u - -y))
  simp only [sub_neg_eq_add, sub_add_cancel] at e1 e2
  rw [e1, e2]
  simpa only [sub_neg_eq_add] using h1

theorem HasWeakGradient.comp_sub_of_isOpen (hU : IsOpen U) {f : Vec d → ℝ}
    {g : Vec d → Vec d} (h : HasWeakGradient U f g) :
    HasWeakGradient {x | x - y ∈ U} (fun x => f (x - y)) (fun x => g (x - y)) := fun i =>
  (h i).comp_sub_of_isOpen y hU

/-- **The functions of `H¹(U + y)` are the translates of those of `H¹(U)`.** -/
theorem H1.comp_sub_of_isOpen (hU : IsOpen U) {u : Vec d → ℝ} {g : Vec d → Vec d}
    (h : H1 U u g) : H1 {x | x - y ∈ U} (fun x => u (x - y)) (fun x => g (x - y)) :=
  ⟨memLp_comp_sub_restrict y h.1, memLp_comp_sub_restrict y h.2.1,
    h.2.2.comp_sub_of_isOpen y hU⟩

theorem volumeReal_preimage_sub (U : Set (Vec d)) :
    volume.real {x | x - y ∈ U} = volume.real U := by
  simp only [Measure.real]
  rw [show {x | x - y ∈ U} = (fun x : Vec d => x - y) ⁻¹' U from rfl,
    (measurePreserving_sub_right volume y).measure_preimage_emb
      (MeasurableEquiv.subRight y).measurableEmbedding]

theorem dualTrialEnergy_preimage_sub (a : CoefficientField d Λ) (U : Set (Vec d)) (q : Vec d)
    (G : Vec d → Vec d) :
    dualTrialEnergy a {x | x - y ∈ U} q (fun x => G (x - y)) =
      dualTrialEnergy (translate y a) U q G := by
  unfold dualTrialEnergy
  rw [setAverage_eq, setAverage_eq, volumeReal_preimage_sub]
  congr 1
  have h := setIntegral_preimage_sub y U
    (fun z => -(1 / 2 : ℝ) * dot (G z) (((translate y a) z).mulVec (G z)) + dot q (G z))
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have hx : (translate y a) (x - y) = a x := by
    change a.field (y + (x - y)) = a.field x
    rw [add_sub_cancel]
  simp only [hx]

/-- **Translation covariance of `μ*`**: `μ*(U + y, q)` for `a` is `μ*(U, q)` for `T_y a`, for an open
set `U`. -/
theorem dualEnergy_preimage_sub (a : CoefficientField d Λ) (hU : IsOpen U) (q : Vec d) :
    dualEnergy a {x | x - y ∈ U} q = dualEnergy (translate y a) U q := by
  unfold dualEnergy
  congr 1
  ext E
  constructor
  · rintro ⟨u, g, hug, rfl⟩
    refine ⟨fun x => u (x - -y), fun x => g (x - -y), ?_, ?_⟩
    · have h := hug.comp_sub_of_isOpen (-y) (isOpen_preimage_sub y hU)
      rwa [preimage_sub_neg_preimage_sub] at h
    · rw [← dualTrialEnergy_preimage_sub]
      congr 1
      funext x
      simp only [sub_neg_eq_add, sub_add_cancel]
  · rintro ⟨u, g, hug, rfl⟩
    exact ⟨fun x => u (x - y), fun x => g (x - y), hug.comp_sub_of_isOpen y hU,
      (dualTrialEnergy_preimage_sub y a U q g).symm⟩

/-- **Translation covariance of `J`**, for an open set `U` of finite measure. -/
theorem dualityDefect_preimage_sub (a : CoefficientField d Λ) (hU : IsOpen U)
    (hUt : volume U ≠ ⊤) (p q : Vec d) :
    dualityDefect a {x | x - y ∈ U} p q = dualityDefect (translate y a) U p q := by
  unfold dualityDefect
  rw [dirichletEnergy_preimage_sub a hUt y p, dualEnergy_preimage_sub y a hU q]

/-- **Translation covariance of `a*⁻¹(U)`**, for an open set `U`. -/
theorem coarseDualInvMatrix_preimage_sub (a : CoefficientField d Λ) (hU : IsOpen U) :
    coarseDualInvMatrix a {x | x - y ∈ U} = coarseDualInvMatrix (translate y a) U := by
  unfold coarseDualInvMatrix
  congr 1
  funext q
  exact dualEnergy_preimage_sub y a hU q

end Translation

end QSH
