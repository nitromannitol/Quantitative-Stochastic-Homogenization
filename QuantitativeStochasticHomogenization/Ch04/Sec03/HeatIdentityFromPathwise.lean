import QuantitativeStochasticHomogenization.Ch04.Sec03.Estimate558FromLaw

/-!
# The bound from the heat identity: absolute convergence of the time integral

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, the heat identity (H) of the route of Proposition 4.10.

`HeatIdentityBound` asks for the time integral `∫_{u > r²/2} ∫ k_r(u, x) |commutator at (z - x, √u)|`
as a Bochner integral, so its absolute convergence is part of the statement. The identity (H) with
the triangle inequality gives the bound with the lower integral (`HeatPathwiseBound`). The first
moment of the time integral is finite as soon as the expected commutator decays at some rate
(`ExpectedCommutatorDecay`): by Tonelli it is at most `C C_k ∫_{u > r²/2} u^{-1-κ/2} du`. Hence the
lower integral is almost surely finite and equals the Bochner integral
(`heatIdentityBound_of_pathwise`).
-/

open MeasureTheory Filter Set
open scoped ENNReal

noncomputable section

namespace QSH

open BaseExponent

variable {d : ℕ} {Λ : ℝ}

section Pathwise

variable {P : Measure (CoefficientField d Λ)}

/-- **The heat bound in lower-integral form**: for `r ≥ 2`, almost surely
`|P eᵢ - eᵢ| ≤ ∫⁻_{u > r²/2} ∫⁻ k_r(u, x) |commutator at (z - x, √u)| dx du`. -/
def HeatPathwiseBound (P : Measure (CoefficientField d Λ)) (S : HomogenizationData P)
    (k : ℝ → ℝ → Vec d → ℝ) : Prop :=
  ∀ (z : Vec d) (r : ℝ), 2 ≤ r → ∀ i : Fin d, ∀ᵐ a ∂P,
    ENNReal.ofReal (euclideanNorm (gradientAverage S a z r (unitVector i) - unitVector i)) ≤
      ∫⁻ u in Ioi (r ^ 2 / 2), ∫⁻ x,
        ENNReal.ofReal (k r u x * commutatorNorm S a (z - x) (Real.sqrt u) i)

/-- **Decay of the expected commutator**: `E |∫ Φ_{y,ρ} (a - ā)(eᵢ + ∇φ_{eᵢ})| ≤ C ρ^{-κ}` for
`ρ ≥ 1`, at every center. -/
def ExpectedCommutatorDecay (P : Measure (CoefficientField d Λ)) (S : HomogenizationData P)
    (κ C : ℝ) : Prop :=
  ∀ (y : Vec d) (ρ : ℝ), 1 ≤ ρ → ∀ i : Fin d,
    ∫⁻ a, ENNReal.ofReal (commutatorNorm S a y ρ i) ∂P ≤ ENNReal.ofReal (C * ρ ^ (-κ))

theorem measurable_commutatorNorm_uncurry (S : HomogenizationData P) (i : Fin d) :
    Measurable fun w : (Vec d × ℝ) × CoefficientField d Λ => commutatorNorm S w.2 w.1.1 w.1.2 i :=
  measurable_commutatorNorm S (measurable_fluxAverage_uncurry S) i

/-- **`HeatIdentityBound` from the lower-integral bound and a decay of the expected
commutator.** -/
theorem heatIdentityBound_of_pathwise [SFinite P] (S : HomogenizationData P) {k : ℝ → ℝ → Vec d → ℝ}
    {Ck : ℝ} (hkm : ∀ r, Measurable (Function.uncurry (k r))) (hk0 : ∀ r u x, 0 < k r u x)
    (hki : ∀ r u, 1 ≤ u → Integrable (k r u) ∧ ∫ x, k r u x ≤ Ck * u⁻¹)
    (hpath : HeatPathwiseBound P S k) {κ C : ℝ} (hκ : 0 < κ) (hC : 0 ≤ C)
    (hdec : ExpectedCommutatorDecay P S κ C) : HeatIdentityBound P S Ck := by
  refine ⟨k, hkm, hk0, hki, fun z r hr i => ?_⟩
  have hCk : 0 ≤ Ck := by
    have h := (hki r 1 le_rfl).2
    rw [inv_one, mul_one] at h
    exact (integral_nonneg fun x => (hk0 r 1 x).le).trans h
  have hmeasC := measurable_commutatorNorm_uncurry S i
  have hu0 : 2 ≤ r ^ 2 / 2 := by nlinarith
  have hu0' : 0 < r ^ 2 / 2 := by linarith
  set Fn : CoefficientField d Λ → ℝ → Vec d → ℝ :=
    fun a u x => k r u x * commutatorNorm S a (z - x) (Real.sqrt u) i with hFndef
  have hFm : Measurable fun p : CoefficientField d Λ × (ℝ × Vec d) => Fn p.1 p.2.1 p.2.2 := by
    have h1 : Measurable fun p : CoefficientField d Λ × (ℝ × Vec d) => k r p.2.1 p.2.2 :=
      (hkm r).comp measurable_snd
    have hg1 : Measurable fun p : CoefficientField d Λ × (ℝ × Vec d) => z - p.2.2 :=
      measurable_const.sub (measurable_snd.comp measurable_snd)
    have hg2 : Measurable fun p : CoefficientField d Λ × (ℝ × Vec d) => Real.sqrt p.2.1 :=
      (measurable_fst.comp measurable_snd).sqrt
    have hg : Measurable fun p : CoefficientField d Λ × (ℝ × Vec d) =>
        ((z - p.2.2, Real.sqrt p.2.1), p.1) := (hg1.prodMk hg2).prodMk measurable_fst
    have h2 := hmeasC.comp hg
    exact h1.mul h2
  have hF0 : ∀ a u x, 0 ≤ Fn a u x := fun a u x =>
    mul_nonneg (hk0 _ _ _).le (euclideanNorm_nonneg _)
  -- measurability of the partial lower integrals
  have hGm : Measurable fun p : CoefficientField d Λ × ℝ =>
      ∫⁻ x, ENNReal.ofReal (Fn p.1 p.2 x) := by
    have h : Measurable fun q : (CoefficientField d Λ × ℝ) × Vec d =>
        ENNReal.ofReal (Fn q.1.1 q.1.2 q.2) :=
      (hFm.comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))).ennreal_ofReal
    exact h.lintegral_prod_right'
  have hTm : Measurable fun a => ∫⁻ u in Ioi (r ^ 2 / 2), ∫⁻ x, ENNReal.ofReal (Fn a u x) :=
    hGm.lintegral_prod_right'
  -- the first moment of the time integral
  have hcomm : ∀ u x, 1 ≤ Real.sqrt u →
      ∫⁻ a, ENNReal.ofReal (Fn a u x) ∂P ≤
        ENNReal.ofReal (k r u x) * ENNReal.ofReal (C * Real.sqrt u ^ (-κ)) := by
    intro u x hu
    have hg : Measurable fun a : CoefficientField d Λ => ((z - x, Real.sqrt u), a) :=
      measurable_const.prodMk measurable_id
    have hm' := (hmeasC.comp hg).ennreal_ofReal
    have hm : Measurable fun a => ENNReal.ofReal (commutatorNorm S a (z - x) (Real.sqrt u) i) :=
      hm'
    calc ∫⁻ a, ENNReal.ofReal (Fn a u x) ∂P
        = ∫⁻ a, ENNReal.ofReal (k r u x) *
            ENNReal.ofReal (commutatorNorm S a (z - x) (Real.sqrt u) i) ∂P := by
          refine lintegral_congr fun a => ?_
          rw [hFndef, ENNReal.ofReal_mul (hk0 _ _ _).le]
      _ = ENNReal.ofReal (k r u x) *
            ∫⁻ a, ENNReal.ofReal (commutatorNorm S a (z - x) (Real.sqrt u) i) ∂P :=
          lintegral_const_mul _ hm
      _ ≤ _ := mul_le_mul_right (hdec _ _ hu i) _
  have hmom : ∫⁻ a, (∫⁻ u in Ioi (r ^ 2 / 2), ∫⁻ x, ENNReal.ofReal (Fn a u x)) ∂P < ⊤ := by
    have hswap1 : ∫⁻ a, (∫⁻ u in Ioi (r ^ 2 / 2), ∫⁻ x, ENNReal.ofReal (Fn a u x)) ∂P =
        ∫⁻ u in Ioi (r ^ 2 / 2), ∫⁻ a, (∫⁻ x, ENNReal.ofReal (Fn a u x)) ∂P :=
      lintegral_lintegral_swap hGm.aemeasurable
    have hswap2 : ∀ u, ∫⁻ a, (∫⁻ x, ENNReal.ofReal (Fn a u x)) ∂P =
        ∫⁻ x, ∫⁻ a, ENNReal.ofReal (Fn a u x) ∂P := fun u => by
      have hg : Measurable fun q : CoefficientField d Λ × Vec d => (q.1, (u, q.2)) :=
        measurable_fst.prodMk (measurable_const.prodMk measurable_snd)
      exact lintegral_lintegral_swap (hFm.comp hg).ennreal_ofReal.aemeasurable
    rw [hswap1]
    have hb : ∀ u ∈ Ioi (r ^ 2 / 2), ∫⁻ a, (∫⁻ x, ENNReal.ofReal (Fn a u x)) ∂P ≤
        ENNReal.ofReal (C * Ck * u ^ (-1 - κ / 2)) := by
      intro u hu
      have hu1 : 1 ≤ u := by have : r ^ 2 / 2 < u := hu; linarith
      have hu0 : 0 < u := zero_lt_one.trans_le hu1
      have hsq : 1 ≤ Real.sqrt u := Real.one_le_sqrt.mpr hu1
      obtain ⟨hki1, hki2⟩ := hki r u hu1
      rw [hswap2]
      calc ∫⁻ x, ∫⁻ a, ENNReal.ofReal (Fn a u x) ∂P
          ≤ ∫⁻ x, ENNReal.ofReal (k r u x) * ENNReal.ofReal (C * Real.sqrt u ^ (-κ)) :=
            lintegral_mono fun x => hcomm u x hsq
        _ = (∫⁻ x, ENNReal.ofReal (k r u x)) * ENNReal.ofReal (C * Real.sqrt u ^ (-κ)) :=
            lintegral_mul_const _ ((hkm r).comp (measurable_const.prodMk measurable_id :
              Measurable fun x : Vec d => (u, x))).ennreal_ofReal
        _ = ENNReal.ofReal (∫ x, k r u x) * ENNReal.ofReal (C * Real.sqrt u ^ (-κ)) := by
            rw [ofReal_integral_eq_lintegral_ofReal hki1
              (Eventually.of_forall fun x => (hk0 r u x).le)]
        _ ≤ ENNReal.ofReal (Ck * u⁻¹) * ENNReal.ofReal (C * Real.sqrt u ^ (-κ)) :=
            mul_le_mul_left (ENNReal.ofReal_le_ofReal hki2) _
        _ = ENNReal.ofReal (C * Ck * u ^ (-1 - κ / 2)) := by
            rw [← ENNReal.ofReal_mul (mul_nonneg hCk (inv_nonneg.mpr hu0.le)),
              ← sqrt_rpow_neg_mul_inv hu0]
            congr 1
            ring
    have hint : IntegrableOn (fun u : ℝ => C * Ck * u ^ (-1 - κ / 2)) (Ioi (r ^ 2 / 2)) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hu0').const_mul _
    calc ∫⁻ u in Ioi (r ^ 2 / 2), ∫⁻ a, (∫⁻ x, ENNReal.ofReal (Fn a u x)) ∂P
        ≤ ∫⁻ u in Ioi (r ^ 2 / 2), ENNReal.ofReal (C * Ck * u ^ (-1 - κ / 2)) :=
          lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).mpr
            (Eventually.of_forall hb))
      _ = ENNReal.ofReal (∫ u in Ioi (r ^ 2 / 2), C * Ck * u ^ (-1 - κ / 2)) :=
          (ofReal_integral_eq_lintegral_ofReal hint ((ae_restrict_iff' measurableSet_Ioi).mpr
            (Eventually.of_forall fun u hu => by
              have : 0 < u := hu0'.trans hu
              positivity))).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hfin : ∀ᵐ a ∂P, ∫⁻ u in Ioi (r ^ 2 / 2), ∫⁻ x, ENNReal.ofReal (Fn a u x) < ⊤ :=
    ae_lt_top hTm hmom.ne
  filter_upwards [hpath z r hr i, hfin] with a ha hfa
  have hxm : ∀ u, AEStronglyMeasurable (fun x => Fn a u x) volume := fun u => by
    have hg : Measurable fun x : Vec d => (a, (u, x)) :=
      measurable_const.prodMk (measurable_const.prodMk measurable_id)
    exact (hFm.comp hg).aestronglyMeasurable
  have hinner : ∀ u, ∫ x, Fn a u x = (∫⁻ x, ENNReal.ofReal (Fn a u x)).toReal := fun u =>
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => hF0 a u x) (hxm u)
  have hum : Measurable fun q : ℝ × Vec d => Fn a q.1 q.2 := by
    have hg : Measurable fun q : ℝ × Vec d => (a, q) := measurable_const.prodMk measurable_id
    exact hFm.comp hg
  have hhm : AEStronglyMeasurable (fun u => ∫ x, Fn a u x) (volume.restrict (Ioi (r ^ 2 / 2))) :=
    (hum.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Vec d)))).aestronglyMeasurable
  have hgm : Measurable fun u => ∫⁻ x, ENNReal.ofReal (Fn a u x) :=
    hum.ennreal_ofReal.lintegral_prod_right'
  have hgfin : ∀ᵐ u ∂(volume.restrict (Ioi (r ^ 2 / 2))),
      ∫⁻ x, ENNReal.ofReal (Fn a u x) < ⊤ := ae_lt_top hgm hfa.ne
  have houter : ∫ u in Ioi (r ^ 2 / 2), ∫ x, Fn a u x =
      (∫⁻ u in Ioi (r ^ 2 / 2), ∫⁻ x, ENNReal.ofReal (Fn a u x)).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun u =>
      integral_nonneg fun x => hF0 a u x) hhm]
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [hgfin] with u hu
    rw [hinner u, ENNReal.ofReal_toReal hu.ne]
  change euclideanNorm (gradientAverage S a z r (unitVector i) - unitVector i) ≤
    ∫ u in Ioi (r ^ 2 / 2), ∫ x, Fn a u x
  rw [houter]
  exact (ENNReal.ofReal_le_iff_le_toReal hfa.ne).mp ha

end Pathwise

end QSH
