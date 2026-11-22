import QuantitativeStochasticHomogenization.Ch04.Sec03.AverageMeasurability
import QuantitativeStochasticHomogenization.Ch05.Sec03.CoarsenedCoefficientEstimatesLiouville
import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicApproximationProof

/-!
# A jointly measurable version of the energy `J₁(Φ_{z,r}, p, q)`

Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, Section 4.2 and Remark 5.17. The spatial integrals of `x ↦ J₁(Φ_{x,r}, p, q)` in
Definition 4.7 and in (5.87)-(5.88) need the energy as a jointly measurable function of the
coefficients and of the parameters `(z, r, p, q)`. Since `J₁` is identified with its
finite-dimensional form (4.12) only almost surely, there is a jointly measurable function `V`
which agrees with `J₁` at every parameter on one event of full probability
(`HasJointHeatVersion`).

On the event where the gradients of `A₁` are the corrected fields `G ξ` and the corrected
coordinates have finite Gaussian energy, `J₁(Φ_{z,r}, p, q)` is the supremum of the trial
functionals at `G ξ` over a countable dense set of slopes `ξ` containing zero
(`j1_eq_countable_trials`); every trial is bounded by `Λ|p|² + |q|²`, so this supremum defines a
jointly measurable function at every sample (`hasJointHeatVersion_of_corrected_trials`,
`hasJointHeatVersion_of_corrector_energy`). For a law satisfying the assumptions the two events
have full probability, by the first-order Liouville theorem and the sublinearity of the
correctors (`hasJointHeatVersion_of_lawHypotheses`). A version can be chosen to satisfy, at every
sample, any pathwise property that holds almost surely and holds for the zero field
(`HasJointHeatVersion.with_pathwise_property`).
-/

open MeasureTheory Set

noncomputable section

namespace QSH

section MeasurableTrials

variable {d : ℕ} {Λ : ℝ} {E : Type*} [MeasurableSpace E]

private theorem measurable_trial_dot {u v : E → Vec d}
    (hu : Measurable u) (hv : Measurable v) : Measurable fun w => dot (u w) (v w) := by
  unfold dot
  exact Finset.measurable_fun_sum _ fun i _ =>
    (measurable_pi_iff.mp hu i).mul (measurable_pi_iff.mp hv i)

private theorem measurable_trial_coefficient {a : E → CoefficientField d Λ}
    (ha : Measurable a) :
    @Measurable (E × Vec d) (Mat d) _ Matrix.instMeasurableSpace
      (fun w => coefficientVersion (a w.1) w.2) := by
  have hmap : Measurable (fun w : E × Vec d => (a w.1, w.2)) :=
    (ha.comp measurable_fst).prodMk measurable_snd
  have h := (measurable_coefficientVersion (d := d) (Λ := Λ)).comp hmap
  exact h

/-- The trial functional `j1Functional` is measurable in jointly measurable parameters. -/
theorem measurable_parametric_j1Functional {a : E → CoefficientField d Λ} {p q : E → Vec d}
    {K : E × Vec d → ℝ} {g : E × Vec d → Vec d}
    (ha : Measurable a) (hp : Measurable p) (hq : Measurable q)
    (hK : Measurable K) (hg : Measurable g) :
    Measurable fun t => j1Functional (a t) (fun x => K (t, x))
      (p t) (q t) (fun x => g (t, x)) := by
  let A (w : E × Vec d) := coefficientVersion (a w.1) w.2
  let M (w : E × Vec d) := (A w).mulVec (g w)
  let H (w : E × Vec d) := K w * (-(1/2 : ℝ) * dot (g w) (M w) -
    dot (p w.1) (M w) + dot (q w.1) (g w))
  have hA : @Measurable (E × Vec d) (Mat d) _ Matrix.instMeasurableSpace A :=
    measurable_trial_coefficient ha
  have hM : Measurable M := measurable_mulVec_uncurry hA hg
  have hH : Measurable H := by
    apply hK.mul
    apply Measurable.add
    · exact ((measurable_trial_dot hg hM).const_mul (-(1/2 : ℝ))).sub
        (measurable_trial_dot (hp.comp measurable_fst) hM)
    · exact measurable_trial_dot (hq.comp measurable_fst) hg
  have heq : (fun t => j1Functional (a t) (fun x => K (t, x))
      (p t) (q t) (fun x => g (t, x))) = (fun t => ∫ x, H (t, x)) := by
    funext t
    unfold j1Functional
    apply integral_congr_ae
    filter_upwards [ae_coefficientVersion_eq (a t)] with x hx
    simp only [H, M, A, hx]
  rw [heq]
  exact hH.stronglyMeasurable.integral_prod_right'.measurable

end MeasurableTrials

variable {d : ℕ} {Λ : ℝ}

/-- The heat kernel of radius zero vanishes (for `d > 0`). -/
theorem heatKernel_at_zero_radius (hd : 0 < d) (z x : Vec d) :
    heatKernel z 0 x = 0 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  simp [heatKernel, euclideanHeatKernel, Real.zero_rpow (show -(d : ℝ)/2 ≠ 0 by linarith)]

/-- If the gradients of `A₁` are exactly the fields `g ξ`, the energy is the supremum of the
trial functionals at `g ξ` over a dense sequence of slopes. -/
theorem j1_eq_countable_trials (a : CoefficientField d Λ)
    (mask : Vec d → ℝ) (p q : Vec d) (g : Vec d → Vec d → Vec d)
    (slope : ℕ → Vec d) (hdense : DenseRange slope)
    (hclass : (∀ w : HarmonicA1 a, ∃ ξ, w.grad =ᵐ[volume] g ξ) ∧
      ∀ ξ, ∃ w : HarmonicA1 a, w.grad =ᵐ[volume] g ξ)
    (hcont : Continuous (fun ξ => j1Functional a mask p q (g ξ)))
    {B : ℝ} (hB : ∀ h, j1Functional a mask p q h ≤ B) :
    J1 a mask p q = ⨆ n, j1Functional a mask p q (g (slope n)) := by
  let F := fun ξ => j1Functional a mask p q (g ξ)
  let M := ⨆ n, F (slope n)
  have hb : BddAbove (range (fun n => F (slope n))) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hB _
  have hall (ξ : Vec d) : F ξ ≤ M :=
    hdense.induction_on ξ (isClosed_le hcont continuous_const) (fun n => le_ciSup hb n)
  rw [J1_eq_sSup_j1Functional]
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, zeroHarmonicA1 a, rfl⟩
    · rintro _ ⟨w, rfl⟩
      obtain ⟨ξ, he⟩ := hclass.1 w
      rw [j1Functional_congr_ae a mask p q he]
      exact hall ξ
  · apply ciSup_le
    intro n
    apply le_csSup
    · refine ⟨B, ?_⟩
      rintro _ ⟨w, rfl⟩
      exact hB _
    · obtain ⟨w, he⟩ := hclass.2 (slope n)
      exact ⟨w, (j1Functional_congr_ae a mask p q he).symm⟩

/-- The parameters `(z, r, p, q)` of `J₁(Φ_{z,r}, p, q)`. -/
abbrev HeatObservationIndex (d : ℕ) :=
  Vec d × ℝ × Vec d × Vec d

/-- **A jointly measurable version of `J₁(Φ_{z,r}, p, q)`**: a function of the coefficients and
the parameters, jointly measurable, equal to `J₁` at every parameter almost surely. -/
def HasJointHeatVersion (P : Measure (CoefficientField d Λ)) : Prop :=
  ∃ V : CoefficientField d Λ → HeatObservationIndex d → ℝ,
    Measurable (Function.uncurry V) ∧ ∀ᵐ a ∂P, ∀ i,
      V a i = J1Heat a i.1 i.2.1 i.2.2.1 i.2.2.2

/-- The trial functional at a corrected field is measurable in jointly measurable parameters. -/
theorem measurable_corrected_heat_trial {P : Measure (CoefficientField d Λ)}
    (S : HomogenizationData P) (ξ : Vec d) {E : Type*} [MeasurableSpace E]
    {a : E → CoefficientField d Λ} {z p q : E → Vec d} {r : E → ℝ}
    (ha : Measurable a) (hz : Measurable z) (hr : Measurable r)
    (hp : Measurable p) (hq : Measurable q) :
    Measurable fun t => j1Functional (a t) (heatKernel (z t) (r t)) (p t) (q t)
      (correctedField S (a t) ξ) := by
  let obs (w : E × Vec d) := ((z w.1, r w.1), w.2)
  let env (w : E × Vec d) := (a w.1, w.2)
  let K (w : E × Vec d) := heatKernel (z w.1) (r w.1) w.2
  let g (w : E × Vec d) := correctedField S (a w.1) ξ w.2
  have ho : Measurable obs :=
    ((hz.comp measurable_fst).prodMk (hr.comp measurable_fst)).prodMk measurable_snd
  have he : Measurable env := (ha.comp measurable_fst).prodMk measurable_snd
  have hK : Measurable K := by
    change Measurable ((fun u : (Vec d × ℝ) × Vec d => heatKernel u.1.1 u.1.2 u.2) ∘ obs)
    exact (measurable_heatKernel_center_radius (d := d)).comp ho
  have hg : Measurable g := by
    change Measurable ((fun u : CoefficientField d Λ × Vec d => correctedField S u.1 ξ u.2) ∘ env)
    exact (measurable_correctedField S ξ).comp he
  exact measurable_parametric_j1Functional (a := a) (p := p) (q := q) (K := K) (g := g)
    ha hp hq hK hg

private theorem heatMask_all (hd : 0 < d) (z : Vec d) (r : ℝ) :
    Integrable (heatKernel z r) ∧ ∫ x, heatKernel z r x ≤ 1 := by
  by_cases hr : r = 0
  · have hz : heatKernel z r = (fun _ => 0) :=
      funext fun x => hr ▸ heatKernel_at_zero_radius hd z x
    rw [hz]
    simp
  · have hk : heatKernel z r = heatKernel z |r| := by funext x; simp [heatKernel]
    rw [hk]
    exact ⟨integrable_heatKernel z (abs_pos.mpr hr), (integral_heatKernel z (abs_pos.mpr hr)).le⟩

open BaseExponent in
/-- A jointly measurable version from the identification (4.12) of the gradients of `A₁` and the
continuity of the trial functionals in the slope. -/
theorem hasJointHeatVersion_of_corrected_trials (hd : 0 < d)
    {P : Measure (CoefficientField d Λ)} (S : HomogenizationData P)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hcont : ∀ᵐ a ∂P, ∀ z r p q,
      Continuous fun ξ => j1Functional a (heatKernel z r) p q (correctedField S a ξ)) :
    HasJointHeatVersion P := by
  let slope : ℕ → Vec d
    | 0 => 0
    | n+1 => TopologicalSpace.denseSeq (Vec d) n
  have hs : DenseRange slope := by
    apply Dense.mono _ (TopologicalSpace.denseRange_denseSeq (Vec d))
    rintro _ ⟨n, rfl⟩
    exact ⟨n+1, rfl⟩
  let value (a : CoefficientField d Λ) (i : HeatObservationIndex d) (n : ℕ) :=
    j1Functional a (heatKernel i.1 i.2.1) i.2.2.1 i.2.2.2 (correctedField S a (slope n))
  refine ⟨fun a i => ⨆ n, value a i n, ?_, ?_⟩
  · change Measurable (fun w : CoefficientField d Λ × HeatObservationIndex d =>
      ⨆ n, value w.1 w.2 n)
    refine Measurable.iSup fun n => ?_
    apply measurable_corrected_heat_trial S (slope n) (a := Prod.fst)
      (z := fun w : CoefficientField d Λ × HeatObservationIndex d => w.2.1)
      (r := fun w => w.2.2.1) (p := fun w => w.2.2.2.1) (q := fun w => w.2.2.2.2)
    all_goals fun_prop
  · filter_upwards [hspan, hcont] with a ha hc
    intro i
    symm
    apply j1_eq_countable_trials a (heatKernel i.1 i.2.1) i.2.2.1 i.2.2.2
      (correctedField S a) slope hs
      ha (hc _ _ _ _) (B := Λ * euclideanSq i.2.2.1 + euclideanSq i.2.2.2)
    intro g
    obtain ⟨hint, hmass⟩ := heatMask_all hd i.1 i.2.1
    exact j1Functional_le a (heatKernel_nonneg _ _) hint hmass _ _ g

/-- The trial functional of a Gram family is continuous in the slope. -/
theorem GramFamily.continuous_j1Functional (F : GramFamily d Λ) (p q : Vec d) :
    Continuous (fun ξ => j1Functional F.coeff F.mask p q (F.field ξ)) := by
  let L : Vec d →ₗ[ℝ] F.H :=
    (SeparationQuotient.mkCLM ℝ F.Space).toLinearMap.comp F.spaceLinearEquiv.symm.toLinearMap
  have hl : Continuous F.toH := L.continuous_of_finiteDimensional
  simp_rw [F.j1Functional_field_eq p q]
  exact (continuous_const.mul (hl.norm.pow 2)).add (continuous_const.inner hl)

/-- A jointly measurable version from the identification (4.12) of the gradients of `A₁` and the
finite Gaussian energy of the corrected coordinates. -/
theorem hasJointHeatVersion_of_corrector_energy (hd : 0 < d)
    {P : Measure (CoefficientField d Λ)} (S : HomogenizationData P)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hen : HasGaussianCorrectorEnergy S) : HasJointHeatVersion P := by
  apply hasJointHeatVersion_of_corrected_trials hd S hspan
  filter_upwards [hspan, hen] with a hc he
  intro z r p q
  by_cases hr : r = 0
  · have hz : heatKernel z r = (fun _ => 0) :=
      funext fun x => hr ▸ heatKernel_at_zero_radius hd z x
    simp only [hz, j1Functional, zero_mul, integral_zero]
    exact continuous_const
  · have ht := abs_pos.mpr hr
    have hk : heatKernel z r = heatKernel z |r| := by funext x; simp [heatKernel]
    rw [hk]
    let F := heatGramFamily a z ht (correctedFieldFamily S a) hc.2
      (integrable_heatKernel_mul_euclideanSq_correctedField S z ht (fun i => he i z |r| ht))
    exact F.continuous_j1Functional p q

/-- **A jointly measurable version of `J₁` for a law satisfying the assumptions**, given
homogenization data: (4.12) holds almost surely by the first-order Liouville theorem, and the
corrected coordinates have finite Gaussian energy by the sublinearity of the correctors. -/
theorem hasJointHeatVersion_of_lawHypotheses (hd : 2 ≤ d) (hΛ : 1 < Λ)
    {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P) (S : HomogenizationData P) :
    HasJointHeatVersion P :=
  hasJointHeatVersion_of_corrector_energy (by omega) S
    (ae_gradientsOfA1AreCorrected_of_liouville firstOrderLiouville hd hΛ hP S)
    (hasGaussianCorrectorEnergy_of_lawHypotheses hd hΛ hP S)

/-- A version can be chosen to satisfy at every sample a pathwise property that holds almost
surely for `J₁` and holds for the zero field. The property may involve all parameters. -/
theorem HasJointHeatVersion.with_pathwise_property {P : Measure (CoefficientField d Λ)}
    (hJ : HasJointHeatVersion P)
    (Q : CoefficientField d Λ → (HeatObservationIndex d → ℝ) → Prop)
    (hzero : ∀ a, Q a 0)
    (hQ : ∀ᵐ a ∂P, Q a (fun i => J1Heat a i.1 i.2.1 i.2.2.1 i.2.2.2)) :
    ∃ V : CoefficientField d Λ → HeatObservationIndex d → ℝ,
      Measurable (Function.uncurry V) ∧
      (∀ᵐ a ∂P, ∀ i, V a i = J1Heat a i.1 i.2.1 i.2.2.1 i.2.2.2) ∧ ∀ a, Q a (V a) := by
  classical
  obtain ⟨F, hFm, hEq⟩ := hJ
  have hFQ : ∀ᵐ a ∂P, Q a (F a) := by
    filter_upwards [hEq, hQ] with a ha hqa
    rwa [funext ha]
  obtain ⟨G, hG, hGm, hGQ⟩ := hFQ.exists_measurable_mem
  let V (a : CoefficientField d Λ) (i : HeatObservationIndex d) := if a ∈ G then F a i else 0
  refine ⟨V, ?_, ?_, ?_⟩
  · exact Measurable.ite (hGm.preimage measurable_fst) hFm measurable_const
  · filter_upwards [hG, hEq] with a hag ha
    simpa [V, hag] using ha
  · intro a
    by_cases hag : a ∈ G
    · simpa [V, hag] using hGQ a hag
    · have he : V a = 0 := by
        funext i
        simp [V, hag]
      rw [he]
      exact hzero a

end QSH
