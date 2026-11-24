import QuantitativeStochasticHomogenization.Ch02.Sec01.Lemma21

/-!
# The maximizer `v(·, U, p, q)` of (2.9)

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.1, Step 1 of the proof of Lemma 2.2 and (2.18)–(2.19).

* `IsDefectMaximizer.setIntegral_dot_eq` and `isDefectMaximizer_of_setIntegral_dot_eq`: the first
  variation (2.16), `∫_U ∇w·a∇v = ∫_U (-p·a∇w + q·∇w)` for every `w ∈ A(U)`, characterizes the
  maximizer;
* `IsDefectMaximizer.setAverage_sub_eq`: the quadratic response (2.17);
* `IsDefectMaximizer.ae_eq`: the gradient of the maximizer is unique;
* `IsDefectMaximizer.linearCombination`: the linearity (2.18) of `(p, q) ↦ v(·, U, p, q)`;
* `IsDefectMaximizer.dualityDefect_eq`: the identity (2.19), `J(U, p, q) = ⨍_U ½ ∇v·a∇v`.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## `A(U) ∩ H¹(U)` is a vector space -/

theorem IsAHarmonic.of_H1 {a : CoefficientField d Λ} {U : Set (Vec d)} (hU : volume U ≠ ⊤)
    {u : Vec d → ℝ} {g : Vec d → Vec d} (hH : H1 U u g)
    (h0 : ∀ (w : Vec d → ℝ) (h : Vec d → Vec d), H01 U w h →
      ∫ x in U, dot (h x) ((a x).mulVec (g x)) = 0) : IsAHarmonic a U u g :=
  ⟨hH, hasWeakDivergence_of_setIntegral_dot_eq_zero a hU hH.2.1 h0⟩

theorem dot_mulVec_linearCombination (A : Mat d) (h g₁ g₂ : Vec d) (c₁ c₂ : ℝ) :
    dot h (A.mulVec (c₁ • g₁ + c₂ • g₂)) = c₁ * dot h (A.mulVec g₁) + c₂ * dot h (A.mulVec g₂) := by
  simp only [dot_eq_dotProduct, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
    dotProduct_smul, smul_eq_mul]

theorem IsAHarmonic.linearCombination {a : CoefficientField d Λ} {U : Set (Vec d)}
    (hU : volume U ≠ ⊤) {u w : Vec d → ℝ} {g h : Vec d → Vec d} (hu : IsAHarmonic a U u g)
    (hw : IsAHarmonic a U w h) (c₁ c₂ : ℝ) :
    IsAHarmonic a U (fun x => c₁ * u x + c₂ * w x) (fun x => c₁ • g x + c₂ • h x) := by
  refine IsAHarmonic.of_H1 hU (hu.1.linearCombination hw.1 c₁ c₂) fun w' h' hw' => ?_
  have i1 := integrable_dot_mulVec_of_memLp a hw'.2.1 hu.1.2.1
  have i2 := integrable_dot_mulVec_of_memLp a hw'.2.1 hw.1.2.1
  simp only [dot_mulVec_linearCombination]
  rw [integral_add (i1.const_mul c₁) (i2.const_mul c₂), integral_const_mul, integral_const_mul,
    hu.setIntegral_dot_eq_zero hw', hw.setIntegral_dot_eq_zero hw']
  ring

theorem IsAHarmonic.add_smul {a : CoefficientField d Λ} {U : Set (Vec d)} (hU : volume U ≠ ⊤)
    {u w : Vec d → ℝ} {g h : Vec d → Vec d} (hu : IsAHarmonic a U u g)
    (hw : IsAHarmonic a U w h) (t : ℝ) :
    IsAHarmonic a U (fun x => u x + t * w x) (fun x => g x + t • h x) := by
  simpa only [one_mul, one_smul] using hu.linearCombination hU hw 1 t

theorem IsAHarmonic.sub {a : CoefficientField d Λ} {U : Set (Vec d)} (hU : volume U ≠ ⊤)
    {u w : Vec d → ℝ} {g h : Vec d → Vec d} (hu : IsAHarmonic a U u g)
    (hw : IsAHarmonic a U w h) : IsAHarmonic a U (fun x => u x - w x) (fun x => g x - h x) := by
  simpa only [neg_one_mul, neg_one_smul, ← sub_eq_add_neg] using hu.add_smul hU hw (-1)

/-! ## The first variation (2.16) -/

theorem integrable_dot_flux_add (a : CoefficientField d Λ) {U : Set (Vec d)} (hU : volume U ≠ ⊤)
    (p q : Vec d) {h : Vec d → Vec d} (hh : MemLp h 2 (volume.restrict U)) :
    Integrable (fun x => -dot p ((a x).mulVec (h x)) + dot q (h x)) (volume.restrict U) :=
  (integrable_dot_mulVec_const_left a hU hh p).neg.add (integrable_dot_left_of_memLp hU hh q)

/-- **The expansion of (2.9) at a critical point**: if `∫_U (h - g)·ag = ∫_U (-p·a(h - g) + q·(h - g))`,
then `⨍_U φ(h) = ⨍_U φ(g) - ⨍_U ½ (h - g)·a(h - g)` for the integrand `φ` of (2.9). -/
theorem defectTrialEnergy_eq_of_setIntegral_dot_eq (a : CoefficientField d Λ)
    {U : Set (Vec d)} (hU : volume U ≠ ⊤) (p q : Vec d) {g h : Vec d → Vec d}
    (hg : MemLp g 2 (volume.restrict U)) (hh : MemLp h 2 (volume.restrict U))
    (hfv : ∫ x in U, dot (h x - g x) ((a x).mulVec (g x)) =
      ∫ x in U, (-dot p ((a x).mulVec (h x - g x)) + dot q (h x - g x))) :
    defectTrialEnergy a U p q h = defectTrialEnergy a U p q g -
      ⨍ x in U, (1 / 2 : ℝ) * dot (h x - g x) ((a x).mulVec (h x - g x)) := by
  have hD : MemLp (fun x => h x - g x) 2 (volume.restrict U) := hh.sub hg
  have hexp := defectTrialEnergy_add_smul a hU p q hg hD 1
  have hc : (fun x => g x + (1 : ℝ) • (h x - g x)) = h := funext fun x => by
    rw [one_smul, add_sub_cancel]
  rw [hc] at hexp
  have j1 : Integrable (fun x => -dot (h x - g x) ((a x).mulVec (g x))) (volume.restrict U) :=
    (integrable_dot_mulVec_of_memLp a hD hg).neg
  have j2 := integrable_dot_mulVec_const_left a hU hD p
  have j3 := integrable_dot_left_of_memLp hU hD q
  have j12 : Integrable (fun x => -dot (h x - g x) ((a x).mulVec (g x)) -
      dot p ((a x).mulVec (h x - g x))) (volume.restrict U) := j1.sub j2
  have j2n : Integrable (fun x => -dot p ((a x).mulVec (h x - g x))) (volume.restrict U) := j2.neg
  have h0 : ⨍ x in U, (-dot (h x - g x) ((a x).mulVec (g x)) - dot p ((a x).mulVec (h x - g x)) +
      dot q (h x - g x)) = 0 := by
    rw [setAverage_eq, smul_eq_mul, integral_add j12 j3, integral_sub j1 j2, integral_neg]
    rw [integral_add j2n j3, integral_neg] at hfv
    rw [hfv]
    ring
  rw [hexp, h0]
  ring

/-- **The first variation (2.16)**: the maximizer `v = v(·, U, p, q)` of (2.9), of gradient `g`,
satisfies `∫_U ∇w·ag = ∫_U (-p·a∇w + q·∇w)` for every `w ∈ A(U) ∩ H¹(U)`. -/
theorem IsDefectMaximizer.setIntegral_dot_eq {a : CoefficientField d Λ} {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) (hU0 : volume U ≠ 0) {p q : Vec d} {v : Vec d → ℝ}
    {g : Vec d → Vec d} (hmax : IsDefectMaximizer a U p q v g) {w : Vec d → ℝ}
    {h : Vec d → Vec d} (hw : IsAHarmonic a U w h) :
    ∫ x in U, dot (h x) ((a x).mulVec (g x)) =
      ∫ x in U, (-dot p ((a x).mulVec (h x)) + dot q (h x)) := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have key : ∀ t : ℝ, (⨍ x in U, (-dot (h x) ((a x).mulVec (g x)) - dot p ((a x).mulVec (h x)) +
      dot q (h x))) * t ≤ (⨍ x in U, (1 / 2 : ℝ) * dot (h x) ((a x).mulVec (h x))) * t ^ 2 := by
    intro t
    have hle := defectTrialEnergy_le_dualityDefect a hUb hU0 (hmax.1.add_smul hU hw t) p q
    rw [defectTrialEnergy_add_smul a hU p q hmax.1.1.2.1 hw.1.2.1 t, hmax.2] at hle
    linarith
  have h0 := setIntegral_eq_zero_of_setAverage hU0 hU (eq_zero_of_forall_mul_le_mul_sq key)
  have j1 : Integrable (fun x => -dot (h x) ((a x).mulVec (g x))) (volume.restrict U) :=
    (integrable_dot_mulVec_of_memLp a hw.1.2.1 hmax.1.1.2.1).neg
  have j2 := integrable_dot_mulVec_const_left a hU hw.1.2.1 p
  have j3 := integrable_dot_left_of_memLp hU hw.1.2.1 q
  have j12 : Integrable (fun x => -dot (h x) ((a x).mulVec (g x)) - dot p ((a x).mulVec (h x)))
      (volume.restrict U) := j1.sub j2
  have j2n : Integrable (fun x => -dot p ((a x).mulVec (h x))) (volume.restrict U) := j2.neg
  rw [integral_add j12 j3, integral_sub j1 j2, integral_neg] at h0
  rw [integral_add j2n j3, integral_neg]
  linarith

/-- **The first variation (2.16) characterizes the maximizer**: `v ∈ A(U) ∩ H¹(U)` of gradient `g`
with `∫_U ∇w·ag = ∫_U (-p·a∇w + q·∇w)` for every `w ∈ A(U) ∩ H¹(U)` is a maximizer of (2.9). -/
theorem isDefectMaximizer_of_setIntegral_dot_eq [NeZero d] {a : CoefficientField d Λ}
    {U : Set (Vec d)} (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U)
    (hne : U.Nonempty) {p q : Vec d} {v : Vec d → ℝ} {g : Vec d → Vec d}
    (hv : IsAHarmonic a U v g)
    (hfv : ∀ (w : Vec d → ℝ) (h : Vec d → Vec d), IsAHarmonic a U w h →
      ∫ x in U, dot (h x) ((a x).mulVec (g x)) =
        ∫ x in U, (-dot p ((a x).mulVec (h x)) + dot q (h x))) :
    IsDefectMaximizer a U p q v g := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  refine ⟨hv, le_antisymm (defectTrialEnergy_le_dualityDefect a hUb hU0 hv p q) ?_⟩
  rw [(lemma_2_1 a hUo hUb hUc hne p q).1.1]
  refine csSup_le ⟨_, v, g, hv, rfl⟩ ?_
  rintro E ⟨w, h, hw, rfl⟩
  rw [defectTrialEnergy_eq_of_setIntegral_dot_eq a hU p q hv.1.2.1 hw.1.2.1
    (hfv _ _ (hw.sub hU hv))]
  have hnn : 0 ≤ ⨍ x in U, (1 / 2 : ℝ) * dot (h x - g x) ((a x).mulVec (h x - g x)) :=
    setAverage_nonneg_of_nonneg fun x => mul_nonneg (by norm_num)
      ((euclideanSq_nonneg _).trans (a.elliptic x _).1)
  linarith

/-! ## The quadratic response (2.17) and the uniqueness of the maximizer -/

/-- **The quadratic response (2.17)**: for the maximizer `v = v(·, U, p, q)` of gradient `g` and
`w ∈ A(U) ∩ H¹(U)` of gradient `h`,
`⨍_U ½ (h - g)·a(h - g) = J(U, p, q) - ⨍_U (-½ h·ah - p·ah + q·h)`. -/
theorem IsDefectMaximizer.setAverage_sub_eq {a : CoefficientField d Λ} {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) (hU0 : volume U ≠ 0) {p q : Vec d} {v : Vec d → ℝ}
    {g : Vec d → Vec d} (hmax : IsDefectMaximizer a U p q v g) {w : Vec d → ℝ}
    {h : Vec d → Vec d} (hw : IsAHarmonic a U w h) :
    ⨍ x in U, (1 / 2 : ℝ) * dot (h x - g x) ((a x).mulVec (h x - g x)) =
      dualityDefect a U p q - defectTrialEnergy a U p q h := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  rw [defectTrialEnergy_eq_of_setIntegral_dot_eq a hU p q hmax.1.1.2.1 hw.1.2.1
    (hmax.setIntegral_dot_eq hUb hU0 (hw.sub hU hmax.1)), hmax.2]
  ring

/-- **The maximizer is unique**: two maximizers of (2.9) have the same gradient almost
everywhere in `U`. -/
theorem IsDefectMaximizer.ae_eq {a : CoefficientField d Λ} {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) (hU0 : volume U ≠ 0) {p q : Vec d} {v₁ v₂ : Vec d → ℝ}
    {g₁ g₂ : Vec d → Vec d} (h₁ : IsDefectMaximizer a U p q v₁ g₁)
    (h₂ : IsDefectMaximizer a U p q v₂ g₂) : g₁ =ᵐ[volume.restrict U] g₂ := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have h := h₁.setAverage_sub_eq hUb hU0 h₂.1
  rw [h₂.2, sub_self] at h
  have hint : Integrable (fun x => (1 / 2 : ℝ) * dot (g₂ x - g₁ x) ((a x).mulVec (g₂ x - g₁ x)))
      (volume.restrict U) :=
    (integrable_dot_mulVec a U (h₂.1.1.2.1.sub h₁.1.1.2.1)).const_mul (1 / 2 : ℝ)
  have hnn : 0 ≤ᵐ[volume.restrict U]
      fun x => (1 / 2 : ℝ) * dot (g₂ x - g₁ x) ((a x).mulVec (g₂ x - g₁ x)) :=
    Eventually.of_forall fun x => mul_nonneg (by norm_num)
      ((euclideanSq_nonneg _).trans (a.elliptic x _).1)
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp
    (setIntegral_eq_zero_of_setAverage hU0 hU h)
  filter_upwards [hae] with x hx
  have hle := (a.elliptic x (g₂ x - g₁ x)).1
  have hx' : (1 / 2 : ℝ) * dot (g₂ x - g₁ x) ((a x).mulVec (g₂ x - g₁ x)) = 0 := hx
  have hsq : euclideanSq (g₂ x - g₁ x) = 0 :=
    le_antisymm (by linarith) (euclideanSq_nonneg _)
  exact (sub_eq_zero.mp (_root_.Homogenization.vecNormSq_eq_zero hsq)).symm

/-! ## (2.18) and (2.19) -/

/-- **(2.19)**: `J(U, p, q) = ⨍_U ½ ∇v·a∇v` for the maximizer `v = v(·, U, p, q)`. -/
theorem IsDefectMaximizer.dualityDefect_eq {a : CoefficientField d Λ} {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) (hU0 : volume U ≠ 0) {p q : Vec d} {v : Vec d → ℝ}
    {g : Vec d → Vec d} (hmax : IsDefectMaximizer a U p q v g) :
    dualityDefect a U p q = ⨍ x in U, (1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x)) := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hfv := hmax.setIntegral_dot_eq hUb hU0 hmax.1
  have hg := hmax.1.1.2.1
  have i1 := integrable_dot_mulVec a U hg
  have j2 := integrable_dot_mulVec_const_left a hU hg p
  have j3 := integrable_dot_left_of_memLp hU hg q
  have j2n : Integrable (fun x => -dot p ((a x).mulVec (g x))) (volume.restrict U) := j2.neg
  have j23 : Integrable (fun x => -dot p ((a x).mulVec (g x)) + dot q (g x))
      (volume.restrict U) := j2n.add j3
  have e : (fun x => -(1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x)) - dot p ((a x).mulVec (g x)) +
      dot q (g x)) = fun x => -(1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x)) +
        (-dot p ((a x).mulVec (g x)) + dot q (g x)) := funext fun x => by ring
  rw [← hmax.2, defectTrialEnergy, setAverage_eq, setAverage_eq, e,
    integral_add (i1.const_mul _) j23, integral_const_mul, integral_const_mul, ← hfv]
  simp only [smul_eq_mul]
  ring

/-- **(2.18)**: `(p, q) ↦ v(·, U, p, q)` is linear: for maximizers `v₁, v₂` for `(p₁, q₁)` and
`(p₂, q₂)`, `c₁ v₁ + c₂ v₂` is a maximizer for `(c₁ p₁ + c₂ p₂, c₁ q₁ + c₂ q₂)`. -/
theorem IsDefectMaximizer.linearCombination [NeZero d] {a : CoefficientField d Λ}
    {U : Set (Vec d)} (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U)
    (hne : U.Nonempty) {p₁ q₁ p₂ q₂ : Vec d} {v₁ v₂ : Vec d → ℝ} {g₁ g₂ : Vec d → Vec d}
    (h₁ : IsDefectMaximizer a U p₁ q₁ v₁ g₁) (h₂ : IsDefectMaximizer a U p₂ q₂ v₂ g₂)
    (c₁ c₂ : ℝ) :
    IsDefectMaximizer a U (c₁ • p₁ + c₂ • p₂) (c₁ • q₁ + c₂ • q₂)
      (fun x => c₁ * v₁ x + c₂ * v₂ x) (fun x => c₁ • g₁ x + c₂ • g₂ x) := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  refine isDefectMaximizer_of_setIntegral_dot_eq hUo hUb hUc hne
    (h₁.1.linearCombination hU h₂.1 c₁ c₂) fun w h hw => ?_
  have e1 := h₁.setIntegral_dot_eq hUb hU0 hw
  have e2 := h₂.setIntegral_dot_eq hUb hU0 hw
  have i1 := integrable_dot_mulVec_of_memLp a hw.1.2.1 h₁.1.1.2.1
  have i2 := integrable_dot_mulVec_of_memLp a hw.1.2.1 h₂.1.1.2.1
  have k1 := integrable_dot_flux_add a hU p₁ q₁ hw.1.2.1
  have k2 := integrable_dot_flux_add a hU p₂ q₂ hw.1.2.1
  have e : (fun x => -dot (c₁ • p₁ + c₂ • p₂) ((a x).mulVec (h x)) +
      dot (c₁ • q₁ + c₂ • q₂) (h x)) = fun x =>
        c₁ * (-dot p₁ ((a x).mulVec (h x)) + dot q₁ (h x)) +
          c₂ * (-dot p₂ ((a x).mulVec (h x)) + dot q₂ (h x)) := funext fun x => by
    simp only [dot_eq_dotProduct, add_dotProduct, smul_dotProduct, smul_eq_mul]
    ring
  simp only [dot_mulVec_linearCombination]
  rw [e, integral_add (i1.const_mul c₁) (i2.const_mul c₂), integral_add (k1.const_mul c₁)
    (k2.const_mul c₂), integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, e1, e2]

end QSH
