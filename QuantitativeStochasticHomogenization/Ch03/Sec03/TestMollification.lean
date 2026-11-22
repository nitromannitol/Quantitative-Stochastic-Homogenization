import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicProjection
import QuantitativeStochasticHomogenization.Ch03.Sec04.EuclideanSqNonneg

/-!
# Mollification of smooth compactly supported functions

Estimates for the smoothing `f ↦ ∫ ρ(y) f(· - y) dy` of a smooth compactly supported function by
a continuous probability density `ρ` supported in the closed ball of radius `ℓ`:

* the weighted Jensen inequality `(∫ g ρ)² ≤ ∫ g² ρ` for `∫ ρ = 1`;
* the translation estimate `∫ (f(x) - f(x - y))² dx ≤ |y|² ∫ |∇f|²`, from the fundamental theorem
  of calculus on the segment and Fubini;
* the mollification estimate `∫ (f - ρ * f)² ≤ ℓ² ∫ |∇f|²`;
* the pointwise bound `(∫ ρ(y) F(x - y) dy)² ≤ (sup ρ) ∫ F²`.
-/

open MeasureTheory Filter Set
open scoped Convolution Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- **Weighted Jensen inequality**: `(∫ g w)² ≤ ∫ g² w` for a weight with `∫ w = 1`. -/
theorem sq_integral_mul_le {X : Type*} [MeasurableSpace X] {ν : Measure X} {g w : X → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hw1 : ∫ x, w x ∂ν = 1) (hwi : Integrable w ν)
    (hgw : Integrable (fun x => g x * w x) ν) (hg2w : Integrable (fun x => g x ^ 2 * w x) ν) :
    (∫ x, g x * w x ∂ν) ^ 2 ≤ ∫ x, g x ^ 2 * w x ∂ν := by
  set m := ∫ x, g x * w x ∂ν with hm
  have h0 : 0 ≤ ∫ x, (g x - m) ^ 2 * w x ∂ν :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hw x)
  have hA : Integrable (fun x => g x ^ 2 * w x - 2 * m * (g x * w x)) ν :=
    hg2w.sub (hgw.const_mul _)
  have hB : Integrable (fun x => m ^ 2 * w x) ν := hwi.const_mul _
  have hC : Integrable (fun x => 2 * m * (g x * w x)) ν := hgw.const_mul _
  have h1 : ∫ x, (g x - m) ^ 2 * w x ∂ν =
      ∫ x, ((g x ^ 2 * w x - 2 * m * (g x * w x)) + m ^ 2 * w x) ∂ν :=
    integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [h1, integral_add hA hB, integral_sub hg2w hC, integral_const_mul, integral_const_mul, hw1,
    ← hm] at h0
  nlinarith

theorem continuous_coordinateDerivative {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) (j : Fin d) :
    Continuous (fun x => coordinateDerivative j f x) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem coordinateDerivative_eq_zero_of_notMem_tsupport {f : Vec d → ℝ} {x : Vec d}
    (hx : x ∉ tsupport f) (j : Fin d) : coordinateDerivative j f x = 0 := by
  have h : fderiv ℝ f x = 0 := by
    by_contra hne
    exact hx (support_fderiv_subset ℝ hne)
  simp [coordinateDerivative, h]

theorem hasCompactSupport_mul_of_right {g ρ : Vec d → ℝ} (hρ : HasCompactSupport ρ) :
    HasCompactSupport (fun y => g y * ρ y) :=
  hρ.mul_left

theorem fderiv_apply_eq_sum_coordinateDerivative {χ : Vec d → ℝ} (x v : Vec d) :
    fderiv ℝ χ x v = ∑ k, v k * coordinateDerivative k χ x := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : Pi.single k (v k) = v k • unitVector k := by
    ext j
    by_cases hj : j = k
    · subst hj
      simp [unitVector]
    · simp [unitVector, hj]
  rw [h, map_smul, smul_eq_mul]
  rfl

/-- The squared gradient `∑ⱼ (∂ⱼ f)²`. -/
def gradSq (f : Vec d → ℝ) (x : Vec d) : ℝ := ∑ j, coordinateDerivative j f x ^ 2

theorem gradSq_nonneg (f : Vec d → ℝ) (x : Vec d) : 0 ≤ gradSq f x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem continuous_gradSq {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (gradSq f) :=
  continuous_finsetSum _ fun j _ => (continuous_coordinateDerivative hf j).pow 2

theorem hasCompactSupport_gradSq {f : Vec d → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport (gradSq f) := by
  refine HasCompactSupport.intro hfc fun x hx => ?_
  have hx' : x ∉ tsupport f := hx
  simp [gradSq, coordinateDerivative_eq_zero_of_notMem_tsupport hx']

theorem integrable_gradSq {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    Integrable (gradSq f) :=
  (continuous_gradSq hf).integrable_of_hasCompactSupport (hasCompactSupport_gradSq hfc)

/-- The fundamental theorem of calculus on the segment from `x - y` to `x` and Jensen's
inequality: `(f(x) - f(x - y))² ≤ |y|² ∫₀¹ |∇f(x - y + t y)|² dt`. -/
theorem sq_sub_comp_sub_le {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) (x y : Vec d) :
    (f x - f (x - y)) ^ 2 ≤
      euclideanSq y * ∫ t in Ioc (0 : ℝ) 1, gradSq f (x - y + t • y) := by
  set γ : ℝ → ℝ := fun t => f (x - y + t • y) with hγ
  set γ' : ℝ → ℝ := fun t => fderiv ℝ f (x - y + t • y) y with hγ'
  have hpath : Continuous fun t : ℝ => x - y + t • y :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hderiv : ∀ t, HasDerivAt γ (γ' t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x - y + t • y) y t := by
      simpa using ((hasDerivAt_id t).smul_const y).const_add (x - y)
    exact ((hf.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt t h1
  have hcont : Continuous γ' :=
    ((hf.continuous_fderiv one_ne_zero).comp hpath).clm_apply continuous_const
  have hftc : ∫ t in (0 : ℝ)..1, γ' t = γ 1 - γ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hcont.intervalIntegrable _ _)
  have hγ1 : γ 1 = f x := by simp [γ]
  have hγ0 : γ 0 = f (x - y) := by simp [γ]
  rw [intervalIntegral.integral_of_le zero_le_one, hγ1, hγ0] at hftc
  rw [← hftc]
  have hprob : ∫ _ in Ioc (0 : ℝ) 1, (1 : ℝ) = 1 := by simp
  have hint : IntegrableOn γ' (Ioc 0 1) :=
    (hcont.integrableOn_Icc (a := 0) (b := 1)).mono_set Ioc_subset_Icc_self
  have hint2 : IntegrableOn (fun t => γ' t ^ 2) (Ioc 0 1) :=
    ((hcont.pow 2).integrableOn_Icc (a := 0) (b := 1)).mono_set Ioc_subset_Icc_self
  have hJ := sq_integral_mul_le (ν := volume.restrict (Ioc (0 : ℝ) 1)) (g := γ')
    (w := fun _ => 1) (fun _ => zero_le_one) hprob (integrable_const _)
    (by simpa using hint.integrable) (by simpa using hint2.integrable)
  simp only [mul_one] at hJ
  refine hJ.trans ?_
  rw [← integral_const_mul]
  have hG : Continuous fun t : ℝ => gradSq f (x - y + t • y) := (continuous_gradSq hf).comp hpath
  refine integral_mono hint2
    ((hG.integrableOn_Icc (a := 0) (b := 1)).mono_set Ioc_subset_Icc_self |>.const_mul _)
    fun t => ?_
  change (fderiv ℝ f (x - y + t • y) y) ^ 2 ≤ euclideanSq y * gradSq f (x - y + t • y)
  rw [fderiv_apply_eq_sum_coordinateDerivative]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => y k)
    (fun k => coordinateDerivative k f (x - y + t • y))
  have e1 : euclideanSq y = ∑ k, y k ^ 2 := by
    unfold euclideanSq dot
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e1]
  exact h

/-- **Translation estimate**: `∫ (f(x) - f(x - y))² dx ≤ |y|² ∫ |∇f|²`. -/
theorem integral_sq_sub_comp_sub_le {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (y : Vec d) :
    ∫ x, (f x - f (x - y)) ^ 2 ≤ euclideanSq y * ∫ x, gradSq f x := by
  set G := gradSq f with hGdef
  have hGc : Continuous G := continuous_gradSq hf
  have hGs : HasCompactSupport G := hasCompactSupport_gradSq hfc
  set I : Set ℝ := Ioc (0 : ℝ) 1 with hIdef
  set Φ : Vec d × ℝ → ℝ := fun p => G (p.1 - y + p.2 • y) with hΦdef
  have hΦc : Continuous Φ :=
    hGc.comp ((continuous_fst.sub continuous_const).add (continuous_snd.smul continuous_const))
  set K' : Set (Vec d) := (fun p : Vec d × ℝ => p.1 + y - p.2 • y) '' (tsupport G ×ˢ Icc 0 1)
    with hK'def
  have hK' : IsCompact K' :=
    (hGs.isCompact.prod isCompact_Icc).image
      ((continuous_fst.add continuous_const).sub (continuous_snd.smul continuous_const))
  have hΦint : Integrable Φ ((volume : Measure (Vec d)).prod (volume.restrict I)) := by
    have hprod : (volume : Measure (Vec d)).prod (volume.restrict I) =
        ((volume : Measure (Vec d)).prod (volume : Measure ℝ)).restrict (univ ×ˢ I) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [hprod]
    have hon : IntegrableOn Φ (K' ×ˢ Icc 0 1) ((volume : Measure (Vec d)).prod volume) :=
      hΦc.continuousOn.integrableOn_compact (hK'.prod isCompact_Icc)
    refine hon.of_forall_sdiff_eq_zero (MeasurableSet.univ.prod measurableSet_Ioc) ?_
    rintro ⟨x, t⟩ ⟨⟨-, ht⟩, hnot⟩
    have htI : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
    have hx : x ∉ K' := fun hx => hnot ⟨hx, htI⟩
    change G (x - y + t • y) = 0
    by_contra hne
    apply hx
    refine ⟨(x - y + t • y, t), ⟨subset_tsupport _ hne, htI⟩, ?_⟩
    change x - y + t • y + y - t • y = x
    abel
  have hswap := integral_integral_swap (f := fun x t => Φ (x, t)) hΦint
  have hinner : ∀ t : ℝ, ∫ x, Φ (x, t) = ∫ x, G x := by
    intro t
    have e : (fun x => Φ (x, t)) = fun x => G (x + (t • y - y)) := by
      funext x
      change G (x - y + t • y) = G (x + (t • y - y))
      congr 1
      abel
    rw [e]
    exact integral_add_right_eq_self G (t • y - y)
  have hvolI : (volume.restrict I).real univ = 1 := by
    simp [hIdef, measureReal_def]
  have hright : ∫ t, ∫ x, Φ (x, t) ∂volume ∂(volume.restrict I) = ∫ x, G x := by
    simp_rw [hinner]
    rw [integral_const, smul_eq_mul, hvolI, one_mul]
  have hLint : Integrable fun x => (f x - f (x - y)) ^ 2 := by
    have hc : Continuous fun x => (f x - f (x - y)) ^ 2 :=
      (hf.continuous.sub (hf.continuous.comp (continuous_id.sub continuous_const))).pow 2
    refine hc.integrable_of_hasCompactSupport ?_
    have h1 : HasCompactSupport fun x => f (x - y) := by
      have := hfc.comp_homeomorph (Homeomorph.subRight y)
      simpa [Function.comp_def] using this
    have h2 : HasCompactSupport fun x => f x - f (x - y) := hfc.sub h1
    have h3 := h2.mul_left (f := fun x => f x - f (x - y))
    convert h3 using 1
    funext x
    simp [pow_two]
  calc ∫ x, (f x - f (x - y)) ^ 2
      ≤ ∫ x, euclideanSq y * ∫ t in I, Φ (x, t) :=
        integral_mono hLint (hΦint.integral_prod_left.const_mul _) fun x =>
          sq_sub_comp_sub_le hf x y
    _ = euclideanSq y * ∫ x, G x := by
        rw [integral_const_mul, hswap, hright]

/-- **The mollification estimate** `∫ (f - ρ * f)² ≤ ℓ² ∫ |∇f|²` for a continuous probability
density `ρ` supported in the closed ball of radius `ℓ`. -/
theorem integral_sq_sub_mollify_le {f ρ : Vec d → ℝ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ)
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∫ y, ρ y = 1) {ℓ : ℝ}
    (hρℓ : ∀ y, ρ y ≠ 0 → euclideanSq y ≤ ℓ ^ 2) :
    ∫ x, (f x - ∫ y, ρ y * f (x - y)) ^ 2 ≤ ℓ ^ 2 * ∫ x, gradSq f x := by
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρs
  set Ψ : Vec d × Vec d → ℝ := fun p => (f p.1 - f (p.1 - p.2)) ^ 2 * ρ p.2 with hΨdef
  have hΨc : Continuous Ψ :=
    ((hf.continuous.comp continuous_fst).sub
      (hf.continuous.comp (continuous_fst.sub continuous_snd))).pow 2 |>.mul
      (hρc.comp continuous_snd)
  have hΨs : HasCompactSupport Ψ := by
    refine HasCompactSupport.intro
      (((hfc.isCompact.add hρs.isCompact).union hfc.isCompact).prod hρs.isCompact) ?_
    rintro ⟨x, y⟩ hxy
    by_contra hne
    apply hxy
    have hρy : ρ y ≠ 0 := fun h => hne (by simp [Ψ, h])
    have hdiff : f x - f (x - y) ≠ 0 := fun h => hne (by simp [Ψ, h])
    refine ⟨?_, subset_tsupport _ hρy⟩
    by_cases hfx : f x = 0
    · have hfxy : f (x - y) ≠ 0 := fun h => hdiff (by rw [hfx, h, sub_zero])
      left
      exact ⟨x - y, subset_tsupport _ hfxy, y, subset_tsupport _ hρy, sub_add_cancel x y⟩
    · right
      exact subset_tsupport _ hfx
  have hΨi : Integrable Ψ ((volume : Measure (Vec d)).prod volume) :=
    hΨc.integrable_of_hasCompactSupport hΨs
  have hcomp : ∀ x, Integrable fun y => f (x - y) * ρ y := by
    intro x
    have hfcont := hf.continuous
    have hc : Continuous fun y => f (x - y) * ρ y := by fun_prop
    exact hc.integrable_of_hasCompactSupport (hasCompactSupport_mul_of_right hρs)
  have hpt : ∀ x, f x - ∫ y, ρ y * f (x - y) = ∫ y, (f x - f (x - y)) * ρ y := by
    intro x
    have e : (fun y => (f x - f (x - y)) * ρ y) = fun y => f x * ρ y - f (x - y) * ρ y := by
      funext y
      ring
    rw [e, integral_sub (hρi.const_mul _) (hcomp x), integral_const_mul, hρ1, mul_one]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun y => by simp [mul_comm])
  have hJ : ∀ x, (f x - ∫ y, ρ y * f (x - y)) ^ 2 ≤ ∫ y, Ψ (x, y) := by
    intro x
    rw [hpt]
    have hgw : Integrable fun y => (f x - f (x - y)) * ρ y := by
      have e : (fun y => (f x - f (x - y)) * ρ y) = fun y => f x * ρ y - f (x - y) * ρ y := by
        funext y
        ring
      rw [e]
      exact (hρi.const_mul _).sub (hcomp x)
    have hg2w : Integrable fun y => (f x - f (x - y)) ^ 2 * ρ y := by
      have hfcont := hf.continuous
      have hc : Continuous fun y => (f x - f (x - y)) ^ 2 * ρ y := by fun_prop
      exact hc.integrable_of_hasCompactSupport (hasCompactSupport_mul_of_right hρs)
    exact sq_integral_mul_le hρ0 hρ1 hρi hgw hg2w
  set I := ∫ x, gradSq f x with hIdef
  have hI : 0 ≤ I := integral_nonneg fun x => gradSq_nonneg f x
  have hswap := integral_integral_swap (f := fun x y => Ψ (x, y)) hΨi
  have hinner : ∀ y, ∫ x, Ψ (x, y) = (∫ x, (f x - f (x - y)) ^ 2) * ρ y := fun y => by
    show ∫ x, (f x - f (x - y)) ^ 2 * ρ y = _
    exact integral_mul_const _ _
  calc ∫ x, (f x - ∫ y, ρ y * f (x - y)) ^ 2
      ≤ ∫ x, ∫ y, Ψ (x, y) :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
          hΨi.integral_prod_left (Eventually.of_forall hJ)
    _ = ∫ y, (∫ x, (f x - f (x - y)) ^ 2) * ρ y := by
        rw [hswap]
        exact integral_congr_ae (Eventually.of_forall hinner)
    _ ≤ ∫ y, ℓ ^ 2 * I * ρ y := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun y =>
          mul_nonneg (integral_nonneg fun x => sq_nonneg _) (hρ0 y)) (hρi.const_mul _)
          (Eventually.of_forall fun y => ?_)
        by_cases hy : ρ y = 0
        · simp [hy]
        · refine mul_le_mul_of_nonneg_right ?_ (hρ0 y)
          calc ∫ x, (f x - f (x - y)) ^ 2 ≤ euclideanSq y * I :=
                integral_sq_sub_comp_sub_le hf hfc y
            _ ≤ ℓ ^ 2 * I := mul_le_mul_of_nonneg_right (hρℓ y hy) hI
    _ = ℓ ^ 2 * I := by rw [integral_const_mul, hρ1, mul_one]

end QSH
