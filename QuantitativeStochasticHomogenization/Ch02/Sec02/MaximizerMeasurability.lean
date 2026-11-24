import QuantitativeStochasticHomogenization.Ch02.Sec02.Lemma213
import QuantitativeStochasticHomogenization.Ch01.Sec04.CubePoincare
import QuantitativeStochasticHomogenization.Ch03.Sec03.ScalarRmsCalculus

/-!
# Measurability of the flatness of the maximizer of `J`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.2: the expectation in Lemma 2.15 is that of the mean square
`⨍_{□_m} |v - ℓ_c - (v - ℓ_c)_{□_m}|²`, `ℓ_c(x) = c·x`, of a maximizer `v = v(·, □_m, p, q)` of (2.9);
this file proves that it is a measurable function of the coefficient field for every choice of the
maximizers (`measurable_setAverage_sq_sub_defectMaximizer`), which the book does not discuss.

As for the minimizers in Proposition 1.8 (`exists_measurable_almostMinimizingTests`), the maximizer
is approximated by functions chosen measurably from a countable family: by Lemma 2.1 its gradient is
`∇v = ∇u* - (p + ∇u)`, `u*` a maximizer of `μ*(□_m, q)` and `ℓ_p + u` the minimizer of `μ(□_m, p)`;
gradients of a countable dense family of `H¹(□_m)` with values of (2.1) within `1/(k + 1)` of
`μ*(□_m, q)` are within `C/(k + 1)` of `∇u*` in `L²` by the quadratic response
(`IsDualMaximizer.dualTrialEnergy_eq`, `exists_measurable_almostMaximizingGradients`), and the same
holds for `∇u` (`exists_measurable_defectApprox`). The Poincaré inequality on the cube turns the
convergence of the gradients into that of the mean squares.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- **The quadratic response of (2.1)** at a maximizer `u*` of `μ*(U, q)`: for `T ∈ H¹(U)`,
`⨍_U (-½ ∇T·a∇T + q·∇T) = μ*(U, q) - ⨍_U ½ (∇T - ∇u*)·a(∇T - ∇u*)`. -/
theorem IsDualMaximizer.dualTrialEnergy_eq {a : CoefficientField d Λ} {U : Set (Vec d)}
    (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤) {q : Vec d} {uN : Vec d → ℝ} {gN : Vec d → Vec d}
    (hmax : IsDualMaximizer a U q uN gN) {T : Vec d → ℝ} {G : Vec d → Vec d} (hT : H1 U T G) :
    dualTrialEnergy a U q G = dualEnergy a U q -
      ⨍ x in U, (1 / 2 : ℝ) * dot (G x - gN x) ((a x).mulVec (G x - gN x)) := by
  have := isFiniteMeasure_restrict.mpr hU
  have hh := hT.sub hmax.1
  have hfv := hmax.setIntegral_dot_eq hU0 hU hh
  have hgN := hmax.1.2.1
  have hhL := hh.2.1
  rw [← hmax.2]
  unfold dualTrialEnergy
  rw [setAverage_eq, setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul, smul_eq_mul, ← mul_sub]
  congr 1
  have i1 : Integrable (fun x => -(1 / 2 : ℝ) * dot (gN x) ((a x).mulVec (gN x)) + dot q (gN x))
      (volume.restrict U) :=
    ((integrable_dot_mulVec a U hgN).const_mul _).add (integrable_dot_left_of_memLp hU hgN q)
  have i2a : Integrable (fun x => dot q (G x - gN x)) (volume.restrict U) :=
    integrable_dot_left_of_memLp hU hhL q
  have i2b : Integrable (fun x => dot (G x - gN x) ((a x).mulVec (gN x))) (volume.restrict U) :=
    integrable_dot_mulVec_of_memLp a hhL hgN
  have i2 : Integrable (fun x => dot q (G x - gN x) - dot (G x - gN x) ((a x).mulVec (gN x)))
      (volume.restrict U) := i2a.sub i2b
  have i12 : Integrable (fun x => (-(1 / 2 : ℝ) * dot (gN x) ((a x).mulVec (gN x)) + dot q (gN x)) +
      (dot q (G x - gN x) - dot (G x - gN x) ((a x).mulVec (gN x)))) (volume.restrict U) :=
    i1.add i2
  have i3 : Integrable (fun x => (1 / 2 : ℝ) * dot (G x - gN x) ((a x).mulVec (G x - gN x)))
      (volume.restrict U) := (integrable_dot_mulVec a U hhL).const_mul _
  have hpt : (fun x => -(1 / 2 : ℝ) * dot (G x) ((a x).mulVec (G x)) + dot q (G x)) = fun x =>
      ((-(1 / 2 : ℝ) * dot (gN x) ((a x).mulVec (gN x)) + dot q (gN x)) +
        (dot q (G x - gN x) - dot (G x - gN x) ((a x).mulVec (gN x)))) -
        (1 / 2 : ℝ) * dot (G x - gN x) ((a x).mulVec (G x - gN x)) := by
    funext x
    have hs := dot_mulVec_comm_of_symm (a.symmetric x) (gN x) (G x)
    simp only [dot_eq_dotProduct, Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct] at hs ⊢
    change gN x ⬝ᵥ (a x).mulVec (G x) = G x ⬝ᵥ (a x).mulVec (gN x) at hs
    linarith
  rw [hpt, integral_sub i12 i3, integral_add i1 i2]
  have h0 : ∫ x in U, (dot q (G x - gN x) - dot (G x - gN x) ((a x).mulVec (gN x))) = 0 := by
    rw [integral_sub i2a i2b, hfv, sub_self]
  rw [h0, add_zero]

/-- **A measurable choice of almost maximizing gradients for (2.1)**. -/
theorem exists_measurable_almostMaximizingGradients {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hU : volume U ≠ ⊤) (hΛ : 0 ≤ Λ) (q : Vec d) :
    ∃ (T : ℕ → Vec d → ℝ) (G : ℕ → Vec d → Vec d), (∀ j, H1 U (T j) (G j)) ∧
      ∃ N : ℕ → CoefficientField d Λ → ℕ, (∀ k, Measurable (N k)) ∧
        ∀ (a : CoefficientField d Λ) (k : ℕ),
          dualEnergy a U q - 1 / ((k : ℝ) + 1) < dualTrialEnergy a U q (G (N k a)) := by
  obtain ⟨S, hSc, hSne, hSH, key⟩ := exists_countable_dualEnergy_eq_iSup (Λ := Λ) hU0 hU hΛ q
  obtain ⟨f, hf⟩ := hSc.exists_eq_range hSne
  have hfH : ∀ j, ∃ (u : Vec d → ℝ) (g : Vec d → Vec d) (h : H1 U u g), f j = h.2.1.toLp g :=
    fun j => hSH (hf ▸ Set.mem_range_self j)
  choose T G hTG hfG using hfH
  have hval : ∀ (a : CoefficientField d Λ) j,
      lpDualTrialEnergy a U q (f j) = dualTrialEnergy a U q (G j) := fun a j => by
    rw [hfG j, lpDualTrialEnergy_toLp a hU q]
  have hex : ∀ (a : CoefficientField d Λ) (k : ℕ), ∃ j,
      dualEnergy a U q - 1 / ((k : ℝ) + 1) < dualTrialEnergy a U q (G j) := by
    intro a k
    have hk : dualEnergy a U q - 1 / ((k : ℝ) + 1) < dualEnergy a U q := by
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    have hk' := hk
    have : Nonempty S := hSne.to_subtype
    rw [key a] at hk'
    obtain ⟨⟨F, hFS⟩, hF⟩ := exists_lt_of_lt_ciSup hk'
    rw [hf] at hFS
    obtain ⟨j, rfl⟩ := hFS
    refine ⟨j, ?_⟩
    rw [key a, ← hval a j]
    exact hF
  classical
  have hm : ∀ j, Measurable fun a : CoefficientField d Λ => dualTrialEnergy a U q (G j) := fun j => by
    have e : (fun a : CoefficientField d Λ => dualTrialEnergy a U q (G j)) =
        fun a => lpDualTrialEnergy a U q (f j) := funext fun a => (hval a j).symm
    rw [e]
    exact measurable_lpDualTrialEnergy U q (f j)
  refine ⟨T, G, hTG, fun k a => Nat.find (hex a k), fun k => measurable_find (fun a => hex a k)
    fun j => measurableSet_lt ((measurable_dualEnergy hU0 hU hΛ q).sub_const _) (hm j),
    fun a k => Nat.find_spec (hex a k)⟩

/-- **A measurable approximation of the maximizer of (2.9)**: functions `W i j ∈ H¹(U)` with
gradients `H i j` and measurable indices `N k`, `M k` such that, for every maximizer of
`J(U, p, q)` with gradient `g`, `∫_U |H (N k a) (M k a) - g|² ≤ 8 |U| / (k + 1)`. -/
theorem exists_measurable_defectApprox [NeZero d] {U : Set (Vec d)} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty) (hΛ : 0 ≤ Λ)
    (p q : Vec d) :
    ∃ (W : ℕ → ℕ → Vec d → ℝ) (H : ℕ → ℕ → Vec d → Vec d), (∀ i j, H1 U (W i j) (H i j)) ∧
      ∃ N M : ℕ → CoefficientField d Λ → ℕ, (∀ k, Measurable (N k)) ∧ (∀ k, Measurable (M k)) ∧
        ∀ (a : CoefficientField d Λ) (k : ℕ) (v : Vec d → ℝ) (g : Vec d → Vec d),
          IsDefectMaximizer a U p q v g →
          ∫ x in U, euclideanSq (H (N k a) (M k a) x - g x) ≤ 8 * volume.real U / ((k : ℝ) + 1) := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  have := isFiniteMeasure_restrict.mpr hU
  have hV : 0 < volume.real U := ENNReal.toReal_pos hU0 hU
  obtain ⟨T, G, hTG, N, hNm, hN⟩ := exists_measurable_almostMaximizingGradients (Λ := Λ) hU0 hU hΛ q
  obtain ⟨t, ht, M, hMm, hM⟩ := exists_measurable_almostMinimizingTests (Λ := Λ) hUb hU0 hΛ p
  have hlin := H1.linear hUb p
  refine ⟨fun i j x => T i x - (dot p x + t j x), fun i j x => G i x - (p + gradient (t j) x),
    fun i j => (hTG i).sub (hlin.add (ht j).h01.h1), N, M, hNm, hMm,
    fun a k v g hmax => ?_⟩
  obtain ⟨uN, gN, hdual⟩ := exists_isDualMaximizer a hUo hUb hUc hne q
  obtain ⟨uD, gD, hDir⟩ := exists_isDirichletMinimizer a hUb hU0 p
  have hJ := (lemma_2_1 a hUo hUb hUc hne p q).2.2 uN gN uD gD hdual hDir
  have hae := hmax.ae_eq hUb hU0 hJ
  -- the dual part
  have hd1 := hdual.dualTrialEnergy_eq hU0 hU (hTG (N k a))
  have hd2 := hN a k
  have hdual_le : ∫ x in U, euclideanSq (G (N k a) x - gN x) ≤ 2 * volume.real U / ((k : ℝ) + 1) := by
    have hint1 : Integrable (fun x => euclideanSq (G (N k a) x - gN x)) (volume.restrict U) :=
      integrable_euclideanSq_of_memLp ((hTG (N k a)).2.1.sub hdual.1.2.1)
    have hint2 : Integrable (fun x => (1 / 2 : ℝ) * dot (G (N k a) x - gN x)
        ((a x).mulVec (G (N k a) x - gN x))) (volume.restrict U) :=
      (integrable_dot_mulVec a U ((hTG (N k a)).2.1.sub hdual.1.2.1)).const_mul _
    have hpt : ∀ x, euclideanSq (G (N k a) x - gN x) ≤ 2 * ((1 / 2 : ℝ) *
        dot (G (N k a) x - gN x) ((a x).mulVec (G (N k a) x - gN x))) := fun x => by
      have := (a.elliptic x (G (N k a) x - gN x)).1
      linarith
    have hmono := integral_mono hint1 (hint2.const_mul 2) hpt
    rw [integral_const_mul] at hmono
    have havg : ⨍ x in U, (1 / 2 : ℝ) * dot (G (N k a) x - gN x)
        ((a x).mulVec (G (N k a) x - gN x)) < 1 / ((k : ℝ) + 1) := by linarith
    rw [setAverage_eq, smul_eq_mul, inv_mul_lt_iff₀ hV] at havg
    calc ∫ x in U, euclideanSq (G (N k a) x - gN x)
        ≤ 2 * ∫ x in U, (1 / 2 : ℝ) * dot (G (N k a) x - gN x)
            ((a x).mulVec (G (N k a) x - gN x)) := hmono
      _ ≤ 2 * (volume.real U * (1 / ((k : ℝ) + 1))) := by linarith
      _ = 2 * volume.real U / ((k : ℝ) + 1) := by ring
  -- the Dirichlet part
  have hq := (hDir.quadraticResponse hU (ht (M k a)).h01).1
  have hDir_le : ∫ x in U, euclideanSq (gradient (t (M k a)) x - gD x) ≤
      2 * volume.real U / ((k : ℝ) + 1) := by
    have h1 := hM a (M k a)
    have h2 := hM a k
    rw [setAverage_eq, smul_eq_mul] at hq
    have h3 : (volume.real U)⁻¹ * ∫ x in U, euclideanSq (gradient (t (M k a)) x - gD x) ≤
        2 * (1 / ((k : ℝ) + 1)) := by linarith
    rw [inv_mul_le_iff₀ hV] at h3
    calc ∫ x in U, euclideanSq (gradient (t (M k a)) x - gD x)
        ≤ volume.real U * (2 * (1 / ((k : ℝ) + 1))) := h3
      _ = 2 * volume.real U / ((k : ℝ) + 1) := by ring
  -- the sum
  have j1 : Integrable (fun x => 2 * euclideanSq (G (N k a) x - gN x)) (volume.restrict U) :=
    (integrable_euclideanSq_of_memLp ((hTG (N k a)).2.1.sub hdual.1.2.1)).const_mul 2
  have j2 : Integrable (fun x => 2 * euclideanSq (gradient (t (M k a)) x - gD x))
      (volume.restrict U) :=
    (integrable_euclideanSq_of_memLp (((ht (M k a)).h01.h1).2.1.sub hDir.1.2.1)).const_mul 2
  have hint : Integrable (fun x => 2 * euclideanSq (G (N k a) x - gN x) +
      2 * euclideanSq (gradient (t (M k a)) x - gD x)) (volume.restrict U) := j1.add j2
  have hle : ∫ x in U, euclideanSq (G (N k a) x - (p + gradient (t (M k a)) x) - g x) ≤
      ∫ x in U, (2 * euclideanSq (G (N k a) x - gN x) +
        2 * euclideanSq (gradient (t (M k a)) x - gD x)) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => euclideanSq_nonneg _) hint ?_
    filter_upwards [hae] with x hx
    rw [hx]
    have e : G (N k a) x - (p + gradient (t (M k a)) x) - (gN x - (p + gD x)) =
        (G (N k a) x - gN x) - (gradient (t (M k a)) x - gD x) := by abel
    rw [e]
    exact euclideanSq_sub_le_two _ _
  rw [integral_add j1 j2, integral_const_mul, integral_const_mul] at hle
  calc ∫ x in U, euclideanSq (G (N k a) x - (p + gradient (t (M k a)) x) - g x)
      ≤ 2 * (∫ x in U, euclideanSq (G (N k a) x - gN x)) +
        2 * ∫ x in U, euclideanSq (gradient (t (M k a)) x - gD x) := hle
    _ ≤ 2 * (2 * volume.real U / ((k : ℝ) + 1)) + 2 * (2 * volume.real U / ((k : ℝ) + 1)) := by
        linarith
    _ = 8 * volume.real U / ((k : ℝ) + 1) := by ring

end QSH
