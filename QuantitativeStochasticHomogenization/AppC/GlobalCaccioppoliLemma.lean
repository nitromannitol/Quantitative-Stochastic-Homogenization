import QuantitativeStochasticHomogenization.AppC.GlobalCaccioppoliBoundary

/-!
# Lemma C.8 on domains with boundary density

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix C, Lemma C.8: for a bounded Lipschitz domain `U` there is `C(U, d, Λ)` such that every
solution `u ∈ H¹₀(U)` of `-∇·(a∇u) = h` satisfies (C.17) and, for every `z ∈ ∂U` and `r > 0`,
(C.18).

The constant of (C.18) depends on the volume factor `|B_r(z) ∩ U| / |B_{r/2}(z) ∩ U|` (the book
controls it by `κ_U`) and, through the normalized `H̲^{-1}(B_r(z) ∩ U)` norm, on
`r |B_r(z) ∩ U|^{-1/d}`. Both are bounded when `U` has boundary density: `|B_r(z) ∩ U| ≥ c |B_r|`
for `z ∈ ∂U` and `0 < r ≤ R₀` (`HasBoundaryDensity`, which bounded Lipschitz domains have, with
the exterior density `|B_r(z) \ U| ≥ c |B_r|` used for Corollary C.9). For `r/2 > R₀`, with
`U ⊆ B_{R₀}(z)`, (C.18) is (C.17). `lemma_C_8_of_boundaryDensity` is Lemma C.8 under these
hypotheses.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- Interior and exterior density of `U` at its boundary up to the scale `R₀`:
`c |B_r| ≤ |B_r(z) ∩ U|` and `c |B_r| ≤ |B_r(z) \ U|` for `z ∈ ∂U` and `0 < r ≤ R₀`. -/
def HasBoundaryDensity (U : Set (Vec d)) (c R₀ : ℝ) : Prop :=
  ∀ z ∈ frontier U, ∀ r : ℝ, 0 < r → r ≤ R₀ →
    c * volume.real (ball z r) ≤ volume.real (ball z r ∩ U) ∧
      c * volume.real (ball z r) ≤ volume.real (ball z r \ U)

theorem volume_real_ball_eq (z : Vec d) {r : ℝ} (hr : 0 < r) :
    volume.real (ball z r) = r ^ d * (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal := by
  rw [measureReal_def, ball_eq_euclideanBall z hr]
  exact PDE.volume_euclideanBall_toReal_eq_unit_mul_of_pos z hr

/-- The constant `(2^d/c · 2 (4 (c |B_1|)^{-1/d} + 256 d + 2 d² + 16384 Λ))^{1/2}` of (C.18) on a
domain with boundary density `c`. -/
def boundaryCaccioppoliConstant (d : ℕ) (Λ c : ℝ) : ℝ :=
  Real.sqrt (2 ^ d / c * (2 * (2 * (2 * (c * (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal) ^
    (-(1 : ℝ) / d)) + 256 * d + 2 * d ^ 2 + 16384 * Λ)))

theorem boundaryCaccioppoliConstant_pos (d : ℕ) {Λ c : ℝ} (hΛ : 1 ≤ Λ) (hc : 0 < c) :
    0 < boundaryCaccioppoliConstant d Λ c := by
  have hω : 0 < (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal :=
    PDE.volume_euclideanBall_toReal_pos 0 one_pos
  have : 0 ≤ (c * (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal) ^ (-(1 : ℝ) / d) :=
    Real.rpow_nonneg (by positivity) _
  exact Real.sqrt_pos.mpr (by positivity)

/-- **(C.18) on a domain with boundary density.** If `U` has boundary density `c` up to `R₀`,
then for `z ∈ ∂U` and `r/2 ≤ R₀`, `|B_{r/2}(z) ∩ U| > 0` and
`‖∇u‖_{L̲²(B_{r/2}(z) ∩ U)} ≤ C (r^{-1} ‖u‖_{L̲²(B_r(z) ∩ U)} + ‖h‖_{H̲^{-1}(B_r(z) ∩ U)})` with
`C = boundaryCaccioppoliConstant d Λ c`. -/
theorem boundaryCaccioppoli_of_density (hd : 0 < d) {Λ : ℝ} (hΛ : 1 ≤ Λ) {U : Set (Vec d)}
    (hUo : IsOpen U) (a : CoefficientField d Λ) {u : Vec d → ℝ} {g : Vec d → Vec d}
    {f : Vec d → ℝ} {F : Vec d → Vec d} (hu : H01 U u g) (hf : MemLp f 2 (volume.restrict U))
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict U))
    (hdiv : HasWeakDivergence U (fun x => (a x).mulVec (g x) + F x) (fun x => -f x))
    {c R₀ : ℝ} (hc : 0 < c) (hden : HasBoundaryDensity U c R₀) {z : Vec d} (hz : z ∈ frontier U)
    {r : ℝ} (hr : 0 < r) (hrR : r / 2 ≤ R₀) :
    ENNReal.ofReal (vectorRms volume (ball z (r / 2) ∩ U) g) ≤
        ENNReal.ofReal (boundaryCaccioppoliConstant d Λ c) *
          (ENNReal.ofReal (r⁻¹ * scalarRms volume (ball z r ∩ U) u) +
            negativeSobolevOneNorm 2 (ball z r ∩ U) f F) ∧
      volume (ball z (r / 2) ∩ U) ≠ 0 := by
  set ω := (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal with hωdef
  have hω : 0 < ω := PDE.volume_euclideanBall_toReal_pos 0 one_pos
  set B₁ := 2 * (2 * (2 * (c * ω) ^ (-(1 : ℝ) / d)) + 256 * d + 2 * d ^ 2 + 16384 * Λ) with hB₁
  have hr2 : 0 < r / 2 := by linarith
  rw [boundaryCaccioppoliConstant, ← hωdef, ← hB₁]
  have hdz := (hden z hz (r / 2) hr2 hrR).1
  have hBpos : 0 < volume.real (ball z (r / 2)) := by
    rw [volume_real_ball_eq z hr2]
    positivity
  have hWpos : 0 < volume.real (ball z (r / 2) ∩ U) := lt_of_lt_of_le (by positivity) hdz
  have hW0 : volume (ball z (r / 2) ∩ U) ≠ 0 := by
    intro h0
    rw [measureReal_def, h0, ENNReal.toReal_zero] at hWpos
    exact lt_irrefl _ hWpos
  have hVt : volume (ball z r ∩ U) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono inter_subset_left)
    rw [ball_eq_euclideanBall z hr]
    exact PDE.volume_euclideanBall_ne_top z hr.le
  have hBrt : volume (ball z r) ≠ ⊤ := by
    rw [ball_eq_euclideanBall z hr]
    exact PDE.volume_euclideanBall_ne_top z hr.le
  have hWV : volume.real (ball z (r / 2) ∩ U) ≤ volume.real (ball z r ∩ U) :=
    measureReal_mono (inter_subset_inter_left U (ball_half_subset z)) hVt
  have hVB : volume.real (ball z r ∩ U) ≤ volume.real (ball z r) :=
    measureReal_mono inter_subset_left hBrt
  have hratio : volume.real (ball z r ∩ U) / volume.real (ball z (r / 2) ∩ U) ≤ 2 ^ d / c := by
    calc volume.real (ball z r ∩ U) / volume.real (ball z (r / 2) ∩ U)
        ≤ volume.real (ball z r) / volume.real (ball z (r / 2) ∩ U) :=
          div_le_div_of_nonneg_right hVB hWpos.le
      _ ≤ volume.real (ball z r) / (c * volume.real (ball z (r / 2))) :=
          div_le_div_of_nonneg_left measureReal_nonneg (by positivity) hdz
      _ = 2 ^ d / c := by
          have e : (r / 2) ^ d * 2 ^ d = r ^ d := by
            rw [← mul_pow, div_mul_cancel₀ r two_ne_zero]
          rw [volume_real_ball_eq z hr, volume_real_ball_eq z hr2,
            div_eq_div_iff (by positivity) hc.ne']
          linear_combination (-(c * ω)) * e
  have hnorm : r * (volume (ball z r ∩ U)).toReal ^ (-(1 : ℝ) / d) ≤
      2 * (c * ω) ^ (-(1 : ℝ) / d) := by
    have hexp : -(1 : ℝ) / d ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num)
      (Nat.cast_nonneg d)
    have h1 : (volume (ball z r ∩ U)).toReal ^ (-(1 : ℝ) / d) ≤
        (c * volume.real (ball z (r / 2))) ^ (-(1 : ℝ) / d) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (hdz.trans hWV) hexp
    have h2 : (c * volume.real (ball z (r / 2))) ^ (-(1 : ℝ) / d) =
        (r / 2)⁻¹ * (c * ω) ^ (-(1 : ℝ) / d) := by
      rw [volume_real_ball_eq z hr2, ← hωdef,
        show c * ((r / 2) ^ d * ω) = (r / 2) ^ d * (c * ω) by ring,
        Real.mul_rpow (pow_nonneg hr2.le d) (by positivity), neg_div,
        Real.rpow_neg (pow_nonneg hr2.le d), one_div,
        Real.pow_rpow_inv_natCast hr2.le (by omega)]
    calc r * (volume (ball z r ∩ U)).toReal ^ (-(1 : ℝ) / d)
        ≤ r * ((r / 2)⁻¹ * (c * ω) ^ (-(1 : ℝ) / d)) := by
          rw [← h2]
          exact mul_le_mul_of_nonneg_left h1 hr.le
      _ = 2 * (c * ω) ^ (-(1 : ℝ) / d) := by
          field_simp
  have h := boundaryCaccioppoli hΛ hUo a hu hf hF hdiv z hr hW0
  refine ⟨h.trans ?_, hW0⟩
  gcongr ENNReal.ofReal ?_ * _
  refine Real.sqrt_le_sqrt ?_
  have hn0 : 0 ≤ r * (volume (ball z r ∩ U)).toReal ^ (-(1 : ℝ) / d) :=
    mul_nonneg hr.le (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  refine mul_le_mul hratio ?_ (by positivity) (by positivity)
  rw [hB₁]
  linarith

/-- **Lemma C.8 (global Caccioppoli estimate)** for a bounded open set `U` of positive measure
with boundary density `c > 0` up to the scale `R₀`, where `U ⊆ B_{R₀}(z)` for every `z ∈ ∂U`:
there is `C(U, d, Λ)` such that for `h = f + ∇·F ∈ H^{-1}(U)` with `f ∈ L²(U)`,
`F ∈ L²(U; ℝ^d)` and `u ∈ H¹₀(U)` solving `-∇·(a∇u) = h` in `U`,
`‖∇u‖_{L̲²(U)} ≤ C ‖h‖_{H̲^{-1}(U)}` (C.17) and, for `z ∈ ∂U` and `r > 0`,
`‖∇u‖_{L̲²(B_{r/2}(z) ∩ U)} ≤ C (r^{-1} ‖u‖_{L̲²(B_r(z) ∩ U)} + ‖h‖_{H̲^{-1}(B_r(z) ∩ U)})`
(C.18). -/
theorem lemma_C_8_of_boundaryDensity {Λ : ℝ} (hΛ : 1 ≤ Λ) {U : Set (Vec d)} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hU0 : volume U ≠ 0) {c R₀ : ℝ} (hc : 0 < c)
    (hden : HasBoundaryDensity U c R₀) (hUR : ∀ z ∈ frontier U, U ⊆ ball z R₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : CoefficientField d Λ) (u : Vec d → ℝ) (g : Vec d → Vec d)
      (f : Vec d → ℝ) (F : Vec d → Vec d), H01 U u g →
      MemLp f 2 (volume.restrict U) →
      (∀ i, MemLp (fun x => F x i) 2 (volume.restrict U)) →
      HasWeakDivergence U (fun x => (a x).mulVec (g x) + F x) (fun x => -f x) →
      ENNReal.ofReal (vectorRms volume U g) ≤
          ENNReal.ofReal C * negativeSobolevOneNorm 2 U f F ∧
        ∀ z ∈ frontier U, ∀ r : ℝ, 0 < r →
          ENNReal.ofReal (vectorRms volume (ball z (r / 2) ∩ U) g) ≤
            ENNReal.ofReal C * (ENNReal.ofReal (r⁻¹ * scalarRms volume (ball z r ∩ U) u) +
              negativeSobolevOneNorm 2 (ball z r ∩ U) f F) := by
  obtain ⟨C₀, hC₀, h17⟩ := lemma_C_8_energy hΛ hUo hUb hU0
  set C₁ := boundaryCaccioppoliConstant d Λ c with hC₁
  refine ⟨max C₀ C₁, lt_max_of_lt_left hC₀, fun a u g f F hu hf hF hdiv => ⟨?_, ?_⟩⟩
  · exact (h17 a u g f F hu hf hF hdiv).trans (by gcongr; exact le_max_left _ _)
  intro z hz r hr
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · exfalso
    subst hd0
    obtain ⟨y, hy⟩ := nonempty_of_measure_ne_zero hU0
    have huniv : U = univ := eq_univ_of_forall fun x => by rwa [Subsingleton.elim x y]
    rw [huniv, frontier_univ] at hz
    exact hz
  have hr2 : 0 < r / 2 := by linarith
  by_cases hrR : r / 2 ≤ R₀
  · exact (boundaryCaccioppoli_of_density hd hΛ hUo a hu hf hF hdiv hc hden hz hr hrR).1.trans
      (by gcongr; exact le_max_right _ _)
  · rw [not_le] at hrR
    have h1 : U ⊆ ball z (r / 2) := (hUR z hz).trans fun x hx => by
      have hx' : euclideanNorm (x - z) < R₀ := hx
      change euclideanNorm (x - z) < r / 2
      linarith
    have h2 : U ⊆ ball z r := h1.trans (ball_half_subset z)
    rw [inter_eq_right.mpr h1, inter_eq_right.mpr h2]
    refine (h17 a u g f F hu hf hF hdiv).trans ?_
    gcongr
    · exact le_max_left _ _
    · exact le_add_self
