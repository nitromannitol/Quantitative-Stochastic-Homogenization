import QuantitativeStochasticHomogenization.Ch04.Sec04.SelectedObservationAbsorption
import QuantitativeStochasticHomogenization.Ch04.Sec04.LocalizedEnergyFromObservation

/-!
# The observation estimate from a finite-ball observation and the smoothed correctors

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.21 (consultant note S9, step 2, and SCOTT-localization (4)–(6)). Two analytic
inputs are isolated.

* `FiniteBallObservation d Λ σ θ k`: above a random radius at the center `z`, every
  `a`-harmonic `u` on `B_T(z)` with `L₀ S ≤ T` satisfies
  `∫_{B_S(z)} u² ≤ C (|B_S| I[u] + (S/T)^{2k} ∫_{B_T(z)} u²)`, where `I` is the objective of the
  coordinate minimization (the truncated Gaussian observation at scale `σ S` on `B_{S/θ}(z)`).
* `SmoothedCorrectorObservation`: for some constant `c`, the observation of `φ_{e_i} - c` is at
  most `(S Y)²` with `Y = O_s(C S^{-β})`, deterministically small above a random radius.

The selected coordinate `w_i` and the corrected coordinate `h = (x - z)_i + φ_{e_i} - c` are both
admissible, so `I[w_i - h] ≤ 4 I[φ_{e_i} - c]`. The outer term is absorbed through the Poincaré
inequality on `B_T` and the admissible gradient bounds, which costs `(S/T)^{2k - 2d - 2} S²` and
is at most `S^{2 - 2β}` once `k ≥ d + 1 + β(1 + δ)/ε`. This gives
`LocalizationObservationEstimate`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- **The finite-ball observation** of SCOTT-localization (4) at an arbitrary center: there are
`L₀ ≥ 1` and `C` and, for every `τ < d`, a constant `C_τ` such that for every law and center `z`
there is a random radius `X ≥ 1` with `X ≤ O_τ(C_τ)` such that almost surely, for `X ≤ S` and
`L₀ S ≤ T`, every `a`-harmonic `u` on `B_T(z)` satisfies
`∫_{B_S(z)} u² ≤ C (|B_S| I[u] + (S/T)^{2k} ∫_{B_T(z)} u²)`. -/
def FiniteBallObservation (d : ℕ) (Λ σ θ k : ℝ) : Prop :=
  ∃ (L₀ C : ℝ), 1 ≤ L₀ ∧ 0 < C ∧ ∀ τ : ℝ, 0 < τ → τ < d → ∃ Cτ : ℝ, 0 < Cτ ∧
    ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ z : Vec d,
      ∃ X : CoefficientField d Λ → ℝ, Measurable X ∧ OsBound P X τ Cτ ∧ (∀ a, 1 ≤ X a) ∧
        ∀ᵐ a ∂P, ∀ S T : ℝ, X a ≤ S → L₀ * S ≤ T → ∀ u : LocalHarmonic a z T,
          ∫ x in ball z S, u.potential x ^ 2 ≤
            C * (volume.real (ball z S) * localizationObjective z T S σ θ u.potential +
              (S / T) ^ (2 * k) * ∫ x in ball z T, u.potential x ^ 2)

/-- **The observation of the smoothed correctors** at the intermediate scale `S = r^{1+δ-ε}`:
for every center and `r ≥ 2` there are nonnegative `X, Y` with `X^γ ≤ O_s(C)` and
`Y ≤ O_s(C S^{-β})` such that almost surely, if `X ≤ r`, then `Y ≤ C r^{-μ}` and for every `i`
some constant `c` has `I[φ_{e_i} - c] ≤ (S Y)²`. -/
def SmoothedCorrectorObservation {P : Measure (CoefficientField d Λ)} (S : HomogenizationData P)
    (s δ γ α σ θ β μ C : ℝ) : Prop :=
  ∀ (z : Vec d) (r : ℝ), 2 ≤ r → ∃ X Y : CoefficientField d Λ → ℝ, (∀ a, 0 ≤ X a) ∧
    (∀ a, 0 ≤ Y a) ∧ AEOsBound P (fun a => X a ^ γ) s C ∧
    AEOsBound P Y s (C * localizationIntermediateRadius δ α γ r ^ (-β)) ∧
    ∀ᵐ a ∂P, X a ≤ r → Y a ≤ C * r ^ (-μ) ∧ ∀ i : Fin d, ∃ c : ℝ,
      localizationObjective z (localizationOuterRadius δ r) (localizationIntermediateRadius δ α γ r)
        σ θ (fun x => (S.corrector (unitVector i)).potential a x - c) ≤
          (localizationIntermediateRadius δ α γ r * Y a) ^ 2

theorem integral_euclideanSq_grad_le_of_admissible' {a : CoefficientField d Λ} {z : Vec d}
    {T C : ℝ} (hT : 0 < T) (hC : 0 ≤ C) (w : LocalHarmonic a z T)
    (hw : IsLocalizationAdmissible C w) :
    ∫ x in ball z T, euclideanSq (w.grad x) ≤ C ^ 2 * volume.real (ball z T) := by
  rw [w.integral_euclideanSq_grad]
  exact (w.admissible_iff hC hT).1 hw

theorem volume_real_ball_div {z : Vec d} {S T : ℝ} (hS : 0 < S) (hT : 0 < T) :
    volume.real (ball z T) / volume.real (ball z S) = (T / S) ^ d := by
  rw [volume_real_ball_eq_mul z hT, volume_real_ball_eq_mul z hS, div_pow]
  have h1 : 0 < volume.real (ball (0 : Vec d) 1) := volume_real_ball_pos 0 one_pos
  have hS' : S ^ d ≠ 0 := pow_ne_zero d hS.ne'
  field_simp

/-- **The observation of one selected coordinate, deterministically**: the finite-ball
observation, the competitor comparison and the absorption of the outer term. -/
theorem selected_observation_le {a : CoefficientField d Λ} {z : Vec d} {T S σ θ C₀ CD k : ℝ}
    (hS : 0 < S) (hST : S ≤ T) (hσS : σ * S ≠ 0) (hC₀ : 0 ≤ C₀) (hCD : 0 ≤ CD) {i : Fin d}
    (hDa : ∀ u : LocalHarmonic a z T, ∫ x in ball z S, u.potential x ^ 2 ≤
      CD * (volume.real (ball z S) * localizationObjective z T S σ θ u.potential +
        (S / T) ^ (2 * k) * ∫ x in ball z T, u.potential x ^ 2))
    (habs : CD * (S / T) ^ (2 * k) * (2 * (T / S) ^ d) ≤ 1 / 2)
    (w : LocalHarmonic a z T) (hw : IsCoordinateMinimizer S σ θ C₀ i w)
    {φ : Vec d → ℝ} {g : Vec d → Vec d} (hφg : HasWeakGradient Set.univ φ g)
    (hloc : ∀ R : ℝ, 0 < R → MemLp φ 2 (volume.restrict (ball 0 R)) ∧
      MemLp g 2 (volume.restrict (ball 0 R)))
    (harm : HasWeakDivergence Set.univ (fun x => (a x).mulVec (unitVector i + g x))
      (fun _ => 0)) (c : ℝ)
    (hadm : vectorRms volume (ball z T) (fun x => unitVector i + g x) ≤ C₀)
    {Y : ℝ} (hY : localizationObjective z T S σ θ (fun x => φ x - c) ≤ (S * Y) ^ 2) :
    ∫ x in ball z S, (w.potential x - (x - z) i - φ x - (-c)) ^ 2 ≤
      volume.real (ball z S) * (8 * CD * (S * Y) ^ 2 +
        24 * CD * (S / T) ^ (2 * k) * (T / S) ^ (2 * d) * (2 ^ d * (2 * T)) ^ 2 * C₀ ^ 2) := by
  have hT : 0 < T := lt_of_lt_of_le hS hST
  set h := localCorrectedCoordinate a z T i c φ g hφg hloc harm with hhdef
  have hhadm : IsLocalizationAdmissible C₀ h := hadm
  set u := w.sub h with hudef
  have hupot : ∀ x, u.potential x = w.potential x - (x - z) i - φ x - (-c) := fun x => by
    simp only [hudef, LocalHarmonic.sub, hhdef, localCorrectedCoordinate_potential]
    ring
  -- the competitor
  have hI : localizationObjective z T S σ θ u.potential ≤ 4 * (S * Y) ^ 2 := by
    have h1 := hw.localizationObjective_sub_corrected_le hσS c φ g hφg hloc harm hadm
    exact h1.trans (by linarith)
  -- the gradient bound
  have hgw := integral_euclideanSq_grad_le_of_admissible' hT hC₀ w hw.1
  have hgh := integral_euclideanSq_grad_le_of_admissible' hT hC₀ h hhadm
  have hgrad : ∫ x in ball z T, euclideanSq (u.grad x) ≤ 4 * C₀ ^ 2 * volume.real (ball z T) := by
    have hint1 : IntegrableOn (fun x => euclideanSq (w.grad x)) (ball z T) :=
      integrableOn_euclideanSq_of_memLp fun k => w.memLp_grad k
    have hint2 : IntegrableOn (fun x => euclideanSq (h.grad x)) (ball z T) :=
      integrableOn_euclideanSq_of_memLp fun k => h.memLp_grad k
    have hint3 : IntegrableOn (fun x => euclideanSq (u.grad x)) (ball z T) :=
      integrableOn_euclideanSq_of_memLp fun k => u.memLp_grad k
    calc ∫ x in ball z T, euclideanSq (u.grad x)
        ≤ ∫ x in ball z T, (2 * euclideanSq (w.grad x) + 2 * euclideanSq (h.grad x)) :=
          setIntegral_mono_on hint3 ((hint1.const_mul 2).add (hint2.const_mul 2))
            (measurableSet_ball z T) fun x _ => euclideanSq_sub_le (w.grad x) (h.grad x)
      _ = 2 * (∫ x in ball z T, euclideanSq (w.grad x)) +
            2 * ∫ x in ball z T, euclideanSq (h.grad x) := by
          rw [integral_add (hint1.const_mul 2) (hint2.const_mul 2), integral_const_mul,
            integral_const_mul]
      _ ≤ 4 * C₀ ^ 2 * volume.real (ball z T) := by linarith
  -- the outer energy
  have hBS : 0 < volume.real (ball z S) := volume_real_ball_pos z hS
  have hXdef := volume_real_ball_div (z := z) hS hT
  set X := volume.real (ball z T) / volume.real (ball z S) with hX
  have hX1 : 1 ≤ X := by
    rw [hXdef]
    exact one_le_pow₀ ((one_le_div hS).2 hST)
  have hBT : volume.real (ball z T) = X * volume.real (ball z S) := by
    have := hBS.ne'
    rw [hX]; field_simp
  have hout := integral_sq_le_of_inner (z := z) hS hST u.square_integrable
  have hP := u.integral_sub_average_sq_le hT
  set A := ∫ x in ball z S, u.potential x ^ 2 with hA
  set B := ∫ x in ball z T, u.potential x ^ 2 with hB
  set V := ∫ x in ball z T, (u.potential x - ⨍ y in ball z T, u.potential y) ^ 2 with hV
  set G := ∫ x in ball z T, euclideanSq (u.grad x) with hG
  set q := (S / T) ^ (2 * k) with hq
  set P := (2 ^ d * (2 * T)) ^ 2 with hPdef
  have hq0 : 0 ≤ q := Real.rpow_nonneg (div_nonneg hS.le hT.le) _
  have hP0 : 0 ≤ P := sq_nonneg _
  have hD1 := hDa u
  have hV' : V ≤ P * (4 * C₀ ^ 2 * (X * volume.real (ball z S))) := by
    rw [← hBT]; exact hP.trans (mul_le_mul_of_nonneg_left hgrad hP0)
  have hA0 : 0 ≤ A := setIntegral_nonneg (measurableSet_ball z S) fun x _ => sq_nonneg _
  have hV0 : 0 ≤ V := setIntegral_nonneg (measurableSet_ball z T) fun x _ => sq_nonneg _
  -- the combination
  have hX3 : 1 + 2 * X ≤ 3 * X := by linarith
  have h1 : A ≤ CD * (volume.real (ball z S) * (4 * (S * Y) ^ 2)) + CD * q * B := by
    calc A ≤ CD * (volume.real (ball z S) * localizationObjective z T S σ θ u.potential + q * B) :=
          hD1
      _ ≤ CD * (volume.real (ball z S) * (4 * (S * Y) ^ 2) + q * B) :=
          mul_le_mul_of_nonneg_left (add_le_add_left (mul_le_mul_of_nonneg_left hI hBS.le) _) hCD
      _ = CD * (volume.real (ball z S) * (4 * (S * Y) ^ 2)) + CD * q * B := by ring
  have h2 : CD * q * B ≤ CD * q * (2 * X * A) + CD * q * (3 * X * V) := by
    have := mul_le_mul_of_nonneg_left hout (mul_nonneg hCD hq0)
    have h3 : (1 + 2 * X) * V ≤ 3 * X * V := mul_le_mul_of_nonneg_right hX3 hV0
    calc CD * q * B ≤ CD * q * (2 * X * A + (1 + 2 * X) * V) := this
      _ ≤ CD * q * (2 * X * A + 3 * X * V) :=
          mul_le_mul_of_nonneg_left (add_le_add_right h3 _) (mul_nonneg hCD hq0)
      _ = CD * q * (2 * X * A) + CD * q * (3 * X * V) := by ring
  have h4 : CD * q * (2 * X * A) ≤ A / 2 := by
    have := mul_le_mul_of_nonneg_right habs hA0
    rw [← hXdef] at this
    calc CD * q * (2 * X * A) = CD * q * (2 * X) * A := by ring
      _ ≤ 1 / 2 * A := this
      _ = A / 2 := by ring
  have h5 : CD * q * (3 * X * V) ≤
      CD * q * (3 * X * (P * (4 * C₀ ^ 2 * (X * volume.real (ball z S))))) := by
    have : 0 ≤ CD * q * (3 * X) := mul_nonneg (mul_nonneg hCD hq0) (by linarith)
    calc CD * q * (3 * X * V) = CD * q * (3 * X) * V := by ring
      _ ≤ CD * q * (3 * X) * (P * (4 * C₀ ^ 2 * (X * volume.real (ball z S)))) :=
          mul_le_mul_of_nonneg_left hV' this
      _ = _ := by ring
  have hfin : A ≤ 2 * (CD * (volume.real (ball z S) * (4 * (S * Y) ^ 2))) +
      2 * (CD * q * (3 * X * (P * (4 * C₀ ^ 2 * (X * volume.real (ball z S)))))) := by
    linarith
  have hgoal : ∫ x in ball z S, (w.potential x - (x - z) i - φ x - (-c)) ^ 2 = A := by
    rw [hA]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only [hupot])
  rw [hgoal]
  rw [hXdef] at hfin
  refine hfin.trans (le_of_eq ?_)
  ring

end QSH
