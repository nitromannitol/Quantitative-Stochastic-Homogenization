import QuantitativeStochasticHomogenization.Ch04.Sec04.CompactTestProfile
import QuantitativeStochasticHomogenization.Ch04.Sec04.CompactTestFluxBound

/-!
# The scale derivative of the compact averages

The first bound of (3) in the finite-ball estimate of the proof of
Lemma 4.21 in Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*.

For the adapted profile `ρ` of the symmetric part `Dₛ` of the homogenized matrix `D` and its
partner `χ`, the averages `V_α(b, x) = ∫ F(w) ∂^α(ρ_b)(x - w) dw` of the zero extension `F` of a
local `a`-harmonic `u` have the scale derivative
`∂_b V_α = -b^{-c-1} ∫ F(w) ((c + y·∇)∂^αρ)((x - w)/b) dw`, `c = d + |α|`, and the scale identity
`(c + y·∇)∂^αρ = ∑ᵢⱼ (Dₛ)ᵢⱼ ∂ᵢ∂ⱼ ∂^αχ` turns the last pairing into `b²` times the pairing of `u` with
`∑ᵢⱼ (D eᵢ)ⱼ ∂ⱼ∂ᵢψ` for the test `ψ(w) = ∂^αχ((x - w)/b)`. The tensor identity bounds it by
`S (d³ + d²√d Λ) |B_r|^{1/2} C₁ r^{1-μ} ‖∇u‖_{L²(B_r)}`, where `S` bounds the second derivatives of
`∂^αχ` (`abs_kernelPairing_eulerOp_le`).
-/

open MeasureTheory Filter Set
open scoped ContDiff

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The symmetric part `(D + Dᵀ)/2`. -/
def symmPart' (D : Mat d) : Mat d := (1 / 2 : ℝ) • (D + D.transpose)

theorem symmPart'_transpose (D : Mat d) : (symmPart' D).transpose = symmPart' D := by
  unfold symmPart'
  rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

/-- The reflected dilated test `w ↦ g((x - w)/b)`. -/
def reflectedTest (g : Vec d → ℝ) (b : ℝ) (x w : Vec d) : ℝ := g (b⁻¹ • (x - w))

theorem reflectedTest_eq (g : Vec d → ℝ) (b : ℝ) (x : Vec d) :
    reflectedTest g b x = fun w => dilate b g (x - w) := rfl

theorem contDiff_reflectedTest {g : Vec d → ℝ} (hg : ContDiff ℝ ∞ g) (b : ℝ) (x : Vec d) :
    ContDiff ℝ ∞ (reflectedTest g b x) :=
  (contDiff_dilate hg b).comp (contDiff_const.sub contDiff_id)

/-- The second derivatives of the reflected dilated test. -/
theorem coordinateDerivative_coordinateDerivative_reflectedTest {g : Vec d → ℝ}
    (hg : ContDiff ℝ ∞ g) (b : ℝ) (x : Vec d) (i j : Fin d) (w : Vec d) :
    coordinateDerivative j (coordinateDerivative i (reflectedTest g b x)) w =
      (b⁻¹) ^ 2 * coordinateDerivative j (coordinateDerivative i g) (b⁻¹ • (x - w)) := by
  rw [reflectedTest_eq, coordinateDerivative_coordinateDerivative_comp_sub (contDiff_dilate hg b),
    coordinateDerivative_dilate (hg.differentiable (by simp)),
    coordinateDerivative_const_mul' ((contDiff_dilate (contDiff_coordinateDerivative hg i)
      b).differentiable (by simp)),
    coordinateDerivative_dilate ((contDiff_coordinateDerivative hg i).differentiable (by simp))]
  simp only [dilate]
  ring

theorem euclideanNorm_le_of_euclideanSq_smul_le {b : ℝ} (hb : 0 < b) {z : Vec d}
    (h : euclideanSq (b⁻¹ • z) ≤ 1 / 4) : euclideanNorm z ≤ b / 2 := by
  have e : euclideanSq (b⁻¹ • z) = (b⁻¹) ^ 2 * euclideanSq z := euclideanSq_smul' _ _
  rw [e] at h
  have h2 : euclideanSq z ≤ (b / 2) ^ 2 := by
    have hb2 : 0 < (b⁻¹) ^ 2 := by positivity
    have : euclideanSq z ≤ (1 / 4) / (b⁻¹) ^ 2 := by rw [le_div_iff₀ hb2]; linarith
    calc euclideanSq z ≤ (1 / 4) / (b⁻¹) ^ 2 := this
      _ = (b / 2) ^ 2 := by field_simp; ring
  calc euclideanNorm z = Real.sqrt (euclideanSq z) := rfl
    _ ≤ Real.sqrt ((b / 2) ^ 2) := Real.sqrt_le_sqrt h2
    _ = b / 2 := Real.sqrt_sq (by linarith)

/-- **The reflected test is a test on `B_r`** when `g` vanishes for `|y|² > 1/4` and
`|x| + b/2 < r`. -/
theorem isSpatialTest_reflectedTest {g : Vec d → ℝ} (hg : ContDiff ℝ ∞ g)
    (hg0 : ∀ y, 1 / 4 < euclideanSq y → g y = 0) {b r : ℝ} (hb : 0 < b) {x : Vec d}
    (hx : euclideanNorm x + b / 2 < r) : IsSpatialTest (ball 0 r) (reflectedTest g b x) := by
  set Kset : Set (Vec d) := {w | euclideanSq (b⁻¹ • (x - w)) ≤ 1 / 4} with hKset
  have hKc : IsClosed Kset :=
    isClosed_le (contDiff_euclideanSq.continuous.comp (by fun_prop :
      Continuous fun w : Vec d => b⁻¹ • (x - w))) continuous_const
  have hKsub : Kset ⊆ ball 0 r := fun w hw => by
    have h1 := euclideanNorm_le_of_euclideanSq_smul_le hb hw
    have h2 : euclideanNorm w ≤ euclideanNorm x + euclideanNorm (x - w) := by
      have h3 := euclideanNorm_add_le x (w - x)
      rw [add_sub_cancel] at h3
      have h4 : euclideanNorm (w - x) = euclideanNorm (x - w) := by
        unfold euclideanNorm euclideanSq dot
        congr 1
        exact Finset.sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring
      linarith
    show euclideanNorm (w - 0) < r
    rw [sub_zero]
    linarith
  have hsupp : Function.support (reflectedTest g b x) ⊆ Kset := fun w hw => by
    by_contra hc
    exact hw (hg0 _ (not_le.mp hc))
  have htsupp : tsupport (reflectedTest g b x) ⊆ Kset := closure_minimal hsupp hKc
  refine ⟨contDiff_reflectedTest hg b x, ?_, htsupp.trans hKsub⟩
  have hbd : IsCompact Kset := by
    refine (isCompact_closedBall (0 : Vec d) r).of_isClosed_subset hKc fun w hw => ?_
    have h1 : euclideanNorm (w - 0) < r := hKsub hw
    rw [sub_zero] at h1
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_euclideanNorm' w).trans h1.le
  exact HasCompactSupport.intro hbd fun w hw => by
    by_contra hc
    exact hw (hsupp hc)

/-- A function vanishing on `{|y|² > 1/4}` has all derivatives vanishing there. -/
theorem iterDeriv_eq_zero_of_vanish {g : Vec d → ℝ} (hg0 : ∀ y, 1 / 4 < euclideanSq y → g y = 0)
    {j : ℕ} (α : Fin j → Fin d) {y : Vec d} (hy : 1 / 4 < euclideanSq y) : iterDeriv α g y = 0 := by
  refine iterDeriv_eq_zero_of_notMem_tsupport α fun h => ?_
  have hc : IsClosed {y : Vec d | euclideanSq y ≤ 1 / 4} :=
    isClosed_le contDiff_euclideanSq.continuous continuous_const
  have hs : Function.support g ⊆ {y : Vec d | euclideanSq y ≤ 1 / 4} := fun y hy' => by
    by_contra hc'
    exact hy' (hg0 y (not_le.mp hc'))
  have := closure_minimal hs hc h
  exact absurd this (not_le.mpr hy)

theorem coordinateDerivative_coordinateDerivative_eq_zero_of_vanish {g : Vec d → ℝ}
    (hg0 : ∀ y, 1 / 4 < euclideanSq y → g y = 0) (i l : Fin d) {y : Vec d}
    (hy : 1 / 4 < euclideanSq y) : coordinateDerivative l (coordinateDerivative i g) y = 0 := by
  have h := iterDeriv_eq_zero_of_vanish hg0
    (Fin.cons i (Fin.cons l Fin.elim0 : Fin 1 → Fin d) : Fin 2 → Fin d) hy
  rwa [iterDeriv_cons, iterDeriv_cons, iterDeriv_zero] at h

/-- **A compact profile pair** for the matrix `D`: smooth `ρ ≥ 0` and `χ` vanishing for
`|y|² > 1/4`, with `∫ ρ = 1` and the scale identity `∑ᵢⱼ (Dₛ)ᵢⱼ ∂ᵢ∂ⱼχ = d ρ + y · ∇ρ` for the
symmetric part `Dₛ`. -/
structure CompactProfilePair (D : Mat d) (ρ χ : Vec d → ℝ) : Prop where
  smooth_rho : ContDiff ℝ ∞ ρ
  smooth_chi : ContDiff ℝ ∞ χ
  vanish_rho : ∀ y, 1 / 4 < euclideanSq y → ρ y = 0
  vanish_chi : ∀ y, 1 / 4 < euclideanSq y → χ y = 0
  nonneg : ∀ y, 0 ≤ ρ y
  integral_eq_one : ∫ y, ρ y = 1
  scale : ScaleIdentity (symmPart' D) d ρ χ

variable {Λ μ C₁ R₀ : ℝ} {a : CoefficientField d Λ} {D : Mat d} {ρ χ : Vec d → ℝ}

theorem CompactProfilePair.hasCompactSupport_rho (P : CompactProfilePair D ρ χ) :
    HasCompactSupport ρ :=
  HasCompactSupport.intro (isCompact_euclideanSq_le (1 / 4)) fun y hy =>
    P.vanish_rho y (not_le.mp hy)

theorem CompactProfilePair.hasCompactSupport_chi (P : CompactProfilePair D ρ χ) :
    HasCompactSupport χ :=
  HasCompactSupport.intro (isCompact_euclideanSq_le (1 / 4)) fun y hy =>
    P.vanish_chi y (not_le.mp hy)

theorem CompactProfilePair.scale_iterDeriv (P : CompactProfilePair D ρ χ) {j : ℕ}
    (α : Fin j → Fin d) :
    ScaleIdentity (symmPart' D) (d + j) (iterDeriv α ρ) (iterDeriv α χ) :=
  P.scale.iterDeriv P.smooth_rho P.smooth_chi α

theorem CompactProfilePair.iterDeriv_chi_vanish (P : CompactProfilePair D ρ χ) {j : ℕ}
    (α : Fin j → Fin d) : ∀ y, 1 / 4 < euclideanSq y → iterDeriv α χ y = 0 :=
  fun _ hy => iterDeriv_eq_zero_of_vanish P.vanish_chi α hy

theorem CompactProfilePair.iterDeriv_rho_vanish (P : CompactProfilePair D ρ χ) {j : ℕ}
    (α : Fin j → Fin d) : ∀ y, 1 / 4 < euclideanSq y → iterDeriv α ρ y = 0 :=
  fun _ hy => iterDeriv_eq_zero_of_vanish P.vanish_rho α hy

/-- **The pairing with the Euler operator of a profile derivative** is bounded through the tensor
identity: it equals `b²` times the pairing of `u` with the second derivatives of the reflected
partner `ψ(w) = ∂^αχ((x - w)/b)`. -/
theorem abs_kernelPairing_eulerOp_le (F : SublinearCorrectorFamily a D μ C₁ R₀) (hΛ : 1 ≤ Λ)
    (hC₁ : 0 ≤ C₁) (P : CompactProfilePair D ρ χ) {j : ℕ}
    (α : Fin j → Fin d) {S₂ : ℝ} (hS₂0 : 0 ≤ S₂)
    (hS₂ : ∀ i l y, |coordinateDerivative l (coordinateDerivative i (iterDeriv α χ)) y| ≤ S₂)
    {T r b : ℝ} (hb : 0 < b) (hr0 : 0 < r) (hR₀r : R₀ ≤ r) (hrT : r ≤ T) {x : Vec d}
    (hx : euclideanNorm x + b / 2 < r) (u : LocalHarmonic a 0 T) :
    |kernelPairing (fun z => eulerOp (d + j) (iterDeriv α ρ) (b⁻¹ • z))
        ((ball 0 T).indicator u.potential) x| ≤
      S₂ * ((d ^ 3 + d ^ 2 * Real.sqrt d * Λ) *
        (Real.sqrt (volume.real (ball (0 : Vec d) r)) * (C₁ * r ^ (1 - μ))) *
        Real.sqrt (∫ x in ball 0 r, euclideanSq (u.grad x))) := by
  set g := iterDeriv α χ with hgdef
  set f := iterDeriv α ρ with hfdef
  have hg : ContDiff ℝ ∞ g := contDiff_iterDeriv α P.smooth_chi
  have hg0 := P.iterDeriv_chi_vanish α
  set ψ := reflectedTest g b x with hψdef
  have hψ : IsSpatialTest (ball 0 r) ψ := isSpatialTest_reflectedTest hg hg0 hb hx
  have hSψ : ∀ i l w, |coordinateDerivative l (coordinateDerivative i ψ) w| ≤ (b⁻¹) ^ 2 * S₂ :=
    fun i l w => by
      rw [coordinateDerivative_coordinateDerivative_reflectedTest hg, abs_mul,
        abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hS₂ i l _) (by positivity)
  have hbound := F.abs_setIntegral_mul_secondOrder_le hΛ hC₁ hr0 hR₀r hrT u hψ (by positivity) hSψ
  have hsi := P.scale_iterDeriv α
  -- the kernel at `x - w` through the second derivatives of `ψ`
  have hkey : ∀ w, eulerOp (d + j) f (b⁻¹ • (x - w)) = b ^ 2 * ∑ i, ∑ l,
      D.mulVec (unitVector i) l * coordinateDerivative l (coordinateDerivative i ψ) w := by
    intro w
    set y := b⁻¹ • (x - w) with hy
    have hsym : ∀ i l, coordinateDerivative l (coordinateDerivative i g) y =
        coordinateDerivative i (coordinateDerivative l g) y := fun i l =>
      coordinateDerivative_comm_of_contDiff_two (hg.of_le (by simp)) l i y
    simp only [hψdef, coordinateDerivative_coordinateDerivative_reflectedTest hg, ← hy]
    rw [← hsi y]
    have e1 := sum_symmPart_mul_eq D (H := fun i l => coordinateDerivative l
      (coordinateDerivative i g) y) fun i l => hsym i l
    have e2 : ∑ i, ∑ l, D.mulVec (unitVector i) l * ((b⁻¹) ^ 2 *
        coordinateDerivative l (coordinateDerivative i g) y) = (b⁻¹) ^ 2 * ∑ i, ∑ l,
          D.mulVec (unitVector i) l * coordinateDerivative l (coordinateDerivative i g) y := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [e2, ← e1]
    have e3 : ∑ i, ∑ l, symmPart' D i l * coordinateDerivative i (coordinateDerivative l g) y =
        ∑ i, ∑ l, ((1 / 2 : ℝ) • (D + D.transpose)) i l *
          coordinateDerivative l (coordinateDerivative i g) y := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
      rw [symmPart', hsym i l]
    rw [e3]
    field_simp
  -- restriction of the pairing to `B_r`
  have hBT : ball (0 : Vec d) r ⊆ ball 0 T := fun w hw => lt_of_lt_of_le hw hrT
  have hpair : kernelPairing (fun z => eulerOp (d + j) f (b⁻¹ • z))
      ((ball 0 T).indicator u.potential) x = b ^ 2 * ∫ w in ball 0 r, u.potential w *
        ∑ i, ∑ l, D.mulVec (unitVector i) l * coordinateDerivative l (coordinateDerivative i ψ) w := by
    unfold kernelPairing
    rw [← integral_const_mul]
    have hout : ∀ w ∉ ball (0 : Vec d) r, ∑ i, ∑ l, D.mulVec (unitVector i) l *
        coordinateDerivative l (coordinateDerivative i ψ) w = 0 := by
      intro w hw
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun l _ => ?_
      have hw' : w ∉ tsupport ψ := fun h => hw (hψ.2.2 h)
      have : coordinateDerivative l (coordinateDerivative i ψ) w = 0 :=
        coordinateDerivative_eq_zero_of_notMem_tsupport
          (fun h => hw' (tsupport_coordinateDerivative_subset' i ψ h)) l
      rw [this, mul_zero]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ball (0 : Vec d) r) fun w hw => by
      show (ball 0 T).indicator u.potential w * eulerOp (d + j) f (b⁻¹ • (x - w)) = 0
      rw [hkey w, hout w hw, mul_zero, mul_zero]]
    refine setIntegral_congr_fun (measurableSet_ball _ _) fun w hw => ?_
    simp only
    rw [Set.indicator_of_mem (hBT hw), hkey w]
    ring
  rw [hpair, abs_mul, abs_of_nonneg (sq_nonneg b)]
  calc b ^ 2 * |∫ w in ball 0 r, u.potential w * ∑ i, ∑ l, D.mulVec (unitVector i) l *
        coordinateDerivative l (coordinateDerivative i ψ) w|
      ≤ b ^ 2 * ((b⁻¹) ^ 2 * S₂ * ((d ^ 3 + d ^ 2 * Real.sqrt d * Λ) *
        (Real.sqrt (volume.real (ball (0 : Vec d) r)) * (C₁ * r ^ (1 - μ))) *
        Real.sqrt (∫ x in ball 0 r, euclideanSq (u.grad x)))) :=
        mul_le_mul_of_nonneg_left hbound (sq_nonneg b)
    _ = _ := by field_simp

end QSH
