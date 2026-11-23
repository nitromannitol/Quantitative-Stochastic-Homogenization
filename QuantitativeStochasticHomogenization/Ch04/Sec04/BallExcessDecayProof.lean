import QuantitativeStochasticHomogenization.Ch04.Sec04.HighContrastBallExcess
import QuantitativeStochasticHomogenization.Ch04.Sec04.TranslatedCorrectorBounds
import QuantitativeStochasticHomogenization.Ch04.Sec05.CubeDecomposition
import HCPoly.Provider.PolynomialHomogenization.Root.Corrector.HomotheticEllipsoidVolume

/-!
# Proof of the excess decay of one slope on balls

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.21: `BallExcessDecay`, the excess decay of one slope on the balls `B_t(z)`, from
Theorem C of Armstrong, Kuusi and Loher (`exists_highContrastExcessPackage`) and the corrector
bounds of Lemma 3.17 at the center `z` (`exists_translated_corrector_bounds`).

`HighContrastExcessPackage.ball_excess` is the deterministic transfer for one coefficient: the
solution `u(x) = v(2x + y)/2` on the ellipsoid `E_R`, the excess decay of the package, the
comparison of weighted norms with normalized `L²` norms and the changes of variables
`∫_{A⁻¹ S} F ∘ A = 2^{-d} ∫_S F`, `A x = 2x + y`, with `B_t(z) ⊆ A(E_{t/2 + d})` and
`A(E_R) ⊆ B_{(2Λ + 4)R}(z)`. The slope is bounded by the Gram lower bound
`c_d |e|² |B_R| ≤ ∫_{B_R(z)} |∑_j e_j W_j|²` above the radius of Lemma 3.17.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

open _root_.Homogenization hiding euclideanBall Vec Mat

open _root_.Homogenization.HighContrast

variable {d : ℕ}

theorem norm_two_smul_add_sub_le (x y z : Vec d) :
    euclideanNorm ((2 : ℝ) • x + y - z) ≤ 2 * euclideanNorm x + euclideanNorm (y - z) := by
  have h1 := euclideanNorm_add_le_add ((2 : ℝ) • x) (y - z)
  have h2 : euclideanNorm ((2 : ℝ) • x) = 2 * euclideanNorm x := by
    rw [euclideanNorm_smul_abs, abs_of_pos two_pos]
  rw [show (2 : ℝ) • x + y - z = (2 : ℝ) • x + (y - z) by abel]
  linarith

theorem two_mul_norm_le (x y z : Vec d) :
    2 * euclideanNorm x ≤ euclideanNorm ((2 : ℝ) • x + y - z) + euclideanNorm (z - y) := by
  have h1 := euclideanNorm_add_le_add ((2 : ℝ) • x + y - z) (z - y)
  have h2 : euclideanNorm ((2 : ℝ) • x) = 2 * euclideanNorm x := by
    rw [euclideanNorm_smul_abs, abs_of_pos two_pos]
  rw [show (2 : ℝ) • x + y - z + (z - y) = (2 : ℝ) • x by abel, h2] at h1
  exact h1

/-- **The excess decay of one slope on balls, for one coefficient.** -/
theorem HighContrastExcessPackage.ball_excess {K : ℝ} (hK : 1 ≤ K)
    {P : Measure (CoefficientField d K)} {κ C : ℝ} {C₁ : ℝ → ℝ}
    (pk : HighContrastExcessPackage hK P κ C C₁) (hκ : 0 < κ) (hC : 0 ≤ C) [NeZero d]
    {b' : CoeffSpace d} (hb' : b' ∈ pk.Ωend) (a : CoefficientField d K) {y z : Vec d}
    (hzy : euclideanNorm (z - y) ≤ 2 * d)
    (hcoef : ∀ᵐ x ∂volume, b'.1 x = a.field ((2 : ℝ) • x + y))
    {W : Fin d → Vec d → Vec d}
    (hW : ∀ e : Vec d, (fun x => e + pk.gradPhi e b' x) =ᵐ[volume]
      fun x => ∑ j, e j • W j ((2 : ℝ) • x + y))
    (hWloc : ∀ j k (R : ℝ), MemLp (fun x => W j x k) 2 (volume.restrict (ball z R)))
    {R : ℝ} (hXR : pk.X b' ≤ R) (hdR : 2 * d ≤ R)
    {v : Vec d → ℝ} {g : Vec d → Vec d}
    (hv : MemLp v 2 (volume.restrict (ball z ((2 * K + 4) * R))))
    (hg : ∀ k, MemLp (fun x => g x k) 2 (volume.restrict (ball z ((2 * K + 4) * R))))
    (hw : HasWeakGradient (ball z ((2 * K + 4) * R)) v g)
    (hdiv : HasWeakDivergence (ball z ((2 * K + 4) * R)) (fun x => (a x).mulVec (g x))
      (fun _ => 0))
    {ϑ : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hC₁ : 0 ≤ C₁ ϑ) :
    ∃ e : Vec d,
      (∀ t : ℝ, 2 * pk.X b' ≤ t → 2 * d ≤ t → t ≤ R →
        ∫ x in ball z t, euclideanSq (g x - ∑ j, e j • W j x) ≤
          C₁ ϑ ^ 2 * K * (t / R) ^ (2 * ϑ) * (t / R) ^ d *
            ∫ x in ball z ((2 * K + 4) * R), euclideanSq (g x)) ∧
      ∫ x in ball z R, euclideanSq (g x - ∑ j, e j • W j x) ≤
        C₁ ϑ ^ 2 * K * ∫ x in ball z ((2 * K + 4) * R), euclideanSq (g x) := by
  have hK0 : 0 ≤ K := by linarith
  have hX1 := pk.one_le_X b'
  have hR0 : 0 < R := lt_of_lt_of_le one_pos (hX1.trans hXR)
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hbell : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 K (b'.1 x) := by
    filter_upwards [hcoef] with x hx
    rw [hx]
    exact coefficientField_isEllipticMatrix a hK le_rfl _
  have hB1 := fun e =>
    pk.toHighContrastCorrectorPackage.vecNormSq_le_vecDot_symmPart_and_le hκ hC hb' hbell e
  have hS : (symmPart pk.abar).PosDef := posDef_symmPart_of_vecDot_pos pk.posDef
  set U := ball z ((2 * K + 4) * R) with hUdef
  have hUm : MeasurableSet U := measurableSet_ball z _
  set r' : ℝ := (K + 1) * R with hr'def
  have hr' : 0 < r' := mul_pos (by linarith) hR0
  have hEU' : ∀ ρ, 0 ≤ ρ → ρ ≤ R → ellipsoid pk.abar ρ ⊆ euclideanBallAt (0 : Vec d) r' := by
    intro ρ hρ0 hρR x hx
    have h1 := vecNormSq_le_of_mem_ellipsoid_of_bounds pk.posDef hB1 hx
    show vecNormSq (x - 0) < r' ^ 2
    rw [sub_zero]
    have : K ^ 2 * ρ ^ 2 < r' ^ 2 := by
      rw [hr'def]
      have h2 : ρ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hρ0 hρR 2
      calc K ^ 2 * ρ ^ 2 ≤ K ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg K)
        _ < ((K + 1) * R) ^ 2 := by nlinarith [sq_pos_of_pos hR0]
    linarith
  have hU'U : ∀ x ∈ euclideanBallAt (0 : Vec d) r', (2 : ℝ) • x + y ∈ U := by
    intro x hx
    have hx' : euclideanNorm x < r' := by
      refine euclideanNorm_lt_of_vecNormSq_lt hr'.le ?_
      have : vecNormSq (x - 0) < r' ^ 2 := hx
      rwa [sub_zero] at this
    show euclideanNorm ((2 : ℝ) • x + y - z) < (2 * K + 4) * R
    have h1 := norm_two_smul_add_sub_le x y z
    have h2 : euclideanNorm (y - z) = euclideanNorm (z - y) := euclideanNorm_sub_comm' y z
    nlinarith
  have hEU : ∀ ρ, 0 ≤ ρ → ρ ≤ R → ∀ x ∈ ellipsoid pk.abar ρ, (2 : ℝ) • x + y ∈ U :=
    fun ρ hρ0 hρR x hx => hU'U x (hEU' ρ hρ0 hρR hx)
  have hmem := memH1a_comp_two_smul_add hK a hUm hr'
    (hEU' R hR0.le le_rfl) y hU'U hv hg hw (b := fun x => b'.1 x) hcoef
  have hsol := isWeakSolutionOn_comp_smul_add a two_pos y (hEU R hR0.le le_rfl) hdiv
    (b := fun x => b'.1 x) hcoef
  obtain ⟨e, he⟩ := pk.excess b' hb' R hXR _ _ hmem hsol ϑ ⟨hϑ0, hϑ1⟩
  refine ⟨e, ?_⟩
  -- the integrands
  set G : Vec d → ℝ := fun x => euclideanSq (g x - ∑ j, e j • W j x) with hGdef
  set Gg : Vec d → ℝ := fun x => euclideanSq (g x) with hGgdef
  have hG0 : ∀ x, 0 ≤ G x := fun x => zero_le_euclideanSq _
  have hGg0 : ∀ x, 0 ≤ Gg x := fun x => zero_le_euclideanSq _
  have hGU : ∀ k, MemLp (fun x => (g x - ∑ j, e j • W j x) k) 2 (volume.restrict U) := by
    intro k
    have h1 : MemLp (fun x => ∑ j, e j * W j x k) 2 (volume.restrict U) :=
      memLp_finsetSum _ fun j _ => (hWloc j k _).const_mul (e j)
    refine ((hg k).sub h1).ae_eq (Eventually.of_forall fun x => ?_)
    simp [Finset.sum_apply, smul_eq_mul]
  have hGA : ∀ V : Set (Vec d), MeasurableSet V → (∀ x ∈ V, (2 : ℝ) • x + y ∈ U) →
      IntegrableOn (fun x => G ((2 : ℝ) • x + y)) V := fun V hV hVU =>
    integrableOn_euclideanSq_of_memLp fun k =>
      MemLp.comp_smul_add_restrict hUm hV two_ne_zero y hVU (hGU k)
  have hGgA : ∀ V : Set (Vec d), MeasurableSet V → (∀ x ∈ V, (2 : ℝ) • x + y ∈ U) →
      IntegrableOn (fun x => Gg ((2 : ℝ) • x + y)) V := fun V hV hVU =>
    integrableOn_euclideanSq_of_memLp fun k =>
      MemLp.comp_smul_add_restrict hUm hV two_ne_zero y hVU (hg k)
  -- the weighted excess in integral form on `E_ρ`
  have hsymm : ∀ᵐ x ∂(volume : Measure (Vec d)),
      symmPart (b'.1 x) = a.field ((2 : ℝ) • x + y) := by
    filter_upwards [hcoef] with x hx
    rw [hx]
    exact symmPart_eq_of_transpose_eq (a.symmetric _)
  have key : ∀ ρ, pk.X b' ≤ ρ → ρ ≤ R →
      ∫ x in ellipsoid pk.abar ρ, G ((2 : ℝ) • x + y) ≤
        (C₁ ϑ * (ρ / R) ^ ϑ) ^ 2 * K * (ρ / R) ^ d *
          ∫ x in ellipsoid pk.abar R, Gg ((2 : ℝ) • x + y) := by
    intro ρ hXρ hρR
    have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos (hX1.trans hXρ)
    have hEm := measurableSet_ellipsoid pk.abar ρ
    have hERm := measurableSet_ellipsoid pk.abar R
    have hF₁ : (fun x => euclideanSq (g ((2 : ℝ) • x + y) - (e + pk.gradPhi e b' x)))
        =ᵐ[volume] fun x => G ((2 : ℝ) • x + y) := by
      filter_upwards [hW e] with x hx
      simp only [hGdef, hx]
    have hint₁ : IntegrableOn
        (fun x => euclideanSq (g ((2 : ℝ) • x + y) - (e + pk.gradPhi e b' x)))
        (ellipsoid pk.abar ρ) :=
      (hGA _ hEm (hEU ρ hρ0.le hρR)).congr_fun_ae (ae_restrict_of_ae hF₁.symm)
    have hint₂ : IntegrableOn (fun x => euclideanSq (g ((2 : ℝ) • x + y)))
        (ellipsoid pk.abar R) := hGgA _ hERm (hEU R hR0.le le_rfl)
    have hlow : ∀ᵐ x ∂volume.restrict (ellipsoid pk.abar ρ),
        euclideanSq (g ((2 : ℝ) • x + y) - (e + pk.gradPhi e b' x)) ≤
          vecDot (g ((2 : ℝ) • x + y) - (e + pk.gradPhi e b' x))
            (matVecMul (symmPart (b'.1 x)) (g ((2 : ℝ) • x + y) - (e + pk.gradPhi e b' x))) := by
      refine ae_restrict_of_ae ?_
      filter_upwards [hsymm] with x hx
      rw [hx]
      exact (a.elliptic _ _).1
    have hup : ∀ᵐ x ∂volume.restrict (ellipsoid pk.abar R),
        vecDot (g ((2 : ℝ) • x + y)) (matVecMul (symmPart (b'.1 x)) (g ((2 : ℝ) • x + y))) ≤
          K * euclideanSq (g ((2 : ℝ) • x + y)) := by
      refine ae_restrict_of_ae ?_
      filter_upwards [hsymm] with x hx
      rw [hx]
      exact (a.elliptic _ _).2
    have hc : 0 ≤ C₁ ϑ * (ρ / R) ^ ϑ :=
      mul_nonneg hC₁ (Real.rpow_nonneg (div_nonneg hρ0.le hR0.le) _)
    have hmain := integral_sq_mul_le_of_weightedGradNorm_le hc hK0
      (volume_ellipsoid_pos pk.abar hρ0).ne' (volume_ellipsoid_lt_top hS ρ).ne
      (volume_ellipsoid_pos pk.abar hR0).ne' (volume_ellipsoid_lt_top hS R).ne
      hint₁ hint₂ hlow hup (he ρ ⟨hXρ, hρR⟩)
    rw [integral_congr_ae (ae_restrict_of_ae hF₁)] at hmain
    have hvol : volume.real (ellipsoid pk.abar ρ) =
        (ρ / R) ^ d * volume.real (ellipsoid pk.abar R) := by
      have h1 := Root.volume_ellipsoid_mul pk.abar (div_pos hρ0 hR0) R
      rw [div_mul_cancel₀ ρ hR0.ne'] at h1
      rw [measureReal_def, h1, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (pow_nonneg (div_nonneg hρ0.le hR0.le) d), measureReal_def]
    rw [hvol] at hmain
    have hVR : 0 < volume.real (ellipsoid pk.abar R) :=
      ENNReal.toReal_pos (volume_ellipsoid_pos pk.abar hR0).ne'
        (volume_ellipsoid_lt_top hS R).ne
    have h2 : (∫ x in ellipsoid pk.abar ρ, G ((2 : ℝ) • x + y)) *
        volume.real (ellipsoid pk.abar R) ≤
        ((C₁ ϑ * (ρ / R) ^ ϑ) ^ 2 * K * (ρ / R) ^ d *
          ∫ x in ellipsoid pk.abar R, Gg ((2 : ℝ) • x + y)) *
            volume.real (ellipsoid pk.abar R) := by
      refine hmain.trans (le_of_eq ?_)
      simp only [hGgdef]
      ring
    exact le_of_mul_le_mul_right h2 hVR
  -- transfer to balls
  have hin : ∀ S : Set (Vec d), MeasurableSet S → ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ R →
      (∀ x, (2 : ℝ) • x + y ∈ S → x ∈ ellipsoid pk.abar ρ) →
      ∫ x in S, G x ≤ 2 ^ d * ∫ x in ellipsoid pk.abar ρ, G ((2 : ℝ) • x + y) := by
    intro S hS ρ hρ0 hρR hSE
    have h1 := setIntegral_preimage_two_smul_add hS G y
    have h2 : ∫ x in (fun x => (2 : ℝ) • x + y) ⁻¹' S, G ((2 : ℝ) • x + y) ≤
        ∫ x in ellipsoid pk.abar ρ, G ((2 : ℝ) • x + y) :=
      setIntegral_mono_set (hGA _ (measurableSet_ellipsoid _ _) (hEU ρ hρ0 hρR))
        (Eventually.of_forall fun x => hG0 _)
        (Eventually.of_forall fun x hx => hSE x hx)
    have h2d : (0 : ℝ) < 2 ^ d := by positivity
    calc ∫ x in S, G x = 2 ^ d * ∫ x in (fun x => (2 : ℝ) • x + y) ⁻¹' S,
          G ((2 : ℝ) • x + y) := by rw [h1]; field_simp
      _ ≤ 2 ^ d * ∫ x in ellipsoid pk.abar ρ, G ((2 : ℝ) • x + y) :=
          mul_le_mul_of_nonneg_left h2 h2d.le
  have hout : ∫ x in ellipsoid pk.abar R, Gg ((2 : ℝ) • x + y) ≤
      (2 ^ d)⁻¹ * ∫ x in U, Gg x := by
    rw [← setIntegral_preimage_two_smul_add hUm Gg y]
    exact setIntegral_mono_set (hGgA _ (hUm.preimage (measurable_two_smul_add y))
        (fun x hx => hx)) (Eventually.of_forall fun x => hGg0 _)
      (Eventually.of_forall fun x hx => hEU R hR0.le le_rfl x hx)
  have hIg : 0 ≤ ∫ x in U, Gg x := setIntegral_nonneg hUm fun x _ => hGg0 x
  have hball : ∀ ρ : ℝ, 0 < ρ → ∀ t : ℝ, t + 2 * d ≤ 2 * ρ →
      ∀ x, (2 : ℝ) • x + y ∈ ball z t → x ∈ ellipsoid pk.abar ρ := by
    intro ρ hρ t ht x hx
    apply euclideanBallAt_zero_subset_ellipsoid
    show vecNormSq (x - 0) < ρ ^ 2
    rw [sub_zero]
    refine vecNormSq_lt_of_euclideanNorm_lt ?_
    have h1 := two_mul_norm_le x y z
    have h2 : euclideanNorm ((2 : ℝ) • x + y - z) < t := hx
    linarith
  refine ⟨fun t ht1 ht2 ht3 => ?_, ?_⟩
  · set ρ := t / 2 + d with hρdef
    have hXρ : pk.X b' ≤ ρ := by rw [hρdef]; linarith
    have hρR : ρ ≤ R := by rw [hρdef]; linarith
    have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos (hX1.trans hXρ)
    have hρt : ρ ≤ t := by rw [hρdef]; linarith
    have h1 := hin (ball z t) (measurableSet_ball z t) ρ hρ0.le hρR
      (hball ρ hρ0 t (by rw [hρdef]; linarith))
    have h2 := key ρ hXρ hρR
    have hq0 : 0 ≤ ρ / R := div_nonneg hρ0.le hR0.le
    have hqt : ρ / R ≤ t / R := div_le_div_of_nonneg_right hρt hR0.le
    have hsq : (C₁ ϑ * (ρ / R) ^ ϑ) ^ 2 = C₁ ϑ ^ 2 * (ρ / R) ^ (2 * ϑ) := by
      rw [mul_pow, ← Real.rpow_natCast ((ρ / R) ^ ϑ), ← Real.rpow_mul hq0]
      congr 2
      push_cast
      ring
    have hmono : (ρ / R) ^ (2 * ϑ) * (ρ / R) ^ d ≤ (t / R) ^ (2 * ϑ) * (t / R) ^ d :=
      mul_le_mul (Real.rpow_le_rpow hq0 hqt (by linarith)) (pow_le_pow_left₀ hq0 hqt d)
        (pow_nonneg hq0 d) (Real.rpow_nonneg (hq0.trans hqt) _)
    have hIE : 0 ≤ ∫ x in ellipsoid pk.abar R, Gg ((2 : ℝ) • x + y) :=
      setIntegral_nonneg (measurableSet_ellipsoid _ _) fun x _ => hGg0 _
    calc ∫ x in ball z t, G x ≤ 2 ^ d * ∫ x in ellipsoid pk.abar ρ, G ((2 : ℝ) • x + y) := h1
      _ ≤ 2 ^ d * ((C₁ ϑ * (ρ / R) ^ ϑ) ^ 2 * K * (ρ / R) ^ d *
            ∫ x in ellipsoid pk.abar R, Gg ((2 : ℝ) • x + y)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = C₁ ϑ ^ 2 * K * ((ρ / R) ^ (2 * ϑ) * (ρ / R) ^ d) *
            (2 ^ d * ∫ x in ellipsoid pk.abar R, Gg ((2 : ℝ) • x + y)) := by
          rw [hsq]; ring
      _ ≤ C₁ ϑ ^ 2 * K * ((t / R) ^ (2 * ϑ) * (t / R) ^ d) * ∫ x in U, Gg x := by
          have h3 : 2 ^ d * ∫ x in ellipsoid pk.abar R, Gg ((2 : ℝ) • x + y) ≤
              ∫ x in U, Gg x := by
            have h2d : (0 : ℝ) < 2 ^ d := by positivity
            calc 2 ^ d * ∫ x in ellipsoid pk.abar R, Gg ((2 : ℝ) • x + y)
                ≤ 2 ^ d * ((2 ^ d)⁻¹ * ∫ x in U, Gg x) := mul_le_mul_of_nonneg_left hout h2d.le
              _ = ∫ x in U, Gg x := by field_simp
          have hc0 : 0 ≤ C₁ ϑ ^ 2 * K := mul_nonneg (sq_nonneg _) hK0
          calc C₁ ϑ ^ 2 * K * ((ρ / R) ^ (2 * ϑ) * (ρ / R) ^ d) *
                (2 ^ d * ∫ x in ellipsoid pk.abar R, Gg ((2 : ℝ) • x + y))
              ≤ C₁ ϑ ^ 2 * K * ((t / R) ^ (2 * ϑ) * (t / R) ^ d) *
                (2 ^ d * ∫ x in ellipsoid pk.abar R, Gg ((2 : ℝ) • x + y)) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hc0)
                  (mul_nonneg (by positivity) hIE)
            _ ≤ C₁ ϑ ^ 2 * K * ((t / R) ^ (2 * ϑ) * (t / R) ^ d) * ∫ x in U, Gg x :=
                mul_le_mul_of_nonneg_left h3 (mul_nonneg hc0 (mul_nonneg
                  (Real.rpow_nonneg (hq0.trans hqt) _) (pow_nonneg (hq0.trans hqt) d)))
      _ = C₁ ϑ ^ 2 * K * (t / R) ^ (2 * ϑ) * (t / R) ^ d * ∫ x in U, Gg x := by ring
  · have h1 := hin (ball z R) (measurableSet_ball z R) R hR0.le le_rfl
      (hball R hR0 R (by linarith))
    have h2 := key R hXR le_rfl
    simp only [div_self hR0.ne', Real.one_rpow, mul_one, one_pow] at h2
    have h2d : (0 : ℝ) < 2 ^ d := by positivity
    calc ∫ x in ball z R, G x ≤ 2 ^ d * ∫ x in ellipsoid pk.abar R, G ((2 : ℝ) • x + y) := h1
      _ ≤ 2 ^ d * (C₁ ϑ ^ 2 * K * ∫ x in ellipsoid pk.abar R, Gg ((2 : ℝ) • x + y)) :=
          mul_le_mul_of_nonneg_left h2 h2d.le
      _ ≤ 2 ^ d * (C₁ ϑ ^ 2 * K * ((2 ^ d)⁻¹ * ∫ x in U, Gg x)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hout
            (mul_nonneg (sq_nonneg _) hK0)) h2d.le
      _ = C₁ ϑ ^ 2 * K * ∫ x in U, Gg x := by field_simp

/-- The Gram constant of `gram_lower_bound_of_sublinear`. -/
def ballGramConstant (d : ℕ) : ℝ := (1 / 4 : ℝ) ^ d / (16 * (2 ^ d * 2) ^ 2)

theorem ballGramConstant_pos (d : ℕ) : 0 < ballGramConstant d := by
  unfold ballGramConstant; positivity

/-- **The slope from the Gram lower bound**: above the radius of Lemma 3.17 the corrected
gradients satisfy `c_d |e|² |B_R| ≤ ∫_{B_R(z)} |∑_j e_j W_j|²`, so an excess bound
`∫_{B_R(z)} |g - ∑_j e_j W_j|² ≤ c₁ ∫_{B_{LR}(z)} |g|²` bounds `|e|`. -/
theorem euclideanSq_slope_mul_le_of_gram {Λ : ℝ} {P : Measure (CoefficientField d Λ)}
    (S : HomogenizationData P) (a : CoefficientField d Λ) {z : Vec d} {R L CE β' c₁ : ℝ}
    (hR0 : 0 < R) (hL1 : 1 ≤ L)
    (hwg : ∀ i : Fin d, HasWeakGradient Set.univ ((S.corrector (unitVector i)).potential a)
      ((S.corrector (unitVector i)).grad a))
    (hloc : ∀ i : Fin d, ∀ R : ℝ, 0 < R →
      MemLp ((S.corrector (unitVector i)).potential a) 2 (volume.restrict (ball 0 R)) ∧
      MemLp ((S.corrector (unitVector i)).grad a) 2 (volume.restrict (ball 0 R)))
    (harm : ∀ i : Fin d, HasWeakDivergence Set.univ
      (fun x => (a x).mulVec (unitVector i + (S.corrector (unitVector i)).grad a x)) (fun _ => 0))
    (hosc : ∀ i : Fin d, ∃ c : ℝ, ∫ x in ball z R,
      ((S.corrector (unitVector i)).potential a x - c) ^ 2 ≤
        2 ^ d * (CE * (2 * R) ^ (1 - β')) ^ 2 * volume.real (ball z R))
    (hε : (d : ℝ) * (2 * Real.sqrt (2 ^ d) * CE * (2 * R) ^ (-β')) ^ 2 ≤ (1 / 4 : ℝ) ^ d / 16)
    {g : Vec d → Vec d} (hg : ∀ k, MemLp (fun x => g x k) 2 (volume.restrict (ball z (L * R))))
    (hWloc : ∀ j k (R' : ℝ), MemLp (fun x => correctorColumn S a j x k) 2
      (volume.restrict (ball z R')))
    (e : Vec d)
    (htop : ∫ x in ball z R, euclideanSq (g x - ∑ j, e j • correctorColumn S a j x) ≤
      c₁ * ∫ x in ball z (L * R), euclideanSq (g x)) :
    euclideanSq e * volume.real (ball z (L * R)) ≤
      L ^ d * (2 * (1 + c₁)) / ballGramConstant d * ∫ x in ball z (L * R), euclideanSq (g x) := by
  have hL0 : 0 < L := by linarith
  have hBLR : volume.real (ball z (L * R)) = L ^ d * volume.real (ball z R) := by
    rw [volume_real_ball_eq_mul z (mul_pos hL0 hR0), volume_real_ball_eq_mul z hR0, mul_pow]
    ring
  choose c hc using hosc
  set h := fun i : Fin d => localCorrectedCoordinate a z R i (c i)
    ((S.corrector (unitVector i)).potential a) ((S.corrector (unitVector i)).grad a)
    (hwg i) (hloc i) (harm i) with hhdef
  have hsub : ∀ i, ∫ x in ball z R, ((h i).potential x - (x - z) i - 0) ^ 2 ≤
      (2 * Real.sqrt (2 ^ d) * CE * (2 * R) ^ (-β')) ^ 2 * R ^ 2 * volume.real (ball z R) := by
    intro i
    rw [sq_two_sqrt_mul_rpow_neg hR0]
    refine le_of_eq_of_le (integral_congr_ae (Eventually.of_forall fun x => ?_)) (hc i)
    simp only [hhdef, localCorrectedCoordinate_potential]
    ring
  have hgram := gram_lower_bound_of_sublinear hR0 (fun i => (h i).potential)
    (fun i => (h i).grad) (fun i => (h i).square_integrable) (fun i j => (h i).memLp_grad j)
    (fun i => (h i).weak_gradient) 0 hsub hε e
  have hgradeq : ∀ i x, (h i).grad x = correctorColumn S a i x := fun i x => rfl
  simp only [hgradeq] at hgram
  have hRLR : ball z R ⊆ ball z (L * R) := fun x hx =>
    lt_of_lt_of_le hx (le_mul_of_one_le_left hR0.le hL1)
  have hgLR : IntegrableOn (fun x => euclideanSq (g x)) (ball z (L * R)) :=
    integrableOn_euclideanSq_of_memLp hg
  have hWR : ∀ k, MemLp (fun x => (∑ j, e j • correctorColumn S a j x) k) 2
      (volume.restrict (ball z R)) := by
    intro k
    have h1 : MemLp (fun x => ∑ j, e j * correctorColumn S a j x k) 2
        (volume.restrict (ball z R)) :=
      memLp_finsetSum Finset.univ fun j _ => (hWloc j k R).const_mul (e j)
    refine h1.ae_eq (Eventually.of_forall fun x => ?_)
    simp [Finset.sum_apply, smul_eq_mul]
  have hgR : ∀ k, MemLp (fun x => g x k) 2 (volume.restrict (ball z R)) := fun k =>
    (hg k).mono_measure (Measure.restrict_mono hRLR le_rfl)
  have hdiffR : ∀ k, MemLp (fun x => (g x - ∑ j, e j • correctorColumn S a j x) k) 2
      (volume.restrict (ball z R)) := fun k => ((hgR k).sub (hWR k)).ae_eq
        (Eventually.of_forall fun x => by simp)
  have hpt : ∀ x, euclideanSq (∑ j, e j • correctorColumn S a j x) ≤
      2 * euclideanSq (g x) + 2 * euclideanSq (g x - ∑ j, e j • correctorColumn S a j x) := by
    intro x
    have := euclideanSq_sub_le (g x) (g x - ∑ j, e j • correctorColumn S a j x)
    rwa [sub_sub_cancel] at this
  have hI1 : ∫ x in ball z R, euclideanSq (∑ j, e j • correctorColumn S a j x) ≤
      2 * (∫ x in ball z R, euclideanSq (g x)) +
        2 * ∫ x in ball z R, euclideanSq (g x - ∑ j, e j • correctorColumn S a j x) := by
    calc ∫ x in ball z R, euclideanSq (∑ j, e j • correctorColumn S a j x)
        ≤ ∫ x in ball z R, (2 * euclideanSq (g x) +
            2 * euclideanSq (g x - ∑ j, e j • correctorColumn S a j x)) :=
          setIntegral_mono_on (integrableOn_euclideanSq_of_memLp hWR)
            (((integrableOn_euclideanSq_of_memLp hgR).const_mul 2).add
              ((integrableOn_euclideanSq_of_memLp hdiffR).const_mul 2))
            (measurableSet_ball z R) fun x _ => hpt x
      _ = 2 * (∫ x in ball z R, euclideanSq (g x)) +
            2 * ∫ x in ball z R, euclideanSq (g x - ∑ j, e j • correctorColumn S a j x) := by
          rw [integral_add ((integrableOn_euclideanSq_of_memLp hgR).const_mul 2)
            ((integrableOn_euclideanSq_of_memLp hdiffR).const_mul 2), integral_const_mul,
            integral_const_mul]
  have hI2 : ∫ x in ball z R, euclideanSq (g x) ≤ ∫ x in ball z (L * R), euclideanSq (g x) :=
    setIntegral_mono_set hgLR (Eventually.of_forall fun x => zero_le_euclideanSq _)
      hRLR.eventuallyLE
  have hcomb : ballGramConstant d * euclideanSq e * volume.real (ball z R) ≤
      2 * (1 + c₁) * ∫ x in ball z (L * R), euclideanSq (g x) := by
    calc ballGramConstant d * euclideanSq e * volume.real (ball z R)
        ≤ 2 * (∫ x in ball z R, euclideanSq (g x)) +
            2 * ∫ x in ball z R, euclideanSq (g x - ∑ j, e j • correctorColumn S a j x) :=
          hgram.trans hI1
      _ ≤ 2 * (∫ x in ball z (L * R), euclideanSq (g x)) +
            2 * (c₁ * ∫ x in ball z (L * R), euclideanSq (g x)) := by linarith
      _ = 2 * (1 + c₁) * ∫ x in ball z (L * R), euclideanSq (g x) := by ring
  have hLd : 0 < L ^ d := pow_pos hL0 d
  rw [hBLR, div_mul_eq_mul_div, le_div_iff₀ (ballGramConstant_pos d)]
  calc euclideanSq e * (L ^ d * volume.real (ball z R)) * ballGramConstant d
      = L ^ d * (ballGramConstant d * euclideanSq e * volume.real (ball z R)) := by ring
    _ ≤ L ^ d * (2 * (1 + c₁) * ∫ x in ball z (L * R), euclideanSq (g x)) :=
        mul_le_mul_of_nonneg_left hcomb hLd.le
    _ = L ^ d * (2 * (1 + c₁)) * ∫ x in ball z (L * R), euclideanSq (g x) := by ring

/-- The zoom bound in the volume form of `BallExcessDecay`. -/
theorem zoom_mul_volume_le {z : Vec d} {L R t c J I : ℝ} (hL0 : 0 < L) (hR0 : 0 < R)
    (ht0 : 0 < t) {ϑ : ℝ}
    (h : J ≤ c * (t / R) ^ (2 * ϑ) * (t / R) ^ d * I) :
    J * volume.real (ball z (L * R)) ≤
      c * L ^ d * (t / R) ^ (2 * ϑ) * volume.real (ball z t) * I := by
  have hvol : (t / R) ^ d * volume.real (ball z (L * R)) = L ^ d * volume.real (ball z t) := by
    rw [volume_real_ball_eq_mul z (mul_pos hL0 hR0), volume_real_ball_eq_mul z ht0, div_pow,
      mul_pow]
    have hR0' := hR0.ne'
    field_simp
  have hB : 0 ≤ volume.real (ball z (L * R)) := measureReal_nonneg
  calc J * volume.real (ball z (L * R))
      ≤ (c * (t / R) ^ (2 * ϑ) * (t / R) ^ d * I) * volume.real (ball z (L * R)) :=
        mul_le_mul_of_nonneg_right h hB
    _ = c * (t / R) ^ (2 * ϑ) * I * ((t / R) ^ d * volume.real (ball z (L * R))) := by ring
    _ = c * L ^ d * (t / R) ^ (2 * ϑ) * volume.real (ball z t) * I := by rw [hvol]; ring

/-- The random radius: a multiple of the larger of the high-contrast scale at the even lattice
point and the radius of Lemma 3.17. -/
theorem exists_ballExcess_radius {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z₁ Z₂ : Ω → ℝ} {τ θ₁ θ₂ c : ℝ} (h₁ : OsBound P Z₁ τ θ₁) (h₂ : OsBound P Z₂ τ θ₂)
    (hZ₂ : ∀ ω, 1 ≤ Z₂ ω) (hc : 1 ≤ c) :
    Measurable (fun ω => c * max (Z₁ ω) (Z₂ ω)) ∧
      OsBound P (fun ω => c * max (Z₁ ω) (Z₂ ω)) τ (c * ((2 : ℝ) ^ τ⁻¹ * max θ₁ θ₂)) ∧
      (∀ ω, 1 ≤ c * max (Z₁ ω) (Z₂ ω)) ∧
      (∀ ω, c * Z₁ ω ≤ c * max (Z₁ ω) (Z₂ ω)) ∧ (∀ ω, c * Z₂ ω ≤ c * max (Z₁ ω) (Z₂ ω)) ∧
      ∀ ω, c ≤ c * max (Z₁ ω) (Z₂ ω) := by
  have hmax := (osBound_max h₁ h₂).const_mul (by linarith : (0 : ℝ) < c)
  refine ⟨hmax.1, hmax, fun ω => one_le_mul_of_one_le_of_one_le hc
    ((hZ₂ ω).trans (le_max_right _ _)), fun ω => mul_le_mul_of_nonneg_left (le_max_left _ _)
      (by linarith), fun ω => mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith),
    fun ω => ?_⟩
  have := mul_le_mul_of_nonneg_left ((hZ₂ ω).trans (le_max_right (Z₁ ω) (Z₂ ω)))
    (by linarith : 0 ≤ c)
  linarith

/-- The tail of the high-contrast scale at the origin under a law. -/
theorem osBound_highContrastScale {Λ : ℝ} (hΛ1 : 1 ≤ Λ) {P : Measure (CoefficientField d Λ)}
    [IsProbabilityMeasure P] {κ C : ℝ} {C₁ : ℝ → ℝ} (pk : HighContrastExcessPackage hΛ1 P κ C C₁)
    (hC : 0 < C) {τ : ℝ} (hτ : 0 < τ) (hτd : τ ≤ d) :
    OsBound P (fun a => pk.X (toHighContrast hΛ1 a)) τ ((8 : ℝ) ^ τ⁻¹ * (C * (2 + Λ / 1) ^ C)) := by
  have hA₀0 : 0 < C * (2 + Λ / 1) ^ C := mul_pos hC (Real.rpow_pos_of_pos (by linarith) _)
  refine osBound_of_tail (pk.measurable_X.comp (measurable_toHighContrast hΛ1)) hτ hτd hA₀0
    fun t ht => ?_
  have h := pk.tail t ht
  have hset : {a : CoefficientField d Λ | t * (C * (2 + Λ / 1) ^ C) ≤
      (pk.X ∘ toHighContrast hΛ1) a} =
      toHighContrast hΛ1 ⁻¹' {b | C * (2 + Λ / 1) ^ C * t ≤ pk.X b} := by
    ext a
    show t * (C * (2 + Λ / 1) ^ C) ≤ pk.X (toHighContrast hΛ1 a) ↔
      C * (2 + Λ / 1) ^ C * t ≤ pk.X (toHighContrast hΛ1 a)
    rw [mul_comm t]
  rw [hset, ← Measure.map_apply (measurable_toHighContrast hΛ1)
    (measurableSet_le measurable_const pk.measurable_X),
    ← ENNReal.ofReal_toReal (measure_ne_top _ _), ← measureReal_def]
  exact ENNReal.ofReal_le_ofReal h

theorem toHighContrast_translate_mem_Ωend {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    {P : Measure (CoefficientField d Λ)} {κ C : ℝ} {C₁ : ℝ → ℝ}
    (pk : HighContrastExcessPackage hΛ1 P κ C C₁) (a : CoefficientField d Λ) (m : Fin d → ℤ)
    (hb : toHighContrast hΛ1 a ∈ pk.Ωend) :
    toHighContrast hΛ1 (translate (latticeShift (2 • m)) a) ∈ pk.Ωend := by
  rw [toHighContrast_translate hΛ1 m a]
  have h := pk.invariant m
  have hb2 : toHighContrast hΛ1 a ∈ translateCoeff m ⁻¹' pk.Ωend := by rw [h]; exact hb
  exact Set.mem_preimage.1 hb2

theorem ae_toHighContrast_translate_eq {Λ : ℝ} (hΛ1 : 1 ≤ Λ) (a : CoefficientField d Λ)
    (m : Fin d → ℤ) :
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      (toHighContrast hΛ1 (translate (latticeShift (2 • m)) a)).1 x =
        a.field ((2 : ℝ) • x + latticeShift (2 • m)) := by
  filter_upwards [toHighContrast_ae_eq hΛ1 (translate (latticeShift (2 • m)) a)] with x hx
  rw [hx, add_comm]
  rfl

theorem ae_add_gradPhi_translate_eq_correctorColumn {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    {P : Measure (CoefficientField d Λ)} {κ C : ℝ} {C₁ : ℝ → ℝ}
    (pk : HighContrastExcessPackage hΛ1 P κ C C₁) (S : HomogenizationData P)
    (a : CoefficientField d Λ) (m : Fin d → ℤ)
    (hida : ∀ j : Fin d, dilatedGradient ((S.corrector (unitVector j)).grad a) =ᵐ[volume]
      pk.gradPhi (unitVector j) (toHighContrast hΛ1 a)) (e : Vec d) :
    (fun x => e + pk.gradPhi e (toHighContrast hΛ1 (translate (latticeShift (2 • m)) a)) x)
      =ᵐ[volume]
      fun x => ∑ j, e j • correctorColumn S a j ((2 : ℝ) • x + latticeShift (2 • m)) := by
  rw [toHighContrast_translate hΛ1 m a]
  exact pk.ae_add_gradPhi_translateCoeff_eq (toHighContrast hΛ1 a) m
    (fun j => (S.corrector (unitVector j)).grad a) hida e

theorem memLp_correctorColumn_ball {Λ : ℝ} {P : Measure (CoefficientField d Λ)}
    (S : HomogenizationData P) (a : CoefficientField d Λ) (z : Vec d)
    (hloc : ∀ i : Fin d, ∀ R : ℝ, 0 < R →
      MemLp ((S.corrector (unitVector i)).potential a) 2 (volume.restrict (ball 0 R)) ∧
      MemLp ((S.corrector (unitVector i)).grad a) 2 (volume.restrict (ball 0 R)))
    (j k : Fin d) (R' : ℝ) :
    MemLp (fun x => correctorColumn S a j x k) 2 (volume.restrict (ball z R')) := by
  have hpos : 0 < euclideanNorm z + |R'| + 1 := by
    have := zero_le_euclideanNorm z; have := abs_nonneg R'; linarith
  have hgR := ((hloc j) _ hpos).2.mono_measure
    (Measure.restrict_mono (ball_subset_originBall' z R') le_rfl)
  have h := (memLp_const (unitVector j k)).add (memLp_pi_iff.mp hgR k)
  exact h

/-- **The excess decay of one slope on balls at the center `z`, for one coefficient** in the
form of `BallExcessDecay`. -/
theorem ballExcessDecay_pathwise {Λ : ℝ} (hΛ1 : 1 ≤ Λ) [NeZero d]
    {P : Measure (CoefficientField d Λ)} {κ C : ℝ} {C₁ : ℝ → ℝ}
    (pk : HighContrastExcessPackage hΛ1 P κ C C₁) (hκ : 0 < κ) (hC : 0 ≤ C)
    (hC₁ : ∀ ϑ, 0 < C₁ ϑ) (S : HomogenizationData P) (a : CoefficientField d Λ)
    (m : Fin d → ℤ) {z : Vec d} (hzy : euclideanNorm (z - latticeShift (2 • m)) ≤ 2 * d)
    (hb : toHighContrast hΛ1 a ∈ pk.Ωend)
    (hida : ∀ j : Fin d, dilatedGradient ((S.corrector (unitVector j)).grad a) =ᵐ[volume]
      pk.gradPhi (unitVector j) (toHighContrast hΛ1 a))
    (hwg : ∀ i : Fin d, HasWeakGradient Set.univ ((S.corrector (unitVector i)).potential a)
      ((S.corrector (unitVector i)).grad a))
    (hloc : ∀ i : Fin d, ∀ R : ℝ, 0 < R →
      MemLp ((S.corrector (unitVector i)).potential a) 2 (volume.restrict (ball 0 R)) ∧
      MemLp ((S.corrector (unitVector i)).grad a) 2 (volume.restrict (ball 0 R)))
    (harm : ∀ i : Fin d, HasWeakDivergence Set.univ
      (fun x => (a x).mulVec (unitVector i + (S.corrector (unitVector i)).grad a x)) (fun _ => 0))
    {CE β' Rε X₀ : ℝ}
    (hRε : ∀ r : ℝ, Rε ≤ r →
      (d : ℝ) * (2 * Real.sqrt (2 ^ d) * CE * (2 * r) ^ (-β')) ^ 2 ≤ (1 / 4 : ℝ) ^ d / 16)
    (hosc : ∀ i : Fin d, ∀ t : ℝ, X₀ ≤ t → ∃ c : ℝ, ∫ x in ball z t,
      ((S.corrector (unitVector i)).potential a x - c) ^ 2 ≤
        2 ^ d * (CE * (2 * t) ^ (1 - β')) ^ 2 * volume.real (ball z t))
    (hXH : 2 * pk.X (toHighContrast hΛ1 (translate (latticeShift (2 • m)) a)) ≤ X₀)
    (hXd : 2 * (d : ℝ) ≤ X₀) (hXRε : Rε ≤ X₀)
    {R : ℝ} (hXR : X₀ ≤ R) {v : Vec d → ℝ} {g : Vec d → Vec d}
    (hv : MemLp v 2 (volume.restrict (ball z ((2 * Λ + 4) * R))))
    (hg : ∀ k, MemLp (fun x => g x k) 2 (volume.restrict (ball z ((2 * Λ + 4) * R))))
    (hw : HasWeakGradient (ball z ((2 * Λ + 4) * R)) v g)
    (hdiv : HasWeakDivergence (ball z ((2 * Λ + 4) * R)) (fun x => (a x).mulVec (g x))
      (fun _ => 0))
    {ϑ : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) :
    ∃ e : Vec d,
      euclideanSq e * volume.real (ball z ((2 * Λ + 4) * R)) ≤
          ((2 * Λ + 4) ^ d * (2 * (1 + C₁ ϑ ^ 2 * Λ)) / ballGramConstant d +
            C₁ ϑ ^ 2 * Λ * (2 * Λ + 4) ^ d) *
            ∫ x in ball z ((2 * Λ + 4) * R), euclideanSq (g x) ∧
        ∀ t : ℝ, X₀ ≤ t → t ≤ R →
          (∫ x in ball z t, euclideanSq (g x - ∑ j, e j • correctorColumn S a j x)) *
              volume.real (ball z ((2 * Λ + 4) * R)) ≤
            ((2 * Λ + 4) ^ d * (2 * (1 + C₁ ϑ ^ 2 * Λ)) / ballGramConstant d +
              C₁ ϑ ^ 2 * Λ * (2 * Λ + 4) ^ d) * (t / R) ^ (2 * ϑ) * volume.real (ball z t) *
              ∫ x in ball z ((2 * Λ + 4) * R), euclideanSq (g x) := by
  have hΛ0 : 0 ≤ Λ := by linarith
  have hL1 : 1 ≤ 2 * Λ + 4 := by linarith
  have hL0 : 0 < 2 * Λ + 4 := by linarith
  have hZ1 := pk.one_le_X (toHighContrast hΛ1 (translate (latticeShift (2 • m)) a))
  have hR0 : 0 < R := by linarith
  have hb' := toHighContrast_translate_mem_Ωend hΛ1 pk a m hb
  have hcoef := ae_toHighContrast_translate_eq hΛ1 a m
  have hW := ae_add_gradPhi_translate_eq_correctorColumn hΛ1 pk S a m hida
  have hWloc := memLp_correctorColumn_ball S a z hloc
  obtain ⟨e, hzoom, htop⟩ := pk.ball_excess hΛ1 hκ hC hb' a hzy hcoef hW hWloc
    (by linarith) (by linarith) hv hg hw hdiv hϑ0 hϑ1 (hC₁ ϑ).le
  have hIg : 0 ≤ ∫ x in ball z ((2 * Λ + 4) * R), euclideanSq (g x) :=
    setIntegral_nonneg (measurableSet_ball z _) fun x _ => zero_le_euclideanSq _
  have hc0 : 0 ≤ C₁ ϑ ^ 2 * Λ := mul_nonneg (sq_nonneg _) hΛ0
  have hA : 0 ≤ (2 * Λ + 4) ^ d * (2 * (1 + C₁ ϑ ^ 2 * Λ)) / ballGramConstant d :=
    div_nonneg (mul_nonneg (pow_nonneg hL0.le d) (by linarith)) (ballGramConstant_pos d).le
  have hB : 0 ≤ C₁ ϑ ^ 2 * Λ * (2 * Λ + 4) ^ d := mul_nonneg hc0 (pow_nonneg hL0.le d)
  refine ⟨e, ?_, fun t ht1 ht2 => ?_⟩
  · refine (euclideanSq_slope_mul_le_of_gram S a hR0 hL1 hwg hloc harm
      (fun i => hosc i R hXR) (hRε R (by linarith)) hg hWloc e htop).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) hIg
  · have ht0 : 0 < t := by linarith
    have h1 := hzoom t (by linarith) (by linarith) ht2
    refine (zoom_mul_volume_le hL0 hR0 ht0 h1).trans ?_
    have hq : 0 ≤ (t / R) ^ (2 * ϑ) := Real.rpow_nonneg (div_nonneg ht0.le hR0.le) _
    have hvt : 0 ≤ volume.real (ball z t) := measureReal_nonneg
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hq) hvt) hIg

/-- **The excess decay of one slope on balls at every center** (`BallExcessDecay`), from
Theorem C of Armstrong, Kuusi and Loher and the corrector bounds of Lemma 3.17, with
`L = 2Λ + 4`. -/
theorem ballExcessDecay (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) : BallExcessDecay d Λ := by
  have hΛ1 : 1 ≤ Λ := hΛ.le
  have hΛ0 : 0 ≤ Λ := by linarith
  have : NeZero d := ⟨by omega⟩
  obtain ⟨κ, C, C₁, hκ, hC, hC₁, hpk⟩ := exists_highContrastExcessPackage d hd
  obtain ⟨β, CE, hβ, hCE, hE8⟩ := exists_translated_corrector_bounds hd hΛ
  have hL1 : 1 ≤ 2 * Λ + 4 := by linarith
  have hL0 : 0 < 2 * Λ + 4 := by linarith
  refine ⟨2 * Λ + 4, fun ϑ => (2 * Λ + 4) ^ d * (2 * (1 + C₁ ϑ ^ 2 * Λ)) / ballGramConstant d +
      C₁ ϑ ^ 2 * Λ * (2 * Λ + 4) ^ d, hL1, fun ϑ => ?_, fun τ hτ hτd => ?_⟩
  · have h1 : 0 < (2 * Λ + 4) ^ d * (2 * (1 + C₁ ϑ ^ 2 * Λ)) / ballGramConstant d :=
      div_pos (mul_pos (pow_pos hL0 d) (by have := sq_nonneg (C₁ ϑ); nlinarith))
        (ballGramConstant_pos d)
    have h2 : 0 ≤ C₁ ϑ ^ 2 * Λ * (2 * Λ + 4) ^ d :=
      mul_nonneg (mul_nonneg (sq_nonneg _) hΛ0) (pow_nonneg hL0.le d)
    linarith
  have hτ' : 0 < β * ((d : ℝ) - τ) := mul_pos hβ (by linarith)
  obtain ⟨Rε, hRε1, hRε⟩ := eventually_oscillationConstant_small (d := d) (C := CE) hτ'
  obtain ⟨Cs, hCs, hE8P⟩ := hE8 τ hτ hτd
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hc1 : 1 ≤ 2 + 2 * (d : ℝ) + Rε := by linarith
  refine ⟨(2 + 2 * d + Rε) * ((2 : ℝ) ^ τ⁻¹ *
    max ((8 : ℝ) ^ τ⁻¹ * (C * (2 + Λ / 1) ^ C)) Cs), ?_, fun P hP S z => ?_⟩
  · have : 0 < (8 : ℝ) ^ τ⁻¹ * (C * (2 + Λ / 1) ^ C) :=
      mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (mul_pos hC (Real.rpow_pos_of_pos
        (by linarith) _))
    have : 0 < max ((8 : ℝ) ^ τ⁻¹ * (C * (2 + Λ / 1) ^ C)) Cs := lt_max_of_lt_left this
    have : 0 < (2 : ℝ) ^ τ⁻¹ := Real.rpow_pos_of_pos two_pos _
    positivity
  have : IsProbabilityMeasure P := hP.1
  obtain ⟨pk⟩ := hpk Λ hΛ1 P hP
  obtain ⟨m, hm⟩ := exists_latticeShift_near ((1 / 2 : ℝ) • z)
  have hy2 : latticeShift (2 • m) = (2 : ℝ) • latticeShift m := by
    funext i
    simp only [latticeShift, Pi.smul_apply, smul_eq_mul]
    push_cast [nsmul_eq_mul]
    ring
  have hzy : euclideanNorm (z - latticeShift (2 • m)) ≤ 2 * d := by
    have h1 : z - latticeShift (2 • m) = (2 : ℝ) • ((1 / 2 : ℝ) • z - latticeShift m) := by
      rw [hy2, smul_sub, smul_smul]
      norm_num
    rw [h1, euclideanNorm_smul_abs, abs_of_pos two_pos]
    linarith
  obtain ⟨XE, hXEm, hXEos, hXE1, hXEae⟩ := hE8P P hP S z
  have hT : MeasurePreserving (translate (latticeShift (2 • m))) P P :=
    ⟨measurable_translateCoefficient _, hP.2.1 (2 • m)⟩
  have hXHos := (osBound_highContrastScale hΛ1 pk hC hτ hτd.le).comp_measurePreserving hT
  obtain ⟨hXm, hXos, hX1, hXH, hXE', hXc⟩ := exists_ballExcess_radius hXHos hXEos hXE1 hc1
  refine ⟨_, hXm, hXos, hX1, ?_⟩
  have hid := fun j : Fin d => ae_dilated_eq_highContrast hP hd hκ hC.le
    pk.toHighContrastCorrectorPackage (S.corrector (unitVector j))
  filter_upwards [ae_mem_Ωend hP pk.toHighContrastCorrectorPackage, ae_all_iff.2 hid, hXEae,
    ae_all_iff.2 fun i : Fin d => (S.corrector (unitVector i)).weak_gradient,
    ae_all_iff.2 fun i : Fin d => (S.corrector (unitVector i)).locally_square_integrable,
    ae_all_iff.2 fun i : Fin d => (S.corrector (unitVector i)).harmonic]
    with a hb hida hE8a hwg hloc harm
  intro R hXR v g hv hg hw hdiv ϑ hϑ0 hϑ1
  have hZ1 := pk.one_le_X (toHighContrast hΛ1 (translate (latticeShift (2 • m)) a))
  have hXH2 : 2 * pk.X (toHighContrast hΛ1 (translate (latticeShift (2 • m)) a)) ≤
      (2 + 2 * d + Rε) * max (pk.X (toHighContrast hΛ1 (translate (latticeShift (2 • m)) a)))
        (XE a) :=
    (mul_le_mul_of_nonneg_right (by linarith) (by linarith)).trans (hXH a)
  have hXE2 : XE a + d ≤
      (2 + 2 * d + Rε) * max (pk.X (toHighContrast hΛ1 (translate (latticeShift (2 • m)) a)))
        (XE a) := by
    refine le_trans ?_ (hXE' a)
    nlinarith [mul_le_mul_of_nonneg_left (hXE1 a) hd0,
      mul_nonneg (by linarith : (0 : ℝ) ≤ Rε) (zero_le_one.trans (hXE1 a))]
  have hXc' := hXc a
  exact ballExcessDecay_pathwise hΛ1 pk hκ hC.le hC₁ S a m hzy hb (fun j => (hida j).2.2)
    hwg hloc harm hRε (fun i t ht => (hE8a i t (hXE2.trans ht)).1) hXH2 (by linarith)
    (by linarith) hXR hv hg hw hdiv hϑ0 hϑ1

end QSH
