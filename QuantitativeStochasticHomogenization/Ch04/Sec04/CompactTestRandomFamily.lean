import QuantitativeStochasticHomogenization.Ch03.Sec03.FirstOrderLiouvilleReduction
import QuantitativeStochasticHomogenization.Ch03.Sec04.CorrectorMeasurability
import QuantitativeStochasticHomogenization.Ch04.Sec06.NegativeSobolevCorrector
import QuantitativeStochasticHomogenization.Ch04.Sec03.TrialGapCore
import QuantitativeStochasticHomogenization.Ch06.Sec01.CorrectorIdentification
import QuantitativeStochasticHomogenization.Ch06.Sec01.HighContrastDivCurl

/-!
# Families of first-order and flux correctors above a random scale

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 3.17, Lemma 6.1 and Proposition 6.2, in the form used by the finite-ball estimate with compact
tests: there are `β, C > 0` such that for every `τ ∈ (0, d)` and every law there are a matrix `D`
(the homogenized matrix of the high-contrast theorem) with `|ξ|² ≤ ξ · D ξ ≤ Λ² |ξ|²` and a random
scale `R ≥ 1` with `R ≤ O_τ(C_τ)`, `C_τ` depending only on `d`, `Λ` and `τ`, such that almost
surely the coordinate correctors and the skew parts of flux correctors form a family with
homogenized matrix `D` whose oscillations on `B_r`, `r ≥ R`, are at most
`(1 + d²) C r^{1 - β(d - τ)}`. This is the construction in the proof of
`firstOrderLiouville_of_quarterExcessStep` at the exponent `τ`, with the random scale
`R = 1 + ∑ᵢ max(Xᵢ, 0)`.
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ}

/-- **Corrector families above a random scale**, with constants chosen before the law. The
ellipticity bound used for `D` is `Λ ^ 2`, not the book's `Λ`; only the constants are affected. -/
theorem exists_ae_sublinearCorrectorFamily (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) :
    ∃ β C : ℝ, 0 < β ∧ 0 < C ∧ ∀ τ : ℝ, 0 < τ → τ < d → ∃ Cτ : ℝ, 0 < Cτ ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
        ∃ (D : Mat d) (R : CoefficientField d Λ → ℝ),
          (∀ ξ : Vec d, euclideanSq ξ ≤ dot ξ (D.mulVec ξ) ∧
            dot ξ (D.mulVec ξ) ≤ Λ ^ 2 * euclideanSq ξ) ∧
          Measurable R ∧ OsBound P R τ Cτ ∧ (∀ a, 1 ≤ R a) ∧
          ∀ᵐ a ∂P, Nonempty (SublinearCorrectorFamily a D (β * ((d : ℝ) - τ))
            ((1 + (d : ℝ) ^ 2) * C) (R a)) := by
  obtain ⟨β, C, hβ, hC, hE8⟩ := sublinearCorrectors d hd Λ hΛ
  obtain ⟨κ, C₀, hκ, hC₀, hpk⟩ := exists_highContrastCorrectorPackage d hd
  refine ⟨β, C, hβ, hC, fun τ hτ hτd => ?_⟩
  obtain ⟨Cs, hCs, hE8s⟩ := hE8 τ hτ hτd
  set c₁ : ℝ := 1 / Real.log 2 ^ τ⁻¹ with hc₁
  have hc₁0 : 0 < c₁ := div_pos one_pos (Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _)
  set Cτ : ℝ := 2 * (2 : ℝ) ^ τ⁻¹ * (c₁ + (2 * (2 : ℝ) ^ τ⁻¹) ^ d * Cs) with hCτ
  have h2 : 0 < (2 : ℝ) ^ τ⁻¹ := Real.rpow_pos_of_pos two_pos _
  refine ⟨Cτ, by positivity, fun P hP => ?_⟩
  have : IsProbabilityMeasure P := hP.1
  have : NeZero d := ⟨by omega⟩
  obtain ⟨S⟩ := homogenizationDataExists d hd Λ hΛ P hP
  obtain ⟨pk⟩ := hpk Λ hΛ.le P hP
  have hunit : ∀ i : Fin d, euclideanNorm (unitVector i) = 1 :=
    euclideanNorm_unitVector_eq_one_of_coord
  have hFl : ∀ i : Fin d, Nonempty (FluxCorrector (S.corrector (unitVector i))) := fun i =>
    (hE8s P hP _ (hunit i) _).1
  set Fl : ∀ i : Fin d, FluxCorrector (S.corrector (unitVector i)) := fun i =>
    Classical.choice (hFl i) with hFldef
  have hX := fun i : Fin d => (hE8s P hP _ (hunit i) _).2 (Fl i)
  choose X hXm hXos hXae using hX
  set R : CoefficientField d Λ → ℝ := fun a => 1 + ∑ i, max (X i a) 0 with hRdef
  set D : Mat d := pk.abar with hDdef
  -- the bounds of the homogenized matrix
  have hD : ∀ ξ : Vec d, euclideanSq ξ ≤ dot ξ (D.mulVec ξ) ∧
      dot ξ (D.mulVec ξ) ≤ Λ ^ 2 * euclideanSq ξ := by
    have hgood := ae_dilated_eq_highContrast hP hd hκ hC₀.le pk (S.corrector (unitVector ⟨0, by omega⟩))
    obtain ⟨a, ha, -⟩ := hgood.exists
    have hbell := ae_isEllipticMatrix_toHighContrast hΛ.le a
    intro ξ
    have h := pk.vecNormSq_le_vecDot_symmPart_and_le hκ hC₀.le ha hbell ξ
    rw [dot_mulVec_eq_vecDot_symmPart]
    exact h
  refine ⟨D, R, hD, measurable_const.add (Finset.measurable_sum _ fun i _ =>
    (hXm i).max measurable_const), ?_, fun a => ?_, ?_⟩
  · have h1 : OsBound P (fun _ : CoefficientField d Λ => (1 : ℝ)) τ c₁ := by
      have := osBound_of_le_const (P := P) (X := fun _ => (1 : ℝ)) measurable_const hτ one_pos
        (ae_of_all _ fun _ => le_rfl)
      simpa [hc₁] using this
    have h2' := osBound_finset_sum_of_pos (P := P) Finset.univ hτ hCs
      (X := fun i a => max (X i a) 0) fun i _ => (hXos i).max_zero
    have h3 := osBound_add_le_sum h1 h2'
    simpa [hCτ, Finset.card_univ, Fintype.card_fin] using h3
  · have : 0 ≤ ∑ i, max (X i a) 0 := Finset.sum_nonneg fun i _ => le_max_right _ _
    simp only [hRdef]
    linarith
  · have hskew := fun i : Fin d =>
      (Fl i).ae_skew_divergence_of_package hd hΛ hP hκ hC₀.le pk (hunit i)
    filter_upwards [ae_all_iff.2 hXae, ae_all_iff.2 hskew,
      ae_all_iff.2 fun i => (S.corrector (unitVector i)).weak_gradient,
      ae_all_iff.2 fun i => (S.corrector (unitVector i)).locally_square_integrable,
      ae_all_iff.2 fun i => (S.corrector (unitVector i)).harmonic,
      ae_all_iff.2 fun i => (Fl i).locally_square_integrable] with a hXa hska hwg hlsi hharm hFlsi
    have hXle : ∀ i, X i a ≤ R a := by
      intro i
      have h1 : X i a ≤ max (X i a) 0 := le_max_left _ _
      have h2 : max (X i a) 0 ≤ ∑ i, max (X i a) 0 :=
        Finset.single_le_sum (f := fun i => max (X i a) 0) (fun i _ => le_max_right _ _)
          (Finset.mem_univ i)
      simp only [hRdef]
      linarith
    exact ⟨{ φ := fun i => (S.corrector (unitVector i)).potential a
             gφ := fun i => (S.corrector (unitVector i)).grad a
             σ := fun i x j k => ((Fl i).potential a x j k - (Fl i).potential a x k j) / 2
             gσ := fun i j k x => (1 / 2 : ℝ) • ((Fl i).grad a j k x - (Fl i).grad a k j x)
             weak_gradient_φ := hwg
             weak_gradient_σ := fun i j k => ((hska i) j).2 k
             memLp := fun i R hR => ⟨(hlsi i R hR).1, (hlsi i R hR).2, fun j k =>
               ⟨((hFlsi i R hR j k).1.sub (hFlsi i R hR k j).1).const_mul (1 / 2 : ℝ) |>.ae_eq
                  (Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring),
                 ((hFlsi i R hR j k).2.sub (hFlsi i R hR k j).2).const_smul (1 / 2 : ℝ)⟩⟩
             harmonic := hharm
             flux := fun i j => ((hska i) j).1
             skew := fun i x j k => by ring
             oscillation := by
               intro i r hr
               have hr0 : 0 < r := lt_of_lt_of_le one_pos ((hXa i).1.trans ((hXle i).trans hr))
               obtain ⟨hbd, -⟩ := (hXa i).2 r ((hXle i).trans hr)
               set A := Real.sqrt (⨍ x in ball 0 r, |(S.corrector (unitVector i)).potential a x -
                 (⨍ y in ball 0 r, (S.corrector (unitVector i)).potential a y)| ^ 2) with hA
               set B := Real.sqrt (⨍ x in ball 0 r, frobeniusNorm ((Fl i).potential a x -
                 (Matrix.of fun i' j' => ⨍ y in ball 0 r, (Fl i).potential a y i' j')) ^ 2) with hB
               have hφ : scalarRms volume (ball 0 r)
                   (fun x => (S.corrector (unitVector i)).potential a x -
                     ⨍ y in ball 0 r, (S.corrector (unitVector i)).potential a y) = A := by
                 rw [hA]
                 unfold scalarRms
                 simp only [sq_abs]
               have hentry : ∀ j k, scalarRms volume (ball 0 r)
                   (fun x => ((Fl i).potential a x j k - (Fl i).potential a x k j) / 2 -
                     ⨍ y in ball 0 r, ((Fl i).potential a y j k -
                       (Fl i).potential a y k j) / 2) ≤ B :=
                 fun j k => scalarRms_skew_entry_le (fun j k => (hFlsi i r hr0 j k).1) j k
               have hsum : ∑ j : Fin d, ∑ k : Fin d, scalarRms volume (ball 0 r)
                   (fun x => ((Fl i).potential a x j k - (Fl i).potential a x k j) / 2 -
                     ⨍ y in ball 0 r, ((Fl i).potential a y j k -
                       (Fl i).potential a y k j) / 2) ≤ (d : ℝ) ^ 2 * B := by
                 calc _ ≤ ∑ _j : Fin d, ∑ _k : Fin d, B :=
                       Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hentry j k
                   _ = (d : ℝ) ^ 2 * B := by simp [Finset.sum_const, sq]; ring
               change scalarRms volume (ball 0 r)
                   (fun x => (S.corrector (unitVector i)).potential a x -
                     ⨍ y in ball 0 r, (S.corrector (unitVector i)).potential a y) +
                 ∑ j : Fin d, ∑ k : Fin d, scalarRms volume (ball 0 r)
                   (fun x => ((Fl i).potential a x j k - (Fl i).potential a x k j) / 2 -
                     ⨍ y in ball 0 r, ((Fl i).potential a y j k -
                       (Fl i).potential a y k j) / 2) ≤
                 (1 + (d : ℝ) ^ 2) * C * r ^ (1 - β * ((d : ℝ) - τ))
               rw [hφ]
               have hA0 : 0 ≤ A := Real.sqrt_nonneg _
               have hB0 : 0 ≤ B := Real.sqrt_nonneg _
               have hd2 : 0 ≤ (d : ℝ) ^ 2 := sq_nonneg _
               have hbd' : A + B ≤ C * r ^ (1 - β * ((d : ℝ) - τ)) := hbd
               nlinarith [mul_le_mul_of_nonneg_left hbd' hd2] }⟩

end QSH
