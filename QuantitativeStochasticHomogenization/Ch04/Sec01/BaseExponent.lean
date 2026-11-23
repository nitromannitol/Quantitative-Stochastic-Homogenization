import QuantitativeStochasticHomogenization.Ch04.Sec01.EnergyQuantityBounds
import QuantitativeStochasticHomogenization.Ch03.Sec04FirstOrderCorrectors
import QuantitativeStochasticHomogenization.Ch04.Sec02AdditiveStructureOfJ1
import QuantitativeStochasticHomogenization.Ch04.Sec05.GaussianMasses

/-!
# Proposition 4.3 and the initial exponent of the bootstrap

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.1, Proposition 4.3, and Step 2 of the proof of Theorem 4.6 in Section 4.2 ("According to
Proposition 4.3 and Lemma A.3, ... `Fluc(t, β/t)` holds").

For a homogenization datum `S` (correctors `φ_e` and the matrix `ā`), the corrected fields are
`G ξ = ∑ ξ_i (e_i + ∇φ_{e_i})`. The inputs, stated as definitions here, are:

* `GradientsOfA1AreCorrected S a`: the gradients of `A₁` are exactly the fields `G ξ`, up to null
  sets ((4.12), from Theorem 3.8 and Lemma 3.6);
* `HomogenizedMatrixBounds ā Λ`: `|ξ|² ≤ ξ·āξ ≤ Λ|ξ|²`;
* `GaussianCorrectorRate P S τ C μ`: Proposition 3.21 for the corrected fields at every center
  `z`: a random scale `X ≤ O_τ(C)` above which the `Φ_{z,r}`-averages of the gradients, fluxes and
  energy densities of `G ξ` are within `C r^{-μ}` of `ξ`, `āξ` and `ξ·āξ` ((3.101)–(3.103), with
  the cross terms of the energy matrix).

Proved here:

* `proposition43`: Proposition 4.3, (4.10), at every center: a random scale `X ≤ O_τ(C')` with
  `|J₁(Φ_{z,r}, p, q) - (½ p·āp + ½ q·ā⁻¹q - p·q)| ≤ 7 C r^{-μ} (|p|² + |q|²)` for `r ≥ X`;
* `flucJ1_of_gaussianCorrectorRate`: for `s ≥ 1`, `Fluc(s, min μ 1)` (Definition 4.8), given the
  measurability of `a ↦ J₁(Φ_{z,r}, p, q)`; it supplies the initial exponent required by
  `additiveStructure_J1` (`flucJ1_base`).

In Proposition 4.3 the book takes the scale of Proposition 3.21 at the origin and uses the
translations of Definition 4.5 for other centers; here the rate is assumed at every center.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## Corrected fields and the inputs -/

section Inputs

variable {P : Measure (CoefficientField d Λ)}

/-- The corrected coordinate `e_i + ∇φ_{e_i}` of a homogenization datum. -/
def correctedCoordinate (S : HomogenizationData P) (a : CoefficientField d Λ) (i : Fin d)
    (x : Vec d) : Vec d :=
  unitVector i + (S.corrector (unitVector i)).grad a x

/-- The corrected field `G ξ = ∑ ξ_i (e_i + ∇φ_{e_i})`. -/
def correctedField (S : HomogenizationData P) (a : CoefficientField d Λ) (ξ : Vec d)
    (x : Vec d) : Vec d :=
  ∑ i, ξ i • correctedCoordinate S a i x

/-- (4.12): the gradients of `A₁` are, up to null sets, exactly the corrected fields. -/
def GradientsOfA1AreCorrected (S : HomogenizationData P) (a : CoefficientField d Λ) : Prop :=
  (∀ w : HarmonicA1 a, ∃ ξ : Vec d, w.grad =ᵐ[volume] correctedField S a ξ) ∧
    ∀ ξ : Vec d, ∃ w : HarmonicA1 a, w.grad =ᵐ[volume] correctedField S a ξ

end Inputs

/-- `|ξ|² ≤ ξ·Aξ ≤ Λ|ξ|²`. -/
def HomogenizedMatrixBounds (A : Mat d) (Λ : ℝ) : Prop :=
  ∀ ξ : Vec d, euclideanSq ξ ≤ dot ξ (A.mulVec ξ) ∧ dot ξ (A.mulVec ξ) ≤ Λ * euclideanSq ξ

/-- The bounds (3.101)–(3.103) with error `ε` on the `Φ_{z,r}`-averages of a family `G ξ`: the
averages of `G ξ`, `a G ξ` and `G ξ·a G ξ` exist and are within `ε|ξ|`, `ε|ξ|` and `2ε|ξ|²` of
`ξ`, `Aξ` and `ξ·Aξ`. -/
def GaussianAverageBounds (a : CoefficientField d Λ) (A : Mat d) (G : Vec d → Vec d → Vec d)
    (z : Vec d) (r ε : ℝ) : Prop :=
  ∀ ξ : Vec d,
    Integrable (fun x => heatKernel z r x • G ξ x) ∧
    Integrable (fun x => heatKernel z r x • (a x).mulVec (G ξ x)) ∧
    Integrable (fun x => heatKernel z r x * dot (G ξ x) ((a x).mulVec (G ξ x))) ∧
    euclideanNorm ((∫ x, heatKernel z r x • G ξ x) - ξ) ≤ ε * euclideanNorm ξ ∧
    euclideanNorm ((∫ x, heatKernel z r x • (a x).mulVec (G ξ x)) - A.mulVec ξ) ≤
      ε * euclideanNorm ξ ∧
    |(∫ x, heatKernel z r x * dot (G ξ x) ((a x).mulVec (G ξ x))) - dot ξ (A.mulVec ξ)| ≤
      2 * ε * euclideanNorm ξ ^ 2

/-- **Proposition 3.21** for the corrected fields of `S`, at the exponent `τ`, with constant `C`
and rate `μ`, at every center: a jointly measurable family of random scales `X(·, z) ≤ O_τ(C)` such
that, for every `z`, almost surely the bounds (3.101)–(3.103) hold with error `C r^{-μ}` at the
masks `Φ_{z,r}`, `r ≥ max(X(·, z), 1)`. -/
def GaussianCorrectorRate (P : Measure (CoefficientField d Λ)) (S : HomogenizationData P)
    (τ C μ : ℝ) : Prop :=
  ∃ X : CoefficientField d Λ → Vec d → ℝ, Measurable (Function.uncurry X) ∧
    ∀ z : Vec d, OsBound P (fun a => X a z) τ C ∧
      ∀ᵐ a ∂P, ∀ r : ℝ, 1 ≤ r → X a z ≤ r →
        GaussianAverageBounds a S.homogenized (correctedField S a) z r (C * r ^ (-μ))

/-! ## The homogenized energy -/

theorem dot_inv_mulVec_nonneg_le {A : Mat d}
    (hA : ∀ ξ : Vec d, euclideanSq ξ ≤ dot ξ (A.mulVec ξ)) (q : Vec d) :
    0 ≤ dot q (A⁻¹.mulVec q) ∧ dot q (A⁻¹.mulVec q) ≤ euclideanSq q := by
  have hy : A.mulVec (A⁻¹.mulVec q) = q := mulVec_inv_mulVec (isUnit_det_of_coercive hA) q
  have h1 : dot q (A⁻¹.mulVec q) = dot (A⁻¹.mulVec q) (A.mulVec (A⁻¹.mulVec q)) := by
    rw [hy]
    exact dotProduct_comm _ _
  refine ⟨h1 ▸ (euclideanSq_nonneg _).trans (hA _), ?_⟩
  have h2 := dot_le q (A⁻¹.mulVec q)
  have h3 := euclideanNorm_inv_mulVec_le hA q
  have hq0 := euclideanNorm_nonneg q
  rw [← euclideanNorm_sq]
  nlinarith [euclideanNorm_nonneg (A⁻¹.mulVec q)]

theorem abs_homogenizedJ1_le {A : Mat d} (hA : HomogenizedMatrixBounds A Λ) {p q : Vec d}
    (hp : euclideanNorm p ≤ 1) (hq : euclideanNorm q ≤ 1) :
    |homogenizedJ1 A p q| ≤ |Λ| + 2 := by
  have hp2 : euclideanSq p ≤ 1 := by
    rw [← euclideanNorm_sq]; nlinarith [euclideanNorm_nonneg p]
  have hq2 : euclideanSq q ≤ 1 := by
    rw [← euclideanNorm_sq]; nlinarith [euclideanNorm_nonneg q]
  obtain ⟨hpa, hpb⟩ := hA p
  have hp0 := euclideanSq_nonneg p
  obtain ⟨hqa, hqb⟩ := dot_inv_mulVec_nonneg_le (fun ξ => (hA ξ).1) q
  have hpq := abs_dot_le p q
  have hpn := euclideanNorm_nonneg p
  have hqn := euclideanNorm_nonneg q
  have hpq' : |dot p q| ≤ 1 := hpq.trans (by nlinarith)
  have hΛ : Λ * euclideanSq p ≤ |Λ| := by
    calc Λ * euclideanSq p ≤ |Λ| * euclideanSq p :=
          mul_le_mul_of_nonneg_right (le_abs_self Λ) hp0
      _ ≤ |Λ| * 1 := mul_le_mul_of_nonneg_left hp2 (abs_nonneg Λ)
      _ = |Λ| := mul_one _
  obtain ⟨h1, h2⟩ := abs_le.mp hpq'
  unfold homogenizedJ1
  rw [abs_le]
  constructor <;> nlinarith [abs_nonneg Λ]

/-! ## Proposition 4.3 -/

section Proposition43

variable {P : Measure (CoefficientField d Λ)}

/-- **Proposition 4.3 at one coefficient field and one scale**: if the gradients of `A₁` are the
corrected fields and the bounds (3.101)–(3.103) hold with error `ε ≤ 1/5` at `Φ_{z,r}`, then
`|J₁(Φ_{z,r}, p, q) - (½ p·āp + ½ q·ā⁻¹q - p·q)| ≤ 7 ε (|p|² + |q|²)`. -/
theorem abs_J1Heat_sub_homogenizedJ1_le (S : HomogenizationData P) (a : CoefficientField d Λ)
    (hA : HomogenizedMatrixBounds S.homogenized Λ) (hspan : GradientsOfA1AreCorrected S a)
    (z : Vec d) (r : ℝ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 5)
    (havg : GaussianAverageBounds a S.homogenized (correctedField S a) z r ε) (p q : Vec d) :
    |J1Heat a z r p q - homogenizedJ1 S.homogenized p q| ≤
      7 * ε * (euclideanNorm p ^ 2 + euclideanNorm q ^ 2) := by
  refine abs_J1_sub_homogenizedJ1_le a (heatKernel z r) S.homogenized S.symmetric
    (fun ξ => (hA ξ).1) (correctedField S a) hspan.1 hspan.2 p q hε0 hε fun ξ => ?_
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := havg ξ
  exact abs_j1Functional_sub_le_of_averages a _ _ p q ξ _ h1 h2 h3 h4 h5 h6

/-- **Proposition 4.3 with the constant of the random scales explicit**: given the structure (4.12)
of `A₁` almost surely, the bounds on `ā` and Proposition 3.21 at the exponent `τ` with constant `C`
and rate `μ`, the random scales `X = max(X_{3.21}, r₀)`, `r₀ = max 1 ((5C)^{1/μ})`, are
`O_τ(2^{1/τ} max(C, r₀ (log 2)^{-1/τ}))` and above them (4.10) holds. -/
theorem proposition43_at [IsProbabilityMeasure P] (S : HomogenizationData P)
    (hA : HomogenizedMatrixBounds S.homogenized Λ)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a) {τ C μ : ℝ} (hτ : 0 < τ)
    (hμ : 0 < μ) (hrate : GaussianCorrectorRate P S τ C μ) :
    ∃ X : CoefficientField d Λ → Vec d → ℝ,
      Measurable (Function.uncurry X) ∧ (∀ a z, 1 ≤ X a z) ∧ ∀ z : Vec d,
        OsBound P (fun a => X a z) τ
          ((2 : ℝ) ^ τ⁻¹ * max C (max 1 ((5 * C) ^ μ⁻¹) / Real.log 2 ^ τ⁻¹)) ∧
        ∀ᵐ a ∂P, ∀ r : ℝ, X a z ≤ r → ∀ p q : Vec d,
          |J1Heat a z r p q - homogenizedJ1 S.homogenized p q| ≤
            7 * (C * r ^ (-μ)) * (euclideanNorm p ^ 2 + euclideanNorm q ^ 2) := by
  have hC : 0 < C := by
    obtain ⟨X, -, hX⟩ := hrate
    exact (hX 0).1.scale_pos
  set r₀ : ℝ := max 1 ((5 * C) ^ μ⁻¹) with hr₀
  have hr₀1 : 1 ≤ r₀ := le_max_left _ _
  have hr₀0 : 0 < r₀ := zero_lt_one.trans_le hr₀1
  have hlog : 0 < Real.log 2 ^ τ⁻¹ := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _
  obtain ⟨X, hXm, hXz⟩ := hrate
  have hconst : OsBound P (fun _ => r₀) τ (r₀ / Real.log 2 ^ τ⁻¹) :=
    osBound_of_le_const measurable_const hτ hr₀0 (Filter.Eventually.of_forall fun _ => le_rfl)
  refine ⟨fun a z => max (X a z) r₀, hXm.max measurable_const,
    fun a z => hr₀1.trans (le_max_right _ _), fun z => ?_⟩
  obtain ⟨hX, hgood⟩ := hXz z
  refine ⟨osBound_max hX hconst, ?_⟩
  filter_upwards [hgood, hspan] with a ha hsp
  intro r hr p q
  have hr₀r : r₀ ≤ r := (le_max_right _ _).trans hr
  have hr1 : 1 ≤ r := hr₀1.trans hr₀r
  have hr0 : 0 < r := zero_lt_one.trans_le hr1
  have hXr : X a z ≤ r := (le_max_left _ _).trans hr
  have h5C : 5 * C ≤ r ^ μ := by
    have h1 : (5 * C) ^ μ⁻¹ ≤ r := (le_max_right _ _).trans hr₀r
    have h2 := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) h1 hμ.le
    rwa [Real.rpow_inv_rpow (by positivity) hμ.ne'] at h2
  have hε : C * r ^ (-μ) ≤ 1 / 5 := by
    rw [Real.rpow_neg hr0.le, ← div_eq_mul_inv, div_le_iff₀ (Real.rpow_pos_of_pos hr0 _)]
    linarith
  exact abs_J1Heat_sub_homogenizedJ1_le S a hA hsp z r
    (mul_nonneg hC.le (Real.rpow_nonneg hr0.le _)) hε (ha r hr1 hXr) p q

/-- **Proposition 4.3**, (4.10), at every center. Given the structure (4.12) of `A₁` almost
surely, the bounds on `ā` and Proposition 3.21 at the exponent `τ` with constant `C` and rate
`μ`, there are `C'` and a jointly measurable family of random scales `1 ≤ X(·, z) ≤ O_τ(C')`
such that for every `z`, almost surely
`|J₁(Φ_{z,r}, p, q) - (½ p·āp + ½ q·ā⁻¹q - p·q)| ≤ 7 C r^{-μ} (|p|² + |q|²)` for all
`r ≥ X(·, z)` and all `p, q`. -/
theorem proposition43 [IsProbabilityMeasure P] (S : HomogenizationData P)
    (hA : HomogenizedMatrixBounds S.homogenized Λ)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a) {τ C μ : ℝ} (hτ : 0 < τ) (hC : 0 < C)
    (hμ : 0 < μ) (hrate : GaussianCorrectorRate P S τ C μ) :
    ∃ C' : ℝ, 0 < C' ∧ ∃ X : CoefficientField d Λ → Vec d → ℝ,
      Measurable (Function.uncurry X) ∧ (∀ a z, 1 ≤ X a z) ∧ ∀ z : Vec d,
        OsBound P (fun a => X a z) τ C' ∧
        ∀ᵐ a ∂P, ∀ r : ℝ, X a z ≤ r → ∀ p q : Vec d,
          |J1Heat a z r p q - homogenizedJ1 S.homogenized p q| ≤
            7 * (C * r ^ (-μ)) * (euclideanNorm p ^ 2 + euclideanNorm q ^ 2) :=
  ⟨_, mul_pos (Real.rpow_pos_of_pos two_pos _) (lt_max_of_lt_left hC),
    proposition43_at S hA hspan hτ hμ hrate⟩

end Proposition43

/-! ## The initial exponent of the bootstrap -/

section BaseExponent

variable {P : Measure (CoefficientField d Λ)}

theorem J1Heat_nonneg_le (a : CoefficientField d Λ) (z : Vec d) {r : ℝ} (hr : 0 < r)
    (p q : Vec d) :
    0 ≤ J1Heat a z r p q ∧ J1Heat a z r p q ≤ Λ * euclideanSq p + euclideanSq q :=
  ⟨J1_nonneg a (heatKernel_nonneg z r) (integrable_heatKernel z hr)
      (integral_heatKernel z hr).le p q,
    J1_le a (heatKernel_nonneg z r) (integrable_heatKernel z hr) (integral_heatKernel z hr).le
      p q⟩

/-- **The initial exponent** (Step 2 of the proof of Theorem 4.6): for `s ≥ 1`, Proposition 3.21
at the exponent `s` with rate `μ`, the structure (4.12) of `A₁` and the bounds on `ā` give
`Fluc(s, min μ 1)` for `J₁`, provided `a ↦ J₁(Φ_{z,r}, p, q)` is measurable. -/
theorem flucJ1_of_gaussianCorrectorRate [IsProbabilityMeasure P] (S : HomogenizationData P)
    (hA : HomogenizedMatrixBounds S.homogenized Λ)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a) {s C μ : ℝ} (hs : 1 ≤ s) (hC : 0 < C)
    (hμ : 0 < μ) (hrate : GaussianCorrectorRate P S s C μ)
    (hmeas : ∀ (z : Vec d) (r : ℝ) (p q : Vec d), Measurable fun a : CoefficientField d Λ => J1Heat a z r p q) :
    FlucJ1 P s (min μ 1) := by
  obtain ⟨C', hC', X, -, hX1, hX⟩ := proposition43 S hA hspan (zero_lt_one.trans_le hs) hC hμ hrate
  set K : ℝ := 2 * |Λ| + 3 with hK
  have hK0 : 0 < K := by positivity
  set L : ℝ := Real.log 2 ^ s⁻¹ with hL
  have hL0 : 0 < L := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _
  refine ⟨K * C' + (28 * C + 2 * K * C') / L, by positivity, ?_⟩
  intro z r hr p q hp hq
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  obtain ⟨hXos, hgood⟩ := hX z
  have hp2 : euclideanSq p ≤ 1 := by
    rw [← euclideanNorm_sq]; nlinarith [euclideanNorm_nonneg p]
  have hq2 : euclideanSq q ≤ 1 := by
    rw [← euclideanNorm_sq]; nlinarith [euclideanNorm_nonneg q]
  set c := homogenizedJ1 S.homogenized p q with hc
  have hcK := abs_homogenizedJ1_le hA hp.le hq.le
  -- deterministic bounds on `J₁`
  have hJK : ∀ a : CoefficientField d Λ, |J1Heat a z r p q| ≤ |Λ| + 1 := by
    intro a
    obtain ⟨h0, h1⟩ := J1Heat_nonneg_le a z hr0 p q
    rw [abs_of_nonneg h0]
    have : Λ * euclideanSq p ≤ |Λ| :=
      (mul_le_mul_of_nonneg_right (le_abs_self Λ) (euclideanSq_nonneg p)).trans
        (by nlinarith [abs_nonneg Λ])
    linarith
  have hm : Measurable fun a : CoefficientField d Λ => J1Heat a z r p q := hmeas z r p q
  have hJint : Integrable (fun a => J1Heat a z r p q) P :=
    Integrable.of_bound hm.aestronglyMeasurable (|Λ| + 1)
      (Filter.Eventually.of_forall fun a => by simpa [Real.norm_eq_abs] using hJK a)
  have hXint := hXos.integrable_and_integral_le hs fun a => (zero_le_one.trans (hX1 a z))
  -- the distance to the homogenized energy
  set δ : ℝ := 14 * C * r ^ (-μ) with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hZ : ∀ᵐ a ∂P, |J1Heat a z r p q - c| ≤ δ + K * (X a z / r) := by
    filter_upwards [hgood] with a ha
    by_cases hXr : X a z ≤ r
    · have h1 := ha r hXr p q
      have h2 : euclideanNorm p ^ 2 + euclideanNorm q ^ 2 ≤ 2 := by
        rw [euclideanNorm_sq, euclideanNorm_sq]; linarith
      have h3 : 0 ≤ C * r ^ (-μ) := mul_nonneg hC.le (Real.rpow_nonneg hr0.le _)
      have h4 : 0 ≤ K * (X a z / r) :=
        mul_nonneg hK0.le (div_nonneg (zero_le_one.trans (hX1 a z)) hr0.le)
      nlinarith
    · have h1 : 1 ≤ X a z / r := by
        rw [le_div_iff₀ hr0]; linarith
      have h2 : |J1Heat a z r p q - c| ≤ K := by
        have := abs_sub (J1Heat a z r p q) c
        linarith [hJK a]
      nlinarith
  -- the expectation
  have hE : |(∫ a, J1Heat a z r p q ∂P) - c| ≤ δ + K * (2 * C') / r := by
    have hsub : (∫ a, J1Heat a z r p q ∂P) - c = ∫ a, (J1Heat a z r p q - c) ∂P := by
      rw [integral_sub hJint (integrable_const c), integral_const, probReal_univ, one_smul]
    have hXr : Integrable (fun a => δ + K * (X a z / r)) P :=
      (integrable_const δ).add ((hXint.1.div_const r).const_mul K)
    calc |(∫ a, J1Heat a z r p q ∂P) - c|
        = |∫ a, (J1Heat a z r p q - c) ∂P| := by rw [hsub]
      _ ≤ ∫ a, |J1Heat a z r p q - c| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ a, (δ + K * (X a z / r)) ∂P :=
          integral_mono_ae (hJint.sub (integrable_const c)).abs hXr hZ
      _ = δ + K * (∫ a, X a z ∂P) / r := by
          rw [integral_add (integrable_const δ) ((hXint.1.div_const r).const_mul K),
            integral_const, probReal_univ, one_smul, integral_const_mul, integral_div]
          ring
      _ ≤ δ + K * (2 * C') / r := by
          gcongr
          exact hXint.2
  -- the stochastic bound
  set D : ℝ := 2 * δ + K * (2 * C') / r with hD
  have hD0 : 0 < D := by positivity
  have hbound : ∀ᵐ a ∂P, |J1Heat a z r p q - ∫ a', J1Heat a' z r p q ∂P| ≤
      K / r * X a z + D := by
    filter_upwards [hZ] with a ha
    have h1 := abs_sub_le (J1Heat a z r p q) c (∫ a', J1Heat a' z r p q ∂P)
    rw [abs_sub_comm c] at h1
    have h2 : K * (X a z / r) = K / r * X a z := by ring
    linarith
  have hos1 : OsBound P (fun a => K / r * X a z) s (K / r * C') := hXos.const_mul (by positivity)
  have hos2 : OsBound P (fun _ => D) s (D / L) :=
    osBound_of_le_const measurable_const (zero_lt_one.trans_le hs) hD0
      (Filter.Eventually.of_forall fun _ => le_rfl)
  have hos := (osBound_add hos1 hos2 hs).of_le_ae
    (continuous_abs.measurable.comp (hm.sub measurable_const)) hbound
  refine ⟨hJint, hos.mono_scale ?_⟩
  -- the scale
  have hmin : r ^ (-μ) ≤ r ^ (-min μ 1) := rpow_neg_le_rpow_neg hr (min_le_left _ _)
  have hone : r⁻¹ ≤ r ^ (-min μ 1) := by
    have := rpow_neg_le_rpow_neg hr (min_le_right μ 1)
    rwa [Real.rpow_neg_one] at this
  have hrinv : 0 < r⁻¹ := inv_pos.mpr hr0
  have hρ0 : 0 ≤ r ^ (-μ) := Real.rpow_nonneg hr0.le _
  calc K / r * C' + D / L
      = K * C' * r⁻¹ + (28 * C * r ^ (-μ) + 2 * K * C' * r⁻¹) / L := by
        rw [hD, hδ]; ring
    _ ≤ K * C' * r ^ (-min μ 1) +
          (28 * C * r ^ (-min μ 1) + 2 * K * C' * r ^ (-min μ 1)) / L := by
        gcongr
    _ = (K * C' + (28 * C + 2 * K * C') / L) * r ^ (-min μ 1) := by ring

/-- **The initial exponent of the bootstrap for Theorem 4.6**: if Proposition 3.21 holds at every
exponent `s ∈ (1, 2)` with some rate, together with the structure (4.12) of `A₁`, the bounds on `ā`
and the measurability of `J₁`, then for every `s ∈ (1, 2)` there is `α₀ > 0` with `Fluc(s, α₀)`:
the hypothesis `hbase` of `additiveStructure_J1`. -/
theorem flucJ1_base [IsProbabilityMeasure P] (S : HomogenizationData P)
    (hA : HomogenizedMatrixBounds S.homogenized Λ)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hrate : ∀ s : ℝ, 1 < s → s < 2 → ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧ GaussianCorrectorRate P S s C μ)
    (hmeas : ∀ (z : Vec d) (r : ℝ) (p q : Vec d), Measurable fun a : CoefficientField d Λ => J1Heat a z r p q) :
    ∀ s : ℝ, 1 < s → s < 2 → ∃ α₀ : ℝ, 0 < α₀ ∧ FlucJ1 P s α₀ := by
  intro s hs1 hs2
  obtain ⟨C, μ, hC, hμ, hrate⟩ := hrate s hs1 hs2
  exact ⟨min μ 1, lt_min hμ one_pos,
    flucJ1_of_gaussianCorrectorRate S hA hspan hs1.le hC hμ hrate hmeas⟩

end BaseExponent

end QSH
