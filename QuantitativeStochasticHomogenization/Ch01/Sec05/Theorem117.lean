import QuantitativeStochasticHomogenization.Ch01.Sec05.TwoScaleSetup
import QuantitativeStochasticHomogenization.Ch01.Sec05.ConvexMeyers
import QuantitativeStochasticHomogenization.AppB.PropositionB11
import QuantitativeStochasticHomogenization.AppB.TheoremB10
import QuantitativeStochasticHomogenization.Ch03.Sec03.CorrectedAffine
import QuantitativeStochasticHomogenization.Ch04.Sec03.TrialGapCore
import QuantitativeStochasticHomogenization.Ch04.Sec03.AveragesFromEnergy

/-!
# Theorem 1.17: homogenization of the Dirichlet problem

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.5, Theorem 1.17, for `d ≥ 2` and a bounded open convex domain `U ⊆ □_0`.

For `ε ∈ (0, 1]` let `m = m(ε)` be the triadic scale of (1.56) (`triadicScale`), `V = ε □_m` and
`φ_k = φ_{m,e_k}` the finite-volume correctors (1.55), that is `ℓ_{e_k} + φ_k` is the minimizer
`v(·, □_m, e_k)` of (1.8), with gradients `Dφ_k`. The quantity (1.56) is
`E'(ε) = ∑_k (‖ε φ_k(·/ε)‖_{L̲²(V)} + ‖a(·/ε)(e_k + ∇φ_k(·/ε)) - ā e_k‖_{H̲⁻¹(V)})²`
(`twoScaleDeviation`), the `H̲⁻¹` norm of a vector field being the sum of the norms of its
components, as in Proposition 1.10.

`theorem_1_17`: for every `δ > 0` there are `β > 0` and `C < ∞` such that, for `ε ∈ (0, 1]`,
`f ∈ W^{1,2+δ}(U)`, solutions `u^ε, u ∈ f + H¹₀(U)` of `-∇·(a(·/ε)∇u^ε) = 0` and `-∇·(ā∇u) = 0`
in `U`, and `r ∈ (0, 1)`, (1.59) holds,
`‖u^ε - u‖_{L̲²(U)} + ‖∇u^ε - ∇u‖_{Ĥ̲⁻¹(U)} + ‖a(·/ε)∇u^ε - ā∇u‖_{Ĥ̲⁻¹(U)} ≤
C ‖∇f‖_{L̲^{2+δ}(U)} (r^β + r^{-2-d/2} E'(ε)^{1/2})`,
and the energy densities satisfy
`‖½∇u^ε·a(·/ε)∇u^ε - ½∇u·ā∇u‖_{W̲^{-2,1}(U)} ≤ C ‖∇f‖²_{L̲^{2+δ}(U)} (r^β + r^{-2-d/2} E'(ε)^{1/2})`.
The matrix `ā` may be any constant symmetric matrix with `Id ≤ ā ≤ Λ Id`.

The proof is the book's: the Meyers estimate for the constant-coefficient problem on `U`
(`meyers_constantCoefficient_of_convex`, from Theorem C.7) bounds the boundary layer term (1.63)
by `r^β`, `β = 1/2 - 1/q`, `q = (2 + δ₀) ∧ (2 + δ)`, `δ₀` the Meyers exponent of `U`; the
multipliers `η_r ∂_j ũ` of the two-scale expansion (`exists_multipliers`) satisfy (1.65); Steps 2–4
(`exists_twoScale_steps`) give the three bounds of (1.59); the energy estimate (Lemma C.8) and
Lemma 1.16 with exponent `1` give the bound of the energy densities. The norms are the normalized
norms of (0.29)–(0.31); the `Ĥ̲⁻¹(U)` norm dominates the `H̲⁻¹(U)` norm of the book.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal Pointwise

noncomputable section

namespace QSH

namespace TwoScale

variable {d : ℕ} {Λ : ℝ}

/-- **The quantity `E'(ε)` of (1.56)** for finite-volume correctors `φ_k` of gradients `Dφ_k` on
`□_m`, `m = m(ε)`: with `V = ε □_m`,
`E'(ε) = ∑_k (‖ε φ_k(·/ε)‖_{L̲²(V)} + ‖a(·/ε)(e_k + ∇φ_k(·/ε)) - A e_k‖_{H̲⁻¹(V)})²`. -/
def twoScaleDeviation (a : CoefficientField d Λ) (A : Mat d) (ε : ℝ) (φ : Fin d → Vec d → ℝ)
    (Dφ : Fin d → Vec d → Vec d) : ℝ≥0∞ :=
  ∑ k, (ENNReal.ofReal (scalarRms volume (ε • triadicCube d (triadicScale ε))
      (fun x => ε * φ k (ε⁻¹ • x))) +
    vectorNegativeSobolevOneNorm 2 (ε • triadicCube d (triadicScale ε))
      (fun x => (a (ε⁻¹ • x)).mulVec (unitVector k + Dφ k (ε⁻¹ • x)) -
        A.mulVec (unitVector k))) ^ 2

/-- `x² ≤ E` gives `x ≤ E^{1/2}`. -/
theorem le_rpow_half_of_sq_le {x E : ℝ≥0∞} (h : x ^ 2 ≤ E) : x ≤ E ^ (1 / 2 : ℝ) := by
  calc x = (x ^ 2) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
    _ ≤ E ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h (by norm_num)

/-- Each term of `E'(ε)` is at most `E'(ε)^{1/2}`. -/
theorem twoScaleDeviation_terms_le (a : CoefficientField d Λ) (A : Mat d) (ε : ℝ)
    (φ : Fin d → Vec d → ℝ) (Dφ : Fin d → Vec d → Vec d) (k : Fin d) :
    ENNReal.ofReal (scalarRms volume (ε • triadicCube d (triadicScale ε))
        (fun x => ε * φ k (ε⁻¹ • x))) ≤ twoScaleDeviation a A ε φ Dφ ^ (1 / 2 : ℝ) ∧
      ∀ i, negativeSobolevOneNorm 2 (ε • triadicCube d (triadicScale ε))
        (fun x => ((a (ε⁻¹ • x)).mulVec (unitVector k + Dφ k (ε⁻¹ • x)) -
          A.mulVec (unitVector k)) i) 0 ≤ twoScaleDeviation a A ε φ Dφ ^ (1 / 2 : ℝ) := by
  have h : ENNReal.ofReal (scalarRms volume (ε • triadicCube d (triadicScale ε))
        (fun x => ε * φ k (ε⁻¹ • x))) +
      vectorNegativeSobolevOneNorm 2 (ε • triadicCube d (triadicScale ε))
        (fun x => (a (ε⁻¹ • x)).mulVec (unitVector k + Dφ k (ε⁻¹ • x)) -
          A.mulVec (unitVector k)) ≤ twoScaleDeviation a A ε φ Dφ ^ (1 / 2 : ℝ) :=
    le_rpow_half_of_sq_le (Finset.single_le_sum (f := fun k =>
      (ENNReal.ofReal (scalarRms volume (ε • triadicCube d (triadicScale ε))
        (fun x => ε * φ k (ε⁻¹ • x))) +
      vectorNegativeSobolevOneNorm 2 (ε • triadicCube d (triadicScale ε))
        (fun x => (a (ε⁻¹ • x)).mulVec (unitVector k + Dφ k (ε⁻¹ • x)) -
          A.mulVec (unitVector k))) ^ 2) (fun _ _ => zero_le) (Finset.mem_univ k))
  refine ⟨le_self_add.trans h, fun i => le_trans ?_ (le_add_self.trans h)⟩
  exact Finset.single_le_sum (f := fun i => negativeSobolevOneNorm 2
    (ε • triadicCube d (triadicScale ε)) (fun x => ((a (ε⁻¹ • x)).mulVec
      (unitVector k + Dφ k (ε⁻¹ • x)) - A.mulVec (unitVector k)) i) 0)
    (fun _ _ => zero_le) (Finset.mem_univ i)

/-- `r^{-2} (r^{-d})^{1/2} = r^{-2-d/2}`. -/
theorem inv_sq_mul_sqrt_inv_pow {r : ℝ} (hr : 0 < r) (n : ℕ) :
    r⁻¹ ^ 2 * Real.sqrt (r⁻¹ ^ n) = r ^ (-(2 + (n : ℝ) / 2)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast r⁻¹ n, ← Real.rpow_mul (inv_nonneg.2 hr.le),
    ← Real.rpow_natCast r⁻¹ 2, ← Real.rpow_add (inv_pos.2 hr), Real.inv_rpow hr.le,
    ← Real.rpow_neg hr.le]
  congr 1
  push_cast
  ring

/-- A sum of `n` terms bounded by `B` is at most `n B`. -/
theorem sum_fin_le_mul {n : ℕ} {f : Fin n → ℝ} {B : ℝ} (h : ∀ k, f k ≤ B) :
    ∑ k, f k ≤ n * B := by
  calc ∑ k, f k ≤ ∑ _k : Fin n, B := Finset.sum_le_sum fun k _ => h k
    _ = n * B := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem subset_cube_of_subset_triadicCube_zero {U : Set (Vec d)} (hU : U ⊆ triadicCube d 0) :
    U ⊆ cube 0 1 := by
  intro x hx
  have h := Set.mem_pi.1 (hU hx)
  show ∀ i, |x i - (0 : Vec d) i| < 1 / 2
  intro i
  have hi := h i (Set.mem_univ i)
  simp only [pow_zero, Set.mem_Ioo] at hi
  rw [Pi.zero_apply, sub_zero, abs_lt]
  constructor <;> linarith [hi.1, hi.2]

theorem subset_ball_of_subset_triadicCube_zero (hd : 0 < d) {U : Set (Vec d)}
    (hU : U ⊆ triadicCube d 0) : U ⊆ ball 0 d := by
  intro x hx
  have h : ∀ i, |x i - (0 : Vec d) i| < 1 / 2 := subset_cube_of_subset_triadicCube_zero hU hx
  show euclideanNorm (x - 0) < d
  rw [sub_zero]
  have h1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  calc euclideanNorm x ≤ ∑ j, |x j| := euclideanNorm_le_sum_abs_apply x
    _ ≤ ∑ _j : Fin d, (1 / 2 : ℝ) := Finset.sum_le_sum fun j _ => by
        have := h j
        rw [Pi.zero_apply, sub_zero] at this
        exact this.le
    _ < d := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        linarith

theorem isBounded_of_subset_ball {U : Set (Vec d)} {R : ℝ} (hU : U ⊆ ball 0 R) :
    Bornology.IsBounded U :=
  (Metric.isBounded_ball (x := (0 : Vec d)) (r := R)).subset fun x hx => by
    have h : euclideanNorm (x - 0) < R := hU hx
    rw [sub_zero] at h
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt euclideanNorm_le_of_norm h

theorem exists_ball_subset_of_mem {U : Set (Vec d)} (hUo : IsOpen U) {x₀ : Vec d}
    (hx₀ : x₀ ∈ U) : ∃ ρ : ℝ, 0 < ρ ∧ ball x₀ ρ ⊆ U := by
  obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.1 hUo x₀ hx₀
  refine ⟨ρ, hρ, fun y hy => hsub ?_⟩
  have h : euclideanNorm (y - x₀) < ρ := hy
  rw [Metric.mem_ball, dist_eq_norm]
  exact lt_of_le_of_lt euclideanNorm_le_of_norm h

/-- The unnormalized `L^p(U)` norm is `|U|^{1/p}` times the normalized one. -/
theorem eLpNorm_restrict_eq_rpow_mul {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hUt : volume U ≠ ⊤) (p : ℝ≥0∞) (f : Vec d → ℝ) :
    eLpNorm f p (volume.restrict U) = volume U ^ (1 / p).toReal * PDE.eLpMeanNormOn U p f := by
  rw [PDE.eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn (lt_top_iff_ne_top.2 hUt), ← mul_assoc,
    ← ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg, ENNReal.mul_inv_cancel hU0 hUt,
    ENNReal.one_rpow, one_mul]
  rfl

/-- The triangle inequality for the normalized `L²(U)` norm of vector fields. -/
theorem vectorRms_le_sub_add {U : Set (Vec d)} (hU0 : volume U ≠ 0) (hUt : volume U ≠ ⊤)
    {G H : Vec d → Vec d} (hG : ∀ i, MemLp (fun x => G x i) 2 (volume.restrict U))
    (hH : ∀ i, MemLp (fun x => H x i) 2 (volume.restrict U)) :
    vectorRms volume U G ≤ vectorRms volume U (fun x => G x - H x) + vectorRms volume U H := by
  have hGH : ∀ i, MemLp (fun x => (G x - H x) i) 2 (volume.restrict U) := fun i =>
    (hG i).sub (hH i)
  have e : ∀ K : Vec d → Vec d, (∀ i, MemLp (fun x => K x i) 2 (volume.restrict U)) →
      vectorRms volume U K =
        ((volume U).toReal ^ (1 / 2 : ℝ))⁻¹ * l2 U (fun x => euclideanNorm (K x)) :=
    fun K hK => by
      rw [← toReal_eLpMeanNormOn_two_eq hUt, eLpMeanNormOn_two_euclideanNorm_eq hU0 hK,
        ENNReal.toReal_ofReal (show 0 ≤ vectorRms volume U K from Real.sqrt_nonneg _)]
  rw [e _ hG, e _ hGH, e _ hH, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Real.rpow_nonneg ENNReal.toReal_nonneg _))
  have m1 := memLp_euclideanNorm_of_coord hGH
  have m2 := memLp_euclideanNorm_of_coord hH
  unfold l2
  rw [← ENNReal.toReal_add m1.eLpNorm_ne_top m2.eLpNorm_ne_top]
  refine ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨m1.eLpNorm_ne_top, m2.eLpNorm_ne_top⟩) ?_
  have hn : ∀ v : Vec d, 0 ≤ euclideanNorm v := fun v => Real.sqrt_nonneg _
  have hm1 : AEStronglyMeasurable (fun x => euclideanNorm (G x)) (volume.restrict U) :=
    (memLp_euclideanNorm_of_coord hG).aestronglyMeasurable
  have hle1 : eLpNorm (fun x => euclideanNorm (G x)) 2 (volume.restrict U) ≤
      eLpNorm (fun x => euclideanNorm (G x - H x) + euclideanNorm (H x)) 2 (volume.restrict U) := by
    refine eLpNorm_mono hm1 fun x => ?_
    have := euclideanNorm_add_le' (G x - H x) (H x)
    rw [sub_add_cancel] at this
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hn _),
      abs_of_nonneg (add_nonneg (hn _) (hn _))]
    exact this
  have hle2 : eLpNorm (fun x => euclideanNorm (G x - H x) + euclideanNorm (H x)) 2
      (volume.restrict U) ≤ eLpNorm (fun x => euclideanNorm (G x - H x)) 2 (volume.restrict U) +
        eLpNorm (fun x => euclideanNorm (H x)) 2 (volume.restrict U) :=
    eLpNorm_add_le (f := fun x => euclideanNorm (G x - H x)) (g := fun x => euclideanNorm (H x))
      one_le_two
  exact hle1.trans hle2

/-- `‖c f‖_{W̲^{-2,q}(U)} ≤ |c| ‖f‖_{W̲^{-2,q}(U)}`. -/
theorem negativeSobolevTwoNorm_const_mul_le (q : ℝ≥0∞) (U : Set (Vec d)) (c : ℝ)
    (f : Vec d → ℝ) :
    negativeSobolevTwoNorm q U (fun x => c * f x) ≤
      ENNReal.ofReal |c| * negativeSobolevTwoNorm q U f := by
  refine iSup_le fun ψ => ?_
  have e : ⨍ x in U, c * f x * ψ.1 x ∂volume = c * ⨍ x in U, f x * ψ.1 x ∂volume := by
    rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul]
    have h : ∫ x in U, c * f x * ψ.1 x ∂volume = c * ∫ x in U, f x * ψ.1 x ∂volume := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    rw [h]
    ring
  show ENNReal.ofReal |⨍ x in U, c * f x * ψ.1 x ∂volume| ≤ _
  rw [e, abs_mul, ENNReal.ofReal_mul (abs_nonneg c)]
  exact mul_le_mul_right (le_iSup (fun ψ : {ψ : Vec d → ℝ // IsSpatialTest U ψ ∧
    sobolevTwoTestNorm q.conjExponent U ψ ≤ 1} =>
      ENNReal.ofReal |⨍ x in U, f x * ψ.1 x ∂volume|) ψ) _

/-- **The bound of `K₁ + M ∑_j ‖Φ_j‖_{L²(U)}`** from the bounds of its terms. -/
theorem stepOneConstant_add_le {U V : Set (Vec d)} (b : CoefficientField d Λ) (A : Mat d)
    (η : Vec d → ℝ) (g : Vec d → Vec d) (G Φ : Fin d → Vec d → ℝ) {M : ℝ}
    (N : Fin d → Fin d → ℝ) {X t s : ℝ} (hM : 0 ≤ M) (ht0 : 0 ≤ t)
    (ht : t = (volume V).toReal ^ (1 / 2 : ℝ))
    (hBL : ∀ k, l2 U (fun x => ((1 - η x) • ((b x).mulVec (g x) - A.mulVec (g x))) k) ≤ X)
    (hT2 : ∀ j k, l2 U (fun x => (b x).mulVec (Φ j x • gradient (G j) x) k) ≤
      Λ * (d * M) * (t * s))
    (hN : ∀ j i, N j i ≤ s) (hΦ : ∀ j, l2 U (Φ j) ≤ t * s) :
    stepOneConstant U V b A η g G Φ M N + M * ∑ j, l2 U (Φ j) ≤
      d * X + M * t * s * (d * d * (Λ * d) + (1 + d) * (d * d) + d) := by
  have h1 := sum_fin_le_mul hBL
  have h2 := sum_fin_le_mul fun j => sum_fin_le_mul fun k => hT2 j k
  have h3 : (volume V).toReal ^ (1 / 2 : ℝ) * ((1 + d) * M) * ∑ j, ∑ i, N j i ≤
      t * ((1 + d) * M) * (d * (d * s)) := by
    rw [← ht]
    exact mul_le_mul_of_nonneg_left (sum_fin_le_mul fun j => sum_fin_le_mul fun i => hN j i)
      (mul_nonneg ht0 (mul_nonneg (by positivity) hM))
  have h4 := mul_le_mul_of_nonneg_left (sum_fin_le_mul hΦ) hM
  unfold stepOneConstant
  calc _ ≤ d * X + d * (d * (Λ * (d * M) * (t * s))) + t * ((1 + d) * M) * (d * (d * s)) +
        M * (d * (t * s)) := add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = _ := by ring

/-- **The rescaled finite-volume correctors** on `V = ε □_m`, `m = m(ε)`, and `U ⊆ □_0`:
`U ⊆ V`, `1 ≤ |V| ≤ 3^d`, `ε φ_j(·/ε) ∈ H¹(U)` with gradient `∇φ_j(·/ε)`, the fluxes
`a(·/ε)(e_j + ∇φ_j(·/ε))` are weakly divergence free in `U`, `E'(ε) < ∞`, the `H̲⁻¹(V)` norms of
the components of the flux errors are at most `E'(ε)^{1/2}` and
`‖ε φ_j(·/ε)‖_{L²(U)} ≤ |V|^{1/2} E'(ε)^{1/2}`. -/
theorem rescaledCorrector_facts (a : CoefficientField d Λ) (A : Mat d) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) {φ : Fin d → Vec d → ℝ} {Dφ : Fin d → Vec d → Vec d}
    (hmin : ∀ k, IsDirichletMinimizer a (triadicCube d (triadicScale ε)) (unitVector k) (φ k)
      (Dφ k)) {U V : Set (Vec d)} (hU : U ⊆ triadicCube d 0)
    (hVdef : V = ε • triadicCube d (triadicScale ε)) :
    twoScaleDeviation a A ε φ Dφ ≠ ⊤ ∧ U ⊆ V ∧ 1 ≤ (volume V).toReal ∧ volume V ≠ ⊤ ∧
      (volume V).toReal ^ (1 / 2 : ℝ) ≤ ((3 : ℝ) ^ d) ^ (1 / 2 : ℝ) ∧
      (∀ j, MemLp (fun x => ε * φ j (ε⁻¹ • x)) 2 (volume.restrict U)) ∧
      (∀ j i, MemLp (fun x => Dφ j (ε⁻¹ • x) i) 2 (volume.restrict U)) ∧
      (∀ j, HasWeakGradient U (fun x => ε * φ j (ε⁻¹ • x)) (fun x => Dφ j (ε⁻¹ • x))) ∧
      (∀ j, HasWeakDivergence U (fun x => (a (ε⁻¹ • x)).mulVec (unitVector j + Dφ j (ε⁻¹ • x)))
        (fun _ => 0)) ∧
      (∀ j i, negativeSobolevOneNorm 2 V (fun x => ((a (ε⁻¹ • x)).mulVec
        (unitVector j + Dφ j (ε⁻¹ • x)) - A.mulVec (unitVector j)) i) 0 ≠ ⊤) ∧
      (∀ j i, (negativeSobolevOneNorm 2 V (fun x => ((a (ε⁻¹ • x)).mulVec
        (unitVector j + Dφ j (ε⁻¹ • x)) - A.mulVec (unitVector j)) i) 0).toReal ≤
          (twoScaleDeviation a A ε φ Dφ ^ (1 / 2 : ℝ)).toReal) ∧
      (∀ j, l2 U (fun x => ε * φ j (ε⁻¹ • x)) ≤
        (volume V).toReal ^ (1 / 2 : ℝ) * (twoScaleDeviation a A ε φ Dφ ^ (1 / 2 : ℝ)).toReal) := by
  have hεne : ε ≠ 0 := hε.ne'
  obtain ⟨hV0sub, hV1, hV3⟩ := volume_smul_triadicCube_bounds hε hε1
  rw [← hVdef] at hV0sub hV1 hV3
  have hUV : U ⊆ V := hU.trans hV0sub
  have hVt : volume V ≠ ⊤ := fun h => by rw [h, ENNReal.toReal_top] at hV1; linarith
  have hV0 : volume V ≠ 0 := fun h => by rw [h, ENNReal.toReal_zero] at hV1; linarith
  have hVm : MeasurableSet V := by
    rw [hVdef]; exact ((isOpen_triadicCube _).smul₀ hεne).measurableSet
  have hVmap : ∀ x ∈ V, ε⁻¹ • x ∈ triadicCube d (triadicScale ε) := fun x hx => by
    rw [hVdef] at hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.1 hx
    rwa [inv_smul_smul₀ hεne]
  have : IsFiniteMeasure (volume.restrict V) := isFiniteMeasure_restrict.mpr hVt
  have hUVμ : volume.restrict U ≤ volume.restrict V := Measure.restrict_mono hUV le_rfl
  have hh1 := fun k => h1_rescaledCorrector (hmin k).1 hε hVm hVt hVmap
  have hfl := fun k => hasWeakDivergence_rescaledCorrector (hmin k) hε hVm hVt hVmap
  have hDe : ∀ j, MemLp (fun x => unitVector j + Dφ j (ε⁻¹ • x)) 2 (volume.restrict V) :=
    fun j => by
      have h1 : MemLp (fun x => Dφ j (ε⁻¹ • x)) 2 (volume.restrict V) :=
        memLp_pi_iff.2 (hh1 j).2.1
      have h0 : MemLp (fun _ : Vec d => unitVector (d := d) j) 2 (volume.restrict V) :=
        memLp_const _
      exact h0.add h1
  have hflL2 : ∀ j i, MemLp (fun x => ((a (ε⁻¹ • x)).mulVec (unitVector j + Dφ j (ε⁻¹ • x)) -
      A.mulVec (unitVector j)) i) 2 (volume.restrict V) := fun j i =>
    (memLp_coefficient_mulVec_apply (rescaledCoefficientField a hεne) (hDe j) i).sub
      (memLp_const (A.mulVec (unitVector j) i))
  have hne : ∀ j i, negativeSobolevOneNorm 2 V (fun x => ((a (ε⁻¹ • x)).mulVec
      (unitVector j + Dφ j (ε⁻¹ • x)) - A.mulVec (unitVector j)) i) 0 ≠ ⊤ := fun j i =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (negativeSobolevOneNorm_two_le hV0 hVt (hflL2 j i))
  have hEne : twoScaleDeviation a A ε φ Dφ ≠ ⊤ := by
    unfold twoScaleDeviation vectorNegativeSobolevOneNorm
    rw [← hVdef]
    exact ENNReal.sum_ne_top.2 fun k _ => ENNReal.pow_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.ofReal_ne_top, ENNReal.sum_ne_top.2 fun i _ => hne k i⟩)
  have hEs : twoScaleDeviation a A ε φ Dφ ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hEne
  have hs1 : ∀ k, scalarRms volume V (fun x => ε * φ k (ε⁻¹ • x)) ≤
      (twoScaleDeviation a A ε φ Dφ ^ (1 / 2 : ℝ)).toReal := fun k => by
    have h := (twoScaleDeviation_terms_le a A ε φ Dφ k).1
    rw [← hVdef] at h
    have h' := ENNReal.toReal_mono hEs h
    rwa [ENNReal.toReal_ofReal (show 0 ≤ scalarRms volume V (fun x => ε * φ k (ε⁻¹ • x)) from
      Real.sqrt_nonneg _)] at h'
  have ht0 : 0 < (volume V).toReal ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  refine ⟨hEne, hUV, hV1, hVt, Real.rpow_le_rpow ENNReal.toReal_nonneg hV3 (by norm_num),
    fun j => (hh1 j).1.mono_measure hUVμ, fun j i => ((hh1 j).2.1 i).mono_measure hUVμ,
    fun j => HasWeakGradient.mono hUV (hh1 j).2.2, fun j => hasWeakDivergence_mono hUV (hfl j),
    hne, fun j i => ?_, fun j => ?_⟩
  · have h := (twoScaleDeviation_terms_le a A ε φ Dφ j).2 i
    rw [← hVdef] at h
    exact ENNReal.toReal_mono hEs h
  · have h1 : l2 U (fun x => ε * φ j (ε⁻¹ • x)) ≤ l2 V (fun x => ε * φ j (ε⁻¹ • x)) :=
      ENNReal.toReal_mono (hh1 j).1.eLpNorm_ne_top (eLpNorm_mono_measure _ hUVμ)
    have h2 : l2 V (fun x => ε * φ j (ε⁻¹ • x)) = (volume V).toReal ^ (1 / 2 : ℝ) *
        scalarRms volume V (fun x => ε * φ j (ε⁻¹ • x)) := by
      rw [scalarRms_eq_inv_mul_l2 hVt hV0 (hh1 j).1, ← mul_assoc, mul_inv_cancel₀ ht0.ne',
        one_mul]
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (hs1 j) ht0.le)

set_option maxHeartbeats 400000 in
/-- **The estimates of the proof of Theorem 1.17** in real form: with
`F_δ = ‖∇f‖_{L̲^{2+δ}(U)}` and `Y = F_δ (r^β + r^{-2-d/2} E'(ε)^{1/2})`, the three terms of (1.59)
are at most `C Y`, `E'(ε)` and `F_δ` are finite, `u^ε, u ∈ H¹(U)` and
`‖∇u^ε‖_{L̲²(U)} + ‖∇u‖_{L̲²(U)} ≤ 2 C_e F_δ`. -/
theorem exists_twoScale_estimate (hd : 2 ≤ d) (hΛ : 1 ≤ Λ) {U : Set (Vec d)} (hUo : IsOpen U)
    (hUc : Convex ℝ U) (hUne : U.Nonempty) (hU : U ⊆ triadicCube d 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ β C Ce : ℝ, 0 < β ∧ 0 ≤ C ∧ 0 ≤ Ce ∧
      ∀ (a : CoefficientField d Λ) (A : Mat d), A.transpose = A →
      (∀ ξ, euclideanSq ξ ≤ dot ξ (A.mulVec ξ)) → (∀ ξ, dot ξ (A.mulVec ξ) ≤ Λ * euclideanSq ξ) →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ (φ : Fin d → Vec d → ℝ) (Dφ : Fin d → Vec d → Vec d),
      (∀ k, IsDirichletMinimizer a (triadicCube d (triadicScale ε)) (unitVector k) (φ k) (Dφ k)) →
      ∀ (f : Vec d → ℝ) (F : Vec d → Vec d), IsW1p U (ENNReal.ofReal (2 + δ)) f F →
      ∀ (uε u : Vec d → ℝ) (gε g : Vec d → Vec d),
      H01 U (fun x => uε x - f x) (fun x => gε x - F x) →
      HasWeakDivergence U (fun x => (a (ε⁻¹ • x)).mulVec (gε x)) (fun _ => 0) →
      H01 U (fun x => u x - f x) (fun x => g x - F x) →
      HasWeakDivergence U (fun x => A.mulVec (g x)) (fun _ => 0) →
      ∀ r : ℝ, 0 < r → r < 1 →
      twoScaleDeviation a A ε φ Dφ ≠ ⊤ ∧
      PDE.eLpMeanNormOn U (ENNReal.ofReal (2 + δ)) (fun x => euclideanNorm (F x)) ≠ ⊤ ∧
      H1 U uε gε ∧ H1 U u g ∧
      scalarRms volume U (fun x => uε x - u x) ≤
        C * ((PDE.eLpMeanNormOn U (ENNReal.ofReal (2 + δ)) (fun x => euclideanNorm (F x))).toReal *
          (r ^ β + r ^ (-(2 + (d : ℝ) / 2)) *
            (twoScaleDeviation a A ε φ Dφ ^ (1 / 2 : ℝ)).toReal)) ∧
      vectorHatNegativeSobolevNorm U (fun x => gε x - g x) ≤
        ENNReal.ofReal (C *
          ((PDE.eLpMeanNormOn U (ENNReal.ofReal (2 + δ)) (fun x => euclideanNorm (F x))).toReal *
          (r ^ β + r ^ (-(2 + (d : ℝ) / 2)) *
            (twoScaleDeviation a A ε φ Dφ ^ (1 / 2 : ℝ)).toReal))) ∧
      vectorHatNegativeSobolevNorm U (fun x => (a (ε⁻¹ • x)).mulVec (gε x) - A.mulVec (g x)) ≤
        ENNReal.ofReal (C *
          ((PDE.eLpMeanNormOn U (ENNReal.ofReal (2 + δ)) (fun x => euclideanNorm (F x))).toReal *
          (r ^ β + r ^ (-(2 + (d : ℝ) / 2)) *
            (twoScaleDeviation a A ε φ Dφ ^ (1 / 2 : ℝ)).toReal))) ∧
      vectorRms volume U gε ≤
        Ce * (PDE.eLpMeanNormOn U (ENNReal.ofReal (2 + δ)) (fun x => euclideanNorm (F x))).toReal ∧
      vectorRms volume U g ≤
        Ce * (PDE.eLpMeanNormOn U (ENNReal.ofReal (2 + δ)) (fun x => euclideanNorm (F x))).toReal := by
  have hd0 : 0 < d := by omega
  have : NeZero d := ⟨hd0.ne'⟩
  have hUcube := subset_cube_of_subset_triadicCube_zero hU
  have hUR := subset_ball_of_subset_triadicCube_zero hd0 hU
  have hUb := isBounded_of_subset_ball hUR
  have hUdom := isOpenBoundedConvexDomain_of_isBounded hUo hUb hUc
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hUne).ne'
  have hUt : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUt
  have : IsProbabilityMeasure (PDE.normalizedVolumeOn U) :=
    PDE.isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top (pos_iff_ne_zero.2 hU0)
      (lt_top_iff_ne_top.2 hUt)
  obtain ⟨x₀, hx₀⟩ := hUne
  obtain ⟨ρ, hρ, hball⟩ := exists_ball_subset_of_mem hUo hx₀
  obtain ⟨δ₀, CM, hδ₀, hCM, hMey⟩ :=
    meyers_constantCoefficient_of_convex hd hΛ hUo hUc hρ hball hUR
  obtain ⟨K, hK, hmult⟩ := exists_multipliers hd0 hΛ hUo hUb hUc hρ (fun y hy => hball hy)
  obtain ⟨c, hc, hsteps⟩ := exists_twoScale_steps hΛ hUdom hUb hU0 hUcube
  obtain ⟨C8, hC8, h8⟩ := lemma_C_8_energy hΛ hUo hUb hU0
  have hΛ0 : 0 ≤ Λ := by linarith
  have hsr : ∀ (W : Set (Vec d)) (h : Vec d → ℝ), 0 ≤ scalarRms volume W h := fun _ _ =>
    Real.sqrt_nonneg _
  have hvr : ∀ (W : Set (Vec d)) (G : Vec d → Vec d), 0 ≤ vectorRms volume W G := fun _ _ =>
    Real.sqrt_nonneg _
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = min (2 + δ₀) (2 + δ) := ⟨_, rfl⟩
  have hq2 : 2 < q := by rw [hq]; exact lt_min (by linarith) (by linarith)
  have hqp : q ≤ 2 + δ := by rw [hq]; exact min_le_right _ _
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = 1 / 2 - 1 / q := ⟨_, rfl⟩
  have hβ0 : 0 < β := by
    have : 1 / q < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) hq2
    rw [hβ]; linarith
  have hvU : 0 < (volume U).toReal := ENNReal.toReal_pos hU0 hUt
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (volume U ^ (1 / ENNReal.ofReal q).toReal).toReal := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; exact ENNReal.toReal_nonneg
  obtain ⟨C1, hC1⟩ : ∃ C1 : ℝ,
      C1 = d * (2 * Λ * (P * CM) * (d * (volume U).toReal) ^ β) := ⟨_, rfl⟩
  have hC10 : 0 ≤ C1 := by
    rw [hC1]
    exact mul_nonneg (Nat.cast_nonneg d) (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hΛ0)
      (mul_nonneg hP0 hCM)) (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg d) hvU.le) β))
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ((3 : ℝ) ^ d) ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  obtain ⟨C2, hC2⟩ : ∃ C2 : ℝ, C2 = d * d * (Λ * d) + (1 + d) * (d * d) + d := ⟨_, rfl⟩
  have hd' : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hC20 : 0 ≤ C2 := by
    rw [hC2]
    exact add_nonneg (add_nonneg (mul_nonneg (mul_nonneg hd' hd') (mul_nonneg hΛ0 hd'))
      (mul_nonneg (by positivity) (mul_nonneg hd' hd'))) hd'
  obtain ⟨KC, hKC⟩ : ∃ KC : ℝ, KC = K * Real.sqrt (volume U).toReal * CM * T * C2 := ⟨_, rfl⟩
  have hKC0 : 0 ≤ KC := by
    rw [hKC, hT]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hK (Real.sqrt_nonneg _)) hCM)
      (Real.rpow_nonneg (by positivity) _)) hC20
  have hCe0 : 0 ≤ C8 * Λ + 1 := add_nonneg (mul_nonneg hC8.le hΛ0) zero_le_one
  refine ⟨β, c * (C1 + KC), CM + (C8 * Λ + 1), hβ0, mul_nonneg hc (add_nonneg hC10 hKC0),
    add_nonneg hCM hCe0,
    fun a A hAt hA1 hA2 ε hε hε1 φ Dφ hmin f F hf uε u gε g huε hdivε hu hdiv r hr0 hr1 => ?_⟩
  have hεne : ε ≠ 0 := hε.ne'
  -- the boundary datum
  have h2le : (2 : ℝ≥0∞) ≤ ENNReal.ofReal (2 + δ) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have h2q : (2 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
    exact ENNReal.ofReal_le_ofReal hq2.le
  have hFi : ∀ i, MemLp (fun x => F x i) (ENNReal.ofReal (2 + δ)) (volume.restrict U) :=
    fun i => hf.2.1.eval i
  have hFp := eLpMeanNormOn_ne_top_of_memLp hU0 hUt (memLp_euclideanNorm_of_coord hFi)
  have hF2 : MemLp F 2 (volume.restrict U) := hf.2.1.mono_exponent h2le
  have hF2i : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict U) := fun i => hF2.eval i
  have hf2 : MemLp f 2 (volume.restrict U) := hf.1.mono_exponent h2le
  obtain ⟨Fr, hFr⟩ : ∃ Fr : ℝ, Fr = (PDE.eLpMeanNormOn U (ENNReal.ofReal (2 + δ))
      (fun x => euclideanNorm (F x))).toReal := ⟨_, rfl⟩
  rw [← hFr]
  have hFr0 : 0 ≤ Fr := by rw [hFr]; exact ENNReal.toReal_nonneg
  -- the solutions
  have hu2 : MemLp u 2 (volume.restrict U) := by
    have e : (fun x => u x - f x) + f = u := by funext x; simp
    rw [← e]; exact hu.1.add hf2
  have huε2 : MemLp uε 2 (volume.restrict U) := by
    have e : (fun x => uε x - f x) + f = uε := by funext x; simp
    rw [← e]; exact huε.1.add hf2
  have hg2 : MemLp g 2 (volume.restrict U) := by
    have e : (fun x => g x - F x) + F = g := by funext x; simp
    rw [← e]; exact hu.2.1.add hF2
  have hgε2 : MemLp gε 2 (volume.restrict U) := by
    have e : (fun x => gε x - F x) + F = gε := by funext x; simp
    rw [← e]; exact huε.2.1.add hF2
  have hug : HasWeakGradient U u g := by
    simpa only [sub_add_cancel] using hasWeakGradient_add hu.2.2.1 hf.2.2
  have hugε : HasWeakGradient U uε gε := by
    simpa only [sub_add_cancel] using hasWeakGradient_add huε.2.2.1 hf.2.2
  have hgi : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U) := fun i => hg2.eval i
  have hgεi : ∀ i, MemLp (fun x => gε x i) 2 (volume.restrict U) := fun i => hgε2.eval i
  -- the Meyers estimate
  have hMg := hMey (2 + δ) (by linarith) A hAt hA1 hA2 u f g F hf hu hdiv
  rw [← hq] at hMg
  have hFq : PDE.eLpMeanNormOn U (ENNReal.ofReal q) (fun x => euclideanNorm (F x)) ≤
      PDE.eLpMeanNormOn U (ENNReal.ofReal (2 + δ)) (fun x => euclideanNorm (F x)) :=
    eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hqp)
  have hFCM : ENNReal.ofReal CM *
      PDE.eLpMeanNormOn U (ENNReal.ofReal (2 + δ)) (fun x => euclideanNorm (F x)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFp
  have hgq : PDE.eLpMeanNormOn U (ENNReal.ofReal q) (fun x => euclideanNorm (g x)) ≤
      ENNReal.ofReal CM *
        PDE.eLpMeanNormOn U (ENNReal.ofReal (2 + δ)) (fun x => euclideanNorm (F x)) :=
    hMg.trans (mul_le_mul_right hFq _)
  have hgq_ne := ne_top_of_le_ne_top hFCM hgq
  have hgqr : (PDE.eLpMeanNormOn U (ENNReal.ofReal q) (fun x => euclideanNorm (g x))).toReal ≤
      CM * Fr := by
    have h := ENNReal.toReal_mono hFCM hgq
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCM, ← hFr] at h
  have hgrms : vectorRms volume U g ≤ CM * Fr := by
    have hle : PDE.eLpMeanNormOn U 2 (fun x => euclideanNorm (g x)) ≤
        PDE.eLpMeanNormOn U (ENNReal.ofReal q) (fun x => euclideanNorm (g x)) :=
      eLpNorm_le_eLpNorm_of_exponent_le h2q
    have h := ENNReal.toReal_mono hgq_ne hle
    rw [eLpMeanNormOn_two_euclideanNorm_eq hU0 hgi, ENNReal.toReal_ofReal (hvr _ _)] at h
    exact h.trans hgqr
  have hFrms : vectorRms volume U F ≤ Fr := by
    have hle : PDE.eLpMeanNormOn U 2 (fun x => euclideanNorm (F x)) ≤
        PDE.eLpMeanNormOn U (ENNReal.ofReal (2 + δ)) (fun x => euclideanNorm (F x)) :=
      eLpNorm_le_eLpNorm_of_exponent_le h2le
    have h := ENNReal.toReal_mono hFp hle
    rwa [eLpMeanNormOn_two_euclideanNorm_eq hU0 hF2i, ENNReal.toReal_ofReal (hvr _ _), ← hFr] at h
  have hint : Real.sqrt (∫ x in U, euclideanSq (g x)) ≤
      Real.sqrt (volume U).toReal * (CM * Fr) := by
    have e : Real.sqrt (∫ x in U, euclideanSq (g x)) =
        Real.sqrt (volume U).toReal * vectorRms volume U g := by
      rw [vectorRms, setAverage_eq, smul_eq_mul, measureReal_def, ← Real.sqrt_mul hvU.le,
        ← mul_assoc, mul_inv_cancel₀ hvU.ne', one_mul]
    rw [e]
    exact mul_le_mul_of_nonneg_left hgrms (Real.sqrt_nonneg _)
  -- the energy estimate for `u^ε`
  have hbF : ∀ i, MemLp (fun x => (rescaledCoefficientField a hεne x).mulVec (F x) i) 2
      (volume.restrict U) := fun i => memLp_coefficient_mulVec_apply _ hF2 i
  have hE8 := h8 (rescaledCoefficientField a hεne) (fun x => uε x - f x) (fun x => gε x - F x)
    (fun _ => 0) (fun x => (rescaledCoefficientField a hεne x).mulVec (F x)) huε (memLp_const 0)
    hbF (by
      convert hdivε using 2 <;> simp [Matrix.mulVec_sub, rescaledCoefficientField_apply])
  have hgεF : vectorRms volume U (fun x => gε x - F x) ≤ C8 * (Λ * Fr) := by
    have hb : negativeSobolevOneNorm 2 U (fun _ => 0)
        (fun x => (rescaledCoefficientField a hεne x).mulVec (F x)) ≤ ENNReal.ofReal (Λ * Fr) := by
      refine (negativeSobolevOneNorm_two_zero_le hU0 hbF).trans ?_
      rw [eLpMeanNormOn_two_euclideanNorm_eq hU0 hbF]
      exact ENNReal.ofReal_le_ofReal ((vectorRms_mulVec_le hΛ0 _ hF2i hUt).trans
        (mul_le_mul_of_nonneg_left hFrms hΛ0))
    have h := hE8.trans (mul_le_mul_right hb _)
    rwa [← ENNReal.ofReal_mul hC8.le, ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg hC8.le (mul_nonneg hΛ0 hFr0))] at h
  have hgεrms : vectorRms volume U gε ≤ (CM + (C8 * Λ + 1)) * Fr := by
    calc vectorRms volume U gε ≤ vectorRms volume U (fun x => gε x - F x) + vectorRms volume U F :=
          vectorRms_le_sub_add hU0 hUt hgεi hF2i
      _ ≤ C8 * (Λ * Fr) + Fr := add_le_add hgεF hFrms
      _ ≤ (CM + (C8 * Λ + 1)) * Fr := by
          rw [show (CM + (C8 * Λ + 1)) * Fr = CM * Fr + (C8 * (Λ * Fr) + Fr) by ring]
          exact le_add_of_nonneg_left (mul_nonneg hCM hFr0)
  have hgrms' : vectorRms volume U g ≤ (CM + (C8 * Λ + 1)) * Fr :=
    hgrms.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCe0) hFr0)
  -- the multipliers
  obtain ⟨η, G, hηc, hη01, hηvol, hGs, hGc, hGU, hGη, hG0, hG1, hG2⟩ :=
    hmult A hAt hA1 hA2 u g hu2 hg2 hug hdiv r hr0 hr1
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = K * r⁻¹ ^ 2 * Real.sqrt (r⁻¹ ^ d) *
      Real.sqrt (∫ x in U, euclideanSq (g x)) := ⟨_, rfl⟩
  rw [← hM] at hG0 hG1 hG2
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact mul_nonneg (mul_nonneg (mul_nonneg hK (pow_nonneg (inv_nonneg.2 hr0.le) 2))
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hR0 : 0 ≤ r ^ (-(2 + (d : ℝ) / 2)) := Real.rpow_nonneg hr0.le _
  have hrβ0 : 0 ≤ r ^ β := Real.rpow_nonneg hr0.le _
  have hMle : M ≤ K * r ^ (-(2 + (d : ℝ) / 2)) * (Real.sqrt (volume U).toReal * (CM * Fr)) := by
    have e : K * r⁻¹ ^ 2 * Real.sqrt (r⁻¹ ^ d) = K * r ^ (-(2 + (d : ℝ) / 2)) := by
      rw [mul_assoc, inv_sq_mul_sqrt_inv_pow hr0 d]
    rw [hM, e]
    exact mul_le_mul_of_nonneg_left hint (mul_nonneg hK hR0)
  -- the cube `V = ε □_m` and the rescaled correctors
  obtain ⟨V, hVdef⟩ : ∃ V : Set (Vec d), V = ε • triadicCube d (triadicScale ε) := ⟨_, rfl⟩
  obtain ⟨hEne, hUV, hV1, hVt, htT, hΦU, hDΦU, hΦw, hflU, hne, hNs, hΦl2⟩ :=
    rescaledCorrector_facts a A hε hε1 hmin hU hVdef
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (twoScaleDeviation a A ε φ Dφ ^ (1 / 2 : ℝ)).toReal :=
    ⟨_, rfl⟩
  rw [← hs] at hNs hΦl2
  rw [← hs]
  have hs0 : 0 ≤ s := by rw [hs]; exact ENNReal.toReal_nonneg
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (volume V).toReal ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  rw [← ht] at htT hΦl2
  rw [← hT] at htT
  have ht0 : 0 ≤ t := by rw [ht]; exact Real.rpow_nonneg ENNReal.toReal_nonneg _
  -- Steps 2–4
  have hdiff : H01 U (fun x => uε x - u x) (fun x => gε x - g x) :=
    (huε.sub hu).congr (fun x => sub_sub_sub_cancel_right _ _ _)
      (fun x => sub_sub_sub_cancel_right _ _ _)
  have hS := hsteps V hUV hV1 hVt (rescaledCoefficientField a hεne) A u uε η g gε G
    (fun j x => ε * φ j (ε⁻¹ • x)) (fun j x => Dφ j (ε⁻¹ • x)) M
    (fun j i => (negativeSobolevOneNorm 2 V (fun x => ((a (ε⁻¹ • x)).mulVec
      (unitVector j + Dφ j (ε⁻¹ • x)) - A.mulVec (unitVector j)) i) 0).toReal)
    hgi hdiv hdiff hdivε hηc hη01 hGs hGc hGU hGη hΦU hDΦU
    hΦw hflU
    hM0 hG0 hG1 hG2 (fun _ _ => ENNReal.toReal_nonneg)
    (fun j i => (ENNReal.ofReal_toReal (hne j i)).ge)
  -- the boundary layer term
  have hBL : ∀ k, l2 U (fun x => ((1 - η x) • ((rescaledCoefficientField a hεne x).mulVec (g x) -
      A.mulVec (g x))) k) ≤
        2 * Λ * (P * (CM * Fr)) * ((d * (volume U).toReal) ^ β * r ^ β) := fun k => by
    have hgqm : MemLp (fun x => euclideanNorm (g x)) (ENNReal.ofReal q) (volume.restrict U) :=
      memLp_of_eLpMeanNormOn_ne_top hU0 hUt hgq_ne
    have h := l2_boundaryLayer_le hΛ hUt (rescaledCoefficientField a hεne) hAt
      (fun ξ => (euclideanSq_nonneg_of_vec ξ).trans (hA1 ξ)) hA2 hηc hη01 hgi h2q hgqm k
    rw [ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ q), ← hβ] at h
    refine h.trans (mul_le_mul (mul_le_mul_of_nonneg_left ?_ (mul_nonneg zero_le_two hΛ0)) ?_
      (Real.rpow_nonneg measureReal_nonneg _)
      (mul_nonneg (mul_nonneg zero_le_two hΛ0) (mul_nonneg hP0 (mul_nonneg hCM hFr0))))
    · rw [eLpNorm_restrict_eq_rpow_mul hU0 hUt, ENNReal.toReal_mul, ← hP]
      exact mul_le_mul_of_nonneg_left hgqr hP0
    · rw [← Real.mul_rpow (mul_nonneg (Nat.cast_nonneg d) hvU.le) hr0.le]
      refine Real.rpow_le_rpow measureReal_nonneg (hηvol.trans (le_of_eq ?_)) hβ0.le
      rw [measureReal_def]
      ring
  -- the corrector terms
  have hT2 : ∀ j k, l2 U (fun x => (rescaledCoefficientField a hεne x).mulVec
      ((ε * φ j (ε⁻¹ • x)) • gradient (G j) x) k) ≤ Λ * (d * M) * (t * s) := fun j k => by
    have hΦG : ∀ i, MemLp (fun x => ((ε * φ j (ε⁻¹ • x)) • gradient (G j) x) i) 2
        (volume.restrict U) := fun i => by
      have h := memLp_continuous_mul (continuous_gradient_apply (hGs j) i)
        (hasCompactSupport_gradient_apply (hGc j) i) (hΦU j)
      refine h.ae_eq (Eventually.of_forall fun x => ?_)
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    have hΦG' : MemLp (fun x => (ε * φ j (ε⁻¹ • x)) • gradient (G j) x) 2 (volume.restrict U) :=
      memLp_pi_iff.2 hΦG
    have hm := (memLp_coefficient_mulVec_apply (rescaledCoefficientField a hεne) hΦG'
      k).aestronglyMeasurable
    have hpt : ∀ x, ‖(rescaledCoefficientField a hεne x).mulVec
        ((ε * φ j (ε⁻¹ • x)) • gradient (G j) x) k‖ ≤
          (Λ * (d * M)) * ‖ε * φ j (ε⁻¹ • x)‖ := fun x => by
      have hE : euclideanNorm (gradient (G j) x) ≤ d * M := by
        refine (euclideanNorm_le_sum_abs_apply _).trans ?_
        calc ∑ i, |gradient (G j) x i| ≤ ∑ _i : Fin d, M :=
              Finset.sum_le_sum fun i _ => hG1 j i x
          _ = d * M := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      refine (abs_coord_le_euclideanNorm _ k).trans
        ((euclideanNorm_coefficient_mulVec_le _ hΛ0 x _).trans ?_)
      calc Λ * euclideanNorm ((ε * φ j (ε⁻¹ • x)) • gradient (G j) x) =
            Λ * euclideanNorm (gradient (G j) x) * |ε * φ j (ε⁻¹ • x)| := by
            rw [euclideanNorm_smul]; ring
        _ ≤ Λ * (d * M) * |ε * φ j (ε⁻¹ • x)| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hΛ0) (abs_nonneg _)
    have hc0 : 0 ≤ Λ * (d * M) := mul_nonneg hΛ0 (mul_nonneg (Nat.cast_nonneg d) hM0)
    have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm (Eventually.of_forall hpt) 2
    have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (hΦU j).eLpNorm_ne_top) h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0] at h'
    exact h'.trans (mul_le_mul_of_nonneg_left (hΦl2 j) hc0)
  have hM' : M * t * s * C2 ≤ KC * (Fr * (r ^ (-(2 + (d : ℝ) / 2)) * s)) := by
    have hM'0 : 0 ≤ K * r ^ (-(2 + (d : ℝ) / 2)) * (Real.sqrt (volume U).toReal * (CM * Fr)) :=
      mul_nonneg (mul_nonneg hK hR0) (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hCM hFr0))
    calc M * t * s * C2 ≤ (K * r ^ (-(2 + (d : ℝ) / 2)) *
          (Real.sqrt (volume U).toReal * (CM * Fr))) * T * s * C2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul hMle htT ht0 hM'0) hs0) hC20
      _ = KC * (Fr * (r ^ (-(2 + (d : ℝ) / 2)) * s)) := by rw [hKC]; ring
  have hX : stepOneConstant U V (rescaledCoefficientField a hεne) A η g G
      (fun j x => ε * φ j (ε⁻¹ • x)) M (fun j i => (negativeSobolevOneNorm 2 V
        (fun x => ((a (ε⁻¹ • x)).mulVec (unitVector j + Dφ j (ε⁻¹ • x)) -
          A.mulVec (unitVector j)) i) 0).toReal) +
        M * ∑ j, l2 U ((fun j x => ε * φ j (ε⁻¹ • x)) j) ≤
      (C1 + KC) * (Fr * (r ^ β + r ^ (-(2 + (d : ℝ) / 2)) * s)) := by
    have e1 : d * (2 * Λ * (P * (CM * Fr)) * ((d * (volume U).toReal) ^ β * r ^ β)) +
        M * t * s * (d * d * (Λ * d) + (1 + d) * (d * d) + d) =
          C1 * Fr * r ^ β + M * t * s * C2 := by
      rw [hC1, hC2]; ring
    have h1 : 0 ≤ C1 * (Fr * (r ^ (-(2 + (d : ℝ) / 2)) * s)) :=
      mul_nonneg hC10 (mul_nonneg hFr0 (mul_nonneg hR0 hs0))
    have h2 : 0 ≤ KC * (Fr * r ^ β) := mul_nonneg hKC0 (mul_nonneg hFr0 hrβ0)
    calc _ ≤ _ := stepOneConstant_add_le (rescaledCoefficientField a hεne) A η g G
          (fun j x => ε * φ j (ε⁻¹ • x)) _ hM0 ht0 ht hBL hT2 hNs hΦl2
      _ = C1 * Fr * r ^ β + M * t * s * C2 := e1
      _ ≤ C1 * Fr * r ^ β + KC * (Fr * (r ^ (-(2 + (d : ℝ) / 2)) * s)) := add_le_add le_rfl hM'
      _ ≤ (C1 + KC) * (Fr * (r ^ β + r ^ (-(2 + (d : ℝ) / 2)) * s)) := by
          rw [show (C1 + KC) * (Fr * (r ^ β + r ^ (-(2 + (d : ℝ) / 2)) * s)) =
            C1 * Fr * r ^ β + KC * (Fr * (r ^ (-(2 + (d : ℝ) / 2)) * s)) +
              (C1 * (Fr * (r ^ (-(2 + (d : ℝ) / 2)) * s)) + KC * (Fr * r ^ β)) by ring]
          exact le_add_of_nonneg_right (add_nonneg h1 h2)
  have hcX := (mul_le_mul_of_nonneg_left hX hc).trans_eq (mul_assoc c (C1 + KC) _).symm
  obtain ⟨hS1, hS2, hS3⟩ := hS
  exact ⟨hEne, hFp, ⟨huε2, hgε2, hugε⟩, ⟨hu2, hg2, hug⟩, hS1.trans hcX,
    hS2.trans (ENNReal.ofReal_le_ofReal hcX), hS3.trans (ENNReal.ofReal_le_ofReal hcX),
    hgεrms, hgrms'⟩

set_option maxHeartbeats 400000 in
/-- **Theorem 1.17** for `d ≥ 2` and a bounded open convex domain `U ⊆ □_0`: for every `δ > 0`
there are `β > 0` and `C < ∞` such that, for every coefficient field `a`, every constant symmetric
matrix `ā` with `Id ≤ ā ≤ Λ Id`, `ε ∈ (0, 1]`, finite-volume correctors `φ_k` of (1.55) on
`□_{m(ε)}`, `f ∈ W^{1,2+δ}(U)` of gradient `∇f`, solutions `u^ε, u ∈ f + H¹₀(U)` of
`-∇·(a(·/ε)∇u^ε) = 0` and `-∇·(ā∇u) = 0` in `U` and `r ∈ (0, 1)`, (1.59) holds,
`‖u^ε - u‖_{L̲²(U)} + ‖∇u^ε - ∇u‖_{Ĥ̲⁻¹(U)} + ‖a(·/ε)∇u^ε - ā∇u‖_{Ĥ̲⁻¹(U)} ≤
C ‖∇f‖_{L̲^{2+δ}(U)} (r^β + r^{-2-d/2} E'(ε)^{1/2})`, and
`‖½∇u^ε·a(·/ε)∇u^ε - ½∇u·ā∇u‖_{W̲^{-2,1}(U)} ≤
C ‖∇f‖²_{L̲^{2+δ}(U)} (r^β + r^{-2-d/2} E'(ε)^{1/2})`. -/
theorem theorem_1_17 (hd : 2 ≤ d) (hΛ : 1 ≤ Λ) {U : Set (Vec d)} (hUo : IsOpen U)
    (hUc : Convex ℝ U) (hUne : U.Nonempty) (hU : U ⊆ triadicCube d 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ β C : ℝ, 0 < β ∧ 0 ≤ C ∧
      ∀ (a : CoefficientField d Λ) (A : Mat d), A.transpose = A →
      (∀ ξ, euclideanSq ξ ≤ dot ξ (A.mulVec ξ)) → (∀ ξ, dot ξ (A.mulVec ξ) ≤ Λ * euclideanSq ξ) →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ (φ : Fin d → Vec d → ℝ) (Dφ : Fin d → Vec d → Vec d),
      (∀ k, IsDirichletMinimizer a (triadicCube d (triadicScale ε)) (unitVector k) (φ k) (Dφ k)) →
      ∀ (f : Vec d → ℝ) (F : Vec d → Vec d), IsW1p U (ENNReal.ofReal (2 + δ)) f F →
      ∀ (uε u : Vec d → ℝ) (gε g : Vec d → Vec d),
      H01 U (fun x => uε x - f x) (fun x => gε x - F x) →
      HasWeakDivergence U (fun x => (a (ε⁻¹ • x)).mulVec (gε x)) (fun _ => 0) →
      H01 U (fun x => u x - f x) (fun x => g x - F x) →
      HasWeakDivergence U (fun x => A.mulVec (g x)) (fun _ => 0) →
      ∀ r : ℝ, 0 < r → r < 1 →
      ENNReal.ofReal (scalarRms volume U (fun x => uε x - u x)) +
          vectorHatNegativeSobolevNorm U (fun x => gε x - g x) +
          vectorHatNegativeSobolevNorm U
            (fun x => (a (ε⁻¹ • x)).mulVec (gε x) - A.mulVec (g x)) ≤
        ENNReal.ofReal C *
          PDE.eLpMeanNormOn U (ENNReal.ofReal (2 + δ)) (fun x => euclideanNorm (F x)) *
          (ENNReal.ofReal (r ^ β) + ENNReal.ofReal (r ^ (-(2 + (d : ℝ) / 2))) *
            twoScaleDeviation a A ε φ Dφ ^ (1 / 2 : ℝ)) ∧
      negativeSobolevTwoNorm (ENNReal.ofReal 1) U (fun x =>
          (1 / 2 : ℝ) * dot (gε x) ((a (ε⁻¹ • x)).mulVec (gε x)) -
            (1 / 2 : ℝ) * dot (g x) (A.mulVec (g x))) ≤
        ENNReal.ofReal C *
          PDE.eLpMeanNormOn U (ENNReal.ofReal (2 + δ)) (fun x => euclideanNorm (F x)) ^ 2 *
          (ENNReal.ofReal (r ^ β) + ENNReal.ofReal (r ^ (-(2 + (d : ℝ) / 2))) *
            twoScaleDeviation a A ε φ Dφ ^ (1 / 2 : ℝ)) := by
  have hd0 : 0 < d := by omega
  have hUb := isBounded_of_subset_ball (subset_ball_of_subset_triadicCube_zero hd0 hU)
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hUne).ne'
  have hUt : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hΛ0 : 0 ≤ Λ := by linarith
  obtain ⟨β, C0, Ce, hβ, hC0, hCe, hmain⟩ := exists_twoScale_estimate hd hΛ hUo hUc hUne hU hδ
  have hq1 : (1 : ℝ) < d / (d - 1) := by
    have : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
    rw [lt_div_iff₀ (by linarith)]
    linarith
  obtain ⟨C16, hC16, h16⟩ := lemma_1_16 hd hUo hUb hUc le_rfl hq1
  have hX0 : 0 ≤ C16 * (C0 * (Ce * (1 + Λ))) :=
    mul_nonneg hC16.le (mul_nonneg hC0 (mul_nonneg hCe (by linarith)))
  refine ⟨β, 3 * C0 + C16 * (C0 * (Ce * (1 + Λ))), hβ,
    add_nonneg (mul_nonneg (by norm_num) hC0) hX0,
    fun a A hAt hA1 hA2 ε hε hε1 φ Dφ hmin f F hf uε u gε g huε hdivε hu hdiv r hr0 hr1 => ?_⟩
  obtain ⟨hEne, hFp, hH1ε, hH1, h1, h2, h3, hgε, hg⟩ :=
    hmain a A hAt hA1 hA2 ε hε hε1 φ Dφ hmin f F hf uε u gε g huε hdivε hu hdiv r hr0 hr1
  obtain ⟨Fr, hFr⟩ : ∃ Fr : ℝ, Fr = (PDE.eLpMeanNormOn U (ENNReal.ofReal (2 + δ))
      (fun x => euclideanNorm (F x))).toReal := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (twoScaleDeviation a A ε φ Dφ ^ (1 / 2 : ℝ)).toReal :=
    ⟨_, rfl⟩
  rw [← hFr, ← hs] at h1 h2 h3
  rw [← hFr] at hgε hg
  have hFr0 : 0 ≤ Fr := by rw [hFr]; exact ENNReal.toReal_nonneg
  have hs0 : 0 ≤ s := by rw [hs]; exact ENNReal.toReal_nonneg
  have eF : ENNReal.ofReal Fr =
      PDE.eLpMeanNormOn U (ENNReal.ofReal (2 + δ)) (fun x => euclideanNorm (F x)) := by
    rw [hFr]; exact ENNReal.ofReal_toReal hFp
  have es : ENNReal.ofReal s = twoScaleDeviation a A ε φ Dφ ^ (1 / 2 : ℝ) := by
    rw [hs]; exact ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hEne)
  have hR0 : 0 ≤ r ^ (-(2 + (d : ℝ) / 2)) := Real.rpow_nonneg hr0.le _
  have hrβ0 : 0 ≤ r ^ β := Real.rpow_nonneg hr0.le _
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = r ^ β + r ^ (-(2 + (d : ℝ) / 2)) * s := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; exact add_nonneg hrβ0 (mul_nonneg hR0 hs0)
  have eB : ENNReal.ofReal (r ^ β) + ENNReal.ofReal (r ^ (-(2 + (d : ℝ) / 2))) *
      twoScaleDeviation a A ε φ Dφ ^ (1 / 2 : ℝ) = ENNReal.ofReal B := by
    rw [hB, ← es, ENNReal.ofReal_add hrβ0 (mul_nonneg hR0 hs0), ENNReal.ofReal_mul hR0]
  rw [← hB] at h1 h2 h3
  rw [eB, ← eF]
  have hY0 : 0 ≤ C0 * (Fr * B) := mul_nonneg hC0 (mul_nonneg hFr0 hB0)
  constructor
  · calc ENNReal.ofReal (scalarRms volume U (fun x => uε x - u x)) +
          vectorHatNegativeSobolevNorm U (fun x => gε x - g x) +
          vectorHatNegativeSobolevNorm U
            (fun x => (a (ε⁻¹ • x)).mulVec (gε x) - A.mulVec (g x)) ≤
        ENNReal.ofReal (C0 * (Fr * B)) + ENNReal.ofReal (C0 * (Fr * B)) +
          ENNReal.ofReal (C0 * (Fr * B)) :=
          add_le_add (add_le_add (ENNReal.ofReal_le_ofReal h1) h2) h3
      _ = ENNReal.ofReal (C0 * (Fr * B) + C0 * (Fr * B) + C0 * (Fr * B)) := by
          rw [ENNReal.ofReal_add (add_nonneg hY0 hY0) hY0, ENNReal.ofReal_add hY0 hY0]
      _ ≤ ENNReal.ofReal ((3 * C0 + C16 * (C0 * (Ce * (1 + Λ)))) * Fr * B) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [show (3 * C0 + C16 * (C0 * (Ce * (1 + Λ)))) * Fr * B =
            C0 * (Fr * B) + C0 * (Fr * B) + C0 * (Fr * B) +
              C16 * (C0 * (Ce * (1 + Λ))) * (Fr * B) by ring]
          exact le_add_of_nonneg_right (mul_nonneg hX0 (mul_nonneg hFr0 hB0))
      _ = _ := by
          rw [ENNReal.ofReal_mul (mul_nonneg (add_nonneg (mul_nonneg (by norm_num) hC0) hX0)
            hFr0), ENNReal.ofReal_mul (add_nonneg (mul_nonneg (by norm_num) hC0) hX0)]
  · have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUt
    have hgi : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U) := fun i => hH1.2.1.eval i
    have hgεi : ∀ i, MemLp (fun x => gε x i) 2 (volume.restrict U) := fun i => hH1ε.2.1.eval i
    have hL2ε : IsL2Sol U (fun x => (rescaledCoefficientField a hε.ne' x).mulVec (gε x)) :=
      ⟨memLp_pi_iff.2 fun i => memLp_coefficient_mulVec_apply _ hH1ε.2.1 i, hdivε⟩
    have hL2 : IsL2Sol U (fun x => A.mulVec (g x)) :=
      ⟨memLp_pi_iff.2 fun i => memLp_const_mulVec A hgi i, hdiv⟩
    have hlem := h16 uε u gε g _ _ hH1ε hH1 hL2ε hL2
    have hvε : PDE.eLpMeanNormOn U 2 (fun x => euclideanNorm (gε x)) ≤
        ENNReal.ofReal (Ce * Fr) := by
      rw [eLpMeanNormOn_two_euclideanNorm_eq hU0 hgεi]; exact ENNReal.ofReal_le_ofReal hgε
    have hvA : PDE.eLpMeanNormOn U 2 (fun x => euclideanNorm (A.mulVec (g x))) ≤
        ENNReal.ofReal (Λ * (Ce * Fr)) := by
      rw [eLpMeanNormOn_two_euclideanNorm_eq hU0 (memLp_const_mulVec A hgi)]
      refine ENNReal.ofReal_le_ofReal (le_trans ?_ (mul_le_mul_of_nonneg_left hg hΛ0))
      exact vectorRms_mulVec_le hΛ0 (constantCoefficientField A hAt hA1 hA2) hgi hUt
    have hvu : PDE.eLpMeanNormOn U 2 (fun x => uε x - u x) ≤ ENNReal.ofReal (C0 * (Fr * B)) := by
      have hm : MemLp (fun x => uε x - u x) 2 (volume.restrict U) := hH1ε.1.sub hH1.1
      rw [eLpMeanNormOn_two_eq_ofReal_scalarRms hU0 hm]
      exact ENNReal.ofReal_le_ofReal h1
    have hvn : vectorNegativeSobolevOneNorm 2 U (fun x =>
        (rescaledCoefficientField a hε.ne' x).mulVec (gε x) - A.mulVec (g x)) ≤
          ENNReal.ofReal (C0 * (Fr * B)) :=
      (Finset.sum_le_sum fun i _ =>
        negativeSobolevOneNorm_two_zero_le_hatNegativeSobolevNorm hU0 hUt _).trans h3
    have e : (fun x => (1 / 2 : ℝ) * dot (gε x) ((a (ε⁻¹ • x)).mulVec (gε x)) -
        (1 / 2 : ℝ) * dot (g x) (A.mulVec (g x))) = fun x => (1 / 2 : ℝ) *
          (dot (gε x) ((a (ε⁻¹ • x)).mulVec (gε x)) - dot (g x) (A.mulVec (g x))) := by
      funext x; ring
    have hCe0 : 0 ≤ Ce * Fr := mul_nonneg hCe hFr0
    rw [e]
    calc _ ≤ ENNReal.ofReal |1 / 2| * negativeSobolevTwoNorm (ENNReal.ofReal 1) U (fun x =>
          dot (gε x) ((a (ε⁻¹ • x)).mulVec (gε x)) - dot (g x) (A.mulVec (g x))) :=
          negativeSobolevTwoNorm_const_mul_le _ U _ _
      _ ≤ 1 * negativeSobolevTwoNorm (ENNReal.ofReal 1) U (fun x =>
          dot (gε x) ((a (ε⁻¹ • x)).mulVec (gε x)) - dot (g x) (A.mulVec (g x))) :=
          mul_le_mul_left (ENNReal.ofReal_le_one.2
            (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; norm_num)) _
      _ ≤ ENNReal.ofReal C16 * (ENNReal.ofReal (Ce * Fr) * ENNReal.ofReal (C0 * (Fr * B)) +
          ENNReal.ofReal (Λ * (Ce * Fr)) * ENNReal.ofReal (C0 * (Fr * B))) := by
          rw [one_mul]
          exact hlem.trans (mul_le_mul_right (add_le_add (mul_le_mul' hvε hvn)
            (mul_le_mul' hvA hvu)) _)
      _ = ENNReal.ofReal (C16 * (Ce * Fr * (C0 * (Fr * B)) + Λ * (Ce * Fr) * (C0 * (Fr * B)))) := by
          rw [ENNReal.ofReal_mul hC16.le, ENNReal.ofReal_add (mul_nonneg hCe0 hY0)
            (mul_nonneg (mul_nonneg hΛ0 hCe0) hY0), ENNReal.ofReal_mul hCe0,
            ENNReal.ofReal_mul (mul_nonneg hΛ0 hCe0)]
      _ ≤ ENNReal.ofReal ((3 * C0 + C16 * (C0 * (Ce * (1 + Λ)))) * Fr ^ 2 * B) :=
          ENNReal.ofReal_le_ofReal (by
            rw [show (3 * C0 + C16 * (C0 * (Ce * (1 + Λ)))) * Fr ^ 2 * B =
              C16 * (Ce * Fr * (C0 * (Fr * B)) + Λ * (Ce * Fr) * (C0 * (Fr * B))) +
                3 * C0 * Fr ^ 2 * B by ring]
            exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (mul_nonneg
              (by norm_num : (0 : ℝ) ≤ 3) hC0) (sq_nonneg Fr)) hB0))
      _ = _ := by
          rw [ENNReal.ofReal_mul (mul_nonneg (add_nonneg (mul_nonneg (by norm_num) hC0) hX0)
            (sq_nonneg Fr)), ENNReal.ofReal_mul (add_nonneg (mul_nonneg (by norm_num) hC0) hX0),
            ENNReal.ofReal_pow hFr0]

end TwoScale

end QSH
