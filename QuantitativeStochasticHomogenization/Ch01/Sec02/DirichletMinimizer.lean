import QuantitativeStochasticHomogenization.Ch01.Sec02.TestPoincare
import QuantitativeStochasticHomogenization.Ch01.Sec03.DirichletEnergyCorrectorBounds

/-!
# The minimizer `v(·, U, p)` of the Dirichlet energy

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.2, (1.8) and Lemma 1.1 (first variation and quadratic response).

A minimizer of (1.7) is a pair `(u, g)` with `u ∈ H¹₀(U)` of weak gradient `g` whose energy
`⨍_U ½ (p + g)·a(p + g)` is `μ(U, p)`; the minimizer of (1.8) is `v(·, U, p) = ℓ_p + u`, with
gradient `p + g`.

* `exists_isDirichletMinimizer`: for a bounded set `U` of positive measure there is a minimizer.
  The book refers to the weak lower semicontinuity of the energy; here a minimizing sequence of
  tests is Cauchy in `L²` by the parallelogram identity and the uniform convexity
  `ξ·aξ ≥ |ξ|²`, together with the Poincaré inequality for the tests, and its limit lies in
  `H¹₀(U)`.
* `IsDirichletMinimizer.integral_dot_eq_zero`: the first variation (1.12),
  `∫_U h·a(p + g) = 0` for every `w ∈ H¹₀(U)` of weak gradient `h`.
* `isDirichletMinimizer_iff_solvesDirichletProblem`: the minimizers are exactly the solutions of
  the Dirichlet problem (1.12) in the weak sense.
* `IsDirichletMinimizer.trialEnergy_sub_eq` and `IsDirichletMinimizer.quadraticResponse`: the
  quadratic response (1.13).
* `IsDirichletMinimizer.ae_eq`: the minimizer is unique up to null sets.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## Linear combinations in `H¹₀(U)` -/

private theorem integrable_mul_of_memLp_two' {μ : Measure (Vec d)} {f g : Vec d → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) : Integrable (fun x => f x * g x) μ := by
  refine (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

private theorem sq_add_le (c₁ c₂ A B : ℝ) :
    (c₁ * A + c₂ * B) ^ 2 ≤ 2 * c₁ ^ 2 * A ^ 2 + 2 * c₂ ^ 2 * B ^ 2 := by
  nlinarith [sq_nonneg (c₁ * A - c₂ * B)]

private theorem euclideanSq_smul_add_le (c₁ c₂ : ℝ) (X Y : Vec d) :
    euclideanSq (c₁ • X + c₂ • Y) ≤ 2 * c₁ ^ 2 * euclideanSq X + 2 * c₂ ^ 2 * euclideanSq Y := by
  simp only [euclideanSq, dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have := sq_add_le c₁ c₂ (X i) (Y i)
  nlinarith [this]

theorem sq_apply_le_euclideanSq (X : Vec d) (i : Fin d) : X i ^ 2 ≤ euclideanSq X := by
  simp only [euclideanSq, dot]
  have := Finset.single_le_sum (f := fun j => X j * X j) (fun j _ => mul_self_nonneg _)
    (Finset.mem_univ i)
  simpa [pow_two] using this

theorem euclideanSq_sub_comm (X Y : Vec d) : euclideanSq (X - Y) = euclideanSq (Y - X) := by
  simp only [euclideanSq, dot, Pi.sub_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **`H¹₀(U)` is a vector space**: `c₁ u + c₂ w ∈ H¹₀(U)` with weak gradient `c₁ g + c₂ h`. -/
theorem H01.linearCombination {U : Set (Vec d)} {u w : Vec d → ℝ} {g h : Vec d → Vec d}
    (hu : H01 U u g) (hw : H01 U w h) (c₁ c₂ : ℝ) :
    H01 U (fun x => c₁ * u x + c₂ * w x) (fun x => c₁ • g x + c₂ • h x) := by
  obtain ⟨hu2, hg2, hug, v, hv, hvc, hvg⟩ := hu
  obtain ⟨hw2, hh2, hwh, v', hv', hv'c, hv'g⟩ := hw
  have hvt : ∀ n, IsSpatialTest U (fun x => c₁ * v n x + c₂ * v' n x) := fun n =>
    ((hv n).const_mul c₁).add ((hv' n).const_mul c₂)
  have hgv : ∀ n x, gradient (fun x => c₁ * v n x + c₂ * v' n x) x =
      c₁ • gradient (v n) x + c₂ • gradient (v' n) x := by
    intro n x
    rw [((hv n).const_mul c₁).gradient_add ((hv' n).const_mul c₂),
      (hv n).gradient_const_mul, (hv' n).gradient_const_mul]
  refine ⟨(hu2.const_mul c₁).add (hw2.const_mul c₂), (hg2.const_smul c₁).add (hh2.const_smul c₂),
    fun i => ⟨?_, ?_, fun φ hφ => ?_⟩, fun n x => c₁ * v n x + c₂ * v' n x, hvt, ?_, ?_⟩
  · exact ((hug i).1.smul c₁).add ((hwh i).1.smul c₂)
  · exact ((hug i).2.1.smul c₁).add ((hwh i).2.1.smul c₂)
  · have hdφ : MemLp (fun x => coordinateDerivative i φ x) 2 (volume.restrict U) :=
      MemLp.eval (hφ.memLp_gradient (volume.restrict U)) i
    have hφ2 : MemLp φ 2 (volume.restrict U) := hφ.memLp_two _
    have i1 := integrable_mul_of_memLp_two' hu2 hdφ
    have i2 := integrable_mul_of_memLp_two' hw2 hdφ
    have i3 := integrable_mul_of_memLp_two' (MemLp.eval hg2 i) hφ2
    have i4 := integrable_mul_of_memLp_two' (MemLp.eval hh2 i) hφ2
    have e1 := (hug i).2.2 φ hφ
    have e2 := (hwh i).2.2 φ hφ
    calc ∫ x in U, (c₁ * u x + c₂ * w x) * coordinateDerivative i φ x
        = c₁ * (∫ x in U, u x * coordinateDerivative i φ x) +
            c₂ * ∫ x in U, w x * coordinateDerivative i φ x := by
          rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul _)
            (i2.const_mul _)]
          exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
      _ = -(c₁ * (∫ x in U, g x i * φ x) + c₂ * ∫ x in U, h x i * φ x) := by rw [e1, e2]; ring
      _ = -∫ x in U, (c₁ • g x + c₂ • h x) i * φ x := by
          rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i3.const_mul _)
            (i4.const_mul _)]
          congr 1
          exact integral_congr_ae (Eventually.of_forall fun x => by
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring)
  · have hv2 : ∀ n, MemLp (v n) 2 (volume.restrict U) := fun n => (hv n).memLp_two _
    have hv'2 : ∀ n, MemLp (v' n) 2 (volume.restrict U) := fun n => (hv' n).memLp_two _
    have hlim : Tendsto (fun n => 2 * c₁ ^ 2 * (∫ x in U, (v n x - u x) ^ 2) +
        2 * c₂ ^ 2 * ∫ x in U, (v' n x - w x) ^ 2) atTop (𝓝 0) := by
      simpa using (hvc.const_mul (2 * c₁ ^ 2)).add (hv'c.const_mul (2 * c₂ ^ 2))
    refine squeeze_zero (fun n => integral_nonneg fun x => sq_nonneg _) (fun n => ?_) hlim
    have j1 : Integrable (fun x => (v n x - u x) ^ 2) (volume.restrict U) :=
      ((hv2 n).sub hu2).integrable_sq
    have j2 : Integrable (fun x => (v' n x - w x) ^ 2) (volume.restrict U) :=
      ((hv'2 n).sub hw2).integrable_sq
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (j1.const_mul _)
      (j2.const_mul _)]
    refine integral_mono ((((hv2 n).const_mul c₁).add ((hv'2 n).const_mul c₂)).sub
      ((hu2.const_mul c₁).add (hw2.const_mul c₂))).integrable_sq
      ((j1.const_mul _).add (j2.const_mul _)) fun x => ?_
    have := sq_add_le c₁ c₂ (v n x - u x) (v' n x - w x)
    simp only
    nlinarith [this]
  · have hdv : ∀ n, MemLp (gradient (v n)) 2 (volume.restrict U) := fun n =>
      (hv n).memLp_gradient _
    have hdv' : ∀ n, MemLp (gradient (v' n)) 2 (volume.restrict U) := fun n =>
      (hv' n).memLp_gradient _
    have hlim : Tendsto (fun n => 2 * c₁ ^ 2 * (∫ x in U, euclideanSq (gradient (v n) x - g x)) +
        2 * c₂ ^ 2 * ∫ x in U, euclideanSq (gradient (v' n) x - h x)) atTop (𝓝 0) := by
      simpa using (hvg.const_mul (2 * c₁ ^ 2)).add (hv'g.const_mul (2 * c₂ ^ 2))
    refine squeeze_zero (fun n => integral_nonneg fun x => euclideanSq_nonneg _) (fun n => ?_) hlim
    have j1 : Integrable (fun x => euclideanSq (gradient (v n) x - g x)) (volume.restrict U) :=
      integrable_euclideanSq_of_memLp ((hdv n).sub hg2)
    have j2 : Integrable (fun x => euclideanSq (gradient (v' n) x - h x)) (volume.restrict U) :=
      integrable_euclideanSq_of_memLp ((hdv' n).sub hh2)
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (j1.const_mul _)
      (j2.const_mul _)]
    have hmem : MemLp (fun x => gradient (fun x => c₁ * v n x + c₂ * v' n x) x -
        (c₁ • g x + c₂ • h x)) 2 (volume.restrict U) :=
      ((hvt n).memLp_gradient _).sub ((hg2.const_smul c₁).add (hh2.const_smul c₂))
    refine integral_mono (integrable_euclideanSq_of_memLp hmem)
      ((j1.const_mul _).add (j2.const_mul _)) fun x => ?_
    have hx : gradient (fun x => c₁ * v n x + c₂ * v' n x) x - (c₁ • g x + c₂ • h x) =
        c₁ • (gradient (v n) x - g x) + c₂ • (gradient (v' n) x - h x) := by
      rw [hgv n x, smul_sub, smul_sub]
      abel
    simp only
    rw [hx]
    exact euclideanSq_smul_add_le c₁ c₂ _ _

theorem H01.congr {U : Set (Vec d)} {u u' : Vec d → ℝ} {g g' : Vec d → Vec d} (hu : H01 U u g)
    (h1 : ∀ x, u x = u' x) (h2 : ∀ x, g x = g' x) : H01 U u' g' := by
  have e1 : u = u' := funext h1
  have e2 : g = g' := funext h2
  rw [← e1, ← e2]
  exact hu

theorem H01.sub {U : Set (Vec d)} {u w : Vec d → ℝ} {g h : Vec d → Vec d} (hu : H01 U u g)
    (hw : H01 U w h) : H01 U (fun x => u x - w x) (fun x => g x - h x) :=
  (hu.linearCombination hw 1 (-1)).congr (fun x => by ring) (fun x => by
    rw [one_smul, neg_one_smul, sub_eq_add_neg])

theorem H01.add_smul {U : Set (Vec d)} {u w : Vec d → ℝ} {g h : Vec d → Vec d} (hu : H01 U u g)
    (hw : H01 U w h) (t : ℝ) : H01 U (fun x => u x + t * w x) (fun x => g x + t • h x) :=
  (hu.linearCombination hw 1 t).congr (fun x => by ring) (fun x => by rw [one_smul])

theorem H01.midpoint {U : Set (Vec d)} {u w : Vec d → ℝ} {g h : Vec d → Vec d} (hu : H01 U u g)
    (hw : H01 U w h) :
    H01 U (fun x => (1 / 2 : ℝ) * (u x + w x)) (fun x => (1 / 2 : ℝ) • (g x + h x)) :=
  (hu.linearCombination hw (1 / 2) (1 / 2)).congr (fun x => by ring) (fun x => by
    rw [smul_add])

/-! ## Expansions of the energy -/

/-- `(X + D)·A(X + D) = X·AX + 2 D·AX + D·AD` for a symmetric matrix `A`. -/
theorem dot_add_mulVec_add_eq {A : Mat d} (hA : A.transpose = A) (X D : Vec d) :
    dot (X + D) (A.mulVec (X + D)) = dot X (A.mulVec X) + 2 * dot D (A.mulVec X) +
      dot D (A.mulVec D) := by
  have hs := dot_mulVec_comm_of_symm hA X D
  have h : dot (X + D) (A.mulVec (X + D)) = dot X (A.mulVec X) + dot X (A.mulVec D) +
      dot D (A.mulVec X) + dot D (A.mulVec D) := by
    simp only [Matrix.mulVec_add, dot, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
    ring
  rw [h, hs]
  ring

/-- **The energy of a perturbed gradient**: `∫_U ½(p + G + D)·a(p + G + D) =
∫_U ½(p + G)·a(p + G) + ∫_U D·a(p + G) + ∫_U ½ D·aD`. -/
theorem integral_energy_add (a : CoefficientField d Λ) {U : Set (Vec d)} (hU : volume U ≠ ⊤)
    (e : Vec d) {G D : Vec d → Vec d} (hG : MemLp G 2 (volume.restrict U))
    (hD : MemLp D 2 (volume.restrict U)) :
    ∫ x in U, (1 / 2 : ℝ) * dot (e + (G x + D x)) ((a x).mulVec (e + (G x + D x))) =
      (∫ x in U, (1 / 2 : ℝ) * dot (e + G x) ((a x).mulVec (e + G x))) +
        (∫ x in U, dot (D x) ((a x).mulVec (e + G x))) +
        ∫ x in U, (1 / 2 : ℝ) * dot (D x) ((a x).mulVec (D x)) := by
  have := isFiniteMeasure_restrict.mpr hU
  have hEG : MemLp (fun x => e + G x) 2 (volume.restrict U) := (memLp_const e).add hG
  have i1 := (integrable_dot_mulVec a U hEG).const_mul (1 / 2 : ℝ)
  have i2 := integrable_dot_mulVec_of_memLp a hD hEG
  have i3 := (integrable_dot_mulVec a U hD).const_mul (1 / 2 : ℝ)
  have i12 : Integrable (fun x => (1 / 2 : ℝ) * dot (e + G x) ((a x).mulVec (e + G x)) +
      dot (D x) ((a x).mulVec (e + G x))) (volume.restrict U) := i1.add i2
  rw [← integral_add i1 i2, ← integral_add i12 i3]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have h := dot_add_mulVec_add_eq (a.symmetric x) (e + G x) (D x)
  dsimp only
  rw [show e + (G x + D x) = e + G x + D x by abel, h]
  ring

/-- The midpoint identity: `E(½(G + H)) + ⅛ ⨍_U (G - H)·a(G - H) = ½ E(G) + ½ E(H)`. -/
theorem trialEnergy_midpoint (a : CoefficientField d Λ) {U : Set (Vec d)} (hU : volume U ≠ ⊤)
    (e : Vec d) {G H : Vec d → Vec d} (hG : MemLp G 2 (volume.restrict U))
    (hH : MemLp H 2 (volume.restrict U)) :
    trialEnergy a U e (fun x => (1 / 2 : ℝ) • (G x + H x)) +
      (1 / 8 : ℝ) * ((volume.real U)⁻¹ * ∫ x in U, dot (G x - H x) ((a x).mulVec (G x - H x))) =
      (1 / 2 : ℝ) * trialEnergy a U e G + (1 / 2 : ℝ) * trialEnergy a U e H := by
  have := isFiniteMeasure_restrict.mpr hU
  have hM : MemLp (fun x => (1 / 2 : ℝ) • (G x + H x)) 2 (volume.restrict U) :=
    (hG.add hH).const_smul (1 / 2 : ℝ)
  have i1 := integrable_energyDensity a hU e hM
  have i2 : Integrable (fun x => dot (G x - H x) ((a x).mulVec (G x - H x)))
      (volume.restrict U) := integrable_dot_mulVec a U (hG.sub hH)
  have i3 := integrable_energyDensity a hU e hG
  have i4 := integrable_energyDensity a hU e hH
  have key : (∫ x in U, (1 / 2 : ℝ) * dot (e + (1 / 2 : ℝ) • (G x + H x))
        ((a x).mulVec (e + (1 / 2 : ℝ) • (G x + H x)))) +
      (1 / 8 : ℝ) * ∫ x in U, dot (G x - H x) ((a x).mulVec (G x - H x)) =
      (1 / 2 : ℝ) * (∫ x in U, (1 / 2 : ℝ) * dot (e + G x) ((a x).mulVec (e + G x))) +
        (1 / 2 : ℝ) * ∫ x in U, (1 / 2 : ℝ) * dot (e + H x) ((a x).mulVec (e + H x)) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
      ← integral_add i1 (i2.const_mul _), ← integral_add (i3.const_mul _) (i4.const_mul _)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have hp := dot_parallelogram (a x) (e + G x) (e + H x)
    have hm : e + (1 / 2 : ℝ) • (G x + H x) = (1 / 2 : ℝ) • (e + G x + (e + H x)) := by
      rw [smul_add, smul_add, smul_add]
      module
    have hs : ∀ v : Vec d, dot ((1 / 2 : ℝ) • v) ((a x).mulVec ((1 / 2 : ℝ) • v)) =
        (1 / 4 : ℝ) * dot v ((a x).mulVec v) := by
      intro v
      simp only [dot_eq_dotProduct, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
        smul_eq_mul]
      ring
    have hd : e + G x - (e + H x) = G x - H x := by abel
    dsimp only
    rw [hm, hs]
    rw [hd] at hp
    linarith
  rw [trialEnergy_eq, trialEnergy_eq, trialEnergy_eq]
  linear_combination (volume.real U)⁻¹ * key

/-! ## The minimizer -/

/-- `(u, g)` is a minimizer of (1.7): `u ∈ H¹₀(U)` has weak gradient `g` and
`⨍_U ½ (p + g)·a(p + g) = μ(U, p)`. The minimizer of (1.8) is `v(·, U, p) = ℓ_p + u`. -/
def IsDirichletMinimizer (a : CoefficientField d Λ) (U : Set (Vec d)) (e : Vec d)
    (u : Vec d → ℝ) (g : Vec d → Vec d) : Prop :=
  H01 U u g ∧ trialEnergy a U e g = dirichletEnergy a U e

/-- `ℓ_p + u` solves the Dirichlet problem (1.12) in the weak sense: `u ∈ H¹₀(U)` has weak
gradient `g` and `∫_U h·a(p + g) = 0` for every `w ∈ H¹₀(U)` of weak gradient `h`. -/
def SolvesDirichletProblem (a : CoefficientField d Λ) (U : Set (Vec d)) (e : Vec d)
    (u : Vec d → ℝ) (g : Vec d → Vec d) : Prop :=
  H01 U u g ∧ ∀ (w : Vec d → ℝ) (h : Vec d → Vec d), H01 U w h →
    ∫ x in U, dot (h x) ((a x).mulVec (e + g x)) = 0

theorem dirichletEnergy_le_of_H01 (a : CoefficientField d Λ) {U : Set (Vec d)} (e : Vec d)
    {u : Vec d → ℝ} {g : Vec d → Vec d} (hu : H01 U u g) :
    dirichletEnergy a U e ≤ trialEnergy a U e g :=
  csInf_le (bddBelow_dirichletEnergySet a U e) ⟨u, g, hu, rfl⟩

/-- **Existence of the minimizer (1.8)** for a bounded set of positive measure. -/
theorem exists_isDirichletMinimizer [NeZero d] (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hU : Bornology.IsBounded U) (hU0 : volume U ≠ 0) (e : Vec d) :
    ∃ (u : Vec d → ℝ) (g : Vec d → Vec d), IsDirichletMinimizer a U e u g := by
  obtain ⟨R, hR, hUR⟩ := exists_subset_cube_of_isBounded hU
  have hUt : volume U ≠ ⊤ := hU.measure_lt_top.ne
  have hfin : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUt
  set m := dirichletEnergy a U e
  set V := volume.real U
  have hV : 0 < V := ENNReal.toReal_pos hU0 hUt
  have hm0 : 0 ≤ m := dirichletEnergy_nonneg a U e
  choose v hv hvE using fun n : ℕ =>
    exists_test_trialEnergy_lt a hUt e (Nat.one_div_pos_of_nat (n := n) (α := ℝ))
  have hdv : ∀ n, MemLp (gradient (v n)) 2 (volume.restrict U) := fun n =>
    (hv n).memLp_gradient _
  have hv2 : ∀ n, MemLp (v n) 2 (volume.restrict U) := fun n => (hv n).memLp_two _
  have hmE : ∀ n, m ≤ trialEnergy a U e (gradient (v n)) := fun n =>
    dirichletEnergy_le_trialEnergy a e (hv n)
  -- the gradients form a Cauchy sequence
  have hgrad : ∀ n k, ∫ x in U, euclideanSq (gradient (v n) x - gradient (v k) x) ≤
      V * (4 / ((n : ℝ) + 1) + 4 / ((k : ℝ) + 1)) := by
    intro n k
    have hw := ((hv n).add (hv k)).const_mul (1 / 2)
    have hgw : gradient (fun x => 1 / 2 * (v n x + v k x)) =
        fun x => (1 / 2 : ℝ) • (gradient (v n) x + gradient (v k) x) := by
      funext x
      rw [((hv n).add (hv k)).gradient_const_mul, (hv n).gradient_add (hv k)]
    have h1 := dirichletEnergy_le_trialEnergy a e hw
    rw [hgw] at h1
    have hmid := trialEnergy_midpoint a hUt e (hdv n) (hdv k)
    have hell : ∫ x in U, euclideanSq (gradient (v n) x - gradient (v k) x) ≤
        ∫ x in U, dot (gradient (v n) x - gradient (v k) x)
          ((a x).mulVec (gradient (v n) x - gradient (v k) x)) :=
      integral_mono (integrable_euclideanSq_of_memLp ((hdv n).sub (hdv k)))
        (integrable_dot_mulVec a U ((hdv n).sub (hdv k))) fun x => (a.elliptic x _).1
    have hn := hvE n
    have hk := hvE k
    have hVi : 0 < V⁻¹ := inv_pos.mpr hV
    have hbound : V⁻¹ * ∫ x in U, dot (gradient (v n) x - gradient (v k) x)
        ((a x).mulVec (gradient (v n) x - gradient (v k) x)) ≤
        4 / ((n : ℝ) + 1) + 4 / ((k : ℝ) + 1) := by
      have e1 : (1 : ℝ) / ((n : ℝ) + 1) * 4 = 4 / ((n : ℝ) + 1) := by ring
      have e2 : (1 : ℝ) / ((k : ℝ) + 1) * 4 = 4 / ((k : ℝ) + 1) := by ring
      nlinarith
    calc ∫ x in U, euclideanSq (gradient (v n) x - gradient (v k) x)
        ≤ V * (V⁻¹ * ∫ x in U, dot (gradient (v n) x - gradient (v k) x)
          ((a x).mulVec (gradient (v n) x - gradient (v k) x))) := by
          rw [← mul_assoc, mul_inv_cancel₀ hV.ne', one_mul]
          exact hell
      _ ≤ _ := mul_le_mul_of_nonneg_left hbound hV.le
  set b : ℕ → ℝ := fun N => V * (8 / ((N : ℝ) + 1)) with hb_def
  have hb : ∀ n k N, N ≤ n → N ≤ k →
      ∫ x in U, euclideanSq (gradient (v n) x - gradient (v k) x) ≤ b N := by
    intro n k N hn hk
    refine (hgrad n k).trans (mul_le_mul_of_nonneg_left ?_ hV.le)
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have h1 : 4 / ((n : ℝ) + 1) ≤ 4 / ((N : ℝ) + 1) :=
      div_le_div_of_nonneg_left (by norm_num) hN (by exact_mod_cast Nat.add_le_add_right hn 1)
    have h2 : 4 / ((k : ℝ) + 1) ≤ 4 / ((N : ℝ) + 1) :=
      div_le_div_of_nonneg_left (by norm_num) hN (by exact_mod_cast Nat.add_le_add_right hk 1)
    have : (8 : ℝ) / ((N : ℝ) + 1) = 4 / ((N : ℝ) + 1) + 4 / ((N : ℝ) + 1) := by ring
    linarith
  have hb0 : Tendsto b atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (V * 8)
    rw [mul_zero] at h
    exact h.congr fun N => by simp only [hb_def]; ring
  -- the coordinates of the gradients converge
  have hcoord : ∀ i : Fin d, ∃ f : Vec d → ℝ, MemLp f 2 (volume.restrict U) ∧
      Tendsto (fun n => ∫ x in U, (gradient (v n) x i - f x) ^ 2) atTop (𝓝 0) := by
    intro i
    refine exists_memLp_tendsto_integral_sq_sub (F := fun n x => gradient (v n) x i)
      (fun n => MemLp.eval (hdv n) i) b (fun n k N hn hk => ?_) hb0
    refine le_trans (integral_mono ((MemLp.eval ((hdv n).sub (hdv k)) i).integrable_sq)
      (integrable_euclideanSq_of_memLp ((hdv n).sub (hdv k))) fun x => ?_) (hb n k N hn hk)
    exact sq_apply_le_euclideanSq (gradient (v n) x - gradient (v k) x) i
  choose G hG hGlim using hcoord
  set g : Vec d → Vec d := fun x i => G i x
  have hg2 : MemLp g 2 (volume.restrict U) := memLp_pi_iff.mpr fun i => hG i
  -- the tests converge by the Poincaré inequality
  have hu : ∃ f : Vec d → ℝ, MemLp f 2 (volume.restrict U) ∧
      Tendsto (fun n => ∫ x in U, (v n x - f x) ^ 2) atTop (𝓝 0) := by
    refine exists_memLp_tendsto_integral_sq_sub hv2 (fun N => testPoincareConstant d * R ^ 2 * b N)
      (fun n k N hn hk => ?_) ?_
    · have hP := setIntegral_sq_le_of_isSpatialTest 0 hR hUR ((hv n).sub (hv k))
      have hgs : ∀ x, gradient (fun x => v n x - v k x) x = gradient (v n) x - gradient (v k) x :=
        (hv n).gradient_sub (hv k)
      simp_rw [hgs] at hP
      exact hP.trans (mul_le_mul_of_nonneg_left (hb n k N hn hk)
        (mul_nonneg (testPoincareConstant_nonneg d) (sq_nonneg R)))
    · simpa using hb0.const_mul (testPoincareConstant d * R ^ 2)
  obtain ⟨u, hu2, hulim⟩ := hu
  have hglim : Tendsto (fun n => ∫ x in U, euclideanSq (gradient (v n) x - g x)) atTop (𝓝 0) := by
    have hsum : ∀ n, ∫ x in U, euclideanSq (gradient (v n) x - g x) =
        ∑ i, ∫ x in U, (gradient (v n) x i - G i x) ^ 2 := by
      intro n
      have hI : ∀ i ∈ (Finset.univ : Finset (Fin d)),
          Integrable (fun x => (gradient (v n) x i - G i x) ^ 2) (volume.restrict U) :=
        fun i _ => (MemLp.eval ((hdv n).sub hg2) i).integrable_sq
      rw [← integral_finsetSum _ hI]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp [euclideanSq, dot, g, pow_two]
    simp_rw [hsum]
    simpa using tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun i _ => hGlim i
  -- the limit is a function of `H¹₀(U)`
  have hH01 : H01 U u g := by
    refine ⟨hu2, hg2, fun i => ⟨?_, ?_, fun φ hφ => ?_⟩, v, hv, hulim, hglim⟩
    · exact (show IntegrableOn u U volume from hu2.integrable one_le_two).locallyIntegrableOn
    · exact (show IntegrableOn (G i) U volume from
        (hG i).integrable one_le_two).locallyIntegrableOn
    · have hdφ : MemLp (fun x => coordinateDerivative i φ x) 2 (volume.restrict U) :=
        MemLp.eval (hφ.memLp_gradient (volume.restrict U)) i
      have t1 := tendsto_integral_mul_of_tendsto_integral_sq_sub hu2 hdφ hv2 hulim
      have t2 := tendsto_integral_mul_of_tendsto_integral_sq_sub (hG i) (hφ.memLp_two _)
        (fun n => MemLp.eval (hdv n) i) (hGlim i)
      have t3 := t1.congr fun n => (hv n).integral_mul_coordinateDerivative hφ i
      exact tendsto_nhds_unique t3 t2.neg
  refine ⟨u, g, hH01, le_antisymm ?_ (dirichletEnergy_le_of_H01 a e hH01)⟩
  -- the energy of the limit is the infimum
  have hEn : Tendsto (fun n => trialEnergy a U e (gradient (v n))) atTop (𝓝 m) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ hmE fun n => (hvE n).le
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_add m
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set t : ℝ := ε / (m + 1) with ht_def
  have ht : 0 < t := by positivity
  have htm : t * m ≤ ε := by
    rw [ht_def, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hlim : Tendsto (fun n => (1 + t) * trialEnergy a U e (gradient (v n)) +
      (1 + t⁻¹) * ((1 / 2) * Λ * (V⁻¹ * ∫ x in U, euclideanSq (g x - gradient (v n) x))))
      atTop (𝓝 ((1 + t) * m)) := by
    have h0 : Tendsto (fun n => ∫ x in U, euclideanSq (g x - gradient (v n) x)) atTop (𝓝 0) :=
      hglim.congr fun n => integral_congr_ae (Eventually.of_forall fun x =>
        euclideanSq_sub_comm _ _)
    simpa using (hEn.const_mul (1 + t)).add
      (((h0.const_mul V⁻¹).const_mul ((1 / 2) * Λ)).const_mul (1 + t⁻¹))
  have hle := le_of_tendsto_of_tendsto' tendsto_const_nhds hlim fun n =>
    trialEnergy_le_of_sub a hUt e (hdv n) hg2 ht
  linarith

/-- **The first variation (1.12)**: the minimizer satisfies `∫_U h·a(p + g) = 0` for every
`w ∈ H¹₀(U)` of weak gradient `h`. -/
theorem IsDirichletMinimizer.integral_dot_eq_zero {a : CoefficientField d Λ} {U : Set (Vec d)}
    (hU : volume U ≠ ⊤) {e : Vec d} {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hmin : IsDirichletMinimizer a U e u g) {w : Vec d → ℝ} {h : Vec d → Vec d}
    (hw : H01 U w h) : ∫ x in U, dot (h x) ((a x).mulVec (e + g x)) = 0 := by
  rcases eq_or_ne (volume U) 0 with h0 | h0
  · rw [Measure.restrict_eq_zero.mpr h0, integral_zero_measure]
  have hV : 0 < volume.real U := ENNReal.toReal_pos h0 hU
  have hg2 := hmin.1.2.1
  have hh2 := hw.2.1
  set B := ∫ x in U, dot (h x) ((a x).mulVec (e + g x))
  set A := ∫ x in U, (1 / 2 : ℝ) * dot (h x) ((a x).mulVec (h x))
  have hq : ∀ t : ℝ, 0 ≤ A * (t * t) + B * t + 0 := by
    intro t
    have hle := dirichletEnergy_le_of_H01 a e (hmin.1.add_smul hw t)
    rw [← hmin.2, trialEnergy_eq, trialEnergy_eq] at hle
    have hexp := integral_energy_add a hU e hg2 (hh2.const_smul t)
    have hlin : ∫ x in U, dot ((t • h) x) ((a x).mulVec (e + g x)) = t * B := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [Pi.smul_apply, dot_eq_dotProduct, smul_dotProduct, smul_eq_mul]
    have hquad : ∫ x in U, (1 / 2 : ℝ) * dot ((t • h) x) ((a x).mulVec ((t • h) x)) =
        t * t * A := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [Pi.smul_apply, dot_eq_dotProduct, Matrix.mulVec_smul, smul_dotProduct,
        dotProduct_smul, smul_eq_mul]
      ring
    simp only [Pi.smul_apply] at hexp hlin hquad
    rw [hexp, hlin, hquad] at hle
    have := (mul_le_mul_iff_right₀ (inv_pos.mpr hV)).mp (by linarith : (volume.real U)⁻¹ *
      ∫ x in U, (1 / 2 : ℝ) * dot (e + g x) ((a x).mulVec (e + g x)) ≤ (volume.real U)⁻¹ *
      ((∫ x in U, (1 / 2 : ℝ) * dot (e + g x) ((a x).mulVec (e + g x))) + t * B + t * t * A))
    nlinarith
  have hd := discrim_le_zero hq
  simp only [discrim] at hd
  nlinarith [sq_nonneg B]

/-- **The minimizers are the solutions of the Dirichlet problem (1.12).** -/
theorem isDirichletMinimizer_iff_solvesDirichletProblem (a : CoefficientField d Λ)
    {U : Set (Vec d)} (hU : volume U ≠ ⊤) (e : Vec d) (u : Vec d → ℝ) (g : Vec d → Vec d) :
    IsDirichletMinimizer a U e u g ↔ SolvesDirichletProblem a U e u g := by
  refine ⟨fun hmin => ⟨hmin.1, fun w h hw => hmin.integral_dot_eq_zero hU hw⟩, fun hsol => ?_⟩
  refine ⟨hsol.1, le_antisymm ?_ (dirichletEnergy_le_of_H01 a e hsol.1)⟩
  refine le_csInf ⟨_, _, _, H01_zero U, rfl⟩ ?_
  rintro E ⟨w, h, hw, rfl⟩
  change trialEnergy a U e g ≤ trialEnergy a U e h
  have hg2 := hsol.1.2.1
  have hD := hw.sub hsol.1
  have hexp := integral_energy_add a hU e hg2 hD.2.1
  have h0 := hsol.2 _ _ hD
  have hpos : 0 ≤ ∫ x in U, (1 / 2 : ℝ) * dot (h x - g x) ((a x).mulVec (h x - g x)) :=
    integral_nonneg fun x => mul_nonneg (by norm_num)
      ((euclideanSq_nonneg _).trans (a.elliptic x _).1)
  have hhg : (fun x => e + (g x + (h x - g x))) = fun x => e + h x := by
    funext x; abel
  rw [trialEnergy_eq, trialEnergy_eq]
  simp only [add_sub_cancel] at hexp
  rw [hexp]
  have hVi : 0 ≤ (volume.real U)⁻¹ := inv_nonneg.mpr measureReal_nonneg
  rw [h0]
  nlinarith

/-- **The quadratic response, exact form**: `⨍_U ½ (p + h)·a(p + h) - μ(U, p) =
⨍_U ½ (h - g)·a(h - g)`, the identity behind (1.13). -/
theorem IsDirichletMinimizer.trialEnergy_sub_eq {a : CoefficientField d Λ} {U : Set (Vec d)}
    (hU : volume U ≠ ⊤) {e : Vec d} {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hmin : IsDirichletMinimizer a U e u g) {w : Vec d → ℝ} {h : Vec d → Vec d}
    (hw : H01 U w h) :
    trialEnergy a U e h - dirichletEnergy a U e =
      ⨍ x in U, (1 / 2 : ℝ) * dot (h x - g x) ((a x).mulVec (h x - g x)) := by
  have hD := hw.sub hmin.1
  have hexp := integral_energy_add a hU e hmin.1.2.1 hD.2.1
  have h0 := hmin.integral_dot_eq_zero hU hD
  simp only [add_sub_cancel] at hexp
  rw [← hmin.2, trialEnergy_eq, trialEnergy_eq, setAverage_eq, smul_eq_mul, hexp, h0]
  ring

/-- **The quadratic response (1.13)**:
`½ ⨍_U |h - g|² ≤ ⨍_U ½ (p + h)·a(p + h) - μ(U, p) ≤ ½Λ ⨍_U |h - g|²`. -/
theorem IsDirichletMinimizer.quadraticResponse {a : CoefficientField d Λ} {U : Set (Vec d)}
    (hU : volume U ≠ ⊤) {e : Vec d} {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hmin : IsDirichletMinimizer a U e u g) {w : Vec d → ℝ} {h : Vec d → Vec d}
    (hw : H01 U w h) :
    (1 / 2 : ℝ) * ⨍ x in U, euclideanSq (h x - g x) ≤
        trialEnergy a U e h - dirichletEnergy a U e ∧
      trialEnergy a U e h - dirichletEnergy a U e ≤
        Λ / 2 * ⨍ x in U, euclideanSq (h x - g x) := by
  have := isFiniteMeasure_restrict.mpr hU
  have hD := hw.sub hmin.1
  have i1 := integrable_euclideanSq_of_memLp hD.2.1
  have i2 := (integrable_dot_mulVec a U hD.2.1).const_mul (1 / 2 : ℝ)
  have hVi : 0 ≤ (volume.real U)⁻¹ := inv_nonneg.mpr measureReal_nonneg
  rw [hmin.trialEnergy_sub_eq hU hw, setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul]
  constructor
  · have hle : ∫ x in U, (1 / 2 : ℝ) * euclideanSq (h x - g x) ≤
        ∫ x in U, (1 / 2 : ℝ) * dot (h x - g x) ((a x).mulVec (h x - g x)) :=
      integral_mono (i1.const_mul _) i2 fun x => by
        have := (a.elliptic x (h x - g x)).1
        simp only
        linarith
    rw [integral_const_mul (1 / 2 : ℝ) (fun x => euclideanSq (h x - g x))] at hle
    calc (1 / 2 : ℝ) * ((volume.real U)⁻¹ * ∫ x in U, euclideanSq (h x - g x))
        = (volume.real U)⁻¹ * ((1 / 2 : ℝ) * ∫ x in U, euclideanSq (h x - g x)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hle hVi
  · have hle : ∫ x in U, (1 / 2 : ℝ) * dot (h x - g x) ((a x).mulVec (h x - g x)) ≤
        ∫ x in U, Λ / 2 * euclideanSq (h x - g x) :=
      integral_mono i2 (i1.const_mul _) fun x => by
        have := (a.elliptic x (h x - g x)).2
        simp only
        linarith
    rw [integral_const_mul (Λ / 2) (fun x => euclideanSq (h x - g x))] at hle
    calc (volume.real U)⁻¹ * ∫ x in U, (1 / 2 : ℝ) * dot (h x - g x) ((a x).mulVec (h x - g x))
        ≤ (volume.real U)⁻¹ * (Λ / 2 * ∫ x in U, euclideanSq (h x - g x)) :=
          mul_le_mul_of_nonneg_left hle hVi
      _ = _ := by ring

/-- **Uniqueness of the minimizer**: two minimizers agree almost everywhere in `U`. -/
theorem IsDirichletMinimizer.ae_eq [NeZero d] {a : CoefficientField d Λ} {U : Set (Vec d)}
    (hU : Bornology.IsBounded U) {e : Vec d} {u₁ u₂ : Vec d → ℝ} {g₁ g₂ : Vec d → Vec d}
    (h₁ : IsDirichletMinimizer a U e u₁ g₁) (h₂ : IsDirichletMinimizer a U e u₂ g₂) :
    g₁ =ᵐ[volume.restrict U] g₂ ∧ u₁ =ᵐ[volume.restrict U] u₂ := by
  have hUt : volume U ≠ ⊤ := hU.measure_lt_top.ne
  rcases eq_or_ne (volume U) 0 with h0 | h0
  · rw [Measure.restrict_eq_zero.mpr h0]
    simp only [Filter.EventuallyEq, ae_zero, Filter.eventually_bot, and_self]
  have hV : 0 < volume.real U := ENNReal.toReal_pos h0 hUt
  have := isFiniteMeasure_restrict.mpr hUt
  have hD := h₂.1.sub h₁.1
  have hq := (h₁.quadraticResponse hUt h₂.1).1
  rw [h₂.2, sub_self, setAverage_eq, smul_eq_mul] at hq
  have hint : ∫ x in U, euclideanSq (g₂ x - g₁ x) = 0 := by
    have hnn : 0 ≤ ∫ x in U, euclideanSq (g₂ x - g₁ x) :=
      integral_nonneg fun x => euclideanSq_nonneg _
    have : (volume.real U)⁻¹ * ∫ x in U, euclideanSq (g₂ x - g₁ x) ≤ 0 := by linarith
    have hpos : 0 < (volume.real U)⁻¹ := inv_pos.mpr hV
    nlinarith
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => euclideanSq_nonneg _)
    (integrable_euclideanSq_of_memLp hD.2.1)).mp hint
  have hg : g₁ =ᵐ[volume.restrict U] g₂ := by
    filter_upwards [hae] with x hx
    have hx' : euclideanSq (g₂ x - g₁ x) = 0 := hx
    have hz : ∀ i, (g₂ x - g₁ x) i = 0 := fun i => by
      have := sq_apply_le_euclideanSq (g₂ x - g₁ x) i
      nlinarith [sq_nonneg ((g₂ x - g₁ x) i)]
    funext i
    have := hz i
    simp only [Pi.sub_apply] at this
    linarith
  refine ⟨hg, ?_⟩
  obtain ⟨R, hR, hUR⟩ := exists_subset_cube_of_isBounded hU
  have hP := setIntegral_sq_le_of_H01 0 hR hUR hD
  rw [hint, mul_zero] at hP
  have hu0 : ∫ x in U, (u₂ x - u₁ x) ^ 2 = 0 :=
    le_antisymm hP (integral_nonneg fun x => sq_nonneg _)
  have hae' := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _)
    hD.1.integrable_sq).mp hu0
  filter_upwards [hae'] with x hx
  have hx' : (u₂ x - u₁ x) ^ 2 = 0 := hx
  have := pow_eq_zero_iff (n := 2) (two_ne_zero) |>.mp hx'
  linarith

end QSH
