import QuantitativeStochasticHomogenization.Ch03.Sec03.GrowthIteration

/-!
# The growth iteration in the proof of (3.47), every `k`

Armstrong–Kuusi–Mourrat, proof of (3.47), Steps 1–3, for every `k`: the growth iteration of
`Ch03/Sec03/GrowthIteration.lean` with polynomials of degree `k + 1`. Along `r_j = r₀ θ^{-j}`, for a
solution `u` in `ℝ^d` with `r^{-(k+1)} ‖u‖_{L̲²(B_r)} → 0`, the growth exponent is lowered from `k + 1`
by `δ` finitely many times, and in the last step the parts of degree `k` of the approximating
polynomials converge in the finite-dimensional space of homogeneous `Ā`-harmonic polynomials of degree
`k` (`homogeneousHarmonic`), to `q` with `‖u - q‖_{L̲²(B_{r_j})} ≤ M r_j^σ`, `σ < k`
(`exists_homogeneous_growth`).
-/

open MeasureTheory Filter Set Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- Evaluation of polynomials, as a linear map. -/
def evalLinearMap : MvPolynomial (Fin d) ℝ →ₗ[ℝ] (Vec d → ℝ) where
  toFun P := fun x => MvPolynomial.eval x P
  map_add' P Q := by funext x; simp
  map_smul' c P := by funext x; simp

/-- The homogeneous `A`-harmonic polynomials of degree `k`, as a space of functions. -/
def homogeneousHarmonic (A : Mat d) (k : ℕ) : Submodule ℝ (Vec d → ℝ) where
  carrier := {f | f ∈ harmonicPolys A k ∧ ∃ P ∈ MvPolynomial.homogeneousSubmodule (Fin d) ℝ k,
    ∀ x, f x = MvPolynomial.eval x P}
  zero_mem' := ⟨zero_mem_harmonicPolys A k, 0, Submodule.zero_mem _, fun x => by simp⟩
  add_mem' := by
    rintro f g ⟨hf, P, hP, hfP⟩ ⟨hg, Q, hQ, hgQ⟩
    exact ⟨add_mem_harmonicPolys hf hg, P + Q, Submodule.add_mem _ hP hQ,
      fun x => by simp [hfP, hgQ]⟩
  smul_mem' := by
    rintro c f ⟨hf, P, hP, hfP⟩
    exact ⟨const_mul_mem_harmonicPolys hf c, c • P, Submodule.smul_mem _ c hP,
      fun x => by simp [hfP]⟩

theorem finiteDimensional_homogeneousHarmonic (A : Mat d) (k : ℕ) :
    FiniteDimensional ℝ (homogeneousHarmonic A k) := by
  have hfg : ((MvPolynomial.homogeneousSubmodule (Fin d) ℝ k).map
      (evalLinearMap (d := d))).FG := by
    rw [← MvPolynomial.homogeneousSubmodule_one_pow, MvPolynomial.homogeneousSubmodule_one_eq_span_X]
    exact ((Submodule.fg_span (Set.finite_range _)).pow k).map _
  have hle : homogeneousHarmonic A k ≤
      (MvPolynomial.homogeneousSubmodule (Fin d) ℝ k).map (evalLinearMap (d := d)) := by
    rintro f ⟨-, P, hP, hfP⟩
    exact ⟨P, hP, funext fun x => (hfP x).symm⟩
  have := (Submodule.fg_iff_finiteDimensional _).1 hfg
  exact Submodule.finiteDimensional_of_le hle

theorem homogeneousHarmonic_smul {A : Mat d} {k : ℕ} {f : Vec d → ℝ}
    (hf : f ∈ homogeneousHarmonic A k) (t : ℝ) (x : Vec d) : f (t • x) = t ^ k * f x := by
  obtain ⟨-, P, hP, hfP⟩ := hf
  rw [hfP, hfP]
  exact PDE.eval_smul_of_isHomogeneous hP t x

theorem memLp_of_mem_homogeneousHarmonic {A : Mat d} {k : ℕ} {f : Vec d → ℝ}
    (hf : f ∈ homogeneousHarmonic A k) (r : ℝ) :
    MemLp f 2 (volume.restrict (ball (0 : Vec d) r)) := by
  obtain ⟨-, P, -, hfP⟩ := hf
  rw [funext hfP]
  exact memLp_eval_ball P r

/-- An element of `homogeneousHarmonic A k` vanishing almost everywhere on `B_1` vanishes. -/
theorem eq_zero_of_mem_homogeneousHarmonic {A : Mat d} {k : ℕ} {f : Vec d → ℝ}
    (hf : f ∈ homogeneousHarmonic A k)
    (h0 : ∀ᵐ x ∂(volume.restrict (ball (0 : Vec d) 1)), f x = 0) : f = 0 := by
  have hcont : Continuous f := by
    obtain ⟨-, P, -, hfP⟩ := hf
    rw [funext hfP]
    exact MvPolynomial.continuous_eval P
  have hb : ball (0 : Vec d) 1 = PDE.euclideanBall 0 1 := ball_zero_eq_pdeEuclideanBall one_pos
  have heq : EqOn f (fun _ => (0 : ℝ)) (PDE.euclideanBall 0 1) := by
    refine Measure.eqOn_open_of_ae_eq (μ := (volume : Measure (Vec d))) ?_
      (PDE.isOpen_euclideanBall 0 1) hcont.continuousOn continuousOn_const
    rw [← hb]
    exact h0
  funext x
  obtain ⟨R, hR⟩ : ∃ R, R = euclideanNorm x + 1 := ⟨_, rfl⟩
  have hR0 : 0 < R := by rw [hR]; have := Real.sqrt_nonneg (euclideanSq x); unfold euclideanNorm; linarith
  have hxR : x ∈ ball (0 : Vec d) R := mem_ball_zero_iff'.2 (by rw [hR]; linarith)
  have ht : 0 < 1 / (2 * R) := by positivity
  have htx : (1 / (2 * R)) • x ∈ ball (0 : Vec d) 1 := by
    have h := Set.smul_mem_smul_set (a := 1 / (2 * R)) hxR
    rw [smul_ball_zero ht] at h
    refine ball_zero_subset_ball_zero ?_ h
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    linarith
  have h1 := heq (hb ▸ htx)
  rw [homogeneousHarmonic_smul hf] at h1
  have hpow : (1 / (2 * R)) ^ k ≠ 0 := pow_ne_zero _ ht.ne'
  simp only [Pi.zero_apply]
  exact (mul_eq_zero.1 h1).resolve_left hpow

/-- **Limits in `homogeneousHarmonic A k`**: a geometric Cauchy sequence for `‖·‖_{L̲²(B_1)}`
converges, with the tail bound. -/
theorem exists_limit_homogeneousHarmonic (A : Mat d) (k : ℕ) {q : ℕ → Vec d → ℝ}
    (hq : ∀ m, q m ∈ homogeneousHarmonic A k) {B ρ : ℝ} (hρ1 : ρ < 1)
    (hinc : ∀ m, scalarRms volume (ball 0 1) (fun x => q m x - q (m + 1) x) ≤ B * ρ ^ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Q ∈ homogeneousHarmonic A k, ∀ m,
      scalarRms volume (ball 0 1) (fun x => q m x - Q x) ≤ C * (B * ρ ^ m / (1 - ρ)) := by
  classical
  have := finiteDimensional_homogeneousHarmonic A k
  set V := homogeneousHarmonic A k with hV
  set b := Module.finBasis ℝ V
  set μ := volume.restrict (ball (0 : Vec d) 1) with hμ
  -- the coordinates
  let L : (Fin (Module.finrank ℝ V) → ℝ) →ₗ[ℝ] (Vec d → ℝ) :=
    V.subtype.comp b.equivFun.symm.toLinearMap
  have hLV : ∀ c, L c ∈ V := fun c => Submodule.coe_mem _
  have hmemL : ∀ c, MemLp (L c) 2 μ := fun c => memLp_of_mem_homogeneousHarmonic (hLV c) 1
  let T : (Fin (Module.finrank ℝ V) → ℝ) →ₗ[ℝ] Lp ℝ 2 μ :=
    { toFun := fun c => (hmemL c).toLp _
      map_add' := fun c c' => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => by rw [map_add])
      map_smul' := fun a c => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => by rw [map_smul]) }
  have hTc : ∀ c, T c = (hmemL c).toLp _ := fun c => rfl
  have hker : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    have hae : ∀ᵐ x ∂μ, L c x = 0 := by
      have h1 := MemLp.coeFn_toLp (hmemL c)
      rw [← hTc, hc] at h1
      filter_upwards [h1.symm.trans (Lp.coeFn_zero _ _ _)] with x hx
      exact hx
    have h0 := eq_zero_of_mem_homogeneousHarmonic (hLV c) hae
    have h1 : b.equivFun.symm c = 0 := Subtype.ext h0
    have h2 := congrArg b.equivFun h1
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h2
  obtain ⟨K, hK0, hK⟩ := T.exists_antilipschitzWith hker
  let T' := LinearMap.toContinuousLinearMap T
  have hvol : 0 < volume.real (ball (0 : Vec d) 1) := volume_real_ball_pos 0 one_pos
  set sv := Real.sqrt (volume.real (ball (0 : Vec d) 1))⁻¹ with hsv
  have hsv0 : 0 < sv := Real.sqrt_pos.2 (inv_pos.2 hvol)
  have hN : ∀ c, scalarRms volume (ball 0 1) (L c) = sv * ‖T c‖ := fun c => by
    rw [hTc]; exact scalarRms_eq_mul_norm_toLp (hmemL c)
  have hsvne : sv ≠ 0 := hsv0.ne'
  have hlow : ∀ c, ‖c‖ ≤ K / sv * scalarRms volume (ball 0 1) (L c) := fun c => by
    have h := hK.le_mul_dist c 0
    rw [map_zero, dist_zero_right, dist_zero_right] at h
    rw [hN]
    calc ‖c‖ ≤ K * ‖T c‖ := h
      _ = K / sv * (sv * ‖T c‖) := by field_simp
  have hupp : ∀ c, scalarRms volume (ball 0 1) (L c) ≤ sv * ‖T'‖ * ‖c‖ := fun c => by
    rw [hN, mul_assoc]
    exact mul_le_mul_of_nonneg_left (T'.le_opNorm c) hsv0.le
  -- the coordinates of `q m`
  set cq : ℕ → (Fin (Module.finrank ℝ V) → ℝ) := fun m => b.equivFun ⟨q m, hq m⟩
  have hqL : ∀ m, L (cq m) = q m := fun m => by
    show ((b.equivFun.symm (b.equivFun ⟨q m, hq m⟩) : V) : Vec d → ℝ) = q m
    rw [LinearEquiv.symm_apply_apply]
  have hdist : ∀ m, dist (cq m) (cq (m + 1)) ≤ (K / sv * B) * ρ ^ m := fun m => by
    rw [dist_eq_norm]
    have e : L (cq m - cq (m + 1)) = q m - q (m + 1) := by
      rw [map_sub, hqL, hqL]
    calc ‖cq m - cq (m + 1)‖ ≤ K / sv * scalarRms volume (ball 0 1) (L (cq m - cq (m + 1))) :=
          hlow _
      _ ≤ K / sv * (B * ρ ^ m) := by
          rw [e]; exact mul_le_mul_of_nonneg_left (hinc m) (div_nonneg (NNReal.coe_nonneg K) hsv0.le)
      _ = _ := by ring
  obtain ⟨cl, hcl⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric _ _ hρ1 hdist)
  refine ⟨sv * ‖T'‖ * (K / sv), mul_nonneg (mul_nonneg hsv0.le (norm_nonneg _))
    (div_nonneg (NNReal.coe_nonneg K) hsv0.le), L cl, hLV _, fun m => ?_⟩
  have h := dist_le_of_le_geometric_of_tendsto _ _ hρ1 hdist hcl m
  rw [dist_eq_norm] at h
  have e : L (cq m - cl) = q m - L cl := by
    rw [map_sub, hqL]
  calc scalarRms volume (ball 0 1) (fun x => q m x - L cl x)
      = scalarRms volume (ball 0 1) (L (cq m - cl)) := congrArg (scalarRms volume (ball 0 1)) e.symm
    _ ≤ sv * ‖T'‖ * ‖cq m - cl‖ := hupp _
    _ ≤ sv * ‖T'‖ * (K / sv * B * ρ ^ m / (1 - ρ)) :=
        mul_le_mul_of_nonneg_left h (mul_nonneg hsv0.le (norm_nonneg _))
    _ = _ := by ring
/-- (3.56)–(3.57) under a growth bound, every `k`: `‖u - Ā_{k+1}‖_{L̲²(B_{r_j})} ≤ C r_j^{β-δ}`. -/
theorem flatness_le_of_growth_k {Λ : ℝ} {a : CoefficientField d Λ} {A : Mat d}
    {θ C₅ δ X r₀ M β : ℝ} {k : ℕ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hC₅ : 0 ≤ C₅) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hX1 : 1 ≤ X) (hXr : X ≤ r₀)
    (H50 : ∀ r : ℝ, X ≤ r → ∀ v, IsSolutionBall a r v →
      harmonicFlatness A (k + 1) v (θ * r) ≤
        1 / 4 * θ ^ (((k + 1 : ℕ) : ℝ) + 1 - δ / 2) * harmonicFlatness A (k + 1) v r +
          C₅ * r ^ (-δ) * scalarRms volume (ball 0 r) v)
    {u : Vec d → ℝ} (hsol : ∀ R : ℝ, 0 < R → IsSolutionBall a R u) (hM : 0 ≤ M) (hβ2 : β ≤ (k : ℝ) + 1)
    (hgrow : ∀ j : ℕ, scalarRms volume (ball 0 (r₀ / θ ^ j)) u ≤ M * (r₀ / θ ^ j) ^ β)
    (j : ℕ) :
    harmonicFlatness A (k + 1) u (r₀ / θ ^ j) ≤
      4 / 3 * (C₅ * M * θ ^ (-(β - δ))) * (r₀ / θ ^ j) ^ (β - δ) := by
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = β - δ := ⟨_, rfl⟩
  rw [← hσ]
  have hr₀ : 0 < r₀ := by linarith
  have hr : ∀ j : ℕ, 0 < r₀ / θ ^ j := fun j => div_pos hr₀ (pow_pos hθ0 j)
  have hrX : ∀ j : ℕ, X ≤ r₀ / θ ^ j := fun j => by
    rw [le_div_iff₀ (pow_pos hθ0 j)]
    have : θ ^ j ≤ 1 := pow_le_one₀ hθ0.le hθ1.le
    nlinarith
  have hsucc : ∀ j : ℕ, θ * (r₀ / θ ^ (j + 1)) = r₀ / θ ^ j := fun j => by
    rw [pow_succ]
    field_simp
  have hrσ : ∀ j : ℕ, 0 < (r₀ / θ ^ j) ^ σ := fun j => Real.rpow_pos_of_pos (hr j) σ
  obtain ⟨y, hy⟩ : ∃ y : ℕ → ℝ, ∀ j, y j = harmonicFlatness A (k + 1) u (r₀ / θ ^ j) / (r₀ / θ ^ j) ^ σ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = 1 / 4 * θ ^ (((k + 1 : ℕ) : ℝ) + 1 - δ / 2 - σ) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = C₅ * M * θ ^ (-σ) := ⟨_, rfl⟩
  have hθe : ∀ e : ℝ, 0 ≤ e → θ ^ e ≤ 1 := fun e he => Real.rpow_le_one hθ0.le hθ1.le he
  have hl0 : 0 ≤ l := by rw [hl]; have := Real.rpow_nonneg hθ0.le (((k + 1 : ℕ) : ℝ) + 1 - δ / 2 - σ); positivity
  have hl4 : l ≤ 1 / 4 := by
    have := hθe (((k + 1 : ℕ) : ℝ) + 1 - δ / 2 - σ) (by rw [hσ]; push_cast; linarith)
    rw [hl]
    linarith
  have hK0 : 0 ≤ K := by rw [hK]; exact mul_nonneg (mul_nonneg hC₅ hM) (Real.rpow_nonneg hθ0.le _)
  have hrec : ∀ j, y j ≤ l * y (j + 1) + K := by
    intro j
    have h1 := H50 (r₀ / θ ^ (j + 1)) (hrX (j + 1)) u (hsol _ (hr (j + 1)))
    rw [hsucc j] at h1
    have h2 : (r₀ / θ ^ (j + 1)) ^ (-δ) * scalarRms volume (ball 0 (r₀ / θ ^ (j + 1))) u ≤
        M * (r₀ / θ ^ (j + 1)) ^ σ := by
      calc _ ≤ (r₀ / θ ^ (j + 1)) ^ (-δ) * (M * (r₀ / θ ^ (j + 1)) ^ β) :=
            mul_le_mul_of_nonneg_left (hgrow (j + 1)) (Real.rpow_nonneg (hr _).le _)
        _ = M * (r₀ / θ ^ (j + 1)) ^ σ := by
            rw [hσ, sub_eq_neg_add, Real.rpow_add (hr _)]
            ring
    have e1 : (r₀ / θ ^ (j + 1)) ^ σ = (r₀ / θ ^ j) ^ σ * θ ^ (-σ) := by
      rw [radius_rpow hθ0 hr₀, radius_rpow hθ0 hr₀, pow_succ]
      ring
    have e2 : θ ^ (((k + 1 : ℕ) : ℝ) + 1 - δ / 2) = θ ^ (((k + 1 : ℕ) : ℝ) + 1 - δ / 2 - σ) * θ ^ σ := by
      rw [← Real.rpow_add hθ0]
      congr 1
      ring
    have e3 : harmonicFlatness A (k + 1) u (r₀ / θ ^ (j + 1)) = y (j + 1) * (r₀ / θ ^ (j + 1)) ^ σ := by
      rw [hy, div_mul_cancel₀ _ (hrσ (j + 1)).ne']
    have e4 : θ ^ σ * θ ^ (-σ) = 1 := by
      rw [← Real.rpow_add hθ0, add_neg_cancel, Real.rpow_zero]
    rw [hy, div_le_iff₀ (hrσ j)]
    calc harmonicFlatness A (k + 1) u (r₀ / θ ^ j)
        ≤ 1 / 4 * θ ^ (((k + 1 : ℕ) : ℝ) + 1 - δ / 2) * harmonicFlatness A (k + 1) u (r₀ / θ ^ (j + 1)) +
          C₅ * ((r₀ / θ ^ (j + 1)) ^ (-δ) * scalarRms volume (ball 0 (r₀ / θ ^ (j + 1))) u) := by
          rw [← mul_assoc C₅]; exact h1
      _ ≤ 1 / 4 * θ ^ (((k + 1 : ℕ) : ℝ) + 1 - δ / 2) * harmonicFlatness A (k + 1) u (r₀ / θ ^ (j + 1)) +
          C₅ * (M * (r₀ / θ ^ (j + 1)) ^ σ) :=
          add_le_add (le_refl _) (mul_le_mul_of_nonneg_left h2 hC₅)
      _ = (l * y (j + 1) + K) * (r₀ / θ ^ j) ^ σ := by
          rw [e3, e1, e2, hl, hK]
          linear_combination (1 / 4 * θ ^ (((k + 1 : ℕ) : ℝ) + 1 - δ / 2 - σ) * y (j + 1) *
            (r₀ / θ ^ j) ^ σ) * e4
  have hflat0 : ∀ j, harmonicFlatness A (k + 1) u (r₀ / θ ^ j) ≤
      scalarRms volume (ball 0 (r₀ / θ ^ j)) u := by
    intro j
    have := harmonicFlatness_le (A := A) (k := k + 1) u (r₀ / θ ^ j) (zero_mem_harmonicPolys A (k + 1))
    simpa using this
  have hB : ∀ j, y j ≤ (M * r₀ ^ δ) * (θ ^ (-δ)) ^ j := by
    intro j
    rw [hy, div_le_iff₀ (hrσ j)]
    have e : (M * r₀ ^ δ) * (θ ^ (-δ)) ^ j * (r₀ / θ ^ j) ^ σ = M * (r₀ / θ ^ j) ^ β := by
      rw [mul_assoc M, ← radius_rpow hθ0 hr₀, mul_assoc, ← Real.rpow_add (hr j), hσ]
      congr 2
      ring
    rw [e]
    exact (hflat0 j).trans (hgrow j)
  have hlρ : l * θ ^ (-δ) < 1 := by
    have e : l * θ ^ (-δ) = 1 / 4 * θ ^ (((k + 1 : ℕ) : ℝ) + 1 - δ / 2 - σ + -δ) := by
      rw [hl, mul_assoc, ← Real.rpow_add hθ0]
    rw [e]
    have := hθe (((k + 1 : ℕ) : ℝ) + 1 - δ / 2 - σ + -δ) (by rw [hσ]; push_cast; linarith)
    linarith
  have hyj := le_of_le_mul_succ_add hl0 (by linarith) hK0 (Real.rpow_nonneg hθ0.le _) hlρ hrec hB j
  have h43 : K / (1 - l) ≤ 4 / 3 * K := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hl4 hK0]
  rw [hy, div_le_iff₀ (hrσ j)] at hyj
  rw [← hK]
  calc _ ≤ K / (1 - l) * (r₀ / θ ^ j) ^ σ := hyj
    _ ≤ 4 / 3 * K * (r₀ / θ ^ j) ^ σ := mul_le_mul_of_nonneg_right h43 (hrσ j).le

/-- **One step of the growth iteration** (Steps 1–2 of the proof of (3.47), every `k`). -/
theorem growth_core_k {Λ : ℝ} {a : CoefficientField d Λ} {A : Mat d} {θ C₅ δ X r₀ M β : ℝ}
    {k : ℕ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hC₅ : 0 ≤ C₅) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hX1 : 1 ≤ X) (hXr : X ≤ r₀)
    (H50 : ∀ r : ℝ, X ≤ r → ∀ v, IsSolutionBall a r v →
      harmonicFlatness A (k + 1) v (θ * r) ≤
        1 / 4 * θ ^ (((k + 1 : ℕ) : ℝ) + 1 - δ / 2) * harmonicFlatness A (k + 1) v r +
          C₅ * r ^ (-δ) * scalarRms volume (ball 0 r) v)
    {u : Vec d → ℝ} (hsol : ∀ R : ℝ, 0 < R → IsSolutionBall a R u)
    (hu2 : Tendsto (fun r : ℝ => (r ^ (k + 1))⁻¹ * scalarRms volume (ball 0 r) u) atTop (𝓝 0))
    (hM : 0 ≤ M) (hβ2 : β ≤ (k : ℝ) + 1)
    (hgrow : ∀ j : ℕ, scalarRms volume (ball 0 (r₀ / θ ^ j)) u ≤ M * (r₀ / θ ^ j) ^ β) :
    ∃ (P : ℕ → MvPolynomial (Fin d) ℝ) (K : ℝ), 0 ≤ K ∧ ∀ j : ℕ, (P j).totalDegree ≤ k + 1 ∧
      (fun x => MvPolynomial.eval x (P j)) ∈ harmonicPolys A (k + 1) ∧
      scalarRms volume (ball 0 (r₀ / θ ^ j)) (fun x => u x - MvPolynomial.eval x (P j)) ≤
        K * (r₀ / θ ^ j) ^ (β - δ) ∧
      scalarRms volume (ball 0 1)
          (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent (k + 1) (P j))) ≤
        K * (r₀ / θ ^ j) ^ (β - δ - (k + 1)) ∧
      ∀ m : ℕ, m ≤ k → scalarRms volume (ball 0 1)
          (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m (P j)) -
            MvPolynomial.eval x (MvPolynomial.homogeneousComponent m (P (j + 1)))) ≤
        K * (r₀ / θ ^ j) ^ (β - δ - m) := by
  have hr₀ : 0 < r₀ := by linarith
  have hr : ∀ j : ℕ, 0 < r₀ / θ ^ j := fun j => div_pos hr₀ (pow_pos hθ0 j)
  have hrmono : ∀ j : ℕ, r₀ / θ ^ j ≤ r₀ / θ ^ (j + 1) := fun j =>
    div_le_div_of_nonneg_left hr₀.le (pow_pos hθ0 (j + 1))
      (pow_le_pow_of_le_one hθ0.le hθ1.le (Nat.le_succ j))
  have hratio : ∀ j : ℕ, (r₀ / θ ^ (j + 1)) / (r₀ / θ ^ j) = θ⁻¹ := fun j => by
    rw [pow_succ]
    field_simp
  have hF := flatness_le_of_growth_k (A := A) hθ0 hθ1 hC₅ hδ0 hδ1 hX1 hXr H50 hsol hM hβ2 hgrow
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = β - δ := ⟨_, rfl⟩
  rw [← hσ]
  rw [← hσ] at hF
  have hσ2 : σ < (k : ℝ) + 1 := by rw [hσ]; linarith
  obtain ⟨KF, hKF⟩ : ∃ KF, KF = 4 / 3 * (C₅ * M * θ ^ (-σ)) := ⟨_, rfl⟩
  have hKF0 : 0 ≤ KF := by
    rw [hKF]
    exact mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hC₅ hM) (Real.rpow_nonneg hθ0.le _))
  rw [← hKF] at hF
  -- near-minimizers in `Ā_{k+1}`
  have hex : ∀ j : ℕ, ∃ p ∈ harmonicPolys A (k + 1), scalarRms volume (ball 0 (r₀ / θ ^ j))
      (fun x => u x - p x) < harmonicFlatness A (k + 1) u (r₀ / θ ^ j) + (r₀ / θ ^ j) ^ σ :=
    fun j => exists_lt_harmonicFlatness A (k + 1) u _ (Real.rpow_pos_of_pos (hr j) σ)
  choose p hpA hpe using hex
  choose P hPdeg hPe using fun j => (hpA j).1
  have hmemP : ∀ j (R : ℝ), MemLp (fun x => MvPolynomial.eval x (P j)) 2
      (volume.restrict (ball (0 : Vec d) R)) := fun j R => memLp_eval_ball (P j) R
  have hmemu : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball (0 : Vec d) R)) :=
    fun R hR => (hsol R hR).1
  have he : ∀ j : ℕ, scalarRms volume (ball 0 (r₀ / θ ^ j))
      (fun x => u x - MvPolynomial.eval x (P j)) ≤ (KF + 1) * (r₀ / θ ^ j) ^ σ := by
    intro j
    have e : (fun x => u x - MvPolynomial.eval x (P j)) = fun x => u x - p j x :=
      funext fun x => by rw [hPe j x]
    rw [e]
    have h1 := hpe j
    have h2 := hF j
    linarith
  -- increments of the polynomials
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = Real.sqrt ((θ⁻¹) ^ d) := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by rw [hκ]; exact Real.sqrt_nonneg _
  have hθσ : 0 ≤ θ ^ (-σ) := Real.rpow_nonneg hθ0.le _
  obtain ⟨KD, hKD⟩ : ∃ KD, KD = (KF + 1) * (1 + κ * θ ^ (-σ)) := ⟨_, rfl⟩
  have hKD0 : 0 ≤ KD := by
    rw [hKD]
    exact mul_nonneg (by linarith) (by have := mul_nonneg hκ0 hθσ; linarith)
  have hrσsucc : ∀ j : ℕ, (r₀ / θ ^ (j + 1)) ^ σ = (r₀ / θ ^ j) ^ σ * θ ^ (-σ) := fun j => by
    rw [radius_rpow hθ0 hr₀, radius_rpow hθ0 hr₀, pow_succ]
    ring
  have hdiff : ∀ j : ℕ, scalarRms volume (ball 0 (r₀ / θ ^ j))
      (fun x => MvPolynomial.eval x (P j) - MvPolynomial.eval x (P (j + 1))) ≤
        KD * (r₀ / θ ^ j) ^ σ := by
    intro j
    have h1 : scalarRms volume (ball 0 (r₀ / θ ^ j))
        (fun x => u x - MvPolynomial.eval x (P (j + 1))) ≤
        κ * scalarRms volume (ball 0 (r₀ / θ ^ (j + 1)))
          (fun x => u x - MvPolynomial.eval x (P (j + 1))) := by
      have h := scalarRms_ball_le (f := fun x => u x - MvPolynomial.eval x (P (j + 1))) (hr j)
        (hrmono j) ((hmemu _ (hr (j + 1))).sub (hmemP (j + 1) _))
      rwa [hratio j, ← hκ] at h
    have h2 : scalarRms volume (ball 0 (r₀ / θ ^ j))
        (fun x => MvPolynomial.eval x (P j) - MvPolynomial.eval x (P (j + 1))) ≤
        scalarRms volume (ball 0 (r₀ / θ ^ j)) (fun x => u x - MvPolynomial.eval x (P (j + 1))) +
        scalarRms volume (ball 0 (r₀ / θ ^ j)) (fun x => u x - MvPolynomial.eval x (P j)) := by
      calc _ = scalarRms volume (ball 0 (r₀ / θ ^ j))
            (fun x => (u x - MvPolynomial.eval x (P (j + 1))) -
              (u x - MvPolynomial.eval x (P j))) := by
            congr 1
            funext x
            ring
        _ ≤ _ := scalarRms_sub_le (f := fun x => u x - MvPolynomial.eval x (P (j + 1)))
            (g := fun x => u x - MvPolynomial.eval x (P j))
            ((hmemu _ (hr j)).sub (hmemP (j + 1) _)) ((hmemu _ (hr j)).sub (hmemP j _))
    have h4 := he (j + 1)
    rw [hrσsucc j] at h4
    have e : κ * ((KF + 1) * ((r₀ / θ ^ j) ^ σ * θ ^ (-σ))) + (KF + 1) * (r₀ / θ ^ j) ^ σ =
        KD * (r₀ / θ ^ j) ^ σ := by
      rw [hKD]
      ring
    calc _ ≤ _ := h2
      _ ≤ κ * ((KF + 1) * ((r₀ / θ ^ j) ^ σ * θ ^ (-σ))) + (KF + 1) * (r₀ / θ ^ j) ^ σ :=
          add_le_add (h1.trans (mul_le_mul_of_nonneg_left h4 hκ0)) (he j)
      _ = _ := e
  -- homogeneous parts of the increments, by (3.27)
  obtain ⟨C27, hC27, h27⟩ := scalarRms_homogeneousComponents_zero (d := d) (k + 1)
  have hcomp : ∀ j : ℕ, ∀ m ∈ Finset.range (k + 2), (r₀ / θ ^ j) ^ m * scalarRms volume (ball 0 1)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m (P j)) -
        MvPolynomial.eval x (MvPolynomial.homogeneousComponent m (P (j + 1)))) ≤
        C27 * KD * (r₀ / θ ^ j) ^ σ := by
    intro j m hm
    have hD : (P j - P (j + 1)).totalDegree ≤ k + 1 :=
      (MvPolynomial.totalDegree_sub _ _).trans (max_le (hPdeg j) (hPdeg (j + 1)))
    have h2 := (h27 (P j - P (j + 1)) hD _ (hr j)).2
    have hsingle := Finset.single_le_sum (f := fun m => scalarRms volume (ball 0 (r₀ / θ ^ j))
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m (P j - P (j + 1)))))
      (fun i _ => scalarRms_nonneg _ _) hm
    beta_reduce at hsingle
    rw [scalarRms_ball_homogeneousComponent m _ (hr j)] at hsingle
    have e1 : (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m (P j - P (j + 1)))) =
        fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m (P j)) -
          MvPolynomial.eval x (MvPolynomial.homogeneousComponent m (P (j + 1))) := by
      funext x
      rw [map_sub, map_sub]
    have e2 : (fun x => MvPolynomial.eval x (P j - P (j + 1))) =
        fun x => MvPolynomial.eval x (P j) - MvPolynomial.eval x (P (j + 1)) := by
      funext x
      rw [map_sub]
    rw [e1] at hsingle
    rw [e2] at h2
    calc _ ≤ _ := hsingle
      _ ≤ C27 * scalarRms volume (ball 0 (r₀ / θ ^ j))
          (fun x => MvPolynomial.eval x (P j) - MvPolynomial.eval x (P (j + 1))) := h2
      _ ≤ C27 * (KD * (r₀ / θ ^ j) ^ σ) := mul_le_mul_of_nonneg_left (hdiff j) hC27
      _ = _ := by ring
  have hinc : ∀ m ∈ Finset.range (k + 2), ∀ j : ℕ, scalarRms volume (ball 0 1)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m (P j)) -
        MvPolynomial.eval x (MvPolynomial.homogeneousComponent m (P (j + 1)))) ≤
        C27 * KD * (r₀ / θ ^ j) ^ (σ - m) :=
    fun m hm j => le_mul_rpow_sub_of_pow_mul_le (hr j) (hcomp j m hm)
  -- the part of degree two
  obtain ⟨aq, haq⟩ : ∃ aq : ℕ → ℝ, ∀ j, aq j = scalarRms volume (ball 0 1)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent (k + 1) (P j))) :=
    ⟨_, fun _ => rfl⟩
  have hmem1 : ∀ m j, MemLp (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m (P j)))
      2 (volume.restrict (ball (0 : Vec d) 1)) := fun m j => memLp_eval_ball _ 1
  have hθ2σ : θ ^ ((k : ℝ) + 1 - σ) < 1 := Real.rpow_lt_one hθ0.le hθ1 (by linarith)
  have hθ2σ0 : 0 ≤ θ ^ ((k : ℝ) + 1 - σ) := Real.rpow_nonneg hθ0.le _
  have hr2 : ∀ j : ℕ, (r₀ / θ ^ j) ^ (σ - (k + 1)) = r₀ ^ (σ - (k + 1)) * (θ ^ ((k : ℝ) + 1 - σ)) ^ j := fun j => by
    rw [radius_rpow hθ0 hr₀, neg_sub]
  have hdist : ∀ j, dist (aq j) (aq (j + 1)) ≤ (C27 * KD * r₀ ^ (σ - (k + 1))) * (θ ^ ((k : ℝ) + 1 - σ)) ^ j := by
    intro j
    have h := hinc (k + 1) (by simp) j
    push_cast at h
    rw [hr2] at h
    rw [Real.dist_eq, haq, haq]
    exact (abs_scalarRms_sub_le (hmem1 (k + 1) j) (hmem1 (k + 1) (j + 1))).trans (h.trans_eq (by ring))
  have hrtend : Tendsto (fun j : ℕ => r₀ / θ ^ j) atTop atTop := by
    have h := (tendsto_pow_atTop_atTop_of_one_lt ((one_lt_inv₀ hθ0).2 hθ1)).const_mul_atTop hr₀
    refine h.congr fun j => ?_
    rw [inv_pow, div_eq_mul_inv]
  have haq0 : Tendsto aq atTop (𝓝 0) := by
    have hup : ∀ j, aq j ≤ C27 * (((r₀ / θ ^ j) ^ (k + 1))⁻¹ * scalarRms volume (ball 0 (r₀ / θ ^ j)) u) +
        C27 * (KF + 1) * r₀ ^ (σ - (k + 1)) * (θ ^ ((k : ℝ) + 1 - σ)) ^ j := by
      intro j
      have hD := (h27 (P j) (hPdeg j) _ (hr j)).2
      have hsingle := Finset.single_le_sum (f := fun m => scalarRms volume (ball 0 (r₀ / θ ^ j))
        (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m (P j))))
        (fun i _ => scalarRms_nonneg _ _) (by simp : k + 1 ∈ Finset.range (k + 2))
      beta_reduce at hsingle
      rw [scalarRms_ball_homogeneousComponent (k + 1) _ (hr j), ← haq j] at hsingle
      have hp := scalarRms_le_add_of_sub (hmemu _ (hr j)) (hmemP j (r₀ / θ ^ j))
      have h3 : (r₀ / θ ^ j) ^ (k + 1) * aq j ≤
          C27 * (scalarRms volume (ball 0 (r₀ / θ ^ j)) u + (KF + 1) * (r₀ / θ ^ j) ^ σ) :=
        (hsingle.trans hD).trans (mul_le_mul_of_nonneg_left (hp.trans (add_le_add (le_refl _) (he j)))
          hC27)
      have hr2' : 0 < (r₀ / θ ^ j) ^ (k + 1) := pow_pos (hr j) (k + 1)
      have e : (r₀ / θ ^ j) ^ σ / (r₀ / θ ^ j) ^ (k + 1) = r₀ ^ (σ - (k + 1)) * (θ ^ ((k : ℝ) + 1 - σ)) ^ j := by
        rw [← hr2, Real.rpow_sub (hr j),
          show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
      rw [← le_div_iff₀' hr2'] at h3
      calc aq j ≤ _ := h3
        _ = C27 * (((r₀ / θ ^ j) ^ (k + 1))⁻¹ * scalarRms volume (ball 0 (r₀ / θ ^ j)) u) +
            C27 * (KF + 1) * ((r₀ / θ ^ j) ^ σ / (r₀ / θ ^ j) ^ (k + 1)) := by
          field_simp
        _ = _ := by rw [e]; ring
    have hlim : Tendsto (fun j : ℕ => C27 * (((r₀ / θ ^ j) ^ (k + 1))⁻¹ *
        scalarRms volume (ball 0 (r₀ / θ ^ j)) u) +
        C27 * (KF + 1) * r₀ ^ (σ - (k + 1)) * (θ ^ ((k : ℝ) + 1 - σ)) ^ j) atTop (𝓝 0) := by
      have h1 := (hu2.comp hrtend).const_mul C27
      have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one hθ2σ0 hθ2σ).const_mul
        (C27 * (KF + 1) * r₀ ^ (σ - (k + 1)))
      simpa [Function.comp_def] using h1.add h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun j => ?_) hup
    rw [haq]
    exact scalarRms_nonneg _ _
  have htail : ∀ j, aq j ≤ C27 * KD / (1 - θ ^ ((k : ℝ) + 1 - σ)) * (r₀ / θ ^ j) ^ (σ - (k + 1)) := by
    intro j
    have h := dist_le_of_le_geometric_of_tendsto (θ ^ ((k : ℝ) + 1 - σ)) (C27 * KD * r₀ ^ (σ - (k + 1))) hθ2σ
      hdist haq0 j
    rw [Real.dist_eq, sub_zero] at h
    rw [hr2]
    calc aq j ≤ |aq j| := le_abs_self _
      _ ≤ _ := h
      _ = _ := by ring
  -- the constant
  have h1θ : 0 < 1 - θ ^ ((k : ℝ) + 1 - σ) := by linarith
  refine ⟨P, (KF + 1) + C27 * KD + C27 * KD / (1 - θ ^ ((k : ℝ) + 1 - σ)),
    by have := mul_nonneg hC27 hKD0; have := div_nonneg this h1θ.le; linarith, fun j => ?_⟩
  have hc1 : KF + 1 ≤ (KF + 1) + C27 * KD + C27 * KD / (1 - θ ^ ((k : ℝ) + 1 - σ)) := by
    have := mul_nonneg hC27 hKD0; have := div_nonneg this h1θ.le; linarith
  have hc2 : C27 * KD ≤ (KF + 1) + C27 * KD + C27 * KD / (1 - θ ^ ((k : ℝ) + 1 - σ)) := by
    have := div_nonneg (mul_nonneg hC27 hKD0) h1θ.le; linarith
  have hc3 : C27 * KD / (1 - θ ^ ((k : ℝ) + 1 - σ)) ≤
      (KF + 1) + C27 * KD + C27 * KD / (1 - θ ^ ((k : ℝ) + 1 - σ)) := by
    have := mul_nonneg hC27 hKD0; linarith
  have hnn : ∀ e : ℝ, 0 ≤ (r₀ / θ ^ j) ^ e := fun e => Real.rpow_nonneg (hr j).le e
  have hPA : (fun x => MvPolynomial.eval x (P j)) ∈ harmonicPolys A (k + 1) := by
    have e : (fun x => MvPolynomial.eval x (P j)) = p j := funext fun x => (hPe j x).symm
    rw [e]
    exact hpA j
  refine ⟨hPdeg j, hPA, (he j).trans (mul_le_mul_of_nonneg_right hc1 (hnn _)), ?_, fun m hm => ?_⟩
  · rw [← haq]
    exact (htail j).trans (mul_le_mul_of_nonneg_right hc3 (hnn _))
  · have h := hinc m (Finset.mem_range.2 (by omega)) j
    exact h.trans (mul_le_mul_of_nonneg_right hc2 (hnn _))

theorem scalarRms_le_sum_homogeneous {Q : MvPolynomial (Fin d) ℝ} {n : ℕ} (hQ : Q.totalDegree ≤ n)
    {r : ℝ} (hr : 0 < r) :
    scalarRms volume (ball 0 r) (fun x => MvPolynomial.eval x Q) ≤
      ∑ m ∈ Finset.range (n + 1), r ^ m * scalarRms volume (ball 0 1)
        (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent m Q)) := by
  obtain ⟨C, -, h⟩ := scalarRms_homogeneousComponents_zero (d := d) n
  exact ((h Q hQ r hr).1).trans (le_of_eq (Finset.sum_congr rfl fun m _ =>
    scalarRms_ball_homogeneousComponent m Q hr))

/-- The parts of degree `i < σ` of the approximating polynomials grow at most like `r_j^{σ-i}`. -/
theorem drift_of_increments {θ r₀ K σ : ℝ} {P : ℕ → MvPolynomial (Fin d) ℝ} {i : ℕ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hr₀ : 0 < r₀) (hK : 0 ≤ K) (hσi : (i : ℝ) < σ)
    (hinc : ∀ j, scalarRms volume (ball 0 1)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent i (P j)) -
        MvPolynomial.eval x (MvPolynomial.homogeneousComponent i (P (j + 1)))) ≤
      K * (r₀ / θ ^ j) ^ (σ - i)) (j : ℕ) :
    scalarRms volume (ball 0 1)
        (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent i (P j))) ≤
      scalarRms volume (ball 0 1)
          (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent i (P 0))) +
        K / (θ ^ (-(σ - i)) - 1) * (r₀ / θ ^ j) ^ (σ - i) := by
  have hρ : 1 < θ ^ (-(σ - i)) := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hθ0 hθ1 (by linarith)
  have hstep : ∀ j, scalarRms volume (ball 0 1)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent i (P (j + 1)))) ≤
      scalarRms volume (ball 0 1)
        (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent i (P j))) +
      (K * r₀ ^ (σ - i)) * (θ ^ (-(σ - i))) ^ j := by
    intro j
    have h := scalarRms_le_add_of_sub (memLp_eval_ball (MvPolynomial.homogeneousComponent i (P j)) 1)
      (memLp_eval_ball (MvPolynomial.homogeneousComponent i (P (j + 1))) 1)
    have hb := hinc j
    rw [radius_rpow hθ0 hr₀] at hb
    linarith
  have h := le_add_geom_of_succ_le (x := fun j => scalarRms volume (ball 0 1)
    (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent i (P j))))
    (mul_nonneg hK (Real.rpow_nonneg hr₀.le _)) hρ hstep j
  rw [radius_rpow hθ0 hr₀]
  calc _ ≤ _ := h
    _ = _ := by ring

/-- `Σ_{i < n} r^i x_i ≤ (Σ_{i < n} (y_i + c_i)) r^σ` when `x_i ≤ y_i + c_i r^{σ-i}`, `n - 1 < σ`. -/
theorem sum_pow_mul_le {r σ : ℝ} {n : ℕ} (hr : 1 ≤ r) (hσ : (n : ℝ) - 1 ≤ σ) {x y c : ℕ → ℝ}
    (hy : ∀ i, 0 ≤ y i) (hx : ∀ i ∈ Finset.range n, x i ≤ y i + c i * r ^ (σ - i)) :
    ∑ i ∈ Finset.range n, r ^ i * x i ≤ (∑ i ∈ Finset.range n, (y i + c i)) * r ^ σ := by
  have hr0 : 0 < r := by linarith
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hin : (i : ℝ) ≤ σ := by
    have : i + 1 ≤ n := Finset.mem_range.1 hi
    have : (i : ℝ) + 1 ≤ n := by exact_mod_cast this
    linarith
  have hri : r ^ i ≤ r ^ σ := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hr hin
  have e : r ^ i * r ^ (σ - i) = r ^ σ := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hr0]
    congr 1
    ring
  have hpi : 0 ≤ r ^ i := pow_nonneg hr0.le i
  calc r ^ i * x i ≤ r ^ i * (y i + c i * r ^ (σ - i)) := mul_le_mul_of_nonneg_left (hx i hi) hpi
    _ = r ^ i * y i + c i * (r ^ i * r ^ (σ - i)) := by ring
    _ ≤ r ^ σ * y i + c i * r ^ σ := by
        rw [e]
        have := mul_le_mul_of_nonneg_right hri (hy i)
        linarith
    _ = (y i + c i) * r ^ σ := by ring

/-- The growth iteration when `β - δ > k`: the growth exponent improves from `β` to `β - δ`. -/
theorem growth_step_large_k {Λ : ℝ} {a : CoefficientField d Λ} {A : Mat d} {θ C₅ δ X r₀ M β : ℝ}
    {k : ℕ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hC₅ : 0 ≤ C₅) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hX1 : 1 ≤ X) (hXr : X ≤ r₀)
    (H50 : ∀ r : ℝ, X ≤ r → ∀ v, IsSolutionBall a r v →
      harmonicFlatness A (k + 1) v (θ * r) ≤
        1 / 4 * θ ^ (((k + 1 : ℕ) : ℝ) + 1 - δ / 2) * harmonicFlatness A (k + 1) v r +
          C₅ * r ^ (-δ) * scalarRms volume (ball 0 r) v)
    {u : Vec d → ℝ} (hsol : ∀ R : ℝ, 0 < R → IsSolutionBall a R u)
    (hu2 : Tendsto (fun r : ℝ => (r ^ (k + 1))⁻¹ * scalarRms volume (ball 0 r) u) atTop (𝓝 0))
    (hM : 0 ≤ M) (hβ2 : β ≤ (k : ℝ) + 1) (hσ1 : (k : ℝ) < β - δ)
    (hgrow : ∀ j : ℕ, scalarRms volume (ball 0 (r₀ / θ ^ j)) u ≤ M * (r₀ / θ ^ j) ^ β) :
    ∃ M' : ℝ, 0 ≤ M' ∧
      ∀ j : ℕ, scalarRms volume (ball 0 (r₀ / θ ^ j)) u ≤ M' * (r₀ / θ ^ j) ^ (β - δ) := by
  obtain ⟨P, K, hK, hP⟩ := growth_core_k (A := A) hθ0 hθ1 hC₅ hδ0 hδ1 hX1 hXr H50 hsol hu2 hM
    hβ2 hgrow
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = β - δ := ⟨_, rfl⟩
  rw [← hσ] at hP hσ1 ⊢
  have hr₀ : 0 < r₀ := by linarith
  have hr : ∀ j : ℕ, 0 < r₀ / θ ^ j := fun j => div_pos hr₀ (pow_pos hθ0 j)
  have hr1 : ∀ j : ℕ, 1 ≤ r₀ / θ ^ j := fun j => by
    rw [le_div_iff₀ (pow_pos hθ0 j)]
    have : θ ^ j ≤ 1 := pow_le_one₀ hθ0.le hθ1.le
    nlinarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ → ℕ → ℝ, ∀ i j, N i j = scalarRms volume (ball 0 1)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent i (P j))) :=
    ⟨_, fun _ _ => rfl⟩
  refine ⟨2 * K + ∑ i ∈ Finset.range (k + 1), (N i 0 + max 0 (K / (θ ^ (-(σ - i)) - 1))),
    by
      have : 0 ≤ ∑ i ∈ Finset.range (k + 1), (N i 0 + max 0 (K / (θ ^ (-(σ - i)) - 1))) :=
        Finset.sum_nonneg fun i _ =>
          add_nonneg (by rw [hN]; exact scalarRms_nonneg _ _) (le_max_left _ _)
      linarith, fun m => ?_⟩
  obtain ⟨hdeg, -, he, hq, hinc⟩ := hP m
  have hσ0 : (k : ℝ) - 1 ≤ σ := by linarith
  set r := r₀ / θ ^ m with hrdef
  have hsum := scalarRms_le_sum_homogeneous hdeg (hr m)
  rw [Finset.sum_range_succ] at hsum
  simp only [← hN] at hsum
  have hlow : ∑ i ∈ Finset.range (k + 1), r ^ i * N i m ≤
      (∑ i ∈ Finset.range (k + 1), (N i 0 + max 0 (K / (θ ^ (-(σ - i)) - 1)))) * r ^ σ := by
    refine sum_pow_mul_le (hr1 m) (by push_cast; linarith) (fun i => by rw [hN]; exact scalarRms_nonneg _ _)
      fun i hi => ?_
    have hik : (i : ℝ) < σ := by
      have : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have : (i : ℝ) ≤ k := by exact_mod_cast this
      linarith
    have hd := drift_of_increments hθ0 hθ1 hr₀ hK hik
      (fun j => (hP j).2.2.2.2 i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))) m
    rw [← hN, ← hN] at hd
    exact hd.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg (hr m).le _)))
  have htop : r ^ (k + 1) * N (k + 1) m ≤ K * r ^ σ := by
    have e2 : r ^ (k + 1) * r ^ (σ - (k + 1)) = r ^ σ := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (hr m)]
      congr 1
      push_cast
      ring
    rw [hN]
    calc _ ≤ r ^ (k + 1) * (K * r ^ (σ - (k + 1))) :=
          mul_le_mul_of_nonneg_left hq (pow_nonneg (hr m).le _)
      _ = K * (r ^ (k + 1) * r ^ (σ - (k + 1))) := by ring
      _ = _ := by rw [e2]
  have hu : scalarRms volume (ball 0 r) u ≤
      scalarRms volume (ball 0 r) (fun x => u x - MvPolynomial.eval x (P m)) +
        scalarRms volume (ball 0 r) (fun x => MvPolynomial.eval x (P m)) := by
    calc scalarRms volume (ball 0 r) u = scalarRms volume (ball 0 r)
          (fun x => (u x - MvPolynomial.eval x (P m)) + MvPolynomial.eval x (P m)) := by
          congr 1
          funext x
          ring
      _ ≤ _ := scalarRms_add_le (f := fun x => u x - MvPolynomial.eval x (P m))
          (g := fun x => MvPolynomial.eval x (P m)) (((hsol r (hr m)).1).sub (memLp_eval_ball _ r))
          (memLp_eval_ball _ r)
  linarith

/-- The growth iteration when `k - 1 < β - δ < k`: a homogeneous `q ∈ Ā_k` of degree `k` with
`‖u - q‖_{L̲²(B_{r_j})} ≤ M r_j^{β-δ}` (Step 3 of the proof of (3.47)). -/
theorem growth_step_final_k {Λ : ℝ} {a : CoefficientField d Λ} {A : Mat d} {θ C₅ δ X r₀ M β : ℝ}
    {k : ℕ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hC₅ : 0 ≤ C₅) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hX1 : 1 ≤ X) (hXr : X ≤ r₀)
    (H50 : ∀ r : ℝ, X ≤ r → ∀ v, IsSolutionBall a r v →
      harmonicFlatness A (k + 1) v (θ * r) ≤
        1 / 4 * θ ^ (((k + 1 : ℕ) : ℝ) + 1 - δ / 2) * harmonicFlatness A (k + 1) v r +
          C₅ * r ^ (-δ) * scalarRms volume (ball 0 r) v)
    {u : Vec d → ℝ} (hsol : ∀ R : ℝ, 0 < R → IsSolutionBall a R u)
    (hu2 : Tendsto (fun r : ℝ => (r ^ (k + 1))⁻¹ * scalarRms volume (ball 0 r) u) atTop (𝓝 0))
    (hM : 0 ≤ M) (hβ2 : β ≤ (k : ℝ) + 1) (hσ0 : (k : ℝ) - 1 < β - δ) (hσ1 : β - δ < k)
    (hgrow : ∀ j : ℕ, scalarRms volume (ball 0 (r₀ / θ ^ j)) u ≤ M * (r₀ / θ ^ j) ^ β) :
    ∃ q ∈ homogeneousHarmonic A k, ∃ M' : ℝ, 0 ≤ M' ∧ ∀ j : ℕ,
      scalarRms volume (ball 0 (r₀ / θ ^ j)) (fun x => u x - q x) ≤
        M' * (r₀ / θ ^ j) ^ (β - δ) := by
  obtain ⟨P, K, hK, hP⟩ := growth_core_k (A := A) hθ0 hθ1 hC₅ hδ0 hδ1 hX1 hXr H50 hsol hu2 hM
    hβ2 hgrow
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = β - δ := ⟨_, rfl⟩
  rw [← hσ] at hP hσ0 hσ1 ⊢
  have hr₀ : 0 < r₀ := by linarith
  have hr : ∀ j : ℕ, 0 < r₀ / θ ^ j := fun j => div_pos hr₀ (pow_pos hθ0 j)
  have hr1 : ∀ j : ℕ, 1 ≤ r₀ / θ ^ j := fun j => by
    rw [le_div_iff₀ (pow_pos hθ0 j)]
    have : θ ^ j ≤ 1 := pow_le_one₀ hθ0.le hθ1.le
    nlinarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ → ℕ → ℝ, ∀ i j, N i j = scalarRms volume (ball 0 1)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent i (P j))) :=
    ⟨_, fun _ _ => rfl⟩
  -- the parts of degree `k` converge
  have hqV : ∀ j, (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent k (P j))) ∈
      homogeneousHarmonic A k := fun j =>
    ⟨homogeneousComponent_mem_harmonicPolys (hP j).2.1 (hP j).1 (fun x => rfl) k,
      MvPolynomial.homogeneousComponent k (P j), MvPolynomial.homogeneousComponent_mem k (P j),
      fun x => rfl⟩
  have hρ1 : θ ^ ((k : ℝ) - σ) < 1 := Real.rpow_lt_one hθ0.le hθ1 (by linarith)
  obtain ⟨Cl, hCl, q, hq, hql⟩ := exists_limit_homogeneousHarmonic A k hqV hρ1
    (B := K * r₀ ^ (σ - k)) (fun j => by
      have h := (hP j).2.2.2.2 k le_rfl
      rw [radius_rpow hθ0 hr₀, neg_sub] at h
      calc _ ≤ _ := h
        _ = _ := by ring)
  have h1ρ : 0 < 1 - θ ^ ((k : ℝ) - σ) := by linarith
  have hKq : 0 ≤ Cl * (K / (1 - θ ^ ((k : ℝ) - σ))) := mul_nonneg hCl (div_nonneg hK h1ρ.le)
  refine ⟨q, hq, 2 * K + ∑ i ∈ Finset.range k, (N i 0 + max 0 (K / (θ ^ (-(σ - i)) - 1))) +
    Cl * (K / (1 - θ ^ ((k : ℝ) - σ))), by
      have : 0 ≤ ∑ i ∈ Finset.range k, (N i 0 + max 0 (K / (θ ^ (-(σ - i)) - 1))) :=
        Finset.sum_nonneg fun i _ =>
          add_nonneg (by rw [hN]; exact scalarRms_nonneg _ _) (le_max_left _ _)
      linarith, fun m => ?_⟩
  obtain ⟨hdeg, -, he, hqtop, hinc⟩ := hP m
  set r := r₀ / θ ^ m with hrdef
  -- the decomposition of `u - q`
  have hdec : (fun x => u x - q x) = fun x =>
      (((u x - MvPolynomial.eval x (P m)) +
        ∑ i ∈ Finset.range k, MvPolynomial.eval x (MvPolynomial.homogeneousComponent i (P m))) +
        (MvPolynomial.eval x (MvPolynomial.homogeneousComponent k (P m)) - q x)) +
        MvPolynomial.eval x (MvPolynomial.homogeneousComponent (k + 1) (P m)) := by
    funext x
    rw [eval_eq_sum_homogeneousComponent hdeg, Finset.sum_range_succ, Finset.sum_range_succ]
    ring
  have hmu : MemLp (fun x => u x - MvPolynomial.eval x (P m)) 2
      (volume.restrict (ball (0 : Vec d) r)) := ((hsol r (hr m)).1).sub (memLp_eval_ball _ r)
  have hmi : ∀ i, MemLp (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent i (P m))) 2
      (volume.restrict (ball (0 : Vec d) r)) := fun i => memLp_eval_ball _ r
  have hms : MemLp (fun x => ∑ i ∈ Finset.range k,
      MvPolynomial.eval x (MvPolynomial.homogeneousComponent i (P m))) 2
      (volume.restrict (ball (0 : Vec d) r)) := by
    simpa only [map_sum] using memLp_eval_ball
      (∑ i ∈ Finset.range k, MvPolynomial.homogeneousComponent i (P m)) r
  have hmq : MemLp (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent k (P m)) - q x)
      2 (volume.restrict (ball (0 : Vec d) r)) :=
    (hmi k).sub (memLp_of_mem_homogeneousHarmonic hq r)
  have t1 := scalarRms_add_le (f := fun x => ((u x - MvPolynomial.eval x (P m)) +
      ∑ i ∈ Finset.range k, MvPolynomial.eval x (MvPolynomial.homogeneousComponent i (P m))) +
      (MvPolynomial.eval x (MvPolynomial.homogeneousComponent k (P m)) - q x))
    (g := fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent (k + 1) (P m)))
    ((hmu.add hms).add hmq) (hmi (k + 1))
  have t2 := scalarRms_add_le (f := fun x => (u x - MvPolynomial.eval x (P m)) +
      ∑ i ∈ Finset.range k, MvPolynomial.eval x (MvPolynomial.homogeneousComponent i (P m)))
    (g := fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent k (P m)) - q x)
    (hmu.add hms) hmq
  have t3 := scalarRms_add_le (f := fun x => u x - MvPolynomial.eval x (P m))
    (g := fun x => ∑ i ∈ Finset.range k,
      MvPolynomial.eval x (MvPolynomial.homogeneousComponent i (P m))) hmu hms
  -- the lower parts
  have hs1 : scalarRms volume (ball 0 r) (fun x => ∑ i ∈ Finset.range k,
      MvPolynomial.eval x (MvPolynomial.homogeneousComponent i (P m))) ≤
      ∑ i ∈ Finset.range k, r ^ i * N i m := by
    have h := scalarRms_finset_sum_le (Finset.range k)
      (f := fun i x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent i (P m))) hmi
      (fun _ => 1)
    simp only [one_mul, abs_one] at h
    refine h.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [hN]
    exact scalarRms_ball_homogeneousComponent i (P m) (hr m)
  have hlow : ∑ i ∈ Finset.range k, r ^ i * N i m ≤
      (∑ i ∈ Finset.range k, (N i 0 + max 0 (K / (θ ^ (-(σ - i)) - 1)))) * r ^ σ := by
    refine sum_pow_mul_le (hr1 m) (by linarith) (fun i => by rw [hN]; exact scalarRms_nonneg _ _)
      fun i hi => ?_
    have hik : (i : ℝ) < σ := by
      have : i + 1 ≤ k := Finset.mem_range.1 hi
      have : (i : ℝ) + 1 ≤ k := by exact_mod_cast this
      linarith
    have hd := drift_of_increments hθ0 hθ1 hr₀ hK hik
      (fun j => (hP j).2.2.2.2 i (by have := Finset.mem_range.1 hi; omega)) m
    rw [← hN, ← hN] at hd
    exact hd.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg (hr m).le _)))
  -- the part of degree `k`
  have hkq : scalarRms volume (ball 0 r)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent k (P m)) - q x) ≤
      Cl * (K / (1 - θ ^ ((k : ℝ) - σ))) * r ^ σ := by
    have hV : (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent k (P m)) - q x) ∈
        homogeneousHarmonic A k := Submodule.sub_mem _ (hqV m) hq
    have hsc := scalarRms_ball_homogeneous (k := k)
      (q := fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent k (P m)) - q x)
      (fun t _ x => homogeneousHarmonic_smul hV t x) (r := 1) (hr m)
    rw [mul_one] at hsc
    rw [hsc]
    have h := hql m
    have e : K * r₀ ^ (σ - k) * (θ ^ ((k : ℝ) - σ)) ^ m / (1 - θ ^ ((k : ℝ) - σ)) =
        K / (1 - θ ^ ((k : ℝ) - σ)) * r ^ (σ - k) := by
      rw [hrdef, radius_rpow hθ0 hr₀, neg_sub]
      ring
    rw [e] at h
    have e2 : r ^ k * r ^ (σ - k) = r ^ σ := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (hr m)]
      congr 1
      ring
    calc r ^ k * _ ≤ r ^ k * (Cl * (K / (1 - θ ^ ((k : ℝ) - σ)) * r ^ (σ - k))) :=
          mul_le_mul_of_nonneg_left h (pow_nonneg (hr m).le _)
      _ = Cl * (K / (1 - θ ^ ((k : ℝ) - σ))) * (r ^ k * r ^ (σ - k)) := by ring
      _ = _ := by rw [e2]
  -- the part of degree `k + 1`
  have htop : scalarRms volume (ball 0 r)
      (fun x => MvPolynomial.eval x (MvPolynomial.homogeneousComponent (k + 1) (P m))) ≤
      K * r ^ σ := by
    rw [scalarRms_ball_homogeneousComponent (k + 1) _ (hr m)]
    have e2 : r ^ (k + 1) * r ^ (σ - (k + 1)) = r ^ σ := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (hr m)]
      congr 1
      push_cast
      ring
    calc _ ≤ r ^ (k + 1) * (K * r ^ (σ - (k + 1))) :=
          mul_le_mul_of_nonneg_left hqtop (pow_nonneg (hr m).le _)
      _ = K * (r ^ (k + 1) * r ^ (σ - (k + 1))) := by ring
      _ = _ := by rw [e2]
  rw [hdec]
  linarith

/-- **The growth iteration, every `k ≥ 1`**: `n` steps with `β - δ > k` and a last one with
`k - 1 < β - δ < k`, for `δ = 2/(2n+1)`, starting from `‖u‖_{L̲²(B_r)} = o(r^{k+1})`. -/
theorem exists_homogeneous_growth {Λ : ℝ} {a : CoefficientField d Λ} {A : Mat d} {θ C₅ δ X r₀ : ℝ}
    {k n : ℕ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hC₅ : 0 ≤ C₅) (hn : 1 ≤ n) (hδ : δ = 2 / (2 * n + 1))
    (hX1 : 1 ≤ X) (hXr : X ≤ r₀)
    (H50 : ∀ r : ℝ, X ≤ r → ∀ v, IsSolutionBall a r v →
      harmonicFlatness A (k + 1) v (θ * r) ≤
        1 / 4 * θ ^ (((k + 1 : ℕ) : ℝ) + 1 - δ / 2) * harmonicFlatness A (k + 1) v r +
          C₅ * r ^ (-δ) * scalarRms volume (ball 0 r) v)
    {u : Vec d → ℝ} (hsol : ∀ R : ℝ, 0 < R → IsSolutionBall a R u)
    (hu2 : Tendsto (fun r : ℝ => (r ^ (k + 1))⁻¹ * scalarRms volume (ball 0 r) u) atTop (𝓝 0)) :
    ∃ q ∈ homogeneousHarmonic A k, ∃ M : ℝ, 0 ≤ M ∧ ∀ j : ℕ,
      scalarRms volume (ball 0 (r₀ / θ ^ j)) (fun x => u x - q x) ≤
        M * (r₀ / θ ^ j) ^ ((k : ℝ) + 1 - ((n : ℝ) + 1) * δ) := by
  have hr₀ : 0 < r₀ := by linarith
  have hr : ∀ j : ℕ, 0 < r₀ / θ ^ j := fun j => div_pos hr₀ (pow_pos hθ0 j)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2n : (0 : ℝ) < 2 * n + 1 := by positivity
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ1 : δ ≤ 1 := by rw [hδ, div_le_one h2n]; linarith
  have hnδ : (n : ℝ) * δ < 1 := by
    rw [hδ, mul_div_assoc', div_lt_one h2n]; linarith
  have hn1δ : 1 < ((n : ℝ) + 1) * δ := by
    rw [hδ, mul_div_assoc', one_lt_div h2n]; linarith
  have hn1δ2 : ((n : ℝ) + 1) * δ < 2 := by
    rw [hδ, mul_div_assoc', div_lt_iff₀ h2n]; linarith
  have hrtend : Tendsto (fun j : ℕ => r₀ / θ ^ j) atTop atTop := by
    have h := (tendsto_pow_atTop_atTop_of_one_lt ((one_lt_inv₀ hθ0).2 hθ1)).const_mul_atTop hr₀
    refine h.congr fun j => ?_
    rw [inv_pow, div_eq_mul_inv]
  obtain ⟨M₀, hM₀⟩ := (hu2.comp hrtend).bddAbove_range
  have hbase : ∀ j : ℕ, scalarRms volume (ball 0 (r₀ / θ ^ j)) u ≤
      M₀ * (r₀ / θ ^ j) ^ ((k : ℝ) + 1 - ((0 : ℕ) : ℝ) * δ) := by
    intro j
    have h := hM₀ ⟨j, rfl⟩
    simp only [Function.comp_apply] at h
    rw [inv_mul_le_iff₀ (pow_pos (hr j) (k + 1))] at h
    rw [Nat.cast_zero, zero_mul, sub_zero, show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
    linarith
  have hM₀0 : 0 ≤ M₀ :=
    (mul_nonneg (inv_nonneg.2 (pow_nonneg (hr 0).le _)) (scalarRms_nonneg _ _)).trans
      (hM₀ ⟨0, rfl⟩)
  have hiter : ∀ i : ℕ, i ≤ n → ∃ M : ℝ, 0 ≤ M ∧ ∀ j : ℕ,
      scalarRms volume (ball 0 (r₀ / θ ^ j)) u ≤ M * (r₀ / θ ^ j) ^ ((k : ℝ) + 1 - (i : ℝ) * δ) := by
    intro i
    induction i with
    | zero => intro _; exact ⟨M₀, hM₀0, hbase⟩
    | succ i ih =>
      intro hi
      obtain ⟨M, hM, hgrow⟩ := ih (by omega)
      have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
      have hσ1 : (k : ℝ) < (k : ℝ) + 1 - (i : ℝ) * δ - δ := by
        have := mul_le_mul_of_nonneg_right hi' hδ0.le
        linarith
      obtain ⟨M', hM', h⟩ := growth_step_large_k (A := A) hθ0 hθ1 hC₅ hδ0 hδ1 hX1 hXr H50 hsol hu2
        hM (by have := mul_nonneg (Nat.cast_nonneg i) hδ0.le; linarith) hσ1 hgrow
      refine ⟨M', hM', fun j => ?_⟩
      have e : (k : ℝ) + 1 - (i : ℝ) * δ - δ = (k : ℝ) + 1 - ((i + 1 : ℕ) : ℝ) * δ := by
        push_cast; ring
      rw [← e]
      exact h j
  obtain ⟨M, hM, hgrow⟩ := hiter n le_rfl
  obtain ⟨q, hq, M', hM', h⟩ := growth_step_final_k (A := A) hθ0 hθ1 hC₅ hδ0 hδ1 hX1 hXr H50 hsol
    hu2 hM (by have := mul_nonneg (Nat.cast_nonneg n) hδ0.le; linarith) (by linarith) (by linarith)
    hgrow
  refine ⟨q, hq, M', hM', fun j => ?_⟩
  have e : (k : ℝ) + 1 - (n : ℝ) * δ - δ = (k : ℝ) + 1 - ((n : ℝ) + 1) * δ := by ring
  rw [← e]
  exact h j

end QSH
