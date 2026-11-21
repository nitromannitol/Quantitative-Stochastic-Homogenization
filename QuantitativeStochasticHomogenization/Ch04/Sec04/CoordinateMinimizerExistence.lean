import QuantitativeStochasticHomogenization.Ch04.Sec04.CoordinateMinimizerCoercivity
import QuantitativeStochasticHomogenization.Ch05.Sec04CentralLimitTheoremForJ1

/-!
# Existence and uniqueness of the least-norm coordinate minimizers

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.4, pp. 155-156. For every coefficient field, every center `z` and positive radii, the
coordinate minimization of the objective `I` over the admissible class `K` has a minimizer, and
among the minimizers one of smallest `L²(B_T(z))` norm. Two least-norm minimizers coincide almost
everywhere on `B_T(z)`, together with their gradients; hence the localized energy `J₁^{(δ)}` of
(4.103) does not depend on the selected basis, and localized families exist.

The minimizer is obtained in the pair space by `exists_lexicographic_minimizer`: the objective is
continuous and convex, its sublevel sets on the admissible pairs are bounded, and the squared norm
of the potential is continuous and convex. Uniqueness follows from the parallelogram law on the
convex set of minimizers and from the fundamental lemma of the calculus of variations.
-/

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ} {a : CoefficientField d Λ} {z : Vec d} {T S σ θ C : ℝ}

theorem convexOn_norm_fst_sq :
    ConvexOn ℝ Set.univ (fun F : PairSpace d z T => ‖F.1‖ ^ 2) := by
  refine ⟨convex_univ, fun F _ G _ s t hs ht hst => ?_⟩
  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
  have h1 : ‖s • F.1 + t • G.1‖ ≤ s * ‖F.1‖ + t * ‖G.1‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have ht' : t = 1 - s := by linarith
  subst ht'
  nlinarith [sq_nonneg (‖F.1‖ - ‖G.1‖), mul_nonneg hs ht]

theorem LocalHarmonic.objective_eq (w : LocalHarmonic a z T) (i : Fin d) :
    localizationObjective z T S σ θ (fun x => w.potential x - (x - z) i) =
      pairObjective z T S σ θ i w.toPair := by
  unfold pairObjective
  refine localizationObjective_congr ?_
  filter_upwards [w.toPair_fst_ae] with x hx
  rw [hx]

theorem LocalHarmonic.integral_potential_sq (w : LocalHarmonic a z T) :
    ∫ x in ball z T, w.potential x ^ 2 = ‖w.toPair.1‖ ^ 2 := by
  rw [norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [w.toPair_fst_ae] with x hx
  rw [hx]

/-- **Existence of the least-norm coordinate minimizer** (pp. 155-156). -/
theorem exists_isLeastNormCoordinateMinimizer (a : CoefficientField d Λ) (z : Vec d)
    (hT : 0 < T) (hσS : σ * S ≠ 0) (hSθ : 0 < S / θ) (hC : 0 ≤ C) (i : Fin d) :
    ∃ w : LocalHarmonic a z T, IsLeastNormCoordinateMinimizer S σ θ C i w := by
  obtain ⟨F, hFK, hmin, hlex⟩ := exists_lexicographic_minimizer isQuadraticGauge_pairGauge
    (isClosed_admissiblePairs a z T C) ⟨0, zero_mem_admissiblePairs a z T⟩
    (continuous_pairObjective (θ := θ) hσS i)
    ((convexOn_pairObjective hσS i).subset (Set.subset_univ _) (convex_admissiblePairs a z T C))
    (fun F _ => pairObjective_nonneg i F) (continuous_fst.norm.pow 2)
    (convexOn_norm_fst_sq.subset (Set.subset_univ _) (convex_admissiblePairs a z T C))
    (fun F _ => sq_nonneg _) (fun t => bddAbove_pairGauge_sublevel hT hσS hSθ i t)
  set w := ofPair a F hFK.1
  have hwF : w.toPair = F := toPair_ofPair F hFK.1
  have hwadm : IsLocalizationAdmissible C w := (w.admissible_iff hC hT).2 (hwF ▸ hFK.2)
  have hwmin : IsCoordinateMinimizer S σ θ C i w := by
    refine ⟨hwadm, fun v hv => ?_⟩
    rw [w.objective_eq, v.objective_eq, hwF]
    exact hmin _ (v.toPair_mem hC hT hv)
  refine ⟨w, hwmin, fun v hv => ?_⟩
  rw [w.integral_potential_sq, v.integral_potential_sq, hwF]
  refine hlex _ (v.toPair_mem hC hT hv.1) ?_
  have h := hv.2 w hwadm
  rw [v.objective_eq, w.objective_eq, hwF] at h
  exact h

/-- An `L²(B_T(z))` class orthogonal to all test functions in `B_T(z)` vanishes. -/
theorem Lp_eq_zero_of_inner_test (g : Lp ℝ 2 (ballMeasure z T))
    (h : ∀ (φ : Vec d → ℝ) (hφ : IsSpatialTest (ball z T) φ),
      ⟪(hφ.memLp (ballMeasure z T)).toLp _, g⟫_ℝ = 0) : g = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have hloc : LocallyIntegrableOn (g : Vec d → ℝ) (ball z T) volume :=
    (integrableOn_ball_of_Lp g).locallyIntegrableOn
  have hz := (isOpen_ball z T).ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun φ hφ hcs hsupp => by
      have h1 := h φ ⟨hφ, hcs, hsupp⟩
      rw [inner_toLp_left] at h1
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ball z T) fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun hx' => hx (hsupp hx')), zero_smul]]
      simpa [mul_comm] using h1)
  rw [EventuallyEq, ae_restrict_iff' (measurableSet_ball z T)]
  filter_upwards [hz] with x hx hxb
  simpa using hx hxb

/-- **Uniqueness of the least-norm coordinate minimizer**: two least-norm minimizers have the same
`L²(B_T(z))` classes of potentials and gradients. -/
theorem IsLeastNormCoordinateMinimizer.toPair_eq (hT : 0 < T) (hσS : σ * S ≠ 0) (hC : 0 ≤ C)
    {i : Fin d} {w v : LocalHarmonic a z T} (hw : IsLeastNormCoordinateMinimizer S σ θ C i w)
    (hv : IsLeastNormCoordinateMinimizer S σ θ C i v) : w.toPair = v.toPair := by
  set F := w.toPair
  set G := v.toPair
  have hFK : F ∈ admissiblePairs a z T C := w.toPair_mem hC hT hw.1.1
  have hGK : G ∈ admissiblePairs a z T C := v.toPair_mem hC hT hv.1.1
  have hfFG : pairObjective z T S σ θ i F ≤ pairObjective z T S σ θ i G := by
    have h := hw.1.2 v hv.1.1
    rwa [w.objective_eq, v.objective_eq] at h
  have hfGF : pairObjective z T S σ θ i G ≤ pairObjective z T S σ θ i F := by
    have h := hv.1.2 w hw.1.1
    rwa [v.objective_eq, w.objective_eq] at h
  set H : PairSpace d z T := (1 / 2 : ℝ) • F + (1 / 2 : ℝ) • G
  have hHK : H ∈ admissiblePairs a z T C :=
    convex_admissiblePairs a z T C hFK hGK (by norm_num) (by norm_num) (by norm_num)
  have hfH : pairObjective z T S σ θ i H ≤ pairObjective z T S σ θ i F := by
    have h := (convexOn_pairObjective (θ := θ) hσS i).2 (Set.mem_univ F) (Set.mem_univ G)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at h
    linarith
  set u := ofPair a H hHK.1
  have huH : u.toPair = H := toPair_ofPair H hHK.1
  have hu : IsCoordinateMinimizer S σ θ C i u := by
    refine ⟨(u.admissible_iff hC hT).2 (huH ▸ hHK.2), fun v' hv' => ?_⟩
    rw [u.objective_eq, v'.objective_eq, huH]
    have h := hw.1.2 v' hv'
    rw [w.objective_eq, v'.objective_eq] at h
    exact hfH.trans h
  have hFH : ‖F.1‖ ^ 2 ≤ ‖H.1‖ ^ 2 := by
    have h := hw.2 u hu
    rwa [w.integral_potential_sq, u.integral_potential_sq, huH] at h
  have hFG : ‖F.1‖ ^ 2 ≤ ‖G.1‖ ^ 2 := by
    have h := hw.2 v hv.1
    rwa [w.integral_potential_sq, v.integral_potential_sq] at h
  have hGF : ‖G.1‖ ^ 2 ≤ ‖F.1‖ ^ 2 := by
    have h := hv.2 w hw.1
    rwa [v.integral_potential_sq, w.integral_potential_sq] at h
  have hH1 : H.1 = (1 / 2 : ℝ) • (F.1 + G.1) := by
    simp only [H, Prod.fst_add, Prod.smul_fst, smul_add]
  have hpar := parallelogram_law_with_norm ℝ F.1 G.1
  have hHn : ‖H.1‖ ^ 2 = (1 / 4 : ℝ) * ‖F.1 + G.1‖ ^ 2 := by
    rw [hH1, norm_smul, mul_pow, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  have hsub : ‖F.1 - G.1‖ ^ 2 = 0 := by
    have := sq_nonneg ‖F.1 - G.1‖
    nlinarith
  have h1 : F.1 = G.1 := by
    have : ‖F.1 - G.1‖ = 0 := by
      have h := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsub
      exact h
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  have h2 : F.2 = G.2 := by
    funext k
    refine sub_eq_zero.1 (Lp_eq_zero_of_inner_test _ fun φ hφ => ?_)
    have hF := hFK.1.1 φ hφ k
    have hG := hGK.1.1 φ hφ k
    simp only [gradConstraint] at hF hG
    rw [h1] at hF
    rw [inner_sub_right]
    linarith
  exact Prod.ext h1 h2

/-- The gradients of two least-norm coordinate minimizers agree almost everywhere on `B_T(z)`. -/
theorem IsLeastNormCoordinateMinimizer.grad_ae_eq (hT : 0 < T) (hσS : σ * S ≠ 0) (hC : 0 ≤ C)
    {i : Fin d} {w v : LocalHarmonic a z T} (hw : IsLeastNormCoordinateMinimizer S σ θ C i w)
    (hv : IsLeastNormCoordinateMinimizer S σ θ C i v) :
    w.grad =ᵐ[ballMeasure z T] v.grad := by
  have h := hw.toPair_eq hT hσS hC hv
  have hk : ∀ k, (fun x => w.grad x k) =ᵐ[ballMeasure z T] fun x => v.grad x k := by
    intro k
    have hk := congrFun (congrArg Prod.snd h) k
    filter_upwards [w.toPair_snd_ae k, v.toPair_snd_ae k] with x hx1 hx2
    rw [← hx1, ← hx2, hk]
  filter_upwards [ae_all_iff.2 hk] with x hx
  funext k
  exact hx k

/-- **The localized energy does not depend on the selected basis**. -/
theorem localizedJ1_eq_of_basis (hT : 0 < T) (hσS : σ * S ≠ 0) (hC : 0 ≤ C)
    (W W' : LocalizedBasis a z T S σ θ C) (r : ℝ) (p q : Vec d) :
    localizedJ1 W r p q = localizedJ1 W' r p q := by
  have hgrad : ∀ c : Vec d, localizedGradient W c =ᵐ[ballMeasure z T] localizedGradient W' c := by
    intro c
    have h := ae_all_iff.2 fun k => (W.selected k).grad_ae_eq hT hσS hC (W'.selected k)
    filter_upwards [h] with x hx
    simp only [localizedGradient]
    exact Finset.sum_congr rfl fun k _ => by rw [hx k]
  unfold localizedJ1
  congr 1
  ext e
  refine exists_congr fun c => ?_
  rw [integral_congr_ae (μ := ballMeasure z T) ?_]
  filter_upwards [hgrad c] with x hx
  rw [hx]

/-- Localized bases exist for every coefficient field, center and admissible radii. -/
theorem nonempty_localizedBasis (a : CoefficientField d Λ) (z : Vec d) (hT : 0 < T)
    (hσS : σ * S ≠ 0) (hSθ : 0 < S / θ) (hC : 0 ≤ C) :
    Nonempty (LocalizedBasis a z T S σ θ C) := by
  choose w hw using fun i => exists_isLeastNormCoordinateMinimizer a z hT hσS hSθ hC i
  exact ⟨⟨w, hw⟩⟩

/-- **Localized families exist** for all positive smoothing constants `σ`, `θ` and `C₀ ≥ 0`. -/
theorem nonempty_localizedFamily (d : ℕ) (Λ δ γ α : ℝ) {σ θ C₀ : ℝ} (hσ : 0 < σ) (hθ : 0 < θ)
    (hC₀ : 0 ≤ C₀) : Nonempty (LocalizedFamily d Λ δ γ α σ θ C₀) := by
  refine ⟨fun a z r hr => Classical.choice (nonempty_localizedBasis a z ?_ ?_ ?_ hC₀)⟩
  · exact Real.rpow_pos_of_pos (by linarith) _
  · exact (mul_pos hσ (Real.rpow_pos_of_pos (by linarith) _)).ne'
  · exact div_pos (Real.rpow_pos_of_pos (by linarith) _) hθ

end QSH
