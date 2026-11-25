import QuantitativeStochasticHomogenization.AppC.GehringIntegration

/-!
# The good-λ inequality in the proof of Lemma 7.2

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 7.2, the good-λ inequality (7.10). The function `G` stands for `ε⁻¹ g` and `η` for
`εA + δ`, so that the hypotheses (7.6) and (7.7) read, on every ball `B_{2ρ}(z) ⊆ B_R`,
`‖h‖_{L̲^q(B_ρ(z))} ≤ A (‖G‖_{L̲²(B_{2ρ}(z))} + ‖f‖_{L̲²(B_{2ρ}(z))})` and
`‖f - h‖_{L̲²(B_ρ(z))} ≤ η (‖G‖_{L̲²(B_{2ρ}(z))} + ‖f‖_{L̲²(B_{2ρ}(z))})` for some `h`.
With `λ₀ = (128/(t - s))^{d/2} (‖f‖_{L̲²(B_R)} + ‖G‖_{L̲²(B_R)})`, every `λ > λ₀` and `M ≥ 1` give
`∫_{B_{sR} ∩ {|f| > Mλ}} f² ≤ 16 · 8^d (2 (M/2)^{2-q} A^q + 6 η²)
  (∫_{B_{tR} ∩ {|f| > λ/4}} f² + ∫_{B_{tR} ∩ {|G| > λ/4}} G²)`.

The proof is the book's. At almost every point `z ∈ B_{sR}` with `|f(z)| > Mλ` (Lebesgue
differentiation on balls) a stopping radius `r` has `λ < E(z, r)` and `E(z, 16r) ≤ λ`, where
`E(z, ρ) = ‖f‖_{L̲²(B_ρ(z))} + ‖G‖_{L̲²(B_ρ(z))}` (Step 1, `exists_cz_stopping_radius`); the
stopping radius is taken among the dyadic radii `(t - s)R/(16 · 2^k)`, which replaces the
equality `E(x, r_x) = λ` of the book by these two inequalities and changes the numerical
constants. The first inequality bounds `λ² |B_r(z)|` by the level set integrals (7.12)
(`volume_mul_sq_le_levelSets`); the second and the hypotheses at the radius `8r` bound the level
set of `f` on `B_{8r}(z)` (7.15) (`setLIntegral_levelSet_le_of_approx`); the Vitali covering
lemma (Lemma C.5) sums these bounds over a countable disjoint subfamily (Step 4).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

theorem enorm_sq_le_of_sq_le {a b c α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (h : a ^ 2 ≤ α * b ^ 2 + β * c ^ 2) :
    ‖a‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal α * ‖b‖ₑ ^ (2 : ℝ) + ENNReal.ofReal β * ‖c‖ₑ ^ (2 : ℝ) := by
  rw [enorm_rpow_eq_ofReal _ zero_le_two, enorm_rpow_eq_ofReal _ zero_le_two,
    enorm_rpow_eq_ofReal _ zero_le_two, ← ENNReal.ofReal_mul hα, ← ENNReal.ofReal_mul hβ,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  simpa only [Real.rpow_two, sq_abs] using h

theorem setLIntegral_enorm_rpow_eq {B : Set (Vec d)} (hB0 : volume B ≠ 0) (hBt : volume B ≠ ⊤)
    {h : Vec d → ℝ} (hhm : Measurable h) {s : ℝ} (hs : 0 < s) :
    ∫⁻ x in B, ‖h x‖ₑ ^ s = volume B * PDE.eLpMeanNormOn B (ENNReal.ofReal s) h ^ s := by
  rw [eLpMeanNormOn_rpow_eq hs hhm.aestronglyMeasurable.restrict, ← mul_assoc,
    ENNReal.mul_inv_cancel hB0 hBt, one_mul]

/-- **The estimate (7.15) on one ball.** If `‖h‖_{L̲^q(B)} ≤ Aλ` and `‖f - h‖_{L̲²(B)} ≤ ηλ`, then
`∫_{B ∩ {|f| > Mλ}} f² ≤ (2 (M/2)^{2-q} A^q + 6 η²) λ² |B|`. -/
theorem setLIntegral_levelSet_le_of_approx {B : Set (Vec d)} (hBm : MeasurableSet B)
    (hB0 : volume B ≠ 0) (hBt : volume B ≠ ⊤) {f h : Vec d → ℝ} (hfm : Measurable f)
    (hhm : Measurable h) {q A η M l : ℝ} (hq : 2 < q) (hA : 0 ≤ A) (hη : 0 ≤ η) (hM : 0 < M)
    (hl : 0 < l) (hhq : PDE.eLpMeanNormOn B (ENNReal.ofReal q) h ≤ ENNReal.ofReal (A * l))
    (hfh : PDE.eLpMeanNormOn B 2 (f - h) ≤ ENNReal.ofReal (η * l)) :
    ∫⁻ x in B ∩ {x | M * l < |f x|}, ‖f x‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal ((2 * (M / 2) ^ (2 - q) * A ^ q + 6 * η ^ 2) * l ^ 2) * volume B := by
  set T := {x | M * l / 2 < |h x|} with hT
  set S := B ∩ {x | M * l < |f x|} with hS
  have hTm : MeasurableSet T := measurableSet_lt measurable_const hhm.abs
  have hfhm : Measurable (f - h) := hfm.sub hhm
  have hc : 0 < M * l / 2 := by positivity
  have hIh : ∫⁻ x in B, ‖h x‖ₑ ^ q ≤ volume B * ENNReal.ofReal ((A * l) ^ q) := by
    rw [setLIntegral_enorm_rpow_eq hB0 hBt hhm (by linarith),
      ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith)]
    gcongr
  have hIfh : ∫⁻ x in B, ‖(f - h) x‖ₑ ^ (2 : ℝ) ≤
      volume B * ENNReal.ofReal ((η * l) ^ (2 : ℝ)) := by
    have e := setLIntegral_enorm_rpow_eq hB0 hBt hfhm two_pos
    rw [ENNReal.ofReal_ofNat] at e
    rw [e, ← ENNReal.ofReal_rpow_of_nonneg (by positivity) zero_le_two]
    gcongr
  have hcheb : ∫⁻ x in B ∩ T, ‖h x‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal ((M * l / 2) ^ (2 - q)) * ∫⁻ x in B, ‖h x‖ₑ ^ q := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ∫⁻ x in B ∩ T, ‖h x‖ₑ ^ (2 : ℝ)
        ≤ ∫⁻ x in B ∩ T, ENNReal.ofReal ((M * l / 2) ^ (2 - q)) * ‖h x‖ₑ ^ q := by
          refine setLIntegral_mono' (hBm.inter hTm) fun x hx => ?_
          have hx' : M * l / 2 < |h x| := hx.2
          rw [enorm_rpow_eq_ofReal _ zero_le_two, enorm_rpow_eq_ofReal _ (by linarith),
            ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hpos : 0 < |h x| := hc.trans hx'
          calc |h x| ^ (2 : ℝ) = |h x| ^ (2 - q) * |h x| ^ q := by
                rw [← Real.rpow_add hpos, sub_add_cancel]
            _ ≤ (M * l / 2) ^ (2 - q) * |h x| ^ q :=
                mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hc hx'.le (by linarith))
                  (Real.rpow_nonneg (abs_nonneg _) _)
      _ ≤ ∫⁻ x in B, ENNReal.ofReal ((M * l / 2) ^ (2 - q)) * ‖h x‖ₑ ^ q :=
          lintegral_mono_set inter_subset_left
  have h1 : ∫⁻ x in S ∩ T, ‖f x‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal 2 * (∫⁻ x in B ∩ T, ‖h x‖ₑ ^ (2 : ℝ)) +
        ENNReal.ofReal 2 * ∫⁻ x in B, ‖(f - h) x‖ₑ ^ (2 : ℝ) := by
    calc ∫⁻ x in S ∩ T, ‖f x‖ₑ ^ (2 : ℝ)
        ≤ ∫⁻ x in S ∩ T, (ENNReal.ofReal 2 * ‖h x‖ₑ ^ (2 : ℝ) +
            ENNReal.ofReal 2 * ‖(f - h) x‖ₑ ^ (2 : ℝ)) := by
          refine lintegral_mono fun x => enorm_sq_le_of_sq_le zero_le_two zero_le_two ?_
          simp only [Pi.sub_apply]
          nlinarith [sq_nonneg (h x - (f x - h x))]
      _ = ENNReal.ofReal 2 * (∫⁻ x in S ∩ T, ‖h x‖ₑ ^ (2 : ℝ)) +
            ENNReal.ofReal 2 * ∫⁻ x in S ∩ T, ‖(f - h) x‖ₑ ^ (2 : ℝ) := by
          rw [lintegral_add_left ((hhm.enorm.pow_const _).const_mul _),
            lintegral_const_mul _ (hhm.enorm.pow_const _),
            lintegral_const_mul _ (hfhm.enorm.pow_const _)]
      _ ≤ _ := by
          gcongr
          · exact inter_subset_left
          · exact inter_subset_left.trans inter_subset_left
  have h2 : ∫⁻ x in S \ T, ‖f x‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal 4 * ∫⁻ x in B, ‖(f - h) x‖ₑ ^ (2 : ℝ) := by
    rw [← lintegral_const_mul _ (hfhm.enorm.pow_const _)]
    calc ∫⁻ x in S \ T, ‖f x‖ₑ ^ (2 : ℝ)
        ≤ ∫⁻ x in S \ T, ENNReal.ofReal 4 * ‖(f - h) x‖ₑ ^ (2 : ℝ) := by
          refine setLIntegral_mono' ((hBm.inter (measurableSet_lt measurable_const
            hfm.abs)).diff hTm) fun x hx => ?_
          have hxf : M * l < |f x| := hx.1.2
          have hxh : |h x| ≤ M * l / 2 := not_lt.mp hx.2
          have htri : |f x| ≤ |h x| + |f x - h x| := by
            have := abs_add_le (h x) (f x - h x)
            rwa [add_sub_cancel] at this
          have hlt : |f x| ≤ 2 * |f x - h x| := by linarith
          have h0 := enorm_sq_le_of_sq_le (a := f x) (b := 0) (c := (f - h) x) (le_refl 0)
            (by norm_num : (0 : ℝ) ≤ 4) (by
              simp only [Pi.sub_apply]
              nlinarith [abs_nonneg (f x), sq_abs (f x), sq_abs (f x - h x)])
          simpa using h0
      _ ≤ ∫⁻ x in B, ENNReal.ofReal 4 * ‖(f - h) x‖ₑ ^ (2 : ℝ) :=
          lintegral_mono_set fun x hx => hx.1.1
  have e1 : (M * l / 2) ^ (2 - q) * (A * l) ^ q = (M / 2) ^ (2 - q) * A ^ q * l ^ 2 := by
    rw [show M * l / 2 = M / 2 * l by ring, Real.mul_rpow (by positivity) hl.le,
      Real.mul_rpow hA hl.le]
    have : l ^ (2 - q) * l ^ q = l ^ 2 := by
      rw [← Real.rpow_add hl, sub_add_cancel, Real.rpow_two]
    calc (M / 2) ^ (2 - q) * l ^ (2 - q) * (A ^ q * l ^ q) =
        (M / 2) ^ (2 - q) * A ^ q * (l ^ (2 - q) * l ^ q) := by ring
      _ = _ := by rw [this]
  have e2 : (η * l) ^ (2 : ℝ) = η ^ 2 * l ^ 2 := by rw [Real.rpow_two, mul_pow]
  have e3 : (2 * (M / 2) ^ (2 - q) * A ^ q + 6 * η ^ 2) * l ^ 2 =
      2 * ((M * l / 2) ^ (2 - q) * (A * l) ^ q) + 6 * (η * l) ^ (2 : ℝ) := by
    rw [e1, e2]
    ring
  calc ∫⁻ x in S, ‖f x‖ₑ ^ (2 : ℝ)
      = (∫⁻ x in S ∩ T, ‖f x‖ₑ ^ (2 : ℝ)) + ∫⁻ x in S \ T, ‖f x‖ₑ ^ (2 : ℝ) :=
        (lintegral_inter_add_sdiff _ S hTm).symm
    _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal ((M * l / 2) ^ (2 - q)) *
          (volume B * ENNReal.ofReal ((A * l) ^ q))) +
        (ENNReal.ofReal 2 + ENNReal.ofReal 4) *
          (volume B * ENNReal.ofReal ((η * l) ^ (2 : ℝ))) := by
        refine (add_le_add h1 h2).trans ?_
        rw [add_mul, ← add_assoc]
        gcongr
        exact hcheb.trans (by gcongr)
    _ = ENNReal.ofReal ((2 * (M / 2) ^ (2 - q) * A ^ q + 6 * η ^ 2) * l ^ 2) * volume B := by
        rw [e3, ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num
        ring

/-- **The stopping-time bound (7.12).** If `λ < ‖f‖_{L̲²(B)} + ‖G‖_{L̲²(B)}`, then
`λ² |B| ≤ 16 (∫_{B ∩ {|f| > λ/4}} f² + ∫_{B ∩ {|G| > λ/4}} G²)`. -/
theorem volume_mul_sq_le_levelSets {B : Set (Vec d)} (hBt : volume B ≠ ⊤) {f G : Vec d → ℝ}
    (hfm : Measurable f) (hGm : Measurable G) {l : ℝ} (hl : 0 < l)
    (hE : ENNReal.ofReal l < PDE.eLpMeanNormOn B 2 f + PDE.eLpMeanNormOn B 2 G) :
    ENNReal.ofReal (l ^ 2) * volume B ≤
      ENNReal.ofReal 16 * ((∫⁻ x in B ∩ {x | l / 4 < |f x|}, ‖f x‖ₑ ^ (2 : ℝ)) +
        ∫⁻ x in B ∩ {x | l / 4 < |G x|}, ‖G x‖ₑ ^ (2 : ℝ)) := by
  have hcase : ENNReal.ofReal (2 * (l / 4)) < PDE.eLpMeanNormOn B (ENNReal.ofReal 2) f ∨
      ENNReal.ofReal (2 * (l / 4)) < PDE.eLpMeanNormOn B (ENNReal.ofReal 2) G := by
    rw [ENNReal.ofReal_ofNat]
    by_contra hcon
    push Not at hcon
    have : PDE.eLpMeanNormOn B 2 f + PDE.eLpMeanNormOn B 2 G ≤ ENNReal.ofReal l := by
      calc _ ≤ ENNReal.ofReal (2 * (l / 4)) + ENNReal.ofReal (2 * (l / 4)) :=
            add_le_add hcon.1 hcon.2
        _ = ENNReal.ofReal l := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            ring
    exact absurd (hE.trans_le this) (lt_irrefl _)
  have hc : (2 : ℝ) ≤ 2 ^ (2 : ℝ) := by norm_num
  have hkey : ENNReal.ofReal (l ^ 2) * ENNReal.ofReal ((l / 4)⁻¹ ^ (2 : ℝ)) =
      ENNReal.ofReal 16 := by
    rw [← ENNReal.ofReal_mul (by positivity), Real.rpow_two, inv_div]
    congr 1
    field_simp
    norm_num
  rcases hcase with h | h
  · have hv := volume_le_of_lt_eLpMeanNormOn hBt hfm two_pos (by positivity) two_pos hc h
    calc ENNReal.ofReal (l ^ 2) * volume B
        ≤ ENNReal.ofReal (l ^ 2) * (ENNReal.ofReal ((l / 4)⁻¹ ^ (2 : ℝ)) *
            ∫⁻ x in B ∩ {x | l / 4 < |f x|}, ‖f x‖ₑ ^ (2 : ℝ)) := by gcongr
      _ = ENNReal.ofReal 16 * ∫⁻ x in B ∩ {x | l / 4 < |f x|}, ‖f x‖ₑ ^ (2 : ℝ) := by
          rw [← mul_assoc, hkey]
      _ ≤ _ := by gcongr; exact le_self_add
  · have hv := volume_le_of_lt_eLpMeanNormOn hBt hGm two_pos (by positivity) two_pos hc h
    calc ENNReal.ofReal (l ^ 2) * volume B
        ≤ ENNReal.ofReal (l ^ 2) * (ENNReal.ofReal ((l / 4)⁻¹ ^ (2 : ℝ)) *
            ∫⁻ x in B ∩ {x | l / 4 < |G x|}, ‖G x‖ₑ ^ (2 : ℝ)) := by gcongr
      _ = ENNReal.ofReal 16 * ∫⁻ x in B ∩ {x | l / 4 < |G x|}, ‖G x‖ₑ ^ (2 : ℝ) := by
          rw [← mul_assoc, hkey]
      _ ≤ _ := by gcongr; exact le_add_self

/-- **The stopping radius (Step 1).** If `λ > λ₀` and `λ < E(z, ρ₁/2^k)` for some `k`, with
`ρ₁ = (t - s)R/16`, then some `r > 0` with `16r ≤ ρ₁` has `λ < E(z, r)` and `E(z, 16r) ≤ λ`. -/
theorem exists_cz_stopping_radius {R s t : ℝ} (hR : 0 < R) (hs : 0 < s) (hst : s < t)
    (ht : t ≤ 1) {f G : Vec d → ℝ} (hfm : Measurable f) (hGm : Measurable G) {l : ℝ}
    (hl₀ : ENNReal.ofReal ((128 / (t - s)) ^ ((d : ℝ) / 2)) *
        (PDE.eLpMeanNormOn (ball 0 R) 2 f + PDE.eLpMeanNormOn (ball 0 R) 2 G) < ENNReal.ofReal l)
    {z : Vec d} (hz : z ∈ ball 0 (s * R))
    (hk : ∃ k : ℕ, ENNReal.ofReal l <
      PDE.eLpMeanNormOn (ball z ((t - s) * R / 16 / 2 ^ k)) 2 f +
        PDE.eLpMeanNormOn (ball z ((t - s) * R / 16 / 2 ^ k)) 2 G) :
    ∃ r : ℝ, 0 < r ∧ 16 * r ≤ (t - s) * R / 16 ∧
      ENNReal.ofReal l < PDE.eLpMeanNormOn (ball z r) 2 f + PDE.eLpMeanNormOn (ball z r) 2 G ∧
      PDE.eLpMeanNormOn (ball z (16 * r)) 2 f + PDE.eLpMeanNormOn (ball z (16 * r)) 2 G ≤
        ENNReal.ofReal l := by
  classical
  have hts : 0 < t - s := by linarith
  set ρ₁ := (t - s) * R / 16 with hρ₁
  have hρ₁0 : 0 < ρ₁ := by positivity
  have hzn : euclideanNorm (z - 0) < s * R := hz
  set k₀ := Nat.find hk with hk₀
  have hspec := Nat.find_spec hk
  have h4 : 4 ≤ k₀ := by
    by_contra hlt
    have hle : k₀ ≤ 3 := by omega
    set ρ := ρ₁ / 2 ^ k₀ with hρdef
    have h2j : (2 : ℝ) ^ k₀ ≤ 8 := by
      calc (2 : ℝ) ^ k₀ ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hle
        _ = 8 := by norm_num
    have hρ : 0 < ρ := by positivity
    have hρle : ρ ≤ ρ₁ := div_le_self hρ₁0.le (one_le_pow₀ (by norm_num))
    have hρge : (t - s) * R / 128 ≤ ρ := by
      rw [hρdef, hρ₁, div_div, le_div_iff₀ (by positivity)]
      nlinarith [mul_pos hts hR]
    have hsub : ball z ρ ⊆ ball 0 R := ball_subset_ball_of_norm (by nlinarith)
    have h1 := eLpMeanNormOn_ball_le hρ hR hsub hfm
    have h2 := eLpMeanNormOn_ball_le hρ hR hsub hGm
    have hcR : ENNReal.ofReal ((R / ρ) ^ ((d : ℝ) / 2)) ≤
        ENNReal.ofReal ((128 / (t - s)) ^ ((d : ℝ) / 2)) := by
      refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) ?_ (by positivity))
      rw [div_le_div_iff₀ hρ hts]
      nlinarith
    have hE : PDE.eLpMeanNormOn (ball z ρ) 2 f + PDE.eLpMeanNormOn (ball z ρ) 2 G ≤
        ENNReal.ofReal ((128 / (t - s)) ^ ((d : ℝ) / 2)) *
          (PDE.eLpMeanNormOn (ball 0 R) 2 f + PDE.eLpMeanNormOn (ball 0 R) 2 G) := by
      rw [mul_add]
      gcongr
      · exact h1.trans (by gcongr)
      · exact h2.trans (by gcongr)
    exact absurd (hspec.trans_le (hE.trans hl₀.le)) (lt_irrefl _)
  set r := ρ₁ / 2 ^ k₀ with hrdef
  have hr : 0 < r := by positivity
  have h16 : ρ₁ / 2 ^ (k₀ - 4) = 16 * r := by
    have e : (2 : ℝ) ^ k₀ = 2 ^ (k₀ - 4) * 16 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_add, Nat.sub_add_cancel h4]
    rw [hrdef, e]
    field_simp
  refine ⟨r, hr, ?_, hspec, ?_⟩
  · rw [← h16]
    exact div_le_self hρ₁0.le (one_le_pow₀ (by norm_num))
  · have hmin := Nat.find_min hk (show k₀ - 4 < k₀ by omega)
    push Not at hmin
    rwa [h16] at hmin

/-- **The good-λ inequality (7.10).** -/
theorem cz_goodLambda {R s t q A η M l : ℝ} (hR : 0 < R) (hs : 0 < s) (hst : s < t)
    (ht : t ≤ 1) (hq : 2 < q) (hA : 0 ≤ A) (hη : 0 ≤ η) (hM : 1 ≤ M) (hl : 0 < l)
    {f G : Vec d → ℝ} (hfm : Measurable f) (hGm : Measurable G)
    (hfint : IntegrableOn f (ball 0 R))
    (happrox : ∀ (z : Vec d) (ρ : ℝ), 0 < ρ → ball z (2 * ρ) ⊆ ball 0 R →
      ∃ h : Vec d → ℝ, Measurable h ∧
        PDE.eLpMeanNormOn (ball z ρ) (ENNReal.ofReal q) h ≤ ENNReal.ofReal A *
          (PDE.eLpMeanNormOn (ball z (2 * ρ)) 2 G + PDE.eLpMeanNormOn (ball z (2 * ρ)) 2 f) ∧
        PDE.eLpMeanNormOn (ball z ρ) 2 (f - h) ≤ ENNReal.ofReal η *
          (PDE.eLpMeanNormOn (ball z (2 * ρ)) 2 G + PDE.eLpMeanNormOn (ball z (2 * ρ)) 2 f))
    (hl₀ : ENNReal.ofReal ((128 / (t - s)) ^ ((d : ℝ) / 2)) *
        (PDE.eLpMeanNormOn (ball 0 R) 2 f + PDE.eLpMeanNormOn (ball 0 R) 2 G) < ENNReal.ofReal l) :
    ∫⁻ x in ball 0 (s * R) ∩ {x | M * l < |f x|}, ‖f x‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (16 * 8 ^ d * (2 * (M / 2) ^ (2 - q) * A ^ q + 6 * η ^ 2)) *
        ((∫⁻ x in ball 0 (t * R) ∩ {x | l / 4 < |f x|}, ‖f x‖ₑ ^ (2 : ℝ)) +
          ∫⁻ x in ball 0 (t * R) ∩ {x | l / 4 < |G x|}, ‖G x‖ₑ ^ (2 : ℝ)) := by
  classical
  have hts : 0 < t - s := by linarith
  set ρ₁ := (t - s) * R / 16 with hρ₁
  have hρ₁0 : 0 < ρ₁ := by positivity
  set c₀ : ℝ := 2 * (M / 2) ^ (2 - q) * A ^ q + 6 * η ^ 2 with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  set Z : Set (Vec d) := {z | z ∈ ball 0 (s * R) ∧ M * l < |f z| ∧ ∃ k : ℕ, ENNReal.ofReal l <
      PDE.eLpMeanNormOn (ball z (ρ₁ / 2 ^ k)) 2 f +
        PDE.eLpMeanNormOn (ball z (ρ₁ / 2 ^ k)) 2 G} with hZ
  have hsubR : ∀ z ∈ ball (0 : Vec d) (s * R), ∀ ρ, ρ ≤ ρ₁ → ball z ρ ⊆ ball 0 R := by
    intro z hz ρ hρ
    have hzn : euclideanNorm (z - 0) < s * R := hz
    exact ball_subset_ball_of_norm (by nlinarith)
  have hsubt : ∀ z ∈ ball (0 : Vec d) (s * R), ∀ ρ, ρ ≤ ρ₁ → ball z ρ ⊆ ball 0 (t * R) := by
    intro z hz ρ hρ
    have hzn : euclideanNorm (z - 0) < s * R := hz
    exact ball_subset_ball_of_norm (by nlinarith)
  set S := {x | M * l < |f x|} with hS
  have hSm : MeasurableSet S := measurableSet_lt measurable_const hfm.abs
  -- almost every point of the level set is in `Z`
  have hnull : volume ((ball 0 (s * R) ∩ S) \ Z) = 0 := by
    set F := (ball (0 : Vec d) R).indicator f with hF
    have hFli : LocallyIntegrable F volume :=
      (hfint.integrable_indicator (measurableSet_ball 0 R)).locallyIntegrable
    have hae := ae_eventually_lt_ballAverage_abs hFli
    refine measure_mono_null ?_ (ae_iff.mp hae)
    rintro x ⟨⟨hxs, hxl⟩, hxZ⟩ hP
    apply hxZ
    have hxR : x ∈ ball (0 : Vec d) R := hsubR x hxs ρ₁ le_rfl (mem_ball_self x hρ₁0)
    have hFx : F x = f x := Set.indicator_of_mem hxR f
    have hxl' : l < |f x| := lt_of_le_of_lt (le_mul_of_one_le_left hl.le hM) hxl
    have hev := hP l (by rw [hFx]; exact hxl')
    have htend : Tendsto (fun k : ℕ => ρ₁ / 2 ^ k) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k =>
        Set.mem_Ioi.mpr (by positivity)⟩
      have h1 : Tendsto (fun k : ℕ => ρ₁ * (1 / 2 : ℝ) ^ k) atTop (𝓝 (ρ₁ * 0)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _
      rw [mul_zero] at h1
      refine h1.congr fun k => ?_
      rw [one_div, inv_pow]
      field_simp
    obtain ⟨k, hk⟩ := (htend.eventually hev).exists
    refine ⟨hxs, hxl, k, ?_⟩
    have hρk : 0 < ρ₁ / 2 ^ k := by positivity
    have hρkle : ρ₁ / 2 ^ k ≤ ρ₁ := div_le_self hρ₁0.le (one_le_pow₀ (by norm_num))
    have hsub := hsubR x hxs _ hρkle
    have havg : ⨍ y in ball x (ρ₁ / 2 ^ k), |F y| ∂volume =
        ⨍ y in ball x (ρ₁ / 2 ^ k), |f y| ∂volume := by
      rw [setAverage_eq, setAverage_eq]
      congr 1
      refine setIntegral_congr_fun (measurableSet_ball x _) fun y hy => ?_
      simp only [hF, Set.indicator_of_mem (hsub hy)]
    rw [havg] at hk
    have h1 : ENNReal.ofReal l < ENNReal.ofReal (⨍ y in ball x (ρ₁ / 2 ^ k), |f y| ∂volume) :=
      (ENNReal.ofReal_lt_ofReal_iff (hl.trans hk)).mpr hk
    have h2 := ofReal_setAverage_abs_le_eLpMeanNormOn_two (volume_ball_ne_zero' x hρk)
      (volume_ball_ne_top' x _) (hfint.mono_set hsub)
    exact (h1.trans_le h2).trans_le le_self_add
  -- the stopping radii and the estimate on each ball
  have hstop : ∀ z : Z, ∃ r : ℝ, 0 < r ∧ 16 * r ≤ ρ₁ ∧
      ∫⁻ x in ball z.1 (8 * r) ∩ S, ‖f x‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (16 * 8 ^ d * c₀) *
          ((∫⁻ x in ball z.1 r ∩ {x | l / 4 < |f x|}, ‖f x‖ₑ ^ (2 : ℝ)) +
            ∫⁻ x in ball z.1 r ∩ {x | l / 4 < |G x|}, ‖G x‖ₑ ^ (2 : ℝ)) := by
    intro z
    obtain ⟨r, hr, hr16, hlow, hup⟩ :=
      exists_cz_stopping_radius hR hs hst ht hfm hGm hl₀ z.2.1 z.2.2.2
    refine ⟨r, hr, hr16, ?_⟩
    have h8 : 0 < 8 * r := by positivity
    have hsub : ball z.1 (2 * (8 * r)) ⊆ ball 0 R :=
      hsubR z.1 z.2.1 _ (by linarith)
    obtain ⟨h, hhm, hhq, hfh⟩ := happrox z.1 (8 * r) h8 hsub
    have e16 : 2 * (8 * r) = 16 * r := by ring
    rw [e16] at hhq hfh
    have hup' : PDE.eLpMeanNormOn (ball z.1 (16 * r)) 2 G +
        PDE.eLpMeanNormOn (ball z.1 (16 * r)) 2 f ≤ ENNReal.ofReal l := by
      rw [add_comm]
      exact hup
    have hhq' : PDE.eLpMeanNormOn (ball z.1 (8 * r)) (ENNReal.ofReal q) h ≤
        ENNReal.ofReal (A * l) := by
      rw [ENNReal.ofReal_mul hA]
      exact hhq.trans (by gcongr)
    have hfh' : PDE.eLpMeanNormOn (ball z.1 (8 * r)) 2 (f - h) ≤ ENNReal.ofReal (η * l) := by
      rw [ENNReal.ofReal_mul hη]
      exact hfh.trans (by gcongr)
    have hball := setLIntegral_levelSet_le_of_approx (measurableSet_ball _ _)
      (volume_ball_ne_zero' z.1 h8) (volume_ball_ne_top' z.1 _) hfm hhm (M := M) hq hA hη
      (by linarith) hl hhq' hfh'
    have hvol := volume_mul_sq_le_levelSets (volume_ball_ne_top' z.1 r) hfm hGm hl hlow
    calc ∫⁻ x in ball z.1 (8 * r) ∩ S, ‖f x‖ₑ ^ (2 : ℝ)
        ≤ ENNReal.ofReal (c₀ * l ^ 2) * volume (ball z.1 (8 * r)) := hball
      _ = ENNReal.ofReal (c₀ * 8 ^ d) * (ENNReal.ofReal (l ^ 2) * volume (ball z.1 r)) := by
          rw [volume_ball_mul z.1 (by norm_num : (0 : ℝ) < 8) hr,
            ENNReal.ofReal_mul hc₀0, ENNReal.ofReal_mul hc₀0]
          ring
      _ ≤ ENNReal.ofReal (c₀ * 8 ^ d) * (ENNReal.ofReal 16 *
            ((∫⁻ x in ball z.1 r ∩ {x | l / 4 < |f x|}, ‖f x‖ₑ ^ (2 : ℝ)) +
              ∫⁻ x in ball z.1 r ∩ {x | l / 4 < |G x|}, ‖G x‖ₑ ^ (2 : ℝ))) := by gcongr
      _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          ring
  choose r hr using hstop
  obtain ⟨J, hJc, hJd, hJcov⟩ := lemma_C_5 (fun z : Z => z.1) r ρ₁ fun z =>
    le_trans (by linarith [(hr z).1]) (hr z).2.1
  have : Countable J := hJc.to_subtype
  have hZcov : Z ⊆ ⋃ β : J, ball β.1.1 (8 * r β.1) ∩ S := by
    intro z hz
    have h1 : z ∈ ⋃ α : Z, ball α.1 (r α) :=
      Set.mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self z (hr ⟨z, hz⟩).1⟩
    have h2 := hJcov h1
    rw [Set.biUnion_eq_iUnion] at h2
    obtain ⟨β, hβ⟩ := Set.mem_iUnion.mp h2
    refine Set.mem_iUnion.mpr ⟨β, ?_, hz.2.1⟩
    have hβ' : euclideanNorm (z - β.1.1) < 5 * r β.1 := hβ
    change euclideanNorm (z - β.1.1) < 8 * r β.1
    linarith [(hr β.1).1]
  set Sf := {x | l / 4 < |f x|} with hSf
  set SG := {x | l / 4 < |G x|} with hSG
  have hSfm : MeasurableSet Sf := measurableSet_lt measurable_const hfm.abs
  have hSGm : MeasurableSet SG := measurableSet_lt measurable_const hGm.abs
  have hdisj : ∀ T : Set (Vec d), Pairwise (Function.onFun Disjoint
      fun β : J => ball β.1.1 (r β.1) ∩ T) := by
    intro T β γ hβγ
    have h := hJd β.2 γ.2 (fun h => hβγ (Subtype.ext h))
    exact h.mono Set.inter_subset_left Set.inter_subset_left
  have hsum : ∀ (T : Set (Vec d)), MeasurableSet T → ∀ k : Vec d → ℝ,
      ∑' β : J, ∫⁻ x in ball β.1.1 (r β.1) ∩ T, ‖k x‖ₑ ^ (2 : ℝ) ≤
        ∫⁻ x in ball 0 (t * R) ∩ T, ‖k x‖ₑ ^ (2 : ℝ) := by
    intro T hT k
    rw [← lintegral_iUnion (fun β => (measurableSet_ball _ _).inter hT) (hdisj T)]
    refine lintegral_mono_set fun x hx => ?_
    obtain ⟨β, hxβ, hxT⟩ := Set.mem_iUnion.mp hx
    exact ⟨hsubt β.1.1 β.1.2.1 (r β.1) (by linarith [(hr β.1).1, (hr β.1).2.1]) hxβ, hxT⟩
  calc ∫⁻ x in ball 0 (s * R) ∩ S, ‖f x‖ₑ ^ (2 : ℝ)
      ≤ ∫⁻ x in Z ∪ ((ball 0 (s * R) ∩ S) \ Z), ‖f x‖ₑ ^ (2 : ℝ) :=
        lintegral_mono_set fun x hx => by
          by_cases hxZ : x ∈ Z
          · exact Or.inl hxZ
          · exact Or.inr ⟨hx, hxZ⟩
    _ ≤ (∫⁻ x in Z, ‖f x‖ₑ ^ (2 : ℝ)) +
          ∫⁻ x in (ball 0 (s * R) ∩ S) \ Z, ‖f x‖ₑ ^ (2 : ℝ) :=
        lintegral_union_le _ _ _
    _ = ∫⁻ x in Z, ‖f x‖ₑ ^ (2 : ℝ) := by
        rw [setLIntegral_measure_zero _ _ hnull, add_zero]
    _ ≤ ∫⁻ x in ⋃ β : J, ball β.1.1 (8 * r β.1) ∩ S, ‖f x‖ₑ ^ (2 : ℝ) :=
        lintegral_mono_set hZcov
    _ ≤ ∑' β : J, ∫⁻ x in ball β.1.1 (8 * r β.1) ∩ S, ‖f x‖ₑ ^ (2 : ℝ) :=
        lintegral_iUnion_le _ _
    _ ≤ ∑' β : J, ENNReal.ofReal (16 * 8 ^ d * c₀) *
          ((∫⁻ x in ball β.1.1 (r β.1) ∩ Sf, ‖f x‖ₑ ^ (2 : ℝ)) +
            ∫⁻ x in ball β.1.1 (r β.1) ∩ SG, ‖G x‖ₑ ^ (2 : ℝ)) :=
        ENNReal.tsum_le_tsum fun β => (hr β.1).2.2
    _ = ENNReal.ofReal (16 * 8 ^ d * c₀) *
          ((∑' β : J, ∫⁻ x in ball β.1.1 (r β.1) ∩ Sf, ‖f x‖ₑ ^ (2 : ℝ)) +
            ∑' β : J, ∫⁻ x in ball β.1.1 (r β.1) ∩ SG, ‖G x‖ₑ ^ (2 : ℝ)) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
    _ ≤ _ := by
        gcongr
        · exact hsum Sf hSfm f
        · exact hsum SG hSGm G

end QSH
