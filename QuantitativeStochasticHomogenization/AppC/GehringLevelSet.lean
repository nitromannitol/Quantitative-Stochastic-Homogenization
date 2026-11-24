import QuantitativeStochasticHomogenization.AppC.GehringBallEstimates

/-!
# The level set estimate in the proof of Gehring's lemma

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma C.4, estimate (C.10). Fix `R > 0`, `0 < σ < τ ≤ 1`, and functions `f, g` satisfying
the reverse Hölder inequality (C.7) on every ball `B_r(z) ⊆ B_R`. With
`λ₀ = (160/(τ - σ))^{d/2} (‖f‖_{L̲²(B_R)} + ‖g‖_{L̲²(B_R)})`, every `λ > λ₀` satisfies
`∫_{B_{σR} ∩ {|f| > λ}} f² ≤ 8^d (8K)^q λ^{2-q} ∫_{B_{τR} ∩ {|f| > λ/(8K)}} |f|^q
  + 8^d (8K)² ∫_{B_{τR} ∩ {|g| > λ/(8K)}} g²`.

The proof is the book's: at almost every point `z ∈ B_{σR}` with `|f(z)| > λ` (Lebesgue
differentiation on balls) a stopping radius `r_z ≤ (τ - σ)R/10` has
`λ < E(z, r_z) := ‖f‖_{L̲²(B_{r_z/2}(z))} + ‖g‖_{L̲²(B_{r_z}(z))}` and
`∫_{B_{5 r_z}(z)} f² ≤ 8^d λ² |B_{r_z}|`; the reverse Hölder inequality bounds `|B_{r_z}|` by the
integrals over the level sets, and the Vitali covering lemma (Lemma C.5) sums these bounds over
a countable disjoint subfamily. The stopping radius is taken among the dyadic radii
`(τ - σ)R/(10 · 2^k)`, and the factor `160` (instead of the book's `20`) in `λ₀` makes the first
four dyadic radii admissible, which gives the constant `8^d` in place of the book's `5^d`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

theorem volume_ball_eq_unit (z : Vec d) {ρ : ℝ} (hρ : 0 < ρ) :
    volume (ball z ρ) = ENNReal.ofReal (ρ ^ d) * volume (PDE.euclideanBall (0 : Vec d) 1) := by
  rw [ball_eq_euclideanBall z hρ]
  exact PDE.volume_euclideanBall_eq_unit_mul_of_pos z hρ

theorem ball_subset_ball_of_norm {z w : Vec d} {ρ R : ℝ} (h : euclideanNorm (z - w) + ρ ≤ R) :
    ball z ρ ⊆ ball w R := by
  intro x hx
  have hx' : euclideanNorm (x - z) < ρ := hx
  change euclideanNorm (x - w) < R
  have := euclideanNorm_sub_le_add x z w
  linarith

theorem lintegral_ball_eq_volume_mul (z : Vec d) {ρ : ℝ} (hρ : 0 < ρ) {h : Vec d → ℝ}
    (hh : AEStronglyMeasurable h (volume.restrict (ball z ρ))) :
    ∫⁻ x in ball z ρ, ‖h x‖ₑ ^ (2 : ℝ) =
      volume (ball z ρ) * PDE.eLpMeanNormOn (ball z ρ) 2 h ^ (2 : ℝ) := by
  have e := eLpMeanNormOn_rpow_eq (U := ball z ρ) (s := 2) two_pos hh
  rw [ENNReal.ofReal_ofNat] at e
  rw [e, ← mul_assoc, ENNReal.mul_inv_cancel (volume_ball_ne_zero' z hρ) (volume_ball_ne_top' z ρ),
    one_mul]

/-- `‖h‖_{L̲²(B_ρ(z))} ≤ (R/ρ)^{d/2} ‖h‖_{L̲²(B_R)}` for `B_ρ(z) ⊆ B_R`. -/
theorem eLpMeanNormOn_ball_le {z : Vec d} {ρ R : ℝ} (hρ : 0 < ρ) (hR : 0 < R)
    (hsub : ball z ρ ⊆ ball 0 R) {h : Vec d → ℝ} (hh : Measurable h) :
    PDE.eLpMeanNormOn (ball z ρ) 2 h ≤
      ENNReal.ofReal ((R / ρ) ^ ((d : ℝ) / 2)) * PDE.eLpMeanNormOn (ball 0 R) 2 h := by
  have e1 := eLpMeanNormOn_rpow_eq (U := ball z ρ) (s := 2) two_pos hh.aestronglyMeasurable
  have e2 := eLpMeanNormOn_rpow_eq (U := ball 0 R) (s := 2) two_pos hh.aestronglyMeasurable
  rw [ENNReal.ofReal_ofNat] at e1 e2
  set ω := volume (PDE.euclideanBall (0 : Vec d) 1)
  have hω0 : ω ≠ 0 := (PDE.volume_euclideanBall_pos 0 one_pos).ne'
  have hωt : ω ≠ ⊤ := PDE.volume_euclideanBall_ne_top 0 zero_le_one
  have hsq : PDE.eLpMeanNormOn (ball z ρ) 2 h ^ (2 : ℝ) ≤
      ENNReal.ofReal ((R / ρ) ^ d) * PDE.eLpMeanNormOn (ball 0 R) 2 h ^ (2 : ℝ) := by
    rw [e1, e2, volume_ball_eq_unit z hρ, volume_ball_eq_unit 0 hR]
    have hmono : ∫⁻ x in ball z ρ, ‖h x‖ₑ ^ (2 : ℝ) ≤ ∫⁻ x in ball 0 R, ‖h x‖ₑ ^ (2 : ℝ) :=
      lintegral_mono_set hsub
    have hρd : ENNReal.ofReal (ρ ^ d) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]; exact pow_pos hρ d
    have hRd : ENNReal.ofReal (R ^ d) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]; exact pow_pos hR d
    have hratio : (ENNReal.ofReal (ρ ^ d) * ω)⁻¹ =
        ENNReal.ofReal ((R / ρ) ^ d) * (ENNReal.ofReal (R ^ d) * ω)⁻¹ := by
      rw [ENNReal.mul_inv (Or.inl hρd) (Or.inl ENNReal.ofReal_ne_top),
        ENNReal.mul_inv (Or.inl hRd) (Or.inl ENNReal.ofReal_ne_top), ← mul_assoc,
        ← ENNReal.ofReal_inv_of_pos (pow_pos hρ d), ← ENNReal.ofReal_inv_of_pos (pow_pos hR d),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      rw [div_pow]
      field_simp
    rw [hratio, mul_assoc]
    gcongr
  have hroot := ENNReal.rpow_le_rpow hsq (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.rpow_one, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at hroot
  convert hroot using 3
  ring_nf

/-- The admissible dyadic radii: on the first four dyadic radii `ρ₁/2^j`, `j ≤ 3`, the quantity
`E(z, ρ₁/2^j)` is at most `λ₀`. -/
theorem E_le_lambda0 {R σ τ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hστ : σ < τ) (hτ : τ ≤ 1)
    {f g : Vec d → ℝ} (hfm : Measurable f) (hgm : Measurable g) {z : Vec d}
    (hz : z ∈ ball 0 (σ * R)) {j : ℕ} (hj : j ≤ 3) :
    PDE.eLpMeanNormOn (ball z ((τ - σ) * R / 10 / 2 ^ j / 2)) 2 f +
        PDE.eLpMeanNormOn (ball z ((τ - σ) * R / 10 / 2 ^ j)) 2 g ≤
      ENNReal.ofReal ((160 / (τ - σ)) ^ ((d : ℝ) / 2)) *
        (PDE.eLpMeanNormOn (ball 0 R) 2 f + PDE.eLpMeanNormOn (ball 0 R) 2 g) := by
  have hts : 0 < τ - σ := by linarith
  set ρ := (τ - σ) * R / 10 / 2 ^ j with hρdef
  have h2j : (2 : ℝ) ^ j ≤ 8 := by
    calc (2 : ℝ) ^ j ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hj
      _ = 8 := by norm_num
  have hρ : 0 < ρ := by positivity
  have hρle : ρ ≤ (τ - σ) * R / 10 := div_le_self (by positivity) (one_le_pow₀ (by norm_num))
  have hρge : (τ - σ) * R / 80 ≤ ρ := by
    rw [hρdef, div_div, le_div_iff₀ (by positivity)]
    nlinarith [mul_pos hts hR]
  have hzn : euclideanNorm (z - 0) < σ * R := hz
  have hsub1 : ball z ρ ⊆ ball 0 R := ball_subset_ball_of_norm (by nlinarith)
  have hsub2 : ball z (ρ / 2) ⊆ ball 0 R := ball_subset_ball_of_norm (by nlinarith)
  have h1 := eLpMeanNormOn_ball_le (half_pos hρ) hR hsub2 hfm
  have h2 := eLpMeanNormOn_ball_le hρ hR hsub1 hgm
  have hd0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hc1 : ENNReal.ofReal ((R / (ρ / 2)) ^ ((d : ℝ) / 2)) ≤
      ENNReal.ofReal ((160 / (τ - σ)) ^ ((d : ℝ) / 2)) := by
    refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) ?_ hd0)
    rw [div_le_div_iff₀ (by positivity) hts]
    nlinarith
  have hc2 : ENNReal.ofReal ((R / ρ) ^ ((d : ℝ) / 2)) ≤
      ENNReal.ofReal ((160 / (τ - σ)) ^ ((d : ℝ) / 2)) := by
    refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) ?_ hd0)
    rw [div_le_div_iff₀ hρ hts]
    nlinarith
  calc PDE.eLpMeanNormOn (ball z (ρ / 2)) 2 f + PDE.eLpMeanNormOn (ball z ρ) 2 g
      ≤ ENNReal.ofReal ((R / (ρ / 2)) ^ ((d : ℝ) / 2)) * PDE.eLpMeanNormOn (ball 0 R) 2 f +
          ENNReal.ofReal ((R / ρ) ^ ((d : ℝ) / 2)) * PDE.eLpMeanNormOn (ball 0 R) 2 g :=
        add_le_add h1 h2
    _ ≤ ENNReal.ofReal ((160 / (τ - σ)) ^ ((d : ℝ) / 2)) * PDE.eLpMeanNormOn (ball 0 R) 2 f +
          ENNReal.ofReal ((160 / (τ - σ)) ^ ((d : ℝ) / 2)) * PDE.eLpMeanNormOn (ball 0 R) 2 g := by
        gcongr
    _ = _ := (mul_add _ _ _).symm

/-- **The stopping radius.** If `λ > λ₀` and `λ < E(z, ρ₁/2^k)` for some `k`, with
`ρ₁ = (τ - σ)R/10`, then some `r ∈ (0, ρ₁]` has `λ < E(z, r)` and
`∫_{B_{5r}(z)} f² ≤ 8^d λ² |B_r(z)|`. -/
theorem exists_stopping_radius {R σ τ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hστ : σ < τ)
    (hτ : τ ≤ 1) {f g : Vec d → ℝ} (hfm : Measurable f) (hgm : Measurable g) {l : ℝ}
    (hl : 0 < l)
    (hl₀ : ENNReal.ofReal ((160 / (τ - σ)) ^ ((d : ℝ) / 2)) *
        (PDE.eLpMeanNormOn (ball 0 R) 2 f + PDE.eLpMeanNormOn (ball 0 R) 2 g) < ENNReal.ofReal l)
    {z : Vec d} (hz : z ∈ ball 0 (σ * R))
    (hk : ∃ k : ℕ, ENNReal.ofReal l <
      PDE.eLpMeanNormOn (ball z ((τ - σ) * R / 10 / 2 ^ k / 2)) 2 f +
        PDE.eLpMeanNormOn (ball z ((τ - σ) * R / 10 / 2 ^ k)) 2 g) :
    ∃ r : ℝ, 0 < r ∧ r ≤ (τ - σ) * R / 10 ∧
      ENNReal.ofReal l < PDE.eLpMeanNormOn (ball z (r / 2)) 2 f +
        PDE.eLpMeanNormOn (ball z r) 2 g ∧
      ∫⁻ x in ball z (5 * r), ‖f x‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (8 ^ d * l ^ 2) * volume (ball z r) := by
  classical
  have hts : 0 < τ - σ := by linarith
  set ρ₁ := (τ - σ) * R / 10 with hρ₁
  have hρ₁0 : 0 < ρ₁ := by positivity
  set k₀ := Nat.find hk with hk₀
  have hspec := Nat.find_spec hk
  have h4 : 4 ≤ k₀ := by
    by_contra hlt
    have hle : k₀ ≤ 3 := by omega
    have := E_le_lambda0 hR hσ hστ hτ hfm hgm hz hle
    exact absurd (hspec.trans_le this) (not_lt.mpr hl₀.le)
  set r := ρ₁ / 2 ^ k₀ with hrdef
  have hr : 0 < r := by positivity
  refine ⟨r, hr, div_le_self hρ₁0.le (one_le_pow₀ (by norm_num)), hspec, ?_⟩
  have hmin := Nat.find_min hk (show k₀ - 4 < k₀ by omega)
  push Not at hmin
  have h16 : ρ₁ / 2 ^ (k₀ - 4) / 2 = 8 * r := by
    have e : (2 : ℝ) ^ k₀ = 2 ^ (k₀ - 4) * 16 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_add, Nat.sub_add_cancel h4]
    rw [hrdef, e]
    field_simp
    ring
  rw [h16] at hmin
  have hN : PDE.eLpMeanNormOn (ball z (8 * r)) 2 f ≤ ENNReal.ofReal l := le_self_add.trans hmin
  have h8r : 0 < 8 * r := by positivity
  calc ∫⁻ x in ball z (5 * r), ‖f x‖ₑ ^ (2 : ℝ) ≤ ∫⁻ x in ball z (8 * r), ‖f x‖ₑ ^ (2 : ℝ) := by
        refine lintegral_mono_set fun x hx => ?_
        have hx' : euclideanNorm (x - z) < 5 * r := hx
        change euclideanNorm (x - z) < 8 * r
        linarith
    _ = volume (ball z (8 * r)) * PDE.eLpMeanNormOn (ball z (8 * r)) 2 f ^ (2 : ℝ) :=
        lintegral_ball_eq_volume_mul z h8r hfm.aestronglyMeasurable
    _ ≤ volume (ball z (8 * r)) * ENNReal.ofReal l ^ (2 : ℝ) := by
        gcongr
    _ = ENNReal.ofReal (8 ^ d * l ^ 2) * volume (ball z r) := by
        rw [volume_ball_mul z (by norm_num : (0 : ℝ) < 8) hr,
          ENNReal.ofReal_rpow_of_nonneg hl.le (by norm_num), Real.rpow_two,
          ENNReal.ofReal_mul (by positivity)]
        ring

/-- **The bound after (C.9).** If `λ < E(z, r)` on a ball `B_r(z)` where the reverse Hölder
inequality holds, then
`|B_r(z)| ≤ (8K/λ)^q ∫_{B_r(z) ∩ {|f| > λ/(8K)}} |f|^q + (8K/λ)² ∫_{B_r(z) ∩ {|g| > λ/(8K)}} g²`. -/
theorem volume_ball_le_levelSets {K q l : ℝ} (hK : 1 ≤ K) (hq : 1 ≤ q) (hl : 0 < l)
    {f g : Vec d → ℝ} (hfm : Measurable f) (hgm : Measurable g) {z : Vec d} {r : ℝ}
    (hRH : PDE.eLpMeanNormOn (ball z (r / 2)) 2 f ≤ ENNReal.ofReal K *
      (PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal q) f + PDE.eLpMeanNormOn (ball z r) 2 g))
    (hE : ENNReal.ofReal l < PDE.eLpMeanNormOn (ball z (r / 2)) 2 f +
      PDE.eLpMeanNormOn (ball z r) 2 g) :
    volume (ball z r) ≤
      ENNReal.ofReal ((8 * K / l) ^ q) *
          (∫⁻ x in ball z r ∩ {x | l / (8 * K) < |f x|}, ‖f x‖ₑ ^ q) +
        ENNReal.ofReal ((8 * K / l) ^ (2 : ℝ)) *
          ∫⁻ x in ball z r ∩ {x | l / (8 * K) < |g x|}, ‖g x‖ₑ ^ (2 : ℝ) := by
  set A := PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal q) f with hA
  set Bg := PDE.eLpMeanNormOn (ball z r) 2 g with hBg
  have hK0 : 0 < K := by linarith
  have h1 : ENNReal.ofReal l < ENNReal.ofReal K * A + ENNReal.ofReal (2 * K) * Bg := by
    have hK1 : ENNReal.ofReal K + 1 ≤ ENNReal.ofReal (2 * K) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add hK0.le zero_le_one]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    calc ENNReal.ofReal l < _ := hE
      _ ≤ ENNReal.ofReal K * (A + Bg) + Bg := add_le_add hRH le_rfl
      _ = ENNReal.ofReal K * A + (ENNReal.ofReal K + 1) * Bg := by ring
      _ ≤ ENNReal.ofReal K * A + ENNReal.ofReal (2 * K) * Bg := by gcongr
  set t := l / (8 * K) with ht
  have htpos : 0 < t := by positivity
  have hcase : ENNReal.ofReal (4 * t) < A ∨ ENNReal.ofReal (2 * t) < Bg := by
    by_contra hcon
    push Not at hcon
    have hsum : ENNReal.ofReal K * A + ENNReal.ofReal (2 * K) * Bg ≤ ENNReal.ofReal l := by
      calc ENNReal.ofReal K * A + ENNReal.ofReal (2 * K) * Bg ≤
          ENNReal.ofReal K * ENNReal.ofReal (4 * t) +
            ENNReal.ofReal (2 * K) * ENNReal.ofReal (2 * t) := by gcongr
              <;> [exact hcon.1; exact hcon.2]
        _ = ENNReal.ofReal l := by
          rw [← ENNReal.ofReal_mul hK0.le, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          rw [ht]
          field_simp
          ring
    exact absurd (h1.trans_le hsum) (lt_irrefl _)
  have hinv : t⁻¹ = 8 * K / l := by rw [ht, inv_div]
  rcases hcase with h | h
  · have hc : 2 ≤ (4 : ℝ) ^ q := by
      calc (2 : ℝ) ≤ 4 ^ (1 : ℝ) := by norm_num
        _ ≤ 4 ^ q := Real.rpow_le_rpow_of_exponent_le (by norm_num) hq
    have hv := volume_le_of_lt_eLpMeanNormOn (volume_ball_ne_top' z r) hfm (by linarith)
      htpos (by norm_num) hc h
    rw [hinv] at hv
    exact hv.trans le_self_add
  · have hc : 2 ≤ (2 : ℝ) ^ (2 : ℝ) := by norm_num
    have h' : ENNReal.ofReal (2 * t) < PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal 2) g := by
      rw [ENNReal.ofReal_ofNat]
      exact h
    have hv := volume_le_of_lt_eLpMeanNormOn (volume_ball_ne_top' z r) hgm two_pos htpos
      two_pos hc h'
    rw [hinv] at hv
    exact hv.trans le_add_self

/-- **The level set estimate (C.10).** For `λ > λ₀`,
`∫_{B_{σR} ∩ {|f| > λ}} f² ≤ 8^d λ² ((8K/λ)^q ∫_{B_{τR} ∩ {|f| > λ/(8K)}} |f|^q
  + (8K/λ)² ∫_{B_{τR} ∩ {|g| > λ/(8K)}} g²)`. -/
theorem levelSet_estimate {R σ τ K q l : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hστ : σ < τ)
    (hτ : τ ≤ 1) (hK : 1 ≤ K) (hq : 1 ≤ q) (hl : 0 < l) {f g : Vec d → ℝ} (hfm : Measurable f)
    (hgm : Measurable g) (hfint : IntegrableOn f (ball 0 R))
    (hRH : ∀ (z : Vec d) (r : ℝ), 0 < r → ball z r ⊆ ball 0 R →
      PDE.eLpMeanNormOn (ball z (r / 2)) 2 f ≤ ENNReal.ofReal K *
        (PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal q) f + PDE.eLpMeanNormOn (ball z r) 2 g))
    (hl₀ : ENNReal.ofReal ((160 / (τ - σ)) ^ ((d : ℝ) / 2)) *
        (PDE.eLpMeanNormOn (ball 0 R) 2 f + PDE.eLpMeanNormOn (ball 0 R) 2 g) < ENNReal.ofReal l) :
    ∫⁻ x in ball 0 (σ * R) ∩ {x | l < |f x|}, ‖f x‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (8 ^ d * l ^ 2) *
        (ENNReal.ofReal ((8 * K / l) ^ q) *
            (∫⁻ x in ball 0 (τ * R) ∩ {x | l / (8 * K) < |f x|}, ‖f x‖ₑ ^ q) +
          ENNReal.ofReal ((8 * K / l) ^ (2 : ℝ)) *
            ∫⁻ x in ball 0 (τ * R) ∩ {x | l / (8 * K) < |g x|}, ‖g x‖ₑ ^ (2 : ℝ)) := by
  classical
  have hts : 0 < τ - σ := by linarith
  set ρ₁ := (τ - σ) * R / 10 with hρ₁
  have hρ₁0 : 0 < ρ₁ := by positivity
  set Z : Set (Vec d) := {z | z ∈ ball 0 (σ * R) ∧ l < |f z| ∧ ∃ k : ℕ, ENNReal.ofReal l <
      PDE.eLpMeanNormOn (ball z (ρ₁ / 2 ^ k / 2)) 2 f +
        PDE.eLpMeanNormOn (ball z (ρ₁ / 2 ^ k)) 2 g} with hZ
  have hsubR : ∀ z ∈ ball (0 : Vec d) (σ * R), ∀ ρ, ρ ≤ ρ₁ → ball z ρ ⊆ ball 0 R := by
    intro z hz ρ hρ
    have hzn : euclideanNorm (z - 0) < σ * R := hz
    exact ball_subset_ball_of_norm (by nlinarith)
  have hsubτ : ∀ z ∈ ball (0 : Vec d) (σ * R), ∀ ρ, ρ ≤ ρ₁ → ball z ρ ⊆ ball 0 (τ * R) := by
    intro z hz ρ hρ
    have hzn : euclideanNorm (z - 0) < σ * R := hz
    exact ball_subset_ball_of_norm (by nlinarith)
  -- almost every point of the level set is in `Z`
  have hnull : volume ((ball 0 (σ * R) ∩ {x | l < |f x|}) \ Z) = 0 := by
    set F := (ball (0 : Vec d) R).indicator f with hF
    have hFli : LocallyIntegrable F volume :=
      (hfint.integrable_indicator (measurableSet_ball 0 R)).locallyIntegrable
    have hae := ae_eventually_lt_ballAverage_abs hFli
    refine measure_mono_null ?_ (ae_iff.mp hae)
    rintro x ⟨⟨hxσ, hxl⟩, hxZ⟩ hP
    apply hxZ
    have hxR : x ∈ ball (0 : Vec d) R := hsubR x hxσ ρ₁ le_rfl (mem_ball_self x hρ₁0)
    have hFx : F x = f x := Set.indicator_of_mem hxR f
    have hev := hP l (by rw [hFx]; exact hxl)
    have htend : Tendsto (fun k : ℕ => ρ₁ / 2 ^ k / 2) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k =>
        Set.mem_Ioi.mpr (by positivity)⟩
      have h1 : Tendsto (fun k : ℕ => (ρ₁ / 2) * (1 / 2 : ℝ) ^ k) atTop (𝓝 ((ρ₁ / 2) * 0)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _
      rw [mul_zero] at h1
      refine h1.congr fun k => ?_
      rw [one_div, inv_pow]
      field_simp
    obtain ⟨k, hk⟩ := (htend.eventually hev).exists
    refine ⟨hxσ, hxl, k, ?_⟩
    have hρk : 0 < ρ₁ / 2 ^ k / 2 := by positivity
    have hρkle : ρ₁ / 2 ^ k / 2 ≤ ρ₁ := by
      calc ρ₁ / 2 ^ k / 2 ≤ ρ₁ / 2 ^ k := div_le_self (by positivity) (by norm_num)
        _ ≤ ρ₁ := div_le_self hρ₁0.le (one_le_pow₀ (by norm_num))
    have hsub := hsubR x hxσ _ hρkle
    have havg : ⨍ y in ball x (ρ₁ / 2 ^ k / 2), |F y| ∂volume =
        ⨍ y in ball x (ρ₁ / 2 ^ k / 2), |f y| ∂volume := by
      rw [setAverage_eq, setAverage_eq]
      congr 1
      refine setIntegral_congr_fun (measurableSet_ball x _) fun y hy => ?_
      simp only [hF, Set.indicator_of_mem (hsub hy)]
    rw [havg] at hk
    have h1 : ENNReal.ofReal l < ENNReal.ofReal (⨍ y in ball x (ρ₁ / 2 ^ k / 2), |f y| ∂volume) :=
      (ENNReal.ofReal_lt_ofReal_iff (hl.trans hk)).mpr hk
    have h2 := ofReal_setAverage_abs_le_eLpMeanNormOn_two (volume_ball_ne_zero' x hρk)
      (volume_ball_ne_top' x _) (hfint.mono_set hsub)
    exact (h1.trans_le h2).trans_le le_self_add
  -- the stopping radii
  have hstop : ∀ z : Z, ∃ r : ℝ, 0 < r ∧ r ≤ ρ₁ ∧
      ENNReal.ofReal l < PDE.eLpMeanNormOn (ball z.1 (r / 2)) 2 f +
        PDE.eLpMeanNormOn (ball z.1 r) 2 g ∧
      ∫⁻ x in ball z.1 (5 * r), ‖f x‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (8 ^ d * l ^ 2) * volume (ball z.1 r) := fun z =>
    exists_stopping_radius hR hσ hστ hτ hfm hgm hl hl₀ z.2.1 z.2.2.2
  choose r hr using hstop
  obtain ⟨J, hJc, hJd, hJcov⟩ := lemma_C_5 (fun z : Z => z.1) r ρ₁ fun z => (hr z).2.1
  have : Countable J := hJc.to_subtype
  have hZcov : Z ⊆ ⋃ β : J, ball β.1.1 (5 * r β.1) := by
    intro z hz
    have h1 : z ∈ ⋃ α : Z, ball α.1 (r α) :=
      Set.mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self z (hr ⟨z, hz⟩).1⟩
    have h2 := hJcov h1
    rw [Set.biUnion_eq_iUnion] at h2
    exact h2
  set Sf := {x | l / (8 * K) < |f x|} with hSf
  set Sg := {x | l / (8 * K) < |g x|} with hSg
  have hSfm : MeasurableSet Sf := measurableSet_lt measurable_const hfm.abs
  have hSgm : MeasurableSet Sg := measurableSet_lt measurable_const hgm.abs
  have hdisj : ∀ S : Set (Vec d), Pairwise (Function.onFun Disjoint
      fun β : J => ball β.1.1 (r β.1) ∩ S) := by
    intro S β γ hβγ
    have h := hJd β.2 γ.2 (fun h => hβγ (Subtype.ext h))
    exact h.mono Set.inter_subset_left Set.inter_subset_left
  have hsum : ∀ (S : Set (Vec d)), MeasurableSet S → ∀ (s : ℝ) (h : Vec d → ℝ),
      ∑' β : J, ∫⁻ x in ball β.1.1 (r β.1) ∩ S, ‖h x‖ₑ ^ s ≤
        ∫⁻ x in ball 0 (τ * R) ∩ S, ‖h x‖ₑ ^ s := by
    intro S hS s h
    rw [← lintegral_iUnion (fun β => (measurableSet_ball _ _).inter hS) (hdisj S)]
    refine lintegral_mono_set fun x hx => ?_
    obtain ⟨β, hxβ, hxS⟩ := Set.mem_iUnion.mp hx
    exact ⟨hsubτ β.1.1 β.1.2.1 (r β.1) (hr β.1).2.1 hxβ, hxS⟩
  set A := ENNReal.ofReal ((8 * K / l) ^ q)
  set B := ENNReal.ofReal ((8 * K / l) ^ (2 : ℝ))
  calc ∫⁻ x in ball 0 (σ * R) ∩ {x | l < |f x|}, ‖f x‖ₑ ^ (2 : ℝ)
      ≤ ∫⁻ x in Z ∪ ((ball 0 (σ * R) ∩ {x | l < |f x|}) \ Z), ‖f x‖ₑ ^ (2 : ℝ) :=
        lintegral_mono_set fun x hx => by
          by_cases hxZ : x ∈ Z
          · exact Or.inl hxZ
          · exact Or.inr ⟨hx, hxZ⟩
    _ ≤ (∫⁻ x in Z, ‖f x‖ₑ ^ (2 : ℝ)) +
          ∫⁻ x in (ball 0 (σ * R) ∩ {x | l < |f x|}) \ Z, ‖f x‖ₑ ^ (2 : ℝ) :=
        lintegral_union_le _ _ _
    _ = ∫⁻ x in Z, ‖f x‖ₑ ^ (2 : ℝ) := by
        rw [setLIntegral_measure_zero _ _ hnull, add_zero]
    _ ≤ ∫⁻ x in ⋃ β : J, ball β.1.1 (5 * r β.1), ‖f x‖ₑ ^ (2 : ℝ) := lintegral_mono_set hZcov
    _ ≤ ∑' β : J, ∫⁻ x in ball β.1.1 (5 * r β.1), ‖f x‖ₑ ^ (2 : ℝ) := lintegral_iUnion_le _ _
    _ ≤ ∑' β : J, ENNReal.ofReal (8 ^ d * l ^ 2) * volume (ball β.1.1 (r β.1)) :=
        ENNReal.tsum_le_tsum fun β => (hr β.1).2.2.2
    _ ≤ ∑' β : J, ENNReal.ofReal (8 ^ d * l ^ 2) *
          (A * (∫⁻ x in ball β.1.1 (r β.1) ∩ Sf, ‖f x‖ₑ ^ q) +
            B * ∫⁻ x in ball β.1.1 (r β.1) ∩ Sg, ‖g x‖ₑ ^ (2 : ℝ)) := by
        refine ENNReal.tsum_le_tsum fun β => ?_
        gcongr
        exact volume_ball_le_levelSets hK hq hl hfm hgm
          (hRH β.1.1 (r β.1) (hr β.1).1 (hsubR β.1.1 β.1.2.1 _ (hr β.1).2.1)) (hr β.1).2.2.1
    _ = ENNReal.ofReal (8 ^ d * l ^ 2) *
          (A * (∑' β : J, ∫⁻ x in ball β.1.1 (r β.1) ∩ Sf, ‖f x‖ₑ ^ q) +
            B * ∑' β : J, ∫⁻ x in ball β.1.1 (r β.1) ∩ Sg, ‖g x‖ₑ ^ (2 : ℝ)) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_mul_left,
          ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal (8 ^ d * l ^ 2) *
          (A * (∫⁻ x in ball 0 (τ * R) ∩ Sf, ‖f x‖ₑ ^ q) +
            B * ∫⁻ x in ball 0 (τ * R) ∩ Sg, ‖g x‖ₑ ^ (2 : ℝ)) := by
        gcongr
        · exact hsum Sf hSfm q f
        · exact hsum Sg hSgm 2 g

end QSH
