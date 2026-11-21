import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.BallPoincareEstimate
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel
import QuantitativeStochasticHomogenization.Ch03.Sec04.EuclideanNormToLp
import QuantitativeStochasticHomogenization.Ch03.Sec04.CoordinateNormBound

/-!
# Spatial Ball Volume

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Correctors/SpatialBallVolume.lean`.

Euclidean ball volumes used in the spatial potential construction. -/

open MeasureTheory

namespace QSH

open Set

/-- All positive Euclidean balls have positive finite coordinate volume.
-/
theorem ball_volume_pos_finite (d : ℕ) (R : ℝ) (hR : 0 < R) :
    0 < volume.real (ball (0 : Vec d) R) := by
  have hU : IsOpen (ball (0 : Vec d) R) := by
    unfold ball euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const
  have hne : (ball (0 : Vec d) R).Nonempty := by
    refine ⟨0, ?_⟩
    simp [ball, euclideanNorm, euclideanSq, dot, hR]
  have hfin : volume (ball (0 : Vec d) R) ≠ ⊤ := by
    have h_sub : ball (0 : Vec d) R ⊆ Metric.closedBall (0 : Vec d) R := by
      intro y hy
      have hy' : euclideanNorm y < R := by
        simpa [ball, sub_zero] using hy
      rw [Metric.mem_closedBall, dist_pi_le_iff hR.le]
      intro j
      rw [Real.dist_eq]
      simp
      have hj := coordinate_abs_le_euclideanNorm y j
      exact hj.trans hy'.le
    have h_closedBall_fin : volume (Metric.closedBall (0 : Vec d) R) ≠ ⊤ := by
      rw [Real.volume_pi_closedBall _ hR.le]
      exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top h_closedBall_fin (measure_mono h_sub)
  exact ENNReal.toReal_pos (hU.measure_pos volume hne).ne' hfin

end QSH
