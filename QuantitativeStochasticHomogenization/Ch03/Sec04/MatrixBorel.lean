import QuantitativeStochasticHomogenization.Front.Notation
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Independence.Basic

/-!
# Coefficient pairs and their translation law

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Environment/Basic.lean`.

Vectors use coordinate functions. All geometric bounds below use the explicitly
defined Euclidean norm, including the operator norm bound for matrix differences.
-/

open MeasureTheory

open scoped BigOperators Matrix

namespace QSH

instance (d : ℕ) : MeasurableSpace (Mat d) := borel (Mat d)

instance (d : ℕ) : BorelSpace (Mat d) := ⟨rfl⟩

end QSH
