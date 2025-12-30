import Mettapedia.ProbabilityTheory.Hypercube.Basic
import Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Counterexamples.SemidirectNoSeparation

namespace Mettapedia.ProbabilityTheory.Hypercube

open Mettapedia.ProbabilityTheory.KnuthSkilling
open Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Counterexamples

/-- The “central question” as stated in `Hypercube.Basic` is false: the `SemidirectNoSeparation`
counterexample provides a noncommutative ordered monoid satisfying all listed hypotheses. -/
theorem not_centralQuestion : ¬ centralQuestion.{0} := by
  intro h
  have hcomm :
      ∀ x y : SD, SD.op x y = SD.op y x :=
    h (α := SD) (op := SD.op) (ident := SD.ident) (by intro x y z; simpa using SD.op_assoc x y z)
      (by intro x; simpa using SD.op_ident_right x) (by intro x; simpa using SD.op_ident_left x)
      (by intro y; simpa using SD.op_strictMono_left y) (by intro x; simpa using SD.op_strictMono_right x)
      (by intro x y hx; simpa using SD.op_archimedean x y hx) (by intro x; simpa using SD.ident_le x)
  have hcomm' :
      KnuthSkillingAlgebra.op SD.exX SD.exY = KnuthSkillingAlgebra.op SD.exY SD.exX := by
    simpa [KnuthSkillingAlgebra.op] using hcomm SD.exX SD.exY
  exact SD.op_not_comm hcomm'

end Mettapedia.ProbabilityTheory.Hypercube
