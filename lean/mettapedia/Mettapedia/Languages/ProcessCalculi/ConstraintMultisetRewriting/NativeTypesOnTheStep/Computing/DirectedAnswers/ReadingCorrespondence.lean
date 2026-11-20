import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DirectedAnswers.Rows
import Mettapedia.GSLT.Core.OperationalReadback
import Mettapedia.GSLT.Meredith.GSLT

/-!
# The rows and their compiled reading, as a correspondence between two systems

The two systems are the closed terms of the extended package under its directed reduction, and the
closed terms of the package under its own (`directedSystem`). The relation between a term `t` of the
first and a term `u` of the second is: **the reading of `t` at the compiled terms is convertible, in the
package, with `u`**. Under the hypotheses of `Definitions.conv_reading` (a checked development whose
rules, read at the bodies, all join) this relation is an operational correspondence in the sense of
`GSLT.Core.OperationalReadback` (`readingCorrespondence`), so it composes with every other one.

**Its kind.** Every firing, of either system, is silent for the relation: a step of the package keeps
its term convertible with the reading, and a step of the rows reads as a conversion of the package, by
`conv_reading`. No firing of one side is matched by a firing of the other. A row fires once where the
compiled term takes several steps, and the right side of a row reads as an expansion of what the
compiled term reduces to, so neither a firing-for-firing statement nor one with positive blocks is
available; what the correspondence carries is the invariant. Being a correspondence says little by
itself: every relation that the steps of both systems keep is one, with every step silent, the empty
relation included. The content is the relation named here and what it preserves.

**What it preserves, from the rows to the package** (`value_preserved`; instance
`addAppend_value_preserved`): a value that the rows reach from `t` is reached by the package from every
related `u`. Nothing is asked of `u`: the invariant makes `u` convertible with the value, and a closed
term of the package convertible with a value reduces to it (`pkg_answer_of_conv`). **What it reflects,
from the package to the rows**, is proved for the ground calls of a recursive constant
(`recursive_call_answer`, `rows_reach`) and not for every related pair. Divergence is neither preserved
nor reflected by anything here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.DirectedAnswers

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open AlgebraicSchema (SchemaTable)
open ConstantExpansion (expand Bodies)
open TowerVectorsModel (zeroC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg)
open ProgrammingOnTheStep.IndexedFamilies.ClosedCalls (one)
open Definitions (Development devCheck devRules devPackage)
open Mettapedia.GSLT (GSLT)
open Mettapedia.GSLT.IndexedOperational (OperationalCorrespondence)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)

/-- **The closed terms of a package under its directed reduction**, as a system of the general theory:
terms up to syntactic equality, one transition for one directed step. -/
abbrev directedSystem (R : Rules Tower.Head) : GSLT := equalityGSLT (Tower.Tm 0) (StrongNormalization.Reduces R)

/-- Finite executions of the system are finite directed reductions. -/
theorem multiStep_iff (R : Rules Tower.Head) {t u : Tower.Tm 0} :
    (directedSystem R).MultiStep t u ↔ StrongNormalization.ReducesStar R t u :=
  Mettapedia.GSLT.Meredith.multiStep_iff_reflTransGen (directedSystem R) t u

section Reading

variable {dev : Development} (ok : devCheck dev = true) {rows : SchemaTable Tower.Head}
  (found : devRules dev = some rows) {bodies : Bodies Tower.Head}
  (others : ∀ d, (∀ e ∈ dev, e.1 ≠ d) → bodies d = .const d) {fuel : Nat}
  (read : Definitions.rulesRead fuel bodies rows = true)

/-- **The reading, as an operational correspondence** from the rows' system to the package's. A term of
the extension is related to a term of the package when its reading is convertible with it in the
package. Every transition of either system is silent for the relation. -/
def readingCorrespondence :
    OperationalCorrespondence (directedSystem (devPackage dev rows)) (directedSystem pkg) where
  related t u := Conv pkg.headEq (expand bodies t) u pkg.computation
  readStep := by
    intro origin current next related step
    have step' : StrongNormalization.Reduces pkg current next := step
    exact .inl (.trans _ _ _ related (.rel _ _ (step_of_reduces step')))
  forward := by
    intro origin after current related step
    have step' : StrongNormalization.Reduces (devPackage dev rows) origin after := step
    exact ⟨current, ⟨.refl current⟩, .trans _ _ _
      (.symm _ _ (Definitions.conv_reading ok found others read (.rel _ _ (step_of_reduces step')))) related⟩

/-- Every term is related to its own reading. -/
theorem related_reading (t : Tower.Tm 0) :
    (readingCorrespondence ok found others read).related t (expand bodies t) :=
  .refl _

/-- **What the correspondence preserves, from the rows to the package**: a value the rows reach from a
term is reached by the package from every related term. The rows' reading answers the value
(`value_of_reading`), so a related term is convertible with it and reduces to it. -/
theorem value_preserved {t u v : Tower.Tm 0}
    (related : (readingCorrespondence ok found others read).related t u) (value : Value v)
    (steps : (directedSystem (devPackage dev rows)).MultiStep t v) :
    (directedSystem pkg).MultiStep u v := by
  have related' : Conv pkg.headEq (expand bodies t) u pkg.computation := related
  have reached := value_of_reading ok found others read value ((multiStep_iff _).mp steps)
  have conversion : Conv pkg.headEq u v pkg.computation := .trans _ _ _ (.symm _ _ related') reached.conv
  exact (multiStep_iff pkg).mpr (pkg_answer_of_conv conversion value).1

end Reading

/-- **The correspondence for addition and append by rows**, read at their compiled terms. -/
def addAppendCorrespondence :
    OperationalCorrespondence (directedSystem addAppendExt) (directedSystem pkg) :=
  readingCorrespondence Definitions.addAppend_devCheck Definitions.addAppend_rules
    Definitions.addAppend_others Definitions.addAppend_read

/-- **Instance of what the correspondence preserves**: the rows take `add 1 0` to `1`, and the compiled
addition at `1` and `0` is related to that call; so the package takes it to `1`. -/
theorem addAppend_value_preserved :
    addAppendCorrespondence.related
        (Definitions.spine (.const Definitions.addName) [one, zeroC])
        (Definitions.spine Definitions.addTerm [one, zeroC]) ∧
      (directedSystem addAppendExt).MultiStep
        (Definitions.spine (.const Definitions.addName) [one, zeroC]) one ∧
      (directedSystem pkg).MultiStep (Definitions.spine Definitions.addTerm [one, zeroC]) one := by
  have steps := add_value_of_reading.1
  have reading : expand Definitions.addAppendReading
      (Definitions.spine (.const Definitions.addName) [one, zeroC] : Tower.Tm 0) =
      Definitions.spine Definitions.addTerm [one, zeroC] := by decide +kernel
  have related : addAppendCorrespondence.related
      (Definitions.spine (.const Definitions.addName) [one, zeroC])
      (Definitions.spine Definitions.addTerm [one, zeroC]) := by
    show Conv pkg.headEq (expand Definitions.addAppendReading
      (Definitions.spine (.const Definitions.addName) [one, zeroC] : Tower.Tm 0))
      (Definitions.spine Definitions.addTerm [one, zeroC]) pkg.computation
    rw [reading]
    exact .refl _
  exact ⟨related, (multiStep_iff addAppendExt).mpr steps,
    value_preserved Definitions.addAppend_devCheck Definitions.addAppend_rules Definitions.addAppend_others
      Definitions.addAppend_read related (.succ .zero) ((multiStep_iff addAppendExt).mpr steps)⟩

end NativeTypesOnTheStep.Computing.DirectedAnswers

section Audit
open NativeTypesOnTheStep.Computing.DirectedAnswers
#print axioms readingCorrespondence
#print axioms related_reading
#print axioms value_preserved
#print axioms addAppendCorrespondence
#print axioms addAppend_value_preserved
end Audit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
