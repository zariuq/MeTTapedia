import Mettapedia.GSLT.LanguageDef.CompiledPlanAdmission

/-!
# Exact term semantics for admitted compiled plans

`CompiledPlanAdmission.Term` is the typed semantic carrier reconstructed from
physical `CGP1` nodes.  This module gives it a vocabulary-independent
instantiation semantics.  It is the common observation boundary for generated
matching, positional heads, immutable-subterm caching, and later frame
specializations.
-/

namespace Mettapedia.GSLT.LanguageDef.CompiledPlanTermSemantics

open CompiledPlanAdmission

mutual

/-- Closed value produced by instantiating an admitted compiled-plan term. -/
inductive GroundTerm where
  | symbol (name : List UInt8)
  | string (value : List UInt8)
  | integer (value : Int64)
  | application (head : List UInt8) (arguments : GroundTerms)
  deriving DecidableEq, Repr

inductive GroundTerms where
  | nil
  | cons (head : GroundTerm) (tail : GroundTerms)
  deriving DecidableEq, Repr

end

def GroundTerms.ofList : List GroundTerm -> GroundTerms
  | [] => .nil
  | head :: tail => .cons head (ofList tail)

/-- Dense slot environment at the exact typed-plan boundary. -/
abbrev Substitution := UInt32 -> Option GroundTerm

mutual

/-- Instantiate one typed plan term.  An unassigned dense slot fails closed. -/
def instantiateTerm (substitution : Substitution) : Term -> Option GroundTerm
  | .symbol name => some (.symbol name)
  | .variable slot => substitution slot
  | .string value => some (.string value)
  | .integer value => some (.integer value)
  | .application head arguments => do
      let grounded <- instantiateTerms substitution arguments
      some (.application head grounded)

def instantiateTerms (substitution : Substitution) :
    Terms -> Option GroundTerms
  | .nil => some .nil
  | .cons head tail => do
      let groundedHead <- instantiateTerm substitution head
      let groundedTail <- instantiateTerms substitution tail
      some (.cons groundedHead groundedTail)

end

/-- Empty dense environment used at rejecting-boundary canaries. -/
def emptySubstitution : Substitution := fun _ => none

/-- Extend one dense slot without changing any other observation. -/
def write (substitution : Substitution) (slot : UInt32)
    (value : GroundTerm) : Substitution :=
  fun candidate => if candidate = slot then some value else substitution candidate

theorem write_same (substitution : Substitution) (slot : UInt32)
    (value : GroundTerm) :
    write substitution slot value slot = some value := by
  simp [write]

theorem write_other (substitution : Substitution)
    {written candidate : UInt32} (different : candidate ≠ written)
    (value : GroundTerm) :
    write substitution written value candidate = substitution candidate := by
  simp [write, different]

/-! ## Independent semantic canaries -/

private def twoSlots : Substitution
  | 0 => some (.symbol [10])
  | 1 => some (.integer 42)
  | _ => none

/-- Symbols, strings, integers, applications, and dense variables remain
distinct at the common observation boundary. -/
example :
    instantiateTerm twoSlots
      (.application [1]
        (.cons (.variable 0)
          (.cons (.string [2])
            (.cons (.variable 1) .nil)))) =
      some (.application [1]
        (.cons (.symbol [10])
          (.cons (.string [2])
            (.cons (.integer 42) .nil)))) := by
  decide

/-- An unresolved slot rejects the instantiation. -/
example : instantiateTerm emptySubstitution (.variable 9) = none := by
  rfl

end Mettapedia.GSLT.LanguageDef.CompiledPlanTermSemantics
