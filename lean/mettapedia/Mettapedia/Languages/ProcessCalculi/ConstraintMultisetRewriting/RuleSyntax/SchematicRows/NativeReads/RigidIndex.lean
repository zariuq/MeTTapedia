import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.Enumeration
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderLicence

/-!
# Rigid first-order heads as a complete candidate filter

The carrier and substitutions are the existing finite LP terms. A function
symbol includes its declared arity. Unknown heads are retained, including
unknown stored rows when the query has a rigid head. The law allows different
substitutions on the two sides, so it applies to freshly opened schemas.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.RigidIndex

open Mettapedia.Logic.LP

variable {signature : LPSignature}

abbrev Key (signature : LPSignature) := Sum signature.constants signature.functionSymbols

def head : Term signature → Option (Key signature)
  | .var _ => none
  | .const value => some (.inl value)
  | .app symbol _ => some (.inr symbol)

theorem head_preserved (point : Subst signature) (term : Term signature)
    (key : Key signature) (known : head term = some key) :
    head (point.applyTerm term) = some key := by
  cases term <;> simp_all [head, Subst.applyTerm]

variable [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]

def permits (pattern row : Term signature) : Bool :=
  match head pattern, head row with
  | some first, some second => decide (first = second)
  | _, _ => true

theorem permits_of_equal_instances (pattern row : Term signature)
    (caller locals : Subst signature)
    (same : caller.applyTerm pattern = locals.applyTerm row) : permits pattern row = true := by
  cases hp : head pattern with
  | none => simp [permits, hp]
  | some first =>
      cases hr : head row with
      | none => simp [permits, hp, hr]
      | some second =>
          have keys := (head_preserved caller pattern first hp).symm.trans
            ((congrArg head same).trans (head_preserved locals row second hr))
          have equal : first = second := Option.some.inj keys
          simp [permits, hp, hr, equal]

theorem rejects_no_instances (pattern row : Term signature)
    (rejected : permits pattern row = false) :
    ¬ ∃ caller locals : Subst signature, caller.applyTerm pattern = locals.applyTerm row := by
  rintro ⟨caller, locals, matched⟩
  have accepted := permits_of_equal_instances pattern row caller locals matched
  rw [rejected] at accepted
  cases accepted

variable {Occurrence : Type}

theorem candidates_preserve_solutions (label : Occurrence → Term signature)
    (pattern : Term signature) (rows : List Occurrence)
    (resolve : Occurrence → List (Subst signature))
    (sound : ∀ occurrence point, point ∈ resolve occurrence →
      point.applyTerm pattern = point.applyTerm (label occurrence)) :
    (NativeReads.enumerate (fun occurrence => permits pattern (label occurrence)) rows).flatMap resolve =
      rows.flatMap resolve := by
  apply NativeReads.enumerate_resolver_word
  intro occurrence _ nonempty
  obtain ⟨point, member⟩ := List.exists_mem_of_ne_nil _ nonempty
  exact permits_of_equal_instances pattern (label occurrence) point point (sound occurrence point member)

#print axioms head_preserved
#print axioms permits_of_equal_instances
#print axioms rejects_no_instances
#print axioms candidates_preserve_solutions

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.RigidIndex
