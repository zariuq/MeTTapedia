import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Terms
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax

/-!
# One curried application rule over the existing first-order row syntax

Judgments and function arrows use two supplied symbol tags. Application is the
existing binary row former, so a proof may itself occur in function position.
Other logical connectives remain ordinary data. No signature, term syntax or
unifier is replaced, and no public symbol spelling is chosen here.

The one rule reads a proof of an arrow and a proof of its domain, then makes
their application at its codomain. A logic's named inference rules can therefore
be typed schematic data. This module establishes the rule and its instances;
derivability and operational closure require their separate correspondences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationSyntax

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig args2 RowFunction)
open OneFrame (Terms)

def app (function argument : Tm) : Tm := .app .app (args2 function argument)
def symbol (tag : Nat) : Tm := .const (.sym tag)
def judgment (tag : Nat) (proof proposition : Tm) : Tm := app (app (symbol tag) proof) proposition
def arrow (tag : Nat) (domain codomain : Tm) : Tm := app (app (symbol tag) domain) codomain

@[simp] theorem vars_app (function argument : Tm) :
    (app function argument).freeVars = function.freeVars ∪ argument.freeVars := by
  ext name
  rw [Finset.mem_union]
  constructor
  · intro member
    rcases Presentation.Schematic.mem_vars_app_cases member with first | second
    · exact Or.inl first
    · exact Or.inr second
  · rintro (first | second)
    · exact Presentation.Schematic.mem_vars_head first
    · exact Presentation.Schematic.mem_vars_tail second

@[simp] theorem vars_symbol (tag : Nat) : (symbol tag).freeVars = ∅ := rfl

@[simp] theorem apply_app (assignment : Subst rowSig) (function argument : Tm) :
    assignment.applyTerm (app function argument) = app (assignment.applyTerm function) (assignment.applyTerm argument) := by
  change Term.app _ _ = Term.app _ _
  apply congrArg (Term.app (σ := rowSig) RowFunction.app)
  funext i
  fin_cases i <;> rfl

@[simp] theorem apply_symbol (assignment : Subst rowSig) (tag : Nat) :
    assignment.applyTerm (symbol tag) = symbol tag := rfl

@[simp] theorem apply_judgment (assignment : Subst rowSig) (tag : Nat) (proof proposition : Tm) :
    assignment.applyTerm (judgment tag proof proposition) =
      judgment tag (assignment.applyTerm proof) (assignment.applyTerm proposition) := by
  simp only [judgment, apply_app, apply_symbol]

@[simp] theorem apply_arrow (assignment : Subst rowSig) (tag : Nat) (domain codomain : Tm) :
    assignment.applyTerm (arrow tag domain codomain) =
      arrow tag (assignment.applyTerm domain) (assignment.applyTerm codomain) := by
  simp only [arrow, apply_app, apply_symbol]

def interpreter (judgmentTag arrowTag : Nat) : Rule (Terms Tm) :=
  ⟨PUnit.unit,
    ⟨[], [judgment judgmentTag (.var 0) (arrow arrowTag (.var 1) (.var 2)),
      judgment judgmentTag (.var 3) (.var 1)], [], [],
      [judgment judgmentTag (app (.var 0) (.var 3)) (.var 2)]⟩, []⟩

theorem interpreter_propagates (judgmentTag arrowTag : Nat) :
    SetStoreSyntax.Propagates (interpreter judgmentTag arrowTag) := by
  refine ⟨rfl, rfl, ⟨?_, rfl⟩, ?_, ?_⟩
  · intro check missing
    cases missing
  · simp only [interpreter, SetStoreSyntax.varsIn, judgment, arrow, vars_app, vars_symbol]
    decide +kernel
  · simp [interpreter, SetStoreSyntax.varsIn]

theorem interpreter_read_instance (judgmentTag arrowTag : Nat) (assignment : Subst rowSig) :
    (interpreter judgmentTag arrowTag).body.read.map assignment.applyTerm =
      [judgment judgmentTag (assignment 0) (arrow arrowTag (assignment 1) (assignment 2)),
        judgment judgmentTag (assignment 3) (assignment 1)] := by
  simp [interpreter, Subst.applyTerm]

theorem interpreter_produce_instance (judgmentTag arrowTag : Nat) (assignment : Subst rowSig) :
    (interpreter judgmentTag arrowTag).body.produce.map assignment.applyTerm =
      [judgment judgmentTag (app (assignment 0) (assignment 3)) (assignment 2)] := by
  simp [interpreter, Subst.applyTerm]

#print axioms interpreter_propagates
#print axioms interpreter_read_instance
#print axioms interpreter_produce_instance

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationSyntax
