import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ReadModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.FirstOrderEq

/-!
# Inconsistent prefix certificates prune whole join regions

A refuted equation core remains refuted under more equations and under one
consistent frame map applied to the whole core. This supplies a negative
join certificate beyond positive head retrieval. A failed universal guard,
timeout or incomplete solver result is not such a certificate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.ConflictCores

open Interface (Frames)

universe uO uT uH uE uOcc
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) {a : Obj}

def Refutes (equations : EquationStore (Tm a)) : Prop := ¬ X.Solvable equations

theorem refutes_extension (core full : EquationStore (Tm a))
    (included : ∀ equation ∈ core, equation ∈ full) (refuted : Refutes X core) : Refutes X full := by
  rintro ⟨future, point, solved⟩
  exact refuted ⟨future, point, fun equation member => solved equation (included equation member)⟩

theorem refutes_instantiation (core : EquationStore (Tm a)) (refuted : Refutes X core)
    {b : Obj} (opening : Hom a b) : Refutes X (X.applyStore opening core) := by
  rintro ⟨future, point, solved⟩
  exact refuted ⟨future, X.comp point opening,
    (Frames.models_applyStore opening point core).mp solved⟩

theorem actual_firing_refused {O : Type uOcc} [DecidableEq O]
    {E : Extensions.{uO, uH, uE} Hom} {P : Set (Rule Tm)} {source : State Tm O}
    (firing : Firing O E P source) (core : EquationStore (Tm (E.target firing.ext)))
    (included : ∀ equation ∈ core, equation ∈ firing.information X) (refuted : Refutes X core) :
    ¬ firing.Admits X := by
  intro admitted
  exact refutes_extension X core (firing.information X) included refuted admitted.2.2.1

open Mettapedia.Logic.LP

variable {signature : LPSignature} [DecidableEq signature.vars]
  [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]

theorem total_unifier_supplies_core (problem : EquationStore (Term signature))
    (refused : unifyTotal problem = none) :
    Refutes (OneFrame.frames (FirstOrder.action signature)) (a := PUnit.unit) problem := by
  rintro ⟨future, point, solved⟩
  cases future
  exact (FirstOrder.refused_iff_inconsistent problem).mp refused ⟨point, solved⟩

#print axioms refutes_extension
#print axioms refutes_instantiation
#print axioms actual_firing_refused
#print axioms total_unifier_supplies_core

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.ConflictCores
