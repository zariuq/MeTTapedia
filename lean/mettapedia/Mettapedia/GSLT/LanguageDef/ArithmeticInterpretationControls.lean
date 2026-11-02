import Mettapedia.GSLT.LanguageDef.ArithmeticReadingInterpretation
import Mettapedia.Logic.HOL.ConstructorGuardInterpretation
import Mettapedia.Logic.HOL.Syntax.DecidableEq

/-!
# Compound-carrier and binding controls for constructor interpretation

The target alphabet is empty. Both source sorts map to the same compound
function type, and zero is a compound beta redex. These are syntax controls;
the chosen operations are not presented as a natural-number model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.ArithmeticInterpretationControls
open Mettapedia.Logic
open HOL HOL.FiniteConstructorEncoding
open IndexedInductiveHOLTerms

abbrev TargetConst (_ : Ty Unit) := Empty
abbrev field : Ty Unit := .prop ⇒ .prop

def arithmetic : Arithmetic TargetConst where
  number := field
  element := field
  zero := .app (.lam (.var .vz)) (.lam (.var .vz))
  successor := .lam (.var .vz)
  addition := .lam (.lam (.var (.vs .vz)))

def changed : Arithmetic TargetConst := { arithmetic with zero := .lam .bot }
abbrev interpretation := ArithmeticReadingInterpretation.interpretation arithmetic
abbrev source := ArithmeticReadingInterpretation.sourceArithmetic
abbrev SourceConst := ArithmeticReadingInterpretation.SourceConst
abbrev SourceBase := ArithmeticReadingInterpretation.SourceBase

theorem sorts_collapse :
    Ty.substitute interpretation.types Controls.number = field ∧
      Ty.substitute interpretation.types Controls.element = field := ⟨rfl, rfl⟩

theorem positions_survive :
    interpretation.term (.var (.vz : Var [Controls.number, Controls.element] Controls.number)) ≠
      interpretation.term (.var (.vs (.vz : Var [Controls.element] Controls.element))) := by decide

theorem changed_zero_refused : interpretation.term source.zero ≠ changed.zero := by
  rw [ArithmeticReadingInterpretation.zero_image]
  decide

def sourceBody : Term SourceConst [Controls.number] (Controls.element ⇒ Controls.number) :=
  .lam (.var (.vs .vz))

theorem substitution_under_binder :
    interpretation.term (instantiate source.zero sourceBody) =
      instantiate (interpretation.term source.zero) (interpretation.term sourceBody) :=
  TermInterpretation.term_instantiate interpretation source.zero sourceBody

theorem capture_refused : interpretation.term (instantiate source.zero sourceBody) ≠
    (.lam (.var .vz) : ClosedTerm TargetConst (field ⇒ field)) := by decide

def signature : List (List (Ty Unit)) := [[field, field]]
def originalArguments : Arguments TargetConst [field, field] [field, field] :=
  (.var (.vs .vz), .var .vz, PUnit.unit)
def reversedArguments : Arguments TargetConst [field, field] [field, field] :=
  (.var .vz, .var (.vs .vz), PUnit.unit)
def duplicatedArguments : Arguments TargetConst [field, field] [field, field] :=
  (.var .vz, .var .vz, PUnit.unit)

theorem field_order_retained :
    encode signature ⟨0, by decide⟩ originalArguments ≠
      encode signature ⟨0, by decide⟩ reversedArguments := by decide

theorem duplicate_relationship_retained :
    encode signature ⟨0, by decide⟩ originalArguments ≠
      encode signature ⟨0, by decide⟩ duplicatedArguments := by decide

theorem constructor_ordinal_retained :
    (encode [[], []] ⟨0, by decide⟩ PUnit.unit : ClosedTerm TargetConst _) ≠
      encode [[], []] ⟨1, by decide⟩ PUnit.unit := by decide

def sourceSignature : List (List (Ty SourceBase)) := [[Controls.number]]
def sourceConditions : ConstructorDataPredicates.Conditions SourceConst [] sourceSignature :=
  Fin.cases (.lam .bot) (fun impossible => nomatch impossible)
def targetConditions : ConstructorDataPredicates.Conditions TargetConst [] [[field]] :=
  Fin.cases (.lam .bot) (fun impossible => nomatch impossible)
def fullConditions : ConstructorDataPredicates.Conditions TargetConst [] [[field]] :=
  Fin.cases (.lam .top) (fun impossible => nomatch impossible)
def sourcePayload := encode sourceSignature ⟨0, by decide⟩ (source.zero, PUnit.unit)
def targetPayload : ClosedTerm TargetConst (payloadType [[field]]) :=
  encode [[field]] ⟨0, by decide⟩ (arithmetic.zero, PUnit.unit)

theorem restrictive_guard_translates :
    interpretation.term (ConstructorDataPredicates.guard sourceSignature sourceConditions sourcePayload) =
      ConstructorDataPredicates.guard [[field]] targetConditions targetPayload := by
  apply guard_interpret
  · intro selected
    refine Fin.cases ?_ (fun impossible => nomatch impossible) selected
    rfl
  · exact encode_interpret interpretation sourceSignature ⟨0, by decide⟩ (source.zero, PUnit.unit)

theorem restrictive_guard_not_erased :
    ConstructorDataPredicates.guard [[field]] targetConditions targetPayload ≠
      ConstructorDataPredicates.guard [[field]] fullConditions targetPayload := by decide

theorem empty_inventory_refused :
    (ConstructorDataPredicates.guard [] (fun impossible => nomatch impossible) .top : ClosedFormula TargetConst) ≠
      .top := by decide

#print axioms positions_survive
#print axioms substitution_under_binder
#print axioms field_order_retained
#print axioms restrictive_guard_translates
#print axioms empty_inventory_refused
end Mettapedia.GSLT.LanguageDef.ArithmeticInterpretationControls
