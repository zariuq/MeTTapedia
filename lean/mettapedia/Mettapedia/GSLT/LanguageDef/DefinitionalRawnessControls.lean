import Mettapedia.GSLT.LanguageDef.DefinitionalAdmission

/-!
# First-order definition metadata controls

Binding metadata does not change the rawness of a binder-free schema. The
existing row recognizer and definitional contract retain those equations.
A binder-bearing schema belongs to the declared-equation route instead.
-/

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.DefinitionalRawnessControls
open Mettapedia.OSLF.MeTTaIL.Syntax
open DefinitionalEquations EquationSemantics SortedFirstOrderRules

def row : Row := ⟨"Identity",["x"],.fvar "x"⟩
def equation (specification : RuleBindingSpec) : Equation :=
  ⟨"identity",[],[],.apply "Identity" [.fvar "x"],.fvar "x",some specification⟩

theorem defines (specification : RuleBindingSpec) : Defines (equation specification) row :=
  ⟨rfl,rfl,rfl⟩

theorem formed : row.WellFormed :=
  ⟨by decide, .metavariable (by simp [row])⟩

theorem metadata_is_readable (specification : RuleBindingSpec) : readsRaw (equation specification) = true :=
  readsRaw_of_defines (defines specification) formed

theorem metadata_row_recognized (specification : RuleBindingSpec) : rowOf? (equation specification) = some row :=
  rowOf?_complete (defines specification)

def explicitSpecification : RuleBindingSpec := ⟨[("x",[])],[]⟩

theorem explicit_metadata_is_readable : readsRaw (equation explicitSpecification) = true :=
  readsRaw_of_defines (defines explicitSpecification) formed

theorem explicit_metadata_row_recognized : rowOf? (equation explicitSpecification) = some row :=
  rowOf?_complete (defines explicitSpecification)

def binderEquation (specification : RuleBindingSpec) : Equation :=
  ⟨"binder",[],[],.lambda "x" (.fvar "body"),.fvar "body",some specification⟩

theorem binder_requires_declared_route (specification : RuleBindingSpec) :
    readsRaw (binderEquation specification) = false := rfl

theorem binder_row_refused (specification : RuleBindingSpec) :
    rowOf? (binderEquation specification) = none := rfl

#print axioms metadata_is_readable
#print axioms metadata_row_recognized
#print axioms binder_requires_declared_route
end Mettapedia.GSLT.LanguageDef.DefinitionalRawnessControls
