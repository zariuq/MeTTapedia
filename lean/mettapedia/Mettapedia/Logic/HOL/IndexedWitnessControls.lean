import Mettapedia.Logic.HOL.IndexedWitnessProofs
import Mettapedia.Logic.HOL.FiniteConstructorEncodingControls
import Mettapedia.Logic.HOL.Soundness

/-!
# Witness preservation and index-selection controls

The positive proof retains a proposition-valued index. Its motive holds at
the witnessed true index and fails at the false index. A second relation
admits both indices, separating existence from functionality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedWitnessControls

open FiniteConstructorEncoding.Controls
open CurriedGuardProgramProofs IndexedWitnessProofs

def family : ClosedTerm Constants (.prop ⇒ .prop) := .lam .top
def root : ClosedTerm Constants (.prop ⇒ .prop ⇒ .prop) := .lam (.lam (.var .vz))
def point : ClosedFormula Constants := .top
def evidence : Formula Constants [.prop] := .top

def member : ProofSyntax Constants [] (.app family point) :=
  .impE (.eqPropER (.beta point .top)) .topI

def lifted : ProofSyntax Constants [] (.app (IndexedPredicateInduction.lift root root) point) :=
  .impE (.eqPropER (IndexedPredicateInduction.lift_beta root root point)) (.allI (.impI (.hyp 0)))

def rootAtTrue : ProofSyntax Constants [] (.app (.app root point) .top) :=
  .impE (.eqPropER (beta2 (.var .vz) point .top)) .topI

def witness : ProofSyntax Constants [] (rootWitness root point evidence) := by
  apply ProofSyntax.exI (.top : ClosedFormula Constants)
  exact .andI .topI rootAtTrue

def retained : ProofSyntax Constants [] (indexedWitness family root root point evidence) :=
  consume family root root point evidence member lifted witness

theorem retained_free : retained.FunctionExtensionalityFree := by
  apply consume_free
  · trivial
  · exact ⟨IndexedPredicateInduction.lift_beta_free _ _ _, trivial⟩
  · exact ⟨trivial, beta2_free _ _ _, trivial⟩

def wrongIndex : ClosedFormula Constants := .app (.app root point) .bot

theorem wrong_index_not_derivable : ¬ Nonempty (ProofSyntax Constants [] wrongIndex) := by
  rintro ⟨proof⟩
  have falseResult := Soundness.extTheorem_sound proof.erase model
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
  change False at falseResult
  exact falseResult

def allRoot : ClosedTerm Constants (.prop ⇒ .prop ⇒ .prop) := .lam (.lam .top)

def anyIndex (index : ClosedFormula Constants) :
    ProofSyntax Constants [] (rootWitness allRoot point evidence) := by
  apply ProofSyntax.exI index
  exact .andI .topI (.impE (.eqPropER (beta2 .top point index)) .topI)

theorem relation_has_two_distinct_indices :
    (model.denote (.app (.app allRoot point) .top) values).down ∧
    (model.denote (.app (.app allRoot point) .bot) values).down ∧
    ¬ model.Eqv .prop (model.denote (.top : ClosedFormula Constants) values)
      (model.denote (.bot : ClosedFormula Constants) values) := by
  refine ⟨True.intro, True.intro, ?_⟩
  change ¬ (True ↔ False)
  exact fun same => same.mp True.intro

#print axioms retained_free
#print axioms wrong_index_not_derivable
#print axioms relation_has_two_distinct_indices

end Mettapedia.Logic.HOL.IndexedWitnessControls
