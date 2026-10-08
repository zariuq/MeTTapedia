import Mettapedia.Logic.HOL.DefinitionHistoryProofConservativity
import Mettapedia.Logic.HOL.Soundness
import Mettapedia.TypeTheory.MaterialSets.Hypersets.AntiFoundation

/-!
# Definitions and retained proofs over actual cyclic material values

The base carrier is the existing hyperset quotient, not a finite surrogate.
A first definition names its Quine atom; a second asks for self-membership
through the first alias. Their Henkin models are constructed from the actual
material carrier and the bodies. Old false statements remain false.

Constant expansion can make two assumptions the same formula while keeping
their hypothesis occurrences distinct. This is fixed-simple-type semantics;
it neither selects a native foundation nor admits additional set axioms.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.MaterialDefinitionHistoryControls

open Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.MaterialSets.Hypersets

abbrev setType : Ty Unit := .base ()

inductive MaterialConst : Ty Unit → Type where
  | member : MaterialConst (setType ⇒ setType ⇒ .prop)
  | empty : MaterialConst setType
  | loop : MaterialConst setType

def materialModel : HenkinModel.{0, 0, 0} Unit MaterialConst :=
  HenkinModel.standard (fun _ => HSet.{0})
    (fun {_} constant => match constant with
      | .member => fun (left right : HSet.{0}) => ULift.up (left ∈ right)
      | .empty => (∅ : HSet.{0})
      | .loop => HSet.quineAtom)

abbrev First := DefinedConst MaterialConst setType
abbrev Second := DefinedConst First .prop

def loopAlias : DefinitionHistory MaterialConst First :=
  .add .nil setType (.const .loop)

def membershipBody : ClosedTerm First .prop :=
  .app (.app (.const (.old .member)) (.const .defined)) (.const .defined)

def history : DefinitionHistory MaterialConst Second :=
  .add loopAlias .prop membershipBody

def query : ClosedFormula Second := .const .defined

def sourceQuery : ClosedFormula MaterialConst :=
  .app (.app (.const .member) (.const .loop)) (.const .loop)

theorem query_expansion : history.erase query = sourceQuery := rfl

theorem query_holds : (history.extendModel materialModel).models query := by
  rw [history.models_erasure materialModel query, query_expansion]
  exact HSet.quineAtom_mem_self

def falseOldClaim : ClosedFormula MaterialConst :=
  .app (.app (.const .member) (.const .empty)) (.const .empty)

theorem false_old_claim_remains_false :
    ¬ (history.extendModel materialModel).models (history.embed falseOldClaim) := by
  rw [history.models_embed materialModel falseOldClaim]
  exact HSet.notMem_empty _

def noSelfMembership : ClosedFormula MaterialConst :=
  .all (.not (.app (.app (.const .member) (.var .vz)) (.var .vz)))

/-- Definitions do not conceal the cyclic obstruction to Foundation. -/
theorem no_self_membership_remains_false :
    ¬ (history.extendModel materialModel).models (history.embed noSelfMembership) := by
  rw [history.models_embed materialModel noSelfMembership]
  intro impossible
  exact impossible HSet.quineAtom trivial HSet.quineAtom_mem_self

/-- Two source formulas differ syntactically and expand to the same query. -/
def originalFormula : ClosedFormula Second := history.embed sourceQuery

theorem original_formula_ne_query : originalFormula ≠ query := by
  intro same
  cases same

theorem formulas_expand_together : history.erase query = history.erase originalFormula := by
  rw [query_expansion, originalFormula, history.erase_embed]

theorem erasure_not_injective :
    ¬ Function.Injective (fun formula : ClosedFormula Second => history.erase formula) := by
  intro injective
  exact original_formula_ne_query (injective formulas_expand_together.symm)

def firstUse : ProofSyntax Second [query, originalFormula] query := .hyp ⟨0, by decide⟩
def secondUse : ProofSyntax Second [query, originalFormula] originalFormula := .hyp ⟨1, by decide⟩

theorem first_position_preserved :
    (history.eraseProof firstUse).rootObservation = ⟨.hyp, some 0⟩ :=
  ProofSyntax.substConst_rootObservation history.images firstUse

theorem second_position_preserved :
    (history.eraseProof secondUse).rootObservation = ⟨.hyp, some 1⟩ :=
  ProofSyntax.substConst_rootObservation history.images secondUse

theorem erased_evidence_still_distinct :
    (history.eraseProof firstUse).rootObservation ≠ (history.eraseProof secondUse).rootObservation := by
  rw [first_position_preserved, second_position_preserved]
  decide

def sharedProof : ProofSyntax Second [query, originalFormula] (.and query originalFormula) :=
  .andI firstUse secondUse

theorem shared_rule_tree_preserved :
    ProofSyntax.ruleTree (history.eraseProof sharedProof).observe =
      ProofSyntax.ruleTree sharedProof.observe :=
  history.eraseProof_ruleTree sharedProof

/-- A supplied β receipt with a newly named proposition is preserved. -/
def betaReceipt : ProofSyntax Second [] (.eq (.app (.lam (.var .vz)) query) query) :=
  .beta query (.var .vz)

theorem beta_receipt_preserved :
    (history.eraseProof betaReceipt).rootObservation = ⟨.beta, none⟩ :=
  ProofSyntax.substConst_rootObservation history.images betaReceipt

def memberTerm : ClosedTerm Second (setType ⇒ setType ⇒ .prop) := .const (.old (.old .member))

def etaReceipt : ProofSyntax Second []
    (.eq (.lam (.app (weaken (σ := setType) memberTerm) (.var .vz))) memberTerm) :=
  .eta memberTerm

theorem eta_receipt_preserved :
    (history.eraseProof etaReceipt).rootObservation = ⟨.eta, none⟩ :=
  ProofSyntax.substConst_rootObservation history.images etaReceipt

/-- The newest defining equation is a usable assumption, then an actual
closed proof after the equation assumptions have been discharged. -/
def newestEquation : ClosedFormula Second := .eq query (DefinedConst.embed membershipBody)

def newestEquationUse : ProofSyntax Second (history.equationsIn []) newestEquation :=
  ProofSyntax.hyp (Const := Second) (Δ := history.equationsIn []) ⟨0, by decide⟩

def newestEquationDischarged : ProofSyntax MaterialConst [] (history.erase newestEquation) :=
  history.dischargeEquations (assumptions := []) newestEquationUse

theorem newest_equation_has_source_proof :
    ExtDerivation MaterialConst [] (history.erase newestEquation) :=
  newestEquationDischarged.erase

theorem equation_discharge_changes_observation :
    newestEquationUse.rootObservation = ⟨.hyp, some 0⟩ ∧
      newestEquationDischarged.rootObservation = ⟨.eqRefl, none⟩ := ⟨rfl, rfl⟩

theorem equation_control_has_equal_counts :
    newestEquationUse.nodeCount = 1 ∧ newestEquationDischarged.nodeCount = 1 := ⟨rfl, rfl⟩

def assumedTruth : ProofSyntax MaterialConst [(.top : ClosedFormula MaterialConst)] .top :=
  .hyp ⟨0, by decide⟩

def branchingTruth : ProofSyntax MaterialConst [] (.top : ClosedFormula MaterialConst) :=
  .andEL (.andI .topI .topI)

def truthSubstitution :
    ProofSyntax.HypothesisSubstitution [(.top : ClosedFormula MaterialConst)] [] :=
  Fin.cases branchingTruth (fun occurrence => Fin.elim0 occurrence)

/-- Arbitrary supplied proofs can grow the tree, unlike its reflexivity leaves. -/
theorem supplied_proof_can_grow_tree :
    assumedTruth.nodeCount = 1 ∧
      (ProofSyntax.substituteHypotheses truthSubstitution assumedTruth).nodeCount = 4 := ⟨rfl, rfl⟩

/-- Even with all the new definition equations available, the old false
membership claim still has no retained HOL proof. -/
theorem false_old_claim_has_no_proof :
    ¬ Nonempty (ProofSyntax Second (history.equationsIn []) (history.embed falseOldClaim)) := by
  rintro ⟨proof⟩
  have oldProof := history.oldProof (assumptions := []) proof
  have valid := Soundness.extTheorem_sound oldProof.erase materialModel
    (materialModel.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
  exact HSet.notMem_empty _ valid

end Mettapedia.SetTheory.Profiles.MaterialDefinitionHistoryControls
