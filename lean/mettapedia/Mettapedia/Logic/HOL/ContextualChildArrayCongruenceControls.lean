import Mettapedia.Logic.HOL.ContextualChildArrayCongruence
import Mettapedia.Logic.HOL.FiniteConstructorEncodingControls

/-!
# Pointwise child-contract controls with active and inactive slots

The propositional slot model has a nonconstant identity array. Active slots
require both an edge equation and predicate membership; inactive slots require
bottom padding. A beta-only pointwise proof transports the original contract
to a syntactically different eta-expanded array without deriving function
equality. The original contract premise is independently realized. Constant
true and false arrays respectively violate padding and active obligations.
This is a child-contract model, not a natural-number or datatype model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.ContextualChildArrayCongruenceControls
open FiniteConstructorEncoding.Controls (Constants model)
open RecursiveSpacePredicate

abbrev context : Ctx Empty := [.prop ⇒ .prop]
def signature : Contextual Constants context where
  number := .prop
  payload := .prop
  space := .prop
  bottom := .bot
  construct := .lam (.lam (.lam (.or (.app (.var .vz) (.var (.vs (.vs .vz)))) (.var (.vs .vz)))))
  validShape := .lam (.lam .top)
  active := .lam (.lam (.var .vz))
  validEdge := .lam (.lam (.lam (.eq (.var (.vs .vz)) (.var .vz))))

def predicate : Term Constants context (.prop ⇒ .prop) := .lam (.var .vz)
def payload : Formula Constants context := .bot
def first : Term Constants context (.prop ⇒ .prop) := .var .vz
def second : Term Constants context (.prop ⇒ .prop) := .lam (.app (weaken first) (.var .vz))
def original : Formula Constants context := signature.childConditions predicate payload first
def target : Formula Constants context := signature.childConditions predicate payload second

def pointwise : ProofSyntax Constants [original]
    (.all (.eq (.app (weaken first) (.var .vz)) (.app (weaken second) (.var .vz)))) := by
  apply ProofSyntax.allI
  apply ProofSyntax.eqSymm
  let body : Term Constants (.prop :: context) .prop := .app (weaken first) (.var .vz)
  apply ProofSyntax.castIndices rfl ?_
    (.beta (.var .vz) (rename (Rename.lift Rename.weaken) body))
  exact congrArg (fun result => Term.eq (.app (weaken second) (.var .vz)) result)
    (ContextualTrinity.instantiate_vz_rename_lift_weaken body)

theorem pointwise_free : pointwise.FunctionExtensionalityFree := by
  simp only [pointwise,ProofSyntax.FunctionExtensionalityFree,ProofSyntax.functionExtensionalityFree_castIndices]

def transported : ProofSyntax Constants [original] target :=
  .impE (.eqPropEL (signature.childConditions_array_eq predicate payload first second pointwise)) (.hyp 0)

theorem transported_free : transported.FunctionExtensionalityFree :=
  ⟨signature.childConditions_array_eq_free predicate payload first second pointwise pointwise_free,True.intro⟩

def values : model.Valuation context := model.extend (σ := .prop ⇒ .prop)
  (fun {type} (index : Var [] type) => nomatch index) (fun value => value)
theorem full : model.FullDomains := HenkinModel.fullDomains_standard _ _

theorem original_contract_realized : (model.denote original values).down := by
  intro slot _
  constructor
  · intro active
    exact ⟨Iff.rfl,active⟩
  · intro inactive
    exact ⟨inactive,False.elim⟩

theorem assumptions_realized : Soundness.SatisfiesHyps model values [original] := by
  intro formula present
  rcases List.mem_cons.mp present with rfl | impossible
  · exact original_contract_realized
  · cases impossible

theorem transported_contract_realized : (model.denote target values).down :=
  Soundness.extDerivation_sound transported.erase (M := model) (ρ := values)
    (model.functionsRespectEqv_of_fullDomains full) (fun _ => trivial) assumptions_realized

theorem original_array_nonconstant :
    model.denote first values (ULift.up True) ≠ model.denote first values (ULift.up False) := by
  intro same
  exact Eq.mp (congrArg ULift.down same) True.intro

def noPadding : Term Constants context (.prop ⇒ .prop) := .lam .top
def noActiveEvidence : Term Constants context (.prop ⇒ .prop) := .lam .bot

theorem wrong_inactive_padding_refused :
    ¬ (model.denote (signature.childConditions predicate payload noPadding) values).down := by
  intro conditions
  have atInactive := conditions (ULift.up False) (by trivial)
  exact (atInactive.2 (fun impossible => impossible)).mp True.intro

theorem wrong_active_obligations_refused :
    ¬ (model.denote (signature.childConditions predicate payload noActiveEvidence) values).down := by
  intro conditions
  have atActive := conditions (ULift.up True) (by trivial)
  exact (atActive.1 True.intro).1.mp True.intro

theorem absent_pointwise_evidence_refused :
    ¬ Nonempty (ProofSyntax Constants [original]
      (.all (.eq (.app (weaken first) (.var .vz)) (.app (weaken noPadding) (.var .vz))))) := by
  rintro ⟨claimed⟩
  have sound := Soundness.extDerivation_sound claimed.erase (M := model) (ρ := values)
    (model.functionsRespectEqv_of_fullDomains full) (fun _ => trivial) assumptions_realized
  exact (sound (ULift.up False) (by trivial)).mpr True.intro

#print axioms pointwise_free
#print axioms transported_free
#print axioms original_contract_realized
#print axioms transported_contract_realized
#print axioms absent_pointwise_evidence_refused

end Mettapedia.Logic.HOL.ContextualChildArrayCongruenceControls
