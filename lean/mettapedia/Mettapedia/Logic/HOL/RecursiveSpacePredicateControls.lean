import Mettapedia.Logic.HOL.RecursiveSpacePredicate
import Mettapedia.Logic.HOL.ContextualRecursiveSpaceProofs
import Mettapedia.Logic.HOL.PredicateFixedPointSemantics
import Mettapedia.TypeTheory.RecursiveSpace

/-!
# Guard and padding controls for the positive recursive-space operator

The model uses real recursive-space trees. A zero node has no active children;
a successor node has exactly its zeroth child active. Hidden non-bottom padding
is refused even when every active child satisfies the predicate. Complementing
the recursive predicate violates monotonicity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.RecursiveSpacePredicate.Controls

open Mettapedia.TypeTheory
abbrev Tree := RecursiveSpace.Tree Bool

inductive Base where | number | payload | space
abbrev number : Ty Base := .base .number
abbrev payload : Ty Base := .base .payload
abbrev space : Ty Base := .base .space

inductive Const : Ty Base → Type where
  | bottom : Const space
  | construct : Const (number ⇒ payload ⇒ (number ⇒ space) ⇒ space)
  | validShape : Const (number ⇒ payload ⇒ .prop)
  | active : Const (payload ⇒ number ⇒ .prop)
  | validEdge : Const (payload ⇒ number ⇒ space ⇒ .prop)

@[reducible] def signature : Signature Const :=
  ⟨number,payload,space,.const .bottom,.const .construct,.const .validShape,.const .active,.const .validEdge⟩

def shape (tag : Nat) (payload : Bool) : Prop :=
  (tag = 0 ∧ payload = false) ∨ (tag = 1 ∧ payload = true)

def active (payload : Bool) (position : Nat) : Prop := payload = true ∧ position = 0

def carrier : Base → Type 1
  | .number => ULift.{1} Nat
  | .payload => ULift.{1} Bool
  | .space => ULift.{1} Tree

@[reducible] def model : HenkinModel.{0,0,0} Base Const := .standard carrier (fun symbol => match symbol with
  | .bottom => .up RecursiveSpace.bottom
  | .construct => fun tag payload children => .up
      (RecursiveSpace.construct tag.down payload.down (fun n => (children (.up n)).down))
  | .validShape => fun tag payload => .up (shape tag.down payload.down)
  | .active => fun payload position => .up (active payload.down position.down)
  | .validEdge => fun _ _ _ => .up True)

theorem full : model.FullDomains := HenkinModel.fullDomains_standard _ _

def holds (predicate : Tree → Prop) (point : Tree) : Prop :=
  (Signature.denotes model signature.operator (fun value => .up (predicate value.down)) (.up point)).down

def step (predicate : Tree → Prop) (point : Tree) : Prop :=
  ∃ tag payload children, shape tag payload ∧ point = RecursiveSpace.construct tag payload children ∧
    ∀ n, (active payload n → predicate (children n)) ∧
      (¬ active payload n → children n = RecursiveSpace.bottom)

theorem holds_iff (predicate : Tree → Prop) (point : Tree) : holds predicate point ↔ step predicate point := by
  unfold holds
  refine (signature.operator_meaning model full (fun value => .up (predicate value.down)) (.up point)).trans ?_
  constructor
  · rintro ⟨⟨tag⟩,⟨payload⟩,children,valid,equal,conditions⟩
    refine ⟨tag,payload,(fun n => (children (.up n)).down),valid,congrArg ULift.down equal,?_⟩
    intro n
    exact ⟨fun present => ((conditions (.up n)).1 present).2,
      fun absent => congrArg ULift.down ((conditions (.up n)).2 absent)⟩
  · rintro ⟨tag,payload,children,valid,equal,conditions⟩
    refine ⟨.up tag,.up payload,(fun n => .up (children n.down)),valid,congrArg ULift.up equal,?_⟩
    rintro ⟨n⟩
    exact ⟨fun present => ⟨True.intro,(conditions n).1 present⟩,
      fun absent => congrArg ULift.up ((conditions n).2 absent)⟩

def zero : Tree := RecursiveSpace.construct 0 false (fun _ => RecursiveSpace.bottom)
def one : Tree := RecursiveSpace.construct 1 true (fun n => if n = 0 then zero else RecursiveSpace.bottom)
def hiddenTail : Tree := RecursiveSpace.construct 1 true
  (fun n => if n = 0 ∨ n = 1 then zero else RecursiveSpace.bottom)

theorem zero_from_empty_predicate : holds (fun _ => False) zero := by
  rw [holds_iff]
  refine ⟨0,false,_,Or.inl ⟨rfl,rfl⟩,rfl,?_⟩
  intro n
  exact ⟨fun present => Bool.noConfusion present.1,fun _ => rfl⟩

theorem one_from_zero : holds (fun tree => tree = zero) one := by
  rw [holds_iff]
  refine ⟨1,true,_,Or.inr ⟨rfl,rfl⟩,rfl,?_⟩
  intro n
  constructor
  · rintro ⟨_,rfl⟩
    rfl
  · intro absent
    have nonzero : n ≠ 0 := fun equal => absent ⟨rfl,equal⟩
    simp only [if_neg nonzero]

theorem hidden_tail_active_child_valid :
    ∀ n, active true n → (if n = 0 ∨ n = 1 then zero else RecursiveSpace.bottom) = zero := by
  intro n present
  rw [present.2]
  rfl

theorem hidden_tail_refused : ¬ holds (fun tree => tree = zero) hiddenTail := by
  rw [holds_iff]
  rintro ⟨tag,payload,children,_,equal,conditions⟩
  obtain ⟨rfl,rfl,same⟩ := (RecursiveSpace.construct_injective _ _ _ _ _ _).mp equal.symm
  have padding := (conditions 1).2 (by simp [active])
  have atOne := congrFun same 1
  simp only [Nat.one_ne_zero, or_true, if_true] at atOne
  exact RecursiveSpace.construct_ne_bottom 0 false _ (atOne.symm.trans padding)

def complement : ClosedTerm Const (PredicateFixedPoint.Operator space) :=
  .lam (.lam (.not (.app (.var (.vs .vz)) (.var .vz))))

theorem complement_not_monotone : ¬ model.models (PredicateFixedPoint.monotone complement) := by
  intro monotone
  have inclusion : ∀ value : ULift.{1} Tree, True → False → True := fun _ _ impossible => impossible.elim
  have contradiction := monotone (fun _ => ULift.up False) True.intro
    (fun _ => ULift.up True) True.intro inclusion (ULift.up RecursiveSpace.bottom) True.intro (fun impossible => impossible)
  exact contradiction True.intro

namespace MethodInduction

def system : Contextual Const [] := signature.contextual

def nonBottom : ClosedTerm Const (space ⇒ .prop) :=
  .lam (.not (.eq (.var .vz) (weaken system.bottom)))

def caseLaw : ClosedFormula Const :=
  .all (σ := number) (.all (σ := payload) (.all (σ := number ⇒ space)
    (.not (.eq
      (system.constructorScope.constructValue system.constructorTag
        system.constructorPayload system.constructorChildren)
      (weaken (weaken (weaken system.bottom)))))))

def method : system.ConstructorMethod (assumptions := [caseLaw])
    (PredicateFixedPoint.intersection system.least nonBottom) nonBottom := by
  let built := system.constructorScope.constructValue system.constructorTag
    system.constructorPayload system.constructorChildren
  have available : ProofSyntax Const
      (system.methodAssumptions (assumptions := [caseLaw])
        (PredicateFixedPoint.intersection system.least nonBottom))
      (weaken (weaken (weaken caseLaw))) :=
    ProofSyntax.hyp (Const := Const)
      (Δ := system.methodAssumptions (assumptions := [caseLaw])
        (PredicateFixedPoint.intersection system.least nonBottom))
      ⟨2, by simp [Contextual.methodAssumptions, weakenHyps]⟩
  have selected := ProofSyntax.allE system.constructorChildren
    (.allE system.constructorPayload (.allE system.constructorTag available))
  apply ProofSyntax.impE (.eqPropER (.beta built
    (.not (.eq (.var .vz) (weaken (Term.const Const.bottom))))))
  apply ProofSyntax.castIndices rfl ?_ selected
  simp [built, system, Signature.contextual, Contextual.constructorScope,
    Contextual.constructorTag, Contextual.constructorPayload,
    Contextual.constructorChildren, Contextual.constructValue, Contextual.subst,
    instantiate, HOL.subst, Subst.single, Subst.lift,
    weaken, HOL.rename, Rename.weaken, Rename.lift]

theorem method_free : method.FunctionExtensionalityFree := by
  unfold method
  apply And.intro True.intro
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

def bottom_excluded : ProofSyntax Const [caseLaw] (.not (.app system.least system.bottom)) := by
  refine .notI ?_
  let retained := system.prepend_method (.app system.least system.bottom)
    (PredicateFixedPoint.intersection system.least nonBottom) nonBottom method
  have result := system.induction_from_method nonBottom system.bottom retained (.hyp 0)
  have unequal := ProofSyntax.impE (.eqPropEL (.beta system.bottom
    (.not (.eq (.var .vz) (weaken system.bottom))))) result
  exact .notE (ProofSyntax.castIndices rfl (by simp [instantiate, HOL.subst, Subst.single]) unequal)
    (.eqRefl system.bottom)

theorem bottom_excluded_free : bottom_excluded.FunctionExtensionalityFree := by
  unfold bottom_excluded
  apply And.intro
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    refine ⟨True.intro, ?_⟩
    apply system.induction_from_method_free
    · exact system.prepend_method_free _ _ _ method method_free
    · trivial
  · trivial

theorem caseLaw_valid : model.models caseLaw := by
  intro tag _ data _ children _ impossible
  exact RecursiveSpace.construct_ne_bottom tag.down data.down
    (fun n => (children (.up n)).down) (congrArg ULift.down impossible)

/-- A counterinterpretation deliberately collapses all constructor outputs.
It is not the recursive-space representation. -/
@[reducible] def collapsedModel : HenkinModel.{0,0,0} Base Const := .standard carrier (fun symbol => match symbol with
  | .bottom => .up RecursiveSpace.bottom
  | .construct => fun _ _ _ => .up RecursiveSpace.bottom
  | .validShape => fun tag payload => .up (shape tag.down payload.down)
  | .active => fun payload position => .up (active payload.down position.down)
  | .validEdge => fun _ _ _ => .up True)

theorem collapsed_full : collapsedModel.FullDomains := HenkinModel.fullDomains_standard _ _

theorem collapsed_caseLaw_invalid : ¬ collapsedModel.models caseLaw := by
  intro law
  exact law (.up 0) True.intro (.up false) True.intro
    (fun _ => .up RecursiveSpace.bottom) True.intro rfl

private def emptyValues (interpretation : HenkinModel.{0,0,0} Base Const) :
    interpretation.Valuation [] := fun index => nomatch index

private theorem emptyValues_unique (interpretation : HenkinModel.{0,0,0} Base Const)
    (values : interpretation.Valuation []) : @values = @emptyValues interpretation := by
  funext type index
  nomatch index

private theorem models_predicate_application (interpretation : HenkinModel.{0,0,0} Base Const)
    {type : Ty Base} (predicate : ClosedTerm Const (type ⇒ .prop))
    (point : ClosedTerm Const type) :
    interpretation.models (.app predicate point) ↔
      (interpretation.denote predicate (fun index => nomatch index)
        (interpretation.denote point (fun index => nomatch index))).down := by
  simp only [HenkinModel.models, PreModel.models, HenkinModel.denote, PreModel.denote]
  simp only [emptyValues_unique interpretation]

private theorem models_least_application (interpretation : HenkinModel.{0,0,0} Base Const)
    (family : Contextual Const []) (point : ClosedTerm Const family.space) :
    interpretation.models (.app family.least point) ↔
      ∀ predicate : Ty.denote interpretation.Carrier (family.space ⇒ .prop),
        interpretation.adm _ predicate →
        (∀ value, interpretation.adm family.space value →
          (interpretation.denote family.operator (fun index => nomatch index) predicate value).down →
          (predicate value).down) →
        (predicate (interpretation.denote point (fun index => nomatch index))).down := by
  rw [models_predicate_application]
  simpa only [Contextual.least, emptyValues_unique interpretation] using
    PredicateFixedPoint.least_denote interpretation family.operator
    (fun index => nomatch index) (interpretation.denote point (fun index => nomatch index))

theorem collapsed_bottom_member :
    collapsedModel.models (.app system.least system.bottom) := by
  apply (models_least_application collapsedModel system system.bottom).mpr
  intro predicate _ closed
  apply closed (.up RecursiveSpace.bottom) True.intro
  apply (system.operator_meaning collapsedModel collapsed_full
    (fun index => nomatch index) predicate (.up RecursiveSpace.bottom)).mpr
  refine ⟨.up 0, .up false, (fun _ => .up RecursiveSpace.bottom), Or.inl ⟨rfl, rfl⟩, rfl, ?_⟩
  intro slot
  constructor
  · intro enabled
    exact Bool.noConfusion enabled.1
  · intro _
    rfl

theorem unlicensed_bottom_exclusion_invalid :
    ¬ collapsedModel.models (.not (.app system.least system.bottom)) := by
  intro excluded
  exact (HenkinModel.models_not collapsedModel).mp excluded collapsed_bottom_member

theorem bottom_excluded_valid : model.models (.not (.app system.least system.bottom)) := by
  have implication : model.models (.imp caseLaw (.not (.app system.least system.bottom))) :=
    Soundness.extTheorem_sound (.impI bottom_excluded.erase) model
      (model.functionsRespectEqv_of_fullDomains full)
  exact (HenkinModel.models_imp model).mp implication caseLaw_valid

theorem separation_cannot_be_dropped :
    ¬ Nonempty (ProofSyntax Const [] (.not (.app system.least system.bottom))) := by
  rintro ⟨proof⟩
  exact unlicensed_bottom_exclusion_invalid
    (Soundness.extTheorem_sound proof.erase collapsedModel
      (collapsedModel.functionsRespectEqv_of_fullDomains collapsed_full))

end MethodInduction

#print axioms holds_iff
#print axioms zero_from_empty_predicate
#print axioms one_from_zero
#print axioms hidden_tail_refused
#print axioms complement_not_monotone
#print axioms MethodInduction.method
#print axioms MethodInduction.method_free
#print axioms MethodInduction.bottom_excluded
#print axioms MethodInduction.bottom_excluded_free
#print axioms MethodInduction.caseLaw_valid
#print axioms MethodInduction.collapsed_caseLaw_invalid
#print axioms MethodInduction.collapsed_bottom_member
#print axioms MethodInduction.unlicensed_bottom_exclusion_invalid
#print axioms MethodInduction.bottom_excluded_valid
#print axioms MethodInduction.separation_cannot_be_dropped

end Mettapedia.Logic.HOL.RecursiveSpacePredicate.Controls
