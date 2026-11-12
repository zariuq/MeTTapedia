import Mettapedia.Languages.MeTTa.PeTTa.ConstructorSpine

/-!
# Ordered source evaluations of constructor operands

Every operand is backed by its actual source path. Alternatives keep their
own substitutions and run their suffixes in discovery order through the shared
world. This finite judgment describes completed schedules, without asserting
that all operands terminate or replacing them by a value oracle.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ConstructorEvaluation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst atomFreeVars)
open Unifying
open Mettapedia.Machines.OrderedProtocol.Completion (OrderedStateFlatMapRel)

structure Values where
  items : List Atom
  bindings : Subst

def Values.toAnswer (value : Values) : Answer := ⟨.expression value.items,value.bindings⟩

def Values.prepend (head : Atom) (value : Values) : Values :=
  ⟨resolve value.bindings head :: value.items,value.bindings⟩

def Values.withHeld (held : List Atom) (value : Values) : Answer :=
  ⟨.expression (held.map (resolve value.bindings) ++ value.items),value.bindings⟩

def Values.Normal (value : Values) : Prop :=
  Idempotent value.bindings ∧ Unbound value.bindings (.expression value.items)

theorem Values.prepend_normal (head : Atom) (value : Values) (normal : value.Normal) :
    (value.prepend head).Normal := by
  refine ⟨normal.1,?_⟩
  intro key member
  change key ∈ atomFreeVars (resolve value.bindings head) ++ atomFreeVars (.expression value.items) at member
  rcases List.mem_append.mp member with inHead | inTail
  · exact unbound_resolve normal.1 head key inHead
  · exact normal.2 key inTail

theorem Values.withHeld_prepend (held : List Atom) (head : Atom) (value : Values) :
    (value.prepend head).withHeld held = value.withHeld (held ++ [head]) := by
  simp [Values.withHeld,Values.prepend,List.map_append,List.append_assoc]

theorem Values.withHeld_nil (value : Values) : value.withHeld [] = value.toAnswer := rfl

mutual
  inductive Items (registry : SpaceSemantics.Program) :
      Configuration → Subst → List Atom → Configuration → List Values → Prop where
    | nil {before bindings} : Items registry before bindings [] before [⟨[],bindings⟩]
    | cons {before middle after bindings first rest answers values} :
        CompletedControl registry (.evaluate bindings first) before answers middle →
        Branches registry rest answers middle after values →
        Items registry before bindings (first :: rest) after values

  inductive Branches (registry : SpaceSemantics.Program) :
      List Atom → List Answer → Configuration → Configuration → List Values → Prop where
    | nil {rest before} : Branches registry rest [] before before []
    | cons {rest head more before middle after firstValues laterValues} :
        Items registry before head.bindings rest middle firstValues →
        Branches registry rest more middle after laterValues →
        Branches registry rest (head :: more) before after
          (firstValues.map (Values.prepend head.value) ++ laterValues)
end

theorem Items.normal {registry : SpaceSemantics.Program} {before after : Configuration}
    {bindings : Subst} {expressions : List Atom} {values : List Values}
    (source : Items registry before bindings expressions after values) :
    Idempotent bindings → ∀ value ∈ values, value.Normal := by
  refine Items.rec
    (motive_1 := fun _ bindings _ _ values _ => Idempotent bindings → ∀ value ∈ values, value.Normal)
    (motive_2 := fun _ answers _ _ values _ =>
      (∀ answer ∈ answers, Idempotent answer.bindings) → ∀ value ∈ values, value.Normal)
    ?_ ?_ ?_ ?_ source
  · intro before bindings valid value member
    simp only [List.mem_singleton] at member
    subst value
    refine ⟨valid,?_⟩
    intro key present
    cases present
  · intro before middle after bindings first rest answers values operand branches ih valid
    exact ih (completed_operand_bindings_valid valid operand)
  · intro rest before _ value member
    cases member
  · intro rest head more before middle after firstValues laterValues first later firstIH laterIH valid
    have firstNormal := firstIH (valid head (by simp))
    have laterNormal := laterIH (fun answer member => valid answer (List.mem_cons_of_mem head member))
    intro value member
    rcases List.mem_append.mp member with earlier | following
    · obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp earlier
      exact original.prepend_normal head.value (firstNormal original originalMember)
    · exact laterNormal value following

theorem Branches.normal {registry : SpaceSemantics.Program} {before after : Configuration}
    {expressions : List Atom} {answers : List Answer} {values : List Values}
    (source : Branches registry expressions answers before after values)
    (valid : ∀ answer ∈ answers, Idempotent answer.bindings) :
    ∀ value ∈ values, value.Normal := by
  induction answers generalizing before after values with
  | nil => cases source; intro value member; cases member
  | cons head more ih =>
      cases source with
      | cons first later =>
          have firstNormal := first.normal (valid head (by simp))
          have laterNormal := ih later (fun answer member => valid answer (List.mem_cons_of_mem head member))
          intro value member
          rcases List.mem_append.mp member with earlier | following
          · obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp earlier
            exact original.prepend_normal head.value (firstNormal original originalMember)
          · exact laterNormal value following

end Mettapedia.Languages.MeTTa.PeTTa.ConstructorEvaluation
