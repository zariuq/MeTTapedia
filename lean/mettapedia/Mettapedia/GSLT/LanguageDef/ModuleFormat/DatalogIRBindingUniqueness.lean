import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRBindingContext
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Sigma

/-! The actual generated declaration context has unique names. Pool slots,
logical variables and anonymous occurrences occupy distinct name domains;
anonymous occurrences retain both their body and argument positions. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.BindingContext

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax

private def anonymousRoles (position : Nat) : Mettapedia.Languages.Datalog.Premise → List Names.Role
  | .comparison _ => []
  | .atom atom => atom.arguments.zipIdx.filterMap fun entry =>
      if entry.1.isAnonymous then some (.anonymous position entry.2) else none

private theorem anonymous_member (position : Nat) (premise : Mettapedia.Languages.Datalog.Premise)
    (role : Names.Role) (member : role ∈ anonymousRoles position premise) :
    ∃ index, role = .anonymous position index := by
  cases premise with
  | comparison _ => cases member
  | atom atom =>
    obtain ⟨entry,_,formed⟩ := List.mem_filterMap.mp member
    split at formed
    · exact ⟨entry.2,(Option.some.inj formed).symm⟩
    · cases formed

private theorem anonymous_nodup (position : Nat) (premise : Mettapedia.Languages.Datalog.Premise) :
    (anonymousRoles position premise).Nodup := by
  cases premise with
  | comparison _ => exact List.nodup_nil
  | atom atom =>
    have indexed := List.pairwise_map.mp (List.nodup_zipIdx_map_snd atom.arguments)
    apply List.Pairwise.filterMap _ ?_ indexed
    intro first second different left leftFormed right rightFormed same
    split at leftFormed
    · cases Option.some.inj leftFormed
      split at rightFormed
      · cases Option.some.inj rightFormed
        exact different (Names.Role.anonymous.inj same).2
      · cases rightFormed
    · cases leftFormed

private def roles (pools : Join.Pools) (clause : Clause) : List Names.Role :=
  (List.range pools.relations.length).map .relation ++
  (List.range pools.literals.length).map .literal ++
  clause.providedVariables.dedup.map .logical ++
  (Join.orderedBody clause).zipIdx.flatMap fun entry => anonymousRoles entry.2 entry.1

private theorem anonymous_batch_nodup (body : List Mettapedia.Languages.Datalog.Premise) :
    (body.zipIdx.flatMap fun entry => anonymousRoles entry.2 entry.1).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun entry _ => anonymous_nodup entry.2 entry.1,?_⟩
  apply (List.pairwise_map.mp (List.nodup_zipIdx_map_snd body)).imp
  intro first second different
  apply List.disjoint_left.mpr
  intro role left right
  obtain ⟨i,firstEqual⟩ := anonymous_member first.2 first.1 role left
  obtain ⟨j,secondEqual⟩ := anonymous_member second.2 second.1 role right
  exact different (Names.Role.anonymous.inj (firstEqual.symm.trans secondEqual)).1

private theorem roles_nodup (pools : Join.Pools) (clause : Clause) : (roles pools clause).Nodup := by
  have relations := (List.nodup_range (n := pools.relations.length)).map (fun _ _ same => Names.Role.relation.inj same)
  have literals := (List.nodup_range (n := pools.literals.length)).map (fun _ _ same => Names.Role.literal.inj same)
  have logical := (List.nodup_dedup clause.providedVariables).map (fun _ _ same => Names.Role.logical.inj same)
  simp only [roles,List.nodup_append']
  refine ⟨⟨⟨relations,literals,?_⟩,logical,?_⟩,anonymous_batch_nodup _,?_⟩
  · apply List.disjoint_left.mpr
    intro role relationMember member
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp relationMember
    obtain ⟨other,_,same⟩ := List.mem_map.mp member
    cases same
  · apply List.disjoint_left.mpr
    intro role member logicalMember
    obtain ⟨name,_,rfl⟩ := List.mem_map.mp logicalMember
    rcases List.mem_append.mp member with relation | literal
    · obtain ⟨index,_,same⟩ := List.mem_map.mp relation
      cases same
    · obtain ⟨index,_,same⟩ := List.mem_map.mp literal
      cases same
  · apply List.disjoint_left.mpr
    intro role member anonymousMember
    obtain ⟨entry,_,produced⟩ := List.mem_flatMap.mp anonymousMember
    obtain ⟨index,rfl⟩ := anonymous_member entry.2 entry.1 role produced
    rcases List.mem_append.mp member with earlier | logical
    · rcases List.mem_append.mp earlier with relation | literal
      · obtain ⟨index,_,same⟩ := List.mem_map.mp relation
        cases same
      · obtain ⟨index,_,same⟩ := List.mem_map.mp literal
        cases same
    · obtain ⟨name,_,same⟩ := List.mem_map.mp logical
      cases same

private theorem logical_injective : Function.Injective Join.logicalVariable := by
  intro first second same
  exact (String.append_right_inj "variable:").mp same

private theorem context_names (pools : Join.Pools) (clause : Clause) :
    (Join.variableContext pools clause).map Prod.fst = "facts" :: (roles pools clause).map Names.encode := by
  simp only [Join.variableContext,roles,List.map_append,List.map_cons,List.map_map,
    Join.relationSlots,Join.literalSlots,List.map_flatMap,
    List.dedup_map_of_injective logical_injective,Function.comp_def,Names.encode,
    List.cons_append,List.nil_append]
  congr 1
  congr 1
  apply List.flatMap_congr
  intro entry _
  rcases entry with ⟨premise,position⟩
  cases premise with
  | comparison _ => rfl
  | atom atom =>
    simp only [anonymousRoles,List.map_filterMap]
    apply List.filterMap_congr
    intro entry _
    split <;> rfl

theorem variable_context_nodup (pools : Join.Pools) (clause : Clause) :
    ((Join.variableContext pools clause).map Prod.fst).Nodup := by
  rw [context_names,List.nodup_cons]
  refine ⟨?_,(roles_nodup pools clause).map Names.encode_injective⟩
  intro member
  obtain ⟨role,_,same⟩ := List.mem_map.mp member
  have first := congrArg (fun name => name.toList.head?) same
  cases role <;> simp [Names.encode,Join.relationSlot,Join.literalSlot,Join.logicalVariable,
    Join.anonymousVariable,String.toList_append] at first

theorem context_nodup (pools : Join.Pools) (clause : Clause) :
    ((context pools clause).map Prod.fst).Nodup :=
  (variable_context_nodup pools clause).sublist (List.filter_sublist.map _)

theorem compiled_context_nodup (pools : Join.Pools) (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (compiled : Query.compileClause? pools ordinal clause = some rule) : (rule.typeContext.map Prod.fst).Nodup := by
  rw [compiled_context pools ordinal clause rule compiled]
  exact context_nodup pools clause

#print axioms variable_context_nodup
#print axioms context_nodup
#print axioms compiled_context_nodup

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.BindingContext
