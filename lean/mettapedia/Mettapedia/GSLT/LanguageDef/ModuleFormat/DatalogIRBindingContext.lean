import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRNames
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRBodyCompilation

/-! Actual clause contexts assign relation slots their relation sort and all
literal, logical and anonymous slots their value sort. Duplicate consistent
entries do not require an extra uniqueness assumption for lookup typing. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.BindingContext

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax

def roleType : Names.Role → TypeExpr
  | .relation _ => .base "DlRelation"
  | _ => .base "DlValue"

def context (pools : Join.Pools) (clause : Clause) : List (String × TypeExpr) :=
  (Join.variableContext pools clause).filter (fun entry => entry.1 != "facts")

theorem context_roles (pools : Join.Pools) (clause : Clause) (entry : String × TypeExpr)
    (member : entry ∈ context pools clause) : ∃ role, entry = (Names.encode role,roleType role) := by
  have filtered : entry ∈ Join.variableContext pools clause ∧ (entry.1 != "facts") = true := List.mem_filter.mp member
  obtain ⟨member,retained⟩ := filtered
  simp only [Join.variableContext,List.mem_append,List.mem_singleton] at member
  rcases member with (((facts | relation) | literal) | logical) | anonymous
  · subst entry
    simp at retained
  · obtain ⟨slot,present,rfl⟩ := List.mem_map.mp relation
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp present
    exact ⟨.relation index,rfl⟩
  · obtain ⟨slot,present,rfl⟩ := List.mem_map.mp literal
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp present
    exact ⟨.literal index,rfl⟩
  · obtain ⟨slot,present,rfl⟩ := List.mem_map.mp logical
    obtain ⟨name,_,rfl⟩ := List.mem_map.mp (List.mem_dedup.mp present)
    exact ⟨.logical name,rfl⟩
  · obtain ⟨⟨premise,position⟩,_,produced⟩ := List.mem_flatMap.mp anonymous
    cases premise with
    | comparison _ => cases produced
    | atom atom =>
      obtain ⟨⟨argument,index⟩,_,formed⟩ := List.mem_filterMap.mp produced
      dsimp only at formed
      split at formed
      · cases Option.some.inj formed
        exact ⟨.anonymous position index,rfl⟩
      · cases formed

private theorem lookup_member {α : Type} (entries : List (String × α)) (name : String) (value : α)
    (found : entries.lookup name = some value) : (name,value) ∈ entries := by
  induction entries with
  | nil => simp at found
  | cons entry rest ih =>
    rcases entry with ⟨key,actual⟩
    by_cases same : name = key
    · subst key
      have actualSame : actual = value := Option.some.inj (by simpa [List.lookup] using found)
      subst actual
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih (by
        simpa only [List.lookup,show (name == key) = false from beq_eq_false_iff_ne.mpr same] using found))

theorem lookup_role_type (pools : Join.Pools) (clause : Clause) (role : Names.Role) (type : TypeExpr)
    (found : (context pools clause).lookup (Names.encode role) = some type) : type = roleType role := by
  obtain ⟨actual,same⟩ := context_roles pools clause _ (lookup_member _ _ _ found)
  have names := congrArg Prod.fst same
  have roles := Names.encode_injective names
  subst actual
  exact congrArg Prod.snd same

theorem compiled_context (pools : Join.Pools) (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (compiled : Query.compileClause? pools ordinal clause = some rule) : rule.typeContext = context pools clause := by
  obtain ⟨original,formed,rfl⟩ := Option.map_eq_some_iff.mp compiled
  cases safe : clause.checkRangeRestriction with
  | false => simp [Join.compileClause?,safe] at formed
  | true =>
    simp only [Join.compileClause?,safe,Bool.not_true,Bool.false_eq_true,if_false] at formed
    change ((Join.atom? pools clause.body.length clause.head).bind fun right =>
      ((Join.orderedBody clause).zipIdx.mapM fun entry => Join.bodyPremise? pools entry.2 entry.1).bind fun premises =>
        some ({
          name := "datalog-clause:" ++ toString ordinal
          typeContext := Join.variableContext pools clause
          premises := premises
          left := .apply "Infer" [Join.poolPattern (Join.relationSlots pools),
            Join.poolPattern (Join.literalSlots pools),.fvar "facts"]
          right := right } : RewriteRule)) = some original at formed
    simp only [Option.bind_eq_some_iff,Option.some.injEq] at formed
    obtain ⟨_,_,_,_,rfl⟩ := formed
    rfl

private theorem role_ne_facts (role : Names.Role) : Names.encode role ≠ "facts" := by
  intro same
  have first := congrArg (fun name => name.toList.head?) same
  cases role <;> simp [Names.encode,Join.relationSlot,Join.literalSlot,Join.logicalVariable,Join.anonymousVariable,String.toList_append] at first

theorem member_lookup (pools : Join.Pools) (clause : Clause) (role : Names.Role)
    (member : (Names.encode role,roleType role) ∈ context pools clause) :
    (context pools clause).lookup (Names.encode role) = some (roleType role) := by
  have defined : ((context pools clause).lookup (Names.encode role)).isSome = true :=
    List.lookup_isSome_iff.mpr ⟨(Names.encode role,roleType role),member,by simp⟩
  obtain ⟨type,found⟩ := Option.isSome_iff_exists.mp defined
  exact lookup_role_type pools clause role type found ▸ found

private theorem retained_role (pools : Join.Pools) (clause : Clause) (role : Names.Role)
    (member : (Names.encode role,roleType role) ∈ Join.variableContext pools clause) :
    (Names.encode role,roleType role) ∈ context pools clause :=
  List.mem_filter.mpr ⟨member,by simp [role_ne_facts role]⟩

theorem relation_declared (pools : Join.Pools) (clause : Clause) (index : Nat) (inside : index < pools.relations.length) :
    (context pools clause).lookup (Join.relationSlot index) = some (.base "DlRelation") := by
  apply member_lookup pools clause (.relation index)
  apply retained_role
  simp only [Join.variableContext,List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map.mpr
    ⟨Join.relationSlot index,List.mem_map.mpr ⟨index,List.mem_range.mpr inside,rfl⟩,rfl⟩))))

theorem literal_declared (pools : Join.Pools) (clause : Clause) (index : Nat) (inside : index < pools.literals.length) :
    (context pools clause).lookup (Join.literalSlot index) = some (.base "DlValue") := by
  apply member_lookup pools clause (.literal index)
  apply retained_role
  simp only [Join.variableContext,List.mem_append]
  exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr
    ⟨Join.literalSlot index,List.mem_map.mpr ⟨index,List.mem_range.mpr inside,rfl⟩,rfl⟩)))

theorem logical_declared (pools : Join.Pools) (clause : Clause) (name : String) (provided : name ∈ clause.providedVariables) :
    (context pools clause).lookup (Join.logicalVariable name) = some (.base "DlValue") := by
  apply member_lookup pools clause (.logical name)
  apply retained_role
  have member : Join.logicalVariable name ∈ (clause.providedVariables.map Join.logicalVariable).dedup :=
    List.mem_dedup.mpr (List.mem_map.mpr ⟨name,provided,rfl⟩)
  simp only [Join.variableContext,List.mem_append,List.mem_singleton]
  exact Or.inl (Or.inr (List.mem_map.mpr ⟨Join.logicalVariable name,member,rfl⟩))

theorem anonymous_declared (pools : Join.Pools) (clause : Clause) (position index : Nat)
    (source : Mettapedia.Languages.Datalog.Atom)
    (atSource : (Join.orderedBody clause)[position]? = some (.atom source))
    (atArgument : source.arguments[index]? = some .anonymous) :
    (context pools clause).lookup (Join.anonymousVariable position index) = some (.base "DlValue") := by
  apply member_lookup pools clause (.anonymous position index)
  apply retained_role
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨(.atom source,position),List.mk_mem_zipIdx_iff_getElem?.mpr atSource,?_⟩
  apply List.mem_filterMap.mpr
  exact ⟨(.anonymous,index),List.mk_mem_zipIdx_iff_getElem?.mpr atArgument,rfl⟩

#print axioms context_roles
#print axioms lookup_role_type
#print axioms compiled_context
#print axioms relation_declared
#print axioms literal_declared
#print axioms logical_declared
#print axioms anonymous_declared

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.BindingContext
