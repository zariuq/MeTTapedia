import Mettapedia.OSLF.MeTTaIL.GeneralNullarySpecificationAdmission
import Mettapedia.Util.LinearHash

/-! A functional assignment of result sorts makes the actual inferred
empty-context capture table unique and consistent, even with arbitrarily
many repeated occurrences of a capture name.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar

open Syntax GeneralFirstOrderProjection

theorem lookupType_of_unique (context : List (String × TypeExpr))
    (unique : (context.map Prod.fst).Nodup) (name : String) (type : TypeExpr)
    (member : (name, type) ∈ context) : lookupType context name = some type := by
  have existsType : (context.lookup name).isSome := List.lookup_isSome_iff.mpr
    ⟨(name, type), member, by simp⟩
  obtain ⟨actual, found⟩ := Option.isSome_iff_exists.mp existsType
  have filtered := context_filter_of_lookup context unique found
  have present : (name, type) ∈ context.filter (fun entry => entry.1 == name) := by
    exact List.mem_filter.mpr ⟨member, by simp⟩
  rw [filtered] at present
  have same : type = actual := congrArg Prod.snd (List.mem_singleton.mp present)
  have justTypes : context.filterMap (fun entry => if entry.1 == name then some entry.2 else none) =
      (context.filter (fun entry => entry.1 == name)).map Prod.snd := by
    clear filtered found existsType present member unique
    induction context with
    | nil => rfl
    | cons entry rest ih =>
        simp only [beq_iff_eq] at ih ⊢
        by_cases equal : entry.1 = name <;> simp [equal, ih]
  simp only [lookupType, justTypes, filtered, List.map_cons, List.map_nil, unique?]
  simp [same, List.eraseDups_cons]

theorem implicitTypes_empty (rule : RewriteRule) (empty : rule.typeContext = []) (rows : List Occurrence) :
    implicitTypes rule rows = (rows.map fun row => (row.name, row.result)).eraseDups := by
  simp [implicitTypes, empty]

theorem implicitTypes_unique (rule : RewriteRule) (empty : rule.typeContext = [])
    (rows : List Occurrence) (typeOf : String → TypeExpr)
    (functional : ∀ row ∈ rows, row.result = typeOf row.name) :
    ((implicitTypes rule rows).map Prod.fst).Nodup := by
  rw [implicitTypes_empty rule empty rows]
  apply List.Nodup.map_on _ (Mettapedia.Util.LinearHash.eraseDups_nodup _)
  intro first firstMember second secondMember same
  obtain ⟨firstRow, firstAt, firstPair⟩ := List.mem_map.mp (List.mem_eraseDups.mp firstMember)
  obtain ⟨secondRow, secondAt, secondPair⟩ := List.mem_map.mp (List.mem_eraseDups.mp secondMember)
  cases firstPair
  cases secondPair
  exact Prod.ext same ((functional firstRow firstAt).trans ((congrArg typeOf same).trans (functional secondRow secondAt).symm))

theorem implicitTypes_member (rule : RewriteRule) (empty : rule.typeContext = [])
    (rows : List Occurrence) (row : Occurrence) (present : row ∈ rows) :
    (row.name, row.result) ∈ implicitTypes rule rows := by
  rw [implicitTypes_empty rule empty rows]
  exact List.mem_eraseDups.mpr (List.mem_map.mpr ⟨row, present, rfl⟩)

theorem implicitTypes_consistent (rule : RewriteRule) (empty : rule.typeContext = [])
    (rows : List Occurrence) (typeOf : String → TypeExpr)
    (functional : ∀ row ∈ rows, row.result = typeOf row.name)
    (unbound : ∀ row ∈ rows, row.bound = []) : consistent (implicitTypes rule rows) rows = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply List.all_eq_true.mpr
    intro row present
    exact beq_iff_eq.mpr (lookupType_of_unique _ (implicitTypes_unique rule empty rows typeOf functional)
      row.name row.result (implicitTypes_member rule empty rows row present))
  · apply List.all_eq_true.mpr
    intro first firstMember
    apply List.all_eq_true.mpr
    intro second secondMember
    simp only [unbound first firstMember, unbound second secondMember, beq_self_eq_true, Bool.or_true]

#print axioms lookupType_of_unique
#print axioms implicitTypes_unique
#print axioms implicitTypes_member
#print axioms implicitTypes_consistent

end Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar
