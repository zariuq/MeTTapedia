import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeTyping
import Mettapedia.GSLT.LanguageDef.OpenSortedEquationInstance

/-! Typed source valuations become sorted substitutions of the shared
equation interface. This connects the source IR to OpenSortedEquationInstance;
it does not identify that disciplined relation with raw EquationEquiv. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics

theorem encode_object (term : Maude.Term) : isObjectPattern (encode term) = true := by
  refine Maude.Term.rec
    (motive_1 := fun term => isObjectPattern (encode term) = true)
    (motive_2 := fun terms => isObjectPatternList (terms.map encode) = true)
    ?_ ?_ ?_ ?_ term
  · intro name
    rw [encode, isObjectPattern]
  · intro id arguments ih
    rw [encode, isObjectPattern, ih]
  · rfl
  · intro first rest firstIH restIH
    simp only [List.map_cons, isObjectPatternList, firstIH, restIH, Bool.and_self]

def assignmentBindings (names : List String) (assignment : Maude.Valuation) : Bindings :=
  names.map fun name => (name, encode (assignment name))

theorem assignmentBindings_find (names : List String) (assignment : Maude.Valuation)
    {name : String} (member : name ∈ names) :
    (assignmentBindings names assignment).find? (fun entry => entry.1 == name) = some (name, encode (assignment name)) := by
  induction names with
  | nil => cases member
  | cons head tail ih =>
      by_cases same : head = name
      · subst head
        simp [assignmentBindings]
      · have later : name ∈ tail := (List.mem_cons.mp member).resolve_left (Ne.symm same)
        simpa [assignmentBindings, same] using ih later

theorem assignmentBindings_apply (names : List String) (assignment : Maude.Valuation)
    {name : String} (member : name ∈ names) :
    applyBindings (assignmentBindings names assignment) (.fvar name) = encode (assignment name) := by
  rw [applyBindings, assignmentBindings_find names assignment member]

theorem context_lookup_of_mem {declarations : Maude.VariableContext}
    (distinct : (declarations.map Prod.fst).Nodup) {name sort : String}
    (member : (name, sort) ∈ declarations) : declarations.lookup name = some sort := by
  induction declarations with
  | nil => cases member
  | cons entry rest ih =>
      rcases entry with ⟨head, type⟩
      simp only [List.map_cons, List.nodup_cons] at distinct
      rcases List.mem_cons.mp member with same | later
      · cases same
        simp
      · have absent : name ≠ head := by
          intro same
          subst head
          exact distinct.1 (List.mem_map.mpr ⟨(name, sort), later, rfl⟩)
        have different : (name == head) = false := beq_eq_false_iff_ne.mpr absent
        simpa only [List.lookup_cons, different] using ih distinct.2 later

theorem source_valuation_sorted (prepared : Prepared) (ambient declarations : Maude.VariableContext)
    (assignment : Maude.Valuation) (distinct : (declarations.map Prod.fst).Nodup)
    (typed : Maude.TypedValuation prepared.source.signature ambient declarations assignment) :
    SortedBindingsIn prepared.language (freeContext ambient)
      (declarations.map fun entry => (entry.1, TypeExpr.base entry.2))
      (assignmentBindings (declarations.map Prod.fst) assignment) := by
  intro name type member
  obtain ⟨⟨key, sort⟩, sourceMember, same⟩ := List.mem_map.mp member
  cases same
  rw [assignmentBindings_apply _ assignment (List.mem_map.mpr ⟨(key, sort), sourceMember, rfl⟩)]
  exact ⟨encode_object _, (prepared_typing_iff prepared ambient (assignment key) sort).mpr
    (typed key sort (context_lookup_of_mem distinct sourceMember))⟩

theorem usedContext_distinct {signature : Maude.Signature} {row : Maude.Row}
    (checked : row.check signature = true) : (row.usedContext.map Prod.fst).Nodup := by
  simp only [Maude.Row.check, Bool.and_eq_true, decide_eq_true_eq] at checked
  have selected : row.usedContext.Sublist row.formals := by
    unfold Maude.Row.usedContext
    exact List.filter_sublist
  exact checked.1.1.1.sublist (selected.map Prod.fst)

theorem row_valuation_sorted (prepared : Prepared) (ambient : Maude.VariableContext)
    (row : Maude.Row) (assignment : Maude.Valuation)
    (checked : row.check prepared.source.signature = true)
    (typed : Maude.TypedValuation prepared.source.signature ambient row.usedContext assignment) :
    SortedBindingsIn prepared.language (freeContext ambient) (context row)
      (assignmentBindings (row.usedContext.map Prod.fst) assignment) :=
  source_valuation_sorted prepared ambient row.usedContext assignment (usedContext_distinct checked) typed

theorem equation_context {signature : Maude.Signature} {index : Nat} {row : Maude.Row} {equation : Equation}
    (produced : equation? signature index row = some equation) : equation.typeContext = context row := by
  cases conditions : conditions? signature row with
  | none => simp [equation?, conditions] at produced
  | some premises =>
      simp only [equation?, conditions, Option.pure_def] at produced
      cases produced
      rfl

theorem compiled_equation_valuation_sorted (prepared : Prepared) (ambient : Maude.VariableContext)
    (row : Maude.Row) (assignment : Maude.Valuation) {index : Nat} {equation : Equation}
    (produced : equation? prepared.source.signature index row = some equation)
    (checked : row.check prepared.source.signature = true)
    (typed : Maude.TypedValuation prepared.source.signature ambient row.usedContext assignment) :
    SortedBindingsIn prepared.language (freeContext ambient) equation.typeContext
      (assignmentBindings (row.usedContext.map Prod.fst) assignment) := by
  rw [equation_context produced]
  exact row_valuation_sorted prepared ambient row assignment checked typed

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation
