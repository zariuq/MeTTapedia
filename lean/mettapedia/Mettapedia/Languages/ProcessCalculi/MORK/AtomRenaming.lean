import Mettapedia.Languages.ProcessCalculi.MORK.Space

/-!
# Relabeling the logical variables of MORK's Atom syntax

Symbols, grounded data and expression shape remain fixed. This is structural
syntax mathematics; it introduces no evaluator or dialect policy. The readout
adapter consumes it downstream.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.AtomRenaming

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def rename (labels : String → String) : Atom → Atom
  | .var name => .var (labels name)
  | .symbol name => .symbol name
  | .grounded value => .grounded value
  | .expression items => .expression (list labels items)
where
  list (labels : String → String) : List Atom → List Atom
    | [] => []
    | first :: rest => rename labels first :: list labels rest

theorem list_eq_map (labels : String → String) : ∀ items : List Atom,
    rename.list labels items = items.map (rename labels)
  | [] => rfl
  | first :: rest => by simp only [rename.list,List.map_cons,list_eq_map labels rest]

theorem freeVars_rename (labels : String → String) : ∀ term : Atom,
    atomFreeVars (rename labels term) = (atomFreeVars term).map labels
  | .var _ => rfl
  | .symbol _ | .grounded _ => rfl
  | .expression items => list items
where
  list : ∀ items : List Atom,
      atomFreeVars.atomFreeVarsList (rename.list labels items) =
        (atomFreeVars.atomFreeVarsList items).map labels
    | [] => rfl
    | first :: rest => by
        simp only [rename.list,atomFreeVars.atomFreeVarsList,List.map_append,
          freeVars_rename labels first,list rest]

theorem identity : ∀ term : Atom, rename id term = term
  | .var _ | .symbol _ | .grounded _ => rfl
  | .expression items => by simp only [rename]; exact congrArg Atom.expression (list items)
where
  list : ∀ items : List Atom, rename.list id items = items
    | [] => rfl
    | first :: rest => by simp only [rename.list,identity first,list rest]

theorem composition (first second : String → String) : ∀ term : Atom,
    rename second (rename first term) = rename (second ∘ first) term
  | .var _ | .symbol _ | .grounded _ => rfl
  | .expression items => by simp only [rename]; exact congrArg Atom.expression (list items)
where
  list : ∀ items : List Atom,
      rename.list second (rename.list first items) = rename.list (second ∘ first) items
    | [] => rfl
    | head :: rest => by simp only [rename.list,composition first second head,list rest]

theorem variables_expression {key : String} {items : List Atom} :
    key ∈ atomFreeVars (.expression items) ↔ ∃ item ∈ items, key ∈ atomFreeVars item := by
  simp only [atomFreeVars]
  induction items with
  | nil => simp [atomFreeVars.atomFreeVarsList]
  | cons head rest ih =>
      simp only [atomFreeVars.atomFreeVarsList,List.mem_append,ih,List.mem_cons,exists_eq_or_imp]

theorem equal_iff_on_variables (first second : String → String) : ∀ term : Atom,
    rename first term = rename second term ↔ ∀ key ∈ atomFreeVars term, first key = second key
  | .var name => by simp [rename,atomFreeVars]
  | .symbol _ | .grounded _ => by simp [rename,atomFreeVars]
  | .expression items => by
      simp only [rename,Atom.expression.injEq,variables_expression]
      rw [list items]
      aesop
where
  list : ∀ items : List Atom,
      rename.list first items = rename.list second items ↔
        ∀ item ∈ items, ∀ key ∈ atomFreeVars item, first key = second key
    | [] => by simp [rename.list]
    | head :: rest => by
        simp only [rename.list,List.cons.injEq,equal_iff_on_variables first second head,
          list rest,List.mem_cons,forall_eq_or_imp]

/-- Two independently supplied variable maps recover both finite terms.
This relation does not mention a canonicalizer or a readout algorithm. -/
def Variant (first second : Atom) : Prop :=
  ∃ forward backward : String → String, rename forward first = second ∧ rename backward second = first

theorem Variant.refl (term : Atom) : Variant term term := ⟨id,id,identity term,identity term⟩
theorem Variant.symm {first second : Atom} (same : Variant first second) : Variant second first := by
  obtain ⟨forward,backward,left,right⟩ := same
  exact ⟨backward,forward,right,left⟩

theorem Variant.trans {first second third : Atom} (left : Variant first second) (right : Variant second third) :
    Variant first third := by
  obtain ⟨f,g,fg,gf⟩ := left
  obtain ⟨h,k,hk,kh⟩ := right
  refine ⟨h ∘ f,g ∘ k,?_,?_⟩
  · rw [← composition,fg,hk]
  · rw [← composition,kh,gf]

theorem retraction_injective_on_variables (term : Atom) (forward backward : String → String)
    (recovered : rename backward (rename forward term) = term) :
    ∀ first ∈ atomFreeVars term, ∀ second ∈ atomFreeVars term,
      forward first = forward second → first = second := by
  have fixed : rename (backward ∘ forward) term = rename id term := by
    rw [← composition,identity]
    exact recovered
  have pointwise := (equal_iff_on_variables _ _ term).mp fixed
  intro first firstIn second secondIn same
  exact (pointwise first firstIn).symm.trans ((congrArg backward same).trans (pointwise second secondIn))

end Mettapedia.Languages.ProcessCalculi.MORK.AtomRenaming
