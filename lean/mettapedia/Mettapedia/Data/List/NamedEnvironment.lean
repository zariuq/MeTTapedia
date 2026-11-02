import Mathlib.Data.List.Basic

/-! Nearest named binding and positional lookup agree. Source-order binding
groups are reversed when pushed, so the last binder is nearest in both
representations. Values are opaque to all lookup and shadowing laws. -/

set_option autoImplicit false

namespace List.NamedEnvironment

universe u
variable {α : Type u}

inductive Lookup (name : String) (value : α) : List (String × α) → Prop where
  | here (rest : List (String × α)) : Lookup name value ((name, value) :: rest)
  | there {other : String} {head : α} {rest : List (String × α)}
      (different : other ≠ name) (found : Lookup name value rest) : Lookup name value ((other, head) :: rest)

def lookup? (entries : List (String × α)) (name : String) : Option α :=
  (entries.find? fun entry => entry.1 == name).map Prod.snd

theorem lookup_cons (name other : String) (value : α) (rest : List (String × α)) :
    lookup? ((other, value) :: rest) name = if other == name then some value else lookup? rest name := by
  by_cases same : other = name <;> simp [lookup?, same]

theorem lookup_iff (entries : List (String × α)) (name : String) (value : α) :
    lookup? entries name = some value ↔ Lookup name value entries := by
  induction entries with
  | nil => constructor <;> intro found <;> cases found
  | cons entry rest ih =>
    obtain ⟨other, head⟩ := entry
    by_cases same : other = name
    · subst other
      simp only [lookup_cons, beq_self_eq_true, if_true, Option.some.injEq]
      constructor
      · intro equal; subst head; exact .here rest
      · intro found
        cases found with
        | here => rfl
        | there different _ => exact (different rfl).elim
    · simp only [lookup_cons, beq_eq_false_iff_ne.mpr same, Bool.false_eq_true, if_false, ih]
      constructor
      · exact .there same
      · intro found
        cases found with
        | here => exact (same rfl).elim
        | there _ found => exact found

theorem lookup_index (entries : List (String × α)) (name : String) :
    lookup? entries name = ((entries.map Prod.fst).idxOf? name).bind (fun index => (entries.map Prod.snd)[index]?) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨other, value⟩ := entry
    rw [lookup_cons]
    simp only [List.map_cons, List.idxOf?_cons]
    by_cases same : other == name
    · simp [same]
    · cases selected : (rest.map Prod.fst).idxOf? name <;> simp [same, ih, selected]

theorem lookup_index_of_names (entries : List (String × α)) (names : List String) (name : String)
    (same : entries.map Prod.fst = names) :
    lookup? entries name = (names.idxOf? name).bind (fun index => (entries.map Prod.snd)[index]?) := by
  rw [lookup_index, same]

theorem lookup_push (entries bindings : List (String × α)) (name : String) :
    lookup? (bindings.reverse ++ entries) name =
      (((bindings.map Prod.fst).reverse ++ entries.map Prod.fst).idxOf? name).bind
        (fun index => ((bindings.map Prod.snd).reverse ++ entries.map Prod.snd)[index]?) := by
  rw [lookup_index]
  simp only [List.map_append, List.map_reverse]

theorem nearest_wins (entries : List (String × α)) (name : String) (value : α) :
    lookup? ((name, value) :: entries) name = some value := by simp [lookup_cons]

theorem absent_iff (entries : List (String × α)) (name : String) :
    lookup? entries name = none ↔ name ∉ entries.map Prod.fst := by
  induction entries with
  | nil => simp [lookup?]
  | cons entry rest ih =>
    obtain ⟨other, value⟩ := entry
    by_cases same : other = name
    · subst other; simp [lookup_cons]
    · simp [lookup_cons, same, Ne.symm same, ih]

#print axioms lookup_iff
#print axioms lookup_index
#print axioms lookup_push
#print axioms nearest_wins
#print axioms absent_iff

end List.NamedEnvironment
