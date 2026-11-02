import Mettapedia.OSLF.Syntax.BindingArgumentSlots
import Mettapedia.OSLF.Syntax.ContextualSupportSubstitution

/-!
# Support bounds can be checked field by field

Lookup exposes an existing field with its binder prefix. A bound on the
argument list is equivalent to a bound on every typed field, and tabulation
preserves the bounds supplied at those positions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ArgumentSlots

open ContextualFamily

variable {S : Signature} {V : Type} {source : V → MetaArity S}

theorem support_get_subset : ∀ {arities : List (MetaArity S)} {Γ : Ctx S}
    (arguments : Args (signature S source) arities Γ) (field : MetaArity S)
    (position : Var arities field) (identity : V),
    identity ∈ support (get arguments field position) → identity ∈ supportArgs arguments
  | _, _, .nil, _, position, _, _ => nomatch position
  | _, _, .cons _ _, _, .zero, _, member => List.mem_append_left _ member
  | _, _, .cons _ tail, field, .succ position, identity, member =>
      List.mem_append_right _ (support_get_subset tail field position identity member)

theorem boundedArgs_of_get (allowed : V → Prop) :
    ∀ {arities : List (MetaArity S)} {Γ : Ctx S}
      (arguments : Args (signature S source) arities Γ),
      (∀ field position, Bounded allowed (get arguments field position)) → BoundedArgs allowed arguments
  | _, _, .nil, _ => fun _ member => False.elim (List.not_mem_nil member)
  | _, _, .cons head tail, fields => by
      intro identity member
      rcases List.mem_append.mp member with first | rest
      · exact fields _ .zero identity first
      · exact boundedArgs_of_get allowed tail (fun field position => fields field (.succ position)) identity rest

theorem boundedArgs_iff_get (allowed : V → Prop) {arities : List (MetaArity S)} {Γ : Ctx S}
    (arguments : Args (signature S source) arities Γ) :
    BoundedArgs allowed arguments ↔ ∀ field position, Bounded allowed (get arguments field position) := by
  constructor
  · intro bound field position identity present
    exact bound identity (support_get_subset arguments field position identity present)
  · exact boundedArgs_of_get allowed arguments

theorem bounded_tabulate (allowed : V → Prop) {Γ : Ctx S} (arities : List (MetaArity S))
    (fields : (field : MetaArity S) → Var arities field → Term (signature S source) (field.1 ++ Γ) field.2)
    (bounded : ∀ field position, Bounded allowed (fields field position)) :
    BoundedArgs allowed (tabulate (S := signature S source) arities fields) := by
  apply boundedArgs_of_get allowed
  intro field position
  rw [get_tabulate]
  exact bounded field position

end Mettapedia.OSLF.Binding.ArgumentSlots
