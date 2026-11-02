import Mettapedia.OSLF.Syntax.ContextualFamily

/-!
# Typed positions in existing binding argument lists

A field position records its binder prefix and result sort. Lookup and
tabulation operate on the existing `Args`; no untyped list or second term
representation is introduced. Instantiation and renaming commute with lookup.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ArgumentSlots

variable {S : Signature}

abbrev Slot (arities : List (MetaArity S)) :=
  (field : MetaArity S) × Var arities field

def get : {arities : List (MetaArity S)} → {Γ : Ctx S} → Args S arities Γ →
    (field : MetaArity S) → Var arities field → Term S (field.1 ++ Γ) field.2
  | _, _, .nil, _, position => nomatch position
  | _, _, .cons head _, _, .zero => head
  | _, _, .cons _ rest, _, .succ position => get rest _ position

def tabulate {Γ : Ctx S} : (arities : List (MetaArity S)) →
    ((field : MetaArity S) → Var arities field → Term S (field.1 ++ Γ) field.2) → Args S arities Γ
  | [], _ => .nil
  | field :: rest, values => .cons (values field .zero)
      (tabulate rest (fun other position => values other (.succ position)))

theorem get_tabulate {Γ : Ctx S} : ∀ (arities : List (MetaArity S))
    (values : (field : MetaArity S) → Var arities field → Term S (field.1 ++ Γ) field.2)
    (field : MetaArity S) (position : Var arities field),
    get (tabulate arities values) field position = values field position
  | [], _, _, position => nomatch position
  | _ :: _, _, _, .zero => rfl
  | _ :: rest, values, field, .succ position =>
      get_tabulate rest (fun other index => values other (.succ index)) field position

theorem tabulate_get {Γ : Ctx S} : ∀ {arities : List (MetaArity S)} (arguments : Args S arities Γ),
    tabulate arities (get arguments) = arguments
  | _, .nil => rfl
  | _, .cons head rest => congrArg (Args.cons head) (tabulate_get rest)

theorem ext {Γ : Ctx S} {arities : List (MetaArity S)} (first second : Args S arities Γ)
    (same : ∀ field position, get first field position = get second field position) : first = second := by
  rw [← tabulate_get first, ← tabulate_get second]
  exact congrArg (tabulate arities) (funext fun field => funext fun position => same field position)

theorem get_rename {Γ Δ : Ctx S} (rho : Ren S Γ Δ) :
    ∀ {arities : List (MetaArity S)} (arguments : Args S arities Γ)
      (field : MetaArity S) (position : Var arities field),
    get (renameArgs rho arguments) field position = rename (liftRen rho field.1) (get arguments field position)
  | _, .nil, _, position => nomatch position
  | _, .cons _ _, _, .zero => rfl
  | _, .cons _ rest, field, .succ position => get_rename rho rest field position

theorem get_instantiate {V W : Type} {source : V → MetaArity S} {target : W → MetaArity S}
    (assignment : ContextualFamily.Assignment source target) :
    ∀ {arities : List (MetaArity S)} {Γ : Ctx S}
      (arguments : Args (ContextualFamily.signature S source) arities Γ)
      (field : MetaArity S) (position : Var arities field),
    get (ContextualFamily.instantiateArgs assignment arguments) field position =
      ContextualFamily.instantiate assignment (get arguments field position)
  | _, _, .nil, _, position => nomatch position
  | _, _, .cons _ _, _, .zero => rfl
  | _, _, .cons _ rest, field, .succ position => get_instantiate assignment rest field position

/-- A variable-only occurrence spine cannot create a rigid root. Its image
therefore reveals the same root in the original term, without an injectivity
assumption on the variable map. -/
theorem rename_eq_operator {Γ Δ : Ctx S} {sort : S.Srt} (rho : Ren S Γ Δ)
    (term : Term S Γ sort) (operator : S.Op sort) (arguments : Args S (S.arity operator) Δ)
    (same : rename rho term = Term.op operator arguments) :
    ∃ original : Args S (S.arity operator) Γ,
      term = Term.op operator original ∧ renameArgs rho original = arguments := by
  cases term with
  | var _ => cases same
  | op other original =>
      have heads := (Term.op.inj same).1
      subst other
      exact ⟨original, rfl, eq_of_heq (Term.op.inj same).2⟩

end Mettapedia.OSLF.Binding.ArgumentSlots
