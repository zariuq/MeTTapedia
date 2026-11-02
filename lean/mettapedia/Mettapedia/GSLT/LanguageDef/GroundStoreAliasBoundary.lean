import Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

/-!
# Ground bindings cannot represent an unresolved alias

The existing ground store denotes its total completions under `Store.LE`.
An equation between two distinct names admits every equal pair of values.
With at least two possible values, no ground store has exactly that set of
completions: leaving both names unbound also permits unequal values, while
fixing either name prematurely rejects a permitted equal pair.

This is a representation boundary. It neither adds an evaluator nor chooses
an open-term unification policy.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

variable {Name Value : Type}

/-- A total assignment is a completion precisely when it retains every
binding already recorded by the existing ground-store information order. -/
def Store.CompletedBy (store : Store Name Value) (assignment : Name → Value) : Prop :=
  Store.LE store (fun name => some (assignment name))

theorem Store.completedBy_iff (store : Store Name Value) (assignment : Name → Value) :
    store.CompletedBy assignment ↔ ∀ name value, store name = some value → assignment name = value := by
  simp only [Store.CompletedBy, Store.LE, Option.some.injEq]

/-- Two distinct common values force every existing ground binding to be
absent. They do not express correlation between otherwise unknown names. -/
theorem Store.empty_of_two_constant_completions (store : Store Name Value)
    (first second : Value) (different : first ≠ second)
    (firstAllowed : store.CompletedBy (fun _ => first))
    (secondAllowed : store.CompletedBy (fun _ => second)) :
    ∀ name, store name = none := by
  intro name
  cases present : store name with
  | none => rfl
  | some value =>
    have one := (store.completedBy_iff _).mp firstAllowed name value present
    have two := (store.completedBy_iff _).mp secondAllowed name value present
    exact False.elim (different (one.trans two.symm))

/-- A single ground store cannot preserve exactly the joint possibilities
of an open equality between distinct names. -/
theorem Store.no_open_alias [DecidableEq Name] (left right : Name)
    (distinct : left ≠ right) (first second : Value) (different : first ≠ second) :
    ¬ ∃ store : Store Name Value, ∀ assignment,
      store.CompletedBy assignment ↔ assignment left = assignment right := by
  rintro ⟨store, exactModels⟩
  have empty := store.empty_of_two_constant_completions first second different
    ((exactModels (fun _ => first)).mpr rfl) ((exactModels (fun _ => second)).mpr rfl)
  let separating : Name → Value := Function.update (fun _ => first) right second
  have permitted : store.CompletedBy separating := by
    apply (store.completedBy_iff _).mpr
    intro name value present
    rw [empty name] at present
    cases present
  have equal := (exactModels separating).mp permitted
  have impossible : first = second := by
    simpa [separating, Function.update, distinct] using equal
  exact different impossible

end Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
