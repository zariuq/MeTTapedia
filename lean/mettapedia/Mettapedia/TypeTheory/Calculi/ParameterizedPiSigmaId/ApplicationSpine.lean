import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
import Mathlib.Data.List.Forall2

/-!
# Constant-headed application spines

The constructor stores arguments outermost first. Head and arity are
observations of that spine; comparison of fixed spines also retains the
ordered component relation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.ApplicationSpine

variable {Head : Type} {n : Nat}

def constant (name : DeclName) : List (Tm Head n) → Tm Head n
  | [] => .const name
  | argument :: rest => .app (constant name rest) argument

/-- The head of a constant spine and the number of applied arguments. -/
def headArity : Tm Head n → Option (DeclName × Nat)
  | .const name => some (name, 0)
  | .app function _ => (headArity function).map (fun info => (info.1, info.2 + 1))
  | _ => none

@[simp] theorem headArity_constant (name : DeclName) (arguments : List (Tm Head n)) :
    headArity (constant name arguments) = some (name, arguments.length) := by
  induction arguments with
  | nil => rfl
  | cons _ _ ih => simp only [constant, headArity, ih, Option.map_some, List.length_cons]

theorem constant_injective (name : DeclName) : Function.Injective (constant (Head := Head) (n := n) name) := by
  intro first
  induction first with
  | nil =>
      intro second same
      cases second with
      | nil => rfl
      | cons _ _ => cases same
  | cons argument rest induction =>
      intro second same
      cases second with
      | nil => cases same
      | cons argument' rest' =>
          obtain ⟨tail, head⟩ := Tm.app.inj same
          exact congrArg₂ List.cons head (induction tail)

theorem excludes_at_smaller_arity {name root : DeclName} {small large arity : Nat}
    (ordered : small ≤ large) (excluded : name ≠ root ∨ large < arity) :
    name ≠ root ∨ small < arity :=
  excluded.imp_right (Nat.lt_of_le_of_lt ordered)

theorem excludes_root {name root : DeclName} {arguments : List (Tm Head n)}
    {source : Tm Head n} {arity : Nat}
    (excluded : name ≠ root ∨ arguments.length < arity)
    (observed : headArity source = some (root, arity)) :
    source ≠ constant name arguments := by
  intro same
  rw [same, headArity_constant] at observed
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj observed)
  exact excluded.elim (fun different => different rfl) (Nat.lt_irrefl _)

theorem excludes_headless {name : DeclName} {arguments : List (Tm Head n)} {source : Tm Head n}
    (observed : headArity source = none) :
    source ≠ constant name arguments := by
  intro same
  rw [same, headArity_constant] at observed
  cases observed

/-- Once the target is fixed, compare its ordered arguments with those of
the source through the exact spine constructor. -/
theorem related_of_fixed {step : Tm Head n → Tm Head n → Prop} {name : DeclName}
    {source target : List (Tm Head n)}
    (view : ∃ reduct, constant name target = constant name reduct ∧
      List.Forall₂ step source reduct) :
    List.Forall₂ step source target := by
  obtain ⟨_, same, arguments⟩ := view
  exact (constant_injective name same).symm ▸ arguments

section Controls

private def sample (name : DeclName) : Tm Unit 2 :=
  constant name [.var 1, .var 0, .var 1]

example (name : DeclName) : headArity (sample name) = some (name, 3) := rfl

example (name : DeclName) :
    sample name ≠ constant name ([.var 0, .var 1, .var 1] : List (Tm Unit 2)) :=
  fun equal => by
    have arguments := constant_injective name equal
    cases arguments

example (name : DeclName) :
    sample name ≠ constant name ([.var 1, .var 0] : List (Tm Unit 2)) :=
  excludes_root (arity := 3) (Or.inr (show 2 < 3 by decide)) rfl

end Controls

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.ApplicationSpine
