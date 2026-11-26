import Mettapedia.OSLF.MeTTaIL.PatternCoded
import Mettapedia.OSLF.MeTTaIL.Match

/-!
# Binding operations computed on codes

Bindings are lists of names paired with patterns, coded as such. Looking a name
up, merging two binding lists (`mergeBindings`), the free names of a pattern,
eliminating a bound level (`instantiateBVarAt`) and applying bindings to a
pattern (`applyBindings`) are computable on codes.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EngineCoded

open Mettapedia.Computability
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.PatternCode

open CodeComputable

/-- Equality of strings as a Boolean test is computable on codes. -/
theorem stringBEq : CodeComputable₂ fun left right : String => left == right :=
  CodeComputable'.stringEq.of_eq fun input => Bool.eq_iff_iff.mpr (by simp)

/-- Equality of patterns as a Boolean test is computable on codes. -/
theorem patternBEq : CodeComputable₂ fun left right : Pattern => left == right :=
  CodeComputable'.patternEq.of_eq fun input => Bool.eq_iff_iff.mpr (by simp)

/-! ## Monadic folds in `Option` -/

private theorem foldl_bind_none {α β : Type} (f : β → α → Option β) :
    ∀ l : List α, l.foldl (fun acc x => acc.bind fun a => f a x) none = none
  | [] => rfl
  | _ :: xs => foldl_bind_none f xs

/-- A fold in the `Option` monad is an ordinary fold that stops at the first failure. -/
theorem foldlM_option {α β : Type} (f : β → α → Option β) :
    ∀ (l : List α) (init : β), l.foldlM f init = l.foldl (fun acc x => acc.bind fun a => f a x) (some init)
  | [], _ => rfl
  | x :: xs, init => by
      rw [List.foldlM_cons, List.foldl_cons, Option.bind_some]
      cases f init x with
      | none => exact (foldl_bind_none f xs).symm
      | some a => exact foldlM_option f xs a

/-! ## Merging bindings -/

/-- Merge one entry into accumulated bindings. -/
def mergeEntry (acc : Bindings) (entry : String × Pattern) : Option Bindings :=
  match acc.find? (·.1 == entry.1) with
  | none => some (entry :: acc)
  | some found => if found.2 == entry.2 then some acc else none

theorem mergeBindings_eq (first second : Bindings) :
    mergeBindings first second =
      second.foldl (fun acc entry => acc.bind fun a => mergeEntry a entry) (some first) := by
  unfold mergeBindings
  rw [foldlM_option]
  congr 1
  funext acc entry
  congr 1
  funext a
  obtain ⟨name, value⟩ := entry
  unfold mergeEntry
  dsimp only
  cases a.find? (·.1 == name) with
  | none => rfl
  | some found => obtain ⟨_, existing⟩ := found; rfl

theorem mergeEntry_computable : CodeComputable₂ mergeEntry := by
  have found : CodeComputable fun input : Bindings × (String × Pattern) =>
      input.1.find? (·.1 == input.2.1) :=
    list_find? fst (stringBEq.comp (pair (fst.comp snd) (fst.comp (snd.comp fst))))
  refine (option_casesOn (onNone := fun input : Bindings × (String × Pattern) => some (input.2 :: input.1))
    (onSome := fun input found => if found.2 == input.2.2 then some input.1 else none) found
    (option_some (list_cons snd fst))
    (CodeComputable.ite (patternBEq.comp (pair (snd.comp snd) (snd.comp (snd.comp fst))))
      (option_some (fst.comp fst)) (const none))).of_eq fun input => ?_
  unfold mergeEntry
  cases input.1.find? (·.1 == input.2.1) <;> rfl

/-- **Merging bindings is computable on codes.** -/
theorem mergeBindings_computable : CodeComputable₂ mergeBindings := by
  have step : CodeComputable fun input : (Bindings × Bindings) × Option Bindings × (String × Pattern) =>
      input.2.1.bind fun a => mergeEntry a input.2.2 :=
    (option_casesOn (onNone := fun _ => (none : Option Bindings))
      (onSome := fun input a => mergeEntry a input.2.2) (fst.comp snd) (const none)
      (mergeEntry_computable.comp (pair snd (snd.comp (snd.comp fst))))).of_eq fun input => by
        cases input.2.1 <;> rfl
  exact (list_foldl snd (option_some fst) step).of_eq fun input => (mergeBindings_eq input.1 input.2).symm

/-! ## Looking names up -/

theorem lookup_computable : CodeComputable₂ Bindings.lookup :=
  (option_map (list_find? fst (stringBEq.comp (pair (fst.comp snd) (snd.comp fst))))
    (snd.comp snd)).of_eq fun _ => rfl

end Mettapedia.OSLF.MeTTaIL.EngineCoded

#print axioms Mettapedia.OSLF.MeTTaIL.EngineCoded.mergeBindings_computable
#print axioms Mettapedia.OSLF.MeTTaIL.EngineCoded.lookup_computable
