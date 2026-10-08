import Mettapedia.GSLT.LanguageDef.ScopePolicies.StraightLine

/-!
# Straight-line authored text under lexical fresh, and the language definition

The fragment of `ScopePolicies.StraightLine` is what lexical fresh elaborates
straight-line authored text to.

* `straightSrc` — authored text: `(let $y₁ s₁ (let $y₂ s₂ … atom))`, each
  `let` without a crossing set, the atom a symbol or a name.
* `elabLFFormAt_straight` — lexical fresh, in the identity model, elaborates
  it to the straight-line program `straightOf`: the `let` at depth `i`
  introduces the slot of its spelling at its own site.
* `straightOf_fresh` — every slot of that program is new where it is bound:
  two `let`s have two sites, even when they spell one name.  Shadowing
  allocates; it does not refine.

Hence `lexicalFresh_straight_agreement`: on straight-line authored text, the
lexical-fresh policy (elaborate, then run, in the identity model) and the
language definition `lexicalFreshCore` (reduce the configuration of the empty
store and the encoded program until no rule applies) reach the same store and
the same atom.

`shadowing_two_slots` is the instance `(let $y s (let $y s' $y))`: two slots,
both bound in the final store, the answer the inner one.  Rule M would refine
one slot here and, for two different symbols, give no answer (row 23c of the
corpus); the definition is of the lexical-fresh core.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ScopePolicies

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open LexicalFreshCore

universe u v

/-- The last term of a straight-line text: a symbol or a name. -/
inductive Atom (S : Type u) (X : Type v) where
  | sym (s : S)
  | name (x : X)

variable {S : Type u} {X : Type v}

/-- An atom, as authored text. -/
def Atom.toSrc : Atom S X → Src S X
  | .sym s => .sym s
  | .name x => .sv x

/-- **Straight-line authored text**: `let`s of symbols into names, with no
crossing set, around an atom. -/
def straightSrc : List (X × S) → Atom S X → Src S X
  | [], atom => atom.toSrc
  | (y, s) :: rest, atom => .letS (.sv y) (.sym s) (straightSrc rest atom) none

variable [DecidableEq X]

/-- The straight-line program that lexical fresh elaborates the text to: the
`let` at position `pos` introduces the slot of its spelling at that site. -/
def straightOf (env : IEnv X) (fr pos : Owner) : List (X × S) → Atom S X → Straight S X
  | [], .sym s => .sym s
  | [], .name x => .slot (env x)
  | (y, s) :: rest, atom =>
      .bind ⟨y, fr, pos, .pat⟩ s
        (straightOf (env.set [y] fun spelling => ⟨spelling, fr, pos, .pat⟩) fr (pos ++ [2]) rest
          atom)

/-- **Lexical fresh elaborates straight-line text to that program**, with no
name in force. -/
theorem elabLFId_straight : ∀ (bindings : List (X × S)) (atom : Atom S X) (env : IEnv X)
    (pv : X → Owner) (fr pos : Owner),
    elabLFId [] env pv fr pos (straightSrc bindings atom) =
      (straightOf env fr pos bindings atom).toTm
  | [], .sym _, _, _, _, _ => rfl
  | [], .name _, _, _, _, _ => rfl
  | (y, s) :: rest, atom, env, pv, fr, pos => by
      have introduced : lfIntro none (.sv y : Src S X) [] = [y] := by
        simp [lfIntro, crossOwn, Src.patNames]
      have inForce : crossIn none [y] ([] : List X) = [] := by simp [crossIn]
      simp only [straightSrc, elabLFId, introduced, inForce, straightOf, Straight.toTm]
      rw [elabLFId_straight rest atom]
      simp [IEnv.set]

/-- At the root of a query. -/
theorem elabLFFormAt_straight (bindings : List (X × S)) (atom : Atom S X) :
    elabLFFormAt [] (straightSrc bindings atom) =
      (straightOf (lfRootEnv []) [] [] bindings atom).toTm :=
  elabLFId_straight bindings atom _ _ _ _

/-- **Every slot is new where it is bound**: the sites of the `let`s are
pairwise different, and longer than every site in the store. -/
theorem straightOf_fresh : ∀ (bindings : List (X × S)) (atom : Atom S X) (env : IEnv X)
    (fr pos : Owner) (store : List (SlotId X × S)),
    (∀ entry ∈ store, entry.1.site.length < pos.length) →
      (straightOf env fr pos bindings atom).Fresh store
  | [], .sym _, _, _, _, _, _ => trivial
  | [], .name _, _, _, _, _, _ => trivial
  | (y, s) :: rest, atom, env, fr, pos, store, shorter => by
      refine ⟨?_, straightOf_fresh rest atom _ fr (pos ++ [2]) _ ?_⟩
      · intro member
        obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp member
        have length := shorter entry entryMember
        rw [same] at length
        exact Nat.lt_irrefl _ length
      · intro entry entryMember
        rcases List.mem_cons.mp entryMember with rfl | inStore
        · simp
        · have length := shorter entry inStore
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega

/-- **Agreement on straight-line authored text.**  The lexical-fresh policy,
in the identity model, and the language definition reach the same store and
the same atom: the evaluator returns one result, and the definition reduces the
configuration of the empty store and the encoded program to the configuration
of that store and that atom, which has no step. -/
theorem lexicalFresh_straight_agreement [DecidableEq S] {enc : SlotId X → String}
    (injective : Function.Injective enc) (code : S → ℕ) (bindings : List (X × S))
    (atom : Atom S X) (d : Disc) (prog : S → Option (Tm S (BId X))) (n : ℕ) (π : Path) :
    run d prog (n + 1 + (straightOf (lfRootEnv []) [] [] bindings atom).length) π Store.empty
        (elabLFFormAt [] (straightSrc bindings atom)) =
      some [((straightOf (lfRootEnv []) [] [] bindings atom).final.toTm,
        storeOf ((straightOf (lfRootEnv []) [] [] bindings atom).extend []))] ∧
    Relation.ReflTransGen (Step (engineBasePremises RelationEnv.empty) lexicalFreshCore)
      (cfg emptyStore ((straightOf (lfRootEnv []) [] [] bindings atom).toPattern enc code))
      (cfg (storePattern enc code ((straightOf (lfRootEnv []) [] [] bindings atom).extend []))
        ((straightOf (lfRootEnv []) [] [] bindings atom).final.toPattern enc code)) ∧
    ∀ target, ¬ Step (engineBasePremises RelationEnv.empty) lexicalFreshCore
      (cfg (storePattern enc code ((straightOf (lfRootEnv []) [] [] bindings atom).extend []))
        ((straightOf (lfRootEnv []) [] [] bindings atom).final.toPattern enc code)) target := by
  have fresh : (straightOf (lfRootEnv []) [] [] bindings atom).Fresh ([] : List (SlotId X × S)) :=
    straightOf_fresh bindings atom _ _ _ _ (fun _ member => absurd member List.not_mem_nil)
  rw [elabLFFormAt_straight]
  exact straight_agreement injective code _ [] fresh d prog n π

/-- **Shadowing allocates.**  `(let $y s (let $y s' $y))` elaborates, under
lexical fresh, to two `let`s of two slots: the outer at the root, the inner at
the site `[2]`; the atom is the inner slot. -/
theorem shadowing_two_slots (y : X) (s s' : S) :
    straightOf (lfRootEnv []) [] [] [(y, s), (y, s')] (.name y : Atom S X) =
      .bind ⟨y, [], [], .pat⟩ s (.bind ⟨y, [], [2], .pat⟩ s' (.slot ⟨y, [], [2], .pat⟩)) := by
  simp [straightOf, IEnv.set]

omit [DecidableEq X] in
/-- Negative, on the same text: the two slots are different, so the inner
`let` does not refine the outer one. -/
theorem shadowing_slots_differ (y : X) :
    (⟨y, [], [], .pat⟩ : SlotId X) ≠ ⟨y, [], [2], .pat⟩ := by
  intro same
  have sites := congrArg SlotId.site same
  cases sites

#print axioms elabLFFormAt_straight
#print axioms straightOf_fresh
#print axioms lexicalFresh_straight_agreement
#print axioms shadowing_two_slots

end Mettapedia.GSLT.LanguageDef.ScopePolicies
