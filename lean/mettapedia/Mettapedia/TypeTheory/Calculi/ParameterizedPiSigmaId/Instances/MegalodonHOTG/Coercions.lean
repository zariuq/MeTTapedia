import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.MegalodonHOTG.SetTheory

/-!
# Typing and membership, in the judgment

The constants of set theory over the tower inside the sets (`MegalodonHOTG.SetTheory`) include three
coercions: `elem A a` takes a term `a` of a type `A` that is a set to a set, `member A a` is a
proof that this set is a member of `A`, and `the A x p` takes a set `x` with a proof `p` that
it is a member of `A` to a term of `A`. `MegalodonHOTG.SetTheory` gives their model. This file is
about what the judgment derives from their two equations, in every package over the set
theory that contains the steps of the family.

* `the A x p` is a term of `A` (`the_typed`).
* **The two round trips** (`elem_the_rule`, `the_elem_rule`): a set with a proof of membership,
  taken as a term and back as a set, is the set; a term, taken as a set and back as a term
  with any proof of the membership of that set, is the term.
* **The term does not depend on the proof** (`the_proof_independent`): for two proofs `p` and
  `q` that `x` is a member of `A`, `the A x p` and `the A x q` are equal terms of `A`. This is
  derived from the two round trips; no rule says that two proofs are equal.

Positive example: the universe at a level, taken as a set and back as a term of the universe
at the next level with the proof `member` gives, is the universe at the level
(`universe_roundTrip`). Negative example: the empty set, as a type, has no closed term in the
package of set theory (`empty_no_term`), relative to cofinally many inaccessible cardinals in
two universes; so no closed proof of a membership in the empty set is turned into a term by
`the`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace MegalodonHOTG

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding

universe u

variable {L : Type} [LevelOrder L]

/-- **A package computes as the set theory** when it contains the steps of the family of the
constants of set theory, with their premises. -/
abbrev ComputesAsSetTheory {R' : Rules (Head L)} (Q : ChurchRules R') : Prop :=
  StepsWithin (familyChurch (rules L) (setDecls L) (setEquations L)) Q

/-- The package of the family computes as the set theory. -/
theorem setTheory_computes : ComputesAsSetTheory (setTheory L) :=
  StepsWithin.sum_right (bare L) (familyChurch (rules L) (setDecls L) (setEquations L))

omit [LevelOrder L] in
/-- The first round trip is an equation of the family. -/
theorem elemThe_member : elemThe L ∈ setEquations L :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

omit [LevelOrder L] in
/-- The second round trip is an equation of the family. -/
theorem theElem_member : theElem L ∈ setEquations L :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self)))

section Judgment

variable {R' : Rules (Head L)} {Q : ChurchRules R'} {n : Nat} {Γ : CCtx (Head L) n}

omit [LevelOrder L] in
/-- The type of `the A` at a set: the proofs that the set is a member of `A` give terms of
`A`. -/
theorem theApp_type (A y : CTm (Head L) n) :
    CTm.inst0 y (.pi (cHolds (cIn (.var 0) (A.rename Fin.succ)))
        ((A.rename Fin.succ).rename Fin.succ)) =
      .pi (cHolds (cIn y A)) (A.rename Fin.succ) := by
  have back : CTm.inst0 y (CTm.rename Fin.succ A) = A := CTm.inst0_rename_wk y A
  have lifted : CTm.subst (CTm.liftSub (CTm.subst0 y))
      (CTm.rename Fin.succ (CTm.rename Fin.succ A)) = CTm.rename Fin.succ A :=
    (CTm.subst_liftSub_wk (CTm.subst0 y) (CTm.rename Fin.succ A)).trans
      (congrArg (CTm.rename Fin.succ) back)
  show CTm.pi (cHolds (cIn y (CTm.inst0 y (CTm.rename Fin.succ A))))
    (CTm.subst (CTm.liftSub (CTm.subst0 y)) (CTm.rename Fin.succ (CTm.rename Fin.succ A))) = _
  rw [back, lifted]

variable (covers : OverSetTheory Q)

include covers in
/-- `the A` takes a set and a proof that it is a member of `A` to a term of `A`. -/
theorem theApp_typed {A : CTm (Head L) n} (hA : CTyped Q Γ A allSets) :
    CTyped Q Γ (.app (.const theN) A)
      (.pi allSets (.pi (cHolds (cIn (.var 0) (A.rename Fin.succ)))
        ((A.rename Fin.succ).rename Fin.succ))) :=
  .appElim (B := .pi allSets (.pi (cHolds (cIn (.var 0) (.var 1))) (.var 2)))
    (theConst_typed covers) hA

include covers in
/-- **A set proved to be a member of a type that is a set is a term of the type.** -/
theorem the_typed {A x p : CTm (Head L) n} (hA : CTyped Q Γ A allSets)
    (hx : CTyped Q Γ x allSets) (hp : CTyped Q Γ p (cHolds (cIn x A))) :
    CTyped Q Γ (cThe A x p) A := by
  have second := CDerivable.appElim (theApp_typed covers hA) hx
  rw [theApp_type] at second
  have third := CDerivable.appElim second hp
  have back : CTm.inst0 p (CTm.rename Fin.succ A) = A := CTm.inst0_rename_wk p A
  rw [back] at third
  exact third

variable (computes : ComputesAsSetTheory Q)

include covers computes in
/-- **A set with a proof of membership, taken as a term and back as a set, is the set.** -/
theorem elem_the_rule {A x p : CTm (Head L) n} (hA : CTyped Q Γ A allSets)
    (hx : CTyped Q Γ x allSets) (hp : CTyped Q Γ p (cHolds (cIn x A))) :
    CEqual Q Γ (cElem A (cThe A x p)) x allSets :=
  have typed : CSubstMor Q (elemThe L).telescope Γ
      (fun j : Fin 3 => match j with
        | ⟨0, _⟩ => p
        | ⟨1, _⟩ => x
        | ⟨2, _⟩ => A) :=
    fun j => match j with
      | ⟨0, _⟩ => hp
      | ⟨1, _⟩ => hx
      | ⟨2, _⟩ => hA
  family_equation_holds (rules L) computes elemThe_member _ typed
    (elem_typed covers hA (the_typed covers hA hx hp)) hx

include covers computes in
/-- **A term of a type that is a set, taken as a set and back as a term, is the term**, with
any proof that the set is a member of the type. -/
theorem the_elem_rule {A a q : CTm (Head L) n} (hA : CTyped Q Γ A allSets)
    (ha : CTyped Q Γ a A) (hq : CTyped Q Γ q (cHolds (cIn (cElem A a) A))) :
    CEqual Q Γ (cThe A (cElem A a) q) a A :=
  have typed : CSubstMor Q (theElem L).telescope Γ
      (fun j : Fin 3 => match j with
        | ⟨0, _⟩ => q
        | ⟨1, _⟩ => a
        | ⟨2, _⟩ => A) :=
    fun j => match j with
      | ⟨0, _⟩ => hq
      | ⟨1, _⟩ => ha
      | ⟨2, _⟩ => hA
  family_equation_holds (rules L) computes theElem_member _ typed
    (the_typed covers hA (elem_typed covers hA ha) hq) ha

include covers computes in
/-- **The term a set gives does not depend on the proof of its membership**: for two proofs
that `x` is a member of `A`, `the A x p` and `the A x q` are equal terms of `A`. Derived from
the two round trips. -/
theorem the_proof_independent {A x p q : CTm (Head L) n} (hA : CTyped Q Γ A allSets)
    (hx : CTyped Q Γ x allSets) (hp : CTyped Q Γ p (cHolds (cIn x A)))
    (hq : CTyped Q Γ q (cHolds (cIn x A))) :
    CEqual Q Γ (cThe A x p) (cThe A x q) A := by
  have term : CTyped Q Γ (cThe A x p) A := the_typed covers hA hx hp
  have asSet : CTyped Q Γ (cElem A (cThe A x p)) allSets := elem_typed covers hA term
  have back : CEqual Q Γ (cElem A (cThe A x p)) x allSets :=
    elem_the_rule covers computes hA hx hp
  -- the two statements of membership are equal propositions, so their proofs are the same type
  have atSet : CEqual Q Γ (.app (.const inN) x) (.app (.const inN) (cElem A (cThe A x p)))
      (.pi allSets cProp) :=
    .appCong (B := .pi allSets cProp) (.refl (in_typed covers)) (.symm back)
  have statement : CEqual Q Γ (cIn x A) (cIn (cElem A (cThe A x p)) A) cProp :=
    .appCong (B := cProp) atSet (.refl hA)
  have proofs : CEqual Q Γ (cHolds (cIn x A)) (cHolds (cIn (cElem A (cThe A x p)) A)) U0 :=
    .appCong (B := U0) (.refl (holds_typed covers)) statement
  have hq' : CTyped Q Γ q (cHolds (cIn (cElem A (cThe A x p)) A)) :=
    .conv hq proofs (covers.contains.isUniverse (.sort _))
  -- the second round trip at the term `the A x p`
  have first : CEqual Q Γ (cThe A (cElem A (cThe A x p)) q) (cThe A x p) A :=
    the_elem_rule covers computes hA term hq'
  -- congruence in the set
  have function : CEqual Q Γ (.app (.app (.const theN) A) (cElem A (cThe A x p)))
      (.app (.app (.const theN) A) x)
      (.pi (cHolds (cIn (cElem A (cThe A x p)) A)) (A.rename Fin.succ)) := by
    have congruence := CDerivable.appCong (.refl (theApp_typed covers hA)) back
    rw [theApp_type] at congruence
    exact congruence
  have second : CEqual Q Γ (cThe A (cElem A (cThe A x p)) q) (cThe A x q) A := by
    have congruence := CDerivable.appCong function (.refl hq')
    have same : CTm.inst0 q (CTm.rename Fin.succ A) = A := CTm.inst0_rename_wk q A
    rw [same] at congruence
    exact congruence
  exact .trans (.symm first) second

include covers computes in
/-- Positive example: **the universe at a level, taken as a set and back as a term of the
universe at the next level, is the universe at the level.** -/
theorem universe_roundTrip (d : L) :
    CEqual Q Γ
      (cThe (universeAt (LevelOrder.succ d))
        (cElem (universeAt (LevelOrder.succ d)) (universeAt d))
        (cMember (universeAt (LevelOrder.succ d)) (universeAt d)))
      (universeAt d) (universeAt (LevelOrder.succ d)) :=
  the_elem_rule covers computes (universe_isSet covers.contains _)
    (universe_typed covers.contains d) (universe_member covers d)

end Judgment

/-! ## What has no term -/

section Refused

open ZFSetUniverseClosure (CofinalInaccessibles univOf)
open ZFSetUniverseLift (univOf_mem_carrierCode)

variable (small : CofinalInaccessibles.{u}) (large : CofinalInaccessibles.{u + 1})

include small large in
/-- Negative example: **the empty set, as a type, has no closed term** in the package of set
theory, relative to cofinally many inaccessible cardinals in two universes. So no closed
proof of a membership in the empty set is turned into a term by `the`. -/
theorem empty_no_term (t : CTm (Head L) 0) : ¬ CTyped (setTheory L) .nil t cEmpty := by
  have model := lowerSets_setTheory_setModel (L := L) small large (fun _ => LevelOrder.bot)
    (empty_mem_universeSet large ZFSet.omega (LevelOrder.bot : L)) (fun _ => ∅)
  refine CDerivable.no_closed_inhabitant model (fun z inside => ?_) t
  exact ZFSet.notMem_empty z inside

end Refused

end MegalodonHOTG
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
