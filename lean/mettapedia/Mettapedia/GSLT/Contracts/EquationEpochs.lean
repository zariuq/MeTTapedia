import Mettapedia.TypeTheory.BubbleJoinCongruence
import Mathlib.Data.Finset.Union

/-!
# Ground equation epochs and exact bucket reuse

A branch carries declared equations and its own ledger of tells. More
tells can merge old classes but cannot split them. The merge map is
determined by the common raw terms, not by a choice of representatives.

A one-bucket read in an older table remains exact precisely when every
current matching row already belonged to that bucket. Otherwise one can
redirect *all* contributing old buckets to the new class. The result
here is a set of physical rows, not a concatenation that pretends to
preserve their order.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.EquationEpochs

open Mettapedia.TypeTheory.BubbleJoinCongruence

universe u v

variable {Term : Type u} {Row : Type v}

/-- Branch-local ground consequences of the declared equations and the
ledger, using the same positional congruence as the language. Directed
runtime transitions are not added to this relation. -/
def epoch (context : CongruenceClosure Term) (declared : Term → Term → Prop)
    (ledger : List (Term × Term)) : Setoid Term :=
  ⟨context.Conv (CongruenceClosure.join declared (fun a b => (a, b) ∈ ledger)),
    Relation.EqvGen.is_equivalence _⟩

def Extends (before after : Setoid Term) : Prop :=
  ∀ ⦃left right⦄, before.r left right → after.r left right

theorem epoch_of_inclusion (context : CongruenceClosure Term) (declared : Term → Term → Prop)
    {first second : List (Term × Term)} (contains : ∀ e ∈ first, e ∈ second) :
    Extends (epoch context declared first) (epoch context declared second) := by
  intro left right known
  apply context.conv_mono ?_ known
  intro a b axiomOrTell
  exact axiomOrTell.imp_right (contains (a, b))

theorem epoch_extends (context : CongruenceClosure Term) (declared : Term → Term → Prop)
    (parent more : List (Term × Term)) :
    Extends (epoch context declared parent) (epoch context declared (parent ++ more)) :=
  epoch_of_inclusion context declared (fun _ member => List.mem_append_left _ member)

variable {before after : Setoid Term}

def advance (grows : Extends before after) : Quotient before → Quotient after :=
  Quotient.lift (Quotient.mk after) (fun _ _ eq => Quotient.sound (s := after) (grows eq))

@[simp] theorem advance_mk (grows : Extends before after) (a : Term) :
    advance grows (Quotient.mk before a) = Quotient.mk after a := rfl

theorem advance_surjective (grows : Extends before after) : Function.Surjective (advance grows) := by
  intro target
  induction target using Quotient.inductionOn with
  | _ term => exact ⟨Quotient.mk before term, rfl⟩

theorem advance_injective_iff (grows : Extends before after) :
    Function.Injective (advance grows) ↔ Extends after before := by
  constructor
  · intro injective a b eq
    exact Quotient.exact (s := before) (injective (Quotient.sound (s := after) eq))
  · intro reflects a b same
    induction a using Quotient.inductionOn with
    | _ a =>
        induction b using Quotient.inductionOn with
        | _ b => exact Quotient.sound (s := before) (reflects (Quotient.exact (s := after) same))

theorem advance_composes {later : Setoid Term} (one : Extends before after)
    (two : Extends after later) (old : Quotient before) :
    advance two (advance one old) = advance (fun _ _ eq => two (one eq)) old := by
  induction old using Quotient.inductionOn with
  | _ term => rfl

section Fork

variable (context : CongruenceClosure Term) (declared : Term → Term → Prop)
  (parent left right : List (Term × Term))

local notation "BaseEq" => epoch context declared parent
local notation "LeftEq" => epoch context declared (parent ++ left)
local notation "RightEq" => epoch context declared (parent ++ right)
local notation "JointEq" => epoch context declared ((parent ++ left) ++ right)

theorem left_to_joint : Extends LeftEq JointEq :=
  epoch_extends context declared (parent ++ left) right

theorem right_to_joint : Extends RightEq JointEq :=
  epoch_of_inclusion context declared (fun _ member =>
    (List.mem_append.mp member).elim
      (fun known => List.mem_append_left _ (List.mem_append_left _ known))
      (List.mem_append_right _))

/-- The joint equation quotient is a pushout at the level of sets:
compatible observations of each child descend to a unique observation
of the joined knowledge. No branch effect is included in that claim. -/
theorem fork_quotient_universal {Answer : Type*}
    (observeLeft : Quotient LeftEq → Answer) (observeRight : Quotient RightEq → Answer)
    (agrees : ∀ base : Quotient BaseEq,
      observeLeft (advance (epoch_extends context declared parent left) base) =
        observeRight (advance (epoch_extends context declared parent right) base)) :
    ∃! observe : Quotient JointEq → Answer,
      (∀ key, observe (advance (left_to_joint context declared parent left right) key) = observeLeft key) ∧
      (∀ key, observe (advance (right_to_joint context declared parent left right) key) = observeRight key) := by
  have rawAgreement (a : Term) :
      observeLeft (Quotient.mk LeftEq a) = observeRight (Quotient.mk RightEq a) :=
    agrees (Quotient.mk BaseEq a)
  have factors {a b : Term} (equiv : (JointEq).r a b) :
      observeLeft (Quotient.mk LeftEq a) = observeLeft (Quotient.mk LeftEq b) := by
    change Relation.EqvGen
      (context.step (CongruenceClosure.join declared (fun a b => (a, b) ∈ (parent ++ left) ++ right))) a b
      at equiv
    induction equiv with
    | rel source target step =>
        have separate :
            context.step (CongruenceClosure.join
              (CongruenceClosure.join declared (fun a b => (a, b) ∈ parent ++ left))
              (CongruenceClosure.join declared (fun a b => (a, b) ∈ parent ++ right))) source target := by
          apply context.mono ?_ step
          intro s t eq
          rcases eq with external | told
          · exact Or.inl (Or.inl external)
          · rcases List.mem_append.mp told with earlier | new
            · exact Or.inl (Or.inr earlier)
            · exact Or.inr (Or.inr (List.mem_append_right _ new))
        rcases context.split separate with one | two
        · exact congrArg observeLeft (Quotient.sound (s := LeftEq) (.rel _ _ one))
        · rw [rawAgreement source, rawAgreement target]
          exact congrArg observeRight (Quotient.sound (s := RightEq) (.rel _ _ two))
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ first second => exact first.trans second
  let observe : Quotient JointEq → Answer :=
    Quotient.lift (fun a => observeLeft (Quotient.mk LeftEq a)) (fun _ _ eq => factors eq)
  refine ⟨observe, ⟨?_, ?_⟩, ?_⟩
  · intro key
    induction key using Quotient.inductionOn with
    | _ a => rfl
  · intro key
    induction key using Quotient.inductionOn with
    | _ a => exact rawAgreement a
  · intro other property
    funext key
    induction key using Quotient.inductionOn with
    | _ a => exact property.1 (Quotient.mk LeftEq a)

end Fork

variable [DecidableEq Row]

noncomputable def bucket (equations : Setoid Term) (label : Row → Term)
    (rows : Finset Row) (key : Quotient equations) : Finset Row := by
  classical
  exact rows.filter (fun row => Quotient.mk equations (label row) = key)

theorem mem_bucket (equations : Setoid Term) (label : Row → Term)
    {rows : Finset Row} {key : Quotient equations} {row : Row} :
    row ∈ bucket equations label rows key ↔
      row ∈ rows ∧ Quotient.mk equations (label row) = key := by
  classical
  exact Finset.mem_filter

/-- This condition is local to the question and the retained rows. It
allows unchanged lookups even when another bucket has merged. -/
theorem old_bucket_exact_iff (grows : Extends before after) (label : Row → Term)
    (rows : Finset Row) (query : Term) :
    bucket before label rows (Quotient.mk before query) =
      bucket after label rows (Quotient.mk after query) ↔
      ∀ row ∈ rows, after.r (label row) query → before.r (label row) query := by
  constructor
  · intro same row present related
    have inCurrent := (mem_bucket after label).mpr
      ⟨present, Quotient.sound (s := after) related⟩
    rw [← same] at inCurrent
    exact Quotient.exact (s := before) ((mem_bucket before label).mp inCurrent).2
  · intro unaffected
    ext row
    simp only [mem_bucket]
    exact ⟨fun ⟨present, same⟩ => ⟨present, congrArg (advance grows) same⟩,
      fun ⟨present, same⟩ => ⟨present, Quotient.sound (s := before)
        (unaffected row present (Quotient.exact (s := after) same))⟩⟩

/-- Reuse the old buckets by routing each occupied key through the
quotient map. This does not require rebuilding the row payloads. -/
noncomputable def redirected (grows : Extends before after) (label : Row → Term)
    (rows : Finset Row) (query : Term) : Finset Row := by
  classical
  let occupied := rows.image (fun row => Quotient.mk before (label row))
  exact (occupied.filter (fun key => advance grows key = Quotient.mk after query)).biUnion
    (bucket before label rows)

theorem redirected_eq_current (grows : Extends before after) (label : Row → Term)
    (rows : Finset Row) (query : Term) :
    redirected grows label rows query = bucket after label rows (Quotient.mk after query) := by
  classical
  ext row
  simp only [redirected, Finset.mem_biUnion, Finset.mem_filter, mem_bucket]
  constructor
  · rintro ⟨key, ⟨_, redirects⟩, present, spelling⟩
    exact ⟨present, (congrArg (advance grows) spelling).trans redirects⟩
  · rintro ⟨present, answer⟩
    exact ⟨Quotient.mk before (label row), ⟨Finset.mem_image_of_mem _ present, answer⟩,
      present, rfl⟩

namespace Controls

private def byIdentity : Setoid Bool := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
private def merged : Setoid Bool := Setoid.ker (fun _ => ())
private theorem growth : Extends byIdentity merged := by intro _ _ eq; cases eq; rfl

theorem one_old_bucket_misses_a_new_match :
    let rows : Finset Bool := {false, true}
    true ∉ bucket byIdentity id rows (Quotient.mk byIdentity false) ∧
      true ∈ bucket merged id rows (Quotient.mk merged false) := by
  dsimp only
  constructor
  · intro missed
    have wrong : true = false := Quotient.exact (s := byIdentity) ((mem_bucket _ _).mp missed).2
    exact Bool.noConfusion wrong
  · exact (mem_bucket _ _).mpr ⟨by simp, Quotient.sound (s := merged) rfl⟩

theorem redirection_recovers_both_rows :
    redirected growth id {false, true} false = {false, true} := by
  rw [redirected_eq_current]
  ext row
  simp only [mem_bucket, id_eq]
  exact ⟨And.left, fun present => ⟨present, Quotient.sound (s := merged) rfl⟩⟩

/-! A language with only three ground constants has no proper contexts.
This is where the smallest split ledger already yields a new equality. -/

private def groundConstants : CongruenceClosure (Fin 3) where
  step rules := rules
  root eq := eq
  mono := by
    intro small large inside source target eq
    exact inside source target eq
  split eq := eq
  congr eq := eq

private def noDeclaration (_ _ : Fin 3) : Prop := False

private theorem observes_ledger (ledger : List (Fin 3 × Fin 3)) (observe : Fin 3 → Bool)
    (respects : ∀ a b, (a, b) ∈ ledger → observe a = observe b)
    {a b : Fin 3} (eq : (epoch groundConstants noDeclaration ledger).r a b) :
    observe a = observe b := by
  change Relation.EqvGen (fun a b => noDeclaration a b ∨ (a,b) ∈ ledger) a b at eq
  induction eq with
  | rel a b step => exact step.elim False.elim (respects a b)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

theorem joined_tells_can_create_a_cross_branch_equality :
    (epoch groundConstants noDeclaration [(0, 1), (1, 2)]).r 0 2 ∧
      ¬ (epoch groundConstants noDeclaration [(0, 1)]).r 0 2 ∧
      ¬ (epoch groundConstants noDeclaration [(1, 2)]).r 0 2 := by
  have inJoint :
      Relation.EqvGen (fun a b : Fin 3 => noDeclaration a b ∨ (a,b) ∈ [(0,1), (1,2)]) 0 2 :=
    .trans 0 1 2 (.rel 0 1 (Or.inr (by simp))) (.rel 1 2 (Or.inr (by simp)))
  refine ⟨inJoint, ?_, ?_⟩
  · intro eq
    have agreed := observes_ledger [(0, 1)] (fun a => decide (a < 2)) (by
      intro a b inside
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp inside)
      rfl) eq
    exact Bool.noConfusion agreed
  · intro eq
    have agreed := observes_ledger [(1, 2)] (fun a => decide (0 < a)) (by
      intro a b inside
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp inside)
      rfl) eq
    exact Bool.noConfusion agreed

private def publicConstant : Bool → Fin 3
  | false => 0
  | true => 2

private theorem reflects_public (equations : Setoid (Fin 3)) (distinct : ¬ equations.r 0 2)
    (a b : Bool) : equations.r (publicConstant a) (publicConstant b) ↔ a = b := by
  cases a <;> cases b
  · exact ⟨fun _ => rfl, fun _ => equations.iseqv.refl _⟩
  · exact ⟨fun collapsed => (distinct collapsed).elim, fun no => by cases no⟩
  · exact ⟨fun collapsed => (distinct (equations.iseqv.symm collapsed)).elim,
      fun no => by cases no⟩
  · exact ⟨fun _ => rfl, fun _ => equations.iseqv.refl _⟩

private theorem constant_cases (a : Fin 3) : a = 0 ∨ a = 1 ∨ a = 2 := by
  have bound := a.isLt
  have cases : a.val = 0 ∨ a.val = 1 ∨ a.val = 2 := by omega
  rcases cases with zero | one | two
  · exact Or.inl (Fin.ext zero)
  · exact Or.inr (Or.inl (Fin.ext one))
  · exact Or.inr (Or.inr (Fin.ext two))

/-- Both imports on their own preserve and reflect equality of the
two public constants and introduce no new observable class. Their
joint import collapses those constants. Checking the two imports
separately is not sufficient for a protecting union. -/
theorem separately_protecting_imports_can_conflict :
    let left := epoch groundConstants noDeclaration [(0, 1)]
    let right := epoch groundConstants noDeclaration [(1, 2)]
    let joint := epoch groundConstants noDeclaration [(0, 1), (1, 2)]
    (∀ a b, left.r (publicConstant a) (publicConstant b) ↔ a = b) ∧
    (∀ a b, right.r (publicConstant a) (publicConstant b) ↔ a = b) ∧
    (∀ a, ∃ oldClass, left.r (publicConstant oldClass) a) ∧
    (∀ a, ∃ oldClass, right.r (publicConstant oldClass) a) ∧
    joint.r (publicConstant false) (publicConstant true) := by
  dsimp only
  obtain ⟨joint, left, right⟩ := joined_tells_can_create_a_cross_branch_equality
  refine ⟨reflects_public _ left, reflects_public _ right, ?_, ?_, joint⟩
  · intro n
    rcases constant_cases n with rfl | rfl | rfl
    · exact ⟨false, .refl _⟩
    · exact ⟨false, .rel 0 1 (Or.inr (by simp))⟩
    · exact ⟨true, .refl _⟩
  · intro n
    rcases constant_cases n with rfl | rfl | rfl
    · exact ⟨false, .refl _⟩
    · exact ⟨true, .symm 1 2 (.rel 1 2 (Or.inr (by simp)))⟩
    · exact ⟨true, .refl _⟩

end Controls

#print axioms epoch_extends
#print axioms advance_injective_iff
#print axioms fork_quotient_universal
#print axioms old_bucket_exact_iff
#print axioms redirected_eq_current
#print axioms Controls.one_old_bucket_misses_a_new_match
#print axioms Controls.redirection_recovers_both_rows
#print axioms Controls.joined_tells_can_create_a_cross_branch_equality
#print axioms Controls.separately_protecting_imports_can_conflict

end Mettapedia.GSLT.Contracts.EquationEpochs
