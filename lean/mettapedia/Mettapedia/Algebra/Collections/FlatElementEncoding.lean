import Mettapedia.Logic.LP.TotalUnification

/-!
# Flat element equations through the existing total unifier

Elements are constants or variables. The function-free signature has exactly
these terms, so encoding and decoding are inverse and substitution commutes
with them. Solver refusal is logical inconsistency, not resource exhaustion.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Collections.FlatElementEncoding

open Mettapedia.Logic.LP (LPSignature Term Subst Unifies)

universe u v

abbrev Element (A X : Type*) := A ⊕ X

abbrev signature (A : Type u) (X : Type v) : LPSignature.{max u v, max u v, 0, max u v} where
  constants := ULift.{v} A
  vars := ULift.{u} X
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := ULift.{max u v} Empty
  functionArity := fun symbol => symbol.down.elim

variable {A X : Type*}

def encode : Element A X → Term (signature A X)
  | .inl value => .const ⟨value⟩
  | .inr name => .var ⟨name⟩

def decode : Term (signature A X) → Element A X
  | .const value => .inl value.down
  | .var name => .inr name.down
  | .app impossible _ => impossible.down.elim

@[simp] theorem decode_encode (element : Element A X) : decode (encode element) = element := by
  cases element <;> rfl

@[simp] theorem encode_decode (term : Term (signature A X)) : encode (decode term) = term := by
  cases term with
  | var | const => rfl
  | app impossible _ => exact impossible.down.elim

def apply (assignment : X → Element A X) : Element A X → Element A X := Sum.elim Sum.inl assignment
def encodeSubst (assignment : X → Element A X) : Subst (signature A X) := fun name => encode (assignment name.down)
def decodeSubst (assignment : Subst (signature A X)) : X → Element A X := fun name => decode (assignment ⟨name⟩)

@[simp] theorem apply_constant (assignment : X → Element A X) (value : A) : apply assignment (.inl value) = .inl value := rfl
@[simp] theorem apply_variable (assignment : X → Element A X) (name : X) : apply assignment (.inr name) = assignment name := rfl

@[simp] theorem apply_id (element : Element A X) : apply Sum.inr element = element := by
  cases element <;> rfl

theorem apply_comp (outer inner : X → Element A X) (element : Element A X) :
    apply (fun name => apply outer (inner name)) element = apply outer (apply inner element) := by
  cases element <;> rfl

theorem encode_apply (assignment : X → Element A X) (element : Element A X) :
    encode (apply assignment element) = (encodeSubst assignment).applyTerm (encode element) := by
  cases element <;> rfl

theorem decode_apply (assignment : Subst (signature A X)) (term : Term (signature A X)) :
    decode (assignment.applyTerm term) = apply (decodeSubst assignment) (decode term) := by
  cases term with
  | var | const => rfl
  | app impossible _ => exact impossible.down.elim

def equations (pairs : List (Element A X × Element A X)) : List (Term (signature A X) × Term (signature A X)) :=
  pairs.map fun pair => (encode pair.1, encode pair.2)

def Solves (pairs : List (Element A X × Element A X)) (assignment : X → Element A X) : Prop :=
  ∀ pair ∈ pairs, apply assignment pair.1 = apply assignment pair.2

theorem encoded_solves (pairs : List (Element A X × Element A X)) (assignment : X → Element A X)
    (solved : Solves pairs assignment) : Unifies (encodeSubst assignment) (equations pairs) := by
  intro pair member
  obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
  rw [← encode_apply, ← encode_apply, solved source present]

variable [DecidableEq A] [DecidableEq X]

def solve (pairs : List (Element A X × Element A X)) : Option (X → Element A X) :=
  (Mettapedia.Logic.LP.unifyTotal (equations pairs)).map decodeSubst

theorem solve_sound (pairs : List (Element A X × Element A X)) (assignment : X → Element A X)
    (accepted : solve pairs = some assignment) : Solves pairs assignment := by
  unfold solve at accepted
  obtain ⟨raw, rawAccepted, rfl⟩ := Option.map_eq_some_iff.mp accepted
  intro pair member
  have same := Mettapedia.Logic.LP.unifyTotal_sound (equations pairs) raw rawAccepted
    (encode pair.1, encode pair.2) (List.mem_map.mpr ⟨pair, member, rfl⟩)
  simpa only [decode_apply, decode_encode] using congrArg decode same

theorem solve_complete (pairs : List (Element A X × Element A X))
    (assignment : X → Element A X) (solved : Solves pairs assignment) :
    ∃ general, solve pairs = some general := by
  obtain ⟨raw, accepted⟩ := Mettapedia.Logic.LP.unifyTotal_complete ⟨encodeSubst assignment, encoded_solves pairs assignment solved⟩
  exact ⟨decodeSubst raw, by simp only [solve, accepted, Option.map_some]⟩

theorem solve_mgu (pairs : List (Element A X × Element A X)) (general : X → Element A X)
    (accepted : solve pairs = some general) (assignment : X → Element A X) (solved : Solves pairs assignment) :
    ∃ remainder : X → Element A X, ∀ name, assignment name = apply remainder (general name) := by
  unfold solve at accepted
  obtain ⟨raw, rawAccepted, rfl⟩ := Option.map_eq_some_iff.mp accepted
  obtain ⟨remainder, factors⟩ := Mettapedia.Logic.LP.unifyTotal_mgu (equations pairs) raw rawAccepted
    (encodeSubst assignment) (encoded_solves pairs assignment solved)
  refine ⟨decodeSubst remainder, ?_⟩
  intro name
  have same := congrArg decode (factors ⟨name⟩)
  simpa only [encodeSubst, decode_encode, decode_apply, decodeSubst] using same

theorem solve_none_iff (pairs : List (Element A X × Element A X)) :
    solve pairs = none ↔ ¬ ∃ assignment, Solves pairs assignment := by
  constructor
  · intro rejected solvable
    obtain ⟨assignment, solved⟩ := solvable
    obtain ⟨general, accepted⟩ := solve_complete pairs assignment solved
    rw [rejected] at accepted
    cases accepted
  · intro impossible
    cases result : solve pairs with
    | none => rfl
    | some assignment => exact (impossible ⟨assignment, solve_sound pairs assignment result⟩).elim

end Mettapedia.Algebra.Collections.FlatElementEncoding
