import Mettapedia.Logic.ConstraintTypes.Contracts

/-!
# Query-directed shared type witnesses

For signatures of closed types and bare parameters, finite observations of each
value suffice to find one shared witness. The type universe itself may be
infinite. No list of all assignments is constructed. Each parameter chooses a
candidate consistent with all its occurrences, including result occurrences.

Completeness requires the observations to cover membership for the values in
this query. Infinitely polymorphic observations such as an uninstantiated empty
list use the symbolic solver in DeclarationTyping instead. This module is
a finite-observation specialization, not the general admission algorithm.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ConstraintTypes.WitnessSolver

variable {P Q V : Type} [DecidableEq P]

abbrev FlatType (P Q : Type) := TypeExpr P Q Empty Empty.elim
abbrev Slots (P Q V : Type) := List (FlatType P Q × V)

def instantiate (assignment : P → Q) : FlatType P Q → Q
  | .parameter p => assignment p
  | .closed q => q
  | .app c _ => nomatch c

def select (predicate : Q → Bool) : List Q → Option Q
  | [] => none
  | q :: rest => if predicate q then some q else select predicate rest

theorem select_sound (predicate : Q → Bool) (pool : List Q) (q : Q)
    (selected : select predicate pool = some q) : q ∈ pool ∧ predicate q = true := by
  induction pool with
  | nil => cases selected
  | cons first rest ih =>
      unfold select at selected
      split at selected
      next accepted => cases selected; exact ⟨List.mem_cons_self, accepted⟩
      next =>
        obtain ⟨member, accepted⟩ := ih selected
        exact ⟨List.mem_cons_of_mem _ member, accepted⟩

theorem select_complete (predicate : Q → Bool) (pool : List Q)
    (witness : ∃ q ∈ pool, predicate q = true) : ∃ q, select predicate pool = some q := by
  induction pool with
  | nil => obtain ⟨_, impossible, _⟩ := witness; cases impossible
  | cons first rest ih =>
      by_cases accepted : predicate first = true
      · exact ⟨first, by simp [select, accepted]⟩
      · obtain ⟨q, hq, hp⟩ := witness
        have tail : q ∈ rest := by
          cases List.mem_cons.1 hq with
          | inl same => subst q; exact False.elim (accepted hp)
          | inr member => exact member
        obtain ⟨result, hr⟩ := ih ⟨q, tail, hp⟩
        exact ⟨result, by simp [select, accepted, hr]⟩

def isParameter (p : P) : FlatType P Q → Bool
  | .parameter other => decide (other = p)
  | .closed _ => false
  | .app c _ => nomatch c

def used (p : P) (slots : Slots P Q V) : Bool := slots.any fun slot => isParameter p slot.1

def consistent (member : Q → V → Bool) (p : P) (q : Q) (slots : Slots P Q V) : Bool :=
  slots.all fun slot => if isParameter p slot.1 then member q slot.2 else true

def pool (observations : V → List Q) (slots : Slots P Q V) : List Q :=
  slots.flatMap fun slot => observations slot.2

def choice (member : Q → V → Bool) (observations : V → List Q) (fallback : Q)
    (slots : Slots P Q V) (p : P) : Option Q :=
  if used p slots then select (fun q => consistent member p q slots) (pool observations slots)
  else some fallback

def solve (member : Q → V → Bool) (observations : V → List Q) (fallback : Q)
    (slots : Slots P Q V) : Option (P → Q) :=
  if slots.all (fun slot => match slot.1 with
      | .parameter p => (choice member observations fallback slots p).isSome
      | .closed q => member q slot.2
      | .app c _ => nomatch c) then
    some (fun p => (choice member observations fallback slots p).getD fallback)
  else none

theorem parameter_used (slots : Slots P Q V) (p : P) (value : V)
    (occurs : (TypeExpr.parameter p, value) ∈ slots) : used p slots = true :=
  List.any_eq_true.2 ⟨_, occurs, by simp [isParameter]⟩

theorem consistent_checks_occurrence (member : Q → V → Bool) (slots : Slots P Q V)
    (p : P) (q : Q) (value : V) (occurs : (TypeExpr.parameter p, value) ∈ slots)
    (accepted : consistent member p q slots = true) : member q value = true := by
  have := (List.all_eq_true.1 accepted) _ occurs
  simpa [isParameter] using this

theorem solve_sound (member : Q → V → Bool) (observations : V → List Q) (fallback : Q)
    (slots : Slots P Q V) (assignment : P → Q)
    (success : solve member observations fallback slots = some assignment) :
    ∀ slot ∈ slots, member (instantiate assignment slot.1) slot.2 = true := by
  unfold solve at success
  split at success
  next admitted =>
    cases success
    intro slot hs
    have accepted := (List.all_eq_true.1 admitted) slot hs
    rcases slot with ⟨type, value⟩
    cases type with
    | closed q => exact accepted
    | app c _ => exact Empty.elim c
    | parameter p =>
        have hu := parameter_used slots p value hs
        cases hc : choice member observations fallback slots p with
        | none => simp [hc] at accepted
        | some q =>
            have selected : select (fun q => consistent member p q slots)
                (pool observations slots) = some q := by
              simpa [choice, hu] using hc
            have fits := consistent_checks_occurrence member slots p q value hs
              (select_sound _ _ _ selected).2
            simpa [instantiate, hc] using fits
  next => cases success

theorem solve_complete (member : Q → V → Bool) (observations : V → List Q) (fallback : Q)
    (slots : Slots P Q V)
    (covers : ∀ slot ∈ slots, ∀ q, member q slot.2 = true → q ∈ observations slot.2)
    (witness : ∃ assignment : P → Q,
      ∀ slot ∈ slots, member (instantiate assignment slot.1) slot.2 = true) :
    ∃ assignment, solve member observations fallback slots = some assignment := by
  obtain ⟨assignment, fits⟩ := witness
  have admitted : slots.all (fun slot => match slot.1 with
      | .parameter p => (choice member observations fallback slots p).isSome
      | .closed q => member q slot.2
      | .app c _ => nomatch c) = true := by
    apply List.all_eq_true.2
    rintro ⟨type, value⟩ hs
    cases type with
    | closed q => exact fits _ hs
    | app c _ => exact Empty.elim c
    | parameter p =>
        have hu := parameter_used slots p value hs
        have inPool : assignment p ∈ pool observations slots :=
          List.mem_flatMap.2 ⟨_, hs, covers _ hs _ (fits _ hs)⟩
        have accepts : consistent member p (assignment p) slots = true := by
          apply List.all_eq_true.2
          rintro ⟨otherType, otherValue⟩ ho
          cases otherType with
          | closed _ => rfl
          | app c _ => exact Empty.elim c
          | parameter other =>
              by_cases equal : other = p
              · subst other
                simpa [isParameter, instantiate] using fits _ ho
              · simp [isParameter, equal]
        obtain ⟨q, selected⟩ := select_complete
          (fun q => consistent member p q slots) (pool observations slots)
          ⟨assignment p, inPool, accepts⟩
        simp [choice, hu, selected]
  exact ⟨(fun p => (choice member observations fallback slots p).getD fallback),
    by simp [solve, admitted]⟩

end Mettapedia.Logic.ConstraintTypes.WitnessSolver
