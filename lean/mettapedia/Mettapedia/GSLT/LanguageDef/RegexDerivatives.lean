import Mettapedia.Computability.RegularLanguages.Regex

/-!
# Typed structural regex rules

The relations in this module retain firing trees for Boolean evaluation,
nullability, derivatives and whole-word matching. They are defined by finite
structural rule families over the existing regex syntax. Scalar equality is
the only alphabet operation used by the derivative rules.

Soundness and completeness connect these rules to the checked executable
matcher and, through it, to independent language semantics. The raw
`LanguageDef` presentation and its source correspondence are separate
obligations; no textual parser or runtime host callback is defined here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexDerivatives

open Mettapedia.Computability.RegularLanguages

universe u
variable {α : Type u}

/-- The four declared Boolean disjunction firings. -/
inductive Disjoin : Bool → Bool → Bool → Type where
  | ff : Disjoin false false false
  | ft : Disjoin false true true
  | tf : Disjoin true false true
  | tt : Disjoin true true true

/-- The four declared Boolean conjunction firings. -/
inductive Conjoin : Bool → Bool → Bool → Type where
  | ff : Conjoin false false false
  | ft : Conjoin false true false
  | tf : Conjoin true false false
  | tt : Conjoin true true true

theorem Disjoin.sound {left right result : Bool} (event : Disjoin left right result) :
    (left || right) = result := by
  cases event <;> rfl

def Disjoin.complete (left right : Bool) : Disjoin left right (left || right) := by
  cases left <;> cases right
  · exact .ff
  · exact .ft
  · exact .tf
  · exact .tt

theorem Conjoin.sound {left right result : Bool} (event : Conjoin left right result) :
    (left && right) = result := by
  cases event <;> rfl

def Conjoin.complete (left right : Bool) : Conjoin left right (left && right) := by
  cases left <;> cases right
  · exact .ff
  · exact .ft
  · exact .tf
  · exact .tt

/-- Nullability firings. The two recursive binary rules retain both operand
firings and the Boolean-combination firing. -/
inductive Nullable : Regex α → Bool → Type u where
  | zero : Nullable 0 false
  | epsilon : Nullable 1 true
  | literal (a : α) : Nullable (literal a) false
  | any : Nullable any false
  | plus {p q : Regex α} {left right result : Bool} :
      Nullable p left → Nullable q right → Disjoin left right result → Nullable (p + q) result
  | comp {p q : Regex α} {left right result : Bool} :
      Nullable p left → Nullable q right → Conjoin left right result → Nullable (p * q) result
  | star (p : Regex α) : Nullable p.star true

theorem Nullable.sound {p : Regex α} {result : Bool} (event : Nullable p result) :
    p.matchEpsilon = result := by
  induction event with
  | zero => rfl
  | epsilon => rfl
  | literal _ => rfl
  | any => rfl
  | plus left right combination hleft hright =>
      change (_ || _) = _
      rw [hleft, hright]
      exact combination.sound
  | comp left right combination hleft hright =>
      change (_ && _) = _
      rw [hleft, hright]
      exact combination.sound
  | star _ => rfl

def Nullable.complete : (p : Regex α) → Nullable p p.matchEpsilon
  | .zero => .zero
  | .epsilon => .epsilon
  | .char (.literal a) => .literal a
  | .char .any => .any
  | .plus p q => .plus (complete p) (complete q) (Disjoin.complete _ _)
  | .comp p q => .comp (complete p) (complete q) (Conjoin.complete _ _)
  | .star p => .star p

theorem Nullable.correct (p : Regex α) (result : Bool) :
    Nonempty (Nullable p result) ↔ p.matchEpsilon = result := by
  constructor
  · rintro ⟨event⟩
    exact event.sound
  · intro h
    exact ⟨h ▸ Nullable.complete p⟩

theorem Nullable.result_unique {p : Regex α} {left right : Bool}
    (first : Nullable p left) (second : Nullable p right) : left = right :=
  first.sound.symm.trans second.sound

/-- Derivative firings. Concatenation has separate nullable and nonnullable
rules. A literal firing uses only equality or inequality of its scalar letters. -/
inductive Derivative (a : α) : Regex α → Regex α → Type u where
  | zero : Derivative a 0 0
  | epsilon : Derivative a 1 0
  | literal_eq {expected : α} : expected = a → Derivative a (literal expected) 1
  | literal_ne {expected : α} : expected ≠ a → Derivative a (literal expected) 0
  | any : Derivative a any 1
  | plus {p q dp dq : Regex α} :
      Derivative a p dp → Derivative a q dq → Derivative a (p + q) (dp + dq)
  | comp_nullable {p q dp dq : Regex α} :
      Nullable p true → Derivative a p dp → Derivative a q dq →
        Derivative a (p * q) (dp * q + dq)
  | comp_nonnullable {p q dp : Regex α} :
      Nullable p false → Derivative a p dp → Derivative a (p * q) (dp * q)
  | star {p dp : Regex α} : Derivative a p dp → Derivative a p.star (dp * p.star)

section Executable
variable [DecidableEq α]

theorem Derivative.sound {a : α} {p result : Regex α} (event : Derivative a p result) :
    derivative a p = result := by
  induction event with
  | zero => rfl
  | epsilon => rfl
  | literal_eq h => simp [derivative, Atom.accepts, literal, h]
  | literal_ne h => simp [derivative, Atom.accepts, literal, h]
  | any => rfl
  | plus left right hleft hright =>
      change derivative _ _ + derivative _ _ = _
      rw [hleft, hright]
  | comp_nullable nullable left right hleft hright =>
      simp only [derivative, nullable.sound, ite_true, hleft, hright]
  | comp_nonnullable nullable left hleft =>
      simp only [derivative, nullable.sound, Bool.false_eq_true, if_false, hleft]
  | star event hevent =>
      change derivative _ _ * _ = _
      rw [hevent]

def Derivative.complete (a : α) : (p : Regex α) → Derivative a p (derivative a p)
  | .zero => .zero
  | .epsilon => .epsilon
  | .char (.literal expected) => by
      by_cases h : expected = a
      · simpa [derivative, Atom.accepts, literal, h] using (Derivative.literal_eq h)
      · simpa [derivative, Atom.accepts, literal, h] using (Derivative.literal_ne h)
  | .char .any => .any
  | .plus p q => .plus (complete a p) (complete a q)
  | .comp p q => by
      cases h : p.matchEpsilon with
      | false =>
          simpa [derivative, h] using
            (Derivative.comp_nonnullable (h ▸ Nullable.complete p) (complete a p))
      | true =>
          simpa [derivative, h] using
            (Derivative.comp_nullable (h ▸ Nullable.complete p) (complete a p) (complete a q))
  | .star p => .star (complete a p)

theorem Derivative.correct (a : α) (p result : Regex α) :
    Nonempty (Derivative a p result) ↔ derivative a p = result := by
  constructor
  · rintro ⟨event⟩
    exact event.sound
  · intro h
    exact ⟨h ▸ Derivative.complete a p⟩

theorem Derivative.result_unique {a : α} {p left right : Regex α}
    (first : Derivative a p left) (second : Derivative a p right) : left = right :=
  first.sound.symm.trans second.sound

end Executable

/-- Whole-word firings retain each derivative firing before continuing with
the remaining input. The empty input retains its final nullability firing. -/
inductive Match : Regex α → List α → Bool → Type u where
  | nil {p : Regex α} {result : Bool} : Nullable p result → Match p [] result
  | cons {p next : Regex α} {a : α} {rest : List α} {result : Bool} :
      Derivative a p next → Match next rest result → Match p (a :: rest) result

section Executable
variable [DecidableEq α]

theorem Match.sound {p : Regex α} {word : List α} {result : Bool}
    (event : Match p word result) : fullMatch p word = result := by
  induction event with
  | nil nullable => exact nullable.sound
  | cons step rest hrest =>
      change fullMatch (derivative _ _) _ = _
      rw [step.sound]
      exact hrest

def Match.complete (p : Regex α) (word : List α) : Match p word (fullMatch p word) := by
  induction word generalizing p with
  | nil => exact .nil (Nullable.complete p)
  | cons a rest ih => exact .cons (Derivative.complete a p) (ih _)

theorem Match.correct (p : Regex α) (word : List α) (result : Bool) :
    Nonempty (Match p word result) ↔ fullMatch p word = result := by
  constructor
  · rintro ⟨event⟩
    exact event.sound
  · intro h
    exact ⟨h ▸ Match.complete p word⟩

/-- Acceptance in the structural rule graph is precisely actual language
membership. -/
theorem Match.accepts_iff (p : Regex α) (word : List α) :
    Nonempty (Match p word true) ↔ word ∈ language p := by
  rw [Match.correct, fullMatch_correct]

/-- Rejection is also reflected: the operational graph invents neither an
acceptance nor a rejection. -/
theorem Match.rejects_iff (p : Regex α) (word : List α) :
    Nonempty (Match p word false) ↔ word ∉ language p := by
  rw [Match.correct, Bool.eq_false_iff]
  exact not_congr (fullMatch_correct p word)

theorem Match.result_unique {p : Regex α} {word : List α} {left right : Bool}
    (first : Match p word left) (second : Match p word right) : left = right :=
  first.sound.symm.trans second.sound

end Executable

namespace Controls

/-- Nullable concatenation consumes the second factor after the first chooses
its empty alternative. Every premise is built from a declared constructor. -/
def nullable_concat_accepts : Match ((1 + literal 'λ') * literal 'β') ['β'] true :=
  .cons
    (.comp_nullable
      (.plus .epsilon (.literal 'λ') .tf)
      (.plus .epsilon (.literal_ne (by decide)))
      (.literal_eq rfl))
    (.nil (.plus (.comp (.plus .zero .zero .ff) (.literal 'β') .ff) .epsilon .ft))

def literal_wrong_rejected : Match (literal 'λ') ['β'] false :=
  .cons (.literal_ne (by decide)) (.nil .zero)

theorem literal_wrong_not_accepted : ¬ Nonempty (Match (literal 'λ') ['β'] true) := by
  rintro ⟨event⟩
  have impossible := event.result_unique literal_wrong_rejected
  cases impossible

/-- A wildcard consumes one Unicode scalar, including newline. -/
def wildcard_newline_accepts : Match any ['\n'] true :=
  .cons .any (.nil .epsilon)

theorem wildcard_empty_not_accepted : ¬ Nonempty (Match (any : Regex Char) [] true) := by
  rintro ⟨event⟩
  have impossible := event.result_unique (.nil .any)
  cases impossible

end Controls

end Mettapedia.GSLT.LanguageDef.RegexDerivatives
