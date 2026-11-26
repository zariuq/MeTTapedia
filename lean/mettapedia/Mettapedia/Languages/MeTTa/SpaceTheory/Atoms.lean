import Mathlib.Data.List.Basic
import Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-!
# The atoms of a space and their interpretations

Classification leaves all occurrences inspectable as atoms. In particular,
a function definition or a type assignment can also be the object of a match.
Filtering by role preserves multiplicity and whatever order this observation
of the space actually supplies; it does not declare a language-wide order.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.Atoms

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

inductive Kind where
  | data | definition | directed | typed | subtype | equational
  deriving DecidableEq, Repr

inductive Family where
  | data | rule | typing
  deriving DecidableEq, Repr

def Kind.family : Kind → Option Family
  | .data => some .data
  | .definition | .directed => some .rule
  | .typed | .subtype => some .typing
  | .equational => none

structure Tag (Name : Type*) where
  kind : Kind
  /-- An occurrence with no rigid head symbol cannot be rejected by name alone. -/
  head : Option Name := none
  deriving DecidableEq, Repr

structure Occurrence (Name A : Type*) where
  tag : Tag Name
  atom : A
  deriving DecidableEq, Repr

/-- The three uses of an equation declaration contribute the same logical
equalities; only the two preferences direct the choice of a printed term. -/
inductive Preference where
  | indifferent | rightward | leftward
  deriving DecidableEq, Repr

inductive Content where
  | data (atom : Atom)
  | definition (lhs rhs : Atom)
  | directed (lhs rhs : Atom)
  | assignment (subject type : Atom)
  | subtype (smaller larger : Atom)
  | equation (pref : Preference) (first second : Atom) (rest : List Atom)
  deriving DecidableEq, Repr

def Preference.symbol : Preference → String
  | .indifferent => "=e"
  | .rightward => "=e>"
  | .leftward => "=e<"

def Content.syntax : Content → Atom
  | .data a => a
  | .definition l r => .expression [.symbol "=", l, r]
  | .directed l r => .expression [.symbol "=%", l, r]
  | .assignment t ty => .expression [.symbol ":", t, ty]
  | .subtype s t => .expression [.symbol ":<", s, t]
  | .equation pref a b rest => .expression (.symbol pref.symbol :: a :: b :: rest)

/-- One interpretation of declaration syntax. This does not make every
syntactically valid declaration applicable in every dialect. -/
def content : Atom → Content
  | .expression [.symbol "=", lhs, rhs] => .definition lhs rhs
  | .expression [.symbol "=%", lhs, rhs] => .directed lhs rhs
  | .expression [.symbol ":", subject, type] => .assignment subject type
  | .expression [.symbol ":<", smaller, larger] => .subtype smaller larger
  | .expression (.symbol "=e" :: a :: b :: rest) => .equation .indifferent a b rest
  | .expression (.symbol "=e>" :: a :: b :: rest) => .equation .rightward a b rest
  | .expression (.symbol "=e<" :: a :: b :: rest) => .equation .leftward a b rest
  | a => .data a

@[simp] theorem content_syntax (a : Atom) : (content a).syntax = a := by
  unfold content
  split <;> rfl

def applicationHead : Atom → Option String
  | .expression (.symbol h :: _) => some h
  | _ => none

def literalHead : Atom → Option String
  | .symbol h => some h
  | a => applicationHead a

def Content.tag : Content → Tag String
  | .data a => ⟨.data, literalHead a⟩
  | .definition l _ => ⟨.definition, applicationHead l⟩
  | .directed l _ => ⟨.directed, applicationHead l⟩
  | .assignment t _ => ⟨.typed, literalHead t⟩
  | .subtype _ _ => ⟨.subtype, none⟩
  | .equation _ _ _ _ => ⟨.equational, none⟩

def classify (a : Atom) : Tag String := (content a).tag

def definition? (a : Atom) : Option (Atom × Atom) :=
  match content a with
  | .definition lhs rhs => some (lhs, rhs)
  | _ => none

theorem definition?_iff {a lhs rhs : Atom} :
    definition? a = some (lhs, rhs) ↔ a = .expression [.symbol "=", lhs, rhs] := by
  constructor
  · intro parsed
    unfold definition? at parsed
    split at parsed
    next l r same =>
      cases parsed
      simpa only [same, Content.syntax] using (content_syntax a).symm
    all_goals contradiction
  · rintro rfl
    rfl

theorem definitionKind_iff (a : Atom) :
    (classify a).kind = .definition ↔ ∃ lhs rhs, a = .expression [.symbol "=", lhs, rhs] := by
  constructor
  · intro tag
    cases c : content a with
    | definition lhs rhs => exact ⟨lhs, rhs, by simpa [c, Content.syntax] using (content_syntax a).symm⟩
    | _ => simp [classify, c, Content.tag] at tag
  · rintro ⟨lhs, rhs, rfl⟩
    rfl

theorem assignmentKind_iff (a : Atom) :
    (classify a).kind = .typed ↔ ∃ subject type, a = .expression [.symbol ":", subject, type] := by
  constructor
  · intro tag
    cases c : content a with
    | assignment subject type =>
      exact ⟨subject, type, by simpa [c, Content.syntax] using (content_syntax a).symm⟩
    | _ => simp [classify, c, Content.tag] at tag
  · rintro ⟨subject, type, rfl⟩
    rfl

variable {N A : Type*}

/-- Classification is an interpretation of occurrences, not a quotient of
their payloads. Equal atoms may occur several times. -/
def annotate (classify : A → Tag N) (atoms : List A) : List (Occurrence N A) :=
  atoms.map fun atom => ⟨classify atom, atom⟩

@[simp] theorem raw_annotate (classify : A → Tag N) (atoms : List A) :
    (annotate classify atoms).map Occurrence.atom = atoms := by
  rw [annotate, List.map_map]
  exact List.map_id atoms

def ofKind (k : Kind) (atoms : List (Occurrence N A)) : List (Occurrence N A) :=
  atoms.filter fun a => decide (a.tag.kind = k)

theorem ofKind_annotate (classify : A → Tag N) (k : Kind) (atoms : List A) :
    (ofKind k (annotate classify atoms)).map Occurrence.atom =
      atoms.filter (fun a => decide ((classify a).kind = k)) := by
  rw [ofKind, annotate, List.filter_map, List.map_map]
  exact List.map_id _

theorem ofKind_partition (k : Kind) (atoms : List (Occurrence N A)) (a : Occurrence N A) :
    a ∈ ofKind k atoms ↔ a ∈ atoms ∧ a.tag.kind = k := by simp [ofKind]

theorem ofKind_disjoint {k k' : Kind} (different : k ≠ k') (atoms : List (Occurrence N A)) :
    List.Disjoint (ofKind k atoms) (ofKind k' atoms) := by
  intro a one two
  exact different (((ofKind_partition k atoms a).mp one).2.symm.trans
    ((ofKind_partition k' atoms a).mp two).2)

/-- A syntactic candidate view. Under additional equations a caller must
use an invariant of equality classes or consider a larger region. -/
def candidates [DecidableEq N] (f : Family) (head : N) (atoms : List (Occurrence N A)) :
    List (Occurrence N A) :=
  atoms.filter fun a => decide (a.tag.kind.family = some f ∧
    (a.tag.head = some head ∨ a.tag.head = none))

theorem mem_candidates [DecidableEq N] (f : Family) (head : N)
    (atoms : List (Occurrence N A)) (a : Occurrence N A) :
    a ∈ candidates f head atoms ↔
      a ∈ atoms ∧ a.tag.kind.family = some f ∧ (a.tag.head = some head ∨ a.tag.head = none) := by
  simp [candidates]

theorem unheaded_is_candidate [DecidableEq N] {f : Family} {head : N}
    {atoms : List (Occurrence N A)} {a : Occurrence N A} (present : a ∈ atoms)
    (family : a.tag.kind.family = some f) (unheaded : a.tag.head = none) :
    a ∈ candidates f head atoms :=
  (mem_candidates _ _ _ _).mpr ⟨present, family, .inr unheaded⟩

end Mettapedia.Languages.MeTTa.SpaceTheory.Atoms
