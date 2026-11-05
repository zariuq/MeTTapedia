import Mettapedia.Algebra.Collections.Unification
import Mettapedia.Algebra.Collections.BoundedWordCompression
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.List.OfFn

/-!
# Bounded symbolic sequence-unifier families

Source variables and residual variables have separate carriers. A bound
limits the images of the finite active variable inventory. Candidate images
use only input constants and a bounded residual namespace, so they can be
enumerated without assuming a finite ambient alphabet.

Residual instantiation preserves unification, but can increase image lengths.
Concrete bounded answers must retain their length check; a bound is not a
global unsatisfiability certificate.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Collections.Unification.BoundedSequence

open Unification (Word substWord)

universe u v w z
variable {A : Type u} {X : Type v} {Y : Type w} {Z : Type z}

/-- The same word substitution, allowing an explicit residual namespace. -/
def applyInto (σ : X → Word A Y) (word : Word A X) : Word A Y :=
  word.flatMap (Sum.elim (fun a => [Sum.inl a]) σ)

theorem applyInto_same (σ : X → Word A X) (word : Word A X) :
    applyInto σ word = substWord σ word := rfl

@[simp] theorem applyInto_nil (σ : X → Word A Y) : applyInto σ [] = [] := rfl
@[simp] theorem applyInto_constant (σ : X → Word A Y) (a : A) (word : Word A X) :
    applyInto σ (.inl a :: word) = .inl a :: applyInto σ word := rfl
@[simp] theorem applyInto_variable (σ : X → Word A Y) (x : X) (word : Word A X) :
    applyInto σ (.inr x :: word) = σ x ++ applyInto σ word := rfl

theorem applyInto_append (σ : X → Word A Y) (first second : Word A X) :
    applyInto σ (first ++ second) = applyInto σ first ++ applyInto σ second := List.flatMap_append

theorem applyInto_compose (σ : X → Word A Y) (τ : Y → Word A Z) (word : Word A X) :
    applyInto τ (applyInto σ word) = applyInto (fun x => applyInto τ (σ x)) word := by
  induction word with
  | nil => rfl
  | cons token rest ih =>
      cases token with
      | inl a => simp only [applyInto_constant, ih]
      | inr x => simp only [applyInto_variable, applyInto_append, ih]

def Solves (left right : Word A X) (σ : X → Word A Y) : Prop := applyInto σ left = applyInto σ right

def Within (bound : Nat) (σ : X → Word A Y) : Prop := ∀ x, (σ x).length ≤ bound

/-- Generality is measured on the declared active variables, not on fresh
parameter names or arbitrary variables outside the problem. -/
def Instance (θ : X → Word A Y) (σ : X → Word A Z) : Prop :=
  ∃ τ : Y → Word A Z, ∀ x, applyInto τ (θ x) = σ x

theorem instance_sound {left right : Word A X} {θ : X → Word A Y} {σ : X → Word A Z}
    (solves : Solves left right θ) (instanceOf : Instance θ σ) : Solves left right σ := by
  obtain ⟨τ, represented⟩ := instanceOf
  have composed := congrArg (applyInto τ) solves
  simp only [applyInto_compose] at composed
  have same : (fun x => applyInto τ (θ x)) = σ := funext represented
  rwa [same] at composed

theorem instance_same_iff (θ σ : X → Word A X) :
    Instance θ σ ↔ Unification.InstanceOn Set.univ θ σ := by
  constructor
  · rintro ⟨τ, represented⟩
    exact ⟨τ, fun x _ => (represented x).symm⟩
  · rintro ⟨τ, represented⟩
    exact ⟨τ, fun x => (represented x (Set.mem_univ x)).symm⟩

/-- An enumerable bounded word, represented by its length and finite array. -/
abbrev ShortWord (Alphabet : Type u) (bound : Nat) :=
  Σ length : Fin (bound + 1), Fin length.val → Alphabet

def ShortWord.word {Alphabet : Type u} {bound : Nat} (code : ShortWord Alphabet bound) : List Alphabet :=
  List.ofFn code.2

theorem ShortWord.length_le {Alphabet : Type u} {bound : Nat} (code : ShortWord Alphabet bound) :
    code.word.length ≤ bound := by
  rw [ShortWord.word, List.length_ofFn]
  have := code.1.isLt
  omega

def ShortWord.ofList {Alphabet : Type u} (bound : Nat) (word : List Alphabet) (within : word.length ≤ bound) :
    ShortWord Alphabet bound := ⟨⟨word.length, by omega⟩, word.get⟩

@[simp] theorem ShortWord.word_ofList {Alphabet : Type u} (bound : Nat) (word : List Alphabet)
    (within : word.length ≤ bound) : (ShortWord.ofList bound word within).word = word := List.ofFn_get word

variable [DecidableEq A]

abbrev Alphabet (constants : Finset A) (arity bound : Nat) := constants ⊕ Fin (arity * bound)
abbrev Candidate (constants : Finset A) (arity bound : Nat) :=
  Fin arity → ShortWord (Alphabet constants arity bound) bound

def embed {constants : Finset A} {arity bound : Nat} : Alphabet constants arity bound → A ⊕ Fin (arity * bound)
  | .inl a => .inl a.val
  | .inr parameter => .inr parameter

def values {constants : Finset A} {arity bound : Nat} (code : Candidate constants arity bound) :
    Fin arity → Word A (Fin (arity * bound)) := fun x => (code x).word.map embed

/-- Exhaustive finite candidates filtered by the actual word equations. -/
def unifiers (constants : Finset A) (arity bound : Nat) (left right : Word A (Fin arity)) :
    Finset (Candidate constants arity bound) :=
  Finset.univ.filter fun code => applyInto (values code) left = applyInto (values code) right

theorem mem_unifiers {constants : Finset A} {arity bound : Nat} {left right : Word A (Fin arity)}
    (code : Candidate constants arity bound) :
    code ∈ unifiers constants arity bound left right ↔ Solves left right (values code) := by
  simp [unifiers, Solves]

omit [DecidableEq A] in
theorem values_bounded {constants : Finset A} {arity bound : Nat} (code : Candidate constants arity bound) :
    Within bound (values code) := by
  intro x
  simpa only [values, List.length_map] using (code x).length_le

theorem all_instances_solve {constants : Finset A} {arity bound : Nat} {left right : Word A (Fin arity)}
    {code : Candidate constants arity bound} (member : code ∈ unifiers constants arity bound left right)
    (σ : Fin arity → Word A Y) (represented : Instance (values code) σ) : Solves left right σ :=
  instance_sound ((mem_unifiers code).mp member) represented

theorem unifiers_finite (constants : Finset A) (arity bound : Nat) (left right : Word A (Fin arity)) :
    (↑(unifiers constants arity bound left right) : Set (Candidate constants arity bound)).Finite :=
  Finset.finite_toSet _

def ConstantsWithin (constants : Finset A) (word : Word A X) : Prop :=
  ∀ a, Sum.inl a ∈ word → a ∈ constants

def constantsOf (word : Word A X) : Finset A :=
  (word.filterMap fun token => match token with | .inl a => some a | .inr _ => none).toFinset

theorem constantsOf_complete (word : Word A X) : ConstantsWithin (constantsOf word) word := by
  intro a member
  apply List.mem_toFinset.mpr
  exact List.mem_filterMap.mpr ⟨.inl a, member, rfl⟩

omit [DecidableEq A] in
theorem ConstantsWithin.mono {first second : Finset A} {word : Word A X}
    (included : first ⊆ second) (closed : ConstantsWithin first word) : ConstantsWithin second word :=
  fun a member => included (closed a member)

omit [DecidableEq A] in
theorem image_length_le (arity bound : Nat) (σ : Fin arity → Word A Y) (within : Within bound σ) :
    (List.ofFn σ).flatten.length ≤ arity * bound := by
  induction arity with
  | zero => simp
  | succ arity ih =>
      rw [List.ofFn_succ, List.flatten_cons, List.length_append]
      have tail := ih (fun x => σ x.succ) (fun x => within x.succ)
      have first := within 0
      simpa only [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add first tail

omit [DecidableEq A] in
theorem encode_substituted {constants : Finset A} {support : Finset (A ⊕ Y)} {arity bound : Nat}
    (encoding : BoundedWordCompression.Encoding constants support (arity * bound))
    (σ : Fin arity → Word A Y) (word : Word A (Fin arity)) (closed : ConstantsWithin constants word) :
    (encoding.encodeWord (applyInto σ word)).map embed =
      applyInto (fun x => (encoding.encodeWord (σ x)).map embed) word := by
  induction word with
  | nil => rfl
  | cons token rest ih =>
      have tailClosed : ConstantsWithin constants rest :=
        fun a member => closed a (List.mem_cons_of_mem _ member)
      cases token with
      | inl a =>
          have literal := encoding.constant a (closed a List.mem_cons_self)
          simp only [applyInto_constant, BoundedWordCompression.Encoding.encodeWord,
            List.filterMap_cons, literal, List.map_cons, embed]
          exact congrArg (List.cons (.inl a)) (ih tailClosed)
      | inr x =>
          simpa only [applyInto_variable, BoundedWordCompression.Encoding.encodeWord,
            List.filterMap_append, List.map_append] using
            congrArg (fun word => (encoding.encodeWord (σ x)).map embed ++ word) (ih tailClosed)

omit [DecidableEq A] in
theorem decode_embedded {constants : Finset A} {support : Finset (A ⊕ Y)} {arity bound : Nat}
    (encoding : BoundedWordCompression.Encoding constants support (arity * bound))
    (word : Word constants (Fin (arity * bound))) :
    applyInto encoding.lift (word.map embed) = encoding.decodeWord word := by
  induction word with
  | nil => rfl
  | cons token rest ih =>
      cases token <;> simp [applyInto, embed, BoundedWordCompression.Encoding.decodeWord] at ih ⊢ <;> rw [ih]

/-- Every bounded unifier is an instance of an actually enumerated symbolic
candidate, including unifiers using constants outside the input alphabet.
The witness may use variables in a different residual namespace. -/
theorem complete (constants : Finset A) (arity bound : Nat) (left right : Word A (Fin arity))
    (leftClosed : ConstantsWithin constants left) (rightClosed : ConstantsWithin constants right)
    (σ : Fin arity → Word A Y) (solves : Solves left right σ) (within : Within bound σ) :
    ∃ code ∈ unifiers constants arity bound left right, Instance (values code) σ := by
  classical
  let support := (List.ofFn σ).flatten.toFinset
  have supported (x : Fin arity) (token : A ⊕ Y) (member : token ∈ σ x) : token ∈ support := by
    apply List.mem_toFinset.mpr
    exact List.mem_flatten.mpr ⟨σ x, List.mem_ofFn.mpr ⟨x, rfl⟩, member⟩
  have capacity : support.card ≤ arity * bound :=
    (List.toFinset_card_le _).trans (image_length_le arity bound σ within)
  obtain ⟨encoding⟩ := BoundedWordCompression.exists_encoding constants support (arity * bound) capacity
  let code : Candidate constants arity bound := fun x =>
    ShortWord.ofList bound (encoding.encodeWord (σ x)) (by
      rw [encoding.encodeWord_length (σ x) (supported x)]
      exact within x)
  have represented (x : Fin arity) : values code x = (encoding.encodeWord (σ x)).map embed := by
    simp only [values, code, ShortWord.word_ofList]
  have codeSolves : Solves left right (values code) := by
    have compressed := congrArg (fun word => (encoding.encodeWord word).map (embed (arity := arity) (bound := bound))) solves
    rw [encode_substituted encoding σ left leftClosed, encode_substituted encoding σ right rightClosed] at compressed
    have same : values code = fun x => (encoding.encodeWord (σ x)).map embed := funext represented
    exact same.symm ▸ compressed
  refine ⟨code, (mem_unifiers code).mpr codeSolves, encoding.lift, ?_⟩
  intro x
  rw [represented, decode_embedded]
  exact encoding.recover_word (σ x) (supported x)

/-- The input itself supplies the finite constant inventory. -/
def solveBounded (arity bound : Nat) (left right : Word A (Fin arity)) :
    Finset (Candidate (constantsOf left ∪ constantsOf right) arity bound) :=
  unifiers (constantsOf left ∪ constantsOf right) arity bound left right

theorem solveBounded_complete (arity bound : Nat) (left right : Word A (Fin arity))
    (σ : Fin arity → Word A Y) (solves : Solves left right σ) (within : Within bound σ) :
    ∃ code ∈ solveBounded arity bound left right, Instance (values code) σ :=
  complete _ arity bound left right
    ((constantsOf_complete left).mono Finset.subset_union_left)
    ((constantsOf_complete right).mono Finset.subset_union_right) σ solves within

/-- Exact bounded-solution readout. Residual expansion is followed by the
same image-length check; omitting that check changes the specified problem. -/
theorem solveBounded_spec (arity bound : Nat) (left right : Word A (Fin arity))
    (σ : Fin arity → Word A Y) :
    Solves left right σ ∧ Within bound σ ↔
      Within bound σ ∧ ∃ code ∈ solveBounded arity bound left right, Instance (values code) σ := by
  constructor
  · rintro ⟨solves, within⟩
    exact ⟨within, solveBounded_complete arity bound left right σ solves within⟩
  · rintro ⟨within, code, member, represented⟩
    exact ⟨all_instances_solve member σ represented, within⟩

end Mettapedia.Algebra.Collections.Unification.BoundedSequence
