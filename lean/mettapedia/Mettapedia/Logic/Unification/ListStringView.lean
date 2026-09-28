import Mettapedia.Data.String.ByteString
import Mettapedia.Logic.Unification.ListSpliceEncoding

/-!
# Unicode scalar string views as ordinary list patterns

The checked scalar view of a string is represented in the existing list-splice
term language. String leaves occupy the left summand of `String ⊕ Other`; other
leaf kinds, variables and expression/list nodes cannot masquerade as character
strings. The inverse accepts exactly proper lists of singleton scalar strings.

The head/rest law is transported through the existing first-order encoding and
prefix-meeting theorem. It therefore uses ordinary list unification, including
the same substitution and splice equations, rather than a new string matcher.

These are scalar values, not grapheme clusters. This view supplies no symbol
declaration, binding authority, evaluator demand or native implementation claim.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Unification.ListStringView

open Mettapedia.Logic.Unification.ListSplice

open Mettapedia.Data.String

variable {Other Var : Type}

abbrev StringTerm (Other Var : Type) := Term (String ⊕ Other) Var

def stringAtom (text : String) : StringTerm Other Var := .atom (.inl text)

def characterAtom (c : Char) : StringTerm Other Var := stringAtom (String.singleton c)

def charactersTerm (text : String) : StringTerm Other Var :=
  .list ((ByteString.characters text).map stringAtom)

def stringAtom? : StringTerm Other Var → Option String
  | .atom (.inl text) => some text
  | _ => none

def stringAtoms? : List (StringTerm Other Var) → Option (List String)
  | [] => some []
  | value :: values => do
    return (← stringAtom? value) :: (← stringAtoms? values)

def stringFromTerm? : StringTerm Other Var → Option String
  | .list values => do ByteString.fromCharacters? (← stringAtoms? values)
  | _ => none

@[simp] theorem stringAtom?_stringAtom (text : String) :
    stringAtom? (stringAtom text : StringTerm Other Var) = some text := rfl

theorem stringAtom?_exact {value : StringTerm Other Var} {text : String}
    (read : stringAtom? value = some text) : value = stringAtom text := by
  cases value with
  | atom leaf =>
    cases leaf with
    | inl stored =>
      have same : stored = text := by simpa [stringAtom?] using read
      rw [same]
      rfl
    | inr other => cases read
  | var _ => cases read
  | expr _ => cases read
  | list _ => cases read
  | rest _ _ => cases read

@[simp] theorem stringAtoms?_map (texts : List String) :
    stringAtoms? (texts.map (stringAtom (Other := Other) (Var := Var))) = some texts := by
  induction texts with
  | nil => rfl
  | cons text texts ih => simp [stringAtoms?, ih]

theorem stringAtoms?_exact {values : List (StringTerm Other Var)} {texts : List String}
    (read : stringAtoms? values = some texts) : values = texts.map stringAtom := by
  induction values generalizing texts with
  | nil =>
    simp only [stringAtoms?, Option.some.injEq] at read
    subst texts
    rfl
  | cons value values ih =>
    cases head : stringAtom? value with
    | none => simp [stringAtoms?, head] at read
    | some text =>
      cases tail : stringAtoms? values with
      | none => simp [stringAtoms?, head, tail] at read
      | some texts' =>
        simp [stringAtoms?, head, tail] at read
        subst texts
        rw [stringAtom?_exact head, ih tail]
        rfl

@[simp] theorem stringFromTerm?_charactersTerm (text : String) :
    stringFromTerm? (charactersTerm text : StringTerm Other Var) = some text := by
  simp [stringFromTerm?, charactersTerm, ByteString.fromCharacters?_characters]

/-- The inverse accepts precisely the proper singleton-string-list image. -/
theorem charactersTerm_of_read {value : StringTerm Other Var} {text : String}
    (read : stringFromTerm? value = some text) : charactersTerm text = value := by
  cases value with
  | list values =>
    cases elements : stringAtoms? values with
    | none => simp [stringFromTerm?, elements] at read
    | some texts =>
      have chars : ByteString.fromCharacters? texts = some text := by
        simpa [stringFromTerm?, elements] using read
      rw [charactersTerm, ByteString.characters_fromCharacters? chars, stringAtoms?_exact elements]
  | atom _ => cases read
  | var _ => cases read
  | expr _ => cases read
  | rest _ _ => cases read

theorem charactersTerm_injective :
    Function.Injective (charactersTerm (Other := Other) (Var := Var)) := by
  intro first second equal
  have read := congrArg stringFromTerm? equal
  simpa only [stringFromTerm?_charactersTerm, Option.some.injEq] using read

theorem stringFromTerm?_eq_some_iff (value : StringTerm Other Var) (text : String) :
    stringFromTerm? value = some text ↔ charactersTerm text = value := by
  constructor
  · exact charactersTerm_of_read
  · intro equal
    rw [← equal, stringFromTerm?_charactersTerm]

theorem charactersTerm_ofList (chars : List Char) :
    (charactersTerm (String.ofList chars) : StringTerm Other Var) =
      .list (chars.map characterAtom) := by
  simp [charactersTerm, ByteString.characters, characterAtom, List.map_map, Function.comp_def]

@[simp] theorem subst_stringAtom (σ : Var → StringTerm Other Var) (text : String) :
    subst σ (stringAtom text) = stringAtom text := by simp [subst, stringAtom]

@[simp] theorem subst_charactersTerm (σ : Var → StringTerm Other Var) (text : String) :
    subst σ (charactersTerm text) = charactersTerm text := by
  simp [charactersTerm, subst, List.map_map, Function.comp_def]

/-- Ordinary head/rest matching, transported from the proved first-order decomposition. -/
theorem head_rest_solution_iff {Leaf : Type} (σ : Var → Term Leaf Var)
    (head rest first : Term Leaf Var) (remaining : List (Term Leaf Var)) :
    Equivalent (subst σ (.rest [head] rest)) (subst σ (.list (first :: remaining))) ↔
      Equivalent (subst σ head) (subst σ first) ∧
      Equivalent (subst σ rest) (subst σ (.list remaining)) := by
  rw [Encoding.solution_iff, Encoding.solution_iff, Encoding.solution_iff]
  simpa only [Encoding.encode, List.map_cons, List.map_nil] using
    ListPrefixMeeting.head_rest_iff (Encoding.encodeSubst σ) (Encoding.encode head)
      (Encoding.encode rest) (Encoding.encode first) (remaining.map Encoding.encode)

/-- A character view gives the same captures as an ordinary nonempty list. -/
theorem character_head_rest_iff (σ : Var → StringTerm Other Var)
    (head rest : StringTerm Other Var) (first : Char) (remaining : List Char) :
    Equivalent (subst σ (.rest [head] rest))
        (charactersTerm (String.ofList (first :: remaining))) ↔
      Equivalent (subst σ head) (characterAtom first) ∧
      Equivalent (subst σ rest) (charactersTerm (String.ofList remaining)) := by
  have law := head_rest_solution_iff σ head rest (characterAtom first)
    (remaining.map characterAtom)
  have full := charactersTerm_ofList (Other := Other) (Var := Var) (first :: remaining)
  rw [List.map_cons] at full
  rw [← full, ← charactersTerm_ofList remaining] at law
  simpa only [subst_charactersTerm, characterAtom, subst_stringAtom] using law

@[simp] theorem charactersTerm_empty :
    (charactersTerm "" : StringTerm Other Var) = .list [] := rfl

/-- The empty string's view is an empty list, not an empty-string element. -/
theorem empty_view_not_empty_string_atom :
    (charactersTerm "" : StringTerm Other Var) ≠ stringAtom "" := by
  intro h
  cases h

theorem empty_view_matches_empty_list (σ : Var → StringTerm Other Var) :
    Equivalent (subst σ (.list [])) (charactersTerm "") := by
  simp only [charactersTerm_empty, subst]
  exact .refl _

theorem head_rest_does_not_match_empty_view (σ : Var → StringTerm Other Var)
    (head rest : StringTerm Other Var) :
    ¬ Equivalent (subst σ (.rest [head] rest)) (charactersTerm "") := by
  intro matched
  have source : Equivalent (subst σ (.rest [head] rest)) (subst σ (.list [])) := by
    simpa [subst] using matched
  have encoded := (Encoding.solution_iff σ (.rest [head] rest) (.list [])).mp source
  apply ListPrefixMeeting.head_rest_ne_empty (Encoding.encodeSubst σ)
    (Encoding.encode head) (Encoding.encode rest)
  simpa only [Encoding.encode, List.map_cons, List.map_nil, ListPrefixMeeting.spine_nil,
    ListPrefixMeeting.close_none, ListPrefixMeeting.apply_nil] using encoded

theorem nonstring_element_rejected (other : Other) :
    stringFromTerm? (.list [.atom (.inr other)] : StringTerm Other Var) = none := rfl

theorem expression_carrier_rejected (values : List (StringTerm Other Var)) :
    stringFromTerm? (.expr values) = none := rfl

theorem variable_element_rejected (name : Var) :
    stringFromTerm? (.list [.var name] : StringTerm Other Var) = none := rfl

example : stringFromTerm? (.list [stringAtom "ab"] : StringTerm Nat Nat) = none := by
  decide +kernel

example : stringFromTerm? (.list [stringAtom ""] : StringTerm Nat Nat) = none := by
  decide +kernel

example : (charactersTerm "héj" : StringTerm Nat Nat) =
    .list [stringAtom "h", stringAtom "é", stringAtom "j"] := by
  have chars : ByteString.characters "héj" = ["h", "é", "j"] := by decide +kernel
  rw [charactersTerm, chars]
  rfl

example : (charactersTerm "e\u0301" : StringTerm Nat Nat) =
    .list [stringAtom "e", stringAtom "\u0301"] := by
  have chars : ByteString.characters "e\u0301" = ["e", "\u0301"] := by decide +kernel
  rw [charactersTerm, chars]
  rfl

theorem hej_head_rest_iff (σ : Nat → StringTerm Other Nat) :
    Equivalent (subst σ (.rest [.var 0] (.var 1))) (charactersTerm "héj") ↔
      Equivalent (σ 0) (stringAtom "h") ∧ Equivalent (σ 1) (charactersTerm "éj") := by
  have full : String.ofList ['h', 'é', 'j'] = "héj" := by decide +kernel
  have tail : String.ofList ['é', 'j'] = "éj" := by decide +kernel
  have first : String.singleton 'h' = "h" := by decide +kernel
  simpa only [full, tail, subst, characterAtom, first] using
    character_head_rest_iff σ (.var 0) (.var 1) 'h' ['é', 'j']

#print axioms stringFromTerm?_charactersTerm
#print axioms charactersTerm_injective
#print axioms character_head_rest_iff
#print axioms head_rest_does_not_match_empty_view
#print axioms hej_head_rest_iff

end Mettapedia.Logic.Unification.ListStringView
