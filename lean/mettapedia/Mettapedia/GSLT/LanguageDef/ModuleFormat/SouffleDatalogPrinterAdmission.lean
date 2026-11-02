import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterFormation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterLexicalLaws
import Init.Data.Nat.ToString

/-! Source admission for the independent Datalog printer is expressed using
the declared lexical classes and IR shape. These conditions do not invoke the
printer. Every admitted lexical value constructs formed source-core data. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing ParserProfileSemantics
open Formation

def Allowed (row : ScalarCore.Row) (character : Char) : Prop :=
  SourceViews.profile.ClassEvidence (ScalarCore.lexicalState row).className character.toNat

def Identifier (name : String) : Prop :=
  name ∉ SourcePolicy.reservedWords ∧ match name.toList with
  | [] => False
  | [character] => Allowed ⟨0, by decide⟩ character
  | first :: rest => Allowed ⟨1, by decide⟩ first ∧ ∀ character ∈ rest, Allowed ⟨2, by decide⟩ character

def Qualified (name : List String) : Prop := name ≠ [] ∧ ∀ part ∈ name, Identifier part

theorem scalar_total (row : ScalarCore.Row) (character : Char) (allowed : Allowed row character) :
    ∃ pattern, scalar? (ScalarCore.lexicalState row).resultSort character = .ok pattern ∧
      Formed (ScalarCore.lexicalState row).resultSort pattern := by
  refine ⟨ScalarCore.leaf row character.toNat allowed, scalar_complete row character allowed, ?_⟩
  exact ScalarSyntaxCore.Formed.scalar (description := description) row character.toNat allowed

theorem identifier_tail_total (characters : List Char) (nonempty : characters ≠ [])
    (allowed : ∀ character ∈ characters, Allowed ⟨2, by decide⟩ character) :
    ∃ pattern, identifierTail? characters = .ok pattern ∧ Formed "DlIdentifierNonempty" pattern := by
  induction characters with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest ih =>
    obtain ⟨head, headRead, headFormed⟩ := scalar_total ⟨2, by decide⟩ first (allowed first (List.mem_cons_self))
    change scalar? "DlIdentifierRestScalar" first = .ok head at headRead
    change Formed "DlIdentifierRestScalar" head at headFormed
    cases rest with
    | nil => exact ⟨_, by simp [identifierTail?, headRead], Formation.identifier_tail_one headFormed⟩
    | cons second tail =>
      obtain ⟨body, bodyRead, bodyFormed⟩ := ih (by simp) (fun character member => allowed character (List.mem_cons_of_mem _ member))
      exact ⟨_, by simp [identifierTail?, headRead, bodyRead, bind, Except.bind, pure, Except.pure], Formation.identifier_tail_more headFormed bodyFormed⟩

theorem identifier_total (name : String) (allowed : Identifier name) :
    ∃ pattern, identifier? name = .ok pattern ∧ Formed "DlIdentifier" pattern := by
  obtain ⟨notReserved, allowed⟩ := allowed
  cases chars : name.toList with
  | nil => simp [chars] at allowed
  | cons first rest =>
    cases rest with
    | nil =>
      have admissible : Allowed ⟨0, by decide⟩ first := by simpa [chars] using allowed
      obtain ⟨head, headRead, headFormed⟩ := scalar_total ⟨0, by decide⟩ first admissible
      change scalar? "DlSingleIdentifierScalar" first = .ok head at headRead
      change Formed "DlSingleIdentifierScalar" head at headFormed
      exact ⟨_, by simp [identifier?, notReserved, chars, headRead], Formation.identifier_one headFormed⟩
    | cons second tail =>
      have admissible : Allowed ⟨1, by decide⟩ first ∧ ∀ character ∈ second :: tail, Allowed ⟨2, by decide⟩ character := by
        simpa [chars] using allowed
      obtain ⟨head, headRead, headFormed⟩ := scalar_total ⟨1, by decide⟩ first admissible.1
      obtain ⟨body, bodyRead, bodyFormed⟩ := identifier_tail_total (second :: tail) (by simp) admissible.2
      change scalar? "DlIdentifierFirstScalar" first = .ok head at headRead
      change Formed "DlIdentifierFirstScalar" head at headFormed
      exact ⟨_, by simp [identifier?, notReserved, chars, headRead, bodyRead, bind, Except.bind, pure, Except.pure], Formation.identifier_more headFormed bodyFormed⟩

theorem qualified_total (names : List String) (allowed : Qualified names) :
    ∃ pattern, qualifiedName? names = .ok pattern ∧ Formed "DlQualifiedName" pattern := by
  induction names with
  | nil => exact False.elim (allowed.1 rfl)
  | cons first rest ih =>
    obtain ⟨head, headRead, headFormed⟩ := identifier_total first (allowed.2 first List.mem_cons_self)
    cases rest with
    | nil => exact ⟨_, by simp [qualifiedName?, headRead], Formation.qualified_name_one headFormed⟩
    | cons second tail =>
      obtain ⟨body, bodyRead, bodyFormed⟩ := ih ⟨by simp, fun name member => allowed.2 name (List.mem_cons_of_mem _ member)⟩
      exact ⟨_, by simp [qualifiedName?, headRead, bodyRead, bind, Except.bind, pure, Except.pure], Formation.qualified_name_more headFormed bodyFormed⟩

theorem digit_allowed (character : Char) (digit : character.isDigit = true) : Allowed ⟨3, by decide⟩ character := by
  have bounds := Char.isDigit_iff_toNat.mp digit
  change 48 ≤ character.toNat ∧ character.toNat ≤ 57 at bounds
  obtain ⟨lower, upper⟩ := bounds
  interval_cases point : character.toNat <;> simp [Allowed, point] <;> decide +kernel

theorem digits_total (characters : List Char) (nonempty : characters ≠ [])
    (digits : ∀ character ∈ characters, character.isDigit = true) :
    ∃ pattern, digits? characters = .ok pattern ∧ Formed "DlDigits" pattern := by
  induction characters with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest ih =>
    obtain ⟨head, headRead, headFormed⟩ := scalar_total ⟨3, by decide⟩ first (digit_allowed first (digits first List.mem_cons_self))
    change scalar? "DlDigitScalar" first = .ok head at headRead
    change Formed "DlDigitScalar" head at headFormed
    cases rest with
    | nil => exact ⟨_, by simp [digits?, headRead], Formation.digits_one headFormed⟩
    | cons second tail =>
      obtain ⟨body, bodyRead, bodyFormed⟩ := ih (by simp) (fun character member => digits character (List.mem_cons_of_mem _ member))
      exact ⟨_, by simp [digits?, headRead, bodyRead, bind, Except.bind, pure, Except.pure], Formation.digits_more headFormed bodyFormed⟩

theorem decimal_total (number : Nat) :
    ∃ pattern, digits? number.repr.toList = .ok pattern ∧ Formed "DlDigits" pattern := by
  apply digits_total
  · simpa only [Nat.toList_repr] using (Nat.toDigits_ne_nil (n := number) (b := 10))
  · intro character member
    rw [Nat.toList_repr] at member
    exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) member

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter
