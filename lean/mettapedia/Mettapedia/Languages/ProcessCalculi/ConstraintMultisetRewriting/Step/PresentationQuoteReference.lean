import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationTermSource

/-!
# Rule references in the authored structural grammar

A rule reference is the existing nullary quoted-rule node. Reading it returns
an origin key, without looking up a rule or granting execution permission.
Every parse of the canonical reference recovers the same key. Source syntax
and its derivation remain available to a later activation interpreter.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.QuoteReference

open Mettapedia.GSLT.Parsing PresentationExprSemantics

def term (key : Nat) : Payloads.Term := .node (.quotedRule key) .nil

def read? : Payloads.Term → Option Nat
  | .node (.quotedRule key) .nil => some key
  | _ => none

def input (key : Nat) : List Nat := Source.termInput (term key)

def readTree? (tree : CST) : Option Nat := do
  let pattern ← LanguageDefScalarStructural.tree? tree
  let value ← Payloads.readTerm pattern
  read? value

theorem canonical_readback (key : Nat) {tree : CST}
    (parsed : Source.Parses "TcTerm" (input key) tree) : readTree? tree = some key := by
  have read := Source.read_canonical_term (term key) parsed
  cases found : LanguageDefScalarStructural.tree? tree with
  | none => simp [found] at read
  | some pattern =>
      have value : Payloads.readTerm pattern = some (term key) := by simpa only [found, Option.bind_some] using read
      simp only [readTree?, found, bind, Option.bind, value]
      rfl

structure Parsed (key : Nat) where
  input : List Nat
  tree : CST
  parsed : Source.Parses "TcTerm" input tree
  read : readTree? tree = some key

theorem canonical (key : Nat) : ∃ parsed : Parsed key, parsed.input = input key := by
  obtain ⟨tree, _, ⟨parsed⟩⟩ := Source.canonical_term_source (term key)
  exact ⟨⟨input key, tree, parsed, canonical_readback key parsed⟩, rfl⟩

noncomputable def readSource? (source : List Nat) : Option Nat := do
  let tree ← Source.parseTree "TcTerm" source
  readTree? tree

theorem readSource_print (key : Nat) : readSource? (input key) = some key := by
  obtain ⟨tree, _, ⟨parsed⟩⟩ := Source.canonical_term_source (term key)
  simp only [readSource?, input, Source.parseTree_of_derivation parsed, bind, Option.bind]
  exact canonical_readback key parsed

noncomputable def presentation : ExactPresentation.Presentation
    (fun _ : Unit => Nat) (fun _ => List Nat) where
  key := ⟨"tcalc.rule-reference", 1⟩
  view := input
  expand := readSource?
  expand_view := readSource_print

theorem wrong_document_key_refused
    (document : ExactPresentation.Document (fun _ : Unit => List Nat) ())
    (different : document.key ≠ presentation.key) :
    ExactPresentation.expandDocument presentation document = none :=
  ExactPresentation.expandDocument_wrong_key _ _ different

theorem key_unique {first second : Nat} {tree : CST}
    (left : readTree? tree = some first) (right : readTree? tree = some second) : first = second :=
  Option.some.inj (left.symm.trans right)

theorem nonempty_fields_refused (key depth : Nat) (body : Payloads.Term) (rest : Payloads.Fields) :
    read? (.node (.quotedRule key) (.cons depth body rest)) = none := rfl

theorem schematic_hole_is_not_a_rule_reference (key : Nat) : read? (.node (.hole key) .nil) = none := rfl

theorem ambient_variable_is_not_a_rule_reference (key : Nat) : read? (.idx key) = none := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.QuoteReference
