import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational

/-!
# Exact cold call-guard transition-family decoding

The cold call-guard compiler is authored as fifteen ordered `RewriteRule`
rows.  Structured lowering must inspect those rows rather than selecting code
from their names.  This module gives each supported row a finite family tag,
defines executable structural equality for complete rewrite rows, and admits a
`LanguageDef` only when its rewrite inventory is exactly the authored ordered
inventory.

The decoder is intentionally prior to StructuredC.  Its output is the finite,
typed control inventory from which later target syntax is folded.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileTransitionFamily

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational

/-- The complete finite family of cold compiler transitions.  Constructor
order is the authored source scheduling order. -/
inductive CompileTransitionFamily where
  | finish
  | skipHead
  | skipArity
  | beginDeclaration
  | argumentsFinished
  | rawInput
  | undefinedInput
  | holeInput
  | checkedInput
  | openInput
  | undefinedResult
  | holeResult
  | atomResult
  | checkedResult
  | openResult
deriving DecidableEq, Repr

/-- Reconstruct the complete authored row represented by a family tag. -/
def CompileTransitionFamily.rewrite : CompileTransitionFamily → RewriteRule
  | .finish => finishTransition
  | .skipHead => skipHeadTransition
  | .skipArity => skipArityTransition
  | .beginDeclaration => beginDeclarationTransition
  | .argumentsFinished => argumentsFinishedTransition
  | .rawInput => rawInputTransition
  | .undefinedInput => undefinedInputTransition
  | .holeInput => holeInputTransition
  | .checkedInput => checkedInputTransition
  | .openInput => openInputTransition
  | .undefinedResult => undefinedResultTransition
  | .holeResult => holeResultTransition
  | .atomResult => atomResultTransition
  | .checkedResult => checkedResultTransition
  | .openResult => openResultTransition

/-- The sole admitted cold scheduling inventory. -/
def orderedFamilies : List CompileTransitionFamily :=
  [ .finish
  , .skipHead
  , .skipArity
  , .beginDeclaration
  , .argumentsFinished
  , .rawInput
  , .undefinedInput
  , .holeInput
  , .checkedInput
  , .openInput
  , .undefinedResult
  , .holeResult
  , .atomResult
  , .checkedResult
  , .openResult ]

@[simp] theorem orderedFamilies_length : orderedFamilies.length = 15 := by
  decide

theorem orderedFamilies_nodup : orderedFamilies.Nodup := by
  decide

/-- Executable equality for complete rewrite rows.  All five fields are
compared: name, metavariable context, ordered premises, left pattern, and right
pattern.  This is local to source authentication; it does not change the
global `RewriteRule` API. -/
def rewriteRuleDecidableEq : DecidableEq RewriteRule := fun left right => by
  cases left
  cases right
  rw [RewriteRule.mk.injEq]
  infer_instance

local instance : DecidableEq RewriteRule := rewriteRuleDecidableEq

/-- A Boolean audit surface for the exact structural comparison used by the
decoder. -/
def rewriteRulesEqual (left right : RewriteRule) : Bool :=
  decide (left = right)

@[simp] theorem rewriteRulesEqual_eq_true_iff
    (left right : RewriteRule) :
    rewriteRulesEqual left right = true ↔ left = right := by
  simp [rewriteRulesEqual]

@[simp] theorem rewriteRulesEqual_eq_false_iff
    (left right : RewriteRule) :
    rewriteRulesEqual left right = false ↔ left ≠ right := by
  simp [rewriteRulesEqual]

/-- The family name narrows the candidate row; the second check compares the
complete row.  A correct name with a changed context, premise, or pattern is
therefore rejected. -/
def familyForName? (name : String) : Option CompileTransitionFamily :=
  if name = finishTransition.name then some .finish
  else if name = skipHeadTransition.name then some .skipHead
  else if name = skipArityTransition.name then some .skipArity
  else if name = beginDeclarationTransition.name then some .beginDeclaration
  else if name = argumentsFinishedTransition.name then some .argumentsFinished
  else if name = rawInputTransition.name then some .rawInput
  else if name = undefinedInputTransition.name then some .undefinedInput
  else if name = holeInputTransition.name then some .holeInput
  else if name = checkedInputTransition.name then some .checkedInput
  else if name = openInputTransition.name then some .openInput
  else if name = undefinedResultTransition.name then some .undefinedResult
  else if name = holeResultTransition.name then some .holeResult
  else if name = atomResultTransition.name then some .atomResult
  else if name = checkedResultTransition.name then some .checkedResult
  else if name = openResultTransition.name then some .openResult
  else none

/-- Decode one row only when both its scheduling name and its complete
structure identify the same authored family. -/
def decodeTransition? (rewrite : RewriteRule) :
    Option CompileTransitionFamily :=
  match familyForName? rewrite.name with
  | none => none
  | some family =>
      if rewrite = family.rewrite then some family else none

@[simp] theorem decodeTransition?_rewrite
    (family : CompileTransitionFamily) :
    decodeTransition? family.rewrite = some family := by
  cases family <;>
    simp [decodeTransition?, familyForName?, CompileTransitionFamily.rewrite,
      finishTransition, skipHeadTransition, skipArityTransition,
      beginDeclarationTransition, argumentsFinishedTransition,
      rawInputTransition, undefinedInputTransition, holeInputTransition,
      checkedInputTransition, openInputTransition, undefinedResultTransition,
      holeResultTransition, atomResultTransition, checkedResultTransition,
      openResultTransition, inputStepTransition, resultStepTransition]

/-- Successful single-row decoding is equivalent to exact reconstruction.
This is the principal anti-spoofing law: the tag contains no authority beyond
the row that was actually inspected. -/
theorem decodeTransition?_eq_some_iff
    (rewrite : RewriteRule) (family : CompileTransitionFamily) :
    decodeTransition? rewrite = some family ↔ rewrite = family.rewrite := by
  constructor
  · intro decoded
    unfold decodeTransition? at decoded
    split at decoded
    · contradiction
    · rename_i candidate candidateSelected
      split at decoded
      · rename_i exactRow
        have candidateEq : candidate = family := Option.some.inj decoded
        simpa [candidateEq] using exactRow
      · contradiction
  · rintro rfl
    exact decodeTransition?_rewrite family

/-- Decode two lists in lockstep.  Unlike `mapM decodeTransition?`, the expected
family at each position is explicit, so reordered, duplicated, omitted, and
extra rows fail closed. -/
def decodeInventory? :
    List RewriteRule → List CompileTransitionFamily →
      Option (List CompileTransitionFamily)
  | [], [] => some []
  | rewrite :: rewrites, family :: families =>
      if rewrite = family.rewrite then
        (decodeInventory? rewrites families).map (family :: ·)
      else
        none
  | _, _ => none

/-- Lockstep decoding succeeds exactly on the re-encoded expected inventory,
and returns precisely that inventory. -/
theorem decodeInventory?_eq_some_iff
    (rewrites : List RewriteRule)
    (expected decoded : List CompileTransitionFamily) :
    decodeInventory? rewrites expected = some decoded ↔
      rewrites = expected.map CompileTransitionFamily.rewrite ∧
        decoded = expected := by
  induction expected generalizing rewrites decoded with
  | nil =>
      cases rewrites <;> simp [decodeInventory?]
  | cons family families inductionHypothesis =>
      cases rewrites with
      | nil => simp [decodeInventory?]
      | cons rewrite rewrites =>
          by_cases exactRow : rewrite = family.rewrite
          · subst rewrite
            simp [decodeInventory?, inductionHypothesis, eq_comm]
          · simp [decodeInventory?, exactRow]

/-- Authenticate the rewrite inventory of a language definition.  Other
language fields remain available to later target-typing proofs; this function
has the deliberately narrow responsibility of admitting the cold control
rows. -/
def decodeLanguage? (source : LanguageDef) :
    Option (List CompileTransitionFamily) :=
  decodeInventory? source.rewrites orderedFamilies

theorem decodeLanguage?_eq_some_iff
    (source : LanguageDef) (decoded : List CompileTransitionFamily) :
    decodeLanguage? source = some decoded ↔
      source.rewrites =
          orderedFamilies.map CompileTransitionFamily.rewrite ∧
        decoded = orderedFamilies := by
  exact decodeInventory?_eq_some_iff source.rewrites orderedFamilies decoded

@[simp] theorem orderedFamilies_reencode :
    orderedFamilies.map CompileTransitionFamily.rewrite = transitions := by
  rfl

/-- The live authored cold language passes structural authentication. -/
theorem language_decodes_exactly :
    decodeLanguage? language = some orderedFamilies := by
  rw [decodeLanguage?_eq_some_iff]
  exact ⟨by rfl, rfl⟩

/-- Any admitted language has exactly the live ordered rewrite rows and no
others. -/
theorem decodeLanguage?_success_exact
    {source : LanguageDef} {decoded : List CompileTransitionFamily}
    (success : decodeLanguage? source = some decoded) :
    source.rewrites = transitions ∧ decoded = orderedFamilies := by
  rw [decodeLanguage?_eq_some_iff] at success
  simpa using success

/-- Fail-closed rejection is exact: a language is rejected precisely when its
rewrite rows differ from the complete authored inventory. -/
theorem decodeLanguage?_eq_none_iff (source : LanguageDef) :
    decodeLanguage? source = none ↔ source.rewrites ≠ transitions := by
  constructor
  · intro rejected rowsExact
    have accepted : decodeLanguage? source = some orderedFamilies :=
      (decodeLanguage?_eq_some_iff source orderedFamilies).2
        ⟨by simpa using rowsExact, rfl⟩
    rw [rejected] at accepted
    contradiction
  · intro rowsDifferent
    cases decoded : decodeLanguage? source with
    | none => rfl
    | some families =>
        exact (rowsDifferent (decodeLanguage?_success_exact decoded).1).elim

/-- Successful decoding entails the complete fifteen-family coverage and
excludes duplicate family tags. -/
theorem decodeLanguage?_success_inventory
    {source : LanguageDef} {decoded : List CompileTransitionFamily}
    (success : decodeLanguage? source = some decoded) :
    decoded.length = 15 ∧ decoded.Nodup := by
  obtain ⟨_, rfl⟩ := decodeLanguage?_success_exact success
  exact ⟨orderedFamilies_length, orderedFamilies_nodup⟩

#print axioms rewriteRulesEqual_eq_true_iff
#print axioms decodeTransition?_eq_some_iff
#print axioms decodeInventory?_eq_some_iff
#print axioms language_decodes_exactly
#print axioms decodeLanguage?_success_exact
#print axioms decodeLanguage?_eq_none_iff
#print axioms decodeLanguage?_success_inventory

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileTransitionFamily
