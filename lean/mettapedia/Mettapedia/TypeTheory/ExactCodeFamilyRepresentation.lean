import Mettapedia.Computability.ReflectiveCode
import Mettapedia.TypeTheory.ExactCodeModalityModel

/-!
# Universe-polymorphic exact code for dependent families

Iterated exact-code layers act pointwise on an arbitrary dependent family.
Quotation and splicing act on sections, commute with reindexing, and satisfy
literal beta and eta.  Code depths compose by addition.

This is the representation-theoretic part of contextual staging at arbitrary
universes.  It does not supply a mode theory, locking discipline, operational
communication rule, or cost interpretation.  Those are separate structures
even when they later use this exact representation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ExactCodeFamilyRepresentation

open Mettapedia.Computability.ReflectiveCode
open Mettapedia.TypeTheory.ExactCodeModalityModel

universe uContext uFibre

/-- Add the selected number of exact representation layers to every fibre. -/
def codeFamily (depth : Nat) {Context : Type uContext}
    (family : Context → Type uFibre) : Context → Type uFibre :=
  fun point => ExactCodeIter depth (family point)

/-- Quote a dependent section pointwise. -/
def quoteSection (depth : Nat) {Context : Type uContext}
    {family : Context → Type uFibre}
    (term : ∀ point, family point) :
    ∀ point, codeFamily depth family point :=
  fun point => quoteIter depth (term point)

/-- Splice a dependent code section pointwise. -/
def spliceSection (depth : Nat) {Context : Type uContext}
    {family : Context → Type uFibre}
    (term : ∀ point, codeFamily depth family point) :
    ∀ point, family point :=
  fun point => spliceIter depth (term point)

/-- Pointwise code depths compose additively. -/
theorem codeFamily_add (earlier later : Nat)
    {Context : Type uContext} (family : Context → Type uFibre) :
    codeFamily (earlier + later) family =
      codeFamily later (codeFamily earlier family) := by
  funext point
  exact exactCodeIter_add earlier later (family point)

/-- Quotation commutes exactly with context reindexing. -/
theorem quoteSection_reindex (depth : Nat)
    {Source : Type uContext} {Target : Type uContext}
    (substitution : Source → Target)
    {family : Target → Type uFibre}
    (term : ∀ point, family point) :
    quoteSection depth (fun point => term (substitution point)) =
      fun point => quoteSection depth term (substitution point) :=
  rfl

/-- Splicing commutes exactly with context reindexing. -/
theorem spliceSection_reindex (depth : Nat)
    {Source : Type uContext} {Target : Type uContext}
    (substitution : Source → Target)
    {family : Target → Type uFibre}
    (term : ∀ point, codeFamily depth family point) :
    spliceSection depth (fun point => term (substitution point)) =
      fun point => spliceSection depth term (substitution point) :=
  rfl

/-- Splicing a quoted section recovers it exactly. -/
theorem splice_quote_section (depth : Nat)
    {Context : Type uContext} {family : Context → Type uFibre}
    (term : ∀ point, family point) :
    spliceSection depth (quoteSection depth term) = term := by
  funext point
  exact splice_quote depth (term point)

/-- Quoting a spliced code section recovers the code exactly. -/
theorem quote_splice_section (depth : Nat)
    {Context : Type uContext} {family : Context → Type uFibre}
    (term : ∀ point, codeFamily depth family point) :
    quoteSection depth (spliceSection depth term) = term := by
  funext point
  exact quote_splice depth (term point)

/-- Exact code on sections as the generic reflective-code interface. -/
def sectionInterface (depth : Nat)
    {Context : Type uContext} (family : Context → Type uFibre) :
    Interface (∀ point, family point)
      (∀ point, codeFamily depth family point) where
  quote := quoteSection depth
  drop := spliceSection depth

/-- The pointwise section interface has literal beta. -/
theorem sectionInterface_beta (depth : Nat)
    {Context : Type uContext} (family : Context → Type uFibre) :
    (sectionInterface depth family).StaticBeta :=
  splice_quote_section depth

/-- The pointwise section interface has literal eta. -/
theorem sectionInterface_eta (depth : Nat)
    {Context : Type uContext} (family : Context → Type uFibre) :
    (sectionInterface depth family).StaticEta :=
  quote_splice_section depth

/-- Consequently sections and their exact codes are equivalent at every
universe level. -/
def sectionEquiv (depth : Nat)
    {Context : Type uContext} (family : Context → Type uFibre) :
    (∀ point, family point) ≃
      (∀ point, codeFamily depth family point) :=
  Interface.exactEquiv (sectionInterface depth family)
    (sectionInterface_beta depth family)
    (sectionInterface_eta depth family)

/-! ## Positive and negative controls -/

abbrev LargeBool := ULift.{1, 0} Bool

def boolFamily : PUnit → Type 1 := fun _ => LargeBool

def falseSection : ∀ point, boolFamily point :=
  fun _ => ULift.up false

def trueSection : ∀ point, boolFamily point :=
  fun _ => ULift.up true

/-- A positive code depth visibly retains the distinction between sections. -/
theorem oneLayer_quotes_distinct :
    quoteSection 1 falseSection ≠ quoteSection 1 trueSection := by
  intro equal
  have equalAtUnit := congrFun equal PUnit.unit
  have equalBodies := congrArg ExactCodeLayer.body equalAtUnit
  exact Bool.false_ne_true (congrArg ULift.down equalBodies)

/-- A constant one-token representation cannot satisfy beta even for the
two Boolean sections. -/
theorem constant_token_cannot_splice_all_sections :
    ¬ ∃ splice : PUnit → LargeBool,
      ∀ term : ∀ point, boolFamily point,
        splice PUnit.unit = term PUnit.unit := by
  rintro ⟨splice, beta⟩
  have falseResult := beta falseSection
  have trueResult := beta trueSection
  have falseEqualsTrue : (ULift.up false : LargeBool) = ULift.up true :=
    falseResult.symm.trans trueResult
  exact Bool.false_ne_true (congrArg ULift.down falseEqualsTrue)

/-- Exact nonidentity representation and the constant-token obstruction
coexist at the large universe used by the shared set-family semantics. -/
theorem exact_large_representation_boundary :
    (sectionInterface 1 boolFamily).StaticBeta ∧
      (sectionInterface 1 boolFamily).StaticEta ∧
      quoteSection 1 falseSection ≠ quoteSection 1 trueSection ∧
      ¬ ∃ splice : PUnit → LargeBool,
        ∀ term : ∀ point, boolFamily point,
          splice PUnit.unit = term PUnit.unit :=
  ⟨sectionInterface_beta 1 boolFamily,
    sectionInterface_eta 1 boolFamily,
    oneLayer_quotes_distinct,
    constant_token_cannot_splice_all_sections⟩

#print axioms codeFamily_add
#print axioms quoteSection_reindex
#print axioms spliceSection_reindex
#print axioms splice_quote_section
#print axioms quote_splice_section
#print axioms sectionEquiv
#print axioms oneLayer_quotes_distinct
#print axioms constant_token_cannot_splice_all_sections
#print axioms exact_large_representation_boundary

end Mettapedia.TypeTheory.ExactCodeFamilyRepresentation
