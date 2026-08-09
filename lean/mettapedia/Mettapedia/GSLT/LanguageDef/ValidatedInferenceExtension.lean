import Mettapedia.GSLT.LanguageDef.InferenceChecker

/-!
# Validated proof calculi as a fibre over term languages

`InferenceExtension` supplies the authored coGSLT and its raw elaborated
payload.  `InferenceChecker` supplies the admission predicate.  This module
combines them without adding fields to the term language.

For each term language, the fibre consists of proof calculi admitted against
that exact base.  Fibre morphisms preserve declared judgments, successful rule
lookup, and any conversion authority already present.  They form a preorder:
identity and composition are inherited from implication.  This is the
conservative-refinement structure used by proof consumers; raw list append is
not treated as a categorical composition.
-/

namespace Mettapedia.GSLT.LanguageDef.ValidatedInferenceExtension

open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The admitted proof-calculus fibre over one exact term language. -/
abbrev AdmittedCalculus (language : LanguageDef) :=
  { calculus : ProofCalculus //
    (Presentation.mk language calculus).isValidV2 = true }

/-- Validated proof calculi form an indexed extension layer. -/
def layer : ExtensionLayer LanguageDef where
  Fiber := AdmittedCalculus

/-- Repackage the checker's historical sigma subtype as the explicit fibre
total space. -/
def toAttached (presentation : ValidatedPresentation) : layer.Total :=
  ⟨presentation.1.language,
    ⟨presentation.1.calculus, presentation.2⟩⟩

/-- Recover the checker-facing validated presentation from a fibre object. -/
def ofAttached (attached : layer.Total) : ValidatedPresentation :=
  ⟨{ language := attached.1, calculus := attached.2.1 }, attached.2.2⟩

@[simp] theorem ofAttached_toAttached (presentation : ValidatedPresentation) :
    ofAttached (toAttached presentation) = presentation := by
  cases presentation with
  | mk presentation valid =>
      cases presentation
      rfl

@[simp] theorem toAttached_ofAttached (attached : layer.Total) :
    toAttached (ofAttached attached) = attached := by
  cases attached with
  | mk language calculus =>
      cases calculus
      rfl

/-- Raw lookup in one proof calculus. -/
def lookupRule? (calculus : ProofCalculus) (id : RuleId) :
    Option RuleSchema :=
  calculus.rules.find? fun rule => decide (rule.id = id)

/-- A conservative refinement inside one fibre.

The target may add judgments and rules.  It may also add the first conversion
authority, but it cannot replace one already declared by the source. -/
structure Refines {language : LanguageDef}
    (source target : AdmittedCalculus language) : Prop where
  judgments : ∀ declaration, declaration ∈ source.1.judgments →
    declaration ∈ target.1.judgments
  rules : ∀ id rule, lookupRule? source.1 id = some rule →
    lookupRule? target.1 id = some rule
  conversion : ∀ declaration, source.1.conversion = some declaration →
    target.1.conversion = some declaration

namespace Refines

@[refl] theorem refl {language : LanguageDef}
    (presentation : AdmittedCalculus language) :
    Refines presentation presentation where
  judgments := fun _ member => member
  rules := fun _ _ found => found
  conversion := fun _ declared => declared

@[trans] theorem trans {language : LanguageDef}
    {first second third : AdmittedCalculus language}
    (firstSecond : Refines first second)
    (secondThird : Refines second third) :
    Refines first third where
  judgments := fun declaration member =>
    secondThird.judgments declaration
      (firstSecond.judgments declaration member)
  rules := fun id rule found =>
    secondThird.rules id rule (firstSecond.rules id rule found)
  conversion := fun declaration declared =>
    secondThird.conversion declaration
      (firstSecond.conversion declaration declared)

end Refines

/-- The underlying term language is exactly conserved by every admitted
attachment. -/
@[simp] theorem erase_attached (language : LanguageDef)
    (calculus : AdmittedCalculus language) :
    layer.erase (layer.attach language calculus) = language :=
  rfl

/-- Negative canary: a fibre morphism cannot erase a declared conversion
authority. -/
theorem not_refines_of_conversion_removed {language : LanguageDef}
    (source target : AdmittedCalculus language) (declaration : ConversionDecl)
    (sourceDeclared : source.1.conversion = some declaration)
    (targetRemoved : target.1.conversion = none) :
    ¬ Refines source target := by
  intro refinement
  have := refinement.conversion declaration sourceDeclared
  rw [targetRemoved] at this
  contradiction

end Mettapedia.GSLT.LanguageDef.ValidatedInferenceExtension
