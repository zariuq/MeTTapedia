import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Conservative extensions of a five-field language

A language definition is five fields: name, types, terms, equations,
rewrites.  Everything a proof calculus needs — judgment signatures, rule
schemas — is *additional authored information*, and this module gives it a
home **beside** the core rather than inside it.

The structure is a **fibration**, not a sheaf.  Extensions live over cores;
`erase` is the projection; the fibre over a core is the set of extensions
that are well-formed relative to it.  Sheaves and gluing would be the further
question of reconstructing a global extension from local ones agreeing on
overlaps — a descent condition, which conservativity does not need and which
should not be claimed before covers exist.

Three things make this a real fibration rather than a product wearing one as
a costume.

* **The fibre genuinely depends on the base.**  `Extension.fresh` requires
  declared judgments not to collide with the base's own constructors.  That
  is the freshness condition conservativity rests on, and it mentions the
  base.
* **Reindexing exists and has the right variance.**  Freshness against a
  larger core is a stronger condition, so an extension over a larger base
  restricts to one over a smaller — `Extension.restrict`, contravariant, as a
  fibration requires.
* **Each fibre is a monoid.**  Extensions over one base compose associatively
  with an identity, so a language may be extended in stages and the order of
  independent stages does not matter.

Conservativity is then structural rather than argued:
`extension_preserves_core` says the base's terms, equations and rewrites are
*literally* unchanged.  Its triviality is the point — the design makes
conservativity hold by construction, which is precisely what putting these
fields in the root record gave up.

And the extensions are themselves ordinary GSLT programs.
`extensionLanguage` is a five-field language whose constructors are
declaration forms, and `decodeJudgment?_encodeJudgment` round-trips judgment
declarations through it.  So "the inference rules are described by a GSLT" is
a fact about an encoding, not a slogan.

What is *not* here is named at the end: rule-schema encoding, and the
specialization theorem that would compile an extension back into core
rewrites.
-/

namespace Mettapedia.GSLT.Core.ConservativeExtension

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Core.NonFactorization

/-! ## The core -/

/-- The five mathematical fields of a language.  Nothing else. -/
structure CoreLanguage where
  name : String
  types : List TypeDecl
  terms : List GrammarRule
  equations : List Equation
  rewrites : List RewriteRule

/-- The core underlying today's record.  Everything else it carries is
extension data that has been stored in the wrong place. -/
def coreOf (language : LanguageDef) : CoreLanguage where
  name := language.name
  types := language.types
  terms := language.terms
  equations := language.equations
  rewrites := language.rewrites

/-- Constructor labels a core declares. -/
def CoreLanguage.constructorLabels (base : CoreLanguage) : List String :=
  base.terms.map GrammarRule.label

/-! ## Judgment heads mentioned by a rule -/

/-- The head symbol at the root of a pattern, when it has one. -/
def rootHead? : Pattern → Option String
  | .apply head _ => some head
  | _ => none

/-- Every judgment a rule schema mentions, premises and conclusion alike. -/
def judgmentHeadsOf (rule : RuleSchema) : List String :=
  (rule.conclusion :: rule.premises).filterMap rootHead?

/-! ## The fibre over a core -/

/-- An extension of `base`: declared judgments and rule schemas, subject to
two conditions that make it well-formed *relative to that base*. -/
structure Extension (base : CoreLanguage) where
  /-- Judgment signatures introduced by this extension. -/
  newJudgments : List JudgmentDecl
  /-- Rule schemas over them. -/
  newRules : List RuleSchema
  /-- **Freshness.**  No declared judgment collides with a constructor of the
  base.  This is what keeps the extension from redefining the language. -/
  fresh : ∀ judgment ∈ newJudgments,
    judgment.head ∉ base.constructorLabels
  /-- **Groundedness.**  Every judgment a rule mentions is declared here, so
  no rule reaches outside the extension. -/
  grounded : ∀ rule ∈ newRules, ∀ head ∈ judgmentHeadsOf rule,
    head ∈ newJudgments.map JudgmentDecl.head

/-- The total space: a core together with an extension of it. -/
structure ExtendedLanguage where
  base : CoreLanguage
  extension : Extension base

/-- **The projection of the fibration.** -/
def ExtendedLanguage.erase (extended : ExtendedLanguage) : CoreLanguage :=
  extended.base

@[simp] theorem erase_mk (base : CoreLanguage) (extension : Extension base) :
    ExtendedLanguage.erase ⟨base, extension⟩ = base := rfl

/-! ## Conservativity, by construction

The base's operational content is not merely preserved up to some relation —
it is the same data.  That is what makes the placement conservative without
an argument. -/

/-- **An extension adds no operational content.**  Terms, equations and
rewrites survive verbatim, so every fact about the base's behaviour survives
with them. -/
theorem extension_preserves_core (base : CoreLanguage) (extension : Extension base) :
    (ExtendedLanguage.erase ⟨base, extension⟩).terms = base.terms ∧
      (ExtendedLanguage.erase ⟨base, extension⟩).equations = base.equations ∧
      (ExtendedLanguage.erase ⟨base, extension⟩).rewrites = base.rewrites :=
  ⟨rfl, rfl, rfl⟩

/-- And erasure recovers the base exactly, so nothing is lost by the round
trip through an extension. -/
theorem erase_extend (base : CoreLanguage) (extension : Extension base) :
    ExtendedLanguage.erase ⟨base, extension⟩ = base := rfl

/-! ## Each fibre is a monoid

Extensions over one base compose, so a language may be extended in stages. -/

/-- The empty extension. -/
def Extension.empty (base : CoreLanguage) : Extension base where
  newJudgments := []
  newRules := []
  fresh := by intro _ membership; cases membership
  grounded := by intro _ membership; cases membership

/-- Compose two extensions over one base. -/
def Extension.compose {base : CoreLanguage} (first second : Extension base) :
    Extension base where
  newJudgments := first.newJudgments ++ second.newJudgments
  newRules := first.newRules ++ second.newRules
  fresh := by
    intro judgment membership
    rcases List.mem_append.mp membership with fromFirst | fromSecond
    · exact first.fresh judgment fromFirst
    · exact second.fresh judgment fromSecond
  grounded := by
    intro rule membership head mentioned
    rw [List.map_append]
    rcases List.mem_append.mp membership with fromFirst | fromSecond
    · exact List.mem_append.mpr (Or.inl (first.grounded rule fromFirst head mentioned))
    · exact List.mem_append.mpr (Or.inr (second.grounded rule fromSecond head mentioned))

/-- Two extensions over one base are equal when their declarations are: the
well-formedness fields are propositions. -/
theorem Extension.ext {base : CoreLanguage} {first second : Extension base}
    (judgments : first.newJudgments = second.newJudgments)
    (rules : first.newRules = second.newRules) : first = second := by
  cases first
  cases second
  simp only at judgments rules
  subst judgments
  subst rules
  rfl

@[simp] theorem Extension.compose_empty_left {base : CoreLanguage}
    (extension : Extension base) :
    (Extension.empty base).compose extension = extension :=
  Extension.ext (by simp [Extension.compose, Extension.empty])
    (by simp [Extension.compose, Extension.empty])

@[simp] theorem Extension.compose_empty_right {base : CoreLanguage}
    (extension : Extension base) :
    extension.compose (Extension.empty base) = extension :=
  Extension.ext (by simp [Extension.compose, Extension.empty])
    (by simp [Extension.compose, Extension.empty])

theorem Extension.compose_assoc {base : CoreLanguage}
    (first second third : Extension base) :
    (first.compose second).compose third =
      first.compose (second.compose third) :=
  Extension.ext (by simp [Extension.compose, List.append_assoc])
    (by simp [Extension.compose, List.append_assoc])

/-! ## Reindexing, with the variance a fibration requires

Freshness against a larger core is the stronger condition, so extensions
restrict *down* along an inclusion of cores. -/

/-- One core's constructors include another's. -/
def CoreLanguage.Includes (smaller larger : CoreLanguage) : Prop :=
  ∀ label ∈ smaller.constructorLabels, label ∈ larger.constructorLabels

/-- **Reindexing.**  An extension of a larger core is an extension of any
core it includes: freshness against more constructors implies freshness
against fewer. -/
def Extension.restrict {smaller larger : CoreLanguage}
    (inclusion : CoreLanguage.Includes smaller larger)
    (extension : Extension larger) : Extension smaller where
  newJudgments := extension.newJudgments
  newRules := extension.newRules
  fresh := by
    intro judgment membership collides
    exact extension.fresh judgment membership (inclusion _ collides)
  grounded := extension.grounded

/-- Reindexing keeps the declarations, so it really is a change of base and
not a change of content. -/
@[simp] theorem Extension.restrict_newJudgments {smaller larger : CoreLanguage}
    (inclusion : CoreLanguage.Includes smaller larger) (extension : Extension larger) :
    (extension.restrict inclusion).newJudgments = extension.newJudgments := rfl

/-! ## Extensions are genuine data

The complementary fact: the base does not determine its extension, so an
extension is information rather than a redundant restatement. -/

/-- A core with no constructors, over which freshness is vacuous. -/
def emptyCore : CoreLanguage where
  name := "empty"
  types := []
  terms := []
  equations := []
  rewrites := []

private def soleJudgment : JudgmentDecl := { head := "Typed", arity := 2 }

/-- A non-empty extension of the empty core. -/
def oneJudgmentExtension : Extension emptyCore where
  newJudgments := [soleJudgment]
  newRules := []
  fresh := by intro _ _; simp [emptyCore, CoreLanguage.constructorLabels]
  grounded := by intro _ membership; cases membership

/-- The judgments an extended language declares, as a view of the total
space. -/
def ExtendedLanguage.declaredJudgments (extended : ExtendedLanguage) :
    List JudgmentDecl :=
  extended.extension.newJudgments

/-- Two extended languages with the same base and different extensions. -/
def extensionFiber :
    NonTrivialFiber ExtendedLanguage.erase ExtendedLanguage.declaredJudgments where
  left := ⟨emptyCore, Extension.empty emptyCore⟩
  right := ⟨emptyCore, oneJudgmentExtension⟩
  sameShadow := rfl
  differentValue := by
    simp [ExtendedLanguage.declaredJudgments, Extension.empty, oneJudgmentExtension]

/-- **A core does not determine its extension.**  So a proof calculus is
authored information, and storing it in the root record was storing something
the record cannot justify. -/
theorem extension_not_determined_by_core :
    ¬ Factors ExtendedLanguage.erase ExtendedLanguage.declaredJudgments :=
  extensionFiber.not_factors

/-! ## Extensions are themselves GSLT programs

The declaration language is an ordinary five-field core, and declarations
encode into its patterns.  So an extension is a program of a language, not a
new kind of object. -/

private def declType : TypeDecl := TypeDecl.plain "Decl"

private def declConstructor (label : String) : GrammarRule :=
  { label := label, category := "Decl", params := [], syntaxPattern := [] }

/-- **The coGSLT in which extensions are written.**  Five fields, no
extensions of its own — the declaration language is not privileged. -/
def extensionLanguage : CoreLanguage where
  name := "gslt-extension-decl"
  types := [declType]
  terms :=
    [ declConstructor "judgment", declConstructor "rule",
      declConstructor "zero", declConstructor "succ" ]
  equations := []
  rewrites := []

/-- Arities as patterns.  Unary is deliberate: it keeps the encoding
self-contained and provable, and a production encoding would use whatever
numeral form the object language already has. -/
def encodeNat : Nat → Pattern
  | 0 => .apply "zero" []
  | count + 1 => .apply "succ" [encodeNat count]

def decodeNat? : Pattern → Option Nat
  | .apply "zero" [] => some 0
  | .apply "succ" [inner] => (decodeNat? inner).map (· + 1)
  | _ => none

@[simp] theorem decodeNat?_encodeNat (count : Nat) :
    decodeNat? (encodeNat count) = some count := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp [encodeNat, decodeNat?, inductionHypothesis]

/-- A judgment declaration as a pattern of the declaration language. -/
def encodeJudgment (judgment : JudgmentDecl) : Pattern :=
  .apply "judgment" [.apply judgment.head [], encodeNat judgment.arity]

def decodeJudgment? : Pattern → Option JudgmentDecl
  | .apply "judgment" [.apply head [], arity] =>
      (decodeNat? arity).map fun count => { head := head, arity := count }
  | _ => none

/-- **Declarations round-trip through the declaration language.**  So the
extension data really is a program of an ordinary GSLT, and the claim that
inference rules are described by a GSLT is a fact about this encoding rather
than an aspiration. -/
@[simp] theorem decodeJudgment?_encodeJudgment (judgment : JudgmentDecl) :
    decodeJudgment? (encodeJudgment judgment) = some judgment := by
  cases judgment
  simp [encodeJudgment, decodeJudgment?]

/-- Encoding is injective, which is the same fact in the form the criterion
uses: nothing about a declaration is lost on the way into the language. -/
theorem encodeJudgment_injective : Function.Injective encodeJudgment := by
  intro first second sameEncoding
  have decoded : decodeJudgment? (encodeJudgment first) =
      decodeJudgment? (encodeJudgment second) := by rw [sameEncoding]
  rw [decodeJudgment?_encodeJudgment, decodeJudgment?_encodeJudgment] at decoded
  exact Option.some.inj decoded

/-! ## What is not here

Named so none of it is mistaken for done.

* **Rule-schema encoding.**  Only judgment declarations round-trip.  Rules
  carry metavariables with binder depths and pattern bodies, and encoding
  them faithfully means preserving that depth discipline — a separate piece
  of work, not a longer version of this one.
* **Specialization.**  Nothing here compiles an extension back into ordinary
  core rewrites, and nothing claims a generic interpreter agrees with such a
  compilation.  That is the staging theorem and it is untouched.
* **Descent.**  The structure proved here is a fibration.  Gluing compatible
  extensions over a cover is a further condition that has not been stated,
  let alone proved.
-/

end Mettapedia.GSLT.Core.ConservativeExtension
