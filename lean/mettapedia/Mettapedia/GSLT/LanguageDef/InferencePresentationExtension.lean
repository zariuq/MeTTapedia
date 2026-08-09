import Mettapedia.GSLT.LanguageDef.InferenceChecker

/-!
# Presentation extensions as first-class validated objects

`RuleLookupRefines` promises only that prior rule lookups survive; a
COMPOSITIONAL presentation calculus needs more: the extension as data
(new constructors, judgments, rules), executable disjointness from its
base, validity of the composite, an EXPLICIT conservativity policy over
the base's judgments, preservation of old derivations, and identity and
associativity laws for composing extensions.  This module provides that
calculus; the PeTTa typing tower (core → guard → determinism) instantiates
it so the composed checker is one validated object built through typed
interfaces rather than ad-hoc list appends.

Conservativity here is a POLICY with executable content: under
`newJudgmentsOnly`, every added rule concludes a judgment head the base
does not declare, so the extension cannot change what was derivable about
the base's own judgments at the root of any derivation
(`lookup_concluding_base_judgment_is_base` makes that root-classification
executable-checkable; the full derivation-level conservativity theorem
builds on it in the correspondence arc).
-/

namespace Mettapedia.GSLT.LanguageDef.InferencePresentationExtension

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-- An extension delta: what a layer ADDS to a base presentation. -/
structure PresentationExtension where
  newTerms : List GrammarRule
  newJudgments : List JudgmentDecl
  newRules : List RuleSchema
  /-- Optional composite name; `none` keeps the base's. -/
  rename : Option String := none
deriving Repr

namespace PresentationExtension

/-- Apply the delta to a base presentation.  Term declarations extend the
five-field language; proof declarations extend only its attached calculus. -/
def apply (extension : PresentationExtension) (base : Presentation) :
    Presentation :=
  { language :=
      { base.language with
        name := extension.rename.getD base.language.name
        terms := base.language.terms ++ extension.newTerms }
    calculus :=
      { base.calculus with
        judgments := base.judgments ++ extension.newJudgments
        rules := base.rules ++ extension.newRules } }

/-- Executable disjointness: no constructor label, judgment head, or rule
identifier of the extension collides with the base. -/
def disjointFrom (extension : PresentationExtension)
    (base : Presentation) : Bool :=
  extension.newTerms.all (fun term =>
    !(base.language.terms.any fun existing => existing.label == term.label)) &&
  extension.newJudgments.all (fun judgment =>
    !(base.judgments.any fun existing =>
        existing.head == judgment.head)) &&
  extension.newRules.all (fun rule =>
    !(base.rules.any fun existing => existing.id == rule.id))

/-- The identity extension. -/
def empty : PresentationExtension := ⟨[], [], [], none⟩

/-- Sequential composition of deltas. -/
def comp (first second : PresentationExtension) : PresentationExtension :=
  { newTerms := first.newTerms ++ second.newTerms
    newJudgments := first.newJudgments ++ second.newJudgments
    newRules := first.newRules ++ second.newRules
    rename := second.rename <|> first.rename }

/-- Left identity law. -/
theorem empty_apply (base : Presentation) : empty.apply base = base := by
  cases base
  simp [empty, apply]

/-- Associativity: composing deltas then applying equals applying in
sequence. -/
theorem comp_apply (first second : PresentationExtension)
    (base : Presentation) :
    (first.comp second).apply base = second.apply (first.apply base) := by
  cases base
  simp only [comp, apply, List.append_assoc]
  cases second.rename <;> cases first.rename <;> simp [Option.getD]

/-- Composition of deltas is associative. -/
theorem comp_assoc (first second third : PresentationExtension) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  simp [comp, List.append_assoc, Option.or_assoc]

theorem empty_comp (extension : PresentationExtension) :
    empty.comp extension = extension := by
  simp [empty, comp]

theorem comp_empty (extension : PresentationExtension) :
    extension.comp empty = extension := by
  simp [empty, comp]

/-- Conservativity policy: the executable discipline governing how the
extension's rules relate to the BASE's judgments. -/
inductive ConservativityPolicy where
  /-- Every added rule concludes a judgment head the base does not
  declare: the base's own judgments gain no new root derivations. -/
  | newJudgmentsOnly
  /-- The extension deliberately adds derivations for the named base
  judgment heads (an explicit, audited non-conservative extension). -/
  | extendsBaseJudgments (heads : List String)
deriving Repr

/-- Executable check of the policy against the delta. -/
def policyHolds (extension : PresentationExtension)
    (base : Presentation) : ConservativityPolicy → Bool
  | .newJudgmentsOnly =>
      extension.newRules.all fun rule =>
        match rule.conclusion with
        | .apply head _ =>
            !(base.judgments.any fun judgment => judgment.head == head)
        | _ => false
  | .extendsBaseJudgments heads =>
      extension.newRules.all fun rule =>
        match rule.conclusion with
        | .apply head _ =>
            !(base.judgments.any fun judgment => judgment.head == head) ||
            heads.contains head
        | _ => false

end PresentationExtension

/-- A validated extension: the delta, its policy, and the proofs that make
the composite a first-class validated presentation. -/
structure ValidatedExtension (base : ValidatedPresentation) where
  extension : PresentationExtension
  policy : PresentationExtension.ConservativityPolicy
  disjoint : extension.disjointFrom base.1 = true
  policyHolds :
    extension.policyHolds base.1 policy = true
  valid :
    (extension.apply base.1).isValidV2 = true

namespace ValidatedExtension

variable {base : ValidatedPresentation}

/-- The composite as a validated presentation. -/
def target (self : ValidatedExtension base) : ValidatedPresentation :=
  ⟨self.extension.apply base.1, self.valid⟩

/-- Every base rule lookup survives into the composite: the extension is
proof-preserving by construction. -/
theorem refines (self : ValidatedExtension base) :
    RuleLookupRefines base self.target := by
  apply RuleLookupRefines.of_rules_eq_append self.extension.newRules
  rfl

/-- Old derivations transport unchanged into the composite. -/
def transport (self : ValidatedExtension base) {goal : Pattern}
    (derivation : Derivation base goal) :
    Derivation self.target goal :=
  derivation.transport self.refines

end ValidatedExtension

end Mettapedia.GSLT.LanguageDef.InferencePresentationExtension
