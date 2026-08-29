import Mettapedia.GSLT.LanguageDef.InferenceChecker

/-!
# Flat calculus-language extensions

`RuleLookupRefines` promises only that prior rule lookups survive; a
compositional language calculus needs more: the extension as data
(new sorts, constructors, equations, rewrites, judgments, and rules),
executable disjointness from its
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

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-- An extension delta: every row family a layer may add to one flat calculus
language.  Defaults keep narrow inference-only deltas ergonomic, while the
same operation also composes generated syntax and operational rules. -/
structure CalculusLanguageExtension where
  newTypes : List TypeDecl := []
  newTerms : List GrammarRule := []
  newEquations : List Equation := []
  newRewrites : List RewriteRule := []
  newJudgments : List JudgmentDecl := []
  newRules : List RuleSchema := []
  /-- Optional composite name; `none` keeps the base's. -/
  rename : Option String := none
deriving Repr

namespace CalculusLanguageExtension

/-- Apply the delta directly to one flat language object. -/
def apply (extension : CalculusLanguageExtension) (base : CalculusLanguageDef) :
    CalculusLanguageDef :=
  { base with
    name := extension.rename.getD base.name
    types := base.types ++ extension.newTypes
    terms := base.terms ++ extension.newTerms
    equations := base.equations ++ extension.newEquations
    rewrites := base.rewrites ++ extension.newRewrites
    judgments := base.judgments ++ extension.newJudgments
    rules := base.rules ++ extension.newRules }

@[simp] theorem apply_types (extension : CalculusLanguageExtension)
    (base : CalculusLanguageDef) :
    (extension.apply base).types = base.types ++ extension.newTypes :=
  rfl

@[simp] theorem apply_terms (extension : CalculusLanguageExtension)
    (base : CalculusLanguageDef) :
    (extension.apply base).terms = base.terms ++ extension.newTerms :=
  rfl

@[simp] theorem apply_equations (extension : CalculusLanguageExtension)
    (base : CalculusLanguageDef) :
    (extension.apply base).equations =
      base.equations ++ extension.newEquations :=
  rfl

@[simp] theorem apply_rewrites (extension : CalculusLanguageExtension)
    (base : CalculusLanguageDef) :
    (extension.apply base).rewrites = base.rewrites ++ extension.newRewrites :=
  rfl

@[simp] theorem apply_judgments (extension : CalculusLanguageExtension)
    (base : CalculusLanguageDef) :
    (extension.apply base).judgments =
      base.judgments ++ extension.newJudgments :=
  rfl

@[simp] theorem apply_rules (extension : CalculusLanguageExtension)
    (base : CalculusLanguageDef) :
    (extension.apply base).rules = base.rules ++ extension.newRules :=
  rfl

/-- Executable disjointness: no authored name of the extension collides with
the corresponding namespace of the base. -/
def disjointFrom (extension : CalculusLanguageExtension)
    (base : CalculusLanguageDef) : Bool :=
  extension.newTypes.all (fun declaration =>
    !(base.types.any fun existing => existing.name == declaration.name)) &&
  extension.newTerms.all (fun term =>
    !(base.terms.any fun existing => existing.label == term.label)) &&
  extension.newEquations.all (fun equation =>
    !(base.equations.any fun existing => existing.name == equation.name)) &&
  extension.newRewrites.all (fun rewrite =>
    !(base.rewrites.any fun existing => existing.name == rewrite.name)) &&
  extension.newJudgments.all (fun judgment =>
    !(base.judgments.any fun existing =>
        existing.head == judgment.head)) &&
  extension.newRules.all (fun rule =>
    !(base.rules.any fun existing => existing.id == rule.id))

/-- The identity extension. -/
def empty : CalculusLanguageExtension := {}

/-- Sequential composition of deltas. -/
def comp (first second : CalculusLanguageExtension) : CalculusLanguageExtension :=
  { newTypes := first.newTypes ++ second.newTypes
    newTerms := first.newTerms ++ second.newTerms
    newEquations := first.newEquations ++ second.newEquations
    newRewrites := first.newRewrites ++ second.newRewrites
    newJudgments := first.newJudgments ++ second.newJudgments
    newRules := first.newRules ++ second.newRules
    rename := second.rename <|> first.rename }

/-- Left identity law. -/
theorem empty_apply (base : CalculusLanguageDef) : empty.apply base = base := by
  cases base
  simp [empty, apply]

/-- Associativity: composing deltas then applying equals applying in
sequence. -/
theorem comp_apply (first second : CalculusLanguageExtension)
    (base : CalculusLanguageDef) :
    (first.comp second).apply base = second.apply (first.apply base) := by
  cases base
  simp only [comp, apply, List.append_assoc]
  cases second.rename <;> cases first.rename <;> simp [Option.getD]

/-- Composition of deltas is associative. -/
theorem comp_assoc (first second third : CalculusLanguageExtension) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  simp [comp, List.append_assoc, Option.or_assoc]

theorem empty_comp (extension : CalculusLanguageExtension) :
    empty.comp extension = extension := by
  simp [empty, comp]

theorem comp_empty (extension : CalculusLanguageExtension) :
    extension.comp empty = extension := by
  simp [empty, comp]

/-! ## Canonical residual of an append-only refinement -/

/-- Every ordered row family of `source` is an exact prefix of `target`.
Conversion is not list-valued and therefore must remain unchanged.  A target
name may differ: the residual extension records it explicitly. -/
structure AppendOnlyCalculusRefinement
    (source target : CalculusLanguageDef) : Prop where
  types : source.types.IsPrefix target.types
  terms : source.terms.IsPrefix target.terms
  equations : source.equations.IsPrefix target.equations
  rewrites : source.rewrites.IsPrefix target.rewrites
  judgments : source.judgments.IsPrefix target.judgments
  rules : source.rules.IsPrefix target.rules
  conversion : target.conversion = source.conversion

/-- Applying an extension is append-only in every ordered row family.  This
is the generic bridge from the extension monoid action to incremental
compilation; no generator has to re-prove the six prefix obligations. -/
theorem apply_appendOnly (extension : CalculusLanguageExtension)
    (base : CalculusLanguageDef) :
    AppendOnlyCalculusRefinement base (extension.apply base) := by
  constructor
  · exact List.prefix_append _ _
  · exact List.prefix_append _ _
  · exact List.prefix_append _ _
  · exact List.prefix_append _ _
  · exact List.prefix_append _ _
  · exact List.prefix_append _ _
  · rfl

namespace AppendOnlyCalculusRefinement

private theorem append_drop_eq_of_prefix {α : Type _}
    {first second : List α} (isPrefix : first.IsPrefix second) :
    first ++ second.drop first.length = second := by
  rcases isPrefix with ⟨suffix, rfl⟩
  simp

/-- The unique executable row suffix selected by an append-only refinement. -/
def residual {source target : CalculusLanguageDef}
    (_refinement : AppendOnlyCalculusRefinement source target) :
    CalculusLanguageExtension :=
  { newTypes := target.types.drop source.types.length
    newTerms := target.terms.drop source.terms.length
    newEquations := target.equations.drop source.equations.length
    newRewrites := target.rewrites.drop source.rewrites.length
    newJudgments := target.judgments.drop source.judgments.length
    newRules := target.rules.drop source.rules.length
    rename := some target.name }

/-- Extracting and applying the residual reconstructs the target exactly.
This is the generic bridge from prefix theorems to incremental compilation. -/
theorem residual_apply {source target : CalculusLanguageDef}
    (refinement : AppendOnlyCalculusRefinement source target) :
    refinement.residual.apply source = target := by
  apply CalculusLanguageDef.ext
  · rfl
  · exact append_drop_eq_of_prefix refinement.types
  · exact append_drop_eq_of_prefix refinement.terms
  · exact append_drop_eq_of_prefix refinement.equations
  · exact append_drop_eq_of_prefix refinement.rewrites
  · exact append_drop_eq_of_prefix refinement.judgments
  · exact append_drop_eq_of_prefix refinement.rules
  · exact refinement.conversion.symm

/-! ### Positive and negative controls -/

namespace Canary

private def firstType : TypeDecl :=
  TypeDecl.plain "append-only-calculus:first"

private def secondType : TypeDecl :=
  TypeDecl.plain "append-only-calculus:second"

private def insertedType : TypeDecl :=
  TypeDecl.plain "append-only-calculus:inserted"

private def source : CalculusLanguageDef :=
  { name := "append-only-calculus:source"
    types := [firstType, secondType]
    terms := []
    equations := []
    rewrites := [] }

private def appendedTarget : CalculusLanguageDef :=
  { name := "append-only-calculus:target"
    types := [firstType, secondType, insertedType]
    terms := []
    equations := []
    rewrites := [] }

private def appended : AppendOnlyCalculusRefinement source appendedTarget where
  types := by simp [source, appendedTarget]
  terms := by simp [source, appendedTarget]
  equations := by simp [source, appendedTarget]
  rewrites := by simp [source, appendedTarget]
  judgments := by simp [source, appendedTarget]
  rules := by simp [source, appendedTarget]
  conversion := rfl

/-- A genuine suffix is recovered and reapplied without regenerating the
already compiled source rows. -/
theorem appended_target_reconstructed :
    appended.residual.apply source = appendedTarget :=
  appended.residual_apply

private def middleInsertion : CalculusLanguageDef :=
  { name := "append-only-calculus:middle-insertion"
    types := [firstType, insertedType, secondType]
    terms := []
    equations := []
    rewrites := [] }

/-- Inserting a declaration into the middle is not mislabeled as an
append-only refinement. -/
theorem middle_insertion_rejected :
    ¬ AppendOnlyCalculusRefinement source middleInsertion := by
  intro refinement
  have typesPrefix := refinement.types
  rw [List.prefix_iff_eq_take] at typesPrefix
  simp [source, middleInsertion, firstType, secondType, insertedType,
    TypeDecl.plain] at typesPrefix

end Canary

end AppendOnlyCalculusRefinement

/-! ## Order-sensitive controls -/

namespace Canary

private def firstType : TypeDecl := TypeDecl.plain "extension-order:first"
private def secondType : TypeDecl := TypeDecl.plain "extension-order:second"

private def first : CalculusLanguageExtension :=
  { newTypes := [firstType] }

private def second : CalculusLanguageExtension :=
  { newTypes := [secondType] }

/-- Composition retains authored order in every row family. -/
theorem composed_type_order :
    (first.comp second).newTypes = [firstType, secondType] :=
  rfl

/-- Extension composition is associative but intentionally not commutative:
authored order remains observable. -/
theorem comp_not_commutative : first.comp second ≠ second.comp first := by
  intro equality
  have typeRows := congrArg CalculusLanguageExtension.newTypes equality
  simp [first, second, comp, firstType, secondType, TypeDecl.plain] at typeRows

end Canary

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
def policyHolds (extension : CalculusLanguageExtension)
    (base : CalculusLanguageDef) : ConservativityPolicy → Bool
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

end CalculusLanguageExtension

/-- A validated extension: the delta, its policy, and the proofs that make
the composite a first-class checked language definition. -/
structure ValidatedCalculusLanguageExtension (base : ValidatedCalculusLanguageDef) where
  extension : CalculusLanguageExtension
  policy : CalculusLanguageExtension.ConservativityPolicy
  disjoint : extension.disjointFrom base.1 = true
  policyHolds :
    extension.policyHolds base.1 policy = true
  valid :
    (extension.apply base.1).isValid = true

namespace ValidatedCalculusLanguageExtension

variable {base : ValidatedCalculusLanguageDef}

/-- The composite as a validated flat language definition. -/
def target (self : ValidatedCalculusLanguageExtension base) : ValidatedCalculusLanguageDef :=
  ⟨self.extension.apply base.1, self.valid⟩

/-- Every base rule lookup survives into the composite: the extension is
proof-preserving by construction. -/
theorem refines (self : ValidatedCalculusLanguageExtension base) :
    RuleLookupRefines base self.target := by
  apply RuleLookupRefines.of_rules_eq_append self.extension.newRules
  rfl

/-- Old derivations transport unchanged into the composite. -/
def transport (self : ValidatedCalculusLanguageExtension base) {goal : Pattern}
    (derivation : Derivation base goal) :
    Derivation self.target goal :=
  derivation.transport self.refines

end ValidatedCalculusLanguageExtension

#print axioms CalculusLanguageExtension.comp_apply
#print axioms CalculusLanguageExtension.comp_assoc
#print axioms CalculusLanguageExtension.AppendOnlyCalculusRefinement.residual_apply
#print axioms CalculusLanguageExtension.AppendOnlyCalculusRefinement.Canary.appended_target_reconstructed
#print axioms CalculusLanguageExtension.AppendOnlyCalculusRefinement.Canary.middle_insertion_rejected
#print axioms CalculusLanguageExtension.Canary.composed_type_order
#print axioms CalculusLanguageExtension.Canary.comp_not_commutative

end Mettapedia.GSLT.LanguageDef
