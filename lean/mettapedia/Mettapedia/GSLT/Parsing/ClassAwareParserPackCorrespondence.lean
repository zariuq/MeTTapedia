import Mettapedia.GSLT.Parsing.ParserProfileSemantics
import Mettapedia.GSLT.Parsing.PresentationExprSemantics

/-!
# Class-aware lexical correspondence for ParserPack

This module formalizes the lexical part of the authored-profile to ParserPack
transformation.  It covers exact characters, Unicode scalar classes, the
`any` matcher, and EOF.  In particular, complement classes are interpreted by
their actual profile semantics rather than expanded into a finite guard set.

Source recognition and compiled matching are distinct proof-relevant
relations.  Their exact-CST fibres are equivalent for every lexical state,
and the compiler retains the source-state occurrence as production evidence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence

open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
open Mettapedia.GSLT.Parsing.ParserProfileSemantics
open Mettapedia.GSLT.Parsing.PresentationExprSemantics
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A physical occurrence in an ordered list.  Equal payloads at distinct
positions remain distinct because the position, rather than propositional
membership, is the identity. -/
abbrev ListOccurrence {α : Type*} (entries : List α) := Fin entries.length

/-- Transport an occurrence through a length-preserving `List.map`. -/
def ListOccurrence.map {α β : Type*} {entries : List α}
    (occurrence : ListOccurrence entries) (f : α → β) :
    ListOccurrence (entries.map f) :=
  ⟨occurrence.val, by
    rw [List.length_map]
    exact occurrence.isLt⟩

@[simp] theorem ListOccurrence.get_map
    {α β : Type*} {entries : List α}
    (occurrence : ListOccurrence entries) (f : α → β) :
    (entries.map f).get (occurrence.map f) = f (entries.get occurrence) := by
  simp [ListOccurrence.map]

/-- The terminal matcher fragment carried by the ParserPack ABI. -/
inductive TerminalMatcher where
  | any
  | eof
  | char (codepoint : Nat)
  | class (className : String)
  deriving DecidableEq, Repr

/-- One lexical production emitted from an authored lexical state.  Slot zero
is retained because the lexical CST node contains its exact scalar leaf. -/
structure CompiledLexicalProduction where
  label : String
  resultSort : String
  matcher : TerminalMatcher
  childSlots : List Nat
  deriving DecidableEq, Repr

def compileLexicalState
    (state : LexicalStateDecl) : CompiledLexicalProduction := {
  label := state.ruleLabel
  resultSort := state.resultSort
  matcher := .class state.className
  childSlots := [0]
}

def compileLexicalProductions
    (profile : ParserProfileLayer) : List CompiledLexicalProduction :=
  profile.states.map compileLexicalState

/-- The lexical portion of a compiled pack retains the complete class table,
not merely class names in productions.  Consequently a change to an exclusion
set changes the artifact even when all production labels remain fixed. -/
structure CompiledLexicalPack where
  profileName : String
  startSort : String
  classes : List LexicalClassDecl
  productions : List CompiledLexicalProduction
  deriving DecidableEq, Repr

def compileLexicalPack
    (profile : ParserProfileLayer) : CompiledLexicalPack := {
  profileName := profile.name
  startSort := profile.startSort
  classes := profile.classes
  productions := compileLexicalProductions profile
}

@[simp] theorem compileLexicalPack_classes
    (profile : ParserProfileLayer) :
    (compileLexicalPack profile).classes = profile.classes :=
  rfl

@[simp] theorem compileLexicalPack_productions
    (profile : ParserProfileLayer) :
    (compileLexicalPack profile).productions =
      profile.states.map compileLexicalState :=
  rfl

/-! ## Structural ParserPack compilation plan -/

/-- ParserPack items after literal terminals have been expanded to Unicode
scalars. -/
inductive PackItem where
  | terminal (matcher : TerminalMatcher)
  | nonterminal (resultSort : String)
  deriving DecidableEq, Repr

/-- Expand one structurally admitted source atom.  Literal decoding remains
an explicit input; unknown spellings fail rather than becoming `any`. -/
def compileStructuralAtomItems?
    (literalScalars? : String → Option (List Nat)) :
    StructuralAtom → Option (List PackItem)
  | .terminal token _parserRef => do
      let codepoints ← literalScalars? token
      pure (codepoints.map fun codepoint =>
        .terminal (.char codepoint))
  | .nonterminal _parameter resultSort _parserRef =>
      some [.nonterminal resultSort]

def compileStructuralItems?
    (literalScalars? : String → Option (List Nat))
    (atoms : List StructuralAtom) : Option (List PackItem) := do
  let rows ← atoms.mapM (compileStructuralAtomItems? literalScalars?)
  pure rows.flatten

/-- Exact zero-based item slots retained by the ParserPack node action. -/
def nonterminalSlots (items : List PackItem) : List Nat :=
  (items.zipIdx.filterMap fun
    | (.nonterminal _, index) => some index
    | (.terminal _, _) => none)

/-- One structural production plus its source-row provenance.  Child slots
are explicit target data and are checked against the emitted item vector. -/
structure CompiledStructuralProduction where
  label : String
  resultSort : String
  items : List PackItem
  childSlots : List Nat
  source : GrammarRule
  deriving DecidableEq, Repr

def compileStructuralRule?
    (literalScalars? : String → Option (List Nat))
    (startSort : String) (rule : CompiledRule) :
    Option CompiledStructuralProduction := do
  let bodyItems ← compileStructuralItems? literalScalars? rule.atoms
  let items :=
    if rule.source.category == startSort then
      bodyItems ++ [.terminal .eof]
    else
      bodyItems
  pure {
    label := rule.source.label
    resultSort := rule.source.category
    items := items
    childSlots := nonterminalSlots items
    source := rule.source
  }

def compileStructuralProductions?
    (literalScalars? : String → Option (List Nat))
    (startSort : String) (rules : List CompiledRule) :
    Option (List CompiledStructuralProduction) :=
  rules.mapM (compileStructuralRule? literalScalars? startSort)

/-- A complete compilation plan joins the class-aware lexical artifact and
the structurally compiled authored rules. -/
structure CompiledParserPackPlan where
  lexical : CompiledLexicalPack
  structural : List CompiledStructuralProduction
  deriving DecidableEq, Repr

def compileParserPackPlan?
    (literalScalars? : String → Option (List Nat))
    (profile : ParserProfileLayer) (rules : List CompiledRule) :
    Option CompiledParserPackPlan := do
  let structural ←
    compileStructuralProductions? literalScalars? profile.startSort rules
  pure {
    lexical := compileLexicalPack profile
    structural := structural
  }

/-- Exact agreement tying an operational plan to the profile, literal
decoder, and ordered structural rules from which it was compiled. -/
structure ParserPackPlanAgreement
    (literalScalars? : String → Option (List Nat))
    (profile : ParserProfileLayer) (rules : List CompiledRule)
    (plan : CompiledParserPackPlan) : Prop where
  lexical_exact : plan.lexical = compileLexicalPack profile
  structural_exact :
    compileStructuralProductions? literalScalars? profile.startSort rules =
      some plan.structural

/-- Successful whole-plan compilation supplies exact operational agreement;
the profile and plan cannot later be paired independently. -/
theorem ParserPackPlanAgreement.of_compilation
    {literalScalars? : String → Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    {plan : CompiledParserPackPlan}
    (compiled : compileParserPackPlan? literalScalars? profile rules =
      some plan) :
    ParserPackPlanAgreement literalScalars? profile rules plan := by
  unfold compileParserPackPlan? at compiled
  cases structuralResult :
      compileStructuralProductions? literalScalars? profile.startSort rules with
  | none => simp [structuralResult] at compiled
  | some structural =>
      simp [structuralResult] at compiled
      subst plan
      exact ⟨rfl, structuralResult⟩

theorem ParserPackPlanAgreement.startSort_eq
    {literalScalars? : String → Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    {plan : CompiledParserPackPlan}
    (agreement :
      ParserPackPlanAgreement literalScalars? profile rules plan) :
    plan.lexical.startSort = profile.startSort := by
  rw [agreement.lexical_exact]
  rfl

/-- Ordered lexical-state occurrences and emitted lexical-production
occurrences are exactly equivalent.  This equivalence is positional: equal
states at different indices remain different inhabitants. -/
def ParserPackPlanAgreement.lexicalOccurrenceEquiv
    {literalScalars? : String → Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    {plan : CompiledParserPackPlan}
    (agreement :
      ParserPackPlanAgreement literalScalars? profile rules plan) :
    ListOccurrence profile.states ≃
      ListOccurrence plan.lexical.productions := by
  have lengthEq :
      profile.states.length = plan.lexical.productions.length := by
    rw [agreement.lexical_exact]
    simp [compileLexicalPack, compileLexicalProductions]
  exact {
    toFun := Fin.cast lengthEq
    invFun := Fin.cast lengthEq.symm
    left_inv := by
      intro occurrence
      apply Fin.ext
      rfl
    right_inv := by
      intro occurrence
      apply Fin.ext
      rfl
  }

theorem ParserPackPlanAgreement.lexical_length_eq
    {literalScalars? : String → Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    {plan : CompiledParserPackPlan}
    (agreement :
      ParserPackPlanAgreement literalScalars? profile rules plan) :
    profile.states.length = plan.lexical.productions.length := by
  rw [agreement.lexical_exact]
  simp [compileLexicalPack, compileLexicalProductions]

/-- Selecting corresponding lexical occurrences retrieves the exact
compiled state row. -/
theorem ParserPackPlanAgreement.lexical_get
    {literalScalars? : String → Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    {plan : CompiledParserPackPlan}
    (agreement :
      ParserPackPlanAgreement literalScalars? profile rules plan)
    (occurrence : ListOccurrence profile.states) :
    plan.lexical.productions.get
        (agreement.lexicalOccurrenceEquiv occurrence) =
      compileLexicalState (profile.states.get occurrence) := by
  simp [ParserPackPlanAgreement.lexicalOccurrenceEquiv,
    agreement.lexical_exact, compileLexicalPack, compileLexicalProductions]

/-- The inverse positional map also retrieves the exact source lexical row. -/
theorem ParserPackPlanAgreement.lexical_get_inverse
    {literalScalars? : String → Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    {plan : CompiledParserPackPlan}
    (agreement :
      ParserPackPlanAgreement literalScalars? profile rules plan)
    (occurrence : ListOccurrence plan.lexical.productions) :
    plan.lexical.productions.get occurrence =
      compileLexicalState
        (profile.states.get
          (agreement.lexicalOccurrenceEquiv.symm occurrence)) := by
  simpa using agreement.lexical_get
    (agreement.lexicalOccurrenceEquiv.symm occurrence)

/-- Successful production compilation retains the complete source rule. -/
theorem compileStructuralRule_source
    (literalScalars? : String → Option (List Nat))
    (startSort : String) (rule : CompiledRule)
    (production : CompiledStructuralProduction)
    (compiled : compileStructuralRule? literalScalars? startSort rule =
      some production) :
    production.source = rule.source := by
  unfold compileStructuralRule? at compiled
  cases itemResult : compileStructuralItems? literalScalars? rule.atoms with
  | none => simp [itemResult] at compiled
  | some items =>
      simp [itemResult] at compiled
      cases compiled
      rfl

/-- The action slots are determined by the emitted item vector itself; no
handwritten child-retention table can disagree with the production. -/
theorem compileStructuralRule_childSlots
    (literalScalars? : String → Option (List Nat))
    (startSort : String) (rule : CompiledRule)
    (production : CompiledStructuralProduction)
    (compiled : compileStructuralRule? literalScalars? startSort rule =
      some production) :
    production.childSlots = nonterminalSlots production.items := by
  unfold compileStructuralRule? at compiled
  cases itemResult : compileStructuralItems? literalScalars? rule.atoms with
  | none => simp [itemResult] at compiled
  | some items =>
      simp [itemResult] at compiled
      cases compiled
      rfl

/-- The whole successful map retains every source row in order and with
multiplicity. -/
theorem compileStructuralProductions_source
    (literalScalars? : String → Option (List Nat))
    (startSort : String) (rules : List CompiledRule)
    (productions : List CompiledStructuralProduction)
    (compiled : compileStructuralProductions? literalScalars? startSort rules =
      some productions) :
    productions.map (fun production => production.source) =
      rules.map (fun rule => rule.source) := by
  induction rules generalizing productions with
  | nil =>
      simp [compileStructuralProductions?] at compiled
      subst productions
      rfl
  | cons rule rules inductionHypothesis =>
      simp only [compileStructuralProductions?, List.mapM_cons,
        Option.bind_eq_bind] at compiled
      cases headResult :
          compileStructuralRule? literalScalars? startSort rule with
      | none => simp [headResult] at compiled
      | some production =>
          cases tailResult :
              rules.mapM (compileStructuralRule? literalScalars? startSort) with
          | none => simp [headResult, tailResult] at compiled
          | some tail =>
              simp [headResult, tailResult] at compiled
              subst productions
              simp [compileStructuralRule_source literalScalars? startSort
                rule production headResult,
                inductionHypothesis tail (by
                  simpa [compileStructuralProductions?] using tailResult)]

/-! ## Positional compilation evidence -/

/-- Pointwise evidence that ordered source rules compiled to ordered target
productions.  The cons shape retains list positions even when two rows have
equal payloads. -/
inductive StructuralRulesCompile
    (literalScalars? : String → Option (List Nat)) (startSort : String) :
    List CompiledRule → List CompiledStructuralProduction → Prop where
  | nil : StructuralRulesCompile literalScalars? startSort [] []
  | cons {rule : CompiledRule}
      {production : CompiledStructuralProduction}
      {rules : List CompiledRule}
      {productions : List CompiledStructuralProduction}
      (head : compileStructuralRule? literalScalars? startSort rule =
        some production)
      (tail : StructuralRulesCompile literalScalars? startSort
        rules productions) :
      StructuralRulesCompile literalScalars? startSort
        (rule :: rules) (production :: productions)

/-- Pointwise evidence that an authored structural-atom vector expanded to
an emitted ParserPack item vector.  A source terminal may expand to several
character items, while one source nonterminal expands to exactly one target
item. -/
inductive StructuralItemsCompile
    (literalScalars? : String → Option (List Nat)) :
    List StructuralAtom → List PackItem → Type where
  | nil : StructuralItemsCompile literalScalars? [] []
  | terminal {token parserRef : String} {codepoints : List Nat}
      {atoms : List StructuralAtom} {tailItems : List PackItem}
      (decoded : literalScalars? token = some codepoints)
      (tail : StructuralItemsCompile literalScalars? atoms tailItems) :
      StructuralItemsCompile literalScalars?
        (.terminal token parserRef :: atoms)
        ((codepoints.map fun codepoint => .terminal (.char codepoint)) ++
          tailItems)
  | nonterminal {parameter resultSort parserRef : String}
      {atoms : List StructuralAtom} {tailItems : List PackItem}
      (tail : StructuralItemsCompile literalScalars? atoms tailItems) :
      StructuralItemsCompile literalScalars?
        (.nonterminal parameter resultSort parserRef :: atoms)
        (.nonterminal resultSort :: tailItems)

/-- Successful list compilation yields exact pointwise expansion evidence. -/
def StructuralItemsCompile.of_compilation
    (literalScalars? : String → Option (List Nat)) :
    ∀ {atoms : List StructuralAtom} {items : List PackItem},
      compileStructuralItems? literalScalars? atoms = some items →
        StructuralItemsCompile literalScalars? atoms items := by
  intro atoms
  induction atoms with
  | nil =>
      intro items compiled
      simp [compileStructuralItems?] at compiled
      subst items
      exact .nil
  | cons atom atoms inductionHypothesis =>
      intro items compiled
      unfold compileStructuralItems? at compiled
      simp only [List.mapM_cons, Option.bind_eq_bind] at compiled
      cases atom with
      | terminal token parserRef =>
          cases decoded : literalScalars? token with
          | none =>
              simp [compileStructuralAtomItems?, decoded] at compiled
          | some codepoints =>
              cases tailResult :
                  atoms.mapM (compileStructuralAtomItems? literalScalars?) with
              | none =>
                  simp [compileStructuralAtomItems?, decoded, tailResult] at compiled
              | some rows =>
                  simp [compileStructuralAtomItems?, decoded, tailResult] at compiled
                  subst items
                  exact .terminal decoded <|
                    inductionHypothesis (by
                      unfold compileStructuralItems?
                      simp [tailResult])
      | nonterminal parameter resultSort parserRef =>
          cases tailResult :
              atoms.mapM (compileStructuralAtomItems? literalScalars?) with
          | none =>
              simp [compileStructuralAtomItems?, tailResult] at compiled
          | some rows =>
              simp [compileStructuralAtomItems?, tailResult] at compiled
              subst items
              exact .nonterminal <|
                inductionHypothesis (by
                  unfold compileStructuralItems?
                  simp [tailResult])

/-- The complete information exposed by one successful structural-rule
compilation.  This view prevents later proofs from treating the target row as
an independently authored table. -/
structure StructuralRuleCompileView
    (literalScalars? : String → Option (List Nat)) (startSort : String)
    (rule : CompiledRule) (production : CompiledStructuralProduction) where
  bodyItems : List PackItem
  body_compiled :
    compileStructuralItems? literalScalars? rule.atoms = some bodyItems
  items_exact : production.items =
    if rule.source.category = startSort then
      bodyItems ++ [.terminal .eof]
    else bodyItems
  label_exact : production.label = rule.source.label
  resultSort_exact : production.resultSort = rule.source.category
  source_exact : production.source = rule.source

/-- Successful compilation determines the complete structural-rule view.
The view contains data, but no second choice once source and target rows are
fixed. -/
instance StructuralRuleCompileView.instSubsingleton
    {literalScalars? : String → Option (List Nat)} {startSort : String}
    {rule : CompiledRule} {production : CompiledStructuralProduction} :
    Subsingleton (StructuralRuleCompileView literalScalars? startSort
      rule production) where
  allEq left right := by
    have bodyEq : left.bodyItems = right.bodyItems :=
      Option.some.inj (left.body_compiled.symm.trans right.body_compiled)
    cases left
    cases right
    simp_all

/-- Expose the exact body expansion and administrative EOF decision made by
one successful rule compilation. -/
def StructuralRuleCompileView.of_compilation
    (literalScalars? : String → Option (List Nat)) (startSort : String)
    (rule : CompiledRule) (production : CompiledStructuralProduction)
    (compiled : compileStructuralRule? literalScalars? startSort rule =
      some production) :
    StructuralRuleCompileView literalScalars? startSort rule production := by
  unfold compileStructuralRule? at compiled
  cases bodyResult : compileStructuralItems? literalScalars? rule.atoms with
  | none => simp [bodyResult] at compiled
  | some bodyItems =>
      simp [bodyResult] at compiled
      subst production
      exact {
        bodyItems := bodyItems
        body_compiled := bodyResult
        items_exact := rfl
        label_exact := rfl
        resultSort_exact := rfl
        source_exact := rfl
      }

/-- Every rule-compilation view contains pointwise atom-to-item expansion
evidence. -/
def StructuralRuleCompileView.itemCompilation
    {literalScalars? : String → Option (List Nat)} {startSort : String}
    {rule : CompiledRule} {production : CompiledStructuralProduction}
    (view : StructuralRuleCompileView literalScalars? startSort
      rule production) :
    StructuralItemsCompile literalScalars? rule.atoms view.bodyItems :=
  StructuralItemsCompile.of_compilation literalScalars? view.body_compiled

theorem StructuralRulesCompile.of_compilation
    (literalScalars? : String → Option (List Nat)) (startSort : String) :
    ∀ {rules : List CompiledRule}
      {productions : List CompiledStructuralProduction},
      compileStructuralProductions? literalScalars? startSort rules =
        some productions →
      StructuralRulesCompile literalScalars? startSort rules productions := by
  intro rules
  induction rules with
  | nil =>
      intro productions compiled
      simp [compileStructuralProductions?] at compiled
      subst productions
      exact .nil
  | cons rule rules inductionHypothesis =>
      intro productions compiled
      simp only [compileStructuralProductions?, List.mapM_cons,
        Option.bind_eq_bind] at compiled
      cases headResult :
          compileStructuralRule? literalScalars? startSort rule with
      | none => simp [headResult] at compiled
      | some production =>
          cases tailResult :
              rules.mapM (compileStructuralRule? literalScalars? startSort) with
          | none => simp [headResult, tailResult] at compiled
          | some tail =>
              simp [headResult, tailResult] at compiled
              subst productions
              exact .cons headResult <|
                inductionHypothesis (by
                  simpa [compileStructuralProductions?] using tailResult)

theorem StructuralRulesCompile.length_eq
    {literalScalars? : String → Option (List Nat)} {startSort : String}
    {rules : List CompiledRule}
    {productions : List CompiledStructuralProduction}
    (compilation : StructuralRulesCompile literalScalars? startSort
      rules productions) :
    rules.length = productions.length := by
  induction compilation with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [inductionHypothesis]

/-- Transport a source-row bound to the compiled row at the same raw
position.  Keeping the raw position definitionally unchanged prevents a
proof of list-length equality from becoming part of occurrence identity. -/
def StructuralRulesCompile.targetValid
    {literalScalars? : String → Option (List Nat)} {startSort : String}
    {rules : List CompiledRule}
    {productions : List CompiledStructuralProduction}
    (compilation : StructuralRulesCompile literalScalars? startSort
      rules productions)
    (position : Nat) (valid : position < rules.length) :
    position < productions.length := by
  rw [← compilation.length_eq]
  exact valid

/-- Transport a compiled-row bound back to the source row at the same raw
position. -/
def StructuralRulesCompile.sourceValid
    {literalScalars? : String → Option (List Nat)} {startSort : String}
    {rules : List CompiledRule}
    {productions : List CompiledStructuralProduction}
    (compilation : StructuralRulesCompile literalScalars? startSort
      rules productions)
    (position : Nat) (valid : position < productions.length) :
    position < rules.length := by
  rw [compilation.length_eq]
  exact valid

@[simp] theorem StructuralRulesCompile.sourceValid_targetValid
    {literalScalars? : String → Option (List Nat)} {startSort : String}
    {rules : List CompiledRule}
    {productions : List CompiledStructuralProduction}
    (compilation : StructuralRulesCompile literalScalars? startSort
      rules productions)
    (position : Nat) (valid : position < rules.length) :
    compilation.sourceValid position
        (compilation.targetValid position valid) = valid := by
  apply Subsingleton.elim

@[simp] theorem StructuralRulesCompile.targetValid_sourceValid
    {literalScalars? : String → Option (List Nat)} {startSort : String}
    {rules : List CompiledRule}
    {productions : List CompiledStructuralProduction}
    (compilation : StructuralRulesCompile literalScalars? startSort
      rules productions)
    (position : Nat) (valid : position < productions.length) :
    compilation.targetValid position
        (compilation.sourceValid position valid) = valid := by
  apply Subsingleton.elim

/-- The target occurrence at the same physical position as a source rule. -/
def StructuralRulesCompile.mapOccurrence
    {literalScalars? : String → Option (List Nat)} {startSort : String}
    {rules : List CompiledRule}
    {productions : List CompiledStructuralProduction}
    (compilation : StructuralRulesCompile literalScalars? startSort
      rules productions)
    (occurrence : ListOccurrence rules) : ListOccurrence productions :=
  ⟨occurrence.val,
    compilation.targetValid occurrence.val occurrence.isLt⟩

/-- Positional compilation is not merely length preservation: the selected
target occurrence is exactly the result of compiling the selected source
occurrence. -/
theorem StructuralRulesCompile.get_compiled
    {literalScalars? : String → Option (List Nat)} {startSort : String}
    {rules : List CompiledRule}
    {productions : List CompiledStructuralProduction}
    (compilation : StructuralRulesCompile literalScalars? startSort
      rules productions)
    (occurrence : ListOccurrence rules) :
    compileStructuralRule? literalScalars? startSort
        (rules.get occurrence) =
      some (productions.get (compilation.mapOccurrence occurrence)) := by
  induction compilation with
  | nil => exact Fin.elim0 occurrence
  | @cons rule production rules productions head tail inductionHypothesis =>
      cases occurrence using Fin.cases with
      | zero =>
          simpa [StructuralRulesCompile.mapOccurrence,
            StructuralRulesCompile.length_eq] using head
      | succ occurrence =>
          simpa [StructuralRulesCompile.mapOccurrence,
            StructuralRulesCompile.length_eq] using
              inductionHypothesis occurrence

/-- The positional source-to-target map is injective; equal compiled
productions at different positions do not collapse their occurrences. -/
theorem StructuralRulesCompile.mapOccurrence_injective
    {literalScalars? : String → Option (List Nat)} {startSort : String}
    {rules : List CompiledRule}
    {productions : List CompiledStructuralProduction}
    (compilation : StructuralRulesCompile literalScalars? startSort
      rules productions) :
    Function.Injective compilation.mapOccurrence := by
  intro left right equal
  apply Fin.ext
  have valueEqual := congrArg (fun occurrence => occurrence.val) equal
  simpa [StructuralRulesCompile.mapOccurrence] using valueEqual

/-- Ordered compilation yields an exact equivalence of source and target
occurrence positions, not merely an injection of equal payloads. -/
def StructuralRulesCompile.occurrenceEquiv
    {literalScalars? : String → Option (List Nat)} {startSort : String}
    {rules : List CompiledRule}
    {productions : List CompiledStructuralProduction}
    (compilation : StructuralRulesCompile literalScalars? startSort
      rules productions) :
    ListOccurrence rules ≃ ListOccurrence productions where
  toFun := compilation.mapOccurrence
  invFun occurrence :=
    ⟨occurrence.val,
      compilation.sourceValid occurrence.val occurrence.isLt⟩
  left_inv occurrence := by
    apply Fin.ext
    rfl
  right_inv occurrence := by
    apply Fin.ext
    rfl

@[simp] theorem StructuralRulesCompile.occurrenceEquiv_apply
    {literalScalars? : String → Option (List Nat)} {startSort : String}
    {rules : List CompiledRule}
    {productions : List CompiledStructuralProduction}
    (compilation : StructuralRulesCompile literalScalars? startSort
      rules productions) (occurrence : ListOccurrence rules) :
    compilation.occurrenceEquiv occurrence =
      compilation.mapOccurrence occurrence := rfl

@[simp] theorem StructuralRulesCompile.occurrenceEquiv_symm_mapOccurrence
    {literalScalars? : String → Option (List Nat)} {startSort : String}
    {rules : List CompiledRule}
    {productions : List CompiledStructuralProduction}
    (compilation : StructuralRulesCompile literalScalars? startSort
      rules productions) (occurrence : ListOccurrence rules) :
    compilation.occurrenceEquiv.symm
        (compilation.mapOccurrence occurrence) = occurrence :=
  compilation.occurrenceEquiv.symm_apply_apply occurrence

/-- The structural component of exact plan agreement supplies pointwise,
position-preserving compiler evidence. -/
def ParserPackPlanAgreement.structuralCompilation
    {literalScalars? : String → Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    {plan : CompiledParserPackPlan}
    (agreement :
      ParserPackPlanAgreement literalScalars? profile rules plan) :
    StructuralRulesCompile literalScalars? profile.startSort
      rules plan.structural :=
  StructuralRulesCompile.of_compilation literalScalars? profile.startSort
    agreement.structural_exact

/-- The exact compilation view for a selected source structural occurrence. -/
def ParserPackPlanAgreement.structuralRuleView
    {literalScalars? : String → Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    {plan : CompiledParserPackPlan}
    (agreement :
      ParserPackPlanAgreement literalScalars? profile rules plan)
    (occurrence : ListOccurrence rules) :
    StructuralRuleCompileView literalScalars? profile.startSort
      (rules.get occurrence)
      (plan.structural.get
        (agreement.structuralCompilation.mapOccurrence occurrence)) :=
  StructuralRuleCompileView.of_compilation _ _ _ _
    (agreement.structuralCompilation.get_compiled occurrence)

/-- The compilation view at one raw physical position, independently of the
particular proofs used to bound that position in the source and target
lists. -/
def ParserPackPlanAgreement.structuralRuleViewAtPosition
    {literalScalars? : String → Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    {plan : CompiledParserPackPlan}
    (agreement :
      ParserPackPlanAgreement literalScalars? profile rules plan)
    (position : Nat) (sourceValid : position < rules.length)
    (targetValid : position < plan.structural.length) :
    StructuralRuleCompileView literalScalars? profile.startSort
      (rules.get ⟨position, sourceValid⟩)
      (plan.structural.get ⟨position, targetValid⟩) := by
  have occurrenceEq :
      agreement.structuralCompilation.mapOccurrence
          ⟨position, sourceValid⟩ =
        (⟨position, targetValid⟩ : ListOccurrence plan.structural) := by
    apply Fin.ext
    rfl
  cases occurrenceEq
  exact agreement.structuralRuleView ⟨position, sourceValid⟩

@[simp] theorem
    ParserPackPlanAgreement.structuralRuleViewAtPosition_targetValid
    {literalScalars? : String → Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    {plan : CompiledParserPackPlan}
    (agreement :
      ParserPackPlanAgreement literalScalars? profile rules plan)
    (position : Nat) (sourceValid : position < rules.length) :
    agreement.structuralRuleViewAtPosition position sourceValid
        (agreement.structuralCompilation.targetValid position sourceValid) =
      agreement.structuralRuleView ⟨position, sourceValid⟩ := by
  apply Subsingleton.elim

@[simp] theorem ParserPackPlanAgreement.structuralRuleViewAtPosition_sourceValid_targetValid
    {literalScalars? : String → Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    {plan : CompiledParserPackPlan}
    (agreement :
      ParserPackPlanAgreement literalScalars? profile rules plan)
    (position : Nat) (sourceValid : position < rules.length) :
    agreement.structuralRuleViewAtPosition position
        (agreement.structuralCompilation.sourceValid position
          (agreement.structuralCompilation.targetValid position sourceValid))
        (agreement.structuralCompilation.targetValid position sourceValid) =
      agreement.structuralRuleView ⟨position, sourceValid⟩ := by
  apply Subsingleton.elim

/-- The exact compilation view for a selected target structural occurrence,
reflected through the inverse positional equivalence. -/
def ParserPackPlanAgreement.structuralRuleViewInverse
    {literalScalars? : String → Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    {plan : CompiledParserPackPlan}
    (agreement :
      ParserPackPlanAgreement literalScalars? profile rules plan)
    (occurrence : ListOccurrence plan.structural) :
    StructuralRuleCompileView literalScalars? profile.startSort
      (rules.get
        (agreement.structuralCompilation.occurrenceEquiv.symm occurrence))
      (plan.structural.get occurrence) := by
  let sourceOccurrence :=
    agreement.structuralCompilation.occurrenceEquiv.symm occurrence
  have occurrenceEq :
      agreement.structuralCompilation.mapOccurrence sourceOccurrence =
        occurrence :=
    agreement.structuralCompilation.occurrenceEquiv.apply_symm_apply occurrence
  cases occurrenceEq
  exact agreement.structuralRuleView sourceOccurrence

/-- Looking a compiled row up backward at the image of a source occurrence
recovers the same canonical compilation view used in the forward direction. -/
@[simp] theorem ParserPackPlanAgreement.structuralRuleViewInverse_mapOccurrence
    {literalScalars? : String → Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    {plan : CompiledParserPackPlan}
    (agreement :
      ParserPackPlanAgreement literalScalars? profile rules plan)
    (occurrence : ListOccurrence rules) :
    agreement.structuralRuleViewInverse
        (agreement.structuralCompilation.mapOccurrence occurrence) =
      agreement.structuralRuleView occurrence := by
  apply Subsingleton.elim

@[simp] theorem ParserPackPlanAgreement.structuralRuleViewInverse_apply
    {literalScalars? : String → Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    {plan : CompiledParserPackPlan}
    (agreement :
      ParserPackPlanAgreement literalScalars? profile rules plan)
    (occurrence : ListOccurrence rules) :
    agreement.structuralRuleViewInverse
        (agreement.structuralCompilation.occurrenceEquiv occurrence) =
      agreement.structuralRuleView occurrence := by
  apply Subsingleton.elim

/-- Appending EOF at the start sort does not manufacture a child slot. -/
theorem nonterminalSlots_append_eof (items : List PackItem) :
    nonterminalSlots (items ++ [.terminal .eof]) =
      nonterminalSlots items := by
  simp [nonterminalSlots, List.zipIdx_append]

/-- Negative control: an unresolved literal makes the structural compiler
fail closed. -/
theorem unresolved_literal_is_rejected :
    compileStructuralAtomItems? (fun _ => none)
      (.terminal "unknown" "ignored-parser-ref") = none := by
  rfl

theorem compileLexicalProductions_member
    {profile : ParserProfileLayer} {state : LexicalStateDecl}
    (member : state ∈ profile.states) :
    compileLexicalState state ∈ compileLexicalProductions profile := by
  exact List.mem_map.mpr ⟨state, member, rfl⟩

set_option autoImplicit true in
/-- Exact-span semantics of one ParserPack terminal matcher. -/
inductive TerminalMatchesAt (profile : ParserProfileLayer)
    (input : List Nat) : TerminalMatcher → Nat → Nat → Type where
  | any
      (lookup : input[start]? = some codepoint) :
      TerminalMatchesAt profile input .any start (start + 1)
  | eof
      (atEnd : cursor = input.length) :
      TerminalMatchesAt profile input .eof cursor cursor
  | char
      (lookup : input[start]? = some codepoint) :
      TerminalMatchesAt profile input (.char codepoint) start (start + 1)
  | classMember
      (lookup : input[start]? = some codepoint)
      (evidence : profile.ClassEvidence className codepoint) :
      TerminalMatchesAt profile input (.class className) start (start + 1)

/-- ParserPack's terminal semantic value.  EOF is zero-width and produces no
child; every consuming matcher retains the exact codepoint occurrence. -/
def TerminalMatchesAt.cst
    {profile : ParserProfileLayer} {input : List Nat}
    {matcher : TerminalMatcher} {start stop : Nat} :
    TerminalMatchesAt profile input matcher start stop → List CST
  | .any (codepoint := codepoint) _ =>
      [.terminal [codepoint] start (start + 1)]
  | .eof _ => []
  | .char (codepoint := codepoint) _ =>
      [.terminal [codepoint] start (start + 1)]
  | .classMember (codepoint := codepoint) _ _ =>
      [.terminal [codepoint] start (start + 1)]

/-- Transport terminal evidence along matcher equality without changing its
input occurrence or CST output. -/
def TerminalMatchesAt.castMatcher
    {profile : ParserProfileLayer} {input : List Nat}
    {left right : TerminalMatcher} {start stop : Nat}
    (matcherEq : left = right) :
    TerminalMatchesAt profile input right start stop →
      TerminalMatchesAt profile input left start stop := by
  cases matcherEq
  exact id

@[simp] theorem TerminalMatchesAt.cst_castMatcher
    {profile : ParserProfileLayer} {input : List Nat}
    {left right : TerminalMatcher} {start stop : Nat}
    (matcherEq : left = right)
    (matched : TerminalMatchesAt profile input right start stop) :
    (matched.castMatcher matcherEq).cst = matched.cst := by
  cases matcherEq
  rfl

abbrev CSTTerminalMatchesAt
    (profile : ParserProfileLayer) (input : List Nat)
    (matcher : TerminalMatcher) (start stop : Nat)
    (output : List CST) : Type :=
  { derivation : TerminalMatchesAt profile input matcher start stop //
    derivation.cst = output }

private def sourcePresentation : Presentation := {
  name := "ParserPackLexicalSource"
  definitions := []
  members := []
}

/-- At one exact CST output, an authored class expression and the compiled
ParserPack class matcher have equivalent evidence fibres. -/
def classCSTEquiv
    (profile : ParserProfileLayer) (input : List Nat)
    (className : String) (start stop : Nat) (output : List CST) :
    CSTRecognizesAtUsing profile.ClassEvidence sourcePresentation input
        (.class className) start stop output ≃
      CSTTerminalMatchesAt profile input (.class className)
        start stop output where
  toFun source := by
    rcases source with ⟨derivation, outputEq⟩
    cases derivation with
    | classMember lookup evidence =>
        exact ⟨.classMember lookup evidence, outputEq⟩
  invFun target := by
    rcases target with ⟨derivation, outputEq⟩
    cases derivation with
    | classMember lookup evidence =>
        exact ⟨.classMember lookup evidence, outputEq⟩
  left_inv source := by
    rcases source with ⟨derivation, outputEq⟩
    cases derivation
    rfl
  right_inv target := by
    rcases target with ⟨derivation, outputEq⟩
    cases derivation
    rfl

set_option autoImplicit true in
/-- Source lexical evidence retains the exact authored state occurrence and
wraps its class leaf in the authored rule-labelled CST node. -/
inductive SourceLexicalDerivesAt (profile : ParserProfileLayer)
    (input : List Nat) : String → Nat → Nat → List CST → Type where
  | apply (occurrence : ListOccurrence profile.states)
      (body : CSTRecognizesAtUsing profile.ClassEvidence sourcePresentation
        input (.class (profile.states.get occurrence).className)
          start stop children) :
      SourceLexicalDerivesAt profile input
        (profile.states.get occurrence).resultSort start stop
        [.node (profile.states.get occurrence).ruleLabel start stop children]

set_option autoImplicit true in
/-- Compiled lexical evidence retains the compiler provenance for its
production and performs the distinct ParserPack terminal-matcher judgment. -/
inductive CompiledLexicalDerivesAt (profile : ParserProfileLayer)
    (input : List Nat) : String → Nat → Nat → List CST → Type where
  | apply (occurrence : ListOccurrence profile.states)
      (body : CSTTerminalMatchesAt profile input
        (.class (profile.states.get occurrence).className)
          start stop children) :
      CompiledLexicalDerivesAt profile input
        (profile.states.get occurrence).resultSort start stop
        [.node (profile.states.get occurrence).ruleLabel start stop children]

/-- Recover the concrete emitted production from one compiled derivation. -/
def CompiledLexicalDerivesAt.production
  {profile : ParserProfileLayer} {input : List Nat}
  {resultSort : String} {start stop : Nat} {output : List CST} :
    CompiledLexicalDerivesAt profile input resultSort start stop output →
      CompiledLexicalProduction
  | .apply occurrence _ => compileLexicalState (profile.states.get occurrence)

theorem CompiledLexicalDerivesAt.production_mem
    {profile : ParserProfileLayer} {input : List Nat}
    {resultSort : String} {start stop : Nat} {output : List CST}
    (derivation :
      CompiledLexicalDerivesAt profile input resultSort start stop output) :
    derivation.production ∈ compileLexicalProductions profile := by
  cases derivation with
  | apply occurrence body =>
      exact compileLexicalProductions_member (List.get_mem _ occurrence)

/-- The lexical compiler preserves every exact CST occurrence and every
source-state alternative. -/
def preserveLexical
    {profile : ParserProfileLayer} {input : List Nat}
  {resultSort : String} {start stop : Nat} {output : List CST} :
    SourceLexicalDerivesAt profile input resultSort start stop output →
      CompiledLexicalDerivesAt profile input resultSort start stop output
  | .apply occurrence body =>
      .apply occurrence
        (classCSTEquiv profile input
          (profile.states.get occurrence).className _ _ _ body)

/-- The compiled lexical machine invents no exact CST occurrence or lexical
state alternative. -/
def reflectLexical
    {profile : ParserProfileLayer} {input : List Nat}
  {resultSort : String} {start stop : Nat} {output : List CST} :
    CompiledLexicalDerivesAt profile input resultSort start stop output →
      SourceLexicalDerivesAt profile input resultSort start stop output
  | .apply occurrence body =>
      .apply occurrence
        ((classCSTEquiv profile input
          (profile.states.get occurrence).className _ _ _).symm body)

/-- The proof-relevant lexical fibres are equivalent, not merely their
acceptance propositions or result may-sets. -/
def lexicalDerivationEquiv
    (profile : ParserProfileLayer) (input : List Nat)
    (resultSort : String) (start stop : Nat) (output : List CST) :
    SourceLexicalDerivesAt profile input resultSort start stop output ≃
      CompiledLexicalDerivesAt profile input resultSort start stop output where
  toFun := preserveLexical
  invFun := reflectLexical
  left_inv source := by
    cases source with
    | apply occurrence body =>
        simp only [preserveLexical, reflectLexical]
        rw [Equiv.symm_apply_apply]
  right_inv target := by
    cases target with
    | apply occurrence body =>
        simp only [preserveLexical, reflectLexical]
        rw [Equiv.apply_symm_apply]

set_option autoImplicit true in
/-- Independent source-side recognition of an exact scalar sequence.  This
is the operational content obtained after an authored literal reference has
been resolved, before it is expanded into ParserPack character items. -/
inductive ScalarSequenceMatchesAt (input : List Nat) :
    List Nat → Nat → Nat → Type where
  | nil (cursor : Nat) :
      ScalarSequenceMatchesAt input [] cursor cursor
  | cons
      (lookup : input[start]? = some codepoint)
      (rest : ScalarSequenceMatchesAt input codepoints (start + 1) stop) :
      ScalarSequenceMatchesAt input (codepoint :: codepoints) start stop

/-- Source-side completion evidence corresponding to the target compiler's
administrative EOF item.  The branch is explicit evidence rather than a
type-level `if`, so start and non-start production behavior remains visible
to recursive translations and NTT analysis. -/
inductive SourceProductionFinish (startSort category : String)
    (input : List Nat) (stop : Nat) : Type where
  | start (categoryIsStart : category = startSort)
      (atEnd : stop = input.length) :
      SourceProductionFinish startSort category input stop
  | nonstart (categoryIsNotStart : category ≠ startSort) :
      SourceProductionFinish startSort category input stop

instance SourceProductionFinish.instSubsingleton
    (startSort category : String) (input : List Nat) (stop : Nat) :
    Subsingleton (SourceProductionFinish startSort category input stop) := by
  constructor
  intro left right
  cases left with
  | start leftCategory leftEnd =>
      cases right with
      | start rightCategory rightEnd => rfl
      | nonstart rightCategory => exact False.elim (rightCategory leftCategory)
  | nonstart leftCategory =>
      cases right with
      | start rightCategory rightEnd => exact False.elim (leftCategory rightCategory)
      | nonstart rightCategory => rfl

/-! ## Independent source-plan semantics -/

set_option autoImplicit true in
mutual
  /-- Scannerless execution of the supplied lexical profile and ordered
  structural-rule rows before ParserPack item expansion.  The chosen source
  occurrence is an index, so duplicate equal rows remain distinct. -/
  inductive SourcePlanDerivesAt
      (literalScalars? : String → Option (List Nat))
      (profile : ParserProfileLayer) (rules : List CompiledRule)
      (input : List Nat) : String → Nat → Nat → CST → Type where
    | lexical
        (position : Nat) (valid : position < profile.states.length)
        {resultSort ruleLabel : String} {children : List CST}
        (resultSort_exact :
          (profile.states.get ⟨position, valid⟩).resultSort = resultSort)
        (ruleLabel_exact :
          (profile.states.get ⟨position, valid⟩).ruleLabel = ruleLabel)
        (matched : CSTRecognizesAtUsing profile.ClassEvidence sourcePresentation
          input (.class (profile.states.get ⟨position, valid⟩).className)
            start stop children) :
        SourcePlanDerivesAt literalScalars? profile rules input
          resultSort start stop (.node ruleLabel start stop children)
    | structural
        (position : Nat) (valid : position < rules.length)
        {resultSort ruleLabel : String}
        (resultSort_exact :
          (rules.get ⟨position, valid⟩).source.category = resultSort)
        (ruleLabel_exact :
          (rules.get ⟨position, valid⟩).source.label = ruleLabel)
        (body : SourcePlanItemsDeriveAt literalScalars? profile rules input
          (rules.get ⟨position, valid⟩).atoms start stop children)
        (finish : SourceProductionFinish profile.startSort
          (rules.get ⟨position, valid⟩).source.category input stop) :
        SourcePlanDerivesAt literalScalars? profile rules input
          resultSort start stop (.node ruleLabel start stop children)

  /-- Left-to-right execution of source structural atoms.  Literal spellings
  are resolved to exact scalar sequences; nonterminals recurse into the same
  supplied source plan. -/
  inductive SourcePlanItemsDeriveAt
      (literalScalars? : String → Option (List Nat))
      (profile : ParserProfileLayer) (rules : List CompiledRule)
      (input : List Nat) :
      List StructuralAtom → Nat → Nat → List CST → Type where
    | nil :
        SourcePlanItemsDeriveAt literalScalars? profile rules input
          [] cursor cursor []
    | terminal
        (decoded : literalScalars? token = some codepoints)
        (matched : ScalarSequenceMatchesAt input codepoints start middle)
        (rest : SourcePlanItemsDeriveAt literalScalars? profile rules input
          atoms middle stop children) :
        SourcePlanItemsDeriveAt literalScalars? profile rules input
          (.terminal token parserRef :: atoms) start stop children
    | nonterminal
        (head : SourcePlanDerivesAt literalScalars? profile rules input
          resultSort start middle tree)
        (rest : SourcePlanItemsDeriveAt literalScalars? profile rules input
          atoms middle stop children) :
        SourcePlanItemsDeriveAt literalScalars? profile rules input
          (.nonterminal parameter resultSort parserRef :: atoms)
          start stop (tree :: children)
end

/-- For a fixed class and exact span, class-recognition evidence is unique:
the consumed codepoint follows from the input lookup and all remaining
fields are propositions. -/
theorem classRecognition_unique
    {profile : ParserProfileLayer}
    {input : List Nat} {start stop : Nat}
    {className : String}
    (left right : RecognizesAtUsing profile.ClassEvidence
      sourcePresentation input (.class className) start stop) :
    left = right := by
  cases left with
  | classMember leftLookup leftEvidence =>
      cases right with
      | classMember rightLookup rightEvidence =>
          have codepointEq := leftLookup.symm.trans rightLookup
          simp at codepointEq
          subst_vars
          rfl

/-- The CST wrapper adds only a proof that the already-determined terminal
output equals the requested output, so its class-recognition fibre is also
canonical. -/
theorem classCSTRecognition_unique
    {profile : ParserProfileLayer}
    {input : List Nat} {start stop : Nat}
    {className : String} {output : List CST}
    (left right : CSTRecognizesAtUsing profile.ClassEvidence
      sourcePresentation input (.class className) start stop output) :
    left = right := by
  apply Subtype.ext
  exact classRecognition_unique left.1 right.1

/-- At a fixed matcher and exact span, target terminal evidence is unique.
For consuming matchers the input lookup determines the codepoint; the
remaining membership and endpoint fields are propositions. -/
theorem terminalRecognition_unique
    {profile : ParserProfileLayer}
    {input : List Nat} {matcher : TerminalMatcher}
    {start stop : Nat}
    (left right : TerminalMatchesAt profile input matcher start stop) :
    left = right := by
  cases left with
  | any leftLookup =>
      cases right with
      | any rightLookup =>
          have codepointEq := leftLookup.symm.trans rightLookup
          simp at codepointEq
          subst_vars
          rfl
  | eof leftEnd =>
      cases right with
      | eof rightEnd => rfl
  | char leftLookup =>
      cases right with
      | char rightLookup => rfl
  | classMember leftLookup leftEvidence =>
      cases right with
      | classMember rightLookup rightEvidence =>
          have codepointEq := leftLookup.symm.trans rightLookup
          simp at codepointEq
          subst_vars
          rfl

theorem cstTerminalRecognition_unique
    {profile : ParserProfileLayer}
    {input : List Nat} {matcher : TerminalMatcher}
    {start stop : Nat} {output : List CST}
    (left right : CSTTerminalMatchesAt profile input matcher
      start stop output) :
    left = right := by
  apply Subtype.ext
  exact terminalRecognition_unique left.1 right.1

/-! ## Operational semantics of the compiled plan -/

set_option autoImplicit true in
mutual
  /-- Proof-relevant execution of one compiled lexical or structural
  production at an exact input span.  Alternatives are retained as distinct
  inhabitants because the selected production occurrence is part of the
  derivation. -/
  inductive ParserPackDerivesAt (profile : ParserProfileLayer)
      (plan : CompiledParserPackPlan) (input : List Nat) :
      String → Nat → Nat → CST → Type where
    | lexical
        (position : Nat)
        (valid : position < plan.lexical.productions.length)
        {matcher : TerminalMatcher} {resultSort ruleLabel : String}
        {children : List CST}
        (matcher_exact :
          (plan.lexical.productions.get ⟨position, valid⟩).matcher = matcher)
        (resultSort_exact :
          (plan.lexical.productions.get ⟨position, valid⟩).resultSort = resultSort)
        (ruleLabel_exact :
          (plan.lexical.productions.get ⟨position, valid⟩).label = ruleLabel)
        (matched : CSTTerminalMatchesAt profile input matcher
          start stop children) :
        ParserPackDerivesAt profile plan input
          resultSort start stop (.node ruleLabel start stop children)
    | structural
        (position : Nat) (valid : position < plan.structural.length)
        {resultSort ruleLabel : String}
        (resultSort_exact :
          (plan.structural.get ⟨position, valid⟩).resultSort = resultSort)
        (ruleLabel_exact :
          (plan.structural.get ⟨position, valid⟩).label = ruleLabel)
        (body : ParserPackItemsDeriveAt profile plan input
          (plan.structural.get ⟨position, valid⟩).items
          start stop children) :
        ParserPackDerivesAt profile plan input
          resultSort start stop (.node ruleLabel start stop children)

  /-- Left-to-right execution of a production body.  Structural terminals
  constrain the cursor but are discarded by the node action; nonterminal
  results are retained exactly once and in order. -/
  inductive ParserPackItemsDeriveAt (profile : ParserProfileLayer)
      (plan : CompiledParserPackPlan) (input : List Nat) :
      List PackItem → Nat → Nat → List CST → Type where
    | nil :
        ParserPackItemsDeriveAt profile plan input [] cursor cursor []
    | terminal
        (matched : TerminalMatchesAt profile input matcher start middle)
        (rest : ParserPackItemsDeriveAt profile plan input items
          middle stop children) :
        ParserPackItemsDeriveAt profile plan input
          (.terminal matcher :: items) start stop children
    | nonterminal
        (head : ParserPackDerivesAt profile plan input resultSort
          start middle tree)
        (rest : ParserPackItemsDeriveAt profile plan input items
          middle stop children) :
        ParserPackItemsDeriveAt profile plan input
          (.nonterminal resultSort :: items) start stop (tree :: children)
end

/-- Recover the item-vector index carried by an item derivation. -/
def ParserPackItemsDeriveAt.itemVector
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {items : List PackItem} {start stop : Nat}
    {children : List CST}
    (_ : ParserPackItemsDeriveAt profile plan input items
      start stop children) : List PackItem :=
  items

/-! Intrinsic heights ignore type indices such as cursors and item vectors,
so they remain invariant under dependent transport. -/
mutual
  /-- Intrinsic height of one complete target derivation. -/
  def ParserPackDerivesAt.height
      {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      {input : List Nat} {resultSort : String} {start stop : Nat}
      {tree : CST} :
      ParserPackDerivesAt profile plan input resultSort start stop tree → Nat
    | .lexical _ _ _ _ _ _ => 1
    | .structural _ _ _ _ body => body.height + 1

  /-- Intrinsic height of one target item-vector derivation. -/
  def ParserPackItemsDeriveAt.height
      {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      {input : List Nat} {items : List PackItem} {start stop : Nat}
      {children : List CST} :
      ParserPackItemsDeriveAt profile plan input items start stop children → Nat
    | .nil => 1
    | .terminal _ rest => rest.height + 1
    | .nonterminal head rest => head.height + rest.height + 1
end

@[simp] theorem ParserPackDerivesAt.height_structural
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {resultSort ruleLabel : String}
    {start stop : Nat} {children : List CST}
    (position : Nat) (valid : position < plan.structural.length)
    (resultSortExact :
      (plan.structural.get ⟨position, valid⟩).resultSort = resultSort)
    (ruleLabelExact :
      (plan.structural.get ⟨position, valid⟩).label = ruleLabel)
    (body : ParserPackItemsDeriveAt profile plan input
      (plan.structural.get ⟨position, valid⟩).items
      start stop children) :
    (ParserPackDerivesAt.structural position valid resultSortExact
      ruleLabelExact body).height = body.height + 1 := rfl

theorem ParserPackItemsDeriveAt.head_height_lt_nonterminal
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {resultSort : String}
    {items : List PackItem} {start middle stop : Nat}
    {tree : CST} {children : List CST}
    (head : ParserPackDerivesAt profile plan input resultSort
      start middle tree)
    (rest : ParserPackItemsDeriveAt profile plan input items
      middle stop children) :
    head.height < (ParserPackItemsDeriveAt.nonterminal head rest).height := by
  change head.height < head.height + rest.height + 1
  omega

theorem ParserPackItemsDeriveAt.rest_height_lt_nonterminal
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {resultSort : String}
    {items : List PackItem} {start middle stop : Nat}
    {tree : CST} {children : List CST}
    (head : ParserPackDerivesAt profile plan input resultSort
      start middle tree)
    (rest : ParserPackItemsDeriveAt profile plan input items
      middle stop children) :
    rest.height < (ParserPackItemsDeriveAt.nonterminal head rest).height := by
  change rest.height < head.height + rest.height + 1
  omega

/-- Transport item execution along an item-vector equality. -/
def ParserPackItemsDeriveAt.castItems
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {left right : List PackItem}
    {start stop : Nat} {children : List CST}
    (itemsEq : left = right) :
    ParserPackItemsDeriveAt profile plan input left start stop children →
      ParserPackItemsDeriveAt profile plan input right start stop children := by
  cases itemsEq
  exact id

@[simp] theorem ParserPackItemsDeriveAt.height_castItems
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {left right : List PackItem}
    {start stop : Nat} {children : List CST}
    (itemsEq : left = right)
    (derivation :
      ParserPackItemsDeriveAt profile plan input left start stop children) :
    (derivation.castItems itemsEq).height = derivation.height := by
  cases itemsEq
  rfl

@[simp] theorem ParserPackItemsDeriveAt.castItems_symm
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {left right : List PackItem}
    {start stop : Nat} {children : List CST}
    (itemsEq : left = right)
    (derivation : ParserPackItemsDeriveAt profile plan input left
      start stop children) :
    (derivation.castItems itemsEq).castItems itemsEq.symm = derivation := by
  cases itemsEq
  rfl

@[simp] theorem ParserPackItemsDeriveAt.castItems_symm_left
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {left right : List PackItem}
    {start stop : Nat} {children : List CST}
    (itemsEq : left = right)
    (derivation : ParserPackItemsDeriveAt profile plan input right
      start stop children) :
    (derivation.castItems itemsEq.symm).castItems itemsEq = derivation := by
  cases itemsEq
  rfl

/-- Two independently constructed equality witnesses for opposite item-vector
transports cancel.  Their proof terms are intentionally irrelevant; only the
two endpoint vectors belong to the execution evidence. -/
@[simp] theorem ParserPackItemsDeriveAt.castItems_cancel
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {left right : List PackItem}
    {start stop : Nat} {children : List CST}
    (forward : left = right) (backward : right = left)
    (derivation : ParserPackItemsDeriveAt profile plan input left
      start stop children) :
    (derivation.castItems forward).castItems backward = derivation := by
  cases forward
  rfl

/-- Sequentially compose two target item derivations.  This is the exact
operational counterpart of concatenating emitted item vectors. -/
def ParserPackItemsDeriveAt.append
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {leftItems rightItems : List PackItem}
    {start middle stop : Nat} {leftChildren rightChildren : List CST} :
    ParserPackItemsDeriveAt profile plan input leftItems
        start middle leftChildren →
      ParserPackItemsDeriveAt profile plan input rightItems
        middle stop rightChildren →
      ParserPackItemsDeriveAt profile plan input
        (leftItems ++ rightItems) start stop
        (leftChildren ++ rightChildren)
  | .nil, right => right
  | .terminal matched rest, right =>
      .terminal matched (ParserPackItemsDeriveAt.append rest right)
  | .nonterminal head rest, right =>
      .nonterminal head (ParserPackItemsDeriveAt.append rest right)

/-- Append the compiler's zero-width EOF check to a completed start-sort
body. -/
def ParserPackItemsDeriveAt.appendEOF
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {items : List PackItem}
    {start stop : Nat} {children : List CST}
    (body : ParserPackItemsDeriveAt profile plan input items
      start stop children)
    (atEnd : stop = input.length) :
    ParserPackItemsDeriveAt profile plan input
      (items ++ [.terminal .eof]) start stop children :=
  match body with
  | .nil => .terminal (.eof atEnd) .nil
  | .terminal matched rest => .terminal matched (rest.appendEOF atEnd)
  | .nonterminal head rest => .nonterminal head (rest.appendEOF atEnd)

/-- Remove the final administrative EOF check while recovering its exact
end-of-input witness. -/
def ParserPackItemsDeriveAt.stripEOF
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} :
    (items : List PackItem) → {start stop : Nat} → {children : List CST} →
      ParserPackItemsDeriveAt profile plan input
        (items ++ [.terminal .eof]) start stop children →
      ParserPackItemsDeriveAt profile plan input items
          start stop children × PLift (stop = input.length)
  | [], _, _, _, .terminal (.eof atEnd) .nil => ⟨.nil, ⟨atEnd⟩⟩
  | .terminal _ :: items, _, _, _, .terminal matched rest =>
      let ⟨body, atEnd⟩ := ParserPackItemsDeriveAt.stripEOF items rest
      ⟨.terminal matched body, atEnd⟩
  | .nonterminal _ :: items, _, _, _, .nonterminal head rest =>
      let ⟨body, atEnd⟩ := ParserPackItemsDeriveAt.stripEOF items rest
      ⟨.nonterminal head body, atEnd⟩

/-- Appending and then stripping the administrative EOF check recovers the
same body derivation and end-of-input evidence. -/
theorem ParserPackItemsDeriveAt.stripEOF_appendEOF
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {items : List PackItem} {start stop : Nat}
    {children : List CST}
    (body : ParserPackItemsDeriveAt profile plan input items
      start stop children) (atEnd : stop = input.length) :
    (body.appendEOF atEnd).stripEOF items = ⟨body, ⟨atEnd⟩⟩ := by
  induction body using ParserPackItemsDeriveAt.rec
    (motive_1 := fun _ _ _ _ _ => PUnit) with
  | nil => rfl
  | terminal matched rest inductionHypothesis =>
      simp only [ParserPackItemsDeriveAt.appendEOF,
        ParserPackItemsDeriveAt.stripEOF]
      rw [inductionHypothesis atEnd]
  | nonterminal head rest headIH restIH =>
      simp only [ParserPackItemsDeriveAt.appendEOF,
        ParserPackItemsDeriveAt.stripEOF]
      rw [restIH atEnd]
  | lexical => exact PUnit.unit
  | structural => exact PUnit.unit

/-- Stripping and then restoring the administrative EOF check recovers the
same complete target derivation. -/
theorem ParserPackItemsDeriveAt.appendEOF_stripEOF
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} :
    (items : List PackItem) → {start stop : Nat} →
      {children : List CST} →
      (derivation : ParserPackItemsDeriveAt profile plan input
        (items ++ [.terminal .eof]) start stop children) →
      (derivation.stripEOF items).1.appendEOF
          (derivation.stripEOF items).2.down = derivation := by
  intro items
  induction items with
  | nil =>
      intro start stop children derivation
      cases derivation with
      | terminal matched rest =>
          cases matched with
          | eof atEnd =>
              cases rest
              rfl
  | cons item items inductionHypothesis =>
      intro start stop children derivation
      cases item with
      | terminal matcher =>
          cases derivation with
          | terminal matched rest =>
              simp only [ParserPackItemsDeriveAt.stripEOF,
                ParserPackItemsDeriveAt.appendEOF]
              rw [inductionHypothesis rest]
      | nonterminal resultSort =>
          cases derivation with
          | nonterminal head rest =>
              simp only [ParserPackItemsDeriveAt.stripEOF,
                ParserPackItemsDeriveAt.appendEOF]
              rw [inductionHypothesis rest]

/-- Removing the administrative EOF suffix never increases derivation size. -/
theorem ParserPackItemsDeriveAt.stripEOF_height_le
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} :
    (items : List PackItem) → {start stop : Nat} → {children : List CST} →
      (derivation : ParserPackItemsDeriveAt profile plan input
        (items ++ [.terminal .eof]) start stop children) →
      (derivation.stripEOF items).1.height ≤ derivation.height := by
  intro items
  induction items with
  | nil =>
      intro start stop children derivation
      cases derivation with
      | terminal matched rest =>
          cases matched with
          | eof atEnd =>
              cases rest
              simp [ParserPackItemsDeriveAt.stripEOF,
                ParserPackItemsDeriveAt.height]
  | cons item items inductionHypothesis =>
      intro start stop children derivation
      cases item with
      | terminal matcher =>
          cases derivation with
          | terminal matched rest =>
              simp only [ParserPackItemsDeriveAt.stripEOF]
              have smaller := inductionHypothesis rest
              simp only [ParserPackItemsDeriveAt.height]
              omega
      | nonterminal resultSort =>
          cases derivation with
          | nonterminal head rest =>
              simp only [ParserPackItemsDeriveAt.stripEOF]
              have smaller := inductionHypothesis rest
              simp only [ParserPackItemsDeriveAt.height]
              omega

/-- Transporting a start-production body and removing its administrative EOF
suffix yields a derivation strictly smaller than the enclosing structural
step. -/
theorem ParserPackItemsDeriveAt.stripEOF_castItems_height_lt_succ
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {sourceItems bodyItems : List PackItem}
    {start stop : Nat} {children : List CST}
    (itemsEq : sourceItems = bodyItems ++ [.terminal .eof])
    (body : ParserPackItemsDeriveAt profile plan input sourceItems
      start stop children) :
    ((body.castItems itemsEq).stripEOF bodyItems).1.height <
      body.height + 1 := by
  exact lt_of_le_of_lt
    ((body.castItems itemsEq).stripEOF_height_le bodyItems)
    (by
      rw [ParserPackItemsDeriveAt.height_castItems]
      exact Nat.lt_succ_self body.height)

/-! ## Exact literal expansion -/

/-- Expand independent source scalar-sequence evidence into the emitted
sequence of ParserPack character items. -/
def preserveScalarSequence
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {codepoints : List Nat} {start stop : Nat} :
    ScalarSequenceMatchesAt input codepoints start stop →
      ParserPackItemsDeriveAt profile plan input
        (codepoints.map fun codepoint => .terminal (.char codepoint))
        start stop []
  | .nil cursor => .nil
  | .cons lookup rest =>
      .terminal (.char lookup) (preserveScalarSequence rest)

/-- Reflect an emitted character-item sequence back to the independently
defined source scalar sequence. -/
def reflectScalarSequence
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} :
    (codepoints : List Nat) → {start stop : Nat} →
      ParserPackItemsDeriveAt profile plan input
          (codepoints.map fun codepoint => .terminal (.char codepoint))
          start stop [] →
        ScalarSequenceMatchesAt input codepoints start stop
  | [], _, _, .nil => .nil _
  | _ :: codepoints, _, _, .terminal (.char lookup) rest =>
      .cons lookup (reflectScalarSequence codepoints rest)

/-- Literal expansion preserves and reflects the complete exact-span proof
fibre, rather than only agreeing on acceptance. -/
def scalarSequenceDerivationEquiv
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input codepoints : List Nat) (start stop : Nat) :
    ScalarSequenceMatchesAt input codepoints start stop ≃
      ParserPackItemsDeriveAt profile plan input
        (codepoints.map fun codepoint => .terminal (.char codepoint))
        start stop [] where
  toFun := preserveScalarSequence
  invFun := reflectScalarSequence codepoints
  left_inv source := by
    induction source with
    | nil => rfl
    | cons lookup rest inductionHypothesis =>
        simp [preserveScalarSequence, reflectScalarSequence,
          inductionHypothesis]
  right_inv target := by
    induction codepoints generalizing start with
    | nil =>
        cases target
        rfl
    | cons codepoint codepoints inductionHypothesis =>
        cases target with
        | terminal matched rest =>
            cases matched with
            | char lookup =>
                simp [reflectScalarSequence, preserveScalarSequence,
                  inductionHypothesis]

/-- Place a compiled scalar sequence before an arbitrary target suffix. -/
def preserveScalarSequencePrefix
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input codepoints : List Nat} {suffix : List PackItem}
    {start middle stop : Nat} {children : List CST}
    (matched : ScalarSequenceMatchesAt input codepoints start middle)
    (rest : ParserPackItemsDeriveAt profile plan input suffix
      middle stop children) :
    ParserPackItemsDeriveAt profile plan input
      ((codepoints.map fun codepoint => .terminal (.char codepoint)) ++ suffix)
      start stop children :=
  match matched with
  | .nil _ => rest
  | .cons lookup tail =>
      .terminal (.char lookup) (preserveScalarSequencePrefix tail rest)

/-- Split an emitted character prefix from an arbitrary target suffix,
recovering the exact source scalar evidence and the intermediate cursor. -/
def reflectScalarSequencePrefix
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} :
    (codepoints : List Nat) → (suffix : List PackItem) →
      {start stop : Nat} → {children : List CST} →
      ParserPackItemsDeriveAt profile plan input
        ((codepoints.map fun codepoint => .terminal (.char codepoint)) ++
          suffix) start stop children →
      Sigma fun middle =>
        ScalarSequenceMatchesAt input codepoints start middle ×
          ParserPackItemsDeriveAt profile plan input suffix
            middle stop children
  | [], suffix, start, _, _, derivation =>
      ⟨start, .nil start, by simpa using derivation⟩
  | _ :: codepoints, suffix, _, _, _,
      .terminal (.char lookup) rest =>
      let ⟨middle, matched, suffixDerivation⟩ :=
        reflectScalarSequencePrefix codepoints suffix rest
      ⟨middle, .cons lookup matched, suffixDerivation⟩

/-- Splitting a scalar prefix immediately after constructing it recovers
the same cursor, scalar evidence, and suffix evidence. -/
theorem reflectScalarSequencePrefix_preserve
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input codepoints : List Nat} {suffix : List PackItem}
    {start middle stop : Nat} {children : List CST}
    (matched : ScalarSequenceMatchesAt input codepoints start middle)
    (rest : ParserPackItemsDeriveAt profile plan input suffix
      middle stop children) :
    reflectScalarSequencePrefix codepoints suffix
        (preserveScalarSequencePrefix matched rest) =
      ⟨middle, matched, rest⟩ := by
  induction matched with
  | nil => rfl
  | cons lookup matched inductionHypothesis =>
      simp only [preserveScalarSequencePrefix,
        reflectScalarSequencePrefix]
      rw [inductionHypothesis rest]

/-- Reconstructing a target item derivation after splitting its emitted
scalar prefix is exactly the original derivation. -/
theorem preserveScalarSequencePrefix_reflect
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} :
    (codepoints : List Nat) → (suffix : List PackItem) →
      {start stop : Nat} → {children : List CST} →
      (derivation : ParserPackItemsDeriveAt profile plan input
        ((codepoints.map fun codepoint => .terminal (.char codepoint)) ++
          suffix) start stop children) →
      preserveScalarSequencePrefix
          (reflectScalarSequencePrefix codepoints suffix derivation).2.1
          (reflectScalarSequencePrefix codepoints suffix derivation).2.2 =
        derivation := by
  intro codepoints
  induction codepoints with
  | nil =>
      intro suffix start stop children derivation
      rfl
  | cons codepoint codepoints inductionHypothesis =>
      intro suffix start stop children derivation
      cases derivation with
      | terminal matched rest =>
          cases matched with
          | char lookup =>
              change ParserPackItemsDeriveAt.terminal (.char lookup)
                  (preserveScalarSequencePrefix
                    (reflectScalarSequencePrefix
                      codepoints suffix rest).2.1
                    (reflectScalarSequencePrefix
                      codepoints suffix rest).2.2) =
                ParserPackItemsDeriveAt.terminal (.char lookup) rest
              rw [inductionHypothesis suffix rest]

/-- Splitting a scalar prefix never increases the size of the remaining
target derivation.  Equality is possible precisely for an empty prefix,
which is why backward recursion also measures the remaining source atoms. -/
theorem reflectScalarSequencePrefix_suffix_height_le
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} :
    (codepoints : List Nat) → (suffix : List PackItem) →
      {start stop : Nat} → {children : List CST} →
      (derivation : ParserPackItemsDeriveAt profile plan input
        ((codepoints.map fun codepoint => .terminal (.char codepoint)) ++
          suffix) start stop children) →
      (reflectScalarSequencePrefix codepoints suffix derivation).2.2.height ≤
        derivation.height := by
  intro codepoints
  induction codepoints with
  | nil =>
      intro suffix start stop children derivation
      rfl
  | cons codepoint codepoints inductionHypothesis =>
      intro suffix start stop children derivation
      cases derivation with
      | terminal matched rest =>
          cases matched with
          | char lookup =>
              change
                  (reflectScalarSequencePrefix codepoints suffix rest).2.2.height ≤
                (ParserPackItemsDeriveAt.terminal
                  (TerminalMatchesAt.char lookup) rest).height
              have smaller := inductionHypothesis suffix rest
              simp only [ParserPackItemsDeriveAt.height]
              omega

/-! ## Recursive preservation -/

mutual
  /-- Compile a complete source-plan derivation into execution evidence for
  the supplied, exactly agreeing ParserPack plan. -/
  def preserveSourcePlanDerivation
      {literalScalars? : String → Option (List Nat)}
      {profile : ParserProfileLayer} {rules : List CompiledRule}
      {plan : CompiledParserPackPlan} {input : List Nat}
      (agreement :
        ParserPackPlanAgreement literalScalars? profile rules plan)
      {resultSort : String} {start stop : Nat} {tree : CST} :
      SourcePlanDerivesAt literalScalars? profile rules input
          resultSort start stop tree →
        ParserPackDerivesAt profile plan input
          resultSort start stop tree
    | .lexical position sourceValid sourceResultSort sourceRuleLabel matched => by
        let sourceOccurrence : ListOccurrence profile.states :=
          ⟨position, sourceValid⟩
        have targetValid : position < plan.lexical.productions.length := by
          rw [← agreement.lexical_length_eq]
          exact sourceValid
        let targetOccurrence : ListOccurrence plan.lexical.productions :=
          ⟨position, targetValid⟩
        let targetMatched :=
          (classCSTEquiv profile input
            (profile.states.get sourceOccurrence).className
            _ _ _).toFun matched
        have productionEq := agreement.lexical_get sourceOccurrence
        have matcherEq :
            (plan.lexical.productions.get targetOccurrence).matcher =
              .class (profile.states.get sourceOccurrence).className :=
          congrArg CompiledLexicalProduction.matcher productionEq
        have labelEq :
            (plan.lexical.productions.get targetOccurrence).label =
              (profile.states.get sourceOccurrence).ruleLabel :=
          congrArg CompiledLexicalProduction.label productionEq
        have resultSortEq :
            (plan.lexical.productions.get targetOccurrence).resultSort =
              (profile.states.get sourceOccurrence).resultSort :=
          congrArg CompiledLexicalProduction.resultSort productionEq
        exact ParserPackDerivesAt.lexical position targetValid matcherEq
          (resultSortEq.trans sourceResultSort)
          (labelEq.trans sourceRuleLabel) targetMatched
    | .structural (children := children) position sourceValid sourceResultSort
        sourceRuleLabel body finish => by
        let compilation := agreement.structuralCompilation
        let sourceOccurrence : ListOccurrence rules := ⟨position, sourceValid⟩
        let targetValid : position < plan.structural.length :=
          compilation.targetValid position sourceValid
        let targetOccurrence : ListOccurrence plan.structural :=
          ⟨position, targetValid⟩
        let view := agreement.structuralRuleViewAtPosition
          position sourceValid targetValid
        let targetBody := preserveSourcePlanItems agreement
          view.itemCompilation body
        have completedBody :
            ParserPackItemsDeriveAt profile plan input
              (plan.structural.get targetOccurrence).items
              start stop children := by
          cases finish with
          | start isStart atEnd =>
              have itemsEq :
                  (plan.structural.get targetOccurrence).items =
                    view.bodyItems ++ [.terminal .eof] := by
                simpa only [if_pos isStart] using view.items_exact
              exact (targetBody.appendEOF atEnd).castItems itemsEq.symm
          | nonstart isNotStart =>
              have itemsEq :
                  (plan.structural.get targetOccurrence).items =
                    view.bodyItems := by
                simpa only [if_neg isNotStart] using view.items_exact
              exact targetBody.castItems itemsEq.symm
        have targetResultSortEq :
            (plan.structural.get targetOccurrence).resultSort =
              (rules.get sourceOccurrence).source.category := by
          exact view.resultSort_exact
        have targetRuleLabelEq :
            (plan.structural.get targetOccurrence).label =
              (rules.get sourceOccurrence).source.label := by
          exact view.label_exact
        exact ParserPackDerivesAt.structural position targetValid
          (targetResultSortEq.trans sourceResultSort)
          (targetRuleLabelEq.trans sourceRuleLabel) completedBody

  /-- Compile a source structural-atom derivation according to its exact
  pointwise atom-to-item expansion evidence. -/
  def preserveSourcePlanItems
      {literalScalars? : String → Option (List Nat)}
      {profile : ParserProfileLayer} {rules : List CompiledRule}
      {plan : CompiledParserPackPlan} {input : List Nat}
      (agreement :
        ParserPackPlanAgreement literalScalars? profile rules plan)
      {atoms : List StructuralAtom} {items : List PackItem}
      {start stop : Nat} {children : List CST}
      (compilation :
        StructuralItemsCompile literalScalars? atoms items) :
      SourcePlanItemsDeriveAt literalScalars? profile rules input
          atoms start stop children →
        ParserPackItemsDeriveAt profile plan input
          items start stop children := fun source =>
    match compilation, source with
    | .nil, .nil => .nil
    | .terminal compiledDecoded tailCompilation,
        .terminal sourceDecoded matched rest => by
          have codepointsEq := Option.some.inj <|
            compiledDecoded.symm.trans sourceDecoded
          cases codepointsEq
          exact preserveScalarSequencePrefix matched
            (preserveSourcePlanItems agreement tailCompilation rest)
    | .nonterminal tailCompilation, .nonterminal head rest =>
        .nonterminal
          (preserveSourcePlanDerivation agreement head)
          (preserveSourcePlanItems agreement tailCompilation rest)
end

/-! ## Recursive reflection / no invention -/

mutual
  /-- Reflect every target-plan derivation through the supplied exact plan
  agreement.  The result is evidence in the independently defined source
  relation; the target cannot invent a lexical or structural occurrence. -/
  def reflectSourcePlanDerivation
      {literalScalars? : String → Option (List Nat)}
      {profile : ParserProfileLayer} {rules : List CompiledRule}
      {plan : CompiledParserPackPlan} {input : List Nat}
      (agreement :
        ParserPackPlanAgreement literalScalars? profile rules plan)
      {resultSort : String} {start stop : Nat} {tree : CST} :
      ParserPackDerivesAt profile plan input resultSort start stop tree →
        SourcePlanDerivesAt literalScalars? profile rules input
          resultSort start stop tree
    | .lexical position targetValid targetMatcher targetResultSort
        targetRuleLabel matched => by
        have sourceValid : position < profile.states.length := by
          rw [agreement.lexical_length_eq]
          exact targetValid
        let sourceOccurrence : ListOccurrence profile.states :=
          ⟨position, sourceValid⟩
        let targetOccurrence : ListOccurrence plan.lexical.productions :=
          ⟨position, targetValid⟩
        have productionEq := agreement.lexical_get sourceOccurrence
        have matcherEq :
            (plan.lexical.productions.get targetOccurrence).matcher =
              .class (profile.states.get sourceOccurrence).className :=
          congrArg CompiledLexicalProduction.matcher productionEq
        have labelEq :
            (plan.lexical.productions.get targetOccurrence).label =
              (profile.states.get sourceOccurrence).ruleLabel :=
          congrArg CompiledLexicalProduction.label productionEq
        have resultSortEq :
            (plan.lexical.productions.get targetOccurrence).resultSort =
              (profile.states.get sourceOccurrence).resultSort :=
          congrArg CompiledLexicalProduction.resultSort productionEq
        have classToMatcher :
            TerminalMatcher.class
                (profile.states.get sourceOccurrence).className =
              _ := matcherEq.symm.trans targetMatcher
        let sourceTerminal : TerminalMatchesAt profile input
            (.class (profile.states.get sourceOccurrence).className)
            start stop := matched.1.castMatcher classToMatcher
        have sourceTerminalCst : sourceTerminal.cst = matched.1.cst :=
          TerminalMatchesAt.cst_castMatcher classToMatcher matched.1
        let sourceMatched :=
          (classCSTEquiv profile input
            (profile.states.get sourceOccurrence).className
            _ _ _).invFun
              ⟨sourceTerminal, sourceTerminalCst.trans matched.property⟩
        exact SourcePlanDerivesAt.lexical position sourceValid
          (resultSortEq.symm.trans targetResultSort)
          (labelEq.symm.trans targetRuleLabel) sourceMatched
    | .structural (children := children) position targetValid
        targetResultSort targetRuleLabel body => by
        let compilation := agreement.structuralCompilation
        let sourceValid : position < rules.length :=
          compilation.sourceValid position targetValid
        let targetOccurrence : ListOccurrence plan.structural :=
          ⟨position, targetValid⟩
        let sourceOccurrence : ListOccurrence rules :=
          ⟨position, sourceValid⟩
        let view := agreement.structuralRuleViewAtPosition
          position sourceValid targetValid
        have targetResultSortRowEq :
            (plan.structural.get targetOccurrence).resultSort =
              (rules.get sourceOccurrence).source.category := by
          exact view.resultSort_exact
        have targetRuleLabelRowEq :
            (plan.structural.get targetOccurrence).label =
              (rules.get sourceOccurrence).source.label := by
          exact view.label_exact
        have itemsEq : (plan.structural.get targetOccurrence).items =
              if (rules.get sourceOccurrence).source.category =
                  profile.startSort then
                view.bodyItems ++ [.terminal .eof]
              else view.bodyItems := view.items_exact
        by_cases isStart :
            (rules.get sourceOccurrence).source.category = profile.startSort
        · have startItemsEq :
              (plan.structural.get targetOccurrence).items =
                view.bodyItems ++ [.terminal .eof] := by
            simpa only [if_pos isStart] using itemsEq
          let bodyWithEOF : ParserPackItemsDeriveAt profile plan input
              (view.bodyItems ++ [.terminal .eof]) start stop children :=
            body.castItems startItemsEq
          let stripped := bodyWithEOF.stripEOF view.bodyItems
          let sourceBody := reflectSourcePlanItems agreement
            view.itemCompilation stripped.1
          have finish : SourceProductionFinish profile.startSort
              (rules.get sourceOccurrence).source.category input stop := by
            exact .start isStart stripped.2.down
          exact SourcePlanDerivesAt.structural position sourceValid
            (targetResultSortRowEq.symm.trans targetResultSort)
            (targetRuleLabelRowEq.symm.trans targetRuleLabel) sourceBody finish
        · have nonstartItemsEq :
              (plan.structural.get targetOccurrence).items =
                view.bodyItems := by
            simpa only [if_neg isStart] using itemsEq
          let bodyWithoutEOF : ParserPackItemsDeriveAt profile plan input
              view.bodyItems start stop children :=
            body.castItems nonstartItemsEq
          let sourceBody := reflectSourcePlanItems agreement
            view.itemCompilation bodyWithoutEOF
          have finish : SourceProductionFinish profile.startSort
              (rules.get sourceOccurrence).source.category input stop := by
            exact .nonstart isStart
          exact SourcePlanDerivesAt.structural position sourceValid
            (targetResultSortRowEq.symm.trans targetResultSort)
            (targetRuleLabelRowEq.symm.trans targetRuleLabel) sourceBody finish
  termination_by derivation => (derivation.height, 0)
  decreasing_by
    · change Prod.Lex (fun left right : Nat => left < right)
        (fun left right : Nat => left < right)
        ((bodyWithEOF.stripEOF view.bodyItems).1.height,
          (rules.get sourceOccurrence).atoms.length)
        (body.height + 1, 0)
      apply Prod.Lex.left
      have strippedSmaller :=
        bodyWithEOF.stripEOF_height_le view.bodyItems
      have castHeight : bodyWithEOF.height = body.height :=
        ParserPackItemsDeriveAt.height_castItems startItemsEq body
      omega
    · change Prod.Lex (fun left right : Nat => left < right)
        (fun left right : Nat => left < right)
        (bodyWithoutEOF.height,
          (rules.get sourceOccurrence).atoms.length)
        (body.height + 1, 0)
      apply Prod.Lex.left
      have castHeight : bodyWithoutEOF.height = body.height :=
        ParserPackItemsDeriveAt.height_castItems nonstartItemsEq body
      omega

  /-- Reflect target item execution through exact atom-expansion evidence.
  The lexicographic termination measure handles zero-scalar literals by
  decreasing the remaining source-atom count even when target evidence is
  unchanged. -/
  def reflectSourcePlanItems
      {literalScalars? : String → Option (List Nat)}
      {profile : ParserProfileLayer} {rules : List CompiledRule}
      {plan : CompiledParserPackPlan} {input : List Nat}
      (agreement :
        ParserPackPlanAgreement literalScalars? profile rules plan)
      {atoms : List StructuralAtom} {items : List PackItem}
      {start stop : Nat} {children : List CST} :
      (compilation : StructuralItemsCompile literalScalars? atoms items) →
        ParserPackItemsDeriveAt profile plan input items start stop children →
        SourcePlanItemsDeriveAt literalScalars? profile rules input
          atoms start stop children
    | .nil, derivation => by
        cases derivation
        exact .nil
    | .terminal decoded tailCompilation, derivation => by
        let split := reflectScalarSequencePrefix _ _ derivation
        exact .terminal decoded split.2.1
          (reflectSourcePlanItems agreement tailCompilation split.2.2)
    | .nonterminal tailCompilation, .nonterminal head rest =>
        .nonterminal
          (reflectSourcePlanDerivation agreement head)
          (reflectSourcePlanItems agreement tailCompilation rest)
  termination_by _ derivation =>
    (derivation.height, atoms.length)
  decreasing_by
    · have suffixSmaller :=
        reflectScalarSequencePrefix_suffix_height_le
          _ _ derivation
      by_cases strict :
          (reflectScalarSequencePrefix
            _ _ derivation).2.2.height < derivation.height
      · exact Prod.Lex.left _ _ strict
      · have equalHeight :
            (reflectScalarSequencePrefix
              _ _ derivation).2.2.height =
                derivation.height :=
          Nat.le_antisymm suffixSmaller (Nat.le_of_not_gt strict)
        rw [equalHeight]
        exact Prod.Lex.right _ (by simp)
    · apply Prod.Lex.left
      simp [ParserPackItemsDeriveAt.height]
    · apply Prod.Lex.left
      simp [ParserPackItemsDeriveAt.height]

end

/-! ## Exact inverse laws -/

/-- Reflection after preservation recovers the exact source derivation,
including every selected physical rule occurrence. -/
theorem reflectSourcePlanDerivation_preserve
    {literalScalars? : String → Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    {plan : CompiledParserPackPlan} {input : List Nat}
    (agreement :
      ParserPackPlanAgreement literalScalars? profile rules plan)
    {resultSort : String} {start stop : Nat} {tree : CST}
    (source : SourcePlanDerivesAt literalScalars? profile rules input
      resultSort start stop tree) :
    reflectSourcePlanDerivation agreement
        (preserveSourcePlanDerivation agreement source) = source := by
  induction source using SourcePlanDerivesAt.rec
    (motive_2 := fun atoms start stop children sourceItems =>
      ∀ {items : List PackItem}
        (compilation : StructuralItemsCompile literalScalars? atoms items),
        reflectSourcePlanItems agreement compilation
            (preserveSourcePlanItems agreement compilation sourceItems) =
          sourceItems) with
  | lexical position valid resultSortExact ruleLabelExact matched =>
      cases resultSortExact
      cases ruleLabelExact
      simp only [preserveSourcePlanDerivation,
        reflectSourcePlanDerivation]
      apply congrArg
      apply classCSTRecognition_unique
  | structural position valid resultSortExact ruleLabelExact body finish bodyIH =>
      cases resultSortExact
      cases ruleLabelExact
      cases finish with
      | start isStart atEnd =>
        simp only [preserveSourcePlanDerivation,
          reflectSourcePlanDerivation]
        split
        · congr 1
          change reflectSourcePlanItems agreement
              (agreement.structuralRuleViewAtPosition position valid
                (agreement.structuralCompilation.targetValid position
                  valid)).itemCompilation _ = body
          simpa [ParserPackItemsDeriveAt.stripEOF_appendEOF] using
            bodyIH (agreement.structuralRuleViewAtPosition position valid
              (agreement.structuralCompilation.targetValid position
                valid)).itemCompilation
        · rename_i contrary
          exact False.elim <| contrary <| by simpa using isStart
      | nonstart isNotStart =>
        simp only [preserveSourcePlanDerivation,
          reflectSourcePlanDerivation]
        split
        · rename_i contrary
          exact False.elim <| isNotStart <| by simpa using contrary
        · congr 1
          change reflectSourcePlanItems agreement
              (agreement.structuralRuleViewAtPosition position valid
                (agreement.structuralCompilation.targetValid position
                  valid)).itemCompilation _ = body
          rw [ParserPackItemsDeriveAt.castItems_cancel]
          exact
            bodyIH (agreement.structuralRuleViewAtPosition position valid
              (agreement.structuralCompilation.targetValid position
                valid)).itemCompilation
  | nil =>
      cases ‹StructuralItemsCompile literalScalars? [] _›
      simp [preserveSourcePlanItems, reflectSourcePlanItems]
  | terminal decoded matched rest restIH =>
      cases ‹StructuralItemsCompile literalScalars?
          (.terminal _ _ :: _) _› with
      | terminal compiledDecoded tailCompilation =>
          have codepointsEq := Option.some.inj <|
            compiledDecoded.symm.trans decoded
          cases codepointsEq
          simp only [preserveSourcePlanItems, reflectSourcePlanItems]
          rw [reflectScalarSequencePrefix_preserve]
          rw [restIH tailCompilation]
  | nonterminal head rest headIH restIH =>
      cases ‹StructuralItemsCompile literalScalars?
          (.nonterminal _ _ _ :: _) _› with
      | nonterminal tailCompilation =>
          simp only [preserveSourcePlanItems, reflectSourcePlanItems]
          rw [headIH, restIH tailCompilation]

mutual
  /-- Preservation after reflection recovers every target derivation,
  including its selected physical production occurrence. -/
  def preserveSourcePlanDerivation_reflect
      {literalScalars? : String → Option (List Nat)}
      {profile : ParserProfileLayer} {rules : List CompiledRule}
      {plan : CompiledParserPackPlan} {input : List Nat}
      (agreement :
        ParserPackPlanAgreement literalScalars? profile rules plan)
      {resultSort : String} {start stop : Nat} {tree : CST}
      (target : ParserPackDerivesAt profile plan input
        resultSort start stop tree) :
      preserveSourcePlanDerivation agreement
          (reflectSourcePlanDerivation agreement target) = target :=
    match target with
    | .lexical position valid matcherExact resultSortExact ruleLabelExact matched =>
        by
          have sourceValid : position < profile.states.length := by
            rw [agreement.lexical_length_eq]
            exact valid
          have productionEq := agreement.lexical_get
            (⟨position, sourceValid⟩ : ListOccurrence profile.states)
          have matcherRow :
              TerminalMatcher.class
                  (profile.states.get ⟨position, sourceValid⟩).className =
                (plan.lexical.productions.get ⟨position, valid⟩).matcher := by
            symm
            exact congrArg CompiledLexicalProduction.matcher productionEq
          have matcherEq := matcherRow.trans matcherExact
          cases matcherEq
          simp only [reflectSourcePlanDerivation,
            preserveSourcePlanDerivation]
          congr 1
          all_goals first
            | exact proof_irrel_heq _ _
            | exact heq_of_eq (cstTerminalRecognition_unique _ _)
            | exact cstTerminalRecognition_unique _ _
    | .structural position valid resultSortExact ruleLabelExact body =>
        by
          simp only [reflectSourcePlanDerivation]
          split
          · simp only [preserveSourcePlanDerivation]
            congr 1
            rename_i isStart
            let compilation := agreement.structuralCompilation
            let sourceValid := compilation.sourceValid position valid
            let view := agreement.structuralRuleViewAtPosition
              position sourceValid valid
            have itemsEq :
                (plan.structural.get ⟨position, valid⟩).items =
                  view.bodyItems ++ [.terminal .eof] := by
              simpa only [if_pos isStart] using view.items_exact
            let bodyWithEOF : ParserPackItemsDeriveAt profile plan input
                (view.bodyItems ++ [.terminal .eof]) _ _ _ :=
              body.castItems itemsEq
            let stripped := bodyWithEOF.stripEOF view.bodyItems
            have strippedSmaller : stripped.1.height < body.height + 1 :=
              ParserPackItemsDeriveAt.stripEOF_castItems_height_lt_succ
                itemsEq body
            have bodyRoundtrip := preserveSourcePlanItems_reflect agreement
              view.itemCompilation stripped.1
            have restored :=
              ParserPackItemsDeriveAt.appendEOF_stripEOF
                view.bodyItems bodyWithEOF
            change ((preserveSourcePlanItems agreement view.itemCompilation
                (reflectSourcePlanItems agreement view.itemCompilation
                  stripped.1)).appendEOF stripped.2.down).castItems _ = body
            rw [bodyRoundtrip, restored]
            apply ParserPackItemsDeriveAt.castItems_cancel
          · simp only [preserveSourcePlanDerivation]
            congr 1
            rename_i isNotStart
            let compilation := agreement.structuralCompilation
            let sourceValid := compilation.sourceValid position valid
            let view := agreement.structuralRuleViewAtPosition
              position sourceValid valid
            have itemsEq :
                (plan.structural.get ⟨position, valid⟩).items =
                  view.bodyItems := by
              simpa only [if_neg isNotStart] using view.items_exact
            let bodyWithoutEOF : ParserPackItemsDeriveAt profile plan input
                view.bodyItems _ _ _ := body.castItems itemsEq
            have bodyRoundtrip := preserveSourcePlanItems_reflect agreement
              view.itemCompilation bodyWithoutEOF
            change (preserveSourcePlanItems agreement view.itemCompilation
                (reflectSourcePlanItems agreement view.itemCompilation
                  bodyWithoutEOF)).castItems _ = body
            rw [bodyRoundtrip]
            apply ParserPackItemsDeriveAt.castItems_cancel
  termination_by (target.height, 0)

  /-- The item-vector translation is likewise inverse on every target proof
  object. -/
  def preserveSourcePlanItems_reflect
      {literalScalars? : String → Option (List Nat)}
      {profile : ParserProfileLayer} {rules : List CompiledRule}
      {plan : CompiledParserPackPlan} {input : List Nat}
      (agreement :
        ParserPackPlanAgreement literalScalars? profile rules plan)
      {atoms : List StructuralAtom} {items : List PackItem}
      {start stop : Nat} {children : List CST} :
      (compilation : StructuralItemsCompile literalScalars? atoms items) →
      (target : ParserPackItemsDeriveAt profile plan input
        items start stop children) →
      preserveSourcePlanItems agreement compilation
          (reflectSourcePlanItems agreement compilation target) = target
    | .nil, target => by
        cases target
        simp [reflectSourcePlanItems, preserveSourcePlanItems]
    | .terminal decoded tailCompilation, target => by
        let split := reflectScalarSequencePrefix _ _ target
        simp only [reflectSourcePlanItems, preserveSourcePlanItems]
        rw [preserveSourcePlanItems_reflect agreement tailCompilation
          split.2.2]
        exact preserveScalarSequencePrefix_reflect _ _ target
    | .nonterminal tailCompilation, .nonterminal head rest => by
        simp only [reflectSourcePlanItems, preserveSourcePlanItems]
        rw [preserveSourcePlanDerivation_reflect agreement head]
        rw [preserveSourcePlanItems_reflect agreement tailCompilation rest]
  termination_by _ target => (target.height, atoms.length)
  decreasing_by
    all_goals
      first
      | exact Prod.Lex.left _ _ strippedSmaller
      | exact Prod.Lex.left _ _
          (ParserPackItemsDeriveAt.stripEOF_castItems_height_lt_succ
            itemsEq body)
      | (have suffixSmaller :=
            reflectScalarSequencePrefix_suffix_height_le _ _ target
         by_cases strict : split.2.2.height < target.height
         · exact Prod.Lex.left _ _ strict
         · have equalHeight : split.2.2.height = target.height :=
             Nat.le_antisymm suffixSmaller (Nat.le_of_not_gt strict)
           rw [equalHeight]
           exact Prod.Lex.right _ (by simp))
      | exact Prod.Lex.left _ _
          (ParserPackItemsDeriveAt.head_height_lt_nonterminal head rest)
      | exact Prod.Lex.left _ _
          (ParserPackItemsDeriveAt.rest_height_lt_nonterminal head rest)
end

/-- The recursively generated ParserPack derivations have exactly the same
proof fibres as the independently authored scannerless plan.  The equivalence
retains physical rule positions, recursive alternatives, CST occurrences, and
the start-production EOF witness. -/
def sourcePlanDerivationEquiv
    {literalScalars? : String → Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    {plan : CompiledParserPackPlan} {input : List Nat}
    (agreement :
      ParserPackPlanAgreement literalScalars? profile rules plan)
    (resultSort : String) (start stop : Nat) (tree : CST) :
    SourcePlanDerivesAt literalScalars? profile rules input
        resultSort start stop tree ≃
      ParserPackDerivesAt profile plan input
        resultSort start stop tree where
  toFun := preserveSourcePlanDerivation agreement
  invFun := reflectSourcePlanDerivation agreement
  left_inv := reflectSourcePlanDerivation_preserve agreement
  right_inv := preserveSourcePlanDerivation_reflect agreement

/-- At every exact sort, span, and CST output, the supplied source plan is
inhabited exactly when its compiled ParserPack plan is inhabited.  This is the
propositional shadow of `sourcePlanDerivationEquiv`; the stronger equivalence
also retains the selected physical row occurrences and recursive evidence. -/
theorem sourcePlan_nonempty_iff_parserPack_nonempty
    {literalScalars? : String → Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    {plan : CompiledParserPackPlan} {input : List Nat}
    (agreement :
      ParserPackPlanAgreement literalScalars? profile rules plan)
    (resultSort : String) (start stop : Nat) (tree : CST) :
    Nonempty (SourcePlanDerivesAt literalScalars? profile rules input
        resultSort start stop tree) ↔
      Nonempty (ParserPackDerivesAt profile plan input
        resultSort start stop tree) := by
  constructor
  · rintro ⟨source⟩
    exact ⟨preserveSourcePlanDerivation agreement source⟩
  · rintro ⟨target⟩
    exact ⟨reflectSourcePlanDerivation agreement target⟩

/-- Whole-source execution starts at the profile's authored start sort and
must consume the complete scalar input. -/
abbrev SourcePlanRootDerives
    (literalScalars? : String → Option (List Nat))
    (profile : ParserProfileLayer) (rules : List CompiledRule)
    (input : List Nat) (tree : CST) : Type :=
  SourcePlanDerivesAt literalScalars? profile rules input
    profile.startSort 0 input.length tree

/-- Whole-target execution starts at the plan's authored start sort and must
consume the complete scalar input. -/
abbrev ParserPackRootDerives
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (tree : CST) : Type :=
  ParserPackDerivesAt profile plan input plan.lexical.startSort
    0 input.length tree

/-- Exact whole-input proof-fibre equivalence at the authored start sort. -/
def sourcePlanRootDerivationEquiv
    {literalScalars? : String → Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    {plan : CompiledParserPackPlan} {input : List Nat}
    (agreement :
      ParserPackPlanAgreement literalScalars? profile rules plan)
    (tree : CST) :
    SourcePlanRootDerives literalScalars? profile rules input tree ≃
      ParserPackRootDerives profile plan input tree := by
  change SourcePlanDerivesAt literalScalars? profile rules input
      profile.startSort 0 input.length tree ≃
    ParserPackDerivesAt profile plan input plan.lexical.startSort
      0 input.length tree
  rw [agreement.startSort_eq]
  exact sourcePlanDerivationEquiv (input := input) agreement
    profile.startSort 0 input.length tree

/-- A structural target occurrence retains its authored source row at the
same physical position. -/
theorem CompiledStructuralProduction.source_get
    {plan : CompiledParserPackPlan}
    (occurrence : ListOccurrence plan.structural) :
    (plan.structural.map (fun row => row.source)).get
        (occurrence.map fun row => row.source) =
      (plan.structural.get occurrence).source := by
  exact ListOccurrence.get_map occurrence (fun row => row.source)

/-! ## Positive and negative calibration -/

private def exampleProfile : ParserProfileLayer := {
  name := "Example"
  startSort := "Scalar"
  classes := [
    { name := "unescaped", kind := .except [34, 92] }]
  states := [
    { resultSort := "Scalar", className := "unescaped",
      ruleLabel := "lex-unescaped" }]
}

private def exampleState : LexicalStateDecl :=
  { resultSort := "Scalar", className := "unescaped",
    ruleLabel := "lex-unescaped" }

private def exampleStateOccurrence : ListOccurrence exampleProfile.states :=
  ⟨0, by decide⟩

private def duplicateStateProfile : ParserProfileLayer :=
  { exampleProfile with states := [exampleState, exampleState] }

/-- Equal lexical rows at different positions remain distinct occurrences.
Propositional list membership alone cannot express this distinction. -/
theorem duplicate_lexical_rows_have_distinct_occurrences :
    ∃ left right : ListOccurrence duplicateStateProfile.states,
      left ≠ right ∧
        duplicateStateProfile.states.get left =
          duplicateStateProfile.states.get right := by
  let left : ListOccurrence duplicateStateProfile.states := ⟨0, by decide⟩
  let right : ListOccurrence duplicateStateProfile.states := ⟨1, by decide⟩
  exact ⟨left, right, by decide, rfl⟩

theorem complement_lexical_occurrence_positive :
    Nonempty (CompiledLexicalDerivesAt exampleProfile [65]
      "Scalar" 0 1
      [.node "lex-unescaped" 0 1 [.terminal [65] 0 1]]) := by
  apply Nonempty.intro
  apply CompiledLexicalDerivesAt.apply exampleStateOccurrence
  exact ⟨.classMember (by rfl) (by
    change exampleProfile.classAccepts? "unescaped" 65 = some true
    decide), rfl⟩

/-- Negative control: a class exclusion cannot be accepted through the
compiled matcher even though the class is complement-shaped. -/
theorem complement_lexical_occurrence_rejects_exclusion :
    IsEmpty (TerminalMatchesAt exampleProfile [34]
      (.class "unescaped") 0 1) := by
  constructor
  intro matched
  cases matched with
  | classMember lookup evidence =>
      simp at lookup
      subst_vars
      simp [ParserProfileLayer.ClassEvidence,
        ParserProfileLayer.classAccepts?, ParserProfileLayer.class?,
        LexicalClassKind.accepts, exampleProfile] at evidence

end Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
