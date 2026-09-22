import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.MeTTaIL.ContextualStepClosedSubsystem
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.OSLF.MeTTaIL.LinearMatch
import Mettapedia.OSLF.MeTTaIL.DecimalNames

/-!
# The observer extension

A generated logic has a structural layer, one connective per term former, and
that layer is in general strictly more discriminating than a bisimilarity whose
steps are the theory's own reductions — a decomposition is not a step.  Read
carelessly, that makes adequacy for a logic with structural connectives
impossible rather than merely unproved.

The repair is not to weaken either claim but to supply the index both are
about.  Adequacy is a statement about bisimilarity *in a theory*, and what
counts as a theory depends on which instruments the observer holds.  Give the
observer the ability to take terms apart and structural inspection becomes
ordinary interaction; withhold it and the structural layer sees more than
interaction does.  Both readings are then true of different theories, and the
index is `Ob`: the set of constructors the observer may open.

The construction is mechanical in the presentation — adjoin some atoms, add
rules per constructor, stop — which is why it composes with the equally
mechanical generation of the logic.  It is realised here as a transformation of
`LanguageDef`s, so the extended theory is an ordinary presentation and every
result about presentations applies to it unchanged.

## What is deliberately excluded

The construction is not capability-safe if run on everything.  Any observer may
form an opening request, so any term whatever may be taken apart and whatever
authority its contents carry harvested.  The repair is to exclude the minting
apparatus: `Ob` is a set of constructors to open, and the mechanism that
generates unforgeable authority must not be among them.  `minting` is that
excluded set, and `ObAdmissible` is the condition that the two are disjoint.
Giving the factory an opening rule would let a token be taken apart, hence
rebuilt, hence forged.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.ObserverExtension

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-! ## The administrative vocabulary -/

/-- The request atom for opening a constructor. -/
def askLabel (constructor : String) : String := "Ask⟨" ++ constructor ++ "⟩"

/-- The former holding the arguments an opening yielded. -/
def argsLabel (constructor : String) : String := "Args⟨" ++ constructor ++ "⟩"

/-- The projection request for one argument position. -/
def getLabel (constructor : String) (index : Nat) : String :=
  "Get⟨" ++ constructor ++ "," ++ toString index ++ "⟩"

/-- The former that rebuilds a term from the arguments an opening yielded. -/
def buildLabel (constructor : String) : String := "Bld⟨" ++ constructor ++ "⟩"

/-- The sort freely adjoined for a constructor's argument bundle. -/
def answerSort (constructor : String) : String := "A⟨" ++ constructor ++ "⟩"

/-- Administrative labels are distinguishable from each other. -/
theorem askLabel_injective {first second : String}
    (equal : askLabel first = askLabel second) : first = second := by
  simpa [askLabel] using equal

theorem argsLabel_injective {first second : String}
    (equal : argsLabel first = argsLabel second) : first = second := by
  simpa [argsLabel] using equal

/-- The build and projection formers are never the same label: their bracketed
prefixes differ at the first character. -/
theorem buildLabel_ne_getLabel (first second : String) (index : Nat) :
    buildLabel first ≠ getLabel second index := by
  simp only [buildLabel, getLabel, String.append_assoc]
  exact Mettapedia.OSLF.MeTTaIL.DecimalNames.literal_ne
    (leftStart := "Bld⟨") (rightStart := "Get⟨") rfl rfl
    (by intro leftTail rightTail same; simp at same) _ _

/-- A projection former determines its index, once its constructor is fixed. -/
theorem getLabel_index_injective (constructor : String) {first second : Nat}
    (same : getLabel constructor first = getLabel constructor second) :
    first = second := by
  simp only [getLabel] at same
  have lists := congrArg String.toList same
  simp only [String.toList_append, List.append_assoc] at lists
  have tails := List.append_cancel_left (List.append_cancel_left
    (List.append_cancel_left lists))
  exact Mettapedia.OSLF.MeTTaIL.DecimalNames.repr_injective
    (String.toList_injective (List.append_cancel_right tails))

/-- Argument metavariable names for an opening rule. -/
def argVars (arity : Nat) : List String :=
  (List.range arity).map fun index => "obsArg" ++ toString index

/-- The argument patterns of an opening rule. -/
def argPatterns (arity : Nat) : List Pattern :=
  (argVars arity).map Pattern.fvar

/-- The argument patterns bind nothing. -/
theorem binderFreeList_argPatterns (arity : Nat) :
    Mettapedia.OSLF.MeTTaIL.Match.binderFreeList (argPatterns arity) = true := by
  simp only [argPatterns]
  induction argVars arity with
  | nil => rfl
  | cons _ _ ih =>
      simp only [List.map_cons, Mettapedia.OSLF.MeTTaIL.Match.binderFreeList,
        Mettapedia.OSLF.MeTTaIL.Match.binderFree, ih, Bool.and_self]

/-- The opening rule for one constructor: a request placed beside the term in
the cut releases the term's arguments.

`{Ask⟨c⟩, c(x₁ … xₙ)} ⇝ Args⟨c⟩(x₁ … xₙ)` -/
def openingRule (cut : CollType) (constructor : String) (arity : Nat) :
    RewriteRule where
  name := "open-" ++ constructor
  typeContext := []
  premises := []
  left := .collection cut
    [.apply (askLabel constructor) [], .apply constructor (argPatterns arity)] none
  right := .apply (argsLabel constructor) (argPatterns arity)

/-- The opening rule's right-hand side binds nothing, so firing it is unaffected
by the scope correction. -/
theorem applyRuleBindings_openingRule (cut : CollType) (constructor : String)
    (arity : Nat) (bindings : Bindings) :
    Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings (openingRule cut constructor arity)
        bindings
      = applyBindings bindings (openingRule cut constructor arity).right :=
  Mettapedia.OSLF.MeTTaIL.Match.applyBindingsScoped_zero_of_binderFree _ bindings _
    (by simp only [openingRule, Mettapedia.OSLF.MeTTaIL.Match.binderFree,
      binderFreeList_argPatterns])

/-- The projection rule for one argument position:
`Get⟨c,i⟩(Args⟨c⟩(x₁ … xₙ)) ⇝ xᵢ`. -/
def projectionRule (constructor : String) (arity index : Nat) : RewriteRule where
  name := "project-" ++ constructor ++ "-" ++ toString index
  typeContext := []
  premises := []
  left := .apply (getLabel constructor index)
    [.apply (argsLabel constructor) (argPatterns arity)]
  right := (argPatterns arity)[index]?.getD (.apply (argsLabel constructor) [])

/-- The projection rule's right-hand side binds nothing either. -/
theorem applyRuleBindings_projectionRule (constructor : String)
    (arity index : Nat) (bindings : Bindings) :
    Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings
        (projectionRule constructor arity index) bindings
      = applyBindings bindings (projectionRule constructor arity index).right := by
  refine Mettapedia.OSLF.MeTTaIL.Match.applyBindingsScoped_zero_of_binderFree _ bindings _ ?_
  simp only [projectionRule]
  cases hget : (argPatterns arity)[index]? with
  | none => simp only [Option.getD_none, Mettapedia.OSLF.MeTTaIL.Match.binderFree,
      Mettapedia.OSLF.MeTTaIL.Match.binderFreeList]
  | some q =>
      simp only [Option.getD_some]
      have hmem : q ∈ argPatterns arity := List.mem_of_getElem? hget
      simp only [argPatterns, List.mem_map] at hmem
      obtain ⟨x, -, rfl⟩ := hmem
      simp only [Mettapedia.OSLF.MeTTaIL.Match.binderFree]

/-- The build rule: what an opening took apart can be put back together.

`Bld⟨c⟩(Args⟨c⟩(x₁ … xₙ)) ⇝ c(x₁ … xₙ)`

Without it the observer's kit is a one-way mirror — a term could be taken apart
and never reassembled — and the source adjoins it for exactly that reason. -/
def buildRule (constructor : String) (arity : Nat) : RewriteRule where
  name := "build-" ++ constructor
  typeContext := []
  premises := []
  left := .apply (buildLabel constructor)
    [.apply (argsLabel constructor) (argPatterns arity)]
  right := .apply constructor (argPatterns arity)

/-! ## The adjoined declarations

The adjoined rules cite constructors, and a presentation in which a rule cites
an undeclared constructor is not a presentation.  Each of the four
administrative formers is therefore declared, over a sort freely adjoined for
the purpose. -/

/-- The positions of a constructor the observer can project: those whose
declared parameter is a term of a base sort.  A binder position is not among
them, and excluding it is not an omission — projecting one would hand back an
open body, whose sort the presentation does not declare. -/
def projectablePositions (rule : GrammarRule) : List (Nat × String) :=
  rule.params.zipIdx.filterMap fun entry =>
    match entry.1 with
    | .simple _ (.base sortName) => some (entry.2, sortName)
    | _ => none

/-- The opening request is a term of the sort it sits beside in the cut. -/
def askDeclaration (rule : GrammarRule) : GrammarRule where
  label := askLabel rule.label
  category := rule.category
  params := []
  syntaxPattern := [.terminal (askLabel rule.label)]

/-- **The freely adjoined argument former.**  It takes exactly the constructor's
declared argument sorts and lands in the fresh sort adjoined for it. -/
def argsDeclaration (rule : GrammarRule) : GrammarRule where
  label := argsLabel rule.label
  category := answerSort rule.label
  params := rule.params
  syntaxPattern := [.terminal (argsLabel rule.label)]

/-- A projection former takes the argument bundle to one declared argument. -/
def getDeclaration (rule : GrammarRule) (position : Nat × String) : GrammarRule where
  label := getLabel rule.label position.1
  category := position.2
  params := [.simple "bundle" (.base (answerSort rule.label))]
  syntaxPattern := [.terminal (getLabel rule.label position.1)]

/-- The build former takes the argument bundle back to the constructor's own
sort. -/
def buildDeclaration (rule : GrammarRule) : GrammarRule where
  label := buildLabel rule.label
  category := rule.category
  params := [.simple "bundle" (.base (answerSort rule.label))]
  syntaxPattern := [.terminal (buildLabel rule.label)]

/-! ## The extension -/

/-- The grammar rules the observer may open, read off the presentation's own
declarations.  An instrument is a constructor *name*; its arity and the sorts of
its arguments come from the theory rather than from a table written beside it,
so an instrument cannot cite a constructor the theory does not have and cannot
disagree with it about arity. -/
def openedRules (lang : LanguageDef) (opened : List String) : List GrammarRule :=
  lang.terms.filter fun rule => opened.contains rule.label

/-- The fresh sort adjoined for one opened constructor. -/
def instrumentSorts (rule : GrammarRule) : List TypeDecl :=
  [TypeDecl.plain (answerSort rule.label)]

/-- Every declaration adjoined for one opened constructor. -/
def instrumentDeclarations (rule : GrammarRule) : List GrammarRule :=
  askDeclaration rule :: argsDeclaration rule :: buildDeclaration rule ::
    (projectablePositions rule).map (getDeclaration rule)

/-- Every rule adjoined for one opened constructor. -/
def instrumentRules (cut : CollType) (rule : GrammarRule) : List RewriteRule :=
  openingRule cut rule.label rule.params.length ::
    buildRule rule.label rule.params.length ::
    (projectablePositions rule).map fun position =>
      projectionRule rule.label rule.params.length position.1

/-- The presentation extended with the observer's instruments.  The authored
sorts, grammar, equations and rewrites are retained exactly; a fresh sort, four
administrative formers per opened constructor, and their rules are adjoined, so
the extended theory is an ordinary presentation in which every rule cites only
declared constructors. -/
def observerExtension (lang : LanguageDef) (cut : CollType)
    (opened : List String) : LanguageDef where
  name := lang.name ++ "+Obs"
  types := lang.types ++ (openedRules lang opened).flatMap instrumentSorts
  terms := lang.terms ++ (openedRules lang opened).flatMap instrumentDeclarations
  equations := lang.equations
  rewrites := lang.rewrites ++
    (openedRules lang opened).flatMap (instrumentRules cut)

/-- The extension retains every authored rule. -/
theorem mem_rewrites_of_mem (lang : LanguageDef) (cut : CollType)
    (opened : List String) {rule : RewriteRule}
    (member : rule ∈ lang.rewrites) :
    rule ∈ (observerExtension lang cut opened).rewrites := by
  simp only [observerExtension, List.mem_append]
  exact Or.inl member

/-- And every authored declaration. -/
theorem mem_terms_of_mem (lang : LanguageDef) (cut : CollType)
    (opened : List String) {rule : GrammarRule}
    (member : rule ∈ lang.terms) :
    rule ∈ (observerExtension lang cut opened).terms := by
  simp only [observerExtension, List.mem_append]
  exact Or.inl member

/-- The extension retains the authored equations, so it presents the same
equation theory on the authored vocabulary. -/
theorem observerExtension_equations (lang : LanguageDef) (cut : CollType)
    (opened : List String) :
    (observerExtension lang cut opened).equations = lang.equations := rfl

/-- An opened constructor is one the presentation declares. -/
theorem openedRules_mem (lang : LanguageDef) (opened : List String)
    {rule : GrammarRule} (member : rule ∈ openedRules lang opened) :
    rule ∈ lang.terms := (List.mem_filter.mp member).1

/-! ### Every adjoined rule cites only declared constructors -/

/-- The request former of an opened constructor is declared. -/
theorem askDeclaration_mem (lang : LanguageDef) (cut : CollType)
    (opened : List String) {rule : GrammarRule}
    (member : rule ∈ openedRules lang opened) :
    askDeclaration rule ∈ (observerExtension lang cut opened).terms := by
  simp only [observerExtension, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨rule, member, by simp [instrumentDeclarations]⟩

/-- The freely adjoined argument former is declared. -/
theorem argsDeclaration_mem (lang : LanguageDef) (cut : CollType)
    (opened : List String) {rule : GrammarRule}
    (member : rule ∈ openedRules lang opened) :
    argsDeclaration rule ∈ (observerExtension lang cut opened).terms := by
  simp only [observerExtension, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨rule, member, by simp [instrumentDeclarations]⟩

/-- The build former is declared. -/
theorem buildDeclaration_mem (lang : LanguageDef) (cut : CollType)
    (opened : List String) {rule : GrammarRule}
    (member : rule ∈ openedRules lang opened) :
    buildDeclaration rule ∈ (observerExtension lang cut opened).terms := by
  simp only [observerExtension, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨rule, member, by simp [instrumentDeclarations]⟩

/-- **The fresh sort is declared.**  Stated on the declared sort names, which is
what the grammar is indexed by. -/
theorem answerSort_declared (lang : LanguageDef) (cut : CollType)
    (opened : List String) {rule : GrammarRule}
    (member : rule ∈ openedRules lang opened) :
    answerSort rule.label ∈
      (observerExtension lang cut opened).types.map TypeDecl.name := by
  simp only [observerExtension, List.map_append, List.mem_append, List.mem_map,
    List.mem_flatMap]
  exact Or.inr ⟨TypeDecl.plain (answerSort rule.label),
    ⟨rule, member, by simp [instrumentSorts]⟩, rfl⟩

/-- The build rule is adjoined. -/
theorem buildRule_mem (lang : LanguageDef) (cut : CollType)
    (opened : List String) {rule : GrammarRule}
    (member : rule ∈ openedRules lang opened) :
    buildRule rule.label rule.params.length ∈
      (observerExtension lang cut opened).rewrites := by
  simp only [observerExtension, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨rule, member, by simp [instrumentRules]⟩

/-! ## Freshness of the administrative vocabulary

The construction adjoins labels and a sort, and it means them to be new.  That
was a convention; here it is a decidable condition on the presentation, and
below it is what buys conservativity — on a term the authored theory could
already have written, the extension rewrites exactly as the authored theory
does. -/

/-- Every label the extension adjoins for one opened constructor. -/
def instrumentLabels (rule : GrammarRule) : List String :=
  askLabel rule.label :: argsLabel rule.label :: buildLabel rule.label ::
    (projectablePositions rule).map fun position => getLabel rule.label position.1

/-- Every label the extension adjoins. -/
def adjoinedLabels (lang : LanguageDef) (opened : List String) : List String :=
  (openedRules lang opened).flatMap instrumentLabels

/-- **The administrative vocabulary is fresh**: none of the labels or sorts the
extension adjoins is already declared by the presentation.  Decidable, so a
presentation can be checked rather than trusted. -/
def AdministrativeFresh (lang : LanguageDef) (opened : List String) : Prop :=
  (∀ label ∈ adjoinedLabels lang opened,
      label ∉ lang.terms.map GrammarRule.label) ∧
    ∀ rule ∈ openedRules lang opened,
      answerSort rule.label ∉ lang.types.map TypeDecl.name

instance (lang : LanguageDef) (opened : List String) :
    Decidable (AdministrativeFresh lang opened) := by
  unfold AdministrativeFresh; infer_instance

/-- Each adjoined rule is one of the three shapes, at an opened constructor. -/
theorem instrumentRules_cases (cut : CollType) {declaration : GrammarRule}
    {rule : RewriteRule} (member : rule ∈ instrumentRules cut declaration) :
    rule = openingRule cut declaration.label declaration.params.length ∨
      rule = buildRule declaration.label declaration.params.length ∨
      ∃ position ∈ projectablePositions declaration,
        rule = projectionRule declaration.label declaration.params.length position.1 := by
  simp only [instrumentRules, List.mem_cons, List.mem_map] at member
  rcases member with rfl | rfl | ⟨position, positionMember, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨position, positionMember, rfl⟩)

/-- **No adjoined rule matches a term headed by an authored operation.**  The
opening rule asks for a cut, and the build and projection rules ask for a head
the presentation does not declare. -/
theorem matchPattern_adjoined_eq_nil
    (lang : LanguageDef) (cut : CollType) (opened : List String)
    {names : List String}
    (namesAuthored : ∀ name ∈ names, name ∈ lang.terms.map GrammarRule.label)
    (fresh : AdministrativeFresh lang opened)
    {source : Pattern} (head : HasOperationHead names source)
    {rule : RewriteRule}
    (member : rule ∈ (openedRules lang opened).flatMap (instrumentRules cut)) :
    matchPattern rule.left source = [] := by
  obtain ⟨declaration, declarationMember, ruleMember⟩ := List.mem_flatMap.mp member
  have adjoined : ∀ label ∈ instrumentLabels declaration,
      ∀ name ∈ names, label ≠ name := by
    intro label labelMember name nameMember equal
    refine fresh.1 label ?_ (equal ▸ namesAuthored name nameMember)
    exact List.mem_flatMap.mpr ⟨declaration, declarationMember, labelMember⟩
  rcases instrumentRules_cases cut ruleMember with rfl | rfl | ⟨position, _, rfl⟩
  · cases source <;> simp only [HasOperationHead] at head
    case apply name arguments => simp [openingRule, matchPattern]
  · refine matchPattern_eq_nil_of_disjoint_operationHeads
      (leftNames := [buildLabel declaration.label]) ?_ head ?_
    · simp [buildRule, HasOperationHead]
    · intro a aMember b bMember
      simp only [List.mem_singleton] at aMember
      subst aMember
      exact adjoined _ (by simp [instrumentLabels]) b bMember
  · refine matchPattern_eq_nil_of_disjoint_operationHeads
      (leftNames := [getLabel declaration.label position.1]) ?_ head ?_
    · simp [projectionRule, HasOperationHead]
    · intro a aMember b bMember
      simp only [List.mem_singleton] at aMember
      subst aMember
      refine adjoined _ ?_ b bMember
      simp only [instrumentLabels, List.mem_cons, List.mem_map]
      exact Or.inr (Or.inr (Or.inr ⟨position, ‹position ∈ projectablePositions declaration›, rfl⟩))

/-- **Conservativity.**  On a term headed by an authored operation, the extended
presentation rewrites exactly as the authored one does — same results, same
order, same multiplicity.  The observer gains instruments; it changes nothing
about what the theory already did. -/
theorem rewriteAt_eq_of_authored_head
    (lang : LanguageDef) (cut : CollType) (opened : List String)
    {names : List String}
    (namesAuthored : ∀ name ∈ names, name ∈ lang.terms.map GrammarRule.label)
    (fresh : AdministrativeFresh lang opened)
    (closed : ∀ rule ∈ lang.rewrites, CallsWithin names rule.premises)
    (base₁ base₂ : BasePremiseEvaluator) (fuel : Nat) {source : Pattern}
    (head : HasOperationHead names source) :
    rewriteAt base₁ lang fuel source
      = rewriteAt base₂ (observerExtension lang cut opened) fuel source :=
  rewriteAt_closed_extension names lang (observerExtension lang cut opened)
    ((openedRules lang opened).flatMap (instrumentRules cut)) base₁ base₂ rfl closed
    (fun _ sourceHead _ ruleMember =>
      matchPattern_adjoined_eq_nil lang cut opened namesAuthored fresh sourceHead ruleMember)
    fuel source head

/-! ## Monotonicity in the instrument set -/

/-- A larger instrument set opens at least as many declared constructors. -/
theorem openedRules_mono (lang : LanguageDef) {smaller larger : List String}
    (inclusion : ∀ name, name ∈ smaller → name ∈ larger)
    {rule : GrammarRule} (member : rule ∈ openedRules lang smaller) :
    rule ∈ openedRules lang larger := by
  obtain ⟨declared, opened⟩ := List.mem_filter.mp member
  refine List.mem_filter.mpr ⟨declared, ?_⟩
  simp only [List.contains_iff_mem] at opened ⊢
  exact inclusion rule.label opened

/-- A larger instrument set retains every rule of a smaller one. -/
theorem rules_mono (lang : LanguageDef) (cut : CollType)
    {smaller larger : List String}
    (inclusion : ∀ name, name ∈ smaller → name ∈ larger)
    (rule : RewriteRule)
    (member : rule ∈ (observerExtension lang cut smaller).rewrites) :
    rule ∈ (observerExtension lang cut larger).rewrites := by
  simp only [observerExtension, List.mem_append, List.mem_flatMap] at member ⊢
  rcases member with authored | ⟨declaration, declarationMember, ruleMember⟩
  · exact Or.inl authored
  · exact Or.inr ⟨declaration,
      openedRules_mono lang inclusion declarationMember, ruleMember⟩

/-- **Monotonicity.**  Every step available to a smaller instrument set is
available to a larger one.  An observer that holds more instruments therefore
distinguishes at least as much: bisimilarity shrinks as `Ob` grows. -/
theorem step_mono (lang : LanguageDef) (cut : CollType)
    {smaller larger : List String}
    (inclusion : ∀ name, name ∈ smaller → name ∈ larger)
    {relEnv : RelationEnv} {source target : Pattern}
    (step : Step (engineBasePremises relEnv)
      (observerExtension lang cut smaller) source target) :
    Step (engineBasePremises relEnv)
      (observerExtension lang cut larger) source target :=
  Step.mono_rules (rules_mono lang cut inclusion) step

/-- In particular the authored theory's steps survive into every extension:
the observer gains instruments, it does not lose behaviour. -/
theorem step_of_base (lang : LanguageDef) (cut : CollType)
    (opened : List String)
    {relEnv : RelationEnv} {source target : Pattern}
    (step : Step (engineBasePremises relEnv) lang source target) :
    Step (engineBasePremises relEnv)
      (observerExtension lang cut opened) source target :=
  Step.mono_rules (fun _ member => mem_rewrites_of_mem lang cut opened member) step

/-! ## The minting exclusion -/

/-- The observer's instruments avoid the minting apparatus. -/
def ObAdmissible (opened : List String) (minting : List String) : Prop :=
  ∀ name ∈ opened, name ∉ minting

/-- The empty instrument set is admissible against any minting apparatus: an
observer holding no instruments can open nothing, in particular no token. -/
theorem obAdmissible_nil (minting : List String) :
    ObAdmissible [] minting := by
  intro name member
  exact absurd member (List.not_mem_nil)

/-- Admissibility is inherited by smaller instrument sets. -/
theorem obAdmissible_mono {smaller larger : List String} {minting : List String}
    (inclusion : ∀ name, name ∈ smaller → name ∈ larger)
    (admissible : ObAdmissible larger minting) :
    ObAdmissible smaller minting :=
  fun name member => admissible name (inclusion name member)

/-- No instrument names a constructor of the minting apparatus. -/
theorem no_opening_for_minting {opened : List String} {minting : List String}
    (admissible : ObAdmissible opened minting)
    {constructor : String} (isMinting : constructor ∈ minting) :
    constructor ∉ opened :=
  fun member => admissible constructor member isMinting

/-- **And therefore no rule is adjoined for it.**  An admissible instrument set
selects no declared rule whose label is a minting constructor, so the factory
receives no opening rule, no projection and no build former: its tokens cannot
be taken apart, hence not rebuilt, hence not forged.

The exclusion is a condition on the instrument set, not a proof of
unforgeability.  Free adjunction cannot deliver unforgeability by itself — a
theory whose tokens are forgeable without any observer stays forgeable — so what
this theorem says is that the construction does not *introduce* a forgery
route. -/
theorem no_instrument_rules_for_minting (lang : LanguageDef) (_cut : CollType)
    {opened minting : List String}
    (admissible : ObAdmissible opened minting)
    {constructor : String} (isMinting : constructor ∈ minting)
    {rule : GrammarRule} (member : rule ∈ openedRules lang opened) :
    rule.label ≠ constructor := by
  intro equal
  obtain ⟨_, isOpened⟩ := List.mem_filter.mp member
  simp only [List.contains_iff_mem] at isOpened
  exact admissible rule.label isOpened (equal ▸ isMinting)

/-! ## What monotonicity of *bisimilarity* would additionally need

`step_mono` says the transitions grow with the instrument set, which is proved.
It does not by itself give that bisimilarity shrinks: adding transitions adds
both obligations to match and ways of matching, so neither inclusion between
the two bisimilarities follows from rule inclusion alone.  The argument in the
source material closes that gap by observing that the administrative rules
adjoined by the larger instrument set carry *fresh* probe atoms, so their
transitions cannot discharge an obligation of the smaller system.  Formalising
that freshness for a given presentation — the authored vocabulary must not
already contain the administrative labels — is what a proof of monotonicity for
bisimilarity needs, and it is not claimed here.

-/

/-! ## The instrument reads the head

The opening rule for a constructor fires beside a term only when that term is an
application of *that* constructor with the declared arity.  That is what makes
an instrument set an observation rather than a decoration, and it is the step a
reconstruction argument descends on: bisimilarity in the full extension forces
two terms to expose the same head, and then the same arguments.

This is stated for every constructor of every presentation, not for a specimen.
The `Gap` section below witnesses the converse concretely -- that the rule does
fire when the head matches -- and the general converse is not claimed here,
because it needs the opening rule's argument metavariables proved distinct and
their bindings proved mergeable, which is a separate obligation. -/

theorem askLabel_ne_self (constructor : String) :
    askLabel constructor ≠ constructor := by
  intro same
  have lengths := congrArg String.length same
  simp only [askLabel, String.length_append] at lengths
  have front : ("Ask⟨" : String).length = 4 := rfl
  have back : ("⟩" : String).length = 1 := rfl
  omega

theorem argPatterns_length (arity : Nat) : (argPatterns arity).length = arity := by
  simp [argPatterns, argVars]

/-- The arguments of a matched application match, with the labels generalised so
that dependent elimination is not asked to unify two concrete label
expressions. -/
theorem matchRel_apply_args {first second : String}
    {patternArguments termArguments : List Pattern} {bindings : Bindings}
    (matched : MatchRel (.apply first patternArguments)
      (.apply second termArguments) bindings) :
    MatchArgsRel patternArguments termArguments bindings := by
  cases matched
  assumption

/-- A constructor pattern matches only an application of the same constructor. -/
theorem matchRel_apply_head {first second : String}
    {patternArguments termArguments : List Pattern} {bindings : Bindings}
    (matched : MatchRel (.apply first patternArguments)
      (.apply second termArguments) bindings) : first = second := by
  cases matched
  rfl

/-- **The instrument reads the head.**  If the opening request for a
constructor, placed beside a term in the cut, matches the constructor's opening
rule, then the term is an application of that constructor at the declared
arity. -/
theorem headed_of_openingRule_match
    {cut : CollType} {constructor : String} {arity : Nat} {term : Pattern}
    {bindings : Bindings}
    (matched : bindings ∈ matchPattern (openingRule cut constructor arity).left
      (.collection cut [.apply (askLabel constructor) [], term] none)) :
    ∃ arguments : List Pattern,
      term = .apply constructor arguments ∧ arguments.length = arity := by
  have relational := matchPattern_iff_matchRel.mp matched
  have bagMatch := matchRel_collection_noRest_to_bag relational
  cases bagMatch with
  | cons index bounded askMatch restMatch _ =>
      match index, bounded with
      | 0, _ =>
          simp only [List.eraseIdx_zero, List.tail_cons] at restMatch
          cases restMatch with
          | cons innerIndex innerBounded constructorMatch tailMatch _ =>
              match innerIndex, innerBounded with
              | 0, _ =>
                  simp only [List.getElem_cons_zero] at constructorMatch
                  cases constructorMatch with
                  | apply argumentsMatch lengths =>
                      refine ⟨_, rfl, ?_⟩
                      rw [← lengths, argPatterns_length]
      | 1, _ =>
          simp only [List.getElem_cons_succ, List.getElem_cons_zero] at askMatch
          simp only [List.eraseIdx_cons_succ, List.eraseIdx_zero,
            List.tail_cons] at restMatch
          cases restMatch with
          | cons innerIndex innerBounded constructorMatch tailMatch _ =>
              match innerIndex, innerBounded with
              | 0, _ =>
                  simp only [List.getElem_cons_zero] at constructorMatch
                  exact absurd (matchRel_apply_head constructorMatch).symm
                    (askLabel_ne_self constructor)


/-! ### And it fires whenever the head matches

The other half of the same statement.  It needs the opening rule to be *linear*
-- each argument metavariable minted once -- which it is, because the generator
mints them from an index and decimal printing is injective.  With that, the
sibling bindings never conflict and the match succeeds. -/

theorem argVars_length (arity : Nat) : (argVars arity).length = arity := by
  simp [argVars]

theorem argVars_nodup (arity : Nat) : (argVars arity).Nodup :=
  Mettapedia.OSLF.MeTTaIL.DecimalNames.prefixed_range_nodup "obsArg" arity

/-- **The instrument fires on the head it reads, and delivers the bundle.**  An
opening request beside an application of that constructor at the declared arity
matches the constructor's opening rule, and applying the bindings the match
produces to the rule's right-hand side yields exactly that constructor's
argument bundle.  The delivery travels with the match because a step needs both:
the rule fires, and the target is what the rule builds. -/
theorem openingRule_match_of_headed
    (cut : CollType) (constructor : String) (arity : Nat)
    {arguments : List Pattern} (length : arguments.length = arity) :
    ∃ bindings, bindings ∈ matchPattern (openingRule cut constructor arity).left
        (.collection cut
          [.apply (askLabel constructor) [], .apply constructor arguments] none) ∧
      applyBindings bindings (openingRule cut constructor arity).right
        = .apply (argsLabel constructor) arguments := by
  obtain ⟨argumentBindings, argumentMember, argumentNodup, -, argumentPairs⟩ :=
    Mettapedia.OSLF.MeTTaIL.LinearMatch.matchArgs_fvars (argVars arity) arguments
      (argVars_nodup arity) (by rw [argVars_length, length])
  have constructorMatch :
      MatchRel (.apply constructor (argPatterns arity))
        (.apply constructor arguments) argumentBindings :=
    MatchRel.apply (matchArgs_iff_matchArgsRel.mp argumentMember)
      (by rw [argPatterns_length, length])
  have tailMerge : mergeBindings argumentBindings [] = some argumentBindings := by
    simp [mergeBindings]
  have restMatch :
      MatchBagRel [.apply constructor (argPatterns arity)] none cut
        [(.apply constructor arguments : Pattern)] argumentBindings :=
    MatchBagRel.cons 0 (by simp) constructorMatch MatchBagRel.nilNoRest tailMerge
  have askMatch :
      MatchRel (.apply (askLabel constructor) [])
        (.apply (askLabel constructor) ([] : List Pattern)) [] :=
    MatchRel.apply MatchArgsRel.nil rfl
  have headMerge : mergeBindings [] argumentBindings
      = some (argumentBindings.reverse ++ []) :=
    Mettapedia.OSLF.MeTTaIL.LinearMatch.mergeBindings_of_fresh argumentBindings []
      (by simp) argumentNodup
  have bagMatch :
      MatchBagRel
        [.apply (askLabel constructor) [], .apply constructor (argPatterns arity)]
        none cut
        [(.apply (askLabel constructor) [] : Pattern), .apply constructor arguments]
        (argumentBindings.reverse ++ []) :=
    MatchBagRel.cons 0 (by simp) askMatch restMatch headMerge
  have collectionMatch :
      MatchRel
        (.collection cut
          [.apply (askLabel constructor) [], .apply constructor (argPatterns arity)] none)
        (.collection cut
          [.apply (askLabel constructor) [], .apply constructor arguments] none)
        (argumentBindings.reverse ++ []) := by
    by_cases vector : cut = .vec
    · subst cut
      exact .vector (.cons askMatch (.cons constructorMatch .nil tailMerge) headMerge)
    · exact .collection vector bagMatch
  refine ⟨argumentBindings.reverse ++ [],
    matchPattern_iff_matchRel.mpr collectionMatch, ?_⟩
  have nodup : (((argumentBindings.reverse ++ []).map Prod.fst)).Nodup := by
    simp only [List.append_nil, List.map_reverse, List.nodup_reverse]
    exact argumentNodup
  have pairs : ∀ pair ∈ (argVars arity).zip arguments,
      pair ∈ argumentBindings.reverse ++ [] := by
    intro pair member
    simpa using argumentPairs pair member
  have delivered :
      ((argVars arity).map Pattern.fvar).map (applyBindings (argumentBindings.reverse ++ []))
        = arguments :=
    Mettapedia.OSLF.MeTTaIL.LinearMatch.applyBindings_fvars _ nodup
      (argVars arity) arguments (by rw [argVars_length, length]) pairs
  simpa [openingRule, applyBindings, argPatterns] using delivered

/-- **So the instrument reads the head exactly.**  This is the iff a
reconstruction argument descends on: bisimilarity forces the same opening
requests to fire, and a firing determines the head. -/
theorem openingRule_match_iff
    (cut : CollType) (constructor : String) (arity : Nat) (term : Pattern) :
    (∃ bindings, bindings ∈ matchPattern (openingRule cut constructor arity).left
        (.collection cut [.apply (askLabel constructor) [], term] none))
      ↔ ∃ arguments : List Pattern,
          term = .apply constructor arguments ∧ arguments.length = arity := by
  constructor
  · rintro ⟨bindings, matched⟩
    exact headed_of_openingRule_match matched
  · rintro ⟨arguments, rfl, length⟩
    obtain ⟨bindings, matched, -⟩ := openingRule_match_of_headed cut constructor arity length
    exact ⟨bindings, matched⟩

/-! ### And the projections expose the arguments

Head-reading tells the observer *which* constructor it is looking at.  The
projection rules tell it *what the constructor was applied to*, and they are
linear for the same reason, so the same two facts settle them: the rule matches,
and the argument it delivers is the one at that position. -/

theorem projectionRule_right (constructor : String) {arity index : Nat}
    (bounded : index < arity) :
    (projectionRule constructor arity index).right
      = .fvar ((argVars arity)[index]'(by rw [argVars_length]; exact bounded)) := by
  have nameBound : index < (argVars arity).length := by
    rw [argVars_length]; exact bounded
  simp only [projectionRule, argPatterns, List.getElem?_map,
    List.getElem?_eq_getElem nameBound, Option.map_some, Option.getD_some]

/-- **The projection reads the argument.**  The request for position `i` matches
the rule, and applying the bindings it produces to the rule's right-hand side
delivers the `i`-th argument. -/
theorem projectionRule_exposes
    (constructor : String) {arity index : Nat} (bounded : index < arity)
    {arguments : List Pattern} (length : arguments.length = arity) :
    ∃ bindings,
      bindings ∈ matchPattern (projectionRule constructor arity index).left
          (.apply (getLabel constructor index)
            [.apply (argsLabel constructor) arguments]) ∧
        applyBindings bindings (projectionRule constructor arity index).right
          = arguments[index]'(by rw [length]; exact bounded) := by
  obtain ⟨argumentBindings, argumentMember, argumentNodup, -, argumentPairs⟩ :=
    Mettapedia.OSLF.MeTTaIL.LinearMatch.matchArgs_fvars (argVars arity) arguments
      (argVars_nodup arity) (by rw [argVars_length, length])
  have nameBound : index < (argVars arity).length := by
    rw [argVars_length]; exact bounded
  have termBound : index < arguments.length := by rw [length]; exact bounded
  have zipBound : index < ((argVars arity).zip arguments).length := by
    rw [List.length_zip]; omega
  have pairMember : ((argVars arity)[index]'nameBound, arguments[index]'termBound)
      ∈ argumentBindings := by
    refine argumentPairs _ ?_
    have entry : ((argVars arity).zip arguments)[index]'zipBound
        = ((argVars arity)[index]'nameBound, arguments[index]'termBound) :=
      List.getElem_zip
    exact entry ▸ List.getElem_mem zipBound
  have lookup : argumentBindings.find?
      (fun entry => entry.1 == (argVars arity)[index]'nameBound)
      = some ((argVars arity)[index]'nameBound, arguments[index]'termBound) :=
    Mettapedia.OSLF.MeTTaIL.LinearMatch.find?_of_mem_of_nodup argumentBindings
      argumentNodup pairMember
  have innerMatch :
      MatchRel (.apply (argsLabel constructor) (argPatterns arity))
        (.apply (argsLabel constructor) arguments) argumentBindings :=
    MatchRel.apply (matchArgs_iff_matchArgsRel.mp argumentMember)
      (by rw [argPatterns_length, length])
  have outerMerge : mergeBindings argumentBindings [] = some argumentBindings := by
    simp [mergeBindings]
  refine ⟨argumentBindings, ?_, ?_⟩
  · exact matchPattern_iff_matchRel.mpr
      (MatchRel.apply
        (MatchArgsRel.cons innerMatch MatchArgsRel.nil outerMerge) rfl)
  · rw [projectionRule_right constructor bounded]
    simp only [applyBindings, lookup]


/-- **And it delivers that argument however it matched.**  `projectionRule_exposes`
exhibits *a* binding list with the delivery property; an inversion supplies one
that merely matches, and the two are the same object only because every match of
a list of distinct metavariables binds each to the term at its position.  This is
the version an inversion can use. -/
theorem projectionRule_delivers_of_match
    (constructor : String) {arity index : Nat} (bounded : index < arity)
    {arguments : List Pattern} (length : arguments.length = arity)
    {bindings : Bindings}
    (matched : bindings ∈ matchPattern (projectionRule constructor arity index).left
      (.apply (getLabel constructor index)
        [.apply (argsLabel constructor) arguments])) :
    applyBindings bindings (projectionRule constructor arity index).right
      = arguments[index]'(by rw [length]; exact bounded) := by
  have nameBound : index < (argVars arity).length := by
    rw [argVars_length]; exact bounded
  have termBound : index < arguments.length := by rw [length]; exact bounded
  have relational := matchPattern_iff_matchRel.mp matched
  simp only [projectionRule] at relational
  have outerArgs := matchRel_apply_args relational
  cases outerArgs with
  | cons innerMatch tailMatch outerMerge =>
      cases tailMatch
      rename_i innerBindings
      have sameBindings : bindings = innerBindings := by
        simpa [mergeBindings] using outerMerge.symm
      have innerArgs := matchRel_apply_args innerMatch
      obtain ⟨-, nodup, pairs⟩ :=
        Mettapedia.OSLF.MeTTaIL.LinearMatch.matchArgsRel_fvars_inversion
          (argVars arity) arguments innerBindings innerArgs (argVars_nodup arity)
      have zipBound : index < ((argVars arity).zip arguments).length := by
        rw [List.length_zip]; omega
      have pairMember : ((argVars arity)[index]'nameBound,
          arguments[index]'termBound) ∈ innerBindings := by
        refine pairs _ ?_
        have entry : ((argVars arity).zip arguments)[index]'zipBound
            = ((argVars arity)[index]'nameBound, arguments[index]'termBound) :=
          List.getElem_zip
        exact entry ▸ List.getElem_mem zipBound
      have lookup := Mettapedia.OSLF.MeTTaIL.LinearMatch.find?_of_mem_of_nodup
        innerBindings nodup pairMember
      rw [sameBindings, projectionRule_right constructor bounded]
      simp only [applyBindings, lookup]

/-- **The opening rule delivers the bundle however it matched.**  The companion of
`projectionRule_delivers_of_match` on the other instrument.  The bag match pairs
the request against the request -- the alternative pairing would need the term to
be the request itself, which `askLabel_ne_self` refuses -- so the constructor
pattern faces the term, and the inversion for distinct metavariables says what the
resulting bindings carry. -/
theorem openingRule_delivers_of_match
    (cut : CollType) (constructor : String) {arity : Nat}
    {arguments : List Pattern} (length : arguments.length = arity)
    {bindings : Bindings}
    (matched : bindings ∈ matchPattern (openingRule cut constructor arity).left
      (.collection cut
        [.apply (askLabel constructor) [], .apply constructor arguments] none)) :
    applyBindings bindings (openingRule cut constructor arity).right
      = .apply (argsLabel constructor) arguments := by
  have relational := matchPattern_iff_matchRel.mp matched
  simp only [openingRule] at relational
  have bagMatch := matchRel_collection_noRest_to_bag relational
  cases bagMatch with
  | cons index bounded askMatch restMatch merged =>
      match index, bounded with
      | 0, _ =>
          simp only [List.eraseIdx_zero, List.tail_cons] at restMatch
          have askEmpty := matchRel_apply_args askMatch
          cases askEmpty
          cases restMatch with
          | cons innerIndex innerBounded constructorMatch tailMatch innerMerge =>
              match innerIndex, innerBounded with
              | 0, _ =>
                  simp only [List.getElem_cons_zero] at constructorMatch
                  cases tailMatch
                  have argumentsMatch := matchRel_apply_args constructorMatch
                  obtain ⟨-, nodup, pairs⟩ :=
                    Mettapedia.OSLF.MeTTaIL.LinearMatch.matchArgsRel_fvars_inversion
                      (argVars arity) arguments _ argumentsMatch (argVars_nodup arity)
                  rename_i constructorBindings _
                  have argumentsMatch := matchRel_apply_args constructorMatch
                  obtain ⟨-, nodup, pairs⟩ :=
                    Mettapedia.OSLF.MeTTaIL.LinearMatch.matchArgsRel_fvars_inversion
                      (argVars arity) arguments constructorBindings
                      argumentsMatch (argVars_nodup arity)
                  have restEq := Option.some.inj (innerMerge.symm.trans
                    (show mergeBindings constructorBindings []
                        = some constructorBindings by simp [mergeBindings]))
                  rw [restEq] at merged
                  have fresh := Mettapedia.OSLF.MeTTaIL.LinearMatch.mergeBindings_of_fresh
                    constructorBindings [] (by simp) nodup
                  rw [fresh] at merged
                  have shape : bindings = constructorBindings.reverse ++ [] := by
                    simpa using merged.symm
                  subst shape
                  have reversedNodup :
                      ((constructorBindings.reverse ++ []).map Prod.fst).Nodup := by
                    simp only [List.append_nil, List.map_reverse, List.nodup_reverse]
                    exact nodup
                  have reversedPairs : ∀ pair ∈ (argVars arity).zip arguments,
                      pair ∈ constructorBindings.reverse ++ [] := by
                    intro pair member
                    simpa using List.mem_reverse.mpr (pairs pair member)
                  have delivered :=
                    Mettapedia.OSLF.MeTTaIL.LinearMatch.applyBindings_fvars _
                      reversedNodup (argVars arity) arguments
                      (by rw [argVars_length, length]) reversedPairs
                  simpa [openingRule, applyBindings, argPatterns] using delivered
      | 1, _ =>
          simp only [List.getElem_cons_succ, List.getElem_cons_zero] at askMatch
          simp only [List.eraseIdx_cons_succ, List.eraseIdx_zero,
            List.tail_cons] at restMatch
          cases restMatch with
          | cons innerIndex innerBounded constructorMatch tailMatch innerMerge =>
              match innerIndex, innerBounded with
              | 0, _ =>
                  simp only [List.getElem_cons_zero] at constructorMatch
                  exact absurd (matchRel_apply_head constructorMatch).symm
                    (askLabel_ne_self constructor)

/-! ## The gap is nonempty

Two nullary constructors occurring in no rule and no equation.  In the authored
theory nothing steps at all, so no context separates them.  Give the observer
the instrument for one of them and a context does: the opening request beside
the first is a redex, beside the second it is not.  So the structural
distinction the generated logic draws is a real distinction — the extension is
closing a gap that was there, not manufacturing one. -/

namespace Gap

/-- The sort the canary's constructors inhabit. -/
def sortT : String := "T"

/-- A declared nullary constructor. -/
def declC : GrammarRule where
  label := "C"
  category := sortT
  params := []
  syntaxPattern := [.terminal "C"]

/-- A second declared nullary constructor, which the observer may not open. -/
def declD : GrammarRule where
  label := "D"
  category := sortT
  params := []
  syntaxPattern := [.terminal "D"]

/-- A declared unary constructor, so that a round trip has something to carry. -/
def declE : GrammarRule where
  label := "E"
  category := sortT
  params := [.simple "x" (.base sortT)]
  syntaxPattern := [.terminal "E"]

/-- A presentation with three inert constructors and no rules at all. -/
def inertPair : LanguageDef where
  name := "InertPair"
  types := [TypeDecl.plain sortT]
  terms := [declC, declD, declE]
  equations := []
  rewrites := []

/-- The observer may open the first and third constructors only. -/
def opened : List String := ["C", "E"]

/-- The extended presentation. -/
def extended : LanguageDef := observerExtension inertPair .hashBag opened

/-- The opening request. -/
def askC : Pattern := .apply (askLabel "C") []

/-- The first constructor. -/
def termC : Pattern := .apply "C" []

/-- The second constructor. -/
def termD : Pattern := .apply "D" []

/-- The opening rule the instrument set generates. -/
def openC : RewriteRule := openingRule .hashBag "C" 0

theorem openC_mem : openC ∈ extended.rewrites := by
  simp [extended, observerExtension, inertPair, opened, openedRules,
    instrumentRules, projectablePositions, declC, declD, declE, openC]

/-- Nothing steps in the authored theory: it has no rules at all. -/
theorem inertPair_no_step (base : BasePremiseEvaluator) (source target : Pattern) :
    ¬ Step base inertPair source target := by
  refine not_step_of_matchPatternForRule_eq_nil ?_
  intro rule member
  exact absurd member (by simp [inertPair])

/-- The request beside the first constructor is a redex. -/
theorem withC_match :
    matchPatternForRule extended openC
      (.collection .hashBag [askC, termC] none) = [[]] := by
  decide +kernel

/-- Beside the second constructor it is not. -/
theorem withD_no_match :
    matchPatternForRule extended openC
      (.collection .hashBag [askC, termD] none) = [] := by
  decide +kernel

/-- So the instrumented theory does step on the first. -/
theorem withC_steps (base : BasePremiseEvaluator) :
    Step base extended (.collection .hashBag [askC, termC] none)
      (applyBindingsForRule extended openC []) :=
  ⟨1, .rule openC_mem (by rw [withC_match]; exact List.Mem.head _) (.nil []) rfl⟩

/-- And does not step on the second: no rule of the extension matches it. -/
theorem withD_no_step (base : BasePremiseEvaluator) (target : Pattern) :
    ¬ Step base extended (.collection .hashBag [askC, termD] none) target := by
  refine not_step_of_matchPatternForRule_eq_nil ?_
  intro rule member
  have enumerated : rule = openingRule .hashBag "C" 0 ∨
      rule = buildRule "C" 0 ∨ rule = openingRule .hashBag "E" 1 ∨
      rule = buildRule "E" 1 ∨ rule = projectionRule "E" 1 0 := by
    simpa [extended, observerExtension, inertPair, opened, openedRules,
      instrumentRules, projectablePositions, declC, declD, declE, sortT]
      using member
  rcases enumerated with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-! ### Freshness is checked, and conservativity follows

The condition on the administrative vocabulary is decidable, so the canary
discharges it by computation rather than by assertion, and a presentation that
already uses one of the adjoined labels is exhibited failing it. -/

/-- The canary's administrative vocabulary is fresh. -/
theorem inertPair_fresh : AdministrativeFresh inertPair opened := by
  decide +kernel

/-- A presentation that already declares the request former.  It is here to
show the condition is not vacuous. -/
def collidingPair : LanguageDef where
  name := "CollidingPair"
  types := [TypeDecl.plain sortT]
  terms :=
    [declC,
      { label := askLabel "C"
        category := sortT
        params := []
        syntaxPattern := [.terminal "collide"] }]
  equations := []
  rewrites := []

/-- And it fails the condition. -/
theorem collidingPair_not_fresh :
    ¬ AdministrativeFresh collidingPair ["C"] := by
  decide +kernel

/-- **Conservativity on the canary.**  A term headed by an authored operation
rewrites identically in the authored theory and in the extension. -/
theorem inertPair_conservative (base₁ base₂ : BasePremiseEvaluator) (fuel : Nat) :
    rewriteAt base₁ inertPair fuel termC
      = rewriteAt base₂ extended fuel termC :=
  rewriteAt_eq_of_authored_head inertPair .hashBag opened
    (names := ["C", "D", "E"]) (by decide +kernel) inertPair_fresh
    (by intro rule member; exact absurd member (by simp [inertPair]))
    base₁ base₂ fuel (by simp [termC, HasOperationHead])

/-! ### The kit is not a one-way mirror

The unary constructor, opened and then rebuilt.  Opening carries the argument
into the freely adjoined bundle; the build rule carries it back to the term it
came from.  Both halves are kernel-checked against the extension's own adjoined
rules, so the observer's kit is invertible on what it takes apart. -/

/-- The opening request for the unary constructor. -/
def askE : Pattern := .apply (askLabel "E") []

/-- An arbitrary declared argument. -/
def argument : Pattern := termD

/-- The unary constructor applied to it. -/
def termE : Pattern := .apply "E" [argument]

/-- The bundle the opening yields, a term of the freely adjoined sort. -/
def bundleE : Pattern := .apply (argsLabel "E") [argument]

/-- The rebuild request applied to that bundle. -/
def buildE : Pattern := .apply (buildLabel "E") [bundleE]

/-- The opening rule for the unary constructor. -/
def openE : RewriteRule := openingRule .hashBag "E" 1

/-- The build rule for the unary constructor. -/
def buildRuleE : RewriteRule := buildRule "E" 1

/-- The bindings both halves produce. -/
def bindingsE : List (String × Pattern) := [("obsArg0", argument)]

theorem openE_mem : openE ∈ extended.rewrites := by
  simp [extended, observerExtension, inertPair, opened, openedRules,
    instrumentRules, projectablePositions, declC, declD, declE, openE]

theorem buildRuleE_mem : buildRuleE ∈ extended.rewrites := by
  simp [extended, observerExtension, inertPair, opened, openedRules,
    instrumentRules, projectablePositions, declC, declD, declE, buildRuleE]

theorem openE_match :
    matchPatternForRule extended openE
      (.collection .hashBag [askE, termE] none) = [bindingsE] := by
  decide +kernel

theorem openE_apply :
    applyBindingsForRule extended openE bindingsE = bundleE := by
  decide +kernel

theorem buildE_match :
    matchPatternForRule extended buildRuleE buildE = [bindingsE] := by
  decide +kernel

theorem buildE_apply :
    applyBindingsForRule extended buildRuleE bindingsE = termE := by
  decide +kernel

/-- **The round trip.**  The request beside the term steps to the argument
bundle, and the rebuild request on that bundle steps back to the term. -/
theorem open_then_build (base : BasePremiseEvaluator) :
    Step base extended (.collection .hashBag [askE, termE] none) bundleE ∧
      Step base extended buildE termE := by
  refine ⟨openE_apply ▸ ?_, buildE_apply ▸ ?_⟩
  · exact ⟨1, .rule openE_mem (by rw [openE_match]; exact List.Mem.head _)
      (.nil bindingsE) rfl⟩
  · exact ⟨1, .rule buildRuleE_mem (by rw [buildE_match]; exact List.Mem.head _)
      (.nil bindingsE) rfl⟩

end Gap

end Mettapedia.OSLF.Framework.ObserverExtension
