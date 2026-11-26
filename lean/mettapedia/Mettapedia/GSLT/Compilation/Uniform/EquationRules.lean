import Mettapedia.GSLT.Compilation.Uniform.DemandRules
import Mettapedia.GSLT.Compilation.Uniform.CollectionLaws
import Mettapedia.GSLT.LanguageDef.EquationSemantics
import Mettapedia.OSLF.MeTTaIL.ReferenceStepEquations
import Mettapedia.GSLT.LanguageDef.CanonicalPresentation

/-!
# Equations as clauses

A language's equations hold in both directions and in every context. They compile to clauses of a second relation,
one equation step, beside the relation of steps:

* each orientation of an equation is a triple, like a rule: one side is matched, the premises hold, and the other
  side is instantiated scope-correctly (`DemandRules.tripleClause`). Each triple also has its converse, which reads an
  instance of the other side back to every term the first side matches (`DemandRules.converseClause`). So the relation
  is one equation step of the source, or one taken back;
* fixed congruence clauses carry one equation step into an argument of an application, the body of a binder, either
  part of an explicit substitution, or an element of a collection, through a third relation on lists
  (`congruenceClauses`). They read the encoding of terms, where every name is a row, so the same clauses serve every
  language and every constructor name;
* the laws a presentation derives from its collection carriers and algebras (bags and sets are unordered, sets drop
  duplicates, an algebra flattens, reads a singleton as its element and absorbs its unit) are clauses of their own
  relation, guarded by typing (`CollectionLaws`); one fixed clause reads an instance of a law, in either direction,
  as one equation step (`lawStepClause`).

A name of the first side that the other side lacks is not read off the instance, nor is a value the other side
substitutes: taken back, the equation chooses them. A clause program builds terms only from the labels of its clauses and of its input, so the program is given a
finite supply of labels, and a chosen value is any datum whose labels are in the supply (`DataClauses.datum_iff`).

At data, the least model of these clauses over a supply is one equation step of the source in a context, or one taken
back whose chosen values are over the supply, to data (`derives_equation_iff`), when both orientations of every
equation have the shape of a rule (`EquationClauses`). Over every supply, these steps generate the source's equivalence
through data, and every path of that equivalence is a path of them over some supply (`eqvGen_dataStep_iff`,
`eqvGen_paths`).

A run moves along two relations: steps and equation steps (`moves`). A move over a supply is a reference step from data
or an equation step over the supply (`MoveWithin`), and the run's moves are exactly these moves on the transform step
(`rowCorrespondence`, `compiledCorrespondence`). Moves over any supply reach only what the source reaches by steps
modulo equivalence through data (`StepModuloOnData`), and what it reaches so, moves over some supply reach
(`moves_sound`, `moves_complete`, `reachModulo_iff`). `StepModuloOnData` implies the reference relation modulo equations
(`stepModulo_of_onData`). Controls: `collapse_compiles`, `collapse_chooses`, `collapse_needs_the_supply`, `chaos_compiles`,
`chaos_chooses`.

Rules and equations may hold binders, their premises and other sides instantiated scope-correctly, and quantified
premises, whose clauses the program holds beside them (`quantifiedPremiseClauses`, `equationQuantifiedClauses`). An
equation side may hold explicit substitutions: taken back, the substituted value is chosen over the supply and the
instance is abstracted over it, which reads every body back (`ScopeClauses.abstract_iff`). Controls:
`betaEquation_compiles`, `beta_expands`, `beta_needs_the_supply`.

Premises are read as the source reads them, at the names bound before each: a name nothing has bound yet stands for
itself, in a step premise's source, a freshness condition, a query's request and a quantified premise's collection, and
in a rule's right side. A query asks for the rows of its arguments read so; no condition on the relations is needed,
beside rows of data for requests of data (`DataRows`). Controls: `stepped_relates`, `literalStep_needs_the_name`,
`unboundFresh_steps`, `unboundFresh_reads_the_name`, `everyUnbound_never_fires`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.Uniform.EquationRules

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec (MatchRel matchPattern_sound matchPattern_iff_matchRel)
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.PredFiniteSufficient (lookupOrFvar BindingsValued)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax
open RuleSyntax.Presentation.Schematic
open RuleSyntax.Machines (unknowns)
open RuleSyntax.ComputedConditions (Relations RuleWithCondition Condition relationGraph programSystem specialized
  rows relationCorrespondence)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep (Step StepValid PremisesValid PremiseValid Witness EquationStep
  AuthoredEquation Generator captureSitesOf stepDepth stepEndpoints)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.OSLF.MeTTaIL.PatternCode (collectionCode)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (DerivedInstance readsRaw no_derivedInstance_of_no_derived_laws)
open RootRewritesOnTheStep (labelCode symTerm appTerm encode encodeList optionRow namesRow numeral)
open OrderedMatching (isData isDataList isDataList_iff names)
open OrderedRows (lower? lowerThen? unknowns_lower unknowns_lowerThen)
open QueryPremises (DataRows)
open StepPremises (Flows Hold TripleShape triple_data)
open DemandTransformation (Goal Clause goalHolds goalInputs goalUnknowns boundAt DerivesAt Derives derives_of_clause
  runRules AtRow Moves bagSystem pick)
open DemandRules (premiseRelations stepRelation tripleClause tripleClause_relation converseClause
  converseClause_relation premiseGoals premiseGoal tripleChecked tripleChecked_spec ruleClauses ruleClauses_spec
  RuleClauses Refusal triple_sound triple_complete converse_sound converse_complete step_of_derivesAt
  derives_step_iff ForAllClauses QuantifiedPresent premisesQuantified derivesAt_unfolds quantifiedPremiseClauses
  quantifiedPremiseClauses_relation quantifiedClauses quantifiedClauses_present quantifiedClauses_moded
  quantifiedClauses_origin quantified_relation listOfClauses_moded TripleWithin freeNames)
open CollectionMatching (CollectionProgram pickClauses wrapClauses insertClauses unwrapClauses pickRelation
  wrapRelation insertRelation unwrapRelation)
open CollectionLaws (lawRelation LawProgram derivedInstance_data)
open PatternRows (encode_apply_inv encode_lambda_inv encode_multiLambda_inv encode_subst_inv encode_collection_inv
  encodeList_cons_inv)

/-! ## The clauses -/

/-- The relation of one equation step. -/
def equationRelation : ℕ := 1

/-- The relation of one equation step inside a list. -/
def elementRelation : ℕ := 2

/-- The clause of one equation step inside the arguments of an application. -/
def applyClause : Clause :=
  { relation := equationRelation, input := appTerm (symTerm 2) (appTerm (.var 0) (.var 1)),
    output := appTerm (symTerm 2) (appTerm (.var 0) (.var 2)), body := [.ask elementRelation (.var 1) (.var 2)] }

/-- The clause of one equation step inside the body of a binder. -/
def lambdaClause : Clause :=
  { relation := equationRelation, input := appTerm (symTerm 3) (appTerm (.var 0) (.var 1)),
    output := appTerm (symTerm 3) (appTerm (.var 0) (.var 2)), body := [.ask equationRelation (.var 1) (.var 2)] }

/-- The clause of one equation step inside the body of a binder of several names. -/
def multiLambdaClause : Clause :=
  { relation := equationRelation, input := appTerm (symTerm 4) (appTerm (.var 0) (appTerm (.var 1) (.var 2))),
    output := appTerm (symTerm 4) (appTerm (.var 0) (appTerm (.var 1) (.var 3))),
    body := [.ask equationRelation (.var 2) (.var 3)] }

/-- The clause of one equation step inside the body of an explicit substitution. -/
def substBodyClause : Clause :=
  { relation := equationRelation, input := appTerm (symTerm 5) (appTerm (.var 0) (.var 1)),
    output := appTerm (symTerm 5) (appTerm (.var 2) (.var 1)), body := [.ask equationRelation (.var 0) (.var 2)] }

/-- The clause of one equation step inside the replacement of an explicit substitution. -/
def substValueClause : Clause :=
  { relation := equationRelation, input := appTerm (symTerm 5) (appTerm (.var 0) (.var 1)),
    output := appTerm (symTerm 5) (appTerm (.var 0) (.var 2)), body := [.ask equationRelation (.var 1) (.var 2)] }

/-- The clause of one equation step inside the elements of a collection. -/
def collectionClause : Clause :=
  { relation := equationRelation, input := appTerm (symTerm 6) (appTerm (.var 0) (appTerm (.var 1) (.var 2))),
    output := appTerm (symTerm 6) (appTerm (.var 0) (appTerm (.var 3) (.var 2))),
    body := [.ask elementRelation (.var 1) (.var 3)] }

/-- The clause of one equation step in the first element of a list. -/
def headClause : Clause :=
  { relation := elementRelation, input := appTerm (.var 0) (.var 1), output := appTerm (.var 2) (.var 1),
    body := [.ask equationRelation (.var 0) (.var 2)] }

/-- The clause of one equation step in a later element of a list. -/
def tailClause : Clause :=
  { relation := elementRelation, input := appTerm (.var 0) (.var 1), output := appTerm (.var 0) (.var 2),
    body := [.ask elementRelation (.var 1) (.var 2)] }

/-- **The congruence clauses**: one equation step inside each part of a term. -/
def congruenceClauses : List Clause :=
  [applyClause, lambdaClause, multiLambdaClause, substBodyClause, substValueClause, collectionClause, headClause,
    tailClause]

theorem congruenceClauses_moded : ∀ c ∈ congruenceClauses, DemandTransformation.Moded c := by
  intro c inside
  simp only [congruenceClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact DemandTransformation.moded_of_check (by decide)

/-- **The clause of the laws**: an instance of a law, in either direction, is one equation step. -/
def lawStepClause : Clause :=
  { relation := equationRelation, input := .var 0, output := .var 1, body := [.ask lawRelation (.var 0) (.var 1)] }

theorem lawStepClause_moded : DemandTransformation.Moded lawStepClause :=
  DemandTransformation.moded_of_check (by decide)

/-- **The clauses that decide the laws**: typing (with unification and telling unknowns apart), the guards of bags
and sets, lists, and the laws themselves. -/
def lawProgramClauses (language : LanguageDef) : List Clause :=
  TypingClauses.typingClauses ++ TypingClauses.grammarClauses language ++ UnificationClauses.unificationClauses ++
    TypingClauses.differClauses ++ [TypingClauses.typedClause] ++ CollectionLaws.guardClauses language ++
    CollectionLaws.listClauses ++ CollectionLaws.lawClauses language

/-- **The clauses of an equation**: each orientation is a triple, matching one side and instantiating the other
scope-correctly, with its converse, which reads the instance back and chooses over the supply what the instance does
not determine: the names of the matched side that the other side lacks, and the values the other side substitutes;
refused by the equation's name. -/
def equationClauses (equation : Equation) : Except Refusal (List Clause) :=
  if readsRaw equation then
    match tripleChecked tripleClause equationRelation equation.name equation.left equation.right equation.premises,
        tripleChecked converseClause equationRelation equation.name equation.left equation.right equation.premises,
        tripleChecked tripleClause equationRelation equation.name equation.right equation.left equation.premises,
        tripleChecked converseClause equationRelation equation.name equation.right equation.left equation.premises with
    | .ok forward, .ok forwardBack, .ok reverse, .ok reverseBack => .ok [forward, forwardBack, reverse, reverseBack]
    | .error reason, _, _, _ => .error reason
    | .ok _, .error reason, _, _ => .error reason
    | .ok _, .ok _, .error reason, _ => .error reason
    | .ok _, .ok _, .ok _, .error reason => .error reason
  else .error (.declaredBinding equation.name)

/-- The clauses of some equations, in their order. -/
def allEquationClauses : List Equation → Except Refusal (List Clause)
  | [] => .ok []
  | equation :: equations =>
      match equationClauses equation, allEquationClauses equations with
      | .ok here, .ok later => .ok (here ++ later)
      | .error reason, _ => .error reason
      | .ok _, .error reason => .error reason

/-- The clauses of collections: picking, wrapping, inserting, unwrapping. -/
def collectionClauses : List Clause := pickClauses ++ wrapClauses ++ insertClauses ++ unwrapClauses

/-- The clauses of the quantified premises of equations, in both orientations. -/
def equationQuantifiedClauses (equations : List Equation) : List Clause :=
  equations.flatMap fun e => quantifiedClauses e.left e.right e.premises ++ quantifiedClauses e.right e.left e.premises

/-- **The clauses of a language**: its rules, the clauses of collections, of scopes, of lowering, of quantified
premises and of data over a supply; and when its presentation has equations or laws, the orientations of the equations,
the congruence clauses, the clause of the laws and the clauses that decide them. The supply is given with a run; it does
not change what the compiler refuses. -/
def clausesOf (language : LanguageDef) (supply : List String) : Except Refusal (List Clause) :=
  match ruleClauses language.rewrites, allEquationClauses language.equations with
  | .ok rules, .ok equations =>
      .ok (rules ++ collectionClauses ++ ScopeClauses.scopeClauses ++ (ScopeClauses.lowerClauses ++ ScopeClauses.abstractClauses) ++
        (quantifiedPremiseClauses language.rewrites ++ equationQuantifiedClauses language.equations) ++
        (DataClauses.dataClauses ++ DataClauses.supplyClauses supply) ++
        if language.isEquationFree then [] else
          equations ++ congruenceClauses ++ lawStepClause :: lawProgramClauses language)
  | .error reason, _ => .error reason
  | .ok _, .error reason => .error reason

/-- The relations a run moves along: steps, and equation steps. -/
def moves : List ℕ := [stepRelation, equationRelation]

/-- **The compiler**: the run of the clauses of the language's canonical presentation, whose binders carry no display
names (`LanguageDef.eraseBinderMetadata`). -/
def compile (language : LanguageDef) (supply : List String) :
    Except Refusal (List (RuleWithCondition ℕ Tm)) :=
  (clausesOf language.eraseBinderMetadata supply).map fun program => runRules program moves

/-! ## What the compiler checked -/

/-- **The clauses of a language's equations** in a program. -/
structure EquationClauses (language : LanguageDef) (program : List Clause) : Prop where
  raw : ∀ e ∈ language.equations, readsRaw e = true
  forwardShape : ∀ e ∈ language.equations, TripleShape e.left e.right e.premises
  reverseShape : ∀ e ∈ language.equations, TripleShape e.right e.left e.premises
  forwardClause : ∀ e ∈ language.equations, ∃ c ∈ program,
    tripleClause equationRelation e.left e.right e.premises = some c
  forwardConverse : ∀ e ∈ language.equations, ∃ c ∈ program,
    converseClause equationRelation e.left e.right e.premises = some c
  reverseClause : ∀ e ∈ language.equations, ∃ c ∈ program,
    tripleClause equationRelation e.right e.left e.premises = some c
  reverseConverse : ∀ e ∈ language.equations, ∃ c ∈ program,
    converseClause equationRelation e.right e.left e.premises = some c
  forwardQuantified : ∀ e ∈ language.equations, QuantifiedPresent program
    (premisesQuantified (DemandRules.tripleRests e.left e.right) (captureSitesOf e.left e.premises) (names e.left)
      e.premises)
  reverseQuantified : ∀ e ∈ language.equations, QuantifiedPresent program
    (premisesQuantified (DemandRules.tripleRests e.right e.left) (captureSitesOf e.right e.premises) (names e.right)
      e.premises)
  converses : Instantiation.ConverseClauses program
  congruence : language.isEquationFree = false → ∀ c ∈ congruenceClauses, c ∈ program
  lawStep : language.isEquationFree = false → lawStepClause ∈ program
  laws : language.isEquationFree = false → ∀ R : Relations,
    (∀ x y : String, R 0 [encode (.fvar x), encode (.fvar y)] (.sym 0) ↔ x ≠ y) → LawProgram language R program
  onlyThese : ∀ c ∈ program, c.relation = equationRelation ∨ c.relation = elementRelation →
    (∃ e ∈ language.equations, tripleClause equationRelation e.left e.right e.premises = some c ∨
      converseClause equationRelation e.left e.right e.premises = some c ∨
      tripleClause equationRelation e.right e.left e.premises = some c ∨
      converseClause equationRelation e.right e.left e.premises = some c) ∨ c ∈ congruenceClauses ∨
      (c = lawStepClause ∧ language.isEquationFree = false)


theorem equationClauses_spec {equation : Equation} {cs : List Clause}
    (computed : equationClauses equation = .ok cs) :
    readsRaw equation = true ∧
      TripleShape equation.left equation.right equation.premises ∧
      TripleShape equation.right equation.left equation.premises ∧
      ∃ forward forwardBack reverse reverseBack, cs = [forward, forwardBack, reverse, reverseBack] ∧
        tripleClause equationRelation equation.left equation.right equation.premises = some forward ∧
        converseClause equationRelation equation.left equation.right equation.premises = some forwardBack ∧
        tripleClause equationRelation equation.right equation.left equation.premises = some reverse ∧
        converseClause equationRelation equation.right equation.left equation.premises = some reverseBack := by
  unfold equationClauses at computed
  split at computed
  · rename_i raw
    split at computed
    · rename_i forward forwardBack reverse reverseBack forwardChecked forwardBackChecked reverseChecked
        reverseBackChecked
      cases computed
      obtain ⟨forwardShape, forwardLowered⟩ := tripleChecked_spec forwardChecked
      obtain ⟨-, forwardBackLowered⟩ := tripleChecked_spec forwardBackChecked
      obtain ⟨reverseShape, reverseLowered⟩ := tripleChecked_spec reverseChecked
      obtain ⟨-, reverseBackLowered⟩ := tripleChecked_spec reverseBackChecked
      exact ⟨raw, forwardShape, reverseShape, forward, forwardBack, reverse, reverseBack,
        rfl, forwardLowered, forwardBackLowered, reverseLowered, reverseBackLowered⟩
    all_goals cases computed
  · cases computed

theorem allEquationClauses_spec : ∀ {equations : List Equation} {cs : List Clause},
    allEquationClauses equations = .ok cs →
      (∀ e ∈ equations, readsRaw e = true ∧ TripleShape e.left e.right e.premises ∧
        TripleShape e.right e.left e.premises ∧
        (∃ c ∈ cs, tripleClause equationRelation e.left e.right e.premises = some c) ∧
        (∃ c ∈ cs, converseClause equationRelation e.left e.right e.premises = some c) ∧
        (∃ c ∈ cs, tripleClause equationRelation e.right e.left e.premises = some c) ∧
        ∃ c ∈ cs, converseClause equationRelation e.right e.left e.premises = some c) ∧
      ∀ c ∈ cs, ∃ e ∈ equations, tripleClause equationRelation e.left e.right e.premises = some c ∨
        converseClause equationRelation e.left e.right e.premises = some c ∨
        tripleClause equationRelation e.right e.left e.premises = some c ∨
        converseClause equationRelation e.right e.left e.premises = some c
  | [], cs, computed => by
      simp only [allEquationClauses, Except.ok.injEq] at computed
      subst computed
      exact ⟨fun _ inside => absurd inside List.not_mem_nil, fun _ inside => absurd inside List.not_mem_nil⟩
  | equation :: equations, cs, computed => by
      unfold allEquationClauses at computed
      split at computed
      · rename_i here later hereComputed laterComputed
        cases computed
        obtain ⟨raw, forwardShape, reverseShape, forward, forwardBack, reverse, reverseBack, rfl,
          forwardLowered, forwardBackLowered, reverseLowered, reverseBackLowered⟩ := equationClauses_spec hereComputed
        obtain ⟨laterEquations, laterClauses⟩ := allEquationClauses_spec laterComputed
        refine ⟨fun e inside => ?_, fun c inside => ?_⟩
        · rcases List.mem_cons.mp inside with rfl | inLater
          · exact ⟨raw, forwardShape, reverseShape, ⟨forward, by simp, forwardLowered⟩,
              ⟨forwardBack, by simp, forwardBackLowered⟩, ⟨reverse, by simp, reverseLowered⟩, reverseBack, by simp,
              reverseBackLowered⟩
          · obtain ⟨eRaw, eForward, eReverse, ⟨c₁, in₁, lowered₁⟩, ⟨c₂, in₂, lowered₂⟩,
              ⟨c₃, in₃, lowered₃⟩, c₄, in₄, lowered₄⟩ := laterEquations e inLater
            exact ⟨eRaw, eForward, eReverse, ⟨c₁, List.mem_append_right _ in₁, lowered₁⟩,
              ⟨c₂, List.mem_append_right _ in₂, lowered₂⟩, ⟨c₃, List.mem_append_right _ in₃, lowered₃⟩, c₄,
              List.mem_append_right _ in₄, lowered₄⟩
        · rcases List.mem_append.mp inside with inHere | inLater
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at inHere
            rcases inHere with rfl | rfl | rfl | rfl
            · exact ⟨equation, List.mem_cons_self, .inl forwardLowered⟩
            · exact ⟨equation, List.mem_cons_self, .inr (.inl forwardBackLowered)⟩
            · exact ⟨equation, List.mem_cons_self, .inr (.inr (.inl reverseLowered))⟩
            · exact ⟨equation, List.mem_cons_self, .inr (.inr (.inr reverseBackLowered))⟩
          · obtain ⟨e, eIn, lowered⟩ := laterClauses c inLater
            exact ⟨e, List.mem_cons_of_mem _ eIn, lowered⟩
      · cases computed
      · cases computed

/-! ## Reading terms off their rows -/

/-! ## Equation steps either way -/

variable {relEnv : RelationEnv} {language : LanguageDef} {program : List Clause}

theorem equationStep_fill (context : OneHoleContext) {left right : Pattern}
    (step : EquationStep relEnv language left right) :
    EquationStep relEnv language (context.fill left) (context.fill right) := by
  cases step with
  | inContext inner generator =>
      simpa [OneHoleContext.fill_comp] using (EquationStep.inContext (context.comp inner) generator)

variable (relEnv language) in
/-- **A generator taken back, its chosen names over a supply**: an orientation of a raw equation whose instance relates
`target` to `origin`, the names of its matched side that its other side lacks having values over the supply; or a
derived collection law relating `target` to `origin`. -/
def BackGenerator (supply : List String) (origin target : Pattern) : Prop :=
  (∃ e ∈ language.equations, readsRaw e = true ∧
    (TripleWithin relEnv language supply e.left e.right e.premises target origin ∨
      TripleWithin relEnv language supply e.right e.left e.premises target origin)) ∨
    DerivedInstance language target origin

variable (relEnv language) in
/-- One generator taken back over a supply, in a context. -/
def BackStep (supply : List String) (u v : Pattern) : Prop :=
  ∃ (context : OneHoleContext) (origin target : Pattern), u = context.fill origin ∧ v = context.fill target ∧
    BackGenerator relEnv language supply origin target

variable (relEnv language) in
/-- **One equation step either way over a supply**: a reference equation step, or one taken back whose chosen names
are over the supply. -/
def EitherWayStep (supply : List String) (u v : Pattern) : Prop :=
  EquationStep relEnv language u v ∨ BackStep relEnv language supply u v

theorem backStep_fill (context : OneHoleContext) {supply : List String} {left right : Pattern}
    (step : BackStep relEnv language supply left right) :
    BackStep relEnv language supply (context.fill left) (context.fill right) := by
  obtain ⟨inner, origin, target, rfl, rfl, back⟩ := step
  exact ⟨context.comp inner, origin, target, by simp [OneHoleContext.fill_comp], by simp [OneHoleContext.fill_comp], back⟩

theorem eitherWayStep_fill (context : OneHoleContext) {supply : List String} {left right : Pattern}
    (step : EitherWayStep relEnv language supply left right) :
    EitherWayStep relEnv language supply (context.fill left) (context.fill right) :=
  step.imp (equationStep_fill context) (backStep_fill context)

/-- **A generator taken back is a generator.** -/
theorem backGenerator_generator {supply : List String} {origin target : Pattern}
    (back : BackGenerator relEnv language supply origin target) : Generator relEnv language target origin := by
  rcases back with ⟨e, member, raw, forward | reverse⟩ | derived
  · obtain ⟨initial, final, witnesses, matched, passed, rfl, -⟩ := forward
    exact .inl (.forward member raw (matchPattern_iff_matchRel.mpr matched) passed)
  · obtain ⟨initial, final, witnesses, matched, passed, rfl, -⟩ := reverse
    exact .inl (.reverse member raw (matchPattern_iff_matchRel.mpr matched) passed)
  · exact .inr derived

/-- **A step taken back is an equation step the other way.** -/
theorem backStep_step {supply : List String} {u v : Pattern} (step : BackStep relEnv language supply u v) :
    EquationStep relEnv language v u := by
  obtain ⟨context, origin, target, rfl, rfl, back⟩ := step
  exact .inContext context (backGenerator_generator back)

theorem tripleWithin_mono {supply wider : List String} (more : ∀ label ∈ supply, label ∈ wider)
    {left right : Pattern} {premises : List Premise} {s t : Pattern}
    (within : TripleWithin relEnv language supply left right premises s t) :
    TripleWithin relEnv language wider left right premises s t := by
  obtain ⟨initial, final, witnesses, matched, passed, built, supplied, substituted⟩ := within
  exact ⟨initial, final, witnesses, matched, passed, built, fun name free label inside =>
    more label (supplied name free label inside), fun v inside label member =>
    more label (substituted v inside label member)⟩

theorem eitherWayStep_mono {supply wider : List String} (more : ∀ label ∈ supply, label ∈ wider) {u v : Pattern}
    (step : EitherWayStep relEnv language supply u v) : EitherWayStep relEnv language wider u v := by
  refine step.imp id fun back => ?_
  obtain ⟨context, origin, target, rfl, rfl, generator⟩ := back
  refine ⟨context, origin, target, rfl, rfl, ?_⟩
  rcases generator with ⟨e, member, raw, forward | reverse⟩ | derived
  · exact .inl ⟨e, member, raw, .inl (tripleWithin_mono more forward)⟩
  · exact .inl ⟨e, member, raw, .inr (tripleWithin_mono more reverse)⟩
  · exact .inr derived

variable (relEnv language) in
/-- One equation step either way over a supply in one element of a list. -/
def ElementStep (supply : List String) (xs ys : List Pattern) : Prop :=
  ∃ before x y after, xs = before ++ x :: after ∧ ys = before ++ y :: after ∧
    EitherWayStep relEnv language supply x y

theorem relation_ne_element_equation : elementRelation ≠ equationRelation := by decide

/-- **The source's freshness check tells two names apart.** -/
theorem premiseRelations_names (relEnv : RelationEnv) (language : LanguageDef) (x y : String) :
    premiseRelations relEnv language 0 [encode (.fvar x), encode (.fvar y)] (.sym 0) ↔ x ≠ y := by
  constructor
  · rintro (⟨_, _, _, -, many, -⟩ | ⟨name, term, same, -, fresh⟩)
    · simp at many
    · simp only [List.cons.injEq, and_true] at same
      obtain ⟨nameIs, termIs⟩ := same
      obtain rfl := Pattern.fvar.inj (RootRewritesOnTheStep.encode_injective nameIs)
      obtain rfl := RootRewritesOnTheStep.encode_injective termIs
      intro same
      subst same
      simp [Mettapedia.OSLF.MeTTaIL.Substitution.checkFreshness, Mettapedia.OSLF.MeTTaIL.Substitution.isFresh,
        Mettapedia.OSLF.MeTTaIL.Substitution.freeVars] at fresh
  · intro differ
    refine .inr ⟨x, .fvar y, rfl, rfl, ?_⟩
    by_contra notFresh
    apply differ
    simp [Mettapedia.OSLF.MeTTaIL.Substitution.checkFreshness, Mettapedia.OSLF.MeTTaIL.Substitution.isFresh,
      Mettapedia.OSLF.MeTTaIL.Substitution.freeVars] at notFresh
    exact notFresh

/-! ## The least model is one matched equation step -/

/-- **Every derivation of an equation step from data is one matched equation step in a context, to data**, and every
derivation inside a list of data is one inside one element. -/
theorem sound (dataRows : DataRows relEnv language)
    (rules : RuleClauses language program) (equations : EquationClauses language program)
    {supply : List String} (dataClauses : DataClauses.DataProgram supply program) :
    ∀ depth : ℕ,
    (∀ (s : Pattern) (w : Expr), isData s = true →
      DerivesAt (premiseRelations relEnv language) program depth equationRelation (encode s) w →
        ∃ t, w = encode t ∧ isData t = true ∧ EitherWayStep relEnv language supply s t) ∧
    (∀ (xs : List Pattern) (w : Expr), isDataList xs = true →
      DerivesAt (premiseRelations relEnv language) program depth elementRelation (encodeList xs) w →
        ∃ ys, w = encodeList ys ∧ isDataList ys = true ∧ ElementStep relEnv language supply xs ys) := by
  intro depth
  induction depth with
  | zero => exact ⟨fun _ _ _ derived => derived.elim, fun _ _ _ derived => derived.elim⟩
  | succ depth ih =>
    have keeps : ∀ u v, isData u = true → Step relEnv language u v → isData v = true :=
      fun _ _ uData stepped => StepPremises.step_data dataRows rules.shape uData stepped
    constructor
    · intro s w data derived
      obtain ⟨c, member, isEquation, θ, input, output, goals⟩ := derived
      rcases equations.onlyThese c member (.inl isEquation) with
        ⟨e, eIn, lowered | lowered | lowered | lowered⟩ | inCongruence | ⟨rfl, notFree⟩
      · obtain ⟨t, outputIs, initial, final, witnesses, matched, passed, rfl⟩ := triple_sound rules.collections
          rules.build rules.forAlls (equations.forwardShape e eIn) lowered (fun _ _ _ asked => ⟨depth, asked⟩)
          (derivesAt_unfolds depth) (fun _ _ asked => step_of_derivesAt rules depth asked) input goals
        exact ⟨_, output.symm.trans outputIs, (triple_data dataRows (equations.forwardShape e eIn) keeps data
          (fun step _ u v stepped => ⟨step, stepped⟩) matched passed).2.2.2,
          .inl (.inContext .hole (.inl (.forward eIn (equations.raw e eIn) (matchPattern_iff_matchRel.mpr matched)
            passed)))⟩
      · obtain ⟨t, outputIs, tData, within⟩ := converse_sound rules.collections rules.build equations.converses
          rules.forAlls dataClauses (equations.forwardShape e eIn) lowered (fun _ _ _ asked => ⟨depth, asked⟩)
          (derivesAt_unfolds depth) (fun _ _ asked => step_of_derivesAt rules depth asked) data input goals
        exact ⟨t, output.symm.trans outputIs, tData,
          .inr ⟨.hole, s, t, rfl, rfl, .inl ⟨e, eIn, equations.raw e eIn, .inl within⟩⟩⟩
      · obtain ⟨t, outputIs, initial, final, witnesses, matched, passed, rfl⟩ := triple_sound rules.collections
          rules.build rules.forAlls (equations.reverseShape e eIn) lowered (fun _ _ _ asked => ⟨depth, asked⟩)
          (derivesAt_unfolds depth) (fun _ _ asked => step_of_derivesAt rules depth asked) input goals
        exact ⟨_, output.symm.trans outputIs, (triple_data dataRows (equations.reverseShape e eIn) keeps data
          (fun step _ u v stepped => ⟨step, stepped⟩) matched passed).2.2.2,
          .inl (.inContext .hole (.inl (.reverse eIn (equations.raw e eIn) (matchPattern_iff_matchRel.mpr matched)
            passed)))⟩
      · obtain ⟨t, outputIs, tData, within⟩ := converse_sound rules.collections rules.build equations.converses
          rules.forAlls dataClauses (equations.reverseShape e eIn) lowered (fun _ _ _ asked => ⟨depth, asked⟩)
          (derivesAt_unfolds depth) (fun _ _ asked => step_of_derivesAt rules depth asked) data input goals
        exact ⟨t, output.symm.trans outputIs, tData,
          .inr ⟨.hole, s, t, rfl, rfl, .inl ⟨e, eIn, equations.raw e eIn, .inr within⟩⟩⟩
      · simp only [congruenceClauses, List.mem_cons, List.not_mem_nil, or_false] at inCongruence
        rcases inCongruence with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          have asked := goals _ List.mem_cons_self <;>
          simp only [applyClause, lambdaClause, multiLambdaClause, substBodyClause, substValueClause,
            collectionClause, headClause, tailClause, goalHolds, DemandTransformation.inst_unknown,
            RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm] at input output asked isEquation
        · obtain ⟨label, arguments, rfl, first, second⟩ := encode_apply_inv input
          rw [second] at asked
          obtain ⟨ys, listed, ysData, before, x, y, after, rfl, rfl, inner⟩ :=
            ih.2 arguments _ (by simpa [isData] using data) asked
          refine ⟨.apply label (before ++ y :: after), ?_, by simpa [isData] using ysData,
            eitherWayStep_fill (.apply label before .hole after) inner⟩
          rw [← output, first, listed]
          simp [encode]
        · obtain ⟨binder, body, rfl, first, second⟩ := encode_lambda_inv input
          rw [second] at asked
          simp only [isData, Bool.and_eq_true, Option.isNone_iff_eq_none] at data
          obtain ⟨rfl, data⟩ := data
          obtain ⟨body', bodyIs, bodyData, inner⟩ := ih.1 body _ data asked
          refine ⟨.lambda none body', ?_, by simpa [isData] using bodyData,
            eitherWayStep_fill (.lambda none .hole) inner⟩
          rw [← output, first, bodyIs]
          simp [encode]
        · obtain ⟨arity, binders, body, rfl, first, second, third⟩ := encode_multiLambda_inv input
          rw [third] at asked
          simp only [isData, Bool.and_eq_true, List.isEmpty_iff] at data
          obtain ⟨rfl, data⟩ := data
          obtain ⟨body', bodyIs, bodyData, inner⟩ := ih.1 body _ data asked
          refine ⟨.multiLambda arity [] body', ?_, by simpa [isData] using bodyData,
            eitherWayStep_fill (.multiLambda arity [] .hole) inner⟩
          rw [← output, first, second, bodyIs]
          simp [encode]
        · obtain ⟨body, value, rfl, first, second⟩ := encode_subst_inv input
          rw [first] at asked
          simp only [isData, Bool.and_eq_true] at data
          obtain ⟨body', bodyIs, bodyData, inner⟩ := ih.1 body _ data.1 asked
          refine ⟨.subst body' value, ?_, by simp [isData, bodyData, data.2],
            eitherWayStep_fill (.substBody .hole value) inner⟩
          rw [← output, second, bodyIs]
          simp [encode]
        · obtain ⟨body, value, rfl, first, second⟩ := encode_subst_inv input
          rw [second] at asked
          simp only [isData, Bool.and_eq_true] at data
          obtain ⟨value', valueIs, valueData, inner⟩ := ih.1 value _ data.2 asked
          refine ⟨.subst body value', ?_, by simp [isData, valueData, data.1],
            eitherWayStep_fill (.substReplacement body .hole) inner⟩
          rw [← output, first, valueIs]
          simp [encode]
        · obtain ⟨kind, elements, rest, rfl, first, second, third⟩ := encode_collection_inv input
          rw [second] at asked
          simp only [isData, Bool.and_eq_true] at data
          obtain ⟨ys, listed, ysData, before, x, y, after, rfl, rfl, inner⟩ := ih.2 elements _ data.2 asked
          refine ⟨.collection kind (before ++ y :: after) rest, ?_, by simp [isData, ysData, data.1],
            eitherWayStep_fill (.collection kind before .hole after rest) inner⟩
          rw [← output, first, listed, third]
          simp [encode]
        · exact absurd isEquation relation_ne_element_equation
        · exact absurd isEquation relation_ne_element_equation
      · simp only [lawStepClause, DemandTransformation.inst_unknown] at input output
        have asked := goals _ List.mem_cons_self
        simp only [goalHolds, DemandTransformation.inst_unknown, input] at asked
        obtain ⟨t, tIs, related⟩ :=
          CollectionLaws.law_sound (equations.laws notFree _ (premiseRelations_names relEnv language)) asked
        rcases related with forward | backward
        · exact ⟨t, output.symm.trans tIs, (derivedInstance_data forward).mp data,
            .inl (.inContext .hole (.inr forward))⟩
        · exact ⟨t, output.symm.trans tIs, (derivedInstance_data backward).mpr data,
            .inr ⟨.hole, s, t, rfl, rfl, .inr backward⟩⟩
    · intro xs w data derived
      obtain ⟨c, member, isElement, θ, input, output, goals⟩ := derived
      rcases equations.onlyThese c member (.inr isElement) with
        ⟨e, eIn, lowered | lowered | lowered | lowered⟩ | inCongruence | ⟨rfl, -⟩
      · exact absurd (isElement.symm.trans (tripleClause_relation lowered)) relation_ne_element_equation
      · exact absurd (isElement.symm.trans (converseClause_relation lowered)) relation_ne_element_equation
      · exact absurd (isElement.symm.trans (tripleClause_relation lowered)) relation_ne_element_equation
      · exact absurd (isElement.symm.trans (converseClause_relation lowered)) relation_ne_element_equation
      · simp only [congruenceClauses, List.mem_cons, List.not_mem_nil, or_false] at inCongruence
        rcases inCongruence with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          have asked := goals _ List.mem_cons_self <;>
          simp only [applyClause, lambdaClause, multiLambdaClause, substBodyClause, substValueClause,
            collectionClause, headClause, tailClause, goalHolds, DemandTransformation.inst_unknown,
            RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm] at input output asked isElement
        · exact absurd isElement.symm relation_ne_element_equation
        · exact absurd isElement.symm relation_ne_element_equation
        · exact absurd isElement.symm relation_ne_element_equation
        · exact absurd isElement.symm relation_ne_element_equation
        · exact absurd isElement.symm relation_ne_element_equation
        · exact absurd isElement.symm relation_ne_element_equation
        · obtain ⟨x, rest, rfl, first, second⟩ := encodeList_cons_inv input
          rw [first] at asked
          simp only [isDataList, Bool.and_eq_true] at data
          obtain ⟨y, yIs, yData, inner⟩ := ih.1 x _ data.1 asked
          refine ⟨y :: rest, ?_, by simp [isDataList, yData, data.2], [], x, y, rest, rfl, rfl, inner⟩
          rw [← output, yIs, second]
          rfl
        · obtain ⟨x, rest, rfl, first, second⟩ := encodeList_cons_inv input
          rw [second] at asked
          simp only [isDataList, Bool.and_eq_true] at data
          obtain ⟨ys, listed, ysData, before, y, z, after, rfl, rfl, inner⟩ := ih.2 rest _ data.2 asked
          refine ⟨x :: (before ++ z :: after), ?_, by simp [isDataList, ysData, data.1], x :: before, y, z, after,
            rfl, rfl, inner⟩
          rw [← output, first, listed]
          rfl
      · exact absurd isElement (by decide)

/-! ## One matched equation step of data is a derivation -/


/-- One equation step of an element is a derivation inside the list. -/
theorem elements_complete (equations : EquationClauses language program)
    (notFree : language.isEquationFree = false)
    {u v : Pattern} (derived : Derives (premiseRelations relEnv language) program equationRelation (encode u) (encode v)) :
    ∀ (before after : List Pattern), Derives (premiseRelations relEnv language) program elementRelation
      (encodeList (before ++ u :: after)) (encodeList (before ++ v :: after))
  | [], after => by
      have clause := derives_of_clause (equations.congruence notFree headClause (by simp [congruenceClauses]))
        (pick [encode u, encodeList after, encode v]) (fun g inside => by
          simp only [headClause, List.mem_cons, List.not_mem_nil, or_false] at inside
          subst inside
          exact derived)
      simpa [headClause, pick, encodeList] using clause
  | b :: before, after => by
      have clause := derives_of_clause (equations.congruence notFree tailClause (by simp [congruenceClauses]))
        (pick [encode b, encodeList (before ++ u :: after), encodeList (before ++ v :: after)]) (fun g inside => by
          simp only [tailClause, List.mem_cons, List.not_mem_nil, or_false] at inside
          subst inside
          exact elements_complete equations notFree derived before after)
      simpa [tailClause, pick, encodeList] using clause

/-- A presentation with an equation is not free of equations. -/
theorem notFree_of_equation {e : Equation} (member : e ∈ language.equations) : language.isEquationFree = false := by
  have nonempty : language.equations.isEmpty = false := by
    cases equationsIs : language.equations with
    | nil => rw [equationsIs] at member; cases member
    | cons _ _ => rfl
  simp [LanguageDef.isEquationFree, nonempty]

/-- A presentation with an instance of a law is not free of equations. -/
theorem notFree_of_derived {s t : Pattern} (derived : DerivedInstance language s t) :
    language.isEquationFree = false := by
  cases free : language.isEquationFree with
  | false => rfl
  | true =>
      simp only [LanguageDef.isEquationFree, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at free
      exact absurd derived (no_derivedInstance_of_no_derived_laws free.1.1.2 free.1.2 free.2 s t)

/-- **A presentation with an equation generator is not free of equations.** -/
theorem notFree_of_generator {redex contractum : Pattern}
    (generator : Generator relEnv language redex contractum) : language.isEquationFree = false := by
  rcases generator with authored | derived
  · cases authored with
    | forward member => exact notFree_of_equation member
    | reverse member => exact notFree_of_equation member
    | declared member => exact notFree_of_equation member
    | premised member => exact notFree_of_equation member
  · exact notFree_of_derived derived

/-- **An instance of a law is one equation step.** -/
theorem lawStep_complete (equations : EquationClauses language program)
    (notFree : language.isEquationFree = false) {x y : Expr}
    (derived : Derives (premiseRelations relEnv language) program lawRelation x y) :
    Derives (premiseRelations relEnv language) program equationRelation x y := by
  have clause := derives_of_clause (R := premiseRelations relEnv language) (equations.lawStep notFree) (pick [x, y])
    (fun g inside => by
      simp only [lawStepClause, List.mem_cons, List.not_mem_nil, or_false] at inside
      subst inside
      simpa [goalHolds, pick] using derived)
  simpa [lawStepClause, pick] using clause

/-- **At data, one equation generator either way, to data, is a derivation.** -/
theorem generator_complete (dataRows : DataRows relEnv language)
    (rules : RuleClauses language program) (equations : EquationClauses language program)
    {supply : List String} (dataClauses : DataClauses.DataProgram supply program)
    {redex contractum : Pattern} (data : isData redex = true) (targetData : isData contractum = true)
    (generator : Generator relEnv language redex contractum ∨
      BackGenerator relEnv language supply redex contractum) :
    Derives (premiseRelations relEnv language) program equationRelation (encode redex) (encode contractum) := by
  have keeps : ∀ u v, isData u = true → Step relEnv language u v → isData v = true :=
    fun _ _ uData stepped => StepPremises.step_data dataRows rules.shape uData stepped
  have steps : ∀ u v, isData u = true → Step relEnv language u v →
      Derives (premiseRelations relEnv language) program stepRelation (encode u) (encode v) :=
    fun _ v uData stepped => (derives_step_iff dataRows rules uData).mpr ⟨v, rfl, stepped⟩
  rcases generator with (authored | derived) | (⟨e, member, -, forward | reverse⟩ | derived)
  · cases authored with
    | @forward e _ _ _ _ member _ matched passed =>
        obtain ⟨c, cIn, lowered⟩ := equations.forwardClause e member
        obtain ⟨θ, input, output, goals⟩ := triple_complete rules.collections rules.build rules.forAlls
          dataRows (equations.forwardShape e member) (equations.forwardQuantified e member) lowered keeps steps data
          (fun step _ u v stepped => ⟨step, stepped⟩) (matchPattern_sound matched) passed
        have clause := derives_of_clause cIn θ goals
        rw [tripleClause_relation lowered, input, output] at clause
        exact clause
    | @reverse e _ _ _ _ member _ matched passed =>
        obtain ⟨c, cIn, lowered⟩ := equations.reverseClause e member
        obtain ⟨θ, input, output, goals⟩ := triple_complete rules.collections rules.build rules.forAlls
          dataRows (equations.reverseShape e member) (equations.reverseQuantified e member) lowered keeps steps data
          (fun step _ u v stepped => ⟨step, stepped⟩) (matchPattern_sound matched) passed
        have clause := derives_of_clause cIn θ goals
        rw [tripleClause_relation lowered, input, output] at clause
        exact clause
    | declared member notRaw _ => exact absurd (equations.raw _ member) (by simp [notRaw])
    | premised member notRaw _ _ => exact absurd (equations.raw _ member) (by simp [notRaw])
  · have notFree := notFree_of_derived derived
    exact lawStep_complete equations notFree
      (CollectionLaws.law_forward (equations.laws notFree _ (premiseRelations_names relEnv language)) derived)
  · obtain ⟨initial, final, witnesses, matched, passed, rfl, supplied, substituted⟩ := forward
    obtain ⟨c, cIn, lowered⟩ := equations.forwardConverse e member
    obtain ⟨θ, input, output, goals⟩ := converse_complete rules.collections rules.build equations.converses
      rules.forAlls dataClauses dataRows (equations.forwardShape e member) (equations.forwardQuantified e member)
      lowered keeps steps targetData (fun step _ u v stepped => ⟨step, stepped⟩) matched passed supplied
      substituted
    have clause := derives_of_clause cIn θ goals
    rw [converseClause_relation lowered, input, output] at clause
    exact clause
  · obtain ⟨initial, final, witnesses, matched, passed, rfl, supplied, substituted⟩ := reverse
    obtain ⟨c, cIn, lowered⟩ := equations.reverseConverse e member
    obtain ⟨θ, input, output, goals⟩ := converse_complete rules.collections rules.build equations.converses
      rules.forAlls dataClauses dataRows (equations.reverseShape e member) (equations.reverseQuantified e member)
      lowered keeps steps targetData (fun step _ u v stepped => ⟨step, stepped⟩) matched passed supplied
      substituted
    have clause := derives_of_clause cIn θ goals
    rw [converseClause_relation lowered, input, output] at clause
    exact clause
  · have notFree := notFree_of_derived derived
    exact lawStep_complete equations notFree
      (CollectionLaws.law_backward (equations.laws notFree _ (premiseRelations_names relEnv language)) derived)

theorem fill_data_inner : ∀ (context : OneHoleContext) {p : Pattern}, isData (context.fill p) = true → isData p = true
  | .hole, _, data => data
  | .apply _ before inner _, _, data => by
      simp only [OneHoleContext.fill, isData, isDataList_iff, List.mem_append, List.mem_cons] at data
      exact fill_data_inner inner (data _ (.inr (.inl rfl)))
  | .lambda _ inner, _, data => by
      simp only [OneHoleContext.fill, isData, Bool.and_eq_true] at data
      exact fill_data_inner inner data.2
  | .multiLambda _ _ inner, _, data => by
      simp only [OneHoleContext.fill, isData, Bool.and_eq_true] at data
      exact fill_data_inner inner data.2
  | .substBody inner _, _, data => by
      simp only [OneHoleContext.fill, isData, Bool.and_eq_true] at data
      exact fill_data_inner inner data.1
  | .substReplacement _ inner, _, data => by
      simp only [OneHoleContext.fill, isData, Bool.and_eq_true] at data
      exact fill_data_inner inner data.2
  | .collection _ before inner _ _, _, data => by
      simp only [OneHoleContext.fill, isData, Bool.and_eq_true, isDataList_iff, List.mem_append,
        List.mem_cons] at data
      exact fill_data_inner inner (data.2 _ (.inr (.inl rfl)))

theorem fill_data_replace : ∀ (context : OneHoleContext) {p q : Pattern}, isData (context.fill p) = true →
    isData q = true → isData (context.fill q) = true
  | .hole, _, _, _, data => data
  | .apply _ before inner after, _, _, data, other => by
      simp only [OneHoleContext.fill, isData, isDataList_iff, List.mem_append, List.mem_cons] at data ⊢
      rintro t (inBefore | rfl | inAfter)
      · exact data t (.inl inBefore)
      · exact fill_data_replace inner (data _ (.inr (.inl rfl))) other
      · exact data t (.inr (.inr inAfter))
  | .lambda _ inner, _, _, data, other => by
      simp only [OneHoleContext.fill, isData, Bool.and_eq_true] at data ⊢
      exact ⟨data.1, fill_data_replace inner data.2 other⟩
  | .multiLambda _ _ inner, _, _, data, other => by
      simp only [OneHoleContext.fill, isData, Bool.and_eq_true] at data ⊢
      exact ⟨data.1, fill_data_replace inner data.2 other⟩
  | .substBody inner _, _, _, data, other => by
      simp only [OneHoleContext.fill, isData, Bool.and_eq_true] at data ⊢
      exact ⟨fill_data_replace inner data.1 other, data.2⟩
  | .substReplacement _ inner, _, _, data, other => by
      simp only [OneHoleContext.fill, isData, Bool.and_eq_true] at data ⊢
      exact ⟨data.1, fill_data_replace inner data.2 other⟩
  | .collection _ before inner after _, _, _, data, other => by
      simp only [OneHoleContext.fill, isData, Bool.and_eq_true, isDataList_iff, List.mem_append,
        List.mem_cons] at data ⊢
      refine ⟨data.1, ?_⟩
      rintro t (inBefore | rfl | inAfter)
      · exact data.2 t (.inl inBefore)
      · exact fill_data_replace inner (data.2 _ (.inr (.inl rfl))) other
      · exact data.2 t (.inr (.inr inAfter))

/-- **At data, one equation generator either way in a context, to data, is a derivation.** -/
theorem complete (dataRows : DataRows relEnv language)
    (rules : RuleClauses language program) (equations : EquationClauses language program)
    {supply : List String} (dataClauses : DataClauses.DataProgram supply program)
    {redex contractum : Pattern}
    (generator : Generator relEnv language redex contractum ∨
      BackGenerator relEnv language supply redex contractum) :
    ∀ (context : OneHoleContext), isData (context.fill redex) = true → isData (context.fill contractum) = true →
      Derives (premiseRelations relEnv language) program equationRelation (encode (context.fill redex))
        (encode (context.fill contractum))
  | .hole, data, targetData => generator_complete dataRows rules equations dataClauses data targetData generator
  | .apply label before inner after, data, targetData => by
      have notFree := generator.elim notFree_of_generator
        fun back => notFree_of_generator (backGenerator_generator back)
      have listed := elements_complete equations notFree
        (complete dataRows rules equations dataClauses generator inner
          (fill_data_inner (.apply label before .hole after) (p := inner.fill redex) data)
          (fill_data_inner (.apply label before .hole after) (p := inner.fill contractum) targetData))
        before after
      have clause := derives_of_clause (equations.congruence notFree applyClause (by simp [congruenceClauses]))
        (pick [.sym (labelCode label), encodeList (before ++ inner.fill redex :: after),
          encodeList (before ++ inner.fill contractum :: after)]) (fun g inside => by
          simp only [applyClause, List.mem_cons, List.not_mem_nil, or_false] at inside
          subst inside
          exact listed)
      simpa [applyClause, pick, encode, OneHoleContext.fill] using clause
  | .lambda binder inner, data, targetData => by
      have notFree := generator.elim notFree_of_generator
        fun back => notFree_of_generator (backGenerator_generator back)
      have innerDerived := complete dataRows rules equations dataClauses generator inner
        (fill_data_inner (.lambda binder .hole) (p := inner.fill redex) data)
        (fill_data_inner (.lambda binder .hole) (p := inner.fill contractum) targetData)
      have clause := derives_of_clause (equations.congruence notFree lambdaClause (by simp [congruenceClauses]))
        (pick [optionRow binder, encode (inner.fill redex), encode (inner.fill contractum)]) (fun g inside => by
          simp only [lambdaClause, List.mem_cons, List.not_mem_nil, or_false] at inside
          subst inside
          exact innerDerived)
      simpa [lambdaClause, pick, encode, OneHoleContext.fill] using clause
  | .multiLambda arity binders inner, data, targetData => by
      have notFree := generator.elim notFree_of_generator
        fun back => notFree_of_generator (backGenerator_generator back)
      have innerDerived := complete dataRows rules equations dataClauses generator inner
        (fill_data_inner (.multiLambda arity binders .hole) (p := inner.fill redex) data)
        (fill_data_inner (.multiLambda arity binders .hole) (p := inner.fill contractum) targetData)
      have clause := derives_of_clause (equations.congruence notFree multiLambdaClause
        (by simp [congruenceClauses]))
        (pick [numeral arity, namesRow binders, encode (inner.fill redex), encode (inner.fill contractum)])
        (fun g inside => by
          simp only [multiLambdaClause, List.mem_cons, List.not_mem_nil, or_false] at inside
          subst inside
          exact innerDerived)
      simpa [multiLambdaClause, pick, encode, OneHoleContext.fill] using clause
  | .substBody inner value, data, targetData => by
      have notFree := generator.elim notFree_of_generator
        fun back => notFree_of_generator (backGenerator_generator back)
      have innerDerived := complete dataRows rules equations dataClauses generator inner
        (fill_data_inner (.substBody .hole value) (p := inner.fill redex) data)
        (fill_data_inner (.substBody .hole value) (p := inner.fill contractum) targetData)
      have clause := derives_of_clause (equations.congruence notFree substBodyClause (by simp [congruenceClauses]))
        (pick [encode (inner.fill redex), encode value, encode (inner.fill contractum)]) (fun g inside => by
          simp only [substBodyClause, List.mem_cons, List.not_mem_nil, or_false] at inside
          subst inside
          exact innerDerived)
      simpa [substBodyClause, pick, encode, OneHoleContext.fill] using clause
  | .substReplacement body inner, data, targetData => by
      have notFree := generator.elim notFree_of_generator
        fun back => notFree_of_generator (backGenerator_generator back)
      have innerDerived := complete dataRows rules equations dataClauses generator inner
        (fill_data_inner (.substReplacement body .hole) (p := inner.fill redex) data)
        (fill_data_inner (.substReplacement body .hole) (p := inner.fill contractum) targetData)
      have clause := derives_of_clause (equations.congruence notFree substValueClause (by simp [congruenceClauses]))
        (pick [encode body, encode (inner.fill redex), encode (inner.fill contractum)]) (fun g inside => by
          simp only [substValueClause, List.mem_cons, List.not_mem_nil, or_false] at inside
          subst inside
          exact innerDerived)
      simpa [substValueClause, pick, encode, OneHoleContext.fill] using clause
  | .collection kind before inner after rest, data, targetData => by
      have notFree := generator.elim notFree_of_generator
        fun back => notFree_of_generator (backGenerator_generator back)
      have listed := elements_complete equations notFree
        (complete dataRows rules equations dataClauses generator inner
          (fill_data_inner (.collection kind before .hole after rest) (p := inner.fill redex) data)
          (fill_data_inner (.collection kind before .hole after rest) (p := inner.fill contractum) targetData))
        before after
      have clause := derives_of_clause (equations.congruence notFree collectionClause (by simp [congruenceClauses]))
        (pick [.sym (collectionCode kind), encodeList (before ++ inner.fill redex :: after), optionRow rest,
          encodeList (before ++ inner.fill contractum :: after)]) (fun g inside => by
          simp only [collectionClause, List.mem_cons, List.not_mem_nil, or_false] at inside
          subst inside
          exact listed)
      simpa [collectionClause, pick, encode, OneHoleContext.fill] using clause

/-- **At data, the least model of the equation clauses is one equation step either way, to data.** -/
theorem derives_equation_iff (dataRows : DataRows relEnv language)
    (rules : RuleClauses language program) (equations : EquationClauses language program)
    {supply : List String} (dataClauses : DataClauses.DataProgram supply program)
    {s : Pattern} (data : isData s = true) {w : Expr} :
    Derives (premiseRelations relEnv language) program equationRelation (encode s) w ↔
      ∃ t, w = encode t ∧ isData t = true ∧ EitherWayStep relEnv language supply s t := by
  constructor
  · rintro ⟨depth, derived⟩
    exact (sound dataRows rules equations dataClauses depth).1 s w data derived
  · rintro ⟨t, rfl, tData, step | step⟩
    · cases step with
      | inContext context generator =>
          exact complete dataRows rules equations dataClauses (.inl generator) context data tData
    · obtain ⟨context, origin, target, rfl, rfl, back⟩ := step
      exact complete dataRows rules equations dataClauses (.inr back) context data tData

/-! ## Equation steps either way and the source's equation steps -/

variable (relEnv language) in
/-- One reference equation step from data. -/
def SourceDataStep (u v : Pattern) : Prop :=
  isData u = true ∧ EquationStep relEnv language u v

variable (relEnv language) in
/-- One equation step either way over a supply, from data to data. -/
def DataStep (supply : List String) (u v : Pattern) : Prop :=
  isData u = true ∧ isData v = true ∧ EitherWayStep relEnv language supply u v

section DataSteps

variable (dataRows : DataRows relEnv language)
  (rules : RuleClauses language program) (equations : EquationClauses language program)

include dataRows rules equations

/-- **A source equation generator from data gives data.** -/
theorem generator_data {redex contractum : Pattern} (data : isData redex = true)
    (generator : Generator relEnv language redex contractum) : isData contractum = true := by
  have keeps : ∀ u v, isData u = true → Step relEnv language u v → isData v = true :=
    fun _ _ uData stepped => StepPremises.step_data dataRows rules.shape uData stepped
  rcases generator with authored | derived
  · cases authored with
    | forward member raw matched passed =>
        exact (triple_data dataRows (equations.forwardShape _ member) keeps data
          (fun step _ u v stepped => ⟨step, stepped⟩) (matchPattern_sound matched) passed).2.2.2
    | reverse member raw matched passed =>
        exact (triple_data dataRows (equations.reverseShape _ member) keeps data
          (fun step _ u v stepped => ⟨step, stepped⟩) (matchPattern_sound matched) passed).2.2.2
    | declared member notRaw _ => exact absurd (equations.raw _ member) (by simp [notRaw])
    | premised member notRaw _ _ => exact absurd (equations.raw _ member) (by simp [notRaw])
  · exact (derivedInstance_data derived).mp data

theorem sourceStep_data {u v : Pattern} (step : SourceDataStep relEnv language u v) : isData v = true := by
  obtain ⟨data, step⟩ := step
  cases step with
  | inContext context generator =>
      exact fill_data_replace context data
        (generator_data dataRows rules equations (fill_data_inner context data) generator)

theorem source_eqvGen_data {a b : Pattern} (related : Relation.EqvGen (SourceDataStep relEnv language) a b) :
    isData a = true ↔ isData b = true := by
  induction related with
  | rel _ _ step => exact ⟨fun _ => sourceStep_data dataRows rules equations step, fun _ => step.1⟩
  | refl => exact Iff.rfl
  | symm _ _ _ same => exact same.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- Source equivalence through data is a congruence on data. -/
theorem source_eqvGen_fill (context : OneHoleContext) {a b : Pattern}
    (related : Relation.EqvGen (SourceDataStep relEnv language) a b) :
    isData (context.fill a) = true →
      Relation.EqvGen (SourceDataStep relEnv language) (context.fill a) (context.fill b) := by
  induction related with
  | rel x y step =>
      intro data
      exact .rel _ _ ⟨data, equationStep_fill context step.2⟩
  | refl => exact fun _ => .refl _
  | symm x y inner ih =>
      intro data
      have xData := (source_eqvGen_data dataRows rules equations inner).mpr (fill_data_inner context data)
      exact .symm _ _ (ih (fill_data_replace context data xData))
  | trans x y z first _ ih₁ ih₂ =>
      intro data
      have yData := (source_eqvGen_data dataRows rules equations first).mp (fill_data_inner context data)
      exact .trans _ _ _ (ih₁ data) (ih₂ (fill_data_replace context data yData))

/-- **Equation steps either way from data, over any supply, generate the source's equivalence through data.** -/
theorem eqvGen_dataStep_iff {supply : List String} {a b : Pattern} :
    Relation.EqvGen (DataStep relEnv language supply) a b ↔ Relation.EqvGen (SourceDataStep relEnv language) a b := by
  constructor
  · intro related
    induction related with
    | rel u v step =>
        obtain ⟨data, targetData, forward | backward⟩ := step
        · exact .rel _ _ ⟨data, forward⟩
        · exact .symm _ _ (.rel _ _ ⟨targetData, backStep_step backward⟩)
    | refl => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
  · intro related
    induction related with
    | rel u v step => exact .rel _ _ ⟨step.1, sourceStep_data dataRows rules equations step, .inl step.2⟩
    | refl => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

end DataSteps

theorem dataStep_mono {supply wider : List String} (more : ∀ label ∈ supply, label ∈ wider) {u v : Pattern}
    (step : DataStep relEnv language supply u v) : DataStep relEnv language wider u v :=
  ⟨step.1, step.2.1, eitherWayStep_mono more step.2.2⟩

theorem dataPath_mono {supply wider : List String} (more : ∀ label ∈ supply, label ∈ wider) {a b : Pattern}
    (path : Relation.ReflTransGen (DataStep relEnv language supply) a b) :
    Relation.ReflTransGen (DataStep relEnv language wider) a b := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (dataStep_mono more step)

/-- **Every generator of a raw equation or a law can be taken back, over the labels of its chosen values.** -/
theorem generator_back (equations : EquationClauses language program) {redex contractum : Pattern}
    (generator : Generator relEnv language redex contractum) :
    ∃ supply, BackGenerator relEnv language supply contractum redex := by
  rcases generator with authored | derived
  · cases authored with
    | @forward e _ initial final witnesses member raw matched passed =>
        exact ⟨(freeNames e.left e.right).flatMap (fun name => DataClauses.labelsOf (lookupOrFvar initial name)) ++
            (Instantiation.substValues (captureSitesOf e.left e.premises) final 0 e.right).flatMap
              DataClauses.labelsOf,
          .inl ⟨e, member, raw, .inl ⟨initial, final, witnesses, matchPattern_sound matched, passed, rfl,
            fun name free label inside => List.mem_append_left _ (List.mem_flatMap.mpr ⟨name, free, inside⟩),
            fun v inside label member => List.mem_append_right _ (List.mem_flatMap.mpr ⟨v, inside, member⟩)⟩⟩⟩
    | @reverse e _ initial final witnesses member raw matched passed =>
        exact ⟨(freeNames e.right e.left).flatMap (fun name => DataClauses.labelsOf (lookupOrFvar initial name)) ++
            (Instantiation.substValues (captureSitesOf e.right e.premises) final 0 e.left).flatMap
              DataClauses.labelsOf,
          .inl ⟨e, member, raw, .inr ⟨initial, final, witnesses, matchPattern_sound matched, passed, rfl,
            fun name free label inside => List.mem_append_left _ (List.mem_flatMap.mpr ⟨name, free, inside⟩),
            fun v inside label member => List.mem_append_right _ (List.mem_flatMap.mpr ⟨v, inside, member⟩)⟩⟩⟩
    | declared member notRaw _ => exact absurd (equations.raw _ member) (by simp [notRaw])
    | premised member notRaw _ _ => exact absurd (equations.raw _ member) (by simp [notRaw])
  · exact ⟨[], .inr derived⟩

/-- **An equation step either way can be taken back, over some supply.** -/
theorem dataStep_back (equations : EquationClauses language program) {supply : List String} {u v : Pattern}
    (step : DataStep relEnv language supply u v) : ∃ supply', DataStep relEnv language supply' v u := by
  obtain ⟨data, targetData, forward | backward⟩ := step
  · cases forward with
    | inContext context generator =>
        obtain ⟨supply', back⟩ := generator_back equations generator
        exact ⟨supply', targetData, data, .inr ⟨context, _, _, rfl, rfl, back⟩⟩
  · exact ⟨[], targetData, data, .inl (backStep_step backward)⟩

/-- A path of equation steps either way, taken back over some supply. -/
theorem dataPath_reverse (equations : EquationClauses language program) {supply : List String} {a b : Pattern}
    (path : Relation.ReflTransGen (DataStep relEnv language supply) a b) :
    ∃ supply', Relation.ReflTransGen (DataStep relEnv language supply') b a := by
  induction path with
  | refl => exact ⟨[], .refl⟩
  | tail _ step ih =>
      obtain ⟨earlier, back⟩ := ih
      obtain ⟨later, stepBack⟩ := dataStep_back equations step
      exact ⟨later ++ earlier, Relation.ReflTransGen.head
        (dataStep_mono (fun _ inside => List.mem_append_left _ inside) stepBack)
        (dataPath_mono (fun _ inside => List.mem_append_right _ inside) back)⟩

/-- **The source's equivalence through data is a path of equation steps either way, over some supply.** -/
theorem eqvGen_paths (dataRows : DataRows relEnv language) (rules : RuleClauses language program)
    (equations : EquationClauses language program) {a b : Pattern}
    (related : Relation.EqvGen (SourceDataStep relEnv language) a b) :
    ∃ supply, Relation.ReflTransGen (DataStep relEnv language supply) a b := by
  induction related with
  | rel x y step => exact ⟨[], .single ⟨step.1, sourceStep_data dataRows rules equations step, .inl step.2⟩⟩
  | refl => exact ⟨[], .refl⟩
  | symm x y _ ih =>
      obtain ⟨supply, path⟩ := ih
      exact dataPath_reverse equations path
  | trans x y z _ _ ih₁ ih₂ =>
      obtain ⟨first, firstPath⟩ := ih₁
      obtain ⟨second, secondPath⟩ := ih₂
      exact ⟨first ++ second, (dataPath_mono (fun _ inside => List.mem_append_left _ inside) firstPath).trans
        (dataPath_mono (fun _ inside => List.mem_append_right _ inside) secondPath)⟩


variable (relEnv language) in
/-- **The reference step relation modulo equations, on data**: one reference step between representatives that are
equivalent through reference equation steps from data. -/
def StepModuloOnData (s t : Pattern) : Prop :=
  ∃ redex contractum, Relation.EqvGen (SourceDataStep relEnv language) s redex ∧
    Step relEnv language redex contractum ∧ Relation.EqvGen (SourceDataStep relEnv language) contractum t

/-- **Steps modulo equations on data are reference steps modulo equations.** -/
theorem stepModulo_of_onData {s t : Pattern} (stepped : StepModuloOnData relEnv language s t) :
    Mettapedia.OSLF.MeTTaIL.ReferenceStep.StepModulo relEnv language s t := by
  obtain ⟨redex, contractum, before, step, after⟩ := stepped
  exact ⟨redex, contractum, Relation.EqvGen.mono (fun _ _ one => one.2) _ _ before, step,
    Relation.EqvGen.mono (fun _ _ one => one.2) _ _ after⟩

/-- **Without equations, steps modulo equations on data are reference steps.** -/
theorem stepModuloOnData_iff_step (noEquations : language.equations = [])
    (noLaws : ∀ s t, ¬ DerivedInstance language s t) {s t : Pattern} :
    StepModuloOnData relEnv language s t ↔ Step relEnv language s t := by
  have none : ∀ u v, ¬ SourceDataStep relEnv language u v := by
    rintro u v ⟨-, step⟩
    cases step with
    | inContext context generator =>
        rcases generator with authored | derived
        · cases authored with
          | forward member => rw [noEquations] at member; cases member
          | reverse member => rw [noEquations] at member; cases member
          | declared member => rw [noEquations] at member; cases member
          | premised member => rw [noEquations] at member; cases member
        · exact noLaws _ _ derived
  have equal : ∀ {a b}, Relation.EqvGen (SourceDataStep relEnv language) a b → a = b := by
    intro a b related
    induction related with
    | rel _ _ step => exact absurd step (none _ _)
    | refl => rfl
    | symm _ _ _ same => exact same.symm
    | trans _ _ _ _ _ first second => exact first.trans second
  constructor
  · rintro ⟨redex, contractum, before, step, after⟩
    rw [equal before, ← equal after]
    exact step
  · exact fun step => ⟨s, t, Relation.EqvGen.refl _, step, Relation.EqvGen.refl _⟩

/-! ## Runs modulo equations -/

theorem stepRelation_mem_moves : stepRelation ∈ moves := List.mem_cons_self

theorem equationRelation_mem_moves : equationRelation ∈ moves := List.mem_cons_of_mem _ List.mem_cons_self

variable (relEnv language) in
/-- **One move of a run over a supply**: a reference step from data, or an equation step either way over the supply
between data. -/
def MoveWithin (supply : List String) (u v : Pattern) : Prop :=
  (isData u = true ∧ Step relEnv language u v) ∨ DataStep relEnv language supply u v

variable (relEnv language) in
/-- **Reachability modulo equations, on data**: steps modulo equations, then a term equivalent to the last through
data. -/
def ReachModulo (s t : Pattern) : Prop :=
  ∃ u, Relation.ReflTransGen (StepModuloOnData relEnv language) s u ∧
    Relation.EqvGen (SourceDataStep relEnv language) u t

theorem moveWithin_mono {supply wider : List String} (more : ∀ label ∈ supply, label ∈ wider) {u v : Pattern}
    (move : MoveWithin relEnv language supply u v) : MoveWithin relEnv language wider u v :=
  move.imp id (dataStep_mono more)

theorem movesWithin_mono {supply wider : List String} (more : ∀ label ∈ supply, label ∈ wider) {a b : Pattern}
    (path : Relation.ReflTransGen (MoveWithin relEnv language supply) a b) :
    Relation.ReflTransGen (MoveWithin relEnv language wider) a b := by
  induction path with
  | refl => exact .refl
  | tail _ move ih => exact ih.tail (moveWithin_mono more move)

/-- Equation steps either way over a supply are moves over it. -/
theorem dataPath_moves {supply : List String} {a b : Pattern}
    (path : Relation.ReflTransGen (DataStep relEnv language supply) a b) :
    Relation.ReflTransGen (MoveWithin relEnv language supply) a b := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (.inr step)

section Runs

variable (dataRows : DataRows relEnv language)
  (rules : RuleClauses language program) (equations : EquationClauses language program)

include dataRows rules equations

/-- **Moves over any supply reach only what the source reaches modulo equations.** -/
theorem moves_sound {supply : List String} {s t : Pattern}
    (path : Relation.ReflTransGen (MoveWithin relEnv language supply) s t) : ReachModulo relEnv language s t := by
  induction path with
  | refl => exact ⟨s, .refl, .refl _⟩
  | tail before move ih =>
      rename_i x y
      obtain ⟨u, chain, equivalent⟩ := ih
      rcases move with ⟨-, step⟩ | dataStep
      · exact ⟨y, chain.tail ⟨x, y, equivalent, step, .refl _⟩, .refl _⟩
      · exact ⟨u, chain, equivalent.trans _ _ _ ((eqvGen_dataStep_iff dataRows rules equations).mp
          (.rel _ _ dataStep))⟩

/-- **What the source reaches modulo equations from data, moves over some supply reach.** -/
theorem moves_complete {s t : Pattern} (data : isData s = true) (reach : ReachModulo relEnv language s t) :
    ∃ supply, Relation.ReflTransGen (MoveWithin relEnv language supply) s t := by
  obtain ⟨u, chain, equivalent⟩ := reach
  have along : ∀ {v : Pattern}, Relation.ReflTransGen (StepModuloOnData relEnv language) s v →
      isData v = true ∧ ∃ supply, Relation.ReflTransGen (MoveWithin relEnv language supply) s v := by
    intro v path
    induction path with
    | refl => exact ⟨data, [], .refl⟩
    | tail _ stepped ih =>
        rename_i x y
        obtain ⟨xData, earlier, earlierPath⟩ := ih
        obtain ⟨redex, contractum, toRedex, step, fromContractum⟩ := stepped
        have redexData := (source_eqvGen_data dataRows rules equations toRedex).mp xData
        have contractumData := StepPremises.step_data dataRows rules.shape redexData step
        obtain ⟨first, firstPath⟩ := eqvGen_paths dataRows rules equations toRedex
        obtain ⟨second, secondPath⟩ := eqvGen_paths dataRows rules equations fromContractum
        refine ⟨(source_eqvGen_data dataRows rules equations fromContractum).mp contractumData,
          earlier ++ (first ++ second), ?_⟩
        have toEarlier : ∀ label ∈ earlier, label ∈ earlier ++ (first ++ second) :=
          fun _ inside => List.mem_append_left _ inside
        have toFirst : ∀ label ∈ first, label ∈ earlier ++ (first ++ second) :=
          fun _ inside => List.mem_append_right _ (List.mem_append_left _ inside)
        have toSecond : ∀ label ∈ second, label ∈ earlier ++ (first ++ second) :=
          fun _ inside => List.mem_append_right _ (List.mem_append_right _ inside)
        exact ((movesWithin_mono toEarlier earlierPath).trans
          ((movesWithin_mono toFirst (dataPath_moves firstPath)).tail (.inl ⟨redexData, step⟩))).trans
          (movesWithin_mono toSecond (dataPath_moves secondPath))
  obtain ⟨-, earlier, earlierPath⟩ := along chain
  obtain ⟨last, lastPath⟩ := eqvGen_paths dataRows rules equations equivalent
  exact ⟨earlier ++ last, (movesWithin_mono (fun _ inside => List.mem_append_left _ inside) earlierPath).trans
    (movesWithin_mono (fun _ inside => List.mem_append_right _ inside) (dataPath_moves lastPath))⟩

/-- **Terms of data and their rows, over a supply**: a move of the source is one derivation of a relation of the run,
and one derivation of a relation of the run from a term's row is a move. -/
def rowCorrespondence {supply : List String} (dataClauses : DataClauses.DataProgram supply program) :
    OperationalCorrespondence (equalityGSLT Pattern (MoveWithin relEnv language supply))
      (equalityGSLT Expr (DemandTransformation.Moves (premiseRelations relEnv language) program moves)) where
  related p x := isData p = true ∧ x = encode p
  readStep := by
    rintro p x y ⟨data, rfl⟩ ⟨relation, member, derived⟩
    right
    simp only [moves, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · obtain ⟨q, rfl, step⟩ := (derives_step_iff dataRows rules data).mp derived
      exact ⟨q, .inl ⟨data, step⟩, StepPremises.step_data dataRows rules.shape data step, rfl⟩
    · obtain ⟨q, rfl, qData, step⟩ := (derives_equation_iff dataRows rules equations dataClauses data).mp derived
      exact ⟨q, .inr ⟨data, qData, step⟩, qData, rfl⟩
  forward := by
    rintro p q x ⟨data, rfl⟩ move
    rcases move with ⟨-, step⟩ | ⟨-, qData, step⟩
    · refine ⟨encode q, (executionPath_nonempty_iff_multiStep _ _ _).mpr (.step ⟨stepRelation,
        stepRelation_mem_moves, (derives_step_iff dataRows rules data).mpr ⟨q, rfl, step⟩⟩ (.refl _)),
        StepPremises.step_data dataRows rules.shape data step, rfl⟩
    · exact ⟨encode q, (executionPath_nonempty_iff_multiStep _ _ _).mpr (.step ⟨equationRelation,
        equationRelation_mem_moves, (derives_equation_iff dataRows rules equations dataClauses data).mpr
          ⟨q, rfl, qData, step⟩⟩ (.refl _)), qData, rfl⟩

end Runs


/-! ## The compiler -/

theorem stepRelation_ne_equation : stepRelation ≠ equationRelation := by decide

theorem stepRelation_ne_element : stepRelation ≠ elementRelation := by decide

theorem congruence_relation {c : Clause} (inside : c ∈ congruenceClauses) :
    c.relation = equationRelation ∨ c.relation = elementRelation := by
  simp only [congruenceClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [applyClause, lambdaClause,
    multiLambdaClause, substBodyClause, substValueClause, collectionClause, headClause, tailClause]

theorem collectionClauses_relation {c : Clause} (inside : c ∈ collectionClauses) :
    (c ∈ pickClauses ∧ c.relation = pickRelation) ∨ (c ∈ wrapClauses ∧ c.relation = wrapRelation) ∨
      (c ∈ insertClauses ∧ c.relation = insertRelation) ∨ (c ∈ unwrapClauses ∧ c.relation = unwrapRelation) := by
  simp only [collectionClauses, List.mem_append] at inside
  rcases inside with ((inPick | inWrap) | inInsert) | inUnwrap
  · refine .inl ⟨inPick, ?_⟩
    simp only [pickClauses, List.mem_cons, List.not_mem_nil, or_false] at inPick
    rcases inPick with rfl | rfl <;> rfl
  · refine .inr (.inl ⟨inWrap, ?_⟩)
    simp only [wrapClauses, List.mem_cons, List.not_mem_nil, or_false] at inWrap
    rcases inWrap with rfl | rfl <;> rfl
  · refine .inr (.inr (.inl ⟨inInsert, ?_⟩))
    simp only [insertClauses, List.mem_cons, List.not_mem_nil, or_false] at inInsert
    rcases inInsert with rfl | rfl <;> rfl
  · refine .inr (.inr (.inr ⟨inUnwrap, ?_⟩))
    simp only [unwrapClauses, List.mem_cons, List.not_mem_nil, or_false] at inUnwrap
    rcases inUnwrap with rfl | rfl <;> rfl

theorem collection_relation_ne {c : Clause} (inside : c ∈ collectionClauses) :
    c.relation ≠ stepRelation ∧ c.relation ≠ equationRelation ∧ c.relation ≠ elementRelation := by
  rcases collectionClauses_relation inside with ⟨-, same⟩ | ⟨-, same⟩ | ⟨-, same⟩ | ⟨-, same⟩ <;>
    rw [same] <;> decide

theorem collectionClauses_moded : ∀ c ∈ collectionClauses, DemandTransformation.Moded c := by
  intro c inside
  simp only [collectionClauses, pickClauses, wrapClauses, insertClauses, unwrapClauses, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with (((rfl | rfl) | (rfl | rfl)) | (rfl | rfl)) | (rfl | rfl) <;>
    exact DemandTransformation.moded_of_check (by decide)

/-- **A program with the collection clauses, whose other clauses have other relations, has exactly them for its
collection relations.** -/
theorem collectionProgram_of {program : List Clause} (included : ∀ c ∈ collectionClauses, c ∈ program)
    (relations : ∀ c ∈ program, c ∈ collectionClauses ∨ c.relation < 3 ∨ 6 < c.relation) :
    CollectionProgram program := by
  have sub : ∀ {cs : List Clause}, (∀ c ∈ cs, c ∈ collectionClauses) → ∀ c ∈ cs, c ∈ program :=
    fun within c inside => included c (within c inside)
  have only : ∀ {cs : List Clause} {r : ℕ}, (∀ c ∈ collectionClauses, c.relation = r → c ∈ cs) →
      3 ≤ r → r ≤ 6 → ∀ c ∈ program, c.relation = r → c ∈ cs := by
    intro cs r within low high c inside isR
    rcases relations c inside with inCollection | below | above
    · exact within c inCollection isR
    · omega
    · omega
  refine ⟨sub fun c inside => by simp [collectionClauses, inside], sub fun c inside => by simp [collectionClauses, inside],
    sub fun c inside => by simp [collectionClauses, inside], sub fun c inside => by simp [collectionClauses, inside],
    only (fun c inside isR => ?_) (by decide) (by decide),
    only (fun c inside isR => ?_) (by decide) (by decide),
    only (fun c inside isR => ?_) (by decide) (by decide),
    only (fun c inside isR => ?_) (by decide) (by decide)⟩
  all_goals
    rcases collectionClauses_relation inside with ⟨member, same⟩ | ⟨member, same⟩ | ⟨member, same⟩ |
        ⟨member, same⟩ <;>
      first
      | exact member
      | exact absurd (same.symm.trans isR) (by decide)

/-- The relations of the clauses that decide the laws. -/
theorem lawProgramClauses_relation {c : Clause} (inside : c ∈ lawProgramClauses language) :
    (c ∈ TypingClauses.typingClauses ∧ 17 ≤ c.relation ∧ c.relation ≤ 21) ∨
    (c ∈ TypingClauses.grammarClauses language ∧ c.relation = 17) ∨
    (c ∈ UnificationClauses.unificationClauses ∧ 7 ≤ c.relation ∧ c.relation ≤ 13) ∨
    (c ∈ TypingClauses.differClauses ∧ 14 ≤ c.relation ∧ c.relation ≤ 16) ∨
    (c = TypingClauses.typedClause ∧ c.relation = 22) ∨
    (c ∈ CollectionLaws.guardClauses language ∧ c.relation = 24) ∨
    (c ∈ CollectionLaws.listClauses ∧ 25 ≤ c.relation ∧ c.relation ≤ 27) ∨
    (c ∈ CollectionLaws.lawClauses language ∧ c.relation = 23) := by
  simp only [lawProgramClauses, List.mem_append, List.mem_singleton] at inside
  rcases inside with ((((((inTyping | inGrammar) | inUnification) | inDiffer) | rfl) | inGuards) | inLists) | inLaws
  · exact .inl ⟨inTyping, TypingClauses.typingClauses_relation c inTyping⟩
  · exact .inr (.inl ⟨inGrammar, TypingClauses.grammarClauses_relation inGrammar⟩)
  · exact .inr (.inr (.inl ⟨inUnification, UnificationClauses.unificationClauses_relation c inUnification⟩))
  · exact .inr (.inr (.inr (.inl ⟨inDiffer, TypingClauses.differClauses_relation c inDiffer⟩)))
  · exact .inr (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨inGuards, CollectionLaws.guardClauses_relation inGuards⟩)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨inLists, CollectionLaws.listClauses_relation inLists⟩))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨inLaws, CollectionLaws.lawClauses_relation inLaws⟩))))))

theorem lawProgramClauses_moded (language : LanguageDef) :
    ∀ c ∈ lawProgramClauses language, DemandTransformation.Moded c := by
  intro c inside
  simp only [lawProgramClauses, List.mem_append, List.mem_singleton] at inside
  rcases inside with ((((((inTyping | inGrammar) | inUnification) | inDiffer) | rfl) | inGuards) | inLists) | inLaws
  · exact TypingClauses.typingClauses_moded c inTyping
  · exact TypingClauses.grammarClauses_moded language c inGrammar
  · exact UnificationClauses.unificationClauses_moded c inUnification
  · exact TypingClauses.differClauses_moded c inDiffer
  · exact TypingClauses.typedClause_moded
  · exact CollectionLaws.guardClauses_moded language c inGuards
  · exact CollectionLaws.listClauses_moded c inLists
  · exact CollectionLaws.lawClauses_moded language c inLaws

/-- **A program holding the clauses that decide the laws, whose other clauses have other relations, is a program of
the laws.** -/
theorem lawProgram_of {program : List Clause} {R : Relations}
    (included : ∀ c ∈ lawProgramClauses language, c ∈ program) (collections : CollectionProgram program)
    (relations : ∀ c ∈ program, c ∈ lawProgramClauses language ∨ c.relation ≤ 6 ∨ 28 ≤ c.relation)
    (names : ∀ x y : String, R 0 [encode (.fvar x), encode (.fvar y)] (.sym 0) ↔ x ≠ y) :
    LawProgram language R program := by
  have origin : ∀ c ∈ program, 7 ≤ c.relation → c.relation ≤ 27 → c ∈ lawProgramClauses language :=
    fun c inside low high => by
      rcases relations c inside with inLaw | below | above
      · exact inLaw
      · omega
      · omega
  have sub : ∀ {cs : List Clause}, (∀ c ∈ cs, c ∈ lawProgramClauses language) → ∀ c ∈ cs, c ∈ program :=
    fun within c inside => included c (within c inside)
  refine ⟨⟨⟨sub fun c inside => ?_, sub fun c inside => ?_, fun c inside low high => ?_⟩,
      ⟨sub fun c inside => ?_, fun c inside low high => ?_, names⟩, sub fun c inside => ?_,
      fun c inside low high => ?_, included _ ?_, fun c inside isTyped => ?_⟩,
    collections.picks, collections.onlyPicks, sub fun c inside => ?_, fun c inside low high => ?_,
    sub fun c inside => ?_, fun c inside isGuard => ?_, sub fun c inside => ?_, fun c inside isLaw => ?_⟩
  · simp [lawProgramClauses, inside]
  · simp [lawProgramClauses, inside]
  · have low' : 17 ≤ c.relation := low
    have high' : c.relation ≤ 21 := high
    rcases lawProgramClauses_relation (origin c inside (by omega) (by omega)) with ⟨inT, t1, t2⟩ | ⟨inG, g⟩ | ⟨inU, u1, u2⟩ |
      ⟨inD, d1, d2⟩ | ⟨isT, tr⟩ | ⟨inGd, gd⟩ | ⟨inL, l1, l2⟩ | ⟨inW, w⟩
    · exact .inl inT
    · exact .inr ⟨g, inG⟩
    all_goals omega
  · simp [lawProgramClauses, inside]
  · have low' : 14 ≤ c.relation := low
    have high' : c.relation ≤ 16 := high
    rcases lawProgramClauses_relation (origin c inside (by omega) (by omega)) with ⟨inT, t1, t2⟩ | ⟨inG, g⟩ | ⟨inU, u1, u2⟩ |
      ⟨inD, d1, d2⟩ | ⟨isT, tr⟩ | ⟨inGd, gd⟩ | ⟨inL, l1, l2⟩ | ⟨inW, w⟩
    · omega
    · omega
    · omega
    · exact inD
    all_goals omega
  · simp [lawProgramClauses, inside]
  · have low' : 7 ≤ c.relation := low
    have high' : c.relation ≤ 13 := high
    rcases lawProgramClauses_relation (origin c inside (by omega) (by omega)) with ⟨inT, t1, t2⟩ | ⟨inG, g⟩ | ⟨inU, u1, u2⟩ |
      ⟨inD, d1, d2⟩ | ⟨isT, tr⟩ | ⟨inGd, gd⟩ | ⟨inL, l1, l2⟩ | ⟨inW, w⟩
    · omega
    · omega
    · exact inU
    all_goals omega
  · simp [lawProgramClauses]
  · have r : c.relation = 22 := isTyped
    rcases lawProgramClauses_relation (origin c inside (by omega) (by omega)) with ⟨inT, t1, t2⟩ | ⟨inG, g⟩ | ⟨inU, u1, u2⟩ |
      ⟨inD, d1, d2⟩ | ⟨isT, tr⟩ | ⟨inGd, gd⟩ | ⟨inL, l1, l2⟩ | ⟨inW, w⟩
    · omega
    · omega
    · omega
    · omega
    · exact isT
    all_goals omega
  · simp [lawProgramClauses, inside]
  · have low' : 25 ≤ c.relation := low
    have high' : c.relation ≤ 27 := high
    rcases lawProgramClauses_relation (origin c inside (by omega) (by omega)) with ⟨inT, t1, t2⟩ | ⟨inG, g⟩ | ⟨inU, u1, u2⟩ |
      ⟨inD, d1, d2⟩ | ⟨isT, tr⟩ | ⟨inGd, gd⟩ | ⟨inL, l1, l2⟩ | ⟨inW, w⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact inL
    · omega
  · simp [lawProgramClauses, inside]
  · have r : c.relation = 24 := isGuard
    rcases lawProgramClauses_relation (origin c inside (by omega) (by omega)) with ⟨inT, t1, t2⟩ | ⟨inG, g⟩ | ⟨inU, u1, u2⟩ |
      ⟨inD, d1, d2⟩ | ⟨isT, tr⟩ | ⟨inGd, gd⟩ | ⟨inL, l1, l2⟩ | ⟨inW, w⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact inGd
    all_goals omega
  · simp [lawProgramClauses, inside]
  · have r : c.relation = 23 := isLaw
    rcases lawProgramClauses_relation (origin c inside (by omega) (by omega)) with ⟨inT, t1, t2⟩ | ⟨inG, g⟩ | ⟨inU, u1, u2⟩ |
      ⟨inD, d1, d2⟩ | ⟨isT, tr⟩ | ⟨inGd, gd⟩ | ⟨inL, l1, l2⟩ | ⟨inW, w⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact inW

/-- **Where a clause of a compiled program comes from**, with its relation. -/
theorem compiled_relation {ruleCs equationCs : List Clause} (rulesAt : ∀ c ∈ ruleCs, c.relation = 0)
    (equationsAt : ∀ c ∈ equationCs, c.relation = 1) {c : Clause}
    {supply : List String}
    (inside : c ∈ ruleCs ++ collectionClauses ++ ScopeClauses.scopeClauses ++ (ScopeClauses.lowerClauses ++ ScopeClauses.abstractClauses) ++
        (quantifiedPremiseClauses language.rewrites ++ equationQuantifiedClauses language.equations) ++
        (DataClauses.dataClauses ++ DataClauses.supplyClauses supply) ++
          if language.isEquationFree then [] else
            equationCs ++ congruenceClauses ++ lawStepClause :: lawProgramClauses language) :
    (c ∈ ruleCs ∧ c.relation = 0) ∨ (c ∈ collectionClauses ∧ 3 ≤ c.relation ∧ c.relation ≤ 6) ∨
      (c ∈ ScopeClauses.scopeClauses ∧ 28 ≤ c.relation ∧ c.relation ≤ 33) ∨
      (c ∈ ScopeClauses.lowerClauses ++ ScopeClauses.abstractClauses ∧ 36 ≤ c.relation ∧ c.relation ≤ 40) ∨
      (c ∈ quantifiedPremiseClauses language.rewrites ++ equationQuantifiedClauses language.equations ∧
        34 ≤ c.relation ∧ c.relation ≤ 35) ∨
      (c ∈ DataClauses.dataClauses ++ DataClauses.supplyClauses supply ∧ 41 ≤ c.relation ∧ c.relation ≤ 44) ∨
      (language.isEquationFree = false ∧ ((c ∈ equationCs ∧ c.relation = 1) ∨
        (c ∈ congruenceClauses ∧ 1 ≤ c.relation ∧ c.relation ≤ 2) ∨ (c = lawStepClause ∧ c.relation = 1) ∨
        (c ∈ lawProgramClauses language ∧ 7 ≤ c.relation ∧ c.relation ≤ 27))) := by
  rcases List.mem_append.mp inside with inFirst | inBlock
  · rcases List.mem_append.mp inFirst with inFirst | inData
    swap
    · refine .inr (.inr (.inr (.inr (.inr (.inl ⟨inData, ?_⟩)))))
      rcases List.mem_append.mp inData with inDataClauses | inSupply
      · rcases DataClauses.dataClauses_relation c inDataClauses with same | same | same <;> rw [same] <;> decide
      · obtain ⟨label, -, rfl⟩ := List.mem_map.mp inSupply
        exact ⟨by simp [DataClauses.supplyClause, DataClauses.supplyRelation],
          by simp [DataClauses.supplyClause, DataClauses.supplyRelation]⟩
    rcases List.mem_append.mp inFirst with inFirst' | inQuantified
    · rcases List.mem_append.mp inFirst' with inFirst'' | inLower
      · rcases List.mem_append.mp inFirst'' with inFirst''' | inScope
        · rcases List.mem_append.mp inFirst''' with inRules | inCollection
          · exact .inl ⟨inRules, rulesAt c inRules⟩
          · refine .inr (.inl ⟨inCollection, ?_⟩)
            rcases collectionClauses_relation inCollection with ⟨-, same⟩ | ⟨-, same⟩ | ⟨-, same⟩ | ⟨-, same⟩ <;>
              rw [same] <;> decide
        · exact .inr (.inr (.inl ⟨inScope, ScopeClauses.scopeClauses_relation c inScope⟩))
      · refine .inr (.inr (.inr (.inl ⟨inLower, ?_⟩)))
        rcases List.mem_append.mp inLower with inLowering | inAbstracting
        · have bounds := ScopeClauses.lowerClauses_relation c inLowering
          simp only [ScopeClauses.subtractRelation, ScopeClauses.lowerListRelation] at bounds
          exact ⟨by omega, by omega⟩
        · have bounds := ScopeClauses.abstractClauses_relation c inAbstracting
          simp only [ScopeClauses.abstractRelation, ScopeClauses.abstractListRelation] at bounds
          exact ⟨by omega, by omega⟩
    · refine .inr (.inr (.inr (.inr (.inl ⟨inQuantified, ?_⟩))))
      rcases List.mem_append.mp inQuantified with inRules | inEquations
      · rcases quantifiedPremiseClauses_relation inRules with ⟨-, same⟩ | ⟨-, same⟩ <;> rw [same] <;> decide
      · obtain ⟨e, -, member⟩ := List.mem_flatMap.mp inEquations
        rcases List.mem_append.mp member with forward | backward
        · obtain ⟨q, -, cs, clausesAre, cIn⟩ := quantifiedClauses_origin forward
          rw [quantified_relation clausesAre c cIn]
          decide
        · obtain ⟨q, -, cs, clausesAre, cIn⟩ := quantifiedClauses_origin backward
          rw [quantified_relation clausesAre c cIn]
          decide
  · split at inBlock
    · exact absurd inBlock List.not_mem_nil
    · rename_i notFree
      refine .inr (.inr (.inr (.inr (.inr (.inr ⟨by simpa using notFree, ?_⟩)))))
      simp only [List.mem_append, List.mem_cons] at inBlock
      rcases inBlock with (inEquations | inCongruence) | rfl | inLaw
      · exact .inl ⟨inEquations, equationsAt c inEquations⟩
      · refine .inr (.inl ⟨inCongruence, ?_⟩)
        rcases congruence_relation inCongruence with same | same <;> rw [same] <;> decide
      · exact .inr (.inr (.inl ⟨rfl, rfl⟩))
      · refine .inr (.inr (.inr ⟨inLaw, ?_⟩))
        rcases lawProgramClauses_relation inLaw with ⟨-, r1, r2⟩ | ⟨-, r⟩ | ⟨-, r1, r2⟩ | ⟨-, r1, r2⟩ | ⟨-, r⟩ |
          ⟨-, r⟩ | ⟨-, r1, r2⟩ | ⟨-, r⟩ <;> omega

/-- **What the compiler checked**: the clauses of the rules, of collections, of scopes, of lowering, of quantified
premises, of the equations and of the laws, all moded. -/
theorem clausesOf_spec {supply : List String} {program : List Clause}
    (computed : clausesOf language supply = .ok program) :
    RuleClauses language program ∧ EquationClauses language program ∧ DataClauses.DataProgram supply program ∧
      ∀ c ∈ program, DemandTransformation.Moded c := by
  unfold clausesOf at computed
  split at computed
  · rename_i ruleCs equationCs rulesComputed equationsComputed
    cases computed
    obtain ⟨rulesShape, rulesOnly⟩ := ruleClauses_spec rulesComputed
    obtain ⟨equationsShape, equationsOnly⟩ := allEquationClauses_spec equationsComputed
    have ruleRelation : ∀ c ∈ ruleCs, c.relation = 0 := fun c inside => by
      obtain ⟨rule, -, lowered⟩ := rulesOnly c inside
      exact tripleClause_relation lowered
    have equationRelationOf : ∀ c ∈ equationCs, c.relation = 1 := fun c inside => by
      obtain ⟨e, -, lowered | lowered | lowered | lowered⟩ := equationsOnly c inside
      · exact tripleClause_relation lowered
      · exact converseClause_relation lowered
      · exact tripleClause_relation lowered
      · exact converseClause_relation lowered
    have quantifiedIn : ∀ c ∈ quantifiedPremiseClauses language.rewrites ++
        equationQuantifiedClauses language.equations, c ∈ ruleCs ++ collectionClauses ++ ScopeClauses.scopeClauses ++ (ScopeClauses.lowerClauses ++ ScopeClauses.abstractClauses) ++
        (quantifiedPremiseClauses language.rewrites ++ equationQuantifiedClauses language.equations) ++
        (DataClauses.dataClauses ++ DataClauses.supplyClauses supply) ++
          if language.isEquationFree then [] else
            equationCs ++ congruenceClauses ++ lawStepClause :: lawProgramClauses language :=
      fun c inside => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ inside))
    have lowerIn : ∀ c ∈ ScopeClauses.lowerClauses, c ∈ ruleCs ++ collectionClauses ++ ScopeClauses.scopeClauses ++ (ScopeClauses.lowerClauses ++ ScopeClauses.abstractClauses) ++
        (quantifiedPremiseClauses language.rewrites ++ equationQuantifiedClauses language.equations) ++
        (DataClauses.dataClauses ++ DataClauses.supplyClauses supply) ++
          if language.isEquationFree then [] else
            equationCs ++ congruenceClauses ++ lawStepClause :: lawProgramClauses language :=
      fun c inside => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_append_left _ inside))))
    have abstractIn : ∀ c ∈ ScopeClauses.abstractClauses, c ∈ ruleCs ++ collectionClauses ++ ScopeClauses.scopeClauses ++ (ScopeClauses.lowerClauses ++ ScopeClauses.abstractClauses) ++
        (quantifiedPremiseClauses language.rewrites ++ equationQuantifiedClauses language.equations) ++
        (DataClauses.dataClauses ++ DataClauses.supplyClauses supply) ++
          if language.isEquationFree then [] else
            equationCs ++ congruenceClauses ++ lawStepClause :: lawProgramClauses language :=
      fun c inside => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_append_right _ inside))))
    have blockIn : language.isEquationFree = false → ∀ c ∈ equationCs ++ congruenceClauses ++
        lawStepClause :: lawProgramClauses language, c ∈ ruleCs ++ collectionClauses ++ ScopeClauses.scopeClauses ++ (ScopeClauses.lowerClauses ++ ScopeClauses.abstractClauses) ++
        (quantifiedPremiseClauses language.rewrites ++ equationQuantifiedClauses language.equations) ++
        (DataClauses.dataClauses ++ DataClauses.supplyClauses supply) ++
          if language.isEquationFree then [] else
            equationCs ++ congruenceClauses ++ lawStepClause :: lawProgramClauses language :=
      fun notFree c inside => by
        rw [if_neg (by simp [notFree])]
        exact List.mem_append_right _ inside
    have collections : CollectionProgram (ruleCs ++ collectionClauses ++ ScopeClauses.scopeClauses ++ (ScopeClauses.lowerClauses ++ ScopeClauses.abstractClauses) ++
        (quantifiedPremiseClauses language.rewrites ++ equationQuantifiedClauses language.equations) ++
        (DataClauses.dataClauses ++ DataClauses.supplyClauses supply) ++
          if language.isEquationFree then [] else
            equationCs ++ congruenceClauses ++ lawStepClause :: lawProgramClauses language) := by
      refine collectionProgram_of
        (fun c inside => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ inside))))))
        (fun c inside => ?_)
      rcases compiled_relation ruleRelation equationRelationOf inside with ⟨-, r⟩ | ⟨inCollection, -⟩ |
        ⟨-, r1, -⟩ | ⟨-, l1, -⟩ | ⟨-, q1, -⟩ | ⟨-, dataLow, -⟩ | ⟨-, ⟨-, r⟩ | ⟨-, r1, r2⟩ | ⟨-, r⟩ | ⟨-, r1, r2⟩⟩
      · exact .inr (.inl (by omega))
      · exact .inl inCollection
      · exact .inr (.inr (by omega))
      · exact .inr (.inr (by omega))
      · exact .inr (.inr (by omega))
      · exact .inr (.inr (by omega))
      · exact .inr (.inl (by omega))
      · exact .inr (.inl (by omega))
      · exact .inr (.inl (by omega))
      · exact .inr (.inr (by omega))
    have scope : ScopeClauses.ScopeProgram (ruleCs ++ collectionClauses ++ ScopeClauses.scopeClauses ++ (ScopeClauses.lowerClauses ++ ScopeClauses.abstractClauses) ++
        (quantifiedPremiseClauses language.rewrites ++ equationQuantifiedClauses language.equations) ++
        (DataClauses.dataClauses ++ DataClauses.supplyClauses supply) ++
          if language.isEquationFree then [] else
            equationCs ++ congruenceClauses ++ lawStepClause :: lawProgramClauses language) := by
      refine ⟨fun c inside => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_right _ inside)))), fun c inside low high => ?_⟩
      have low' : 28 ≤ c.relation := low
      have high' : c.relation ≤ 33 := high
      rcases compiled_relation ruleRelation equationRelationOf inside with ⟨-, r⟩ | ⟨-, -, r2⟩ |
        ⟨inScope, -⟩ | ⟨-, l1, -⟩ | ⟨-, q1, -⟩ | ⟨-, dataLow, -⟩ | ⟨-, ⟨-, r⟩ | ⟨-, -, r2⟩ | ⟨-, r⟩ | ⟨-, -, r2⟩⟩
      · omega
      · omega
      · exact inScope
      all_goals omega
    have lowers : ScopeClauses.LowerProgram (ruleCs ++ collectionClauses ++ ScopeClauses.scopeClauses ++ (ScopeClauses.lowerClauses ++ ScopeClauses.abstractClauses) ++
        (quantifiedPremiseClauses language.rewrites ++ equationQuantifiedClauses language.equations) ++
        (DataClauses.dataClauses ++ DataClauses.supplyClauses supply) ++
          if language.isEquationFree then [] else
            equationCs ++ congruenceClauses ++ lawStepClause :: lawProgramClauses language) := by
      refine ⟨scope, lowerIn, fun c inside low high => ?_⟩
      have low' : 36 ≤ c.relation := low
      have high' : c.relation ≤ 38 := high
      rcases compiled_relation ruleRelation equationRelationOf inside with ⟨-, r⟩ | ⟨-, -, r2⟩ |
        ⟨-, -, r2⟩ | ⟨inLower, -⟩ | ⟨-, -, q2⟩ | ⟨-, dataLow, -⟩ | ⟨-, ⟨-, r⟩ | ⟨-, -, r2⟩ | ⟨-, r⟩ | ⟨-, -, r2⟩⟩
      · omega
      · omega
      · omega
      · rcases List.mem_append.mp inLower with inLowering | inAbstracting
        · exact inLowering
        · have bounds := ScopeClauses.abstractClauses_relation c inAbstracting
          simp only [ScopeClauses.abstractRelation] at bounds
          omega
      all_goals omega
    have abstracts : ScopeClauses.AbstractProgram (ruleCs ++ collectionClauses ++ ScopeClauses.scopeClauses ++
        (ScopeClauses.lowerClauses ++ ScopeClauses.abstractClauses) ++
        (quantifiedPremiseClauses language.rewrites ++ equationQuantifiedClauses language.equations) ++
        (DataClauses.dataClauses ++ DataClauses.supplyClauses supply) ++
          if language.isEquationFree then [] else
            equationCs ++ congruenceClauses ++ lawStepClause :: lawProgramClauses language) := by
      refine ⟨scope, abstractIn, fun c inside low high => ?_⟩
      have low' : 39 ≤ c.relation := low
      have high' : c.relation ≤ 40 := high
      rcases compiled_relation ruleRelation equationRelationOf inside with ⟨-, r⟩ | ⟨-, -, r2⟩ |
        ⟨-, -, r2⟩ | ⟨inLower, -⟩ | ⟨-, -, q2⟩ | ⟨-, dataLow, -⟩ | ⟨-, ⟨-, r⟩ | ⟨-, -, r2⟩ | ⟨-, r⟩ | ⟨-, -, r2⟩⟩
      · omega
      · omega
      · omega
      · rcases List.mem_append.mp inLower with inLowering | inAbstracting
        · have bounds := ScopeClauses.lowerClauses_relation c inLowering
          simp only [ScopeClauses.lowerListRelation] at bounds
          omega
        · exact inAbstracting
      all_goals omega
    have forAlls : ForAllClauses (ruleCs ++ collectionClauses ++ ScopeClauses.scopeClauses ++ (ScopeClauses.lowerClauses ++ ScopeClauses.abstractClauses) ++
        (quantifiedPremiseClauses language.rewrites ++ equationQuantifiedClauses language.equations) ++
        (DataClauses.dataClauses ++ DataClauses.supplyClauses supply) ++
          if language.isEquationFree then [] else
            equationCs ++ congruenceClauses ++ lawStepClause :: lawProgramClauses language) := by
      refine ⟨fun c inside => quantifiedIn c (List.mem_append_left _ (List.mem_append_left _ inside)),
        fun c inside isListOf => ?_, fun c inside isForAll => ?_⟩
      · have r : c.relation = 34 := isListOf
        rcases compiled_relation ruleRelation equationRelationOf inside with ⟨-, r'⟩ | ⟨-, -, r2⟩ |
          ⟨-, -, r2⟩ | ⟨-, l1, -⟩ | ⟨inQuantified, -⟩ | ⟨-, dataLow, -⟩ | ⟨-, ⟨-, r'⟩ | ⟨-, -, r2⟩ | ⟨-, r'⟩ | ⟨-, -, r2⟩⟩
        · omega
        · omega
        · omega
        · omega
        · rcases List.mem_append.mp inQuantified with inRules | inEquations
          · rcases quantifiedPremiseClauses_relation inRules with ⟨inList, -⟩ | ⟨-, r'⟩
            · exact inList
            · have r'' : c.relation = 35 := r'
              omega
          · obtain ⟨e, -, member⟩ := List.mem_flatMap.mp inEquations
            rcases List.mem_append.mp member with forward | backward
            · obtain ⟨q, -, cs, clausesAre, cIn⟩ := quantifiedClauses_origin forward
              have r'' : c.relation = 35 := quantified_relation clausesAre c cIn
              omega
            · obtain ⟨q, -, cs, clausesAre, cIn⟩ := quantifiedClauses_origin backward
              have r'' : c.relation = 35 := quantified_relation clausesAre c cIn
              omega
        all_goals omega
      · have r : c.relation = 35 := isForAll
        rcases compiled_relation ruleRelation equationRelationOf inside with ⟨-, r'⟩ | ⟨-, -, r2⟩ |
          ⟨-, -, r2⟩ | ⟨-, l1, -⟩ | ⟨inQuantified, -⟩ | ⟨-, dataLow, -⟩ | ⟨-, ⟨-, r'⟩ | ⟨-, -, r2⟩ | ⟨-, r'⟩ | ⟨-, -, r2⟩⟩
        · omega
        · omega
        · omega
        · omega
        · rcases List.mem_append.mp inQuantified with inRules | inEquations
          · rcases quantifiedPremiseClauses_relation inRules with ⟨-, r'⟩ | ⟨⟨rule, -, member⟩, -⟩
            · have r'' : c.relation = 34 := r'
              omega
            · obtain ⟨q, -, cs, clausesAre, cIn⟩ := quantifiedClauses_origin member
              exact ⟨q, cs, clausesAre, cIn⟩
          · obtain ⟨e, -, member⟩ := List.mem_flatMap.mp inEquations
            rcases List.mem_append.mp member with forward | backward
            · obtain ⟨q, -, cs, clausesAre, cIn⟩ := quantifiedClauses_origin forward
              exact ⟨q, cs, clausesAre, cIn⟩
            · obtain ⟨q, -, cs, clausesAre, cIn⟩ := quantifiedClauses_origin backward
              exact ⟨q, cs, clausesAre, cIn⟩
        all_goals omega
    refine ⟨⟨collections, ⟨scope, collections.unwraps, collections.onlyUnwraps⟩,
        fun rule inside => (rulesShape rule inside).1, fun rule inside => ?_, fun c inside isStep => ?_, forAlls,
        fun rule ruleIn => quantifiedClauses_present fun c inside =>
          quantifiedIn c (List.mem_append_left _ (List.mem_append_right _
            (List.mem_flatMap.mpr ⟨rule, ruleIn, inside⟩)))⟩,
      ⟨fun e inside => (equationsShape e inside).1, fun e inside => (equationsShape e inside).2.1,
        fun e inside => (equationsShape e inside).2.2.1, fun e inside => ?_, fun e inside => ?_,
        fun e inside => ?_, fun e inside => ?_,
        fun e eIn => quantifiedClauses_present fun c inside =>
          quantifiedIn c (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, eIn, List.mem_append_left _ inside⟩)),
        fun e eIn => quantifiedClauses_present fun c inside =>
          quantifiedIn c (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, eIn, List.mem_append_right _ inside⟩)),
        ⟨lowers, abstracts, collections.wraps, collections.onlyWraps⟩,
        fun notFree c inside => blockIn notFree c (List.mem_append_left _ (List.mem_append_right _ inside)),
        fun notFree => blockIn notFree _ (List.mem_append_right _ List.mem_cons_self),
        fun notFree R names => ?_, fun c inside related => ?_⟩,
      ⟨fun c inside => List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ inside)),
        fun label inside => List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _
          (List.mem_map.mpr ⟨label, inside, rfl⟩))), fun c inside isData' => ?_, fun c inside isSupply => ?_⟩,
      fun c inside => ?_⟩
    · obtain ⟨c, cIn, lowered⟩ := (rulesShape rule inside).2
      exact ⟨c, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ cIn))))), lowered⟩
    · have isZero : c.relation = 0 := isStep
      rcases compiled_relation ruleRelation equationRelationOf inside with ⟨inRules, -⟩ | ⟨-, r1, r2⟩ |
        ⟨-, r1, r2⟩ | ⟨-, l1, l2⟩ | ⟨-, q1, q2⟩ | ⟨-, dataLow, -⟩ | ⟨-, ⟨-, r⟩ | ⟨-, r1, r2⟩ | ⟨-, r⟩ | ⟨-, r1, r2⟩⟩
      · exact rulesOnly c inRules
      all_goals omega
    · obtain ⟨c, cIn, lowered⟩ := (equationsShape e inside).2.2.2.1
      exact ⟨c, blockIn (notFree_of_equation inside) c (List.mem_append_left _ (List.mem_append_left _ cIn)),
        lowered⟩
    · obtain ⟨c, cIn, lowered⟩ := (equationsShape e inside).2.2.2.2.1
      exact ⟨c, blockIn (notFree_of_equation inside) c (List.mem_append_left _ (List.mem_append_left _ cIn)),
        lowered⟩
    · obtain ⟨c, cIn, lowered⟩ := (equationsShape e inside).2.2.2.2.2.1
      exact ⟨c, blockIn (notFree_of_equation inside) c (List.mem_append_left _ (List.mem_append_left _ cIn)),
        lowered⟩
    · obtain ⟨c, cIn, lowered⟩ := (equationsShape e inside).2.2.2.2.2.2
      exact ⟨c, blockIn (notFree_of_equation inside) c (List.mem_append_left _ (List.mem_append_left _ cIn)),
        lowered⟩
    · refine lawProgram_of
        (fun c inside => blockIn notFree c (List.mem_append_right _ (List.mem_cons_of_mem _ inside))) collections
        (fun c inside => ?_) names
      rcases compiled_relation ruleRelation equationRelationOf inside with ⟨-, r⟩ | ⟨-, -, r2⟩ | ⟨-, r1, -⟩ |
        ⟨-, l1, -⟩ | ⟨-, q1, -⟩ | ⟨-, dataLow, -⟩ | ⟨-, ⟨-, r⟩ | ⟨-, -, r2⟩ | ⟨-, r⟩ | ⟨inLaw, -⟩⟩
      · exact .inr (.inl (by omega))
      · exact .inr (.inl r2)
      · exact .inr (.inr r1)
      · exact .inr (.inr (by omega))
      · exact .inr (.inr (by omega))
      · exact .inr (.inr (by omega))
      · exact .inr (.inl (by omega))
      · exact .inr (.inl (by omega))
      · exact .inr (.inl (by omega))
      · exact .inl inLaw
    · have related' : c.relation = 1 ∨ c.relation = 2 := related
      rcases compiled_relation ruleRelation equationRelationOf inside with ⟨-, r⟩ | ⟨-, r1, r2⟩ | ⟨-, r1, r2⟩ |
        ⟨-, l1, l2⟩ | ⟨-, q1, q2⟩ | ⟨-, dataLow, -⟩ | ⟨notFree, ⟨inEquations, -⟩ | ⟨inCongruence, -⟩ | ⟨rfl, -⟩ | ⟨-, r1, r2⟩⟩
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · exact .inl (equationsOnly c inEquations)
      · exact .inr (.inl inCongruence)
      · exact .inr (.inr ⟨rfl, notFree⟩)
      · omega
    · have r : 41 ≤ c.relation ∧ c.relation ≤ 43 := by
        rcases isData' with same | same | same <;> rw [same] <;> decide
      rcases compiled_relation ruleRelation equationRelationOf inside with ⟨-, r'⟩ | ⟨-, -, r2⟩ |
        ⟨-, -, r2⟩ | ⟨-, -, r2⟩ | ⟨-, -, r2⟩ | ⟨inData, -⟩ | ⟨-, ⟨-, r'⟩ | ⟨-, -, r2⟩ | ⟨-, r'⟩ | ⟨-, -, r2⟩⟩
      · omega
      · omega
      · omega
      · omega
      · omega
      · rcases List.mem_append.mp inData with inDataClauses | inSupply
        · exact inDataClauses
        · obtain ⟨label, -, rfl⟩ := List.mem_map.mp inSupply
          simp [DataClauses.supplyClause, DataClauses.supplyRelation] at r
      all_goals omega
    · have r : c.relation = 44 := isSupply
      rcases compiled_relation ruleRelation equationRelationOf inside with ⟨-, r'⟩ | ⟨-, -, r2⟩ |
        ⟨-, -, r2⟩ | ⟨-, -, r2⟩ | ⟨-, -, r2⟩ | ⟨inData, -⟩ | ⟨-, ⟨-, r'⟩ | ⟨-, -, r2⟩ | ⟨-, r'⟩ | ⟨-, -, r2⟩⟩
      · omega
      · omega
      · omega
      · omega
      · omega
      · rcases List.mem_append.mp inData with inDataClauses | inSupply
        · rcases DataClauses.dataClauses_relation c inDataClauses with same | same | same <;> rw [same] at r <;>
            exact absurd r (by decide)
        · obtain ⟨label, member, rfl⟩ := List.mem_map.mp inSupply
          exact ⟨label, member, rfl⟩
      all_goals omega
    · rcases List.mem_append.mp inside with inFirst | inBlock
      · rcases List.mem_append.mp inFirst with inFirst | inData
        swap
        · rcases List.mem_append.mp inData with inDataClauses | inSupply
          · exact DataClauses.dataClauses_moded c inDataClauses
          · obtain ⟨label, -, rfl⟩ := List.mem_map.mp inSupply
            exact DataClauses.supplyClause_moded label
        rcases List.mem_append.mp inFirst with inFirst' | inQuantified
        · rcases List.mem_append.mp inFirst' with inFirst'' | inLower
          · rcases List.mem_append.mp inFirst'' with inFirst''' | inScope
            · rcases List.mem_append.mp inFirst''' with inRules | inCollection
              · obtain ⟨rule, ruleIn, lowered⟩ := rulesOnly c inRules
                exact DemandRules.tripleClause_moded (rulesShape rule ruleIn).1 lowered
              · exact collectionClauses_moded c inCollection
            · exact ScopeClauses.scopeClauses_moded c inScope
          · rcases List.mem_append.mp inLower with inLowering | inAbstracting
            · exact ScopeClauses.lowerClauses_moded c inLowering
            · exact ScopeClauses.abstractClauses_moded c inAbstracting
        · rcases List.mem_append.mp inQuantified with inRules | inEquations
          · rcases List.mem_append.mp inRules with inList | inRuleQuantified
            · exact listOfClauses_moded c inList
            · obtain ⟨rule, ruleIn, member⟩ := List.mem_flatMap.mp inRuleQuantified
              exact quantifiedClauses_moded (rulesShape rule ruleIn).1 c member
          · obtain ⟨e, eIn, member⟩ := List.mem_flatMap.mp inEquations
            rcases List.mem_append.mp member with forward | backward
            · exact quantifiedClauses_moded (equationsShape e eIn).2.1 c forward
            · exact quantifiedClauses_moded (equationsShape e eIn).2.2.1 c backward
      · split at inBlock
        · exact absurd inBlock List.not_mem_nil
        · simp only [List.mem_append, List.mem_cons] at inBlock
          rcases inBlock with (inEquations | inCongruence) | rfl | inLaw
          · obtain ⟨e, eIn, lowered | lowered | lowered | lowered⟩ := equationsOnly c inEquations
            · exact DemandRules.tripleClause_moded (equationsShape e eIn).2.1 lowered
            · exact DemandRules.converseClause_moded (equationsShape e eIn).2.1 lowered
            · exact DemandRules.tripleClause_moded (equationsShape e eIn).2.2.1 lowered
            · exact DemandRules.converseClause_moded (equationsShape e eIn).2.2.1 lowered
          · exact congruenceClauses_moded c inCongruence
          · exact lawStepClause_moded
          · exact lawProgramClauses_moded language c inLaw
  · cases computed
  · cases computed

/-- A triple whose other side carries no binder display names is never refused for them. -/
theorem tripleChecked_canonical {lower : ℕ → Pattern → Pattern → List Premise → Option Clause} {relation : ℕ}
    {name : String} {left right : Pattern} {premises : List Premise}
    (canonical : right.hasCanonicalBinderMetadata = true) (other : String) :
    tripleChecked lower relation name left right premises ≠ .error (.binderNames other) := by
  unfold tripleChecked
  rw [if_pos canonical]
  split
  · split <;> simp
  · simp

theorem ruleClauses_canonical : ∀ {rules : List RewriteRule},
    (∀ rule ∈ rules, rule.right.hasCanonicalBinderMetadata = true) →
      ∀ other, ruleClauses rules ≠ .error (.binderNames other)
  | [], _, _ => by simp [ruleClauses]
  | rule :: rules, canonical, other => by
      have here : DemandRules.ruleClause rule ≠ .error (.binderNames other) :=
        tripleChecked_canonical (canonical rule List.mem_cons_self) other
      have later := ruleClauses_canonical (fun r inside => canonical r (List.mem_cons_of_mem _ inside)) other
      simp only [ruleClauses]
      generalize DemandRules.ruleClause rule = first at here
      generalize ruleClauses rules = second at later
      cases first <;> cases second <;> simp_all

theorem equationClauses_canonical {equation : Equation} (leftCanonical : equation.left.hasCanonicalBinderMetadata = true)
    (rightCanonical : equation.right.hasCanonicalBinderMetadata = true) (other : String) :
    equationClauses equation ≠ .error (.binderNames other) := by
  unfold equationClauses
  split
  · have n1 := tripleChecked_canonical (lower := tripleClause) (relation := equationRelation) (name := equation.name)
      (left := equation.left) (premises := equation.premises) rightCanonical other
    have n2 := tripleChecked_canonical (lower := converseClause) (relation := equationRelation)
      (name := equation.name) (left := equation.left) (premises := equation.premises) rightCanonical other
    have n3 := tripleChecked_canonical (lower := tripleClause) (relation := equationRelation) (name := equation.name)
      (left := equation.right) (premises := equation.premises) leftCanonical other
    have n4 := tripleChecked_canonical (lower := converseClause) (relation := equationRelation)
      (name := equation.name) (left := equation.right) (premises := equation.premises) leftCanonical other
    generalize tripleChecked tripleClause equationRelation equation.name equation.left equation.right
      equation.premises = r1 at n1
    generalize tripleChecked converseClause equationRelation equation.name equation.left equation.right
      equation.premises = r2 at n2
    generalize tripleChecked tripleClause equationRelation equation.name equation.right equation.left
      equation.premises = r3 at n3
    generalize tripleChecked converseClause equationRelation equation.name equation.right equation.left
      equation.premises = r4 at n4
    cases r1 <;> cases r2 <;> cases r3 <;> cases r4 <;> simp_all
  · simp

theorem allEquationClauses_canonical : ∀ {equations : List Equation},
    (∀ e ∈ equations, e.left.hasCanonicalBinderMetadata = true ∧ e.right.hasCanonicalBinderMetadata = true) →
      ∀ other, allEquationClauses equations ≠ .error (.binderNames other)
  | [], _, _ => by simp [allEquationClauses]
  | equation :: equations, canonical, other => by
      have here := equationClauses_canonical (canonical equation List.mem_cons_self).1
        (canonical equation List.mem_cons_self).2 other
      have later := allEquationClauses_canonical (fun e inside => canonical e (List.mem_cons_of_mem _ inside)) other
      simp only [allEquationClauses]
      generalize equationClauses equation = first at here
      generalize allEquationClauses equations = second at later
      cases first <;> cases second <;> simp_all

/-- **The canonical presentation is never refused for binder display names.** -/
theorem clausesOf_canonical (language : LanguageDef) (supply : List String) (other : String) :
    clausesOf language.eraseBinderMetadata supply ≠ .error (.binderNames other) := by
  have rules := ruleClauses_canonical (rules := language.eraseBinderMetadata.rewrites)
    (fun rule inside => (LanguageDef.rule_canonical inside).2.1) other
  have equations := allEquationClauses_canonical (equations := language.eraseBinderMetadata.equations)
    (fun e inside => LanguageDef.equation_canonical inside) other
  unfold clausesOf
  generalize ruleClauses language.eraseBinderMetadata.rewrites = first at rules
  generalize allEquationClauses language.eraseBinderMetadata.equations = second at equations
  cases first <;> cases second <;> simp_all

theorem compile_eq (language : LanguageDef) (supply : List String) :
    compile language supply = (clausesOf language.eraseBinderMetadata supply).map fun program =>
      runRules program moves := rfl

/-- What the compiler refuses does not depend on the supply. -/
theorem clausesOf_supply {supply : List String} {program : List Clause}
    (computed : clausesOf language supply = .ok program) (other : List String) :
    ∃ program', clausesOf language other = .ok program' := by
  unfold clausesOf at computed ⊢
  split at computed
  · exact ⟨_, rfl⟩
  · cases computed
  · cases computed

/-- **GSLT modulo equations to transform, over a supply**: a language the compiler accepts, its moves over the supply
on data, and the run of its clauses with the supply on the transform step. -/
def compiledCorrespondence {O : Type} [DecidableEq O] [Infinite O] {supply : List String}
    (dataRows : DataRows relEnv language) (computed : clausesOf language supply = .ok program) :
    OperationalCorrespondence (equalityGSLT Pattern (MoveWithin relEnv language supply))
      (programSystem O (specialized rows (relationGraph (premiseRelations relEnv language))
        {ρ | ρ ∈ runRules program moves})) :=
  (rowCorrespondence dataRows (clausesOf_spec computed).1 (clausesOf_spec computed).2.1
    (clausesOf_spec computed).2.2.1).comp
    (DemandTransformation.stepCorrespondence (premiseRelations relEnv language) program
      (clausesOf_spec computed).2.2.2 moves)

/-- **Reachability modulo equations is reachability by moves, over some supply.** -/
theorem reachModulo_iff (dataRows : DataRows relEnv language) {supply : List String}
    (computed : clausesOf language supply = .ok program) {s t : Pattern} (data : isData s = true) :
    ReachModulo relEnv language s t ↔ ∃ supply', Relation.ReflTransGen (MoveWithin relEnv language supply') s t :=
  ⟨moves_complete dataRows (clausesOf_spec computed).1 (clausesOf_spec computed).2.1 data,
    fun ⟨_, path⟩ => moves_sound dataRows (clausesOf_spec computed).1 (clausesOf_spec computed).2.1 path⟩

/-! ## Controls -/

namespace Controls

/-- Without relations of its own, an environment answers data with data. -/
theorem empty_dataRows (language : LanguageDef) : DataRows RelationEnv.empty language := by
  intro relation asked row offered askedData
  simp only [QueryPremises.queryRows, RelationEnv.empty, List.append_nil, builtinRelationTuples] at offered
  split at offered
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at offered
    simp only [isDataList, Bool.and_eq_true] at askedData
    rcases offered with rfl | rfl <;> simp [isDataList, askedData]
  · simp at offered

/-- The refusal of a compilation, if any. -/
def refusalOf {α : Type} : Except Refusal α → Option Refusal
  | .error reason => some reason
  | .ok _ => none

theorem eq_error_of_refusalOf {α : Type} {result : Except Refusal α} {reason : Refusal}
    (refused : refusalOf result = some reason) : result = .error reason := by
  cases result with
  | error other => simp only [refusalOf, Option.some.injEq] at refused; rw [refused]
  | ok _ => simp [refusalOf] at refused

/-- Two components may be exchanged. -/
def swap : Equation where
  name := "swap"
  typeContext := []
  premises := []
  left := .apply "pair" [.fvar "x", .fvar "y"]
  right := .apply "pair" [.fvar "y", .fvar "x"]

/-- A pair whose first component is zero gives its second. -/
def pickZero : RewriteRule where
  name := "pickZero"
  typeContext := []
  premises := []
  left := .apply "pick" [.apply "pair" [.apply "zero" [], .fvar "y"]]
  right := .fvar "y"

/-- Pairs modulo exchange. -/
def swapping : LanguageDef := { LanguageDef.empty "swapping" with rewrites := [pickZero], equations := [swap] }

/-- **Positive**: an equation is compiled in both orientations and their converses, beside the rules. -/
theorem swapping_compiles : (clausesOf swapping []).isOk = true := by decide

/-- A term equals a constant, whatever its argument. -/
def collapse : Equation where
  name := "collapse"
  typeContext := []
  premises := []
  left := .apply "f" [.fvar "x"]
  right := .apply "c" []

def collapsing : LanguageDef := { LanguageDef.empty "collapsing" with equations := [collapse] }

/-- **Positive**: an equation with a name on one side only compiles: taken back from the constant side, the name's
value is chosen over the supply. -/
theorem collapse_compiles : (clausesOf collapsing []).isOk = true := by decide

theorem collapse_free : freeNames collapse.left collapse.right = ["x"] := by decide

/-- **Positive**: over the supply `a`, the compiled program relates `c` to `f(a)`: taken back, the equation chooses `a`
for its name. -/
theorem collapse_chooses : ∃ program, clausesOf collapsing ["a"] = .ok program ∧
    Derives (premiseRelations RelationEnv.empty collapsing) program equationRelation
      (encode (.apply "c" [])) (encode (.apply "f" [.apply "a" []])) := by
  obtain ⟨program, computed⟩ : ∃ program, clausesOf collapsing ["a"] = .ok program := ⟨_, rfl⟩
  obtain ⟨rules, equations, dataClauses, -⟩ := clausesOf_spec computed
  refine ⟨program, computed, (derives_equation_iff (empty_dataRows _) rules equations dataClauses
    (by decide)).mpr ⟨_, rfl, by decide, .inr ⟨.hole, _, _, rfl, rfl, .inl ⟨collapse, by simp [collapsing],
      by decide, .inl ⟨[("x", .apply "a" [])], [("x", .apply "a" [])], [], matchPattern_sound (by decide +kernel),
        .nil _, by decide +kernel, ?_, ?_⟩⟩⟩⟩⟩
  · intro name free label inside
    rw [collapse_free, List.mem_singleton] at free
    subst free
    have value : lookupOrFvar [("x", Pattern.apply "a" [])] "x" = .apply "a" [] := by decide +kernel
    rw [value] at inside
    simpa [DataClauses.labelsOf, DataClauses.labelsOfList] using inside
  · intro v inside
    simp [collapse, Instantiation.substValues, Instantiation.substValuesList] at inside

theorem equationStep_cases {language : LanguageDef} {u v : Pattern}
    (step : EquationStep RelationEnv.empty language u v) :
    ∃ (context : OneHoleContext) (redex contractum : Pattern), Generator RelationEnv.empty language redex contractum ∧
      u = context.fill redex ∧ v = context.fill contractum := by
  cases step with
  | inContext context generator => exact ⟨context, _, _, generator, rfl, rfl⟩

theorem hole_of_fill_constant {context : OneHoleContext} {p : Pattern} (filled : context.fill p = .apply "c" []) :
    context = .hole ∧ p = .apply "c" [] := by
  cases context <;> simp [OneHoleContext.fill] at filled ⊢
  exact filled

/-- **Negative**: over the supply `b`, the compiled program does not relate `c` to `f(a)`: `a` is no value over the
supply, and read from the constant side the equation gives the name itself, `f(x)`. -/
theorem collapse_needs_the_supply {program : List Clause} (computed : clausesOf collapsing ["b"] = .ok program) :
    ¬ Derives (premiseRelations RelationEnv.empty collapsing) program equationRelation
      (encode (.apply "c" [])) (encode (.apply "f" [.apply "a" []])) := by
  intro derived
  obtain ⟨rules, equations, dataClauses, -⟩ := clausesOf_spec computed
  obtain ⟨t, same, -, step⟩ := (derives_equation_iff (empty_dataRows _) rules equations dataClauses
    (by decide)).mp derived
  obtain rfl := RootRewritesOnTheStep.encode_injective same
  have noLaws : ∀ s t, ¬ DerivedInstance collapsing s t :=
    no_derivedInstance_of_no_derived_laws (by decide) (by decide) (by decide)
  rcases step with forward | back
  · obtain ⟨context, redex, contractum, generator, sourceIs, targetIs⟩ := equationStep_cases forward
    obtain ⟨rfl, redexIs⟩ := hole_of_fill_constant sourceIs.symm
    simp only [OneHoleContext.fill] at targetIs
    rcases generator with authored | derived
    · cases authored with
      | forward member raw matched passed =>
          simp only [collapsing, LanguageDef.empty, List.mem_singleton] at member
          subst member
          rw [redexIs] at matched
          have unmatched : matchPattern collapse.left (.apply "c" []) = [] := by decide +kernel
          rw [unmatched] at matched
          exact absurd matched List.not_mem_nil
      | reverse member raw matched passed =>
          simp only [collapsing, LanguageDef.empty, List.mem_singleton] at member
          subst member
          rw [redexIs] at matched
          have only_ : matchPattern collapse.right (.apply "c" []) = [[]] := by decide +kernel
          rw [only_, List.mem_singleton] at matched
          subst matched
          cases passed
          have literal : applyBindingsScoped (captureSitesOf collapse.right collapse.premises) [] 0 collapse.left =
              .apply "f" [.fvar "x"] := by decide +kernel
          rw [literal] at targetIs
          simp at targetIs
      | declared member notRaw _ =>
          simp only [collapsing, LanguageDef.empty, List.mem_singleton] at member
          subst member
          exact absurd notRaw (by decide)
      | premised member notRaw _ _ =>
          simp only [collapsing, LanguageDef.empty, List.mem_singleton] at member
          subst member
          exact absurd notRaw (by decide)
    · exact noLaws _ _ derived
  · obtain ⟨context, origin, target, originIs, targetIs, generator⟩ := back
    obtain ⟨rfl, rfl⟩ := hole_of_fill_constant originIs.symm
    simp only [OneHoleContext.fill] at targetIs
    subst targetIs
    rcases generator with ⟨e, member, -, within | within⟩ | derived
    · simp only [collapsing, LanguageDef.empty, List.mem_singleton] at member
      subst member
      obtain ⟨initial, final, witnesses, matched, -, -, supplied, -⟩ := within
      have found := matchPattern_iff_matchRel.mpr matched
      have only_ : matchPattern collapse.left (.apply "f" [.apply "a" []]) = [[("x", .apply "a" [])]] := by
        decide +kernel
      rw [only_, List.mem_singleton] at found
      subst found
      have chosen := supplied "x" (by rw [collapse_free]; exact List.mem_singleton_self _) "a" (by decide +kernel)
      exact absurd chosen (by decide)
    · simp only [collapsing, LanguageDef.empty, List.mem_singleton] at member
      subst member
      obtain ⟨initial, final, witnesses, matched, -, -, -, -⟩ := within
      have found := matchPattern_iff_matchRel.mpr matched
      have unmatched : matchPattern collapse.right (.apply "f" [.apply "a" []]) = [] := by decide +kernel
      rw [unmatched] at found
      exact absurd found List.not_mem_nil
    · exact noLaws _ _ derived

/-- Chaos absorbs whatever runs beside it. -/
def chaos : Equation where
  name := "chaos"
  typeContext := []
  premises := []
  left := .apply "PPar" [.collection .hashBag [.apply "PChaos" [], .fvar "P"] none]
  right := .apply "PChaos" []

def chaotic : LanguageDef := { LanguageDef.empty "chaotic" with equations := [chaos] }

/-- **Positive**: an equation whose name lies in a bag on one side only compiles. -/
theorem chaos_compiles : (clausesOf chaotic []).isOk = true := by decide

/-- **Positive**: over the supply `u`, the compiled program relates `PChaos` to `PPar {PChaos, u}`. -/
theorem chaos_chooses : ∃ program, clausesOf chaotic ["u"] = .ok program ∧
    Derives (premiseRelations RelationEnv.empty chaotic) program equationRelation
      (encode (.apply "PChaos" []))
      (encode (.apply "PPar" [.collection .hashBag [.apply "PChaos" [], .apply "u" []] none])) := by
  obtain ⟨program, computed⟩ : ∃ program, clausesOf chaotic ["u"] = .ok program := ⟨_, rfl⟩
  obtain ⟨rules, equations, dataClauses, -⟩ := clausesOf_spec computed
  refine ⟨program, computed, (derives_equation_iff (empty_dataRows _) rules equations dataClauses
    (by decide)).mpr ⟨_, rfl, by decide, .inr ⟨.hole, .apply "PChaos" [],
      .apply "PPar" [.collection .hashBag [.apply "PChaos" [], .apply "u" []] none], rfl, rfl,
      .inl ⟨chaos, by simp [chaotic], by decide, .inl ⟨[("P", .apply "u" [])], [("P", .apply "u" [])], [],
        matchPattern_sound (by decide +kernel), .nil _, by decide +kernel, ?_, ?_⟩⟩⟩⟩⟩
  · have onlyP : freeNames chaos.left chaos.right = ["P"] := by decide
    intro name free label inside
    rw [onlyP, List.mem_singleton] at free
    subst free
    have value : lookupOrFvar [("P", Pattern.apply "u" [])] "P" = .apply "u" [] := by decide +kernel
    rw [value] at inside
    simpa [DataClauses.labelsOf, DataClauses.labelsOfList] using inside
  · intro v inside
    simp [chaos, Instantiation.substValues, Instantiation.substValuesList] at inside

/-- Two terms are equal when one steps to the other's argument. -/
def stepped : Equation where
  name := "stepped"
  typeContext := []
  premises := [.congruence (.fvar "z") (.fvar "y")]
  left := .apply "g" [.fvar "x"]
  right := .apply "h" [.fvar "x"]

def stepping : LanguageDef := { LanguageDef.empty "stepping" with equations := [stepped] }

/-- **Positive**: an equation whose premise asks the step of a name that no side binds compiles: the step's source is
the name itself, as in the source. -/
theorem stepped_compiles : (clausesOf stepping []).isOk = true := by decide

/-- Every term finishes. -/
def finish : RewriteRule where
  name := "finish"
  typeContext := []
  premises := []
  left := .fvar "m"
  right := .apply "done" []

def steppingOn : LanguageDef := { LanguageDef.empty "steppingOn" with rewrites := [finish], equations := [stepped] }

/-- **Positive**: where every term finishes, the name `z` itself steps, so `g(a)` and `h(a)` are one equation step
apart. -/
theorem stepped_relates : ∃ program, clausesOf steppingOn [] = .ok program ∧
    Derives (premiseRelations RelationEnv.empty steppingOn) program equationRelation
      (encode (.apply "g" [.apply "a" []])) (encode (.apply "h" [.apply "a" []])) := by
  obtain ⟨program, computed⟩ : ∃ program, clausesOf steppingOn [] = .ok program := ⟨_, rfl⟩
  obtain ⟨rules, equations, dataClauses, -⟩ := clausesOf_spec computed
  refine ⟨program, computed, (derives_equation_iff (empty_dataRows _) rules equations dataClauses
    (by decide)).mpr ⟨_, rfl, by decide, .inl ?_⟩⟩
  have finished : StepValid RelationEnv.empty steppingOn (.fvar "z") (.rule 0 [("m", .fvar "z")] [])
      (.apply "done" []) :=
    (Mettapedia.OSLF.MeTTaIL.ReferenceStep.checkStep_eq_some_iff RelationEnv.empty steppingOn _).mp
      (by decide +kernel)
  have sourceIs : applyBindingsScoped (captureSitesOf stepped.left stepped.premises) [("x", .apply "a" [])]
      (stepDepth (captureSitesOf stepped.left stepped.premises) (.congruence (.fvar "z") (.fvar "y")))
      (.fvar "z") = .fvar "z" := by decide +kernel
  have premise : PremisesValid RelationEnv.empty steppingOn (captureSitesOf stepped.left stepped.premises)
      [("x", .apply "a" [])] stepped.premises
      [.premiseStep (.rule 0 [("m", .fvar "z")] []) (.apply "done" []) [("y", .apply "done" [])]
        [("y", .apply "done" []), ("x", .apply "a" [])]]
      [("y", .apply "done" []), ("x", .apply "a" [])] :=
    .cons (.step rfl (sourceIs ▸ finished) (by decide +kernel) (by decide +kernel)) (.nil _)
  have generator := AuthoredEquation.forward (relEnv := RelationEnv.empty) (language := steppingOn)
    (equation := stepped) (source := .apply "g" [.apply "a" []]) (by simp [steppingOn]) (by decide)
    (by decide +kernel) premise
  have target : applyBindingsScoped (captureSitesOf stepped.left stepped.premises)
      [("y", .apply "done" []), ("x", .apply "a" [])] 0 stepped.right = .apply "h" [.apply "a" []] := by
    decide +kernel
  rw [target] at generator
  exact .inContext .hole (.inl generator)

/-- A rule whose premise steps a name no side binds. -/
def literalStep : RewriteRule where
  name := "literalStep"
  typeContext := []
  premises := [.congruence (.fvar "z") (.fvar "y")]
  left := .apply "g" [.fvar "x"]
  right := .apply "h" [.fvar "x"]

def literalStepping : LanguageDef := { LanguageDef.empty "literalStepping" with rewrites := [literalStep] }

/-- **Negative**: where nothing steps the name `z` itself, the rule does not fire: `g(a)` does not step. -/
theorem literalStep_needs_the_name {program : List Clause} (computed : clausesOf literalStepping [] = .ok program)
    (w : Expr) : ¬ Derives (premiseRelations RelationEnv.empty literalStepping) program stepRelation
      (encode (.apply "g" [.apply "a" []])) w := by
  intro derived
  obtain ⟨t, -, step⟩ := (derives_step_iff (empty_dataRows _) (clausesOf_spec computed).1
    (by decide)).mp derived
  have stuck : ∀ t, ¬ Step RelationEnv.empty literalStepping (.fvar "z") t := by
    intro t stepped
    obtain ⟨rule, member, initial, -, -, matched, -, -⟩ := StepPremises.step_iff.mp stepped
    simp only [literalStepping, List.mem_singleton] at member
    subst member
    have unmatched : matchPattern literalStep.left (.fvar "z") = [] := by decide +kernel
    exact absurd (matchPattern_iff_matchRel.mpr matched) (by rw [unmatched]; exact List.not_mem_nil)
  obtain ⟨rule, member, initial, final, witnesses, matched, passed, -⟩ := StepPremises.step_iff.mp step
  simp only [literalStepping, List.mem_singleton] at member
  subst member
  have found := matchPattern_iff_matchRel.mpr matched
  have matches_ : matchPattern literalStep.left (.apply "g" [.apply "a" []]) = [[("x", .apply "a" [])]] := by
    decide +kernel
  rw [matches_, List.mem_singleton] at found
  subst found
  cases passed with
  | cons here _ =>
    obtain ⟨stepWitness, candidate, -, -, stepped, -, -⟩ := StepPremises.premiseValid_step rfl here
    have sourceIs : applyBindingsScoped (captureSitesOf literalStep.left literalStep.premises) [("x", .apply "a" [])]
        (stepDepth (captureSitesOf literalStep.left literalStep.premises) (.congruence (.fvar "z") (.fvar "y")))
        (.fvar "z") = .fvar "z" := by decide +kernel
    exact stuck candidate ⟨stepWitness, sourceIs ▸ stepped⟩

/-- A restriction drops its name when the name does not occur in the body. -/
def dropUnused : RewriteRule where
  name := "dropUnused"
  typeContext := []
  premises := [.freshness { varName := "x", term := .fvar "p" }]
  left := .apply "new" [.fvar "x", .fvar "p"]
  right := .fvar "p"

def restricting : LanguageDef := { LanguageDef.empty "restricting" with rewrites := [dropUnused] }

/-- **Positive**: a rule with a freshness condition compiles; the condition is the source's own freshness check. -/
theorem restricting_compiles : (clausesOf restricting []).isOk = true := by decide

/-- A freshness condition on a name nothing binds. -/
def dropUnbound : RewriteRule where
  name := "dropUnbound"
  typeContext := []
  premises := [.freshness { varName := "y", term := .fvar "p" }]
  left := .apply "new" [.fvar "x", .fvar "p"]
  right := .fvar "p"

def unboundFresh : LanguageDef := { LanguageDef.empty "unboundFresh" with rewrites := [dropUnbound] }

/-- **Positive**: a freshness condition on a name the rule does not bind compiles: the name is read as itself. -/
theorem unboundFresh_compiles : (clausesOf unboundFresh []).isOk = true := by decide

/-- **Positive**: the compiled program drops a restriction whose body does not mention the name `y` itself. -/
theorem unboundFresh_steps : ∃ program, clausesOf unboundFresh [] = .ok program ∧
    Derives (premiseRelations RelationEnv.empty unboundFresh) program stepRelation
      (encode (.apply "new" [.apply "a" [], .fvar "q"])) (encode (.fvar "q")) := by
  obtain ⟨program, computed⟩ : ∃ program, clausesOf unboundFresh [] = .ok program := ⟨_, rfl⟩
  refine ⟨program, computed, (derives_step_iff (empty_dataRows _) (clausesOf_spec computed).1
    (by decide)).mpr ⟨_, rfl, .rule 0 [("p", .fvar "q"), ("x", .apply "a" [])]
      [.base [("p", .fvar "q"), ("x", .apply "a" [])]], ?_⟩⟩
  exact (Mettapedia.OSLF.MeTTaIL.ReferenceStep.checkStep_eq_some_iff RelationEnv.empty unboundFresh _).mp
    (by decide +kernel)

/-- **Negative**: it does not drop a restriction whose body mentions the name `y` itself. -/
theorem unboundFresh_reads_the_name {program : List Clause} (computed : clausesOf unboundFresh [] = .ok program)
    (w : Expr) : ¬ Derives (premiseRelations RelationEnv.empty unboundFresh) program stepRelation
      (encode (.apply "new" [.apply "a" [], .fvar "y"])) w := by
  intro derived
  obtain ⟨t, -, step⟩ := (derives_step_iff (empty_dataRows _) (clausesOf_spec computed).1
    (by decide)).mp derived
  obtain ⟨rule, member, initial, final, witnesses, matched, passed, -⟩ := StepPremises.step_iff.mp step
  simp only [unboundFresh, List.mem_singleton] at member
  subst member
  have found := matchPattern_iff_matchRel.mpr matched
  have matches_ : matchPattern dropUnbound.left (.apply "new" [.apply "a" [], .fvar "y"]) =
      [[("p", .fvar "y"), ("x", .apply "a" [])]] := by decide +kernel
  rw [matches_, List.mem_singleton] at found
  subst found
  cases passed with
  | cons here _ =>
    obtain ⟨-, offered⟩ := StepPremises.premiseValid_base rfl here
    have none_ : premiseStepWithEnv RelationEnv.empty unboundFresh [("p", .fvar "y"), ("x", .apply "a" [])]
        (.freshness { varName := "y", term := .fvar "p" }) = [] := by decide +kernel
    rw [none_] at offered
    exact absurd offered List.not_mem_nil

/-- Two reagents react to a product, beside whatever else is present. -/
def react : RewriteRule where
  name := "react"
  typeContext := []
  premises := []
  left := .collection .hashBag [.apply "a" [], .apply "b" []] (some "rest")
  right := .collection .hashBag [.apply "c" []] (some "rest")

def reacting : LanguageDef := { LanguageDef.empty "reacting" with rewrites := [react] }

/-- **Positive**: a rule that picks elements of a bag and keeps its rest compiles. -/
theorem reacting_compiles : (clausesOf reacting []).isOk = true := by decide

/-- A set with an element equals the element beside the set without it. -/
def unfoldSet : Equation where
  name := "unfoldSet"
  typeContext := []
  premises := []
  left := .apply "set" [.collection .hashSet [.fvar "x"] (some "r")]
  right := .apply "cons" [.fvar "x", .apply "set" [.collection .hashSet [] (some "r")]]

def unfolding : LanguageDef := { LanguageDef.empty "unfolding" with equations := [unfoldSet] }

/-- **Positive**: an equation that matches a set on one side and a smaller set on the other compiles. -/
theorem unfolding_compiles : (clausesOf unfolding []).isOk = true := by decide

/-- A bag's rest given back as a set. -/
def rekind : RewriteRule where
  name := "rekind"
  typeContext := []
  premises := []
  left := .apply "f" [.collection .hashBag [] (some "r")]
  right := .apply "g" [.collection .hashSet [] (some "r")]

def rekinding : LanguageDef := { LanguageDef.empty "rekinding" with rewrites := [rekind] }

/-- **Negative**: a rest given back in a collection of another kind is refused by the rule's name. -/
theorem rekinding_refused : clausesOf rekinding [] = .error (.restOfResult "rekind") :=
  eq_error_of_refusalOf (by decide)

/-- A rule under a binder. -/
def underBinder : RewriteRule where
  name := "underBinder"
  typeContext := []
  premises := []
  left := .lambda none (.apply "a" [])
  right := .apply "b" []

def binding : LanguageDef := { LanguageDef.empty "binding" with rewrites := [underBinder] }

/-- **Positive**: a rule whose left side holds a binder compiles. -/
theorem binding_compiles : (clausesOf binding []).isOk = true := by decide

/-- β: an application of an abstraction is its body with the argument for its bound index. -/
def beta : RewriteRule where
  name := "beta"
  typeContext := []
  premises := []
  left := .apply "app" [.lambda none (.fvar "B"), .fvar "A"]
  right := .subst (.fvar "B") (.fvar "A")

def lambdaCalculus : LanguageDef := { LanguageDef.empty "lambda" with rewrites := [beta] }

/-- **Positive**: β compiles; its right side instantiates the bound index of the body with the argument. -/
theorem beta_compiles : (clausesOf lambdaCalculus []).isOk = true := by decide

/-- **Positive**: the compiled program steps `(λ. f 0) c` to `f c`. -/
theorem beta_steps : ∃ program, clausesOf lambdaCalculus [] = .ok program ∧
    Derives (premiseRelations RelationEnv.empty lambdaCalculus) program stepRelation
      (encode (.apply "app" [.lambda none (.apply "f" [.bvar 0]), .apply "c" []]))
      (encode (.apply "f" [.apply "c" []])) := by
  obtain ⟨program, computed⟩ : ∃ program, clausesOf lambdaCalculus [] = .ok program := ⟨_, rfl⟩
  refine ⟨program, computed, (derives_step_iff (empty_dataRows _) (clausesOf_spec computed).1
    (by decide)).mpr ⟨_, rfl, .rule 0 [("A", .apply "c" []), ("B", .apply "f" [.bvar 0])] [], ?_⟩⟩
  exact (Mettapedia.OSLF.MeTTaIL.ReferenceStep.checkStep_eq_some_iff RelationEnv.empty lambdaCalculus _).mp
    (by decide +kernel)

/-- **Negative**: the compiled program does not step an application whose function is not an abstraction. -/
theorem beta_needs_abstraction {program : List Clause} (computed : clausesOf lambdaCalculus [] = .ok program)
    (w : Expr) : ¬ Derives (premiseRelations RelationEnv.empty lambdaCalculus) program stepRelation
      (encode (.apply "app" [.apply "c" [], .apply "c" []])) w := by
  intro derived
  obtain ⟨t, -, step⟩ := (derives_step_iff (empty_dataRows _) (clausesOf_spec computed).1
    (by decide)).mp derived
  obtain ⟨rule, member, initial, final, witnesses, matched, -, -⟩ := StepPremises.step_iff.mp step
  have isBeta : rule = beta := by simpa [lambdaCalculus] using member
  subst isBeta
  have unmatched : matchPattern beta.left (.apply "app" [.apply "c" [], .apply "c" []]) = [] := by decide +kernel
  exact absurd (matchPattern_iff_matchRel.mpr matched) (by rw [unmatched]; exact List.not_mem_nil)

/-- Weakening: a term under a new binder it does not use, the binder named. -/
def weaken : RewriteRule where
  name := "weaken"
  typeContext := []
  premises := []
  left := .apply "w" [.fvar "X"]
  right := .lambda (some "x") (.fvar "X")

def weakening : LanguageDef := { LanguageDef.empty "weakening" with rewrites := [weaken] }

/-- **Negative**: the clauses of a rule whose right side names its binder are refused by the rule's name: the name
is display metadata, which the canonical carrier does not hold. -/
theorem weakening_named_refused : clausesOf weakening [] = .error (.binderNames "weaken") :=
  eq_error_of_refusalOf (by decide)

/-- The canonical presentation of weakening: its binder carries no name. -/
theorem weakening_canonical : weakening.eraseBinderMetadata =
    { LanguageDef.empty "weakening" with rewrites := [{ weaken with right := .lambda none (.fvar "X") }] } := by
  simp [weakening, weaken, LanguageDef.eraseBinderMetadata, RewriteRule.eraseBinderMetadata,
    Pattern.eraseBinderMetadata, LanguageDef.empty]

/-- **Positive**: the compiler compiles the canonical presentation, where the binder carries no name. -/
theorem weakening_compiles : (compile weakening []).isOk = true := by
  rw [compile_eq, weakening_canonical]
  decide

/-- η: an abstraction applying a term to its bound index is the term. -/
def eta : Equation where
  name := "eta"
  typeContext := []
  premises := []
  left := .lambda none (.apply "app" [.fvar "f", .bvar 0])
  right := .fvar "f"

def etaLanguage : LanguageDef := { LanguageDef.empty "eta" with equations := [eta] }

/-- **Positive**: η compiles: its left side holds a binder, and each orientation instantiates the other side
scope-correctly. -/
theorem eta_compiles : (clausesOf etaLanguage []).isOk = true := by decide

/-- **Positive**: the compiled program relates `λ. c 0` to `c` by one equation step. -/
theorem eta_steps : ∃ program, clausesOf etaLanguage [] = .ok program ∧
    Derives (premiseRelations RelationEnv.empty etaLanguage) program equationRelation
      (encode (.lambda none (.apply "app" [.apply "c" [], .bvar 0]))) (encode (.apply "c" [])) := by
  obtain ⟨program, computed⟩ : ∃ program, clausesOf etaLanguage [] = .ok program := ⟨_, rfl⟩
  obtain ⟨rules, equations, dataClauses, -⟩ := clausesOf_spec computed
  refine ⟨program, computed, (derives_equation_iff (empty_dataRows _) rules equations dataClauses
    (by decide)).mpr ⟨_, rfl, by decide, .inl ?_⟩⟩
  have generator := AuthoredEquation.forward (relEnv := RelationEnv.empty) (language := etaLanguage)
    (equation := eta) (source := .lambda none (.apply "app" [.apply "c" [], .bvar 0]))
    (initial := [("f", .apply "c" [])]) (final := [("f", .apply "c" [])]) (witnesses := [])
    (by simp [etaLanguage]) (by decide) (by decide +kernel) (.nil _)
  have target : applyBindingsScoped (captureSitesOf eta.left eta.premises) [("f", .apply "c" [])] 0 eta.right =
      .apply "c" [] := by decide +kernel
  rw [target] at generator
  exact .inContext .hole (.inl generator)

/-- Wrapping a term under a binder it does not use. -/
def wrapUnder : Equation where
  name := "wrapUnder"
  typeContext := []
  premises := []
  left := .apply "wrap" [.fvar "X"]
  right := .lambda none (.apply "pair" [.fvar "X", .bvar 0])

def wrapping : LanguageDef := { LanguageDef.empty "wrapping" with equations := [wrapUnder] }

theorem wrapping_compiles : (clausesOf wrapping []).isOk = true := by decide

/-- **Positive**: the compiled program reads the instance `λ. pair(1, 0)` back to `wrap(0)`: the converse lowers the
index that the instance lifted. -/
theorem wrapping_lowers : ∃ program, clausesOf wrapping [] = .ok program ∧
    Derives (premiseRelations RelationEnv.empty wrapping) program equationRelation
      (encode (.lambda none (.apply "pair" [.bvar 1, .bvar 0]))) (encode (.apply "wrap" [.bvar 0])) := by
  obtain ⟨program, computed⟩ : ∃ program, clausesOf wrapping [] = .ok program := ⟨_, rfl⟩
  obtain ⟨rules, equations, dataClauses, -⟩ := clausesOf_spec computed
  refine ⟨program, computed, (derives_equation_iff (empty_dataRows _) rules equations dataClauses
    (by decide)).mpr ⟨_, rfl, by decide, .inr ⟨.hole, .lambda none (.apply "pair" [.bvar 1, .bvar 0]),
      .apply "wrap" [.bvar 0], rfl, rfl, .inl ⟨wrapUnder, by simp [wrapping], by decide,
        .inl ⟨[("X", .bvar 0)], [("X", .bvar 0)], [], matchPattern_sound (by decide +kernel), .nil _,
          by decide +kernel, ?_, ?_⟩⟩⟩⟩⟩
  · have noneFree : freeNames wrapUnder.left wrapUnder.right = [] := by decide
    intro name free
    rw [noneFree] at free
    exact absurd free List.not_mem_nil
  · intro v inside
    simp [wrapUnder, Instantiation.substValues, Instantiation.substValuesList] at inside

/-- β as an equation: an application of an abstraction is its body with the argument for its bound index. -/
def betaEquation : Equation where
  name := "betaEquation"
  typeContext := []
  premises := []
  left := .apply "app" [.lambda none (.fvar "B"), .fvar "A"]
  right := .subst (.fvar "B") (.fvar "A")

def betaEquational : LanguageDef := { LanguageDef.empty "betaEquational" with equations := [betaEquation] }

/-- **Positive**: β as an equation, whose right side is an explicit substitution, compiles: taken back, the equation
chooses the substituted value over the supply and abstracts the instance over it. -/
theorem betaEquation_compiles : (clausesOf betaEquational []).isOk = true := by decide

/-- **Positive**: over the supply `a`, the compiled program relates `pair(a, a)` to `app(λ. pair(0, 0), a)`: taken back,
β chooses `a` for the substituted value and abstracts both of its occurrences. -/
theorem beta_expands : ∃ program, clausesOf betaEquational ["a"] = .ok program ∧
    Derives (premiseRelations RelationEnv.empty betaEquational) program equationRelation
      (encode (.apply "pair" [.apply "a" [], .apply "a" []]))
      (encode (.apply "app" [.lambda none (.apply "pair" [.bvar 0, .bvar 0]), .apply "a" []])) := by
  obtain ⟨program, computed⟩ : ∃ program, clausesOf betaEquational ["a"] = .ok program := ⟨_, rfl⟩
  obtain ⟨rules, equations, dataClauses, -⟩ := clausesOf_spec computed
  refine ⟨program, computed, (derives_equation_iff (empty_dataRows _) rules equations dataClauses
    (by decide)).mpr ⟨_, rfl, by decide, .inr ⟨.hole, .apply "pair" [.apply "a" [], .apply "a" []],
      .apply "app" [.lambda none (.apply "pair" [.bvar 0, .bvar 0]), .apply "a" []], rfl, rfl,
      .inl ⟨betaEquation, by simp [betaEquational], by decide,
        .inl ⟨[("A", .apply "a" []), ("B", .apply "pair" [.bvar 0, .bvar 0])],
          [("A", .apply "a" []), ("B", .apply "pair" [.bvar 0, .bvar 0])], [],
          matchPattern_sound (by decide +kernel), .nil _, by decide +kernel, ?_, ?_⟩⟩⟩⟩⟩
  · have noneFree : freeNames betaEquation.left betaEquation.right = [] := by decide
    intro name free
    rw [noneFree] at free
    exact absurd free List.not_mem_nil
  · have values : Instantiation.substValues (captureSitesOf betaEquation.left betaEquation.premises)
        [("A", .apply "a" []), ("B", .apply "pair" [.bvar 0, .bvar 0])] 0 betaEquation.right =
        [.apply "a" []] := by decide +kernel
    intro v inside label member
    rw [values, List.mem_singleton] at inside
    subst inside
    simpa [DataClauses.labelsOf, DataClauses.labelsOfList] using member

theorem hole_of_fill_heads {context : OneHoleContext} {redex contractum : Pattern} {f g : String}
    {fs gs : List Pattern} (different : f ≠ g) (source : context.fill redex = .apply f fs)
    (target : context.fill contractum = .apply g gs) : context = .hole := by
  cases context <;> simp_all [OneHoleContext.fill]

/-- **Negative**: over the supply `b`, the compiled program does not relate `pair(a, a)` to `app(λ. pair(0, 0), a)`:
the substituted value `a` is no datum over the supply, and no other generator relates the two. -/
theorem beta_needs_the_supply {program : List Clause} (computed : clausesOf betaEquational ["b"] = .ok program) :
    ¬ Derives (premiseRelations RelationEnv.empty betaEquational) program equationRelation
      (encode (.apply "pair" [.apply "a" [], .apply "a" []]))
      (encode (.apply "app" [.lambda none (.apply "pair" [.bvar 0, .bvar 0]), .apply "a" []])) := by
  intro derived
  obtain ⟨rules, equations, dataClauses, -⟩ := clausesOf_spec computed
  obtain ⟨t, same, -, step⟩ := (derives_equation_iff (empty_dataRows _) rules equations dataClauses
    (by decide)).mp derived
  obtain rfl := RootRewritesOnTheStep.encode_injective same
  have noLaws : ∀ s t, ¬ DerivedInstance betaEquational s t :=
    no_derivedInstance_of_no_derived_laws (by decide) (by decide) (by decide)
  rcases step with forward | back
  · obtain ⟨context, redex, contractum, generator, sourceIs, targetIs⟩ := equationStep_cases forward
    obtain rfl := hole_of_fill_heads (by decide) sourceIs.symm targetIs.symm
    simp only [OneHoleContext.fill] at sourceIs targetIs
    rcases generator with authored | derived
    · cases authored with
      | forward member raw matched passed =>
          simp only [betaEquational, LanguageDef.empty, List.mem_singleton] at member
          subst member
          rw [← sourceIs] at matched
          have unmatched : matchPattern betaEquation.left (.apply "pair" [.apply "a" [], .apply "a" []]) = [] := by
            decide +kernel
          rw [unmatched] at matched
          exact absurd matched List.not_mem_nil
      | reverse member raw matched passed =>
          simp only [betaEquational, LanguageDef.empty, List.mem_singleton] at member
          subst member
          rw [← sourceIs] at matched
          have unmatched : matchPattern betaEquation.right (.apply "pair" [.apply "a" [], .apply "a" []]) = [] := by
            decide +kernel
          rw [unmatched] at matched
          exact absurd matched List.not_mem_nil
      | declared member notRaw _ =>
          simp only [betaEquational, LanguageDef.empty, List.mem_singleton] at member
          subst member
          exact absurd notRaw (by decide)
      | premised member notRaw _ _ =>
          simp only [betaEquational, LanguageDef.empty, List.mem_singleton] at member
          subst member
          exact absurd notRaw (by decide)
    · exact noLaws _ _ derived
  · obtain ⟨context, origin, target, originIs, targetIs, generator⟩ := back
    obtain rfl := hole_of_fill_heads (by decide) originIs.symm targetIs.symm
    simp only [OneHoleContext.fill] at originIs targetIs
    subst originIs targetIs
    rcases generator with ⟨e, member, -, within | within⟩ | derived
    · simp only [betaEquational, LanguageDef.empty, List.mem_singleton] at member
      subst member
      obtain ⟨initial, final, witnesses, matched, passed, -, -, substituted⟩ := within
      have found := matchPattern_iff_matchRel.mpr matched
      have only_ : matchPattern betaEquation.left
          (.apply "app" [.lambda none (.apply "pair" [.bvar 0, .bvar 0]), .apply "a" []]) =
          [[("A", .apply "a" []), ("B", .apply "pair" [.bvar 0, .bvar 0])]] := by decide +kernel
      rw [only_, List.mem_singleton] at found
      subst found
      cases passed
      have values : Instantiation.substValues (captureSitesOf betaEquation.left betaEquation.premises)
          [("A", .apply "a" []), ("B", .apply "pair" [.bvar 0, .bvar 0])] 0 betaEquation.right =
          [.apply "a" []] := by decide +kernel
      have chosen := substituted (.apply "a" []) (by rw [values]; exact List.mem_singleton_self _) "a"
        (by decide +kernel)
      exact absurd chosen (by decide)
    · simp only [betaEquational, LanguageDef.empty, List.mem_singleton] at member
      subst member
      obtain ⟨initial, final, witnesses, matched, -, -, -, -⟩ := within
      have found := matchPattern_iff_matchRel.mpr matched
      have unmatched : matchPattern betaEquation.right
          (.apply "app" [.lambda none (.apply "pair" [.bvar 0, .bvar 0]), .apply "a" []]) = [] := by
        decide +kernel
      rw [unmatched] at found
      exact absurd found List.not_mem_nil
    · exact noLaws _ _ derived

/-- A part `a` steps to `b`. -/
def partStep : RewriteRule where
  name := "part"
  typeContext := []
  premises := []
  left := .apply "a" []
  right := .apply "b" []

/-- A whole steps when every part of it steps. -/
def everyPart : RewriteRule where
  name := "every"
  typeContext := []
  premises := [.forAll "xs" "x" (.congruence (.fvar "x") (.fvar "y"))]
  left := .apply "all" [.fvar "xs"]
  right := .apply "done" []

/-- A grid steps when every cell of every row steps: one quantified premise inside another. -/
def everyCell : RewriteRule where
  name := "cells"
  typeContext := []
  premises := [.forAll "rows" "row" (.forAll "row" "x" (.congruence (.fvar "x") (.fvar "y")))]
  left := .apply "grid" [.fvar "rows"]
  right := .apply "done" []

/-- A spread steps when every element after its head steps: a quantified premise over a rest. -/
def everyRest : RewriteRule where
  name := "rest"
  typeContext := []
  premises := [.forAll "t" "x" (.congruence (.fvar "x") (.fvar "y"))]
  left := .apply "spread" [.collection .vec [.fvar "h"] (some "t")]
  right := .apply "done" []

def quantifiers : LanguageDef :=
  { LanguageDef.empty "quantifiers" with rewrites := [partStep, everyPart, everyCell, everyRest] }

/-- **Positive**: rules with quantified premises compile: over a bound collection, nested, and over a rest. -/
theorem quantifiers_compile : (clausesOf quantifiers []).isOk = true := by decide

/-- The evidence that the part `a` steps to `b`, at bindings where the parameter `x` is bound to it. -/
def partWitness (bindings : Bindings) : Witness :=
  .premiseStep (.rule 0 [] []) (.apply "b" []) [("y", .apply "b" [])]
    ((mergeBindings (Mettapedia.OSLF.MeTTaIL.ReferenceStep.bindParameter bindings "x" (.apply "a" []))
      [("y", .apply "b" [])]).getD [])

/-- A collection of parts `a`. -/
def partsOf (count : ℕ) : Pattern := .collection .vec (List.replicate count (.apply "a" [])) none

/-- **Positive**: the compiled program steps a whole whose every part steps. -/
theorem everyPart_steps : ∃ program, clausesOf quantifiers [] = .ok program ∧
    Derives (premiseRelations RelationEnv.empty quantifiers) program stepRelation
      (encode (.apply "all" [partsOf 2])) (encode (.apply "done" [])) := by
  obtain ⟨program, computed⟩ : ∃ program, clausesOf quantifiers [] = .ok program := ⟨_, rfl⟩
  refine ⟨program, computed, (derives_step_iff (empty_dataRows _) (clausesOf_spec computed).1
    (by decide)).mpr ⟨_, rfl, .rule 1 [("xs", partsOf 2)]
      [.forAll [partWitness [("xs", partsOf 2)], partWitness [("xs", partsOf 2)]]], ?_⟩⟩
  exact (Mettapedia.OSLF.MeTTaIL.ReferenceStep.checkStep_eq_some_iff RelationEnv.empty quantifiers _).mp
    (by decide +kernel)

/-- The bindings of a grid's rows. -/
def gridBindings : Bindings := [("rows", .collection .vec [partsOf 1, partsOf 2] none)]

/-- **Positive**: the compiled program steps a grid whose every cell steps. -/
theorem everyCell_steps : ∃ program, clausesOf quantifiers [] = .ok program ∧
    Derives (premiseRelations RelationEnv.empty quantifiers) program stepRelation
      (encode (.apply "grid" [.collection .vec [partsOf 1, partsOf 2] none])) (encode (.apply "done" [])) := by
  obtain ⟨program, computed⟩ : ∃ program, clausesOf quantifiers [] = .ok program := ⟨_, rfl⟩
  refine ⟨program, computed, (derives_step_iff (empty_dataRows _) (clausesOf_spec computed).1
    (by decide)).mpr ⟨_, rfl, .rule 2 gridBindings
      [.forAll [.forAll [partWitness (Mettapedia.OSLF.MeTTaIL.ReferenceStep.bindParameter gridBindings "row"
          (partsOf 1))],
        .forAll [partWitness (Mettapedia.OSLF.MeTTaIL.ReferenceStep.bindParameter gridBindings "row" (partsOf 2)),
          partWitness (Mettapedia.OSLF.MeTTaIL.ReferenceStep.bindParameter gridBindings "row" (partsOf 2))]]], ?_⟩⟩
  exact (Mettapedia.OSLF.MeTTaIL.ReferenceStep.checkStep_eq_some_iff RelationEnv.empty quantifiers _).mp
    (by decide +kernel)

/-- **Positive**: the compiled program steps a spread whose elements after its head step; its head need not. -/
theorem everyRest_steps : ∃ program, clausesOf quantifiers [] = .ok program ∧
    Derives (premiseRelations RelationEnv.empty quantifiers) program stepRelation
      (encode (.apply "spread" [.collection .vec [.apply "c" [], .apply "a" [], .apply "a" []] none]))
      (encode (.apply "done" [])) := by
  obtain ⟨program, computed⟩ : ∃ program, clausesOf quantifiers [] = .ok program := ⟨_, rfl⟩
  refine ⟨program, computed, (derives_step_iff (empty_dataRows _) (clausesOf_spec computed).1
    (by decide)).mpr ⟨_, rfl, .rule 3 [("t", partsOf 2), ("h", .apply "c" [])]
      [.forAll [partWitness [("t", partsOf 2), ("h", .apply "c" [])],
        partWitness [("t", partsOf 2), ("h", .apply "c" [])]]], ?_⟩⟩
  exact (Mettapedia.OSLF.MeTTaIL.ReferenceStep.checkStep_eq_some_iff RelationEnv.empty quantifiers _).mp
    (by decide +kernel)

/-- **Negative**: the compiled program does not step a whole with a part that does not step. -/
theorem everyPart_needs_every {program : List Clause} (computed : clausesOf quantifiers [] = .ok program)
    (w : Expr) : ¬ Derives (premiseRelations RelationEnv.empty quantifiers) program stepRelation
      (encode (.apply "all" [.collection .vec [.apply "a" [], .apply "c" []] none])) w := by
  intro derived
  obtain ⟨t, -, step⟩ := (derives_step_iff (empty_dataRows _) (clausesOf_spec computed).1
    (by decide)).mp derived
  have stuck : ∀ t, ¬ Step RelationEnv.empty quantifiers (.apply "c" []) t := by
    intro t stepped
    obtain ⟨rule, member, initial, final, witnesses, matched, -, -⟩ := StepPremises.step_iff.mp stepped
    have unmatched : ∀ rule ∈ quantifiers.rewrites, matchPattern rule.left (.apply "c" []) = [] := by
      decide +kernel
    exact absurd (matchPattern_iff_matchRel.mpr matched) (by rw [unmatched rule member]; exact List.not_mem_nil)
  obtain ⟨rule, member, initial, final, witnesses, matched, passed, -⟩ := StepPremises.step_iff.mp step
  have found := matchPattern_iff_matchRel.mpr matched
  simp only [quantifiers, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · have unmatched : matchPattern partStep.left
        (.apply "all" [.collection .vec [.apply "a" [], .apply "c" []] none]) = [] := by decide +kernel
    rw [unmatched] at found
    exact absurd found List.not_mem_nil
  · have matches_ : matchPattern everyPart.left (.apply "all" [.collection .vec [.apply "a" [], .apply "c" []] none]) =
        [[("xs", .collection .vec [.apply "a" [], .apply "c" []] none)]] := by decide +kernel
    rw [matches_, List.mem_singleton] at found
    subst found
    cases passed with
    | cons here _ =>
      obtain ⟨-, bodies, kind, elements, -, looked, forAllValid⟩ := StepPremises.premiseValid_forAll here
      simp [Bindings.lookup] at looked
      obtain ⟨-, elementsIs⟩ := looked
      obtain ⟨bodyWitness, -, result, bodyValid⟩ :=
        StepPremises.forAllValid_mem forAllValid (.apply "c" []) (by rw [← elementsIs]; simp)
      obtain ⟨stepWitness, candidate, -, -, stepped, -, -⟩ := StepPremises.premiseValid_step rfl bodyValid
      have sourceIs : applyBindingsScoped (captureSitesOf everyPart.left everyPart.premises)
          (Mettapedia.OSLF.MeTTaIL.ReferenceStep.bindParameter
            [("xs", .collection .vec [.apply "a" [], .apply "c" []] none)] "x" (.apply "c" []))
          (stepDepth (captureSitesOf everyPart.left everyPart.premises)
            (.congruence (.fvar "x") (.fvar "y"))) (.fvar "x") = .apply "c" [] := by decide +kernel
      exact stuck candidate ⟨stepWitness, sourceIs ▸ stepped⟩
  · have unmatched : matchPattern everyCell.left
        (.apply "all" [.collection .vec [.apply "a" [], .apply "c" []] none]) = [] := by decide +kernel
    rw [unmatched] at found
    exact absurd found List.not_mem_nil
  · have unmatched : matchPattern everyRest.left
        (.apply "all" [.collection .vec [.apply "a" [], .apply "c" []] none]) = [] := by decide +kernel
    rw [unmatched] at found
    exact absurd found List.not_mem_nil

/-- A spread steps when every element after its head steps; the parameter has the name of the rest it ranges over and
shadows it in the body, as the source binds a parameter. -/
def shadowRest : RewriteRule where
  name := "shadow"
  typeContext := []
  premises := [.forAll "t" "t" (.congruence (.fvar "t") (.fvar "y"))]
  left := .apply "spread" [.collection .vec [.fvar "h"] (some "t")]
  right := .apply "done" []

def shadowing : LanguageDef := { LanguageDef.empty "shadowing" with rewrites := [partStep, shadowRest] }

/-- **Positive**: a quantified premise whose parameter has the name of a rest of the left side compiles. -/
theorem shadowing_compiles : (clausesOf shadowing []).isOk = true := by decide

/-- The witness that an element `a`, bound to the parameter `t`, steps to `b`. -/
def shadowWitness (bindings : Bindings) : Witness :=
  .premiseStep (.rule 0 [] []) (.apply "b" []) [("y", .apply "b" [])]
    ((mergeBindings (Mettapedia.OSLF.MeTTaIL.ReferenceStep.bindParameter bindings "t" (.apply "a" []))
      [("y", .apply "b" [])]).getD [])

/-- **Positive**: the compiled program steps `spread([c, a, a])` to `done`: in the body, `t` is each element, not the
rest, whose list would not step. -/
theorem shadowRest_steps : ∃ program, clausesOf shadowing [] = .ok program ∧
    Derives (premiseRelations RelationEnv.empty shadowing) program stepRelation
      (encode (.apply "spread" [.collection .vec [.apply "c" [], .apply "a" [], .apply "a" []] none]))
      (encode (.apply "done" [])) := by
  obtain ⟨program, computed⟩ : ∃ program, clausesOf shadowing [] = .ok program := ⟨_, rfl⟩
  refine ⟨program, computed, (derives_step_iff (empty_dataRows _) (clausesOf_spec computed).1
    (by decide)).mpr ⟨_, rfl, .rule 1 [("t", partsOf 2), ("h", .apply "c" [])]
      [.forAll [shadowWitness [("t", partsOf 2), ("h", .apply "c" [])],
        shadowWitness [("t", partsOf 2), ("h", .apply "c" [])]]], ?_⟩⟩
  exact (Mettapedia.OSLF.MeTTaIL.ReferenceStep.checkStep_eq_some_iff RelationEnv.empty shadowing _).mp
    (by decide +kernel)

/-- **Negative**: the compiled program does not step `spread([c, a, c])`: the element `c` does not step. -/
theorem shadowRest_needs_every {program : List Clause} (computed : clausesOf shadowing [] = .ok program)
    (w : Expr) : ¬ Derives (premiseRelations RelationEnv.empty shadowing) program stepRelation
      (encode (.apply "spread" [.collection .vec [.apply "c" [], .apply "a" [], .apply "c" []] none])) w := by
  intro derived
  obtain ⟨t, -, step⟩ := (derives_step_iff (empty_dataRows _) (clausesOf_spec computed).1
    (by decide)).mp derived
  have stuck : ∀ t, ¬ Step RelationEnv.empty shadowing (.apply "c" []) t := by
    intro t stepped
    obtain ⟨rule, member, initial, final, witnesses, matched, -, -⟩ := StepPremises.step_iff.mp stepped
    have unmatched : ∀ rule ∈ shadowing.rewrites, matchPattern rule.left (.apply "c" []) = [] := by
      decide +kernel
    exact absurd (matchPattern_iff_matchRel.mpr matched) (by rw [unmatched rule member]; exact List.not_mem_nil)
  obtain ⟨rule, member, initial, final, witnesses, matched, passed, -⟩ := StepPremises.step_iff.mp step
  have found := matchPattern_iff_matchRel.mpr matched
  simp only [shadowing, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · have unmatched : matchPattern partStep.left
        (.apply "spread" [.collection .vec [.apply "c" [], .apply "a" [], .apply "c" []] none]) = [] := by
      decide +kernel
    rw [unmatched] at found
    exact absurd found List.not_mem_nil
  · have matches_ : matchPattern shadowRest.left
        (.apply "spread" [.collection .vec [.apply "c" [], .apply "a" [], .apply "c" []] none]) =
        [[("t", .collection .vec [.apply "a" [], .apply "c" []] none), ("h", .apply "c" [])]] := by
      decide +kernel
    rw [matches_, List.mem_singleton] at found
    subst found
    cases passed with
    | cons here _ =>
      obtain ⟨-, bodies, kind, elements, -, looked, forAllValid⟩ := StepPremises.premiseValid_forAll here
      simp [Bindings.lookup] at looked
      obtain ⟨-, elementsIs⟩ := looked
      obtain ⟨bodyWitness, -, result, bodyValid⟩ :=
        StepPremises.forAllValid_mem forAllValid (.apply "c" []) (by rw [← elementsIs]; simp)
      obtain ⟨stepWitness, candidate, -, -, stepped, -, -⟩ := StepPremises.premiseValid_step rfl bodyValid
      have sourceIs : applyBindingsScoped (captureSitesOf shadowRest.left shadowRest.premises)
          (Mettapedia.OSLF.MeTTaIL.ReferenceStep.bindParameter
            [("t", .collection .vec [.apply "a" [], .apply "c" []] none), ("h", .apply "c" [])] "t"
            (.apply "c" []))
          (stepDepth (captureSitesOf shadowRest.left shadowRest.premises)
            (.congruence (.fvar "t") (.fvar "y"))) (.fvar "t") = .apply "c" [] := by decide +kernel
      exact stuck candidate ⟨stepWitness, sourceIs ▸ stepped⟩

/-- A quantified premise over a collection no name of the rule binds. -/
def everyUnbound : RewriteRule where
  name := "unboundAll"
  typeContext := []
  premises := [.forAll "ys" "x" (.congruence (.fvar "x") (.fvar "y"))]
  left := .apply "all" [.fvar "xs"]
  right := .apply "done" []

def unboundQuantifier : LanguageDef := { LanguageDef.empty "unbound" with rewrites := [everyUnbound] }

/-- **Positive**: a rule whose quantified premise ranges over a collection nothing binds compiles. -/
theorem unboundQuantifier_compiles : (clausesOf unboundQuantifier []).isOk = true := by decide

/-- **Negative**: the collection is the name itself, which is no collection, so the rule never fires. -/
theorem everyUnbound_never_fires {program : List Clause} (computed : clausesOf unboundQuantifier [] = .ok program)
    (items : List Pattern) (w : Expr) :
    ¬ Derives (premiseRelations RelationEnv.empty unboundQuantifier) program stepRelation
      (encode (.apply "all" [.collection .vec items none])) w := by
  intro derived
  obtain ⟨depth, derivedAt⟩ := derived
  obtain ⟨t, -, step⟩ := step_of_derivesAt (clausesOf_spec computed).1 depth derivedAt
  obtain ⟨rule, member, initial, final, witnesses, matched, passed, -⟩ := StepPremises.step_iff.mp step
  simp only [unboundQuantifier, List.mem_singleton] at member
  subst member
  have keys := (MatchesAndInstances.match_functional everyUnbound.left matched).2
  cases passed with
  | cons here _ =>
    obtain ⟨-, bodies, kind, elements, -, looked, -⟩ := StepPremises.premiseValid_forAll here
    obtain ⟨⟨key, value⟩, found, same⟩ := Option.map_eq_some_iff.mp looked
    have named : key = "ys" := by simpa using List.find?_some found
    subst named
    have inLeft := keys "ys" value (List.mem_of_find?_eq_some found)
    exact absurd inLeft (by decide)

open Mettapedia.GSLT.LanguageDef.WellSorted (HasType CollectionTypedAt FreeTypeContext)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (AlgebraRule SortedAt)

/-- A constructor with no parameters. -/
def constant (label category : String) : GrammarRule := { label, category, params := [], syntaxPattern := [] }

theorem constant_typed {language : LanguageDef} {label category : String}
    (member : constant label category ∈ language.terms) :
    HasType language FreeTypeContext.empty [] (.apply label []) (.base category) :=
  .constructor (rule := constant label category) member
    (by rintro ⟨_, _, _, shape⟩; simp [constant, GrammarRule.bareParams] at shape) .nil

/-- A soup: a bag of molecules. -/
def soupRule : GrammarRule :=
  { label := "soup", category := "Soup", params := [.simple "ms" (.collection .hashBag (.base "Mol"))],
    syntaxPattern := [] }

def souping : LanguageDef :=
  { LanguageDef.empty "souping" with terms := [constant "a" "Mol", constant "b" "Mol", soupRule] }

/-- **Positive**: a language with a bag carrier compiles. -/
theorem souping_compiles : (clausesOf souping []).isOk = true := by decide

/-- **Positive**: the compiled program relates a soup to its reordering by one equation step. -/
theorem souping_reorders (relEnv : RelationEnv) : ∃ program, clausesOf souping [] = .ok program ∧
    Derives (premiseRelations relEnv souping) program equationRelation
      (encode (.collection .hashBag [.apply "a" [], .apply "b" []] none))
      (encode (.collection .hashBag [.apply "b" [], .apply "a" []] none)) := by
  obtain ⟨program, computed⟩ : ∃ program, clausesOf souping [] = .ok program := ⟨_, rfl⟩
  have equations := (clausesOf_spec computed).2.1
  have notFree : souping.isEquationFree = false := by decide
  have typed : CollectionTypedAt souping soupRule .hashBag [.apply "a" [], .apply "b" []] :=
    ⟨.simple "ms" (.collection .hashBag (.base "Mol")), by simp [soupRule], .base "Mol", .here,
      FreeTypeContext.empty, [], .collection (.cons (constant_typed (by simp [souping]))
        (.cons (constant_typed (by simp [souping])) (.nil _ _)))⟩
  exact ⟨program, computed, lawStep_complete equations notFree (CollectionLaws.law_forward
    (equations.laws notFree _ (premiseRelations_names relEnv souping))
    (.bagPerm (by simp [souping]) typed (.swap _ _ _)))⟩

/-- No rule of the soup declares an algebra. -/
theorem souping_no_algebra {rule : GrammarRule} {kind : CollType} {algebra : CollectionAlgebra} :
    ¬ AlgebraRule souping rule kind algebra := by
  rintro ⟨member, declared, -, -⟩
  simp only [souping, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp [constant, soupRule] at declared

/-- A bag holding a term the grammar does not declare has no collection type. -/
theorem stray_untyped {elements : List Pattern} (stray : .apply "z" [] ∈ elements) (rule : GrammarRule) :
    ¬ CollectionTypedAt souping rule .hashBag elements := by
  rintro ⟨parameter, -, element, -, free, bound, typed⟩
  cases typed with
  | collection elementsTyped =>
      have zTyped := CollectionLaws.elementsHaveType_iff.mp elementsTyped _ stray
      generalize zIs : Pattern.apply "z" [] = z at zTyped
      cases zTyped
      all_goals first
        | (simp at zIs; done)
        | (obtain ⟨labelIs, -⟩ := Pattern.apply.inj zIs
           have member := ‹_ ∈ souping.terms›
           simp only [souping, List.mem_cons, List.not_mem_nil, or_false] at member
           rcases member with rfl | rfl | rfl <;> simp [constant, soupRule] at labelIs)

theorem stray_no_law {elements : List Pattern} (stray : .apply "z" [] ∈ elements) (t : Pattern) :
    ¬ DerivedInstance souping (.collection .hashBag elements none) t := by
  intro derived
  generalize sourceIs : Pattern.collection .hashBag elements none = s at derived
  cases derived with
  | bagPerm _ typed _ =>
      simp only [Pattern.collection.injEq, true_and, and_true] at sourceIs
      subst sourceIs
      exact stray_untyped stray _ typed
  | setPerm => simp at sourceIs
  | setDedup => simp at sourceIs
  | flatten algebraRule => exact souping_no_algebra algebraRule
  | singleton algebraRule => exact souping_no_algebra algebraRule
  | unitElim algebraRule => exact souping_no_algebra algebraRule
  | emptyUnit algebraRule => exact souping_no_algebra algebraRule

/-- **Negative**: a bag holding a term the grammar does not declare is not reordered, in either direction: its
elements have no common type, so no law relates it. -/
theorem stray_kept (relEnv : RelationEnv) {program : List Clause} (computed : clausesOf souping [] = .ok program) :
    ¬ Derives (premiseRelations relEnv souping) program lawRelation
      (encode (.collection .hashBag [.apply "a" [], .apply "z" []] none))
      (encode (.collection .hashBag [.apply "z" [], .apply "a" []] none)) := by
  have equations := (clausesOf_spec computed).2.1
  have notFree : souping.isEquationFree = false := by decide
  intro derived
  obtain ⟨t, same, related⟩ := (CollectionLaws.derives_law_iff
    (equations.laws notFree _ (premiseRelations_names relEnv souping))).mp derived
  obtain rfl := RootRewritesOnTheStep.encode_injective same
  rcases related with forward | backward
  · exact stray_no_law (by simp) _ forward
  · exact stray_no_law (by simp) _ backward

/-- A parallel composition: a bag of processes, which flattens and absorbs its unit. -/
def parRule : GrammarRule :=
  { label := "par", category := "Proc", params := [.simple "ps" (.collection .hashBag (.base "Proc"))],
    syntaxPattern := [], algebra? := some { flatten := true, unit := some "zero" } }

def parallel : LanguageDef :=
  { LanguageDef.empty "parallel" with terms := [constant "zero" "Proc", constant "out" "Proc", parRule] }

/-- **Positive**: the compiled program absorbs the unit of a parallel composition by one equation step. -/
theorem parallel_absorbs (relEnv : RelationEnv) : ∃ program, clausesOf parallel [] = .ok program ∧
    Derives (premiseRelations relEnv parallel) program equationRelation
      (encode (.collection .hashBag [.apply "zero" [], .apply "out" []] none))
      (encode (.collection .hashBag [.apply "out" []] none)) := by
  obtain ⟨program, computed⟩ : ∃ program, clausesOf parallel [] = .ok program := ⟨_, rfl⟩
  have equations := (clausesOf_spec computed).2.1
  have notFree : parallel.isEquationFree = false := by decide
  have algebraRule : AlgebraRule parallel parRule .hashBag { flatten := true, unit := some "zero" } :=
    ⟨by simp [parallel], rfl, ⟨"ps", rfl⟩, fun unit unitIs =>
      ⟨constant "zero" "Proc", by simp [parallel], Option.some.inj unitIs, rfl, rfl⟩⟩
  have sorted : SortedAt parallel (.collection .hashBag [.apply "zero" [], .apply "out" []] none) "Proc" :=
    ⟨FreeTypeContext.empty, [], .collectionConstructor (rule := parRule) (by simp [parallel]) rfl
      (.cons (constant_typed (by simp [parallel])) (.cons (constant_typed (by simp [parallel])) (.nil _ _)))⟩
  exact ⟨program, computed, lawStep_complete equations notFree (CollectionLaws.law_forward
    (equations.laws notFree _ (premiseRelations_names relEnv parallel))
    (.unitElim (pre := []) (post := [.apply "out" []]) algebraRule rfl sorted))⟩

/-- An algebra declared on a collection of another category. -/
def mixedRule : GrammarRule :=
  { label := "mixed", category := "Proc", params := [.simple "ms" (.collection .hashBag (.base "Mol"))],
    syntaxPattern := [], algebra? := some { flatten := true, unit := none } }

def mixing : LanguageDef := { LanguageDef.empty "mixing" with terms := [constant "a" "Mol", mixedRule] }

/-- **Negative**: an algebra declared on a collection of another category is not lawful, and derives no clauses of
an algebra. -/
theorem mixing_unlawful : CollectionLaws.algebraOf? mixing mixedRule = none := by decide

end Controls

end Mettapedia.GSLT.Compilation.Uniform.EquationRules

#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.derives_equation_iff
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.eqvGen_dataStep_iff
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.eqvGen_paths
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.moves_sound
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.moves_complete
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.rowCorrespondence
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.compiledCorrespondence
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.reachModulo_iff
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.clausesOf_canonical
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.swapping_compiles
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.collapse_compiles
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.collapse_chooses
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.collapse_needs_the_supply
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.chaos_compiles
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.chaos_chooses
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.stepped_compiles
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.stepped_relates
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.literalStep_needs_the_name
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.restricting_compiles
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.shadowing_compiles
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.shadowRest_steps
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.shadowRest_needs_every
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.unboundQuantifier_compiles
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.everyUnbound_never_fires
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.unboundFresh_compiles
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.unboundFresh_steps
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.unboundFresh_reads_the_name
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.reacting_compiles
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.binding_compiles
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.eta_compiles
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.eta_steps
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.wrapping_lowers
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.betaEquation_compiles
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.beta_expands
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.beta_needs_the_supply
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.beta_compiles
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.beta_steps
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.beta_needs_abstraction
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.weakening_named_refused
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.weakening_compiles
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.unfolding_compiles
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.rekinding_refused
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.souping_compiles
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.souping_reorders
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.stray_kept
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.parallel_absorbs
#print axioms Mettapedia.GSLT.Compilation.Uniform.EquationRules.Controls.mixing_unlawful
