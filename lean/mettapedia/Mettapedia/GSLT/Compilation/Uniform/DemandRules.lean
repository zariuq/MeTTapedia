import Mettapedia.GSLT.Compilation.Uniform.DemandTransformation
import Mettapedia.GSLT.Compilation.Uniform.StepPremises
import Mettapedia.GSLT.Compilation.Uniform.CollectionMatching
import Mettapedia.GSLT.Compilation.Uniform.DataClauses
import Mettapedia.OSLF.MeTTaIL.ContextualStepFuel

/-!
# Rules as clauses

An authored rule is one clause of the relation of steps (`tripleClause`): its left side is matched, its premises are
goals, and its right side is instantiated scope-correctly at depth zero, from the rule's binding sites. A bag or a set
on the left side is matched by picking its elements from its list, in turn; one on the right side is instantiated from
the lists its rests hold. Every input is read as the source reads it, at the names bound before it: the variable of a
name nothing has bound yet is replaced by the name itself (`literalize`). A query asks its relation for the rows of its
arguments read so, and its arguments are the row it gets; a step premise instantiates its source scope-correctly at the
premise's depth and asks the relation of steps; a freshness condition is decided by the source's own freshness check.
A name of the right side that nothing binds is read as itself too.

A quantified premise asks a relation of its own (`forAllRelation`) about its collection's list and the values of the
names bound before it. That relation has two clauses per quantified premise (`Quantified.clauses`): none for no
elements, and for a first element its body's goals with the parameter bound to it, then the other elements. The
clauses are keyed by the premise's structure (`Quantified.key`), so equal keys mean equal clauses, and the body's
names stay inside it.

An instance of the clause whose goals hold is an instance of the triple whose premises have witnesses, at every term
(`triple_sound`); at data the converse holds (`triple_complete`). So the least model of the rules' clauses is the
reference step relation at data (`derives_step_iff`): every derivation is a step (`step_of_derivesAt`), and every step
of data is a derivation (`derives_of_stepValid`).

The converse clause of a triple reads the triple backwards (`converseClause`): its input is an instance of the right side,
read back by the converses of the instantiation's goals (lowering for a lift, wrapping for an unwrap), and its output
is every term the left side matches. It relates exactly the instances of the triple taken back (`converse_sound`,
`converse_complete`).

The compiler checks the shape a triple needs, by name (`tripleChecked`, `ruleClause`): a right side without binder
names, the rests of the right side among those of the left of the same kind, and premises of the shapes they are read in
(`flows?`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.Uniform.DemandRules

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec (MatchRel matchPattern_sound)
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.Framework.PredFiniteSufficient (lookupOrFvar BindingsValued)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax
open RuleSyntax.Presentation.Schematic
open Mettapedia.OSLF.MeTTaIL.ReferenceStep (StepValid PremisesValid Witness Step stepDepth stepEndpoints
  captureSitesOf bindParameter)
open RootRewritesOnTheStep (labelCode labelCode_injective symTerm appTerm encode encodeList encode_injective
  encodeList_inj)
open OrderedMatching (ordered orderedList isData isDataList names namesList restNames restNamesList Settled DataOn
  Covers lookup_of_valued)
open OrderedRows (lower? lowerThen? inst_lower inst_lowerThen lower_captures lowerThen_captures exists_witness
  Captured Holds unknowns_lower unknowns_lowerThen)
open RuleSyntax.Machines (unknowns)
open QueryPremises (DataRows queryRows)
open QueryRulesOnTheStep (valueRow)
open Mettapedia.OSLF.MeTTaIL.Substitution (checkFreshness)
open RuleSyntax.ComputedConditions (Relations)
open StepPremises (Flows Hold TripleShape TripleAt triple_data nextBound scopeOf mem_scopeOf restrict boundAfter)
open DemandTransformation (Goal Clause goalHolds goalUnknowns goalInputs DerivesAt Derives InputsBound)
open MatchesAndInstances (vectorRests bagRests BagSettled)
open CollectionMatching (matchRow invertGoals CollectionProgram matchRow_sound matchRow_complete matchRow_scope
  matchRow_decodes matchRow_matching matchRow_moded matchRow_readBack invertGoals_hold mem_invertGoals_unknowns
  untouched_name holds_congr goals_agree InScope AgreeOutside)
open Instantiation (buildRow BuildClauses buildRow_sound buildRow_complete buildRow_scope buildRow_moded)
open CollectionMatching (collectionTerm listUnknown listUnknown_ne listUnknown_injective)
open UnificationClauses (triple)
open Mettapedia.OSLF.MeTTaIL.PatternCode (collectionCode)

/-! ## The clause of a triple -/

/-- The relation of steps. -/
def stepRelation : ℕ := 0

/-- **The relations a rule's goals consult**: the queried relations, and freshness: the row of a name and the row
of a term in which the name does not occur free. The source's own freshness check decides it. -/
def premiseRelations (relEnv : RelationEnv) (language : LanguageDef) : Relations :=
  fun f arguments value =>
    (∃ relation request row, f = labelCode relation ∧ arguments = [encodeList request] ∧ value = encodeList row ∧
      row ∈ queryRows relEnv language relation request) ∨
    ∃ name term, arguments = [encode (.fvar name), encode term] ∧ value = .sym 0 ∧
      checkFreshness { varName := name, term := term } = true

/-! ## Names read as themselves -/

/-- The row of a name read as itself. -/
def literalRow (name : String) : Tm := toTerm (encode (.fvar name))

/-- **Reading some names as themselves**: the variable of each becomes the name's row. -/
def literalSubst (unbound : List String) : Mettapedia.Logic.LP.Subst rowSig := fun x =>
  match unbound.find? (fun name => labelCode name == x) with
  | some name => literalRow name
  | none => .var x

/-- A row pattern with some names read as themselves. -/
def literalize (unbound : List String) (t : Tm) : Tm := (literalSubst unbound).applyTerm t

/-- A goal with some names read as themselves. -/
def literalGoal (unbound : List String) : Goal → Goal
  | .query condition => .query
      { name := condition.name
        arguments := condition.arguments.map (literalize unbound)
        value := literalize unbound condition.value }
  | .ask relation input output => .ask relation (literalize unbound input) (literalize unbound output)

/-- An instantiation with some names read as themselves. -/
def literalValues (θ : ℕ → Expr) (unbound : List String) : ℕ → Expr := fun x =>
  match unbound.find? (fun name => labelCode name == x) with
  | some name => encode (.fvar name)
  | none => θ x

theorem inst_applyTerm (θ : ℕ → Expr) (σ : Mettapedia.Logic.LP.Subst rowSig) :
    ∀ t : Tm, inst θ (σ.applyTerm t) = inst (fun x => inst θ (σ x)) t
  | .var _ => rfl
  | .const (.sym _) => rfl
  | .const (.name _) => rfl
  | .app .app ts => by
      show Expr.app (inst θ (σ.applyTerm (ts head))) (inst θ (σ.applyTerm (ts tail))) = _
      rw [inst_applyTerm θ σ (ts head), inst_applyTerm θ σ (ts tail)]
      rfl
  | .app .code ts => by
      show Expr.code (inst θ (σ.applyTerm (ts body))) = _
      rw [inst_applyTerm θ σ (ts body)]
      rfl

theorem inst_literalize (θ : ℕ → Expr) (unbound : List String) (t : Tm) :
    inst θ (literalize unbound t) = inst (literalValues θ unbound) t := by
  rw [literalize, inst_applyTerm]
  congr 1
  funext x
  simp only [literalSubst, literalValues]
  split
  · exact inst_toTerm θ _
  · rfl

theorem goalHolds_literal {R : Relations} {D : ℕ → Expr → Expr → Prop} {θ : ℕ → Expr} {unbound : List String} :
    ∀ g : Goal, goalHolds R D θ (literalGoal unbound g) ↔ goalHolds R D (literalValues θ unbound) g
  | .query condition => by
      simp only [literalGoal, goalHolds, List.map_map]
      rw [inst_literalize]
      have same : (inst θ ∘ literalize unbound) = inst (literalValues θ unbound) := funext (inst_literalize θ unbound)
      rw [same]
  | .ask relation input output => by simp only [literalGoal, goalHolds, inst_literalize]

theorem literalValues_of_mem {θ : ℕ → Expr} {unbound : List String} {name : String} (inside : name ∈ unbound) :
    literalValues θ unbound (labelCode name) = encode (.fvar name) := by
  simp only [literalValues]
  split
  · rename_i found foundIs
    have := List.find?_some foundIs
    simp only [beq_iff_eq] at this
    rw [labelCode_injective this]
  · rename_i absent
    rw [List.find?_eq_none] at absent
    exact absurd (absent name inside) (by simp)

@[simp] theorem literalValues_nil (θ : ℕ → Expr) : literalValues θ [] = θ := by
  funext x
  simp [literalValues]

theorem literalValues_of_not_mem {θ : ℕ → Expr} {unbound : List String} {x : ℕ}
    (outside : ∀ name ∈ unbound, labelCode name ≠ x) : literalValues θ unbound x = θ x := by
  simp only [literalValues]
  split
  · rename_i found foundIs
    have := List.find?_some foundIs
    simp only [beq_iff_eq] at this
    exact absurd this (outside found (List.mem_of_find?_eq_some foundIs))
  · rfl

theorem unknowns_literalize (unbound : List String) :
    ∀ (t : Tm) {x : ℕ}, x ∈ unknowns (literalize unbound t) → x ∈ unknowns t ∧ ∀ name ∈ unbound, labelCode name ≠ x
  | .var y, x, inside => by
      simp only [literalize, Mettapedia.Logic.LP.Subst.applyTerm_var, literalSubst] at inside
      split at inside
      · simp [literalRow, Instantiation.unknowns_toTerm] at inside
      · rename_i absent
        rw [List.find?_eq_none] at absent
        simp only [unknowns, List.mem_singleton] at inside
        subst inside
        refine ⟨List.mem_singleton_self _, fun name member same => ?_⟩
        have := absent name member
        simp [same] at this
  | .const _, _, inside => by simp [literalize, unknowns] at inside
  | .app .app ts, x, inside => by
      have split : unknowns (literalize unbound (.app .app ts)) =
          unknowns (literalize unbound (ts head)) ++ unknowns (literalize unbound (ts tail)) := rfl
      rw [split, List.mem_append] at inside
      rcases inside with inside | inside
      · obtain ⟨member, outside⟩ := unknowns_literalize unbound (ts head) inside
        exact ⟨List.mem_append_left _ member, outside⟩
      · obtain ⟨member, outside⟩ := unknowns_literalize unbound (ts tail) inside
        exact ⟨List.mem_append_right _ member, outside⟩
  | .app .code ts, x, inside => by
      have split : unknowns (literalize unbound (.app .code ts)) = unknowns (literalize unbound (ts body)) := rfl
      rw [split] at inside
      exact unknowns_literalize unbound (ts body) inside

/-- The names of a list that are not bound yet. -/
def unboundIn (bound mentioned : List String) : List String := mentioned.filter (· ∉ bound)

theorem mem_unboundIn {bound mentioned : List String} {name : String} :
    name ∈ unboundIn bound mentioned ↔ name ∈ mentioned ∧ name ∉ bound := by
  simp [unboundIn]

theorem mem_unknowns_literalize {unbound : List String} {t : Tm} {x : ℕ}
    (inside : x ∈ unknowns (literalize unbound t)) : x ∈ unknowns t :=
  (unknowns_literalize unbound t inside).1

theorem goalUnknowns_literal {unbound : List String} :
    ∀ (g : Goal) {x : ℕ}, x ∈ goalUnknowns (literalGoal unbound g) →
      x ∈ goalUnknowns g ∧ ∀ name ∈ unbound, labelCode name ≠ x
  | .query condition, x, inside => by
      simp only [literalGoal, goalUnknowns, List.mem_append, List.mem_flatMap, List.mem_map] at inside ⊢
      rcases inside with ⟨_, ⟨argument, member, rfl⟩, inArgument⟩ | inValue
      · obtain ⟨found, outside⟩ := unknowns_literalize unbound argument inArgument
        exact ⟨.inl ⟨argument, member, found⟩, outside⟩
      · obtain ⟨found, outside⟩ := unknowns_literalize unbound _ inValue
        exact ⟨.inr found, outside⟩
  | .ask _ input output, x, inside => by
      simp only [literalGoal, goalUnknowns, List.mem_append] at inside ⊢
      rcases inside with inInput | inOutput
      · obtain ⟨found, outside⟩ := unknowns_literalize unbound input inInput
        exact ⟨.inl found, outside⟩
      · obtain ⟨found, outside⟩ := unknowns_literalize unbound output inOutput
        exact ⟨.inr found, outside⟩

theorem mem_unknowns_literalize_of {unbound : List String} :
    ∀ (t : Tm) {x : ℕ}, x ∈ unknowns t → (∀ name ∈ unbound, labelCode name ≠ x) → x ∈ unknowns (literalize unbound t)
  | .var y, x, inside, outside => by
      simp only [unknowns, List.mem_singleton] at inside
      subst inside
      have absent : unbound.find? (fun name => labelCode name == x) = none := by
        rw [List.find?_eq_none]
        intro name member same
        exact outside name member (by simpa using same)
      show x ∈ unknowns ((literalSubst unbound) x)
      simp [literalSubst, absent]
  | .const _, _, inside, _ => by simp [unknowns] at inside
  | .app .app ts, x, inside, outside => by
      have split : unknowns (literalize unbound (.app .app ts)) =
          unknowns (literalize unbound (ts head)) ++ unknowns (literalize unbound (ts tail)) := rfl
      have split' : unknowns (.app .app ts : Tm) = unknowns (ts head) ++ unknowns (ts tail) := rfl
      rw [split]
      rw [split'] at inside
      rcases List.mem_append.mp inside with found | found
      · exact List.mem_append_left _ (mem_unknowns_literalize_of (ts head) found outside)
      · exact List.mem_append_right _ (mem_unknowns_literalize_of (ts tail) found outside)
  | .app .code ts, x, inside, outside => by
      have split : unknowns (literalize unbound (.app .code ts)) = unknowns (literalize unbound (ts body)) := rfl
      have split' : unknowns (.app .code ts : Tm) = unknowns (ts body) := rfl
      rw [split]
      rw [split'] at inside
      exact mem_unknowns_literalize_of (ts body) inside outside

theorem goalUnknowns_literal_of {unbound : List String} :
    ∀ (g : Goal) {x : ℕ}, x ∈ goalUnknowns g → (∀ name ∈ unbound, labelCode name ≠ x) →
      x ∈ goalUnknowns (literalGoal unbound g)
  | .query condition, x, inside, outside => by
      simp only [literalGoal, goalUnknowns, List.mem_append, List.mem_flatMap, List.mem_map] at inside ⊢
      rcases inside with ⟨argument, member, inArgument⟩ | inValue
      · exact .inl ⟨_, ⟨argument, member, rfl⟩, mem_unknowns_literalize_of argument inArgument outside⟩
      · exact .inr (mem_unknowns_literalize_of _ inValue outside)
  | .ask _ input output, x, inside, outside => by
      simp only [literalGoal, goalUnknowns, List.mem_append] at inside ⊢
      rcases inside with found | found
      · exact .inl (mem_unknowns_literalize_of input found outside)
      · exact .inr (mem_unknowns_literalize_of output found outside)

theorem goalInputs_literal {unbound : List String} :
    ∀ (g : Goal) {x : ℕ}, x ∈ goalInputs (literalGoal unbound g) →
      x ∈ goalInputs g ∧ ∀ name ∈ unbound, labelCode name ≠ x
  | .query condition, x, inside => by
      simp only [literalGoal, goalInputs, List.mem_flatMap, List.mem_map] at inside ⊢
      obtain ⟨_, ⟨argument, member, rfl⟩, inArgument⟩ := inside
      obtain ⟨found, outside⟩ := unknowns_literalize unbound argument inArgument
      exact ⟨⟨argument, member, found⟩, outside⟩
  | .ask _ input _, x, inside => by
      simp only [literalGoal, goalInputs] at inside ⊢
      exact unknowns_literalize unbound input inside

/-- **Reading names as themselves binds them**: goals moded once those names' unknowns are bound are moded without
them once the names are read as themselves. -/
theorem inputsBound_literal {unbound : List String} : ∀ {before : List ℕ} {goals : List Goal},
    InputsBound (before ++ unbound.map labelCode) goals → InputsBound before (goals.map (literalGoal unbound))
  | before, [], _ => .nil before
  | before, g :: goals, .cons first later => by
      refine .cons (fun x inside => ?_) (inputsBound_literal (InputsBound.mono ?_ later))
      · obtain ⟨found, outside⟩ := goalInputs_literal g inside
        rcases List.mem_append.mp (first x found) with inBefore | literal
        · exact inBefore
        · obtain ⟨name, member, rfl⟩ := List.mem_map.mp literal
          exact absurd rfl (outside name member)
      · intro x inside
        rcases List.mem_append.mp inside with front | inGoal
        · rcases List.mem_append.mp front with inBefore | literal
          · exact List.mem_append_left _ (List.mem_append_left _ inBefore)
          · exact List.mem_append_right _ literal
        · by_cases isLiteral : ∃ name ∈ unbound, labelCode name = x
          · obtain ⟨name, member, rfl⟩ := isLiteral
            exact List.mem_append_right _ (List.mem_map.mpr ⟨name, member, rfl⟩)
          · simp only [not_exists, not_and] at isLiteral
            exact List.mem_append_left _ (List.mem_append_right _ (goalUnknowns_literal_of g inGoal isLiteral))

/-- The relation from a collection to the list of its elements. -/
def listOfRelation : ℕ := 34

/-- The relation of a quantified premise: it holds of a key, a list of elements and the values of a context. -/
def forAllRelation : ℕ := 35

/-- Reading the list of a collection of a kind. -/
def listOfClause (kind : CollType) : Clause :=
  { relation := listOfRelation, input := collectionTerm kind (.var 0), output := .var 0, body := [] }

/-- The clauses of reading lists: of a vector, a bag and a set. -/
def listOfClauses : List Clause := [listOfClause .vec, listOfClause .hashBag, listOfClause .hashSet]

/-- The rests of a triple: the vector rests of its sides. -/
def tripleRests (left right : Pattern) : List String := vectorRests left ++ vectorRests right

/-- The names a premise mentions in its clause. -/
def premiseNamesOf : Premise → List String
  | .relationQuery _ arguments => namesList arguments
  | .freshness condition => condition.varName :: names condition.term
  | .congruence source target => names source ++ names target
  | .scopedStep step => names step.source ++ names step.target
  | .forAll collection _ _ => [collection]

/-- The names some premises mention. -/
def premiseNames (premises : List Premise) : List String := premises.flatMap premiseNamesOf

theorem premiseNamesOf_step {premise : Premise} {source target : Pattern}
    (endpoints : stepEndpoints premise = some (source, target)) :
    premiseNamesOf premise = names source ++ names target := by
  cases premise <;> simp_all [stepEndpoints, premiseNamesOf]

/-- **A premise as a pattern**: the parts the clauses of a quantified premise over it are read from. A scoped step
premise counts its binders. -/
def premiseKey : Premise → Pattern
  | .relationQuery relation arguments => .apply "query" [.fvar relation, .collection .vec arguments none]
  | .freshness condition => .apply "fresh" [.fvar condition.varName, condition.term]
  | .congruence source target => .apply "step" [source, target]
  | .scopedStep step => .apply "scoped" [.bvar step.binders.length, step.source, step.target]
  | .forAll collection parameter body => .apply "all" [.fvar collection, .fvar parameter, premiseKey body]

/-- Some names as a pattern. -/
def namesPattern (names : List String) : Pattern := .collection .vec (names.map .fvar) none

/-- **A quantified premise, as its clauses read it**: the rests of the clauses, the binding sites, the names its body
sees besides its parameter, its parameter, and its body. -/
structure Quantified where
  rests : List String
  sites : Pattern
  context : List String
  parameter : String
  body : Premise

/-- The quantified premise with a parameter and a body, in a clause with some rests and binding sites, at the names
bound before it. -/
def quantifiedAt (rests : List String) (sites : Pattern) (bound : List String) (parameter : String) (body : Premise) :
    Quantified :=
  { rests := rests.filter (· ≠ parameter), sites, context := bound.filter (· ≠ parameter), parameter, body }

/-- The key of a quantified premise's clauses: a constant row of everything they are read from. -/
def Quantified.key (q : Quantified) : Tm :=
  toTerm (encode (.apply "key" [q.sites, namesPattern q.rests, .fvar q.parameter, premiseKey q.body,
    namesPattern q.context]))

/-- The names a quantified premise's clauses mention; their fresh lists avoid them. -/
def Quantified.avoid (q : Quantified) : List String := q.parameter :: q.context ++ premiseNamesOf q.body

/-- The row of the values of some names. -/
def contextRow : List String → Tm
  | [] => symTerm 0
  | name :: names => appTerm (.var (labelCode name)) (contextRow names)

/-- **The goals of a step premise**: its source instantiated scope-correctly at the premise's depth, with the names not
bound before it read as themselves, and a goal asking the relation of steps for its target; with the next fresh
unknown. -/
def stepGoals (rests avoid : List String) (sites : Pattern) (bound : List String) (next : ℕ) (premise : Premise)
    (source target : Pattern) : Option (List Goal × ℕ) :=
  (buildRow rests avoid sites (stepDepth sites premise) next source).bind fun built =>
    (lower? rests target).map fun targetRow =>
      (built.2.1.map (literalGoal (unboundIn bound (names source))) ++
        [.ask stepRelation (literalize (unboundIn bound (names source)) built.1) targetRow], built.2.2)

/-- **The goals of a quantified premise**: the list of its collection, read off the collection unless the collection is
a vector rest, already a list; and a goal asking the relation of the quantified premise for its key, the list and the
values of its context. -/
def forAllGoals (rests avoid bound : List String) (next : ℕ) (collection : String) (q : Quantified) : List Goal :=
  if collection ∈ rests then
    [.ask forAllRelation (triple q.key (.var (labelCode collection)) (contextRow q.context)) (symTerm 0)]
  else
    [.ask listOfRelation (literalize (unboundIn bound [collection]) (.var (labelCode collection)))
        (.var (listUnknown avoid next)),
      .ask forAllRelation (triple q.key (.var (listUnknown avoid next)) (contextRow q.context)) (symTerm 0)]

/-- The goals of a premise, and the next fresh unknown, at the names bound before it, the others read as themselves:
a query asks its relation for the row of its arguments and gets them, a step premise asks the relation of steps, and a
freshness condition is a condition on freshness. -/
def premiseGoal (rests avoid : List String) (sites : Pattern) (bound : List String) (next : ℕ) :
    Premise → Option (List Goal × ℕ)
  | .relationQuery relation arguments => (lowerThen? rests arguments (symTerm 0)).map fun row =>
      ([.query
          { name := labelCode relation
            arguments := [literalize (unboundIn bound (namesList arguments)) row]
            value := row }], next)
  | .freshness condition => (lower? rests condition.term).map fun termRow =>
      ([.query
          { name := 0
            arguments := [literalize (unboundIn bound (condition.varName :: names condition.term))
                (.var (labelCode condition.varName)),
              literalize (unboundIn bound (condition.varName :: names condition.term)) termRow]
            value := symTerm 0 }], next)
  | .congruence source target => stepGoals rests avoid sites bound next (.congruence source target) source target
  | .scopedStep step => stepGoals rests avoid sites bound next (.scopedStep step) step.source step.target
  | .forAll collection parameter body =>
      (premiseGoal (quantifiedAt rests sites bound parameter body).rests
          (quantifiedAt rests sites bound parameter body).avoid sites (scopeOf bound parameter) 1 body).map fun _ =>
        (forAllGoals rests avoid bound next collection (quantifiedAt rests sites bound parameter body), next + 1)

/-- The goals of premises, in their order, and the next fresh unknown, from the names bound before the first. -/
def premiseGoals (rests avoid : List String) (sites : Pattern) : List String → ℕ → List Premise →
    Option (List Goal × ℕ)
  | _, next, [] => some ([], next)
  | bound, next, premise :: premises => (premiseGoal rests avoid sites bound next premise).bind fun here =>
      (premiseGoals rests avoid sites (nextBound bound premise) here.2 premises).map fun later =>
        (here.1 ++ later.1, later.2)

/-- The clause of a quantified premise for no elements. -/
def Quantified.nilClause (q : Quantified) : Clause :=
  { relation := forAllRelation, input := triple q.key (symTerm 0) (contextRow q.context), output := symTerm 0,
    body := [] }

/-- The clause of a quantified premise for a first element: the body's goals with the parameter bound to it, then the
other elements. -/
def Quantified.consClause (q : Quantified) (bodyGoals : List Goal) : Clause :=
  { relation := forAllRelation,
    input := triple q.key (appTerm (.var (labelCode q.parameter)) (.var (listUnknown q.avoid 0)))
      (contextRow q.context),
    output := symTerm 0,
    body := bodyGoals ++
      [.ask forAllRelation (triple q.key (.var (listUnknown q.avoid 0)) (contextRow q.context)) (symTerm 0)] }

/-- **The clauses of a quantified premise**: none for no elements, and for an element, its body's goals with the
parameter bound to it, then the rest. -/
def Quantified.clauses (q : Quantified) : Option (List Clause) :=
  (premiseGoal q.rests q.avoid q.sites (q.parameter :: q.context) 1 q.body).map fun bodyGoals =>
    [q.nilClause, q.consClause bodyGoals.1]

/-- The quantified premises of a premise at the names bound before it: its own, and those inside its body. -/
def premiseQuantified (rests : List String) (sites : Pattern) (bound : List String) : Premise → List Quantified
  | .relationQuery _ _ => []
  | .freshness _ => []
  | .congruence _ _ => []
  | .scopedStep _ => []
  | .forAll _ parameter body => quantifiedAt rests sites bound parameter body ::
      premiseQuantified (rests.filter (· ≠ parameter)) sites (scopeOf bound parameter) body

/-- The quantified premises of premises, from the names bound before the first. -/
def premisesQuantified (rests : List String) (sites : Pattern) : List String → List Premise → List Quantified
  | _, [] => []
  | bound, premise :: premises => premiseQuantified rests sites bound premise ++
      premisesQuantified rests sites (nextBound bound premise) premises

theorem premisesQuantified_cons {rests : List String} {sites : Pattern} {bound : List String} {premise : Premise}
    {premises : List Premise} :
    premisesQuantified rests sites bound (premise :: premises) =
      premiseQuantified rests sites bound premise ++ premisesQuantified rests sites (nextBound bound premise) premises :=
  rfl

/-- The clauses of quantified premises are clauses of a program. -/
def QuantifiedPresent (program : List Clause) (quantified : List Quantified) : Prop :=
  ∀ q ∈ quantified, ∀ cs, q.clauses = some cs → ∀ c ∈ cs, c ∈ program

theorem premiseGoals_single {rests avoid : List String} {sites : Pattern} {bound : List String} {next : ℕ}
    {premise : Premise} {result : List Goal × ℕ} (lowered : premiseGoal rests avoid sites bound next premise = some result) :
    premiseGoals rests avoid sites bound next [premise] = some result := by
  simp [premiseGoals, lowered]

theorem premiseGoal_step {rests avoid : List String} {sites : Pattern} {bound : List String} {next : ℕ}
    {premise : Premise} {source target : Pattern} (endpoints : stepEndpoints premise = some (source, target)) :
    premiseGoal rests avoid sites bound next premise = stepGoals rests avoid sites bound next premise source target := by
  cases premise <;> simp_all [stepEndpoints, premiseGoal]

/-! ## Quantified premises: lists, contexts and keys -/

section QuantifiedRows

variable {R : Relations} {program : List Clause}

theorem listOf_sound (onlyListOfs : ∀ c ∈ program, c.relation = listOfRelation → c ∈ listOfClauses) {x y : Expr}
    (derived : Derives R program listOfRelation x y) :
    ∃ kind, x = .app (.sym 6) (.app (.sym (collectionCode kind)) (.app y (.sym 0))) := by
  obtain ⟨c, member, isListOf, θ, input, output, -⟩ := DemandTransformation.derives_cases derived
  have inClauses := onlyListOfs c member isListOf
  simp only [listOfClauses, List.mem_cons, List.not_mem_nil, or_false] at inClauses
  rcases inClauses with rfl | rfl | rfl <;>
    · simp only [listOfClause, CollectionMatching.inst_collectionTerm, DemandTransformation.inst_unknown] at input output
      exact ⟨_, by rw [← input, ← output]⟩

theorem listOf_complete (listOfs : ∀ c ∈ listOfClauses, c ∈ program) (kind : CollType) (items : List Pattern) :
    Derives R program listOfRelation (encode (.collection kind items none)) (encodeList items) := by
  have member : listOfClause kind ∈ program := listOfs _ (by cases kind <;> simp [listOfClauses])
  have clause := DemandTransformation.derives_of_clause (R := R) member (fun _ => encodeList items)
    (fun g inside => by simp [listOfClause] at inside)
  rw [CollectionMatching.encode_collection]
  simpa [listOfClause, CollectionMatching.inst_collectionTerm] using clause

end QuantifiedRows

theorem inst_contextRow_agree {θ θ' : ℕ → Expr} : ∀ {names : List String},
    inst θ (contextRow names) = inst θ' (contextRow names) → ∀ name ∈ names, θ (labelCode name) = θ' (labelCode name)
  | [], _, _, inside => absurd inside List.not_mem_nil
  | _ :: _, same, name, inside => by
      simp only [contextRow, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, Expr.app.injEq]
        at same
      rcases List.mem_cons.mp inside with rfl | later
      · exact same.1
      · exact inst_contextRow_agree same.2 name later

theorem inst_contextRow_congr {θ θ' : ℕ → Expr} : ∀ {names : List String},
    (∀ name ∈ names, θ (labelCode name) = θ' (labelCode name)) → inst θ (contextRow names) = inst θ' (contextRow names)
  | [], _ => rfl
  | _ :: _, agree => by
      simp only [contextRow, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown]
      rw [agree _ List.mem_cons_self, inst_contextRow_congr fun name inside => agree name (List.mem_cons_of_mem _ inside)]

theorem unknowns_contextRow : ∀ names : List String, unknowns (contextRow names) = names.map labelCode
  | [] => by simp [contextRow]
  | name :: names => by
      simp [contextRow, RootRewritesOnTheStep.unknowns_appTerm, unknowns_contextRow names]

theorem namesPattern_injective {first second : List String} (same : namesPattern first = namesPattern second) :
    first = second := by
  simp only [namesPattern, Pattern.collection.injEq, true_and, and_true] at same
  exact (List.map_injective_iff.mpr fun _ _ fvars => Pattern.fvar.inj fvars) same

theorem Quantified.key_same {θ θ' : ℕ → Expr} {q q' : Quantified} (same : inst θ' q'.key = inst θ q.key) :
    q'.rests = q.rests ∧ q'.sites = q.sites ∧ q'.context = q.context ∧ q'.parameter = q.parameter ∧
      premiseKey q'.body = premiseKey q.body := by
  simp only [Quantified.key, inst_toTerm] at same
  have patterns := encode_injective same
  simp only [Pattern.apply.injEq, true_and, List.cons.injEq, and_true, Pattern.fvar.injEq] at patterns
  obtain ⟨sites, rests, parameter, body, context⟩ := patterns
  exact ⟨namesPattern_injective rests, sites, namesPattern_injective context, parameter, body⟩

theorem premiseNamesOf_key {premise premise' : Premise} (same : premiseKey premise' = premiseKey premise) :
    premiseNamesOf premise' = premiseNamesOf premise := by
  cases premise <;> cases premise' <;> simp_all [premiseKey, premiseNamesOf]

/-- **A premise's goals are read off its key.** -/
theorem premiseGoal_key : ∀ {rests avoid : List String} {sites : Pattern} {bound : List String} {next : ℕ}
    (premise : Premise) {premise' : Premise}, premiseKey premise' = premiseKey premise →
      premiseGoal rests avoid sites bound next premise' = premiseGoal rests avoid sites bound next premise
  | _, _, _, _, _, .relationQuery _ _, premise', same => by
      cases premise' <;> simp_all [premiseKey]
  | _, _, _, _, _, .freshness condition, premise', same => by
      cases premise' with
      | freshness condition' =>
          obtain ⟨varName, term⟩ := condition
          obtain ⟨varName', term'⟩ := condition'
          simp_all [premiseKey]
      | _ => simp [premiseKey] at same
  | _, _, _, _, _, .congruence _ _, premise', same => by
      cases premise' <;> simp_all [premiseKey]
  | _, _, _, _, _, .scopedStep step, premise', same => by
      cases premise' with
      | scopedStep step' =>
          simp only [premiseKey, Pattern.apply.injEq, List.cons.injEq, Pattern.bvar.injEq, and_true, true_and]
            at same
          obtain ⟨length, source, target⟩ := same
          simp only [premiseGoal, stepGoals, stepDepth, length, source, target]
      | _ => simp [premiseKey] at same
  | rests, avoid, sites, bound, next, .forAll collection parameter body, premise', same => by
      cases premise' with
      | forAll collection' parameter' body' =>
          simp only [premiseKey, Pattern.apply.injEq, List.cons.injEq, Pattern.fvar.injEq, and_true, true_and]
            at same
          obtain ⟨collectionSame, parameterSame, bodySame⟩ := same
          rw [collectionSame, parameterSame]
          have avoidSame : (quantifiedAt rests sites bound parameter body').avoid =
              (quantifiedAt rests sites bound parameter body).avoid := by
            simp [Quantified.avoid, quantifiedAt, premiseNamesOf_key bodySame]
          have keySame : (quantifiedAt rests sites bound parameter body').key =
              (quantifiedAt rests sites bound parameter body).key := by
            simp [Quantified.key, quantifiedAt, bodySame]
          have goalsSame : forAllGoals rests avoid bound next collection (quantifiedAt rests sites bound parameter body') =
              forAllGoals rests avoid bound next collection (quantifiedAt rests sites bound parameter body) := by
            unfold forAllGoals
            rw [keySame]
            rfl
          simp only [premiseGoal]
          rw [avoidSame, goalsSame, premiseGoal_key body bodySame]
          rfl
      | _ => simp [premiseKey] at same

/-- **Quantified premises with the same key have the same clauses.** -/
theorem Quantified.clauses_of_key {q q' : Quantified} (rests : q'.rests = q.rests) (sites : q'.sites = q.sites)
    (context : q'.context = q.context) (parameter : q'.parameter = q.parameter)
    (body : premiseKey q'.body = premiseKey q.body) :
    q'.key = q.key ∧ q'.avoid = q.avoid ∧
      premiseGoal q'.rests q'.avoid q'.sites (q'.parameter :: q'.context) 1 q'.body =
        premiseGoal q.rests q.avoid q.sites (q.parameter :: q.context) 1 q.body := by
  obtain ⟨rests', sites', context', parameter', body'⟩ := q'
  obtain ⟨rests₀, sites₀, context₀, parameter₀, body₀⟩ := q
  simp only at rests sites context parameter body
  subst rests sites context parameter
  have avoidSame : (Quantified.mk rests' sites' context' parameter' body').avoid =
      (Quantified.mk rests' sites' context' parameter' body₀).avoid := by
    simp [Quantified.avoid, premiseNamesOf_key body]
  refine ⟨by simp [Quantified.key, body], avoidSame, ?_⟩
  rw [avoidSame]
  exact premiseGoal_key body₀ body

theorem derivesAt_unfold {R : Relations} {program : List Clause} {depth relation : ℕ} {x y : Expr}
    (derived : DerivesAt R program depth relation x y) :
    ∃ c ∈ program, c.relation = relation ∧ ∃ θ : ℕ → Expr, inst θ c.input = x ∧ inst θ c.output = y ∧
      ∀ g ∈ c.body, goalHolds R (DerivesAt R program depth) θ g := by
  cases depth with
  | zero => exact derived.elim
  | succ depth =>
      obtain ⟨c, member, relationIs, θ, input, output, goals⟩ := derived
      exact ⟨c, member, relationIs, θ, input, output, fun g inside => DemandTransformation.goalHolds_mono
        (fun _ _ _ held => DemandTransformation.DerivesAt.mono (Nat.le_succ _) held) (goals g inside)⟩

/-- **A relation of derivations that unfolds at quantified premises**: each of its facts of the relation of quantified
premises is an instance of a clause of the program whose goals hold in it. -/
def Unfolds (R : Relations) (program : List Clause) (D : ℕ → Expr → Expr → Prop) : Prop :=
  ∀ x y, D forAllRelation x y → ∃ c ∈ program, c.relation = forAllRelation ∧ ∃ θ : ℕ → Expr,
    inst θ c.input = x ∧ inst θ c.output = y ∧ ∀ g ∈ c.body, goalHolds R D θ g

theorem derivesAt_unfolds {R : Relations} {program : List Clause} (depth : ℕ) :
    Unfolds R program (DerivesAt R program depth) := fun _ _ derived => derivesAt_unfold derived

/-- **The clauses of quantified premises** in a program: reading lists, and every clause of the relation of quantified
premises is a clause of some quantified premise. -/
structure ForAllClauses (program : List Clause) : Prop where
  listOfs : ∀ c ∈ listOfClauses, c ∈ program
  onlyListOfs : ∀ c ∈ program, c.relation = listOfRelation → c ∈ listOfClauses
  onlyForAlls : ∀ c ∈ program, c.relation = forAllRelation → ∃ (q : Quantified) (cs : List Clause),
    q.clauses = some cs ∧ c ∈ cs

/-- The names a triple mentions; its fresh lists avoid them. -/
def tripleNames (left right : Pattern) (premises : List Premise) : List String :=
  names left ++ names right ++ premiseNames premises

/-- The names of a triple's right side that nothing binds: read as themselves. -/
def rightUnbound (left right : Pattern) (premises : List Premise) : List String :=
  unboundIn (boundAfter (names left) premises) (names right)

/-- **The clause of a triple**: the left side is matched, the premises are goals, and the right side is
instantiated scope-correctly at depth zero, from the binding sites of the left side and the premises, a name nothing
binds read as itself. -/
def tripleClause (relation : ℕ) (left right : Pattern) (premises : List Premise) : Option Clause :=
  (matchRow (tripleRests left right) (tripleNames left right premises) 0 left).bind fun matched =>
    (premiseGoals (tripleRests left right) (tripleNames left right premises) (captureSitesOf left premises)
        (names left) matched.2.2 premises).bind fun body =>
      (buildRow (tripleRests left right) (tripleNames left right premises) (captureSitesOf left premises) 0 body.2
          right).map fun built =>
        { relation, input := matched.1, output := literalize (rightUnbound left right premises) built.1,
          body := matched.2.1 ++ body.1 ++ built.2.1.map (literalGoal (rightUnbound left right premises)) }

theorem tripleClause_relation {relation : ℕ} {left right : Pattern} {premises : List Premise} {c : Clause}
    (lowered : tripleClause relation left right premises = some c) : c.relation = relation := by
  simp only [tripleClause, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
  obtain ⟨_, _, _, _, _, _, rfl⟩ := lowered
  rfl

/-- **The names a converse chooses**: the names of the matched side that the built side does not hold. -/
def freeNames (left right : Pattern) : List String := (names left).filter (· ∉ names right)

/-- The goal choosing a name over the supply: a list of data for a vector rest of the matched side, a datum
otherwise. -/
def freeGoal (left : Pattern) (name : String) : Goal :=
  if name ∈ vectorRests left then .ask DataClauses.datumListRelation DataClauses.unitTerm (.var (labelCode name))
  else .ask DataClauses.datumRelation DataClauses.unitTerm (.var (labelCode name))

/-- The goals choosing the names a converse chooses. -/
def freeGoals (left right : Pattern) : List Goal := (freeNames left right).map (freeGoal left)

/-- **The converse clause of a triple**: the right side instantiated scope-correctly, a name nothing binds read as
itself, is the input, read back by the converses of its instantiation's goals; the names of the left side the right side
does not hold are chosen over the supply; the premises are goals; and the left side is the output, read back from its
matching goals. The clause relates an instance of the right side to the terms that the left side matches. -/
def converseClause (relation : ℕ) (left right : Pattern) (premises : List Premise) : Option Clause :=
  (buildRow (tripleRests left right) (tripleNames left right premises) (captureSitesOf left premises) 0 0 right).bind
    fun built => (Instantiation.buildConverses built.2.1).bind fun converses =>
      (premiseGoals (tripleRests left right) (tripleNames left right premises) (captureSitesOf left premises)
          (names left) built.2.2 premises).bind fun body =>
        (matchRow (tripleRests left right) (tripleNames left right premises) body.2 left).map fun other =>
          { relation, input := literalize (rightUnbound left right premises) built.1, output := other.1,
            body := converses.map (literalGoal (rightUnbound left right premises)) ++ freeGoals left right ++
              body.1 ++ invertGoals other.2.1 }

theorem converseClause_relation {relation : ℕ} {left right : Pattern} {premises : List Premise} {c : Clause}
    (lowered : converseClause relation left right premises = some c) : c.relation = relation := by
  simp only [converseClause, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := lowered
  rfl

/-! ## Witnesses -/

theorem holds_captured {rests : List String} {θ : ℕ → Expr} {witness : Bindings} {name : String}
    (holds : OrderedRows.Holds rests θ witness name) : Captured rests θ name := by
  unfold OrderedRows.Holds at holds
  unfold Captured
  split at holds
  · rename_i inRests
    rw [if_pos inRests]
    obtain ⟨tail, _, listed⟩ := holds
    exact ⟨tail, listed⟩
  · rename_i outside
    rw [if_neg outside]
    exact ⟨_, holds⟩

theorem holds_settled {rests : List String} {θ : ℕ → Expr} {witness : Bindings} {name : String}
    (holds : OrderedRows.Holds rests θ witness name) (inRests : name ∈ rests) :
    ∃ tail, witness.find? (·.1 == name) = some (name, .collection .vec tail none) := by
  unfold OrderedRows.Holds at holds
  rw [if_pos inRests] at holds
  obtain ⟨tail, value, -⟩ := holds
  refine ⟨tail, ?_⟩
  cases found : witness.find? (·.1 == name) with
  | none => simp [lookupOrFvar, applyBindings, found] at value
  | some entry =>
      have keyed := OrderedMatching.find_named found
      rw [keyed] at found ⊢
      simp only [lookupOrFvar, applyBindings, found] at value
      rw [value]

/-- The instantiation that a witness determines, with the rests as lists. -/
noncomputable def valuesOf (rests : List String) (witness : Bindings) : ℕ → Expr :=
  Function.extend labelCode (valueRow rests witness) (fun _ => .sym 0)

theorem holds_valuesOf {rests : List String} {witness : Bindings} (settled : Settled witness rests) (name : String) :
    OrderedRows.Holds rests (valuesOf rests witness) witness name := by
  have valued : valuesOf rests witness (labelCode name) = valueRow rests witness name :=
    labelCode_injective.extend_apply _ _ name
  unfold OrderedRows.Holds
  split
  · rename_i inRests
    obtain ⟨tail, found⟩ := settled name inRests
    have value : lookupOrFvar witness name = .collection .vec tail none := by
      simp [lookupOrFvar, applyBindings, found]
    exact ⟨tail, value, by rw [valued, valueRow, if_pos inRests, value]⟩
  · rename_i outside
    rw [valued, valueRow, if_neg outside]

theorem Flows.bound_last {settled : List String} {bags : List (String × CollType)} :
    ∀ {bound : List String} {premises : List Premise} {last : List String},
      Flows settled bags bound premises last → ∀ name ∈ bound, name ∈ last
  | _, _, _, .nil, _, inside => inside
  | _, _, _, .query _ _ flows, name, inside => Flows.bound_last flows name (List.mem_append_left _ inside)
  | _, _, _, .step _ _ _ _ _ flows, name, inside => Flows.bound_last flows name (List.mem_append_left _ inside)
  | _, _, _, .fresh _ _ flows, name, inside => Flows.bound_last flows name inside
  | _, _, _, .forAll _ flows, name, inside => Flows.bound_last flows name inside

theorem encodeList_ne_fvar (items : List Pattern) (name : String) : encodeList items ≠ encode (.fvar name) := by
  cases items with
  | nil => simp [encodeList, encode]
  | cons item items =>
      simp only [encodeList, encode, ne_eq, Expr.app.injEq, not_and]
      intro same
      cases item <;> simp [encode] at same

/-- The value a witness gives a name, read off the instantiation, when the instantiation gives it a name. -/
theorem lookup_of_name_row {rests : List String} {θ : ℕ → Expr} {witness : Bindings} {name other : String}
    (holds : OrderedRows.Holds rests θ witness name) (row : θ (labelCode name) = encode (.fvar other)) :
    lookupOrFvar witness name = .fvar other := by
  unfold OrderedRows.Holds at holds
  split at holds
  · obtain ⟨tail, -, listed⟩ := holds
    exact absurd (listed.symm.trans row) (encodeList_ne_fvar tail other)
  · exact encode_injective (holds.symm.trans row)

/-- What a name holds is the same under bindings that agree on it. -/
theorem holds_of_agree {rests : List String} {θ : ℕ → Expr} {first second : Bindings} {name : String}
    (holds : Holds rests θ first name) (same : lookupOrFvar second name = lookupOrFvar first name) :
    Holds rests θ second name := by
  unfold OrderedRows.Holds at holds ⊢
  split at holds
  · rename_i inRests
    rw [if_pos inRests]
    obtain ⟨tail, value, listed⟩ := holds
    exact ⟨tail, same.trans value, listed⟩
  · rename_i outside
    rw [if_neg outside, same]
    exact holds

/-- What a name holds carries over to another instantiation and other bindings that give it the same value. -/
theorem holds_transfer {rests rests' : List String} {θ θ' : ℕ → Expr} {first second : Bindings} {name : String}
    (holds : Holds rests θ first name) (row : θ' (labelCode name) = θ (labelCode name))
    (same : lookupOrFvar second name = lookupOrFvar first name) (member : name ∈ rests' ↔ name ∈ rests) :
    Holds rests' θ' second name := by
  unfold OrderedRows.Holds at holds ⊢
  by_cases inRests : name ∈ rests
  · rw [if_pos inRests] at holds
    rw [if_pos (member.mpr inRests)]
    obtain ⟨tail, value, listed⟩ := holds
    exact ⟨tail, same.trans value, row.trans listed⟩
  · rw [if_neg inRests] at holds
    rw [if_neg fun inside => inRests (member.mp inside), row, holds, same]

/-- **Names read at the names bound so far**: at the instantiation that reads the names not bound yet as themselves,
each name a premise mentions holds at the bindings restricted to the bound names. -/
theorem holds_reading {rests : List String} {θ : ℕ → Expr} {witness reading : Bindings} {bound mentioned : List String}
    (restsBound : ∀ name ∈ rests, name ∈ bound) (boundHolds : ∀ name ∈ bound, OrderedRows.Holds rests θ witness name)
    (reads : ∀ name, lookupOrFvar reading name = if name ∈ bound then lookupOrFvar witness name else .fvar name)
    {name : String} (inside : name ∈ mentioned) :
    OrderedRows.Holds rests (literalValues θ (unboundIn bound mentioned)) reading name := by
  by_cases inBound : name ∈ bound
  · refine holds_transfer (boundHolds name inBound) (literalValues_of_not_mem fun other member same => ?_)
      (by rw [reads, if_pos inBound]) Iff.rfl
    rw [labelCode_injective same] at member
    exact (mem_unboundIn.mp member).2 inBound
  · have notRest : name ∉ rests := fun inRests => inBound (restsBound name inRests)
    unfold OrderedRows.Holds
    rw [if_neg notRest, literalValues_of_mem (mem_unboundIn.mpr ⟨inside, inBound⟩), reads, if_neg inBound]

theorem holds_restrict {rests : List String} {θ : ℕ → Expr} {witness : Bindings} {bound mentioned : List String}
    (restsBound : ∀ name ∈ rests, name ∈ bound) (boundHolds : ∀ name ∈ bound, OrderedRows.Holds rests θ witness name)
    {name : String} (inside : name ∈ mentioned) :
    OrderedRows.Holds rests (literalValues θ (unboundIn bound mentioned)) (restrict witness bound) name :=
  holds_reading restsBound boundHolds (StepPremises.lookupOrFvar_restrict witness bound) inside

/-- **A literal reading changes nothing** where the names are already read as themselves. -/
theorem literalValues_eq {θ : ℕ → Expr} {unbound : List String}
    (literal : ∀ name ∈ unbound, θ (labelCode name) = encode (.fvar name)) : literalValues θ unbound = θ := by
  funext x
  simp only [literalValues]
  split
  · rename_i name found
    have isName := List.find?_some found
    simp only [beq_iff_eq] at isName
    subst isName
    exact (literal name (List.mem_of_find?_eq_some found)).symm
  · rfl

/-- **What a name holds determines its value.** -/
theorem holds_lookup_unique {rests : List String} {θ : ℕ → Expr} {first second : Bindings} {name : String}
    (one : Holds rests θ first name) (two : Holds rests θ second name) :
    lookupOrFvar first name = lookupOrFvar second name := by
  unfold OrderedRows.Holds at one two
  by_cases inRests : name ∈ rests
  · rw [if_pos inRests] at one two
    obtain ⟨tail, value, listed⟩ := one
    obtain ⟨tail', value', listed'⟩ := two
    rw [value, value', encodeList_inj _ _ (listed.symm.trans listed')]
  · rw [if_neg inRests] at one two
    exact encode_injective (one.symm.trans two)

/-- **A value determines the row a name holds.** -/
theorem holds_row_unique {rests rests' : List String} {θ θ' : ℕ → Expr} {first second : Bindings} {name : String}
    (one : Holds rests θ first name) (two : Holds rests' θ' second name) (member : name ∈ rests' ↔ name ∈ rests)
    (same : lookupOrFvar second name = lookupOrFvar first name) : θ' (labelCode name) = θ (labelCode name) := by
  unfold OrderedRows.Holds at one two
  by_cases inRests : name ∈ rests
  · rw [if_pos inRests] at one
    rw [if_pos (member.mpr inRests)] at two
    obtain ⟨tail, value, listed⟩ := one
    obtain ⟨tail', value', listed'⟩ := two
    rw [same, value] at value'
    simp only [Pattern.collection.injEq, true_and, and_true] at value'
    rw [listed, listed', value']
  · rw [if_neg inRests] at one
    rw [if_neg fun inside => inRests (member.mp inside)] at two
    rw [one, two, same]

/-! ## The goals of premises -/

section Scope

variable {rests avoid : List String} {sites : Pattern}

theorem stepGoals_scope {bound : List String} {next next' : ℕ} {premise : Premise} {source target : Pattern}
    {goals : List Goal} (lowered : stepGoals rests avoid sites bound next premise source target = some (goals, next')) :
    next ≤ next' ∧ ∀ u ∈ goals.flatMap goalUnknowns, InScope avoid (names source ++ names target) next next' u := by
  simp only [stepGoals, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
  obtain ⟨⟨sourceRow, sourceGoals, middle⟩, sourceLowered, targetRow, targetLowered, rfl, rfl⟩ := lowered
  obtain ⟨ordered, sourceScope⟩ := buildRow_scope source sourceLowered
  refine ⟨ordered, fun u inside => ?_⟩
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, goalUnknowns,
    List.mem_append] at inside
  rcases inside with inSourceGoals | inSourceRow | inTargetRow
  · obtain ⟨g', gIn, inG⟩ := List.mem_flatMap.mp inSourceGoals
    obtain ⟨g, member, rfl⟩ := List.mem_map.mp gIn
    exact (sourceScope u (List.mem_append_right _ (List.mem_flatMap.mpr ⟨g, member, (goalUnknowns_literal g inG).1⟩))).widen
      (fun _ inside => List.mem_append_left _ inside) le_rfl le_rfl
  · exact (sourceScope u (List.mem_append_left _ (mem_unknowns_literalize inSourceRow))).widen
      (fun _ inside => List.mem_append_left _ inside) le_rfl le_rfl
  · rw [unknowns_lower target targetLowered] at inTargetRow
    obtain ⟨name, inTarget, rfl⟩ := List.mem_map.mp inTargetRow
    exact .inl ⟨name, List.mem_append_right _ inTarget, rfl⟩

theorem mem_nextBound {bound : List String} {premise : Premise} {name : String}
    (inside : name ∈ nextBound bound premise) : name ∈ bound ∨ name ∈ premiseNamesOf premise := by
  cases premise <;> simp_all [nextBound, premiseNamesOf] <;> tauto

theorem premiseNames_later {bound : List String} {premise : Premise} {premises : List Premise} {name : String}
    (inside : name ∈ premiseNames premises ++ nextBound bound premise) :
    name ∈ premiseNames (premise :: premises) ++ bound := by
  simp only [premiseNames, List.flatMap_cons, List.mem_append] at inside ⊢
  rcases inside with inLater | inNext
  · exact .inl (.inr inLater)
  · rcases mem_nextBound inNext with inBound | inHere
    · exact .inr inBound
    · exact .inl (.inl inHere)

theorem premiseGoal_scope {bound : List String} {next next' : ℕ} {premise : Premise} {goals : List Goal}
    (lowered : premiseGoal rests avoid sites bound next premise = some (goals, next')) :
    next ≤ next' ∧ ∀ u ∈ goals.flatMap goalUnknowns, InScope avoid (premiseNamesOf premise ++ bound) next next' u := by
  suffices plain : next ≤ next' ∧ ∀ u ∈ goals.flatMap goalUnknowns,
      InScope avoid (premiseNamesOf premise ++ bound) next next' u from plain
  cases premise with
  | relationQuery relation arguments =>
      simp only [premiseGoal, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
      obtain ⟨row, rowLowered, rfl, rfl⟩ := lowered
      refine ⟨le_rfl, fun u inside => ?_⟩
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, goalUnknowns, List.mem_append] at inside
      have inRow : u ∈ unknowns row := inside.elim mem_unknowns_literalize id
      simp only [unknowns_lowerThen arguments rowLowered, RootRewritesOnTheStep.unknowns_symTerm, List.append_nil,
        List.mem_map] at inRow
      obtain ⟨name, inArguments, rfl⟩ := inRow
      exact .inl ⟨name, by simp [premiseNamesOf, inArguments], rfl⟩
  | freshness condition =>
      simp only [premiseGoal, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
      obtain ⟨termRow, termLowered, rfl, rfl⟩ := lowered
      refine ⟨le_rfl, fun u inside => ?_⟩
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, goalUnknowns,
        RootRewritesOnTheStep.unknowns_symTerm, List.mem_append] at inside
      rcases inside with inVar | inTerm
      · have isVar := mem_unknowns_literalize inVar
        simp only [DemandTransformation.unknowns_unknown, List.mem_singleton] at isVar
        subst isVar
        exact .inl ⟨condition.varName, by simp [premiseNamesOf], rfl⟩
      · have inRow := mem_unknowns_literalize inTerm
        rw [unknowns_lower condition.term termLowered] at inRow
        obtain ⟨name, inNames, rfl⟩ := List.mem_map.mp inRow
        exact .inl ⟨name, by simp [premiseNamesOf, inNames], rfl⟩
  | congruence source target =>
      obtain ⟨ordered, scope⟩ := stepGoals_scope lowered
      exact ⟨ordered, fun u inside => (scope u inside).widen (fun _ member => List.mem_append_left _ member)
        le_rfl le_rfl⟩
  | scopedStep step =>
      obtain ⟨ordered, scope⟩ := stepGoals_scope lowered
      exact ⟨ordered, fun u inside => (scope u inside).widen (fun _ member => List.mem_append_left _ member)
        le_rfl le_rfl⟩
  | forAll collection parameter body =>
      simp only [premiseGoal, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
      obtain ⟨_, -, rfl, rfl⟩ := lowered
      refine ⟨by omega, fun u inside => ?_⟩
      unfold forAllGoals at inside
      split at inside
      · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, goalUnknowns, triple,
          RootRewritesOnTheStep.unknowns_appTerm, Quantified.key, Instantiation.unknowns_toTerm,
          DemandTransformation.unknowns_unknown, unknowns_contextRow, RootRewritesOnTheStep.unknowns_symTerm,
          List.nil_append, List.mem_append, List.mem_singleton, List.mem_map] at inside
        rcases inside with rfl | ⟨name, nameInside, rfl⟩
        · exact .inl ⟨collection, by simp [premiseNamesOf], rfl⟩
        · exact .inl ⟨name, List.mem_append_right _ (List.mem_filter.mp nameInside).1, rfl⟩
      · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, goalUnknowns, triple,
          RootRewritesOnTheStep.unknowns_appTerm, Quantified.key, Instantiation.unknowns_toTerm,
          DemandTransformation.unknowns_unknown, unknowns_contextRow, RootRewritesOnTheStep.unknowns_symTerm,
          List.nil_append, List.mem_append, List.mem_singleton, List.mem_map] at inside
        rcases inside with (inInput | rfl) | rfl | ⟨name, nameInside, rfl⟩
        · have isVar := mem_unknowns_literalize inInput
          simp only [DemandTransformation.unknowns_unknown, List.mem_singleton] at isVar
          subst isVar
          exact .inl ⟨collection, by simp [premiseNamesOf], rfl⟩
        · exact .inr ⟨next, le_rfl, by omega, rfl⟩
        · exact .inr ⟨next, le_rfl, by omega, rfl⟩
        · exact .inl ⟨name, List.mem_append_right _ (List.mem_filter.mp nameInside).1, rfl⟩

/-- **The goals of premises mention the premises' names and their own fresh lists.** -/
theorem premiseGoals_scope : ∀ {bound : List String} {premises : List Premise} {next next' : ℕ} {body : List Goal},
    premiseGoals rests avoid sites bound next premises = some (body, next') →
      next ≤ next' ∧ ∀ u ∈ body.flatMap goalUnknowns, InScope avoid (premiseNames premises ++ bound) next next' u
  | _, [], next, next', body, lowered => by
      simp only [premiseGoals, Option.some.injEq, Prod.mk.injEq] at lowered
      obtain ⟨rfl, rfl⟩ := lowered
      exact ⟨le_rfl, fun u inside => by simp at inside⟩
  | _, premise :: premises, next, next', body, lowered => by
      simp only [premiseGoals, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
      obtain ⟨⟨here, middle⟩, hereLowered, ⟨later, last⟩, laterLowered, same⟩ := lowered
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      obtain ⟨hereOrdered, hereScope⟩ := premiseGoal_scope hereLowered
      obtain ⟨laterOrdered, laterScope⟩ := premiseGoals_scope laterLowered
      refine ⟨le_trans hereOrdered laterOrdered, fun u inside => ?_⟩
      simp only [List.flatMap_append, List.mem_append] at inside
      rcases inside with inHere | inLater
      · exact (hereScope u inHere).widen (fun name member => by
          simp only [premiseNames, List.flatMap_cons, List.mem_append] at member ⊢; tauto) le_rfl laterOrdered
      · exact (laterScope u inLater).widen (fun name member => by
          simp only [premiseNames, List.flatMap_cons, List.mem_append] at member ⊢
          rcases member with inPremises | inNext
          · exact .inl (.inr inPremises)
          · rcases mem_nextBound inNext with inBound | inHere
            · exact .inr inBound
            · exact .inl (.inl inHere)) hereOrdered le_rfl

end Scope

variable {relEnv : RelationEnv} {language : LanguageDef} {program : List Clause}

/-- **Goals that hold at an instance are premises that hold**, under a witness the instance determines. -/
theorem goals_sound (build : BuildClauses program) (forAlls : ForAllClauses program) {rests avoid : List String}
    {sites : Pattern} {D : ℕ → Expr → Expr → Prop}
    (lift : ∀ r x y, D r x y → Derives (premiseRelations relEnv language) program r x y)
    (unfold : Unfolds (premiseRelations relEnv language) program D)
    {S : Pattern → Pattern → Prop} (steps : ∀ (u : Pattern) (w : Expr), D stepRelation (encode u) w → ∃ v, w = encode v ∧ S u v)
    {θ : ℕ → Expr} {settled : List String} {bags : List (String × CollType)} :
    ∀ {bound last : List String} {premises : List Premise} {next next' : ℕ} {body : List Goal},
      (∀ name ∈ rests, name ∈ bound) →
      Flows settled bags bound premises last → premiseGoals rests avoid sites bound next premises = some (body, next') →
      (∀ g ∈ body, goalHolds (premiseRelations relEnv language) D θ g) →
      ∀ witness : Bindings, (∀ name ∈ bound, Holds rests θ witness name) →
        ∃ larger : Bindings, (∀ name ∈ last, Holds rests θ larger name) ∧
          Hold relEnv language S sites (fun _ => True) larger bound premises
  | _, _, _, _, _, _, _, .nil, lowered, _, witness, holds => by
      simp only [premiseGoals, Option.some.injEq, Prod.mk.injEq] at lowered
      exact ⟨witness, holds, trivial⟩
  | bound, _, _, next, _, _, restsBound, .query (relation := relation) (arguments := arguments) _ _ flows, lowered,
      goals, witness, holds => by
      simp only [premiseGoals, premiseGoal, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
      obtain ⟨_, ⟨row, rowLowered, rfl⟩, ⟨later, last'⟩, laterLowered, same⟩ := lowered
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      obtain ⟨relation', request, queried, named, requestIs, valueIs, inRows⟩ | ⟨_, _, never, -⟩ :=
        goals (.query
            { name := labelCode relation
              arguments := [literalize (unboundIn bound (namesList arguments)) row]
              value := row })
          (List.mem_append_left _ (List.mem_singleton_self _))
      swap
      · simp at never
      obtain rfl : relation = relation' := labelCode_injective named
      obtain ⟨captured, -⟩ := lowerThen_captures arguments rowLowered valueIs
      obtain ⟨nextWitness, nextHolds⟩ := exists_witness (rests := rests) (θ := θ) (bound ++ namesList arguments)
        fun name inside => (List.mem_append.mp inside).elim (fun inBound => holds_captured (holds name inBound))
          (captured name)
      obtain ⟨larger, largerHolds, hold⟩ := goals_sound build forAlls lift unfold steps
        (fun name inside => List.mem_append_left _ (restsBound name inside)) flows laterLowered
        (fun g inside => goals g (by simp [inside])) nextWitness nextHolds
      have rowIs := inst_lowerThen arguments rowLowered
        (fun name inside => largerHolds name (Flows.bound_last flows name (List.mem_append_right _ inside)))
        (tail := []) (by simp [encodeList])
      have argumentsAre : arguments.map (applyBindings larger) = queried :=
        encodeList_inj _ _ (by simpa using rowIs.symm.trans valueIs)
      have requestAt := inst_lowerThen (θ := literalValues θ (unboundIn bound (namesList arguments)))
        (witness := restrict larger bound) arguments rowLowered
        (fun name inside => holds_restrict restsBound
          (fun other member => largerHolds other (Flows.bound_last flows other (List.mem_append_left _ member)))
          inside) (tail := []) (by simp [encodeList])
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true, inst_literalize] at requestIs
      have requestAre : arguments.map (applyBindings (restrict larger bound)) = request :=
        encodeList_inj _ _ (by simpa using requestAt.symm.trans requestIs)
      refine ⟨larger, largerHolds, ?_, hold⟩
      show arguments.map (applyBindings larger) ∈
        queryRows relEnv language relation (arguments.map (applyBindings (restrict larger bound)))
      rw [argumentsAre, requestAre]
      exact inRows
  | bound, _, _, next, _, _, restsBound, .step (premise := premise) (source := source) (target := target) endpoints
      _ _ _ _ flows, lowered, goals, witness, holds => by
      simp only [premiseGoals, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
      obtain ⟨⟨here, middle⟩, hereLowered, ⟨later, last'⟩, laterLowered, same⟩ := lowered
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      rw [StepPremises.nextBound_step endpoints] at laterLowered
      rw [premiseGoal_step endpoints] at hereLowered
      simp only [stepGoals, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at hereLowered
      obtain ⟨⟨sourceRow, sourceGoals, middle'⟩, sourceLowered, targetRow, targetLowered, rfl, rfl⟩ := hereLowered
      have sourceHold : ∀ g ∈ sourceGoals, goalHolds (premiseRelations relEnv language)
          (Derives (premiseRelations relEnv language) program) (literalValues θ (unboundIn bound (names source))) g :=
        fun g inside => DemandTransformation.goalHolds_mono lift ((goalHolds_literal g).mp
          (goals (literalGoal (unboundIn bound (names source)) g) (by
            simp only [List.mem_append, List.mem_map]
            exact .inl (.inl ⟨g, inside, rfl⟩))))
      have sourceIs : inst (literalValues θ (unboundIn bound (names source))) sourceRow =
          encode (applyBindingsScoped sites (restrict witness bound) (stepDepth sites premise) source) :=
        buildRow_sound build source sourceLowered (fun name inside => holds_restrict restsBound holds inside)
          sourceHold
      have asked := goals (.ask stepRelation (literalize (unboundIn bound (names source)) sourceRow) targetRow)
        (by simp)
      simp only [goalHolds, inst_literalize] at asked
      rw [sourceIs] at asked
      obtain ⟨v, targetIs, stepped⟩ := steps _ _ asked
      obtain ⟨nextWitness, nextHolds⟩ := exists_witness (rests := rests) (θ := θ) (bound ++ names target)
        fun name inside => (List.mem_append.mp inside).elim (fun inBound => holds_captured (holds name inBound))
          (lower_captures target targetLowered targetIs name)
      obtain ⟨larger, largerHolds, hold⟩ := goals_sound build forAlls lift unfold steps
        (fun name inside => List.mem_append_left _ (restsBound name inside)) flows laterLowered
        (fun g inside => goals g (by simp [inside])) nextWitness nextHolds
      have sourceLarger : applyBindingsScoped sites (restrict larger bound) (stepDepth sites premise) source =
          applyBindingsScoped sites (restrict witness bound) (stepDepth sites premise) source :=
        encode_injective ((buildRow_sound build source sourceLowered (fun name inside => holds_restrict restsBound
          (fun other member => largerHolds other (Flows.bound_last flows other (List.mem_append_left _ member)))
          inside) sourceHold).symm.trans sourceIs)
      have targetLarger : applyBindings larger target = v :=
        encode_injective ((inst_lower target targetLowered fun name inside => largerHolds name
          (Flows.bound_last flows name (List.mem_append_right _ inside))).symm.trans targetIs)
      refine ⟨larger, largerHolds, (StepPremises.premiseHolds_step endpoints).mpr ?_,
        by rw [StepPremises.nextBound_step endpoints]; exact hold⟩
      rw [sourceLarger, targetLarger]
      exact stepped
  | bound, _, _, next, _, _, restsBound, .fresh (condition := condition) _ _ flows, lowered, goals, witness,
      holds => by
      simp only [premiseGoals, premiseGoal, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
      obtain ⟨_, ⟨termRow, termLowered, rfl⟩, ⟨later, last'⟩, laterLowered, same⟩ := lowered
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      obtain ⟨_, _, _, _, never, -⟩ | ⟨name, term, argumentsAre, -, fresh⟩ :=
        goals (.query
            { name := 0
              arguments := [literalize (unboundIn bound (condition.varName :: names condition.term))
                  (.var (labelCode condition.varName)),
                literalize (unboundIn bound (condition.varName :: names condition.term)) termRow]
              value := symTerm 0 }) (List.mem_append_left _ (List.mem_singleton_self _))
      · simp at never
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true, inst_literalize,
        DemandTransformation.inst_unknown] at argumentsAre
      obtain ⟨varIs, termIs⟩ := argumentsAre
      obtain ⟨larger, largerHolds, hold⟩ := goals_sound build forAlls lift unfold steps restsBound flows laterLowered
        (fun g inside => goals g (by simp [inside])) witness holds
      have boundLarger : ∀ name ∈ bound, Holds rests θ larger name :=
        fun name inside => largerHolds name (Flows.bound_last flows name inside)
      refine ⟨larger, largerHolds, ⟨name, lookup_of_name_row
        (holds_restrict (mentioned := condition.varName :: names condition.term) restsBound boundLarger
          List.mem_cons_self) varIs, ?_⟩, hold⟩
      have termAt := inst_lower (θ := literalValues θ (unboundIn bound (condition.varName :: names condition.term)))
        (witness := restrict larger bound) condition.term termLowered fun other inside =>
        holds_restrict restsBound boundLarger (List.mem_cons_of_mem _ inside)
      rw [termIs] at termAt
      rw [← encode_injective termAt]
      exact fresh
  | bound, _, _, next, _, _, restsBound, .forAll (collection := collection) (parameter := parameter)
      (body := premiseBody) bodyFlows flows, lowered, goals, witness, holds => by
      simp only [premiseGoals, premiseGoal, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
      obtain ⟨_, ⟨⟨bodyGoals, bodyNext⟩, bodyLowered, rfl⟩, ⟨later, last'⟩, laterLowered, same⟩ := lowered
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      obtain ⟨q, qIs⟩ : ∃ q, quantifiedAt rests sites bound parameter premiseBody = q := ⟨_, rfl⟩
      rw [qIs] at bodyLowered goals
      have qRests : q.rests = rests.filter (· ≠ parameter) := by rw [← qIs]; rfl
      have qSites : q.sites = sites := by rw [← qIs]; rfl
      have qContext : q.context = bound.filter (· ≠ parameter) := by rw [← qIs]; rfl
      have qParameter : q.parameter = parameter := by rw [← qIs]; rfl
      have qBody : q.body = premiseBody := by rw [← qIs]; rfl
      have bodyAt : premiseGoal q.rests q.avoid q.sites (q.parameter :: q.context) 1 q.body =
          some (bodyGoals, bodyNext) := by
        rw [qSites, qParameter, qContext, qBody]
        exact bodyLowered
      obtain ⟨larger, largerHolds, hold⟩ := goals_sound build forAlls lift unfold steps restsBound flows laterLowered
        (fun g inside => goals g (List.mem_append_right _ inside)) witness holds
      have boundHolds : ∀ name ∈ bound, Holds rests θ larger name :=
        fun name inside => largerHolds name (Flows.bound_last flows name inside)
      -- the collection's elements, and the fact that the quantified premise holds of them
      obtain ⟨kind, elements, looked, listDerived⟩ : ∃ kind elements,
          lookupOrFvar (restrict larger bound) collection = .collection kind elements none ∧
          D forAllRelation (.app (.app (inst θ q.key) (encodeList elements)) (inst θ (contextRow q.context)))
            (.sym 0) := by
        by_cases collectionBound : collection ∉ bound
        · have notRest : collection ∉ rests := fun inRests => collectionBound (restsBound collection inRests)
          have listed := goals (.ask listOfRelation
            (literalize (unboundIn bound [collection]) (.var (labelCode collection)))
            (.var (listUnknown avoid next))) (List.mem_append_left _ (by simp [forAllGoals, notRest]))
          simp only [goalHolds, inst_literalize, DemandTransformation.inst_unknown,
            literalValues_of_mem (mem_unboundIn.mpr ⟨List.mem_singleton_self collection, collectionBound⟩)] at listed
          obtain ⟨kind, collectionRow⟩ := listOf_sound forAlls.onlyListOfs (lift _ _ _ listed)
          obtain ⟨_, valueIs, -⟩ := PatternRows.encode_closed_inv collectionRow.symm
          cases valueIs
        rw [not_not] at collectionBound
        rw [StepPremises.lookupOrFvar_restrict, if_pos collectionBound]
        have unboundNone : unboundIn bound [collection] = [] := by simp [unboundIn, collectionBound]
        have held := boundHolds collection collectionBound
        unfold OrderedRows.Holds at held
        by_cases inRests : collection ∈ rests
        · rw [if_pos inRests] at held
          obtain ⟨tail, value, listed⟩ := held
          have asked := goals (.ask forAllRelation (triple q.key (.var (labelCode collection)) (contextRow q.context))
            (symTerm 0)) (List.mem_append_left _ (by simp [forAllGoals, inRests]))
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
            RootRewritesOnTheStep.inst_symTerm] at asked
          rw [listed] at asked
          exact ⟨.vec, tail, value, asked⟩
        · rw [if_neg inRests] at held
          have listed := goals (.ask listOfRelation
            (literalize (unboundIn bound [collection]) (.var (labelCode collection)))
            (.var (listUnknown avoid next))) (List.mem_append_left _ (by simp [forAllGoals, inRests]))
          have asked := goals (.ask forAllRelation (triple q.key (.var (listUnknown avoid next)) (contextRow q.context))
            (symTerm 0)) (List.mem_append_left _ (by simp [forAllGoals, inRests]))
          rw [unboundNone] at listed
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
            RootRewritesOnTheStep.inst_symTerm, inst_literalize, literalValues_nil] at listed asked
          obtain ⟨kind, collectionRow⟩ := listOf_sound forAlls.onlyListOfs (lift _ _ _ listed)
          obtain ⟨elements, valueIs, listIs⟩ := PatternRows.encode_closed_inv (collectionRow.symm.trans held)
          rw [listIs] at asked
          exact ⟨kind, elements, valueIs, asked⟩
      -- each element: the clause for a first element holds of it, and its body's goals are its premise
      have chain : ∀ items : List Pattern,
          D forAllRelation (.app (.app (inst θ q.key) (encodeList items)) (inst θ (contextRow q.context))) (.sym 0) →
          ∀ element ∈ items, ∃ result : Bindings, True ∧
            (∀ name ∈ parameter :: bound,
              lookupOrFvar result name = lookupOrFvar (bindParameter larger parameter element) name) ∧
            StepPremises.PremiseHolds relEnv language S sites (fun _ => True) (scopeOf bound parameter) result
              premiseBody := by
        intro items
        induction items with
        | nil => exact fun _ element inside => absurd inside List.not_mem_nil
        | cons head tail ih =>
          intro derived element inside
          obtain ⟨c, member, isForAll, θc, input, -, clauseGoals⟩ := unfold _ _ derived
          obtain ⟨q', cs, clausesAre, inClauses⟩ := forAlls.onlyForAlls c member isForAll
          simp only [Quantified.clauses, Option.map_eq_some_iff] at clausesAre
          obtain ⟨bodyGoals', bodyLowered', rfl⟩ := clausesAre
          simp only [List.mem_cons, List.not_mem_nil, or_false] at inClauses
          rcases inClauses with rfl | rfl
          · simp [Quantified.nilClause, triple, encodeList] at input
          simp only [Quantified.consClause, triple, RootRewritesOnTheStep.inst_appTerm,
            DemandTransformation.inst_unknown, encodeList, Expr.app.injEq] at input
          simp only [Quantified.consClause] at clauseGoals
          obtain ⟨⟨keyIs, headIs, tailIs⟩, contextIs⟩ := input
          obtain ⟨restsSame, sitesSame, contextSame, parameterSame, bodySame⟩ := Quantified.key_same keyIs
          obtain ⟨-, -, goalsSame⟩ :=
            Quantified.clauses_of_key restsSame sitesSame contextSame parameterSame bodySame
          have sameGoals : bodyGoals' = (bodyGoals, bodyNext) :=
            Option.some.inj (bodyLowered'.symm.trans (goalsSame.trans bodyAt))
          subst sameGoals
          rcases List.mem_cons.mp inside with same | later
          · rw [same]
            rw [parameterSame, qParameter] at headIs
            rw [contextSame] at contextIs
            have contextAgree := inst_contextRow_agree contextIs
            have bodyWitness : ∀ name ∈ scopeOf bound parameter,
                Holds q.rests θc (bindParameter larger parameter head) name := by
              intro name inScope
              by_cases named : name = parameter
              · rw [named]
                unfold OrderedRows.Holds
                rw [if_neg (show parameter ∉ q.rests by rw [qRests]; simp), StepPremises.lookupOrFvar_bindParameter,
                  if_pos rfl]
                exact headIs
              · have inBound : name ∈ bound := (mem_scopeOf.mp inScope).resolve_left named
                exact holds_transfer (boundHolds name inBound)
                  (contextAgree name (by rw [qContext]; simp [inBound, named]))
                  (by rw [StepPremises.lookupOrFvar_bindParameter, if_neg named])
                  (by rw [qRests]; simp [named])
            have bodyRests : ∀ name ∈ q.rests, name ∈ scopeOf bound parameter := fun name inside => by
              rw [qRests] at inside
              exact mem_scopeOf.mpr (.inr (restsBound name (List.mem_filter.mp inside).1))
            obtain ⟨result, resultHolds, resultHold⟩ := goals_sound build forAlls lift unfold steps bodyRests bodyFlows
              (premiseGoals_single bodyLowered) (fun g inBody => clauseGoals g (List.mem_append_left _ inBody))
              (bindParameter larger parameter head) bodyWitness
            refine ⟨result, trivial, fun name named => ?_, resultHold.1⟩
            have inScope : name ∈ scopeOf bound parameter := mem_scopeOf.mpr (List.mem_cons.mp named)
            exact holds_lookup_unique (resultHolds name (Flows.bound_last bodyFlows name inScope))
              (bodyWitness name inScope)
          · have tailAsked := clauseGoals (.ask forAllRelation (triple q'.key (.var (listUnknown q'.avoid 0))
              (contextRow q'.context)) (symTerm 0)) (List.mem_append_right _ List.mem_cons_self)
            simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
              RootRewritesOnTheStep.inst_symTerm] at tailAsked
            rw [keyIs, tailIs, contextIs] at tailAsked
            exact ih tailAsked element later
      exact ⟨larger, largerHolds, ⟨kind, elements, looked, chain elements listDerived⟩, hold⟩

/-- **Restoring the names read as themselves**: an instantiation that agrees with the literal reading outside some
fresh unknowns is the literal reading of one that agrees with the original outside them. -/
theorem literal_reconcile {avoid unbound : List String} {next next' : ℕ} {θ θ₀ : ℕ → Expr}
    (named : ∀ name ∈ unbound, name ∈ avoid) (agree : AgreeOutside avoid next next' (literalValues θ unbound) θ₀) :
    ∃ θ', AgreeOutside avoid next next' θ θ' ∧ literalValues θ' unbound = θ₀ := by
  refine ⟨fun x => match unbound.find? (fun name => labelCode name == x) with
    | some _ => θ x
    | none => θ₀ x, fun u untouched => ?_, funext fun x => ?_⟩
  · simp only
    split
    · rfl
    · rename_i absent
      rw [agree u untouched]
      simp only [literalValues, absent]
  · simp only [literalValues]
    split
    · rename_i name found
      have isName := List.find?_some found
      simp only [beq_iff_eq] at isName
      subst isName
      have same := agree (labelCode name) (untouched_name (named name (List.mem_of_find?_eq_some found)) _ _)
      rw [same, literalValues_of_mem (List.mem_of_find?_eq_some found)]
    · rfl

/-- **Premises that hold are goals that hold**, at an instantiation that a witness determines on the names and that
gives the premises' fresh lists their values. -/
theorem goals_complete (build : BuildClauses program) (forAlls : ForAllClauses program) {S : Pattern → Pattern → Prop}
    (steps : ∀ u v, isData u = true → S u v →
      Derives (premiseRelations relEnv language) program stepRelation (encode u) (encode v))
    {rests avoid : List String} {sites : Pattern} {witness : Bindings} (dataOn : DataOn witness)
    {settled : List String} {bags : List (String × CollType)} (settledOn : Settled witness settled)
    (bagsOn : BagSettled witness bags) :
    ∀ {bound last : List String} {premises : List Premise} {next next' : ℕ} {body : List Goal},
      Flows settled bags bound premises last → premiseGoals rests avoid sites bound next premises = some (body, next') →
      (∀ name ∈ settled, name ∈ bound) → (∀ pair ∈ bags, pair.1 ∈ bound) → (∀ name ∈ rests, name ∈ bound) →
      QuantifiedPresent program (premisesQuantified rests sites bound premises) →
      (∀ name ∈ premiseNames premises ++ bound, name ∈ avoid) →
      Hold relEnv language S sites DataOn witness bound premises →
      ∀ {θ : ℕ → Expr}, (∀ name ∈ avoid, Holds rests θ witness name) →
      ∃ θ', AgreeOutside avoid next next' θ θ' ∧
        ∀ g ∈ body, goalHolds (premiseRelations relEnv language) (Derives (premiseRelations relEnv language) program)
          θ' g
  | _, _, _, _, _, _, .nil, lowered, _, _, _, _, _, _, θ, _ => by
      simp only [premiseGoals, Option.some.injEq, Prod.mk.injEq] at lowered
      obtain ⟨rfl, rfl⟩ := lowered
      exact ⟨θ, AgreeOutside.refl θ, fun _ inside => absurd inside List.not_mem_nil⟩
  | bound, _, _, next, _, _, .query (relation := relation) (arguments := arguments) _ _ flows, lowered, settledBound,
      bagsBound, restsBound, present, named, hold, θ, agree => by
      simp only [premiseGoals, premiseGoal, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
      obtain ⟨_, ⟨row, rowLowered, rfl⟩, ⟨later, last'⟩, laterLowered, same⟩ := lowered
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      have argumentsNamed : ∀ name ∈ namesList arguments, name ∈ avoid :=
        fun name inside => named name (by simp [premiseNames, premiseNamesOf, inside])
      obtain ⟨θ', agree', laterHold⟩ := goals_complete build forAlls steps dataOn settledOn bagsOn flows laterLowered
        (fun name inside => List.mem_append_left _ (settledBound name inside))
        (fun pair inside => List.mem_append_left _ (bagsBound pair inside))
        (fun name inside => List.mem_append_left _ (restsBound name inside))
        (fun q inside => present q (List.mem_append_right _ inside))
        (fun name inside => named name (premiseNames_later inside)) hold.2 agree
      refine ⟨θ', agree', fun g inside => ?_⟩
      rcases List.mem_append.mp inside with inHere | inLater
      · simp only [List.mem_singleton] at inHere
        subst inHere
        have rowIs := inst_lowerThen arguments rowLowered
          (fun name inside => holds_congr (agree' _ (untouched_name (argumentsNamed name inside) _ _))
            (agree name (argumentsNamed name inside))) (tail := []) (by simp [encodeList])
        rw [List.append_nil] at rowIs
        have boundHolds : ∀ name ∈ bound, Holds rests θ' witness name := fun name inside =>
          holds_congr (agree' _ (untouched_name (named name (List.mem_append_right _ inside)) _ _))
            (agree name (named name (List.mem_append_right _ inside)))
        have requestIs := inst_lowerThen (θ := literalValues θ' (unboundIn bound (namesList arguments)))
          (witness := restrict witness bound) arguments rowLowered
          (fun name inside => holds_restrict restsBound boundHolds inside) (tail := []) (by simp [encodeList])
        rw [List.append_nil] at requestIs
        exact .inl ⟨relation, _, _, rfl, by simp only [List.map_cons, List.map_nil, inst_literalize, requestIs],
          rowIs, hold.1⟩
      · exact laterHold g inLater
  | bound, _, _, next, _, _, .step (premise := premise) (source := source) (target := target) endpoints
      sourceCanonical _ restsSettled bagsWithin flows, lowered, settledBound, bagsBound, restsBound, present, named,
      hold, θ, agree => by
      simp only [premiseGoals, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
      obtain ⟨⟨here, middle⟩, hereLowered, ⟨later, last'⟩, laterLowered, same⟩ := lowered
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      rw [StepPremises.nextBound_step endpoints] at laterLowered
      rw [premiseGoal_step endpoints] at hereLowered
      have hereScope := stepGoals_scope hereLowered
      simp only [stepGoals, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at hereLowered
      obtain ⟨⟨sourceRow, sourceGoals, middle'⟩, sourceLowered, targetRow, targetLowered, rfl, rfl⟩ := hereLowered
      have endpointsNamed : ∀ name ∈ names source ++ names target, name ∈ avoid := by
        intro name inside
        apply named name
        simp only [premiseNames, List.flatMap_cons, List.mem_append, premiseNamesOf_step endpoints]
        exact .inl (.inl (List.mem_append.mp inside))
      have unboundNamed : ∀ name ∈ unboundIn bound (names source), name ∈ avoid := fun name inside =>
        endpointsNamed name (List.mem_append_left _ (mem_unboundIn.mp inside).1)
      have boundHolds : ∀ name ∈ bound, Holds rests θ witness name := fun name inside =>
        agree name (named name (List.mem_append_right _ inside))
      obtain ⟨θ₀, agree₀, sourceIs, sourceHold⟩ := buildRow_complete (θ := literalValues θ (unboundIn bound (names source)))
        build source sourceLowered
        (fun name inside => endpointsNamed name (List.mem_append_left _ inside))
        (StepPremises.bagSettled_restrict (fun pair inside => bagsOn pair (bagsWithin pair inside))
          fun pair inside => bagsBound pair (bagsWithin pair inside))
        (fun name inside => holds_restrict restsBound boundHolds inside)
      obtain ⟨θ₁, agree₁, literalIs⟩ := literal_reconcile unboundNamed agree₀
      have agreeLater : ∀ name ∈ avoid, Holds rests θ₁ witness name :=
        fun name inside => holds_congr (agree₁ _ (untouched_name inside _ _)) (agree name inside)
      obtain ⟨θ₂, agree₂, laterHold⟩ := goals_complete build forAlls steps dataOn settledOn bagsOn flows laterLowered
        (fun name inside => List.mem_append_left _ (settledBound name inside))
        (fun pair inside => List.mem_append_left _ (bagsBound pair inside))
        (fun name inside => List.mem_append_left _ (restsBound name inside))
        (fun q inside => present q (by
          rw [premisesQuantified_cons, StepPremises.nextBound_step endpoints]
          exact List.mem_append_right _ inside))
        (fun name inside => named name (premiseNames_later (by
          rw [StepPremises.nextBound_step endpoints]
          exact inside)))
        (by rw [← StepPremises.nextBound_step endpoints]; exact hold.2) agreeLater
      obtain ⟨sourceOrdered, sourceScope⟩ := buildRow_scope source sourceLowered
      obtain ⟨laterOrdered, -⟩ := premiseGoals_scope laterLowered
      have sourceStays : ∀ u ∈ unknowns sourceRow ++ sourceGoals.flatMap goalUnknowns,
          literalValues θ₂ (unboundIn bound (names source)) u = θ₀ u := by
        intro u inside
        rw [← literalIs]
        simp only [literalValues]
        split
        · rfl
        · exact agree₂ u ((sourceScope u inside).untouched
            (fun name member => endpointsNamed name (List.mem_append_left _ member)) (.inl le_rfl))
      have targetIs : inst θ₂ targetRow = encode (applyBindings witness target) :=
        inst_lower target targetLowered fun name inside =>
          holds_congr (agree₂ _ (untouched_name (endpointsNamed name (List.mem_append_right _ inside)) _ _))
            (agreeLater name (endpointsNamed name (List.mem_append_right _ inside)))
      refine ⟨θ₂, agree₁.trans agree₂ sourceOrdered laterOrdered, fun g inside => ?_⟩
      simp only [List.append_assoc, List.mem_append, List.mem_singleton] at inside
      rcases inside with inSource | rfl | inLater
      · obtain ⟨g₀, g₀In, rfl⟩ := List.mem_map.mp inSource
        exact (goalHolds_literal g₀).mpr
          (goals_agree (fun u inU => sourceStays u (List.mem_append_right _ inU)) sourceHold g₀ g₀In)
      · simp only [goalHolds, inst_literalize]
        rw [DemandTransformation.inst_agree sourceRow fun u inU => sourceStays u (List.mem_append_left _ inU),
          sourceIs, targetIs]
        exact steps _ _ (Instantiation.scoped_data (StepPremises.dataOn_restrict dataOn bound) sites _ source
          sourceCanonical
          (StepPremises.settled_restrict
            (fun rest inside => settledOn rest (restsSettled rest (List.mem_append_left _ inside)))
            fun rest inside => settledBound rest (restsSettled rest (List.mem_append_left _ inside)))
          (StepPremises.bagSettled_restrict (fun pair inside => bagsOn pair (bagsWithin pair inside))
            fun pair inside => bagsBound pair (bagsWithin pair inside)))
          ((StepPremises.premiseHolds_step endpoints).mp hold.1)
      · exact laterHold g inLater
  | bound, _, _, next, _, _, .fresh (condition := condition) _ _ flows, lowered, settledBound, bagsBound, restsBound,
      present, named, hold, θ, agree => by
      simp only [premiseGoals, premiseGoal, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
      obtain ⟨_, ⟨termRow, termLowered, rfl⟩, ⟨later, last'⟩, laterLowered, same⟩ := lowered
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      have conditionNamed : ∀ name ∈ condition.varName :: names condition.term, name ∈ avoid := by
        intro name inside
        apply named name
        simp only [premiseNames, List.flatMap_cons, premiseNamesOf, List.mem_append]
        exact .inl (.inl inside)
      obtain ⟨θ', agree', laterHold⟩ := goals_complete build forAlls steps dataOn settledOn bagsOn flows laterLowered
        settledBound bagsBound restsBound (fun q inside => present q (List.mem_append_right _ inside))
        (fun name inside => named name (premiseNames_later inside)) hold.2 agree
      refine ⟨θ', agree', fun g inside => ?_⟩
      rcases List.mem_append.mp inside with inHere | inLater
      · simp only [List.mem_singleton] at inHere
        subst inHere
        obtain ⟨name, looked, fresh⟩ := hold.1
        have boundHolds : ∀ name ∈ bound, Holds rests θ' witness name := fun name inside =>
          holds_congr (agree' _ (untouched_name (named name (List.mem_append_right _ inside)) _ _))
            (agree name (named name (List.mem_append_right _ inside)))
        have varHolds := holds_restrict (mentioned := condition.varName :: names condition.term) restsBound boundHolds
          List.mem_cons_self
        have nameRow : literalValues θ' (unboundIn bound (condition.varName :: names condition.term))
            (labelCode condition.varName) = encode (.fvar name) := by
          unfold OrderedRows.Holds at varHolds
          split at varHolds
          · obtain ⟨tail, value, -⟩ := varHolds
            rw [value] at looked
            cases looked
          · rw [varHolds, looked]
        refine .inr ⟨name, applyBindings (restrict witness bound) condition.term, ?_, rfl, fresh⟩
        simp only [List.map_cons, List.map_nil, inst_literalize, DemandTransformation.inst_unknown, nameRow,
          inst_lower (θ := literalValues θ' (unboundIn bound (condition.varName :: names condition.term)))
            (witness := restrict witness bound) condition.term termLowered fun other inside =>
            holds_restrict restsBound boundHolds (List.mem_cons_of_mem _ inside)]
      · exact laterHold g inLater
  | bound, _, _, next, _, _, .forAll (collection := collection) (parameter := parameter) (body := premiseBody)
      bodyFlows flows, lowered, settledBound, bagsBound, restsBound, present, named,
      hold, θ, agree => by
      simp only [premiseGoals, premiseGoal, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
      obtain ⟨_, ⟨⟨bodyGoals, bodyNext⟩, bodyLowered, rfl⟩, ⟨later, last'⟩, laterLowered, same⟩ := lowered
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      have presentHere := present (quantifiedAt rests sites bound parameter premiseBody)
        (by rw [premisesQuantified_cons]; exact List.mem_append_left _ List.mem_cons_self)
      have presentBody : QuantifiedPresent program
          (premisesQuantified (rests.filter (· ≠ parameter)) sites (scopeOf bound parameter) [premiseBody]) :=
        fun q' inside => present q' (by
          rw [premisesQuantified_cons]
          refine List.mem_append_left _ (List.mem_cons_of_mem _ ?_)
          simpa [premisesQuantified] using inside)
      obtain ⟨q, qIs⟩ : ∃ q, quantifiedAt rests sites bound parameter premiseBody = q := ⟨_, rfl⟩
      rw [qIs] at bodyLowered presentHere ⊢
      have qRests : q.rests = rests.filter (· ≠ parameter) := by rw [← qIs]; rfl
      have qSites : q.sites = sites := by rw [← qIs]; rfl
      have qContext : q.context = bound.filter (· ≠ parameter) := by rw [← qIs]; rfl
      have qParameter : q.parameter = parameter := by rw [← qIs]; rfl
      have qBody : q.body = premiseBody := by rw [← qIs]; rfl
      have qAvoid : q.avoid = parameter :: bound.filter (· ≠ parameter) ++ premiseNamesOf premiseBody := by
        rw [← qIs]; rfl
      rw [← qRests] at presentBody
      have bodyAt : premiseGoal q.rests q.avoid q.sites (q.parameter :: q.context) 1 q.body =
          some (bodyGoals, bodyNext) := by
        rw [qSites, qParameter, qContext, qBody]
        exact bodyLowered
      have clausesAre : q.clauses = some [q.nilClause, q.consClause bodyGoals] := by
        simp [Quantified.clauses, bodyAt]
      have nilIn : q.nilClause ∈ program := presentHere _ clausesAre _ List.mem_cons_self
      have consIn : q.consClause bodyGoals ∈ program :=
        presentHere _ clausesAre _ (List.mem_cons_of_mem _ List.mem_cons_self)
      obtain ⟨kind, elements, lookedAt, each⟩ := hold.1
      have collectionBound : collection ∈ bound := by
        by_contra outside
        rw [StepPremises.lookupOrFvar_restrict, if_neg outside] at lookedAt
        cases lookedAt
      have looked : lookupOrFvar witness collection = .collection kind elements none := by
        rw [StepPremises.lookupOrFvar_restrict, if_pos collectionBound] at lookedAt
        exact lookedAt
      have unboundNone : unboundIn bound [collection] = [] := by simp [unboundIn, collectionBound]
      have collectionAvoid : collection ∈ avoid :=
        named collection (List.mem_append_left _ (by simp [premiseNames, premiseNamesOf]))
      -- the later premises, with the list unknown given the elements
      have agree₁ : AgreeOutside avoid next (next + 1) θ
          (Function.update θ (listUnknown avoid next) (encodeList elements)) :=
        fun u untouched => Function.update_of_ne (untouched next le_rfl (Nat.lt_succ_self next)) _ _
      obtain ⟨θ', agree', laterHold⟩ := goals_complete build forAlls steps dataOn settledOn bagsOn flows laterLowered
        settledBound bagsBound restsBound (fun q' inside => present q' (List.mem_append_right _ inside))
        (fun name inside => named name (premiseNames_later inside)) hold.2
        fun name inside => holds_congr (agree₁ _ (untouched_name inside _ _)) (agree name inside)
      obtain ⟨laterOrdered, -⟩ := premiseGoals_scope laterLowered
      have agreeAll : AgreeOutside avoid next last' θ θ' := agree₁.trans agree' (Nat.le_succ next) laterOrdered
      have θ'Name : ∀ name ∈ avoid, θ' (labelCode name) = θ (labelCode name) :=
        fun name inside => agreeAll _ (untouched_name inside _ _)
      have θ'List : θ' (listUnknown avoid next) = encodeList elements := by
        rw [agree' _ fun k low _ same => by have := listUnknown_injective avoid same; omega, Function.update_self]
      have contextOf : ∀ name ∈ q.context, name ∈ bound ∧ name ≠ parameter := fun name inside => by
        rw [qContext] at inside
        obtain ⟨inBound, differ⟩ := List.mem_filter.mp inside
        exact ⟨inBound, by simpa using differ⟩
      -- the quantified premise's clauses derive it for every list of its elements
      have chain : ∀ items : List Pattern, (∀ element ∈ items, element ∈ elements) →
          Derives (premiseRelations relEnv language) program forAllRelation
            (.app (.app (inst θ' q.key) (encodeList items)) (inst θ' (contextRow q.context))) (.sym 0) := by
        intro items
        induction items with
        | nil =>
          intro _
          have clause := DemandTransformation.derives_of_clause (R := premiseRelations relEnv language) nilIn θ'
            fun g inside => by
            simp [Quantified.nilClause] at inside
          simpa [Quantified.nilClause, triple, encodeList] using clause
        | cons head tail ih =>
          intro within
          have tailDerived := ih fun element inside => within element (List.mem_cons_of_mem _ inside)
          obtain ⟨result, resultData, resultAgree, resultHolds⟩ := each head (within head List.mem_cons_self)
          have resultSettled : Settled result (settled.filter (· ≠ parameter)) := fun rest restInside => by
            obtain ⟨inSettled, differ⟩ := List.mem_filter.mp restInside
            have differ : rest ≠ parameter := by simpa using differ
            obtain ⟨tail', found⟩ := settledOn rest inSettled
            have value : lookupOrFvar witness rest = .collection .vec tail' none := by
              simp [lookupOrFvar, applyBindings, found]
            have atResult := resultAgree rest (List.mem_cons_of_mem _ (settledBound rest inSettled))
            rw [StepPremises.lookupOrFvar_bindParameter, if_neg differ, value] at atResult
            exact ⟨tail', CollectionMatching.find_of_lookup_collection atResult⟩
          have resultBags : BagSettled result (bags.filter (·.1 ≠ parameter)) := fun pair pairInside => by
            obtain ⟨inBags, differ⟩ := List.mem_filter.mp pairInside
            have differ : pair.1 ≠ parameter := by simpa using differ
            obtain ⟨tail', found⟩ := bagsOn pair inBags
            have value : lookupOrFvar witness pair.1 = .collection pair.2 tail' none := by
              simp [lookupOrFvar, applyBindings, found]
            have atResult := resultAgree pair.1 (List.mem_cons_of_mem _ (bagsBound pair inBags))
            rw [StepPremises.lookupOrFvar_bindParameter, if_neg differ, value] at atResult
            exact ⟨tail', CollectionMatching.find_of_lookup_collection atResult⟩
          have restsResult : Settled result q.rests := fun rest restInside => by
            rw [qRests] at restInside
            obtain ⟨inRests, differ⟩ := List.mem_filter.mp restInside
            have differ' : rest ≠ parameter := by simpa using differ
            have held := agree rest (named rest (List.mem_append_right _ (restsBound rest inRests)))
            unfold OrderedRows.Holds at held
            rw [if_pos inRests] at held
            obtain ⟨tail', value, -⟩ := held
            have atResult := resultAgree rest (List.mem_cons_of_mem _ (restsBound rest inRests))
            rw [StepPremises.lookupOrFvar_bindParameter, if_neg differ', value] at atResult
            exact ⟨tail', CollectionMatching.find_of_lookup_collection atResult⟩
          have bodyNamed : ∀ name ∈ premiseNamesOf premiseBody ++ scopeOf bound parameter, name ∈ q.avoid := by
            intro name inside
            rw [qAvoid]
            simp only [List.mem_append, mem_scopeOf, List.mem_cons, List.mem_filter, decide_eq_true_eq] at inside ⊢
            by_cases same : name = parameter
            · exact .inl (.inl same)
            · tauto
          obtain ⟨θb, agreeB, bodyHold⟩ := goals_complete build forAlls steps resultData resultSettled resultBags
            bodyFlows (premiseGoals_single bodyLowered)
            (fun name inside => mem_scopeOf.mpr (.inr (settledBound name (List.mem_filter.mp inside).1)))
            (fun pair inside => mem_scopeOf.mpr (.inr (bagsBound pair (List.mem_filter.mp inside).1)))
            (fun name inside => mem_scopeOf.mpr (.inr (restsBound name (by
              rw [qRests] at inside
              exact (List.mem_filter.mp inside).1))))
            presentBody (fun name inside => bodyNamed name (by simpa [premiseNames] using inside))
            ⟨resultHolds, trivial⟩ fun name _ => holds_valuesOf restsResult name
          obtain ⟨θc, θcIs⟩ : ∃ θc : ℕ → Expr, θc = Function.update θb (listUnknown q.avoid 0) (encodeList tail) :=
            ⟨_, rfl⟩
          have θcList : θc (listUnknown q.avoid 0) = encodeList tail := by rw [θcIs, Function.update_self]
          have θcName : ∀ name ∈ q.avoid, θc (labelCode name) = valuesOf q.rests result (labelCode name) :=
            fun name inside => by
              rw [θcIs, Function.update_of_ne (listUnknown_ne inside 0).symm, agreeB _ (untouched_name inside _ _)]
          have bodyScope := (premiseGoal_scope bodyLowered).2
          have θcBody : ∀ g ∈ bodyGoals, ∀ u ∈ goalUnknowns g, θb u = θc u := fun g inside u inU => by
            have untouched := (bodyScope u (List.mem_flatMap.mpr ⟨g, inside, inU⟩)).untouched bodyNamed
              (.inr le_rfl) 0 le_rfl Nat.one_pos
            rw [θcIs, Function.update_of_ne untouched]
          have keySame : inst θc q.key = inst θ' q.key := by simp only [Quantified.key, inst_toTerm]
          have headSame : θc (labelCode q.parameter) = encode head := by
            have parameterAvoid : q.parameter ∈ q.avoid := by rw [qAvoid, qParameter]; simp
            rw [θcName _ parameterAvoid, qParameter]
            have held := holds_valuesOf restsResult parameter
            unfold OrderedRows.Holds at held
            rw [if_neg (show parameter ∉ q.rests by rw [qRests]; simp)] at held
            rw [held, resultAgree parameter List.mem_cons_self, StepPremises.lookupOrFvar_bindParameter, if_pos rfl]
          have contextSame : inst θc (contextRow q.context) = inst θ' (contextRow q.context) :=
            inst_contextRow_congr fun name inside => by
              obtain ⟨inBound, differ⟩ := contextOf name inside
              have inAvoid : name ∈ avoid := named name (List.mem_append_right _ inBound)
              have inBodyAvoid : name ∈ q.avoid := by rw [qAvoid]; simp [inBound, differ]
              rw [θcName name inBodyAvoid, θ'Name name inAvoid]
              exact holds_row_unique (agree name inAvoid) (holds_valuesOf restsResult name)
                (by rw [qRests]; simp [differ])
                (by rw [resultAgree name (List.mem_cons_of_mem _ inBound), StepPremises.lookupOrFvar_bindParameter,
                  if_neg differ])
          have clause := DemandTransformation.derives_of_clause (R := premiseRelations relEnv language) consIn θc
            fun g inside => by
            simp only [Quantified.consClause, List.mem_append, List.mem_singleton] at inside
            rcases inside with inBody | rfl
            · exact DemandTransformation.goalHolds_congr g (θcBody g inBody) (bodyHold g inBody)
            · simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
                RootRewritesOnTheStep.inst_symTerm]
              rw [keySame, θcList, contextSame]
              exact tailDerived
          simp only [Quantified.consClause, triple, RootRewritesOnTheStep.inst_appTerm,
            DemandTransformation.inst_unknown, RootRewritesOnTheStep.inst_symTerm] at clause
          rw [keySame, headSame, θcList, contextSame] at clause
          exact clause
      have forAllDerived := chain elements fun _ inside => inside
      refine ⟨θ', agreeAll, fun g inside => ?_⟩
      rcases List.mem_append.mp inside with inHere | inLater
      · by_cases inRests : collection ∈ rests
        · simp only [forAllGoals, if_pos inRests, List.mem_singleton] at inHere
          subst inHere
          have held := agree collection collectionAvoid
          unfold OrderedRows.Holds at held
          rw [if_pos inRests] at held
          obtain ⟨tail, value, listed⟩ := held
          rw [looked] at value
          simp only [Pattern.collection.injEq, and_true] at value
          obtain ⟨-, rfl⟩ := value
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
            RootRewritesOnTheStep.inst_symTerm]
          rw [θ'Name collection collectionAvoid, listed]
          exact forAllDerived
        · simp only [forAllGoals, if_neg inRests, List.mem_cons, List.not_mem_nil, or_false] at inHere
          rcases inHere with rfl | rfl
          · have held := agree collection collectionAvoid
            unfold OrderedRows.Holds at held
            rw [if_neg inRests, looked] at held
            simp only [goalHolds, unboundNone, inst_literalize, literalValues_nil, DemandTransformation.inst_unknown]
            rw [θ'Name collection collectionAvoid, held, θ'List]
            exact listOf_complete forAlls.listOfs kind elements
          · simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
              RootRewritesOnTheStep.inst_symTerm]
            rw [θ'List]
            exact forAllDerived
      · exact laterHold g inLater

/-! ## A triple and its clause -/

theorem rests_bound {left right : Pattern} {premises : List Premise} (shape : TripleShape left right premises) :
    ∀ name ∈ tripleRests left right, name ∈ names left :=
  fun name inside => (List.mem_append.mp inside).elim (MatchesAndInstances.vectorRests_names left)
    fun inRight => MatchesAndInstances.vectorRests_names left (shape.restsWithin name inRight)

/-- **The left side and the premises of a clause instance whose goals hold**: the source matches, and the premises
have witnesses, under bindings the instantiation determines. -/
theorem matched_sound (collections : CollectionProgram program) (build : BuildClauses program)
    (forAlls : ForAllClauses program)
    {left right : Pattern} {premises : List Premise} (shape : TripleShape left right premises)
    {next middle : ℕ} {inputRow : Tm} {matchGoals body : List Goal}
    (inputLowered : matchRow (tripleRests left right) (tripleNames left right premises) 0 left =
      some (inputRow, matchGoals, next))
    (bodyLowered : premiseGoals (tripleRests left right) (tripleNames left right premises)
      (captureSitesOf left premises) (names left) next premises = some (body, middle))
    {D : ℕ → Expr → Expr → Prop}
    (lift : ∀ r x y, D r x y → Derives (premiseRelations relEnv language) program r x y)
    (unfold : Unfolds (premiseRelations relEnv language) program D)
    (steps : ∀ (u : Pattern) (w : Expr), D stepRelation (encode u) w → ∃ v, w = encode v ∧ Step relEnv language u v)
    {θ : ℕ → Expr} {s : Pattern} (input : inst θ inputRow = encode s)
    (matchHold : ∀ g ∈ matchGoals, goalHolds (premiseRelations relEnv language) D θ g)
    (bodyHold : ∀ g ∈ body, goalHolds (premiseRelations relEnv language) D θ g) :
    ∃ larger initial final witnesses,
      (∀ name ∈ boundAfter (names left) premises, Holds (tripleRests left right) θ larger name) ∧
      MatchRel left s initial ∧
      PremisesValid relEnv language (captureSitesOf left premises) initial premises witnesses final ∧
      ∀ name, lookupOrFvar final name =
        if name ∈ boundAfter (names left) premises then lookupOrFvar larger name else .fvar name := by
  obtain ⟨captured, matching⟩ := matchRow_sound collections.sound left inputLowered input
    fun g inside => DemandTransformation.goalHolds_mono lift (matchHold g inside)
  obtain ⟨last, flows⟩ := shape.flows
  obtain ⟨witness, holds⟩ := exists_witness (rests := tripleRests left right) (θ := θ) (names left) captured
  obtain ⟨larger, largerHolds, hold⟩ := goals_sound build forAlls lift unfold steps (rests_bound shape) flows
    bodyLowered bodyHold witness holds
  have leftHolds : ∀ name ∈ names left, Holds (tripleRests left right) θ larger name :=
    fun name inside => largerHolds name (Flows.bound_last flows name inside)
  obtain ⟨initial, matched, valued, covered⟩ := matching larger leftHolds
  have settled : Settled larger (vectorRests left) := fun rest inside =>
    holds_settled (leftHolds rest (MatchesAndInstances.vectorRests_names left inside)) (List.mem_append_left _ inside)
  obtain ⟨final, witnesses, passed, finalCovered, finalKeys, finalValued⟩ :=
    StepPremises.premises_complete larger settled
      (fun rest inside => MatchesAndInstances.vectorRests_names left inside) flows covered
      (MatchesAndInstances.match_functional left matched).2 valued hold
  rw [← StepPremises.Flows.last_eq flows]
  exact ⟨larger, initial, final, witnesses, largerHolds, matched, passed, fun name =>
    (StepPremises.lookupOrFvar_point finalKeys (fun _ member => lookup_of_valued finalValued finalCovered member)
      name).trans (StepPremises.lookupOrFvar_restrict larger last name)⟩

/-- **An instance of a triple's clause is an instance of the triple**, at every term. -/
theorem triple_sound (collections : CollectionProgram program) (build : BuildClauses program)
    (forAlls : ForAllClauses program) {relation : ℕ} {left right : Pattern} {premises : List Premise} {c : Clause}
    (shape : TripleShape left right premises) (lowered : tripleClause relation left right premises = some c)
    {D : ℕ → Expr → Expr → Prop}
    (lift : ∀ r x y, D r x y → Derives (premiseRelations relEnv language) program r x y)
    (unfold : Unfolds (premiseRelations relEnv language) program D)
    (steps : ∀ (u : Pattern) (w : Expr), D stepRelation (encode u) w → ∃ v, w = encode v ∧ Step relEnv language u v)
    {θ : ℕ → Expr} {s : Pattern} (input : inst θ c.input = encode s)
    (goals : ∀ g ∈ c.body, goalHolds (premiseRelations relEnv language) D θ g) :
    ∃ t, inst θ c.output = encode t ∧ TripleAt relEnv language left right premises s t := by
  simp only [tripleClause, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
  obtain ⟨⟨inputRow, matchGoals, next⟩, inputLowered, ⟨body, middle⟩, bodyLowered,
    ⟨outputRow, buildGoals, last⟩, outputLowered, rfl⟩ := lowered
  dsimp only at input goals bodyLowered outputLowered ⊢
  obtain ⟨larger, initial, final, witnesses, lastHolds, matched, passed, reads⟩ :=
    matched_sound collections build forAlls shape inputLowered bodyLowered lift unfold steps input
      (fun g inside => goals g (List.mem_append_left _ (List.mem_append_left _ inside)))
      (fun g inside => goals g (List.mem_append_left _ (List.mem_append_right _ inside)))
  have restsLast : ∀ name ∈ tripleRests left right, name ∈ boundAfter (names left) premises := by
    obtain ⟨last, flows⟩ := shape.flows
    rw [← StepPremises.Flows.last_eq flows]
    exact fun name inside => Flows.bound_last flows name (rests_bound shape name inside)
  have outputIs := buildRow_sound (θ := literalValues θ (rightUnbound left right premises)) (witness := final) build
    right outputLowered (fun name inside => holds_reading restsLast lastHolds reads inside)
    fun g inside => DemandTransformation.goalHolds_mono lift ((goalHolds_literal g).mp
      (goals (literalGoal (rightUnbound left right premises) g)
        (List.mem_append_right _ (List.mem_map.mpr ⟨g, inside, rfl⟩))))
  exact ⟨_, by rw [inst_literalize]; exact outputIs, initial, final, witnesses, matched, passed, rfl⟩

/-- **The left side and the premises of a triple instance at data are a clause instance whose matching and premise
goals hold**, which every later change at the right side's own fresh lists keeps. -/
theorem matched_complete (collections : CollectionProgram program) (build : BuildClauses program)
    (forAlls : ForAllClauses program)
    (dataRows : DataRows relEnv language) {left right : Pattern} {premises : List Premise}
    (shape : TripleShape left right premises)
    (present : QuantifiedPresent program
      (premisesQuantified (tripleRests left right) (captureSitesOf left premises) (names left) premises))
    {next middle : ℕ} {inputRow : Tm} {matchGoals body : List Goal}
    (inputLowered : matchRow (tripleRests left right) (tripleNames left right premises) 0 left =
      some (inputRow, matchGoals, next))
    (bodyLowered : premiseGoals (tripleRests left right) (tripleNames left right premises)
      (captureSitesOf left premises) (names left) next premises = some (body, middle))
    {S : Pattern → Pattern → Prop} (keeps : ∀ u v, isData u = true → S u v → isData v = true)
    (steps : ∀ u v, isData u = true → S u v →
      Derives (premiseRelations relEnv language) program stepRelation (encode u) (encode v))
    {s : Pattern} (data : isData s = true) {initial final : Bindings} {witnesses : List Witness}
    (nested : ∀ step, (∃ witness ∈ witnesses, StepPremises.StepWithin step witness) →
      ∀ u v, StepValid relEnv language u step v → S u v)
    (matched : MatchRel left s initial)
    (passed : PremisesValid relEnv language (captureSitesOf left premises) initial premises witnesses final)
    {last : ℕ} {P : (ℕ → Expr) → Prop}
    (later : ∀ θ₂ : ℕ → Expr, (∀ name ∈ names right, Holds (tripleRests left right) θ₂ final name) →
      ∃ θ₃, AgreeOutside (tripleNames left right premises) middle last θ₂ θ₃ ∧ P θ₃) :
    ∃ θ₃ : ℕ → Expr, inst θ₃ inputRow = encode s ∧
      (∀ g ∈ matchGoals ++ body, goalHolds (premiseRelations relEnv language)
        (Derives (premiseRelations relEnv language) program) θ₃ g) ∧ P θ₃ := by
  obtain ⟨above, finalData, hold, -⟩ := triple_data dataRows shape keeps data nested matched passed
  obtain ⟨-, settledLeft, bagsLeft⟩ := MatchesAndInstances.match_binds left matched
  have settledAll : Settled final (tripleRests left right) := fun rest inside =>
    (List.mem_append.mp inside).elim (fun inLeft => settledLeft.extends_ above rest inLeft)
      fun inRight => settledLeft.extends_ above rest (shape.restsWithin rest inRight)
  have agree := holds_valuesOf settledAll
  obtain ⟨lastNames, flows⟩ := shape.flows
  have leftNamed : ∀ name ∈ names left, name ∈ tripleNames left right premises :=
    fun name inside => by simp [tripleNames, inside]
  have rightNamed : ∀ name ∈ names right, name ∈ tripleNames left right premises :=
    fun name inside => by simp [tripleNames, inside]
  have premisesNamed : ∀ name ∈ premiseNames premises ++ names left, name ∈ tripleNames left right premises :=
    fun name inside => by simp only [tripleNames, List.mem_append] at inside ⊢; tauto
  obtain ⟨θ₁, agree₁, inputIs, matchHold⟩ := matchRow_complete collections.included left inputLowered leftNamed
    matched data above fun name _ => agree name
  obtain ⟨θ₂, agree₂, premisesHold⟩ := goals_complete build forAlls steps finalData (settledLeft.extends_ above)
    (bagsLeft.extends_ above) flows bodyLowered (fun name inside => MatchesAndInstances.vectorRests_names left inside)
    (fun pair inside => MatchesAndInstances.bagRests_names left inside)
    (fun name inside => (List.mem_append.mp inside).elim (MatchesAndInstances.vectorRests_names left)
      fun inRight => MatchesAndInstances.vectorRests_names left (shape.restsWithin name inRight))
    present premisesNamed hold
    fun name inside => holds_congr (agree₁ _ (untouched_name inside _ _)) (agree name)
  obtain ⟨θ₃, agree₃, holdsLater⟩ := later θ₂ fun name inside =>
    holds_congr ((agree₂ _ (untouched_name (rightNamed name inside) _ _)).trans
      (agree₁ _ (untouched_name (rightNamed name inside) _ _))) (agree name)
  obtain ⟨matchOrdered, matchScope⟩ := matchRow_scope left inputLowered
  obtain ⟨bodyOrdered, bodyScope⟩ := premiseGoals_scope bodyLowered
  have matchStays : ∀ u ∈ unknowns inputRow ++ matchGoals.flatMap goalUnknowns, θ₃ u = θ₁ u := fun u inside =>
    (agree₃ u ((matchScope u inside).untouched leftNamed (.inl bodyOrdered))).trans
      (agree₂ u ((matchScope u inside).untouched leftNamed (.inl le_rfl)))
  have bodyStays : ∀ u ∈ body.flatMap goalUnknowns, θ₃ u = θ₂ u := fun u inside =>
    agree₃ u ((bodyScope u inside).untouched premisesNamed (.inl le_rfl))
  refine ⟨θ₃, ?_, fun g inside => ?_, holdsLater⟩
  · rw [← inputIs]
    exact DemandTransformation.inst_agree inputRow fun u inU => matchStays u (List.mem_append_left _ inU)
  · rcases List.mem_append.mp inside with inMatch | inBody
    · exact goals_agree (fun u inU => matchStays u (List.mem_append_right _ inU)) matchHold g inMatch
    · exact goals_agree bodyStays premisesHold g inBody

/-- **At data, an instance of a triple is an instance of its clause.** -/
theorem triple_complete (collections : CollectionProgram program) (build : BuildClauses program)
    (forAlls : ForAllClauses program)
    (dataRows : DataRows relEnv language) {relation : ℕ} {left right : Pattern} {premises : List Premise}
    {c : Clause} (shape : TripleShape left right premises)
    (present : QuantifiedPresent program
      (premisesQuantified (tripleRests left right) (captureSitesOf left premises) (names left) premises))
    (lowered : tripleClause relation left right premises = some c)
    {S : Pattern → Pattern → Prop} (keeps : ∀ u v, isData u = true → S u v → isData v = true)
    (steps : ∀ u v, isData u = true → S u v →
      Derives (premiseRelations relEnv language) program stepRelation (encode u) (encode v))
    {s : Pattern} (data : isData s = true) {initial final : Bindings} {witnesses : List Witness}
    (nested : ∀ step, (∃ witness ∈ witnesses, StepPremises.StepWithin step witness) →
      ∀ u v, StepValid relEnv language u step v → S u v)
    (matched : MatchRel left s initial)
    (passed : PremisesValid relEnv language (captureSitesOf left premises) initial premises witnesses final) :
    ∃ θ : ℕ → Expr, inst θ c.input = encode s ∧
      inst θ c.output = encode (applyBindingsScoped (captureSitesOf left premises) final 0 right) ∧
      ∀ g ∈ c.body, goalHolds (premiseRelations relEnv language) (Derives (premiseRelations relEnv language) program)
        θ g := by
  simp only [tripleClause, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
  obtain ⟨⟨inputRow, matchGoals, next⟩, inputLowered, ⟨body, middle⟩, bodyLowered,
    ⟨outputRow, buildGoals, last⟩, outputLowered, rfl⟩ := lowered
  dsimp only at bodyLowered outputLowered ⊢
  obtain ⟨above, -, -, -⟩ := triple_data dataRows shape keeps data nested matched passed
  have finalKeys := StepPremises.triple_keys dataRows shape keeps data nested matched passed
  obtain ⟨-, -, bagsLeft⟩ := MatchesAndInstances.match_binds left matched
  have rightNamed : ∀ name ∈ names right, name ∈ tripleNames left right premises :=
    fun name inside => by simp [tripleNames, inside]
  have restsOut : ∀ name ∈ rightUnbound left right premises, name ∉ tripleRests left right := by
    intro name inside inRests
    obtain ⟨last, flows⟩ := shape.flows
    have := Flows.bound_last flows name (rests_bound shape name inRests)
    rw [StepPremises.Flows.last_eq flows] at this
    exact (mem_unboundIn.mp inside).2 this
  obtain ⟨θ, inputIs, firstHold, outputIs, buildHold⟩ := matched_complete collections build forAlls dataRows
    shape present inputLowered bodyLowered keeps steps data nested matched passed
    (P := fun θ₃ => inst θ₃ (literalize (rightUnbound left right premises) outputRow) =
        encode (applyBindingsScoped (captureSitesOf left premises) final 0 right) ∧
      ∀ g ∈ buildGoals, goalHolds (premiseRelations relEnv language)
        (Derives (premiseRelations relEnv language) program) θ₃ (literalGoal (rightUnbound left right premises) g))
    fun θ₂ rightHolds => by
      obtain ⟨θ₃, agree₃, rowIs, goalsHold⟩ := buildRow_complete build right outputLowered rightNamed
        (fun pair member => (bagsLeft.extends_ above) pair (shape.bagsWithin pair member)) rightHolds
      have literal : literalValues θ₃ (rightUnbound left right premises) = θ₃ := by
        refine literalValues_eq fun name inside => ?_
        have inRight := (mem_unboundIn.mp inside).1
        have held := rightHolds name inRight
        unfold OrderedRows.Holds at held
        rw [if_neg (restsOut name inside)] at held
        rw [agree₃ _ (untouched_name (rightNamed name inRight) _ _), held,
          StepPremises.lookupOrFvar_absent fun v member => (mem_unboundIn.mp inside).2 (finalKeys name v member)]
      exact ⟨θ₃, agree₃, by rw [inst_literalize, literal]; exact rowIs,
        fun g inside => (goalHolds_literal g).mpr (by rw [literal]; exact goalsHold g inside)⟩
  refine ⟨θ, inputIs, outputIs, fun g inside => ?_⟩
  rcases List.mem_append.mp inside with inFirst | inBuild
  · exact firstHold g inFirst
  · obtain ⟨g₀, g₀In, rfl⟩ := List.mem_map.mp inBuild
    exact buildHold g₀ g₀In

/-! ## The converse of a triple -/

theorem subset_boundAfter : ∀ {bound : List String} (premises : List Premise) {name : String},
    name ∈ bound → name ∈ boundAfter bound premises
  | _, [], _, inside => inside
  | _, premise :: premises, _, inside => subset_boundAfter premises (by cases premise <;> simp [nextBound, inside])

theorem not_mem_left_of_rightUnbound {left right : Pattern} {premises : List Premise} {name : String}
    (inside : name ∈ rightUnbound left right premises) : name ∉ names left :=
  fun inLeft => (mem_unboundIn.mp inside).2 (subset_boundAfter premises inLeft)

theorem mem_freeNames {left right : Pattern} {name : String} :
    name ∈ freeNames left right ↔ name ∈ names left ∧ name ∉ names right := by
  simp [freeNames]

theorem free_rests {left right : Pattern} {name : String} (free : name ∈ freeNames left right) :
    name ∈ tripleRests left right ↔ name ∈ vectorRests left := by
  constructor
  · intro inRests
    rcases List.mem_append.mp inRests with inLeft | inRight
    · exact inLeft
    · exact absurd (MatchesAndInstances.vectorRests_names right inRight) (mem_freeNames.mp free).2
  · exact List.mem_append_left _

/-- **Captured unknowns are one witness**, which binds only them. -/
theorem exists_witness_keys {rests : List String} {θ : ℕ → Expr} : ∀ (wanted : List String),
    (∀ name ∈ wanted, OrderedRows.Captured rests θ name) →
    ∃ witness : Bindings, (∀ name ∈ wanted, Holds rests θ witness name) ∧ ∀ x v, (x, v) ∈ witness → x ∈ wanted
  | [], _ => ⟨[], by simp, fun _ _ inside => absurd inside List.not_mem_nil⟩
  | first :: others, captured => by
      obtain ⟨witness, holds, keys⟩ := exists_witness_keys others fun name member => captured name (by simp [member])
      have here := captured first (by simp)
      have value : ∃ bound, Holds rests θ ((first, bound) :: witness) first := by
        unfold OrderedRows.Captured at here
        split at here
        · rename_i inRests
          obtain ⟨tail, listed⟩ := here
          exact ⟨.collection .vec tail none, by simp [OrderedRows.Holds, inRests, lookupOrFvar, applyBindings, listed]⟩
        · rename_i outside
          obtain ⟨bound, encoded⟩ := here
          exact ⟨bound, by simp [OrderedRows.Holds, outside, lookupOrFvar, applyBindings, encoded]⟩
      obtain ⟨bound, firstHolds⟩ := value
      refine ⟨(first, bound) :: witness, fun name member => ?_, fun x v inside => ?_⟩
      · by_cases same : first = name
        · subst same
          exact firstHolds
        · have later : name ∈ others := (List.mem_cons.mp member).resolve_left fun equal => same equal.symm
          simpa [OrderedRows.Holds, lookupOrFvar, applyBindings, same] using holds name later
      · rcases List.mem_cons.mp inside with same | later
        · simp only [Prod.mk.injEq] at same
          exact same.1 ▸ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (keys x v later)

variable (relEnv language) in
/-- **An instance of a triple whose choices are over the supply**: the values of the names of its matched side that
its other side lacks, and the values its other side substitutes, which reading the other side back does not recover. -/
def TripleWithin (supply : List String) (left right : Pattern) (premises : List Premise) (s t : Pattern) : Prop :=
  ∃ initial final witnesses, MatchRel left s initial ∧
    PremisesValid relEnv language (captureSitesOf left premises) initial premises witnesses final ∧
    applyBindingsScoped (captureSitesOf left premises) final 0 right = t ∧
    (∀ name ∈ freeNames left right, ∀ label ∈ DataClauses.labelsOf (lookupOrFvar initial name), label ∈ supply) ∧
    ∀ v ∈ Instantiation.substValues (captureSitesOf left premises) final 0 right,
      ∀ label ∈ DataClauses.labelsOf v, label ∈ supply

/-- What a chosen name's goal states at an instance: its value is a list of data, or a datum, over the supply. -/
theorem freeGoal_holds {supply : List String} (data : DataClauses.DataProgram supply program)
    {left right : Pattern} {name : String} (free : name ∈ freeNames left right) {θ : ℕ → Expr}
    (holds : goalHolds (premiseRelations relEnv language) (Derives (premiseRelations relEnv language) program) θ
      (freeGoal left name)) :
    ∃ value : Pattern, Holds (tripleRests left right) θ [(name, value)] name ∧ isData value = true ∧
      ∀ label ∈ DataClauses.labelsOf value, label ∈ supply := by
  unfold freeGoal at holds
  split at holds
  · rename_i inRests
    obtain ⟨tail, tailIs, tailData, tailSupplied⟩ := (DataClauses.datumList_iff data).mp holds
    refine ⟨.collection .vec tail none, ?_, by simpa [isData] using tailData,
      fun label inside => tailSupplied label (by simpa [DataClauses.labelsOf] using inside)⟩
    unfold OrderedRows.Holds
    rw [if_pos ((free_rests free).mpr inRests)]
    exact ⟨tail, by simp [lookupOrFvar, applyBindings], by simpa [DemandTransformation.inst_unknown] using tailIs⟩
  · rename_i outside
    obtain ⟨value, valueIs, valueData, valueSupplied⟩ := (DataClauses.datum_iff data).mp holds
    refine ⟨value, ?_, valueData, valueSupplied⟩
    unfold OrderedRows.Holds
    rw [if_neg fun inRests => outside ((free_rests free).mp inRests)]
    simpa [lookupOrFvar, applyBindings, DemandTransformation.inst_unknown] using valueIs

/-- **An instance of a triple's converse clause from data reads an instance of the right side back to a term of data
that the left side matches, related by the triple, with the chosen names over the supply.** -/
theorem converse_sound (collections : CollectionProgram program) (build : BuildClauses program)
    (converses : Instantiation.ConverseClauses program) (forAlls : ForAllClauses program)
    {supply : List String} (data : DataClauses.DataProgram supply program)
    {relation : ℕ} {left right : Pattern} {premises : List Premise}
    {c : Clause} (shape : TripleShape left right premises)
    (lowered : converseClause relation left right premises = some c) {D : ℕ → Expr → Expr → Prop}
    (lift : ∀ r x y, D r x y → Derives (premiseRelations relEnv language) program r x y)
    (unfold : Unfolds (premiseRelations relEnv language) program D)
    (steps : ∀ (u : Pattern) (w : Expr), D stepRelation (encode u) w → ∃ v, w = encode v ∧ Step relEnv language u v)
    {θ : ℕ → Expr} {s : Pattern} (sData : isData s = true) (input : inst θ c.input = encode s)
    (goals : ∀ g ∈ c.body, goalHolds (premiseRelations relEnv language) D θ g) :
    ∃ t, inst θ c.output = encode t ∧ isData t = true ∧
      TripleWithin relEnv language supply left right premises t s := by
  simp only [converseClause, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
  obtain ⟨⟨inputRow, buildGoals, next⟩, inputLowered, inverse, inverseFound, ⟨body, middle⟩, bodyLowered,
    ⟨outputRow, leftGoals, last⟩, outputLowered, rfl⟩ := lowered
  dsimp only at input goals ⊢
  have holdsAt : ∀ g ∈ inverse.map (literalGoal (rightUnbound left right premises)) ++ freeGoals left right ++ body ++
      invertGoals leftGoals, goalHolds (premiseRelations relEnv language)
        (Derives (premiseRelations relEnv language) program) θ g :=
    fun g inside => DemandTransformation.goalHolds_mono lift (goals g inside)
  -- the instance of the right side, read back at the literal reading
  have inverseHold : ∀ g ∈ inverse, goalHolds (premiseRelations relEnv language)
      (Derives (premiseRelations relEnv language) program)
      (literalValues θ (rightUnbound left right premises)) g := by
    intro g inside
    refine (goalHolds_literal g).mp (holdsAt _ ?_)
    simp only [List.mem_append, List.mem_map]
    exact .inl (.inl (.inl ⟨g, inside, rfl⟩))
  have buildHold := Instantiation.buildConverses_sound build converses inverseFound inverseHold
  have read := Instantiation.substitutionsRead_of_converses converses data inverseFound inverseHold
  rw [inst_literalize] at input
  have captured := Instantiation.buildRow_captures build right inputLowered inverseFound input buildHold read
  have rightData := Instantiation.buildRow_data build right inputLowered inverseFound input sData buildHold read
  -- the chosen names
  have chosen : ∀ name ∈ freeNames left right, ∃ value : Pattern,
      Holds (tripleRests left right) θ [(name, value)] name ∧ isData value = true ∧
        ∀ label ∈ DataClauses.labelsOf value, label ∈ supply := by
    intro name free
    refine freeGoal_holds data free (holdsAt _ ?_)
    simp only [List.mem_append, freeGoals, List.mem_map]
    exact .inl (.inl (.inr ⟨name, free, rfl⟩))
  have literalSame : ∀ name ∈ names left, literalValues θ (rightUnbound left right premises) (labelCode name) =
      θ (labelCode name) := fun name inLeft =>
    literalValues_of_not_mem fun other inside same => not_mem_left_of_rightUnbound inside
      (labelCode_injective same ▸ inLeft)
  -- one witness of what is read back and what is chosen
  obtain ⟨witness, holds, keys⟩ := exists_witness_keys (rests := tripleRests left right)
    (θ := literalValues θ (rightUnbound left right premises))
    ((names right).filter (· ∉ rightUnbound left right premises) ++ freeNames left right) fun name inside => by
      rcases List.mem_append.mp inside with readBack | free
      · exact captured name (List.mem_filter.mp readBack).1
      · obtain ⟨value, held, -, -⟩ := chosen name free
        exact holds_captured (holds_congr (literalSame name (mem_freeNames.mp free).1) held)
  have wanted_left : ∀ name ∈ names left,
      name ∈ (names right).filter (· ∉ rightUnbound left right premises) ++ freeNames left right := by
    intro name inLeft
    by_cases inRight : name ∈ names right
    · exact List.mem_append_left _ (List.mem_filter.mpr ⟨inRight, by
        simpa using fun inside => not_mem_left_of_rightUnbound inside inLeft⟩)
    · exact List.mem_append_right _ (mem_freeNames.mpr ⟨inLeft, inRight⟩)
  have rightHolds : ∀ name ∈ names right,
      Holds (tripleRests left right) (literalValues θ (rightUnbound left right premises)) witness name := by
    intro name inRight
    by_cases literal : name ∈ rightUnbound left right premises
    · have notRest : name ∉ tripleRests left right := fun inRests =>
        not_mem_left_of_rightUnbound literal (rests_bound shape name inRests)
      have absent : ∀ v, (name, v) ∉ witness := fun v inside => by
        rcases List.mem_append.mp (keys name v inside) with readBack | free
        · exact absurd literal (by simpa using (List.mem_filter.mp readBack).2)
        · exact not_mem_left_of_rightUnbound literal (mem_freeNames.mp free).1
      unfold OrderedRows.Holds
      rw [if_neg notRest, literalValues_of_mem literal, StepPremises.lookupOrFvar_absent absent]
    · exact holds name (List.mem_append_left _ (List.mem_filter.mpr ⟨inRight, by simpa using literal⟩))
  have sourceIs := buildRow_sound build right inputLowered rightHolds buildHold
  have sIs : s = applyBindingsScoped (captureSitesOf left premises) witness 0 right :=
    encode_injective (input.symm.trans sourceIs)
  -- the premises
  obtain ⟨lastNames, flows⟩ := shape.flows
  have leftWitness : ∀ name ∈ names left, Holds (tripleRests left right) θ witness name :=
    fun name inLeft => holds_congr (literalSame name inLeft).symm (holds name (wanted_left name inLeft))
  obtain ⟨larger, largerHolds, hold⟩ := goals_sound build forAlls lift unfold steps (rests_bound shape) flows
    bodyLowered (fun g inside => goals g (List.mem_append_left _ (List.mem_append_right _ inside))) witness
    leftWitness
  have leftHolds : ∀ name ∈ names left, Holds (tripleRests left right) θ larger name :=
    fun name inside => largerHolds name (Flows.bound_last flows name inside)
  have leftHold := (invertGoals_hold collections (matchRow_matching left outputLowered)).mp
    fun g inside => holdsAt g (List.mem_append_right _ inside)
  obtain ⟨t, outputIs⟩ := matchRow_decodes collections.sound left outputLowered leftHold
    fun name inside => holds_captured (leftHolds name inside)
  have chosenValue : ∀ name ∈ freeNames left right, ∃ value : Pattern, lookupOrFvar larger name = value ∧
      isData value = true ∧ ∀ label ∈ DataClauses.labelsOf value, label ∈ supply := by
    intro name free
    obtain ⟨value, held, valueData, valueSupplied⟩ := chosen name free
    refine ⟨value, ?_, valueData, valueSupplied⟩
    rw [holds_lookup_unique (leftHolds name (mem_freeNames.mp free).1) (leftWitness name (mem_freeNames.mp free).1)]
    have same := holds_lookup_unique (leftWitness name (mem_freeNames.mp free).1)
      (holds_congr rfl held)
    rw [same]
    simp [lookupOrFvar, applyBindings]
  have valueData : ∀ name ∈ names left, isData (lookupOrFvar larger name) = true := by
    intro name inside
    by_cases inRight : name ∈ names right
    · have readBack : name ∉ rightUnbound left right premises := fun literal =>
        not_mem_left_of_rightUnbound literal inside
      rw [holds_lookup_unique (leftHolds name inside) (leftWitness name inside)]
      have held := holds name (wanted_left name inside)
      have dataHeld := rightData name inRight
      unfold OrderedRows.Holds at held
      unfold Instantiation.DataHeld at dataHeld
      split at held
      · rename_i inRests
        rw [if_pos inRests] at dataHeld
        obtain ⟨tail, value, listed⟩ := held
        rw [value]
        simp [isData, dataHeld tail listed]
      · rename_i outside
        rw [if_neg outside] at dataHeld
        exact dataHeld _ held
    · obtain ⟨value, rfl, valueData, -⟩ := chosenValue name (mem_freeNames.mpr ⟨inside, inRight⟩)
      exact valueData
  have tData := CollectionMatching.matchRow_data collections.sound left outputLowered outputIs leftHold leftHolds
    valueData
  obtain ⟨-, leftMatches⟩ := matchRow_sound collections.sound left outputLowered outputIs leftHold
  obtain ⟨initial, matched, valued, covered⟩ := leftMatches larger leftHolds
  have settled : Settled larger (vectorRests left) := fun rest inside =>
    holds_settled (leftHolds rest (MatchesAndInstances.vectorRests_names left inside)) (List.mem_append_left _ inside)
  obtain ⟨final, witnesses, passed, finalCovered, finalKeys, finalValued⟩ :=
    StepPremises.premises_complete larger settled
      (fun rest inside => MatchesAndInstances.vectorRests_names left inside) flows covered
      (MatchesAndInstances.match_functional left matched).2 valued hold
  have agreeRight : ∀ name ∈ names right, lookupOrFvar final name = lookupOrFvar witness name := by
    intro name inside
    by_cases inLast : name ∈ lastNames
    · rw [lookup_of_valued finalValued finalCovered inLast]
      have readBack : name ∉ rightUnbound left right premises := fun literal =>
        (mem_unboundIn.mp literal).2 (by rw [← StepPremises.Flows.last_eq flows]; exact inLast)
      exact holds_lookup_unique (largerHolds name inLast)
        (holds_congr (literalValues_of_not_mem fun other member same =>
          readBack (by rw [← labelCode_injective same]; exact member)).symm
          (holds name (List.mem_append_left _ (List.mem_filter.mpr ⟨inside, by simpa using readBack⟩))))
    · have literal : name ∈ rightUnbound left right premises :=
        mem_unboundIn.mpr ⟨inside, by rw [← StepPremises.Flows.last_eq flows]; exact inLast⟩
      have absent : ∀ v, (name, v) ∉ witness := fun v member => by
        rcases List.mem_append.mp (keys name v member) with readBack | free
        · exact absurd literal (by simpa using (List.mem_filter.mp readBack).2)
        · exact not_mem_left_of_rightUnbound literal (mem_freeNames.mp free).1
      rw [StepPremises.lookupOrFvar_absent fun v member => inLast (finalKeys name v member),
        StepPremises.lookupOrFvar_absent absent]
  refine ⟨t, outputIs, tData, initial, final, witnesses, matched, passed,
    by rw [sIs]; exact Instantiation.applyBindingsScoped_agree _ 0 right agreeRight,
    fun name free label inside => ?_, fun v inside label member => ?_⟩
  · obtain ⟨value, valueIs, -, valueSupplied⟩ := chosenValue name free
    rw [lookup_of_valued valued covered (mem_freeNames.mp free).1, valueIs] at inside
    exact valueSupplied label inside
  · rw [Instantiation.substValues_agree _ 0 right agreeRight] at inside
    obtain ⟨-, substituted⟩ := Instantiation.buildRow_substituted build right inputLowered rightHolds buildHold
    obtain ⟨depthRow, value, body, out, instMember, valueIs⟩ := substituted v inside
    have chosenHolds := inverseHold _ (Instantiation.converses_of_instantiate inverseFound instMember).1
    simp only [goalHolds, DataClauses.unitTerm, RootRewritesOnTheStep.inst_symTerm, valueIs] at chosenHolds
    obtain ⟨p, pIs, -, pSupplied⟩ := (DataClauses.datum_iff data).mp chosenHolds
    rw [encode_injective pIs] at member
    exact pSupplied label member

/-- **At data, an instance of a triple read backwards, its chosen names over the supply, is an instance of its
converse clause.** -/
theorem converse_complete (collections : CollectionProgram program) (build : BuildClauses program)
    (converses : Instantiation.ConverseClauses program) (forAlls : ForAllClauses program)
    {supply : List String} (data : DataClauses.DataProgram supply program)
    (dataRows : DataRows relEnv language) {relation : ℕ}
    {left right : Pattern} {premises : List Premise} {c : Clause} (shape : TripleShape left right premises)
    (present : QuantifiedPresent program
      (premisesQuantified (tripleRests left right) (captureSitesOf left premises) (names left) premises))
    (lowered : converseClause relation left right premises = some c)
    {S : Pattern → Pattern → Prop} (keeps : ∀ u v, isData u = true → S u v → isData v = true)
    (steps : ∀ u v, isData u = true → S u v →
      Derives (premiseRelations relEnv language) program stepRelation (encode u) (encode v))
    {t : Pattern} (tData : isData t = true) {initial final : Bindings} {witnesses : List Witness}
    (nested : ∀ step, (∃ witness ∈ witnesses, StepPremises.StepWithin step witness) →
      ∀ u v, StepValid relEnv language u step v → S u v)
    (matched : MatchRel left t initial)
    (passed : PremisesValid relEnv language (captureSitesOf left premises) initial premises witnesses final)
    (supplied : ∀ name ∈ freeNames left right, ∀ label ∈ DataClauses.labelsOf (lookupOrFvar initial name),
      label ∈ supply)
    (substituted : ∀ v ∈ Instantiation.substValues (captureSitesOf left premises) final 0 right,
      ∀ label ∈ DataClauses.labelsOf v, label ∈ supply) :
    ∃ θ : ℕ → Expr, inst θ c.input = encode (applyBindingsScoped (captureSitesOf left premises) final 0 right) ∧
      inst θ c.output = encode t ∧
      ∀ g ∈ c.body, goalHolds (premiseRelations relEnv language) (Derives (premiseRelations relEnv language) program)
        θ g := by
  simp only [converseClause, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
  obtain ⟨⟨inputRow, buildGoals, next⟩, inputLowered, inverse, inverseFound, ⟨body, middle⟩, bodyLowered,
    ⟨outputRow, leftGoals, last⟩, outputLowered, rfl⟩ := lowered
  dsimp only at bodyLowered outputLowered ⊢
  obtain ⟨above, finalData, hold, -⟩ := triple_data dataRows shape keeps tData nested matched passed
  have finalKeys := StepPremises.triple_keys dataRows shape keeps tData nested matched passed
  obtain ⟨initialCovered, settledLeft, bagsLeft⟩ := MatchesAndInstances.match_binds left matched
  have settledAll : Settled final (tripleRests left right) := fun rest inside =>
    (List.mem_append.mp inside).elim (fun inLeft => settledLeft.extends_ above rest inLeft)
      fun inRight => settledLeft.extends_ above rest (shape.restsWithin rest inRight)
  have agree := holds_valuesOf settledAll
  obtain ⟨lastNames, flows⟩ := shape.flows
  have leftNamed : ∀ name ∈ names left, name ∈ tripleNames left right premises :=
    fun name inside => by simp [tripleNames, inside]
  have rightNamed : ∀ name ∈ names right, name ∈ tripleNames left right premises :=
    fun name inside => by simp [tripleNames, inside]
  have premisesNamed : ∀ name ∈ premiseNames premises ++ names left, name ∈ tripleNames left right premises :=
    fun name inside => by simp only [tripleNames, List.mem_append] at inside ⊢; tauto
  obtain ⟨θ₁, agree₁, inputIs, buildHold⟩ := buildRow_complete build right inputLowered rightNamed
    (fun pair member => (bagsLeft.extends_ above) pair (shape.bagsWithin pair member)) fun name _ => agree name
  have rightHeld : ∀ name ∈ names right, Holds (tripleRests left right) θ₁ final name :=
    fun name inside => holds_congr (agree₁ _ (untouched_name (rightNamed name inside) _ _)) (agree name)
  have chosen : ∀ value, Goal.ask DataClauses.datumRelation DataClauses.unitTerm value ∈ inverse →
      goalHolds (premiseRelations relEnv language) (Derives (premiseRelations relEnv language) program) θ₁
        (.ask DataClauses.datumRelation DataClauses.unitTerm value) := by
    intro value member
    obtain ⟨depthRow, body, out, instMember⟩ := Instantiation.datum_of_converses inverseFound member
    obtain ⟨fromGoals, -⟩ := Instantiation.buildRow_substituted build right inputLowered rightHeld buildHold
    obtain ⟨v, vIn, vIs⟩ := fromGoals instMember
    simp only [goalHolds, DataClauses.unitTerm, RootRewritesOnTheStep.inst_symTerm, vIs]
    exact (DataClauses.datum_iff data).mpr ⟨v, rfl, Instantiation.substValues_data finalData _ 0 right
      shape.rightCanonical (fun rest inside => settledLeft.extends_ above rest (shape.restsWithin rest inside))
      (fun pair inside => (bagsLeft.extends_ above) pair (shape.bagsWithin pair inside)) v vIn,
      substituted v vIn⟩
  have inverseHold := Instantiation.buildConverses_complete build converses
    (Instantiation.buildRow_goals right inputLowered) inverseFound buildHold chosen
  obtain ⟨θ₂, agree₂, premisesHold⟩ := goals_complete build forAlls steps finalData (settledLeft.extends_ above)
    (bagsLeft.extends_ above) flows bodyLowered (fun name inside => MatchesAndInstances.vectorRests_names left inside)
    (fun pair inside => MatchesAndInstances.bagRests_names left inside)
    (fun name inside => (List.mem_append.mp inside).elim (MatchesAndInstances.vectorRests_names left)
      fun inRight => MatchesAndInstances.vectorRests_names left (shape.restsWithin name inRight))
    present premisesNamed hold fun name inside => holds_congr (agree₁ _ (untouched_name inside _ _)) (agree name)
  obtain ⟨θ₃, agree₃, outputIs, leftHold⟩ := matchRow_complete collections.included left outputLowered leftNamed
    matched tData above fun name inside =>
      holds_congr ((agree₂ _ (untouched_name (leftNamed name inside) _ _)).trans
        (agree₁ _ (untouched_name (leftNamed name inside) _ _))) (agree name)
  obtain ⟨buildOrdered, buildScope⟩ := buildRow_scope right inputLowered
  obtain ⟨bodyOrdered, bodyScope⟩ := premiseGoals_scope bodyLowered
  have inputStays : ∀ u ∈ unknowns inputRow ++ buildGoals.flatMap goalUnknowns, θ₃ u = θ₁ u := fun u inside =>
    (agree₃ u ((buildScope u inside).untouched rightNamed (.inl bodyOrdered))).trans
      (agree₂ u ((buildScope u inside).untouched rightNamed (.inl le_rfl)))
  have bodyStays : ∀ u ∈ body.flatMap goalUnknowns, θ₃ u = θ₂ u := fun u inside =>
    agree₃ u ((bodyScope u inside).untouched premisesNamed (.inl le_rfl))
  -- a name's row at the end is its row under the instance's bindings
  have nameRow : ∀ name ∈ names left ++ names right, θ₃ (labelCode name) = θ₁ (labelCode name) := by
    intro name inside
    rcases List.mem_append.mp inside with inLeft | inRight
    · exact (agree₃ _ (untouched_name (leftNamed name inLeft) _ _)).trans
        (agree₂ _ (untouched_name (leftNamed name inLeft) _ _))
    · exact (agree₃ _ (untouched_name (rightNamed name inRight) _ _)).trans
        (agree₂ _ (untouched_name (rightNamed name inRight) _ _))
  have literal : literalValues θ₃ (rightUnbound left right premises) = θ₃ := by
    refine literalValues_eq fun name inside => ?_
    have inRight := (mem_unboundIn.mp inside).1
    have notRest : name ∉ tripleRests left right := fun inRests =>
      not_mem_left_of_rightUnbound inside (rests_bound shape name inRests)
    have held := holds_congr (agree₁ _ (untouched_name (rightNamed name inRight) _ _)) (agree name)
    unfold OrderedRows.Holds at held
    rw [if_neg notRest] at held
    rw [nameRow name (List.mem_append_right _ inRight), held,
      StepPremises.lookupOrFvar_absent fun v member => (mem_unboundIn.mp inside).2 (finalKeys name v member)]
  refine ⟨θ₃, ?_, outputIs, fun g inside => ?_⟩
  · rw [inst_literalize, literal, ← inputIs]
    exact DemandTransformation.inst_agree inputRow fun u inU => inputStays u (List.mem_append_left _ inU)
  · simp only [List.mem_append] at inside
    rcases inside with ((inInverse | inFree) | inBody) | inLeft
    · obtain ⟨g₀, g₀In, rfl⟩ := List.mem_map.mp inInverse
      rw [goalHolds_literal, literal]
      exact goals_agree (fun u inU => inputStays u (List.mem_append_right _
        (Instantiation.buildConverses_unknowns inverseFound u inU))) inverseHold g₀ g₀In
    · obtain ⟨name, free, rfl⟩ := List.mem_map.mp inFree
      obtain ⟨inLeft, -⟩ := mem_freeNames.mp free
      have valueIs : lookupOrFvar final name = lookupOrFvar initial name :=
        (OrderedMatching.lookup_of_extends initialCovered above inLeft).symm
      have held := holds_congr ((nameRow name (List.mem_append_left _ inLeft)).trans
        (agree₁ _ (untouched_name (leftNamed name inLeft) _ _))) (agree name)
      unfold freeGoal
      split
      · rename_i inRests
        unfold OrderedRows.Holds at held
        rw [if_pos ((free_rests free).mpr inRests)] at held
        obtain ⟨tail, value, listed⟩ := held
        have tailData : isDataList tail = true := by
          have := Instantiation.lookupOrFvar_data finalData name
          rw [value] at this
          simpa [isData] using this
        simp only [goalHolds, DemandTransformation.inst_unknown, DataClauses.unitTerm,
          RootRewritesOnTheStep.inst_symTerm]
        rw [listed]
        exact DataClauses.datumList_complete data tail tailData fun label member =>
          supplied name free label (by rw [← valueIs, value]; simpa [DataClauses.labelsOf] using member)
      · rename_i outside
        unfold OrderedRows.Holds at held
        rw [if_neg fun inRests => outside ((free_rests free).mp inRests)] at held
        simp only [goalHolds, DemandTransformation.inst_unknown, DataClauses.unitTerm,
          RootRewritesOnTheStep.inst_symTerm]
        rw [held]
        exact DataClauses.datum_complete data _ (Instantiation.lookupOrFvar_data finalData name)
          fun label member => supplied name free label (by rw [← valueIs]; exact member)
    · exact goals_agree bodyStays premisesHold g inBody
    · exact (invertGoals_hold collections (matchRow_matching left outputLowered)).mpr leftHold g inLeft

/-! ## A triple's clause is moded -/

/-- **What each premise goal needs is bound when it is reached**, and what the premises bind is bound at the end. -/
theorem goals_moded {rests avoid : List String} {sites : Pattern} {settled : List String}
    {bags : List (String × CollType)} :
    ∀ {bound last : List String} {premises : List Premise} {next next' : ℕ} {body : List Goal},
      (∀ name ∈ rests, name ∈ bound) →
      Flows settled bags bound premises last → premiseGoals rests avoid sites bound next premises = some (body, next') →
      ∀ before : List ℕ, (∀ name ∈ bound, labelCode name ∈ before) →
        InputsBound before body ∧ ∀ name ∈ last, labelCode name ∈ before ++ body.flatMap goalUnknowns
  | _, _, _, _, _, _, _, .nil, lowered, before, boundIn => by
      simp only [premiseGoals, Option.some.injEq, Prod.mk.injEq] at lowered
      obtain ⟨rfl, rfl⟩ := lowered
      exact ⟨.nil before, fun name inside => by simpa using boundIn name inside⟩
  | bound, _, _, next, _, _, restsBound, .query (relation := relation) (arguments := arguments) _ _ flows, lowered,
      before, boundIn => by
      simp only [premiseGoals, premiseGoal, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
      obtain ⟨_, ⟨row, rowLowered, rfl⟩, ⟨later, last'⟩, laterLowered, same⟩ := lowered
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      have rowUnknowns : ∀ {x : ℕ}, x ∈ unknowns row ↔ ∃ name ∈ namesList arguments, labelCode name = x := by
        intro x
        simp only [unknowns_lowerThen arguments rowLowered, RootRewritesOnTheStep.unknowns_symTerm, List.append_nil,
          List.mem_map]
      obtain ⟨laterFlows, lastBound⟩ := goals_moded (fun name inside => List.mem_append_left _ (restsBound name inside))
        flows laterLowered
        (before ++ [Goal.query
            { name := labelCode relation
              arguments := [literalize (unboundIn bound (namesList arguments)) row]
              value := row }].flatMap goalUnknowns)
        fun name inside => by
          rcases List.mem_append.mp inside with inBound | inArguments
          · exact List.mem_append_left _ (boundIn name inBound)
          · refine List.mem_append_right _ ?_
            simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, goalUnknowns, List.mem_append]
            exact .inr (rowUnknowns.mpr ⟨name, inArguments, rfl⟩)
      refine ⟨InputsBound.append (.cons (fun x inside => ?_) (.nil _)) laterFlows, fun name inside => ?_⟩
      · simp only [goalInputs, List.flatMap_cons, List.flatMap_nil, List.append_nil] at inside
        obtain ⟨found, outside⟩ := unknowns_literalize _ row inside
        obtain ⟨name, inArguments, rfl⟩ := rowUnknowns.mp found
        by_cases inBound : name ∈ bound
        · exact boundIn name inBound
        · exact absurd rfl (outside name (mem_unboundIn.mpr ⟨inArguments, inBound⟩))
      · simpa [List.flatMap_append, List.append_assoc] using lastBound name inside
  | bound, _, _, next, _, _, restsBound, .step (premise := premise) (source := source) (target := target) endpoints
      _ _ _ _ flows, lowered, before, boundIn => by
      simp only [premiseGoals, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
      obtain ⟨⟨here, middle⟩, hereLowered, ⟨later, last'⟩, laterLowered, same⟩ := lowered
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      rw [StepPremises.nextBound_step endpoints] at laterLowered
      rw [premiseGoal_step endpoints] at hereLowered
      simp only [stepGoals, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at hereLowered
      obtain ⟨⟨sourceRow, sourceGoals, middle'⟩, sourceLowered, targetRow, targetLowered, rfl, rfl⟩ := hereLowered
      obtain ⟨sourceFlows, sourceRowBound⟩ := buildRow_moded source sourceLowered
        (bound := before ++ (unboundIn bound (names source)).map labelCode)
        fun name inside => by
          by_cases inBound : name ∈ bound
          · exact List.mem_append_left _ (boundIn name inBound)
          · exact List.mem_append_right _ (List.mem_map.mpr ⟨name, mem_unboundIn.mpr ⟨inside, inBound⟩, rfl⟩)
      have targetUnknowns := unknowns_lower target targetLowered
      have hereFlows : InputsBound before (sourceGoals.map (literalGoal (unboundIn bound (names source))) ++
          [Goal.ask stepRelation (literalize (unboundIn bound (names source)) sourceRow) targetRow]) := by
        refine InputsBound.append (inputsBound_literal sourceFlows) (.cons (fun x inside => ?_) (.nil _))
        simp only [goalInputs] at inside
        obtain ⟨found, outside⟩ := unknowns_literalize _ sourceRow inside
        rcases List.mem_append.mp (sourceRowBound x found) with front | inGoals
        · rcases List.mem_append.mp front with inBefore | literal
          · exact List.mem_append_left _ inBefore
          · obtain ⟨name, member, rfl⟩ := List.mem_map.mp literal
            exact absurd rfl (outside name member)
        · obtain ⟨g, gIn, inG⟩ := List.mem_flatMap.mp inGoals
          exact List.mem_append_right _ (List.mem_flatMap.mpr
            ⟨literalGoal _ g, List.mem_map.mpr ⟨g, gIn, rfl⟩, goalUnknowns_literal_of g inG outside⟩)
      obtain ⟨laterFlows, lastBound⟩ := goals_moded (fun name inside => List.mem_append_left _ (restsBound name inside))
        flows laterLowered
        (before ++ (sourceGoals.map (literalGoal (unboundIn bound (names source))) ++
          [Goal.ask stepRelation (literalize (unboundIn bound (names source)) sourceRow) targetRow]).flatMap goalUnknowns)
        fun name inside => by
          rcases List.mem_append.mp inside with inBound | inTarget
          · exact List.mem_append_left _ (boundIn name inBound)
          · refine List.mem_append_right _ ?_
            simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, goalUnknowns,
              targetUnknowns, List.mem_append, List.mem_map]
            exact .inr (.inr ⟨name, inTarget, rfl⟩)
      refine ⟨InputsBound.append hereFlows laterFlows, fun name inside => ?_⟩
      simpa [List.flatMap_append, List.append_assoc] using lastBound name inside
  | bound, _, _, next, _, _, restsBound, .fresh (condition := condition) _ _ flows, lowered, before, boundIn => by
      simp only [premiseGoals, premiseGoal, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
      obtain ⟨_, ⟨termRow, termLowered, rfl⟩, ⟨later, last'⟩, laterLowered, same⟩ := lowered
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      have termUnknowns := unknowns_lower condition.term termLowered
      obtain ⟨laterFlows, lastBound⟩ := goals_moded restsBound flows laterLowered
        (before ++ [Goal.query ⟨symTerm 0, 0,
          [literalize (unboundIn bound (condition.varName :: names condition.term)) (.var (labelCode condition.varName)),
            literalize (unboundIn bound (condition.varName :: names condition.term)) termRow]⟩].flatMap goalUnknowns)
        fun name inside => List.mem_append_left _ (boundIn name inside)
      refine ⟨InputsBound.append (.cons (fun x inside => ?_) (.nil _)) laterFlows, fun name inside => ?_⟩
      · simp only [goalInputs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at inside
        rcases inside with inVar | inTerm
        · obtain ⟨found, outside⟩ := unknowns_literalize _ _ inVar
          simp only [DemandTransformation.unknowns_unknown, List.mem_singleton] at found
          subst found
          by_cases inBound : condition.varName ∈ bound
          · exact boundIn _ inBound
          · exact absurd rfl (outside _ (mem_unboundIn.mpr ⟨List.mem_cons_self, inBound⟩))
        · obtain ⟨found, outside⟩ := unknowns_literalize _ _ inTerm
          rw [termUnknowns] at found
          obtain ⟨other, inNames, rfl⟩ := List.mem_map.mp found
          by_cases inBound : other ∈ bound
          · exact boundIn other inBound
          · exact absurd rfl (outside other (mem_unboundIn.mpr ⟨List.mem_cons_of_mem _ inNames, inBound⟩))
      · simpa [List.flatMap_append, List.append_assoc] using lastBound name inside
  | boundNames, _, _, next, _, _, restsBound, .forAll (collection := collection) (parameter := parameter)
      (body := premiseBody) _ flows, lowered, before, boundIn => by
      simp only [premiseGoals, premiseGoal, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
      obtain ⟨_, ⟨_, -, rfl⟩, ⟨later, last'⟩, laterLowered, same⟩ := lowered
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      have hereFlows : InputsBound before (forAllGoals rests avoid boundNames next collection
          (quantifiedAt rests sites boundNames parameter premiseBody)) := by
        unfold forAllGoals
        split
        · rename_i inRests
          refine .cons (fun x inside => ?_) (.nil _)
          simp only [goalInputs, triple, RootRewritesOnTheStep.unknowns_appTerm, Quantified.key,
            Instantiation.unknowns_toTerm, DemandTransformation.unknowns_unknown, unknowns_contextRow,
            List.nil_append, List.mem_append, List.mem_singleton, List.mem_map] at inside
          rcases inside with rfl | ⟨name, nameInside, rfl⟩
          · exact boundIn _ (restsBound _ inRests)
          · exact boundIn name (List.mem_filter.mp nameInside).1
        · refine .cons (fun x inside => ?_) (.cons (fun x inside => ?_) (.nil _))
          · simp only [goalInputs] at inside
            obtain ⟨found, outside⟩ := unknowns_literalize _ _ inside
            simp only [DemandTransformation.unknowns_unknown, List.mem_singleton] at found
            subst found
            by_cases inBound : collection ∈ boundNames
            · exact boundIn _ inBound
            · exact absurd rfl (outside _ (mem_unboundIn.mpr ⟨List.mem_singleton_self _, inBound⟩))
          · simp only [goalInputs, triple, RootRewritesOnTheStep.unknowns_appTerm, Quantified.key,
              Instantiation.unknowns_toTerm, DemandTransformation.unknowns_unknown, unknowns_contextRow,
              List.nil_append, List.mem_append, List.mem_singleton, List.mem_map] at inside
            rcases inside with rfl | ⟨name, nameInside, rfl⟩
            · simp [goalUnknowns]
            · exact List.mem_append_left _ (boundIn name (List.mem_filter.mp nameInside).1)
      obtain ⟨laterFlows, lastBound⟩ := goals_moded restsBound flows laterLowered
        (before ++ (forAllGoals rests avoid boundNames next collection
          (quantifiedAt rests sites boundNames parameter premiseBody)).flatMap goalUnknowns)
        fun name inside => List.mem_append_left _ (boundIn name inside)
      refine ⟨InputsBound.append hereFlows laterFlows, fun name inside => ?_⟩
      simpa [List.flatMap_append, List.append_assoc] using lastBound name inside

/-- **The clause of a triple of the shape is moded.** -/
theorem tripleClause_moded {relation : ℕ} {left right : Pattern} {premises : List Premise} {c : Clause}
    (shape : TripleShape left right premises) (lowered : tripleClause relation left right premises = some c) :
    DemandTransformation.Moded c := by
  simp only [tripleClause, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
  obtain ⟨⟨inputRow, matchGoals, next⟩, inputLowered, ⟨body, middle⟩, bodyLowered,
    ⟨outputRow, buildGoals, last⟩, outputLowered, rfl⟩ := lowered
  dsimp only at bodyLowered outputLowered ⊢
  obtain ⟨lastNames, flows⟩ := shape.flows
  obtain ⟨matchFlows, leftNamed⟩ := matchRow_moded left inputLowered (bound := unknowns inputRow) fun _ inside => inside
  obtain ⟨premiseFlows, lastBound⟩ := goals_moded (rests_bound shape) flows bodyLowered
    (unknowns inputRow ++ matchGoals.flatMap goalUnknowns) leftNamed
  obtain ⟨buildFlows, outputBound⟩ := buildRow_moded right outputLowered
    (bound := unknowns inputRow ++ matchGoals.flatMap goalUnknowns ++ body.flatMap goalUnknowns ++
      (rightUnbound left right premises).map labelCode)
    fun name inside => by
      by_cases inLast : name ∈ boundAfter (names left) premises
      · rw [← StepPremises.Flows.last_eq flows] at inLast
        exact List.mem_append_left _ (lastBound name inLast)
      · exact List.mem_append_right _ (List.mem_map.mpr ⟨name, mem_unboundIn.mpr ⟨inside, inLast⟩, rfl⟩)
  refine DemandTransformation.moded_of_inputsBound ((matchFlows.append premiseFlows).append ?_) fun x inside => ?_
  · simpa [List.flatMap_append, List.append_assoc] using inputsBound_literal buildFlows
  · obtain ⟨found, outside⟩ := unknowns_literalize _ outputRow inside
    have here := outputBound x found
    simp only [List.flatMap_append, List.mem_append] at here ⊢
    rcases here with ((((inInput | inMatch) | inBody) | literal) | inBuild)
    · exact .inl inInput
    · exact .inr (.inl (.inl inMatch))
    · exact .inr (.inl (.inr inBody))
    · obtain ⟨name, member, rfl⟩ := List.mem_map.mp literal
      exact absurd rfl (outside name member)
    · obtain ⟨g, gIn, inG⟩ := List.mem_flatMap.mp inBuild
      exact .inr (.inr (List.mem_flatMap.mpr
        ⟨literalGoal _ g, List.mem_map.mpr ⟨g, gIn, rfl⟩, goalUnknowns_literal_of g inG outside⟩))

/-- The goals choosing names read nothing. -/
theorem freeGoals_inputsBound {left right : Pattern} (before : List ℕ) : InputsBound before (freeGoals left right) := by
  unfold freeGoals
  induction freeNames left right generalizing before with
  | nil => exact .nil _
  | cons name names ih =>
      refine .cons (fun x inside => ?_) (ih _)
      unfold freeGoal at inside
      split at inside <;> simp [goalInputs, DataClauses.unitTerm, RootRewritesOnTheStep.symTerm,
        RuleSyntax.Machines.unknowns] at inside

/-- The goals choosing names bind them. -/
theorem freeGoals_bind {left right : Pattern} {name : String} (free : name ∈ freeNames left right) :
    labelCode name ∈ (freeGoals left right).flatMap goalUnknowns := by
  refine List.mem_flatMap.mpr ⟨freeGoal left name, List.mem_map.mpr ⟨name, free, rfl⟩, ?_⟩
  unfold freeGoal
  split <;> simp [goalUnknowns, DemandTransformation.unknowns_unknown]

/-- **The converse clause of a triple of the shape is moded.** -/
theorem converseClause_moded {relation : ℕ} {left right : Pattern} {premises : List Premise} {c : Clause}
    (shape : TripleShape left right premises)
    (lowered : converseClause relation left right premises = some c) : DemandTransformation.Moded c := by
  simp only [converseClause, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
  obtain ⟨⟨inputRow, buildGoals, next⟩, inputLowered, inverse, inverseFound, ⟨body, middle⟩, bodyLowered,
    ⟨outputRow, leftGoals, last⟩, outputLowered, rfl⟩ := lowered
  dsimp only at bodyLowered outputLowered ⊢
  obtain ⟨lastNames, flows⟩ := shape.flows
  obtain ⟨inverseFlows, rightNamed⟩ := Instantiation.buildRow_converses right inputLowered inverseFound
    (bound := unknowns (literalize (rightUnbound left right premises) inputRow) ++
      (rightUnbound left right premises).map labelCode) fun u inside => by
      by_cases isLiteral : ∃ name ∈ rightUnbound left right premises, labelCode name = u
      · obtain ⟨name, member, rfl⟩ := isLiteral
        exact List.mem_append_right _ (List.mem_map.mpr ⟨name, member, rfl⟩)
      · simp only [not_exists, not_and] at isLiteral
        exact List.mem_append_left _ (mem_unknowns_literalize_of inputRow inside isLiteral)
  have literalFlows := inputsBound_literal inverseFlows
  set readBack := unknowns (literalize (rightUnbound left right premises) inputRow) ++
    (inverse.map (literalGoal (rightUnbound left right premises))).flatMap goalUnknowns with readBackIs
  have leftBound : ∀ name ∈ names left, labelCode name ∈ readBack ++ (freeGoals left right).flatMap goalUnknowns := by
    intro name inLeft
    by_cases inRight : name ∈ names right
    · have notLiteral : ∀ other ∈ rightUnbound left right premises, labelCode other ≠ labelCode name :=
        fun other member same => not_mem_left_of_rightUnbound member (labelCode_injective same ▸ inLeft)
      refine List.mem_append_left _ ?_
      rcases List.mem_append.mp (rightNamed name inRight) with front | inInverse
      · rcases List.mem_append.mp front with inRow | literal
        · exact List.mem_append_left _ inRow
        · obtain ⟨other, member, same⟩ := List.mem_map.mp literal
          exact absurd same (notLiteral other member)
      · obtain ⟨g, gIn, inG⟩ := List.mem_flatMap.mp inInverse
        exact List.mem_append_right _ (List.mem_flatMap.mpr
          ⟨literalGoal _ g, List.mem_map.mpr ⟨g, gIn, rfl⟩, goalUnknowns_literal_of g inG notLiteral⟩)
    · exact List.mem_append_right _ (freeGoals_bind (mem_freeNames.mpr ⟨inLeft, inRight⟩))
  obtain ⟨premiseFlows, lastBound⟩ := goals_moded (rests_bound shape) flows bodyLowered
    (readBack ++ (freeGoals left right).flatMap goalUnknowns) leftBound
  obtain ⟨leftFlows, outputBound⟩ := matchRow_readBack left outputLowered
    (bound := readBack ++ (freeGoals left right).flatMap goalUnknowns ++ body.flatMap goalUnknowns)
    fun name inside => lastBound name (Flows.bound_last flows name inside)
  have combined : InputsBound (unknowns (literalize (rightUnbound left right premises) inputRow))
      (inverse.map (literalGoal (rightUnbound left right premises)) ++ freeGoals left right ++ body ++
        invertGoals leftGoals) := by
    refine ((literalFlows.append (freeGoals_inputsBound _)).append ?_).append ?_
    · simpa [readBackIs, List.flatMap_append, List.append_assoc] using premiseFlows
    · simpa [readBackIs, List.flatMap_append, List.append_assoc] using leftFlows
  refine DemandTransformation.moded_of_inputsBound combined fun x inside => ?_
  · have here := outputBound x inside
    simp only [readBackIs, List.flatMap_append, List.mem_append, mem_invertGoals_unknowns] at here ⊢
    tauto

/-! ## The clauses of quantified premises -/

theorem premiseQuantified_step {rests : List String} {sites : Pattern} {bound : List String} {premise : Premise}
    {source target : Pattern} (endpoints : stepEndpoints premise = some (source, target)) :
    premiseQuantified rests sites bound premise = [] := by
  cases premise <;> simp_all [stepEndpoints, premiseQuantified]

/-- **Every quantified premise's body flows** from its parameter and the names bound before it. -/
theorem quantified_flows {settled : List String} {bags : List (String × CollType)} {sites : Pattern} :
    ∀ {rests bound last : List String} {premises : List Premise}, (∀ name ∈ rests, name ∈ bound) →
      Flows settled bags bound premises last → ∀ q ∈ premisesQuantified rests sites bound premises,
        (∀ name ∈ q.rests, name ∈ q.parameter :: q.context) ∧
          ∃ settled' bags' inner, Flows settled' bags' (q.parameter :: q.context) [q.body] inner
  | _, _, _, _, _, .nil, q, inside => by simp [premisesQuantified] at inside
  | _, _, _, _, restsBound, .query _ _ flows, q, inside =>
      quantified_flows (fun name member => List.mem_append_left _ (restsBound name member)) flows q inside
  | _, _, _, _, restsBound, .step endpoints _ _ _ _ flows, q, inside => by
      rw [premisesQuantified_cons, premiseQuantified_step endpoints, List.nil_append,
        StepPremises.nextBound_step endpoints] at inside
      exact quantified_flows (fun name member => List.mem_append_left _ (restsBound name member)) flows q inside
  | _, _, _, _, restsBound, .fresh _ _ flows, q, inside => quantified_flows restsBound flows q inside
  | rests, bound, _, _, restsBound, .forAll (parameter := parameter) bodyFlows flows, q, inside => by
      rw [premisesQuantified_cons] at inside
      simp only [premiseQuantified, List.cons_append, List.mem_cons, List.mem_append] at inside
      rcases inside with rfl | inBody | inLater
      · refine ⟨fun name member => ?_, _, _, _, bodyFlows⟩
        simp only [quantifiedAt, List.mem_filter, decide_eq_true_eq] at member
        exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨restsBound name member.1, by simpa using member.2⟩)
      · exact quantified_flows (rests := rests.filter (· ≠ parameter))
          (fun name member => mem_scopeOf.mpr (.inr (restsBound name (List.mem_filter.mp member).1))) bodyFlows q
          (by simpa [premisesQuantified] using inBody)
      · exact quantified_flows restsBound flows q inLater

/-- **The clauses of a quantified premise are moded** when its body flows from its parameter and its context. -/
theorem quantified_moded {settled : List String} {bags : List (String × CollType)} {q : Quantified}
    (restsIn : ∀ name ∈ q.rests, name ∈ q.parameter :: q.context)
    {inner : List String} (flows : Flows settled bags (q.parameter :: q.context) [q.body] inner)
    {cs : List Clause} (lowered : q.clauses = some cs) : ∀ c ∈ cs, DemandTransformation.Moded c := by
  simp only [Quantified.clauses, Option.map_eq_some_iff] at lowered
  obtain ⟨⟨bodyGoals, bodyNext⟩, bodyLowered, rfl⟩ := lowered
  intro c inside
  simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl
  · exact DemandTransformation.moded_of_inputsBound (.nil _) fun x inside => by
      simp [Quantified.nilClause] at inside
  · have inputIs : unknowns (q.consClause bodyGoals).input =
        labelCode q.parameter :: listUnknown q.avoid 0 :: q.context.map labelCode := by
      simp [Quantified.consClause, triple, Quantified.key, Instantiation.unknowns_toTerm, unknowns_contextRow]
    obtain ⟨bodyFlows, -⟩ := goals_moded restsIn flows (premiseGoals_single bodyLowered)
      (unknowns (q.consClause bodyGoals).input) fun name inside => by
        rw [inputIs]
        rcases List.mem_cons.mp inside with rfl | inContext
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map_of_mem inContext))
    refine DemandTransformation.moded_of_inputsBound ?_ fun x inside => by simp [Quantified.consClause] at inside
    refine bodyFlows.append (.cons (fun x inside => ?_) (.nil _))
    refine List.mem_append_left _ ?_
    rw [inputIs]
    simp only [goalInputs, triple, RootRewritesOnTheStep.unknowns_appTerm, Quantified.key,
      Instantiation.unknowns_toTerm, DemandTransformation.unknowns_unknown, unknowns_contextRow, List.nil_append,
      List.mem_append, List.mem_singleton] at inside
    rcases inside with rfl | inContext
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ inContext)

theorem quantified_relation {q : Quantified} {cs : List Clause} (lowered : q.clauses = some cs) :
    ∀ c ∈ cs, c.relation = forAllRelation := by
  simp only [Quantified.clauses, Option.map_eq_some_iff] at lowered
  obtain ⟨_, -, rfl⟩ := lowered
  intro c inside
  simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl <;> rfl

/-- **The clauses of a triple's quantified premises.** -/
def quantifiedClauses (left right : Pattern) (premises : List Premise) : List Clause :=
  (premisesQuantified (tripleRests left right) (captureSitesOf left premises) (names left) premises).flatMap
    fun q => q.clauses.getD []

theorem quantifiedClauses_present {program : List Clause} {left right : Pattern} {premises : List Premise}
    (included : ∀ c ∈ quantifiedClauses left right premises, c ∈ program) :
    QuantifiedPresent program
      (premisesQuantified (tripleRests left right) (captureSitesOf left premises) (names left) premises) :=
  fun q inside cs clausesAre c member =>
    included c (List.mem_flatMap.mpr ⟨q, inside, by rw [clausesAre]; exact member⟩)

theorem quantifiedClauses_origin {left right : Pattern} {premises : List Premise} {c : Clause}
    (inside : c ∈ quantifiedClauses left right premises) :
    ∃ q ∈ premisesQuantified (tripleRests left right) (captureSitesOf left premises) (names left) premises,
      ∃ cs, q.clauses = some cs ∧ c ∈ cs := by
  obtain ⟨q, qIn, member⟩ := List.mem_flatMap.mp inside
  cases clausesAre : q.clauses with
  | none =>
      rw [clausesAre] at member
      exact absurd member List.not_mem_nil
  | some cs =>
      rw [clausesAre] at member
      exact ⟨q, qIn, cs, clausesAre, member⟩

theorem quantifiedClauses_moded {left right : Pattern} {premises : List Premise}
    (shape : TripleShape left right premises) :
    ∀ c ∈ quantifiedClauses left right premises, DemandTransformation.Moded c := by
  obtain ⟨last, flows⟩ := shape.flows
  intro c inside
  obtain ⟨q, qIn, cs, clausesAre, member⟩ := quantifiedClauses_origin inside
  obtain ⟨restsIn, settled', bags', inner, bodyFlows⟩ := quantified_flows (rests_bound shape) flows q qIn
  exact quantified_moded restsIn bodyFlows clausesAre c member

/-- **The clauses of rules' quantified premises**: reading a collection's list, and each quantified premise's own
clauses. -/
def quantifiedPremiseClauses (rules : List RewriteRule) : List Clause :=
  listOfClauses ++ rules.flatMap fun rule => quantifiedClauses rule.left rule.right rule.premises

theorem listOfClauses_moded : ∀ c ∈ listOfClauses, DemandTransformation.Moded c := by
  intro c inside
  simp only [listOfClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl | rfl <;>
    exact DemandTransformation.moded_of_inputsBound (.nil _) fun x inside => by
      simpa [listOfClause, DemandTransformation.unknowns_unknown] using inside

theorem quantifiedPremiseClauses_relation {rules : List RewriteRule} {c : Clause}
    (inside : c ∈ quantifiedPremiseClauses rules) :
    (c ∈ listOfClauses ∧ c.relation = listOfRelation) ∨
      ((∃ rule ∈ rules, c ∈ quantifiedClauses rule.left rule.right rule.premises) ∧
        c.relation = forAllRelation) := by
  rcases List.mem_append.mp inside with inList | inRules
  · refine .inl ⟨inList, ?_⟩
    simp only [listOfClauses, List.mem_cons, List.not_mem_nil, or_false] at inList
    rcases inList with rfl | rfl | rfl <;> rfl
  · obtain ⟨rule, ruleIn, member⟩ := List.mem_flatMap.mp inRules
    obtain ⟨q, -, cs, clausesAre, cIn⟩ := quantifiedClauses_origin member
    exact .inr ⟨⟨rule, ruleIn, member⟩, quantified_relation clausesAre c cIn⟩

/-! ## The rules as clauses -/

/-- **The clauses of a language's rules** in a program: the program has the collection clauses and the clauses an
instantiation asks, every rule has the shape and its clause, and every clause of the relation of steps is a rule's. -/
structure RuleClauses (language : LanguageDef) (program : List Clause) : Prop where
  collections : CollectionProgram program
  build : BuildClauses program
  shape : ∀ rule ∈ language.rewrites, TripleShape rule.left rule.right rule.premises
  clause : ∀ rule ∈ language.rewrites, ∃ c ∈ program,
    tripleClause stepRelation rule.left rule.right rule.premises = some c
  onlyRules : ∀ c ∈ program, c.relation = stepRelation → ∃ rule ∈ language.rewrites,
    tripleClause stepRelation rule.left rule.right rule.premises = some c
  forAlls : ForAllClauses program
  quantified : ∀ rule ∈ language.rewrites, QuantifiedPresent program
    (premisesQuantified (tripleRests rule.left rule.right) (captureSitesOf rule.left rule.premises) (names rule.left)
      rule.premises)

/-- **Every derivation of the relation of steps is a reference step.** -/
theorem step_of_derivesAt (clauses : RuleClauses language program) :
    ∀ (depth : ℕ) {s : Pattern} {w : Expr},
      DerivesAt (premiseRelations relEnv language) program depth stepRelation (encode s) w →
        ∃ t, w = encode t ∧ Step relEnv language s t
  | 0, _, _, derived => derived.elim
  | depth + 1, _, _, derived => by
      obtain ⟨c, member, isStep, θ, input, output, goals⟩ := derived
      obtain ⟨rule, ruleIn, lowered⟩ := clauses.onlyRules c member isStep
      obtain ⟨t, outputIs, instance_⟩ := triple_sound clauses.collections clauses.build clauses.forAlls
        (clauses.shape rule ruleIn) lowered (fun _ _ _ asked => ⟨depth, asked⟩) (derivesAt_unfolds depth)
        (fun _ _ asked => step_of_derivesAt clauses depth asked) input goals
      exact ⟨t, output.symm.trans outputIs, StepPremises.step_iff.mpr ⟨rule, ruleIn, instance_⟩⟩

/-- **Every reference step of data is a derivation of the relation of steps**, by the size of its witness. -/
theorem derives_of_stepValid (dataRows : DataRows relEnv language) (clauses : RuleClauses language program) :
    ∀ (n : ℕ) {witness : Witness} {s t : Pattern}, sizeOf witness < n → isData s = true →
      StepValid relEnv language s witness t →
      Derives (premiseRelations relEnv language) program stepRelation (encode s) (encode t)
  | 0, _, _, _, small, _, _ => absurd small (Nat.not_lt_zero _)
  | n + 1, _, _, _, small, data, valid => by
      cases valid with
      | rule found matched passed =>
        rename_i index rule initial final witnesses
        rw [matchPatternForRule_eq_syntactic] at matched
        have ruleIn := List.mem_iff_getElem?.mpr ⟨index, found⟩
        obtain ⟨c, member, lowered⟩ := clauses.clause rule ruleIn
        obtain ⟨θ, input, output, goals⟩ := triple_complete clauses.collections clauses.build clauses.forAlls
          dataRows (clauses.shape rule ruleIn) (clauses.quantified rule ruleIn) lowered
          (S := fun u v => ∃ w, sizeOf w < n ∧ StepValid relEnv language u w v)
          (fun _ _ uData ⟨_, wSmall, wValid⟩ =>
            StepPremises.stepValid_data dataRows clauses.shape n wSmall uData wValid)
          (fun _ _ uData ⟨_, wSmall, wValid⟩ => derives_of_stepValid dataRows clauses n wSmall uData wValid)
          data (fun step inside u v stepped =>
            ⟨step, by have := StepPremises.nested_lt (index := index) (initial := initial) inside; omega, stepped⟩)
          (matchPattern_sound matched) passed
        have clause := DemandTransformation.derives_of_clause member θ goals
        rw [tripleClause_relation lowered, input, output] at clause
        exact clause

/-- **At data, the least model of the rules' clauses is the reference step relation.** -/
theorem derives_step_iff (dataRows : DataRows relEnv language)
    (clauses : RuleClauses language program) {s : Pattern} (data : isData s = true) {w : Expr} :
    Derives (premiseRelations relEnv language) program stepRelation (encode s) w ↔
      ∃ t, w = encode t ∧ Step relEnv language s t := by
  constructor
  · rintro ⟨depth, derived⟩
    exact step_of_derivesAt clauses depth derived
  · rintro ⟨t, rfl, witness, valid⟩
    exact derives_of_stepValid dataRows clauses (sizeOf witness + 1) (Nat.lt_succ_self _) data valid

/-! ## Checking a triple -/

/-- Whether a step premise's source and target are of the shapes they are read in. -/
def stepChecked (settled : List String) (bags : List (String × CollType)) (source target : Pattern) : Bool :=
  source.hasCanonicalBinderMetadata && ordered target &&
    (vectorRests source ++ restNames target).all (fun rest => settled.contains rest) &&
    (bagRests source).all (fun pair => bags.contains pair)

/-- Whether a premise is of the shape it is read in, and the names bound after it. A quantified premise's body is read
from the names bound before it and the parameter, which shadows a rest of the same name there; what the body binds stays
inside it. -/
def premiseFlows? (settled : List String) (bags : List (String × CollType)) :
    List String → Premise → Option (List String)
  | bound, .relationQuery _ arguments =>
      if orderedList arguments && (restNamesList arguments).all (fun rest => settled.contains rest) then
        some (bound ++ namesList arguments)
      else none
  | bound, .congruence source target =>
      if stepChecked settled bags source target then some (bound ++ names target) else none
  | bound, .scopedStep step =>
      if stepChecked settled bags step.source step.target then some (bound ++ names step.target) else none
  | bound, .freshness condition =>
      if ordered condition.term && (restNames condition.term).all (fun rest => settled.contains rest) then
        some bound
      else none
  | bound, .forAll _ parameter body =>
      (premiseFlows? (settled.filter (· ≠ parameter)) (bags.filter (·.1 ≠ parameter)) (scopeOf bound parameter)
        body).map fun _ => bound

/-- Whether every premise is of the shape it is read in, and what is bound at the end. -/
def flows? (settled : List String) (bags : List (String × CollType)) :
    List String → List Premise → Option (List String)
  | bound, [] => some bound
  | bound, premise :: premises =>
      (premiseFlows? settled bags bound premise).bind fun next => flows? settled bags next premises

theorem premiseFlows_spec {settled : List String} {bags : List (String × CollType)} :
    ∀ {premise : Premise} {bound next : List String}, premiseFlows? settled bags bound premise = some next →
      ∀ {premises : List Premise} {last : List String}, Flows settled bags next premises last →
        Flows settled bags bound (premise :: premises) last
  | .relationQuery relation arguments, bound, next, computed => by
      intro later
      simp only [premiseFlows?] at computed
      split at computed
      · rename_i checked
        simp only [Option.some.injEq] at computed
        subst computed
        simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at checked
        exact .query checked.1 checked.2 later
      · cases computed
  | .congruence source target, bound, next, computed => by
      intro later
      simp only [premiseFlows?] at computed
      split at computed
      · rename_i checked
        simp only [Option.some.injEq] at computed
        subst computed
        simp only [stepChecked, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at checked
        exact .step rfl checked.1.1.1 checked.1.1.2 checked.1.2 checked.2 later
      · cases computed
  | .scopedStep step, bound, next, computed => by
      intro later
      simp only [premiseFlows?] at computed
      split at computed
      · rename_i checked
        simp only [Option.some.injEq] at computed
        subst computed
        simp only [stepChecked, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at checked
        exact .step rfl checked.1.1.1 checked.1.1.2 checked.1.2 checked.2 later
      · cases computed
  | .freshness condition, bound, next, computed => by
      intro later
      simp only [premiseFlows?] at computed
      split at computed
      · rename_i checked
        simp only [Option.some.injEq] at computed
        subst computed
        simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at checked
        exact .fresh checked.1 checked.2 later
      · cases computed
  | .forAll collection parameter body, bound, next, computed => by
      intro later
      simp only [premiseFlows?, Option.map_eq_some_iff] at computed
      obtain ⟨inner, bodyComputed, rfl⟩ := computed
      exact .forAll (premiseFlows_spec bodyComputed .nil) later

theorem flows_spec {settled : List String} {bags : List (String × CollType)} :
    ∀ {premises : List Premise} {bound last : List String},
      flows? settled bags bound premises = some last → Flows settled bags bound premises last
  | [], bound, last, computed => by
      simp only [flows?, Option.some.injEq] at computed
      subst computed
      exact .nil
  | premise :: premises, bound, last, computed => by
      simp only [flows?, Option.bind_eq_some_iff] at computed
      obtain ⟨next, here, later⟩ := computed
      exact premiseFlows_spec here (flows_spec later)

/-- Why a declaration is outside this compiler. -/
inductive Refusal where
  | premises (name : String)
  | binderNames (name : String)
  | restOfResult (name : String)
  | declaredBinding (name : String)
  deriving DecidableEq, Repr

/-- **A triple's clause under a lowering, after the checks of its shape**, refused by the declaration's name. -/
def tripleChecked (lower : ℕ → Pattern → Pattern → List Premise → Option Clause)
    (relation : ℕ) (name : String) (left right : Pattern) (premises : List Premise) : Except Refusal Clause :=
  if right.hasCanonicalBinderMetadata then
    if (vectorRests right).all (fun rest => (vectorRests left).contains rest) &&
        (bagRests right).all (fun pair => (bagRests left).contains pair) then
      match flows? (vectorRests left) (bagRests left) (names left) premises, lower relation left right premises with
      | some _, some c => .ok c
      | _, _ => .error (.premises name)
    else .error (.restOfResult name)
  else .error (.binderNames name)

theorem tripleChecked_spec {lower : ℕ → Pattern → Pattern → List Premise → Option Clause} {relation : ℕ}
    {name : String} {left right : Pattern} {premises : List Premise} {c : Clause}
    (checked : tripleChecked lower relation name left right premises = .ok c) :
    TripleShape left right premises ∧ lower relation left right premises = some c := by
  unfold tripleChecked at checked
  split at checked
  · rename_i canonical
    split at checked
    · rename_i restsOk
      split at checked
      · rename_i last c' flowsOk lowered
        cases checked
        simp only [Bool.and_eq_true] at restsOk
        simp only [List.all_eq_true, List.contains_iff_mem] at restsOk
        exact ⟨⟨canonical, restsOk.1, restsOk.2, last, flows_spec flowsOk⟩, lowered⟩
      · cases checked
    · cases checked
  · cases checked

/-- **The clause of a rule**, refused by the rule's name. -/
def ruleClause (rule : RewriteRule) : Except Refusal Clause :=
  tripleChecked tripleClause stepRelation rule.name rule.left rule.right rule.premises

theorem ruleClause_spec {rule : RewriteRule} {c : Clause} (checked : ruleClause rule = .ok c) :
    TripleShape rule.left rule.right rule.premises ∧
      tripleClause stepRelation rule.left rule.right rule.premises = some c :=
  tripleChecked_spec checked

/-- The clauses of some rules, in their order. -/
def ruleClauses : List RewriteRule → Except Refusal (List Clause)
  | [] => .ok []
  | rule :: rules =>
      match ruleClause rule, ruleClauses rules with
      | .ok c, .ok cs => .ok (c :: cs)
      | .error reason, _ => .error reason
      | .ok _, .error reason => .error reason

theorem ruleClauses_spec : ∀ {rules : List RewriteRule} {cs : List Clause}, ruleClauses rules = .ok cs →
    (∀ rule ∈ rules, TripleShape rule.left rule.right rule.premises ∧
      ∃ c ∈ cs, tripleClause stepRelation rule.left rule.right rule.premises = some c) ∧
      ∀ c ∈ cs, ∃ rule ∈ rules, tripleClause stepRelation rule.left rule.right rule.premises = some c
  | [], cs, computed => by
      simp only [ruleClauses, Except.ok.injEq] at computed
      subst computed
      exact ⟨fun _ inside => absurd inside List.not_mem_nil, fun _ inside => absurd inside List.not_mem_nil⟩
  | rule :: rules, cs, computed => by
      unfold ruleClauses at computed
      split at computed
      · rename_i c cs' here later
        cases computed
        obtain ⟨shape, lowered⟩ := ruleClause_spec here
        obtain ⟨laterRules, laterClauses⟩ := ruleClauses_spec later
        refine ⟨fun r inside => ?_, fun c' inside => ?_⟩
        · rcases List.mem_cons.mp inside with rfl | inRules
          · exact ⟨shape, c, List.mem_cons_self, lowered⟩
          · obtain ⟨rShape, c', cIn, rLowered⟩ := laterRules r inRules
            exact ⟨rShape, c', List.mem_cons_of_mem _ cIn, rLowered⟩
        · rcases List.mem_cons.mp inside with rfl | inClauses
          · exact ⟨rule, List.mem_cons_self, lowered⟩
          · obtain ⟨r, rIn, rLowered⟩ := laterClauses c' inClauses
            exact ⟨r, List.mem_cons_of_mem _ rIn, rLowered⟩
      · cases computed
      · cases computed

end Mettapedia.GSLT.Compilation.Uniform.DemandRules

#print axioms Mettapedia.GSLT.Compilation.Uniform.DemandRules.derives_step_iff
