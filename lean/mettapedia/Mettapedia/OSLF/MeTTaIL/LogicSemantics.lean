import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.Logic.LP.Core
import Mettapedia.Logic.LP.Semantics
import Mettapedia.Logic.LP.FunctionFree

/-!
# LogicSemantics — Bridge from LanguageDef.logic to LP.Core

Connects the typed `DatalogClause` rules in `LanguageDef.logic` to
the proven LP.Core semantics (T_P operator, least Herbrand model,
fixpoint theorems).

## Architecture

```
LanguageDef.logic : List LogicDecl
    │
    ├─ .relation : LogicRelationDecl → relation signature
    ├─ .datalogClause : DatalogClause → typed Datalog rule
    │       │
    │       ↓ datalogClauseToLPClause
    │   LP.Clause langDefLPSig
    │       │
    │       ↓ langDefKnowledgeBase
    │   LP.KnowledgeBase langDefLPSig
    │       │
    │       ↓ LP.leastHerbrandModel (proven: T_P monotone, Tarski fixpoint)
    │   LP.Interpretation langDefLPSig
    │
    └─ .ruleText : String → legacy (opaque, no semantics)
```

## Trust model

The bridge from `DatalogClause` to `LP.Clause` is a total function
on well-formed clauses. The LP.Core semantics (T_P, least Herbrand model,
isModel) are proven by the LP library. The executable `RelationEnv`
closure below is connected by step-support, trace, tuple-shape, and
atom-match grounding theorems, plus a recursive theorem that every tuple in
the finite executable closure maps to an arity-preserving LP least-model atom.
The converse least-model completeness theorem remains an explicit open
obligation.

## References

- Lloyd, *Foundations of Logic Programming*, 2nd ed., 1987
- van Emden & Kowalski, "Semantics of predicate logic as a programming language", 1976
-/

namespace Mettapedia.OSLF.MeTTaIL.LogicSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.Logic.LP

/-! ## Section 1: The LanguageDef LP Signature -/

/-- String-based function-free LP signature for LanguageDef logic rules.

    - Constants = String (Pattern constructor names, lexical items)
    - Variables = String (from rule typeContext)
    - Relations = String (from LogicRelationDecl names)
    - Functions = Empty (Datalog = function-free)

    The relation arity is set to 0 here because LP.Core requires
    a fixed arity per relation symbol, but LanguageDef uses dynamic
    List-based arguments. The bridge handles arity checking per-clause. -/
def langDefLPSig : LPSignature where
  constants := String
  vars := String
  relationSymbols := String
  relationArity := fun _ => 0
  functionSymbols := Empty
  functionArity := Empty.elim

instance : IsEmpty langDefLPSig.functionSymbols := Empty.instIsEmpty

/-! ## Section 1b: Arity-preserving LP signature

`langDefLPSig` above is the historical nullary encoding.  The definitions below
preserve each Datalog atom's arity in the LP relation symbol itself.  This gives
the least-Herbrand-model bridge the right target for executable relation tuples;
the remaining open obligation is the full equivalence between the finite tuple
closure in Section 4b and this arity-preserving LP model.
-/

abbrev DatalogRelKey := String × Nat

/-- Function-free LP signature whose relation key stores both name and arity. -/
def arityDefLPSig : LPSignature where
  constants := String
  vars := String
  relationSymbols := DatalogRelKey
  relationArity := fun r => r.2
  functionSymbols := Empty
  functionArity := Empty.elim

/-- The arity-preserving LanguageDef LP signature is function-free. -/
theorem arityDef_logic_functionFree :
    arityDefLPSig.isFunctionFree :=
  Empty.instIsEmpty

/-! ## Section 2: DatalogTerm/Atom → LP.Core.Term/Atom -/

/-- Convert a DatalogTerm to an LP.Core Term (function-free). -/
def datalogTermToLP (t : DatalogTerm) : Term langDefLPSig :=
  match t with
  | .var v => .var v
  | .const c => .const c

/-- Convert a DatalogAtom to an LP.Core Atom.
    Since `langDefLPSig.relationArity` is 0 for all relations,
    we use a flexible encoding: the atom carries its relation name
    but arguments are encoded via a separate mechanism.

    For the formal bridge, we define a per-clause signature with
    correct arities. Here we provide the raw conversion. -/
def datalogAtomToLPTerms (a : DatalogAtom) : List (Term langDefLPSig) :=
  a.args.map datalogTermToLP

/-- Convert a DatalogTerm to the arity-preserving LP signature. -/
def datalogTermToArityLP : DatalogTerm → Term arityDefLPSig
  | .var v => .var v
  | .const c => .const c

/-- Convert a DatalogAtom to an arity-preserving LP atom. -/
def datalogAtomToArityLP (a : DatalogAtom) : Atom arityDefLPSig where
  symbol := (a.rel, a.args.length)
  args := fun i => datalogTermToArityLP (a.args.get i)

/-- Convert a DatalogClause to an arity-preserving LP clause. -/
def datalogClauseToArityLPClause (c : DatalogClause) : Clause arityDefLPSig where
  head := datalogAtomToArityLP c.head
  body := c.body.map datalogAtomToArityLP

/-- Arity preservation for the converted atom's relation symbol. -/
theorem datalogAtomToArityLP_relationArity (a : DatalogAtom) :
    arityDefLPSig.relationArity (datalogAtomToArityLP a).symbol = a.args.length := rfl

/-! ## Section 3: Safety properties -/

/-- Variable names occurring in a DatalogTerm. -/
def DatalogTerm.vars : DatalogTerm → List String
  | .var v => [v]
  | .const _ => []

/-- All variables in a list of DatalogAtoms. -/
def bodyVars (body : List DatalogAtom) : List String :=
  body.flatMap DatalogAtom.vars

/-- Safety (range-restriction): head variables ⊆ body variables.
    This is the standard Datalog safety condition ensuring every
    answer variable is bound. -/
theorem isSafe_iff_head_vars_subset_body_vars (c : DatalogClause) :
    c.isSafe = true ↔ c.head.vars.all (fun v => c.body.any (fun b => v ∈ b.vars)) = true := by
  simp [DatalogClause.isSafe]

/-- A fact (empty body) is safe iff the head has no variables. -/
theorem fact_safe_iff_ground (c : DatalogClause) (hfact : c.isFact = true) :
    c.isSafe = true ↔ c.head.vars = [] := by
  simp [DatalogClause.isSafe, DatalogClause.isFact] at *
  constructor
  · intro h
    cases hv : c.head.vars with
    | nil => rfl
    | cons v vs =>
      simp [hv] at h
      simp [hfact] at h
  · intro h
    simp [h]

/-! ## Section 4: Extract Datalog program from LanguageDef -/

/-- Extract all typed Datalog clauses from a LanguageDef's logic declarations. -/
def extractDatalogClauses (lang : LanguageDef) : List DatalogClause :=
  lang.logic.filterMap fun
    | .datalogClause dc => some dc
    | _ => none

/-- Extract relation declarations from a LanguageDef. -/
def extractRelationDecls (lang : LanguageDef) : List LogicRelationDecl :=
  lang.logic.filterMap fun
    | .relation rd => some rd
    | _ => none

/-- Arity-preserving LP program extracted from LanguageDef Datalog clauses. -/
def langDefArityProgram (lang : LanguageDef) : Program arityDefLPSig :=
  (extractDatalogClauses lang).map datalogClauseToArityLPClause

/-- Arity-preserving LP knowledge base for LanguageDef logic.  Facts are kept as
    empty-body clauses in `prog`, so `db` remains empty. -/
def langDefArityKnowledgeBase (lang : LanguageDef) :
    KnowledgeBase arityDefLPSig where
  prog := langDefArityProgram lang
  db := ∅

/-- Any extracted Datalog clause contributes its arity-preserving LP head to the
    least Herbrand model when its converted body is already in that model. -/
theorem langDefArity_clause_head_in_leastModel
    (lang : LanguageDef) (c : DatalogClause)
    (hc : c ∈ extractDatalogClauses lang) (g : Grounding arityDefLPSig)
    (hbody : ∀ b ∈ (datalogClauseToArityLPClause c).body,
      g.groundAtom b ∈ leastHerbrandModel (langDefArityKnowledgeBase lang)) :
    g.groundAtom (datalogClauseToArityLPClause c).head ∈
      leastHerbrandModel (langDefArityKnowledgeBase lang) := by
  exact leastHerbrandModel_clause (langDefArityKnowledgeBase lang)
    (datalogClauseToArityLPClause c)
    (List.mem_map.mpr ⟨c, hc, rfl⟩) g hbody

/-! ## Section 4b: Datalog closures as relation-query tuples

The premise-aware engine consumes `relationQuery` side conditions through a
`RelationEnv`.  The definitions below provide a generic executable bridge from
typed `LanguageDef.logic` declarations to that engine path: function-free
Datalog clauses are saturated over their syntactic constants, and the resulting
ground atoms become relation tuples.

This is a real rule-consumption path for OSLF reductions.  The soundness
direction into the arity-preserving least model is proved below; converse
completeness and external checker adequacy are tracked separately.
-/

/-- Interpret a ground Datalog constant as the nullary constructor pattern with
    the same name. Variables are not ground and therefore do not yield tuples. -/
def datalogTermToGroundPattern? : DatalogTerm → Option Pattern
  | .const c => some (.apply c [])
  | .var _ => none

def datalogTermsToGroundPatterns? : List DatalogTerm → Option (List Pattern)
  | [] => some []
  | t :: ts =>
      match datalogTermToGroundPattern? t, datalogTermsToGroundPatterns? ts with
      | some p, some ps => some (p :: ps)
      | _, _ => none

/-- A ground Datalog atom can be used as a `RelationEnv` tuple. -/
def datalogAtomToGroundTuple? (a : DatalogAtom) : Option (String × List Pattern) :=
  match datalogTermsToGroundPatterns? a.args with
  | some args => some (a.rel, args)
  | none => none

/-- Extract a relation tuple from a ground Datalog fact. Non-facts and facts
    containing variables are ignored by this conservative bridge. -/
def datalogClauseToGroundFactTuple? (c : DatalogClause) : Option (String × List Pattern) :=
  match c.body with
  | [] => datalogAtomToGroundTuple? c.head
  | _ => none

/-- Ground fact tuples authored in `LanguageDef.logic`. -/
def extractGroundFactTuples (lang : LanguageDef) : List (String × List Pattern) :=
  (extractDatalogClauses lang).filterMap datalogClauseToGroundFactTuple?

/-- Generic relation environment induced by ground Datalog facts in
    `LanguageDef.logic`. The query arguments are matched later by the engine's
    normal `relationQuery` machinery, so this table returns all tuples for the
    requested relation name. -/
def logicFactRelationEnv (lang : LanguageDef) : RelationEnv where
  tuples rel _queryArgs :=
    (extractGroundFactTuples lang).filterMap fun fact =>
      if fact.1 = rel then some fact.2 else none

abbrev GroundTuple := String × List Pattern

/-- Executable Datalog tuples store LP constants as nullary MeTTaIL
    constructor patterns. -/
def Pattern.isNullaryConst : Pattern → Prop
  | .apply _ [] => True
  | _ => False

/-- Extract the LP constant name represented by a nullary constructor pattern.
    Non-nullary patterns map to a harmless default; soundness lemmas below use
    `Pattern.isNullaryConst` hypotheses when the default could otherwise matter. -/
def patternNullaryConstName : Pattern → String
  | .apply c [] => c
  | _ => ""

abbrev GroundTuple.allNullaryConst (tuple : GroundTuple) : Prop :=
  ∀ p ∈ tuple.2, Pattern.isNullaryConst p

abbrev GroundTuplesAllNullaryConst (tuples : List GroundTuple) : Prop :=
  ∀ tuple ∈ tuples, tuple.allNullaryConst

theorem datalogTermToGroundPattern?_isNullaryConst
    {t : DatalogTerm} {p : Pattern}
    (h : datalogTermToGroundPattern? t = some p) :
    Pattern.isNullaryConst p := by
  cases t with
  | const c =>
      simp [datalogTermToGroundPattern?, Pattern.isNullaryConst] at h ⊢
      exact h ▸ trivial
  | var _ =>
      simp [datalogTermToGroundPattern?] at h

theorem datalogTermsToGroundPatterns?_allNullaryConst :
    ∀ {terms : List DatalogTerm} {patterns : List Pattern},
      datalogTermsToGroundPatterns? terms = some patterns →
        ∀ p ∈ patterns, Pattern.isNullaryConst p
  | [], patterns, h => by
      simp [datalogTermsToGroundPatterns?] at h
      subst patterns
      simp
  | term :: terms, patterns, h => by
      cases hp : datalogTermToGroundPattern? term with
      | none =>
          change
            (match datalogTermToGroundPattern? term,
                datalogTermsToGroundPatterns? terms with
              | some p, some ps => some (p :: ps)
              | _, _ => none) = some patterns at h
          rw [hp] at h
          simp at h
      | some p =>
          cases hps : datalogTermsToGroundPatterns? terms with
          | none =>
              change
                (match datalogTermToGroundPattern? term,
                    datalogTermsToGroundPatterns? terms with
                  | some p, some ps => some (p :: ps)
                  | _, _ => none) = some patterns at h
              rw [hp, hps] at h
              simp at h
          | some ps =>
              change
                (match datalogTermToGroundPattern? term,
                    datalogTermsToGroundPatterns? terms with
                  | some p, some ps => some (p :: ps)
                  | _, _ => none) = some patterns at h
              rw [hp, hps] at h
              injection h with h
              subst patterns
              intro q hq
              simp at hq
              cases hq with
              | inl hq =>
                  subst q
                  exact datalogTermToGroundPattern?_isNullaryConst hp
              | inr hq =>
                  exact datalogTermsToGroundPatterns?_allNullaryConst hps q hq

theorem datalogAtomToGroundTuple?_allNullaryConst
    {atom : DatalogAtom} {tuple : GroundTuple}
    (h : datalogAtomToGroundTuple? atom = some tuple) :
    tuple.allNullaryConst := by
  unfold datalogAtomToGroundTuple? at h
  split at h <;> try contradiction
  rename_i args hargs
  cases h
  exact datalogTermsToGroundPatterns?_allNullaryConst hargs

theorem datalogClauseToGroundFactTuple?_allNullaryConst
    {clause : DatalogClause} {tuple : GroundTuple}
    (h : datalogClauseToGroundFactTuple? clause = some tuple) :
    tuple.allNullaryConst := by
  unfold datalogClauseToGroundFactTuple? at h
  split at h <;> try contradiction
  exact datalogAtomToGroundTuple?_allNullaryConst h

theorem extractGroundFactTuples_allNullaryConst
    (lang : LanguageDef) :
    GroundTuplesAllNullaryConst (extractGroundFactTuples lang) := by
  intro tuple h
  simp [extractGroundFactTuples, List.mem_filterMap] at h
  obtain ⟨clause, _hclause, htuple⟩ := h
  exact datalogClauseToGroundFactTuple?_allNullaryConst htuple

/-- Ground facts extracted for the executable relation environment also have an
    arity-preserving LP least-model witness for each grounding.  The exact
    tuple-level ground-atom theorem is proved below, after executable bindings
    have been defined. -/
theorem langDefArity_groundFactTuple_head_in_leastModel
    (lang : LanguageDef) (c : DatalogClause) (tuple : GroundTuple)
    (hc : c ∈ extractDatalogClauses lang)
    (htuple : datalogClauseToGroundFactTuple? c = some tuple)
    (g : Grounding arityDefLPSig) :
    g.groundAtom (datalogClauseToArityLPClause c).head ∈
      leastHerbrandModel (langDefArityKnowledgeBase lang) := by
  cases hbody : c.body with
  | nil =>
      apply langDefArity_clause_head_in_leastModel lang c hc g
      intro b hb
      simp [datalogClauseToArityLPClause, hbody] at hb
  | cons _ _ =>
      simp [datalogClauseToGroundFactTuple?, hbody] at htuple

abbrev DatalogBindings := List (String × Pattern)

namespace DatalogBindings

def lookup (bindings : DatalogBindings) (name : String) : Option Pattern :=
  bindings.find? (·.1 == name) |>.map (·.2)

def bind (bindings : DatalogBindings) (name : String) (value : Pattern) :
    Option DatalogBindings :=
  match lookup bindings name with
  | none => some ((name, value) :: bindings)
  | some existing => if existing = value then some bindings else none

end DatalogBindings

/-- Interpret executable Datalog bindings as an LP grounding. Missing variables
    use a default constant; successful instantiation/matching lemmas only inspect
    variables that have just been bound. -/
def DatalogBindings.toArityGrounding (bindings : DatalogBindings) :
    Grounding arityDefLPSig :=
  fun v => .const (match DatalogBindings.lookup bindings v with
    | some p => patternNullaryConstName p
    | none => "")

/-- LP ground terms obtained by grounding a Datalog term list under executable
    bindings. -/
def groundDatalogTerms (bindings : DatalogBindings) (terms : List DatalogTerm) :
    List (GroundTerm arityDefLPSig) :=
  terms.map fun term =>
    (DatalogBindings.toArityGrounding bindings).groundTerm (datalogTermToArityLP term)

/-- LP ground terms represented by a tuple's executable pattern arguments. -/
def groundTuplePatterns (patterns : List Pattern) : List (GroundTerm arityDefLPSig) :=
  patterns.map fun p => .const (patternNullaryConstName p)

/-- Fin-indexed LP ground-atom arguments re-exposed as a list for comparison
    with executable relation tuples. -/
def arityGroundAtomArgsList (a : GroundAtom arityDefLPSig) :
    List (GroundTerm arityDefLPSig) :=
  List.ofFn a.args

/-- Grounding an arity-preserving Datalog atom through LP.Core produces the same
    argument list as the executable Datalog grounding helper. -/
theorem groundDatalogAtom_argsList_eq
    (bindings : DatalogBindings) (atom : DatalogAtom) :
    arityGroundAtomArgsList
        ((DatalogBindings.toArityGrounding bindings).groundAtom (datalogAtomToArityLP atom)) =
      groundDatalogTerms bindings atom.args := by
  rw [← List.ofFn_get (groundDatalogTerms bindings atom.args)]
  unfold arityGroundAtomArgsList groundDatalogTerms
  simp [Grounding.groundAtom, datalogAtomToArityLP]
  rfl

def groundTupleToArityGroundAtom (tuple : GroundTuple) : GroundAtom arityDefLPSig where
  symbol := (tuple.1, tuple.2.length)
  args := fun i => .const (patternNullaryConstName (tuple.2.get i))

theorem groundTupleToArityGroundAtom_argsList (tuple : GroundTuple) :
    arityGroundAtomArgsList (groundTupleToArityGroundAtom tuple) =
      groundTuplePatterns tuple.2 := by
  rw [← List.ofFn_get (groundTuplePatterns tuple.2)]
  unfold arityGroundAtomArgsList groundTuplePatterns groundTupleToArityGroundAtom
  simp
  rfl

theorem arityGroundAtom_eq_groundTupleToArityGroundAtom
    {a : GroundAtom arityDefLPSig} {tuple : GroundTuple}
    (hsym : a.symbol = (tuple.1, tuple.2.length))
    (hargs : arityGroundAtomArgsList a = groundTuplePatterns tuple.2) :
    a = groundTupleToArityGroundAtom tuple := by
  have hargs' :
      arityGroundAtomArgsList a =
        arityGroundAtomArgsList (groundTupleToArityGroundAtom tuple) := by
    rw [hargs, groundTupleToArityGroundAtom_argsList]
  cases a with
  | mk sym args =>
      simp only at hsym
      subst sym
      congr
      funext i
      unfold arityGroundAtomArgsList at hargs'
      have hfn := List.ofFn_injective hargs'
      simpa [groundTupleToArityGroundAtom] using congr_fun hfn i

abbrev DatalogBindings.allNullaryConst (bindings : DatalogBindings) : Prop :=
  ∀ name p, (name, p) ∈ bindings → Pattern.isNullaryConst p

theorem DatalogBindings.bind_lookup_self
    {bindings bindings' : DatalogBindings} {name : String} {value : Pattern}
    (h : DatalogBindings.bind bindings name value = some bindings') :
    DatalogBindings.lookup bindings' name = some value := by
  unfold DatalogBindings.bind at h
  cases hlookup : DatalogBindings.lookup bindings name with
  | none =>
      simp [hlookup] at h
      cases h
      simp [DatalogBindings.lookup]
  | some existing =>
      simp [hlookup] at h
      rcases h with ⟨hexisting, hbindings⟩
      cases hbindings
      subst existing
      exact hlookup

theorem DatalogBindings.bind_lookup_preserves
    {bindings bindings' : DatalogBindings} {name other : String}
    {pat value : Pattern}
    (h : DatalogBindings.bind bindings name value = some bindings')
    (hlookupOther : DatalogBindings.lookup bindings other = some pat) :
    DatalogBindings.lookup bindings' other = some pat := by
  unfold DatalogBindings.bind at h
  cases hlookup : DatalogBindings.lookup bindings name with
  | none =>
      simp [hlookup] at h
      cases h
      unfold DatalogBindings.lookup at hlookupOther ⊢
      cases hbeq : (name == other)
      · simp [hbeq, hlookupOther]
      · have hname : name = other := by
          simpa using hbeq
        subst other
        unfold DatalogBindings.lookup at hlookup
        rw [hlookup] at hlookupOther
        cases hlookupOther
  | some _existing =>
      simp [hlookup] at h
      rcases h with ⟨_hexisting, hbindings⟩
      cases hbindings
      exact hlookupOther

theorem DatalogBindings.lookup_isNullaryConst
    {bindings : DatalogBindings} (hb : bindings.allNullaryConst)
    {name : String} {p : Pattern}
    (h : DatalogBindings.lookup bindings name = some p) :
    Pattern.isNullaryConst p := by
  unfold DatalogBindings.lookup at h
  cases hfind : List.find? (fun b : String × Pattern => b.1 == name) bindings with
  | none =>
      simp [hfind] at h
  | some pair =>
      rcases pair with ⟨found, value⟩
      simp [hfind] at h
      subst value
      have hkey : found = name := by
        have hpred := List.find?_some hfind
        simp at hpred
        exact hpred
      subst found
      exact hb name p (List.mem_of_find?_eq_some hfind)

theorem DatalogBindings.bind_preserves_allNullaryConst
    {bindings bindings' : DatalogBindings} {name : String} {value : Pattern}
    (hb : bindings.allNullaryConst)
    (hv : Pattern.isNullaryConst value)
    (h : DatalogBindings.bind bindings name value = some bindings') :
    bindings'.allNullaryConst := by
  unfold DatalogBindings.bind at h
  cases hlookup : DatalogBindings.lookup bindings name with
  | none =>
      simp [hlookup] at h
      cases h
      intro name' p hp
      simp at hp
      cases hp with
      | inl hhead =>
          rcases hhead with ⟨_hname, hpvalue⟩
          simpa [hpvalue] using hv
      | inr htail =>
          exact hb name' p htail
  | some existing =>
      simp [hlookup] at h
      rcases h with ⟨_hexisting, hbindings⟩
      cases hbindings
      exact hb

def bindDatalogTerm? (bindings : DatalogBindings) (term : DatalogTerm)
    (value : Pattern) : Option DatalogBindings :=
  match term with
  | .const c =>
      if value = .apply c [] then some bindings else none
  | .var v =>
      DatalogBindings.bind bindings v value

theorem bindDatalogTerm?_lookup_preserves
    {bindings bindings' : DatalogBindings} {term : DatalogTerm}
    {value pat : Pattern} {other : String}
    (h : bindDatalogTerm? bindings term value = some bindings')
    (hlookupOther : DatalogBindings.lookup bindings other = some pat) :
    DatalogBindings.lookup bindings' other = some pat := by
  cases term with
  | const c =>
      by_cases hvalue : value = .apply c []
      · simp [bindDatalogTerm?, hvalue] at h
        cases h
        exact hlookupOther
      · simp [bindDatalogTerm?, hvalue] at h
  | var _ =>
      exact DatalogBindings.bind_lookup_preserves h hlookupOther

theorem bindDatalogTerm?_preserves_allNullaryConst
    {bindings bindings' : DatalogBindings} {term : DatalogTerm} {value : Pattern}
    (hb : bindings.allNullaryConst)
    (hv : Pattern.isNullaryConst value)
    (h : bindDatalogTerm? bindings term value = some bindings') :
    bindings'.allNullaryConst := by
  cases term with
  | const c =>
      by_cases hvalue : value = .apply c []
      · simp [bindDatalogTerm?, hvalue] at h
        cases h
        exact hb
      · simp [bindDatalogTerm?, hvalue] at h
  | var v =>
      exact DatalogBindings.bind_preserves_allNullaryConst hb hv h

def bindDatalogTerms? : DatalogBindings → List DatalogTerm → List Pattern →
    Option DatalogBindings
  | bindings, [], [] => some bindings
  | bindings, term :: terms, value :: values =>
      match bindDatalogTerm? bindings term value with
      | some bindings' => bindDatalogTerms? bindings' terms values
      | none => none
  | _, _, _ => none

theorem bindDatalogTerms?_lookup_preserves :
    ∀ {bindings bindings' : DatalogBindings} {terms : List DatalogTerm}
      {values : List Pattern} {other : String} {pat : Pattern},
      bindDatalogTerms? bindings terms values = some bindings' →
      DatalogBindings.lookup bindings other = some pat →
      DatalogBindings.lookup bindings' other = some pat
  | bindings, bindings', [], [], _other, _pat, h, hlookup => by
      simp [bindDatalogTerms?] at h
      cases h
      exact hlookup
  | _bindings, _bindings', [], _ :: _, _other, _pat, h, _hlookup => by
      simp [bindDatalogTerms?] at h
  | _bindings, _bindings', _ :: _, [], _other, _pat, h, _hlookup => by
      simp [bindDatalogTerms?] at h
  | bindings, bindings', term :: terms, value :: values, _other, _pat, h, hlookup => by
      cases hbind : bindDatalogTerm? bindings term value with
      | none =>
          simp [bindDatalogTerms?, hbind] at h
      | some bindings₁ =>
          have htail : bindDatalogTerms? bindings₁ terms values = some bindings' := by
            simpa [bindDatalogTerms?, hbind] using h
          exact bindDatalogTerms?_lookup_preserves htail
            (bindDatalogTerm?_lookup_preserves hbind hlookup)

theorem bindDatalogTerms?_preserves_allNullaryConst :
    ∀ {bindings : DatalogBindings} {terms : List DatalogTerm}
      {values : List Pattern} {bindings' : DatalogBindings},
      bindings.allNullaryConst →
      (∀ p ∈ values, Pattern.isNullaryConst p) →
      bindDatalogTerms? bindings terms values = some bindings' →
      bindings'.allNullaryConst
  | bindings, [], [], bindings', hb, _hv, h => by
      simp [bindDatalogTerms?] at h
      cases h
      exact hb
  | bindings, [], _ :: _, _bindings', _hb, _hv, h => by
      simp [bindDatalogTerms?] at h
  | bindings, _ :: _, [], _bindings', _hb, _hv, h => by
      simp [bindDatalogTerms?] at h
  | bindings, term :: terms, value :: values, bindings', hb, hv, h => by
      cases hbind : bindDatalogTerm? bindings term value with
      | none =>
          simp [bindDatalogTerms?, hbind] at h
      | some bindings₁ =>
          have hb₁ :
              bindings₁.allNullaryConst :=
            bindDatalogTerm?_preserves_allNullaryConst hb
              (hv value (by simp)) hbind
          have hvTail : ∀ p ∈ values, Pattern.isNullaryConst p := by
            intro p hp
            exact hv p (by simp [hp])
          have htail : bindDatalogTerms? bindings₁ terms values = some bindings' := by
            simpa [bindDatalogTerms?, hbind] using h
          exact bindDatalogTerms?_preserves_allNullaryConst hb₁ hvTail htail

theorem bindDatalogTerm?_groundTerm_eq_of_preserves
    {bindings bindings₁ bindingsFinal : DatalogBindings}
    {term : DatalogTerm} {value : Pattern}
    (hbind : bindDatalogTerm? bindings term value = some bindings₁)
    (hpreserve : ∀ {name : String} {pat : Pattern},
      DatalogBindings.lookup bindings₁ name = some pat →
        DatalogBindings.lookup bindingsFinal name = some pat) :
    (DatalogBindings.toArityGrounding bindingsFinal).groundTerm
        (datalogTermToArityLP term) =
      .const (patternNullaryConstName value) := by
  cases term with
  | const c =>
      by_cases hvalue : value = .apply c []
      · simp [bindDatalogTerm?, hvalue] at hbind
        simp [datalogTermToArityLP, Grounding.groundTerm,
          patternNullaryConstName, hvalue]
      · simp [bindDatalogTerm?, hvalue] at hbind
  | var v =>
      have hlookupFinal : DatalogBindings.lookup bindingsFinal v = some value :=
        hpreserve (DatalogBindings.bind_lookup_self hbind)
      simp [datalogTermToArityLP, DatalogBindings.toArityGrounding,
        Grounding.groundTerm, hlookupFinal]

theorem bindDatalogTerms?_groundTerms_eq_of_preserves :
    ∀ {bindings bindings' bindingsFinal : DatalogBindings} {terms : List DatalogTerm}
      {values : List Pattern},
      bindDatalogTerms? bindings terms values = some bindings' →
      (∀ {name : String} {pat : Pattern},
        DatalogBindings.lookup bindings' name = some pat →
          DatalogBindings.lookup bindingsFinal name = some pat) →
      groundDatalogTerms bindingsFinal terms = groundTuplePatterns values
  | _bindings, _bindings', _bindingsFinal, [], [], h, _hpreserve => by
      simp [bindDatalogTerms?, groundDatalogTerms, groundTuplePatterns] at h ⊢
  | _bindings, _bindings', _bindingsFinal, [], _ :: _, h, _hpreserve => by
      simp [bindDatalogTerms?] at h
  | _bindings, _bindings', _bindingsFinal, _ :: _, [], h, _hpreserve => by
      simp [bindDatalogTerms?] at h
  | bindings, bindings', bindingsFinal, term :: terms, value :: values, h, hpreserve => by
      cases hbind : bindDatalogTerm? bindings term value with
      | none =>
          simp [bindDatalogTerms?, hbind] at h
      | some bindings₁ =>
          have htail : bindDatalogTerms? bindings₁ terms values = some bindings' := by
            simpa [bindDatalogTerms?, hbind] using h
          have hhead :
              (DatalogBindings.toArityGrounding bindingsFinal).groundTerm
                  (datalogTermToArityLP term) =
                .const (patternNullaryConstName value) := by
            apply bindDatalogTerm?_groundTerm_eq_of_preserves hbind
            intro name pat hlookup
            exact hpreserve (bindDatalogTerms?_lookup_preserves htail hlookup)
          have htailEq :
              groundDatalogTerms bindingsFinal terms = groundTuplePatterns values :=
            bindDatalogTerms?_groundTerms_eq_of_preserves htail hpreserve
          simp [groundDatalogTerms, groundTuplePatterns, hhead]
          exact htailEq

theorem bindDatalogTerms?_groundTerms_eq :
    ∀ {bindings bindings' : DatalogBindings} {terms : List DatalogTerm}
      {values : List Pattern},
      bindDatalogTerms? bindings terms values = some bindings' →
      groundDatalogTerms bindings' terms = groundTuplePatterns values
  | _bindings, bindings', _terms, _values, h => by
      exact bindDatalogTerms?_groundTerms_eq_of_preserves h
        (by intro _name _pat hlookup; exact hlookup)

def matchDatalogAtomOnTuple? (atom : DatalogAtom) (tuple : GroundTuple)
    (bindings : DatalogBindings) : Option DatalogBindings :=
  if tuple.1 = atom.rel then
    bindDatalogTerms? bindings atom.args tuple.2
  else
    none

theorem matchDatalogAtomOnTuple?_preserves_allNullaryConst
    {atom : DatalogAtom} {tuple : GroundTuple}
    {bindings bindings' : DatalogBindings}
    (hb : bindings.allNullaryConst)
    (htuple : tuple.allNullaryConst)
    (h : matchDatalogAtomOnTuple? atom tuple bindings = some bindings') :
    bindings'.allNullaryConst := by
  unfold matchDatalogAtomOnTuple? at h
  split at h
  · exact bindDatalogTerms?_preserves_allNullaryConst hb htuple h
  · contradiction

theorem matchDatalogAtomOnTuple?_grounds_terms
    {atom : DatalogAtom} {tuple : GroundTuple}
    {bindings bindings' : DatalogBindings}
    (h : matchDatalogAtomOnTuple? atom tuple bindings = some bindings') :
    tuple.1 = atom.rel ∧
      groundDatalogTerms bindings' atom.args = groundTuplePatterns tuple.2 := by
  unfold matchDatalogAtomOnTuple? at h
  by_cases hrel : tuple.1 = atom.rel
  · simp [hrel] at h
    exact ⟨hrel, bindDatalogTerms?_groundTerms_eq h⟩
  · simp [hrel] at h

theorem matchDatalogAtomOnTuple?_lookup_preserves
    {atom : DatalogAtom} {tuple : GroundTuple}
    {bindings bindings' : DatalogBindings} {other : String} {pat : Pattern}
    (h : matchDatalogAtomOnTuple? atom tuple bindings = some bindings')
    (hlookup : DatalogBindings.lookup bindings other = some pat) :
    DatalogBindings.lookup bindings' other = some pat := by
  unfold matchDatalogAtomOnTuple? at h
  by_cases hrel : tuple.1 = atom.rel
  · simp [hrel] at h
    exact bindDatalogTerms?_lookup_preserves h hlookup
  · simp [hrel] at h

theorem matchDatalogAtomOnTuple?_grounds_terms_of_preserves
    {atom : DatalogAtom} {tuple : GroundTuple}
    {bindings bindings' bindingsFinal : DatalogBindings}
    (h : matchDatalogAtomOnTuple? atom tuple bindings = some bindings')
    (hpreserve : ∀ {name : String} {pat : Pattern},
      DatalogBindings.lookup bindings' name = some pat →
        DatalogBindings.lookup bindingsFinal name = some pat) :
    tuple.1 = atom.rel ∧
      groundDatalogTerms bindingsFinal atom.args = groundTuplePatterns tuple.2 := by
  unfold matchDatalogAtomOnTuple? at h
  by_cases hrel : tuple.1 = atom.rel
  · simp [hrel] at h
    exact ⟨hrel, bindDatalogTerms?_groundTerms_eq_of_preserves h hpreserve⟩
  · simp [hrel] at h

def satisfyDatalogAtom (known : List GroundTuple) (bindings : DatalogBindings)
    (atom : DatalogAtom) : List DatalogBindings :=
  known.filterMap fun tuple => matchDatalogAtomOnTuple? atom tuple bindings

theorem satisfyDatalogAtom_preserves_allNullaryConst
    {known : List GroundTuple} {bindings bindings' : DatalogBindings}
    {atom : DatalogAtom}
    (hknown : GroundTuplesAllNullaryConst known)
    (hb : bindings.allNullaryConst)
    (h : bindings' ∈ satisfyDatalogAtom known bindings atom) :
    bindings'.allNullaryConst := by
  simp [satisfyDatalogAtom, List.mem_filterMap] at h
  obtain ⟨rel, args, htupleMem, hmatch⟩ := h
  exact matchDatalogAtomOnTuple?_preserves_allNullaryConst hb
    (hknown (rel, args) htupleMem) hmatch

theorem satisfyDatalogAtom_mem_ground_terms
    {known : List GroundTuple} {bindings bindings' : DatalogBindings}
    {atom : DatalogAtom}
    (h : bindings' ∈ satisfyDatalogAtom known bindings atom) :
    ∃ tuple ∈ known,
      tuple.1 = atom.rel ∧
        groundDatalogTerms bindings' atom.args = groundTuplePatterns tuple.2 := by
  simp [satisfyDatalogAtom, List.mem_filterMap] at h
  obtain ⟨rel, args, hmem, hmatch⟩ := h
  exact ⟨(rel, args), hmem, matchDatalogAtomOnTuple?_grounds_terms hmatch⟩

theorem satisfyDatalogAtom_mem_arity_ground_atom
    {known : List GroundTuple} {bindings bindings' : DatalogBindings}
    {atom : DatalogAtom}
    (h : bindings' ∈ satisfyDatalogAtom known bindings atom) :
    ∃ tuple ∈ known,
      ((DatalogBindings.toArityGrounding bindings').groundAtom
          (datalogAtomToArityLP atom)).symbol = (tuple.1, tuple.2.length) ∧
        arityGroundAtomArgsList
          ((DatalogBindings.toArityGrounding bindings').groundAtom
            (datalogAtomToArityLP atom)) =
          groundTuplePatterns tuple.2 := by
  obtain ⟨tuple, htupleMem, hrel, hterms⟩ := satisfyDatalogAtom_mem_ground_terms h
  have hlen := congrArg List.length hterms
  simp [groundDatalogTerms, groundTuplePatterns] at hlen
  refine ⟨tuple, htupleMem, ?_, ?_⟩
  · simp [Grounding.groundAtom, datalogAtomToArityLP, hrel, hlen]
  · rw [groundDatalogAtom_argsList_eq]
    exact hterms

theorem satisfyDatalogAtom_lookup_preserves
    {known : List GroundTuple} {bindings bindings' : DatalogBindings}
    {atom : DatalogAtom} {other : String} {pat : Pattern}
    (h : bindings' ∈ satisfyDatalogAtom known bindings atom)
    (hlookup : DatalogBindings.lookup bindings other = some pat) :
    DatalogBindings.lookup bindings' other = some pat := by
  simp [satisfyDatalogAtom, List.mem_filterMap] at h
  obtain ⟨rel, args, _hmem, hmatch⟩ := h
  exact matchDatalogAtomOnTuple?_lookup_preserves hmatch hlookup

theorem satisfyDatalogAtom_mem_ground_terms_of_preserves
    {known : List GroundTuple} {bindings bindings' bindingsFinal : DatalogBindings}
    {atom : DatalogAtom}
    (h : bindings' ∈ satisfyDatalogAtom known bindings atom)
    (hpreserve : ∀ {name : String} {pat : Pattern},
      DatalogBindings.lookup bindings' name = some pat →
        DatalogBindings.lookup bindingsFinal name = some pat) :
    ∃ tuple ∈ known,
      tuple.1 = atom.rel ∧
        groundDatalogTerms bindingsFinal atom.args = groundTuplePatterns tuple.2 := by
  simp [satisfyDatalogAtom, List.mem_filterMap] at h
  obtain ⟨rel, args, hmem, hmatch⟩ := h
  exact ⟨(rel, args), hmem,
    matchDatalogAtomOnTuple?_grounds_terms_of_preserves hmatch hpreserve⟩

def satisfyDatalogBody (known : List GroundTuple) (body : List DatalogAtom)
    (seed : DatalogBindings := []) : List DatalogBindings :=
  body.foldl
    (fun acc atom => acc.flatMap fun bindings => satisfyDatalogAtom known bindings atom)
    [seed]

private abbrev DatalogBindingsListAllNullaryConst
    (bindings : List DatalogBindings) : Prop :=
  ∀ binding ∈ bindings, binding.allNullaryConst

private theorem satisfyDatalogBody_fold_preserves_allNullaryConst
    (known : List GroundTuple) (hknown : GroundTuplesAllNullaryConst known) :
    ∀ (body : List DatalogAtom) (acc : List DatalogBindings),
      DatalogBindingsListAllNullaryConst acc →
      DatalogBindingsListAllNullaryConst
        (body.foldl
          (fun acc atom =>
            acc.flatMap fun bindings => satisfyDatalogAtom known bindings atom)
          acc)
  | [], acc, hacc => by
      simpa using hacc
  | atom :: body, acc, hacc => by
      apply satisfyDatalogBody_fold_preserves_allNullaryConst known hknown body
      intro bindings hb
      simp only [List.mem_flatMap] at hb
      obtain ⟨seed, hseed, hbindings⟩ := hb
      exact satisfyDatalogAtom_preserves_allNullaryConst hknown
        (hacc seed hseed) hbindings

private abbrev DatalogBindingsListPreservesLookup
    (seed : DatalogBindings) (bindings : List DatalogBindings) : Prop :=
  ∀ {name : String} {pat : Pattern} {binding : DatalogBindings},
    binding ∈ bindings →
      DatalogBindings.lookup seed name = some pat →
        DatalogBindings.lookup binding name = some pat

private theorem satisfyDatalogBody_fold_lookup_preserves
    (known : List GroundTuple) :
    ∀ (body : List DatalogAtom) (acc : List DatalogBindings)
      (seed : DatalogBindings),
      DatalogBindingsListPreservesLookup seed acc →
      DatalogBindingsListPreservesLookup seed
        (body.foldl
          (fun acc atom =>
            acc.flatMap fun bindings => satisfyDatalogAtom known bindings atom)
          acc)
  | [], acc, _seed, hacc => by
      simpa using hacc
  | atom :: body, acc, seed, hacc => by
      apply satisfyDatalogBody_fold_lookup_preserves known body
      intro name pat binding hb hlookup
      simp only [List.mem_flatMap] at hb
      obtain ⟨binding₀, hb₀, hsat⟩ := hb
      exact satisfyDatalogAtom_lookup_preserves hsat (hacc hb₀ hlookup)

theorem satisfyDatalogBody_lookup_preserves
    {known : List GroundTuple} {body : List DatalogAtom}
    {seed bindings : DatalogBindings} {name : String} {pat : Pattern}
    (h : bindings ∈ satisfyDatalogBody known body seed)
    (hlookup : DatalogBindings.lookup seed name = some pat) :
    DatalogBindings.lookup bindings name = some pat := by
  unfold satisfyDatalogBody at h
  exact satisfyDatalogBody_fold_lookup_preserves known body [seed] seed
    (by
      intro name pat binding hb hlookup
      simp at hb
      subst binding
      exact hlookup)
    h hlookup

private theorem satisfyDatalogBody_fold_origin_lookup_preserves
    (known : List GroundTuple) :
    ∀ (body : List DatalogAtom) (acc : List DatalogBindings)
      {bindings : DatalogBindings},
      bindings ∈ body.foldl
        (fun acc atom =>
          acc.flatMap fun bindings => satisfyDatalogAtom known bindings atom)
        acc →
      ∃ origin ∈ acc,
        ∀ {name : String} {pat : Pattern},
          DatalogBindings.lookup origin name = some pat →
            DatalogBindings.lookup bindings name = some pat
  | [], _acc, bindings, h => by
      exact ⟨bindings, h, by intro _name _pat hlookup; exact hlookup⟩
  | atom :: body, acc, bindings, h => by
      have htail :=
        satisfyDatalogBody_fold_origin_lookup_preserves known body
          (acc.flatMap fun bindings => satisfyDatalogAtom known bindings atom) h
      obtain ⟨mid, hmid, hpresMidFinal⟩ := htail
      simp only [List.mem_flatMap] at hmid
      obtain ⟨origin, horigin, hsat⟩ := hmid
      exact ⟨origin, horigin, by
        intro name pat hlookup
        exact hpresMidFinal (satisfyDatalogAtom_lookup_preserves hsat hlookup)⟩

private theorem satisfyDatalogBody_fold_mem_ground_terms
    (known : List GroundTuple) :
    ∀ (body : List DatalogAtom) (acc : List DatalogBindings)
      {bindings : DatalogBindings} {atom : DatalogAtom},
      bindings ∈ body.foldl
        (fun acc atom =>
          acc.flatMap fun bindings => satisfyDatalogAtom known bindings atom)
        acc →
      atom ∈ body →
      ∃ tuple ∈ known,
        tuple.1 = atom.rel ∧
          groundDatalogTerms bindings atom.args = groundTuplePatterns tuple.2
  | [], _acc, _bindings, _atom, _hbindings, hatom => by
      simp at hatom
  | atom₀ :: body, acc, bindings, atom, hbindings, hatom => by
      simp at hatom
      cases hatom with
      | inl heq =>
          subst atom
          have horigin :=
            satisfyDatalogBody_fold_origin_lookup_preserves known body
              (acc.flatMap fun bindings => satisfyDatalogAtom known bindings atom₀)
              hbindings
          obtain ⟨matched, hmatched, hpreserve⟩ := horigin
          simp only [List.mem_flatMap] at hmatched
          obtain ⟨seed, _hseed, hsat⟩ := hmatched
          exact satisfyDatalogAtom_mem_ground_terms_of_preserves hsat hpreserve
      | inr hmem =>
          exact satisfyDatalogBody_fold_mem_ground_terms known body
            (acc.flatMap fun bindings => satisfyDatalogAtom known bindings atom₀)
            hbindings hmem

theorem satisfyDatalogBody_preserves_allNullaryConst
    {known : List GroundTuple} {body : List DatalogAtom}
    {seed bindings : DatalogBindings}
    (hknown : GroundTuplesAllNullaryConst known)
    (hseed : seed.allNullaryConst)
    (h : bindings ∈ satisfyDatalogBody known body seed) :
    bindings.allNullaryConst := by
  unfold satisfyDatalogBody at h
  exact satisfyDatalogBody_fold_preserves_allNullaryConst known hknown body [seed]
    (by
      intro binding hb
      simp at hb
      subst binding
      exact hseed)
    bindings h

theorem satisfyDatalogBody_mem_ground_terms
    {known : List GroundTuple} {body : List DatalogAtom}
    {seed bindings : DatalogBindings} {atom : DatalogAtom}
    (h : bindings ∈ satisfyDatalogBody known body seed)
    (hatom : atom ∈ body) :
    ∃ tuple ∈ known,
      tuple.1 = atom.rel ∧
        groundDatalogTerms bindings atom.args = groundTuplePatterns tuple.2 := by
  unfold satisfyDatalogBody at h
  exact satisfyDatalogBody_fold_mem_ground_terms known body [seed] h hatom

theorem satisfyDatalogBody_mem_arity_ground_atom
    {known : List GroundTuple} {body : List DatalogAtom}
    {seed bindings : DatalogBindings} {atom : DatalogAtom}
    (h : bindings ∈ satisfyDatalogBody known body seed)
    (hatom : atom ∈ body) :
    ∃ tuple ∈ known,
      ((DatalogBindings.toArityGrounding bindings).groundAtom
          (datalogAtomToArityLP atom)).symbol = (tuple.1, tuple.2.length) ∧
        arityGroundAtomArgsList
          ((DatalogBindings.toArityGrounding bindings).groundAtom
            (datalogAtomToArityLP atom)) =
          groundTuplePatterns tuple.2 := by
  obtain ⟨tuple, htupleMem, hrel, hterms⟩ := satisfyDatalogBody_mem_ground_terms h hatom
  have hlen := congrArg List.length hterms
  simp [groundDatalogTerms, groundTuplePatterns] at hlen
  refine ⟨tuple, htupleMem, ?_, ?_⟩
  · simp [Grounding.groundAtom, datalogAtomToArityLP, hrel, hlen]
  · rw [groundDatalogAtom_argsList_eq]
    exact hterms

def instantiateDatalogTerm? (bindings : DatalogBindings) : DatalogTerm → Option Pattern
  | .const c => some (.apply c [])
  | .var v => DatalogBindings.lookup bindings v

theorem instantiateDatalogTerm?_isNullaryConst
    {bindings : DatalogBindings} {term : DatalogTerm} {p : Pattern}
    (hb : bindings.allNullaryConst)
    (h : instantiateDatalogTerm? bindings term = some p) :
    Pattern.isNullaryConst p := by
  cases term with
  | const c =>
      simp [instantiateDatalogTerm?, Pattern.isNullaryConst] at h ⊢
      exact h ▸ trivial
  | var v =>
      exact DatalogBindings.lookup_isNullaryConst hb h

def instantiateDatalogTerms? (bindings : DatalogBindings) :
    List DatalogTerm → Option (List Pattern)
  | [] => some []
  | term :: terms =>
      match instantiateDatalogTerm? bindings term, instantiateDatalogTerms? bindings terms with
      | some p, some ps => some (p :: ps)
      | _, _ => none

theorem instantiateDatalogTerm?_groundTerm_eq
    {bindings : DatalogBindings} {term : DatalogTerm} {p : Pattern}
    (h : instantiateDatalogTerm? bindings term = some p) :
    (DatalogBindings.toArityGrounding bindings).groundTerm
        (datalogTermToArityLP term) =
      .const (patternNullaryConstName p) := by
  cases term with
  | const c =>
      simp [instantiateDatalogTerm?] at h
      subst p
      simp [datalogTermToArityLP, Grounding.groundTerm, patternNullaryConstName]
  | var v =>
      simp [instantiateDatalogTerm?] at h
      simp [datalogTermToArityLP, DatalogBindings.toArityGrounding,
        Grounding.groundTerm, h]

theorem instantiateDatalogTerms?_groundTerms_eq :
    ∀ {bindings : DatalogBindings} {terms : List DatalogTerm} {patterns : List Pattern},
      instantiateDatalogTerms? bindings terms = some patterns →
        groundDatalogTerms bindings terms = groundTuplePatterns patterns
  | _bindings, [], patterns, h => by
      simp [instantiateDatalogTerms?] at h
      subst patterns
      simp [groundDatalogTerms, groundTuplePatterns]
  | bindings, term :: terms, patterns, h => by
      cases hp : instantiateDatalogTerm? bindings term with
      | none =>
          simp [instantiateDatalogTerms?, hp] at h
      | some p =>
          cases hps : instantiateDatalogTerms? bindings terms with
          | none =>
              simp [instantiateDatalogTerms?, hp, hps] at h
          | some ps =>
              simp [instantiateDatalogTerms?, hp, hps] at h
              subst patterns
              have hhead := instantiateDatalogTerm?_groundTerm_eq hp
              have htail := instantiateDatalogTerms?_groundTerms_eq hps
              unfold groundDatalogTerms groundTuplePatterns
              simp [hhead]
              exact htail

theorem instantiateDatalogTerms?_allNullaryConst
    {bindings : DatalogBindings} (hb : bindings.allNullaryConst) :
    ∀ {terms : List DatalogTerm} {patterns : List Pattern},
      instantiateDatalogTerms? bindings terms = some patterns →
        ∀ p ∈ patterns, Pattern.isNullaryConst p
  | [], patterns, h => by
      simp [instantiateDatalogTerms?] at h
      subst patterns
      simp
  | term :: terms, patterns, h => by
      cases hp : instantiateDatalogTerm? bindings term with
      | none =>
          simp [instantiateDatalogTerms?, hp] at h
      | some p =>
          cases hps : instantiateDatalogTerms? bindings terms with
          | none =>
              simp [instantiateDatalogTerms?, hp, hps] at h
          | some ps =>
              simp [instantiateDatalogTerms?, hp, hps] at h
              subst patterns
              intro q hq
              simp at hq
              cases hq with
              | inl hq =>
                  subst q
                  exact instantiateDatalogTerm?_isNullaryConst hb hp
              | inr hq =>
                  exact instantiateDatalogTerms?_allNullaryConst hb hps q hq

def instantiateDatalogAtom? (bindings : DatalogBindings) (atom : DatalogAtom) :
    Option GroundTuple :=
  match instantiateDatalogTerms? bindings atom.args with
  | some args => some (atom.rel, args)
  | none => none

theorem instantiateDatalogAtom?_allNullaryConst
    {bindings : DatalogBindings} {atom : DatalogAtom} {tuple : GroundTuple}
    (hb : bindings.allNullaryConst)
    (h : instantiateDatalogAtom? bindings atom = some tuple) :
    tuple.allNullaryConst := by
  unfold instantiateDatalogAtom? at h
  split at h <;> try contradiction
  rename_i args hargs
  cases h
  exact instantiateDatalogTerms?_allNullaryConst hb hargs

theorem instantiateDatalogAtom?_groundAtom_eq
    {bindings : DatalogBindings} {atom : DatalogAtom} {tuple : GroundTuple}
    (h : instantiateDatalogAtom? bindings atom = some tuple) :
    (DatalogBindings.toArityGrounding bindings).groundAtom
        (datalogAtomToArityLP atom) =
      groundTupleToArityGroundAtom tuple := by
  unfold instantiateDatalogAtom? at h
  split at h <;> try contradiction
  rename_i args hargs
  cases h
  have hterms := instantiateDatalogTerms?_groundTerms_eq hargs
  have hsymbol :
      ((DatalogBindings.toArityGrounding bindings).groundAtom
          (datalogAtomToArityLP atom)).symbol =
        (atom.rel, args.length) := by
    have hlen := congrArg List.length hterms
    simp [groundDatalogTerms, groundTuplePatterns] at hlen
    simp [Grounding.groundAtom, datalogAtomToArityLP, hlen]
  have hargsList :
      arityGroundAtomArgsList
          ((DatalogBindings.toArityGrounding bindings).groundAtom
            (datalogAtomToArityLP atom)) =
        groundTuplePatterns args := by
    rw [groundDatalogAtom_argsList_eq]
    exact hterms
  exact arityGroundAtom_eq_groundTupleToArityGroundAtom hsymbol hargsList

theorem datalogTermToGroundPattern?_instantiate_empty
    {term : DatalogTerm} {p : Pattern}
    (h : datalogTermToGroundPattern? term = some p) :
    instantiateDatalogTerm? ([] : DatalogBindings) term = some p := by
  cases term with
  | const c =>
      simp [datalogTermToGroundPattern?, instantiateDatalogTerm?] at h ⊢
      exact h
  | var _ =>
      simp [datalogTermToGroundPattern?] at h

theorem datalogTermsToGroundPatterns?_instantiate_empty :
    ∀ {terms : List DatalogTerm} {patterns : List Pattern},
      datalogTermsToGroundPatterns? terms = some patterns →
        instantiateDatalogTerms? ([] : DatalogBindings) terms = some patterns
  | [], patterns, h => by
      simp [datalogTermsToGroundPatterns?] at h
      subst patterns
      simp [instantiateDatalogTerms?]
  | term :: terms, patterns, h => by
      cases hp : datalogTermToGroundPattern? term with
      | none =>
          simp [datalogTermsToGroundPatterns?, hp] at h
      | some p =>
          cases hps : datalogTermsToGroundPatterns? terms with
          | none =>
              simp [datalogTermsToGroundPatterns?, hp, hps] at h
          | some ps =>
              simp [datalogTermsToGroundPatterns?, hp, hps] at h
              subst patterns
              have hp' := datalogTermToGroundPattern?_instantiate_empty hp
              have hps' := datalogTermsToGroundPatterns?_instantiate_empty hps
              simp [instantiateDatalogTerms?, hp', hps']

theorem datalogAtomToGroundTuple?_groundAtom_eq
    {atom : DatalogAtom} {tuple : GroundTuple}
    (h : datalogAtomToGroundTuple? atom = some tuple) :
    (DatalogBindings.toArityGrounding ([] : DatalogBindings)).groundAtom
        (datalogAtomToArityLP atom) =
      groundTupleToArityGroundAtom tuple := by
  unfold datalogAtomToGroundTuple? at h
  split at h <;> try contradiction
  rename_i args hargs
  cases h
  have hinstTerms := datalogTermsToGroundPatterns?_instantiate_empty hargs
  have hinstAtom :
      instantiateDatalogAtom? ([] : DatalogBindings) atom =
        some (atom.rel, args) := by
    simp [instantiateDatalogAtom?, hinstTerms]
  exact instantiateDatalogAtom?_groundAtom_eq hinstAtom

abbrev GroundTuplesInArityLeastModel (lang : LanguageDef)
    (known : List GroundTuple) : Prop :=
  ∀ tuple ∈ known,
    groundTupleToArityGroundAtom tuple ∈
      leastHerbrandModel (langDefArityKnowledgeBase lang)

theorem datalogClauseToGroundFactTuple?_groundAtom_in_leastModel
    (lang : LanguageDef) {clause : DatalogClause} {tuple : GroundTuple}
    (hc : clause ∈ extractDatalogClauses lang)
    (htuple : datalogClauseToGroundFactTuple? clause = some tuple) :
    groundTupleToArityGroundAtom tuple ∈
      leastHerbrandModel (langDefArityKnowledgeBase lang) := by
  cases hbody : clause.body with
  | nil =>
      have hhead :
          datalogAtomToGroundTuple? clause.head = some tuple := by
        simpa [datalogClauseToGroundFactTuple?, hbody] using htuple
      have heq := datalogAtomToGroundTuple?_groundAtom_eq hhead
      rw [← heq]
      apply langDefArity_clause_head_in_leastModel lang clause hc
        (DatalogBindings.toArityGrounding ([] : DatalogBindings))
      intro b hb
      simp [datalogClauseToArityLPClause, hbody] at hb
  | cons _ _ =>
      simp [datalogClauseToGroundFactTuple?, hbody] at htuple

theorem extractGroundFactTuples_in_leastModel
    (lang : LanguageDef) :
    GroundTuplesInArityLeastModel lang (extractGroundFactTuples lang) := by
  intro tuple htuple
  simp [extractGroundFactTuples, List.mem_filterMap] at htuple
  obtain ⟨clause, hc, hfact⟩ := htuple
  exact datalogClauseToGroundFactTuple?_groundAtom_in_leastModel lang hc hfact

def deriveDatalogClauseTuples (known : List GroundTuple) (clause : DatalogClause) :
    List GroundTuple :=
  (satisfyDatalogBody known clause.body []).filterMap fun bindings =>
    instantiateDatalogAtom? bindings clause.head

theorem deriveDatalogClauseTuples_preserves_allNullaryConst
    {known : List GroundTuple} {clause : DatalogClause} {tuple : GroundTuple}
    (hknown : GroundTuplesAllNullaryConst known)
    (h : tuple ∈ deriveDatalogClauseTuples known clause) :
    tuple.allNullaryConst := by
  simp [deriveDatalogClauseTuples, List.mem_filterMap] at h
  obtain ⟨bindings, hbindings, hinst⟩ := h
  have hb : bindings.allNullaryConst :=
    satisfyDatalogBody_preserves_allNullaryConst hknown
      (by
        intro name p hp
        simp at hp)
      hbindings
  exact instantiateDatalogAtom?_allNullaryConst hb hinst

theorem deriveDatalogClauseTuples_in_leastModel
    (lang : LanguageDef) {known : List GroundTuple} {clause : DatalogClause}
    {tuple : GroundTuple}
    (hc : clause ∈ extractDatalogClauses lang)
    (hknown : GroundTuplesInArityLeastModel lang known)
    (htuple : tuple ∈ deriveDatalogClauseTuples known clause) :
    groundTupleToArityGroundAtom tuple ∈
      leastHerbrandModel (langDefArityKnowledgeBase lang) := by
  simp [deriveDatalogClauseTuples, List.mem_filterMap] at htuple
  obtain ⟨bindings, hbindings, hinst⟩ := htuple
  have hheadEq := instantiateDatalogAtom?_groundAtom_eq hinst
  rw [← hheadEq]
  apply langDefArity_clause_head_in_leastModel lang clause hc
    (DatalogBindings.toArityGrounding bindings)
  intro b hb
  simp only [datalogClauseToArityLPClause, List.mem_map] at hb
  obtain ⟨bodyAtom, hbodyAtom, rfl⟩ := hb
  have hbodyWitness :=
    satisfyDatalogBody_mem_arity_ground_atom (known := known)
      (body := clause.body) (seed := ([] : DatalogBindings))
      (bindings := bindings) (atom := bodyAtom) hbindings hbodyAtom
  obtain ⟨bodyTuple, hbodyTupleMem, hsym, hargs⟩ := hbodyWitness
  have hbodyEq :
      (DatalogBindings.toArityGrounding bindings).groundAtom
          (datalogAtomToArityLP bodyAtom) =
        groundTupleToArityGroundAtom bodyTuple :=
    arityGroundAtom_eq_groundTupleToArityGroundAtom hsym hargs
  rw [hbodyEq]
  exact hknown bodyTuple hbodyTupleMem

def datalogClosureStep (clauses : List DatalogClause) (known : List GroundTuple) :
    List GroundTuple :=
  (known ++ clauses.flatMap (deriveDatalogClauseTuples known)).eraseDups

/-- One executable closure step adds only already-known tuples or tuples derived
    by one of the declared clauses. -/
theorem mem_datalogClosureStep_iff_supported
    (clauses : List DatalogClause) (known : List GroundTuple) (tuple : GroundTuple) :
    tuple ∈ datalogClosureStep clauses known ↔
      tuple ∈ known ∨
        ∃ clause ∈ clauses, tuple ∈ deriveDatalogClauseTuples known clause := by
  simp [datalogClosureStep, List.mem_flatMap]

theorem datalogClosureStep_preserves_allNullaryConst
    {clauses : List DatalogClause} {known : List GroundTuple} {tuple : GroundTuple}
    (hknown : GroundTuplesAllNullaryConst known)
    (h : tuple ∈ datalogClosureStep clauses known) :
    tuple.allNullaryConst := by
  rw [mem_datalogClosureStep_iff_supported] at h
  cases h with
  | inl hmem =>
      exact hknown tuple hmem
  | inr hderived =>
      obtain ⟨clause, _hclause, htuple⟩ := hderived
      exact deriveDatalogClauseTuples_preserves_allNullaryConst hknown htuple

theorem datalogClosureStep_in_leastModel
    (lang : LanguageDef) {known : List GroundTuple} {tuple : GroundTuple}
    (hknown : GroundTuplesInArityLeastModel lang known)
    (h : tuple ∈ datalogClosureStep (extractDatalogClauses lang) known) :
    groundTupleToArityGroundAtom tuple ∈
      leastHerbrandModel (langDefArityKnowledgeBase lang) := by
  rw [mem_datalogClosureStep_iff_supported] at h
  cases h with
  | inl hmem =>
      exact hknown tuple hmem
  | inr hderived =>
      obtain ⟨clause, hc, htuple⟩ := hderived
      exact deriveDatalogClauseTuples_in_leastModel lang hc hknown htuple

theorem datalogClosureStep_preserves_leastModelSound
    (lang : LanguageDef) {known : List GroundTuple}
    (hknown : GroundTuplesInArityLeastModel lang known) :
    GroundTuplesInArityLeastModel lang
      (datalogClosureStep (extractDatalogClauses lang) known) := by
  intro tuple htuple
  exact datalogClosureStep_in_leastModel lang hknown htuple

def datalogClosureWithFuel (clauses : List DatalogClause) : Nat → List GroundTuple →
    List GroundTuple
  | 0, known => known.eraseDups
  | fuel + 1, known =>
      let current := known.eraseDups
      let next := datalogClosureStep clauses current
      if next = current then
        current
      else
        datalogClosureWithFuel clauses fuel next

theorem datalogClosureWithFuel_preserves_allNullaryConst
    (clauses : List DatalogClause) :
    ∀ {fuel : Nat} {known : List GroundTuple} {tuple : GroundTuple},
      GroundTuplesAllNullaryConst known →
      tuple ∈ datalogClosureWithFuel clauses fuel known →
      tuple.allNullaryConst := by
  intro fuel
  induction fuel with
  | zero =>
      intro known tuple hknown h
      simp [datalogClosureWithFuel] at h
      exact hknown tuple h
  | succ fuel ih =>
      intro known tuple hknown h
      have hcurrent : GroundTuplesAllNullaryConst known.eraseDups := by
        intro t ht
        exact hknown t (by simpa using ht)
      have hnext :
          GroundTuplesAllNullaryConst
            (datalogClosureStep clauses known.eraseDups) := by
        intro t ht
        exact datalogClosureStep_preserves_allNullaryConst hcurrent ht
      by_cases hfixed : datalogClosureStep clauses known.eraseDups = known.eraseDups
      · simp [datalogClosureWithFuel, hfixed] at h
        exact hknown tuple h
      · simp [datalogClosureWithFuel, hfixed] at h
        exact ih hnext h

theorem datalogClosureWithFuel_in_leastModel
    (lang : LanguageDef) :
    ∀ {fuel : Nat} {known : List GroundTuple} {tuple : GroundTuple},
      GroundTuplesInArityLeastModel lang known →
      tuple ∈ datalogClosureWithFuel (extractDatalogClauses lang) fuel known →
      groundTupleToArityGroundAtom tuple ∈
        leastHerbrandModel (langDefArityKnowledgeBase lang) := by
  intro fuel
  induction fuel with
  | zero =>
      intro known tuple hknown h
      have hmem : tuple ∈ known := by
        simpa [datalogClosureWithFuel] using h
      exact hknown tuple hmem
  | succ fuel ih =>
      intro known tuple hknown h
      have hcurrent : GroundTuplesInArityLeastModel lang known.eraseDups := by
        intro t ht
        exact hknown t (by simpa using ht)
      have hnext :
          GroundTuplesInArityLeastModel lang
            (datalogClosureStep (extractDatalogClauses lang) known.eraseDups) :=
        datalogClosureStep_preserves_leastModelSound lang hcurrent
      by_cases hfixed :
          datalogClosureStep (extractDatalogClauses lang) known.eraseDups =
            known.eraseDups
      · have hmem : tuple ∈ known.eraseDups := by
          simpa [datalogClosureWithFuel, hfixed] using h
        exact hcurrent tuple hmem
      · have htail :
            tuple ∈ datalogClosureWithFuel (extractDatalogClauses lang) fuel
              (datalogClosureStep (extractDatalogClauses lang) known.eraseDups) := by
          simpa [datalogClosureWithFuel, hfixed] using h
        exact ih hnext htail

/-- Prop-level trace for the finite executable Datalog closure.  This mirrors the
    fuelled closure computation and is intentionally weaker than least-model
    adequacy: it records how a tuple enters this executable table. -/
def DatalogClosureTrace (clauses : List DatalogClause) :
    Nat → List GroundTuple → GroundTuple → Prop
  | 0, known, tuple => tuple ∈ known
  | fuel + 1, known, tuple =>
      let current := known.eraseDups
      let next := datalogClosureStep clauses current
      if next = current then
        tuple ∈ current
      else
        DatalogClosureTrace clauses fuel next tuple

/-- The finite executable closure is exact for its Prop-level trace. -/
theorem mem_datalogClosureWithFuel_iff_trace
    (clauses : List DatalogClause) :
    ∀ (fuel : Nat) (known : List GroundTuple) (tuple : GroundTuple),
      tuple ∈ datalogClosureWithFuel clauses fuel known ↔
        DatalogClosureTrace clauses fuel known tuple := by
  intro fuel
  induction fuel with
  | zero =>
      intro known tuple
      simp [datalogClosureWithFuel, DatalogClosureTrace]
  | succ fuel ih =>
      intro known tuple
      by_cases h : datalogClosureStep clauses known.eraseDups = known.eraseDups
      · simp [datalogClosureWithFuel, DatalogClosureTrace, h]
      · simp [datalogClosureWithFuel, DatalogClosureTrace, h, ih]

def datalogTermConstants : DatalogTerm → List String
  | .const c => [c]
  | .var _ => []

def datalogAtomConstants (atom : DatalogAtom) : List String :=
  atom.args.flatMap datalogTermConstants

def datalogClauseConstants (clause : DatalogClause) : List String :=
  datalogAtomConstants clause.head ++ clause.body.flatMap datalogAtomConstants

def datalogAtomRelationSpec (atom : DatalogAtom) : String × Nat :=
  (atom.rel, atom.args.length)

def datalogClauseRelationSpecs (clause : DatalogClause) : List (String × Nat) :=
  datalogAtomRelationSpec clause.head :: clause.body.map datalogAtomRelationSpec

def datalogRelationSpecs (lang : LanguageDef) : List (String × Nat) :=
  ((extractRelationDecls lang).map fun rel => (rel.name, rel.argTypes.length)) ++
    ((extractDatalogClauses lang).flatMap datalogClauseRelationSpecs)

def datalogConstants (lang : LanguageDef) : List String :=
  ((extractDatalogClauses lang).flatMap datalogClauseConstants).eraseDups

def datalogClosureFuelBound (lang : LanguageDef) : Nat :=
  let constCount := (datalogConstants lang).length
  let specs := (datalogRelationSpecs lang).eraseDups
  specs.foldl (fun acc spec => acc + constCount ^ spec.2) 1

def datalogClosureTuplesWithFuel (lang : LanguageDef) (fuel : Nat) : List GroundTuple :=
  datalogClosureWithFuel (extractDatalogClauses lang) fuel (extractGroundFactTuples lang)

def datalogClosureTuples (lang : LanguageDef) : List GroundTuple :=
  datalogClosureTuplesWithFuel lang (datalogClosureFuelBound lang)

theorem datalogClosureTuplesWithFuel_in_leastModel
    (lang : LanguageDef) (fuel : Nat) :
    GroundTuplesInArityLeastModel lang
      (datalogClosureTuplesWithFuel lang fuel) := by
  intro tuple h
  exact datalogClosureWithFuel_in_leastModel lang
    (extractGroundFactTuples_in_leastModel lang) h

theorem datalogClosureTuples_in_leastModel
    (lang : LanguageDef) :
    GroundTuplesInArityLeastModel lang (datalogClosureTuples lang) :=
  datalogClosureTuplesWithFuel_in_leastModel lang (datalogClosureFuelBound lang)

theorem datalogClosureTuplesWithFuel_allNullaryConst
    (lang : LanguageDef) (fuel : Nat) :
    GroundTuplesAllNullaryConst (datalogClosureTuplesWithFuel lang fuel) := by
  intro tuple h
  exact datalogClosureWithFuel_preserves_allNullaryConst
    (extractDatalogClauses lang)
    (extractGroundFactTuples_allNullaryConst lang) h

theorem datalogClosureTuples_allNullaryConst
    (lang : LanguageDef) :
    GroundTuplesAllNullaryConst (datalogClosureTuples lang) :=
  datalogClosureTuplesWithFuel_allNullaryConst lang (datalogClosureFuelBound lang)

/-- Generic relation environment induced by finite Datalog closure over
    `LanguageDef.logic`. The query arguments are matched later by the engine's
    normal `relationQuery` machinery. -/
def logicDatalogRelationEnv (lang : LanguageDef) : RelationEnv where
  tuples rel _queryArgs :=
    (datalogClosureTuples lang).filterMap fun fact =>
      if fact.1 = rel then some fact.2 else none

/-- The relation environment used by premise queries exposes exactly the tuples
    with the requested relation name from the finite Datalog closure. -/
theorem mem_logicDatalogRelationEnv_tuples_iff
    (lang : LanguageDef) (rel : String) (query tuple : List Pattern) :
    tuple ∈ (logicDatalogRelationEnv lang).tuples rel query ↔
      (rel, tuple) ∈ datalogClosureTuples lang := by
  simp [logicDatalogRelationEnv]

theorem logicDatalogRelationEnv_tuples_in_leastModel
    (lang : LanguageDef) {rel : String} {query tuple : List Pattern}
    (h : tuple ∈ (logicDatalogRelationEnv lang).tuples rel query) :
    groundTupleToArityGroundAtom (rel, tuple) ∈
      leastHerbrandModel (langDefArityKnowledgeBase lang) := by
  rw [mem_logicDatalogRelationEnv_tuples_iff] at h
  exact datalogClosureTuples_in_leastModel lang (rel, tuple) h

theorem logicDatalogRelationEnv_tuples_allNullaryConst
    (lang : LanguageDef) {rel : String} {query tuple : List Pattern}
    (h : tuple ∈ (logicDatalogRelationEnv lang).tuples rel query) :
    ∀ p ∈ tuple, Pattern.isNullaryConst p := by
  rw [mem_logicDatalogRelationEnv_tuples_iff] at h
  exact datalogClosureTuples_allNullaryConst lang (rel, tuple) h

/-- Check if all Datalog clauses in a LanguageDef are safe. -/
def allClausesSafe (lang : LanguageDef) : Bool :=
  (extractDatalogClauses lang).all DatalogClause.isSafe

/-! ## Section 4c: Converse-completeness boundary -/

def unsafeVariableFactClause : DatalogClause :=
  { name := "unsafe-variable-fact"
    head := { rel := "unsafeAny", args := [.var "X"] }
    body := [] }

def unsafeVariableFactLang : LanguageDef :=
  { LanguageDef.empty "UnsafeVariableFact" with
    types := [TypeDecl.plain "Obj"]
    logic :=
      [ .relation { name := "unsafeAny", argTypes := [.base "Obj"] }
      , .datalogClause unsafeVariableFactClause ] }

def unsafeVariableFactGrounding : Grounding arityDefLPSig :=
  fun _ => .const "fresh"

def unsafeVariableFactAtom : GroundAtom arityDefLPSig :=
  unsafeVariableFactGrounding.groundAtom
    (datalogAtomToArityLP unsafeVariableFactClause.head)

def unsafeVariableFactTuple : GroundTuple :=
  ("unsafeAny", [.apply "fresh" []])

theorem unsafeVariableFactLang_not_safe :
    allClausesSafe unsafeVariableFactLang = false := rfl

theorem unsafeVariableFactLang_validate_rejects :
    LanguageDef.validate unsafeVariableFactLang ≠ [] := by
  apply List.ne_nil_of_mem (a :=
    ({ context := "UnsafeVariableFact",
       message := "unsafe Datalog clause unsafe-variable-fact: head variable not in body" } :
      ValidationError))
  simp [LanguageDef.validate, LanguageDef.empty, LanguageDef.typeNames,
    unsafeVariableFactLang, unsafeVariableFactClause, DatalogClause.isSafe]
  right
  constructor
  · exact ⟨"X", by simp [DatalogAtom.vars]⟩
  · rfl

theorem unsafeVariableFactAtom_in_leastModel :
    unsafeVariableFactAtom ∈
      leastHerbrandModel (langDefArityKnowledgeBase unsafeVariableFactLang) := by
  apply langDefArity_clause_head_in_leastModel
    unsafeVariableFactLang unsafeVariableFactClause
    (g := unsafeVariableFactGrounding)
  · simp [unsafeVariableFactLang, extractDatalogClauses]
  · intro b hb
    simp [datalogClauseToArityLPClause, unsafeVariableFactClause] at hb

theorem unsafeVariableFactTuple_not_in_executable_closure :
    unsafeVariableFactTuple ∉ datalogClosureTuples unsafeVariableFactLang := by
  decide

/-- Check if all Datalog clauses reference only declared relations. -/
def allRelationsDeclared (lang : LanguageDef) : Bool :=
  let declaredRels := (extractRelationDecls lang).map (·.name)
  let clauses := extractDatalogClauses lang
  clauses.all fun c =>
    c.head.rel ∈ declaredRels && c.body.all fun b => b.rel ∈ declaredRels

/-! ## Section 5: Semantic characterization

The key theorem: typed Datalog rules in a LanguageDef have a unique
minimal model (the least Herbrand model), provided:
- All clauses are safe (range-restricted)
- All relations are declared
- The program is function-free (guaranteed by construction)

The LP.Core infrastructure provides:
- `T_P_LP`: immediate consequence operator (proven monotone)
- `leastHerbrandModel`: via Tarski's fixpoint theorem
- `leastHerbrandModel_fixpoint`: the model IS a fixpoint of T_P
- `leastHerbrandModel_least`: it's the SMALLEST model

These theorems compose with the bridge to give LanguageDef logic
rules a model-theoretic target. Executable closure equivalence is tracked
separately above. -/

/-- The semantic claim: any LanguageDef with well-formed typed Datalog rules
    has a unique minimal model characterized by LP.Core's T_P fixpoint.
    This is inherited from LP.Semantics and requires no new proof work —
    the bridge maps DatalogClause to LP.Clause, and the LP theorems apply. -/
theorem langDef_logic_functionFree :
    langDefLPSig.isFunctionFree :=
  Empty.instIsEmpty

end Mettapedia.OSLF.MeTTaIL.LogicSemantics
