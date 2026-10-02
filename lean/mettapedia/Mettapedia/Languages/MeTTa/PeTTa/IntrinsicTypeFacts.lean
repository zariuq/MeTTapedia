import Mettapedia.Logic.LP.UnificationRenaming
import Mettapedia.Machines.RevisionedQueryFacts
import Mathlib.Data.Nat.Pairing

/-!
# Ordered intrinsic PeTTa facts for closed leaf subjects

This is the leaf boundary of the native intrinsic query service. The rules
are the primitive and declaration clauses of `get_type_candidate`: a
primitive clause cuts only after its output matches the incoming requirement.
Thus checking a number against a different declared type can reach the
declaration clause, although fresh inference cuts at `Number`.

The source scans declarations in occurrence order. An independently built
index produces canonical answer schemes. The comparison retains order and
duplicates, uses the existing total LP unifier for closed requirements, and
proves that invocation freshening can occur after computing the facts.

Native cache admission also excludes non-symbol declaration subjects and
authored classifiers. The latter exclusion belongs to the guard adapter:
this module specifies intrinsic clauses only. Function application,
elementwise structural queries and the memoized traversal bound remain
separate obligations; this leaf result does not certify that larger family.
Native allocation, revision maintenance and pointer ownership are outside
the mathematical source/index comparison.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.IntrinsicTypeFacts

open Mettapedia.Logic.LP
open Mettapedia.Logic.LP.UnificationRenaming
open Mettapedia.Machines

/-- Closed non-expression subjects. Numeric representation does not affect
the primitive rule, so its spelling is retained without interpreting it. -/
inductive Scalar where
  | symbol (name : String)
  | number (lexeme : String)
  | string (value : String)
  | boolean (value : Bool)
  deriving DecidableEq, Repr

/-- Proper expressions, including arrow schemes, use the existing LP term
constructor at their actual arity. Type and value variables share one syntax. -/
abbrev signature : LPSignature where
  constants := Scalar
  vars := Nat
  relationSymbols := Unit
  relationArity _ := 0
  functionSymbols := Nat
  functionArity := id

abbrev TypeTerm := Term signature
abbrev ClosedType := GroundTerm signature

def named (name : String) : TypeTerm := .const (.symbol name)
def undefinedType : TypeTerm := named "%Undefined%"

def primitiveType : Scalar → Option TypeTerm
  | .number _ => some (named "Number")
  | .string _ => some (named "String")
  | .boolean _ => some (named "Bool")
  | .symbol _ => none

structure Declaration where
  occurrence : Nat
  subject : Scalar
  scheme : TypeTerm

structure Inventory where
  rows : List Declaration
  distinct : (rows.map Declaration.occurrence).Nodup

def SymbolOnly (inventory : Inventory) : Prop :=
  ∀ row ∈ inventory.rows, ∃ name, row.subject = .symbol name

/-- An occurrence scope separates identically spelled declaration variables;
an invocation scope separates uses of a retained fact. Neither changes the
constructors or repeated occurrences within a scheme. -/
def scope (identity : Nat) (term : TypeTerm) : TypeTerm :=
  rename (Nat.pair identity) term

theorem scope_injective (identity : Nat) : Function.Injective (scope identity) :=
  rename_injective (σ := signature) (Nat.pair identity) (fun name => (Nat.unpair name).2)
    (fun name => by simp)

theorem scope_preserves_ground (identity : Nat) (term : TypeTerm)
    (closed : term.isGround) : scope identity term = term := by
  induction term with
  | var _ => cases closed
  | const _ => rfl
  | app function children ih =>
      simp only [scope, rename_app]
      congr 1
      funext i
      exact ih i (closed i)

theorem occurrence_names_equal_iff (invocation first second left right : Nat) :
    Nat.pair invocation (Nat.pair first left) =
      Nat.pair invocation (Nat.pair second right) ↔
      first = second ∧ left = right := by
  simp only [Nat.pair_eq_pair, true_and]

theorem invocation_names_disjoint (first second occurrence slot : Nat)
    (different : first ≠ second) (otherOccurrence otherSlot : Nat) :
    Nat.pair first (Nat.pair occurrence slot) ≠
      Nat.pair second (Nat.pair otherOccurrence otherSlot) := by
  intro same
  exact different (Nat.pair_eq_pair.mp same).1

theorem scoped_variable_origin (identity : Nat) (term : TypeTerm) (name : Nat)
    (member : name ∈ (scope identity term).freeVars) :
    ∃ original ∈ term.freeVars, name = Nat.pair identity original := by
  induction term with
  | var original =>
      refine ⟨original, by simp [Term.freeVars], ?_⟩
      simpa [scope, rename, Subst.applyTerm, Term.freeVars] using member
  | const _ => simp [scope, rename, Subst.applyTerm, Term.freeVars] at member
  | app function children ih =>
      change name ∈ Finset.biUnion Finset.univ
        (fun i => (scope identity (children i)).freeVars) at member
      obtain ⟨i, _, childMember⟩ := Finset.mem_biUnion.mp member
      obtain ⟨original, present, same⟩ := ih i childMember
      exact ⟨original, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, present⟩, same⟩

theorem declaration_occurrences_disjoint (invocation first second : Nat)
    (left right : TypeTerm) (different : first ≠ second) :
    Disjoint (scope invocation (scope first left)).freeVars
      (scope invocation (scope second right)).freeVars := by
  apply Finset.disjoint_left.mpr
  intro name inLeft inRight
  obtain ⟨leftName, leftMember, leftEq⟩ :=
    scoped_variable_origin invocation (scope first left) name inLeft
  obtain ⟨rightName, rightMember, rightEq⟩ :=
    scoped_variable_origin invocation (scope second right) name inRight
  obtain ⟨leftSlot, _, leftScope⟩ := scoped_variable_origin first left leftName leftMember
  obtain ⟨rightSlot, _, rightScope⟩ := scoped_variable_origin second right rightName rightMember
  rw [leftScope] at leftEq
  rw [rightScope] at rightEq
  exact different ((occurrence_names_equal_iff invocation first second leftSlot rightSlot).mp
    (leftEq.symm.trans rightEq)).1

theorem inventory_rows_fresh (inventory : Inventory) (invocation : Nat)
    (first second : Declaration) (firstMember : first ∈ inventory.rows)
    (secondMember : second ∈ inventory.rows) (different : first ≠ second) :
    Disjoint (scope invocation (scope first.occurrence first.scheme)).freeVars
      (scope invocation (scope second.occurrence second.scheme)).freeVars := by
  apply declaration_occurrences_disjoint
  intro same
  exact different (List.inj_on_of_nodup_map inventory.distinct firstMember secondMember same)

theorem invocation_variables_disjoint (first second : Nat) (left right : TypeTerm)
    (different : first ≠ second) :
    Disjoint (scope first left).freeVars (scope second right).freeVars := by
  apply Finset.disjoint_left.mpr
  intro name inLeft inRight
  obtain ⟨leftSlot, _, leftEq⟩ := scoped_variable_origin first left name inLeft
  obtain ⟨rightSlot, _, rightEq⟩ := scoped_variable_origin second right name inRight
  exact different (Nat.pair_eq_pair.mp (leftEq.symm.trans rightEq)).1

/-- Source declaration enumeration, without deduplication or reordering. -/
def sourceDeclarations (subject : Scalar) : List Declaration → List TypeTerm
  | [] => []
  | row :: later =>
      if row.subject = subject then
        scope row.occurrence row.scheme :: sourceDeclarations subject later
      else sourceDeclarations subject later

abbrev Index := List (Scalar × List TypeTerm)

def bucket (subject : Scalar) : Index → List TypeTerm
  | [] => []
  | (name, facts) :: later => if name = subject then facts else bucket subject later

def prependBucket (subject : Scalar) (fact : TypeTerm) : Index → Index
  | [] => [(subject, [fact])]
  | (name, facts) :: later =>
      if name = subject then (name, fact :: facts) :: later
      else (name, facts) :: prependBucket subject fact later

theorem bucket_prepend (subject name : Scalar) (fact : TypeTerm) (index : Index) :
    bucket subject (prependBucket name fact index) =
      if name = subject then fact :: bucket subject index else bucket subject index := by
  induction index with
  | nil => simp only [prependBucket, bucket]
  | cons pair later ih =>
      rcases pair with ⟨key, facts⟩
      by_cases sameKey : key = name
      · subst key
        simp only [prependBucket, ↓reduceIte, bucket]
        split <;> rfl
      · by_cases queriedKey : key = subject
        · subst key
          have different : name ≠ subject := Ne.symm sameKey
          simp only [prependBucket, sameKey, ↓reduceIte, bucket, different]
        · simp only [prependBucket, sameKey, ↓reduceIte, bucket, queriedKey, ih]

/-- The index is a finite bucket inventory built before querying it. -/
def buildIndex : List Declaration → Index
  | [] => []
  | row :: later =>
      prependBucket row.subject (scope row.occurrence row.scheme) (buildIndex later)

theorem index_matches_source (rows : List Declaration) (subject : Scalar) :
    bucket subject (buildIndex rows) = sourceDeclarations subject rows := by
  induction rows with
  | nil => rfl
  | cons row later ih =>
      simp only [buildIndex, bucket_prepend, sourceDeclarations, ih]

/-- Live source materialization activates each declaration occurrence before
it is used. The cache will activate the entire retained vector afterward. -/
def sourceActiveDeclarations (invocation : Nat) (subject : Scalar) :
    List Declaration → List TypeTerm
  | [] => []
  | row :: later =>
      if row.subject = subject then
        scope invocation (scope row.occurrence row.scheme) ::
          sourceActiveDeclarations invocation subject later
      else sourceActiveDeclarations invocation subject later

theorem source_activation_commutes (invocation : Nat) (subject : Scalar)
    (rows : List Declaration) :
    sourceActiveDeclarations invocation subject rows =
      (sourceDeclarations subject rows).map (scope invocation) := by
  induction rows with
  | nil => rfl
  | cons row later ih =>
      simp only [sourceActiveDeclarations, sourceDeclarations]
      split <;> simp only [List.map_cons, ih]

inductive Mode where
  | fresh
  | rootVariable
  | bound (required : ClosedType)

structure Query where
  subject : Scalar
  mode : Mode

/-- A total unifier failure is a logical failure, never exhausted fuel. -/
def accepts (candidate required : TypeTerm) : Bool :=
  (unifyTotal [(candidate, required)]).isSome

theorem accepts_iff_unifiable (candidate required : TypeTerm) :
    accepts candidate required = true ↔
      ∃ substitution, Unifies substitution [(candidate, required)] := by
  have rejected := unifyTotal_none_iff_not_unifiable [(candidate, required)]
  unfold accepts
  cases result : unifyTotal [(candidate, required)] <;> simp_all

theorem accepts_scoped (invocation : Nat) (candidate : TypeTerm)
    (required : ClosedType) :
    accepts (scope invocation candidate) required.toTerm =
      accepts candidate required.toTerm := by
  have rejected := rejection_iff (σ := signature)
    (Nat.pair invocation) (fun name => (Nat.unpair name).2)
    (fun name => by simp) [(candidate, required.toTerm)]
  have unchanged := scope_preserves_ground invocation required.toTerm
    required.toTerm_isGround
  change scope invocation required.toTerm = required.toTerm at unchanged
  simp only [equations, List.map_cons, List.map_nil] at rejected
  change (unifyTotal [(scope invocation candidate,
      scope invocation required.toTerm)] = none) ↔ _ at rejected
  rw [unchanged] at rejected
  unfold accepts
  cases first : unifyTotal [(scope invocation candidate, required.toTerm)] <;>
    cases second : unifyTotal [(candidate, required.toTerm)] <;>
    simp_all

def selected (required : ClosedType) (candidates : List TypeTerm) : List TypeTerm :=
  candidates.flatMap fun candidate =>
    if accepts candidate required.toTerm then [required.toTerm] else []

theorem selected_scoped (invocation : Nat) (required : ClosedType)
    (candidates : List TypeTerm) :
    selected required (candidates.map (scope invocation)) =
      selected required candidates := by
  induction candidates with
  | nil => rfl
  | cons candidate later ih =>
      simp only [selected, List.map_cons, List.flatMap_cons, accepts_scoped] at *
      rw [ih]

theorem selected_is_closed (invocation : Nat) (required : ClosedType)
    (candidates : List TypeTerm) :
    (selected required candidates).map (scope invocation) =
      selected required candidates := by
  induction candidates with
  | nil => rfl
  | cons candidate later ih =>
      simp only [selected, List.flatMap_cons, List.map_append] at *
      rw [ih]
      split <;> simp only [List.map_cons, List.map_nil,
        scope_preserves_ground invocation required.toTerm required.toTerm_isGround]

def freshFallback (candidates : List TypeTerm) : List TypeTerm :=
  if candidates.isEmpty then [undefinedType] else candidates

def boundFallback (required : ClosedType) (candidates : List TypeTerm) : List TypeTerm :=
  if candidates.isEmpty then selected required [undefinedType] else candidates

/-- The primitive output is matched before its cut. Declaration alternatives
are tried only if that primitive clause did not succeed. Undefined is tried
only after the actual candidate query has no answers. -/
def clauses (query : Query) (declarations : List TypeTerm) : List TypeTerm :=
  match query.mode with
  | .fresh | .rootVariable =>
      match primitiveType query.subject with
      | some type => [type]
      | none => freshFallback declarations
  | .bound required =>
      match primitiveType query.subject with
      | some type =>
          if accepts type required.toTerm then [required.toTerm]
          else boundFallback required (selected required declarations)
      | none => boundFallback required (selected required declarations)

theorem primitive_scoped (invocation : Nat) (subject : Scalar) :
    (primitiveType subject).map (scope invocation) = primitiveType subject := by
  cases subject <;> rfl

theorem clauses_scoped (invocation : Nat) (query : Query)
    (declarations : List TypeTerm) :
    clauses query (declarations.map (scope invocation)) =
      (clauses query declarations).map (scope invocation) := by
  rcases query with ⟨subject, mode⟩
  cases mode with
  | fresh =>
      cases subject <;>
        simp [clauses, primitiveType, freshFallback, scope, rename, named,
          undefinedType, Subst.applyTerm]
      split <;> simp_all [scope, rename, Subst.applyTerm]
  | rootVariable =>
      cases subject <;>
        simp [clauses, primitiveType, freshFallback, scope, rename, named,
          undefinedType, Subst.applyTerm]
      split <;> simp_all [scope, rename, Subst.applyTerm]
  | bound required =>
      have closed := scope_preserves_ground invocation required.toTerm
        required.toTerm_isGround
      have fallback :
          (boundFallback required (selected required declarations)).map (scope invocation) =
            boundFallback required (selected required declarations) := by
        unfold boundFallback
        split <;> exact selected_is_closed invocation required _
      cases primitiveEq : primitiveType subject with
      | none =>
          simpa only [clauses, primitiveEq, selected_scoped] using fallback.symm
      | some primitive =>
          by_cases accepted : accepts primitive required.toTerm = true
          · simp only [clauses, primitiveEq, accepted, ↓reduceIte, List.map_cons,
              List.map_nil, closed]
          · simpa only [clauses, primitiveEq, accepted, Bool.false_eq_true,
              ↓reduceIte, selected_scoped]
              using fallback.symm

def sourceFacts (rows : List Declaration) (query : Query) : List TypeTerm :=
  clauses query (sourceDeclarations query.subject rows)

def indexedFacts (rows : List Declaration) (query : Query) : List TypeTerm :=
  clauses query (bucket query.subject (buildIndex rows))

theorem indexed_facts_exact (rows : List Declaration) (query : Query) :
    indexedFacts rows query = sourceFacts rows query := by
  unfold indexedFacts sourceFacts
  rw [index_matches_source]

def sourceAnswers (rows : List Declaration) (invocation : Nat)
    (query : Query) : List TypeTerm :=
  clauses query (sourceActiveDeclarations invocation query.subject rows)

theorem materialization_exact (rows : List Declaration) (invocation : Nat)
    (query : Query) :
    (indexedFacts rows query).map (scope invocation) =
      sourceAnswers rows invocation query := by
  rw [indexed_facts_exact]
  unfold sourceFacts sourceAnswers
  rw [source_activation_commutes, clauses_scoped]

/-- A declaration bucket, including an empty bucket, is the entire mutable
read dependency for this leaf service. Irrelevant subject rows need not agree. -/
theorem declaration_dependency (first second : List Declaration) (query : Query)
    (same : sourceDeclarations query.subject first =
      sourceDeclarations query.subject second) :
    sourceFacts first query = sourceFacts second query := by
  unfold sourceFacts
  rw [same]

structure Authority where
  owner : Nat
  declarationRevision : Nat
  equationRevision : Nat
  deriving DecidableEq

/-- An immutable history interprets each owner/revision stamp once. The C
adapter must maintain that stamp-to-inventory invariant across mutation. -/
abbrev History := Authority → Inventory

abbrev Context (history : History) :=
  { authority : Authority // SymbolOnly (history authority) }

def leafAdmission (history : History) :
    RevisionedQueryFacts.Factorization (Context history) Query Authority Query TypeTerm where
  stamp context _ := context.val
  key _ query := query
  compute authority query := indexedFacts (history authority).rows query
  service context query := sourceFacts (history context.val).rows query
  correct context query := (indexed_facts_exact (history context.val).rows query).symm

theorem cached_materialization_exact (history : History) (context : Context history)
    (query : Query) (invocation : Nat)
    (cache : RevisionedQueryFacts.Cache Authority Query TypeTerm)
    (valid : RevisionedQueryFacts.Valid (leafAdmission history).compute cache) :
    letI : DecidableEq Query := Classical.decEq _
    ((RevisionedQueryFacts.request (leafAdmission history).compute
      ⟨context.val, query⟩ cache).facts).map (scope invocation) =
      sourceAnswers (history context.val).rows invocation query := by
  classical
  rw [RevisionedQueryFacts.request_exact _ _ _ valid]
  exact materialization_exact _ _ _

namespace Controls

def literalDeclaration : List Declaration :=
  [⟨0, .number "6", named "Foo"⟩]

theorem fresh_number_cuts_before_declaration :
    sourceFacts literalDeclaration ⟨.number "6", .fresh⟩ = [named "Number"] := rfl

theorem bound_number_reaches_declaration :
    sourceFacts literalDeclaration
      ⟨.number "6", .bound (.const (.symbol "Foo"))⟩ = [named "Foo"] := by
  simp [sourceFacts, sourceDeclarations, literalDeclaration, clauses, primitiveType,
    named, scope, rename, Subst.applyTerm, accepts, unifyTotal,
    boundFallback, selected, GroundTerm.toTerm]

theorem filtering_fresh_inference_loses_bound_answer :
    selected (.const (.symbol "Foo"))
      (sourceFacts literalDeclaration ⟨.number "6", .fresh⟩) = [] := by
  simp [fresh_number_cuts_before_declaration, selected, accepts, named, unifyTotal,
    GroundTerm.toTerm]

theorem literal_declaration_is_not_cache_admitted :
    ¬ SymbolOnly ⟨literalDeclaration, by decide⟩ := by
  intro admitted
  obtain ⟨name, impossible⟩ := admitted ⟨0, .number "6", named "Foo"⟩ (by simp [literalDeclaration])
  cases impossible

def orderedDeclarations : List Declaration :=
  [⟨0, .symbol "x", named "First"⟩,
   ⟨1, .symbol "other", named "Ignored"⟩,
   ⟨2, .symbol "x", named "Second"⟩,
   ⟨3, .symbol "x", named "First"⟩]

theorem indexed_order_and_duplicates :
    indexedFacts orderedDeclarations ⟨.symbol "x", .fresh⟩ =
      [named "First", named "Second", named "First"] := rfl

theorem mismatching_bound_candidate_uses_undefined :
    indexedFacts orderedDeclarations
      ⟨.symbol "x", .bound (.const (.symbol "%Undefined%"))⟩ = [undefinedType] := by
  simp [indexedFacts, orderedDeclarations, buildIndex, bucket, prependBucket,
    clauses, primitiveType, boundFallback, selected, accepts, scope, rename,
    Subst.applyTerm, named, undefinedType, unifyTotal, GroundTerm.toTerm]

def sharedArrow : TypeTerm :=
  .app 3 ![named "->", .var 0, .var 0]

theorem scoped_shared_arrow (invocation occurrence : Nat) :
    scope invocation (scope occurrence sharedArrow) =
      .app 3 ![named "->", .var (Nat.pair invocation (Nat.pair occurrence 0)),
        .var (Nat.pair invocation (Nat.pair occurrence 0))] := by
  change Term.app _ _ = Term.app _ _
  congr 1
  funext i
  fin_cases i <;> rfl

def polymorphicDeclarations : List Declaration :=
  [⟨0, .symbol "id", sharedArrow⟩, ⟨1, .symbol "id", sharedArrow⟩]

theorem polymorphic_occurrences_are_fresh :
    sourceAnswers polymorphicDeclarations 9 ⟨.symbol "id", .rootVariable⟩ =
      [.app 3 ![named "->", .var (Nat.pair 9 (Nat.pair 0 0)),
                             .var (Nat.pair 9 (Nat.pair 0 0))],
       .app 3 ![named "->", .var (Nat.pair 9 (Nat.pair 1 0)),
                             .var (Nat.pair 9 (Nat.pair 1 0))]] := by
  simp only [sourceAnswers, sourceActiveDeclarations, polymorphicDeclarations,
    clauses, primitiveType, freshFallback, List.isEmpty_cons, Bool.false_eq_true,
    ↓reduceIte, scoped_shared_arrow]

theorem shared_scheme_acceptance_iff (left right : Scalar) :
    accepts sharedArrow (.app 3 ![named "->", .const left, .const right]) = true ↔
      left = right := by
  rw [accepts_iff_unifiable]
  constructor
  · rintro ⟨substitution, solves⟩
    have solved := solves (sharedArrow,
      .app 3 ![named "->", .const left, .const right]) (by simp)
    have children :
        (fun i : Fin 3 => substitution.applyTerm (![named "->", .var 0, .var 0] i)) =
        (fun i : Fin 3 => substitution.applyTerm (![named "->", .const left, .const right] i)) := by
      simpa only [sharedArrow, Subst.applyTerm_app, Term.app.injEq,
        heq_eq_eq, true_and, id_eq] using solved
    have first := congrFun children 1
    have second := congrFun children 2
    change substitution 0 = Term.const left at first
    change substitution 0 = Term.const right at second
    exact Term.const.inj (first.symm.trans second)
  · intro same
    subst right
    refine ⟨fun _ => Term.const left, ?_⟩
    intro pair member
    obtain rfl := List.mem_singleton.mp member
    change Term.app _ _ = Term.app _ _
    congr 1
    funext i
    fin_cases i <;> rfl

theorem shared_scheme_rejects_inconsistent_positions :
    accepts sharedArrow (.app 3 ![named "->", named "Number", named "String"]) =
      false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have impossible :=
    (shared_scheme_acceptance_iff (.symbol "Number") (.symbol "String")).mp accepted
  exact (by decide : Scalar.symbol "Number" ≠ .symbol "String") impossible

theorem shared_scheme_accepts_consistent_positions :
    accepts sharedArrow (.app 3 ![named "->", named "Number", named "Number"]) =
      true :=
  (shared_scheme_acceptance_iff (.symbol "Number") (.symbol "Number")).mpr rfl

theorem another_invocation_does_not_reuse_variables (occurrence slot : Nat) :
    Nat.pair 9 (Nat.pair occurrence slot) ≠ Nat.pair 10 (Nat.pair occurrence slot) :=
  invocation_names_disjoint 9 10 occurrence slot (by decide) occurrence slot

theorem missing_declaration_and_added_declaration_differ :
    sourceFacts [] ⟨.symbol "x", .fresh⟩ = [undefinedType] ∧
    sourceFacts [⟨0, .symbol "x", named "First"⟩] ⟨.symbol "x", .fresh⟩ =
      [named "First"] := by
  constructor <;> rfl

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.IntrinsicTypeFacts
