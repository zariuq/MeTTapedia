import Mettapedia.GSLT.Parsing.HornCategoryTable

/-!
# Fail-closed finite root universes for Horn parser compilation

A compiler may use a finite grammar-term universe only after checking that it
contains the requested root, contains no duplicate or symbolic terms, and is
closed under the child-grammar relation extracted from admitted Horn rule
bodies.  These checks turn a finite serialized universe into constructive
coverage evidence: every root-reachable grammar receives a category.

The child extractor remains a parameter here.  Its correspondence with body
specialization is the next layer; this module does not assume that arbitrary
children are source-derived.
-/

namespace Mettapedia.GSLT.Parsing.HornRootUniverse

open HornCertificate HornSpecialization HornCategoryTable

inductive Reachable (root : Term) (children : Term → List Term) : Term → Prop where
  | root : Reachable root children root
  | child {parent child : Term} :
      Reachable root children parent →
      child ∈ children parent →
      Reachable root children child

def RootUniverseCovers (root : Term) (children : Term → List Term)
    (domain : List Term) : Prop :=
  domain.Nodup ∧
  root ∈ domain ∧
  (∀ grammar ∈ domain, termVariables grammar = []) ∧
  ∀ grammar ∈ domain, ∀ child ∈ children grammar, child ∈ domain

def rootUniverseValid (root : Term) (children : Term → List Term)
    (domain : List Term) : Bool :=
  decide domain.Nodup &&
  decide (root ∈ domain) &&
  domain.all fun grammar =>
    decide (termVariables grammar = []) &&
    (children grammar).all fun child => decide (child ∈ domain)

theorem rootUniverseValid_iff (root : Term) (children : Term → List Term)
    (domain : List Term) :
    rootUniverseValid root children domain = true ↔
      RootUniverseCovers root children domain := by
  simp only [rootUniverseValid, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true]
  constructor
  · rintro ⟨⟨unique, rootMember⟩, checked⟩
    refine ⟨unique, rootMember, ?_, ?_⟩
    · intro grammar grammarMember
      exact (checked grammar grammarMember).1
    · intro grammar grammarMember child childMember
      exact (checked grammar grammarMember).2 child childMember
  · rintro ⟨unique, rootMember, ground, closed⟩
    exact ⟨⟨unique, rootMember⟩, fun grammar grammarMember =>
      ⟨ground grammar grammarMember,
        closed grammar grammarMember⟩⟩

/-- Fail closed if the proposed finite universe omits even one child edge.
The returned table is constructed, not supplied by the caller. -/
def buildRootCategoryTable (root : Term) (children : Term → List Term)
    (domain : List Term) : Option CategoryTable :=
  if rootUniverseValid root children domain then
    some (makeCategoryTable domain)
  else none

theorem buildRootCategoryTable_valid {root : Term}
    {children : Term → List Term} {domain : List Term}
    {table : CategoryTable}
    (accepted : buildRootCategoryTable root children domain = some table) :
    categoryTableValid table = true := by
  simp only [buildRootCategoryTable] at accepted
  split at accepted
  next checked =>
    have valid := (rootUniverseValid_iff root children domain).mp checked
    have admissible : domain.Nodup ∧
        ∀ grammar ∈ domain, termVariables grammar = [] :=
      ⟨valid.1, valid.2.2.1⟩
    injection accepted with tableEq
    subst table
    exact buildCategoryTable_valid
      (grammars := domain) (table := makeCategoryTable domain)
      (by unfold buildCategoryTable; rw [if_pos admissible])
  next invalid => simp at accepted

theorem reachable_mem_of_valid {root grammar : Term}
    {children : Term → List Term} {domain : List Term}
    (valid : RootUniverseCovers root children domain)
    (reachable : Reachable root children grammar) :
    grammar ∈ domain := by
  induction reachable with
  | root => exact valid.2.1
  | child parentReachable childMember inductionHypothesis =>
      exact valid.2.2.2 _ inductionHypothesis _ childMember

theorem buildRootCategoryTable_covers_reachable {root grammar : Term}
    {children : Term → List Term} {domain : List Term}
    {table : CategoryTable}
    (accepted : buildRootCategoryTable root children domain = some table)
    (reachable : Reachable root children grammar) :
    ∃ category, lookupCategory grammar table = some category := by
  simp only [buildRootCategoryTable] at accepted
  split at accepted
  next checked =>
    have valid := (rootUniverseValid_iff root children domain).mp checked
    have admissible : domain.Nodup ∧
        ∀ grammar ∈ domain, termVariables grammar = [] :=
      ⟨valid.1, valid.2.2.1⟩
    injection accepted with tableEq
    subst table
    exact buildCategoryTable_covers
      (grammars := domain) (table := makeCategoryTable domain)
      (by unfold buildCategoryTable; rw [if_pos admissible])
      (reachable_mem_of_valid valid reachable)
  next invalid => simp at accepted

theorem buildRootCategoryTable_lookup_is_in_universe {root grammar : Term}
    {children : Term → List Term} {domain : List Term}
    {table : CategoryTable}
    (accepted : buildRootCategoryTable root children domain = some table)
    {category : CompilerCorrespondence.Category}
    (found : lookupCategory grammar table = some category) :
    grammar ∈ domain := by
  simp only [buildRootCategoryTable] at accepted
  split at accepted
  next checked =>
    have valid := (rootUniverseValid_iff root children domain).mp checked
    have admissible : domain.Nodup ∧
        ∀ candidate ∈ domain, termVariables candidate = [] :=
      ⟨valid.1, valid.2.2.1⟩
    injection accepted with tableEq
    subst table
    exact buildCategoryTable_lookup_source
      (grammars := domain) (table := makeCategoryTable domain)
      (by unfold buildCategoryTable; rw [if_pos admissible]) found
  next invalid => simp at accepted

/-! ## Executable positive and negative controls -/

def controlChildren : Term → List Term
  | grammar => if grammar = grammarA then [grammarB] else []

theorem closedRootUniverse_accepts :
    (buildRootCategoryTable grammarA controlChildren [grammarA, grammarB]).isSome =
      true := by
  decide

theorem missingReachableChild_rejects :
    buildRootCategoryTable grammarA controlChildren [grammarA] = none := by
  decide

theorem missingRoot_rejects :
    buildRootCategoryTable grammarA controlChildren [grammarB] = none := by
  decide

theorem duplicateDomain_rejects :
    buildRootCategoryTable grammarA controlChildren
      [grammarA, grammarB, grammarB] = none := by
  decide

theorem symbolicRootUniverse_rejects :
    buildRootCategoryTable (.var 0) (fun _ => []) [.var 0] = none := by
  decide

theorem controlChild_is_covered :
    ∃ category,
      lookupCategory grammarB (makeCategoryTable [grammarA, grammarB]) =
        some category := by
  apply buildRootCategoryTable_covers_reachable
    (root := grammarA) (children := controlChildren)
    (domain := [grammarA, grammarB])
    (table := makeCategoryTable [grammarA, grammarB])
  · decide
  · exact .child .root (by simp [controlChildren])

end Mettapedia.GSLT.Parsing.HornRootUniverse
