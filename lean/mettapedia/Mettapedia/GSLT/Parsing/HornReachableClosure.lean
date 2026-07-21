import Mettapedia.GSLT.Parsing.HornChildDiscovery

/-!
# Constructive finite closure of root-reachable parser grammars

The compiler must construct its grammar-term universe rather than receive a
hand-authored list.  Starting from the requested root, `discoverDomain`
repeatedly follows a supplied child relation and removes duplicates.  A fuel
bound limits construction only: `discoverRootCategoryTable` accepts the result
only when the ordinary fail-closed root-universe checker proves that the final
domain is closed.  Running out of fuel with an unseen child is therefore a
rejection of the proposed compilation plan, never evidence that the language
has no such child.

When the child relation is `HornChildDiscovery.semanticChildren`, the previous
module proves that semantic recursive parser calls arise from the admitted
Horn bodies and follow exactly these edges.
-/

namespace Mettapedia.GSLT.Parsing.HornReachableClosure

open HornCertificate HornSpecialization HornCategoryTable HornRootUniverse
open HornChildDiscovery HornSpecializationBody

def expandDomain (children : Term → List Term) (domain : List Term) : List Term :=
  (domain ++ domain.flatMap children).dedup

theorem mem_expandDomain_iff {children : Term → List Term}
    {domain : List Term} {grammar : Term} :
    grammar ∈ expandDomain children domain ↔
      grammar ∈ domain ∨
        ∃ parent ∈ domain, grammar ∈ children parent := by
  simp [expandDomain, List.mem_flatMap]

def discoverDomain (root : Term) (children : Term → List Term) :
    Nat → List Term
  | 0 => [root]
  | fuel + 1 => expandDomain children (discoverDomain root children fuel)

theorem discoverDomain_nodup (root : Term) (children : Term → List Term)
    (fuel : Nat) :
    (discoverDomain root children fuel).Nodup := by
  cases fuel with
  | zero => simp [discoverDomain]
  | succ fuel => exact List.nodup_dedup _

theorem discoverDomain_root_mem (root : Term) (children : Term → List Term)
    (fuel : Nat) :
    root ∈ discoverDomain root children fuel := by
  induction fuel with
  | zero => simp [discoverDomain]
  | succ fuel inductionHypothesis =>
      rw [discoverDomain, mem_expandDomain_iff]
      exact Or.inl inductionHypothesis

theorem discoverDomain_sound {root grammar : Term}
    {children : Term → List Term} {fuel : Nat}
    (member : grammar ∈ discoverDomain root children fuel) :
    Reachable root children grammar := by
  induction fuel generalizing grammar with
  | zero =>
      simp [discoverDomain] at member
      subst grammar
      exact .root
  | succ fuel inductionHypothesis =>
      rw [discoverDomain, mem_expandDomain_iff] at member
      rcases member with oldMember | ⟨parent, parentMember, childMember⟩
      · exact inductionHypothesis oldMember
      · exact .child (inductionHypothesis parentMember) childMember

structure DiscoveredRootTable where
  domain : List Term
  table : CategoryTable
  deriving DecidableEq, Repr

def discoverRootCategoryTable (root : Term) (children : Term → List Term)
    (fuel : Nat) : Option DiscoveredRootTable := do
  let domain := discoverDomain root children fuel
  let table ← buildRootCategoryTable root children domain
  pure { domain, table }

theorem discoverRootCategoryTable_components
    {root : Term} {children : Term → List Term} {fuel : Nat}
    {result : DiscoveredRootTable}
    (accepted : discoverRootCategoryTable root children fuel = some result) :
    result.domain = discoverDomain root children fuel ∧
      buildRootCategoryTable root children result.domain = some result.table := by
  simp only [discoverRootCategoryTable] at accepted
  cases checked : buildRootCategoryTable root children
      (discoverDomain root children fuel) with
  | none => simp [checked] at accepted
  | some table =>
      simp [checked] at accepted
      subst result
      exact ⟨rfl, checked⟩

theorem discoverRootCategoryTable_domain_exact
    {root grammar : Term} {children : Term → List Term} {fuel : Nat}
    {result : DiscoveredRootTable}
    (accepted : discoverRootCategoryTable root children fuel = some result) :
    grammar ∈ result.domain ↔ Reachable root children grammar := by
  obtain ⟨domainEq, tableAccepted⟩ :=
    discoverRootCategoryTable_components accepted
  constructor
  · intro member
    rw [domainEq] at member
    exact discoverDomain_sound member
  · intro reachable
    obtain ⟨category, found⟩ :=
      buildRootCategoryTable_covers_reachable tableAccepted reachable
    exact buildRootCategoryTable_lookup_is_in_universe tableAccepted found

theorem discoverRootCategoryTable_category_exact
    {root grammar : Term} {children : Term → List Term} {fuel : Nat}
    {result : DiscoveredRootTable}
    (accepted : discoverRootCategoryTable root children fuel = some result) :
    (∃ category, lookupCategory grammar result.table = some category) ↔
      Reachable root children grammar := by
  obtain ⟨_, tableAccepted⟩ :=
    discoverRootCategoryTable_components accepted
  constructor
  · rintro ⟨category, found⟩
    have domainMember :=
      buildRootCategoryTable_lookup_is_in_universe tableAccepted found
    exact (discoverRootCategoryTable_domain_exact accepted).mp domainMember
  · intro reachable
    exact buildRootCategoryTable_covers_reachable tableAccepted reachable

/-- Construct the category universe directly from recursive parser calls in
the instantiated admitted Horn bodies. -/
def discoverSemanticRootCategoryTable (parseRelation : String)
    (bodies : Term → List Atom) (root : Term) (fuel : Nat) :
    Option DiscoveredRootTable :=
  discoverRootCategoryTable root (semanticChildren parseRelation bodies) fuel

/-- Every recursive call in certificate-independent body semantics receives a
category from the constructively discovered root universe. -/
theorem discoverSemanticRootCategoryTable_covers_call
    {program : Program} {parseRelation : String} {root parent : Term}
    {bodies : Term → List Atom} {fuel : Nat} {result : DiscoveredRootTable}
    (accepted : discoverSemanticRootCategoryTable parseRelation bodies root fuel =
      some result)
    (parentReachable :
      Reachable root (semanticChildren parseRelation bodies) parent)
    {calls : List HornStream.ParseCall}
    (semantic : SemanticBodySpecializes program parseRelation result.table
      (bodies parent) calls)
    {call : HornStream.ParseCall} (member : call ∈ calls) :
    ∃ grammar,
      Reachable root (semanticChildren parseRelation bodies) grammar ∧
      grammar ∈ result.domain ∧
      lookupCategory grammar result.table = some call.category := by
  have rootAccepted : discoverRootCategoryTable root
      (semanticChildren parseRelation bodies) fuel = some result := by
    simpa [discoverSemanticRootCategoryTable] using accepted
  obtain ⟨domainEq, tableAccepted⟩ :=
    discoverRootCategoryTable_components rootAccepted
  exact rootTable_covers_semantic_call tableAccepted parentReachable semantic
    member

/-! ## Executable positive and negative controls -/

theorem one_step_control_closure_accepts :
    (discoverRootCategoryTable grammarA controlChildren 1).isSome = true := by
  decide

theorem unfinished_control_frontier_rejects :
    discoverRootCategoryTable grammarA controlChildren 0 = none := by
  decide

def cyclicChildren : Term → List Term
  | grammar =>
      if grammar = grammarA then [grammarB]
      else if grammar = grammarB then [grammarA]
      else []

theorem finite_cycle_closes_and_accepts :
    (discoverRootCategoryTable grammarA cyclicChildren 1).isSome = true := by
  decide

def growingChildren : Term → List Term
  | .integer value => [.integer (value + 1)]
  | _ => []

theorem growing_frontier_never_claims_closed_at_two_steps :
    discoverRootCategoryTable (.integer 0) growingChildren 2 = none := by
  decide

theorem symbolic_root_rejects_after_construction :
    discoverRootCategoryTable (.var 0) (fun _ => []) 0 = none := by
  decide

end Mettapedia.GSLT.Parsing.HornReachableClosure
