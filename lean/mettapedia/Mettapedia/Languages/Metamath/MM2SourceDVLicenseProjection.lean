import Mettapedia.Languages.Metamath.MM2NormalDataRows
import Mettapedia.Languages.Metamath.SourceStateNativeTypes

/-!
# Source-derived DV license projection for MM2

Metamath retains every active `$d` occurrence, including repeated pairs, but
the MM2 proof space is set-valued.  A proof-facing DV row is licensed exactly
when at least one active occurrence of its canonical pair exists and both
endpoints have active floating hypotheses.

This module states that quotient explicitly.  It does not introduce another
source semantics: the occurrence list and active endpoints are projections of
the existing `SourceState`, and accepted `$d` and `$f` operations remain steps
of the authored source-state GSLT classified through OSLF.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2SourceDVLicenseProjection

open Mettapedia.GSLT
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.Metamath.SourceGSLTOperations
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceStateGSLT
open Mettapedia.Languages.Metamath.SourceStateNativeTypes

/-! ## Occurrence-multiplicity ledger and proof-facing support -/

/-- The exact source information that determines proof-facing DV rows.
`distinctOccurrences` deliberately retains order and multiplicity. -/
structure DVLicenseProjection where
  activeFloatingVariables : List String
  distinctOccurrences : List (String × String)
deriving DecidableEq, Repr

/-- The DV license projection is computed from the authored source state. -/
def DVLicenseProjection.ofSourceState (state : SourceState) :
    DVLicenseProjection where
  activeFloatingVariables := state.activeFloatingVariables
  distinctOccurrences := state.activeDistinctVariables

/-- Occurrences whose two endpoints currently have active `$f` hypotheses.
Multiplicity is retained here. -/
def DVLicenseProjection.licensedOccurrences
    (projection : DVLicenseProjection) : List (String × String) :=
  projection.distinctOccurrences.filter fun pair =>
    projection.activeFloatingVariables.contains pair.1 &&
      projection.activeFloatingVariables.contains pair.2

/-- The exact list-level rows expected by the existing normal proof machine.
Repeated source licenses may therefore repeat equal rows in this list. -/
def DVLicenseProjection.runtimeRows (owner : Atom)
    (projection : DVLicenseProjection) : List Atom :=
  callerDVRowsOfPairs owner projection.licensedOccurrences

/-- MM2 stores atoms in a set.  This is the proof-facing support quotient;
occurrence multiplicity remains in `distinctOccurrences` for correct scope
exit and provenance accounting. -/
def DVLicenseProjection.runtimeSupport (owner : Atom)
    (projection : DVLicenseProjection) : Finset Atom :=
  (projection.runtimeRows owner).toFinset

@[simp] theorem licensedOccurrences_ofSourceState (state : SourceState) :
    (DVLicenseProjection.ofSourceState state).licensedOccurrences =
      state.proofDistinctVariables := by
  rfl

@[simp] theorem runtimeRows_ofSourceState (owner : Atom)
    (state : SourceState) :
    (DVLicenseProjection.ofSourceState state).runtimeRows owner =
      callerDVRows owner state := by
  rfl

theorem pair_mem_licensedOccurrences_iff
    (projection : DVLicenseProjection) (pair : String × String) :
    pair ∈ projection.licensedOccurrences ↔
      pair ∈ projection.distinctOccurrences ∧
        pair.1 ∈ projection.activeFloatingVariables ∧
        pair.2 ∈ projection.activeFloatingVariables := by
  simp [DVLicenseProjection.licensedOccurrences]

/-- Every proof-facing row has both an occurrence witness and live endpoints.
The two disjuncts are the symmetric query orientations of the same canonical
Metamath pair. -/
theorem mem_runtimeRows_iff (owner row : Atom)
    (projection : DVLicenseProjection) :
    row ∈ projection.runtimeRows owner ↔
      ∃ pair ∈ projection.distinctOccurrences,
        pair.1 ∈ projection.activeFloatingVariables ∧
        pair.2 ∈ projection.activeFloatingVariables ∧
          (row = callerDVRow owner pair.1 pair.2 ∨
           row = callerDVRow owner pair.2 pair.1) := by
  simp [DVLicenseProjection.runtimeRows,
    DVLicenseProjection.licensedOccurrences, callerDVRowsOfPairs,
    callerDVRowsForPair]
  aesop

/-- A repeated `$d` occurrence remains distinct provenance but cannot mint a
second proof capability in the set-valued MM2 space. -/
theorem runtimeSupport_append_existing_occurrence
    (owner : Atom) (projection : DVLicenseProjection)
    (pair : String × String)
    (existing : pair ∈ projection.distinctOccurrences) :
    (DVLicenseProjection.runtimeSupport owner
      { projection with
        distinctOccurrences := projection.distinctOccurrences ++ [pair] }) =
      projection.runtimeSupport owner := by
  apply Finset.ext
  intro row
  simp only [DVLicenseProjection.runtimeSupport, List.mem_toFinset]
  constructor
  · intro member
    rw [mem_runtimeRows_iff] at member
    rw [mem_runtimeRows_iff]
    obtain ⟨candidate, candidateMember, leftActive, rightActive,
      orientation⟩ := member
    refine ⟨candidate, ?_, leftActive, rightActive, orientation⟩
    rcases List.mem_append.mp candidateMember with prior | appended
    · exact prior
    · have candidateEq : candidate = pair := List.mem_singleton.mp appended
      simpa [candidateEq] using existing
  · intro member
    rw [mem_runtimeRows_iff] at member
    rw [mem_runtimeRows_iff]
    obtain ⟨candidate, candidateMember, leftActive, rightActive,
      orientation⟩ := member
    exact ⟨candidate, List.mem_append_left [pair] candidateMember,
      leftActive, rightActive, orientation⟩

/-- Removing one of several equal source occurrences cannot revoke the shared
proof capability. -/
theorem runtimeSupport_duplicate_tail_removal
    (owner : Atom) (active : List String) (pair : String × String) :
    (DVLicenseProjection.runtimeSupport owner
      { activeFloatingVariables := active
        distinctOccurrences := [pair, pair] }) =
    (DVLicenseProjection.runtimeSupport owner
      { activeFloatingVariables := active
        distinctOccurrences := [pair] }) := by
  exact runtimeSupport_append_existing_occurrence owner
    { activeFloatingVariables := active, distinctOccurrences := [pair] }
    pair (by simp)

/-- Without both active `$f` endpoints, an occurrence contributes no runtime
rows even though its provenance remains present. -/
theorem runtimeRows_singleton_eq_nil_of_endpoint_inactive
    (owner : Atom) (active : List String) (pair : String × String)
    (inactive : pair.1 ∉ active ∨ pair.2 ∉ active) :
    (DVLicenseProjection.runtimeRows owner
      { activeFloatingVariables := active
        distinctOccurrences := [pair] }) = [] := by
  rcases inactive with leftInactive | rightInactive
  · simp [DVLicenseProjection.runtimeRows,
      DVLicenseProjection.licensedOccurrences, callerDVRowsOfPairs,
      leftInactive]
  · by_cases leftActive : pair.1 ∈ active
    · simp [DVLicenseProjection.runtimeRows,
        DVLicenseProjection.licensedOccurrences, callerDVRowsOfPairs,
        leftActive, rightInactive]
    · simp [DVLicenseProjection.runtimeRows,
        DVLicenseProjection.licensedOccurrences, callerDVRowsOfPairs,
        leftActive]

/-! ## LIFO ownership markers

The MM2 space does not need arithmetic reference counts.  Active source
occurrences are removed in reverse declaration order at scope exit.  The
earliest active occurrence of a pair may therefore own the shared proof row;
every later occurrence is marked as a duplicate and is necessarily removed
before its owner.
-/

inductive DVOccurrenceKind where
  | first
  | duplicate
deriving DecidableEq, Repr

structure MarkedDVOccurrence where
  pair : String × String
  kind : DVOccurrenceKind
deriving DecidableEq, Repr

def markOccurrenceKind (seen : List (String × String))
    (pair : String × String) : DVOccurrenceKind :=
  if pair ∈ seen then .duplicate else .first

def markOccurrencesFrom (seen : List (String × String)) :
    List (String × String) → List MarkedDVOccurrence
  | [] => []
  | pair :: rest =>
      { pair, kind := markOccurrenceKind seen pair } ::
        markOccurrencesFrom (seen ++ [pair]) rest

def markOccurrences (occurrences : List (String × String)) :
    List MarkedDVOccurrence :=
  markOccurrencesFrom [] occurrences

def firstMarkedPairs : List MarkedDVOccurrence → List (String × String)
  | [] => []
  | occurrence :: rest =>
      match occurrence.kind with
      | .first => occurrence.pair :: firstMarkedPairs rest
      | .duplicate => firstMarkedPairs rest

/-- Marking enriches the ordered occurrence ledger without changing its
pair projection.  In particular, equal pairs remain separate occurrences. -/
@[simp] theorem pair_projection_markOccurrencesFrom
    (seen occurrences : List (String × String)) :
    (markOccurrencesFrom seen occurrences).map MarkedDVOccurrence.pair =
      occurrences := by
  induction occurrences generalizing seen with
  | nil => rfl
  | cons pair rest induction =>
      simp [markOccurrencesFrom, induction]

@[simp] theorem pair_projection_markOccurrences
    (occurrences : List (String × String)) :
    (markOccurrences occurrences).map MarkedDVOccurrence.pair =
      occurrences := by
  exact pair_projection_markOccurrencesFrom [] occurrences

/-- Every marked occurrence is backed by an exact occurrence of its pair in
the source ledger.  The marker is derived information, not new authority. -/
theorem marked_mem_markOccurrences_has_source_pair
    (occurrences : List (String × String))
    (marked : MarkedDVOccurrence)
    (member : marked ∈ markOccurrences occurrences) :
    marked.pair ∈ occurrences := by
  have mapped : marked.pair ∈
      (markOccurrences occurrences).map MarkedDVOccurrence.pair :=
    List.mem_map_of_mem member
  simpa using mapped

/-- Marking is compositional at an ordered append boundary.  The second
segment sees every occurrence in the first segment as prior provenance. -/
theorem markOccurrencesFrom_append (seen left right : List (String × String)) :
    markOccurrencesFrom seen (left ++ right) =
      markOccurrencesFrom seen left ++
        markOccurrencesFrom (seen ++ left) right := by
  induction left generalizing seen with
  | nil => simp [markOccurrencesFrom]
  | cons pair rest induction =>
      simp [markOccurrencesFrom, induction, List.append_assoc]

/-- The first markers retain exactly the new support not already present in
the incoming occurrence prefix. -/
theorem pair_mem_firstMarkedPairs_markOccurrencesFrom
    (seen occurrences : List (String × String)) (pair : String × String) :
    pair ∈ firstMarkedPairs (markOccurrencesFrom seen occurrences) ↔
      pair ∈ occurrences ∧ pair ∉ seen := by
  induction occurrences generalizing seen with
  | nil => simp [markOccurrencesFrom, firstMarkedPairs]
  | cons head rest induction =>
      by_cases headSeen : head ∈ seen
      · simp only [markOccurrencesFrom, markOccurrenceKind, if_pos headSeen,
          firstMarkedPairs]
        rw [induction]
        constructor
        · rintro ⟨pairRest, pairNotSeenAppend⟩
          have pairNotSeen : pair ∉ seen := by
            intro pairSeen
            exact pairNotSeenAppend
              (List.mem_append_left [head] pairSeen)
          exact ⟨List.mem_cons_of_mem head pairRest, pairNotSeen⟩
        · rintro ⟨pairMember, pairNotSeen⟩
          have pairNeHead : pair ≠ head := by
            intro equal
            subst pair
            exact pairNotSeen headSeen
          have pairRest : pair ∈ rest := by
            rcases List.mem_cons.mp pairMember with pairHead | restMember
            · exact False.elim (pairNeHead pairHead)
            · exact restMember
          have pairNotSeenAppend : pair ∉ seen ++ [head] := by
            simp [pairNotSeen, pairNeHead]
          exact ⟨pairRest, pairNotSeenAppend⟩
      · simp only [markOccurrencesFrom, markOccurrenceKind, if_neg headSeen,
          firstMarkedPairs, List.mem_cons]
        rw [induction]
        constructor
        · intro member
          rcases member with pairHead | ⟨pairRest, pairNotSeenAppend⟩
          · subst pair
            exact ⟨Or.inl rfl, headSeen⟩
          · have pairNotSeen : pair ∉ seen := by
              intro pairSeen
              exact pairNotSeenAppend
                (List.mem_append_left [head] pairSeen)
            exact ⟨Or.inr pairRest, pairNotSeen⟩
        · rintro ⟨pairMember, pairNotSeen⟩
          rcases pairMember with pairHead | pairRest
          · exact Or.inl pairHead
          · by_cases pairHead : pair = head
            · exact Or.inl pairHead
            · right
              refine ⟨pairRest, ?_⟩
              simp [pairNotSeen, pairHead]

theorem pair_mem_firstMarkedPairs_markOccurrences
    (occurrences : List (String × String)) (pair : String × String) :
    pair ∈ firstMarkedPairs (markOccurrences occurrences) ↔
      pair ∈ occurrences := by
  simpa [markOccurrences] using
    pair_mem_firstMarkedPairs_markOccurrencesFrom [] occurrences pair

/-- Occurrence markers preserve exactly the source support while retaining
which particular occurrence owns each capability. -/
theorem firstMarkedPairs_support_eq
    (occurrences : List (String × String)) :
    (firstMarkedPairs (markOccurrences occurrences)).toFinset =
      occurrences.toFinset := by
  apply Finset.ext
  intro pair
  simp [pair_mem_firstMarkedPairs_markOccurrences]

/-- Equal support in a different order has different ownership receipts.
This prevents the support quotient from masquerading as occurrence
provenance. -/
theorem markOccurrences_order_sensitive :
    markOccurrences [("x", "y"), ("y", "z"), ("x", "y")] ≠
      markOccurrences [("x", "y"), ("x", "y"), ("y", "z")] := by
  decide +kernel

/-! ## Exact source-operation projection -/

/-- An accepted `$d` appends exactly the source-generated occurrence list.
It does not decide proof visibility independently. -/
theorem ofSourceState_declareDisjoint
    {before after : SourceState} {names : List String}
    (declared : declareDisjoint? before names = some after) :
    DVLicenseProjection.ofSourceState after =
      { DVLicenseProjection.ofSourceState before with
        distinctOccurrences :=
          before.activeDistinctVariables ++ allDistinctPairs names } := by
  rw [declareDisjoint?_eq_some_state declared]
  rfl

/-- An accepted `$f` activates exactly one endpoint in the projection while
retaining the complete `$d` occurrence ledger. -/
theorem ofSourceState_declareFloating
    {before after : SourceState} {label typecode variableName : String}
    (declared :
      declareFloating? before label typecode variableName = some after) :
    DVLicenseProjection.ofSourceState after =
      { DVLicenseProjection.ofSourceState before with
        activeFloatingVariables :=
          before.activeFloatingVariables ++ [variableName] } := by
  obtain ⟨_, _, shape⟩ := declareFloating?_inv declared
  rw [shape]
  simp [DVLicenseProjection.ofSourceState,
    SourceState.activeFloatingVariables,
    floatingVariableNames_append_floating]

/-- The accepted `$d` operation remains classified by the OSLF-generated
native type of the authored source-state GSLT. -/
theorem declareDisjoint_inhabits_source_native_type
    {before after : SourceState} {names : List String}
    (declared : declareDisjoint? before names = some after) :
    (gsltOSLF SourceStateGSLT.theory).satisfies before
      (sourceStateExactTargetNativeType after).pred := by
  exact local_payload_inhabits_exact_target
    (payload := .declareDisjoint names) (source := before) (target := after)
    declared

/-- The accepted `$f` operation is likewise interpreted only by the authored
source GSLT and its OSLF-derived NTT. -/
theorem declareFloating_inhabits_source_native_type
    {before after : SourceState} {label typecode variableName : String}
    (declared :
      declareFloating? before label typecode variableName = some after) :
    (gsltOSLF SourceStateGSLT.theory).satisfies before
      (sourceStateExactTargetNativeType after).pred := by
  exact local_payload_inhabits_exact_target
    (payload := .declareFloating label typecode variableName)
    (source := before) (target := after) declared

/-! ## Small positive and negative controls -/

private def canaryOwner : Atom := .symbol "dv-license-source"

private def activeCanary : DVLicenseProjection :=
  { activeFloatingVariables := ["x", "y"]
    distinctOccurrences := [("x", "y")] }

private def inactiveCanary : DVLicenseProjection :=
  { activeFloatingVariables := ["x"]
    distinctOccurrences := [("x", "y")] }

theorem activeCanary_has_both_orientations :
    activeCanary.runtimeRows canaryOwner =
      [callerDVRow canaryOwner "x" "y",
       callerDVRow canaryOwner "y" "x"] := by
  decide +kernel

theorem inactiveCanary_has_no_runtime_rows :
    inactiveCanary.runtimeRows canaryOwner = [] := by
  decide +kernel

theorem duplicateCanary_has_single_support :
    (DVLicenseProjection.runtimeSupport canaryOwner
      { activeFloatingVariables := ["x", "y"]
        distinctOccurrences := [("x", "y"), ("x", "y")] }) =
    activeCanary.runtimeSupport canaryOwner := by
  exact runtimeSupport_duplicate_tail_removal canaryOwner ["x", "y"]
    ("x", "y")

section AxiomAudit

#print axioms runtimeRows_ofSourceState
#print axioms mem_runtimeRows_iff
#print axioms runtimeSupport_append_existing_occurrence
#print axioms runtimeRows_singleton_eq_nil_of_endpoint_inactive
#print axioms markOccurrencesFrom_append
#print axioms pair_projection_markOccurrences
#print axioms marked_mem_markOccurrences_has_source_pair
#print axioms pair_mem_firstMarkedPairs_markOccurrencesFrom
#print axioms firstMarkedPairs_support_eq
#print axioms markOccurrences_order_sensitive
#print axioms ofSourceState_declareDisjoint
#print axioms ofSourceState_declareFloating
#print axioms declareDisjoint_inhabits_source_native_type
#print axioms declareFloating_inhabits_source_native_type
#print axioms activeCanary_has_both_orientations
#print axioms inactiveCanary_has_no_runtime_rows
#print axioms duplicateCanary_has_single_support

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2SourceDVLicenseProjection
