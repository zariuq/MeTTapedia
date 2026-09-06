import Mettapedia.GSLT.LanguageDef.GuardSupportProjectionCompilation

/-!
# Source-directed root observations before structural matching

An ordinary source pattern selects one occurrence of a slot. Its query path
can reveal an atomic value or a rigid application head and arity without
forcing the application's children or the other source fields. A known root
survives arbitrary logical substitution. An open root remains unknown.

The matching theorem derives agreement with a final slot binding from actual
structural instantiation. It retains every equation imposed by repeated
variables. A concrete supplier classifier then excludes callable symbols,
canonical partial shapes, and underapplications at an observed slot root.
The classifier deliberately overapproximates groundness, canonical partial
payload validity, and the exact-arity exception to underapplication.

This is a per-source-slot theorem. It neither enumerates every entry produced
by a physical matcher nor proves coverage of a specialization selector or its
interprocedural productivity decisions. Projection follows the first supported
subtree in depth-first source order; a breadth-first occurrence selector is a
different algorithm. Physical matching, current program authority, ready-value
interpretation, effects, and borrowed lifetime require separate refinement.
The open carrier has only rigid named application heads. Its partial-argument
list examples do not embed empty expressions or expressions with non-symbol
heads from a physical runtime.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RootSupportProjectionCompilation

open CompiledPlanAdmission
open CompiledPlanActivationViewCompilation
open CompiledPlanOpenActivationViewCompilation
open Mettapedia.Languages.MeTTa.TermViewCompilation

open GuardSupportProjectionCompilation (sourceArity queryArity)

/-- Exactly the rigid information that simultaneous substitution preserves.
The application observation carries no claim about its children. -/
inductive RootObservation where
  | symbol (name : List UInt8)
  | string (value : List UInt8)
  | integer (value : Int64)
  | application (head : List UInt8) (arity : Nat)
  deriving DecidableEq, Repr

def observeRoot? : OpenTerm -> Option RootObservation
  | .symbol name => some (.symbol name)
  | .variable _ => none
  | .string value => some (.string value)
  | .integer value => some (.integer value)
  | .application head arguments =>
      some (.application head (queryArity arguments))

theorem queryArity_substitution
    (substitution : OpenSubstitution) (arguments : OpenTerms) :
    queryArity (substituteOpenTerms substitution arguments) =
      queryArity arguments := by
  cases arguments with
  | nil => rfl
  | cons head tail =>
      simp only [substituteOpenTerms, queryArity,
        queryArity_substitution substitution tail]

/-- Observed roots stay fixed even when their children contain aliases that
later substitutions resolve. This theorem does not treat an unknown as a
negative observation. -/
theorem observeRoot?_substitution
    (substitution : OpenSubstitution) (query : OpenTerm)
    (root : RootObservation) (observed : observeRoot? query = some root) :
    observeRoot? (substituteOpen substitution query) = some root := by
  cases query <;>
    simp_all [observeRoot?, substituteOpen, queryArity_substitution]

mutual

/-- Follow the first authored occurrence, checking every rigid head and
arity on its structural spine. The source support list is exact. -/
def projectSlot? (slot : UInt32) : Term -> OpenTerm -> Option RootObservation
  | .variable sourceSlot, query =>
      if sourceSlot = slot then observeRoot? query else none
  | .application sourceHead sources, .application queryHead queries =>
      if sourceHead = queryHead ∧ sourceArity sources = queryArity queries then
        projectSlotTerms? slot sources queries
      else none
  | _, _ => none

def projectSlotTerms? (slot : UInt32) :
    Terms -> OpenTerms -> Option RootObservation
  | .cons sourceHead sourceTail, .cons queryHead queryTail =>
      if slot ∈ usedSlots sourceHead then
        projectSlot? slot sourceHead queryHead
      else
        projectSlotTerms? slot sourceTail queryTail
  | _, _ => none

end

mutual

theorem projectSlot?_used
    (slot : UInt32) (source : Term) (query : OpenTerm)
    (root : RootObservation)
    (observed : projectSlot? slot source query = some root) :
    slot ∈ usedSlots source := by
  cases source with
  | symbol name => simp [projectSlot?] at observed
  | string text => simp [projectSlot?] at observed
  | integer number => simp [projectSlot?] at observed
  | «variable» sourceSlot =>
      simp only [projectSlot?] at observed
      split at observed
      · rename_i same
        simp [usedSlots, same]
      · contradiction
  | application sourceHead sources =>
      cases query <;> simp only [projectSlot?] at observed
      all_goals try contradiction
      split at observed
      · exact projectSlotTerms?_used slot sources _ root observed
      · contradiction

theorem projectSlotTerms?_used
    (slot : UInt32) (sources : Terms) (queries : OpenTerms)
    (root : RootObservation)
    (observed : projectSlotTerms? slot sources queries = some root) :
    slot ∈ usedSlotsTerms sources := by
  cases sources with
  | nil => cases queries <;> simp [projectSlotTerms?] at observed
  | cons sourceHead sourceTail =>
      cases queries with
      | nil => simp [projectSlotTerms?] at observed
      | cons queryHead queryTail =>
          simp only [projectSlotTerms?] at observed
          split at observed
          · rename_i used
            simp [usedSlotsTerms, used]
          · have used :=
              projectSlotTerms?_used slot sourceTail queryTail root observed
            simp [usedSlotsTerms, used]

end

mutual

/-- Every complete structural match binds the projected source slot to a
value with the observed root. Matching existence is not inferred from one
successful path: other fields and repeated occurrences may still conflict. -/
theorem projectSlot?_sound
    (slot : UInt32) (source : Term) (query : OpenTerm)
    (root : RootObservation) (generation : UInt32)
    (environment : OpenEnvironment) (substitution : OpenSubstitution)
    (observed : projectSlot? slot source query = some root)
    (matched : instantiateOpen generation environment source =
      substituteOpen substitution query) :
    ∃ value, environment slot = some value ∧
      observeRoot? value = some root := by
  cases source with
  | symbol name => simp [projectSlot?] at observed
  | string text => simp [projectSlot?] at observed
  | integer number => simp [projectSlot?] at observed
  | «variable» sourceSlot =>
      simp only [projectSlot?] at observed
      split at observed
      · rename_i same
        subst sourceSlot
        have stable := observeRoot?_substitution substitution query root observed
        rw [← matched] at stable
        cases present : environment slot with
        | none => simp [instantiateOpen, present, observeRoot?] at stable
        | some value =>
            exact ⟨value, rfl, by simpa [instantiateOpen, present] using stable⟩
      · contradiction
  | application sourceHead sources =>
      cases query <;> simp only [projectSlot?] at observed
      all_goals try contradiction
      case application queryHead queries =>
        split at observed
        · simp only [instantiateOpen, substituteOpen,
            OpenTerm.application.injEq] at matched
          exact projectSlotTerms?_sound slot sources queries root
            generation environment substitution observed matched.2
        · contradiction

theorem projectSlotTerms?_sound
    (slot : UInt32) (sources : Terms) (queries : OpenTerms)
    (root : RootObservation) (generation : UInt32)
    (environment : OpenEnvironment) (substitution : OpenSubstitution)
    (observed : projectSlotTerms? slot sources queries = some root)
    (matched : instantiateOpenTerms generation environment sources =
      substituteOpenTerms substitution queries) :
    ∃ value, environment slot = some value ∧
      observeRoot? value = some root := by
  cases sources with
  | nil => cases queries <;> simp [projectSlotTerms?] at observed
  | cons sourceHead sourceTail =>
      cases queries with
      | nil => simp [projectSlotTerms?] at observed
      | cons queryHead queryTail =>
          simp only [instantiateOpenTerms, substituteOpenTerms,
            OpenTerms.cons.injEq] at matched
          simp only [projectSlotTerms?] at observed
          split at observed
          · exact projectSlot?_sound slot sourceHead queryHead root
              generation environment substitution observed matched.1
          · exact projectSlotTerms?_sound slot sourceTail queryTail root
              generation environment substitution observed matched.2

end

/-- Logical environment composition may update aliases inside an occupied
slot. Its admitted root still agrees; occupied-slot equality is not required. -/
theorem projectSlot?_sound_after_extension
    (slot : UInt32) (source : Term) (query : OpenTerm)
    (root : RootObservation) (generation : UInt32)
    (environment : OpenEnvironment)
    (substitution extension : OpenSubstitution)
    (observed : projectSlot? slot source query = some root)
    (matched : instantiateOpen generation environment source =
      substituteOpen substitution query) :
    ∃ value, composeEnvironment generation environment extension slot =
      some value ∧ observeRoot? value = some root := by
  obtain ⟨value, present, same⟩ := projectSlot?_sound slot source query root
    generation environment substitution observed matched
  exact ⟨substituteOpen extension value,
    by simp [composeEnvironment, present],
    observeRoot?_substitution extension value root same⟩

/-! ## An explicit supplier overapproximation at one immutable authority -/

/-- Finite semantic data for this classifier. An implementation must establish
that its current program and symbol authority supplies these tables. Equality
of an unrelated revision counter is not a proof of that correspondence. -/
structure SupplierAuthority where
  callableSymbols : List (List UInt8)
  namedArities : List (List UInt8 × Nat)
  partialHead : List UInt8
  deriving DecidableEq, Repr

/-- Root-only rejection cannot inspect the partial's payload. It therefore
admits every application of the partial head to two children. It also admits
every larger known arity, even when another declaration has the exact arity. -/
def maySupplyRoot (authority : SupplierAuthority) : RootObservation -> Bool
  | .symbol name => authority.callableSymbols.contains name
  | .string _ => false
  | .integer _ => false
  | .application head arity =>
      (head == authority.partialHead && arity == 2) ||
        authority.namedArities.any fun declaration =>
          declaration.1 == head && decide (arity < declaration.2)

/-- Three explicit supplier shapes, independent of the Boolean classifier.
Groundness is deliberately omitted, making this a conservative target for
negative evidence. Canonical partials require an expression argument list;
the root classifier does not need to read it to overapproximate this shape. -/
inductive SupplierShape (authority : SupplierAuthority) : OpenTerm -> Prop
  | callable (name : List UInt8)
      (present : name ∈ authority.callableSymbols) :
      SupplierShape authority (.symbol name)
  | canonicalPartial (base : OpenTerm) (argumentsHead : List UInt8)
      (arguments : OpenTerms) :
      SupplierShape authority
        (.application authority.partialHead
          (.cons base (.cons (.application argumentsHead arguments) .nil)))
  | underapplication (head : List UInt8) (arguments : OpenTerms)
      (wanted : Nat) (present : (head, wanted) ∈ authority.namedArities)
      (fewer : queryArity arguments < wanted) :
      SupplierShape authority (.application head arguments)

/-- Every independently described supplier shape is accepted by the concrete
classifier. This proves shape coverage, not coverage of a runtime selector's
possible binding entries or an interprocedural analysis. -/
theorem supplierShape_observed_possible
    (authority : SupplierAuthority) (value : OpenTerm)
    (supplier : SupplierShape authority value) :
    ∃ root, observeRoot? value = some root ∧
      maySupplyRoot authority root = true := by
  cases supplier with
  | callable name present =>
      exact ⟨.symbol name, rfl, by simpa [maySupplyRoot] using present⟩
  | canonicalPartial base argumentsHead arguments =>
      exact ⟨.application authority.partialHead 2, rfl,
        by simp [maySupplyRoot]⟩
  | underapplication head arguments wanted present fewer =>
      refine ⟨.application head (queryArity arguments), rfl, ?_⟩
      have accepted : authority.namedArities.any (fun declaration =>
          declaration.1 == head && decide (queryArity arguments < declaration.2)) =
          true := by
        exact List.any_eq_true.mpr ⟨(head, wanted), present, by simp [fewer]⟩
      simp [maySupplyRoot, accepted]

/-- Unknown projection remains a decline. Only a known root can justify
`some false`; no materialization or whole-forest groundness scan is required. -/
def projectedSupply? (authority : SupplierAuthority) (slot : UInt32)
    (source : Term) (query : OpenTerm) : Option Bool :=
  (projectSlot? slot source query).map (maySupplyRoot authority)

/-- A negative source-directed root observation rules out all three supplier
shapes for this slot in every successful structural match. It says nothing
about whether a different slot or matcher-produced entry can be a supplier. -/
theorem projectedSupply?_negative_sound
    (authority : SupplierAuthority) (slot : UInt32)
    (source : Term) (query : OpenTerm) (generation : UInt32)
    (environment : OpenEnvironment) (substitution : OpenSubstitution)
    (negative : projectedSupply? authority slot source query = some false)
    (matched : instantiateOpen generation environment source =
      substituteOpen substitution query) :
    ∃ value, environment slot = some value ∧ ¬ SupplierShape authority value := by
  cases projected : projectSlot? slot source query with
  | none => simp [projectedSupply?, projected] at negative
  | some root =>
      have rejected : maySupplyRoot authority root = false := by
        simpa [projectedSupply?, projected] using negative
      obtain ⟨value, present, same⟩ := projectSlot?_sound slot source query root
        generation environment substitution projected matched
      refine ⟨value, present, ?_⟩
      intro supplier
      obtain ⟨supplierRoot, supplierObserved, possible⟩ :=
        supplierShape_observed_possible authority value supplier
      have roots : supplierRoot = root :=
        Option.some.inj (supplierObserved.symm.trans same)
      simp [roots, rejected] at possible

/-! ## Positive and negative controls -/

namespace Canaries

private def authority : SupplierAuthority where
  callableSymbols := [[40], [41]]
  namedArities := [([40], 1), ([41], 3)]
  partialHead := [42]

private def nestedSource : Term :=
  .application [10]
    (.cons (.application [11] (.cons (.variable 0) .nil))
      (.cons (.variable 1) .nil))

private def nestedQuery (value payload : OpenTerm) : OpenTerm :=
  .application [10]
    (.cons (.application [11] (.cons value .nil)) (.cons payload .nil))

private def aliasName : LogicVariable := { generation := 7, slot := 8 }

private def replaceAlias (value : OpenTerm) : OpenSubstitution :=
  fun name => if name = aliasName then some value else none

private def largePayload : Nat -> OpenTerm
  | 0 => .symbol [40]
  | depth + 1 =>
      .application [50]
        (.cons (largePayload depth) (.cons (.variable aliasName) .nil))

/-- The unrelated payload can be any finite tree. Neither it nor the observed
application's children are forced to discover the latter's head and arity. -/
theorem arbitrary_payload_root_observed
    (arguments : OpenTerms) (payload : OpenTerm) :
    projectSlot? 0 nestedSource
      (nestedQuery (.application [30] arguments) payload) =
      some (.application [30] (queryArity arguments)) := by
  rfl

/-- Successful full matching is possible even when both the selected value
and the unrelated payload contain open variables. -/
theorem arbitrary_payload_has_structural_match
    (value payload : OpenTerm) :
    instantiateOpen 9 (fun slot => if slot = 0 then some value else some payload)
      nestedSource = nestedQuery value payload := by
  rfl

/-- A deep irrelevant tree and a callable symbol inside the selected data
value do not make that data root a supplier. This exercises the projection
algorithm and concrete classifier, not a postulated demand certificate. -/
theorem large_irrelevant_subtree_negative_supply :
    projectedSupply? authority 0 nestedSource
      (nestedQuery (.application [30] (.cons (.symbol [40]) .nil))
        (largePayload 4096)) = some false := by
  rfl

theorem open_children_keep_rigid_observation :
    observeRoot?
      (substituteOpen (replaceAlias (.symbol [40]))
        (.application [30] (.cons (.variable aliasName) .nil))) =
      some (.application [30] 1) := by
  exact observeRoot?_substitution _ _ _ rfl

/-- The observer's negative result is nonvacuous: concrete successful
environments exist and the captured data root is outside every supplier shape. -/
theorem data_root_binding_excludes_supplier :
    ¬ SupplierShape authority
      (.application [30] (.cons (.symbol [40]) .nil)) := by
  let value : OpenTerm := .application [30] (.cons (.symbol [40]) .nil)
  let payload : OpenTerm := .variable aliasName
  let environment : OpenEnvironment :=
    fun slot => if slot = 0 then some value else some payload
  have matched : instantiateOpen 9 environment nestedSource =
      substituteOpen emptyOpenSubstitution (nestedQuery value payload) := by
    rw [substituteOpen_empty]
    exact arbitrary_payload_has_structural_match value payload
  obtain ⟨bound, present, excluded⟩ :=
    projectedSupply?_negative_sound authority 0 nestedSource
      (nestedQuery value payload) 9 environment emptyOpenSubstitution
      (by rfl) matched
  have same : bound = value := by
    simpa [environment] using present.symm
  simpa [same, value] using excluded

private def repeatedSource : Term :=
  .application [13] (.cons (.variable 0) (.cons (.variable 0) .nil))

private def repeatedQuery (first second : OpenTerm) : OpenTerm :=
  .application [13] (.cons first (.cons second .nil))

/-- The first occurrence reveals a root while a later occurrence remains an
alias. Ordinary matching is still responsible for equating both fields. -/
theorem repeated_slot_known_first :
    projectSlot? 0 repeatedSource
      (repeatedQuery (.application [30] .nil) (.variable aliasName)) =
      some (.application [30] 0) := by
  rfl

theorem repeated_alias_has_consistent_match :
    instantiateOpen 9 (fun _ => some (.application [30] .nil)) repeatedSource =
      substituteOpen (replaceAlias (.application [30] .nil))
        (repeatedQuery (.application [30] .nil) (.variable aliasName)) := by
  rfl

/-- An incompatible later alias resolution defeats the complete match even
though the first occurrence's root was observable. Projection cannot erase
the second occurrence's equation. -/
theorem repeated_alias_conflict_has_no_match
    (generation : UInt32) (environment : OpenEnvironment) :
    instantiateOpen generation environment repeatedSource ≠
      substituteOpen (replaceAlias (.integer 3))
        (repeatedQuery (.integer 2) (.variable aliasName)) := by
  intro matched
  simp only [repeatedSource, repeatedQuery, instantiateOpen, instantiateOpenTerms,
    substituteOpen, substituteOpenTerms, replaceAlias,
    OpenTerm.application.injEq, OpenTerms.cons.injEq] at matched
  cases present : environment 0 with
  | none => simp [present] at matched
  | some value =>
      simp [present] at matched
      have distinct : OpenTerm.integer 2 ≠ .integer 3 := by decide
      exact distinct (matched.1.symm.trans matched.2)

/-- A later known occurrence is not a substitute for the selected unresolved
first occurrence. After resolving the alias, the same observer may succeed. -/
theorem unknown_first_occurrence_declines :
    projectedSupply? authority 0 repeatedSource
      (repeatedQuery (.variable aliasName) (.application [30] .nil)) = none ∧
    projectedSupply? authority 0 repeatedSource
      (substituteOpen (replaceAlias (.application [30] .nil))
        (repeatedQuery (.variable aliasName) (.application [30] .nil))) =
      some false := by
  decide

theorem unknown_is_not_negative_supply :
    projectedSupply? authority 0 (.variable 0) (.variable aliasName) = none ∧
    projectedSupply? authority 0 (.variable 0) (.variable aliasName) ≠
      some false := by
  decide

/-- A replacement for the same numeric slot in another rule generation does
not resolve this variable. Source identity must survive physical adaptation. -/
theorem another_generation_remains_unknown :
    observeRoot? (substituteOpen (replaceAlias (.integer 2))
      (.variable { generation := 8, slot := 8 })) = none := by
  decide

/-- Missing query children, wrong rigid heads, and a wholly open query root
all decline the source path instead of producing negative supply evidence. -/
theorem incompatible_spines_decline :
    projectSlot? 0 nestedSource (.variable aliasName) = none ∧
    projectSlot? 0 nestedSource
      (.application [10]
        (.cons (.application [11] (.cons (.integer 2) .nil)) .nil)) = none ∧
    projectSlot? 0 nestedSource
      (.application [10]
        (.cons (.application [99] (.cons (.integer 2) .nil))
          (.cons (.integer 3) .nil))) = none := by
  decide

/-- Atomic data is negative while known callable symbols, a possible partial
root with unresolved payload, and a known underapplication remain possible. -/
theorem classifier_positive_and_negative_roots :
    maySupplyRoot authority (.integer 2) = false ∧
    maySupplyRoot authority (.string [40]) = false ∧
    maySupplyRoot authority (.symbol [30]) = false ∧
    maySupplyRoot authority (.symbol [40]) = true ∧
    projectedSupply? authority 0 (.variable 0)
      (.application [42] (.cons (.variable aliasName) (.cons (.variable aliasName) .nil))) =
      some true ∧
    maySupplyRoot authority (.application [41] 2) = true := by
  decide

/-- A root-only partial test deliberately accepts a malformed payload. It is
an overapproximation and therefore cannot be used as positive validity proof. -/
theorem malformed_partial_root_remains_possible :
    projectedSupply? authority 0 (.variable 0)
      (.application [42] (.cons (.integer 1) (.cons (.integer 2) .nil))) =
      some true := by
  decide

theorem exact_arity_exception_is_conservatively_ignored :
    maySupplyRoot
      { authority with namedArities := [([41], 2), ([41], 3)] }
      (.application [41] 2) = true := by
  decide

/-- The term has not changed, but a new callable declaration changes the
negative result. Cached evidence must stay tied to authority that covers all
classifier inputs; logical substitution stability is insufficient. -/
theorem stale_authority_changes_negative_to_possible :
    projectedSupply? authority 0 (.variable 0) (.symbol [30]) = some false ∧
    projectedSupply? { authority with callableSymbols := [30] :: authority.callableSymbols }
      0 (.variable 0) (.symbol [30]) = some true := by
  decide

end Canaries

#print axioms observeRoot?_substitution
#print axioms projectSlot?_sound
#print axioms projectSlot?_sound_after_extension
#print axioms supplierShape_observed_possible
#print axioms projectedSupply?_negative_sound
#print axioms Canaries.large_irrelevant_subtree_negative_supply
#print axioms Canaries.data_root_binding_excludes_supplier
#print axioms Canaries.repeated_alias_conflict_has_no_match
#print axioms Canaries.unknown_first_occurrence_declines
#print axioms Canaries.stale_authority_changes_negative_to_possible

end Mettapedia.GSLT.LanguageDef.RootSupportProjectionCompilation
