import Mettapedia.Languages.MeTTa.PeTTa.IntrinsicTypeTraversal

/-!
# Independent output admission for recursive intrinsic type queries

Fresh allocation locality and the recursive coordinate law establish that a
query cannot invent an absent caller or parent name. This is the support
condition needed when an output alias is moved across child queries.

The resolved traversal preserves solved form: a solved private codomain
name cannot reappear in later argument refinements. This discharges the
recursive variable-codomain publication case, with all ordered projected
refinement families retained. Nonvariable codomains leave the argument
traversal unchanged. The whole ordered function dispatch preserves these
projected answer families. Independent structural products are treated in
`IndependentTypeOutputStructural`. The completed recursive root comparison,
including its fuel relation, is proved in `IndependentTypeOutputRoot`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutput.Admission

open Mettapedia.Logic.LP
open Mettapedia.Logic.LP.UnificationRenaming
open IntrinsicTypeFacts (signature TypeTerm Declaration)
open SupplyLocality

private def names (terms : List TypeTerm) : Finset Nat :=
  terms.foldr (fun term tail => term.freeVars ∪ tail) ∅

private theorem name_mem {terms : List TypeTerm} {term : TypeTerm} {name : Nat}
    (present : term ∈ terms) (occurs : name ∈ term.freeVars) : name ∈ names terms := by
  induction terms with
  | nil => simp at present
  | cons head tail ih =>
      rcases List.mem_cons.mp present with rfl | later
      · exact Finset.mem_union_left _ occurs
      · exact Finset.mem_union_right _ (ih later)

/-- The caller namespace has a name outside any finite set of terms. -/
theorem unused_caller (terms : List TypeTerm) :
    ∃ slot, ∀ term ∈ terms, callerName slot ∉ term.freeVars := by
  let slot := (names terms).sup id + 1
  refine ⟨slot, ?_⟩
  intro term present occurs
  have small : callerName slot ≤ (names terms).sup id :=
    Finset.le_sup (f := id) (name_mem present occurs)
  have large : slot ≤ callerName slot := Nat.right_le_pair 0 slot
  dsimp only [slot] at small large
  omega

/-- Renaming two absent variables changes no part of a term. -/
theorem swap_fixes_term (left right : Nat) (term : TypeTerm)
    (leftAbsent : left ∉ term.freeVars) (rightAbsent : right ∉ term.freeVars) :
    Coordinates.R (Equiv.swap left right) term = term := by
  apply Subst.applyTerm_eq_self
  intro name occurs
  have notLeft : name ≠ left := fun equal => leftAbsent (equal ▸ occurs)
  have notRight : name ≠ right := fun equal => rightAbsent (equal ▸ occurs)
  simp only [Equiv.swap_apply_of_ne_of_ne notLeft notRight]

private theorem map_fixes {α : Type} (f : α → α) (items : List α)
    (same : items.map f = items) : ∀ item ∈ items, f item = item := by
  induction items with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.cons.injEq] at same
      intro item member
      rcases List.mem_cons.mp member with rfl | later
      · exact same.1
      · exact ih same.2 item later

/-- Every returned term is supported by the incoming operands and names
allocated below this invocation. Failed trials and ordered alternatives are
covered by the same concrete recursive execution theorem. -/
theorem run_excludes_name (library : List Declaration) (fuel : Nat) (path : Path)
    (subject : TypeTerm) (required : Option TypeTerm) (answers : List TypeTerm)
    (excluded : Nat)
    (notAllocated : ∀ stem slot, freshSupply (stem ++ path) slot ≠ excluded)
    (subjectAbsent : excluded ∉ subject.freeVars)
    (requirementAbsent : ∀ term ∈ required.toList, excluded ∉ term.freeVars)
    (returned : run library freshSupply fuel path subject required = some answers) :
    ∀ answer ∈ answers, excluded ∉ answer.freeVars := by
  obtain ⟨slot, unused⟩ := unused_caller
    ((Term.var excluded) :: subject :: (required.toList ++ answers))
  let witness := callerName slot
  have distinct : excluded ≠ witness := by
    have fresh := unused (.var excluded) List.mem_cons_self
    simpa only [Term.freeVars, Finset.mem_singleton, ne_eq, eq_comm] using fresh
  have subjectFixed : Coordinates.R (Equiv.swap excluded witness) subject = subject :=
    swap_fixes_term excluded witness subject subjectAbsent
      (unused subject (by simp))
  have requiredFixed : required.map (Coordinates.R (Equiv.swap excluded witness)) = required := by
    cases required with
    | none => rfl
    | some term =>
        simp only [Option.map_some, Option.some.injEq]
        exact swap_fixes_term excluded witness term
          (requirementAbsent term (by simp)) (unused term (by simp))
  have supplyFixed : SuppliesAgreeAt path freshSupply
      (Coordinates.S (Equiv.swap excluded witness) freshSupply) := by
    intro stem childSlot
    dsimp only [Coordinates.S]
    symm
    exact Equiv.swap_apply_of_ne_of_ne (notAllocated stem childSlot)
      (fresh_supply_separate _ childSlot slot)
  have same := run_equivariant_of_local_supply (Equiv.swap excluded witness)
    library freshSupply freshSupply fuel path supplyFixed subject required
  rw [subjectFixed, requiredFixed, returned] at same
  simp only [Option.map_some, Option.some.injEq] at same
  have fixes : ∀ answer ∈ answers,
      Coordinates.R (Equiv.swap excluded witness) answer = answer := by
    exact map_fixes _ answers same.symm
  intro answer present occurs
  have nameFixed := Subst.var_fixed_of_applyTerm_eq_self (fixes answer present)
    excluded occurs
  have impossible : witness = excluded := by
    simpa only [Equiv.swap_apply_left, Term.var.injEq] using nameFixed
  exact distinct impossible.symm

/-- A successful match cannot introduce a name absent from its operands. -/
theorem match_excludes_name (candidate formal : TypeTerm) (excluded : Nat)
    (refinement : Subst signature)
    (accepted : unifyTotal [(candidate, formal)] = some refinement)
    (candidateAbsent : excluded ∉ candidate.freeVars)
    (formalAbsent : excluded ∉ formal.freeVars) (term : TypeTerm)
    (termAbsent : excluded ∉ term.freeVars) :
    excluded ∉ (refinement.applyTerm term).freeVars := by
  intro occurs
  have relevant := unifyTotal_relevantIdempotent _ _ accepted
  rcases Finset.mem_union.mp (relevant.freeVars_applyTerm_subset term occurs) with old | new
  · exact termAbsent old
  · simp only [eqVars, Finset.union_empty,
      Finset.mem_union] at new
    exact new.elim candidateAbsent formalAbsent

/-- The resolved argument traversal never reintroduces a name when child
queries and the actual matcher both preserve its absence. -/
theorem arguments_excludes_name (query : Query) (path : Path) (excluded : Nat)
    (children : ∀ position subject formal values,
      excluded ∉ subject.freeVars → excluded ∉ formal.freeVars →
      query (0 :: position :: path) subject (some formal) = some values →
      ∀ value ∈ values, excluded ∉ value.freeVars)
    (position : Nat) (pending : List (TypeTerm × TypeTerm)) (result : TypeTerm)
    (pendingAbsent : ∀ pair ∈ pending,
      excluded ∉ pair.1.freeVars ∧ excluded ∉ pair.2.freeVars)
    (resultAbsent : excluded ∉ result.freeVars) (answers : List TypeTerm)
    (returned : Resolution.argumentsResolved query path position pending result = some answers) :
    ∀ answer ∈ answers, excluded ∉ answer.freeVars := by
  induction length : pending.length using Nat.strong_induction_on generalizing pending position result answers with
  | h count ih =>
      cases pending with
      | nil =>
          simp only [Resolution.argumentsResolved, Option.some.injEq] at returned
          subst answers
          simpa using resultAbsent
      | cons pair rest =>
          rcases pair with ⟨subject, formal⟩
          simp only [Resolution.argumentsResolved] at returned
          by_cases rootVariable : isVariable subject = true
          · simp only [rootVariable, ↓reduceIte] at returned
            exact ih rest.length (by simp only [List.length_cons] at length; omega) (position + 1) rest result
              (fun pair member => pendingAbsent pair (List.mem_cons_of_mem _ member))
              resultAbsent answers returned rfl
          · simp only [rootVariable, Bool.false_eq_true, ↓reduceIte] at returned
            cases got : query (0 :: position :: path) subject (some formal) with
            | none => simp [got] at returned
            | some candidates =>
                simp only [got] at returned
                intro answer present
                obtain ⟨candidate, member, values, branch, inBranch⟩ :=
                  collect_member candidates _ answers returned present
                cases accepted : unifyTotal [(candidate, formal)] with
                | none => simp [accepted] at branch; subst values; simp at inBranch
                | some refinement =>
                    simp only [accepted] at branch
                    have absent := pendingAbsent (subject, formal) List.mem_cons_self
                    have candidateAbsent := children position subject formal candidates
                      absent.1 absent.2 got candidate member
                    have preserve := match_excludes_name candidate formal excluded refinement
                      accepted candidateAbsent absent.2
                    exact ih rest.length (by simp only [List.length_cons] at length; omega)
                      (position + 1) (rest.map fun pair =>
                        (refinement.applyTerm pair.1, refinement.applyTerm pair.2)) (refinement.applyTerm result)
                      (by
                        intro pair member
                        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
                        have old := pendingAbsent original
                          (List.mem_cons_of_mem _ originalMember)
                        exact ⟨preserve _ old.1, preserve _ old.2⟩)
                      (preserve _ resultAbsent) values branch (by simp) answer inBranch

/-- Output support needs only the pending requirements. Subject variables
may be present, but intrinsic child queries return types, not their syntax. -/
theorem arguments_result_excludes_name (query : Query) (path : Path) (excluded : Nat)
    (children : ∀ position subject formal values,
      excluded ∉ formal.freeVars →
      query (0 :: position :: path) subject (some formal) = some values →
      ∀ value ∈ values, excluded ∉ value.freeVars)
    (position : Nat) (pending : List (TypeTerm × TypeTerm)) (result : TypeTerm)
    (pendingAbsent : ∀ pair ∈ pending, excluded ∉ pair.2.freeVars)
    (resultAbsent : excluded ∉ result.freeVars) (answers : List TypeTerm)
    (returned : Resolution.argumentsResolved query path position pending result = some answers) :
    ∀ answer ∈ answers, excluded ∉ answer.freeVars := by
  induction length : pending.length using Nat.strong_induction_on
      generalizing pending position result answers with
  | h count ih =>
      cases pending with
      | nil =>
          simp only [Resolution.argumentsResolved, Option.some.injEq] at returned
          subst answers
          simpa using resultAbsent
      | cons pair rest =>
          rcases pair with ⟨subject, formal⟩
          simp only [Resolution.argumentsResolved] at returned
          by_cases rootVariable : isVariable subject = true
          · simp only [rootVariable, ↓reduceIte] at returned
            exact ih rest.length (by simp only [List.length_cons] at length; omega)
              (position + 1) rest result
              (fun pair member => pendingAbsent pair (List.mem_cons_of_mem _ member))
              resultAbsent answers returned rfl
          · simp only [rootVariable, Bool.false_eq_true, ↓reduceIte] at returned
            cases got : query (0 :: position :: path) subject (some formal) with
            | none => simp [got] at returned
            | some candidates =>
                simp only [got] at returned
                intro answer present
                obtain ⟨candidate, member, values, branch, inBranch⟩ :=
                  collect_member candidates _ answers returned present
                cases accepted : unifyTotal [(candidate, formal)] with
                | none => simp [accepted] at branch; subst values; simp at inBranch
                | some refinement =>
                    simp only [accepted] at branch
                    have formalAbsent := pendingAbsent (subject, formal) List.mem_cons_self
                    have candidateAbsent := children position subject formal candidates
                      formalAbsent got candidate member
                    have preserve := match_excludes_name candidate formal excluded refinement
                      accepted candidateAbsent formalAbsent
                    exact ih rest.length (by simp only [List.length_cons] at length; omega)
                      (position + 1) (rest.map fun pair =>
                        (refinement.applyTerm pair.1, refinement.applyTerm pair.2))
                      (refinement.applyTerm result)
                      (by
                        intro pair member
                        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
                        exact preserve _
                          (pendingAbsent original (List.mem_cons_of_mem _ originalMember)))
                      (preserve _ resultAbsent) values branch (by simp) answer inBranch

private theorem row_excludes (items : List TypeTerm) (excluded : Nat)
    (absent : ∀ item ∈ items, excluded ∉ item.freeVars) :
    excluded ∉ (row items).freeVars := by
  intro occurs
  obtain ⟨index, present⟩ := (Term.mem_freeVars_app (σ := signature)).mp occurs
  exact absent items[index] (List.getElem_mem _) present

private theorem row_member_excludes (term : TypeTerm) (items : List TypeTerm)
    (parsed : elements term = some items) (excluded : Nat)
    (absent : excluded ∉ term.freeVars) :
    ∀ item ∈ items, excluded ∉ item.freeVars := by
  cases term with
  | var _ => simp [elements] at parsed
  | const _ => simp [elements] at parsed
  | app arity children =>
      simp only [elements, Option.some.injEq] at parsed
      subst items
      intro item member occurs
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
      exact absent ((Term.mem_freeVars_app (σ := signature)).mpr ⟨index, occurs⟩)

private theorem parts_exclude (items : List TypeTerm) (arity : Nat)
    (domains : List TypeTerm) (result : TypeTerm) (excluded : Nat)
    (absent : ∀ item ∈ items, excluded ∉ item.freeVars)
    (parsed : parts arity items = some (domains, result)) :
    (∀ domain ∈ domains, excluded ∉ domain.freeVars) ∧ excluded ∉ result.freeVars := by
  cases items with
  | nil => simp [parts] at parsed
  | cons head fields =>
      simp only [parts] at parsed
      split at parsed
      · cases reversed : fields.reverse with
        | nil => simp [reversed] at parsed
        | cons output inputs =>
            simp only [reversed] at parsed
            split at parsed
            · simp only [Option.some.injEq, Prod.mk.injEq] at parsed
              rcases parsed with ⟨rfl, rfl⟩
              constructor
              · intro domain member
                apply absent _ (List.mem_cons_of_mem _ ?_)
                apply List.mem_reverse.mp
                rw [reversed]
                exact List.mem_cons_of_mem _ (List.mem_reverse.mp member)
              · apply absent _ (List.mem_cons_of_mem _ ?_)
                apply List.mem_reverse.mp
                rw [reversed]
                exact List.mem_cons_self
            · simp at parsed
      · simp at parsed

theorem callParts_exclude (scheme : TypeTerm) (arity : Nat)
    (domains : List TypeTerm) (result : TypeTerm) (excluded : Nat)
    (absent : excluded ∉ scheme.freeVars)
    (parsed : callParts arity scheme = some (domains, result)) :
    (∀ domain ∈ domains, excluded ∉ domain.freeVars) ∧ excluded ∉ result.freeVars := by
  unfold callParts at parsed
  cases elementsFound : elements scheme with
  | none => simp [elementsFound] at parsed
  | some items =>
      exact parts_exclude items arity domains result excluded
        (row_member_excludes scheme items elementsFound excluded absent)
        (by simpa [elementsFound] using parsed)

theorem declarations_exclude (library : List Declaration) (supply : Supply)
    (path : Path) (subject : TypeTerm) (excluded : Nat)
    (notAllocated : ∀ occurrence slot, supply (1 :: occurrence :: path) slot ≠ excluded) :
    ∀ scheme ∈ declarations library supply path subject, excluded ∉ scheme.freeVars := by
  cases subject with
  | var _ => simp [declarations]
  | app _ _ => simp [declarations]
  | const scalar =>
      cases scalar with
      | number _ => simp [declarations]
      | string _ => simp [declarations]
      | boolean _ => simp [declarations]
      | symbol name =>
          intro scheme member occurs
          obtain ⟨declaration, _, item⟩ := List.mem_flatMap.mp member
          split at item
          · simp only [List.mem_singleton] at item
            subst scheme
            obtain ⟨original, _, generated⟩ := (Subst.mem_freeVars_applyTerm (σ := signature)).mp occurs
            change excluded ∈ (Term.var (supply (1 :: declaration.occurrence :: path) original) : TypeTerm).freeVars
              at generated
            exact notAllocated declaration.occurrence original
              ((Term.mem_freeVars_var (σ := signature)).mp generated).symm
          · simp at item

private theorem matched_excludes (required : TypeTerm) (candidates : List TypeTerm)
    (excluded : Nat) (requiredAbsent : excluded ∉ required.freeVars)
    (candidateAbsent : ∀ candidate ∈ candidates, excluded ∉ candidate.freeVars) :
    ∀ answer ∈ matched required candidates, excluded ∉ answer.freeVars := by
  intro answer member
  obtain ⟨candidate, present, branch⟩ := List.mem_flatMap.mp member
  obtain ⟨refinement, accepted, rfl⟩ := List.mem_map.mp branch
  have found : unifyTotal [(candidate, required)] = some refinement := by
    simpa using accepted
  exact match_excludes_name candidate required excluded refinement found
    (candidateAbsent candidate present) requiredAbsent required requiredAbsent

private theorem select_excludes (required : Option TypeTerm) (candidates : List TypeTerm)
    (excluded : Nat) (requiredAbsent : ∀ term ∈ required.toList, excluded ∉ term.freeVars)
    (candidateAbsent : ∀ candidate ∈ candidates, excluded ∉ candidate.freeVars) :
    ∀ answer ∈ select required candidates, excluded ∉ answer.freeVars := by
  cases required with
  | none => exact candidateAbsent
  | some term =>
      exact matched_excludes term candidates excluded
        (requiredAbsent term (by simp)) candidateAbsent

private theorem finish_excludes (required : Option TypeTerm) (candidates : List TypeTerm)
    (excluded : Nat) (requiredAbsent : ∀ term ∈ required.toList, excluded ∉ term.freeVars)
    (candidateAbsent : ∀ candidate ∈ candidates, excluded ∉ candidate.freeVars) :
    ∀ answer ∈ finish required candidates, excluded ∉ answer.freeVars := by
  unfold finish
  split
  · cases required with
    | none => simp [IntrinsicTypeFacts.undefinedType, IntrinsicTypeFacts.named, Term.freeVars]
    | some term =>
        exact matched_excludes term [IntrinsicTypeFacts.undefinedType] excluded
          (requiredAbsent term (by simp)) (by simp [IntrinsicTypeFacts.undefinedType,
            IntrinsicTypeFacts.named, Term.freeVars])
  · exact candidateAbsent

private theorem stored_arguments_exclude (query : Query) (path : Path) (excluded : Nat)
    (children : ∀ position subject formal values,
      excluded ∉ formal.freeVars →
      query (0 :: position :: path) subject (some formal) = some values →
      ∀ value ∈ values, excluded ∉ value.freeVars)
    (position : Nat) (pending : List (TypeTerm × TypeTerm)) (result : TypeTerm)
    (store : Subst signature)
    (pendingAbsent : ∀ pair ∈ pending, excluded ∉ (store.applyTerm pair.2).freeVars)
    (resultAbsent : excluded ∉ (store.applyTerm result).freeVars) (answers : List TypeTerm)
    (returned : arguments query path position pending result store = some answers) :
    ∀ answer ∈ answers, excluded ∉ answer.freeVars := by
  rw [Resolution.arguments_eq_resolved] at returned
  apply arguments_result_excludes_name query path excluded children position _ _ _ resultAbsent
    answers returned
  intro pair member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact pendingAbsent original present

private theorem functions_exclude (library : List Declaration) (supply : Supply)
    (query : Query) (path : Path) (excluded : Nat)
    (notAllocated : ∀ occurrence slot, supply (1 :: occurrence :: path) slot ≠ excluded)
    (children : ∀ position subject formal values,
      excluded ∉ formal.freeVars →
      query (0 :: position :: path) subject (some formal) = some values →
      ∀ value ∈ values, excluded ∉ value.freeVars)
    (items : List TypeTerm) (required : Option TypeTerm)
    (requiredAbsent : ∀ term ∈ required.toList, excluded ∉ term.freeVars)
    (answers : List TypeTerm)
    (returned : functions library supply query path items required = some answers) :
    ∀ answer ∈ answers, excluded ∉ answer.freeVars := by
  cases items with
  | nil => simp [functions] at returned; subst answers; simp
  | cons head actuals =>
      intro answer present
      obtain ⟨scheme, member, values, branch, inBranch⟩ :=
        collect_member _ _ answers returned present
      have schemeAbsent := declarations_exclude library supply path head excluded notAllocated
        scheme member
      cases parsed : callParts actuals.length scheme with
      | none => simp [parsed] at branch; subst values; simp at inBranch
      | some pair =>
          rcases pair with ⟨domains, result⟩
          have absent := callParts_exclude scheme actuals.length domains result excluded
            schemeAbsent parsed
          simp only [parsed] at branch
          cases required with
          | none =>
              exact stored_arguments_exclude query path excluded children 0 (actuals.zip domains)
                result (Subst.id signature)
                (fun pair member => by
                  simpa only [Subst.applyTerm_id] using
                    (absent.1 pair.2 (List.of_mem_zip member).2))
                (by simpa only [Subst.applyTerm_id] using absent.2) values branch answer inBranch
          | some target =>
              dsimp only at branch
              cases accepted : unifyTotal [(result, target)] with
              | none => simp [accepted] at branch; subst values; simp at inBranch
              | some initial =>
                  simp only [accepted] at branch
                  have preserve := match_excludes_name result target excluded initial accepted
                    absent.2 (requiredAbsent target (by simp))
                  exact stored_arguments_exclude query path excluded children 0 (actuals.zip domains)
                    result initial (fun pair member => preserve _
                      (absent.1 _ (List.of_mem_zip member).2))
                    (preserve result absent.2) values branch answer inBranch

private theorem freshRows_exclude (query : Query) (path : Path) (excluded : Nat)
    (children : ∀ position subject values,
      query (0 :: position :: path) subject none = some values →
      ∀ value ∈ values, excluded ∉ value.freeVars)
    (position : Nat) (items : List TypeTerm) (answers : List (List TypeTerm))
    (returned : freshRows query path position items = some answers) :
    ∀ row ∈ answers, ∀ item ∈ row, excluded ∉ item.freeVars := by
  induction items generalizing position answers with
  | nil => simp [freshRows] at returned; subst answers; simp
  | cons subject rest ih =>
      simp only [freshRows] at returned
      cases first : query (0 :: position :: path) subject none with
      | none => simp [first] at returned
      | some candidates =>
          cases later : freshRows query path (position + 1) rest with
          | none => simp [first, later] at returned
          | some rows =>
              simp only [first, later, bind, Option.bind, Option.pure_def,
                Option.some.injEq] at returned
              subst answers
              intro values member value occurs
              obtain ⟨candidate, present, branch⟩ := List.mem_flatMap.mp member
              obtain ⟨tail, inTail, rfl⟩ := List.mem_map.mp branch
              rcases List.mem_cons.mp occurs with rfl | remaining
              · exact children position subject candidates first value present
              · exact ih (position + 1) rows later tail inTail value remaining

private theorem structural_excludes (supply : Supply) (query : Query) (path : Path)
    (excluded : Nat) (notAllocated : ∀ slot, supply (3 :: path) slot ≠ excluded)
    (children : ∀ position subject required values,
      (∀ term ∈ required.toList, excluded ∉ term.freeVars) →
      query (0 :: position :: 4 :: path) subject required = some values →
      ∀ value ∈ values, excluded ∉ value.freeVars)
    (items : List TypeTerm) (required : Option TypeTerm)
    (requiredAbsent : ∀ term ∈ required.toList, excluded ∉ term.freeVars)
    (answers : List TypeTerm)
    (returned : structural supply query path items required = some answers) :
    ∀ answer ∈ answers, excluded ∉ answer.freeVars := by
  cases required with
  | none =>
      cases got : freshRows query (4 :: path) 0 items with
      | none => simp [structural, got] at returned
      | some rows =>
          simp only [structural, got, Option.map_some, Option.some.injEq] at returned
          subst answers
          intro answer member
          obtain ⟨values, present, rfl⟩ := List.mem_map.mp member
          exact row_excludes values excluded
            (freshRows_exclude query (4 :: path) excluded
              (fun position subject values => children position subject none values (by simp))
              0 items rows got values present)
  | some target =>
      let fields : List TypeTerm := (List.range items.length).map
        (fun index => .var (supply (3 :: path) index))
      have fieldsAbsent : ∀ field ∈ fields, excluded ∉ field.freeVars := by
        intro field member
        obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
        simpa only [Term.freeVars, Finset.mem_singleton] using Ne.symm (notAllocated index)
      have resultAbsent := row_excludes fields excluded fieldsAbsent
      change (match unifyTotal [(row fields, target)] with
        | none => some []
        | some initial => arguments query (4 :: path) 0 (items.zip fields)
            (row fields) initial) = some answers at returned
      cases accepted : unifyTotal [(row fields, target)] with
      | none => simp [accepted] at returned; subst answers; simp
      | some initial =>
          simp only [accepted] at returned
          have preserve := match_excludes_name (row fields) target excluded initial accepted
            resultAbsent (requiredAbsent target (by simp))
          exact stored_arguments_exclude query (4 :: path) excluded
            (fun position subject formal values absent =>
              children position subject (some formal) values (by simpa using absent))
            0 (items.zip fields) (row fields) initial
            (fun pair member => preserve _ (fieldsAbsent _ (List.of_mem_zip member).2))
            (preserve _ resultAbsent) answers returned

private theorem expression_excludes (library : List Declaration) (supply : Supply)
    (query : Query) (path : Path) (excluded : Nat)
    (notAllocated : ∀ stem slot, supply (stem ++ path) slot ≠ excluded)
    (children : ∀ stem subject required values,
      (∀ term ∈ required.toList, excluded ∉ term.freeVars) →
      query (stem ++ path) subject required = some values →
      ∀ value ∈ values, excluded ∉ value.freeVars)
    (items : List TypeTerm) (required : Option TypeTerm)
    (requiredAbsent : ∀ term ∈ required.toList, excluded ∉ term.freeVars)
    (answers : List TypeTerm)
    (returned : expression library supply query path items required = some answers) :
    ∀ answer ∈ answers, excluded ∉ answer.freeVars := by
  obtain ⟨functionAnswers, functionRun, rest⟩ := Option.bind_eq_some_iff.mp returned
  obtain ⟨allFunctions, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨rowAnswers, rowRun, final⟩ := Option.bind_eq_some_iff.mp rest
  have finalEq : finish required (functionAnswers ++ rowAnswers) = answers := Option.some.inj final
  rw [← finalEq]
  apply finish_excludes required _ excluded requiredAbsent
  intro answer present
  rcases List.mem_append.mp present with fromFunction | fromRow
  · exact functions_exclude library supply query path excluded
      (fun occurrence slot => notAllocated [1, occurrence] slot)
      (fun position subject formal values absent => children [0, position] subject
        (some formal) values (by simpa using absent))
      items required requiredAbsent functionAnswers functionRun answer fromFunction
  · split at rowRun
    · exact structural_excludes supply query path excluded (notAllocated [3])
        (fun position subject required values => children [0, position, 4] subject required values)
        items required requiredAbsent rowAnswers rowRun answer fromRow
    · simp only [Option.some.injEq] at rowRun
      subst rowAnswers
      simp at fromRow

theorem literal_excludes (subject primitive : TypeTerm) (excluded : Nat)
    (found : literal subject = some primitive) : excluded ∉ primitive.freeVars := by
  cases subject with
  | var _ => simp [literal] at found
  | app _ _ => simp [literal] at found
  | const value =>
      cases value <;> simp [literal, IntrinsicTypeFacts.primitiveType] at found
      all_goals subst primitive
      all_goals simp [IntrinsicTypeFacts.named, Term.freeVars]

/-- Intrinsic queries return names from their requirement and fresh type
allocations only. A variable occurring in the subject is not thereby a
variable of its type. This stronger support result establishes independence
between separate structural-product positions. -/
theorem run_output_excludes_name (library : List Declaration) (fuel : Nat) (path : Path)
    (subject : TypeTerm) (required : Option TypeTerm) (answers : List TypeTerm)
    (excluded : Nat)
    (notAllocated : ∀ stem slot, freshSupply (stem ++ path) slot ≠ excluded)
    (requirementAbsent : ∀ term ∈ required.toList, excluded ∉ term.freeVars)
    (returned : run library freshSupply fuel path subject required = some answers) :
    ∀ answer ∈ answers, excluded ∉ answer.freeVars := by
  induction fuel generalizing path subject required answers with
  | zero => simp [run] at returned
  | succ fuel ih =>
      have children : ∀ stem childSubject childRequired values,
          (∀ term ∈ childRequired.toList, excluded ∉ term.freeVars) →
          run library freshSupply fuel (stem ++ path) childSubject childRequired = some values →
          ∀ value ∈ values, excluded ∉ value.freeVars := by
        intro stem childSubject childRequired values absent got
        exact ih (stem ++ path) childSubject childRequired values
          (fun more slot => by simpa only [List.append_assoc] using notAllocated (more ++ stem) slot)
          absent got
      change step library freshSupply (run library freshSupply fuel) path subject required =
        some answers at returned
      unfold step at returned
      split at returned
      · simp only [Option.some.injEq] at returned
        subst answers
        cases required with
        | none =>
            simpa only [Option.getD_none, List.mem_singleton, forall_eq, Term.freeVars,
              Finset.mem_singleton, List.cons_append, List.nil_append] using Ne.symm (notAllocated [5] 0)
        | some term =>
            simpa only [Option.getD_some, List.mem_singleton, forall_eq] using
              requirementAbsent term (by simp)
      · cases primitiveRun : literal subject with
        | some primitive =>
            simp only [primitiveRun] at returned
            have primitiveAbsent := literal_excludes subject primitive excluded primitiveRun
            split at returned
            · simp only [Option.some.injEq] at returned
              subst answers
              exact select_excludes required [primitive] excluded requirementAbsent
                (by simpa using primitiveAbsent)
            · simp only [Option.some.injEq] at returned
              subst answers
              exact finish_excludes required [] excluded requirementAbsent (by simp)
        | none =>
            simp only [primitiveRun] at returned
            cases expressionRun : elements subject with
            | none =>
                simp only [expressionRun, Option.some.injEq] at returned
                subst answers
                exact finish_excludes required _ excluded requirementAbsent
                  (select_excludes required _ excluded requirementAbsent
                    (declarations_exclude library freshSupply path subject excluded
                      (fun occurrence slot => notAllocated [1, occurrence] slot)))
            | some items =>
                simp only [expressionRun] at returned
                exact expression_excludes library freshSupply (run library freshSupply fuel)
                  path excluded notAllocated children items required requirementAbsent answers returned

/-- Starting from a variable result, each completed answer either leaves
that variable unsolved or contains no occurrence of it. Once the total
unifier solves it, idempotence removes it from every remaining operand;
the recursive service therefore cannot create a later occurs-check cycle. -/
theorem arguments_variable_solved_form (query : Query) (path : Path) (name : Nat)
    (children : ∀ position subject formal values,
      name ∉ subject.freeVars → name ∉ formal.freeVars →
      query (0 :: position :: path) subject (some formal) = some values →
      ∀ value ∈ values, name ∉ value.freeVars)
    (position : Nat) (pending : List (TypeTerm × TypeTerm)) (answers : List TypeTerm)
    (returned : Resolution.argumentsResolved query path position pending (.var name) = some answers) :
    ∀ answer ∈ answers, answer = .var name ∨ name ∉ answer.freeVars := by
  induction length : pending.length using Nat.strong_induction_on generalizing pending position answers with
  | h count ih =>
      cases pending with
      | nil =>
          simp only [Resolution.argumentsResolved, Option.some.injEq] at returned
          subst answers
          simp
      | cons pair rest =>
          rcases pair with ⟨subject, formal⟩
          simp only [Resolution.argumentsResolved] at returned
          by_cases rootVariable : isVariable subject = true
          · simp only [rootVariable, ↓reduceIte] at returned
            exact ih rest.length (by simp only [List.length_cons] at length; omega) (position + 1) rest answers returned rfl
          · simp only [rootVariable, Bool.false_eq_true, ↓reduceIte] at returned
            cases got : query (0 :: position :: path) subject (some formal) with
            | none => simp [got] at returned
            | some candidates =>
                simp only [got] at returned
                intro answer present
                obtain ⟨candidate, _, values, branch, inBranch⟩ :=
                  collect_member candidates _ answers returned present
                cases accepted : unifyTotal [(candidate, formal)] with
                | none => simp [accepted] at branch; subst values; simp at inBranch
                | some refinement =>
                    simp only [accepted, Subst.applyTerm_var] at branch
                    by_cases fixed : refinement name = .var name
                    · rw [fixed] at branch
                      exact ih rest.length (by simp only [List.length_cons] at length; omega)
                        (position + 1) (rest.map fun pair =>
                          (refinement.applyTerm pair.1, refinement.applyTerm pair.2))
                        values branch (by simp) answer inBranch
                    · have absent := (unifyTotal_relevantIdempotent _ _ accepted).absorbs.solved_absent fixed
                      right
                      exact arguments_excludes_name query path name children (position + 1)
                        (rest.map fun pair =>
                          (refinement.applyTerm pair.1, refinement.applyTerm pair.2))
                        (refinement name)
                        (by
                          intro pair member
                          obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
                          exact ⟨absent _, absent _⟩)
                        (absent (.var name)) values branch answer inBranch

private theorem matched_variable_solved_form (name : Nat) (candidates : List TypeTerm) :
    ∀ answer ∈ matched (.var name) candidates,
      answer = .var name ∨ name ∉ answer.freeVars := by
  intro answer member
  obtain ⟨candidate, _, member⟩ := List.mem_flatMap.mp member
  obtain ⟨refinement, accepted, rfl⟩ := List.mem_map.mp member
  have accepted : unifyTotal [(candidate, .var name)] = some refinement :=
    Option.mem_toList.mp accepted
  by_cases fixed : refinement name = .var name
  · exact Or.inl fixed
  · exact Or.inr
      ((unifyTotal_relevantIdempotent _ _ accepted).absorbs.solved_absent fixed (.var name))

/-- Matching a variable result before a recursive argument sequence cannot
leave that variable inside its own solution. This applies to both function
codomains and structural fields, including later recursive refinements. -/
theorem matched_arguments_variable_solved_form (query : Query) (path : Path) (name : Nat)
    (children : ∀ position subject formal values,
      name ∉ formal.freeVars →
      query (0 :: position :: path) subject (some formal) = some values →
      ∀ value ∈ values, name ∉ value.freeVars)
    (position : Nat) (pending : List (TypeTerm × TypeTerm)) (result : TypeTerm)
    (initial : Subst signature)
    (accepted : unifyTotal [(result, .var name)] = some initial)
    (answers : List TypeTerm)
    (returned : arguments query path position pending result initial = some answers) :
    ∀ answer ∈ answers, answer = .var name ∨ name ∉ answer.freeVars := by
  rw [Resolution.arguments_eq_resolved] at returned
  have equated : initial.applyTerm result = initial name :=
    unifyTotal_sound _ _ accepted (result, .var name) List.mem_cons_self
  rw [equated] at returned
  by_cases fixed : initial name = .var name
  · rw [fixed] at returned
    exact arguments_variable_solved_form query path name
      (fun position subject formal values _ => children position subject formal values)
      position _ answers returned
  · have absent := (unifyTotal_relevantIdempotent _ _ accepted).absorbs.solved_absent fixed
    intro answer present
    right
    apply arguments_result_excludes_name query path name children position _ _ _
      (absent (.var name)) answers returned answer present
    intro pair member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    exact absent _

private theorem functions_variable_solved_form (library : List Declaration) (supply : Supply)
    (query : Query) (path : Path) (name : Nat)
    (children : ∀ position subject formal values,
      name ∉ formal.freeVars →
      query (0 :: position :: path) subject (some formal) = some values →
      ∀ value ∈ values, name ∉ value.freeVars)
    (items : List TypeTerm) (answers : List TypeTerm)
    (returned : functions library supply query path items (some (.var name)) = some answers) :
    ∀ answer ∈ answers, answer = .var name ∨ name ∉ answer.freeVars := by
  cases items with
  | nil => simp [functions] at returned; subst answers; simp
  | cons head actuals =>
      intro answer present
      obtain ⟨scheme, _, values, branch, inBranch⟩ :=
        collect_member _ _ answers returned present
      cases parsed : callParts actuals.length scheme with
      | none => simp [parsed] at branch; subst values; simp at inBranch
      | some pair =>
          rcases pair with ⟨domains, result⟩
          simp only [parsed] at branch
          cases accepted : unifyTotal [(result, .var name)] with
          | none => simp [accepted] at branch; subst values; simp at inBranch
          | some initial =>
              simp only [accepted] at branch
              exact matched_arguments_variable_solved_form query path name children 0
                (actuals.zip domains) result initial accepted values branch answer inBranch

private theorem structural_variable_solved_form (supply : Supply)
    (query : Query) (path : Path) (name : Nat)
    (children : ∀ position subject formal values,
      name ∉ formal.freeVars →
      query (0 :: position :: 4 :: path) subject (some formal) = some values →
      ∀ value ∈ values, name ∉ value.freeVars)
    (items : List TypeTerm) (answers : List TypeTerm)
    (returned : structural supply query path items (some (.var name)) = some answers) :
    ∀ answer ∈ answers, answer = .var name ∨ name ∉ answer.freeVars := by
  let fields := (List.range items.length).map fun index =>
    (Term.var (supply (3 :: path) index) : TypeTerm)
  change (match unifyTotal [(row fields, .var name)] with
    | none => some []
    | some initial => arguments query (4 :: path) 0 (items.zip fields)
        (row fields) initial) = some answers at returned
  cases accepted : unifyTotal [(row fields, .var name)] with
  | none => simp [accepted] at returned; subst answers; simp
  | some initial =>
      simp only [accepted] at returned
      exact matched_arguments_variable_solved_form query (4 :: path) name children
        0 _ _ initial accepted answers returned

private theorem finish_variable_solved_form (name : Nat) (candidates : List TypeTerm)
    (solved : ∀ answer ∈ candidates, answer = .var name ∨ name ∉ answer.freeVars) :
    ∀ answer ∈ finish (some (.var name)) candidates,
      answer = .var name ∨ name ∉ answer.freeVars := by
  unfold finish
  split
  · exact matched_variable_solved_form name _
  · exact solved

/-- Every completed bound query keeps its output in solved form. The
output may remain unconstrained; otherwise it never occurs inside its own
returned type, even through recursive function and structural branches. -/
theorem run_bound_variable_solved_form (library : List Declaration) (fuel : Nat)
    (path : Path) (subject : TypeTerm) (name : Nat)
    (notAllocated : ∀ stem slot, freshSupply (stem ++ path) slot ≠ name)
    (answers : List TypeTerm)
    (returned : run library freshSupply fuel path subject (some (.var name)) = some answers) :
    ∀ answer ∈ answers, answer = .var name ∨ name ∉ answer.freeVars := by
  cases fuel with
  | zero => simp [run] at returned
  | succ fuel =>
      have children : ∀ stem childSubject formal values,
          name ∉ formal.freeVars →
          run library freshSupply fuel (stem ++ path) childSubject (some formal) = some values →
          ∀ value ∈ values, name ∉ value.freeVars := by
        intro stem childSubject formal values absent got
        exact run_output_excludes_name library fuel (stem ++ path) childSubject
          (some formal) values name
          (fun more slot => by simpa only [List.append_assoc] using notAllocated (more ++ stem) slot)
          (by simpa using absent) got
      change step library freshSupply (run library freshSupply fuel) path subject
        (some (.var name)) = some answers at returned
      unfold step at returned
      split at returned
      · simp only [Option.getD_some, Option.some.injEq] at returned
        subst answers
        simp
      · cases primitiveRun : literal subject with
        | some primitive =>
            simp only [primitiveRun] at returned
            split at returned
            · simp only [Option.some.injEq] at returned
              subst answers
              exact matched_variable_solved_form name _
            · simp only [Option.some.injEq] at returned
              subst answers
              exact finish_variable_solved_form name [] (by simp)
        | none =>
            simp only [primitiveRun] at returned
            cases parsed : elements subject with
            | none =>
                simp only [parsed, Option.some.injEq] at returned
                subst answers
                exact finish_variable_solved_form name _ (matched_variable_solved_form name _)
            | some items =>
                simp only [parsed] at returned
                obtain ⟨functionAnswers, functionRun, rest⟩ := Option.bind_eq_some_iff.mp returned
                obtain ⟨allFunctions, _, rest⟩ := Option.bind_eq_some_iff.mp rest
                obtain ⟨rowAnswers, rowRun, final⟩ := Option.bind_eq_some_iff.mp rest
                have finalEq : finish (some (.var name)) (functionAnswers ++ rowAnswers) = answers :=
                  Option.some.inj final
                rw [← finalEq]
                apply finish_variable_solved_form
                intro answer present
                rcases List.mem_append.mp present with fromFunction | fromRow
                · exact functions_variable_solved_form library freshSupply
                    (run library freshSupply fuel) path name (children [0, ·])
                    items functionAnswers functionRun answer fromFunction
                · split at rowRun
                  · exact structural_variable_solved_form freshSupply (run library freshSupply fuel)
                      path name (children [0, ·, 4]) items rowAnswers rowRun answer fromRow
                  · simp only [Option.some.injEq] at rowRun
                    subst rowAnswers
                    simp at fromRow

/-- Instantiate absence preservation with the actual recursive query and
its disjoint allocation subtrees. No property of an abstract child service
remains an admission hypothesis. -/
theorem recursive_arguments_excludes_name (library : List Declaration) (fuel : Nat)
    (path : Path) (excluded : Nat)
    (notAllocated : ∀ position stem slot,
      freshSupply (stem ++ 0 :: position :: path) slot ≠ excluded)
    (position : Nat) (pending : List (TypeTerm × TypeTerm)) (result : TypeTerm)
    (pendingAbsent : ∀ pair ∈ pending,
      excluded ∉ pair.1.freeVars ∧ excluded ∉ pair.2.freeVars)
    (resultAbsent : excluded ∉ result.freeVars) (answers : List TypeTerm)
    (returned : Resolution.argumentsResolved (run library freshSupply fuel)
      path position pending result = some answers) :
    ∀ answer ∈ answers, excluded ∉ answer.freeVars := by
  apply arguments_excludes_name _ path excluded _ position pending result
    pendingAbsent resultAbsent answers returned
  intro position subject formal values subjectAbsent formalAbsent accepted
  exact run_excludes_name library fuel (0 :: position :: path) subject
    (some formal) values excluded (notAllocated position) subjectAbsent
    (by simpa using formalAbsent) accepted

/-- The native function-trial allocation policy discharges the solved-form
invariant: a parent codomain variable cannot become a proper subterm of
its returned refinement, however many recursive argument queries follow. -/
theorem recursive_codomain_solved_form (library : List Declaration) (fuel : Nat)
    (path : Path) (occurrence slot position : Nat)
    (pending : List (TypeTerm × TypeTerm)) (answers : List TypeTerm)
    (returned : arguments (run library freshSupply fuel) path position pending
      (.var (freshSupply (1 :: occurrence :: path) slot)) (Subst.id signature) =
        some answers) :
    ∀ answer ∈ answers,
      answer = .var (freshSupply (1 :: occurrence :: path) slot) ∨
      freshSupply (1 :: occurrence :: path) slot ∉ answer.freeVars := by
  rw [Resolution.arguments_id] at returned
  apply arguments_variable_solved_form _ path _ _ position pending answers returned
  intro childPosition subject formal values subjectAbsent formalAbsent accepted
  exact run_excludes_name library fuel (0 :: childPosition :: path) subject
    (some formal) values (freshSupply (1 :: occurrence :: path) slot)
    (fun stem childSlot => Ne.symm
      (function_name_ne_recursive_supply path stem occurrence slot childPosition childSlot))
    subjectAbsent (by simpa using formalAbsent) accepted

/-- Fresh inference through a whole argument sequence also keeps every
independent caller output absent. This is separate from the codomain
solved-form property and is needed to make the coordinate swap hygienic. -/
theorem recursive_arguments_excludes_caller (library : List Declaration) (fuel : Nat)
    (path : Path) (caller position : Nat) (pending : List (TypeTerm × TypeTerm))
    (result : TypeTerm)
    (pendingAbsent : ∀ pair ∈ pending,
      callerName caller ∉ pair.1.freeVars ∧ callerName caller ∉ pair.2.freeVars)
    (resultAbsent : callerName caller ∉ result.freeVars) (answers : List TypeTerm)
    (returned : arguments (run library freshSupply fuel) path position pending
      result (Subst.id signature) = some answers) :
    ∀ answer ∈ answers, callerName caller ∉ answer.freeVars := by
  rw [Resolution.arguments_id] at returned
  exact recursive_arguments_excludes_name library fuel path (callerName caller)
    (fun _ _ slot => fresh_supply_separate _ slot caller) position pending result
    pendingAbsent resultAbsent answers returned

private theorem arguments_eq_of_children_eq (left right : Query) (path : Path)
    (same : ∀ position subject formal,
      left (0 :: position :: path) subject formal =
        right (0 :: position :: path) subject formal)
    (position : Nat) (pending : List (TypeTerm × TypeTerm))
    (result : TypeTerm) (store : Subst signature) :
    arguments left path position pending result store =
      arguments right path position pending result store := by
  induction pending generalizing position store with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨subject, formal⟩
      simp only [arguments]
      by_cases rootVar : isVariable (store.applyTerm subject) = true
      · simp only [rootVar, ↓reduceIte]
        exact ih (position + 1) store
      · simp only [rootVar, Bool.false_eq_true, ↓reduceIte, same]
        cases right (0 :: position :: path) (store.applyTerm subject)
            (some (store.applyTerm formal)) with
        | none => rfl
        | some candidates =>
            dsimp only [bind, Option.bind]
            apply Coordinates.collect_congr
            intro candidate _
            cases unifyTotal [(candidate, store.applyTerm formal)] with
            | none => rfl
            | some refinement => exact ih (position + 1) (refinement ∘ₛ store)

/-- For a nonvariable codomain, the independently absent output has no
effect on the argument traversal at all. The initial matcher is executed
here, as in the bound function branch of `functions`. -/
theorem nonvariable_codomain_arguments (query : Query) (path : Path) (position : Nat)
    (pending : List (TypeTerm × TypeTerm)) (result : TypeTerm) (output : Nat)
    (proper : ∀ name, result ≠ .var name)
    (independent : ∀ pair ∈ pending, output ∉ pair.1.freeVars ∧ output ∉ pair.2.freeVars)
    (resultAbsent : output ∉ result.freeVars) :
    ((unifyTotal [(result, .var output)]).bind fun initial =>
      arguments query path position pending result initial) =
        arguments query path position pending result (Subst.id signature) := by
  rw [IndependentOutputUnification.nonvariable_output_match output result proper resultAbsent]
  simp only [Option.bind_some]
  rw [Resolution.arguments_eq_resolved, Resolution.arguments_id]
  have fixed : ∀ term : TypeTerm, output ∉ term.freeVars →
      (Subst.single output result).applyTerm term = term := by
    intro term absent
    apply Subst.applyTerm_eq_self
    intro name occurs
    exact Subst.single_ne result (fun same => absent (same ▸ occurs))
  rw [fixed result resultAbsent]
  congr 1
  conv_rhs => rw [← List.map_id pending]
  apply List.map_congr_left
  intro pair member
  exact Prod.ext (fixed pair.1 (independent pair member).1)
    (fixed pair.2 (independent pair member).2)

/-- For a variable codomain, aliasing the independent output before the
actual recursive argument service preserves every ordered projected answer
family. The result accounts for both unsolved aliases and arbitrarily deep
later refinements; incompleteness and duplicate occurrences are preserved.
The observations may include the output and all subject variables, but
cannot read the freshly activated private codomain name. The output may
also belong to an enclosing structural field, outside this invocation's
allocation subtree. -/
theorem recursive_variable_codomain_publication
    (library : List Declaration) (fuel : Nat) (path : Path)
    (occurrence slot output position : Nat)
    (notAllocated : ∀ stem freshSlot, freshSupply (stem ++ path) freshSlot ≠ output) (pending : List (TypeTerm × TypeTerm))
    (independent : ∀ pair ∈ pending,
      output ∉ pair.1.freeVars ∧ output ∉ pair.2.freeVars)
    (observations : List TypeTerm)
    (privateAbsent : ∀ term ∈ observations,
      freshSupply (1 :: occurrence :: path) slot ∉ term.freeVars) :
    let privateName := freshSupply (1 :: occurrence :: path) slot
    let project := fun answer =>
      IndependentOutputUnification.solutions [(answer, .var output)] observations
    (arguments (run library freshSupply fuel) path position pending (.var privateName)
        (Subst.single privateName (.var output))).map (List.map project) =
      (arguments (run library freshSupply fuel) path position pending (.var privateName)
        (Subst.id signature)).map (List.map project) := by
  dsimp only
  let privateName := freshSupply (1 :: occurrence :: path) slot
  let names := Equiv.swap privateName output
  have different : privateName ≠ output := notAllocated [1, occurrence] slot
  have resultAbsent : output ∉ (Term.var privateName : TypeTerm).freeVars := by
    simpa only [Term.freeVars, Finset.mem_singleton] using Ne.symm different
  have sameChildren : ∀ childPosition subject formal,
      run library (Coordinates.S names freshSupply) fuel (0 :: childPosition :: path)
          subject formal = run library freshSupply fuel (0 :: childPosition :: path)
            subject formal := by
    intro childPosition subject formal
    exact (run_eq_of_supply_suffix library freshSupply (Coordinates.S names freshSupply)
      fuel (0 :: childPosition :: path)
      (by
        intro stem freshSlot
        dsimp only [Coordinates.S]
        symm
        apply Equiv.swap_apply_of_ne_of_ne
        · exact Ne.symm (function_name_ne_recursive_supply path stem occurrence slot
            childPosition freshSlot)
        · simpa only [List.append_assoc, List.cons_append, List.nil_append] using
            notAllocated (stem ++ [0, childPosition]) freshSlot)
      subject formal).symm
  have comparison := Resolution.private_alias_arguments privateName output
    (run library freshSupply fuel) (run library (Coordinates.S names freshSupply) fuel)
    (Coordinates.run_equivariant names library freshSupply fuel)
    path position pending (.var privateName) independent resultAbsent
  rw [arguments_eq_of_children_eq _ _ path sameChildren] at comparison
  rw [comparison]
  cases returned : arguments (run library freshSupply fuel) path position pending
      (.var privateName) (Subst.id signature) with
  | none => rfl
  | some answers =>
      simp only [Option.map_some, Option.some.injEq, List.map_map]
      apply List.map_congr_left
      intro answer present
      exact IndependentOutputUnification.solved_private_output_publication
        privateName output different answer
        (recursive_codomain_solved_form library fuel path occurrence slot position
          pending answers returned answer present)
        (recursive_arguments_excludes_name library fuel path output
          (fun childPosition stem freshSlot => by
            simpa only [List.append_assoc, List.cons_append, List.nil_append] using
              notAllocated (stem ++ [0, childPosition]) freshSlot)
          position pending (.var privateName) independent resultAbsent answers
          (by simpa only [Resolution.arguments_id] using returned) answer present)
        observations privateAbsent

private theorem finish_unconstrained_nonempty (required : Option TypeTerm)
    (unconstrained : required = none ∨ ∃ name, required = some (.var name))
    (candidates : List TypeTerm) : finish required candidates ≠ [] := by
  unfold finish
  split
  · rcases unconstrained with rfl | ⟨name, rfl⟩
    · simp
    · have proper : ∀ variableName, IntrinsicTypeFacts.undefinedType ≠ .var variableName := by
        simp [IntrinsicTypeFacts.undefinedType, IntrinsicTypeFacts.named]
      have absent : name ∉ IntrinsicTypeFacts.undefinedType.freeVars := by
        simp [IntrinsicTypeFacts.undefinedType, IntrinsicTypeFacts.named, Term.freeVars]
      simp [matched, IndependentOutputUnification.nonvariable_output_match name
        IntrinsicTypeFacts.undefinedType proper absent]
  · simpa only [List.isEmpty_iff] using ‹¬candidates.isEmpty = true›

private theorem step_unconstrained_nonempty (library : List Declaration) (supply : Supply)
    (query : Query) (path : Path) (subject : TypeTerm) (required : Option TypeTerm)
    (unconstrained : required = none ∨ ∃ name, required = some (.var name))
    (answers : List TypeTerm)
    (returned : step library supply query path subject required = some answers) : answers ≠ [] := by
  unfold step at returned
  split at returned
  · simp only [Option.some.injEq] at returned
    subst answers
    simp
  · cases primitiveRun : literal subject with
    | some primitive =>
        simp only [primitiveRun] at returned
        split at returned
        · simp only [Option.some.injEq] at returned
          subst answers
          intro empty
          have nonempty := ‹(! (select required [primitive]).isEmpty) = true›
          simp [empty] at nonempty
        · simp only [Option.some.injEq] at returned
          subst answers
          exact finish_unconstrained_nonempty required unconstrained []
    | none =>
        simp only [primitiveRun] at returned
        cases parsed : elements subject with
        | none =>
            simp only [parsed, Option.some.injEq] at returned
            subst answers
            exact finish_unconstrained_nonempty required unconstrained _
        | some items =>
            simp only [parsed] at returned
            obtain ⟨functionAnswers, _, rest⟩ := Option.bind_eq_some_iff.mp returned
            obtain ⟨allFunctions, _, rest⟩ := Option.bind_eq_some_iff.mp rest
            obtain ⟨rowAnswers, _, final⟩ := Option.bind_eq_some_iff.mp rest
            have finalEq : finish required (functionAnswers ++ rowAnswers) = answers := Option.some.inj final
            rw [← finalEq]
            exact finish_unconstrained_nonempty required unconstrained _

/-- A completed fresh query always has an answer, including its explicit
Undefined fallback. This is not an assertion that every finite fuel
approximation completes. -/
theorem run_fresh_nonempty (library : List Declaration) (supply : Supply) (fuel : Nat)
    (path : Path) (subject : TypeTerm) (answers : List TypeTerm)
    (returned : run library supply fuel path subject none = some answers) : answers ≠ [] := by
  cases fuel with
  | zero => simp [run] at returned
  | succ fuel =>
      exact step_unconstrained_nonempty library supply (run library supply fuel)
        path subject none (Or.inl rfl) answers returned

/-- An unconstrained variable requirement also keeps normal completion
nonempty. Structural field traversal therefore cannot silently skip the
completion of later fields by receiving an empty child vector. -/
theorem run_variable_nonempty (library : List Declaration) (supply : Supply) (fuel : Nat)
    (path : Path) (subject : TypeTerm) (name : Nat) (answers : List TypeTerm)
    (returned : run library supply fuel path subject (some (.var name)) = some answers) : answers ≠ [] := by
  cases fuel with
  | zero => simp [run] at returned
  | succ fuel =>
      exact step_unconstrained_nonempty library supply (run library supply fuel)
        path subject (some (.var name)) (Or.inr ⟨name, rfl⟩) answers returned

private theorem declaration_result_variable_origin (library : List Declaration)
    (path : Path) (subject scheme : TypeTerm) (member : scheme ∈ declarations library freshSupply path subject)
    (arity : Nat) (domains : List TypeTerm) (name : Nat)
    (parsed : callParts arity scheme = some (domains, .var name)) :
    ∃ occurrence slot, name = freshSupply (1 :: occurrence :: path) slot := by
  by_contra missing
  push Not at missing
  have absent := declarations_exclude library freshSupply path subject name
    (fun occurrence slot => Ne.symm (missing occurrence slot)) scheme member
  have resultAbsent := (callParts_exclude scheme arity domains (.var name) name absent parsed).2
  exact resultAbsent (by simp [Term.freeVars])

/-- Whole ordered function dispatch preserves projected answer schemes
when its root requirement is independent. This includes every activated
signature, both codomain shapes, rejected argument trials, normal empty
completion and duplicate answers. Recursive services are the actual query. -/
theorem functions_variable_publication (library : List Declaration) (fuel : Nat)
    (path : Path) (items : List TypeTerm) (output : Nat)
    (notAllocated : ∀ stem slot, freshSupply (stem ++ path) slot ≠ output)
    (independent : ∀ item ∈ items, output ∉ item.freeVars)
    (observations : List TypeTerm)
    (privateAbsent : ∀ occurrence slot term, term ∈ observations →
      freshSupply (1 :: occurrence :: path) slot ∉ term.freeVars) :
    let project := fun answer =>
      IndependentOutputUnification.solutions [(answer, .var output)] observations
    (functions library freshSupply (run library freshSupply fuel) path items
      (some (.var output))).map (List.map project) =
    (functions library freshSupply (run library freshSupply fuel) path items none).map
      (List.map project) := by
  dsimp only
  cases items with
  | nil => rfl
  | cons head actuals =>
      simp only [functions, ← Coordinates.collect_results]
      apply Coordinates.collect_congr
      intro scheme member
      cases parsed : callParts actuals.length scheme with
      | none => rfl
      | some pair =>
          rcases pair with ⟨domains, result⟩
          dsimp only
          have schemeAbsent := declarations_exclude library freshSupply path head output
            (fun occurrence slot => notAllocated [1, occurrence] slot) scheme member
          have partsAbsent := callParts_exclude scheme actuals.length domains result output
            schemeAbsent parsed
          have pendingAbsent : ∀ pair ∈ actuals.zip domains,
              output ∉ pair.1.freeVars ∧ output ∉ pair.2.freeVars := by
            intro pair present
            obtain ⟨actual, domain⟩ := List.of_mem_zip present
            exact ⟨independent pair.1 (List.mem_cons_of_mem _ actual), partsAbsent.1 pair.2 domain⟩
          cases result with
          | var name =>
              obtain ⟨occurrence, slot, rfl⟩ := declaration_result_variable_origin
                library path head scheme member actuals.length domains name parsed
              have different : freshSupply (1 :: occurrence :: path) slot ≠ output :=
                notAllocated [1, occurrence] slot
              simp only [IndependentOutputUnification.variable_output_match
                (σ := signature) _ _ different]
              exact recursive_variable_codomain_publication library fuel path occurrence slot output 0
                notAllocated (actuals.zip domains) pendingAbsent observations
                (fun term present => privateAbsent occurrence slot term present)
          | const value =>
              have proper : ∀ name, (Term.const value : TypeTerm) ≠ .var name := by simp
              have same := nonvariable_codomain_arguments (run library freshSupply fuel) path 0
                (actuals.zip domains) (.const value) output proper pendingAbsent partsAbsent.2
              rw [IndependentOutputUnification.nonvariable_output_match output (.const value)
                proper partsAbsent.2] at same ⊢
              simp only [Option.bind_some] at same
              dsimp only
              rw [same]
          | app arity children =>
              have proper : ∀ name, (Term.app arity children : TypeTerm) ≠ .var name := by simp
              have same := nonvariable_codomain_arguments (run library freshSupply fuel) path 0
                (actuals.zip domains) (.app arity children) output proper pendingAbsent partsAbsent.2
              rw [IndependentOutputUnification.nonvariable_output_match output (.app arity children)
                proper partsAbsent.2] at same ⊢
              simp only [Option.bind_some] at same
              dsimp only
              rw [same]

namespace Controls

def openRow : TypeTerm := row [.var (callerName 0)]

theorem fresh_row_variable_name :
    run [] freshSupply 2 [] openRow none =
      some [row [.var (freshSupply [5, 0, 0, 4] 0)]] := by
  simp [run, step, expression, functions, declarations, structural, freshRows,
    collect, allowsRow, finish, isVariable, literal, elements, openRow,
    row, Subst.id]

theorem bound_row_variable_name :
    run [] freshSupply 2 [] openRow (some (.var (callerName 1))) =
      some [row [.var (freshSupply [3] 0)]] := by
  simp [run, step, expression, functions, declarations, structural,
    arguments, collect, allowsRow, finish, isVariable, literal, elements, openRow,
    row, Subst.id, Subst.applyTerm, unifyTotal, Subst.applyEqs,
    Subst.comp, Subst.single, Term.occursIn, freshSupply, callerName]
  rfl

/-- Traversal fuel is an implementation approximation, not a shared cost
metric: fresh rows query a variable child, whereas bound rows skip it. -/
theorem equal_fuel_does_not_preserve_completion :
    run [] freshSupply 1 [] openRow none = none ∧
    run [] freshSupply 1 [] openRow (some (.var (callerName 1))) =
      some [row [.var (freshSupply [3] 0)]] := by
  constructor
  · simp [run, step, expression, functions, declarations, structural, freshRows,
      collect, allowsRow, isVariable, literal, elements, openRow, row, Subst.id]
  · simp [run, step, expression, functions, declarations, structural,
      arguments, collect, allowsRow, finish, isVariable, literal, elements, openRow,
      row, Subst.id, Subst.applyTerm, unifyTotal, Subst.applyEqs,
      Subst.comp, Subst.single, Term.occursIn, freshSupply, callerName]
    rfl

/-- Structural inference and checking use different private coordinates. -/
theorem raw_structural_answers_differ :
    run [] freshSupply 2 [] openRow none ≠
      run [] freshSupply 2 [] openRow (some (.var (callerName 1))) := by
  rw [fresh_row_variable_name, bound_row_variable_name]
  intro same
  have terms := (List.cons.inj (Option.some.inj same)).1
  have children := congrArg elements terms
  have names : freshSupply [5, 0, 0, 4] 0 = freshSupply [3] 0 := by
    simpa [elements, row] using children
  simp [fresh_supply_injective] at names

/-- The two structural answers differ only in a private coordinate; every
caller name remains fixed by this renaming. -/
theorem structural_row_private_renaming :
    let names := Equiv.swap (freshSupply [3] 0) (freshSupply [5, 0, 0, 4] 0)
    (∀ caller, names (callerName caller) = callerName caller) ∧
    (run [] freshSupply 2 [] openRow (some (.var (callerName 1)))).map
      (List.map (Coordinates.R names)) = run [] freshSupply 2 [] openRow none := by
  dsimp only
  constructor
  · intro caller
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm (fresh_supply_separate _ _ _))
      (Ne.symm (fresh_supply_separate _ _ _))
  · rw [bound_row_variable_name, fresh_row_variable_name]
    simp only [Option.map_some, List.map_cons, List.map_nil, Coordinates.row_rename,
      rename_var, Equiv.swap_apply_left]

/-- This subject deliberately captures the first structural field's name.
A native invocation must allocate its fields outside the source namespace. -/
def collidingSubject : TypeTerm :=
  row [.const (.number "7"), .var (freshSupply [3] 0)]

theorem fresh_colliding_subject :
    run [] freshSupply 2 [] collidingSubject none =
      some [row [IntrinsicTypeFacts.named "Number", .var (freshSupply [5, 0, 1, 4] 0)]] := by
  simp [run, step, expression, functions, structural, freshRows, collect, declarations,
    callParts, parts, isArrow, elements, literal, isVariable, select, finish, allowsRow,
    collidingSubject, row, IntrinsicTypeFacts.named, Subst.id, freshSupply,
    IntrinsicTypeFacts.primitiveType]

/-- With captured allocation, checking the first field changes the second
subject before it is queried. Independent output alone is insufficient. -/
theorem bound_colliding_subject :
    run [] freshSupply 2 [] collidingSubject (some (.var (callerName 0))) =
      some [row [IntrinsicTypeFacts.named "Number", IntrinsicTypeFacts.undefinedType]] := by
  have initial : unifyTotal [(row [.var 33125, .var 33490], (.var 0 : TypeTerm))] =
      some (Subst.single (σ := signature) 0 (row [.var 33125, .var 33490])) := by
    apply IndependentOutputUnification.nonvariable_output_match
    · intro name same
      cases same
    · simp [row, Term.freeVars, Fin.exists_fin_two]
  have structuralRun : structural freshSupply (run [] freshSupply 1) []
      [.const (.number "7"), .var 33125] (some (.var 0)) =
        some [row [IntrinsicTypeFacts.named "Number", IntrinsicTypeFacts.undefinedType]] := by
    unfold structural
    change (match unifyTotal [(row [.var 33125, .var 33490], (.var 0 : TypeTerm))] with
      | none => some []
      | some theta => arguments (run [] freshSupply 1) [4] 0
        [(.const (.number "7"), .var 33125), (.var 33125, .var 33490)]
        (row [.var 33125, .var 33490]) theta) = _
    rw [initial]
    simp [arguments, run, step, isVariable, literal, IntrinsicTypeFacts.primitiveType,
      select, matched, unifyTotal, Subst.applyEqs, Subst.single, Subst.comp,
      Subst.applyTerm, Subst.id, row, collect, finish, IntrinsicTypeFacts.named,
      IntrinsicTypeFacts.undefinedType, elements, declarations]
    funext i
    fin_cases i <;> rfl
  change (structural freshSupply (run [] freshSupply 1) []
      [.const (.number "7"), .var 33125] (some (.var 0))).bind
    (fun answers => some (finish (some (.var 0)) answers)) = _
  rw [structuralRun]
  rfl

def unresolvedStore : Subst signature := fun name =>
  if name = 0 then IntrinsicTypeFacts.named "Number"
  else if name = 1 then .var 0 else .var name

/-- Reading an unnormalized store once can reintroduce a solved name.
The idempotence premise is essential, even without recursive allocation. -/
theorem solved_entry_alone_is_insufficient :
    unresolvedStore 0 ≠ .var 0 ∧
      0 ∈ (unresolvedStore.applyTerm (.var 1)).freeVars := by
  simp [unresolvedStore, Subst.applyTerm, IntrinsicTypeFacts.named, Term.freeVars]

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutput.Admission
