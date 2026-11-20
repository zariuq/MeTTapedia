import Mettapedia.OSLF.MeTTaIL.ReflectiveCoherentSubstitution

/-!
# Binder-eliminating reflective instantiation

This operation is parameterized by the existing reflective declaration. Like
reflective substitution, it first resolves every quotation of a drop and then
substitutes structurally: it retains literal quotation, runs a received
quotation at a drop of the selected name, and substitutes through every other
drop. It additionally eliminates the received binder and lifts an open
replacement under intervening binders.

The ambient and closed interpreters share the resolution and the whole-name
test. Only ambient instantiation removes a binder level and lifts the payload.
Ordinary scope and admission as a sealed literal quotation remain distinct.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation

open Syntax Reflection Substitution ScopedPattern ReflectiveSubstitution ReflectiveCanonical
open ReflectiveCoherent

/-- Static quote/drop normalization introduces no dangling bound index. -/
theorem normalizeReflective_scoped (declaration : ReflectivePresentationDecl)
    {pattern : Pattern} {ambient : Nat}
    (safe : pattern.isWellScopedAt ambient = true) :
    (normalizeReflective declaration pattern).isWellScopedAt ambient = true := by
  induction pattern using Pattern.inductionOn generalizing ambient with
  | hbvar index => exact safe
  | hfvar name => rfl
  | happly constructor arguments ih =>
      have each : ∀ p ∈ arguments,
          (normalizeReflective declaration p).isWellScopedAt ambient = true := by
        intro p member
        exact ih p member ((isWellScopedListAt_eq_true_iff _ _).mp safe p member)
      have listSafe : Pattern.isWellScopedListAt ambient
          (normalizeReflectiveList declaration arguments) = true := by
        rw [normalizeReflectiveList_eq_map, isWellScopedListAt_eq_true_iff]
        intro p member
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        exact each original originalMember
      exact finishNormalizeReflectiveApply_scoped declaration constructor listSafe
  | hlambda binder body ih => exact ih safe
  | hmultiLambda arity binders body ih => exact ih safe
  | hsubst body replacement ihBody ihReplacement =>
      simp only [normalizeReflective, Pattern.isWellScopedAt, Bool.and_eq_true] at safe ⊢
      exact ⟨ihBody safe.1, ihReplacement safe.2⟩
  | hcollection kind elements rest ih =>
      change Pattern.isWellScopedListAt ambient (normalizeReflectiveList declaration elements) = true
      have each := (isWellScopedListAt_eq_true_iff _ _).mp safe
      rw [normalizeReflectiveList_eq_map, isWellScopedListAt_eq_true_iff]
      intro p member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact ih original originalMember (each original originalMember)

/-- Neither the direct nor the structural test mistakes closed code for a
reference to an ambient binder. -/
theorem matchesBinder_closed (declaration : ReflectivePresentationDecl)
    (depth : Nat) {name : Pattern} (closed : name.isWellScopedAt 0 = true) :
    matchesBinder declaration depth (normalizeReflective declaration name) = false := by
  simp only [matchesBinder, decide_eq_false_iff_not, BinderHead.ofPattern_index_iff]
  intro equality
  have safe := canonicalize_scoped declaration (normalizeReflective_scoped declaration closed)
  simp [equality, Pattern.isWellScopedAt] at safe

/-- Eliminate one binder with the declared reflective activation behavior. -/
def instantiate (declaration : ReflectivePresentationDecl)
    (depth : Nat) (replacement body : Pattern) : Pattern :=
  substituteResolved declaration
    (fun level index => instantiateBVarAt level replacement (.bvar index)) depth
    (resolveQuotes declaration body)

/-- Pointwise `instantiate`. -/
def instantiateList (declaration : ReflectivePresentationDecl)
    (depth : Nat) (replacement : Pattern) (patterns : List Pattern) : List Pattern :=
  patterns.map (instantiate declaration depth replacement)

/-- The Boolean records substitution of the selected whole name. Lowering
an ambient index does not confer substituted-quote provenance. -/
def nameMark (declaration : ReflectivePresentationDecl)
    (depth : Nat) (replacement name : Pattern) : Pattern × Bool :=
  if matchesBinder declaration depth (resolveQuotes declaration name) then
    (instantiateBVarAt depth replacement (.bvar depth), true)
  else
    (instantiate declaration depth replacement name, false)

@[simp] theorem nameMark_bvar (declaration : ReflectivePresentationDecl)
    (depth : Nat) (replacement : Pattern) (level : Nat) :
    nameMark declaration depth replacement (.bvar level) =
      (instantiateBVarAt depth replacement (.bvar level), level == depth) := by
  by_cases hit : level = depth
  · subst hit; simp [nameMark, resolveQuotes]
  · simp [nameMark, resolveQuotes, instantiate, substituteResolved, hit]

@[simp] theorem nameMark_fvar (declaration : ReflectivePresentationDecl)
    (depth : Nat) (replacement : Pattern) (name : String) :
    nameMark declaration depth replacement (.fvar name) = (.fvar name, false) := rfl

/-- Closed code is never the selected binder; its mark keeps the resolved
spelling. -/
theorem substituteNameMark_closed (declaration : ReflectivePresentationDecl)
    (depth : Nat) (replacement : Pattern) {name : Pattern}
    (closed : name.isWellScopedAt 0 = true) :
    substituteNameMark declaration depth replacement name =
      (resolveQuotes declaration name, false) := by
  have resolvedClosed := resolveQuotes_isWellScopedAt (declaration := declaration) closed
  have miss : matchesBinder declaration depth (resolveQuotes declaration name) = false := by
    simp only [matchesBinder, decide_eq_false_iff_not, BinderHead.ofPattern_index_iff]
    intro equality
    have safe := canonicalize_scoped declaration resolvedClosed
    simp [equality, Pattern.isWellScopedAt] at safe
  simp only [substituteNameMark, miss, Bool.false_eq_true, if_false, substituteReflective]
  rw [substituteResolved_of_isWellScopedAt _ (fun level index below => by simp [Nat.ne_of_lt below])
    (isWellScopedAt_mono resolvedClosed (Nat.zero_le _))]

/-- On the established closed domain, binder elimination and replacement
lifting are vacuous. The full operations agree, including whether a dropped
quotation was supplied by this substitution or occurred literally in code. -/
theorem closed_agreement (declaration : ReflectivePresentationDecl)
    {depth : Nat} {body replacement : Pattern}
    (bodySafe : body.isWellScopedAt (depth + 1) = true)
    (replacementSafe : replacement.isWellScopedAt 0 = true) :
    instantiate declaration depth replacement body =
      substituteReflective declaration depth replacement body := by
  unfold instantiate substituteReflective
  apply substituteResolved_congr _ (resolveQuotes_isWellScopedAt bodySafe)
  intro level index _ below
  rcases Nat.lt_or_eq_of_le below with below | rfl
  · simp [instantiateBVarAt, below, Nat.ne_of_lt below]
  · simp [instantiateBVarAt, liftBVars_eq_self_of_isWellScopedAt replacementSafe]

theorem nameMark_closed_agreement (declaration : ReflectivePresentationDecl)
    {depth : Nat} {name replacement : Pattern}
    (nameSafe : name.isWellScopedAt (depth + 1) = true)
    (replacementSafe : replacement.isWellScopedAt 0 = true) :
    nameMark declaration depth replacement name =
      substituteNameMark declaration depth replacement name := by
  unfold nameMark substituteNameMark
  split
  · simp [instantiateBVarAt, liftBVars_eq_self_of_isWellScopedAt replacementSafe]
  · rw [closed_agreement declaration nameSafe replacementSafe]

/-- The source's stronger quotation-sealing premises imply the preceding
comparison without identifying quotation admission with ordinary scope. -/
theorem binderSafe_closed_agreement (declaration : ReflectivePresentationDecl)
    {depth : Nat} {body replacement : Pattern}
    (bodySafe : binderSafeAt declaration.quoteConstructor (depth + 1) body = true)
    (replacementSafe : binderSafeAt declaration.quoteConstructor 0 replacement = true) :
    instantiate declaration depth replacement body =
      substituteReflective declaration depth replacement body :=
  closed_agreement declaration
    (isWellScopedAt_of_binderSafeAt _ bodySafe)
    (isWellScopedAt_of_binderSafeAt _ replacementSafe)

/-- **Instantiation respects the declared equations.** -/
theorem canonicalize_instantiate (declaration : ReflectivePresentationDecl)
    (depth : Nat) (replacement body : Pattern) :
    canonicalize declaration (instantiate declaration depth replacement body) =
      canonicalize declaration (substituteResolved declaration
        (fun level index => instantiateBVarAt level replacement (.bvar index)) depth
        (canonicalize declaration body)) :=
  canonicalize_substituteResolved_resolveQuotes _ _ _

theorem instantiate_respects (declaration : ReflectivePresentationDecl)
    (depth : Nat) (replacement : Pattern) {left right : Pattern}
    (same : canonicalEquivalent declaration left right = true) :
    canonicalEquivalent declaration (instantiate declaration depth replacement left)
      (instantiate declaration depth replacement right) = true := by
  rw [canonicalEquivalent_eq_true_iff] at same ⊢
  rw [canonicalize_instantiate, canonicalize_instantiate, same]

/-- **Binder elimination a presentation declares.** Under a closed quote scope it
is `instantiate`; under a reaching scope a genuine quotation is entered with the
declared view. -/
def instantiateDeclared (declaration : ReflectivePresentationDecl)
    (depth : Nat) (replacement body : Pattern) : Pattern :=
  substituteScoped declaration declaration.quoteScope
    (fun level index => instantiateBVarAt level replacement (.bvar index)) depth body

@[simp] theorem instantiateDeclared_of_closed {declaration : ReflectivePresentationDecl}
    (closed : declaration.quoteScope = .closed) (depth : Nat) (replacement body : Pattern) :
    instantiateDeclared declaration depth replacement body =
      instantiate declaration depth replacement body := by
  simp only [instantiateDeclared, closed, substituteScoped, instantiate]

/-- **Declared binder elimination respects the declared equations.** -/
theorem instantiateDeclared_respects (declaration : ReflectivePresentationDecl)
    (depth : Nat) (replacement : Pattern) {left right : Pattern}
    (same : canonicalEquivalent declaration left right = true) :
    canonicalEquivalent declaration (instantiateDeclared declaration depth replacement left)
      (instantiateDeclared declaration depth replacement right) = true :=
  ReflectiveCoherent.substituteScoped_respects declaration.quoteScope _ depth same

/-- A name compared atomically by the reflected operation is either a
variable or sealed code. An untyped compound such as `F(bound 0)` does not
satisfy this test. Declaration-derived rho names have precisely these forms. -/
def atomicOrClosed (declaration : ReflectivePresentationDecl) (name : Pattern) : Bool :=
  match normalizeReflective declaration name with
  | .bvar _ => true
  | other => other.isWellScopedAt 0

mutual
  /-- Check the forms of names inspected by operational Drop. Literal quotes
  are opaque; ordinary constructors, including generated apparatus, recurse. -/
  def namesAdmitted (declaration : ReflectivePresentationDecl) : Pattern → Bool
    | .bvar _ | .fvar _ => true
    | .apply constructor [payload] =>
        if constructor == declaration.quoteConstructor then true
        else if constructor == declaration.dropConstructor then atomicOrClosed declaration payload
        else namesAdmitted declaration payload
    | .apply _ arguments => namesAdmittedList declaration arguments
    | .lambda _ body | .multiLambda _ _ body => namesAdmitted declaration body
    | .subst body replacement => namesAdmitted declaration body && namesAdmitted declaration replacement
    | .collection _ elements _ => namesAdmittedList declaration elements

  def namesAdmittedList (declaration : ReflectivePresentationDecl) : List Pattern → Bool
    | [] => true
    | head :: tail => namesAdmitted declaration head && namesAdmittedList declaration tail
end

private theorem namesAdmittedList_iff (declaration : ReflectivePresentationDecl)
    (patterns : List Pattern) : namesAdmittedList declaration patterns = true ↔
      ∀ p ∈ patterns, namesAdmitted declaration p = true := by
  induction patterns with
  | nil => simp [namesAdmittedList]
  | cons head tail ih => simp [namesAdmittedList, ih]

theorem binderSafeAt_of_mem_parallelLeaves (declaration : ReflectivePresentationDecl)
    {pattern member : Pattern} {depth : Nat}
    (safe : binderSafeAt declaration.quoteConstructor depth pattern = true)
    (membership : member ∈ parallelLeaves declaration pattern) :
    binderSafeAt declaration.quoteConstructor depth member = true := by
  induction pattern using Pattern.inductionOn with
  | hcollection kind elements rest ih =>
      cases rest with
      | some rest =>
          simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact safe
      | none =>
          by_cases parallel : kind = declaration.parallelCollection
          · simp only [parallelLeaves, parallel, if_true, parallelLeavesList_eq_flatMap,
              List.mem_flatMap] at membership
            obtain ⟨element, elementMember, membership⟩ := membership
            exact ih element elementMember
              ((binderSafeListAt_eq_true_iff _ _ _).mp safe element elementMember) membership
          · simp only [parallelLeaves, parallel, if_false, List.mem_singleton] at membership
            subst membership; exact safe
  | happly constructor arguments ih =>
      cases arguments with
      | nil =>
          by_cases unit : constructor = declaration.parallelUnitConstructor
          · simp [parallelLeaves, unit] at membership
          · simp only [parallelLeaves, unit, if_false, List.mem_singleton] at membership
            subst membership; exact safe
      | cons argument arguments =>
          simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact safe
  | hbvar index => simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact safe
  | hfvar name => simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact safe
  | hlambda binder body ih =>
      simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact safe
  | hmultiLambda arity binders body ih =>
      simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact safe
  | hsubst body replacement ihBody ihReplacement =>
      simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact safe

private theorem binderSafeAt_unary (quoteConstructor constructor : String) (depth : Nat)
    (payload : Pattern) :
    binderSafeAt quoteConstructor depth (.apply constructor [payload]) =
      if constructor = quoteConstructor then binderSafeAt quoteConstructor 0 payload
      else binderSafeAt quoteConstructor depth payload := by
  by_cases quoted : constructor = quoteConstructor
  · simp [binderSafeAt, quoted]
  · simp [binderSafeAt, quoted, binderSafeListAt]

/-- Resolving quotations keeps quotation-sealed scope. -/
theorem resolveQuotes_binderSafeAt (declaration : ReflectivePresentationDecl)
    {pattern : Pattern} {depth : Nat}
    (safe : binderSafeAt declaration.quoteConstructor depth pattern = true) :
    binderSafeAt declaration.quoteConstructor depth (resolveQuotes declaration pattern) = true := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index => exact safe
  | hfvar name => rfl
  | hlambda binder body ih => exact ih safe
  | hmultiLambda arity binders body ih => exact ih safe
  | hsubst body replacement ihBody ihReplacement =>
      simp only [binderSafeAt, Bool.and_eq_true, resolveQuotes] at safe ⊢
      exact ⟨ihBody safe.1, ihReplacement safe.2⟩
  | hcollection kind elements rest ih =>
      have each := (binderSafeListAt_eq_true_iff _ _ _).mp safe
      show binderSafeListAt declaration.quoteConstructor depth
        (resolveQuotesList declaration elements) = true
      rw [resolveQuotesList_eq_map, binderSafeListAt_eq_true_iff]
      intro p member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact ih original originalMember (each original originalMember)
  | happly constructor arguments ih =>
      simp only [resolveQuotes, resolveQuotesList_eq_map]
      match arguments, safe, ih with
      | [], _, _ => rfl
      | first :: second :: rest, safe, ih =>
          have each := (binderSafeListAt_eq_true_iff _ _ _).mp (by simpa [binderSafeAt] using safe)
          show binderSafeListAt declaration.quoteConstructor depth
            ((first :: second :: rest).map (resolveQuotes declaration)) = true
          rw [binderSafeListAt_eq_true_iff]
          intro p member
          obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
          exact ih original originalMember (each original originalMember)
      | [payload], safe, ih =>
          rw [binderSafeAt_unary] at safe
          simp only [List.map_cons, List.map_nil, finishResolveApply]
          by_cases quoted : constructor = declaration.quoteConstructor
          · simp only [quoted, if_true] at safe ⊢
            have payloadSafe := ih payload (by simp) safe
            split
            · rename_i name exposed
              have dropSafe := binderSafeAt_of_mem_parallelLeaves declaration payloadSafe
                (by rw [exposedDrop?_eq_some_iff.mp exposed]; exact List.mem_singleton_self _)
              rw [binderSafeAt_unary] at dropSafe
              have nameSafe : binderSafeAt declaration.quoteConstructor 0 name = true := by
                split at dropSafe
                · exact dropSafe
                · exact dropSafe
              exact binderSafeAt_mono _ nameSafe (Nat.zero_le _)
            · rw [binderSafeAt_unary, if_pos rfl]; exact payloadSafe
          · simp only [quoted, if_false] at safe ⊢
            rw [binderSafeAt_unary, if_neg quoted]
            exact ih payload (by simp) safe

/-- Open instantiation preserves ordinary scope when literal source quotes are
sealed. The name-admission premise is not used: every drop either receives
the selected name or is substituted through. The resulting name of an open
payload need not itself be a sealed literal quotation. -/
theorem instantiate_scoped (declaration : ReflectivePresentationDecl)
    {ambient depth : Nat} {body replacement : Pattern}
    (bodySafe : binderSafeAt declaration.quoteConstructor (ambient + depth + 1) body = true)
    (_names : namesAdmitted declaration body = true)
    (replacementSafe : replacement.isWellScopedAt ambient = true) :
    (instantiate declaration depth replacement body).isWellScopedAt (ambient + depth) = true := by
  unfold instantiate
  have resolvedSafe := resolveQuotes_binderSafeAt declaration bodySafe
  generalize resolveQuotes declaration body = resolved at resolvedSafe
  clear _names bodySafe body
  induction resolved using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      exact instantiateBVarAt_isWellScopedAt resolvedSafe replacementSafe
  | hfvar name => rfl
  | hlambda binder body ih =>
      have bodySafe' : binderSafeAt declaration.quoteConstructor (ambient + (depth + 1) + 1) body = true := by
        simpa [binderSafeAt, Nat.add_assoc] using resolvedSafe
      simpa [substituteResolved, Pattern.isWellScopedAt, Nat.add_assoc] using ih bodySafe'
  | hmultiLambda arity binders body ih =>
      have bodySafe' : binderSafeAt declaration.quoteConstructor (ambient + (depth + arity) + 1) body = true := by
        simpa [binderSafeAt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using resolvedSafe
      simpa [substituteResolved, Pattern.isWellScopedAt, Nat.add_assoc] using ih bodySafe'
  | hsubst body value ihBody ihValue =>
      simp only [binderSafeAt, Bool.and_eq_true] at resolvedSafe
      simp only [substituteResolved, Pattern.isWellScopedAt, Bool.and_eq_true]
      refine ⟨?_, ihValue resolvedSafe.2⟩
      simpa [Nat.add_assoc] using ihBody (depth := depth + 1)
        (by simpa [Nat.add_assoc] using resolvedSafe.1)
  | hcollection kind elements rest ih =>
      have each := (binderSafeListAt_eq_true_iff _ _ _).mp resolvedSafe
      show Pattern.isWellScopedListAt (ambient + depth)
        (substituteResolvedList declaration _ depth elements) = true
      rw [substituteResolvedList_eq_map, isWellScopedListAt_eq_true_iff]
      intro p member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact ih original originalMember (each original originalMember)
  | happly constructor arguments ih =>
      match arguments, resolvedSafe, ih with
      | [], _, _ => rfl
      | first :: second :: rest, resolvedSafe, ih =>
          have each := (binderSafeListAt_eq_true_iff _ _ _).mp (by simpa [binderSafeAt] using resolvedSafe)
          show Pattern.isWellScopedListAt (ambient + depth)
            (substituteResolvedList declaration _ depth (first :: second :: rest)) = true
          rw [substituteResolvedList_eq_map, isWellScopedListAt_eq_true_iff]
          intro p member
          obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
          exact ih original originalMember (each original originalMember)
      | [payload], resolvedSafe, ih =>
          rw [binderSafeAt_unary] at resolvedSafe
          by_cases quoted : constructor = declaration.quoteConstructor
          · simp only [quoted, if_true] at resolvedSafe
            simp only [substituteResolved, quoted, if_true]
            have closed := isWellScopedAt_of_binderSafeAt _ resolvedSafe
            simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using
              isWellScopedAt_mono closed (Nat.zero_le (ambient + depth))
          · simp only [quoted, if_false] at resolvedSafe
            have received : (instantiateBVarAt depth replacement (.bvar depth)).isWellScopedAt
                (ambient + depth) = true :=
              instantiateBVarAt_isWellScopedAt (by simp [Pattern.isWellScopedAt]; omega) replacementSafe
            have through : (Pattern.apply constructor [substituteResolved declaration
                (fun level index => instantiateBVarAt level replacement (.bvar index)) depth
                payload]).isWellScopedAt (ambient + depth) = true := by
              simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using
                ih payload (by simp) resolvedSafe
            simp only [substituteResolved, quoted, if_false]
            split
            · split
              · rcases receive_cases (declaration := declaration) constructor
                    (instantiateBVarAt depth replacement (.bvar depth)) with plain | ⟨process, shaped, ran⟩
                · rw [plain]
                  simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using received
                · rw [ran]
                  rw [shaped] at received
                  simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using received
              · exact through
            · exact through

#print axioms closed_agreement
#print axioms instantiate_scoped
#print axioms instantiate_respects

end Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation

/-! ## Free-name coverage of the operations -/

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Reflection
open ReflectiveSubstitution
open Substitution

private theorem substituteResolved_free_within (footprint : List String)
    (declaration : ReflectivePresentationDecl) (depth : Nat) (replacement body : Pattern)
    (inserted : ∀ free ∈ replacement.freeFvarNames, free ∈ footprint)
    (original : ∀ free ∈ body.freeFvarNames, free ∈ footprint) :
    ∀ free ∈ (substituteResolved declaration
      (fun level index => instantiateBVarAt level replacement (.bvar index)) depth body).freeFvarNames,
      free ∈ footprint := by
  induction body using Pattern.inductionOn generalizing depth with
  | hbvar index => exact instantiate_bvar_at_free_within footprint depth replacement (.bvar index) inserted original
  | hfvar name => exact original
  | hlambda binder body ih =>
      simp only [substituteResolved, Pattern.freeFvarNames] at original ⊢
      exact ih _ original
  | hmultiLambda arity binders body ih =>
      simp only [substituteResolved, Pattern.freeFvarNames] at original ⊢
      exact ih _ original
  | hsubst body value ihBody ihValue =>
      simp only [substituteResolved, Pattern.freeFvarNames] at original ⊢
      intro free occurs
      rcases List.mem_append.mp occurs with occurs | occurs
      · exact ihBody _ (fun name member => original name (List.mem_append_left _ member)) free occurs
      · exact ihValue _ (fun name member => original name (List.mem_append_right _ member)) free occurs
  | hcollection kind elements rest ih =>
      simp only [substituteResolved, substituteResolvedList_eq_map, Pattern.freeFvarNames,
        List.flatMap_map] at original ⊢
      intro free occurs
      rcases List.mem_append.mp occurs with occurs | occurs
      · rcases List.mem_flatMap.mp occurs with ⟨element, member, occurs⟩
        exact ih element member depth
          (fun name present => original name (List.mem_append_left _
            (List.mem_flatMap.mpr ⟨element, member, present⟩))) free occurs
      · exact original free (List.mem_append_right _ occurs)
  | happly constructor arguments ih =>
      have each : ∀ argument ∈ arguments, ∀ free ∈ argument.freeFvarNames, free ∈ footprint := by
        intro argument member free occurs
        apply original free
        simpa only [Pattern.freeFvarNames] using List.mem_flatMap.mpr ⟨argument, member, occurs⟩
      match arguments, each, ih with
      | [], _, _ => intro free occurs; simp [substituteResolved, Pattern.freeFvarNames] at occurs
      | first :: second :: rest, each, ih =>
          intro free occurs
          simp only [substituteResolved, substituteResolvedList_eq_map, Pattern.freeFvarNames,
            List.flatMap_map, List.mem_flatMap] at occurs
          obtain ⟨argument, member, occurs⟩ := occurs
          exact ih argument member depth (each argument member) free occurs
      | [payload], each, ih =>
          have payloadWithin := each payload (by simp)
          have through : ∀ free ∈ (Pattern.apply constructor [substituteResolved declaration
              (fun level index => instantiateBVarAt level replacement (.bvar index)) depth
              payload]).freeFvarNames, free ∈ footprint := by
            simpa [Pattern.freeFvarNames] using ih payload (by simp) depth payloadWithin
          have received := instantiate_bvar_at_free_within footprint depth replacement (.bvar depth)
            inserted (by simp [Pattern.freeFvarNames])
          simp only [substituteResolved]
          split
          · simpa [Pattern.freeFvarNames] using payloadWithin
          · split
            · split
              · rcases ReflectiveCoherent.receive_cases (declaration := declaration) constructor
                    (instantiateBVarAt depth replacement (.bvar depth)) with plain | ⟨process, shaped, ran⟩
                · rw [plain]
                  simpa [Pattern.freeFvarNames] using received
                · rw [ran]
                  rw [shaped] at received
                  simpa [Pattern.freeFvarNames] using received
              · exact through
            · exact through

theorem reflective_instantiate_free_within (footprint : List String)
    (declaration : ReflectivePresentationDecl) (depth : Nat) (replacement body : Pattern)
    (inserted : ∀ free ∈ replacement.freeFvarNames, free ∈ footprint)
    (original : ∀ free ∈ body.freeFvarNames, free ∈ footprint) :
    ∀ free ∈ (ReflectiveInstantiation.instantiate declaration depth replacement body).freeFvarNames,
      free ∈ footprint :=
  substituteResolved_free_within footprint declaration depth replacement _ inserted
    (fun free occurs => original free (resolve_quotes_free_names declaration body free occurs))

private theorem receive_free_within (footprint : List String) (declaration : ReflectivePresentationDecl)
    (constructor : String) {name : Pattern} (within : ∀ free ∈ name.freeFvarNames, free ∈ footprint) :
    ∀ free ∈ (receive declaration constructor name).freeFvarNames, free ∈ footprint := by
  rcases ReflectiveCoherent.receive_cases (declaration := declaration) constructor name with
    plain | ⟨process, shaped, ran⟩
  · rw [plain]; simpa [Pattern.freeFvarNames] using within
  · rw [ran]; rw [shaped] at within; simpa [Pattern.freeFvarNames] using within

/-- Substitution with actions whose values stay within a footprint stays within
it, at every quote scope. -/
private theorem substituteViewed_free_within (footprint : List String)
    (declaration : ReflectivePresentationDecl) {inside : Nat → Nat → Pattern}
    (insideWithin : ∀ level index, ∀ free ∈ (inside level index).freeFvarNames, free ∈ footprint)
    {body : Pattern} (original : ∀ free ∈ body.freeFvarNames, free ∈ footprint) :
    ∀ (outside : Nat → Nat → Pattern),
      (∀ level index, ∀ free ∈ (outside level index).freeFvarNames, free ∈ footprint) → ∀ depth,
      ∀ free ∈ (substituteViewed declaration inside outside depth body).freeFvarNames, free ∈ footprint := by
  induction body using Pattern.inductionOn with
  | hbvar index => intro outside outsideWithin depth; exact outsideWithin depth index
  | hfvar name => intro _ _ _; exact original
  | hlambda binder body ih =>
      intro outside outsideWithin depth
      simp only [substituteViewed, Pattern.freeFvarNames] at original ⊢
      exact ih original outside outsideWithin (depth + 1)
  | hmultiLambda arity binders body ih =>
      intro outside outsideWithin depth
      simp only [substituteViewed, Pattern.freeFvarNames] at original ⊢
      exact ih original outside outsideWithin (depth + arity)
  | hsubst body value ihBody ihValue =>
      intro outside outsideWithin depth
      simp only [substituteViewed, Pattern.freeFvarNames] at original ⊢
      intro free occurs
      rcases List.mem_append.mp occurs with occurs | occurs
      · exact ihBody (fun name member => original name (List.mem_append_left _ member)) outside
          outsideWithin (depth + 1) free occurs
      · exact ihValue (fun name member => original name (List.mem_append_right _ member)) outside
          outsideWithin depth free occurs
  | hcollection kind elements rest ih =>
      intro outside outsideWithin depth
      simp only [substituteViewed, substituteViewedList_eq_map, Pattern.freeFvarNames,
        List.flatMap_map] at original ⊢
      intro free occurs
      rcases List.mem_append.mp occurs with occurs | occurs
      · rcases List.mem_flatMap.mp occurs with ⟨element, member, occurs⟩
        exact ih element member (fun name present => original name (List.mem_append_left _
          (List.mem_flatMap.mpr ⟨element, member, present⟩))) outside outsideWithin depth free occurs
      · exact original free (List.mem_append_right _ occurs)
  | happly constructor arguments ih =>
      intro outside outsideWithin depth
      have each : ∀ argument ∈ arguments, ∀ free ∈ argument.freeFvarNames, free ∈ footprint := by
        intro argument member free occurs
        apply original free
        simpa only [Pattern.freeFvarNames] using List.mem_flatMap.mpr ⟨argument, member, occurs⟩
      match arguments, each, ih with
      | [], _, _ => intro free occurs; simp [substituteViewed, Pattern.freeFvarNames] at occurs
      | first :: second :: rest, each, ih =>
          intro free occurs
          simp only [substituteViewed, substituteViewedList_eq_map, Pattern.freeFvarNames,
            List.flatMap_map, List.mem_flatMap] at occurs
          obtain ⟨argument, member, occurs⟩ := occurs
          exact ih argument member (each argument member) outside outsideWithin depth free occurs
      | [payload], each, ih =>
          have payloadWithin := each payload (by simp)
          simp only [substituteViewed]
          split
          · have inner := ih payload (by simp) payloadWithin inside insideWithin depth
            simpa [Pattern.freeFvarNames] using inner
          · have through := ih payload (by simp) payloadWithin outside outsideWithin depth
            split
            · split
              · exact receive_free_within footprint declaration constructor (outsideWithin depth depth)
              · simpa [Pattern.freeFvarNames] using through
            · simpa [Pattern.freeFvarNames] using through

/-- **Declared binder elimination stays within a footprint** containing the
replacement's and the body's free names. A frozen spelling has no free name. -/
theorem reflective_instantiateDeclared_free_within (footprint : List String)
    (declaration : ReflectivePresentationDecl) (depth : Nat) (replacement body : Pattern)
    (inserted : ∀ free ∈ replacement.freeFvarNames, free ∈ footprint)
    (original : ∀ free ∈ body.freeFvarNames, free ∈ footprint) :
    ∀ free ∈ (instantiateDeclared declaration depth replacement body).freeFvarNames, free ∈ footprint := by
  have lowered : ∀ level index, ∀ free ∈ (instantiateBVarAt level replacement (.bvar index)).freeFvarNames,
      free ∈ footprint := fun level index =>
    instantiate_bvar_at_free_within footprint level replacement (.bvar index) inserted
      (by simp [Pattern.freeFvarNames])
  have resolvedWithin : ∀ free ∈ (resolveQuotes declaration body).freeFvarNames, free ∈ footprint :=
    fun free occurs => original free (resolve_quotes_free_names declaration body free occurs)
  unfold instantiateDeclared
  cases declaration.quoteScope with
  | closed =>
      exact reflective_instantiate_free_within footprint declaration depth replacement body inserted original
  | reaching view =>
      apply substituteViewed_free_within footprint declaration _ resolvedWithin _ lowered depth
      intro level index
      cases view with
      | apply => exact lowered level index
      | freeze frozen =>
          simp only [QuoteView.inside]
          split
          · intro free occurs
            rw [frozen.ground.1] at occurs
            cases occurs
          · exact lowered level index
      | closure context =>
          simp only [QuoteView.inside]
          split
          · intro free occurs
            simp only [Pattern.freeFvarNames, List.flatMap_cons, List.flatMap_nil, List.append_nil] at occurs
            exact lowered level level free occurs
          · exact lowered level index

theorem name_mark_free_within (footprint : List String) (declaration : ReflectivePresentationDecl)
    (depth : Nat) (replacement name : Pattern)
    (inserted : ∀ free ∈ replacement.freeFvarNames, free ∈ footprint)
    (original : ∀ free ∈ name.freeFvarNames, free ∈ footprint) :
    ∀ free ∈ (ReflectiveInstantiation.nameMark declaration depth replacement name).1.freeFvarNames,
      free ∈ footprint := by
  simp only [ReflectiveInstantiation.nameMark]
  split
  · exact instantiate_bvar_at_free_within footprint depth replacement (.bvar depth)
      inserted (by simp [Pattern.freeFvarNames])
  · exact reflective_instantiate_free_within footprint declaration depth replacement name
      inserted original

#print axioms Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation.name_mark_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation.reflective_instantiate_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation.reflective_instantiateDeclared_free_within

end Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation
