import Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
import Mettapedia.OSLF.MeTTaIL.ScopedPattern

/-!
# Binder-eliminating reflective instantiation

This operation is parameterized by the existing reflective declaration. It
retains literal quotation and the distinction between a substituted dropped
name and a free dropped quote. It additionally eliminates the received binder
and lifts an open replacement under intervening binders.

The existing closed reflective interpreter is unchanged. Agreement below is
an explicit comparison, not a replacement of its operational meaning.
Ordinary scope and admission as a sealed literal quotation remain distinct.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation

open Syntax Reflection Substitution ScopedPattern ReflectiveSubstitution

private theorem normalizeReflectiveList_eq_map (declaration : ReflectivePresentationDecl)
    (patterns : List Pattern) : normalizeReflectiveList declaration patterns =
      patterns.map (normalizeReflective declaration) := by
  induction patterns with
  | nil => rfl
  | cons head tail ih => simp [normalizeReflectiveList, ih]

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
      simp only [normalizeReflective, finishNormalizeReflectiveApply]
      split
      · generalize normalizedEq : normalizeReflectiveList declaration arguments = normalized at listSafe ⊢
        split
        · rename_i drop name
          split
          · simpa [Pattern.isWellScopedListAt, Pattern.isWellScopedAt] using listSafe
          · exact listSafe
        · exact listSafe
      · exact listSafe
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

/-- The Boolean records substitution of the selected whole name. Lowering
an ambient index does not confer substituted-quote provenance. -/
def nameMark (declaration : ReflectivePresentationDecl)
    (depth : Nat) (replacement name : Pattern) : Pattern × Bool :=
  match normalizeReflective declaration name with
  | .bvar index =>
      (instantiateBVarAt depth replacement (.bvar index), index == depth)
  | normalized => (normalized, false)

mutual
  /-- Eliminate one binder with the declared reflective activation behavior. -/
  def instantiate (declaration : ReflectivePresentationDecl)
      (depth : Nat) (replacement : Pattern) : Pattern → Pattern
    | .bvar index => instantiateBVarAt depth replacement (.bvar index)
    | .fvar name => .fvar name
    | .apply constructor [payload] =>
        if constructor == declaration.quoteConstructor then
          (nameMark declaration depth replacement (.apply constructor [payload])).1
        else if constructor == declaration.dropConstructor then
          let (name, matched) := nameMark declaration depth replacement payload
          match name, matched with
          | .apply quote [process], true =>
              if quote == declaration.quoteConstructor then process
              else .apply constructor [name]
          | _, _ => .apply constructor [name]
        else .apply constructor [instantiate declaration depth replacement payload]
    | .apply constructor arguments =>
        .apply constructor (instantiateList declaration depth replacement arguments)
    | .lambda binder body =>
        .lambda binder (instantiate declaration (depth + 1) replacement body)
    | .multiLambda arity binders body =>
        .multiLambda arity binders (instantiate declaration (depth + arity) replacement body)
    | .subst body value =>
        .subst (instantiate declaration (depth + 1) replacement body)
          (instantiate declaration depth replacement value)
    | .collection kind elements rest =>
        .collection kind (instantiateList declaration depth replacement elements) rest

  def instantiateList (declaration : ReflectivePresentationDecl)
      (depth : Nat) (replacement : Pattern) : List Pattern → List Pattern
    | [] => []
    | head :: tail => instantiate declaration depth replacement head ::
        instantiateList declaration depth replacement tail
end

theorem nameMark_closed_agreement (declaration : ReflectivePresentationDecl)
    {depth : Nat} {name replacement : Pattern}
    (nameSafe : name.isWellScopedAt (depth + 1) = true)
    (replacementSafe : replacement.isWellScopedAt 0 = true) :
    nameMark declaration depth replacement name =
      substituteNameMark declaration depth replacement name := by
  have normalizedSafe := normalizeReflective_scoped declaration nameSafe
  unfold nameMark substituteNameMark
  generalize normalizedEq : normalizeReflective declaration name = normalized at normalizedSafe ⊢
  cases normalized <;> try rfl
  rename_i index
  have bound : index < depth + 1 := by simpa [Pattern.isWellScopedAt] using normalizedSafe
  by_cases hit : index = depth
  · subst index
    simp [instantiateBVarAt, liftBVars_eq_self_of_isWellScopedAt replacementSafe]
  · have below : index < depth := by omega
    simp [instantiateBVarAt, below, hit]

private theorem instantiateList_eq_map (declaration : ReflectivePresentationDecl)
    (depth : Nat) (replacement : Pattern) (patterns : List Pattern) :
    instantiateList declaration depth replacement patterns =
      patterns.map (instantiate declaration depth replacement) := by
  induction patterns with
  | nil => rfl
  | cons head tail ih => simp [instantiateList, ih]

private theorem substituteReflectiveList_eq_map (declaration : ReflectivePresentationDecl)
    (depth : Nat) (replacement : Pattern) (patterns : List Pattern) :
    substituteReflectiveList declaration depth replacement patterns =
      patterns.map (substituteReflective declaration depth replacement) := by
  induction patterns with
  | nil => rfl
  | cons head tail ih => simp [substituteReflectiveList, ih]

/-- On the established closed domain, binder elimination and replacement
lifting are vacuous. The full operations agree, including whether a dropped
quotation was supplied by this substitution or occurred literally in code. -/
theorem closed_agreement (declaration : ReflectivePresentationDecl)
    {depth : Nat} {body replacement : Pattern}
    (bodySafe : body.isWellScopedAt (depth + 1) = true)
    (replacementSafe : replacement.isWellScopedAt 0 = true) :
    instantiate declaration depth replacement body =
      substituteReflective declaration depth replacement body := by
  induction body using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      have bound : index < depth + 1 := by simpa [Pattern.isWellScopedAt] using bodySafe
      by_cases hit : index = depth
      · subst index
        simp [instantiate, substituteReflective, instantiateBVarAt,
          liftBVars_eq_self_of_isWellScopedAt replacementSafe]
      · have below : index < depth := by omega
        simp [instantiate, substituteReflective, instantiateBVarAt, below, hit]
  | hfvar name => rfl
  | happly constructor arguments ih =>
      have each := (isWellScopedListAt_eq_true_iff _ _).mp bodySafe
      have listAgreement : instantiateList declaration depth replacement arguments =
          substituteReflectiveList declaration depth replacement arguments := by
        rw [instantiateList_eq_map, substituteReflectiveList_eq_map]
        exact List.map_congr_left fun p hp => ih p hp (each p hp)
      cases arguments with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil =>
              have firstSafe := each first (by simp)
              simp only [instantiate, substituteReflective]
              split
              · rw [nameMark_closed_agreement declaration bodySafe replacementSafe]
              · split
                · rw [nameMark_closed_agreement declaration firstSafe replacementSafe]
                  rfl
                · rw [ih first (by simp) firstSafe]
          | cons second more =>
              exact congrArg (Pattern.apply constructor) listAgreement
  | hlambda binder body ih =>
      exact congrArg (Pattern.lambda binder) (ih bodySafe)
  | hmultiLambda arity binders body ih =>
      have bodySafe' : body.isWellScopedAt (depth + arity + 1) = true := by
        simpa [Pattern.isWellScopedAt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using bodySafe
      exact congrArg (Pattern.multiLambda arity binders) (ih bodySafe')
  | hsubst body value ihBody ihValue =>
      have pair : body.isWellScopedAt (depth + 1 + 1) = true ∧
          value.isWellScopedAt (depth + 1) = true := by
        simpa only [Pattern.isWellScopedAt, Bool.and_eq_true] using bodySafe
      exact congrArg₂ Pattern.subst (ihBody pair.1) (ihValue pair.2)
  | hcollection kind elements rest ih =>
      change Pattern.collection kind (instantiateList declaration depth replacement elements) rest =
        Pattern.collection kind (substituteReflectiveList declaration depth replacement elements) rest
      congr 1
      rw [instantiateList_eq_map, substituteReflectiveList_eq_map]
      exact List.map_congr_left fun p hp => ih p hp
        ((isWellScopedListAt_eq_true_iff _ _).mp bodySafe p hp)

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

theorem nameMark_scoped (declaration : ReflectivePresentationDecl)
    {ambient depth : Nat} {name replacement : Pattern}
    (nameSafe : name.isWellScopedAt (ambient + depth + 1) = true)
    (nameAdmitted : atomicOrClosed declaration name = true)
    (replacementSafe : replacement.isWellScopedAt ambient = true) :
    (nameMark declaration depth replacement name).1.isWellScopedAt (ambient + depth) = true := by
  have normalizedSafe := normalizeReflective_scoped declaration nameSafe
  unfold atomicOrClosed at nameAdmitted
  unfold nameMark
  generalize normalizeReflective declaration name = normalized at normalizedSafe nameAdmitted ⊢
  cases normalized with
  | bvar index => exact instantiateBVarAt_isWellScopedAt normalizedSafe replacementSafe
  | fvar name => rfl
  | apply constructor arguments => exact isWellScopedAt_mono nameAdmitted (Nat.zero_le _)
  | lambda binder body => exact isWellScopedAt_mono nameAdmitted (Nat.zero_le _)
  | multiLambda arity binders body => exact isWellScopedAt_mono nameAdmitted (Nat.zero_le _)
  | subst body value => exact isWellScopedAt_mono nameAdmitted (Nat.zero_le _)
  | collection kind elements rest => exact isWellScopedAt_mono nameAdmitted (Nat.zero_le _)

private theorem nameMark_closed_name (declaration : ReflectivePresentationDecl)
    (depth : Nat) (replacement : Pattern) {name : Pattern}
    (nameSafe : name.isWellScopedAt 0 = true) :
    (nameMark declaration depth replacement name).1 = normalizeReflective declaration name := by
  have normalizedSafe := normalizeReflective_scoped declaration nameSafe
  unfold nameMark
  generalize normalizeReflective declaration name = normalized at normalizedSafe ⊢
  cases normalized <;> try rfl
  simp [Pattern.isWellScopedAt] at normalizedSafe

/-- Open instantiation preserves ordinary scope. Literal source quotes are
sealed and operationally inspected names are atomic or closed. The resulting
name of an open payload need not itself be a sealed literal quotation. -/
theorem instantiate_scoped (declaration : ReflectivePresentationDecl)
    {ambient depth : Nat} {body replacement : Pattern}
    (bodySafe : binderSafeAt declaration.quoteConstructor (ambient + depth + 1) body = true)
    (names : namesAdmitted declaration body = true)
    (replacementSafe : replacement.isWellScopedAt ambient = true) :
    (instantiate declaration depth replacement body).isWellScopedAt (ambient + depth) = true := by
  induction body using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      exact instantiateBVarAt_isWellScopedAt bodySafe replacementSafe
  | hfvar name => rfl
  | happly constructor arguments ih =>
      cases arguments with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil =>
              by_cases quoted : constructor = declaration.quoteConstructor
              · have firstClosed : first.isWellScopedAt 0 = true :=
                  isWellScopedAt_of_binderSafeAt _ (by simpa [binderSafeAt, quoted] using bodySafe)
                have wholeClosed : (Pattern.apply constructor [first]).isWellScopedAt 0 = true := by
                  simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using firstClosed
                simp only [instantiate, quoted, beq_self_eq_true, if_true]
                rw [nameMark_closed_name declaration depth replacement
                  (show (Pattern.apply declaration.quoteConstructor [first]).isWellScopedAt 0 = true by
                    simpa [quoted] using wholeClosed)]
                exact isWellScopedAt_mono (normalizeReflective_scoped declaration
                  (by simpa [quoted] using wholeClosed)) (Nat.zero_le _)
              · have firstSafe : binderSafeAt declaration.quoteConstructor (ambient + depth + 1)
                    first = true := by simpa [binderSafeAt, quoted, binderSafeListAt] using bodySafe
                by_cases dropped : constructor = declaration.dropConstructor
                · have admitted : atomicOrClosed declaration first = true := by
                    simpa only [namesAdmitted, beq_iff_eq, if_neg quoted, if_pos dropped] using names
                  have nameScoped := nameMark_scoped declaration
                    (isWellScopedAt_of_binderSafeAt _ firstSafe) admitted replacementSafe
                  simp only [instantiate, beq_iff_eq, if_neg quoted, if_pos dropped]
                  generalize markedEq : nameMark declaration depth replacement first = marked at nameScoped ⊢
                  rcases marked with ⟨name, matched⟩
                  simp only at nameScoped ⊢
                  split
                  · split
                    · simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using nameScoped
                    · simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using nameScoped
                  · simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using nameScoped
                · have firstNames : namesAdmitted declaration first = true := by
                    simpa [namesAdmitted, quoted, dropped] using names
                  simpa [instantiate, quoted, dropped, Pattern.isWellScopedAt,
                    Pattern.isWellScopedListAt] using ih first (by simp) firstSafe firstNames
          | cons second more =>
              have each := (binderSafeListAt_eq_true_iff _ _ _).mp bodySafe
              have eachNames := (namesAdmittedList_iff declaration _).mp names
              change Pattern.isWellScopedListAt (ambient + depth)
                (instantiateList declaration depth replacement (first :: second :: more)) = true
              rw [instantiateList_eq_map, isWellScopedListAt_eq_true_iff]
              intro p member
              obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
              exact ih original originalMember (each original originalMember) (eachNames original originalMember)
  | hlambda binder body ih =>
      have bodySafe' : binderSafeAt declaration.quoteConstructor (ambient + (depth + 1) + 1) body = true := by
        simpa [binderSafeAt, Nat.add_assoc] using bodySafe
      simpa [instantiate, Pattern.isWellScopedAt, Nat.add_assoc] using ih bodySafe' names
  | hmultiLambda arity binders body ih =>
      have bodySafe' : binderSafeAt declaration.quoteConstructor (ambient + (depth + arity) + 1) body = true := by
        simpa [binderSafeAt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bodySafe
      simpa [instantiate, Pattern.isWellScopedAt, Nat.add_assoc] using ih bodySafe' names
  | hsubst body value ihBody ihValue =>
      simp only [binderSafeAt, Bool.and_eq_true] at bodySafe
      simp only [namesAdmitted, Bool.and_eq_true] at names
      simp only [instantiate, Pattern.isWellScopedAt, Bool.and_eq_true]
      refine ⟨?_, ihValue bodySafe.2 names.2⟩
      simpa [Nat.add_assoc] using ihBody (depth := depth + 1)
        (by simpa [Nat.add_assoc] using bodySafe.1) names.1
  | hcollection kind elements rest ih =>
      have each := (binderSafeListAt_eq_true_iff _ _ _).mp bodySafe
      have eachNames := (namesAdmittedList_iff declaration _).mp names
      change Pattern.isWellScopedListAt (ambient + depth)
        (instantiateList declaration depth replacement elements) = true
      rw [instantiateList_eq_map, isWellScopedListAt_eq_true_iff]
      intro p member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact ih original originalMember (each original originalMember) (eachNames original originalMember)

#print axioms closed_agreement
#print axioms instantiate_scoped

end Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation
