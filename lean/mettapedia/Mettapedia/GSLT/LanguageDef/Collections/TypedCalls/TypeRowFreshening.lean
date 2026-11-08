import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeAlphaNormalization

/-!
# Fresh row names in ordered type inference

The actual ordered argument and row drivers commute with one permutation of
their private type variables. Retained ground child observations need not be
renamed, and an admitted ground result is literally unchanged. This is a
row-local reuse law, not a simulation of the recursive allocation supply or a
proof of the native nested-wildcard matcher.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeRowFreshening

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open TypeDependencyAdmission TypeScopeMatcher TypeScopeRenaming NativeTypeViews

mutual
theorem admitted_rename (rename : String → String) : ∀ atom,
    RetainedTypePayloads.admitted atom = true → renameAtom rename atom = atom
  | .symbol _, _ => rfl
  | .var _, accepted => by simp [RetainedTypePayloads.admitted] at accepted
  | .grounded _, _ => rfl
  | .expression children, accepted =>
      congrArg Atom.expression (admittedList_rename rename children accepted)
theorem admittedList_rename (rename : String → String) : ∀ atoms,
    RetainedTypePayloads.admittedList atoms = true → renameAtomList rename atoms = atoms
  | [], _ => rfl
  | atom :: atoms, accepted => by
      simp only [RetainedTypePayloads.admittedList, Bool.and_eq_true] at accepted
      rw [renameAtomList, admitted_rename rename atom accepted.1,
        admittedList_rename rename atoms accepted.2]
end

mutual
theorem admitted_resourceFree : ∀ atom,
    RetainedTypePayloads.admitted atom = true → resourceFree atom = true
  | .symbol _, _ => rfl
  | .var _, accepted => by simp [RetainedTypePayloads.admitted] at accepted
  | .grounded value, accepted => by
      cases value <;> simp_all [RetainedTypePayloads.admitted, resourceFree]
  | .expression children, accepted => admittedList_resourceFree children accepted
theorem admittedList_resourceFree : ∀ atoms,
    RetainedTypePayloads.admittedList atoms = true → resourceFreeList atoms = true
  | [], _ => rfl
  | atom :: atoms, accepted => by
      simp only [RetainedTypePayloads.admittedList, Bool.and_eq_true] at accepted
      exact Bool.and_eq_true_iff.mpr
        ⟨admitted_resourceFree atom accepted.1, admittedList_resourceFree atoms accepted.2⟩
end

def renameChild (permutation : Equiv.Perm String) (child : ChildView Atom Atom) : ChildView Atom Atom :=
  ⟨renameAtom permutation child.kind, child.inferred.map (renameAtom permutation),
    child.tuplePart.map (renameAtom permutation)⟩

def ChildrenSafe (children : List (ChildView Atom Atom)) : Prop :=
  ∀ child ∈ children, resourceFreeList child.inferred = true

theorem metaCheck_rename (permutation : Equiv.Perm String) (formal kind : Atom) :
    metaCheckAtom (renameAtom permutation formal) (renameAtom permutation kind) =
      metaCheckAtom formal kind := by
  simp only [metaCheckAtom,
    show (renameAtom permutation formal == Atom.atomType) = (formal == Atom.atomType)
      from symbol_test_rename permutation formal "Atom",
    show (renameAtom permutation formal == Atom.symbolType) = (formal == Atom.symbolType)
      from symbol_test_rename permutation formal "Symbol",
    show (renameAtom permutation formal == Atom.variableType) = (formal == Atom.variableType)
      from symbol_test_rename permutation formal "Variable",
    show (renameAtom permutation formal == Atom.groundedType) = (formal == Atom.groundedType)
      from symbol_test_rename permutation formal "Grounded",
    show (renameAtom permutation formal == Atom.expressionType) = (formal == Atom.expressionType)
      from symbol_test_rename permutation formal "Expression",
    show (renameAtom permutation formal == renameAtom permutation kind) = (formal == kind)
      from TypeNormalizationNames.equality_equivariant permutation formal kind]

theorem initial_rename (permutation : Equiv.Perm String) :
    renameState permutation Atom.var = Atom.var := by
  funext name
  simp [renameState, renameAtom]

theorem args_rename (external : RetainedTypePayloads.ExternalView)
    (normalize : Atom → Atom) (subtypes : List Atom → List Atom)
    (permutation : Equiv.Perm String) :
    ∀ formals children state,
      resourceFreeList formals = true → ChildrenSafe children → SafeState state →
      transitionArgs (ops external normalize subtypes) (renameAtomList permutation formals)
          (children.map (renameChild permutation)) (renameState permutation state) =
        (transitionArgs (ops external normalize subtypes) formals children state).map
          (renameState permutation)
  | [], children, state, _, _, _ => by cases children <;> rfl
  | _ :: _, [], _, _, _, _ => rfl
  | formal :: formals, child :: children, state, formalsSafe, childrenSafe, stateSafe => by
      simp only [resourceFreeList, Bool.and_eq_true] at formalsSafe
      have expectedSafe := substitute_resourceFree state stateSafe formal formalsSafe.1
      have tailSafe : ChildrenSafe children := fun other member =>
        childrenSafe other (List.mem_cons_of_mem _ member)
      have childSafe := childrenSafe child (by simp)
      simp only [renameAtomList, List.map_cons, transitionArgs, ops, renameChild,
        substitute, metaCheck_rename]
      cases metatype : metaCheckAtom (substA state formal) child.kind with
      | some answer =>
          cases answer with
          | false => rfl
          | true =>
              exact args_rename external normalize subtypes permutation
                formals children state formalsSafe.2 tailSafe stateSafe
      | none =>
          rw [firstChoice_rename external permutation state stateSafe _ expectedSafe _ childSafe]
          cases selected : StampInference.firstResult
              (fun actual => unify external state actual (substA state formal)) child.inferred with
          | none => rfl
          | some next =>
              exact args_rename external normalize subtypes permutation formals children next
                formalsSafe.2 tailSafe
                (firstResult_preserves external state stateSafe _ expectedSafe _ childSafe next selected)

theorem functionArgs_rename (rename : String → String) (row : Atom) :
    getFunctionArgTypes (renameAtom rename row) =
      (getFunctionArgTypes row).map (renameAtomList rename) := by
  cases row with
  | symbol _ | var _ | grounded _ => rfl
  | expression children =>
      cases children with
      | nil => rfl
      | cons head rest =>
          cases head with
          | var _ | grounded _ | expression _ => rfl
          | symbol name =>
              by_cases isArrow : name = "->"
              · subst name
                simp [getFunctionArgTypes, renameAtom, renameAtomList_eq_map, List.map_dropLast]
              · simp [getFunctionArgTypes, renameAtom, renameAtomList, isArrow]

theorem functionRange_rename (rename : String → String) (row : Atom) :
    getFunctionRetType (renameAtom rename row) =
      (getFunctionRetType row).map (renameAtom rename) := by
  cases row with
  | symbol _ | var _ | grounded _ => rfl
  | expression children =>
      cases children with
      | nil => rfl
      | cons head rest =>
          cases head with
          | var _ | grounded _ | expression _ => rfl
          | symbol name =>
              by_cases isArrow : name = "->"
              · subst name
                simp only [getFunctionRetType, renameAtom, renameAtomList_eq_map,
                  List.map_cons, List.length_map, List.getLast?_map]
                split <;> rfl
              · simp [getFunctionRetType, renameAtom, renameAtomList, isArrow]

theorem arrow_rename (external : RetainedTypePayloads.ExternalView)
    (normalize : Atom → Atom) (subtypes : List Atom → List Atom)
    (permutation : Equiv.Perm String) (row : Atom) :
    (ops external normalize subtypes).arrow (renameAtom permutation row) =
      ((ops external normalize subtypes).arrow row).map
        (fun signature => (renameAtomList permutation signature.1, renameAtom permutation signature.2)) := by
  simp only [ops, functionArgs_rename, functionRange_rename]
  cases getFunctionArgTypes row <;> cases getFunctionRetType row <;> rfl

theorem args_preserves (external : RetainedTypePayloads.ExternalView)
    (normalize : Atom → Atom) (subtypes : List Atom → List Atom) :
    ∀ formals children state,
      resourceFreeList formals = true → ChildrenSafe children → SafeState state →
      ∀ after, transitionArgs (ops external normalize subtypes) formals children state = some after →
        SafeState after
  | [], [], _, _, _, safe, after, checked => by cases Option.some.inj checked; exact safe
  | [], _ :: _, _, _, _, _, _, checked => by simp [transitionArgs] at checked
  | _ :: _, [], _, _, _, _, _, checked => by simp [transitionArgs] at checked
  | formal :: formals, child :: children, state, formalsSafe, childrenSafe, stateSafe, after, checked => by
      simp only [resourceFreeList, Bool.and_eq_true] at formalsSafe
      have tailSafe : ChildrenSafe children := fun other member =>
        childrenSafe other (List.mem_cons_of_mem _ member)
      have expectedSafe := substitute_resourceFree state stateSafe formal formalsSafe.1
      simp only [transitionArgs, ops] at checked
      split at checked
      · exact args_preserves external normalize subtypes formals children state
          formalsSafe.2 tailSafe stateSafe after checked
      · contradiction
      · simp only [Option.bind_eq_some_iff] at checked
        obtain ⟨next, selected, returned⟩ := checked
        exact args_preserves external normalize subtypes formals children next formalsSafe.2 tailSafe
          (firstResult_preserves external state stateSafe _ expectedSafe _
            (childrenSafe child (by simp)) next selected) after returned

theorem row_rename (external : RetainedTypePayloads.ExternalView)
    (normalize : Atom → Atom) (subtypes : List Atom → List Atom)
    (permutation : Equiv.Perm String)
    (normalizes : ∀ atom, resourceFree atom = true →
      normalize (renameAtom permutation atom) = renameAtom permutation (normalize atom))
    (children : List (ChildView Atom Atom)) (childrenSafe : ChildrenSafe children)
    (row : Atom) (rowSafe : resourceFree row = true) :
    transitionRow (ops external normalize subtypes) (children.map (renameChild permutation))
        (renameAtom permutation row) =
      (transitionRow (ops external normalize subtypes) children row).map (renameAtom permutation) := by
  simp only [transitionRow, arrow_rename]
  cases arrow : (ops external normalize subtypes).arrow row with
  | none => rfl
  | some signature =>
      obtain ⟨formals, range⟩ := signature
      have safe := arrow_resourceFree external normalize subtypes rowSafe arrow
      simp only [Option.map_some, Option.bind_some]
      have renamedArgs := args_rename external normalize subtypes permutation formals children
        Atom.var safe.1 childrenSafe (fun _ => rfl)
      rw [initial_rename] at renamedArgs
      change ((transitionArgs (ops external normalize subtypes) (renameAtomList permutation formals)
        (children.map (renameChild permutation)) Atom.var).map
          (fun state => normalize (substA state (renameAtom permutation range)))) =
        ((transitionArgs (ops external normalize subtypes) formals children Atom.var).map
          (fun state => normalize (substA state range))).map (renameAtom permutation)
      rw [renamedArgs]
      cases checked : transitionArgs (ops external normalize subtypes) formals children Atom.var with
      | none => rfl
      | some state =>
          have stateSafe := args_preserves external normalize subtypes formals children Atom.var
            safe.1 childrenSafe (fun _ => rfl) state checked
          simp only [Option.map_some, substitute]
          exact congrArg some (normalizes _ (substitute_resourceFree state stateSafe range safe.2))

theorem retained_child_fixed (permutation : Equiv.Perm String) (child : ChildView Atom Atom)
    (kindSafe : RetainedTypePayloads.admitted child.kind = true)
    (typesSafe : RetainedTypePayloads.admittedList child.inferred = true)
    (tupleSafe : RetainedTypePayloads.admittedList child.tuplePart = true) :
    renameChild permutation child = child := by
  cases child with
  | mk kind inferred tuplePart =>
      simp only [renameChild]
      rw [admitted_rename permutation kind kindSafe,
        ← renameAtomList_eq_map, admittedList_rename permutation inferred typesSafe,
        ← renameAtomList_eq_map, admittedList_rename permutation tuplePart tupleSafe]

def ChildrenRetained (children : List (ChildView Atom Atom)) : Prop :=
  ∀ child ∈ children, RetainedTypePayloads.admitted child.kind = true ∧
    RetainedTypePayloads.admittedList child.inferred = true ∧
    RetainedTypePayloads.admittedList child.tuplePart = true

theorem retained_children_safe {children : List (ChildView Atom Atom)}
    (retained : ChildrenRetained children) : ChildrenSafe children :=
  fun child member => admittedList_resourceFree _ (retained child member).2.1

theorem retained_children_fixed (permutation : Equiv.Perm String)
    {children : List (ChildView Atom Atom)} (retained : ChildrenRetained children) :
    children.map (renameChild permutation) = children := by
  calc
    children.map (renameChild permutation) = children.map id := by
      apply List.map_congr_left
      intro child member
      obtain ⟨kind, inferred, tuplePart⟩ := retained child member
      exact retained_child_fixed permutation child kind inferred tuplePart
    _ = children := List.map_id children

/-- The payload admission is checked on the actual result. It does not
assert that every successful row has a ground range. -/
theorem retained_row_exact (external : RetainedTypePayloads.ExternalView)
    (normalize : Atom → Atom) (subtypes : List Atom → List Atom)
    (permutation : Equiv.Perm String)
    (normalizes : ∀ atom, resourceFree atom = true →
      normalize (renameAtom permutation atom) = renameAtom permutation (normalize atom))
    (children : List (ChildView Atom Atom)) (childrenRetained : ChildrenRetained children)
    (row : Atom) (rowSafe : resourceFree row = true)
    (outputRetained : ∀ result,
      transitionRow (ops external normalize subtypes) children row = some result →
        RetainedTypePayloads.admitted result = true) :
    transitionRow (ops external normalize subtypes) children (renameAtom permutation row) =
      transitionRow (ops external normalize subtypes) children row := by
  have renamed := row_rename external normalize subtypes permutation normalizes children
    (retained_children_safe childrenRetained) row rowSafe
  rw [retained_children_fixed permutation childrenRetained] at renamed
  rw [renamed]
  cases result : transitionRow (ops external normalize subtypes) children row with
  | none => rfl
  | some value => exact congrArg some (admitted_rename permutation value (outputRetained value result))

/-- Each occurrence may use its own fresh names. The relation preserves
row order and duplicate occurrences, rather than comparing a set of rows. -/
theorem independently_fresh_rows_exact (external : RetainedTypePayloads.ExternalView)
    (normalize : Atom → Atom) (subtypes : List Atom → List Atom)
    (normalizes : ∀ (permutation : Equiv.Perm String) atom, resourceFree atom = true →
      normalize (renameAtom permutation atom) = renameAtom permutation (normalize atom))
    (children : List (ChildView Atom Atom)) (childrenRetained : ChildrenRetained children)
    {rows freshRows : List Atom}
    (fresh : List.Forall₂ (fun row freshRow =>
      ∃ permutation : Equiv.Perm String, freshRow = renameAtom permutation row) rows freshRows)
    (rowsSafe : resourceFreeList rows = true)
    (outputsRetained : ∀ row ∈ rows, ∀ result,
      transitionRow (ops external normalize subtypes) children row = some result →
        RetainedTypePayloads.admitted result = true) :
    transitionRows (ops external normalize subtypes) children freshRows =
      transitionRows (ops external normalize subtypes) children rows := by
  induction fresh with
  | nil => rfl
  | @cons row freshRow rows freshRows head tail ih =>
      simp only [resourceFreeList, Bool.and_eq_true] at rowsSafe
      obtain ⟨permutation, rfl⟩ := head
      have same := retained_row_exact external normalize subtypes permutation (normalizes permutation)
        children childrenRetained row rowsSafe.1 (outputsRetained row (by simp))
      have rest := ih rowsSafe.2 (fun item member => outputsRetained item (List.mem_cons_of_mem _ member))
      simp only [transitionRows, List.filterMap_cons, same]
      simp only [transitionRows] at rest
      rw [rest]

theorem alpha_normalized_retained_rows_exact (external : RetainedTypePayloads.ExternalView)
    (subtypes : List Atom → List Atom) (children : List (ChildView Atom Atom))
    (childrenRetained : ChildrenRetained children) {rows freshRows : List Atom}
    (fresh : List.Forall₂ (fun row freshRow =>
      ∃ permutation : Equiv.Perm String, freshRow = renameAtom permutation row) rows freshRows)
    (rowsSafe : resourceFreeList rows = true)
    (outputsRetained : ∀ row ∈ rows, ∀ result,
      transitionRow (ops external
        (InertTypeDependencies.normalize TypeAlphaNormalization.active
          (TypeNormalizationScope.observed external TypeAlphaNormalization.dispatch)) subtypes)
        children row = some result → RetainedTypePayloads.admitted result = true) :
    transitionRows (ops external
      (InertTypeDependencies.normalize TypeAlphaNormalization.active
        (TypeNormalizationScope.observed external TypeAlphaNormalization.dispatch)) subtypes)
      children freshRows =
    transitionRows (ops external
      (InertTypeDependencies.normalize TypeAlphaNormalization.active
        (TypeNormalizationScope.observed external TypeAlphaNormalization.dispatch)) subtypes)
      children rows :=
  independently_fresh_rows_exact external _ subtypes
    (TypeAlphaNormalization.normalization_renames external) children childrenRetained fresh rowsSafe outputsRetained

namespace Controls

def external : RetainedTypePayloads.ExternalView := fun tag key => .grounded (.custom tag key)
def checkOps : Ops Atom State Atom := ops external id (fun _ => [])
def number : ChildView Atom Atom := ⟨Atom.groundedType, [.symbol "Number"], [.symbol "Number"]⟩
def string : ChildView Atom Atom := ⟨Atom.groundedType, [.symbol "String"], [.symbol "String"]⟩
def signature (name : String) : Atom := .expression [.symbol "->", .var name, .var name]

theorem private_rows_preserve_duplicate_answers :
    transitionRows checkOps [number] [signature "first", signature "second"] =
      [.symbol "Number", .symbol "Number"] := by cbv

theorem shared_formal_is_not_two_independent_checks :
    transitionRow checkOps [number, string]
      (.expression [.symbol "->", .var "a", .var "a", .symbol "Result"]) = none ∧
    transitionRow checkOps [number, string]
      (.expression [.symbol "->", .var "a", .var "b", .symbol "Result"]) = some (.symbol "Result") := by cbv

theorem unresolved_range_cannot_be_retained :
    transitionRow checkOps [number]
      (.expression [.symbol "->", .var "argument", .var "result"]) = some (.var "result") ∧
      RetainedTypePayloads.admitted (.var "result") = false := by cbv

theorem metatype_cut_does_not_require_an_inferred_typing :
    transitionRow checkOps [⟨Atom.expressionType, [], []⟩]
      (.expression [.symbol "->", Atom.expressionType, .symbol "Result"]) = some (.symbol "Result") := by cbv

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeRowFreshening
