/-
# State-free producer preservation

This module proves that the atom-producing structural operations used by the
minimal evaluator cannot introduce a world-mutating instruction when their
inputs contain none.  The final evaluator induction consumes these facts; it
does not unfold binding resolution or substitution again.
-/
import Mettapedia.Languages.MeTTa.HE.StateFreeFragment

namespace Mettapedia.Languages.MeTTa.HE.StateFreePreservation

open Metta
open Mettapedia.Languages.MeTTa.HE.StateFreeFragment

/-! ## Opaque binding-payload restoration

`collapse-bind` stores live atoms in the snapshot carrier from `Core.Atom`;
`superpose-bind` restores them.  The following mutual proof is the boundary
showing that this round-trip cannot expose a state operation hidden inside an
otherwise opaque grounded value. -/

mutual

/-- Restoring a safe stored atom yields a safe live atom. -/
theorem storedAtom_toAtom_stateOpFree : ∀ atom : StoredAtom,
    StoredAtomStateOpFree atom → StateOpFree atom.toAtom
  | .sym name, safe => by
      simpa only [StoredAtom.toAtom, StoredAtomStateOpFree, StateOpFree] using safe
  | .var name, _ => by
      simp only [StoredAtom.toAtom, StateOpFree]
  | .gnd ground, safe => by
      cases ground <;>
        simp only [StoredAtom.toAtom, StoredGround.toGround,
          StoredAtomStateOpFree, StoredGroundStateOpFree, StateOpFree] at safe ⊢ <;>
        exact safe
  | .expr atoms, safe => by
      rw [StoredAtom.toAtom, stateOpFree_expr_iff_list]
      exact storedAtoms_toAtoms_stateOpFree atoms safe.2

/-- Restoring a safe stored atom list yields a safe live atom list. -/
theorem storedAtoms_toAtoms_stateOpFree : ∀ atoms : List StoredAtom,
    StoredAtomsStateOpFree atoms →
      StateOpFreeList (atoms.map StoredAtom.toAtom)
  | [], _ => trivial
  | atom :: atoms, safe =>
      ⟨storedAtom_toAtom_stateOpFree atom safe.1,
        storedAtoms_toAtoms_stateOpFree atoms safe.2⟩

end


/-- Restoring one safe stored relation yields a safe live relation. -/
theorem storedBinding_toBindingRel_stateOpFree
    (binding : StoredBinding) (safe : StoredBindingStateOpFree binding) :
    BindingRelStateOpFree binding.toBindingRel := by
  cases binding with
  | val name value =>
      exact storedAtom_toAtom_stateOpFree value safe
  | eq left right => trivial

/-- Restoring a complete opaque payload preserves binding safety. -/
theorem storedBindings_restore_stateOpFree : ∀ bindings : List StoredBinding,
    StoredBindingsStateOpFree bindings →
      BindingsStateOpFree (Bindings.restore bindings)
  | [], _ => trivial
  | binding :: bindings, safe =>
      ⟨storedBinding_toBindingRel_stateOpFree binding safe.1,
        storedBindings_restore_stateOpFree bindings safe.2⟩

/-- Every value in a first-order substitution is state-operation-free. -/
def SubstStateOpFree (substitution : Subst) : Prop :=
  ∀ name value, (name, value) ∈ substitution → StateOpFree value

/-- Successful substitution lookup returns a safe value. -/
theorem subst_lookup_stateOpFree {substitution : Subst}
    (safe : SubstStateOpFree substitution) {name : VarName} {value : Atom}
    (lookup : Subst.lookup substitution name = some value) :
    StateOpFree value := by
  induction substitution with
  | nil => simp [Subst.lookup] at lookup
  | cons entry rest inductionHypothesis =>
      obtain ⟨key, stored⟩ := entry
      simp only [Subst.lookup] at lookup
      split at lookup
      · cases lookup
        exact safe key value (by simp)
      · exact inductionHypothesis (by
          intro candidate candidateValue member
          exact safe candidate candidateValue (by simp [member])) lookup

/-- Applying a safe substitution to a safe atom stays in the fragment. -/
theorem stateOpFree_substApply {substitution : Subst}
    (substitutionSafe : SubstStateOpFree substitution) :
    ∀ atom, StateOpFree atom →
      StateOpFree (Subst.apply substitution atom)
  | .sym symbol, safe => by simpa [Subst.apply] using safe
  | .var name, safe => by
      simp only [Subst.apply]
      cases lookup : Subst.lookup substitution name with
      | none => simp
      | some value =>
          simpa [lookup] using
            subst_lookup_stateOpFree substitutionSafe lookup
  | .gnd value, safe => by simpa [Subst.apply] using safe
  | .expr atoms, safe => by
      rw [Subst.apply, stateOpFree_expr_iff_list]
      rw [stateOpFreeList_iff_forall_mem]
      intro result member
      obtain ⟨atom, atomMember, rfl⟩ := List.mem_map.mp member
      exact stateOpFree_substApply substitutionSafe atom
        (stateOpFree_of_mem safe.2 atomMember)

/-- Every direct atom value stored in a runtime binding set is safe. -/
theorem bindingValue_stateOpFree_of_mem {bindings : Bindings}
    (safe : BindingsStateOpFree bindings) {name : VarName} {value : Atom}
    (member : BindingRel.val name value ∈ bindings) : StateOpFree value := by
  induction bindings with
  | nil => simp at member
  | cons relation rest inductionHypothesis =>
      rcases List.mem_cons.mp member with head | tail
      · subst relation
        exact safe.1
      · exact inductionHypothesis safe.2 tail

/-- Direct lookup through a safe binding set returns a safe value. -/
theorem bindings_lookupVal_stateOpFree {bindings : Bindings}
    (safe : BindingsStateOpFree bindings) {name : VarName} {value : Atom}
    (lookup : Bindings.lookupVal bindings name = some value) :
    StateOpFree value := by
  induction bindings with
  | nil => simp [Bindings.lookupVal] at lookup
  | cons relation rest inductionHypothesis =>
      cases relation with
      | val key stored =>
          simp only [Bindings.lookupVal] at lookup
          split at lookup
          · cases lookup
            exact safe.1
          · exact inductionHypothesis safe.2 lookup
      | eq left right =>
          exact inductionHypothesis safe.2 lookup

/-- Every value selected from an equality class is a direct safe binding
value. -/
theorem classValues_stateOpFree {bindings : Bindings}
    (safe : BindingsStateOpFree bindings) {name : VarName} {value : Atom}
    (member : value ∈ Bindings.classValues bindings name) :
    StateOpFree value := by
  rw [Bindings.classValues] at member
  obtain ⟨representative, representativeMember, lookup⟩ :=
    List.mem_filterMap.mp member
  exact bindings_lookupVal_stateOpFree safe lookup

/-- Successful recursive binding resolution cannot synthesize a mutation
symbol: it returns either structure from the input atom, a variable
representative, or structure from a direct safe binding value. -/
theorem resolveAtomAux_stateOpFree {bindings : Bindings}
    (bindingsSafe : BindingsStateOpFree bindings) :
    ∀ fuel visited atom resolved,
      StateOpFree atom →
      Bindings.resolveAtomAux bindings fuel visited atom = some resolved →
      StateOpFree resolved := by
  intro fuel
  induction fuel with
  | zero =>
      intro visited atom resolved safe resolvedEquation
      simp [Bindings.resolveAtomAux] at resolvedEquation
  | succ fuel inductionHypothesis =>
      intro visited atom resolved safe resolvedEquation
      cases atom with
      | sym symbol =>
          simp [Bindings.resolveAtomAux] at resolvedEquation
          subst resolved
          exact safe
      | gnd ground =>
          simp [Bindings.resolveAtomAux] at resolvedEquation
          subst resolved
          exact safe
      | var name =>
          simp only [Bindings.resolveAtomAux] at resolvedEquation
          cases overlap : (Bindings.eqClassOrdered bindings name).any
              visited.contains with
          | true => simp [overlap] at resolvedEquation
          | false =>
              cases valuesEquation : Bindings.classValues bindings name with
              | nil =>
                  simp [overlap, valuesEquation] at resolvedEquation
                  subst resolved
                  simp [StateOpFree]
              | cons value rest =>
                  have valueSafe : StateOpFree value :=
                    classValues_stateOpFree bindingsSafe (by
                      rw [valuesEquation]
                      simp)
                  cases value with
                  | var target =>
                      simp only [overlap, Bool.false_eq_true, ↓reduceIte,
                        valuesEquation] at resolvedEquation
                      cases contains :
                          (Bindings.eqClassOrdered bindings name).contains target with
                      | true =>
                          simp only [contains, ↓reduceIte] at resolvedEquation
                          cases singleton :
                              (Bindings.eqClassOrdered bindings name).length == 1 with
                          | true => simp [singleton] at resolvedEquation
                          | false =>
                              simp [singleton] at resolvedEquation
                              subst resolved
                              simp [StateOpFree]
                      | false =>
                          simp only [contains, Bool.false_eq_true, ↓reduceIte]
                            at resolvedEquation
                          exact inductionHypothesis _ _ _ valueSafe resolvedEquation
                  | sym symbol =>
                      simp only [overlap, Bool.false_eq_true, ↓reduceIte,
                        valuesEquation] at resolvedEquation
                      exact inductionHypothesis _ _ _ valueSafe resolvedEquation
                  | gnd ground =>
                      simp only [overlap, Bool.false_eq_true, ↓reduceIte,
                        valuesEquation] at resolvedEquation
                      exact inductionHypothesis _ _ _ valueSafe resolvedEquation
                  | expr atoms =>
                      simp only [overlap, Bool.false_eq_true, ↓reduceIte,
                        valuesEquation] at resolvedEquation
                      exact inductionHypothesis _ _ _ valueSafe resolvedEquation
      | expr atoms =>
          simp only [Bindings.resolveAtomAux] at resolvedEquation
          cases mapEquation : atoms.mapM
              (Bindings.resolveAtomAux bindings fuel visited) with
          | none => simp [mapEquation] at resolvedEquation
          | some resolvedAtoms =>
              simp [mapEquation] at resolvedEquation
              subst resolved
              apply stateOpFree_expr_iff_list.mpr
              rw [stateOpFreeList_iff_forall_mem]
              intro resolvedAtom resolvedMember
              induction atoms generalizing resolvedAtoms with
              | nil =>
                  simp at mapEquation
                  subst resolvedAtoms
                  simp at resolvedMember
              | cons atom atoms tailInduction =>
                  simp only [List.mapM_cons] at mapEquation
                  cases headEquation : Bindings.resolveAtomAux bindings fuel
                      visited atom with
                  | none => simp [headEquation] at mapEquation
                  | some resolvedHead =>
                      cases tailEquation : atoms.mapM
                          (Bindings.resolveAtomAux bindings fuel visited) with
                      | none => simp [headEquation, tailEquation] at mapEquation
                      | some resolvedTail =>
                          simp [headEquation, tailEquation] at mapEquation
                          subst resolvedAtoms
                          rcases List.mem_cons.mp resolvedMember with rfl | tailMember
                          · exact inductionHypothesis _ _ _
                              (stateOpFree_of_mem safe.2 (by simp)) headEquation
                          · exact tailInduction
                              (stateOpFree_expr_iff_list.mpr safe.2.2)
                              resolvedTail tailEquation tailMember

/-- Full runtime instantiation preserves the fragment. -/
theorem stateOpFree_instantiate {bindings : Bindings}
    (bindingsSafe : BindingsStateOpFree bindings) :
    ∀ atom, StateOpFree atom → StateOpFree (instantiate bindings atom)
  | .sym symbol, safe => by simpa [instantiate, Bindings.resolveAtom] using safe
  | .gnd ground, safe => by
      simpa [instantiate, Bindings.resolveAtom] using safe
  | .var name, safe => by
      simp only [instantiate, Bindings.resolveAtom]
      cases resolveEquation : Bindings.resolve bindings name with
      | none => simp
      | some resolved =>
          simp only [Option.getD_some]
          unfold Bindings.resolve at resolveEquation
          dsimp only at resolveEquation
          cases guard :
              ((Bindings.eqClassOrdered bindings name == [name]) &&
                (Bindings.classValues bindings name).isEmpty) with
          | true => simp [guard] at resolveEquation
          | false =>
              simp only [guard, Bool.false_eq_true, ↓reduceIte]
                at resolveEquation
              exact resolveAtomAux_stateOpFree bindingsSafe _ _ _ _
                (by simp [StateOpFree]) resolveEquation
  | .expr atoms, safe => by
      rw [instantiate, Bindings.resolveAtom, stateOpFree_expr_iff_list]
      rw [stateOpFreeList_iff_forall_mem]
      intro resolved member
      obtain ⟨atom, atomMember, rfl⟩ := List.mem_map.mp member
      exact stateOpFree_instantiate bindingsSafe atom
        (stateOpFree_of_mem safe.2 atomMember)

/-- Repeated fixpoint instantiation preserves the fragment at every fuel. -/
theorem stateOpFree_minimalResolveAtom {bindings : Bindings}
    (bindingsSafe : BindingsStateOpFree bindings) :
    ∀ fuel atom, StateOpFree atom →
      StateOpFree (Metta.Minimal.resolveAtom bindings fuel atom)
  | 0, atom, safe => safe
  | fuel + 1, atom, safe => by
      rw [Metta.Minimal.resolveAtom]
      split
      · exact safe
      · exact stateOpFree_minimalResolveAtom bindingsSafe fuel
          (instantiate bindings atom)
          (stateOpFree_instantiate bindingsSafe atom safe)

/-- Filtering binding relations cannot introduce an unsafe value. -/
theorem bindingsStateOpFree_filter {bindings : Bindings}
    (safe : BindingsStateOpFree bindings) (keep : BindingRel → Bool) :
    BindingsStateOpFree (bindings.filter keep) := by
  induction bindings with
  | nil => trivial
  | cons relation rest inductionHypothesis =>
      simp only [List.filter_cons]
      split
      · exact ⟨safe.1, inductionHypothesis safe.2⟩
      · exact inductionHypothesis safe.2

/-- Appending two safe binding presentations preserves safety. -/
theorem bindingsStateOpFree_append {left right : Bindings}
    (leftSafe : BindingsStateOpFree left)
    (rightSafe : BindingsStateOpFree right) :
    BindingsStateOpFree (left ++ right) := by
  induction left with
  | nil => exact rightSafe
  | cons relation rest inductionHypothesis =>
      exact ⟨leftSafe.1, inductionHypothesis leftSafe.2⟩

/-- A `filterMap` of binding relations is safe when every emitted relation is
safe. -/
theorem bindingsStateOpFree_filterMap {α : Type _} {items : List α}
    {emit : α → Option BindingRel}
    (safe : ∀ item ∈ items, ∀ relation,
      emit item = some relation → BindingRelStateOpFree relation) :
    BindingsStateOpFree (items.filterMap emit) := by
  induction items with
  | nil => trivial
  | cons item items inductionHypothesis =>
      simp only [List.filterMap_cons]
      cases equation : emit item with
      | none =>
          exact inductionHypothesis (by
            intro tail tailMember relation emitted
            exact safe tail (by simp [tailMember]) relation emitted)
      | some relation =>
          exact ⟨safe item (by simp) relation equation,
            inductionHypothesis (by
              intro tail tailMember output emitted
              exact safe tail (by simp [tailMember]) output emitted)⟩

/-- The raw public projection of a safe binding set keeps every emitted
resolved value safe.  Canonical merge replay is handled by
`MatcherProvenance`, where the generic merge-safety algebra is available. -/
theorem bindingsStateOpFree_restrictBndRaw {bindings : Bindings}
    (safe : BindingsStateOpFree bindings) (variables : List VarName) :
    BindingsStateOpFree (Metta.Minimal.restrictBndRaw variables bindings) := by
  unfold Metta.Minimal.restrictBndRaw
  apply bindingsStateOpFree_append
  · apply bindingsStateOpFree_filterMap
    intro name nameMember relation emitted
    dsimp only at emitted
    cases resolvedEquation : Metta.Minimal.resolveAtom bindings
        (bindings.length + 1) (.var name) with
    | var target =>
        by_cases same : (target == name) = true
        · simp [resolvedEquation, same] at emitted
        · simp [resolvedEquation, same] at emitted
          cases emitted
          trivial
    | sym symbol =>
        simp [resolvedEquation] at emitted
        cases emitted
        simpa [BindingRelStateOpFree, resolvedEquation] using
          stateOpFree_minimalResolveAtom safe
            (bindings.length + 1) (.var name) (by simp [StateOpFree])
    | gnd grounded =>
        simp [resolvedEquation] at emitted
        cases emitted
        simpa [BindingRelStateOpFree, resolvedEquation] using
          stateOpFree_minimalResolveAtom safe
            (bindings.length + 1) (.var name) (by simp [StateOpFree])
    | expr atoms =>
        simp [resolvedEquation] at emitted
        cases emitted
        simpa [BindingRelStateOpFree, resolvedEquation] using
          stateOpFree_minimalResolveAtom safe
            (bindings.length + 1) (.var name) (by simp [StateOpFree])
  · exact bindingsStateOpFree_filter safe _

/-! ## Stack constructors -/

/-- Every malformed-`unify` diagnostic begins with a fixed prefix longer than
any world-mutating instruction name. -/
private def unifyErrorPrefix : String :=
  "expected: (unify <atom> <pattern> <then> <else>), found: "

private theorem unifyBadArityMessage_length (atom : Atom) :
    unifyErrorPrefix.length ≤
      (Metta.Minimal.unifyBadArityMessage atom).length := by
  unfold unifyErrorPrefix Metta.Minimal.unifyBadArityMessage
  split
  · rename_i source argument pattern continuation
    simp only [String.length_append]
    have fixed :
        "expected: (unify <atom> <pattern> <then> <else>), found: ".length ≤
          "expected: (unify <atom> <pattern> <then> <else>), found: (unify ".length := by
      decide
    omega
  · simp only [String.length_append]
    omega

private theorem unifyBadArityMessage_ne_of_short (atom : Atom)
    (target : String) (short : target.length < unifyErrorPrefix.length) :
    Metta.Minimal.unifyBadArityMessage atom ≠ target := by
  intro equal
  have lower := unifyBadArityMessage_length atom
  have lengths := congrArg String.length equal
  omega

/-- A malformed-`unify` diagnostic cannot itself name a world mutation. -/
theorem unifyBadArityMessage_not_mutating (atom : Atom) :
    Metta.Minimal.unifyBadArityMessage atom ∉ worldMutatingHeads := by
  intro member
  simp only [worldMutatingHeads, List.mem_cons, List.not_mem_nil, or_false]
    at member
  rcases member with equal | equal | equal | equal | equal | equal | equal |
    equal | equal
  · exact unifyBadArityMessage_ne_of_short atom "new-state" (by decide) equal
  · exact unifyBadArityMessage_ne_of_short atom "change-state!" (by decide) equal
  · exact unifyBadArityMessage_ne_of_short atom "new-space" (by decide) equal
  · exact unifyBadArityMessage_ne_of_short atom "new-mork-space" (by decide) equal
  · exact unifyBadArityMessage_ne_of_short atom "fork-space" (by decide) equal
  · exact unifyBadArityMessage_ne_of_short atom "add-atom" (by decide) equal
  · exact unifyBadArityMessage_ne_of_short atom "remove-atom" (by decide) equal
  · exact unifyBadArityMessage_ne_of_short atom "bind!" (by decide) equal
  · exact unifyBadArityMessage_ne_of_short atom "import!" (by decide) equal

/-- Error construction adds only fixed non-mutating symbols around a safe
source atom. -/
theorem stateOpFree_errAtom {atom : Atom} (safe : StateOpFree atom)
    (message : String) (messageSafe : message ∉ worldMutatingHeads) :
    StateOpFree (Metta.Minimal.errAtom atom message) := by
  apply stateOpFree_expr_iff_list.mpr
  exact ⟨by simp [StateOpFree, worldMutatingHeads],
    ⟨safe, ⟨messageSafe, trivial⟩⟩⟩

/-- `finItem` preserves a safe continuation, result, and binding set. -/
theorem finItem_stateOpFree {stack : Metta.Minimal.Stack} {atom : Atom}
    {bindings : Bindings}
    (stackSafe : StackStateOpFree stack) (atomSafe : StateOpFree atom)
    (bindingsSafe : BindingsStateOpFree bindings) :
    ItemStateOpFree (Metta.Minimal.finItem stack atom bindings) :=
  ⟨⟨atomSafe, stackSafe⟩, bindingsSafe⟩

/-- Expanding an embedded control atom into its stack representation preserves
the state-free boundary.  The recursive `chain` and `function` cases inherit
the safety of their nested atom from the source expression; malformed controls
produce only fixed non-mutating diagnostics. -/
theorem atomToStack_stateOpFree :
    ∀ atom stack, StateOpFree atom → StackStateOpFree stack →
      StackStateOpFree (Metta.Minimal.atomToStack atom stack) := by
  intro atom stack atomSafe stackSafe
  fun_induction Metta.Minimal.atomToStack atom stack
  case case1 prev nested binderName template inductionHypothesis =>
    apply inductionHypothesis
    · exact stateOpFree_of_mem atomSafe.2 (by simp)
    · exact ⟨atomSafe, stackSafe⟩
  case case2 prev body inductionHypothesis =>
    apply inductionHypothesis
    · exact stateOpFree_of_mem atomSafe.2 (by simp)
    · exact ⟨atomSafe, stackSafe⟩
  case case3 prev left pattern thenBranch elseBranch =>
    exact ⟨atomSafe, stackSafe⟩
  case case4 prev tail notValid =>
    exact ⟨stateOpFree_errAtom atomSafe _ (by simp [worldMutatingHeads]),
      stackSafe⟩
  case case5 prev tail notValid =>
    exact ⟨stateOpFree_errAtom atomSafe _ (by simp [worldMutatingHeads]),
      stackSafe⟩
  case case6 prev tail notValid =>
    exact ⟨stateOpFree_errAtom atomSafe _
      (unifyBadArityMessage_not_mutating _), stackSafe⟩
  case case7 atom prev notChain notFunction notUnify notChainHead
      notFunctionHead notUnifyHead =>
    exact ⟨atomSafe, stackSafe⟩

/-- `evalResult` either finishes a safe result or opens its already-safe
function expression; in both cases the continuation remains safe. -/
theorem evalResult_stateOpFree {stack : Metta.Minimal.Stack} {atom : Atom}
    {bindings : Bindings}
    (stackSafe : StackStateOpFree stack) (atomSafe : StateOpFree atom)
    (bindingsSafe : BindingsStateOpFree bindings)
    (expandedSafe :
      StackStateOpFree (Metta.Minimal.atomToStack atom stack)) :
    ItemStateOpFree (Metta.Minimal.evalResult stack atom bindings) := by
  unfold Metta.Minimal.evalResult
  split
  · exact ⟨expandedSafe, bindingsSafe⟩
  · exact finItem_stateOpFree stackSafe atomSafe bindingsSafe

/-- Extracting a final pair preserves both the instantiated result and its
binding presentation. -/
theorem finalPair_stateOpFree {item : Metta.Minimal.Item}
    (safe : ItemStateOpFree item) :
    ResultStateOpFree (Metta.Minimal.finalPair item) := by
  rcases item with ⟨stack, bindings⟩
  cases stack with
  | nil =>
      exact ⟨by simp [Metta.Minimal.finalPair, Metta.Minimal.emptyA,
          worldMutatingHeads], trivial⟩
  | cons frame stack =>
      exact ⟨stateOpFree_instantiate safe.2 frame.atom safe.1.1,
        safe.2⟩

/-- Fuel exhaustion adds only the fixed `Error` and `StackOverflow` symbols
around the safe in-progress atom. -/
theorem exhaustedPair_stateOpFree {item : Metta.Minimal.Item}
    (safe : ItemStateOpFree item) :
    ResultStateOpFree (Metta.Minimal.exhaustedPair item) := by
  rcases item with ⟨stack, bindings⟩
  cases stack with
  | nil =>
      exact ⟨by simp [Metta.Minimal.exhaustedPair, Metta.Minimal.emptyA,
          worldMutatingHeads], safe.2⟩
  | cons frame stack =>
      constructor
      · apply stateOpFree_expr_iff_list.mpr
        exact ⟨by simp [StateOpFree, worldMutatingHeads],
          ⟨stateOpFree_instantiate safe.2 frame.atom safe.1.1,
            ⟨by simp [StateOpFree, worldMutatingHeads], trivial⟩⟩⟩
      · exact safe.2

/-- Positive canary: a closed substitution containing only an ordinary symbol
is safe and preserves an application. -/
theorem substApply_safe_canary :
    StateOpFree
      (Subst.apply [("x", .sym "A")] (.expr [.sym "f", .var "x"])) := by
  apply stateOpFree_substApply
  · intro name value member
    simp at member
    rcases member with ⟨rfl, rfl⟩
    simp [StateOpFree, worldMutatingHeads]
  · exact stateOpFree_expr_iff_list.mpr
      ⟨by simp [StateOpFree, worldMutatingHeads],
        ⟨by simp [StateOpFree], trivial⟩⟩

/-- Negative canary: allowing a mutation symbol as a substitution value would
violate closure by placing it in executable head position. -/
theorem subst_with_mutation_not_safe :
    ¬SubstStateOpFree [("x", .sym "add-atom")] := by
  intro safe
  exact not_stateOpFree_mutating_symbol
    (safe "x" (.sym "add-atom") (by simp))

end Mettapedia.Languages.MeTTa.HE.StateFreePreservation
