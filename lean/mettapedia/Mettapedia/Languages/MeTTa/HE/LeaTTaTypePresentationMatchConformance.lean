import Mettapedia.Languages.MeTTa.HE.HumanTypePresentationExact
import Mettapedia.Languages.MeTTa.HE.HumanTypePresentationNormal
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypeCanonicalSubst

/-!
# Syntactic type-match simulation state

The semantic type-binding invariant proves solution-theory soundness.  Exact
ordered evaluator candidates additionally require the concrete return-type
presentation.  `TypePresentationState` is the small simulation invariant for
that purpose: a human finite substitution and a repaired LeaTTa binding state
agree on every atom in one explicit finite observation scope.

The four published gradual-wildcard branches preserve this state without
changing either carrier.  The remaining structural branch is deliberately
separate: it must establish the same invariant through repaired reduced-type
matching rather than smuggling semantic equivalence into a syntactic claim.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationMatchConformance

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open HumanTypeSpec
open HumanTypePresentation
open HumanTypePresentationExact
open LeaTTaBridge
open LeaTTaHumanConformance
open LeaTTaTypeConformance
open LeaTTaTypeCanonicalSubst

/-- Exact agreement of the human finite presentation and LeaTTa's canonical
binding resolver on a declared finite observation scope.  The runtime field
threads the repaired loop/saturation invariants needed by the next reduced
match. -/
structure TypePresentationState
    (scope : List String) (human : TypeSubst)
    (lea : Metta.Bindings) : Prop where
  observation : ∀ atom : Atom,
    (∀ name, name ∈ TypeSubst.typeVars atom → name ∈ scope) →
      human.apply atom =
        fromLeaTTaAtom (Metta.instantiate lea (toLeaTTaAtom atom))
  runtime : LeaRuntimeBindingInvariant lea

/-- The reachable presentation lane additionally carries the normal form
that makes one-pass `bind` genuine substitution composition. -/
structure NormalTypePresentationState
    (scope : List String) (human : TypeSubst)
    (lea : Metta.Bindings) : Prop
    extends TypePresentationState scope human lea where
  normal : human.Normal

/-- Every repaired runtime state has a canonical finite presentation on any
chosen finite scope. -/
theorem TypePresentationState.canonical
    (scope : List String) {lea : Metta.Bindings}
    (runtime : LeaRuntimeBindingInvariant lea) :
    TypePresentationState scope
      (leaCanonicalTypeSubstOn lea scope) lea := by
  constructor
  · intro atom hscope
    exact leaCanonicalTypeSubstOn_apply_eq_instantiate
      lea scope atom hscope
  · exact runtime

/-- A declared return whose variables are in scope has exactly the same
human presentation as the atom emitted by LeaTTa instantiation. -/
theorem TypePresentationState.return_eq
    {scope : List String} {human : TypeSubst}
    {lea : Metta.Bindings}
    (state : TypePresentationState scope human lea)
    (declared : Atom)
    (hscope : ∀ name, name ∈ TypeSubst.typeVars declared → name ∈ scope) :
    human.apply declared =
      fromLeaTTaAtom (Metta.instantiate lea (toLeaTTaAtom declared)) :=
  state.observation declared hscope

/-- Empty human and LeaTTa presentations agree on every finite scope. -/
theorem typePresentationState_empty (scope : List String) :
    TypePresentationState scope [] Metta.Bindings.empty := by
  constructor
  · intro atom _
    simp [Metta.Bindings.empty, Metta.instantiate]
  · exact leaRuntimeBindingInvariant_empty

/-- Empty human and LeaTTa presentations establish the reachable normal
simulation state. -/
theorem normalTypePresentationState_empty (scope : List String) :
    NormalTypePresentationState scope [] Metta.Bindings.empty := by
  exact ⟨typePresentationState_empty scope, TypeSubst.normal_empty⟩

/-- The four top-level gradual wildcards return their incoming bindings
unchanged in both presentations. -/
theorem matchType_wildcard_presentation_sound
    {scope : List String} {humanIncoming : TypeSubst}
    {leaIncoming leaOutput : Metta.Bindings} {left right : Atom}
    (state : TypePresentationState scope humanIncoming leaIncoming)
    (wildcard :
      left = Atom.undefinedType ∨ right = Atom.undefinedType ∨
        left = Atom.atomType ∨ right = Atom.atomType)
    (success : Metta.Minimal.matchType leaIncoming
      (toLeaTTaAtom left) (toLeaTTaAtom right) = some leaOutput) :
    CorePlusR2TypePresentationMatchRel
        humanIncoming left right humanIncoming ∧
      TypePresentationState scope humanIncoming leaOutput := by
  rcases wildcard with hleftUndefined | hrightUndefined |
      hleftAtom | hrightAtom
  · subst left
    have hundefinedBeq :
        (Metta.Atom.sym "%Undefined%" ==
          Metta.Atom.sym "%Undefined%") = true := by decide
    have hsame : leaIncoming = leaOutput := by
      simpa [Metta.Minimal.matchType, toLeaTTaAtom,
        Atom.undefinedType, hundefinedBeq] using success
    subst leaOutput
    exact ⟨.undefinedLeft humanIncoming right, state⟩
  · subst right
    have hundefinedBeq :
        (Metta.Atom.sym "%Undefined%" ==
          Metta.Atom.sym "%Undefined%") = true := by decide
    have hsame : leaIncoming = leaOutput := by
      simpa [Metta.Minimal.matchType, toLeaTTaAtom,
        Atom.undefinedType, hundefinedBeq] using success
    subst leaOutput
    exact ⟨.undefinedRight humanIncoming left, state⟩
  · subst left
    have hatomBeq :
        (Metta.Atom.sym "Atom" == Metta.Atom.sym "Atom") = true := by
      decide
    have hsame : leaIncoming = leaOutput := by
      simpa [Metta.Minimal.matchType, toLeaTTaAtom,
        Atom.atomType, hatomBeq] using success
    subst leaOutput
    exact ⟨.atomLeft humanIncoming right, state⟩
  · subst right
    have hatomBeq :
        (Metta.Atom.sym "Atom" == Metta.Atom.sym "Atom") = true := by
      decide
    have hsame : leaIncoming = leaOutput := by
      simpa [Metta.Minimal.matchType, toLeaTTaAtom,
        Atom.atomType, hatomBeq] using success
    subst leaOutput
    exact ⟨.atomRight humanIncoming left, state⟩

/-- An ordinary non-expression type matches itself without changing either
presentation.  This is the base case of the remaining reduced-type
simulation. -/
theorem matchType_identical_leaf_presentation_sound
    {scope : List String} {humanIncoming : TypeSubst}
    {leaIncoming leaOutput : Metta.Bindings} {type : Atom}
    (state : TypePresentationState scope humanIncoming leaIncoming)
    (notExpression : ∀ atoms, type ≠ .expression atoms)
    (notUndefined : type ≠ Atom.undefinedType)
    (notAtom : type ≠ Atom.atomType)
    (success : Metta.Minimal.matchType leaIncoming
      (toLeaTTaAtom type) (toLeaTTaAtom type) = some leaOutput) :
    CorePlusR2TypePresentationMatchRel
        humanIncoming type type humanIncoming ∧
      TypePresentationState scope humanIncoming leaOutput := by
  have hundefined :
      (toLeaTTaAtom type == Metta.Atom.sym "%Undefined%") = false := by
    cases hbeq : (toLeaTTaAtom type ==
        Metta.Atom.sym "%Undefined%") with
    | false => rfl
    | true =>
        change Metta.Atom.beq (toLeaTTaAtom type)
          (Metta.Atom.sym "%Undefined%") = true at hbeq
        have heq : type = Atom.undefinedType :=
          (toLeaTTaAtom_beq_eq_true_iff type Atom.undefinedType).mp
            (by simpa [toLeaTTaAtom, Atom.undefinedType] using hbeq)
        exact (notUndefined heq).elim
  have hatom :
      (toLeaTTaAtom type == Metta.Atom.sym "Atom") = false := by
    cases hbeq : (toLeaTTaAtom type == Metta.Atom.sym "Atom") with
    | false => rfl
    | true =>
        change Metta.Atom.beq (toLeaTTaAtom type)
          (Metta.Atom.sym "Atom") = true at hbeq
        have heq : type = Atom.atomType :=
          (toLeaTTaAtom_beq_eq_true_iff type Atom.atomType).mp
            (by simpa [toLeaTTaAtom, Atom.atomType] using hbeq)
        exact (notAtom heq).elim
  rw [Metta.Minimal.matchType, hundefined, hatom] at success
  have hsame : leaIncoming = leaOutput := by
    cases type with
    | symbol name =>
        simpa [Metta.Minimal.matchReduced, Metta.matchAtoms,
          Metta.matchAtomsWith, Metta.Bindings.merge,
          state.runtime.loopFree, toLeaTTaAtom, hundefined] using success
    | var name =>
        simpa [Metta.Minimal.matchReduced, Metta.matchAtoms,
          Metta.matchAtomsWith, Metta.Bindings.merge,
          state.runtime.loopFree, toLeaTTaAtom, hundefined] using success
    | grounded value =>
        have hgroundBeq :
            (toLeaTTaGround value == toLeaTTaGround value) = true := by
          have hatomSelf :=
            (toLeaTTaAtom_beq_eq_true_iff
              (.grounded value) (.grounded value)).mpr rfl
          simpa [toLeaTTaAtom, Metta.Atom.beq] using hatomSelf
        have hgroundEquiv :
            Metta.Ground.equiv (toLeaTTaGround value)
              (toLeaTTaGround value) = true := by
          cases value <;>
            simpa [Metta.Ground.equiv, toLeaTTaGround] using hgroundBeq
        simpa [Metta.Minimal.matchReduced, Metta.matchAtoms,
          Metta.matchAtomsWith, Metta.Bindings.merge,
          state.runtime.loopFree, toLeaTTaAtom, hundefined,
          Metta.Atom.equiv, hgroundEquiv] using success
    | expression atoms => exact (notExpression atoms rfl).elim
  subst leaOutput
  have hleaf : ReducedTypeLeafShape type type := by
    cases type with
    | symbol => simp [ReducedTypeLeafShape]
    | var => simp [ReducedTypeLeafShape]
    | grounded => simp [ReducedTypeLeafShape]
    | expression atoms => exact (notExpression atoms rfl).elim
  constructor
  · apply CorePlusR2TypePresentationMatchRel.reduced
      notUndefined notUndefined notAtom notAtom
    exact ReducedTypePresentationMatchRel.ordinary
      notUndefined notUndefined hleaf rfl rfl
      (AppliedReducedTypeMatchRel.identical _ _)
  · exact state

/-! ## Boundary examples -/

/-- Positive: the gradual undefined type preserves an existing syntactic
presentation and its repaired runtime state. -/
theorem undefined_preserves_empty_presentation (actual : Atom) :
    CorePlusR2TypePresentationMatchRel [] Atom.undefinedType actual [] ∧
      TypePresentationState (TypeSubst.typeVars actual) []
        Metta.Bindings.empty := by
  constructor
  · exact .undefinedLeft [] actual
  · exact typePresentationState_empty _

private def initialVariableSymbolHuman : TypeSubst :=
  [("t", .symbol "A")]

private def initialVariableSymbolLea : Metta.Bindings :=
  [Metta.BindingRel.val "t" (.sym "A")]

/-- Positive reduced-leaf base case: the first variable-to-symbol match has
the same finite presentation as the repaired runtime binding. -/
theorem initial_variable_symbol_presentation :
    CorePlusR2TypePresentationMatchRel []
        (.var "t") (.symbol "A") initialVariableSymbolHuman ∧
      TypePresentationState ["t"] initialVariableSymbolHuman
        initialVariableSymbolLea := by
  have hloop : initialVariableSymbolLea.hasLoop = false := by
    simpa [initialVariableSymbolLea] using
      (Metta.Bindings.hasLoop_singleton_val_of_not_mem
        "t" (.sym "A") (by simp [Metta.Atom.vars]))
  have hmatch : initialVariableSymbolLea ∈
      Metta.matchAtoms (.var "t") (.sym "A") := by
    rw [Metta.matchAtoms]
    apply List.mem_filter.mpr
    constructor
    · simp [initialVariableSymbolLea, Metta.matchAtomsWith]
    · simp [hloop]
  have hmerge : initialVariableSymbolLea ∈
      Metta.Bindings.merge Metta.Bindings.empty
        initialVariableSymbolLea := by
    simp [initialVariableSymbolLea, Metta.Bindings.empty,
      Metta.Bindings.merge, Metta.Bindings.mergeOne,
      Metta.Bindings.addVarBinding, Metta.Bindings.addValRaw,
      Metta.Bindings.removeVal]
  have runtime : LeaRuntimeBindingInvariant initialVariableSymbolLea :=
    LeaRuntimeBindingInvariant.merge_matchOutput
      leaRuntimeBindingInvariant_empty
      (by simp [MettaAtomNoFloat])
      (by simp [MettaAtomNoFloat]) hmatch hmerge hloop
  constructor
  · apply CorePlusR2TypePresentationMatchRel.reduced
    · simp [Atom.undefinedType]
    · simp [Atom.undefinedType]
    · simp [Atom.atomType]
    · simp [Atom.atomType]
    apply ReducedTypePresentationMatchRel.ordinary
        (resolvedLeft := .var "t") (resolvedRight := .symbol "A")
    · simp [Atom.undefinedType]
    · simp [Atom.undefinedType]
    · simp [ReducedTypeLeafShape]
    · exact TypeSubst.apply_empty (.var "t")
    · exact TypeSubst.apply_empty (.symbol "A")
    · simpa [initialVariableSymbolHuman, TypeSubst.bind,
        TypeSubst.apply, TypeSubst.lookup, TypeSubst.erase] using
        (AppliedReducedTypeMatchRel.bindLeft
          (substitution := []) (name := "t") (right := .symbol "A")
          (by simp [TypeSubst.typeVars]))
  · have canonical := TypePresentationState.canonical ["t"] runtime
    have hsolution :
        leaClassSolution initialVariableSymbolLea "t" = .sym "A" := by
      simp [initialVariableSymbolLea, leaClassSolution,
      Metta.Bindings.resolve, Metta.Bindings.eqClassOrdered,
      Metta.Bindings.eqVarsInOrder, Metta.Bindings.classValues,
      Metta.Bindings.lookupVal, Metta.Bindings.eqClass,
      Metta.Bindings.eqClassAux, Metta.Bindings.eqStep,
      Metta.Bindings.resolveAtomAux,
      Metta.Bindings.resolutionFuel,
        Metta.Bindings.relationResolutionFuel, Metta.Atom.size]
    have hsubst :
        leaCanonicalTypeSubstOn initialVariableSymbolLea ["t"] =
          initialVariableSymbolHuman := by
      have herase : ["t"].eraseDups = ["t"] := by decide
      simp [leaCanonicalTypeSubstOn, initialVariableSymbolHuman,
        hsolution, fromLeaTTaAtom, herase]
    rw [hsubst] at canonical
    exact canonical

/-- The first concrete variable binding also establishes the normal form
needed by every later presentation-composition step. -/
theorem initial_variable_symbol_normal_state :
    NormalTypePresentationState ["t"] initialVariableSymbolHuman
      initialVariableSymbolLea := by
  refine ⟨initial_variable_symbol_presentation.2, ?_⟩
  simp [TypeSubst.Normal, TypeSubst.keys,
    TypeSubst.typeVars, initialVariableSymbolHuman]

/-- Negative: two distinct ordinary symbols do not enter any gradual
wildcard branch. -/
theorem distinct_symbols_are_not_top_level_wildcards :
    ¬((.symbol "A" : Atom) = Atom.undefinedType ∨
      (.symbol "B" : Atom) = Atom.undefinedType ∨
      (.symbol "A" : Atom) = Atom.atomType ∨
      (.symbol "B" : Atom) = Atom.atomType) := by
  decide

end Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationMatchConformance
