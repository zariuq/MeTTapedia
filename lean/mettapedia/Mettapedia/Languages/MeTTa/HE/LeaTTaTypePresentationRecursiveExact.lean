import Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationApplicationExact
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Conformance
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Freshness

/-!
# Recursive exact type-presentation conformance

This module lifts the exact finite-presentation correspondence from one
application candidate to repaired LeaTTa's complete recursive type lookup.
Independent child inference scopes are compared only up to their lawful
private alpha presentations; the parent application scan is exact in order,
multiplicity, and negative candidate positions.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationRecursiveExact

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Type
open Spec.Type.Conformance
open Spec.Type.Presentation
open Spec.Type.Presentation.Alpha
open Spec.Type.Presentation.ApplicationEquivariance
open Spec.Type.Presentation.Exact
open Spec.Type.RuntimeRefinement
open LeaTTaBridge
open LeaTTaTypeConformance
open LeaTTaTypePresentationExactConformance
open LeaTTaTypePresentationApplicationExact

/-- Complete ordered runtime type lists for every application argument,
decoded back into the independent atom language.  Keeping every candidate is
load-bearing: the repaired application inference enumerates their ordered
Cartesian product rather than selecting one head per argument. -/
def runtimeArgumentTypeLists
    (env : Metta.Minimal.MinEnv) (arguments : List Atom) :
    List (List Atom) :=
  arguments.map fun argument =>
    fromLeaTTaAtoms
      (Metta.Minimal.getTypes env (toLeaTTaAtom argument))

private theorem observedTypeAlphaList_refl (types : List Atom) :
    List.Forall₂ ObservedTypeAlphaRel types types := by
  induction types with
  | nil => exact List.Forall₂.nil
  | cons type types ih =>
      exact List.Forall₂.cons (ObservedTypeAlphaRel.refl type) ih

@[simp] private theorem observedTypes_publishedPackages
    (types : List Atom) :
    observedTypes (types.map publishedPackage) = types := by
  simp [observedTypes, publishedPackage,
    Spec.Type.Presentation.RuntimeTypePackage.published,
    Function.comp_def]

private theorem observedTypeAlpha_stateMonad
    {left right : Atom} (alpha : ObservedTypeAlphaRel left right) :
    ObservedTypeAlphaRel
      (.expression [.symbol "StateMonad", left])
      (.expression [.symbol "StateMonad", right]) := by
  rcases alpha with
    ⟨source,
      ⟨leftRename, leftInjective, leftEquation⟩,
      ⟨rightRename, rightInjective, rightEquation⟩⟩
  refine ⟨.expression [.symbol "StateMonad", source],
    ⟨leftRename, leftInjective, ?_⟩,
    ⟨rightRename, rightInjective, ?_⟩⟩
  · simp [renameTypeVars, leftEquation]
  · simp [renameTypeVars, rightEquation]

private theorem notStateValueShape_toLeaTTa
    {head : Atom} {tail : List Atom}
    (notState : NotStateValueShape head tail) :
    ∀ leaValue,
      toLeaTTaAtom head = .sym "StateValue" →
      toLeaTTaAtoms tail = [leaValue] → False := by
  intro leaValue headEquation tailEquation
  cases head with
  | symbol name =>
      simp [toLeaTTaAtom] at headEquation
      subst name
      cases tail with
      | nil => simp [toLeaTTaAtoms] at tailEquation
      | cons value values =>
          cases values with
          | nil =>
              simpa using notState value
          | cons next values =>
              simp [toLeaTTaAtoms] at tailEquation
  | var name => simp [toLeaTTaAtom] at headEquation
  | grounded value => simp [toLeaTTaAtom] at headEquation
  | expression atoms => simp [toLeaTTaAtom] at headEquation

/-- Every complete recursively computed argument list re-encodes exactly. -/
theorem runtimeArgumentTypeLists_roundtrip
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env) (arguments : List Atom) :
    (runtimeArgumentTypeLists env arguments).map toLeaTTaAtoms =
      arguments.map fun argument =>
        Metta.Minimal.getTypes env (toLeaTTaAtom argument) := by
  induction arguments with
  | nil => rfl
  | cons argument arguments ih =>
      simp only [runtimeArgumentTypeLists, List.map_cons,
        List.cons.injEq]
      constructor
      · apply toLeaTTaAtoms_fromLeaTTaAtoms_of_heImage
        apply leaAtomsHEImage_of_forall
        intro leaType member
        exact getTypes_result_heImage index
          (toLeaTTaAtom argument) leaType
          (leaAtomHEImage_toLeaTTaAtom argument) member
      · simpa [runtimeArgumentTypeLists] using ih

/-- The complete recursively computed operator list re-encodes exactly. -/
theorem runtimeOperatorTypes_roundtrip
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env) (operator : Atom) :
    toLeaTTaAtoms
        (fromLeaTTaAtoms
          (Metta.Minimal.getTypes env (toLeaTTaAtom operator))) =
      Metta.Minimal.getTypes env (toLeaTTaAtom operator) := by
  apply toLeaTTaAtoms_fromLeaTTaAtoms_of_heImage
  apply leaAtomsHEImage_of_forall
  intro leaType member
  exact getTypes_result_heImage index
    (toLeaTTaAtom operator) leaType
    (leaAtomHEImage_toLeaTTaAtom operator) member

private theorem freshenTypeCandidate_heImage
    (avoid : List String) (position : Nat) {atom : Metta.Atom}
    (image : LeaAtomHEImage atom) :
    LeaAtomHEImage
      (Metta.Minimal.freshenTypeCandidate avoid position atom) := by
  obtain ⟨native, rfl⟩ := image
  refine ⟨renameTypeVars
    (Metta.Minimal.captureAvoidingName avoid position) native, ?_⟩
  simpa [Metta.Minimal.freshenTypeCandidate] using
    toLeaTTaAtom_renameTypeVars
      (Metta.Minimal.captureAvoidingName avoid position) native

private theorem freshenArgumentTypes_heImage
    (avoid : List String) (position : Nat)
    {atoms : List Metta.Atom} (image : LeaAtomsHEImage atoms) :
    LeaAtomsHEImage
      (Metta.Minimal.freshenArgumentTypes avoid position atoms) := by
  induction atoms generalizing avoid position with
  | nil => exact leaAtomsHEImage_nil
  | cons atom atoms ih =>
      rw [leaAtomsHEImage_cons_iff] at image
      let fresh :=
        Metta.Minimal.freshenTypeCandidate avoid position atom
      change LeaAtomsHEImage
        (fresh :: Metta.Minimal.freshenArgumentTypes
          (avoid ++ fresh.vars) (position + 1) atoms)
      exact leaAtomsHEImage_cons
        (freshenTypeCandidate_heImage avoid position image.1)
        (ih (avoid ++ fresh.vars) (position + 1) image.2)

private theorem freshenOperatorTypes_heImage
    (avoid : List String) (position : Nat)
    {atoms : List Metta.Atom} (image : LeaAtomsHEImage atoms) :
    LeaAtomsHEImage
      (atoms.map (Metta.Minimal.freshenTypeCandidate avoid position)) := by
  apply leaAtomsHEImage_of_forall
  intro fresh member
  obtain ⟨raw, rawMember, rfl⟩ := List.mem_map.mp member
  exact freshenTypeCandidate_heImage avoid position
    (leaAtomsHEImage_of_mem image raw rawMember)

/-- Freshening a complete runtime `getTypes` list left-to-right preserves its
exact native/runtime round trip.  This is the list-valued companion of
`runtimeFreshenedOperatorTypes_roundtrip`; unlike operator selection, a type
cast gives successive candidates growing avoid sets. -/
theorem runtimeFreshenedArgumentTypes_roundtrip
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env) (atom : Atom)
    (avoid : List String) (position : Nat) :
    let runtimeCandidates := Metta.Minimal.freshenArgumentTypes avoid position
      (Metta.Minimal.getTypes env (toLeaTTaAtom atom))
    toLeaTTaAtoms (fromLeaTTaAtoms runtimeCandidates) = runtimeCandidates := by
  dsimp only
  apply toLeaTTaAtoms_fromLeaTTaAtoms_of_heImage
  apply freshenArgumentTypes_heImage
  apply leaAtomsHEImage_of_forall
  intro leaType member
  exact getTypes_result_heImage index
    (toLeaTTaAtom atom) leaType
    (leaAtomHEImage_toLeaTTaAtom atom) member

/-- Freshening the complete recursively computed operator list preserves the
exact native/runtime round trip.  This is the representation boundary needed
by the concrete selector: the specification may decode the runtime list,
reason about its private presentation, and re-encode the identical ordered
list without exposing the image-preservation implementation. -/
theorem runtimeFreshenedOperatorTypes_roundtrip
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env) (operator : Atom)
    (avoid : List String) (position : Nat) :
    let runtimeCandidates :=
      (Metta.Minimal.getTypes env (toLeaTTaAtom operator)).map
        (Metta.Minimal.freshenTypeCandidate avoid position)
    toLeaTTaAtoms (fromLeaTTaAtoms runtimeCandidates) = runtimeCandidates := by
  dsimp only
  apply toLeaTTaAtoms_fromLeaTTaAtoms_of_heImage
  apply freshenOperatorTypes_heImage
  apply leaAtomsHEImage_of_forall
  intro leaType member
  exact getTypes_result_heImage index
    (toLeaTTaAtom operator) leaType
    (leaAtomHEImage_toLeaTTaAtom operator) member

/-- A presentation avoiding a larger suffix also realizes the same global
operator presentation at the smaller prefix avoid set. -/
private theorem operatorAlphaVariants_weaken_append
    {avoid extra : List String} {sources targets : List Atom}
    (variants : OperatorAlphaVariantsRel
      (avoid ++ extra) sources targets) :
    OperatorAlphaVariantsRel avoid sources targets := by
  induction variants with
  | nil => exact OperatorAlphaVariantsRel.nil
  | @cons source target sources targets head tail ih =>
      rcases head with ⟨rename, injective, presentation, fresh⟩
      apply OperatorAlphaVariantsRel.cons
      · exact ⟨rename, injective, presentation, by
          intro name member avoidMember
          exact fresh name member
            (List.mem_append_left extra avoidMember)⟩
      · exact ih

/-- Avoiding every variable in every fresh argument choice implies the exact
operator/choice cell-scope law carried by the independent matrix relation. -/
private theorem operatorAlphaVariants_scopesSeparated
    {avoid : List String} {rawOperators freshOperators : List Atom}
    {freshArgumentChoices : List (List Atom)}
    (variants : OperatorAlphaVariantsRel
      (avoid ++ TypeSubst.typeVarsList freshArgumentChoices.flatten)
      rawOperators freshOperators) :
    ApplicationPackageScopesSeparated
      freshArgumentChoices freshOperators := by
  apply ApplicationPackageScopesSeparated.mk
  intro actualTypes actualMember operatorType operatorMember
  induction variants with
  | nil => simp at operatorMember
  | @cons source target sources targets head tail ih =>
      rcases List.mem_cons.mp operatorMember with rfl | tailMember
      · intro name operatorVar argumentVar
        apply
          (Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationExactConformance.TypeCandidateAlphaVariantRel.target_vars_fresh
            head name operatorVar)
        apply List.mem_append_right avoid
        obtain ⟨argument, argumentMember, nameMember⟩ :=
          Spec.Type.Presentation.Freshness.exists_mem_of_mem_typeVarsList
            argumentVar
        apply
          Spec.Type.Presentation.Freshness.typeVars_mem_typeVarsList_of_mem
            (atom := argument)
            (atoms := freshArgumentChoices.flatten)
        · exact List.mem_flatten.mpr
            ⟨actualTypes, actualMember, argumentMember⟩
        · exact nameMember
      · exact ih tailMember

/-- The one-candidate filter in the repaired runtime, named locally so the
recursive `getTypes` equation can be compared with the native presentation
bridge without duplicating its match tree in theorem statements. -/
private def leaRuntimeApplicationCandidate
    (actualTypes : List Metta.Atom) (operatorType : Metta.Atom) :
    Option Metta.Atom :=
  match operatorType with
  | .expr (.sym "->" :: types) =>
      match types.getLast? with
      | none => none
      | some returnType =>
          match Metta.Minimal.matchApplicationTypeArguments
              Metta.Bindings.empty types.dropLast actualTypes with
          | some bindings => some (Metta.instantiate bindings returnType)
          | none => none
  | _ => none

private theorem runtimeApplicationCandidate_decode
    {actualTypes : List Metta.Atom} {operatorType : Metta.Atom}
    (actualImage : LeaAtomsHEImage actualTypes)
    (operatorImage : LeaAtomHEImage operatorType) :
    runtimeApplicationCandidate
        (fromLeaTTaAtoms actualTypes) (fromLeaTTaAtom operatorType) =
      leaRuntimeApplicationCandidate actualTypes operatorType := by
  obtain ⟨nativeActuals, actualEquation⟩ := actualImage
  obtain ⟨nativeOperator, operatorEquation⟩ := operatorImage
  rw [← actualEquation, ← operatorEquation]
  simp only [fromLeaTTaAtoms_toLeaTTaAtoms,
    fromLeaTTaAtom_toLeaTTaAtom]
  cases nativeOperator with
  | symbol name => simp [runtimeApplicationCandidate,
      leaRuntimeApplicationCandidate, toLeaTTaAtom]
  | var name => simp [runtimeApplicationCandidate,
      leaRuntimeApplicationCandidate, toLeaTTaAtom]
  | grounded value => simp [runtimeApplicationCandidate,
      leaRuntimeApplicationCandidate, toLeaTTaAtom]
  | expression atoms =>
      cases atoms with
      | nil => simp [runtimeApplicationCandidate,
          leaRuntimeApplicationCandidate, toLeaTTaAtom, toLeaTTaAtoms]
      | cons head tail =>
          cases head with
          | symbol name =>
              by_cases arrow : name = "->"
              · subst name
                cases last : tail.getLast? with
                | none =>
                    simp [runtimeApplicationCandidate,
                      leaRuntimeApplicationCandidate, toLeaTTaAtom,
                      toLeaTTaAtoms, last]
                | some returnType =>
                    simp [runtimeApplicationCandidate,
                      leaRuntimeApplicationCandidate, toLeaTTaAtom,
                      toLeaTTaAtoms, last]
                    cases matchEquation :
                        Metta.Minimal.matchApplicationTypeArguments
                          Metta.Bindings.empty
                          (tail.map toLeaTTaAtom).dropLast
                          (nativeActuals.map toLeaTTaAtom) <;>
                      simp
              · simp [runtimeApplicationCandidate,
                  leaRuntimeApplicationCandidate, toLeaTTaAtom,
                  toLeaTTaAtoms, arrow]
          | var name => simp [runtimeApplicationCandidate,
              leaRuntimeApplicationCandidate, toLeaTTaAtom,
              toLeaTTaAtoms]
          | grounded value => simp [runtimeApplicationCandidate,
              leaRuntimeApplicationCandidate, toLeaTTaAtom,
              toLeaTTaAtoms]
          | expression atoms => simp [runtimeApplicationCandidate,
              leaRuntimeApplicationCandidate, toLeaTTaAtom,
              toLeaTTaAtoms]

private theorem runtimeApplicationCandidates_decode
    {actualTypes operatorTypes : List Metta.Atom}
    (actualImage : LeaAtomsHEImage actualTypes)
    (operatorImage : LeaAtomsHEImage operatorTypes) :
    runtimeApplicationCandidates
        (fromLeaTTaAtoms actualTypes) (fromLeaTTaAtoms operatorTypes) =
      operatorTypes.filterMap
        (leaRuntimeApplicationCandidate actualTypes) := by
  induction operatorTypes with
  | nil => rfl
  | cons operator operators ih =>
      rw [leaAtomsHEImage_cons_iff] at operatorImage
      simp only [runtimeApplicationCandidates, fromLeaTTaAtoms,
        List.filterMap_cons]
      rw [runtimeApplicationCandidate_decode actualImage operatorImage.1]
      have tailEquation := ih operatorImage.2
      unfold runtimeApplicationCandidates at tailEquation
      rw [tailEquation]

/-! ## Ordered Cartesian and matrix transport algebra -/

private abbrev TypePackageAlphaRel
    (left right : TypePackage) : Prop :=
  ObservedTypeAlphaRel left.observed right.observed

/-- Pointwise relations lift through the spec's row-major Cartesian product
without changing order or multiplicity. -/
private theorem orderedCartesian_rel
    {α β : Type} {relation : α → β → Prop}
    {left : List (List α)} {right : List (List β)}
    (related : List.Forall₂ (List.Forall₂ relation) left right) :
    List.Forall₂ (List.Forall₂ relation)
      (orderedCartesian left) (orderedCartesian right) := by
  induction related with
  | nil => exact List.Forall₂.cons List.Forall₂.nil List.Forall₂.nil
  | @cons leftChoices rightChoices leftTail rightTail head tail ih =>
      simpa [orderedCartesian] using
        (List.rel_flatMap head (fun _ _ headRelated =>
          List.rel_map
            (fun _ _ tailRelated =>
              List.Forall₂.cons headRelated tailRelated)
            ih))

/-- Mapping every candidate commutes with the row-major Cartesian product. -/
private theorem orderedCartesian_map
    {α β : Type} (mapCandidate : α → β) :
    ∀ choices : List (List α),
      (orderedCartesian choices).map (List.map mapCandidate) =
        orderedCartesian (choices.map (List.map mapCandidate)) := by
  intro choices
  induction choices with
  | nil => rfl
  | cons choices rest ih =>
      simp only [List.map_cons, orderedCartesian, List.map_flatMap,
        List.flatMap_map]
      apply List.flatMap_congr
      intro choice _member
      rw [← ih]
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro tail _tailMember
      rfl

/-- The independent row-major Cartesian combinator has exactly the repaired
runtime helper's enumeration, including duplicates. -/
private theorem orderedCartesian_eq_runtimeCartesian
    {α : Type} (choices : List (List α)) :
    orderedCartesian choices = Metta.Minimal.cartesian choices := by
  induction choices with
  | nil => rfl
  | cons choices rest ih =>
      simp [orderedCartesian, Metta.Minimal.cartesian, ih]

/-- Every Cartesian choice contains one entry per source list. -/
private theorem orderedCartesian_choice_length
    {choices : List (List Atom)} {choice : List Atom}
    (member : choice ∈ orderedCartesian choices) :
    choice.length = choices.length := by
  induction choices generalizing choice with
  | nil =>
      simp [orderedCartesian] at member
      subst choice
      rfl
  | cons candidates choices ih =>
      simp only [orderedCartesian, List.mem_flatMap, List.mem_map]
        at member
      obtain ⟨candidate, _candidateMember, tail, tailMember, rfl⟩ := member
      simp [ih tailMember]

/-- Alpha-related raw choice lists may reuse the same fresh target choices. -/
private theorem argumentChoiceVariants_transport_left
    {avoid : List String}
    {left right targets : List (List Atom)}
    (alpha : List.Forall₂ (List.Forall₂ ObservedTypeAlphaRel)
      left right)
    (variants : List.Forall₂ (ArgumentAlphaVariantsRel avoid)
      right targets) :
    List.Forall₂ (ArgumentAlphaVariantsRel avoid)
      left targets := by
  induction alpha generalizing targets with
  | nil =>
      cases variants
      exact List.Forall₂.nil
  | @cons leftHead rightHead leftTail rightTail headAlpha tailAlpha ih =>
      cases variants with
      | @cons _ target _ targets headVariant tailVariants =>
          exact List.Forall₂.cons
            (ArgumentAlphaVariantsRel.transport_left
              headAlpha headVariant)
            (ih tailVariants)

/-- Deterministic repaired-runtime freshening realizes the independent
argument-family contract pointwise over every ordered Cartesian choice. -/
private theorem freshenArgumentChoices_alphaVariants
    (avoid : List String) (choices : List (List Atom)) :
    List.Forall₂ (ArgumentAlphaVariantsRel avoid) choices
      (choices.map fun choice =>
        fromLeaTTaAtoms
          (Metta.Minimal.freshenArgumentTypes avoid 0
            (toLeaTTaAtoms choice))) := by
  induction choices with
  | nil => exact List.Forall₂.nil
  | cons choice choices ih =>
      exact List.Forall₂.cons
        (freshenArgumentTypes_alphaVariants avoid 0 choice) ih

/-- Pointwise freshening preserves native-image provenance for every
Cartesian argument choice. -/
private theorem freshenArgumentChoices_heImage
    (avoid : List String) (choices : List (List Atom)) :
    ∀ freshChoice ∈ choices.map (fun choice =>
      Metta.Minimal.freshenArgumentTypes avoid 0
        (toLeaTTaAtoms choice)),
      LeaAtomsHEImage freshChoice := by
  intro freshChoice member
  obtain ⟨choice, _choiceMember, rfl⟩ := List.mem_map.mp member
  apply freshenArgumentTypes_heImage
  exact ⟨choice, rfl⟩

/-- The runtime's distinct positional counters realize the independent
cell-scope law for every Cartesian choice.  Operator position is the common
arity; argument positions are strictly below it. -/
private theorem runtimeFreshenedScopesSeparated
    {rawArgumentChoices : List (List Atom)} {rawOperators : List Atom}
    (argumentAvoid functionAvoid : List String) (arity : Nat)
    (choiceLength : ∀ choice ∈ rawArgumentChoices,
      choice.length = arity) :
    ApplicationPackageScopesSeparated
      (rawArgumentChoices.map fun choice =>
        fromLeaTTaAtoms
          (Metta.Minimal.freshenArgumentTypes argumentAvoid 0
            (toLeaTTaAtoms choice)))
      (fromLeaTTaAtoms
        ((toLeaTTaAtoms rawOperators).map
          (Metta.Minimal.freshenTypeCandidate functionAvoid arity))) := by
  apply ApplicationPackageScopesSeparated.mk
  intro freshArguments freshArgumentsMember
    freshOperator freshOperatorMember name operatorVar argumentVar
  obtain ⟨rawArguments, rawArgumentsMember, rfl⟩ :=
    List.mem_map.mp freshArgumentsMember
  simp only [toLeaTTaAtoms_eq_map, List.map_map,
    fromLeaTTaAtoms_eq_map] at freshOperatorMember
  obtain ⟨rawOperator, rawOperatorMember, rfl⟩ :=
    List.mem_map.mp freshOperatorMember
  let leaFreshOperator := Metta.Minimal.freshenTypeCandidate
    functionAvoid arity (toLeaTTaAtom rawOperator)
  let leaFreshArguments := Metta.Minimal.freshenArgumentTypes
    argumentAvoid 0 (toLeaTTaAtoms rawArguments)
  have operatorImage : LeaAtomHEImage leaFreshOperator := by
    exact freshenTypeCandidate_heImage functionAvoid arity
      (leaAtomHEImage_toLeaTTaAtom rawOperator)
  have argumentsImage : LeaAtomsHEImage leaFreshArguments := by
    exact freshenArgumentTypes_heImage argumentAvoid 0
      ⟨rawArguments, rfl⟩
  have operatorRoundtrip :
      toLeaTTaAtom (fromLeaTTaAtom leaFreshOperator) =
        leaFreshOperator :=
    toLeaTTaAtom_fromLeaTTaAtom_of_heImage operatorImage
  have argumentsRoundtrip :
      toLeaTTaAtoms (fromLeaTTaAtoms leaFreshArguments) =
        leaFreshArguments :=
    toLeaTTaAtoms_fromLeaTTaAtoms_of_heImage argumentsImage
  have operatorMember : name ∈ leaFreshOperator.vars := by
    rw [← operatorRoundtrip,
      toLeaTTaAtom_vars_eq_typeVars]
    exact operatorVar
  have argumentsMember : name ∈ leaFreshArguments.flatMap Metta.Atom.vars := by
    have translated := argumentVar
    rw [← toLeaTTaAtoms_vars_eq_typeVars] at translated
    rw [argumentsRoundtrip] at translated
    exact translated
  have disjoint :=
    Metta.Minimal.freshenTypeCandidate_disjoint_from_positioned_arguments
      argumentAvoid functionAvoid (toLeaTTaAtom rawOperator)
        (toLeaTTaAtoms rawArguments)
  rw [show (toLeaTTaAtoms rawArguments).length = arity by
    simpa [toLeaTTaAtoms_eq_map] using
      choiceLength rawArguments rawArgumentsMember] at disjoint
  exact disjoint name operatorMember argumentsMember

/-- Filtering option rows preserves the alpha relation of every surviving
package and drops paired failures at identical positions. -/
private theorem outcomeAlpha_filterMap
    {left right : List (Option TypePackage)}
    (alpha : List.Forall₂ ApplicationPackageOutcomeAlphaRel left right) :
    List.Forall₂ TypePackageAlphaRel
      (left.filterMap id) (right.filterMap id) := by
  induction alpha with
  | nil => exact List.Forall₂.nil
  | @cons leftHead rightHead leftTail rightTail headAlpha tailAlpha ih =>
      cases leftHead with
      | none =>
          cases rightHead with
          | none => simpa using ih
          | some rightPackage =>
              simp [ApplicationPackageOutcomeAlphaRel] at headAlpha
      | some leftPackage =>
          cases rightHead with
          | none =>
              simp [ApplicationPackageOutcomeAlphaRel] at headAlpha
          | some rightPackage =>
              change TypePackageAlphaRel leftPackage rightPackage at headAlpha
              exact List.Forall₂.cons headAlpha ih

/-- One complete argument-choice row transports across two independently
freshened, cell-separated presentations without changing failure positions. -/
private theorem applicationPackageOutcomeRow_transport
    {leftArgumentAvoid rightArgumentAvoid : List String}
    {leftOperatorAvoid rightOperatorAvoid : List String}
    {rawArgumentChoices leftArgumentChoices rightArgumentChoices :
      List (List Atom)}
    {rawOperator leftOperator rightOperator : Atom}
    {leftOutcomes : List (Option TypePackage)}
    (leftArgumentVariants :
      List.Forall₂ (ArgumentAlphaVariantsRel leftArgumentAvoid)
        rawArgumentChoices leftArgumentChoices)
    (rightArgumentVariants :
      List.Forall₂ (ArgumentAlphaVariantsRel rightArgumentAvoid)
        rawArgumentChoices rightArgumentChoices)
    (leftOperatorVariant : TypeCandidateAlphaVariantRel
      leftOperatorAvoid rawOperator leftOperator)
    (rightOperatorVariant : TypeCandidateAlphaVariantRel
      rightOperatorAvoid rawOperator rightOperator)
    (leftSeparated : ∀ actualTypes ∈ leftArgumentChoices,
      AtomVarsFreshFromAtoms leftOperator actualTypes)
    (rightSeparated : ∀ actualTypes ∈ rightArgumentChoices,
      AtomVarsFreshFromAtoms rightOperator actualTypes)
    (leftRow : List.Forall₂
      (fun actualTypes outcome =>
        ApplicationPackageOutcomeRel actualTypes leftOperator outcome)
      leftArgumentChoices leftOutcomes) :
    ∃ rightOutcomes,
      List.Forall₂
        (fun actualTypes outcome =>
          ApplicationPackageOutcomeRel actualTypes rightOperator outcome)
        rightArgumentChoices rightOutcomes ∧
      List.Forall₂ ApplicationPackageOutcomeAlphaRel
        leftOutcomes rightOutcomes := by
  induction leftArgumentVariants generalizing
      rightArgumentChoices leftOutcomes with
  | nil =>
      cases rightArgumentVariants
      cases leftRow
      exact ⟨[], List.Forall₂.nil, List.Forall₂.nil⟩
  | @cons rawArguments leftArguments rawArgumentTail leftArgumentTail
      leftHeadVariant leftTailVariants ih =>
      cases rightArgumentVariants with
      | @cons _ rightArguments _ rightArgumentTail
          rightHeadVariant rightTailVariants =>
          cases leftRow with
          | @cons _ leftOutcome _ leftOutcomeTail
              leftHeadOutcome leftTailOutcomes =>
              have leftHeadSeparated : AtomVarsFreshFromAtoms
                  leftOperator leftArguments :=
                leftSeparated leftArguments (by simp)
              have rightHeadSeparated : AtomVarsFreshFromAtoms
                  rightOperator rightArguments :=
                rightSeparated rightArguments (by simp)
              obtain ⟨rightOutcome, rightHeadOutcome, headAlpha⟩ :=
                applicationPackageOutcome_transport_separated_scopes
                  leftHeadVariant rightHeadVariant
                  leftOperatorVariant rightOperatorVariant
                  leftHeadSeparated rightHeadSeparated leftHeadOutcome
              have leftTailSeparated : ∀ actualTypes ∈ leftArgumentTail,
                  AtomVarsFreshFromAtoms leftOperator actualTypes := by
                intro actualTypes member
                exact leftSeparated actualTypes (by simp [member])
              have rightTailSeparated : ∀ actualTypes ∈ rightArgumentTail,
                  AtomVarsFreshFromAtoms rightOperator actualTypes := by
                intro actualTypes member
                exact rightSeparated actualTypes (by simp [member])
              obtain ⟨rightOutcomeTail, rightTailOutcomes, tailAlpha⟩ :=
                ih rightTailVariants leftTailSeparated
                  rightTailSeparated leftTailOutcomes
              exact ⟨rightOutcome :: rightOutcomeTail,
                List.Forall₂.cons rightHeadOutcome rightTailOutcomes,
                List.Forall₂.cons headAlpha tailAlpha⟩

/-- The complete operator-major matrix transports through two lawful
freshening families.  Row order, cell failures, multiplicity, and flattened
result order are all preserved exactly; only private spellings vary. -/
private theorem applicationPackageMatrix_transport
    {leftArgumentAvoid rightArgumentAvoid : List String}
    {leftOperatorAvoid rightOperatorAvoid : List String}
    {rawArgumentChoices leftArgumentChoices rightArgumentChoices :
      List (List Atom)}
    {rawOperators leftOperators rightOperators : List Atom}
    {leftResults : List TypePackage}
    (leftArgumentVariants :
      List.Forall₂ (ArgumentAlphaVariantsRel leftArgumentAvoid)
        rawArgumentChoices leftArgumentChoices)
    (rightArgumentVariants :
      List.Forall₂ (ArgumentAlphaVariantsRel rightArgumentAvoid)
        rawArgumentChoices rightArgumentChoices)
    (leftOperatorVariants : OperatorAlphaVariantsRel
      leftOperatorAvoid rawOperators leftOperators)
    (rightOperatorVariants : OperatorAlphaVariantsRel
      rightOperatorAvoid rawOperators rightOperators)
    (leftSeparated : ApplicationPackageScopesSeparated
      leftArgumentChoices leftOperators)
    (rightSeparated : ApplicationPackageScopesSeparated
      rightArgumentChoices rightOperators)
    (leftMatrix : ApplicationPackageMatrixRel
      leftArgumentChoices leftOperators leftResults) :
    ∃ rightResults,
      ApplicationPackageMatrixRel
        rightArgumentChoices rightOperators rightResults ∧
      List.Forall₂ TypePackageAlphaRel leftResults rightResults := by
  obtain ⟨leftRows, leftRowsRel, rfl⟩ := leftMatrix
  induction leftOperatorVariants generalizing rightOperators leftRows with
  | nil =>
      cases rightOperatorVariants
      cases leftRowsRel
      exact ⟨[], ⟨[], List.Forall₂.nil, rfl⟩, List.Forall₂.nil⟩
  | @cons rawOperator leftOperator rawOperatorTail leftOperatorTail
      leftHeadVariant leftTailVariants ih =>
      cases rightOperatorVariants with
      | @cons _ rightOperator _ rightOperatorTail
          rightHeadVariant rightTailVariants =>
          cases leftRowsRel with
          | @cons _ leftRow _ leftRowTail leftHeadRow leftTailRows =>
              obtain ⟨leftOutcomes, leftOutcomeRel, leftRowEquation⟩ :=
                leftHeadRow
              have leftHeadSeparated : ∀ actualTypes ∈ leftArgumentChoices,
                  AtomVarsFreshFromAtoms leftOperator actualTypes := by
                intro actualTypes actualMember name operatorVar
                exact ApplicationPackageScopesSeparated.atom leftSeparated
                  actualMember (by simp) operatorVar
              have rightHeadSeparated : ∀ actualTypes ∈ rightArgumentChoices,
                  AtomVarsFreshFromAtoms rightOperator actualTypes := by
                intro actualTypes actualMember name operatorVar
                exact ApplicationPackageScopesSeparated.atom rightSeparated
                  actualMember (by simp) operatorVar
              obtain ⟨rightOutcomes, rightOutcomeRel, outcomeAlpha⟩ :=
                applicationPackageOutcomeRow_transport
                  leftArgumentVariants rightArgumentVariants
                  leftHeadVariant rightHeadVariant
                  leftHeadSeparated rightHeadSeparated leftOutcomeRel
              let rightRow := rightOutcomes.filterMap id
              have rightHeadRow : ApplicationPackageOutcomeRowRel
                  rightArgumentChoices rightOperator rightRow :=
                ⟨rightOutcomes, rightOutcomeRel, rfl⟩
              have headAlpha : List.Forall₂ TypePackageAlphaRel
                  leftRow rightRow := by
                rw [← leftRowEquation]
                exact outcomeAlpha_filterMap outcomeAlpha
              have leftTailSeparated : ApplicationPackageScopesSeparated
                  leftArgumentChoices leftOperatorTail := by
                intro actualTypes actualMember operatorType operatorMember
                exact leftSeparated actualTypes actualMember operatorType
                  (by simp [operatorMember])
              have rightTailSeparated : ApplicationPackageScopesSeparated
                  rightArgumentChoices rightOperatorTail := by
                intro actualTypes actualMember operatorType operatorMember
                exact rightSeparated actualTypes actualMember operatorType
                  (by simp [operatorMember])
              obtain ⟨rightTailResults, rightTailMatrix, tailAlpha⟩ :=
                ih rightTailVariants leftTailSeparated
                  rightTailSeparated leftRowTail leftTailRows
              obtain ⟨rightRows, rightRowsRel, rightRowsEquation⟩ :=
                rightTailMatrix
              refine ⟨rightRow ++ rightTailResults,
                ⟨rightRow :: rightRows,
                  List.Forall₂.cons rightHeadRow rightRowsRel, ?_⟩, ?_⟩
              · simpa using congrArg (rightRow ++ ·) rightRowsEquation
              · exact List.rel_append headAlpha tailAlpha

/-- Concrete operator-major, argument-choice-minor candidate matrix. -/
private def runtimeApplicationCandidateMatrix
    (argumentChoices : List (List Atom))
    (operatorTypes : List Atom) : List Metta.Atom :=
  operatorTypes.flatMap fun operatorType =>
    argumentChoices.filterMap fun actualTypes =>
      runtimeApplicationCandidate actualTypes operatorType

/-- Native LeaTTa spelling of the same operator-major matrix. -/
private def leaRuntimeApplicationCandidateMatrix
    (argumentChoices : List (List Metta.Atom))
    (operatorTypes : List Metta.Atom) : List Metta.Atom :=
  operatorTypes.flatMap fun operatorType =>
    argumentChoices.filterMap fun actualTypes =>
      leaRuntimeApplicationCandidate actualTypes operatorType

private theorem runtimeApplicationCandidateRow_decode
    {argumentChoices : List (List Metta.Atom)}
    {operatorType : Metta.Atom}
    (argumentImage : ∀ actualTypes ∈ argumentChoices,
      LeaAtomsHEImage actualTypes)
    (operatorImage : LeaAtomHEImage operatorType) :
    (argumentChoices.map fromLeaTTaAtoms).filterMap
        (fun actualTypes => runtimeApplicationCandidate
          actualTypes (fromLeaTTaAtom operatorType)) =
      argumentChoices.filterMap
        (fun actualTypes =>
          leaRuntimeApplicationCandidate actualTypes operatorType) := by
  induction argumentChoices with
  | nil => rfl
  | cons actualTypes argumentChoices ih =>
      simp only [List.map_cons, List.filterMap_cons]
      rw [runtimeApplicationCandidate_decode
        (argumentImage actualTypes (by simp)) operatorImage]
      rw [ih]
      intro choice member
      exact argumentImage choice (by simp [member])

/-- Decoding an image-valued native matrix commutes with every cell while
preserving the exact operator-major enumeration. -/
private theorem runtimeApplicationCandidateMatrix_decode
    {argumentChoices : List (List Metta.Atom)}
    {operatorTypes : List Metta.Atom}
    (argumentImage : ∀ actualTypes ∈ argumentChoices,
      LeaAtomsHEImage actualTypes)
    (operatorImage : LeaAtomsHEImage operatorTypes) :
    runtimeApplicationCandidateMatrix
        (argumentChoices.map fromLeaTTaAtoms)
        (fromLeaTTaAtoms operatorTypes) =
      leaRuntimeApplicationCandidateMatrix
        argumentChoices operatorTypes := by
  induction operatorTypes with
  | nil => rfl
  | cons operatorType operatorTypes ih =>
      rw [leaAtomsHEImage_cons_iff] at operatorImage
      simp only [runtimeApplicationCandidateMatrix,
        leaRuntimeApplicationCandidateMatrix, fromLeaTTaAtoms,
        List.flatMap_cons]
      rw [runtimeApplicationCandidateRow_decode
        argumentImage operatorImage.1]
      apply congrArg
        (List.filterMap
          (fun actualTypes =>
            leaRuntimeApplicationCandidate actualTypes operatorType)
          argumentChoices ++ ·)
      simpa [runtimeApplicationCandidateMatrix,
        leaRuntimeApplicationCandidateMatrix] using ih operatorImage.2

/-- A complete spec row over separated cells is emitted by the repaired
runtime row with exactly the same successes, order, and multiplicity. -/
private theorem applicationPackageOutcomeRow_complete
    {argumentChoices : List (List Atom)} {operatorType : Atom}
    {results : List TypePackage}
    (row : ApplicationPackageOutcomeRowRel
      argumentChoices operatorType results)
    (separated : ∀ actualTypes ∈ argumentChoices,
      VarsDisjoint operatorType (.expression actualTypes)) :
    List.Forall₂ ObservedTypeAlphaRel (observedTypes results)
      (fromLeaTTaAtoms
        (argumentChoices.filterMap fun actualTypes =>
          runtimeApplicationCandidate actualTypes operatorType)) := by
  obtain ⟨outcomes, outcomeRel, outcomeEquation⟩ := row
  subst results
  induction outcomeRel with
  | nil => exact List.Forall₂.nil
  | @cons actualTypes outcome argumentTail outcomeTail
      headOutcome tailOutcomes ih =>
      have headSeparated := separated actualTypes (by simp)
      have tailSeparated : ∀ choice ∈ argumentTail,
          VarsDisjoint operatorType (.expression choice) := by
        intro choice member
        exact separated choice (by simp [member])
      cases headOutcome with
      | failure noSuccess =>
          have runtimeNone :=
            (runtimeApplicationCandidate_none_iff headSeparated).mpr
              noSuccess
          simpa [runtimeNone] using ih tailSeparated
      | @success result success =>
          obtain ⟨leaResult, runtimeSome, alpha⟩ :=
            runtimeApplicationCandidate_complete success headSeparated
          simpa [runtimeSome, observedTypes, fromLeaTTaAtoms] using
            List.Forall₂.cons alpha (ih tailSeparated)

/-- Matrix-level completeness of the repaired runtime.  This is the single
consumer of one-cell completeness; recursive type lookup never unfolds the
candidate matcher again. -/
private theorem applicationPackageMatrix_complete
    {argumentChoices : List (List Atom)} {operatorTypes : List Atom}
    {results : List TypePackage}
    (matrix : ApplicationPackageMatrixRel
      argumentChoices operatorTypes results)
    (separated : ∀ actualTypes ∈ argumentChoices,
      ∀ operatorType ∈ operatorTypes,
        VarsDisjoint operatorType (.expression actualTypes)) :
    List.Forall₂ ObservedTypeAlphaRel (observedTypes results)
      (fromLeaTTaAtoms
        (runtimeApplicationCandidateMatrix
          argumentChoices operatorTypes)) := by
  obtain ⟨rows, rowsRel, rowsEquation⟩ := matrix
  subst results
  induction rowsRel with
  | nil => exact List.Forall₂.nil
  | @cons operatorType row operatorTail rowTail headRow tailRows ih =>
      have headSeparated : ∀ actualTypes ∈ argumentChoices,
          VarsDisjoint operatorType (.expression actualTypes) := by
        intro actualTypes member
        exact separated actualTypes member operatorType (by simp)
      have tailSeparated : ∀ actualTypes ∈ argumentChoices,
          ∀ candidate ∈ operatorTail,
            VarsDisjoint candidate (.expression actualTypes) := by
        intro actualTypes actualMember candidate candidateMember
        exact separated actualTypes actualMember candidate
          (by simp [candidateMember])
      have headAlpha :=
        applicationPackageOutcomeRow_complete headRow headSeparated
      have tailAlpha := ih tailSeparated
      simpa [observedTypes, runtimeApplicationCandidateMatrix,
        fromLeaTTaAtoms] using List.rel_append headAlpha tailAlpha

/-- The independent cell-scope predicate is exactly the structural
disjointness premise required by one-candidate runtime completeness after
translation. -/
private theorem applicationPackageScopesSeparated_varsDisjoint
    {argumentChoices : List (List Atom)} {operatorTypes : List Atom}
    (separated : ApplicationPackageScopesSeparated
      argumentChoices operatorTypes) :
    ∀ actualTypes ∈ argumentChoices,
      ∀ operatorType ∈ operatorTypes,
        VarsDisjoint operatorType (.expression actualTypes) := by
  intro actualTypes actualMember operatorType operatorMember
    name operatorVar argumentVar
  rw [toLeaTTaAtom_vars_eq_typeVars] at operatorVar
  rw [toLeaTTaAtom_vars_eq_typeVars] at argumentVar
  exact ApplicationPackageScopesSeparated.atom separated actualMember
    operatorMember operatorVar (by
      simpa [TypeSubst.typeVars, TypeSubst.typeVarsList] using argumentVar)

/-- Transporting an independent matrix to a concrete separated presentation
and realizing it in the repaired runtime is one reusable boundary theorem. -/
private theorem applicationPackageMatrix_transport_complete
    {leftArgumentAvoid rightArgumentAvoid : List String}
    {leftOperatorAvoid rightOperatorAvoid : List String}
    {rawArgumentChoices leftArgumentChoices rightArgumentChoices :
      List (List Atom)}
    {rawOperators leftOperators rightOperators : List Atom}
    {leftResults : List TypePackage}
    (leftArgumentVariants :
      List.Forall₂ (ArgumentAlphaVariantsRel leftArgumentAvoid)
        rawArgumentChoices leftArgumentChoices)
    (rightArgumentVariants :
      List.Forall₂ (ArgumentAlphaVariantsRel rightArgumentAvoid)
        rawArgumentChoices rightArgumentChoices)
    (leftOperatorVariants : OperatorAlphaVariantsRel
      leftOperatorAvoid rawOperators leftOperators)
    (rightOperatorVariants : OperatorAlphaVariantsRel
      rightOperatorAvoid rawOperators rightOperators)
    (leftSeparated : ApplicationPackageScopesSeparated
      leftArgumentChoices leftOperators)
    (rightSeparated : ApplicationPackageScopesSeparated
      rightArgumentChoices rightOperators)
    (leftMatrix : ApplicationPackageMatrixRel
      leftArgumentChoices leftOperators leftResults) :
    List.Forall₂ ObservedTypeAlphaRel (observedTypes leftResults)
      (fromLeaTTaAtoms
        (runtimeApplicationCandidateMatrix
          rightArgumentChoices rightOperators)) := by
  obtain ⟨rightResults, rightMatrix, matrixAlpha⟩ :=
    applicationPackageMatrix_transport
      leftArgumentVariants rightArgumentVariants
      leftOperatorVariants rightOperatorVariants
      leftSeparated rightSeparated leftMatrix
  exact observedTypeAlphaList_trans
    (by simpa [observedTypes, TypePackageAlphaRel] using matrixAlpha)
    (applicationPackageMatrix_complete rightMatrix
      (applicationPackageScopesSeparated_varsDisjoint rightSeparated))

/-- Recursive child exactness, deterministic positional freshening, and the
matrix boundary compose without mentioning `getTypes`' implementation tree.
The remaining executable proof is therefore only the final list equation. -/
private theorem applicationPackageMatrix_concrete_alpha
    {specArgumentLists runtimeArgumentLists : List (List Atom)}
    {specOperators runtimeOperators : List Atom}
    {leftArgumentChoices : List (List Atom)}
    {leftOperators : List Atom} {leftResults : List TypePackage}
    {leftArgumentAvoid leftOperatorAvoid : List String}
    (argumentAlpha : List.Forall₂ (List.Forall₂ ObservedTypeAlphaRel)
      specArgumentLists runtimeArgumentLists)
    (operatorAlpha : List.Forall₂ ObservedTypeAlphaRel
      specOperators runtimeOperators)
    (leftArgumentVariants : List.Forall₂
      (ArgumentAlphaVariantsRel leftArgumentAvoid)
      (orderedCartesian specArgumentLists) leftArgumentChoices)
    (leftOperatorVariants : OperatorAlphaVariantsRel
      leftOperatorAvoid specOperators leftOperators)
    (leftSeparated : ApplicationPackageScopesSeparated
      leftArgumentChoices leftOperators)
    (leftMatrix : ApplicationPackageMatrixRel
      leftArgumentChoices leftOperators leftResults)
    (argumentAvoid functionAvoid : List String) (arity : Nat)
    (arityEquation : runtimeArgumentLists.length = arity) :
    let runtimeRawChoices := orderedCartesian runtimeArgumentLists
    let runtimeFreshChoices := runtimeRawChoices.map fun choice =>
      fromLeaTTaAtoms
        (Metta.Minimal.freshenArgumentTypes argumentAvoid 0
          (toLeaTTaAtoms choice))
    let runtimeFreshOperators := fromLeaTTaAtoms
      ((toLeaTTaAtoms runtimeOperators).map
        (Metta.Minimal.freshenTypeCandidate functionAvoid arity))
    List.Forall₂ ObservedTypeAlphaRel (observedTypes leftResults)
      (fromLeaTTaAtoms
        (runtimeApplicationCandidateMatrix
          runtimeFreshChoices runtimeFreshOperators)) := by
  dsimp only
  have rawChoiceAlpha := orderedCartesian_rel argumentAlpha
  have runtimeArgumentBase := freshenArgumentChoices_alphaVariants
    argumentAvoid (orderedCartesian runtimeArgumentLists)
  have runtimeArgumentVariants : List.Forall₂
      (ArgumentAlphaVariantsRel argumentAvoid)
      (orderedCartesian specArgumentLists)
      ((orderedCartesian runtimeArgumentLists).map fun choice =>
        fromLeaTTaAtoms
          (Metta.Minimal.freshenArgumentTypes argumentAvoid 0
            (toLeaTTaAtoms choice))) :=
    argumentChoiceVariants_transport_left rawChoiceAlpha runtimeArgumentBase
  have runtimeOperatorBase := freshenOperatorTypes_alphaVariants
    functionAvoid arity runtimeOperators
  have runtimeOperatorVariants : OperatorAlphaVariantsRel
      functionAvoid specOperators
      (fromLeaTTaAtoms
        ((toLeaTTaAtoms runtimeOperators).map
          (Metta.Minimal.freshenTypeCandidate functionAvoid arity))) :=
    OperatorAlphaVariantsRel.transport_left
      operatorAlpha runtimeOperatorBase
  have runtimeSeparated := runtimeFreshenedScopesSeparated
    (rawArgumentChoices := orderedCartesian runtimeArgumentLists)
    (rawOperators := runtimeOperators)
    argumentAvoid functionAvoid arity (by
      intro choice member
      rw [← arityEquation]
      exact orderedCartesian_choice_length member)
  exact applicationPackageMatrix_transport_complete
    leftArgumentVariants runtimeArgumentVariants
    leftOperatorVariants runtimeOperatorVariants
    leftSeparated runtimeSeparated leftMatrix

/-- The decoded concrete matrix is definitionally the repaired runtime's
operator-major `flatMap` over its ordered Cartesian argument choices. -/
private theorem runtimeApplicationCandidateMatrix_encode
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    (head : Atom) (tail : List Atom)
    (argumentAvoid functionAvoid : List String) (arity : Nat) :
    let runtimeRawArgumentLists := runtimeArgumentTypeLists env tail
    let runtimeRawArgumentChoices :=
      orderedCartesian runtimeRawArgumentLists
    let leaFreshArgumentChoices :=
      runtimeRawArgumentChoices.map fun choice =>
        Metta.Minimal.freshenArgumentTypes argumentAvoid 0
          (toLeaTTaAtoms choice)
    let runtimeFreshArgumentChoices :=
      leaFreshArgumentChoices.map fromLeaTTaAtoms
    let runtimeRawOperators := fromLeaTTaAtoms
      (Metta.Minimal.getTypes env (toLeaTTaAtom head))
    let leaFreshOperators :=
      ((toLeaTTaAtoms runtimeRawOperators).map
        (Metta.Minimal.freshenTypeCandidate functionAvoid arity))
    let runtimeFreshOperators := fromLeaTTaAtoms leaFreshOperators
    runtimeApplicationCandidateMatrix
        runtimeFreshArgumentChoices runtimeFreshOperators =
      ((Metta.Minimal.getTypes env (toLeaTTaAtom head)).map
        (Metta.Minimal.freshenTypeCandidate functionAvoid arity)).flatMap
          fun operatorType =>
            (Metta.Minimal.cartesian
              ((toLeaTTaAtoms tail).map
                (Metta.Minimal.getTypes env))).filterMap fun rawArguments =>
              leaRuntimeApplicationCandidate
                (Metta.Minimal.freshenArgumentTypes
                  argumentAvoid 0 rawArguments)
                operatorType := by
  dsimp only
  let runtimeRawArgumentChoices :=
    orderedCartesian (runtimeArgumentTypeLists env tail)
  let leaFreshArgumentChoices := runtimeRawArgumentChoices.map fun choice =>
    Metta.Minimal.freshenArgumentTypes argumentAvoid 0
      (toLeaTTaAtoms choice)
  let runtimeRawOperators := fromLeaTTaAtoms
    (Metta.Minimal.getTypes env (toLeaTTaAtom head))
  let leaFreshOperators :=
    (toLeaTTaAtoms runtimeRawOperators).map
      (Metta.Minimal.freshenTypeCandidate functionAvoid arity)
  have argumentImage : ∀ actualTypes ∈ leaFreshArgumentChoices,
      LeaAtomsHEImage actualTypes := by
    simpa [leaFreshArgumentChoices, runtimeRawArgumentChoices] using
      freshenArgumentChoices_heImage argumentAvoid
        (orderedCartesian (runtimeArgumentTypeLists env tail))
  have operatorImage : LeaAtomsHEImage leaFreshOperators := by
    apply freshenOperatorTypes_heImage
    exact ⟨runtimeRawOperators, rfl⟩
  have decoded := runtimeApplicationCandidateMatrix_decode
    argumentImage operatorImage
  have rawListRoundtrip := runtimeArgumentTypeLists_roundtrip index tail
  have rawChoiceRoundtrip :
      (orderedCartesian (runtimeArgumentTypeLists env tail)).map
          toLeaTTaAtoms =
        Metta.Minimal.cartesian
          ((toLeaTTaAtoms tail).map (Metta.Minimal.getTypes env)) := by
    calc
      (orderedCartesian (runtimeArgumentTypeLists env tail)).map
          toLeaTTaAtoms =
          (orderedCartesian (runtimeArgumentTypeLists env tail)).map
            (List.map toLeaTTaAtom) := by
        apply List.map_congr_left
        intro choice _member
        exact toLeaTTaAtoms_eq_map choice
      _ =
          orderedCartesian
            ((runtimeArgumentTypeLists env tail).map
              (List.map toLeaTTaAtom)) :=
        orderedCartesian_map toLeaTTaAtom
          (runtimeArgumentTypeLists env tail)
      _ = orderedCartesian
          ((runtimeArgumentTypeLists env tail).map toLeaTTaAtoms) := by
        apply congrArg orderedCartesian
        apply List.map_congr_left
        intro choice _member
        exact (toLeaTTaAtoms_eq_map choice).symm
      _ = orderedCartesian
          (tail.map fun argument =>
            Metta.Minimal.getTypes env (toLeaTTaAtom argument)) :=
        congrArg orderedCartesian rawListRoundtrip
      _ = Metta.Minimal.cartesian
          ((toLeaTTaAtoms tail).map (Metta.Minimal.getTypes env)) := by
        rw [orderedCartesian_eq_runtimeCartesian]
        simp [toLeaTTaAtoms_eq_map, List.map_map, Function.comp_def]
  have freshChoiceEquation : leaFreshArgumentChoices =
      (Metta.Minimal.cartesian
        ((toLeaTTaAtoms tail).map
          (Metta.Minimal.getTypes env))).map
            (Metta.Minimal.freshenArgumentTypes argumentAvoid 0) := by
    calc
      leaFreshArgumentChoices =
          ((orderedCartesian (runtimeArgumentTypeLists env tail)).map
            toLeaTTaAtoms).map
              (Metta.Minimal.freshenArgumentTypes argumentAvoid 0) := by
        simp [leaFreshArgumentChoices, runtimeRawArgumentChoices,
          List.map_map, Function.comp_def]
      _ = _ := congrArg
        (List.map (Metta.Minimal.freshenArgumentTypes argumentAvoid 0))
        rawChoiceRoundtrip
  have operatorRoundtrip := runtimeOperatorTypes_roundtrip index head
  have freshOperatorEquation : leaFreshOperators =
      (Metta.Minimal.getTypes env (toLeaTTaAtom head)).map
        (Metta.Minimal.freshenTypeCandidate functionAvoid arity) := by
    simpa [leaFreshOperators, runtimeRawOperators] using congrArg
      (List.map (Metta.Minimal.freshenTypeCandidate functionAvoid arity))
      operatorRoundtrip
  calc
    runtimeApplicationCandidateMatrix
        (leaFreshArgumentChoices.map fromLeaTTaAtoms)
        (fromLeaTTaAtoms leaFreshOperators) =
      leaRuntimeApplicationCandidateMatrix
        leaFreshArgumentChoices leaFreshOperators := decoded
    _ = ((Metta.Minimal.getTypes env (toLeaTTaAtom head)).map
        (Metta.Minimal.freshenTypeCandidate functionAvoid arity)).flatMap
          fun operatorType =>
            (Metta.Minimal.cartesian
              ((toLeaTTaAtoms tail).map
                (Metta.Minimal.getTypes env))).filterMap fun rawArguments =>
              leaRuntimeApplicationCandidate
                (Metta.Minimal.freshenArgumentTypes
                  argumentAvoid 0 rawArguments)
                operatorType := by
      rw [freshChoiceEquation, freshOperatorEquation]
      simp [leaRuntimeApplicationCandidateMatrix,
        List.filterMap_map, Function.comp_def]

/-- An expression with no published direct annotation also has no concrete
`exprTypes` entry.  This packages the only list-shape argument needed before
the recursive inference boundary is exposed. -/
private theorem expressionTypes_filter_eq_nil
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {head : Atom} {tail : List Atom}
    (noAnnotations : AnnotationTypesRel
      (.expression (head :: tail)) space.atoms []) :
    env.exprTypes.filter (fun entry =>
      entry.1 ==
        .expr (toLeaTTaAtom head :: toLeaTTaAtoms tail)) = [] := by
  have mapped := index.expressionTypes head tail
  have noAnnotationsEquation :
      getAnnotatedTypes space (.expression (head :: tail)) = [] := by
    simpa [Space.ofList] using
      annotationTypesRel_eq_getAnnotatedTypes noAnnotations
  rw [noAnnotationsEquation] at mapped
  have nativeMapped :
      (env.exprTypes.filter (fun entry =>
        entry.1 ==
          .expr (toLeaTTaAtom head :: toLeaTTaAtoms tail))).map
            (fun entry => entry.2) = [] := by
    simpa [toLeaTTaAtom, toLeaTTaAtoms_eq_map] using mapped
  exact List.map_eq_nil_iff.mp nativeMapped

/-- With direct annotations excluded, repaired LeaTTa's expression lookup is
exactly the operator-major candidate matrix followed by the explicit
`%Undefined%` fallback.  All recursive/freshening implementation detail is
quarantined in this one executable characterization theorem. -/
private theorem getTypes_expression_eq_candidateMatrix
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    (head : Atom) (tail : List Atom)
    (notState : NotStateValueShape head tail)
    (nativeNoDirect : env.exprTypes.filter (fun entry =>
      entry.1 ==
        .expr (toLeaTTaAtom head :: toLeaTTaAtoms tail)) = []) :
    let runtimeRawArgumentLists := runtimeArgumentTypeLists env tail
    let runtimeRawArgumentChoices :=
      orderedCartesian runtimeRawArgumentLists
    let leaAllRawArgumentTypes :=
      ((toLeaTTaAtoms tail).map
        (Metta.Minimal.getTypes env)).flatten
    let runtimeRawOperators := fromLeaTTaAtoms
      (Metta.Minimal.getTypes env (toLeaTTaAtom head))
    let argumentAvoid := Metta.Minimal.typeInferenceAvoid env
      (.expr (toLeaTTaAtom head :: toLeaTTaAtoms tail))
      (Metta.Minimal.getTypes env (toLeaTTaAtom head) ++
        leaAllRawArgumentTypes)
    let functionAvoid := argumentAvoid ++
      leaAllRawArgumentTypes.flatMap Metta.Atom.vars
    let runtimeFreshArgumentChoices :=
      runtimeRawArgumentChoices.map fun choice =>
        fromLeaTTaAtoms
          (Metta.Minimal.freshenArgumentTypes argumentAvoid 0
            (toLeaTTaAtoms choice))
    let runtimeFreshOperators := fromLeaTTaAtoms
      ((toLeaTTaAtoms runtimeRawOperators).map
        (Metta.Minimal.freshenTypeCandidate
          functionAvoid tail.length))
    Metta.Minimal.getTypes env
        (toLeaTTaAtom (.expression (head :: tail))) =
      match runtimeApplicationCandidateMatrix
          runtimeFreshArgumentChoices runtimeFreshOperators with
      | [] => [.sym "%Undefined%"]
      | results => results := by
  dsimp only
  have encoded := runtimeApplicationCandidateMatrix_encode
    index head tail
      (Metta.Minimal.typeInferenceAvoid env
        (.expr (toLeaTTaAtom head :: toLeaTTaAtoms tail))
        (Metta.Minimal.getTypes env (toLeaTTaAtom head) ++
          ((toLeaTTaAtoms tail).map
            (Metta.Minimal.getTypes env)).flatten))
      (Metta.Minimal.typeInferenceAvoid env
          (.expr (toLeaTTaAtom head :: toLeaTTaAtoms tail))
          (Metta.Minimal.getTypes env (toLeaTTaAtom head) ++
            ((toLeaTTaAtoms tail).map
              (Metta.Minimal.getTypes env)).flatten) ++
        ((toLeaTTaAtoms tail).map
          (Metta.Minimal.getTypes env)).flatten.flatMap Metta.Atom.vars)
      tail.length
  rw [show toLeaTTaAtom (.expression (head :: tail)) =
      .expr (toLeaTTaAtom head :: toLeaTTaAtoms tail) by
    simp [toLeaTTaAtom, toLeaTTaAtoms_eq_map]]
  rw [Metta.Minimal.getTypes.eq_10 env
    (toLeaTTaAtom head) (toLeaTTaAtoms tail)
    (notStateValueShape_toLeaTTa notState), nativeNoDirect]
  simp only [toLeaTTaAtoms_eq_map, List.length_map]
  have fallbackEncoded := congrArg
    (fun results => match results with
      | [] => [Metta.Atom.sym "%Undefined%"]
      | values => values)
    encoded
  convert fallbackEncoded.symm using 1
  all_goals
    simp only [leaRuntimeApplicationCandidate,
      toLeaTTaAtoms_eq_map, List.flatMap_id,
      List.map_map, Function.comp_def, Metta.Bindings.empty]
  all_goals rfl

/-! ## Totality of the executable-independent presentation relation -/

private theorem applicationPackageOutcomeRel_exists
    (actualTypes : List Atom) (operatorType : Atom) :
    ∃ output, ApplicationPackageOutcomeRel
      actualTypes operatorType output := by
  classical
  by_cases success : ∃ result,
      ApplicationPackageSuccessRel actualTypes operatorType result
  · obtain ⟨result, resultSuccess⟩ := success
    exact ⟨some result, ApplicationPackageOutcomeRel.success resultSuccess⟩
  · refine ⟨none, ApplicationPackageOutcomeRel.failure ?_⟩
    intro result resultSuccess
    exact success ⟨result, resultSuccess⟩

private theorem applicationPackageOutcomeRowRel_exists
    (argumentChoices : List (List Atom)) (operatorType : Atom) :
    ∃ results,
      ApplicationPackageOutcomeRowRel
        argumentChoices operatorType results := by
  induction argumentChoices with
  | nil =>
      exact ⟨[], [], List.Forall₂.nil, rfl⟩
  | cons actualTypes argumentChoices ih =>
      obtain ⟨tailResults, tailOutcomes, tailRel, tailEquation⟩ := ih
      obtain ⟨outcome, outcomeRel⟩ :=
        applicationPackageOutcomeRel_exists actualTypes operatorType
      cases outcome with
      | none =>
          refine ⟨tailResults, none :: tailOutcomes,
            List.Forall₂.cons outcomeRel tailRel, ?_⟩
          simpa using tailEquation
      | some result =>
          refine ⟨result :: tailResults, some result :: tailOutcomes,
            List.Forall₂.cons outcomeRel tailRel, ?_⟩
          simpa using congrArg (result :: ·) tailEquation

private theorem applicationPackageMatrixRel_exists
    (argumentChoices : List (List Atom)) : ∀ operatorTypes,
    ∃ results,
      ApplicationPackageMatrixRel
        argumentChoices operatorTypes results := by
  intro operatorTypes
  induction operatorTypes with
  | nil => exact ⟨[], [], List.Forall₂.nil, rfl⟩
  | cons operatorType operatorTypes ih =>
      obtain ⟨row, rowRel⟩ :=
        applicationPackageOutcomeRowRel_exists
          argumentChoices operatorType
      obtain ⟨tailResults, tailRows, tailRel, tailEquation⟩ := ih
      refine ⟨row ++ tailResults, row :: tailRows,
        List.Forall₂.cons rowRel tailRel, ?_⟩
      simpa using congrArg (row ++ ·) tailEquation

private theorem argumentAlphaChoiceVariantsRel_exists
    (avoid : List String) : ∀ choices : List (List Atom),
    ∃ freshChoices,
      List.Forall₂ (ArgumentAlphaVariantsRel avoid)
        choices freshChoices := by
  intro choices
  induction choices with
  | nil => exact ⟨[], List.Forall₂.nil⟩
  | cons choice choices ih =>
      let freshChoice := fromLeaTTaAtoms
        (Metta.Minimal.freshenArgumentTypes avoid 0
          (toLeaTTaAtoms choice))
      have variant : ArgumentAlphaVariantsRel
          avoid choice freshChoice := by
        simpa [freshChoice] using
          freshenArgumentTypes_alphaVariants avoid 0 choice
      obtain ⟨freshChoices, variants⟩ := ih
      exact ⟨freshChoice :: freshChoices,
        List.Forall₂.cons variant variants⟩

/-- The exact package-presentation relation is total on the independent atom
language.  Concrete freshening is used only as an existence witness for the
finite alpha contracts; it does not occur in the relation being constructed. -/
theorem runtimeTypePackages_exists (space : Space) : ∀ atom : Atom,
    ∃ packages, RuntimeTypePackagesRel space atom packages := by
  intro atom
  induction atom using Atom.rec
      (motive_2 := fun atoms =>
        ∃ packageLists : List (List TypePackage),
          List.Forall₂ (RuntimeTypePackagesRel space)
            atoms packageLists) with
  | symbol name =>
      let annotated := getAnnotatedTypes
        (Space.ofList space.atoms) (.symbol name)
      have annotation : AnnotationTypesRel (.symbol name)
          space.atoms annotated :=
        annotationTypesRel_getAnnotatedTypes (.symbol name) space.atoms
      by_cases nonempty : annotated ≠ []
      · exact ⟨annotated.map publishedPackage,
          RuntimeTypePackagesRel.symbolKnown annotation nonempty⟩
      · have empty : annotated = [] := by simpa using nonempty
        rw [empty] at annotation
        exact ⟨[publishedPackage Atom.undefinedType],
          RuntimeTypePackagesRel.symbolUndefined annotation⟩
  | var name =>
      exact ⟨[publishedPackage Atom.undefinedType],
        RuntimeTypePackagesRel.variable name⟩
  | grounded value =>
      cases value with
      | int value =>
          exact ⟨[publishedPackage (.symbol "Number")],
            RuntimeTypePackagesRel.grounded
              (IntrinsicGroundedTypeRel.int value)⟩
      | string value =>
          exact ⟨[publishedPackage (.symbol "String")],
            RuntimeTypePackagesRel.grounded
              (IntrinsicGroundedTypeRel.string value)⟩
      | bool value =>
          exact ⟨[publishedPackage (.symbol "Bool")],
            RuntimeTypePackagesRel.grounded
              (IntrinsicGroundedTypeRel.bool value)⟩
      | custom type payload =>
          exact ⟨[publishedPackage (.symbol type)],
            RuntimeTypePackagesRel.grounded
              (IntrinsicGroundedTypeRel.custom type payload)⟩
  | expression atoms allTypes =>
      cases atoms with
      | nil =>
          exact ⟨[publishedPackage Atom.undefinedType],
            RuntimeTypePackagesRel.unit⟩
      | cons head tail =>
          obtain ⟨packageLists, packageTypes⟩ := allTypes
          cases packageTypes with
          | @cons _ headPackages _ tailPackageLists headTypes tailTypes =>
              by_cases stateShape : head = .symbol "StateValue" ∧
                  ∃ value, tail = [value]
              · obtain ⟨rfl, value, rfl⟩ := stateShape
                cases tailTypes with
                | @cons _ valuePackages _ _ valueTypes emptyTypes =>
                    cases emptyTypes
                    obtain ⟨content, remaining, packagesEquation⟩ :=
                      List.exists_cons_of_ne_nil valueTypes.nonempty
                    subst valuePackages
                    exact ⟨[stateMonadPackage content],
                      RuntimeTypePackagesRel.stateValue valueTypes⟩
              · have notState : NotStateValueShape head tail := by
                  intro value
                  by_cases headEquation : head = .symbol "StateValue"
                  · exact Or.inr (by
                      intro tailEquation
                      exact stateShape
                        ⟨headEquation, value, tailEquation⟩)
                  · exact Or.inl headEquation
                let expression := Atom.expression (head :: tail)
                let annotated := getAnnotatedTypes
                  (Space.ofList space.atoms) expression
                have annotation : AnnotationTypesRel expression
                    space.atoms annotated :=
                  annotationTypesRel_getAnnotatedTypes
                    expression space.atoms
                by_cases nonempty : annotated ≠ []
                · exact ⟨annotated.map publishedPackage,
                    RuntimeTypePackagesRel.expressionKnown
                      notState annotation nonempty⟩
                · have empty : annotated = [] := by
                    simpa using nonempty
                  rw [empty] at annotation
                  have noAnnotations : AnnotationTypesRel
                      (.expression (head :: tail)) space.atoms [] := by
                    simpa [expression] using annotation
                  let rawArgumentLists :=
                    tailPackageLists.map observedTypes
                  let rawArgumentChoices :=
                    orderedCartesian rawArgumentLists
                  let rawOperators := observedTypes headPackages
                  let avoid := inferenceAvoidNames space expression
                    (rawOperators ++ rawArgumentLists.flatten)
                  obtain ⟨freshArgumentChoices, argumentVariants⟩ :=
                    argumentAlphaChoiceVariantsRel_exists
                      avoid rawArgumentChoices
                  let operatorAvoid :=
                    avoid ++
                      TypeSubst.typeVarsList rawArgumentLists.flatten
                  let separatedOperatorAvoid :=
                    operatorAvoid ++
                      TypeSubst.typeVarsList freshArgumentChoices.flatten
                  let freshOperators := fromLeaTTaAtoms
                    ((toLeaTTaAtoms rawOperators).map
                      (Metta.Minimal.freshenTypeCandidate
                        separatedOperatorAvoid tail.length))
                  have separatedOperatorVariants : OperatorAlphaVariantsRel
                      separatedOperatorAvoid rawOperators freshOperators := by
                    simpa [freshOperators] using
                      freshenOperatorTypes_alphaVariants
                        separatedOperatorAvoid tail.length rawOperators
                  have operatorVariants : OperatorAlphaVariantsRel
                      operatorAvoid rawOperators freshOperators := by
                    apply operatorAlphaVariants_weaken_append
                      (avoid := operatorAvoid)
                      (extra := TypeSubst.typeVarsList
                        freshArgumentChoices.flatten)
                    exact separatedOperatorVariants
                  have scopesSeparated : ApplicationPackageScopesSeparated
                      freshArgumentChoices freshOperators := by
                    apply operatorAlphaVariants_scopesSeparated
                      (avoid := operatorAvoid)
                    exact separatedOperatorVariants
                  obtain ⟨results, scan⟩ :=
                    applicationPackageMatrixRel_exists
                      freshArgumentChoices freshOperators
                  by_cases resultsNonempty : results ≠ []
                  · exact ⟨results,
                      RuntimeTypePackagesRel.expressionInferred
                        notState noAnnotations headTypes tailTypes
                        rfl rfl rfl argumentVariants operatorVariants
                        scopesSeparated scan resultsNonempty⟩
                  · have resultsEmpty : results = [] := by
                      simpa using resultsNonempty
                    subst results
                    exact ⟨[publishedPackage Atom.undefinedType],
                      RuntimeTypePackagesRel.expressionUndefined
                        notState noAnnotations headTypes tailTypes
                        rfl rfl rfl argumentVariants operatorVariants
                        scopesSeparated scan⟩
  | nil => exact ⟨[], List.Forall₂.nil⟩
  | cons atom atoms atomTypes tailTypes =>
      obtain ⟨packages, packagesRel⟩ := atomTypes
      obtain ⟨packageLists, packageListsRel⟩ := tailTypes
      exact ⟨packages :: packageLists,
        List.Forall₂.cons packagesRel packageListsRel⟩

/-- Every exact spec package presentation is alpha-exact with the concrete
repaired runtime's complete recursive type list. -/
theorem runtimeTypePackages_complete
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {atom : Atom} {packages : List TypePackage}
    (types : RuntimeTypePackagesRel space atom packages) :
    List.Forall₂ ObservedTypeAlphaRel (observedTypes packages)
      (fromLeaTTaAtoms
        (Metta.Minimal.getTypes env (toLeaTTaAtom atom))) := by
  induction types using RuntimeTypePackagesRel.rec
      (motive_2 := fun arguments packageLists _ =>
        List.Forall₂ (List.Forall₂ ObservedTypeAlphaRel)
          (packageLists.map observedTypes)
          (runtimeArgumentTypeLists env arguments))
  case «variable» name =>
      simpa [observedTypes, publishedPackage,
        Spec.Type.Presentation.RuntimeTypePackage.published,
        Metta.Minimal.getTypes, toLeaTTaAtom, fromLeaTTaAtoms,
        fromLeaTTaAtom, Atom.undefinedType] using
          (List.Forall₂.cons
            (ObservedTypeAlphaRel.refl Atom.undefinedType)
            List.Forall₂.nil)
  case grounded intrinsic =>
      cases intrinsic <;>
        simpa [observedTypes, publishedPackage,
          Spec.Type.Presentation.RuntimeTypePackage.published,
          Metta.Minimal.getTypes, toLeaTTaAtom, toLeaTTaGround,
          fromLeaTTaAtoms, fromLeaTTaAtom] using
            (List.Forall₂.cons
              (ObservedTypeAlphaRel.refl _) List.Forall₂.nil)
  case symbolKnown name annotated annotation nonempty =>
      have annotationEquation :=
        annotationTypesRel_eq_getAnnotatedTypes annotation
      have annotationEquation' :
          getAnnotatedTypes space (.symbol name) = annotated := by
        simpa [Space.ofList] using annotationEquation
      have indexEquation := index.symbolTypes name
      rw [annotationEquation'] at indexEquation
      have runtimeEquation :
          Metta.Minimal.getTypes env
              (toLeaTTaAtom (.symbol name)) =
            toLeaTTaAtoms annotated := by
        simp [Metta.Minimal.getTypes, toLeaTTaAtom,
          indexEquation, nonempty]
      rw [runtimeEquation, fromLeaTTaAtoms_toLeaTTaAtoms]
      rw [observedTypes_publishedPackages]
      exact observedTypeAlphaList_refl annotated
  case symbolUndefined name annotation =>
      have annotationEquation :=
        annotationTypesRel_eq_getAnnotatedTypes annotation
      have annotationEquation' :
          getAnnotatedTypes space (.symbol name) = [] := by
        simpa [Space.ofList] using annotationEquation
      have indexEquation := index.symbolTypes name
      rw [annotationEquation'] at indexEquation
      have runtimeEquation :
          Metta.Minimal.getTypes env
              (toLeaTTaAtom (.symbol name)) =
            [.sym "%Undefined%"] := by
        simp [Metta.Minimal.getTypes, toLeaTTaAtom, indexEquation]
      rw [runtimeEquation]
      change List.Forall₂ ObservedTypeAlphaRel
        [Atom.undefinedType] [Atom.undefinedType]
      exact List.Forall₂.cons (ObservedTypeAlphaRel.refl _)
        List.Forall₂.nil
  case unit =>
      simpa [observedTypes, publishedPackage,
        Spec.Type.Presentation.RuntimeTypePackage.published,
        Metta.Minimal.getTypes, toLeaTTaAtom, fromLeaTTaAtoms,
        fromLeaTTaAtom, Atom.undefinedType] using
          (List.Forall₂.cons
            (ObservedTypeAlphaRel.refl Atom.undefinedType)
            List.Forall₂.nil)
  case stateValue value content remaining contentTypes contentIH =>
      obtain ⟨runtimeHead, runtimeTail, runtimeTypesEquation⟩ :=
        List.exists_cons_of_ne_nil
          (Metta.getTypes_ne_nil env (toLeaTTaAtom value))
      have decodedTypesEquation :
          fromLeaTTaAtoms
              (Metta.Minimal.getTypes env (toLeaTTaAtom value)) =
            fromLeaTTaAtom runtimeHead :: fromLeaTTaAtoms runtimeTail := by
        rw [runtimeTypesEquation]
        rfl
      rw [decodedTypesEquation] at contentIH
      cases contentIH with
      | cons headAlpha tailAlpha =>
          have runtimeEquation :
              Metta.Minimal.getTypes env
                  (toLeaTTaAtom
                    (.expression [.symbol "StateValue", value])) =
                [.expr [.sym "StateMonad", runtimeHead]] := by
            simp [Metta.Minimal.getTypes, toLeaTTaAtom,
              toLeaTTaAtoms, runtimeTypesEquation]
          rw [runtimeEquation]
          change List.Forall₂ ObservedTypeAlphaRel
            [.expression [.symbol "StateMonad", content.observed]]
            [.expression
              [.symbol "StateMonad", fromLeaTTaAtom runtimeHead]]
          exact List.Forall₂.cons
            (observedTypeAlpha_stateMonad headAlpha)
            List.Forall₂.nil
  case expressionKnown head tail annotated notState annotation nonempty =>
      have annotationEquation :=
        annotationTypesRel_eq_getAnnotatedTypes annotation
      have annotationEquation' :
          getAnnotatedTypes space (.expression (head :: tail)) =
            annotated := by
        simpa [Space.ofList] using annotationEquation
      have indexEquation := index.expressionTypes head tail
      rw [annotationEquation'] at indexEquation
      let filtered := env.exprTypes.filter (fun entry =>
        entry.1 == toLeaTTaAtom (.expression (head :: tail)))
      have filteredNonempty : filtered ≠ [] := by
        intro filteredEmpty
        have emptyTypes :
            (filtered.map (fun entry => entry.2)) = [] := by
          simp [filteredEmpty]
        rw [emptyTypes] at indexEquation
        have : annotated = [] := by
          simpa using congrArg fromLeaTTaAtoms indexEquation.symm
        exact nonempty this
      obtain ⟨first, rest, filteredEquation⟩ :=
        List.exists_cons_of_ne_nil filteredNonempty
      have runtimeEquation :
          Metta.Minimal.getTypes env
              (toLeaTTaAtom (.expression (head :: tail))) =
            toLeaTTaAtoms annotated := by
        rw [show toLeaTTaAtom (.expression (head :: tail)) =
          .expr (toLeaTTaAtom head :: toLeaTTaAtoms tail) by
            simp [toLeaTTaAtom, toLeaTTaAtoms_eq_map]]
        rw [Metta.Minimal.getTypes.eq_10 env
          (toLeaTTaAtom head) (toLeaTTaAtoms tail)
          (notStateValueShape_toLeaTTa notState)]
        have nativeFilteredEquation :
            env.exprTypes.filter (fun entry =>
              entry.1 ==
                .expr (toLeaTTaAtom head :: toLeaTTaAtoms tail)) =
              first :: rest := by
          simpa [filtered, toLeaTTaAtom,
            toLeaTTaAtoms_eq_map] using filteredEquation
        rw [nativeFilteredEquation]
        simpa [filtered, filteredEquation] using indexEquation
      rw [runtimeEquation, fromLeaTTaAtoms_toLeaTTaAtoms]
      rw [observedTypes_publishedPackages]
      exact observedTypeAlphaList_refl annotated
  case expressionInferred head tail operatorPackages argumentPackages
      rawArguments rawOperators avoid freshArguments freshOperators results
      notState noAnnotations operatorTypes argumentHeads
      rawArgumentsEquation rawOperatorsEquation avoidEquation
      leftArgumentVariants leftOperatorVariants leftScopesSeparated
      leftScan resultsNonempty
      operatorIH argumentIH =>
      subst rawArguments
      subst rawOperators
      subst avoid
      let runtimeRawArgumentLists := runtimeArgumentTypeLists env tail
      let runtimeRawArgumentChoices :=
        orderedCartesian runtimeRawArgumentLists
      let leaAllRawArgumentTypes :=
        ((toLeaTTaAtoms tail).map
          (Metta.Minimal.getTypes env)).flatten
      let runtimeRawOperators := fromLeaTTaAtoms
        (Metta.Minimal.getTypes env (toLeaTTaAtom head))
      let runtimeAvoid :=
        Metta.Minimal.typeInferenceAvoid env
          (.expr (toLeaTTaAtom head :: toLeaTTaAtoms tail))
          (Metta.Minimal.getTypes env (toLeaTTaAtom head) ++
            leaAllRawArgumentTypes)
      let functionAvoid := runtimeAvoid ++
        leaAllRawArgumentTypes.flatMap Metta.Atom.vars
      let runtimeFreshArgumentChoices :=
        runtimeRawArgumentChoices.map fun choice =>
          fromLeaTTaAtoms
            (Metta.Minimal.freshenArgumentTypes runtimeAvoid 0
              (toLeaTTaAtoms choice))
      let runtimeFreshOperators := fromLeaTTaAtoms
        ((toLeaTTaAtoms runtimeRawOperators).map
          (Metta.Minimal.freshenTypeCandidate
            functionAvoid tail.length))
      have argumentListLength :
          runtimeRawArgumentLists.length = tail.length := by
        simp [runtimeRawArgumentLists, runtimeArgumentTypeLists]
      have concreteAlpha : List.Forall₂ ObservedTypeAlphaRel
          (observedTypes results)
          (fromLeaTTaAtoms
            (runtimeApplicationCandidateMatrix
              runtimeFreshArgumentChoices runtimeFreshOperators)) := by
        simpa [runtimeRawArgumentLists, runtimeRawArgumentChoices,
          leaAllRawArgumentTypes, runtimeRawOperators, runtimeAvoid,
          functionAvoid, runtimeFreshArgumentChoices,
          runtimeFreshOperators] using
            (applicationPackageMatrix_concrete_alpha
              argumentIH operatorIH leftArgumentVariants
              leftOperatorVariants leftScopesSeparated leftScan
              runtimeAvoid functionAvoid tail.length argumentListLength)
      have runtimeMatrixNonempty : runtimeApplicationCandidateMatrix
          runtimeFreshArgumentChoices runtimeFreshOperators ≠ [] := by
        intro matrixEmpty
        have resultLength : results.length = 0 := by
          calc
            results.length = (observedTypes results).length := by
              simp [observedTypes]
            _ = (fromLeaTTaAtoms
                (runtimeApplicationCandidateMatrix
                  runtimeFreshArgumentChoices
                  runtimeFreshOperators)).length :=
              concreteAlpha.length_eq
            _ = 0 := by simp [matrixEmpty]
        exact resultsNonempty (List.length_eq_zero_iff.mp resultLength)
      have nativeNoDirect := expressionTypes_filter_eq_nil
        index noAnnotations
      have runtimeEquation := getTypes_expression_eq_candidateMatrix
        index head tail notState nativeNoDirect
      rw [runtimeEquation]
      cases matrixEquation : runtimeApplicationCandidateMatrix
          runtimeFreshArgumentChoices runtimeFreshOperators with
      | nil => exact (runtimeMatrixNonempty matrixEquation).elim
      | cons first rest =>
          simpa [matrixEquation] using concreteAlpha
  case expressionUndefined head tail operatorPackages argumentPackages
      rawArguments rawOperators avoid freshArguments freshOperators
      notState noAnnotations operatorTypes argumentHeads
      rawArgumentsEquation rawOperatorsEquation avoidEquation
      leftArgumentVariants leftOperatorVariants leftScopesSeparated leftScan
      operatorIH argumentIH =>
      subst rawArguments
      subst rawOperators
      subst avoid
      let runtimeRawArgumentLists := runtimeArgumentTypeLists env tail
      let runtimeRawArgumentChoices :=
        orderedCartesian runtimeRawArgumentLists
      let leaAllRawArgumentTypes :=
        ((toLeaTTaAtoms tail).map
          (Metta.Minimal.getTypes env)).flatten
      let runtimeRawOperators := fromLeaTTaAtoms
        (Metta.Minimal.getTypes env (toLeaTTaAtom head))
      let runtimeAvoid :=
        Metta.Minimal.typeInferenceAvoid env
          (.expr (toLeaTTaAtom head :: toLeaTTaAtoms tail))
          (Metta.Minimal.getTypes env (toLeaTTaAtom head) ++
            leaAllRawArgumentTypes)
      let functionAvoid := runtimeAvoid ++
        leaAllRawArgumentTypes.flatMap Metta.Atom.vars
      let runtimeFreshArgumentChoices :=
        runtimeRawArgumentChoices.map fun choice =>
          fromLeaTTaAtoms
            (Metta.Minimal.freshenArgumentTypes runtimeAvoid 0
              (toLeaTTaAtoms choice))
      let runtimeFreshOperators := fromLeaTTaAtoms
        ((toLeaTTaAtoms runtimeRawOperators).map
          (Metta.Minimal.freshenTypeCandidate
            functionAvoid tail.length))
      have argumentListLength :
          runtimeRawArgumentLists.length = tail.length := by
        simp [runtimeRawArgumentLists, runtimeArgumentTypeLists]
      have concreteAlpha : List.Forall₂ ObservedTypeAlphaRel
          (observedTypes ([] : List TypePackage))
          (fromLeaTTaAtoms
            (runtimeApplicationCandidateMatrix
              runtimeFreshArgumentChoices runtimeFreshOperators)) := by
        simpa [runtimeRawArgumentLists, runtimeRawArgumentChoices,
          leaAllRawArgumentTypes, runtimeRawOperators, runtimeAvoid,
          functionAvoid, runtimeFreshArgumentChoices,
          runtimeFreshOperators] using
            (applicationPackageMatrix_concrete_alpha
              argumentIH operatorIH leftArgumentVariants
              leftOperatorVariants leftScopesSeparated leftScan
              runtimeAvoid functionAvoid tail.length argumentListLength)
      have runtimeMatrixEmpty : runtimeApplicationCandidateMatrix
          runtimeFreshArgumentChoices runtimeFreshOperators = [] := by
        apply List.length_eq_zero_iff.mp
        simpa [observedTypes, fromLeaTTaAtoms] using
          concreteAlpha.length_eq.symm
      have nativeNoDirect := expressionTypes_filter_eq_nil
        index noAnnotations
      have runtimeEquation := getTypes_expression_eq_candidateMatrix
        index head tail notState nativeNoDirect
      rw [runtimeEquation, runtimeMatrixEmpty]
      change List.Forall₂ ObservedTypeAlphaRel
        [Atom.undefinedType] [Atom.undefinedType]
      exact List.Forall₂.cons (ObservedTypeAlphaRel.refl _)
        List.Forall₂.nil
  case nil => exact List.Forall₂.nil
  case cons argument arguments packages packageLists
      argumentTypes tailTypes argumentIH tailIH =>
      simpa [runtimeArgumentTypeLists] using
        (List.Forall₂.cons argumentIH tailIH)

private theorem observedTypeAlphaList_symm
    {left right : List Atom}
    (alpha : List.Forall₂ ObservedTypeAlphaRel left right) :
    List.Forall₂ ObservedTypeAlphaRel right left := by
  induction alpha with
  | nil => exact List.Forall₂.nil
  | cons headAlpha _ tailIH =>
      exact List.Forall₂.cons headAlpha.symm tailIH

/-- Every concrete recursive runtime lookup has an exact spec package
presentation, with the same candidate order and multiplicity up to private
alpha-renaming. -/
theorem runtimeGetTypes_has_exact_package_presentation
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env) (atom : Atom) :
    ∃ packages,
      RuntimeTypePackagesRel space atom packages ∧
      List.Forall₂ ObservedTypeAlphaRel (observedTypes packages)
        (fromLeaTTaAtoms
          (Metta.Minimal.getTypes env (toLeaTTaAtom atom))) := by
  obtain ⟨packages, packagesRel⟩ := runtimeTypePackages_exists space atom
  exact ⟨packages, packagesRel,
    runtimeTypePackages_complete index packagesRel⟩

/-- Exact package presentations of one atom are unique up to their private
alpha scopes.  This is the candidate-set equality principle used by negative
applicability premises. -/
theorem runtimeTypePackages_alpha_unique
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {atom : Atom} {left right : List TypePackage}
    (leftRel : RuntimeTypePackagesRel space atom left)
    (rightRel : RuntimeTypePackagesRel space atom right) :
    List.Forall₂ ObservedTypeAlphaRel
      (observedTypes left) (observedTypes right) := by
  exact observedTypeAlphaList_trans
    (runtimeTypePackages_complete index leftRel)
    (observedTypeAlphaList_symm
      (runtimeTypePackages_complete index rightRel))

end Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationRecursiveExact
