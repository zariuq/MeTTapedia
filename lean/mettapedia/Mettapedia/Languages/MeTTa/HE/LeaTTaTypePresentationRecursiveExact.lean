import Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationApplicationExact
import Mettapedia.Languages.MeTTa.HE.HumanTypeConformance

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
open HumanTypeSpec
open HumanTypeConformance
open HumanTypePresentation
open HumanTypePresentationAlpha
open HumanTypePresentationExact
open HumanTypeRuntimeRefinement
open LeaTTaBridge
open LeaTTaTypeConformance
open LeaTTaTypePresentationExactConformance
open LeaTTaTypePresentationApplicationExact

/-- Concrete first type selected recursively for every application argument,
decoded back into the independent atom language. -/
def runtimeArgumentHeadTypes
    (env : Metta.Minimal.MinEnv) (arguments : List Atom) : List Atom :=
  arguments.map fun argument =>
    fromLeaTTaAtom
      ((Metta.Minimal.getTypes env (toLeaTTaAtom argument)).head?.getD
        (.sym "%Undefined%"))

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
    HumanTypePresentation.RuntimeTypePackage.published,
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
  · simp [renameHumanTypeVars, leftEquation]
  · simp [renameHumanTypeVars, rightEquation]

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

/-- Every recursively selected concrete argument head re-encodes exactly. -/
theorem runtimeArgumentHeadTypes_roundtrip
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env) (arguments : List Atom) :
    toLeaTTaAtoms (runtimeArgumentHeadTypes env arguments) =
      arguments.map fun argument =>
        (Metta.Minimal.getTypes env
          (toLeaTTaAtom argument)).head?.getD (.sym "%Undefined%") := by
  simpa [runtimeArgumentHeadTypes, fromLeaTTaAtoms] using
    (getTypes_argumentHeads_roundtrip arguments
      (fun argument _ leaType member =>
        toLeaTTaAtom_fromLeaTTaAtom_of_heImage
          (getTypes_result_heImage index
            (toLeaTTaAtom argument) leaType
            (leaAtomHEImage_toLeaTTaAtom argument) member)))

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
  refine ⟨renameHumanTypeVars
    (Metta.Minimal.captureAvoidingName avoid position) native, ?_⟩
  simpa [Metta.Minimal.freshenTypeCandidate] using
    toLeaTTaAtom_renameHumanTypeVars
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

private theorem applicationPackageScanRel_exists
    (actualTypes : List Atom) : ∀ operatorTypes,
    ∃ results, ApplicationPackageScanRel
      actualTypes operatorTypes results := by
  intro operatorTypes
  induction operatorTypes with
  | nil => exact ⟨[], ApplicationPackageScanRel.nil⟩
  | cons operatorType operatorTypes ih =>
      obtain ⟨tailResults, tailScan⟩ := ih
      obtain ⟨outcome, outcomeRel⟩ :=
        applicationPackageOutcomeRel_exists actualTypes operatorType
      cases outcome with
      | none =>
          exact ⟨tailResults,
            ApplicationPackageScanRel.skip outcomeRel tailScan⟩
      | some result =>
          exact ⟨result :: tailResults,
            ApplicationPackageScanRel.emit outcomeRel tailScan⟩

private theorem runtimeArgumentHeads_of_all
    {space : Space} {arguments : List Atom}
    {packageLists : List (List TypePackage)}
    (allTypes : List.Forall₂
      (RuntimeTypePackagesRel space) arguments packageLists) :
    ∃ heads, RuntimeArgumentHeadPackagesRel space arguments heads := by
  induction allTypes with
  | nil => exact ⟨[], RuntimeArgumentHeadPackagesRel.nil⟩
  | @cons argument headPackages arguments packageLists types _ ih =>
      obtain ⟨head, tail, packagesEquation⟩ :=
        List.exists_cons_of_ne_nil types.nonempty
      subst headPackages
      obtain ⟨heads, headsRel⟩ := ih
      exact ⟨head :: heads,
        RuntimeArgumentHeadPackagesRel.cons types headsRel⟩

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
                  obtain ⟨argumentPackages, argumentHeads⟩ :=
                    runtimeArgumentHeads_of_all tailTypes
                  let rawArguments := observedTypes argumentPackages
                  let rawOperators := observedTypes headPackages
                  let avoid := inferenceAvoidNames space expression
                    (rawOperators ++ rawArguments)
                  let freshArguments := fromLeaTTaAtoms
                    (Metta.Minimal.freshenArgumentTypes avoid 0
                      (toLeaTTaAtoms rawArguments))
                  have argumentVariants : ArgumentAlphaVariantsRel
                      avoid rawArguments freshArguments := by
                    simpa [freshArguments] using
                      freshenArgumentTypes_alphaVariants avoid 0 rawArguments
                  let operatorAvoid :=
                    avoid ++ TypeSubst.typeVarsList freshArguments
                  let freshOperators := fromLeaTTaAtoms
                    ((toLeaTTaAtoms rawOperators).map
                      (Metta.Minimal.freshenTypeCandidate
                        operatorAvoid tail.length))
                  have operatorVariants : OperatorAlphaVariantsRel
                      operatorAvoid rawOperators freshOperators := by
                    simpa [freshOperators] using
                      freshenOperatorTypes_alphaVariants
                        operatorAvoid tail.length rawOperators
                  obtain ⟨results, scan⟩ :=
                    applicationPackageScanRel_exists
                      freshArguments freshOperators
                  by_cases resultsNonempty : results ≠ []
                  · exact ⟨results,
                      RuntimeTypePackagesRel.expressionInferred
                        notState noAnnotations headTypes argumentHeads
                        rfl rfl rfl argumentVariants operatorVariants
                        scan resultsNonempty⟩
                  · have resultsEmpty : results = [] := by
                      simpa using resultsNonempty
                    subst results
                    exact ⟨[publishedPackage Atom.undefinedType],
                      RuntimeTypePackagesRel.expressionUndefined
                        notState noAnnotations headTypes argumentHeads
                        rfl rfl rfl argumentVariants operatorVariants scan⟩
  | nil => exact ⟨[], List.Forall₂.nil⟩
  | cons atom atoms atomTypes tailTypes =>
      obtain ⟨packages, packagesRel⟩ := atomTypes
      obtain ⟨packageLists, packageListsRel⟩ := tailTypes
      exact ⟨packages :: packageLists,
        List.Forall₂.cons packagesRel packageListsRel⟩

/-- Every exact human package presentation is alpha-exact with the concrete
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
      (motive_2 := fun arguments heads _ =>
        List.Forall₂ ObservedTypeAlphaRel (observedTypes heads)
          (runtimeArgumentHeadTypes env arguments))
  case «variable» name =>
      simpa [observedTypes, publishedPackage,
        HumanTypePresentation.RuntimeTypePackage.published,
        Metta.Minimal.getTypes, toLeaTTaAtom, fromLeaTTaAtoms,
        fromLeaTTaAtom, Atom.undefinedType] using
          (List.Forall₂.cons
            (ObservedTypeAlphaRel.refl Atom.undefinedType)
            List.Forall₂.nil)
  case grounded intrinsic =>
      cases intrinsic <;>
        simpa [observedTypes, publishedPackage,
          HumanTypePresentation.RuntimeTypePackage.published,
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
        HumanTypePresentation.RuntimeTypePackage.published,
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
      leftArgumentVariants leftOperatorVariants leftScan resultsNonempty
      operatorIH argumentIH =>
      subst rawArguments
      subst rawOperators
      subst avoid
      let leaRawArguments : List Metta.Atom :=
        tail.map fun argument =>
          (Metta.Minimal.getTypes env
            (toLeaTTaAtom argument)).head?.getD (.sym "%Undefined%")
      let leaRawOperators : List Metta.Atom :=
        Metta.Minimal.getTypes env (toLeaTTaAtom head)
      let runtimeAvoid : List String :=
        Metta.Minimal.typeInferenceAvoid env
          (.expr (toLeaTTaAtom head :: toLeaTTaAtoms tail))
          (leaRawOperators ++ leaRawArguments)
      let leaFreshArguments : List Metta.Atom :=
        Metta.Minimal.freshenArgumentTypes runtimeAvoid 0 leaRawArguments
      let runtimeFreshArguments : List Atom :=
        fromLeaTTaAtoms leaFreshArguments
      let functionAvoid : List String :=
        runtimeAvoid ++ leaFreshArguments.flatMap Metta.Atom.vars
      let leaFreshOperators : List Metta.Atom :=
        leaRawOperators.map
          (Metta.Minimal.freshenTypeCandidate functionAvoid tail.length)
      let runtimeFreshOperators : List Atom :=
        fromLeaTTaAtoms leaFreshOperators
      have argumentRoundtrip :
          toLeaTTaAtoms (runtimeArgumentHeadTypes env tail) =
            leaRawArguments := by
        simpa [leaRawArguments] using
          runtimeArgumentHeadTypes_roundtrip index tail
      have runtimeArgumentBase : ArgumentAlphaVariantsRel
          runtimeAvoid (runtimeArgumentHeadTypes env tail)
          runtimeFreshArguments := by
        have realized := freshenArgumentTypes_alphaVariants
          runtimeAvoid 0 (runtimeArgumentHeadTypes env tail)
        rw [argumentRoundtrip] at realized
        simpa [runtimeFreshArguments, leaFreshArguments] using realized
      have runtimeArgumentVariants : ArgumentAlphaVariantsRel
          runtimeAvoid (observedTypes argumentPackages)
          runtimeFreshArguments :=
        ArgumentAlphaVariantsRel.transport_left
          argumentIH runtimeArgumentBase
      have operatorRoundtrip :
          toLeaTTaAtoms
              (fromLeaTTaAtoms leaRawOperators) = leaRawOperators := by
        simpa [leaRawOperators] using
          runtimeOperatorTypes_roundtrip index head
      have runtimeOperatorBase : OperatorAlphaVariantsRel
          (runtimeAvoid ++ TypeSubst.typeVarsList runtimeFreshArguments)
          (fromLeaTTaAtoms leaRawOperators) runtimeFreshOperators := by
        have realized := freshenOperatorTypes_alphaVariants
          (runtimeAvoid ++ TypeSubst.typeVarsList runtimeFreshArguments)
          tail.length (fromLeaTTaAtoms leaRawOperators)
        rw [operatorRoundtrip] at realized
        have freshArgumentRoundtrip :
            toLeaTTaAtoms runtimeFreshArguments = leaFreshArguments := by
          apply toLeaTTaAtoms_fromLeaTTaAtoms_of_heImage
          apply freshenArgumentTypes_heImage
          apply leaAtomsHEImage_of_forall
          intro selected selectedMember
          obtain ⟨argument, argumentMember, rfl⟩ :=
            List.mem_map.mp selectedMember
          apply getTypes_head_heImage
          intro leaType member
          exact getTypes_result_heImage index
            (toLeaTTaAtom argument) leaType
            (leaAtomHEImage_toLeaTTaAtom argument) member
        have avoidLists :
            runtimeAvoid ++ TypeSubst.typeVarsList runtimeFreshArguments =
              functionAvoid := by
          apply congrArg (runtimeAvoid ++ ·)
          have varsEquation := congrArg
            (List.flatMap Metta.Atom.vars) freshArgumentRoundtrip
          simpa [← toLeaTTaAtoms_vars_eq_typeVars] using varsEquation
        simp only [runtimeFreshOperators, leaFreshOperators]
        rw [← avoidLists]
        simpa [runtimeFreshOperators, leaFreshOperators] using realized
      have runtimeOperatorVariants : OperatorAlphaVariantsRel
          (runtimeAvoid ++ TypeSubst.typeVarsList runtimeFreshArguments)
          (observedTypes operatorPackages) runtimeFreshOperators :=
        OperatorAlphaVariantsRel.transport_left
          operatorIH runtimeOperatorBase
      obtain ⟨runtimeResults, runtimeScan, scanAlpha⟩ :=
        ApplicationPackageScanRel.transport_common_scopes
          leftArgumentVariants runtimeArgumentVariants
          leftOperatorVariants runtimeOperatorVariants leftScan
      have runtimeDisjoint : ∀ operatorType ∈ runtimeFreshOperators,
          VarsDisjoint operatorType (.expression runtimeFreshArguments) :=
        OperatorAlphaVariantsRel.disjoint_from_arguments
          runtimeOperatorVariants
      have concreteAlpha :=
        runtimeApplicationCandidates_complete runtimeScan runtimeDisjoint
      have combinedAlpha :=
        observedTypeAlphaList_trans scanAlpha concreteAlpha
      have leaRawArgumentsImage : LeaAtomsHEImage leaRawArguments := by
        apply leaAtomsHEImage_of_forall
        intro selected selectedMember
        obtain ⟨argument, argumentMember, rfl⟩ :=
          List.mem_map.mp selectedMember
        apply getTypes_head_heImage
        intro leaType member
        exact getTypes_result_heImage index
          (toLeaTTaAtom argument) leaType
          (leaAtomHEImage_toLeaTTaAtom argument) member
      have leaRawOperatorsImage : LeaAtomsHEImage leaRawOperators := by
        apply leaAtomsHEImage_of_forall
        intro leaType member
        exact getTypes_result_heImage index
          (toLeaTTaAtom head) leaType
          (leaAtomHEImage_toLeaTTaAtom head) member
      have leaFreshArgumentsImage : LeaAtomsHEImage leaFreshArguments :=
        freshenArgumentTypes_heImage runtimeAvoid 0 leaRawArgumentsImage
      have leaFreshOperatorsImage : LeaAtomsHEImage leaFreshOperators :=
        freshenOperatorTypes_heImage functionAvoid tail.length
          leaRawOperatorsImage
      have candidatesDecode := runtimeApplicationCandidates_decode
        leaFreshArgumentsImage leaFreshOperatorsImage
      have runtimeCandidatesNonempty :
          runtimeApplicationCandidates
            runtimeFreshArguments runtimeFreshOperators ≠ [] := by
        intro emptyCandidates
        have leftLength : results.length = runtimeResults.length := by
          simpa [observedTypes] using scanAlpha.length_eq
        have rightLength : runtimeResults.length =
            (runtimeApplicationCandidates
              runtimeFreshArguments runtimeFreshOperators).length := by
          simpa [observedTypes, fromLeaTTaAtoms] using
            concreteAlpha.length_eq
        have : results.length = 0 := by
          rw [leftLength, rightLength, emptyCandidates]
          rfl
        exact resultsNonempty (List.length_eq_zero_iff.mp this)
      have noDirectMapped := index.expressionTypes head tail
      have noAnnotationsEquation :
          getAnnotatedTypes space (.expression (head :: tail)) = [] := by
        simpa [Space.ofList] using
          annotationTypesRel_eq_getAnnotatedTypes noAnnotations
      rw [noAnnotationsEquation] at noDirectMapped
      have noDirect :
          env.exprTypes.filter (fun entry =>
            entry.1 == toLeaTTaAtom (.expression (head :: tail))) = [] := by
        cases filteredEquation : env.exprTypes.filter (fun entry =>
            entry.1 == toLeaTTaAtom (.expression (head :: tail))) with
        | nil => rfl
        | cons first rest =>
            rw [filteredEquation] at noDirectMapped
            simp at noDirectMapped
      have nativeNoDirect :
          env.exprTypes.filter (fun entry =>
            entry.1 ==
              .expr (toLeaTTaAtom head :: toLeaTTaAtoms tail)) = [] := by
        simpa [toLeaTTaAtom, toLeaTTaAtoms_eq_map] using noDirect
      have runtimeEquation :
          Metta.Minimal.getTypes env
              (toLeaTTaAtom (.expression (head :: tail))) =
            runtimeApplicationCandidates
              runtimeFreshArguments runtimeFreshOperators := by
        rw [show toLeaTTaAtom (.expression (head :: tail)) =
          .expr (toLeaTTaAtom head :: toLeaTTaAtoms tail) by
            simp [toLeaTTaAtom, toLeaTTaAtoms_eq_map]]
        rw [Metta.Minimal.getTypes.eq_10 env
          (toLeaTTaAtom head) (toLeaTTaAtoms tail)
          (notStateValueShape_toLeaTTa notState), nativeNoDirect]
        simp only
        have rawArgumentsCode :
            (toLeaTTaAtoms tail).map (fun argument =>
              (Metta.Minimal.getTypes env argument).head?.getD
                (.sym "%Undefined%")) = leaRawArguments := by
          simp [leaRawArguments, toLeaTTaAtoms_eq_map,
            List.map_map, Function.comp_def]
        have lengthCode : (toLeaTTaAtoms tail).length = tail.length := by
          simp [toLeaTTaAtoms_eq_map]
        rw [rawArgumentsCode, lengthCode]
        change (match leaFreshOperators.filterMap
            (leaRuntimeApplicationCandidate leaFreshArguments) with
          | [] => [.sym "%Undefined%"]
          | values => values) =
            runtimeApplicationCandidates
              runtimeFreshArguments runtimeFreshOperators
        rw [← candidatesDecode]
        change (match runtimeApplicationCandidates
            runtimeFreshArguments runtimeFreshOperators with
          | [] => [.sym "%Undefined%"]
          | values => values) =
            runtimeApplicationCandidates
              runtimeFreshArguments runtimeFreshOperators
        cases candidatesEquation : runtimeApplicationCandidates
            runtimeFreshArguments runtimeFreshOperators with
        | nil => exact (runtimeCandidatesNonempty candidatesEquation).elim
        | cons head tail => rfl
      rw [runtimeEquation]
      exact combinedAlpha
  case expressionUndefined head tail operatorPackages argumentPackages
      rawArguments rawOperators avoid freshArguments freshOperators
      notState noAnnotations operatorTypes argumentHeads
      rawArgumentsEquation rawOperatorsEquation avoidEquation
      leftArgumentVariants leftOperatorVariants leftScan
      operatorIH argumentIH =>
      subst rawArguments
      subst rawOperators
      subst avoid
      let leaRawArguments : List Metta.Atom :=
        tail.map fun argument =>
          (Metta.Minimal.getTypes env
            (toLeaTTaAtom argument)).head?.getD (.sym "%Undefined%")
      let leaRawOperators : List Metta.Atom :=
        Metta.Minimal.getTypes env (toLeaTTaAtom head)
      let runtimeAvoid : List String :=
        Metta.Minimal.typeInferenceAvoid env
          (.expr (toLeaTTaAtom head :: toLeaTTaAtoms tail))
          (leaRawOperators ++ leaRawArguments)
      let leaFreshArguments : List Metta.Atom :=
        Metta.Minimal.freshenArgumentTypes runtimeAvoid 0 leaRawArguments
      let runtimeFreshArguments : List Atom :=
        fromLeaTTaAtoms leaFreshArguments
      let functionAvoid : List String :=
        runtimeAvoid ++ leaFreshArguments.flatMap Metta.Atom.vars
      let leaFreshOperators : List Metta.Atom :=
        leaRawOperators.map
          (Metta.Minimal.freshenTypeCandidate functionAvoid tail.length)
      let runtimeFreshOperators : List Atom :=
        fromLeaTTaAtoms leaFreshOperators
      have argumentRoundtrip :
          toLeaTTaAtoms (runtimeArgumentHeadTypes env tail) =
            leaRawArguments := by
        simpa [leaRawArguments] using
          runtimeArgumentHeadTypes_roundtrip index tail
      have runtimeArgumentBase : ArgumentAlphaVariantsRel
          runtimeAvoid (runtimeArgumentHeadTypes env tail)
          runtimeFreshArguments := by
        have realized := freshenArgumentTypes_alphaVariants
          runtimeAvoid 0 (runtimeArgumentHeadTypes env tail)
        rw [argumentRoundtrip] at realized
        simpa [runtimeFreshArguments, leaFreshArguments] using realized
      have runtimeArgumentVariants : ArgumentAlphaVariantsRel
          runtimeAvoid (observedTypes argumentPackages)
          runtimeFreshArguments :=
        ArgumentAlphaVariantsRel.transport_left
          argumentIH runtimeArgumentBase
      have operatorRoundtrip :
          toLeaTTaAtoms
              (fromLeaTTaAtoms leaRawOperators) = leaRawOperators := by
        simpa [leaRawOperators] using
          runtimeOperatorTypes_roundtrip index head
      have runtimeOperatorBase : OperatorAlphaVariantsRel
          (runtimeAvoid ++ TypeSubst.typeVarsList runtimeFreshArguments)
          (fromLeaTTaAtoms leaRawOperators) runtimeFreshOperators := by
        have realized := freshenOperatorTypes_alphaVariants
          (runtimeAvoid ++ TypeSubst.typeVarsList runtimeFreshArguments)
          tail.length (fromLeaTTaAtoms leaRawOperators)
        rw [operatorRoundtrip] at realized
        have freshArgumentRoundtrip :
            toLeaTTaAtoms runtimeFreshArguments = leaFreshArguments := by
          apply toLeaTTaAtoms_fromLeaTTaAtoms_of_heImage
          apply freshenArgumentTypes_heImage
          apply leaAtomsHEImage_of_forall
          intro selected selectedMember
          obtain ⟨argument, argumentMember, rfl⟩ :=
            List.mem_map.mp selectedMember
          apply getTypes_head_heImage
          intro leaType member
          exact getTypes_result_heImage index
            (toLeaTTaAtom argument) leaType
            (leaAtomHEImage_toLeaTTaAtom argument) member
        have avoidLists :
            runtimeAvoid ++ TypeSubst.typeVarsList runtimeFreshArguments =
              functionAvoid := by
          apply congrArg (runtimeAvoid ++ ·)
          have varsEquation := congrArg
            (List.flatMap Metta.Atom.vars) freshArgumentRoundtrip
          simpa [← toLeaTTaAtoms_vars_eq_typeVars] using varsEquation
        simp only [runtimeFreshOperators, leaFreshOperators]
        rw [← avoidLists]
        simpa [runtimeFreshOperators, leaFreshOperators] using realized
      have runtimeOperatorVariants : OperatorAlphaVariantsRel
          (runtimeAvoid ++ TypeSubst.typeVarsList runtimeFreshArguments)
          (observedTypes operatorPackages) runtimeFreshOperators :=
        OperatorAlphaVariantsRel.transport_left
          operatorIH runtimeOperatorBase
      obtain ⟨runtimeResults, runtimeScan, scanAlpha⟩ :=
        ApplicationPackageScanRel.transport_common_scopes
          leftArgumentVariants runtimeArgumentVariants
          leftOperatorVariants runtimeOperatorVariants leftScan
      have runtimeResultsEmpty : runtimeResults = [] := by
        apply List.length_eq_zero_iff.mp
        simpa [observedTypes] using scanAlpha.length_eq.symm
      subst runtimeResults
      have runtimeDisjoint : ∀ operatorType ∈ runtimeFreshOperators,
          VarsDisjoint operatorType (.expression runtimeFreshArguments) :=
        OperatorAlphaVariantsRel.disjoint_from_arguments
          runtimeOperatorVariants
      have concreteAlpha :=
        runtimeApplicationCandidates_complete runtimeScan runtimeDisjoint
      have runtimeCandidatesEmpty :
          runtimeApplicationCandidates
            runtimeFreshArguments runtimeFreshOperators = [] := by
        apply List.length_eq_zero_iff.mp
        simpa [observedTypes, fromLeaTTaAtoms] using
          concreteAlpha.length_eq.symm
      have leaRawArgumentsImage : LeaAtomsHEImage leaRawArguments := by
        apply leaAtomsHEImage_of_forall
        intro selected selectedMember
        obtain ⟨argument, argumentMember, rfl⟩ :=
          List.mem_map.mp selectedMember
        apply getTypes_head_heImage
        intro leaType member
        exact getTypes_result_heImage index
          (toLeaTTaAtom argument) leaType
          (leaAtomHEImage_toLeaTTaAtom argument) member
      have leaRawOperatorsImage : LeaAtomsHEImage leaRawOperators := by
        apply leaAtomsHEImage_of_forall
        intro leaType member
        exact getTypes_result_heImage index
          (toLeaTTaAtom head) leaType
          (leaAtomHEImage_toLeaTTaAtom head) member
      have leaFreshArgumentsImage : LeaAtomsHEImage leaFreshArguments :=
        freshenArgumentTypes_heImage runtimeAvoid 0 leaRawArgumentsImage
      have leaFreshOperatorsImage : LeaAtomsHEImage leaFreshOperators :=
        freshenOperatorTypes_heImage functionAvoid tail.length
          leaRawOperatorsImage
      have candidatesDecode := runtimeApplicationCandidates_decode
        leaFreshArgumentsImage leaFreshOperatorsImage
      have noDirectMapped := index.expressionTypes head tail
      have noAnnotationsEquation :
          getAnnotatedTypes space (.expression (head :: tail)) = [] := by
        simpa [Space.ofList] using
          annotationTypesRel_eq_getAnnotatedTypes noAnnotations
      rw [noAnnotationsEquation] at noDirectMapped
      have noDirect :
          env.exprTypes.filter (fun entry =>
            entry.1 == toLeaTTaAtom (.expression (head :: tail))) = [] := by
        cases filteredEquation : env.exprTypes.filter (fun entry =>
            entry.1 == toLeaTTaAtom (.expression (head :: tail))) with
        | nil => rfl
        | cons first rest =>
            rw [filteredEquation] at noDirectMapped
            simp at noDirectMapped
      have nativeNoDirect :
          env.exprTypes.filter (fun entry =>
            entry.1 ==
              .expr (toLeaTTaAtom head :: toLeaTTaAtoms tail)) = [] := by
        simpa [toLeaTTaAtom, toLeaTTaAtoms_eq_map] using noDirect
      have runtimeEquation :
          Metta.Minimal.getTypes env
              (toLeaTTaAtom (.expression (head :: tail))) =
            [.sym "%Undefined%"] := by
        rw [show toLeaTTaAtom (.expression (head :: tail)) =
          .expr (toLeaTTaAtom head :: toLeaTTaAtoms tail) by
            simp [toLeaTTaAtom, toLeaTTaAtoms_eq_map]]
        rw [Metta.Minimal.getTypes.eq_10 env
          (toLeaTTaAtom head) (toLeaTTaAtoms tail)
          (notStateValueShape_toLeaTTa notState), nativeNoDirect]
        simp only
        have rawArgumentsCode :
            (toLeaTTaAtoms tail).map (fun argument =>
              (Metta.Minimal.getTypes env argument).head?.getD
                (.sym "%Undefined%")) = leaRawArguments := by
          simp [leaRawArguments, toLeaTTaAtoms_eq_map,
            List.map_map, Function.comp_def]
        have lengthCode : (toLeaTTaAtoms tail).length = tail.length := by
          simp [toLeaTTaAtoms_eq_map]
        rw [rawArgumentsCode, lengthCode]
        change (match leaFreshOperators.filterMap
            (leaRuntimeApplicationCandidate leaFreshArguments) with
          | [] => [.sym "%Undefined%"]
          | values => values) = [.sym "%Undefined%"]
        rw [← candidatesDecode]
        change (match runtimeApplicationCandidates
            runtimeFreshArguments runtimeFreshOperators with
          | [] => [.sym "%Undefined%"]
          | values => values) = [.sym "%Undefined%"]
        rw [runtimeCandidatesEmpty]
      rw [runtimeEquation]
      change List.Forall₂ ObservedTypeAlphaRel
        [Atom.undefinedType] [Atom.undefinedType]
      exact List.Forall₂.cons (ObservedTypeAlphaRel.refl _)
        List.Forall₂.nil
  case nil => exact List.Forall₂.nil
  case cons argument arguments head tail heads
      argumentTypes tailTypes argumentIH tailIH =>
      obtain ⟨runtimeHead, runtimeTail, runtimeTypesEquation⟩ :=
        List.exists_cons_of_ne_nil
          (Metta.getTypes_ne_nil env (toLeaTTaAtom argument))
      have decodedTypesEquation :
          fromLeaTTaAtoms
              (Metta.Minimal.getTypes env (toLeaTTaAtom argument)) =
            fromLeaTTaAtom runtimeHead :: fromLeaTTaAtoms runtimeTail := by
        rw [runtimeTypesEquation]
        rfl
      rw [decodedTypesEquation] at argumentIH
      cases argumentIH with
      | cons headAlpha _ =>
          simp only [runtimeArgumentHeadTypes, List.map_cons]
          rw [runtimeTypesEquation]
          exact List.Forall₂.cons headAlpha tailIH

private theorem observedTypeAlphaList_symm
    {left right : List Atom}
    (alpha : List.Forall₂ ObservedTypeAlphaRel left right) :
    List.Forall₂ ObservedTypeAlphaRel right left := by
  induction alpha with
  | nil => exact List.Forall₂.nil
  | cons headAlpha _ tailIH =>
      exact List.Forall₂.cons headAlpha.symm tailIH

/-- Every concrete recursive runtime lookup has an exact human package
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
