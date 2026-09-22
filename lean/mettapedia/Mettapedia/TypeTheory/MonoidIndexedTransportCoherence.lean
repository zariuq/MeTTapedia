import Mettapedia.TypeTheory.MonoidIndexedFamilyConversion
import Mettapedia.TypeTheory.ScopedIdentity

/-!
# Observer-relative replacement of accepted indexed conversion evidence

Primitive accepted certificates act on actual dependent fibres; a structural
fold extends those actions through reflexivity, reversal and composition.
For the existing monoid-indexed semantic family this fold agrees with its
independently specified canonical-word transport. Parallel paths therefore
act identically on this family without being identified as syntax.

For any supplied primitive transport interpretation, replacement is safe for
an observer exactly when the observer is invariant under the resulting
target-fibre loop. In the canonical family that loop acts trivially. An
observer of retained evidence can still distinguish two accepted typing
receipts, even while their nontrivial application values agree.

This is an indexed conversion/transport experiment, not a native J model,
global UIP principle, proof-erasure policy or new trusted conversion rule.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MonoidIndexedTransportCoherence

open JudgmentalEquality FreeConversion ConversionDecisionComparison
open MonoidIndexedFamilyConversion
open Mettapedia.UniversalAlgebra Mettapedia.UniversalAlgebra.Monoid
open Mettapedia.UniversalAlgebra.Monoid.FreeNormalization

universe uFibre uObservation

/-- A supplied interpretation of primitive accepted certificates. The
extension is actual recursion on retained evidence, not an endpoint decoder. -/
def transportAlgebra (Fibre : IndexedType → Type uFibre)
    (primitive : ∀ {source target}, ConversionStep source target → Fibre source ≃ Fibre target) :
    Algebra State (fun {_index : Unit} => ConversionStep)
      (fun {_index : Unit} source target => Fibre source ≃ Fibre target) where
  onStep := primitive
  onRefl := fun source => Equiv.refl (Fibre source)
  onSymm := Equiv.symm
  onTrans := Equiv.trans

def transportEquiv {Fibre : IndexedType → Type uFibre}
    (primitive : ∀ {source target}, ConversionStep source target → Fibre source ≃ Fibre target)
    {source target : IndexedType} (path : ConversionPath source target) :
    Fibre source ≃ Fibre target :=
  (transportAlgebra Fibre primitive).fold path

/-- The exact obstruction for this family and observer is the action of
the target-fibre loop, not equality or uniqueness of the supplied paths. -/
theorem replacement_iff_loop_invariant
    {Fibre : IndexedType → Type uFibre}
    (primitive : ∀ {source target}, ConversionStep source target → Fibre source ≃ Fibre target)
    {source target : IndexedType} (first second : ConversionPath source target)
    {Observation : Type uObservation} (observe : Fibre target → Observation) :
    (∀ value, observe (transportEquiv primitive first value) =
      observe (transportEquiv primitive second value)) ↔
    ∀ value, observe (((transportEquiv primitive first).symm.trans
        (transportEquiv primitive second)) value) = observe value := by
  constructor
  · intro interchangeable value
    have same := interchangeable ((transportEquiv primitive first).symm value)
    simpa only [Equiv.apply_symm_apply, Equiv.trans_apply] using same.symm
  · intro invariant value
    have same := invariant (transportEquiv primitive first value)
    simpa only [Equiv.trans_apply, Equiv.symm_apply_apply] using same.symm

/-! ## Agreement with the independently defined indexed family -/

private def codeFibre (code : Code) : Type :=
  match code.1 with
  | .packet => Fin code.2.length.succ
  | .channel => PUnit

private theorem canonical_cast {source target : IndexedType}
    (path : ConversionPath source target) :
    semanticFibreEquivOfPath path =
      Equiv.cast (congrArg codeFibre (path_preserves_normalCode path)) := by
  rcases source with ⟨sourceFamily, sourceIndex⟩
  rcases target with ⟨targetFamily, targetIndex⟩
  have families := congrArg Prod.fst (path_preserves_normalCode path)
  change sourceFamily = targetFamily at families
  subst targetFamily
  cases sourceFamily <;> rfl

private theorem canonical_refl (source : IndexedType) :
    semanticFibreEquivOfPath (reflexivePath source) = Equiv.refl (SemanticFibre source) := by
  rw [canonical_cast]
  rfl

private theorem canonical_symm {source target : IndexedType}
    (path : ConversionPath source target) :
    semanticFibreEquivOfPath (.symm path) = (semanticFibreEquivOfPath path).symm := by
  rw [canonical_cast, canonical_cast]
  exact Equiv.cast_symm _

private theorem canonical_trans {source middle target : IndexedType}
    (first : ConversionPath source middle) (second : ConversionPath middle target) :
    semanticFibreEquivOfPath (.trans first second) =
      (semanticFibreEquivOfPath first).trans (semanticFibreEquivOfPath second) := by
  rw [canonical_cast, canonical_cast, canonical_cast]
  exact Equiv.cast_trans _ _

/-- Only the primitive accepted certificate is interpreted directly by
the independently specified semantic fibre operation. -/
def certifiedStepTransport {source target : IndexedType}
    (certificate : ConversionStep source target) : SemanticFibre source ≃ SemanticFibre target :=
  semanticFibreEquivOfPath (.step certificate)

def transport {source target : IndexedType} (path : ConversionPath source target) :
    SemanticFibre source ≃ SemanticFibre target := transportEquiv certifiedStepTransport path

private def canonicalExtension : Extension (transportAlgebra SemanticFibre certifiedStepTransport) where
  onPath := fun {index} {_ _} path => by
    cases index
    exact semanticFibreEquivOfPath path
  onStep := by
    intro index source target certificate
    cases index
    rfl
  onRefl := by
    intro index source
    cases index
    exact canonical_refl source
  onSymm := by
    intro index source target path
    cases index
    exact canonical_symm path
  onTrans := by
    intro index source middle target first second
    cases index
    exact canonical_trans first second

/-- Constructorwise agreement, including reversal and composite evidence.
The desired whole-path agreement is not a primitive premise. -/
theorem transport_agrees {source target : IndexedType} (path : ConversionPath source target) :
    transport path = semanticFibreEquivOfPath path :=
  (canonicalExtension.onPath_unique path).symm

theorem transport_parallel {source target : IndexedType}
    (first second : ConversionPath source target) : transport first = transport second := by
  rw [transport_agrees, transport_agrees, canonical_cast, canonical_cast]

theorem transport_refl (source : IndexedType) (value : SemanticFibre source) :
    transport (reflexivePath source) value = value := by
  simp only [transport, transportEquiv, reflexivePath, Algebra.fold_refl,
    transportAlgebra, Equiv.refl_apply]

theorem transport_trans {source middle target : IndexedType}
    (first : ConversionPath source middle) (second : ConversionPath middle target)
    (value : SemanticFibre source) :
    transport (.trans first second) value = transport second (transport first value) := by
  simp only [transport, transportEquiv, Algebra.fold_trans, transportAlgebra, Equiv.trans_apply]

theorem transport_inverse {source target : IndexedType}
    (path : ConversionPath source target) (value : SemanticFibre source) :
    transport (.symm path) (transport path value) = value := by
  simp only [transport, transportEquiv, Algebra.fold_symm, transportAlgebra,
    Equiv.symm_apply_apply]

theorem application_observers_agree {source target : IndexedType}
    (first second : ConversionPath source target) (value : SemanticFibre source)
    {Observation : Type uObservation} (observe : SemanticFibre target → Observation) :
    observe (transport first value) = observe (transport second value) :=
  congrArg (fun equivalence => observe (equivalence value)) (transport_parallel first second)

/-- For a consumer allowed to inspect the retained route, replacement is
safe for all input values exactly when that inspection agrees in every
target fibre value. Surjectivity supplies the nontrivial reverse test. -/
theorem retained_observer_replacement_iff {source target : IndexedType}
    (first second : ConversionPath source target)
    {Observation : Type uObservation}
    (observe : ConversionPath source target → SemanticFibre target → Observation) :
    (∀ value, observe first (transport first value) = observe second (transport second value)) ↔
      ∀ value, observe first value = observe second value := by
  constructor
  · intro interchangeable value
    have same := interchangeable ((transport first).symm value)
    rw [← transport_parallel first second, Equiv.apply_symm_apply] at same
    exact same
  · intro independent value
    rw [← transport_parallel first second]
    exact independent _

/-! ## Actual substitution of symbolic indices and packet cursors -/

private def substituteCode (substitution : Nat → Term signature) (code : Code) : Code :=
  (code.1, code.2.flatMap (fun index => flatten (substitution index)))

private theorem substitution_code (substitution : Nat → Term signature) (type : IndexedType) :
    normalCode (type.subst substitution) = substituteCode substitution (normalCode type) :=
  Prod.ext rfl (flatten_subst substitution type.index)

private def substituteCodeValue (substitution : Nat → Term signature) (code : Code) :
    codeFibre code → codeFibre (substituteCode substitution code) := by
  rcases code with ⟨family, word⟩
  cases family with
  | packet =>
      intro cursor
      refine ⟨((word.take cursor.val).flatMap (fun index => flatten (substitution index))).length, ?_⟩
      have split : (word.take cursor.val).flatMap (fun index => flatten (substitution index)) ++
          (word.drop cursor.val).flatMap (fun index => flatten (substitution index)) =
            word.flatMap (fun index => flatten (substitution index)) := by
        rw [← List.flatMap_append, List.take_append_drop]
      have lengths := congrArg List.length split
      simp only [List.length_append] at lengths
      change _ < (word.flatMap (fun index => flatten (substitution index))).length.succ
      omega
  | channel => exact id

private theorem substituteCodeValue_natural (substitution : Nat → Term signature)
    {source target : Code} (same : source = target) (value : codeFibre source) :
    substituteCodeValue substitution target (cast (congrArg codeFibre same) value) =
      cast (congrArg codeFibre (congrArg (substituteCode substitution) same))
        (substituteCodeValue substitution source value) := by
  cases same
  rfl

/-- A packet value is a boundary cursor in its normalized word. Replacing
variables by words sends that cursor to the length of the replaced prefix.
The target fibre may grow or shrink; no invertibility is assumed. -/
def substituteValue (substitution : Nat → Term signature) (type : IndexedType)
    (value : SemanticFibre type) : SemanticFibre (type.subst substitution) :=
  cast (congrArg codeFibre (substitution_code substitution type)).symm
    (substituteCodeValue substitution (normalCode type) value)

/-- The actual structurally substituted accepted path commutes with the
independently defined cursor substitution. This uses word-substitution
normalization and its dependent value map, not parallel-path equality. -/
theorem substitute_transport (substitution : Nat → Term signature)
    {source target : IndexedType} (path : ConversionPath source target)
    (value : SemanticFibre source) :
    transport (substPath substitution path) (substituteValue substitution source value) =
      substituteValue substitution target (transport path value) := by
  rw [transport_agrees, transport_agrees, canonical_cast, canonical_cast]
  change
    cast (congrArg codeFibre (path_preserves_normalCode (substPath substitution path)))
      (cast (congrArg codeFibre (substitution_code substitution source)).symm
        (substituteCodeValue substitution (normalCode source) value)) =
    cast (congrArg codeFibre (substitution_code substitution target)).symm
      (substituteCodeValue substitution (normalCode target)
        (cast (congrArg codeFibre (path_preserves_normalCode path)) value))
  change codeFibre (normalCode source) at value
  rw [substituteCodeValue_natural substitution (path_preserves_normalCode path) value]
  simp only [cast_cast]

/-! ## Actual accepted typing receipts, visible values and retained history -/

namespace Controls

def expandedRightUnitPath : ConversionPath packetXUnit packetX :=
  .trans (reflexivePath packetXUnit) (.trans rightUnitPath (reflexivePath packetX))

def directReceipt : TypingReceipt packetValueXUnit packetX where
  source := packetXUnit
  typing := .token .packet (mul x one)
  conversion := rightUnitPath

def expandedReceipt : TypingReceipt packetValueXUnit packetX where
  source := packetXUnit
  typing := .token .packet (mul x one)
  conversion := expandedRightUnitPath

theorem receipt_path_sizes :
    pathConstructorCount directReceipt.conversion = 1 ∧
      pathConstructorCount expandedReceipt.conversion = 5 := ⟨rfl, rfl⟩

theorem accepted_routes_distinct : rightUnitPath ≠ expandedRightUnitPath := by
  intro same
  have sizes := congrArg pathConstructorCount same
  change 1 = 5 at sizes
  cases sizes

/-- The tested source and target fibres have two values; the selected one
is not a unit witness or an empty-fibre argument. -/
def cursor : SemanticFibre packetXUnit := ⟨1, by decide⟩

def targetCursor : SemanticFibre packetX := ⟨1, by decide⟩

theorem application_value : transport rightUnitPath cursor = targetCursor := by
  rw [transport_agrees]
  rfl

theorem two_accepted_routes_one_application :
    Nonempty (TypingReceipt packetValueXUnit packetX) ∧
      rightUnitPath ≠ expandedRightUnitPath ∧
      transport rightUnitPath cursor = targetCursor ∧
      transport expandedRightUnitPath cursor = targetCursor :=
  ⟨⟨directReceipt⟩, accepted_routes_distinct, application_value,
    (congrArg (fun equivalence => equivalence cursor)
      (transport_parallel expandedRightUnitPath rightUnitPath)).trans application_value⟩

/-- An application readout cannot reconstruct this route observation;
the negative uses the existing general no-factorization theorem. -/
theorem route_inspection_not_supported_by_mere_conversion :
    ¬ ∃ inspect : Nonempty (ConversionPath packetXUnit packetX) → Nat,
      ∀ path, inspect ⟨path⟩ = pathConstructorCount path :=
  no_path_observer_factors_through_mere pathConstructorCount rightUnitPath expandedRightUnitPath
    (by change (1 : Nat) ≠ 5; decide)

theorem route_inspection_rejects_replacement :
    ¬ ∀ value : SemanticFibre packetXUnit,
      (pathConstructorCount rightUnitPath, transport rightUnitPath value) =
        (pathConstructorCount expandedRightUnitPath, transport expandedRightUnitPath value) := by
  intro interchangeable
  have sizes := congrArg Prod.fst (interchangeable cursor)
  change 1 = 5 at sizes
  cases sizes

/-- This actual accepted-path layer is not route-UIP, even though all
parallel transports in the selected semantic family agree. -/
theorem application_coherence_without_routeUIP :
    (∀ {source target : IndexedType} (first second : ConversionPath source target),
      transport first = transport second) ∧
      ¬ ScopedIdentity.RouteUIP
        (ScopedIdentity.conversionLayer
          (computation State (fun {_index : Unit} => ConversionStep)) ()) := by
  refine ⟨transport_parallel, ?_⟩
  intro uip
  exact ScopedIdentity.routeUIP_excludes_distinctRoutes uip
    ⟨packetXUnit, packetX, rightUnitPath, expandedRightUnitPath, accepted_routes_distinct⟩

/-- Coherence for parallel evidence does not make differently indexed
semantic fibres equivalent or incorrectly typed application inputs valid. -/
theorem wrong_index_still_rejected :
    ¬ Nonempty (SemanticFibre packetX ≃ SemanticFibre packetXY) ∧
      ¬ Nonempty (TypingReceipt packetValueXUnit packetY) :=
  ⟨packet_fibres_are_genuinely_indexed, packetValue_has_no_wrong_index_receipt⟩

def expandIndex (index : Nat) : Term signature := mul (.var index) (.var (index + 1))

def expandedTargetCursor : SemanticFibre (packetX.subst expandIndex) := ⟨2, by decide⟩

/-- Substitution genuinely changes a two-value packet fibre to three
values, and sends the nonzero cursor to the new endpoint boundary. -/
theorem expanded_cursor_value :
    substituteValue expandIndex packetX targetCursor = expandedTargetCursor := by
  rfl

theorem substituted_application_value :
    transport (substPath expandIndex rightUnitPath)
        (substituteValue expandIndex packetXUnit cursor) = expandedTargetCursor := by
  rw [substitute_transport, application_value]
  exact expanded_cursor_value

/-- Erasing index variables collapses two admitted cursor values. Hence
the substitution square cannot be justified by an assumed fibre equivalence. -/
theorem erasing_substitution_not_injective :
    ¬ Function.Injective (substituteValue (fun _ => one) packetX) := by
  intro injective
  have same := injective (a₁ := (⟨0, by decide⟩ : SemanticFibre packetX))
    (a₂ := targetCursor) (by rfl)
  have impossible := congrArg (fun cursor : SemanticFibre packetX => cursor.val) same
  change 0 = 1 at impossible
  cases impossible

end Controls

#print axioms replacement_iff_loop_invariant
#print axioms transport_agrees
#print axioms transport_parallel
#print axioms retained_observer_replacement_iff
#print axioms substitute_transport
#print axioms Controls.two_accepted_routes_one_application
#print axioms Controls.route_inspection_rejects_replacement
#print axioms Controls.application_coherence_without_routeUIP
#print axioms Controls.wrong_index_still_rejected
#print axioms Controls.substituted_application_value
#print axioms Controls.erasing_substitution_not_injective

end Mettapedia.TypeTheory.MonoidIndexedTransportCoherence
