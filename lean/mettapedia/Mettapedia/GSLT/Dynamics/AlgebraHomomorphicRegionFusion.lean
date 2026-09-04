import Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted
import Mathlib.Tactic

/-!
# Algebra-homomorphic fusion inside deterministic regions

A deterministic region may interpret a well-sorted construction tree without
materializing the representation of every intermediate value.  This module
states the representation-independent condition which licenses that
transformation.

The source presentation supplies only kinds, leaves, and typed operations.  A
`PartialRealization` gives those constructors a possibly-failing meaning.
`Hom` is a kind-preserving map which commutes with leaves and operations,
including failure.  Evaluation is natural under every such homomorphism.
Consequently a region may evaluate in a compact carrier and cross into a
boxed carrier once at its declared boundary, provided no observer can inspect
intermediate boxes.

The cost result is deliberately conditional.  For a successful route with at
least one operation, eager intermediate materialization performs one crossing
per operation, while boundary-only materialization performs one.  The latter
is minimal only among realizations whose boundary contract requires a fresh
represented result.  No claim is made about allocation, cache, or wall-clock
optimality outside that cost observation.

The negative theorem is equally load-bearing: if two successful routes have
the same final value but an observer distinguishes their construction
histories, that observer cannot factor through the final value.  Such a region
must retain the observation boundary and is not admitted for fusion.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.AlgebraHomomorphicRegionFusion

open Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted

universe uKind uPresentationObject uSource uOperation uCarrier uTarget uThird
  uObservation

variable
  {presentation :
    ManySortedConstructionAlgebra.{
      uKind, uPresentationObject, uSource, uOperation}}

/-! ## Partial realizations of one many-sorted presentation -/

/-- A possibly-failing interpretation of one many-sorted source
presentation.  Logical absence remains distinct from physical specialization
decline; a runtime realization must place the latter outside this algebra. -/
structure PartialRealization
    (presentation :
      ManySortedConstructionAlgebra.{
        uKind, uPresentationObject, uSource, uOperation}) where
  Carrier : presentation.Kind -> Type uCarrier
  interpretSource : forall {kind},
    presentation.Source kind -> Option (Carrier kind)
  interpretOperation : forall {inputs output},
    presentation.Operation inputs output ->
      FamilyList Carrier inputs -> Option (Carrier output)

namespace PartialRealization

variable
  (realization :
    PartialRealization.{
      uKind, uPresentationObject, uSource, uOperation, uCarrier}
      presentation)

/- The evaluator uses `ULift` only to place its two dependent result families
in one universe.  Public definitions immediately project the values back. -/
mutual
  private def evaluateLift {kind : presentation.Kind} :
      ConstructionTree presentation kind ->
        ULift.{uKind} (Option (realization.Carrier kind))
    | .source value =>
        ⟨realization.interpretSource value⟩
    | .apply operation arguments =>
        match (evaluateArgumentsLift arguments).down with
        | none => ⟨none⟩
        | some values =>
            ⟨realization.interpretOperation operation values⟩

  private def evaluateArgumentsLift {kinds : List presentation.Kind} :
      ConstructionArguments presentation kinds ->
        ULift.{uCarrier}
          (Option (FamilyList realization.Carrier kinds))
    | .nil => ⟨some .nil⟩
    | .cons head tail =>
        match (evaluateLift head).down,
            (evaluateArgumentsLift tail).down with
        | some headValue, some tailValues =>
            ⟨some (.cons headValue tailValues)⟩
        | _, _ => ⟨none⟩
end

/-- Evaluate one well-sorted route in a partial realization. -/
def evaluate {kind : presentation.Kind}
    (route : ConstructionTree presentation kind) :
    Option (realization.Carrier kind) :=
  (evaluateLift realization route).down

/-- Evaluate the ordered arguments of one operation. -/
def evaluateArguments {kinds : List presentation.Kind}
    (arguments : ConstructionArguments presentation kinds) :
    Option (FamilyList realization.Carrier kinds) :=
  (evaluateArgumentsLift realization arguments).down

@[simp] theorem evaluate_source {kind : presentation.Kind}
    (value : presentation.Source kind) :
    realization.evaluate (.source value) =
      realization.interpretSource value :=
  rfl

@[simp] theorem evaluate_apply
    {inputs : List presentation.Kind} {output : presentation.Kind}
    (operation : presentation.Operation inputs output)
    (arguments : ConstructionArguments presentation inputs) :
    realization.evaluate (.apply operation arguments) =
      match realization.evaluateArguments arguments with
      | none => none
      | some values => realization.interpretOperation operation values :=
  by
    unfold evaluate evaluateArguments
    simp only [evaluateLift]
    split <;> rfl

@[simp] theorem evaluateArguments_nil :
    realization.evaluateArguments
        (.nil : ConstructionArguments presentation []) =
      some .nil :=
  rfl

@[simp] theorem evaluateArguments_cons
    {kind : presentation.Kind} {kinds : List presentation.Kind}
    (head : ConstructionTree presentation kind)
    (tail : ConstructionArguments presentation kinds) :
    realization.evaluateArguments (.cons head tail) =
      match realization.evaluate head,
          realization.evaluateArguments tail with
      | some headValue, some tailValues =>
          some (.cons headValue tailValues)
      | _, _ => none :=
  by
    unfold evaluate evaluateArguments
    simp only [evaluateArgumentsLift]
    split <;> rfl

end PartialRealization

/-! ## Family maps and algebra homomorphisms -/

theorem familyMap_id
    {Family : presentation.Kind -> Type uCarrier}
    {kinds : List presentation.Kind}
    (values : FamilyList Family kinds) :
    FamilyList.map (fun _ value => value) values = values := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [inductionHypothesis]

theorem familyMap_comp
    {First : presentation.Kind -> Type uCarrier}
    {Second : presentation.Kind -> Type uTarget}
    {Third : presentation.Kind -> Type uThird}
    (first : forall kind, First kind -> Second kind)
    (second : forall kind, Second kind -> Third kind)
    {kinds : List presentation.Kind}
    (values : FamilyList First kinds) :
    FamilyList.map second (FamilyList.map first values) =
      FamilyList.map (fun kind value => second kind (first kind value))
        values := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [inductionHypothesis]

/-- A map of partial algebras over the same source presentation.  It preserves
kind, leaves, operations, and failure exactly. -/
structure Hom
    (source : PartialRealization.{
      uKind, uPresentationObject, uSource, uOperation, uCarrier}
      presentation)
    (target : PartialRealization.{
      uKind, uPresentationObject, uSource, uOperation, uTarget}
      presentation) where
  map : forall kind, source.Carrier kind -> target.Carrier kind
  source_natural : forall {kind} (value : presentation.Source kind),
    target.interpretSource value =
      Option.map (map kind) (source.interpretSource value)
  operation_natural : forall {inputs output}
      (operation : presentation.Operation inputs output)
      (arguments : FamilyList source.Carrier inputs),
    target.interpretOperation operation (FamilyList.map map arguments) =
      Option.map (map output)
        (source.interpretOperation operation arguments)

namespace Hom

variable
  {source : PartialRealization.{
    uKind, uPresentationObject, uSource, uOperation, uCarrier}
    presentation}
  {target : PartialRealization.{
    uKind, uPresentationObject, uSource, uOperation, uTarget}
    presentation}
  {third : PartialRealization.{
    uKind, uPresentationObject, uSource, uOperation, uThird}
    presentation}

/-- Identity partial-algebra homomorphism. -/
def identity (source : PartialRealization.{
    uKind, uPresentationObject, uSource, uOperation, uCarrier}
    presentation) :
    Hom source source where
  map := fun _ value => value
  source_natural := by simp
  operation_natural := by
    intro inputs output operation arguments
    rw [familyMap_id]
    simp

/-- Composition of partial-algebra homomorphisms. -/
def compose (first : Hom source target) (second : Hom target third) :
    Hom source third where
  map := fun kind value => second.map kind (first.map kind value)
  source_natural := by
    intro kind value
    rw [second.source_natural, first.source_natural]
    simp [Function.comp_def]
  operation_natural := by
    intro inputs output operation arguments
    rw [<- familyMap_comp first.map second.map arguments]
    rw [second.operation_natural, first.operation_natural]
    simp [Function.comp_def]

@[simp] theorem identity_map {kind : presentation.Kind}
    (value : source.Carrier kind) :
    (identity source).map kind value = value :=
  rfl

@[simp] theorem compose_map (first : Hom source target)
    (second : Hom target third) {kind : presentation.Kind}
    (value : source.Carrier kind) :
    (compose first second).map kind value =
      second.map kind (first.map kind value) :=
  rfl

@[ext] theorem ext (first second : Hom source target)
    (maps : forall kind value,
      first.map kind value = second.map kind value) :
    first = second := by
  cases first with
  | mk firstMap firstSource firstOperation =>
      cases second with
      | mk secondMap secondSource secondOperation =>
          simp only at maps
          have sameMap : firstMap = secondMap := by
            funext kind value
            exact maps kind value
          cases sameMap
          rfl

@[simp] theorem identity_compose (hom : Hom source target) :
    compose (identity source) hom = hom := by
  ext kind value
  rfl

@[simp] theorem compose_identity (hom : Hom source target) :
    compose hom (identity target) = hom := by
  ext kind value
  rfl

theorem compose_assoc
    {fourth : PartialRealization.{
      uKind, uPresentationObject, uSource, uOperation, uObservation}
      presentation}
    (first : Hom source target) (second : Hom target third)
    (last : Hom third fourth) :
    compose (compose first second) last =
      compose first (compose second last) := by
  ext kind value
  rfl

mutual
  /-- Evaluation is natural under every partial-algebra homomorphism.  This is
  the semantic license for evaluating a deterministic region in one carrier
  and crossing representations only at its boundary. -/
  theorem evaluate_natural (hom : Hom source target)
      {kind : presentation.Kind}
      (route : ConstructionTree presentation kind) :
      target.evaluate route =
        Option.map (hom.map kind) (source.evaluate route) := by
    cases route with
    | source value =>
        exact hom.source_natural value
    | apply operation arguments =>
        simp only [PartialRealization.evaluate_apply]
        rw [evaluateArguments_natural hom arguments]
        cases observed : source.evaluateArguments arguments with
        | none => simp
        | some values =>
            simp only [Option.map_some]
            exact hom.operation_natural operation values

  theorem evaluateArguments_natural (hom : Hom source target)
      {kinds : List presentation.Kind}
      (arguments : ConstructionArguments presentation kinds) :
      target.evaluateArguments arguments =
        Option.map (FamilyList.map hom.map)
          (source.evaluateArguments arguments) := by
    cases arguments with
    | nil => rfl
    | @cons kind kinds head tail =>
        simp only [PartialRealization.evaluateArguments_cons]
        rw [evaluate_natural hom head]
        rw [evaluateArguments_natural hom tail]
        cases headObserved : source.evaluate head <;>
          cases tailObserved : source.evaluateArguments tail <;>
          simp
end

/-- Failure is reflected as well as preserved by a representation map. -/
theorem evaluate_none_iff (hom : Hom source target)
    {kind : presentation.Kind}
    (route : ConstructionTree presentation kind) :
    target.evaluate route = none <-> source.evaluate route = none := by
  rw [evaluate_natural hom route]
  exact Option.map_eq_none_iff

end Hom

/-! ## Exact operation and boundary-materialization accounting -/

mutual
  /-- Number of operation occurrences in one well-sorted route. -/
  def operationCount {kind : presentation.Kind} :
      ConstructionTree presentation kind -> Nat
    | .source _ => 0
    | .apply _ arguments => 1 + operationCountArguments arguments

  /-- Sum of operation occurrences in an ordered argument family. -/
  def operationCountArguments {kinds : List presentation.Kind} :
      ConstructionArguments presentation kinds -> Nat
    | .nil => 0
    | .cons head tail =>
        operationCount head + operationCountArguments tail
end

@[simp] theorem operationCount_source {kind : presentation.Kind}
    (value : presentation.Source kind) :
    operationCount (ConstructionTree.source value) = 0 :=
  rfl

@[simp] theorem operationCount_apply
    {inputs : List presentation.Kind} {output : presentation.Kind}
    (operation : presentation.Operation inputs output)
    (arguments : ConstructionArguments presentation inputs) :
    operationCount (ConstructionTree.apply operation arguments) =
      1 + operationCountArguments arguments :=
  rfl

/-- Eager intermediate materialization crosses the representation boundary
once for every successful operation result. -/
def eagerMaterializations
    (realization : PartialRealization.{
      uKind, uPresentationObject, uSource, uOperation, uCarrier}
      presentation)
    {kind : presentation.Kind}
    (route : ConstructionTree presentation kind) : Option Nat :=
  (realization.evaluate route).map (fun _ => operationCount route)

/-- Boundary-only materialization crosses once for a successful route which
contains an operation, and zero times for a source leaf already represented by
its caller. -/
def boundaryMaterializations
    (realization : PartialRealization.{
      uKind, uPresentationObject, uSource, uOperation, uCarrier}
      presentation)
    {kind : presentation.Kind}
    (route : ConstructionTree presentation kind) : Option Nat :=
  (realization.evaluate route).map
    (fun _ => if operationCount route = 0 then 0 else 1)

theorem failed_route_has_no_materialization_receipt
    (realization : PartialRealization.{
      uKind, uPresentationObject, uSource, uOperation, uCarrier}
      presentation)
    {kind : presentation.Kind}
    (route : ConstructionTree presentation kind)
    (failed : realization.evaluate route = none) :
    eagerMaterializations realization route = none /\
      boundaryMaterializations realization route = none := by
  simp [eagerMaterializations, boundaryMaterializations, failed]

/-- On every successful non-leaf route, boundary-only evaluation removes
exactly all but one of the eager representation crossings. -/
theorem successful_materialization_saving
    (realization : PartialRealization.{
      uKind, uPresentationObject, uSource, uOperation, uCarrier}
      presentation)
    {kind : presentation.Kind}
    (route : ConstructionTree presentation kind)
    (result : realization.Carrier kind)
    (succeeds : realization.evaluate route = some result)
    (hasOperation : 0 < operationCount route) :
    eagerMaterializations realization route =
        some (1 + (operationCount route - 1)) /\
      boundaryMaterializations realization route = some 1 := by
  constructor
  · simp [eagerMaterializations, succeeds]
    omega
  · simp [boundaryMaterializations, succeeds, Nat.ne_of_gt hasOperation]

/-- A cost assignment satisfies the fresh-boundary contract when every
successful operation route spends at least one representation crossing. -/
def FreshBoundaryCost
    (realization : PartialRealization.{
      uKind, uPresentationObject, uSource, uOperation, uCarrier}
      presentation)
    (cost : forall {kind : presentation.Kind},
      ConstructionTree presentation kind -> Nat) : Prop :=
  forall {kind : presentation.Kind}
      (route : ConstructionTree presentation kind)
      (result : realization.Carrier kind),
    realization.evaluate route = some result ->
      0 < operationCount route -> 1 <= cost route

/-- Total cost of the boundary-only strategy.  Failed routes and source leaves
do not cross the representation boundary; a successful route containing an
operation crosses exactly once. -/
def boundaryCrossingCost
    (realization : PartialRealization.{
      uKind, uPresentationObject, uSource, uOperation, uCarrier}
      presentation)
    {kind : presentation.Kind}
    (route : ConstructionTree presentation kind) : Nat :=
  match realization.evaluate route with
  | none => 0
  | some _ => if operationCount route = 0 then 0 else 1

/-- The boundary-only strategy is itself an admissible fresh-boundary cost. -/
theorem boundaryCrossingCost_fresh
    (realization : PartialRealization.{
      uKind, uPresentationObject, uSource, uOperation, uCarrier}
      presentation) :
    FreshBoundaryCost realization
      (boundaryCrossingCost realization) := by
  intro kind route result succeeds hasOperation
  simp [boundaryCrossingCost, succeeds, Nat.ne_of_gt hasOperation]

/-- The boundary-only strategy is pointwise least among all costs satisfying
the explicit fresh-boundary contract.  This is not a claim about realizations
which may reuse an existing represented result or expose no represented
boundary at all. -/
theorem boundaryCrossingCost_pointwise_minimal
    (realization : PartialRealization.{
      uKind, uPresentationObject, uSource, uOperation, uCarrier}
      presentation)
    (cost : forall {kind : presentation.Kind},
      ConstructionTree presentation kind -> Nat)
    (fresh : FreshBoundaryCost realization cost)
    {kind : presentation.Kind}
    (route : ConstructionTree presentation kind) :
    boundaryCrossingCost realization route <= cost route := by
  cases observed : realization.evaluate route with
  | none =>
      simp [boundaryCrossingCost, observed]
  | some result =>
      by_cases isLeaf : operationCount route = 0
      · simp [boundaryCrossingCost, observed, isLeaf]
      · have hasOperation : 0 < operationCount route :=
          Nat.pos_of_ne_zero isLeaf
        simpa [boundaryCrossingCost, observed, isLeaf] using
          fresh route result observed hasOperation

/-! ## The observer obstruction -/

/-- Ordinary final-value factorization for a common observation carrier. -/
def CommonFactorsThroughFinal
    (realization : PartialRealization.{
      uKind, uPresentationObject, uSource, uOperation, uCarrier}
      presentation)
    (Observation : Type uObservation)
    (observe : forall {kind : presentation.Kind},
      ConstructionTree presentation kind -> Observation) : Prop :=
  exists decode : forall kind, realization.Carrier kind -> Observation,
    forall {kind : presentation.Kind}
      (route : ConstructionTree presentation kind)
      (result : realization.Carrier kind),
      realization.evaluate route = some result ->
        observe route = decode kind result

/-- If equal final values arise from histories separated by an observer, that
observer cannot be reconstructed from the final value.  Fusion across that
observer is therefore inadmissible. -/
theorem no_common_factor_of_distinguishing_routes
    (realization : PartialRealization.{
      uKind, uPresentationObject, uSource, uOperation, uCarrier}
      presentation)
    (Observation : Type uObservation)
    (observe : forall {kind : presentation.Kind},
      ConstructionTree presentation kind -> Observation)
    {kind : presentation.Kind}
    (left right : ConstructionTree presentation kind)
    (result : realization.Carrier kind)
    (leftSucceeds : realization.evaluate left = some result)
    (rightSucceeds : realization.evaluate right = some result)
    (distinguished : observe left ≠ observe right) :
    ¬ CommonFactorsThroughFinal realization Observation observe := by
  intro factors
  rcases factors with ⟨decode, exactness⟩
  apply distinguished
  calc
    observe left = decode kind result := by
      simpa using exactness left result leftSucceeds
    _ = observe right := by
      simpa using (exactness right result rightSucceeds).symm

/-! ## Nontrivial positive and negative controls -/

namespace Canary

/-- Five independent operation families over one kind. -/
inductive Operation : List Unit -> Unit -> Type
  | add : Operation [(), ()] ()
  | multiply : Operation [(), ()] ()
  | successor : Operation [()] ()
  | double : Operation [()] ()
  | square : Operation [()] ()

def interpretNat : forall {inputs output},
    Operation inputs output ->
      FamilyList (fun _ : Unit => Nat) inputs -> Nat
  | _, _, .add, .cons left (.cons right .nil) => left + right
  | _, _, .multiply, .cons left (.cons right .nil) => left * right
  | _, _, .successor, .cons value .nil => Nat.succ value
  | _, _, .double, .cons value .nil => value + value
  | _, _, .square, .cons value .nil => value * value

def interpretInt : forall {inputs output},
    Operation inputs output ->
      FamilyList (fun _ : Unit => Int) inputs -> Int
  | _, _, .add, .cons left (.cons right .nil) => left + right
  | _, _, .multiply, .cons left (.cons right .nil) => left * right
  | _, _, .successor, .cons value .nil => value + 1
  | _, _, .double, .cons value .nil => value + value
  | _, _, .square, .cons value .nil => value * value

/-- The source syntax is independent of both partial realizations below. -/
def demoPresentation : ManySortedConstructionAlgebra where
  Kind := Unit
  Object := fun _ => Nat
  Source := fun _ => Nat
  Operation := Operation
  interpretSource := fun value => value
  interpretOperation := interpretNat

def naturalRealization : PartialRealization demoPresentation where
  Carrier := fun _ => Nat
  interpretSource := fun value => some value
  interpretOperation := fun operation arguments =>
    some (interpretNat operation arguments)

def integerRealization : PartialRealization demoPresentation where
  Carrier := fun _ => Int
  interpretSource := fun value => some (Int.ofNat value)
  interpretOperation := fun operation arguments =>
    some (interpretInt operation arguments)

theorem operation_natural
    {inputs : List Unit} {output : Unit}
    (operation : Operation inputs output)
    (arguments : FamilyList (fun _ : Unit => Nat) inputs) :
    integerRealization.interpretOperation operation
        (FamilyList.map (fun _ value => Int.ofNat value) arguments) =
      Option.map Int.ofNat
        (naturalRealization.interpretOperation operation arguments) := by
  cases operation with
  | add =>
      cases arguments with
      | cons left tail =>
          cases tail with
          | cons right rest =>
              cases rest
              change some (Int.ofNat left + Int.ofNat right) =
                some (Int.ofNat (left + right))
              simp
  | multiply =>
      cases arguments with
      | cons left tail =>
          cases tail with
          | cons right rest =>
              cases rest
              change some (Int.ofNat left * Int.ofNat right) =
                some (Int.ofNat (left * right))
              simp
  | successor =>
      cases arguments with
      | cons value tail =>
          cases tail
          change some (Int.ofNat value + 1) =
            some (Int.ofNat (Nat.succ value))
          simp
  | double =>
      cases arguments with
      | cons value tail =>
          cases tail
          change some (Int.ofNat value + Int.ofNat value) =
            some (Int.ofNat (value + value))
          simp
  | square =>
      cases arguments with
      | cons value tail =>
          cases tail
          change some (Int.ofNat value * Int.ofNat value) =
            some (Int.ofNat (value * value))
          simp

/-- A non-identity representation homomorphism covering all five operation
families. -/
def natToInt : Hom naturalRealization integerRealization where
  map := fun _ value => Int.ofNat value
  source_natural := by simp [naturalRealization, integerRealization]
  operation_natural := operation_natural

abbrev Tree := ConstructionTree demoPresentation ()
abbrev Arguments := ConstructionArguments demoPresentation

def leaf (value : Nat) : Tree := .source value
def unary (operation : Operation [()] ()) (argument : Tree) : Tree :=
  .apply operation (.cons argument .nil)
def binary (operation : Operation [(), ()] ())
    (left right : Tree) : Tree :=
  .apply operation (.cons left (.cons right .nil))

def addRoute : Tree := binary .add (leaf 2) (leaf 3)
def multiplyRoute : Tree := binary .multiply (leaf 3) (leaf 4)
def successorRoute : Tree := unary .successor (leaf 7)
def doubleRoute : Tree := unary .double (leaf 6)
def squareRoute : Tree := unary .square (leaf 5)

example : integerRealization.evaluate addRoute = some (5 : Int) := by
  change some (5 : Int) = some 5
  rfl
example : integerRealization.evaluate multiplyRoute = some (12 : Int) := by
  change some (12 : Int) = some 12
  rfl
example : integerRealization.evaluate successorRoute = some (8 : Int) := by
  change some (8 : Int) = some 8
  rfl
example : integerRealization.evaluate doubleRoute = some (12 : Int) := by
  change some (12 : Int) = some 12
  rfl
example : integerRealization.evaluate squareRoute = some (25 : Int) := by
  change some (25 : Int) = some 25
  rfl

/-- Two histories with the same final value and different operation counts. -/
def shortRoute : Tree := binary .add (leaf 1) (leaf 1)
def longRoute : Tree :=
  binary .add (leaf 0) (binary .add (leaf 1) (leaf 1))

example : naturalRealization.evaluate shortRoute = some (2 : Nat) := by
  change some (2 : Nat) = some 2
  rfl
example : naturalRealization.evaluate longRoute = some (2 : Nat) := by
  change some (2 : Nat) = some 2
  rfl
example : operationCount shortRoute = 1 := by decide
example : operationCount longRoute = 2 := by decide

/-- Operation-count observation cannot be erased merely because the final
values agree. -/
theorem operation_count_does_not_factor :
    ¬ CommonFactorsThroughFinal naturalRealization Nat
      (fun route => operationCount route) := by
  apply no_common_factor_of_distinguishing_routes
    naturalRealization Nat (fun route => operationCount route)
    shortRoute longRoute (2 : Nat)
  · change some (2 : Nat) = some 2
    rfl
  · change some (2 : Nat) = some 2
    rfl
  · decide

end Canary

#print axioms Hom.evaluate_natural
#print axioms Hom.evaluate_none_iff
#print axioms successful_materialization_saving
#print axioms boundaryCrossingCost_fresh
#print axioms boundaryCrossingCost_pointwise_minimal
#print axioms no_common_factor_of_distinguishing_routes
#print axioms Canary.operation_count_does_not_factor

end Mettapedia.GSLT.Dynamics.AlgebraHomomorphicRegionFusion
