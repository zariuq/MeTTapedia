import Mettapedia.GSLT.LanguageDef.Encodings.PatternShape
import Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingMorphism
import Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Interaction

/-!
# The pi-to-rho encoding is not a map of signatures

The encoding of the pi calculus into the rho calculus sends a process to a rho
term that depends on two names, a namespace and a value channel.  Three facts
make precise that it is not the action of a signature map.

* **On no process.**  For every process, every renaming of constructors and
  every choice of the two names, the renamed pi term differs from the
  encoding.  The reason is shape: inaction becomes an empty parallel
  composition, an output acquires a dereference, a restriction becomes a
  request in parallel with an input, a replication is wrapped.
* **Not a function of the term.**  The encoding of a restriction determines
  both names, so no function of the pi term alone produces it.
* **Not into the rho calculus as authored.**  The image uses a replication
  constructor that the authored rho calculus does not declare, and free names
  as channels, so encoded terms are not closed terms of the rho calculus.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (closeFVar)
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context (parComponents)

open private rhoPar_eq_parComponents_append from
  Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingMorphism

/-! ## Shapes of parallel compositions -/

/-- The components a shape contributes to a flattened parallel composition. -/
def shapeComponents : PatternShape → List PatternShape
  | .collection .hashBag elements false => elements
  | shape => [shape]

/-- The shape of a flattened parallel composition of two shapes. -/
def shapeParallel (left right : PatternShape) : PatternShape :=
  .collection .hashBag (shapeComponents left ++ shapeComponents right) false

/-- The two flattening parallel compositions are one function. -/
theorem piPar_eq_rhoPar (left right : Pattern) : piPar left right = rhoPar left right := by
  cases left <;> cases right <;>
    simp only [piPar, rhoPar] <;>
    (repeat (first | cases ‹CollType› | cases ‹Option String›)) <;>
    rfl

theorem map_patternShape_parComponents (pattern : Pattern) :
    (parComponents pattern).map patternShape = shapeComponents (patternShape pattern) := by
  rcases pattern with _ | _ | _ | _ | _ | _ | ⟨kind, elements, rest⟩ <;>
    try rfl
  cases kind <;> cases rest <;>
    simp [parComponents, patternShape, shapeComponents]

/-- The shape of a flattened parallel composition. -/
theorem patternShape_rhoPar (left right : Pattern) :
    patternShape (rhoPar left right) =
      shapeParallel (patternShape left) (patternShape right) := by
  rw [rhoPar_eq_parComponents_append]
  simp only [patternShape, patternShapeList_eq_map, List.map_append,
    map_patternShape_parComponents, shapeParallel, Option.isSome_none]

/-! ## The shapes of the two readings of a process -/

/-- The shape of a process as a pi term. -/
def piShape : Process → PatternShape
  | .nil => .application []
  | .par left right => shapeParallel (piShape left) (piShape right)
  | .input _ _ body => .application [.leaf, .binder (piShape body)]
  | .output _ _ => .application [.leaf, .leaf]
  | .nu _ body => .application [.binder (piShape body)]
  | .replicate _ _ body => .application [.leaf, .binder (piShape body)]

/-- The shape of the encoding of a process.  It does not depend on the two
names. -/
def rhoShape : Process → PatternShape
  | .nil => .collection .hashBag [] false
  | .par left right => shapeParallel (rhoShape left) (rhoShape right)
  | .input _ _ body => .application [.leaf, .binder (rhoShape body)]
  | .output _ _ => .application [.leaf, .application [.leaf]]
  | .nu _ body =>
      .collection .hashBag
        [.application [.leaf, .leaf], .application [.leaf, .binder (rhoShape body)]] false
  | .replicate _ _ body => .application [.application [.leaf, .binder (rhoShape body)]]

theorem patternShape_piToPattern :
    ∀ process : Process, patternShape (piToPattern process) = piShape process
  | .nil => rfl
  | .par left right => by
      rw [piToPattern, piPar_eq_rhoPar, patternShape_rhoPar, patternShape_piToPattern left,
        patternShape_piToPattern right, piShape]
  | .input _ bound body => by
      simp only [piToPattern, patternShape, patternShapeList_eq_map, List.map_cons, List.map_nil,
        patternShape_closeFVar bound (piToPattern body) 0, patternShape_piToPattern body, piShape]
  | .output _ _ => rfl
  | .nu bound body => by
      simp only [piToPattern, patternShape, patternShapeList_eq_map, List.map_cons, List.map_nil,
        patternShape_closeFVar bound (piToPattern body) 0, patternShape_piToPattern body, piShape]
  | .replicate _ bound body => by
      simp only [piToPattern, patternShape, patternShapeList_eq_map, List.map_cons, List.map_nil,
        patternShape_closeFVar bound (piToPattern body) 0, patternShape_piToPattern body, piShape]

theorem patternShape_encode :
    ∀ (process : Process) (n v : String), patternShape (encode process n v) = rhoShape process
  | .nil, _, _ => rfl
  | .par left right, n, v => by
      rw [encode, patternShape_rhoPar, patternShape_encode left, patternShape_encode right,
        rhoShape]
  | .input _ bound body, n, v => by
      simp only [encode, rhoInput, piNameToRhoName, patternShape, patternShapeList_eq_map,
        List.map_cons, List.map_nil, patternShape_closeFVar bound (encode body n v) 0,
        patternShape_encode body n v, rhoShape]
  | .output _ _, _, _ => rfl
  | .nu bound body, n, v => by
      rw [encode, patternShape_rhoPar]
      simp only [rhoOutput, rhoInput, patternShape, patternShapeList_eq_map, List.map_cons,
        List.map_nil, patternShape_closeFVar bound (encode body (n ++ "_" ++ n) v) 0,
        patternShape_encode body (n ++ "_" ++ n) v, rhoShape, shapeParallel, shapeComponents,
        List.cons_append, List.nil_append]
  | .replicate _ bound body, n, v => by
      simp only [encode, rhoReplicate, rhoInput, piNameToRhoName, patternShape,
        patternShapeList_eq_map, List.map_cons, List.map_nil,
        patternShape_closeFVar bound (encode body (n ++ "_rep") v) 0,
        patternShape_encode body (n ++ "_rep") v, rhoShape]

/-! ## Counting constructors -/

/-- Occurrences of inaction. -/
def Process.nilCount : Process → Nat
  | .nil => 1
  | .par left right => left.nilCount + right.nilCount
  | .input _ _ body => body.nilCount
  | .output _ _ => 0
  | .nu _ body => body.nilCount
  | .replicate _ _ body => body.nilCount

/-- Occurrences of output. -/
def Process.outputCount : Process → Nat
  | .nil => 0
  | .par left right => left.outputCount + right.outputCount
  | .input _ _ body => body.outputCount
  | .output _ _ => 1
  | .nu _ body => body.outputCount
  | .replicate _ _ body => body.outputCount

/-- Occurrences of input. -/
def Process.inputCount : Process → Nat
  | .nil => 0
  | .par left right => left.inputCount + right.inputCount
  | .input _ _ body => 1 + body.inputCount
  | .output _ _ => 0
  | .nu _ body => body.inputCount
  | .replicate _ _ body => body.inputCount

/-- Occurrences of restriction. -/
def Process.restrictionCount : Process → Nat
  | .nil => 0
  | .par left right => left.restrictionCount + right.restrictionCount
  | .input _ _ body => body.restrictionCount
  | .output _ _ => 0
  | .nu _ body => 1 + body.restrictionCount
  | .replicate _ _ body => body.restrictionCount

/-- Occurrences of replication. -/
def Process.replicationCount : Process → Nat
  | .nil => 0
  | .par left right => left.replicationCount + right.replicationCount
  | .input _ _ body => body.replicationCount
  | .output _ _ => 0
  | .nu _ body => body.replicationCount
  | .replicate _ _ body => 1 + body.replicationCount

/-- Every process has a leaf: an inaction or an output. -/
theorem Process.leaf_pos : ∀ process : Process, 0 < process.nilCount + process.outputCount
  | .nil => by simp [Process.nilCount]
  | .par left right => by
      have := Process.leaf_pos left
      simp only [Process.nilCount, Process.outputCount]
      omega
  | .input _ _ body => Process.leaf_pos body
  | .output _ _ => by simp [Process.outputCount]
  | .nu _ body => Process.leaf_pos body
  | .replicate _ _ body => Process.leaf_pos body

theorem arityCountList_shapeComponents (arity : Nat) (shape : PatternShape) :
    PatternShape.arityCountList arity (shapeComponents shape) = shape.arityCount arity := by
  rcases shape with _ | _ | _ | _ | _ | ⟨kind, elements, isOpen⟩
  case collection =>
    cases kind <;> cases isOpen <;>
      simp [shapeComponents, PatternShape.arityCount, PatternShape.arityCountList]
  all_goals simp [shapeComponents, PatternShape.arityCountList]

theorem arityCount_shapeParallel (arity : Nat) (left right : PatternShape) :
    (shapeParallel left right).arityCount arity =
      left.arityCount arity + right.arityCount arity := by
  rw [shapeParallel, PatternShape.arityCount, PatternShape.arityCountList_append,
    arityCountList_shapeComponents, arityCountList_shapeComponents]

/-- As a pi term a process has one nullary application per inaction. -/
theorem arityCount_zero_piShape :
    ∀ process : Process, (piShape process).arityCount 0 = process.nilCount
  | .nil => by simp [piShape, PatternShape.arityCount, PatternShape.arityCountList,
      Process.nilCount]
  | .par left right => by
      rw [piShape, arityCount_shapeParallel, arityCount_zero_piShape left,
        arityCount_zero_piShape right, Process.nilCount]
  | .input _ _ body => by
      simp [piShape, PatternShape.arityCount, PatternShape.arityCountList,
        arityCount_zero_piShape body, Process.nilCount]
  | .output _ _ => by
      simp [piShape, PatternShape.arityCount, PatternShape.arityCountList, Process.nilCount]
  | .nu _ body => by
      simp [piShape, PatternShape.arityCount, PatternShape.arityCountList,
        arityCount_zero_piShape body, Process.nilCount]
  | .replicate _ _ body => by
      simp [piShape, PatternShape.arityCount, PatternShape.arityCountList,
        arityCount_zero_piShape body, Process.nilCount]

/-- The encoding of a process has no nullary application. -/
theorem arityCount_zero_rhoShape :
    ∀ process : Process, (rhoShape process).arityCount 0 = 0
  | .nil => by simp [rhoShape, PatternShape.arityCount, PatternShape.arityCountList]
  | .par left right => by
      rw [rhoShape, arityCount_shapeParallel, arityCount_zero_rhoShape left,
        arityCount_zero_rhoShape right]
  | .input _ _ body => by
      simp [rhoShape, PatternShape.arityCount, PatternShape.arityCountList,
        arityCount_zero_rhoShape body]
  | .output _ _ => by
      simp [rhoShape, PatternShape.arityCount, PatternShape.arityCountList]
  | .nu _ body => by
      simp [rhoShape, PatternShape.arityCount, PatternShape.arityCountList,
        arityCount_zero_rhoShape body]
  | .replicate _ _ body => by
      simp [rhoShape, PatternShape.arityCount, PatternShape.arityCountList,
        arityCount_zero_rhoShape body]

/-- As a pi term a process has one unary application per restriction. -/
theorem arityCount_one_piShape :
    ∀ process : Process, (piShape process).arityCount 1 = process.restrictionCount
  | .nil => by simp [piShape, PatternShape.arityCount, PatternShape.arityCountList,
      Process.restrictionCount]
  | .par left right => by
      rw [piShape, arityCount_shapeParallel, arityCount_one_piShape left,
        arityCount_one_piShape right, Process.restrictionCount]
  | .input _ _ body => by
      simp [piShape, PatternShape.arityCount, PatternShape.arityCountList,
        arityCount_one_piShape body, Process.restrictionCount]
  | .output _ _ => by
      simp [piShape, PatternShape.arityCount, PatternShape.arityCountList,
        Process.restrictionCount]
  | .nu _ body => by
      simp [piShape, PatternShape.arityCount, PatternShape.arityCountList,
        arityCount_one_piShape body, Process.restrictionCount]
  | .replicate _ _ body => by
      simp [piShape, PatternShape.arityCount, PatternShape.arityCountList,
        arityCount_one_piShape body, Process.restrictionCount]

/-- The encoding of a process has one unary application per output, the
dereference of the name it carries, and one per replication. -/
theorem arityCount_one_rhoShape :
    ∀ process : Process,
      (rhoShape process).arityCount 1 = process.outputCount + process.replicationCount
  | .nil => by simp [rhoShape, PatternShape.arityCount, PatternShape.arityCountList,
      Process.outputCount, Process.replicationCount]
  | .par left right => by
      rw [rhoShape, arityCount_shapeParallel, arityCount_one_rhoShape left,
        arityCount_one_rhoShape right, Process.outputCount, Process.replicationCount]
      omega
  | .input _ _ body => by
      simp [rhoShape, PatternShape.arityCount, PatternShape.arityCountList,
        arityCount_one_rhoShape body, Process.outputCount, Process.replicationCount]
  | .output _ _ => by
      simp [rhoShape, PatternShape.arityCount, PatternShape.arityCountList,
        Process.outputCount, Process.replicationCount]
  | .nu _ body => by
      simp [rhoShape, PatternShape.arityCount, PatternShape.arityCountList,
        arityCount_one_rhoShape body, Process.outputCount, Process.replicationCount]
  | .replicate _ _ body => by
      simp [rhoShape, PatternShape.arityCount, PatternShape.arityCountList,
        arityCount_one_rhoShape body, Process.outputCount, Process.replicationCount]
      omega

/-- As a pi term a process has one binary application per input, output and
replication. -/
theorem arityCount_two_piShape :
    ∀ process : Process,
      (piShape process).arityCount 2 =
        process.inputCount + process.outputCount + process.replicationCount
  | .nil => by simp [piShape, PatternShape.arityCount, PatternShape.arityCountList,
      Process.inputCount, Process.outputCount, Process.replicationCount]
  | .par left right => by
      rw [piShape, arityCount_shapeParallel, arityCount_two_piShape left,
        arityCount_two_piShape right, Process.inputCount, Process.outputCount,
        Process.replicationCount]
      omega
  | .input _ _ body => by
      simp [piShape, PatternShape.arityCount, PatternShape.arityCountList,
        arityCount_two_piShape body, Process.inputCount, Process.outputCount,
        Process.replicationCount]
  | .output _ _ => by
      simp [piShape, PatternShape.arityCount, PatternShape.arityCountList,
        Process.inputCount, Process.outputCount, Process.replicationCount]
  | .nu _ body => by
      simp [piShape, PatternShape.arityCount, PatternShape.arityCountList,
        arityCount_two_piShape body, Process.inputCount, Process.outputCount,
        Process.replicationCount]
  | .replicate _ _ body => by
      simp [piShape, PatternShape.arityCount, PatternShape.arityCountList,
        arityCount_two_piShape body, Process.inputCount, Process.outputCount,
        Process.replicationCount]
      omega

/-- The encoding of a process has one binary application per input, output
and replication, and two per restriction: the request and the input that
awaits the fresh name. -/
theorem arityCount_two_rhoShape :
    ∀ process : Process,
      (rhoShape process).arityCount 2 =
        process.inputCount + process.outputCount + process.replicationCount +
          2 * process.restrictionCount
  | .nil => by simp [rhoShape, PatternShape.arityCount, PatternShape.arityCountList,
      Process.inputCount, Process.outputCount, Process.replicationCount,
      Process.restrictionCount]
  | .par left right => by
      rw [rhoShape, arityCount_shapeParallel, arityCount_two_rhoShape left,
        arityCount_two_rhoShape right, Process.inputCount, Process.outputCount,
        Process.replicationCount, Process.restrictionCount]
      omega
  | .input _ _ body => by
      simp [rhoShape, PatternShape.arityCount, PatternShape.arityCountList,
        arityCount_two_rhoShape body, Process.inputCount, Process.outputCount,
        Process.replicationCount, Process.restrictionCount]
  | .output _ _ => by
      simp [rhoShape, PatternShape.arityCount, PatternShape.arityCountList,
        Process.inputCount, Process.outputCount, Process.replicationCount,
        Process.restrictionCount]
  | .nu _ body => by
      simp [rhoShape, PatternShape.arityCount, PatternShape.arityCountList,
        arityCount_two_rhoShape body, Process.inputCount, Process.outputCount,
        Process.replicationCount, Process.restrictionCount]
      omega
  | .replicate _ _ body => by
      simp [rhoShape, PatternShape.arityCount, PatternShape.arityCountList,
        arityCount_two_rhoShape body, Process.inputCount, Process.outputCount,
        Process.replicationCount, Process.restrictionCount]
      omega

/-- **The two readings of a process never have the same shape.** -/
theorem piShape_ne_rhoShape (process : Process) : piShape process ≠ rhoShape process := by
  intro same
  have zero := congrArg (PatternShape.arityCount 0) same
  have one := congrArg (PatternShape.arityCount 1) same
  have two := congrArg (PatternShape.arityCount 2) same
  rw [arityCount_zero_piShape, arityCount_zero_rhoShape] at zero
  rw [arityCount_one_piShape, arityCount_one_rhoShape] at one
  rw [arityCount_two_piShape, arityCount_two_rhoShape] at two
  have leaf := Process.leaf_pos process
  omega

/-! ## The encoding is not a signature map -/

/-- **On no process is the encoding the action of a signature map.**  Whatever
the renaming of constructors and whatever the two names, the renamed pi term
is not the encoding of the process. -/
theorem encode_not_signatureMap (process : Process) (symbols : LanguageDefSymbolMap)
    (n v : String) : mapPattern symbols (piToPattern process) ≠ encode process n v :=
  mapPattern_ne_of_shape_ne
    (by
      rw [patternShape_piToPattern, patternShape_encode]
      exact piShape_ne_rhoShape process)
    symbols

/-- The term action of a structural morphism between validated languages is
never the encoding, on any process. -/
theorem encode_not_structural {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) (process : Process) (n v : String) :
    mapPattern morphism.symbols (piToPattern process) ≠ encode process n v :=
  encode_not_signatureMap process morphism.symbols n v

/-- **No morphism of interactive GSLTs out of the pi calculus acts as the
encoding.**  The term action of such a morphism is the signature map of its
structural part, so on a closed term that reads a process it differs from the
encoding of that process, whatever the target theory. -/
theorem encode_not_igsltMorphism {target : IGSLT}
    (morphism : IGSLT.Morphism Interaction.piIGSLT target)
    (term : Interaction.piInteractivePresentation.Term) (process : Process)
    (reads : term.1 = piToPattern process) (n v : String) :
    (morphism.mapTerm term).1 ≠ encode process n v := by
  change mapPattern morphism.structural.structural.symbols term.1 ≠ _
  rw [reads]
  exact encode_not_signatureMap process _ n v

/-- Inaction as a closed term of the pi calculus. -/
def nilTerm : Interaction.piInteractivePresentation.Term :=
  ClosedTerm.ofCheck (piToPattern .nil) (by decide +kernel)

/-- Inaction is already not preserved: a morphism sends it to a nullary
constructor, and the encoding sends it to the empty parallel composition. -/
theorem nil_image_ne_encoding {target : IGSLT}
    (morphism : IGSLT.Morphism Interaction.piIGSLT target) (n v : String) :
    (morphism.mapTerm nilTerm).1 ≠ encode .nil n v :=
  encode_not_igsltMorphism morphism nilTerm .nil rfl n v

/-- **The encoding of a restriction determines both names.** -/
theorem encode_nu_parameters_injective {x : Name} {body : Process} {n n' v v' : String}
    (same : encode (.nu x body) n v = encode (.nu x body) n' v') : n = n' ∧ v = v' := by
  have unfolded : ∀ (m w : String), encode (.nu x body) m w =
      .collection .hashBag
        [.apply "POutput" [.fvar w, .fvar m],
          rhoInput (.fvar m) x (encode body (m ++ "_" ++ m) w)] none := fun _ _ => rfl
  rw [unfolded n v, unfolded n' v'] at same
  injection same with _ elements _
  injection elements with request _
  injection request with _ arguments
  simp only [List.cons.injEq, Pattern.fvar.injEq, and_true] at arguments
  exact ⟨arguments.2, arguments.1⟩

/-- **The encoding is not a function of the term alone.**  No translation of
pi terms produces the encoding of a restriction at every pair of names. -/
theorem no_parameter_free_translation (translate : Pattern → Pattern) (x : Name)
    (body : Process) :
    ¬ ∀ n v : String, translate (piToPattern (.nu x body)) = encode (.nu x body) n v := by
  intro agrees
  have same := (agrees "a" "v").symm.trans (agrees "b" "v")
  have names := (encode_nu_parameters_injective same).1
  exact absurd names (by decide)

/-! ## The image is not in the rho calculus as authored -/

/-- The authored rho calculus declares no replication. -/
theorem rhoCalc_declares_no_replication :
    ∀ rule ∈ rhoCalc.terms, rule.label ≠ "PReplicate" := by
  decide

/-- **The encoding of a replication is not a term of the authored rho
calculus**, in any typing context. -/
theorem encode_replicate_untypable (x y : Name) (body : Process) (n v : String)
    (free : FreeTypeContext) (bound : List TypeExpr) (type : TypeExpr) :
    ¬ HasType rhoCalc free bound (encode (.replicate x y body) n v) type := by
  intro typed
  have unfolded : encode (.replicate x y body) n v =
      .apply "PReplicate" [rhoInput (piNameToRhoName x) y (encode body (n ++ "_rep") v)] := rfl
  rw [unfolded] at typed
  generalize shape : Pattern.apply "PReplicate"
    [rhoInput (piNameToRhoName x) y (encode body (n ++ "_rep") v)] = pattern at typed
  cases typed with
  | bvar _ => cases shape
  | fvar _ => cases shape
  | @constructor _ rule _ membership _ _ =>
      injection shape with label _
      exact rhoCalc_declares_no_replication rule membership label.symm
  | lambda _ => cases shape
  | multiLambda _ => cases shape
  | subst _ _ => cases shape
  | collection _ => cases shape
  | collectionConstructor _ _ _ => cases shape

/-- **The encoding of an output is not a closed term**: its channel is a free
name. -/
theorem encode_output_not_closed (x z : Name) (n v : String) (bound : List TypeExpr)
    (type : TypeExpr) :
    ¬ HasType rhoCalc FreeTypeContext.empty bound (encode (.output x z) n v) type := by
  intro typed
  have unfolded : encode (.output x z) n v =
      .apply "POutput" [.fvar x, .apply "PDrop" [.fvar z]] := rfl
  rw [unfolded] at typed
  generalize shape : Pattern.apply "POutput" [.fvar x, .apply "PDrop" [.fvar z]] = pattern
    at typed
  cases typed with
  | bvar _ => cases shape
  | fvar _ => cases shape
  | @constructor _ rule _ membership _ arguments =>
      injection shape with _ sameArguments
      subst sameArguments
      generalize rule.params = parameters at arguments
      cases arguments with
      | cons _ _ channel _ =>
          cases channel with
          | fvar lookup => simp [FreeTypeContext.empty] at lookup
  | lambda _ => cases shape
  | multiLambda _ => cases shape
  | subst _ _ => cases shape
  | collection _ => cases shape
  | collectionConstructor _ _ _ => cases shape

end Mettapedia.Languages.ProcessCalculi.PiCalculus
