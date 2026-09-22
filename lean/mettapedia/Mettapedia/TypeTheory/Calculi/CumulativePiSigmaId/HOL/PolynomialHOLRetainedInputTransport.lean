import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.PolynomialHOLRetainedInputs

/-!
# Native substitution of exact-input proof-plan trees

The existing Free fold has a substitution-indexed function carrier. Every
retained child moves at its own scope; a primitive routing square identifies
that moved input with the actual target child input. No tree representation or
recursive compiler is added. Substitution here is syntax, not an assertion of
native typing for arbitrary input maps.
-/

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PolynomialHOLRetainedInputTransport

open Mettapedia.Logic Presentation FormationSensitiveHOLInterface
open HOLNativeGenericProofCompiler ProofSearch ProofObligations
open Mettapedia.TypeTheory Mettapedia.TypeTheory.IndexedPolynomial
open PolynomialHOLRetainedInputs

variable {Base : Type} {Const : HOL.Ty Base → Type}

def moveInput {goal : HOLAdapter.Goal Base Const} (input : Input goal)
    {target : Nat} (sigma : Sub Tower.Head input.1 target) : Input goal :=
  ⟨target, (fun index => subst sigma (input.2.1 index)),
    (fun index => subst sigma (input.2.2 index))⟩

def moveIndex (index : Index Base Const) {target : Nat}
    (sigma : Sub Tower.Head index.2.1 target) : Index Base Const :=
  ⟨index.1, moveInput index.2 sigma⟩

variable {Routes : HOLAdapter.Goal Base Const → Type}
variable (methods : ∀ goal, Routes goal → Refinement HOLAdapter.Solution goal)
variable (routing : Routing methods)

/-- A constructor determines the substitution at each actual child scope. -/
abbrev ChildSubstitution := ∀ (index : Index Base Const) (route : Routes index.1)
    (target : Nat), Sub Tower.Head index.2.1 target →
    ∀ premise, Σ childTarget : Nat,
      Sub Tower.Head (routing index.1 route index.2 premise).1 childTarget

variable (childSubstitution : ChildSubstitution methods routing)

/-- Compatibility is only equality of the primitive routed input maps. -/
abbrev RoutingSquare := ∀ (index : Index Base Const) (route : Routes index.1)
    (target : Nat) (sigma : Sub Tower.Head index.2.1 target) (premise : (methods index.1 route).Premise),
  moveInput (routing index.1 route index.2 premise)
      (childSubstitution index route target sigma premise).2 =
    routing index.1 route (moveInput index.2 sigma) premise

variable (square : RoutingSquare methods routing childSubstitution)

abbrev HoleAction (Holes Next : Unit → Index Base Const → Type) :=
  ∀ base (index : Index Base Const) (target : Nat) (sigma : Sub Tower.Head index.2.1 target),
    Holes base index → Next base (moveIndex index sigma)

def transportAlgebra (Next : Unit → Index Base Const → Type) :
    (PolynomialPlans.polynomial (inputMethods methods routing)).Algebra
      (fun base index => ∀ target (sigma : Sub Tower.Head index.2.1 target),
        (PolynomialPlans.polynomial (inputMethods methods routing)).Free
          Next base (moveIndex index sigma)) where
  act := fun base index inputLayer target sigma =>
    Free.node _ inputLayer.1 (fun premise =>
      Eq.mp (congrArg
        (fun input => (PolynomialPlans.polynomial (inputMethods methods routing)).Free
          Next base ⟨(methods index.1 inputLayer.1).query premise, input⟩)
        (square index inputLayer.1 target sigma premise))
        (inputLayer.2 premise
          (childSubstitution index inputLayer.1 target sigma premise).1
          (childSubstitution index inputLayer.1 target sigma premise).2))

noncomputable def transport {Holes Next : Unit → Index Base Const → Type}
    (holes : HoleAction Holes Next) :=
  Free.fold (PolynomialPlans.polynomial (inputMethods methods routing))
    (fun base index hole target sigma => Free.pure _ (holes base index target sigma hole))
    (transportAlgebra methods routing childSubstitution square Next)

@[simp] theorem transport_node {Holes Next : Unit → Index Base Const → Type}
    (holes : HoleAction Holes Next) {base : Unit} {index : Index Base Const}
    (route : Routes index.1)
    (children : ∀ premise,
      (PolynomialPlans.polynomial (inputMethods methods routing)).Free Holes base
        ((inputMethods methods routing index route).query premise))
    (target : Nat) (sigma : Sub Tower.Head index.2.1 target) :
    transport methods routing childSubstitution square holes base index
      (Free.node _ route children) target sigma =
    Free.node (PolynomialPlans.polynomial (inputMethods methods routing))
      (holes := Next) (base := base) (index := moveIndex index sigma) route
      (fun premise => Eq.mp (congrArg
        (fun input => (PolynomialPlans.polynomial (inputMethods methods routing)).Free
          Next base ⟨(methods index.1 route).query premise, input⟩)
        (square index route target sigma premise))
        (transport methods routing childSubstitution square holes base _ (children premise)
          (childSubstitution index route target sigma premise).1
          (childSubstitution index route target sigma premise).2)) := rfl

theorem bind_cast {Holes Next : Unit → Index Base Const → Type}
    (fill : ∀ base index, Holes base index →
      (PolynomialPlans.polynomial (inputMethods methods routing)).Free Next base index)
    {base : Unit} {goal : HOLAdapter.Goal Base Const} {first second : Input goal}
    (equal : first = second)
    (plan : (PolynomialPlans.polynomial (inputMethods methods routing)).Free Holes base ⟨goal, first⟩) :
    Free.bind _ fill base ⟨goal, second⟩
      (Eq.mp (congrArg (fun input =>
        (PolynomialPlans.polynomial (inputMethods methods routing)).Free Holes base ⟨goal, input⟩)
        equal) plan) =
    Eq.mp (congrArg (fun input =>
      (PolynomialPlans.polynomial (inputMethods methods routing)).Free Next base ⟨goal, input⟩)
      equal) (Free.bind _ fill base ⟨goal, first⟩ plan) := by
  cases equal
  rfl

/-- Replacement plans must themselves be transported at the hole's actual
input. This local substitution compatibility extends to the surrounding tree. -/
theorem transport_fill {Holes Next TargetHoles TargetNext : Unit → Index Base Const → Type}
    (holes : HoleAction Holes TargetHoles) (next : HoleAction Next TargetNext)
    (sourceFill : ∀ base index, Holes base index →
      (PolynomialPlans.polynomial (inputMethods methods routing)).Free Next base index)
    (targetFill : ∀ base index, TargetHoles base index →
      (PolynomialPlans.polynomial (inputMethods methods routing)).Free TargetNext base index)
    (fillSquare : ∀ base index target sigma hole,
      transport methods routing childSubstitution square next base index
        (sourceFill base index hole) target sigma =
      targetFill base (moveIndex index sigma) (holes base index target sigma hole))
    {base : Unit} {index : Index Base Const}
    (plan : (PolynomialPlans.polynomial (inputMethods methods routing)).Free Holes base index)
    (target : Nat) (sigma : Sub Tower.Head index.2.1 target) :
    transport methods routing childSubstitution square next base index
      (Free.bind _ sourceFill base index plan) target sigma =
    Free.bind _ targetFill base (moveIndex index sigma)
      (transport methods routing childSubstitution square holes base index plan target sigma) := by
  refine Mettapedia.TypeTheory.IndexedPolynomial.Fix.eliminate
    ((PolynomialPlans.polynomial (inputMethods methods routing)).withHoles Holes)
    (fun base index plan => ∀ (target : Nat) (sigma : Sub Tower.Head index.2.1 target),
      transport methods routing childSubstitution square next base index
        (Free.bind _ sourceFill base index plan) target sigma =
      Free.bind _ targetFill base (moveIndex index sigma)
        (transport methods routing childSubstitution square holes base index plan target sigma))
    ?_ base index plan target sigma
  intro base index shape children inductionHypothesis target sigma
  cases shape with
  | inl hole => exact fillSquare base index target sigma hole
  | inr route =>
      change transport methods routing childSubstitution square next base index
        (Free.bind _ sourceFill base index (Free.node _ route children)) target sigma =
        Free.bind _ targetFill base (moveIndex index sigma)
          (transport methods routing childSubstitution square holes base index
            (Free.node _ route children) target sigma)
      change Free.node (PolynomialPlans.polynomial (inputMethods methods routing))
        (holes := TargetNext) (base := base) (index := moveIndex index sigma) route
        (fun premise => Eq.mp (congrArg
          (fun input => (PolynomialPlans.polynomial (inputMethods methods routing)).Free
            TargetNext base ⟨(methods index.1 route).query premise, input⟩)
          (square index route target sigma premise))
          (transport methods routing childSubstitution square next base _
            (Free.bind _ sourceFill base _ (children premise)) _
            (childSubstitution index route target sigma premise).2)) =
        Free.node (PolynomialPlans.polynomial (inputMethods methods routing))
          (holes := TargetNext) (base := base) (index := moveIndex index sigma) route
          (fun premise => Free.bind _ targetFill base _ (Eq.mp (congrArg
            (fun input => (PolynomialPlans.polynomial (inputMethods methods routing)).Free
              TargetHoles base ⟨(methods index.1 route).query premise, input⟩)
            (square index route target sigma premise))
            (transport methods routing childSubstitution square holes base _
              (children premise) _ (childSubstitution index route target sigma premise).2)))
      congr 1
      funext premise
      exact (congrArg (fun plan => Eq.mp (congrArg
        (fun input => (PolynomialPlans.polynomial (inputMethods methods routing)).Free
          TargetNext base ⟨(methods index.1 route).query premise, input⟩)
        (square index route target sigma premise)) plan)
        (inductionHypothesis premise _ (childSubstitution index route target sigma premise).2)).trans
        (bind_cast methods routing targetFill (square index route target sigma premise) _).symm

/-- Flattening retained subplans is a genuine filling instance: its local
replacement square is definitional, not an assumed whole-plan conclusion. -/
theorem transport_join {Holes Next : Unit → Index Base Const → Type}
    (holes : HoleAction Holes Next)
    {base : Unit} {index : Index Base Const}
    (plan : (PolynomialPlans.polynomial (inputMethods methods routing)).Free
      ((PolynomialPlans.polynomial (inputMethods methods routing)).Free Holes) base index)
    (target : Nat) (sigma : Sub Tower.Head index.2.1 target) :
    transport methods routing childSubstitution square holes base index
      (Free.join _ plan) target sigma =
    Free.join _ (transport methods routing childSubstitution square
      (fun base index target sigma inner =>
        transport methods routing childSubstitution square holes base index inner target sigma)
      base index plan target sigma) :=
  transport_fill methods routing childSubstitution square
    (fun base index target sigma inner =>
      transport methods routing childSubstitution square holes base index inner target sigma)
    holes (fun _ _ inner => inner) (fun _ _ inner => inner)
    (by intros; rfl) plan target sigma

variable {Values : HOLAdapter.Goal Base Const → Type}

/-- Source erasure followed by a leaf projection; input tags are not falsely
claimed to remain unchanged under substitution. -/
noncomputable def sourceTree {Holes : Unit → Index Base Const → Type}
    (values : ∀ base index, Holes base index → Values index.1)
    (base : Unit) (index : Index Base Const)
    (plan : (PolynomialPlans.polynomial (inputMethods methods routing)).Free Holes base index) :=
  Free.map (PolynomialPlans.polynomial methods)
    (fun base goal (tag : ErasedHole Holes base goal) => values base ⟨goal, tag.1⟩ tag.2)
    base index.1 (erase methods routing base index plan)

theorem sourceTree_cast {Holes : Unit → Index Base Const → Type}
    (values : ∀ base index, Holes base index → Values index.1)
    {base : Unit} {goal : HOLAdapter.Goal Base Const} {first second : Input goal}
    (equal : first = second)
    (plan : (PolynomialPlans.polynomial (inputMethods methods routing)).Free Holes base ⟨goal, first⟩) :
    sourceTree methods routing values base ⟨goal, second⟩
      (Eq.mp (congrArg (fun input =>
        (PolynomialPlans.polynomial (inputMethods methods routing)).Free Holes base ⟨goal, input⟩)
        equal) plan) = sourceTree methods routing values base ⟨goal, first⟩ plan := by
  cases equal
  rfl

theorem transport_sourceTree {Holes Next : Unit → Index Base Const → Type}
    (holes : HoleAction Holes Next)
    (sourceValues : ∀ base index, Holes base index → Values index.1)
    (targetValues : ∀ base index, Next base index → Values index.1)
    (leafSquare : ∀ base index target sigma hole,
      targetValues base (moveIndex index sigma) (holes base index target sigma hole) =
        sourceValues base index hole)
    {base : Unit} {index : Index Base Const}
    (plan : (PolynomialPlans.polynomial (inputMethods methods routing)).Free Holes base index)
    (target : Nat) (sigma : Sub Tower.Head index.2.1 target) :
    sourceTree methods routing targetValues base (moveIndex index sigma)
      (transport methods routing childSubstitution square holes base index plan target sigma) =
    sourceTree methods routing sourceValues base index plan := by
  refine Mettapedia.TypeTheory.IndexedPolynomial.Fix.eliminate
    ((PolynomialPlans.polynomial (inputMethods methods routing)).withHoles Holes)
    (fun base index plan => ∀ (target : Nat) (sigma : Sub Tower.Head index.2.1 target),
      sourceTree methods routing targetValues base (moveIndex index sigma)
        (transport methods routing childSubstitution square holes base index plan target sigma) =
      sourceTree methods routing sourceValues base index plan)
    ?_ base index plan target sigma
  intro base index shape children inductionHypothesis target sigma
  cases shape with
      | inl hole =>
          change Free.pure (PolynomialPlans.polynomial methods)
            (holes := fun _ => Values) (base := base) (index := index.1)
            (targetValues base (moveIndex _ sigma) (holes base _ target sigma hole)) =
              Free.pure (PolynomialPlans.polynomial methods)
                (holes := fun _ => Values) (base := base) (index := index.1)
                (sourceValues base _ hole)
          rw [leafSquare]
      | inr route =>
          change Free.node (PolynomialPlans.polynomial methods)
            (holes := fun _ => Values) (base := base) (index := index.1) route
            (fun premise => sourceTree methods routing targetValues base _
              (Eq.mp (congrArg (fun input =>
                (PolynomialPlans.polynomial (inputMethods methods routing)).Free Next base
                  ⟨(methods _ route).query premise, input⟩)
                (square _ route target sigma premise))
                (transport methods routing childSubstitution square holes base _
                  (children premise) _ (childSubstitution _ route target sigma premise).2))) =
            Free.node (PolynomialPlans.polynomial methods)
              (holes := fun _ => Values) (base := base) (index := index.1) route (fun premise =>
              sourceTree methods routing sourceValues base _ (children premise))
          congr 1
          funext premise
          exact (sourceTree_cast methods routing targetValues
            (square index route target sigma premise) _).trans
            (inductionHypothesis premise _ (childSubstitution _ route target sigma premise).2)

theorem reconstruct_sourceTree {Holes : Unit → Index Base Const → Type}
    (values : ∀ base index, Holes base index → HOLAdapter.Solution index.1)
    {base : Unit} {index : Index Base Const}
    (plan : (PolynomialPlans.polynomial (inputMethods methods routing)).Free Holes base index) :
    Free.fold (PolynomialPlans.polynomial methods) (fun _ _ proof => proof)
      (PolynomialPlans.reconstruction methods) base index.1
      (sourceTree methods routing values base index plan) =
    Free.fold (PolynomialPlans.polynomial (inputMethods methods routing)) values
      (PolynomialPlans.reconstruction (inputMethods methods routing)) base index plan := by
  unfold sourceTree Free.map
  rw [Free.fold_bind]
  exact erase_reconstruct methods routing values plan

variable (signature : LogicalSignature Base Const) (proofName : DeclName)
variable (operations : Operations signature proofName) (natural : operations.raw.Natural)

def receiptAction : HoleAction (fun _ => Receipt signature proofName operations)
    (fun _ => Receipt signature proofName operations) :=
  fun _ _ _ sigma receipt =>
    PolynomialHOLRetainedCompilation.transportRetained signature proofName operations natural
      sigma receipt

theorem receipt_source_tree
    {base : Unit} {index : Index Base Const}
    (plan : (PolynomialPlans.polynomial (inputMethods methods routing)).Free
      (fun _ => Receipt signature proofName operations) base index)
    (target : Nat) (sigma : Sub Tower.Head index.2.1 target) :
    sourceTree methods routing (fun _ _ receipt => receipt.1) base (moveIndex index sigma)
      (transport methods routing childSubstitution square
        (receiptAction signature proofName operations natural) base index plan target sigma) =
    sourceTree methods routing (fun _ _ receipt => receipt.1) base index plan :=
  transport_sourceTree methods routing childSubstitution square
    (receiptAction signature proofName operations natural)
    (fun _ _ receipt => receipt.1) (fun _ _ receipt => receipt.1)
    (by intros; rfl) plan target sigma

/-- Actual target assembly is compared with the existing transported receipt
using the original compiler's functional equation, not an assembly law field. -/
theorem assembly_substitution
    (assemble : LocalAssembly methods routing signature proofName operations)
    {base : Unit} {index : Index Base Const}
    (plan : (PolynomialPlans.polynomial (inputMethods methods routing)).Free
      (fun _ => Receipt signature proofName operations) base index)
    (target : Nat) (sigma : Sub Tower.Head index.2.1 target) :
    (assemblePlan methods routing signature proofName operations assemble
      (fun _ _ receipt => receipt) base (moveIndex index sigma)
      (transport methods routing childSubstitution square
        (receiptAction signature proofName operations natural) base index plan target sigma)).2.1 =
    subst sigma (assemblePlan methods routing signature proofName operations assemble
      (fun _ _ receipt => receipt) base index plan).2.1 := by
  have tree := receipt_source_tree methods routing childSubstitution square
    signature proofName operations natural plan target sigma
  have proofs := congrArg
    (Free.fold (PolynomialPlans.polynomial methods) (fun _ _ proof => proof)
      (PolynomialPlans.reconstruction methods) base index.1) tree
  have reconstructed := (reconstruct_sourceTree methods routing
    (Holes := fun _ => Receipt signature proofName operations)
    (fun _ _ receipt => receipt.1)
    (transport methods routing childSubstitution square
      (receiptAction signature proofName operations natural) base index plan target sigma)).symm.trans
    (proofs.trans (reconstruct_sourceTree methods routing
      (Holes := fun _ => Receipt signature proofName operations)
      (fun _ _ receipt => receipt.1) plan))
  let original := assemblePlan methods routing signature proofName operations assemble
    (fun _ _ receipt => receipt) base index plan
  let transported := assemblePlan methods routing signature proofName operations assemble
    (fun _ _ receipt => receipt) base (moveIndex index sigma)
    (transport methods routing childSubstitution square
      (receiptAction signature proofName operations natural) base index plan target sigma)
  let moved := PolynomialHOLRetainedCompilation.transportRetained
    signature proofName operations natural sigma original
  have sourceEqual : transported.1 = moved.1 :=
    (assemble_source methods routing signature proofName operations assemble
      (fun _ _ receipt => receipt) _).trans
      (reconstructed.trans (assemble_source methods routing signature proofName operations assemble
        (fun _ _ receipt => receipt) plan).symm)
  exact Option.some.inj (transported.2.2.symm.trans
    ((congrArg (fun source => compile signature proofName operations source
      (moveInput index.2 sigma).2.1 (moveInput index.2 sigma).2.2) sourceEqual).trans moved.2.2))

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PolynomialHOLRetainedInputTransport
