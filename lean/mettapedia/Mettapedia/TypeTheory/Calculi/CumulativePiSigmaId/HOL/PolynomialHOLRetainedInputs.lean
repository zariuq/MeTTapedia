import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.PolynomialHOLRetainedCompilation

/-!
# Retained proof plans at their actual compiler inputs

Changing scope changes an index, not the polynomial base. Each derived method
keeps its original source reconstruction and premise positions. Its child input
action supplies the actual compiler substitutions; no flattening of object and
proof binders is selected. Trees and filling are the existing polynomial Free.
-/

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PolynomialHOLRetainedInputs

open Mettapedia.Logic Presentation FormationSensitiveHOLInterface
open HOLNativeGenericProofCompiler ProofSearch ProofObligations
open Mettapedia.TypeTheory Mettapedia.TypeTheory.IndexedPolynomial

variable {Base : Type} {Const : HOL.Ty Base → Type}

/-- The existing compiler's two input maps, with their actual common scope. -/
abbrev Input (goal : HOLAdapter.Goal Base Const) :=
  Σ scope : Nat, Sub Tower.Head goal.context.length scope ×
    (Fin goal.hypotheses.length → Tower.Tm scope)

abbrev Index (Base : Type) (Const : HOL.Ty Base → Type) :=
  Σ goal : HOLAdapter.Goal Base Const, Input goal

variable {Routes : HOLAdapter.Goal Base Const → Type}
variable (methods : ∀ goal, Routes goal → Refinement HOLAdapter.Solution goal)

/-- Per-constructor compiler input routing is separate from source methods. -/
abbrev Routing := ∀ goal (route : Routes goal), Input goal →
  ∀ premise, Input ((methods goal route).query premise)

variable (routing : Routing methods)

/-- Derive only the input indices; reuse source premises and reconstruction. -/
def inputMethods (index : Index Base Const) (route : Routes index.1) :
    Refinement (fun index : Index Base Const => HOLAdapter.Solution index.1) index where
  Premise := (methods index.1 route).Premise
  query premise := ⟨(methods index.1 route).query premise,
    routing index.1 route index.2 premise⟩
  rebuild := (methods index.1 route).rebuild

variable (signature : LogicalSignature Base Const) (proofName : DeclName)
variable (operations : Operations signature proofName)

abbrev Receipt (index : Index Base Const) :=
  PolynomialHOLRetainedCompilation.Retained signature proofName operations
    index.2.2.1 index.2.2.2

/-- Only a local compiler equation is required. Native child outputs are
already retained at the exact inputs prescribed for their occurrences. -/
abbrev LocalAssembly := ∀ (index : Index Base Const) (route : Routes index.1)
    (children : ∀ (premise : (methods index.1 route).Premise), Receipt signature proofName operations
      ((inputMethods methods routing index route).query premise)),
  {native : Tower.Tm index.2.1 // compile signature proofName operations
    ((methods index.1 route).rebuild (fun premise => (children premise).1))
    index.2.2.1 index.2.2.2 = some native}

variable (assemble : LocalAssembly methods routing signature proofName operations)

def assembledAlgebra : (PolynomialPlans.polynomial (inputMethods methods routing)).Algebra
    (fun _ index => Receipt signature proofName operations index) where
  act := fun _ index inputLayer =>
    ⟨(methods index.1 inputLayer.1).rebuild (fun premise => (inputLayer.2 premise).1),
      assemble index inputLayer.1 inputLayer.2⟩

noncomputable def assemblePlan {Holes : Unit → Index Base Const → Type}
    (leaves : ∀ base index, Holes base index → Receipt signature proofName operations index) :=
  Free.fold (PolynomialPlans.polynomial (inputMethods methods routing)) leaves
    (assembledAlgebra methods routing signature proofName operations assemble)

theorem assemble_source {Holes : Unit → Index Base Const → Type}
    (leaves : ∀ base index, Holes base index → Receipt signature proofName operations index)
    {base : Unit} {index : Index Base Const}
    (plan : (PolynomialPlans.polynomial (inputMethods methods routing)).Free Holes base index) :
    (assemblePlan methods routing signature proofName operations assemble leaves base index plan).1 =
      Free.fold (PolynomialPlans.polynomial (inputMethods methods routing))
        (fun base index hole => (leaves base index hole).1)
        (PolynomialPlans.reconstruction (inputMethods methods routing)) base index plan :=
  Free.fold_unique _ _ _ (fun base index plan =>
    (assemblePlan methods routing signature proofName operations assemble leaves base index plan).1)
    (by intros; rfl) (by intros; rfl) base index plan

theorem assemble_fill {Holes Next : Unit → Index Base Const → Type}
    (replacement : ∀ base index, Holes base index →
      (PolynomialPlans.polynomial (inputMethods methods routing)).Free Next base index)
    (leaves : ∀ base index, Next base index → Receipt signature proofName operations index)
    {base : Unit} {index : Index Base Const}
    (plan : (PolynomialPlans.polynomial (inputMethods methods routing)).Free Holes base index) :
    assemblePlan methods routing signature proofName operations assemble leaves base index
      (Free.bind _ replacement base index plan) =
    assemblePlan methods routing signature proofName operations assemble
      (fun base index hole => assemblePlan methods routing signature proofName operations assemble
        leaves base index (replacement base index hole)) base index plan :=
  Free.fold_bind _ _ _ _ plan

/-- The original finite optional reconstruction now consumes exact-input
receipts. A missing child remains missing; no failure classification is added. -/
def retainedMethod (index : Index Base Const) (route : Routes index.1) :
    Refinement (Receipt signature proofName operations) index where
  Premise := (methods index.1 route).Premise
  query := (inputMethods methods routing index route).query
  rebuild children := ⟨(methods index.1 route).rebuild (fun premise => (children premise).1),
    assemble index route children⟩

def partialAlgebra : (PolynomialPlans.polynomial (inputMethods methods routing)).Algebra
    (fun _ index => Option (Receipt signature proofName operations index)) :=
  PolynomialPlans.partialReconstruction
    (retainedMethod methods routing signature proofName operations assemble)

theorem missing_child_no_receipt {index : Index Base Const} (route : Routes index.1)
    (children : ∀ premise, Option (Receipt signature proofName operations
      ((inputMethods methods routing index route).query premise)))
    (missing : ∃ premise, children premise = none) :
    (partialAlgebra methods routing signature proofName operations assemble).act
      () index ⟨route, children⟩ = none :=
  (Refinement.tryRebuild_eq_none_iff _ _).2 missing

theorem partial_fill {Holes Next : Unit → Index Base Const → Type}
    (replacement : ∀ base index, Holes base index →
      (PolynomialPlans.polynomial (inputMethods methods routing)).Free Next base index)
    (leaves : ∀ base index, Next base index → Option (Receipt signature proofName operations index))
    {base : Unit} {index : Index Base Const}
    (plan : (PolynomialPlans.polynomial (inputMethods methods routing)).Free Holes base index) :
    Free.fold _ leaves (partialAlgebra methods routing signature proofName operations assemble)
      base index (Free.bind _ replacement base index plan) =
    Free.fold _ (fun base index hole => Free.fold _ leaves
      (partialAlgebra methods routing signature proofName operations assemble)
      base index (replacement base index hole))
      (partialAlgebra methods routing signature proofName operations assemble) base index plan :=
  Free.fold_bind _ _ _ _ plan

/-- Forgetting to source goals retains the actual input attached to each hole. -/
abbrev ErasedHole (Holes : Unit → Index Base Const → Type)
    (base : Unit) (goal : HOLAdapter.Goal Base Const) :=
  Σ input : Input goal, Holes base ⟨goal, input⟩

def erasureAlgebra (Holes : Unit → Index Base Const → Type) :
    (PolynomialPlans.polynomial (inputMethods methods routing)).Algebra
      (fun base index => (PolynomialPlans.polynomial methods).Free (ErasedHole Holes) base index.1)
    where
  act := fun _ _ inputLayer => Free.node _ inputLayer.1 inputLayer.2

noncomputable def erase {Holes : Unit → Index Base Const → Type} :=
  Free.fold (PolynomialPlans.polynomial (inputMethods methods routing))
    (fun base index hole => Free.pure (PolynomialPlans.polynomial methods)
      (holes := ErasedHole Holes) (base := base) (index := index.1) ⟨index.2, hole⟩)
    (erasureAlgebra methods routing Holes)

theorem erase_reconstruct {Holes : Unit → Index Base Const → Type}
    (leaves : ∀ base index, Holes base index → HOLAdapter.Solution index.1)
    {base : Unit} {index : Index Base Const}
    (plan : (PolynomialPlans.polynomial (inputMethods methods routing)).Free Holes base index) :
    Free.fold (PolynomialPlans.polynomial methods)
      (fun base goal (tag : ErasedHole Holes base goal) => leaves base ⟨goal, tag.1⟩ tag.2)
      (PolynomialPlans.reconstruction methods) base index.1 (erase methods routing base index plan) =
    Free.fold (PolynomialPlans.polynomial (inputMethods methods routing)) leaves
      (PolynomialPlans.reconstruction (inputMethods methods routing)) base index plan :=
  Free.fold_unique _ _ _ (fun base index plan =>
    Free.fold (PolynomialPlans.polynomial methods)
      (fun base goal (tag : ErasedHole Holes base goal) => leaves base ⟨goal, tag.1⟩ tag.2)
      (PolynomialPlans.reconstruction methods) base index.1 (erase methods routing base index plan))
    (by intros; rfl) (by intros; rfl) base index plan

theorem assembled_erasure {Holes : Unit → Index Base Const → Type}
    (leaves : ∀ base index, Holes base index → Receipt signature proofName operations index)
    {base : Unit} {index : Index Base Const}
    (plan : (PolynomialPlans.polynomial (inputMethods methods routing)).Free Holes base index) :
    (assemblePlan methods routing signature proofName operations assemble leaves base index plan).1 =
    Free.fold (PolynomialPlans.polynomial methods)
      (fun base goal (tag : ErasedHole Holes base goal) => (leaves base ⟨goal, tag.1⟩ tag.2).1)
      (PolynomialPlans.reconstruction methods) base index.1 (erase methods routing base index plan) :=
  (assemble_source methods routing signature proofName operations assemble leaves plan).trans
    (erase_reconstruct methods routing (fun base index hole => (leaves base index hole).1) plan).symm

theorem erase_fill {Holes Next : Unit → Index Base Const → Type}
    (replacement : ∀ base index, Holes base index →
      (PolynomialPlans.polynomial (inputMethods methods routing)).Free Next base index)
    {base : Unit} {index : Index Base Const}
    (plan : (PolynomialPlans.polynomial (inputMethods methods routing)).Free Holes base index) :
    erase methods routing base index (Free.bind _ replacement base index plan) =
    Free.bind (PolynomialPlans.polynomial methods)
      (fun base goal (tag : ErasedHole Holes base goal) =>
        erase methods routing base ⟨goal, tag.1⟩ (replacement base ⟨goal, tag.1⟩ tag.2))
      base index.1 (erase methods routing base index plan) := by
  have left := Free.fold_bind (PolynomialPlans.polynomial (inputMethods methods routing))
    replacement (fun base index hole => Free.pure (PolynomialPlans.polynomial methods)
      (holes := ErasedHole Next) (base := base) (index := index.1) ⟨index.2, hole⟩)
    (erasureAlgebra methods routing Next) plan
  have right := Free.fold_unique (PolynomialPlans.polynomial (inputMethods methods routing))
    (fun base index hole => erase methods routing base index (replacement base index hole))
    (erasureAlgebra methods routing Next)
    (fun base index plan => Free.bind (PolynomialPlans.polynomial methods)
      (fun base goal (tag : ErasedHole Holes base goal) =>
        erase methods routing base ⟨goal, tag.1⟩ (replacement base ⟨goal, tag.1⟩ tag.2))
      base index.1 (erase methods routing base index plan))
    (by intros; rfl) (by intros; rfl) base index plan
  exact left.trans right.symm

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PolynomialHOLRetainedInputs
