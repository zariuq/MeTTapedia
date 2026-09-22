import Mettapedia.Logic.ProofSearch.PlanExpansion
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLProofObligations
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeUniformListStateSubstitution

/-!
# Assembling retained child compilations over the existing proof-plan tree

The carrier retains each actual source proof, native output, and successful
equation of the existing compiler. Local method assembly consumes those native
outputs; it does not invoke the recursive compiler on children. The free fold
uses the existing polynomial and reconstruction. Its local obligations concern
one method only, and concrete implication/universal elimination discharges them
by the actual compiler constructor equations.
-/

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PolynomialHOLRetainedCompilation

open Mettapedia.Logic Presentation FormationSensitiveHOLInterface
open HOLNativeGenericProofCompiler ProofSearch ProofObligations
open Mettapedia.TypeTheory Mettapedia.TypeTheory.IndexedPolynomial

variable {Base : Type} {Const : HOL.Ty Base → Type}
variable (signature : LogicalSignature Base Const) (proofName : DeclName)
variable (operations : Operations signature proofName)

/-- Data from a completed compilation, not a new checking judgment. -/
abbrev Retained {goal : HOLAdapter.Goal Base Const} {n : Nat}
    (objects : Sub Tower.Head goal.context.length n)
    (hypotheses : Fin goal.hypotheses.length → Tower.Tm n) :=
  Σ source : HOLAdapter.Solution goal,
    {native : Tower.Tm n // compile signature proofName operations source objects hypotheses =
      some native}

/-- Move the actual retained output and its original compilation equation.
The source proof is unchanged, and the computational output is substitution,
not a recursive compiler invocation. -/
def transportRetained (natural : operations.raw.Natural)
    {goal : HOLAdapter.Goal Base Const} {sourceScope targetScope : Nat}
    {objectInputs : Sub Tower.Head goal.context.length sourceScope}
    {hypothesisInputs : Fin goal.hypotheses.length → Tower.Tm sourceScope}
    (sigma : Sub Tower.Head sourceScope targetScope)
    (retained : Retained signature proofName operations objectInputs hypothesisInputs) :
    Retained signature proofName operations
      (fun index => subst sigma (objectInputs index))
      (fun index => subst sigma (hypothesisInputs index)) :=
  ⟨retained.1, subst sigma retained.2.1, by
    exact (compile_substitute signature proofName operations natural retained.1
      objectInputs hypothesisInputs sigma).trans
        (congrArg (Option.map (subst sigma)) retained.2.2)⟩

variable {Routes : HOLAdapter.Goal Base Const → Type}
variable (methods : ∀ goal, Routes goal → Refinement HOLAdapter.Solution goal)
variable {n : Nat}
variable (objects : ∀ goal : HOLAdapter.Goal Base Const, Sub Tower.Head goal.context.length n)
variable (hypotheses : ∀ goal : HOLAdapter.Goal Base Const,
  Fin goal.hypotheses.length → Tower.Tm n)

/-- One constructor's native assembly, justified against that constructor's
source reconstruction. It receives the actual retained child outputs. -/
abbrev LocalAssembly := ∀ goal route
    (children : ∀ premise, Retained signature proofName operations
      (objects ((methods goal route).query premise))
      (hypotheses ((methods goal route).query premise))),
  {native : Tower.Tm n // compile signature proofName operations
    ((methods goal route).rebuild (fun premise => (children premise).1))
    (objects goal) (hypotheses goal) = some native}

def assembledAlgebra
    (assemble : LocalAssembly signature proofName operations methods objects hypotheses) :
    (PolynomialPlans.polynomial methods).Algebra
      (fun _ goal => Retained signature proofName operations (objects goal) (hypotheses goal)) where
  act := fun _ goal inputLayer =>
    ⟨(methods goal inputLayer.1).rebuild (fun premise => (inputLayer.2 premise).1),
      assemble goal inputLayer.1 inputLayer.2⟩

noncomputable def assemblePlan
    (assemble : LocalAssembly signature proofName operations methods objects hypotheses)
    {Holes : Unit → HOLAdapter.Goal Base Const → Type}
    (leaves : ∀ base goal, Holes base goal →
      Retained signature proofName operations (objects goal) (hypotheses goal)) :=
  Free.fold (PolynomialPlans.polynomial methods) leaves
    (assembledAlgebra signature proofName operations methods objects hypotheses assemble)

theorem assembled_source
    (assemble : LocalAssembly signature proofName operations methods objects hypotheses)
    {Holes : Unit → HOLAdapter.Goal Base Const → Type}
    (leaves : ∀ base goal, Holes base goal →
      Retained signature proofName operations (objects goal) (hypotheses goal))
    {base : Unit} {goal : HOLAdapter.Goal Base Const}
    (plan : (PolynomialPlans.polynomial methods).Free Holes base goal) :
    (assemblePlan signature proofName operations methods objects hypotheses assemble leaves
      base goal plan).1 =
    Free.fold (PolynomialPlans.polynomial methods) (fun base goal hole => (leaves base goal hole).1)
      (PolynomialPlans.reconstruction methods) base goal plan :=
  Free.fold_unique _ _ _ (fun base goal plan =>
    (assemblePlan signature proofName operations methods objects hypotheses assemble leaves
      base goal plan).1) (by intros; rfl) (by intros; rfl) base goal plan

theorem assemble_fill
    (assemble : LocalAssembly signature proofName operations methods objects hypotheses)
    {Holes Next : Unit → HOLAdapter.Goal Base Const → Type}
    (replacement : ∀ base goal, Holes base goal →
      (PolynomialPlans.polynomial methods).Free Next base goal)
    (leaves : ∀ base goal, Next base goal →
      Retained signature proofName operations (objects goal) (hypotheses goal))
    {base : Unit} {goal : HOLAdapter.Goal Base Const}
    (plan : (PolynomialPlans.polynomial methods).Free Holes base goal) :
    assemblePlan signature proofName operations methods objects hypotheses assemble leaves
      base goal (Free.bind _ replacement base goal plan) =
    assemblePlan signature proofName operations methods objects hypotheses assemble
      (fun base goal hole => assemblePlan signature proofName operations methods objects hypotheses
        assemble leaves base goal (replacement base goal hole)) base goal plan :=
  Free.fold_bind _ _ _ _ plan

/-- The existing compiler is functional: distinct assembly histories cannot
change its output when they retain the same source proof and inputs. -/
theorem same_source_same_native {goal : HOLAdapter.Goal Base Const}
    (first second : Retained signature proofName operations (objects goal) (hypotheses goal))
    (same : first.1 = second.1) : first.2.1 = second.2.1 := by
  exact Option.some.inj (first.2.2.symm.trans
    ((congrArg (fun source => compile signature proofName operations source
      (objects goal) (hypotheses goal)) same).trans second.2.2))

/-- Assembling transported child receipts agrees with transporting the
original assembled output. Only compiler-operation naturality is required;
no naturality field for the method assembler or whole-tree semantic conclusion
is assumed. Source reconstruction remains exactly the same proof. -/
theorem assembly_naturality (natural : operations.raw.Natural)
    (assemble : LocalAssembly signature proofName operations methods objects hypotheses)
    {targetScope : Nat} (sigma : Sub Tower.Head n targetScope)
    (targetAssembly : LocalAssembly signature proofName operations methods
      (fun goal index => subst sigma (objects goal index))
      (fun goal index => subst sigma (hypotheses goal index)))
    {Holes : Unit → HOLAdapter.Goal Base Const → Type}
    (leaves : ∀ base goal, Holes base goal →
      Retained signature proofName operations (objects goal) (hypotheses goal))
    {base : Unit} {goal : HOLAdapter.Goal Base Const}
    (plan : (PolynomialPlans.polynomial methods).Free Holes base goal) :
    (assemblePlan signature proofName operations methods
      (fun goal index => subst sigma (objects goal index))
      (fun goal index => subst sigma (hypotheses goal index)) targetAssembly
      (fun base goal hole => transportRetained signature proofName operations natural sigma
        (leaves base goal hole)) base goal plan).2.1 =
    subst sigma (assemblePlan signature proofName operations methods objects hypotheses
      assemble leaves base goal plan).2.1 := by
  apply same_source_same_native signature proofName operations
    (fun goal index => subst sigma (objects goal index))
    (fun goal index => subst sigma (hypotheses goal index)) _
    (transportRetained signature proofName operations natural sigma
      (assemblePlan signature proofName operations methods objects hypotheses
        assemble leaves base goal plan))
  exact (assembled_source signature proofName operations methods
    (fun goal index => subst sigma (objects goal index))
    (fun goal index => subst sigma (hypotheses goal index)) targetAssembly
    (fun base goal hole => transportRetained signature proofName operations natural sigma
      (leaves base goal hole)) plan).trans
        (assembled_source signature proofName operations methods objects hypotheses
          assemble leaves plan).symm

/-- Composite assembly retains both layers' child artifacts. -/
def compositeAssembly
    (assemble : LocalAssembly signature proofName operations methods objects hypotheses) :
    LocalAssembly signature proofName operations (PolynomialPlans.compositeMethods methods)
      objects hypotheses :=
  fun goal route children => assemble goal route.1 (fun premise =>
    ⟨(methods _ (route.2 premise)).rebuild (fun leaf => (children ⟨premise, leaf⟩).1),
      assemble _ (route.2 premise) (fun leaf => children ⟨premise, leaf⟩)⟩)

/-- Method expansion preserves the exact native output, not just its type.
Source reconstruction is supplied by the existing expansion theorem and native
agreement by the original compiler's functional equation. -/
theorem assembled_expansion
    (assemble : LocalAssembly signature proofName operations methods objects hypotheses)
    {Holes : Unit → HOLAdapter.Goal Base Const → Type}
    (leaves : ∀ base goal, Holes base goal →
      Retained signature proofName operations (objects goal) (hypotheses goal))
    {base : Unit} {goal : HOLAdapter.Goal Base Const}
    (plan : (PolynomialPlans.polynomial (PolynomialPlans.compositeMethods methods)).Free
      Holes base goal) :
    (assemblePlan signature proofName operations methods objects hypotheses assemble leaves
      base goal ((PolynomialPlans.expansion methods).run base goal plan)).2.1 =
    (assemblePlan signature proofName operations (PolynomialPlans.compositeMethods methods)
      objects hypotheses
      (compositeAssembly signature proofName operations methods objects hypotheses assemble)
      leaves base goal plan).2.1 := by
  apply same_source_same_native
  exact (assembled_source signature proofName operations methods objects hypotheses assemble leaves
    ((PolynomialPlans.expansion methods).run base goal plan)).trans
      ((PolynomialPlans.reconstruct_expansion methods (fun base goal h => (leaves base goal h).1)
        plan).trans (assembled_source signature proofName operations
          (PolynomialPlans.compositeMethods methods) objects hypotheses
          (compositeAssembly signature proofName operations methods objects hypotheses assemble)
          leaves plan).symm)

/-- Use the existing finite optional reconstruction on compilation receipts. -/
def retainedMethod
    (assemble : LocalAssembly signature proofName operations methods objects hypotheses)
    (goal : HOLAdapter.Goal Base Const) (route : Routes goal) :
    Refinement (fun goal => Retained signature proofName operations
      (objects goal) (hypotheses goal)) goal where
  Premise := (methods goal route).Premise
  query := (methods goal route).query
  rebuild children := ⟨(methods goal route).rebuild (fun premise => (children premise).1),
    assemble goal route children⟩

def partialAlgebra
    (assemble : LocalAssembly signature proofName operations methods objects hypotheses) :
    (PolynomialPlans.polynomial methods).Algebra
      (fun _ goal => Option (Retained signature proofName operations
        (objects goal) (hypotheses goal))) :=
  PolynomialPlans.partialReconstruction
    (retainedMethod signature proofName operations methods objects hypotheses assemble)

theorem missing_child_no_assembly
    (assemble : LocalAssembly signature proofName operations methods objects hypotheses)
    {goal : HOLAdapter.Goal Base Const} (route : Routes goal)
    (children : ∀ premise, Option (Retained signature proofName operations
      (objects ((methods goal route).query premise))
      (hypotheses ((methods goal route).query premise))))
    (missing : ∃ premise, children premise = none) :
    (partialAlgebra signature proofName operations methods objects hypotheses assemble).act
      () goal ⟨route, children⟩ = none :=
  (Refinement.tryRebuild_eq_none_iff _ _).2 missing

theorem partial_assembly_fill
    (assemble : LocalAssembly signature proofName operations methods objects hypotheses)
    {Holes Next : Unit → HOLAdapter.Goal Base Const → Type}
    (replacement : ∀ base goal, Holes base goal →
      (PolynomialPlans.polynomial methods).Free Next base goal)
    (leaves : ∀ base goal, Next base goal → Option
      (Retained signature proofName operations (objects goal) (hypotheses goal)))
    {base : Unit} {goal : HOLAdapter.Goal Base Const}
    (plan : (PolynomialPlans.polynomial methods).Free Holes base goal) :
    Free.fold _ leaves
      (partialAlgebra signature proofName operations methods objects hypotheses assemble)
      base goal (Free.bind _ replacement base goal plan) =
    Free.fold _ (fun base goal h => Free.fold _ leaves
      (partialAlgebra signature proofName operations methods objects hypotheses assemble)
      base goal (replacement base goal h))
      (partialAlgebra signature proofName operations methods objects hypotheses assemble)
      base goal plan := Free.fold_bind _ _ _ _ plan

/-- Implication introduction consumes a body retained under the exact new
proof input and weakened old inputs used by the existing compiler. The output
is one abstraction around that native body, not a recursive compilation. -/
def implicationAbstraction {gamma : HOL.Ctx Base} {delta : List (HOL.Formula Const gamma)}
    {antecedent conclusion : HOL.Formula Const gamma}
    {code : Tower.Tm gamma.length}
    (represented : represent signature antecedent = some code) {scope : Nat}
    {objectInputs : Sub Tower.Head gamma.length scope}
    {hypothesisInputs : Fin delta.length → Tower.Tm scope}
    (body : Retained signature proofName operations
      (goal := ⟨gamma, antecedent :: delta, conclusion⟩)
      (fun index => rename wk (objectInputs index))
      (Fin.cases (.var 0) (fun index => rename wk (hypothesisInputs index)))) :
    Retained signature proofName operations
      (goal := ⟨gamma, delta, .imp antecedent conclusion⟩) objectInputs hypothesisInputs :=
  ⟨.impI body.1, .lam body.2.1, by
    simp only [compile, represented, body.2.2]
    rfl⟩

/-- Universal introduction consumes a body retained under the actual lifted
object substitution. Old proofs weaken; the new object is not a new proof. -/
def universalAbstraction {gamma : HOL.Ctx Base} {delta : List (HOL.Formula Const gamma)}
    {type : HOL.Ty Base} {proposition : HOL.Formula Const (type :: gamma)} {scope : Nat}
    {objectInputs : Sub Tower.Head gamma.length scope}
    {hypothesisInputs : Fin delta.length → Tower.Tm scope}
    (body : Retained signature proofName operations
      (goal := ⟨type :: gamma, HOL.weakenHyps delta, proposition⟩)
      (liftSub objectInputs)
      (fun index => rename wk (hypothesisInputs (index.cast (by simp [HOL.weakenHyps]))))) :
    Retained signature proofName operations
      (goal := ⟨gamma, delta, .all proposition⟩) objectInputs hypothesisInputs :=
  ⟨.allI body.1, .lam body.2.1, by
    simp only [compile, body.2.2]
    rfl⟩

/-- Implication elimination adds one application around the two retained
native children. No recursive compiler call is used to choose the output. -/
def implicationApplication {gamma : HOL.Ctx Base} {delta : List (HOL.Formula Const gamma)}
    {antecedent conclusion : HOL.Formula Const gamma} {scope : Nat}
    {objectInputs : Sub Tower.Head gamma.length scope}
    {hypothesisInputs : Fin delta.length → Tower.Tm scope}
    (major : Retained signature proofName operations
      (goal := ⟨gamma, delta, .imp antecedent conclusion⟩) objectInputs hypothesisInputs)
    (minor : Retained signature proofName operations
      (goal := ⟨gamma, delta, antecedent⟩) objectInputs hypothesisInputs) :
    Retained signature proofName operations (goal := ⟨gamma, delta, conclusion⟩)
      objectInputs hypothesisInputs :=
  ⟨.impE major.1 minor.1, .app major.2.1 minor.2.1, by
    simp only [compile, major.2.2, minor.2.2]
    rfl⟩

/-- Universal elimination retains the major compilation and an actual
successful representation of its object argument. -/
def universalApplication {gamma : HOL.Ctx Base} {delta : List (HOL.Formula Const gamma)}
    {type : HOL.Ty Base} {body : HOL.Formula Const (type :: gamma)}
    (argument : HOL.Term Const gamma type) {code : Tower.Tm gamma.length}
    (represented : represent signature argument = some code) {scope : Nat}
    {objectInputs : Sub Tower.Head gamma.length scope}
    {hypothesisInputs : Fin delta.length → Tower.Tm scope}
    (major : Retained signature proofName operations
      (goal := ⟨gamma, delta, .all body⟩) objectInputs hypothesisInputs) :
    Retained signature proofName operations
      (goal := ⟨gamma, delta, HOL.instantiate argument body⟩) objectInputs hypothesisInputs :=
  ⟨.allE argument major.1, .app major.2.1 (subst objectInputs code), by
    simp only [compile, represented, major.2.2]
    rfl⟩

section UniformList

open HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding

universe u

/-- A filled method plan's retained output can be instantiated without
recompiling its leaves or selecting a new proof. The object and hypothesis
meanings are exactly the existing State-based semantic qualification. -/
theorem assembled_substitution {a : ZFSet.{u}}
    {routes : HOLAdapter.Goal BaseSort Symbol → Type}
    (selected : ∀ goal, routes goal → Refinement HOLAdapter.Solution goal)
    {sourceScope targetScope : Nat}
    (objectInputs : ∀ goal : HOLAdapter.Goal BaseSort Symbol,
      Sub Tower.Head goal.context.length sourceScope)
    (hypothesisInputs : ∀ goal : HOLAdapter.Goal BaseSort Symbol,
      Fin goal.hypotheses.length → Tower.Tm sourceScope)
    (assemble : LocalAssembly FormationSensitiveHOLLeibnizInterface.signature
      UniformList.proofName UniformList.operations selected objectInputs hypothesisInputs)
    {Holes : Unit → HOLAdapter.Goal BaseSort Symbol → Type}
    (leaves : ∀ base goal, Holes base goal → Retained
      FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
      UniformList.operations (objectInputs goal) (hypothesisInputs goal))
    {base : Unit} {goal : HOLAdapter.Goal BaseSort Symbol}
    (plan : (PolynomialPlans.polynomial selected).Free Holes base goal)
    (sigma : Sub Tower.Head sourceScope targetScope)
    (state : UniformListSemantics.State a (fun index => subst sigma (objectInputs goal index)))
    (hypothesisMeanings : ∀ index, UniformListSemantics.Denotes a state
      (subst sigma (hypothesisInputs goal index)) (goal.hypotheses.get index)) :
    UniformListSemantics.Denotes a state
      (subst sigma (assemblePlan FormationSensitiveHOLLeibnizInterface.signature
        UniformList.proofName UniformList.operations selected objectInputs hypothesisInputs
        assemble leaves base goal plan).2.1) goal.conclusion := by
  let retained := assemblePlan FormationSensitiveHOLLeibnizInterface.signature
    UniformList.proofName UniformList.operations selected objectInputs hypothesisInputs
    assemble leaves base goal plan
  exact UniformListStateSubstitution.retained_substitution retained.1 retained.2.2 sigma
    state hypothesisMeanings

end UniformList

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PolynomialHOLRetainedCompilation
