import Mettapedia.Languages.Lean.Declarations.CEKBlockCorrespondence

/-!
# Source Krivine thunks and the admitted thunk/list block

The tagged description is read from Lean's actual nested declaration. The
two source fibres retain terms and complete thunk environments. Their
constructor-layer bijection and source induction instantiate the shared
indexed-polynomial representation theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Lean.Declarations.KrivineBlockCorrespondence

open Mettapedia.Machines
open Mettapedia.TypeTheory
open IndexedPolynomial IndexedPolynomial.Description
open Mettapedia.GSLT.LanguageDef

abbrev model := CEKBlockCorrespondence.model
abbrev Index := Nat × List Unit

def admitted : IndexedInductive.Admitted (BlockProfile.interface model) [] :=
  ((BlockProfile.admit model BlockControls.krivine).toOption).get (by decide)

def Source (index : Index) : Type :=
  match index.2 with
  | [] => match index.1 with
      | 0 => Krivine.NThunk
      | 1 => List Krivine.NThunk
      | _ => PEmpty
  | _ :: _ => PEmpty

abbrev Args (index : Index) := InventoryArguments admitted.constructors PUnit.unit Source index

def assemble (index : Index) (arguments : Args index) : Source index := by
  rcases arguments with ⟨occurrence, arguments⟩
  change Fin 3 at occurrence
  refine Fin.cases ?_ (fun rest => ?_) occurrence arguments
  · intro arguments
    change (Σ term : Tm, List Krivine.NThunk × ULift (PLift ((0, ([] : List Unit)) = index))) at arguments
    rcases arguments with ⟨term, environment, ⟨⟨same⟩⟩⟩
    subst index
    exact .mk term environment
  · refine Fin.cases ?_ (fun rest => ?_) rest
    · intro arguments
      change ULift (PLift ((1, ([] : List Unit)) = index)) at arguments
      rcases arguments with ⟨⟨same⟩⟩
      subst index
      exact []
    · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) rest
      intro arguments
      change Krivine.NThunk × List Krivine.NThunk × ULift (PLift ((1, ([] : List Unit)) = index)) at arguments
      rcases arguments with ⟨head, tail, ⟨⟨same⟩⟩⟩
      subst index
      exact head :: tail

def disassemble : (index : Index) → Source index → Args index
  | (0, []), .mk term environment => by
      refine ⟨⟨0, by decide⟩, ?_⟩
      change Σ term : Tm, List Krivine.NThunk × ULift (PLift ((0, ([] : List Unit)) = (0, [])))
      exact ⟨term, environment, ⟨⟨rfl⟩⟩⟩
  | (1, []), [] => by
      refine ⟨⟨1, by decide⟩, ?_⟩
      change ULift (PLift ((1, ([] : List Unit)) = (1, [])))
      exact ⟨⟨rfl⟩⟩
  | (1, []), head :: tail => by
      refine ⟨⟨2, by decide⟩, ?_⟩
      change Krivine.NThunk × List Krivine.NThunk × ULift (PLift ((1, ([] : List Unit)) = (1, [])))
      exact ⟨head, tail, ⟨⟨rfl⟩⟩⟩
  | (n + 2, []), impossible => PEmpty.elim impossible
  | (_, _ :: _), impossible => PEmpty.elim impossible

theorem assemble_disassemble (index : Index) (source : Source index) :
    assemble index (disassemble index source) = source := by
  rcases index with ⟨tag, arguments⟩
  cases arguments with
  | cons _ _ => exact source.elim
  | nil =>
      cases tag with
      | zero => cases source; rfl
      | succ tag =>
          cases tag with
          | zero => cases source <;> rfl
          | succ _ => exact source.elim

theorem disassemble_assemble (index : Index) (arguments : Args index) :
    disassemble index (assemble index arguments) = arguments := by
  rcases arguments with ⟨occurrence, arguments⟩
  change Fin 3 at occurrence
  fin_cases occurrence
  · change (Σ term : Tm, List Krivine.NThunk × ULift (PLift ((0, ([] : List Unit)) = index))) at arguments
    rcases arguments with ⟨term, environment, ⟨⟨same⟩⟩⟩
    subst index
    rfl
  · change ULift (PLift ((1, ([] : List Unit)) = index)) at arguments
    rcases arguments with ⟨⟨same⟩⟩
    subst index
    rfl
  · change Krivine.NThunk × List Krivine.NThunk × ULift (PLift ((1, ([] : List Unit)) = index)) at arguments
    rcases arguments with ⟨head, tail, ⟨⟨same⟩⟩⟩
    subst index
    rfl

def layerEquiv (index : Index) : Args index ≃ Source index where
  toFun := assemble index
  invFun := disassemble index
  left_inv := disassemble_assemble index
  right_inv := assemble_disassemble index

def algebra : Algebra admitted.polynomial (fun _ => Source) :=
  admitted.algebra (fun _ index arguments => assemble index arguments)

theorem algebra_injective (environment : Env (BlockProfile.interface model).Value []) (index : Index) :
    Function.Injective (algebra.act environment index) := by
  cases environment
  exact (layerEquiv index).injective.comp
    (inventoryArgumentsEquiv admitted.constructors PUnit.unit Source index).symm.injective

abbrev Generated (index : Index) (source : Source index) := Algebra.Generated algebra PUnit.unit index source

theorem generated_assemble (index : Index) (arguments : Args index)
    (children : ∀ position, Generated
      (admitted.polynomial.next (inventoryEncode admitted.constructors arguments).1 position)
      ((inventoryEncode admitted.constructors arguments).2 position)) :
    Generated index (assemble index arguments) := by
  have closed := Algebra.generated_closed algebra PUnit.unit index
    (inventoryEncode admitted.constructors arguments).1
    (inventoryEncode admitted.constructors arguments).2 children
  change Generated index (assemble index
    (inventoryDecode admitted.constructors (inventoryEncode admitted.constructors arguments))) at closed
  exact Eq.mp (congrArg (fun remaining : Args index => Generated index (assemble index remaining))
    ((inventoryArgumentsEquiv admitted.constructors PUnit.unit Source index).left_inv arguments)) closed

theorem generated_thunk (term : Tm) (environment : List Krivine.NThunk)
    (generated : Generated (1, []) environment) : Generated (0, []) (.mk term environment) := by
  rw [← assemble_disassemble (0, []) (Krivine.NThunk.mk term environment)]
  apply generated_assemble
  intro position
  change Option PEmpty at position
  cases position with
  | none => exact generated
  | some impossible => exact impossible.elim

theorem generated_nil : Generated (1, []) ([] : List Krivine.NThunk) := by
  rw [← assemble_disassemble (1, []) ([] : List Krivine.NThunk)]
  apply generated_assemble
  intro position
  change PEmpty at position
  exact position.elim

theorem generated_cons (head : Krivine.NThunk) (tail : List Krivine.NThunk)
    (headGenerated : Generated (0, []) head) (tailGenerated : Generated (1, []) tail) :
    Generated (1, []) (head :: tail) := by
  rw [← assemble_disassemble (1, []) (head :: tail)]
  apply generated_assemble
  intro position
  change Option (Option PEmpty) at position
  cases position with
  | none => exact headGenerated
  | some position =>
      cases position with
      | none => exact tailGenerated
      | some impossible => exact impossible.elim

theorem generated_value (source : Krivine.NThunk) : Generated (0, []) source :=
  Krivine.NThunk.rec (motive_1 := fun value => Generated (0, []) value)
    (motive_2 := fun values => Generated (1, []) values)
    generated_thunk generated_nil generated_cons source

theorem generated_environment (source : List Krivine.NThunk) : Generated (1, []) source := by
  induction source with
  | nil => exact generated_nil
  | cons head tail ih => exact generated_cons head tail (generated_value head) ih

theorem generated_all (environment : Env (BlockProfile.interface model).Value [])
    (index : Index) (source : Source index) : Algebra.Generated algebra environment index source := by
  cases environment
  rcases index with ⟨tag, indices⟩
  cases indices with
  | cons _ _ => exact source.elim
  | nil =>
      cases tag with
      | zero => exact generated_value source
      | succ tag =>
          cases tag with
          | zero => exact generated_environment source
          | succ _ => exact source.elim

noncomputable def representation : Algebra.Representation admitted.polynomial algebra :=
  Algebra.representationOfGeneration algebra
    (Algebra.generatedAlgebra_injective algebra algebra_injective) generated_all

noncomputable def thunkEquiv : Krivine.NThunk ≃ admitted.Family PUnit.unit (0, []) :=
  (representation.toEquiv PUnit.unit (0, [])).symm

noncomputable def environmentEquiv : List Krivine.NThunk ≃ admitted.Family PUnit.unit (1, []) :=
  (representation.toEquiv PUnit.unit (1, [])).symm

theorem representation_construct (index : Index)
    (arguments : InventoryArguments admitted.constructors PUnit.unit (admitted.Family PUnit.unit) index) :
    representation.toEquiv PUnit.unit index (admitted.construct arguments) =
      assemble index (InventoryArguments.map admitted.constructors
        (fun index => representation.toEquiv PUnit.unit index) arguments) :=
  admitted.fold_construct (fun _ index arguments => assemble index arguments) arguments

theorem captured_environment_reflected (firstTerm secondTerm : Tm)
    (firstEnvironment secondEnvironment : List Krivine.NThunk)
    (same : thunkEquiv (.mk firstTerm firstEnvironment) = thunkEquiv (.mk secondTerm secondEnvironment)) :
    firstTerm = secondTerm ∧ firstEnvironment = secondEnvironment := by
  have original := thunkEquiv.injective same
  cases original
  exact ⟨rfl, rfl⟩

theorem empty_environment_is_not_cons (head : Krivine.NThunk) (tail : List Krivine.NThunk) :
    environmentEquiv [] ≠ environmentEquiv (head :: tail) := by
  intro same
  have original := environmentEquiv.injective same
  cases original

end Mettapedia.Languages.Lean.Declarations.KrivineBlockCorrespondence
