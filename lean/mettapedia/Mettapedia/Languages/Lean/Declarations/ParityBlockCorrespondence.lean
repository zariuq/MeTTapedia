import Mettapedia.Languages.Lean.Declarations.CEKBlockCorrespondence

/-!
# The indexed Even/Odd source block and its admitted fibres

Member ordinals and natural indices are both retained. Source propositions
are lifted into Type only for the polynomial algebra; the final inhabitance
theorems recover the original propositions. No proof is eliminated into data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Lean.Declarations.ParityBlockCorrespondence

open Mettapedia.TypeTheory
open IndexedPolynomial IndexedPolynomial.Description
open Mettapedia.GSLT.LanguageDef

inductive IndexValue where
  | natural (value : Nat)
  | successor
  | invalid
  deriving DecidableEq, Repr

def value (sort : STerm) : Type := if sort = .name "Nat" then Nat else PEmpty

def inject (sort : STerm) (data : value sort) : IndexValue := by
  by_cases same : sort = .name "Nat"
  · subst sort
    exact .natural data
  · exact PEmpty.elim (show PEmpty from by simpa [value, same] using data)

def model : Profile.Model where
  Value := value
  Domain := IndexValue
  inject := inject
  constant := fun name => if name = "Nat.zero" then .natural 0
    else if name = "Nat.succ" then .successor else .invalid
  apply := fun function argument => match function, argument with
    | .successor, .natural n => .natural (n + 1)
    | _, _ => .invalid

def admitted : IndexedInductive.Admitted (BlockProfile.interface model) [] :=
  ((BlockProfile.admit model BlockControls.parity).toOption).get (by decide)

abbrev Index := Nat × List IndexValue

def Source (index : Index) : Type :=
  match index.2 with
  | [.natural n] => match index.1 with
      | 0 => PLift (Controls.Even n)
      | 1 => PLift (Controls.Odd n)
      | _ => PEmpty
  | _ => PEmpty

abbrev Args (index : Index) := InventoryArguments admitted.constructors PUnit.unit Source index

def assemble (index : Index) (arguments : Args index) : Source index := by
  rcases arguments with ⟨occurrence, arguments⟩
  change Fin 3 at occurrence
  refine Fin.cases ?_ (fun rest => ?_) occurrence arguments
  · intro arguments
    change ULift (PLift ((0, [IndexValue.natural 0]) = index)) at arguments
    rcases arguments with ⟨⟨same⟩⟩
    subst index
    exact ⟨Controls.Even.zero⟩
  · refine Fin.cases ?_ (fun rest => ?_) rest
    · intro arguments
      change (Σ n : Nat, PLift (Controls.Odd n) ×
        ULift (PLift ((0, [IndexValue.natural (n + 1)]) = index))) at arguments
      rcases arguments with ⟨n, child, ⟨⟨same⟩⟩⟩
      subst index
      exact ⟨Controls.Even.succ child.down⟩
    · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) rest
      intro arguments
      change (Σ n : Nat, PLift (Controls.Even n) ×
        ULift (PLift ((1, [IndexValue.natural (n + 1)]) = index))) at arguments
      rcases arguments with ⟨n, child, ⟨⟨same⟩⟩⟩
      subst index
      exact ⟨Controls.Odd.succ child.down⟩

theorem even_predecessor {n : Nat} (proof : Controls.Even (n + 1)) : Controls.Odd n := by
  cases proof with
  | succ previous => exact previous

theorem odd_predecessor {n : Nat} (proof : Controls.Odd (n + 1)) : Controls.Even n := by
  cases proof with
  | succ previous => exact previous

theorem odd_zero_false (proof : Controls.Odd 0) : False := by cases proof

def disassemble (index : Index) (source : Source index) : Args index := by
  rcases index with ⟨tag, indices⟩
  cases indices with
  | nil => exact source.elim
  | cons first tail =>
      cases first with
      | successor => cases tail <;> exact source.elim
      | invalid => cases tail <;> exact source.elim
      | natural n =>
          cases tail with
          | cons _ _ => exact source.elim
          | nil =>
              cases tag with
              | zero =>
                  cases n with
                  | zero =>
                      refine ⟨⟨0, by decide⟩, ?_⟩
                      change ULift (PLift ((0, [IndexValue.natural 0]) = (0, [IndexValue.natural 0])))
                      exact ⟨⟨rfl⟩⟩
                  | succ n =>
                      refine ⟨⟨1, by decide⟩, ?_⟩
                      change Σ m : Nat, PLift (Controls.Odd m) ×
                        ULift (PLift ((0, [IndexValue.natural (m + 1)]) = (0, [IndexValue.natural (n + 1)])))
                      exact ⟨n, ⟨even_predecessor source.down⟩, ⟨⟨rfl⟩⟩⟩
              | succ tag =>
                  cases tag with
                  | succ _ => exact source.elim
                  | zero =>
                      cases n with
                      | zero => exact False.elim (odd_zero_false source.down)
                      | succ n =>
                          refine ⟨⟨2, by decide⟩, ?_⟩
                          change Σ m : Nat, PLift (Controls.Even m) ×
                            ULift (PLift ((1, [IndexValue.natural (m + 1)]) = (1, [IndexValue.natural (n + 1)])))
                          exact ⟨n, ⟨odd_predecessor source.down⟩, ⟨⟨rfl⟩⟩⟩

instance sourceSubsingleton (index : Index) : Subsingleton (Source index) := by
  unfold Source
  split
  · split <;> infer_instance
  · infer_instance

theorem assemble_disassemble (index : Index) (source : Source index) :
    assemble index (disassemble index source) = source := Subsingleton.elim _ _

theorem disassemble_assemble (index : Index) (arguments : Args index) :
    disassemble index (assemble index arguments) = arguments := by
  rcases arguments with ⟨occurrence, arguments⟩
  change Fin 3 at occurrence
  fin_cases occurrence
  · change ULift (PLift ((0, [IndexValue.natural 0]) = index)) at arguments
    rcases arguments with ⟨⟨same⟩⟩
    subst index
    rfl
  · change (Σ n : Nat, PLift (Controls.Odd n) ×
      ULift (PLift ((0, [IndexValue.natural (n + 1)]) = index))) at arguments
    rcases arguments with ⟨n, ⟨child⟩, ⟨⟨same⟩⟩⟩
    subst index
    rfl
  · change (Σ n : Nat, PLift (Controls.Even n) ×
      ULift (PLift ((1, [IndexValue.natural (n + 1)]) = index))) at arguments
    rcases arguments with ⟨n, ⟨child⟩, ⟨⟨same⟩⟩⟩
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

def evenValue (n : Nat) (proof : Controls.Even n) : Source (0, [.natural n]) := ⟨proof⟩
def oddValue (n : Nat) (proof : Controls.Odd n) : Source (1, [.natural n]) := ⟨proof⟩

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

theorem generated_zero : Generated (0, [.natural 0]) ⟨Controls.Even.zero⟩ := by
  rw [← assemble_disassemble (0, [.natural 0]) ⟨Controls.Even.zero⟩]
  apply generated_assemble
  intro position
  change PEmpty at position
  exact position.elim

theorem generated_even_step (n : Nat) (proof : Controls.Odd n)
    (generated : Generated (1, [.natural n]) ⟨proof⟩) :
    Generated (0, [.natural (n + 1)]) (evenValue (n + 1) (Controls.Even.succ proof)) := by
  rw [← assemble_disassemble (0, [.natural (n + 1)]) (evenValue (n + 1) (Controls.Even.succ proof))]
  apply generated_assemble
  intro position
  change Option PEmpty at position
  cases position with
  | none => exact generated
  | some impossible => exact impossible.elim

theorem generated_odd_step (n : Nat) (proof : Controls.Even n)
    (generated : Generated (0, [.natural n]) ⟨proof⟩) :
    Generated (1, [.natural (n + 1)]) (oddValue (n + 1) (Controls.Odd.succ proof)) := by
  rw [← assemble_disassemble (1, [.natural (n + 1)]) (oddValue (n + 1) (Controls.Odd.succ proof))]
  apply generated_assemble
  intro position
  change Option PEmpty at position
  cases position with
  | none => exact generated
  | some impossible => exact impossible.elim

theorem generated_even (n : Nat) (proof : Controls.Even n) : Generated (0, [.natural n]) ⟨proof⟩ :=
  Controls.Even.rec
    (motive_1 := fun n proof => Generated (0, [.natural n]) ⟨proof⟩)
    (motive_2 := fun n proof => Generated (1, [.natural n]) ⟨proof⟩)
    generated_zero (fun {_} child ih => generated_even_step _ child ih)
    (fun {_} child ih => generated_odd_step _ child ih) proof

theorem generated_odd (n : Nat) (proof : Controls.Odd n) : Generated (1, [.natural n]) ⟨proof⟩ :=
  Controls.Odd.rec
    (motive_1 := fun n proof => Generated (0, [.natural n]) ⟨proof⟩)
    (motive_2 := fun n proof => Generated (1, [.natural n]) ⟨proof⟩)
    generated_zero (fun {_} child ih => generated_even_step _ child ih)
    (fun {_} child ih => generated_odd_step _ child ih) proof

theorem generated_all (environment : Env (BlockProfile.interface model).Value [])
    (index : Index) (source : Source index) : Algebra.Generated algebra environment index source := by
  cases environment
  rcases index with ⟨tag, indices⟩
  cases indices with
  | nil => exact source.elim
  | cons first tail =>
      cases first with
      | successor => cases tail <;> exact source.elim
      | invalid => cases tail <;> exact source.elim
      | natural n =>
          cases tail with
          | cons _ _ => exact source.elim
          | nil =>
              cases tag with
              | zero => exact generated_even n source.down
              | succ tag =>
                  cases tag with
                  | zero => exact generated_odd n source.down
                  | succ _ => exact source.elim

noncomputable def representation : Algebra.Representation admitted.polynomial algebra :=
  Algebra.representationOfGeneration algebra
    (Algebra.generatedAlgebra_injective algebra algebra_injective) generated_all

noncomputable def evenEquiv (n : Nat) : PLift (Controls.Even n) ≃ admitted.Family PUnit.unit (0, [.natural n]) :=
  (representation.toEquiv PUnit.unit (0, [.natural n])).symm

noncomputable def oddEquiv (n : Nat) : PLift (Controls.Odd n) ≃ admitted.Family PUnit.unit (1, [.natural n]) :=
  (representation.toEquiv PUnit.unit (1, [.natural n])).symm

theorem representation_construct (index : Index)
    (arguments : InventoryArguments admitted.constructors PUnit.unit (admitted.Family PUnit.unit) index) :
    representation.toEquiv PUnit.unit index (admitted.construct arguments) =
      assemble index (InventoryArguments.map admitted.constructors
        (fun index => representation.toEquiv PUnit.unit index) arguments) :=
  admitted.fold_construct (fun _ index arguments => assemble index arguments) arguments

theorem even_inhabited_iff (n : Nat) : Nonempty (admitted.Family PUnit.unit (0, [.natural n])) ↔ Controls.Even n := by
  constructor
  · rintro ⟨tree⟩
    exact ((evenEquiv n).symm tree).down
  · intro proof
    exact ⟨evenEquiv n ⟨proof⟩⟩

theorem odd_inhabited_iff (n : Nat) : Nonempty (admitted.Family PUnit.unit (1, [.natural n])) ↔ Controls.Odd n := by
  constructor
  · rintro ⟨tree⟩
    exact ((oddEquiv n).symm tree).down
  · intro proof
    exact ⟨oddEquiv n ⟨proof⟩⟩

theorem odd_zero_has_no_value : ¬ Nonempty (admitted.Family PUnit.unit (1, [.natural 0])) := by
  intro inhabited
  exact odd_zero_false ((odd_inhabited_iff 0).mp inhabited)

theorem even_zero_has_value : Nonempty (admitted.Family PUnit.unit (0, [.natural 0])) :=
  (even_inhabited_iff 0).mpr Controls.Even.zero

end Mettapedia.Languages.Lean.Declarations.ParityBlockCorrespondence
