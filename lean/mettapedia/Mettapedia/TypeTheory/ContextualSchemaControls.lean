import Mettapedia.TypeTheory.ContextualSchemaTelescopes

/-!
# Dependent argument controls in the set-family model

The second argument is a finite index whose range is the first argument.
This tests a nonconstant family, the absence of a closed value in its empty
fibre, preservation of the old environment, and distinct supplied evidence.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSchemaControls

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualSchemaTelescopes

abbrev model := familiesCwf.{0}

def indexedArguments : Extension model Unit :=
  .cons (fun _ => Nat)
    (.cons (fun point => Fin point.2) (.nil _))

def supplied (n : Nat) (index : Fin n) :
    indexedArguments.Arguments (fun point : Unit => point) :=
  ⟨(fun _ => n), (fun _ => index), PUnit.unit⟩

theorem preserves_size_and_index (n : Nat) (index : Fin n) :
    indexedArguments.assemble (fun point : Unit => point) (supplied n index) () =
      ⟨⟨(), n⟩, index⟩ := rfl

theorem recovers_supplied_arguments (n : Nat) (index : Fin n) :
    indexedArguments.comprehensionEquiv Unit
        (indexedArguments.assemble (fun point : Unit => point) (supplied n index)) =
      ⟨(fun point : Unit => point), supplied n index⟩ :=
  indexedArguments.decompose_assemble _ _

/-- The family has a typed context even though its zero-size fibre has no closed point. -/
theorem no_zero_size_assignment :
    ¬ ∃ args : indexedArguments.Arguments (fun point : Unit => point), args.1 () = 0 := by
  rintro ⟨args, zero⟩
  have index : Fin (args.1 ()) := args.2.1 ()
  rw [zero] at index
  exact Fin.elim0 index

theorem different_indices_remain_distinct :
    indexedArguments.assemble (fun point : Unit => point) (supplied 3 ⟨0, by decide⟩) ≠
      indexedArguments.assemble (fun point : Unit => point) (supplied 3 ⟨2, by decide⟩) := by
  intro same
  have impossible := congrArg (fun value => (value ()).2.val) same
  change (0 : Nat) = 2 at impossible
  cases impossible

def varyingBase : Extension model Nat :=
  .cons (fun n => Fin (n + 1)) (.nil _)

def varyingValues : varyingBase.Arguments (fun n : Nat => n) :=
  ⟨(fun n => ⟨n, Nat.lt_succ_self n⟩), PUnit.unit⟩

theorem reindex_preserves_the_dependency (n : Nat) :
    let moved := varyingBase.precompose
      ⟨(fun n : Nat => n), varyingValues⟩ (fun n : Nat => n + 1)
    varyingBase.assemble moved.1 moved.2 n = ⟨n + 1, ⟨n + 1, Nat.lt_succ_self _⟩⟩ := by
  dsimp only
  rw [varyingBase.assemble_precompose]
  rfl

theorem empty_extension_preserves_every_environment (source base : model.Ctx)
    (substitution : model.Sub source base) :
    (Extension.nil base : Extension model base).assemble substitution PUnit.unit = substitution :=
  rfl

/-- A raw pair is checked before it can become a dependent argument tuple. -/
def checkIndexed (size index : Nat) :
    Option (indexedArguments.Arguments (fun point : Unit => point)) :=
  if valid : index < size then some (supplied size ⟨index, valid⟩) else none

theorem checkIndexed_none_iff (size index : Nat) :
    checkIndexed size index = none ↔ size ≤ index := by
  simp [checkIndexed]

theorem checked_arguments_retain_the_input (size index : Nat)
    (args : indexedArguments.Arguments (fun point : Unit => point))
    (accepted : checkIndexed size index = some args) :
    args.1 () = size ∧ (args.2.1 ()).val = index := by
  unfold checkIndexed at accepted
  split at accepted
  · cases Option.some.inj accepted
    exact ⟨rfl, rfl⟩
  · cases accepted

theorem a_dependency_breaking_exchange_is_rejected :
    (checkIndexed 2 1).isSome = true ∧ checkIndexed 1 2 = none := by
  constructor <;> rfl

def rememberBase : Extension model Bool :=
  .cons (fun _ => Bool) (.nil _)

def newTrue : rememberBase.Arguments (fun _ : Unit => false) :=
  ⟨(fun _ => true), PUnit.unit⟩

theorem new_value_does_not_capture_old_value :
    rememberBase.assemble (fun _ : Unit => false) newTrue () = ⟨false, true⟩ := rfl

/-- A type-correct map can still capture an old variable. Such a map cannot
be produced by opening with the fixed old environment. -/
theorem capturing_map_is_not_an_instantiation :
    ¬ ∃ args : rememberBase.Arguments (fun _ : Unit => false),
      rememberBase.assemble (fun _ : Unit => false) args =
        (fun _ : Unit => (⟨true, true⟩ : rememberBase.target)) := by
  rintro ⟨args, captured⟩
  have old := congrFun (rememberBase.weaken_assemble (fun _ : Unit => false) args) ()
  rw [captured] at old
  change true = false at old
  cases old

end Mettapedia.TypeTheory.ContextualSchemaControls
