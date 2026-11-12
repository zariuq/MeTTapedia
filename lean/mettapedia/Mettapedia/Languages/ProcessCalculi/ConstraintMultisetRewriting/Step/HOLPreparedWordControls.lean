import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLPreparedWordModel
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Reindex

/-!
# Arbitrarily long native words and permission-sensitive loaded domains

This control profile deliberately permits repeated prepared tells. It is a
different admission profile from the duplicate-refusing source example.
Every finite Boolean label word yields an actual native run and changes the
physical equation-list length. The same complete packets are refused under
the false permission profile. No fixed run length or enumeration is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLPreparedWordControls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Controls (Store frame effect)
open HOLPreparedRunEncoding

def repeated : Step frame Nat Store (fun _ => Unit) := Step.ofEffect effect (fun _ _ => True)
def program : Step frame Nat Store (fun _ => Bool) := repeated.reindex (fun _ => ())

theorem allowed (store : Store) (label : Bool) : program.Admits (s := store) label :=
  ⟨Presentation.Controls.prepares store (), trivial⟩

theorem result_append (store : Store) (label : Bool) (permitted : program.Admits (s := store) label) :
    program.result label permitted = store ++ [(true, false)] := rfl

def run : (store : Store) → List Bool → program.Run store
  | store, [] => .nil store
  | store, label :: labels => .cons label (allowed store label) (run _ labels)

theorem labels_retained (store : Store) (labels : List Bool) :
    ((run store labels).word.map fun event => event.2) = labels := by
  induction labels generalizing store with
  | nil => rfl
  | cons label labels ih => simp only [run, Step.Run.word, List.map_cons, ih]

theorem physical_length (store : Store) (labels : List Bool) :
    (run store labels).last.length = store.length + labels.length := by
  induction labels generalizing store with
  | nil => simp [run, Step.Run.last]
  | cons label labels ih =>
      change (run (program.result label (allowed store label)) labels).last.length = _
      rw [ih, result_append]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

theorem event_path_length (store : Store) (labels : List Bool) :
    ((run store labels).eventPath program).length = labels.length := by
  induction labels generalizing store with
  | nil => rfl
  | cons label labels ih => simp [run, Step.Run.eventPath, ih, Nat.add_comm]

def packets (store : Store) (labels : List Bool) : List (RawEvent program.effectCore) :=
  HOLPreparedRunEncoding.word program.effectCore program.eventAdmission ((run store labels).eventPath program)

theorem packet_length (store : Store) (labels : List Bool) : (packets store labels).length = labels.length :=
  (HOLPreparedWordPackets.packet_word_length program.effectCore program.eventAdmission _).trans
    (event_path_length store labels)

variable (input : HOLPreparedWordModel.Input) (other : TypeFamilySemantics.OperatorFamilies.{0})
  (prior : TypeFamilySemantics.Assignment.{0})

theorem every_finite_word_admitted (store : Store) (labels : List Bool) :
    (input.operations.signature.domainValue (input.model program.effectCore other prior)
      (HOLPreparedWordSpecialization.preparationValue program.effectCore _ _ (input.coding program.effectCore other prior))
      (HOLPreparedWordSpecialization.resultValue program.effectCore _ _ (input.coding program.effectCore other prior))
      (HOLPreparedWordSpecialization.permissionValue program.effectCore _ _ (input.coding program.effectCore other prior)
        program.eventAdmission)
      (HOLPreparedWordSpecialization.wordValue program.effectCore _ _ (input.coding program.effectCore other prior)
        (input.agreement program.effectCore other prior) (packets store labels))
      ((input.coding program.effectCore other prior).states.symm (some store))).down :=
  (input.domain_iff_native_path program.effectCore other prior program.eventAdmission _ store).mpr
    ⟨(run store labels).last, (run store labels).eventPath program, rfl⟩

theorem every_nonempty_word_refused (store : Store) (label : Bool) (labels : List Bool) :
    ¬(input.operations.signature.domainValue (input.model program.effectCore other prior)
      (HOLPreparedWordSpecialization.preparationValue program.effectCore _ _ (input.coding program.effectCore other prior))
      (HOLPreparedWordSpecialization.resultValue program.effectCore _ _ (input.coding program.effectCore other prior))
      (HOLPreparedWordSpecialization.permissionValue program.effectCore _ _ (input.coding program.effectCore other prior)
        (fun _ _ => False))
      (HOLPreparedWordSpecialization.wordValue program.effectCore _ _ (input.coding program.effectCore other prior)
        (input.agreement program.effectCore other prior) (packets store (label :: labels)))
      ((input.coding program.effectCore other prior).states.symm (some store))).down := by
  intro domain
  obtain ⟨destination, path, same⟩ :=
    (input.domain_iff_native_path program.effectCore other prior (fun _ _ => False) _ store).mp domain
  have native := HOLPreparedRunEncoding.path_word_run program.effectCore (fun _ _ => False) path
  rw [same] at native
  have nonempty : (packets store (label :: labels)).length ≠ 0 := by rw [packet_length]; simp
  cases wordEq : packets store (label :: labels) with
  | nil => simp [wordEq] at nonempty
  | cons event events =>
      rw [wordEq] at native
      exact HOLPreparedRunEncoding.refused_nonempty program.effectCore event events _ _ native

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLPreparedWordControls
