import Mettapedia.TypeTheory.ContextualCwfUniverseLift

/-!
# Dependent values survive a change of contextual carrier sizes

The original set-family model has different context and section levels.
Its common-level lift retains a genuinely varying finite family, a supplied
section and a nonidentity substitution. Comprehension returns the exact
supplied witness; distinct sections remain distinct after lifting.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCwfUniverseLiftControls

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualCwfUniverseLift

abbrev original := familiesCwfWithTerminal.{0}
abbrev raised : CwfWithTerminal.{1, 1, 1, 1} := commonLiftWithTerminal.{1, 0, 1, 0, 1} original

abbrev context : raised.toCwf.Ctx := ⟨Nat⟩
abbrev domain : raised.toCwf.Ty context := ⟨fun (n : Nat) => Fin (n + 1)⟩
def diagonal : raised.toCwf.Tm context domain := ⟨fun (n : Nat) => ⟨n, Nat.lt_succ_self n⟩⟩
def otherSection : raised.toCwf.Tm context domain := ⟨fun (n : Nat) => ⟨0, Nat.zero_lt_succ n⟩⟩
def successor : raised.toCwf.Sub context context := ⟨fun (n : Nat) => n + 1⟩

theorem varying_family_readout (n : Nat) : domain.down n = Fin (n + 1) := rfl

theorem supplied_section_readout (n : Nat) : (diagonal.down n).val = n := rfl

theorem substituted_family_readout (n : Nat) :
    ((raised.toCwf.tySub domain successor).down n) = Fin (n + 2) := rfl

theorem substituted_section_readout (n : Nat) :
    ((raised.toCwf.tmSub diagonal successor).down n).val = n + 1 := rfl

theorem nonidentity_substitution : successor ≠ raised.toCwf.idS context := by
  intro same
  have values := congrArg (fun arrow : raised.toCwf.Sub context context => arrow.down 0) same
  exact (by decide : (1 : Nat) ≠ 0) values

theorem distinct_sections_retained : diagonal ≠ otherSection := by
  intro same
  have values := congrArg (fun term : raised.toCwf.Tm context domain => (term.down 1).val) same
  exact (by decide : (1 : Nat) ≠ 0) values

def actualPair : raised.toCwf.Sub context (raised.toCwf.ext context domain) :=
  raised.toCwf.pair successor domain (raised.toCwf.tmSub diagonal successor)

theorem pair_witness_readout (n : Nat) : (actualPair.down n).1 = n + 1 ∧
    (actualPair.down n).2.val = n + 1 := ⟨rfl, rfl⟩

theorem projection_recovers_substitution :
    raised.toCwf.compS (raised.toCwf.wk domain) actualPair = successor := raised.toCwf.wk_pair _ _ _

theorem variable_recovers_supplied_witness (n : Nat) :
    ((raised.toCwf.tmSub (raised.toCwf.vz domain) actualPair).down n).val = n + 1 := rfl

theorem substitution_equiv_recovers_arrow :
    (substitutionEquiv.{1, 0, 1, 0, 1, 1, 1, 1} original.toCwf context context).symm
      ((substitutionEquiv original.toCwf context context) successor) = successor :=
  (substitutionEquiv original.toCwf context context).symm_apply_apply successor

theorem section_equiv_recovers_witness :
    (termEquiv.{1, 0, 1, 0, 1, 1, 1, 1} original.toCwf context domain).symm
      ((termEquiv original.toCwf context domain) diagonal) = diagonal :=
  (termEquiv original.toCwf context domain).symm_apply_apply diagonal

end Mettapedia.TypeTheory.ContextualCwfUniverseLiftControls
