import Mettapedia.OSLF.Syntax.BindingWireString
import Mettapedia.OSLF.Syntax.BindingTelescopeWireCodec
import Mettapedia.Languages.Agda.Structural.StaticSyntax

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Native.Codec
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.Languages.Agda.Structural
open Mettapedia.OSLF.Binding

instance signatureSortEq : DecidableEq sig.Srt := inferInstanceAs (DecidableEq Srt)

def putSort : Srt → Data
  | .term => .atom 0 | .type => .atom 1 | .sort => .atom 2
  | .level => .atom 3 | .elim => .atom 4 | .spine => .atom 5

def getSort : Data → Option Srt
  | .atom 0 => some .term | .atom 1 => some .type | .atom 2 => some .sort
  | .atom 3 => some .level | .atom 4 => some .elim | .atom 5 => some .spine
  | _ => none

def sort : Codec Srt := ⟨putSort, getSort, fun s => by cases s <;> rfl⟩

def putOperator : (Σ s : Srt, Op s) → Data
  | ⟨_, .lam⟩ => .atom 0
  | ⟨_, .lamNoAbs⟩ => .atom 1
  | ⟨_, .pi⟩ => .atom 2
  | ⟨_, .piNoAbs⟩ => .atom 3
  | ⟨_, .eliminate⟩ => .atom 4
  | ⟨_, .defined name⟩ => .pair (.atom 5) (Codec.string.put name)
  | ⟨_, .constructor name⟩ => .pair (.atom 6) (Codec.string.put name)
  | ⟨_, .natLiteral value⟩ => .pair (.atom 7) (.atom value)
  | ⟨_, .sortTerm⟩ => .atom 8
  | ⟨_, .levelTerm⟩ => .atom 9
  | ⟨_, .el⟩ => .atom 10
  | ⟨_, .set⟩ => .atom 11
  | ⟨_, .prop⟩ => .atom 12
  | ⟨_, .setOmega index⟩ => .pair (.atom 13) (.atom index)
  | ⟨_, .levelClosed value⟩ => .pair (.atom 14) (.atom value)
  | ⟨_, .levelSuc⟩ => .atom 15
  | ⟨_, .levelMax⟩ => .atom 16
  | ⟨_, .levelNeutral⟩ => .atom 17
  | ⟨_, .apply⟩ => .atom 18
  | ⟨_, .proj name⟩ => .pair (.atom 19) (Codec.string.put name)
  | ⟨_, .nil⟩ => .atom 20
  | ⟨_, .cons⟩ => .atom 21
  | ⟨_, .append⟩ => .atom 22

def getOperator : Data → Option (Σ s : Srt, Op s)
  | .atom 0 => some ⟨_, .lam⟩
  | .atom 1 => some ⟨_, .lamNoAbs⟩
  | .atom 2 => some ⟨_, .pi⟩
  | .atom 3 => some ⟨_, .piNoAbs⟩
  | .atom 4 => some ⟨_, .eliminate⟩
  | .pair (.atom 5) payload => Codec.string.get payload |>.map (fun name => ⟨_, .defined name⟩)
  | .pair (.atom 6) payload => Codec.string.get payload |>.map (fun name => ⟨_, .constructor name⟩)
  | .pair (.atom 7) (.atom value) => some ⟨_, .natLiteral value⟩
  | .atom 8 => some ⟨_, .sortTerm⟩
  | .atom 9 => some ⟨_, .levelTerm⟩
  | .atom 10 => some ⟨_, .el⟩
  | .atom 11 => some ⟨_, .set⟩
  | .atom 12 => some ⟨_, .prop⟩
  | .pair (.atom 13) (.atom index) => some ⟨_, .setOmega index⟩
  | .pair (.atom 14) (.atom value) => some ⟨_, .levelClosed value⟩
  | .atom 15 => some ⟨_, .levelSuc⟩
  | .atom 16 => some ⟨_, .levelMax⟩
  | .atom 17 => some ⟨_, .levelNeutral⟩
  | .atom 18 => some ⟨_, .apply⟩
  | .pair (.atom 19) payload => Codec.string.get payload |>.map (fun name => ⟨_, .proj name⟩)
  | .atom 20 => some ⟨_, .nil⟩
  | .atom 21 => some ⟨_, .cons⟩
  | .atom 22 => some ⟨_, .append⟩
  | _ => none

theorem get_putOperator (value : Σ s : Srt, Op s) : getOperator (putOperator value) = some value := by
  rcases value with ⟨s, op⟩
  cases op <;> first | rfl | (simp only [putOperator, getOperator, Codec.get_put]; rfl)

def operator : Codec (Σ s : sig.Srt, sig.Op s) := ⟨putOperator, getOperator, get_putOperator⟩

def scopedTerm (Γ : Ctx sig) (s : Srt) : Codec (Term sig Γ s) := Mettapedia.OSLF.Binding.WireCodec.term operator Γ s
def rawTerm (n : Nat) (s : Srt) : Codec (Term sig (Telescope.scope (S := sig) .term n) s) :=
  scopedTerm (Telescope.scope (S := sig) .term n) s
def rawContext (n : Nat) : Codec (ContextGeometry.RawContext n) :=
  Mettapedia.OSLF.Binding.WireCodec.contextAt operator .term .type n
def context : Codec (Sigma ContextGeometry.RawContext) := Mettapedia.OSLF.Binding.WireCodec.context operator .term .type
def rawSub (n m : Nat) : Codec (ContextGeometry.RawSub n m) :=
  Mettapedia.OSLF.Binding.WireCodec.substitution operator .term n m

theorem rawTerm_roundtrip (n : Nat) (s : Srt) (t : Term sig (scope n) s) :
    (rawTerm n s).get ((rawTerm n s).put t) = some t := (rawTerm n s).get_put t

end Mettapedia.Languages.Agda.Native.Codec
