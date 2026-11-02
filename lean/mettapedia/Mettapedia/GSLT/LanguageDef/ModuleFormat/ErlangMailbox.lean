import Mettapedia.GSLT.LanguageDef.ModuleSource.Loader
import Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews
import Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
import Mettapedia.Languages.Erlang.Mailbox
import Mathlib.Data.Nat.Digits.Defs

/-! Authored Core Erlang mailbox operations, independent of source grammar.
These operations are a component of the eventual actor configuration, not an
implementation of complete Core Erlang. In particular, local waiting does
not decide global blockedness; the channel/delivery scheduler is separate.
The ground payload vocabulary is extended by the sequential IR as it lands. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat

namespace ErlangMailboxAuthoring
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
#module_tree "../../../../../../metta/gslt/module/ErlangMailbox.module" as Mailbox
#module_roundtrip ErlangData
#module_roundtrip ErlangMailbox
end ErlangMailboxAuthoring

namespace ErlangMailbox

open Mettapedia.OSLF.MeTTaIL Syntax
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

private instance : DecidableEq LanguageDef := fun first second => by
  cases first
  cases second
  exact decidable_of_iff' _ (Iff.of_eq (LanguageDef.mk.injEq _ _ _ _ _ _ _ _ _ _))

def language? : Option LanguageDef := ErlangMailboxAuthoring.Mailbox.language.toOption
def language : LanguageDef := module_language_view% language?
theorem language_exact : language? = some language := by decide +kernel

def node (name : String) (arguments : List Pattern := []) : Pattern := .apply name arguments

def values : List Pattern → Pattern
  | [] => node "ErValuesNil"
  | head :: tail => node "ErValuesCons" [head, values tail]

def atom (text : String) : Pattern := node "ErAtom" [.collection .vec
  (text.toUTF8.toList.flatMap fun byte =>
    [node ("R16Nibble" ++ toString (byte.toNat / 16)),
     node ("R16Nibble" ++ toString (byte.toNat % 16))]) none]

def integer (value : Int) : Pattern := node "ErInteger"
  [node (if value < 0 then "ErNegative" else "ErNonnegative"),
   .collection .vec ((Nat.digits 16 value.natAbs).map fun digit => node ("R16Nibble" ++ toString digit)) none]

def mailbox {α : Type*} (encode : α → Pattern) (box : Mettapedia.Languages.Erlang.Mailbox α) : Pattern :=
  node "ErMailbox" [values (box.savedRev.map encode), values (box.front.map encode), values (box.rearRev.map encode)]

def provider : GeneralPremise.ProviderSnapshot := {signatures := [], rows := []}
def permissions : GeneralExecutionAdmission.Permissions := {sites := .rootOnly, includeDerivedEquations := false}
def plan : GeneralExecutionAdmission.Plan := GeneralExecutionAdmission.compile ⟨language, [], provider⟩ permissions

#guard language.validate.isEmpty
#guard language.rewrites.length == 14
#guard language.equations.isEmpty
#guard plan.obligations.isEmpty

end ErlangMailbox
end Mettapedia.GSLT.LanguageDef.ModuleFormat
