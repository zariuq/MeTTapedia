import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox
import Mettapedia.Languages.Erlang.Network

/-! The point-to-point queue component of the Erlang operational IR. A send
appends to a selected channel; delivery transfers only its head into the
receiver's mailbox. Selection between channels belongs to the configuration
scheduler, governed independently by Erlang.Network. These operations do not
conflate a local empty channel with global blockedness. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat

namespace ErlangChannelAuthoring
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
#module_tree "../../../../../../metta/gslt/module/ErlangChannel.module" as Channel
#module_roundtrip ErlangChannel
end ErlangChannelAuthoring

namespace ErlangChannel

open Mettapedia.OSLF.MeTTaIL Syntax
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

private instance : DecidableEq LanguageDef := fun first second => by
  cases first
  cases second
  exact decidable_of_iff' _ (Iff.of_eq (LanguageDef.mk.injEq _ _ _ _ _ _ _ _ _ _))

def language? : Option LanguageDef := ErlangChannelAuthoring.Channel.language.toOption
def language : LanguageDef := module_language_view% language?
theorem language_exact : language? = some language := by decide +kernel

def pid (number : Nat) : Pattern := ErlangMailbox.node "ErPid" [.collection .vec
  ((Nat.digits 16 number).map fun digit => ErlangMailbox.node ("R16Nibble" ++ toString digit)) none]

def provider : GeneralPremise.ProviderSnapshot := {signatures := [], rows := []}
def permissions : GeneralExecutionAdmission.Permissions :=
  {sites := .rootOnly, includeDerivedEquations := false}
def plan : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile ⟨language, [], provider⟩ permissions

#guard language.validate.isEmpty
#guard language.rewrites.length == 20
#guard language.equations.isEmpty
#guard plan.obligations.isEmpty

end ErlangChannel
end Mettapedia.GSLT.LanguageDef.ModuleFormat
