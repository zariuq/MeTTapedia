import Mettapedia.OSLF.Framework.SortedTypedInstrumentKitTransitions

/-!
# Unique whole firing reconstruction at old supported bounds

Actual firing receipts retain a declaration, its whole reaction context,
square and IPO proof. Expansion preserves those readings. At an old source
and label, support of the actual square reconstructs every supplied larger
receipt with the same authored occurrence and complete result. Uniqueness
concerns the preimage of a supplied receipt, not all firings at one label.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence

universe u v w z

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop} {OriginalOrigins : Type z} {NativeOrigins : Type w}
variable {before after : ContextCategory source Parallel}
  {agent : (.origin : ContextCategory source Parallel) ⟶ before} {label : before ⟶ after}

def expandFiring {first second : Policy source Parallel}
    (subkit : ∀ head, first head → second head)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (supplied : Source.FiringAt (Declaration source Parallel OriginalOrigins NativeOrigins first)
      (fun declaration => ruleImage (declaration.rule originalRules)) agent label) :
    Source.FiringAt (Declaration source Parallel OriginalOrigins NativeOrigins second)
      (fun declaration => ruleImage (declaration.rule originalRules)) agent label := by
  rcases supplied with ⟨declaration, reaction, square, minimal⟩
  cases declaration with
  | original origin => exact ⟨.original origin, reaction, square, minimal⟩
  | administrative occurrence permitted =>
    exact ⟨.administrative occurrence (permitted.monotone subkit), reaction, square, minimal⟩

def recoverFiring {first second : Policy source Parallel}
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (agentSupported : ArrowSupported first agent) (labelSupported : ArrowSupported first label)
    (supplied : Source.FiringAt (Declaration source Parallel OriginalOrigins NativeOrigins second)
      (fun declaration => ruleImage (declaration.rule originalRules)) agent label) :
    Source.FiringAt (Declaration source Parallel OriginalOrigins NativeOrigins first)
      (fun declaration => ruleImage (declaration.rule originalRules)) agent label := by
  rcases supplied with ⟨declaration, reaction, square, minimal⟩
  have filledSupported : ArrowSupported first ((ruleImage (declaration.rule originalRules)).redex ≫ reaction) :=
    square ▸ agentSupported.comp labelSupported
  have redexSupported := ((arrow_supported_comp_iff first _ _).mp filledSupported).1
  cases declaration with
  | original origin => exact ⟨.original origin, reaction, square, minimal⟩
  | administrative occurrence permitted =>
    exact ⟨.administrative occurrence ((occurrence_redex_supported_iff first occurrence).mp redexSupported),
      reaction, square, minimal⟩

theorem expandFiring_occurrence {first second : Policy source Parallel}
    (subkit : ∀ head, first head → second head)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (supplied : Source.FiringAt (Declaration source Parallel OriginalOrigins NativeOrigins first)
      (fun declaration => ruleImage (declaration.rule originalRules)) agent label) :
    (expandFiring subkit originalRules supplied).occurrence = supplied.occurrence.expand subkit := by
  rcases supplied with ⟨declaration, reaction, square, minimal⟩
  cases declaration <;> rfl

theorem expandFiring_origin {first second : Policy source Parallel}
    (subkit : ∀ head, first head → second head)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (supplied : Source.FiringAt (Declaration source Parallel OriginalOrigins NativeOrigins first)
      (fun declaration => ruleImage (declaration.rule originalRules)) agent label) :
    (expandFiring subkit originalRules supplied).occurrence.origin = supplied.occurrence.origin := by
  rw [expandFiring_occurrence, Declaration.expand_origin]

theorem expandFiring_reaction {first second : Policy source Parallel}
    (subkit : ∀ head, first head → second head)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (supplied : Source.FiringAt (Declaration source Parallel OriginalOrigins NativeOrigins first)
      (fun declaration => ruleImage (declaration.rule originalRules)) agent label) :
    HEq (expandFiring subkit originalRules supplied).reaction supplied.reaction := by
  rcases supplied with ⟨declaration, reaction, square, minimal⟩
  cases declaration <;> rfl

theorem expandFiring_result {first second : Policy source Parallel}
    (subkit : ∀ head, first head → second head)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (supplied : Source.FiringAt (Declaration source Parallel OriginalOrigins NativeOrigins first)
      (fun declaration => ruleImage (declaration.rule originalRules)) agent label) :
    (expandFiring subkit originalRules supplied).result = supplied.result := by
  rcases supplied with ⟨declaration, reaction, square, minimal⟩
  cases declaration <;> rfl

theorem recoverFiring_origin {first second : Policy source Parallel}
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (agentSupported : ArrowSupported first agent) (labelSupported : ArrowSupported first label)
    (supplied : Source.FiringAt (Declaration source Parallel OriginalOrigins NativeOrigins second)
      (fun declaration => ruleImage (declaration.rule originalRules)) agent label) :
    (recoverFiring originalRules agentSupported labelSupported supplied).occurrence.origin = supplied.occurrence.origin := by
  rcases supplied with ⟨declaration, reaction, square, minimal⟩
  cases declaration <;> rfl

theorem recoverFiring_reaction {first second : Policy source Parallel}
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (agentSupported : ArrowSupported first agent) (labelSupported : ArrowSupported first label)
    (supplied : Source.FiringAt (Declaration source Parallel OriginalOrigins NativeOrigins second)
      (fun declaration => ruleImage (declaration.rule originalRules)) agent label) :
    HEq (recoverFiring originalRules agentSupported labelSupported supplied).reaction supplied.reaction := by
  rcases supplied with ⟨declaration, reaction, square, minimal⟩
  cases declaration <;> rfl

theorem recoverFiring_result {first second : Policy source Parallel}
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (agentSupported : ArrowSupported first agent) (labelSupported : ArrowSupported first label)
    (supplied : Source.FiringAt (Declaration source Parallel OriginalOrigins NativeOrigins second)
      (fun declaration => ruleImage (declaration.rule originalRules)) agent label) :
    (recoverFiring originalRules agentSupported labelSupported supplied).result = supplied.result := by
  rcases supplied with ⟨declaration, reaction, square, minimal⟩
  cases declaration <;> rfl

theorem recover_expandFiring {first second : Policy source Parallel}
    (subkit : ∀ head, first head → second head)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (agentSupported : ArrowSupported first agent) (labelSupported : ArrowSupported first label)
    (supplied : Source.FiringAt (Declaration source Parallel OriginalOrigins NativeOrigins first)
      (fun declaration => ruleImage (declaration.rule originalRules)) agent label) :
    recoverFiring originalRules agentSupported labelSupported (expandFiring subkit originalRules supplied) = supplied := by
  rcases supplied with ⟨declaration, reaction, square, minimal⟩
  cases declaration <;> rfl

theorem expand_recoverFiring {first second : Policy source Parallel}
    (subkit : ∀ head, first head → second head)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (agentSupported : ArrowSupported first agent) (labelSupported : ArrowSupported first label)
    (supplied : Source.FiringAt (Declaration source Parallel OriginalOrigins NativeOrigins second)
      (fun declaration => ruleImage (declaration.rule originalRules)) agent label) :
    expandFiring subkit originalRules (recoverFiring originalRules agentSupported labelSupported supplied) = supplied := by
  rcases supplied with ⟨declaration, reaction, square, minimal⟩
  cases declaration <;> rfl

theorem expandFiring_injective {first second : Policy source Parallel}
    (subkit : ∀ head, first head → second head)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (agentSupported : ArrowSupported first agent) (labelSupported : ArrowSupported first label) :
    Function.Injective (expandFiring (NativeOrigins := NativeOrigins) subkit originalRules (agent := agent) (label := label)) := by
  intro before after same
  have recovered := congrArg (recoverFiring originalRules agentSupported labelSupported) same
  simpa only [recover_expandFiring] using recovered

theorem unique_old_firing {first second : Policy source Parallel}
    (subkit : ∀ head, first head → second head)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (agentSupported : ArrowSupported first agent) (labelSupported : ArrowSupported first label)
    (supplied : Source.FiringAt (Declaration source Parallel OriginalOrigins NativeOrigins second)
      (fun declaration => ruleImage (declaration.rule originalRules)) agent label) :
    ∃! old : Source.FiringAt (Declaration source Parallel OriginalOrigins NativeOrigins first)
      (fun declaration => ruleImage (declaration.rule originalRules)) agent label,
        expandFiring subkit originalRules old = supplied := by
  refine ⟨recoverFiring originalRules agentSupported labelSupported supplied,
    expand_recoverFiring subkit originalRules agentSupported labelSupported supplied, ?_⟩
  intro other same
  apply expandFiring_injective subkit originalRules agentSupported labelSupported
  exact same.trans (expand_recoverFiring subkit originalRules agentSupported labelSupported supplied).symm

theorem permitted_bounds {opened : Policy source Parallel}
    (occurrence : Occurrence source Parallel NativeOrigins) (permitted : Permitted opened occurrence) :
    ArrowSupported opened occurrence.agent ∧ ArrowSupported opened occurrence.label := by
  apply (arrow_supported_comp_iff opened _ _).mp
  rw [occurrence.complete_probe_square]
  exact (occurrence_redex_supported_iff opened occurrence).mpr permitted

def administrativeAgent {opened : Policy source Parallel}
    (occurrence : Occurrence source Parallel NativeOrigins) (permitted : Permitted opened occurrence) :
    origin opened ⟶ interface opened (receiver occurrence.instrument) :=
  ⟨occurrence.agent, (permitted_bounds occurrence permitted).1⟩

def administrativeLabel {opened : Policy source Parallel}
    (occurrence : Occurrence source Parallel NativeOrigins) (permitted : Permitted opened occurrence) :
    interface opened (receiver occurrence.instrument) ⟶ interface opened (result occurrence.instrument) :=
  ⟨occurrence.label, (permitted_bounds occurrence permitted).2⟩

def directAdministrativeFiring {opened : Policy source Parallel}
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (occurrence : Occurrence source Parallel NativeOrigins) (permitted : Permitted opened occurrence) :
    Source.FiringAt (Declaration source Parallel OriginalOrigins NativeOrigins opened)
      (fun declaration => declaration.rule originalRules)
      (administrativeAgent occurrence permitted) (administrativeLabel occurrence permitted) where
  occurrence := .administrative occurrence permitted
  reaction := 𝟙 _
  square := Subtype.ext (occurrence.complete_probe_square.trans (Category.comp_id occurrence.rule.redex).symm)
  minimal := (idemPushout_iff _).mpr (raw_right_identity_isIPO _ occurrence.complete_probe_square)

theorem directAdministrativeFiring_result {opened : Policy source Parallel}
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (occurrence : Occurrence source Parallel NativeOrigins) (permitted : Permitted opened occurrence) :
    ((directAdministrativeFiring originalRules occurrence permitted).result).val = occurrence.target :=
  Category.comp_id occurrence.rule.reactum

theorem directAdministrativeFiring_distinct_origins {opened : Policy source Parallel}
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (first second : NativeOrigins) (different : first ≠ second) (head : SourceHead source Parallel)
    (arguments : Arguments head) (permitted : Permitted opened (.ask first head arguments)) :
    HEq (directAdministrativeFiring originalRules (.ask first head arguments) permitted)
      (directAdministrativeFiring originalRules (.ask second head arguments) permitted) → False := by
  intro same
  have receiptSame := eq_of_heq same
  have origins := congrArg (fun receipt => receipt.occurrence.origin) receiptSame
  exact different (Sum.inr.inj origins)

end Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit
