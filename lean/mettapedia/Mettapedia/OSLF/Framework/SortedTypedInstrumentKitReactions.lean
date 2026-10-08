import Mettapedia.OSLF.Framework.SortedTypedInstrumentKitOccurrenceSupport
import Mettapedia.OSLF.Framework.SortedTypedInstrumentSourceFiringComparison

/-!
# Authored typed kit declarations with complete retained occurrences

Original rules are independently supplied over the original context category.
An administrative declaration retains its whole occurrence, including the
authored origin, typed argument tuple and selected position, with the kit
permissions derived for that occurrence. Expansion changes no occurrence.
Whole old-redex support reconstructs its unique old declaration preimage.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence

universe u v w z

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop} {OriginalOrigins : Type z} {NativeOrigins : Type w}

inductive Declaration (source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v})
    (Parallel : source.Srt → Prop) (OriginalOrigins : Type z) (NativeOrigins : Type w)
    (opened : Policy source Parallel) where
  | original (origin : OriginalOrigins)
  | administrative (occurrence : Occurrence source Parallel NativeOrigins)
      (permitted : Permitted opened occurrence)

variable {opened : Policy source Parallel}

def Declaration.origin : Declaration source Parallel OriginalOrigins NativeOrigins opened →
    OriginalOrigins ⊕ NativeOrigins
  | .original origin => .inl origin
  | .administrative occurrence _ => .inr occurrence.origin

def Declaration.rule
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel)) :
    Declaration source Parallel OriginalOrigins NativeOrigins opened → ReactionRule (Kit.origin opened)
  | .original supplied =>
      { codomain := (sourceInclusion opened).obj (originalRules supplied).codomain
        redex := (sourceInclusion opened).map (originalRules supplied).redex
        reactum := (sourceInclusion opened).map (originalRules supplied).reactum }
  | .administrative occurrence permitted =>
      { codomain := interface opened (result occurrence.instrument)
        redex := ⟨occurrence.rule.redex, (occurrence_redex_supported_iff opened occurrence).mpr permitted⟩
        reactum := ⟨occurrence.rule.reactum, occurrence_target_supported permitted⟩ }

def ruleImage (rule : ReactionRule (Kit.origin opened)) :
    ReactionRule (.origin : ContextCategory source Parallel) where
  codomain := rule.codomain.base
  redex := rule.redex.val
  reactum := rule.reactum.val

theorem original_ruleImage
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (supplied : OriginalOrigins) :
    ruleImage ((Declaration.original supplied :
      Declaration source Parallel OriginalOrigins NativeOrigins opened).rule originalRules) =
      Source.mapReactionRule (originalRules supplied) := rfl

theorem administrative_ruleImage
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (occurrence : Occurrence source Parallel NativeOrigins) (permitted : Permitted opened occurrence) :
    ruleImage ((Declaration.administrative occurrence permitted :
      Declaration source Parallel OriginalOrigins NativeOrigins opened).rule originalRules) =
      occurrence.rule := rfl

def categoryRules
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (opened : Policy source Parallel) (rule : ReactionRule (Kit.origin opened)) : Prop :=
  ∃ declaration : Declaration source Parallel OriginalOrigins NativeOrigins opened,
    declaration.rule originalRules = rule

def Declaration.expand {first second : Policy source Parallel}
    (subkit : ∀ head, first head → second head) :
    Declaration source Parallel OriginalOrigins NativeOrigins first →
      Declaration source Parallel OriginalOrigins NativeOrigins second
  | .original origin => .original origin
  | .administrative occurrence permitted => .administrative occurrence (permitted.monotone subkit)

theorem Declaration.expand_origin {first second : Policy source Parallel}
    (subkit : ∀ head, first head → second head)
    (declaration : Declaration source Parallel OriginalOrigins NativeOrigins first) :
    (declaration.expand subkit).origin = declaration.origin := by
  cases declaration <;> rfl

theorem Declaration.expand_id (opened : Policy source Parallel)
    (declaration : Declaration source Parallel OriginalOrigins NativeOrigins opened) :
    declaration.expand (fun head (permission : opened head) => permission) = declaration := by
  cases declaration <;> rfl

theorem Declaration.expand_comp {first second third : Policy source Parallel}
    (before : ∀ head, first head → second head) (after : ∀ head, second head → third head)
    (declaration : Declaration source Parallel OriginalOrigins NativeOrigins first) :
    (declaration.expand before).expand after =
      declaration.expand (fun head permission => after head (before head permission)) := by
  cases declaration <;> rfl

theorem Declaration.expand_injective {first second : Policy source Parallel}
    (subkit : ∀ head, first head → second head) :
    Function.Injective (Declaration.expand (OriginalOrigins := OriginalOrigins)
      (NativeOrigins := NativeOrigins) subkit) := by
  intro before after same
  cases before <;> cases after <;> cases same <;> rfl

def expandRule {first second : Policy source Parallel} (subkit : ∀ head, first head → second head)
    (rule : ReactionRule (Kit.origin first)) : ReactionRule (Kit.origin second) where
  codomain := (expand subkit).obj rule.codomain
  redex := (expand subkit).map rule.redex
  reactum := (expand subkit).map rule.reactum

theorem Declaration.expand_rule {first second : Policy source Parallel}
    (subkit : ∀ head, first head → second head)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (declaration : Declaration source Parallel OriginalOrigins NativeOrigins first) :
    expandRule subkit (declaration.rule originalRules) =
      (declaration.expand subkit).rule originalRules := by
  cases declaration <;> rfl

def Declaration.recover {first second : Policy source Parallel}
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (declaration : Declaration source Parallel OriginalOrigins NativeOrigins second)
    (supported : ArrowSupported first (ruleImage (declaration.rule originalRules)).redex) :
    Declaration source Parallel OriginalOrigins NativeOrigins first := by
  cases declaration with
  | original supplied => exact .original supplied
  | administrative occurrence permitted =>
    exact .administrative occurrence ((occurrence_redex_supported_iff first occurrence).mp supported)

theorem Declaration.recover_ruleImage {first second : Policy source Parallel}
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (declaration : Declaration source Parallel OriginalOrigins NativeOrigins second)
    (supported : ArrowSupported first (ruleImage (declaration.rule originalRules)).redex) :
    ruleImage ((declaration.recover originalRules supported).rule originalRules) =
      ruleImage (declaration.rule originalRules) := by
  cases declaration <;> rfl

theorem Declaration.recover_origin {first second : Policy source Parallel}
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (declaration : Declaration source Parallel OriginalOrigins NativeOrigins second)
    (supported : ArrowSupported first (ruleImage (declaration.rule originalRules)).redex) :
    (declaration.recover originalRules supported).origin = declaration.origin := by
  cases declaration <;> rfl

theorem Declaration.reactum_support_recover {first second : Policy source Parallel}
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (declaration : Declaration source Parallel OriginalOrigins NativeOrigins second)
    (supported : ArrowSupported first (ruleImage (declaration.rule originalRules)).redex) :
    ArrowSupported first (ruleImage (declaration.rule originalRules)).reactum := by
  cases declaration with
  | original supplied => exact source_arrow_supported first (originalRules supplied).reactum
  | administrative occurrence permitted =>
    exact occurrence_target_supported ((occurrence_redex_supported_iff first occurrence).mp supported)

theorem Declaration.expand_recover {first second : Policy source Parallel}
    (subkit : ∀ head, first head → second head)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (declaration : Declaration source Parallel OriginalOrigins NativeOrigins second)
    (supported : ArrowSupported first (ruleImage (declaration.rule originalRules)).redex) :
    (declaration.recover originalRules supported).expand subkit = declaration := by
  cases declaration <;> rfl

theorem Declaration.unique_old_preimage {first second : Policy source Parallel}
    (subkit : ∀ head, first head → second head)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (declaration : Declaration source Parallel OriginalOrigins NativeOrigins second)
    (supported : ArrowSupported first (ruleImage (declaration.rule originalRules)).redex) :
    ∃! before : Declaration source Parallel OriginalOrigins NativeOrigins first,
      before.expand subkit = declaration := by
  refine ⟨declaration.recover originalRules supported,
    declaration.expand_recover subkit originalRules supported, ?_⟩
  intro before readout
  apply Declaration.expand_injective subkit
  exact readout.trans (declaration.expand_recover subkit originalRules supported).symm

end Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit
