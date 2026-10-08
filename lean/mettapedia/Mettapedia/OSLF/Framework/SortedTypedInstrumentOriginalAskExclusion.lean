import Mettapedia.OSLF.Framework.SortedTypedInstrumentOriginalAskFactorization
import Mettapedia.OSLF.Framework.SortedTypedInstrumentSourceFiringComparison

/-!
# Actual original-rule exclusion at heterogeneous ask IPOs

Whole original-reaction factorization supplies an explicit smaller candidate
at the actual ask receiver. IPO down-splitting contradicts the positive
probe support. Original rules at the source origin have a separate candidate.
The result permits arbitrary original rules, sorts and unit redexes; it
excludes no original get firing merely by its declaration namespace.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence

universe u v w

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop} {Origins : Type w}

theorem original_ask_square_not_ipo {original : source.Srt} (head : SourceHead source Parallel)
    (supplied : ValueClass (source := source) (Parallel := Parallel) (.original (headOutput head)))
    (redex : ValueClass (source := source) (Parallel := Parallel) (.original original))
    (reaction : ContextClass (signature source Parallel) NativeParallel (.original original) (.arguments head))
    (square : (RawArrow.value supplied : (.origin : ContextCategory source Parallel) ⟶
        .interface (.original (headOutput head))) ≫ probeLabel (.ask head) =
      RawArrow.value redex ≫ RawArrow.context reaction) :
    ¬IsIdemPushout (C := ContextCategory source Parallel) (RawArrow.value supplied) (RawArrow.value redex)
      (probeLabel (.ask head)) (RawArrow.context reaction) square := by
  have read : reaction.fill redex = (contextClassOf (probeContext (.ask head))).fill supplied :=
    (RawArrow.value.inj square).symm
  obtain ⟨before, inputRead, reactionRead⟩ := ask_reaction_factorization head supplied redex reaction read
  let candidate : Candidate (C := ContextCategory source Parallel)
      (RawArrow.value supplied) (RawArrow.value redex) (probeLabel (.ask head)) (RawArrow.context reaction) :=
    { apex := .interface (.original (headOutput head))
      inl := 𝟙 (.interface (.original (headOutput head)) : ContextCategory source Parallel)
      inr := RawArrow.context before
      down := probeLabel (.ask head)
      comm := (Category.comp_id _).trans (congrArg RawArrow.value inputRead).symm
      fac_left := Category.id_comp _
      fac_right := congrArg RawArrow.context reactionRead.symm }
  intro minimal
  obtain ⟨section_, recovers⟩ := minimal.down_splits candidate
  have support := congrArg arrowObserverCount recovers
  change arrowObserverCount (section_ ≫ probeLabel (.ask head)) = 0 at support
  rw [arrowCount_comp, probeLabel_support] at support
  omega

theorem origin_probe_square_not_ipo (instrument : Probe source Parallel)
    (supplied : ValueClass (source := source) (Parallel := Parallel) (receiver instrument))
    (reaction : (.origin : ContextCategory source Parallel) ⟶ .interface (result instrument))
    (square : (RawArrow.value supplied : (.origin : ContextCategory source Parallel) ⟶
        .interface (receiver instrument)) ≫ probeLabel instrument =
      𝟙 (.origin : ContextCategory source Parallel) ≫ reaction) :
    ¬IsIdemPushout (C := ContextCategory source Parallel) (RawArrow.value supplied)
      (𝟙 (.origin : ContextCategory source Parallel)) (probeLabel instrument) reaction square := by
  let candidate : Candidate (C := ContextCategory source Parallel) (RawArrow.value supplied)
      (𝟙 (.origin : ContextCategory source Parallel)) (probeLabel instrument) reaction :=
    { apex := .interface (receiver instrument)
      inl := 𝟙 (.interface (receiver instrument) : ContextCategory source Parallel)
      inr := RawArrow.value supplied
      down := probeLabel instrument
      comm := by simp only [Category.comp_id, Category.id_comp]
      fac_left := Category.id_comp _
      fac_right := square.trans (Category.id_comp reaction) }
  intro minimal
  obtain ⟨section_, recovers⟩ := minimal.down_splits candidate
  have support := congrArg arrowObserverCount recovers
  change arrowObserverCount (section_ ≫ probeLabel instrument) = 0 at support
  rw [arrowCount_comp, probeLabel_support] at support
  omega

theorem mapped_original_ask_not_ipo (head : SourceHead source Parallel)
    (original : ReactionRule (.origin : SourceCategory source Parallel))
    (supplied : ValueClass (source := source) (Parallel := Parallel) (.original (headOutput head)))
    (reaction : (Source.mapReactionRule original).codomain ⟶
      (.interface (.arguments head) : ContextCategory source Parallel))
    (square : (RawArrow.value supplied : (.origin : ContextCategory source Parallel) ⟶
        .interface (.original (headOutput head))) ≫ probeLabel (.ask head) =
      (Source.mapReactionRule original).redex ≫ reaction) :
    ¬IsIdemPushout (C := ContextCategory source Parallel) (RawArrow.value supplied)
      (Source.mapReactionRule original).redex (probeLabel (.ask head)) reaction square := by
  cases original with
  | mk codomain redex reactum =>
    cases codomain with
    | origin =>
      cases redex with
      | identity => exact origin_probe_square_not_ipo (.ask head) supplied reaction square
    | interface sort =>
      cases redex with
      | value redex =>
        cases reaction with
        | context reaction => exact original_ask_square_not_ipo head supplied _ reaction square

def combinedSourceRules
    (sourceRules : ReactionRule (.origin : SourceCategory source Parallel) → Prop) (Origins : Type w) :
    ReactionRule (.origin : ContextCategory source Parallel) → Prop :=
  fun rule => rules source Parallel Origins rule ∨ Source.mappedRules sourceRules rule

theorem source_rules_do_not_fire_under_ask
    (sourceRules : ReactionRule (.origin : SourceCategory source Parallel) → Prop)
    (head : SourceHead source Parallel)
    (supplied : ValueClass (source := source) (Parallel := Parallel) (.original (headOutput head)))
    (observed : (.origin : ContextCategory source Parallel) ⟶ .interface (.arguments head)) :
    ¬ActIPO (Source.mappedRules sourceRules) (probeLabel (.ask head)) (RawArrow.value supplied) observed := by
  rintro ⟨rule, ⟨original, _admitted, rfl⟩, reaction, square, minimal, _output⟩
  exact mapped_original_ask_not_ipo head original supplied reaction square minimal

theorem combined_ask_step_iff_administrative
    (sourceRules : ReactionRule (.origin : SourceCategory source Parallel) → Prop)
    (head : SourceHead source Parallel)
    (supplied : ValueClass (source := source) (Parallel := Parallel) (.original (headOutput head)))
    (observed : (.origin : ContextCategory source Parallel) ⟶ .interface (.arguments head)) :
    ActIPO (combinedSourceRules sourceRules Origins) (probeLabel (.ask head))
        (RawArrow.value supplied) observed ↔
      ActIPO (rules source Parallel Origins) (probeLabel (.ask head)) (RawArrow.value supplied) observed := by
  constructor
  · rintro ⟨rule, admitted, reaction, square, minimal, output⟩
    rcases admitted with administrative | original
    · exact ⟨rule, administrative, reaction, square, minimal, output⟩
    · exact (source_rules_do_not_fire_under_ask sourceRules head supplied observed
        ⟨rule, original, reaction, square, minimal, output⟩).elim
  · rintro ⟨rule, admitted, reaction, square, minimal, output⟩
    exact ⟨rule, Or.inl admitted, reaction, square, minimal, output⟩

theorem combined_ask_step_iff
    (sourceRules : ReactionRule (.origin : SourceCategory source Parallel) → Prop)
    (head : SourceHead source Parallel)
    (supplied : ValueClass (source := source) (Parallel := Parallel) (.original (headOutput head)))
    (observed : ValueClass (source := source) (Parallel := Parallel) (.arguments head)) :
    ActIPO (combinedSourceRules sourceRules Origins) (probeLabel (.ask head))
        (RawArrow.value supplied) (RawArrow.value observed) ↔
      ∃ _origin : Origins, ∃ arguments : Arguments head,
        supplied = classOf (sourceNode head arguments) ∧ observed = classOf (bundle head arguments) :=
  (combined_ask_step_iff_administrative sourceRules head supplied _).trans (ask_step_iff head supplied observed)

end Mettapedia.OSLF.Framework.SortedTypedInstruments
