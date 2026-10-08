import Mettapedia.OSLF.Framework.SortedCommutativeOriginalAskFactorization
import Mettapedia.OSLF.Framework.SortedCommutativeSourceFiringComparison

/-!+# Original base reactions cannot supply an ask IPO

The complete factorization through the ask label gives an actual smaller
candidate for the same commuting span. IPO minimality would split the ask
label, contradicting its strictly positive fresh-constructor support.

This excludes every independently authored rule in the original source
category. A rule at its origin also has an explicit smaller candidate. It
does not exclude original rules under a get label, and it does not assume
that ground filling is faithful.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence
open Support

universe u w

variable {Symbols : Type u} {arity : Symbols → Nat} {Origins : Type w}

theorem base_ask_square_not_ipo (constructor : SourceSymbol Symbols)
    (supplied redex : ValueClass arity .base)
    (reaction : ContextClass (signature arity) (Parallel arity) .base (.arguments constructor))
    (square : (RawArrow.value supplied : (.origin : ContextCategory arity) ⟶ .interface .base) ≫
      askLabel constructor = RawArrow.value redex ≫ RawArrow.context reaction) :
    ¬ IsIdemPushout (C := ContextCategory arity)
      (RawArrow.value supplied) (RawArrow.value redex) (askLabel constructor)
      (RawArrow.context reaction) square := by
  have read : reaction.fill redex =
      (contextClassOf (probeContext arity (.ask constructor))).fill supplied :=
    (RawArrow.value.inj square).symm
  obtain ⟨before, inputRead, reactionRead⟩ := ask_reaction_factorization constructor supplied redex reaction read
  let candidate : Candidate (C := ContextCategory arity)
      (RawArrow.value supplied) (RawArrow.value redex) (askLabel constructor)
      (RawArrow.context reaction) :=
    { apex := .interface .base
      inl := 𝟙 (.interface .base : ContextCategory arity)
      inr := RawArrow.context before
      down := askLabel constructor
      comm := (Category.comp_id _).trans (congrArg RawArrow.value inputRead).symm
      fac_left := Category.id_comp _
      fac_right := congrArg RawArrow.context reactionRead.symm }
  intro minimal
  obtain ⟨section_, recovers⟩ := minimal.down_splits candidate
  have support := congrArg arrowObserverCount recovers
  change arrowObserverCount (section_ ≫ askLabel constructor) = 0 at support
  rw [arrowCount_comp, askLabel_support] at support
  omega

theorem origin_ask_square_not_ipo (constructor : SourceSymbol Symbols)
    (supplied : ValueClass arity .base)
    (reaction : (.origin : ContextCategory arity) ⟶ .interface (.arguments constructor))
    (square : (RawArrow.value supplied : (.origin : ContextCategory arity) ⟶ .interface .base) ≫
      askLabel constructor = 𝟙 (.origin : ContextCategory arity) ≫ reaction) :
    ¬ IsIdemPushout (C := ContextCategory arity)
      (RawArrow.value supplied) (𝟙 (.origin : ContextCategory arity))
      (askLabel constructor) reaction square := by
  let candidate : Candidate (C := ContextCategory arity)
      (RawArrow.value supplied) (𝟙 (.origin : ContextCategory arity))
      (askLabel constructor) reaction :=
    { apex := .interface .base
      inl := 𝟙 (.interface .base : ContextCategory arity)
      inr := RawArrow.value supplied
      down := askLabel constructor
      comm := by simp only [Category.comp_id, Category.id_comp]
      fac_left := Category.id_comp _
      fac_right := square.trans (Category.id_comp reaction) }
  intro minimal
  obtain ⟨section_, recovers⟩ := minimal.down_splits candidate
  have support := congrArg arrowObserverCount recovers
  change arrowObserverCount (section_ ≫ askLabel constructor) = 0 at support
  rw [arrowCount_comp, askLabel_support] at support
  omega

theorem mapped_original_ask_not_ipo (constructor : SourceSymbol Symbols)
    (original : ReactionRule (.origin : Source.SourceCategory (arity := arity)))
    (supplied : ValueClass arity .base)
    (reaction : (Source.mapReactionRule original).codomain ⟶ .interface (.arguments constructor))
    (square : (RawArrow.value supplied : (.origin : ContextCategory arity) ⟶ .interface .base) ≫
      askLabel constructor = (Source.mapReactionRule original).redex ≫ reaction) :
    ¬ IsIdemPushout (C := ContextCategory arity)
      (RawArrow.value supplied) (Source.mapReactionRule original).redex
      (askLabel constructor) reaction square := by
  cases original with
  | mk codomain redex reactum =>
    cases codomain with
    | origin =>
      cases redex with
      | identity => exact origin_ask_square_not_ipo constructor supplied reaction square
    | interface sort =>
      cases redex with
      | value redex =>
        cases reaction with
        | context reaction => exact base_ask_square_not_ipo constructor supplied _ reaction square

theorem source_rules_do_not_fire_under_ask
    (sourceRules : ReactionRule (.origin : Source.SourceCategory (arity := arity)) → Prop)
    (constructor : SourceSymbol Symbols) (supplied : ValueClass arity .base)
    (result : (.origin : ContextCategory arity) ⟶ .interface (.arguments constructor)) :
    ¬ ActIPO (Source.mappedRules sourceRules) (askLabel constructor) (RawArrow.value supplied) result := by
  rintro ⟨rule, ⟨original, admitted, rfl⟩, reaction, square, minimal, _output⟩
  exact mapped_original_ask_not_ipo constructor original supplied reaction square minimal

theorem combined_ask_step_iff_administrative
    (sourceRules : ReactionRule (.origin : Source.SourceCategory (arity := arity)) → Prop)
    (constructor : SourceSymbol Symbols) (supplied : ValueClass arity .base)
    (result : (.origin : ContextCategory arity) ⟶ .interface (.arguments constructor)) :
    ActIPO (fun rule => rules arity Origins rule ∨ Source.mappedRules sourceRules rule)
        (askLabel constructor) (RawArrow.value supplied) result ↔
      ActIPO (rules arity Origins) (askLabel constructor) (RawArrow.value supplied) result := by
  constructor
  · rintro ⟨rule, admitted, reaction, square, minimal, output⟩
    rcases admitted with administrative | original
    · exact ⟨rule, administrative, reaction, square, minimal, output⟩
    · exact (source_rules_do_not_fire_under_ask sourceRules constructor supplied result
        ⟨rule, original, reaction, square, minimal, output⟩).elim
  · rintro ⟨rule, admitted, reaction, square, minimal, output⟩
    exact ⟨rule, Or.inl admitted, reaction, square, minimal, output⟩

theorem combined_ask_source_step_iff
    (sourceRules : ReactionRule (.origin : Source.SourceCategory (arity := arity)) → Prop)
    (constructor : SourceSymbol Symbols) (supplied : Source.ValueClass arity)
    (result : (.origin : ContextCategory arity) ⟶ .interface (.arguments constructor)) :
    ActIPO (fun rule => rules arity Origins rule ∨ Source.mappedRules sourceRules rule)
        (askLabel constructor) (RawArrow.value (Source.classEmbedding supplied)) result ↔
      ∃ _suppliedOrigin : Origins, ∃ arguments : Fin (sourceArity arity constructor) → Source.Value arity,
        supplied = classOf (Source.sourceNode constructor arguments) ∧
          result = RawArrow.value (classOf (bundle arity constructor
            (fun position => Source.embed (arguments position)))) :=
  (combined_ask_step_iff_administrative (Origins := Origins) sourceRules constructor _ result).trans
    (ask_source_step_iff (Origins := Origins) constructor supplied result)

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments
