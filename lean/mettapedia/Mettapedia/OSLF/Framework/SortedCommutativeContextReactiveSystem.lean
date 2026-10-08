import Mettapedia.OSLF.Syntax.SortedCommutativeContextCategory

/-!
# Complete RPOs in the actual sorted raw equation/context category

The earned full and faithful normalization transports every competing RPO
apex, complete mediator triangle and uniqueness equation. All origin-based
spans in the independently formed raw quotient category consequently have
RPOs. Literal IPO bisimulation for any actual reaction family is preserved by
every raw context class, including designated Cut and other free frames.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.SortedCommutative

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors
open Mettapedia.GSLT.RelativePushout
open Mettapedia.GSLT.RedexRelativeCongruence

universe u v

variable {signature : Signature.{u,v}} {Parallel : signature.Srt → Prop}

theorem raw_idemPushout_iff_normalized
    {root first second target : RawObject signature Parallel}
    {agent : root ⟶ first} {redex : root ⟶ second}
    {left : first ⟶ target} {right : second ⟶ target} (square : agent ≫ left = redex ≫ right) :
    IsIdemPushout agent redex left right square ↔
      IsIdemPushout (normalizeFunctor.map agent) (normalizeFunctor.map redex)
        (normalizeFunctor.map left) (normalizeFunctor.map right)
        (by rw [← normalizeFunctor.map_comp, square, normalizeFunctor.map_comp]) := by
  refine ⟨preserves_idemPushout normalizeFunctor normalizeObject_surjective square,
    reflects_idemPushout normalizeFunctor square⟩

theorem raw_redex_relativePushouts {first second : RawObject signature Parallel}
    (agent : (.origin : RawObject signature Parallel) ⟶ first)
    (redex : (.origin : RawObject signature Parallel) ⟶ second) :
    HasRelativePushouts agent redex := by
  apply reflects_hasRelativePushouts normalizeFunctor normalizeObject_surjective
  exact mixed_redex_relativePushouts (normalizeFunctor.map agent) (normalizeFunctor.map redex)

theorem raw_bisimulation_congruence
    (rules : ReactionRule (.origin : RawObject signature Parallel) → Prop)
    {source target : RawObject signature Parallel}
    {first second : (.origin : RawObject signature Parallel) ⟶ source}
    (related : IPOBisimilar rules first second) (context : source ⟶ target) :
    IPOBisimilar rules (first ≫ context) (second ≫ context) :=
  ipoBisimilar_comp (fun _ agent rule _ => raw_redex_relativePushouts agent rule.redex) related context

theorem raw_hasRelativePushouts {first second : signature.Srt}
    (firstValue : Class signature Parallel first) (secondValue : Class signature Parallel second) :
    HasRelativePushouts (C := RawObject signature Parallel)
      (RawArrow.value firstValue : (.origin : RawObject signature Parallel) ⟶ .interface first)
      (RawArrow.value secondValue : (.origin : RawObject signature Parallel) ⟶ .interface second) :=
  raw_redex_relativePushouts _ _

end Mettapedia.OSLF.SortedCommutative
