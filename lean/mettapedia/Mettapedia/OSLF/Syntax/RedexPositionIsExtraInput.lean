import Mettapedia.OSLF.Syntax.BindingSignature

/-!
# A redex position is not determined by the rule it sits in

Chapter 19 of Finding Mind (draft 26) describes the generator's input twice.
Section 7.6 calls the classifying theory "the presentation-independent form in
which the type-theoretic construction of Chapter 19 takes its input".  Section
19.3 then says the algorithm "takes as input a theory in the classifying form
of Section 7.6" and adds that, as "the crucial extra datum, it also tracks
redex positions", a position being a chosen subterm occurrence of a left-hand
side.  Section 19.4 places the generated modality at the carrier of that
position, and Section 19.5 adds one structural type former per term former.

These cannot both hold.  This module exhibits the obstruction concretely: one
left-hand side over a two-sorted signature carries two redex positions whose
carriers are different sorts.  A construction that reads the carrier therefore
cannot be a function of the rule alone, still less of the relation the rule
generates, so the choice of position is genuine extra input and must be
supplied as part of the data.

Two controls accompany the separation.  The first shows the plugging equation
is not vacuous.  The second shows the plugging equation is also not *enough*:
a context that ignores its hole satisfies it with an arbitrary redex, so
"choosing a subterm occurrence" needs an occurrence condition in addition to
`K[t] = L`.
-/

namespace Mettapedia.OSLF.Binding

set_option autoImplicit false

namespace RedexPositionWitness

inductive Srt where
  | nm
  | pr
  deriving DecidableEq, Repr

inductive Op : Srt → Type where
  | out : Op Srt.pr
  | aName : Op Srt.nm

/-- A two-sorted fragment: `out` takes a name and a process and yields a
process; `aName` is a name constant. -/
abbrev sig : Signature where
  Srt := Srt
  Op := Op
  arity := fun {_} o => match o with
    | .out => [([], Srt.nm), ([], Srt.pr)]
    | .aName => []

/-- Context `n : nm, p : pr`. -/
abbrev G : Ctx sig := [Srt.nm, Srt.pr]

/-- The left-hand side `out(n, p)`. -/
def lhs : Term sig G Srt.pr :=
  Term.op (S := sig) Op.out (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil))

/-- Position at the name argument: hole of sort `nm`, redex `n`. -/
def namePosition : RedexPosition sig G Srt.pr lhs where
  carrier := Srt.nm
  ctxt := Term.op (S := sig) Op.out (.cons (.var .zero) (.cons (.var (.succ (.succ .zero))) .nil))
  redex := .var .zero
  plugs := rfl

/-- Position at the process argument: hole of sort `pr`, redex `p`. -/
def procPosition : RedexPosition sig G Srt.pr lhs where
  carrier := Srt.pr
  ctxt := Term.op (S := sig) Op.out (.cons (.var (.succ .zero)) (.cons (.var .zero) .nil))
  redex := .var (.succ .zero)
  plugs := rfl

/-- Both positions decompose **the same** left-hand side. -/
theorem same_lhs :
    inst namePosition.ctxt namePosition.redex
      = inst procPosition.ctxt procPosition.redex := by
  rw [namePosition.plugs, procPosition.plugs]

/-- **The carrier is not a function of the left-hand side.**  The generated
modality is a type former *at the carrier*, so a construction that reads the
carrier cannot factor through the rewrite rule alone: the choice of position is
genuine extra input. -/
theorem carrier_not_determined_by_lhs :
    namePosition.carrier ≠ procPosition.carrier := by
  intro h
  have hns : Srt.nm = Srt.pr := h
  exact Srt.noConfusion hns

/-- One left-hand side, two positions, two carriers. -/
theorem positions_differ_on_the_same_lhs :
    ∃ P₁ P₂ : RedexPosition sig G Srt.pr lhs, P₁.carrier ≠ P₂.carrier :=
  ⟨namePosition, procPosition, carrier_not_determined_by_lhs⟩

/-! ### Negative control: `plugs` carries content -/

/-- Taking the whole term to sit in the hole at the root, with `p` as the
redex, does not decompose `lhs`.  So `RedexPosition` is not inhabited by
arbitrary sort-correct context/redex pairs: the plugging equation is doing
work. -/
theorem not_every_pair_is_a_position :
    inst (Γ := G) (c := Srt.pr) (s := Srt.pr) (.var .zero) (.var (.succ .zero))
      ≠ lhs := by
  intro h
  simp [inst, bind, extend, lhs] at h

/-! ### A gap the plugging equation does not close -/

/-- A context that ignores its hole, with `p` in the hole. -/
def vacuousPosition : RedexPosition sig G Srt.pr lhs where
  carrier := Srt.pr
  ctxt := weaken lhs
  redex := .var (.succ .zero)
  plugs := inst_weaken lhs _

/-- The same context, with a different redex — still a position. -/
def vacuousPosition' : RedexPosition sig G Srt.pr lhs where
  carrier := Srt.pr
  ctxt := weaken lhs
  redex := lhs
  plugs := inst_weaken lhs _

/-- **The plugging equation alone does not say a subterm was selected.**  Two
positions share a context and decompose the same left-hand side while choosing
different redexes, because that context never uses its hole.  So a faithful
reading of "choosing a subterm occurrence" needs an occurrence condition on top
of `K[t] = L`; the equation by itself admits vacuous positions whose redex is
entirely unconstrained. -/
theorem redex_unconstrained_at_a_vacuous_position :
    vacuousPosition.ctxt = vacuousPosition'.ctxt
      ∧ vacuousPosition.redex ≠ vacuousPosition'.redex := by
  refine ⟨rfl, ?_⟩
  intro h
  simp [vacuousPosition, vacuousPosition', lhs] at h

/-! ### The separation survives the occurrence condition

Strengthening `RedexPosition` to demand that the hole occur exactly once
removes the vacuous positions, but does not restore determinacy of the carrier:
both positions above are linear. -/

/-- The name position, with the hole occurring exactly once. -/
def nameLinear : LinearRedexPosition sig G Srt.pr lhs where
  toRedexPosition := namePosition
  linear := rfl

/-- The process position, with the hole occurring exactly once. -/
def procLinear : LinearRedexPosition sig G Srt.pr lhs where
  toRedexPosition := procPosition
  linear := rfl

/-- **The carrier is still not determined once vacuous positions are excluded.**
So the extra input is not an artefact of a permissive definition: it is the
choice of occurrence itself. -/
theorem linear_positions_differ_on_the_same_lhs :
    ∃ P₁ P₂ : LinearRedexPosition sig G Srt.pr lhs, P₁.carrier ≠ P₂.carrier :=
  ⟨nameLinear, procLinear, carrier_not_determined_by_lhs⟩

/-- The vacuous position is excluded: its context never uses its hole. -/
theorem vacuousPosition_not_linear :
    holeCount vacuousPosition.ctxt ≠ 1 := by
  rw [show vacuousPosition.ctxt = weaken lhs from rfl, holeCount_weaken]
  exact Nat.zero_ne_one

/-- And the linearity condition is what does the excluding: the two vacuous
positions of the previous section share a context whose hole count is `0`. -/
theorem vacuous_contexts_have_no_occurrence :
    holeCount vacuousPosition.ctxt = 0 ∧ holeCount vacuousPosition'.ctxt = 0 :=
  ⟨holeCount_weaken lhs, holeCount_weaken lhs⟩

end RedexPositionWitness

end Mettapedia.OSLF.Binding
