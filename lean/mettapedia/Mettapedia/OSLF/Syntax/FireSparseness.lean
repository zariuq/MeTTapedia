import Mettapedia.OSLF.Syntax.ContextualSplitting

/-!
# Events are sparse, and the sparseness is the content

Section 17.4 of Finding Mind says that `Fire` is much smaller than `Split`: most
cuts are inert, because nothing at that cut matches the left-hand side of any
rule, and that this sparseness "is not a defect of the construction but the
content of it -- it is what makes the difference between a state in which
anything might happen and a state in which specific things might."

That claim is exhibited here in its sharpest form: one state, two cuts, the same
term reconstructed by both, one of them an available event and the other inert.
So `Fire` is a proper sub-bundle of `Split` over a single fibre, which is the
strongest version of the claim -- sparseness is not a fact about which states are
reachable but about which cuts of one state are live.
-/

namespace Mettapedia.OSLF.Binding

open Mettapedia.OSLF.Binding.NoCovering
open Mettapedia.OSLF.Binding.Collapsing

set_option autoImplicit false

namespace FireSparse

/-- The state: an output of a name on a channel, ready to fire. -/
def state : Term sig3 [] Srt3.pr :=
  Term.op (S := sig3) Op3.out (.cons t3 (.cons nilS .nil))

/-- The cut at the root: everything is the redex, nothing is context. -/
def liveCut : Splitting sig3 [] Srt3.pr where
  carrier := Srt3.pr
  ctxt := Term.var Var.zero
  redex := state

/-- A cut inside the same term: the output's payload is the redex and the output
itself is the context. -/
def deadCut : Splitting sig3 [] Srt3.pr where
  carrier := Srt3.pr
  ctxt := Term.op (S := sig3) Op3.out
    (.cons (weaken t3) (.cons (Term.var Var.zero) .nil))
  redex := nilS

/-- **Both cuts reconstruct the same state.**  So the two are points of one
fibre of `plug`, and any difference between them is a difference between cuts
rather than between states. -/
theorem same_state : plug liveCut = state ∧ plug deadCut = state := by
  constructor
  · rfl
  · rfl

/-! ## One of them is an event -/

theorem liveCut_fires : Fire P4 liveCut :=
  ⟨rfl, nilS, fires⟩

/-! ## The other is inert

Nothing at that cut matches the rule's left-hand side, and the reason is
structural: every source of a root step is headed by the rule's own head
constructor, and the payload is not. -/

/-- Is this term headed by the output former? -/
def isOut : Term sig3 [] Srt3.pr → Bool
  | .op Op3.out _ => true
  | _ => false

/-- **Every source of a root step is headed by the rule's head constructor.** -/
theorem rootStep_source_is_out {t u : Term sig3 [] Srt3.pr}
    (h : RootStep P4 t u) : isOut t = true := by
  obtain ⟨I, hl, -⟩ := h
  rw [← hl]
  simp [isOut, P4, lhs4, instantiate, instantiateArgs, bind, bindArgs, liftSub]

theorem nilS_is_not_out : isOut nilS = false := by decide

/-- **The payload cut is inert.** -/
theorem deadCut_is_inert : ¬ Fire P4 deadCut := by
  rintro ⟨h, b, hb⟩
  have hout : isOut nilS = true := by
    have := rootStep_source_is_out hb
    simpa [deadCut, castTermSort] using this
  rw [nilS_is_not_out] at hout
  exact absurd hout (by decide)

/-- **Fire is a proper sub-bundle over a single fibre.**  One state, two cuts
that reconstruct it, one live and one dead: the sparseness is a property of the
cuts, not of the states. -/
theorem fire_is_sparse :
    plug liveCut = plug deadCut ∧ Fire P4 liveCut ∧ ¬ Fire P4 deadCut := by
  refine ⟨?_, liveCut_fires, deadCut_is_inert⟩
  rw [same_state.1, same_state.2]

/-- **And the live cut is a direction the state can move in**: firing there is a
step of the generated relation, with the context side untouched. -/
theorem liveCut_is_a_direction :
    Step P4 (plug (⟨P4.sort, Term.var Var.zero, state⟩ : Splitting sig3 [] Srt3.pr))
      (residual (P := P4) (Term.var Var.zero) nilS) :=
  fire_gives_a_step (P := P4) (Term.var Var.zero) state nilS fires rfl

end FireSparse

end Mettapedia.OSLF.Binding
