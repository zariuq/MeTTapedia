import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.Contractum
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternFragment

/-!
# The program: four rules of the step defined by rule syntax

Each rule has its own declaration frame of unknowns (`RuleSyntax.Rule`), at the contextual frames
of the twin-binder signature with the knowledge of `Knowledge`.

* `commRule`: unknowns `X : ([], nm)`, `K : ([nm, pr], pr)` (second order: a continuation open in
  a name and a process) and `Q : ([], pr)`. Take `input(X, K⟨y, p⟩)` and `output(X, Q)`; make
  `K⟨@Q, Q⟩`.
* `heatRule`: take `bag(A :: R)`; make `A` and `bag R`.
* `clearBagRule`: take `bag []`. `clearZeroRule`: take `0`.
* `program`: these four, fixed before any process is given.

What the syntax says, as theorems:
* the takes are in the tree's structural pattern class (`takes_are_patterns`); the made row of
  communication is not (`made_not_pattern`), and it is never matched, only instantiated;
* the made row under any assignment of the unknowns is the continuation instantiated at the
  received name and process (`made_instantiation`): `bind (received q) b`, the term algebra's own
  substitution. No former of the signature computes anything.
* the canonical opening of a rule is fresh at every state of this frame action
  (`canonical_fresh_here`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Interface.Frames (Frame)

/-! ## The rules' unknowns -/

/-- The unknowns of communication: the channel, the continuation and the payload. -/
inductive CommUnknown where
  | channel
  | body
  | payload
  deriving DecidableEq

/-- The continuation is second order: a process open in a name and its twin. -/
def commArity : CommUnknown → MetaArity sig
  | .channel => ([], .nm)
  | .body => ([.nm, .pr], .pr)
  | .payload => ([], .pr)

/-- The unknowns of heating: the first component and the rest. -/
inductive HeatUnknown where
  | first
  | rest
  deriving DecidableEq

def heatArity : HeatUnknown → MetaArity sig
  | .first => ([], .pr)
  | .rest => ([], .ps)

abbrev commFrame : Frame sig := ⟨CommUnknown, commArity⟩
abbrev heatFrame : Frame sig := ⟨HeatUnknown, heatArity⟩

/-- An observation of a closed process term. -/
abbrev obs {V : Type} {D : V → MetaArity sig} (t : Term (signature sig D) [] .pr) :
    Observation sig D :=
  ⟨[], .pr, t⟩

/-! ## The patterns and the made rows -/

/-- `input(X, K⟨y, p⟩)`. -/
def commInput : Term (signature sig commArity) [] .pr :=
  inputT (generator commArity .channel) (generator commArity .body)

/-- `output(X, Q)`. -/
def commOutput : Term (signature sig commArity) [] .pr :=
  outputT (generator commArity .channel) (generator commArity .payload)

/-- `K⟨@Q, Q⟩`: the continuation applied to the received name and the received process. -/
def commMade : Term (signature sig commArity) [] .pr :=
  .op (.inr (Operator.mk (declaration := commArity) CommUnknown.body))
    (.cons (quoteT (generator commArity .payload)) (.cons (generator commArity .payload) .nil))

/-- `bag(A :: R)`. -/
def heatBag : Term (signature sig heatArity) [] .pr :=
  bagT (pconsT (generator heatArity .first) (generator heatArity .rest))

/-! ## The rules -/

/-- **Communication.** -/
abbrev commRule : RuleSyntax.Rule (RuleSyntax.Contextual.Terms sig) where
  locals := commFrame
  body := { take := [obs commInput, obs commOutput], read := [], tell := [], checks := [],
            produce := [obs commMade] }
  collect := []

/-- **Heating.** -/
abbrev heatRule : RuleSyntax.Rule (RuleSyntax.Contextual.Terms sig) where
  locals := heatFrame
  body := { take := [obs heatBag], read := [], tell := [], checks := [],
            produce := [obs (generator heatArity .first), obs (bagT (generator heatArity .rest))] }
  collect := []

/-- **Clearing the empty bag.** -/
abbrev clearBagRule : RuleSyntax.Rule (RuleSyntax.Contextual.Terms sig) where
  locals := groundFrame
  body := { take := [obs (bagT pnilT)], read := [], tell := [], checks := [], produce := [] }
  collect := []

/-- **Clearing the null process.** -/
abbrev clearZeroRule : RuleSyntax.Rule (RuleSyntax.Contextual.Terms sig) where
  locals := groundFrame
  body := { take := [obs zeroT], read := [], tell := [], checks := [], produce := [] }
  collect := []

/-- **The program**: four rules, fixed before any process is given. -/
def program : RuleSyntax.Program (RuleSyntax.Contextual.Terms sig) :=
  {commRule, heatRule, clearBagRule, clearZeroRule}

theorem mem_program {r : RuleSyntax.Rule (RuleSyntax.Contextual.Terms sig)} :
    r ∈ program ↔ r = commRule ∨ r = heatRule ∨ r = clearBagRule ∨ r = clearZeroRule := by
  simp [program]

theorem commRule_mem : commRule ∈ program := mem_program.mpr (.inl rfl)
theorem heatRule_mem : heatRule ∈ program := mem_program.mpr (.inr (.inl rfl))
theorem clearBagRule_mem : clearBagRule ∈ program := mem_program.mpr (.inr (.inr (.inl rfl)))
theorem clearZeroRule_mem : clearZeroRule ∈ program := mem_program.mpr (.inr (.inr (.inr rfl)))

/-- What a rule takes, read back, and how many rows it makes. -/
def shape (r : RuleSyntax.Rule (RuleSyntax.Contextual.Terms sig)) : List Pattern × Nat :=
  (r.body.take.map fun o => read o.2.2, r.body.produce.length)

/-- The four rules are different. -/
theorem rules_differ :
    commRule ≠ heatRule ∧ commRule ≠ clearBagRule ∧ commRule ≠ clearZeroRule ∧
      heatRule ≠ clearBagRule ∧ heatRule ≠ clearZeroRule ∧ clearBagRule ≠ clearZeroRule := by
  refine ⟨fun same => ?_, fun same => ?_, fun same => ?_, fun same => ?_, fun same => ?_,
    fun same => ?_⟩ <;>
  · have shapes := congrArg shape same
    simp [shape, commRule, heatRule, clearBagRule, clearZeroRule, obs, read, readArgs, build,
      commInput, commOutput, heatBag] at shapes

/-! ## The pattern class -/

open ContextualPatternFragment in
/-- **The takes are in the tree's structural pattern class**: every unknown is applied to distinct
bound variables (the continuation to the two variables its input binds). -/
theorem takes_are_patterns :
    Pattern sig commArity commInput ∧ Pattern sig commArity commOutput ∧
      Pattern sig heatArity heatBag := by
  refine ⟨?_, ?_, ?_⟩
  · exact Pattern.rigid (S := sig) (declaration := commArity) Op.input _
      (.cons _ _ (generator_pattern (S := sig) (declaration := commArity) .channel)
        (.cons _ _ (generator_pattern (S := sig) (declaration := commArity) .body) .nil))
  · exact Pattern.rigid (S := sig) (declaration := commArity) Op.output _
      (.cons _ _ (generator_pattern (S := sig) (declaration := commArity) .channel)
        (.cons _ _ (generator_pattern (S := sig) (declaration := commArity) .payload) .nil))
  · have inner : Pattern sig heatArity
        (pconsT (generator heatArity .first) (generator heatArity .rest)) :=
      Pattern.rigid (S := sig) (declaration := heatArity) Op.pcons _
        (.cons _ _ (generator_pattern (S := sig) (declaration := heatArity) .first)
          (.cons _ _ (generator_pattern (S := sig) (declaration := heatArity) .rest) .nil))
    exact Pattern.rigid (S := sig) (declaration := heatArity) Op.bag _ (.cons _ _ inner .nil)

/-- The continuation is the only second-order unknown. -/
theorem second_order_unknowns :
    (commArity .body).1 = [.nm, .pr] ∧ (commArity .channel).1 = [] ∧
      (commArity .payload).1 = [] ∧ (heatArity .first).1 = [] ∧ (heatArity .rest).1 = [] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **The made row is outside the pattern class**: its continuation is applied to `@Q` and `Q`, not
to bound variables. It is never matched; it is instantiated. -/
theorem made_check_false :
    ContextualPatternFragment.check (S := sig) (declaration := commArity) commMade = false := by
  simp only [ContextualPatternFragment.check, commMade]
  rfl

theorem made_not_pattern : ¬ ContextualPatternFragment.Pattern sig commArity commMade := by
  intro pattern
  have accepted :=
    (ContextualPatternFragment.check_iff (S := sig) (declaration := commArity) commMade).mpr pattern
  rw [made_check_false] at accepted
  exact Bool.false_ne_true accepted

/-! ## Instantiation of the rules' terms -/

section Instantiation

variable {W : Type} {target : W → MetaArity sig}

theorem instantiate_commInput (h : Assignment commArity target) :
    instantiate h commInput = inputT (h .channel) (h .body) :=
  congrArg₂ (fun c b => inputT (D := target) (Γ := []) c b)
    (instantiate_generator h CommUnknown.channel) (instantiate_generator h CommUnknown.body)

theorem instantiate_commOutput (h : Assignment commArity target) :
    instantiate h commOutput = outputT (h .channel) (h .payload) :=
  congrArg₂ (fun c p => outputT (D := target) (Γ := []) c p)
    (instantiate_generator h CommUnknown.channel) (instantiate_generator h CommUnknown.payload)

/-- **The made row under an assignment is the continuation instantiated at the received name and
the received process**: the term algebra's own substitution `bind`, nothing else. -/
theorem made_instantiation (h : Assignment commArity target) :
    instantiate h commMade =
      bind (argsToSub (.cons (quoteT (h .payload)) (.cons (h .payload) .nil))) (h .body) :=
  congrArg (fun q : Term (signature sig target) [] .pr =>
      bind (argsToSub (S := signature sig target) (bs := [.nm, .pr]) (Γ := [])
        (.cons (quoteT q) (.cons q .nil))) (h .body))
    (instantiate_generator h CommUnknown.payload)

theorem instantiate_heatBag (h : Assignment heatArity target) :
    instantiate h heatBag = bagT (pconsT (h .first) (h .rest)) :=
  congrArg₂ (fun p l => bagT (D := target) (Γ := []) (pconsT p l))
    (instantiate_generator h HeatUnknown.first) (instantiate_generator h HeatUnknown.rest)

end Instantiation

/-- At ground assignments the made row is `bind (received q) b`. -/
theorem made_instantiation_ground (h : Grounding commFrame) :
    instantiate h commMade = bind (received (h .payload)) (h .body) :=
  made_instantiation h

/-! ## The step of the program -/

/-- **The step**: `RuleSyntax.step` of `program` at the contextual frames of the twin-binder
signature with the knowledge `knowledge`, occurrences numbered by `ℕ`, firings extending the frame
by declarations. -/
abbrev theStep :=
  RuleSyntax.step knowledge ℕ (RuleSyntax.Contextual.declarations sig) program

/-- States of the step. -/
abbrev State := RuleSyntax.State (RuleSyntax.Contextual.Terms sig) ℕ

/-- Firings of the step at a state. -/
abbrev Firing (s : State) := RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations sig) program s.frame

/-- **The canonical opening is fresh at every state of this frame action.** -/
theorem canonical_fresh_here (s : State) (r : RuleSyntax.Rule (RuleSyntax.Contextual.Terms sig))
    (member : r ∈ program) (selection : Selection ℕ) (seen : List (Finset ℕ)) :
    (RuleSyntax.Contextual.canonical (F := s.frame) r member selection seen).Fresh knowledge s := by
  intro B g h
  obtain ⟨u, state, rule⟩ :=
    RuleSyntax.Contextual.canonical_fresh (S := sig) s r member selection seen B g h
  refine ⟨u, fun t mentioned => ?_, fun t inside => ?_⟩
  · exact (congrArg (fun x => Equal x ((Interface.Frames.contextual sig).act g t))
      (state t mentioned)).mpr (fun _ => obsSimilar_refl _)
  · exact (congrArg (fun x => Equal x ((Interface.Frames.contextual sig).act h t))
      (rule t inside)).mpr (fun _ => obsSimilar_refl _)

#print axioms takes_are_patterns
#print axioms made_not_pattern
#print axioms made_instantiation
#print axioms canonical_fresh_here

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation
