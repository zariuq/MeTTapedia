import Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFreshConnections
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu

/-!
# Lexical fresh: the rho reading of lifetimes

A closure is a replicated server on its channel `f`: each call is a replica.
Lybech's (2024) two encodings separate the lifetimes:

* per call, `!(f?x. (ν z) P)`: each replica restricts its own `z`;
* per closure, `(ν z) !(f?x. P)`: all replicas share one `z`;

and a crossing name `{$t}` is a free name of the server, an existing name every
replica communicates on.

On the model these are theorems (`LexicalFreshConnections`):
`per_call_replicas` (two activations copy each own slot to different names and
leave every other name, a crossing one included, unchanged) and
`per_closure_shared` (a hoisted closure renames nothing).  On the corpus:
`ListsCorpus.lifetime_separation` (row 1: per call answers
`(Pair (g 1) (g 2))`, per closure no answer, the shared name conflicting) and
`LexicalFreshCorpus.body_only_translated` (row H1: `(new ($hole) $hole)` is a
restriction per call, the untranslated hole one existing name).

Against Mettapedia's rho formalization (checked 2026-10-06):
* the canonical calculus (`RhoCalculus.Reduction`) has `Comm` and no
  restriction or replication;
* the reference-encoding delta (`RhoCalculus.Extended`, `rhoCalcExtended`) has
  `PNew` with scope extrusion (`Extrude`) and `NewCong`, and no replication;
* the derived layer (`RhoCalculus.DerivedRepNu`) has the administrative heads
  `PReplicate`, with `rep_unfold`, and `PNu`, with no rule
  (`no_direct_core_step_from_PNu`).

So the per-call encoding runs there: one unfolding spawns a replica that carries
its own restrictions (`perCall_unfold`).  The per-closure encoding does not:
every derived step of a restricted server is a core step, and the replication
under the restriction cannot unfold (`perClosure_steps_are_core`).  No rule of
the formalization allocates a name, so the name each replica restricts is a
binder, not a fresh name; the allocation is the model's activation
(`fresh_per_call`).
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFreshRho

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu

/-- `n` nested restrictions. -/
def nuN : ℕ → Pattern → Pattern
  | 0, p => p
  | n + 1, p => .apply "PNu" [nuN n p]

/-- A closure on channel `f` per call: `!(f?x. (ν z₁ … zₙ) body)`. -/
def perCallRho (f : Pattern) (n : ℕ) (body : Pattern) : Pattern :=
  .apply "PReplicate" [.apply "PInput" [f, .lambda none (nuN n body)]]

/-- A closure on channel `f` per closure: `(ν z₁ … zₙ) !(f?x. body)`. -/
def perClosureRho (f : Pattern) (n : ℕ) (body : Pattern) : Pattern :=
  nuN n (.apply "PReplicate" [.apply "PInput" [f, .lambda none body]])

/-- **Per call, each replica restricts its own names**: one unfolding of the
replication spawns the replica `f?x. (ν z…) body`, its restrictions inside,
beside the server. -/
def perCall_unfold (f : Pattern) (n : ℕ) (body : Pattern) :
    perCallRho f n body ⇝ᵈ
      .collection .hashBag [.apply "PInput" [f, .lambda none (nuN n body)], perCallRho f n body] none :=
  .rep_unfold

/-- **Per closure, the replication does not unfold under the restriction**: a
derived step of `(ν z) !P` is a core step (no `rep_unfold`, no bag congruence
applies to a restriction), and no core rule reduces `PNu` directly
(`no_direct_core_step_from_PNu`). -/
theorem perClosure_steps_are_core (f : Pattern) (n : ℕ) (body : Pattern) {q : Pattern}
    (h : perClosureRho f (n + 1) body ⇝ᵈ q) : Nonempty (perClosureRho f (n + 1) body ⇝ q) := by
  generalize hs : perClosureRho f (n + 1) body = s at h
  cases h with
  | core hc => exact ⟨hs ▸ hc⟩
  | rep_unfold => simp [perClosureRho, nuN] at hs
  | par _ => simp [perClosureRho, nuN] at hs
  | par_any _ => simp [perClosureRho, nuN] at hs

/-- The two encodings differ as terms whenever a name is restricted: the
restrictions sit inside the replication, or outside it. -/
theorem perCall_ne_perClosure (f : Pattern) (n : ℕ) (body : Pattern) :
    perCallRho f (n + 1) body ≠ perClosureRho f (n + 1) body := by
  intro h
  simp [perCallRho, perClosureRho, nuN] at h

end Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFreshRho
