import Mettapedia.Logic.ASP.Checker

/-!
# Controls for the stable-model checker and enumerator

Every value below is computed by the kernel (`decide`), from the executable
definitions of `Checker`, and read as a statement about stable models through
`mem_stableModels` and `stable_iff_mem_stableModels`.

* `p :- not q.` has exactly the stable model `{p}`.
* `p :- not p.` has no stable model and no supported model.
* `p :- not q. q :- not p.` has exactly `{p}` and `{q}`; it is tight, and its
  supported models are its stable models (Fages).
* `p :- p.` has only `{}` as a stable model, although `{p}` is a supported model;
  it is not tight, so Fages' theorem does not apply to it.
* `p :- q. q :- p. r :- not p.` is not tight: `{p, q}` is a loop. `{p, q}` is a
  supported model without external support, so it is not stable; the only stable
  model is `{r}`.
* `p :- q. q :- p. p :- not r. r :- not p.` has the same loop, now with external
  support through `p :- not r`; `{p, q}` and `{r}` are its stable models.
* The enumerator's data output, over natural-number atom identifiers.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP.CheckerControls

open Program

/-- Three atoms. -/
inductive Atom
  | p
  | q
  | r
  deriving DecidableEq, Repr

open Atom

theorem no_stable_of_stableModels_eq_empty {P : Program Atom} (none : P.stableModels = ∅) (S : Set Atom) :
    ¬ P.Stable S := by
  intro h
  obtain ⟨M, hM, _⟩ := (P.stable_iff_mem_stableModels S).mp h
  rw [none] at hM
  exact Finset.notMem_empty M hM

/-! ## `p :- not q.` -/

def onlyP : Program Atom := [⟨p, [], [q]⟩]

theorem onlyP_stableModels : onlyP.stableModels = {{p}} := by decide

theorem onlyP_stable_iff (S : Set Atom) : onlyP.Stable S ↔ S = {p} := by
  rw [stable_iff_mem_stableModels, onlyP_stableModels]
  simp [eq_comm]

/-! ## `p :- not p.` -/

def liar : Program Atom := [⟨p, [], [p]⟩]

theorem liar_stableModels : liar.stableModels = ∅ := by decide

theorem liar_supportedModels : liar.supportedModels = ∅ := by decide

theorem liar_no_stable (S : Set Atom) : ¬ liar.Stable S :=
  no_stable_of_stableModels_eq_empty liar_stableModels S

/-! ## `p :- not q. q :- not p.` -/

def choice : Program Atom := [⟨p, [], [q]⟩, ⟨q, [], [p]⟩]

theorem choice_stableModels : choice.stableModels = {{p}, {q}} := by decide

theorem choice_stable_iff (S : Set Atom) : choice.Stable S ↔ S = {p} ∨ S = {q} := by
  rw [stable_iff_mem_stableModels, choice_stableModels]
  simp [eq_comm]

theorem choice_tight : choice.Tight := by
  constructor
  intro a
  constructor
  rintro b ⟨r, hr, _, hb⟩
  simp only [choice, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp at hb

/-- Fages, observed: on the tight choice program the supported models are the stable ones. -/
theorem choice_supported_eq_stable : choice.supportedModels = choice.stableModels := by decide

/-! ## `p :- p.` -/

def selfSupport : Program Atom := [⟨p, [p], []⟩]

theorem selfSupport_stableModels : selfSupport.stableModels = {∅} := by decide

theorem selfSupport_supportedModels : selfSupport.supportedModels = {∅, {p}} := by decide

/-- `{p}` supports itself, so it is a supported model, but it is not stable. -/
theorem selfSupport_p : selfSupport.Supported {p} ∧ ¬ selfSupport.Stable {p} := by
  have supported := (selfSupport.isSupported_iff {p}).mp (by decide)
  have notStable : selfSupport.isStable {p} = false := by decide
  refine ⟨by simpa using supported, fun h => ?_⟩
  have := (selfSupport.isStable_iff {p}).mpr (by simpa using h)
  rw [notStable] at this
  exact Bool.false_ne_true this

theorem selfSupport_loop : selfSupport.IsLoop {p} := (selfSupport.loopCheck_iff _).mp (by decide)

/-- Fages' hypothesis matters: `p :- p.` is not tight, and `{p}` is supported but not stable. -/
theorem selfSupport_not_tight : ¬ selfSupport.Tight :=
  fun tight => selfSupport.not_isLoop_of_tight tight _ selfSupport_loop

/-- Fages, applied: on the tight choice program stability is supportedness. -/
theorem choice_stable_iff_supported (M : Set Atom) : choice.Stable M ↔ choice.Supported M :=
  choice.stable_iff_supported_of_tight choice_tight M

/-! ## A loop without external support: `p :- q. q :- p. r :- not p.` -/

def unsupportedLoop : Program Atom := [⟨p, [q], []⟩, ⟨q, [p], []⟩, ⟨r, [], [p]⟩]

theorem unsupportedLoop_stableModels : unsupportedLoop.stableModels = {{r}} := by decide

theorem unsupportedLoop_supportedModels : unsupportedLoop.supportedModels = {{r}, {p, q}} := by decide

theorem unsupportedLoop_loop : unsupportedLoop.IsLoop {p, q} :=
  (unsupportedLoop.loopCheck_iff _).mp (by decide)

theorem unsupportedLoop_not_tight : ¬ unsupportedLoop.Tight :=
  fun tight => unsupportedLoop.not_isLoop_of_tight tight _ unsupportedLoop_loop

/-- The witness of `unsupported_loop`: `{p, q}` is true and has no external support. -/
theorem unsupportedLoop_no_external : ¬ unsupportedLoop.ExternalSupport ↑({p, q} : Finset Atom) {p, q} := by
  rw [← externalSupportFin_iff]
  decide

/-! ## The same loop with external support: `p :- q. q :- p. p :- not r. r :- not p.` -/

def supportedLoop : Program Atom := [⟨p, [q], []⟩, ⟨q, [p], []⟩, ⟨p, [], [r]⟩, ⟨r, [], [p]⟩]

theorem supportedLoop_stableModels : supportedLoop.stableModels = {{p, q}, {r}} := by decide

theorem supportedLoop_loop : supportedLoop.IsLoop {p, q} :=
  (supportedLoop.loopCheck_iff _).mp (by decide)

theorem supportedLoop_external : supportedLoop.ExternalSupport ↑({p, q} : Finset Atom) {p, q} :=
  (supportedLoop.externalSupportFin_iff _ _).mp (by decide)

/-- Not every set of atoms is a loop: `{p, r}` is not strongly connected by positive edges. -/
theorem supportedLoop_not_loop : ¬ supportedLoop.IsLoop {p, r} := by
  rw [← loopCheck_iff]
  decide

/-! ## The data output over atom identifiers -/

/-- `0 :- not 1. 1 :- not 0. 2 :- 0. 2 :- 1.` -/
def numbered : Program ℕ := [⟨0, [], [1]⟩, ⟨1, [], [0]⟩, ⟨2, [0], []⟩, ⟨2, [1], []⟩]

theorem numbered_stableModelList : numbered.stableModelList = [[0, 2], [1, 2]] := by decide

end Mettapedia.Logic.ASP.CheckerControls
