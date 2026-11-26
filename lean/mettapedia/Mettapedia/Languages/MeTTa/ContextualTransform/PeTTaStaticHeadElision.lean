import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaResumptionLowerBound
import Mathlib.Computability.Halting

/-!
# Exact static elision of a suspended constructor read

There is one pending answer, one symbol and at most one installation. The
consumer is given a finite bound at run time. It performs a bounded, primitive
recursive computation and installs the equation for `S` if that computation
finds a result. Reusing the original constructor must preserve the next
answer for **every** bound the consumer could receive.

Safety of this particular optimization is co-halting. A total sound analysis
can recognize restricted cases, and every effective sound recognizer misses
some safe programs in this family. Bounded evaluation terminates on each
individual input. The quantifier over the consumer's possible inputs is
essential to the reduction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStaticHeadElision

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Nat.Partrec (Code)
open PeTTaResumptionLowerBound (model source source_trace wrap pending)
open PeTTaWorldSemantics (eval)

/-- Install an equation between two equal alternatives of the same entered
generator, then run its actual residual. The initial output is discarded. -/
def afterEditor (x : Atom) (install : Bool) : List Atom × Bool :=
  match eval (model [x, x]) source false with
  | .done world => ([], world)
  | .answer _ world resume =>
    let action := if install then .edit true else .value (.symbol "true")
    (((eval (model []) action).bind fun _ => resume) world).drain

theorem afterEditor_eq (x : Atom) (install : Bool) :
    afterEditor x install = ([wrap install x], install) := by
  unfold afterEditor
  rw [source_trace]
  cases install <;> rfl

/-- The criterion compares the actual answer and final world with running
the same editor and retaining the original output head. -/
def SafeForAll (x : Atom) (installs : Nat → Bool) : Prop :=
  ∀ bound, afterEditor x (installs bound) = ([wrap false x], installs bound)

theorem safeForAll_iff (x : Atom) (installs : Nat → Bool) :
    SafeForAll x installs ↔ ¬ ∃ bound, installs bound = true := by
  constructor
  · intro safe ⟨bound, found⟩
    have same := safe bound
    simp [afterEditor_eq, found, wrap] at same
  · intro none bound
    cases found : installs bound with
    | false => exact afterEditor_eq x false
    | true => exact (none ⟨bound, found⟩).elim

/-- Mathlib's bounded universal evaluator measures an evaluation bound,
which is independent of SWI instruction counts and wall time. -/
def installsAt (editor : Code) (bound : Nat) : Bool :=
  (Code.evaln bound editor 0).isSome

theorem installsAt_primitive_recursive :
    Primrec fun p : Code × Nat => installsAt p.1 p.2 :=
  Primrec.option_isSome.comp
    (Code.primrec_evaln.comp ((Primrec.snd.pair Primrec.fst).pair (Primrec.const 0)))

theorem some_install_iff_halts (editor : Code) :
    (∃ bound, installsAt editor bound = true) ↔ (editor.eval 0).Dom := by
  constructor
  · rintro ⟨bound, found⟩
    obtain ⟨output, result⟩ := Option.isSome_iff_exists.mp found
    exact Part.dom_iff_mem.mpr ⟨output, Code.evaln_sound (Option.mem_def.mpr result)⟩
  · intro halted
    obtain ⟨output, result⟩ := Part.dom_iff_mem.mp halted
    obtain ⟨bound, found⟩ := Code.evaln_complete.mp result
    exact ⟨bound, Option.isSome_iff_exists.mpr ⟨output, Option.mem_def.mp found⟩⟩

def SafeToHoist (editor : Code) : Prop := SafeForAll (.symbol "Z") (installsAt editor)

theorem safeToHoist_iff_nonhalting (editor : Code) :
    SafeToHoist editor ↔ ¬ (editor.eval 0).Dom :=
  (safeForAll_iff _ _).trans (not_congr (some_install_iff_halts editor))

theorem safeToHoist_not_re : ¬ REPred SafeToHoist :=
  fun recognized => ComputablePred.halting_problem_not_re 0
    (recognized.of_eq safeToHoist_iff_nonhalting)

theorem exact_elision_undecidable : ¬ ComputablePred SafeToHoist :=
  fun decision => safeToHoist_not_re decision.to_re

theorem sound_recognizer_misses_safe_editor (accept : Code → Prop)
    (effective : REPred accept) (sound : ∀ code, accept code → SafeToHoist code) :
    ∃ code, SafeToHoist code ∧ ¬ accept code := by
  classical
  by_contra allFound
  apply safeToHoist_not_re
  exact effective.of_eq fun code => ⟨sound code, fun safe =>
    Classical.byContradiction fun missed => allFound ⟨code, safe, missed⟩⟩

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStaticHeadElision
