import Mettapedia.GSLT.Core.MultiRewrite
import Mettapedia.OSLF.Framework.RelyPossiblyScheme

/-!
# Rely environments of a multi-rewrite window

The hole is one source of a `WindowWitness`.  Its *partners* are the other
sources of that same window — the minimal enabling context (Leifer–Milner),
not the leftover document `pre ++ suf`.

This is a `RelyFrame`.  The modality is still the scheme
`∀ e, rely e → ∃ w, Fit w e t ∧ B (out w)`.  The kernel step remains
`Nonempty WindowWitness`; rely reads the witness, not `GSLT.Step`.

Rho COMM is not claimed: that needs a join on a shared channel.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.MultiRewriteRely

open Mettapedia.GSLT
open Mettapedia.GSLT.MultiRewrite
open Mettapedia.OSLF.Framework.RelyPossiblyScheme

/-- A window together with a chosen source as the hole. -/
structure Focus (M : MultiRewriteTheory)
    (source target : List M.Term) where
  witness : MultiRewriteTheory.WindowWitness M source target
  hole : Fin witness.sources.length

namespace Focus

/-- Partners of the hole: the other sources of the same rule window. -/
def partners {M : MultiRewriteTheory} {source target : List M.Term}
    (focus : Focus M source target) : List M.Term :=
  focus.witness.sources.eraseIdx focus.hole.val

/-- The leftover document around the window, which is *not* the rely
environment. -/
def rest {M : MultiRewriteTheory} {source target : List M.Term}
    (focus : Focus M source target) : List M.Term :=
  focus.witness.pre ++ focus.witness.suf

def holeTerm {M : MultiRewriteTheory} {source target : List M.Term}
    (focus : Focus M source target) : M.Term :=
  focus.witness.sources.get focus.hole

end Focus

/-- Rely frame of an ordered multi-rewrite theory.  Carrier is the hole
term; environments are partner lists; outputs are the rule targets. -/
def windowFrame (M : MultiRewriteTheory) : RelyFrame where
  Carrier := M.Term
  Env := List M.Term
  Out := List M.Term
  Wit := Σ source target : List M.Term, Focus M source target
  Fit := fun wit env hole =>
    env = Focus.partners wit.2.2 ∧ hole = Focus.holeTerm wit.2.2
  out := fun wit => wit.2.2.witness.targets

/-! ## Canary on `meet`: `[false, true] → [true]` -/

def meetWitness :
    MultiRewriteTheory.WindowWitness meet [false, true] [true] where
  pre := []
  sources := [false, true]
  targets := [true]
  suf := []
  source_eq := Pointwise.refl meet.equations.refl [false, true]
  target_eq := Pointwise.refl meet.equations.refl [true]
  rule := meet_fires
  real := Or.inl (List.cons_ne_nil _ _)

def meetFocus0 : Focus meet [false, true] [true] where
  witness := meetWitness
  hole := ⟨0, Nat.succ_pos 1⟩

theorem meet_partners_are_the_other_source :
    Focus.partners meetFocus0 = [true] :=
  rfl

theorem meet_rest_is_empty :
    Focus.rest meetFocus0 = [] :=
  rfl

theorem meet_hole_is_false :
    Focus.holeTerm meetFocus0 = false :=
  rfl

/-- Partners are not the leftover document.  On this window they happen
to differ as lists (`[true]` vs `[]`); in general they are different
roles even when both are nonempty. -/
theorem partners_are_not_rest :
    Focus.partners meetFocus0 ≠ Focus.rest meetFocus0 := by
  intro h
  cases h

theorem meet_fit :
    (windowFrame meet).Fit ⟨[false, true], [true], meetFocus0⟩
      [true] false :=
  ⟨rfl, rfl⟩

/-- The induced step: placing `false` under partners `[true]` yields `[true]`. -/
theorem meet_rely_step :
    (windowFrame meet).step [true] false [true] :=
  ⟨⟨[false, true], [true], meetFocus0⟩, meet_fit, rfl⟩

#print axioms meet_partners_are_the_other_source
#print axioms partners_are_not_rest
#print axioms meet_rely_step
#print axioms RelyFrame.modality_iff_diamond

end Mettapedia.OSLF.Framework.MultiRewriteRely
