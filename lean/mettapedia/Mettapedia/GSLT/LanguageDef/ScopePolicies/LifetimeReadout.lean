import Mettapedia.GSLT.LanguageDef.ScopePolicies.Translators

/-!
# Lifetime and readout: can explicit text express them?

## Readout

No.  The readout is not in the elaborated term: a text elaborates to the same
term under both readouts (`elabCfg_readout`), and the two judgments differ in
the discipline that the evaluator runs under (`elabState_readout`).  A
translator keeps the judgment up to the static equivalence of the core, which
keeps the discipline; so there is no translator between two policies of
different readouts, on any domain with a program
(`not_translates_across_readout`).  A snapshot readout is a different reduction
of the core, not an authoring of it.

What this does not rule out: a map of programs that is hosting without keeping
the judgment.  None is built, and none is refuted.

## Lifetime

Not on the nose.  Under the per-closure lifetime a lambda's own slots are
bound by the scope that creates the closure, and at the top of a form they
stay free, with the owner they had: the position of the lambda's body.  In the
per-call elaboration of explicit text every free slot is a slot of the form's
root (`freeNames_elabQ_explicit`).  So the per-closure elaboration of
`(lam z $y){}` is the per-call elaboration of no explicit text, under any
ownership policy (`perClosure_not_explicit`).

Up to a renaming of that slot it is: `(lam z $y){$y}` shares the slot with the
root, and its per-call elaboration differs from the per-closure one in the
owner of that one slot (`perClosure_up_to_owner`).  The static equivalence of
the core does not contain that renaming, so this is a statement about two
terms, not a translator.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ScopePolicies

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.IdSlot

universe u v

variable {S : Type u} {X : Type v} [DecidableEq X]

/-! ## Readout -/

/-- **The readout is not in the elaborated term.** -/
theorem elabCfg_readout (ownership : Ownership) (lifetime : Lifetime) (readout readout' : Readout)
    (root : Owner) (t : Src S X) :
    elabCfg ⟨ownership, lifetime, readout⟩ root t = elabCfg ⟨ownership, lifetime, readout'⟩ root t :=
  rfl

/-- **Two readouts, one program: the same equations and the same query, run
under two disciplines.** -/
theorem elabState_readout (ownership : Ownership) (lifetime : Lifetime) (u : X) (unit : S)
    (text : Program S X) :
    ∃ (prog : S → Option (Tm S (Slot X))) (query : Tm S (Slot X)),
      elabState ⟨ownership, lifetime, .reference⟩ u unit (.program text) = .run .static prog query ∧
      elabState ⟨ownership, lifetime, .snapshot⟩ u unit (.program text) =
        .run .copyAtCall prog query :=
  ⟨_, _, rfl, rfl⟩

/-- A translator keeps the discipline. -/
theorem Translates.disc {c c' : Config} {u : X} {unit : S} {domain : Program S X → Prop}
    {convert : Program S X → Program S X} (translates : Translates c c' u unit domain convert)
    {text : Program S X} (inside : domain text) : c'.disc = c.disc :=
  Option.some.inj (coreEquiv_discipline (translates text inside))

/-- **No translator between two readouts**, on any domain with a program:
explicit text cannot express a readout. -/
theorem not_translates_across_readout (ownership ownership' : Ownership)
    (lifetime lifetime' : Lifetime) (readout readout' : Readout) (differ : readout ≠ readout')
    (u : X) (unit : S) (domain : Program S X → Prop) (convert : Program S X → Program S X)
    {text : Program S X} (inside : domain text) :
    ¬ Translates ⟨ownership, lifetime, readout⟩ ⟨ownership', lifetime', readout'⟩ u unit domain
      convert := by
  intro translates
  have same := translates.disc inside
  cases readout <;> cases readout' <;> first
    | exact differ rfl
    | cases same

/-- Positive, for comparison: within one readout the identity translates a
policy into itself. -/
theorem translates_same_readout (c : Config) (u : X) (unit : S) :
    Translates c c u unit (fun _ : Program S X => True) fun text => text :=
  Translates.id c u unit _

/-! ## Lifetime -/

/-- **In the per-call elaboration of explicit text, every free slot is a slot
of the environment.**  (Through lexical fresh and its annotated text:
`elabLF_explicit`, `elabLF_eq_slotOf`, `Ann.freeNames_slotOf`.) -/
theorem freeNames_elabQ_explicit {t : Src S X} (written : explicit t = true)
    (admissible : t.patsNewFree = true) (env : REnv X) (pos : Owner) (n : Nm (Slot X))
    (free : n ∈ freeNames (elabQ env pos t)) : ∃ y, n = .src (env y, y) := by
  rw [← elabLF_explicit t env [] pos written, elabLF_eq_slotOf t [] pos pos env pos] at free
  obtain ⟨y, -, same⟩ :=
    Ann.freeNames_slotOf _ env pos n (Ann.Open.of_WF (annLF_WF t [] pos pos admissible)) free
  exact ⟨y, same⟩

/-- The per-closure elaboration of `(lam z $y){}`: the lambda owns nothing any
more, and its slot is free, with the owner it had. -/
theorem perClosure_lam (ownership : Ownership) (readout : Readout) (z y : X) :
    elabCfg ⟨ownership, .perClosure, readout⟩ [] (.lam z (some []) (.sv y) : Src S X) =
      .lam (parName z) [] (.var (.src ([0], y))) := by
  cases ownership <;> simp [elabCfg, elabCfgX, elabForm, elabQ, elabMS, elabLF, elabEC, crossOwn,
    Src.uses, Src.direct, Src.sharedUp, hoistOwn, slotVar, REnv.update]

/-- **The per-closure lifetime is not expressed by explicit per-call text, on
the nose.**  No explicit text without a `new` block on a pattern's spine
elaborates per call, under any ownership policy, to the per-closure elaboration
of `(lam z $y){}`. -/
theorem perClosure_not_explicit (ownership ownership' : Ownership) (readout readout' : Readout)
    (z y : X) {t : Src S X} (written : explicit t = true) (admissible : t.patsNewFree = true) :
    elabCfg ⟨ownership', .perCall, readout'⟩ [] t ≠
      elabCfg ⟨ownership, .perClosure, readout⟩ [] (.lam z (some []) (.sv y)) := by
  intro same
  rw [perClosure_lam] at same
  have toQ : elabCfg ⟨ownership', .perCall, readout'⟩ [] t = elabQ (fun _ => []) [] t :=
    elabForm_explicit ownership' .queryWide [] written
  rw [toQ] at same
  have free : (Nm.src (([0] : Owner), y) : Nm (Slot X)) ∈
      freeNames (elabQ (fun _ => []) [] t) := by
    rw [same]
    simp [freeNames, ownKey]
  obtain ⟨y', isRoot⟩ := freeNames_elabQ_explicit written admissible _ _ _ free
  injection isRoot with pair
  have owners := congrArg Prod.fst pair
  cases owners

/-- **Up to the owner of one slot it is.**  `(lam z $y){$y}` shares the slot
with the root; its per-call elaboration is the per-closure elaboration of
`(lam z $y){}` with the slot `([0], y)` named `([], y)`. -/
theorem perClosure_up_to_owner (ownership : Ownership) (readout : Readout) (z y : X) :
    elabCfg ⟨ownership, .perCall, readout⟩ [] (.lam z (some [y]) (.sv y) : Src S X) =
      .lam (parName z) [] (.var (.src ([], y))) := by
  cases ownership <;> simp [elabCfg, elabCfgX, elabForm, elabQ, elabMS, elabLF, elabEC, crossOwn,
    Src.uses, Src.direct, Src.sharedUp, slotVar, REnv.update]

#print axioms not_translates_across_readout
#print axioms freeNames_elabQ_explicit
#print axioms perClosure_not_explicit
#print axioms perClosure_up_to_owner

end Mettapedia.GSLT.LanguageDef.ScopePolicies
