/-
# The draft's two congruences, and what transfers to them

Every report in this lane has carried the same caveat: the mechanized `Cong` is
closed under parallel composition and nothing else, so it is the
*parallel-structural* congruence and strictly weaker than the draft's, which is a
least congruence closed under every former together with a **separate name
equivalence** retaining one equation. And every report has added the same
remark — that results proved with the smaller relation are robust to enlarging
it, because they are proved with the smaller one.

That remark was prose for eighteen reports. This file makes it a theorem, and
mechanizes the pair it is about.

## The pair

`ProcCong` and `NameCong` are mutually recursive, and they have to be. A process
congruence closed under the atom formers needs its name arguments related, and a
name is a quoted process — so name equivalence is process congruence plus the one
equation the draft retains:

```
    NameCong.dropQuote :  ⌜drop x⌝  ≡_N  x
```

In this syntax a name position carries its quoted process directly, so `⌜drop x⌝`
*is* the term `ev x`, and the retained equation reads `NameCong (ev x) x`. The
equation the draft **deletes** — `drop ⌜P⌝ ≃ P`, the one `defect` shows
collapses the calculus — is not here and must not be added.

## What transfers, and why

`StepMinus.mono` and `Step.mono`: reduction is monotone in its congruence
parameter. So every reachability result in this lane — the defect, the gate,
the distributor, both encodings, the translation's release, the compilers'
traces — holds verbatim for `ProcCong` and for `NameCong`.
`stepMinus_procCong_of_cong` and friends are the instances.

That is the source-faithfulness statement for the positive half of the lane, and
it is one short induction rather than an argument.

## What does not transfer, precisely

`cong_components` and `cong_names` are theorems *about* the parallel-structural
relation, and `CongruenceScope.lean` already shows they fail under closure at
atom arguments. So the inversion-based results — inertness, the linearity
theorems, `cost_not_saturated` — are about `Cong` specifically. That is a
statement about which relation those results characterize, not a gap in them.

`tags` is the invariant that makes the boundary provable in the other direction.
`ProcCong` preserves the multiset of top-level atom *tags* — an `mm` stays an
`mm` however its names are rewritten — while `NameCong` does not, because the
retained equation relates a one-atom soup to an arbitrary one. So:

```
    Cong  ⊊  ProcCong  ⊊  NameCong
```

with both inclusions proved and both strict, the first witnessed by the atom
argument `CongruenceScope` already isolated and the second by the retained
equation itself.
-/
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.CongruenceScope

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb

/-! ## The mutually recursive pair -/

mutual

/-- The draft's structural congruence: the monoid laws on parallel composition,
closed under **every** former, with name arguments related by name
equivalence. -/
inductive ProcCong : Comb → Comb → Prop where
  | refl (p : Comb) : ProcCong p p
  | symm {p q : Comb} : ProcCong p q → ProcCong q p
  | trans {p q r : Comb} : ProcCong p q → ProcCong q r → ProcCong p r
  | parNil (p : Comb) : ProcCong (par p nil) p
  | parComm (p q : Comb) : ProcCong (par p q) (par q p)
  | parAssoc (p q r : Comb) : ProcCong (par (par p q) r) (par p (par q r))
  | parCong {p p' q q' : Comb} :
      ProcCong p p' → ProcCong q q' → ProcCong (par p q) (par p' q')
  | mmCong {a a' b b' : Comb} :
      NameCong a a' → NameCong b b' → ProcCong (mm a b) (mm a' b')
  | ddCong {a a' b b' c c' : Comb} :
      NameCong a a' → NameCong b b' → NameCong c c' →
      ProcCong (dd a b c) (dd a' b' c')
  | kkCong {a a' : Comb} : NameCong a a' → ProcCong (kk a) (kk a')
  | fwCong {a a' b b' : Comb} :
      NameCong a a' → NameCong b b' → ProcCong (fw a b) (fw a' b')
  | blCong {a a' b b' : Comb} :
      NameCong a a' → NameCong b b' → ProcCong (bl a b) (bl a' b')
  | brCong {a a' b b' : Comb} :
      NameCong a a' → NameCong b b' → ProcCong (br a b) (br a' b')
  | syCong {a a' b b' c c' : Comb} :
      NameCong a a' → NameCong b b' → NameCong c c' →
      ProcCong (sy a b c) (sy a' b' c')
  | evCong {a a' : Comb} : NameCong a a' → ProcCong (ev a) (ev a')
  | qqCong {a a' p p' : Comb} :
      NameCong a a' → NameCong p p' → ProcCong (qq a p) (qq a' p')
  | consParCong {a a' b b' c c' : Comb} :
      NameCong a a' → NameCong b b' → NameCong c c' →
      ProcCong (consPar a b c) (consPar a' b' c')
  | consMsgCong {a a' b b' c c' : Comb} :
      NameCong a a' → NameCong b b' → NameCong c c' →
      ProcCong (consMsg a b c) (consMsg a' b' c')
  | consDupCong {a a' b b' c c' e e' : Comb} :
      NameCong a a' → NameCong b b' → NameCong c c' → NameCong e e' →
      ProcCong (consDup a b c e) (consDup a' b' c' e')
  | consSynCong {a a' b b' c c' e e' : Comb} :
      NameCong a a' → NameCong b b' → NameCong c c' → NameCong e e' →
      ProcCong (consSyn a b c e) (consSyn a' b' c' e')

/-- The draft's name equivalence: process congruence, since a name is a quoted
process, together with the one equation the draft retains — the quotation of a
drop is the name dropped.  The converse identification is deliberately absent;
`defect` is why. -/
inductive NameCong : Comb → Comb → Prop where
  | ofProc {a b : Comb} : ProcCong a b → NameCong a b
  | dropQuote (x : Comb) : NameCong (ev x) x
  | symm {a b : Comb} : NameCong a b → NameCong b a
  | trans {a b c : Comb} : NameCong a b → NameCong b c → NameCong a c

end

theorem NameCong.refl (a : Comb) : NameCong a a := .ofProc (ProcCong.refl a)

/-! ## The parallel-structural congruence is contained in it -/

/-- **Everything the mechanized relation identifies, the draft's does too.** -/
theorem procCong_of_cong {p q : Comb} (h : Cong p q) : ProcCong p q := by
  induction h with
  | refl p => exact .refl p
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | parNil p => exact .parNil p
  | parComm p q => exact .parComm p q
  | parAssoc p q r => exact .parAssoc p q r
  | parLeft q _ ih => exact .parCong ih (.refl q)
  | parRight p _ ih => exact .parCong (.refl p) ih

theorem nameCong_of_cong {p q : Comb} (h : Cong p q) : NameCong p q :=
  .ofProc (procCong_of_cong h)

/-! ## Reduction is monotone in its congruence -/

/-- **Monotonicity.**  Enlarging the congruence can only add reductions, so
every reachability result proved with a smaller relation holds for a larger
one. -/
theorem StepMinus.mono {C D : Comb → Comb → Prop} (h : ∀ a b, C a b → D a b) :
    ∀ {p q : Comb}, StepMinus C p q → StepMinus D p q := by
  intro p q step
  induction step with
  | duplicate b c v hc => exact .duplicate b c v (h _ _ hc)
  | discard v hc => exact .discard v (h _ _ hc)
  | forward b v hc => exact .forward b v (h _ _ hc)
  | bindOut b v hc => exact .bindOut b v (h _ _ hc)
  | bindIn b v hc => exact .bindIn b v (h _ _ hc)
  | synchronise b c v hc => exact .synchronise b c v (h _ _ hc)
  | opening p hc => exact .opening p (h _ _ hc)
  | release b p hc => exact .release b p (h _ _ hc)
  | parLeft r _ ih => exact .parLeft r ih
  | congruent hc _ hc' ih => exact .congruent (h _ _ hc) ih (h _ _ hc')

theorem Step.mono {C D : Comb → Comb → Prop} (h : ∀ a b, C a b → D a b) :
    ∀ {p q : Comb}, Step C p q → Step D p q := by
  intro p q step
  induction step with
  | ofMinus hmin => exact .ofMinus (StepMinus.mono h hmin)
  | buildPar c p q h₁ h₂ => exact .buildPar c p q (h _ _ h₁) (h _ _ h₂)
  | buildMsg c u v h₁ h₂ => exact .buildMsg c u v (h _ _ h₁) (h _ _ h₂)
  | buildDup e p q r h₁ h₂ h₃ =>
      exact .buildDup e p q r (h _ _ h₁) (h _ _ h₂) (h _ _ h₃)
  | buildSyn e p q r h₁ h₂ h₃ =>
      exact .buildSyn e p q r (h _ _ h₁) (h _ _ h₂) (h _ _ h₃)
  | parLeft r _ ih => exact .parLeft r ih
  | congruent hc _ hc' ih => exact .congruent (h _ _ hc) ih (h _ _ hc')

/-- **Every reachability result in this lane holds for the draft's
congruence.**  The defect, the gate, the distributor, the encodings, the
translation's release and both compilers' traces are all reductions, and
reduction is monotone. -/
theorem stepMinus_procCong_of_cong {p q : Comb} (step : StepMinus Cong p q) :
    StepMinus ProcCong p q :=
  StepMinus.mono (fun _ _ h => procCong_of_cong h) step

theorem step_procCong_of_cong {p q : Comb} (step : Step Cong p q) :
    Step ProcCong p q :=
  Step.mono (fun _ _ h => procCong_of_cong h) step

theorem step_nameCong_of_cong {p q : Comb} (step : Step Cong p q) :
    Step NameCong p q :=
  Step.mono (fun _ _ h => nameCong_of_cong h) step

/-! ## Both inclusions are strict -/

/-- The top-level atom tags of a soup: what former each running atom is, with
its name arguments ignored. -/
inductive Tag where
  | message | duplicate | discard | forward | bindIn | bindOut
  | synchronise | opening | storage
  | buildPar | buildMsg | buildDup | buildSyn
  deriving DecidableEq

def tags : Comb → Multiset Tag
  | nil => 0
  | par p q => tags p + tags q
  | mm _ _ => {Tag.message}
  | dd _ _ _ => {Tag.duplicate}
  | kk _ => {Tag.discard}
  | fw _ _ => {Tag.forward}
  | bl _ _ => {Tag.bindIn}
  | br _ _ => {Tag.bindOut}
  | sy _ _ _ => {Tag.synchronise}
  | ev _ => {Tag.opening}
  | qq _ _ => {Tag.storage}
  | consPar _ _ _ => {Tag.buildPar}
  | consMsg _ _ _ => {Tag.buildMsg}
  | consDup _ _ _ _ => {Tag.buildDup}
  | consSyn _ _ _ _ => {Tag.buildSyn}

/-- **Process congruence preserves the atom tags.**  It may rewrite a name
however name equivalence allows, but an `mm` stays an `mm`.  This is the
invariant `cong_components` is to the smaller relation. -/
theorem procCong_tags : ∀ {p q : Comb}, ProcCong p q → tags p = tags q
  | _, _, .refl _ => rfl
  | _, _, .symm h => (procCong_tags h).symm
  | _, _, .trans h₁ h₂ => (procCong_tags h₁).trans (procCong_tags h₂)
  | _, _, .parNil _ => by simp [tags]
  | _, _, .parComm _ _ => by simp only [tags]; exact add_comm _ _
  | _, _, .parAssoc _ _ _ => by simp only [tags]; exact add_assoc _ _ _
  | _, _, .parCong h₁ h₂ => by
      simp only [tags, procCong_tags h₁, procCong_tags h₂]
  | _, _, .mmCong _ _ => rfl
  | _, _, .ddCong _ _ _ => rfl
  | _, _, .kkCong _ => rfl
  | _, _, .fwCong _ _ => rfl
  | _, _, .blCong _ _ => rfl
  | _, _, .brCong _ _ => rfl
  | _, _, .syCong _ _ _ => rfl
  | _, _, .evCong _ => rfl
  | _, _, .qqCong _ _ => rfl
  | _, _, .consParCong _ _ _ => rfl
  | _, _, .consMsgCong _ _ _ => rfl
  | _, _, .consDupCong _ _ _ _ => rfl
  | _, _, .consSynCong _ _ _ _ => rfl

/-- **`Cong` is strictly smaller than `ProcCong`.**  The witness is the atom
argument `CongruenceScope` isolated: rewriting inside a name is invisible to the
draft's congruence and visible to the mechanized one. -/
theorem cong_lt_procCong :
    ProcCong (kk (par nil nil)) (kk nil) ∧ ¬ Cong (kk (par nil nil)) (kk nil) :=
  ⟨.kkCong (.ofProc (.parNil nil)),
    cong_not_closed_under_atom_arguments.2⟩

/-- **`ProcCong` is strictly smaller than `NameCong`.**  The witness is the
retained equation itself: it relates a one-atom soup to the empty one, which no
tag-preserving relation can do. -/
theorem procCong_lt_nameCong :
    NameCong (ev nil) nil ∧ ¬ ProcCong (ev nil) nil := by
  refine ⟨.dropQuote nil, ?_⟩
  intro h
  have counted := procCong_tags h
  simp [tags] at counted

/-- **The deleted equation is still absent.**  Nothing above identifies the
opening of a quotation with the process quoted, which is the equation `defect`
shows collapses the calculus.  `NameCong` relates `ev x` to `x` — the quotation
of a drop to the name dropped — and that is the opposite direction. -/
theorem retained_equation_is_the_safe_direction (x : Comb) :
    NameCong (ev x) x ∧ tags (ev x) = {Tag.opening} :=
  ⟨.dropQuote x, rfl⟩

end Mettapedia.Languages.ProcessCalculi.RhoCombinators
