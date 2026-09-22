/-
# The source's own reduction, and why the simulation must be behavioural

Full abstraction has been carried as a remaining step for many turns with an
estimate attached, and the estimate was misleading: the statement was not
available. `Src` had a syntax and a translation but **no reduction relation**, so
"the translation is fully abstract" had nothing to be fully abstract with
respect to.

This file supplies the missing semantics — de Bruijn substitution, the
communication rule, and the source's structural congruence — and then records
what trying to state the simulation immediately shows.

## The obstruction

The natural first attempt at a simulation lemma is that translation commutes
with substitution:

```
    ⟦P{⌜Q⌝/y}⟧  =  ⟦P⟧ with the proxy for y instantiated by ⟦Q⟧
```

**This is false, and `substitution_duplicates_code` exhibits why.** The
translation is offset-sensitive: a term compiled at offset `k` allocates slots
from `k`. So a name substituted at *two* occurrences is translated *twice*, at
two different slot ranges, and the two copies are genuinely different terms —
`translate_inp_offset_injective` proves the offsets are recoverable from the
output, so no two of them coincide.

The target does not do that. It routes **one** name to both occurrences; the
payload's code is stored once and shared. So the target implements substitution
*with sharing* while syntactic substitution copies, and the two agree
behaviourally rather than syntactically.

That is not a defect on either side. It is the reflective mechanism working:
storing a continuation as a name is precisely what avoids copying it. But it
does mean the cheap syntactic route to full simulation is closed, and that any
simulation argument has to be behavioural from the start. Recording that is
worth more than an optimistic estimate, because it says which kind of argument
is needed rather than how much of one is left.

## What is here

`Src.subst` and `SrcName.substName` substitute a name for the bound index,
descending under an input with the level raised. The substituted name is
required to be closed — which it is in the communication rule, where it is the
quotation of a running process — so no shifting is needed, and that restriction
is stated rather than assumed silently.

`SrcCong` is the source's structural congruence: the monoid laws on parallel
composition, closed under composition. `SrcStep` is reduction: the
communication rule, closure under parallel composition, and closure under the
congruence.

`FullyAbstract` states the property, with the target equivalence taken relative
to translated contexts as the draft requires. It is a definition, not a theorem;
nothing below proves it.
-/
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Compositionality

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb

/-! ## Substitution -/

mutual

/-- Substitute a closed name for the bound index `level`, descending under an
input with the level raised.  The substituted name must be closed; in the
communication rule it is the quotation of a running process, so it is. -/
def Src.subst (name : SrcName) (level : ℕ) : Src → Src
  | Src.nil => Src.nil
  | Src.par p q => Src.par (p.subst name level) (q.subst name level)
  | Src.out subject body =>
      Src.out (SrcName.substName name level subject) (body.subst name level)
  | Src.inp subject body =>
      Src.inp (SrcName.substName name level subject) (body.subst name (level + 1))
  | Src.drop subject => Src.drop (SrcName.substName name level subject)

def SrcName.substName (name : SrcName) (level : ℕ) : SrcName → SrcName
  | SrcName.quote p => SrcName.quote (p.subst name level)
  | SrcName.bvar index => if index = level then name else SrcName.bvar index

end

/-! ## The source's reduction -/

/-- The source's structural congruence: the monoid laws on parallel
composition. -/
inductive SrcCong : Src → Src → Prop where
  | refl (p : Src) : SrcCong p p
  | symm {p q : Src} : SrcCong p q → SrcCong q p
  | trans {p q r : Src} : SrcCong p q → SrcCong q r → SrcCong p r
  | parNil (p : Src) : SrcCong (Src.par p Src.nil) p
  | parComm (p q : Src) : SrcCong (Src.par p q) (Src.par q p)
  | parAssoc (p q r : Src) :
      SrcCong (Src.par (Src.par p q) r) (Src.par p (Src.par q r))
  | parCong {p p' q q' : Src} :
      SrcCong p p' → SrcCong q q' → SrcCong (Src.par p q) (Src.par p' q')

/-- The source's reduction: communication, closed under parallel composition and
under the congruence. -/
inductive SrcStep : Src → Src → Prop where
  | comm (subject : SrcName) (body payload : Src) :
      SrcStep (Src.par (Src.inp subject body) (Src.out subject payload))
        (body.subst (SrcName.quote payload) 0)
  | parLeft {p p' : Src} (q : Src) : SrcStep p p' → SrcStep (Src.par p q) (Src.par p' q)
  | parRight (p : Src) {q q' : Src} : SrcStep q q' → SrcStep (Src.par p q) (Src.par p q')
  | congruent {p p' q' q : Src} :
      SrcCong p p' → SrcStep p' q' → SrcCong q' q → SrcStep p q

/-- Multi-step source reduction. -/
inductive SrcReaches : Src → Src → Prop where
  | refl (p : Src) : SrcReaches p p
  | tail {p q r : Src} : SrcReaches p q → SrcStep q r → SrcReaches p r
  | congruent {p q : Src} : SrcCong p q → SrcReaches p q
  | trans {p q r : Src} : SrcReaches p q → SrcReaches q r → SrcReaches p r

/-! ## The statement of full abstraction -/

/-- Two source terms are equated by encoded contexts when, in every source
context, their translations are behaviourally indistinguishable in the target.
This is the observer class the draft restricts to: contexts in the image of the
translation, rather than arbitrary target contexts. -/
def EquatedByEncodedContexts (s : Comb)
    (targetEquivalence : Comb → Comb → Prop) (first second : Src) : Prop :=
  ∀ (ctx : SrcContext) (proxies : List Comb) (offset : ℕ),
    targetEquivalence (translate s proxies (ctx.fill first) offset)
      (translate s proxies (ctx.fill second) offset)

/-- Two source terms are equated by the source's own contexts. -/
def EquatedBySourceContexts (sourceEquivalence : Src → Src → Prop)
    (first second : Src) : Prop :=
  ∀ ctx : SrcContext, sourceEquivalence (ctx.fill first) (ctx.fill second)

/-- **Full abstraction relative to encoded contexts.**  A definition, not a
theorem: nothing below proves it, and the obstruction recorded next says which
kind of argument it needs. -/
def FullyAbstract (s : Comb) (sourceEquivalence : Src → Src → Prop)
    (targetEquivalence : Comb → Comb → Prop) : Prop :=
  ∀ first second : Src,
    EquatedBySourceContexts sourceEquivalence first second
      ↔ EquatedByEncodedContexts s targetEquivalence first second

/-! ## Why the simulation cannot be syntactic -/

/-- The offset a compiled input allocated is recoverable from its output, so no
two offsets give the same term. -/
theorem translate_inp_offset_injective (s : Comb) (proxies : List Comb)
    (subject : SrcName) (body : Src) {first second : ℕ}
    (h : translate s proxies (Src.inp subject body) first
        = translate s proxies (Src.inp subject body) second) :
    first = second := by
  simp only [translate] at h
  injection h with hleft _
  injection hleft with _ hmid _
  exact slot_injective s hmid

/-- A source term whose bound name is dropped twice. -/
def droppedTwice : Src :=
  Src.par (Src.drop (SrcName.bvar 0)) (Src.drop (SrcName.bvar 0))

/-- A payload whose translation allocates slots, so that translating it at two
offsets gives two different terms. -/
def allocatingPayload : Src := Src.inp (SrcName.quote Src.nil) Src.nil

/-- **Translation and substitution do not commute on the nose.**  Substituting a
name at two occurrences translates the payload **twice**, at two different slot
ranges, and the two copies are different terms.  The target does not copy: it
routes one name and stores the code once.

So the two agree behaviourally, not syntactically, and a simulation argument has
to be behavioural from the start.  That is the reflective mechanism working —
storing a continuation as a name is exactly what avoids copying it — and it is
why the cheap route to full simulation is closed. -/
theorem substitution_duplicates_code (s : Comb) :
    translate s [] (droppedTwice.subst (SrcName.quote allocatingPayload) 0) 0
        = par (ev (translate s [] allocatingPayload 0))
          (ev (translate s [] allocatingPayload 5))
      ∧ translate s [] allocatingPayload 0 ≠ translate s [] allocatingPayload 5 := by
  refine ⟨rfl, ?_⟩
  intro h
  exact absurd (translate_inp_offset_injective s [] (SrcName.quote Src.nil) Src.nil h)
    (by decide)

/-- The communication rule does fire in the source, so the semantics above is
not vacuous. -/
theorem srcStep_comm_example :
    SrcStep (Src.par (Src.inp (SrcName.quote Src.nil) (Src.drop (SrcName.bvar 0)))
        (Src.out (SrcName.quote Src.nil) Src.nil))
      (Src.drop (SrcName.quote Src.nil)) :=
  SrcStep.comm (SrcName.quote Src.nil) (Src.drop (SrcName.bvar 0)) Src.nil

end Mettapedia.Languages.ProcessCalculi.RhoCombinators
