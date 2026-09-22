/-
# A step is a redex replaced in place

`Inertness.lean` inverts reduction far enough to prove absences: a step implies
a matching pair in the bag.  That is enough to show a term inert, but not enough
to say *what* a step did, because it does not recover the residual.

This file supplies the full inversion.  A `RuleInstance` names a rule together
with the terms filling it, and carries the two terms that rule relates:

```
    redexTerm     the participants, composed in parallel
    reactumTerm   what replaces them
    Valid         the name-equivalence side conditions the rule demands
```

`step_iff_redex` then says a step is exactly: pick a valid rule instance, find
it in the soup beside some context, and replace it by its reactum leaving that
context alone.  Because the congruence is component equality, "find it beside a
context" is stated with `Cong` and needs no arithmetic on multisets.

This is the shape a bag reactive system wants — a rule's redex beside a reaction
context becoming its reactum beside the same context — so the same
decomposition that pins down what a step did is what the relative-pushout
analysis consumes.
-/
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.NormalForm

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb

/-- A rule of the calculus together with the terms filling it.  The primed names
are the subjects the speaking participant uses, which the rule requires to be
name-equivalent to the ones the listener uses. -/
inductive RuleInstance where
  | duplicate (a a' b c v : Comb)
  | discard (a a' v : Comb)
  | forward (a a' b v : Comb)
  | bindOut (a a' b v : Comb)
  | bindIn (a a' b v : Comb)
  | synchronise (a a' b c v : Comb)
  | opening (a a' p : Comb)
  | release (a a' b p : Comb)
  | buildPar (a a' b b' c p q : Comb)
  | buildMsg (a a' b b' c u v : Comb)
  | buildDup (a a' b b' c c' e p q r : Comb)
  | buildSyn (a a' b b' c c' e p q r : Comb)
  deriving DecidableEq

namespace RuleInstance

/-- The participants the instance consumes, composed in parallel. -/
def redexTerm : RuleInstance → Comb
  | duplicate a a' b c v => par (dd a b c) (mm a' v)
  | discard a a' v => par (kk a) (mm a' v)
  | forward a a' b v => par (fw a b) (mm a' v)
  | bindOut a a' b v => par (br a b) (mm a' v)
  | bindIn a a' b v => par (bl a b) (mm a' v)
  | synchronise a a' b c v => par (sy a b c) (mm a' v)
  | opening a a' p => par (ev a) (mm a' p)
  | release a a' b p => par (fw a b) (qq a' p)
  | buildPar a a' b b' c p q => par (consPar a b c) (par (mm a' p) (mm b' q))
  | buildMsg a a' b b' c u v => par (consMsg a b c) (par (mm a' u) (mm b' v))
  | buildDup a a' b b' c c' e p q r =>
      par (consDup a b c e) (par (mm a' p) (par (mm b' q) (mm c' r)))
  | buildSyn a a' b b' c c' e p q r =>
      par (consSyn a b c e) (par (mm a' p) (par (mm b' q) (mm c' r)))

/-- What replaces the participants. -/
def reactumTerm : RuleInstance → Comb
  | duplicate _ _ b c v => par (mm b v) (mm c v)
  | discard _ _ _ => nil
  | forward _ _ b v => mm b v
  | bindOut _ _ b v => fw b v
  | bindIn _ _ b v => fw v b
  | synchronise _ _ b c _ => fw b c
  | opening _ _ p => p
  | release _ _ b p => mm b p
  | buildPar _ _ _ _ c p q => mm c (par p q)
  | buildMsg _ _ _ _ c u v => mm c (mm u v)
  | buildDup _ _ _ _ _ _ e p q r => mm e (dd p q r)
  | buildSyn _ _ _ _ _ _ e p q r => mm e (sy p q r)

/-- The name-equivalence side conditions the rule demands.  A router needs its
one subject matched; a constructor needs every child's subject matched, which is
why it cannot fire until all of them have arrived. -/
def Valid : RuleInstance → Prop
  | duplicate a a' _ _ _ => Cong a a'
  | discard a a' _ => Cong a a'
  | forward a a' _ _ => Cong a a'
  | bindOut a a' _ _ => Cong a a'
  | bindIn a a' _ _ => Cong a a'
  | synchronise a a' _ _ _ => Cong a a'
  | opening a a' _ => Cong a a'
  | release a a' _ _ => Cong a a'
  | buildPar a a' b b' _ _ _ => Cong a a' ∧ Cong b b'
  | buildMsg a a' b b' _ _ _ => Cong a a' ∧ Cong b b'
  | buildDup a a' b b' c c' _ _ _ _ => Cong a a' ∧ Cong b b' ∧ Cong c c'
  | buildSyn a a' b b' c c' _ _ _ _ => Cong a a' ∧ Cong b b' ∧ Cong c c'

/-- A valid instance is a step of its own participants. -/
theorem toStep : ∀ {ri : RuleInstance}, ri.Valid → Step Cong ri.redexTerm ri.reactumTerm
  | duplicate _ _ b c v, h => Step.ofMinus (StepMinus.duplicate b c v h)
  | discard _ _ v, h => Step.ofMinus (StepMinus.discard v h)
  | forward _ _ b v, h => Step.ofMinus (StepMinus.forward b v h)
  | bindOut _ _ b v, h => Step.ofMinus (StepMinus.bindOut b v h)
  | bindIn _ _ b v, h => Step.ofMinus (StepMinus.bindIn b v h)
  | synchronise _ _ b c v, h => Step.ofMinus (StepMinus.synchronise b c v h)
  | opening _ _ p, h => Step.ofMinus (StepMinus.opening p h)
  | release _ _ b p, h => Step.ofMinus (StepMinus.release b p h)
  | buildPar _ _ _ _ c p q, h => Step.buildPar c p q h.1 h.2
  | buildMsg _ _ _ _ c u v, h => Step.buildMsg c u v h.1 h.2
  | buildDup _ _ _ _ _ _ e p q r, h => Step.buildDup e p q r h.1 h.2.1 h.2.2
  | buildSyn _ _ _ _ _ _ e p q r, h => Step.buildSyn e p q r h.1 h.2.1 h.2.2

end RuleInstance

/-! ## Decomposition -/

/-- **Every step is a redex replaced in place.**  A step decomposes into a valid
rule instance and a context: the instance's participants sit in the soup beside
the context, and the target is the instance's reactum beside the very same
context.  The context is untouched, which is what makes the system a bag
reactive system rather than merely a rewriting relation. -/
theorem step_decompose {t t' : Comb} (h : Step Cong t t') :
    ∃ (ri : RuleInstance) (ctx : Comb),
      ri.Valid ∧ Cong t (par ri.redexTerm ctx) ∧ Cong t' (par ri.reactumTerm ctx) := by
  induction h with
  | ofMinus hmin =>
      induction hmin with
      | duplicate b c v hc =>
          exact ⟨.duplicate _ _ b c v, nil, hc,
            Cong.symm (Cong.parNil _), Cong.symm (Cong.parNil _)⟩
      | discard v hc =>
          exact ⟨.discard _ _ v, nil, hc,
            Cong.symm (Cong.parNil _), Cong.symm (Cong.parNil _)⟩
      | forward b v hc =>
          exact ⟨.forward _ _ b v, nil, hc,
            Cong.symm (Cong.parNil _), Cong.symm (Cong.parNil _)⟩
      | bindOut b v hc =>
          exact ⟨.bindOut _ _ b v, nil, hc,
            Cong.symm (Cong.parNil _), Cong.symm (Cong.parNil _)⟩
      | bindIn b v hc =>
          exact ⟨.bindIn _ _ b v, nil, hc,
            Cong.symm (Cong.parNil _), Cong.symm (Cong.parNil _)⟩
      | synchronise b c v hc =>
          exact ⟨.synchronise _ _ b c v, nil, hc,
            Cong.symm (Cong.parNil _), Cong.symm (Cong.parNil _)⟩
      | opening p hc =>
          exact ⟨.opening _ _ p, nil, hc,
            Cong.symm (Cong.parNil _), Cong.symm (Cong.parNil _)⟩
      | release b p hc =>
          exact ⟨.release _ _ b p, nil, hc,
            Cong.symm (Cong.parNil _), Cong.symm (Cong.parNil _)⟩
      | parLeft r _ ih =>
          obtain ⟨ri, ctx, hvalid, hsrc, htgt⟩ := ih
          refine ⟨ri, par ctx r, hvalid, ?_, ?_⟩
          · refine cong_of_components ?_
            have := cong_components hsrc
            simp only [components] at this ⊢
            rw [this]; exact (add_assoc _ _ _)
          · refine cong_of_components ?_
            have := cong_components htgt
            simp only [components] at this ⊢
            rw [this]; exact (add_assoc _ _ _)
      | congruent hc _ hc' ih =>
          obtain ⟨ri, ctx, hvalid, hsrc, htgt⟩ := ih
          exact ⟨ri, ctx, hvalid, Cong.trans hc hsrc, Cong.trans (Cong.symm hc') htgt⟩
  | buildPar c p q h₁ h₂ =>
      exact ⟨.buildPar _ _ _ _ c p q, nil, ⟨h₁, h₂⟩,
        Cong.symm (Cong.parNil _), Cong.symm (Cong.parNil _)⟩
  | buildMsg c u v h₁ h₂ =>
      exact ⟨.buildMsg _ _ _ _ c u v, nil, ⟨h₁, h₂⟩,
        Cong.symm (Cong.parNil _), Cong.symm (Cong.parNil _)⟩
  | buildDup e p q r h₁ h₂ h₃ =>
      exact ⟨.buildDup _ _ _ _ _ _ e p q r, nil, ⟨h₁, h₂, h₃⟩,
        Cong.symm (Cong.parNil _), Cong.symm (Cong.parNil _)⟩
  | buildSyn e p q r h₁ h₂ h₃ =>
      exact ⟨.buildSyn _ _ _ _ _ _ e p q r, nil, ⟨h₁, h₂, h₃⟩,
        Cong.symm (Cong.parNil _), Cong.symm (Cong.parNil _)⟩
  | parLeft r _ ih =>
      obtain ⟨ri, ctx, hvalid, hsrc, htgt⟩ := ih
      refine ⟨ri, par ctx r, hvalid, ?_, ?_⟩
      · refine cong_of_components ?_
        have := cong_components hsrc
        simp only [components] at this ⊢
        rw [this]; exact (add_assoc _ _ _)
      · refine cong_of_components ?_
        have := cong_components htgt
        simp only [components] at this ⊢
        rw [this]; exact (add_assoc _ _ _)
  | congruent hc _ hc' ih =>
      obtain ⟨ri, ctx, hvalid, hsrc, htgt⟩ := ih
      exact ⟨ri, ctx, hvalid, Cong.trans hc hsrc, Cong.trans (Cong.symm hc') htgt⟩

/-- The converse: a valid instance sitting beside a context is a step. -/
theorem step_of_decompose {t t' : Comb} {ri : RuleInstance} {ctx : Comb}
    (hvalid : ri.Valid) (hsrc : Cong t (par ri.redexTerm ctx))
    (htgt : Cong t' (par ri.reactumTerm ctx)) : Step Cong t t' :=
  Step.congruent hsrc (Step.parLeft ctx (RuleInstance.toStep hvalid)) (Cong.symm htgt)

/-- **A step is exactly a redex replaced in place.**  This is the inversion the
reactive-systems analysis consumes: the left side is the reduction relation, the
right side is "a rule's redex beside a reaction context becomes its reactum
beside the same context". -/
theorem step_iff_redex {t t' : Comb} :
    Step Cong t t' ↔ ∃ (ri : RuleInstance) (ctx : Comb),
      ri.Valid ∧ Cong t (par ri.redexTerm ctx) ∧ Cong t' (par ri.reactumTerm ctx) :=
  ⟨step_decompose, fun ⟨_, _, hvalid, hsrc, htgt⟩ => step_of_decompose hvalid hsrc htgt⟩

/-- Decomposition in component form, which is how a bag calculation uses it. -/
theorem components_of_step {t t' : Comb} (h : Step Cong t t') :
    ∃ (ri : RuleInstance) (ctx : Multiset Comb),
      ri.Valid ∧ components t = components ri.redexTerm + ctx
              ∧ components t' = components ri.reactumTerm + ctx := by
  obtain ⟨ri, ctxTerm, hvalid, hsrc, htgt⟩ := step_decompose h
  refine ⟨ri, components ctxTerm, hvalid, ?_, ?_⟩
  · simpa only [components] using cong_components hsrc
  · simpa only [components] using cong_components htgt

end Mettapedia.Languages.ProcessCalculi.RhoCombinators
