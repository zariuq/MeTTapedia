import Mettapedia.GSLT.LanguageDef.CompiledTwoSidedHeadProgram

/-!
# Destination passing at activation

The defunctionalized machine of `DefunctionalizedEquationBodies` passes outputs
back: a callee returns its value and the caller unifies its pattern with it when
the return frame resumes.  PeTTa's reference translation, and now CeTTa's open
equation machine, pass outputs forward: the head of an equation carries, as one
more argument, the term its body exposes as output, so the caller's destination
is unified with that term during head matching, before any goal of the body runs.
This module defines the constructions of that discipline and the machine that
runs them.  `DestinationPassingRefinement` compares it with the output-at-return
machine.

**Exposed outputs.**  `Code.exposed` is the template a body in administrative
normal form returns, seen through calls, primitives and bindings to its `ret`; a
conditional, a last call and failure expose none.  `Source.exposed` is the same
on nested source bodies, seen through `let` to the body's result and defined only
for a spine that may return (`Source.mayReturn`).  For `(S (plus $l $r))`, written
`letE h (call plus [l, r]) (ret (S h))`, the exposed output is `(S h)`: the
constructor skeleton with the call's output hole.  Basic facts:
`Code.exposed_support` (an exposed output reads only slots its body reads),
`inspectCode_ret_exposed` and `inspectOut_ret_exposed` (a body with an exposed
output returns exactly its instance, in either machine), `exposed_normFirst`
(output-first normalization keeps it), `Source.exposed_mayReturn`.

**Output-first normalization.**  `normFirst` is `norm` except that a `let` whose
bound body exposes an output binds its pattern to that output *before* the bound
body runs (`bindFirst`); the binding after it stays, and once the first has been
made it adds no constraint (`ExactStore.unify_entailed` in
`DestinationPassingRefinement`).  `BindsAhead E late early` relates a body to one that
performs some of its bindings earlier, `E` listing, innermost first, those
performed ahead and not yet reached by the later body; `bindsAhead_norm` shows
`BindsAhead [] (norm s) (normFirst s)` for every source body, and
`BindsAhead.support_eq`, `BindsAhead.exposed_eq` show both bodies read the same
slots and expose the same output.

**The output-first machine** (`outputFirst`) is the generic shared-continuation
machine on the same codes.  A control carries its destination (`none` at the top
of a query).  Activation (`activateOut`) unifies the head with the arguments and
then meets the destination: it unifies the rhs's exposed output with it
(`meet`).  A call passes its pattern as the callee's destination; a last call
passes its own destination on; a conditional meets the destination with the
exposed output of the branch it takes, before the branch runs; a return does not
unify.

**Destination as a head parameter.**  `activateOut_eq_extended`: for a
destination `d`, activating an equation whose rhs exposes `x` is the ordinary
activation of the equation whose head is extended by `x`, against the arguments
extended by `d` (`unifyAll_append_singleton`); `activateOut_withOutputs` states
it for a whole relation.  Over head patterns and the substitution store,
`destinationActivation_eq_source` identifies this step with `sourceActivation` of
the extended lists, so `destinationActivation_exact` and
`destinationActivation_variant` are `activation_exact` and `activation_variant`
for them: the compiled head of the extended equation agrees with the
destination-passing activation up to the names of fresh variables.
`compiledActivate_withOutputs_exact` is the same for a whole relation, in
authored order.  In the source activation the slots of the exposed output,
including an output hole, are fresh supply variables like every slot; in the
head code emitted for the extended head, a slot the head already bound occurs
again (`equateSlot`) while an output hole occurs first (`bindSlot`) and takes
the destination's subterm, as `DestinationPassingControls.plusZero_head_code`
and `plusSucc_head_code` show for `plus`.

**Correspondence with the C open equation machine**
(`open_equation_machine.c`).  `oem_build_tail` computes the exposed template of
a tail construct: through `let`/`let*` to the body, a constructor over its
elements' templates, and a fresh hole for a call, a primitive and an `if`;
`oem_compile_equation` records it as the equation's destination.  In the model a
call's or primitive's hole is the pattern its `letCall` or `letPrim` binds, and
an `if`'s hole is the destination itself (`Code.exposed = none`, met in the
branches).  At activation (`oem_activate`), `OEM_DEST_UNIFY` is `meet` on an
exposed template, and `OEM_DEST_SLOT` is `meet` on an exposed slot: the C makes
a slot the head left unbound the destination itself, the model unifies the
slot's fresh variable with it.
`OEM_DEST_NONE` (a last call or `empty`) is `Code.exposed = none`: no meeting,
and `OEM_S_TAIL` keeps the continuation, as `.tail` keeps the destination.
`oem_emit_tail` emits `OEM_S_BIND` of a let's pattern with its value's exposed
term before the value's goals (`bindFirst`), and `oem_emit_branch` emits
`OEM_S_BIND` of the if's output hole with a branch's exposed term before the
branch (`meet` in `inspectOut`).  `OEM_S_RET` does not unify (`outputFirst.resume`).
A call's destination is its `pattern` (`OEM_S_CALL`), as `inspectOut` passes
the instance of a `letCall` pattern.

**Not covered.**  The front end that turns a nested MeTTa value into slots and
goals (`oem_build_value`, `oem_emit_goals`); here source bodies are
`DefunctionalizedEquationBodies.Source` terms, with calls nested in data written
as `let`s of temporary slots.  `oem_unify_template` unifies a template with a
term without building the template; the model instantiates the template first.
Relational occurrences in heads, handoffs, costs, and conformance of the C code:
this is a model, not a verified translation.  The model keeps the binding after a
let's value, which the C does not emit.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies

open Mettapedia.Machines.SharedContinuation

variable {Term Rel Op : Type} {L : TemplateLanguage Term}

/-! ## Exposed outputs -/

/-- The exposed output of a body in administrative normal form: the template
its `ret` returns, seen through calls, primitives and bindings.  A conditional,
a last call and failure expose none: the destination is met in the branches,
passed to the callee, or never met. -/
def Code.exposed {k : Nat} : Code L Rel Op k → Option (L.Tmpl k)
  | .ret t => some t
  | .fail => none
  | .letCall _ _ _ body => body.exposed
  | .letPrim _ _ _ body => body.exposed
  | .bind _ _ body => body.exposed
  | .ite _ _ _ _ => none
  | .tail _ _ => none

/-- An exposed output reads only slots its body reads. -/
theorem Code.exposed_support {k : Nat} :
    ∀ (code : Code L Rel Op k) {x : L.Tmpl k}, code.exposed = some x →
      L.support x ⊆ code.support L
  | .ret t, x, exposed => by
      simp only [Code.exposed, Option.some.injEq] at exposed
      subst exposed
      exact fun _ member => by simpa [Code.support] using member
  | .fail, _, exposed => by simp [Code.exposed] at exposed
  | .letCall p rel args body, x, exposed => fun i member => by
      simp only [Code.support, Finset.mem_union]
      exact .inr (Code.exposed_support body exposed member)
  | .letPrim p op args body, x, exposed => fun i member => by
      simp only [Code.support, Finset.mem_union]
      exact .inr (Code.exposed_support body exposed member)
  | .bind p v body, x, exposed => fun i member => by
      simp only [Code.support, Finset.mem_union]
      exact .inr (Code.exposed_support body exposed member)
  | .ite _ _ _ _, _, exposed => by simp [Code.exposed] at exposed
  | .tail _ _, _, exposed => by simp [Code.exposed] at exposed

/-- Whether a source body may reach its result: it is not failure, and a `let`
may return only when its bound body may. -/
def Source.mayReturn {k : Nat} : Source L Rel Op k → Bool
  | .ret _ => true
  | .fail => false
  | .call _ _ => true
  | .letPrim _ _ _ body => body.mayReturn
  | .ite _ _ yes no => yes.mayReturn || no.mayReturn
  | .letE _ bound body => bound.mayReturn && body.mayReturn

/-- The exposed output of a source body: the template it returns, seen through
`let` to its body and through primitives.  A last call, a conditional and
failure expose none, and so does a `let` whose bound body cannot return. -/
def Source.exposed {k : Nat} : Source L Rel Op k → Option (L.Tmpl k)
  | .ret t => some t
  | .fail => none
  | .call _ _ => none
  | .letPrim _ _ _ body => body.exposed
  | .ite _ _ _ _ => none
  | .letE _ bound body => if bound.mayReturn then body.exposed else none

theorem Source.exposed_mayReturn {k : Nat} :
    ∀ (s : Source L Rel Op k) {x : L.Tmpl k}, s.exposed = some x → s.mayReturn = true
  | .ret _, _, _ => rfl
  | .fail, _, exposed => by simp [Source.exposed] at exposed
  | .call _ _, _, exposed => by simp [Source.exposed] at exposed
  | .letPrim _ _ _ body, _, exposed => Source.exposed_mayReturn body exposed
  | .ite _ _ _ _, _, exposed => by simp [Source.exposed] at exposed
  | .letE _ bound body, _, exposed => by
      simp only [Source.exposed] at exposed
      split at exposed
      · rename_i returns
        simp [Source.mayReturn, returns, Source.exposed_mayReturn body exposed]
      · cases exposed

/-! ## Output-first normalization -/

section Normalization

variable (L)

/-- Bind a let's pattern to the exposed output of its bound body before the
bound body runs, when there is one. -/
def bindFirst {k : Nat} (pattern : L.Tmpl k) (bound : Source L Rel Op k)
    (code : Code L Rel Op k) : Code L Rel Op k :=
  match bound.exposed with
  | some x => .bind pattern x code
  | none => code

/-- `normBind` with every nested `let` binding its pattern first. -/
def normBindFirst {k : Nat} :
    Source L Rel Op k → L.Tmpl k → Code L Rel Op k → Code L Rel Op k
  | .ret t, p, c => .bind p t c
  | .fail, _, _ => .fail
  | .call rel args, p, c => .letCall p rel args c
  | .letPrim q op args b, p, c => .letPrim q op args (normBindFirst b p c)
  | .ite op args yes no, p, c => .ite op args (normBindFirst yes p c) (normBindFirst no p c)
  | .letE q bound body, p, c => bindFirst L q bound (normBindFirst bound q (normBindFirst body p c))

/-- Output-first normalization: `norm`, with every `let` binding its pattern to
its bound body's exposed output before the bound body runs. -/
def normFirst {k : Nat} : Source L Rel Op k → Code L Rel Op k
  | .ret t => .ret t
  | .fail => .fail
  | .call rel args => .tail rel args
  | .letPrim q op args b => .letPrim q op args (normFirst b)
  | .ite op args yes no => .ite op args (normFirst yes) (normFirst no)
  | .letE q bound body => bindFirst L q bound (normBindFirst L bound q (normFirst body))

/-- Normalize every equation body output-first; heads are unchanged. -/
def SProgram.normalizeFirst (P : SProgram L Rel Op) : EqProgram L Rel Op :=
  P.map fun e => (e.1, ⟨e.2.slots, e.2.params, normFirst L e.2.rhs⟩)

/-! ## Bodies that bind ahead -/

/-- `BindsAhead E late early`: `early` performs every binding of `late`, some of
them earlier.  `E` lists, innermost first, the bindings `early` has performed
and `late` has not reached yet; `late` performs each of them at a `settle`, where
`early` repeats it.  A binding performed ahead reads only slots `late` reads. -/
inductive BindsAhead {k : Nat} :
    List (L.Tmpl k × L.Tmpl k) → Code L Rel Op k → Code L Rel Op k → Prop
  | ret (t : L.Tmpl k) : BindsAhead [] (.ret t) (.ret t)
  | fail (E : List (L.Tmpl k × L.Tmpl k)) : BindsAhead E .fail .fail
  | tail (rel : Rel) (args : List (L.Tmpl k)) : BindsAhead [] (.tail rel args) (.tail rel args)
  | letCall {E late early} (p : L.Tmpl k) (rel : Rel) (args : List (L.Tmpl k)) :
      BindsAhead E late early →
        BindsAhead E (.letCall p rel args late) (.letCall p rel args early)
  | letPrim {E late early} (p : L.Tmpl k) (op : Op) (args : List (L.Tmpl k)) :
      BindsAhead E late early →
        BindsAhead E (.letPrim p op args late) (.letPrim p op args early)
  | bind {E late early} (p v : L.Tmpl k) :
      BindsAhead E late early → BindsAhead E (.bind p v late) (.bind p v early)
  | settle {E late early} (p v : L.Tmpl k) :
      BindsAhead E late early → BindsAhead ((p, v) :: E) (.bind p v late) (.bind p v early)
  | ahead {E late early} (p v : L.Tmpl k) :
      BindsAhead ((p, v) :: E) late early → L.support p ∪ L.support v ⊆ late.support L →
        BindsAhead E late (.bind p v early)
  | ite {E yes yes' no no'} (op : Op) (args : List (L.Tmpl k)) :
      BindsAhead E yes yes' → BindsAhead E no no' →
        BindsAhead E (.ite op args yes no) (.ite op args yes' no')

variable {L}

/-- Both bodies read the same slots. -/
theorem BindsAhead.support_eq {k : Nat} {E : List (L.Tmpl k × L.Tmpl k)}
    {late early : Code L Rel Op k} (h : BindsAhead L E late early) :
    early.support L = late.support L := by
  induction h with
  | ret => rfl
  | fail => rfl
  | tail => rfl
  | letCall p rel args _ ih => simp [Code.support, ih]
  | letPrim p op args _ ih => simp [Code.support, ih]
  | bind p v _ ih => simp [Code.support, ih]
  | settle p v _ ih => simp [Code.support, ih]
  | ahead p v _ inside ih =>
      simp only [Code.support, ih]
      exact Finset.union_eq_right.mpr inside
  | ite op args _ _ ihYes ihNo => simp [Code.support, ihYes, ihNo]

/-- Both bodies expose the same output. -/
theorem BindsAhead.exposed_eq {k : Nat} {E : List (L.Tmpl k × L.Tmpl k)}
    {late early : Code L Rel Op k} (h : BindsAhead L E late early) :
    early.exposed = late.exposed := by
  induction h with
  | ret => rfl
  | fail => rfl
  | tail => rfl
  | letCall _ _ _ _ ih => exact ih
  | letPrim _ _ _ _ ih => exact ih
  | bind _ _ _ ih => exact ih
  | settle _ _ _ ih => exact ih
  | ahead _ _ _ _ ih => exact ih
  | ite => rfl

/-- Every body binds ahead of itself, with nothing pending. -/
theorem BindsAhead.refl {k : Nat} : ∀ code : Code L Rel Op k, BindsAhead L [] code code
  | .ret t => .ret t
  | .fail => .fail []
  | .letCall p rel args body => .letCall p rel args (BindsAhead.refl body)
  | .letPrim p op args body => .letPrim p op args (BindsAhead.refl body)
  | .bind p v body => .bind p v (BindsAhead.refl body)
  | .ite op args yes no => .ite op args (BindsAhead.refl yes) (BindsAhead.refl no)
  | .tail rel args => .tail rel args

/-- A continuation is part of the normalization of a body that may return. -/
theorem support_subset_normBind {k : Nat} :
    ∀ (s : Source L Rel Op k) (p : L.Tmpl k) (c : Code L Rel Op k), s.mayReturn = true →
      c.support L ⊆ (normBind L s p c).support L
  | .ret t, p, c, _ => fun i member => by simp [normBind, Code.support, member]
  | .fail, _, _, returns => by simp [Source.mayReturn] at returns
  | .call rel args, p, c, _ => fun i member => by simp [normBind, Code.support, member]
  | .letPrim q op args b, p, c, returns => fun i member => by
      simp only [normBind, Code.support, Finset.mem_union]
      exact .inr (support_subset_normBind b p c returns member)
  | .ite op args yes no, p, c, returns => fun i member => by
      simp only [Source.mayReturn, Bool.or_eq_true] at returns
      simp only [normBind, Code.support, Finset.mem_union]
      rcases returns with returns | returns
      · exact .inl (.inr (support_subset_normBind yes p c returns member))
      · exact .inr (support_subset_normBind no p c returns member)
  | .letE q bound body, p, c, returns => by
      simp only [Source.mayReturn, Bool.and_eq_true] at returns
      exact (support_subset_normBind body p c returns.2).trans
        (support_subset_normBind bound q _ returns.1)

/-- The binding at the end of a body with an exposed output reads the pattern and
the output. -/
theorem exposed_support_normBind {k : Nat} :
    ∀ (s : Source L Rel Op k) {x : L.Tmpl k} (p : L.Tmpl k) (c : Code L Rel Op k),
      s.exposed = some x → L.support p ∪ L.support x ⊆ (normBind L s p c).support L
  | .ret t, x, p, c, exposed => by
      simp only [Source.exposed, Option.some.injEq] at exposed
      subst exposed
      intro i member
      simp only [Finset.mem_union] at member
      simp only [normBind, Code.support, Finset.mem_union]
      tauto
  | .fail, _, _, _, exposed => by simp [Source.exposed] at exposed
  | .call _ _, _, _, _, exposed => by simp [Source.exposed] at exposed
  | .letPrim q op args b, x, p, c, exposed => fun i member => by
      simp only [normBind, Code.support, Finset.mem_union]
      exact .inr (exposed_support_normBind b p c exposed member)
  | .ite _ _ _ _, _, _, _, exposed => by simp [Source.exposed] at exposed
  | .letE q bound body, x, p, c, exposed => by
      simp only [Source.exposed] at exposed
      split at exposed
      · rename_i returns
        exact (exposed_support_normBind body p c exposed).trans
          (support_subset_normBind bound q _ returns)
      · cases exposed

/-- `normBindFirst` binds ahead of `normBind`.  `joint`: the pattern `p` is bound
at the same point in both.  `pending`: when the body exposes `x`, the binding
`p := x` has been made ahead, and the body's result settles it. -/
theorem bindsAhead_normBind {k : Nat} (s : Source L Rel Op k) :
    (∀ (p : L.Tmpl k) (E : List (L.Tmpl k × L.Tmpl k)) (c c' : Code L Rel Op k),
        BindsAhead L E c c' → BindsAhead L E (normBind L s p c) (normBindFirst L s p c')) ∧
      (∀ (x p : L.Tmpl k) (E : List (L.Tmpl k × L.Tmpl k)) (c c' : Code L Rel Op k),
        s.exposed = some x → BindsAhead L E c c' →
          BindsAhead L ((p, x) :: E) (normBind L s p c) (normBindFirst L s p c')) := by
  induction s with
  | ret t =>
      refine ⟨fun p E c c' h => .bind p t h, fun x p E c c' exposed h => ?_⟩
      simp only [Source.exposed, Option.some.injEq] at exposed
      subst exposed
      exact .settle p t h
  | fail =>
      exact ⟨fun _ E _ _ _ => .fail E, fun _ _ E _ _ _ _ => .fail _⟩
  | call rel args =>
      refine ⟨fun p E c c' h => .letCall p rel args h, fun x p E c c' exposed _ => ?_⟩
      simp [Source.exposed] at exposed
  | letPrim q op args b ih =>
      exact ⟨fun p E c c' h => .letPrim q op args (ih.1 p E c c' h),
        fun x p E c c' exposed h => .letPrim q op args (ih.2 x p E c c' exposed h)⟩
  | ite op args yes no ihYes ihNo =>
      refine ⟨fun p E c c' h => .ite op args (ihYes.1 p E c c' h) (ihNo.1 p E c c' h),
        fun x p E c c' exposed _ => ?_⟩
      simp [Source.exposed] at exposed
  | letE q bound body ihBound ihBody =>
      -- the bound body binds `q`, first when it exposes an output
      have boundStep : ∀ (E : List (L.Tmpl k × L.Tmpl k)) (c c' : Code L Rel Op k),
          BindsAhead L E c c' →
            BindsAhead L E (normBind L bound q c)
              (bindFirst L q bound (normBindFirst L bound q c')) := by
        intro E c c' h
        unfold bindFirst
        split
        · rename_i x exposed
          exact .ahead q x (ihBound.2 x q E c c' exposed h)
            (exposed_support_normBind bound q c exposed)
        · exact ihBound.1 q E c c' h
      refine ⟨fun p E c c' h => boundStep E _ _ (ihBody.1 p E c c' h),
        fun x p E c c' exposed h => ?_⟩
      simp only [Source.exposed] at exposed
      split at exposed
      · exact boundStep ((p, x) :: E) _ _ (ihBody.2 x p E c c' exposed h)
      · cases exposed

/-- Output-first normalization binds ahead of `norm`, with nothing pending. -/
theorem bindsAhead_norm {k : Nat} (s : Source L Rel Op k) :
    BindsAhead L [] (norm L s) (normFirst L s) := by
  induction s with
  | ret t => exact .ret t
  | fail => exact .fail []
  | call rel args => exact .tail rel args
  | letPrim q op args b ih => exact .letPrim q op args ih
  | ite op args yes no ihYes ihNo => exact .ite op args ihYes ihNo
  | letE q bound body _ ihBody =>
      simp only [norm, normFirst, bindFirst]
      split
      · rename_i x exposed
        exact .ahead q x ((bindsAhead_normBind bound).2 x q [] _ _ exposed ihBody)
          (exposed_support_normBind bound q _ exposed)
      · exact (bindsAhead_normBind bound).1 q [] _ _ ihBody

/-- Output-first normalization keeps the exposed output. -/
theorem exposed_normFirst {k : Nat} (s : Source L Rel Op k) :
    (normFirst L s).exposed = (norm L s).exposed :=
  (bindsAhead_norm s).exposed_eq

end Normalization

/-- A body with an exposed output returns exactly that output's instance. -/
theorem inspectCode_ret_exposed {Store : Type} (L : TemplateLanguage Term)
    (S : StoreAlgebra Term Store Op) {k : Nat} (frame : Fin k → Term) :
    ∀ (σ : Store) (code : Code L Rel Op k) {x : L.Tmpl k} {v : Term} {σ' : Store},
      code.exposed = some x → inspectCode L S frame σ code = .ret (v, σ') → v = L.inst x frame
  | σ, .ret t, x, v, σ', exposed, returned => by
      simp only [Code.exposed, Option.some.injEq] at exposed
      simp only [inspectCode, Instruction.ret.injEq, Prod.mk.injEq] at returned
      rw [← exposed, returned.1]
  | _, .fail, _, _, _, exposed, _ => by simp [Code.exposed] at exposed
  | σ, .letCall p rel args body, _, _, _, _, returned => by simp [inspectCode] at returned
  | σ, .letPrim p op args body, x, v, σ', exposed, returned => by
      simp only [inspectCode] at returned
      split at returned
      · cases returned
      · split at returned
        · exact inspectCode_ret_exposed L S frame _ body exposed returned
        · cases returned
  | σ, .bind p w body, x, v, σ', exposed, returned => by
      simp only [inspectCode] at returned
      split at returned
      · exact inspectCode_ret_exposed L S frame _ body exposed returned
      · cases returned
  | _, .ite _ _ _ _, _, _, _, exposed, _ => by simp [Code.exposed] at exposed
  | _, .tail _ _, _, _, _, exposed, _ => by simp [Code.exposed] at exposed

end Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies

namespace Mettapedia.GSLT.LanguageDef.DestinationPassing

open Mettapedia.Machines.SharedContinuation
open DefunctionalizedEquationBodies

section Generic

variable {Term Store Rel Op : Type}

/-- A call of the output-first machine: relation, arguments, store, and the
destination its answers must meet (`none` at the top of a query). -/
abbrev DestCall (Term Store Rel : Type) := Rel × List Term × Store × Option Term

/-- A control of the output-first machine: the defunctionalized machine's
control and the destination of the running activation. -/
structure DestControl (L : TemplateLanguage Term) (Rel Op Store : Type)
    extends Control L Rel Op Store where
  dest : Option Term

/-- A return frame of the output-first machine: the resume site with its
captured slots, and the destination of the code that resumes. -/
structure DestFrame (L : TemplateLanguage Term) (Rel Op : Type)
    extends ReturnFrame L Rel Op where
  dest : Option Term

section Machine

variable (L : TemplateLanguage Term) (S : StoreAlgebra Term Store Op)

/-- Meet the destination: unify the body's exposed output with it, when both
exist. -/
def meet {k : Nat} (frame : Fin k → Term) (code : Code L Rel Op k) (dest : Option Term)
    (σ : Store) : Option Store :=
  match code.exposed, dest with
  | some x, some d => S.unify (L.inst x frame) d σ
  | _, _ => some σ

/-- The next control boundary of the output-first machine.  It runs the same
local work as `inspectCode`; a call passes its pattern's instance as the
callee's destination, a last call passes on its own destination, and a
conditional meets the destination with the exposed output of the branch it
takes before running it. -/
def inspectOut {k : Nat} (frame : Fin k → Term) (dest : Option Term) :
    Store → Code L Rel Op k →
      Instruction (DestCall Term Store Rel) (DestFrame L Rel Op) (Answer Term Store)
  | σ, .ret t => .ret (L.inst t frame, σ)
  | _, .fail => .fail
  | σ, .letCall p rel args body =>
      .call (rel, instArgs L args frame, σ, some (L.inst p frame))
        ⟨⟨k, p, body, capture frame (frameSupport L p body)⟩, dest⟩
  | σ, .letPrim p op args body =>
      match S.prim op (instArgs L args frame) σ with
      | none => .fail
      | some v =>
          match S.unify (L.inst p frame) v σ with
          | some σ' => inspectOut frame dest σ' body
          | none => .fail
  | σ, .bind p v body =>
      match S.unify (L.inst p frame) (L.inst v frame) σ with
      | some σ' => inspectOut frame dest σ' body
      | none => .fail
  | σ, .ite op args yes no =>
      match S.test op (instArgs L args frame) σ with
      | some true =>
          match meet L S frame yes dest σ with
          | some σ' => inspectOut frame dest σ' yes
          | none => .fail
      | some false =>
          match meet L S frame no dest σ with
          | some σ' => inspectOut frame dest σ' no
          | none => .fail
      | none => .fail
  | σ, .tail rel args => .tail (rel, instArgs L args frame, σ, dest)

/-- A body with an exposed output returns exactly that output's instance. -/
theorem inspectOut_ret_exposed {k : Nat} (frame : Fin k → Term) (dest : Option Term) :
    ∀ (σ : Store) (code : Code L Rel Op k) {x : L.Tmpl k} {v : Term} {σ' : Store},
      code.exposed = some x → inspectOut L S frame dest σ code = .ret (v, σ') →
        v = L.inst x frame
  | σ, .ret t, x, v, σ', exposed, returned => by
      simp only [Code.exposed, Option.some.injEq] at exposed
      simp only [inspectOut, Instruction.ret.injEq, Prod.mk.injEq] at returned
      rw [← exposed, returned.1]
  | _, .fail, _, _, _, exposed, _ => by simp [Code.exposed] at exposed
  | σ, .letCall p rel args body, _, _, _, _, returned => by simp [inspectOut] at returned
  | σ, .letPrim p op args body, x, v, σ', exposed, returned => by
      simp only [inspectOut] at returned
      split at returned
      · cases returned
      · split at returned
        · exact inspectOut_ret_exposed frame dest _ body exposed returned
        · cases returned
  | σ, .bind p w body, x, v, σ', exposed, returned => by
      simp only [inspectOut] at returned
      split at returned
      · exact inspectOut_ret_exposed frame dest _ body exposed returned
      · cases returned
  | _, .ite _ _ _ _, _, _, _, exposed, _ => by simp [Code.exposed] at exposed
  | _, .tail _ _, _, _, _, exposed, _ => by simp [Code.exposed] at exposed

variable [DecidableEq Rel]

/-- Output-first activation: every equation of the called relation, in authored
order, whose head unifies with the arguments and whose exposed output then meets
the destination. -/
def activateOut (P : EqProgram L Rel Op) :
    DestCall Term Store Rel → List (DestControl L Rel Op Store)
  | (rel, args, σ, dest) =>
      (P.equations rel).filterMap fun e =>
        let fresh := S.fresh σ e.slots
        ((unifyAll S (instArgs L e.params fresh.1) args fresh.2).bind
            (meet L S fresh.1 e.rhs dest)).map
          fun σ' => ⟨⟨e.slots, e.rhs, fresh.1, σ'⟩, dest⟩

variable [Inhabited Term]

/-- The output-first machine, as an instance of the generic shared-continuation
program.  Resuming a frame does not unify: the callee met its destination when
it was activated. -/
def outputFirst (P : EqProgram L Rel Op) :
    Program Unit (DestControl L Rel Op Store) (DestCall Term Store Rel)
      (DestFrame L Rel Op) (Answer Term Store) where
  inspect c := inspectOut L S c.frame c.dest c.store c.code
  branches _ c := (activateOut L S P c).map fun a => ((), a)
  resume _ f a := ((), ⟨⟨f.slots, f.body, reconstruct f.captured, a.2⟩, f.dest⟩)

/-- The initial state of a query without a destination: every activation of the
call, as in `DefunctionalizedEquationBodies.initial`. -/
def initialOut (P : EqProgram L Rel Op) (c : Call Term Store Rel) :
    State Unit (DestControl L Rel Op Store) (DestFrame L Rel Op) (Answer Term Store) :=
  ⟨(activateOut L S P (c.1, c.2.1, c.2.2, none)).map fun a => ⟨(), a, []⟩, []⟩

end Machine

/-! ## The destination as a head parameter -/

section HeadParameter

variable (S : StoreAlgebra Term Store Op)

/-- Unifying a list extended by one pair is unifying the list, then the pair. -/
theorem unifyAll_append_singleton :
    ∀ (ps as : List Term) (p a : Term) (σ : Store),
      unifyAll S (ps ++ [p]) (as ++ [a]) σ = (unifyAll S ps as σ).bind (S.unify p a)
  | [], [], p, a, σ => by simp [unifyAll]
  | [], b :: bs, p, a, σ => by
      cases bs <;> simp [unifyAll]
  | q :: qs, [], p, a, σ => by
      cases qs <;> simp [unifyAll]
  | q :: qs, b :: bs, p, a, σ => by
      simp only [List.cons_append, unifyAll, Option.bind_assoc]
      congr 1
      funext σ'
      exact unifyAll_append_singleton qs bs p a σ'

variable (L : TemplateLanguage Term)

/-- An equation whose head is extended by its body's exposed output. -/
def Equation.withOutput (e : Equation L Rel Op) : Equation L Rel Op :=
  ⟨e.slots, e.params ++ e.rhs.exposed.toList, e.rhs⟩

/-- Every equation's head extended by its body's exposed output. -/
def withOutputs (P : EqProgram L Rel Op) : EqProgram L Rel Op :=
  P.map fun e => (e.1, Equation.withOutput L e.2)

/-- **The destination is a head parameter.**  Activating an equation whose body
exposes `x` against a destination `d` is unifying the head extended by `x` with
the arguments extended by `d`. -/
theorem activateOut_eq_extended (e : Equation L Rel Op) {x : L.Tmpl e.slots}
    (exposed : e.rhs.exposed = some x) (args : List Term) (d : Term) (σ : Store) :
    (unifyAll S (instArgs L e.params (S.fresh σ e.slots).1) args (S.fresh σ e.slots).2).bind
        (meet L S (S.fresh σ e.slots).1 e.rhs (some d)) =
      unifyAll S (instArgs L (e.params ++ [x]) (S.fresh σ e.slots).1) (args ++ [d])
        (S.fresh σ e.slots).2 := by
  simp only [instArgs, List.map_append, List.map_cons, List.map_nil]
  rw [unifyAll_append_singleton]
  congr 1
  funext σ'
  simp [meet, exposed]

variable [DecidableEq Rel]

omit S in
theorem withOutputs_equations (P : EqProgram L Rel Op) (rel : Rel) :
    (withOutputs L P).equations rel = (P.equations rel).map (Equation.withOutput L) := by
  simp only [EqProgram.equations, withOutputs, List.filter_map, List.map_map]
  rfl

/-- For a relation whose every equation exposes an output, the output-first
activation of a call with destination `d` is the defunctionalized machine's
activation of the call extended by `d` against the extended heads. -/
theorem activateOut_withOutputs (P : EqProgram L Rel Op) (rel : Rel) (args : List Term)
    (d : Term) (σ : Store) (exposes : ∀ e ∈ P.equations rel, e.rhs.exposed.isSome) :
    activateOut L S P (rel, args, σ, some d) =
      (activate L S (withOutputs L P) (rel, args ++ [d], σ)).map
        fun a => ⟨⟨a.slots, a.code, a.frame, a.store⟩, some d⟩ := by
  simp only [activateOut, activate, withOutputs_equations, List.filterMap_map, List.map_filterMap]
  apply List.filterMap_congr
  intro e member
  obtain ⟨x, exposed⟩ := Option.isSome_iff_exists.mp (exposes e member)
  have extended := activateOut_eq_extended S L e exposed args d σ
  simp only [Function.comp_apply, Equation.withOutput, exposed, Option.toList_some]
  rw [extended]
  cases unifyAll S (instArgs L (e.params ++ [x]) (S.fresh σ e.slots).1) (args ++ [d])
    (S.fresh σ e.slots).2 <;> rfl

end HeadParameter

end Generic

universe r

section SubstitutionHeads

open Mettapedia.Logic.LP
open CompiledTwoSidedHeadProgram

variable {σ : LPSignature.{0, 0, r, 0}}
variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
variable (name : ℕ → σ.vars)
variable {Op : Type} (prim : Op → List (Term σ) → Subst σ × ℕ → Option (Term σ))
  (test : Op → List (Term σ) → Subst σ × ℕ → Option Bool)

/-- The destination-passing activation of one head over the substitution store:
allocate the frame, unify the head with the arguments, then unify the exposed
output with the destination. -/
def destinationActivation {k : ℕ} (params : List (HeadPattern σ (Fin k)))
    (output : HeadPattern σ (Fin k)) (args : List (Term σ)) (dest : Term σ) (θ : Subst σ)
    (n : ℕ) : Option ((Fin k → Term σ) × Subst σ × ℕ) :=
  let fresh := (substitutionStore name prim test).fresh (θ, n) k
  ((unifyAll (substitutionStore name prim test)
      (instArgs (headTemplates σ) params fresh.1) args fresh.2).bind
    fun store => (substitutionStore name prim test).unify (instantiate fresh.1 output) dest
      store).map fun store => (fresh.1, store)

/-- The destination-passing activation is the source activation of the head
extended by the output, against the arguments extended by the destination. -/
theorem destinationActivation_eq_source {k : ℕ} (params : List (HeadPattern σ (Fin k)))
    (output : HeadPattern σ (Fin k)) (args : List (Term σ)) (dest : Term σ) (θ : Subst σ)
    (n : ℕ) :
    destinationActivation name prim test params output args dest θ n =
      sourceActivation name prim test (params ++ [output]) (args ++ [dest]) θ n := by
  simp only [destinationActivation, sourceActivation, instArgs, List.map_append,
    List.map_cons, List.map_nil]
  rw [unifyAll_append_singleton]

/-- **Exactness of destination passing at activation.**  The compiled head of an
equation extended by its exposed output succeeds exactly when the
destination-passing activation does, and the two results are instances of each
other on every variable outside the fresh supply and on every slot. -/
theorem destinationActivation_exact (injective : Function.Injective name) {k : ℕ}
    (params : List (HeadPattern σ (Fin k))) (output : HeadPattern σ (Fin k))
    (args : List (Term σ)) (dest : Term σ) (θ : Subst σ) (n : ℕ)
    (entry : EntryCondition name θ n (args ++ [dest])) :
    (compiledActivation name (params ++ [output]) (args ++ [dest]) θ n).isSome =
        (destinationActivation name prim test params output args dest θ n).isSome ∧
      ∀ compiled source,
        compiledActivation name (params ++ [output]) (args ++ [dest]) θ n = some compiled →
        destinationActivation name prim test params output args dest θ n = some source →
        InstanceOffSupply name n (observe compiled.1 compiled.2.1)
            (observe source.1 source.2.1) ∧
          InstanceOffSupply name n (observe source.1 source.2.1)
            (observe compiled.1 compiled.2.1) := by
  rw [destinationActivation_eq_source]
  exact activation_exact name prim test injective (params ++ [output]) (args ++ [dest]) θ n entry

/-- **Exactness up to renaming.**  When both succeed, the compiled head's result
is the destination-passing activation's with its variables renamed, on every
variable outside the fresh supply and on every slot. -/
theorem destinationActivation_variant (injective : Function.Injective name) {k : ℕ}
    (params : List (HeadPattern σ (Fin k))) (output : HeadPattern σ (Fin k))
    (args : List (Term σ)) (dest : Term σ) (θ : Subst σ) (n : ℕ)
    (entry : EntryCondition name θ n (args ++ [dest]))
    {compiled source : (Fin k → Term σ) × Subst σ × ℕ}
    (compiledAccepted :
      compiledActivation name (params ++ [output]) (args ++ [dest]) θ n = some compiled)
    (sourceAccepted :
      destinationActivation name prim test params output args dest θ n = some source) :
    VariantOffSupply name n (observe source.1 source.2.1) (observe compiled.1 compiled.2.1) := by
  rw [destinationActivation_eq_source] at sourceAccepted
  exact activation_variant name prim test injective (params ++ [output]) (args ++ [dest]) θ n
    entry compiledAccepted sourceAccepted

/-- The output-first machine's activation step over head patterns and the
substitution store is `destinationActivation`, per equation. -/
theorem activateOut_step_eq_destinationActivation {Rel : Type}
    (e : Equation (headTemplates σ) Rel Op)
    {x : HeadPattern σ (Fin e.slots)} (exposed : e.rhs.exposed = some x) (args : List (Term σ))
    (d : Term σ) (θ : Subst σ) (n : ℕ) :
    (((unifyAll (substitutionStore name prim test)
          (instArgs (headTemplates σ) e.params
            ((substitutionStore name prim test).fresh (θ, n) e.slots).1) args
          ((substitutionStore name prim test).fresh (θ, n) e.slots).2).bind
        (meet (headTemplates σ) (substitutionStore name prim test)
          ((substitutionStore name prim test).fresh (θ, n) e.slots).1 e.rhs (some d))).map
        fun store => (((substitutionStore name prim test).fresh (θ, n) e.slots).1, store)) =
      destinationActivation name prim test e.params x args d θ n := by
  unfold destinationActivation meet
  simp only [exposed]

/-- **Exactness for a whole relation.**  When every equation of the called
relation exposes an output, the compiled heads extended by their outputs,
activated on the arguments extended by the destination, yield the output-first
activations: the same equations in authored order, each pair sharing its body
and agreeing up to the names of fresh variables. -/
theorem compiledActivate_withOutputs_exact (injective : Function.Injective name) {Rel : Type}
    [DecidableEq Rel] (P : EqProgram (headTemplates σ) Rel Op) (rel : Rel) (args : List (Term σ))
    (d : Term σ) (θ : Subst σ) (n : ℕ) (entry : EntryCondition name θ n (args ++ [d]))
    (exposes : ∀ e ∈ P.equations rel, e.rhs.exposed.isSome) :
    List.Forall₂ (fun compiled out =>
        SameActivation name n compiled ⟨out.slots, out.frame, out.store, out.code⟩)
      (compiledActivate name (withOutputs (headTemplates σ) P) (rel, args ++ [d], (θ, n)))
      (activateOut (headTemplates σ) (substitutionStore name prim test) P
        (rel, args, (θ, n), some d)) := by
  rw [activateOut_withOutputs (substitutionStore name prim test) (headTemplates σ) P rel args d
    (θ, n) exposes, List.forall₂_map_right_iff]
  exact compiledActivate_exact name prim test injective (withOutputs (headTemplates σ) P) rel
    (args ++ [d]) θ n entry

end SubstitutionHeads

end Mettapedia.GSLT.LanguageDef.DestinationPassing
