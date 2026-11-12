import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperRightEffects

/-!
# Typed interleavings of two complete source-local helper runs

The schedule retains the source event on each side. Its plan stores actual
joint admission at every prefix. Interpretation constructs a native run and
an endpoint isomorphism; neither is supplied as an assumption.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
variable {S : Signature} {O : Type} [DecidableEq O]

inductive Schedule : {left right : State S O} → helperStep.Run left → helperStep.Run right → Type 1
  | done (left right : State S O) : Schedule (left := left) (right := right) (.nil left) (.nil right)
  | left {l r : State S O} (f : Firing l) (allowed : helperStep.Admits f)
      {rest : helperStep.Run f.after} {other : helperStep.Run r}
      (tail : Schedule (left := f.after) (right := r) rest other) :
      Schedule (left := l) (right := r) (.cons f allowed rest) other
  | right {l r : State S O} (g : Firing r) (allowed : helperStep.Admits g)
      {other : helperStep.Run l} {rest : helperStep.Run g.after}
      (tail : Schedule (left := l) (right := g.after) other rest) :
      Schedule (left := l) (right := r) other (.cons g allowed rest)

namespace Schedule

def target : {left right : State S O} → {first : helperStep.Run left} → {second : helperStep.Run right} →
    (place : ContextPlacement left right) → Schedule first second → ContextPlacement first.last second.last
  | _, _, _, _, place, .done _ _ => place
  | _l, r, _, _, place, .left f _ rest =>
      target (left := f.after) (right := r) (first := _) (second := _) (place.afterLeft f) rest
  | l, _r, _, _, place, .right g _ rest =>
      target (left := l) (right := g.after) (first := _) (second := _) (place.afterRight g) rest

inductive Plan : {left right : State S O} → {first : helperStep.Run left} → {second : helperStep.Run right} →
    ContextPlacement left right → Schedule first second → Type 1
  | done {l r : State S O} (place : ContextPlacement l r) : Plan place (.done l r)
  | left {l r : State S O} {place : ContextPlacement l r} {f : Firing l} {allowed : helperStep.Admits f}
      {rest : helperStep.Run f.after} {other : helperStep.Run r}
      {tail : Schedule (left := f.after) (right := r) rest other}
      (nativeAllowed : helperStep.Admits (s := place.state) (place.leftFiring f))
      (later : Plan (place.afterLeft f) tail) : Plan place (.left f allowed tail)
  | right {l r : State S O} {place : ContextPlacement l r} {g : Firing r} {allowed : helperStep.Admits g}
      {other : helperStep.Run l} {rest : helperStep.Run g.after}
      {tail : Schedule (left := l) (right := g.after) other rest}
      (nativeAllowed : helperStep.Admits (s := place.state) (place.rightFiring g))
      (later : Plan (place.afterRight g) tail) : Plan place (.right g allowed tail)

structure Result {left right : State S O} {first : helperStep.Run left} {second : helperStep.Run right}
    (place : ContextPlacement left right) (schedule : Schedule first second) where
  execution : helperStep.Run place.state
  resultIso : helperStep.StateIso execution.last (target place schedule).state

def Plan.realize : ∀ {left right : State S O} {first : helperStep.Run left} {second : helperStep.Run right}
    (place : ContextPlacement left right) (schedule : Schedule first second), Plan place schedule → Result place schedule
  | _, _, _, _, place, .done _ _, .done _ => ⟨.nil _, Step.StateIso.refl _⟩
  | _, _, _, _, place, .left f _ tail, .left allowed later => by
      let rest := realize (place.afterLeft f) tail later
      let iso := place.left_result_iso f
      let moved := helperTransport.moveRun (helperTransport.symm iso) rest.execution
      exact ⟨.cons (place.leftFiring f) allowed moved,
        helperTransport.trans
          (helperTransport.symm (helperTransport.moveRunEndIso (helperTransport.symm iso) rest.execution)) rest.resultIso⟩
  | _, _, _, _, place, .right g _ tail, .right allowed later => by
      let rest := realize (place.afterRight g) tail later
      let iso := place.right_result_iso g
      let moved := helperTransport.moveRun (helperTransport.symm iso) rest.execution
      exact ⟨.cons (place.rightFiring g) allowed moved,
        helperTransport.trans
          (helperTransport.symm (helperTransport.moveRunEndIso (helperTransport.symm iso) rest.execution)) rest.resultIso⟩

end Schedule
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers
