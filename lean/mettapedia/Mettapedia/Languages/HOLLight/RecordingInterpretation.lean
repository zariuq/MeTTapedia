import Mettapedia.Languages.HOLLight.RunSourceReadback

/-! # Forward records from the loaded continuation pullback

The interpretation uses the received `tc_pullback` operation, whose recursion
equations have already been read from its accepted source history. At an
endomorphism carrier its right fold computes forward event updates. The
carrier equivalence changes representation; it assumes no update equation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.RecordingInterpretation

open Mettapedia.Logic Mettapedia.Languages.OpenTheory

universe w r

variable (signature : RunModelCorrespondence.Signature)
  (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
  {Record : Type r} (values : signature.Value model ≃ (Record → Record))

def continuationBack (update : signature.lists.Element model → Record → Record)
    (event : signature.lists.Element model) (next : signature.Value model) :
    signature.Value model :=
  values.symm (fun prior => values next (update event prior))

theorem continuation_fold (update : signature.lists.Element model → Record → Record)
    (events : List (signature.lists.Element model)) (next : signature.Value model)
    (prior : Record) :
    values (events.foldr (continuationBack signature model values update) next) prior =
      values next (events.foldl (fun record event => update event record) prior) := by
  induction events generalizing prior with
  | nil => rfl
  | cons event events ih =>
      simp only [List.foldr_cons, continuationBack, Equiv.apply_symm_apply, List.foldl_cons]
      exact ih (update event prior)

def record (agreement : RunSourceReadback.Correspondence signature model)
    (update : signature.lists.Element model → Record → Record)
    (events : List (signature.lists.Element model)) (prior : Record) : Record :=
  values (signature.backValue model (continuationBack signature model values update)
    (agreement.lists.equivalence events) (values.symm id)) prior

theorem record_eq_foldl (agreement : RunSourceReadback.Correspondence signature model)
    (update : signature.lists.Element model → Record → Record)
    (events : List (signature.lists.Element model)) (prior : Record) :
    record signature model values agreement update events prior =
      events.foldl (fun record event => update event record) prior := by
  unfold record
  rw [agreement.pullback, continuation_fold]
  exact congrFun (values.apply_symm_apply id) _

theorem record_append (agreement : RunSourceReadback.Correspondence signature model)
    (update : signature.lists.Element model → Record → Record)
    (first second : List (signature.lists.Element model)) (prior : Record) :
    record signature model values agreement update (first ++ second) prior =
      record signature model values agreement update second
        (record signature model values agreement update first prior) := by
  simp only [record_eq_foldl, List.foldl_append]

end Mettapedia.Languages.HOLLight.RecordingInterpretation
