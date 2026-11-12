import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperScheduleDomain

/-! # Source-compatible transport of complete two-sided schedule plans -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
variable {S : Signature} {O : Type} [DecidableEq O]

namespace PlacementIso

def afterRight {left right : State S O} {p q : ContextPlacement left right}
    (mapping : PlacementIso p q) (g : Firing right) : PlacementIso (p.afterRight g) (q.afterRight g) :=
  (mapping.swap.afterLeft g).swap

theorem right_candidate {left right : State S O} {p q : ContextPlacement left right}
    (mapping : PlacementIso p q) (g : Firing right) :
    helperTransport.move mapping.toStateIso (p.rightFiring g) = q.rightFiring g := by
  apply Firing.mk_congr _ _
  · exact (Assignment.instantiate_compose mapping.frame.hom p.rightMap g.value).symm.trans
      (congrArg (fun assignment => instantiate assignment g.value) mapping.right_map)
  · have same : (Frames.contextual S).comp mapping.frame.hom p.rightMap = q.rightMap := mapping.right_map
    exact (Frames.applyStore_applyStore (X := Frames.contextual S) p.rightMap mapping.frame.hom g.guards).trans
      (congrArg (fun assignment => (Frames.contextual S).applyStore assignment g.guards) same)

end PlacementIso

namespace Schedule

def targetsMap : ∀ {left right : State S O} {first : helperStep.Run left} {second : helperStep.Run right}
    {p q : ContextPlacement left right} (_mapping : PlacementIso p q) (schedule : Schedule first second),
    PlacementIso (target p schedule) (target q schedule)
  | _, _, _, _, _, _, mapping, .done _ _ => mapping
  | _, _, _, _, _, _, mapping, .left f _ tail => targetsMap (mapping.afterLeft f) tail
  | _, _, _, _, _, _, mapping, .right g _ tail => targetsMap (mapping.afterRight g) tail

def Plan.map : ∀ {left right : State S O} {first : helperStep.Run left} {second : helperStep.Run right}
    {p q : ContextPlacement left right} (_mapping : PlacementIso p q) (schedule : Schedule first second),
    Plan p schedule → Plan q schedule
  | _, _, _, _, _, _, _, .done _ _, .done _ => .done _
  | _, _, _, _, _, _, mapping, .left f _ tail, .left allowed later =>
      .left ((helperTransport.admits_alike (mapping.candidate f)).mp
        ((helperTransport.admits_move mapping.toStateIso _).mpr allowed))
        (map (mapping.afterLeft f) tail later)
  | _, _, _, _, _, _, mapping, .right g _ tail, .right allowed later =>
      .right ((helperTransport.admits_alike (mapping.right_candidate g)).mp
        ((helperTransport.admits_move mapping.toStateIso _).mpr allowed))
        (map (mapping.afterRight g) tail later)

theorem Plan.natural : ∀ {left right : State S O} {first : helperStep.Run left} {second : helperStep.Run right}
    {p q : ContextPlacement left right} (_mapping : PlacementIso p q) (schedule : Schedule first second)
    (one : Plan p schedule) (two : Plan q schedule),
    helperTransport.Similar (one.realize p schedule).execution (two.realize q schedule).execution
  | _, _, _, _, _, _, mapping, .done _ _, .done _, .done _ => ⟨mapping.toStateIso⟩
  | _, _, _, _, p, q, mapping, .left f _ tail, .left ap laterP, .left aq laterQ => by
      have middle := natural (mapping.afterLeft f) tail laterP laterQ
      have fromP := Transport.Similar.moveRun (helperTransport.symm (p.left_result_iso f))
        (laterP.realize (p.afterLeft f) tail).execution
      have toQ := Transport.Similar.moveRun (helperTransport.symm (q.left_result_iso f))
        (laterQ.realize (q.afterLeft f) tail).execution
      exact ⟨mapping.toStateIso, mapping.candidate f,
        Transport.Similar.trans (Transport.Similar.symm fromP) (Transport.Similar.trans middle toQ)⟩
  | _, _, _, _, p, q, mapping, .right g _ tail, .right ap laterP, .right aq laterQ => by
      have middle := natural (mapping.afterRight g) tail laterP laterQ
      have fromP := Transport.Similar.moveRun (helperTransport.symm (p.right_result_iso g))
        (laterP.realize (p.afterRight g) tail).execution
      have toQ := Transport.Similar.moveRun (helperTransport.symm (q.right_result_iso g))
        (laterQ.realize (q.afterRight g) tail).execution
      exact ⟨mapping.toStateIso, mapping.right_candidate g,
        Transport.Similar.trans (Transport.Similar.symm fromP) (Transport.Similar.trans middle toQ)⟩

end Schedule
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers
