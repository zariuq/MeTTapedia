import Mettapedia.OSLF.Syntax.RhoScopedNativeAbsence
import Mettapedia.TypeTheory.PresheafEventCertificates

/-!
# Dependent event certificates and their actual rho future action

The independently authored original event graph supplies both ends of the
native event span. A certificate retains its entire rule instance and a
supplied witness at the actual target. Both readouts commute with every
syntactic substitution. Quotation-origin families supply a varying concrete
postcondition; distinct origins and rule receipts remain visible in it.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScopedDependentEventFutures

open _root_.CategoryTheory Mettapedia.OSLF.Binding Mettapedia.TypeTheory
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls RhoScopedParallelEvents
open RhoScopedEventPresheaf PresheafEventCertificates DisplayedPresheafTransport
open DisplayedPresheafComprehension DisplayedPresheafSliceSubstitution

theorem substitute_quote {context destination : Ctx sig} (change : Sub sig context destination)
    (process : Process context) : bindQ change (quote process) = quote (bindQ change process) := by
  induction process using Quotient.inductionOn with
  | _ process => rfl

def quotation : terms .pr ⟶ terms .nm where
  app _ := TypeCat.ofHom quote
  naturality _ _ change := by
    apply ConcreteCategory.hom_ext
    intro process
    exact (substitute_quote change.unop process).symm

def span (admitted : SourceRule → Prop) : EventSpan (terms .pr) (terms .pr) where
  events := RhoScopedEventPresheaf.events admitted
  source := RhoScopedEventPresheaf.source admitted
  target := RhoScopedEventPresheaf.target admitted

/-- A target-dependent origin fibre, with full contextual substitution. -/
def quotedTargetOrigins : DisplayedFamily (terms .pr) :=
  reindexDisplayed quotation (observationFibreFamily quotation)

def certificates (admitted : SourceRule → Prop) (family : DisplayedFamily (terms .pr)) :
    DisplayedFamily (terms .pr) :=
  (span admitted).certificates family

def complete_fibre (admitted : SourceRule → Prop) (family : DisplayedFamily (terms .pr))
    (world : (Syntactic.Ctxt sig)ᵒᵖ) (process : Process world.unop.vars) :
    (certificates admitted family).obj ⟨world, process⟩ ≃
      Σ event : {event : (RhoScopedEventPresheaf.events admitted).obj world //
        join event.1.source event.2 = process},
        family.obj ⟨world, join event.val.1.target event.val.2⟩ :=
  (span admitted).fibreEquiv family world process

def introduce (admitted : SourceRule → Prop) (family : DisplayedFamily (terms .pr))
    (world : (Syntactic.Ctxt sig)ᵒᵖ)
    (event : (RhoScopedEventPresheaf.events admitted).obj world)
    (evidence : family.obj ⟨world, join event.1.target event.2⟩) :
    (certificates admitted family).obj ⟨world, join event.1.source event.2⟩ :=
  (span admitted).introduce family world event evidence

theorem supplied_event_recovered (admitted : SourceRule → Prop)
    (family : DisplayedFamily (terms .pr)) (world : (Syntactic.Ctxt sig)ᵒᵖ)
    (event : (RhoScopedEventPresheaf.events admitted).obj world)
    (evidence : family.obj ⟨world, join event.1.target event.2⟩) :
    ((span admitted).eventReadout family).app world
      ⟨join event.1.source event.2, introduce admitted family world event evidence⟩ = event :=
  (span admitted).introduce_event family world event evidence

theorem supplied_target_evidence_recovered (admitted : SourceRule → Prop)
    (family : DisplayedFamily (terms .pr)) (world : (Syntactic.Ctxt sig)ᵒᵖ)
    (event : (RhoScopedEventPresheaf.events admitted).obj world)
    (evidence : family.obj ⟨world, join event.1.target event.2⟩) :
    ((span admitted).resultReadout family).app world
      ⟨join event.1.source event.2, introduce admitted family world event evidence⟩ =
        ⟨join event.1.target event.2, evidence⟩ :=
  (span admitted).introduce_result family world event evidence

theorem future_event_readout (admitted : SourceRule → Prop)
    (family : DisplayedFamily (terms .pr)) {world future : (Syntactic.Ctxt sig)ᵒᵖ}
    (change : world ⟶ future)
    (receipt : (totalSpace (certificates admitted family)).obj world) :
    ((span admitted).eventReadout family).app future
      ((totalSpace (certificates admitted family)).map change receipt) =
        (RhoScopedEventPresheaf.events admitted).map change
          (((span admitted).eventReadout family).app world receipt) :=
  ((span admitted).eventReadout family).naturality_apply change receipt

def originFamily (admitted : SourceRule → Prop) : (Syntactic.Ctxt sig)ᵒᵖ ⥤ Type :=
  (Functor.const _).obj (Selected admitted)

def eventOrigin (admitted : SourceRule → Prop) :
    RhoScopedEventPresheaf.events admitted ⟶ originFamily admitted where
  app _ := TypeCat.ofHom (fun event => event.1.1)

def receiptOrigin (admitted : SourceRule → Prop) (family : DisplayedFamily (terms .pr)) :
    totalSpace (certificates admitted family) ⟶ originFamily admitted :=
  (span admitted).eventReadout family ≫ eventOrigin admitted

theorem future_rule_origin (admitted : SourceRule → Prop)
    (family : DisplayedFamily (terms .pr)) {world future : (Syntactic.Ctxt sig)ᵒᵖ}
    (change : world ⟶ future)
    (receipt : (totalSpace (certificates admitted family)).obj world) :
    (receiptOrigin admitted family).app future
      ((totalSpace (certificates admitted family)).map change receipt) =
        (receiptOrigin admitted family).app world receipt :=
  (receiptOrigin admitted family).naturality_apply change receipt

def targetReadout (admitted : SourceRule → Prop) (family : DisplayedFamily (terms .pr)) :
    totalSpace (certificates admitted family) ⟶ totalSpace family :=
  (span admitted).resultReadout family

theorem future_target_certificate (admitted : SourceRule → Prop)
    (family : DisplayedFamily (terms .pr)) {world future : (Syntactic.Ctxt sig)ᵒᵖ}
    (change : world ⟶ future) :
    (totalSpace (certificates admitted family)).map change ≫
      (targetReadout admitted family).app future =
        (targetReadout admitted family).app world ≫ (totalSpace family).map change :=
  (targetReadout admitted family).naturality change

def universal_elimination (admitted : SourceRule → Prop)
    (family specification : DisplayedFamily (terms .pr)) :
    (certificates admitted family ⟶ specification) ≃
      (reindexDisplayed (span admitted).target family ⟶
        reindexDisplayed (span admitted).source specification) :=
  (span admitted).eliminationEquiv family specification

end Mettapedia.OSLF.Framework.RhoScopedDependentEventFutures
