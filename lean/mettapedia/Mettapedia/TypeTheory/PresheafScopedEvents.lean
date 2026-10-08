import Mettapedia.TypeTheory.PresheafEventCertificates

/-!
# Scoped contextual events

A scope is a subfunctor of names. Restricting an event to a scope stores the
membership witness beside its occurrence; all context maps preserve that
membership. The complete dependent event certificate still reads out the
original event and its target evidence.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafEventCertificates

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafSlice
open PresheafEventCertificates

universe u
variable {C : Type u} [Category.{u} C]
variable {P Q N : Cᵒᵖ ⥤ Type u}

namespace EventSpan

variable (span : PresheafEventCertificates.EventSpan P Q)
  (name : span.events ⟶ N) (scope : Subfunctor N)

/-- The event fibre admitted by a contextual name predicate. -/
def inScope : PresheafEventCertificates.EventSpan P Q where
  events := (scope.preimage name).toFunctor
  source := (scope.preimage name).ι ≫ span.source
  target := (scope.preimage name).ι ≫ span.target

/-- Scope erasure keeps the actual event, not only its endpoints. -/
def scopeErasure : (span.inScope name scope).events ⟶ span.events :=
  (scope.preimage name).ι

theorem scopeErasure_source :
    span.scopeErasure name scope ≫ span.source = (span.inScope name scope).source := rfl

theorem scopeErasure_target :
    span.scopeErasure name scope ≫ span.target = (span.inScope name scope).target := rfl

/-- Any supplied admitted event has a natural, scope-certified lift. -/
def scopeLift {E : Cᵒᵖ ⥤ Type u} (event : E ⟶ span.events)
    (admitted : ∀ world (e : E.obj world), name.app world (event.app world e) ∈ scope.obj world) :
    E ⟶ (span.inScope name scope).events :=
  Subfunctor.lift event (by
    intro world e member
    obtain ⟨given, rfl⟩ := member
    exact admitted world given)

theorem scopeLift_erasure {E : Cᵒᵖ ⥤ Type u} (event : E ⟶ span.events)
    (admitted : ∀ world (e : E.obj world), name.app world (event.app world e) ∈ scope.obj world) :
    span.scopeLift name scope event admitted ≫ span.scopeErasure name scope = event :=
  Subfunctor.lift_ι event _

/-- The scope-certified factorization is unique over the event readout. -/
theorem scopeLift_unique {E : Cᵒᵖ ⥤ Type u} (event : E ⟶ span.events)
    (admitted : ∀ world (e : E.obj world), name.app world (event.app world e) ∈ scope.obj world)
    (lift : E ⟶ (span.inScope name scope).events)
    (erases : lift ≫ span.scopeErasure name scope = event) :
    lift = span.scopeLift name scope event admitted := by
  ext world given
  apply Subtype.ext
  change (lift.app world given).val = event.app world given
  exact ConcreteCategory.congr_hom (NatTrans.congr_app erases world) given

/-- Forgetting scope membership preserves the event and complete target witness. -/
def forgetScope (A : DisplayedFamily Q) :
    (span.inScope name scope).certificates A ⟶ span.certificates A where
  app point := ↾fun receipt =>
    ⟨⟨receipt.val.1.val, receipt.val.2⟩, receipt.property⟩
  naturality _ _ _ := by
    ext receipt
    rfl

theorem forgetScope_event (A : DisplayedFamily Q) :
    totalHom (span.forgetScope name scope A) ≫ span.eventReadout A =
      (span.inScope name scope).eventReadout A ≫ span.scopeErasure name scope := by
  ext world receipt
  rfl

theorem forgetScope_result (A : DisplayedFamily Q) :
    totalHom (span.forgetScope name scope A) ≫ span.resultReadout A =
      (span.inScope name scope).resultReadout A := by
  ext world receipt
  rfl

/-- Scoped inhabitation is precisely an admitted, enabled event with a target
certificate. Endpoint or scope membership alone does not supply it. -/
theorem scoped_nonempty_iff (A : DisplayedFamily Q) (world : Cᵒᵖ)
    (program : P.obj world) :
    Nonempty (((span.inScope name scope).certificates A).obj ⟨world, program⟩) ↔
      ∃ event : span.events.obj world,
        span.source.app world event = program ∧
        name.app world event ∈ scope.obj world ∧
        Nonempty (A.obj ⟨world, span.target.app world event⟩) := by
  constructor
  · rintro ⟨receipt⟩
    exact ⟨receipt.val.1.val, receipt.property, receipt.val.1.property, ⟨receipt.val.2⟩⟩
  · rintro ⟨event, source, admitted, ⟨evidence⟩⟩
    exact ⟨⟨⟨⟨event, admitted⟩, evidence⟩, source⟩⟩

/-- Scope membership is checked in every reached context, by the actual
subfunctor action; it is not a predicate on only the current name spelling. -/
theorem scope_future {U V : Cᵒᵖ} (arrow : U ⟶ V)
    (event : (span.inScope name scope).events.obj U) :
    name.app V (span.events.map arrow event.val) ∈ scope.obj V := by
  change (scope.preimage name).toFunctor.obj U at event
  rw [NatTrans.naturality_apply name arrow event.val]
  exact scope.map arrow event.property

end EventSpan

end Mettapedia.TypeTheory.PresheafEventCertificates
