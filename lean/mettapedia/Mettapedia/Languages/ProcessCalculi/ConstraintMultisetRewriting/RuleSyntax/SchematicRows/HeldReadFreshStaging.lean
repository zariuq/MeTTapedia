import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadDatumSpan
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadStateScope
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadScopeReassociation

/-!
# Deriving both actual firing freshness obligations from joint scopes

The first scope exposes the consumer spec; the second exposes the datum spec.
The datum's actual freshness follows when their local frames coincide. The
consumer's freshness follows from reassociation and the proved span of the
actual materialized state. No universal variable object, global assignment
inhabitance or consumer-freshness conclusion is assumed.

Scope members expose terms only. They are not asserted to be admitted batches
or extra runtime steps.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadFreshStaging

open Interface (Frames)
open RuleOccurrences JointFirings

universe uO uT uH uE uOcc uR uC uZ
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) {O : Type uOcc} [DecidableEq O] {R : Type uR} [DecidableEq R]
  {C : Type uC} {Z : Type uZ} {E : Extensions.{uO, uH, uE} Hom}
  {codes : Codes Tm C Z} {source : RState Tm O R C Z}

def specScope (spec : Spec Tm C Z) : RuleSyntax.Rule Tm :=
  ⟨spec.locals, ⟨[], [], [], [], spec.terms⟩, []⟩

theorem specScope_terms (spec : Spec Tm C Z) : (specScope spec).terms = spec.terms := by
  exact List.append_nil spec.terms

def datumMember (firing : RFiring O R E codes source) :
    Member (Tm source.frame) E (Set.univ : RuleSyntax.Program Tm) firing.ext :=
  ⟨specScope firing.spec, Set.mem_univ _, firing.opening, ⟨[], [], []⟩, []⟩

def consumerMember (firing : RFiring O R E codes source)
    (consumer : RFiring O R (HeldReadScopeReassociation.identityExtensions X) codes (firing.result X)) :
    Member (Tm source.frame) E (Set.univ : RuleSyntax.Program Tm) firing.ext :=
  ⟨specScope consumer.spec, Set.mem_univ _, consumer.opening, ⟨[], [], []⟩, []⟩

def scopes (firing : RFiring O R E codes source)
    (consumer : RFiring O R (HeldReadScopeReassociation.identityExtensions X) codes (firing.result X)) :
    Bag (Tm source.frame) E (Set.univ : RuleSyntax.Program Tm) source.frame :=
  ⟨firing.ext, [consumerMember X firing consumer, datumMember firing]⟩

theorem datum_fresh (firing : RFiring O R E codes source)
    (consumer : RFiring O R (HeldReadScopeReassociation.identityExtensions X) codes (firing.result X))
    (same : consumer.spec.locals = firing.spec.locals)
    (joint : (scopes X firing consumer).Fresh X (HeldReadStateScope.scope source)) :
    firing.Fresh X := by
  have core := HeldReadScopeReassociation.datum_fresh X (HeldReadStateScope.scope source)
    firing.ext (consumerMember X firing consumer) (datumMember firing) same joint
  intro target caller assignment
  obtain ⟨combined, kept, locals⟩ := core target caller assignment
  refine ⟨combined, ?_, ?_⟩
  · intro term mentioned
    exact kept term ((HeldReadStateScope.mentions_iff source term).mpr mentioned)
  · intro term member
    apply locals term
    change term ∈ (specScope firing.spec).terms
    rwa [specScope_terms]

theorem consumer_fresh (firing : RFiring O R E codes source)
    (consumer : RFiring O R (HeldReadScopeReassociation.identityExtensions X) codes (firing.result X))
    (ambient : Set C) (available : source.Available ambient firing.use)
    (noTake : firing.spec.body.take = []) (noRead : firing.spec.body.read = [])
    (noTaken : firing.selection.taken = []) (out : O) (value : Tm firing.spec.locals)
    (made : firing.selection.made = [out]) (produced : firing.spec.body.produce = [value])
    (noMadeRules : firing.madeRules = [])
    (joint : (scopes X firing consumer).Fresh X (HeldReadStateScope.scope source)) :
    consumer.Fresh X := by
  let old := HeldReadStateScope.scope source
  let later := HeldReadStateScope.scope (firing.result X)
  have span : ∀ term,
      (⟨E.target firing.ext, later.knowledge, later.present, later.label⟩ :
        RuleSyntax.State Tm (Tm (E.target firing.ext))).Mentions term →
      (∃ prior, old.Mentions prior ∧ term = X.act (E.weaken firing.ext) prior) ∨
        (∃ datumTerm, datumTerm ∈ (datumMember firing).rule.terms ∧
          term = X.act (datumMember firing).opening datumTerm) := by
    intro term mentioned
    have actual := (HeldReadStateScope.mentions_iff (firing.result X) term).mp mentioned
    have images := HeldReadDatumSpan.result_mentions_span X firing ambient available noTake noRead
      noTaken out value made produced noMadeRules term actual
    rcases images with ⟨prior, priorMentioned, equality⟩ | ⟨datumTerm, member, equality⟩
    · exact Or.inl ⟨prior, (HeldReadStateScope.mentions_iff source prior).mpr priorMentioned, equality⟩
    · refine Or.inr ⟨datumTerm, ?_, equality⟩
      change datumTerm ∈ (specScope firing.spec).terms
      rwa [specScope_terms]
  have residual := HeldReadScopeReassociation.fresh_after_datum_span X old firing.ext
    (consumerMember X firing consumer) (datumMember firing)
    later.knowledge later.present later.label joint span
  intro target caller assignment
  obtain ⟨combined, kept, locals⟩ := residual target caller assignment
  refine ⟨combined, ?_, ?_⟩
  · intro term mentioned
    exact kept term ((HeldReadStateScope.mentions_iff (firing.result X) term).mpr mentioned)
  · intro term member
    apply locals term
    change term ∈ (specScope consumer.spec).terms
    rwa [specScope_terms]

#print axioms datum_fresh
#print axioms consumer_fresh

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadFreshStaging
