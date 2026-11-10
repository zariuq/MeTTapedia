import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationSchemaPreparation
import Mathlib.Data.List.FinRange

/-! # Complete physical preparation and scalar readback of schema views

The physical operation opens every selected port and every rule position.
Order, multiplicity and the reserved scope ledger survive readback. This
bundle contains prepared views, not a replacement for the firing's admission,
publication recipes or retained origin data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.SchemaPreparation

open Mettapedia.OSLF
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

structure Views (T : Type) where
  rule : RuleInstance T
  taken : List T
  read : List T
  occupied : Finset Nat

def Views.map {T U : Type} (write : T → U) (views : Views T) : Views U :=
  ⟨views.rule.map write, views.taken.map write, views.read.map write, views.occupied⟩

def Views.traverse? {T U : Type} (decode : T → Option U) (views : Views T) : Option (Views U) := do
  return ⟨← views.rule.traverse? decode, ← views.taken.mapM decode,
    ← views.read.mapM decode, views.occupied⟩

private theorem mapM_read_map {T U : Type} (write : T → U) (read : U → Option T)
    (roundtrip : ∀ term, read (write term) = some term) (terms : List T) :
    (terms.map write).mapM read = some terms := by
  induction terms with
  | nil => rfl
  | cons first rest earlier =>
      simp only [List.map_cons, List.mapM_cons, roundtrip, earlier]
      rfl

theorem Views.traverse_map {T U : Type} (write : T → U) (read : U → Option T)
    (roundtrip : ∀ term, read (write term) = some term) (views : Views T) :
    (views.map write).traverse? read = some views := by
  cases views
  simp only [Views.map, Views.traverse?, RuleInstance.traverse?_map write read roundtrip,
    mapM_read_map write read roundtrip]
  rfl

variable {S : Signature} {Local Shared O : Type}
  (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
  (code : Intrinsic.HeadPresentation (TargetSignature locals captures))

def viewsOf {selection : Selection O} {Γ : Ctx S} {sort : S.Srt}
    (views : ContextualSelectionViews.Prepared locals captures selection Γ sort) :
    Views (Term (TargetSignature locals captures) Γ sort) :=
  ⟨views.rule, List.ofFn views.taken, List.ofFn views.read, views.occupied⟩

def prepareViews? (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) : Option (Views Payloads.Term) := do
  let preparedRule ← openRule? locals captures code
    (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.rulePort selection)) rule
  let taken ← (List.finRange selection.taken.length).mapM (fun port =>
    (ContextualABTPreparation.takeAt locals captures occupied selection rows port).map
      (encodePhysical locals captures code))
  let read ← (List.finRange selection.read.length).mapM (fun port =>
    (ContextualABTPreparation.readAt locals captures occupied selection rows port).map
      (encodePhysical locals captures code))
  return ⟨preparedRule, taken, read, ContextualActivationScopes.after occupied selection⟩

theorem prepareViews_exact (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) :
    prepareViews? locals captures code occupied selection rule rows =
      some ((viewsOf locals captures
        (ContextualActivatedStep.prepared locals captures occupied selection rule rows)).map (Intrinsic.lower code)) := by
  have takes (port : Fin selection.taken.length) :
      (ContextualABTPreparation.takeAt locals captures occupied selection rows port).map
        (encodePhysical locals captures code) =
      some (Intrinsic.lower code
        ((ContextualActivatedStep.prepared locals captures occupied selection rule rows).taken port)) := by
    rw [ContextualABTPreparation.take_exact locals captures occupied selection rule rows port]
    rfl
  have reads (port : Fin selection.read.length) :
      (ContextualABTPreparation.readAt locals captures occupied selection rows port).map
        (encodePhysical locals captures code) =
      some (Intrinsic.lower code
        ((ContextualActivatedStep.prepared locals captures occupied selection rule rows).read port)) := by
    rw [ContextualABTPreparation.read_exact locals captures occupied selection rule rows port]
    rfl
  simp only [prepareViews?, openRule_exact, list_mapM_some _ _ takes, list_mapM_some _ _ reads]
  simp only [viewsOf, Views.map, List.ofFn_eq_map, List.map_map]
  rfl

variable [DecidableEq S.Srt]

def readViews? (Γ : Ctx S) (sort : S.Srt) (views : Views Payloads.Term) :
    Option (Views (Term (TargetSignature locals captures) Γ sort)) :=
  views.traverse? (Intrinsic.read? code Γ sort)

theorem readViews_mapped {Γ : Ctx S} {sort : S.Srt}
    (views : Views (Term (TargetSignature locals captures) Γ sort)) :
    readViews? locals captures code Γ sort (views.map (Intrinsic.lower code)) = some views :=
  Views.traverse_map _ _ (Intrinsic.read_lower code) views

theorem prepared_views_readback (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) {physical : Views Payloads.Term}
    (computed : prepareViews? locals captures code occupied selection rule rows = some physical) :
    readViews? locals captures code Γ sort physical =
      some (viewsOf locals captures (ContextualActivatedStep.prepared locals captures occupied selection rule rows)) := by
  rw [prepareViews_exact] at computed
  rw [← Option.some.inj computed]
  exact readViews_mapped locals captures code _

/-- Each component is source in its existing authored sort; the ledger is
retained metadata, not inferred from the decoded terms. -/
structure SourceViews where
  rule : List Nat
  taken : List (List Nat)
  read : List (List Nat)
  occupied : Finset Nat

def printViews (views : Views Payloads.Term) : SourceViews :=
  ⟨Source.ruleInput views.rule, views.taken.map Source.termInput,
    views.read.map Source.termInput, views.occupied⟩

noncomputable def readSourceViews? (Γ : Ctx S) (sort : S.Srt) (source : SourceViews) :
    Option (Views (Term (TargetSignature locals captures) Γ sort)) := do
  return ⟨← readRuleSource? locals captures code Γ sort source.rule,
    ← source.taken.mapM (Intrinsic.readSource? code Γ sort),
    ← source.read.mapM (Intrinsic.readSource? code Γ sort), source.occupied⟩

theorem readSourceViews_print {Γ : Ctx S} {sort : S.Srt}
    (views : Views (Term (TargetSignature locals captures) Γ sort)) :
    readSourceViews? locals captures code Γ sort (printViews (views.map (Intrinsic.lower code))) = some views := by
  have terms (values : List (Term (TargetSignature locals captures) Γ sort)) :
      ((values.map (Intrinsic.lower code)).map Source.termInput).mapM
        (Intrinsic.readSource? code Γ sort) = some values := by
    simpa only [List.map_map, Function.comp_def] using
      mapM_read_map (fun value => Source.termInput (Intrinsic.lower code value))
        (Intrinsic.readSource? code Γ sort) (fun value => Intrinsic.readSource_print code value) values
  cases views
  simp only [readSourceViews?, printViews, Views.map, readRuleSource_print, terms]
  rfl

theorem prepared_source_views_readback (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) {physical : Views Payloads.Term}
    (computed : prepareViews? locals captures code occupied selection rule rows = some physical) :
    readSourceViews? locals captures code Γ sort (printViews physical) =
      some (viewsOf locals captures (ContextualActivatedStep.prepared locals captures occupied selection rule rows)) := by
  rw [prepareViews_exact] at computed
  rw [← Option.some.inj computed]
  exact readSourceViews_print locals captures code _

noncomputable def sourceViewsPresentation :
    Mettapedia.GSLT.Parsing.ExactPresentation.Presentation
      (fun index : Intrinsic.Index S => Views (Term (TargetSignature locals captures) index.1 index.2))
      (fun _ => SourceViews) where
  key := ⟨code.key.name ++ ".prepared-views", code.key.version⟩
  view views := printViews (views.map (Intrinsic.lower code))
  expand {sort} := readSourceViews? locals captures code sort.1 sort.2
  expand_view := readSourceViews_print locals captures code

theorem wrong_document_key_refused (index : Intrinsic.Index S)
    (document : Mettapedia.GSLT.Parsing.ExactPresentation.Document (fun _ : Intrinsic.Index S => SourceViews) index)
    (different : document.key ≠ (sourceViewsPresentation locals captures code).key) :
    Mettapedia.GSLT.Parsing.ExactPresentation.expandDocument
      (sourceViewsPresentation locals captures code) document = none :=
  Mettapedia.GSLT.Parsing.ExactPresentation.expandDocument_wrong_key _ _ different

theorem prepared_document_readback (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) {physical : Views Payloads.Term}
    (computed : prepareViews? locals captures code occupied selection rule rows = some physical) :
    Mettapedia.GSLT.Parsing.ExactPresentation.expandDocument
      (sourceViewsPresentation locals captures code)
      (sort := (Γ, sort)) ⟨(sourceViewsPresentation locals captures code).key, printViews physical⟩ =
        some (viewsOf locals captures (ContextualActivatedStep.prepared locals captures occupied selection rule rows)) := by
  simp only [Mettapedia.GSLT.Parsing.ExactPresentation.expandDocument]
  exact prepared_source_views_readback locals captures code occupied selection rule rows computed

#print axioms prepareViews_exact
#print axioms prepared_source_views_readback
#print axioms prepared_document_readback

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.SchemaPreparation
