import Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationEvidence
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompilePremiseProfile

/-!
# Exact PeTTa call-guard premise evidence

The cold call-guard compiler uses seven private relation names for its
guarded authored transitions.  This module proves that the concrete PeTTa
relation environment is an exact deterministic echo-or-empty table and that
none of those names overlaps the MeTTaIL builtin relation.

Consequently a well-typed, fully bound decoded PeTTa guard premise receives
the generic exact evidence contract: it has independent relation meaning
exactly when ordinary premise evaluation succeeds, and success preserves the
binding environment.  The relation environment remains the only authority
for the answer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompilePremiseEvidence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.RelationQueryAdmission
open Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationPremise
open Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationEvidence
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompilePremiseProfile

/-- The small table constructor used by the cold relation environment can
only return its exact input row or no row. -/
private theorem rowWhen_echo_or_empty (condition : Bool)
    (arguments : List Pattern) :
    rowWhen condition arguments = [arguments] ∨
      rowWhen condition arguments = [] := by
  cases condition <;> simp [rowWhen]

/-- Every query to the concrete cold relation environment is deterministic
and answer-preserving.  Unsupported names and arities are the empty case. -/
theorem relationEnv_echo_or_empty (relation : String)
    (arguments : List Pattern) :
    relationEnv.tuples relation arguments = [arguments] ∨
      relationEnv.tuples relation arguments = [] := by
  cases arguments with
  | nil => simp [relationEnv]
  | cons first rest =>
      cases rest with
      | nil =>
          simp only [relationEnv]
          repeat' first | split | exact rowWhen_echo_or_empty _ _ | simp
      | cons second tail =>
          cases tail with
          | nil =>
              simp only [relationEnv]
              repeat' first | split | exact rowWhen_echo_or_empty _ _ | simp
          | cons third more => simp [relationEnv]

/-- Exact finite inventory of relation names authored by the cold compiler. -/
def SupportedRelation (relation : String) : Prop :=
  relation ∈
    [ notEqualRelation, arityMatchesRelation, arityDiffersRelation
    , checkedInputRelation, openInputRelation, checkedResultRelation
    , openResultRelation ]

/-- The seven private PeTTa relations cannot collide with the builtin
equality relation. -/
theorem supportedRelation_ne_builtinEq {relation : String}
    (supported : SupportedRelation relation) : relation ≠ "eq" := by
  simp [SupportedRelation, notEqualRelation, arityMatchesRelation,
    arityDiffersRelation, checkedInputRelation, openInputRelation,
    checkedResultRelation, openResultRelation] at supported
  rcases supported with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- A supported PeTTa query has no competing builtin tuple source. -/
theorem supportedRelation_noBuiltin (language : LanguageDef)
    {relation : String} (supported : SupportedRelation relation)
    (arguments : List Pattern) :
    builtinRelationTuples language relation arguments = [] := by
  have different := supportedRelation_ne_builtinEq supported
  cases arguments with
  | nil => simp [builtinRelationTuples]
  | cons first rest =>
      cases rest with
      | nil => simp [builtinRelationTuples]
      | cons second tail =>
          cases tail with
          | nil => simp [builtinRelationTuples, different]
          | cons third more => simp [builtinRelationTuples]

/-- Instantiate the generic exact evidence contract for a supported PeTTa
query.  The caller supplies source typing and concrete binding alignment, but
does not supply or precompute the query answer. -/
def echoContract {language : LanguageDef} {rewrite : RewriteRule}
    {view : View rewrite} {bindings : Bindings}
    (supported : SupportedRelation view.relation)
    (typed : view.WellTyped) (bound : BoundArguments view bindings) :
    EchoContract relationEnv language view bindings :=
  EchoContract.ofEchoOrEmpty typed bound
    (supportedRelation_noBuiltin language supported bound.values)
    (relationEnv_echo_or_empty view.relation bound.values)

/-! ## Authored-root coverage -/

/-- One authored premise uses one of the seven private cold relation names. -/
def PremiseUsesSupportedRelation : Premise → Prop
  | .relationQuery relation _ => SupportedRelation relation
  | _ => False

/-- Every premise in an authored rewrite uses the private cold relation
surface. -/
def PremisesUseSupportedRelations (rewrite : RewriteRule) : Prop :=
  ∀ premise ∈ rewrite.premises, PremiseUsesSupportedRelation premise

/-- All fifteen authored roots use only the exact seven-name inventory.  The
finite proof inspects source rewrites rather than generated typing rows. -/
theorem rootPremises_useSupportedRelations
    (index : Fin coldSource.language.rewrites.length) :
    PremisesUseSupportedRelations (rootTyping index).site.rewrite := by
  fin_cases index <;>
    simp [PremisesUseSupportedRelations, PremiseUsesSupportedRelation,
      SupportedRelation, rootTyping,
      Mettapedia.OSLF.Framework.DisplayedRewriteSite.rewrite,
      Mettapedia.OSLF.Framework.DisplayedRewriteSite.root,
      coldSource, language, transitions, finishTransition,
      skipHeadTransition, skipArityTransition, beginDeclarationTransition,
      argumentsFinishedTransition, rawInputTransition,
      undefinedInputTransition, holeInputTransition,
      checkedInputTransition, openInputTransition,
      undefinedResultTransition, holeResultTransition, atomResultTransition,
      checkedResultTransition, openResultTransition,
      inputStepTransition, resultStepTransition, query, v,
      notEqualRelation, arityMatchesRelation, arityDiffersRelation,
      checkedInputRelation, openInputRelation, checkedResultRelation,
      openResultRelation]

/-- Any typed view reconstructing an authored root premise inherits the
root's supported-relation evidence. -/
theorem supportedRelation_of_rootView
    (index : Fin coldSource.language.rewrites.length)
    {view : View (rootTyping index).site.rewrite}
    (membership : view.encode ∈ (rootTyping index).site.rewrite.premises) :
    SupportedRelation view.relation := by
  have supported := rootPremises_useSupportedRelations index
    view.encode membership
  simpa [PremiseUsesSupportedRelation, View.encode] using supported

/-- Successful exact decoding of an authored premise cannot introduce a
foreign relation name. -/
theorem supportedRelation_of_root_decode
    (index : Fin coldSource.language.rewrites.length)
    {premise : Premise}
    (membership : premise ∈ (rootTyping index).site.rewrite.premises)
    {view : View (rootTyping index).site.rewrite}
    (decoded : decode? (rootTyping index).site.rewrite premise = some view) :
    SupportedRelation view.relation := by
  have supported := rootPremises_useSupportedRelations index premise membership
  have encoded := encode_of_decode?_eq_some decoded
  rw [← encoded] at supported
  simpa [PremiseUsesSupportedRelation, View.encode] using supported

/-! ## Ordered root rows -/

/-- Build the exact ordered contract row from pointwise source-derived
support, typing, and concrete binding alignment. -/
def contractRowOf {language : LanguageDef} {rewrite : RewriteRule}
    {bindings : Bindings} (views : List (View rewrite))
    (supported : ∀ view ∈ views, SupportedRelation view.relation)
    (typed : ∀ view ∈ views, view.WellTyped)
    (bound : ∀ view ∈ views, BoundArguments view bindings) :
    ContractRow relationEnv language bindings views := by
  induction views with
  | nil => exact .nil
  | cons head tail inductionHypothesis =>
      exact .cons
        (echoContract (supported head (by simp))
          (typed head (by simp)) (bound head (by simp)))
        (inductionHypothesis
          (fun view membership => supported view (by simp [membership]))
          (fun view membership => typed view (by simp [membership]))
          (fun view membership => bound view (by simp [membership])))

/-- The exact view row of one authored root receives an ordered PeTTa echo
contract.  Encoding equality is proof-relevant: it preserves premise order
and repeated occurrences. -/
def rootContractRow
    (index : Fin coldSource.language.rewrites.length)
    {bindings : Bindings}
    (views : List (View (rootTyping index).site.rewrite))
    (encoded :
      views.map View.encode = (rootTyping index).site.rewrite.premises)
    (typed : ∀ view ∈ views, view.WellTyped)
    (bound : ∀ view ∈ views, BoundArguments view bindings) :
    ContractRow relationEnv language bindings views :=
  contractRowOf views
    (fun view membership =>
      supportedRelation_of_rootView index (by
        rw [← encoded]
        exact List.mem_map_of_mem membership))
    typed bound

/-- Crown theorem for one authored cold root: its independently meaningful
ordered relation row is equivalent to the ordinary `PremisesAt` execution,
and successful execution preserves the matched source bindings exactly. -/
theorem rootPremisesAt_iff_meanings
    (index : Fin coldSource.language.rewrites.length)
    {fuel : Nat} {bindings final : Bindings}
    (views : List (View (rootTyping index).site.rewrite))
    (encoded :
      views.map View.encode = (rootTyping index).site.rewrite.premises)
    (typed : ∀ view ∈ views, view.WellTyped)
    (bound : ∀ view ∈ views, BoundArguments view bindings) :
    PremisesAt (engineBasePremises relationEnv) language fuel bindings
        (rootTyping index).site.rewrite.premises final ↔
      ContractRow.Meanings relationEnv bindings views ∧ final = bindings := by
  rw [← encoded]
  exact (rootContractRow index views encoded typed bound).premisesAt_iff_meanings

/-! ## Canonical decoded root rows -/

/-- The shared exact decoder succeeds for every one of the fifteen authored
cold roots. -/
theorem rootViews?_isSome
    (index : Fin coldSource.language.rewrites.length) :
    (decodeViews? (rootTyping index).site.rewrite).isSome = true := by
  obtain ⟨views, decoded⟩ :=
    exists_decodeViews?_eq_some_of_sourceBound (rootTyping index)
      (rootPremises_sourceBound index)
  simp [decoded]

/-- Canonical source-computed view row for one cold root. -/
def rootViews (index : Fin coldSource.language.rewrites.length) :
    List (View (rootTyping index).site.rewrite) :=
  (decodeViews? (rootTyping index).site.rewrite).get
    (rootViews?_isSome index)

/-- The canonical view row is exactly the successful output of the shared
decoder, not a separately authored inventory. -/
theorem rootViews_decoded
    (index : Fin coldSource.language.rewrites.length) :
    decodeViews? (rootTyping index).site.rewrite = some (rootViews index) :=
  (Option.some_get (rootViews?_isSome index)).symm

/-- Canonical view encoding reconstructs the complete authored premise row. -/
theorem rootViews_encoded
    (index : Fin coldSource.language.rewrites.length) :
    (rootViews index).map View.encode =
      (rootTyping index).site.rewrite.premises :=
  encodeViews_of_decodeViews?_eq_some (rootViews_decoded index)

/-- Every canonical root view carries the source-derived authored type row. -/
theorem rootViews_typed
    (index : Fin coldSource.language.rewrites.length) :
    ∀ view ∈ rootViews index, view.WellTyped :=
  wellTyped_of_mem_decodeViews?_eq_some (rootViews_decoded index)

/-- Final exact boundary for the canonical root row.  The only remaining
runtime hypothesis is the unavoidable one: source matching supplied concrete
bindings for every authored query argument. -/
theorem rootPremisesAt_iff_rootMeanings
    (index : Fin coldSource.language.rewrites.length)
    {fuel : Nat} {bindings final : Bindings}
    (bound : ∀ view ∈ rootViews index, BoundArguments view bindings) :
    PremisesAt (engineBasePremises relationEnv) language fuel bindings
        (rootTyping index).site.rewrite.premises final ↔
      ContractRow.Meanings relationEnv bindings (rootViews index) ∧
        final = bindings :=
  rootPremisesAt_iff_meanings index (rootViews index)
    (rootViews_encoded index) (rootViews_typed index) bound

/-! ## Negative controls -/

/-- A foreign relation name is outside the exact cold inventory. -/
theorem foreignRelation_not_supported :
    ¬ SupportedRelation "PeTTaCallGuardForeign" := by
  simp [SupportedRelation, notEqualRelation, arityMatchesRelation,
    arityDiffersRelation, checkedInputRelation, openInputRelation,
    checkedResultRelation, openResultRelation]

/-- No reconstructed authored root view can silently carry a foreign
relation name. -/
theorem foreignRelation_view_not_authored
    (index : Fin coldSource.language.rewrites.length)
    {view : View (rootTyping index).site.rewrite}
    (foreign : view.relation = "PeTTaCallGuardForeign") :
    view.encode ∉ (rootTyping index).site.rewrite.premises := by
  intro membership
  have supported := supportedRelation_of_rootView index membership
  rw [foreign] at supported
  exact foreignRelation_not_supported supported

#print axioms relationEnv_echo_or_empty
#print axioms supportedRelation_ne_builtinEq
#print axioms supportedRelation_noBuiltin
#print axioms rootPremises_useSupportedRelations
#print axioms supportedRelation_of_rootView
#print axioms supportedRelation_of_root_decode
#print axioms rootPremisesAt_iff_meanings
#print axioms rootViews_decoded
#print axioms rootViews_encoded
#print axioms rootPremisesAt_iff_rootMeanings
#print axioms foreignRelation_view_not_authored

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompilePremiseEvidence
