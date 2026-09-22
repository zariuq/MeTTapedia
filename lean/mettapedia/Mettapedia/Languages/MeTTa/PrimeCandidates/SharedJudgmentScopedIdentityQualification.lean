import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanNamedRegion
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeDecidableIdentity
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanInterpretation
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanPreservation

/-!
# Joint scoped identity qualification in the native Boolean/J fragment

The profile uses propositional identity witnesses. A proved region and an
explicitly assumed local region have the same application rule, but different
source scopes. Exporting from an assumed region retains its Pi premise;
discharge supplies an actual typed witness. Neither operation changes native
conversion or the retained source syntax.

All typing, substitution and named-application laws below use the same native
Boolean/J rules. The guest compatibility statements are conditional boundaries,
not constructions of univalence or assumptions of global native UIP.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentScopedIdentityQualification

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.Declaration Presentation.FormationSensitive RussellTarski
open FormationSensitiveBasedIdentity (doubleWeaken)
open SharedJudgmentNativeBooleanRegion (boolTm zero one)
open SharedJudgmentNamedIdentityRegions
open Mettapedia.TypeTheory.NamedValueContexts
open Mettapedia.TypeTheory.RetainedPresentationViews
open Mettapedia.Machines
open Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation
open _root_.CategoryTheory
open FormationSensitiveContextual

abbrev rules : Rules Tower.Head := SharedJudgmentNativeBooleanRegion.rules

variable {n m : Nat} {context : Tower.Ctx n}

def tripleWeaken (term : Tower.Tm n) : Tower.Tm (n + 3) := rename wk (doubleWeaken term)
def quadrupleWeaken (term : Tower.Tm n) : Tower.Tm (n + 4) := rename wk (tripleWeaken term)

/-- A local uniqueness principle is an ordinary four-argument native type. -/
def regionType (carrier : Tower.Tm n) : Tower.Tm n :=
  .pi carrier (.pi (rename wk carrier)
    (.pi (.id (doubleWeaken carrier) (.var 1) (.var 0))
      (.pi (.id (tripleWeaken carrier) (.var 2) (.var 1))
        (.id (.id (quadrupleWeaken carrier) (.var 3) (.var 2)) (.var 1) (.var 0)))))

@[simp] theorem regionType_substitute (sigma : Sub Tower.Head n m) (carrier : Tower.Tm n) :
    subst sigma (regionType carrier) = regionType (subst sigma carrier) := by
  simp only [regionType, subst, doubleWeaken, tripleWeaken, quadrupleWeaken,
    subst_liftSub_wk, liftSub]
  rfl

@[simp] theorem regionType_rename (rho : Ren n m) (carrier : Tower.Tm n) :
    rename rho (regionType carrier) = regionType (rename rho carrier) := by
  simpa only [subst_renSub] using regionType_substitute (renSub rho) carrier

theorem regionType_formed {carrier : Tower.Tm n}
    (carrierFormed : Typing rules context carrier (sortTm zero)) :
    Typing rules context (regionType carrier) (sortTm zero) := by
  apply SharedJudgmentNativeBooleanRegion.pi_formed carrierFormed
  apply SharedJudgmentNativeBooleanRegion.pi_formed carrierFormed.weaken
  apply SharedJudgmentNativeBooleanRegion.pi_formed
    (.idForm carrierFormed.weaken.weaken (.sort zero) (.var 1) (.var 0))
  apply SharedJudgmentNativeBooleanRegion.pi_formed
    (.idForm carrierFormed.weaken.weaken.weaken (.sort zero) (.var 2) (.var 1))
  exact .idForm (.idForm carrierFormed.weaken.weaken.weaken.weaken (.sort zero) (.var 3) (.var 2))
    (.sort zero) (.var 1) (.var 0)

def basedRegionType (carrier left : Tower.Tm n) : Tower.Tm n :=
  .pi carrier (.pi (.id (rename wk carrier) (rename wk left) (.var 0))
    (.pi (.id (doubleWeaken carrier) (doubleWeaken left) (.var 1))
      (.id (.id (tripleWeaken carrier) (tripleWeaken left) (.var 2)) (.var 1) (.var 0))))

theorem regionType_after_left (carrier left : Tower.Tm n) :
    inst0 left (.pi (rename wk carrier)
      (.pi (.id (doubleWeaken carrier) (.var 1) (.var 0))
        (.pi (.id (tripleWeaken carrier) (.var 2) (.var 1))
          (.id (.id (quadrupleWeaken carrier) (.var 3) (.var 2)) (.var 1) (.var 0))))) =
      basedRegionType carrier left := by
  simp only [inst0, subst, doubleWeaken, tripleWeaken, quadrupleWeaken,
    subst_liftSub_wk, SharedJudgmentNativeHedberg.subst0_weaken, subst0,
    basedRegionType, liftSub]
  rfl

theorem basedRegionType_after_right (carrier left right : Tower.Tm n) :
    inst0 right (.pi (.id (rename wk carrier) (rename wk left) (.var 0))
      (.pi (.id (doubleWeaken carrier) (doubleWeaken left) (.var 1))
        (.id (.id (tripleWeaken carrier) (tripleWeaken left) (.var 2)) (.var 1) (.var 0)))) =
      SharedJudgmentNativeBooleanConstancy.pathPairType (.id carrier left right) := by
  simp only [inst0, subst, doubleWeaken, tripleWeaken,
    subst_liftSub_wk, SharedJudgmentNativeHedberg.subst0_weaken, subst0,
    SharedJudgmentNativeBooleanConstancy.pathPairType, rename, liftSub]
  rfl

def applyRegion (region left right first second : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.app region left) right) first) second

@[simp] theorem applyRegion_substitute (sigma : Sub Tower.Head n m)
    (region left right first second : Tower.Tm n) :
    subst sigma (applyRegion region left right first second) =
      applyRegion (subst sigma region) (subst sigma left) (subst sigma right)
        (subst sigma first) (subst sigma second) := rfl

/-- Region application consumes a typed region witness, never a scope name,
origin tag or an assumption that its intended result already holds. -/
theorem applyRegion_typed {carrier region left right first second : Tower.Tm n}
    (regionTyped : Typing rules context region (regionType carrier))
    (leftTyped : Typing rules context left carrier)
    (rightTyped : Typing rules context right carrier)
    (firstTyped : Typing rules context first (.id carrier left right))
    (secondTyped : Typing rules context second (.id carrier left right)) :
    Typing rules context (applyRegion region left right first second)
      (.id (.id carrier left right) first second) := by
  have firstApplication : Typing rules context (.app region left) (basedRegionType carrier left) := by
    simpa only [regionType, regionType_after_left] using Typing.appElim regionTyped leftTyped
  have secondApplication : Typing rules context (.app (.app region left) right)
      (SharedJudgmentNativeBooleanConstancy.pathPairType (.id carrier left right)) := by
    simpa only [basedRegionType, basedRegionType_after_right] using Typing.appElim firstApplication rightTyped
  exact SharedJudgmentNativeBooleanConstancy.pathPair_apply_typed secondApplication firstTyped secondTyped

/-- A region assumption extends the mathematical context rather than adding
an equality equation to the underlying rules. -/
def assumedContext (context : Tower.Ctx n) (carrier : Tower.Tm n) : Tower.Ctx (n + 1) :=
  .snoc context (regionType carrier)

theorem assumed_context_formed {carrier : Tower.Tm n}
    (formed : ContextFormation rules context)
    (carrierFormed : Typing rules context carrier (sortTm zero)) :
    ContextFormation rules (assumedContext context carrier) :=
  .snoc formed (regionType_formed carrierFormed) (.sort zero)

theorem local_region_typed (carrier : Tower.Tm n) :
    Typing rules (assumedContext context carrier) (.var 0) (regionType (rename wk carrier)) := by
  simpa only [assumedContext, Ctx.lookup_snoc_zero, regionType_rename] using
    (Typing.var (R := rules) (Γ := assumedContext context carrier) 0)

def exportAssumption (body : Tower.Tm (n + 1)) : Tower.Tm n := .lam body

/-- Export works for every admitted result family, including one that really
depends on the assumed region witness. It retains that dependency in Pi. -/
theorem conditional_export {carrier : Tower.Tm n} {body result : Tower.Tm (n + 1)}
    (judgment : Judgment rules (assumedContext context carrier) body result) :
    Judgment rules context (exportAssumption body) (.pi (regionType carrier) result) :=
  SharedJudgmentNativeIdentityExtension.abstract_judgment judgment

theorem conditional_discharge {carrier region : Tower.Tm n} {body result : Tower.Tm (n + 1)}
    (judgment : Judgment rules (assumedContext context carrier) body result)
    (regionTyped : Typing rules context region (regionType carrier)) :
    Judgment rules context (.app (exportAssumption body) region) (inst0 region result) :=
  ⟨(conditional_export judgment).context, .appElim (conditional_export judgment).typing regionTyped⟩

theorem discharge_beta (body : Tower.Tm (n + 1)) (region : Tower.Tm n) :
    Conv rules.headEq (.app (exportAssumption body) region) (inst0 region body) rules.computation :=
  .rel _ _ (.betaPi body region)

theorem conditional_export_substitute (sigma : Sub Tower.Head n m) (body : Tower.Tm (n + 1)) :
    subst sigma (exportAssumption body) = exportAssumption (subst (liftSub sigma) body) := rfl

/-- A target scope receives the same region assumption after reindexing.
The typed lift is constructed from the supplied ordinary substitution. -/
theorem assumed_scope_reindex {target : Tower.Ctx m} {sigma : Sub Tower.Head n m}
    (typed : FormationSensitive.CtxMor rules context target sigma) (carrier : Tower.Tm n) :
    FormationSensitive.CtxMor rules (assumedContext context carrier)
      (assumedContext target (subst sigma carrier)) (liftSub sigma) := by
  simpa only [assumedContext, regionType_substitute] using typed.lift (regionType carrier)

/-- The Boolean theorem is independently derived in this very rules instance. -/
theorem boolean_region_derived (context : Tower.Ctx n) (formed : ContextFormation rules context) :
    Typing rules context SharedJudgmentNativeBooleanConstancy.region (regionType boolTm) :=
  SharedJudgmentNativeBooleanConstancy.region_typed formed

/-- Region admission from a native equality decision is theorem application,
not the installation of a new identity axiom. -/
def regionFromDecision (carrier decision : Tower.Tm n) : Tower.Tm n :=
  .app (.app (liftClosed SharedJudgmentNativeDecidableIdentity.hedbergClosed) carrier) decision

theorem regionFromDecision_typed {carrier decision : Tower.Tm n}
    (carrierFormed : Typing rules context carrier (sortTm zero))
    (decisionTyped : Typing rules context decision
      (SharedJudgmentNativeDecidableIdentity.decidableEqualityType carrier)) :
    Typing rules context (regionFromDecision carrier decision) (regionType carrier) := by
  have closed : Typing rules context
      (liftClosed SharedJudgmentNativeDecidableIdentity.hedbergClosed)
      (liftClosed SharedJudgmentNativeDecidableIdentity.hedbergClosedType) :=
    SharedJudgmentNativeDecidableIdentity.hedbergClosed_judgment.typing.renameTyping
      (fun index => Fin.elim0 index)
  change Typing rules context _ (.pi (sortTm zero)
    (.pi (SharedJudgmentNativeDecidableIdentity.decidableEqualityType (.var 0))
      (regionType (.var 1)))) at closed
  have first : Typing rules context
      (.app (liftClosed SharedJudgmentNativeDecidableIdentity.hedbergClosed) carrier)
      (.pi (SharedJudgmentNativeDecidableIdentity.decidableEqualityType carrier)
        (regionType (rename wk carrier))) := by
    have application := Typing.appElim closed carrierFormed
    have atOne : liftSub (subst0 carrier) (1 : Fin (n + 2)) = rename wk carrier := by
      rw [← Fin.succ_zero_eq_one]
      rfl
    simpa only [inst0, subst, SharedJudgmentNativeDecidableIdentity.decidableEqualityType,
      SharedJudgmentNativeDecidableIdentity.basedDecisionType_subst, subst_liftSub_wk,
      regionType_substitute, atOne, liftSub_zero, subst0, Fin.cases_zero] using application
  simpa only [regionFromDecision, inst0, regionType_substitute,
    SharedJudgmentNativeHedberg.subst0_weaken] using
    Typing.appElim first decisionTyped

def congruenceArguments (domain left codomain function right witness : Tower.Tm n) : Sub Tower.Head 6 n :=
  consSub witness (consSub right (consSub left (consSub function (consSub codomain
    (consSub domain (fun index => Fin.elim0 index))))))

/-- The admitted consumer is a genuine native function. Its congruence proof
is imported before the Boolean computation extension and then instantiated,
so the extension's roots are retained. -/
theorem congruence_typed {domain left codomain function right witness : Tower.Tm n}
    (domainFormed : Typing rules context domain (sortTm one))
    (codomainFormed : Typing rules context codomain (sortTm one))
    (leftTyped : Typing rules context left domain)
    (rightTyped : Typing rules context right domain)
    (functionTyped : Typing rules context function (SharedJudgmentIdentityRegions.arrow domain codomain))
    (witnessTyped : Typing rules context witness (.id domain left right)) :
    Typing rules context (SharedJudgmentIdentityRegions.congruenceTerm domain left codomain function right witness)
      (.id codomain (.app function left) (.app function right)) := by
  have parameters : FormationSensitive.CtxMor rules
      (SharedJudgmentIdentityRegions.Controls.assumedContext (fun _ => one)) context
      (congruenceArguments domain left codomain function right witness) :=
    Fin.cases witnessTyped (Fin.cases rightTyped (Fin.cases leftTyped
      (Fin.cases functionTyped (Fin.cases codomainFormed
        (Fin.cases domainFormed (fun index => Fin.elim0 index))))))
  have application :=
    ((SharedJudgmentIdentityRegions.Controls.assumed_example (fun _ => one) Signature.empty).typing.includeSignature
      SharedJudgmentNativeBooleanRegion.signature).substitute parameters
  simp only [SharedJudgmentIdentityRegions.congruenceTerm_substitute, subst] at application
  exact application

/-- Any function admitted by this fragment can use either equality proof.
The conclusion is a native identity witness, not raw syntax identification. -/
theorem region_consumer_interchange {carrier region left right first second codomain consumer : Tower.Tm n}
    (carrierFormed : Typing rules context carrier (sortTm zero))
    (codomainFormed : Typing rules context codomain (sortTm one))
    (regionTyped : Typing rules context region (regionType carrier))
    (leftTyped : Typing rules context left carrier)
    (rightTyped : Typing rules context right carrier)
    (firstTyped : Typing rules context first (.id carrier left right))
    (secondTyped : Typing rules context second (.id carrier left right))
    (consumerTyped : Typing rules context consumer
      (SharedJudgmentIdentityRegions.arrow (.id carrier left right) codomain)) :
    Typing rules context
      (SharedJudgmentIdentityRegions.congruenceTerm (.id carrier left right) first codomain consumer second
        (applyRegion region left right first second))
      (.id codomain (.app consumer first) (.app consumer second)) :=
  congruence_typed
    (.cumul (.idForm carrierFormed (.sort zero) leftTyped rightTyped) (fun _ => Nat.le_succ _))
    codomainFormed firstTyped secondTyped consumerTyped
    (applyRegion_typed regionTyped leftTyped rightTyped firstTyped secondTyped)

/-- This relation says a native equality proof exists; it is not conversion
and does not identify the raw syntax of its endpoints. -/
def NativeEquality (context : Tower.Ctx n) (carrier first second : Tower.Tm n) : Prop :=
  ∃ witness, Typing rules context witness (.id carrier first second)

def ObservationCompatible {Observation : Type} (context : Tower.Ctx n) (carrier : Tower.Tm n)
    (observe : Tower.Tm n → Observation) : Prop :=
  ∀ first second, NativeEquality context carrier first second → observe first = observe second

/-- A raw inspector reads a syntactic coordinate, not an equality theorem. -/
def variableIndex : Tower.Tm n → Option Nat
  | .var index => some index.val
  | _ => none

def booleanPathCarrier : Tower.Tm 4 := .id boolTm (.var 3) (.var 2)

theorem native_boolean_paths_equal :
    NativeEquality SharedJudgmentNativeBooleanNamedRegion.sourceContext booleanPathCarrier (.var 1) (.var 0) :=
  ⟨SharedJudgmentNativeBooleanNamedRegion.derivedProof.term,
    SharedJudgmentNativeBooleanNamedRegion.derived_proof_typed.typing⟩

/-- The actual derived native region is a discriminator against a stronger
profile that would silently treat its path equalities as raw-code equality. -/
theorem raw_inspection_incompatible_with_path_collapse :
    ¬ ObservationCompatible SharedJudgmentNativeBooleanNamedRegion.sourceContext booleanPathCarrier variableIndex := by
  intro compatible
  have impossible := compatible (.var 1) (.var 0) native_boolean_paths_equal
  exact (by decide : (some 1 : Option Nat) ≠ some 0) impossible

/-- Any proposed coarser equality relation that includes native equality
inherits the same obstruction if it promises to preserve raw inspection. -/
theorem stronger_collapse_cannot_keep_raw_inspection
    (equivalent : Tower.Tm 4 → Tower.Tm 4 → Prop)
    (includesNative : ∀ first second,
      NativeEquality SharedJudgmentNativeBooleanNamedRegion.sourceContext booleanPathCarrier first second →
        equivalent first second) :
    ¬ (∀ first second, equivalent first second → variableIndex first = variableIndex second) := by
  intro observed
  exact raw_inspection_incompatible_with_path_collapse
    (fun first second witness => observed first second (includesNative first second witness))

/-- Explicit semantic input for a stronger guest: it realizes a loop that
acts as Boolean negation. This is not a construction of a univalent universe. -/
structure SwapGuest where
  Path : Type
  reflexivity : Path
  swap : Path
  transport : Path → Bool → Bool
  reflexivity_action : ∀ value, transport reflexivity value = value
  swap_action : ∀ value, transport swap value = !value

theorem swap_guest_excludes_unique_paths (guest : SwapGuest) : ¬ Subsingleton guest.Path := by
  intro unique
  have same : guest.swap = guest.reflexivity := unique.allEq _ _
  have contradiction : (true : Bool) = false := by
    calc
      true = guest.transport guest.swap false := (guest.swap_action false).symm
      _ = guest.transport guest.reflexivity false := congrArg (fun path => guest.transport path false) same
      _ = false := guest.reflexivity_action false
  cases contradiction

theorem swap_guest_excludes_transport_irrelevance (guest : SwapGuest) :
    ¬ (∀ first second, guest.transport first = guest.transport second) := by
  intro irrelevant
  have same := congrFun (irrelevant guest.swap guest.reflexivity) false
  rw [guest.swap_action, guest.reflexivity_action] at same
  cases same

/-- A concrete interpretation of those premises, without claiming native
univalence. Its loop distinguishes a meaningful transport action. -/
def booleanSwapGuest : SwapGuest where
  Path := Bool
  reflexivity := false
  swap := true
  transport path value := if path then !value else value
  reflexivity_action _ := rfl
  swap_action _ := rfl

/-- A closed profile contract over fixed rules and the stated small-carrier
fragment. Each field quantifies over all of its admitted inputs, rather than
only the supplied examples. Retention is opt-in through successful capture. -/
structure Qualification : Prop where
  theoremAdmission : ∀ {n : Nat} {context : Tower.Ctx n} {carrier decision : Tower.Tm n},
    Typing rules context carrier (sortTm zero) →
    Typing rules context decision (SharedJudgmentNativeDecidableIdentity.decidableEqualityType carrier) →
    Typing rules context (regionFromDecision carrier decision) (regionType carrier)
  assumedAdmission : ∀ {n : Nat} {context : Tower.Ctx n} {carrier : Tower.Tm n},
    ContextFormation rules context → Typing rules context carrier (sortTm zero) →
    ContextFormation rules (assumedContext context carrier) ∧
      Typing rules (assumedContext context carrier) (.var 0) (regionType (rename wk carrier))
  application : ∀ {n : Nat} {context : Tower.Ctx n} {carrier region left right first second : Tower.Tm n},
    Typing rules context region (regionType carrier) →
    Typing rules context left carrier → Typing rules context right carrier →
    Typing rules context first (.id carrier left right) → Typing rules context second (.id carrier left right) →
    Typing rules context (applyRegion region left right first second) (.id (.id carrier left right) first second)
  consumerInterchange : ∀ {n : Nat} {context : Tower.Ctx n}
      {carrier region left right first second codomain consumer : Tower.Tm n},
    Typing rules context carrier (sortTm zero) → Typing rules context codomain (sortTm one) →
    Typing rules context region (regionType carrier) →
    Typing rules context left carrier → Typing rules context right carrier →
    Typing rules context first (.id carrier left right) → Typing rules context second (.id carrier left right) →
    Typing rules context consumer (SharedJudgmentIdentityRegions.arrow (.id carrier left right) codomain) →
    Typing rules context
      (SharedJudgmentIdentityRegions.congruenceTerm (.id carrier left right) first codomain consumer second
        (applyRegion region left right first second))
      (.id codomain (.app consumer first) (.app consumer second))
  conditionalExport : ∀ {n : Nat} {context : Tower.Ctx n} {carrier : Tower.Tm n} {body result : Tower.Tm (n + 1)},
    Judgment rules (assumedContext context carrier) body result →
    Judgment rules context (exportAssumption body) (.pi (regionType carrier) result)
  conditionalDischarge : ∀ {n : Nat} {context : Tower.Ctx n} {carrier region : Tower.Tm n}
      {body result : Tower.Tm (n + 1)},
    Judgment rules (assumedContext context carrier) body result →
    Typing rules context region (regionType carrier) →
    Judgment rules context (.app (exportAssumption body) region) (inst0 region result)
  beta : ∀ {n : Nat} (body : Tower.Tm (n + 1)) (region : Tower.Tm n),
    Conv rules.headEq (.app (exportAssumption body) region) (inst0 region body) rules.computation
  scopeReindexing : ∀ {n m : Nat} {context : Tower.Ctx n} {target : Tower.Ctx m}
      {sigma : Sub Tower.Head n m},
    FormationSensitive.CtxMor rules context target sigma → ∀ carrier,
    FormationSensitive.CtxMor rules (assumedContext context carrier)
      (assumedContext target (subst sigma carrier)) (liftSub sigma)
  typedReindexing : ∀ {n m : Nat} {context : Tower.Ctx n} {target : Tower.Ctx m}
      {sigma : Sub Tower.Head n m} {term type : Tower.Tm n},
    Judgment rules context term type → ContextFormation rules target →
    FormationSensitive.CtxMor rules context target sigma →
    Judgment rules target (subst sigma term) (subst sigma type)
  capturedInspection : ∀ {Name Revision : Type} {n : Nat}
      (proofs : ProofStore Name Revision n) (current : RevisionEnvironment Name Revision)
      (name : Name) (view : ProofView Name Revision n),
    captureView proofs current name ProofPresentation.claim = some view →
    ∃ original, recover proofs view = some original ∧ view.value = original.claim
  currentApplication : ∀ {Name Revision : Type} {n m : Nat}
      (proofs : ProofStore Name Revision n) (bindings : BindingStore Name Revision n m)
      (current : RevisionEnvironment Name Revision) (view : ProofView Name Revision n)
      (reference : Reference Name Revision) (proof : ProofPresentation n) (binding : Binding n m),
    recover proofs view = some proof → resolve bindings current reference = some binding →
    Judgment rules proof.context proof.term proof.type → ContextFormation rules binding.target →
    FormationSensitive.CtxMor rules proof.context binding.target binding.substitution →
    ∃ output, resolveApplication proofs bindings current view reference = some output ∧
      Judgment rules output.context output.term output.type
  missingApplication : ∀ {Name Revision : Type} {n m : Nat}
      (proofs : ProofStore Name Revision n) (bindings : BindingStore Name Revision n m)
      (current : RevisionEnvironment Name Revision) (view : ProofView Name Revision n)
      (reference : Reference Name Revision),
    resolve bindings current reference = none → resolveApplication proofs bindings current view reference = none
  derivedBoolean : Judgment rules (.nil : Tower.Ctx 0) SharedJudgmentNativeBooleanConstancy.region (regionType boolTm)
  noRawCollapse : ¬ ObservationCompatible SharedJudgmentNativeBooleanNamedRegion.sourceContext booleanPathCarrier variableIndex
  guestBoundary : ∀ guest : SwapGuest,
    ¬ Subsingleton guest.Path ∧ ¬ (∀ first second, guest.transport first = guest.transport second)

theorem qualified : Qualification where
  theoremAdmission := regionFromDecision_typed
  assumedAdmission formed carrierFormed := ⟨assumed_context_formed formed carrierFormed, local_region_typed _⟩
  application := applyRegion_typed
  consumerInterchange := region_consumer_interchange
  conditionalExport := conditional_export
  conditionalDischarge := conditional_discharge
  beta := discharge_beta
  scopeReindexing := assumed_scope_reindex
  typedReindexing := Judgment.substitute
  capturedInspection proofs current name view captured :=
    captured_view_is_supported proofs current name ProofPresentation.claim view captured
  currentApplication := resolved_application_typed rules
  missingApplication := missing_binding_no_application
  derivedBoolean := SharedJudgmentNativeBooleanConstancy.closed_region_judgment
  noRawCollapse := raw_inspection_incompatible_with_path_collapse
  guestBoundary guest := ⟨swap_guest_excludes_unique_paths guest, swap_guest_excludes_transport_irrelevance guest⟩

/-- Jointly witness the profile laws and the actual retained/current example
without inventing an unconditional context or a global proof-erasure operation. -/
theorem scoped_profile_joint : Qualification ∧
    (∃ output, resolveApplication SharedJudgmentNativeBooleanNamedRegion.proofs
      SharedJudgmentNativeBooleanNamedRegion.bindings SharedJudgmentNativeBooleanNamedRegion.before
      SharedJudgmentNativeBooleanNamedRegion.view (.live "Boolean-region-parameters") = some output ∧
      Judgment rules output.context output.term output.type) ∧
    recover SharedJudgmentNativeBooleanNamedRegion.proofs SharedJudgmentNativeBooleanNamedRegion.view =
      some SharedJudgmentNativeBooleanNamedRegion.derivedProof :=
  ⟨qualified, SharedJudgmentNativeBooleanNamedRegion.derived_named_application_typed,
    SharedJudgmentNativeBooleanNamedRegion.recover_original⟩

namespace Controls

/-- Exporting the local witness itself produces a well-formed conditional
theorem. This is a scope control, not a claim that Boolean uniqueness cannot
also be proved independently. -/
theorem assumed_region_exported : Judgment rules (.nil : Tower.Ctx 0)
    (exportAssumption (.var 0))
    (.pi (regionType boolTm) (rename wk (regionType boolTm))) :=
  conditional_export
    ⟨assumed_context_formed .nil (SharedJudgmentNativeBooleanRegion.bool_typed .nil), .var 0⟩

theorem conditional_type_not_unconditional :
    (.pi (regionType boolTm) (rename wk (regionType boolTm)) : Tower.Tm 0) ≠
      regionType boolTm := by decide

def checks : List Bool :=
  [decide (variableIndex (.var 1 : Tower.Tm 4) ≠ variableIndex (.var 0 : Tower.Tm 4)),
   decide (booleanSwapGuest.transport booleanSwapGuest.reflexivity false = false),
   decide (booleanSwapGuest.transport booleanSwapGuest.swap false = true),
   decide ((.pi (regionType boolTm) (rename wk (regionType boolTm)) : Tower.Tm 0) ≠ regionType boolTm)]

theorem checks_pass : checks = [true, true, true, true] := by decide

#eval checks

end Controls

/-! ## The same profile in the actual nondegenerate quotient interpretation -/

open SharedJudgmentNativeBooleanInterpretation (classOf emptyContext JInput observeJ
  runJ requestOf semanticReindex regionClass pathType firstPath secondPath sourceContext
  expandedOriginal)

theorem closed_false_judgment : Judgment rules (.nil : Tower.Ctx 0)
    SharedJudgmentNativeBooleanRegion.falseTm boolTm :=
  ⟨.nil, SharedJudgmentNativeBooleanRegion.false_typed .nil⟩

theorem closed_true_judgment : Judgment rules (.nil : Tower.Ctx 0)
    SharedJudgmentNativeBooleanRegion.trueTm boolTm :=
  ⟨.nil, SharedJudgmentNativeBooleanRegion.true_typed .nil⟩

/-- The actual model does not trivialize the scoped laws by collapsing the
Boolean constructors. The negative uses unbounded native conversion. -/
theorem boolean_meanings_distinct :
    classOf (context := emptyContext) closed_false_judgment ≠
      classOf (context := emptyContext) closed_true_judgment := by
  intro same
  exact SharedJudgmentNativeBooleanParallel.false_not_convertible_true
    ((SharedJudgmentNativeBooleanInterpretation.classOf_eq_iff _ _).mp same).2

theorem parallel_variables_fixed {index : Fin n} {target : Tower.Tm n}
    (steps : SharedJudgmentNativeBooleanParallel.ParStar (.var index) target) :
    target = .var index := by
  induction steps with
  | refl => rfl
  | tail previous finalStep ih =>
      rw [ih] at finalStep
      cases finalStep
      rfl

theorem variables_conversion_iff {first second : Fin n} :
    Conv rules.headEq (.var first) (.var second) rules.computation ↔ first = second := by
  constructor
  · intro conversion
    obtain ⟨common, firstSteps, secondSteps⟩ :=
      SharedJudgmentNativeBooleanParallel.conversion_join conversion
    exact Tm.var.inj ((parallel_variables_fixed firstSteps).symm.trans
      (parallel_variables_fixed secondSteps))
  · rintro rfl
    exact .refl _

/-- The native theorem equates the two paths propositionally, while their
conversion classes remain distinct. Thus the code/identity distinction also
holds inside the actual interpretation, not just for an external printer. -/
theorem native_path_presentations_distinct :
    QTerm.mk firstPath ≠ QTerm.mk secondPath := by
  intro same
  have conversion := ((QTerm.mk_eq_iff firstPath secondPath).mp same).2
  have indices := variables_conversion_iff.mp conversion
  exact (by decide : (1 : Fin 4) ≠ 0) indices

theorem derived_identity_does_not_erase_presentations :
    Nonempty (TermFibre
      (QuotientIdentity.idTy (context := (quotientProjection rules).obj sourceContext)
        (QType.mk pathType) (TermFibre.mk firstPath) (TermFibre.mk secondPath))) ∧
      QTerm.mk firstPath ≠ QTerm.mk secondPath :=
  ⟨⟨SharedJudgmentNativeBooleanInterpretation.regionIdentityValue⟩,
    native_path_presentations_distinct⟩

/-- Every computational step of an admitted judgment preserves both its
displayed type and its actual quotient meaning. No conversion boundary is
passed in by the consumer. -/
theorem reduction_preserves_meaning {context : Context rules}
    {source target displayed : Tower.Tm context.arity}
    (admitted : Judgment rules context.raw source displayed)
    (step : Step rules.headEq source target rules.computation) :
    classOf (SharedJudgmentNativeBooleanPreservation.step_preserves admitted step) =
      classOf admitted := by
  apply (SharedJudgmentNativeBooleanInterpretation.classOf_eq_iff _ _).mpr
  exact ⟨.refl _, .symm _ _ (.rel _ _ step)⟩

/-- The fixed-fragment boundary combines the scope contract with the actual
Boolean/J model, complete contextual subject reduction, retained-motive J,
and the original/current distinction. These are properties of one fixed
rules instance, not independently supplied models or profile assumptions. -/
structure FixedFragmentQualification : Prop extends Qualification where
  preservation : ∀ {n : Nat} {context : Tower.Ctx n} {source target displayed : Tower.Tm n},
    Judgment rules context source displayed →
    Step rules.headEq source target rules.computation →
    Judgment rules context target displayed
  semanticImage : ∀ (context : Context rules) (term type : Tower.Tm context.arity),
    Judgment rules context.raw term type ↔
      ∃ semanticType : QType context, QuotientInterpretation.TypeMeaning context type semanticType ∧
        ∃ value : TermFibre semanticType,
          QuotientInterpretation.TermMeaning context term type semanticType value
  semanticSubstitution : ∀ {source target : Context rules} {term type : Tower.Tm target.arity}
      (admitted : Judgment rules target.raw term type) (sigma : source ⟶ target),
    QuotientCwf.totalSub (classOf admitted) (QuotientCwf.project sigma) =
      classOf (admitted.substitute source.formed sigma.typed)
  computationMeaning : ∀ {context : Context rules} {source target displayed : Tower.Tm context.arity}
      (admitted : Judgment rules context.raw source displayed)
      (step : Step rules.headEq source target rules.computation),
    classOf (SharedJudgmentNativeBooleanPreservation.step_preserves admitted step) = classOf admitted
  retainedMotive : ∀ {context : Context rules} (first second : JInput context),
    observeJ first = observeJ second → classOf first.judgment = classOf second.judgment
  identityBeta : ∀ {context : Context rules} (input : JInput context),
    runJ (requestOf input.atReflexivity) = (observeJ input).method
  identitySemanticSubstitution : ∀ {source target : QuotientCwf.QContext rules}
      (request : SharedJudgmentNativeBooleanInterpretation.JRequest target.as) (sigma : source ⟶ target),
    QuotientCwf.totalSub (runJ request) sigma = runJ (semanticReindex request sigma)
  derivedRegionIdentity : regionClass.type =
    QuotientIdentity.idTy (context := (quotientProjection rules).obj sourceContext)
      (QType.mk pathType) (TermFibre.mk firstPath) (TermFibre.mk secondPath)
  nativePathPresentationSeparation : QTerm.mk firstPath ≠ QTerm.mk secondPath
  originalNotMeaning : expandedOriginal ≠ SharedJudgmentNativeBooleanNamedRegion.derivedProof.term ∧
    classOf SharedJudgmentNativeBooleanInterpretation.expanded_original_judgment = regionClass
  liveWithdrawal :
    recover SharedJudgmentNativeBooleanNamedRegion.proofs SharedJudgmentNativeBooleanNamedRegion.view =
      some SharedJudgmentNativeBooleanNamedRegion.derivedProof ∧
    resolveApplication SharedJudgmentNativeBooleanNamedRegion.proofs
      SharedJudgmentNativeBooleanNamedRegion.bindings SharedJudgmentNativeBooleanNamedRegion.afterWithdrawal
      SharedJudgmentNativeBooleanNamedRegion.view (.live "Boolean-region-parameters") = none ∧
    QuotientInterpretation.TermMeaning sourceContext SharedJudgmentNativeBooleanNamedRegion.derivedProof.term
      SharedJudgmentNativeBooleanNamedRegion.derivedProof.type
      (QType.mk (SharedJudgmentNativeBooleanInterpretation.annotation
        SharedJudgmentNativeBooleanNamedRegion.derived_proof_typed))
      (TermFibre.mk (SharedJudgmentNativeBooleanInterpretation.representative
        SharedJudgmentNativeBooleanNamedRegion.derived_proof_typed))
  booleanSeparation : classOf (context := emptyContext) closed_false_judgment ≠
    classOf (context := emptyContext) closed_true_judgment

theorem fixed_fragment_qualified : FixedFragmentQualification where
  toQualification := qualified
  preservation := SharedJudgmentNativeBooleanPreservation.step_preserves
  semanticImage := SharedJudgmentNativeBooleanInterpretation.admitted_iff_interpreted
  semanticSubstitution := SharedJudgmentNativeBooleanInterpretation.classOf_substitution
  computationMeaning := reduction_preserves_meaning
  retainedMotive := SharedJudgmentNativeBooleanInterpretation.retained_j_coherent
  identityBeta := SharedJudgmentNativeBooleanInterpretation.semantic_j_beta
  identitySemanticSubstitution := SharedJudgmentNativeBooleanInterpretation.semantic_j_substitution
  derivedRegionIdentity := SharedJudgmentNativeBooleanInterpretation.derived_region_has_identity_meaning
  nativePathPresentationSeparation := native_path_presentations_distinct
  originalNotMeaning := SharedJudgmentNativeBooleanInterpretation.equivalent_not_original
  liveWithdrawal := SharedJudgmentNativeBooleanInterpretation.missing_live_binding_does_not_erase_meaning
  booleanSeparation := boolean_meanings_distinct

#print axioms applyRegion_typed
#print axioms conditional_export
#print axioms conditional_discharge
#print axioms assumed_scope_reindex
#print axioms boolean_region_derived
#print axioms regionFromDecision_typed
#print axioms region_consumer_interchange
#print axioms raw_inspection_incompatible_with_path_collapse
#print axioms stronger_collapse_cannot_keep_raw_inspection
#print axioms swap_guest_excludes_unique_paths
#print axioms qualified
#print axioms scoped_profile_joint
#print axioms Controls.assumed_region_exported
#print axioms Controls.conditional_type_not_unconditional
#print axioms Controls.checks_pass
#print axioms boolean_meanings_distinct
#print axioms variables_conversion_iff
#print axioms native_path_presentations_distinct
#print axioms derived_identity_does_not_erase_presentations
#print axioms reduction_preserves_meaning
#print axioms fixed_fragment_qualified

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentScopedIdentityQualification
