import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublicationInventory
import Mettapedia.OSLF.Syntax.ContextualSupportSubstitution

/-!
# Resolved output expressions with private template binders

Actor locals and the private variables of produced templates have different
origins. Each template origin includes its production-port index. Declared
captures refer to the actor's already resolved identities. Lowering uses the
existing binding terms, preserves their sorts and object binders, and adds
no transition or text-based ownership rule.

This construction does not yet install its selectively captured schema in
the publication endpoint. In particular its schema constructor must not be
collapsed into the existing Boolean choice between ordinary and shared output.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTemplateSource

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)

variable {S : Signature} {Local Inner Shared Next : Type}
    (locals : Local → MetaArity S) (inners : Inner → MetaArity S)
    (captures : Shared → MetaArity S)

abbrev Actor := ContextualSelectionViews.source locals captures
abbrev Templates : Nat × Inner → MetaArity S := fun entry => inners entry.2
abbrev Expanded : Local ⊕ (Nat × Inner) → MetaArity S := Sum.elim locals (Templates inners)
abbrev Raw := ContextualSelectionViews.source (Expanded locals inners) captures
abbrev Active := ContextualSelectionViews.target (Expanded locals inners) captures
abbrev Blueprint := ContextualSelectionViews.source inners (Actor locals captures)

def actorInclusion : Assignment (Actor locals captures) (Raw locals inners captures) :=
  ContextualPublication.includePrivate locals (Templates inners)

def templateInclusion (port : Nat) :
    Assignment (Blueprint locals inners captures) (Raw locals inners captures)
  | .inl identity => generator (Raw locals inners captures) (.inl (.inr (port,identity)))
  | .inr (.inl identity) => generator (Raw locals inners captures) (.inl (.inl identity))
  | .inr (.inr identity) => generator (Raw locals inners captures) (.inr identity)

def actorAt (scope : Nat) : Assignment (Actor locals captures) (Active locals inners captures) :=
  Assignment.compose (ContextualFreshening.assignment (Expanded locals inners) captures scope)
    (actorInclusion locals inners captures)

def templateAt (scope port : Nat) :
    Assignment (Blueprint locals inners captures) (Active locals inners captures) :=
  Assignment.compose (ContextualFreshening.assignment (Expanded locals inners) captures scope)
    (templateInclusion locals inners captures port)

theorem actorAt_local (scope : Nat) (identity : Local) :
    actorAt locals inners captures scope (.inl identity) =
      generator (Active locals inners captures) (.inl (ScopedVar.at scope (.inl identity))) := by
  change instantiate (ContextualFreshening.assignment (Expanded locals inners) captures scope)
    (generator (Raw locals inners captures) (.inl (.inl identity))) = _
  exact instantiate_generator _ _

theorem actorAt_shared (scope : Nat) (identity : Shared) :
    actorAt locals inners captures scope (.inr identity) =
      generator (Active locals inners captures) (.inr identity) := by
  change instantiate (ContextualFreshening.assignment (Expanded locals inners) captures scope)
    (generator (Raw locals inners captures) (.inr identity)) = _
  exact instantiate_generator _ _

theorem templateAt_private (scope port : Nat) (identity : Inner) :
    templateAt locals inners captures scope port (.inl identity) =
      generator (Active locals inners captures) (.inl (ScopedVar.at scope (.inr (port,identity)))) := by
  change instantiate (ContextualFreshening.assignment (Expanded locals inners) captures scope)
    (generator (Raw locals inners captures) (.inl (.inr (port,identity)))) = _
  exact instantiate_generator _ _

theorem templateAt_capture (scope port : Nat) (identity : Local ⊕ Shared) :
    templateAt locals inners captures scope port (.inr identity) = actorAt locals inners captures scope identity := by
  cases identity <;> rfl

inductive Production (context : Ctx S) (sort : S.Srt) where
  | ordinary : Term (signature S (Actor locals captures)) context sort → Production context sort
  | shared : Term (signature S (Actor locals captures)) context sort → Production context sort
  | schema : Term (signature S (Blueprint locals inners captures)) context sort → Production context sort

def Production.lower {Γ : Ctx S} {sort : S.Srt} (port : Nat) :
    Production locals inners captures Γ sort → Term (signature S (Raw locals inners captures)) Γ sort
  | .ordinary value | .shared value => instantiate (actorInclusion locals inners captures) value
  | .schema body => instantiate (templateInclusion locals inners captures port) body

def Production.atScope {Γ : Ctx S} {sort : S.Srt} (scope port : Nat) :
    Production locals inners captures Γ sort → Term (signature S (Active locals inners captures)) Γ sort
  | .ordinary value | .shared value => instantiate (actorAt locals inners captures scope) value
  | .schema body => instantiate (templateAt locals inners captures scope port) body

theorem Production.freshened_lower {Γ : Ctx S} {sort : S.Srt} (scope port : Nat)
    (production : Production locals inners captures Γ sort) :
    ContextualFreshening.termAt (Expanded locals inners) captures scope
        (production.lower locals inners captures port) = production.atScope locals inners captures scope port := by
  cases production <;> exact (Assignment.instantiate_compose _ _ _).symm

structure Rule (context : Ctx S) (sort : S.Srt) where
  take : List (Term (signature S (Actor locals captures)) context sort)
  read : List (Term (signature S (Actor locals captures)) context sort)
  tell : EquationStore (Term (signature S (Actor locals captures)) context sort)
  checks : List (Check (Term (signature S (Actor locals captures)) context sort))
  produce : List (Production locals inners captures context sort)

def Rule.lower {Γ : Ctx S} {sort : S.Srt} (rule : Rule locals inners captures Γ sort) :
    RuleInstance (Term (signature S (Raw locals inners captures)) Γ sort) where
  take := rule.take.map (instantiate (actorInclusion locals inners captures))
  read := rule.read.map (instantiate (actorInclusion locals inners captures))
  tell := rule.tell.map fun equation =>
    (instantiate (actorInclusion locals inners captures) equation.1,
     instantiate (actorInclusion locals inners captures) equation.2)
  checks := rule.checks.map (Check.map (instantiate (actorInclusion locals inners captures)))
  produce := rule.produce.mapIdx (fun port output => output.lower locals inners captures port)

theorem Rule.lower_at_port {Γ : Ctx S} {sort : S.Srt}
    (rule : Rule locals inners captures Γ sort) (port : Fin rule.produce.length) :
    (rule.lower locals inners captures).produce.get ⟨port.val, by
      simpa only [Rule.lower, List.length_mapIdx] using port.isLt⟩ =
      (rule.produce.get port).lower locals inners captures port.val :=
  List.getElem_mapIdx

universe uO uA uB

/-- Production metadata is assigned in source-port order. Fresh occurrence
allocation cannot change the chosen source constructor or its port origin. -/
def assign {O : Type uO} {A : Type uA} [DecidableEq O] : List O → List A → O → Option A
  | occurrence :: rest, value :: values, selected =>
      if selected = occurrence then some value else assign rest values selected
  | _, _, _ => none

theorem assign_values_map {O : Type uO} {A : Type uA} {B : Type uB} [DecidableEq O]
    (f : A → B) : ∀ (keys : List O) (values : List A) (key : O),
    (assign keys values key).map f =
      assign keys (values.map f) key
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | first :: rest, value :: values, key => by
      by_cases same : key = first
      · simp only [assign, if_pos same, Option.map_some, List.map_cons]
      · simp only [assign, if_neg same, List.map_cons]
        exact assign_values_map f rest values key


theorem assign_mem {O : Type uO} {A : Type uA} [DecidableEq O] :
    ∀ (occurrences : List O) (values : List A) (selected : O) (value : A),
      assign occurrences values selected = some value → selected ∈ occurrences
  | [], _, _, _, impossible => by cases impossible
  | _ :: _, [], _, _, impossible => by cases impossible
  | first :: rest, initial :: values, selected, value, found => by
      by_cases same : selected = first
      · exact List.mem_cons.mpr (.inl same)
      · exact List.mem_cons.mpr (.inr (assign_mem rest values selected value
          (by simpa only [assign, if_neg same] using found)))

theorem assign_get {O : Type uO} {A : Type uA} [DecidableEq O] :
    ∀ (occurrences : List O) (values : List A) (_unique : occurrences.Nodup)
      (sameLength : occurrences.length = values.length) (port : Fin occurrences.length),
      assign occurrences values (occurrences.get port) =
        some (values.get ⟨port.val, by omega⟩)
  | [], _, _, _, port => Fin.elim0 port
  | _ :: _, [], _, sameLength, _ => by cases sameLength
  | occurrence :: rest, value :: values, unique, sameLength, port => by
      cases port using Fin.cases with
      | zero => simp [assign, List.get_eq_getElem]
      | succ port =>
          have different : rest.get port ≠ occurrence := by
            intro same
            exact (List.nodup_cons.mp unique).1 (same ▸ List.get_mem rest port)
          have restLength : rest.length = values.length := Nat.succ.inj sameLength
          have bound : port.val < values.length := restLength ▸ port.isLt
          change (if rest.get port = occurrence then some value else assign rest values (rest.get port)) =
            some (values.get ⟨port.val, bound⟩)
          rw [if_neg different]
          exact assign_get rest values (List.nodup_cons.mp unique).2 (Nat.succ.inj sameLength) port

theorem assign_map {O : Type uO} {A : Type uA} [DecidableEq O] :
    ∀ (occurrences : List O) (values : List A) (fallback : O → A),
      occurrences.Nodup → occurrences.length = values.length →
        occurrences.map (fun occurrence => (assign occurrences values occurrence).getD (fallback occurrence)) = values
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, lengths => by cases lengths
  | _ :: _, [], _, _, lengths => by cases lengths
  | first :: rest, value :: values, fallback, unique, lengths => by
      simp only [List.map_cons, assign, ite_true, Option.getD_some]
      have tail : rest.map (fun occurrence =>
          (if occurrence = first then some value else assign rest values occurrence).getD (fallback occurrence)) =
          rest.map (fun occurrence => (assign rest values occurrence).getD (fallback occurrence)) := by
        apply List.map_congr_left
        intro occurrence member
        have different : occurrence ≠ first := by
          intro same
          exact (List.nodup_cons.mp unique).1 (same ▸ member)
        rw [if_neg different]
      rw [tail, assign_map rest values fallback (List.nodup_cons.mp unique).2 (Nat.succ.inj lengths)]

def Rule.descriptors {Γ : Ctx S} {sort : S.Srt} (rule : Rule locals inners captures Γ sort) :=
  List.ofFn (fun port : Fin rule.produce.length => (port.val, rule.produce.get port))

def Rule.outputsFor {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
    (rule : Rule locals inners captures Γ sort) (made : List O) : O → Option (Nat × Production locals inners captures Γ sort) :=
  assign made (rule.descriptors locals inners captures)

theorem Rule.output_at_port {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
    (rule : Rule locals inners captures Γ sort) (made : List O) (unique : made.Nodup)
    (sameLength : made.length = rule.produce.length) (port : Fin made.length) :
    rule.outputsFor locals inners captures made (made.get port) =
      some (port.val, rule.produce.get ⟨port.val, by omega⟩) := by
  have length : made.length = (rule.descriptors locals inners captures).length :=
    sameLength.trans (List.length_ofFn).symm
  exact (assign_get made (rule.descriptors locals inners captures) unique length port).trans
    (congrArg some (List.get_ofFn _ _))

theorem Rule.output_origin {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
    (rule : Rule locals inners captures Γ sort) (made : List O) (unique : made.Nodup)
    (sameLength : made.length = rule.produce.length) (occurrence : O) (origin : Nat)
    (production : Production locals inners captures Γ sort)
    (selected : rule.outputsFor locals inners captures made occurrence = some (origin, production)) :
    ∃ port : Fin rule.produce.length, port.val = origin ∧ rule.produce.get port = production := by
  have member := assign_mem made (rule.descriptors locals inners captures) occurrence (origin, production) selected
  obtain ⟨position, same⟩ := List.mem_iff_get.mp member
  have atPort := rule.output_at_port locals inners captures made unique sameLength position
  rw [same] at atPort
  have pairEq := Option.some.inj (atPort.symm.trans selected)
  exact ⟨⟨position.val, by omega⟩, congrArg Prod.fst pairEq, congrArg Prod.snd pairEq⟩

def storedBody {Names : Type} {next : Names → MetaArity S}
    (captureValues : Assignment (Actor locals captures) next) (port : Nat) :
    Assignment (Blueprint locals inners captures)
      (ContextualSelectionViews.source (Expanded locals inners) next)
  | .inl identity => generator (ContextualSelectionViews.source (Expanded locals inners) next) (.inl (.inr (port,identity)))
  | .inr identity => instantiate (ContextualSelectionViews.capturedSource (Expanded locals inners) next)
      (captureValues identity)

def stored {Names : Type} {next : Names → MetaArity S}
    (captureValues : Assignment (Actor locals captures) next) (port : Nat)
    {Γ : Ctx S} {sort : S.Srt} (body : Term (signature S (Blueprint locals inners captures)) Γ sort) :
    ContextualStoredRows.Row (Expanded locals inners) next Γ sort :=
  .schema (instantiate (storedBody locals inners captures captureValues port) body)

theorem stored_instance {Names Future Model : Type} {next : Names → MetaArity S}
    {future : Future → MetaArity S} {model : Model → MetaArity S}
    (captureValues : Assignment (Actor locals captures) next) (port : Nat)
    (images : Assignment (Expanded locals inners) model)
    (embedding : Assignment future model) (candidate : Assignment next future)
    {Γ : Ctx S} {sort : S.Srt} (body : Term (signature S (Blueprint locals inners captures)) Γ sort) :
    instantiate (ContextualGuardMatching.instanceAssignment (Expanded locals inners) images embedding candidate)
        (instantiate (storedBody locals inners captures captureValues port) body) =
      instantiate (ContextualGuardMatching.instanceAssignment inners
        (fun identity => images (.inr (port,identity))) embedding (Assignment.compose candidate captureValues)) body := by
  rw [instantiate_comp]
  apply congrArg (fun assignment => instantiate assignment body)
  funext identity
  cases identity with
  | inl identity => exact instantiate_generator _ _
  | inr identity =>
      exact ContextualGuardMatching.instance_on_shared_value (Expanded locals inners) images embedding candidate
        (captureValues identity)

theorem stored_matches_iff {Names Future : Type} {next : Names → MetaArity S}
    {future : Future → MetaArity S} (captureValues : Assignment (Actor locals captures) next)
    (port : Nat) (candidate : Assignment next future)
    {Γ : Ctx S} {sort : S.Srt} (body : Term (signature S (Blueprint locals inners captures)) Γ sort)
    (pattern : Term (signature S future) Γ sort) :
    ContextualGuardMatching.Matches (Expanded locals inners) candidate pattern
        (stored locals inners captures captureValues port body) ↔
      ContextualGuardMatching.Matches inners (Assignment.compose candidate captureValues) pattern (.schema body) := by
  constructor
  · rintro ⟨extension,images,same⟩
    refine ⟨extension,fun identity => images (.inr (port,identity)),?_⟩
    exact (stored_instance locals inners captures captureValues port images extension.assignment candidate body).symm.trans same
  · rintro ⟨extension,images,same⟩
    let added := ContextualGuardMatching.Extension.withLocals (Expanded locals inners) extension.declarations
    let images' : Assignment (Expanded locals inners) added.declarations
      | .inl identity => generator added.declarations (.inl (.inl identity))
      | .inr (origin,identity) => if origin = port then instantiate added.assignment (images identity)
          else generator added.declarations (.inl (.inr (origin,identity)))
    refine ⟨extension.trans added,images',?_⟩
    change instantiate (ContextualGuardMatching.instanceAssignment (Expanded locals inners) images'
        (extension.trans added).assignment candidate)
      (instantiate (storedBody locals inners captures captureValues port) body) = _
    erw [stored_instance,ContextualGuardMatching.Extension.trans_assignment]
    have mapped := congrArg (instantiate added.assignment) same
    have assignments :
        (fun identity => instantiate added.assignment
          (ContextualGuardMatching.instanceAssignment inners images extension.assignment
            (Assignment.compose candidate captureValues) identity)) =
        ContextualGuardMatching.instanceAssignment inners (fun identity => images' (.inr (port,identity)))
          (Assignment.compose added.assignment extension.assignment) (Assignment.compose candidate captureValues) := by
      funext identity
      cases identity with
      | inl identity =>
          change instantiate added.assignment (images identity) =
            if port = port then instantiate added.assignment (images identity)
              else generator added.declarations (.inl (.inr (port,identity)))
          exact (if_pos rfl).symm
      | inr identity =>
          exact instantiate_comp extension.assignment added.assignment
            ((Assignment.compose candidate captureValues) identity)
    have left := (instantiate_comp (ContextualGuardMatching.instanceAssignment inners images extension.assignment
      (Assignment.compose candidate captureValues)) added.assignment body).trans
        (congrArg (fun assignment => instantiate assignment body) assignments)
    exact left.symm.trans
      (mapped.trans (Assignment.instantiate_compose added.assignment extension.assignment pattern).symm)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTemplateSource
