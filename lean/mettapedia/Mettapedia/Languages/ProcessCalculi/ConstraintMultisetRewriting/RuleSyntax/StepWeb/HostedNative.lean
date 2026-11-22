import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Named
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeIteratedAgreement
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeDeadNames

/-!
# Hosted contextual firings as native live firings

The hosted source runs on the contextual rule-syntax step (`Hosting.hostStep`); the native concurrency
theory runs on native states and their live firings (`Interface.NativeState`, `Interface.LiveFiring`).
This module maps the first to the second and proves the correspondence laws.

## The two constructions, in their five choices

* **The contextual rule-syntax step** (`RuleSyntax.step` at `Frames.contextual S` with extensions by
  declarations): the store is a bag of occurrences labelled by terms at the state's frame; a firing is
  one match (one rule, one opening, one selection); guards are asked at every solution of the
  information, which includes the firing's own tells; the program is a fixed set of rules beside the
  store; there is one store of knowledge.
* **The native step** (`Interface.native`, on live firings): the store is a bag of occurrences holding
  conditional rows (shared values, private schemas, latent obligations); a firing is one match whose
  rule and every selected row are opened at their own reserved scopes; guards and predicate queries
  are asked at every solution of the information, which includes the firing's own tells; the rule is
  carried by the firing itself, its unknowns drawn from the state's private family; there is one store
  of knowledge, published along the solver's returned frame.

## The adapter

* `Presented`: a hosted state whose labels are terms at the top sort, as all hosted rows are.
* `Placed`: a hosted rule presented at the top sort, with its unknowns placed injectively in the
  private family `ruleLocals` (control unknowns beside schema unknowns).
* `state`: the native state of a presented hosted state: the same names, knowledge and present
  occurrences, every row shared, the scope ledger a parameter.
* `live`: the live firing of the canonical hosted firing of a placed rule.
* `infoExtension`: the information frame map, an injective arity-preserving extension: old names to
  captured names, the rule's unknowns to their placed locals opened at the rule's scope.

The first fragment's rules are placed (`placedRet`, `placedUnmatched`, `placedLeft`, `placedRight`,
`placedSchema`, and `placedNamed` for every name of the fragment); `fail` denotes no rule. The start of a
run is presented (`startPresented`), and so is the result of every canonical firing of a placed rule
(`resultPresented`), so runs stay presented.

## Laws

* **Firings to live firings.** `information_eq`: the native information is the hosted information
  carried along `infoExtension`. `admits_iff`: the canonical hosted firing is admitted exactly when its
  live firing is, for every guard the rule carries (equation guards, absence and counts:
  `check_iff`, `holds_iff`), every program holding the rule, every scope ledger and every budget.
* **Frames preserved.** `info_injective`: the frame map identifies no two observations.
* **Results to results.** `resultExtension`: the native result is a dead-name extension
  (`NativeDead.DeadExtension`) of the native state of the hosted result, taken at the native result's
  scope ledger (`resultState`): rows and knowledge carried along `resultInclusion`, the same present
  occurrences. The solver's returned names lie outside the inclusion (`returned_outside`) and are dead.
* **Residual frames.** `residual_eq`: after the step, the native residual of a second placed rule's live
  firing (`NativeIterated.residualAfter`) is its live firing at the hosted result, carried along the
  result inclusion; the rule scope moves by `NativeResidual.shift` (`carried_produced`).

Canonical openings only: an admitted firing with another opening is not adapted here. Hosted firings
with arbitrary openings are named moves of the source (`Hosting.Alternatives.reflection_named`), whose
canonical firings this adapter covers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.HostedNative

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open Interface (NativeState LiveFiring native)
open Interface.Frames (Frame)
open SourceLanguage Hosting Hosting.Alternatives

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} {κ : Keys S}

/-! ## The private family of the hosted rules' unknowns -/

/-- The names of the private family: the control rules' unknowns beside the schemas' unknowns. -/
abbrev RuleLocal (κ : Keys S) := Unknown ⊕ (Name κ ⊕ Unit)

variable (Γ star κ) in
/-- The arities of the private family: each control unknown and each schema unknown keeps its own. -/
abbrev ruleLocals : RuleLocal κ → MetaArity S :=
  Sum.elim (unknownArity Γ star) (schemaArity Γ star κ)

/-! ## Presented states and placed rules -/

variable (Γ star) in
/-- **A hosted state presented at the top sort**: every label is a term at `(Γ, star)`. -/
structure Presented (s : HostState S) where
  term : ℕ → Term (signature S s.frame.arity) Γ star
  label_eq : ∀ o, s.label o = observe (term o)

variable (Γ star κ) in
/-- **A hosted rule presented at the top sort**, its unknowns placed injectively in the private family. -/
structure Placed (r : CRule S) where
  body : RuleInstance (Term (signature S r.locals.arity) Γ star)
  body_eq : r.body = body.map observe
  collect_eq : r.collect = []
  name : r.locals.Names → RuleLocal κ
  injective : Function.Injective name
  preserves : ∀ x, ruleLocals Γ star κ (name x) = r.locals.arity x

/-! ## The first fragment's rules, placed -/

section Named

variable (N : Nodes S Γ star)

/-- `ret`: the control unknowns, placed as themselves. -/
def placedRet : Placed Γ star κ (retRule N) where
  body := { take := [altN N (evalN N (retN N (unk .datum))) (unk .stack)], read := [], tell := [], checks := [],
            produce := [altN N (valueN N (unk .datum)) (unk .stack)] }
  body_eq := rfl
  collect_eq := rfl
  name := Sum.inl
  injective := Sum.inl_injective
  preserves _ := rfl

/-- `apply` with no matching equation: the absence guard is part of the body. -/
def placedUnmatched : Placed Γ star κ (unmatchedRule N) where
  body := { take := [altN N (evalN N (applyN N (unk .datum))) (unk .stack)], read := [], tell := [],
            checks := [.predicate .none (eqnN N (unk .datum))],
            produce := [altN N (valueN N (unk .datum)) (unk .stack)] }
  body_eq := rfl
  collect_eq := rfl
  name := Sum.inl
  injective := Sum.inl_injective
  preserves _ := rfl

/-- `choice`, left. -/
def placedLeft : Placed Γ star κ (choiceLeftRule N) where
  body := { take := [altN N (evalN N (choiceN N (unk .first) (unk .second))) (unk .stack)],
            read := [], tell := [], checks := [], produce := [altN N (evalN N (unk .first)) (unk .stack)] }
  body_eq := rfl
  collect_eq := rfl
  name := Sum.inl
  injective := Sum.inl_injective
  preserves _ := rfl

/-- `choice`, right. -/
def placedRight : Placed Γ star κ (choiceRightRule N) where
  body := { take := [altN N (evalN N (choiceN N (unk .first) (unk .second))) (unk .stack)],
            read := [], tell := [], checks := [], produce := [altN N (evalN N (unk .second)) (unk .stack)] }
  body_eq := rfl
  collect_eq := rfl
  name := Sum.inl
  injective := Sum.inl_injective
  preserves _ := rfl

/-- `apply` by an equation: the schema's unknowns, the source's names and the stack, placed as
themselves. -/
def placedSchema {Ty : Type} (e : SourceLanguage.Equation κ Γ star Ty) : Placed Γ star κ (schema N e) where
  body := { take := [altN N (evalN N (applyN N (instantiate asUnknowns e.lhs))) schemaStack], read := [], tell := [],
            checks := [], produce := [altN N (evalN N (encComp N (instantiate asUnknowns) e.rhs)) schemaStack] }
  body_eq := rfl
  collect_eq := rfl
  name := Sum.inr
  injective := Sum.inr_injective
  preserves _ := rfl

/-- **Every rule a name of the first fragment denotes is placed.** `fail` denotes no rule. -/
def placedNamed {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty) :
    (n : RuleName) → (r : CRule S) → ruleNamed N P n = some r → Placed Γ star κ r
  | .ret, _, named => Option.some.inj named ▸ placedRet N
  | .unmatched, _, named => Option.some.inj named ▸ placedUnmatched N
  | .left, _, named => Option.some.inj named ▸ placedLeft N
  | .right, _, named => Option.some.inj named ▸ placedRight N
  | .eqn i, r, named =>
      match found : P.equations[i]? with
      | some e =>
          have same : schema N e = r := by
            simp only [ruleNamed, found, Option.map_some] at named
            exact Option.some.inj named
          same ▸ placedSchema N e
      | none => absurd named (by simp [ruleNamed, found])

/-- **The start of a run, presented**: the equation rows and the query's alternative are terms at the
top sort. -/
def startPresented {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty) (q : Comp κ Γ star Ty) :
    Presented Γ star (start N P q) where
  term o := if h : o < P.equations.length then
      eqnN N (instantiate (rowNames o) (P.equations.get ⟨o, h⟩).lhs)
    else encAlt N (instantiate queryNames) (.eval q) []
  label_eq o := by
    show startLabel N P q o = _
    unfold startLabel
    split <;> rfl

end Named

/-! ## The native state and the live firing -/

variable (κ) in
/-- **The native state of a presented hosted state**: the hosted frame's names, knowledge and present
occurrences; every row the shared value of its label, with no latent obligation; the scope ledger
`occupied`. -/
noncomputable def state (s : HostState S) (p : Presented Γ star s) (occupied : Finset ℕ) :
    NativeState S ℕ Γ star where
  Local := RuleLocal κ
  localEquality := Classical.decEq _
  locals := ruleLocals Γ star κ
  state :=
    { Names := s.frame.Names
      equality := Classical.decEq _
      declarations := s.frame.arity
      occupied := occupied
      equations := s.knowledge
      present := s.present
      rows := fun o => ContextualConditionalRows.ofStored (ruleLocals Γ star κ) s.frame.arity
        (.shared (p.term o)) }

/-- The rule's unknowns, placed in the private family, as names of the rule frame at a state. -/
def place {r : CRule S} (pl : Placed Γ star κ r) (F : Frame S) :
    Assignment r.locals.arity (ContextualActivatedStep.source (ruleLocals Γ star κ) F.arity) :=
  reindex (fun x => Sum.inl (pl.name x)) pl.preserves

/-- The scope a firing opens its rule at. -/
abbrev ruleScope (occupied : Finset ℕ) (selection : Selection ℕ) : ℕ :=
  ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.rulePort selection)

/-- The opened made rows of a placed rule at a state, at the information frame. -/
def produced {r : CRule S} (pl : Placed Γ star κ r) (F : Frame S) (scope : ℕ) :
    List (Term (signature S (ContextualActivatedStep.target (ruleLocals Γ star κ) F.arity)) Γ star) :=
  (pl.body.produce.map (instantiate (place pl F))).map
    (ContextualFreshening.termAt (ruleLocals Γ star κ) F.arity scope)

/-- **The live firing of the canonical hosted firing of a placed rule**: the rule placed in the
private family; each made identity outputs its opened made row, every other identity the closed node
`emptyN`; no query patterns; the solver budget `fuel`. -/
noncomputable def live (N : Nodes S Γ star) (s : HostState S) (p : Presented Γ star s) (occupied : Finset ℕ)
    {r : CRule S} (pl : Placed Γ star κ r) (selection : Selection ℕ) (fuel : ℕ) :
    LiveFiring (state κ s p occupied) where
  rule := pl.body.map (instantiate (place pl s.frame))
  selection := selection
  outputs := RuleSyntax.relabel
    (Tm := fun _ : Unit => Term (signature S (ContextualActivatedStep.target (ruleLocals Γ star κ) s.frame.arity)) Γ star)
    (a := ()) (fun _ => emptyN N) selection.made (produced pl s.frame (ruleScope occupied selection))
  patterns := []
  fuel := fuel

/-! ## The information frame map -/

/-- An old name to its captured name; a rule unknown to its placed local opened at `scope`. -/
def infoName {r : CRule S} (pl : Placed Γ star κ r) (F : Frame S) (scope : ℕ) :
    (RuleSyntax.Contextual.extend S F r.locals).Names → ScopedVar (RuleLocal κ) ⊕ F.Names
  | .inl name => .inr name
  | .inr x => .inl (ScopedVar.at scope (pl.name x))

theorem infoName_injective {r : CRule S} (pl : Placed Γ star κ r) (F : Frame S) (scope : ℕ) :
    Function.Injective (infoName pl F scope) := by
  rintro (first | first) (second | second) same
  · exact congrArg Sum.inl (Sum.inr.inj same)
  · cases same
  · cases same
  · have names := congrArg ScopedVar.name (Sum.inl.inj same)
    exact congrArg Sum.inr (pl.injective names)

theorem infoName_preserves {r : CRule S} (pl : Placed Γ star κ r) (F : Frame S) (scope : ℕ) :
    ∀ name, ContextualActivatedStep.target (ruleLocals Γ star κ) F.arity (infoName pl F scope name) =
      (RuleSyntax.Contextual.extend S F r.locals).arity name
  | .inl _ => rfl
  | .inr x => pl.preserves x

/-- **The information frame map**, an injective arity-preserving extension of the hosted extended
frame into the native information frame. -/
def infoExtension {r : CRule S} (pl : Placed Γ star κ r) (F : Frame S) (scope : ℕ) :
    ContextualGuardMatching.Extension (RuleSyntax.Contextual.extend S F r.locals).arity :=
  ⟨ScopedVar (RuleLocal κ) ⊕ F.Names, ContextualActivatedStep.target (ruleLocals Γ star κ) F.arity,
    infoName pl F scope, infoName_injective pl F scope, infoName_preserves pl F scope⟩

/-- **Frames preserved**: the information frame map identifies no two observations of the hosted
extended frame; distinct names and distinct unknowns of one sort stay distinct. -/
theorem info_injective {r : CRule S} (pl : Placed Γ star κ r) (F : Frame S) (scope : ℕ) :
    Function.Injective (instantiateObservation (infoExtension pl F scope).assignment) :=
  ContextualConditionalNaturality.observation_extension_injective _

/-- Old names go to captured names. -/
theorem info_weaken {r : CRule S} (pl : Placed Γ star κ r) (F : Frame S) (scope : ℕ) :
    Assignment.compose (infoExtension pl F scope).assignment (RuleSyntax.Contextual.weakenNames S F r.locals) =
      ContextualSelectionViews.capturedTarget (ruleLocals Γ star κ) F.arity := by
  funext name
  exact instantiate_generator (infoExtension pl F scope).assignment (Sum.inl name)

/-- Rule unknowns go to their placed locals, opened at the scope. -/
theorem info_opening {r : CRule S} (pl : Placed Γ star κ r) (F : Frame S) (scope : ℕ) :
    Assignment.compose (infoExtension pl F scope).assignment (RuleSyntax.Contextual.canonicalOpening S F r.locals) =
      Assignment.compose (ContextualFreshening.assignment (ruleLocals Γ star κ) F.arity scope) (place pl F) := by
  funext x
  change instantiate (infoExtension pl F scope).assignment
      (generator (RuleSyntax.Contextual.extend S F r.locals).arity (Sum.inr x)) =
    instantiate (ContextualFreshening.assignment (ruleLocals Γ star κ) F.arity scope) (place pl F x)
  rw [instantiate_generator]
  unfold place reindex
  rw [instantiate_castMetaBody, instantiate_generator]
  rfl

/-- An opened rule term, carried, is the native rule term opened at the scope. -/
theorem opened_term {r : CRule S} (pl : Placed Γ star κ r) (F : Frame S) (scope : ℕ)
    (t : Term (signature S r.locals.arity) Γ star) :
    instantiateObservation (infoExtension pl F scope).assignment
        (instantiateObservation (RuleSyntax.Contextual.canonicalOpening S F r.locals) (observe t)) =
      observe (ContextualFreshening.termAt (ruleLocals Γ star κ) F.arity scope (instantiate (place pl F) t)) := by
  rw [instantiateObservation_comp, info_opening, instantiateObservation_observe]
  unfold ContextualFreshening.termAt
  rw [Assignment.instantiate_compose]

/-- A row read at the extended frame, carried, is the row's captured value. -/
theorem row_term {r : CRule S} (pl : Placed Γ star κ r) (s : HostState S) (p : Presented Γ star s)
    (scope : ℕ) (o : ℕ) :
    instantiateObservation (infoExtension pl s.frame scope).assignment
        (instantiateObservation (RuleSyntax.Contextual.weakenNames S s.frame r.locals) (s.label o)) =
      observe (instantiate (ContextualSelectionViews.capturedTarget (ruleLocals Γ star κ) s.frame.arity) (p.term o)) := by
  rw [instantiateObservation_comp, info_weaken, p.label_eq o]
  rfl

/-- The matched patterns, carried, are the native use equations. -/
theorem matching_eq {r : CRule S} (pl : Placed Γ star κ r) (s : HostState S) (p : Presented Γ star s)
    (scope : ℕ) :
    ∀ (ts : List (Term (signature S r.locals.arity) Γ star)) (os : List ℕ),
      ContextualResidual.mapProblem (infoExtension pl s.frame scope).assignment
          (((ts.map observe).map (instantiateObservation (RuleSyntax.Contextual.canonicalOpening S s.frame r.locals))).zipWith
            (fun pattern o => (pattern,
              instantiateObservation (RuleSyntax.Contextual.weakenNames S s.frame r.locals) (s.label o))) os) =
        ContextualResidual.observeProblem (ContextualActivatedStep.useEquations
          ((ts.map (instantiate (place pl s.frame))).map
            (ContextualFreshening.termAt (ruleLocals Γ star κ) s.frame.arity scope))
          (os.map fun o => instantiate (ContextualSelectionViews.capturedTarget (ruleLocals Γ star κ) s.frame.arity)
            (p.term o)))
  | [], _ => rfl
  | _ :: _, [] => rfl
  | t :: ts, o :: os => congrArg₂ List.cons (Prod.ext (opened_term pl s.frame scope t) (row_term pl s p scope o))
      (matching_eq pl s p scope ts os)

/-- The opened tells, carried, are the native opened tells. -/
theorem tell_eq {r : CRule S} (pl : Placed Γ star κ r) (F : Frame S) (scope : ℕ) :
    ∀ (es : EquationStore (Term (signature S r.locals.arity) Γ star)),
      ContextualResidual.mapProblem (infoExtension pl F scope).assignment
          ((es.map fun e => (observe e.1, observe e.2)).map fun e =>
            (instantiateObservation (RuleSyntax.Contextual.canonicalOpening S F r.locals) e.1,
              instantiateObservation (RuleSyntax.Contextual.canonicalOpening S F r.locals) e.2)) =
        ContextualResidual.observeProblem ((es.map fun e => (instantiate (place pl F) e.1, instantiate (place pl F) e.2)).map
          fun e => (ContextualFreshening.termAt (ruleLocals Γ star κ) F.arity scope e.1,
            ContextualFreshening.termAt (ruleLocals Γ star κ) F.arity scope e.2))
  | [] => rfl
  | e :: es => congrArg₂ List.cons (Prod.ext (opened_term pl F scope e.1) (opened_term pl F scope e.2))
      (tell_eq pl F scope es)

theorem observeProblem_append {V : Type} {source : V → MetaArity S} {Δ : Ctx S} {kind : S.Srt}
    (first second : EquationStore (Term (signature S source) Δ kind)) :
    ContextualResidual.observeProblem (first ++ second) =
      ContextualResidual.observeProblem first ++ ContextualResidual.observeProblem second :=
  List.map_append ..

/-- The views of shared rows at their ports are their captured values. -/
theorem shared_views (s : HostState S) (p : Presented Γ star s) (occupied : Finset ℕ) (selection : Selection ℕ)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source (ruleLocals Γ star κ) s.frame.arity)) Γ star)) :
    List.ofFn (ContextualActivatedStep.prepared (ruleLocals Γ star κ) s.frame.arity occupied selection rule
        (fun o => ContextualStoredRows.Row.shared (p.term o))).taken =
      selection.taken.map (fun o =>
        instantiate (ContextualSelectionViews.capturedTarget (ruleLocals Γ star κ) s.frame.arity) (p.term o)) ∧
    List.ofFn (ContextualActivatedStep.prepared (ruleLocals Γ star κ) s.frame.arity occupied selection rule
        (fun o => ContextualStoredRows.Row.shared (p.term o))).read =
      selection.read.map (fun o =>
        instantiate (ContextualSelectionViews.capturedTarget (ruleLocals Γ star κ) s.frame.arity) (p.term o)) := by
  constructor
  · apply List.ext_getElem
    · simp
    · intro i _ _
      simp only [List.getElem_ofFn, List.getElem_map]
      exact ContextualSelectionViews.shared_value_at_port _ _ _ _ _
  · apply List.ext_getElem
    · simp
    · intro i _ _
      simp only [List.getElem_ofFn, List.getElem_map]
      exact ContextualSelectionViews.shared_value_at_port _ _ _ _ _

/-! ## Firings to live firings: the information -/

/-- **The native information of the live firing is the hosted information carried along the
information frame map.** -/
theorem information_eq (N : Nodes S Γ star) (s : HostState S) (p : Presented Γ star s) (occupied : Finset ℕ)
    {P : CProgram S} {r : CRule S} (member : r ∈ P) (pl : Placed Γ star κ r) (selection : Selection ℕ) (fuel : ℕ) :
    (live N s p occupied pl selection fuel).toNative.information =
      ContextualResidual.mapProblem (infoExtension pl s.frame (ruleScope occupied selection)).assignment
        ((RuleSyntax.Contextual.canonical (F := s.frame) r member selection []).information
          (Interface.Frames.contextual S) s) := by
  obtain ⟨takenViews, readViews⟩ := shared_views s p occupied selection (pl.body.map (instantiate (place pl s.frame)))
  have hostedInfo : (RuleSyntax.Contextual.canonical (F := s.frame) r member selection []).information
      (Interface.Frames.contextual S) s =
      ContextualResidual.mapProblem (RuleSyntax.Contextual.weakenNames S s.frame r.locals) s.knowledge ++
        (r.body.take.map (instantiateObservation (RuleSyntax.Contextual.canonicalOpening S s.frame r.locals))).zipWith
          (fun pattern o => (pattern,
            instantiateObservation (RuleSyntax.Contextual.weakenNames S s.frame r.locals) (s.label o))) selection.taken ++
        (r.body.read.map (instantiateObservation (RuleSyntax.Contextual.canonicalOpening S s.frame r.locals))).zipWith
          (fun pattern o => (pattern,
            instantiateObservation (RuleSyntax.Contextual.weakenNames S s.frame r.locals) (s.label o))) selection.read ++
        r.body.tell.map (fun e =>
          (instantiateObservation (RuleSyntax.Contextual.canonicalOpening S s.frame r.locals) e.1,
            instantiateObservation (RuleSyntax.Contextual.canonicalOpening S s.frame r.locals) e.2)) := rfl
  have nativeInfo : (live N s p occupied pl selection fuel).toNative.information =
      ContextualResidual.mapProblem (ContextualSelectionViews.capturedTarget (ruleLocals Γ star κ) s.frame.arity)
          s.knowledge ++
        ContextualResidual.observeProblem
          (ContextualActivatedStep.useEquations
              (((pl.body.map (instantiate (place pl s.frame))).map
                (ContextualFreshening.termAt (ruleLocals Γ star κ) s.frame.arity (ruleScope occupied selection))).take)
              (List.ofFn (ContextualActivatedStep.prepared (ruleLocals Γ star κ) s.frame.arity occupied selection
                (pl.body.map (instantiate (place pl s.frame))) (fun o => ContextualStoredRows.Row.shared (p.term o))).taken) ++
            ContextualActivatedStep.useEquations
              (((pl.body.map (instantiate (place pl s.frame))).map
                (ContextualFreshening.termAt (ruleLocals Γ star κ) s.frame.arity (ruleScope occupied selection))).read)
              (List.ofFn (ContextualActivatedStep.prepared (ruleLocals Γ star κ) s.frame.arity occupied selection
                (pl.body.map (instantiate (place pl s.frame))) (fun o => ContextualStoredRows.Row.shared (p.term o))).read) ++
            ((pl.body.map (instantiate (place pl s.frame))).map
              (ContextualFreshening.termAt (ruleLocals Γ star κ) s.frame.arity (ruleScope occupied selection))).tell) ++
        ContextualConditionalExecution.latent (ruleLocals Γ star κ) s.frame.arity occupied selection
          (fun o => ContextualConditionalRows.ofStored (ruleLocals Γ star κ) s.frame.arity (.shared (p.term o))) := rfl
  rw [nativeInfo, hostedInfo, ContextualConditionalExecution.latent_ofStored, List.append_nil, takenViews, readViews,
    pl.body_eq]
  simp only [RuleInstance.map]
  rw [Interface.NativeResidual.mapProblem_append, Interface.NativeResidual.mapProblem_append,
    Interface.NativeResidual.mapProblem_append, ContextualConditionalNaturality.map_problem_compose, info_weaken,
    matching_eq pl s p _ pl.body.take selection.taken, matching_eq pl s p _ pl.body.read selection.read, tell_eq,
    observeProblem_append, observeProblem_append]
  simp only [List.append_assoc]

/-! ## Firings to live firings: guards -/

/-- Observations stay apart under the inclusion into a frame with added names. -/
theorem inclusion_observation_injective {Extra W : Type} (unused : Extra → MetaArity S) (next : W → MetaArity S) :
    Function.Injective (instantiateObservation (ContextualPrefixModels.inclusion unused next)) := by
  have same : (ContextualGuardMatching.Extension.withLocals unused next).assignment =
      ContextualPrefixModels.inclusion unused next := by
    funext name
    rfl
  rw [← same]
  exact ContextualConditionalNaturality.observation_extension_injective _

/-- The rows a hosted pattern matches do not change when names are added. -/
theorem matchesAt_inclusion {a b : Frame S} {Extra : Type} (unused : Extra → MetaArity S)
    (σ : Assignment a.arity b.arity) (row : ℕ → Observation S a.arity) (present : Finset ℕ)
    (pattern : Observation S a.arity) :
    RuleSyntax.matchesAt (Interface.Frames.contextual S) (b := ⟨Extra ⊕ b.Names, ContextualPrefixModels.extended unused b.arity⟩)
        (Assignment.compose (ContextualPrefixModels.inclusion unused b.arity) σ) row present pattern =
      RuleSyntax.matchesAt (Interface.Frames.contextual S) σ row present pattern := by
  ext o
  rw [RuleSyntax.mem_matchesAt, RuleSyntax.mem_matchesAt]
  refine and_congr Iff.rfl ?_
  show instantiateObservation _ pattern = instantiateObservation _ (row o) ↔
    instantiateObservation σ pattern = instantiateObservation σ (row o)
  rw [← instantiateObservation_comp, ← instantiateObservation_comp]
  exact (inclusion_observation_injective unused b.arity).eq_iff

/-- **A hosted check holds at a solution exactly when it holds after adding names.** -/
theorem checkHolds_inclusion {a b : Frame S} {Extra : Type} (unused : Extra → MetaArity S)
    (σ : Assignment a.arity b.arity) (row : ℕ → Observation S a.arity) (present : Finset ℕ)
    (c : Check (Observation S a.arity)) :
    RuleSyntax.checkHolds (Interface.Frames.contextual S) (b := ⟨Extra ⊕ b.Names, ContextualPrefixModels.extended unused b.arity⟩)
        (Assignment.compose (ContextualPrefixModels.inclusion unused b.arity) σ) row present c ↔
      RuleSyntax.checkHolds (Interface.Frames.contextual S) σ row present c := by
  have moved : ∀ x y : Observation S a.arity,
      instantiateObservation (Assignment.compose (ContextualPrefixModels.inclusion unused b.arity) σ) x =
          instantiateObservation (Assignment.compose (ContextualPrefixModels.inclusion unused b.arity) σ) y ↔
        instantiateObservation σ x = instantiateObservation σ y := by
    intro x y
    rw [← instantiateObservation_comp, ← instantiateObservation_comp]
    exact (inclusion_observation_injective unused b.arity).eq_iff
  cases c with
  | equal left right => exact moved left right
  | predicate quantifier pattern =>
      show quantifier.Holds present _ ↔ quantifier.Holds present _
      exact quantifier.holds_congr fun o _ => moved pattern (row o)
  | count pattern number =>
      have same : RuleSyntax.matchesAt (Interface.Frames.contextual S)
          (b := ⟨Extra ⊕ b.Names, ContextualPrefixModels.extended unused b.arity⟩)
          (Assignment.compose (ContextualPrefixModels.inclusion unused b.arity) σ) row present pattern =
          RuleSyntax.matchesAt (Interface.Frames.contextual S) σ row present pattern := by
        ext o
        rw [RuleSyntax.mem_matchesAt, RuleSyntax.mem_matchesAt]
        exact and_congr Iff.rfl (moved pattern (row o))
      show (RuleSyntax.matchesAt _ _ _ _ _).card = number ↔ (RuleSyntax.matchesAt _ _ _ _ _).card = number
      rw [same]

/-- An opened rule term at a native solution. -/
theorem opened_at {r : CRule S} (pl : Placed Γ star κ r) (F : Frame S) (scope : ℕ) {b : Frame S}
    (σ : Assignment (ContextualActivatedStep.target (ruleLocals Γ star κ) F.arity) b.arity)
    (t : Term (signature S r.locals.arity) Γ star) :
    instantiateObservation (Assignment.compose σ (infoExtension pl F scope).assignment)
        (instantiateObservation (RuleSyntax.Contextual.canonicalOpening S F r.locals) (observe t)) =
      observe (instantiate σ (ContextualFreshening.termAt (ruleLocals Γ star κ) F.arity scope (instantiate (place pl F) t))) := by
  rw [← instantiateObservation_comp, opened_term]
  rfl

/-- A hosted row at a native solution. -/
theorem row_at {r : CRule S} (pl : Placed Γ star κ r) (s : HostState S) (p : Presented Γ star s) (scope : ℕ)
    {b : Frame S} (σ : Assignment (ContextualActivatedStep.target (ruleLocals Γ star κ) s.frame.arity) b.arity) (o : ℕ) :
    instantiateObservation (Assignment.compose σ (infoExtension pl s.frame scope).assignment)
        (instantiateObservation (RuleSyntax.Contextual.weakenNames S s.frame r.locals) (s.label o)) =
      observe (instantiate σ (instantiate (ContextualSelectionViews.capturedTarget (ruleLocals Γ star κ) s.frame.arity)
        (p.term o))) := by
  rw [← instantiateObservation_comp, row_term]
  rfl

/-- A native guard row matches exactly the captured value of the hosted label. -/
theorem guard_matches_iff (s : HostState S) (p : Presented Γ star s) (occupied : Finset ℕ) {b : Frame S}
    (σ : Assignment (ContextualActivatedStep.target (ruleLocals Γ star κ) s.frame.arity) b.arity)
    (pattern : Term (signature S b.arity) Γ star) (o : ℕ) :
    ContextualConditionalRows.Matches (ruleLocals Γ star κ) (ContextualActivatedStep.target (ruleLocals Γ star κ) s.frame.arity)
        σ pattern (ContextualConditionalExecution.guardRows (ruleLocals Γ star κ) s.frame.arity
          (state κ s p occupied).state.rows o) ↔
      pattern = instantiate σ (instantiate (ContextualSelectionViews.capturedTarget (ruleLocals Γ star κ) s.frame.arity)
        (p.term o)) :=
  (ContextualConditionalRows.ofStored_matches_iff (ruleLocals Γ star κ)
    (ContextualActivatedStep.target (ruleLocals Γ star κ) s.frame.arity) σ pattern
    (.shared (instantiate (ContextualSelectionViews.capturedTarget (ruleLocals Γ star κ) s.frame.arity) (p.term o)))).trans
    (ContextualGuardMatching.shared_matches_iff _ σ pattern _)

/-- **A check of the rule holds at the hosted solution read through the frame map exactly when the
native check holds at the native solution.** -/
theorem check_iff (s : HostState S) (p : Presented Γ star s) (occupied : Finset ℕ) {r : CRule S}
    (pl : Placed Γ star κ r) (selection : Selection ℕ) {b : Frame S}
    (σ : Assignment (ContextualActivatedStep.target (ruleLocals Γ star κ) s.frame.arity) b.arity)
    (c : Check (Term (signature S r.locals.arity) Γ star)) :
    RuleSyntax.checkHolds (Interface.Frames.contextual S)
        (Assignment.compose σ (infoExtension pl s.frame (ruleScope occupied selection)).assignment)
        (fun o => instantiateObservation (RuleSyntax.Contextual.weakenNames S s.frame r.locals) (s.label o))
        s.present (Check.map (instantiateObservation (RuleSyntax.Contextual.canonicalOpening S s.frame r.locals))
          (Check.map observe c)) ↔
      ContextualConditionalGuards.Holds (ruleLocals Γ star κ) σ
        (ContextualConditionalExecution.guardRows (ruleLocals Γ star κ) s.frame.arity (state κ s p occupied).state.rows)
        s.present
        (Check.map (ContextualFreshening.termAt (ruleLocals Γ star κ) s.frame.arity (ruleScope occupied selection))
          (Check.map (instantiate (place pl s.frame)) c)) := by
  cases c with
  | equal left right =>
      show instantiateObservation _ (instantiateObservation _ (observe left)) =
          instantiateObservation _ (instantiateObservation _ (observe right)) ↔ _
      rw [opened_at, opened_at]
      exact ⟨fun same => observe_injective same, congrArg observe⟩
  | predicate quantifier pattern =>
      refine quantifier.holds_congr fun o _ => ?_
      show instantiateObservation _ (instantiateObservation _ (observe pattern)) =
          instantiateObservation _ (instantiateObservation _ (s.label o)) ↔ _
      rw [opened_at, row_at pl s p, guard_matches_iff s p occupied]
      exact ⟨fun same => observe_injective same, congrArg observe⟩
  | count pattern number =>
      have same : RuleSyntax.matchesAt (Interface.Frames.contextual S)
          (Assignment.compose σ (infoExtension pl s.frame (ruleScope occupied selection)).assignment)
          (fun o => instantiateObservation (RuleSyntax.Contextual.weakenNames S s.frame r.locals) (s.label o)) s.present
          (instantiateObservation (RuleSyntax.Contextual.canonicalOpening S s.frame r.locals) (observe pattern)) =
          ContextualConditionalGuards.region (ruleLocals Γ star κ) σ
            (ContextualConditionalExecution.guardRows (ruleLocals Γ star κ) s.frame.arity (state κ s p occupied).state.rows)
            s.present (ContextualFreshening.termAt (ruleLocals Γ star κ) s.frame.arity (ruleScope occupied selection)
              (instantiate (place pl s.frame) pattern)) := by
        ext o
        rw [RuleSyntax.mem_matchesAt, ContextualConditionalGuards.mem_region]
        refine and_congr Iff.rfl ?_
        show instantiateObservation _ (instantiateObservation _ (observe pattern)) =
            instantiateObservation _ (instantiateObservation _ (s.label o)) ↔ _
        rw [opened_at, row_at pl s p, guard_matches_iff s p occupied]
        exact ⟨fun same => observe_injective same, congrArg observe⟩
      show (RuleSyntax.matchesAt _ _ _ _ _).card = number ↔ (ContextualConditionalGuards.region _ _ _ _ _).card = number
      rw [same]

/-- **The guard predicate of a hosted firing does not change when names are added.** -/
theorem firing_holds_inclusion {P : CProgram S} {s : HostState S}
    (f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) P s.frame) {b : Frame S} {Extra : Type}
    (unused : Extra → MetaArity S)
    (σ : Assignment ((RuleSyntax.Contextual.declarations S).target f.ext).arity b.arity) :
    f.Holds (Interface.Frames.contextual S) s (b := ⟨Extra ⊕ b.Names, ContextualPrefixModels.extended unused b.arity⟩)
        (Assignment.compose (ContextualPrefixModels.inclusion unused b.arity) σ) ↔
      f.Holds (Interface.Frames.contextual S) s σ :=
  and_congr (forall₂_congr fun c _ => checkHolds_inclusion unused σ _ s.present c)
    (forall₂_congr fun q _ => by rw [matchesAt_inclusion unused σ _ s.present q.1])

/-- Relabelling the made identities, in order, reads back the made rows. -/
theorem map_relabel {T : Type} (old : ℕ → T) :
    ∀ (made : List ℕ) (rows : List T), made.Nodup → made.length = rows.length →
      made.map (RuleSyntax.relabel (Tm := fun _ : Unit => T) (a := ()) old made rows) = rows
  | [], [], _, _ => rfl
  | [], _ :: _, _, lengths => by simp at lengths
  | _ :: _, [], _, lengths => by simp at lengths
  | o :: rest, t :: ts, nodup, lengths => by
      have fresh : o ∉ rest := (List.nodup_cons.mp nodup).1
      have tail := map_relabel old rest ts (List.nodup_cons.mp nodup).2 (Nat.succ.inj lengths)
      simp only [List.map_cons, RuleSyntax.relabel]
      congr 1
      refine Eq.trans (List.map_congr_left fun x inside => ?_) tail
      have different : x ≠ o := fun same => fresh (same ▸ inside)
      simp only [if_neg different]

/-- Relabelling commutes with every map of labels. -/
theorem map_relabel_apply {Obj₁ Obj₂ : Type*} {Tm₁ : Obj₁ → Type*} {Tm₂ : Obj₂ → Type*} {a₁ : Obj₁} {a₂ : Obj₂}
    (φ : Tm₁ a₁ → Tm₂ a₂) (old : ℕ → Tm₁ a₁) :
    ∀ (made : List ℕ) (rows : List (Tm₁ a₁)) (o : ℕ),
      φ (RuleSyntax.relabel old made rows o) =
        RuleSyntax.relabel (Tm := Tm₂) (a := a₂) (fun o => φ (old o)) made (rows.map φ) o
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | o' :: rest, t :: ts, o => by
      simp only [RuleSyntax.relabel, List.map_cons]
      split_ifs
      · rfl
      · exact map_relabel_apply φ old rest ts o

/-- A made identity's relabelling reads only the made rows. -/
theorem relabel_mem {Obj : Type*} {Tm : Obj → Type*} {a : Obj} (first second : ℕ → Tm a) :
    ∀ (made : List ℕ) (rows : List (Tm a)), made.length = rows.length → ∀ o ∈ made,
      RuleSyntax.relabel first made rows o = RuleSyntax.relabel second made rows o
  | [], _, _, _, inside => by cases inside
  | _ :: _, [], lengths, _, _ => by simp at lengths
  | o' :: rest, t :: ts, lengths, o, inside => by
      simp only [RuleSyntax.relabel]
      split_ifs with same
      · rfl
      · exact relabel_mem first second rest ts (Nat.succ.inj lengths) o
          ((List.mem_cons.mp inside).resolve_left same)

/-! ## Results -/

/-- The opened made rows, carried, are the native opened made rows. -/
theorem produced_eq {r : CRule S} (pl : Placed Γ star κ r) (F : Frame S) (scope : ℕ) :
    (pl.body.produce.map (instantiate (RuleSyntax.Contextual.canonicalOpening S F r.locals))).map
        (instantiate (infoExtension pl F scope).assignment) = produced pl F scope := by
  rw [List.map_map, produced, List.map_map]
  refine List.map_congr_left fun t _ => ?_
  show instantiate _ (instantiate _ t) = ContextualFreshening.termAt _ _ scope (instantiate _ t)
  rw [← Assignment.instantiate_compose, info_opening, Assignment.instantiate_compose]
  rfl

/-- **The result of the canonical hosted firing of a placed rule, presented**: every made identity
labelled by its opened made row, every other one by its old label at the extended frame. -/
def resultPresented (s : HostState S) (p : Presented Γ star s) {P : CProgram S} {r : CRule S}
    (member : r ∈ P) (pl : Placed Γ star κ r) (selection : Selection ℕ) :
    Presented Γ star ((RuleSyntax.Contextual.canonical (F := s.frame) r member selection []).result
      (Interface.Frames.contextual S) s) where
  term := RuleSyntax.relabel
    (Tm := fun _ : Unit => Term (signature S (RuleSyntax.Contextual.extend S s.frame r.locals).arity) Γ star) (a := ())
    (fun o => instantiate (RuleSyntax.Contextual.weakenNames S s.frame r.locals) (p.term o)) selection.made
    (pl.body.produce.map (instantiate (RuleSyntax.Contextual.canonicalOpening S s.frame r.locals)))
  label_eq o := by
    have rows : ((RuleSyntax.Contextual.canonical (F := s.frame) r member selection []).opened
        (Interface.Frames.contextual S)).produce =
        (pl.body.produce.map (instantiate (RuleSyntax.Contextual.canonicalOpening S s.frame r.locals))).map observe := by
      show r.body.produce.map _ = _
      rw [pl.body_eq]
      show (pl.body.produce.map observe).map _ = _
      rw [List.map_map, List.map_map]
      rfl
    have old : RuleSyntax.Firing.row (Interface.Frames.contextual S) s
        (RuleSyntax.Contextual.canonical (F := s.frame) r member selection []) =
        fun o => observe (instantiate (RuleSyntax.Contextual.weakenNames S s.frame r.locals) (p.term o)) := by
      funext o
      show instantiateObservation _ (s.label o) = _
      rw [p.label_eq o]
      rfl
    have label : ((RuleSyntax.Contextual.canonical (F := s.frame) r member selection []).result
        (Interface.Frames.contextual S) s).label =
        RuleSyntax.relabel (Tm := fun F : Frame S => Observation S F.arity)
          (a := RuleSyntax.Contextual.extend S s.frame r.locals)
          (RuleSyntax.Firing.row (Interface.Frames.contextual S) s
            (RuleSyntax.Contextual.canonical (F := s.frame) r member selection [])) selection.made
          ((RuleSyntax.Contextual.canonical (F := s.frame) r member selection []).opened
            (Interface.Frames.contextual S)).produce := rfl
    rw [label, rows, old]
    exact (map_relabel_apply
      (Tm₁ := fun _ : Unit => Term (signature S (RuleSyntax.Contextual.extend S s.frame r.locals).arity) Γ star)
      (a₁ := ()) (Tm₂ := fun F : Frame S => Observation S F.arity)
      (a₂ := RuleSyntax.Contextual.extend S s.frame r.locals) observe _ _ _ o).symm

section Admission

variable [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

/-- **The guards correspond**: the hosted guards at the hosted solution read through the frame map
are the native guards and queries at the native solution. -/
theorem holds_iff (N : Nodes S Γ star) (s : HostState S) (p : Presented Γ star s) (occupied : Finset ℕ)
    {P : CProgram S} {r : CRule S} (member : r ∈ P) (pl : Placed Γ star κ r) (selection : Selection ℕ) (fuel : ℕ)
    {b : Frame S} (σ : Assignment (ContextualActivatedStep.target (ruleLocals Γ star κ) s.frame.arity) b.arity) :
    (RuleSyntax.Contextual.canonical (F := s.frame) r member selection []).Holds (Interface.Frames.contextual S) s
        (Assignment.compose σ (infoExtension pl s.frame (ruleScope occupied selection)).assignment) ↔
      native.Holds (live N s p occupied pl selection fuel).toNative b σ := by
  have hostedChecks : ((RuleSyntax.Contextual.canonical (F := s.frame) r member selection []).opened
      (Interface.Frames.contextual S)).checks =
      (pl.body.checks.map (Check.map observe)).map
        (Check.map (instantiateObservation (RuleSyntax.Contextual.canonicalOpening S s.frame r.locals))) := by
    show r.body.checks.map _ = _
    rw [pl.body_eq]
    rfl
  constructor
  · rintro ⟨checks, -⟩
    refine ⟨?_, fun query inside => by cases inside⟩
    intro check inside
    obtain ⟨placed, insidePlaced, rfl⟩ := List.mem_map.mp inside
    obtain ⟨c, insideBody, rfl⟩ := List.mem_map.mp insidePlaced
    apply (check_iff s p occupied pl selection σ c).mp
    apply checks
    rw [hostedChecks]
    exact List.mem_map_of_mem (List.mem_map_of_mem insideBody)
  · rintro ⟨checks, -⟩
    refine ⟨?_, fun q inside => by simp [RuleSyntax.Contextual.canonical] at inside⟩
    intro check inside
    rw [hostedChecks] at inside
    obtain ⟨observed, insideObserved, rfl⟩ := List.mem_map.mp inside
    obtain ⟨c, insideBody, rfl⟩ := List.mem_map.mp insideObserved
    apply (check_iff s p occupied pl selection σ c).mpr
    exact checks _ (List.mem_map_of_mem (List.mem_map_of_mem insideBody))

/-- **Firings to live firings: admission.** The canonical hosted firing of a placed rule is admitted
by the contextual rule-syntax step exactly when its live firing is admitted by the native step, for
every guard the rule carries, every program holding the rule, every scope ledger and every budget. -/
theorem admits_iff (N : Nodes S Γ star) (s : HostState S) (p : Presented Γ star s) (occupied : Finset ℕ)
    {P : CProgram S} {r : CRule S} (member : r ∈ P) (pl : Placed Γ star κ r) (selection : Selection ℕ) (fuel : ℕ) :
    (RuleSyntax.Contextual.canonical (F := s.frame) r member selection []).Admits (Interface.Frames.contextual S) s ↔
      (live N s p occupied pl selection fuel).toNative.Realized := by
  rw [Interface.native_admits_iff]
  unfold RuleSyntax.Firing.Admits RuleSyntax.Firing.Shapes
  have take : r.body.take.length = pl.body.take.length := by rw [pl.body_eq]; exact List.length_map ..
  have read : r.body.read.length = pl.body.read.length := by rw [pl.body_eq]; exact List.length_map ..
  have produce : r.body.produce.length = (produced pl s.frame (ruleScope occupied selection)).length := by
    rw [pl.body_eq, produced, List.length_map, List.length_map]
    exact List.length_map ..
  have collect : r.collect.length = ([] : List (Finset ℕ)).length := by
    rw [pl.collect_eq]
    rfl
  refine and_congr ?_ (and_congr Iff.rfl (and_congr ?_ ?_))
  · constructor
    · rintro ⟨-, takenNodup, madeNodup, takeLength, readLength, produceLength, -⟩
      refine ⟨takenNodup, madeNodup, ?_, ?_, ?_⟩
      · show (pl.body.take.map _).length = _
        rw [List.length_map, ← take]
        exact takeLength
      · show (pl.body.read.map _).length = _
        rw [List.length_map, ← read]
        exact readLength
      · exact map_relabel _ selection.made _ madeNodup (produceLength.symm.trans produce)
    · rintro ⟨takenNodup, madeNodup, takeLength, readLength, outputs⟩
      refine ⟨RuleSyntax.Contextual.canonical_fresh s r member selection [], takenNodup, madeNodup, ?_, ?_, ?_,
        collect⟩
      · show r.body.take.length = selection.taken.length
        rw [take]
        exact (List.length_map ..).symm.trans takeLength
      · show r.body.read.length = selection.read.length
        rw [read]
        exact (List.length_map ..).symm.trans readLength
      · show r.body.produce.length = selection.made.length
        rw [produce]
        exact ((congrArg List.length outputs).symm.trans (List.length_map ..))
  · rw [information_eq N s p occupied member pl selection fuel]
    refine (Interface.Frames.contextual_solvable_iff _).trans
      (Iff.trans ?_ (Interface.Frames.contextual_solvable_iff _).symm)
    exact (ContextualConditionalNaturality.solvable_extension_iff
      (infoExtension pl s.frame (ruleScope occupied selection)) _).symm
  · rw [information_eq N s p occupied member pl selection fuel]
    constructor
    · intro asked b σ solved
      have restricted := (ContextualResidual.models_mapProblem _ _ _).mp solved
      exact (holds_iff N s p occupied member pl selection fuel σ).mp (asked b _ restricted)
    · intro asked b σ solved
      have lifted := (ContextualConditionalNaturality.models_liftModel_iff
        (infoExtension pl s.frame (ruleScope occupied selection)) σ _).mpr solved
      have held := (holds_iff N s p occupied member pl selection fuel
        (b := ⟨(infoExtension pl s.frame (ruleScope occupied selection)).Complement ⊕ b.Names,
          ContextualPrefixModels.extended (infoExtension pl s.frame (ruleScope occupied selection)).complementDeclarations
            b.arity⟩)
        ((infoExtension pl s.frame (ruleScope occupied selection)).liftModel σ)).mpr
        (asked ⟨(infoExtension pl s.frame (ruleScope occupied selection)).Complement ⊕ b.Names,
          ContextualPrefixModels.extended (infoExtension pl s.frame (ruleScope occupied selection)).complementDeclarations
            b.arity⟩ _ lifted)
      rw [ContextualGuardMatching.Extension.liftModel_square] at held
      exact (firing_holds_inclusion _ _ σ).mp held

/-! ## Results to results -/

section Results

variable (N : Nodes S Γ star) (s : HostState S) (p : Presented Γ star s) (occupied : Finset ℕ)
  {P : CProgram S} {r : CRule S} (member : r ∈ P) (pl : Placed Γ star κ r) (selection : Selection ℕ) (fuel : ℕ)

/-- The native state of the hosted result, at the native result's scope ledger. -/
noncomputable abbrev resultState (realized : (live N s p occupied pl selection fuel).toNative.Realized) :
    NativeState S ℕ Γ star :=
  state κ ((RuleSyntax.Contextual.canonical (F := s.frame) r member selection []).result
      (Interface.Frames.contextual S) s) (resultPresented s p member pl selection)
    (native.result (live N s p occupied pl selection fuel).toNative realized).state.occupied

/-- **The inclusion of the hosted result into the native result**: the private family into its old
part, and the hosted result's names through the information frame map into the old part of the
returned frame. The solver's returned names and every other opened local are outside its image. -/
def resultInclusion (realized : (live N s p occupied pl selection fuel).toNative.Realized) :
    Interface.NativeDead.Inclusion (resultState N s p occupied member pl selection fuel realized)
      (native.result (live N s p occupied pl selection fuel).toNative realized) where
  locals := Sum.inl
  locals_injective := Sum.inl_injective
  locals_preserves _ := rfl
  names name := Sum.inl (infoName pl s.frame (ruleScope occupied selection) name)
  names_injective := Sum.inl_injective.comp (infoName_injective pl s.frame _)
  names_preserves name := infoName_preserves pl s.frame _ name

/-- **The returned frame, explicit**: no hosted name is sent to a name the solver returned. -/
theorem returned_outside (realized : (live N s p occupied pl selection fuel).toNative.Realized)
    (name : (resultState N s p occupied member pl selection fuel realized).state.Names)
    (returned : (Interface.LiveFiring.execution realized).update.Variables ⊕ Empty) :
    (resultInclusion N s p occupied member pl selection fuel realized).names name ≠ Sum.inr returned := by
  intro same
  cases same

/-- The result inclusion on names is the information frame map followed by the solver frame's
inclusion of its source. -/
theorem resultInclusion_frame (realized : (live N s p occupied pl selection fuel).toNative.Realized) :
    (resultInclusion N s p occupied member pl selection fuel realized).frame =
      Assignment.compose (ContextualComputedFreshFrame.includeSource (Interface.LiveFiring.execution realized).update)
        (infoExtension pl s.frame (ruleScope occupied selection)).assignment := by
  funext name
  change reindex _ _ name = instantiate _ (reindex _ _ name)
  unfold reindex
  rw [instantiate_castMetaBody, instantiate_generator, Interface.NativeResidual.includeSource_apply]
  rfl

/-- The made identities and the opened made rows have equal lengths at an admitted firing. -/
theorem made_length (realized : (live N s p occupied pl selection fuel).toNative.Realized) :
    selection.made.length = (produced pl s.frame (ruleScope occupied selection)).length := by
  have shapes := ((Interface.native_admits_iff _).mp realized).1
  exact (List.length_map ..).symm.trans (congrArg List.length shapes.2.2.2.2)

/-- **The rows correspond**: every native result row is the carried row of the hosted result. -/
theorem result_rows (realized : (live N s p occupied pl selection fuel).toNative.Realized) (o : ℕ) :
    (native.result (live N s p occupied pl selection fuel).toNative realized).state.rows o =
      (resultInclusion N s p occupied member pl selection fuel realized).row
        ((resultState N s p occupied member pl selection fuel realized).state.rows o) := by
  by_cases made : o ∈ selection.made
  · change (Interface.LiveFiring.execution realized).target.rows o = _
    rw [ContextualConditionalExecution.Firing.shared_row _ o made rfl]
    change _ = ContextualConditionalRows.ofStored _ _ (.shared (instantiate
      (resultInclusion N s p occupied member pl selection fuel realized).frame
        ((resultPresented s p member pl selection).term o)))
    rw [resultInclusion_frame, Assignment.instantiate_compose]
    congr 3
    change RuleSyntax.relabel
        (Tm := fun _ : Unit => Term (signature S (ContextualActivatedStep.target (ruleLocals Γ star κ) s.frame.arity)) Γ star)
        (a := ()) (fun _ => emptyN N) selection.made (produced pl s.frame (ruleScope occupied selection)) o = _
    have key := map_relabel_apply
      (Tm₁ := fun _ : Unit => Term (signature S (RuleSyntax.Contextual.extend S s.frame r.locals).arity) Γ star)
      (a₁ := ())
      (Tm₂ := fun _ : Unit =>
        Term (signature S (ContextualActivatedStep.target (ruleLocals Γ star κ) s.frame.arity)) Γ star)
      (a₂ := ()) (instantiate (infoExtension pl s.frame (ruleScope occupied selection)).assignment)
      (fun o => instantiate (RuleSyntax.Contextual.weakenNames S s.frame r.locals) (p.term o)) selection.made
      (pl.body.produce.map (instantiate (RuleSyntax.Contextual.canonicalOpening S s.frame r.locals))) o
    rw [produced_eq] at key
    exact (relabel_mem
      (Tm := fun _ : Unit => Term (signature S (ContextualActivatedStep.target (ruleLocals Γ star κ) s.frame.arity)) Γ star)
      (a := ()) _ _ selection.made _ (made_length N s p occupied pl selection fuel realized) o made).trans key.symm
  · change (Interface.LiveFiring.execution realized).target.rows o = _
    rw [Interface.NativeResidual.rows_of_not_made _ made]
    change ContextualConditionalRows.ofStored _ _ (.shared (instantiate
        (Interface.NativeResidual.change (Interface.LiveFiring.execution realized)) (p.term o))) =
      ContextualConditionalRows.ofStored _ _ (.shared (instantiate
        (resultInclusion N s p occupied member pl selection fuel realized).frame
          ((resultPresented s p member pl selection).term o)))
    have kept : (resultPresented s p member pl selection).term o =
        instantiate (RuleSyntax.Contextual.weakenNames S s.frame r.locals) (p.term o) :=
      RuleSyntax.Firing.relabel_of_not_mem
        (Tm := fun _ : Unit => Term (signature S (RuleSyntax.Contextual.extend S s.frame r.locals).arity) Γ star)
        (a := ()) _ _ _ made
    rw [kept, ← Assignment.instantiate_compose, resultInclusion_frame, ← Assignment.compose_associative, info_weaken]
    rfl

/-- **The knowledge corresponds**: the native result's knowledge is the hosted result's, carried. -/
theorem result_equations (realized : (live N s p occupied pl selection fuel).toNative.Realized) :
    (native.result (live N s p occupied pl selection fuel).toNative realized).state.equations.Perm
      (ContextualResidual.mapProblem (resultInclusion N s p occupied member pl selection fuel realized).frame
        (resultState N s p occupied member pl selection fuel realized).state.equations) := by
  rw [resultInclusion_frame]
  apply List.Perm.of_eq
  change ContextualResidual.mapProblem
      (ContextualComputedFreshFrame.includeSource (Interface.LiveFiring.execution realized).update)
      (live N s p occupied pl selection fuel).toNative.information =
    ContextualResidual.mapProblem (Assignment.compose
      (ContextualComputedFreshFrame.includeSource (Interface.LiveFiring.execution realized).update)
      (infoExtension pl s.frame (ruleScope occupied selection)).assignment)
      ((RuleSyntax.Contextual.canonical (F := s.frame) r member selection []).information
        (Interface.Frames.contextual S) s)
  rw [← ContextualConditionalNaturality.map_problem_compose, information_eq N s p occupied member pl selection fuel]

/-- **Results to results.** The native result of the live firing is a dead-name extension of the
native state of the hosted result: rows and knowledge carried, the same present occurrences, the same
scope ledger. The solver's returned names and the other opened locals are dead. -/
def resultExtension (realized : (live N s p occupied pl selection fuel).toNative.Realized) :
    Interface.NativeDead.DeadExtension (resultState N s p occupied member pl selection fuel realized)
      (native.result (live N s p occupied pl selection fuel).toNative realized) where
  toInclusion := resultInclusion N s p occupied member pl selection fuel realized
  rows := result_rows N s p occupied member pl selection fuel realized
  equations := result_equations N s p occupied member pl selection fuel realized
  present := rfl
  occupied := rfl

/-! ## Residual frames -/

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- The closed node `emptyN` is fixed by every instantiation. -/
theorem instantiate_emptyN {V W : Type} {D : V → MetaArity S} {E : W → MetaArity S} (σ : Assignment D E) :
    instantiate σ (emptyN N (D := D)) = emptyN N := by
  unfold emptyN
  rw [N.instantiate_node]
  congr 1
  funext i
  exact (Nat.not_lt_zero _ i.isLt).elim

/-- **A second rule's placement, carried by the step, is its placement at the hosted result, carried
along the result inclusion.** -/
theorem carried_place (realized : (live N s p occupied pl selection fuel).toNative.Realized)
    {r₂ : CRule S} (pl₂ : Placed Γ star κ r₂) :
    Assignment.compose (Interface.NativeResidual.sourceCarry (Interface.LiveFiring.execution realized))
        (place pl₂ s.frame) =
      Assignment.compose (resultInclusion N s p occupied member pl selection fuel realized).source
        (place pl₂ ((RuleSyntax.Contextual.canonical (F := s.frame) r member selection []).result
          (Interface.Frames.contextual S) s).frame) := by
  funext x
  change instantiate _ (reindex _ _ x) = instantiate _ (reindex _ _ x)
  unfold reindex
  rw [instantiate_castMetaBody, instantiate_castMetaBody, instantiate_generator, instantiate_generator]
  unfold Interface.NativeDead.Inclusion.source reindex
  rw [castMetaBody_trans]
  rfl

/-- The second rule's opened made rows, carried by the step, are its opened made rows at the hosted
result, carried along the result inclusion: the step shifts the rule's scope by `NativeResidual.shift`. -/
theorem carried_produced (realized : (live N s p occupied pl selection fuel).toNative.Realized)
    {r₂ : CRule S} (pl₂ : Placed Γ star κ r₂) (selection₂ : Selection ℕ) :
    (produced pl₂ s.frame (ruleScope occupied selection₂)).map
        (instantiate (Interface.NativeResidual.carry (Interface.LiveFiring.execution realized))) =
      (produced pl₂ ((RuleSyntax.Contextual.canonical (F := s.frame) r member selection []).result
          (Interface.Frames.contextual S) s).frame
          (ruleScope (native.result (live N s p occupied pl selection fuel).toNative realized).state.occupied
            selection₂)).map
        (instantiate (resultInclusion N s p occupied member pl selection fuel realized).target) := by
  unfold produced
  rw [List.map_map, List.map_map, List.map_map, List.map_map]
  refine List.map_congr_left fun t _ => ?_
  have shifted := Interface.NativeResidual.scopeAt_shift (Interface.LiveFiring.execution realized)
    (ContextualActivationScopes.rulePort selection₂)
  change instantiate _ (ContextualFreshening.termAt _ _ _ (instantiate _ t)) =
    instantiate _ (ContextualFreshening.termAt _ _ _ (instantiate _ t))
  rw [Interface.NativeResidual.carry_termAt, Interface.NativeDead.Inclusion.termAt_carried,
    ← Assignment.instantiate_compose, ← Assignment.instantiate_compose,
    carried_place N s p occupied member pl selection fuel realized pl₂]
  change ContextualFreshening.termAt _ _ (ruleScope occupied selection₂ + _) _ =
    ContextualFreshening.termAt _ _ (ContextualActivationScopes.scopeAt
      (Interface.LiveFiring.execution realized).target.occupied (ContextualActivationScopes.rulePort selection₂)) _
  rw [shifted]
  rfl

/-- **Residual frames, explicit.** After the step of the live firing, the native residual of a second
placed rule's live firing is that rule's live firing at the hosted result, carried along the result
inclusion. The residual's rule scope is the old one shifted by `NativeResidual.shift`; the hosted
result is adapted at the native result's scope ledger. -/
theorem residual_eq (realized : (live N s p occupied pl selection fuel).toNative.Realized)
    {r₂ : CRule S} (pl₂ : Placed Γ star κ r₂) (selection₂ : Selection ℕ) (fuel₂ : ℕ) :
    Interface.NativeIterated.residualAfter realized (live N s p occupied pl₂ selection₂ fuel₂) =
      (resultInclusion N s p occupied member pl selection fuel realized).firing
        (live N ((RuleSyntax.Contextual.canonical (F := s.frame) r member selection []).result
            (Interface.Frames.contextual S) s) (resultPresented s p member pl selection)
          (native.result (live N s p occupied pl selection fuel).toNative realized).state.occupied
          pl₂ selection₂ fuel₂) := by
  refine Interface.NativeIterated.liveFiring_ext ?_ rfl ?_ rfl rfl
  · change (pl₂.body.map (instantiate (place pl₂ s.frame))).map _ = (pl₂.body.map (instantiate _)).map _
    rw [OccurrenceRelabeling.rule_map_comp, OccurrenceRelabeling.rule_map_comp]
    refine congrArg (fun mapping => pl₂.body.map mapping) (funext fun t => ?_)
    change instantiate _ (instantiate _ t) = instantiate _ (instantiate _ t)
    rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose,
      carried_place N s p occupied member pl selection fuel realized pl₂]
  · funext o
    have left := map_relabel_apply
      (Tm₁ := fun _ : Unit =>
        Term (signature S (ContextualActivatedStep.target (ruleLocals Γ star κ) s.frame.arity)) Γ star)
      (a₁ := ())
      (Tm₂ := fun _ : Unit => Term (signature S (ContextualActivatedStep.target
        (native.result (live N s p occupied pl selection fuel).toNative realized).locals
        (native.result (live N s p occupied pl selection fuel).toNative realized).state.declarations)) Γ star)
      (a₂ := ()) (instantiate (Interface.NativeResidual.carry (Interface.LiveFiring.execution realized)))
      (fun _ => emptyN N) selection₂.made (produced pl₂ s.frame (ruleScope occupied selection₂)) o
    have right := map_relabel_apply
      (Tm₁ := fun _ : Unit => Term (signature S (ContextualActivatedStep.target (ruleLocals Γ star κ)
        ((RuleSyntax.Contextual.canonical (F := s.frame) r member selection []).result
          (Interface.Frames.contextual S) s).frame.arity)) Γ star)
      (a₁ := ())
      (Tm₂ := fun _ : Unit => Term (signature S (ContextualActivatedStep.target
        (native.result (live N s p occupied pl selection fuel).toNative realized).locals
        (native.result (live N s p occupied pl selection fuel).toNative realized).state.declarations)) Γ star)
      (a₂ := ()) (instantiate (resultInclusion N s p occupied member pl selection fuel realized).target)
      (fun _ => emptyN N) selection₂.made
      (produced pl₂ ((RuleSyntax.Contextual.canonical (F := s.frame) r member selection []).result
          (Interface.Frames.contextual S) s).frame
        (ruleScope (native.result (live N s p occupied pl selection fuel).toNative realized).state.occupied
          selection₂)) o
    rw [carried_produced N s p occupied member pl selection fuel realized pl₂ selection₂] at left
    simp only [instantiate_emptyN] at left right
    exact left.trans right.symm

/-- **The second step corresponds.** After the step of the live firing, the canonical hosted firing of a
second placed rule at the hosted result is admitted exactly when the native residual of its live firing
is admitted: the residual law, admission along the dead-name extension of the result
(`NativeDead.DeadExtension.admits_iff`), and admission at the hosted result. -/
theorem residual_admits_iff (realized : (live N s p occupied pl selection fuel).toNative.Realized)
    {P₂ : CProgram S} {r₂ : CRule S} (member₂ : r₂ ∈ P₂) (pl₂ : Placed Γ star κ r₂) (selection₂ : Selection ℕ)
    (fuel₂ : ℕ) :
    (RuleSyntax.Contextual.canonical
        (F := ((RuleSyntax.Contextual.canonical (F := s.frame) r member selection []).result
          (Interface.Frames.contextual S) s).frame) r₂ member₂ selection₂ []).Admits (Interface.Frames.contextual S)
        ((RuleSyntax.Contextual.canonical (F := s.frame) r member selection []).result (Interface.Frames.contextual S) s) ↔
      (Interface.NativeIterated.residualAfter realized (live N s p occupied pl₂ selection₂ fuel₂)).toNative.Realized := by
  rw [residual_eq N s p occupied member pl selection fuel realized pl₂ selection₂ fuel₂,
    admits_iff N _ (resultPresented s p member pl selection)
      (native.result (live N s p occupied pl selection fuel).toNative realized).state.occupied member₂ pl₂ selection₂ fuel₂]
  exact (resultExtension N s p occupied member pl selection fuel realized).admits_iff _

end Results

end Admission

#print axioms residual_admits_iff
#print axioms info_injective
#print axioms info_weaken
#print axioms info_opening
#print axioms information_eq
#print axioms checkHolds_inclusion
#print axioms firing_holds_inclusion
#print axioms check_iff
#print axioms holds_iff
#print axioms admits_iff
#print axioms resultPresented
#print axioms resultInclusion_frame
#print axioms result_rows
#print axioms result_equations
#print axioms resultExtension
#print axioms returned_outside
#print axioms carried_place
#print axioms carried_produced
#print axioms residual_eq
#print axioms placedNamed
#print axioms startPresented

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.HostedNative
