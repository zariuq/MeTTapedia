import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Transfer
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Contextual

/-!
# Native template matching by a fixed contextual transform rule

A query task carries the literal pattern and held template. The rule consumes
the task, reads one selected row without consuming it, and emits the template
under the retained match information. It consumes the same query node as
the hosting translation. This fixed-space adapter materializes one
selected row's private information;
different alternatives never share that information by conjunction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.NativeQuery.MatchKernel

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit
open RuleSyntax
open Interface (Frames)

abbrev callerFrame : Interface.Frames.Frame MSig := ⟨Name mkeys, fam mkeys⟩
abbrev locals : Interface.Frames.Frame MSig := ⟨Fin 2, fun _ => ([], ())⟩
abbrev X := Frames.contextual MSig
abbrev E := Contextual.declarations MSig
abbrev Tm := Contextual.Terms MSig
abbrev Body (frame : Interface.Frames.Frame MSig) := Term (signature MSig frame.arity) [] ()

def slot (index : Fin 2) : Body locals := generator locals.arity index
def queryAt {frame : Interface.Frames.Frame MSig} (space pattern template : Body frame) : Body frame :=
  Hosting.mettaNodes.node .query ![space, pattern, Hosting.retN Hosting.mettaNodes template]

def task {frame : Interface.Frames.Frame MSig} (pattern template : Body frame) : Body frame :=
  queryAt (symAt "&self") pattern template

theorem task_encodes_held_query (pattern template : MData) :
    task (frame := callerFrame) pattern template =
      Hosting.encComp Hosting.mettaNodes id (.query (sym "&self") pattern (.ret template) :
        Comp mkeys [] () MTy) := rfl

theorem task_inj {frame : Interface.Frames.Frame MSig} {p t q u : Body frame}
    (same : task (frame := frame) p t = task q u) : p = q ∧ t = u := by
  have parts := Hosting.vec3_inj (Hosting.mettaNodes.args_eq same)
  exact ⟨parts.2.1, Hosting.vec1_inj (Hosting.mettaNodes.args_eq parts.2.2)⟩

@[simp] theorem instantiate_task {before after : Interface.Frames.Frame MSig}
    (point : Assignment before.arity after.arity) (pattern template : Body before) :
    instantiate point (task pattern template) = task (instantiate point pattern) (instantiate point template) := by
  unfold task queryAt
  rw [Hosting.mettaNodes.instantiate_node]
  congr 1
  funext i
  fin_cases i <;> rfl

def rule : Rule Tm :=
  ⟨locals, ⟨[observe (task (slot 0) (slot 1))], [observe (slot 0)], [], [], [observe (slot 1)]⟩, []⟩
def program : RuleSyntax.Program Tm := {rule}

theorem program_finite : program.Finite := Set.finite_singleton _

def observedStore {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}
    (store : List (Constraint κ Γ star)) : EquationStore (Observation S (fam κ)) :=
  store.map fun equation => (observe equation.1, observe equation.2)

theorem observed_models {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}
    {future : Interface.Frames.Frame S}
    (point : Assignment (fam κ) future.arity) (store : List (Constraint κ Γ star)) :
    (Frames.contextual S).Models (a := ⟨Name κ, fam κ⟩) (b := future)
      point (observedStore store) ↔ Models point store := by
  constructor
  · intro model equation inside
    exact observe_injective (model _ (List.mem_map.mpr ⟨equation, inside, rfl⟩))
  · intro model equation inside
    obtain ⟨original, member, rfl⟩ := List.mem_map.mp inside
    exact congrArg observe (model original member)

/-! This firing takes a scoped query and reads one already opened occurrence.
Each choice owns its row and complete knowledge inside one alternative. -/

namespace Opened

def rowEquations {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}
    (row : Row κ Γ star) (pattern : Data κ Γ star) : List (Constraint κ Γ star) :=
  row.store ++ [(pattern, row.atom)]

def initial (store : List (Constraint mkeys [] ()))
    (pattern template : MData) (row : Row mkeys [] ()) : RuleSyntax.State Tm Nat :=
  ⟨callerFrame, observedStore (store ++ row.store), {0, 1},
    fun occurrence => if occurrence = 0 then observe (task pattern template)
      else observe row.atom⟩

def firing (store : List (Constraint mkeys [] ()))
    (pattern template : MData) (row : Row mkeys [] ()) :
    RuleSyntax.Firing Nat E program (initial store pattern template row).frame :=
  Contextual.canonical (S := MSig) rule (Set.mem_singleton _) ⟨[0], [1], [2]⟩ []

theorem information_eq (store : List (Constraint mkeys [] ()))
    (pattern template : MData) (row : Row mkeys [] ()) :
    (firing store pattern template row).information X (initial store pattern template row) =
      X.applyStore (Contextual.weakenNames MSig callerFrame locals)
        (observedStore (store ++ row.store)) ++
      [(instantiateObservation (Contextual.canonicalOpening MSig callerFrame locals)
          (observe (task (slot 0) (slot 1))),
        instantiateObservation (Contextual.weakenNames MSig callerFrame locals) (observe (task pattern template)))] ++
      [(instantiateObservation (Contextual.canonicalOpening MSig callerFrame locals) (observe (slot 0)),
        instantiateObservation (Contextual.weakenNames MSig callerFrame locals)
          (observe row.atom))] := by
  exact List.append_nil _

/-- A source solution extends across the fresh match-rule slots without
changing the assignment of any caller name. -/
theorem extend_model (store : List (Constraint mkeys [] ()))
    (pattern template : MData) (row : Row mkeys [] ()) {future : Interface.Frames.Frame MSig}
    (caller : Assignment callerFrame.arity future.arity)
    (model : Models caller (store ++ rowEquations row pattern)) :
    ∃ point : Assignment (Contextual.extend MSig callerFrame locals).arity future.arity,
      Assignment.compose point (Contextual.weakenNames MSig callerFrame locals) = caller ∧
      X.Models point ((firing store pattern template row).information X
        (initial store pattern template row)) := by
  let localPoint : Assignment locals.arity future.arity := fun index =>
    if index = 0 then instantiate caller pattern else instantiate caller template
  let point : Assignment (Contextual.extend MSig callerFrame locals).arity future.arity :=
    Contextual.copair MSig (F := callerFrame) (N := locals) (B := future) caller localPoint
  have expanded : Models caller ((store ++ row.store) ++
      [(pattern, row.atom)]) := by
    simpa only [rowEquations, List.append_assoc] using model
  have old := ((models_append caller _ _).mp expanded).1
  have matchedRow : instantiate caller pattern = instantiate caller row.atom := by
    exact ((models_append caller _ _).mp expanded).2 _ (List.mem_singleton_self _)
  refine ⟨point, ?_, ?_⟩
  · funext name
    exact instantiate_generator point (.inl name)
  · rw [information_eq]
    intro equation member
    rcases List.mem_append.mp member with earlier | read
    · rcases List.mem_append.mp earlier with known | taken
      · obtain ⟨original, inside, rfl⟩ := List.mem_map.mp known
        exact (Contextual.copair_weaken MSig (F := callerFrame) (N := locals) (B := future) caller localPoint original.1).trans
          (((observed_models (future := future) caller _).mpr old original inside).trans
            (Contextual.copair_weaken MSig (F := callerFrame) (N := locals) (B := future) caller localPoint original.2).symm)
      · obtain rfl := List.mem_singleton.mp taken
        change instantiateObservation point
            (instantiateObservation (Contextual.canonicalOpening MSig callerFrame locals) (observe (task (slot 0) (slot 1)))) =
          instantiateObservation point (instantiateObservation (Contextual.weakenNames MSig callerFrame locals) (observe (task pattern template)))
        rw [Contextual.copair_opening, Contextual.copair_weaken]
        change observe (instantiate localPoint (task (frame := locals) (slot 0) (slot 1))) =
          observe (instantiate caller (task (frame := callerFrame) pattern template))
        rw [instantiate_task,
          instantiate_task (before := callerFrame) (after := future) caller pattern template]
        simp [slot, instantiate_generator, localPoint]
    · obtain rfl := List.mem_singleton.mp read
      change instantiateObservation point
          (instantiateObservation (Contextual.canonicalOpening MSig callerFrame locals) (observe (slot 0))) =
        instantiateObservation point (instantiateObservation (Contextual.weakenNames MSig callerFrame locals)
          (observe row.atom))
      rw [Contextual.copair_opening, Contextual.copair_weaken]
      change observe (instantiate localPoint (slot 0)) = observe (instantiate caller row.atom)
      rw [show instantiate localPoint (slot 0) = instantiate caller pattern by
        rw [slot, instantiate_generator]; simp [localPoint]]
      exact congrArg observe matchedRow
/-- A real solution of the source row problem constructs admission. The rule
does not accept a solver verdict without the model that justifies it. -/
theorem admitted_of_source (store : List (Constraint mkeys [] ()))
    (pattern template : MData) (row : Row mkeys [] ())
    (live : Solvable (store ++ rowEquations row pattern)) :
    (firing store pattern template row).Admits X (initial store pattern template row) := by
  obtain ⟨Names, declaration, caller, model⟩ := live
  obtain ⟨point, _, known⟩ := extend_model store pattern template row
    (future := ⟨Names, declaration⟩) caller model
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨Contextual.canonical_fresh _ _ _ _ _,
      by change ([0] : List Nat).Nodup; decide,
      by change ([2] : List Nat).Nodup; decide, rfl, rfl, rfl, rfl⟩
  · change MeTTaCalculus.OccurrenceCommits.Enabled (fun _ : Nat => ()) {0, 1}
      (⟨{0}, {1}, {2}, []⟩ : MeTTaCalculus.OccurrenceCommits.Commit Nat Unit)
    decide
  · exact ⟨_, point, known⟩
  · intro future assignment _
    exact ⟨fun _ impossible => False.elim (List.not_mem_nil impossible),
      fun _ impossible => False.elim (List.not_mem_nil impossible)⟩

theorem match_parts (store : List (Constraint mkeys [] ()))
    (pattern template : MData) (row : Row mkeys [] ())
    {future : Interface.Frames.Frame MSig}
    (point : Assignment (Contextual.extend MSig callerFrame locals).arity future.arity)
    (known : X.Models point ((firing store pattern template row).information X
      (initial store pattern template row))) :
    instantiate (Assignment.compose point (Contextual.canonicalOpening MSig callerFrame locals)) (slot 0) =
        instantiate (Assignment.compose point (Contextual.weakenNames MSig callerFrame locals)) pattern ∧
      instantiate (Assignment.compose point (Contextual.canonicalOpening MSig callerFrame locals)) (slot 1) =
        instantiate (Assignment.compose point (Contextual.weakenNames MSig callerFrame locals)) template := by
  rw [information_eq] at known
  have taken := known _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _)))
  change instantiateObservation point (instantiateObservation (Contextual.canonicalOpening MSig callerFrame locals)
      (observe (task (slot 0) (slot 1)))) =
    instantiateObservation point (instantiateObservation (Contextual.weakenNames MSig callerFrame locals)
      (observe (task pattern template))) at taken
  rw [instantiateObservation_comp, instantiateObservation_comp] at taken
  have terms := observe_injective (S := MSig) (source := future.arity) (Γ := []) (sort := ()) taken
  rw [instantiate_task, instantiate_task] at terms
  exact task_inj terms

/-- Restricting a model of the fired information recovers the original
caller, including constraints attached to a privately opened row. -/
theorem restrict_model (store : List (Constraint mkeys [] ()))
    (pattern template : MData) (row : Row mkeys [] ()) {future : Interface.Frames.Frame MSig}
    (point : Assignment (Contextual.extend MSig callerFrame locals).arity future.arity)
    (known : X.Models point ((firing store pattern template row).information X
      (initial store pattern template row))) :
    Models (Assignment.compose point (Contextual.weakenNames MSig callerFrame locals))
      (store ++ rowEquations row pattern) := by
  let caller := Assignment.compose point (Contextual.weakenNames MSig callerFrame locals)
  have old := (observed_models caller (store ++ row.store)).mp
    (Firing.knowledge_solved (X := X) (firing store pattern template row) known)
  have parts := match_parts store pattern template row point known
  rw [information_eq] at known
  have read := known _ (List.mem_append_right _ (List.mem_singleton_self _))
  change instantiateObservation point (instantiateObservation (Contextual.canonicalOpening MSig callerFrame locals)
      (observe (slot 0))) =
    instantiateObservation point (instantiateObservation (Contextual.weakenNames MSig callerFrame locals)
      (observe row.atom)) at read
  rw [instantiateObservation_comp, instantiateObservation_comp] at read
  have selected := observe_injective (S := MSig) (source := future.arity) (Γ := []) (sort := ()) read
  rw [rowEquations, ← List.append_assoc]
  apply (models_append caller _ _).mpr
  refine ⟨old, ?_⟩
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  exact parts.1.symm.trans selected

/-- Readback at a fixed caller assignment existentially hides just the
match rule's helper names. -/
theorem projected_models (store : List (Constraint mkeys [] ()))
    (pattern template : MData) (row : Row mkeys [] ()) {future : Interface.Frames.Frame MSig}
    (caller : Assignment callerFrame.arity future.arity) :
    Models caller (store ++ rowEquations row pattern) ↔
      ∃ point : Assignment (Contextual.extend MSig callerFrame locals).arity future.arity,
        Assignment.compose point (Contextual.weakenNames MSig callerFrame locals) = caller ∧
        X.Models point ((firing store pattern template row).result X
          (initial store pattern template row)).knowledge := by
  refine ⟨extend_model _ _ _ _ caller, ?_⟩
  rintro ⟨point, rfl, known⟩
  exact restrict_model _ _ _ _ point known

/-- Every admitted result reflects a solution of the same source row problem.
An invalid syntactic match cannot be licensed by the semantic adapter. -/
theorem source_of_admitted (store : List (Constraint mkeys [] ()))
    (pattern template : MData) (row : Row mkeys [] ())
    (admitted : (firing store pattern template row).Admits X (initial store pattern template row)) :
    Solvable (store ++ rowEquations row pattern) := by
  obtain ⟨future, point, known⟩ := admitted.2.2.1
  exact ⟨future.Names, future.arity, _, restrict_model _ _ _ _ point known⟩

theorem admitted_iff_source (store : List (Constraint mkeys [] ()))
    (pattern template : MData) (row : Row mkeys [] ()) :
    (firing store pattern template row).Admits X (initial store pattern template row) ↔
      Solvable (store ++ rowEquations row pattern) :=
  ⟨source_of_admitted store pattern template row, admitted_of_source store pattern template row⟩

/-- At every resulting model, the output is the original template read by
the same caller assignment that solves the retained source constraints. -/
theorem output_template (store : List (Constraint mkeys [] ()))
    (pattern template : MData) (row : Row mkeys [] ())
    {future : Interface.Frames.Frame MSig}
    (point : Assignment (Contextual.extend MSig callerFrame locals).arity future.arity)
    (known : X.Models point ((firing store pattern template row).result X
      (initial store pattern template row)).knowledge) :
    instantiateObservation point (((firing store pattern template row).result X
      (initial store pattern template row)).label 2) =
      observe (instantiate (Assignment.compose point (Contextual.weakenNames MSig callerFrame locals)) template) := by
  have parts := match_parts store pattern template row point known
  change instantiateObservation point (instantiateObservation (Contextual.canonicalOpening MSig callerFrame locals)
    (observe (slot 1))) = _
  rw [instantiateObservation_comp]
  exact congrArg observe parts.2

theorem row_retained (store : List (Constraint mkeys [] ()))
    (pattern template : MData) (row : Row mkeys [] ()) :
    ((firing store pattern template row).result X (initial store pattern template row)).present = {1, 2} := by
  change (({0, 1} : Finset Nat) \ {0}) ∪ {2} = {1, 2}
  decide

end Opened

/-- Interpret an occurrence using its supplied opening. Row equations and
the value use the same assignment. A retained argument keeps its name
when the opening acts as the identity on that caller coordinate. -/
def openRow {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}
    (opening : Assignment (fam κ) (fam κ)) (row : Row κ Γ star) : Row κ Γ star :=
  ⟨instantiate opening row.atom,
    row.store.map fun e => (instantiate opening e.1, instantiate opening e.2)⟩

/-- In the existing fully schematic profile, each occurrence opens all of its
names. Scoped clients can prepare their own row and use `Opened.firing`. -/
abbrev initial (scope : Nat) (store : List (Constraint mkeys [] ()))
    (pattern template : MData) (row : Row mkeys [] ()) : RuleSyntax.State Tm Nat :=
  Opened.initial store pattern template (openRow (copyAt mkeys scope) row)

abbrev firing (scope : Nat) (store : List (Constraint mkeys [] ()))
    (pattern template : MData) (row : Row mkeys [] ()) :
    RuleSyntax.Firing Nat E program (initial scope store pattern template row).frame :=
  Opened.firing store pattern template (openRow (copyAt mkeys scope) row)

theorem admitted_iff_source (scope : Nat) (store : List (Constraint mkeys [] ()))
    (pattern template : MData) (row : Row mkeys [] ()) :
    (firing scope store pattern template row).Admits X (initial scope store pattern template row) ↔
      Solvable (store ++ rowUse scope row pattern) :=
  Opened.admitted_iff_source store pattern template (openRow (copyAt mkeys scope) row)

theorem admitted_of_source (scope : Nat) (store : List (Constraint mkeys [] ()))
    (pattern template : MData) (row : Row mkeys [] ())
    (live : Solvable (store ++ rowUse scope row pattern)) :
    (firing scope store pattern template row).Admits X (initial scope store pattern template row) :=
  (admitted_iff_source scope store pattern template row).mpr live

theorem source_of_admitted (scope : Nat) (store : List (Constraint mkeys [] ()))
    (pattern template : MData) (row : Row mkeys [] ())
    (admitted : (firing scope store pattern template row).Admits X (initial scope store pattern template row)) :
    Solvable (store ++ rowUse scope row pattern) :=
  (admitted_iff_source scope store pattern template row).mp admitted

theorem projected_models (scope : Nat) (store : List (Constraint mkeys [] ()))
    (pattern template : MData) (row : Row mkeys [] ()) {future : Interface.Frames.Frame MSig}
    (caller : Assignment callerFrame.arity future.arity) :
    Models caller (store ++ rowUse scope row pattern) ↔
      ∃ point : Assignment (Contextual.extend MSig callerFrame locals).arity future.arity,
        Assignment.compose point (Contextual.weakenNames MSig callerFrame locals) = caller ∧
        X.Models point ((firing scope store pattern template row).result X
          (initial scope store pattern template row)).knowledge :=
  Opened.projected_models store pattern template (openRow (copyAt mkeys scope) row) caller

theorem output_template (scope : Nat) (store : List (Constraint mkeys [] ()))
    (pattern template : MData) (row : Row mkeys [] ())
    {future : Interface.Frames.Frame MSig}
    (point : Assignment (Contextual.extend MSig callerFrame locals).arity future.arity)
    (known : X.Models point ((firing scope store pattern template row).result X
      (initial scope store pattern template row)).knowledge) :
    instantiateObservation point (((firing scope store pattern template row).result X
      (initial scope store pattern template row)).label 2) =
      observe (instantiate (Assignment.compose point (Contextual.weakenNames MSig callerFrame locals)) template) :=
  Opened.output_template store pattern template (openRow (copyAt mkeys scope) row) point known

theorem row_retained (scope : Nat) (store : List (Constraint mkeys [] ()))
    (pattern template : MData) (row : Row mkeys [] ()) :
    ((firing scope store pattern template row).result X (initial scope store pattern template row)).present = {1, 2} :=
  Opened.row_retained store pattern template (openRow (copyAt mkeys scope) row)

namespace Hosted

open Hosting Contextual

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star)
variable {F B : Interface.Frames.Frame S}

abbrev BodyAt (Γ : Ctx S) (star : S.Srt) (frame : Interface.Frames.Frame S) :=
  Term (signature S frame.arity) Γ star

local notation "Body" => BodyAt Γ star
local notation "ReadTerm" => Contextual.Terms S
local notation "ReadFrames" => Frames.contextual S
local notation "ReadExtensions" => Contextual.declarations S

def request (space pattern template stack : Body F) : Body F :=
  altN N (evalN N (N.node .query ![space, pattern, retN N template])) stack

def returned (template stack : Body F) : Body F :=
  altN N (valueN N template) stack

def fact (space term : Body F) : Body F := N.node .fact ![space, term]
def revision (space : Body F) : Body F := N.node .revision ![space]

theorem instantiate_request (point : Assignment F.arity B.arity)
    (sp p t k : Body F) :
    instantiate point (request N sp p t k) =
      request N (instantiate point sp) (instantiate point p) (instantiate point t) (instantiate point k) := by
  unfold request
  rw [instantiate_altN, instantiate_evalN, N.instantiate_node]
  apply congrArg (fun q => altN N (evalN N q) (instantiate point k))
  apply congrArg (N.node .query)
  funext i
  fin_cases i <;> first | rfl | exact instantiate_retN N point t

theorem instantiate_fact (point : Assignment F.arity B.arity) (sp t : Body F) :
    instantiate point (fact N sp t) = fact N (instantiate point sp) (instantiate point t) := by
  unfold fact
  rw [N.instantiate_node]
  apply congrArg (N.node .fact)
  funext i
  fin_cases i <;> rfl

theorem instantiate_revision (point : Assignment F.arity B.arity) (sp : Body F) :
    instantiate point (revision N sp) = revision N (instantiate point sp) := by
  unfold revision
  rw [N.instantiate_node]
  apply congrArg (N.node .revision)
  funext i
  fin_cases i
  rfl

theorem instantiate_returned (point : Assignment F.arity B.arity) (t k : Body F) :
    instantiate point (returned N t k) = returned N (instantiate point t) (instantiate point k) := by
  unfold returned
  rw [instantiate_altN, instantiate_valueN]

private theorem observe_eq {a b : Body F} : observe a = observe b ↔ a = b :=
  ⟨fun same => observe_injective same, congrArg observe⟩

theorem request_inj {a p t k a' p' t' k' : Body F}
    (same : request N a p t k = request N a' p' t' k') :
    a = a' ∧ p = p' ∧ t = t' ∧ k = k' := by
  obtain ⟨focus, stack⟩ := vec2_inj (N.args_eq same)
  obtain ⟨space, pat, body⟩ := vec3_inj (N.args_eq (vec1_inj (N.args_eq focus)))
  exact ⟨space, pat, vec1_inj (N.args_eq body), stack⟩

theorem request_ne_return (space pattern template stack value tail : Body F) :
    request N space pattern template stack ≠
      altN N (evalN N (retN N value)) tail := by
  intro same
  have focus := (vec2_inj (N.args_eq same)).1
  have code := vec1_inj (N.args_eq focus)
  have clash : Tag.query = Tag.ret := N.tag_eq code
  cases clash

local notation "RuleFrame" => (controlFrame (S := S) Γ star)

/-- A version is an occurrence identity. A write replaces that occurrence.
The rule reads the selected fact and revision at the same address, consumes
its request and makes the original continuation with the held template. -/
def rule : Rule ReadTerm :=
  ⟨RuleFrame, ⟨[observe (request N (unk .first) (unk .pattern) (unk .datum) (unk .stack))],
    [observe (fact N (unk .first) (unk .pattern)), observe (revision N (unk .first))],
    [], [], [observe (returned N (unk .datum) (unk .stack))]⟩, []⟩

def firing (N : Nodes S Γ star) {P : RuleSyntax.Program ReadTerm} (member : rule N ∈ P)
    (state : State ReadTerm Nat) (control selected stamp output : Nat) : Firing Nat ReadExtensions P state.frame :=
  canonical (rule N) member ⟨[control], [selected, stamp], [output]⟩ []

private abbrev after (N : Nodes S Γ star) {P : RuleSyntax.Program ReadTerm} (member : rule N ∈ P)
    (state : State ReadTerm Nat) (control selected stamp output : Nat) :=
  (firing N member state control selected stamp output).result ReadFrames state

variable {P : RuleSyntax.Program (Contextual.Terms S)}
  (member : rule (S := S) (Γ := Γ) (star := star) N ∈ P)
  (state : State (Contextual.Terms S) Nat) (control selected stamp output : Nat)

theorem shapes : (firing N member state control selected stamp output).Shapes ReadFrames state :=
  ⟨canonical_fresh state _ member _ _, List.nodup_singleton _, List.nodup_singleton _,
    rfl, rfl, rfl, rfl⟩

private theorem copair_restrict (caller : Assignment F.arity B.arity)
    (locals : Assignment (RuleFrame).arity B.arity) :
    Assignment.compose (copair S (F := F) (N := RuleFrame) (B := B) caller locals)
      (weakenNames S F RuleFrame) = caller := by
  funext name
  exact instantiate_generator (copair S caller locals) (Sum.inl name)

private theorem information {B : Interface.Frames.Frame S}
    (caller : Assignment state.frame.arity B.arity) (localPoint : Assignment (RuleFrame).arity B.arity) :
    (ReadFrames).Models (copair S (F := state.frame) (N := RuleFrame) (B := B) caller localPoint)
        (after N member state control selected stamp output).knowledge ↔
      (ReadFrames).Models caller state.knowledge ∧
      instantiateObservation localPoint (observe (request N (unk .first) (unk .pattern) (unk .datum) (unk .stack))) =
        instantiateObservation caller (state.label control) ∧
      instantiateObservation localPoint (observe (fact N (unk .first) (unk .pattern))) =
        instantiateObservation caller (state.label selected) ∧
      instantiateObservation localPoint (observe (revision N (unk .first))) =
        instantiateObservation caller (state.label stamp) := by
  let u := copair S (F := state.frame) (N := RuleFrame) (B := B) caller localPoint
  let old := weakenNames S state.frame RuleFrame
  let openRule := canonicalOpening S state.frame RuleFrame
  let taken : ReadTerm RuleFrame := observe (request N (unk .first) (unk .pattern) (unk .datum) (unk .stack))
  let read : ReadTerm RuleFrame := observe (fact N (unk .first) (unk .pattern))
  let revisionRow : ReadTerm RuleFrame := observe (revision N (unk .first))
  change (ReadFrames).Models u ((ReadFrames).applyStore old state.knowledge ++
    [(instantiateObservation openRule taken, instantiateObservation old (state.label control))] ++
    [(instantiateObservation openRule read, instantiateObservation old (state.label selected)),
      (instantiateObservation openRule revisionRow, instantiateObservation old (state.label stamp))] ++
        ([] : EquationStore (ReadTerm (extend S state.frame RuleFrame)))) ↔ _
  have restrict : (ReadFrames).comp u old = caller := copair_restrict caller localPoint
  rw [List.append_nil, Frames.models_append, Frames.models_append, Frames.models_applyStore, restrict]
  change ((ReadFrames).Models caller state.knowledge ∧
    (∀ e ∈ [(instantiateObservation openRule taken, instantiateObservation old (state.label control))],
      instantiateObservation u e.1 = instantiateObservation u e.2)) ∧
    (∀ e ∈ [(instantiateObservation openRule read, instantiateObservation old (state.label selected)),
      (instantiateObservation openRule revisionRow, instantiateObservation old (state.label stamp))],
      instantiateObservation u e.1 = instantiateObservation u e.2) ↔ _
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_assoc]
  simp only [u, old, openRule, taken, read, revisionRow,
    copair_weaken (F := state.frame) (N := RuleFrame) (B := B),
    copair_opening (F := state.frame) (N := RuleFrame) (B := B)]

/-- At a fixed caller assignment the available models only restrict that
assignment by the selected read. Fresh rule locals project away. The made
row keeps the stack and template in that very assignment. -/
theorem models {B : Interface.Frames.Frame S}
    (space pattern template stack address datum epoch : Body state.frame)
    (waiting : state.label control = observe (request N space pattern template stack))
    (borrowed : state.label selected = observe (fact N address datum))
    (version : state.label stamp = observe (revision N epoch))
    (caller : Assignment state.frame.arity B.arity) (value : ReadTerm B) :
    ((ReadFrames).Models caller state.knowledge ∧
      instantiate caller space = instantiate caller address ∧
      instantiate caller space = instantiate caller epoch ∧
      instantiate caller pattern = instantiate caller datum ∧
      observe (returned N (instantiate caller template) (instantiate caller stack)) = value) ↔
    ∃ point : Assignment (after N member state control selected stamp output).frame.arity B.arity,
      Assignment.compose point (weakenNames S state.frame RuleFrame) = caller ∧
      (ReadFrames).Models point (after N member state control selected stamp output).knowledge ∧
      instantiateObservation point ((after N member state control selected stamp output).label output) = value := by
  have make := (firing N member state control selected stamp output).result_label_made (X := ReadFrames)
    (shapes N member state control selected stamp output)
    (show (output, instantiateObservation (canonicalOpening S state.frame RuleFrame)
      (observe (returned N (unk .datum) (unk .stack)))) ∈
        (firing N member state control selected stamp output).selection.made.zip
          ((firing N member state control selected stamp output).opened ReadFrames).produce from List.mem_singleton_self _)
  have equations (h : Assignment (RuleFrame).arity B.arity) :
      (ReadFrames).Models (copair S (F := state.frame) (N := RuleFrame) (B := B) caller h)
        (after N member state control selected stamp output).knowledge ↔
      (ReadFrames).Models caller state.knowledge ∧
      request N (h .first) (h .pattern) (h .datum) (h .stack) =
        request N (instantiate caller space) (instantiate caller pattern) (instantiate caller template) (instantiate caller stack) ∧
      fact N (h .first) (h .pattern) = fact N (instantiate caller address) (instantiate caller datum) ∧
      revision N (h .first) = revision N (instantiate caller epoch) := by
    rw [information N member state control selected stamp output, waiting, borrowed, version]
    change ((ReadFrames).Models caller state.knowledge ∧
      observe (instantiate h (request N (unk .first) (unk .pattern) (unk .datum) (unk .stack))) =
        observe (instantiate caller (request N space pattern template stack)) ∧
      observe (instantiate h (fact N (unk .first) (unk .pattern))) =
        observe (instantiate caller (fact N address datum)) ∧
      observe (instantiate h (revision N (unk .first))) = observe (instantiate caller (revision N epoch))) ↔ _
    rw [instantiate_request N (B := B), instantiate_request N (B := B), instantiate_fact N (B := B),
      instantiate_fact N (B := B), instantiate_revision N (B := B), instantiate_revision N (B := B)]
    simp only [unk, instantiate_generator, observe_eq]
  have result (h : Assignment (RuleFrame).arity B.arity) :
      instantiateObservation (copair S (F := state.frame) (N := RuleFrame) (B := B) caller h)
        ((after N member state control selected stamp output).label output) =
          observe (returned N (h .datum) (h .stack)) := by
    rw [make, copair_opening]
    change observe (instantiate h (returned N (unk .datum) (unk .stack))) = _
    rw [instantiate_returned N (B := B)]
    simp only [unk, instantiate_generator]
  constructor
  · rintro ⟨known, loc, epoch', fits, rfl⟩
    let h : Assignment (RuleFrame).arity B.arity := fun
      | .first => instantiate caller space
      | .pattern => instantiate caller pattern
      | .datum => instantiate caller template
      | .stack => instantiate caller stack
      | .second => instantiate caller template
    refine ⟨copair S (F := state.frame) (N := RuleFrame) (B := B) caller h, copair_restrict caller h,
      (equations h).mpr ⟨known, rfl, congrArg₂ (fact N) loc fits, congrArg (revision N) epoch'⟩, result h⟩
  · rintro ⟨point, restrict, known, made⟩
    let h : Assignment (RuleFrame).arity B.arity := fun name => point (.inr name)
    have same : copair S (F := state.frame) (N := RuleFrame) (B := B) caller h = point := by
      funext name
      cases name with
      | inr name => rfl
      | inl name =>
        change caller name = point (.inl name)
        rw [← restrict]
        exact instantiate_generator point (.inl name)
    rw [← same] at known made
    obtain ⟨old, req, dat, stampEq⟩ := (equations h).mp known
    obtain ⟨sp, pattern', held, tail⟩ := request_inj N req
    obtain ⟨loc, fit⟩ := vec2_inj (N.args_eq dat)
    have curr := vec1_inj (N.args_eq stampEq)
    rw [result h, held, tail] at made
    exact ⟨old, sp.symm.trans loc, sp.symm.trans curr, pattern'.symm.trans fit, made⟩

theorem admitted_iff :
    (firing N member state control selected stamp output).Admits ReadFrames state ↔
      Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Enabled
        (fun _ : Nat => ()) state.present (⟨[control], [selected, stamp], [output]⟩ : Selection Nat).commit ∧
      (ReadFrames).Solvable (after N member state control selected stamp output).knowledge := by
  refine ⟨fun admitted => ⟨admitted.2.1, admitted.2.2.1⟩, ?_⟩
  rintro ⟨enabled, live⟩
  refine ⟨shapes N member state control selected stamp output, enabled, live, fun _ _ _ => ?_⟩
  constructor
  · intro _ none
    exact False.elim (List.not_mem_nil none)
  · intro _ none
    exact False.elim (List.not_mem_nil none)

theorem stale_refused (stale : stamp ∉ state.present) :
    ¬ (firing N member state control selected stamp output).Admits ReadFrames state := by
  intro admitted
  apply stale
  apply admitted.2.1.kept_subset
  change stamp ∈ ([selected, stamp] : List Nat).toFinset
  simp

theorem present_result :
    (after N member state control selected stamp output).present = insert output (state.present.erase control) := by
  ext id
  simp [after, firing, canonical, Firing.result, Selection.commit,
    Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.fire, and_comm]

end Hosted
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.NativeQuery.MatchKernel
