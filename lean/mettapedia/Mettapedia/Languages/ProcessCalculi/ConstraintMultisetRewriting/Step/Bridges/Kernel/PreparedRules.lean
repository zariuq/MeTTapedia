import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.InterpretedFrames

/-!
# Finite interpreted rule schemas with explicit prepared witnesses

A schema reads its prepared local values from a certificate occurrence. Its
opening remains fresh; reading the certificate, rather than choosing a
ground opening, determines the locals. Field premises are ordinary take and
read patterns, and the guard is an equality between interpreted terms.

The result below is a semantic admission theorem for the actual RuleSyntax
step. Producing certificates, interpreting a particular source guard, and
executing its operations require separate constructions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.PreparedRules

open InterpretedFrames
open MeTTaCalculus.OccurrenceCommits (Enabled)

universe u v w

structure Schema (Value : Type v) where
  locals : Frame.{u}
  certificate : locals.Carrier → Value
  certificate_injective : Function.Injective certificate
  proposition : Prop → Value
  proposition_injective : Function.Injective proposition
  take : List (Terms Value locals)
  read : List (Terms Value locals)
  produce : List (Terms Value locals)
  guard : locals.Carrier → Prop

namespace Schema

variable {Value : Type v} (schema : Schema Value)

def rule : RuleSyntax.Rule (Terms Value) where
  locals := schema.locals
  body := {
    take := schema.take
    read := schema.certificate :: schema.read
    tell := []
    checks := [.equal (fun locals => schema.proposition (schema.guard locals))
      (fun _ => schema.proposition True)]
    produce := schema.produce }
  collect := []

def selected {Occurrence : Type w} (certificate : Occurrence) (selection : Selection Occurrence) :
    Selection Occurrence :=
  ⟨selection.taken, certificate :: selection.read, selection.made⟩

def firing {Occurrence : Type w} {program : RuleSyntax.Program (Terms Value)}
    {old : Frame.{u}} (member : schema.rule ∈ program)
    (certificate : Occurrence) (selection : Selection Occurrence) :
    RuleSyntax.Firing Occurrence extensions program old :=
  canonical schema.rule member (Schema.selected certificate selection)

end Schema

def Matches {Value : Type v} {Occurrence : Type w} {locals : Frame.{u}}
    (patterns : List (Terms Value locals)) (selected : List Occurrence)
    (rows : Occurrence → Value) (environment : locals.Carrier) : Prop :=
  ∀ pair ∈ patterns.zip selected, pair.1 environment = rows pair.2

theorem matching_satisfies {Value : Type v} {Occurrence : Type w}
    {old locals : Frame.{u}} (patterns : List (Terms Value locals)) (selected : List Occurrence)
    (rows : Occurrence → Terms Value old) (environment : (extend old locals).Carrier) :
    Satisfies (patterns.zipWith (fun pattern occurrence =>
      ((fun value : (extend old locals).Carrier => pattern value.2), fun value => rows occurrence value.1))
      selected) environment ↔
      Matches patterns selected (fun occurrence => rows occurrence environment.1) environment.2 := by
  induction patterns generalizing selected with
  | nil => simp [Satisfies, Matches]
  | cons pattern rest ih =>
      cases selected with
      | nil => simp [Satisfies, Matches]
      | cons occurrence later =>
          simpa [Satisfies, Matches] using and_congr_right (fun _ => ih later)

theorem satisfies_append {Value : Type v} {frame : Frame.{u}}
    (first second : EquationStore (Terms Value frame)) (environment : frame.Carrier) :
    Satisfies (first ++ second) environment ↔
      Satisfies first environment ∧ Satisfies second environment := by
  simp only [Satisfies, List.forall_mem_append]

theorem satisfies_reindexed {Value : Type v} {before after : Frame.{u}}
    (equations : EquationStore (Terms Value before)) (substitution : Hom before after)
    (environment : after.Carrier) :
    Satisfies (equations.map fun equation =>
      (equation.1 ∘ substitution, equation.2 ∘ substitution)) environment ↔
      Satisfies equations (substitution environment) := by
  simp only [Satisfies, List.forall_mem_map, Function.comp_apply]

theorem information_iff {Value : Type v} {Occurrence : Type w}
    {program : RuleSyntax.Program (Terms Value)}
    (schema : Schema Value) (member : schema.rule ∈ program)
    (state : RuleSyntax.State (Terms Value) Occurrence)
    (certificate : Occurrence) (selection : Selection Occurrence)
    (environment : (extend state.frame schema.locals).Carrier) :
    Satisfies ((schema.firing (old := state.frame) member certificate selection).information
      (frames Value) state) environment ↔
      Satisfies state.knowledge environment.1 ∧
      Matches schema.take selection.taken (fun occurrence => state.label occurrence environment.1)
        environment.2 ∧
      schema.certificate environment.2 = state.label certificate environment.1 ∧
      Matches schema.read selection.read (fun occurrence => state.label occurrence environment.1)
        environment.2 := by
  simp only [RuleSyntax.Firing.information, RuleSyntax.Firing.matching, Schema.firing,
    canonical, Schema.rule, Schema.selected, RuleSyntax.Firing.opened,
    RuleSyntax.Firing.row, RuleInstance.map, Frames.applyStore, frames, extensions,
    List.map_nil, List.append_nil, List.zipWith_map_left]
  rw [satisfies_append, satisfies_append, satisfies_reindexed]
  simp only [Function.comp_def]
  rw [matching_satisfies, matching_satisfies]
  simp [Matches, and_assoc]

theorem holds_iff {Value : Type v} {Occurrence : Type w}
    {program : RuleSyntax.Program (Terms Value)}
    (schema : Schema Value) (member : schema.rule ∈ program)
    (state : RuleSyntax.State (Terms Value) Occurrence)
    (certificate : Occurrence) (selection : Selection Occurrence)
    {later : Frame.{u}} (substitution : Hom (extend state.frame schema.locals) later) :
    (schema.firing (old := state.frame) member certificate selection).Holds (frames Value) state substitution ↔
      ∀ environment, schema.guard (substitution environment).2 := by
  change ((∀ check ∈ [Check.equal
    (fun environment => schema.proposition (schema.guard environment.2))
    (fun _ => schema.proposition True)],
      RuleSyntax.checkHolds (frames Value) substitution _ state.present check) ∧
      ∀ query ∈ ([] : List (Terms Value (extend state.frame schema.locals) × Finset Occurrence)),
        RuleSyntax.matchesAt (frames Value) substitution _ state.present query.1 = query.2) ↔ _
  simp only [List.mem_singleton, forall_eq, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true, RuleSyntax.checkHolds]
  constructor
  · intro same environment
    have equal : schema.guard (substitution environment).2 = True :=
      schema.proposition_injective (congrFun same environment)
    exact equal.mpr trivial
  · intro holds
    funext environment
    apply congrArg schema.proposition
    exact propext ⟨fun _ => trivial, fun _ => holds environment⟩

theorem locals_of_information {Value : Type v} {Occurrence : Type w}
    {program : RuleSyntax.Program (Terms Value)}
    (schema : Schema Value) (member : schema.rule ∈ program)
    (state : RuleSyntax.State (Terms Value) Occurrence)
    (certificate : Occurrence) (selection : Selection Occurrence)
    (chosen : schema.locals.Carrier)
    (certificateValue : ∀ environment, state.label certificate environment = schema.certificate chosen)
    (environment : (extend state.frame schema.locals).Carrier)
    (satisfies : Satisfies ((schema.firing (old := state.frame) member certificate selection).information
      (frames Value) state) environment) : environment.2 = chosen := by
  have fixed := ((information_iff schema member state certificate selection environment).mp satisfies).2.2.1
  exact schema.certificate_injective (fixed.trans (certificateValue environment.1))

theorem information_solvable_iff {Value : Type v} {Occurrence : Type w}
    {program : RuleSyntax.Program (Terms Value)}
    (schema : Schema Value) (member : schema.rule ∈ program)
    (state : RuleSyntax.State (Terms Value) Occurrence)
    (certificate : Occurrence) (selection : Selection Occurrence)
    (chosen : schema.locals.Carrier)
    (certificateValue : ∀ environment, state.label certificate environment = schema.certificate chosen) :
    (frames Value).Solvable ((schema.firing (old := state.frame) member certificate selection).information
      (frames Value) state) ↔
      ∃ environment, Satisfies state.knowledge environment ∧
        Matches schema.take selection.taken (fun occurrence => state.label occurrence environment) chosen ∧
        Matches schema.read selection.read (fun occurrence => state.label occurrence environment) chosen := by
  rw [InterpretedFrames.solvable_iff]
  constructor
  · rintro ⟨environment, satisfies⟩
    have locals := locals_of_information schema member state certificate selection chosen
      certificateValue environment satisfies
    obtain ⟨old, takes, _, reads⟩ :=
      (information_iff schema member state certificate selection environment).mp satisfies
    exact ⟨environment.1, old, locals ▸ takes, locals ▸ reads⟩
  · rintro ⟨environment, old, takes, reads⟩
    exact ⟨(environment, chosen),
      (information_iff schema member state certificate selection (environment, chosen)).mpr
        ⟨old, takes, (certificateValue environment).symm, reads⟩⟩

theorem guard_entailment_iff {Value : Type v} {Occurrence : Type w}
    {program : RuleSyntax.Program (Terms Value)}
    (schema : Schema Value) (member : schema.rule ∈ program)
    (state : RuleSyntax.State (Terms Value) Occurrence)
    (certificate : Occurrence) (selection : Selection Occurrence)
    (chosen : schema.locals.Carrier)
    (certificateValue : ∀ environment, state.label certificate environment = schema.certificate chosen)
    (solvable : (frames Value).Solvable
      ((schema.firing (old := state.frame) member certificate selection).information (frames Value) state)) :
    (frames Value).Entails
      ((schema.firing (old := state.frame) member certificate selection).information (frames Value) state)
      (fun _ substitution =>
        (schema.firing (old := state.frame) member certificate selection).Holds (frames Value) state substitution) ↔
      schema.guard chosen := by
  constructor
  · intro entails
    obtain ⟨environment, satisfies⟩ := (InterpretedFrames.solvable_iff _).mp solvable
    have sameLocals := locals_of_information schema member state certificate selection chosen
      certificateValue environment satisfies
    have models := (models_iff (fun _ : ground.Carrier => environment) _).mpr (fun _ => satisfies)
    have guard := (holds_iff schema member state certificate selection
      (fun _ : ground.Carrier => environment)).mp (entails ground (fun _ => environment) models) PUnit.unit
    exact sameLocals ▸ guard
  · intro guard later substitution models
    apply (holds_iff schema member state certificate selection substitution).mpr
    intro environment
    have sameLocals := locals_of_information schema member state certificate selection chosen
      certificateValue (substitution environment) ((models_iff substitution _).mp models environment)
    exact sameLocals.symm ▸ guard

/-- The actual schema admission is a physical selection, compatible reads,
and the guard on the prepared values. No source transition relation is used
as a field of the target step. -/
theorem admitted_iff {Value : Type v} {Occurrence : Type w} [DecidableEq Occurrence]
    {program : RuleSyntax.Program (Terms Value)}
    (schema : Schema Value) (member : schema.rule ∈ program)
    (state : RuleSyntax.State (Terms Value) Occurrence)
    (certificate : Occurrence) (selection : Selection Occurrence)
    (chosen : schema.locals.Carrier)
    (certificateValue : ∀ environment, state.label certificate environment = schema.certificate chosen) :
    (RuleSyntax.step (frames Value) Occurrence extensions program).Admits
      (schema.firing (old := state.frame) member certificate selection) ↔
      selection.taken.Nodup ∧ selection.made.Nodup ∧
      schema.take.length = selection.taken.length ∧ schema.read.length = selection.read.length ∧
      schema.produce.length = selection.made.length ∧
      Enabled (fun _ : Occurrence => ()) state.present
        ((Schema.selected certificate selection).commit (T := Unit)) ∧
      (∃ environment, Satisfies state.knowledge environment ∧
        Matches schema.take selection.taken (fun occurrence => state.label occurrence environment) chosen ∧
        Matches schema.read selection.read (fun occurrence => state.label occurrence environment) chosen) ∧
      schema.guard chosen := by
  change (schema.firing (old := state.frame) member certificate selection).Admits (frames Value) state ↔ _
  constructor
  · rintro ⟨⟨_, taken, made, takeLength, readLength, produceLength, _⟩, enabled, solvable, entails⟩
    refine ⟨taken, made, takeLength, ?_, produceLength, enabled,
      (information_solvable_iff schema member state certificate selection chosen certificateValue).mp solvable,
      (guard_entailment_iff schema member state certificate selection chosen certificateValue solvable).mp entails⟩
    exact Nat.succ.inj readLength
  · rintro ⟨taken, made, takeLength, readLength, produceLength, enabled, compatible, guard⟩
    have solvable := (information_solvable_iff schema member state certificate selection chosen certificateValue).mpr compatible
    refine ⟨⟨canonical_fresh state schema.rule member (Schema.selected certificate selection),
      taken, made, takeLength, ?_, produceLength, rfl⟩, enabled, solvable,
      (guard_entailment_iff schema member state certificate selection chosen certificateValue solvable).mpr guard⟩
    exact congrArg Nat.succ readLength

theorem produced_readout {Value : Type v} {Occurrence : Type w} [DecidableEq Occurrence]
    {program : RuleSyntax.Program (Terms Value)}
    (schema : Schema Value) (member : schema.rule ∈ program)
    (state : RuleSyntax.State (Terms Value) Occurrence)
    (certificate : Occurrence) (selection : Selection Occurrence)
    (chosen : schema.locals.Carrier)
    (certificateValue : ∀ environment, state.label certificate environment = schema.certificate chosen)
    (admitted : (schema.firing (old := state.frame) member certificate selection).Admits (frames Value) state)
    (occurrence : Occurrence) (output : Terms Value schema.locals)
    (made : (occurrence, fun environment => output environment.2) ∈
      (schema.firing (old := state.frame) member certificate selection).selection.made.zip
        ((schema.firing (old := state.frame) member certificate selection).opened (frames Value)).produce)
    (environment : (extend state.frame schema.locals).Carrier)
    (satisfies : Satisfies
      ((schema.firing (old := state.frame) member certificate selection).result (frames Value) state).knowledge
      environment) :
    ((schema.firing (old := state.frame) member certificate selection).result (frames Value) state).label
      occurrence environment = output chosen := by
  have labelled := RuleSyntax.Firing.result_label_made
    (schema.firing (old := state.frame) member certificate selection) admitted.1 made
  have localValues := locals_of_information schema member state certificate selection chosen
    certificateValue environment satisfies
  exact (congrFun labelled environment).trans (congrArg output localValues)

theorem other_readout {Value : Type v} {Occurrence : Type w} [DecidableEq Occurrence]
    {program : RuleSyntax.Program (Terms Value)}
    (schema : Schema Value) (member : schema.rule ∈ program)
    (state : RuleSyntax.State (Terms Value) Occurrence)
    (certificate : Occurrence) (selection : Selection Occurrence)
    (occurrence : Occurrence) (missing : occurrence ∉ selection.made)
    (environment : (extend state.frame schema.locals).Carrier) :
    ((schema.firing (old := state.frame) member certificate selection).result (frames Value) state).label
      occurrence environment = state.label occurrence environment.1 := by
  exact congrFun (RuleSyntax.Firing.result_label_other
    (schema.firing (old := state.frame) member certificate selection) missing) environment

theorem false_guard_refused {Value : Type v} {Occurrence : Type w} [DecidableEq Occurrence]
    {program : RuleSyntax.Program (Terms Value)}
    (schema : Schema Value) (member : schema.rule ∈ program)
    (state : RuleSyntax.State (Terms Value) Occurrence)
    (certificate : Occurrence) (selection : Selection Occurrence)
    (chosen : schema.locals.Carrier)
    (certificateValue : ∀ environment, state.label certificate environment = schema.certificate chosen)
    (refused : ¬ schema.guard chosen) :
    ¬ (RuleSyntax.step (frames Value) Occurrence extensions program).Admits
      (schema.firing (old := state.frame) member certificate selection) := by
  intro admitted
  exact refused ((admitted_iff schema member state certificate selection chosen certificateValue).mp admitted).2.2.2.2.2.2.2

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.PreparedRules
