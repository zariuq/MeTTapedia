import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationResultTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationExecution

/-!
# Actual publication runs through coherent helper transport

Each source application uses the canonical pullback of its helper telescope
along the current state comparison. The newly solved target frame is retained,
so the comparison for the following application is the derived result map.
This constructs complete runs of the publication step. A separately authored
program's rule-table membership or permission is not inferred from a state
isomorphism.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.RunTransport

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type} [DecidableEq O]

def application {source target : State rules O} (comparison : PlainIso levels source target)
    (candidate : Application levels O source) : Application levels O target :=
  ApplicationTransport.carry candidate comparison (candidate.schema.helpers.reindex comparison.frame.hom)
    (liftIso comparison.frame candidate.schema.helpers)
    (Helpers.lift_weaken comparison.frame.hom candidate.schema.helpers)

theorem admits {source target : State rules O} (comparison : PlainIso levels source target)
    (candidate : Application levels O source) :
    (realizationStep levels O).Admits (application comparison candidate) ↔
      (realizationStep levels O).Admits candidate :=
  ApplicationTransport.native_admits candidate comparison _ _ _

def after {source target : State rules O} (comparison : PlainIso levels source target)
    (candidate : Application levels O source) (accepted : (realizationStep levels O).Admits candidate) :
    PlainIso levels ((realizationStep levels O).result candidate accepted)
      ((realizationStep levels O).result (application comparison candidate)
        ((admits comparison candidate).mpr accepted)) :=
  ApplicationTransport.nativeResultIso candidate comparison _ _ _ accepted

def move : {source target : State rules O} → (comparison : PlainIso levels source target) →
    (run : (realizationStep levels O).Run source) → (realizationStep levels O).Run target
  | _, _, _, .nil _ => .nil _
  | _, _, comparison, .cons candidate accepted rest =>
      .cons (application comparison candidate) ((admits comparison candidate).mpr accepted)
        (move (after comparison candidate accepted) rest)

def endpoint : {source target : State rules O} → (comparison : PlainIso levels source target) →
    (run : (realizationStep levels O).Run source) → PlainIso levels run.last (move comparison run).last
  | _, _, comparison, .nil _ => comparison
  | _, _, comparison, .cons candidate accepted rest => endpoint (after comparison candidate accepted) rest

theorem event_count : ∀ {source target : State rules O} (comparison : PlainIso levels source target)
    (run : (realizationStep levels O).Run source), (move comparison run).word.length = run.word.length
  | _, _, _, .nil _ => rfl
  | _, _, comparison, .cons candidate accepted rest =>
      congrArg Nat.succ (event_count (after comparison candidate accepted) rest)

theorem typed_results {source target : State rules O} (comparison : PlainIso levels source target)
    (run : (realizationStep levels O).Run source) (occurrence : O) :
    (move comparison run).last.label occurrence =
      (run.last.label occurrence).reindex (endpoint comparison run).frame.hom :=
  (endpoint comparison run).label occurrence

theorem exact_knowledge {source target : State rules O} (comparison : PlainIso levels source target)
    (run : (realizationStep levels O).Run source) :
    (frames levels).Equivalent
      ((frames levels).applyStore (endpoint comparison run).frame.hom run.last.knowledge)
      (move comparison run).last.knowledge := (endpoint comparison run).knowledge

theorem after_frame {source target : State rules O} (comparison : PlainIso levels source target)
    (candidate : Application levels O source) (accepted : (realizationStep levels O).Admits candidate) :
    (after comparison candidate accepted).frame.hom = 𝟙 candidate.target := rfl

theorem refinement_square : ∀ {source target : State rules O} (comparison : PlainIso levels source target)
    (run : (realizationStep levels O).Run source),
    (move comparison run).toLast ≫ comparison.frame.hom =
      (endpoint comparison run).frame.hom ≫ run.toLast
  | _, _, comparison, .nil _ => by
      change (𝟙 _) ≫ comparison.frame.hom = comparison.frame.hom ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
  | _, _, comparison, .cons candidate accepted rest => by
      have one := ApplicationTransport.refinement_square candidate comparison
        (candidate.schema.helpers.reindex comparison.frame.hom)
        (liftIso comparison.frame candidate.schema.helpers)
        (Helpers.lift_weaken comparison.frame.hom candidate.schema.helpers)
      have following := refinement_square (after comparison candidate accepted) rest
      rw [after_frame] at following
      have following' : (move (after comparison candidate accepted) rest).toLast =
          (endpoint (after comparison candidate accepted) rest).frame.hom ≫ rest.toLast :=
        (Category.comp_id (move (after comparison candidate accepted) rest).toLast).symm.trans following
      change ((move (after comparison candidate accepted) rest).toLast ≫
        ((application comparison candidate).answer ≫ (application comparison candidate).schema.helpers.weaken)) ≫
        comparison.frame.hom =
        (endpoint (after comparison candidate accepted) rest).frame.hom ≫
          (rest.toLast ≫ (candidate.answer ≫ candidate.schema.helpers.weaken))
      have localSquare :
          ((application comparison candidate).answer ≫ (application comparison candidate).schema.helpers.weaken) ≫
            comparison.frame.hom = candidate.answer ≫ candidate.schema.helpers.weaken :=
        (Category.assoc _ _ _).trans one
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun arrow => (move (after comparison candidate accepted) rest).toLast ≫ arrow) localSquare).trans
          ((congrArg (fun arrow => arrow ≫ (candidate.answer ≫ candidate.schema.helpers.weaken)) following').trans
            (Category.assoc _ _ _)))

/-- This forgets neither applications nor their settlement, but it does
forget the program-table index. Consumers needing rule identity use the
separate retained rule word below; table closure under transport is additional. -/
def realize {program : Program levels O}
    {permission : {state : State rules O} → Candidate program state → Prop} :
    {state : State rules O} → (execution : program.Execution permission state) →
      (realizationStep levels O).Run state
  | _, .nil state => .nil state
  | _, .cons candidate accepted _ rest =>
      .cons candidate.application ((realization_admits_iff candidate.application).mpr accepted)
        ((realization_result candidate.application accepted).symm ▸ realize rest)

def origins {program : Program levels O}
    {permission : {state : State rules O} → Candidate program state → Prop}
    {state : State rules O} (execution : program.Execution permission state) : List Nat :=
  execution.word.map (fun event => event.2.ruleIndex.val)

theorem realize_word {program : Program levels O}
    {permission : {state : State rules O} → Candidate program state → Prop} :
    ∀ {state : State rules O} (execution : program.Execution permission state),
      (realize execution).word = execution.word.map (fun event => ⟨event.1, event.2.application⟩)
  | _, .nil _ => rfl
  | _, .cons candidate accepted allowed rest => by
      simp only [realize, Step.Run.word, Step.Run.word_cast, Program.Execution.word, List.map_cons]
      exact congrArg (List.cons _) (realize_word rest)

theorem origin_count {program : Program levels O}
    {permission : {state : State rules O} → Candidate program state → Prop}
    {source target : State rules O} (comparison : PlainIso levels source target)
    (execution : program.Execution permission source) :
    (origins execution).length = (move comparison (realize execution)).word.length := by
  rw [event_count, realize_word, List.length_map]
  exact List.length_map _

/-- A retained source event includes its actual rule-table index, selected
occurrences and solver evidence. Pairing positions preserves the entire
source event, including repeated rule identities, beside the new firing. -/
def ledger {program : Program levels O}
    {permission : {state : State rules O} → Candidate program state → Prop}
    {source target : State rules O} (comparison : PlainIso levels source target)
    (execution : program.Execution permission source) :=
  execution.word.zip (move comparison (realize execution)).word

theorem ledger_sources {program : Program levels O}
    {permission : {state : State rules O} → Candidate program state → Prop}
    {source target : State rules O} (comparison : PlainIso levels source target)
    (execution : program.Execution permission source) :
    (ledger comparison execution).map Prod.fst = execution.word := by
  apply List.map_fst_zip
  rw [event_count, realize_word, List.length_map]

theorem ledger_targets {program : Program levels O}
    {permission : {state : State rules O} → Candidate program state → Prop}
    {source target : State rules O} (comparison : PlainIso levels source target)
    (execution : program.Execution permission source) :
    (ledger comparison execution).map Prod.snd = (move comparison (realize execution)).word := by
  apply List.map_snd_zip
  rw [event_count, realize_word, List.length_map]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.RunTransport

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.RunTransport.typed_results
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.RunTransport.realize_word
