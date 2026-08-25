import Mettapedia.Enactive.Finite
import Mathlib.Data.Finset.Image

/-!
# Bennett's 2023 Boolean-program presentation as a finite model

Michael Timothy Bennett's *The Optimal Choice of Hypothesis Is the Weakest,
Not the Shortest* (2023), Definitions 1--2 and 7, represents a declarative
program by a Boolean-valued function on worlds.  His 2024 presentation instead
represents the same object by its set of realizing worlds.

This module proves that the 2023 presentation is a characteristic-set view of
the finite 2024 theory in `Enactive.Finite`.  Statements, completion, and
weakness are transported across an equivalence; they are not installed as a
second foundation.  The task/model bridge follows after these representation
laws.
-/

set_option autoImplicit false

namespace Mettapedia.Enactive.Bennett2023

universe uWorld

variable {World : Type uWorld} [Fintype World] [DecidableEq World]

/-- Bennett's 2023 declarative programs. -/
abbrev Program (World : Type uWorld) := World → Bool

/-- The set-valued meaning of a Boolean declarative program. -/
def truthSet (program : Program World) : Finset World :=
  Finset.univ.filter fun world => program world = true

omit [DecidableEq World] in
@[simp]
theorem mem_truthSet (program : Program World) (world : World) :
    world ∈ truthSet program ↔ program world = true := by
  simp [truthSet]

/-- The characteristic program of a finite fact. -/
def characteristic (fact : Finset World) : Program World :=
  fun world => decide (world ∈ fact)

omit [Fintype World] in
@[simp]
theorem characteristic_eq_true (fact : Finset World) (world : World) :
    characteristic fact world = true ↔ world ∈ fact := by
  simp [characteristic]

@[simp]
theorem characteristic_truthSet (program : Program World) :
    characteristic (truthSet program) = program := by
  funext world
  cases value : program world <;>
    simp [characteristic, truthSet, value]

@[simp]
theorem truthSet_characteristic (fact : Finset World) :
    truthSet (characteristic fact) = fact := by
  ext world
  simp

/-- Boolean programs and finite facts are equivalent by characteristic sets.
This is the representation theorem connecting Bennett's 2023 and 2024
environment formalisms. -/
def programFactEquiv : Program World ≃ Finset World where
  toFun := truthSet
  invFun := characteristic
  left_inv := characteristic_truthSet
  right_inv := truthSet_characteristic

instance : DecidableEq (Program World) := fun left right =>
  decidable_of_iff (truthSet left = truthSet right)
    ⟨fun equal => by
        apply programFactEquiv.injective
        exact equal,
      fun equal => congrArg truthSet equal⟩

/-- A 2023 implementable language is a finite vocabulary of Boolean
declarative programs. -/
structure Layer (World : Type uWorld) [Fintype World] [DecidableEq World] where
  vocabulary : Finset (Program World)

/-- A world realizes a 2023 collection of declarative programs when every
program returns true there. -/
def Realizes (world : World) (programs : Finset (Program World)) : Prop :=
  ∀ program ∈ programs, program world = true

instance (world : World) (programs : Finset (Program World)) :
    Decidable (Realizes world programs) := by
  unfold Realizes
  infer_instance

/-- A 2023 statement candidate is realizable when it has a witnessing world. -/
def Realizable (programs : Finset (Program World)) : Prop :=
  ∃ world : World, Realizes world programs

instance (programs : Finset (Program World)) : Decidable (Realizable programs) := by
  unfold Realizable
  infer_instance

namespace Layer

variable (layer : Layer World)

/-- Bennett's finite implementable language `L_v` in the 2023 presentation. -/
def statements : Finset (Finset (Program World)) :=
  layer.vocabulary.powerset.filter Realizable

/-- A 2023 statement is a realizable subset of the selected vocabulary. -/
abbrev Statement := {programs // programs ∈ layer.statements}

@[simp]
theorem mem_statements {programs : Finset (Program World)} :
    programs ∈ layer.statements ↔
      programs ⊆ layer.vocabulary ∧ Realizable programs := by
  simp [statements]

instance : DecidableEq layer.Statement := inferInstance

/-- Translate the 2023 vocabulary pointwise to its 2024 finite fact
presentation. -/
def toFinite : Mettapedia.Enactive.Finite.Layer World where
  vocabulary := programFactEquiv.finsetCongr layer.vocabulary

theorem realizes_finsetCongr_iff
    (world : World) (programs : Finset (Program World)) :
    Mettapedia.Enactive.Finite.Realizes world
        (programFactEquiv.finsetCongr programs) ↔
      Realizes world programs := by
  constructor
  · intro realized program member
    have mapped : truthSet program ∈ programFactEquiv.finsetCongr programs := by
      rw [Equiv.finsetCongr_apply]
      exact Finset.mem_map.mpr ⟨program, member, rfl⟩
    exact (mem_truthSet program world).mp (realized (truthSet program) mapped)
  · intro realized fact member
    rw [Equiv.finsetCongr_apply, Finset.mem_map] at member
    obtain ⟨program, programMember, rfl⟩ := member
    exact (mem_truthSet program world).mpr (realized program programMember)

theorem realizable_finsetCongr_iff (programs : Finset (Program World)) :
    Mettapedia.Enactive.Finite.Realizable
        (programFactEquiv.finsetCongr programs) ↔
      Realizable programs := by
  constructor
  · rintro ⟨world, realized⟩
    exact ⟨world, (realizes_finsetCongr_iff world programs).mp realized⟩
  · rintro ⟨world, realized⟩
    exact ⟨world, (realizes_finsetCongr_iff world programs).mpr realized⟩

/-- Program-to-fact translation preserves and reflects membership in the
finite language. -/
theorem finsetCongr_mem_statements_iff
    (programs : Finset (Program World)) :
    programFactEquiv.finsetCongr programs ∈ layer.toFinite.statements ↔
      programs ∈ layer.statements := by
  rw [Mettapedia.Enactive.Finite.Layer.mem_statements,
    mem_statements]
  simp only [toFinite]
  constructor
  · rintro ⟨included, realized⟩
    exact ⟨by
      intro program member
      have mapped : programFactEquiv program ∈
          programFactEquiv.finsetCongr layer.vocabulary :=
        included (by simp [member])
      simpa using mapped,
      (realizable_finsetCongr_iff programs).mp realized⟩
  · rintro ⟨included, realized⟩
    exact ⟨by
      intro fact member
      rw [Equiv.finsetCongr_apply, Finset.mem_map] at member
      obtain ⟨program, programMember, rfl⟩ := member
      simp [included programMember],
      (realizable_finsetCongr_iff programs).mpr realized⟩

/-- Translate a 2023 statement to the canonical finite 2024 statement. -/
def Statement.toFinite (source : layer.Statement) : layer.toFinite.Statement :=
  ⟨programFactEquiv.finsetCongr source.val,
    (finsetCongr_mem_statements_iff layer source.val).mpr source.property⟩

/-- Recover a 2023 statement from its finite fact representation. -/
def Statement.ofFinite (source : layer.toFinite.Statement) : layer.Statement :=
  ⟨programFactEquiv.symm.finsetCongr source.val, by
    apply (finsetCongr_mem_statements_iff layer _).mp
    have membership :
        programFactEquiv.finsetCongr
            (programFactEquiv.symm.finsetCongr source.val) ∈
          layer.toFinite.statements := by
      have equality :
          programFactEquiv.finsetCongr
              (programFactEquiv.symm.finsetCongr source.val) = source.val := by
        rw [← Equiv.finsetCongr_symm]
        exact (programFactEquiv.finsetCongr).apply_symm_apply source.val
      rw [equality]
      exact source.property
    exact membership⟩

/-- The two statement representations are equivalent, not merely related. -/
def statementEquiv : layer.Statement ≃ layer.toFinite.Statement where
  toFun := Statement.toFinite layer
  invFun := Statement.ofFinite layer
  left_inv source := by
    apply Subtype.ext
    change programFactEquiv.symm.finsetCongr
        (programFactEquiv.finsetCongr source.val) = source.val
    rw [← Equiv.finsetCongr_symm]
    exact (programFactEquiv.finsetCongr).symm_apply_apply source.val
  right_inv source := by
    apply Subtype.ext
    change programFactEquiv.finsetCongr
        (programFactEquiv.symm.finsetCongr source.val) = source.val
    rw [← Equiv.finsetCongr_symm]
    exact (programFactEquiv.finsetCongr).apply_symm_apply source.val

/-- Translation preserves and reflects the completion order. -/
theorem statementEquiv_le_iff {left right : layer.Statement} :
    (statementEquiv layer left).val ⊆ (statementEquiv layer right).val ↔
      left.val ⊆ right.val := by
  constructor
  · intro included program member
    have mapped : programFactEquiv program ∈
        (statementEquiv layer right).val :=
      included (by
        change programFactEquiv program ∈
          programFactEquiv.finsetCongr left.val
        simp [member])
    change programFactEquiv program ∈
      programFactEquiv.finsetCongr right.val at mapped
    simpa using mapped
  · intro included fact member
    change fact ∈ programFactEquiv.finsetCongr left.val at member
    rw [Equiv.finsetCongr_apply, Finset.mem_map] at member
    obtain ⟨program, programMember, rfl⟩ := member
    change programFactEquiv program ∈
      programFactEquiv.finsetCongr right.val
    simp [included programMember]

/-- The induced equivalence on finite collections preserves and reflects
subset. -/
theorem statementFinsetEquiv_subset_iff
    {left right : Finset layer.Statement} :
    (statementEquiv layer).finsetCongr left ⊆
        (statementEquiv layer).finsetCongr right ↔
      left ⊆ right := by
  constructor
  · intro included source sourceMember
    have mapped : statementEquiv layer source ∈
        (statementEquiv layer).finsetCongr right :=
      included (by
        rw [Equiv.finsetCongr_apply]
        exact Finset.mem_map.mpr ⟨source, sourceMember, rfl⟩)
    rw [Equiv.finsetCongr_apply, Finset.mem_map] at mapped
    obtain ⟨target, targetMember, equal⟩ := mapped
    exact (statementEquiv layer).injective equal ▸ targetMember
  · intro included target targetMember
    rw [Equiv.finsetCongr_apply, Finset.mem_map] at targetMember ⊢
    obtain ⟨source, sourceMember, rfl⟩ := targetMember
    exact ⟨source, included sourceMember, rfl⟩

/-- The 2023 extension `Z_x`. -/
def extension (source : layer.Statement) : Finset layer.Statement :=
  layer.statements.attach.filter fun target => source.val ⊆ target.val

@[simp]
theorem mem_extension {source target : layer.Statement} :
    target ∈ layer.extension source ↔ source.val ⊆ target.val := by
  simp [extension]

/-- Bennett weakness in the 2023 presentation. -/
def weakness (source : layer.Statement) : Nat :=
  (layer.extension source).card

/-- The 2023 extension `Z_S` of a finite set of situations. -/
def extensionSet (sources : Finset layer.Statement) : Finset layer.Statement :=
  layer.statements.attach.filter fun target =>
    ∃ source ∈ sources, source.val ⊆ target.val

@[simp]
theorem mem_extensionSet {sources : Finset layer.Statement}
    {target : layer.Statement} :
    target ∈ layer.extensionSet sources ↔
      ∃ source ∈ sources, source.val ⊆ target.val := by
  simp [extensionSet]

/-- Characteristic-set translation carries the entire 2023 extension to the
2024 extension. -/
theorem extension_agreement (source : layer.Statement) :
    (statementEquiv layer).finsetCongr (layer.extension source) =
      layer.toFinite.extension (statementEquiv layer source) := by
  ext target
  constructor
  · intro member
    rw [Equiv.finsetCongr_apply, Finset.mem_map] at member
    obtain ⟨original, originalMember, rfl⟩ := member
    rw [Mettapedia.Enactive.Finite.Layer.mem_extension]
    exact (statementEquiv_le_iff (layer := layer)).mpr
      ((mem_extension (layer := layer)).mp originalMember)
  · intro member
    have included := member
    rw [Mettapedia.Enactive.Finite.Layer.mem_extension] at included
    have originalMember :
        (statementEquiv layer).symm target ∈ layer.extension source :=
      (mem_extension (layer := layer)).mpr <|
        (statementEquiv_le_iff (layer := layer)).mp <| by
        simpa using included
    simpa [Equiv.finsetCongr_apply] using originalMember

/-- Weakness is representation-invariant: counting Boolean-program
completions and counting their finite characteristic sets give the same number.
This is the exact 2023-to-2024 weakness agreement. -/
theorem weakness_agreement (source : layer.Statement) :
    layer.weakness source =
      layer.toFinite.weakness (statementEquiv layer source) := by
  rw [weakness, Mettapedia.Enactive.Finite.Layer.weakness]
  have congruence := extension_agreement layer source
  have cards := congrArg Finset.card congruence
  simpa [Equiv.finsetCongr_apply] using cards

/-- Characteristic-set translation also carries extensions of situation sets.
This is the set-valued `Z_S`/`E_I` agreement needed by the task bridge. -/
theorem extensionSet_agreement (sources : Finset layer.Statement) :
    (statementEquiv layer).finsetCongr (layer.extensionSet sources) =
      layer.toFinite.extensionSet
        ((statementEquiv layer).finsetCongr sources) := by
  ext target
  constructor
  · intro member
    rw [Equiv.finsetCongr_apply, Finset.mem_map] at member
    obtain ⟨original, originalMember, rfl⟩ := member
    obtain ⟨source, sourceMember, included⟩ :=
      (mem_extensionSet (layer := layer)).mp originalMember
    rw [Mettapedia.Enactive.Finite.Layer.mem_extensionSet]
    exact ⟨statementEquiv layer source, by
      rw [Equiv.finsetCongr_apply]
      exact Finset.mem_map.mpr ⟨source, sourceMember, rfl⟩,
      (statementEquiv_le_iff (layer := layer)).mpr included⟩
  · intro member
    rw [Mettapedia.Enactive.Finite.Layer.mem_extensionSet] at member
    obtain ⟨source, sourceMember, included⟩ := member
    rw [Equiv.finsetCongr_apply, Finset.mem_map] at sourceMember
    obtain ⟨originalSource, originalSourceMember, rfl⟩ := sourceMember
    have originalTargetMember :
        (statementEquiv layer).symm target ∈
          layer.extensionSet sources :=
      (mem_extensionSet (layer := layer)).mpr
        ⟨originalSource, originalSourceMember,
          (statementEquiv_le_iff (layer := layer)).mp (by
            simpa using included)⟩
    rw [Equiv.finsetCongr_apply]
    exact Finset.mem_map.mpr
      ⟨(statementEquiv layer).symm target, originalTargetMember, by simp⟩

end Layer

/-! ## The 2023 task triple and its 2024 policy interpretation -/

/-- Bennett's 2023 task `⟨S,D,M⟩`, with `M` derived below rather than stored
redundantly.  The side condition says every correct decision completes a
situation. -/
structure Task {World : Type uWorld} [Fintype World] [DecidableEq World]
    (layer : Layer World) where
  situations : Finset layer.Statement
  correctDecisions : Finset layer.Statement
  correctDecisions_subset :
    ∀ decision ∈ correctDecisions,
      ∃ situation ∈ situations, situation.val ⊆ decision.val

namespace Task

variable {layer : Layer World}

/-- The decisions available for at least one situation, Bennett's `Z_S`. -/
def decisions (task : Task layer) : Finset layer.Statement :=
  layer.extensionSet task.situations

/-- The model predicate defining the 2023 `M` component:
`Z_S ∩ Z_h = D`. -/
def IsModel (task : Task layer) (hypothesis : layer.Statement) : Prop :=
  task.decisions ∩ layer.extension hypothesis = task.correctDecisions

instance (task : Task layer) (hypothesis : layer.Statement) :
    Decidable (task.IsModel hypothesis) := by
  unfold IsModel
  infer_instance

/-- The derived set `M` of all task models. -/
def models (task : Task layer) : Finset layer.Statement :=
  layer.statements.attach.filter task.IsModel

@[simp]
theorem mem_models {task : Task layer} {hypothesis : layer.Statement} :
    hypothesis ∈ task.models ↔ task.IsModel hypothesis := by
  simp [models]

/-- The 2023 triple translated to the finite 2024 task/policy presentation. -/
def toFinite (task : Task layer) :
    Mettapedia.Enactive.Finite.Task layer.toFinite where
  inputs := (Layer.statementEquiv layer).finsetCongr task.situations
  correctOutputs :=
    (Layer.statementEquiv layer).finsetCongr task.correctDecisions
  correctOutputs_subset := by
    intro output outputMember
    rw [Equiv.finsetCongr_apply, Finset.mem_map] at outputMember
    obtain ⟨decision, decisionMember, rfl⟩ := outputMember
    obtain ⟨situation, situationMember, included⟩ :=
      task.correctDecisions_subset decision decisionMember
    exact ⟨Layer.statementEquiv layer situation, by
      rw [Equiv.finsetCongr_apply]
      exact Finset.mem_map.mpr ⟨situation, situationMember, rfl⟩,
      (Layer.statementEquiv_le_iff (layer := layer)).mpr included⟩

/-- Translating a 2023 model's selected decisions gives exactly the output
selected by the translated 2024 policy. -/
theorem inferredOutputs_agreement (task : Task layer)
    (hypothesis : layer.Statement) :
    (Layer.statementEquiv layer).finsetCongr
        (task.decisions ∩ layer.extension hypothesis) =
      task.toFinite.inferredOutputs (Layer.statementEquiv layer hypothesis) := by
  change (Layer.statementEquiv layer).finsetCongr
      (layer.extensionSet task.situations ∩ layer.extension hypothesis) =
    layer.toFinite.extensionSet
        ((Layer.statementEquiv layer).finsetCongr task.situations) ∩
      layer.toFinite.extension (Layer.statementEquiv layer hypothesis)
  rw [Equiv.finsetCongr_apply, Finset.map_inter,
    ← Equiv.finsetCongr_apply, Layer.extensionSet_agreement,
    ← Equiv.finsetCongr_apply, Layer.extension_agreement]

/-- The theorem-level recovery of the 2023 `M` component: a statement is a
2023 model iff its characteristic-set image is a correct 2024 policy. -/
theorem isModel_iff_isCorrectPolicy (task : Task layer)
    (hypothesis : layer.Statement) :
    task.IsModel hypothesis ↔
      task.toFinite.IsCorrectPolicy (Layer.statementEquiv layer hypothesis) := by
  constructor
  · intro model
    unfold Mettapedia.Enactive.Finite.Task.IsCorrectPolicy
    rw [← inferredOutputs_agreement task hypothesis]
    change (Layer.statementEquiv layer).finsetCongr
        (task.decisions ∩ layer.extension hypothesis) =
      (Layer.statementEquiv layer).finsetCongr task.correctDecisions
    rw [model]
  · intro correct
    unfold Mettapedia.Enactive.Finite.Task.IsCorrectPolicy at correct
    rw [← inferredOutputs_agreement task hypothesis] at correct
    apply (Layer.statementEquiv layer).finsetCongr.injective
    exact correct

/-- The 2023 child relation. -/
def IsChild (child parent : Task layer) : Prop :=
  child.situations ⊂ parent.situations ∧
    child.correctDecisions ⊆ parent.correctDecisions

instance (child parent : Task layer) : Decidable (child.IsChild parent) := by
  unfold IsChild
  infer_instance

/-- Child/parent structure is representation-invariant. -/
theorem isChild_iff_toFinite_isChild (child parent : Task layer) :
    child.IsChild parent ↔ child.toFinite.IsChild parent.toFinite := by
  simp only [IsChild, Mettapedia.Enactive.Finite.Task.IsChild, toFinite]
  constructor
  · rintro ⟨situations, decisions⟩
    exact ⟨by
      constructor
      · intro source member
        rw [Equiv.finsetCongr_apply, Finset.mem_map] at member ⊢
        obtain ⟨original, originalMember, rfl⟩ := member
        exact ⟨original, situations.1 originalMember, rfl⟩
      · intro equal
        apply situations.2
        exact (Layer.statementFinsetEquiv_subset_iff
          (layer := layer)).mp equal,
      by
        intro source member
        rw [Equiv.finsetCongr_apply, Finset.mem_map] at member ⊢
        obtain ⟨original, originalMember, rfl⟩ := member
        exact ⟨original, decisions originalMember, rfl⟩⟩
  · rintro ⟨situations, decisions⟩
    exact ⟨by
      constructor
      · intro source member
        have mapped : Layer.statementEquiv layer source ∈
            (Layer.statementEquiv layer).finsetCongr parent.situations :=
          situations.1 (by
            rw [Equiv.finsetCongr_apply]
            exact Finset.mem_map.mpr ⟨source, member, rfl⟩)
        rw [Equiv.finsetCongr_apply, Finset.mem_map] at mapped
        obtain ⟨target, targetMember, equal⟩ := mapped
        exact (Layer.statementEquiv layer).injective equal ▸ targetMember
      · intro equal
        exact situations.2
          ((Layer.statementFinsetEquiv_subset_iff
            (layer := layer)).mpr equal),
      by
        intro source member
        have mapped : Layer.statementEquiv layer source ∈
            (Layer.statementEquiv layer).finsetCongr parent.correctDecisions :=
          decisions (by
            rw [Equiv.finsetCongr_apply]
            exact Finset.mem_map.mpr ⟨source, member, rfl⟩)
        rw [Equiv.finsetCongr_apply, Finset.mem_map] at mapped
        obtain ⟨target, targetMember, equal⟩ := mapped
        exact (Layer.statementEquiv layer).injective equal ▸ targetMember⟩

end Task

/-! ## Executable representation and task canaries -/

namespace Canary

def trueProgram : Program Bool := fun world => world

def falseProgram : Program Bool := fun world => !world

def topProgram : Program Bool := fun _ => true

def boolLayer : Layer Bool where
  vocabulary := {trueProgram, falseProgram, topProgram}

def emptyStatement : boolLayer.Statement :=
  ⟨∅, by decide⟩

def trueStatement : boolLayer.Statement :=
  ⟨{trueProgram}, by decide⟩

/-- Positive representation canary: the Boolean program for truth denotes the
singleton finite fact containing `true`. -/
theorem trueProgram_truthSet :
    truthSet trueProgram = {true} := by
  decide

/-- Negative representation canary: the truth program is not confused with
the universally true program. -/
theorem trueProgram_ne_topProgram : trueProgram ≠ topProgram := by
  intro equal
  have := congrFun equal false
  simp [trueProgram, topProgram] at this

/-- A concrete 2023 task whose correct decisions are exactly the completions
allowed by `trueStatement`. -/
def truePolicyTask : Task boolLayer where
  situations := {emptyStatement}
  correctDecisions := boolLayer.extension trueStatement
  correctDecisions_subset := by
    intro decision decisionMember
    exact ⟨emptyStatement, by simp, Finset.empty_subset _⟩

/-- Positive model canary: the intended true-only hypothesis is a model. -/
theorem trueStatement_isModel :
    truePolicyTask.IsModel trueStatement := by
  decide

/-- Negative model canary: the unconstrained statement permits too many
decisions and is not a model of the true-only task. -/
theorem emptyStatement_not_model :
    ¬ truePolicyTask.IsModel emptyStatement := by
  decide

def parentTask : Task boolLayer where
  situations := {emptyStatement, trueStatement}
  correctDecisions := boolLayer.extension trueStatement
  correctDecisions_subset := by
    intro decision decisionMember
    exact ⟨emptyStatement, by simp, Finset.empty_subset _⟩

/-- Positive child canary. -/
theorem truePolicyTask_isChild_parent :
    truePolicyTask.IsChild parentTask := by
  decide

/-- Negative child canary: strictness prevents a task from being its own
child. -/
theorem truePolicyTask_not_child_self :
    ¬ truePolicyTask.IsChild truePolicyTask := by
  decide

end Canary

#print axioms programFactEquiv
#print axioms Layer.statementEquiv_le_iff
#print axioms Layer.extension_agreement
#print axioms Layer.weakness_agreement
#print axioms Task.isModel_iff_isCorrectPolicy
#print axioms Task.isChild_iff_toFinite_isChild
#print axioms Canary.emptyStatement_not_model
#print axioms Canary.truePolicyTask_isChild_parent

end Mettapedia.Enactive.Bennett2023
