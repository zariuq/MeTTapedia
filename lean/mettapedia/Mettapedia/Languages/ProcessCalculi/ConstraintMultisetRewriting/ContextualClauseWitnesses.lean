import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalRealizations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalSourceProblem

/-!
# Joint source models expose one shared query and per-port row realizations

All witnesses live in one future declaration family. Query bindings and
the caller valuation remain shared across every source port. Each use of
a stored schema has its own private images and latent conditions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseWitnesses

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualConjunctiveQueries ContextualConditionalRows ContextualConditionalRealizations

variable {S : Signature} {Query Local Shared Next O : Type}
    (queries : Query → MetaArity S) (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
    {next : Next → MetaArity S}

def caller (candidate : Assignment (family queries locals captures) next) : Assignment captures next :=
  fun name => candidate (.inr (.inr name))

def queryBodies (candidate : Assignment (family queries locals captures) next) : Assignment queries next :=
  fun name => candidate (.inl name)

def rowBodies (candidate : Assignment (family queries locals captures) next) (scope : Nat) : Assignment locals next :=
  fun name => candidate (.inr (.inl ⟨scope, name⟩))

theorem captures_square (candidate : Assignment (family queries locals captures) next) :
    Assignment.compose candidate (captureEmbedding queries locals captures) = caller queries locals captures candidate := by
  funext name
  change instantiate candidate (instantiate (rowEmbedding queries locals captures)
    (generator (rowFamily locals captures) (.inr name))) = _
  erw [instantiate_generator, instantiate_generator]
  rfl

theorem query_square (candidate : Assignment (family queries locals captures) next) :
    Assignment.compose candidate (queryEmbedding queries locals captures) =
      valuation queries captures (queryBodies queries locals captures candidate) (caller queries locals captures candidate) := by
  funext name
  cases name <;> exact instantiate_generator _ _

theorem row_square (candidate : Assignment (family queries locals captures) next) (scope : Nat) :
    Assignment.compose candidate (Assignment.compose (rowEmbedding queries locals captures)
      (ContextualFreshening.assignment locals captures scope)) =
      valuation locals captures (rowBodies queries locals captures candidate scope) (caller queries locals captures candidate) := by
  funext name
  cases name with
  | inl name =>
      change instantiate candidate (instantiate (rowEmbedding queries locals captures)
        (generator (rowFamily locals captures) (.inl (ScopedVar.at scope name)))) = _
      erw [instantiate_generator, instantiate_generator]
      rfl
  | inr name =>
      change instantiate candidate (instantiate (rowEmbedding queries locals captures)
        (generator (rowFamily locals captures) (.inr name))) = _
      erw [instantiate_generator, instantiate_generator]
      rfl

theorem row_value (candidate : Assignment (family queries locals captures) next) (scope : Nat)
    {Γ : Ctx S} {sort : S.Srt} (row : Row locals captures Γ sort) :
    instantiate candidate (instantiate (rowEmbedding queries locals captures) (row.viewAt locals captures scope)) =
      instantiate (valuation locals captures (rowBodies queries locals captures candidate scope)
        (caller queries locals captures candidate)) (ContextualStoredRows.asTemplate locals captures row.value) := by
  change instantiate candidate (instantiate (rowEmbedding queries locals captures)
    (ContextualStoredRows.viewAt locals captures scope row.value)) = _
  rw [ContextualStoredRows.viewAt_eq_freshening, ContextualFreshening.termAt,
    ← Assignment.instantiate_compose, ← Assignment.instantiate_compose, ← Assignment.compose_associative, row_square]

private theorem models_flatten_ofFn {V : Type} {declaration : V → MetaArity S} {count : Nat}
    (candidate : Assignment declaration next) (problems : Fin count → ContextualResidual.Problem declaration) :
    ContextualResidual.Models candidate (List.ofFn problems).flatten ↔
      ∀ port, ContextualResidual.Models candidate (problems port) := by
  constructor
  · intro models port equation member
    exact models equation (List.mem_flatten.mpr ⟨problems port, List.mem_ofFn.mpr ⟨port, rfl⟩, member⟩)
  · intro models equation member
    obtain ⟨problem, present, inside⟩ := List.mem_flatten.mp member
    obtain ⟨port, rfl⟩ := List.mem_ofFn.mp present
    exact models port equation inside

theorem latent_models (candidate : Assignment (family queries locals captures) next)
    {Γ : Ctx S} {sort : S.Srt} (picked : Selection O) (rows : O → Row locals captures Γ sort) :
    ContextualResidual.Models candidate (ContextualConditionalSourceProblem.latent queries locals captures picked rows) ↔
      (∀ port : Fin picked.taken.length,
        ContextualResidual.Models (valuation locals captures
          (rowBodies queries locals captures candidate (port.val + 2)) (caller queries locals captures candidate))
          (rows (picked.taken.get port)).obligations) ∧
      (∀ port : Fin picked.read.length,
        ContextualResidual.Models (valuation locals captures
          (rowBodies queries locals captures candidate (picked.taken.length + port.val + 2))
          (caller queries locals captures candidate)) (rows (picked.read.get port)).obligations) := by
  rw [ContextualConditionalSourceProblem.latent, ContextualResidual.models_append,
    models_flatten_ofFn, models_flatten_ofFn]
  apply and_congr <;> apply forall_congr' <;> intro port <;>
    erw [ContextualResidual.models_mapProblem, ContextualConditionalRows.Row.obligationsAt,
      ContextualResidual.models_mapProblem, ← Assignment.compose_associative, row_square]

private theorem models_use_iff {V : Type} {declaration : V → MetaArity S}
    (candidate : Assignment declaration next) {Γ : Ctx S} {sort : S.Srt}
    (patterns values : List (Term (signature S declaration) Γ sort)) (size : patterns.length = values.length) :
    ContextualFrameUnifier.Models candidate (ContextualActivatedStep.useEquations patterns values) ↔
      List.Forall₂ (fun pattern value => instantiate candidate pattern = instantiate candidate value) patterns values := by
  induction patterns generalizing values with
  | nil =>
      have empty : values = [] := List.length_eq_zero_iff.mp size.symm
      subst values
      simp [ContextualActivatedStep.useEquations, Selection.equations, ContextualFrameUnifier.Models]
  | cons pattern rest ih =>
      cases values with
      | nil => cases size
      | cons value tail =>
          simpa only [ContextualActivatedStep.useEquations, Selection.equations, List.zipWith_cons_cons,
            ContextualFrameUnifier.Models, List.forall_mem_cons, List.forall₂_cons, id] using
            and_congr_right (fun _ => ih tail (Nat.succ.inj size))

theorem binding_models (candidate : Assignment (family queries locals captures) next)
    {Γ : Ctx S} {sort : S.Srt} (picked : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → Row locals captures Γ sort)
    (takeShape : code.take.length = picked.taken.length) (readShape : code.read.length = picked.read.length) :
    ContextualFrameUnifier.Models candidate
      (ContextualConditionalSourceProblem.bindingEquations queries locals captures picked code rows) ↔
      (List.Forall₂ (fun pattern value => instantiate candidate pattern = instantiate candidate value)
        (code.take.map (queryView queries locals captures))
        (ContextualClauseProblem.takeViews queries locals captures picked (fun occurrence => (rows occurrence).value)) ∧
      List.Forall₂ (fun pattern value => instantiate candidate pattern = instantiate candidate value)
        (code.read.map (queryView queries locals captures))
        (ContextualClauseProblem.readViews queries locals captures picked (fun occurrence => (rows occurrence).value))) ∧
      ContextualFrameUnifier.Models (valuation queries captures (queryBodies queries locals captures candidate)
        (caller queries locals captures candidate)) code.tell := by
  have takeLength : (code.take.map (queryView queries locals captures)).length =
      (ContextualClauseProblem.takeViews queries locals captures picked (fun occurrence => (rows occurrence).value)).length := by
    simpa only [List.length_map, ContextualClauseProblem.takeViews, List.length_ofFn] using takeShape
  have readLength : (code.read.map (queryView queries locals captures)).length =
      (ContextualClauseProblem.readViews queries locals captures picked (fun occurrence => (rows occurrence).value)).length := by
    simpa only [List.length_map, ContextualClauseProblem.readViews, List.length_ofFn] using readShape
  change ContextualFrameUnifier.Models candidate
    ((ContextualActivatedStep.useEquations _ _ ++ ContextualActivatedStep.useEquations _ _) ++
      ContextualFrameUnifier.mapProblem (queryEmbedding queries locals captures) code.tell) ↔ _
  rw [ContextualFrameUnifier.models_append, ContextualFrameUnifier.models_append,
    models_use_iff candidate _ _ takeLength, models_use_iff candidate _ _ readLength,
    ContextualFrameUnifier.models_mapProblem, query_square]

structure Witness {Γ : Ctx S} {sort : S.Srt} (picked : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → Row locals captures Γ sort) (before : ContextualResidual.Problem captures)
    (takeShape : code.take.length = picked.taken.length) (readShape : code.read.length = picked.read.length)
    (next : Next → MetaArity S) where
  query : Assignment queries next
  capture : Assignment captures next
  filler : Assignment locals next
  previous : ContextualResidual.Models capture before
  tells : ContextualFrameUnifier.Models (valuation queries captures query capture) code.tell
  taken : ∀ port : Fin picked.taken.length, Realizes locals captures capture
    (instantiate (valuation queries captures query capture)
      (code.take.get ⟨port.val, takeShape.symm ▸ port.isLt⟩)) (rows (picked.taken.get port))
  read : ∀ port : Fin picked.read.length, Realizes locals captures capture
    (instantiate (valuation queries captures query capture)
      (code.read.get ⟨port.val, readShape.symm ▸ port.isLt⟩)) (rows (picked.read.get port))

def witness_of_model {Γ : Ctx S} {sort : S.Srt} (picked : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → Row locals captures Γ sort) (before : ContextualResidual.Problem captures)
    (takeShape : code.take.length = picked.taken.length) (readShape : code.read.length = picked.read.length)
    (candidate : Assignment (family queries locals captures) next)
    (model : ContextualResidual.Models candidate
      (ContextualConditionalSourceProblem.problem queries locals captures picked code rows before)) :
    Witness queries locals captures picked code rows before takeShape readShape next := by
  have split := (ContextualResidual.models_append candidate _ _).mp model
  have base := (ContextualResidual.models_append candidate _ _).mp split.1
  have previous := (ContextualResidual.models_mapProblem _ _ _).mp base.1
  rw [captures_square] at previous
  have paired := (ContextualResidual.models_observeProblem candidate _).mp base.2
  have binding := (binding_models queries locals captures candidate picked code rows takeShape readShape).mp paired
  have takes := binding.1.1
  have reads := binding.1.2
  have tells := binding.2
  have conditions := (latent_models queries locals captures candidate picked rows).mp split.2
  have takeConditions := conditions.1
  have readConditions := conditions.2
  refine ⟨queryBodies queries locals captures candidate, caller queries locals captures candidate,
    rowBodies queries locals captures candidate 0, previous, tells, ?_, ?_⟩
  · intro port
    refine ⟨rowBodies queries locals captures candidate (port.val + 2), takeConditions port, ?_⟩
    have patternBound : port.val < (code.take.map (queryView queries locals captures)).length := by
      simpa only [List.length_map, takeShape] using port.isLt
    have valueBound : port.val < (ContextualClauseProblem.takeViews queries locals captures picked
        (fun occurrence => (rows occurrence).value)).length := by simpa only [ContextualClauseProblem.takeViews, List.length_ofFn] using port.isLt
    have equal := takes.get patternBound valueBound
    simp only [List.get_eq_getElem, List.getElem_map] at equal
    dsimp only [ContextualClauseProblem.takeViews] at equal
    erw [List.getElem_ofFn] at equal
    change instantiate candidate (queryView queries locals captures
      (code.take.get ⟨port.val, takeShape.symm ▸ port.isLt⟩)) =
      instantiate candidate (instantiate (rowEmbedding queries locals captures)
        ((rows (picked.taken.get port)).viewAt locals captures (port.val + 2))) at equal
    erw [← Assignment.instantiate_compose, query_square, row_value] at equal
    exact equal.symm
  · intro port
    refine ⟨rowBodies queries locals captures candidate (picked.taken.length + port.val + 2), readConditions port, ?_⟩
    have patternBound : port.val < (code.read.map (queryView queries locals captures)).length := by
      simpa only [List.length_map, readShape] using port.isLt
    have valueBound : port.val < (ContextualClauseProblem.readViews queries locals captures picked
        (fun occurrence => (rows occurrence).value)).length := by simpa only [ContextualClauseProblem.readViews, List.length_ofFn] using port.isLt
    have equal := reads.get patternBound valueBound
    simp only [List.get_eq_getElem, List.getElem_map] at equal
    dsimp only [ContextualClauseProblem.readViews] at equal
    erw [List.getElem_ofFn] at equal
    change instantiate candidate (queryView queries locals captures
      (code.read.get ⟨port.val, readShape.symm ▸ port.isLt⟩)) =
      instantiate candidate (instantiate (rowEmbedding queries locals captures)
        ((rows (picked.read.get port)).viewAt locals captures (picked.taken.length + port.val + 2))) at equal
    erw [← Assignment.instantiate_compose, query_square, row_value] at equal
    exact equal.symm

def portBodies (takeCount readCount : Nat)
    (takes : Fin takeCount → Assignment locals next) (reads : Fin readCount → Assignment locals next)
    (filler : Assignment locals next) : Assignment (rowLocals locals) next :=
  fun name =>
    if taken : 2 ≤ name.scope ∧ name.scope - 2 < takeCount then takes ⟨name.scope - 2, taken.2⟩ name.name
    else if read : takeCount + 2 ≤ name.scope ∧ name.scope - (takeCount + 2) < readCount then
      reads ⟨name.scope - (takeCount + 2), read.2⟩ name.name
    else filler name.name

theorem portBodies_take (takeCount readCount : Nat)
    (takes : Fin takeCount → Assignment locals next) (reads : Fin readCount → Assignment locals next)
    (filler : Assignment locals next) (port : Fin takeCount) :
    (fun name => portBodies locals takeCount readCount takes reads filler ⟨port.val + 2, name⟩) = takes port := by
  funext name
  have taken : 2 ≤ port.val + 2 ∧ port.val + 2 - 2 < takeCount := by omega
  dsimp only [portBodies]
  rw [dif_pos taken]
  exact congrArg (fun selected : Fin takeCount => takes selected name)
    (Fin.ext (by change port.val + 2 - 2 = port.val; omega))

theorem portBodies_read (takeCount readCount : Nat)
    (takes : Fin takeCount → Assignment locals next) (reads : Fin readCount → Assignment locals next)
    (filler : Assignment locals next) (port : Fin readCount) :
    (fun name => portBodies locals takeCount readCount takes reads filler ⟨takeCount + port.val + 2, name⟩) = reads port := by
  funext name
  have notTaken : ¬ (2 ≤ takeCount + port.val + 2 ∧ takeCount + port.val + 2 - 2 < takeCount) := by omega
  have read : takeCount + 2 ≤ takeCount + port.val + 2 ∧
      takeCount + port.val + 2 - (takeCount + 2) < readCount := by omega
  dsimp only [portBodies]
  rw [dif_neg notTaken, dif_pos read]
  exact congrArg (fun selected : Fin readCount => reads selected name)
    (Fin.ext (by change takeCount + port.val + 2 - (takeCount + 2) = port.val; omega))

theorem Witness.gives_model {Γ : Ctx S} {sort : S.Srt} {picked : Selection O}
    {code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort)}
    {rows : O → Row locals captures Γ sort} {before : ContextualResidual.Problem captures}
    {takeShape : code.take.length = picked.taken.length} {readShape : code.read.length = picked.read.length}
    (witness : Witness queries locals captures picked code rows before takeShape readShape next) :
    ∃ candidate : Assignment (family queries locals captures) next,
      ContextualResidual.Models candidate
        (ContextualConditionalSourceProblem.problem queries locals captures picked code rows before) ∧
      queryBodies queries locals captures candidate = witness.query ∧ caller queries locals captures candidate = witness.capture := by
  classical
  let takes := fun port => Classical.choose (witness.taken port)
  let reads := fun port => Classical.choose (witness.read port)
  let slots := portBodies locals picked.taken.length picked.read.length takes reads witness.filler
  let candidate : Assignment (family queries locals captures) next
    | .inl name => witness.query name
    | .inr (.inl name) => slots name
    | .inr (.inr name) => witness.capture name
  have queryFixed : queryBodies queries locals captures candidate = witness.query := rfl
  have callerFixed : caller queries locals captures candidate = witness.capture := rfl
  have takeFixed : ∀ port : Fin picked.taken.length,
      rowBodies queries locals captures candidate (port.val + 2) = takes port := by
    intro port
    exact portBodies_take locals _ _ takes reads witness.filler port
  have readFixed : ∀ port : Fin picked.read.length,
      rowBodies queries locals captures candidate (picked.taken.length + port.val + 2) = reads port := by
    intro port
    exact portBodies_read locals _ _ takes reads witness.filler port
  refine ⟨candidate, ?_, queryFixed, callerFixed⟩
  apply (ContextualResidual.models_append candidate _ _).mpr
  constructor
  · apply (ContextualResidual.models_append candidate _ _).mpr
    constructor
    · apply (ContextualResidual.models_mapProblem _ _ _).mpr
      rw [captures_square, callerFixed]
      exact witness.previous
    · apply (ContextualResidual.models_observeProblem candidate _).mpr
      apply (binding_models queries locals captures candidate picked code rows takeShape readShape).mpr
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · apply List.forall₂_of_length_eq_of_get
          (by simp only [List.length_map, ContextualClauseProblem.takeViews, List.length_ofFn]; exact takeShape)
        intro index patternBound valueBound
        let port : Fin picked.taken.length := ⟨index, by
          simpa only [List.length_map, takeShape] using patternBound⟩
        have same := (Classical.choose_spec (witness.taken port)).2
        simp only [List.get_eq_getElem, List.getElem_map]
        dsimp only [ContextualClauseProblem.takeViews]
        erw [List.getElem_ofFn]
        change instantiate candidate (queryView queries locals captures
          (code.take.get ⟨port.val, takeShape.symm ▸ port.isLt⟩)) =
          instantiate candidate (instantiate (rowEmbedding queries locals captures)
            ((rows (picked.taken.get port)).viewAt locals captures (port.val + 2)))
        erw [← Assignment.instantiate_compose, query_square, row_value,
          queryFixed, callerFixed, takeFixed]
        exact same.symm
      · apply List.forall₂_of_length_eq_of_get
          (by simp only [List.length_map, ContextualClauseProblem.readViews, List.length_ofFn]; exact readShape)
        intro index patternBound valueBound
        let port : Fin picked.read.length := ⟨index, by
          simpa only [List.length_map, readShape] using patternBound⟩
        have same := (Classical.choose_spec (witness.read port)).2
        simp only [List.get_eq_getElem, List.getElem_map]
        dsimp only [ContextualClauseProblem.readViews]
        erw [List.getElem_ofFn]
        change instantiate candidate (queryView queries locals captures
          (code.read.get ⟨port.val, readShape.symm ▸ port.isLt⟩)) =
          instantiate candidate (instantiate (rowEmbedding queries locals captures)
            ((rows (picked.read.get port)).viewAt locals captures (picked.taken.length + port.val + 2)))
        erw [← Assignment.instantiate_compose, query_square, row_value,
          queryFixed, callerFixed, readFixed]
        exact same.symm
      · rw [queryFixed, callerFixed]
        exact witness.tells
  · apply (latent_models queries locals captures candidate picked rows).mpr
    constructor
    · intro port
      rw [callerFixed, takeFixed]
      exact (Classical.choose_spec (witness.taken port)).1
    · intro port
      rw [callerFixed, readFixed]
      exact (Classical.choose_spec (witness.read port)).1

theorem solvable_iff {Γ : Ctx S} {sort : S.Srt} (picked : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → Row locals captures Γ sort) (before : ContextualResidual.Problem captures)
    (takeShape : code.take.length = picked.taken.length) (readShape : code.read.length = picked.read.length) :
    ContextualConditionalExecution.Solvable
      (ContextualConditionalSourceProblem.problem queries locals captures picked code rows before) ↔
      ∃ (Future : Type) (future : Future → MetaArity S),
        Nonempty (Witness queries locals captures picked code rows before takeShape readShape future) := by
  constructor
  · rintro ⟨Future, future, candidate, model⟩
    exact ⟨Future, future, ⟨witness_of_model queries locals captures picked code rows before
      takeShape readShape candidate model⟩⟩
  · rintro ⟨Future, future, ⟨witness⟩⟩
    obtain ⟨candidate, model, _, _⟩ := witness.gives_model queries locals captures
    exact ⟨Future, future, candidate, model⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseWitnesses
