import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalRows
import Mettapedia.OSLF.Syntax.ContextualFiniteSupport
import Mettapedia.OSLF.Syntax.ContextualReindexSupport
import Mettapedia.OSLF.Syntax.ContextualSupportSubstitution

/-!
# Dense frames for contextual stored rows

A row's value and latent equations are compiled into one finite declaration
frame. An open view borrows the code and supplies a scope. A private slot
has identity (scope, slot), while a capture names its existing declaration.
The same opening assignment is used for the value and all equations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStoredRowCompilation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)

variable {S : Signature} {Local Shared : Type}
  (locals : Local → MetaArity S) (captures : Shared → MetaArity S)

private abbrev source := ContextualSelectionViews.source locals captures
private abbrev target := ContextualSelectionViews.target locals captures

/-! ## Private renaming at a fixed use -/

theorem opened_private_rename {Other : Type} (other : Other → MetaArity S)
    (rename : Local ≃ Other) (arity : ∀ name, other (rename name) = locals name)
    {Γ : Ctx S} {sort : S.Srt} (body : Term (signature S (source locals captures)) Γ sort) (scope : Nat) :
    let originalNames : Assignment (source locals captures) (source other captures) :=
      reindex (Sum.map rename id) (fun | .inl name => arity name | .inr _ => rfl)
    let useNames : Assignment (target locals captures) (target other captures) :=
      reindex (Sum.map (fun name => ScopedVar.at name.scope (rename name.name)) id)
        (fun | .inl name => arity name.name | .inr _ => rfl)
    instantiate useNames (ContextualFreshening.termAt locals captures scope body) =
      ContextualFreshening.termAt other captures scope (instantiate originalNames body) := by
  dsimp only
  unfold ContextualFreshening.termAt
  rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose]
  congr 1
  funext name
  cases name with
  | inl name =>
      change instantiate _ (generator (target locals captures) (.inl (ScopedVar.at scope name))) =
        instantiate (ContextualFreshening.assignment other captures scope)
          (castMetaBody (V := signature S (source other captures)) (arity name)
            (generator (source other captures) (.inl (rename name))))
      rw [instantiate_generator]
      let action := ContextualFreshening.assignment other captures scope
      let image := generator (source other captures) (.inl (rename name))
      have decoded := instantiate_generator action (.inl (rename name))
      exact (congrArg (castMetaBody (V := signature S (target other captures)) (arity name))
        decoded.symm).trans (instantiate_castMetaBody action (arity name) image).symm
  | inr name =>
      change instantiate _ (generator (target locals captures) (.inr name)) =
        instantiate _ (generator (source other captures) (.inr name))
      rw [instantiate_generator, instantiate_generator]
      rfl

abbrev declaration (names : List (Local ⊕ Shared)) :=
  FiniteSupport.declaration (source := source locals captures) names

structure Code (Γ : Ctx S) (sort : S.Srt) where
  names : List (Local ⊕ Shared)
  value : Term (signature S (declaration locals captures names)) Γ sort
  equations : ContextualResidual.Problem (declaration locals captures names)

private def equationSupport {V : Type} {family : V → MetaArity S} :
    ContextualResidual.Problem family → List V
  | [] => []
  | (left, right) :: rest =>
      (support left.2.2 ++ support right.2.2) ++ equationSupport rest

section Compile

variable [DecidableEq Local] [DecidableEq Shared]

private def compileEquations (names : List (Local ⊕ Shared)) :
    (problem : ContextualResidual.Problem (source locals captures)) →
    (∀ name ∈ equationSupport problem, name ∈ names) →
    ContextualResidual.Problem (declaration locals captures names)
  | [], _ => []
  | (left, right) :: rest, covered =>
      (observe (FiniteSupport.compile names left.2.2 (fun name used => covered name
        (List.mem_append_left _ (List.mem_append_left _ used)))),
      observe (FiniteSupport.compile names right.2.2 (fun name used => covered name
        (List.mem_append_left _ (List.mem_append_right _ used))))) ::
      compileEquations names rest (fun name used => covered name (List.mem_append_right _ used))

def compile {Γ : Ctx S} {sort : S.Srt} (row : ContextualConditionalRows.Row locals captures Γ sort) :
    Code locals captures Γ sort :=
  let value := ContextualStoredRows.asTemplate locals captures row.value
  let names := FiniteSupport.firstNames (support value ++ equationSupport row.obligations)
  ⟨names, FiniteSupport.compile names value (fun _ used =>
      FiniteSupport.mem_firstNames.mpr (List.mem_append_left _ used)),
    compileEquations locals captures names row.obligations (fun _ used =>
      FiniteSupport.mem_firstNames.mpr (List.mem_append_right _ used))⟩

variable {V : Type} {family : V → MetaArity S}

private theorem map_compileEquations (names : List (Local ⊕ Shared))
    (assignment : Assignment (source locals captures) family) :
    ∀ (problem : ContextualResidual.Problem (source locals captures))
      (covered : ∀ name ∈ equationSupport problem, name ∈ names),
    ContextualResidual.mapProblem (FiniteSupport.slots names assignment)
        (compileEquations locals captures names problem covered) =
      ContextualResidual.mapProblem assignment problem
  | [], _ => rfl
  | (⟨leftContext, leftSort, left⟩, ⟨rightContext, rightSort, right⟩) :: rest, covered => by
      unfold compileEquations
      simp only [ContextualResidual.mapProblem, List.map_cons,
        FiniteSupport.instantiate_compile, observe, instantiateObservation]
      exact congrArg (List.cons _) (map_compileEquations names assignment rest
        (fun name used => covered name (List.mem_append_right _ used)))

theorem compile_instantiates {Γ : Ctx S} {sort : S.Srt}
    (row : ContextualConditionalRows.Row locals captures Γ sort)
    (assignment : Assignment (source locals captures) family) :
    let code := compile locals captures row
    let frame := FiniteSupport.slots code.names assignment
    instantiate frame code.value = instantiate assignment
        (ContextualStoredRows.asTemplate locals captures row.value) ∧
      ContextualResidual.mapProblem frame code.equations =
        ContextualResidual.mapProblem assignment row.obligations := by
  exact ⟨FiniteSupport.instantiate_compile _ assignment _ _,
    map_compileEquations locals captures _ assignment _ _⟩

theorem compile_models {Γ : Ctx S} {sort : S.Srt}
    (row : ContextualConditionalRows.Row locals captures Γ sort)
    (assignment : Assignment (source locals captures) family) :
    let code := compile locals captures row
    ContextualResidual.Models (FiniteSupport.slots code.names assignment) code.equations ↔
      ContextualResidual.Models assignment row.obligations := by
  let code := compile locals captures row
  let frame := FiniteSupport.slots code.names assignment
  have opened := (compile_instantiates locals captures row assignment).2
  have before := ContextualResidual.models_mapProblem assignment (generator family) row.obligations
  have after := ContextualResidual.models_mapProblem frame (generator family) code.equations
  rw [Assignment.compose_identity_left] at before after
  change ContextualResidual.Models frame code.equations ↔ _
  rw [← after, opened, before]

end Compile

variable {locals captures} {Γ : Ctx S} {sort : S.Srt}

abbrev Code.Opened (code : Code locals captures Γ sort) :=
  ContextualFreshening.scopedDeclarations (declaration locals captures code.names) captures

private def slotImage (code : Code locals captures Γ sort) (scope : Nat)
    (slot : Fin code.names.length) :
    (origin : Local ⊕ Shared) → code.names[slot] = origin →
      Term (signature S code.Opened) ((source locals captures) origin).1 ((source locals captures) origin).2
  | .inl _, located => castMetaBody (V := signature S code.Opened)
      (congrArg (source locals captures) located) (generator code.Opened (.inl (ScopedVar.at scope slot)))
  | .inr name, _ => generator code.Opened (.inr name)

/-- A private slot uses the supplied scope and its dense position. A
captured slot uses the captured name from the immutable code layout. -/
def Code.frame (code : Code locals captures Γ sort) (scope : Nat) :
    Assignment (declaration locals captures code.names) code.Opened :=
  fun slot => slotImage code scope slot code.names[slot] rfl

/-- A layout with only captures can dispense with a fresh scope. -/
theorem Code.frame_eq_of_captures_only (code : Code locals captures Γ sort) (first second : Nat)
    (captured : ∀ slot : Fin code.names.length, ∃ name, code.names[slot] = .inr name) :
    code.frame first = code.frame second := by
  funext slot
  have independent (origin : Local ⊕ Shared) (located : code.names[slot] = origin)
      (shared : ∃ name, origin = .inr name) :
      slotImage code first slot origin located = slotImage code second slot origin located := by
    obtain ⟨name, rfl⟩ := shared
    rfl
  exact independent _ rfl (captured slot)

private def openedIdentity {width : Nat} (scope : Nat) (slot : Fin width) :
    Local ⊕ Shared → ScopedVar (Fin width) ⊕ Shared
  | .inl _ => .inl (ScopedVar.at scope slot)
  | .inr name => .inr name

def Code.identityAt (code : Code locals captures Γ sort) (scope : Nat)
    (slot : Fin code.names.length) : ScopedVar (Fin code.names.length) ⊕ Shared :=
  openedIdentity scope slot code.names[slot]

private theorem slotImage_support (code : Code locals captures Γ sort) (scope : Nat)
    (slot : Fin code.names.length) (origin : Local ⊕ Shared) (located : code.names[slot] = origin) :
    support (slotImage code scope slot origin located) = [openedIdentity scope slot origin] := by
  cases origin with
  | inl name =>
      exact (support_castMetaBody (congrArg (source locals captures) located)
        (generator code.Opened (.inl (ScopedVar.at scope slot)))).trans (support_generator _)
  | inr name => exact support_generator (source := code.Opened) (.inr name)

theorem Code.slot_support (code : Code locals captures Γ sort) (scope : Nat)
    (slot : Fin code.names.length) :
    support (code.frame scope slot) = [code.identityAt scope slot] :=
  slotImage_support code scope slot _ rfl

/-- This law also applies to the operands of every latent equation. -/
theorem Code.opened_local_scope (code : Code locals captures Γ sort) (scope : Nat)
    {Δ : Ctx S} {result : S.Srt}
    (body : Term (signature S (declaration locals captures code.names)) Δ result)
    (localName : ScopedVar (Fin code.names.length))
    (present : Sum.inl localName ∈ support (instantiate (code.frame scope) body)) :
    localName.scope = scope := by
  let allowed : ScopedVar (Fin code.names.length) ⊕ Shared → Prop
    | .inl active => active.scope = scope
    | .inr _ => True
  apply bounded_instantiate allowed (code.frame scope) body _ (.inl localName) present
  intro slot _ identity member
  rw [code.slot_support] at member
  obtain rfl := List.mem_singleton.mp member
  unfold Code.identityAt
  cases code.names[slot] <;> simp [openedIdentity, allowed, ScopedVar.at]

def Code.readback (code : Code locals captures Γ sort) : Assignment code.Opened (target locals captures)
  | .inl localName => ContextualFreshening.assignment locals captures localName.scope code.names[localName.name]
  | .inr name => generator (target locals captures) (.inr name)

private theorem slotImage_readback (code : Code locals captures Γ sort) (scope : Nat)
    (slot : Fin code.names.length) (origin : Local ⊕ Shared) (located : code.names[slot] = origin) :
    instantiate code.readback (slotImage code scope slot origin located) =
      ContextualFreshening.assignment locals captures scope origin := by
  cases origin with
  | inl name =>
      unfold slotImage
      refine (instantiate_castMetaBody code.readback (congrArg (source locals captures) located)
        (generator code.Opened (.inl (ScopedVar.at scope slot)))).trans ?_
      have transport {first second : Local ⊕ Shared} (same : first = second) :
          castMetaBody (V := signature S (target locals captures))
            (congrArg (source locals captures) same) (ContextualFreshening.assignment locals captures scope first) =
          ContextualFreshening.assignment locals captures scope second := by
        cases same
        rfl
      exact (congrArg (castMetaBody (V := signature S (target locals captures))
        (congrArg (source locals captures) located))
        (instantiate_generator code.readback (.inl (ScopedVar.at scope slot)))).trans
        (transport located)
  | inr name => exact instantiate_generator code.readback (.inr name)

theorem Code.frame_readback (code : Code locals captures Γ sort) (scope : Nat) :
    Assignment.compose code.readback (code.frame scope) =
      FiniteSupport.slots code.names (ContextualFreshening.assignment locals captures scope) := by
  funext slot
  exact slotImage_readback code scope slot _ rfl

theorem compile_openAt [DecidableEq Local] [DecidableEq Shared]
    (row : ContextualConditionalRows.Row locals captures Γ sort) (scope : Nat) :
    let code := compile locals captures row
    let frame := code.frame scope
    instantiate code.readback (instantiate frame code.value) =
        row.viewAt locals captures scope ∧
      ContextualResidual.mapProblem code.readback
          (ContextualResidual.mapProblem frame code.equations) =
        row.obligationsAt locals captures scope := by
  dsimp only
  generalize eq : compile locals captures row = code
  have compileLaw := compile_instantiates locals captures row
    (ContextualFreshening.assignment locals captures scope)
  dsimp only at compileLaw
  rw [eq] at compileLaw
  constructor
  · rw [← Assignment.instantiate_compose, code.frame_readback, compileLaw.1]
    exact (ContextualStoredRows.viewAt_eq_freshening locals captures scope row.value).symm
  · simp only [ContextualResidual.mapProblem, List.map_map, Function.comp_def, instantiateObservation_comp]
    rw [code.frame_readback]
    exact compileLaw.2

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStoredRowCompilation
