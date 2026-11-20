import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Core

/-!
# Interpreted term frames with explicit inhabited environments

An interpreted term is a function of its environment. Substitution is
precomposition; a canonical rule opening adds an independent environment.
Every environment is inhabited, so an empty future environment cannot make
inconsistent equations vacuously solvable.

This is a semantic frame instance. It supplies no decision procedure for
function equality, no executable guard evaluator, and no finite presentation
of the interpreted values.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.InterpretedFrames

universe u v w

structure Frame where
  Carrier : Type u
  nonempty : Nonempty Carrier

abbrev Terms (Value : Type v) (frame : Frame.{u}) := frame.Carrier → Value

abbrev Hom (source target : Frame.{u}) := target.Carrier → source.Carrier

def ground : Frame.{u} := ⟨PUnit, ⟨PUnit.unit⟩⟩

def extend (old locals : Frame.{u}) : Frame.{u} :=
  ⟨old.Carrier × locals.Carrier, by
    obtain ⟨first⟩ := old.nonempty
    obtain ⟨second⟩ := locals.nonempty
    exact ⟨(first, second)⟩⟩

def frames (Value : Type v) : Frames (Terms Value) Hom where
  E := Eq
  equivalence _ := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
  act substitution term := term ∘ substitution
  id _ := id
  comp later earlier := earlier ∘ later
  act_id _ := rfl
  act_comp _ _ _ := rfl
  preserves := by
    intro before after substitution first second same
    exact congrArg (fun term => term ∘ substitution) same

def extensions : RuleSyntax.Extensions Hom where
  Ext _ := Frame.{u}
  target {old} locals := extend old locals
  weaken _ := Prod.fst

def canonical {Value : Type v} {Occurrence : Type w}
    {program : RuleSyntax.Program (Terms Value)} {old : Frame.{u}}
    (rule : RuleSyntax.Rule (Terms Value)) (member : rule ∈ program)
    (selection : Selection Occurrence) :
    RuleSyntax.Firing Occurrence extensions program old :=
  ⟨rule, member, rule.locals, Prod.snd, selection, []⟩

theorem canonical_fresh {Value : Type v} {Occurrence : Type w}
    {program : RuleSyntax.Program (Terms Value)}
    (state : RuleSyntax.State (Terms Value) Occurrence)
    (rule : RuleSyntax.Rule (Terms Value)) (member : rule ∈ program)
    (selection : Selection Occurrence) :
    (canonical (old := state.frame) rule member selection).Fresh (frames Value) state := by
  intro later old locals
  exact ⟨fun environment => (old environment, locals environment),
    fun _ _ => rfl, fun _ _ => rfl⟩

def Satisfies {Value : Type v} {frame : Frame.{u}}
    (equations : EquationStore (Terms Value frame)) (environment : frame.Carrier) : Prop :=
  ∀ equation ∈ equations, equation.1 environment = equation.2 environment

theorem models_iff {Value : Type v} {before after : Frame.{u}}
    (substitution : Hom before after) (equations : EquationStore (Terms Value before)) :
    (frames Value).Models substitution equations ↔
      ∀ environment, Satisfies equations (substitution environment) := by
  constructor
  · intro models environment equation member
    exact congrFun (models equation member) environment
  · intro satisfies equation member
    funext environment
    exact satisfies environment equation member

theorem solvable_iff {Value : Type v} {frame : Frame.{u}}
    (equations : EquationStore (Terms Value frame)) :
    (frames Value).Solvable equations ↔ ∃ environment, Satisfies equations environment := by
  constructor
  · rintro ⟨later, substitution, models⟩
    obtain ⟨environment⟩ := later.nonempty
    exact ⟨substitution environment, (models_iff substitution equations).mp models environment⟩
  · rintro ⟨environment, satisfies⟩
    exact ⟨ground, fun _ => environment,
      (models_iff (fun _ : ground.Carrier => environment) equations).mpr (fun _ => satisfies)⟩

theorem entails_iff {Value : Type v} {frame : Frame.{u}}
    (equations : EquationStore (Terms Value frame)) (predicate : frame.Carrier → Prop) :
    (frames Value).Entails equations (fun later substitution =>
      ∀ environment : later.Carrier, predicate (substitution environment)) ↔
      ∀ environment, Satisfies equations environment → predicate environment := by
  constructor
  · intro entails environment satisfies
    exact entails ground (fun _ => environment)
      ((models_iff (fun _ : ground.Carrier => environment) equations).mpr (fun _ => satisfies))
      PUnit.unit
  · intro entails later substitution models environment
    exact entails (substitution environment) ((models_iff substitution equations).mp models environment)

theorem certificate_determines_locals {Value : Type v} {old locals later : Frame.{u}}
    (certificate : locals.Carrier → Value) (injective : Function.Injective certificate)
    (chosen : locals.Carrier) (substitution : Hom (extend old locals) later)
    (same : (frames Value).Solves substitution
      (fun environment => certificate environment.2, fun _ => certificate chosen)) :
    ∀ environment, (substitution environment).2 = chosen := by
  intro environment
  exact injective (congrFun same environment)

theorem inconsistent_closed_values {Value : Type v} (left right : Value) (different : left ≠ right) :
    ¬ (frames Value).Solvable ([(fun _ : ground.Carrier => left, fun _ => right)] :
      EquationStore (Terms Value ground)) := by
  rw [solvable_iff]
  rintro ⟨environment, satisfies⟩
  exact different (satisfies _ (List.mem_singleton_self _))

theorem constant_environment_solvable {Value : Type v} {frame : Frame.{u}}
    (environment : frame.Carrier) (terms : List (Terms Value frame)) :
    (frames Value).Solvable (terms.map fun term => (term, fun _ => term environment)) := by
  apply (solvable_iff _).mpr
  refine ⟨environment, ?_⟩
  intro equation member
  obtain ⟨term, _, rfl⟩ := List.mem_map.mp member
  rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.InterpretedFrames
