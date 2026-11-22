import Mettapedia.OSLF.Syntax.DeterministicGSOSEdgeReadout
import Mettapedia.OSLF.Syntax.DeterministicGSOSFinitePresentation
import Mettapedia.GSLT.Topos.PresheafEventAbsence

/-!
# Native positive and negative availability guards of deterministic GSOS

The label predicate is an actual subfunctor of the operational event
presheaf. Its source image is existential availability, and native negative
availability is its Heyting negation. The earned operational naturality
equation reflects availability, so in this qualified model native negation
agrees with the complete Boolean guard. Event existence explicitly requires
an inhabited occurrence carrier.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS.NativeGuard

open _root_.CategoryTheory Mettapedia.TypeTheory
open EdgeReadout PresheafEventCertificates
open Mettapedia.GSLT.Topos

universe u
variable {S : Signature.{u}} {Actions : S.Srt → Type u}
variable {C : Type u} [Category.{u} C]
variable (law : Law S Actions) (worlds : Cᵒᵖ ⥤ S.Families)
variable (steps : worlds ⟶ worlds ⋙ behaviourFunctor S Actions)
variable {Origins : Type u}

/-- A declared action predicate on complete events, with the original
occurrence identifier and endpoint left in its native fibre. -/
def labelPredicate (Origins : Type u) (sort : S.Srt) (action : Actions sort) :
    Subfunctor (events law worlds steps Origins sort) where
  obj _ := {event | event.action = action}
  map _ := by intro event member; exact member

/-- Positive action availability is the actual source image of its label. -/
noncomputable def enabled (Origins : Type u) (sort : S.Srt) (action : Actions sort) :
    Subfunctor (terms worlds sort) :=
  PresheafEventAbsence.enabled (eventSpan law worlds steps Origins sort).source
    (labelPredicate law worlds steps Origins sort action)

/-- Negative action availability uses the native Heyting implication. -/
noncomputable def noAction (Origins : Type u) (sort : S.Srt) (action : Actions sort) :
    Subfunctor (terms worlds sort) :=
  PresheafEventAbsence.absent (eventSpan law worlds steps Origins sort).source
    (labelPredicate law worlds steps Origins sort action)

theorem mem_enabled (Origins : Type u) (sort : S.Srt) (action : Actions sort)
    (world : Cᵒᵖ) (program : S.Term (worlds.obj world) sort) :
    program ∈ (enabled law worlds steps Origins sort action).obj world ↔
      ∃ event : Event law worlds steps Origins sort world,
        event.action = action ∧ event.source = program := Iff.rfl

/-- An actual operational transition supplies an event when an occurrence
identifier is available. No inhabitant is silently manufactured. -/
theorem enabled_iff_step [Nonempty Origins] (sort : S.Srt) (action : Actions sort)
    (world : Cᵒᵖ) (program : S.Term (worlds.obj world) sort) :
    program ∈ (enabled law worlds steps Origins sort action).obj world ↔
      ∃ target, Operational.coalgebra law (steps.app world) PUnit.unit sort program action = some target := by
  rw [mem_enabled]
  constructor
  · rintro ⟨event, label, source⟩
    exact ⟨event.target, by simpa only [← label, ← source] using event.valid⟩
  · rintro ⟨target, valid⟩
    obtain ⟨origin⟩ := ‹Nonempty Origins›
    exact ⟨⟨origin, program, action, target, valid⟩, rfl, rfl⟩

/-- Exact Option-map naturality earns source-fibre reflection. -/
theorem reflectsAvailability (Origins : Type u) (sort : S.Srt) (action : Actions sort) :
    PresheafEventAbsence.ReflectsAvailability
      (eventSpan law worlds steps Origins sort).source
      (labelPredicate law worlds steps Origins sort action) := by
  intro world future change program event label source
  change event.action = action at label
  change event.source = S.rename (worlds.map change) program at source
  have valid : Operational.coalgebra law (steps.app future) PUnit.unit sort
      (S.rename (worlds.map change) program) action = some event.target := by
    rw [← source, ← label]
    exact event.valid
  rw [step_map law worlds steps change sort program action] at valid
  cases earlier : Operational.coalgebra law (steps.app world) PUnit.unit sort program action with
  | none => simp only [earlier, Option.map_none] at valid; contradiction
  | some target =>
      exact ⟨⟨event.origin, program, action, target, earlier⟩, rfl, rfl⟩

/-- Native negative availability excludes precisely a present action in
this natural deterministic coalgebra, not in an arbitrary event span. -/
theorem noAction_iff_none [Nonempty Origins] (sort : S.Srt) (action : Actions sort)
    (world : Cᵒᵖ) (program : S.Term (worlds.obj world) sort) :
    program ∈ (noAction law worlds steps Origins sort action).obj world ↔
      Operational.coalgebra law (steps.app world) PUnit.unit sort program action = none := by
  have reflected := PresheafEventAbsence.absent_iff_present
    (eventSpan law worlds steps Origins sort).source
    (labelPredicate law worlds steps Origins sort action)
    (reflectsAvailability law worlds steps Origins sort action) world program
  change program ∈ (noAction law worlds steps Origins sort action).obj world ↔
    ¬ program ∈ (enabled law worlds steps Origins sort action).obj world at reflected
  rw [reflected, enabled_iff_step]
  cases Operational.coalgebra law (steps.app world) PUnit.unit sort program action <;> simp

/-- Independently supplied child sources form their genuine contextual
tuple presheaf, even when some children have no outgoing events. -/
noncomputable def children {sort : S.Srt} (operator : S.Operator sort) : Cᵒᵖ ⥤ Type u where
  obj world := ∀ position, S.Term (worlds.obj world) (S.argument operator position)
  map change := ↾fun given position => S.rename (worlds.map change) (given position)
  map_id world := by
    ext given position
    rw [worlds.map_id]
    exact IndexedPolynomial.Free.map_id S.polynomial (given position)
  map_comp earlier later := by
    ext given position
    rw [worlds.map_comp]
    exact (IndexedPolynomial.Free.map_comp S.polynomial
      (fun base sort => worlds.map earlier base sort)
      (fun base sort => worlds.map later base sort) (given position)).symm

def childProjection {sort : S.Srt} (operator : S.Operator sort) (position : S.Position operator) :
    children worlds operator ⟶ terms worlds (S.argument operator position) where
  app _ := ↾fun given => given position

/-- Read actual child behavior, independently of a chosen rule. -/
noncomputable def actualGuard {sort : S.Srt} {operator : S.Operator sort}
    (world : Cᵒᵖ) (given : (children worlds operator).obj world) : Guard Actions operator :=
  inputGuard Actions (fun position =>
    (given position, Operational.coalgebra law (steps.app world) PUnit.unit _ (given position)))

theorem actualGuard_map {sort : S.Srt} (operator : S.Operator sort)
    {world future : Cᵒᵖ} (change : world ⟶ future)
    (given : (children worlds operator).obj world) :
    actualGuard law worlds steps future ((children worlds operator).map change given) =
      actualGuard law worlds steps world given :=
  constructorGuard_map law worlds steps change operator given _ rfl

/-- One positive or negative native premise at its actual argument address. -/
noncomputable def premise (Origins : Type u) {sort : S.Srt} (operator : S.Operator sort)
    (address : Address Actions operator) (positive : Bool) : Subfunctor (children worlds operator) :=
  if positive then
    (enabled law worlds steps Origins _ address.2).preimage (childProjection worlds operator address.1)
  else (noAction law worlds steps Origins _ address.2).preimage (childProjection worlds operator address.1)

theorem premise_iff_guard [Nonempty Origins] {sort : S.Srt} (operator : S.Operator sort)
    (address : Address Actions operator) (positive : Bool) (world : Cᵒᵖ)
    (given : (children worlds operator).obj world) :
    given ∈ (premise law worlds steps Origins operator address positive).obj world ↔
      actualGuard law worlds steps world given address = positive := by
  cases positive with
  | false =>
      change given address.1 ∈ (noAction law worlds steps Origins _ address.2).obj world ↔ _
      rw [noAction_iff_none]
      unfold actualGuard inputGuard
      cases read : Operational.coalgebra law (steps.app world) PUnit.unit _ (given address.1) address.2 <;> simp [read]
  | true =>
      change given address.1 ∈ (enabled law worlds steps Origins _ address.2).obj world ↔ _
      rw [enabled_iff_step]
      unfold actualGuard inputGuard
      cases read : Operational.coalgebra law (steps.app world) PUnit.unit _ (given address.1) address.2 <;> simp [read]

/-- The actual finite conjunction of a rule's authored positive and negative
premises. It does not test unmentioned actions. -/
noncomputable def finiteGuard (Origins : Type u) {sort : S.Srt} {operator : S.Operator sort}
    (rule : FiniteRule Actions operator) : Subfunctor (children worlds operator) where
  obj world := {given | ∀ address : {a // a ∈ rule.observed},
    given ∈ (premise law worlds steps Origins operator address.val (rule.pattern address)).obj world}
  map change := by
    intro given holds address
    exact (premise law worlds steps Origins operator address.val (rule.pattern address)).map change (holds address)

theorem finiteGuard_iff_matches [Nonempty Origins] {sort : S.Srt} {operator : S.Operator sort}
    (rule : FiniteRule Actions operator) (world : Cᵒᵖ)
    (given : (children worlds operator).obj world) :
    given ∈ (finiteGuard law worlds steps Origins rule).obj world ↔
      rule.Matches (actualGuard law worlds steps world given) := by
  constructor
  · intro holds address present
    exact (premise_iff_guard law worlds steps operator address _ world given).mp (holds ⟨address, present⟩)
  · intro matching address
    exact (premise_iff_guard law worlds steps operator address.val _ world given).mpr
      (matching address.val address.property)

/-- The complete guarded-law predicate reads every argument/action
address, using native availability and negation at that address. Its index
may be infinite; it is separate from a finite authored premise inventory. -/
noncomputable def completeGuard (Origins : Type u) {sort : S.Srt}
    (operator : S.Operator sort) (guard : Guard Actions operator) :
    Subfunctor (children worlds operator) where
  obj world := {given | ∀ address : Address Actions operator,
    given ∈ (premise law worlds steps Origins operator address (guard address)).obj world}
  map change := by
    intro given holds address
    exact (premise law worlds steps Origins operator address (guard address)).map change (holds address)

/-- Exact availability reflection identifies the complete native guard
with the independently given Boolean action profile, without imposing a
finite alphabet or finite successful observation. -/
theorem completeGuard_iff [Nonempty Origins] {sort : S.Srt}
    (operator : S.Operator sort) (guard : Guard Actions operator) (world : Cᵒᵖ)
    (given : (children worlds operator).obj world) :
    given ∈ (completeGuard law worlds steps Origins operator guard).obj world ↔
      actualGuard law worlds steps world given = guard := by
  constructor
  · intro holds
    funext address
    exact (premise_iff_guard law worlds steps operator address _ world given).mp (holds address)
  · intro equality address
    exact (premise_iff_guard law worlds steps operator address _ world given).mpr
      (congrFun equality address)

/-- Complete profiles entail each finite restriction that they match;
the converse would require information about unobserved addresses. -/
theorem completeGuard_finite [Nonempty Origins] {sort : S.Srt}
    {operator : S.Operator sort} (guard : Guard Actions operator)
    (rule : FiniteRule Actions operator) (matching : rule.Matches guard)
    (world : Cᵒᵖ) (given : (children worlds operator).obj world)
    (holds : given ∈ (completeGuard law worlds steps Origins operator guard).obj world) :
    given ∈ (finiteGuard law worlds steps Origins rule).obj world := by
  apply (finiteGuard_iff_matches law worlds steps rule world given).mpr
  rw [(completeGuard_iff law worlds steps operator guard world given).mp holds]
  exact matching

end Mettapedia.OSLF.DeterministicGSOS.NativeGuard
