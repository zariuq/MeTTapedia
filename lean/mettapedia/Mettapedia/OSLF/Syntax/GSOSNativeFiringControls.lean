import Mettapedia.OSLF.Syntax.GSOSNativeFiringOccurrences
import Mettapedia.OSLF.Syntax.DeterministicGSOSControls
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Actual negative-only and repeated-positive GSOS firings

Independent clauses include a negative-only unary rule and a binary rule
testing two positive actions on its left argument while ignoring its dead
right argument. A noninjective world map collapses Nat variables to Unit.
Duplicate rule and premise occurrences retain their identities, and the
native postcondition has a genuinely target-dependent finite witness type.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS.NativeFiringControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Functor Opposite
open Mettapedia.TypeTheory Controls EdgeReadout NativeGuard NativeFiring
open PresheafEventCertificates DisplayedPresheafTransport DisplayedPresheafComprehension

abbrev clauseOrigins (_sort : signature.Srt) (operator : Operator) (_action : Nat) : Type :=
  match operator with
  | .stopped => Empty
  | .prefix _ => Fin 2
  | .priority => Unit

noncomputable def negativeClause (label : Nat) : FiniteRule actions (sort := ()) (.prefix label) where
  observed := {⟨(), 8⟩}
  pattern _ := false
  target := Controls.pure (.original ())

noncomputable def bothClause : FiniteRule actions (sort := ()) .priority where
  observed := {⟨left, 7⟩, ⟨left, 8⟩}
  pattern _ := true
  target := priority
    (Controls.pure (.derivative ⟨left, 7⟩ (by simp [observedGuard])))
    (Controls.pure (.derivative ⟨left, 8⟩ (by simp [observedGuard])))

noncomputable abbrev authored : AuthoredFinitePresentation actions where
  Origin := clauseOrigins
  rule := fun _ operator _ origin => match operator with
    | .stopped => origin.elim
    | .prefix label => negativeClause label
    | .priority => bothClause

theorem consistent : FinitePresentation.Consistent actions authored.readoutSet := by
  intro sort operator action guard first second firstMember _ secondMember _
  obtain ⟨firstOrigin, rfl⟩ := firstMember
  obtain ⟨secondOrigin, rfl⟩ := secondMember
  cases operator with
  | stopped => exact firstOrigin.elim
  | «prefix» label => rfl
  | priority => rfl

abbrev Context := WalkingParallelPairᵒᵖ
abbrev spot : Contextᵒᵖ := op (op (.zero : WalkingParallelPair))
abbrev future : Contextᵒᵖ := op (op (.one : WalkingParallelPair))
def change : spot ⟶ future :=
  (show (.zero : WalkingParallelPair) ⟶ .one from WalkingParallelPairHom.left).op.op

/-- Both actual nonidentity world arrows identify all supplied Nat names. -/
abbrev worlds : Contextᵒᵖ ⥤ signature.Families :=
  (opOpEquivalence WalkingParallelPair).functor ⋙ parallelPair Controls.collapse Controls.collapse

def steps : worlds ⟶ worlds ⋙ behaviourFunctor signature actions where
  app _ := fun _ _ => ↾fun _ _ => none
  naturality {first second} arrow := by
    funext base sort
    apply ConcreteCategory.hom_ext
    intro value
    funext label
    rfl

noncomputable abbrev programs : Contextᵒᵖ ⥤ Type := terms worlds ()

theorem variable_collision : ¬ Function.Injective (worlds.map change PUnit.unit ()) := by
  intro injective
  have impossible : (0 : Nat) = 1 := injective rfl
  exact Nat.zero_ne_one impossible

noncomputable def negativeChildren : (NativeGuard.children worlds (sort := ()) (.prefix 9)).obj spot :=
  fun _ => Controls.pure (X := naturals) 10

/-- No positive premise identifier is needed for this actual negative-only
rule: its complete positive inventory is empty. -/
noncomputable def negativeFiring (origin : Fin 2) (action : Nat) :
    Firing authored worlds steps Empty spot (sort := ()) (.prefix 9) action where
  origin := origin
  children := negativeChildren
  positive address := by
    have impossible := address.property
    simp [authored, negativeClause] at impossible
  positive_source address := by
    have impossible := address.property
    simp [authored, negativeClause] at impossible
  positive_action address := by
    have impossible := address.property
    simp [authored, negativeClause] at impossible
  negative address :=
    (noAction_iff_none authored.toLaw worlds steps _ address.val.val.2 spot _).mpr rfl

theorem negative_source (origin : Fin 2) (action : Nat) :
    ((negativeFiring origin action).conclusion consistent).source = prefixed 9 (Controls.pure (X := naturals) 10) := rfl

theorem negative_target (origin : Fin 2) (action : Nat) :
    ((negativeFiring origin action).conclusion consistent).target = Controls.pure (X := naturals) 10 := by
  rw [Firing.conclusion_target]
  simp only [Firing.rule, negativeFiring, authored, negativeClause, Firing.suppliedAssignment,
    Controls.pure, Signature.rename, IndexedPolynomial.Free.map_pure, IndexedPolynomial.Free.join_pure]
  rfl

/-- This actual dead child satisfies the negative profile at every Nat
action, not just the single address inspected by the finite clause. -/
theorem complete_negative_profile :
    negativeChildren ∈ (completeGuard authored.toLaw worlds steps SupportOrigin
      (sort := ()) (.prefix 9) (fun _ => false)).obj spot := by
  apply (completeGuard_iff authored.toLaw worlds steps (.prefix 9) (fun _ => false)
    spot negativeChildren).mpr
  funext address
  rfl

def unobservedPositiveProfile : Guard actions (sort := ()) (.prefix 9) :=
  fun address => decide (address.2 = 7)

/-- The finite clause leaves action seven untested. Its successful guard
does not entail a complete profile demanding that unobserved action. -/
theorem finite_guard_does_not_determine_complete_profile :
    negativeChildren ∈ (finiteGuard authored.toLaw worlds steps SupportOrigin (negativeClause 9)).obj spot ∧
      ¬ negativeChildren ∈ (completeGuard authored.toLaw worlds steps SupportOrigin
        (sort := ()) (.prefix 9) unobservedPositiveProfile).obj spot := by
  refine ⟨(negativeFiring 0 0).native_guard, ?_⟩
  intro holds
  have profile := (completeGuard_iff authored.toLaw worlds steps (.prefix 9)
    unobservedPositiveProfile spot negativeChildren).mp holds
  have impossible := congrFun profile ⟨(), 7⟩
  change false = true at impossible
  exact Bool.false_ne_true impossible

/-- The tested child really has no outgoing action, so the old product of
one selected edge per child cannot provide this valid rule instance. -/
theorem dead_child_has_no_edge :
    ¬ Nonempty (SourceEdgeFibre authored.toLaw worlds steps (Fin 2) () spot (Controls.pure (X := naturals) 10)) := by
  rintro ⟨edge⟩
  have valid := edge.val.valid
  rw [edge.property] at valid
  change none = some edge.val.target at valid
  cases valid

theorem duplicate_rule_origins_retained :
    ((negativeFiring 0 0).conclusion consistent).origin = 0 ∧
      ((negativeFiring 1 0).conclusion consistent).origin = 1 := ⟨rfl, rfl⟩

theorem duplicate_rule_events_differ :
    (negativeFiring 0 0).conclusion consistent ≠ (negativeFiring 1 0).conclusion consistent := by
  intro same
  exact Fin.zero_ne_one (congrArg Event.origin same)

theorem duplicate_rule_targets_agree :
    ((negativeFiring 0 0).conclusion consistent).target =
      ((negativeFiring 1 0).conclusion consistent).target :=
  (negative_target 0 0).trans (negative_target 1 0).symm

noncomputable def childEvent (origin : Fin 3) (action : Nat) :
    Event authored.toLaw worlds steps (Fin 3) () spot where
  origin := origin
  source := prefixed 9 (Controls.pure (X := naturals) 10)
  action := action
  target := Controls.pure (X := naturals) 10
  valid := by
    have issued := ((negativeFiring 0 action).conclusion consistent).valid
    change Operational.coalgebra authored.toLaw (steps.app spot) PUnit.unit ()
      ((negativeFiring 0 action).conclusion consistent).source action =
        some ((negativeFiring 0 action).conclusion consistent).target at issued
    simpa only [negative_source, negative_target] using issued

noncomputable def bothChildren : (NativeGuard.children worlds (sort := ()) .priority).obj spot :=
  fun position => if position = left then prefixed 9 (Controls.pure (X := naturals) 10) else Controls.pure (X := naturals) 20

theorem positive_position_left (address : PositiveAddress bothClause) : address.val.val.1 = left := by
  have member := address.val.property
  simp only [bothClause, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with same | same <;> exact congrArg Sigma.fst same

noncomputable def bothFiring : Firing authored worlds steps (Fin 3) spot (sort := ()) .priority 0 where
  origin := ()
  children := bothChildren
  positive address := childEvent (if address.val.val.2 = 7 then 0 else 1) address.val.val.2
  positive_source address := by
    have atLeft := positive_position_left address
    simp only [childEvent, bothChildren, atLeft, ↓reduceIte]
    rfl
  positive_action _ := rfl
  negative address := by
    have impossible := address.property
    simp [authored, bothClause] at impossible

def seven : PositiveAddress bothClause := ⟨⟨⟨left, 7⟩, by simp [bothClause]⟩, rfl⟩
def eight : PositiveAddress bothClause := ⟨⟨⟨left, 8⟩, by simp [bothClause]⟩, rfl⟩

theorem multiple_actions_one_child :
    (bothFiring.positive seven).action = 7 ∧ (bothFiring.positive eight).action = 8 ∧
      seven.val.val.1 = eight.val.val.1 := ⟨rfl, rfl, rfl⟩

theorem supplied_positive_origins :
    (bothFiring.positive seven).origin = 0 ∧ (bothFiring.positive eight).origin = 1 := ⟨rfl, rfl⟩

theorem both_target :
    (bothFiring.conclusion consistent).target = priority (Controls.pure (X := naturals) 10) (Controls.pure (X := naturals) 10) := by
  rw [Firing.conclusion_target]
  simp only [Firing.rule, bothFiring, authored, bothClause, Firing.suppliedAssignment,
    priority, Controls.pure, Signature.rename, IndexedPolynomial.Free.map_node]
  change IndexedPolynomial.Free.bind signature.polynomial (fun _ _ tree => tree) _ _
    (IndexedPolynomial.Free.node signature.polynomial Operator.priority _) = _
  rw [IndexedPolynomial.Free.bind_node]
  apply congrArg (IndexedPolynomial.Free.node signature.polynomial Operator.priority)
  funext position
  by_cases atLeft : position = left <;>
    simp [atLeft, IndexedPolynomial.Free.map_pure, positiveAddress, childEvent]
  all_goals rfl

theorem ignored_child_dead :
    ¬ Nonempty (SourceEdgeFibre authored.toLaw worlds steps (Fin 2) () spot (bothChildren right)) := by
  rintro ⟨edge⟩
  have valid := edge.val.valid
  rw [edge.property] at valid
  change none = some edge.val.target at valid
  cases valid

theorem future_rule_origin :
    ((negativeFiring 1 0).map change).origin = 1 := rfl

theorem future_positive_origins :
    (((bothFiring.map change).positive seven).origin = 0) ∧
      (((bothFiring.map change).positive eight).origin = 1) := ⟨rfl, rfl⟩

theorem future_negative_target :
    (((negativeFiring 1 0).map change).conclusion consistent).target = Controls.pure () := by
  have natural := congrArg Event.target ((negativeFiring 1 0).conclusion_natural consistent change)
  change signature.rename (worlds.map change)
      ((negativeFiring 1 0).conclusion consistent).target = _ at natural
  rw [negative_target] at natural
  exact natural.symm.trans rfl

def sizeAlgebra : signature.polynomial.Algebra (fun _ _ => Nat) where
  act := fun _ _ layer => match layer with
    | ⟨.stopped, _⟩ => 0
    | ⟨.prefix _, children⟩ => children () + 1
    | ⟨.priority, children⟩ => children left + children right + 1

noncomputable def size {X : signature.Families} (term : signature.Term X ()) : Nat :=
  IndexedPolynomial.Free.fold signature.polynomial (fun _ _ _ => 1) sizeAlgebra PUnit.unit () term

theorem size_rename {X Y : signature.Families} (mapping : X ⟶ Y) (term : signature.Term X ()) :
    size (signature.rename mapping term) = size term :=
  IndexedPolynomial.Free.fold_unique signature.polynomial (fun _ _ _ => 1) sizeAlgebra
    (fun base sort term => IndexedPolynomial.Free.fold signature.polynomial
      (fun _ _ _ => 1) sizeAlgebra base sort
        (IndexedPolynomial.Free.map signature.polynomial (fun base sort => mapping base sort) base sort term))
    (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) PUnit.unit () term

theorem size_elements {first second : programs.Elements} (arrow : first ⟶ second) :
    size first.2 = size second.2 :=
  (size_rename (worlds.map arrow.val) first.2).symm.trans (congrArg size arrow.property)

/-- The postcondition's bound depends on the whole actual target tree. -/
noncomputable def targetFamily : DisplayedFamily programs where
  obj point := Fin (size point.2 + 1)
  map arrow := ↾(Fin.cast (congrArg (fun value => value + 1) (size_elements arrow)))
  map_id _ := by ext value; rfl
  map_comp _ _ := by ext value; rfl

noncomputable def suppliedWitness : targetFamily.obj ⟨spot, (bothFiring.conclusion consistent).target⟩ :=
  Fin.last (size (bothFiring.conclusion consistent).target)

noncomputable def receipt := bothFiring.certificate consistent targetFamily suppliedWitness

theorem complete_certificate_retained :
    ((eventSpan authored.toLaw worlds steps (authored.Origin () .priority 0) ()).resultReadout targetFamily).app spot
      ⟨(bothFiring.conclusion consistent).source, receipt⟩ =
        ⟨(bothFiring.conclusion consistent).target, suppliedWitness⟩ :=
  bothFiring.certificate_result consistent targetFamily suppliedWitness

theorem target_bounds_vary :
    size ((negativeFiring 0 0).conclusion consistent).target + 1 ≠
      size (bothFiring.conclusion consistent).target + 1 := by
  rw [negative_target, both_target]
  decide

end Mettapedia.OSLF.DeterministicGSOS.NativeFiringControls
