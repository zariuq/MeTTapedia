import Mettapedia.OSLF.Syntax.DeterministicGSOSGuardedRules

/-!
# Complete guarded presentations and actual natural laws

Every complete guard has independently authored original and derivative
variables. Instantiating its conclusion gives a natural law, and evaluating
a natural law on those generic inputs recovers its complete guarded rule.
The two roundtrips use arbitrary variable maps, including identifications.
No finiteness condition on action carriers is used.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS

open CategoryTheory Mettapedia.TypeTheory

universe u

variable {S : Signature.{u}} (Actions : S.Srt → Type u)

/-- Relabel the complete supplied constructor inputs. -/
abbrev mapArguments {X Y : S.Families} (mapping : X ⟶ Y)
    {sort : S.Srt} {operator : S.Operator sort}
    (arguments : BehaviourArguments S Actions X operator) :
    BehaviourArguments S Actions Y operator :=
  fun position => (mapping PUnit.unit _ (arguments position).1,
    behaviourMap S Actions mapping PUnit.unit _ (arguments position).2)

theorem assignmentAt_map {X Y : S.Families} (mapping : X ⟶ Y)
    {sort : S.Srt} {operator : S.Operator sort} (guard : Guard Actions operator)
    (arguments : BehaviourArguments S Actions X operator)
    (first : inputGuard Actions arguments = guard)
    (second : inputGuard Actions (mapArguments Actions mapping arguments) = guard) :
    assignmentAt Actions guard (mapArguments Actions mapping arguments) second =
      assignmentAt Actions guard arguments first ≫ mapping := by
  funext base index
  apply ConcreteCategory.hom_ext
  intro name
  cases base
  cases name with
  | original position => rfl
  | derivative address enabled =>
      rcases address with ⟨position, action⟩
      have present : ((arguments position).2 action).isSome = true :=
        (congrFun first ⟨position, action⟩).trans enabled
      cases read : (arguments position).2 action with
      | none => simp [read] at present
      | some value => simp [assignmentAt, behaviourMap, read]

/-- Instantiate an authored conclusion using a separately supplied matching guard. -/
noncomputable def instantiateAt (rules : GuardedSchemas Actions)
    {X : S.Families} {sort : S.Srt} (operator : S.Operator sort)
    (guard : Guard Actions operator)
    (arguments : BehaviourArguments S Actions X operator)
    (matching : inputGuard Actions arguments = guard) (action : Actions sort) :
    Option (S.Term X sort) :=
  (rules sort operator guard action).map (S.rename (assignmentAt Actions guard arguments matching))

/-- Read the guard from the input and instantiate its independently authored rule. -/
noncomputable def instantiate (rules : GuardedSchemas Actions)
    {X : S.Families} {sort : S.Srt} (operator : S.Operator sort)
    (arguments : BehaviourArguments S Actions X operator) (action : Actions sort) :
    Option (S.Term X sort) :=
  instantiateAt Actions rules operator (inputGuard Actions arguments) arguments rfl action

theorem instantiate_eq_at (rules : GuardedSchemas Actions)
    {X : S.Families} {sort : S.Srt} (operator : S.Operator sort)
    (guard : Guard Actions operator)
    (arguments : BehaviourArguments S Actions X operator)
    (matching : inputGuard Actions arguments = guard) (action : Actions sort) :
    instantiate Actions rules operator arguments action =
      instantiateAt Actions rules operator guard arguments matching action := by
  cases matching
  rfl

/-- Rule instantiation commutes with every map of typed variables. -/
theorem instantiate_map (rules : GuardedSchemas Actions)
    {X Y : S.Families} (mapping : X ⟶ Y)
    {sort : S.Srt} (operator : S.Operator sort)
    (arguments : BehaviourArguments S Actions X operator) (action : Actions sort) :
    instantiate Actions rules operator (mapArguments Actions mapping arguments) action =
      (instantiate Actions rules operator arguments action).map (S.rename mapping) := by
  rw [instantiate_eq_at Actions rules operator (inputGuard Actions arguments)
    (mapArguments Actions mapping arguments) (inputGuard_map Actions mapping arguments)]
  unfold instantiate instantiateAt
  cases read : rules sort operator (inputGuard Actions arguments) action with
  | none => rfl
  | some target =>
      change some (S.rename (assignmentAt Actions _ _ _) target) =
        some (S.rename mapping (S.rename (assignmentAt Actions _ _ _) target))
      rw [assignmentAt_map Actions mapping _ arguments rfl]
      congr 1
      exact (IndexedPolynomial.Free.map_comp S.polynomial
        (fun base index => assignmentAt Actions _ arguments rfl base index)
        (fun base index => mapping base index) target).symm

/-- The law obtained by instantiating genuinely independent guarded rules. -/
noncomputable def toLaw (rules : GuardedSchemas Actions) : Law S Actions where
  app X := fun base sort => ↾(fun layer =>
    match base, layer with
    | .unit, ⟨operator, arguments⟩ => instantiate Actions rules operator arguments)
  naturality {X Y} mapping := by
    funext base sort
    apply ConcreteCategory.hom_ext
    intro layer
    cases base
    rcases layer with ⟨operator, arguments⟩
    funext action
    exact instantiate_map Actions rules mapping operator arguments action

/-- Recover an independent guarded conclusion by using distinct generic names. -/
noncomputable def fromLaw (law : Law S Actions) : GuardedSchemas Actions :=
  fun sort operator guard action =>
    law.app (ruleVariables Actions operator guard) PUnit.unit sort
      ⟨operator, genericArguments Actions operator guard⟩ action

theorem fromLaw_toLaw (rules : GuardedSchemas Actions) :
    fromLaw Actions (toLaw Actions rules) = rules := by
  funext sort operator guard action
  change instantiate Actions rules operator (genericArguments Actions operator guard) action = _
  rw [instantiate_eq_at Actions rules operator guard _
    (inputGuard_generic Actions operator guard)]
  unfold instantiateAt
  rw [assignmentAt_generic]
  cases rules sort operator guard action with
  | none => rfl
  | some target =>
      change some (S.rename (𝟙 (ruleVariables Actions operator guard)) target) = some target
      exact congrArg some (IndexedPolynomial.Free.map_id S.polynomial target)

theorem toLaw_fromLaw (law : Law S Actions) :
    toLaw Actions (fromLaw Actions law) = law := by
  apply NatTrans.ext
  funext X base sort
  apply ConcreteCategory.hom_ext
  intro layer
  cases base
  rcases layer with ⟨operator, arguments⟩
  funext action
  have natural := congrArg (fun mapping =>
      mapping PUnit.unit sort
        ⟨operator, genericArguments Actions operator (inputGuard Actions arguments)⟩ action)
    (law.naturality (assignment Actions arguments))
  change law.app X PUnit.unit sort
      ⟨operator, mapArguments Actions (assignment Actions arguments)
        (genericArguments Actions operator (inputGuard Actions arguments))⟩ action =
    (fromLaw Actions law sort operator (inputGuard Actions arguments) action).map
      (S.rename (assignment Actions arguments)) at natural
  have recovered : mapArguments Actions (assignment Actions arguments)
      (genericArguments Actions operator (inputGuard Actions arguments)) = arguments :=
    generic_assignment Actions arguments
  rw [recovered] at natural
  change (fromLaw Actions law sort operator (inputGuard Actions arguments) action).map
      (S.rename (assignmentAt Actions _ arguments rfl)) = _
  have assigned := @assignmentAt_self S Actions X sort operator arguments
  exact (congrArg (fun assignment =>
    (fromLaw Actions law sort operator (inputGuard Actions arguments) action).map
      (S.rename assignment)) assigned).trans natural.symm

/-- Arbitrary-action complete guarded schemas classify the actual natural laws. -/
noncomputable def guardedLawEquiv : GuardedSchemas Actions ≃ Law S Actions where
  toFun := toLaw Actions
  invFun := fromLaw Actions
  left_inv := fromLaw_toLaw Actions
  right_inv := toLaw_fromLaw Actions

end Mettapedia.OSLF.DeterministicGSOS
