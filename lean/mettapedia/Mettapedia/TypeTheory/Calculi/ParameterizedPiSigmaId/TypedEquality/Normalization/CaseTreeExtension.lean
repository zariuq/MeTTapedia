import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CaseTreeConfluence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.WeakHead

/-!
# A constructor system extended by case trees

A rule package presented by constructor patterns stays a constructor system
when its root computation is extended by case-tree definitions, provided the
two families are orthogonal. Orthogonality is the condition `Apart`: each
name defined by a tree is not a defined name of the base and does not occur
in a base left side, and each constructor a tree splits on is not a defined
name of the base. A base left side and a leaf left side are then headed by
distinct defined constants, so no term is an instance of both, and the leaf
equations remain a determined constructor family. The extended package is
Church–Rosser by the complete development of a constructor system.

Root steps of any constructor presentation are deterministic. That is a
different statement from Church–Rosser: it is one step at one term, read off
the determined equations, and it is what `RootShape` asks of the extended
package. `RootShape` also asks that each root step be a computing spine whose
inspection accepts the arguments. Base steps keep their roles because their
heads are not tree names. Tree steps are settled by the covering hypothesis,
and acceptance follows.

The conditions are not dispensable. A base equation `f x ⟶ z` together with a
leaf `f x ⟶ o` for the same `f` is a critical pair. The two contracts are
constants, no root step starts at a constant, and they have no common reduct.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization
namespace CaseTreeExtension

open AlgebraicSchema (SchemaFamily SchemaStep LeftLinearFamily variableMultiplicity)
open AlgebraicParallel ConversionCoherence
open ConstructorSystem (Pattern LeftSide System spineHead spineHead_subst_leftSide
  ConstructorPresentation Normal defined_or_cons spineHead_appSpine_const
  root_deterministic computation_head)

variable {Head : Type}

/-! ## The extended family -/

/-- The equations of a base together with the leaf equations of case-tree
definitions. -/
inductive ExtendedSchema (schema : SchemaFamily Head) (defs : List (CaseTreeDefinition Head)) :
    {arity : Nat} → Tm Head arity → Tm Head arity → Prop where
  | base {arity : Nat} {left right : Tm Head arity} :
      schema left right → ExtendedSchema schema defs left right
  | tree {arity : Nat} {left right : Tm Head arity} :
      leafSchema defs left right → ExtendedSchema schema defs left right

theorem ExtendedSchema.map {schema schema' : SchemaFamily Head}
    {defs : List (CaseTreeDefinition Head)}
    (f : ∀ {arity : Nat} {left right : Tm Head arity}, schema left right → schema' left right)
    {arity : Nat} {left right : Tm Head arity} (rule : ExtendedSchema schema defs left right) :
    ExtendedSchema schema' defs left right :=
  match rule with
  | .base rule => .base (f rule)
  | .tree rule => .tree rule

/-- Whether a list of case-tree definitions contains `c`, as a `Bool`. -/
def nameDefined : List (CaseTreeDefinition Head) → DeclName → Bool
  | [], _ => false
  | d :: ds, c => d.name == c || nameDefined ds c

theorem nameDefined_iff :
    ∀ (defs : List (CaseTreeDefinition Head)) (c : DeclName),
      nameDefined defs c = true ↔ definedIn defs c
  | [], _ => Iff.intro (fun h => by cases h) (fun mem => by cases mem)
  | d :: ds, c => by
      refine ⟨fun h => ?_, fun mem => ?_⟩
      · rcases Bool.or_eq_true_iff.mp h with hname | hrest
        · exact List.mem_cons.mpr (Or.inl ((beq_iff_eq.mp hname).symm))
        · exact List.mem_cons.mpr (Or.inr ((nameDefined_iff ds c).mp hrest))
      · rcases List.mem_cons.mp mem with same | rest
        · rw [nameDefined, same, BEq.rfl, Bool.true_or]
        · rw [nameDefined, (nameDefined_iff ds c).mpr rest, Bool.or_true]

theorem nameDefined_eq_false {defs : List (CaseTreeDefinition Head)} {c : DeclName}
    (fresh : ¬ definedIn defs c) : nameDefined defs c = false :=
  match h : nameDefined defs c with
  | false => rfl
  | true => absurd ((nameDefined_iff defs c).mp h) fresh

/-- Case-tree definitions kept apart from a constructor system.

`names` and `constructors` are the two separations named for the extension.
`absent` is the further fact the left-side proof uses: a constant that
occurs in a base left side, and then becomes defined, is no longer a pattern
constant, so that left side is not a left side of the extended system. A name
defined by both families fails `names`, and it also fails `absent`, because
the base left side is headed by it. -/
structure Apart (defs : List (CaseTreeDefinition Head)) (system : System Head) : Prop where
  names : ∀ d ∈ defs, ¬ system.defined d.name
  constructors : ∀ d ∈ defs, ∀ c ∈ d.tree.constructors, ¬ system.defined c
  absent : ∀ d ∈ defs, ∀ {m : Nat} {left right : Tm Head m}, system.schema left right →
    ConstructorSystem.mentionsConst d.name left = false

/-- The defined constants of the extension: the base's, or a tree's. -/
def extendDefined (system : System Head) (defs : List (CaseTreeDefinition Head))
    (c : DeclName) : Prop :=
  system.defined c ∨ definedIn defs c

/-- Their arities: a tree's arity on a tree's name, and the base's otherwise. -/
def extendArity (system : System Head) (defs : List (CaseTreeDefinition Head))
    (c : DeclName) : Nat :=
  if nameDefined defs c then arityOf defs c else system.arity c

theorem extendArity_of_tree {system : System Head} {defs : List (CaseTreeDefinition Head)}
    {c : DeclName} (defined : nameDefined defs c = true) :
    extendArity system defs c = arityOf defs c := by
  rw [extendArity, defined]
  exact if_pos rfl

theorem extendArity_of_base {system : System Head} {defs : List (CaseTreeDefinition Head)}
    {c : DeclName} (fresh : nameDefined defs c = false) :
    extendArity system defs c = system.arity c := by
  rw [extendArity, fresh]
  exact if_neg Bool.false_ne_true

theorem not_definedIn_of_names {defs : List (CaseTreeDefinition Head)} {system : System Head}
    (apart : Apart defs system) {name : DeclName} (defined : system.defined name) :
    ¬ definedIn defs name := by
  intro mem
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp mem
  exact apart.names d hd defined

/-- No term instantiates both a base left side and a leaf left side: they are
headed by distinct defined constants. -/
theorem base_tree_disjoint {defs : List (CaseTreeDefinition Head)}
    (conditions : LeafConditions defs) {system : System Head} (apart : Apart defs system)
    {m m' n : Nat} {left right : Tm Head m} {left' right' : Tm Head m'}
    (rule : system.schema left right) (rule' : leafSchema defs left' right')
    (σ : Sub Head m n) (σ' : Sub Head m' n) (same : subst σ left = subst σ' left') : False := by
  obtain ⟨name, defined, -, side⟩ := system.left rule
  obtain ⟨name', mem, -, side'⟩ := leafSchema_left conditions rule'
  have first := spineHead_subst_leftSide side σ
  have second := spineHead_subst_leftSide side' σ'
  rw [same, second] at first
  obtain ⟨headSame, -⟩ := Prod.mk.inj (Option.some.inj first)
  obtain ⟨d, hd, nameEq⟩ := List.mem_map.mp mem
  exact apart.names d hd (nameEq.trans headSame ▸ defined)

theorem extend_left {defs : List (CaseTreeDefinition Head)} (conditions : LeafConditions defs)
    {system : System Head} (apart : Apart defs system) {m : Nat} {left right : Tm Head m}
    (rule : ExtendedSchema system.schema defs left right) :
    ∃ name, extendDefined system defs name ∧ 0 < extendArity system defs name ∧
      LeftSide (extendDefined system defs) left name (extendArity system defs name) := by
  cases rule with
  | base rule =>
      obtain ⟨name, defined, positive, side⟩ := system.left rule
      have fresh : nameDefined defs name = false :=
        nameDefined_eq_false (not_definedIn_of_names apart defined)
      have arityEq : extendArity system defs name = system.arity name :=
        extendArity_of_base fresh
      refine ⟨name, Or.inl defined, ?_, ?_⟩
      · rw [arityEq]
        exact positive
      · rw [arityEq]
        exact LeftSide.of_list side (defs.map CaseTreeDefinition.name) fun c mem => by
          obtain ⟨d, hd, rfl⟩ := List.mem_map.mp mem
          exact apart.absent d hd rule
  | tree rule =>
      obtain ⟨d, mem, N, leaf, rfl⟩ := rule
      have inTrees : definedIn defs d.name := List.mem_map_of_mem mem
      have marked : nameDefined defs d.name = true := (nameDefined_iff defs d.name).mpr inTrees
      have arityEq : extendArity system defs d.name = d.arity := by
        rw [extendArity_of_tree marked, arityOf_of_mem conditions.names mem]
      have hN := leafSchema_vars conditions mem leaf
      have length : (Pat.terms N (varTerms (Head := Head) m)).length = d.arity := by
        rw [Pat.fillAll_length, leaf.length, List.length_replicate]
      refine ⟨d.name, Or.inr inTrees, ?_, ?_⟩
      · rw [arityEq]
        exact conditions.arity_pos d mem
      · rw [arityEq, ← length]
        refine leftSide_appSpine d.name _
          (Pat.pattern_terms N _ ?_ (fun _ mem => varTerms_var mem)
            (by rw [varTerms_length, hN]))
        intro c cmem defined
        rcases leaf.constructors c cmem with root | split
        · rw [Pat.constructorsAll_replicate] at root
          cases root
        · rcases defined with base | tree
          · exact apart.constructors d mem c split base
          · exact conditions.constructors d mem c split tree

theorem extend_linear {defs : List (CaseTreeDefinition Head)} (conditions : LeafConditions defs)
    {system : System Head} : LeftLinearFamily (ExtendedSchema system.schema defs) := by
  intro _ _ _ rule
  cases rule with
  | base rule => exact system.linear rule
  | tree rule =>
      intro index
      exact Nat.le_of_eq (leafSchema_multiplicity conditions rule index)

theorem extend_covered {defs : List (CaseTreeDefinition Head)} (conditions : LeafConditions defs)
    {system : System Head} {m : Nat} {left right : Tm Head m}
    (rule : ExtendedSchema system.schema defs left right) :
    ∀ index, 0 < variableMultiplicity index right → 0 < variableMultiplicity index left := by
  intro index occurs
  cases rule with
  | base rule => exact system.covered rule index occurs
  | tree rule =>
      rw [leafSchema_multiplicity conditions rule index]
      exact Nat.zero_lt_succ 0

theorem extend_determined {defs : List (CaseTreeDefinition Head)} (conditions : LeafConditions defs)
    {system : System Head} (apart : Apart defs system) :
    ∀ {m m' n n' : Nat} {left right : Tm Head m} {left' right' : Tm Head m'},
      ExtendedSchema system.schema defs left right →
        ExtendedSchema system.schema defs left' right' →
      ∀ (σ : Sub Head m n) (σ' : Sub Head m' n), subst σ left = subst σ' left' →
      ∀ develop : Tm Head n → Tm Head n',
        subst (fun index => develop (σ index)) right =
          subst (fun index => develop (σ' index)) right' := by
  intro _ _ _ _ _ _ _ _ rule rule' σ σ' same develop
  cases rule with
  | base rule =>
      cases rule' with
      | base rule' => exact system.determined rule rule' σ σ' same develop
      | tree rule' => exact (base_tree_disjoint conditions apart rule rule' σ σ' same).elim
  | tree rule =>
      cases rule' with
      | base rule' => exact (base_tree_disjoint conditions apart rule' rule σ' σ same.symm).elim
      | tree rule' => exact leafSchema_determined conditions rule rule' σ σ' same develop

/-- The base's equations and the leaf equations form a constructor system when
the case-tree definitions are apart from the base. -/
def extendSystem {defs : List (CaseTreeDefinition Head)} (conditions : LeafConditions defs)
    {system : System Head} (apart : Apart defs system) : System Head where
  schema := ExtendedSchema system.schema defs
  defined := extendDefined system defs
  arity := extendArity system defs
  left := extend_left conditions apart
  linear := extend_linear conditions
  covered := extend_covered conditions
  determined := extend_determined conditions apart

/-! ## The extended package -/

/-- The union of two root computations. -/
def rootUnion (first second : RootComputation Head) : RootComputation Head where
  step := fun left right => first.step left right ∨ second.step left right
  rename := by
    intro _ _ ρ _ _ step
    exact step.elim (fun h => Or.inl (first.rename ρ h)) (fun h => Or.inr (second.rename ρ h))
  substitute := by
    intro _ _ σ _ _ step
    exact step.elim (fun h => Or.inl (first.substitute σ h)) (fun h => Or.inr (second.substitute σ h))

/-- The package `base` extended by case-tree definitions. Its root step is a
step of the base or a step of the trees. Every other field is the base's. -/
def extend (base : Rules Head) (defs : List (CaseTreeDefinition Head)) : Rules Head :=
  { base with computation := rootUnion base.computation (caseTreeComputation defs) }

theorem extend_step {base : Rules Head} {defs : List (CaseTreeDefinition Head)} {n : Nat}
    {t u : Tm Head n} :
    (extend base defs).computation.step t u ↔
      base.computation.step t u ∨ (caseTreeComputation defs).step t u :=
  Iff.rfl

/-- A presentation of the base extends to the package with case trees. -/
def extendPresentation {defs : List (CaseTreeDefinition Head)} (conditions : LeafConditions defs)
    {base : Rules Head} (presentation : SchemaPresentation base) :
    SchemaPresentation (extend base defs) where
  schema := ExtendedSchema presentation.schema defs
  sound := fun rule substitution => by
    cases rule with
    | base rule => exact Or.inl (presentation.sound rule substitution)
    | tree rule =>
        exact Or.inr ((caseTreeComputation_iff_leafSchema conditions).mpr
          (SchemaStep.instantiate rule substitution))
  cover := fun step => by
    rcases step with step | step
    · obtain ⟨arity, left, right, substitution, rule, rfl, rfl⟩ := presentation.cover step
      exact ⟨arity, left, right, substitution, .base rule, rfl, rfl⟩
    · cases (caseTreeComputation_iff_leafSchema conditions).mp step with
      | instantiate rule substitution =>
          exact ⟨_, _, _, substitution, .tree rule, rfl, rfl⟩

/-- The extended package as a definition by constructor patterns. -/
def extendConstructors {base : Rules Head} {defs : List (CaseTreeDefinition Head)}
    (equations : ConstructorPresentation base) (conditions : LeafConditions defs)
    (apart : Apart defs equations.system) : ConstructorPresentation (extend base defs) where
  presentation := extendPresentation conditions equations.presentation
  system := extendSystem conditions apart
  same := fun _ _ =>
    Iff.intro
      (fun h => ExtendedSchema.map (fun rule => (equations.same _ _).mp rule) h)
      (fun h => ExtendedSchema.map (fun rule => (equations.same _ _).mpr rule) h)
  symmetric := equations.symmetric

/-- A constructor system extended by case-tree definitions apart from it is
Church–Rosser. -/
theorem extend_churchRosser {base : Rules Head} {defs : List (CaseTreeDefinition Head)}
    (equations : ConstructorPresentation base) (conditions : LeafConditions defs)
    (apart : Apart defs equations.system) : ChurchRosser (extend base defs) :=
  (extendConstructors equations conditions apart).churchRosser

/-- Root steps of the extended package are deterministic. -/
theorem extend_root_deterministic {base : Rules Head} {defs : List (CaseTreeDefinition Head)}
    (equations : ConstructorPresentation base) (conditions : LeafConditions defs)
    (apart : Apart defs equations.system) {n : Nat} {t u u' : Tm Head n}
    (step : (extend base defs).computation.step t u)
    (step' : (extend base defs).computation.step t u') : u = u' :=
  root_deterministic (extendConstructors equations conditions apart) step step'

/-! ## Root shape -/

/-- The tree recorded for a name, the first definition of that name. -/
def treeOf : List (CaseTreeDefinition Head) → DeclName → Option (CaseTree Head)
  | [], _ => none
  | d :: ds, name => if d.name = name then some d.tree else treeOf ds name

theorem treeOf_of_mem :
    ∀ {defs : List (CaseTreeDefinition Head)}, (defs.map CaseTreeDefinition.name).Nodup →
      ∀ {d : CaseTreeDefinition Head}, d ∈ defs → treeOf defs d.name = some d.tree
  | [], _, _, mem => by cases mem
  | d' :: ds, names, d, mem => by
      rw [treeOf]
      rcases List.mem_cons.mp mem with rfl | mem'
      · exact if_pos rfl
      · have fresh : d'.name ∉ ds.map CaseTreeDefinition.name := (List.nodup_cons.mp names).1
        have ne : d'.name ≠ d.name := fun same => fresh (same.symm ▸ List.mem_map_of_mem mem')
        rw [if_neg ne]
        exact treeOf_of_mem (List.nodup_cons.mp names).2 mem'

theorem treeOf_eq_none :
    ∀ (defs : List (CaseTreeDefinition Head)) (c : DeclName), ¬ definedIn defs c →
      treeOf defs c = none
  | [], _, _ => rfl
  | d :: ds, c, fresh => by
      rw [treeOf]
      have ne : d.name ≠ c := fun same =>
        fresh (same ▸
          (List.mem_cons_self : d.name ∈ d.name :: ds.map CaseTreeDefinition.name))
      rw [if_neg ne]
      exact treeOf_eq_none ds c fun mem => fresh (List.mem_cons_of_mem _ mem)

/-- Roles of the extension: a tree name computes by its tree, and every other
name keeps the role it had in the base. -/
def extendRoles (baseRoles : Roles Head) (defs : List (CaseTreeDefinition Head)) : Roles Head :=
  fun c => match treeOf defs c with
    | some tree => .computes (arityOf defs c) tree.inspect
    | none => baseRoles c

theorem extendRoles_base {baseRoles : Roles Head} {defs : List (CaseTreeDefinition Head)}
    {c : DeclName} (fresh : ¬ definedIn defs c) :
    extendRoles baseRoles defs c = baseRoles c := by
  rw [extendRoles, treeOf_eq_none defs c fresh]

theorem extendRoles_tree {baseRoles : Roles Head} {defs : List (CaseTreeDefinition Head)}
    (names : (defs.map CaseTreeDefinition.name).Nodup) {d : CaseTreeDefinition Head}
    (mem : d ∈ defs) :
    extendRoles baseRoles defs d.name = .computes d.arity d.tree.inspect := by
  rw [extendRoles, treeOf_of_mem names mem, arityOf_of_mem names mem]

theorem extendRoles_keep_constructor {baseRoles : Roles Head}
    {defs : List (CaseTreeDefinition Head)}
    (notConstructor : ∀ d ∈ defs, ∀ arity : Nat, baseRoles d.name ≠ .constructor arity)
    {c : DeclName} {arity : Nat} (role : baseRoles c = .constructor arity) :
    extendRoles baseRoles defs c = .constructor arity := by
  have fresh : ¬ definedIn defs c := by
    intro mem
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp mem
    exact notConstructor d hd arity role
  rw [extendRoles_base fresh, role]

/-- The extended package has root shape when the base does, the base inspects
only constructor forms, no tree name is a constructor of the base, and each
tree covers the extended roles.

A tree name that was a constructor would be overwritten by a computing role,
and a constructor inspection of the base would no longer accept. A head-form
inspection is not kept, because acceptance at a head form reads every
non-computing role. Coverage is a hypothesis: it mentions the roles of the
families the trees split on, and those roles are the caller's. -/
theorem extend_rootShape {base : Rules Head} {defs : List (CaseTreeDefinition Head)}
    {baseRoles : Roles Head} (equations : ConstructorPresentation base)
    (shape : RootShape base baseRoles) (conditions : LeafConditions defs)
    (apart : Apart defs equations.system)
    (onlyConstructors : ∀ {c : DeclName} {arity : Nat} {inspect : InspectTree},
      baseRoles c = .computes arity inspect → inspect.OnlyConstructors)
    (notConstructor : ∀ d ∈ defs, ∀ arity : Nat, baseRoles d.name ≠ .constructor arity)
    (declared : ConstructorsDeclared (extendRoles baseRoles defs))
    (covers : ∀ d ∈ defs, d.tree.Covers (extendRoles baseRoles defs)) :
    RootShape (extend base defs) (extendRoles baseRoles defs) where
  spine := fun step => by
    rcases step with step | step
    · obtain ⟨c, arity, inspect, args, role, rfl, length, accepts⟩ := shape.spine step
      obtain ⟨name, _, defined, head⟩ := computation_head equations step
      have shapeHead := spineHead_appSpine_const c args
      obtain ⟨cEq, _⟩ := Prod.mk.inj (Option.some.inj (shapeHead.symm.trans head))
      have definedC : equations.system.defined c := cEq.symm ▸ defined
      have fresh : ¬ definedIn defs c := not_definedIn_of_names apart definedC
      refine ⟨c, arity, inspect, args, ?_, rfl, length, ?_⟩
      · rw [extendRoles_base fresh]
        exact role
      · exact (accepts.of_constructors (extendRoles_keep_constructor notConstructor))
          (onlyConstructors role)
    · obtain ⟨d, mem, treeStep⟩ := step
      obtain ⟨args, rfl, length, settled⟩ :=
        CaseTree.step_settled declared (covers d mem) treeStep
      exact ⟨d.name, d.arity, d.tree.inspect, args, extendRoles_tree conditions.names mem, rfl,
        length, settled.accepts⟩
  deterministic := fun step step' =>
    root_deterministic (extendConstructors equations conditions apart) step step'

/-! ## A shared name is a critical pair -/

/-- One equation `f x ⟶ z`, for the overlap below. -/
inductive ForkSchema : {arity : Nat} → Tm Unit arity → Tm Unit arity → Prop where
  | rule : ForkSchema (.app (.const `f) (.var (0 : Fin 1))) (.const `z)

/-- A leaf `f x ⟶ o` for the same `f`. -/
def forkDef : CaseTreeDefinition Unit where
  name := `f
  arity := 1
  tree := .leaf 1 (.const `o)

/-- The leaf is a case-tree definition: one name, positive arity, a scoped
leaf, and no constructor to split on. -/
theorem fork_leafConditions : LeafConditions [forkDef] where
  names := by
    refine List.nodup_cons.mpr ⟨?_, List.nodup_nil⟩
    intro h
    cases h
  arity_pos := by
    intro _ mem
    cases mem with
    | head => exact Nat.zero_lt_succ 0
    | tail _ h => cases h
  inScope := by
    intro _ mem
    cases mem with
    | head => exact .leaf (.const `o)
    | tail _ h => cases h
  constructors := by
    intro _ mem _ hc
    cases mem with
    | head => cases hc
    | tail _ h => cases h

def forkBase : Rules Unit where
  headTyping := fun _ _ => False
  isUniverse := fun _ => False
  join := fun _ _ _ => False
  cumulative := fun _ _ => False
  headEq := fun _ _ => False
  computation := SchemaFamily.computation ForkSchema

/-- The one-equation package extended by the leaf of the same name. -/
def forkExtend : Rules Unit :=
  extend forkBase [forkDef]

theorem fork_base_step :
    forkExtend.computation.step (.app (.const `f) (.var (0 : Fin 1))) (.const `z) :=
  Or.inl (SchemaStep.instantiate ForkSchema.rule ids)

theorem fork_tree_step :
    forkExtend.computation.step (.app (.const `f) (.var (0 : Fin 1))) (.const `o) :=
  Or.inr ⟨forkDef, List.Mem.head [], ⟨[.var (0 : Fin 1)], rfl, rfl, .leaf (.const `o) rfl⟩⟩

theorem fork_spineHead {n : Nat} {t u : Tm Unit n} (step : forkExtend.computation.step t u) :
    spineHead t = some (`f, 1) := by
  rcases step with step | step
  · cases step with
    | instantiate schemaRule _ =>
        cases schemaRule
        rfl
  · obtain ⟨_, mem, treeStep⟩ := step
    cases mem with
    | head =>
        obtain ⟨_, rfl, length, _⟩ := treeStep
        rw [spineHead_appSpine_const, length]
        rfl
    | tail _ h => cases h

theorem fork_no_const (name : DeclName) {n : Nat} {u : Tm Unit n} :
    ¬ forkExtend.computation.step (.const name) u := by
  intro step
  have h := fork_spineHead step
  change (some (name, 0) : Option (DeclName × Nat)) = some (`f, 1) at h
  obtain ⟨-, countEq⟩ := Prod.mk.inj (Option.some.inj h)
  cases countEq

theorem fork_const_normal {n : Nat} (name : DeclName) :
    Normal forkExtend (.const name : Tm Unit n) :=
  Normal.const name (fork_no_const name)

theorem z_ne_o : (`z : DeclName) ≠ `o := by
  decide

/-- Without the separation of names, Church–Rosser fails. `f x` steps to `z`
by the base and to `o` by the tree. Both contracts are constants, so neither
takes a root step, and a common reduct would identify `z` with `o`. The leaf
conditions hold; the shared name is what fails. -/
theorem fork_not_churchRosser : ¬ ChurchRosser forkExtend := by
  intro churchRosser
  obtain ⟨_, toZ, toO⟩ := churchRosser (n := 1)
    (.trans _ _ _
      (.symm _ _ (.rel _ _ (.root fork_base_step)))
      (.rel _ _ (.root fork_tree_step)))
  have toConstZ := Normal.stepStar (fork_const_normal (n := 1) `z) toZ
  have toConstO := Normal.stepStar (fork_const_normal (n := 1) `o) toO
  exact z_ne_o (Tm.const.inj (toConstZ.symm.trans toConstO))

end CaseTreeExtension
end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
