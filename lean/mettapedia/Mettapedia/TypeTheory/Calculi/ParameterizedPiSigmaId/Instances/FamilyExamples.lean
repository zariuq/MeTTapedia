import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.FamilyVectors
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.FamilyVectorsEliminator
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.FamilyExpressions
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.Tower

/-!
# Elements of declared families in a concrete setting

The cumulative tower extended by the types `ty` (with `tnum`, `tbool`) and `num` (with
`zero`, `succ`) as simple inductive types, and by the families of expressions and vectors,
whose declared types are those of their declarations (`FamilyDecl.familyType`,
`FamilyDecl.ctorType`), and by the eliminator of vectors at its declared type. The setting
meets every field of `Setting`: a level model, the shape of root steps (there are none in
this package; the eliminator's rules are added in `FamilyVectorsEliminatorExamples`), and
declared constructors.

In it the family packs have reducible constructor elements, not only neutral ones:

* `lit x : exp tnum` for a variable `x : num` (`lit_reducible`);
* `ite t c x y : exp t` at the variable type `t`, in the context
  `t : ty, c : exp tbool, x : exp t, y : exp t` (`ite_reducible_at_variable`);
* `vnil A : vec A zero` for a variable `A : U0` (`vnil_reducible`).

The families' type constants are rigid here: the present relation has no family case, and
this module exercises the family pack, which stands before the relation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization
namespace FamilyExamples

open Families
open Mettapedia.TypeTheory.UniverseLevel

/-! ## The setting -/

/-- The lowest universe. -/
abbrev u0 : Tower.Head := .sort (.const 0)

/-- The declared types. -/
def constantType : DeclName → Option (Tm Tower.Head 0) := fun name =>
  if name = FamilyExpressions.ty then some (.head u0)
  else if name = FamilyExpressions.tnum then some (.const FamilyExpressions.ty)
  else if name = FamilyExpressions.tbool then some (.const FamilyExpressions.ty)
  else if name = FamilyExpressions.num then some (.head u0)
  else if name = FamilyVectors.zero then some (.const FamilyExpressions.num)
  else if name = FamilyExpressions.exp then some (FamilyExpressions.expDecl u0).familyType
  else if name = FamilyExpressions.lit then
    some ((FamilyExpressions.expDecl u0).ctorType FamilyExpressions.litTele)
  else if name = FamilyExpressions.ite then
    some ((FamilyExpressions.expDecl u0).ctorType FamilyExpressions.iteTele)
  else if name = FamilyVectors.vec then some (FamilyVectors.vecDecl u0).familyType
  else if name = FamilyVectors.vnil then
    some ((FamilyVectors.vecDecl u0).ctorType FamilyVectors.vnilTele)
  else if name = FamilyVectors.succ then
    some (.pi (.const FamilyExpressions.num) (.const FamilyExpressions.num))
  else if name = FamilyVectors.vcons then
    some ((FamilyVectors.vecDecl u0).ctorType FamilyVectors.vconsTele)
  else if name = FamilyVectorsEliminator.vecElim then
    some (FamilyVectorsEliminator.elimType u0 u0)
  else none

/-- The tower with the declared constants. -/
def rules : Rules Tower.Head := { Tower.rules with constantType := constantType }

/-- The roles: two simple inductive types and the constructors; the family constants are
rigid, since the present relation has no family case. -/
def roles : Roles Tower.Head := fun name =>
  if name = FamilyExpressions.ty then .inductive FamilyExpressions.tyCtors
  else if name = FamilyExpressions.num then .inductive FamilyVectors.numCtors
  else if name = FamilyExpressions.tnum ∨ name = FamilyExpressions.tbool ∨
      name = FamilyVectors.zero then .constructor 0
  else if name = FamilyVectors.succ ∨ name = FamilyExpressions.lit ∨
      name = FamilyExpressions.iszero ∨ name = FamilyVectors.vnil then .constructor 1
  else if name = FamilyExpressions.add then .constructor 2
  else if name = FamilyExpressions.ite ∨ name = FamilyVectors.vcons then .constructor 4
  else if name = FamilyVectorsEliminator.vecElim then
    .computes 6 (.split 5 .constructor fun _ => .leaf)
  else .rigid

theorem roles_ty : roles FamilyExpressions.ty = .inductive FamilyExpressions.tyCtors := rfl
theorem roles_num : roles FamilyExpressions.num = .inductive FamilyVectors.numCtors := rfl
theorem roles_tnum : roles FamilyExpressions.tnum = .constructor 0 := rfl
theorem roles_tbool : roles FamilyExpressions.tbool = .constructor 0 := rfl
theorem roles_zero : roles FamilyVectors.zero = .constructor 0 := rfl
theorem roles_succ : roles FamilyVectors.succ = .constructor 1 := rfl
theorem roles_lit : roles FamilyExpressions.lit = .constructor 1 := rfl
theorem roles_vnil : roles FamilyVectors.vnil = .constructor 1 := rfl
theorem roles_ite : roles FamilyExpressions.ite = .constructor 4 := rfl
theorem roles_vcons : roles FamilyVectors.vcons = .constructor 4 := rfl
theorem roles_vecElim :
    roles FamilyVectorsEliminator.vecElim = .computes 6 (.split 5 .constructor fun _ => .leaf) :=
  rfl

/-- The only inductive types are `ty` and `num`. -/
theorem roles_inductive {T : DeclName} {cs : List (DeclName × List (Field Tower.Head))}
    (role : roles T = .inductive cs) :
    (T = FamilyExpressions.ty ∧ cs = FamilyExpressions.tyCtors) ∨
      (T = FamilyExpressions.num ∧ cs = FamilyVectors.numCtors) := by
  unfold roles at role
  split at role
  · exact .inl ⟨‹_›, (Role.inductive.inj role).symm⟩
  · split at role
    · exact .inr ⟨‹_›, (Role.inductive.inj role).symm⟩
    · split at role
      · cases role
      · split at role
        · cases role
        · split at role
          · cases role
          · split at role
            · cases role
            · split at role
              · cases role
              · cases role

theorem constructorsDeclared : ConstructorsDeclared roles where
  arity := by
    intro T cs k fields role mem
    rcases roles_inductive role with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [FamilyExpressions.tyCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
        or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact roles_tnum
      · exact roles_tbool
    · simp only [FamilyVectors.numCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
        or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact roles_zero
      · exact roles_succ
  distinct := by
    intro T cs role
    rcases roles_inductive role with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact List.nodup_cons.mpr ⟨by simp [FamilyExpressions.tnum_ne_tbool],
        List.nodup_singleton _⟩
    · exact List.nodup_cons.mpr ⟨by simp [FamilyVectors.zero_ne_succ], List.nodup_singleton _⟩

theorem shape : RootShape rules roles where
  spine := fun step => step.elim
  deterministic := fun step => step.elim

/-- The tower's level model, for the rule package with the declared constants. -/
def levels : LevelModel rules ℕ where
  level := (TowerModel.levels (L := ℕ) fun _ => 0).level
  successor := (TowerModel.levels (L := ℕ) fun _ => 0).successor
  universe_typing := (TowerModel.levels (L := ℕ) fun _ => 0).universe_typing
  ground_typing := (TowerModel.levels (L := ℕ) fun _ => 0).ground_typing
  cumulative_universe := (TowerModel.levels (L := ℕ) fun _ => 0).cumulative_universe
  headEq_level := (TowerModel.levels (L := ℕ) fun _ => 0).headEq_level
  join_level := (TowerModel.levels (L := ℕ) fun _ => 0).join_level
  join_exists := (TowerModel.levels (L := ℕ) fun _ => 0).join_exists
  join_upper := (TowerModel.levels (L := ℕ) fun _ => 0).join_upper
  cumulative_refl := (TowerModel.levels (L := ℕ) fun _ => 0).cumulative_refl
  headEq_symm := (TowerModel.levels (L := ℕ) fun _ => 0).headEq_symm
  headEq_trans := (TowerModel.levels (L := ℕ) fun _ => 0).headEq_trans
  universe_decided := (TowerModel.levels (L := ℕ) fun _ => 0).universe_decided

/-- The normalization setting. -/
def setting : Setting Tower.Head ℕ where
  R := rules
  roles := roles
  E := declarative rules
  levels := levels
  shape := shape
  constructors := constructorsDeclared

theorem laws : setting.E.Laws setting.R setting.roles := declarative_laws roles levels

/-! ## Typing of the declared constants -/

section Typing

variable {n : Nat} {Γ : Ctx Tower.Head n}

theorem u0_universe : rules.isUniverse u0 := LevelTower.IsUniverse.sort _

/-- `U0 : U1`. -/
theorem u0_typed : Typed rules Γ (.head u0) (.head (.sort (.succ (.const 0)))) :=
  .headType (LevelTower.HeadTyping.sort _)

theorem u1_universe : rules.isUniverse (.sort (.succ (.const 0))) := LevelTower.IsUniverse.sort _

/-- A closed type of `U0` declared at a name is a type of `U0`. -/
theorem small_typed {name : DeclName} (h : rules.constantType name = some (.head u0)) :
    Typed rules Γ (.const name) (.head u0) :=
  .const h u0_typed u1_universe

theorem ty_typed : Typed rules Γ (.const FamilyExpressions.ty) (.head u0) := small_typed rfl
theorem num_typed : Typed rules Γ (.const FamilyExpressions.num) (.head u0) := small_typed rfl

theorem tnum_typed : Typed rules Γ (.const FamilyExpressions.tnum) (.const FamilyExpressions.ty) :=
  .const (u := u0) rfl ty_typed u0_universe

theorem tbool_typed :
    Typed rules Γ (.const FamilyExpressions.tbool) (.const FamilyExpressions.ty) :=
  .const (u := u0) rfl ty_typed u0_universe

theorem zero_typed : Typed rules Γ (.const FamilyVectors.zero) (.const FamilyExpressions.num) :=
  .const (u := u0) rfl num_typed u0_universe

/-- The declared type of `exp` is typed. -/
theorem expType_typed :
    Typed rules .nil (.pi (.const FamilyExpressions.ty) (.head u0))
      (.head (.sort (.max (.const 0) (.succ (.const 0))))) :=
  .piForm ty_typed u0_universe u0_typed u1_universe (.sorts _ _)

/-- `exp : ty → U0`; the declared type is the declaration's family type. -/
theorem exp_typed :
    Typed rules Γ (.const FamilyExpressions.exp)
      (.pi (.const FamilyExpressions.ty) (.head u0)) :=
  .const (type := .pi (.const FamilyExpressions.ty) (.head u0)) rfl expType_typed (.sort _)

/-- `exp t : U0` for `t : ty`. -/
theorem exp_app_typed {t : Tm Tower.Head n} (typing : Typed rules Γ t (.const FamilyExpressions.ty)) :
    Typed rules Γ (.app (.const FamilyExpressions.exp) t) (.head u0) :=
  .appElim exp_typed typing

/-- The declared type of `lit` is typed. -/
theorem litType_typed :
    Typed rules .nil
      (.pi (.const FamilyExpressions.num)
        (.app (.const FamilyExpressions.exp) (.const FamilyExpressions.tnum)))
      (.head (.sort (.max (.const 0) (.const 0)))) :=
  .piForm num_typed u0_universe (exp_app_typed tnum_typed) u0_universe (.sorts _ _)

/-- `lit : num → exp tnum`; the declared type is the declaration's constructor type. -/
theorem lit_typed :
    Typed rules Γ (.const FamilyExpressions.lit)
      (.pi (.const FamilyExpressions.num)
        (.app (.const FamilyExpressions.exp) (.const FamilyExpressions.tnum))) :=
  .const (type := .pi (.const FamilyExpressions.num)
      (.app (.const FamilyExpressions.exp) (.const FamilyExpressions.tnum))) rfl litType_typed
    (.sort _)

/-- The type of `ite`. -/
abbrev iteType : Tm Tower.Head 0 :=
  .pi (.const FamilyExpressions.ty)
    (.pi (.app (.const FamilyExpressions.exp) (.const FamilyExpressions.tbool))
      (.pi (.app (.const FamilyExpressions.exp) (.var 1))
        (.pi (.app (.const FamilyExpressions.exp) (.var 2))
          (.app (.const FamilyExpressions.exp) (.var 3)))))

theorem iteType_typed :
    Typed rules .nil iteType
      (.head (.sort (.max (.const 0) (.max (.const 0) (.max (.const 0) (.max (.const 0)
        (.const 0))))))) :=
  .piForm ty_typed u0_universe
    (.piForm (exp_app_typed tbool_typed) u0_universe
      (.piForm (exp_app_typed (.var 1)) u0_universe
        (.piForm (exp_app_typed (.var 2)) u0_universe (exp_app_typed (.var 3)) u0_universe
          (.sorts _ _))
        (.sort _) (.sorts _ _))
      (.sort _) (.sorts _ _))
    (.sort _) (.sorts _ _)

/-- `ite : Π (t : ty). exp tbool → exp t → exp t → exp t`; the declared type is the
declaration's constructor type. -/
theorem ite_typed : Typed rules Γ (.const FamilyExpressions.ite) (liftClosed iteType) :=
  .const (type := iteType) rfl iteType_typed (.sort _)

/-- The declared type of `vec` is typed. -/
theorem vecType_typed :
    Typed rules .nil (.pi (.head u0) (.pi (.const FamilyExpressions.num) (.head u0)))
      (.head (.sort (.max (.succ (.const 0)) (.max (.const 0) (.succ (.const 0)))))) :=
  .piForm u0_typed u1_universe
    (.piForm num_typed u0_universe u0_typed u1_universe (.sorts _ _)) (.sort _) (.sorts _ _)

/-- `vec : U0 → num → U0`; the declared type is the declaration's family type. -/
theorem vec_typed :
    Typed rules Γ (.const FamilyVectors.vec)
      (.pi (.head u0) (.pi (.const FamilyExpressions.num) (.head u0))) :=
  .const (type := .pi (.head u0) (.pi (.const FamilyExpressions.num) (.head u0))) rfl
    vecType_typed (.sort _)

/-- The declared type of `vnil` is typed. -/
theorem vnilType_typed :
    Typed rules .nil
      (.pi (.head u0) (.app (.app (.const FamilyVectors.vec) (.var 0)) (.const FamilyVectors.zero)))
      (.head (.sort (.max (.succ (.const 0)) (.const 0)))) := by
  have applied : Typed rules (.snoc .nil (.head u0)) (.app (.const FamilyVectors.vec) (.var 0))
      (.pi (.const FamilyExpressions.num) (.head u0)) := .appElim vec_typed (.var 0)
  have full : Typed rules (.snoc .nil (.head u0))
      (.app (.app (.const FamilyVectors.vec) (.var 0)) (.const FamilyVectors.zero)) (.head u0) :=
    .appElim applied zero_typed
  exact .piForm u0_typed u1_universe full u0_universe (.sorts _ _)

/-- `vnil : Π (A : U0). vec A zero`; the declared type is the declaration's constructor
type. -/
theorem vnil_typed :
    Typed rules Γ (.const FamilyVectors.vnil)
      (.pi (.head u0) (.app (.app (.const FamilyVectors.vec) (.var 0)) (.const FamilyVectors.zero))) :=
  .const (type := .pi (.head u0)
      (.app (.app (.const FamilyVectors.vec) (.var 0)) (.const FamilyVectors.zero))) rfl
    vnilType_typed (.sort _)

end Typing

/-! ## Packs of the index and field types -/

section Packs

variable {n : Nat}

/-- A pack for closed field types, which the simple types here do not have. -/
def noFields : Tm Tower.Head 0 → Pack Tower.Head n := fun _ => ⟨fun _ => False, fun _ => False,
  fun _ _ => False⟩

/-- The packs of the field and index types: `num` and `ty` at their simple inductive packs,
any other type, such as a variable parameter `A`, at the pack of a neutral type. -/
def typePack (Γ : Ctx Tower.Head n) : Tm Tower.Head n → Pack Tower.Head n := fun T =>
  if T = .const FamilyExpressions.num then
    indPack setting Γ FamilyExpressions.num FamilyVectors.numCtors noFields
  else if T = .const FamilyExpressions.ty then
    indPack setting Γ FamilyExpressions.ty FamilyExpressions.tyCtors noFields
  else neutralPack setting Γ T

theorem typePack_var (Γ : Ctx Tower.Head n) (i : Fin n) :
    typePack Γ (.var i) = neutralPack setting Γ (.var i) := rfl

theorem typePack_ty (Γ : Ctx Tower.Head n) :
    typePack Γ (.const FamilyExpressions.ty) =
      indPack setting Γ FamilyExpressions.ty FamilyExpressions.tyCtors noFields := rfl

theorem typePack_num (Γ : Ctx Tower.Head n) :
    typePack Γ (.const FamilyExpressions.num) =
      indPack setting Γ FamilyExpressions.num FamilyVectors.numCtors noFields := rfl

/-- A variable of a simple inductive type is a reducible neutral term of it. -/
theorem var_reducible {Γ : Ctx Tower.Head n} {T : DeclName}
    {cs : List (DeclName × List (Field Tower.Head))} (i : Fin n)
    (typing : Typed rules Γ (.var i) (.const T)) :
    IndRedTm setting Γ T cs noFields (.var i) :=
  .mk (RedTm.refl typing) (.refl typing) (.neutral (.var i) (.refl typing))

/-- A variable of a simple inductive type is reducibly equal to itself. -/
theorem var_self {Γ : Ctx Tower.Head n} {T : DeclName}
    {cs : List (DeclName × List (Field Tower.Head))} (i : Fin n)
    (typing : Typed rules Γ (.var i) (.const T)) :
    IndEqTm setting Γ T cs noFields (.var i) (.var i) :=
  .mk (RedTm.refl typing) (RedTm.refl typing) (.refl typing)
    (.neutral (.var i) (.var i) (.refl typing))

/-- A constructor without fields of a simple inductive type, typed, is reducibly equal to
itself. -/
theorem nullary_self {Γ : Ctx Tower.Head n} {T k : DeclName}
    {cs : List (DeclName × List (Field Tower.Head))} (mem : (k, []) ∈ cs)
    (typing : Typed rules Γ (.const k) (.const T)) :
    IndEqTm setting Γ T cs noFields (.const k) (.const k) :=
  .mk (RedTm.refl typing) (RedTm.refl typing) (.refl typing) (.ctor (args := []) mem .nil)

end Packs

/-! ## Elements -/

/-- The context `x : num`. -/
abbrev numCtx : Ctx Tower.Head 1 := .snoc .nil (.const FamilyExpressions.num)

/-- **A literal is a reducible expression of type `tnum`**: `lit x` for a variable `x : num`. -/
theorem lit_reducible :
    FamRedTm setting numCtx (FamilyExpressions.view setting numCtx u0 (typePack numCtx))
      [.const FamilyExpressions.tnum] (.app (.const FamilyExpressions.lit) (.var 0)) := by
  have typing : Typed rules numCtx (.app (.const FamilyExpressions.lit) (.var 0))
      (.app (.const FamilyExpressions.exp) (.const FamilyExpressions.tnum)) :=
    .appElim lit_typed (.var 0)
  exact .mk (RedTm.refl typing) (.refl typing)
    (FamilyExpressions.lit_canonical_at_tnum (k := .var 0)
      (var_reducible 0 (.var 0))
      (nullary_self (List.mem_cons_self ..) tnum_typed))

/-- The context `t : ty, c : exp tbool, x : exp t, y : exp t`. -/
abbrev iteCtx : Ctx Tower.Head 4 :=
  .snoc (.snoc (.snoc (.snoc .nil (.const FamilyExpressions.ty))
    (.app (.const FamilyExpressions.exp) (.const FamilyExpressions.tbool)))
    (.app (.const FamilyExpressions.exp) (.var 1)))
    (.app (.const FamilyExpressions.exp) (.var 2))

/-- **A conditional is a reducible expression at a variable type**: `ite t c x y : exp t`. -/
theorem ite_reducible_at_variable :
    FamRedTm setting iteCtx (FamilyExpressions.view setting iteCtx u0 (typePack iteCtx))
      [.var 3] (appSpine (.const FamilyExpressions.ite) [.var 3, .var 2, .var 1, .var 0]) := by
  have tVar : Typed rules iteCtx (.var 3) (.const FamilyExpressions.ty) := .var 3
  have cVar : Typed rules iteCtx (.var 2)
      (.app (.const FamilyExpressions.exp) (.const FamilyExpressions.tbool)) := .var 2
  have xVar : Typed rules iteCtx (.var 1) (.app (.const FamilyExpressions.exp) (.var 3)) := .var 1
  have yVar : Typed rules iteCtx (.var 0) (.app (.const FamilyExpressions.exp) (.var 3)) := .var 0
  have typing : Typed rules iteCtx
      (appSpine (.const FamilyExpressions.ite) [.var 3, .var 2, .var 1, .var 0])
      (.app (.const FamilyExpressions.exp) (.var 3)) :=
    .appElim (.appElim (.appElim (.appElim ite_typed tVar) cVar) xVar) yVar
  exact .mk (RedTm.refl typing) (.refl typing)
    (FamilyExpressions.ite_canonical_at_variable (j := 3)
      (var_reducible 3 tVar)
      (FamRedTm.of_neutral laws (.var 2) cVar (.refl cVar))
      (FamRedTm.of_neutral laws (.var 1) xVar (.refl xVar))
      (FamRedTm.of_neutral laws (.var 0) yVar (.refl yVar))
      (var_self 3 tVar))

/-- The context `A : U0`. -/
abbrev typeCtx : Ctx Tower.Head 1 := .snoc .nil (.head u0)

/-- **The empty vector is a reducible vector of length `zero`**: `vnil A` for a variable
`A : U0`. -/
theorem vnil_reducible :
    FamRedTm setting typeCtx (FamilyVectors.view setting typeCtx u0 (typePack typeCtx) (.var 0))
      [.const FamilyVectors.zero] (.app (.const FamilyVectors.vnil) (.var 0)) := by
  have aVar : Typed rules typeCtx (.var 0) (.head u0) := .var 0
  have typing : Typed rules typeCtx (.app (.const FamilyVectors.vnil) (.var 0))
      (.app (.app (.const FamilyVectors.vec) (.var 0)) (.const FamilyVectors.zero)) :=
    .appElim vnil_typed aVar
  exact .mk (RedTm.refl typing) (.refl typing)
    (FamilyVectors.vnil_canonical (A' := .var 0) (.refl aVar)
      (nullary_self (List.mem_cons_self ..) zero_typed))

/-! ## Controls in the same setting -/

/-- The context `t : ty, x : num`. -/
abbrev litCtx : Ctx Tower.Head 2 :=
  .snoc (.snoc .nil (.const FamilyExpressions.ty)) (.const FamilyExpressions.num)

/-- **Negative control: a literal is not an expression at a variable type**, although
`lit x : exp tnum` is (`lit_reducible`). -/
theorem lit_not_reducible_at_variable :
    ¬ FamRedTm setting litCtx (FamilyExpressions.view setting litCtx u0 (typePack litCtx))
      [.var 1] (appSpine (.const FamilyExpressions.lit) [.var 0]) :=
  FamilyExpressions.lit_not_reducible_at_variable (typePack_ty litCtx) roles_tnum roles_tbool
    roles_lit (.var 0)

/-- **At a variable length a vector has no canonical form**, here with a variable `n : num`
in the context `A : U0, n : num`. -/
theorem vector_neutral_at_variable {nf : Tm Tower.Head 2}
    (normal : FamNf setting (.snoc typeCtx (.const FamilyExpressions.num))
      (FamilyVectors.view setting (.snoc typeCtx (.const FamilyExpressions.num)) u0
        (typePack (.snoc typeCtx (.const FamilyExpressions.num))) (.var 1)) [.var 0] nf) :
    Neutral roles nf :=
  FamilyVectors.neutral_at_variable (typePack_num _) roles_zero roles_succ normal

/-- The constructors of the two declarations are declared as constructors under distinct
names, so their constructor forms are rigid. -/
theorem expDecl_declared : (FamilyExpressions.expDecl u0).CtorsDeclared setting where
  role := by
    intro entry mem
    rcases List.mem_cons.mp mem with rfl | mem
    · exact ⟨1, rfl⟩
    rcases List.mem_cons.mp mem with rfl | mem
    · exact ⟨2, rfl⟩
    rcases List.mem_cons.mp mem with rfl | mem
    · exact ⟨4, rfl⟩
    obtain rfl := List.mem_singleton.mp mem
    exact ⟨1, rfl⟩
  distinct := by decide

theorem vecDecl_declared : (FamilyVectors.vecDecl u0).CtorsDeclared setting where
  role := by
    intro entry mem
    rcases List.mem_cons.mp mem with rfl | mem
    · exact ⟨1, rfl⟩
    obtain rfl := List.mem_singleton.mp mem
    exact ⟨4, rfl⟩
  distinct := by decide

end FamilyExamples
end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
