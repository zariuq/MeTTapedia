import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.FamilyExamples

/-!
# The eliminator of vectors in a concrete rule package

In the tower with the declared families of `FamilyExamples`:

* the declared type of the eliminator of vectors is a type (`elimType_isType`), so the
  eliminator is typed at it (`vecElim_typed`); this checks the motive, the two methods and
  the scrutinee of the declared type binder by binder;
* the rule package whose root computation is the eliminator's two rules (`rulesElim`) meets
  the shape obligations of the normalization model (`shapeElim`), and so is a setting
  (`settingElim`) with the declarative equality and its laws (`lawsElim`);
* the rules fire as weak-head steps (`elim_vnil_step`, `elim_vcons_step`);
* an extension `vcons A m x xs` is a reducible vector of length `succ m`
  (`vcons_reducible`), with its element at the pack of the parameter type and its tail at
  the length computed from its fields.

The preservation of typing by the two rules is not proved here: it needs injectivity of the
family former, which the relation's family case will give.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization
namespace FamilyVectorsEliminatorExamples

open Families FamilyExamples FamilyVectorsEliminator

/-! ## Formation helpers -/

section Helpers

variable {n : Nat} {Γ : Ctx Tower.Head n}

theorem isType_of_u0 {A : Tm Tower.Head n} (typing : Typed rules Γ A (.head u0)) :
    IsType rules Γ A :=
  ⟨u0, u0_universe, typing⟩

theorem isType_u0 : IsType rules Γ (.head u0) := ⟨_, u1_universe, u0_typed⟩

theorem isType_pi {A : Tm Tower.Head n} {B : Tm Tower.Head (n + 1)} (domain : IsType rules Γ A)
    (codomain : IsType rules (.snoc Γ A) B) : IsType rules Γ (.pi A B) := by
  obtain ⟨u, hu, tA⟩ := domain
  obtain ⟨v, hv, tB⟩ := codomain
  obtain ⟨w, join⟩ := levels.join_exists hu hv
  exact ⟨w, (levels.join_level join).1, .piForm tA hu tB hv join⟩

/-- `vec A len : U0`. -/
theorem vec_app_typed {A len : Tm Tower.Head n} (hA : Typed rules Γ A (.head u0))
    (hlen : Typed rules Γ len (.const FamilyExpressions.num)) :
    Typed rules Γ (.app (.app (.const FamilyVectors.vec) A) len) (.head u0) := by
  have applied : Typed rules Γ (.app (.const FamilyVectors.vec) A)
      (.pi (.const FamilyExpressions.num) (.head u0)) := .appElim vec_typed hA
  exact .appElim applied hlen

/-- The declared type of `succ` is a type. -/
theorem succType_isType :
    IsType rules .nil (.pi (.const FamilyExpressions.num) (.const FamilyExpressions.num)) :=
  isType_pi (isType_of_u0 num_typed) (isType_of_u0 num_typed)

theorem succ_typed :
    Typed rules Γ (.const FamilyVectors.succ)
      (.pi (.const FamilyExpressions.num) (.const FamilyExpressions.num)) := by
  obtain ⟨u, hu, typing⟩ := succType_isType
  exact .const (type := .pi (.const FamilyExpressions.num) (.const FamilyExpressions.num)) rfl
    typing hu

/-- The declared type of `vcons`: `Π (A : U0) (m : num) (x : A) (xs : vec A m). vec A (succ m)`. -/
abbrev vconsType : Tm Tower.Head 0 :=
  .pi (.head u0) (.pi (.const FamilyExpressions.num) (.pi (.var 1)
    (.pi (.app (.app (.const FamilyVectors.vec) (.var 2)) (.var 1))
      (.app (.app (.const FamilyVectors.vec) (.var 3))
        (.app (.const FamilyVectors.succ) (.var 2))))))

theorem vconsType_isType : IsType rules .nil vconsType := by
  let C1 : Ctx Tower.Head 1 := .snoc .nil (.head u0)
  let C2 : Ctx Tower.Head 2 := .snoc C1 (.const FamilyExpressions.num)
  let C3 : Ctx Tower.Head 3 := .snoc C2 (.var 1)
  let C4 : Ctx Tower.Head 4 := .snoc C3 (.app (.app (.const FamilyVectors.vec) (.var 2)) (.var 1))
  have xs : Typed rules C3 (.app (.app (.const FamilyVectors.vec) (.var 2)) (.var 1)) (.head u0) :=
    vec_app_typed (.var 2) (.var 1)
  have succM : Typed rules C4 (.app (.const FamilyVectors.succ) (.var 2))
      (.const FamilyExpressions.num) := .appElim succ_typed (.var 2)
  have result : Typed rules C4
      (.app (.app (.const FamilyVectors.vec) (.var 3)) (.app (.const FamilyVectors.succ) (.var 2)))
      (.head u0) := vec_app_typed (.var 3) succM
  exact isType_pi isType_u0 (isType_pi (isType_of_u0 num_typed)
    (isType_pi (isType_of_u0 (Γ := C2) (.var 1))
      (isType_pi (isType_of_u0 xs) (isType_of_u0 result))))

/-- `vcons` at its declared type, the declaration's constructor type. -/
theorem vcons_typed : Typed rules Γ (.const FamilyVectors.vcons) (liftClosed vconsType) := by
  obtain ⟨u, hu, typing⟩ := vconsType_isType
  exact .const (type := vconsType) rfl typing hu

end Helpers

/-! ## The declared type of the eliminator is a type -/

/-- The context `A : U0`. -/
abbrev C1 : Ctx Tower.Head 1 := .snoc .nil (.head u0)
/-- `A, P`. -/
abbrev C2 : Ctx Tower.Head 2 := .snoc C1 (FamilyVectorsEliminator.motiveType u0)
/-- `A, P, mn`. -/
abbrev C3 : Ctx Tower.Head 3 := .snoc C2 FamilyVectorsEliminator.nilMethodType
/-- `A, P, mn, m`. -/
abbrev D1 : Ctx Tower.Head 4 := .snoc C3 (.const FamilyExpressions.num)
/-- `A, P, mn, m, x`. -/
abbrev D2 : Ctx Tower.Head 5 := .snoc D1 (.var 3)
/-- `A, P, mn, m, x, xs`. -/
abbrev D3 : Ctx Tower.Head 6 := .snoc D2 (.app (.app (.const FamilyVectors.vec) (.var 4)) (.var 1))
/-- `A, P, mn, m, x, xs, ih`. -/
abbrev D4 : Ctx Tower.Head 7 := .snoc D3 (.app (.app (.var 4) (.var 2)) (.var 0))
/-- `A, P, mn, mc`. -/
abbrev C4 : Ctx Tower.Head 4 := .snoc C3 FamilyVectorsEliminator.consMethodType
/-- `A, P, mn, mc, n`. -/
abbrev C5 : Ctx Tower.Head 5 := .snoc C4 (.const FamilyExpressions.num)
/-- `A, P, mn, mc, n, t`. -/
abbrev C6 : Ctx Tower.Head 6 := .snoc C5 (.app (.app (.const FamilyVectors.vec) (.var 4)) (.var 0))

theorem motiveType_isType : IsType rules C1 (FamilyVectorsEliminator.motiveType u0) := by
  let M1 : Ctx Tower.Head 2 := .snoc C1 (.const FamilyExpressions.num)
  have vecT : Typed rules M1 (.app (.app (.const FamilyVectors.vec) (.var 1)) (.var 0)) (.head u0) :=
    vec_app_typed (.var 1) (.var 0)
  exact isType_pi (isType_of_u0 num_typed) (isType_pi (isType_of_u0 vecT) isType_u0)

theorem nilMethodType_isType : IsType rules C2 FamilyVectorsEliminator.nilMethodType := by
  have motive : Typed rules C2 (.var 0)
      (.pi (.const FamilyExpressions.num)
        (.pi (.app (.app (.const FamilyVectors.vec) (.var 2)) (.var 0)) (.head u0))) := .var 0
  have atZero : Typed rules C2 (.app (.var 0) (.const FamilyVectors.zero))
      (.pi (.app (.app (.const FamilyVectors.vec) (.var 1)) (.const FamilyVectors.zero))
        (.head u0)) := .appElim motive zero_typed
  have empty : Typed rules C2 (.app (.const FamilyVectors.vnil) (.var 1))
      (.app (.app (.const FamilyVectors.vec) (.var 1)) (.const FamilyVectors.zero)) :=
    .appElim vnil_typed (.var 1)
  exact isType_of_u0 (.appElim atZero empty)

theorem consMethodType_isType : IsType rules C3 FamilyVectorsEliminator.consMethodType := by
  have xsT : Typed rules D2 (.app (.app (.const FamilyVectors.vec) (.var 4)) (.var 1)) (.head u0) :=
    vec_app_typed (.var 4) (.var 1)
  have motive3 : Typed rules D3 (.var 4)
      (.pi (.const FamilyExpressions.num)
        (.pi (.app (.app (.const FamilyVectors.vec) (.var 6)) (.var 0)) (.head u0))) := .var 4
  have ihHead : Typed rules D3 (.app (.var 4) (.var 2))
      (.pi (.app (.app (.const FamilyVectors.vec) (.var 5)) (.var 2)) (.head u0)) :=
    .appElim motive3 (.var 2)
  have ihT : Typed rules D3 (.app (.app (.var 4) (.var 2)) (.var 0)) (.head u0) :=
    .appElim ihHead (.var 0)
  have motive4 : Typed rules D4 (.var 5)
      (.pi (.const FamilyExpressions.num)
        (.pi (.app (.app (.const FamilyVectors.vec) (.var 7)) (.var 0)) (.head u0))) := .var 5
  have succM : Typed rules D4 (.app (.const FamilyVectors.succ) (.var 3))
      (.const FamilyExpressions.num) := .appElim succ_typed (.var 3)
  have goalHead : Typed rules D4 (.app (.var 5) (.app (.const FamilyVectors.succ) (.var 3)))
      (.pi (.app (.app (.const FamilyVectors.vec) (.var 6)) (.app (.const FamilyVectors.succ) (.var 3)))
        (.head u0)) := .appElim motive4 succM
  have v1 : Typed rules D4 (.app (.const FamilyVectors.vcons) (.var 6))
      (.pi (.const FamilyExpressions.num) (.pi (.var 7)
        (.pi (.app (.app (.const FamilyVectors.vec) (.var 8)) (.var 1))
          (.app (.app (.const FamilyVectors.vec) (.var 9))
            (.app (.const FamilyVectors.succ) (.var 2)))))) := .appElim vcons_typed (.var 6)
  have v2 : Typed rules D4 (.app (.app (.const FamilyVectors.vcons) (.var 6)) (.var 3))
      (.pi (.var 6) (.pi (.app (.app (.const FamilyVectors.vec) (.var 7)) (.var 4))
        (.app (.app (.const FamilyVectors.vec) (.var 8)) (.app (.const FamilyVectors.succ) (.var 5)))))
      := .appElim v1 (.var 3)
  have v3 : Typed rules D4 (.app (.app (.app (.const FamilyVectors.vcons) (.var 6)) (.var 3)) (.var 2))
      (.pi (.app (.app (.const FamilyVectors.vec) (.var 6)) (.var 3))
        (.app (.app (.const FamilyVectors.vec) (.var 7)) (.app (.const FamilyVectors.succ) (.var 4))))
      := .appElim v2 (.var 2)
  have v4 : Typed rules D4 (appSpine (.const FamilyVectors.vcons) [.var 6, .var 3, .var 2, .var 1])
      (.app (.app (.const FamilyVectors.vec) (.var 6)) (.app (.const FamilyVectors.succ) (.var 3))) :=
    .appElim v3 (.var 1)
  have result : Typed rules D4
      (.app (.app (.var 5) (.app (.const FamilyVectors.succ) (.var 3)))
        (appSpine (.const FamilyVectors.vcons) [.var 6, .var 3, .var 2, .var 1])) (.head u0) :=
    .appElim goalHead v4
  exact isType_pi (isType_of_u0 num_typed)
    (isType_pi (isType_of_u0 (Γ := D1) (.var 3))
      (isType_pi (isType_of_u0 xsT) (isType_pi (isType_of_u0 ihT) (isType_of_u0 result))))

/-- **The declared type of the eliminator of vectors is a type.** -/
theorem elimType_isType : IsType rules .nil (FamilyVectorsEliminator.elimType u0 u0) := by
  have vecNT : Typed rules C5 (.app (.app (.const FamilyVectors.vec) (.var 4)) (.var 0)) (.head u0) :=
    vec_app_typed (.var 4) (.var 0)
  have motive6 : Typed rules C6 (.var 4)
      (.pi (.const FamilyExpressions.num)
        (.pi (.app (.app (.const FamilyVectors.vec) (.var 6)) (.var 0)) (.head u0))) := .var 4
  have atN : Typed rules C6 (.app (.var 4) (.var 1))
      (.pi (.app (.app (.const FamilyVectors.vec) (.var 5)) (.var 1)) (.head u0)) :=
    .appElim motive6 (.var 1)
  have result : Typed rules C6 (.app (.app (.var 4) (.var 1)) (.var 0)) (.head u0) :=
    .appElim atN (.var 0)
  exact isType_pi isType_u0 (isType_pi motiveType_isType (isType_pi nilMethodType_isType
    (isType_pi consMethodType_isType (isType_pi (isType_of_u0 num_typed)
      (isType_pi (isType_of_u0 vecNT) (isType_of_u0 result))))))

/-- The eliminator at its declared type. -/
theorem vecElim_typed {n : Nat} {Γ : Ctx Tower.Head n} :
    Typed rules Γ (.const vecElim) (liftClosed (FamilyVectorsEliminator.elimType u0 u0)) := by
  obtain ⟨u, hu, typing⟩ := elimType_isType
  exact .const rfl typing hu

/-! ## The rule package with the eliminator's rules -/

/-- The package with the eliminator's two rules as its root computation. -/
def rulesElim : Rules Tower.Head := { rules with computation := vecIota }

theorem shapeElim : RootShape rulesElim roles where
  spine := fun step => vecIota_spine roles_vecElim roles_vnil roles_vcons step
  deterministic := fun step step' => vecIota_deterministic step step'

/-- The tower's level model, for the package with the eliminator's rules. -/
def levelsElim : LevelModel rulesElim ℕ where
  level := levels.level
  successor := levels.successor
  universe_typing := levels.universe_typing
  ground_typing := levels.ground_typing
  cumulative_universe := levels.cumulative_universe
  headEq_level := levels.headEq_level
  join_level := levels.join_level
  join_exists := levels.join_exists
  join_upper := levels.join_upper
  cumulative_refl := levels.cumulative_refl
  headEq_symm := levels.headEq_symm
  headEq_trans := levels.headEq_trans
  universe_decided := levels.universe_decided

/-- **The package with the eliminator's rules is a setting of the normalization model.** -/
def settingElim : Setting Tower.Head ℕ where
  R := rulesElim
  roles := roles
  E := declarative rulesElim
  levels := levelsElim
  shape := shapeElim
  constructors := constructorsDeclared

theorem lawsElim : settingElim.E.Laws settingElim.R settingElim.roles :=
  declarative_laws roles levelsElim

/-- **The rule at the empty vector fires**: `vec-elim A P mn mc n (vnil A') ⟶ mn` is a
weak-head step of the package. -/
theorem elim_vnil_step {n : Nat} (A P mn mc len A' : Tm Tower.Head n) :
    WhStep rulesElim roles
      (appSpine (.const vecElim) [A, P, mn, mc, len, .app (.const FamilyVectors.vnil) A']) mn :=
  .root (VecIota.vnil A P mn mc len A')

/-- **The rule at an extension fires**: it unfolds to the method at the fields and the
recursive call. -/
theorem elim_vcons_step {n : Nat} (A P mn mc len A' m x xs : Tm Tower.Head n) :
    WhStep rulesElim roles
      (appSpine (.const vecElim)
        [A, P, mn, mc, len, appSpine (.const FamilyVectors.vcons) [A', m, x, xs]])
      (appSpine mc [m, x, xs, appSpine (.const vecElim) [A, P, mn, mc, m, xs]]) :=
  .root (VecIota.vcons A P mn mc len A' m x xs)

/-! ## An extension is a reducible vector -/

/-- The context `A : U0, m : num, x : A, xs : vec A m`. -/
abbrev consCtx : Ctx Tower.Head 4 :=
  .snoc (.snoc (.snoc (.snoc .nil (.head u0)) (.const FamilyExpressions.num)) (.var 1))
    (.app (.app (.const FamilyVectors.vec) (.var 2)) (.var 1))

/-- **An extension is a reducible vector of a successor length**: `vcons A m x xs` at
`vec A (succ m)`, its fields a number, an element of the parameter type, and a vector at
the index `m` computed from the fields. -/
theorem vcons_reducible :
    FamRedTm setting consCtx (FamilyVectors.view setting consCtx u0 (typePack consCtx) (.var 3))
      [.app (.const FamilyVectors.succ) (.var 2)]
      (appSpine (.const FamilyVectors.vcons) [.var 3, .var 2, .var 1, .var 0]) := by
  have aVar : Typed rules consCtx (.var 3) (.head u0) := .var 3
  have mVar : Typed rules consCtx (.var 2) (.const FamilyExpressions.num) := .var 2
  have xVar : Typed rules consCtx (.var 1) (.var 3) := .var 1
  have xsVar : Typed rules consCtx (.var 0)
      (.app (.app (.const FamilyVectors.vec) (.var 3)) (.var 2)) := .var 0
  have succM : Typed rules consCtx (.app (.const FamilyVectors.succ) (.var 2))
      (.const FamilyExpressions.num) := .appElim succ_typed mVar
  have v1 : Typed rules consCtx (.app (.const FamilyVectors.vcons) (.var 3))
      (.pi (.const FamilyExpressions.num) (.pi (.var 4)
        (.pi (.app (.app (.const FamilyVectors.vec) (.var 5)) (.var 1))
          (.app (.app (.const FamilyVectors.vec) (.var 6))
            (.app (.const FamilyVectors.succ) (.var 2)))))) := .appElim vcons_typed aVar
  have v2 : Typed rules consCtx (.app (.app (.const FamilyVectors.vcons) (.var 3)) (.var 2))
      (.pi (.var 3) (.pi (.app (.app (.const FamilyVectors.vec) (.var 4)) (.var 3))
        (.app (.app (.const FamilyVectors.vec) (.var 5)) (.app (.const FamilyVectors.succ) (.var 4)))))
      := .appElim v1 mVar
  have v3 : Typed rules consCtx
      (.app (.app (.app (.const FamilyVectors.vcons) (.var 3)) (.var 2)) (.var 1))
      (.pi (.app (.app (.const FamilyVectors.vec) (.var 3)) (.var 2))
        (.app (.app (.const FamilyVectors.vec) (.var 4)) (.app (.const FamilyVectors.succ) (.var 3))))
      := .appElim v2 xVar
  have typing : Typed rules consCtx
      (appSpine (.const FamilyVectors.vcons) [.var 3, .var 2, .var 1, .var 0])
      (.app (.app (.const FamilyVectors.vec) (.var 3)) (.app (.const FamilyVectors.succ) (.var 2))) :=
    .appElim v3 xsVar
  have lengths : IndEqTm setting consCtx FamilyExpressions.num FamilyVectors.numCtors noFields
      (.app (.const FamilyVectors.succ) (.var 2)) (.app (.const FamilyVectors.succ) (.var 2)) :=
    .mk (RedTm.refl succM) (RedTm.refl succM) (.refl succM)
      (.ctor (args := [.var 2]) (List.mem_cons_of_mem _ (List.mem_singleton_self _))
        (.recursive (var_self 2 mVar) .nil))
  have elem : (typePack consCtx (.var 3)).redTm (.var 1) :=
    ⟨.var 1, RedTm.refl xVar, .var 1, .refl xVar⟩
  exact .mk (RedTm.refl typing) (.refl typing)
    (FamilyVectors.vcons_canonical (A' := .var 3) (.refl aVar) (var_reducible 2 mVar) elem
      (FamRedTm.of_neutral laws (.var 0) xsVar (.refl xsVar)) lengths)

end FamilyVectorsEliminatorExamples
end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
