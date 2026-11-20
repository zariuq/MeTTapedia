import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes.Agreement
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerSyntaxLimit

/-!
# Canonicity for the model's numbers, and the type in the knowledge as a whole

The normalization model gives every typed term a reducible form: at an inductive type, a reduction to
a constructor applied to reducible arguments, or to a neutral term (`IndRedTm`, `IndNf`). What it does
not state is that the neutral case is empty for closed terms. It is, for the tower with addition:

* **A closed neutral term mentions a rigid constant** (`neutral_mentions_rigid`): its head is a
  variable, which a closed term lacks, or a rigid constant, possibly under eliminations and stuck
  computations, whose inspected argument is a part of its arguments (`constFree_of_focus`).
* **A rigid constant of the package is undeclared** (`undeclared_of_rigid`), and an undeclared
  constant occurs in no derivable judgment (`TowerSyntaxLimit.free_of_undeclared`).

So **every closed term typed at `num` is equal to exactly one numeral** (`canonicity`,
`canonicity_unique`), and the agreement extends from the canonical terms to the whole type: **every
closed term of the model's numbers is equal to the reading of exactly one generated row**
(`closed_term_has_row`), and **the step's addition answers, on the rows of any two closed terms of
`num`, the numeral the model's addition of those terms equals** (`answer_agrees_closed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes

open WhenTypesApply.ThatsAll
open NamesOnTheStep NamesOnTheStep.IssuingControls
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality Normalization
open TowerNumbersModel (num zero succ numRec ctors u mem_zero mem_succ)
open TowerArithmeticModel (add)
open TowerSyntaxLimit (free_of_undeclared)

namespace Agreement

/-! ## Closed neutral terms mention a rigid constant -/

theorem constFree_appSpine {f : DeclName} {n : Nat} :
    ∀ (g : Tm Tower.Head n) (args : List (Tm Tower.Head n)),
      ConstFree f (appSpine g args) ↔ ConstFree f g ∧ ∀ a ∈ args, ConstFree f a
  | g, [] => by simp [appSpine]
  | g, a :: args => by
      rw [show appSpine g (a :: args) = appSpine (.app g a) args from rfl,
        constFree_appSpine (.app g a) args]
      simp only [ConstFree, List.mem_cons, forall_eq_or_imp]
      exact and_assoc

/-- The value an inspection focuses on is a part of the inspected values. -/
theorem constFree_of_focus {f : DeclName} {roles : Roles Tower.Head} {n : Nat} {tree : InspectTree}
    {values values' : List (Tm Tower.Head n)} {kind : Inspection} {a a' : Tm Tower.Head n}
    (focus : tree.Focus roles values values' kind a a') :
    (∀ v ∈ values, ConstFree f v) → ConstFree f a := by
  induction focus with
  | here _ => exact fun all => all _ (List.mem_append_right _ (List.mem_cons_self ..))
  | @constructor position next before after fields before' after' fields' value value' key kind a a'
      _ _ _ view _ _ ih =>
      intro all
      apply ih
      intro v member
      rcases List.mem_append.mp member with member | inAfter
      · rcases List.mem_append.mp member with inBefore | inFields
        · exact all v (List.mem_append_left _ inBefore)
        · have valueFree := all value (List.mem_append_right _ (List.mem_cons_self ..))
          cases view with
          | spine args _ => exact ((constFree_appSpine _ _).mp valueFree).2 v inFields
          | refl x =>
              rw [List.mem_singleton.mp inFields]
              exact valueFree
      · exact all v (List.mem_append_right _ (List.mem_cons_of_mem _ inAfter))
  | headForm _ _ _ ih => exact ih

/-- **A closed neutral term mentions a rigid constant.** -/
theorem neutral_mentions_rigid {roles : Roles Tower.Head} {n : Nat} {t : Tm Tower.Head n}
    (neutral : Neutral roles t) : n = 0 → ∃ c, roles c = .rigid ∧ ¬ ConstFree c t := by
  induction neutral with
  | var i =>
      intro closed
      subst closed
      exact i.elim0
  | app _ ih =>
      intro closed
      obtain ⟨c, rigid, notFree⟩ := ih closed
      exact ⟨c, rigid, fun free => notFree free.1⟩
  | fst _ ih =>
      intro closed
      obtain ⟨c, rigid, notFree⟩ := ih closed
      exact ⟨c, rigid, fun free => notFree free⟩
  | snd _ ih =>
      intro closed
      obtain ⟨c, rigid, notFree⟩ := ih closed
      exact ⟨c, rigid, fun free => notFree free⟩
  | @rigid c args role =>
      intro _
      exact ⟨c, role, fun free => ((constFree_appSpine _ _).mp free).1 rfl⟩
  | stuck _ _ focus _ _ ih =>
      intro closed
      obtain ⟨c, rigid, notFree⟩ := ih closed
      exact ⟨c, rigid, fun free => notFree (constFree_of_focus focus ((constFree_appSpine _ _).mp free).2)⟩

variable (lv : LevelExpr Nat)

/-- **A rigid constant of the tower with addition is undeclared.** -/
theorem undeclared_of_rigid {c : DeclName} (rigid : TowerArithmeticModel.roles c = .rigid) :
    (TowerArithmeticModel.rules lv).constantType c = none := by
  by_cases hadd : c = add
  · subst hadd
    rw [TowerArithmeticModel.roles_add] at rigid
    cases rigid
  by_cases hnum : c = num
  · subst hnum
    rw [TowerArithmeticModel.roles_num] at rigid
    cases rigid
  by_cases hrec : c = numRec
  · subst hrec
    rw [TowerArithmeticModel.roles_numRec] at rigid
    cases rigid
  by_cases hzero : c = zero
  · subst hzero
    simp [TowerArithmeticModel.roles, TowerArithmeticModel.zero_ne_add,
      TowerNumbersModel.roles_zero] at rigid
  by_cases hsucc : c = succ
  · subst hsucc
    simp [TowerArithmeticModel.roles, TowerArithmeticModel.succ_ne_add,
      TowerNumbersModel.roles_succ] at rigid
  rw [TowerArithmeticModel.constantType_ne_add lv hadd]
  simp [TowerNumbersModel.rules, TowerNumbersModel.constantType, hnum, hzero, hsucc, hrec]

/-! ## Canonicity -/

/-- The constructors of the numbers have no closed fields. -/
theorem ctors_no_closed {k : DeclName} {fields : List (Normalization.Field Tower.Head)}
    (mem : (k, fields) ∈ ctors) : ∀ F, Normalization.Field.closed F ∉ fields := by
  simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
  rcases mem with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp

mutual

theorem canonical_of_redTm {fieldPack : Tm Tower.Head 0 → Pack Tower.Head 0} :
    ∀ {t : Tm Tower.Head 0},
      IndRedTm (TowerArithmeticModel.setting lv fun _ => 0) .nil num ctors fieldPack t →
        ∃ k, Equal (TowerArithmeticModel.rules lv) .nil t (numTm k) (.const num)
  | _, .mk red _ normal => by
      obtain ⟨k, equal⟩ := canonical_of_nf normal
      exact ⟨k, .trans red.equal equal⟩

theorem canonical_of_nf {fieldPack : Tm Tower.Head 0 → Pack Tower.Head 0} :
    ∀ {nf : Tm Tower.Head 0},
      IndNf (TowerArithmeticModel.setting lv fun _ => 0) .nil num ctors fieldPack nf →
        ∃ k, Equal (TowerArithmeticModel.rules lv) .nil nf (numTm k) (.const num)
  | _, .ctor mem arguments => by
      have each := canonical_of_fields arguments (ctors_no_closed mem)
      simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · cases arguments
        exact ⟨0, .refl (zero_typed lv)⟩
      · cases arguments with
        | recursive head tail =>
            cases tail
            obtain ⟨k, equal⟩ := each _ (List.mem_singleton_self _)
            exact ⟨k + 1, .appCong (.refl (succ_typed lv)) equal⟩
  | _, .neutral neutral conv => by
      exfalso
      obtain ⟨c, rigid, notFree⟩ := neutral_mentions_rigid neutral rfl
      exact notFree (free_of_undeclared (undeclared_of_rigid lv rigid) conv).1

theorem canonical_of_fields {fieldPack : Tm Tower.Head 0 → Pack Tower.Head 0} :
    ∀ {fields : List (Normalization.Field Tower.Head)} {args : List (Tm Tower.Head 0)},
      IndFields (TowerArithmeticModel.setting lv fun _ => 0) .nil num ctors fieldPack fields args →
        (∀ F, Normalization.Field.closed F ∉ fields) →
          ∀ a ∈ args, ∃ k, Equal (TowerArithmeticModel.rules lv) .nil a (numTm k) (.const num)
  | _, _, .nil, _ => fun _ member => absurd member List.not_mem_nil
  | _, _, .recursive head tail, noClosed => by
      have first := canonical_of_redTm head
      have rest := canonical_of_fields tail fun F inTail => noClosed F (List.mem_cons_of_mem _ inTail)
      intro a member
      rcases List.mem_cons.mp member with rfl | later
      · exact first
      · exact rest a later
  | _, _, .closed _ _, noClosed => absurd (List.mem_cons_self ..) (noClosed _)

end

/-- **Canonicity**: every closed term typed at `num` is equal to a numeral. -/
theorem canonicity {t : Tm Tower.Head 0}
    (typing : Typed (TowerArithmeticModel.rules lv) .nil t (.const num)) :
    ∃ k, Equal (TowerArithmeticModel.rules lv) .nil t (numTm k) (.const num) := by
  obtain ⟨r, h⟩ := Typed.reducible (S := TowerArithmeticModel.setting lv fun _ => 0)
    (TowerArithmeticModel.laws lv _) (TowerArithmeticModel.constants lv _) typing CtxFormed.nil
  obtain ⟨fieldPack, same, -⟩ :=
    Reducible.inductive_view (TowerArithmeticModel.setting_roles_num lv _) r
  rw [same] at h
  exact canonical_of_redTm lv h

/-- **To exactly one numeral.** -/
theorem canonicity_unique {t : Tm Tower.Head 0}
    (typing : Typed (TowerArithmeticModel.rules lv) .nil t (.const num)) :
    ∃! k, Equal (TowerArithmeticModel.rules lv) .nil t (numTm k) (.const num) := by
  obtain ⟨k, equal⟩ := canonicity lv typing
  exact ⟨k, equal, fun j equal' => numTm_equal lv (.trans (.symm equal') equal)⟩

/-! ## The type in the knowledge as a whole -/

/-- **Every closed term of the model's numbers is equal to the reading of exactly one generated
row.** -/
theorem closed_term_has_row {t : Tm Tower.Head 0}
    (typing : Typed (TowerArithmeticModel.rules lv) .nil t (.const num)) :
    ∃! e, Generated natRules ∅ (natRow e) ∧
      ∃ t', toModel e = some t' ∧ Equal (TowerArithmeticModel.rules lv) .nil t t' (.const num) := by
  obtain ⟨k, equal⟩ := canonicity lv typing
  refine ⟨numeral k, ⟨Numbers.numeral_generated k, numTm k, toModel_numeral k, equal⟩, ?_⟩
  rintro e ⟨-, t', read, equal'⟩
  obtain ⟨j, rfl, rfl⟩ := toModel_eq_some read
  rw [numTm_equal lv (.trans (.symm equal') equal)]

/-- **The step's addition computes the model's addition on any two closed terms of `num`**: their rows
exist, and for a request on them every final state's answer reads as the numeral that the model's
addition of the two terms equals, and as no other numeral. -/
theorem answer_agrees_closed {a b : Tm Tower.Head 0}
    (ta : Typed (TowerArithmeticModel.rules lv) .nil a (.const num))
    (tb : Typed (TowerArithmeticModel.rules lv) .nil b (.const num)) :
    ∃ x y, Generated natRules ∅ (natRow x) ∧ Generated natRules ∅ (natRow y) ∧
      ∀ C, Recursion.Request x y C →
        ∀ C', Relation.ReflTransGen Recursion.addStep C C' → (∀ C'', ¬ Recursion.addStep C' C'') →
          ∃ v t, outE v ∈ contents C' ∧ toModel v = some t ∧
            Equal (TowerArithmeticModel.rules lv) .nil (addTm a b) t (.const num) ∧
            ∀ k, Equal (TowerArithmeticModel.rules lv) .nil (addTm a b) (numTm k) (.const num) →
              t = numTm k := by
  obtain ⟨i, ei⟩ := canonicity lv ta
  obtain ⟨j, ej⟩ := canonicity lv tb
  refine ⟨numeral i, numeral j, Numbers.numeral_generated i, Numbers.numeral_generated j,
    fun C request C' run stops => ?_⟩
  obtain ⟨_, _, ra, rb, answers⟩ :=
    answer_agrees lv (Numbers.numeral_generated i) (Numbers.numeral_generated j) request
  rw [toModel_numeral] at ra rb
  cases ra
  cases rb
  obtain ⟨v, t, present, read, canonical, equal, _⟩ := answers C' run stops
  have congruent : Equal (TowerArithmeticModel.rules lv) .nil (addTm a b) (addTm (numTm i) (numTm j))
      (.const num) :=
    .appCong (.appCong (.refl (add_typed lv)) ei) ej
  refine ⟨v, t, present, read, .trans congruent equal, fun k equal' => ?_⟩
  obtain ⟨m, rfl⟩ := (closedCanonical_iff lv).mp canonical
  rw [numTm_equal lv (.trans (.symm (.trans congruent equal)) equal')]

end Agreement

#print axioms Agreement.neutral_mentions_rigid
#print axioms Agreement.undeclared_of_rigid
#print axioms Agreement.canonicity
#print axioms Agreement.canonicity_unique
#print axioms Agreement.closed_term_has_row
#print axioms Agreement.answer_agrees_closed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes
