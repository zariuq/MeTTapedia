import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes.Canonicity

/-!
# Agreement with the model against a total reading of contents

`Agreement.generated_iff_closedCanonical` reads a content into the model by `Agreement.toModel`,
which is defined on numerals only, so that agreement holds by the reading's construction. Here the
reading is total and compositional: `translate` sends every content, junk included, to a closed raw
term of the model, symbol by symbol, and application to application. The symbols the step shares
with the model are read as its constants (`zeroE` as `zero`, the successor symbol as `succ`, the
request symbol of the addition program as `add`); every other symbol, every generative name and the
code former are read as constants the model does not declare. Whether the translation of a content
is typed, and whether it is canonical, are then questions about the model, answered by its typing
and its constructor roles.

* **Agreement** (`generated_iff_translate`): a row of the number region is generated exactly when
  the translation of its content is typed at `num` in the empty context and is in canonical form all
  the way down (`CanonicalForm`: a constructor spine of the model's roles, or reflexivity, whose
  fields are in canonical form). The backward direction uses canonicity of the model's numbers
  (`Agreement.canonicity`) and injectivity and discrimination of its constructors
  (`numeral_of_canonical`).
* **Each condition is needed, and the reading meets terms off the numerals** (none of these rows is
  generated):
  * `junk_untranslatable`: the translation of `junkE` is typed at no type and is not in canonical
    form;
  * `overApplied_canonical`, `overApplied_untyped`: `zero` applied to `zero` is in canonical form,
    since the roles do not count arguments, and is not typed at `num`;
  * `request_typed_not_canonical`: the request `askAdd zeroE zeroE` translates to `add zero zero`,
    typed at `num` and equal there to the numeral `0`, and not in canonical form.
* `generated_iff_closedCanonical_translate`: with the total reading in place of the partial one, the
  membership agreement of `Agreement` holds as stated there; the two readings agree where the partial
  one is defined (`translate_of_toModel`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes.Translation

open WhenTypesApply.ThatsAll
open NamesOnTheStep
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality Normalization
open TowerNumbersModel (num zero succ numRec ctors mem_zero mem_succ)
open TowerArithmeticModel (add)
open TowerSyntaxLimit (free_of_undeclared)
open Agreement (numTm numTm_typed ClosedCanonicalNum closedCanonical_iff canonicity addTm addTm_typed
  add_numerals toModel toModel_eq_some)

/-! ## The total reading -/

/-- The model's constant for a symbol of the step that is not one of the model's constants. -/
def symName (k : ℕ) : DeclName := .mkNum (.mkSimple "sym") k

/-- The model's constant for a generative name. -/
def nameName (n : ℕ) : DeclName := .mkNum (.mkSimple "name") n

/-- The model's constant for the structural code former. -/
def codeName : DeclName := .mkSimple "code"

/-- **A symbol of the step, read in the model**: zero, the successor and the request for a sum are the
model's `zero`, `succ` and `add`; every other symbol is a constant of its own. -/
def symbol (k : ℕ) : Tm Tower.Head 0 :=
  if k = 100 then .const zero
  else if k = 101 then .const succ
  else if k = 130 then .const add
  else .const (symName k)

/-- **The total translation of contents into closed raw terms of the model**, by recursion on the
content. -/
def translate : Expr → Tm Tower.Head 0
  | .sym k => symbol k
  | .app f a => .app (translate f) (translate a)
  | .name n => .const (nameName n)
  | .code e => .app (.const codeName) (translate e)

theorem symName_ne {k : ℕ} {c : DeclName} (simple : ∃ s, c = .mkSimple s) : symName k ≠ c := by
  obtain ⟨s, rfl⟩ := simple
  intro same
  cases same

theorem nameName_ne {n : ℕ} {c : DeclName} (simple : ∃ s, c = .mkSimple s) : nameName n ≠ c := by
  obtain ⟨s, rfl⟩ := simple
  intro same
  cases same

/-- **Reading the constant `zero` back**: only `zeroE` translates to it. -/
theorem translate_eq_zero {e : Expr} (same : translate e = .const zero) : e = zeroE := by
  cases e with
  | sym k =>
      change symbol k = .const zero at same
      unfold symbol at same
      split_ifs at same with h100 h101 h130
      · rw [h100]
        rfl
      · exact absurd (Tm.const.inj same) TowerNumbersModel.zero_ne_succ.symm
      · exact absurd (Tm.const.inj same) TowerArithmeticModel.zero_ne_add.symm
      · exact absurd (Tm.const.inj same) (symName_ne ⟨_, rfl⟩)
  | app f a => cases same
  | name n => exact absurd (Tm.const.inj same) (nameName_ne ⟨_, rfl⟩)
  | code e => cases same

/-- **Reading the constant `succ` back**: only the successor symbol translates to it. -/
theorem translate_eq_succ {e : Expr} (same : translate e = .const succ) : e = .sym 101 := by
  cases e with
  | sym k =>
      change symbol k = .const succ at same
      unfold symbol at same
      split_ifs at same with h100 h101 h130
      · exact absurd (Tm.const.inj same) TowerNumbersModel.zero_ne_succ
      · rw [h101]
      · exact absurd (Tm.const.inj same) TowerArithmeticModel.succ_ne_add.symm
      · exact absurd (Tm.const.inj same) (symName_ne ⟨_, rfl⟩)
  | app f a => cases same
  | name n => exact absurd (Tm.const.inj same) (nameName_ne ⟨_, rfl⟩)
  | code e => cases same

/-- **Reading an application of `succ` back**: only a successor content translates to it. -/
theorem translate_eq_succ_app {e : Expr} {a : Tm Tower.Head 0}
    (same : translate e = .app (.const succ) a) : ∃ x, e = succE x ∧ translate x = a := by
  cases e with
  | sym k =>
      change symbol k = .app (.const succ) a at same
      unfold symbol at same
      split_ifs at same
  | app f x =>
      obtain ⟨head, argument⟩ := Tm.app.inj same
      exact ⟨x, by rw [translate_eq_succ head]; rfl, argument⟩
  | name n => cases same
  | code x =>
      obtain ⟨head, -⟩ := Tm.app.inj same
      exact absurd (Tm.const.inj head) (by decide)

/-- The translation never yields reflexivity. -/
theorem translate_ne_refl (e : Expr) (x : Tm Tower.Head 0) : translate e ≠ .refl x := by
  cases e with
  | sym k =>
      change symbol k ≠ .refl x
      unfold symbol
      split_ifs <;> exact fun same => by cases same
  | app f a => exact fun same => by cases same
  | name n => exact fun same => by cases same
  | code e => exact fun same => by cases same

/-- **On numerals the translation is the model's numeral.** -/
theorem translate_numeral : ∀ k : ℕ, translate (numeral k) = numTm k
  | 0 => rfl
  | k + 1 => by
      show Tm.app (symbol 101) (translate (numeral k)) = .app (.const succ) (numTm k)
      rw [translate_numeral k]
      rfl

/-- **Only numerals translate to numerals.** -/
theorem translate_numTm (k : ℕ) : ∀ {e : Expr}, translate e = numTm k → e = numeral k := by
  induction k with
  | zero =>
      intro e same
      exact translate_eq_zero same
  | succ k ih =>
      intro e same
      obtain ⟨x, rfl, inner⟩ := translate_eq_succ_app same
      rw [ih inner]
      rfl

/-- **The two readings agree where the partial one is defined.** -/
theorem translate_of_toModel {e : Expr} {t : Tm Tower.Head 0} (read : toModel e = some t) :
    translate e = t := by
  obtain ⟨k, rfl, rfl⟩ := toModel_eq_some read
  exact translate_numeral k

/-! ## Canonical forms by the model's roles -/

/-- **In canonical form all the way down**, by the model's constructor view: a constructor spine of
the model's roles, or reflexivity, whose fields are in canonical form all the way down. The roles do
not count a constructor's arguments. -/
inductive CanonicalForm : Tm Tower.Head 0 → Prop
  | view {t : Tm Tower.Head 0} {key : InspectKey} {fields : List (Tm Tower.Head 0)} :
      ConstructorView TowerArithmeticModel.roles t key fields → (∀ a ∈ fields, CanonicalForm a) →
      CanonicalForm t

theorem roles_zero : TowerArithmeticModel.roles zero = .constructor 0 := by
  simp [TowerArithmeticModel.roles, TowerArithmeticModel.zero_ne_add, TowerNumbersModel.roles_zero]

theorem roles_succ : TowerArithmeticModel.roles succ = .constructor 1 := by
  simp [TowerArithmeticModel.roles, TowerArithmeticModel.succ_ne_add, TowerNumbersModel.roles_succ]

/-- The constructors of the model are `zero` and `succ`. -/
theorem roles_constructor {c : DeclName} {arity : Nat}
    (role : TowerArithmeticModel.roles c = .constructor arity) : c = zero ∨ c = succ := by
  by_cases hadd : c = add
  · subst hadd
    rw [TowerArithmeticModel.roles_add] at role
    cases role
  by_cases hnum : c = num
  · subst hnum
    rw [TowerArithmeticModel.roles_num] at role
    cases role
  by_cases hrec : c = numRec
  · subst hrec
    rw [TowerArithmeticModel.roles_numRec] at role
    cases role
  by_cases hzero : c = zero
  · exact Or.inl hzero
  by_cases hsucc : c = succ
  · exact Or.inr hsucc
  exfalso
  have rigid : TowerArithmeticModel.roles c = .rigid := by
    simp [TowerArithmeticModel.roles, hadd, TowerNumbersModel.roles, hnum, hzero, hsucc, hrec]
  rw [rigid] at role
  cases role

/-- A constructor view of a constant spine has the spine's arguments as its fields. -/
theorem view_fields {t : Tm Tower.Head 0} {key : InspectKey} {fields : List (Tm Tower.Head 0)}
    (view : ConstructorView TowerArithmeticModel.roles t key fields) {c : DeclName}
    {args : List (Tm Tower.Head 0)} (same : t = appSpine (.const c) args) : fields = args := by
  cases view with
  | spine args' _ => exact (appSpine_const_injective same).2
  | refl a => exact absurd same.symm appSpine_const_ne_refl

/-- **The model's numerals are in canonical form.** -/
theorem numTm_canonical : ∀ k : ℕ, CanonicalForm (numTm k)
  | 0 => .view (ConstructorView.spine (c := zero) [] roles_zero) fun _ member =>
      absurd member List.not_mem_nil
  | k + 1 => .view (ConstructorView.spine (c := succ) [numTm k] roles_succ) fun a member => by
      rw [List.mem_singleton.mp member]
      exact numTm_canonical k

variable (lv : LevelExpr Nat)

/-- **A translation in canonical form that the model equates with a numeral is that numeral's
translation**, by injectivity and discrimination of the model's constructors. -/
theorem numeral_of_canonical :
    ∀ (m : ℕ) {e : Expr}, Equal (TowerArithmeticModel.rules lv) .nil (translate e) (numTm m) (.const num) →
      CanonicalForm (translate e) → e = numeral m := by
  intro m
  induction m with
  | zero =>
      intro e equal canonical
      obtain ⟨view, fieldsCanonical⟩ := canonical
      rcases view.canonical with ⟨x, isRefl⟩ | ⟨c, arity, args, role, isSpine⟩
      · exact absurd isRefl (translate_ne_refl e x)
      · have fields := view_fields view isSpine
        rw [isSpine] at equal
        have mem : (c, if c = zero then [] else [.recursive]) ∈ ctors := by
          rcases roles_constructor role with rfl | rfl
          · simpa using mem_zero
          · simpa [TowerNumbersModel.zero_ne_succ.symm] using mem_succ
        obtain ⟨rfl, _, fieldsEqual⟩ := Equal.ctor_injective (S := TowerArithmeticModel.setting lv fun _ => 0)
          (TowerArithmeticModel.laws lv _) (TowerArithmeticModel.constants lv _) CtxFormed.nil
          (TowerArithmeticModel.setting_roles_num lv _) mem mem_zero (as := args) (bs := [])
          equal
        rw [if_pos rfl] at fieldsEqual
        cases fieldsEqual
        exact translate_eq_zero isSpine
  | succ m ih =>
      intro e equal canonical
      obtain ⟨view, fieldsCanonical⟩ := canonical
      rcases view.canonical with ⟨x, isRefl⟩ | ⟨c, arity, args, role, isSpine⟩
      · exact absurd isRefl (translate_ne_refl e x)
      · have fields := view_fields view isSpine
        rw [isSpine] at equal
        have mem : (c, if c = zero then [] else [.recursive]) ∈ ctors := by
          rcases roles_constructor role with rfl | rfl
          · simpa using mem_zero
          · simpa [TowerNumbersModel.zero_ne_succ.symm] using mem_succ
        obtain ⟨rfl, _, fieldsEqual⟩ := Equal.ctor_injective (S := TowerArithmeticModel.setting lv fun _ => 0)
          (TowerArithmeticModel.laws lv _) (TowerArithmeticModel.constants lv _) CtxFormed.nil
          (TowerArithmeticModel.setting_roles_num lv _) mem mem_succ (as := args) (bs := [numTm m])
          equal
        rw [if_neg TowerNumbersModel.zero_ne_succ.symm] at fieldsEqual
        cases fieldsEqual with
        | cons head tail =>
            cases tail
            obtain ⟨x, rfl, inner⟩ := translate_eq_succ_app isSpine
            have canonicalX : CanonicalForm (translate x) := by
              rw [inner]
              exact fieldsCanonical _ (by rw [fields]; exact List.mem_singleton_self _)
            have equalX : Equal (TowerArithmeticModel.rules lv) .nil (translate x) (numTm m) (.const num) := by
              rw [inner]
              exact head
            rw [ih equalX canonicalX]
            rfl

/-! ## Agreement -/

/-- **A row of the number region is generated exactly when the translation of its content is typed at
`num` in the empty context and in canonical form all the way down.** -/
theorem generated_iff_translate (e : Expr) :
    Generated natRules ∅ (natRow e) ↔
      Typed (TowerArithmeticModel.rules lv) .nil (translate e) (.const num) ∧
        CanonicalForm (translate e) := by
  constructor
  · intro generated
    obtain ⟨k, same⟩ := Numbers.natRules_generated_iff.mp generated
    rw [natRow_injective same, translate_numeral]
    exact ⟨numTm_typed lv k, numTm_canonical k⟩
  · rintro ⟨typed, canonical⟩
    obtain ⟨m, equal⟩ := canonicity lv typed
    rw [numeral_of_canonical lv m equal canonical]
    exact Numbers.numeral_generated m

/-- **The membership agreement of `Agreement`, with the total reading**: a row is generated exactly
when the translation of its content is a closed canonical number of the model. -/
theorem generated_iff_closedCanonical_translate (e : Expr) :
    Generated natRules ∅ (natRow e) ↔ ClosedCanonicalNum lv (translate e) := by
  rw [closedCanonical_iff]
  constructor
  · intro generated
    obtain ⟨k, same⟩ := Numbers.natRules_generated_iff.mp generated
    rw [natRow_injective same, translate_numeral]
    exact ⟨k, rfl⟩
  · rintro ⟨k, same⟩
    rw [translate_numTm k same]
    exact Numbers.numeral_generated k

/-! ## Each condition is needed -/

theorem symName_rigid : TowerArithmeticModel.roles (symName 199) = .rigid := by
  have hadd : symName 199 ≠ add := by decide
  have hnum : symName 199 ≠ num := by decide
  have hzero : symName 199 ≠ zero := by decide
  have hsucc : symName 199 ≠ succ := by decide
  have hrec : symName 199 ≠ numRec := by decide
  simp [TowerArithmeticModel.roles, hadd, TowerNumbersModel.roles, hnum, hzero, hsucc, hrec]

/-- **Junk is read, and its reading is neither typed nor canonical**: the translation of `junkE` is a
constant the model does not declare, typed at no type and not in canonical form. -/
theorem junk_untranslatable :
    translate junkE = .const (symName 199) ∧
      (∀ T, ¬ Typed (TowerArithmeticModel.rules lv) .nil (translate junkE) T) ∧
      ¬ CanonicalForm (translate junkE) ∧ ¬ Generated natRules ∅ (natRow junkE) := by
  have read : translate junkE = .const (symName 199) := rfl
  refine ⟨read, fun T typed => ?_, fun canonical => ?_, Numbers.junk_not_generated⟩
  · exact free_of_undeclared (Agreement.undeclared_of_rigid lv symName_rigid) typed rfl
  · obtain ⟨view, -⟩ := canonical
    rcases view.canonical with ⟨x, isRefl⟩ | ⟨c, arity, args, role, isSpine⟩
    · exact translate_ne_refl junkE x isRefl
    · rw [read] at isSpine
      have heads := (appSpine_const_injective (as := []) isSpine).1
      rw [← heads, symName_rigid] at role
      cases role

/-- `zero` applied to `zero`. -/
def overApplied : Expr := .app zeroE zeroE

/-- **In canonical form**: a constructor spine of `zero`, whose one field is `zero`. -/
theorem overApplied_canonical : CanonicalForm (translate overApplied) :=
  .view (ConstructorView.spine (c := zero) [.const zero] roles_zero) fun a member => by
    rw [List.mem_singleton.mp member]
    exact numTm_canonical 0

theorem overApplied_not_generated : ¬ Generated natRules ∅ (natRow overApplied) := by
  intro generated
  obtain ⟨k, same⟩ := Numbers.natRules_generated_iff.mp generated
  have content := natRow_injective same
  cases k with
  | zero => cases content
  | succ k =>
      simp only [overApplied, numeral, zeroE, succE, Expr.app.injEq] at content
      exact absurd content.1 (by decide)

/-- **Not typed at `num`**: the typing counts the arguments the roles do not. -/
theorem overApplied_untyped :
    ¬ Typed (TowerArithmeticModel.rules lv) .nil (translate overApplied) (.const num) := fun typed =>
  overApplied_not_generated ((generated_iff_translate lv overApplied).mpr ⟨typed, overApplied_canonical⟩)

/-- The request for the sum of zero and zero. -/
def request : Expr := askAdd zeroE zeroE

/-- **Typed and not canonical**: the request translates to `add zero zero`, which is typed at `num`
and equal there to the numeral `0`, and is not in canonical form; its row is not generated. -/
theorem request_typed_not_canonical :
    translate request = addTm (numTm 0) (numTm 0) ∧
      Typed (TowerArithmeticModel.rules lv) .nil (translate request) (.const num) ∧
      Equal (TowerArithmeticModel.rules lv) .nil (translate request) (numTm 0) (.const num) ∧
      ¬ CanonicalForm (translate request) ∧ ¬ Generated natRules ∅ (natRow request) := by
  have read : translate request = addTm (numTm 0) (numTm 0) := rfl
  have notCanonical : ¬ CanonicalForm (translate request) := by
    intro canonical
    obtain ⟨view, -⟩ := canonical
    rcases view.canonical with ⟨x, isRefl⟩ | ⟨c, arity, args, role, isSpine⟩
    · exact translate_ne_refl request x isRefl
    · have spine : translate request = appSpine (.const add) [.const zero, .const zero] := rfl
      have heads := (appSpine_const_injective (spine.symm.trans isSpine)).1
      rw [← heads, TowerArithmeticModel.roles_add] at role
      cases role
  refine ⟨read, ?_, ?_, notCanonical, fun generated => ?_⟩
  · rw [read]
    exact addTm_typed lv (numTm_typed lv 0) (numTm_typed lv 0)
  · rw [read]
    exact add_numerals lv 0 0
  · exact notCanonical ((generated_iff_translate lv request).mp generated).2

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes.Translation

section Audit
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes.Translation
#print axioms translate_eq_zero
#print axioms translate_eq_succ_app
#print axioms translate_numeral
#print axioms translate_numTm
#print axioms translate_of_toModel
#print axioms roles_constructor
#print axioms numTm_canonical
#print axioms numeral_of_canonical
#print axioms generated_iff_translate
#print axioms generated_iff_closedCanonical_translate
#print axioms junk_untranslatable
#print axioms overApplied_canonical
#print axioms overApplied_untyped
#print axioms request_typed_not_canonical
end Audit
