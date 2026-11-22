import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentOccursRenamed
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentOccursFullUnder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIdEndpoints

/-!
# The occurs rule for a side held at the bound variable of the other side

An equation `λ x̄. V ≐ λ x̄. Π (y : D). B` at `Π x̄. U`, with `U` a universe, `D` the type of one of the abstracted
variables `x`, and `B` with `y` replaced by `x` equal to `V`, has no solution at any later context. The same holds
with Σ for Π. This is the shape of `λ x. Q x ≐ λ x. Π (y : A). Q y`: the pattern's unknown at the variable that the
other side binds. The same holds at any depth: the other side may carry `V` along type-former positions. A codomain
is passed either with its bound variable replaced by `x`, when its domain is `D`, or past its bound variable, with
`V` weakened (`Carried`), as in `λ x. Q x ≐ λ x. Π (y : A). Π (z : Q y). A` and
`λ x. Q x ≐ λ x. Π (w : R x). Π (y : A). Q y`.

* `Carried` is the carrying on codes, `UnderBound` the shape: it picks an abstraction (`here`), and below the
  remaining abstractions reads the carrying (`Held`). A later abstraction of the type of the picked one may be
  merged into it (`Held.merge`), since equal abstractions are equal at equal arguments: this reads
  `λ x w y. Q y ≐ λ x w y. Π (z : A). Q x`. Both are kept by every substitution (`Carried.subst`,
  `UnderBound.subst`), because merging at a variable commutes with a substitution that keeps the variable a variable
  (`rename_mergeAt_subst`).
* `carried_not_typeEq`: a type is never equal to a type that carries it past a former. Past a codomain the normal
  form of the codomain is sent by the merging to a normal form of the merged codomain, with the same number of
  nodes (`normal_carried`). `underBound_not_equal`: sides of the shape are never equal.
* **Merging.** Equal abstractions are equal at equal arguments. So an equation under two consecutive abstractions of
  one type is refuted as soon as the equation with the two variables merged is (`Merged`, `merged_not_equal`,
  `Merged.subst`). The merged equation is read by the shape above or by the tower's occurs check under abstractions
  (`UnderInside`). This reads the unknown at **another outer variable**: `λ x y. Q y ≐ λ x y. Π (z : A). Q x` merges
  to `λ x. Q x ≐ λ x. Π (z : A). Q x`, and `λ x y. G y ≐ λ x y. Π (z : y). G x` to `λ x. G x ≐ λ x. Π (z : x). G x`.
* `carried?`, `underBound?` and `merged?` read the shapes from codes, with their proofs; `boundShape` reads them from
  an equation; `BoundShape.refutes` refutes the equation at every later context; `boundSearch` refutes a store at
  the first equation of a shape, in either orientation.

Abstractions are merged only when their types are one code, and a bound variable is replaced only by the one picked
abstraction, when the domain is the code of its type. A pattern with two arguments of different types, both held at
bound variables, is not read.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentOccursBound

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentInPlace ContextualDependentRigidFormers ContextualDependentEtaExpansion
open ContextualDependentConversionBudget ContextualDependentEtaLong ContextualDependentOccursCheck
open ContextualDependentRecognitionConversion ContextualDependentOccursFull ContextualDependentOccursRenamed
open ContextualDependentIdEndpoints

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## The shape on codes -/

omit [UniverseLevel.LevelOrder L] in
/-- Merging at a variable commutes with a substitution that keeps the variable a variable. -/
theorem rename_mergeAt_subst {n m : Nat} (τ : Sub Head n m) {x : Fin n} {x' : Fin m} (kept : τ x = .var x')
    (term : Tm Head (n + 1)) :
    Presentation.rename (mergeAt x') (Presentation.subst (liftSub τ) term) =
      Presentation.subst τ (Presentation.rename (mergeAt x) term) := by
  rw [rename_subst, subst_rename]
  congr 1
  funext index
  refine Fin.cases ?_ ?_ index
  · show Presentation.rename (mergeAt x') (.var 0) = τ (mergeAt x 0)
    rw [mergeAt_zero, kept]
    rfl
  · intro prior
    show Presentation.rename (mergeAt x') (Presentation.rename wk (τ prior)) = τ (mergeAt x prior.succ)
    rw [rename_mergeAt_wk, mergeAt_succ]

/-- **`T` carries `V` along type-former positions, its bound variables merged into `x`**: `T` is `V`, or a Π or Σ
type with `V` carried by its domain, or with domain `D` and `V` carried by its codomain where the bound variable is
replaced by `x`, or an identity type with `V` carried by its carrier. The flag records that at least one former was
passed. -/
inductive Carried : {n : Nat} → Fin n → Tm Head n → Bool → Tm Head n → Tm Head n → Prop
  | here {n : Nat} (x : Fin n) (D V : Tm Head n) : Carried x D false V V
  | domain (isPi : Bool) {proper : Bool} {n : Nat} {x : Fin n} {D V A : Tm Head n} {B : Tm Head (n + 1)} :
      Carried x D proper V A → Carried x D true V (binder isPi A B)
  | codomain (isPi : Bool) {proper : Bool} {n : Nat} {x : Fin n} {D V : Tm Head n} {B : Tm Head (n + 1)} :
      Carried x D proper V (Presentation.rename (mergeAt x) B) → Carried x D true V (binder isPi D B)
  | weak (isPi : Bool) {proper : Bool} {n : Nat} {x : Fin n} {D V A : Tm Head n} {B : Tm Head (n + 1)} :
      Carried x.succ (Presentation.rename wk D) proper (Presentation.rename wk V) B →
      Carried x D true V (binder isPi A B)
  | carrier {proper : Bool} {n : Nat} {x : Fin n} {D V A a b : Tm Head n} :
      Carried x D proper V A → Carried x D true V (.id A a b)

omit [UniverseLevel.LevelOrder L] in
/-- Carrying is kept by a substitution that keeps the variable a variable. -/
theorem Carried.subst {n : Nat} {x : Fin n} {D V T : Tm Head n} {proper : Bool} (carried : Carried x D proper V T) :
    ∀ {m : Nat} (τ : Sub Head n m) {x' : Fin m}, τ x = .var x' →
      Carried x' (Presentation.subst τ D) proper (Presentation.subst τ V) (Presentation.subst τ T) := by
  induction carried with
  | here x D V =>
      intro m τ x' _
      exact .here _ _ _
  | domain isPi _ ih =>
      intro m τ x' kept
      rw [subst_binder]
      exact .domain isPi (ih τ kept)
  | @codomain isPi proper n x D V B _ ih =>
      intro m τ x' kept
      rw [subst_binder]
      have inner := ih τ kept
      rw [← rename_mergeAt_subst τ kept] at inner
      exact .codomain isPi inner
  | @weak isPi proper n x D V A B _ ih =>
      intro m τ x' kept
      rw [subst_binder]
      have lifted : liftSub τ x.succ = .var x'.succ := by
        have step : liftSub τ x.succ = Presentation.rename wk (τ x) := by simp [liftSub]
        rw [step, kept]
        rfl
      have inner := ih (liftSub τ) lifted
      simp only [subst_liftSub_wk] at inner
      exact .weak isPi inner
  | carrier _ ih => exact fun τ _ kept => .carrier (ih τ kept)

/-- **Below the abstractions**: `λ ȳ. V ≐ λ ȳ. T` at `Π ȳ. U`, for a variable `x` and the code `D` of its type, both
weakened past `ȳ`, where `T` carries `V` past at least one former with its bound variables merged into `x`. -/
inductive Held (R : Rules Head) : {n : Nat} → Fin n → Tm Head n → Tm Head n → Tm Head n → Tm Head n → Prop
  | stop {n : Nat} {u : Head} {x : Fin n} {D V T : Tm Head n} :
      R.isUniverse u → Carried x D true V T → Held R x D (.head u) V T
  | bind {n : Nat} {x : Fin n} {D A : Tm Head n} {C V T : Tm Head (n + 1)} :
      Held R x.succ (Presentation.rename wk D) C V T → Held R x D (.pi A C) (.lam V) (.lam T)
  | merge {n : Nat} {x : Fin n} {D : Tm Head n} {C V T : Tm Head (n + 1)} :
      Held R x D (Presentation.rename (mergeAt x) C) (Presentation.rename (mergeAt x) V)
        (Presentation.rename (mergeAt x) T) →
      Held R x D (.pi D C) (.lam V) (.lam T)

/-- **The shape**: under some abstractions, an abstraction whose variable and type are held below it. -/
inductive UnderBound (R : Rules Head) : {n : Nat} → Tm Head n → Tm Head n → Tm Head n → Prop
  | here {n : Nat} {A : Tm Head n} {C V T : Tm Head (n + 1)} :
      Held R 0 (Presentation.rename wk A) C V T → UnderBound R (.pi A C) (.lam V) (.lam T)
  | bind {n : Nat} {A : Tm Head n} {C V T : Tm Head (n + 1)} :
      UnderBound R C V T → UnderBound R (.pi A C) (.lam V) (.lam T)

omit [UniverseLevel.LevelOrder L] in
/-- The reading below the abstractions is kept by a substitution that keeps the variable a variable. -/
theorem Held.subst {R : Rules Head} {n : Nat} {x : Fin n} {D annotation left right : Tm Head n}
    (held : Held R x D annotation left right) :
    ∀ {m : Nat} (τ : Sub Head n m) {x' : Fin m}, τ x = .var x' →
      Held R x' (Presentation.subst τ D) (Presentation.subst τ annotation) (Presentation.subst τ left)
        (Presentation.subst τ right) := by
  induction held with
  | @stop n u x D V T universal carried =>
      intro m τ x' kept
      exact .stop universal (carried.subst τ kept)
  | @bind n x D A C V T _ ih =>
      intro m τ x' kept
      have lifted : liftSub τ x.succ = .var x'.succ := by
        have step : liftSub τ x.succ = Presentation.rename wk (τ x) := by simp [liftSub]
        rw [step, kept]
        rfl
      have inner := ih (liftSub τ) lifted
      rw [subst_liftSub_wk] at inner
      exact .bind inner
  | @merge n x D C V T _ ih =>
      intro m τ x' kept
      have inner := ih τ kept
      simp only [← rename_mergeAt_subst τ kept] at inner
      exact .merge inner

omit [UniverseLevel.LevelOrder L] in
/-- The shape is kept by substitution. -/
theorem UnderBound.subst {R : Rules Head} {n : Nat} {annotation left right : Tm Head n}
    (under : UnderBound R annotation left right) :
    ∀ {m : Nat} (σ : Sub Head n m),
      UnderBound R (Presentation.subst σ annotation) (Presentation.subst σ left) (Presentation.subst σ right) := by
  induction under with
  | @here n A C V T held =>
      intro m σ
      have inner := held.subst (liftSub σ) (x' := 0) rfl
      rw [subst_liftSub_wk] at inner
      exact .here inner
  | bind _ ih => exact fun σ => .bind (ih (liftSub σ))

/-! ### All the abstractions in scope at once -/

/-- Abstractions of an equation in scope, each with the code of its type. -/
abbrev Locals (Head : Type) (n : Nat) := List (Fin n × Tm Head n)

/-- The abstractions in scope, past one more binder. -/
def shiftLocals {n : Nat} (locals : Locals Head n) : Locals Head (n + 1) :=
  locals.map fun entry => (entry.1.succ, Presentation.rename wk entry.2)

/-- **`T` carries `V`, each bound variable it passes replaced by an abstraction of the type of its domain**, or
passed with `V` weakened. Different bound variables may go to different abstractions. -/
inductive CarriedIn : {n : Nat} → Locals Head n → Bool → Tm Head n → Tm Head n → Prop
  | here {n : Nat} (locals : Locals Head n) (V : Tm Head n) : CarriedIn locals false V V
  | domain (isPi : Bool) {proper : Bool} {n : Nat} {locals : Locals Head n} {V A : Tm Head n}
      {B : Tm Head (n + 1)} : CarriedIn locals proper V A → CarriedIn locals true V (binder isPi A B)
  | codomain (isPi : Bool) {proper : Bool} {n : Nat} {locals : Locals Head n} {x : Fin n} {D V : Tm Head n}
      {B : Tm Head (n + 1)} : (x, D) ∈ locals → CarriedIn locals proper V (Presentation.rename (mergeAt x) B) →
      CarriedIn locals true V (binder isPi D B)
  | weak (isPi : Bool) {proper : Bool} {n : Nat} {locals : Locals Head n} {V A : Tm Head n}
      {B : Tm Head (n + 1)} : CarriedIn (shiftLocals locals) proper (Presentation.rename wk V) B →
      CarriedIn locals true V (binder isPi A B)
  | carrier {proper : Bool} {n : Nat} {locals : Locals Head n} {V A a b : Tm Head n} :
      CarriedIn locals proper V A → CarriedIn locals true V (.id A a b)

/-- **Below the abstractions, all of them in scope**: each abstraction is added to the abstractions in scope, or
merged into an earlier one of its type; at the universe the right side carries the left. -/
inductive HeldIn (R : Rules Head) : {n : Nat} → Locals Head n → Tm Head n → Tm Head n → Tm Head n → Prop
  | stop {n : Nat} {u : Head} {locals : Locals Head n} {V T : Tm Head n} :
      R.isUniverse u → CarriedIn locals true V T → HeldIn R locals (.head u) V T
  | bind {n : Nat} {locals : Locals Head n} {A : Tm Head n} {C V T : Tm Head (n + 1)} :
      HeldIn R ((0, Presentation.rename wk A) :: shiftLocals locals) C V T →
      HeldIn R locals (.pi A C) (.lam V) (.lam T)
  | merge {n : Nat} {locals : Locals Head n} {x : Fin n} {D : Tm Head n} {C V T : Tm Head (n + 1)} :
      (x, D) ∈ locals →
      HeldIn R locals (Presentation.rename (mergeAt x) C) (Presentation.rename (mergeAt x) V)
        (Presentation.rename (mergeAt x) T) →
      HeldIn R locals (.pi D C) (.lam V) (.lam T)

/-- A substitution keeps the abstractions in scope: it sends each to a variable, of the substituted type. -/
def Kept {n m : Nat} (τ : Sub Head n m) (locals : Locals Head n) (locals' : Locals Head m) : Prop :=
  List.Forall₂ (fun entry entry' => τ entry.1 = .var entry'.1 ∧ entry'.2 = Presentation.subst τ entry.2)
    locals locals'

theorem Kept.mem {n m : Nat} {τ : Sub Head n m} {locals : Locals Head n} {locals' : Locals Head m}
    (kept : Kept τ locals locals') {x : Fin n} {D : Tm Head n} (member : (x, D) ∈ locals) :
    ∃ x', (x', Presentation.subst τ D) ∈ locals' ∧ τ x = .var x' := by
  induction kept with
  | nil => cases member
  | @cons entry entry' rest rest' head _ ih =>
      rcases List.mem_cons.mp member with same | later
      · subst same
        have second : entry'.2 = Presentation.subst τ D := head.2
        exact ⟨entry'.1, by rw [← second]; exact List.mem_cons_self, head.1⟩
      · obtain ⟨x', member', sent⟩ := ih later
        exact ⟨x', List.mem_cons_of_mem _ member', sent⟩

theorem Kept.shift {n m : Nat} {τ : Sub Head n m} {locals : Locals Head n} {locals' : Locals Head m}
    (kept : Kept τ locals locals') : Kept (liftSub τ) (shiftLocals locals) (shiftLocals locals') := by
  induction kept with
  | nil => exact .nil
  | @cons entry entry' rest rest' head _ ih =>
      refine List.Forall₂.cons ⟨?_, ?_⟩ ih
      · show liftSub τ entry.1.succ = .var entry'.1.succ
        have step : liftSub τ entry.1.succ = Presentation.rename wk (τ entry.1) := by simp [liftSub]
        rw [step, head.1]
        rfl
      · show Presentation.rename wk entry'.2 = Presentation.subst (liftSub τ) (Presentation.rename wk entry.2)
        rw [subst_liftSub_wk, head.2]

/-- Carrying is kept by a substitution that keeps the abstractions in scope. -/
theorem CarriedIn.subst {n : Nat} {locals : Locals Head n} {V T : Tm Head n} {proper : Bool}
    (carried : CarriedIn locals proper V T) :
    ∀ {m : Nat} (τ : Sub Head n m) {locals' : Locals Head m}, Kept τ locals locals' →
      CarriedIn locals' proper (Presentation.subst τ V) (Presentation.subst τ T) := by
  induction carried with
  | here locals V =>
      intro m τ locals' _
      exact .here _ _
  | domain isPi _ ih =>
      intro m τ locals' kept
      rw [subst_binder]
      exact .domain isPi (ih τ kept)
  | @codomain isPi proper n locals x D V B member _ ih =>
      intro m τ locals' kept
      obtain ⟨x', member', sent⟩ := kept.mem member
      rw [subst_binder]
      have inner := ih τ kept
      rw [← rename_mergeAt_subst τ sent] at inner
      exact .codomain isPi member' inner
  | @weak isPi proper n locals V A B _ ih =>
      intro m τ locals' kept
      rw [subst_binder]
      have inner := ih (liftSub τ) kept.shift
      rw [subst_liftSub_wk] at inner
      exact .weak isPi inner
  | carrier _ ih => exact fun τ _ kept => .carrier (ih τ kept)

/-- The reading below the abstractions is kept by a substitution that keeps the abstractions in scope. -/
theorem HeldIn.subst {R : Rules Head} {n : Nat} {locals : Locals Head n} {annotation left right : Tm Head n}
    (held : HeldIn R locals annotation left right) :
    ∀ {m : Nat} (τ : Sub Head n m) {locals' : Locals Head m}, Kept τ locals locals' →
      HeldIn R locals' (Presentation.subst τ annotation) (Presentation.subst τ left)
        (Presentation.subst τ right) := by
  induction held with
  | stop universal carried =>
      intro m τ locals' kept
      exact .stop universal (carried.subst τ kept)
  | @bind n locals A C V T _ ih =>
      intro m τ locals' kept
      have extended : Kept (liftSub τ) ((0, Presentation.rename wk A) :: shiftLocals locals)
          ((0, Presentation.rename wk (Presentation.subst τ A)) :: shiftLocals locals') :=
        List.Forall₂.cons ⟨rfl, (subst_liftSub_wk τ A).symm⟩ kept.shift
      exact .bind (ih (liftSub τ) extended)
  | @merge n locals x D C V T member _ ih =>
      intro m τ locals' kept
      obtain ⟨x', member', sent⟩ := kept.mem member
      have inner := ih τ kept
      simp only [← rename_mergeAt_subst τ sent] at inner
      exact .merge member' inner

/-- **The shapes read after merging abstractions**: the shape above, or the occurs check under abstractions of the
tower (`UnderInside`), read as they stand, or after two consecutive abstractions of one type are merged into one, or
under an abstraction; or the reading with all the abstractions in scope. Equal abstractions are equal at equal
arguments, so a refutation of the merged equation refutes the equation. -/
inductive Merged (R : Rules Head) : {n : Nat} → Tm Head n → Tm Head n → Tm Head n → Prop
  | bound {n : Nat} {annotation left right : Tm Head n} :
      UnderBound R annotation left right → Merged R annotation left right
  | inScope {n : Nat} {annotation left right : Tm Head n} :
      HeldIn R [] annotation left right → Merged R annotation left right
  | inside {n : Nat} {annotation left right : Tm Head n} :
      UnderInside R annotation left right → Merged R annotation left right
  | merge {n : Nat} {A : Tm Head n} {C V T : Tm Head (n + 1 + 1)} :
      Merged R (.pi A (Presentation.rename (mergeAt 0) C)) (.lam (Presentation.rename (mergeAt 0) V))
        (.lam (Presentation.rename (mergeAt 0) T)) →
      Merged R (.pi A (.pi (Presentation.rename wk A) C)) (.lam (.lam V)) (.lam (.lam T))
  | bind {n : Nat} {A : Tm Head n} {C V T : Tm Head (n + 1)} :
      Merged R C V T → Merged R (.pi A C) (.lam V) (.lam T)

omit [UniverseLevel.LevelOrder L] in
/-- The merged shapes are kept by substitution. -/
theorem Merged.subst {R : Rules Head} {n : Nat} {annotation left right : Tm Head n}
    (merged : Merged R annotation left right) :
    ∀ {m : Nat} (σ : Sub Head n m),
      Merged R (Presentation.subst σ annotation) (Presentation.subst σ left) (Presentation.subst σ right) := by
  induction merged with
  | bound under => exact fun σ => .bound (under.subst σ)
  | inScope held => exact fun σ => .inScope (held.subst σ .nil)
  | inside under => exact fun σ => .inside (under.subst σ)
  | @merge n A C V T _ ih =>
      intro m σ
      have inner := ih σ
      have moveC := rename_mergeAt_subst (liftSub σ) (x := 0) (x' := 0) rfl C
      have moveV := rename_mergeAt_subst (liftSub σ) (x := 0) (x' := 0) rfl V
      have moveT := rename_mergeAt_subst (liftSub σ) (x := 0) (x' := 0) rfl T
      have shaped : Merged R
          (.pi (Presentation.subst σ A)
            (Presentation.rename (mergeAt 0) (Presentation.subst (liftSub (liftSub σ)) C)))
          (.lam (Presentation.rename (mergeAt 0) (Presentation.subst (liftSub (liftSub σ)) V)))
          (.lam (Presentation.rename (mergeAt 0) (Presentation.subst (liftSub (liftSub σ)) T))) := by
        rw [moveC, moveV, moveT]
        exact inner
      have result := Merged.merge shaped
      show Merged R
        (.pi (Presentation.subst σ A) (.pi (Presentation.subst (liftSub σ) (Presentation.rename wk A))
          (Presentation.subst (liftSub (liftSub σ)) C)))
        (.lam (.lam (Presentation.subst (liftSub (liftSub σ)) V)))
        (.lam (.lam (Presentation.subst (liftSub (liftSub σ)) T)))
      rw [subst_liftSub_wk]
      exact result
  | bind _ ih => exact fun σ => .bind (ih (liftSub σ))

section Refutation

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **Normal forms along a carrying**: when `x` has the declared type `D` and `V` is equal to a normal type `N`, a
type that carries `V` has a normal form with at least as many nodes as `N`, and strictly more when a former was
passed. Past a codomain, the normal form of the codomain is carried by the merging to a normal form of the merged
codomain, with the same number of nodes. -/
theorem normal_carried {n : Nat} {x : Fin n} {D V T : Tm Head n} {proper : Bool}
    (carried : Carried x D proper V T) :
    ∀ {Γ : Ctx Head n}, CtxFormed S.R Γ → Ctx.lookup Γ x = D → ∀ {N : Tm Head n},
      Long S.R S.roles (.type Γ N) → TypeEq S.R Γ V N → IsType S.R Γ T →
      ∃ W, Long S.R S.roles (.type Γ W) ∧ TypeEq S.R Γ T W ∧ nodes N ≤ nodes W ∧
        (proper = true → nodes N < nodes W) := by
  induction carried with
  | here x D V =>
      intro Γ _ _ N lN VN _
      exact ⟨N, lN, VN, le_refl _, fun h => absurd h (by decide)⟩
  | domain isPi _ ih =>
      intro Γ formed declared N lN VN isType
      obtain ⟨isA, _⟩ := binder_parts_typed isPi isType
      obtain ⟨WA, lWA, AWA, le, _⟩ := ih formed declared lN VN isA
      obtain ⟨W, lW, TW, larger⟩ :=
        normal_binder facts roots heads algebra rigid complete isPi formed lWA AWA isType
      exact ⟨W, lW, TW, by omega, fun _ => by omega⟩
  | @codomain isPi proper n x D V B _ ih =>
      intro Γ formed declared N lN VN isType
      obtain ⟨isD, v, hv, tB⟩ := binder_parts_typed isPi isType
      have formedB : CtxFormed S.R (.snoc Γ D) := formed.snoc isD
      have compatible : CtxRen (.snoc Γ D) Γ (mergeAt x) := by
        rw [← declared]
        exact mergeAt_ctxRen Γ x
      obtain ⟨NB, lNB, atNB⟩ := long_type_exists facts roots heads algebra rigid complete formedB ⟨v, hv, tB⟩
      have BNB : TypeEq S.R (.snoc Γ D) B NB := ⟨v, hv, (atNB hv tB).2⟩
      have isMerged : IsType S.R Γ (Presentation.rename (mergeAt x) B) :=
        IsType.rename ⟨v, hv, tB⟩ compatible
      obtain ⟨W', lW', BW', le, _⟩ := ih formed declared lN VN isMerged
      have lMerged : Long S.R S.roles (.type Γ (Presentation.rename (mergeAt x) NB)) :=
        lNB.type_rename facts compatible formedB formed
      have same := nodes_of_same (long_type_unique facts roots heads algebra complete formed lMerged lW'
        (TypeEq.trans S.levels (BNB.rename compatible).symm BW'))
      rw [nodes_rename] at same
      obtain ⟨W, lW, TW, larger⟩ :=
        normal_codomain facts roots heads algebra rigid complete isPi formed lNB BNB isType
      exact ⟨W, lW, TW, by omega, fun _ => by omega⟩
  | @weak isPi proper n x D V A B _ ih =>
      intro Γ formed declared N lN VN isType
      obtain ⟨isA, v, hv, tB⟩ := binder_parts_typed isPi isType
      have declaredB : Ctx.lookup (.snoc Γ A) x.succ = Presentation.rename wk D := by
        rw [← declared]
        rfl
      obtain ⟨WB, lWB, BWB, le, _⟩ := ih (formed.snoc isA) declaredB (lN.type_weaken facts formed isA)
        (VN.rename (CtxRen.wk Γ A)) ⟨v, hv, tB⟩
      rw [nodes_rename] at le
      obtain ⟨W, lW, TW, larger⟩ :=
        normal_codomain facts roots heads algebra rigid complete isPi formed lWB BWB isType
      exact ⟨W, lW, TW, by omega, fun _ => by omega⟩
  | carrier _ ih =>
      intro Γ formed declared N lN VN isType
      obtain ⟨u, hu, tId⟩ := isType
      obtain ⟨WA, lWA, AWA, le, _⟩ := ih formed declared lN VN ⟨u, hu, (id_typed tId).1⟩
      obtain ⟨W, lW, TW, larger⟩ :=
        normal_carrier facts roots heads algebra rigid complete formed lWA AWA ⟨u, hu, tId⟩
      exact ⟨W, lW, TW, by omega, fun _ => by omega⟩

include facts roots heads algebra rigid complete in
/-- **The occurs check along a carrying**: a type is never equal to a type that carries it past at least one former,
its bound variables merged into a variable of the declared type. -/
theorem carried_not_typeEq {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {x : Fin n} {D V T : Tm Head n}
    (declared : Ctx.lookup Γ x = D) (carried : Carried x D true V T) (isV : IsType S.R Γ V)
    (isT : IsType S.R Γ T) : ¬ TypeEq S.R Γ V T := by
  intro same
  obtain ⟨N, lN, atN⟩ := long_type_exists facts roots heads algebra rigid complete formed isV
  obtain ⟨u, hu, tV⟩ := isV
  have VN : TypeEq S.R Γ V N := ⟨u, hu, (atN hu tV).2⟩
  obtain ⟨W, lW, TW, _, larger⟩ :=
    normal_carried facts roots heads algebra rigid complete carried formed declared lN VN isT
  have NW : TypeEq S.R Γ N W := TypeEq.trans S.levels VN.symm (TypeEq.trans S.levels same TW)
  have equalNodes := nodes_of_same (long_type_unique facts roots heads algebra complete formed lN lW NW)
  have := larger rfl
  omega

include facts roots heads algebra rigid complete in
/-- **Sides held at a variable of the declared type are never equal.** -/
theorem held_not_equal {n : Nat} {x : Fin n} {D annotation left right : Tm Head n}
    (held : Held S.R x D annotation left right) :
    ∀ {Δ : Ctx Head n}, CtxFormed S.R Δ → Ctx.lookup Δ x = D → Typed S.R Δ left annotation →
      Typed S.R Δ right annotation → ¬ Equal S.R Δ left right annotation := by
  induction held with
  | @stop n u x D V T universal carried =>
      intro Δ formed declared tLeft tRight same
      exact carried_not_typeEq facts roots heads algebra rigid complete formed declared carried
        ⟨u, universal, tLeft⟩ ⟨u, universal, tRight⟩ ⟨u, universal, same⟩
  | @bind n x D A C V T _ ih =>
      intro Δ formed declared tLeft tRight same
      obtain ⟨⟨u, hu, tA⟩, _⟩ := IsType.pi_parts (Typed.isType tLeft formed)
      exact ih (formed.snoc ⟨u, hu, tA⟩) (by rw [← declared]; rfl) (Typed.lam_inv facts tLeft formed)
        (Typed.lam_inv facts tRight formed) (lam_equal_inv facts formed same)
  | @merge n x D C V T _ ih =>
      intro Δ formed declared tLeft tRight same
      have compatible : CtxRen (.snoc Δ D) Δ (mergeAt x) := by
        rw [← declared]
        exact mergeAt_ctxRen Δ x
      exact ih formed declared ((Typed.lam_inv facts tLeft formed).rename compatible)
        ((Typed.lam_inv facts tRight formed).rename compatible)
        ((lam_equal_inv facts formed same).rename compatible)

include facts roots heads algebra rigid complete in
/-- **Sides of the shape are never equal.** -/
theorem underBound_not_equal {n : Nat} {annotation left right : Tm Head n}
    (under : UnderBound S.R annotation left right) :
    ∀ {Δ : Ctx Head n}, CtxFormed S.R Δ → Typed S.R Δ left annotation → Typed S.R Δ right annotation →
      ¬ Equal S.R Δ left right annotation := by
  induction under with
  | @here n A C V T held =>
      intro Δ formed tLeft tRight same
      obtain ⟨⟨u, hu, tA⟩, _⟩ := IsType.pi_parts (Typed.isType tLeft formed)
      exact held_not_equal facts roots heads algebra rigid complete held (formed.snoc ⟨u, hu, tA⟩) rfl
        (Typed.lam_inv facts tLeft formed) (Typed.lam_inv facts tRight formed) (lam_equal_inv facts formed same)
  | @bind n A B V T _ ih =>
      intro Δ formed tLeft tRight same
      obtain ⟨⟨u, hu, tA⟩, _⟩ := IsType.pi_parts (Typed.isType tLeft formed)
      exact ih (formed.snoc ⟨u, hu, tA⟩) (Typed.lam_inv facts tLeft formed) (Typed.lam_inv facts tRight formed)
        (lam_equal_inv facts formed same)

/-- The abstractions in scope have their codes as declared types. -/
def Declared {n : Nat} (Γ : Ctx Head n) (locals : Locals Head n) : Prop :=
  ∀ entry ∈ locals, Ctx.lookup Γ entry.1 = entry.2

theorem Declared.shift {n : Nat} {Γ : Ctx Head n} {locals : Locals Head n} (declared : Declared Γ locals)
    (A : Tm Head n) : Declared (.snoc Γ A) (shiftLocals locals) := by
  intro entry member
  obtain ⟨source, inside, rfl⟩ := List.mem_map.mp member
  show Ctx.lookup (.snoc Γ A) source.1.succ = Presentation.rename wk source.2
  rw [← declared source inside]
  rfl

include facts roots heads algebra rigid complete in
/-- **Normal forms along a carrying with the abstractions in scope**: as `normal_carried`, each codomain merged
into an abstraction of the declared type of its domain. -/
theorem normal_carriedIn {n : Nat} {locals : Locals Head n} {V T : Tm Head n} {proper : Bool}
    (carried : CarriedIn locals proper V T) :
    ∀ {Γ : Ctx Head n}, CtxFormed S.R Γ → Declared Γ locals → ∀ {N : Tm Head n},
      Long S.R S.roles (.type Γ N) → TypeEq S.R Γ V N → IsType S.R Γ T →
      ∃ W, Long S.R S.roles (.type Γ W) ∧ TypeEq S.R Γ T W ∧ nodes N ≤ nodes W ∧
        (proper = true → nodes N < nodes W) := by
  induction carried with
  | here locals V =>
      intro Γ _ _ N lN VN _
      exact ⟨N, lN, VN, le_refl _, fun h => absurd h (by decide)⟩
  | domain isPi _ ih =>
      intro Γ formed declared N lN VN isType
      obtain ⟨isA, _⟩ := binder_parts_typed isPi isType
      obtain ⟨WA, lWA, AWA, le, _⟩ := ih formed declared lN VN isA
      obtain ⟨W, lW, TW, larger⟩ :=
        normal_binder facts roots heads algebra rigid complete isPi formed lWA AWA isType
      exact ⟨W, lW, TW, by omega, fun _ => by omega⟩
  | @codomain isPi proper n locals x D V B member _ ih =>
      intro Γ formed declared N lN VN isType
      obtain ⟨isD, v, hv, tB⟩ := binder_parts_typed isPi isType
      have formedB : CtxFormed S.R (.snoc Γ D) := formed.snoc isD
      have atX : Ctx.lookup Γ x = D := declared (x, D) member
      have compatible : CtxRen (.snoc Γ D) Γ (mergeAt x) := by
        rw [← atX]
        exact mergeAt_ctxRen Γ x
      obtain ⟨NB, lNB, atNB⟩ := long_type_exists facts roots heads algebra rigid complete formedB ⟨v, hv, tB⟩
      have BNB : TypeEq S.R (.snoc Γ D) B NB := ⟨v, hv, (atNB hv tB).2⟩
      have isMerged : IsType S.R Γ (Presentation.rename (mergeAt x) B) :=
        IsType.rename ⟨v, hv, tB⟩ compatible
      obtain ⟨W', lW', BW', le, _⟩ := ih formed declared lN VN isMerged
      have lMerged : Long S.R S.roles (.type Γ (Presentation.rename (mergeAt x) NB)) :=
        lNB.type_rename facts compatible formedB formed
      have same := nodes_of_same (long_type_unique facts roots heads algebra complete formed lMerged lW'
        (TypeEq.trans S.levels (BNB.rename compatible).symm BW'))
      rw [nodes_rename] at same
      obtain ⟨W, lW, TW, larger⟩ :=
        normal_codomain facts roots heads algebra rigid complete isPi formed lNB BNB isType
      exact ⟨W, lW, TW, by omega, fun _ => by omega⟩
  | @weak isPi proper n locals V A B _ ih =>
      intro Γ formed declared N lN VN isType
      obtain ⟨isA, v, hv, tB⟩ := binder_parts_typed isPi isType
      obtain ⟨WB, lWB, BWB, le, _⟩ := ih (formed.snoc isA) (declared.shift A) (lN.type_weaken facts formed isA)
        (VN.rename (CtxRen.wk Γ A)) ⟨v, hv, tB⟩
      rw [nodes_rename] at le
      obtain ⟨W, lW, TW, larger⟩ :=
        normal_codomain facts roots heads algebra rigid complete isPi formed lWB BWB isType
      exact ⟨W, lW, TW, by omega, fun _ => by omega⟩
  | carrier _ ih =>
      intro Γ formed declared N lN VN isType
      obtain ⟨u, hu, tId⟩ := isType
      obtain ⟨WA, lWA, AWA, le, _⟩ := ih formed declared lN VN ⟨u, hu, (id_typed tId).1⟩
      obtain ⟨W, lW, TW, larger⟩ :=
        normal_carrier facts roots heads algebra rigid complete formed lWA AWA ⟨u, hu, tId⟩
      exact ⟨W, lW, TW, by omega, fun _ => by omega⟩

include facts roots heads algebra rigid complete in
/-- **The occurs check along a carrying with the abstractions in scope.** -/
theorem carriedIn_not_typeEq {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {locals : Locals Head n}
    {V T : Tm Head n} (declared : Declared Γ locals) (carried : CarriedIn locals true V T)
    (isV : IsType S.R Γ V) (isT : IsType S.R Γ T) : ¬ TypeEq S.R Γ V T := by
  intro same
  obtain ⟨N, lN, atN⟩ := long_type_exists facts roots heads algebra rigid complete formed isV
  obtain ⟨u, hu, tV⟩ := isV
  have VN : TypeEq S.R Γ V N := ⟨u, hu, (atN hu tV).2⟩
  obtain ⟨W, lW, TW, _, larger⟩ :=
    normal_carriedIn facts roots heads algebra rigid complete carried formed declared lN VN isT
  have NW : TypeEq S.R Γ N W := TypeEq.trans S.levels VN.symm (TypeEq.trans S.levels same TW)
  have equalNodes := nodes_of_same (long_type_unique facts roots heads algebra complete formed lN lW NW)
  have := larger rfl
  omega

include facts roots heads algebra rigid complete in
/-- **Sides held with the abstractions in scope are never equal.** -/
theorem heldIn_not_equal {n : Nat} {locals : Locals Head n} {annotation left right : Tm Head n}
    (held : HeldIn S.R locals annotation left right) :
    ∀ {Δ : Ctx Head n}, CtxFormed S.R Δ → Declared Δ locals → Typed S.R Δ left annotation →
      Typed S.R Δ right annotation → ¬ Equal S.R Δ left right annotation := by
  induction held with
  | @stop n u locals V T universal carried =>
      intro Δ formed declared tLeft tRight same
      exact carriedIn_not_typeEq facts roots heads algebra rigid complete formed declared carried
        ⟨u, universal, tLeft⟩ ⟨u, universal, tRight⟩ ⟨u, universal, same⟩
  | @bind n locals A C V T _ ih =>
      intro Δ formed declared tLeft tRight same
      obtain ⟨⟨u, hu, tA⟩, _⟩ := IsType.pi_parts (Typed.isType tLeft formed)
      have extended : Declared (.snoc Δ A) ((0, Presentation.rename wk A) :: shiftLocals locals) := by
        intro entry member
        rcases List.mem_cons.mp member with first | later
        · subst first
          rfl
        · exact declared.shift A entry later
      exact ih (formed.snoc ⟨u, hu, tA⟩) extended (Typed.lam_inv facts tLeft formed)
        (Typed.lam_inv facts tRight formed) (lam_equal_inv facts formed same)
  | @merge n locals x D C V T member _ ih =>
      intro Δ formed declared tLeft tRight same
      have atX : Ctx.lookup Δ x = D := declared (x, D) member
      have compatible : CtxRen (.snoc Δ D) Δ (mergeAt x) := by
        rw [← atX]
        exact mergeAt_ctxRen Δ x
      exact ih formed declared ((Typed.lam_inv facts tLeft formed).rename compatible)
        ((Typed.lam_inv facts tRight formed).rename compatible)
        ((lam_equal_inv facts formed same).rename compatible)

include facts roots heads algebra rigid complete in
/-- **Sides of a merged shape are never equal.** Two equal abstractions over two variables of one type are equal
with the two variables merged. -/
theorem merged_not_equal {n : Nat} {annotation left right : Tm Head n}
    (merged : Merged S.R annotation left right) :
    ∀ {Δ : Ctx Head n}, CtxFormed S.R Δ → Typed S.R Δ left annotation → Typed S.R Δ right annotation →
      ¬ Equal S.R Δ left right annotation := by
  induction merged with
  | bound under =>
      exact fun formed tLeft tRight =>
        underBound_not_equal facts roots heads algebra rigid complete under formed tLeft tRight
  | inScope held =>
      exact fun formed tLeft tRight =>
        heldIn_not_equal facts roots heads algebra rigid complete held formed
          (fun _ member => absurd member List.not_mem_nil) tLeft tRight
  | inside under =>
      exact fun formed tLeft tRight =>
        underInside_not_equal facts roots heads algebra rigid complete under formed tLeft tRight
  | @merge n A C V T _ ih =>
      intro Δ formed tLeft tRight same
      obtain ⟨⟨u, hu, tA⟩, v, hv, tInner⟩ := IsType.pi_parts (Typed.isType tLeft formed)
      have formed1 : CtxFormed S.R (.snoc Δ A) := formed.snoc ⟨u, hu, tA⟩
      obtain ⟨_, w, hw, tC⟩ :=
        IsType.pi_parts (⟨v, hv, tInner⟩ : IsType S.R (.snoc Δ A) (.pi (Presentation.rename wk A) C))
      have compatible : CtxRen (.snoc (.snoc Δ A) (Presentation.rename wk A)) (.snoc Δ A) (mergeAt 0) :=
        mergeAt_ctxRen (.snoc Δ A) 0
      have tC' : Typed S.R (.snoc Δ A) (Presentation.rename (mergeAt 0) C) (.head w) := tC.rename compatible
      obtain ⟨z, joined⟩ := S.levels.join_exists hu hw
      have tPi : Typed S.R Δ (.pi A (Presentation.rename (mergeAt 0) C)) (.head z) :=
        Derivable.piForm tA hu tC' hw joined
      have hz := (S.levels.join_level joined).1
      have bodyLeft := (Typed.lam_inv facts (Typed.lam_inv facts tLeft formed) formed1).rename compatible
      have bodyRight := (Typed.lam_inv facts (Typed.lam_inv facts tRight formed) formed1).rename compatible
      have bodies := (lam_equal_inv facts formed1 (lam_equal_inv facts formed same)).rename compatible
      exact ih formed (Derivable.lamIntro tPi hz bodyLeft) (Derivable.lamIntro tPi hz bodyRight)
        (Derivable.lamCong tPi hz bodies)
  | @bind n A B V T _ ih =>
      intro Δ formed tLeft tRight same
      obtain ⟨⟨u, hu, tA⟩, _⟩ := IsType.pi_parts (Typed.isType tLeft formed)
      exact ih (formed.snoc ⟨u, hu, tA⟩) (Typed.lam_inv facts tLeft formed) (Typed.lam_inv facts tRight formed)
        (lam_equal_inv facts formed same)

end Refutation

/-! ## Reading the shape -/

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]

/-- Read a carrying by a codomain with its bound variable merged into `x`, when the domain is `D`. -/
def carriedMerge? (again : {k : Nat} → (x : Fin k) → (D V T : Tm Head k) → Option (PLift (Carried x D true V T)))
    (isPi : Bool) {n : Nat} (x : Fin n) (D V A : Tm Head n) (B : Tm Head (n + 1)) :
    Option (PLift (Carried x D true V (binder isPi A B))) :=
  if domain : A = D then
    if back : Presentation.rename (mergeAt x) B = V then
      some ⟨by subst domain; subst back; exact .codomain isPi (.here _ _ _)⟩
    else
      match again x D V (Presentation.rename (mergeAt x) B) with
      | some inner => some ⟨by subst domain; exact .codomain isPi inner.down⟩
      | none => none
  else none

/-- Read a carrying by a Π or Σ type: by its domain, by its codomain with the bound variable merged, or by its
codomain past the bound variable. -/
def carriedBinder? (again : {k : Nat} → (x : Fin k) → (D V T : Tm Head k) → Option (PLift (Carried x D true V T)))
    (isPi : Bool) {n : Nat} (x : Fin n) (D V A : Tm Head n) (B : Tm Head (n + 1)) :
    Option (PLift (Carried x D true V (binder isPi A B))) :=
  if same : A = V then some ⟨by subst same; exact .domain isPi (.here _ _ _)⟩
  else
    match again x D V A with
    | some inner => some ⟨.domain isPi inner.down⟩
    | none =>
        match carriedMerge? again isPi x D V A B with
        | some found => some found
        | none =>
            if weakened : B = Presentation.rename wk V then
              some ⟨by subst weakened; exact .weak isPi (.here _ _ _)⟩
            else
              match again x.succ (Presentation.rename wk D) (Presentation.rename wk V) B with
              | some inner => some ⟨.weak isPi inner.down⟩
              | none => none

/-- **Read a carrying past at least one former**, with its proof, in at most the given number of steps. -/
def carried? : Nat → {n : Nat} → (x : Fin n) → (D V T : Tm Head n) → Option (PLift (Carried x D true V T))
  | 0, _, _, _, _, _ => none
  | steps + 1, _, x, D, V, .pi A B =>
      carriedBinder? (fun x D V T => carried? steps x D V T) true x D V A B
  | steps + 1, _, x, D, V, .sigma A B =>
      carriedBinder? (fun x D V T => carried? steps x D V T) false x D V A B
  | steps + 1, _, x, D, V, .id A _ _ =>
      if same : A = V then some ⟨by subst same; exact .carrier (.here _ _ _)⟩
      else (carried? steps x D V A).map fun inner => ⟨.carrier inner.down⟩
  | _ + 1, _, _, _, _, _ => none

/-- Read the sides below the abstractions, for a variable and the code of its type, in at most the given number of
steps: an abstraction of the type of the variable is merged into it when the merged sides are read, and passed
otherwise. -/
def held? : Nat → {n : Nat} → (x : Fin n) → (D annotation left right : Tm Head n) →
    Option (PLift (Held S.R x D annotation left right))
  | _, _, x, D, .head u, V, T =>
      if universal : S.R.isUniverse u then
        match carried? (nodes T) x D V T with
        | some carried => some ⟨.stop universal carried.down⟩
        | none => none
      else none
  | steps + 1, _, x, D, .pi A C, .lam V, .lam T =>
      let under : Option (PLift (Held S.R x D (.pi A C) (.lam V) (.lam T))) :=
        (held? steps x.succ (Presentation.rename wk D) C V T).map fun inner => ⟨.bind inner.down⟩
      if domain : A = D then
        match held? steps x D (Presentation.rename (mergeAt x) C) (Presentation.rename (mergeAt x) V)
            (Presentation.rename (mergeAt x) T) with
        | some inner => some ⟨by subst domain; exact .merge inner.down⟩
        | none => under
      else under
  | _, _, _, _, _, _, _ => none

/-- **Read the shape from three codes**, with its proof; no budget. The outermost abstraction that is held is taken. -/
def underBound? : {n : Nat} → (annotation left right : Tm Head n) →
    Option (PLift (UnderBound S.R annotation left right))
  | _, .pi A C, .lam V, .lam T =>
      match held? (S := S) (nodes C + 1) 0 (Presentation.rename wk A) C V T with
      | some inner => some ⟨.here inner.down⟩
      | none =>
          match underBound? C V T with
          | some inner => some ⟨.bind inner.down⟩
          | none => none
  | _, _, _, _ => none

/-- Try the abstractions in scope whose type has the code `A`, for a reading that uses one. -/
def firstLocal? {n : Nat} {α : Type} (all : Locals Head n) (A : Tm Head n)
    (attempt : (x : Fin n) → (x, A) ∈ all → Option α) :
    (rest : Locals Head n) → (∀ entry ∈ rest, entry ∈ all) → Option α
  | [], _ => none
  | entry :: rest, inside =>
      if same : entry.2 = A then
        match attempt entry.1 (by rw [← same]; exact inside entry List.mem_cons_self) with
        | some found => some found
        | none => firstLocal? all A attempt rest fun other member => inside other (List.mem_cons_of_mem _ member)
      else firstLocal? all A attempt rest fun other member => inside other (List.mem_cons_of_mem _ member)

/-- Read a carrying by a Π or Σ type with the abstractions in scope: by its domain, by its codomain with the bound
variable replaced by an abstraction of the domain's type, or by its codomain past the bound variable. -/
def carriedInBinder? (again : {k : Nat} → (locals : Locals Head k) → (V T : Tm Head k) →
      Option (PLift (CarriedIn locals true V T)))
    (isPi : Bool) {n : Nat} (locals : Locals Head n) (V A : Tm Head n) (B : Tm Head (n + 1)) :
    Option (PLift (CarriedIn locals true V (binder isPi A B))) :=
  if same : A = V then some ⟨by subst same; exact .domain isPi (.here _ _)⟩
  else
    match again locals V A with
    | some inner => some ⟨.domain isPi inner.down⟩
    | none =>
        match firstLocal? locals A (fun x member =>
            if back : Presentation.rename (mergeAt x) B = V then
              some (⟨by subst back; exact .codomain isPi member (.here _ _)⟩ :
                PLift (CarriedIn locals true V (binder isPi A B)))
            else
              match again locals V (Presentation.rename (mergeAt x) B) with
              | some inner => some ⟨.codomain isPi member inner.down⟩
              | none => none) locals (fun _ member => member) with
        | some found => some found
        | none =>
            if weakened : B = Presentation.rename wk V then
              some ⟨by subst weakened; exact .weak isPi (.here _ _)⟩
            else
              match again (shiftLocals locals) (Presentation.rename wk V) B with
              | some inner => some ⟨.weak isPi inner.down⟩
              | none => none

/-- **Read a carrying with the abstractions in scope**, with its proof, in at most the given number of steps. -/
def carriedIn? : Nat → {n : Nat} → (locals : Locals Head n) → (V T : Tm Head n) →
    Option (PLift (CarriedIn locals true V T))
  | 0, _, _, _, _ => none
  | steps + 1, _, locals, V, .pi A B =>
      carriedInBinder? (fun locals V T => carriedIn? steps locals V T) true locals V A B
  | steps + 1, _, locals, V, .sigma A B =>
      carriedInBinder? (fun locals V T => carriedIn? steps locals V T) false locals V A B
  | steps + 1, _, locals, V, .id A _ _ =>
      if same : A = V then some ⟨by subst same; exact .carrier (.here _ _)⟩
      else (carriedIn? steps locals V A).map fun inner => ⟨.carrier inner.down⟩
  | _ + 1, _, _, _, _ => none

/-- **Read the sides below the abstractions with all of them in scope**, with its proof, in at most the given
number of steps: an abstraction is merged into an earlier one of its type when the merged sides are read, and added
to the abstractions in scope otherwise. -/
def heldIn? : Nat → {n : Nat} → (locals : Locals Head n) → (annotation left right : Tm Head n) →
    Option (PLift (HeldIn S.R locals annotation left right))
  | _, _, locals, .head u, V, T =>
      if universal : S.R.isUniverse u then
        match carriedIn? (nodes T) locals V T with
        | some carried => some ⟨.stop universal carried.down⟩
        | none => none
      else none
  | steps + 1, _, locals, .pi A C, .lam V, .lam T =>
      match firstLocal? locals A (fun x member =>
          match heldIn? steps locals (Presentation.rename (mergeAt x) C) (Presentation.rename (mergeAt x) V)
              (Presentation.rename (mergeAt x) T) with
          | some inner => some (⟨.merge member inner.down⟩ : PLift (HeldIn S.R locals (.pi A C) (.lam V) (.lam T)))
          | none => none) locals (fun _ member => member) with
      | some found => some found
      | none =>
          match heldIn? steps ((0, Presentation.rename wk A) :: shiftLocals locals) C V T with
          | some inner => some ⟨.bind inner.down⟩
          | none => none
  | _, _, _, _, _, _ => none

/-- Read a shape as it stands: the shape above, the tower's occurs check under abstractions, or the reading with
all the abstractions in scope. -/
def standing? {n : Nat} (annotation left right : Tm Head n) : Option (PLift (Merged S.R annotation left right)) :=
  match underBound? (S := S) annotation left right with
  | some found => some ⟨.bound found.down⟩
  | none =>
      if found : underInsideOccurs (S := S) annotation left right = true then
        some ⟨.inside (underInsideOccurs_sound _ _ _ found)⟩
      else
        match heldIn? (S := S) (nodes annotation + 1) [] annotation left right with
        | some found => some ⟨.inScope found.down⟩
        | none => none

/-- One step of the reading: merge the two outermost abstractions when they have one type, or go under the
outermost abstraction, and read again. -/
def mergeStep? (again : {n : Nat} → (annotation left right : Tm Head n) →
      Option (PLift (Merged S.R annotation left right))) :
    {n : Nat} → (annotation left right : Tm Head n) → Option (PLift (Merged S.R annotation left right))
  | _, .pi A (.pi A' C), .lam (.lam V), .lam (.lam T) =>
      if domain : A' = Presentation.rename wk A then
        match again (.pi A (Presentation.rename (mergeAt 0) C)) (.lam (Presentation.rename (mergeAt 0) V))
            (.lam (Presentation.rename (mergeAt 0) T)) with
        | some inner => some ⟨by subst domain; exact .merge inner.down⟩
        | none => (again (.pi A' C) (.lam V) (.lam T)).map fun inner => ⟨.bind inner.down⟩
      else (again (.pi A' C) (.lam V) (.lam T)).map fun inner => ⟨.bind inner.down⟩
  | _, .pi _ C, .lam V, .lam T => (again C V T).map fun inner => ⟨.bind inner.down⟩
  | _, _, _, _ => none

/-- **Read a merged shape from three codes**, with its proof, in at most the given number of steps. -/
def merged? : Nat → {n : Nat} → (annotation left right : Tm Head n) →
    Option (PLift (Merged S.R annotation left right))
  | 0, _, annotation, left, right => standing? annotation left right
  | steps + 1, _, annotation, left, right =>
      match standing? (S := S) annotation left right with
      | some found => some found
      | none => mergeStep? (fun annotation left right => merged? steps annotation left right) annotation left right

/-- **A store equation of a merged shape**, both sides at one annotation code. -/
structure BoundShape {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Type where
  same : equation.2.1.code = equation.1.1.code
  under : Merged S.R equation.1.1.code equation.1.2.code equation.2.2.code

/-- Read the shape from the codes of an equation; the steps are bounded by the size of the annotation. -/
def boundShape {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Option (BoundShape equation) :=
  if same : equation.2.1.code = equation.1.1.code then
    match merged? (S := S) (nodes equation.1.1.code) equation.1.1.code equation.1.2.code equation.2.2.code with
    | some found => some ⟨same, found.down⟩
    | none => none
  else none

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] in
include facts roots heads algebra rigid complete in
/-- **An equation of the shape has no solution at any later context.** -/
theorem BoundShape.refutes {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (shape : BoundShape equation)
    {Δ : Context S.R} (σ : Δ ⟶ Θ) : ¬ (frames S.levels).Solves σ equation := by
  intro solved
  rw [solves_raw] at solved
  have tLeft := equation.1.2.typed.substitute σ.typed
  have tRight := equation.2.2.typed.substitute σ.typed
  rw [shape.same] at tRight
  exact merged_not_equal facts roots heads algebra rigid complete (shape.under.subst _) Δ.formed tLeft tRight
    solved.2

/-- **The rule**: refute the store at the first equation of the shape, read in either orientation. -/
def boundSearch {Θ : Context S.R} : (problem : EquationStore (TotalTerm Θ)) →
    Option (PLift (¬ (frames S.levels).Solvable problem))
  | [] => none
  | equation :: rest =>
      match boundShape equation with
      | some shape => some ⟨fun ⟨_, σ, solved⟩ =>
          shape.refutes facts roots heads algebra rigid complete σ (solved equation List.mem_cons_self)⟩
      | none =>
          match boundShape (swap equation) with
          | some shape => some ⟨fun ⟨_, σ, solved⟩ =>
              shape.refutes facts roots heads algebra rigid complete σ
                ((solves_swap σ equation).mpr (solved equation List.mem_cons_self))⟩
          | none => (boundSearch rest).map fun absent =>
              ⟨fun ⟨Δ, σ, solved⟩ =>
                absent.down ⟨Δ, σ, fun other member => solved other (List.mem_cons_of_mem _ member)⟩⟩

end ContextualDependentOccursBound
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
