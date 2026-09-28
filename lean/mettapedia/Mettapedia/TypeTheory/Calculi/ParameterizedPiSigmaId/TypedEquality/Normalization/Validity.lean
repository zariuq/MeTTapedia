import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Uniqueness

/-!
# Validity

A substitution is valid from `Γ` into a formed context `Δ` when it sends each
variable of `Γ` to a reducible term of the substituted type of that variable.
Two substitutions are reducibly equal when they send each variable to
reducibly equal terms.

* A type is valid in `Γ` when every valid substitution makes it reducible, and
  reducibly equal substitutions make it reducibly equal.
* A term is valid at a valid type when every valid substitution makes it
  reducible, and reducibly equal substitutions make it reducibly equal.
* Two valid terms are validly equal when every valid substitution makes them
  reducibly equal.
* A context is valid when each entry is a valid type in the context before it.

Since a reducible type has one pack, validity quantifies over packs instead of
carrying them. Valid substitutions are closed under the worlds of the model:
renaming their target into a formed context keeps them valid.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-- The substitution for the variables before the last one. -/
abbrev tailSub {n m : Nat} (σ : Sub Head (n + 1) m) : Sub Head n m := fun i => σ i.succ

/-! ## Definitions -/

/-- Valid substitutions from `Γ` into `Δ`. -/
def ValidSubst (S : Setting Head L) :
    {n m : Nat} → Ctx Head n → Ctx Head m → Sub Head n m → Prop
  | _, _, .nil, Δ, _ => CtxFormed S.R Δ
  | _, _, .snoc Γ A, Δ, σ => ValidSubst S Γ Δ (tailSub σ) ∧
      ∃ P, Reducible S Δ (Presentation.subst (tailSub σ) A) P ∧ P.redTm (σ 0)

/-- Reducibly equal substitutions from `Γ` into `Δ`. -/
def EqSubst (S : Setting Head L) :
    {n m : Nat} → Ctx Head n → Ctx Head m → Sub Head n m → Sub Head n m → Prop
  | _, _, .nil, _, _, _ => True
  | _, _, .snoc Γ A, Δ, σ, σ' => EqSubst S Γ Δ (tailSub σ) (tailSub σ') ∧
      ∃ P, Reducible S Δ (Presentation.subst (tailSub σ) A) P ∧ P.eqTm (σ 0) (σ' 0)

/-- A valid type. -/
structure ValidTy (S : Setting Head L) {n : Nat} (Γ : Ctx Head n) (A : Tm Head n) : Prop where
  red : ∀ {m : Nat} {Δ : Ctx Head m} {σ : Sub Head n m}, ValidSubst S Γ Δ σ →
    ∃ P, Reducible S Δ (Presentation.subst σ A) P
  ext : ∀ {m : Nat} {Δ : Ctx Head m} {σ σ' : Sub Head n m}, ValidSubst S Γ Δ σ →
    ValidSubst S Γ Δ σ' → EqSubst S Γ Δ σ σ' →
    ∀ {P}, Reducible S Δ (Presentation.subst σ A) P → P.eqTy (Presentation.subst σ' A)

/-- A valid context: every entry is valid in the context before it. -/
def ValidCtx (S : Setting Head L) : {n : Nat} → Ctx Head n → Prop
  | _, .nil => True
  | _, .snoc Γ A => ValidCtx S Γ ∧ ValidTy S Γ A

/-- A valid term at a valid type. -/
structure ValidTm (S : Setting Head L) {n : Nat} (Γ : Ctx Head n) (t A : Tm Head n) :
    Prop where
  type : ValidTy S Γ A
  red : ∀ {m : Nat} {Δ : Ctx Head m} {σ : Sub Head n m}, ValidSubst S Γ Δ σ →
    ∀ {P}, Reducible S Δ (Presentation.subst σ A) P → P.redTm (Presentation.subst σ t)
  ext : ∀ {m : Nat} {Δ : Ctx Head m} {σ σ' : Sub Head n m}, ValidSubst S Γ Δ σ →
    ValidSubst S Γ Δ σ' → EqSubst S Γ Δ σ σ' →
    ∀ {P}, Reducible S Δ (Presentation.subst σ A) P →
      P.eqTm (Presentation.subst σ t) (Presentation.subst σ' t)

/-- Two valid terms that are validly equal. -/
structure ValidEq (S : Setting Head L) {n : Nat} (Γ : Ctx Head n) (t u A : Tm Head n) :
    Prop where
  left : ValidTm S Γ t A
  right : ValidTm S Γ u A
  eq : ∀ {m : Nat} {Δ : Ctx Head m} {σ : Sub Head n m}, ValidSubst S Γ Δ σ →
    ∀ {P}, Reducible S Δ (Presentation.subst σ A) P →
      P.eqTm (Presentation.subst σ t) (Presentation.subst σ u)

/-! ## Substitution identities -/

theorem subst_rename_wk {n m : Nat} (σ : Sub Head (n + 1) m) (A : Tm Head n) :
    Presentation.subst σ (Presentation.rename wk A) = Presentation.subst (tailSub σ) A :=
  subst_rename σ wk A

theorem tailSub_liftSub {n m : Nat} (σ : Sub Head n m) :
    tailSub (liftSub σ) = fun i => Presentation.rename wk (σ i) :=
  rfl

theorem tailSub_consSub {n m : Nat} (a : Tm Head m) (σ : Sub Head n m) :
    tailSub (consSub a σ) = σ :=
  rfl

/-- Substituting after lifting a renamed substitution under a binder, then
instantiating, is substituting with the extended substitution. -/
theorem inst0_rename_subst_liftSub {n m k : Nat} (a : Tm Head k) (ρ : Ren m k)
    (σ : Sub Head n m) (B : Tm Head (n + 1)) :
    inst0 a (Presentation.rename (liftRen ρ) (Presentation.subst (liftSub σ) B)) =
      Presentation.subst (consSub a fun i => Presentation.rename ρ (σ i)) B := by
  rw [subst_consSub, rename_subst]
  congr 1
  apply subst_ext
  intro i
  exact rename_liftSub ρ σ i

/-- Instantiating the lift of a substitution is the extended substitution. -/
theorem inst0_subst_liftSub {n m : Nat} (a : Tm Head m) (σ : Sub Head n m)
    (B : Tm Head (n + 1)) :
    inst0 a (Presentation.subst (liftSub σ) B) = Presentation.subst (consSub a σ) B :=
  (subst_consSub a σ B).symm

/-- The body of a binder, renamed past a fresh variable and instantiated at it. -/
theorem inst0_var_rename_liftRen_wk {n : Nat} (B : Tm Head (n + 1)) :
    inst0 (.var 0) (Presentation.rename (liftRen wk) B) = B := by
  unfold inst0
  rw [subst_rename]
  conv => rhs; rw [← subst_ids B]
  apply subst_ext
  intro i
  refine Fin.cases rfl (fun j => rfl) i

/-! ## Valid substitutions -/

theorem ValidSubst.formed {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {σ : Sub Head n m} (valid : ValidSubst S Γ Δ σ) : CtxFormed S.R Δ := by
  induction Γ with
  | nil => exact valid
  | snoc Γ A ih => exact ih valid.1

theorem ValidSubst.cons {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {σ : Sub Head n m}
    {A : Tm Head n} {a : Tm Head m} {P : Pack Head m} (valid : ValidSubst S Γ Δ σ)
    (reducible : Reducible S Δ (Presentation.subst σ A) P) (ha : P.redTm a) :
    ValidSubst S (.snoc Γ A) Δ (consSub a σ) :=
  ⟨valid, P, reducible, ha⟩

theorem EqSubst.cons {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {σ σ' : Sub Head n m}
    {A : Tm Head n} {a a' : Tm Head m} {P : Pack Head m} (equal : EqSubst S Γ Δ σ σ')
    (reducible : Reducible S Δ (Presentation.subst σ A) P) (ha : P.eqTm a a') :
    EqSubst S (.snoc Γ A) Δ (consSub a σ) (consSub a' σ') :=
  ⟨equal, P, reducible, ha⟩

/-- A valid substitution is reducibly equal to itself. -/
theorem ValidSubst.refl {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {σ : Sub Head n m} (valid : ValidSubst S Γ Δ σ) : EqSubst S Γ Δ σ σ := by
  induction Γ with
  | nil => trivial
  | snoc Γ A ih =>
      obtain ⟨tail, P, reducible, head⟩ := valid
      exact ⟨ih tail, P, reducible, reducible.reflexive.eqTm head⟩

section Laws

variable (laws : S.E.Laws S.R S.roles)
include laws

/-- Valid substitutions are closed under the worlds of the model. -/
theorem ValidSubst.weaken {n m k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {Θ : Ctx Head k} {σ : Sub Head n m} {ρ : Ren m k} (valid : ValidSubst S Γ Δ σ)
    (w : World S Δ Θ ρ) :
    ValidSubst S Γ Θ (fun i => Presentation.rename ρ (σ i)) := by
  induction Γ with
  | nil => exact w.2
  | snoc Γ A ih =>
      obtain ⟨tail, P, reducible, head⟩ := valid
      obtain ⟨P', reducible', weakened⟩ := reducible.weaken laws w
      refine ⟨ih tail, P', ?_, weakened.redTm head⟩
      rwa [rename_subst] at reducible'

/-- Equal substitutions are closed under the worlds of the model. -/
theorem EqSubst.weaken {n m k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {Θ : Ctx Head k} {σ σ' : Sub Head n m} {ρ : Ren m k} (equal : EqSubst S Γ Δ σ σ')
    (w : World S Δ Θ ρ) :
    EqSubst S Γ Θ (fun i => Presentation.rename ρ (σ i))
      (fun i => Presentation.rename ρ (σ' i)) := by
  induction Γ with
  | nil => trivial
  | snoc Γ A ih =>
      obtain ⟨tail, P, reducible, head⟩ := equal
      obtain ⟨P', reducible', weakened⟩ := reducible.weaken laws w
      refine ⟨ih tail, P', ?_, weakened.eqTm head⟩
      rwa [rename_subst] at reducible'

omit laws in
/-- A valid substitution sends each variable to a reducible term of its type. -/
theorem ValidSubst.lookup {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {σ : Sub Head n m} (valid : ValidSubst S Γ Δ σ) (i : Fin n) :
    ∃ P, Reducible S Δ (Presentation.subst σ (Ctx.lookup Γ i)) P ∧ P.redTm (σ i) := by
  induction Γ with
  | nil => exact Fin.elim0 i
  | snoc Γ A ih =>
      obtain ⟨tail, P, reducible, head⟩ := valid
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨P, by rwa [Ctx.lookup_snoc_zero, subst_rename_wk], head⟩
      · obtain ⟨Q, reducibleQ, hQ⟩ := ih tail j
        exact ⟨Q, by rwa [Ctx.lookup_snoc_succ, subst_rename_wk], hQ⟩

omit laws in
/-- Equal substitutions send each variable to reducibly equal terms. -/
theorem EqSubst.lookup {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {σ σ' : Sub Head n m} (equal : EqSubst S Γ Δ σ σ') (i : Fin n) :
    ∃ P, Reducible S Δ (Presentation.subst σ (Ctx.lookup Γ i)) P ∧ P.eqTm (σ i) (σ' i) := by
  induction Γ with
  | nil => exact Fin.elim0 i
  | snoc Γ A ih =>
      obtain ⟨tail, P, reducible, head⟩ := equal
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨P, by rwa [Ctx.lookup_snoc_zero, subst_rename_wk], head⟩
      · obtain ⟨Q, reducibleQ, hQ⟩ := ih tail j
        exact ⟨Q, by rwa [Ctx.lookup_snoc_succ, subst_rename_wk], hQ⟩

/-! ## Valid types -/

/-- Two valid substitutions that are equal give a valid type the same pack. -/
theorem ValidTy.pack_eq {n m : Nat} {Γ : Ctx Head n} {A : Tm Head n} (valid : ValidTy S Γ A)
    {Δ : Ctx Head m} {σ σ' : Sub Head n m} (vσ : ValidSubst S Γ Δ σ)
    (vσ' : ValidSubst S Γ Δ σ') (equal : EqSubst S Γ Δ σ σ') {P Q : Pack Head m}
    (reducible : Reducible S Δ (Presentation.subst σ A) P)
    (reducible' : Reducible S Δ (Presentation.subst σ' A) Q) : P = Q :=
  reducible.conv laws reducible' (valid.ext vσ vσ' equal reducible)

omit laws in
/-- A valid type stays valid past one more context entry. -/
theorem ValidTy.wk {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} (valid : ValidTy S Γ A) :
    ValidTy S (.snoc Γ B) (Presentation.rename wk A) := by
  refine ⟨fun vσ => ?_, fun vσ vσ' equal P reducible => ?_⟩
  · rw [subst_rename_wk]
    exact valid.red vσ.1
  · rw [subst_rename_wk] at reducible ⊢
    exact valid.ext vσ.1 vσ'.1 equal.1 reducible

omit laws in
/-- Every entry of a valid context is a valid type. -/
theorem ValidCtx.lookup {n : Nat} {Γ : Ctx Head n} (valid : ValidCtx S Γ) (i : Fin n) :
    ValidTy S Γ (Ctx.lookup Γ i) := by
  induction Γ with
  | nil => exact Fin.elim0 i
  | snoc Γ A ih =>
      obtain ⟨validΓ, validA⟩ := valid
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Ctx.lookup_snoc_zero]
        exact validA.wk
      · rw [Ctx.lookup_snoc_succ]
        exact (ih validΓ j).wk

/-- A fresh variable is a reducible term of the weakened type of its binder. -/
theorem Reducible.var_zero {n : Nat} {Δ : Ctx Head n} {A : Tm Head n} {P : Pack Head n}
    (reducible : Reducible S Δ A P) (formed : CtxFormed S.R Δ) :
    ∃ P', Reducible S (.snoc Δ A) (Presentation.rename wk A) P' ∧ Weakened P wk P' ∧
      P'.redTm (.var 0) ∧ World S Δ (.snoc Δ A) wk := by
  have w : World S Δ (.snoc Δ A) wk := ⟨CtxRen.wk Δ A, .snoc formed (reducible.escape laws).type⟩
  obtain ⟨P', reducible', weakened⟩ := reducible.weaken laws w
  have typing : Typed S.R (.snoc Δ A) (.var 0) (Presentation.rename wk A) := .var 0
  exact ⟨P', reducible', weakened, (reducible'.reflects laws).redTm (.var 0) typing
    (laws.convNe_var 0 typing), w⟩

/-- Lifting a valid substitution under a binder. -/
theorem ValidSubst.lift {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {σ : Sub Head n m}
    {A : Tm Head n} {P : Pack Head m} (valid : ValidSubst S Γ Δ σ)
    (reducible : Reducible S Δ (Presentation.subst σ A) P) :
    ValidSubst S (.snoc Γ A) (.snoc Δ (Presentation.subst σ A)) (liftSub σ) := by
  obtain ⟨P', reducible', _, var0, w⟩ := reducible.var_zero laws valid.formed
  refine ⟨valid.weaken laws w, P', ?_, var0⟩
  rwa [tailSub_liftSub, ← rename_subst]

/-- Lifting equal substitutions under a binder, in the context extended by the
first substitution. -/
theorem EqSubst.lift {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {σ σ' : Sub Head n m}
    {A : Tm Head n} {P : Pack Head m} (validA : ValidTy S Γ A) (vσ : ValidSubst S Γ Δ σ)
    (vσ' : ValidSubst S Γ Δ σ') (equal : EqSubst S Γ Δ σ σ')
    (reducible : Reducible S Δ (Presentation.subst σ A) P) :
    ValidSubst S (.snoc Γ A) (.snoc Δ (Presentation.subst σ A)) (liftSub σ') ∧
      EqSubst S (.snoc Γ A) (.snoc Δ (Presentation.subst σ A)) (liftSub σ) (liftSub σ') := by
  obtain ⟨P', reducible', weakened, var0, w⟩ := reducible.var_zero laws vσ.formed
  obtain ⟨Q, reducibleQ⟩ := validA.red vσ'
  have same : P = Q := validA.pack_eq laws vσ vσ' equal reducible reducibleQ
  subst same
  obtain ⟨Q', reducibleQ', _⟩ := reducibleQ.weaken laws w
  have sameW : P' = Q' := reducible'.conv laws reducibleQ'
    (weakened.eqTy (validA.ext vσ vσ' equal reducible))
  subst sameW
  refine ⟨⟨vσ'.weaken laws w, P', ?_, var0⟩, ⟨equal.weaken laws w, P', ?_, ?_⟩⟩
  · rwa [tailSub_liftSub, ← rename_subst]
  · rwa [tailSub_liftSub, ← rename_subst]
  · exact reducible'.reflexive.eqTm var0

/-- The identity substitution of a valid context is valid, and the context is
formed. -/
theorem ValidCtx.formed_ids {n : Nat} {Γ : Ctx Head n} (valid : ValidCtx S Γ) :
    CtxFormed S.R Γ ∧ ValidSubst S Γ Γ ids := by
  induction Γ with
  | nil => exact ⟨.nil, .nil⟩
  | snoc Γ A ih =>
      obtain ⟨validΓ, validA⟩ := valid
      obtain ⟨formed, vids⟩ := ih validΓ
      obtain ⟨P, reducible⟩ := validA.red vids
      rw [subst_ids] at reducible
      obtain ⟨P', reducible', _, var0, w⟩ := reducible.var_zero laws formed
      refine ⟨w.2, vids.weaken laws w, P', ?_, var0⟩
      change Reducible S (.snoc Γ A)
        (Presentation.subst (fun i => Presentation.rename wk (ids i)) A) P'
      rw [← rename_subst, subst_ids]
      exact reducible'

/-! ## Validly equal types -/

/-- Validly equal types: at every valid substitution the first is reducibly
equal to the second. -/
structure ValidTyEq (S : Setting Head L) {n : Nat} (Γ : Ctx Head n) (A B : Tm Head n) :
    Prop where
  left : ValidTy S Γ A
  right : ValidTy S Γ B
  eq : ∀ {m : Nat} {Δ : Ctx Head m} {σ : Sub Head n m}, ValidSubst S Γ Δ σ →
    ∀ {P}, Reducible S Δ (Presentation.subst σ A) P → P.eqTy (Presentation.subst σ B)

/-- Validly equal types have the same pack at every valid substitution. -/
theorem ValidTyEq.pack_eq {n m : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (equal : ValidTyEq S Γ A B) {Δ : Ctx Head m} {σ : Sub Head n m}
    (vσ : ValidSubst S Γ Δ σ) {P Q : Pack Head m}
    (reducible : Reducible S Δ (Presentation.subst σ A) P)
    (reducible' : Reducible S Δ (Presentation.subst σ B) Q) : P = Q :=
  reducible.conv laws reducible' (equal.eq vσ reducible)

/-- Validity at a type transfers to a validly equal type. -/
theorem ValidTm.conv {n : Nat} {Γ : Ctx Head n} {t A B : Tm Head n}
    (valid : ValidTm S Γ t A) (equal : ValidTyEq S Γ A B) : ValidTm S Γ t B := by
  refine ⟨equal.right, fun {m Δ σ} vσ P reducible => ?_, fun {m Δ σ σ'} vσ vσ' e P reducible => ?_⟩
  · obtain ⟨Q, reducibleA⟩ := equal.left.red vσ
    rw [← equal.pack_eq laws vσ reducibleA reducible]
    exact valid.red vσ reducibleA
  · obtain ⟨Q, reducibleA⟩ := equal.left.red vσ
    rw [← equal.pack_eq laws vσ reducibleA reducible]
    exact valid.ext vσ vσ' e reducibleA

/-- Valid equality at a type transfers to a validly equal type. -/
theorem ValidEq.conv {n : Nat} {Γ : Ctx Head n} {t u A B : Tm Head n}
    (valid : ValidEq S Γ t u A) (equal : ValidTyEq S Γ A B) : ValidEq S Γ t u B := by
  refine ⟨valid.left.conv laws equal, valid.right.conv laws equal,
    fun {m Δ σ} vσ P reducible => ?_⟩
  obtain ⟨Q, reducibleA⟩ := equal.left.red vσ
  rw [← equal.pack_eq laws vσ reducibleA reducible]
  exact valid.eq vσ reducibleA

omit laws in
theorem ValidTyEq.refl {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} (valid : ValidTy S Γ A) :
    ValidTyEq S Γ A A :=
  ⟨valid, valid, fun _ _ reducible => reducible.reflexive.eqTy⟩

theorem ValidTyEq.symm {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (equal : ValidTyEq S Γ A B) : ValidTyEq S Γ B A := by
  refine ⟨equal.right, equal.left, fun {m Δ σ} vσ P reducible => ?_⟩
  obtain ⟨Q, reducibleA⟩ := equal.left.red vσ
  rw [← equal.pack_eq laws vσ reducibleA reducible]
  exact reducibleA.reflexive.eqTy

/-! ## Instantiation -/

omit laws in
theorem subst_inst0_consSub {n m : Nat} (σ : Sub Head n m) (a : Tm Head n)
    (B : Tm Head (n + 1)) :
    Presentation.subst σ (inst0 a B) =
      Presentation.subst (consSub (Presentation.subst σ a) σ) B := by
  rw [subst_inst0, inst0_subst_liftSub]

omit laws in
/-- Extending a valid substitution by a valid term. -/
theorem ValidTm.extend {n m : Nat} {Γ : Ctx Head n} {a A : Tm Head n} (valid : ValidTm S Γ a A)
    {Δ : Ctx Head m} {σ : Sub Head n m} (vσ : ValidSubst S Γ Δ σ) :
    ValidSubst S (.snoc Γ A) Δ (consSub (Presentation.subst σ a) σ) := by
  obtain ⟨P, reducible⟩ := valid.type.red vσ
  exact vσ.cons reducible (valid.red vσ reducible)

omit laws in
/-- Extending equal substitutions by a valid term. -/
theorem ValidTm.extend_eq {n m : Nat} {Γ : Ctx Head n} {a A : Tm Head n}
    (valid : ValidTm S Γ a A) {Δ : Ctx Head m} {σ σ' : Sub Head n m}
    (vσ : ValidSubst S Γ Δ σ) (vσ' : ValidSubst S Γ Δ σ') (e : EqSubst S Γ Δ σ σ') :
    EqSubst S (.snoc Γ A) Δ (consSub (Presentation.subst σ a) σ)
      (consSub (Presentation.subst σ' a) σ') := by
  obtain ⟨P, reducible⟩ := valid.type.red vσ
  exact e.cons reducible (valid.ext vσ vσ' e reducible)

omit laws in
/-- Instantiating a valid type at a valid term. -/
theorem ValidTy.instantiate {n : Nat} {Γ : Ctx Head n} {A a : Tm Head n} {B : Tm Head (n + 1)}
    (validB : ValidTy S (.snoc Γ A) B) (valid : ValidTm S Γ a A) :
    ValidTy S Γ (inst0 a B) := by
  refine ⟨fun vσ => ?_, fun vσ vσ' e P reducible => ?_⟩
  · rw [subst_inst0_consSub]
    exact validB.red (valid.extend vσ)
  · rw [subst_inst0_consSub] at reducible ⊢
    exact validB.ext (valid.extend vσ) (valid.extend vσ') (valid.extend_eq vσ vσ' e)
      reducible

omit laws in
/-- Instantiating a valid term at a valid term. -/
theorem ValidTm.instantiate {n : Nat} {Γ : Ctx Head n} {A a : Tm Head n} {body B : Tm Head (n + 1)}
    (validBody : ValidTm S (.snoc Γ A) body B) (valid : ValidTm S Γ a A) :
    ValidTm S Γ (inst0 a body) (inst0 a B) := by
  refine ⟨validBody.type.instantiate valid, fun vσ P reducible => ?_,
    fun vσ vσ' e P reducible => ?_⟩
  · rw [subst_inst0_consSub] at reducible ⊢
    exact validBody.red (valid.extend vσ) reducible
  · rw [subst_inst0_consSub] at reducible
    rw [subst_inst0_consSub, subst_inst0_consSub]
    exact validBody.ext (valid.extend vσ) (valid.extend vσ') (valid.extend_eq vσ vσ' e)
      reducible

/-- A valid type over an extended context has the same pack at equal
substitutions extended by equal terms. -/
theorem ValidTy.pack_eq_cons {n m : Nat} {Γ : Ctx Head n} {A : Tm Head n}
    {B : Tm Head (n + 1)} (validA : ValidTy S Γ A) (validB : ValidTy S (.snoc Γ A) B)
    {Δ : Ctx Head m} {τ τ' : Sub Head n m} (vτ : ValidSubst S Γ Δ τ)
    (vτ' : ValidSubst S Γ Δ τ') (e : EqSubst S Γ Δ τ τ') {x x' : Tm Head m}
    (hx : (packOf S Δ (Presentation.subst τ A)).redTm x)
    (hx' : (packOf S Δ (Presentation.subst τ' A)).redTm x')
    (hxx : (packOf S Δ (Presentation.subst τ A)).eqTm x x') :
    packOf S Δ (Presentation.subst (consSub x τ) B) =
      packOf S Δ (Presentation.subst (consSub x' τ') B) := by
  obtain ⟨PA, rA⟩ := validA.red vτ
  obtain ⟨PA', rA'⟩ := validA.red vτ'
  have r₁ := rA.packOf_self laws
  have r₂ := rA'.packOf_self laws
  have vx := vτ.cons r₁ hx
  have vx' := vτ'.cons r₂ hx'
  have ex := e.cons r₁ hxx
  obtain ⟨PC, rC⟩ := validB.red vx
  obtain ⟨PC', rC'⟩ := validB.red vx'
  rw [← rC.eq_packOf laws, ← rC'.eq_packOf laws]
  exact validB.pack_eq laws vx vx' ex rC rC'

/-! ## Universes -/

/-- The pack of a universe. -/
theorem universe_pack {n : Nat} {Δ : Ctx Head n} {u : Head} (isUniverse : S.R.isUniverse u)
    (formed : CtxFormed S.R Δ) {P : Pack Head n} (reducible : Reducible S Δ (.head u) P) :
    P = universePack S (levelsBelow S (LevelOrder.succ (S.levels.level u))) Δ u :=
  reducible.unique laws (universe_logRel isUniverse formed).reducible

omit laws in
/-- A valid term of a universe is a valid type, reducible at the universe's
level. -/
theorem ValidTm.logRel_at_level {n m : Nat} {Γ : Ctx Head n} {A : Tm Head n} {u : Head}
    (valid : ValidTm S Γ A (.head u)) (isUniverse : S.R.isUniverse u) {Δ : Ctx Head m}
    {σ : Sub Head n m} (vσ : ValidSubst S Γ Δ σ) :
    ∃ P, LogRel S (S.levels.level u) Δ (Presentation.subst σ A) P := by
  have reducibleU := (universe_logRel (S := S) isUniverse vσ.formed).reducible
  have member := valid.red vσ reducibleU
  exact universePack_redTm_logRel (LevelOrder.lt_succ _) member

/-- A valid term of a universe is a valid type. -/
theorem ValidTm.validTy {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {u : Head}
    (valid : ValidTm S Γ A (.head u)) (isUniverse : S.R.isUniverse u) : ValidTy S Γ A := by
  refine ⟨fun vσ => ?_, fun {m Δ σ σ'} vσ vσ' equal P reducible => ?_⟩
  · obtain ⟨P, r⟩ := valid.logRel_at_level isUniverse vσ
    exact ⟨P, r.reducible⟩
  · have reducibleU := (universe_logRel (S := S) isUniverse vσ.formed).reducible
    have equalU := valid.ext vσ vσ' equal reducibleU
    obtain ⟨_, _, _, _, _, _, _, _, Q, r, eqQ⟩ := equalU
    have lower := (levelsBelow_iff S (LevelOrder.lt_succ _) Δ _ Q).mp r
    rwa [reducible.unique laws lower.reducible]

end Laws

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
