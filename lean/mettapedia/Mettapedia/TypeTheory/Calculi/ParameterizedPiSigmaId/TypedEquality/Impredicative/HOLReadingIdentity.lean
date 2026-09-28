import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.HOLReadingPointedTyping

/-!
# The equality algebra of the identity reading

Under the identity reading the decoder takes `holds (eq@A x y)` to
`Id A x y`. The equality rules of HOL are then realized in the selected judgment
by reflexivity and by identity elimination at code motives, with two
exceptions that stay assumptions of the package:

* reflexivity at a point is `refl l`. It proves `l = r` whenever `l` and `r`
  are typed-equal, so the β and η rules of HOL are realized by reflexivity;
* symmetry, transitivity, the forward direction of an equation between
  propositions, and congruence in the function and in the argument are
  transport of a code family along the identity evidence,
  `J A x (λ y _. holds (C y)) d y e` (`HOLReading.transport`). Every motive is
  the decoding of a code family, so it lands in the universe of proofs;
* function extensionality and propositional extensionality are not derivable
  from identity elimination. A reading may track them as declared constants of
  its package whose types are the decodings of the source axioms
  (`TrackedEquality`); the algebra uses them when they are present and
  otherwise declines. It never supplies a realizer for them.

The identity elimination the algebra needs is an interface of the package,
`HOLReading.CodeTransport`: transport of every code family along identity
evidence at a carrier.

**Results.** The algebra `HOLReading.identityRaw` commutes with substitution
(`identityRaw_natural`), its availability depends only on the types of a node
(`identityRaw_termUniform`), and under the laws of a reading with code
transport it is lawful (`identityRaw_lawful`), giving
`identityEqOperations : PointedOperations ρ`. Its compiler is exactly total on
the read proofs whose extensionality steps are tracked
(`identityEqOperations_isSome_iff`). Without the identity reading every
realization by reflexivity or transport is declined
(`identityRaw_declines_of_not_identity`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative

open Normalization
open Mettapedia.Logic

universe u v

variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}

namespace HOLReading

/-! ## Transport and the extensionality codes -/

section Terms

variable (ρ : HOLReading Head Base Const)

/-- Transport of the code family `C` along identity evidence `e : Id A x y`,
by the eliminator `J` at the motive `λ y _. holds (C y)`:
`J A x (λ y _. holds C) d y e`. -/
def transport (J : DeclName) {n : Nat} (A x : Tm Head n) (C : Tm Head (n + 1))
    (d y e : Tm Head n) : Tm Head n :=
  .app (.app (.app (.app (.app (.app (.const J) A) x)
    (.lam (.lam (ρ.holdsOf (Presentation.rename wk C))))) d) y) e

/-- The code of function extensionality at `σ ⇒ τ`:
`∀ f g : σ ⇒ τ. (∀ x : σ. f x = g x) → f = g`. -/
def funextCode (σ τ : HOL.Ty Base) {n : Nat} : Tm Head n :=
  ρ.allOf (.arr σ τ) (.lam (ρ.allOf (.arr σ τ) (.lam (ρ.impOf
    (ρ.allOf σ (.lam (ρ.eqOf τ (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0)))))
    (ρ.eqOf (.arr σ τ) (.var 1) (.var 0))))))

/-- The code of propositional extensionality:
`∀ p q : prop. (p → q) → (q → p) → p = q`. -/
def propextCode {n : Nat} : Tm Head n :=
  ρ.allOf .prop (.lam (ρ.allOf .prop (.lam (ρ.impOf (ρ.impOf (.var 1) (.var 0))
    (ρ.impOf (ρ.impOf (.var 0) (.var 1)) (ρ.eqOf .prop (.var 1) (.var 0)))))))

end Terms

/-- The source statement of function extensionality at `σ ⇒ τ`. -/
def funextFormula {Γ : HOL.Ctx Base} (σ τ : HOL.Ty Base) : HOL.Formula Const Γ :=
  .all (σ := .arr σ τ) (.all (σ := .arr σ τ) (.imp
    (.all (σ := σ) (.eq (.app (.var (.vs (.vs .vz))) (.var .vz)) (.app (.var (.vs .vz)) (.var .vz))))
    (.eq (.var (.vs .vz)) (.var .vz))))

/-- The source statement of propositional extensionality. -/
def propextFormula {Γ : HOL.Ctx Base} : HOL.Formula Const Γ :=
  .all (σ := .prop) (.all (σ := .prop) (.imp (.imp (.var (.vs .vz)) (.var .vz))
    (.imp (.imp (.var .vz) (.var (.vs .vz))) (.eq (.var (.vs .vz)) (.var .vz)))))

variable {ρ : HOLReading Head Base Const}

/-- The extensionality codes are the readings of the source axioms. -/
theorem term_funextFormula {Γ : HOL.Ctx Base} (σ τ : HOL.Ty Base) :
    ρ.term (funextFormula (Const := Const) (Γ := Γ) σ τ) = some (ρ.funextCode σ τ) :=
  rfl

theorem term_propextFormula {Γ : HOL.Ctx Base} :
    ρ.term (propextFormula (Const := Const) (Γ := Γ)) = some ρ.propextCode :=
  rfl

theorem liftClosed_funextCode {n : Nat} (σ τ : HOL.Ty Base) :
    (liftClosed (ρ.funextCode σ τ : Tm Head 0) : Tm Head n) = ρ.funextCode σ τ :=
  rfl

theorem liftClosed_propextCode {n : Nat} :
    (liftClosed (ρ.propextCode : Tm Head 0) : Tm Head n) = ρ.propextCode :=
  rfl

theorem subst_transport (J : DeclName) {n m : Nat} (σ : Sub Head n m) (A x : Tm Head n)
    (C : Tm Head (n + 1)) (d y e : Tm Head n) :
    Presentation.subst σ (ρ.transport J A x C d y e) =
      ρ.transport J (Presentation.subst σ A) (Presentation.subst σ x)
        (Presentation.subst (liftSub σ) C) (Presentation.subst σ d) (Presentation.subst σ y)
        (Presentation.subst σ e) := by
  simp only [transport, Presentation.subst, subst_liftSub_wk]

/-! ## The interface: transport at code motives -/

/-- **Identity elimination at code motives.** The eliminator `J` transports
every code family along identity evidence at a type of the universe of proofs. -/
structure CodeTransport (ρ : HOLReading Head Base Const) (J : DeclName) : Prop where
  typed : ∀ {n : Nat} {Γ : Ctx Head n} {A x y d e : Tm Head n} {C : Tm Head (n + 1)},
    Typed ρ.rules Γ A ρ.U → Typed ρ.rules Γ x A → Typed ρ.rules Γ y A →
    Typed ρ.rules (.snoc Γ A) C ρ.codes.propT →
    Typed ρ.rules Γ d (ρ.holdsOf (inst0 x C)) → Typed ρ.rules Γ e (.id A x y) →
    Typed ρ.rules Γ (ρ.transport J A x C d y e) (ρ.holdsOf (inst0 y C))

end HOLReading

/-! ## Tracked extensionality -/

/-- Function extensionality (at each type) and propositional extensionality
as tracked assumptions: optional constants, declared in the reading's package
at the decodings of the source axioms. A tracked constant is never given a
realizer. -/
structure TrackedEquality (ρ : HOLReading Head Base Const) where
  funext : HOL.Ty Base → HOL.Ty Base → Option DeclName
  propext : Option DeclName
  funext_declared : ∀ {σ τ : HOL.Ty Base} {c : DeclName}, funext σ τ = some c →
    ρ.rules.constantType c = some (ρ.holdsOf (ρ.funextCode σ τ))
  propext_declared : ∀ {c : DeclName}, propext = some c →
    ρ.rules.constantType c = some (ρ.holdsOf ρ.propextCode)

/-- No extensionality is tracked. -/
def TrackedEquality.untracked (ρ : HOLReading Head Base Const) : TrackedEquality ρ where
  funext := fun _ _ => none
  propext := none
  funext_declared := fun h => nomatch h
  propext_declared := fun h => nomatch h

namespace HOLReading

/-! ## The algebra -/

section Algebra

variable (ρ : HOLReading Head Base Const) (J : DeclName)

/-- The equality algebra of the identity reading. Reflexivity and transport
are offered only under the identity reading; the extensionality steps only
when their constants are tracked. -/
def identityRaw (funext : HOL.Ty Base → HOL.Ty Base → Option DeclName)
    (propext : Option DeclName) : PointedRaw Head Base where
  reflexivity := none
  pointed := fun _ l => if ρ.codes.identity then some (.refl l) else none
  symmetry := fun {n} τ l r e =>
    if ρ.codes.identity then
      some (ρ.transport J (ρ.carrierAt n τ) l (ρ.eqOf τ (.var 0) (Presentation.rename wk l))
        (.refl l) r e)
    else none
  transitivity := fun {n} τ l m r e₁ e₂ =>
    if ρ.codes.identity then
      some (ρ.transport J (ρ.carrierAt n τ) m (ρ.eqOf τ (Presentation.rename wk l) (.var 0))
        e₁ r e₂)
    else none
  propositionExtensionality := fun p q f b =>
    propext.map fun c => .app (.app (.app (.app (.const c) p) q) f) b
  propositionForward := fun p q e =>
    if ρ.codes.identity then
      some (.lam (ρ.transport J ρ.codes.propT (Presentation.rename wk p) (.var 0) (.var 0)
        (Presentation.rename wk q) (Presentation.rename wk e)))
    else none
  functionCongruence := fun {n} σ τ f g a e =>
    if ρ.codes.identity then
      some (ρ.transport J (ρ.carrierAt n (.arr σ τ)) f
        (ρ.eqOf τ (.app (Presentation.rename wk f) (Presentation.rename wk a))
          (.app (.var 0) (Presentation.rename wk a)))
        (.refl (.app f a)) g e)
    else none
  argumentCongruence := fun {n} σ τ f l r e =>
    if ρ.codes.identity then
      some (ρ.transport J (ρ.carrierAt n σ) l
        (ρ.eqOf τ (.app (Presentation.rename wk f) (Presentation.rename wk l))
          (.app (Presentation.rename wk f) (.var 0)))
        (.refl (.app f l)) r e)
    else none
  functionExtensionality := fun σ τ f g pw =>
    (funext σ τ).map fun c => .app (.app (.app (.const c) f) g) pw

end Algebra

variable {ρ : HOLReading Head Base Const} {J : DeclName}
  {funext : HOL.Ty Base → HOL.Ty Base → Option DeclName} {propext : Option DeclName}

/-! ### Naturality -/

/-- **Substitution naturality** of the identity algebra. -/
theorem identityRaw_natural : (ρ.identityRaw J funext propext).Natural where
  reflexivity := fun _ => rfl
  pointed := by
    intro n m σ τ l
    cases h : ρ.codes.identity <;> simp [identityRaw, h, Presentation.subst]
  symmetry := by
    intro n m σ τ l r e
    cases h : ρ.codes.identity
    · simp [identityRaw, h]
    · simp only [identityRaw, h, if_true, Option.map_some, subst_transport, subst_carrierAt,
        Presentation.subst, subst_liftSub_wk]
      rfl
  transitivity := by
    intro n m σ τ l mid r e₁ e₂
    cases h : ρ.codes.identity
    · simp [identityRaw, h]
    · simp only [identityRaw, h, if_true, Option.map_some, subst_transport, subst_carrierAt,
        Presentation.subst, subst_liftSub_wk]
      rfl
  propositionExtensionality := by
    intro n m σ p q f b
    simp only [identityRaw]
    cases propext <;> simp [Presentation.subst]
  propositionForward := by
    intro n m σ p q e
    cases h : ρ.codes.identity
    · simp [identityRaw, h]
    · simp only [identityRaw, h, if_true, Option.map_some, Presentation.subst, subst_transport,
        subst_liftSub_wk]
      rfl
  functionCongruence := by
    intro n m σ s τ f g a e
    cases h : ρ.codes.identity
    · simp [identityRaw, h]
    · simp only [identityRaw, h, if_true, Option.map_some, subst_transport, subst_carrierAt,
        Presentation.subst, subst_liftSub_wk]
      rfl
  argumentCongruence := by
    intro n m σ s τ f l r e
    cases h : ρ.codes.identity
    · simp [identityRaw, h]
    · simp only [identityRaw, h, if_true, Option.map_some, subst_transport, subst_carrierAt,
        Presentation.subst, subst_liftSub_wk]
      rfl
  functionExtensionality := by
    intro n m σ s τ f g pw
    simp only [identityRaw]
    cases funext s τ <;> simp [Presentation.subst]

/-! ### Availability -/

/-- The availability of the identity algebra depends only on the types of a
node. -/
theorem identityRaw_termUniform : (ρ.identityRaw J funext propext).TermUniform := by
  intro q
  cases q with
  | pointed τ =>
      cases h : ρ.codes.identity
      · exact .inr fun l => by simp [identityRaw, h]
      · exact .inl fun l => by simp [identityRaw, h]
  | symmetry τ =>
      cases h : ρ.codes.identity
      · exact .inr fun l r e => by simp [identityRaw, h]
      · exact .inl fun l r e => by simp [identityRaw, h]
  | transitivity τ =>
      cases h : ρ.codes.identity
      · exact .inr fun l m r e₁ e₂ => by simp [identityRaw, h]
      · exact .inl fun l m r e₁ e₂ => by simp [identityRaw, h]
  | propositionExtensionality =>
      cases propext
      · exact .inr fun p q f b => by simp [identityRaw]
      · exact .inl fun p q f b => by simp [identityRaw]
  | propositionForward =>
      cases h : ρ.codes.identity
      · exact .inr fun p q e => by simp [identityRaw, h]
      · exact .inl fun p q e => by simp [identityRaw, h]
  | functionCongruence σ τ =>
      cases h : ρ.codes.identity
      · exact .inr fun f g a e => by simp [identityRaw, h]
      · exact .inl fun f g a e => by simp [identityRaw, h]
  | argumentCongruence σ τ =>
      cases h : ρ.codes.identity
      · exact .inr fun f l r e => by simp [identityRaw, h]
      · exact .inl fun f l r e => by simp [identityRaw, h]
  | functionExtensionality σ τ =>
      cases h : funext σ τ
      · exact .inr fun f g pw => by simp [identityRaw, h]
      · exact .inl fun f g pw => by simp [identityRaw, h]

/-- Under the identity reading, a request is available exactly when it is not
an extensionality step whose constant is untracked. -/
theorem identityRaw_available (identity : ρ.codes.identity = true) (q : Request Base) :
    (ρ.identityRaw J funext propext).Available q ↔
      (q = .propositionExtensionality → propext.isSome) ∧
        (∀ σ τ, q = .functionExtensionality σ τ → (funext σ τ).isSome) := by
  have z : Tm Head 0 := .const .anonymous
  cases q with
  | propositionExtensionality =>
      constructor
      · intro available
        refine ⟨fun _ => ?_, fun σ τ same => nomatch same⟩
        have h := available z z z z
        simp only [identityRaw, Option.isSome_map] at h
        exact h
      · rintro ⟨tracked, -⟩ n p q f b
        obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (tracked rfl)
        simp [identityRaw, hc]
  | functionExtensionality σ τ =>
      constructor
      · intro available
        refine ⟨(fun same => nomatch same), fun σ' τ' same => ?_⟩
        cases same
        have h := available z z z
        simp only [identityRaw, Option.isSome_map] at h
        exact h
      · rintro ⟨-, tracked⟩ n f g pw
        obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (tracked σ τ rfl)
        simp [identityRaw, hc]
  | _ => simp [PointedRaw.Available, identityRaw, identity]

/-- **Without the identity reading** the algebra declines every step realized
by reflexivity or transport. -/
theorem identityRaw_declines_of_not_identity (notIdentity : ρ.codes.identity = false) :
    ∀ q : Request Base, q ≠ .propositionExtensionality →
      (∀ σ τ, q ≠ .functionExtensionality σ τ) → (ρ.identityRaw J funext propext).Refuses q := by
  intro q notPropext notFunext
  cases q with
  | propositionExtensionality => exact absurd rfl notPropext
  | functionExtensionality σ τ => exact absurd rfl (notFunext σ τ)
  | _ => simp [PointedRaw.Refuses, identityRaw, notIdentity]

/-! ## The laws -/

theorem inst0_eqOf_var_wk {n : Nat} {τ : HOL.Ty Base} (x l : Tm Head n) :
    inst0 x (ρ.eqOf τ (.var 0) (Presentation.rename wk l)) = ρ.eqOf τ x l := by
  change ρ.eqOf τ x (inst0 x (Presentation.rename wk l)) = _
  rw [inst0_rename_wk]

theorem inst0_eqOf_wk_var {n : Nat} {τ : HOL.Ty Base} (x l : Tm Head n) :
    inst0 x (ρ.eqOf τ (Presentation.rename wk l) (.var 0)) = ρ.eqOf τ l x := by
  change ρ.eqOf τ (inst0 x (Presentation.rename wk l)) x = _
  rw [inst0_rename_wk]

theorem inst0_eqOf_function {n : Nat} {τ : HOL.Ty Base} (x f a : Tm Head n) :
    inst0 x (ρ.eqOf τ (.app (Presentation.rename wk f) (Presentation.rename wk a))
      (.app (.var 0) (Presentation.rename wk a))) = ρ.eqOf τ (.app f a) (.app x a) := by
  change ρ.eqOf τ (.app (inst0 x (Presentation.rename wk f)) (inst0 x (Presentation.rename wk a)))
    (.app x (inst0 x (Presentation.rename wk a))) = _
  rw [inst0_rename_wk, inst0_rename_wk]

theorem inst0_eqOf_argument {n : Nat} {τ : HOL.Ty Base} (x f l : Tm Head n) :
    inst0 x (ρ.eqOf τ (.app (Presentation.rename wk f) (Presentation.rename wk l))
      (.app (Presentation.rename wk f) (.var 0))) = ρ.eqOf τ (.app f l) (.app f x) := by
  change ρ.eqOf τ (.app (inst0 x (Presentation.rename wk f)) (inst0 x (Presentation.rename wk l)))
    (.app (inst0 x (Presentation.rename wk f)) x) = _
  rw [inst0_rename_wk, inst0_rename_wk]

/-- A variable of a carrier, seen past one more binder. -/
theorem var_succ_carrier {n : Nat} {Γ : Ctx Head n} {i : Fin n} {τ : HOL.Ty Base}
    {X : Tm Head n} (h : Typed ρ.rules Γ (.var i) (ρ.carrierAt n τ)) :
    Typed ρ.rules (.snoc Γ X) (.var i.succ) (ρ.carrierAt (n + 1) τ) := by
  simpa only [rename_carrierAt, Presentation.rename, wk] using h.weaken (extension := X)

theorem weaken_carrier {n : Nat} {Γ : Ctx Head n} {t : Tm Head n} {τ : HOL.Ty Base}
    {X : Tm Head n} (h : Typed ρ.rules Γ t (ρ.carrierAt n τ)) :
    Typed ρ.rules (.snoc Γ X) (Presentation.rename wk t) (ρ.carrierAt (n + 1) τ) := by
  simpa only [rename_carrierAt] using h.weaken (extension := X)

namespace Laws

variable (L : ρ.Laws)
include L

/-- A lawful reading has the identity reading. -/
theorem identity : ρ.codes.identity = true := by
  have h := L.equation .prop
  unfold Codes.equationCarrier at h
  cases hid : ρ.codes.identity
  · simp [hid] at h
  · rfl

/-- Evidence for an equation code is identity evidence. -/
theorem identity_of_holds {n : Nat} {Γ : Ctx Head n} {τ : HOL.Ty Base} {l r e : Tm Head n}
    (hl : Typed ρ.rules Γ l (ρ.carrierAt n τ)) (hr : Typed ρ.rules Γ r (ρ.carrierAt n τ))
    (he : Typed ρ.rules Γ e (ρ.holdsOf (ρ.eqOf τ l r))) :
    Typed ρ.rules Γ e (.id (ρ.carrierAt n τ) l r) :=
  .conv he (L.equal_holds_eq hl hr) L.proofs_universe

/-- The code of function extensionality is a code. -/
theorem funextCode_typed {n : Nat} {Γ : Ctx Head n} (σ τ : HOL.Ty Base) :
    Typed ρ.rules Γ (ρ.funextCode σ τ) ρ.codes.propT := by
  exact typed_closed (Γ := Γ) (L.term_typed (ρ.term_funextFormula (Const := Const) (Γ := []) σ τ))

theorem propextCode_typed {n : Nat} {Γ : Ctx Head n} :
    Typed ρ.rules Γ ρ.propextCode ρ.codes.propT := by
  exact typed_closed (Γ := Γ) (L.term_typed (ρ.term_propextFormula (Const := Const) (Γ := [])))

/-- A tracked constant is typed at the decoding of its axiom. -/
theorem declared_typed {n : Nat} {Γ : Ctx Head n} {c : DeclName} {code : ∀ {k : Nat}, Tm Head k}
    (declared : ρ.rules.constantType c = some (ρ.holdsOf (code (k := 0))))
    (codeTyped : Typed ρ.rules .nil (code (k := 0)) ρ.codes.propT)
    (lifted : (liftClosed (code (k := 0)) : Tm Head n) = code) :
    Typed ρ.rules Γ (.const c) (ρ.holdsOf code) := by
  have h := Derivable.const (Γ := Γ) declared (L.holdsOf_typed codeTyped) L.proofs_universe
  change Typed ρ.rules Γ (.const c) (ρ.holdsOf (liftClosed (code (k := 0)))) at h
  rwa [lifted] at h

/-- **The identity algebra is lawful** under the laws of the reading, code
transport, and the declarations of the tracked constants. -/
theorem identityRaw_lawful (T : ρ.CodeTransport J) (tracked : TrackedEquality ρ) :
    (ρ.identityRaw J tracked.funext tracked.propext).Lawful ρ where
  reflexivity := fun h => nomatch h
  pointed := by
    intro n Γ τ l r out success hl hr hlr
    simp only [identityRaw, L.identity, if_true, Option.some.injEq] at success
    subst success
    have identities : Equal ρ.rules Γ (.id (ρ.carrierAt n τ) l l) (.id (ρ.carrierAt n τ) l r) ρ.U :=
      .idCong (.refl (L.carrierAt_typed τ)) L.proofs_universe (.refl hl) hlr
    exact .conv (.reflIntro hl) (.trans identities (.symm (L.equal_holds_eq hl hr)))
      L.proofs_universe
  symmetry := by
    intro n Γ τ l r e out success hl hr he
    simp only [identityRaw, L.identity, if_true, Option.some.injEq] at success
    subst success
    have family : Typed ρ.rules (.snoc Γ (ρ.carrierAt n τ))
        (ρ.eqOf τ (.var 0) (Presentation.rename wk l)) ρ.codes.propT :=
      L.eqOf_typed (ρ.var_carrier τ) (weaken_carrier hl)
    have base : Typed ρ.rules Γ (.refl l)
        (ρ.holdsOf (inst0 l (ρ.eqOf τ (.var 0) (Presentation.rename wk l)))) := by
      rw [inst0_eqOf_var_wk]
      exact L.reflIntro hl
    have moved := T.typed (L.carrierAt_typed τ) hl hr family base (L.identity_of_holds hl hr he)
    rwa [inst0_eqOf_var_wk] at moved
  transitivity := by
    intro n Γ τ l m r e₁ e₂ out success hl hm hr he₁ he₂
    simp only [identityRaw, L.identity, if_true, Option.some.injEq] at success
    subst success
    have family : Typed ρ.rules (.snoc Γ (ρ.carrierAt n τ))
        (ρ.eqOf τ (Presentation.rename wk l) (.var 0)) ρ.codes.propT :=
      L.eqOf_typed (weaken_carrier hl) (ρ.var_carrier τ)
    have base : Typed ρ.rules Γ e₁
        (ρ.holdsOf (inst0 m (ρ.eqOf τ (Presentation.rename wk l) (.var 0)))) := by
      rw [inst0_eqOf_wk_var]
      exact he₁
    have moved := T.typed (L.carrierAt_typed τ) hm hr family base (L.identity_of_holds hm hr he₂)
    rwa [inst0_eqOf_wk_var] at moved
  propositionExtensionality := by
    intro n Γ p q f b out success hp hq hf hb
    simp only [identityRaw] at success
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp success
    have constant : Typed ρ.rules Γ (.const c) (ρ.holdsOf ρ.propextCode) :=
      L.declared_typed (code := fun {_} => ρ.propextCode) (tracked.propext_declared hc)
        L.propextCode_typed liftClosed_propextCode
    have outer : Typed ρ.rules (.snoc Γ (ρ.carrierAt n .prop))
        (ρ.allOf .prop (.lam (ρ.impOf (ρ.impOf (.var 1) (.var 0))
          (ρ.impOf (ρ.impOf (.var 0) (.var 1)) (ρ.eqOf .prop (.var 1) (.var 0))))))
        ρ.codes.propT := by
      have inner : Typed ρ.rules (.snoc (.snoc Γ (ρ.carrierAt n .prop))
          (ρ.carrierAt (n + 1) .prop))
          (ρ.impOf (ρ.impOf (.var 1) (.var 0))
            (ρ.impOf (ρ.impOf (.var 0) (.var 1)) (ρ.eqOf .prop (.var 1) (.var 0))))
          ρ.codes.propT := by
        have first : Typed ρ.rules (.snoc (.snoc Γ (ρ.carrierAt n .prop))
            (ρ.carrierAt (n + 1) .prop)) (.var 1) ρ.codes.propT :=
          var_succ_carrier (τ := .prop) (ρ.var_carrier .prop)
        have second : Typed ρ.rules (.snoc (.snoc Γ (ρ.carrierAt n .prop))
            (ρ.carrierAt (n + 1) .prop)) (.var 0) ρ.codes.propT := ρ.var_carrier .prop
        exact L.impOf_typed (L.impOf_typed first second)
          (L.impOf_typed (L.impOf_typed second first) (L.eqOf_typed (τ := .prop) first second))
      exact L.allOf_typed (.lamIntro (L.pi_typed (L.carrierAt_typed .prop) L.prop_typed)
        L.proofs_universe inner)
    have atP := L.allElim outer constant hp
    have middle : Typed ρ.rules (.snoc Γ (ρ.carrierAt n .prop))
        (ρ.impOf (ρ.impOf (Presentation.rename wk p) (.var 0))
          (ρ.impOf (ρ.impOf (.var 0) (Presentation.rename wk p))
            (ρ.eqOf .prop (Presentation.rename wk p) (.var 0)))) ρ.codes.propT := by
      have first : Typed ρ.rules (.snoc Γ (ρ.carrierAt n .prop)) (Presentation.rename wk p)
          ρ.codes.propT := weaken_carrier (τ := .prop) hp
      have second : Typed ρ.rules (.snoc Γ (ρ.carrierAt n .prop)) (.var 0) ρ.codes.propT :=
        ρ.var_carrier .prop
      exact L.impOf_typed (L.impOf_typed first second)
        (L.impOf_typed (L.impOf_typed second first) (L.eqOf_typed (τ := .prop) first second))
    have atPQ := L.allElim middle atP hq
    have unfolded : inst0 q (ρ.impOf (ρ.impOf (Presentation.rename wk p) (.var 0))
        (ρ.impOf (ρ.impOf (.var 0) (Presentation.rename wk p))
          (ρ.eqOf .prop (Presentation.rename wk p) (.var 0)))) =
        ρ.impOf (ρ.impOf p q) (ρ.impOf (ρ.impOf q p) (ρ.eqOf .prop p q)) := by
      change ρ.impOf (ρ.impOf (inst0 q (Presentation.rename wk p)) q)
          (ρ.impOf (ρ.impOf q (inst0 q (Presentation.rename wk p)))
            (ρ.eqOf .prop (inst0 q (Presentation.rename wk p)) q)) = _
      rw [inst0_rename_wk]
    rw [unfolded] at atPQ
    have typedPQ : Typed ρ.rules Γ (ρ.impOf p q) ρ.codes.propT := L.impOf_typed hp hq
    have typedQP : Typed ρ.rules Γ (ρ.impOf q p) ρ.codes.propT := L.impOf_typed hq hp
    have afterForward := L.impElim typedPQ
      (L.impOf_typed typedQP (L.eqOf_typed (τ := .prop) hp hq)) atPQ hf
    exact L.impElim typedQP (L.eqOf_typed (τ := .prop) hp hq) afterForward hb
  propositionForward := by
    intro n Γ p q e out success hp hq he
    simp only [identityRaw, L.identity, if_true, Option.some.injEq] at success
    subst success
    have extendedP : Typed ρ.rules (.snoc Γ (ρ.holdsOf p)) (Presentation.rename wk p)
        ρ.codes.propT := hp.weaken
    have extendedQ : Typed ρ.rules (.snoc Γ (ρ.holdsOf p)) (Presentation.rename wk q)
        ρ.codes.propT := hq.weaken
    have family : Typed ρ.rules (.snoc (.snoc Γ (ρ.holdsOf p)) ρ.codes.propT) (.var 0)
        ρ.codes.propT := Derivable.var 0
    have base : Typed ρ.rules (.snoc Γ (ρ.holdsOf p)) (.var 0)
        (ρ.holdsOf (inst0 (Presentation.rename wk p) (.var 0))) := Derivable.var 0
    have path : Typed ρ.rules (.snoc Γ (ρ.holdsOf p)) (Presentation.rename wk e)
        (.id ρ.codes.propT (Presentation.rename wk p) (Presentation.rename wk q)) :=
      (L.identity_of_holds (τ := .prop) hp hq he).weaken
    have moved := T.typed L.prop_typed extendedP extendedQ family base path
    exact L.impIntro hp hq moved
  functionCongruence := by
    intro n Γ σ τ f g a e out success hf hg ha he
    simp only [identityRaw, L.identity, if_true, Option.some.injEq] at success
    subst success
    have family : Typed ρ.rules (.snoc Γ (ρ.carrierAt n (.arr σ τ)))
        (ρ.eqOf τ (.app (Presentation.rename wk f) (Presentation.rename wk a))
          (.app (.var 0) (Presentation.rename wk a))) ρ.codes.propT :=
      L.eqOf_typed (app_carrier (weaken_carrier hf) (weaken_carrier ha))
        (app_carrier (ρ.var_carrier (.arr σ τ)) (weaken_carrier ha))
    have base : Typed ρ.rules Γ (.refl (.app f a))
        (ρ.holdsOf (inst0 f (ρ.eqOf τ (.app (Presentation.rename wk f) (Presentation.rename wk a))
          (.app (.var 0) (Presentation.rename wk a))))) := by
      rw [inst0_eqOf_function]
      exact L.reflIntro (app_carrier hf ha)
    have moved := T.typed (L.carrierAt_typed (.arr σ τ)) hf hg family base
      (L.identity_of_holds hf hg he)
    rwa [inst0_eqOf_function] at moved
  argumentCongruence := by
    intro n Γ σ τ f l r e out success hf hl hr he
    simp only [identityRaw, L.identity, if_true, Option.some.injEq] at success
    subst success
    have family : Typed ρ.rules (.snoc Γ (ρ.carrierAt n σ))
        (ρ.eqOf τ (.app (Presentation.rename wk f) (Presentation.rename wk l))
          (.app (Presentation.rename wk f) (.var 0))) ρ.codes.propT :=
      L.eqOf_typed (app_carrier (weaken_carrier hf) (weaken_carrier hl))
        (app_carrier (weaken_carrier hf) (ρ.var_carrier σ))
    have base : Typed ρ.rules Γ (.refl (.app f l))
        (ρ.holdsOf (inst0 l (ρ.eqOf τ (.app (Presentation.rename wk f) (Presentation.rename wk l))
          (.app (Presentation.rename wk f) (.var 0))))) := by
      rw [inst0_eqOf_argument]
      exact L.reflIntro (app_carrier hf hl)
    have moved := T.typed (L.carrierAt_typed σ) hl hr family base (L.identity_of_holds hl hr he)
    rwa [inst0_eqOf_argument] at moved
  functionExtensionality := by
    intro n Γ σ τ f g pw out success hf hg hpw
    simp only [identityRaw] at success
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp success
    have constant : Typed ρ.rules Γ (.const c) (ρ.holdsOf (ρ.funextCode σ τ)) :=
      L.declared_typed (code := fun {_} => ρ.funextCode σ τ) (tracked.funext_declared hc)
        (L.funextCode_typed σ τ) (liftClosed_funextCode σ τ)
    have inner : ∀ {k : Nat} {Θ : Ctx Head k} {F G : Tm Head k},
        Typed ρ.rules Θ F (ρ.carrierAt k (.arr σ τ)) →
        Typed ρ.rules Θ G (ρ.carrierAt k (.arr σ τ)) →
        Typed ρ.rules Θ (ρ.allOf σ (.lam (ρ.eqOf τ
          (.app (Presentation.rename wk F) (.var 0)) (.app (Presentation.rename wk G) (.var 0)))))
          ρ.codes.propT := by
      intro k Θ F G hF hG
      exact L.allOf_typed (.lamIntro (L.pi_typed (L.carrierAt_typed σ) L.prop_typed)
        L.proofs_universe (L.eqOf_typed (app_carrier (weaken_carrier hF) (ρ.var_carrier σ))
          (app_carrier (weaken_carrier hG) (ρ.var_carrier σ))))
    have outer : Typed ρ.rules (.snoc Γ (ρ.carrierAt n (.arr σ τ)))
        (ρ.allOf (.arr σ τ) (.lam (ρ.impOf
          (ρ.allOf σ (.lam (ρ.eqOf τ (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0)))))
          (ρ.eqOf (.arr σ τ) (.var 1) (.var 0))))) ρ.codes.propT := by
      have first : Typed ρ.rules (.snoc (.snoc Γ (ρ.carrierAt n (.arr σ τ)))
          (ρ.carrierAt (n + 1) (.arr σ τ))) (.var 1) (ρ.carrierAt (n + 2) (.arr σ τ)) :=
        var_succ_carrier (ρ.var_carrier (.arr σ τ))
      have second : Typed ρ.rules (.snoc (.snoc Γ (ρ.carrierAt n (.arr σ τ)))
          (ρ.carrierAt (n + 1) (.arr σ τ))) (.var 0) (ρ.carrierAt (n + 2) (.arr σ τ)) :=
        ρ.var_carrier (.arr σ τ)
      exact L.allOf_typed (.lamIntro (L.pi_typed (L.carrierAt_typed (.arr σ τ)) L.prop_typed)
        L.proofs_universe (L.impOf_typed (inner first second) (L.eqOf_typed first second)))
    have atF := L.allElim outer constant hf
    have middle : Typed ρ.rules (.snoc Γ (ρ.carrierAt n (.arr σ τ)))
        (ρ.impOf (ρ.allOf σ (.lam (ρ.eqOf τ
            (.app (Presentation.rename wk (Presentation.rename wk f)) (.var 0))
            (.app (.var 1) (.var 0)))))
          (ρ.eqOf (.arr σ τ) (Presentation.rename wk f) (.var 0))) ρ.codes.propT :=
      L.impOf_typed (inner (weaken_carrier hf) (ρ.var_carrier (.arr σ τ)))
        (L.eqOf_typed (weaken_carrier hf) (ρ.var_carrier (.arr σ τ)))
    have atFG := L.allElim middle atF hg
    have unfolded : inst0 g (ρ.impOf (ρ.allOf σ (.lam (ρ.eqOf τ
          (.app (Presentation.rename wk (Presentation.rename wk f)) (.var 0))
          (.app (.var 1) (.var 0)))))
        (ρ.eqOf (.arr σ τ) (Presentation.rename wk f) (.var 0))) =
        ρ.impOf (ρ.allOf σ (.lam (ρ.eqOf τ (.app (Presentation.rename wk f) (.var 0))
          (.app (Presentation.rename wk g) (.var 0)))))
          (ρ.eqOf (.arr σ τ) f g) := by
      change ρ.impOf (ρ.allOf σ (.lam (ρ.eqOf τ
          (.app (Presentation.subst (liftSub (subst0 g))
            (Presentation.rename wk (Presentation.rename wk f))) (.var 0))
          (.app (Presentation.rename wk g) (.var 0)))))
          (ρ.eqOf (.arr σ τ) (inst0 g (Presentation.rename wk f)) g) = _
      rw [subst_liftSub_wk, ← inst0, inst0_rename_wk]
    rw [unfolded] at atFG
    exact L.impElim (inner hf hg) (L.eqOf_typed hf hg) atFG hpw

end Laws

end HOLReading

/-! ## The algebra with its laws -/

/-- **The equality algebra of the identity reading**, lawful in the selected
judgment of the reading's package. -/
def identityEqOperations {ρ : HOLReading Head Base Const} {J : DeclName} (L : ρ.Laws)
    (T : ρ.CodeTransport J) (tracked : TrackedEquality ρ) : PointedOperations ρ :=
  ⟨ρ.identityRaw J tracked.funext tracked.propext, L.identityRaw_lawful T tracked⟩

variable {ρ : HOLReading Head Base Const} {J : DeclName}

/-- **Substitution naturality** of the identity algebra. -/
theorem identityEqOperations_natural (L : ρ.Laws) (T : ρ.CodeTransport J)
    (tracked : TrackedEquality ρ) : (identityEqOperations L T tracked).raw.Natural :=
  HOLReading.identityRaw_natural

/-- **Exact totality under the identity reading**: a proof compiles exactly
when it is read, every function-extensionality step is at a type pair whose
constant is tracked, and a propositional-extensionality step occurs only when
that constant is tracked. -/
theorem identityEqOperations_isSome_iff (L : ρ.Laws) (T : ρ.CodeTransport J)
    (tracked : TrackedEquality ρ) {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)}
    {φ : HOL.Formula Const Γ} (d : HOL.ProofSyntax Const Δ φ) {n : Nat}
    (objects : Sub Head Γ.length n) (hyps : Fin Δ.length → Tm Head n) :
    (ρ.compileP (identityEqOperations L T tracked).raw d objects hyps).isSome ↔
      ρ.ReadProof d ∧
        (Request.propositionExtensionality ∈ requests d → tracked.propext.isSome) ∧
        (∀ σ τ, Request.functionExtensionality σ τ ∈ requests d → (tracked.funext σ τ).isSome) := by
  refine (HOLReading.compileP_isSome_iff (ops := (identityEqOperations L T tracked).raw)
    HOLReading.identityRaw_termUniform d objects hyps).trans ?_
  constructor
  · rintro ⟨read, covered⟩
    refine ⟨read, fun m => ?_, fun σ τ m => ?_⟩
    · have available : (ρ.identityRaw J tracked.funext tracked.propext).Available
          .propositionExtensionality := fun {_} => covered _ m
      exact ((HOLReading.identityRaw_available (ρ := ρ) (J := J) (funext := tracked.funext)
        (propext := tracked.propext) L.identity .propositionExtensionality).mp available).1 rfl
    · have available : (ρ.identityRaw J tracked.funext tracked.propext).Available
          (.functionExtensionality σ τ) := fun {_} => covered _ m
      exact ((HOLReading.identityRaw_available (ρ := ρ) (J := J) (funext := tracked.funext)
        (propext := tracked.propext) L.identity (.functionExtensionality σ τ)).mp available).2 σ τ rfl
  · rintro ⟨read, propext, funext⟩
    refine ⟨read, fun q m => (HOLReading.identityRaw_available L.identity q).mpr ⟨?_, ?_⟩⟩
    · rintro rfl
      exact propext m
    · rintro σ τ rfl
      exact funext σ τ m

end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
