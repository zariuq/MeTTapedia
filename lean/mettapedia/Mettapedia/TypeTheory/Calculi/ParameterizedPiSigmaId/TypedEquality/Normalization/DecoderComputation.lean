import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.DeclaredComputations

/-!
# The decoder of proposition codes

A proposition code is a term of a type of codes; the decoder `holds` sends a
code to the type of its proofs. Its root computation decodes the connectives:

* `holds (imp p q) ⟶ Π (_ : holds p). holds q`;
* `holds (a f) ⟶ Π (x : A). holds (f x)`, for every quantifier instance `a`
  over a closed carrier `A`;
* `holds (e x y) ⟶ Id A x y`, for every equation instance `e` at a closed
  carrier `A`; a package without the identity reading lists no equation
  instances.

Under a binder the code's parts are weakened, as the draft kernel shifts
the pattern variables of a rule's right-hand side by the binders it passes
(`regular_rule_instantiate`). The quantifier instances and equation
instances are exactly those the draft lists in `sj_native_rules`, read from
the same instance declarations (`Decoders.ofInstances`).

The decoder computes at arity one with the code as its scrutinee, and the
code constructors are constructors: its steps are spine-shaped, headed by
the decoder, deterministic, and closed under renaming and substitution, the
laws the other declared computations carry.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

variable {Head : Type}

/-- The names of a package of proposition codes: the decoder, implication,
and the closed carriers of its quantifier and equation instances. -/
structure Decoders (Head : Type) where
  holds : DeclName
  imp : DeclName
  allCarrier : DeclName → Option (Tm Head 0)
  eqCarrier : DeclName → Option (Tm Head 0)

/-- The decoding steps of a package of proposition codes. -/
inductive DecoderStep (D : Decoders Head) : {n : Nat} → Tm Head n → Tm Head n → Prop where
  | imp {n : Nat} (p q : Tm Head n) :
      DecoderStep D (.app (.const D.holds) (.app (.app (.const D.imp) p) q))
        (.pi (.app (.const D.holds) p) (.app (.const D.holds) (Presentation.rename wk q)))
  | all {n : Nat} {a : DeclName} {A : Tm Head 0} (carrier : D.allCarrier a = some A)
      (f : Tm Head n) :
      DecoderStep D (.app (.const D.holds) (.app (.const a) f))
        (.pi (liftClosed A)
          (.app (.const D.holds) (.app (Presentation.rename wk f) (.var 0))))
  | eq {n : Nat} {e : DeclName} {A : Tm Head 0} (carrier : D.eqCarrier e = some A)
      (x y : Tm Head n) :
      DecoderStep D (.app (.const D.holds) (.app (.app (.const e) x) y))
        (.id (liftClosed A) x y)

namespace DecoderStep

variable {D : Decoders Head}

theorem rename {n m : Nat} (ρ : Ren n m) {l r : Tm Head n} (step : DecoderStep D l r) :
    DecoderStep D (Presentation.rename ρ l) (Presentation.rename ρ r) := by
  cases step with
  | imp p q =>
      have decoded := DecoderStep.imp (D := D) (Presentation.rename ρ p)
        (Presentation.rename ρ q)
      simpa only [Presentation.rename, rename_liftRen_wk] using decoded
  | all carrier f =>
      have decoded := DecoderStep.all carrier (Presentation.rename ρ f)
      have zero : liftRen ρ 0 = 0 := rfl
      simpa only [Presentation.rename, rename_liftRen_wk, rename_liftClosed, zero] using decoded
  | eq carrier x y =>
      have decoded := DecoderStep.eq carrier (Presentation.rename ρ x)
        (Presentation.rename ρ y)
      simpa only [Presentation.rename, rename_liftClosed] using decoded

theorem substitute {n m : Nat} (σ : Sub Head n m) {l r : Tm Head n}
    (step : DecoderStep D l r) :
    DecoderStep D (Presentation.subst σ l) (Presentation.subst σ r) := by
  cases step with
  | imp p q =>
      have decoded := DecoderStep.imp (D := D) (Presentation.subst σ p)
        (Presentation.subst σ q)
      simpa only [Presentation.subst, subst_liftSub_wk] using decoded
  | all carrier f =>
      have decoded := DecoderStep.all carrier (Presentation.subst σ f)
      have zero : liftSub σ 0 = .var 0 := rfl
      simpa only [Presentation.subst, subst_liftSub_wk, subst_liftClosed, zero] using decoded
  | eq carrier x y =>
      have decoded := DecoderStep.eq carrier (Presentation.subst σ x)
        (Presentation.subst σ y)
      simpa only [Presentation.subst, subst_liftClosed] using decoded

end DecoderStep

/-- The decoding rules as a root computation. -/
def decoderComputation (D : Decoders Head) : RootComputation Head where
  step := DecoderStep D
  rename := by
    intro n m ρ l r step
    exact step.rename ρ
  substitute := by
    intro n m σ l r step
    exact step.substitute σ

/-! ## The laws of a declared computation -/

/-- The roles the decoding rules need: the decoder computes at arity one with
the code as its scrutinee, and the code constructors are constructors of
their numbers of arguments. -/
structure DecoderRoles (roles : Roles Head) (D : Decoders Head) : Prop where
  holds : roles D.holds = .computes 1 (.split 0 .constructor fun _ => .leaf)
  imp : roles D.imp = .constructor 2
  all : ∀ {a : DeclName} {A : Tm Head 0}, D.allCarrier a = some A → roles a = .constructor 1
  eq : ∀ {e : DeclName} {A : Tm Head 0}, D.eqCarrier e = some A → roles e = .constructor 2

theorem decoderComputation_spine {roles : Roles Head} {D : Decoders Head}
    (declared : DecoderRoles roles D) : SpineShaped roles (decoderComputation D) := by
  intro n t u step
  cases step with
  | imp p q =>
      exact ⟨D.holds, 1, _, [.app (.app (.const D.imp) p) q], declared.holds, rfl,
        rfl, InspectTree.accepts_single.mpr ⟨_, rfl, .inr ⟨D.imp, 2, [p, q], declared.imp, rfl⟩⟩⟩
  | all carrier f =>
      exact ⟨D.holds, 1, _, [.app (.const _) f], declared.holds, rfl, rfl,
        InspectTree.accepts_single.mpr ⟨_, rfl, .inr ⟨_, 1, [f], declared.all carrier, rfl⟩⟩⟩
  | eq carrier x y =>
      exact ⟨D.holds, 1, _, [.app (.app (.const _) x) y], declared.holds, rfl,
        rfl, InspectTree.accepts_single.mpr ⟨_, rfl, .inr ⟨_, 2, [x, y], declared.eq carrier, rfl⟩⟩⟩

theorem decoderComputation_headed (D : Decoders Head) :
    HeadedBy D.holds (decoderComputation D) := by
  intro n t u step
  cases step with
  | imp p q => exact ⟨[.app (.app (.const D.imp) p) q], rfl⟩
  | all carrier f => exact ⟨[.app (.const _) f], rfl⟩
  | eq carrier x y => exact ⟨[.app (.app (.const _) x) y], rfl⟩

/-- Decoding is deterministic when implication is not an equation instance;
the shapes of the codes separate the other cases. -/
theorem decoderComputation_deterministic {D : Decoders Head}
    (impNotEquation : D.eqCarrier D.imp = none) :
    Deterministic (decoderComputation D) := by
  intro n t u u' step step'
  cases step with
  | imp p q =>
      cases step' with
      | imp p' q' => rfl
      | eq carrier' x y =>
          rw [impNotEquation] at carrier'
          exact absurd carrier' (by simp)
  | all carrier f =>
      cases step' with
      | all carrier' f' =>
          rw [carrier] at carrier'
          cases carrier'
          rfl
  | eq carrier x y =>
      cases step' with
      | imp p q =>
          rw [impNotEquation] at carrier
          exact absurd carrier (by simp)
      | eq carrier' x' y' =>
          rw [carrier] at carrier'
          cases carrier'
          rfl

/-! ## The instances the draft decodes -/

/-- The decoders of a package from its instance declarations: each quantifier
instance with its carrier, and, under the identity reading, each equation
instance with its carrier. This is the list `sj_native_rules` walks: one
quantifier rule per quantifier instance, and equation rules only when the
identity reading is on. -/
def Decoders.ofInstances [DecidableEq Head] (holds imp : DeclName)
    (quantifiers equations : List (DeclName × Tm Head 0)) (identity : Bool) :
    Decoders Head where
  holds := holds
  imp := imp
  allCarrier a := quantifiers.lookup a
  eqCarrier e := if identity then equations.lookup e else none

theorem Decoders.ofInstances_eq_none [DecidableEq Head] (holds imp : DeclName)
    (quantifiers equations : List (DeclName × Tm Head 0)) (e : DeclName) :
    (Decoders.ofInstances holds imp quantifiers equations false).eqCarrier e = none := rfl

/-- Without the identity reading no equation code decodes: the only decoding
steps are implication and the quantifier instances. -/
theorem DecoderStep.without_identity [DecidableEq Head] {holds imp : DeclName}
    {quantifiers equations : List (DeclName × Tm Head 0)} {n : Nat} {l r : Tm Head n}
    (step : DecoderStep (Decoders.ofInstances holds imp quantifiers equations false) l r) :
    (∃ p q, l = .app (.const holds) (.app (.app (.const imp) p) q)) ∨
      ∃ a A f, quantifiers.lookup a = some A ∧ l = .app (.const holds) (.app (.const a) f) := by
  cases step with
  | imp p q => exact .inl ⟨p, q, rfl⟩
  | all carrier f => exact .inr ⟨_, _, f, carrier, rfl⟩
  | eq carrier x y => exact absurd carrier (by simp [Decoders.ofInstances])

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
