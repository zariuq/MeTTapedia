import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.InterpLaws

/-!
# Decoding: inversion of truth, and stuck eliminations

The truth value of an implication, a quantified code or an equation code comes
from its parts. A code in weak-head normal form reduces only to itself, so the
clause that gives it a truth value is the clause of its shape.

The package decodes `holds c` into a type former, while the model keeps
`holds c` rigid. A term that eliminates a type former, a head or `holds c` by
an application or a projection is stuck: it is neither a numeral, nor a code,
nor an interpreted type. Every partial equivalence of the model that relates
one stuck term to itself relates it to every stuck term.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

open Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {M : Model Head L}

/-! ## Weak-head normal forms reduce only to themselves -/

theorem WhRed.of_whnf {R : Rules Head} {roles : Roles Head} {n : Nat}
    {w w' : Tm Head n} (normal : Whnf R roles w) (red : WhRed R roles w w') : w' = w := by
  cases red using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head step _ => exact absurd step (normal _)

/-! ## Inversion of truth for codes in normal form -/

section Inversion

variable {Head : Type} {S : Reading Head} (laws : S.Laws)
include laws

theorem Truth.imp_inv {n : Nat} {ξ : World S n} {p q : Tm Head n} {P : S.P}
    (truth : Truth S ξ (.app (.app (.const S.imp) p) q) P) :
    ∃ P₁ Q₁, Truth S ξ p P₁ ∧ Truth S ξ q Q₁ ∧ P = S.impMeaning P₁ Q₁ := by
  cases truth with
  | imp red hp hq =>
      cases WhRed.of_whnf (laws.whnf_imp _ _) red
      exact ⟨_, _, hp, hq, rfl⟩
  | all carrier red _ => cases WhRed.of_whnf (laws.whnf_imp _ _) red
  | eq carrier red _ _ =>
      cases WhRed.of_whnf (laws.whnf_imp _ _) red
      rw [laws.impNotEq] at carrier
      cases carrier
  | generic red _ =>
      exact absurd (show appSpine (.const S.imp) [p, q] = _ from
        (WhRed.of_whnf (laws.whnf_imp _ _) red).symm) constSpine_ne_varSpine
  | neutral red neutral =>
      exact absurd (WhRed.of_whnf (laws.whnf_imp _ _) red) (laws.neutral_ne_imp neutral)

theorem Truth.all_inv {n : Nat} {ξ : World S n} {a : DeclName} {k : Kind} {A : Carrier k}
    (carrier : S.allCarrier a = some ⟨k, A⟩) {f : Tm Head n} {P : S.P}
    (truth : Truth S ξ (.app (.const a) f) P) :
    ∃ φ : A.V S → S.P, Read S ξ f (.arr A .prop) φ ∧ P = S.allMeaning A φ := by
  cases truth with
  | imp red _ _ => cases WhRed.of_whnf (laws.whnf_all carrier _) red
  | all carrier' red read =>
      cases WhRed.of_whnf (laws.whnf_all carrier _) red
      rw [carrier] at carrier'
      cases carrier'
      exact ⟨_, read, rfl⟩
  | eq carrier' red _ _ => cases WhRed.of_whnf (laws.whnf_all carrier _) red
  | generic red _ =>
      exact absurd (show appSpine (.const a) [f] = _ from
        (WhRed.of_whnf (laws.whnf_all carrier _) red).symm) constSpine_ne_varSpine
  | neutral red neutral =>
      exact absurd (WhRed.of_whnf (laws.whnf_all carrier _) red)
        (laws.neutral_ne_all neutral carrier)

theorem Truth.eq_inv {n : Nat} {ξ : World S n} {e : DeclName} {k : Kind} {A : Carrier k}
    (carrier : S.eqCarrier e = some ⟨k, A⟩) {x y : Tm Head n} {P : S.P}
    (truth : Truth S ξ (.app (.app (.const e) x) y) P) :
    ∃ v w : A.V S, Read S ξ x A v ∧ Read S ξ y A w ∧ P = S.eqMeaning A v w := by
  cases truth with
  | imp red _ _ =>
      cases WhRed.of_whnf (laws.whnf_eq carrier _ _) red
      rw [laws.impNotEq] at carrier
      cases carrier
  | all carrier' red _ => cases WhRed.of_whnf (laws.whnf_eq carrier _ _) red
  | eq carrier' red readX readY =>
      cases WhRed.of_whnf (laws.whnf_eq carrier _ _) red
      rw [carrier] at carrier'
      cases carrier'
      exact ⟨_, _, readX, readY, rfl⟩
  | generic red _ =>
      exact absurd (show appSpine (.const e) [x, y] = _ from
        (WhRed.of_whnf (laws.whnf_eq carrier _ _) red).symm) constSpine_ne_varSpine
  | neutral red neutral =>
      exact absurd (WhRed.of_whnf (laws.whnf_eq carrier _ _) red)
        (laws.neutral_ne_eq neutral carrier)

end Inversion

/-! ## Stuck eliminations -/

/-- A type former, a head, or `holds` applied to one code. -/
inductive TypeLike (M : Model Head L) {n : Nat} : Tm Head n → Prop where
  | holds (c : Tm Head n) : TypeLike M (.app (.const M.holds) c)
  | head (h : Head) : TypeLike M (.head h)
  | pi (A : Tm Head n) (B : Tm Head (n + 1)) : TypeLike M (.pi A B)
  | sigma (A : Tm Head n) (B : Tm Head (n + 1)) : TypeLike M (.sigma A B)
  | id (A a b : Tm Head n) : TypeLike M (.id A a b)

/-- An application or projection of a type-like term or of a stuck term. -/
inductive Stuck (M : Model Head L) {n : Nat} : Tm Head n → Prop where
  | appLike {t : Tm Head n} (a : Tm Head n) : TypeLike M t → Stuck M (.app t a)
  | appStuck {t : Tm Head n} (a : Tm Head n) : Stuck M t → Stuck M (.app t a)
  | fstLike {t : Tm Head n} : TypeLike M t → Stuck M (.fst t)
  | fstStuck {t : Tm Head n} : Stuck M t → Stuck M (.fst t)
  | sndLike {t : Tm Head n} : TypeLike M t → Stuck M (.snd t)
  | sndStuck {t : Tm Head n} : Stuck M t → Stuck M (.snd t)

theorem TypeLike.rename {n m : Nat} {t : Tm Head n} (like : TypeLike M t) (ρ : Ren n m) :
    TypeLike M (Presentation.rename ρ t) := by
  cases like with
  | holds c => exact .holds _
  | head h => exact .head h
  | pi A B => exact .pi _ _
  | sigma A B => exact .sigma _ _
  | id A a b => exact .id _ _ _

theorem Stuck.rename {n : Nat} {t : Tm Head n} (stuck : Stuck M t) :
    ∀ {m : Nat} (ρ : Ren n m), Stuck M (Presentation.rename ρ t) := by
  induction stuck with
  | appLike a like => exact fun ρ => .appLike _ (like.rename ρ)
  | appStuck a _ ih => exact fun ρ => .appStuck _ (ih ρ)
  | fstLike like => exact fun ρ => .fstLike (like.rename ρ)
  | fstStuck _ ih => exact fun ρ => .fstStuck (ih ρ)
  | sndLike like => exact fun ρ => .sndLike (like.rename ρ)
  | sndStuck _ ih => exact fun ρ => .sndStuck (ih ρ)

/-- The head of a type-like term is `holds` whenever it is a constant. -/
theorem TypeLike.head_const {n : Nat} {t : Tm Head n} (like : TypeLike M t) {c : DeclName}
    (e : (headArgs t).1 = .const c) : c = M.holds := by
  cases like with
  | holds _ => exact (Tm.const.inj e).symm
  | head _ => cases e
  | pi _ _ => cases e
  | sigma _ _ => cases e
  | id _ _ _ => cases e

/-- The head of a stuck term is `holds` whenever it is a constant. -/
theorem Stuck.head_const {n : Nat} {t : Tm Head n} (stuck : Stuck M t) :
    ∀ {c : DeclName}, (headArgs t).1 = .const c → c = M.holds := by
  induction stuck with
  | appLike a like => exact fun e => like.head_const e
  | appStuck a _ ih => exact fun e => ih e
  | fstLike _ => exact fun e => by cases e
  | fstStuck _ _ => exact fun e => by cases e
  | sndLike _ => exact fun e => by cases e
  | sndStuck _ _ => exact fun e => by cases e

theorem TypeLike.ne_lam {n : Nat} {t : Tm Head n} (like : TypeLike M t)
    (body : Tm Head (n + 1)) : t ≠ .lam body := by
  cases like <;> intro e <;> cases e

theorem TypeLike.ne_pair {n : Nat} {t : Tm Head n} (like : TypeLike M t)
    (a b : Tm Head n) : t ≠ .pair a b := by
  cases like <;> intro e <;> cases e

theorem Stuck.ne_lam {n : Nat} {t : Tm Head n} (stuck : Stuck M t)
    (body : Tm Head (n + 1)) : t ≠ .lam body := by
  cases stuck <;> intro e <;> cases e

theorem Stuck.ne_pair {n : Nat} {t : Tm Head n} (stuck : Stuck M t)
    (a b : Tm Head n) : t ≠ .pair a b := by
  cases stuck <;> intro e <;> cases e

section StuckLaws

variable (laws : M.Laws)
include laws

/-- A type-like term is weak-head normal. -/
theorem TypeLike.whnf {n : Nat} {t : Tm Head n} (like : TypeLike M t) :
    Whnf M.rules M.roles t := by
  cases like with
  | holds c => exact laws.whnf_holds c
  | head h => exact head_whnf laws.shape h
  | pi A B => exact pi_whnf laws.shape A B
  | sigma A B => exact sigma_whnf laws.shape A B
  | id A a b => exact id_whnf laws.shape A a b

/-- A computing constant does not head an application whose function has a
head that is `holds` whenever it is a constant. -/
theorem app_ne_computing {n : Nat} {x a : Tm Head n}
    (headHolds : ∀ {c : DeclName}, (headArgs x).1 = .const c → c = M.holds)
    {c : DeclName} {arity : Nat} {scrutinee : InspectTree}
    (role : M.roles c = .computes arity scrutinee) {args : List (Tm Head n)}
    (e : Tm.app x a = appSpine (.const c) args) : False := by
  have heads := congrArg (fun t => (headArgs t).1) e
  simp only [headArgs, headArgs_appSpine (f := (.const c : Tm Head n)) (by trivial)] at heads
  have hc := headHolds heads
  subst hc
  rw [laws.holds] at role
  cases role

/-- An application of a weak-head normal term whose constant head is `holds`
does not step. -/
theorem app_whnf_of_head {n : Nat} {x a : Tm Head n} (hx : Whnf M.rules M.roles x)
    (notLam : ∀ body, x ≠ .lam body)
    (headHolds : ∀ {c : DeclName}, (headArgs x).1 = .const c → c = M.holds) :
    Whnf M.rules M.roles (.app x a) := by
  intro u step
  generalize e : Tm.app x a = t at step
  cases step with
  | beta body _ => cases e; exact notLam body rfl
  | root step =>
      obtain ⟨c, arity, scrutinee, args, role, e', _⟩ := laws.shape.spine step
      exact app_ne_computing laws headHolds role (e.trans e')
  | appFun step' => cases e; exact hx _ step'
  | scrutinee role _ _ => exact app_ne_computing laws headHolds role e
  | fstPair _ _ => cases e
  | sndPair _ _ => cases e
  | fst _ => cases e
  | snd _ => cases e

/-- A projection of a weak-head normal term that is not a pair does not step. -/
theorem fst_whnf_of {n : Nat} {x : Tm Head n} (hx : Whnf M.rules M.roles x)
    (notPair : ∀ a b, x ≠ .pair a b) : Whnf M.rules M.roles (.fst x) := by
  intro u step
  generalize e : Tm.fst x = t at step
  cases step with
  | fstPair _ _ => cases e; exact notPair _ _ rfl
  | root step =>
      obtain ⟨c, _, _, args, _, e', _⟩ := laws.shape.spine step
      exact appSpine_const_ne_fst (e.trans e').symm
  | fst step' => cases e; exact hx _ step'
  | scrutinee _ _ _ => exact appSpine_const_ne_fst e.symm
  | beta _ _ => cases e
  | sndPair _ _ => cases e
  | appFun _ => cases e
  | snd _ => cases e

theorem snd_whnf_of {n : Nat} {x : Tm Head n} (hx : Whnf M.rules M.roles x)
    (notPair : ∀ a b, x ≠ .pair a b) : Whnf M.rules M.roles (.snd x) := by
  intro u step
  generalize e : Tm.snd x = t at step
  cases step with
  | sndPair _ _ => cases e; exact notPair _ _ rfl
  | root step =>
      obtain ⟨c, _, _, args, _, e', _⟩ := laws.shape.spine step
      exact appSpine_const_ne_snd (e.trans e').symm
  | snd step' => cases e; exact hx _ step'
  | scrutinee _ _ _ => exact appSpine_const_ne_snd e.symm
  | beta _ _ => cases e
  | fstPair _ _ => cases e
  | appFun _ => cases e
  | fst _ => cases e

/-- A stuck term is weak-head normal. -/
theorem Stuck.whnf {n : Nat} {t : Tm Head n} (stuck : Stuck M t) :
    Whnf M.rules M.roles t := by
  induction stuck with
  | appLike a like =>
      exact app_whnf_of_head laws (like.whnf laws) like.ne_lam like.head_const
  | appStuck a s ih => exact app_whnf_of_head laws ih s.ne_lam s.head_const
  | fstLike like => exact fst_whnf_of laws (like.whnf laws) like.ne_pair
  | fstStuck s ih => exact fst_whnf_of laws ih s.ne_pair
  | sndLike like => exact snd_whnf_of laws (like.whnf laws) like.ne_pair
  | sndStuck s ih => exact snd_whnf_of laws ih s.ne_pair

end StuckLaws

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
