import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Proofs
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.ConstantRenaming

/-!
# The accessibility package: an inert recursor and its propositional unfolding

The package extends a base package with proposition codes by two constants and
no computation rule:

* the recursor, with a proof-taking guard,
  `rec : Π (P : A → U_m) (R : A → A → prop)
           (F : Π x. (Π y. holds (R y x) → P y) → P x) (a : A).
           holds (acc R a) → P a`;
* its propositional unfolding, an identity proof under the same premises,
  `unfold : Π P R F a q. Id (P a) (rec P R F a q)
              (F a (λ y r. rec P R F y (inv R a q y r)))`,
  where `inv` is the inversion of the accessibility code (`CodeNames.invTerm`).

Both are unconditional in the accessibility proof `q`, as in the propositional
variant of the published accessibility eliminator: the recursive call receives
the proof of `R y a` and passes on the inverted accessibility proof.

The extended package (`rules`) has the base package's universes, head
equality and root computation; only its declared types grow
(`rules_computation`, `rules_headEq`). Every derivation of the base package is a
derivation of the extended one (`derivable_mono`). The declared types are
formed (`recType_typed`, `unfoldType_typed`), so full applications are typed
(`rec_apply`, `unfold_apply`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Impredicative
open TelescopeAbstraction (closeType applyClosed)

variable {Head : Type}

/-- The accessibility package over a base package: the code names, the base, a
closed carrier, a universe of motives, and the names of the recursor and of its
propositional unfolding. -/
structure Signature (Head : Type) extends CodeNames Head where
  base : Rules Head
  carrier : Tm Head 0
  motive : Head
  recursor : DeclName
  unfold : DeclName

namespace Signature

variable (S : Signature Head)

/-! ## The declared types -/

/-- `A → U_m`: the type of motives. -/
def motiveType {n : Nat} : Tm Head n := .pi (liftClosed S.carrier) (.head S.motive)

/-- `Π x. (Π y. holds (R y x) → P y) → P x`, with `R = var 0` and `P = var 1`. -/
def stepType : Tm Head 2 :=
  .pi (liftClosed S.carrier)
    (.pi (.pi (liftClosed S.carrier)
        (.pi (S.codes.holdsOf (CodeNames.relOf (.var 2) (.var 0) (.var 1))) (.app (.var 4) (.var 1))))
      (.app (.var 3) (.var 1)))

/-- The telescope `P R F a q` of the recursor. -/
def recTelescope : Ctx Head 5 :=
  .snoc (.snoc (.snoc (.snoc (.snoc .nil S.motiveType) (S.relType S.carrier)) S.stepType)
    (liftClosed S.carrier)) (S.codes.holdsOf (S.acc (.var 2) (.var 0)))

/-- `P a`, in the telescope. -/
def recBody : Tm Head 5 := .app (.var 4) (.var 1)

/-- The declared type of the recursor. -/
def recType : Tm Head 0 := closeType S.recTelescope (recBody (Head := Head))

/-- `rec P R F a q`. -/
def recSpine {n : Nat} (P R F a q : Tm Head n) : Tm Head n :=
  .app (.app (.app (.app (.app (.const S.recursor) P) R) F) a) q

/-- `unfold P R F a q`. -/
def unfoldSpine {n : Nat} (P R F a q : Tm Head n) : Tm Head n :=
  .app (.app (.app (.app (.app (.const S.unfold) P) R) F) a) q

/-- `inv R a q y r : holds (acc R y)`. -/
def invSpine {n : Nat} (R a q y r : Tm Head n) : Tm Head n :=
  .app (.app (.app (.app (.app (liftClosed (S.invTerm (Head := Head))) R) a) q) y) r

/-- The unfolding `F a (λ y r. rec P R F y (inv R a q y r))`. -/
def unfolding {n : Nat} (P R F a q : Tm Head n) : Tm Head n :=
  .app (.app F a) (.lam (.lam
    (S.recSpine (rename wk (rename wk P)) (rename wk (rename wk R)) (rename wk (rename wk F))
      (.var 1)
      (S.invSpine (rename wk (rename wk R)) (rename wk (rename wk a)) (rename wk (rename wk q))
        (.var 1) (.var 0)))))

/-- `Id (P a) (rec P R F a q) (F a (λ y r. rec P R F y (inv R a q y r)))`, in the telescope. -/
def unfoldBody : Tm Head 5 :=
  .id (recBody (Head := Head)) (S.recSpine (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))
    (S.unfolding (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))

/-- The declared type of the propositional unfolding. -/
def unfoldType : Tm Head 0 := closeType S.recTelescope S.unfoldBody

/-! ## The packages -/

/-- The base package with the recursor declared. -/
def recBase : Rules Head :=
  { S.base with
    constantType := fun c => if c = S.recursor then some S.recType else S.base.constantType c }

/-- The base package with the recursor and its unfolding declared. -/
def accBase : Rules Head :=
  { S.base with
    constantType := fun c =>
      if c = S.recursor then some S.recType
      else if c = S.unfold then some S.unfoldType
      else S.base.constantType c }

/-- The base package with the codes: the candidate before the extension. -/
abbrev baseRules : Rules Head := S.codes.extend S.base

/-- The base package with the recursor, and the codes. -/
abbrev recRules : Rules Head := S.codes.extend S.recBase

/-- The extended package: the base with the two constants, and the codes. -/
abbrev rules : Rules Head := S.codes.extend S.accBase

/-! ### Inertness at the level of the package -/

/-- **The extension adds no computation.** -/
theorem rules_computation : S.rules.computation = S.baseRules.computation := rfl

theorem rules_headEq : S.rules.headEq = S.baseRules.headEq := rfl

theorem rules_isUniverse : S.rules.isUniverse = S.baseRules.isUniverse := rfl

theorem rules_headTyping : S.rules.headTyping = S.baseRules.headTyping := rfl

theorem rules_join : S.rules.join = S.baseRules.join := rfl

theorem rules_cumulative : S.rules.cumulative = S.baseRules.cumulative := rfl

@[simp] theorem rename_motiveType {n m : Nat} (ρ : Ren n m) :
    rename ρ (S.motiveType : Tm Head n) = S.motiveType := by
  simp only [motiveType, Presentation.rename, rename_liftClosed]

@[simp] theorem subst_motiveType {n m : Nat} (σ : Sub Head n m) :
    subst σ (S.motiveType : Tm Head n) = S.motiveType := by
  simp only [motiveType, Presentation.subst, subst_liftClosed]

/-- The type of step functions for a motive `P` and a relation `R`. -/
def stepTypeOf {n : Nat} (P R : Tm Head n) : Tm Head n :=
  subst (consSub R (consSub P (fun i => Fin.elim0 i))) S.stepType

/-- **Conversion is unchanged**, on every pair of terms, including terms that
mention the new constants. -/
theorem conv_iff {n : Nat} (t u : Tm Head n) :
    Conv S.rules.headEq t u S.rules.computation ↔
      Conv S.baseRules.headEq t u S.baseRules.computation := Iff.rfl

end Signature

/-! ## Extensions of base packages -/

/-- `B'` extends `B`: the same universe rules and computation, and every declared
constant of `B` keeps its declared type. -/
structure Extends (B B' : Rules Head) : Prop where
  headTyping : B'.headTyping = B.headTyping
  isUniverse : B'.isUniverse = B.isUniverse
  join : B'.join = B.join
  cumulative : B'.cumulative = B.cumulative
  headEq : B'.headEq = B.headEq
  computation : B'.computation = B.computation
  constantType : ∀ {c : DeclName} {T : Tm Head 0}, B.constantType c = some T →
    B'.constantType c = some T

theorem Statement.mapConst_id (st : Statement Head) : st.mapConst (fun c => c) = st := by
  cases st <;> simp [Statement.mapConst]

theorem Extends.codes {B B' : Rules Head} (K : Codes Head) (ext : Extends B B') :
    Extends (K.extend B) (K.extend B') where
  headTyping := ext.headTyping
  isUniverse := ext.isUniverse
  join := ext.join
  cumulative := ext.cumulative
  headEq := ext.headEq
  computation := by simp only [Codes.extend, ext.computation]
  constantType := fun {c} {T} declared => by
    simp only [Codes.extend, Option.orElse] at declared ⊢
    cases e : K.codeType c with
    | some T' => rw [e] at declared; exact declared
    | none => rw [e] at declared; exact ext.constantType declared

/-- **Monotonicity.** Every derivation of a package is a derivation of every
package extending it. -/
theorem Extends.derivable {B B' : Rules Head} (ext : Extends B B') {st : Statement Head}
    (d : Derivable B st) : Derivable B' st := by
  have ren : RulesRenaming B B' (fun c => c) :=
    { headTyping := fun h => by rw [ext.headTyping]; exact h
      isUniverse := fun h => by rw [ext.isUniverse]; exact h
      join := fun h => by rw [ext.join]; exact h
      cumulative := fun h => by rw [ext.cumulative]; exact h
      headEq := fun h => by rw [ext.headEq]; exact h
      constantType := fun declared => by
        simpa only [Tm.mapConst_id] using ext.constantType declared
      computation := fun step => by rw [Tm.mapConst_id, Tm.mapConst_id, ext.computation]; exact step }
  simpa only [Statement.mapConst_id] using d.mapConst ren

theorem Extends.trans {B B' B'' : Rules Head} (first : Extends B B') (second : Extends B' B'') :
    Extends B B'' where
  headTyping := second.headTyping.trans first.headTyping
  isUniverse := second.isUniverse.trans first.isUniverse
  join := second.join.trans first.join
  cumulative := second.cumulative.trans first.cumulative
  headEq := second.headEq.trans first.headEq
  computation := second.computation.trans first.computation
  constantType := fun declared => second.constantType (first.constantType declared)

/-! ## The laws of the package -/

/-- The universes of the package over a base package `B`: the laws of the
codes, a universe of motives containing the proofs and closed under function
types, and a universe above it that is closed under function types. -/
structure Signature.Universes (S : Signature Head) (B : Rules Head) : Prop where
  codes : S.toCodeNames.Laws B S.carrier
  motive_universe : B.isUniverse S.motive
  proofs_below_motive : B.cumulative S.codes.proofs S.motive
  motive_pi : ∃ w, B.join S.motive S.motive w ∧ B.cumulative w S.motive
  top : ∃ t, B.isUniverse t ∧ B.headTyping S.motive t ∧
    B.cumulative S.motive t ∧ ∃ w, B.join t t w ∧ B.cumulative w t

/-- The laws of the accessibility package: its universes over the base, and
fresh names. -/
structure Signature.Laws (S : Signature Head) : Prop where
  universes : S.Universes S.base
  recursor_fresh : S.codes.codeType S.recursor = none ∧ S.base.constantType S.recursor = none
  unfold_fresh : S.codes.codeType S.unfold = none ∧ S.base.constantType S.unfold = none
  recursor_ne_unfold : S.recursor ≠ S.unfold

namespace Signature

variable {S : Signature Head}

theorem Universes.mono {B B' : Rules Head} (U : S.Universes B) (ext : Extends B B') :
    S.Universes B' where
  codes :=
    { point := U.codes.point
      predicate := U.codes.predicate
      point_apart := U.codes.point_apart
      predicate_apart := U.codes.predicate_apart
      imp_apart := U.codes.imp_apart
      holds_apart := U.codes.holds_apart
      proofs_universe := by rw [ext.isUniverse]; exact U.codes.proofs_universe
      proofs_typed := by rw [ext.isUniverse, ext.headTyping]; exact U.codes.proofs_typed
      proofs_pi := by rw [ext.join, ext.cumulative]; exact U.codes.proofs_pi
      holds_formed := by
        obtain ⟨w, hw, ht⟩ := U.codes.holds_formed
        exact ⟨w, by rw [ext.isUniverse]; exact hw, (ext.codes S.codes).derivable ht⟩
      carrier_typed := (ext.codes S.codes).derivable U.codes.carrier_typed }
  motive_universe := by rw [ext.isUniverse]; exact U.motive_universe
  proofs_below_motive := by rw [ext.cumulative]; exact U.proofs_below_motive
  motive_pi := by rw [ext.join, ext.cumulative]; exact U.motive_pi
  top := by rw [ext.isUniverse, ext.headTyping, ext.cumulative, ext.join]; exact U.top

theorem Laws.base_recBase (L : S.Laws) : Extends S.base S.recBase where
  headTyping := rfl
  isUniverse := rfl
  join := rfl
  cumulative := rfl
  headEq := rfl
  computation := rfl
  constantType := fun {c} {T} declared => by
    by_cases hr : c = S.recursor
    · subst hr
      rw [L.recursor_fresh.2] at declared
      cases declared
    · simpa [recBase, hr] using declared

theorem Laws.recBase_accBase (L : S.Laws) : Extends S.recBase S.accBase where
  headTyping := rfl
  isUniverse := rfl
  join := rfl
  cumulative := rfl
  headEq := rfl
  computation := rfl
  constantType := fun {c} {T} declared => by
    by_cases hr : c = S.recursor
    · subst hr
      simpa [recBase, accBase] using declared
    · by_cases hu : c = S.unfold
      · subst hu
        simp [recBase, Ne.symm L.recursor_ne_unfold, L.unfold_fresh.2] at declared
      · simpa [recBase, accBase, hr, hu] using declared

theorem Laws.base_accBase (L : S.Laws) : Extends S.base S.accBase :=
  L.base_recBase.trans L.recBase_accBase

/-- **Monotonicity of the extension.** Every derivation of the base package with
codes is a derivation of the extended package. -/
theorem derivable_mono (L : S.Laws) {st : Statement Head} (d : Derivable S.baseRules st) :
    Derivable S.rules st :=
  (L.base_accBase.codes S.codes).derivable d

theorem recRules_constantType_recursor (L : S.Laws) :
    S.recRules.constantType S.recursor = some S.recType := by
  simp [Codes.extend, recBase, L.recursor_fresh.1, Option.orElse]

theorem rules_constantType_recursor (L : S.Laws) :
    S.rules.constantType S.recursor = some S.recType := by
  simp [Codes.extend, accBase, L.recursor_fresh.1, Option.orElse]

theorem rules_constantType_unfold (L : S.Laws) :
    S.rules.constantType S.unfold = some S.unfoldType := by
  simp [Codes.extend, accBase, L.unfold_fresh.1, Option.orElse, Ne.symm L.recursor_ne_unfold]

/-! ## Universe facts -/

namespace Universes

variable {B : Rules Head} (U : S.Universes B)
include U

theorem toMotive {n : Nat} {Γ : Ctx Head n} {X : Tm Head n}
    (h : Typed (S.toCodeNames.rules B) Γ X (.head S.codes.proofs)) :
    Typed (S.toCodeNames.rules B) Γ X (.head S.motive) :=
  .cumul h U.proofs_below_motive

theorem piMotive {n : Nat} {Γ : Ctx Head n} {X : Tm Head n} {Y : Tm Head (n + 1)}
    (hX : Typed (S.toCodeNames.rules B) Γ X (.head S.motive))
    (hY : Typed (S.toCodeNames.rules B) (.snoc Γ X) Y (.head S.motive)) :
    Typed (S.toCodeNames.rules B) Γ (.pi X Y) (.head S.motive) := by
  obtain ⟨w, hj, hc⟩ := U.motive_pi
  exact .cumul (.piForm hX U.motive_universe hY U.motive_universe hj) hc

/-- A universe above the universe of motives, closed under function types. -/
theorem top_facts : ∃ t, (S.toCodeNames.rules B).isUniverse t ∧
    (∀ {n : Nat} {Γ : Ctx Head n},
      Typed (S.toCodeNames.rules B) Γ (.head S.motive) (.head t)) ∧
    (∀ {n : Nat} {Γ : Ctx Head n} {X : Tm Head n},
      Typed (S.toCodeNames.rules B) Γ X (.head S.motive) →
        Typed (S.toCodeNames.rules B) Γ X (.head t)) ∧
    (∀ {n : Nat} {Γ : Ctx Head n} {X : Tm Head n} {Y : Tm Head (n + 1)},
      Typed (S.toCodeNames.rules B) Γ X (.head t) →
        Typed (S.toCodeNames.rules B) (.snoc Γ X) Y (.head t) →
        Typed (S.toCodeNames.rules B) Γ (.pi X Y) (.head t)) := by
  obtain ⟨t, ht, hmt, hc, w, hj, hw⟩ := U.top
  exact ⟨t, ht, .headType hmt, fun h => .cumul h hc,
    fun hX hY => .cumul (.piForm hX ht hY ht hj) hw⟩

end Universes

/-- `P x : U_m`, for a motive `P` and a point `x`. -/
theorem motiveApp_typed {B : Rules Head} {n : Nat} {Γ : Ctx Head n} {P x : Tm Head n}
    (hP : Typed (S.toCodeNames.rules B) Γ P S.motiveType)
    (hx : Typed (S.toCodeNames.rules B) Γ x (liftClosed S.carrier)) :
    Typed (S.toCodeNames.rules B) Γ (.app P x) (.head S.motive) :=
  .appElim hP hx

end Signature

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion
