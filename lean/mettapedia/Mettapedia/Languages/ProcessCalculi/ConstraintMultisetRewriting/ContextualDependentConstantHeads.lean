import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentTwinsUnder

/-!
# Neutral heads: locals, rigid constants and projections, and their clashes

A neutral term is a **spine**: a head, a local or a rigid constant, followed by eliminations, each an
application or a projection. Its **skeleton** is its head with the list of its eliminations, the
arguments not read. The algorithmic comparison compares two neutral terms elimination by elimination,
and heads last, so **two neutral terms of different skeletons are never equal** at a type where terms
are compared as spines (`spines_skeleton`). This covers distinct locals, distinct constants, a local
against a constant, `fst` against `snd`, a projection against an application, and spines of different
lengths.

The clash reading of the ranked abstraction round reads only spines of locals. The **head clash**
reads, under the abstractions of an equation:

* at a rigid base type, two neutral terms of different skeletons;
* at a universe, two type forms of different kinds, a neutral type counting by its skeleton;
* at an identity type, reflexivity against any neutral term.

Skeletons with heads among the bound locals, or at constants, are kept by every later substitution
(`fixedSkeleton_subst`), so the refutation holds at every later context (`headClash_not_equal`).

The **heads round** is the twin round, and when that round is stuck, the head clash on the prepared
store with homogeneous twins.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentConstantHeads

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentRigidFormers ContextualDependentRank ContextualDependentSpinesMany
open ContextualDependentFragment ContextualDependentDecisiveFragment ContextualDependentConversionBudget
open ContextualDependentFragmentDecisive ContextualDependentRigidDecomposition ContextualDependentOccursFull
open ContextualDependentTwinsUnder ContextualDependentPatternSolver

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Skeletons -/

/-- The head of a neutral spine: a local, by its index, or a constant. -/
inductive SpineHead where
  | local (j : Nat)
  | const (name : DeclName)
  deriving DecidableEq

/-- One elimination of a neutral spine. -/
inductive Elim where
  | app
  | fst
  | snd
  deriving DecidableEq

/-- The skeleton of a neutral spine: its head and its eliminations, outermost first. -/
abbrev Skeleton := SpineHead × List Elim

/-- **The skeleton of a code**, when it is a spine. -/
def skeleton : {n : Nat} → Tm Head n → Option Skeleton
  | _, .var i => some (.local i.val, [])
  | _, .const c => some (.const c, [])
  | _, .app f _ => (skeleton f).map fun s => (s.1, .app :: s.2)
  | _, .fst p => (skeleton p).map fun s => (s.1, .fst :: s.2)
  | _, .snd p => (skeleton p).map fun s => (s.1, .snd :: s.2)
  | _, .head _ | _, .pi _ _ | _, .sigma _ _ | _, .id _ _ _ | _, .lam _ | _, .pair _ _ | _, .refl _ => none

/-- **The skeleton of a spine whose head is fixed under `depth` abstractions**: a local bound by them, or a
constant. -/
def fixedSkeleton (depth : Nat) : {n : Nat} → Tm Head n → Option Skeleton
  | _, .var i => if i.val < depth then some (.local i.val, []) else none
  | _, .const c => some (.const c, [])
  | _, .app f _ => (fixedSkeleton depth f).map fun s => (s.1, .app :: s.2)
  | _, .fst p => (fixedSkeleton depth p).map fun s => (s.1, .fst :: s.2)
  | _, .snd p => (fixedSkeleton depth p).map fun s => (s.1, .snd :: s.2)
  | _, .head _ | _, .pi _ _ | _, .sigma _ _ | _, .id _ _ _ | _, .lam _ | _, .pair _ _ | _, .refl _ => none

theorem fixedSkeleton_skeleton {depth : Nat} :
    ∀ {n : Nat} {t : Tm Head n} {s : Skeleton}, fixedSkeleton depth t = some s → skeleton t = some s
  | _, .var i, s, found => by
      simp only [fixedSkeleton] at found
      split at found
      · exact found
      · cases found
  | _, .const _, _, found => found
  | _, .app f _, s, found => by
      simp only [fixedSkeleton, Option.map_eq_some_iff] at found
      obtain ⟨inner, read, rfl⟩ := found
      simp only [skeleton, fixedSkeleton_skeleton read, Option.map_some]
  | _, .fst p, s, found => by
      simp only [fixedSkeleton, Option.map_eq_some_iff] at found
      obtain ⟨inner, read, rfl⟩ := found
      simp only [skeleton, fixedSkeleton_skeleton read, Option.map_some]
  | _, .snd p, s, found => by
      simp only [fixedSkeleton, Option.map_eq_some_iff] at found
      obtain ⟨inner, read, rfl⟩ := found
      simp only [skeleton, fixedSkeleton_skeleton read, Option.map_some]
  | _, .head _, _, found | _, .pi _ _, _, found | _, .sigma _ _, _, found | _, .id _ _ _, _, found
  | _, .lam _, _, found | _, .pair _ _, _, found | _, .refl _, _, found => by cases found

/-- **A fixed skeleton is kept by every substitution that fixes the bound locals.** -/
theorem fixedSkeleton_subst {depth : Nat} :
    ∀ {n m : Nat} {σ : Sub Head n m}, ContextualDependentSpinesMany.Fixes σ depth → depth ≤ m →
      ∀ {t : Tm Head n} {s : Skeleton}, fixedSkeleton depth t = some s →
        fixedSkeleton depth (Presentation.subst σ t) = some s
  | _, _, σ, fixes, bound, .var i, s, found => by
      simp only [fixedSkeleton] at found
      split at found
      · rename_i small
        have fixed : σ i = .var ⟨i.val, by omega⟩ := fixes i.val i.isLt (by omega) small
        change fixedSkeleton depth (σ i) = some s
        rw [fixed]
        simp only [fixedSkeleton, if_pos small]
        exact found
      · cases found
  | _, _, _, _, _, .const _, _, found => found
  | _, _, σ, fixes, bound, .app f _, s, found => by
      simp only [fixedSkeleton, Option.map_eq_some_iff] at found
      obtain ⟨inner, read, rfl⟩ := found
      change (fixedSkeleton depth (Presentation.subst σ f)).map _ = _
      rw [fixedSkeleton_subst fixes bound read]
      rfl
  | _, _, σ, fixes, bound, .fst p, s, found => by
      simp only [fixedSkeleton, Option.map_eq_some_iff] at found
      obtain ⟨inner, read, rfl⟩ := found
      change (fixedSkeleton depth (Presentation.subst σ p)).map _ = _
      rw [fixedSkeleton_subst fixes bound read]
      rfl
  | _, _, σ, fixes, bound, .snd p, s, found => by
      simp only [fixedSkeleton, Option.map_eq_some_iff] at found
      obtain ⟨inner, read, rfl⟩ := found
      change (fixedSkeleton depth (Presentation.subst σ p)).map _ = _
      rw [fixedSkeleton_subst fixes bound read]
      rfl
  | _, _, _, _, _, .head _, _, found | _, _, _, _, _, .pi _ _, _, found | _, _, _, _, _, .sigma _ _, _, found
  | _, _, _, _, _, .id _ _ _, _, found | _, _, _, _, _, .lam _, _, found | _, _, _, _, _, .pair _ _, _, found
  | _, _, _, _, _, .refl _, _, found => by cases found

/-- **A spine of a rigid head is neutral.** -/
theorem skeleton_neutral (rigid : ∀ name, S.roles name = .rigid) :
    ∀ {n : Nat} {t : Tm Head n} {s : Skeleton}, skeleton t = some s → Neutral S.roles t
  | _, .var i, _, _ => .var i
  | _, .const c, _, _ => .rigid [] (rigid c)
  | _, .app f _, s, found => by
      simp only [skeleton, Option.map_eq_some_iff] at found
      obtain ⟨inner, read, _⟩ := found
      exact .app (skeleton_neutral rigid read)
  | _, .fst p, s, found => by
      simp only [skeleton, Option.map_eq_some_iff] at found
      obtain ⟨inner, read, _⟩ := found
      exact .fst (skeleton_neutral rigid read)
  | _, .snd p, s, found => by
      simp only [skeleton, Option.map_eq_some_iff] at found
      obtain ⟨inner, read, _⟩ := found
      exact .snd (skeleton_neutral rigid read)
  | _, .head _, _, found | _, .pi _ _, _, found | _, .sigma _ _, _, found | _, .id _ _ _, _, found
  | _, .lam _, _, found | _, .pair _ _, _, found | _, .refl _, _, found => by cases found

/-! ## The algorithmic comparison compares skeletons -/

/-- **Two spines compared by the algorithmic equality have one skeleton.** -/
theorem spines_skeleton {n : Nat} {Γ : Ctx Head n} :
    ∀ (l r U : Tm Head n), Algorithmic S.R S.roles (.spines Γ l r U) → skeleton l = skeleton r
  | .var _, _, _, derivation => by
      cases derivation
      rfl
  | .const _, _, _, derivation => by
      cases derivation
      rfl
  | .app f _, _, _, derivation => by
      cases derivation with
      | app inner _ =>
          cases inner with
          | spinesW prefixSpines _ _ =>
              simp only [skeleton, spines_skeleton _ _ _ prefixSpines]
  | .fst p, _, _, derivation => by
      cases derivation with
      | fst inner =>
          cases inner with
          | spinesW prefixSpines _ _ =>
              simp only [skeleton, spines_skeleton _ _ _ prefixSpines]
  | .snd p, _, _, derivation => by
      cases derivation with
      | snd inner =>
          cases inner with
          | spinesW prefixSpines _ _ =>
              simp only [skeleton, spines_skeleton _ _ _ prefixSpines]
  | .head _, _, _, derivation | .pi _ _, _, _, derivation | .sigma _ _, _, _, derivation
  | .id _ _ _, _, _, derivation | .lam _, _, _, derivation | .pair _ _, _, _, derivation
  | .refl _, _, _, derivation => by cases derivation

section Refutation

variable (facts : FormFacts S.R S.roles) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include complete in
/-- **Two neutral terms of different skeletons are never equal** at a base type. -/
theorem skeletons_not_equal {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {l r C : Tm Head n}
    (base : BaseType S C) (leftNeutral : Neutral S.roles l) (rightNeutral : Neutral S.roles r)
    (differ : skeleton l ≠ skeleton r) : ¬ Equal S.R Γ l r C := by
  intro same
  obtain ⟨_, spines⟩ := terms_neutral_spines base leftNeutral rightNeutral (complete formed same)
  exact differ (spines_skeleton _ _ _ spines)

/-! ## Kinds of type forms -/

/-- **The kind of a type form**: a former, a universe head, or a neutral type by its skeleton. -/
inductive TypeKind where
  | pi
  | sigma
  | id
  | head
  | neutral (s : Skeleton)
  deriving DecidableEq

/-- Read the kind of a type form under `depth` abstractions. -/
def typeKind (depth : Nat) {n : Nat} (t : Tm Head n) : Option TypeKind :=
  match t with
  | .pi _ _ => some .pi
  | .sigma _ _ => some .sigma
  | .id _ _ _ => some .id
  | .head _ => some .head
  | .lam _ | .pair _ _ | .refl _ => none
  | .var _ | .const _ | .app _ _ | .fst _ | .snd _ => (fixedSkeleton depth t).map .neutral

theorem typeKind_subst {n m : Nat} {depth : Nat} {σ : Sub Head n m} (fixes : ContextualDependentSpinesMany.Fixes σ depth)
    (bound : depth ≤ m) {t : Tm Head n} {k : TypeKind} (kind : typeKind depth t = some k) :
    typeKind depth (Presentation.subst σ t) = some k := by
  cases t with
  | pi _ _ => exact kind
  | sigma _ _ => exact kind
  | id _ _ _ => exact kind
  | head _ => exact kind
  | lam _ => cases kind
  | pair _ _ => cases kind
  | refl _ => cases kind
  | var i =>
      simp only [typeKind, Option.map_eq_some_iff] at kind
      obtain ⟨s, read, rfl⟩ := kind
      have kept := fixedSkeleton_subst fixes bound read
      cases image : Presentation.subst σ (.var i) <;> rw [image] at kept <;> simp_all [typeKind, fixedSkeleton]
  | const c =>
      simp only [typeKind, Option.map_eq_some_iff] at kind
      obtain ⟨s, read, rfl⟩ := kind
      change (fixedSkeleton depth (Tm.const (Head := Head) (n := m) c)).map TypeKind.neutral = _
      simp only [fixedSkeleton, Option.some.injEq, Option.map_some] at read ⊢
      subst read
      rfl
  | app f a =>
      simp only [typeKind, Option.map_eq_some_iff] at kind
      obtain ⟨s, read, rfl⟩ := kind
      have kept := fixedSkeleton_subst fixes bound read
      change (fixedSkeleton depth (Presentation.subst σ (.app f a))).map _ = _
      rw [kept]
      rfl
  | fst p =>
      simp only [typeKind, Option.map_eq_some_iff] at kind
      obtain ⟨s, read, rfl⟩ := kind
      have kept := fixedSkeleton_subst fixes bound read
      change (fixedSkeleton depth (Presentation.subst σ (.fst p))).map _ = _
      rw [kept]
      rfl
  | snd p =>
      simp only [typeKind, Option.map_eq_some_iff] at kind
      obtain ⟨s, read, rfl⟩ := kind
      have kept := fixedSkeleton_subst fixes bound read
      change (fixedSkeleton depth (Presentation.subst σ (.snd p))).map _ = _
      rw [kept]
      rfl

include rigid in
theorem typeKind_form {n : Nat} {depth : Nat} {t : Tm Head n} {k : TypeKind} (kind : typeKind depth t = some k) :
    IsTypeForm S.roles t := by
  cases t with
  | pi _ _ => exact .inr (.inl ⟨_, _, rfl⟩)
  | sigma _ _ => exact .inr (.inr (.inl ⟨_, _, rfl⟩))
  | id _ _ _ => exact .inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))
  | head _ => exact .inl ⟨_, rfl⟩
  | lam _ => cases kind
  | pair _ _ => cases kind
  | refl _ => cases kind
  | var _ | const _ | app _ _ | fst _ | snd _ =>
      simp only [typeKind, Option.map_eq_some_iff] at kind
      obtain ⟨s, read, _⟩ := kind
      exact .inr (.inr (.inr (.inr (.inl (skeleton_neutral rigid (fixedSkeleton_skeleton read))))))

/-- The kind of a neutral type is its skeleton. -/
theorem neutral_typeKind {n : Nat} {depth : Nat} {t : Tm Head n} {k : TypeKind} (neutral : Neutral S.roles t)
    (kind : typeKind depth t = some k) : ∃ s, k = .neutral s ∧ fixedSkeleton depth t = some s := by
  cases t with
  | pi A B => exact absurd rfl (neutral.not_former.2.1 A B)
  | sigma A B => exact absurd rfl (neutral.not_former.2.2.1 A B)
  | id A a b => exact absurd rfl (neutral.not_former.2.2.2 A a b)
  | head h => exact absurd rfl (neutral.not_former.1 h)
  | lam _ => cases kind
  | pair _ _ => cases kind
  | refl _ => cases kind
  | var _ | const _ | app _ _ | fst _ | snd _ =>
      simp only [typeKind, Option.map_eq_some_iff] at kind
      obtain ⟨s, read, rfl⟩ := kind
      exact ⟨s, rfl, read⟩

/-! ## Head clashes under abstractions -/

/-- **A head clash under abstractions.** -/
inductive HeadClash (R : Rules Head) : Nat → {n : Nat} → Tm Head n → Tm Head n → Tm Head n → Prop
  | base {depth n : Nat} {C l r : Tm Head n} {s s' : Skeleton} : rigidBase depth C = true →
      fixedSkeleton depth l = some s → fixedSkeleton depth r = some s' → s ≠ s' → HeadClash R depth C l r
  | universal {depth n : Nat} {u : Head} {l r : Tm Head n} {k k' : TypeKind} : R.isUniverse u →
      typeKind depth l = some k → typeKind depth r = some k' → k ≠ k' → HeadClash R depth (.head u) l r
  | reflNeutral {depth n : Nat} {C x y z r : Tm Head n} {s : Skeleton} : fixedSkeleton depth r = some s →
      HeadClash R depth (.id C x y) (.refl z) r
  | neutralRefl {depth n : Nat} {C x y z l : Tm Head n} {s : Skeleton} : fixedSkeleton depth l = some s →
      HeadClash R depth (.id C x y) l (.refl z)
  | bind {depth n : Nat} {D : Tm Head n} {T l r : Tm Head (n + 1)} :
      HeadClash R (depth + 1) T l r → HeadClash R depth (.pi D T) (.lam l) (.lam r)

omit [UniverseLevel.LevelOrder L] in
/-- **The reading is kept by substitutions that fix the locals.** -/
theorem HeadClash.subst {R : Rules Head} {depth n : Nat} {annotation left right : Tm Head n}
    (clash : HeadClash R depth annotation left right) :
    ∀ {m : Nat} (σ : Sub Head n m), ContextualDependentSpinesMany.Fixes σ depth → depth ≤ m →
      HeadClash R depth (Presentation.subst σ annotation) (Presentation.subst σ left)
        (Presentation.subst σ right) := by
  induction clash with
  | base base kl kr differ =>
      intro m σ fixes bound
      exact .base (rigidBase_subst fixes bound base) (fixedSkeleton_subst fixes bound kl)
        (fixedSkeleton_subst fixes bound kr) differ
  | universal hu kl kr differ =>
      intro m σ fixes bound
      exact .universal hu (typeKind_subst fixes bound kl) (typeKind_subst fixes bound kr) differ
  | reflNeutral kr =>
      intro m σ fixes bound
      exact .reflNeutral (fixedSkeleton_subst fixes bound kr)
  | neutralRefl kl =>
      intro m σ fixes bound
      exact .neutralRefl (fixedSkeleton_subst fixes bound kl)
  | bind _ ih =>
      intro m σ fixes bound
      exact .bind (ih (liftSub σ) fixes.lift (by omega))

include facts rigid complete in
/-- **A head clash under abstractions never holds.** -/
theorem headClash_not_equal {depth n : Nat} {annotation left right : Tm Head n}
    (clash : HeadClash S.R depth annotation left right) :
    ∀ {Γ : Ctx Head n}, CtxFormed S.R Γ → TypedEquality.Typed S.R Γ left annotation →
      TypedEquality.Typed S.R Γ right annotation → ¬ Equal S.R Γ left right annotation := by
  induction clash with
  | base base kl kr differ =>
      intro Γ formed _ _ same
      refine skeletons_not_equal complete formed (rigidBase_spec base)
        (skeleton_neutral rigid (fixedSkeleton_skeleton kl)) (skeleton_neutral rigid (fixedSkeleton_skeleton kr))
        ?_ same
      rw [fixedSkeleton_skeleton kl, fixedSkeleton_skeleton kr]
      intro equal
      exact differ (Option.some.inj equal)
  | @universal depth n u l r k k' hu kl kr differ =>
      intro Γ formed _ _ same
      have matched := facts.forms ⟨u, hu, same⟩ formed (typeKind_form rigid kl) (typeKind_form rigid kr)
      rcases matched with ⟨_, _, rfl, rfl, _⟩ | ⟨_, _, _, _, rfl, rfl, _⟩ | ⟨_, _, _, _, rfl, rfl, _⟩ |
        ⟨_, _, _, _, _, _, rfl, rfl, _⟩ | ⟨T, _, isInductive, rfl, rfl⟩ | ⟨leftNeutral, rightNeutral⟩
      · simp only [typeKind, Option.some.injEq] at kl kr
        exact differ (kl.symm.trans kr)
      · simp only [typeKind, Option.some.injEq] at kl kr
        exact differ (kl.symm.trans kr)
      · simp only [typeKind, Option.some.injEq] at kl kr
        exact differ (kl.symm.trans kr)
      · simp only [typeKind, Option.some.injEq] at kl kr
        exact differ (kl.symm.trans kr)
      · rw [rigid T] at isInductive
        cases isInductive
      · obtain ⟨s, rfl, sl⟩ := neutral_typeKind leftNeutral kl
        obtain ⟨s', rfl, sr⟩ := neutral_typeKind rightNeutral kr
        refine skeletons_not_equal complete formed (.inr (.inl ⟨u, rfl⟩)) leftNeutral rightNeutral ?_ same
        rw [fixedSkeleton_skeleton sl, fixedSkeleton_skeleton sr]
        intro equal
        exact differ (by rw [Option.some.inj equal])
  | reflNeutral kr =>
      intro Γ formed _ _ same
      exact refl_neutral_not_equal complete formed (skeleton_neutral rigid (fixedSkeleton_skeleton kr)) same
  | neutralRefl kl =>
      intro Γ formed _ _ same
      exact refl_neutral_not_equal complete formed (skeleton_neutral rigid (fixedSkeleton_skeleton kl)) (.symm same)
  | bind _ ih =>
      intro Γ formed tl tr same
      obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
      exact ih (formed.snoc ⟨u, hu, tD⟩) (Typed.lam_inv facts tl formed) (Typed.lam_inv facts tr formed)
        (lam_equal_inv facts formed same)

end Refutation

/-! ## Deciding a head clash -/

variable [∀ head, Decidable (S.R.isUniverse head)]

/-- Two spines of different fixed skeletons. -/
def skeletonsDiffer {n : Nat} (depth : Nat) (left right : Tm Head n) : Bool :=
  match fixedSkeleton depth left, fixedSkeleton depth right with
  | some s, some s' => decide (s ≠ s')
  | _, _ => false

/-- Two type forms of different kinds. -/
def kindsDiffer {n : Nat} (depth : Nat) (left right : Tm Head n) : Bool :=
  match typeKind depth left, typeKind depth right with
  | some k, some k' => decide (k ≠ k')
  | _, _ => false

/-- Reflexivity against a spine with a fixed head. -/
def reflAgainst {n : Nat} (depth : Nat) (left right : Tm Head n) : Bool :=
  match left, fixedSkeleton depth right with
  | .refl _, some _ => true
  | _, _ => false

theorem reflAgainst_spec {n : Nat} {depth : Nat} {left right : Tm Head n} (found : reflAgainst depth left right = true) :
    ∃ z s, left = .refl z ∧ fixedSkeleton depth right = some s := by
  unfold reflAgainst at found
  split at found
  · rename_i z s read
    exact ⟨z, s, rfl, read⟩
  · cases found

/-- The head clash test at the bottom of the reading. -/
def headClashBase {n : Nat} (depth : Nat) (C left right : Tm Head n) : Bool :=
  (rigidBase depth C && skeletonsDiffer depth left right) ||
    (universeCode (S := S) C && kindsDiffer depth left right) ||
    (identityCode C && (reflAgainst depth left right || reflAgainst depth right left))

/-- **The decision of a head clash under abstractions**, by the codes. -/
def headClashAt : {n : Nat} → Nat → Tm Head n → Tm Head n → Tm Head n → Bool
  | _, depth, .pi _ T, .lam left, .lam right => headClashAt (depth + 1) T left right
  | _, depth, C, left, right => headClashBase (S := S) depth C left right

theorem headClashBase_sound {n : Nat} {depth : Nat} {C left right : Tm Head n}
    (found : headClashBase (S := S) depth C left right = true) : HeadClash S.R depth C left right := by
  unfold headClashBase at found
  simp only [Bool.or_eq_true, Bool.and_eq_true] at found
  rcases found with (⟨base, differ⟩ | ⟨universal, differ⟩) | ⟨identity, against | against⟩
  · unfold skeletonsDiffer at differ
    cases sl : fixedSkeleton depth left with
    | none => rw [sl] at differ; cases differ
    | some s =>
        cases sr : fixedSkeleton depth right with
        | none => rw [sl, sr] at differ; cases differ
        | some s' =>
            rw [sl, sr] at differ
            exact .base base sl sr (by simpa using differ)
  · cases C with
    | head u =>
        simp only [universeCode, decide_eq_true_eq] at universal
        unfold kindsDiffer at differ
        cases kl : typeKind depth left with
        | none => rw [kl] at differ; cases differ
        | some k =>
            cases kr : typeKind depth right with
            | none => rw [kl, kr] at differ; cases differ
            | some k' =>
                rw [kl, kr] at differ
                exact .universal universal kl kr (by simpa using differ)
    | _ => simp [universeCode] at universal
  · cases C with
    | id C x y =>
        obtain ⟨z, s, rfl, read⟩ := reflAgainst_spec against
        exact .reflNeutral read
    | _ => simp [identityCode] at identity
  · cases C with
    | id C x y =>
        obtain ⟨z, s, rfl, read⟩ := reflAgainst_spec against
        exact .neutralRefl read
    | _ => simp [identityCode] at identity

theorem headClashAt_cases {n : Nat} {depth : Nat} {annotation left right : Tm Head n}
    (found : headClashAt (S := S) depth annotation left right = true) :
    (∃ D T l r, annotation = .pi D T ∧ left = .lam l ∧ right = .lam r ∧
        headClashAt (S := S) (depth + 1) T l r = true) ∨
      headClashBase (S := S) depth annotation left right = true := by
  cases annotation with
  | pi D T =>
      cases left with
      | lam l =>
          cases right with
          | lam r => exact .inl ⟨D, T, l, r, rfl, rfl, rfl, by simpa [headClashAt] using found⟩
          | _ => exact .inr (by simpa [headClashAt] using found)
      | _ => exact .inr (by simpa [headClashAt] using found)
  | _ => exact .inr (by simpa [headClashAt] using found)

theorem headClashAt_sound : ∀ {n : Nat} (depth : Nat) (annotation left right : Tm Head n),
    headClashAt (S := S) depth annotation left right = true → HeadClash S.R depth annotation left right
  | _, depth, .pi D T, left, right, found => by
      rcases headClashAt_cases found with ⟨D', T', l, r, same, rfl, rfl, inner⟩ | base
      · injection same with _ sameD sameT
        subst sameD
        subst sameT
        exact .bind (headClashAt_sound (depth + 1) T l r inner)
      · exact headClashBase_sound base
  | _, depth, .var _, left, right, found | _, depth, .const _, left, right, found
  | _, depth, .head _, left, right, found | _, depth, .sigma _ _, left, right, found
  | _, depth, .id _ _ _, left, right, found | _, depth, .lam _, left, right, found
  | _, depth, .app _ _, left, right, found | _, depth, .pair _ _, left, right, found
  | _, depth, .fst _, left, right, found | _, depth, .snd _, left, right, found
  | _, depth, .refl _, left, right, found => by
      rcases headClashAt_cases found with ⟨_, _, _, _, same, _⟩ | base
      · cases same
      · exact headClashBase_sound base

/-! ## The head clash rule -/

variable [DecidableEq Head]

/-- **A store equation whose sides clash at their heads under its abstractions**, at one annotation code. -/
structure HeadClashShape {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Type where
  same : equation.2.1.code = equation.1.1.code
  clash : HeadClash S.R 0 equation.1.1.code equation.1.2.code equation.2.2.code

/-- Read a head clash from the codes; no budget. -/
def headClashShape {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Option (HeadClashShape equation) :=
  if same : equation.2.1.code = equation.1.1.code then
    if found : headClashAt (S := S) 0 equation.1.1.code equation.1.2.code equation.2.2.code = true then
      some ⟨same, headClashAt_sound _ _ _ _ found⟩
    else none
  else none

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

omit [∀ head, Decidable (S.R.isUniverse head)] [DecidableEq Head] in
include facts rigid complete in
/-- **A head clash has no solution at any later context.** -/
theorem HeadClashShape.refutes {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (shape : HeadClashShape equation)
    {Δ : Context S.R} (σ : Δ ⟶ Θ) : ¬ (frames S.levels).Solves σ equation := by
  intro solved
  rw [solves_raw] at solved
  have tLeft := equation.1.2.typed.substitute σ.typed
  have tRight := equation.2.2.typed.substitute σ.typed
  rw [shape.same] at tRight
  exact headClash_not_equal facts rigid complete
    (shape.clash.subst σ.substitution (fun _ _ _ small => absurd small (Nat.not_lt_zero _)) (Nat.zero_le _))
    Δ.formed tLeft tRight solved.2

/-- **The head clash rule**: refute the store at the first equation whose sides clash at their heads. -/
def headClashSearch {Θ : Context S.R} : (problem : EquationStore (TotalTerm Θ)) → Option (Found problem)
  | [] => none
  | equation :: rest =>
      match headClashShape equation with
      | some shape => some (.refuted fun ⟨_, σ, solved⟩ =>
          shape.refutes facts rigid complete σ (solved equation List.mem_cons_self))
      | none => (headClashSearch rest).map (Found.keepLeft equation)

/-- The refutation of the head clash rule on an update of a store, moved back to the store. -/
def headClashOf {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (prepared : Update S.levels problem) :
    Option (PLift (¬ (frames S.levels).Solvable problem)) :=
  match headClashSearch facts rigid complete prepared.remaining with
  | some (.refuted absent) => some ⟨fun solvable => absent (prepared.solvable_iff.mp solvable)⟩
  | _ => none

/-! ## The heads round -/

variable [DecidableRel S.R.headEq] [DecidableRel S.R.cumulative]
variable (declared : DeclaredTypesFormed S.R) (choices : ExecutableChecking.HeadChoices S.R)
  (reducer : ExecutableReduction.Reducer S.R) (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)

/-- The prepared store with homogeneous twins, as an update of the store. -/
def preparedTwins (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Update S.levels problem :=
  (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).then
    (collapse facts roots heads algebra reducer fuel
      (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining)

/-- The head clash on the prepared store with homogeneous twins. -/
def headsRefuted (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Option (PLift (¬ (frames S.levels).Solvable problem)) :=
  headClashOf facts rigid complete (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem)

/-- **One heads round**: the twin round; when it is stuck, the head clash on the prepared store with
homogeneous twins. -/
def headsRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match twinRound facts roots heads algebra rigid complete reducer declared choices root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | .stuck =>
      match headsRefuted facts roots heads algebra rigid complete reducer root rootComplete fuel problem with
      | some absent => .refuted absent.down
      | none => .stuck
  | other => other

/-- **The heads family**, at the weight rank. -/
noncomputable def headsFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := headsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel

/-! ## Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

omit [DecidableRel S.R.cumulative] in
include stable in
theorem headsRefuted_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      (headsRefuted facts roots heads algebra rigid complete reducer root rootComplete fuel problem).isSome := by
  unfold headsRefuted preparedTwins
  exact EventuallyConst.dep (h := fun fuel => ContextualDependentNormalizing.prepare root rootComplete facts roots heads
      fuel problem)
    (k := fun fuel prepared => (headClashOf facts rigid complete
      (prepared.then (collapseOf (collapsed facts roots heads algebra reducer fuel prepared.remaining)))).isSome)
    (prepare_const root rootComplete facts roots heads problem)
    (fun prepared => EventuallyConst.comp (fun store => (headClashOf facts rigid complete
        (prepared.then (collapseOf store))).isSome)
      (collapsed_const facts roots heads algebra reducer stable prepared.remaining))

theorem headsRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (headsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem) =
      (roundView (twinRound facts roots heads algebra rigid complete reducer declared choices root normalizes
          certifyNormal headTypingUnique rootComplete fuel problem)).or
        (if (headsRefuted facts roots heads algebra rigid complete reducer root rootComplete fuel problem).isSome then
          some none else none) := by
  unfold headsRound
  cases twinRound facts roots heads algebra rigid complete reducer declared choices root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | stuck =>
      cases headsRefuted facts roots heads algebra rigid complete reducer root rootComplete fuel problem <;> rfl
  | progress update smaller => rfl
  | refuted absent => rfl

include stable in
/-- **The heads round is eventually constant on every store.** -/
theorem headsRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => headsRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => headsRound_view facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete fuel problem) ?_
  exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) × Bool =>
      pair.1.or (if pair.2 then some none else none))
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (twinRound_const facts roots heads algebra rigid complete reducer declared choices
        root normalizes certifyNormal headTypingUnique rootComplete stable problem))
      (headsRefuted_const facts roots heads algebra rigid complete reducer root rootComplete stable problem))

include stable in
/-- **The heads family settles** on every class of stores on which, at each nonempty store and from some
budget on, its round is not stuck and keeps every residual store in the class. -/
noncomputable def headsSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        headsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
            headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          headsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
              headTypingUnique rootComplete larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (headsFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => headsRound_const facts roots heads algebra rigid complete declared choices reducer
    root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end ContextualDependentConstantHeads
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
