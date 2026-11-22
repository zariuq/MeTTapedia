import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSpinesManyDependent

/-!
# Rigid clashes under abstractions

R75's clash test reads the outermost codes of a store equation. A fragment equation of the kind
"rigid–rigid with distinct heads" may clash only **under its abstractions**: `λ x. Π x x ≐ λ x. Σ x x`,
or `λ f g. f a ≐ λ f g. g a`. Such an equation never holds:

* at a universe, two types whose outermost shapes differ (Π, Σ, identity type, universe head, or a
  spine of a local, with distinct locals counting as distinct shapes) are never equal: their weak-head
  forms would have to match (`FormFacts.forms`);
* at a rigid base type, two spines of distinct locals are never equal: the algorithmic comparison
  compares spines of one head only (`spines_heads`).

The reading under abstractions keeps the bound locals fixed under every later substitution
(`ClashAt.subst`), so the refutation holds at every later context (`clash_not_equal`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFragmentDecisive

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentInPlace
open ContextualDependentRigidFormers ContextualDependentEtaLong ContextualDependentOccursCheck
open ContextualDependentRank ContextualDependentOccursFull ContextualDependentRigidDecomposition
open ContextualDependentSpinesMany ContextualDependentEtaExpansion

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Rigid shapes -/

/-- **The rigid shape of a code**: a type former, a universe head, or a spine of the local `j`. -/
inductive RigidKind where
  | pi
  | sigma
  | id
  | head
  | local (j : Nat)
  deriving DecidableEq

/-- Read the rigid shape of a code under `depth` locals. -/
def rigidKind {n : Nat} (depth : Nat) : Tm Head n → Option RigidKind
  | .pi _ _ => some .pi
  | .sigma _ _ => some .sigma
  | .id _ _ _ => some .id
  | .head _ => some .head
  | .var i => if i.val < depth then some (.local i.val) else none
  | .app f a => match spineOf (.app f a) with
      | some (h, _) => if h.val < depth then some (.local h.val) else none
      | none => none
  | .const _ | .lam _ | .pair _ _ | .fst _ | .snd _ | .refl _ => none

theorem rigidKind_local {n : Nat} {depth : Nat} {t : Tm Head n} {j : Nat}
    (kind : rigidKind depth t = some (.local j)) :
    ∃ (h : Fin n) (as : List (Tm Head n)), t = appSpine (.var h) as ∧ h.val = j ∧ j < depth := by
  cases t with
  | var i =>
      simp only [rigidKind] at kind
      split at kind
      · rename_i small
        simp only [Option.some.injEq, RigidKind.local.injEq] at kind
        exact ⟨i, [], rfl, kind, kind ▸ small⟩
      · cases kind
  | app f a =>
      simp only [rigidKind] at kind
      split at kind
      · rename_i h as found
        split at kind
        · rename_i small
          simp only [Option.some.injEq, RigidKind.local.injEq] at kind
          exact ⟨h, as, spineOf_spec found, kind, kind ▸ small⟩
        · cases kind
      · cases kind
  | _ => simp [rigidKind] at kind

theorem rigidKind_subst {n m : Nat} {depth : Nat} {σ : Sub Head n m} (fixes : Fixes σ depth) (bound : depth ≤ m)
    {t : Tm Head n} {k : RigidKind} (kind : rigidKind depth t = some k) :
    rigidKind depth (Presentation.subst σ t) = some k := by
  cases k with
  | «local» j =>
      obtain ⟨h, as, rfl, rfl, small⟩ := rigidKind_local kind
      have fixed : σ h = .var ⟨h.val, by omega⟩ := fixes h.val h.isLt (by omega) small
      rw [subst_appSpine]
      change rigidKind depth (appSpine (σ h) _) = _
      rw [fixed]
      rcases List.eq_nil_or_concat (as.map (Presentation.subst σ)) with empty | ⟨init, last, split⟩
      · rw [empty]
        simp [rigidKind, small]
      · rw [split, List.concat_eq_append, appSpine_concat]
        have read := spineOf_appSpine (Head := Head) ⟨h.val, by omega⟩ (init ++ [last])
        rw [appSpine_concat] at read
        simp only [rigidKind, read, small, if_true]
  | _ =>
      cases t <;> simp_all [rigidKind, Presentation.subst]
      all_goals (split at kind <;> simp_all)

/-! ## Spines of distinct locals -/

/-- **The algorithmic comparison of two spines of variables compares one head.** -/
theorem spines_heads {n : Nat} {Γ : Ctx Head n} (i j : Fin n) : ∀ (as bs : List (Tm Head n)) {U : Tm Head n},
    Algorithmic S.R S.roles (.spines Γ (appSpine (.var i) as) (appSpine (.var j) bs) U) → i = j := by
  intro as
  induction as using List.reverseRecOn with
  | nil =>
      intro bs U derivation
      rcases List.eq_nil_or_concat bs with rfl | ⟨bs', b, rfl⟩
      · cases derivation
        rfl
      · rw [List.concat_eq_append, appSpine_concat] at derivation
        cases derivation
  | append_singleton as a ih =>
      intro bs U derivation
      rcases List.eq_nil_or_concat bs with rfl | ⟨bs', b, rfl⟩
      · rw [appSpine_concat] at derivation
        cases derivation
      · rw [List.concat_eq_append, appSpine_concat, appSpine_concat] at derivation
        cases derivation with
        | app inner _ =>
            cases inner with
            | spinesW prefixSpines _ _ => exact ih bs' prefixSpines

/-- **At a base type, the algorithmic comparison of two neutral terms compares their spines.** -/
theorem terms_neutral_spines {n : Nat} {Γ : Ctx Head n} {l r C : Tm Head n} (base : BaseType S C)
    (leftNeutral : Neutral S.roles l) (rightNeutral : Neutral S.roles r)
    (derivation : Algorithmic S.R S.roles (.terms Γ l r C)) :
    ∃ U, Algorithmic S.R S.roles (.spines Γ l r U) := by
  cases derivation with
  | terms typeRed _ leftRed rightRed inner =>
      have typeSame := WhRed.eq_of_whnf (S := S) base.whnf typeRed.red
      have leftSame := WhRed.eq_of_whnf (S := S) (leftNeutral.whnf S.shape) leftRed.red
      have rightSame := WhRed.eq_of_whnf (S := S) (rightNeutral.whnf S.shape) rightRed.red
      subst typeSame
      subst leftSame
      subst rightSame
      cases inner with
      | univ _ _ _ types =>
          cases types with
          | heads => exact absurd rfl (leftNeutral.not_former.1 _)
          | pi => exact absurd rfl (leftNeutral.not_former.2.1 _ _)
          | sigma => exact absurd rfl (leftNeutral.not_former.2.2.1 _ _)
          | id => exact absurd rfl (leftNeutral.not_former.2.2.2 _ _ _)
          | inductiveType role => exact absurd rfl (leftNeutral.ne_inductive role)
          | neutralTypes _ _ _ spines =>
              cases spines with
              | spinesW inner _ _ => exact ⟨_, inner⟩
      | eta =>
          rcases base with ⟨_, _, _, impossible⟩ | ⟨_, impossible⟩ | neutral
          · cases impossible
          · cases impossible
          · exact absurd rfl (neutral.not_former.2.1 _ _)
      | sigmaEta =>
          rcases base with ⟨_, _, _, impossible⟩ | ⟨_, impossible⟩ | neutral
          · cases impossible
          · cases impossible
          · exact absurd rfl (neutral.not_former.2.2.1 _ _)
      | refl => exact absurd rfl leftNeutral.ne_refl
      | spine _ _ _ _ _ spines =>
          cases spines with
          | spinesW inner _ _ => exact ⟨_, inner⟩

/-! ## Clashes under abstractions -/

/-- **A rigid clash under abstractions**: at a universe, two codes of distinct rigid shapes; at a rigid
base type, two spines of distinct locals; or the same under one more abstraction. -/
inductive ClashAt (R : Rules Head) : Nat → {n : Nat} → Tm Head n → Tm Head n → Tm Head n → Prop
  | universal {depth n : Nat} {u : Head} {l r : Tm Head n} {k k' : RigidKind} : R.isUniverse u →
      rigidKind depth l = some k → rigidKind depth r = some k' → k ≠ k' → ClashAt R depth (.head u) l r
  | locals {depth n : Nat} {C : Tm Head n} {i j : Fin n} {as bs : List (Tm Head n)} : rigidBase depth C = true →
      i.val < depth → j.val < depth → i ≠ j → ClashAt R depth C (appSpine (.var i) as) (appSpine (.var j) bs)
  | reflSpine {depth n : Nat} {C x y z : Tm Head n} {i : Fin n} {as : List (Tm Head n)} :
      i.val < depth → ClashAt R depth (.id C x y) (.refl z) (appSpine (.var i) as)
  | spineRefl {depth n : Nat} {C x y z : Tm Head n} {i : Fin n} {as : List (Tm Head n)} :
      i.val < depth → ClashAt R depth (.id C x y) (appSpine (.var i) as) (.refl z)
  | bind {depth n : Nat} {D : Tm Head n} {T l r : Tm Head (n + 1)} :
      ClashAt R (depth + 1) T l r → ClashAt R depth (.pi D T) (.lam l) (.lam r)

/-- **The reading is kept by substitutions that fix the locals.** -/
theorem ClashAt.subst {R : Rules Head} {depth n : Nat} {annotation left right : Tm Head n}
    (clash : ClashAt R depth annotation left right) :
    ∀ {m : Nat} (σ : Sub Head n m), Fixes σ depth → depth ≤ m →
      ClashAt R depth (Presentation.subst σ annotation) (Presentation.subst σ left) (Presentation.subst σ right) := by
  induction clash with
  | universal hu kl kr differ =>
      intro m σ fixes bound
      exact .universal hu (rigidKind_subst fixes bound kl) (rigidKind_subst fixes bound kr) differ
  | @locals depth n C i j as bs base si sj differ =>
      intro m σ fixes bound
      rw [subst_appSpine, subst_appSpine]
      have fi : σ i = .var ⟨i.val, by omega⟩ := fixes i.val i.isLt (by omega) si
      have fj : σ j = .var ⟨j.val, by omega⟩ := fixes j.val j.isLt (by omega) sj
      change ClashAt R depth _ (appSpine (σ i) _) (appSpine (σ j) _)
      rw [fi, fj]
      refine .locals (rigidBase_subst fixes bound base) si sj ?_
      intro same
      exact differ (Fin.ext (by simpa using congrArg Fin.val same))
  | @reflSpine depth n C x y z i as si =>
      intro m σ fixes bound
      rw [subst_appSpine]
      have fi : σ i = .var ⟨i.val, by omega⟩ := fixes i.val i.isLt (by omega) si
      change ClashAt R depth _ _ (appSpine (σ i) _)
      rw [fi]
      exact .reflSpine si
  | @spineRefl depth n C x y z i as si =>
      intro m σ fixes bound
      rw [subst_appSpine]
      have fi : σ i = .var ⟨i.val, by omega⟩ := fixes i.val i.isLt (by omega) si
      change ClashAt R depth _ (appSpine (σ i) _) _
      rw [fi]
      exact .spineRefl si
  | bind _ ih =>
      intro m σ fixes bound
      exact .bind (ih (liftSub σ) fixes.lift (by omega))

theorem rigidKind_form {n : Nat} {depth : Nat} {t : Tm Head n} {k : RigidKind}
    (kind : rigidKind depth t = some k) : IsTypeForm S.roles t := by
  cases k with
  | «local» j =>
      obtain ⟨h, as, rfl, _, _⟩ := rigidKind_local kind
      exact .inr (.inr (.inr (.inr (.inl (neutral_appSpine h as)))))
  | _ =>
      cases t <;> simp [rigidKind] at kind
      all_goals first
        | exact .inl ⟨_, rfl⟩
        | exact .inr (.inl ⟨_, _, rfl⟩)
        | exact .inr (.inr (.inl ⟨_, _, rfl⟩))
        | exact .inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))
        | (split at kind <;> simp_all)

theorem neutral_kind {n : Nat} {depth : Nat} {t : Tm Head n} {k : RigidKind} (neutral : Neutral S.roles t)
    (kind : rigidKind depth t = some k) : ∃ j, k = .local j := by
  cases k with
  | «local» j => exact ⟨j, rfl⟩
  | _ =>
      exfalso
      cases t with
      | head h => exact neutral.not_former.1 h rfl
      | pi A B => exact neutral.not_former.2.1 A B rfl
      | sigma A B => exact neutral.not_former.2.2.1 A B rfl
      | id A a b => exact neutral.not_former.2.2.2 A a b rfl
      | var i =>
          simp only [rigidKind] at kind
          split at kind <;> simp_all
      | app f a =>
          simp only [rigidKind] at kind
          split at kind
          · split at kind <;> simp_all
          · simp_all
      | _ => simp [rigidKind] at kind

/-- Matching weak-head forms of two rigid shapes: equal shapes, or two spines of locals. -/
theorem formsMatch_kind {n : Nat} {Γ : Ctx Head n} {depth : Nat} {l r : Tm Head n} {k k' : RigidKind}
    (matched : FormsMatch S.R S.roles Γ l r) (kl : rigidKind depth l = some k) (kr : rigidKind depth r = some k') :
    k = k' ∨ ∃ j j', k = .local j ∧ k' = .local j' := by
  rcases matched with ⟨_, _, rfl, rfl, _⟩ | ⟨_, _, _, _, rfl, rfl, _⟩ | ⟨_, _, _, _, rfl, rfl, _⟩ |
    ⟨_, _, _, _, _, _, rfl, rfl, _⟩ | ⟨_, _, _, rfl, rfl⟩ | ⟨neutralL, neutralR⟩
  · simp only [rigidKind, Option.some.injEq] at kl kr
    exact .inl (kl.symm.trans kr)
  · simp only [rigidKind, Option.some.injEq] at kl kr
    exact .inl (kl.symm.trans kr)
  · simp only [rigidKind, Option.some.injEq] at kl kr
    exact .inl (kl.symm.trans kr)
  · simp only [rigidKind, Option.some.injEq] at kl kr
    exact .inl (kl.symm.trans kr)
  · simp [rigidKind] at kl
  · obtain ⟨j, rfl⟩ := neutral_kind neutralL kl
    obtain ⟨j', rfl⟩ := neutral_kind neutralR kr
    exact .inr ⟨j, j', rfl, rfl⟩

section Refutation

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (complete : AlgorithmicComplete S.R S.roles)

include complete in
/-- Two spines of distinct variables are never equal at a base type. -/
theorem distinct_spines_not_equal {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {i j : Fin n}
    {as bs : List (Tm Head n)} {C : Tm Head n} (base : BaseType S C) (differ : i ≠ j) :
    ¬ Equal S.R Γ (appSpine (.var i) as) (appSpine (.var j) bs) C := by
  intro same
  obtain ⟨_, spines⟩ := terms_neutral_spines base (neutral_appSpine i as) (neutral_appSpine j bs) (complete formed same)
  exact differ (spines_heads (S := S) i j as bs spines)

/-- Reflexivity is not compared as a spine. -/
theorem refl_not_spineForm {n : Nat} {z : Tm Head n} (form : SpineForm S.roles (.refl z)) : False := by
  rcases form with neutral | ⟨k, _, args, _, same⟩
  · exact neutral.ne_refl rfl
  · rcases appSpine_const_cases k args with constant | ⟨_, _, application⟩
    · rw [constant] at same
      cases same
    · rw [application] at same
      cases same

include complete in
/-- Reflexivity is never equal to a neutral term at an identity type. -/
theorem refl_neutral_not_equal {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {C x y z r : Tm Head n}
    (neutral : Neutral S.roles r) : ¬ Equal S.R Γ (.refl z) r (.id C x y) := by
  intro same
  cases complete formed same with
  | terms typeRed _ leftRed rightRed inner =>
      have typeSame := WhRed.eq_of_whnf (S := S) (id_whnf S.shape _ _ _) typeRed.red
      have leftSame := WhRed.eq_of_whnf (S := S) (refl_whnf S.shape _) leftRed.red
      have rightSame := WhRed.eq_of_whnf (S := S) (neutral.whnf S.shape) rightRed.red
      subst typeSame
      subst leftSame
      subst rightSame
      cases inner with
      | refl => exact neutral.ne_refl rfl
      | spine _ form _ _ _ _ => exact refl_not_spineForm form

include complete in
/-- **Reflexivity is never equal to a spine of a variable** at an identity type. -/
theorem refl_spine_not_equal {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {C x y z : Tm Head n}
    {i : Fin n} {as : List (Tm Head n)} :
    ¬ Equal S.R Γ (.refl z) (appSpine (.var i) as) (.id C x y) :=
  refl_neutral_not_equal complete formed (neutral_appSpine (S := S) i as)

include facts complete in
/-- **A rigid clash under abstractions never holds.** -/
theorem clash_not_equal {depth n : Nat} {annotation left right : Tm Head n}
    (clash : ClashAt S.R depth annotation left right) :
    ∀ {Γ : Ctx Head n}, CtxFormed S.R Γ → TypedEquality.Typed S.R Γ left annotation →
      TypedEquality.Typed S.R Γ right annotation → ¬ Equal S.R Γ left right annotation := by
  induction clash with
  | @universal depth n u l r k k' hu kl kr differ =>
      intro Γ formed _ _ same
      have matched := facts.forms ⟨u, hu, same⟩ formed (rigidKind_form kl) (rigidKind_form kr)
      rcases formsMatch_kind matched kl kr with equalKinds | ⟨j, j', rfl, rfl⟩
      · exact differ equalKinds
      · obtain ⟨h, as, rfl, rfl, _⟩ := rigidKind_local kl
        obtain ⟨h', bs, rfl, rfl, _⟩ := rigidKind_local kr
        refine distinct_spines_not_equal complete formed (.inr (.inl ⟨u, rfl⟩)) ?_ same
        intro sameHead
        exact differ (by rw [sameHead])
  | locals base _ _ differ =>
      intro Γ formed _ _ same
      exact distinct_spines_not_equal complete formed (rigidBase_spec base) differ same
  | reflSpine _ =>
      intro Γ formed _ _ same
      exact refl_spine_not_equal complete formed same
  | spineRefl _ =>
      intro Γ formed _ _ same
      exact refl_spine_not_equal complete formed (.symm same)
  | bind _ ih =>
      intro Γ formed tl tr same
      obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
      exact ih (formed.snoc ⟨u, hu, tD⟩) (Typed.lam_inv facts tl formed) (Typed.lam_inv facts tr formed)
        (lam_equal_inv facts formed same)

end Refutation

/-! ## Deciding a clash -/

variable [∀ head, Decidable (S.R.isUniverse head)]

/-- A universe code. -/
def universeCode {n : Nat} : Tm Head n → Bool
  | .head u => decide (S.R.isUniverse u)
  | _ => false

/-- Two rigid shapes that differ. -/
def kindsDiffer {n : Nat} (depth : Nat) (left right : Tm Head n) : Bool :=
  match rigidKind depth left, rigidKind depth right with
  | some k, some k' => decide (k ≠ k')
  | _, _ => false

/-- Two spines of distinct locals. -/
def localsDiffer {n : Nat} (depth : Nat) (left right : Tm Head n) : Bool :=
  match spineOf left, spineOf right with
  | some (i, _), some (j, _) => decide (i ≠ j ∧ i.val < depth ∧ j.val < depth)
  | _, _ => false

/-- An identity-type code. -/
def identityCode {n : Nat} : Tm Head n → Bool
  | .id _ _ _ => true
  | _ => false

/-- Reflexivity against a spine of a local. -/
def reflAgainst {n : Nat} (depth : Nat) (left right : Tm Head n) : Bool :=
  match left, spineOf right with
  | .refl _, some (i, _) => decide (i.val < depth)
  | _, _ => false

theorem reflAgainst_spec {n : Nat} {depth : Nat} {left right : Tm Head n} (found : reflAgainst depth left right = true) :
    ∃ z i as, left = .refl z ∧ right = appSpine (.var i) as ∧ i.val < depth := by
  unfold reflAgainst at found
  split at found
  · rename_i z i as read
    exact ⟨z, i, as, rfl, spineOf_spec read, by simpa using found⟩
  · cases found

/-- The clash test at the bottom of the reading. -/
def clashBase {n : Nat} (depth : Nat) (C left right : Tm Head n) : Bool :=
  (universeCode (S := S) C && kindsDiffer depth left right) || (rigidBase depth C && localsDiffer depth left right) ||
    (identityCode C && (reflAgainst depth left right || reflAgainst depth right left))

/-- **The decision of a rigid clash under abstractions**, by the codes. -/
def clashAt : {n : Nat} → Nat → Tm Head n → Tm Head n → Tm Head n → Bool
  | _, depth, .pi _ T, .lam left, .lam right => clashAt (depth + 1) T left right
  | _, depth, C, left, right => clashBase (S := S) depth C left right

theorem clashBase_sound {n : Nat} {depth : Nat} {C left right : Tm Head n}
    (found : clashBase (S := S) depth C left right = true) : ClashAt S.R depth C left right := by
  unfold clashBase at found
  simp only [Bool.or_eq_true, Bool.and_eq_true] at found
  rcases found with (⟨universal, differ⟩ | ⟨base, differ⟩) | ⟨identity, against | against⟩
  rotate_left 2
  · cases C with
    | id C x y =>
        obtain ⟨z, i, as, rfl, rfl, small⟩ := reflAgainst_spec against
        exact .reflSpine small
    | _ => simp [identityCode] at identity
  · cases C with
    | id C x y =>
        obtain ⟨z, i, as, rfl, rfl, small⟩ := reflAgainst_spec against
        exact .spineRefl small
    | _ => simp [identityCode] at identity
  · cases C with
    | head u =>
        simp only [universeCode, decide_eq_true_eq] at universal
        unfold kindsDiffer at differ
        cases kl : rigidKind depth left with
        | none => rw [kl] at differ; cases differ
        | some k =>
            cases kr : rigidKind depth right with
            | none => rw [kl, kr] at differ; cases differ
            | some k' =>
                rw [kl, kr] at differ
                exact .universal universal kl kr (by simpa using differ)
    | _ => simp [universeCode] at universal
  · unfold localsDiffer at differ
    cases sl : spineOf left with
    | none => rw [sl] at differ; cases differ
    | some readL =>
        obtain ⟨i, as⟩ := readL
        cases sr : spineOf right with
        | none => rw [sl, sr] at differ; cases differ
        | some readR =>
            obtain ⟨j, bs⟩ := readR
            rw [sl, sr] at differ
            simp only [decide_eq_true_eq] at differ
            obtain ⟨distinct, si, sj⟩ := differ
            rw [spineOf_spec sl, spineOf_spec sr]
            exact .locals base si sj distinct

theorem clashAt_cases {n : Nat} {depth : Nat} {annotation left right : Tm Head n}
    (found : clashAt (S := S) depth annotation left right = true) :
    (∃ D T l r, annotation = .pi D T ∧ left = .lam l ∧ right = .lam r ∧ clashAt (S := S) (depth + 1) T l r = true) ∨
      clashBase (S := S) depth annotation left right = true := by
  cases annotation with
  | pi D T =>
      cases left with
      | lam l =>
          cases right with
          | lam r => exact .inl ⟨D, T, l, r, rfl, rfl, rfl, by simpa [clashAt] using found⟩
          | _ => exact .inr (by simpa [clashAt] using found)
      | _ => exact .inr (by simpa [clashAt] using found)
  | _ => exact .inr (by simpa [clashAt] using found)

theorem clashAt_sound : ∀ {n : Nat} (depth : Nat) (annotation left right : Tm Head n),
    clashAt (S := S) depth annotation left right = true → ClashAt S.R depth annotation left right
  | _, depth, .pi D T, left, right, found => by
      rcases clashAt_cases found with ⟨D', T', l, r, same, rfl, rfl, inner⟩ | base
      · injection same with _ sameD sameT
        subst sameD
        subst sameT
        exact .bind (clashAt_sound (depth + 1) T l r inner)
      · exact clashBase_sound base
  | _, depth, .var _, left, right, found | _, depth, .const _, left, right, found
  | _, depth, .head _, left, right, found | _, depth, .sigma _ _, left, right, found
  | _, depth, .id _ _ _, left, right, found | _, depth, .lam _, left, right, found
  | _, depth, .app _ _, left, right, found | _, depth, .pair _ _, left, right, found
  | _, depth, .fst _, left, right, found | _, depth, .snd _, left, right, found
  | _, depth, .refl _, left, right, found => by
      rcases clashAt_cases found with ⟨_, _, _, _, same, _⟩ | base
      · cases same
      · exact clashBase_sound base

/-! ## The clash rule -/

variable [DecidableEq Head]

/-- **A store equation whose sides clash under its abstractions**, both sides at one annotation code. -/
structure ClashShape {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Type where
  same : equation.2.1.code = equation.1.1.code
  clash : ClashAt S.R 0 equation.1.1.code equation.1.2.code equation.2.2.code

/-- Read a clash from the codes; no budget. -/
def clashShape {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Option (ClashShape equation) :=
  if same : equation.2.1.code = equation.1.1.code then
    if found : clashAt (S := S) 0 equation.1.1.code equation.1.2.code equation.2.2.code = true then
      some ⟨same, clashAt_sound _ _ _ _ found⟩
    else none
  else none

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

omit [∀ head, Decidable (S.R.isUniverse head)] [DecidableEq Head] in
include facts complete in
/-- **A clash has no solution at any later context.** -/
theorem ClashShape.refutes {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (shape : ClashShape equation)
    {Δ : Context S.R} (σ : Δ ⟶ Θ) : ¬ (frames S.levels).Solves σ equation := by
  intro solved
  rw [solves_raw] at solved
  have tLeft := equation.1.2.typed.substitute σ.typed
  have tRight := equation.2.2.typed.substitute σ.typed
  rw [shape.same] at tRight
  exact clash_not_equal facts complete
    (shape.clash.subst σ.substitution (fun _ _ _ small => absurd small (Nat.not_lt_zero _)) (Nat.zero_le _))
    Δ.formed tLeft tRight solved.2

/-- **The clash rule**: refute the store at the first equation whose sides clash under its abstractions. -/
def clashSearch {Θ : Context S.R} : (problem : EquationStore (TotalTerm Θ)) → Option (Found problem)
  | [] => none
  | equation :: rest =>
      match clashShape equation with
      | some shape => some (.refuted fun ⟨_, σ, solved⟩ =>
          shape.refutes facts complete σ (solved equation List.mem_cons_self))
      | none => (clashSearch rest).map (Found.keepLeft equation)

/-- The refutation of the clash rule on a prepared store, moved back to the store. -/
def clashOf {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (prepared : Update S.levels problem) :
    Option (PLift (¬ (frames S.levels).Solvable problem)) :=
  match clashSearch facts complete prepared.remaining with
  | some (.refuted absent) => some ⟨fun solvable => absent (prepared.solvable_iff.mp solvable)⟩
  | _ => none

end ContextualDependentFragmentDecisive
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
