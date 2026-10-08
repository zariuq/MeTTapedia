import Mettapedia.GSLT.Dedukti.Metatheory
import Mettapedia.GSLT.Dedukti.PureTypeSystem

/-!
# Weakening and substitution for typing modulo declared rules

The two structural lemmas of the typing judgment `HasType`, for every profile
and every theory whose definitions and declared types are closed.

* `HasType.weaken_at`: a variable may be inserted anywhere in the context;
  the entries in front of it, the term and the type are lifted over it.
  `HasType.weaken` is the case of the front of the context.
* `HasType.subst_at`: a variable may be replaced by a term of its type; the
  entries in front of it, the term and the type are substituted.
  `HasType.subst0` is the case of the front of the context: from
  `x : A ⊢ t : T` and `⊢ a : A`, `⊢ t[a] : T[a]`.

The conversion rule goes through because conversion is stable under lifting
and under substitution (`Conv.lift`, `Conv.subst`), with no condition on the
declared rules: an instance of a rule is lifted and substituted to an
instance.  Closedness of the definitions and of the declared types is used
for the constants only.

With them and injectivity of products under confluence, a beta contraction
at the root keeps the type (`HasType.beta_root`).  Preservation of types under
a step inside a term and under a declared rule is not derived here; it stays
the hypothesis `SubjectReduction` of `Typing`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0 Ctx ctxLookup)
open Mettapedia.GSLT.LanguageDef.LFProfile (Profile ProductRule)
open Mettapedia.GSLT.LanguageDef.LFContextualBetaEta (Context)

/-! ## More commutation -/

/-- A lift above a substituted variable commutes with the substitution. -/
theorem lift_subst_below (term : Term) :
    ∀ (amount cutoff target : Nat) (replacement : Term), target ≤ cutoff →
      lift amount cutoff (subst target replacement term) =
        subst target (lift amount cutoff replacement) (lift amount (cutoff + 1) term) := by
  induction term with
  | var index =>
      intro amount cutoff target replacement ordered
      by_cases same : index = target
      · have below : target < cutoff + 1 := by omega
        simp [lift, subst, same, below]
      · by_cases above : target < index
        · by_cases belowCutoff : index < cutoff + 1
          · have belowPred : index - 1 < cutoff := by omega
            simp [lift, subst, same, above, belowCutoff, belowPred]
          · have notBelowPred : ¬ index - 1 < cutoff := by omega
            have notSame : index + amount ≠ target := by omega
            have aboveShifted : target < index + amount := by omega
            simp only [lift, subst, same, above, belowCutoff, notBelowPred, notSame, aboveShifted,
              if_true, if_false]
            congr 1
            omega
        · have belowCutoff : index < cutoff + 1 := by omega
          have belowCutoff' : index < cutoff := by omega
          simp [lift, subst, same, above, belowCutoff, belowCutoff']
  | srt sort => intro amount cutoff target replacement _; rfl
  | con name => intro amount cutoff target replacement _; rfl
  | pi domain body ihDomain ihBody =>
      intro amount cutoff target replacement ordered
      have under := ihBody amount (cutoff + 1) (target + 1) (lift 1 0 replacement)
        (Nat.succ_le_succ ordered)
      have commute : lift amount (cutoff + 1) (lift 1 0 replacement) =
          lift 1 0 (lift amount cutoff replacement) :=
        (lift_lift replacement 1 amount 0 cutoff (Nat.zero_le _)).symm
      rw [commute] at under
      simp [lift, subst, ihDomain amount cutoff target replacement ordered, under]
  | lam domain body ihDomain ihBody =>
      intro amount cutoff target replacement ordered
      have under := ihBody amount (cutoff + 1) (target + 1) (lift 1 0 replacement)
        (Nat.succ_le_succ ordered)
      have commute : lift amount (cutoff + 1) (lift 1 0 replacement) =
          lift 1 0 (lift amount cutoff replacement) :=
        (lift_lift replacement 1 amount 0 cutoff (Nat.zero_le _)).symm
      rw [commute] at under
      simp [lift, subst, ihDomain amount cutoff target replacement ordered, under]
  | app function argument ihFunction ihArgument =>
      intro amount cutoff target replacement ordered
      simp [lift, subst, ihFunction amount cutoff target replacement ordered,
        ihArgument amount cutoff target replacement ordered]

/-- Lifting commutes with a beta contraction. -/
theorem lift_subst0 (amount cutoff : Nat) (argument body : Term) :
    lift amount cutoff (subst0 argument body) =
      subst0 (lift amount cutoff argument) (lift amount (cutoff + 1) body) :=
  lift_subst_below body amount cutoff 0 argument (Nat.zero_le _)

/-- Lifting commutes with the instantiation of pattern variables. -/
theorem lift_instantiate (assignment : Nat → Term) (pattern : Term) :
    ∀ (depth amount cutoff : Nat),
      lift amount (cutoff + depth) (instantiate assignment depth pattern) =
        instantiate (fun index => lift amount cutoff (assignment index)) depth pattern := by
  induction pattern with
  | var index =>
      intro depth amount cutoff
      by_cases below : index < depth
      · have belowCutoff : index < cutoff + depth := by omega
        simp [instantiate, lift, below, belowCutoff]
      · simp only [instantiate, below, if_false]
        exact (lift_lift (assignment (index - depth)) depth amount 0 cutoff (Nat.zero_le _)).symm
  | srt sort => intro depth amount cutoff; rfl
  | con name => intro depth amount cutoff; rfl
  | pi domain body ihDomain ihBody =>
      intro depth amount cutoff
      have under := ihBody (depth + 1) amount cutoff
      have shifted : cutoff + (depth + 1) = cutoff + depth + 1 := by omega
      rw [shifted] at under
      simp [instantiate, lift, ihDomain depth amount cutoff, under]
  | lam domain body ihDomain ihBody =>
      intro depth amount cutoff
      have under := ihBody (depth + 1) amount cutoff
      have shifted : cutoff + (depth + 1) = cutoff + depth + 1 := by omega
      rw [shifted] at under
      simp [instantiate, lift, ihDomain depth amount cutoff, under]
  | app function argument ihFunction ihArgument =>
      intro depth amount cutoff
      simp [instantiate, lift, ihFunction depth amount cutoff, ihArgument depth amount cutoff]

theorem lift_inst (assignment : Nat → Term) (pattern : Term) (amount cutoff : Nat) :
    lift amount cutoff (inst assignment pattern) =
      inst (fun index => lift amount cutoff (assignment index)) pattern :=
  lift_instantiate assignment pattern 0 amount cutoff

/-- A lift whose cutoff lies within an earlier lift merges with it. -/
theorem lift_lift_merge (term : Term) :
    ∀ (outer inner cutoff base : Nat), cutoff ≤ inner →
      lift outer (cutoff + base) (lift inner base term) = lift (outer + inner) base term := by
  induction term with
  | var index =>
      intro outer inner cutoff base ordered
      by_cases below : index < base
      · have belowCutoff : index < cutoff + base := by omega
        simp [lift, below, belowCutoff]
      · have notBelow : ¬ index + inner < cutoff + base := by omega
        simp only [lift, below, notBelow, if_false]
        congr 1
        omega
  | srt sort => intro outer inner cutoff base _; rfl
  | con name => intro outer inner cutoff base _; rfl
  | pi domain body ihDomain ihBody =>
      intro outer inner cutoff base ordered
      have under := ihBody outer inner cutoff (base + 1) ordered
      have shifted : cutoff + (base + 1) = cutoff + base + 1 := by omega
      rw [shifted] at under
      simp [lift, ihDomain outer inner cutoff base ordered, under]
  | lam domain body ihDomain ihBody =>
      intro outer inner cutoff base ordered
      have under := ihBody outer inner cutoff (base + 1) ordered
      have shifted : cutoff + (base + 1) = cutoff + base + 1 := by omega
      rw [shifted] at under
      simp [lift, ihDomain outer inner cutoff base ordered, under]
  | app function argument ihFunction ihArgument =>
      intro outer inner cutoff base ordered
      simp [lift, ihFunction outer inner cutoff base ordered, ihArgument outer inner cutoff base ordered]

/-- Substituting for a variable that a lift has skipped undoes one step of the
lift. -/
theorem subst_lift_above (term : Term) :
    ∀ (target amount base : Nat) (replacement : Term), target < amount →
      subst (target + base) replacement (lift amount base term) = lift (amount - 1) base term := by
  induction term with
  | var index =>
      intro target amount base replacement ordered
      by_cases below : index < base
      · have notSame : index ≠ target + base := by omega
        have notAbove : ¬ target + base < index := by omega
        simp [lift, subst, below, notSame, notAbove]
      · have notSame : index + amount ≠ target + base := by omega
        have above : target + base < index + amount := by omega
        simp only [lift, subst, below, notSame, above, if_true, if_false]
        congr 1
        omega
  | srt sort => intro target amount base replacement _; rfl
  | con name => intro target amount base replacement _; rfl
  | pi domain body ihDomain ihBody =>
      intro target amount base replacement ordered
      have under := ihBody target amount (base + 1) (lift 1 0 replacement) ordered
      have shifted : target + (base + 1) = target + base + 1 := by omega
      rw [shifted] at under
      simp [lift, subst, ihDomain target amount base replacement ordered, under]
  | lam domain body ihDomain ihBody =>
      intro target amount base replacement ordered
      have under := ihBody target amount (base + 1) (lift 1 0 replacement) ordered
      have shifted : target + (base + 1) = target + base + 1 := by omega
      rw [shifted] at under
      simp [lift, subst, ihDomain target amount base replacement ordered, under]
  | app function argument ihFunction ihArgument =>
      intro target amount base replacement ordered
      simp [lift, subst, ihFunction target amount base replacement ordered,
        ihArgument target amount base replacement ordered]

/-! ## Steps and conversion under lifting -/

variable {theory : Theory}

theorem RootStep.lift (closed : theory.ClosedBodies) {source target : Term}
    (step : RootStep theory source target) (amount cutoff : Nat) :
    RootStep theory (LFTyping.lift amount cutoff source) (LFTyping.lift amount cutoff target) := by
  cases step with
  | beta domain body argument =>
      rw [lift_subst0]
      exact .beta _ _ _
  | delta defined =>
      rw [(closed _ _ defined).lift]
      exact .delta defined
  | rule assignment member =>
      rw [lift_inst, lift_inst]
      exact .rule _ member

/-- **A step is stable under lifting.** -/
theorem Step.lift (closed : theory.ClosedBodies) {source target : Term}
    (step : Step theory source target) (amount : Nat) :
    ∀ cutoff : Nat,
      Step theory (LFTyping.lift amount cutoff source) (LFTyping.lift amount cutoff target) := by
  cases step with
  | @inContext context redex contractum root =>
      induction context with
      | hole => intro cutoff; exact Step.root (root.lift closed amount cutoff)
      | piDomain rest body ih => intro cutoff; exact (ih cutoff).plug (.piDomain .hole _)
      | piBody domain rest ih => intro cutoff; exact (ih (cutoff + 1)).plug (.piBody _ .hole)
      | lamDomain rest body ih => intro cutoff; exact (ih cutoff).plug (.lamDomain .hole _)
      | lamBody domain rest ih => intro cutoff; exact (ih (cutoff + 1)).plug (.lamBody _ .hole)
      | appFunction rest argument ih => intro cutoff; exact (ih cutoff).plug (.appFunction .hole _)
      | appArgument function rest ih => intro cutoff; exact (ih cutoff).plug (.appArgument _ .hole)

/-- **Conversion is stable under lifting.** -/
theorem Conv.lift (closed : theory.ClosedBodies) {source target : Term}
    (convertible : Conv theory source target) (amount cutoff : Nat) :
    Conv theory (LFTyping.lift amount cutoff source) (LFTyping.lift amount cutoff target) := by
  induction convertible with
  | rel _ _ step => exact .rel _ _ (step.lift closed amount cutoff)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact .trans _ _ _ ihFirst ihSecond

/-! ## Weakening -/

/-- The declared types of a theory are closed terms. -/
def Theory.ClosedTypes (theory : Theory) : Prop :=
  ∀ name type, theory.constType name = some type → Closed type

/-- Lift the entries in front of an inserted variable: each over the entries
behind it. -/
def liftCtx : Ctx → Ctx
  | [] => []
  | head :: tail => lift 1 tail.length head :: liftCtx tail

@[simp] theorem liftCtx_length (context : Ctx) : (liftCtx context).length = context.length := by
  induction context with
  | nil => rfl
  | cons head tail ih => simp [liftCtx, ih]

theorem liftCtx_getElem? (context : Ctx) :
    ∀ index : Nat, (liftCtx context)[index]? =
      (context[index]?).map (lift 1 (context.length - 1 - index)) := by
  induction context with
  | nil => intro index; rfl
  | cons head tail ih =>
      intro index
      cases index with
      | zero => simp [liftCtx]
      | succ index =>
          have same : tail.length - (index + 1) = tail.length - 1 - index := by omega
          simp [liftCtx, ih, same]

/-- The lookup of a variable after an insertion. -/
theorem ctxLookup_insert (front back : Ctx) (inserted : Term) (index : Nat) :
    ctxLookup (liftCtx front ++ inserted :: back) (if index < front.length then index else index + 1) =
      (ctxLookup (front ++ back) index).map (lift 1 front.length) := by
  rw [ctxLookup_eq_getElem?, ctxLookup_eq_getElem?]
  by_cases below : index < front.length
  · have belowLifted : index < (liftCtx front).length := by simpa using below
    simp only [below, if_true]
    rw [List.getElem?_append_left belowLifted, List.getElem?_append_left below, liftCtx_getElem?]
    cases front[index]? with
    | none => rfl
    | some value =>
        simp only [Option.map_some]
        have commute := lift_lift value (index + 1) 1 0 (front.length - 1 - index) (Nat.zero_le _)
        have total : front.length - 1 - index + (index + 1) = front.length := by omega
        rw [total] at commute
        rw [commute]
  · have above : front.length ≤ index := by omega
    have aboveLifted : (liftCtx front).length ≤ index + 1 := by simp; omega
    simp only [below, if_false]
    rw [List.getElem?_append_right aboveLifted, List.getElem?_append_right above]
    have position : index + 1 - (liftCtx front).length = index - front.length + 1 := by simp; omega
    rw [position, List.getElem?_cons_succ]
    cases back[index - front.length]? with
    | none => rfl
    | some value =>
        simp only [Option.map_some]
        have merge := lift_lift_merge value 1 (index + 1) front.length 0 (by omega)
        rw [Nat.add_zero] at merge
        rw [merge]
        congr 2
        omega

/-- **Weakening**: a variable inserted anywhere in the context. -/
theorem HasType.weaken_at {profile : Profile} (closedBodies : theory.ClosedBodies)
    (closedTypes : theory.ClosedTypes) (back : Ctx) (inserted : Term) {context : Ctx}
    {term type : Term} (typed : HasType profile theory context term type) :
    ∀ front : Ctx, context = front ++ back →
      HasType profile theory (liftCtx front ++ inserted :: back)
        (lift 1 front.length term) (lift 1 front.length type) := by
  induction typed with
  | sort axiomHolds => intro front _; exact .sort axiomHolds
  | @var context index type found =>
      intro front same
      subst same
      have lookup := ctxLookup_insert front back inserted index
      rw [found] at lookup
      exact .var lookup
  | @con context name type declared =>
      intro front _
      have unchanged : lift 1 front.length type = type := (closedTypes _ _ declared).lift _ _
      rw [unchanged]
      exact .con declared
  | pi _ _ rule ihDomain ihBody =>
      intro front same
      exact .pi (ihDomain front same) (ihBody (_ :: front) (by rw [same]; rfl)) rule
  | lam _ _ rule _ ihDomain ihBodyType ihBody =>
      intro front same
      exact .lam (ihDomain front same) (ihBodyType (_ :: front) (by rw [same]; rfl)) rule
        (ihBody (_ :: front) (by rw [same]; rfl))
  | app _ _ ihFunction ihArgument =>
      intro front same
      rw [lift_subst0]
      exact .app (ihFunction front same) (ihArgument front same)
  | conv _ convertible _ ihTerm ihTarget =>
      intro front same
      exact .conv (ihTerm front same) (convertible.lift closedBodies 1 front.length)
        (ihTarget front same)

/-- **Weakening at the front of the context.** -/
theorem HasType.weaken {profile : Profile} (closedBodies : theory.ClosedBodies)
    (closedTypes : theory.ClosedTypes) {context : Ctx} {term type : Term} (inserted : Term)
    (typed : HasType profile theory context term type) :
    HasType profile theory (inserted :: context) (lift 1 0 term) (lift 1 0 type) :=
  typed.weaken_at closedBodies closedTypes context inserted [] rfl

/-- Weakening by any number of variables at the front. -/
theorem HasType.weaken_many {profile : Profile} (closedBodies : theory.ClosedBodies)
    (closedTypes : theory.ClosedTypes) {context : Ctx} {term type : Term}
    (typed : HasType profile theory context term type) :
    ∀ front : Ctx, HasType profile theory (front ++ context)
      (lift front.length 0 term) (lift front.length 0 type) := by
  intro front
  induction front with
  | nil => simpa [lift_zero] using typed
  | cons head tail ih =>
      have step := ih.weaken closedBodies closedTypes head
      rw [lift_lift_same, lift_lift_same] at step
      have length : 1 + tail.length = (head :: tail).length := by simp [Nat.add_comm]
      rw [length] at step
      exact step

/-! ## Substitution -/

/-- Substitute for a variable in the entries in front of it: each under the
entries behind it. -/
def substCtx (argument : Term) : Ctx → Ctx
  | [] => []
  | head :: tail => subst tail.length (lift tail.length 0 argument) head :: substCtx argument tail

@[simp] theorem substCtx_length (argument : Term) (context : Ctx) :
    (substCtx argument context).length = context.length := by
  induction context with
  | nil => rfl
  | cons head tail ih => simp [substCtx, ih]

theorem substCtx_getElem? (argument : Term) (context : Ctx) :
    ∀ index : Nat, (substCtx argument context)[index]? =
      (context[index]?).map (subst (context.length - 1 - index)
        (lift (context.length - 1 - index) 0 argument)) := by
  induction context with
  | nil => intro index; rfl
  | cons head tail ih =>
      intro index
      cases index with
      | zero => simp [substCtx]
      | succ index =>
          have same : tail.length - (index + 1) = tail.length - 1 - index := by omega
          simp [substCtx, ih, same]

/-- The lookup of a variable in front of the substituted one. -/
theorem ctxLookup_subst_below (front back : Ctx) (domain argument : Term) {index : Nat}
    (below : index < front.length) :
    ctxLookup (substCtx argument front ++ back) index =
      (ctxLookup (front ++ domain :: back) index).map
        (subst front.length (lift front.length 0 argument)) := by
  rw [ctxLookup_eq_getElem?, ctxLookup_eq_getElem?]
  have belowSubst : index < (substCtx argument front).length := by simpa using below
  rw [List.getElem?_append_left belowSubst, List.getElem?_append_left below, substCtx_getElem?]
  cases front[index]? with
  | none => rfl
  | some value =>
      simp only [Option.map_some]
      have commute := lift_subst value (index + 1) 0 (front.length - 1 - index)
        (lift (front.length - 1 - index) 0 argument) (Nat.zero_le _)
      have total : front.length - 1 - index + (index + 1) = front.length := by omega
      have merged : lift (index + 1) 0 (lift (front.length - 1 - index) 0 argument) =
          lift front.length 0 argument := by
        rw [lift_lift_same]
        congr 1
        omega
      rw [total, merged] at commute
      rw [commute]

/-- The lookup of a variable behind the substituted one. -/
theorem ctxLookup_subst_above (front back : Ctx) (domain argument : Term) {index : Nat}
    (above : front.length < index) :
    ctxLookup (substCtx argument front ++ back) (index - 1) =
      (ctxLookup (front ++ domain :: back) index).map
        (subst front.length (lift front.length 0 argument)) := by
  rw [ctxLookup_eq_getElem?, ctxLookup_eq_getElem?]
  have aboveSubst : (substCtx argument front).length ≤ index - 1 := by simp; omega
  have aboveFront : front.length ≤ index := by omega
  rw [List.getElem?_append_right aboveSubst, List.getElem?_append_right aboveFront]
  have position : index - front.length = index - 1 - (substCtx argument front).length + 1 := by
    simp
    omega
  rw [position, List.getElem?_cons_succ]
  cases back[index - 1 - (substCtx argument front).length]? with
  | none => rfl
  | some value =>
      simp only [Option.map_some]
      have cancel := subst_lift_above value front.length (index + 1) 0
        (lift front.length 0 argument) (by omega)
      rw [Nat.add_zero] at cancel
      rw [cancel]
      congr 2
      omega

/-- The lookup of the substituted variable. -/
theorem ctxLookup_subst_same (front back : Ctx) (domain : Term) :
    ctxLookup (front ++ domain :: back) front.length = some (lift (front.length + 1) 0 domain) := by
  rw [ctxLookup_eq_getElem?, List.getElem?_append_right (Nat.le_refl _)]
  simp

/-- **The substitution lemma**: a variable anywhere in the context is replaced
by a term of its type. -/
theorem HasType.subst_at {profile : Profile} (closedBodies : theory.ClosedBodies)
    (closedTypes : theory.ClosedTypes) (back : Ctx) {domain argument : Term}
    (argumentTyped : HasType profile theory back argument domain) {context : Ctx}
    {term type : Term} (typed : HasType profile theory context term type) :
    ∀ front : Ctx, context = front ++ domain :: back →
      HasType profile theory (substCtx argument front ++ back)
        (subst front.length (lift front.length 0 argument) term)
        (subst front.length (lift front.length 0 argument) type) := by
  induction typed with
  | sort axiomHolds => intro front _; exact .sort axiomHolds
  | @var context index type found =>
      intro front same
      subst same
      by_cases below : index < front.length
      · have notSame : index ≠ front.length := by omega
        have notAbove : ¬ front.length < index := by omega
        have lookup := ctxLookup_subst_below front back domain argument below
        rw [found] at lookup
        simp only [LFTyping.subst, notSame, notAbove, if_false]
        exact .var lookup
      · by_cases isSame : index = front.length
        · subst isSame
          have declared := ctxLookup_subst_same front back domain
          have typeSame : type = lift (front.length + 1) 0 domain :=
            Option.some.inj (found.symm.trans declared)
          have cancel := subst_lift_above domain front.length (front.length + 1) 0
            (lift front.length 0 argument) (Nat.lt_succ_self _)
          rw [Nat.add_zero] at cancel
          have weakened := argumentTyped.weaken_many closedBodies closedTypes
            (substCtx argument front)
          rw [substCtx_length] at weakened
          simp only [LFTyping.subst, if_true]
          rw [typeSame, cancel]
          exact weakened
        · have above : front.length < index := by omega
          have lookup := ctxLookup_subst_above front back domain argument above
          rw [found] at lookup
          simp only [LFTyping.subst, isSame, above, if_true, if_false]
          exact .var lookup
  | @con context name type declared =>
      intro front _
      have unchanged : subst front.length (lift front.length 0 argument) type = type :=
        (closedTypes _ _ declared).subst _ _
      rw [unchanged]
      exact .con declared
  | pi _ _ rule ihDomain ihBody =>
      intro front same
      have key : lift 1 0 (lift front.length 0 argument) = lift (front.length + 1) 0 argument := by
        rw [lift_lift_same, Nat.add_comm]
      simp only [LFTyping.subst, key]
      exact .pi (ihDomain front same) (ihBody (_ :: front) (by rw [same]; rfl)) rule
  | lam _ _ rule _ ihDomain ihBodyType ihBody =>
      intro front same
      have key : lift 1 0 (lift front.length 0 argument) = lift (front.length + 1) 0 argument := by
        rw [lift_lift_same, Nat.add_comm]
      simp only [LFTyping.subst, key]
      exact .lam (ihDomain front same) (ihBodyType (_ :: front) (by rw [same]; rfl)) rule
        (ihBody (_ :: front) (by rw [same]; rfl))
  | app _ _ ihFunction ihArgument =>
      intro front same
      rw [subst_subst0]
      exact .app (ihFunction front same) (ihArgument front same)
  | conv _ convertible _ ihTerm ihTarget =>
      intro front same
      exact .conv (ihTerm front same) (convertible.subst closedBodies _ _) (ihTarget front same)

/-- **Substitution at the front of the context**: from `x : A ⊢ t : T` and
`⊢ a : A`, `⊢ t[a] : T[a]`. -/
theorem HasType.subst0 {profile : Profile} (closedBodies : theory.ClosedBodies)
    (closedTypes : theory.ClosedTypes) {context : Ctx} {domain argument term type : Term}
    (typed : HasType profile theory (domain :: context) term type)
    (argumentTyped : HasType profile theory context argument domain) :
    HasType profile theory context (LFTyping.subst0 argument term) (LFTyping.subst0 argument type) := by
  have general := HasType.subst_at closedBodies closedTypes context argumentTyped typed [] rfl
  simpa [substCtx, lift_zero, LFTyping.subst0] using general

/-! ## A beta contraction at the root keeps the type -/

/-- **A beta contraction at the root keeps the type**, for a type that is
formed.  Confluence is used once, to pass from the two types of the
abstraction to their domains and codomains; the substitution lemma does the
rest.  Preservation under a step inside a term, and under a declared rule, is
not derived here. -/
theorem HasType.beta_root {profile : Profile}
    (confluent : Mettapedia.Logic.Relation.Confluent (Step theory)) (headed : theory.Headed)
    (closedBodies : theory.ClosedBodies) (closedTypes : theory.ClosedTypes) {context : Ctx}
    {annotation body argument type : Term} {sort : Srt}
    (typed : HasType profile theory context (.app (.lam annotation body) argument) type)
    (formed : HasType profile theory context type (.srt sort)) :
    HasType profile theory context (LFTyping.subst0 argument body) type := by
  obtain ⟨domain, codomain, functionTyped, argumentTyped, resultConv⟩ := typed.app_inv
  obtain ⟨bodyType, domainSort, _, _, annotationTyped, _, _, bodyTyped, productConv⟩ :=
    functionTyped.lam_inv
  obtain ⟨domains, codomains⟩ := Conv.pi_injective confluent headed productConv
  have argumentAtAnnotation : HasType profile theory context argument annotation :=
    .conv argumentTyped (.symm _ _ domains) annotationTyped
  have substituted := HasType.subst0 closedBodies closedTypes bodyTyped argumentAtAnnotation
  exact .conv substituted
    (.trans _ _ _ (codomains.subst closedBodies 0 argument) resultConv) formed

#print axioms lift_subst_below
#print axioms lift_instantiate
#print axioms subst_lift_above
#print axioms Conv.lift
#print axioms HasType.weaken_at
#print axioms HasType.weaken_many
#print axioms HasType.subst_at
#print axioms HasType.subst0
#print axioms HasType.beta_root

end Mettapedia.GSLT.Dedukti
