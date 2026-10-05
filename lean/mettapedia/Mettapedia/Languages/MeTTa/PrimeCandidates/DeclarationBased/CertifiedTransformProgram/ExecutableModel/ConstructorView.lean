import Mettapedia.GSLT.Logic.PrivilegedView
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueLists

/-!
# The canonical head: which branch a match takes

A match by constructor on a scrutinee reads one thing of it: which constructor it reaches. That
reading is the **canonical head**. As a view of terms it keeps which branch and forgets the fields
and the timing: a redex and the constructor form it reduces to have one canonical head, and so do
two forms of one constructor with different fields.

## At a declared datatype

Fix a simple datatype `d` admissible over the object package and the weak-head steps of its
package (`dataHead`).

* A term **shows** the constructor at position `i` when it is that constructor applied to as
  many terms as the constructor has fields (`ShowsCtor`). It then takes no step
  (`ShowsCtor.normal`) and shows no other constructor (`ShowsCtor.unique`), the names of the
  constructors being distinct.
* A term **has the head** `i` when its weak-head steps reach a term that shows the constructor at
  `i` (`HeadAt`). It has at most one head (`HeadAt.unique`), by determinism of the package's
  weak-head steps: two reductions of one term to normal forms end at one form.
* **Invariance.** A step, and so a reduction, keeps the head (`headAt_step`, `headAt_red`). This
  uses determinism, not confluence: the step of a term is the first step of its reduction to a
  constructor form, unless the term is that form, which takes no step.
* **The canonical head.** Canonicity (`data_canonical`) gives every closed term typed at the
  datatype a head, and it is unique (`existsUnique_headAt`). The canonical head
  (`canonicalHead`) is the function from these terms (`ClosedAt`) to the positions of the
  constructors that picks it (`canonicalHead_eq_iff`), and it is invariant under reduction
  (`canonicalHead_red`). The package's steps are a relation, with no step function, so the
  function is taken by description from the unique existence and uses choice; the statements
  about heads do not.
* **The one-shot decision.** The recursor at a scrutinee with the head `i` reduces, through the
  scrutinee's own reduction, to the recursor at the scrutinee's constructor form, whose only step
  is to the branch of `i`: the method of that constructor applied to the fields and to the
  recursor at each recursive field (`recBranch`, `rec_ctor_step`, `rec_selects`). At a closed
  typed scrutinee this is the branch of its canonical head (`rec_selects_canonical`).
* **Negative: the boundary.** A term whose erasure is neutral has no head
  (`not_headAt_of_neutral`): a variable (`not_headAt_var`), or the recursor at a variable, which
  takes no step (`rec_var_stuck`). A match there has no branch to take and stays a residual.
* **Distinct constructors.** A constructor spine typed at the datatype applies its constructor
  to as many terms as it has fields (`dataCtorSpine_saturated`). So two closed applications of
  different constructors, with any arguments, are never derivably equal at the datatype
  (`ctor_not_equal_ctor`): the reading sends them to constructor elements with different tags.
  Equal applications of one constructor have arguments with equal readings
  (`ctor_equal_ctor_reads`).

Examples at the lists: positive, `nil` and `cons 1 nil` show their constructors at the positions
`0` and `1` (`lists_heads`); negative, over a list variable `x`, neither `x` nor `append x nil`
has a head (`listVar_no_head`), and no closed `nil ≡ cons a l` is derivable
(`nil_not_equal_cons`). The binary trees of numbers give the examples of canonical heads in their
own module.

## For a step function

The first part of the module states the same reading for a deterministic step function
`step : A → A` with a head reading `head : A → Option K`, the constructor a point shows now, if
any. The package's steps are a relation, so this part is not instantiated at the package; it
relates the reading to the views of `Mettapedia.GSLT.Logic.PrivilegedView`, for the evaluation
`head`.

**The setting.** The dynamics is **settled** (`Settled`): a point that shows a constructor is
fixed by the step. The **bubble** is the set of points that show a constructor after finitely
many steps (`Reaches`, `Bubble`); with settled dynamics it is closed under the step
(`Reaches.next`, `Bubble.next`). The canonical head of a point of the bubble is the first
constructor it shows, found by a bounded search (`Nat.find`), with no choice.

* The head reading along the run is eventually constant at the canonical head
  (`behaviour_eventually`, `behaviour_eventually'`), and a constructor shown at any time is the
  canonical head (`canonicalHead_eq_of_head`).
* It is invariant under the step (`canonicalHead_step`, `canonicalHead_iterate`), so it is a
  stable view (`stable_canonicalHead`).
* Two points have one canonical head exactly when their head readings agree from some time on
  (`canonicalHead_eq_iff`): it is the behaviour of `head` up to finite time.

**Relation to the views of `PrivilegedView`, for the evaluation `head`.** The behaviour of `head`
(the stream of heads along the run) is the coarsest stable view that keeps `head`. It determines
the canonical head (`factors_behaviour_canonicalHead`, and without choice
`constantOnFibers_behaviour_canonicalHead`); hence, by `factors_behaviour`, so does every stable
view that keeps `head` (`factors_canonicalHead_of_stable`, `commonCoarsening_canonicalHead`). The
canonical head does not keep `head` (`not_factors_canonicalHead_head`): a point of the bubble that
does not yet show its constructor has the canonical head of the constructor form it reaches and
another head now. So it is a stable view strictly coarser than the behaviour, not the coarsest
view that keeps `head`.

**Negative.** At a point that shows no constructor and takes no step the head reading is
constantly empty (`behaviour_stuck`) and the point is outside the bubble (`not_reaches_stuck`).

**Examples** on a four-state system (`Toy`): a redex that steps to the constructor `yes`, the
constructors `yes` and `no`, and a stuck point. Positive: the redex is in the bubble with the
canonical head of `yes` (`toy_canonicalHead_redex`), its head reading is eventually that
constructor (`toy_behaviour_redex`), and `yes` and `no` have different canonical heads
(`toy_canonicalHead_yes_ne_no`). Negative: the stuck point's head reading is constantly empty and
it is outside the bubble (`toy_stuck`); the head readings separate the redex from `yes`
(`toy_behaviour_redex_ne_yes`) while the canonical head identifies them, so it does not keep the
head now (`toy_not_factors_head`).

**The three faces.** This adds to the operational face: which constructor a computation reaches,
and what a match does with it. The intensional face enters through typing, which makes closed
terms reach a constructor; the extensional face separates the constructors in the domain reading
(`ctor_not_equal_ctor`, with `nil_not_equal_cons` and `leaf_not_equal_node` as instances).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.PrivilegedView

open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.ViewPluralism
open Mettapedia.Coalgebra.StreamFinality

universe u v w

/-! ## Settled dynamics and the bubble -/

section Settling

variable {A : Type u} {K : Type w}

/-- The dynamics is **settled** for the head evaluation: a point that shows a constructor is
fixed by the step. -/
def Settled (step : A → A) (head : A → Option K) : Prop :=
  ∀ a k, head a = some k → step a = a

/-- A point **reaches** a constructor when it shows one after finitely many steps. -/
def Reaches (step : A → A) (head : A → Option K) (a : A) : Prop :=
  ∃ n, (head (step^[n] a)).isSome = true

/-- **The bubble**: the points that reach a constructor. -/
abbrev Bubble (step : A → A) (head : A → Option K) : Type u :=
  {a : A // Reaches step head a}

variable {step : A → A} {head : A → Option K}

/-- A point that shows a constructor stays where it is under settled dynamics. -/
theorem Settled.iterate (settled : Settled step head) {b : A} {k : K} (shows : head b = some k) :
    ∀ m, step^[m] b = b
  | 0 => rfl
  | m + 1 => by
      rw [Function.iterate_succ_apply, settled b k shows]
      exact Settled.iterate settled shows m

/-- Under settled dynamics, the head after a constructor shows is that constructor. -/
theorem Settled.head_iterate (settled : Settled step head) {a : A} {n : Nat} {k : K}
    (shows : head (step^[n] a) = some k) {m : Nat} (later : n ≤ m) :
    head (step^[m] a) = some k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le later
  rw [Nat.add_comm, Function.iterate_add_apply, settled.iterate shows d, shows]

/-- **The bubble is closed under settled dynamics.** -/
theorem Reaches.next (settled : Settled step head) {a : A} (reaches : Reaches step head a) :
    Reaches step head (step a) := by
  obtain ⟨n, shows⟩ := reaches
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 shows
  refine ⟨n, ?_⟩
  rw [← Function.iterate_succ_apply, settled.head_iterate hk (Nat.le_succ n)]
  rfl

/-- The step of the bubble. -/
def Bubble.next (settled : Settled step head) (a : Bubble step head) : Bubble step head :=
  ⟨step a.1, a.2.next settled⟩

theorem Bubble.iterate_val (settled : Settled step head) (a : Bubble step head) :
    ∀ n, ((Bubble.next settled)^[n] a).1 = step^[n] a.1
  | 0 => rfl
  | n + 1 => by
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        Bubble.iterate_val settled (Bubble.next settled a) n]
      rfl

/-- The behaviour of a point of the bubble is its behaviour in the subject. -/
theorem behaviour_bubble (settled : Settled step head) (a : Bubble step head) :
    behaviour (Bubble.next settled) (fun b => head b.1) a = behaviour step head a.1 := by
  funext n
  rw [behaviour_apply, behaviour_apply, Bubble.iterate_val]

/-! ## The canonical head -/

/-- **The canonical head**: the first constructor a point of the bubble shows. -/
def canonicalHead (a : Bubble step head) : K :=
  (head (step^[Nat.find a.2] a.1)).get (Nat.find_spec a.2)

/-- The first constructor is shown at the first time a constructor shows. -/
theorem head_find (a : Bubble step head) :
    head (step^[Nat.find a.2] a.1) = some (canonicalHead a) :=
  (Option.some_get _).symm

/-- **The behaviour is eventually constant at the canonical head.** -/
theorem behaviour_eventually (settled : Settled step head) (a : Bubble step head) :
    ∀ n, Nat.find a.2 ≤ n → behaviour step head a.1 n = some (canonicalHead a) :=
  fun _ later => by
    rw [behaviour_apply]
    exact settled.head_iterate (head_find a) later

theorem behaviour_eventually' (settled : Settled step head) (a : Bubble step head) :
    ∃ N, ∀ n, N ≤ n → behaviour step head a.1 n = some (canonicalHead a) :=
  ⟨Nat.find a.2, behaviour_eventually settled a⟩

/-- **A constructor shown at any time is the canonical head.** -/
theorem canonicalHead_eq_of_head (settled : Settled step head) (a : Bubble step head) {n : Nat}
    {k : K}
    (shows : head (step^[n] a.1) = some k) : canonicalHead a = k := by
  have least : Nat.find a.2 ≤ n := Nat.find_min' a.2 (by rw [shows]; rfl)
  have e := behaviour_eventually settled a n least
  rw [behaviour_apply, shows] at e
  exact (Option.some.inj e).symm

/-- **The canonical head is invariant under the step.** -/
theorem canonicalHead_step (settled : Settled step head) (a : Bubble step head) :
    canonicalHead (Bubble.next settled a) = canonicalHead a := by
  refine canonicalHead_eq_of_head settled _ (n := Nat.find a.2) ?_
  show head (step^[Nat.find a.2] (step a.1)) = some (canonicalHead a)
  rw [← Function.iterate_succ_apply]
  exact settled.head_iterate (head_find a) (Nat.le_succ _)

theorem canonicalHead_iterate (settled : Settled step head) (a : Bubble step head) :
    ∀ n, canonicalHead ((Bubble.next settled)^[n] a) = canonicalHead a
  | 0 => rfl
  | n + 1 => by
      rw [Function.iterate_succ_apply, canonicalHead_iterate settled (Bubble.next settled a) n,
        canonicalHead_step]

/-- **The canonical head is stable.** -/
theorem stable_canonicalHead (settled : Settled step head) :
    Stable (Bubble.next settled) (canonicalHead (step := step) (head := head)) := fun a b same => by
  rw [canonicalHead_step, canonicalHead_step, same]

/-- **The behaviour determines the canonical head**, without choice. -/
theorem constantOnFibers_behaviour_canonicalHead (settled : Settled step head) :
    ConstantOnFibers (fun a : Bubble step head => behaviour step head a.1) canonicalHead := by
  intro a b same
  have ea := behaviour_eventually settled a (max (Nat.find a.2) (Nat.find b.2))
    (Nat.le_max_left _ _)
  have eb := behaviour_eventually settled b (max (Nat.find a.2) (Nat.find b.2))
    (Nat.le_max_right _ _)
  have same' : behaviour step head a.1 (max (Nat.find a.2) (Nat.find b.2)) =
      behaviour step head b.1 (max (Nat.find a.2) (Nat.find b.2)) :=
    congrFun same (max (Nat.find a.2) (Nat.find b.2))
  rw [ea, eb] at same'
  exact Option.some.inj same'

theorem factors_behaviour_canonicalHead [Nonempty K] (settled : Settled step head) :
    Factors (fun a : Bubble step head => behaviour step head a.1) canonicalHead :=
  factors_of_constantOnFibers (constantOnFibers_behaviour_canonicalHead settled)

/-- **The canonical head is the behaviour up to finite time.** -/
theorem canonicalHead_eq_iff (settled : Settled step head) (a b : Bubble step head) :
    canonicalHead a = canonicalHead b ↔
      ∃ N, ∀ n, N ≤ n → behaviour step head a.1 n = behaviour step head b.1 n := by
  constructor
  · intro same
    refine ⟨max (Nat.find a.2) (Nat.find b.2), fun n later => ?_⟩
    rw [behaviour_eventually settled a n (le_trans (Nat.le_max_left _ _) later),
      behaviour_eventually settled b n (le_trans (Nat.le_max_right _ _) later), same]
  · rintro ⟨N, agree⟩
    have later : N ≤ max N (max (Nat.find a.2) (Nat.find b.2)) := Nat.le_max_left _ _
    have e := agree _ later
    rw [behaviour_eventually settled a _
        (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)),
      behaviour_eventually settled b _
        (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))] at e
    exact Option.some.inj e

/-- **Every stable view of the bubble that keeps the head evaluation determines the
canonical head**: it factors through the behaviour, which is the coarsest such view, and the
behaviour determines the canonical head. -/
theorem factors_canonicalHead_of_stable [Nonempty K] (settled : Settled step head) {V : Type v}
    {view : Bubble step head → V} (stable : Stable (Bubble.next settled) view)
    (keeps : Factors view fun a => head a.1) : Factors view canonicalHead := by
  have coarsest := factors_behaviour stable keeps
  rw [show behaviour (Bubble.next settled) (fun b : Bubble step head => head b.1) =
    fun a => behaviour step head a.1 from funext (behaviour_bubble settled)] at coarsest
  exact factors_trans coarsest (factors_behaviour_canonicalHead settled)

/-- **The canonical head is a common coarsening of all stable views that keep the head
evaluation.** -/
theorem commonCoarsening_canonicalHead [Nonempty K] (settled : Settled step head) :
    CommonCoarsening
      (fun member : StableKeepingView.{u, v, w} (Bubble.next settled)
        (fun a : Bubble step head => head a.1) => member.view) canonicalHead :=
  fun member => factors_canonicalHead_of_stable settled member.stable member.keeps

/-! ## The boundary of the bubble -/

/-- **Negative: a stuck point never shows a constructor.** -/
theorem behaviour_stuck {a : A} (noHead : head a = none) (fixed : step a = a) (n : Nat) :
    behaviour step head a n = none := by
  rw [behaviour_apply, Function.iterate_fixed fixed]
  exact noHead

theorem not_reaches_stuck {a : A} (noHead : head a = none) (fixed : step a = a) :
    ¬ Reaches step head a := by
  rintro ⟨n, shows⟩
  have e := behaviour_stuck noHead fixed n
  rw [behaviour_apply] at e
  rw [e] at shows
  cases shows

/-- **Negative: the canonical head does not keep the head evaluation**, at a point of the
bubble that does not yet show its constructor: the constructor form it reaches has the same
canonical head and another head. -/
theorem not_factors_canonicalHead_head (settled : Settled step head) (a : Bubble step head)
    (noHead : head a.1 = none) : ¬ Factors canonicalHead fun b : Bubble step head => head b.1 := by
  refine NonTrivialFiber.not_factors ⟨a, (Bubble.next settled)^[Nat.find a.2] a,
    (canonicalHead_iterate settled a _).symm, fun same => ?_⟩
  rw [noHead, Bubble.iterate_val, head_find (step := step) (head := head) a] at same
  cases same

end Settling

/-! ## Examples: a redex, two constructors and a stuck point -/

/-- A redex, the two constructors `yes` and `no`, and a stuck point. -/
inductive Toy
  | redex
  | yes
  | no
  | stuck
  deriving DecidableEq

namespace Toy

/-- The redex steps to `yes`; the other points stay. -/
def step : Toy → Toy
  | redex => yes
  | yes => yes
  | no => no
  | stuck => stuck

/-- `yes` and `no` show their constructors; the redex and the stuck point show none. -/
def head : Toy → Option Bool
  | redex => none
  | yes => some true
  | no => some false
  | stuck => none

theorem settled : Settled step head := by
  rintro (_ | _ | _ | _) k shows <;> first | rfl | cases shows

theorem reaches_redex : Reaches step head redex := ⟨1, rfl⟩

theorem reaches_yes : Reaches step head yes := ⟨0, rfl⟩

theorem reaches_no : Reaches step head no := ⟨0, rfl⟩

end Toy

/-- **Positive**: the redex has the constructor of `yes`. -/
theorem toy_canonicalHead_redex :
    canonicalHead (⟨.redex, Toy.reaches_redex⟩ : Bubble Toy.step Toy.head) = true ∧
      canonicalHead (⟨.yes, Toy.reaches_yes⟩ : Bubble Toy.step Toy.head) = true :=
  ⟨canonicalHead_eq_of_head Toy.settled _ (n := 1) rfl,
    canonicalHead_eq_of_head Toy.settled _ (n := 0) rfl⟩

/-- **Positive**: the behaviour of the redex is eventually that constructor. -/
theorem toy_behaviour_redex :
    ∃ N, ∀ n, N ≤ n → behaviour Toy.step Toy.head .redex n = some true := by
  obtain ⟨N, eventually⟩ := behaviour_eventually' Toy.settled
    (⟨.redex, Toy.reaches_redex⟩ : Bubble Toy.step Toy.head)
  exact ⟨N, fun n later => (eventually n later).trans (by rw [toy_canonicalHead_redex.1])⟩

/-- **Positive**: `yes` and `no` have different canonical heads. -/
theorem toy_canonicalHead_yes_ne_no :
    canonicalHead (⟨.yes, Toy.reaches_yes⟩ : Bubble Toy.step Toy.head) ≠
      canonicalHead (⟨.no, Toy.reaches_no⟩ : Bubble Toy.step Toy.head) := by
  rw [canonicalHead_eq_of_head Toy.settled _ (n := 0) rfl,
    canonicalHead_eq_of_head Toy.settled _ (n := 0) rfl]
  decide

/-- **Negative**: the stuck point never shows a constructor and is outside the bubble. -/
theorem toy_stuck :
    (∀ n, behaviour Toy.step Toy.head .stuck n = none) ∧ ¬ Reaches Toy.step Toy.head .stuck :=
  ⟨behaviour_stuck (step := Toy.step) (head := Toy.head) (a := .stuck) rfl rfl,
    not_reaches_stuck (step := Toy.step) (head := Toy.head) (a := .stuck) rfl rfl⟩

/-- **Negative**: the behaviour separates the redex from `yes`, which the canonical head
identifies. -/
theorem toy_behaviour_redex_ne_yes :
    behaviour Toy.step Toy.head .redex ≠ behaviour Toy.step Toy.head .yes :=
  fun same => by
    have e := congrFun same 0
    rw [behaviour_apply, behaviour_apply] at e
    cases e

/-- **Negative**: so the canonical head does not keep the head evaluation. -/
theorem toy_not_factors_head :
    ¬ Factors (canonicalHead (step := Toy.step) (head := Toy.head)) fun b => Toy.head b.1 :=
  not_factors_canonicalHead_head Toy.settled ⟨.redex, Toy.reaches_redex⟩ rfl

end Mettapedia.GSLT.PrivilegedView

/-! ## The canonical head of a closed term of a declared datatype -/

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Domain

namespace CodeModel

section CanonicalHead

variable (d : Datatype Tower.Head)

/-- `t` **shows the constructor at `i`**: it is that constructor applied to as many terms as the
constructor has fields. -/
def ShowsCtor {n : Nat} (t : CTm Tower.Head n) (i : Nat) : Prop :=
  ∃ k fs args, d.ctors[i]? = some (k, fs) ∧ args.length = fs.length ∧
    t = CTm.appSpine (.const k) args

variable {d} (hd : d.Admissible objectChurch)

/-- `t` **has the head `i`**: its weak-head steps reach a term that shows the constructor at
`i`. -/
def HeadAt {n : Nat} (t : CTm Tower.Head n) (i : Nat) : Prop :=
  ∃ u, Relation.ReflTransGen (dataHead hd).step t u ∧ ShowsCtor d u i

/-- Two positions of a list without repeats that hold one element are one position. -/
theorem getElem?_inj_of_nodup {α : Type} : ∀ {l : List α}, l.Nodup → ∀ {i j : Nat} {a : α},
    l[i]? = some a → l[j]? = some a → i = j
  | [], _, _, _, _, hi, _ => nomatch hi
  | x :: xs, nd, i, j, a, hi, hj => by
      rw [List.nodup_cons] at nd
      match i, j, hi, hj with
      | 0, 0, _, _ => rfl
      | 0, j + 1, hi, hj =>
          rw [List.getElem?_cons_zero, Option.some.injEq] at hi
          rw [List.getElem?_cons_succ, ← hi] at hj
          exact absurd (List.mem_of_getElem? hj) nd.1
      | i + 1, 0, hi, hj =>
          rw [List.getElem?_cons_zero, Option.some.injEq] at hj
          rw [List.getElem?_cons_succ, ← hj] at hi
          exact absurd (List.mem_of_getElem? hi) nd.1
      | i + 1, j + 1, hi, hj =>
          rw [List.getElem?_cons_succ] at hi hj
          exact congrArg (· + 1) (getElem?_inj_of_nodup nd.2 hi hj)

omit hd in
/-- A term shows at most one constructor. -/
theorem ShowsCtor.unique (distinct : DistinctNames d.type d.ctors d.recursor) {n : Nat}
    {t : CTm Tower.Head n} {i j : Nat} (si : ShowsCtor d t i) (sj : ShowsCtor d t j) : i = j := by
  obtain ⟨k, fs, args, hi, -, rfl⟩ := si
  obtain ⟨k', fs', args', hj, -, e⟩ := sj
  obtain ⟨rfl, -⟩ := CTm.appSpine_const_injective e
  refine getElem?_inj_of_nodup distinct.ctorsNodup (a := k) ?_ ?_
  · rw [List.getElem?_map, hi]; rfl
  · rw [List.getElem?_map, hj]; rfl

/-- A term that shows a constructor takes no weak-head step. -/
theorem ShowsCtor.normal {n : Nat} {t : CTm Tower.Head n} {i : Nat} (shows : ShowsCtor d t i) :
    (dataHead hd).Normal t := by
  obtain ⟨k, fs, args, hi, length, rfl⟩ := shows
  intro u
  exact (dataHead hd).ctor_normal (d := d.type) (c := k)
    (fs := fieldShapes (paramTypes (d.ctors.take i)).length fs) u (.inr ⟨rfl, i, fs, hi, rfl⟩)
    (by rw [fieldShapes_length]; exact length)

/-- The position of a constructor is below the number of constructors. -/
theorem ShowsCtor.lt {n : Nat} {t : CTm Tower.Head n} {i : Nat} (shows : ShowsCtor d t i) :
    i < d.ctors.length := by
  obtain ⟨k, fs, args, hi, -, -⟩ := shows
  exact (List.getElem?_eq_some_iff.1 hi).1

/-- **A term has at most one head**: its weak-head steps are deterministic, and a term that
shows a constructor takes no step. -/
theorem HeadAt.unique {n : Nat} {t : CTm Tower.Head n} {i j : Nat} (hi : HeadAt hd t i)
    (hj : HeadAt hd t j) : i = j := by
  obtain ⟨u, ru, su⟩ := hi
  obtain ⟨v, rv, sv⟩ := hj
  have e := (dataHead hd).nf_unique ru rv (su.normal hd) (sv.normal hd)
  subst e
  exact su.unique hd.distinct sv

/-- **The head is invariant under a step.** By determinism of the package's weak-head steps:
the step of `t` is the first step of its reduction to a constructor form, unless `t` is that
form, which takes no step. -/
theorem headAt_step {n : Nat} {t t' : CTm Tower.Head n} (step : (dataHead hd).step t t')
    {i : Nat} : HeadAt hd t i ↔ HeadAt hd t' i := by
  constructor
  · rintro ⟨u, red, shows⟩
    rcases rtg_head red with rfl | ⟨c, step', rest⟩
    · exact absurd step (shows.normal hd _)
    · rw [(dataHead hd).deterministic step step']
      exact ⟨u, rest, shows⟩
  · rintro ⟨u, red, shows⟩
    exact ⟨u, .head step red, shows⟩

/-- **The head is invariant under reduction.** -/
theorem headAt_red {n : Nat} {t t' : CTm Tower.Head n}
    (red : Relation.ReflTransGen (dataHead hd).step t t') {i : Nat} :
    HeadAt hd t i ↔ HeadAt hd t' i := by
  induction red with
  | refl => exact Iff.rfl
  | tail _ step ih => exact ih.trans (headAt_step hd step)

/-! ### The negative: an open neutral term has no head -/

/-- **An open term whose erasure is neutral has no head**: it is normal, and it is no
constructor form. A match on it has no branch to take; it stays a residual. -/
theorem not_headAt_of_neutral {n : Nat} {t : CTm Tower.Head n}
    (neutral : Neutral (dataRoles d) t.erase) (i : Nat) : ¬ HeadAt hd t i := by
  rintro ⟨u, red, k, fs, args, hi, -, rfl⟩
  have e := (dataHead hd).red_normal ((dataExtension hd).neutralNormal neutral) red
  rw [← e, CTm.erase_appSpine] at neutral
  exact neutral.not_canonical (.inr ⟨k, fs.length, _, dataRoles_ctor hd.distinct hi, rfl⟩)

/-- A variable has no head. -/
theorem not_headAt_var {n : Nat} (v : Fin n) (i : Nat) : ¬ HeadAt hd (.var v) i :=
  not_headAt_of_neutral hd (.var v) i

include hd in
/-- **The recursor at a variable is stuck**: its erasure is neutral. -/
theorem rec_var_neutral {n : Nat} {pre : List (CTm Tower.Head n)}
    (hpre : pre.length = d.ctors.length + 1) (v : Fin n) :
    Neutral (dataRoles d) (CTm.appSpine (.const d.recursor) (pre ++ [.var v])).erase := by
  rw [CTm.erase_appSpine, List.map_append]
  exact Neutral.stuck_single (before := pre.map CTm.erase) (after := [])
    (by rw [List.length_map, hpre]; exact dataRoles_rec hd.distinct)
    (by rw [List.length_map, hpre]; rfl) (.var v)

/-- **Negative: the recursor at a variable selects no branch.** It takes no step and has no
head: the case analysis stays a residual. -/
theorem rec_var_stuck {n : Nat} {pre : List (CTm Tower.Head n)}
    (hpre : pre.length = d.ctors.length + 1) (v : Fin n) :
    (dataHead hd).Normal (CTm.appSpine (.const d.recursor) (pre ++ [.var v])) ∧
      ∀ i, ¬ HeadAt hd (CTm.appSpine (.const d.recursor) (pre ++ [.var v])) i :=
  ⟨(dataExtension hd).neutralNormal (rec_var_neutral hd hpre v),
    not_headAt_of_neutral hd (rec_var_neutral hd hpre v)⟩

/-! ### The one-shot decision -/

variable (d) in
/-- **The branch of the constructor at `i`**, at the motive and methods `pre` and the fields
`args`: the method of the constructor applied to the fields and to the recursor at each
recursive field. -/
def recBranch {n : Nat} (pre : List (CTm Tower.Head n)) (i : Nat) (fs : List CtorField)
    (args : List (CTm Tower.Head n)) : CTm Tower.Head n :=
  CTm.appSpine (pre.getD (1 + i) (.const .anonymous))
    (args ++ (Ideal.recFields (fs.map fieldFlag) args).map
      fun t => CTm.appSpine (.const d.recursor) (pre ++ [t]))

/-- **At a constructor form, the recursor steps to the branch of that constructor, and to
nothing else.** -/
theorem rec_ctor_step {n : Nat} {pre : List (CTm Tower.Head n)}
    (hpre : pre.length = d.ctors.length + 1) {i : Nat} {k : DeclName} {fs : List CtorField}
    (entry : d.ctors[i]? = some (k, fs)) {args : List (CTm Tower.Head n)}
    (length : args.length = fs.length) (u : CTm Tower.Head n) :
    (dataHead hd).step
        (CTm.appSpine (.const d.recursor) (pre ++ [CTm.appSpine (.const k) args])) u ↔
      u = recBranch d pre i fs args := by
  have step := dataHead_iota hd entry (listCSub (d.ctors.length + 1) pre) length
  rw [subArgs_listCSub hpre] at step
  exact ⟨fun step' => (dataHead hd).deterministic step' step, fun e => e ▸ step⟩

/-- **The one-shot decision.** The recursor at a scrutinee with the head `i` reduces, through
the scrutinee's reduction to its constructor form, to the branch of the constructor at `i`; at
that form the branch of `i` is its only step. -/
theorem rec_selects {n : Nat} {pre : List (CTm Tower.Head n)}
    (hpre : pre.length = d.ctors.length + 1) {t : CTm Tower.Head n} {i : Nat}
    (head : HeadAt hd t i) :
    ∃ k fs args, d.ctors[i]? = some (k, fs) ∧ args.length = fs.length ∧
      Relation.ReflTransGen (dataHead hd).step (CTm.appSpine (.const d.recursor) (pre ++ [t]))
        (CTm.appSpine (.const d.recursor) (pre ++ [CTm.appSpine (.const k) args])) ∧
      ∀ u, (dataHead hd).step
          (CTm.appSpine (.const d.recursor) (pre ++ [CTm.appSpine (.const k) args])) u ↔
        u = recBranch d pre i fs args := by
  obtain ⟨_, red, k, fs, args, entry, length, rfl⟩ := head
  exact ⟨k, fs, args, entry, length, dataHead_rec_red hd hpre red,
    rec_ctor_step hd hpre entry length⟩

/-! ### Distinct constructors -/

include hd in
/-- **A typed spine of a constructor at the datatype applies it to as many terms as the
constructor has fields**: it is a weak-head normal form typed at the datatype, so a canonical
form of it, and not neutral. -/
theorem dataCtorSpine_saturated {n : Nat} {Γ : CCtx Tower.Head n}
    (formed : CCtxFormed (dataChurch d) Γ) {i : Nat} {k : DeclName} {fs : List CtorField}
    (hi : d.ctors[i]? = some (k, fs)) {args : List (CTm Tower.Head n)}
    (typed : CTyped (dataChurch d) Γ (CTm.appSpine (.const k) args) (.const d.type)) :
    args.length = fs.length := by
  have role := dataRoles_ctor (base := objectRoles) hd.distinct hi
  rcases Annotated.Progress.canonical_at (dataProgressFacts hd) (dataExtension hd).levels
      (dataRules_algebra d) formed (.constructorSpine args role) typed (k := .const d.type) rfl
      (fun _ h => by cases h; exact Annotated.Progress.relevant_of_inductive dataRoles_type) with
    neutral | fits
  · rw [CTm.erase_appSpine] at neutral
    exact (neutral.not_canonical (.inr ⟨k, _, _, role, rfl⟩)).elim
  · obtain ⟨i', k', fs', args', hi', length, e⟩ := data_fits hd fits
    obtain ⟨rfl, rfl⟩ := CTm.appSpine_const_injective e
    obtain rfl : i = i' := getElem?_inj_of_nodup hd.distinct.ctorsNodup (a := k)
      (by rw [List.getElem?_map, hi]; rfl) (by rw [List.getElem?_map, hi']; rfl)
    rw [hi] at hi'
    cases hi'
    exact length

include hd in
/-- **Distinct constructors are never derivably equal**: two closed applications of different
constructors of the datatype, with any arguments, are not equal at the datatype. Both are typed
there, so each applies its constructor to as many arguments as it has fields
(`dataCtorSpine_saturated`), and the reading sends them to constructor elements with different
tags. -/
theorem ctor_not_equal_ctor {i j : Nat} {k k' : DeclName} {fs fs' : List CtorField}
    (hi : d.ctors[i]? = some (k, fs)) (hj : d.ctors[j]? = some (k', fs')) (ne : k ≠ k')
    (args args' : List (CTm Tower.Head 0)) :
    ¬ CEqual (dataChurch d) .nil (CTm.appSpine (.const k) args)
      (CTm.appSpine (.const k') args') (.const d.type) := by
  intro h
  obtain ⟨t, t'⟩ := CEqual.typed (dataExtension hd).levels h .nil
  have len := dataCtorSpine_saturated hd .nil hi t
  have len' := dataCtorSpine_saturated hd .nil hj t'
  have e := CEqual.sound (dataReading_valid hd) h (ρ := Env.nil) trivial
  rw [cinterp_appSpine, cinterp_appSpine, cinterp_const, cinterp_const, dataReading_ctor hd hi,
    dataReading_ctor hd hj,
    appSpine_ctorConstI_proj (d := d) _ _ (by rw [List.length_map, fieldShapes_length, len]),
    appSpine_ctorConstI_proj (d := d) _ _ (by rw [List.length_map, fieldShapes_length, len'])]
    at e
  exact Ideal.ctorI_ne_of_ne (fun same => ne (Kind.ctor.inj same).2.1) _ _ e

include hd in
/-- Arguments typed at the fields of a constructor are read as elements of the fields'
types. -/
theorem zipWith_projT_fieldTypeI {entry : DeclName × List CtorField} (mem : entry ∈ d.ctors) :
    ∀ {fs : List CtorField} {args : List (CTm Tower.Head 0)}, (∀ f ∈ fs, f ∈ entry.2) →
      List.Forall₂ (fun a (f : CtorField) =>
        CTyped (dataChurch d) .nil a (liftTm (f.type d.type)).liftClosed) args fs →
      List.zipWith Ideal.projT (fs.map (fieldTypeI d))
          (args.map (cinterp (dataReading d) · Env.nil)) =
        args.map (cinterp (dataReading d) · Env.nil)
  | [], [], _, .nil => rfl
  | f :: fs, a :: args, sub, .cons ha rest => by
      have sound := (CTyped.sound (dataReading_valid hd) ha (ρ := Env.nil) trivial).2.1
      rw [cinterp_liftClosed, dataReading_fieldType hd mem (sub f List.mem_cons_self)] at sound
      simp only [List.map_cons, List.zipWith_cons_cons]
      rw [sound, zipWith_projT_fieldTypeI mem (fun g hg => sub g (List.mem_cons_of_mem _ hg)) rest]

include hd in
/-- **Equal applications of one constructor have arguments with equal readings**: the reading
of a constructor application is its constructor element of the readings of its arguments, each
in its field's type, and a constructor element determines its fields. -/
theorem ctor_equal_ctor_reads {i : Nat} {k : DeclName} {fs : List CtorField}
    (hi : d.ctors[i]? = some (k, fs)) {args args' : List (CTm Tower.Head 0)}
    (h : CEqual (dataChurch d) .nil (CTm.appSpine (.const k) args)
      (CTm.appSpine (.const k) args') (.const d.type)) :
    args.map (cinterp (dataReading d) · Env.nil) =
      args'.map (cinterp (dataReading d) · Env.nil) := by
  obtain ⟨t, t'⟩ := CEqual.typed (dataExtension hd).levels h .nil
  have len := dataCtorSpine_saturated hd .nil hi t
  have len' := dataCtorSpine_saturated hd .nil hi t'
  have principal : Annotated.Progress.PrincipalType (dataChurch d) .nil (.const k)
      (cArrows (fs.map fun f => liftTm (f.type d.type)) (.const d.type)) := by
    have h : Annotated.Progress.PrincipalType (dataChurch d) .nil (.const k)
        (liftTm (ctorType d.type fs)).liftClosed :=
      Annotated.Progress.principal_const (dataExtension hd).levels .nil
        (data_ctor_declared hd hi)
    rwa [liftTm_ctorType, liftClosed_cArrows] at h
  have fields : ∀ {as : List (CTm Tower.Head 0)}, as.length = fs.length →
      CTyped (dataChurch d) .nil (CTm.appSpine (.const k) as) (.const d.type) →
      List.Forall₂ (fun a (f : CtorField) =>
        CTyped (dataChurch d) .nil a (liftTm (f.type d.type)).liftClosed) as fs :=
    fun length typed => (List.forall₂_map_right_iff
      (R := fun a (F : CTm Tower.Head 0) => CTyped (dataChurch d) .nil a F.liftClosed)).1
      (forall₂_typed_of_cArrows (dataFormerFacts hd) (dataExtension hd).levels .nil
        (.const d.type) (fs.map fun f => liftTm (f.type d.type)) _
        (by rw [List.length_map, length]) principal typed)
  have mem : (k, fs) ∈ d.ctors := List.mem_of_getElem? hi
  have e := CEqual.sound (dataReading_valid hd) h (ρ := Env.nil) trivial
  rw [cinterp_appSpine, cinterp_appSpine, cinterp_const, dataReading_ctor hd hi,
    appSpine_ctorConstI_proj (d := d) _ _ (by rw [List.length_map, fieldShapes_length, len]),
    appSpine_ctorConstI_proj (d := d) _ _ (by rw [List.length_map, fieldShapes_length, len'])]
    at e
  have e' := Ideal.ctorI_inj (by simp only [List.length_zipWith, List.length_map, len, len']) e
  rw [dataShapes_typeI hi, zipWith_projT_fieldTypeI hd mem (fun _ h => h) (fields len t),
    zipWith_projT_fieldTypeI hd mem (fun _ h => h) (fields len' t')] at e'
  exact e'

/-! ### Closed typed terms: the canonical head as a function -/

variable (d) in
/-- The closed terms typed at the declared datatype. -/
abbrev ClosedAt : Type := {t : CTm Tower.Head 0 // CTyped (dataChurch d) .nil t (.const d.type)}

variable (avoid : AvoidsModelNames d)

include avoid in
/-- **Every closed term typed at the datatype has exactly one head**: canonicity gives one,
and determinism makes it unique. -/
theorem existsUnique_headAt (t : ClosedAt d) : ∃! i : Fin d.ctors.length, HeadAt hd t.1 i := by
  obtain ⟨i, k, fs, args, hi, length, -, red⟩ := data_canonical hd avoid t.2
  have shows : ShowsCtor d (CTm.appSpine (.const k) args) i := ⟨k, fs, args, hi, length, rfl⟩
  exact ⟨⟨i, shows.lt⟩, ⟨_, red.1, shows⟩, fun j hj =>
    Fin.ext (HeadAt.unique hd hj ⟨_, red.1, shows⟩)⟩

/-- **The canonical head** of a closed term typed at the datatype: the position of the
constructor its weak-head steps reach. The package's steps are a relation with no step
function, so the head is taken by description from its unique existence. -/
noncomputable def canonicalHead (t : ClosedAt d) : Fin d.ctors.length :=
  (existsUnique_headAt hd avoid t).exists.choose

theorem canonicalHead_spec (t : ClosedAt d) : HeadAt hd t.1 (canonicalHead hd avoid t) :=
  (existsUnique_headAt hd avoid t).exists.choose_spec

/-- The canonical head is the head. -/
theorem canonicalHead_eq_iff (t : ClosedAt d) (i : Fin d.ctors.length) :
    canonicalHead hd avoid t = i ↔ HeadAt hd t.1 i :=
  ⟨fun e => e ▸ canonicalHead_spec hd avoid t,
    fun h => Fin.ext (HeadAt.unique hd (canonicalHead_spec hd avoid t) h)⟩

/-- **The canonical head is invariant under reduction.** -/
theorem canonicalHead_red (t t' : ClosedAt d)
    (red : Relation.ReflTransGen (dataHead hd).step t.1 t'.1) :
    canonicalHead hd avoid t = canonicalHead hd avoid t' :=
  (canonicalHead_eq_iff hd avoid t _).2
    ((headAt_red hd red).2 (canonicalHead_spec hd avoid t'))

/-- **The recursor on a closed typed scrutinee selects exactly the branch of its canonical
head.** -/
theorem rec_selects_canonical {pre : List (CTm Tower.Head 0)}
    (hpre : pre.length = d.ctors.length + 1) (t : ClosedAt d) :
    ∃ k fs args, d.ctors[(canonicalHead hd avoid t : Nat)]? = some (k, fs) ∧
      args.length = fs.length ∧
      Relation.ReflTransGen (dataHead hd).step (CTm.appSpine (.const d.recursor) (pre ++ [t.1]))
        (CTm.appSpine (.const d.recursor) (pre ++ [CTm.appSpine (.const k) args])) ∧
      ∀ u, (dataHead hd).step
          (CTm.appSpine (.const d.recursor) (pre ++ [CTm.appSpine (.const k) args])) u ↔
        u = recBranch d pre (canonicalHead hd avoid t) fs args :=
  rec_selects hd hpre (canonicalHead_spec hd avoid t)

end CanonicalHead


/-! ### Examples at the lists -/

section Lists

/-- **Positive**: `nil` and `cons 1 nil` show their constructors, at the positions `0` and
`1`. -/
theorem lists_heads :
    HeadAt listDecl_admissible (cnil : CTm Tower.Head 0) 0 ∧
      HeadAt listDecl_admissible (ccons (csuc czero) cnil : CTm Tower.Head 0) 1 :=
  ⟨⟨_, .refl, nilN, [], [], rfl, rfl, rfl⟩,
    ⟨_, .refl, consN, _, [csuc czero, cnil], rfl, rfl, rfl⟩⟩

/-- **Negative: the empty list is no non-empty list.** No closed equality `nil ≡ cons a l` at the
lists is derivable: the instance of `ctor_not_equal_ctor` at the lists. -/
theorem nil_not_equal_cons (a l : CTm Tower.Head 0) :
    ¬ CEqual (dataChurch listDecl) .nil cnil (ccons a l) clist :=
  ctor_not_equal_ctor listDecl_admissible (i := 0) (j := 1) rfl rfl (by decide) [] [a, l]

/-- **Negative**: over a list variable `x`, neither `x` nor `append x nil` has a head, so a
match on either stays a residual. -/
theorem listVar_no_head (i : Nat) :
    ¬ HeadAt listDecl_admissible (.var 0 : CTm Tower.Head 1) i ∧
      ¬ HeadAt listDecl_admissible appendVarNil i :=
  ⟨not_headAt_var _ 0 i, not_headAt_of_neutral _ (.app (Neutral.stuck_single
    (roles := dataRoles listDecl) (before := [appendMotive.erase, appendBase.erase,
      appendStep.erase]) (after := []) (dataRoles_rec listDecl_admissible.distinct) rfl
    (.var 0))) i⟩

end Lists

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

/-! ## Axiom audit -/

namespace Mettapedia.GSLT.PrivilegedView
#print axioms behaviour_eventually
#print axioms canonicalHead_step
#print axioms constantOnFibers_behaviour_canonicalHead
#print axioms factors_behaviour_canonicalHead
#print axioms canonicalHead_eq_iff
#print axioms factors_canonicalHead_of_stable
#print axioms commonCoarsening_canonicalHead
#print axioms behaviour_stuck
#print axioms not_factors_canonicalHead_head
#print axioms toy_canonicalHead_redex
#print axioms toy_not_factors_head

end Mettapedia.GSLT.PrivilegedView

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.CodeModel

#print axioms HeadAt.unique
#print axioms headAt_red
#print axioms existsUnique_headAt
#print axioms canonicalHead_red
#print axioms rec_selects
#print axioms rec_selects_canonical
#print axioms not_headAt_of_neutral
#print axioms rec_var_stuck
#print axioms listVar_no_head
#print axioms dataCtorSpine_saturated
#print axioms ctor_not_equal_ctor
#print axioms ctor_equal_ctor_reads
#print axioms nil_not_equal_cons

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.CodeModel
