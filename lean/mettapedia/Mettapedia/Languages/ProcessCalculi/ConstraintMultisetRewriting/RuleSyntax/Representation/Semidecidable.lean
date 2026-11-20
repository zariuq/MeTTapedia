import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.Hosting
import Mathlib.Computability.RE
import Mathlib.Computability.Primrec.List

/-!
# What the may sense can host is semi-decidable, given a computable enumeration of successors

A target whose step is given by a primitive recursive enumeration of the successors of each state
(`y ∈ next x`), read through a primitive recursive encoding of the source states and a primitive recursive
representation:

* **Bounded reach** (`within`, `reaches_iff_within`): the states reachable in at most `k` steps are a list,
  primitive recursive in the state and `k` (`within_primrec`), and every reachable state is in one of them.
* **Reaching a represented state is semi-decidable** (`reach_re`): the set of pairs `(a, b)` such that a state
  representing `b` is reachable from the encoding of `a` is recursively enumerable in Mathlib's sense
  (`REPred`: the domain of a partial recursive function), by an unbounded search over `k`.
* **So the may sense hosts only systems with a recursively enumerable reachability relation** (`may_re`): a
  system on the naturals hosted in the may sense (`Hosting.MayHosting`) by such a target has a recursively
  enumerable reflexive-transitive closure.

Together with `Machines.Enumerable.hosts_re` (every recursively enumerable step relation is hosted in the may
sense by a finite program) this pins the may sense to recursive enumerability, up to the reachability the may
sense observes, once the program's step has such an enumeration: the hypothesis below.

## What is assumed of the program

The theorems here are stated for a target of the form `equalityGSLT T (fun x y => y ∈ next x)` with `T`
`Primcodable` and `next` primitive recursive. For the step of a finite program this is the one hypothesis left
open: a coding of bags of rows into a `Primcodable` type under which the successors of a bag are enumerated by a
primitive recursive function. The search space is the one of `Effective.successors_finite` (a rule, and rows of the
bag for its take and read patterns), at each point of which first-order matching decides the one successor;
what is missing in the tree is a `Primcodable` instance for rows and bags and a primitive recursive matcher.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.Semidecidable

open Mettapedia.GSLT
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)
open Hosting (MayHosting reflTransGen_of_multiStep)

variable {T : Type} [Primcodable T]

/-- **The states within `k` steps** of a successor enumeration. -/
def within (next : T → List T) : ℕ → T → List T
  | 0, t => [t]
  | k + 1, t => within next k t ++ (within next k t).flatMap next

omit [Primcodable T] in
/-- **A state is reachable exactly when it is within some number of steps.** -/
theorem reaches_iff_within {next : T → List T} {a t : T} :
    Relation.ReflTransGen (fun x y => y ∈ next x) a t ↔ ∃ k, t ∈ within next k a := by
  constructor
  · intro path
    induction path with
    | refl => exact ⟨0, List.mem_singleton_self _⟩
    | tail _ stepped reached =>
        obtain ⟨k, inside⟩ := reached
        exact ⟨k + 1, List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, inside, stepped⟩)⟩
  · rintro ⟨k, inside⟩
    induction k generalizing t with
    | zero =>
        rw [List.mem_singleton.mp inside]
    | succ k ih =>
        rcases List.mem_append.mp inside with old | new
        · exact ih old
        · obtain ⟨x, inX, stepped⟩ := List.mem_flatMap.mp new
          exact (ih inX).tail stepped

/-- **Bounded reach is primitive recursive.** -/
theorem within_primrec {next : T → List T} (prim : Primrec next) :
    Primrec₂ fun (a : T) (k : ℕ) => within next k a := by
  have start : Primrec fun a : T => [a] := Primrec.list_cons.comp Primrec.id (Primrec.const [])
  have grow : Primrec₂ fun (_ : T) (p : ℕ × List T) => p.2 ++ p.2.flatMap next :=
    Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.list_flatMap (Primrec.snd.comp Primrec.snd) (prim.comp Primrec.snd).to₂)
  refine (Primrec.nat_rec start grow).of_eq fun a k => ?_
  induction k with
  | zero => rfl
  | succ k ih => rw [within, ← ih]

/-- **Reaching a represented state is semi-decidable**: for a primitive recursive successor enumeration, a
primitive recursive encoding and a primitive recursive representation, the pairs `(a, b)` such that a state
representing `b` is reachable from the encoding of `a` form a recursively enumerable set. -/
theorem reach_re {next : T → List T} (prim : Primrec next) {enc : ℕ → T} (encPrim : Primrec enc)
    {rep : ℕ → T → Bool} (repPrim : Primrec₂ rep) :
    REPred fun p : ℕ × ℕ => ∃ t, Relation.ReflTransGen (fun x y => y ∈ next x) (enc p.1) t ∧ rep p.2 t = true := by
  have reach : Primrec fun q : (ℕ × ℕ) × ℕ => within next q.2 (enc q.1.1) :=
    (within_primrec prim).comp (encPrim.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
  have found : Primrec fun q : (ℕ × ℕ) × ℕ => (within next q.2 (enc q.1.1)).findIdx (rep q.1.2) :=
    Primrec.list_findIdx reach (repPrim.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
  have size : Primrec fun q : (ℕ × ℕ) × ℕ => (within next q.2 (enc q.1.1)).length :=
    Primrec.list_length.comp reach
  have test : Primrec fun q : (ℕ × ℕ) × ℕ =>
      decide ((within next q.2 (enc q.1.1)).findIdx (rep q.1.2) < (within next q.2 (enc q.1.1)).length) :=
    Primrec.nat_lt.decide.comp found size
  have search : Partrec fun p : ℕ × ℕ => Nat.rfind fun k =>
      Part.some (decide ((within next k (enc p.1)).findIdx (rep p.2) < (within next k (enc p.1)).length)) :=
    Partrec.rfind test.to_comp.to₂.partrec₂
  refine (Partrec.dom_re search).of_eq fun p => Nat.rfind_dom.trans ?_
  constructor
  · rintro ⟨k, inside, -⟩
    have holds := of_decide_eq_true (Part.mem_some_iff.mp inside).symm
    obtain ⟨t, member, represented⟩ := List.findIdx_lt_length.mp holds
    exact ⟨t, reaches_iff_within.mpr ⟨k, member⟩, represented⟩
  · rintro ⟨t, path, represented⟩
    obtain ⟨k, member⟩ := reaches_iff_within.mp path
    exact ⟨k, Part.mem_some_iff.mpr (decide_eq_true (List.findIdx_lt_length.mpr ⟨t, member, represented⟩)).symm,
      fun _ => trivial⟩

/-- **The may sense hosts only systems whose reachability is recursively enumerable**, for a target whose step is
a primitive recursive successor enumeration, read through a primitive recursive encoding whose states represent
their numbers and a primitive recursive representation. -/
theorem may_re {R : ℕ → ℕ → Prop} {next : T → List T} (prim : Primrec next)
    (H : MayHosting (equalityGSLT ℕ R) (equalityGSLT T fun x y => y ∈ next x))
    {enc : ℕ → T} (encPrim : Primrec enc) (encRepresents : ∀ a, H.represents a (enc a))
    {rep : ℕ → T → Bool} (repPrim : Primrec₂ rep) (represents_iff : ∀ b t, H.represents b t ↔ rep b t = true) :
    REPred fun p : ℕ × ℕ => Relation.ReflTransGen R p.1 p.2 := by
  refine (reach_re prim encPrim repPrim).of_eq fun p =>
    Iff.trans ?_ (H.reachable_iff (encRepresents p.1) p.2).symm
  constructor
  · rintro ⟨t, path, represented⟩
    exact ⟨t, multiStep_of_steps path, (represents_iff p.2 t).mpr represented⟩
  · rintro ⟨t, run, represented⟩
    exact ⟨t, reflTransGen_of_multiStep run, (represents_iff p.2 t).mp represented⟩
where
  /-- A path of steps is a run. -/
  multiStep_of_steps {a t : T} (path : Relation.ReflTransGen (fun x y => y ∈ next x) a t) :
      (equalityGSLT T fun x y => y ∈ next x).MultiStep a t := by
    induction path with
    | refl => exact .refl _
    | tail _ stepped reached =>
        exact Mettapedia.GSLT.IndexedOperational.multiStepAppend reached (.step stepped (.refl _))

/-! ## An instance of every hypothesis -/

/-- The successor system on the naturals. -/
def succStep (a b : ℕ) : Prop := b = a + 1

/-- Its enumeration of successors. -/
def succNext (x : ℕ) : List ℕ := [x + 1]

/-- **The successor system, hosted by its own enumeration**: a number is related to itself and represents
itself. -/
def succMay : MayHosting (equalityGSLT ℕ succStep) (equalityGSLT ℕ fun x y => y ∈ succNext x) where
  related := fun (a t : ℕ) => t = a
  readStep := by
    intro a t t' related stepped
    have isA : t = a := related
    subst isA
    exact Or.inr ⟨t', List.mem_singleton.mp stepped, rfl⟩
  represents := fun (a t : ℕ) => t = a
  related_of_represents := fun same => same
  sound := fun {_ _ _} first second => first.symm.trans second
  realize := by
    intro a b t represented stepped
    have isA : t = a := represented
    subst isA
    exact ⟨b, .step (show b ∈ succNext t from List.mem_singleton.mpr stepped) (.refl _), rfl⟩

/-- **The hypotheses of `may_re` are met**: the reachability of the successor system is recursively
enumerable by `may_re`, with the successor enumeration, the identity encoding and equality as representation. -/
theorem succ_re : REPred fun p : ℕ × ℕ => Relation.ReflTransGen succStep p.1 p.2 :=
  may_re (T := ℕ) (next := succNext) (Primrec.list_cons.comp Primrec.succ (Primrec.const [])) succMay
    (enc := id) Primrec.id (fun _ => rfl) (rep := fun b t => decide (t = b))
    (Primrec.eq.decide.comp Primrec.snd Primrec.fst)
    (fun (b t : ℕ) => show t = b ↔ decide (t = b) = true from decide_eq_true_iff.symm)

#print axioms reaches_iff_within
#print axioms within_primrec
#print axioms reach_re
#print axioms may_re
#print axioms succMay
#print axioms succ_re

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.Semidecidable
