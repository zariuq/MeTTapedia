import Mettapedia.Logic.HOL.Embedding.ZFSetInductive
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts

/-!
# Recursion along the subterm order of an inductive carrier

`recFun` computes a value from the values at the direct recursive arguments of one
constructor. The recursion defined here follows every proper subterm. A direct subterm
has a smaller rank than the set it stands in, and a set outside the carrier has no
subterm; so the subterm relation and its transitive closure are well-founded on every
set, for every signature, and `WellFounded.fix` supplies the unfolding equation at every
set. When no two constructors carry one tag, the stage drops as well: a direct subterm of
a set in `iterate sig (n + 1)` lies in `iterate sig n` (`sub_mem_prev`).

Two carriers give the lexicographic product of their transitive subterm relations.
A third carrier, and any further one, is the same product nested once more; the
function set is the corresponding tower of traced products. The development writes
the two-carrier case.

Primitive recursion is the special case that reads only the direct subterms, for a
signature with distinct tags (`subRec_recFun`). Half,
the Ackermann function, and addition with an accumulator are computed on the embedded
natural numbers. An equation that does not descend along a subterm may have no
solution, or more than one.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetInductiveRecursion

open Mettapedia.Logic.HOL.Embedding.ZFSetInductive
open Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts
open Mettapedia.Logic.HOL.Embedding.ZFSetDependentProducts
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation (numeral)
open Relation
open scoped ZFSet Ordinal
open Classical

universe u

/-! ## Recursive positions -/

/-- `y` stands in a recursive field of the argument list. -/
inductive AtRecursive : List Field.{u} → List ZFSet.{u} → ZFSet.{u} → Prop where
  | head {fs : List Field.{u}} {args : List ZFSet.{u}} {a : ZFSet.{u}} :
      AtRecursive (Field.recursive :: fs) (a :: args) a
  | tail {field : Field.{u}} {fs : List Field.{u}} {a y : ZFSet.{u}} {args : List ZFSet.{u}} :
      AtRecursive fs args y → AtRecursive (field :: fs) (a :: args) y

theorem atRecursive_mem {X : ZFSet.{u}} {fs : List Field.{u}} {args : List ZFSet.{u}}
    {y : ZFSet.{u}} (fitting : Fits X fs args) (pos : AtRecursive fs args y) : y ∈ X := by
  induction pos with
  | head =>
      cases fitting with
      | recursive member _ => exact member
  | tail _ ih =>
      cases fitting with
      | recursive _ rest => exact ih rest
      | ofSet _ rest => exact ih rest

theorem atRecursive_tuple_rank {fs : List Field.{u}} {args : List ZFSet.{u}} {y : ZFSet.{u}}
    (pos : AtRecursive fs args y) : y.rank < (tuple args).rank := by
  induction pos with
  | head =>
      rw [tuple]
      exact rank_gt_first _ _
  | tail _ ih =>
      rw [tuple]
      exact ih.trans (rank_gt_second _ _)

theorem arg_rank_lt_constructor (t y : ZFSet.{u}) (ys : List ZFSet.{u}) :
    y.rank < (constructorValue t (y :: ys)).rank := by
  have inTuple : y.rank < (tuple (y :: ys)).rank := by
    rw [tuple]
    exact rank_gt_first y (tuple ys)
  have inValue : (tuple (y :: ys)).rank < (constructorValue t (y :: ys)).rank := by
    rw [constructorValue]
    exact rank_gt_second t (tuple (y :: ys))
  exact inTuple.trans inValue

/-! ## The subterm relation -/

/-- `y` is a direct subterm of `x`: `x` lies in the carrier, and `y` is the argument
at a recursive field of the constructor value that `x` is. -/
def Sub (sig : Signature.{u}) (y x : ZFSet.{u}) : Prop :=
  x ∈ carrier sig ∧
    ∃ (i : Nat) (c : Constructor.{u}) (args : List ZFSet.{u}),
      sig[i]? = some c ∧ Fits (carrier sig) c.fields args ∧
        constructorValue c.tag args = x ∧ AtRecursive c.fields args y

theorem sub_right_mem {sig : Signature.{u}} {y x : ZFSet.{u}} (related : Sub sig y x) :
    x ∈ carrier sig :=
  related.1

theorem sub_left_mem {sig : Signature.{u}} {y x : ZFSet.{u}} (related : Sub sig y x) :
    y ∈ carrier sig := by
  obtain ⟨_, _, _, _, _, fitting, _, pos⟩ := related
  exact atRecursive_mem fitting pos

/-- A set outside the carrier has no direct subterm. -/
theorem sub_outside {sig : Signature.{u}} {x : ZFSet.{u}} (outside : x ∉ carrier sig)
    (y : ZFSet.{u}) : ¬ Sub sig y x :=
  fun related => outside (sub_right_mem related)

theorem sub_at {sig : Signature.{u}} {i : Nat} {c : Constructor.{u}} {args : List ZFSet.{u}}
    {y : ZFSet.{u}} (atIndex : sig[i]? = some c) (fitting : Fits (carrier sig) c.fields args)
    (pos : AtRecursive c.fields args y) : Sub sig y (constructorValue c.tag args) :=
  ⟨constructor_mem_carrier atIndex fitting, i, c, args, atIndex, fitting, rfl, pos⟩

theorem sub_rank_lt {sig : Signature.{u}} {y x : ZFSet.{u}} (related : Sub sig y x) :
    y.rank < x.rank := by
  obtain ⟨_, _, c, args, _, _, valueEq, pos⟩ := related
  have hlt : y.rank < (constructorValue c.tag args).rank :=
    (atRecursive_tuple_rank pos).trans (by
      rw [constructorValue]
      exact rank_gt_second c.tag (tuple args))
  rw [valueEq] at hlt
  exact hlt

/-- The stage drops, for a signature with distinct tags. A direct subterm of a member of
`iterate sig (n + 1)` was already present in `iterate sig n`. -/
theorem sub_mem_prev {sig : Signature.{u}} (distinct : DistinctTags sig) {y x : ZFSet.{u}}
    {n : Nat} (related : Sub sig y x) (member : x ∈ iterate sig (n + 1)) :
    y ∈ iterate sig n := by
  obtain ⟨_, i, c, args, atIndex, fitting, valueEq, pos⟩ := related
  obtain ⟨j, d, args', atJ, fitting', valueEq'⟩ := exists_presentation member
  obtain ⟨rfl, rfl, rfl⟩ := inversion_unique distinct atIndex atJ fitting
    (fitting'.mono (iterate_subset_carrier n)) valueEq valueEq'
  exact atRecursive_mem fitting' pos

/-- `Sub sig` is well-founded on every set: a direct subterm has a smaller rank. A set
outside the carrier has no predecessor. -/
theorem sub_wf (sig : Signature.{u}) : WellFounded (Sub sig) :=
  Subrelation.wf (r := InvImage (· < ·) ZFSet.rank) (fun related => sub_rank_lt related)
    (InvImage.wf ZFSet.rank Ordinal.lt_wf)

/-- The transitive closure of the direct subterm relation. -/
def SubPlus (sig : Signature.{u}) (y x : ZFSet.{u}) : Prop :=
  TransGen (Sub sig) y x

theorem subPlus_wf (sig : Signature.{u}) : WellFounded (SubPlus sig) :=
  WellFounded.transGen (sub_wf sig)

theorem subPlus_mem {sig : Signature.{u}} {y x : ZFSet.{u}} (related : SubPlus sig y x) :
    y ∈ carrier sig ∧ x ∈ carrier sig := by
  induction related with
  | single h => exact ⟨sub_left_mem h, sub_right_mem h⟩
  | tail _ hbc ih => exact ⟨ih.1, sub_right_mem hbc⟩

theorem subPlus_left_mem {sig : Signature.{u}} {y x : ZFSet.{u}} (related : SubPlus sig y x) :
    y ∈ carrier sig :=
  (subPlus_mem related).1

theorem subPlus_right_mem {sig : Signature.{u}} {y x : ZFSet.{u}} (related : SubPlus sig y x) :
    x ∈ carrier sig :=
  (subPlus_mem related).2

theorem subPlus_rank_lt {sig : Signature.{u}} {y x : ZFSet.{u}} (related : SubPlus sig y x) :
    y.rank < x.rank := by
  induction related with
  | single h => exact sub_rank_lt h
  | tail _ hbc ih => exact ih.trans (sub_rank_lt hbc)

theorem subPlus_at {sig : Signature.{u}} {i : Nat} {c : Constructor.{u}}
    {args : List ZFSet.{u}} {y : ZFSet.{u}} (atIndex : sig[i]? = some c)
    (fitting : Fits (carrier sig) c.fields args) (pos : AtRecursive c.fields args y) :
    SubPlus sig y (constructorValue c.tag args) :=
  TransGen.single (sub_at atIndex fitting pos)

/-- The one-step function of recursion along proper subterms. -/
abbrev SubStep (sig : Signature.{u}) :=
  (x : ZFSet.{u}) → ((y : ZFSet.{u}) → SubPlus sig y x → ZFSet.{u}) → ZFSet.{u}

/-- The two-argument step, lexicographic in the two transitive subterm relations. -/
abbrev LexStep (sig₁ sig₂ : Signature.{u}) :=
  (p : ZFSet.{u} × ZFSet.{u}) →
    ((q : ZFSet.{u} × ZFSet.{u}) →
      Prod.Lex (SubPlus sig₁) (SubPlus sig₂) q p → ZFSet.{u}) →
    ZFSet.{u}

/-! ## Recursion along subterms -/

noncomputable def subRec {sig : Signature.{u}} (F : SubStep sig) (x : ZFSet.{u}) : ZFSet.{u} :=
  WellFounded.fix (subPlus_wf sig) F x

theorem subRec_eq {sig : Signature.{u}} (F : SubStep sig) (x : ZFSet.{u}) :
    subRec F x = F x (fun y _ => subRec F y) :=
  WellFounded.fix_eq (subPlus_wf sig) F x

theorem subRec_unique {sig : Signature.{u}} (F : SubStep sig) (g : ZFSet.{u} → ZFSet.{u})
    (equations : ∀ x, x ∈ carrier sig → g x = F x (fun y _ => g y))
    {x : ZFSet.{u}} (member : x ∈ carrier sig) : g x = subRec F x := by
  suffices ∀ x, x ∈ carrier sig → g x = subRec F x from this x member
  intro x
  refine WellFounded.induction (hwf := subPlus_wf sig)
    (C := fun z => z ∈ carrier sig → g z = subRec F z) x ?_
  intro x ih member
  rw [equations x member, subRec_eq]
  apply congrArg (F x)
  funext y
  funext related
  exact ih y related (subPlus_left_mem related)

/-! ## Primitive recursion reads only the direct subterms -/

/-- A constructor presentation of a member of the carrier. With distinct tags there is
one (`inversionOf_spec`). -/
structure Inversion (sig : Signature.{u}) (x : ZFSet.{u}) where
  index : Nat
  ctor : Constructor.{u}
  args : List ZFSet.{u}
  atIndex : sig[index]? = some ctor
  fitting : Fits (carrier sig) ctor.fields args
  valueEq : constructorValue ctor.tag args = x

theorem inversion_nonempty {sig : Signature.{u}} {x : ZFSet.{u}} (member : x ∈ carrier sig) :
    Nonempty (Inversion sig x) := by
  obtain ⟨i, c, args, atIndex, fitting, valueEq⟩ := exists_inversion member
  exact ⟨⟨i, c, args, atIndex, fitting, valueEq⟩⟩

noncomputable def inversionOf {sig : Signature.{u}} {x : ZFSet.{u}} (member : x ∈ carrier sig) :
    Inversion sig x :=
  Classical.choice (inversion_nonempty member)

theorem inversionOf_spec {sig : Signature.{u}} (distinct : DistinctTags sig) {x : ZFSet.{u}}
    (member : x ∈ carrier sig) {i : Nat} {c : Constructor.{u}} {args : List ZFSet.{u}}
    (atIndex : sig[i]? = some c) (fitting : Fits (carrier sig) c.fields args)
    (valueEq : constructorValue c.tag args = x) :
    (inversionOf member).index = i ∧ (inversionOf member).ctor = c ∧
      (inversionOf member).args = args :=
  inversion_unique distinct (inversionOf member).atIndex atIndex (inversionOf member).fitting
    fitting (inversionOf member).valueEq valueEq

noncomputable def applyConstructor {sig : Signature.{u}}
    (onConstructor : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    (x : ZFSet.{u}) (f : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  if member : x ∈ carrier sig then
    onConstructor (inversionOf member).index (inversionOf member).args
      (mapRec f (inversionOf member).ctor.fields (inversionOf member).args)
  else
    ∅

theorem applyConstructor_eq {sig : Signature.{u}} (distinct : DistinctTags sig)
    (onConstructor : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    {i : Nat} {c : Constructor.{u}} {args : List ZFSet.{u}}
    (atIndex : sig[i]? = some c) (fitting : Fits (carrier sig) c.fields args)
    (f : ZFSet.{u} → ZFSet.{u}) :
    applyConstructor (sig := sig) onConstructor (constructorValue c.tag args) f =
      onConstructor i args (mapRec f c.fields args) := by
  have member := constructor_mem_carrier atIndex fitting
  obtain ⟨hi, hc, ha⟩ := inversionOf_spec distinct member atIndex fitting rfl
  rw [applyConstructor, dif_pos member, hi, hc, ha]

theorem mapRec_at_congr {f g : ZFSet.{u} → ZFSet.{u}} {X : ZFSet.{u}}
    {fs : List Field.{u}} {args : List ZFSet.{u}} (fitting : Fits X fs args)
    (agree : ∀ a, AtRecursive fs args a → f a = g a) : mapRec f fs args = mapRec g fs args := by
  induction fitting with
  | nil => rfl
  | recursive _ _ ih =>
      rename_i a _member _rest
      rw [mapRec_recursive, mapRec_recursive, agree a AtRecursive.head]
      exact congrArg (fun rest => g a :: rest)
        (ih fun b hb => agree b (AtRecursive.tail hb))
  | ofSet _ _ ih =>
      rw [mapRec_ofSet, mapRec_ofSet]
      exact ih fun b hb => agree b (AtRecursive.tail hb)

/-- The primitive step, read through the subterm recursion. At a recursive argument
the value is the recursive call; at every other set it is `∅`, and `mapRec` does not
read those positions. -/
noncomputable def recAsSubStep {sig : Signature.{u}}
    (onConstructor : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u}) :
    SubStep sig :=
  fun x rec =>
    applyConstructor (sig := sig) onConstructor x fun y =>
      if related : Nonempty (SubPlus sig y x) then
        rec y (Classical.choice related)
      else
        ∅

theorem subRec_recFun {sig : Signature.{u}} (distinct : DistinctTags sig)
    (onConstructor : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    {x : ZFSet.{u}} (member : x ∈ carrier sig) :
    subRec (sig := sig) (recAsSubStep (sig := sig) onConstructor) x =
      recFun (sig := sig) onConstructor x := by
  refine recFun_unique distinct onConstructor
    (subRec (sig := sig) (recAsSubStep (sig := sig) onConstructor)) ?_ member
  intro i c args atIndex fitting
  rw [subRec_eq, recAsSubStep, applyConstructor_eq distinct onConstructor atIndex fitting]
  apply congrArg (onConstructor i args)
  refine mapRec_at_congr fitting ?_
  intro a pos
  rw [dif_pos ⟨subPlus_at atIndex fitting pos⟩]

/-! ## Two arguments, lexicographically -/

theorem lex_wf {α : Type*} {β : Type*} {ra : α → α → Prop} {rb : β → β → Prop}
    (ha : WellFounded ra) (hb : WellFounded rb) : WellFounded (Prod.Lex ra rb) :=
  ⟨fun ⟨a, b⟩ => Prod.lexAccessible (ha.apply a) hb.apply b⟩

noncomputable def lexRec {sig₁ sig₂ : Signature.{u}} (F : LexStep sig₁ sig₂)
    (p : ZFSet.{u} × ZFSet.{u}) : ZFSet.{u} :=
  WellFounded.fix (lex_wf (subPlus_wf sig₁) (subPlus_wf sig₂)) F p

theorem lexRec_eq {sig₁ sig₂ : Signature.{u}} (F : LexStep sig₁ sig₂)
    (p : ZFSet.{u} × ZFSet.{u}) :
    lexRec F p = F p (fun q _ => lexRec F q) :=
  WellFounded.fix_eq (lex_wf (subPlus_wf sig₁) (subPlus_wf sig₂)) F p

/-- If the unfolding equation holds at every pair, the function is the lexicographic
recursion at every pair, and in particular on the product of the carriers. -/
theorem lexRec_unique_all {sig₁ sig₂ : Signature.{u}} (F : LexStep sig₁ sig₂)
    (g : ZFSet.{u} × ZFSet.{u} → ZFSet.{u})
    (equations : ∀ p, g p = F p (fun q _ => g q)) (p : ZFSet.{u} × ZFSet.{u}) :
    g p = lexRec F p := by
  refine WellFounded.induction (hwf := lex_wf (subPlus_wf sig₁) (subPlus_wf sig₂))
    (C := fun q => g q = lexRec F q) p ?_
  intro p ih
  rw [equations p, lexRec_eq]
  apply congrArg (F p)
  funext q
  funext related
  exact ih q related

/-- On the product of the carriers, a function that satisfies the unfolding there
agrees with `lexRec` when the step depends on a recursive value only through pairs
that remain in the product. A left step of `Prod.Lex` may replace the second
component by a set outside the second carrier, and the equation on the product does
not determine that value. -/
theorem lexRec_unique {sig₁ sig₂ : Signature.{u}} (F : LexStep sig₁ sig₂)
    (g : ZFSet.{u} × ZFSet.{u} → ZFSet.{u})
    (equations : ∀ p, p.1 ∈ carrier sig₁ → p.2 ∈ carrier sig₂ →
      g p = F p (fun q _ => g q))
    (stable : ∀ p rec rec', p.1 ∈ carrier sig₁ → p.2 ∈ carrier sig₂ →
      (∀ q (hq : Prod.Lex (SubPlus sig₁) (SubPlus sig₂) q p),
        q.1 ∈ carrier sig₁ → q.2 ∈ carrier sig₂ → rec q hq = rec' q hq) →
      F p rec = F p rec')
    {p : ZFSet.{u} × ZFSet.{u}} (h1 : p.1 ∈ carrier sig₁) (h2 : p.2 ∈ carrier sig₂) :
    g p = lexRec F p := by
  suffices ∀ p, p.1 ∈ carrier sig₁ → p.2 ∈ carrier sig₂ → g p = lexRec F p from this p h1 h2
  intro p
  refine WellFounded.induction (hwf := lex_wf (subPlus_wf sig₁) (subPlus_wf sig₂))
    (C := fun q => q.1 ∈ carrier sig₁ → q.2 ∈ carrier sig₂ → g q = lexRec F q) p ?_
  intro p ih h1 h2
  rw [equations p h1 h2, lexRec_eq]
  exact stable p (fun q _ => g q) (fun q _ => lexRec F q) h1 h2
    fun q hq hq1 hq2 => ih q hq hq1 hq2

/-! ## The value is an element of the traced function set -/

theorem subRec_mem {sig : Signature.{u}} {B : ZFSet.{u} → ZFSet.{u}} {F : SubStep sig}
    (preserve : ∀ x rec, x ∈ carrier sig →
      (∀ y (hy : SubPlus sig y x), rec y hy ∈ B y) → F x rec ∈ B x)
    {x : ZFSet.{u}} (member : x ∈ carrier sig) : subRec F x ∈ B x := by
  suffices ∀ x, x ∈ carrier sig → subRec F x ∈ B x from this x member
  intro x
  refine WellFounded.induction (hwf := subPlus_wf sig)
    (C := fun z => z ∈ carrier sig → subRec F z ∈ B z) x ?_
  intro x ih member
  rw [subRec_eq]
  exact preserve x (fun y _ => subRec F y) member fun y hy => ih y hy (subPlus_left_mem hy)

theorem subRec_trace_mem {sig : Signature.{u}} {B : ZFSet.{u} → ZFSet.{u}} {F : SubStep sig}
    (preserve : ∀ x rec, x ∈ carrier sig →
      (∀ y (hy : SubPlus sig y x), rec y hy ∈ B y) → F x rec ∈ B x) :
    traceLam (graph (carrier sig) (subRec F)) ∈ tracePiSet (carrier sig) B :=
  mem_tracePiSet.mpr
    ⟨graph (carrier sig) (subRec F),
      graph_mem_piSet (fun _ hx => subRec_mem preserve hx), rfl⟩

theorem subRec_trace_app {sig : Signature.{u}} (F : SubStep sig) {x : ZFSet.{u}}
    (member : x ∈ carrier sig) :
    traceApp (traceLam (graph (carrier sig) (subRec F))) x = subRec F x :=
  traceApp_graph_beta (subRec F) member

theorem lexRec_mem {sig₁ sig₂ : Signature.{u}} {C : ZFSet.{u}} {F : LexStep sig₁ sig₂}
    (preserve : ∀ p rec, p.1 ∈ carrier sig₁ → p.2 ∈ carrier sig₂ →
      (∀ q hq, q.1 ∈ carrier sig₁ → q.2 ∈ carrier sig₂ → rec q hq ∈ C) → F p rec ∈ C)
    {p : ZFSet.{u} × ZFSet.{u}} (h1 : p.1 ∈ carrier sig₁) (h2 : p.2 ∈ carrier sig₂) :
    lexRec F p ∈ C := by
  suffices ∀ p, p.1 ∈ carrier sig₁ → p.2 ∈ carrier sig₂ → lexRec F p ∈ C from this p h1 h2
  intro p
  refine WellFounded.induction (hwf := lex_wf (subPlus_wf sig₁) (subPlus_wf sig₂))
    (C := fun q => q.1 ∈ carrier sig₁ → q.2 ∈ carrier sig₂ → lexRec F q ∈ C) p ?_
  intro p ih h1 h2
  rw [lexRec_eq]
  exact preserve p (fun q _ => lexRec F q) h1 h2 fun q hq hq1 hq2 => ih q hq hq1 hq2

/-- The curried trace of a two-argument recursion: at each first argument, the trace
of the function of the second argument. -/
noncomputable def lexTrace {sig₁ sig₂ : Signature.{u}} (F : LexStep sig₁ sig₂) : ZFSet.{u} :=
  traceLam (graph (carrier sig₁) fun m =>
    traceLam (graph (carrier sig₂) fun n => lexRec F (m, n)))

theorem lexTrace_mem {sig₁ sig₂ : Signature.{u}} {C : ZFSet.{u}} {F : LexStep sig₁ sig₂}
    (preserve : ∀ p rec, p.1 ∈ carrier sig₁ → p.2 ∈ carrier sig₂ →
      (∀ q hq, q.1 ∈ carrier sig₁ → q.2 ∈ carrier sig₂ → rec q hq ∈ C) → F p rec ∈ C) :
    lexTrace F ∈
      tracePiSet (carrier sig₁) fun _ => tracePiSet (carrier sig₂) fun _ => C := by
  refine mem_tracePiSet.mpr ⟨graph (carrier sig₁) fun m =>
      traceLam (graph (carrier sig₂) fun n => lexRec F (m, n)), ?_, rfl⟩
  refine graph_mem_piSet fun m hm => ?_
  refine mem_tracePiSet.mpr ⟨graph (carrier sig₂) fun n => lexRec F (m, n), ?_, rfl⟩
  exact graph_mem_piSet fun n hn => lexRec_mem preserve hm hn

theorem lexTrace_app {sig₁ sig₂ : Signature.{u}} (F : LexStep sig₁ sig₂)
    {m n : ZFSet.{u}} (hm : m ∈ carrier sig₁) (hn : n ∈ carrier sig₂) :
    traceApp (traceApp (lexTrace F) m) n = lexRec F (m, n) := by
  rw [lexTrace, traceApp_graph_beta _ hm, traceApp_graph_beta _ hn]

/-! ## Embedded natural numbers -/

theorem sub_embed_succ (n : Nat) : Sub natSignature (natEmbed n) (natEmbed (n + 1)) :=
  sub_at (i := 1) (c := ⟨numeral 1, [Field.recursive]⟩) rfl
    (Fits.recursive (natEmbed_mem n) Fits.nil) AtRecursive.head

theorem subPlus_embed_one (n : Nat) :
    SubPlus natSignature (natEmbed n) (natEmbed (n + 1)) :=
  TransGen.single (sub_embed_succ n)

theorem subPlus_embed_two (n : Nat) :
    SubPlus natSignature (natEmbed n) (natEmbed (n + 2)) :=
  TransGen.tail (subPlus_embed_one n) (sub_embed_succ (n + 1))

theorem natEmbed_zero_ne_succ (n : Nat) : natEmbed 0 ≠ natEmbed (n + 1) :=
  constructorValue_ne_of_tag_ne numeral_zero_ne_one [] [natEmbed n]

theorem natEmbed_injective : Function.Injective (natEmbed : Nat → ZFSet.{u}) := by
  intro m n h
  induction m generalizing n with
  | zero =>
      cases n with
      | zero => rfl
      | succ n => exact (natEmbed_zero_ne_succ n h).elim
  | succ m ih =>
      cases n with
      | zero => exact (natEmbed_zero_ne_succ m h.symm).elim
      | succ n =>
          injection constructorValue_args h with head _
          exact congrArg Nat.succ (ih head)

theorem embed_pair_eq {p : ZFSet.{u} × ZFSet.{u}} {m n m' n' : Nat}
    (left : p = (natEmbed m, natEmbed n)) (right : p = (natEmbed m', natEmbed n')) :
    m = m' ∧ n = n' := by
  have eqv := left.symm.trans right
  exact ⟨natEmbed_injective (congrArg Prod.fst eqv), natEmbed_injective (congrArg Prod.snd eqv)⟩

/-! ## Half -/

theorem twoProof (n : Nat) {x : ZFSet.{u}} (eq : x = natEmbed (n + 2)) :
    SubPlus natSignature (natEmbed n) x :=
  eq.symm ▸ subPlus_embed_two n

def halfPred (x : ZFSet.{u})
    (rec : (y : ZFSet.{u}) → SubPlus natSignature y x → ZFSet.{u}) (result : ZFSet.{u}) : Prop :=
  (x = natEmbed 0 → result = natEmbed 0) ∧
    (x = natEmbed 1 → result = natEmbed 0) ∧
      ∀ n, (eq : x = natEmbed (n + 2)) →
        result = constructorValue (numeral 1) [rec (natEmbed n) (twoProof n eq)]

theorem halfPred_exists (x : ZFSet.{u})
    (rec : (y : ZFSet.{u}) → SubPlus natSignature y x → ZFSet.{u}) :
    ∃ result, halfPred x rec result := by
  if member : x ∈ carrier natSignature then
    obtain ⟨k, hk⟩ := exists_natEmbed member
    cases k with
    | zero =>
        refine ⟨natEmbed 0, ?_, ?_, ?_⟩
        · intro _; rfl
        · intro _; rfl
        · intro n eq
          exfalso
          exact Nat.succ_ne_zero (n + 1) (natEmbed_injective (hk.trans eq)).symm
    | succ k =>
        cases k with
        | zero =>
            refine ⟨natEmbed 0, ?_, ?_, ?_⟩
            · intro _; rfl
            · intro _; rfl
            · intro n eq
              exfalso
              exact Nat.succ_ne_zero n
                (Nat.succ.inj (natEmbed_injective (hk.trans eq))).symm
        | succ k =>
            refine ⟨constructorValue (numeral 1) [rec (natEmbed k) (twoProof k hk.symm)],
              ?_, ?_, ?_⟩
            · intro h
              exfalso
              exact Nat.succ_ne_zero (k + 1) (natEmbed_injective (hk.trans h))
            · intro h
              exfalso
              exact Nat.succ_ne_zero k (Nat.succ.inj (natEmbed_injective (hk.trans h)))
            · intro n eq
              have nk : n + 2 = k + 2 := natEmbed_injective (eq.symm.trans hk.symm)
              have nk' : n = k := Nat.succ.inj (Nat.succ.inj nk)
              cases nk'
              rfl
  else
    refine ⟨∅, ?_, ?_, ?_⟩
    · intro h
      exfalso
      exact member (h.symm ▸ natEmbed_mem 0)
    · intro h
      exfalso
      exact member (h.symm ▸ natEmbed_mem 1)
    · intro n h
      exfalso
      exact member (h.symm ▸ natEmbed_mem (n + 2))

noncomputable def halfStep (x : ZFSet.{u})
    (rec : (y : ZFSet.{u}) → SubPlus natSignature y x → ZFSet.{u}) : ZFSet.{u} :=
  @Classical.epsilon ZFSet.{u} ⟨∅⟩ (halfPred x rec)

theorem halfStep_spec (x : ZFSet.{u})
    (rec : (y : ZFSet.{u}) → SubPlus natSignature y x → ZFSet.{u}) :
    halfPred x rec (halfStep x rec) :=
  Classical.epsilon_spec_aux ⟨(∅ : ZFSet.{u})⟩ (halfPred x rec) (halfPred_exists x rec)

noncomputable def half : ZFSet.{u} → ZFSet.{u} :=
  subRec halfStep

theorem half_zero : half (natEmbed 0) = natEmbed 0 := by
  rw [half, subRec_eq]
  exact (halfStep_spec (natEmbed 0) (fun y _ => half y)).1 rfl

theorem half_one : half (natEmbed 1) = natEmbed 0 := by
  rw [half, subRec_eq]
  exact (halfStep_spec (natEmbed 1) (fun y _ => half y)).2.1 rfl

theorem half_succ_succ (n : Nat) :
    half (natEmbed (n + 2)) = constructorValue (numeral 1) [half (natEmbed n)] := by
  rw [half, subRec_eq]
  exact (halfStep_spec (natEmbed (n + 2)) (fun y _ => half y)).2.2 n rfl

theorem half_double (n : Nat) : half (natEmbed (2 * n)) = natEmbed n := by
  induction n with
  | zero =>
      rw [Nat.mul_zero, half_zero]
  | succ n ih =>
      have step : 2 * (n + 1) = (2 * n + 1) + 1 := by
        rw [Nat.mul_succ]
      rw [step, half_succ_succ, ih]
      rfl

/-! ## The Ackermann function -/

theorem ackZeroProof (m : Nat) {p : ZFSet.{u} × ZFSet.{u}}
    (eq : p = (natEmbed (m + 1), natEmbed 0)) :
    Prod.Lex (SubPlus natSignature) (SubPlus natSignature) (natEmbed m, natEmbed 1) p :=
  eq.symm ▸ Prod.Lex.left (natEmbed 1) (natEmbed 0) (subPlus_embed_one m)

theorem ackRightProof (m n : Nat) {p : ZFSet.{u} × ZFSet.{u}}
    (eq : p = (natEmbed (m + 1), natEmbed (n + 1))) :
    Prod.Lex (SubPlus natSignature) (SubPlus natSignature)
      (natEmbed (m + 1), natEmbed n) p :=
  eq.symm ▸ Prod.Lex.right (natEmbed (m + 1)) (subPlus_embed_one n)

theorem ackLeftProof (m n : Nat) (inner : ZFSet.{u}) {p : ZFSet.{u} × ZFSet.{u}}
    (eq : p = (natEmbed (m + 1), natEmbed (n + 1))) :
    Prod.Lex (SubPlus natSignature) (SubPlus natSignature) (natEmbed m, inner) p :=
  eq.symm ▸ Prod.Lex.left inner (natEmbed (n + 1)) (subPlus_embed_one m)

def ackPred (p : ZFSet.{u} × ZFSet.{u})
    (rec : (q : ZFSet.{u} × ZFSet.{u}) →
      Prod.Lex (SubPlus natSignature) (SubPlus natSignature) q p → ZFSet.{u})
    (result : ZFSet.{u}) : Prop :=
  (∀ n, p = (natEmbed 0, natEmbed n) → result = natEmbed (n + 1)) ∧
    (∀ m, (eq : p = (natEmbed (m + 1), natEmbed 0)) →
      result = rec (natEmbed m, natEmbed 1) (ackZeroProof m eq)) ∧
      ∀ m n, (eq : p = (natEmbed (m + 1), natEmbed (n + 1))) →
        result =
          rec (natEmbed m, rec (natEmbed (m + 1), natEmbed n) (ackRightProof m n eq))
            (ackLeftProof m n
              (rec (natEmbed (m + 1), natEmbed n) (ackRightProof m n eq)) eq)

theorem ackPred_exists (p : ZFSet.{u} × ZFSet.{u})
    (rec : (q : ZFSet.{u} × ZFSet.{u}) →
      Prod.Lex (SubPlus natSignature) (SubPlus natSignature) q p → ZFSet.{u}) :
    ∃ result, ackPred p rec result := by
  if h1 : p.1 ∈ carrier natSignature then
    obtain ⟨m, hm⟩ := exists_natEmbed h1
    if h2 : p.2 ∈ carrier natSignature then
      obtain ⟨n, hn⟩ := exists_natEmbed h2
      have eqp : p = (natEmbed m, natEmbed n) := Prod.ext hm.symm hn.symm
      cases m with
      | zero =>
          refine ⟨natEmbed (n + 1), ?_, ?_, ?_⟩
          · intro k hk
            have ⟨_, sn⟩ := embed_pair_eq eqp hk
            cases sn
            rfl
          · intro k hk
            have ⟨fm, _⟩ := embed_pair_eq eqp hk
            exfalso
            exact Nat.succ_ne_zero k fm.symm
          · intro k j hk
            have ⟨fm, _⟩ := embed_pair_eq eqp hk
            exfalso
            exact Nat.succ_ne_zero k fm.symm
      | succ m =>
          cases n with
          | zero =>
              refine ⟨rec (natEmbed m, natEmbed 1) (ackZeroProof m eqp), ?_, ?_, ?_⟩
              · intro k hk
                have ⟨fm, _⟩ := embed_pair_eq eqp hk
                exfalso
                exact Nat.succ_ne_zero m fm
              · intro k hk
                have ⟨fm, sn⟩ := embed_pair_eq eqp hk
                have fm' : m = k := Nat.succ.inj fm
                cases fm'
                cases sn
                rfl
              · intro k j hk
                have ⟨_, sn⟩ := embed_pair_eq eqp hk
                exfalso
                exact Nat.succ_ne_zero j sn.symm
          | succ n =>
              let inner := rec (natEmbed (m + 1), natEmbed n) (ackRightProof m n eqp)
              refine ⟨rec (natEmbed m, inner) (ackLeftProof m n inner eqp), ?_, ?_, ?_⟩
              · intro k hk
                have ⟨fm, _⟩ := embed_pair_eq eqp hk
                exfalso
                exact Nat.succ_ne_zero m fm
              · intro k hk
                have ⟨_, sn⟩ := embed_pair_eq eqp hk
                exfalso
                exact Nat.succ_ne_zero n sn
              · intro k j hk
                have ⟨fm, sn⟩ := embed_pair_eq eqp hk
                have fm' : m = k := Nat.succ.inj fm
                have sn' : n = j := Nat.succ.inj sn
                cases fm'
                cases sn'
                rfl
    else
      refine ⟨∅, ?_, ?_, ?_⟩
      · intro k hk
        exfalso
        exact h2 ((congrArg Prod.snd hk).symm ▸ natEmbed_mem k)
      · intro k hk
        exfalso
        exact h2 ((congrArg Prod.snd hk).symm ▸ natEmbed_mem 0)
      · intro k j hk
        exfalso
        exact h2 ((congrArg Prod.snd hk).symm ▸ natEmbed_mem (j + 1))
  else
    refine ⟨∅, ?_, ?_, ?_⟩
    · intro k hk
      exfalso
      exact h1 ((congrArg Prod.fst hk).symm ▸ natEmbed_mem 0)
    · intro k hk
      exfalso
      exact h1 ((congrArg Prod.fst hk).symm ▸ natEmbed_mem (k + 1))
    · intro k j hk
      exfalso
      exact h1 ((congrArg Prod.fst hk).symm ▸ natEmbed_mem (k + 1))

noncomputable def ackStep (p : ZFSet.{u} × ZFSet.{u})
    (rec : (q : ZFSet.{u} × ZFSet.{u}) →
      Prod.Lex (SubPlus natSignature) (SubPlus natSignature) q p → ZFSet.{u}) : ZFSet.{u} :=
  @Classical.epsilon ZFSet.{u} ⟨∅⟩ (ackPred p rec)

theorem ackStep_spec (p : ZFSet.{u} × ZFSet.{u})
    (rec : (q : ZFSet.{u} × ZFSet.{u}) →
      Prod.Lex (SubPlus natSignature) (SubPlus natSignature) q p → ZFSet.{u}) :
    ackPred p rec (ackStep p rec) :=
  Classical.epsilon_spec_aux ⟨(∅ : ZFSet.{u})⟩ (ackPred p rec) (ackPred_exists p rec)

noncomputable def ack : ZFSet.{u} × ZFSet.{u} → ZFSet.{u} :=
  lexRec ackStep

theorem ack_zero (n : Nat) : ack (natEmbed 0, natEmbed n) = natEmbed (n + 1) := by
  rw [ack, lexRec_eq]
  exact (ackStep_spec (natEmbed 0, natEmbed n) (fun q _ => ack q)).1 n rfl

theorem ack_succ_zero (m : Nat) :
    ack (natEmbed (m + 1), natEmbed 0) = ack (natEmbed m, natEmbed 1) := by
  rw [ack, lexRec_eq]
  exact (ackStep_spec (natEmbed (m + 1), natEmbed 0) (fun q _ => ack q)).2.1 m rfl

theorem ack_succ_succ (m n : Nat) :
    ack (natEmbed (m + 1), natEmbed (n + 1)) =
      ack (natEmbed m, ack (natEmbed (m + 1), natEmbed n)) := by
  rw [ack, lexRec_eq]
  exact (ackStep_spec (natEmbed (m + 1), natEmbed (n + 1)) (fun q _ => ack q)).2.2 m n rfl

/-! ## Addition with an accumulator -/

theorem plusOneProof (n : Nat) {x : ZFSet.{u}} (eq : x = natEmbed (n + 1)) :
    SubPlus natSignature (natEmbed n) x :=
  eq.symm ▸ subPlus_embed_one n

def plusPred (x : ZFSet.{u})
    (rec : (y : ZFSet.{u}) → SubPlus natSignature y x → ZFSet.{u} → ZFSet.{u})
    (a result : ZFSet.{u}) : Prop :=
  (x = natEmbed 0 → result = a) ∧
    ∀ n, (eq : x = natEmbed (n + 1)) →
      result = rec (natEmbed n) (plusOneProof n eq) (constructorValue (numeral 1) [a])

theorem plusPred_exists (x : ZFSet.{u})
    (rec : (y : ZFSet.{u}) → SubPlus natSignature y x → ZFSet.{u} → ZFSet.{u})
    (a : ZFSet.{u}) : ∃ result, plusPred x rec a result := by
  if member : x ∈ carrier natSignature then
    obtain ⟨k, hk⟩ := exists_natEmbed member
    cases k with
    | zero =>
        refine ⟨a, ?_, ?_⟩
        · intro _; rfl
        · intro n eq
          exfalso
          exact Nat.succ_ne_zero n (natEmbed_injective (hk.trans eq)).symm
    | succ k =>
        refine ⟨rec (natEmbed k) (plusOneProof k hk.symm) (constructorValue (numeral 1) [a]),
          ?_, ?_⟩
        · intro h
          exfalso
          exact Nat.succ_ne_zero k (natEmbed_injective (hk.trans h))
        · intro n eq
          have nk : n = k := Nat.succ.inj (natEmbed_injective (eq.symm.trans hk.symm))
          cases nk
          rfl
  else
    refine ⟨∅, ?_, ?_⟩
    · intro h
      exfalso
      exact member (h.symm ▸ natEmbed_mem 0)
    · intro n h
      exfalso
      exact member (h.symm ▸ natEmbed_mem (n + 1))

noncomputable def plusAt (x : ZFSet.{u})
    (rec : (y : ZFSet.{u}) → SubPlus natSignature y x → ZFSet.{u} → ZFSet.{u})
    (a : ZFSet.{u}) : ZFSet.{u} :=
  @Classical.epsilon ZFSet.{u} ⟨∅⟩ (plusPred x rec a)

theorem plusAt_spec (x : ZFSet.{u})
    (rec : (y : ZFSet.{u}) → SubPlus natSignature y x → ZFSet.{u} → ZFSet.{u})
    (a : ZFSet.{u}) : plusPred x rec a (plusAt x rec a) :=
  Classical.epsilon_spec_aux ⟨(∅ : ZFSet.{u})⟩ (plusPred x rec a) (plusPred_exists x rec a)

/-- Addition with an accumulator. The motive is `ZFSet → ZFSet`: the accumulator is a
parameter, and the recursive call is at the predecessor of the first argument. The
new accumulator is the successor of the old one, so the second argument grows and is
not a subterm of the old accumulator. -/
noncomputable def plus (x : ZFSet.{u}) : ZFSet.{u} → ZFSet.{u} :=
  WellFounded.fix (subPlus_wf natSignature) plusAt x

theorem plus_zero (a : ZFSet.{u}) : plus (natEmbed 0) a = a := by
  rw [plus, WellFounded.fix_eq]
  exact (plusAt_spec (natEmbed 0) (fun y _ => plus y) a).1 rfl

theorem plus_succ (n : Nat) (a : ZFSet.{u}) :
    plus (natEmbed (n + 1)) a = plus (natEmbed n) (constructorValue (numeral 1) [a]) := by
  rw [plus, WellFounded.fix_eq]
  exact (plusAt_spec (natEmbed (n + 1)) (fun y _ => plus y) a).2 n rfl

theorem not_subPlus_successor (a : ZFSet.{u}) :
    ¬ SubPlus natSignature (constructorValue (numeral 1) [a]) a := by
  intro related
  exact absurd ((subPlus_rank_lt related).trans (arg_rank_lt_constructor (numeral 1) a []))
    (lt_irrefl _)

theorem plus_natEmbed (m n : Nat) : plus (natEmbed m) (natEmbed n) = natEmbed (m + n) := by
  induction m generalizing n with
  | zero =>
      rw [Nat.zero_add, plus_zero]
  | succ m ih =>
      have embedStep : constructorValue (numeral 1) [natEmbed n] = natEmbed (n + 1) := rfl
      rw [plus_succ, embedStep, ih]
      exact congrArg natEmbed ((Nat.add_succ m n).trans (Nat.succ_add m n).symm)

/-! ## Equations without a descent -/

theorem no_self_successor (x : ZFSet.{u}) : x ≠ constructorValue (numeral 1) [x] := by
  intro eq
  have hlt := arg_rank_lt_constructor (numeral 1) x []
  rw [← eq] at hlt
  exact absurd hlt (lt_irrefl _)

theorem no_self_successor_function :
    ¬ ∃ g : ZFSet.{u} → ZFSet.{u}, ∃ x : ZFSet.{u}, g x = constructorValue (numeral 1) [g x] := by
  intro ⟨g, x, h⟩
  exact no_self_successor (g x) h

/-- The equation `g (suc x) = g (suc (suc x))` refers to a strictly larger set. -/
theorem not_subPlus_embed_skip (n : Nat) :
    ¬ SubPlus natSignature (natEmbed (n + 2)) (natEmbed (n + 1)) := by
  intro related
  exact absurd
    ((subPlus_rank_lt related).trans (sub_rank_lt (sub_embed_succ (n + 1)))) (lt_irrefl _)

def solutionConst : ZFSet.{u} → ZFSet.{u} :=
  fun _ => natEmbed 0

noncomputable def solutionAlt (x : ZFSet.{u}) : ZFSet.{u} :=
  if member : x ∈ carrier natSignature then
    if (inversionOf member).index = 0 then natEmbed 0 else natEmbed 1
  else
    natEmbed 0

theorem solutionAlt_zero : solutionAlt (natEmbed 0) = natEmbed 0 := by
  rw [solutionAlt, dif_pos (natEmbed_mem 0),
    if_pos (inversionOf_spec natSignature_distinct (natEmbed_mem 0) (i := 0)
      (c := ⟨numeral 0, []⟩) rfl Fits.nil rfl).1]

theorem solutionAlt_successor (x : ZFSet.{u}) (member : x ∈ carrier natSignature) :
    solutionAlt (constructorValue (numeral 1) [x]) = natEmbed 1 := by
  have inCarrier := constructor_mem_carrier (sig := natSignature) (i := 1)
    (c := ⟨numeral 1, [Field.recursive]⟩) rfl (Fits.recursive member Fits.nil)
  have indexOne := (inversionOf_spec natSignature_distinct (i := 1)
    (c := ⟨numeral 1, [Field.recursive]⟩) inCarrier rfl (Fits.recursive member Fits.nil) rfl).1
  rw [solutionAlt, dif_pos inCarrier, if_neg (by rw [indexOne]; decide)]

theorem solutionAlt_shift (x : ZFSet.{u}) (member : x ∈ carrier natSignature) :
    solutionAlt (constructorValue (numeral 1) [x]) =
      solutionAlt (constructorValue (numeral 1) [constructorValue (numeral 1) [x]]) := by
  rw [solutionAlt_successor x member,
    solutionAlt_successor (constructorValue (numeral 1) [x])
      (constructor_mem_carrier (sig := natSignature) (i := 1)
        (c := ⟨numeral 1, [Field.recursive]⟩) rfl (Fits.recursive member Fits.nil))]

theorem solution_differ : solutionConst (natEmbed 1) ≠ solutionAlt (natEmbed 1) := by
  have asSucc : natEmbed 1 = constructorValue (numeral 1) [natEmbed 0] := rfl
  rw [solutionConst, asSucc, solutionAlt_successor (natEmbed 0) (natEmbed_mem 0)]
  exact natEmbed_zero_ne_succ 0

theorem shift_not_unique :
    ∃ g₁ g₂ : ZFSet.{u} → ZFSet.{u},
      g₁ (natEmbed 0) = natEmbed 0 ∧
      g₂ (natEmbed 0) = natEmbed 0 ∧
      (∀ x, x ∈ carrier natSignature →
        g₁ (constructorValue (numeral 1) [x]) =
          g₁ (constructorValue (numeral 1) [constructorValue (numeral 1) [x]])) ∧
      (∀ x, x ∈ carrier natSignature →
        g₂ (constructorValue (numeral 1) [x]) =
          g₂ (constructorValue (numeral 1) [constructorValue (numeral 1) [x]])) ∧
      g₁ (natEmbed 1) ≠ g₂ (natEmbed 1) :=
  ⟨solutionConst, solutionAlt, rfl, solutionAlt_zero,
    fun _ _ => rfl, solutionAlt_shift, solution_differ⟩

#print axioms sub_wf
#print axioms subPlus_wf
#print axioms subPlus_left_mem
#print axioms sub_outside
#print axioms subRec_eq
#print axioms subRec_unique
#print axioms subRec_recFun
#print axioms lexRec_eq
#print axioms lexRec_unique
#print axioms lexRec_unique_all
#print axioms subRec_mem
#print axioms subRec_trace_mem
#print axioms subRec_trace_app
#print axioms lexRec_mem
#print axioms lexTrace_mem
#print axioms lexTrace_app
#print axioms half_zero
#print axioms half_one
#print axioms half_succ_succ
#print axioms half_double
#print axioms ack_zero
#print axioms ack_succ_zero
#print axioms ack_succ_succ
#print axioms plus_zero
#print axioms plus_succ
#print axioms plus_natEmbed
#print axioms not_subPlus_successor
#print axioms no_self_successor_function
#print axioms not_subPlus_embed_skip
#print axioms shift_not_unique
#print axioms sub_mem_prev

end Mettapedia.Logic.HOL.Embedding.ZFSetInductiveRecursion
