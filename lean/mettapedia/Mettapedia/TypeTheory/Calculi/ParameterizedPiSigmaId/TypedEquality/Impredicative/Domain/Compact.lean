import Mathlib.Data.List.Basic
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

/-!
# Compact elements of the domain model

The domain of the model of Carneiro, Coquand, Frabetti Mathieu, Lennon-Bertrand,
Melliès and Weirich, *Definitional Inversion, Without Normalisation*, solves an
equation `D ≅ [D ⇒ D] + ↑(D × [D ⇒ D]) + ↑1 + …` whose summands are the
functions, the dependent function types and the universe, extended here with
dependent pair types and pairs, identity types and reflexivity, the numbers,
a universe of codes, ground types, and a type former for each declared datatype
and a constructor for each declared constructor, named as the constants of the
terms are. The domain is determined by its compact
elements, and the compact elements are presented here as the finite sets of an
information system (Scott; Larsen and Winskel): a *token* is one finite
observation of an element, and a compact element is a finite list of tokens,
the join of its observations.

A token says that an element

* is built by the constructor of kind `k` (`tag k`);
* has a component `i`, of the constructor of kind `k`, entailing a token `t`,
  and a component `0` above `C` (`arg k i C t`);
* maps, as a step function of kind `k`, every element above `X` to an element
  above `Y`, and has a component `0` above `C` (`fn k C X Y`).

The dependency `C` is empty unless the component's type depends on another
component: the family of a dependent type depends on the domain, the endpoints
of an identity type on the carrier, and the second projection of a pair on the
first. Carrying it on the token makes typing a property of single tokens.

Entailment `ent v t` decides whether the list `v` entails the token `t`; it is
defined by well-founded recursion on the depth of the tokens involved. The
order `u ⊑ v` on compact elements is entailment of every token of `u` by `v`;
it is a preorder (`Le.refl`, `Le.trans`, the latter from cut), and the join of
two compact elements is their concatenation.

**Tokens over any kinds.** Selections, entailment, the order and cut never
inspect a kind except to compare it with another, so they are stated once over
any type of kinds `κ` with decidable equality (`Tok κ`). The kinds of the domain
(`Kind`) are the default: `Tok` alone is `Tok Kind`, and every statement about
the domain's tokens is the general one at `Kind`, the type of kinds found by
unification. Other types of kinds, such as one with a kind for each declared
constructor, reuse the same construction.

**Declared datatypes.** Beside the built-in numbers (`nat`, `zero`, `succ`), each
declared datatype `d` is a kind of its own (`data d`), whose components are its
parameters, and so is each constructor `c` of it (`ctor d c fs`), named as the
constants of the terms are; the constructor's kind also records the shape of each of
its fields (`FieldShape`): the datatype itself, or one of its parameters. So
constructors keep their identity: a tag of one constructor is never entailed by tokens
of another, and a constructor element carries its tag even with no field or with least
fields.

Two kinds are *lazy*: a function or a pair with no observations is the least
element, since only its applications and projections can be observed. Every
other constructor carries a tag, which is itself an observation: `Π ⊥ ⊥` and
`S ⊥` are above `⊥` and different from it, while `λ ⊥` and `(⊥, ⊥)` are `⊥`.
This is what validates the η-laws of functions and pairs.

Examples. Positive: a list entails each of its tokens (`ent_of_mem`), the
successor of an element is below a list exactly when the list has the successor
tag and the element is below its predecessor (`Elem.succ_le_iff`), and the
predecessor of a successor is the element (`Elem.pred_succ`). Negative: a tag is
entailed only by a list that has it (`hasTag_iff`), so zero, `[tag zero]`, is not
below the least element `[]` nor below a successor, and the declared constructor
`nil` of the lists, `[tag (ctor list nil [])]`, is not below
`[tag (ctor list cons [param 0, self])]`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Domain

/-! ## Tokens -/

/-- Equality of declared names, decided by their structure; unlike the instance of the core
library, the decision uses no axiom, and the kinds of the domain decide their equality by it. -/
def declNameDecEq : (a b : DeclName) → Decidable (a = b)
  | .anonymous, .anonymous => isTrue rfl
  | .str p s, .str q t =>
      match declNameDecEq p q, decEq s t with
      | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
      | isFalse h₁, _ => isFalse fun h => h₁ (by injection h)
      | _, isFalse h₂ => isFalse fun h => h₂ (by injection h)
  | .num p m, .num q n =>
      match declNameDecEq p q, decEq m n with
      | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
      | isFalse h₁, _ => isFalse fun h => h₁ (by injection h)
      | _, isFalse h₂ => isFalse fun h => h₂ (by injection h)
  | .anonymous, .str .. | .anonymous, .num .. | .str .., .anonymous | .str .., .num ..
  | .num .., .anonymous | .num .., .str .. => isFalse nofun

/-- The shape of a field of a declared constructor: the datatype itself (a recursive field), or
the parameter `j` of the datatype (a field whose type is given beside the datatype). -/
inductive FieldShape where
  /-- The datatype being declared. -/
  | self
  /-- The parameter `j` of the datatype. -/
  | param (j : Nat)
  deriving DecidableEq, Repr

section KindDecidableEq

local instance : DecidableEq DeclName := declNameDecEq

/-- The constructors of the domain. -/
inductive Kind where
  /-- The universe of all types. -/
  | univ
  /-- A ground type, whose only element is the least one. -/
  | ground
  /-- A universe of codes, whose elements are types. -/
  | codes
  /-- The type of numbers. -/
  | nat
  /-- The number zero. -/
  | zero
  /-- A successor. -/
  | succ
  /-- A dependent function type: a domain and a family. -/
  | pi
  /-- A dependent pair type: a domain and a family. -/
  | sigma
  /-- An identity type: a carrier and two endpoints. -/
  | ident
  /-- Reflexivity, with its point. -/
  | refl
  /-- A function, observed only through its applications. -/
  | lam
  /-- A pair, observed only through its projections. -/
  | pair
  /-- The declared datatype `d`, a type former whose components are its parameters. -/
  | data (d : DeclName)
  /-- The constructor `c` of the declared datatype `d`, whose components are its fields, each
  of the shape `fields` gives it. -/
  | ctor (d c : DeclName) (fields : List FieldShape)
  deriving DecidableEq, Repr

end KindDecidableEq

/-- The finite observations of elements, over a type `κ` of kinds; the kinds of the domain
unless another type is given. -/
inductive Tok (κ : Type := Kind) where
  /-- The element is built by the constructor of kind `k`. -/
  | tag (k : κ)
  /-- The component `i` of the element entails `t`, and its component `0` is above `C`. -/
  | arg (k : κ) (i : Nat) (C : List (Tok κ)) (t : Tok κ)
  /-- As a step function of kind `k`, the element maps every element above `X` to an element
  above `Y`, and its component `0` is above `C`. -/
  | fn (k : κ) (C X Y : List (Tok κ))
  deriving Repr

variable {κ : Type}

/-- The kind of a token. -/
def Tok.kind : Tok κ → κ
  | .tag k => k
  | .arg k _ _ _ => k
  | .fn k _ _ _ => k

/-- The dependency of a token: what it asserts of the component `0`. -/
def Tok.dep : Tok κ → List (Tok κ)
  | .tag _ => []
  | .arg _ _ C _ => C
  | .fn _ C _ _ => C

mutual
/-- The nesting depth of a token. -/
def Tok.depth : Tok κ → Nat
  | .tag _ => 0
  | .arg _ _ C t => max (Tok.depthL C) t.depth + 1
  | .fn _ C X Y => max (Tok.depthL C) (max (Tok.depthL X) (Tok.depthL Y)) + 1
/-- The largest depth of the tokens of a list. -/
def Tok.depthL : List (Tok κ) → Nat
  | [] => 0
  | t :: ts => max t.depth (Tok.depthL ts)
end

theorem Tok.depth_le_of_mem {t : Tok κ} {v : List (Tok κ)} (h : t ∈ v) :
    t.depth ≤ Tok.depthL v := by
  induction v with
  | nil => cases h
  | cons s v ih =>
    simp only [Tok.depthL]
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem Tok.depthL_le {v : List (Tok κ)} {n : Nat} (h : ∀ t ∈ v, t.depth ≤ n) :
    Tok.depthL v ≤ n := by
  induction v with
  | nil => exact Nat.zero_le _
  | cons s v ih =>
    simp only [Tok.depthL]
    exact Nat.max_le.2 ⟨h s (by simp), ih fun t ht => h t (by simp [ht])⟩

theorem Tok.depth_lt_of_mem_dep {t s : Tok κ} (h : s ∈ t.dep) : s.depth < t.depth := by
  cases t with
  | tag => cases h
  | arg k i C t =>
    change s ∈ C at h
    have := Tok.depth_le_of_mem h
    have := Nat.le_max_left (Tok.depthL C) t.depth
    simp only [Tok.depth]; omega
  | fn k C X Y =>
    change s ∈ C at h
    have := Tok.depth_le_of_mem h
    have := Nat.le_max_left (Tok.depthL C) (max (Tok.depthL X) (Tok.depthL Y))
    simp only [Tok.depth]; omega

theorem depth_lt_arg (k : κ) (i : Nat) (C : List (Tok κ)) (t : Tok κ) :
    t.depth < (Tok.arg k i C t).depth := by
  have := Nat.le_max_right (Tok.depthL C) t.depth
  simp only [Tok.depth]; omega

theorem depth_lt_fn_left {k : κ} {C X Y : List (Tok κ)} {s : Tok κ} (h : s ∈ X) :
    s.depth < (Tok.fn k C X Y).depth := by
  have := Tok.depth_le_of_mem h
  have := Nat.le_max_left (Tok.depthL X) (Tok.depthL Y)
  have := Nat.le_max_right (Tok.depthL C) (max (Tok.depthL X) (Tok.depthL Y))
  simp only [Tok.depth]; omega

theorem depth_lt_fn_right {k : κ} {C X Y : List (Tok κ)} {s : Tok κ} (h : s ∈ Y) :
    s.depth < (Tok.fn k C X Y).depth := by
  have := Tok.depth_le_of_mem h
  have := Nat.le_max_right (Tok.depthL X) (Tok.depthL Y)
  have := Nat.le_max_right (Tok.depthL C) (max (Tok.depthL X) (Tok.depthL Y))
  simp only [Tok.depth]; omega

theorem depthL_lt_fn_left (k : κ) (C X Y : List (Tok κ)) :
    Tok.depthL X < (Tok.fn k C X Y).depth := by
  have := Nat.le_max_left (Tok.depthL X) (Tok.depthL Y)
  have := Nat.le_max_right (Tok.depthL C) (max (Tok.depthL X) (Tok.depthL Y))
  simp only [Tok.depth]; omega

theorem depthL_lt_of_fn_mem {k : κ} {v C X Y : List (Tok κ)} (h : Tok.fn k C X Y ∈ v) :
    Tok.depthL X < Tok.depthL v :=
  Nat.lt_of_lt_of_le (depthL_lt_fn_left k C X Y) (Tok.depth_le_of_mem h)

/-! ## Selections -/

section Entailment

variable [DecidableEq κ]

/-- Whether a list has the tag of kind `k`. -/
def hasTag (k : κ) : List (Tok κ) → Bool
  | [] => false
  | .tag k' :: v => k' == k || hasTag k v
  | _ :: v => hasTag k v

/-- The component `i` of kind `k`: the tokens its component tokens entail, and,
for the component `0`, the dependencies of all its tokens of kind `k`. -/
def args (k : κ) (i : Nat) : List (Tok κ) → List (Tok κ)
  | [] => []
  | t :: v =>
      ((match t with
        | .arg k' i' _ s => if k' = k ∧ i' = i then [s] else []
        | _ => []) ++
      (if t.kind = k ∧ i = 0 then t.dep else [])) ++ args k i v

/-- The entries of the step function of kind `k`. -/
def fns (k : κ) : List (Tok κ) → List (List (Tok κ) × List (Tok κ))
  | [] => []
  | .fn k' _ X Y :: v => if k' = k then (X, Y) :: fns k v else fns k v
  | _ :: v => fns k v

theorem hasTag_iff {k : κ} {v : List (Tok κ)} : hasTag k v = true ↔ Tok.tag k ∈ v := by
  induction v with
  | nil => simp [hasTag]
  | cons t v ih =>
    cases t with
    | tag k' =>
      simp only [hasTag, Bool.or_eq_true, beq_iff_eq, ih, List.mem_cons, Tok.tag.injEq]
      exact or_congr_left eq_comm
    | arg => simp [hasTag, ih]
    | fn => simp [hasTag, ih]

theorem mem_args_iff {k : κ} {i : Nat} {v : List (Tok κ)} {s : Tok κ} :
    s ∈ args k i v ↔
      (∃ C, Tok.arg k i C s ∈ v) ∨ (i = 0 ∧ ∃ t ∈ v, t.kind = k ∧ s ∈ t.dep) := by
  induction v with
  | nil => simp [args]
  | cons t v ih =>
    simp only [args, List.mem_append, ih, List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · cases t with
        | tag => cases h
        | fn => cases h
        | arg k' i' C' s' =>
          simp only at h
          split at h
          · rename_i hk
            obtain ⟨rfl, rfl⟩ := hk
            obtain rfl := List.mem_singleton.1 h
            exact .inl ⟨C', .inl rfl⟩
          · cases h
      · split at h
        · rename_i hk
          exact .inr ⟨hk.2, t, .inl rfl, hk.1, h⟩
        · cases h
      · rcases h with ⟨C, hC⟩ | ⟨hi, t', ht', hk, hs⟩
        · exact .inl ⟨C, .inr hC⟩
        · exact .inr ⟨hi, t', .inr ht', hk, hs⟩
    · rintro (⟨C, rfl | hC⟩ | ⟨hi, t', rfl | ht', hk, hs⟩)
      · left; left; simp
      · right; exact .inl ⟨C, hC⟩
      · left; right; rw [if_pos ⟨hk, hi⟩]; exact hs
      · right; exact .inr ⟨hi, t', ht', hk, hs⟩

theorem mem_fns_iff {k : κ} {v : List (Tok κ)} {X Y : List (Tok κ)} :
    (X, Y) ∈ fns k v ↔ ∃ C, Tok.fn k C X Y ∈ v := by
  induction v with
  | nil => simp [fns]
  | cons s v ih =>
    cases s with
    | tag => simp [fns, ih]
    | arg => simp [fns, ih]
    | fn k' C' X' Y' =>
      simp only [fns]
      split
      · rename_i hk
        subst hk
        simp only [List.mem_cons, Prod.mk.injEq, ih, Tok.fn.injEq, true_and]
        constructor
        · rintro (⟨rfl, rfl⟩ | ⟨C, hC⟩)
          · exact ⟨C', .inl ⟨rfl, rfl, rfl⟩⟩
          · exact ⟨C, .inr hC⟩
        · rintro ⟨C, ⟨-, rfl, rfl⟩ | hC⟩
          · exact .inl ⟨rfl, rfl⟩
          · exact .inr ⟨C, hC⟩
      · rename_i hk
        simp only [List.mem_cons, ih, Tok.fn.injEq]
        constructor
        · rintro ⟨C, hC⟩; exact ⟨C, .inr hC⟩
        · rintro ⟨C, ⟨rfl, -, -, -⟩ | hC⟩
          · exact absurd rfl hk
          · exact ⟨C, hC⟩

theorem mem_args_of_arg {k : κ} {i : Nat} {C : List (Tok κ)} {s : Tok κ} {v : List (Tok κ)}
    (h : Tok.arg k i C s ∈ v) : s ∈ args k i v :=
  mem_args_iff.2 (.inl ⟨C, h⟩)

theorem mem_args_of_dep {k : κ} {t s : Tok κ} {v : List (Tok κ)} (ht : t ∈ v) (hk : t.kind = k)
    (hs : s ∈ t.dep) : s ∈ args k 0 v :=
  mem_args_iff.2 (.inr ⟨rfl, t, ht, hk, hs⟩)

theorem args_subset {k : κ} {i : Nat} {v w : List (Tok κ)} (h : ∀ s ∈ v, s ∈ w) :
    ∀ s ∈ args k i v, s ∈ args k i w := by
  intro s hs
  rcases mem_args_iff.1 hs with ⟨C, hC⟩ | ⟨hi, t, ht, hk, hs⟩
  · exact mem_args_iff.2 (.inl ⟨C, h _ hC⟩)
  · exact mem_args_iff.2 (.inr ⟨hi, t, h _ ht, hk, hs⟩)

theorem fns_subset {k : κ} {v w : List (Tok κ)} (h : ∀ s ∈ v, s ∈ w) :
    ∀ p ∈ fns k v, p ∈ fns k w := by
  rintro ⟨X, Y⟩ hp
  obtain ⟨C, hC⟩ := mem_fns_iff.1 hp
  exact mem_fns_iff.2 ⟨C, h _ hC⟩

theorem args_append (k : κ) (i : Nat) (u v : List (Tok κ)) :
    args k i (u ++ v) = args k i u ++ args k i v := by
  induction u with
  | nil => rfl
  | cons s u ih => simp only [List.cons_append, args, ih, List.append_assoc]

theorem fns_append (k : κ) (u v : List (Tok κ)) : fns k (u ++ v) = fns k u ++ fns k v := by
  induction u with
  | nil => rfl
  | cons s u ih =>
    cases s with
    | tag => exact ih
    | arg => exact ih
    | fn k' C X Y =>
      simp only [List.cons_append, fns]
      split <;> simp [ih]

/-! ## Depth bounds -/

theorem depthL_args (k : κ) (i : Nat) (v : List (Tok κ)) :
    Tok.depthL (args k i v) ≤ Tok.depthL v := by
  apply Tok.depthL_le
  intro s hs
  rcases mem_args_iff.1 hs with ⟨C, hC⟩ | ⟨-, t, ht, -, hs⟩
  · have h1 := Tok.depth_le_of_mem hC
    have h2 := Nat.le_max_right (Tok.depthL C) s.depth
    simp only [Tok.depth] at h1
    omega
  · have h1 := Tok.depth_le_of_mem ht
    have h2 := Tok.depth_lt_of_mem_dep hs
    omega

theorem depth_fn_le {k : κ} {v X Y : List (Tok κ)} (h : (X, Y) ∈ fns k v) :
    max (Tok.depthL X) (Tok.depthL Y) + 1 ≤ Tok.depthL v := by
  obtain ⟨C, hC⟩ := mem_fns_iff.1 h
  have h1 := Tok.depth_le_of_mem hC
  have h2 := Nat.le_max_right (Tok.depthL C) (max (Tok.depthL X) (Tok.depthL Y))
  simp only [Tok.depth] at h1
  omega

theorem depthL_select (k : κ) (v : List (Tok κ)) (P : {p // p ∈ fns k v} → Bool) :
    Tok.depthL (((fns k v).attach.filter P).flatMap fun q => q.1.2) ≤ Tok.depthL v := by
  apply Tok.depthL_le
  intro t ht
  obtain ⟨⟨q, hq⟩, -, ht⟩ := List.mem_flatMap.1 ht
  have h1 := depth_fn_le hq
  have h2 : t.depth ≤ Tok.depthL q.2 := Tok.depth_le_of_mem ht
  have h3 := Nat.le_max_right (Tok.depthL q.1) (Tok.depthL q.2)
  omega

/-! ## Entailment -/

/-- Entailment: whether the list `v` entails the token `t`. A tag is entailed
by its presence; a component token by the component, once its dependency is
entailed by the component `0`; a step-function token by the value at its input
of the step function the list presents, once its dependency is entailed. -/
def ent (v : List (Tok κ)) : Tok κ → Bool
  | .tag k => hasTag k v
  | .arg k i C t => (C.attach.all fun ⟨c, _⟩ => ent (args k 0 v) c) && ent (args k i v) t
  | .fn k C X Y => (C.attach.all fun ⟨c, _⟩ => ent (args k 0 v) c) &&
      Y.attach.all fun ⟨s, _⟩ =>
        ent (((fns k v).attach.filter fun ⟨p, _⟩ =>
          p.1.attach.all fun ⟨s', _⟩ => ent X s').flatMap (fun q => q.1.2)) s
termination_by t => Tok.depthL v + t.depth
decreasing_by
  · have := depthL_args k 0 v
    have := Tok.depth_lt_of_mem_dep (t := .arg k i C t) ‹c ∈ C›
    omega
  · have := depthL_args k i v
    have := depth_lt_arg k i C t
    omega
  · have := depthL_args k 0 v
    have := Tok.depth_lt_of_mem_dep (t := .fn k C X Y) ‹c ∈ C›
    omega
  · rename_i _ hp hs'
    have h1 := depth_fn_le hp
    have h2 := Tok.depth_le_of_mem hs'
    have h3 := Nat.le_max_left (Tok.depthL p.1) (Tok.depthL p.2)
    have h4 := depthL_lt_fn_left k C X Y
    omega
  · rename_i hs
    refine Nat.lt_of_le_of_lt (Nat.add_le_add_right (depthL_select k v _) _) ?_
    have := depth_lt_fn_right (k := k) (C := C) (X := X) hs
    omega

/-- The value at `X` of the step function of kind `k` that `v` presents: the
outputs of its entries whose inputs are entailed by `X`. -/
def fnApp (k : κ) (v X : List (Tok κ)) : List (Tok κ) :=
  ((fns k v).filter fun p => p.1.all (ent X)).flatMap Prod.snd

private theorem all_attach_val {α : Type} (l : List α) (f : α → Bool) :
    (l.attach.all fun x => f x.1) = l.all f := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, List.mem_attach, forall_const, Subtype.forall]

private theorem flatMap_filter_attach_val {α β : Type} (l : List α) (P : α → Bool)
    (f : α → List β) :
    ((l.attach.filter fun x => P x.1).flatMap fun q => f q.1) = (l.filter P).flatMap f := by
  have h : l.filter P = (l.attach.filter fun x => P x.1).map Subtype.val := by
    conv_lhs => rw [← List.attach_map_subtype_val l]
    rw [List.filter_map]
    rfl
  rw [h, List.flatMap_map]

theorem ent_tag (v : List (Tok κ)) (k : κ) : ent v (.tag k) = hasTag k v := by
  rw [ent]

theorem ent_arg (v : List (Tok κ)) (k : κ) (i : Nat) (C : List (Tok κ)) (t : Tok κ) :
    ent v (.arg k i C t) = (C.all (ent (args k 0 v)) && ent (args k i v) t) := by
  rw [ent]
  simp only [all_attach_val]

theorem ent_fn (v : List (Tok κ)) (k : κ) (C X Y : List (Tok κ)) :
    ent v (.fn k C X Y) = (C.all (ent (args k 0 v)) && Y.all (ent (fnApp k v X))) := by
  rw [ent]
  simp only [all_attach_val]
  rw [flatMap_filter_attach_val (fns k v) (fun p => p.1.all (ent X)) Prod.snd]
  rfl

theorem mem_fnApp {k : κ} {v X : List (Tok κ)} {t : Tok κ} :
    t ∈ fnApp k v X ↔
      ∃ C X' Y', Tok.fn k C X' Y' ∈ v ∧ (∀ s ∈ X', ent X s = true) ∧ t ∈ Y' := by
  simp only [fnApp, List.mem_flatMap, List.mem_filter, List.all_eq_true]
  constructor
  · rintro ⟨⟨X', Y'⟩, ⟨hp, hX⟩, ht⟩
    obtain ⟨C, hC⟩ := mem_fns_iff.1 hp
    exact ⟨C, X', Y', hC, hX, ht⟩
  · rintro ⟨C, X', Y', hp, hX, ht⟩
    exact ⟨(X', Y'), ⟨mem_fns_iff.2 ⟨C, hp⟩, hX⟩, ht⟩

theorem fnApp_subset {k : κ} {v w : List (Tok κ)} (X : List (Tok κ)) (h : ∀ s ∈ v, s ∈ w) :
    ∀ s ∈ fnApp k v X, s ∈ fnApp k w X := by
  intro s hs
  obtain ⟨C, X', Y', hp, hX, hs⟩ := mem_fnApp.1 hs
  exact mem_fnApp.2 ⟨C, X', Y', h _ hp, hX, hs⟩

theorem depthL_fnApp_le (k : κ) (v X : List (Tok κ)) :
    Tok.depthL (fnApp k v X) ≤ Tok.depthL v := by
  apply Tok.depthL_le
  intro t ht
  obtain ⟨C, X', Y', hp, -, ht⟩ := mem_fnApp.1 ht
  have h1 := Tok.depth_le_of_mem hp
  have h2 := depth_lt_fn_right (k := k) (C := C) (X := X') ht
  omega

/-! ## The order -/

/-- `u ⊑ v`: `v` entails every token of `u`. This is the order of the compact
elements, and the join of two compact elements is their concatenation. -/
def Le (u v : List (Tok κ)) : Prop := ∀ t ∈ u, ent v t = true

@[inherit_doc] scoped infix:50 " ⊑ " => Le

/-- Every token of a list is entailed by it. -/
theorem ent_of_mem : ∀ {v : List (Tok κ)} {t : Tok κ}, t ∈ v → ent v t = true
  | _, .tag k, h => by rw [ent_tag, hasTag_iff]; exact h
  | _, .arg k i C t, h => by
      rw [ent_arg, Bool.and_eq_true, List.all_eq_true]
      exact ⟨fun c hc => ent_of_mem (mem_args_of_dep h rfl hc), ent_of_mem (mem_args_of_arg h)⟩
  | _, .fn k C X Y, h => by
      rw [ent_fn, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
      refine ⟨fun c hc => ent_of_mem (mem_args_of_dep h rfl hc), fun s hs => ?_⟩
      exact ent_of_mem (mem_fnApp.2 ⟨C, X, Y, h, fun s' hs' => ent_of_mem hs', hs⟩)
termination_by _ t => t.depth
decreasing_by
  · exact Tok.depth_lt_of_mem_dep (t := .arg k i C t) hc
  · exact depth_lt_arg k i C t
  · exact Tok.depth_lt_of_mem_dep (t := .fn k C X Y) hc
  · exact depth_lt_fn_left hs'
  · exact depth_lt_fn_right hs

/-- Entailment is monotone in the entailing list. -/
theorem ent_mono : ∀ {v w : List (Tok κ)} {t : Tok κ}, (∀ s ∈ v, s ∈ w) →
    ent v t = true → ent w t = true
  | _, _, .tag k, h, e => by
      rw [ent_tag, hasTag_iff] at e ⊢
      exact h _ e
  | _, _, .arg k i C t, h, e => by
      rw [ent_arg, Bool.and_eq_true, List.all_eq_true] at e ⊢
      exact ⟨fun c hc => ent_mono (args_subset h) (e.1 c hc), ent_mono (args_subset h) e.2⟩
  | _, _, .fn k C X Y, h, e => by
      rw [ent_fn, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at e ⊢
      exact ⟨fun c hc => ent_mono (args_subset h) (e.1 c hc),
        fun s hs => ent_mono (fnApp_subset X h) (e.2 s hs)⟩
termination_by _ _ t => t.depth
decreasing_by
  · exact Tok.depth_lt_of_mem_dep (t := .arg k i C t) hc
  · exact depth_lt_arg k i C t
  · exact Tok.depth_lt_of_mem_dep (t := .fn k C X Y) hc
  · exact depth_lt_fn_right hs

theorem Le.refl (u : List (Tok κ)) : u ⊑ u := fun _ ht => ent_of_mem ht

theorem Le.of_subset {u v : List (Tok κ)} (h : ∀ t ∈ u, t ∈ v) : u ⊑ v :=
  fun _ ht => ent_of_mem (h _ ht)

theorem Le.nil (v : List (Tok κ)) : [] ⊑ v := fun _ ht => absurd ht List.not_mem_nil

/-- The components of an element below another are below its components. -/
theorem Le.args {v w : List (Tok κ)} (h : v ⊑ w) (k : κ) (i : Nat) :
    args k i v ⊑ args k i w := by
  intro s hs
  rcases mem_args_iff.1 hs with ⟨C, hC⟩ | ⟨hi, t, ht, hk, hd⟩
  · have := h _ hC
    rw [ent_arg, Bool.and_eq_true] at this
    exact this.2
  · subst hi
    have := h _ ht
    cases t with
    | tag => cases hd
    | arg k' i' C t =>
      change k' = k at hk
      change s ∈ C at hd
      subst hk
      rw [ent_arg, Bool.and_eq_true, List.all_eq_true] at this
      exact this.1 s hd
    | fn k' C X Y =>
      change k' = k at hk
      change s ∈ C at hd
      subst hk
      rw [ent_fn, Bool.and_eq_true, List.all_eq_true] at this
      exact this.1 s hd

/-- **Cut**: entailment is transitive. -/
theorem ent_cut : ∀ {v w : List (Tok κ)} {t : Tok κ}, ent v t = true → v ⊑ w →
    ent w t = true
  | _, _, .tag k, e, h => h _ (hasTag_iff.1 (by rwa [ent_tag] at e))
  | v, w, .arg k i C t, e, h => by
      rw [ent_arg, Bool.and_eq_true, List.all_eq_true] at e ⊢
      exact ⟨fun c hc => ent_cut (e.1 c hc) (h.args k 0), ent_cut e.2 (h.args k i)⟩
  | v, w, .fn k C X Y, e, h => by
      rw [ent_fn, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at e ⊢
      refine ⟨fun c hc => ent_cut (e.1 c hc) (h.args k 0), fun s hs => ?_⟩
      refine ent_cut (e.2 s hs) ?_
      intro s' hs'
      obtain ⟨C', X', Y', hp, hX, hs'⟩ := mem_fnApp.1 hs'
      have hw := h _ hp
      rw [ent_fn, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hw
      refine ent_mono ?_ (hw.2 s' hs')
      intro r hr
      obtain ⟨C'', X'', Y'', hq, hX', hr⟩ := mem_fnApp.1 hr
      exact mem_fnApp.2 ⟨C'', X'', Y'', hq, fun x hx => ent_cut (hX' x hx) hX, hr⟩
termination_by v _ t => (Tok.depthL v, t.depth)
decreasing_by
  all_goals first
    | exact Prod.Lex.left _ _ (depthL_lt_of_fn_mem hp)
    | (rcases Nat.lt_or_eq_of_le (depthL_args k 0 v) with hl | hl
       · exact Prod.Lex.left _ _ hl
       · first
         | (rw [hl]; exact Prod.Lex.right _ (Tok.depth_lt_of_mem_dep (t := .arg k i C t) hc))
         | (rw [hl]; exact Prod.Lex.right _ (Tok.depth_lt_of_mem_dep (t := .fn k C X Y) hc)))
    | (rcases Nat.lt_or_eq_of_le (depthL_args k i v) with hl | hl
       · exact Prod.Lex.left _ _ hl
       · rw [hl]; exact Prod.Lex.right _ (depth_lt_arg k i C t))
    | (rcases Nat.lt_or_eq_of_le (depthL_fnApp_le k v X) with hl | hl
       · exact Prod.Lex.left _ _ hl
       · rw [hl]; exact Prod.Lex.right _ (depth_lt_fn_right hs))

theorem Le.trans {u v w : List (Tok κ)} (h₁ : u ⊑ v) (h₂ : v ⊑ w) : u ⊑ w :=
  fun _ ht => ent_cut (h₁ _ ht) h₂

/-- Equivalent compact elements: each below the other. -/
def Equiv (u v : List (Tok κ)) : Prop := u ⊑ v ∧ v ⊑ u

theorem Equiv.refl (u : List (Tok κ)) : Equiv u u := ⟨Le.refl u, Le.refl u⟩

theorem Equiv.symm {u v : List (Tok κ)} (h : Equiv u v) : Equiv v u := ⟨h.2, h.1⟩

theorem Equiv.trans {u v w : List (Tok κ)} (h₁ : Equiv u v) (h₂ : Equiv v w) : Equiv u w :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

theorem ent_of_le {u v : List (Tok κ)} {t : Tok κ} (h : u ⊑ v) (e : ent u t = true) :
    ent v t = true :=
  ent_cut e h

/-! ## Joins -/

theorem Le.append_left (u v : List (Tok κ)) : u ⊑ u ++ v :=
  Le.of_subset fun _ ht => List.mem_append_left _ ht

theorem Le.append_right (u v : List (Tok κ)) : v ⊑ u ++ v :=
  Le.of_subset fun _ ht => List.mem_append_right _ ht

/-- The concatenation of two elements is their least upper bound. -/
theorem Le.append {u v w : List (Tok κ)} (hu : u ⊑ w) (hv : v ⊑ w) : u ++ v ⊑ w := by
  intro t ht
  rcases List.mem_append.1 ht with ht | ht
  · exact hu t ht
  · exact hv t ht

theorem Le.cons_iff {t : Tok κ} {u v : List (Tok κ)} :
    t :: u ⊑ v ↔ ent v t = true ∧ u ⊑ v := by
  constructor
  · intro h
    exact ⟨h t List.mem_cons_self, fun s hs => h s (List.mem_cons_of_mem _ hs)⟩
  · rintro ⟨ht, hu⟩ s hs
    rcases List.mem_cons.1 hs with rfl | hs
    · exact ht
    · exact hu s hs

theorem Le.map_iff {α : Type} {u : List α} {v : List (Tok κ)} (f : α → Tok κ) :
    u.map f ⊑ v ↔ ∀ t ∈ u, ent v (f t) = true := by
  simp only [Le, List.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h t ht
    exact h _ t ht rfl
  · rintro h _ t ht rfl
    exact h t ht

/-! ## Step functions -/

/-- The value at `X` of a step function presented by its entries. -/
def stepApp (f : List (List (Tok κ) × List (Tok κ))) (X : List (Tok κ)) : List (Tok κ) :=
  (f.filter fun p => p.1.all (ent X)).flatMap Prod.snd

theorem mem_stepApp {f : List (List (Tok κ) × List (Tok κ))} {X : List (Tok κ)} {t : Tok κ} :
    t ∈ stepApp f X ↔ ∃ p ∈ f, p.1 ⊑ X ∧ t ∈ p.2 := by
  simp only [stepApp, List.mem_flatMap, List.mem_filter, List.all_eq_true]
  constructor
  · rintro ⟨p, ⟨hp, hX⟩, ht⟩
    exact ⟨p, hp, hX, ht⟩
  · rintro ⟨p, hp, hX, ht⟩
    exact ⟨p, ⟨hp, hX⟩, ht⟩

theorem mem_fnApp' {k : κ} {v X : List (Tok κ)} {t : Tok κ} :
    t ∈ fnApp k v X ↔ ∃ C X' Y', Tok.fn k C X' Y' ∈ v ∧ X' ⊑ X ∧ t ∈ Y' :=
  mem_fnApp

/-- The value of a step function is monotone in the function and the argument. -/
theorem fnApp_mono {k : κ} {v w X X' : List (Tok κ)} (hv : v ⊑ w) (hX : X ⊑ X') :
    fnApp k v X ⊑ fnApp k w X' := by
  intro s hs
  obtain ⟨C, X₀, Y₀, hp, h₀, hs⟩ := mem_fnApp'.1 hs
  have hw := hv _ hp
  rw [ent_fn, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hw
  refine ent_mono ?_ (hw.2 s hs)
  intro r hr
  obtain ⟨C', X₁, Y₁, hq, h₁, hr⟩ := mem_fnApp'.1 hr
  exact mem_fnApp'.2 ⟨C', X₁, Y₁, hq, (h₁.trans h₀).trans hX, hr⟩

theorem fnApp_append (k : κ) (u v X : List (Tok κ)) :
    fnApp k (u ++ v) X = fnApp k u X ++ fnApp k v X := by
  simp only [fnApp, fns_append, List.filter_append, List.flatMap_append]

/-! ## The selections of single tokens -/

@[simp] theorem args_nil (k : κ) (i : Nat) : args k i [] = [] := rfl

@[simp] theorem args_cons_tag (k k' : κ) (i : Nat) (v : List (Tok κ)) :
    args k i (.tag k' :: v) = args k i v := by
  simp [args, Tok.dep]

@[simp] theorem args_cons_arg (k k' : κ) (i i' : Nat) (C : List (Tok κ)) (t : Tok κ)
    (v : List (Tok κ)) :
    args k i (.arg k' i' C t :: v) =
      ((if k' = k ∧ i' = i then [t] else []) ++ (if k' = k ∧ i = 0 then C else [])) ++
        args k i v := rfl

@[simp] theorem args_cons_fn (k k' : κ) (i : Nat) (C X Y : List (Tok κ)) (v : List (Tok κ)) :
    args k i (.fn k' C X Y :: v) = (if k' = k ∧ i = 0 then C else []) ++ args k i v := rfl

@[simp] theorem fns_nil (k : κ) : fns k [] = [] := rfl

@[simp] theorem fns_cons_tag (k k' : κ) (v : List (Tok κ)) : fns k (.tag k' :: v) = fns k v := rfl

@[simp] theorem fns_cons_arg (k k' : κ) (i : Nat) (C : List (Tok κ)) (t : Tok κ)
    (v : List (Tok κ)) :
    fns k (.arg k' i C t :: v) = fns k v := rfl

@[simp] theorem fns_cons_fn (k k' : κ) (C X Y : List (Tok κ)) (v : List (Tok κ)) :
    fns k (.fn k' C X Y :: v) = if k' = k then (X, Y) :: fns k v else fns k v := rfl

@[simp] theorem hasTag_cons_tag (k k' : κ) (v : List (Tok κ)) :
    hasTag k (.tag k' :: v) = (k' == k || hasTag k v) := rfl

@[simp] theorem hasTag_cons_arg (k k' : κ) (i : Nat) (C : List (Tok κ)) (t : Tok κ)
    (v : List (Tok κ)) : hasTag k (.arg k' i C t :: v) = hasTag k v := rfl

@[simp] theorem hasTag_cons_fn (k k' : κ) (C X Y : List (Tok κ)) (v : List (Tok κ)) :
    hasTag k (.fn k' C X Y :: v) = hasTag k v := rfl

theorem args_map_arg (k : κ) (i : Nat) (C u : List (Tok κ)) (k' : κ) (j : Nat) :
    args k' j (u.map (.arg k i C)) =
      u.flatMap fun t => (if k = k' ∧ i = j then [t] else []) ++
        (if k = k' ∧ j = 0 then C else []) := by
  induction u with
  | nil => rfl
  | cons t u ih => simp only [List.map_cons, args_cons_arg, ih, List.flatMap_cons]

theorem args_map_arg_same (k : κ) (i : Nat) (u : List (Tok κ)) :
    args k i (u.map (.arg k i [])) = u := by
  induction u with
  | nil => rfl
  | cons t u ih => simp [ih]

theorem args_map_fn (k : κ) (C : List (Tok κ)) (f : List (List (Tok κ) × List (Tok κ)))
    (k' : κ) (j : Nat) :
    args k' j (f.map fun p => .fn k C p.1 p.2) =
      f.flatMap fun _ => if k = k' ∧ j = 0 then C else [] := by
  induction f with
  | nil => rfl
  | cons p f ih => simp only [List.map_cons, args_cons_fn, ih, List.flatMap_cons]

theorem fns_map_arg (k : κ) (i : Nat) (C u : List (Tok κ)) (k' : κ) :
    fns k' (u.map (.arg k i C)) = [] := by
  induction u with
  | nil => rfl
  | cons t u ih => simpa using ih

theorem fns_map_fn (k : κ) (C : List (Tok κ)) (f : List (List (Tok κ) × List (Tok κ))) :
    fns k (f.map fun p => .fn k C p.1 p.2) = f := by
  induction f with
  | nil => rfl
  | cons p f ih => simp [ih]

theorem hasTag_map_arg (k : κ) (i : Nat) (C u : List (Tok κ)) (k' : κ) :
    hasTag k' (u.map (.arg k i C)) = false := by
  induction u with
  | nil => rfl
  | cons t u ih => simpa using ih

theorem hasTag_map_fn (k : κ) (C : List (Tok κ)) (f : List (List (Tok κ) × List (Tok κ)))
    (k' : κ) : hasTag k' (f.map fun p => .fn k C p.1 p.2) = false := by
  induction f with
  | nil => rfl
  | cons p f ih => simpa using ih

theorem hasTag_append (k : κ) (u v : List (Tok κ)) :
    hasTag k (u ++ v) = (hasTag k u || hasTag k v) := by
  rw [Bool.eq_iff_iff]
  simp only [hasTag_iff, List.mem_append, Bool.or_eq_true]

end Entailment

/-! ## Elements of the domain -/

namespace Elem

/-- The universe. -/
def univ : List Tok := [.tag .univ]
/-- A ground type. -/
def ground : List Tok := [.tag .ground]
/-- The universe of codes. -/
def codes : List Tok := [.tag .codes]
/-- The type of numbers. -/
def nat : List Tok := [.tag .nat]
/-- Zero. -/
def zero : List Tok := [.tag .zero]
/-- The successor of an element. -/
def succ (u : List Tok) : List Tok := .tag .succ :: u.map (.arg .succ 0 [])
/-- The predecessor of an element. -/
def pred (u : List Tok) : List Tok := args .succ 0 u
/-- The dependent function type (`k = pi`) or dependent pair type (`k = sigma`)
with domain `a` and a family presented by the entries `f`. -/
def former (k : Kind) (a : List Tok) (f : List (List Tok × List Tok)) : List Tok :=
  .tag k :: (a.map (.arg k 0 []) ++ f.map fun p => .fn k a p.1 p.2)
/-- The domain of a dependent type of kind `k`. -/
def dom (k : Kind) (a : List Tok) : List Tok := args k 0 a
/-- The value of the family of a dependent type of kind `k` at `X`. -/
def fam (k : Kind) (a X : List Tok) : List Tok := fnApp k a X
/-- The function presented by the entries `f`. -/
def lam (f : List (List Tok × List Tok)) : List Tok := f.map fun p => .fn .lam [] p.1 p.2
/-- Application. -/
def app (u X : List Tok) : List Tok := fnApp .lam u X
/-- A pair. -/
def pair (u v : List Tok) : List Tok := u.map (.arg .pair 0 []) ++ v.map (.arg .pair 1 u)
/-- The first projection. -/
def fst (u : List Tok) : List Tok := args .pair 0 u
/-- The second projection. -/
def snd (u : List Tok) : List Tok := args .pair 1 u
/-- The identity type of carrier `c` between `u` and `v`. -/
def ident (c u v : List Tok) : List Tok :=
  .tag .ident :: (c.map (.arg .ident 0 []) ++ u.map (.arg .ident 1 c) ++ v.map (.arg .ident 2 c))
/-- Reflexivity at a point. -/
def refl (w : List Tok) : List Tok := .tag .refl :: w.map (.arg .refl 0 [])

/-! ## Laws of the elements -/

theorem pred_succ (u : List Tok) : pred (succ u) = u := by
  simp [pred, succ, args_map_arg_same]

theorem snd_pair (u v : List Tok) : snd (pair u v) = v := by
  simp only [snd, pair, args_append, args_map_arg]
  simp

theorem fst_pair (u v : List Tok) : Equiv (fst (pair u v)) u := by
  simp only [fst, pair, args_append, args_map_arg]
  simp only [and_self, if_true, List.append_nil, List.flatMap_singleton']
  constructor
  · refine Le.append (Le.of_subset fun t ht => ?_) (Le.of_subset fun t ht => ?_)
    · exact ht
    · obtain ⟨_, -, ht⟩ := List.mem_flatMap.1 ht
      exact ht
  · exact Le.append_left _ _

theorem app_lam (f : List (List Tok × List Tok)) (X : List Tok) : app (lam f) X = stepApp f X := by
  simp only [app, lam, fnApp, fns_map_fn, stepApp]

theorem fam_former (k : Kind) (a : List Tok) (f : List (List Tok × List Tok)) (X : List Tok) :
    fam k (former k a f) X = stepApp f X := by
  simp only [fam, former, fnApp, fns_cons_tag, fns_append, fns_map_arg, fns_map_fn,
    List.nil_append, stepApp]

theorem dom_former (k : Kind) (a : List Tok) (f : List (List Tok × List Tok)) :
    Equiv (dom k (former k a f)) a := by
  simp only [dom, former, args_cons_tag, args_append, args_map_arg_same, args_map_fn,
    and_self, if_true]
  constructor
  · refine Le.append (Le.refl a) (Le.of_subset fun t ht => ?_)
    obtain ⟨_, -, ht⟩ := List.mem_flatMap.1 ht
    exact ht
  · exact Le.append_left _ _

theorem lam_nil : lam [] = [] := rfl

theorem pair_nil : pair [] [] = [] := rfl

theorem app_nil (X : List Tok) : app [] X = [] := rfl

theorem fst_nil : fst [] = [] := rfl

theorem snd_nil : snd [] = [] := rfl

/-- A function is below an element when each of its entries is below the value
of the element at the entry's input. -/
theorem lam_le_iff {f : List (List Tok × List Tok)} {v : List Tok} :
    lam f ⊑ v ↔ ∀ p ∈ f, p.2 ⊑ app v p.1 := by
  rw [lam, Le.map_iff]
  simp only [ent_fn, List.all_nil, Bool.true_and, List.all_eq_true]
  rfl

theorem tag_le_iff {k : Kind} {v : List Tok} : [Tok.tag k] ⊑ v ↔ Tok.tag k ∈ v := by
  simp only [Le, List.mem_singleton, forall_eq, ent_tag, hasTag_iff]

theorem succ_le_iff {u v : List Tok} : succ u ⊑ v ↔ Tok.tag .succ ∈ v ∧ u ⊑ pred v := by
  simp only [succ, Le.cons_iff, ent_tag, hasTag_iff, Le.map_iff, ent_arg, List.all_nil,
    Bool.true_and, pred]
  rfl

theorem pair_le_iff {u w v : List Tok} : pair u w ⊑ v ↔ u ⊑ fst v ∧ (w ≠ [] → u ⊑ fst v) ∧
    w ⊑ snd v := by
  simp only [pair, Le]
  simp only [List.mem_append, List.mem_map, fst, snd]
  constructor
  · intro h
    refine ⟨fun t ht => ?_, fun _ t ht => ?_, fun t ht => ?_⟩
    · have := h _ (.inl ⟨t, ht, rfl⟩)
      rwa [ent_arg, List.all_nil, Bool.true_and] at this
    · have := h _ (.inl ⟨t, ht, rfl⟩)
      rwa [ent_arg, List.all_nil, Bool.true_and] at this
    · have := h _ (.inr ⟨t, ht, rfl⟩)
      rw [ent_arg, Bool.and_eq_true] at this
      exact this.2
  · rintro ⟨hu, -, hw⟩ _ (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · rw [ent_arg, List.all_nil, Bool.true_and]; exact hu t ht
    · rw [ent_arg, Bool.and_eq_true, List.all_eq_true]; exact ⟨hu, hw t ht⟩

theorem former_le_iff {k : Kind} {a v : List Tok} {f : List (List Tok × List Tok)} :
    former k a f ⊑ v ↔ Tok.tag k ∈ v ∧ a ⊑ dom k v ∧ ∀ p ∈ f, p.2 ⊑ fam k v p.1 := by
  simp only [former, Le.cons_iff, ent_tag, hasTag_iff]
  refine and_congr_right fun _ => ?_
  simp only [Le, List.mem_append, List.mem_map, dom, fam]
  constructor
  · intro h
    refine ⟨fun t ht => ?_, fun p hp t ht => ?_⟩
    · have := h _ (.inl ⟨t, ht, rfl⟩)
      rwa [ent_arg, List.all_nil, Bool.true_and] at this
    · have := h _ (.inr ⟨p, hp, rfl⟩)
      rw [ent_fn, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at this
      exact this.2 t ht
  · rintro ⟨ha, hf⟩ _ (⟨t, ht, rfl⟩ | ⟨p, hp, rfl⟩)
    · rw [ent_arg, List.all_nil, Bool.true_and]; exact ha t ht
    · rw [ent_fn, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
      exact ⟨ha, hf p hp⟩

end Elem

end Domain
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
