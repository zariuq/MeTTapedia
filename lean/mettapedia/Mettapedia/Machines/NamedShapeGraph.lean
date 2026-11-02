import Mettapedia.Machines.NamesOverStores

/-!
# Recursive shape holes referring across stores

Expressions contain constructor structure and named holes. Names may carry
store tags; expansion consults a single resolver, not a per-hole namespace.
Finite expansion is justified by decreasing reference ranks and closure of
the named heap. Sharing and repeated edges are allowed. Arbitrary cyclic
references are deliberately outside this finite-term interpretation.

The skeleton/list projection connects directly to ShapeStore reassembly.
Depth bounds concern reference dereferences, not bytes, evaluator time, or
the size of the unfolded tree.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NamedShapeGraph

open ShapeStore

variable {α Name : Type}

inductive Expr (α Name : Type) where
  | atom (value : α)
  | node (left right : Expr α Name)
  | ref (name : Name)
  deriving DecidableEq

def Expr.refs : Expr α Name → List Name
  | .atom _ => []
  | .node l r => l.refs ++ r.refs
  | .ref n => [n]

def Expr.skeleton : Expr α Name → Skel α
  | .atom a => .atom a
  | .node l r => .node l.skeleton r.skeleton
  | .ref _ => .hole

def Expr.plug (values : Name → Tm α) : Expr α Name → Tm α
  | .atom a => .atom a
  | .node l r => .node (l.plug values) (r.plug values)
  | .ref n => values n

def Expr.eval (read : Name → Option (Tm α)) : Expr α Name → Option (Tm α)
  | .atom a => some (.atom a)
  | .node l r => (l.eval read).bind fun a => (r.eval read).map (Tm.node a)
  | .ref n => read n

theorem refs_length (e : Expr α Name) : e.refs.length = e.skeleton.holes := by
  induction e <;> simp_all [Expr.refs, Expr.skeleton, Skel.holes]

theorem fill_plug (e : Expr α Name) (values : Name → Tm α) (suffix : List (Tm α)) :
    fill e.skeleton (e.refs.map values ++ suffix) = some (e.plug values, suffix) := by
  induction e generalizing suffix with
  | atom a => rfl
  | ref n => rfl
  | node l r ihl ihr =>
      simp [Expr.skeleton, Expr.refs, Expr.plug, fill, List.append_assoc, ihl, ihr]

theorem reassemble_plug (e : Expr α Name) (values : Name → Tm α) :
    reassemble (e.skeleton, e.refs.map values) = some (e.plug values) := by
  have filled := fill_plug e values []
  simp only [List.append_nil] at filled
  simp only [reassemble, filled]

theorem eval_plug (e : Expr α Name) (read : Name → Option (Tm α))
    (values : Name → Tm α) (available : ∀ n ∈ e.refs, read n = some (values n)) :
    e.eval read = some (e.plug values) := by
  induction e with
  | atom a => rfl
  | ref n => exact available n (by simp [Expr.refs])
  | node l r ihl ihr =>
      have hl := ihl (fun n hn => available n (List.mem_append_left _ hn))
      have hr := ihr (fun n hn => available n (List.mem_append_right _ hn))
      simp [Expr.eval, Expr.plug, hl, hr]

theorem eval_exists (e : Expr α Name) (read : Name → Option (Tm α))
    (available : ∀ n ∈ e.refs, ∃ t, read n = some t) : ∃ t, e.eval read = some t := by
  induction e with
  | atom a => exact ⟨.atom a, rfl⟩
  | ref n => exact available n (by simp [Expr.refs])
  | node l r ihl ihr =>
      obtain ⟨tl, hl⟩ := ihl (fun n hn => available n (List.mem_append_left _ hn))
      obtain ⟨tr, hr⟩ := ihr (fun n hn => available n (List.mem_append_right _ hn))
      exact ⟨.node tl tr, by simp [Expr.eval, hl, hr]⟩

theorem eval_congr (e : Expr α Name) (a b : Name → Option (Tm α))
    (same : ∀ n ∈ e.refs, a n = b n) : e.eval a = e.eval b := by
  induction e with
  | atom a => rfl
  | ref n => exact same n (by simp [Expr.refs])
  | node l r ihl ihr =>
      rw [Expr.eval, Expr.eval, ihl (fun n hn => same n (List.mem_append_left _ hn)),
        ihr (fun n hn => same n (List.mem_append_right _ hn))]

/-- Replace named holes by further contexts, permitting sharing across layers. -/
def Expr.bindRefs {Other : Type} (next : Name → Expr α Other) : Expr α Name → Expr α Other
  | .atom a => .atom a
  | .node l r => .node (l.bindRefs next) (r.bindRefs next)
  | .ref n => next n

theorem bindRefs_identity (e : Expr α Name) : e.bindRefs Expr.ref = e := by
  induction e <;> simp_all [Expr.bindRefs]

theorem bindRefs_assoc {Middle Last : Type} (e : Expr α Name)
    (first : Name → Expr α Middle) (second : Middle → Expr α Last) :
    (e.bindRefs first).bindRefs second = e.bindRefs (fun n => (first n).bindRefs second) := by
  induction e <;> simp_all [Expr.bindRefs]

theorem refs_bindRefs {Other : Type} (e : Expr α Name) (next : Name → Expr α Other) :
    (e.bindRefs next).refs = e.refs.flatMap (fun n => (next n).refs) := by
  induction e <;> simp_all [Expr.bindRefs, Expr.refs]

theorem plug_bindRefs {Other : Type} (e : Expr α Name)
    (next : Name → Expr α Other) (values : Other → Tm α) :
    (e.bindRefs next).plug values = e.plug (fun n => (next n).plug values) := by
  induction e <;> simp_all [Expr.bindRefs, Expr.plug]

theorem eval_bindRefs {Other : Type} (e : Expr α Name)
    (next : Name → Expr α Other) (read : Other → Option (Tm α)) :
    (e.bindRefs next).eval read = e.eval (fun n => (next n).eval read) := by
  induction e <;> simp_all [Expr.bindRefs, Expr.eval]

/-- Successful resolutions can be extended without changing an expression's
successful result; failures are not silently treated as values. -/
theorem eval_extension (e : Expr α Name) (a b : Name → Option (Tm α))
    (preserved : ∀ n t, a n = some t → b n = some t) (t : Tm α)
    (success : e.eval a = some t) : e.eval b = some t := by
  induction e generalizing t with
  | atom x => exact success
  | ref n => exact preserved n t success
  | node l r ihl ihr =>
      obtain ⟨tl, hl, rest⟩ := Option.bind_eq_some_iff.mp success
      obtain ⟨tr, hr, equal⟩ := Option.map_eq_some_iff.mp rest
      subst t
      simp [Expr.eval, ihl tl hl, ihr tr hr]

abbrev Heap (α Name : Type) := Name → Option (Expr α Name)

def unfoldName (heap : Heap α Name) : Nat → Name → Option (Tm α)
  | 0, _ => none
  | depth + 1, n => (heap n).bind fun e => e.eval (unfoldName heap depth)

theorem unfold_monotone (heap : Heap α Name) (small big : Nat) (le : small ≤ big)
    (n : Name) (t : Tm α) (success : unfoldName heap small n = some t) :
    unfoldName heap big n = some t := by
  induction small generalizing big n t with
  | zero => simp [unfoldName] at success
  | succ small ih =>
      cases big with
      | zero => omega
      | succ big =>
          obtain ⟨e, found, expanded⟩ := Option.bind_eq_some_iff.mp success
          simp only [unfoldName, found, Option.bind_some]
          exact eval_extension e _ _ (fun name value h => ih big (by omega) name value h)
            t expanded

/-- Every outgoing reference is present and strictly decreases rank. -/
abbrev Ranked (heap : Heap α Name) (rank : Name → Nat) : Prop :=
  ∀ n e, heap n = some e → ∀ child ∈ e.refs,
    rank child < rank n ∧ ∃ body, heap child = some body

theorem ranked_unfolds (heap : Heap α Name) (rank : Name → Nat)
    (valid : Ranked heap rank) (n : Name) (body : Expr α Name)
    (found : heap n = some body) :
    ∃ t, unfoldName heap (rank n + 1) n = some t := by
  generalize hsize : rank n = size
  induction size using Nat.strong_induction_on generalizing n body with
  | h size ih =>
      have available : ∀ child ∈ body.refs, ∃ t, unfoldName heap size child = some t := by
        intro child occurs
        obtain ⟨lower, childBody, childFound⟩ := valid n body found child occurs
        obtain ⟨t, ht⟩ := ih (rank child) (by omega) child childBody childFound rfl
        exact ⟨t, unfold_monotone heap (rank child + 1) size (by omega) child t ht⟩
      obtain ⟨t, ht⟩ := eval_exists body _ available
      exact ⟨t, by simp [unfoldName, found, ht]⟩

theorem unfolded_value_unique (heap : Heap α Name) (a b : Nat) (n : Name)
    (x y : Tm α) (hx : unfoldName heap a n = some x)
    (hy : unfoldName heap b n = some y) : x = y := by
  have ha := unfold_monotone heap a (max a b) (le_max_left _ _) n x hx
  have hb := unfold_monotone heap b (max a b) (le_max_right _ _) n y hy
  exact Option.some.inj (ha.symm.trans hb)

/-- Heap extension or relocation preserves existing expansions when all
stored bodies are preserved. Payload-preserving re-cuts use `eval_congr`
and a stronger representation relation rather than this syntactic lemma. -/
theorem unfold_extension (before after : Heap α Name)
    (preserved : ∀ n e, before n = some e → after n = some e)
    (depth : Nat) (n : Name) (t : Tm α)
    (success : unfoldName before depth n = some t) : unfoldName after depth n = some t := by
  induction depth generalizing n t with
  | zero => simp [unfoldName] at success
  | succ depth ih =>
      obtain ⟨e, found, expanded⟩ := Option.bind_eq_some_iff.mp success
      simp only [unfoldName, preserved n e found, Option.bind_some]
      exact eval_extension e _ _ (fun n t h => ih n t h) t expanded

def termSize : Tm α → Nat
  | .atom _ => 1
  | .node l r => 1 + termSize l + termSize r

/-- Quote selected subterms, preserving the original position-sensitive policy. -/
def quote (name : Tm α → Name) : Policy α → Tm α → Expr α Name
  | policy, .atom a => if policy [] (.atom a) then .ref (name (.atom a)) else .atom a
  | policy, .node l r =>
      if policy [] (.node l r) then .ref (name (.node l r)) else
        .node (quote name (fun p => policy (false :: p)) l)
          (quote name (fun p => policy (true :: p)) r)

theorem quote_decomposition (name : Tm α → Name) (policy : Policy α) (t : Tm α) :
    (quote name policy t).skeleton = (dec policy t).1 ∧
    (quote name policy t).refs = (dec policy t).2.map name := by
  induction t generalizing policy with
  | atom a => by_cases h : policy [] (.atom a) <;> simp [quote, dec, h, Expr.skeleton, Expr.refs]
  | node l r ihl ihr =>
      by_cases h : policy [] (.node l r)
      · simp [quote, dec, h, Expr.skeleton, Expr.refs]
      · simp [quote, dec, h, Expr.skeleton, Expr.refs, (ihl _).1, (ihl _).2,
          (ihr _).1, (ihr _).2]

theorem quote_eval (name : Tm α → Name) (read : Name → Option (Tm α))
    (roundtrip : ∀ t, read (name t) = some t) (policy : Policy α) (t : Tm α) :
    (quote name policy t).eval read = some t := by
  induction t generalizing policy with
  | atom a => by_cases h : policy [] (.atom a) <;> simp [quote, h, Expr.eval, roundtrip]
  | node l r ihl ihr =>
      by_cases h : policy [] (.node l r) <;> simp [quote, h, Expr.eval, roundtrip, ihl, ihr]

theorem quote_refs_size (name : Tm α → Name) (policy : Policy α) (t : Tm α)
    (n : Name) (member : n ∈ (quote name policy t).refs) :
    ∃ sub, n = name sub ∧ termSize sub ≤ termSize t := by
  induction t generalizing policy with
  | atom a =>
      by_cases h : policy [] (.atom a)
      · simp [quote, h, Expr.refs] at member
        exact ⟨.atom a, member, le_refl _⟩
      · simp [quote, h, Expr.refs] at member
  | node l r ihl ihr =>
      by_cases h : policy [] (.node l r)
      · simp [quote, h, Expr.refs] at member
        exact ⟨.node l r, member, le_refl _⟩
      · simp only [quote, h, Bool.false_eq_true, ↓reduceIte, Expr.refs, List.mem_append] at member
        rcases member with hl | hr
        · obtain ⟨sub, equal, le⟩ := ihl _ hl
          exact ⟨sub, equal, by simp only [termSize]; omega⟩
        · obtain ⟨sub, equal, le⟩ := ihr _ hr
          exact ⟨sub, equal, by simp only [termSize]; omega⟩

/-- A stored body must not quote itself at the root. -/
def quoteBody (name : Tm α → Name) (policy : Policy α) : Tm α → Expr α Name
  | .atom a => .atom a
  | .node l r => .node (quote name (fun p => policy (false :: p)) l)
      (quote name (fun p => policy (true :: p)) r)

theorem quoteBody_eval (name : Tm α → Name) (read : Name → Option (Tm α))
    (roundtrip : ∀ t, read (name t) = some t) (policy : Policy α) (t : Tm α) :
    (quoteBody name policy t).eval read = some t := by
  cases t <;> simp [quoteBody, Expr.eval, quote_eval name read roundtrip]

theorem quoteBody_refs_strict (name : Tm α → Name) (policy : Policy α) (t : Tm α)
    (n : Name) (member : n ∈ (quoteBody name policy t).refs) :
    ∃ sub, n = name sub ∧ termSize sub < termSize t := by
  cases t with
  | atom a => simp [quoteBody, Expr.refs] at member
  | node l r =>
      rcases List.mem_append.mp member with hl | hr
      · obtain ⟨sub, equal, le⟩ := quote_refs_size name _ l n hl
        exact ⟨sub, equal, by simp only [termSize]; omega⟩
      · obtain ⟨sub, equal, le⟩ := quote_refs_size name _ r n hr
        exact ⟨sub, equal, by simp only [termSize]; omega⟩

namespace Controls

abbrev N := Bool × Nat
def heap : Heap String N
  | (false, 0) => some (.atom "a")
  | (true, 1) => some (.node (.ref (false, 0)) (.ref (false, 0)))
  | _ => none

theorem repeated_cross_store_reference :
    unfoldName heap 2 (true, 1) = some (.node (.atom "a") (.atom "a")) := by decide

example : unfoldName heap 1 (true, 1) = none := by decide
example : unfoldName heap 10 (true, 2) = none := by decide

def cycle : Heap Unit Unit := fun _ => some (.ref ())

theorem cycle_never_unfolds (depth : Nat) : unfoldName cycle depth () = none := by
  induction depth <;> simp_all [unfoldName, cycle, Expr.eval]

theorem cycle_has_no_rank : ¬ ∃ rank, Ranked cycle rank := by
  rintro ⟨rank, valid⟩
  have lower := (valid () (.ref ()) rfl () (by simp [Expr.refs])).1
  omega

end Controls

#print axioms reassemble_plug
#print axioms ranked_unfolds
#print axioms quoteBody_refs_strict
#print axioms unfolded_value_unique

end Mettapedia.Machines.NamedShapeGraph
