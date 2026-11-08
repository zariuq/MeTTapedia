import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ImpliedMeets

/-!
# HE's argument check, and type rows on expressions below a value's top

HE checks an argument of a typed call by the argument's typings, in its order
(for an expression: its tuple typings, the rows whose subject is the expression
itself, then its application typings): the **first typing that unifies with the
formal binds it**, and the argument is then **evaluated at that instance**. An
expression is evaluated at a type by its head: the first path of the head's
function types (each function type, then each choice of the arguments' typings,
the first argument slowest) whose range meets the type is taken, and each
argument is in turn evaluated at its formal under that path's solutions, in
order, each narrowing what the next one sees. A leaf is cast to the type by its
first typing that meets it.

**The model** reads every typing by the ground types it allows (a set), every
unifier by its ground solutions: two types unify exactly when their sets meet,
and the instance a unifier leaves is the meet. A value is a leaf with its
typings, or a node `(h a₁ … aₙ)` with the rows HE lists before its application
typings (`rows`), its head's function types (at least one) and its arguments.
Formals are ordinary types (no `Atom`, `%Undefined%` or metatype formal); an
untyped argument is `%Undefined%`, which meets every type (`orUndef`).
* `typs`: HE's typings of a value; `eval`: HE's evaluation at an instance set,
  `none` for an error, otherwise the instances left; `heCheck`: the check of an
  argument at a formal;
* `Accepts`: CeTTa's machine check (`prepared_pure_he_value_has_type`): some
  typing of the value unifies with the formal.

**Theorem** (`check_iff`): on a value with **no row on any node** (`Plain`),
HE's check succeeds exactly where the machine's does. Every typing of such a
value has a path behind it, and every argument of that path is again such a
value at an instance one of its typings meets, so each evaluation succeeds
(`eval_ok`, `evalArgs_ok`), whatever the instances its earlier arguments left.

**Refutation of the top-head guard** (`Controls.inner_row`,
`Controls.top_guard_insufficient`). CeTTa refuses a value whose top head a row
may type as an expression (`prepared_pure_value_row_typed`). A row on an
argument's head is not refused, and it does not flow consistently: with
`(: (Wrap 1) Foo)`, `(: Wrap (-> Number W))` and `(: g (-> (List $t) Number))`, the
typings of `(Cons (Wrap 1) Nil)` are `(List Foo)` then `(List W)`; HE binds `$t`
to `Foo`, evaluates the argument at `(List Foo)`, takes `Cons`'s path through the
row's `Foo`, and evaluates `(Wrap 1)` at `Foo`, where `Wrap`'s only path gives
`W`: an error, where the machine accepts. HE's interpreter model answers
`(Error (Wrap 1) (BadType Foo W))`, Rust's answer, and `7` without the row
(`Controls.inner_row_he`). The guard must hold at every node of the value; the
same value at a top row is `Controls.top_row` (the case CeTTa refuses).

**The hereditary guard** (CeTTa's fix, `space_type_rows_free_below`): `rowsFree`,
its memoized walk (`walkRF_eq`, `mark_after_walk`, `bindScope_sound`), and the
reading of an admitted value as one with no row on any node
(`plain_of_rowsFree`, `admitted_check_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ValueRows

/-- A function type of a head: its formals and its range. -/
abbrev FnTy := List (Ty String) × Ty String

/-- A typing, read by the ground types it allows. -/
abbrev TySet := Set (Ty Empty)

/-- An assignment of a function type's variables. -/
abbrev Asg := String → Ty Empty

/-- A value as HE's argument check reads it. -/
inductive Val where
  /-- A symbol or a grounded value, with its typings in HE's order. -/
  | leaf (typs : List TySet)
  /-- `(h a₁ … aₙ)`: the typings HE lists before its application typings (rows
  whose subject is the expression), the head's function types `f :: fs`, and the
  arguments. -/
  | node (rows : List TySet) (f : FnTy) (fs : List FnTy) (args : List Val)

/-- Every choice of one element of each list, the first list varying slowest. -/
def choices {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | l :: ls => l.flatMap fun a => (choices ls).map (a :: ·)

/-- An argument's typings as a path reads them: an untyped argument is
`%Undefined%`, which meets every type. -/
def orUndef : List TySet → List TySet
  | [] => [Set.univ]
  | t :: ts => t :: ts

/-- A path's solutions under an expected set: each argument's chosen typing
allows its formal, and the range lies in the expected set. -/
def pathSols (Fs : List (Ty String)) (R : Ty String) (c : List TySet) (E : TySet) : Set Asg :=
  {ψ | List.Forall₂ (fun F S => F.bind ψ ∈ S) Fs c ∧ R.bind ψ ∈ E}

/-- A type read under a set of assignments. -/
def readAt (R : Ty String) (Ψ : Set Asg) : TySet := {T | ∃ ψ ∈ Ψ, R.bind ψ = T}

/-- HE's paths for a head: each function type, then each choice of the
arguments' typings. -/
def paths (fns : List FnTy) (tss : List (List TySet)) : List (FnTy × List TySet) :=
  fns.flatMap fun f => (choices tss).map fun c => (f, c)

/-- The application typings: the range of each path. -/
def appTyps (fns : List FnTy) (tss : List (List TySet)) : List TySet :=
  (paths fns tss).map fun p => readAt p.1.2 (pathSols p.1.1 p.1.2 p.2 Set.univ)

mutual
/-- **HE's typings of a value**, in its order. -/
def typs : Val → List TySet
  | .leaf ts => ts
  | .node rows f fs args => rows ++ appTyps (f :: fs) (argTyps args)
/-- The typings of each argument, as a path reads them. -/
def argTyps : List Val → List (List TySet)
  | [] => []
  | a :: as => orUndef (typs a) :: argTyps as
end

open Classical in
/-- The first typing that meets an expected set. -/
noncomputable def firstMeet (ts : List TySet) (E : TySet) : Option TySet :=
  ts.find? fun S => decide (S ∩ E).Nonempty

open Classical in
/-- The first path that meets an expected set. -/
noncomputable def firstPath (fns : List FnTy) (tss : List (List TySet)) (E : TySet) :
    Option (FnTy × List TySet) :=
  (paths fns tss).find? fun p => decide (pathSols p.1.1 p.1.2 p.2 E).Nonempty

mutual
/-- **HE evaluates a value at an expected set**: `none` is an error, `some E'`
answers the value with the instances `E'` its bindings leave. A leaf is cast by
its first typing that meets the set; a node takes its head's first path that
meets it and evaluates its arguments in order. -/
noncomputable def eval : Val → TySet → Option TySet
  | .leaf ts, E => (firstMeet (orUndef ts) E).map (· ∩ E)
  | .node _ f fs args, E =>
      match firstPath (f :: fs) (argTyps args) E with
      | none => none
      | some (g, c) => (evalArgs args g.1 (pathSols g.1 g.2 c E)).map (readAt g.2)
/-- The arguments evaluated in order at their formals under the path's
solutions, each narrowing the solutions to what it leaves. -/
noncomputable def evalArgs : List Val → List (Ty String) → Set Asg → Option (Set Asg)
  | [], [], Ψ => some Ψ
  | a :: as, F :: Fs, Ψ =>
      match eval a (readAt F Ψ) with
      | none => none
      | some J => evalArgs as Fs {ψ | ψ ∈ Ψ ∧ F.bind ψ ∈ J}
  | _, _, _ => none
end

/-- **HE's check of an argument at a formal** (its instances `E`): the first
typing that meets the formal binds it, and the argument is evaluated there. -/
noncomputable def heCheck (v : Val) (E : TySet) : Option TySet :=
  (firstMeet (orUndef (typs v)) E).bind fun S => eval v (S ∩ E)

/-- **The machine's check**: some typing of the value meets the formal. -/
def Accepts (v : Val) (E : TySet) : Prop := ∃ S ∈ orUndef (typs v), (S ∩ E).Nonempty

mutual
/-- A value with no row on any node. -/
def Plain : Val → Prop
  | .leaf _ => True
  | .node rows _ _ args => rows = [] ∧ PlainArgs args
/-- Arguments with no row on any node. -/
def PlainArgs : List Val → Prop
  | [] => True
  | a :: as => Plain a ∧ PlainArgs as
end

/-- The guard CeTTa applies: no row on the value's top node. -/
def TopPlain : Val → Prop
  | .leaf _ => True
  | .node rows _ _ _ => rows = []

/-! ## Lemmas -/

theorem forall₂_of_mem_choices {α : Type} :
    ∀ {ls : List (List α)} {c : List α}, c ∈ choices ls → List.Forall₂ (fun x l => x ∈ l) c ls
  | [], c, h => by
      simp only [choices, List.mem_singleton] at h
      subst h
      exact .nil
  | l :: ls, c, h => by
      simp only [choices, List.mem_flatMap, List.mem_map] at h
      obtain ⟨a, ha, c', hc', rfl⟩ := h
      exact .cons ha (forall₂_of_mem_choices hc')

theorem choices_ne_nil {α : Type} : ∀ {ls : List (List α)}, (∀ l ∈ ls, l ≠ []) → choices ls ≠ []
  | [], _ => by simp [choices]
  | l :: ls, h => by
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil l (h l (by simp))
      obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _
        (choices_ne_nil (ls := ls) fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
      exact List.ne_nil_of_mem (a := a :: c)
        (by simp only [choices, List.mem_flatMap, List.mem_map]; exact ⟨a, ha, c, hc, rfl⟩)

theorem orUndef_ne_nil (ts : List TySet) : orUndef ts ≠ [] := by
  cases ts <;> simp [orUndef]

theorem orUndef_of_ne_nil {ts : List TySet} (h : ts ≠ []) : orUndef ts = ts := by
  cases ts with
  | nil => exact absurd rfl h
  | cons t ts => rfl

theorem argTyps_ne_nil : ∀ (as : List Val), ∀ l ∈ argTyps as, l ≠ []
  | [], l, h => by simp [argTyps] at h
  | a :: as, l, h => by
      simp only [argTyps, List.mem_cons] at h
      rcases h with rfl | h
      · exact orUndef_ne_nil _
      · exact argTyps_ne_nil as l h

theorem appTyps_ne_nil (f : FnTy) (fs : List FnTy) (as : List Val) : appTyps (f :: fs) (argTyps as) ≠ [] := by
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ (choices_ne_nil (argTyps_ne_nil as))
  refine List.ne_nil_of_mem (a := readAt f.2 (pathSols f.1 f.2 c Set.univ)) ?_
  simp only [appTyps, paths, List.mem_map, List.mem_flatMap, List.mem_cons]
  exact ⟨(f, c), ⟨f, .inl rfl, c, hc, rfl⟩, rfl⟩

theorem firstMeet_spec {ts : List TySet} {E : TySet} (h : ∃ S ∈ ts, (S ∩ E).Nonempty) :
    ∃ S, firstMeet ts E = some S ∧ S ∈ ts ∧ (S ∩ E).Nonempty := by
  classical
  have hs : (firstMeet ts E).isSome := by
    unfold firstMeet
    rw [List.find?_isSome]
    obtain ⟨S, hS, hne⟩ := h
    exact ⟨S, hS, by simpa using hne⟩
  obtain ⟨S, hS⟩ := Option.isSome_iff_exists.mp hs
  refine ⟨S, hS, List.mem_of_find?_eq_some hS, ?_⟩
  have := List.find?_some hS
  simpa using this

theorem firstMeet_some {ts : List TySet} {E S : TySet} (h : firstMeet ts E = some S) :
    S ∈ ts ∧ (S ∩ E).Nonempty := by
  classical
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simpa using this

theorem firstMeet_of_head {ts : List TySet} {E S : TySet} (h : ts.head? = some S)
    (hne : (S ∩ E).Nonempty) : firstMeet ts E = some S := by
  classical
  cases ts with
  | nil => cases h
  | cons t ts =>
      simp only [List.head?_cons, Option.some.injEq] at h
      subst h
      unfold firstMeet
      rw [List.find?_cons_of_pos]
      exact decide_eq_true hne

theorem firstPath_of_head {fns : List FnTy} {tss : List (List TySet)} {E : TySet}
    {p : FnTy × List TySet} (h : (paths fns tss).head? = some p)
    (hne : (pathSols p.1.1 p.1.2 p.2 E).Nonempty) : firstPath fns tss E = some p := by
  classical
  unfold firstPath
  cases hps : paths fns tss with
  | nil => rw [hps] at h; cases h
  | cons q qs =>
      rw [hps] at h
      simp only [List.head?_cons, Option.some.injEq] at h
      subst h
      rw [List.find?_cons_of_pos]
      exact decide_eq_true hne

theorem eval_node (rows : List TySet) (f : FnTy) (fs : List FnTy) (args : List Val) (E : TySet) :
    eval (.node rows f fs args) E =
      match firstPath (f :: fs) (argTyps args) E with
      | none => none
      | some (g, c) => (evalArgs args g.1 (pathSols g.1 g.2 c E)).map (readAt g.2) := by
  rw [eval]

theorem evalArgs_cons (a : Val) (as : List Val) (F : Ty String) (Fs : List (Ty String)) (Ψ : Set Asg) :
    evalArgs (a :: as) (F :: Fs) Ψ =
      match eval a (readAt F Ψ) with
      | none => none
      | some J => evalArgs as Fs {ψ | ψ ∈ Ψ ∧ F.bind ψ ∈ J} := by
  rw [evalArgs]

/-! ## Values with no row on any node -/

mutual
/-- **Every evaluation of a value with no row succeeds** at an expected set one
of its typings meets, leaving a nonempty part of it. -/
theorem eval_ok : ∀ (v : Val), Plain v → ∀ (E : TySet), (∃ S ∈ orUndef (typs v), (S ∩ E).Nonempty) →
    ∃ E', eval v E = some E' ∧ E'.Nonempty ∧ E' ⊆ E
  | .leaf ts, _, E, h => by
      obtain ⟨S, hS, _, hne⟩ := firstMeet_spec h
      refine ⟨S ∩ E, ?_, hne, Set.inter_subset_right⟩
      simp only [typs] at hS
      simp [eval, hS]
  | .node rows f fs args, hp, E, h => by
      classical
      obtain ⟨hrows, hargs⟩ := hp
      subst hrows
      have htyps : orUndef (typs (.node [] f fs args)) = appTyps (f :: fs) (argTyps args) := by
        simp only [typs, List.nil_append]
        exact orUndef_of_ne_nil (appTyps_ne_nil f fs args)
      rw [htyps] at h
      obtain ⟨S, hS, T, hTS, hTE⟩ := h
      simp only [appTyps, List.mem_map] at hS
      obtain ⟨p, hp, rfl⟩ := hS
      obtain ⟨ψ, hψ, rfl⟩ := hTS
      have hsome : (firstPath (f :: fs) (argTyps args) E).isSome := by
        unfold firstPath
        rw [List.find?_isSome]
        exact ⟨p, hp, by simpa using ⟨ψ, hψ.1, hTE⟩⟩
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hsome
      have hqne : (pathSols q.1.1 q.1.2 q.2 E).Nonempty := by
        have := List.find?_some hq
        simpa using this
      have hqmem : q ∈ paths (f :: fs) (argTyps args) := List.mem_of_find?_eq_some hq
      have hc : List.Forall₂ (fun x l => x ∈ l) q.2 (argTyps args) := by
        simp only [paths, List.mem_flatMap, List.mem_map] at hqmem
        obtain ⟨g, _, c, hc, rfl⟩ := hqmem
        exact forall₂_of_mem_choices hc
      obtain ⟨Ψ', hΨ', hne', hsub'⟩ := evalArgs_ok args hargs q.1.1 q.2 (pathSols q.1.1 q.1.2 q.2 E)
        hc hqne fun ψ hψ => hψ.1
      obtain ⟨ψ', hψ'⟩ := hne'
      refine ⟨readAt q.1.2 Ψ', ?_, ⟨_, ψ', hψ', rfl⟩, ?_⟩
      · obtain ⟨⟨Fs, R⟩, c⟩ := q
        simp only [eval, hq, hΨ', Option.map_some]
      · rintro _ ⟨χ, hχ, rfl⟩
        exact (hsub' hχ).2
/-- **The arguments of a path evaluate in order**: from nonempty solutions under
which every chosen typing allows its formal, each argument meets its formal's
instances at its chosen typing, and what it leaves is again nonempty. -/
theorem evalArgs_ok : ∀ (as : List Val), PlainArgs as → ∀ (Fs : List (Ty String)) (c : List TySet)
    (Ψ : Set Asg), List.Forall₂ (fun x l => x ∈ l) c (argTyps as) → Ψ.Nonempty →
    (∀ ψ ∈ Ψ, List.Forall₂ (fun F S => F.bind ψ ∈ S) Fs c) →
    ∃ Ψ', evalArgs as Fs Ψ = some Ψ' ∧ Ψ'.Nonempty ∧ Ψ' ⊆ Ψ
  | [], _, Fs, c, Ψ, hc, hne, hall => by
      obtain ⟨ψ, hψ⟩ := hne
      cases hc
      cases hall ψ hψ
      exact ⟨Ψ, rfl, ⟨ψ, hψ⟩, subset_rfl⟩
  | a :: as, hp, Fs, c, Ψ, hc, hne, hall => by
      obtain ⟨hpa, hpas⟩ := hp
      obtain ⟨ψ, hψ⟩ := hne
      cases hc with
      | cons hS hc' =>
        rename_i S c'
        cases hFs : Fs with
        | nil =>
            have := hall ψ hψ
            rw [hFs] at this
            cases this
        | cons F Fs' =>
            have hJ : (S ∩ readAt F Ψ).Nonempty := by
              refine ⟨F.bind ψ, ?_, ψ, hψ, rfl⟩
              have := hall ψ hψ
              rw [hFs] at this
              cases this with
              | cons h _ => exact h
            obtain ⟨J, hJeq, ⟨T, hT⟩, hJsub⟩ := eval_ok a hpa (readAt F Ψ) ⟨S, hS, hJ⟩
            obtain ⟨χ, hχ, rfl⟩ := hJsub hT
            have hall' : ∀ φ ∈ {φ | φ ∈ Ψ ∧ F.bind φ ∈ J}, List.Forall₂ (fun F S => F.bind φ ∈ S) Fs' c' := by
              intro φ hφ
              have := hall φ hφ.1
              rw [hFs] at this
              cases this with
              | cons _ h => exact h
            obtain ⟨Ψ', hΨ', hne', hsub'⟩ :=
              evalArgs_ok as hpas Fs' c' {φ | φ ∈ Ψ ∧ F.bind φ ∈ J} hc' ⟨χ, hχ, hT⟩ hall'
            refine ⟨Ψ', ?_, hne', fun φ hφ => (hsub' hφ).1⟩
            simp only [evalArgs, hJeq, hΨ']
end

/-- **On values with no row on any node, HE's check is the machine's**: it
succeeds exactly where some typing of the value meets the formal. -/
theorem check_iff (v : Val) (hv : Plain v) (E : TySet) : (heCheck v E).isSome ↔ Accepts v E := by
  constructor
  · intro h
    obtain ⟨E', hE'⟩ := Option.isSome_iff_exists.mp h
    unfold heCheck at hE'
    cases hm : firstMeet (orUndef (typs v)) E with
    | none => simp [hm] at hE'
    | some S =>
        obtain ⟨hS, hne⟩ := firstMeet_some hm
        exact ⟨S, hS, hne⟩
  · intro h
    obtain ⟨S, hm, hS, hne⟩ := firstMeet_spec h
    have hS' : ∃ S' ∈ orUndef (typs v), (S' ∩ (S ∩ E)).Nonempty := ⟨S, hS, by
      obtain ⟨T, hT⟩ := hne
      exact ⟨T, hT.1, hT⟩⟩
    obtain ⟨E', hE', _, _⟩ := eval_ok v hv (S ∩ E) hS'
    simp [heCheck, hm, hE']

/-- What HE's check leaves lies within the formal. -/
theorem heCheck_within {v : Val} {E E' : TySet} (h : heCheck v E = some E') (hv : Plain v) :
    E'.Nonempty ∧ E' ⊆ E := by
  unfold heCheck at h
  cases hm : firstMeet (orUndef (typs v)) E with
  | none => simp [hm] at h
  | some S =>
      obtain ⟨hS, hne⟩ := firstMeet_some hm
      rw [hm, Option.bind_some] at h
      have hS' : ∃ S' ∈ orUndef (typs v), (S' ∩ (S ∩ E)).Nonempty := ⟨S, hS, by
        obtain ⟨T, hT⟩ := hne
        exact ⟨T, hT.1, hT⟩⟩
      obtain ⟨E'', hE'', hne'', hsub''⟩ := eval_ok v hv (S ∩ E) hS'
      rw [hE''] at h
      cases h
      exact ⟨hne'', fun T hT => (hsub'' hT).2⟩

/-! ## CeTTa's hereditary guard and its memo (`space_type_rows_free_below`)

CeTTa refuses a value unless no type row types any of its expression nodes as an
expression: every expression node has a symbol head whose rows are declarations of
the symbol itself (`rowsFree`). The check walks the value and keeps, per node, the
answer in the type stamp store, keyed by the node's address with its arena and the
arena's epoch, in a store bound to the space's declaration revision.

* `walkRF_eq`: a walk that skips the nodes the store marks answers `rowsFree`
  wherever every mark is sound.
* `rowsFree_below`: the answer is hereditary, so a successful walk may mark every
  node it walked (`mark_after_walk`); with `ShapeTyping.sound_record` and
  `ShapeTyping.validated_hit` the address store stays sound across allocation and
  arena resets.
* `bindScope_sound`: a store cleared whenever the declaration revision changes is
  sound for the current declarations; the per-symbol cache of heads with
  expression rows is cleared with it.
* `plain_of_rowsFree`: a reading of an admitted value whose nodes carry their
  heads' expression rows is `Plain`, so `check_iff` gives HE's check there. The
  reading takes heads typed by function types; a head with a value type adds
  tuple typings, which the model does not read. -/

section RowsFree

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

mutual
/-- **CeTTa's hereditary guard**: every expression node has a symbol head that no
type row types as an expression. -/
def rowsFree (typesExpr : String → Bool) : Atom → Bool
  | .expression [] => true
  | .expression (.symbol h :: rest) => !typesExpr h && rowsFreeAll typesExpr rest
  | .expression (_ :: _) => false
  | _ => true
/-- The guard on the elements after a head. -/
def rowsFreeAll (typesExpr : String → Bool) : List Atom → Bool
  | [] => true
  | x :: xs => rowsFree typesExpr x && rowsFreeAll typesExpr xs
end

mutual
/-- **The walk**: a node the store marks is skipped with its subtree. -/
def walkRF (typesExpr : String → Bool) (marked : Atom → Bool) : Atom → Bool
  | .expression [] => true
  | .expression (.symbol h :: rest) =>
      marked (.expression (.symbol h :: rest)) || (!typesExpr h && walkRFAll typesExpr marked rest)
  | .expression (_ :: _) => false
  | _ => true
/-- The walk of the elements after a head. -/
def walkRFAll (typesExpr : String → Bool) (marked : Atom → Bool) : List Atom → Bool
  | [] => true
  | x :: xs => walkRF typesExpr marked x && walkRFAll typesExpr marked xs
end

mutual
/-- **A walk over sound marks answers the guard.** -/
theorem walkRF_eq (typesExpr : String → Bool) (marked : Atom → Bool)
    (sound : ∀ t, marked t = true → rowsFree typesExpr t = true) :
    ∀ t, walkRF typesExpr marked t = rowsFree typesExpr t
  | .expression [] => rfl
  | .expression (.symbol h :: rest) => by
      simp only [walkRF, rowsFree, walkRFAll_eq typesExpr marked sound rest]
      cases hm : marked (.expression (.symbol h :: rest))
      · rfl
      · have := sound _ hm
        simp only [rowsFree] at this
        simp [this]
  | .expression (.var _ :: _) => rfl
  | .expression (.grounded _ :: _) => rfl
  | .expression (.expression _ :: _) => rfl
  | .symbol _ => rfl
  | .var _ => rfl
  | .grounded _ => rfl
theorem walkRFAll_eq (typesExpr : String → Bool) (marked : Atom → Bool)
    (sound : ∀ t, marked t = true → rowsFree typesExpr t = true) :
    ∀ xs, walkRFAll typesExpr marked xs = rowsFreeAll typesExpr xs
  | [] => rfl
  | x :: xs => by
      simp only [walkRFAll, rowsFreeAll, walkRF_eq typesExpr marked sound x,
        walkRFAll_eq typesExpr marked sound xs]
end

/-- A node at or below another: the node itself, or one below an element. -/
inductive Below : Atom → Atom → Prop
  | refl (t : Atom) : Below t t
  | elem {u x : Atom} {xs : List Atom} : x ∈ xs → Below u x → Below u (.expression xs)

theorem rowsFreeAll_mem {typesExpr : String → Bool} :
    ∀ {xs : List Atom}, rowsFreeAll typesExpr xs = true → ∀ x ∈ xs, rowsFree typesExpr x = true
  | [], _, _, hx => absurd hx List.not_mem_nil
  | y :: ys, h, x, hx => by
      simp only [rowsFreeAll, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h.1
      · exact rowsFreeAll_mem h.2 x hx

/-- **The guard is hereditary**: every node below a value it admits is admitted. -/
theorem rowsFree_below {typesExpr : String → Bool} {u t : Atom} (hb : Below u t)
    (ht : rowsFree typesExpr t = true) : rowsFree typesExpr u = true := by
  induction hb with
  | refl => exact ht
  | @elem x xs hx _ ih =>
      apply ih
      match xs, hx, ht with
      | .symbol h :: rest, hx, ht =>
          simp only [rowsFree, Bool.and_eq_true] at ht
          rcases List.mem_cons.mp hx with rfl | hx
          · rfl
          · exact rowsFreeAll_mem ht.2 x hx
      | .var _ :: _, _, ht => simp [rowsFree] at ht
      | .grounded _ :: _, _, ht => simp [rowsFree] at ht
      | .expression _ :: _, _, ht => simp [rowsFree] at ht

/-- **A successful walk may mark every node below its root**: over sound marks,
each such node is admitted by the guard. -/
theorem mark_after_walk {typesExpr : String → Bool} {marked : Atom → Bool}
    (sound : ∀ t, marked t = true → rowsFree typesExpr t = true) {t u : Atom}
    (walked : walkRF typesExpr marked t = true) (hb : Below u t) : rowsFree typesExpr u = true :=
  rowsFree_below hb (by rwa [← walkRF_eq typesExpr marked sound t])

/-- A store bound to a declaration revision. -/
structure ScopedStore (Addr : Type) where
  revision : ℕ
  memo : ShapeTyping.AddrMemo Addr Bool

/-- **Binding the store** (`type_stamps_bind_scope`): kept for the same revision,
cleared otherwise. -/
def ScopedStore.bind {Addr : Type} (st : ScopedStore Addr) (r : ℕ) : ScopedStore Addr :=
  if st.revision = r then st else ⟨r, fun _ => none⟩

/-- **A store cleared on every change of declarations is sound for the current
ones**: entries kept under revision `r` answer the guard read at `r`. -/
theorem bindScope_sound {Addr : Type} [DecidableEq Addr] (H : ShapeTyping.Heap Addr)
    (typesExprAt : ℕ → String → Bool) (st : ScopedStore Addr)
    (kept : ShapeTyping.Sound H (rowsFree (typesExprAt st.revision)) st.memo) (r : ℕ) :
    ShapeTyping.Sound H (rowsFree (typesExprAt r)) (st.bind r).memo := by
  unfold ScopedStore.bind
  split_ifs with same
  · rw [← same]
    exact kept
  · exact ShapeTyping.sound_empty H _

/-- A reading of atoms as values: leaves by their typings, and an application of a
symbol head by its expression rows, its function types and its read elements. -/
structure Reading where
  leafTyps : Atom → List TySet
  rowsOf : String → List TySet
  fnsOf : String → FnTy × List FnTy

mutual
/-- The value an atom reads as. -/
def Reading.read (ρ : Reading) : Atom → Val
  | .expression (.symbol h :: rest) => .node (ρ.rowsOf h) (ρ.fnsOf h).1 (ρ.fnsOf h).2 (ρ.readAll rest)
  | t => .leaf (ρ.leafTyps t)
/-- The values elements read as. -/
def Reading.readAll (ρ : Reading) : List Atom → List Val
  | [] => []
  | x :: xs => ρ.read x :: ρ.readAll xs
end

mutual
/-- **An admitted value reads as a value with no row on any node**, where a head no
row types as an expression has no rows in the reading. -/
theorem plain_of_rowsFree (ρ : Reading) (typesExpr : String → Bool)
    (rows : ∀ h, typesExpr h = false → ρ.rowsOf h = []) :
    ∀ t, rowsFree typesExpr t = true → Plain (ρ.read t)
  | .expression [], _ => by simp [Reading.read, Plain]
  | .expression (.symbol h :: rest), ht => by
      simp only [rowsFree, Bool.and_eq_true, Bool.not_eq_true'] at ht
      simp only [Reading.read, Plain]
      exact ⟨rows h ht.1, plainAll_of_rowsFree ρ typesExpr rows rest ht.2⟩
  | .expression (.var _ :: _), ht => by simp [rowsFree] at ht
  | .expression (.grounded _ :: _), ht => by simp [rowsFree] at ht
  | .expression (.expression _ :: _), ht => by simp [rowsFree] at ht
  | .symbol _, _ => by simp [Reading.read, Plain]
  | .var _, _ => by simp [Reading.read, Plain]
  | .grounded _, _ => by simp [Reading.read, Plain]
theorem plainAll_of_rowsFree (ρ : Reading) (typesExpr : String → Bool)
    (rows : ∀ h, typesExpr h = false → ρ.rowsOf h = []) :
    ∀ xs, rowsFreeAll typesExpr xs = true → PlainArgs (ρ.readAll xs)
  | [], _ => by simp [Reading.readAll, PlainArgs]
  | x :: xs, h => by
      simp only [rowsFreeAll, Bool.and_eq_true] at h
      simp only [Reading.readAll, PlainArgs]
      exact ⟨plain_of_rowsFree ρ typesExpr rows x h.1, plainAll_of_rowsFree ρ typesExpr rows xs h.2⟩
end

/-- **The guard closes the R11 class**: on every value it admits, HE's check
succeeds exactly where the machine's does. -/
theorem admitted_check_iff (ρ : Reading) (typesExpr : String → Bool)
    (rows : ∀ h, typesExpr h = false → ρ.rowsOf h = []) (t : Atom)
    (admitted : rowsFree typesExpr t = true) (E : TySet) :
    (heCheck (ρ.read t) E).isSome ↔ Accepts (ρ.read t) E :=
  check_iff (ρ.read t) (plain_of_rowsFree ρ typesExpr rows t admitted) E

end RowsFree

/-! ## Controls -/

namespace Controls

/-- `(List x)` at a ground type. -/
def gList (x : Ty Empty) : Ty Empty := .app [.sym "List", x]

/-- The instances of `(List $t)`. -/
def lists : TySet := {T | ∃ x, T = gList x}

/-- `1`: a number. -/
def one : Val := .leaf [{.sym "Number"}]

/-- `Nil`, typed `(List $a)`. -/
def nil : Val := .leaf [lists]

/-- `(: Wrap (-> Number W))`. -/
def wrapFn : FnTy := ([.sym "Number"], .sym "W")

/-- `(: Cons (-> $a (List $a) (List $a)))`. -/
def consFn : FnTy := ([.var "a", .app [.sym "List", .var "a"]], .app [.sym "List", .var "a"])

/-- `(Wrap 1)` with the row `(: (Wrap 1) Foo)`. -/
def wrapRow : Val := .node [{.sym "Foo"}] wrapFn [] [one]

/-- `(Cons (Wrap 1) Nil)`: no row on its top node. -/
def value : Val := .node [] consFn [] [wrapRow, nil]

/-- `(List Foo)`, the typing the row gives the list. -/
def listFoo : TySet := readAt consFn.2 (pathSols consFn.1 consFn.2 [{.sym "Foo"}, lists] Set.univ)

/-- The assignment `$a := Foo`. -/
def aFoo : Asg := fun _ => .sym "Foo"

theorem aFoo_sols (E : TySet) (hE : gList (.sym "Foo") ∈ E) :
    aFoo ∈ pathSols consFn.1 consFn.2 [{.sym "Foo"}, lists] E := by
  refine ⟨.cons rfl (.cons ⟨.sym "Foo", rfl⟩ .nil), hE⟩

theorem foo_mem_listFoo : gList (.sym "Foo") ∈ listFoo :=
  ⟨aFoo, aFoo_sols _ trivial, rfl⟩

theorem foo_mem_lists : gList (.sym "Foo") ∈ lists := ⟨_, rfl⟩

/-- The typings of `(Cons (Wrap 1) Nil)` begin with the row's `(List Foo)`. -/
theorem value_typs_head : (orUndef (typs value)).head? = some listFoo := rfl

/-- Its first path takes `Cons` through the row's `Foo`. -/
theorem value_paths_head :
    (paths [consFn] (argTyps [wrapRow, nil])).head? = some (consFn, [{.sym "Foo"}, lists]) := rfl

theorem value_accepts : Accepts value lists := by
  obtain ⟨_, hm, hS, _⟩ := firstMeet_spec (ts := orUndef (typs value)) (E := lists)
    ⟨listFoo, List.mem_of_mem_head? value_typs_head, _, foo_mem_listFoo, foo_mem_lists⟩
  exact ⟨_, (firstMeet_some hm).1, (firstMeet_some hm).2⟩

/-- `(Wrap 1)` evaluated at a set within `Foo` is an error: `Wrap`'s only path
gives `W`. -/
theorem wrapRow_eval {J : TySet} (hJ : J ⊆ {.sym "Foo"}) : eval wrapRow J = none := by
  classical
  have hnone : firstPath [wrapFn] (argTyps [one]) J = none := by
    unfold firstPath
    rw [List.find?_eq_none]
    intro p hp hpred
    have hp' : (pathSols p.1.1 p.1.2 p.2 J).Nonempty := by simpa using hpred
    have hp1 : p.1 = wrapFn := by
      simp only [paths, List.mem_flatMap, List.mem_map, List.mem_singleton] at hp
      obtain ⟨g, rfl, c, _, rfl⟩ := hp
      rfl
    obtain ⟨ψ, _, hR⟩ := hp'
    rw [hp1] at hR
    have := hJ hR
    simp [wrapFn] at this
  rw [wrapRow, eval_node, hnone]

/-- **HE's check of `(Cons (Wrap 1) Nil)` at `(List $t)` fails**: the row binds
`$t` to `Foo` and `(Wrap 1)` is then evaluated at `Foo`. -/
theorem value_check : heCheck value lists = none := by
  have hm : firstMeet (orUndef (typs value)) lists = some listFoo :=
    firstMeet_of_head value_typs_head ⟨_, foo_mem_listFoo, foo_mem_lists⟩
  have hpath : firstPath [consFn] (argTyps [wrapRow, nil]) (listFoo ∩ lists) =
      some (consFn, [{.sym "Foo"}, lists]) :=
    firstPath_of_head value_paths_head ⟨aFoo, aFoo_sols _ ⟨foo_mem_listFoo, foo_mem_lists⟩⟩
  unfold heCheck
  rw [hm, Option.bind_some, value, eval_node, hpath]
  dsimp only
  rw [show consFn.1 = [.var "a", .app [.sym "List", .var "a"]] from rfl, evalArgs_cons]
  split
  · rfl
  · rename_i J heq
    rw [wrapRow_eval] at heq
    · cases heq
    · rintro _ ⟨ψ, hψ, rfl⟩
      cases hψ.1 with
      | cons h _ => exact h

/-- **Refutation of the top-head guard**: a value with no row on its top node
whose typing the machine accepts and HE's check rejects. -/
theorem top_guard_insufficient : ∃ v E, TopPlain v ∧ Accepts v E ∧ heCheck v E = none :=
  ⟨value, lists, rfl, value_accepts, value_check⟩

/-- `(Cons 1 Nil)` with the row `(: (Cons 1 Nil) (List Foo))` on its top node:
the case CeTTa's guard refuses. -/
def topRow : Val := .node [{gList (.sym "Foo")}] consFn [] [one, nil]

theorem top_row : Accepts topRow lists ∧ heCheck topRow lists = none := by
  classical
  have hhead : (orUndef (typs topRow)).head? = some {gList (.sym "Foo")} := rfl
  have hne : ({gList (.sym "Foo")} ∩ lists).Nonempty := ⟨gList (.sym "Foo"), rfl, foo_mem_lists⟩
  have hm : firstMeet (orUndef (typs topRow)) lists = some {gList (.sym "Foo")} :=
    firstMeet_of_head hhead hne
  refine ⟨⟨_, (firstMeet_some hm).1, hne⟩, ?_⟩
  have hnone : firstPath [consFn] (argTyps [one, nil]) ({gList (.sym "Foo")} ∩ lists) = none := by
    unfold firstPath
    rw [List.find?_eq_none]
    intro p hp hpred
    have hp' : (pathSols p.1.1 p.1.2 p.2 ({gList (.sym "Foo")} ∩ lists)).Nonempty := by
      simpa using hpred
    have hp1 : p = (consFn, [{.sym "Number"}, lists]) := by
      simpa [paths, argTyps, orUndef, typs, one, nil, choices] using hp
    subst hp1
    obtain ⟨ψ, hargs, hR⟩ := hp'
    have ha : ψ "a" = .sym "Number" := by
      cases hargs with
      | cons h1 _ => simpa using h1
    have hb : (Ty.app [.sym "List", .var "a"] : Ty String).bind ψ = gList (.sym "Foo") := hR.1
    simp [ha, gList] at hb
  unfold heCheck
  rw [hm, Option.bind_some, topRow, eval_node, hnone]

section HE

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.LanguageDef.Collections.HECorrespondence.Interpreter (symbol apply equation typed)
open Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HETypedRuleControls (arrowAtom answersWith)
open Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEReturns.Controls (num)
open Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ImpliedMeets.Controls (listA)

/-- `(Wrap 1)`. -/
def wrap1 : Atom := apply "Wrap" [num 1]

/-- `(Cons (Wrap 1) Nil)`. -/
def cellW : Atom := apply "Cons" [wrap1, symbol "Nil"]

/-- The list rows, `(: Wrap (-> Number W))`, `(: g (-> (List $t) Number))` and
`(= (g $l) 7)`, with the row `(: (Wrap 1) Foo)` when `row` holds. -/
def innerSpace (row : Bool) : Space := Space.ofList (
  [typed "Nil" (listA (.var "a")),
   typed "Cons" (arrowAtom [.var "a", listA (.var "a"), listA (.var "a")]),
   typed "Wrap" (arrowAtom [symbol "Number", symbol "W"])] ++
  (if row then [.expression [symbol ":", wrap1, symbol "Foo"]] else []) ++
  [typed "g" (arrowAtom [listA (.var "t"), symbol "Number"]),
   equation (apply "g" [.var "l"]) (num 7)])

/-- Rust's answer to `(g (Cons (Wrap 1) Nil))` with the row. -/
def innerError : Atom := .expression [symbol "Error", wrap1,
  .expression [symbol "BadType", symbol "Foo", symbol "W"]]

/-- **HE's interpreter reproduces the inner row's error**: with the row,
`(g (Cons (Wrap 1) Nil))` is `(Error (Wrap 1) (BadType Foo W))` at budgets 24
and 40, Rust's answer; without it, `7`. -/
theorem inner_row_he :
    answersWith (innerSpace true) (apply "g" [cellW]) 24 = [innerError] ∧
      answersWith (innerSpace true) (apply "g" [cellW]) 40 = [innerError] ∧
      answersWith (innerSpace false) (apply "g" [cellW]) 24 = [num 7] ∧
      answersWith (innerSpace false) (apply "g" [cellW]) 40 = [num 7] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

end HE

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ValueRows
