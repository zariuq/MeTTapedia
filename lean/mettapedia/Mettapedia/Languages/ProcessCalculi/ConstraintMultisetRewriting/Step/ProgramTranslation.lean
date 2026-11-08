import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramRows
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Semantic

/-!
# Schemas of row rewriting, and their firings on the step

A **schema** has take patterns, read patterns and made terms (`Schema`). It rewrites a multiset of
rows (`Schema.Fires`): an instance of its take and read patterns is found among the rows, the taken
rows are replaced by the made terms, and the read rows stay. A program is a family of schemas, and
its source reductions are `Rewrites`.

On the step, the schema's **instance at scope `n`** copies every pattern into the fresh scope `n`
(`Schema.rule`); its firing takes and reads selected occurrences and makes new ones carrying the
made terms (`Schema.firing`). It has no guard and no predicate query, so it is a firing of the
ordinary step (`firing_isSemantic`, `translated_admitted`). Each firing uses the next scope
(`Translated`), and the equation store keeps every take and read equation.

## Adequacy

A configuration **represents** rows (`Represents`) when its knowledge is consistent, and at every
solution each present occurrence reads as one fixed row. The rows are read through solutions: a
made occurrence's label is the made term at its scope, an open term the store determines.

* **Soundness** (`sound`): every source rewrite from represented rows is matched by one admitted
  firing of the same schema, whose result represents the rewritten rows.
* **Completeness** (`complete`): every admitted firing of a schema instance from represented rows is
  the image of a source rewrite, and its result represents the rewritten rows. There are no
  administrative firings: each firing is one source rewrite.
* **Runs** (`execution_iff`): from the initial configuration of a list of rows, the source rewrites
  reach `W` exactly when a run of translated firings reaches a configuration representing `W`.
  Represented rows are unique (`represents_unique`).

The schemas are well formed (`Schema.WellFormed`): every made variable is matched by a take or read
pattern, and there is at most one read pattern, so read selections are distinct.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramTranslation

open Mettapedia.Logic.LP
open ProgramRows
open AnnotatedRuns

/-- An occurrence of the step: its label, and the scope and position of the firing that made it. -/
structure Occ where
  label : Tm
  scope : ℕ
  index : ℕ

noncomputable instance : DecidableEq Occ := Classical.decEq _

/-- The first-order unifier on rows. -/
abbrev A : SubstitutionAction Tm (Subst rows) := FirstOrder.action rows

/-- Configurations of the step over rows. -/
abbrev Config := Configuration Tm Occ

/-- Rows in front of a multiset, in order. -/
def push (l : List Sx) (rest : Multiset Sx) : Multiset Sx := l.foldr (· ::ₘ ·) rest

theorem push_eq (l : List Sx) (rest : Multiset Sx) : push l rest = (l : Multiset Sx) + rest := by
  induction l with
  | nil => simp [push]
  | cons a l ih =>
      show a ::ₘ push l rest = _
      rw [ih, ← Multiset.cons_coe, Multiset.cons_add]

/-- A rule schema: take patterns, read patterns and made terms. -/
structure Schema where
  take : List Pat
  read : List Pat
  make : List Pat

namespace Schema

/-- **A schema rewrites rows**: an instance of its take and read patterns among the rows; the taken
rows are replaced by the made terms, and the read rows stay. -/
def Fires (r : Schema) (W W' : Multiset Sx) : Prop :=
  ∃ (θ : ℕ → Sx) (F : Multiset Sx),
    W = push (r.take.map (Pat.inst θ)) (push (r.read.map (Pat.inst θ)) F) ∧
    W' = push (r.make.map (Pat.inst θ)) (push (r.read.map (Pat.inst θ)) F)

/-- Every made variable is matched by a take or read pattern, and there is at most one read
pattern. -/
structure WellFormed (r : Schema) : Prop where
  covered : ∀ q ∈ r.make, ∀ x ∈ q.vars, ∃ p ∈ r.take ++ r.read, x ∈ p.vars
  single_read : r.read.length ≤ 1

/-- The rule instance at scope `n`: every pattern copied into the fresh scope. -/
def rule (r : Schema) (n : ℕ) : RuleInstance Tm :=
  ⟨r.take.map (Pat.at n), r.read.map (Pat.at n), [], [], r.make.map (Pat.at n)⟩

end Schema

/-- The made occurrences of a firing at scope `n`. -/
def madeAt (n : ℕ) : ℕ → List Pat → List Occ
  | _, [] => []
  | i, q :: qs => ⟨q.at n, n, i⟩ :: madeAt n (i + 1) qs

theorem madeAt_mem {n : ℕ} : ∀ {i : ℕ} {qs : List Pat} {o : Occ}, o ∈ madeAt n i qs →
    o.scope = n ∧ i ≤ o.index ∧ ∃ q ∈ qs, o.label = q.at n
  | _, [], _, h => absurd h List.not_mem_nil
  | i, q :: qs, o, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨rfl, le_rfl, q, List.mem_cons_self, rfl⟩
      · obtain ⟨scope, index, p, member, label⟩ := madeAt_mem h
        exact ⟨scope, Nat.le_of_succ_le index, p, List.mem_cons_of_mem _ member, label⟩

theorem madeAt_nodup (n : ℕ) : ∀ (i : ℕ) (qs : List Pat), (madeAt n i qs).Nodup
  | _, [] => List.nodup_nil
  | i, q :: qs => List.nodup_cons.mpr ⟨fun h => by
      have := (madeAt_mem h).2.1
      exact Nat.not_succ_le_self i this, madeAt_nodup n (i + 1) qs⟩

theorem madeAt_label (n : ℕ) : ∀ (i : ℕ) (qs : List Pat), (madeAt n i qs).map Occ.label = qs.map (Pat.at n)
  | _, [] => rfl
  | i, q :: qs => congrArg (q.at n :: ·) (madeAt_label n (i + 1) qs)

/-- The firing of a schema instance at scope `n` on selected occurrences. -/
def Schema.firing (r : Schema) (n : ℕ) (taken read : List Occ) : Firing Tm (Subst rows) Occ :=
  ⟨r.rule n, [], ⟨taken, read, madeAt n 0 r.make⟩⟩

/-- **Translated firings are firings of the ordinary step**: they have no predicate query. -/
theorem firing_isSemantic (r : Schema) (n : ℕ) (taken read : List Occ) :
    Semantic.IsSemantic A (r.firing n taken read) :=
  Semantic.isSemantic_of_queries_nil rfl

/-! ## Representation -/

/-- **A configuration represents rows** below scope `n`: its knowledge is consistent and names only
scopes below `n`; its present occurrences were made below `n`; at every solution each present
occurrence reads as one fixed row; and these rows are `W`. -/
def Represents (C : Config) (W : Multiset Sx) (n : ℕ) : Prop :=
  A.Consistent C.equations ∧
  (∀ e ∈ C.equations, Bounded n e.1 ∧ Bounded n e.2) ∧
  (∀ o ∈ C.present, o.scope < n ∧ Bounded n o.label) ∧
  ∃ value : Occ → Sx,
    (∀ σ, A.Models σ C.equations → ∀ o ∈ C.present, σ.applyTerm o.label = embed (value o)) ∧
    C.present.val.map value = W

/-- **Represented rows are unique.** -/
theorem represents_unique {C : Config} {W W' : Multiset Sx} {n m : ℕ}
    (one : Represents C W n) (two : Represents C W' m) : W = W' := by
  obtain ⟨⟨σ, solved⟩, -, -, value, observed, rfl⟩ := one
  obtain ⟨-, -, -, value', observed', rfl⟩ := two
  refine Multiset.map_congr rfl fun o member => embed_injective ?_
  rw [← observed σ solved o member, ← observed' σ solved o member]

/-! ## Selection bookkeeping -/

theorem pick (value : Occ → Sx) : ∀ (L : List Sx) (s : Finset Occ) (F : Multiset Sx),
    s.val.map value = (L : Multiset Sx) + F →
      ∃ os : List Occ, os.Nodup ∧ (∀ o ∈ os, o ∈ s) ∧ os.map value = L ∧
        (s \ os.toFinset).val.map value = F
  | [], s, F, h => ⟨[], List.nodup_nil, fun _ h => absurd h List.not_mem_nil, rfl, by simpa using h⟩
  | a :: L, s, F, h => by
      have mem : a ∈ s.val.map value := by rw [h]; simp
      obtain ⟨o, oIn, rfl⟩ := Multiset.mem_map.mp mem
      have split : (s.erase o).val.map value = (L : Multiset Sx) + F := by
        have hs : s.val = o ::ₘ (s.erase o).val := by rw [Finset.erase_val, Multiset.cons_erase oIn]
        rw [hs, Multiset.map_cons, ← Multiset.cons_coe, Multiset.cons_add] at h
        exact (Multiset.cons_inj_right _).mp h
      obtain ⟨os, nodup, inside, values, rest⟩ := pick value L (s.erase o) F split
      refine ⟨o :: os, List.nodup_cons.mpr ⟨fun h => Finset.notMem_erase o s (inside o h), nodup⟩, ?_,
        by simp [values], ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact oIn
        · exact Finset.mem_of_mem_erase (inside x hx)
      · rw [List.toFinset_cons, Finset.sdiff_insert, ← Finset.erase_sdiff_comm]
        exact rest

theorem split_off (value : Occ → Sx) : ∀ (os : List Occ) (s : Finset Occ), os.Nodup → (∀ o ∈ os, o ∈ s) →
    s.val.map value = ((os.map value : List Sx) : Multiset Sx) + (s \ os.toFinset).val.map value
  | [], s, _, _ => by simp
  | o :: os, s, nodup, inside => by
      obtain ⟨notIn, nodup'⟩ := List.nodup_cons.mp nodup
      have oIn : o ∈ s := inside o List.mem_cons_self
      have inside' : ∀ x ∈ os, x ∈ s.erase o := fun x hx =>
        Finset.mem_erase.mpr ⟨fun same => notIn (same ▸ hx), inside x (List.mem_cons_of_mem _ hx)⟩
      have hs : s.val = o ::ₘ (s.erase o).val := by rw [Finset.erase_val, Multiset.cons_erase oIn]
      rw [hs, Multiset.map_cons, split_off value os (s.erase o) nodup' inside', List.map_cons,
        ← Multiset.cons_coe, Multiset.cons_add, List.toFinset_cons, Finset.sdiff_insert,
        ← Finset.erase_sdiff_comm]

theorem forall₂_of_map_eq {θ : ℕ → Sx} {value : Occ → Sx} :
    ∀ {ps : List Pat} {os : List Occ}, os.map value = ps.map (Pat.inst θ) →
      List.Forall₂ (fun p o => p.inst θ = value o) ps os
  | [], [], _ => .nil
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | p :: ps, o :: os, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      exact .cons h.1.symm (forall₂_of_map_eq h.2)

theorem map_eq_of_forall₂ {θ : ℕ → Sx} {value : Occ → Sx} :
    ∀ {ps : List Pat} {os : List Occ}, List.Forall₂ (fun p o => p.inst θ = value o) ps os →
      os.map value = ps.map (Pat.inst θ)
  | _, _, .nil => rfl
  | _, _, .cons head rest => by
      simp only [List.map_cons, head, map_eq_of_forall₂ rest]

theorem forall₂_both {α β : Type*} {R S : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → List.Forall₂ S l₁ l₂ →
      List.Forall₂ (fun a b => R a b ∧ S a b) l₁ l₂
  | _, _, .nil, .nil => .nil
  | _, _, .cons r rs, .cons s ss => .cons ⟨r, s⟩ (forall₂_both rs ss)

theorem forall₂_imp_mem {α β : Type*} {R S : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → (∀ a b, b ∈ l₂ → R a b → S a b) →
      List.Forall₂ S l₁ l₂
  | _, _, .nil, _ => .nil
  | _, _, .cons r rs, imp => .cons (imp _ _ List.mem_cons_self r)
      (forall₂_imp_mem rs fun a b member related => imp a b (List.mem_cons_of_mem _ member) related)

theorem forall₂_mem_left {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b ∈ l₂, R a b
  | _, _, .nil, _, h => absurd h List.not_mem_nil
  | _, _, .cons (b := b) r rs, a, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨b, List.mem_cons_self, r⟩
      · obtain ⟨c, member, related⟩ := forall₂_mem_left rs a h
        exact ⟨c, List.mem_cons_of_mem _ member, related⟩

theorem mem_equations : ∀ {ps : List Tm} {os : List Occ} {e : Tm × Tm},
    e ∈ Selection.equations (T := Tm) Occ.label ps os → ∃ p ∈ ps, ∃ o ∈ os, e = (p, o.label)
  | [], _, _, h => by simp [Selection.equations] at h
  | _ :: _, [], _, h => by simp [Selection.equations] at h
  | p :: ps, o :: os, e, h => by
      simp only [Selection.equations, List.zipWith_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨p, List.mem_cons_self, o, List.mem_cons_self, rfl⟩
      · obtain ⟨p', member, o', member', rfl⟩ := mem_equations (ps := ps) (os := os) h
        exact ⟨p', List.mem_cons_of_mem _ member, o', List.mem_cons_of_mem _ member', rfl⟩

theorem models_take_iff (σ : Subst rows) {ps : List Pat} {os : List Occ} (n : ℕ)
    (lengths : (ps.map (Pat.at n)).length = os.length) :
    A.Models σ (Selection.equations (T := Tm) Occ.label (ps.map (Pat.at n)) os) ↔
      List.Forall₂ (fun p o => σ.applyTerm (p.at n) = σ.applyTerm o.label) ps os := by
  rw [Selection.models_equations_iff A σ Occ.label lengths, List.forall₂_map_left_iff]
  rfl

/-! ## The firing of a schema instance -/

/-- **The core of both directions**: on selected occurrences whose rows are an instance of the take
and read patterns, the schema's firing at a fresh scope is admitted, and its result represents the
made rows in place of the taken ones. -/
theorem fire_at {C : Config} {n : ℕ} {r : Schema} (wf : r.WellFormed)
    (consistent : A.Consistent C.equations)
    (eqs : ∀ e ∈ C.equations, Bounded n e.1 ∧ Bounded n e.2)
    (pres : ∀ o ∈ C.present, o.scope < n ∧ Bounded n o.label)
    {value : Occ → Sx}
    (observed : ∀ σ, A.Models σ C.equations → ∀ o ∈ C.present, σ.applyTerm o.label = embed (value o))
    (θ : ℕ → Sx) {taken read : List Occ}
    (takenNodup : taken.Nodup) (takenIn : ∀ o ∈ taken, o ∈ C.present)
    (readIn : ∀ o ∈ read, o ∈ C.present) (apart : ∀ o ∈ taken, o ∉ read)
    (takeMatch : List.Forall₂ (fun p o => p.inst θ = value o) r.take taken)
    (readMatch : List.Forall₂ (fun p o => p.inst θ = value o) r.read read) :
    (r.firing n taken read).Valid A Occ.label C ∧
      Represents ((r.firing n taken read).result Occ.label C)
        (push (r.make.map (Pat.inst θ)) ((C.present \ taken.toFinset).val.map value)) (n + 1) := by
  classical
  obtain ⟨σ, solved⟩ := consistent
  let τ : Subst rows := fun v => if v.1 = n then embed (θ v.2) else σ v
  have below : ∀ v : ℕ × ℕ, v.1 < n → τ v = σ v := fun v lt => if_neg (Nat.ne_of_lt lt)
  have τAt : ∀ p : Pat, τ.applyTerm (p.at n) = embed (p.inst θ) := fun p =>
    apply_at p fun x _ => if_pos rfl
  have τOld : ∀ o ∈ C.present, τ.applyTerm o.label = embed (value o) := fun o member => by
    rw [apply_bounded (pres o member).2 below]
    exact observed σ solved o member
  have takeLength : (r.take.map (Pat.at n)).length = taken.length := by
    rw [List.length_map]; exact takeMatch.length_eq
  have readLength : (r.read.map (Pat.at n)).length = read.length := by
    rw [List.length_map]; exact readMatch.length_eq
  have problem : (r.firing n taken read).selection.problem Occ.label (r.firing n taken read).rule C =
      C.equations ++ Selection.equations (T := Tm) Occ.label (r.take.map (Pat.at n)) taken ++
        Selection.equations (T := Tm) Occ.label (r.read.map (Pat.at n)) read ++ [] := rfl
  have τModels : A.Models τ ((r.firing n taken read).selection.problem Occ.label
      (r.firing n taken read).rule C) := by
    rw [problem]
    simp only [SubstitutionAction.models_append, SubstitutionAction.models_nil, and_true]
    refine ⟨⟨fun e member => ?_, ?_⟩, ?_⟩
    · change τ.applyTerm e.1 = τ.applyTerm e.2
      rw [apply_bounded (eqs e member).1 below, apply_bounded (eqs e member).2 below]
      exact solved e member
    · rw [models_take_iff τ n takeLength]
      exact forall₂_imp_mem takeMatch fun p o member same => by
        rw [τAt, τOld o (takenIn o member)]
        exact congrArg embed same
    · rw [models_take_iff τ n readLength]
      exact forall₂_imp_mem readMatch fun p o member same => by
        rw [τAt, τOld o (readIn o member)]
        exact congrArg embed same
  have disjointMade : ∀ o ∈ madeAt n 0 r.make, o ∉ C.present := fun o made present => by
    have scope := (madeAt_mem made).1
    have lt := (pres o present).1
    omega
  have valid : (r.firing n taken read).Valid A Occ.label C := by
    refine ⟨⟨takenNodup, madeAt_nodup n 0 r.make, takeLength, readLength, madeAt_label n 0 r.make,
      ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨τ, τModels⟩, ?_⟩, ?_⟩
    · intro o h
      exact takenIn o (List.mem_toFinset.mp h)
    · intro o h
      exact readIn o (List.mem_toFinset.mp h)
    · exact Finset.disjoint_left.mpr fun o h₁ h₂ =>
        apart o (List.mem_toFinset.mp h₁) (List.mem_toFinset.mp h₂)
    · exact Finset.disjoint_left.mpr fun o h₁ h₂ => disjointMade o (List.mem_toFinset.mp h₁) h₂
    · intro q h
      simp [Selection.commit] at h
    · intro check h
      simp [Schema.firing, Schema.rule] at h
    · intro query h
      simp [Schema.firing] at h
  let value' : Occ → Sx := fun o => if o.scope = n then decode (τ.applyTerm o.label) else value o
  have valueMade : ∀ (i : ℕ) (qs : List Pat), (madeAt n i qs).map value' = qs.map (Pat.inst θ) := by
    intro i qs
    induction qs generalizing i with
    | nil => rfl
    | cons q qs ih =>
        simp only [madeAt, List.map_cons, ih]
        congr 1
        simp only [value', if_pos rfl, τAt, decode_embed]
  have resultEqs : ((r.firing n taken read).result Occ.label C).equations =
      C.equations ++ Selection.equations (T := Tm) Occ.label (r.take.map (Pat.at n)) taken ++
        Selection.equations (T := Tm) Occ.label (r.read.map (Pat.at n)) read ++ [] := rfl
  have resultPresent : ((r.firing n taken read).result Occ.label C).present =
      (C.present \ taken.toFinset) ∪ (madeAt n 0 r.make).toFinset := rfl
  have oldBounded : ∀ {ps : List Pat} {os : List Occ}, (∀ o ∈ os, o ∈ C.present) →
      ∀ e ∈ Selection.equations (T := Tm) Occ.label (ps.map (Pat.at n)) os,
        Bounded (n + 1) e.1 ∧ Bounded (n + 1) e.2 := by
    intro ps os inside e member
    obtain ⟨p', hp', o, ho, rfl⟩ := mem_equations member
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hp'
    exact ⟨at_bounded n p, (pres o (inside o ho)).2.mono (Nat.le_succ n)⟩
  refine ⟨valid, ⟨τ, τModels⟩, ?_, ?_, value', ?_, ?_⟩
  · intro e member
    rw [resultEqs] at member
    simp only [List.append_nil, List.mem_append] at member
    rcases member with (old | taken') | read'
    · exact ⟨(eqs e old).1.mono (Nat.le_succ n), (eqs e old).2.mono (Nat.le_succ n)⟩
    · exact oldBounded takenIn e taken'
    · exact oldBounded readIn e read'
  · intro o member
    rw [resultPresent, Finset.mem_union, Finset.mem_sdiff] at member
    rcases member with ⟨old, -⟩ | made
    · exact ⟨Nat.lt_succ_of_lt (pres o old).1, (pres o old).2.mono (Nat.le_succ n)⟩
    · obtain ⟨scope, -, q, -, label⟩ := madeAt_mem (List.mem_toFinset.mp made)
      rw [scope, label]
      exact ⟨Nat.lt_succ_self n, at_bounded n q⟩
  · intro σ' models o member
    rw [resultEqs] at models
    simp only [SubstitutionAction.models_append, SubstitutionAction.models_nil, and_true] at models
    obtain ⟨⟨oldModels, takeModels⟩, readModels⟩ := models
    rw [models_take_iff σ' n takeLength] at takeModels
    rw [models_take_iff σ' n readLength] at readModels
    rw [resultPresent, Finset.mem_union, Finset.mem_sdiff] at member
    rcases member with ⟨old, -⟩ | made
    · have scope : o.scope ≠ n := Nat.ne_of_lt (pres o old).1
      simp only [value', if_neg scope]
      exact observed σ' oldModels o old
    · obtain ⟨scope, -, q, qIn, label⟩ := madeAt_mem (List.mem_toFinset.mp made)
      simp only [value', if_pos scope, label, τAt, decode_embed]
      refine apply_at q fun x hx => ?_
      obtain ⟨p, pIn, xIn⟩ := wf.covered q qIn x hx
      have matched : σ'.applyTerm (p.at n) = embed (p.inst θ) := by
        rcases List.mem_append.mp pIn with pIn | pIn
        · obtain ⟨o', o'In, same, solves⟩ := forall₂_mem_left (forall₂_both takeMatch takeModels) p pIn
          rw [solves, observed σ' oldModels o' (takenIn o' o'In), same]
        · obtain ⟨o', o'In, same, solves⟩ := forall₂_mem_left (forall₂_both readMatch readModels) p pIn
          rw [solves, observed σ' oldModels o' (readIn o' o'In), same]
      exact agree_of_apply p matched x xIn
  · have disjoint : Disjoint (C.present \ taken.toFinset) (madeAt n 0 r.make).toFinset :=
      Finset.disjoint_left.mpr fun o h₁ h₂ =>
        disjointMade o (List.mem_toFinset.mp h₂) (Finset.mem_sdiff.mp h₁).1
    rw [resultPresent, ← Finset.disjUnion_eq_union _ _ disjoint]
    change Multiset.map value' ((C.present \ taken.toFinset).val + (madeAt n 0 r.make).toFinset.val) = _
    rw [Multiset.map_add, List.toFinset_val, (madeAt_nodup n 0 r.make).dedup, Multiset.map_coe,
      valueMade, push_eq, add_comm]
    congr 1
    refine Multiset.map_congr rfl fun o member => ?_
    have scope : o.scope ≠ n := Nat.ne_of_lt (pres o (Finset.mem_sdiff.mp member).1).1
    simp only [value', if_neg scope]

/-! ## Adequacy -/

/-- **Soundness**: every source rewrite from represented rows is matched by one admitted firing of
the same schema at the next scope, whose result represents the rewritten rows. -/
theorem sound {C : Config} {W W' : Multiset Sx} {n : ℕ} {r : Schema} (wf : r.WellFormed)
    (rep : Represents C W n) (fires : r.Fires W W') :
    ∃ taken read : List Occ, (r.firing n taken read).Valid A Occ.label C ∧
      Represents ((r.firing n taken read).result Occ.label C) W' (n + 1) := by
  obtain ⟨consistent, eqs, pres, value, observed, image⟩ := rep
  obtain ⟨θ, F, rfl, rfl⟩ := fires
  rw [push_eq, push_eq] at image
  obtain ⟨taken, takenNodup, takenIn, takenValues, rest⟩ :=
    pick value (r.take.map (Pat.inst θ)) C.present _ image
  obtain ⟨read, -, readIn, readValues, -⟩ :=
    pick value (r.read.map (Pat.inst θ)) (C.present \ taken.toFinset) F rest
  have readPresent : ∀ o ∈ read, o ∈ C.present := fun o h => (Finset.mem_sdiff.mp (readIn o h)).1
  have apart : ∀ o ∈ taken, o ∉ read := fun o h h' =>
    (Finset.mem_sdiff.mp (readIn o h')).2 (List.mem_toFinset.mpr h)
  obtain ⟨valid, represents⟩ := fire_at wf consistent eqs pres observed θ takenNodup takenIn readPresent
    apart (forall₂_of_map_eq takenValues) (forall₂_of_map_eq readValues)
  refine ⟨taken, read, valid, ?_⟩
  rwa [rest, ← push_eq] at represents

theorem nodup_of_length_le_one {α : Type*} : ∀ {l : List α}, l.length ≤ 1 → l.Nodup
  | [], _ => List.nodup_nil
  | [_], _ => List.nodup_singleton _
  | _ :: _ :: _, h => by simp at h

/-- **Completeness**: every admitted firing of a schema instance at the next scope from represented
rows is the image of a source rewrite of the same schema, and its result represents the rewritten
rows. -/
theorem complete {C : Config} {W : Multiset Sx} {n : ℕ} {r : Schema} (wf : r.WellFormed)
    (rep : Represents C W n) {taken read : List Occ}
    (valid : (r.firing n taken read).Valid A Occ.label C) :
    ∃ W', r.Fires W W' ∧ Represents ((r.firing n taken read).result Occ.label C) W' (n + 1) := by
  classical
  obtain ⟨consistent, eqs, pres, value, observed, rfl⟩ := rep
  obtain ⟨σ, solved⟩ := valid.firing.consistent
  have problem : (r.firing n taken read).selection.problem Occ.label (r.firing n taken read).rule C =
      C.equations ++ Selection.equations (T := Tm) Occ.label (r.take.map (Pat.at n)) taken ++
        Selection.equations (T := Tm) Occ.label (r.read.map (Pat.at n)) read ++ [] := rfl
  rw [problem] at solved
  simp only [SubstitutionAction.models_append, SubstitutionAction.models_nil, and_true] at solved
  obtain ⟨⟨oldModels, takeModels⟩, readModels⟩ := solved
  have takeLength : (r.take.map (Pat.at n)).length = taken.length := valid.firing.take_length
  have readLength : (r.read.map (Pat.at n)).length = read.length := valid.firing.read_length
  rw [models_take_iff σ n takeLength] at takeModels
  rw [models_take_iff σ n readLength] at readModels
  have takenIn : ∀ o ∈ taken, o ∈ C.present := fun o h =>
    valid.firing.occurrences.taken_subset (List.mem_toFinset.mpr h)
  have readIn : ∀ o ∈ read, o ∈ C.present := fun o h =>
    valid.firing.occurrences.kept_subset (List.mem_toFinset.mpr h)
  have apart : ∀ o ∈ taken, o ∉ read := fun o h h' =>
    Finset.disjoint_left.mp valid.firing.occurrences.apart (List.mem_toFinset.mpr h)
      (List.mem_toFinset.mpr h')
  let θ : ℕ → Sx := fun x => decode (σ (n, x))
  have matched : ∀ {ps : List Pat} {os : List Occ}, (∀ o ∈ os, o ∈ C.present) →
      List.Forall₂ (fun p o => σ.applyTerm (p.at n) = σ.applyTerm o.label) ps os →
        List.Forall₂ (fun p o => p.inst θ = value o) ps os := fun inside models =>
    forall₂_imp_mem models fun p o member same =>
      (match_at p (same.trans (observed σ oldModels o (inside o member)))).1
  have takeMatch := matched takenIn takeModels
  have readMatch := matched readIn readModels
  have takenNodup : taken.Nodup := valid.firing.take_distinct
  obtain ⟨-, represents⟩ := fire_at wf consistent eqs pres observed θ takenNodup takenIn
    readIn apart takeMatch readMatch
  have readNodup : read.Nodup := nodup_of_length_le_one (by
    rw [← readLength, List.length_map]; exact wf.single_read)
  have readRest : ∀ o ∈ read, o ∈ C.present \ taken.toFinset := fun o h =>
    Finset.mem_sdiff.mpr ⟨readIn o h, fun h' => apart o (List.mem_toFinset.mp h') h⟩
  have restSplit := split_off value read (C.present \ taken.toFinset) readNodup readRest
  refine ⟨_, ⟨θ, ((C.present \ taken.toFinset) \ read.toFinset).val.map value, ?_, ?_⟩, represents⟩
  · rw [split_off value taken C.present takenNodup takenIn, restSplit, push_eq, push_eq,
      map_eq_of_forall₂ takeMatch, map_eq_of_forall₂ readMatch]
  · rw [restSplit, push_eq, push_eq, push_eq, map_eq_of_forall₂ readMatch]

/-! ## Runs -/

/-- **Source reductions of a program**: one of its schemas rewrites the rows. -/
def Rewrites {ι : Type*} (schema : ι → Schema) (W W' : Multiset Sx) : Prop := ∃ i, (schema i).Fires W W'

/-- **The translated program**: at scope `n`, an admitted firing of the instance of one of its
schemas at scope `n`; the next firing uses scope `n + 1`. -/
inductive Translated {ι : Type*} (schema : ι → Schema) : Config × ℕ → Config × ℕ → Prop
  | fire {C : Config} {n : ℕ} (i : ι) (taken read : List Occ)
      (valid : ((schema i).firing n taken read).Valid A Occ.label C) :
      Translated schema (C, n) (((schema i).firing n taken read).result Occ.label C, n + 1)

/-- **Every translated firing is an admitted firing of the ordinary step** (R80's `semanticStep`),
with the same result. -/
theorem translated_admitted {ι : Type*} (schema : ι → Schema) (i : ι) (n : ℕ) (taken read : List Occ)
    {C : Config} (valid : ((schema i).firing n taken read).Valid A Occ.label C) :
    ∃ admitted : (Semantic.semanticStep A Occ.label).Admits (s := C)
        ⟨(schema i).firing n taken read, firing_isSemantic _ n taken read⟩,
      (Semantic.semanticStep A Occ.label).result _ admitted =
        ((schema i).firing n taken read).result Occ.label C :=
  ⟨valid, rfl⟩

variable {ι : Type*} {schema : ι → Schema}

theorem path_sound (wf : ∀ i, (schema i).WellFormed) {W W' : Multiset Sx}
    (path : Relation.ReflTransGen (Rewrites schema) W W') {C : Config} {n : ℕ} (rep : Represents C W n) :
    ∃ q : Config × ℕ, Relation.ReflTransGen (Translated schema) (C, n) q ∧ Represents q.1 W' q.2 := by
  induction path with
  | refl => exact ⟨(C, n), .refl, rep⟩
  | tail _ step ih =>
      obtain ⟨⟨C', n'⟩, run, rep'⟩ := ih
      obtain ⟨i, fires⟩ := step
      obtain ⟨taken, read, valid, rep''⟩ := sound (wf i) rep' fires
      exact ⟨_, run.tail (.fire i taken read valid), rep''⟩

theorem path_complete (wf : ∀ i, (schema i).WellFormed) {p q : Config × ℕ}
    (path : Relation.ReflTransGen (Translated schema) p q) {W : Multiset Sx} (rep : Represents p.1 W p.2) :
    ∃ W', Relation.ReflTransGen (Rewrites schema) W W' ∧ Represents q.1 W' q.2 := by
  induction path with
  | refl => exact ⟨W, .refl, rep⟩
  | tail _ step ih =>
      obtain ⟨W', reductions, rep'⟩ := ih
      cases step with
      | fire i taken read valid =>
          obtain ⟨W'', fires, rep''⟩ := complete (wf i) rep' valid
          exact ⟨W'', reductions.tail ⟨i, fires⟩, rep''⟩

/-- The initial occurrences of a list of rows, at scope `0`. -/
def initialRows : ℕ → List Sx → List Occ
  | _, [] => []
  | i, s :: l => ⟨embed s, 0, i⟩ :: initialRows (i + 1) l

theorem initialRows_mem : ∀ {i : ℕ} {l : List Sx} {o : Occ}, o ∈ initialRows i l →
    o.scope = 0 ∧ i ≤ o.index ∧ ∃ s ∈ l, o.label = embed s
  | _, [], _, h => absurd h List.not_mem_nil
  | i, s :: l, o, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨rfl, le_rfl, s, List.mem_cons_self, rfl⟩
      · obtain ⟨scope, index, s', member, label⟩ := initialRows_mem h
        exact ⟨scope, Nat.le_of_succ_le index, s', List.mem_cons_of_mem _ member, label⟩

theorem initialRows_nodup : ∀ (i : ℕ) (l : List Sx), (initialRows i l).Nodup
  | _, [] => List.nodup_nil
  | i, _ :: l => List.nodup_cons.mpr ⟨fun h => Nat.not_succ_le_self i (initialRows_mem h).2.1,
      initialRows_nodup (i + 1) l⟩

/-- The initial configuration of a list of rows: no equations, one occurrence per row. -/
noncomputable def initial (l : List Sx) : Config := ⟨[], (initialRows 0 l).toFinset⟩

theorem initial_represents (l : List Sx) : Represents (initial l) (l : Multiset Sx) 1 := by
  refine ⟨⟨Subst.id rows, SubstitutionAction.models_nil A _⟩, fun e h => absurd h List.not_mem_nil,
    ?_, fun o => decode o.label, ?_, ?_⟩
  · intro o member
    obtain ⟨scope, -, s, -, label⟩ := initialRows_mem (List.mem_toFinset.mp member)
    rw [scope, label]
    exact ⟨Nat.zero_lt_one, embed_bounded 1 s⟩
  · intro σ _ o member
    obtain ⟨-, -, s, -, label⟩ := initialRows_mem (List.mem_toFinset.mp member)
    show σ.applyTerm o.label = embed (decode o.label)
    rw [label, apply_embed, decode_embed]
  · change Multiset.map _ (initialRows 0 l).toFinset.val = _
    rw [List.toFinset_val, (initialRows_nodup 0 l).dedup, Multiset.map_coe]
    congr 1
    suffices ∀ i, (initialRows i l).map (fun o => decode o.label) = l from this 0
    induction l with
    | nil => intro i; rfl
    | cons s l ih =>
        intro i
        simp only [initialRows, List.map_cons, decode_embed, ih]

/-- **Adequacy for runs.** From the initial configuration of a list of rows, the source reductions
reach `W` exactly when a run of translated firings reaches a configuration representing `W`. -/
theorem execution_iff (wf : ∀ i, (schema i).WellFormed) (l : List Sx) (W : Multiset Sx) :
    Relation.ReflTransGen (Rewrites schema) (l : Multiset Sx) W ↔
      ∃ q : Config × ℕ, Relation.ReflTransGen (Translated schema) (initial l, 1) q ∧ Represents q.1 W q.2 := by
  constructor
  · intro path
    exact path_sound wf path (initial_represents l)
  · rintro ⟨q, run, rep⟩
    obtain ⟨W', path, rep'⟩ := path_complete wf run (initial_represents l)
    rwa [represents_unique rep' rep] at path

#print axioms push_eq
#print axioms represents_unique
#print axioms pick
#print axioms split_off
#print axioms fire_at
#print axioms sound
#print axioms complete
#print axioms translated_admitted
#print axioms path_sound
#print axioms path_complete
#print axioms initial_represents
#print axioms execution_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramTranslation
