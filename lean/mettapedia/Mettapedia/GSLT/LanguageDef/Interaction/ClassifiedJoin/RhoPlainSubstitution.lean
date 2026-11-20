import Mettapedia.OSLF.Syntax.RhoPayloadTranslation
import Mettapedia.OSLF.MeTTaIL.ScopedPattern

/-!
# The authored binder elimination in the payload presentation

The authored communication rule of the rho calculus eliminates the binder of
an input by replacing the bound name with the quotation of the payload,
textually.  The payload presentation binds the received process instead, and
its communication instantiates the continuation at the payload.

Read through the translation into the payload presentation, the textual
elimination is the extension of the environment by the *dropped name of the
payload*, up to the equations: at every name position the two agree, and at
every drop of the received name the textual elimination leaves the drop of
the quoted payload where the payload presentation runs the payload itself.
A whole name such as `@(*x|0)` becomes `@(*@q|0)`, which is literal code
equal to `@q` only up to the equations.

Three facts are proved.

* A translatable pattern mentions no bound index its environment lacks.
* Eliminating a binder at the quotation of a closed translatable payload
  translates, up to the equations, as the unsubstituted pattern in the
  environment that holds the dropped name of the payload at that index.
* The translation of the authored communication result is the continuation
  instantiated at the dropped name of the payload, up to the equations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoPayloadPresentation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern CollType rhoReflectivePresentation)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (BinderHead)
open Mettapedia.OSLF.MeTTaIL.Substitution
  (instantiateBVarAt instantiateBVar liftBVars_eq_self_of_isWellScopedAt
    instantiateBVarAt_eq_self_of_isWellScopedAt)
open Mettapedia.OSLF.MeTTaIL.ScopedPattern (isWellScopedAt_mono)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus (noBVar noBVarList)

/-! ## Scope and free indices -/

private theorem noBVarList_map {k k' : Nat} {f : Pattern → Pattern} {patterns : List Pattern}
    (each : ∀ pattern ∈ patterns, noBVar k (f pattern) = noBVar k' pattern) :
    noBVarList k (patterns.map f) = noBVarList k' patterns := by
  induction patterns with
  | nil => rfl
  | cons pattern rest ih =>
      simp only [List.map_cons, noBVarList]
      rw [each pattern (by simp), ih fun p member => each p (by simp [member])]

/-- Eliminating a binder at a closed replacement removes that index and moves
the indices above it down by one. -/
theorem noBVar_instantiateBVarAt {replacement : Pattern}
    (closed : replacement.isWellScopedAt 0 = true) (pattern : Pattern) :
    ∀ depth k, noBVar k (instantiateBVarAt depth replacement pattern) =
      if k < depth then noBVar k pattern else noBVar (k + 1) pattern := by
  have absent : ∀ k, noBVar k replacement = true :=
    fun k => (isWellScopedAt_iff_noBVar replacement 0).mp closed k (Nat.zero_le k)
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro depth k
      have free : ∀ i j, noBVar j (.bvar i) = true ↔ i ≠ j := fun i j => by simp [noBVar]
      simp only [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt]
      split_ifs <;> rw [Bool.eq_iff_iff] <;>
        simp only [free, liftBVars_eq_self_of_isWellScopedAt closed, absent, true_iff] <;>
        omega
  | hfvar name =>
      intro depth k
      simp only [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt]
      split <;> rfl
  | happly constructor arguments ih =>
      intro depth k
      simp only [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt, noBVar]
      split
      · rename_i below
        exact noBVarList_map fun argument member => by
          rw [ih argument member depth k, if_pos below]
      · rename_i above
        exact noBVarList_map fun argument member => by
          rw [ih argument member depth k, if_neg above]
  | hlambda name body ih =>
      intro depth k
      simp only [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt, noBVar]
      rw [ih (depth + 1) (k + 1)]
      by_cases below : k < depth
      · rw [if_pos (by omega), if_pos below]
      · rw [if_neg (by omega), if_neg below]
  | hmultiLambda arity names body ih =>
      intro depth k
      simp only [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt, noBVar]
      rw [ih (depth + arity) (k + arity)]
      by_cases below : k < depth
      · rw [if_pos (by omega), if_pos below]
      · rw [if_neg (by omega), if_neg below, show k + arity + 1 = k + 1 + arity by omega]
  | hsubst body replacement' ihBody ihReplacement =>
      intro depth k
      simp only [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt, noBVar]
      rw [ihBody (depth + 1) (k + 1), ihReplacement depth k]
      by_cases below : k < depth
      · rw [if_pos (by omega), if_pos below, if_pos below]
      · rw [if_neg (by omega), if_neg below, if_neg below]
  | hcollection kind elements rest ih =>
      intro depth k
      simp only [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt, noBVar]
      split
      · rename_i below
        exact noBVarList_map fun element member => by
          rw [ih element member depth k, if_pos below]
      · rename_i above
        exact noBVarList_map fun element member => by
          rw [ih element member depth k, if_neg above]

/-! ## Translatable patterns are scoped -/

/-- Beneath an input, an environment with no entry from `depth` on has none
from `depth + 1` on. -/
theorem up_eq_none {Γ : Ctx sig} {ρ : Env Γ} {depth : Nat}
    (beyond : ∀ j, depth ≤ j → ρ j = none) : ∀ j, depth + 1 ≤ j → ρ.up j = none := by
  intro j bound
  cases j with
  | zero => omega
  | succ j => simp [Env.up, beyond j (by omega)]

/-- **A translatable pattern mentions no bound index its environment lacks.** -/
theorem translate_wellScoped :
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (n : Pattern) (depth : Nat),
      (∀ j, depth ≤ j → ρ j = none) → ∀ t, tName ρ n = some t →
        n.isWellScopedAt depth = true) ∧
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (p : Pattern) (depth : Nat),
      (∀ j, depth ≤ j → ρ j = none) → ∀ t, tProc ρ p = some t →
        p.isWellScopedAt depth = true) ∧
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (ps : List Pattern) (depth : Nat),
      (∀ j, depth ≤ j → ρ j = none) → ∀ t, tProcs ρ ps = some t →
        Pattern.isWellScopedListAt depth ps = true) := by
  refine tName.mutual_induct
    (fun {Γ} ρ n => ∀ (depth : Nat), (∀ j, depth ≤ j → ρ j = none) →
      ∀ t, tName ρ n = some t → n.isWellScopedAt depth = true)
    (fun {Γ} ρ p => ∀ (depth : Nat), (∀ j, depth ≤ j → ρ j = none) →
      ∀ t, tProc ρ p = some t → p.isWellScopedAt depth = true)
    (fun {Γ} ρ ps => ∀ (depth : Nat), (∀ j, depth ≤ j → ρ j = none) →
      ∀ t, tProcs ρ ps = some t → Pattern.isWellScopedListAt depth ps = true)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro Γ ρ k depth beyond t h
    rw [tName_bvar] at h
    simp only [Pattern.isWellScopedAt, decide_eq_true_eq]
    by_contra outside
    rw [beyond k (Nat.le_of_not_lt outside)] at h
    cases h
  · intro Γ ρ label depth beyond t h
    simp [Pattern.isWellScopedAt]
  · intro Γ ρ name ih depth beyond t h
    rw [tName_quoteDrop] at h
    simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using ih depth beyond t h
  · intro Γ ρ code hcode k head ih depth beyond t h
    rw [tName_quote_of_nameHead _ hcode head] at h
    obtain ⟨c, hc, -⟩ := Option.bind_eq_some_iff.mp h
    simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using ih depth beyond c hc
  · intro Γ ρ code hcode head ih depth beyond t h
    rw [tName_quote _ hcode head] at h
    obtain ⟨literal, hliteral, -⟩ := Option.map_eq_some_iff.mp h
    have closed := ih 0 (fun _ _ => rfl) literal hliteral
    simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using
      isWellScopedAt_mono closed (Nat.zero_le depth)
  · intro x Γ ρ hbvar hfvar _ hquote depth beyond t h
    rw [tName_eq_none _ hbvar hfvar hquote] at h
    cases h
  · intro Γ ρ depth beyond t h
    simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt]
  · intro Γ ρ name k hk ih depth beyond t h
    rw [tProc_drop_of_nameHead _ hk] at h
    obtain ⟨m, hm, -⟩ := Option.bind_eq_some_iff.mp h
    simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using ih depth beyond m hm
  · intro Γ ρ name hk ih depth beyond t h
    rw [tProc_drop_of_nameHead_none _ hk] at h
    obtain ⟨m, hm, -⟩ := Option.map_eq_some_iff.mp h
    simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using ih depth beyond m hm
  · intro Γ ρ name payload ihn ihp depth beyond t h
    rw [tProc.eq_3] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨c, hc, process, hprocess, -⟩ := h
    simp only [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Bool.and_true,
      Bool.and_eq_true]
    exact ⟨ihn depth beyond c hc, ihp depth beyond process hprocess⟩
  · intro Γ ρ name body ihn ihb depth beyond t h
    rw [tProc.eq_4] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨c, hc, continuation, hcontinuation, -⟩ := h
    simp only [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Bool.and_true,
      Bool.and_eq_true]
    exact ⟨ihn depth beyond c hc,
      ihb (depth + 1) (up_eq_none beyond) continuation hcontinuation⟩
  · intro Γ ρ elements ih depth beyond t h
    rw [tProc.eq_5] at h
    simpa [Pattern.isWellScopedAt] using ih depth beyond t h
  · intro x Γ ρ hzero hdrop hout hinp hbag depth beyond t h
    rw [tProc.eq_6 _ _ hzero hdrop hout hinp hbag] at h
    cases h
  · intro Γ ρ depth beyond t h
    rfl
  · intro Γ ρ process rest ihp ihr depth beyond t h
    rw [tProcs.eq_2] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨head, hhead, tail, htail, -⟩ := h
    simp only [Pattern.isWellScopedListAt, Bool.and_eq_true]
    exact ⟨ihp depth beyond head hhead, ihr depth beyond tail htail⟩

/-- A process translatable with no bound index in scope is locally closed. -/
theorem wellScoped_of_closed {p : Pattern} {t : Term sig [] Srt.pr}
    (h : tProc (Env.empty []) p = some t) : p.isWellScopedAt 0 = true :=
  translate_wellScoped.2.1 (Env.empty []) p 0 (fun _ _ => rfl) t h

/-- A translatable pattern still translates in any environment that supplies
the indices occurring free in it. -/
theorem translate_of_free :
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (n : Pattern), (∃ t, tName ρ n = some t) →
      ∀ {Δ : Ctx sig} (ρ' : Env Δ), (∀ k, noBVar k n = false → ∃ u, ρ' k = some u) →
        ∃ t, tName ρ' n = some t) ∧
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (p : Pattern), (∃ t, tProc ρ p = some t) →
      ∀ {Δ : Ctx sig} (ρ' : Env Δ), (∀ k, noBVar k p = false → ∃ u, ρ' k = some u) →
        ∃ t, tProc ρ' p = some t) ∧
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (ps : List Pattern), (∃ t, tProcs ρ ps = some t) →
      ∀ {Δ : Ctx sig} (ρ' : Env Δ), (∀ k, noBVarList k ps = false → ∃ u, ρ' k = some u) →
        ∃ t, tProcs ρ' ps = some t) := by
  refine tName.mutual_induct
    (fun {Γ} ρ n => (∃ t, tName ρ n = some t) →
      ∀ {Δ : Ctx sig} (ρ' : Env Δ), (∀ k, noBVar k n = false → ∃ u, ρ' k = some u) →
        ∃ t, tName ρ' n = some t)
    (fun {Γ} ρ p => (∃ t, tProc ρ p = some t) →
      ∀ {Δ : Ctx sig} (ρ' : Env Δ), (∀ k, noBVar k p = false → ∃ u, ρ' k = some u) →
        ∃ t, tProc ρ' p = some t)
    (fun {Γ} ρ ps => (∃ t, tProcs ρ ps = some t) →
      ∀ {Δ : Ctx sig} (ρ' : Env Δ), (∀ k, noBVarList k ps = false → ∃ u, ρ' k = some u) →
        ∃ t, tProcs ρ' ps = some t)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro Γ ρ k _ Δ ρ' supplied
    obtain ⟨u, hu⟩ := supplied k (by simp [noBVar])
    exact ⟨nameOf u, by rw [tName_bvar, hu, Option.map_some]⟩
  · intro Γ ρ label _ Δ ρ' _
    exact ⟨freeT label, tName_fvar ρ' label⟩
  · intro Γ ρ name ih ⟨t, h⟩ Δ ρ' supplied
    rw [tName_quoteDrop] at h ⊢
    exact ih ⟨t, h⟩ ρ' fun k hk => supplied k (by simp [noBVar, noBVarList, hk])
  · intro Γ ρ code hcode j head ih ⟨t, h⟩ Δ ρ' supplied
    rw [tName_quote_of_nameHead _ hcode head] at h
    obtain ⟨c, hc, -⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c', hc'⟩ := ih ⟨c, hc⟩ ρ' fun k hk => supplied k (by simp [noBVar, noBVarList, hk])
    obtain ⟨u, hu⟩ := supplied j (by rw [nameHead_noBVar head]; simp)
    exact ⟨nameOf u, by
      rw [tName_quote_of_nameHead _ hcode head, hc', Option.bind_some, hu, Option.map_some]⟩
  · intro Γ ρ code hcode head _ ⟨t, h⟩ Δ ρ' _
    rw [tName_quote _ hcode head] at h
    obtain ⟨literal, hliteral, -⟩ := Option.map_eq_some_iff.mp h
    exact ⟨nameOf (lift0 literal), by
      rw [tName_quote _ hcode head, hliteral, Option.map_some]⟩
  · intro x Γ ρ hbvar hfvar _ hquote ⟨t, h⟩ Δ ρ' _
    rw [tName_eq_none _ hbvar hfvar hquote] at h
    cases h
  · intro Γ ρ _ Δ ρ' _
    exact ⟨nilT, tProc.eq_1 ρ'⟩
  · intro Γ ρ name j head ih ⟨t, h⟩ Δ ρ' supplied
    rw [tProc_drop_of_nameHead _ head] at h
    obtain ⟨m, hm, -⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨m', hm'⟩ := ih ⟨m, hm⟩ ρ' fun k hk => supplied k (by simp [noBVar, noBVarList, hk])
    obtain ⟨u, hu⟩ := supplied j (by simp [noBVar, noBVarList, nameHead_noBVar head])
    exact ⟨u, by rw [tProc_drop_of_nameHead _ head, hm', Option.bind_some, hu]⟩
  · intro Γ ρ name head ih ⟨t, h⟩ Δ ρ' supplied
    rw [tProc_drop_of_nameHead_none _ head] at h
    obtain ⟨m, hm, -⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨m', hm'⟩ := ih ⟨m, hm⟩ ρ' fun k hk => supplied k (by simp [noBVar, noBVarList, hk])
    exact ⟨drpT m', by rw [tProc_drop_of_nameHead_none _ head, hm', Option.map_some]⟩
  · intro Γ ρ name payload ihn ihp ⟨t, h⟩ Δ ρ' supplied
    rw [tProc.eq_3] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨c, hc, process, hprocess, -⟩ := h
    obtain ⟨c', hc'⟩ := ihn ⟨c, hc⟩ ρ' fun k hk => supplied k (by simp [noBVar, noBVarList, hk])
    obtain ⟨process', hprocess'⟩ :=
      ihp ⟨process, hprocess⟩ ρ' fun k hk => supplied k (by simp [noBVar, noBVarList, hk])
    exact ⟨outT c' process', by
      rw [tProc.eq_3, hc', Option.bind_some, hprocess', Option.map_some]⟩
  · intro Γ ρ name body ihn ihb ⟨t, h⟩ Δ ρ' supplied
    rw [tProc.eq_4] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨c, hc, continuation, hcontinuation, -⟩ := h
    obtain ⟨c', hc'⟩ := ihn ⟨c, hc⟩ ρ' fun k hk => supplied k (by simp [noBVar, noBVarList, hk])
    obtain ⟨continuation', hcontinuation'⟩ := ihb ⟨continuation, hcontinuation⟩ ρ'.up (by
      intro k hk
      cases k with
      | zero => exact ⟨.var .zero, rfl⟩
      | succ k =>
          obtain ⟨u, hu⟩ := supplied k (by simp [noBVar, noBVarList, hk])
          exact ⟨weaken u, by simp [Env.up, hu]⟩)
    exact ⟨inpT c' continuation', by
      rw [tProc.eq_4, hc', Option.bind_some, hcontinuation', Option.map_some]⟩
  · intro Γ ρ elements ih ⟨t, h⟩ Δ ρ' supplied
    rw [tProc.eq_5] at h ⊢
    exact ih ⟨t, h⟩ ρ' fun k hk => supplied k (by simpa [noBVar] using hk)
  · intro x Γ ρ hzero hdrop hout hinp hbag ⟨t, h⟩ Δ ρ' _
    rw [tProc.eq_6 _ _ hzero hdrop hout hinp hbag] at h
    cases h
  · intro Γ ρ _ Δ ρ' _
    exact ⟨nilT, rfl⟩
  · intro Γ ρ process rest ihp ihr ⟨t, h⟩ Δ ρ' supplied
    rw [tProcs.eq_2] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨head, hhead, tail, htail, -⟩ := h
    obtain ⟨head', hhead'⟩ :=
      ihp ⟨head, hhead⟩ ρ' fun k hk => supplied k (by simp [noBVarList, hk])
    obtain ⟨tail', htail'⟩ :=
      ihr ⟨tail, htail⟩ ρ' fun k hk => supplied k (by simp [noBVarList, hk])
    exact ⟨parT head' tail', by
      rw [tProcs.eq_2, hhead', Option.bind_some, htail', Option.map_some]⟩

/-! ## Binder observations of translatable patterns -/

/-- An observation that a parallel unit or a drop cannot hide: an index or
an opaque term. -/
def BinderHead.isAtomic : BinderHead → Bool
  | .index _ => true
  | .opaque => true
  | _ => false

/-- The observations a translatable process can have: the unit, a drop of an
atomic observation, or an opaque term. -/
def BinderHead.isProcessHead : BinderHead → Bool
  | .unit => true
  | .drop name => BinderHead.isAtomic name
  | .opaque => true
  | .index _ => false

theorem BinderHead.isProcessHead_join {left right : BinderHead}
    (hleft : BinderHead.isProcessHead left = true) (hright : BinderHead.isProcessHead right = true) :
    BinderHead.isProcessHead (BinderHead.join left right) = true := by
  cases left <;> cases right <;> simp_all [BinderHead.join, BinderHead.isProcessHead]

/-- A parallel bag is observed through its elements. -/
theorem ofPattern_bag (elements : List Pattern) :
    BinderHead.ofPattern rhoReflectivePresentation (.collection .hashBag elements none) =
      (BinderHead.ofList rhoReflectivePresentation elements).foldr BinderHead.join .unit :=
  rfl

/-- An application to two arguments is opaque to the binder observation. -/
theorem ofPattern_apply_two (constructor : String) (first second : Pattern) :
    BinderHead.ofPattern rhoReflectivePresentation (.apply constructor [first, second]) =
      .opaque := by
  simp only [BinderHead.ofPattern, BinderHead.ofList]
  generalize BinderHead.ofPattern rhoReflectivePresentation first = observed
  cases observed <;> rfl

/-- Every translatable name is observed as an index or as opaque, and every
translatable process as the unit, a drop of such a name, or opaque. -/
theorem ofPattern_of_translate :
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (n : Pattern), (∃ t, tName ρ n = some t) →
      BinderHead.isAtomic (BinderHead.ofPattern rhoReflectivePresentation n) = true) ∧
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (p : Pattern), (∃ t, tProc ρ p = some t) →
      BinderHead.isProcessHead (BinderHead.ofPattern rhoReflectivePresentation p) = true) ∧
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (ps : List Pattern), (∃ t, tProcs ρ ps = some t) →
      BinderHead.isProcessHead
        ((BinderHead.ofList rhoReflectivePresentation ps).foldr BinderHead.join .unit) = true) := by
  refine tName.mutual_induct
    (fun {Γ} ρ n => (∃ t, tName ρ n = some t) →
      BinderHead.isAtomic (BinderHead.ofPattern rhoReflectivePresentation n) = true)
    (fun {Γ} ρ p => (∃ t, tProc ρ p = some t) →
      BinderHead.isProcessHead (BinderHead.ofPattern rhoReflectivePresentation p) = true)
    (fun {Γ} ρ ps => (∃ t, tProcs ρ ps = some t) →
      BinderHead.isProcessHead
        ((BinderHead.ofList rhoReflectivePresentation ps).foldr BinderHead.join .unit) = true)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro Γ ρ k _
    rfl
  · intro Γ ρ label _
    rfl
  · intro Γ ρ name ih ⟨t, h⟩
    rw [ofPattern_quoteDrop]
    rw [tName_quoteDrop] at h
    exact ih ⟨t, h⟩
  · intro Γ ρ code _ k head _ _
    rw [nameHead_eq_some_iff_ofPattern.mp head]
    rfl
  · intro Γ ρ code hcode head ih ⟨t, h⟩
    rw [tName_quote _ hcode head] at h
    obtain ⟨literal, hliteral, -⟩ := Option.map_eq_some_iff.mp h
    have inner := ih ⟨literal, hliteral⟩
    simp only [BinderHead.ofPattern, BinderHead.ofList]
    generalize BinderHead.ofPattern rhoReflectivePresentation code = observed at inner
    cases observed with
    | index level => simp [BinderHead.isProcessHead] at inner
    | unit => rfl
    | drop name => simpa [BinderHead.isProcessHead, BinderHead.apply,
        rhoReflectivePresentation] using inner
    | «opaque» => rfl
  · intro x Γ ρ hbvar hfvar _ hquote ⟨t, h⟩
    rw [tName_eq_none _ hbvar hfvar hquote] at h
    cases h
  · intro Γ ρ _
    rfl
  · intro Γ ρ name k head ih ⟨t, h⟩
    rw [tProc_drop_of_nameHead _ head] at h
    obtain ⟨m, hm, -⟩ := Option.bind_eq_some_iff.mp h
    have inner := ih ⟨m, hm⟩
    simp only [BinderHead.ofPattern, BinderHead.ofList]
    generalize BinderHead.ofPattern rhoReflectivePresentation name = observed at inner
    cases observed <;> simp_all [BinderHead.isAtomic, BinderHead.isProcessHead,
      BinderHead.apply, BinderHead.rigid, rhoReflectivePresentation]
  · intro Γ ρ name head ih ⟨t, h⟩
    rw [tProc_drop_of_nameHead_none _ head] at h
    obtain ⟨m, hm, -⟩ := Option.map_eq_some_iff.mp h
    have inner := ih ⟨m, hm⟩
    simp only [BinderHead.ofPattern, BinderHead.ofList]
    generalize BinderHead.ofPattern rhoReflectivePresentation name = observed at inner
    cases observed <;> simp_all [BinderHead.isAtomic, BinderHead.isProcessHead,
      BinderHead.apply, BinderHead.rigid, rhoReflectivePresentation]
  · intro Γ ρ name payload _ _ _
    rw [ofPattern_apply_two]
    rfl
  · intro Γ ρ name body _ _ _
    rw [ofPattern_apply_two]
    rfl
  · intro Γ ρ elements ih ⟨t, h⟩
    rw [tProc.eq_5] at h
    rw [ofPattern_bag]
    exact ih ⟨t, h⟩
  · intro x Γ ρ hzero hdrop hout hinp hbag ⟨t, h⟩
    rw [tProc.eq_6 _ _ hzero hdrop hout hinp hbag] at h
    cases h
  · intro Γ ρ _
    rfl
  · intro Γ ρ process rest ihp ihr ⟨t, h⟩
    rw [tProcs.eq_2] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨head, hhead, tail, htail, -⟩ := h
    simp only [BinderHead.ofList, List.foldr_cons]
    exact BinderHead.isProcessHead_join (ihp ⟨head, hhead⟩) (ihr ⟨tail, htail⟩)

theorem BinderHead.join_eq_unit {left right : BinderHead}
    (h : BinderHead.join left right = .unit) : left = .unit ∧ right = .unit := by
  cases left <;> cases right <;> simp_all [BinderHead.join]

theorem BinderHead.join_eq_drop {left right name : BinderHead}
    (h : BinderHead.join left right = .drop name) :
    (left = .unit ∧ right = .drop name) ∨ (left = .drop name ∧ right = .unit) := by
  cases left <;> cases right <;> simp_all [BinderHead.join]

/-- A translated process observed as the unit is the null process, and one
observed as the drop of a bound index is the process received there, up to
the equations. -/
theorem translate_unit_or_drop :
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (p : Pattern) (c : Term sig Γ Srt.pr), tProc ρ p = some c →
      (BinderHead.ofPattern rhoReflectivePresentation p = .unit →
        EqClosure equations c nilT) ∧
      (∀ k, BinderHead.ofPattern rhoReflectivePresentation p = .drop (.index k) →
        ∃ u, ρ k = some u ∧ EqClosure equations c u)) ∧
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (ps : List Pattern) (c : Term sig Γ Srt.pr),
      tProcs ρ ps = some c →
      ((BinderHead.ofList rhoReflectivePresentation ps).foldr BinderHead.join .unit = .unit →
        EqClosure equations c nilT) ∧
      (∀ k, (BinderHead.ofList rhoReflectivePresentation ps).foldr BinderHead.join .unit =
          .drop (.index k) → ∃ u, ρ k = some u ∧ EqClosure equations c u)) := by
  refine (tName.mutual_induct (fun _ _ => True)
    (fun {Γ} ρ p => ∀ c : Term sig Γ Srt.pr, tProc ρ p = some c →
      (BinderHead.ofPattern rhoReflectivePresentation p = .unit →
        EqClosure equations c nilT) ∧
      (∀ k, BinderHead.ofPattern rhoReflectivePresentation p = .drop (.index k) →
        ∃ u, ρ k = some u ∧ EqClosure equations c u))
    (fun {Γ} ρ ps => ∀ c : Term sig Γ Srt.pr, tProcs ρ ps = some c →
      ((BinderHead.ofList rhoReflectivePresentation ps).foldr BinderHead.join .unit = .unit →
        EqClosure equations c nilT) ∧
      (∀ k, (BinderHead.ofList rhoReflectivePresentation ps).foldr BinderHead.join .unit =
          .drop (.index k) → ∃ u, ρ k = some u ∧ EqClosure equations c u))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).2
  all_goals first | (intros; trivial) | skip
  · intro Γ ρ c h
    rw [tProc.eq_1] at h
    cases h
    exact ⟨fun _ => .refl _, fun k observed => by cases observed⟩
  · intro Γ ρ name j head _ c h
    rw [tProc_drop_of_nameHead _ head] at h
    obtain ⟨_, _, received⟩ := Option.bind_eq_some_iff.mp h
    have observedName := nameHead_eq_some_iff_ofPattern.mp head
    simp only [BinderHead.ofPattern, BinderHead.ofList, observedName]
    refine ⟨fun observed => by simp [BinderHead.apply, BinderHead.rigid,
      rhoReflectivePresentation] at observed, fun k observed => ?_⟩
    simp [BinderHead.apply, BinderHead.rigid, rhoReflectivePresentation] at observed
    subst observed
    exact ⟨c, received, .refl _⟩
  · intro Γ ρ name head _ c _
    simp only [BinderHead.ofPattern, BinderHead.ofList]
    refine ⟨fun observed => ?_, fun k observed => ?_⟩
    · generalize BinderHead.ofPattern rhoReflectivePresentation name = observedName at observed
      cases observedName <;> simp [BinderHead.apply, BinderHead.rigid,
        rhoReflectivePresentation] at observed
    · have observedName : BinderHead.ofPattern rhoReflectivePresentation name = .index k := by
        generalize BinderHead.ofPattern rhoReflectivePresentation name = observedName at observed
        cases observedName <;> simp_all [BinderHead.apply, BinderHead.rigid,
          rhoReflectivePresentation]
      rw [← nameHead_eq_some_iff_ofPattern, head] at observedName
      cases observedName
  · intro Γ ρ name payload _ _ c _
    rw [ofPattern_apply_two]
    exact ⟨fun observed => (by cases observed), fun k observed => (by cases observed)⟩
  · intro Γ ρ name body _ _ c _
    rw [ofPattern_apply_two]
    exact ⟨fun observed => (by cases observed), fun k observed => (by cases observed)⟩
  · intro Γ ρ elements ih c h
    rw [tProc.eq_5] at h
    rw [ofPattern_bag]
    exact ih c h
  · intro x Γ ρ hzero hdrop hout hinp hbag c h
    rw [tProc.eq_6 _ _ hzero hdrop hout hinp hbag] at h
    cases h
  · intro Γ ρ c h
    rw [tProcs.eq_1] at h
    cases h
    exact ⟨fun _ => .refl _, fun k observed => by cases observed⟩
  · intro Γ ρ process rest ihp ihr c h
    rw [tProcs.eq_2] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨head, hhead, tail, htail, rfl⟩ := h
    obtain ⟨headUnit, headDrop⟩ := ihp head hhead
    obtain ⟨tailUnit, tailDrop⟩ := ihr tail htail
    simp only [BinderHead.ofList, List.foldr_cons]
    refine ⟨fun observed => ?_, fun k observed => ?_⟩
    · obtain ⟨hu, tu⟩ := BinderHead.join_eq_unit observed
      exact (equiv_parT (headUnit hu) (tailUnit tu)).trans (parT_nil nilT)
    · rcases BinderHead.join_eq_drop observed with ⟨hu, td⟩ | ⟨hd, tu⟩
      · obtain ⟨u, hu', e⟩ := tailDrop k td
        exact ⟨u, hu', (equiv_parT (headUnit hu) e).trans (nil_parT u)⟩
      · obtain ⟨u, hu', e⟩ := headDrop k hd
        exact ⟨u, hu', (equiv_parT e (tailUnit tu)).trans (parT_nil u)⟩

/-! ## Binder observations under binder elimination -/

/-- Replace the indices of a binder observation. -/
def BinderHead.substIndex (σ : Nat → BinderHead) : BinderHead → BinderHead
  | .index level => σ level
  | .unit => .unit
  | .drop name => .drop (BinderHead.substIndex σ name)
  | .opaque => .opaque

theorem BinderHead.substIndex_join {σ : Nat → BinderHead}
    (atomic : ∀ level, BinderHead.isAtomic (σ level) = true) (left right : BinderHead) :
    BinderHead.substIndex σ (BinderHead.join left right) =
      BinderHead.join (BinderHead.substIndex σ left) (BinderHead.substIndex σ right) := by
  have nonunit : ∀ level, σ level ≠ .unit := fun level same => by
    have := atomic level
    rw [same] at this
    cases this
  cases left <;> cases right <;>
    simp [BinderHead.join, BinderHead.substIndex, nonunit]

theorem BinderHead.substIndex_fold {σ : Nat → BinderHead}
    (atomic : ∀ level, BinderHead.isAtomic (σ level) = true) (heads : List BinderHead) :
    BinderHead.substIndex σ (heads.foldr BinderHead.join .unit) =
      (heads.map (BinderHead.substIndex σ)).foldr BinderHead.join .unit := by
  induction heads with
  | nil => rfl
  | cons head rest ih =>
      simp only [List.foldr_cons, List.map_cons]
      rw [BinderHead.substIndex_join atomic, ih]

theorem BinderHead.apply_single_of_not_drop
    (declaration : Mettapedia.OSLF.MeTTaIL.Syntax.ReflectivePresentationDecl)
    (constructor : String) {head : BinderHead} (notDrop : ∀ name, head ≠ .drop name) :
    BinderHead.apply declaration constructor [head] =
      BinderHead.rigid declaration constructor [head] := by
  cases head with
  | drop name => exact absurd rfl (notDrop name)
  | _ => rfl

theorem BinderHead.apply_long
    (declaration : Mettapedia.OSLF.MeTTaIL.Syntax.ReflectivePresentationDecl)
    (constructor : String) (first second : BinderHead) (rest : List BinderHead) :
    BinderHead.apply declaration constructor (first :: second :: rest) = .opaque := by
  cases first <;> rfl

theorem BinderHead.substIndex_rigid (σ : Nat → BinderHead)
    (declaration : Mettapedia.OSLF.MeTTaIL.Syntax.ReflectivePresentationDecl)
    (constructor : String) (heads : List BinderHead) :
    BinderHead.substIndex σ (BinderHead.rigid declaration constructor heads) =
      BinderHead.rigid declaration constructor (heads.map (BinderHead.substIndex σ)) := by
  match heads with
  | [] =>
      simp only [BinderHead.rigid, List.map_nil]
      split <;> rfl
  | [_] =>
      simp only [BinderHead.rigid, List.map_cons, List.map_nil]
      split <;> rfl
  | _ :: _ :: _ => rfl

theorem BinderHead.substIndex_apply {σ : Nat → BinderHead}
    (atomic : ∀ level, BinderHead.isAtomic (σ level) = true)
    (declaration : Mettapedia.OSLF.MeTTaIL.Syntax.ReflectivePresentationDecl)
    (constructor : String) (heads : List BinderHead) :
    BinderHead.substIndex σ (BinderHead.apply declaration constructor heads) =
      BinderHead.apply declaration constructor (heads.map (BinderHead.substIndex σ)) := by
  match heads with
  | [] => exact BinderHead.substIndex_rigid σ declaration constructor []
  | [.drop name] =>
      simp only [BinderHead.apply, List.map_cons, List.map_nil, BinderHead.substIndex]
      split
      · rfl
      · exact BinderHead.substIndex_rigid σ declaration constructor [.drop name]
  | [.index level] =>
      have notDrop : ∀ name, σ level ≠ .drop name := fun name same => by
        have := atomic level
        rw [same] at this
        cases this
      show BinderHead.substIndex σ (BinderHead.rigid declaration constructor [.index level]) =
        BinderHead.apply declaration constructor [σ level]
      rw [BinderHead.substIndex_rigid, BinderHead.apply_single_of_not_drop _ _ notDrop]
      rfl
  | [.unit] => exact BinderHead.substIndex_rigid σ declaration constructor [.unit]
  | [.opaque] => exact BinderHead.substIndex_rigid σ declaration constructor [.opaque]
  | first :: second :: rest =>
      rw [BinderHead.apply_long, List.map_cons, List.map_cons, BinderHead.apply_long]
      rfl

/-- Binder elimination acts on the binder observation through the
observations of the eliminated and lowered indices. -/
theorem ofPattern_instantiateBVarAt {depth : Nat} {replacement : Pattern}
    {σ : Nat → BinderHead} (atomic : ∀ level, BinderHead.isAtomic (σ level) = true)
    (pattern : Pattern)
    (atIndices : ∀ level, noBVar level pattern = false →
      BinderHead.ofPattern rhoReflectivePresentation
        (instantiateBVarAt depth replacement (.bvar level)) = σ level) :
    BinderHead.ofPattern rhoReflectivePresentation (instantiateBVarAt depth replacement pattern) =
      BinderHead.substIndex σ (BinderHead.ofPattern rhoReflectivePresentation pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar level =>
      exact atIndices level (by simp [noBVar])
  | hfvar name =>
      simp only [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt]
      rfl
  | happly constructor arguments ih =>
      simp only [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt, BinderHead.ofPattern,
        BinderHead.ofList_eq_map, List.map_map]
      rw [BinderHead.substIndex_apply atomic, List.map_map]
      congr 1
      apply List.map_congr_left
      intro argument member
      exact ih argument member fun level free => atIndices level (by
        have : noBVarList level arguments = false := by
          cases hall : noBVarList level arguments with
          | false => rfl
          | true => rw [(noBVarList_iff level arguments).mp hall argument member] at free; cases free
        simpa [noBVar] using this)
  | hlambda name body _ =>
      simp only [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt]
      rfl
  | hmultiLambda arity names body _ =>
      simp only [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt]
      rfl
  | hsubst body replacement' _ _ =>
      simp only [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt]
      rfl
  | hcollection kind elements rest ih =>
      cases rest with
      | some rest =>
          simp only [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt]
          rfl
      | none =>
          simp only [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt, BinderHead.ofPattern]
          split
          · rw [BinderHead.substIndex_fold atomic, BinderHead.ofList_eq_map,
              BinderHead.ofList_eq_map, List.map_map, List.map_map]
            congr 1
            apply List.map_congr_left
            intro element member
            exact ih element member fun level free => atIndices level (by
              have : noBVarList level elements = false := by
                cases hall : noBVarList level elements with
                | false => rfl
                | true => rw [(noBVarList_iff level elements).mp hall element member] at free; cases free
              simpa [noBVar] using this)
          · rfl

/-- Lowering the indices above an eliminated binder. -/
def lowerHead (depth level : Nat) : BinderHead :=
  if level < depth then .index level else .index (level - 1)

/-- The observation of binder elimination at a replacement. -/
def instantiateHead (depth : Nat) (replacement : BinderHead) (level : Nat) : BinderHead :=
  if level < depth then .index level else if level = depth then replacement else .index (level - 1)

/-! ## The quotation of a closed payload -/

/-- The quotation of a payload: the name the authored rule substitutes. -/
abbrev literalName (q : Pattern) : Pattern := .apply "NQuote" [q]

/-- The drop of the name of a process.  A process that is itself the drop of
a name is its own dropped name; any other process `P` gives `*@P`. -/
def droppedName {Γ : Ctx sig} (process : Term sig Γ Srt.pr) : Term sig Γ Srt.pr :=
  drpT (nameOf process)

theorem droppedName_drpT {Γ : Ctx sig} (name : Term sig Γ Srt.nm) :
    droppedName (drpT name) = drpT name := rfl

variable {q : Pattern} {q₀ : Term sig [] Srt.pr}

theorem lift0_droppedName {Γ : Ctx sig} (process : Term sig [] Srt.pr) :
    lift0 (Γ := Γ) (droppedName process) = drpT (nameOf (lift0 process)) := by
  show rename (emptyRen Γ) (drpT (nameOf process)) =
    drpT (nameOf (rename (emptyRen Γ) process))
  rw [← rename_nameOf]
  rfl

theorem nameOf_lift0_droppedName {Γ : Ctx sig} (process : Term sig [] Srt.pr) :
    nameOf (lift0 (Γ := Γ) (droppedName process)) = nameOf (lift0 process) := by
  rw [lift0_droppedName]
  rfl

/-- The quotation of a closed translatable payload denotes no bound index. -/
theorem nameHead_literalName (hq : tProc (Env.empty []) q = some q₀) :
    nameHead (literalName q) = none :=
  nameHead_quote_of_closed hq

/-- The quotation of a closed translatable payload is the name of the
payload, in every environment. -/
theorem tName_literalName (hq : tProc (Env.empty []) q = some q₀) {Γ : Ctx sig}
    (ρ : Env Γ) : tName ρ (literalName q) = some (nameOf (lift0 q₀)) := by
  have closed := nameHead_quote_of_closed hq
  by_cases hdrop : ∃ m, q = .apply "PDrop" [m]
  · obtain ⟨m, rfl⟩ := hdrop
    rw [nameHead_quoteDrop] at closed
    rw [literalName, tName_quoteDrop]
    rw [tProc_drop_of_nameHead_none _ closed] at hq
    obtain ⟨m₀, hm₀, rfl⟩ := Option.map_eq_some_iff.mp hq
    rw [tName_closed hm₀ ρ]
    rfl
  · have hnot : ∀ m, q = .apply "PDrop" [m] → False := fun m h => hdrop ⟨m, h⟩
    rw [literalName, tName_quote _ hnot closed, hq, Option.map_some]

/-- The quotation of a locally closed payload is unchanged by lifting. -/
theorem lift_literalName (closedPayload : q.isWellScopedAt 0 = true) (depth : Nat) :
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0 depth (literalName q) = literalName q :=
  liftBVars_eq_self_of_isWellScopedAt
    (by simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, closedPayload])

/-- The quotation of a closed translatable payload is observed as an atom. -/
theorem literalName_atomic (hq : tProc (Env.empty []) q = some q₀) :
    BinderHead.isAtomic (BinderHead.ofPattern rhoReflectivePresentation (literalName q)) = true :=
  ofPattern_of_translate.1 (Env.empty []) (literalName q) ⟨_, tName_literalName hq (Env.empty [])⟩

/-- Binder elimination at the quotation of a closed translatable payload acts
on every observation through `instantiateHead`. -/
theorem ofPattern_instantiate_literal (hq : tProc (Env.empty []) q = some q₀) (depth : Nat)
    (pattern : Pattern) :
    BinderHead.ofPattern rhoReflectivePresentation
        (instantiateBVarAt depth (literalName q) pattern) =
      BinderHead.substIndex
        (instantiateHead depth (BinderHead.ofPattern rhoReflectivePresentation (literalName q)))
        (BinderHead.ofPattern rhoReflectivePresentation pattern) := by
  refine ofPattern_instantiateBVarAt (fun level => ?_) pattern fun level _ => ?_
  · unfold instantiateHead
    split
    · rfl
    · split
      · exact literalName_atomic hq
      · rfl
  · simp only [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt, instantiateHead]
    split
    · rfl
    · split
      · rw [lift_literalName (wellScoped_of_closed hq)]
      · rfl

/-! ## Binder elimination at a name -/

theorem instantiate_quoteDrop (depth : Nat) (replacement name : Pattern) :
    instantiateBVarAt depth replacement (.apply "NQuote" [.apply "PDrop" [name]]) =
      .apply "NQuote" [.apply "PDrop" [instantiateBVarAt depth replacement name]] := by
  simp only [instantiateBVarAt, List.map_cons, List.map_nil]

theorem instantiate_drop (depth : Nat) (replacement name : Pattern) :
    instantiateBVarAt depth replacement (.apply "PDrop" [name]) =
      .apply "PDrop" [instantiateBVarAt depth replacement name] := by
  simp only [instantiateBVarAt, List.map_cons, List.map_nil]

theorem instantiate_quote (depth : Nat) (replacement code : Pattern) :
    instantiateBVarAt depth replacement (.apply "NQuote" [code]) =
      .apply "NQuote" [instantiateBVarAt depth replacement code] := by
  simp only [instantiateBVarAt, List.map_cons, List.map_nil]

/-- A name denoting an index below the eliminated binder is unchanged. -/
theorem instantiate_name_below {name : Pattern} {index depth : Nat} (replacement : Pattern)
    (head : nameHead name = some index) (below : index < depth) :
    instantiateBVarAt depth replacement name = name :=
  instantiateBVarAt_eq_self_of_isWellScopedAt
    (by rw [nameHead_wellScoped head]; exact decide_eq_true below)

/-- A name denoting an index above the eliminated binder denotes the index
below it afterwards. -/
theorem nameHead_instantiate_above {name : Pattern} {index depth : Nat}
    (replacement : Pattern) (head : nameHead name = some index) (above : depth < index) :
    nameHead (instantiateBVarAt depth replacement name) = some (index - 1) := by
  have observed := nameHead_eq_some_iff_ofPattern.mp head
  rw [nameHead_eq_some_iff_ofPattern,
    ofPattern_instantiateBVarAt (σ := lowerHead depth) (fun level => by
      unfold lowerHead
      split <;> rfl) name (fun level free => by
        rw [nameHead_noBVar head] at free
        have same : index = level := by simpa using free
        subst same
        simp only [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt, lowerHead,
          if_neg (Nat.not_lt_of_gt above), if_neg (Nat.ne_of_gt above)]
        rfl),
    observed]
  simp only [BinderHead.substIndex, lowerHead, if_neg (Nat.not_lt_of_gt above)]

/-- A name denoting the eliminated binder denotes no bound index once the
binder is eliminated at the quotation of a closed translatable payload. -/
theorem nameHead_instantiate_here (hq : tProc (Env.empty []) q = some q₀)
    {name : Pattern} {depth : Nat} (head : nameHead name = some depth) :
    nameHead (instantiateBVarAt depth (literalName q) name) = none := by
  have observed := nameHead_eq_some_iff_ofPattern.mp head
  have literal := nameHead_literalName hq
  unfold nameHead at literal ⊢
  rw [ofPattern_instantiate_literal hq, observed]
  simp only [BinderHead.substIndex, instantiateHead, Nat.lt_irrefl, if_false, if_true]
  exact literal

/-- Binder elimination at a quotation produces a drop only from a drop. -/
theorem eq_drop_of_instantiate_eq_drop (closedPayload : q.isWellScopedAt 0 = true) {depth : Nat}
    {pattern name : Pattern}
    (same : instantiateBVarAt depth (literalName q) pattern = .apply "PDrop" [name]) :
    ∃ original, pattern = .apply "PDrop" [original] := by
  cases pattern with
  | bvar index =>
      rw [instantiateBVarAt.eq_1] at same
      split at same
      · cases same
      · split at same
        · rw [lift_literalName closedPayload] at same
          simp [literalName] at same
        · cases same
  | fvar label => simp [instantiateBVarAt] at same
  | apply label arguments =>
      rw [instantiateBVarAt.eq_3] at same
      simp only [Pattern.apply.injEq] at same
      obtain ⟨rfl, mapped⟩ := same
      cases arguments with
      | nil => simp at mapped
      | cons original rest =>
          cases rest with
          | nil => exact ⟨original, rfl⟩
          | cons _ _ => simp at mapped
  | lambda binder body => simp [instantiateBVarAt] at same
  | multiLambda arity binders body => simp [instantiateBVarAt] at same
  | subst body replacement => simp [instantiateBVarAt] at same
  | collection kind elements rest => simp [instantiateBVarAt] at same

/-- A name denoting no bound index still denotes none after the binder is
eliminated at the quotation of a closed translatable payload. -/
theorem nameHead_instantiate_none (hq : tProc (Env.empty []) q = some q₀)
    {name : Pattern} (depth : Nat) (head : nameHead name = none) :
    nameHead (instantiateBVarAt depth (literalName q) name) = none := by
  unfold nameHead at head ⊢
  rw [ofPattern_instantiate_literal hq]
  generalize BinderHead.ofPattern rhoReflectivePresentation name = observed at head
  cases observed with
  | index level => simp at head
  | unit => rfl
  | drop inner => rfl
  | «opaque» => rfl

/-- After the binder is eliminated, a name that denoted it has no free
index left. -/
theorem noBVar_instantiate_here (hq : tProc (Env.empty []) q = some q₀)
    {name : Pattern} {depth : Nat} (head : nameHead name = some depth) (k : Nat) :
    noBVar k (instantiateBVarAt depth (literalName q) name) = true := by
  have closedName : (literalName q).isWellScopedAt 0 = true := by
    simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, wellScoped_of_closed hq]
  rw [noBVar_instantiateBVarAt closedName, nameHead_noBVar head, nameHead_noBVar head]
  split <;> simp only [bne_iff_ne, ne_eq] <;> omega

/-! ## Binder elimination is extension of the environment -/

/-- The environment `larger` is `smaller` with the dropped name of the
payload inserted at an index: the entries above it are moved up by one. -/
structure Inserted {Γ : Ctx sig} (payload : Term sig [] Srt.pr) (index : Nat)
    (smaller larger : Env Γ) : Prop where
  here : larger index = some (lift0 (droppedName payload))
  below : ∀ j, j < index → larger j = smaller j
  above : ∀ j, index ≤ j → larger (j + 1) = smaller j

/-- Beneath an input the insertion is at the next index. -/
theorem Inserted.up {Γ : Ctx sig} {payload : Term sig [] Srt.pr} {index : Nat}
    {smaller larger : Env Γ} (inserted : Inserted payload index smaller larger) :
    Inserted payload (index + 1) smaller.up larger.up where
  here := by
    simp only [Env.up, inserted.here, Option.map_some, weaken, rename_lift0]
  below := by
    intro j bound
    cases j with
    | zero => rfl
    | succ j =>
        simp only [Env.up]
        rw [inserted.below j (by omega)]
  above := by
    intro j bound
    cases j with
    | zero => omega
    | succ j =>
        simp only [Env.up]
        rw [inserted.above j (by omega)]

/-- An entry above the insertion is the entry one below it. -/
theorem Inserted.moved {Γ : Ctx sig} {payload : Term sig [] Srt.pr} {index j : Nat}
    {smaller larger : Env Γ} (inserted : Inserted payload index smaller larger)
    (above : index < j) : smaller (j - 1) = larger j := by
  have moved := inserted.above (j - 1) (by omega)
  rw [show j - 1 + 1 = j by omega] at moved
  exact moved.symm

/-- **Binder elimination is extension of the environment.**  Whatever
translates in the environment holding the dropped name of the payload at an
index translates, up to the equations, once that binder is eliminated at the
quotation of the payload. -/
theorem translate_instantiate (hq : tProc (Env.empty []) q = some q₀) :
    (∀ {Γ : Ctx sig} (larger : Env Γ) (n : Pattern) (index : Nat) (smaller : Env Γ),
      Inserted q₀ index smaller larger → ∀ t, tName larger n = some t →
        ∃ t', tName smaller (instantiateBVarAt index (literalName q) n) = some t' ∧
          EqClosure equations t' t) ∧
    (∀ {Γ : Ctx sig} (larger : Env Γ) (p : Pattern) (index : Nat) (smaller : Env Γ),
      Inserted q₀ index smaller larger → ∀ t, tProc larger p = some t →
        ∃ t', tProc smaller (instantiateBVarAt index (literalName q) p) = some t' ∧
          EqClosure equations t' t) ∧
    (∀ {Γ : Ctx sig} (larger : Env Γ) (ps : List Pattern) (index : Nat) (smaller : Env Γ),
      Inserted q₀ index smaller larger → ∀ t, tProcs larger ps = some t →
        ∃ t', tProcs smaller (ps.map (instantiateBVarAt index (literalName q))) = some t' ∧
          EqClosure equations t' t) := by
  have closedPayload := wellScoped_of_closed hq
  refine tName.mutual_induct
    (fun {Γ} larger n => ∀ (index : Nat) (smaller : Env Γ),
      Inserted q₀ index smaller larger → ∀ t, tName larger n = some t →
        ∃ t', tName smaller (instantiateBVarAt index (literalName q) n) = some t' ∧
          EqClosure equations t' t)
    (fun {Γ} larger p => ∀ (index : Nat) (smaller : Env Γ),
      Inserted q₀ index smaller larger → ∀ t, tProc larger p = some t →
        ∃ t', tProc smaller (instantiateBVarAt index (literalName q) p) = some t' ∧
          EqClosure equations t' t)
    (fun {Γ} larger ps => ∀ (index : Nat) (smaller : Env Γ),
      Inserted q₀ index smaller larger → ∀ t, tProcs larger ps = some t →
        ∃ t', tProcs smaller (ps.map (instantiateBVarAt index (literalName q))) = some t' ∧
          EqClosure equations t' t)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro Γ larger j index smaller inserted t h
    rw [tName_bvar] at h
    rw [instantiateBVarAt.eq_1]
    rcases Nat.lt_trichotomy j index with lt | rfl | gt
    · rw [if_pos lt, tName_bvar, ← inserted.below j lt]
      exact ⟨t, h, .refl _⟩
    · rw [if_neg (Nat.lt_irrefl _), if_pos rfl, lift_literalName closedPayload,
        tName_literalName hq]
      rw [inserted.here, Option.map_some, nameOf_lift0_droppedName] at h
      exact ⟨t, h, .refl _⟩
    · rw [if_neg (Nat.not_lt_of_gt gt), if_neg (Nat.ne_of_gt gt), tName_bvar,
        inserted.moved gt]
      exact ⟨t, h, .refl _⟩
  · intro Γ larger label index smaller inserted t h
    rw [instantiateBVarAt.eq_2]
    exact ⟨t, h, .refl _⟩
  · intro Γ larger name ih index smaller inserted t h
    rw [tName_quoteDrop] at h
    rw [instantiate_quoteDrop, tName_quoteDrop]
    exact ih index smaller inserted t h
  · intro Γ larger code hcode j head ih index smaller inserted t h
    rw [tName_quote_of_nameHead _ hcode head] at h
    obtain ⟨c, hc, received⟩ := Option.bind_eq_some_iff.mp h
    have hcode' : ∀ name, instantiateBVarAt index (literalName q) code =
        .apply "PDrop" [name] → False := fun name same => by
      obtain ⟨original, rfl⟩ := eq_drop_of_instantiate_eq_drop closedPayload same
      exact hcode original rfl
    obtain ⟨c', hc', equivalent⟩ := ih index smaller inserted c hc
    rw [instantiate_quote]
    rcases Nat.lt_trichotomy j index with lt | rfl | gt
    · have unchanged := instantiate_name_below (literalName q) head lt
      rw [instantiate_quote] at unchanged
      simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at unchanged
      rw [unchanged] at hc' ⊢
      rw [tName_quote_of_nameHead _ hcode head, hc', Option.bind_some,
        ← inserted.below j lt]
      exact ⟨t, received, .refl _⟩
    · have headHere := nameHead_instantiate_here hq head
      rw [instantiate_quote] at headHere
      have closedCode : ∀ k, noBVar k (instantiateBVarAt j (literalName q) code) = true := by
        intro k
        have := noBVar_instantiate_here hq head k
        rw [instantiate_quote] at this
        simpa [noBVar, noBVarList] using this
      obtain ⟨literal, hliteral⟩ := (translate_of_free.2.1 smaller _ ⟨c', hc'⟩ (Env.empty [])
        fun k free => by rw [closedCode k] at free; cases free)
      have lifted : c' = lift0 literal := by
        rw [tProc_closed hliteral smaller] at hc'
        cases hc'
        rfl
      subst lifted
      refine ⟨nameOf (lift0 literal), by rw [tName_quote _ hcode' headHere, hliteral,
        Option.map_some], ?_⟩
      have observedCode : BinderHead.ofPattern rhoReflectivePresentation code =
          .drop (.index j) := by
        have observed := nameHead_eq_some_iff_ofPattern.mp head
        simp only [BinderHead.ofPattern, BinderHead.ofList] at observed
        generalize BinderHead.ofPattern rhoReflectivePresentation code = h at observed
        cases h <;> simp_all [BinderHead.apply, BinderHead.rigid, rhoReflectivePresentation]
      obtain ⟨u, hu, codeEquivalent⟩ := (translate_unit_or_drop.1 larger code c hc).2 j observedCode
      rw [inserted.here] at hu
      cases hu
      rw [inserted.here, Option.map_some, nameOf_lift0_droppedName] at received
      cases received
      rw [lift0_droppedName] at codeEquivalent
      exact (nameOf_equiv _).trans ((equiv_quoT (equivalent.trans codeEquivalent)).trans
        (quoteDrop_equiv _))
    · have headAbove := nameHead_instantiate_above (literalName q) head gt
      rw [instantiate_quote] at headAbove
      rw [tName_quote_of_nameHead _ hcode' headAbove, hc', Option.bind_some,
        inserted.moved gt]
      exact ⟨t, received, .refl _⟩
  · intro Γ larger code hcode head ih index smaller inserted t h
    rw [tName_quote _ hcode head] at h
    obtain ⟨literal, hliteral, rfl⟩ := Option.map_eq_some_iff.mp h
    have unchanged : instantiateBVarAt index (literalName q) code = code :=
      instantiateBVarAt_eq_self_of_isWellScopedAt
        (isWellScopedAt_mono (wellScoped_of_closed hliteral) (Nat.zero_le index))
    rw [instantiate_quote, unchanged, tName_quote _ hcode head, hliteral, Option.map_some]
    exact ⟨_, rfl, .refl _⟩
  · intro x Γ larger hbvar hfvar _ hquote index smaller inserted t h
    rw [tName_eq_none _ hbvar hfvar hquote] at h
    cases h
  · intro Γ larger index smaller inserted t h
    rw [tProc.eq_1] at h
    rw [instantiateBVarAt.eq_3, List.map_nil, tProc.eq_1]
    exact ⟨t, h, .refl _⟩
  · intro Γ larger name j hj ih index smaller inserted t h
    rw [tProc_drop_of_nameHead _ hj] at h
    obtain ⟨m, hm, received⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨m', hm', equivalent⟩ := ih index smaller inserted m hm
    rw [instantiate_drop]
    rcases Nat.lt_trichotomy j index with lt | rfl | gt
    · rw [instantiate_name_below _ hj lt] at hm' ⊢
      rw [tProc_drop_of_nameHead _ hj, hm', Option.bind_some, ← inserted.below j lt]
      exact ⟨t, received, .refl _⟩
    · rw [tProc_drop_of_nameHead_none _ (nameHead_instantiate_here hq hj), hm', Option.map_some]
      have name := tName_of_nameHead hj hm
      rw [inserted.here, Option.map_some, nameOf_lift0_droppedName] at name
      cases name
      rw [inserted.here, lift0_droppedName] at received
      cases received
      exact ⟨_, rfl, equiv_drpT equivalent⟩
    · rw [tProc_drop_of_nameHead _ (nameHead_instantiate_above _ hj gt), hm', Option.bind_some,
        inserted.moved gt]
      exact ⟨t, received, .refl _⟩
  · intro Γ larger name hnone ih index smaller inserted t h
    rw [tProc_drop_of_nameHead_none _ hnone] at h
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨m', hm', equivalent⟩ := ih index smaller inserted m hm
    rw [instantiate_drop, tProc_drop_of_nameHead_none _ (nameHead_instantiate_none hq index hnone),
      hm', Option.map_some]
    exact ⟨_, rfl, equiv_drpT equivalent⟩
  · intro Γ larger name payload ihn ihp index smaller inserted t h
    rw [tProc.eq_3] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨c, hc, process, hprocess, rfl⟩ := h
    obtain ⟨c', hc', equivc⟩ := ihn index smaller inserted c hc
    obtain ⟨process', hprocess', equivp⟩ := ihp index smaller inserted process hprocess
    rw [instantiateBVarAt.eq_3, List.map_cons, List.map_cons, List.map_nil, tProc.eq_3,
      hc', Option.bind_some, hprocess', Option.map_some]
    exact ⟨_, rfl, equiv_outT equivc equivp⟩
  · intro Γ larger name body ihn ihb index smaller inserted t h
    rw [tProc.eq_4] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨c, hc, continuation, hcontinuation, rfl⟩ := h
    obtain ⟨c', hc', equivc⟩ := ihn index smaller inserted c hc
    obtain ⟨continuation', hcontinuation', equivK⟩ :=
      ihb (index + 1) smaller.up inserted.up continuation hcontinuation
    rw [instantiateBVarAt.eq_3, List.map_cons, List.map_cons, List.map_nil,
      instantiateBVarAt.eq_4, tProc.eq_4, hc', Option.bind_some, hcontinuation',
      Option.map_some]
    exact ⟨_, rfl, equiv_inpT equivc equivK⟩
  · intro Γ larger elements ih index smaller inserted t h
    rw [tProc.eq_5] at h
    rw [instantiateBVarAt.eq_7, tProc.eq_5]
    exact ih index smaller inserted t h
  · intro x Γ larger hzero hdrop hout hinp hbag index smaller inserted t h
    rw [tProc.eq_6 _ _ hzero hdrop hout hinp hbag] at h
    cases h
  · intro Γ larger index smaller inserted t h
    rw [tProcs.eq_1] at h
    rw [List.map_nil, tProcs.eq_1]
    exact ⟨t, h, .refl _⟩
  · intro Γ larger process rest ihp ihr index smaller inserted t h
    rw [tProcs.eq_2] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨head, hhead, tail, htail, rfl⟩ := h
    obtain ⟨head', hhead', equivh⟩ := ihp index smaller inserted head hhead
    obtain ⟨tail', htail', equivt⟩ := ihr index smaller inserted tail htail
    rw [List.map_cons, tProcs.eq_2, hhead', Option.bind_some, htail', Option.map_some]
    exact ⟨_, rfl, equiv_parT equivh equivt⟩

/-! ## The authored communication law -/

/-- **The authored communication law.**  Translating the result of the
authored binder elimination is instantiating the translated continuation at
the dropped name of the translated payload, up to quote/drop cancellation. -/
theorem translate_plainCommSubst {body : Pattern} {K : Term sig [Srt.pr] Srt.pr}
    (hbody : tProc (Env.empty []).up body = some K)
    (hq : tProc (Env.empty []) q = some q₀) :
    ∃ t, tProc (Env.empty []) (instantiateBVar (literalName q) body) = some t ∧
      EqClosure equations t (inst K (droppedName q₀)) := by
  obtain ⟨t, translated, equivalent⟩ :=
    translate_bind.2.1 (Env.empty []).up body (extend (droppedName q₀))
      (Env.received (droppedName q₀)) (by
        intro j t h
        cases j with
        | zero =>
            cases h
            rfl
        | succ j => cases h) K hbody
  have inserted : Inserted q₀ 0 (Env.empty []) (Env.received (droppedName q₀)) :=
    { here := by rw [lift0_nil]; rfl
      below := fun j bound => absurd bound (Nat.not_lt_zero j)
      above := fun j _ => rfl }
  obtain ⟨t', instantiated, equivalent'⟩ :=
    (translate_instantiate hq).2.1 (Env.received (droppedName q₀)) body 0
      (Env.empty []) inserted t translated
  exact ⟨t', instantiated, equivalent'.trans equivalent⟩

end Mettapedia.OSLF.Binding.RhoPayloadPresentation
