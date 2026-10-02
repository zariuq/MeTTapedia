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
payload*: at every name position the two agree, and at every drop of the
received name the textual elimination leaves the drop of the quoted payload
where the payload presentation runs the payload itself.

Three facts are proved.

* A translatable pattern mentions no bound index its environment lacks.
* Eliminating a binder at the quotation of a closed translatable payload
  translates as the unsubstituted pattern in the environment that holds the
  dropped name of the payload at that index.
* The translation of the authored communication result is the continuation
  instantiated at the dropped name of the payload, up to the equations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoPayloadPresentation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern CollType)
open Mettapedia.OSLF.MeTTaIL.Substitution
  (instantiateBVarAt instantiateBVar liftBVars_eq_self_of_isWellScopedAt
    instantiateBVarAt_eq_self_of_isWellScopedAt)
open Mettapedia.OSLF.MeTTaIL.ScopedPattern (isWellScopedAt_mono)

/-! ## Translatable patterns are scoped -/

/-- A name that denotes a bound index is in scope exactly when that index is. -/
theorem nameHead_wellScoped {name : Pattern} {index : Nat}
    (head : nameHead name = some index) (depth : Nat) :
    name.isWellScopedAt depth = decide (index < depth) := by
  induction name using nameHead.induct with
  | case1 k =>
      simp only [nameHead, Option.some.injEq] at head
      subst head
      rfl
  | case2 inner ih =>
      rw [nameHead.eq_2] at head
      simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, ih head]
  | case3 x hbvar hquoteDrop =>
      rw [nameHead.eq_3 x hbvar hquoteDrop] at head
      cases head

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
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro Γ ρ k depth beyond t h
    rw [tName.eq_1] at h
    simp only [Pattern.isWellScopedAt, decide_eq_true_eq]
    by_contra outside
    rw [beyond k (Nat.le_of_not_lt outside)] at h
    cases h
  · intro Γ ρ label depth beyond t h
    simp [Pattern.isWellScopedAt]
  · intro Γ ρ name ih depth beyond t h
    rw [tName.eq_3] at h
    simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using ih depth beyond t h
  · intro Γ ρ code hcode ih depth beyond t h
    rw [tName.eq_4 _ _ hcode] at h
    obtain ⟨literal, hliteral, -⟩ := Option.map_eq_some_iff.mp h
    have closed := ih 0 (fun _ _ => rfl) literal hliteral
    simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using
      isWellScopedAt_mono closed (Nat.zero_le depth)
  · intro x Γ ρ hbvar hfvar hquoteDrop hquote depth beyond t h
    rw [tName.eq_5 _ _ hbvar hfvar hquoteDrop hquote] at h
    cases h
  · intro Γ ρ depth beyond t h
    simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt]
  · intro Γ ρ name k hk depth beyond t h
    simp only [tProc.eq_2, hk] at h
    simp only [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Bool.and_true]
    rw [nameHead_wellScoped hk, decide_eq_true_eq]
    by_contra outside
    rw [beyond k (Nat.le_of_not_lt outside)] at h
    cases h
  · intro Γ ρ name hk ih depth beyond t h
    simp only [tProc.eq_2, hk] at h
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
    nameHead (literalName q) = none := by
  by_cases hdrop : ∃ m, q = .apply "PDrop" [m]
  · obtain ⟨m, rfl⟩ := hdrop
    rw [literalName, nameHead.eq_2]
    rw [tProc.eq_2] at hq
    cases hm : nameHead m with
    | some k => simp [hm, Env.empty] at hq
    | none => rfl
  · exact nameHead.eq_3 _ (by simp)
      (fun m e => hdrop ⟨m, by simpa using e⟩)

/-- The quotation of a closed translatable payload is the name of the
payload, in every environment. -/
theorem tName_literalName (hq : tProc (Env.empty []) q = some q₀) {Γ : Ctx sig}
    (ρ : Env Γ) : tName ρ (literalName q) = some (nameOf (lift0 q₀)) := by
  by_cases hdrop : ∃ m, q = .apply "PDrop" [m]
  · obtain ⟨m, rfl⟩ := hdrop
    rw [literalName, tName.eq_3]
    rw [tProc.eq_2] at hq
    cases hm : nameHead m with
    | some k => simp [hm, Env.empty] at hq
    | none =>
        simp only [hm] at hq
        obtain ⟨m₀, hm₀, rfl⟩ := Option.map_eq_some_iff.mp hq
        rw [tName_closed hm₀ ρ]
        rfl
  · have hnot : ∀ m, q = .apply "PDrop" [m] → False := fun m h => hdrop ⟨m, h⟩
    rw [literalName, tName.eq_4 _ _ hnot, hq, Option.map_some]

/-- The quotation of a locally closed payload is unchanged by lifting. -/
theorem lift_literalName (closedPayload : q.isWellScopedAt 0 = true) (depth : Nat) :
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0 depth (literalName q) = literalName q :=
  liftBVars_eq_self_of_isWellScopedAt
    (by simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, closedPayload])

/-! ## Binder elimination at a name -/

theorem instantiate_quoteDrop (depth : Nat) (replacement name : Pattern) :
    instantiateBVarAt depth replacement (.apply "NQuote" [.apply "PDrop" [name]]) =
      .apply "NQuote" [.apply "PDrop" [instantiateBVarAt depth replacement name]] := by
  simp only [instantiateBVarAt, List.map_cons, List.map_nil]

theorem instantiate_drop (depth : Nat) (replacement name : Pattern) :
    instantiateBVarAt depth replacement (.apply "PDrop" [name]) =
      .apply "PDrop" [instantiateBVarAt depth replacement name] := by
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
  induction name using nameHead.induct with
  | case1 k =>
      simp only [nameHead, Option.some.injEq] at head
      subst head
      rw [instantiateBVarAt.eq_1, if_neg (Nat.not_lt_of_gt above), if_neg (Nat.ne_of_gt above)]
      rfl
  | case2 inner ih =>
      rw [nameHead.eq_2] at head
      rw [instantiate_quoteDrop, nameHead.eq_2]
      exact ih head
  | case3 x hbvar hquoteDrop =>
      rw [nameHead.eq_3 x hbvar hquoteDrop] at head
      cases head

/-- A name denoting the eliminated binder becomes a name that denotes no
bound index and translates to the name of the payload. -/
theorem nameHead_instantiate_here (hq : tProc (Env.empty []) q = some q₀)
    {name : Pattern} {depth : Nat} (head : nameHead name = some depth) :
    nameHead (instantiateBVarAt depth (literalName q) name) = none ∧
      ∀ {Γ : Ctx sig} (ρ : Env Γ),
        tName ρ (instantiateBVarAt depth (literalName q) name) = some (nameOf (lift0 q₀)) := by
  induction name using nameHead.induct with
  | case1 k =>
      simp only [nameHead, Option.some.injEq] at head
      subst head
      rw [instantiateBVarAt.eq_1, if_neg (Nat.lt_irrefl _), if_pos rfl,
        lift_literalName (wellScoped_of_closed hq)]
      exact ⟨nameHead_literalName hq, fun ρ => tName_literalName hq ρ⟩
  | case2 inner ih =>
      rw [nameHead.eq_2] at head
      rw [instantiate_quoteDrop, nameHead.eq_2]
      refine ⟨(ih head).1, fun ρ => ?_⟩
      rw [tName.eq_3]
      exact (ih head).2 ρ
  | case3 x hbvar hquoteDrop =>
      rw [nameHead.eq_3 x hbvar hquoteDrop] at head
      cases head

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
eliminated at a quotation. -/
theorem nameHead_instantiate_none (closedPayload : q.isWellScopedAt 0 = true)
    {name : Pattern} (depth : Nat) (head : nameHead name = none) :
    nameHead (instantiateBVarAt depth (literalName q) name) = none := by
  induction name using nameHead.induct with
  | case1 k => simp [nameHead] at head
  | case2 inner ih =>
      rw [nameHead.eq_2] at head
      rw [instantiate_quoteDrop, nameHead.eq_2]
      exact ih head
  | case3 x hbvar hquoteDrop =>
      apply nameHead.eq_3
      · intro k same
        cases x with
        | bvar index => exact hbvar index rfl
        | fvar label => simp [instantiateBVarAt] at same
        | apply label arguments => simp [instantiateBVarAt] at same
        | lambda binder body => simp [instantiateBVarAt] at same
        | multiLambda arity binders body => simp [instantiateBVarAt] at same
        | subst body replacement => simp [instantiateBVarAt] at same
        | collection kind elements rest => simp [instantiateBVarAt] at same
      · intro inner same
        cases x with
        | bvar index => exact hbvar index rfl
        | fvar label => simp [instantiateBVarAt] at same
        | apply label arguments =>
            rw [instantiateBVarAt.eq_3] at same
            simp only [Pattern.apply.injEq] at same
            obtain ⟨rfl, mapped⟩ := same
            cases arguments with
            | nil => simp at mapped
            | cons argument rest =>
                cases rest with
                | nil =>
                    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
                    obtain ⟨original, rfl⟩ :=
                      eq_drop_of_instantiate_eq_drop closedPayload mapped
                    exact hquoteDrop original rfl
                | cons _ _ => simp at mapped
        | lambda binder body => simp [instantiateBVarAt] at same
        | multiLambda arity binders body => simp [instantiateBVarAt] at same
        | subst body replacement => simp [instantiateBVarAt] at same
        | collection kind elements rest => simp [instantiateBVarAt] at same

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

/-- **Binder elimination is extension of the environment.**  Whatever
translates in the environment holding the dropped name of the payload at an
index translates to the same term once that binder is eliminated at the
quotation of the payload. -/
theorem translate_instantiate (hq : tProc (Env.empty []) q = some q₀) :
    (∀ {Γ : Ctx sig} (larger : Env Γ) (n : Pattern) (index : Nat) (smaller : Env Γ),
      Inserted q₀ index smaller larger → ∀ t, tName larger n = some t →
        tName smaller (instantiateBVarAt index (literalName q) n) = some t) ∧
    (∀ {Γ : Ctx sig} (larger : Env Γ) (p : Pattern) (index : Nat) (smaller : Env Γ),
      Inserted q₀ index smaller larger → ∀ t, tProc larger p = some t →
        tProc smaller (instantiateBVarAt index (literalName q) p) = some t) ∧
    (∀ {Γ : Ctx sig} (larger : Env Γ) (ps : List Pattern) (index : Nat) (smaller : Env Γ),
      Inserted q₀ index smaller larger → ∀ t, tProcs larger ps = some t →
        tProcs smaller (ps.map (instantiateBVarAt index (literalName q))) = some t) := by
  have closedPayload := wellScoped_of_closed hq
  refine tName.mutual_induct
    (fun {Γ} larger n => ∀ (index : Nat) (smaller : Env Γ),
      Inserted q₀ index smaller larger → ∀ t, tName larger n = some t →
        tName smaller (instantiateBVarAt index (literalName q) n) = some t)
    (fun {Γ} larger p => ∀ (index : Nat) (smaller : Env Γ),
      Inserted q₀ index smaller larger → ∀ t, tProc larger p = some t →
        tProc smaller (instantiateBVarAt index (literalName q) p) = some t)
    (fun {Γ} larger ps => ∀ (index : Nat) (smaller : Env Γ),
      Inserted q₀ index smaller larger → ∀ t, tProcs larger ps = some t →
        tProcs smaller (ps.map (instantiateBVarAt index (literalName q))) = some t)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro Γ larger j index smaller inserted t h
    rw [tName.eq_1] at h
    rw [instantiateBVarAt.eq_1]
    rcases Nat.lt_trichotomy j index with lt | rfl | gt
    · rw [if_pos lt, tName.eq_1, ← inserted.below j lt]
      exact h
    · rw [if_neg (Nat.lt_irrefl _), if_pos rfl, lift_literalName closedPayload,
        tName_literalName hq]
      rw [inserted.here, Option.map_some, nameOf_lift0_droppedName] at h
      exact h
    · rw [if_neg (Nat.not_lt_of_gt gt), if_neg (Nat.ne_of_gt gt), tName.eq_1]
      have moved := inserted.above (j - 1) (by omega)
      rw [show j - 1 + 1 = j by omega] at moved
      rw [← moved]
      exact h
  · intro Γ larger label index smaller inserted t h
    rw [tName.eq_2] at h
    rw [instantiateBVarAt.eq_2, tName.eq_2]
    exact h
  · intro Γ larger name ih index smaller inserted t h
    rw [tName.eq_3] at h
    rw [instantiate_quoteDrop, tName.eq_3]
    exact ih index smaller inserted t h
  · intro Γ larger code hcode ih index smaller inserted t h
    rw [tName.eq_4 _ _ hcode] at h
    obtain ⟨literal, hliteral, rfl⟩ := Option.map_eq_some_iff.mp h
    have unchanged : instantiateBVarAt index (literalName q) code = code :=
      instantiateBVarAt_eq_self_of_isWellScopedAt
        (isWellScopedAt_mono (wellScoped_of_closed hliteral) (Nat.zero_le index))
    rw [instantiateBVarAt.eq_3, List.map_cons, List.map_nil, unchanged,
      tName.eq_4 _ _ hcode, hliteral, Option.map_some]
  · intro x Γ larger hbvar hfvar hquoteDrop hquote index smaller inserted t h
    rw [tName.eq_5 _ _ hbvar hfvar hquoteDrop hquote] at h
    cases h
  · intro Γ larger index smaller inserted t h
    rw [tProc.eq_1] at h
    rw [instantiateBVarAt.eq_3, List.map_nil, tProc.eq_1]
    exact h
  · intro Γ larger name j hj index smaller inserted t h
    simp only [tProc.eq_2, hj] at h
    rw [instantiate_drop, tProc.eq_2]
    rcases Nat.lt_trichotomy j index with lt | rfl | gt
    · rw [instantiate_name_below _ hj lt]
      simp only [hj]
      rw [← inserted.below j lt]
      exact h
    · obtain ⟨headNone, translated⟩ := nameHead_instantiate_here hq hj
      simp only [headNone, translated smaller, Option.map_some]
      rw [inserted.here, lift0_droppedName] at h
      exact h
    · simp only [nameHead_instantiate_above _ hj gt]
      have moved := inserted.above (j - 1) (by omega)
      rw [show j - 1 + 1 = j by omega] at moved
      rw [← moved]
      exact h
  · intro Γ larger name hnone ih index smaller inserted t h
    simp only [tProc.eq_2, hnone] at h
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [instantiate_drop, tProc.eq_2]
    simp only [nameHead_instantiate_none closedPayload index hnone, ih index smaller inserted m hm,
      Option.map_some]
  · intro Γ larger name payload ihn ihp index smaller inserted t h
    rw [tProc.eq_3] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨c, hc, process, hprocess, rfl⟩ := h
    rw [instantiateBVarAt.eq_3, List.map_cons, List.map_cons, List.map_nil, tProc.eq_3,
      ihn index smaller inserted c hc, Option.bind_some,
      ihp index smaller inserted process hprocess, Option.map_some]
  · intro Γ larger name body ihn ihb index smaller inserted t h
    rw [tProc.eq_4] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨c, hc, continuation, hcontinuation, rfl⟩ := h
    rw [instantiateBVarAt.eq_3, List.map_cons, List.map_cons, List.map_nil,
      instantiateBVarAt.eq_4, tProc.eq_4, ihn index smaller inserted c hc, Option.bind_some,
      ihb (index + 1) smaller.up inserted.up continuation hcontinuation, Option.map_some]
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
    exact h
  · intro Γ larger process rest ihp ihr index smaller inserted t h
    rw [tProcs.eq_2] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨head, hhead, tail, htail, rfl⟩ := h
    rw [List.map_cons, tProcs.eq_2, ihp index smaller inserted head hhead, Option.bind_some,
      ihr index smaller inserted tail htail, Option.map_some]

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
  refine ⟨t, ?_, equivalent⟩
  refine (translate_instantiate hq).2.1 (Env.received (droppedName q₀)) body 0
    (Env.empty []) ?_ t translated
  exact
    { here := by rw [lift0_nil]; rfl
      below := fun j bound => absurd bound (Nat.not_lt_zero j)
      above := fun j _ => rfl }

end Mettapedia.OSLF.Binding.RhoPayloadPresentation
