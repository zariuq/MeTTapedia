import Mettapedia.OSLF.Syntax.RhoPayloadPresentation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SemanticSubstitution

/-!
# Authored rho processes in the payload presentation

An authored process uses bound names. The translation reads each bound name
as the quotation of the process received there, and each drop of a bound
name as that process. A whole name is resolved up to quote/drop cancellation
before scope is consulted, so `@*y` denotes the bound name `y`. Any other
quotation is literal code: it is translated with no bound names in scope,
so an outer binder never reaches inside it.

The translation is parameterised by an environment giving the process
received at each bound index. Under an input the environment is extended by
the new variable.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoPayloadPresentation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern CollType)

/-- The process received at each bound index, if any. -/
abbrev Env (Γ : Ctx sig) : Type := Nat → Option (Term sig Γ Srt.pr)

/-- No bound index is in scope. -/
def Env.empty (Γ : Ctx sig) : Env Γ := fun _ => none

/-- Beneath an input, index zero is the newly received process. -/
def Env.up {Γ : Ctx sig} (ρ : Env Γ) : Env (Srt.pr :: Γ)
  | 0 => some (.var .zero)
  | k + 1 => (ρ k).map weaken

/-- The unique renaming out of the empty context. -/
def emptyRen (Γ : Ctx sig) : Ren sig [] Γ := fun _ v => by cases v

/-- Closed code, placed in any context. -/
def lift0 {Γ : Ctx sig} {s : Srt} (t : Term sig [] s) : Term sig Γ s :=
  rename (emptyRen Γ) t

/-- The name of a process. The name of a dropped name is that name. -/
def nameOf {Γ : Ctx sig} : Term sig Γ Srt.pr → Term sig Γ Srt.nm
  | .op Op.drp (.cons name .nil) => name
  | process => quoT process

/-- The bound index a name denotes, up to quote/drop cancellation. -/
def nameHead : Pattern → Option Nat
  | .bvar k => some k
  | .apply "NQuote" [.apply "PDrop" [name]] => nameHead name
  | _ => none

mutual

/-- Translate a name: a bound name is the name of its received process,
a quote/drop redex is resolved as a whole name, and any other quotation is
literal code with no bound names in scope. -/
def tName {Γ : Ctx sig} (ρ : Env Γ) : Pattern → Option (Term sig Γ Srt.nm)
  | .bvar k => (ρ k).map nameOf
  | .fvar label => some (freeT label)
  | .apply "NQuote" [.apply "PDrop" [name]] => tName ρ name
  | .apply "NQuote" [code] =>
      (tProc (Env.empty []) code).map fun literal => nameOf (lift0 literal)
  | _ => none

/-- Translate a process of the reflective core. A drop of a bound name is
the received process itself; any other drop is inert. -/
def tProc {Γ : Ctx sig} (ρ : Env Γ) : Pattern → Option (Term sig Γ Srt.pr)
  | .apply "PZero" [] => some nilT
  | .apply "PDrop" [name] =>
      match nameHead name with
      | some k => ρ k
      | none => (tName ρ name).map drpT
  | .apply "POutput" [name, payload] =>
      (tName ρ name).bind fun channel =>
        (tProc ρ payload).map fun process => outT channel process
  | .apply "PInput" [name, .lambda none body] =>
      (tName ρ name).bind fun channel =>
        (tProc ρ.up body).map fun continuation => inpT channel continuation
  | .collection .hashBag elements none => tProcs ρ elements
  | _ => none

/-- A parallel bag, composed from the left with the null process last. -/
def tProcs {Γ : Ctx sig} (ρ : Env Γ) : List Pattern → Option (Term sig Γ Srt.pr)
  | [] => some nilT
  | process :: rest =>
      (tProc ρ process).bind fun head =>
        (tProcs ρ rest).map fun tail => parT head tail

end


/-! ## Closed code and renaming -/

section Renaming

variable {Γ Δ : Ctx sig}

/-- Every renaming out of the empty context places closed code. -/
theorem rename_empty_eq_lift0 (r : Ren sig [] Γ) {s : Srt} (t : Term sig [] s) :
    rename r t = lift0 t := by
  unfold lift0
  congr 1
  funext _ v
  cases v

theorem rename_lift0 (r : Ren sig Γ Δ) {s : Srt} (t : Term sig [] s) :
    rename r (lift0 t) = lift0 t := by
  unfold lift0
  rw [rename_comp]
  exact rename_empty_eq_lift0 _ t

theorem lift0_nil {s : Srt} (t : Term sig [] s) : lift0 (Γ := []) t = t :=
  (rename_empty_eq_lift0 (fun _ v => v) t).symm.trans (rename_id t)

/-- Every substitution out of the empty context places closed code. -/
theorem bind_empty_eq_lift0 (τ : Sub sig [] Γ) {s : Srt} (t : Term sig [] s) :
    bind τ t = lift0 t := by
  have hτ : τ = fun s v => Term.var (emptyRen Γ s v) := by
    funext _ v
    cases v
  rw [hτ, bind_var_eq_rename]
  exact rename_empty_eq_lift0 _ t

theorem bind_lift0 (σ : Sub sig Γ Δ) {s : Srt} (t : Term sig [] s) :
    bind σ (lift0 t) = lift0 t := by
  unfold lift0
  rw [bind_rename]
  exact bind_empty_eq_lift0 _ t

theorem nameOf_drpT (m : Term sig Γ Srt.nm) : nameOf (drpT m) = m := rfl

theorem rename_nameOf (r : Ren sig Γ Δ) (t : Term sig Γ Srt.pr) :
    rename r (nameOf t) = nameOf (rename r t) := by
  cases t with
  | var v => rfl
  | op o args =>
      cases o with
      | drp =>
          cases args with
          | cons name tail =>
              match tail with
              | .nil => rfl
      | _ => rfl

/-- The environment beneath an input follows a renaming lifted past the
received process. -/
theorem up_rename (r : Ren sig Γ Δ) {ρ : Env Γ} {ρ' : Env Δ}
    (hρ : ∀ j t, ρ j = some t → ρ' j = some (rename r t)) :
    ∀ j t, ρ.up j = some t → ρ'.up j = some (rename (liftRen r [Srt.pr]) t) := by
  intro j t h
  cases j with
  | zero =>
      cases h
      rfl
  | succ j =>
      simp only [Env.up, Option.map_eq_some_iff] at h ⊢
      obtain ⟨u, hu, rfl⟩ := h
      refine ⟨rename r u, hρ j u hu, ?_⟩
      simp only [weaken, rename_comp]
      rfl

/-- Translation commutes with renaming, and an environment with more
entries translates at least as much. -/
theorem translate_rename :
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (n : Pattern) {Δ : Ctx sig} (r : Ren sig Γ Δ)
        (ρ' : Env Δ), (∀ j t, ρ j = some t → ρ' j = some (rename r t)) →
      ∀ t, tName ρ n = some t → tName ρ' n = some (rename r t)) ∧
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (p : Pattern) {Δ : Ctx sig} (r : Ren sig Γ Δ)
        (ρ' : Env Δ), (∀ j t, ρ j = some t → ρ' j = some (rename r t)) →
      ∀ t, tProc ρ p = some t → tProc ρ' p = some (rename r t)) ∧
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (ps : List Pattern) {Δ : Ctx sig} (r : Ren sig Γ Δ)
        (ρ' : Env Δ), (∀ j t, ρ j = some t → ρ' j = some (rename r t)) →
      ∀ t, tProcs ρ ps = some t → tProcs ρ' ps = some (rename r t)) := by
  refine tName.mutual_induct
    (fun {Γ} ρ n => ∀ {Δ : Ctx sig} (r : Ren sig Γ Δ) (ρ' : Env Δ),
      (∀ j t, ρ j = some t → ρ' j = some (rename r t)) →
      ∀ t, tName ρ n = some t → tName ρ' n = some (rename r t))
    (fun {Γ} ρ p => ∀ {Δ : Ctx sig} (r : Ren sig Γ Δ) (ρ' : Env Δ),
      (∀ j t, ρ j = some t → ρ' j = some (rename r t)) →
      ∀ t, tProc ρ p = some t → tProc ρ' p = some (rename r t))
    (fun {Γ} ρ ps => ∀ {Δ : Ctx sig} (r : Ren sig Γ Δ) (ρ' : Env Δ),
      (∀ j t, ρ j = some t → ρ' j = some (rename r t)) →
      ∀ t, tProcs ρ ps = some t → tProcs ρ' ps = some (rename r t))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro Γ ρ k Δ r ρ' hρ t h
    rw [tName.eq_1] at h ⊢
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [hρ k u hu, Option.map_some, rename_nameOf]
  · intro Γ ρ label Δ r ρ' hρ t h
    rw [tName.eq_2] at h ⊢
    cases h
    rfl
  · intro Γ ρ name ih Δ r ρ' hρ t h
    rw [tName.eq_3] at h ⊢
    exact ih r ρ' hρ t h
  · intro Γ ρ code hcode _ Δ r ρ' hρ t h
    rw [tName.eq_4 _ _ hcode] at h ⊢
    obtain ⟨literal, hliteral, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [hliteral, Option.map_some, rename_nameOf, rename_lift0]
  · intro x Γ ρ hbvar hfvar hquoteDrop hquote Δ r ρ' hρ t h
    rw [tName.eq_5 _ _ hbvar hfvar hquoteDrop hquote] at h
    cases h
  · intro Γ ρ Δ r ρ' hρ t h
    rw [tProc.eq_1] at h ⊢
    cases h
    rfl
  · intro Γ ρ name k hk Δ r ρ' hρ t h
    simp only [tProc.eq_2, hk] at h ⊢
    exact hρ k t h
  · intro Γ ρ name hk ih Δ r ρ' hρ t h
    simp only [tProc.eq_2, hk] at h ⊢
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [ih r ρ' hρ m hm, Option.map_some]
    rfl
  · intro Γ ρ name payload ihn ihp Δ r ρ' hρ t h
    rw [tProc.eq_3] at h ⊢
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨c, hc, process, hprocess, rfl⟩ := h
    rw [ihn r ρ' hρ c hc, Option.bind_some, ihp r ρ' hρ process hprocess, Option.map_some]
    rfl
  · intro Γ ρ name body ihn ihb Δ r ρ' hρ t h
    rw [tProc.eq_4] at h ⊢
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨c, hc, continuation, hcontinuation, rfl⟩ := h
    rw [ihn r ρ' hρ c hc, Option.bind_some,
      ihb (liftRen r [Srt.pr]) ρ'.up (up_rename r hρ) continuation hcontinuation,
      Option.map_some]
    rfl
  · intro Γ ρ elements ih Δ r ρ' hρ t h
    rw [tProc.eq_5] at h ⊢
    exact ih r ρ' hρ t h
  · intro x Γ ρ hzero hdrop hout hinp hbag Δ r ρ' hρ t h
    rw [tProc.eq_6 _ _ hzero hdrop hout hinp hbag] at h
    cases h
  · intro Γ ρ Δ r ρ' hρ t h
    rw [tProcs.eq_1] at h ⊢
    cases h
    rfl
  · intro Γ ρ process rest ihp ihr Δ r ρ' hρ t h
    rw [tProcs.eq_2] at h ⊢
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨head, hhead, tail, htail, rfl⟩ := h
    rw [ihp r ρ' hρ head hhead, Option.bind_some, ihr r ρ' hρ tail htail, Option.map_some]
    rfl

/-- A closed name translates the same way in every environment. -/
theorem tName_closed {n : Pattern} {t : Term sig [] Srt.nm}
    (h : tName (Env.empty []) n = some t) (ρ : Env Γ) :
    tName ρ n = some (lift0 t) := by
  exact translate_rename.1 (Env.empty []) n (emptyRen Γ) ρ (fun _ _ h => by cases h) t h

/-- A closed process translates the same way in every environment. -/
theorem tProc_closed {p : Pattern} {t : Term sig [] Srt.pr}
    (h : tProc (Env.empty []) p = some t) (ρ : Env Γ) :
    tProc ρ p = some (lift0 t) := by
  exact translate_rename.2.1 (Env.empty []) p (emptyRen Γ) ρ (fun _ _ h => by cases h) t h

/-- A name that denotes no bound index does not consult the environment. -/
theorem tName_env_irrelevant (n : Pattern) (h : nameHead n = none) (ρ ρ' : Env Γ) :
    tName ρ n = tName ρ' n := by
  induction n using nameHead.induct with
  | case1 k => simp [nameHead] at h
  | case2 name ih =>
      rw [nameHead.eq_2] at h
      rw [tName.eq_3, tName.eq_3, ih h]
  | case3 x hbvar hquoteDrop =>
      rw [tName.eq_def, tName.eq_def]
      split
      · exact (hbvar _ rfl).elim
      · rfl
      · exact (hquoteDrop _ rfl).elim
      · rfl
      · rfl

end Renaming

/-! ## Name normalization

The executor normalizes a name by cancelling `@*` before it compares names.
The translation already resolves `@*n` as the whole name `n`, so a name and
its normal form have the same translation. -/

section Normalization

open Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-- Normalization sends a process that is not a drop to one that is not a
drop. -/
theorem semanticNormalizeProc_not_drop {p : Pattern}
    (h : ∀ n, p = .apply "PDrop" [n] → False) :
    ∀ n, semanticNormalizeProc p = .apply "PDrop" [n] → False := by
  intro n hn
  rw [semanticNormalizeProc.eq_def] at hn
  split at hn <;> first | (simp at hn; done) | exact h _ rfl | exact h _ hn

/-- A normal name is not a quoted drop. -/
theorem semanticNormalizeName_not_quoteDrop (n : Pattern) :
    ∀ m, semanticNormalizeName n = .apply "NQuote" [.apply "PDrop" [m]] → False := by
  refine (semanticNormalizeName.mutual_induct
    (fun n => ∀ m, semanticNormalizeName n = .apply "NQuote" [.apply "PDrop" [m]] → False)
    (fun _ => True) (fun _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).1 n
  · intro k m h
    simp [semanticNormalizeName] at h
  · intro x m h
    simp [semanticNormalizeName] at h
  · intro n ih m h
    rw [semanticNormalizeName.eq_3] at h
    exact ih m h
  · intro p hp _ m h
    rw [semanticNormalizeName.eq_4 p hp] at h
    simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at h
    exact semanticNormalizeProc_not_drop hp _ h
  · intro n _ _ hquoteDrop _ m h
    rw [semanticNormalizeName.eq_5 n (by assumption) (by assumption) hquoteDrop
      (by assumption)] at h
    exact hquoteDrop m h
  all_goals intros; trivial

/-- Normalization preserves the bound index a name denotes. -/
theorem nameHead_semanticNormalizeName (n : Pattern) :
    nameHead (semanticNormalizeName n) = nameHead n := by
  refine (semanticNormalizeName.mutual_induct
    (fun n => nameHead (semanticNormalizeName n) = nameHead n)
    (fun _ => True) (fun _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).1 n
  · intro k
    simp [semanticNormalizeName]
  · intro x
    simp [semanticNormalizeName]
  · intro n ih
    rw [semanticNormalizeName.eq_3, nameHead.eq_2, ih]
  · intro p hp _
    rw [semanticNormalizeName.eq_4 p hp]
    rw [nameHead.eq_3 _ (by simp), nameHead.eq_3 _ (by simp)]
    · intro m h
      simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at h
      exact hp m h
    · intro m h
      simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at h
      exact semanticNormalizeProc_not_drop hp m h
  · intro n hbvar hfvar hquoteDrop hquote
    rw [semanticNormalizeName.eq_5 n hbvar hfvar hquoteDrop hquote]
  all_goals intros; trivial

/-- A process that is none of the translated forms has no translation. -/
theorem tProc_eq_none_of_not {Γ : Ctx sig} (ρ : Env Γ) (p : Pattern)
    (hzero : p = .apply "PZero" [] → False)
    (hdrop : ∀ name, p = .apply "PDrop" [name] → False)
    (hout : ∀ name payload, p = .apply "POutput" [name, payload] → False)
    (hinp : ∀ name body, p = .apply "PInput" [name, .lambda none body] → False)
    (hbag : ∀ elements, p = .collection .hashBag elements none → False) :
    tProc ρ p = none :=
  tProc.eq_6 ρ p hzero hdrop hout hinp hbag

/-- The translation of a name is that of its normal form. -/
theorem translate_semanticNormalize :
    (∀ n : Pattern, ∀ {Γ : Ctx sig} (ρ : Env Γ),
      tName ρ (semanticNormalizeName n) = tName ρ n) ∧
    (∀ p : Pattern, ∀ {Γ : Ctx sig} (ρ : Env Γ),
      tProc ρ (semanticNormalizeProc p) = tProc ρ p) ∧
    (∀ ps : List Pattern, ∀ {Γ : Ctx sig} (ρ : Env Γ),
      tProcs ρ (semanticNormalizeProcList ps) = tProcs ρ ps) := by
  refine semanticNormalizeName.mutual_induct
    (fun n => ∀ {Γ : Ctx sig} (ρ : Env Γ), tName ρ (semanticNormalizeName n) = tName ρ n)
    (fun p => ∀ {Γ : Ctx sig} (ρ : Env Γ), tProc ρ (semanticNormalizeProc p) = tProc ρ p)
    (fun ps => ∀ {Γ : Ctx sig} (ρ : Env Γ),
      tProcs ρ (semanticNormalizeProcList ps) = tProcs ρ ps)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro k Γ ρ
    simp [semanticNormalizeName]
  · intro x Γ ρ
    simp [semanticNormalizeName]
  · intro n ih Γ ρ
    rw [semanticNormalizeName.eq_3, tName.eq_3, ih]
  · intro p hp ih Γ ρ
    rw [semanticNormalizeName.eq_4 p hp, tName.eq_4 _ _ hp,
      tName.eq_4 _ _ (semanticNormalizeProc_not_drop hp), ih]
  · intro n hbvar hfvar hquoteDrop hquote Γ ρ
    rw [semanticNormalizeName.eq_5 n hbvar hfvar hquoteDrop hquote]
  · intro k Γ ρ
    simp [semanticNormalizeProc]
  · intro x Γ ρ
    simp [semanticNormalizeProc]
  · intro n q ihn ihq Γ ρ
    rw [semanticNormalizeProc.eq_3, tProc.eq_3, tProc.eq_3, ihn, ihq]
  · intro n body ihn ihbody Γ ρ
    rw [semanticNormalizeProc.eq_4, tProc.eq_4, tProc.eq_4, ihn, ihbody]
  · intro n ihn Γ ρ
    rw [semanticNormalizeProc.eq_5, tProc.eq_2, tProc.eq_2,
      nameHead_semanticNormalizeName, ihn]
  · intro p _ Γ ρ
    rw [semanticNormalizeProc.eq_6]
    rw [tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
      tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp)]
  · intro nm body _ Γ ρ
    rw [semanticNormalizeProc.eq_7]
    rw [tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
      tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp)]
  · intro n nms body _ Γ ρ
    rw [semanticNormalizeProc.eq_8]
    rw [tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
      tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp)]
  · intro body repl _ _ Γ ρ
    rw [semanticNormalizeProc.eq_9]
    rw [tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
      tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp)]
  · intro ct elems rest ih Γ ρ
    rw [semanticNormalizeProc.eq_10]
    by_cases hbag : ct = .hashBag ∧ rest = none
    · obtain ⟨rfl, rfl⟩ := hbag
      rw [tProc.eq_5, tProc.eq_5, ih]
    · have hne : ∀ elements : List Pattern, ∀ others : List Pattern,
          Pattern.collection ct others rest = .collection .hashBag elements none → False := by
        intro elements others h
        simp only [Pattern.collection.injEq] at h
        exact hbag ⟨h.1, h.2.2⟩
      rw [tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp)
          (fun elements => hne elements _),
        tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp)
          (fun elements => hne elements _)]
  · intro p hbvar hfvar hout hinp hdrop hquote hlam hmulti hsubst hcoll Γ ρ
    rw [semanticNormalizeProc.eq_11 p hbvar hfvar hout hinp hdrop hquote hlam hmulti
      hsubst hcoll]
  · intro Γ ρ
    rfl
  · intro p ps ihp ihps Γ ρ
    simp only [semanticNormalizeProcList, tProcs, ihp, ihps]

end Normalization

/-! ## Communication is extension of the environment

Executor COMM replaces every whole name of the received channel by the
quoted payload and runs the payload at each drop of that name. Translating
the result is translating the continuation with the payload received at
that index. -/

section Communication

open Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-- The three outcomes of the executor's name substitution. -/
theorem semanticSubstNameMark_spec (k : Nat) (replacement name : Pattern) :
    (semanticNormalizeName name = .bvar k ∧
      semanticSubstNameMark k replacement name = (replacement, true)) ∨
    (∃ m, m ≠ k ∧ semanticNormalizeName name = .bvar m ∧
      semanticSubstNameMark k replacement name = (.bvar m, false)) ∨
    ((∀ m, semanticNormalizeName name ≠ .bvar m) ∧
      semanticSubstNameMark k replacement name = (semanticNormalizeName name, false)) := by
  unfold semanticSubstNameMark
  generalize semanticNormalizeName name = norm
  cases norm with
  | bvar m =>
      by_cases hm : m = k
      · subst hm
        left
        simp
      · right
        left
        exact ⟨m, hm, rfl, by simp [hm]⟩
  | _ =>
      right
      right
      exact ⟨fun _ => by simp, rfl⟩

variable {q : Pattern} {q₀ : Term sig [] Srt.pr}

/-- The name under which the executor substitutes a payload. -/
abbrev payloadName (q : Pattern) : Pattern :=
  .apply "NQuote" [semanticNormalizeProc q]

/-- The executor's payload name translates to the name of the payload. -/
theorem tName_payloadName (hq : tProc (Env.empty []) q = some q₀)
    {Γ : Ctx sig} (ρ : Env Γ) :
    tName ρ (payloadName q) = some (nameOf (lift0 q₀)) := by
  by_cases hdrop : ∃ m, q = .apply "PDrop" [m]
  · obtain ⟨m, rfl⟩ := hdrop
    rw [payloadName, semanticNormalizeProc.eq_5, tName.eq_3,
      translate_semanticNormalize.1 m ρ]
    rw [tProc.eq_2] at hq
    cases hm : nameHead m with
    | some k =>
        simp [hm, Env.empty] at hq
    | none =>
        simp only [hm] at hq
        obtain ⟨m₀, hm₀, rfl⟩ := Option.map_eq_some_iff.mp hq
        rw [tName_closed hm₀ ρ]
        rfl
  · have hnot : ∀ m, q = .apply "PDrop" [m] → False := fun m h => hdrop ⟨m, h⟩
    rw [payloadName, tName.eq_4 _ _ (semanticNormalizeProc_not_drop hnot),
      translate_semanticNormalize.2.1 q (Env.empty []), hq, Option.map_some]

/-- A name that is not a bound index after normalization denotes none. -/
theorem nameHead_eq_none_of_normal {name : Pattern}
    (h : ∀ m, semanticNormalizeName name ≠ .bvar m) : nameHead name = none := by
  rw [← nameHead_semanticNormalizeName]
  exact nameHead.eq_3 _ (fun m e => h m e) (semanticNormalizeName_not_quoteDrop name)

section Environments

variable {Γ : Ctx sig} (k : Nat) (ρ ρ' : Env Γ)

/-- Executor name substitution is environment extension. -/
theorem tName_semanticSubstName (hq : tProc (Env.empty []) q = some q₀) (n : Pattern)
    (hk : ρ' k = some (lift0 q₀)) (hother : ∀ j, j ≠ k → ρ' j = ρ j) :
    tName ρ (semanticSubstName k (payloadName q) n) = tName ρ' n := by
  unfold semanticSubstName
  rcases semanticSubstNameMark_spec k (payloadName q) n with
    ⟨hnorm, hmark⟩ | ⟨m, hm, hnorm, hmark⟩ | ⟨hnorm, hmark⟩
  · rw [hmark, tName_payloadName hq, ← translate_semanticNormalize.1 n ρ', hnorm,
      tName.eq_1, hk, Option.map_some]
  · rw [hmark, ← translate_semanticNormalize.1 n ρ', hnorm, tName.eq_1, tName.eq_1,
      hother m hm]
  · rw [hmark, translate_semanticNormalize.1 n ρ]
    exact tName_env_irrelevant n (nameHead_eq_none_of_normal hnorm) ρ ρ'

/-- Executor substitution at a drop is environment extension: a drop of
the received name runs the payload; any other drop is unchanged. -/
theorem tProc_semanticSubst_drop (hq : tProc (Env.empty []) q = some q₀) (name : Pattern)
    (hk : ρ' k = some (lift0 q₀)) (hother : ∀ j, j ≠ k → ρ' j = ρ j) :
    tProc ρ (semanticSubstProc k (payloadName q) (.apply "PDrop" [name])) =
      tProc ρ' (.apply "PDrop" [name]) := by
  rw [semanticSubstProc.eq_4]
  rcases semanticSubstNameMark_spec k (payloadName q) name with
    ⟨hnorm, hmark⟩ | ⟨m, hm, hnorm, hmark⟩ | ⟨hnorm, hmark⟩
  · rw [hmark]
    show tProc ρ (semanticNormalizeProc q) = _
    rw [translate_semanticNormalize.2.1 q ρ, tProc_closed hq ρ, tProc.eq_2,
      ← nameHead_semanticNormalizeName, hnorm]
    exact hk.symm
  · rw [hmark]
    show tProc ρ (.apply "PDrop" [.bvar m]) = _
    rw [tProc.eq_2, tProc.eq_2, ← nameHead_semanticNormalizeName name, hnorm]
    exact (hother m hm).symm
  · rw [hmark]
    have hnone := nameHead_eq_none_of_normal hnorm
    have hnormNone : nameHead (semanticNormalizeName name) = none := by
      rw [nameHead_semanticNormalizeName]
      exact hnone
    split
    rename_i name' matched hpair
    obtain ⟨rfl, rfl⟩ := hpair
    split
    · rename_i hfalse
      cases hfalse
    · rw [tProc.eq_2, tProc.eq_2, hnormNone, hnone]
      simp only
      rw [translate_semanticNormalize.1 name ρ,
        tName_env_irrelevant name hnone ρ ρ']

end Environments

/-- Beneath an input the extended environment is extended at the next
index. -/
theorem up_extended {Γ : Ctx sig} {k : Nat} {ρ ρ' : Env Γ}
    (hk : ρ' k = some (lift0 q₀)) (hother : ∀ j, j ≠ k → ρ' j = ρ j) :
    ρ'.up (k + 1) = some (lift0 q₀) ∧ ∀ j, j ≠ k + 1 → ρ'.up j = ρ.up j := by
  refine ⟨?_, ?_⟩
  · simp only [Env.up, hk, Option.map_some, weaken, rename_lift0]
  · intro j hj
    cases j with
    | zero => rfl
    | succ j =>
        simp only [Env.up]
        rw [hother j (fun e => hj (by rw [e]))]

/-- **Executor COMM is environment extension.** For a closed payload, the
executor's substitution at index `k` translates exactly as the unsubstituted
process in the environment that receives the payload at `k`. -/
theorem translate_semanticSubst (hq : tProc (Env.empty []) q = some q₀) :
    (∀ (k : Nat) (p : Pattern) {Γ : Ctx sig} (ρ ρ' : Env Γ),
      ρ' k = some (lift0 q₀) → (∀ j, j ≠ k → ρ' j = ρ j) →
      tProc ρ (semanticSubstProc k (payloadName q) p) = tProc ρ' p) ∧
    (∀ (k : Nat) (ps : List Pattern) {Γ : Ctx sig} (ρ ρ' : Env Γ),
      ρ' k = some (lift0 q₀) → (∀ j, j ≠ k → ρ' j = ρ j) →
      tProcs ρ (semanticSubstProcList k (payloadName q) ps) = tProcs ρ' ps) := by
  refine semanticSubstProc.mutual_induct (payloadName q)
    (fun k p => ∀ {Γ : Ctx sig} (ρ ρ' : Env Γ),
      ρ' k = some (lift0 q₀) → (∀ j, j ≠ k → ρ' j = ρ j) →
      tProc ρ (semanticSubstProc k (payloadName q) p) = tProc ρ' p)
    (fun k ps => ∀ {Γ : Ctx sig} (ρ ρ' : Env Γ),
      ρ' k = some (lift0 q₀) → (∀ j, j ≠ k → ρ' j = ρ j) →
      tProcs ρ (semanticSubstProcList k (payloadName q) ps) = tProcs ρ' ps)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro k n hn Γ ρ ρ' _ _
    rw [semanticSubstProc.eq_1, if_pos hn]
    rw [tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
      tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp)]
  · intro k n hn Γ ρ ρ' _ _
    rw [semanticSubstProc.eq_1, if_neg hn]
    rw [tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
      tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp)]
  · intro k x Γ ρ ρ' _ _
    rw [semanticSubstProc.eq_2]
    rw [tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
      tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp)]
  · intro k p Γ ρ ρ' _ _
    rw [semanticSubstProc.eq_3]
    rw [tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
      tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp)]
  · intro k name _ _ Γ ρ ρ' hk hother
    exact tProc_semanticSubst_drop k ρ ρ' hq name hk hother
  · intro k name _ _ _ _ Γ ρ ρ' hk hother
    exact tProc_semanticSubst_drop k ρ ρ' hq name hk hother
  · intro k n payload ih Γ ρ ρ' hk hother
    rw [semanticSubstProc.eq_5, tProc.eq_3, tProc.eq_3,
      tName_semanticSubstName k ρ ρ' hq n hk hother, ih ρ ρ' hk hother]
  · intro k n body ih Γ ρ ρ' hk hother
    obtain ⟨hk', hother'⟩ := up_extended hk hother
    rw [semanticSubstProc.eq_6, tProc.eq_4, tProc.eq_4,
      tName_semanticSubstName k ρ ρ' hq n hk hother, ih ρ.up ρ'.up hk' hother']
  · intro k nm body _ Γ ρ ρ' _ _
    rw [semanticSubstProc.eq_7]
    rw [tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
      tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp)]
  · intro k n nms body _ Γ ρ ρ' _ _
    rw [semanticSubstProc.eq_8]
    rw [tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
      tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp)]
  · intro k body repl _ _ Γ ρ ρ' _ _
    rw [semanticSubstProc.eq_9]
    rw [tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
      tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp)]
  · intro k ct elems rest ih Γ ρ ρ' hk hother
    rw [semanticSubstProc.eq_10]
    by_cases hbag : ct = .hashBag ∧ rest = none
    · obtain ⟨rfl, rfl⟩ := hbag
      rw [tProc.eq_5, tProc.eq_5, ih ρ ρ' hk hother]
    · have hne : ∀ elements others : List Pattern,
          Pattern.collection ct others rest = .collection .hashBag elements none → False := by
        intro elements others h
        simp only [Pattern.collection.injEq] at h
        exact hbag ⟨h.1, h.2.2⟩
      rw [tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp)
          (fun elements => hne elements _),
        tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp)
          (fun elements => hne elements _)]
  · intro k p hbvar hfvar hquote hdrop hout hinp hlam hmulti hsubst hcoll Γ ρ ρ' _ _
    rw [semanticSubstProc.eq_11 k _ p hbvar hfvar hquote hdrop hout hinp hlam hmulti
      hsubst hcoll]
    by_cases hzero : p = .apply "PZero" []
    · subst hzero
      rw [tProc.eq_1, tProc.eq_1]
    · rw [tProc_eq_none_of_not _ _ hzero hdrop hout hinp (fun e h => hcoll _ _ _ h),
        tProc_eq_none_of_not _ _ hzero hdrop hout hinp (fun e h => hcoll _ _ _ h)]
  · intro k Γ ρ ρ' _ _
    rfl
  · intro k p ps ihp ihps Γ ρ ρ' hk hother
    rw [semanticSubstProcList.eq_2, tProcs.eq_2, tProcs.eq_2, ihp ρ ρ' hk hother,
      ihps ρ ρ' hk hother]

end Communication

/-! ## Environments are substitutions up to quote/drop cancellation

A received name is translated as the name of the received process. When the
received process is itself a drop `*m`, that name is `m`, whereas
substituting into the quotation of the process variable gives `@*m`. The
two agree by the name equation, and by no other equation. -/

section Substitution

variable {Γ Δ : Ctx sig}

/-- The name of a process is its quotation, up to the name equation. -/
theorem nameOf_equiv (t : Term sig Γ Srt.pr) : EqClosure equations (nameOf t) (quoT t) := by
  cases t with
  | var v => exact .refl _
  | op o args =>
      cases o with
      | drp =>
          cases args with
          | cons name tail =>
              match tail with
              | .nil => exact .symm (quoteDrop_equiv name)
      | _ => exact .refl _

/-- Naming commutes with substitution up to the name equation. -/
theorem nameOf_bind_equiv (σ : Sub sig Γ Δ) (t : Term sig Γ Srt.pr) :
    EqClosure equations (nameOf (bind σ t)) (bind σ (nameOf t)) := by
  cases t with
  | var v => exact nameOf_equiv (σ _ v)
  | op o args =>
      cases o with
      | drp =>
          cases args with
          | cons name tail =>
              match tail with
              | .nil => exact .refl _
      | _ => exact .refl _

/-- Closed code is fixed by substitution, and so is its name. -/
theorem bind_nameOf_lift0 (σ : Sub sig Γ Δ) (t : Term sig [] Srt.pr) :
    bind σ (nameOf (lift0 t)) = nameOf (lift0 t) := by
  have hname : nameOf (lift0 (Γ := Γ) t) = lift0 (nameOf t) :=
    (rename_nameOf (emptyRen Γ) t).symm
  have hname' : nameOf (lift0 (Γ := Δ) t) = lift0 (nameOf t) :=
    (rename_nameOf (emptyRen Δ) t).symm
  rw [hname, hname', bind_lift0]

/-- The environment beneath an input follows a substitution lifted past the
received process. -/
theorem up_bind (σ : Sub sig Γ Δ) {ρ : Env Γ} {ρ' : Env Δ}
    (hρ : ∀ j t, ρ j = some t → ρ' j = some (bind σ t)) :
    ∀ j t, ρ.up j = some t → ρ'.up j = some (bind (liftSub σ [Srt.pr]) t) := by
  intro j t h
  cases j with
  | zero =>
      cases h
      rfl
  | succ j =>
      simp only [Env.up, Option.map_eq_some_iff] at h ⊢
      obtain ⟨u, hu, rfl⟩ := h
      refine ⟨bind σ u, hρ j u hu, ?_⟩
      simp only [weaken, bind_rename, rename_bind]
      rfl

/-- **Environments are substitutions.** Translating in an environment whose
entries are substituted gives the substituted translation, up to the name
equation. -/
theorem translate_bind :
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (n : Pattern) {Δ : Ctx sig} (σ : Sub sig Γ Δ)
        (ρ' : Env Δ), (∀ j t, ρ j = some t → ρ' j = some (bind σ t)) →
      ∀ t, tName ρ n = some t →
        ∃ t', tName ρ' n = some t' ∧ EqClosure equations t' (bind σ t)) ∧
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (p : Pattern) {Δ : Ctx sig} (σ : Sub sig Γ Δ)
        (ρ' : Env Δ), (∀ j t, ρ j = some t → ρ' j = some (bind σ t)) →
      ∀ t, tProc ρ p = some t →
        ∃ t', tProc ρ' p = some t' ∧ EqClosure equations t' (bind σ t)) ∧
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (ps : List Pattern) {Δ : Ctx sig} (σ : Sub sig Γ Δ)
        (ρ' : Env Δ), (∀ j t, ρ j = some t → ρ' j = some (bind σ t)) →
      ∀ t, tProcs ρ ps = some t →
        ∃ t', tProcs ρ' ps = some t' ∧ EqClosure equations t' (bind σ t)) := by
  refine tName.mutual_induct
    (fun {Γ} ρ n => ∀ {Δ : Ctx sig} (σ : Sub sig Γ Δ) (ρ' : Env Δ),
      (∀ j t, ρ j = some t → ρ' j = some (bind σ t)) →
      ∀ t, tName ρ n = some t →
        ∃ t', tName ρ' n = some t' ∧ EqClosure equations t' (bind σ t))
    (fun {Γ} ρ p => ∀ {Δ : Ctx sig} (σ : Sub sig Γ Δ) (ρ' : Env Δ),
      (∀ j t, ρ j = some t → ρ' j = some (bind σ t)) →
      ∀ t, tProc ρ p = some t →
        ∃ t', tProc ρ' p = some t' ∧ EqClosure equations t' (bind σ t))
    (fun {Γ} ρ ps => ∀ {Δ : Ctx sig} (σ : Sub sig Γ Δ) (ρ' : Env Δ),
      (∀ j t, ρ j = some t → ρ' j = some (bind σ t)) →
      ∀ t, tProcs ρ ps = some t →
        ∃ t', tProcs ρ' ps = some t' ∧ EqClosure equations t' (bind σ t))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro Γ ρ k Δ σ ρ' hρ t h
    rw [tName.eq_1] at h
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h
    refine ⟨nameOf (bind σ u), ?_, nameOf_bind_equiv σ u⟩
    rw [tName.eq_1, hρ k u hu, Option.map_some]
  · intro Γ ρ label Δ σ ρ' hρ t h
    rw [tName.eq_2] at h
    cases h
    exact ⟨freeT label, tName.eq_2 ρ' label, .refl _⟩
  · intro Γ ρ name ih Δ σ ρ' hρ t h
    rw [tName.eq_3] at h ⊢
    exact ih σ ρ' hρ t h
  · intro Γ ρ code hcode _ Δ σ ρ' hρ t h
    rw [tName.eq_4 _ _ hcode] at h ⊢
    obtain ⟨literal, hliteral, rfl⟩ := Option.map_eq_some_iff.mp h
    refine ⟨nameOf (lift0 literal), by rw [hliteral, Option.map_some], ?_⟩
    rw [bind_nameOf_lift0]
    exact .refl _
  · intro x Γ ρ hbvar hfvar hquoteDrop hquote Δ σ ρ' hρ t h
    rw [tName.eq_5 _ _ hbvar hfvar hquoteDrop hquote] at h
    cases h
  · intro Γ ρ Δ σ ρ' hρ t h
    rw [tProc.eq_1] at h
    cases h
    exact ⟨nilT, tProc.eq_1 ρ', .refl _⟩
  · intro Γ ρ name k hk Δ σ ρ' hρ t h
    simp only [tProc.eq_2, hk] at h ⊢
    exact ⟨bind σ t, hρ k t h, .refl _⟩
  · intro Γ ρ name hk ih Δ σ ρ' hρ t h
    simp only [tProc.eq_2, hk] at h ⊢
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨m', hm', equiv⟩ := ih σ ρ' hρ m hm
    exact ⟨drpT m', by rw [hm', Option.map_some], equiv_drpT equiv⟩
  · intro Γ ρ name payload ihn ihp Δ σ ρ' hρ t h
    rw [tProc.eq_3] at h ⊢
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨c, hc, process, hprocess, rfl⟩ := h
    obtain ⟨c', hc', equivc⟩ := ihn σ ρ' hρ c hc
    obtain ⟨process', hprocess', equivp⟩ := ihp σ ρ' hρ process hprocess
    exact ⟨outT c' process', by rw [hc', Option.bind_some, hprocess', Option.map_some],
      equiv_outT equivc equivp⟩
  · intro Γ ρ name body ihn ihb Δ σ ρ' hρ t h
    rw [tProc.eq_4] at h ⊢
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨c, hc, continuation, hcontinuation, rfl⟩ := h
    obtain ⟨c', hc', equivc⟩ := ihn σ ρ' hρ c hc
    obtain ⟨continuation', hcontinuation', equivK⟩ :=
      ihb (liftSub σ [Srt.pr]) ρ'.up (up_bind σ hρ) continuation hcontinuation
    exact ⟨inpT c' continuation',
      by rw [hc', Option.bind_some, hcontinuation', Option.map_some],
      equiv_inpT equivc equivK⟩
  · intro Γ ρ elements ih Δ σ ρ' hρ t h
    rw [tProc.eq_5] at h ⊢
    exact ih σ ρ' hρ t h
  · intro x Γ ρ hzero hdrop hout hinp hbag Δ σ ρ' hρ t h
    rw [tProc.eq_6 _ _ hzero hdrop hout hinp hbag] at h
    cases h
  · intro Γ ρ Δ σ ρ' hρ t h
    rw [tProcs.eq_1] at h
    cases h
    exact ⟨nilT, tProcs.eq_1 ρ', .refl _⟩
  · intro Γ ρ process rest ihp ihr Δ σ ρ' hρ t h
    rw [tProcs.eq_2] at h ⊢
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨head, hhead, tail, htail, rfl⟩ := h
    obtain ⟨head', hhead', equivh⟩ := ihp σ ρ' hρ head hhead
    obtain ⟨tail', htail', equivt⟩ := ihr σ ρ' hρ tail htail
    exact ⟨parT head' tail', by rw [hhead', Option.bind_some, htail', Option.map_some],
      equiv_parT equivh equivt⟩

end Substitution

/-! ## The communication law -/

section CommunicationLaw

open Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-- A closed payload received at the only bound index. -/
def Env.received (q₀ : Term sig [] Srt.pr) : Env []
  | 0 => some q₀
  | _ + 1 => none

/-- **Communication law.** Translating the executor's COMM result is
instantiating the translated continuation at the translated payload, up to
quote/drop cancellation. -/
theorem translate_semanticCommSubst {body q : Pattern}
    {K : Term sig [Srt.pr] Srt.pr} {q₀ : Term sig [] Srt.pr}
    (hbody : tProc (Env.empty []).up body = some K)
    (hq : tProc (Env.empty []) q = some q₀) :
    ∃ t, tProc (Env.empty []) (semanticCommSubst body q) = some t ∧
      EqClosure equations t (inst K q₀) := by
  have hsubst : tProc (Env.empty []) (semanticCommSubst body q) =
      tProc (Env.received q₀) body := by
    refine (translate_semanticSubst hq).1 0 body (Env.empty []) (Env.received q₀) ?_ ?_
    · rw [lift0_nil]
      rfl
    · intro j hj
      cases j with
      | zero => exact (hj rfl).elim
      | succ j => rfl
  rw [hsubst]
  refine (translate_bind.2.1 (Env.empty []).up body (extend q₀) (Env.received q₀) ?_ K hbody)
  intro j t h
  cases j with
  | zero =>
      cases h
      rfl
  | succ j => cases h

end CommunicationLaw

/-! ## Parallel bags

A bag is translated as a right-nested parallel composition ending in the null
process. Up to the monoid equations this is independent of how the bag is
listed, and a bag element that is itself a bag may be spliced into it. -/

section Bags

variable {Γ : Ctx sig} (ρ : Env Γ)

theorem tProcs_mem {xs : List Pattern} {a : Term sig Γ Srt.pr}
    (h : tProcs ρ xs = some a) {x : Pattern} (hx : x ∈ xs) :
    ∃ t, tProc ρ x = some t := by
  induction xs generalizing a with
  | nil => cases hx
  | cons y ys ih =>
      rw [tProcs.eq_2] at h
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨head, hhead, tail, htail, rfl⟩ := h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨head, hhead⟩
      · exact ih htail hx

theorem tProcs_append {xs ys : List Pattern} {c : Term sig Γ Srt.pr}
    (h : tProcs ρ (xs ++ ys) = some c) :
    ∃ a b, tProcs ρ xs = some a ∧ tProcs ρ ys = some b ∧
      EqClosure equations c (parT a b) := by
  induction xs generalizing c with
  | nil => exact ⟨nilT, c, rfl, h, (nil_parT c).symm⟩
  | cons x xs ih =>
      rw [List.cons_append, tProcs.eq_2] at h
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨head, hhead, tail, htail, rfl⟩ := h
      obtain ⟨a, b, ha, hb, equiv⟩ := ih htail
      refine ⟨parT head a, b, ?_, hb, ?_⟩
      · rw [tProcs.eq_2, hhead, Option.bind_some, ha, Option.map_some]
      · exact (equiv_parT (.refl head) equiv).trans (parT_assoc head a b).symm

theorem tProcs_append_of {xs ys : List Pattern} {a b : Term sig Γ Srt.pr}
    (ha : tProcs ρ xs = some a) (hb : tProcs ρ ys = some b) :
    ∃ c, tProcs ρ (xs ++ ys) = some c ∧ EqClosure equations c (parT a b) := by
  induction xs generalizing a with
  | nil =>
      cases ha
      exact ⟨b, hb, (nil_parT b).symm⟩
  | cons x xs ih =>
      rw [tProcs.eq_2] at ha
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at ha
      obtain ⟨head, hhead, tail, htail, rfl⟩ := ha
      obtain ⟨c, hc, equiv⟩ := ih htail
      refine ⟨parT head c, ?_, ?_⟩
      · rw [List.cons_append, tProcs.eq_2, hhead, Option.bind_some, hc, Option.map_some]
      · exact (equiv_parT (.refl head) equiv).trans (parT_assoc head tail b).symm

/-- Listing order does not matter up to the monoid equations. -/
theorem tProcs_perm {xs ys : List Pattern} (perm : xs.Perm ys) {a : Term sig Γ Srt.pr}
    (h : tProcs ρ xs = some a) :
    ∃ b, tProcs ρ ys = some b ∧ EqClosure equations a b := by
  induction perm generalizing a with
  | nil => exact ⟨a, h, .refl a⟩
  | cons x _ ih =>
      rw [tProcs.eq_2] at h
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨head, hhead, tail, htail, rfl⟩ := h
      obtain ⟨b, hb, equiv⟩ := ih htail
      exact ⟨parT head b, by rw [tProcs.eq_2, hhead, Option.bind_some, hb, Option.map_some],
        equiv_parT (.refl head) equiv⟩
  | swap x y l =>
      rw [tProcs.eq_2] at h
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨hy, hhy, tail, htail, rfl⟩ := h
      rw [tProcs.eq_2] at htail
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at htail
      obtain ⟨hx, hhx, rest, hrest, rfl⟩ := htail
      refine ⟨parT hx (parT hy rest), ?_, parT_swap hy hx rest⟩
      rw [tProcs.eq_2, hhx, Option.bind_some, tProcs.eq_2, hhy, Option.bind_some, hrest,
        Option.map_some, Option.map_some]
  | trans _ _ ih₁ ih₂ =>
      obtain ⟨b, hb, e₁⟩ := ih₁ h
      obtain ⟨c, hc, e₂⟩ := ih₂ hb
      exact ⟨c, hc, e₁.trans e₂⟩

/-- A selected element can be brought to the front. -/
theorem tProcs_select {xs : List Pattern} {a : Term sig Γ Srt.pr}
    (h : tProcs ρ xs = some a) (i : Nat) (hi : i < xs.length) :
    ∃ x rest, tProc ρ xs[i] = some x ∧ tProcs ρ (xs.eraseIdx i) = some rest ∧
      EqClosure equations a (parT x rest) := by
  obtain ⟨b, hb, equiv⟩ := tProcs_perm ρ (List.getElem_cons_eraseIdx_perm hi).symm h
  rw [tProcs.eq_2] at hb
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hb
  obtain ⟨x, hx, rest, hrest, rfl⟩ := hb
  exact ⟨x, rest, hx, hrest, equiv⟩

end Bags

end Mettapedia.OSLF.Binding.RhoPayloadPresentation
