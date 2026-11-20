import Mettapedia.OSLF.Syntax.RhoPayloadPresentation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SemanticSubstitution
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalMatch

/-!
# Authored rho processes in the payload presentation

An authored process uses bound names. The translation reads each bound name
as the quotation of the process received there, and each drop of a bound
name as that process. A whole name is read under rho's declared equations
before scope is consulted, exactly as the executor's whole-name test reads
it: the quote of a drop is the dropped name, and a parallel unit beside a
drop is ignored. So `@*y` and `@(*y|0)` both denote the bound name `y`. The
translation is sorted: a name is a variable or the quotation of a process,
so a pattern whose whole name is a bound index translates only when it is
such a name. Any other quotation is literal code: it is translated with no
bound names in scope, so an outer binder never reaches inside it.

The translation is parameterised by an environment giving the process
received at each bound index. Under an input the environment is extended by
the new variable.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoPayloadPresentation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern CollType rhoReflectivePresentation)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (BinderHead)

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

/-- The bound index a whole name denotes. The name is read by the binder
observation of rho's reflective presentation, which decides the executor's
whole-name test without sorting a parallel bag. -/
def nameHead (n : Pattern) : Option Nat :=
  match BinderHead.ofPattern rhoReflectivePresentation n with
  | .index k => some k
  | _ => none

mutual

/-- Translate a name: a bound name is the name of its received process, the
quote of a drop is resolved as a whole name, a quotation of a process whose
whole name is a bound index is that bound name, and any other quotation is
literal code with no bound names in scope. -/
def tName {Γ : Ctx sig} (ρ : Env Γ) : Pattern → Option (Term sig Γ Srt.nm)
  | .bvar k => (ρ k).map nameOf
  | .fvar label => some (freeT label)
  | .apply "NQuote" [.apply "PDrop" [name]] => tName ρ name
  | .apply "NQuote" [code] =>
      match nameHead (.apply "NQuote" [code]) with
      | some k => (tProc ρ code).bind fun _ => (ρ k).map nameOf
      | none => (tProc (Env.empty []) code).map fun literal => nameOf (lift0 literal)
  | _ => none

/-- Translate a process of the reflective core. A drop of a bound name is
the received process itself; any other drop is inert. -/
def tProc {Γ : Ctx sig} (ρ : Env Γ) : Pattern → Option (Term sig Γ Srt.pr)
  | .apply "PZero" [] => some nilT
  | .apply "PDrop" [name] =>
      match nameHead name with
      | some k => (tName ρ name).bind fun _ => ρ k
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

/-! ## Reading a whole name

The binder observation is the decidable reading of the executor's
whole-name test: a pattern's canonical form is a bound index exactly when
its observation is that index. -/

section Heads

open Mettapedia.Languages.ProcessCalculi.RhoCalculus

theorem nameHead_eq_some_iff_ofPattern {n : Pattern} {k : Nat} :
    nameHead n = some k ↔ BinderHead.ofPattern rhoReflectivePresentation n = .index k := by
  unfold nameHead
  cases BinderHead.ofPattern rhoReflectivePresentation n <;> simp

/-- **The executor's whole-name test is the translation's reading.** A
pattern's canonical form is the bound index `k` exactly when, as a name, it
denotes `k`. -/
theorem canonicalize_eq_bvar_iff_nameHead (n : Pattern) (k : Nat) :
    Canonical.canonicalize n = .bvar k ↔ nameHead n = some k := by
  rw [nameHead_eq_some_iff_ofPattern,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.BinderHead.ofPattern_index_iff,
    CanonicalMatch.derivedCanonicalize_eq]

theorem nameHead_bvar (k : Nat) : nameHead (.bvar k) = some k := rfl

theorem nameHead_fvar (label : String) : nameHead (.fvar label) = none := rfl

/-- The quote of a drop is observed as the dropped name. -/
theorem ofPattern_quoteDrop (name : Pattern) :
    BinderHead.ofPattern rhoReflectivePresentation (.apply "NQuote" [.apply "PDrop" [name]]) =
      BinderHead.ofPattern rhoReflectivePresentation name := by
  simp only [BinderHead.ofPattern, BinderHead.ofList]
  cases BinderHead.ofPattern rhoReflectivePresentation name <;> rfl

theorem nameHead_quoteDrop (name : Pattern) :
    nameHead (.apply "NQuote" [.apply "PDrop" [name]]) = nameHead name := by
  unfold nameHead
  rw [ofPattern_quoteDrop]

/-- A name with a bound head avoids every other index. -/
theorem nameHead_noBVar {name : Pattern} {j : Nat} (head : nameHead name = some j) (k : Nat) :
    noBVar k name = (j != k) := by
  rw [(Canonical.canonicalize_sound name).noBVar_eq k,
    (canonicalize_eq_bvar_iff_nameHead name j).mpr head]
  rfl

theorem isWellScopedListAt_iff (depth : Nat) (patterns : List Pattern) :
    Pattern.isWellScopedListAt depth patterns = true ↔
      ∀ pattern ∈ patterns, pattern.isWellScopedAt depth = true := by
  induction patterns with
  | nil => simp [Pattern.isWellScopedListAt]
  | cons pattern rest ih => simp [Pattern.isWellScopedListAt, ih]

theorem noBVarList_iff (k : Nat) (patterns : List Pattern) :
    noBVarList k patterns = true ↔ ∀ pattern ∈ patterns, noBVar k pattern = true := by
  induction patterns with
  | nil => simp [noBVarList]
  | cons pattern rest ih => simp [noBVarList, ih]

/-- A pattern is in scope at a depth exactly when no index from that depth on
occurs free in it. -/
theorem isWellScopedAt_iff_noBVar (pattern : Pattern) :
    ∀ depth, pattern.isWellScopedAt depth = true ↔ ∀ k, depth ≤ k → noBVar k pattern = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro depth
      simp only [Pattern.isWellScopedAt, decide_eq_true_eq, noBVar, bne_iff_ne, ne_eq]
      constructor
      · intro below k above same
        omega
      · intro absent
        by_contra outside
        exact absent index (by omega) rfl
  | hfvar name =>
      intro depth
      simp [Pattern.isWellScopedAt, noBVar]
  | happly constructor arguments ih =>
      intro depth
      simp only [Pattern.isWellScopedAt, noBVar, isWellScopedListAt_iff, noBVarList_iff]
      constructor
      · intro inScope k above argument member
        exact (ih argument member depth).mp (inScope argument member) k above
      · intro absent argument member
        exact (ih argument member depth).mpr fun k above => absent k above argument member
  | hlambda name body ih =>
      intro depth
      simp only [Pattern.isWellScopedAt, noBVar]
      rw [ih (depth + 1)]
      constructor
      · intro absent k above
        exact absent (k + 1) (by omega)
      · intro absent k above
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        exact absent j (by omega)
  | hmultiLambda arity names body ih =>
      intro depth
      simp only [Pattern.isWellScopedAt, noBVar]
      rw [ih (depth + arity)]
      constructor
      · intro absent k above
        exact absent (k + arity) (by omega)
      · intro absent k above
        obtain ⟨j, rfl⟩ : ∃ j, k = j + arity := ⟨k - arity, by omega⟩
        exact absent j (by omega)
  | hsubst body replacement ihBody ihReplacement =>
      intro depth
      simp only [Pattern.isWellScopedAt, noBVar, Bool.and_eq_true]
      rw [ihBody (depth + 1), ihReplacement depth]
      constructor
      · rintro ⟨absentBody, absentReplacement⟩ k above
        exact ⟨absentBody (k + 1) (by omega), absentReplacement k above⟩
      · intro absent
        refine ⟨fun k above => ?_, fun k above => (absent k above).2⟩
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        exact (absent j (by omega)).1
  | hcollection kind elements rest ih =>
      intro depth
      simp only [Pattern.isWellScopedAt, noBVar, isWellScopedListAt_iff, noBVarList_iff]
      constructor
      · intro inScope k above element member
        exact (ih element member depth).mp (inScope element member) k above
      · intro absent element member
        exact (ih element member depth).mpr fun k above => absent k above element member

/-- A name that denotes a bound index is in scope exactly when that index is. -/
theorem nameHead_wellScoped {name : Pattern} {index : Nat}
    (head : nameHead name = some index) (depth : Nat) :
    name.isWellScopedAt depth = decide (index < depth) := by
  rw [Bool.eq_iff_iff, isWellScopedAt_iff_noBVar, decide_eq_true_iff]
  constructor
  · intro absent
    by_contra outside
    have present := absent index (by omega)
    rw [nameHead_noBVar head] at present
    simp at present
  · intro below k above
    rw [nameHead_noBVar head]
    simp only [bne_iff_ne, ne_eq]
    omega

end Heads

/-! ## The equations of the translation -/

section Equations

variable {Γ : Ctx sig}

theorem tName_bvar (ρ : Env Γ) (k : Nat) : tName ρ (.bvar k) = (ρ k).map nameOf :=
  rfl

theorem tName_fvar (ρ : Env Γ) (label : String) :
    tName ρ (.fvar label) = some (freeT label) :=
  rfl

/-- The quote of a drop translates as the dropped name. -/
theorem tName_quoteDrop (ρ : Env Γ) (name : Pattern) :
    tName ρ (.apply "NQuote" [.apply "PDrop" [name]]) = tName ρ name :=
  tName.eq_3 ρ name

/-- A quotation of a process whose whole name is a bound index is that bound
name. -/
theorem tName_quote_of_nameHead (ρ : Env Γ) {code : Pattern} {k : Nat}
    (hcode : ∀ name, code = .apply "PDrop" [name] → False)
    (head : nameHead (.apply "NQuote" [code]) = some k) :
    tName ρ (.apply "NQuote" [code]) = (tProc ρ code).bind fun _ => (ρ k).map nameOf := by
  rw [tName.eq_4 ρ code hcode, head]

/-- Any other quotation, apart from the quote of a drop, is literal code. -/
theorem tName_quote (ρ : Env Γ) {code : Pattern}
    (hcode : ∀ name, code = .apply "PDrop" [name] → False)
    (head : nameHead (.apply "NQuote" [code]) = none) :
    tName ρ (.apply "NQuote" [code]) =
      (tProc (Env.empty []) code).map fun literal => nameOf (lift0 literal) := by
  rw [tName.eq_4 ρ code hcode, head]

/-- Nothing else is a name. -/
theorem tName_eq_none (ρ : Env Γ) {x : Pattern}
    (hbvar : ∀ k, x = .bvar k → False)
    (hfvar : ∀ label, x = .fvar label → False)
    (hquote : ∀ code, x = .apply "NQuote" [code] → False) :
    tName ρ x = none :=
  tName.eq_5 ρ x hbvar hfvar (fun _ e => hquote _ e) hquote

/-- A drop of a name whose whole name is a bound index runs the process
received there. -/
theorem tProc_drop_of_nameHead (ρ : Env Γ) {name : Pattern} {k : Nat}
    (head : nameHead name = some k) :
    tProc ρ (.apply "PDrop" [name]) = (tName ρ name).bind fun _ => ρ k := by
  rw [tProc.eq_2, head]

/-- Any other drop is inert. -/
theorem tProc_drop_of_nameHead_none (ρ : Env Γ) {name : Pattern}
    (head : nameHead name = none) :
    tProc ρ (.apply "PDrop" [name]) = (tName ρ name).map drpT := by
  rw [tProc.eq_2, head]

end Equations

/-- A translated name whose whole name is a bound index is the name of the
process received there. -/
theorem tName_of_nameHead {Γ : Ctx sig} {name : Pattern} {j : Nat}
    (head : nameHead name = some j) {ρ : Env Γ} {t : Term sig Γ Srt.nm}
    (translated : tName ρ name = some t) : (ρ j).map nameOf = some t := by
  refine (tName.mutual_induct
    (fun {Γ} ρ n => ∀ j t, nameHead n = some j → tName ρ n = some t →
      (ρ j).map nameOf = some t)
    (fun _ _ => True) (fun _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).1 ρ name j t head translated
  · intro Γ ρ k j t head h
    rw [nameHead_bvar] at head
    cases head
    exact h
  · intro Γ ρ label j t head _
    rw [nameHead_fvar] at head
    cases head
  · intro Γ ρ name ih j t head h
    rw [nameHead_quoteDrop] at head
    rw [tName_quoteDrop] at h
    exact ih j t head h
  · intro Γ ρ code hcode k hk _ j t head h
    rw [hk] at head
    cases head
    rw [tName_quote_of_nameHead ρ hcode hk] at h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    exact h
  · intro Γ ρ code _ hk _ j t head _
    rw [hk] at head
    cases head
  · intro x Γ ρ hbvar hfvar _ hquote j t _ h
    rw [tName_eq_none ρ hbvar hfvar hquote] at h
    cases h
  all_goals intros; trivial

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
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro Γ ρ k Δ r ρ' hρ t h
    rw [tName_bvar] at h ⊢
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [hρ k u hu, Option.map_some, rename_nameOf]
  · intro Γ ρ label Δ r ρ' hρ t h
    rw [tName_fvar] at h ⊢
    cases h
    rfl
  · intro Γ ρ name ih Δ r ρ' hρ t h
    rw [tName_quoteDrop] at h ⊢
    exact ih r ρ' hρ t h
  · intro Γ ρ code hcode k head ih Δ r ρ' hρ t h
    rw [tName_quote_of_nameHead _ hcode head] at h ⊢
    obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [ih r ρ' hρ c hc, Option.bind_some, hρ k u hu, Option.map_some, rename_nameOf]
  · intro Γ ρ code hcode head _ Δ r ρ' hρ t h
    rw [tName_quote _ hcode head] at h
    rw [tName_quote _ hcode head]
    obtain ⟨literal, hliteral, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [hliteral, Option.map_some, rename_nameOf, rename_lift0]
  · intro x Γ ρ hbvar hfvar _ hquote Δ r ρ' hρ t h
    rw [tName_eq_none _ hbvar hfvar hquote] at h
    cases h
  · intro Γ ρ Δ r ρ' hρ t h
    rw [tProc.eq_1] at h ⊢
    cases h
    rfl
  · intro Γ ρ name k hk ih Δ r ρ' hρ t h
    rw [tProc_drop_of_nameHead _ hk] at h ⊢
    obtain ⟨m, hm, h⟩ := Option.bind_eq_some_iff.mp h
    rw [ih r ρ' hρ m hm, Option.bind_some]
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
  refine (tName.mutual_induct
    (fun {Γ} ρ n => nameHead n = none → ∀ ρ' : Env Γ, tName ρ n = tName ρ' n)
    (fun _ _ => True) (fun _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).1 ρ n h ρ'
  · intro Γ ρ k none _
    rw [nameHead_bvar] at none
    cases none
  · intro Γ ρ label _ ρ'
    rw [tName_fvar, tName_fvar]
  · intro Γ ρ name ih none ρ'
    rw [nameHead_quoteDrop] at none
    rw [tName_quoteDrop, tName_quoteDrop, ih none ρ']
  · intro Γ ρ code _ k head _ none _
    rw [head] at none
    cases none
  · intro Γ ρ code hcode head _ _ ρ'
    rw [tName_quote _ hcode head, tName_quote _ hcode head]
  · intro x Γ ρ hbvar hfvar _ hquote _ ρ'
    rw [tName_eq_none _ hbvar hfvar hquote, tName_eq_none _ hbvar hfvar hquote]
  all_goals intros; trivial

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

/-- Normalization is invisible to the binder observation. -/
theorem ofPattern_semanticNormalize :
    (∀ n : Pattern, BinderHead.ofPattern rhoReflectivePresentation (semanticNormalizeName n) =
      BinderHead.ofPattern rhoReflectivePresentation n) ∧
    (∀ p : Pattern, BinderHead.ofPattern rhoReflectivePresentation (semanticNormalizeProc p) =
      BinderHead.ofPattern rhoReflectivePresentation p) ∧
    (∀ ps : List Pattern,
      BinderHead.ofList rhoReflectivePresentation (semanticNormalizeProcList ps) =
        BinderHead.ofList rhoReflectivePresentation ps) := by
  refine semanticNormalizeName.mutual_induct
    (fun n => BinderHead.ofPattern rhoReflectivePresentation (semanticNormalizeName n) =
      BinderHead.ofPattern rhoReflectivePresentation n)
    (fun p => BinderHead.ofPattern rhoReflectivePresentation (semanticNormalizeProc p) =
      BinderHead.ofPattern rhoReflectivePresentation p)
    (fun ps => BinderHead.ofList rhoReflectivePresentation (semanticNormalizeProcList ps) =
      BinderHead.ofList rhoReflectivePresentation ps)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro k
    rfl
  · intro x
    rfl
  · intro n ih
    rw [semanticNormalizeName.eq_3, ofPattern_quoteDrop, ih]
  · intro p hp ih
    rw [semanticNormalizeName.eq_4 p hp]
    simp only [BinderHead.ofPattern, BinderHead.ofList, ih]
  · intro n hbvar hfvar hquoteDrop hquote
    rw [semanticNormalizeName.eq_5 n hbvar hfvar hquoteDrop hquote]
  · intro k
    rfl
  · intro x
    rfl
  · intro n q ihn ihq
    simp only [semanticNormalizeProc.eq_3, BinderHead.ofPattern, BinderHead.ofList, ihn, ihq]
  · intro n body ihn _
    simp only [semanticNormalizeProc.eq_4, BinderHead.ofPattern, BinderHead.ofList, ihn]
  · intro n ihn
    simp only [semanticNormalizeProc.eq_5, BinderHead.ofPattern, BinderHead.ofList, ihn]
  · intro p ihp
    simp only [semanticNormalizeProc.eq_6, BinderHead.ofPattern, BinderHead.ofList, ihp]
  · intro nm body _
    rw [semanticNormalizeProc.eq_7]
    rfl
  · intro n nms body _
    rw [semanticNormalizeProc.eq_8]
    rfl
  · intro body repl _ _
    rw [semanticNormalizeProc.eq_9]
    rfl
  · intro ct elems rest ih
    rw [semanticNormalizeProc.eq_10]
    cases rest with
    | none => simp only [BinderHead.ofPattern, ih]
    | some rest => rfl
  · intro p hbvar hfvar hout hinp hdrop hquote hlam hmulti hsubst hcoll
    rw [semanticNormalizeProc.eq_11 p hbvar hfvar hout hinp hdrop hquote hlam hmulti
      hsubst hcoll]
  · rfl
  · intro p ps ihp ihps
    simp only [semanticNormalizeProcList, BinderHead.ofList, ihp, ihps]

/-- Normalization preserves the bound index a name denotes. -/
theorem nameHead_semanticNormalizeName (n : Pattern) :
    nameHead (semanticNormalizeName n) = nameHead n := by
  unfold nameHead
  rw [ofPattern_semanticNormalize.1 n]

/-- The normalized test is one half of the executor's whole-name test: a
name that normalizes to a bound index is that index. The converse fails:
`@(*x|0)` is normal, and its canonical form is `x` (see the controls). -/
theorem canonicalize_eq_bvar_of_semanticNormalizeName {n : Pattern} {k : Nat}
    (normal : semanticNormalizeName n = .bvar k) : Canonical.canonicalize n = .bvar k := by
  rw [canonicalize_eq_bvar_iff_nameHead, ← nameHead_semanticNormalizeName, normal]
  rfl

/-- Normalization preserves the bound index of a quotation. -/
theorem nameHead_quote_semanticNormalizeProc (p : Pattern) :
    nameHead (.apply "NQuote" [semanticNormalizeProc p]) = nameHead (.apply "NQuote" [p]) := by
  unfold nameHead
  simp only [BinderHead.ofPattern, BinderHead.ofList, ofPattern_semanticNormalize.2.1 p]

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
    rw [semanticNormalizeName.eq_3, tName_quoteDrop, ih]
  · intro p hp ih Γ ρ
    rw [semanticNormalizeName.eq_4 p hp]
    have heads := nameHead_quote_semanticNormalizeProc p
    have hp' := semanticNormalizeProc_not_drop hp
    cases head : nameHead (.apply "NQuote" [p]) with
    | some k =>
        rw [tName_quote_of_nameHead ρ hp head, tName_quote_of_nameHead ρ hp' (heads.trans head),
          ih]
    | none =>
        rw [tName_quote ρ hp head, tName_quote ρ hp' (heads.trans head), ih]
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

/-- A translated pattern has no free occurrence of an index that its
environment leaves unbound. -/
theorem translate_noBVar :
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (n : Pattern), ∀ t, tName ρ n = some t →
      ∀ k, ρ k = none → noBVar k n = true) ∧
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (p : Pattern), ∀ t, tProc ρ p = some t →
      ∀ k, ρ k = none → noBVar k p = true) ∧
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (ps : List Pattern), ∀ t, tProcs ρ ps = some t →
      ∀ k, ρ k = none → noBVarList k ps = true) := by
  refine tName.mutual_induct
    (fun {Γ} ρ n => ∀ t, tName ρ n = some t → ∀ k, ρ k = none → noBVar k n = true)
    (fun {Γ} ρ p => ∀ t, tProc ρ p = some t → ∀ k, ρ k = none → noBVar k p = true)
    (fun {Γ} ρ ps => ∀ t, tProcs ρ ps = some t → ∀ k, ρ k = none → noBVarList k ps = true)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro Γ ρ j t h k hk
    rw [tName_bvar] at h
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h
    have distinct : j ≠ k := by
      rintro rfl
      rw [hk] at hu
      cases hu
    simpa [noBVar] using distinct
  · intro Γ ρ label t h k hk
    simp [noBVar]
  · intro Γ ρ name ih t h k hk
    rw [tName_quoteDrop] at h
    simp [noBVar, noBVarList, ih t h k hk]
  · intro Γ ρ code hcode j head ih t h k hk
    rw [tName_quote_of_nameHead _ hcode head] at h
    obtain ⟨c, hc, -⟩ := Option.bind_eq_some_iff.mp h
    simp [noBVar, noBVarList, ih c hc k hk]
  · intro Γ ρ code hcode head ih t h k hk
    rw [tName_quote _ hcode head] at h
    obtain ⟨literal, hliteral, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [noBVar, noBVarList, ih literal hliteral k rfl]
  · intro x Γ ρ hbvar hfvar _ hquote t h k hk
    rw [tName_eq_none _ hbvar hfvar hquote] at h
    cases h
  · intro Γ ρ t h k hk
    simp [noBVar, noBVarList]
  · intro Γ ρ name j hj ih t h k hk
    rw [tProc_drop_of_nameHead _ hj] at h
    obtain ⟨m, hm, -⟩ := Option.bind_eq_some_iff.mp h
    simp [noBVar, noBVarList, ih m hm k hk]
  · intro Γ ρ name hj ih t h k hk
    simp only [tProc.eq_2, hj] at h
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [noBVar, noBVarList, ih m hm k hk]
  · intro Γ ρ name payload ihn ihp t h k hk
    rw [tProc.eq_3] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨c, hc, process, hprocess, rfl⟩ := h
    simp [noBVar, noBVarList, ihn c hc k hk, ihp process hprocess k hk]
  · intro Γ ρ name body ihn ihb t h k hk
    rw [tProc.eq_4] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨c, hc, continuation, hcontinuation, rfl⟩ := h
    have unbound : ρ.up (k + 1) = none := by simp [Env.up, hk]
    simp [noBVar, noBVarList, ihn c hc k hk, ihb continuation hcontinuation (k + 1) unbound]
  · intro Γ ρ elements ih t h k hk
    rw [tProc.eq_5] at h
    simp [noBVar, ih t h k hk]
  · intro x Γ ρ hzero hdrop hout hinp hbag t h k hk
    rw [tProc.eq_6 _ _ hzero hdrop hout hinp hbag] at h
    cases h
  · intro Γ ρ t h k hk
    simp [noBVarList]
  · intro Γ ρ process rest ihp ihr t h k hk
    rw [tProcs.eq_2] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨head, hhead, tail, htail, rfl⟩ := h
    simp [noBVarList, ihp head hhead k hk, ihr tail htail k hk]

/-- The three outcomes of the executor's name substitution: the whole name
is the substituted index, another bound index, or no bound index. -/
theorem semanticSubstNameMark_spec (k : Nat) (replacement name : Pattern) :
    (nameHead name = some k ∧
      semanticSubstNameMark k replacement name = (replacement, true)) ∨
    (∃ m, m ≠ k ∧ nameHead name = some m ∧
      semanticSubstNameMark k replacement name = (semanticNormalizeName name, false)) ∨
    (nameHead name = none ∧
      semanticSubstNameMark k replacement name = (semanticNormalizeName name, false)) := by
  unfold semanticSubstNameMark
  simp only [canonicalize_eq_bvar_iff_nameHead]
  cases head : nameHead name with
  | some m =>
      by_cases hm : m = k
      · subst hm
        left
        simp
      · right
        left
        exact ⟨m, hm, rfl, by simp [hm]⟩
  | none =>
      right
      right
      simp

variable {q : Pattern} {q₀ : Term sig [] Srt.pr}

/-- The name under which the executor substitutes a payload. -/
abbrev payloadName (q : Pattern) : Pattern :=
  .apply "NQuote" [semanticNormalizeProc q]

/-- The quotation of a closed translatable payload denotes no bound index. -/
theorem nameHead_quote_of_closed (hq : tProc (Env.empty []) q = some q₀) :
    nameHead (.apply "NQuote" [q]) = none := by
  cases head : nameHead (.apply "NQuote" [q]) with
  | none => rfl
  | some k =>
      have absent := translate_noBVar.2.1 (Env.empty []) q q₀ hq k rfl
      have present := nameHead_noBVar head k
      simp [noBVar, noBVarList, absent] at present

/-- The executor's payload name translates to the name of the payload. -/
theorem tName_payloadName (hq : tProc (Env.empty []) q = some q₀)
    {Γ : Ctx sig} (ρ : Env Γ) :
    tName ρ (payloadName q) = some (nameOf (lift0 q₀)) := by
  have closed := nameHead_quote_of_closed hq
  by_cases hdrop : ∃ m, q = .apply "PDrop" [m]
  · obtain ⟨m, rfl⟩ := hdrop
    rw [nameHead_quoteDrop] at closed
    rw [payloadName, semanticNormalizeProc.eq_5, tName_quoteDrop,
      translate_semanticNormalize.1 m ρ]
    simp only [tProc.eq_2, closed] at hq
    obtain ⟨m₀, hm₀, rfl⟩ := Option.map_eq_some_iff.mp hq
    rw [tName_closed hm₀ ρ]
    rfl
  · have hnot : ∀ m, q = .apply "PDrop" [m] → False := fun m h => hdrop ⟨m, h⟩
    rw [payloadName, tName_quote _ (semanticNormalizeProc_not_drop hnot)
        ((nameHead_quote_semanticNormalizeProc q).trans closed),
      translate_semanticNormalize.2.1 q (Env.empty []), hq, Option.map_some]

/-- The translation consults its environment only at the indices that occur
free. -/
theorem translate_agree :
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (n : Pattern) (ρ' : Env Γ),
      (∀ k, noBVar k n = false → ρ' k = ρ k) → tName ρ' n = tName ρ n) ∧
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (p : Pattern) (ρ' : Env Γ),
      (∀ k, noBVar k p = false → ρ' k = ρ k) → tProc ρ' p = tProc ρ p) ∧
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (ps : List Pattern) (ρ' : Env Γ),
      (∀ k, noBVarList k ps = false → ρ' k = ρ k) → tProcs ρ' ps = tProcs ρ ps) := by
  refine tName.mutual_induct
    (fun {Γ} ρ n => ∀ ρ' : Env Γ,
      (∀ k, noBVar k n = false → ρ' k = ρ k) → tName ρ' n = tName ρ n)
    (fun {Γ} ρ p => ∀ ρ' : Env Γ,
      (∀ k, noBVar k p = false → ρ' k = ρ k) → tProc ρ' p = tProc ρ p)
    (fun {Γ} ρ ps => ∀ ρ' : Env Γ,
      (∀ k, noBVarList k ps = false → ρ' k = ρ k) → tProcs ρ' ps = tProcs ρ ps)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro Γ ρ k ρ' agree
    rw [tName_bvar, tName_bvar, agree k (by simp [noBVar])]
  · intro Γ ρ label ρ' _
    rfl
  · intro Γ ρ name ih ρ' agree
    rw [tName_quoteDrop, tName_quoteDrop]
    exact ih ρ' fun k hk => agree k (by simp [noBVar, noBVarList, hk])
  · intro Γ ρ code hcode j head ih ρ' agree
    rw [tName_quote_of_nameHead _ hcode head, tName_quote_of_nameHead _ hcode head,
      ih ρ' fun k hk => agree k (by simp [noBVar, noBVarList, hk]),
      agree j (by rw [nameHead_noBVar head]; simp)]
  · intro Γ ρ code hcode head _ ρ' _
    rw [tName_quote _ hcode head, tName_quote _ hcode head]
  · intro x Γ ρ hbvar hfvar _ hquote ρ' _
    rw [tName_eq_none _ hbvar hfvar hquote, tName_eq_none _ hbvar hfvar hquote]
  · intro Γ ρ ρ' _
    rfl
  · intro Γ ρ name j head ih ρ' agree
    rw [tProc_drop_of_nameHead _ head, tProc_drop_of_nameHead _ head,
      ih ρ' fun k hk => agree k (by simp [noBVar, noBVarList, hk]),
      agree j (by simp [noBVar, noBVarList, nameHead_noBVar head])]
  · intro Γ ρ name head ih ρ' agree
    rw [tProc_drop_of_nameHead_none _ head, tProc_drop_of_nameHead_none _ head,
      ih ρ' fun k hk => agree k (by simp [noBVar, noBVarList, hk])]
  · intro Γ ρ name payload ihn ihp ρ' agree
    rw [tProc.eq_3, tProc.eq_3, ihn ρ' fun k hk => agree k (by simp [noBVar, noBVarList, hk]),
      ihp ρ' fun k hk => agree k (by simp [noBVar, noBVarList, hk])]
  · intro Γ ρ name body ihn ihb ρ' agree
    rw [tProc.eq_4, tProc.eq_4, ihn ρ' fun k hk => agree k (by simp [noBVar, noBVarList, hk]),
      ihb ρ'.up ?_]
    intro k hk
    cases k with
    | zero => rfl
    | succ k =>
        simp only [Env.up]
        rw [agree k (by simp [noBVar, noBVarList, hk])]
  · intro Γ ρ elements ih ρ' agree
    rw [tProc.eq_5, tProc.eq_5]
    exact ih ρ' fun k hk => agree k (by simpa [noBVar] using hk)
  · intro x Γ ρ hzero hdrop hout hinp hbag ρ' _
    rw [tProc.eq_6 _ _ hzero hdrop hout hinp hbag, tProc.eq_6 _ _ hzero hdrop hout hinp hbag]
  · intro Γ ρ ρ' _
    rfl
  · intro Γ ρ process rest ihp ihr ρ' agree
    rw [tProcs.eq_2, tProcs.eq_2,
      ihp ρ' fun k hk => agree k (by simp [noBVarList, hk]),
      ihr ρ' fun k hk => agree k (by simp [noBVarList, hk])]

section Environments

variable {Γ : Ctx sig} (k : Nat) (ρ ρ' : Env Γ)

/-- Executor name substitution is environment extension. -/
theorem tName_semanticSubstName (hq : tProc (Env.empty []) q = some q₀) (n : Pattern)
    (hk : ρ' k = some (lift0 q₀)) (hother : ∀ j, j ≠ k → ρ' j = ρ j)
    {t : Term sig Γ Srt.nm} (translated : tName ρ' n = some t) :
    tName ρ (semanticSubstName k (payloadName q) n) = tName ρ' n := by
  unfold semanticSubstName
  rcases semanticSubstNameMark_spec k (payloadName q) n with
    ⟨head, hmark⟩ | ⟨m, hm, head, hmark⟩ | ⟨head, hmark⟩
  · have received := tName_of_nameHead head translated
    rw [hk, Option.map_some] at received
    rw [hmark, tName_payloadName hq, translated, received]
  · rw [hmark, translate_semanticNormalize.1 n ρ]
    refine (translate_agree.1 ρ n ρ' fun j hj => hother j ?_).symm
    rintro rfl
    rw [nameHead_noBVar head] at hj
    exact hm (by simpa using hj)
  · rw [hmark, translate_semanticNormalize.1 n ρ]
    exact tName_env_irrelevant n head ρ ρ'

/-- A drop whose name the substitution did not supply keeps the drop. -/
theorem semanticSubstProc_drop_of_unmatched {replacement name name' : Pattern}
    (hmark : semanticSubstNameMark k replacement name = (name', false)) :
    semanticSubstProc k replacement (.apply "PDrop" [name]) = .apply "PDrop" [name'] := by
  rw [semanticSubstProc.eq_4, hmark]
  split
  rename_i first second hpair
  obtain ⟨rfl, rfl⟩ := hpair
  split
  · rename_i hfalse
    cases hfalse
  · rfl

/-- Executor substitution at a drop is environment extension: a drop of
the received name runs the payload; any other drop is unchanged. -/
theorem tProc_semanticSubst_drop (hq : tProc (Env.empty []) q = some q₀) (name : Pattern)
    (hk : ρ' k = some (lift0 q₀)) (hother : ∀ j, j ≠ k → ρ' j = ρ j)
    {t : Term sig Γ Srt.pr} (translated : tProc ρ' (.apply "PDrop" [name]) = some t) :
    tProc ρ (semanticSubstProc k (payloadName q) (.apply "PDrop" [name])) =
      tProc ρ' (.apply "PDrop" [name]) := by
  rcases semanticSubstNameMark_spec k (payloadName q) name with
    ⟨head, hmark⟩ | ⟨m, hm, head, hmark⟩ | ⟨head, hmark⟩
  · rw [semanticSubstProc.eq_4, hmark]
    show tProc ρ (semanticNormalizeProc q) = _
    rw [translate_semanticNormalize.2.1 q ρ, tProc_closed hq ρ, translated]
    rw [tProc_drop_of_nameHead _ head] at translated
    obtain ⟨_, _, received⟩ := Option.bind_eq_some_iff.mp translated
    rw [hk] at received
    exact received
  · rw [semanticSubstProc_drop_of_unmatched k hmark, ← semanticNormalizeProc.eq_5,
      translate_semanticNormalize.2.1 _ ρ]
    refine (translate_agree.2.1 ρ _ ρ' fun j hj => hother j ?_).symm
    intro same
    rw [same] at hj
    have free : noBVar k name = false := by simpa [noBVar, noBVarList] using hj
    rw [nameHead_noBVar head] at free
    exact hm (by simpa using free)
  · rw [semanticSubstProc_drop_of_unmatched k hmark, tProc.eq_2, tProc.eq_2,
      nameHead_semanticNormalizeName, head]
    simp only
    rw [translate_semanticNormalize.1 name ρ, tName_env_irrelevant name head ρ ρ']

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

/-- **Executor COMM is environment extension.** For a closed payload and a
process that translates in the receiving environment, the executor's
substitution at index `k` translates exactly as the unsubstituted process in
the environment that receives the payload at `k`. -/
theorem translate_semanticSubst (hq : tProc (Env.empty []) q = some q₀) :
    (∀ (k : Nat) (p : Pattern) {Γ : Ctx sig} (ρ ρ' : Env Γ),
      ρ' k = some (lift0 q₀) → (∀ j, j ≠ k → ρ' j = ρ j) →
      (∃ t, tProc ρ' p = some t) →
      tProc ρ (semanticSubstProc k (payloadName q) p) = tProc ρ' p) ∧
    (∀ (k : Nat) (ps : List Pattern) {Γ : Ctx sig} (ρ ρ' : Env Γ),
      ρ' k = some (lift0 q₀) → (∀ j, j ≠ k → ρ' j = ρ j) →
      (∃ t, tProcs ρ' ps = some t) →
      tProcs ρ (semanticSubstProcList k (payloadName q) ps) = tProcs ρ' ps) := by
  refine semanticSubstProc.mutual_induct (payloadName q)
    (fun k p => ∀ {Γ : Ctx sig} (ρ ρ' : Env Γ),
      ρ' k = some (lift0 q₀) → (∀ j, j ≠ k → ρ' j = ρ j) →
      (∃ t, tProc ρ' p = some t) →
      tProc ρ (semanticSubstProc k (payloadName q) p) = tProc ρ' p)
    (fun k ps => ∀ {Γ : Ctx sig} (ρ ρ' : Env Γ),
      ρ' k = some (lift0 q₀) → (∀ j, j ≠ k → ρ' j = ρ j) →
      (∃ t, tProcs ρ' ps = some t) →
      tProcs ρ (semanticSubstProcList k (payloadName q) ps) = tProcs ρ' ps)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro k n hn Γ ρ ρ' _ _ _
    rw [semanticSubstProc.eq_1, if_pos hn]
    rw [tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
      tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp)]
  · intro k n hn Γ ρ ρ' _ _ _
    rw [semanticSubstProc.eq_1, if_neg hn]
    rw [tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
      tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp)]
  · intro k x Γ ρ ρ' _ _ _
    rw [semanticSubstProc.eq_2]
    rw [tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
      tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp)]
  · intro k p Γ ρ ρ' _ _ _
    rw [semanticSubstProc.eq_3]
    rw [tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
      tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp)]
  · intro k name _ _ Γ ρ ρ' hk hother ⟨t, translated⟩
    exact tProc_semanticSubst_drop k ρ ρ' hq name hk hother translated
  · intro k name _ _ _ _ Γ ρ ρ' hk hother ⟨t, translated⟩
    exact tProc_semanticSubst_drop k ρ ρ' hq name hk hother translated
  · intro k n payload ih Γ ρ ρ' hk hother ⟨t, translated⟩
    rw [tProc.eq_3] at translated
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at translated
    obtain ⟨c, hc, process, hprocess, -⟩ := translated
    rw [semanticSubstProc.eq_5, tProc.eq_3, tProc.eq_3,
      tName_semanticSubstName k ρ ρ' hq n hk hother hc, ih ρ ρ' hk hother ⟨process, hprocess⟩]
  · intro k n body ih Γ ρ ρ' hk hother ⟨t, translated⟩
    rw [tProc.eq_4] at translated
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at translated
    obtain ⟨c, hc, continuation, hcontinuation, -⟩ := translated
    obtain ⟨hk', hother'⟩ := up_extended hk hother
    rw [semanticSubstProc.eq_6, tProc.eq_4, tProc.eq_4,
      tName_semanticSubstName k ρ ρ' hq n hk hother hc,
      ih ρ.up ρ'.up hk' hother' ⟨continuation, hcontinuation⟩]
  · intro k nm body _ Γ ρ ρ' _ _ _
    rw [semanticSubstProc.eq_7]
    rw [tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
      tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp)]
  · intro k n nms body _ Γ ρ ρ' _ _ _
    rw [semanticSubstProc.eq_8]
    rw [tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
      tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp)]
  · intro k body repl _ _ Γ ρ ρ' _ _ _
    rw [semanticSubstProc.eq_9]
    rw [tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
      tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp)]
  · intro k ct elems rest ih Γ ρ ρ' hk hother translated
    rw [semanticSubstProc.eq_10]
    by_cases hbag : ct = .hashBag ∧ rest = none
    · obtain ⟨rfl, rfl⟩ := hbag
      rw [tProc.eq_5, tProc.eq_5, ih ρ ρ' hk hother (by simpa only [tProc.eq_5] using translated)]
    · have hne : ∀ elements others : List Pattern,
          Pattern.collection ct others rest = .collection .hashBag elements none → False := by
        intro elements others h
        simp only [Pattern.collection.injEq] at h
        exact hbag ⟨h.1, h.2.2⟩
      rw [tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp)
          (fun elements => hne elements _),
        tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp)
          (fun elements => hne elements _)]
  · intro k p hbvar hfvar hquote hdrop hout hinp hlam hmulti hsubst hcoll Γ ρ ρ' _ _ _
    rw [semanticSubstProc.eq_11 k _ p hbvar hfvar hquote hdrop hout hinp hlam hmulti
      hsubst hcoll]
    by_cases hzero : p = .apply "PZero" []
    · subst hzero
      rw [tProc.eq_1, tProc.eq_1]
    · rw [tProc_eq_none_of_not _ _ hzero hdrop hout hinp (fun e h => hcoll _ _ _ h),
        tProc_eq_none_of_not _ _ hzero hdrop hout hinp (fun e h => hcoll _ _ _ h)]
  · intro k Γ ρ ρ' _ _ _
    rfl
  · intro k p ps ihp ihps Γ ρ ρ' hk hother ⟨t, translated⟩
    rw [tProcs.eq_2] at translated
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at translated
    obtain ⟨head, hhead, tail, htail, -⟩ := translated
    rw [semanticSubstProcList.eq_2, tProcs.eq_2, tProcs.eq_2, ihp ρ ρ' hk hother ⟨head, hhead⟩,
      ihps ρ ρ' hk hother ⟨tail, htail⟩]

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
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro Γ ρ k Δ σ ρ' hρ t h
    rw [tName_bvar] at h
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h
    refine ⟨nameOf (bind σ u), ?_, nameOf_bind_equiv σ u⟩
    rw [tName_bvar, hρ k u hu, Option.map_some]
  · intro Γ ρ label Δ σ ρ' hρ t h
    rw [tName_fvar] at h
    cases h
    exact ⟨freeT label, tName_fvar ρ' label, .refl _⟩
  · intro Γ ρ name ih Δ σ ρ' hρ t h
    rw [tName_quoteDrop] at h ⊢
    exact ih σ ρ' hρ t h
  · intro Γ ρ code hcode k head ih Δ σ ρ' hρ t h
    rw [tName_quote_of_nameHead _ hcode head] at h
    obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨c', hc', -⟩ := ih σ ρ' hρ c hc
    refine ⟨nameOf (bind σ u), ?_, nameOf_bind_equiv σ u⟩
    rw [tName_quote_of_nameHead _ hcode head, hc', Option.bind_some, hρ k u hu, Option.map_some]
  · intro Γ ρ code hcode head _ Δ σ ρ' hρ t h
    rw [tName_quote _ hcode head] at h
    rw [tName_quote _ hcode head]
    obtain ⟨literal, hliteral, rfl⟩ := Option.map_eq_some_iff.mp h
    refine ⟨nameOf (lift0 literal), by rw [hliteral, Option.map_some], ?_⟩
    rw [bind_nameOf_lift0]
    exact .refl _
  · intro x Γ ρ hbvar hfvar _ hquote Δ σ ρ' hρ t h
    rw [tName_eq_none _ hbvar hfvar hquote] at h
    cases h
  · intro Γ ρ Δ σ ρ' hρ t h
    rw [tProc.eq_1] at h
    cases h
    exact ⟨nilT, tProc.eq_1 ρ', .refl _⟩
  · intro Γ ρ name k hk ih Δ σ ρ' hρ t h
    rw [tProc_drop_of_nameHead _ hk] at h ⊢
    obtain ⟨m, hm, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨m', hm', -⟩ := ih σ ρ' hρ m hm
    exact ⟨bind σ t, by rw [hm', Option.bind_some, hρ k t h], .refl _⟩
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
  obtain ⟨t, received, equivalent⟩ :=
    translate_bind.2.1 (Env.empty []).up body (extend q₀) (Env.received q₀) (by
      intro j t h
      cases j with
      | zero =>
          cases h
          rfl
      | succ j => cases h) K hbody
  have hsubst : tProc (Env.empty []) (semanticCommSubst body q) =
      tProc (Env.received q₀) body := by
    refine (translate_semanticSubst hq).1 0 body (Env.empty []) (Env.received q₀) ?_ ?_ ⟨t, received⟩
    · rw [lift0_nil]
      rfl
    · intro j hj
      cases j with
      | zero => exact (hj rfl).elim
      | succ j => rfl
  rw [hsubst]
  exact ⟨t, received, equivalent⟩

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

/-! ## Controls

`@(*x|0)` is the quote of a parallel bag holding the drop of `x` and the
unit. Under a binder for `x` it is the bound name `x`, exactly as the
executor's whole-name test reads it. A non-unit partner, or a second drop,
leaves literal code. A pattern whose whole name is `x` but which is not a
name, such as a bag in name position, has no translation. -/

section Controls

open Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-- `@(*x|partner)`. -/
private abbrev quotedDropBeside (x partner : Pattern) : Pattern :=
  .apply "NQuote" [.collection .hashBag [.apply "PDrop" [x], partner] none]

/-- `@(*x|0)`. -/
private abbrev quotedDropBesideUnit (x : Pattern) : Pattern :=
  quotedDropBeside x (.apply "PZero" [])

/-- A non-unit partner, `@0!(0)`. -/
private abbrev partner : Pattern :=
  .apply "POutput" [.apply "NQuote" [.apply "PZero" []], .apply "PZero" []]

/-! ### `@(*x|0)` is the bound name `x` -/

example : nameHead (quotedDropBesideUnit (.bvar 0)) = some 0 := by decide

example : tName (Env.empty []).up (quotedDropBesideUnit (.bvar 0)) =
    tName (Env.empty []).up (.bvar 0) := rfl

example : tName (Env.empty []).up (quotedDropBesideUnit (.bvar 0)) =
    some (quoT (.var .zero)) := rfl

/-- Its drop runs the received process. -/
example : tProc (Env.empty []).up (.apply "PDrop" [quotedDropBesideUnit (.bvar 0)]) =
    some (.var .zero) := rfl

/-- Beneath two binders it denotes the outer one. -/
example : tName (Env.empty []).up.up (quotedDropBesideUnit (.bvar 1)) =
    tName (Env.empty []).up.up (.bvar 1) := rfl

/-- The unit may come first, and the drop may sit in a nested bag. -/
example : nameHead (.apply "NQuote" [.collection .hashBag
    [.apply "PZero" [], .collection .hashBag [.apply "PDrop" [.bvar 0], .apply "PZero" []] none]
    none]) = some 0 := by decide

/-- The quote of a drop is still resolved as the dropped name. -/
example : nameHead (.apply "NQuote" [.apply "PDrop" [.bvar 0]]) = some 0 := by decide

/-- The executor's whole-name test agrees and substitutes it, although the
name is normal and is not itself an index. -/
example : Canonical.canonicalize (quotedDropBesideUnit (.bvar 0)) = .bvar 0 :=
  (canonicalize_eq_bvar_iff_nameHead _ 0).mpr (by decide)

example : semanticNormalizeName (quotedDropBesideUnit (.bvar 0)) ≠ .bvar 0 := by decide

example (replacement : Pattern) :
    semanticSubstNameMark 0 replacement (quotedDropBesideUnit (.bvar 0)) =
      (replacement, true) := by
  unfold semanticSubstNameMark
  rw [if_pos ((canonicalize_eq_bvar_iff_nameHead _ 0).mpr (by decide))]

/-! ### A non-unit partner leaves literal code -/

example : nameHead (quotedDropBeside (.bvar 0) partner) = none := by decide

/-- It is translated as literal code, which no binder reaches, so beneath a
binder for `x` it has no translation. -/
example : tName (Env.empty []).up (quotedDropBeside (.bvar 0) partner) =
    (tProc (Env.empty []) (.collection .hashBag [.apply "PDrop" [.bvar 0], partner] none)).map
      fun literal => nameOf (lift0 literal) := rfl

example : tName (Env.empty []).up (quotedDropBeside (.bvar 0) partner) = none := rfl

/-- With a free name the same literal code is translated. -/
example : (tName (Env.empty []) (quotedDropBeside (.fvar "x") partner)).isSome = true := rfl

/-- The executor's whole-name test misses it at every index. -/
example (k : Nat) : Canonical.canonicalize (quotedDropBeside (.bvar 0) partner) ≠ .bvar k := by
  rw [Ne, canonicalize_eq_bvar_iff_nameHead,
    show nameHead (quotedDropBeside (.bvar 0) partner) = none by decide]
  simp

/-! ### Two drops in one bag are not a name -/

example : nameHead (.apply "NQuote"
    [.collection .hashBag [.apply "PDrop" [.bvar 0], .apply "PDrop" [.bvar 1]] none]) = none := by
  decide

example : nameHead (.apply "NQuote"
    [.collection .hashBag [.apply "PDrop" [.bvar 0], .apply "PDrop" [.bvar 0]] none]) = none := by
  decide

example : tName (Env.empty []).up.up (.apply "NQuote"
    [.collection .hashBag [.apply "PDrop" [.bvar 0], .apply "PDrop" [.bvar 1]] none]) = none := rfl

/-! ### A whole name must still be a name -/

/-- A bag in name position has the whole name `x`, but it is not a name, so
neither it nor its drop translates. -/
example : nameHead (.collection .hashBag [.bvar 0] none) = some 0 := by decide

example : tName (Env.empty []).up (.collection .hashBag [.bvar 0] none) = none := rfl

example : tProc (Env.empty []).up (.apply "PDrop" [.collection .hashBag [.bvar 0] none]) =
    none := rfl

/-- A quotation whose code is not a process is not a name either. -/
example : nameHead (.apply "NQuote" [.collection .hashBag
    [.apply "PDrop" [.bvar 0], .apply "NQuote" [.apply "PDrop" [.apply "PZero" []]]] none]) =
      some 0 := by
  decide

example : tName (Env.empty []).up (.apply "NQuote" [.collection .hashBag
    [.apply "PDrop" [.bvar 0], .apply "NQuote" [.apply "PDrop" [.apply "PZero" []]]] none]) =
      none := rfl

end Controls

end Mettapedia.OSLF.Binding.RhoPayloadPresentation
