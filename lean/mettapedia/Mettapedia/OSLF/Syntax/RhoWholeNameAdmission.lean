import Mettapedia.OSLF.Syntax.RhoPayloadExecutorComparison
import Mettapedia.OSLF.MeTTaIL.ScopedPattern
import Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax

/-!
# Scope admission for rho whole names

Rho's name equation identifies `@*n` with the whole name `n`. The
scope checker therefore resolves this exact shape before applying the
literal-quotation boundary. Other quotations remain sealed: a bound
index inside their code does not gain access to the surrounding binder.
This checker is specific to the rho presentation and does not change the
shared MeTTaIL quotation checker.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoPayloadPresentation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep (RhoStep)

mutual

/-- Rho-specific scope admission for a pattern at a binder depth.
The exact whole-name shape `@*n` inherits the scope of `n`; every other
quotation checks its code from depth zero. -/
def wholeNameSafeAt (depth : Nat) : Pattern → Bool
  | .bvar index => decide (index < depth)
  | .fvar _ => true
  | .apply "NQuote" [.apply "PDrop" [name]] =>
      wholeNameSafeAt depth name
  | .apply "NQuote" [body] => wholeNameSafeAt 0 body
  | .apply _ arguments => wholeNameSafeListAt depth arguments
  | .lambda _ body => wholeNameSafeAt (depth + 1) body
  | .multiLambda arity _ body => wholeNameSafeAt (depth + arity) body
  | .subst body replacement =>
      wholeNameSafeAt (depth + 1) body &&
        wholeNameSafeAt depth replacement
  | .collection _ elements _ => wholeNameSafeListAt depth elements

/-- List recursion for the rho-specific scope admission. -/
def wholeNameSafeListAt (depth : Nat) : List Pattern → Bool
  | [] => true
  | pattern :: rest =>
      wholeNameSafeAt depth pattern && wholeNameSafeListAt depth rest

end

/-- Closed rho scope admission. -/
def wholeNameSafe (pattern : Pattern) : Bool := wholeNameSafeAt 0 pattern

/-- A bound whole name is admitted where the shared literal-quotation
checker rejects it. -/
theorem bound_wholeNameSafe_control :
    wholeNameSafeAt 1
      (.apply "NQuote" [.apply "PDrop" [.bvar 0]]) = true ∧
    binderSafeAt "NQuote" 1
      (.apply "NQuote" [.apply "PDrop" [.bvar 0]]) = false := by
  decide

/-- A literal quotation of code containing an outer bound index remains
rejected, even though the exact `@*n` whole-name form is admitted. -/
theorem literal_quote_remains_sealed :
    wholeNameSafeAt 1
      (.apply "NQuote" [.apply "POutput"
        [.bvar 0, .apply "PZero" []]]) = false := by
  decide

/-- A whole name denotes only an index actually available at the current
binder depth. This is the scope fact needed by translation coverage. -/
theorem nameHead_lt_of_wholeNameSafe {name : Pattern} {index : Nat}
    (head : nameHead name = some index) :
    ∀ {depth : Nat}, wholeNameSafeAt depth name = true → index < depth := by
  induction name using nameHead.induct with
  | case1 k =>
      intro depth safe
      simp only [nameHead, Option.some.injEq] at head
      subst head
      simpa [wholeNameSafeAt] using safe
  | case2 inner ih =>
      intro depth safe
      rw [nameHead.eq_2] at head
      exact ih head (by simpa [wholeNameSafeAt] using safe)
  | case3 other hbvar hquoteDrop =>
      rw [nameHead.eq_3 other hbvar hquoteDrop] at head
      cases head

/-- Translation resolves an exact whole-name chain through the same
environment entry as its underlying bound index. -/
theorem tName_eq_env_of_nameHead {Γ : Ctx sig} (ρ : Env Γ)
    {name : Pattern} {index : Nat} (head : nameHead name = some index) :
    tName ρ name = (ρ index).map nameOf := by
  induction name using nameHead.induct with
  | case1 k =>
      simp only [nameHead, Option.some.injEq] at head
      subst head
      rfl
  | case2 inner ih =>
      rw [nameHead.eq_2] at head
      rw [tName.eq_3]
      exact ih head
  | case3 other hbvar hquoteDrop =>
      rw [nameHead.eq_3 other hbvar hquoteDrop] at head
      cases head

/-- If the drop of a well-scoped name translates, the name itself
translates. This recovers the name witness needed for whole-name quotes. -/
theorem tName_exists_of_drop_translation {Γ : Ctx sig} (ρ : Env Γ)
    {name : Pattern} {process : Term sig Γ Srt.pr}
    (translated : tProc ρ (.apply "PDrop" [name]) = some process) :
    ∃ value, tName ρ name = some value := by
  rw [tProc.eq_2] at translated
  cases head : nameHead name with
  | some index =>
      simp only [head] at translated
      refine ⟨nameOf process, ?_⟩
      rw [tName_eq_env_of_nameHead ρ head, translated]
      rfl
  | none =>
      simp only [head] at translated
      obtain ⟨value, hvalue, _⟩ := Option.map_eq_some_iff.mp translated
      exact ⟨value, hvalue⟩

/-- Every well-sorted rho process admitted by whole-name-aware scope
checking translates in an environment that supplies its bound indices.
Literal quotations remain closed, while an exact `@*n` follows the
surrounding name environment. -/
theorem translate_covers_wholeNameSafe {free : FreeSortContext}
    (hfree : ∀ x, free x ≠ some rhoReflectivePresentation.processSort)
    {bound : List String} {p : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free bound p) :
    (∀ i : Nat, bound[i]? ≠ some rhoReflectivePresentation.processSort) →
      ∀ (depth : Nat) {Γ : Ctx sig} (ρ : Env Γ),
        (∀ index, index < depth → ∃ t, ρ index = some t) →
          wholeNameSafeAt depth p = true → ∃ t, tProc ρ p = some t := by
  refine ProcWellSorted.rec
    (motive_1 := fun bound name _ =>
      (∀ i : Nat, bound[i]? ≠ some rhoReflectivePresentation.processSort) →
      ∀ (depth : Nat) {Γ : Ctx sig} (ρ : Env Γ),
        (∀ index, index < depth → ∃ t, ρ index = some t) →
          wholeNameSafeAt depth name = true → ∃ value, tName ρ name = some value)
    (motive_2 := fun bound process _ =>
      (∀ i : Nat, bound[i]? ≠ some rhoReflectivePresentation.processSort) →
      ∀ (depth : Nat) {Γ : Ctx sig} (ρ : Env Γ),
        (∀ index, index < depth → ∃ t, ρ index = some t) →
          wholeNameSafeAt depth process = true → ∃ t, tProc ρ process = some t)
    (motive_3 := fun bound processes _ =>
      (∀ i : Nat, bound[i]? ≠ some rhoReflectivePresentation.processSort) →
      ∀ (depth : Nat) {Γ : Ctx sig} (ρ : Env Γ),
        (∀ index, index < depth → ∃ t, ρ index = some t) →
          wholeNameSafeListAt depth processes = true →
            ∃ t, tProcs ρ processes = some t)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
  · intro bound index _ _ depth Γ ρ hρ safe
    have hlt : index < depth := by simpa [wholeNameSafeAt] using safe
    obtain ⟨t, ht⟩ := hρ index hlt
    exact ⟨nameOf t, by rw [tName.eq_1, ht, Option.map_some]⟩
  · intro bound name _ _ depth Γ ρ _ _
    exact ⟨freeT name, tName.eq_2 ρ name⟩
  · intro bound process _ ih hb depth Γ ρ hρ safe
    change wholeNameSafeAt depth (.apply "NQuote" [process]) = true at safe
    show ∃ value, tName ρ (.apply "NQuote" [process]) = some value
    by_cases hdrop : ∃ name, process = .apply "PDrop" [name]
    · obtain ⟨name, rfl⟩ := hdrop
      rw [tName.eq_3]
      have safeDrop : wholeNameSafeAt depth (.apply "PDrop" [name]) = true := by
        simpa [wholeNameSafeAt, wholeNameSafeListAt] using safe
      obtain ⟨t, ht⟩ := ih hb depth ρ hρ safeDrop
      exact tName_exists_of_drop_translation ρ ht
    · have safe0 : wholeNameSafeAt 0 process = true := by
        cases process <;> simp_all [wholeNameSafeAt]
      obtain ⟨code, hcode⟩ := ih hb 0 (Env.empty [])
        (fun index hi => absurd hi (Nat.not_lt_zero index)) safe0
      have hnot : ∀ name, process = .apply "PDrop" [name] → False :=
        fun name equal => hdrop ⟨name, equal⟩
      exact ⟨nameOf (lift0 code), by
        rw [tName.eq_4 _ _ hnot, hcode, Option.map_some]⟩
  · intro bound index lookup hb
    exact absurd lookup (hb index)
  · intro bound name lookup _
    exact absurd lookup (hfree name)
  · intro bound _ depth Γ ρ _ _
    exact ⟨nilT, tProc.eq_1 ρ⟩
  · intro bound name _ ih hb depth Γ ρ hρ safe
    change wholeNameSafeAt depth (.apply "PDrop" [name]) = true at safe
    show ∃ t, tProc ρ (.apply "PDrop" [name]) = some t
    rw [tProc.eq_2]
    cases head : nameHead name with
    | some index =>
        exact hρ index (nameHead_lt_of_wholeNameSafe head
          (by simpa [wholeNameSafeAt, wholeNameSafeListAt] using safe))
    | none =>
        have safeName : wholeNameSafeAt depth name = true := by
          simpa [wholeNameSafeAt, wholeNameSafeListAt] using safe
        obtain ⟨value, hvalue⟩ := ih hb depth ρ hρ safeName
        exact ⟨drpT value, by simp only [hvalue, Option.map_some]⟩
  · intro bound channel payload _ _ ihc ihp hb depth Γ ρ hρ safe
    change wholeNameSafeAt depth (.apply "POutput" [channel, payload]) = true at safe
    show ∃ t, tProc ρ (.apply "POutput" [channel, payload]) = some t
    have ⟨safeChannel, safePayload⟩ :
        wholeNameSafeAt depth channel = true ∧
          wholeNameSafeAt depth payload = true := by
      simpa [wholeNameSafeAt, wholeNameSafeListAt] using safe
    obtain ⟨c, hc⟩ := ihc hb depth ρ hρ safeChannel
    obtain ⟨q, hq⟩ := ihp hb depth ρ hρ safePayload
    exact ⟨outT c q, by rw [tProc.eq_3, hc, Option.bind_some, hq, Option.map_some]⟩
  · intro bound channel body _ _ ihc ihb hb depth Γ ρ hρ safe
    change wholeNameSafeAt depth (.apply "PInput" [channel, .lambda none body]) = true at safe
    show ∃ t, tProc ρ (.apply "PInput" [channel, .lambda none body]) = some t
    have ⟨safeChannel, safeBody⟩ :
        wholeNameSafeAt depth channel = true ∧
          wholeNameSafeAt (depth + 1) body = true := by
      simpa [wholeNameSafeAt, wholeNameSafeListAt] using safe
    obtain ⟨c, hc⟩ := ihc hb depth ρ hρ safeChannel
    have hb' : ∀ i : Nat,
        (rhoReflectivePresentation.nameSort :: bound)[i]? ≠
          some rhoReflectivePresentation.processSort := by
      intro i
      cases i with
      | zero => simp [rhoReflectivePresentation]
      | succ i => simpa using hb i
    have hρ' : ∀ index, index < depth + 1 → ∃ t, ρ.up index = some t := by
      intro index hi
      cases index with
      | zero => exact ⟨.var .zero, rfl⟩
      | succ index =>
          obtain ⟨t, ht⟩ := hρ index (by omega)
          exact ⟨weaken t, by simp [Env.up, ht]⟩
    obtain ⟨bodyTerm, hbody⟩ := ihb hb' (depth + 1) ρ.up hρ' safeBody
    exact ⟨inpT c bodyTerm, by
      rw [tProc.eq_4, hc, Option.bind_some, hbody, Option.map_some]⟩
  · intro bound processes _ ih hb depth Γ ρ hρ safe
    have safeList : wholeNameSafeListAt depth processes = true := by
      simpa [wholeNameSafeAt] using safe
    obtain ⟨t, ht⟩ := ih hb depth ρ hρ safeList
    exact ⟨t, by rw [show rhoReflectivePresentation.parallelCollection =
      .hashBag from rfl, tProc.eq_5]; exact ht⟩
  · intro bound _ depth Γ ρ _ _
    exact ⟨nilT, rfl⟩
  · intro bound process processes _ _ ihp ihs hb depth Γ ρ hρ safe
    simp only [wholeNameSafeListAt, Bool.and_eq_true] at safe
    obtain ⟨head, hhead⟩ := ihp hb depth ρ hρ safe.1
    obtain ⟨tail, htail⟩ := ihs hb depth ρ hρ safe.2
    exact ⟨parT head tail, by
      rw [tProcs.eq_2, hhead, Option.bind_some, htail, Option.map_some]⟩

/-- Every closed well-sorted process accepted by the whole-name-aware
checker has a translation into the intrinsic rho presentation. -/
theorem closed_admitted_translates_wholeNameSafe {free : FreeSortContext}
    (hfree : ∀ x, free x ≠ some rhoReflectivePresentation.processSort)
    {p : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] p)
    (safe : wholeNameSafe p = true) :
    ∃ t, tProc (Env.empty []) p = some t :=
  translate_covers_wholeNameSafe hfree typed (fun i => by simp)
    0 (Env.empty []) (fun index hi => absurd hi (Nat.not_lt_zero index)) safe

/-- The newly admitted bound whole name denotes the binder's name,
while the identical bound index in an ordinary quoted output is sealed. -/
theorem bound_wholeName_translation_control :
    tName (Env.empty []).up
      (.apply "NQuote" [.apply "PDrop" [.bvar 0]]) =
        some (quoT (.var .zero)) ∧
    wholeNameSafeAt 1
      (.apply "NQuote" [.apply "POutput"
        [.bvar 0, .apply "PZero" []]]) = false := by
  constructor
  · rfl
  · exact literal_quote_remains_sealed

/-- Repeated applications of the rho whole-name equation keep the same
bound name. The unrelated quoted output still fails the opacity control
above. -/
theorem nested_wholeName_translation_control :
    wholeNameSafeAt 1
      (.apply "NQuote" [.apply "PDrop"
        [.apply "NQuote" [.apply "PDrop" [.bvar 0]]]]) = true ∧
    tName (Env.empty []).up
      (.apply "NQuote" [.apply "PDrop"
        [.apply "NQuote" [.apply "PDrop" [.bvar 0]]]]) =
          some (quoT (.var .zero)) := by
  constructor
  · decide
  · rfl

/-- Quote/drop cancellation and the parallel-unit equation also identify a
quoted process of the form `*n | 0` with the whole name `n`. The current
source admission checker recognizes only the literal quote/drop spine: a
bound index in this structurally equivalent spelling remains behind its
quotation boundary. Thus coverage of all equation-equivalent spellings is
not implied by the exact-spine admission theorem. -/
theorem structural_unit_whole_name_boundary {Γ : Ctx sig}
    (name : Term sig Γ Srt.nm) :
    EqClosure equations
      (quoT (parT (drpT name) nilT)) name ∧
    wholeNameSafeAt 1
      (.apply "NQuote" [.collection .hashBag
        [.apply "PDrop" [.bvar 0], .apply "PZero" []] none]) = false := by
  constructor
  · exact (equiv_quoT (parT_nil (drpT name))).trans
      (quoteDrop_equiv name)
  · decide

/-- A well-sorted bound name may have an equation-equivalent spelling that
the exact-spine scope check rejects. The current translation also leaves
that spelling undefined: its literal-quotation branch checks the code in an
empty environment. This is a boundary of the admission criterion, rather
than a claim about the executable surface parser. -/
theorem structural_unit_bound_name_admission_gap :
    let wrapped : Pattern := .apply "NQuote" [.collection .hashBag
      [.apply "PDrop" [.bvar 0], .apply "PZero" []] none]
    NameWellSorted rhoReflectivePresentation FreeSortContext.empty
      [rhoReflectivePresentation.nameSort] wrapped ∧
    NameEquiv wrapped (.bvar 0) ∧
    wholeNameSafeAt 1 wrapped = false ∧
    tName (Env.empty []).up wrapped = none := by
  dsimp
  refine ⟨?_, ?_, by decide, by decide⟩
  · exact .quote (.parallel (.cons (.drop (.bvar rfl))
      (.cons .unit .nil)))
  · exact NameEquiv.trans _ _ _
      (NameEquiv.struct_equiv _ _
        (StructuralCongruence.par_nil_right (.apply "PDrop" [.bvar 0])))
      (NameEquiv.quote_drop (.bvar 0))

/-- Whole-name-aware admission is sufficient to enter the strict-core
executor/presentation comparison. The simulation theorem itself has no
additional quotation premise once the source translation exists. -/
theorem wholeNameSafe_strict_simulation {free : FreeSortContext}
    (hfree : ∀ x, free x ≠ some rhoReflectivePresentation.processSort)
    {source target : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] source)
    (safe : wholeNameSafe source = true)
    (step : RhoStep source target) :
    ∃ s t, tProc (Env.empty []) source = some s ∧
      tProc (Env.empty []) target = some t ∧ Steps strictRules s t := by
  obtain ⟨s, hs⟩ := closed_admitted_translates_wholeNameSafe hfree typed safe
  obtain ⟨t, ht, hstep⟩ := rhoStep_simulation typed step hs
  exact ⟨s, t, hs, ht, hstep⟩

/-- The same admission law applies to the book profile with Drop. -/
theorem wholeNameSafe_book_simulation {free : FreeSortContext}
    (hfree : ∀ x, free x ≠ some rhoReflectivePresentation.processSort)
    {source target : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] source)
    (safe : wholeNameSafe source = true)
    (step : RhoCombinedInterpretedStep.RhoStepWithDrop source target) :
    ∃ s t, tProc (Env.empty []) source = some s ∧
      tProc (Env.empty []) target = some t ∧ Steps bookRules s t := by
  obtain ⟨s, hs⟩ := closed_admitted_translates_wholeNameSafe hfree typed safe
  obtain ⟨t, ht, hstep⟩ := rhoStepWithDrop_simulation typed step hs
  exact ⟨s, t, hs, ht, hstep⟩

/-- Every strict-core presented step from a newly admitted source is
reflected by an authored step after structural rearrangement. -/
theorem wholeNameSafe_strict_reflection {free : FreeSortContext}
    (hfree : ∀ x, free x ≠ some rhoReflectivePresentation.processSort)
    {source : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] source)
    (safe : wholeNameSafe source = true) :
    ∃ s, tProc (Env.empty []) source = some s ∧
      ∀ {u : Term sig [] Srt.pr}, Steps strictRules s u →
        ∃ source' target', StructuralCongruence source source' ∧
          RhoStep source' target' ∧
          ∃ t, tProc (Env.empty []) target' = some t ∧ cls t = cls u := by
  obtain ⟨s, hs⟩ := closed_admitted_translates_wholeNameSafe hfree typed safe
  exact ⟨s, hs, fun step => strict_reflection typed hs step⟩

/-- The corresponding reflection for the book profile retains its
separately declared Drop rule. -/
theorem wholeNameSafe_book_reflection {free : FreeSortContext}
    (hfree : ∀ x, free x ≠ some rhoReflectivePresentation.processSort)
    {source : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] source)
    (safe : wholeNameSafe source = true) :
    ∃ s, tProc (Env.empty []) source = some s ∧
      ∀ {u : Term sig [] Srt.pr}, Steps bookRules s u →
        ∃ source' target', StructuralCongruence source source' ∧
          RhoCombinedInterpretedStep.RhoStepWithDrop source' target' ∧
          ∃ t, tProc (Env.empty []) target' = some t ∧ cls t = cls u := by
  obtain ⟨s, hs⟩ := closed_admitted_translates_wholeNameSafe hfree typed safe
  exact ⟨s, hs, fun step => book_reflection typed hs step⟩

end Mettapedia.OSLF.Binding.RhoPayloadPresentation

#print axioms Mettapedia.OSLF.Binding.RhoPayloadPresentation.structural_unit_whole_name_boundary
#print axioms Mettapedia.OSLF.Binding.RhoPayloadPresentation.structural_unit_bound_name_admission_gap
