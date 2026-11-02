import Mettapedia.Languages.MeTTa.PeTTa.BridgeKit
import Mettapedia.Languages.MeTTa.PeTTa.PureData

/-!
# Moving proved facts between programs

A fact proved about one program holds in another that agrees with it on the heads the fact's code
can reach. Agreement composes: it is transitive, it restricts to fewer heads, each library's
runtime agrees with its base on the heads it leaves alone, and a call fragment agrees with its
source on the heads it keeps. A chain of these moves a fact from the program it was proved in into
any library stacked above it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.BridgeKit

open SpaceSemantics (Program Equation)
open Eval

theorem agreement_trans {allowed : String → Bool} {first second third : Program}
    (one : ProgramAgreementOn allowed first second) (two : ProgramAgreementOn allowed second third) :
    ProgramAgreementOn allowed first third where
  dispatch head supported := (one.dispatch head supported).trans (two.dispatch head supported)
  demand head index supported := (one.demand head index supported).trans (two.demand head index supported)
  bodies head values supported := (one.bodies head values supported).trans (two.bodies head values supported)

theorem agreement_mono {fewer more : String → Bool} {first second : Program}
    (within : ∀ head, fewer head = true → more head = true) (agreed : ProgramAgreementOn more first second) :
    ProgramAgreementOn fewer first second where
  dispatch head supported := agreed.dispatch head (within head supported)
  demand head index supported := agreed.demand head index (within head supported)
  bodies head values supported := agreed.bodies head values (within head supported)

/-- **A library's runtime agrees with its base** on any heads it leaves alone. -/
theorem Library.agreement_on {L : Library} (checked : L.check = true) {allowed : String → Bool}
    (inherited : ∀ head, allowed head = true → L.inherited head = true) :
    ProgramAgreementOn allowed L.base L.runtime :=
  agreement_mono inherited (Library.agreement checked)

/-- **A call fragment agrees with its source** on the heads it keeps: a program whose equations and
arrow declarations are the source's for the heads it owns. -/
theorem fragment_agreement {owns allowed : String → Bool} (fragment source : Program)
    (equations : fragment.equations = source.equations.filter fun equation => owns equation.head)
    (declarations : fragment.declarations = source.declarations.filter (retainedCallDeclaration owns))
    (kept : ∀ head, allowed head = true → owns head = true) :
    ProgramAgreementOn allowed fragment source := by
  apply programAgreementOn_of_retained_rows
  · rw [equations, List.filter_filter]
    congr 1
    funext equation
    cases supported : allowed equation.head
    · simp
    · simp [kept _ supported]
  · rw [declarations, List.filter_filter]
    congr 1
    funext declaration
    unfold retainedCallDeclaration
    split
    · rename_i name _
      cases supported : allowed name
      · simp
      · simp [kept _ supported]
    · simp

/-- Code within fewer heads is within more. -/
theorem codeWithin_mono {fewer more : String → Bool} (within : ∀ head, fewer head = true → more head = true) :
    ∀ code : Mettapedia.Languages.MeTTa.OSLFCore.Atom, codeWithin fewer code = true → codeWithin more code = true
  | .symbol _, _ => rfl
  | .var _, _ => rfl
  | .grounded _, _ => rfl
  | .expression items, supported => by
      simp only [codeWithin, Bool.and_eq_true, atomsWithin_eq_all, List.all_eq_true] at supported ⊢
      refine ⟨?_, fun item member => codeWithin_mono within item (supported.2 item member)⟩
      have head := supported.1
      match items, head with
      | [], _ => rfl
      | .symbol name :: _, head =>
          simp only [expressionHeadWithin, Bool.and_eq_true] at head ⊢
          exact ⟨within name head.1, head.2⟩
      | .var _ :: _, _ => rfl
      | .grounded _ :: _, _ => rfl
      | .expression _ :: _, _ => rfl
termination_by code => sizeOf code
decreasing_by
  have := List.sizeOf_lt_of_mem member
  simp only [Mettapedia.Languages.MeTTa.OSLFCore.Atom.expression.sizeOf_spec]
  omega

/-- A program is closed under heads when every body of a kept head stays within them. -/
theorem closed_of_all (allowed : String → Bool) (program : Program) (binding : allowed "let" = true)
    (checked : program.equations.all (fun equation => !allowed equation.head || codeWithin allowed equation.body) = true) :
    ProgramClosed allowed program := by
  refine ⟨binding, fun equation member supported => ?_⟩
  have row := List.all_eq_true.mp checked equation member
  simpa only [supported, Bool.not_true, Bool.false_or] using row

/-- **Transport.** A computation of a program closed under some heads, whose code stays within them,
runs unchanged in any program agreeing on them. -/
theorem transport {allowed : String → Bool} {first second : Program}
    (closed : ProgramClosed allowed first) (agreement : ProgramAgreementOn allowed first second)
    {caller : Mettapedia.Languages.ProcessCalculi.MORK.Subst} {before after : Effects.State}
    {code answer : Mettapedia.Languages.MeTTa.OSLFCore.Atom}
    (supported : codeWithin allowed code = true) (returned : PureReturns first caller before code after answer) :
    PureReturns second caller before code after answer :=
  path_of_closed_agreement closed agreement ⟨supported, rfl⟩ returned

open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst) in
/-- Distinct names bound to values read back the values. -/
theorem zip_reads (names : List String) (distinct : names.Nodup) :
    ∀ values : List Mettapedia.Languages.MeTTa.OSLFCore.Atom, values.length = names.length →
      (names.map Mettapedia.Languages.MeTTa.OSLFCore.Atom.var).map (applySubst (names.zip values)) = values := by
  induction names with
  | nil => intro values length; cases values <;> simp_all
  | cons name rest ih =>
    intro values length
    cases values with
    | nil => simp at length
    | cons value others =>
      simp only [List.nodup_cons] at distinct
      have tail := ih distinct.2 others (by simpa using length)
      simp only [List.map_cons, List.zip_cons_cons, List.cons.injEq]
      refine ⟨by simp [applySubst, Subst.lookup, List.find?], ?_⟩
      have skip : ∀ other ∈ rest, applySubst ((name, value) :: rest.zip others) (.var other) =
          applySubst (rest.zip others) (.var other) := by
        intro other inRest
        have different : (name == other) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]
          intro same
          exact distinct.1 (same ▸ inRest)
        simp [applySubst, Subst.lookup, List.find?, different]
      conv_rhs => rw [← tail]
      simp only [List.map_map]
      apply List.map_congr_left
      intro other inRest
      exact skip other inRest

open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst) in
/-- **A base head's fact at values holds in the runtime.** The values are bound to distinct names,
so the transported code is the call alone. -/
theorem Library.lift_call {L : Library} (checked : L.check = true) {head : String}
    (inherited : L.inherited head = true) (notEval : head ≠ "eval")
    (dispatch : (ioHead head || StdLib.known head || L.base.equations.any (·.head == head)) = true)
    (ordinary : head ∉ specialForms) (names : List String) (distinct : names.Nodup)
    {values : List Mettapedia.Languages.MeTTa.OSLFCore.Atom} (length : values.length = names.length)
    (raw : ∀ index < names.length, argumentIsRaw L.base head index = true)
    {state : Effects.State} {answer : Mettapedia.Languages.MeTTa.OSLFCore.Atom}
    (fact : PureReturns L.base [] state (.expression (.symbol head :: values)) state answer) :
    PureReturns L.runtime [] state (.expression (.symbol head :: values)) state answer := by
  have special : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "match"] := by
    simpa [specialForms] using ordinary
  have unchanged : values.map (applySubst []) = values := by
    have identity : applySubst [] = id := by
      funext value
      exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
    simp only [identity, List.map_id]
  have reads := zip_reads names distinct values length
  let code := Mettapedia.Languages.MeTTa.OSLFCore.Atom.expression
    (.symbol head :: names.map Mettapedia.Languages.MeTTa.OSLFCore.Atom.var)
  have bound : PureReturns L.base (names.zip values) state code state answer :=
    PureData.raw_capture_returns L.base [] (names.zip values) state state head values _ answer dispatch
      (fun index bounded => raw index (by omega)) special (by rw [unchanged, reads]) fact
  have supported : codeWithin L.inherited code = true := by
    simp only [Library.inherited] at inherited
    simp [code, codeWithin, expressionHeadWithin, Library.inherited, inherited, notEval]
  have lifted := L.lift checked supported bound
  have agreed := Library.agreement checked
  apply PureData.raw_capture_returns L.runtime (names.zip values) [] state state head
    (names.map Mettapedia.Languages.MeTTa.OSLFCore.Atom.var) values answer
  · rw [← agreed.dispatch head inherited]
    exact dispatch
  · intro index bounded
    rw [← agreed.demand head index inherited]
    exact raw index (by simpa only [List.length_map] using bounded)
  · exact special
  · rw [unchanged, reads]
  · exact lifted

open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst) in
/-- **A fact about a call at values moves to any agreeing program.** The values are bound to
distinct names, so only the call needs to stay within the agreed heads. -/
theorem transport_call {allowed : String → Bool} {first second : Program}
    (closed : ProgramClosed allowed first) (agreement : ProgramAgreementOn allowed first second) {head : String}
    (kept : allowed head = true) (notEval : head ≠ "eval")
    (dispatch : (ioHead head || StdLib.known head || first.equations.any (·.head == head)) = true)
    (ordinary : head ∉ specialForms) (names : List String) (distinct : names.Nodup)
    {values : List Mettapedia.Languages.MeTTa.OSLFCore.Atom} (length : values.length = names.length)
    (raw : ∀ index < names.length, argumentIsRaw first head index = true)
    {state : Effects.State} {answer : Mettapedia.Languages.MeTTa.OSLFCore.Atom}
    (fact : PureReturns first [] state (.expression (.symbol head :: values)) state answer) :
    PureReturns second [] state (.expression (.symbol head :: values)) state answer := by
  have special : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "match"] := by
    simpa [specialForms] using ordinary
  have unchanged : values.map (applySubst []) = values := by
    have identity : applySubst [] = id := by
      funext value
      exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
    simp only [identity, List.map_id]
  have reads := zip_reads names distinct values length
  let code := Mettapedia.Languages.MeTTa.OSLFCore.Atom.expression
    (.symbol head :: names.map Mettapedia.Languages.MeTTa.OSLFCore.Atom.var)
  have bound : PureReturns first (names.zip values) state code state answer :=
    PureData.raw_capture_returns first [] (names.zip values) state state head values _ answer dispatch
      (fun index bounded => raw index (by omega)) special (by rw [unchanged, reads]) fact
  have supported : codeWithin allowed code = true := by
    simp [code, codeWithin, expressionHeadWithin, kept, notEval]
  have moved := transport closed agreement supported bound
  apply PureData.raw_capture_returns second (names.zip values) [] state state head
    (names.map Mettapedia.Languages.MeTTa.OSLFCore.Atom.var) values answer
  · rw [← agreement.dispatch head kept]
    exact dispatch
  · intro index bounded
    rw [← agreement.demand head index kept]
    exact raw index (by simpa only [List.length_map] using bounded)
  · exact special
  · rw [unchanged, reads]
  · exact moved

open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst) in
/-- **A call at values from the call at bound names.** When every argument of the head is raw,
binding the values to distinct names and calling the head on the names returns the same answer as
calling it on the values. -/
theorem call_of_bound {program : Program} {head : String}
    (dispatch : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = true)
    (ordinary : head ∉ specialForms) (names : List String) (distinct : names.Nodup)
    {values : List Mettapedia.Languages.MeTTa.OSLFCore.Atom} (length : values.length = names.length)
    (raw : ∀ index < names.length, argumentIsRaw program head index = true)
    {state : Effects.State} {answer : Mettapedia.Languages.MeTTa.OSLFCore.Atom}
    (bound : PureReturns program (names.zip values) state
      (.expression (.symbol head :: names.map Mettapedia.Languages.MeTTa.OSLFCore.Atom.var)) state answer) :
    PureReturns program [] state (.expression (.symbol head :: values)) state answer := by
  have special : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "match"] := by
    simpa [specialForms] using ordinary
  have unchanged : values.map (applySubst []) = values := by
    have identity : applySubst [] = id := by
      funext value
      exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
    simp only [identity, List.map_id]
  apply PureData.raw_capture_returns program (names.zip values) [] state state head
    (names.map Mettapedia.Languages.MeTTa.OSLFCore.Atom.var) values answer dispatch
  · intro index bounded
    exact raw index (by simpa only [List.length_map] using bounded)
  · exact special
  · rw [unchanged, zip_reads names distinct values length]
  · exact bound

end Mettapedia.Languages.MeTTa.PeTTa.BridgeKit
