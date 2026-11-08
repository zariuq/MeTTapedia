import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TrustedAliasControls

/-!
# Trusted versions whose polymorphic argument is ground

A trusted version of a PeTTa relation with the row `(-> A₁ … $t … Aₖ $t)`
skips the guard pair at `$t` on its calls to itself and on the calls other
versions discharge into it. The analysis reads facts by variable name: a
fact says that a name's current value is ground, uninterpreted, or both.
An open value can share variables with other values, and a binding made
through any of them changes it, so a fact about an open value can break
without the analysis seeing the name that broke it.

This module models the activation with every parameter in one substitution,
bound by two-way head unification, so a body binds any of them, ANY
parameters included. The analysis is the C's (`contract_eval`,
`contract_bind_any`, `contract_mark` with its OR-merge of a name's flags, the
restore of facts after a branch, `contract_self_call`,
`contract_meets_version`, `contract_equation`), for the entry facts ANY and
UNINTERPRETED, under three admission rules for the polymorphic value: before
the alias fix (uninterpreted), ground (uninterpreted and ground), and refined
(uninterpreted, and ground or every other value ground).

* `admits_run`: under the ground rule every fact that claims a value ground
  holds in every run, with its uninterpreted claim, and a run reads its calls
  only at arguments the versions admit. Open claims are never needed.
* `ground_version_eq_protocol`, `ground_version_answers`: under the ground
  rule, at arguments whose polymorphic argument is ground and uninterpreted,
  the version is the protocol at every fuel, multiplicity included, whatever
  the ANY arguments hold and however the body binds them, with no premise on
  declarations outside the argument; its answers are that argument, which is
  what a caller's discharge reads.
* `Refutations.callFlow_refutes`: with one parameter the refined rule admits
  any open argument; an untyped call's answer carries its variables to a name
  without a claim, which `contract_bind_any` lets a declared symbol bind.
  The version answers `(inc 1)`, the protocol nothing.
* `Refutations.headShare_refutes`: "every other argument is ground" does not
  stop head unification from binding the open argument through a variable its
  pattern shares with a ground ANY argument.
* `Controls`: the C counterexample's discharge is declined by the ground and
  the refined rules and admitted by the rule before them; a ground argument
  enters the version; the clean alias and the apart case keep their protocol,
  which answers as the version would.

Calls answer values only; bindings a callee makes in its arguments do not
flow back (a third refutation, a pure callee binding the open argument, is
outside this model). ANY parameters are the unguarded ones (`%Undefined%`,
`_`); GROUND, INSTANCE, CONSTANT and space parameters are outside it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.GroundUninterpretedVersions

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open UnifyingRegions UnifyingFrames OpenFrameEffects CapturedUninterpretedRegions
  ContractBindingFacts

/-! ## Two-way evaluation with calls -/

mutual
/-- The analysed syntax with two-way binding: `let`, a `case` arm and a
`match` row unify their pattern with the value under the current
substitution, which every later recipe reads. Calls receive their
arguments as the substitution leaves them. -/
def eval (E : Env) (O : Oracle) : Expr → Substitution → Multiset Outcome
  | .var x, σ => {(.var x, σ)}
  | .const a, σ => {(a, σ)}
  | .ctor c args, σ => (evalAll E O args σ).map fun out =>
      (.expression (.symbol c :: out.1), out.2)
  | .self args, σ => (evalAll E O args σ).bind fun out =>
      (O.self (out.1.map (substA out.2))).map fun r => (r, out.2)
  | .prim op args, σ => (evalAll E O args σ).bind fun out =>
      (E.prim op (out.1.map (substA out.2))).map fun r => (r, out.2)
  | .call f args, σ => (evalAll E O args σ).bind fun out =>
      (E.kept f (out.1.map (substA out.2))).map fun r => (r, out.2)
  | .enter f args, σ => (evalAll E O args σ).bind fun out =>
      (O.enter f (out.1.map (substA out.2))).map fun r => (r, out.2)
  | .letE p val body, σ => (eval E O val σ).bind fun out =>
      match bindPattern out.2 p out.1 with
      | none => 0
      | some τ => eval E O body τ
  | .ifE c t e, σ => (eval E O c σ).bind fun out =>
      if substA out.2 out.1 = truth then eval E O t out.2 else eval E O e out.2
  | .empty, _ => 0
  | .caseE key pats bodies, σ => (eval E O key σ).bind fun out =>
      evalArms E O out.2 out.1 pats bodies
  | .matchE src p t, σ => (eval E O src σ).bind fun out =>
      (E.rows (substA out.2 out.1)).bind fun row =>
        match bindPattern out.2 p row with
        | none => 0
        | some τ => eval E O t τ

/-- Evaluation of a list, left to right, threading the substitution. -/
def evalAll (E : Env) (O : Oracle) : List Expr → Substitution → Multiset (List Atom × Substitution)
  | [], σ => {([], σ)}
  | e :: es, σ => (eval E O e σ).bind fun first =>
      (evalAll E O es first.2).map fun rest => (first.1 :: rest.1, rest.2)

/-- The arms of a `case`: the first whose pattern unifies with the key. -/
def evalArms (E : Env) (O : Oracle) (σ : Substitution) (key : Atom) :
    List Pat → List Expr → Multiset Outcome
  | p :: ps, b :: bs => match bindPattern σ p key with
    | some τ => eval E O b τ
    | none => evalArms E O σ key ps bs
  | _, _ => 0
end

/-! ## Ground observations survive every run -/

/-- Every name whose value is ground keeps it. -/
def KeepsGround (σ τ : Substitution) : Prop := ∀ x, support (σ x) = ∅ → τ x = σ x

theorem KeepsGround.refl (σ : Substitution) : KeepsGround σ σ := fun _ _ => rfl

theorem KeepsGround.trans {σ τ υ : Substitution} (first : KeepsGround σ τ)
    (second : KeepsGround τ υ) : KeepsGround σ υ := by
  intro x ground
  rw [second x (by rw [first x ground]; exact ground), first x ground]

theorem KeepsGround.bind {σ τ : Substitution} {p : Pat} {value : Atom}
    (bound : bindPattern σ p value = some τ) : KeepsGround σ τ :=
  fun x ground => ground_observation_preserved bound x ground

theorem substA_congr {σ τ : Substitution} (a : Atom) :
    (∀ x ∈ support a, σ x = τ x) → substA σ a = substA τ a := by
  induction a using Atom.rec (motive_2 := fun values => ∀ a ∈ values,
      (∀ x ∈ support a, σ x = τ x) → substA σ a = substA τ a) with
  | var name =>
      intro same
      exact same name (by simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars])
  | symbol _ => intro _; rfl
  | grounded _ => intro _; rfl
  | expression values ih =>
      intro same
      rw [substA, substA, UnifyAtoms.substL_eq_map, UnifyAtoms.substL_eq_map]
      congr 1
      apply List.map_congr_left
      intro a member
      exact ih a member fun x occurs => same x ((support_expression values x).mpr ⟨a, member, occurs⟩)
  | nil a member => cases member
  | cons first rest ihFirst ihRest a member same =>
      rcases List.mem_cons.mp member with rfl | present
      · exact ihFirst same
      · exact ihRest a present same

/-- A recipe whose observation is ground keeps it. -/
theorem KeepsGround.observe {σ τ : Substitution} (keeps : KeepsGround σ τ) {a : Atom}
    (ground : support (substA σ a) = ∅) : substA τ a = substA σ a := by
  apply substA_congr
  intro x occurs
  apply keeps x
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y present
  have escaped := (support_subst σ a y).mpr ⟨x, occurs, present⟩
  rw [ground] at escaped
  exact Finset.notMem_empty y escaped

mutual
theorem eval_keeps (E : Env) (O : Oracle) :
    ∀ (e : Expr) (σ : Substitution), ∀ out ∈ eval E O e σ, KeepsGround σ out.2
  | .var _, σ, out, member => by
      simp only [eval, Multiset.mem_singleton] at member
      subst member
      exact KeepsGround.refl σ
  | .const _, σ, out, member => by
      simp only [eval, Multiset.mem_singleton] at member
      subst member
      exact KeepsGround.refl σ
  | .ctor _ args, σ, out, member => by
      simp only [eval, Multiset.mem_map] at member
      obtain ⟨values, present, rfl⟩ := member
      exact evalAll_keeps E O args σ values present
  | .self args, σ, out, member => by
      simp only [eval, Multiset.mem_bind, Multiset.mem_map] at member
      obtain ⟨values, present, _, _, rfl⟩ := member
      exact evalAll_keeps E O args σ values present
  | .prim _ args, σ, out, member => by
      simp only [eval, Multiset.mem_bind, Multiset.mem_map] at member
      obtain ⟨values, present, _, _, rfl⟩ := member
      exact evalAll_keeps E O args σ values present
  | .call _ args, σ, out, member => by
      simp only [eval, Multiset.mem_bind, Multiset.mem_map] at member
      obtain ⟨values, present, _, _, rfl⟩ := member
      exact evalAll_keeps E O args σ values present
  | .enter _ args, σ, out, member => by
      simp only [eval, Multiset.mem_bind, Multiset.mem_map] at member
      obtain ⟨values, present, _, _, rfl⟩ := member
      exact evalAll_keeps E O args σ values present
  | .letE p val body, σ, out, member => by
      simp only [eval, Multiset.mem_bind] at member
      obtain ⟨first, present, member⟩ := member
      have before := eval_keeps E O val σ first present
      cases bound : bindPattern first.2 p first.1 with
      | none => simp [bound] at member
      | some τ =>
          rw [bound] at member
          exact before.trans ((KeepsGround.bind bound).trans (eval_keeps E O body τ out member))
  | .ifE c t e, σ, out, member => by
      simp only [eval, Multiset.mem_bind] at member
      obtain ⟨first, present, member⟩ := member
      have before := eval_keeps E O c σ first present
      split at member
      · exact before.trans (eval_keeps E O t first.2 out member)
      · exact before.trans (eval_keeps E O e first.2 out member)
  | .empty, _, out, member => by simp [eval] at member
  | .caseE key pats bodies, σ, out, member => by
      simp only [eval, Multiset.mem_bind] at member
      obtain ⟨first, present, member⟩ := member
      exact (eval_keeps E O key σ first present).trans
        (evalArms_keeps E O first.2 first.1 pats bodies out member)
  | .matchE src p t, σ, out, member => by
      simp only [eval, Multiset.mem_bind] at member
      obtain ⟨first, present, row, _, member⟩ := member
      have before := eval_keeps E O src σ first present
      cases bound : bindPattern first.2 p row with
      | none => simp [bound] at member
      | some τ =>
          rw [bound] at member
          exact before.trans ((KeepsGround.bind bound).trans (eval_keeps E O t τ out member))

theorem evalAll_keeps (E : Env) (O : Oracle) :
    ∀ (es : List Expr) (σ : Substitution), ∀ out ∈ evalAll E O es σ, KeepsGround σ out.2
  | [], σ, out, member => by
      simp only [evalAll, Multiset.mem_singleton] at member
      subst member
      exact KeepsGround.refl σ
  | e :: es, σ, out, member => by
      simp only [evalAll, Multiset.mem_bind, Multiset.mem_map] at member
      obtain ⟨first, present, rest, restPresent, rfl⟩ := member
      exact (eval_keeps E O e σ first present).trans (evalAll_keeps E O es first.2 rest restPresent)

theorem evalArms_keeps (E : Env) (O : Oracle) (σ : Substitution) (key : Atom) :
    ∀ (ps : List Pat) (bs : List Expr), ∀ out ∈ evalArms E O σ key ps bs, KeepsGround σ out.2
  | p :: ps, b :: bs, out, member => by
      simp only [evalArms] at member
      split at member
      · next τ bound => exact (KeepsGround.bind bound).trans (eval_keeps E O b τ out member)
      · exact evalArms_keeps E O σ key ps bs out member
  | [], _, out, member => by simp [evalArms] at member
  | _ :: _, [], out, member => by simp [evalArms] at member
end

/-! ## The analysis's facts -/

mutual
/-- The variables of an atom, each occurrence in order (`contract_mark`'s walk). -/
def atomVars : Atom → List String
  | .var x => [x]
  | .symbol _ => []
  | .grounded _ => []
  | .expression values => atomVarsAll values

def atomVarsAll : List Atom → List String
  | [] => []
  | a :: rest => atomVars a ++ atomVarsAll rest
end

theorem mem_atomVars {x : String} (a : Atom) : x ∈ atomVars a ↔ x ∈ support a := by
  induction a using Atom.rec (motive_2 := fun values =>
      (x ∈ atomVarsAll values ↔ ∃ a ∈ values, x ∈ support a)) with
  | var name => simp [atomVars, support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars]
  | symbol _ => simp [atomVars, support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars]
  | grounded _ => simp [atomVars, support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars]
  | expression values ih => rw [atomVars, ih, support_expression]
  | nil => simp [atomVarsAll]
  | cons first rest ihFirst ihRest =>
      rw [atomVarsAll, List.mem_append, ihFirst, ihRest]
      constructor
      · rintro (occurs | ⟨a, present, occurs⟩)
        · exact ⟨first, by simp, occurs⟩
        · exact ⟨a, by simp [present], occurs⟩
      · rintro ⟨a, present, occurs⟩
        rcases List.mem_cons.mp present with rfl | present
        · exact Or.inl occurs
        · exact Or.inr ⟨a, present, occurs⟩

/-- A name's cell after a mark: the C ORs the new flags into the old. -/
def mergeInto : Option Flags → Flags → Flags
  | none, new => new
  | some old, new => mergeFlags old new

/-- Mark one name, newest first, so `lookup` reads the merged cell. -/
def markVar (F : Facts) (x : String) (flags : Flags) : Facts :=
  (x, mergeInto (F.lookup x) flags) :: F

def markVars (F : Facts) (xs : List String) (flags : Flags) : Facts :=
  xs.foldl (fun F x => markVar F x flags) F

/-- `contract_mark`: every variable of a pattern takes the flags. -/
def markPat (F : Facts) (p : Pat) (flags : Flags) : Facts := markVars F (atomVars p.toAtom) flags

theorem lookup_markVar (F : Facts) (x : String) (flags : Flags) (y : String) :
    (markVar F x flags).lookup y = if y = x then some (mergeInto (F.lookup x) flags) else F.lookup y := by
  by_cases same : y = x
  · subst y
    simp [markVar]
  · rw [if_neg same]
    simp only [markVar, List.lookup]
    rw [beq_false_of_ne same]

theorem mergeInto_idem (old : Option Flags) (flags : Flags) :
    mergeInto (some (mergeInto old flags)) flags = mergeInto old flags := by
  cases old with
  | none => cases flags; simp [mergeInto, mergeFlags]
  | some old => cases old; cases flags; simp [mergeInto, mergeFlags]

theorem lookup_markVars (flags : Flags) (y : String) :
    ∀ (xs : List String) (F : Facts), (markVars F xs flags).lookup y =
      if y ∈ xs then some (mergeInto (F.lookup y) flags) else F.lookup y
  | [], F => by simp [markVars]
  | x :: xs, F => by
      have step : markVars F (x :: xs) flags = markVars (markVar F x flags) xs flags := rfl
      rw [step, lookup_markVars flags y xs (markVar F x flags), lookup_markVar]
      by_cases here : y = x
      · subst y
        by_cases later : x ∈ xs <;> simp [later, mergeInto_idem]
      · by_cases later : y ∈ xs <;> simp [here, later]

theorem lookup_markPat (F : Facts) (p : Pat) (flags : Flags) (y : String) :
    (markPat F p flags).lookup y =
      if y ∈ support p.toAtom then some (mergeInto (F.lookup y) flags) else F.lookup y := by
  rw [markPat, lookup_markVars]
  simp only [mem_atomVars]

/-- The facts that claim groundness hold, each with its uninterpreted claim.
Open claims are not part of this invariant: no binding the analysis checks
can be relied on to keep them, and the ground rule never needs them. -/
def GroundSound (Γ : Decls) (σ : Substitution) (F : Facts) : Prop :=
  ∀ x flags, F.lookup x = some flags → flags.ground = true →
    support (σ x) = ∅ ∧ (flags.uninterpreted = true → Uninterp Γ (σ x))

theorem GroundSound.keep {Γ : Decls} {σ τ : Substitution} {F : Facts}
    (sound : GroundSound Γ σ F) (keeps : KeepsGround σ τ) : GroundSound Γ τ F := by
  intro x flags found ground
  obtain ⟨isGround, clean⟩ := sound x flags found ground
  rw [keeps x isGround]
  exact ⟨isGround, clean⟩

theorem GroundSound.nil (Γ : Decls) (σ : Substitution) : GroundSound Γ σ [] := by
  intro x flags found
  simp at found

/-! ### What the C's two binding tests say about names -/

mutual
theorem patternUninterpreted_names {Γ : Decls} {F : Facts} :
    ∀ a : Atom, patternUninterpreted Γ F a = true →
      ∀ x ∈ support a, ∀ flags, F.lookup x = some flags → flags.uninterpreted = true
  | .var name, checked, x, occurs, flags, found => by
      have same : x = name := by
        simpa [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars] using occurs
      subst x
      simpa [patternUninterpreted, found] using checked
  | .symbol _, _, x, occurs, _, _ => by
      simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars] at occurs
  | .grounded _, _, x, occurs, _, _ => by
      simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars] at occurs
  | .expression values, checked, x, occurs, flags, found => by
      obtain ⟨a, present, occurs⟩ := (support_expression values x).mp occurs
      exact patternsUninterpreted_names values (by simpa [patternUninterpreted] using checked)
        a present x occurs flags found

theorem patternsUninterpreted_names {Γ : Decls} {F : Facts} :
    ∀ values : List Atom, patternsUninterpreted Γ F values = true →
      ∀ a ∈ values, ∀ x ∈ support a, ∀ flags, F.lookup x = some flags → flags.uninterpreted = true
  | [], _, _, member, _, _, _, _ => by cases member
  | first :: rest, checked, a, member, x, occurs, flags, found => by
      have parts := Bool.and_eq_true_iff.mp (by simpa [patternsUninterpreted] using checked)
      rcases List.mem_cons.mp member with same | present
      · exact patternUninterpreted_names first parts.1 x (same ▸ occurs) flags found
      · exact patternsUninterpreted_names rest parts.2 a present x occurs flags found
end

mutual
theorem patternKeepsClaims_names {F : Facts} :
    ∀ a : Atom, patternKeepsClaims F a = true →
      ∀ x ∈ support a, ∀ flags, F.lookup x = some flags →
        flags.uninterpreted = true → flags.ground = true
  | .var name, checked, x, occurs, flags, found, open_ => by
      have same : x = name := by
        simpa [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars] using occurs
      subst x
      simp only [patternKeepsClaims, found, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
        Bool.not_true] at checked
      rcases checked with ground | closed
      · exact ground
      · rw [open_] at closed
        cases closed
  | .symbol _, _, x, occurs, _, _, _ => by
      simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars] at occurs
  | .grounded _, _, x, occurs, _, _, _ => by
      simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars] at occurs
  | .expression values, checked, x, occurs, flags, found, open_ => by
      obtain ⟨a, present, occurs⟩ := (support_expression values x).mp occurs
      exact patternsKeepClaims_names values (by simpa [patternKeepsClaims] using checked)
        a present x occurs flags found open_

theorem patternsKeepClaims_names {F : Facts} :
    ∀ values : List Atom, patternsKeepClaims F values = true →
      ∀ a ∈ values, ∀ x ∈ support a, ∀ flags, F.lookup x = some flags →
        flags.uninterpreted = true → flags.ground = true
  | [], _, _, member, _, _, _, _, _ => by cases member
  | first :: rest, checked, a, member, x, occurs, flags, found, open_ => by
      have parts := Bool.and_eq_true_iff.mp (by simpa [patternsKeepClaims] using checked)
      rcases List.mem_cons.mp member with same | present
      · exact patternKeepsClaims_names first parts.1 x (same ▸ occurs) flags found open_
      · exact patternsKeepClaims_names rest parts.2 a present x occurs flags found open_
end


/-! ## The analysis -/

/-- The entry fact of a parameter: ANY (an unguarded formal), or the
polymorphic UNINTERPRETED one shared with the result. -/
inductive Position where
  | any
  | uninterpreted
  deriving DecidableEq

/-- How a version admits a value at its polymorphic parameter. -/
inductive Rule where
  /-- Before the alias fix: uninterpreted, open or not. -/
  | unchecked
  /-- Ground and uninterpreted. -/
  | ground
  /-- Uninterpreted, and ground or every other value ground. -/
  | refined
  deriving DecidableEq

/-- The flags `contract_equation` gives the polymorphic pattern's variables. -/
def Rule.entryFlags : Rule → Flags
  | .ground => ⟨true, true⟩
  | _ => ⟨false, true⟩

def bottomValue : ValueFlags := ⟨⟨false, false⟩, true⟩

def anyBottom (vs : List ValueFlags) : Bool := vs.any (·.bottom)

/-- Every value but the polymorphic one is ground (`contract_others_ground`). -/
def othersGround (ps : List Position) (vs : List ValueFlags) : Bool :=
  (ps.zip vs).all fun qv => qv.1 == .uninterpreted || qv.2.ground

/-- One position's test, given whether the other values are ground. -/
def meetsOne (rule : Rule) (others : Bool) : Position → ValueFlags → Bool
  | .any, _ => true
  | .uninterpreted, v => v.uninterpreted && match rule with
      | .unchecked => true
      | .ground => v.ground
      | .refined => v.ground || others

/-- `contract_meets_version` and `contract_self_call` at the version's positions. -/
def meets (rule : Rule) (ps : List Position) (vs : List ValueFlags) : Bool :=
  ps.length == vs.length &&
    (ps.zip vs).all fun pv => meetsOne rule (othersGround ps vs) pv.1 pv.2

/-- The flags of the value at the polymorphic position: what a version's
call answers (`contract_call`'s polymorphic pair, `contract_self_call`). -/
def activeFlags : List Position → List ValueFlags → Flags
  | .uninterpreted :: _, v :: _ => v.toFlags
  | .any :: ps, _ :: vs => activeFlags ps vs
  | _, _ => ⟨false, false⟩

/-- A variable's value: its fact, or, with none, uninterpreted and open. -/
def varValue (F : Facts) (x : String) : ValueFlags :=
  match F.lookup x with
  | some flags => ⟨flags, false⟩
  | none => ⟨⟨false, true⟩, false⟩

mutual
/-- `contract_eval` of data written as an atom. -/
def atomFlags (Γ : Decls) (F : Facts) : Atom → Flags
  | .var x => (varValue F x).toFlags
  | .symbol s => ⟨true, (Γ s).isEmpty⟩
  | .grounded _ => ⟨true, true⟩
  | .expression values => atomsFlags Γ F values

def atomsFlags (Γ : Decls) (F : Facts) : List Atom → Flags
  | [] => ⟨true, true⟩
  | a :: rest => ⟨(atomFlags Γ F a).ground && (atomsFlags Γ F rest).ground,
      (atomFlags Γ F a).uninterpreted && (atomsFlags Γ F rest).uninterpreted⟩
end

def dataValue (Γ : Decls) (c : String) (vs : List ValueFlags) : ValueFlags :=
  if anyBottom vs then bottomValue
  else ⟨⟨vs.all (·.ground), (Γ c).isEmpty && vs.all (·.uninterpreted)⟩, false⟩

def primValue (vs : List ValueFlags) : ValueFlags :=
  if anyBottom vs then bottomValue else ⟨⟨true, false⟩, false⟩

def keptValue (vs : List ValueFlags) : ValueFlags :=
  if anyBottom vs then bottomValue else ⟨⟨false, false⟩, false⟩

def callValue (ps : List Position) (vs : List ValueFlags) : ValueFlags :=
  if anyBottom vs then bottomValue else ⟨activeFlags ps vs, false⟩

/-- `contract_join`. -/
def join (a b : ValueFlags) : ValueFlags :=
  if a.bottom then b
  else if b.bottom then a
  else ⟨⟨a.ground && b.ground, a.uninterpreted && b.uninterpreted⟩, false⟩

/-- What the analysis knows of the program: the analysed relation's positions,
the positions of the versions other relations offer, and the operations PeTTa
provides (`contract_pure_operation`). -/
structure Program where
  positions : List Position
  versions : String → Option (List Position)
  prim : String → ℕ → Bool

/-- `contract_bind_any`: an uninterpreted value into an uninterpreted pattern
marks its variables uninterpreted, ground where the value is; otherwise a value
that is ground or claims nothing, into a pattern none of whose variables claims
to be uninterpreted while open, marks them ground where the value is. -/
inductive BindAny (Γ : Decls) (F : Facts) (p : Pat) (v : ValueFlags) : Facts → Prop
  | clean : v.uninterpreted = true → patternUninterpreted Γ F p.toAtom = true →
      BindAny Γ F p v (markPat F p ⟨v.ground, true⟩)
  | keeps : (v.uninterpreted = true → v.ground = true) → patternKeepsClaims F p.toAtom = true →
      BindAny Γ F p v (markPat F p ⟨v.ground && !v.bottom, false⟩)

/-- A call's arguments meet the version's facts, or one has no answer. -/
def Discharges (rule : Rule) (ps : List Position) (vs : List ValueFlags) : Prop :=
  anyBottom vs = true ∨ meets rule ps vs = true

mutual
/-- **The analysis** (`contract_eval`), from the facts before an occurrence to
its value and the facts after it. A branch's facts are dropped after it
(`contract_facts_restore`). -/
inductive Admits (Γ : Decls) (rule : Rule) (P : Program) : Facts → Expr → ValueFlags → Facts → Prop
  | var (F : Facts) (x : String) : Admits Γ rule P F (.var x) (varValue F x) F
  | const (F : Facts) (a : Atom) : Admits Γ rule P F (.const a) ⟨atomFlags Γ F a, false⟩ F
  | ctor {F F' : Facts} {c : String} {args : List Expr} {vs : List ValueFlags} :
      AdmitsAll Γ rule P F args vs F' → Admits Γ rule P F (.ctor c args) (dataValue Γ c vs) F'
  | self {F F' : Facts} {args : List Expr} {vs : List ValueFlags} :
      AdmitsAll Γ rule P F args vs F' → Discharges rule P.positions vs →
      Admits Γ rule P F (.self args) (callValue P.positions vs) F'
  | prim {F F' : Facts} {op : String} {args : List Expr} {vs : List ValueFlags} :
      AdmitsAll Γ rule P F args vs F' → P.prim op args.length = true →
      Admits Γ rule P F (.prim op args) (primValue vs) F'
  | call {F F' : Facts} {f : String} {args : List Expr} {vs : List ValueFlags} :
      AdmitsAll Γ rule P F args vs F' → Admits Γ rule P F (.call f args) (keptValue vs) F'
  | enter {F F' : Facts} {f : String} {args : List Expr} {vs : List ValueFlags}
      {ps : List Position} :
      AdmitsAll Γ rule P F args vs F' → P.versions f = some ps → Discharges rule ps vs →
      Admits Γ rule P F (.enter f args) (callValue ps vs) F'
  | letBottom {F F' : Facts} {p : Pat} {val body : Expr} {vv : ValueFlags} :
      Admits Γ rule P F val vv F' → vv.bottom = true → Admits Γ rule P F (.letE p val body) vv F'
  | letE {F F₁ F₂ F₃ : Facts} {p : Pat} {val body : Expr} {vv bv : ValueFlags} :
      Admits Γ rule P F val vv F₁ → vv.bottom = false → BindAny Γ F₁ p vv F₂ →
      Admits Γ rule P F₂ body bv F₃ → Admits Γ rule P F (.letE p val body) bv F₃
  | ifE {F F₁ Ft Fe : Facts} {c t e : Expr} {cv tv ev : ValueFlags} :
      Admits Γ rule P F c cv F₁ → Admits Γ rule P F₁ t tv Ft → Admits Γ rule P F₁ e ev Fe →
      Admits Γ rule P F (.ifE c t e) (join tv ev) F₁
  | empty (F : Facts) : Admits Γ rule P F .empty bottomValue F
  | caseBottom {F F₁ : Facts} {key : Expr} {ps : List Pat} {bs : List Expr} {kv : ValueFlags} :
      Admits Γ rule P F key kv F₁ → kv.bottom = true → Admits Γ rule P F (.caseE key ps bs) kv F₁
  | caseE {F F₁ : Facts} {key : Expr} {ps : List Pat} {bs : List Expr} {kv v : ValueFlags} :
      Admits Γ rule P F key kv F₁ → kv.bottom = false → AdmitsArms Γ rule P F₁ kv ps bs v →
      Admits Γ rule P F (.caseE key ps bs) v F₁
  | matchE {F F₁ F₂ : Facts} {src t : Expr} {p : Pat} {sv tv : ValueFlags} :
      Admits Γ rule P F src sv F₁ → patternUninterpreted Γ F₁ p.toAtom = true →
      Admits Γ rule P (markPat F₁ p ⟨false, true⟩) t tv F₂ →
      Admits Γ rule P F (.matchE src p t) tv F₂

/-- Arguments, left to right. -/
inductive AdmitsAll (Γ : Decls) (rule : Rule) (P : Program) :
    Facts → List Expr → List ValueFlags → Facts → Prop
  | nil (F : Facts) : AdmitsAll Γ rule P F [] [] F
  | cons {F F₁ F₂ : Facts} {e : Expr} {es : List Expr} {v : ValueFlags} {vs : List ValueFlags} :
      Admits Γ rule P F e v F₁ → AdmitsAll Γ rule P F₁ es vs F₂ →
      AdmitsAll Γ rule P F (e :: es) (v :: vs) F₂

/-- The arms of a `case`, each from the facts after the key (`contract_case`). -/
inductive AdmitsArms (Γ : Decls) (rule : Rule) (P : Program) :
    Facts → ValueFlags → List Pat → List Expr → ValueFlags → Prop
  | nil (F : Facts) (kv : ValueFlags) : AdmitsArms Γ rule P F kv [] [] bottomValue
  | cons {F F₂ F₃ : Facts} {kv : ValueFlags} {p : Pat} {ps : List Pat} {b : Expr} {bs : List Expr}
      {bv rest : ValueFlags} :
      BindAny Γ F p kv F₂ → Admits Γ rule P F₂ b bv F₃ → AdmitsArms Γ rule P F kv ps bs rest →
      AdmitsArms Γ rule P F kv (p :: ps) (b :: bs) (join bv rest)
end

/-! ## Soundness of the ground facts -/

/-- A value's flags hold of an outcome: it has an answer, and where it claims
ground, the observation is ground, uninterpreted where it claims that too. -/
def Faithful (Γ : Decls) (out : Outcome) (v : ValueFlags) : Prop :=
  v.bottom = false ∧ (v.ground = true → support (substA out.2 out.1) = ∅ ∧
    (v.uninterpreted = true → Uninterp Γ (substA out.2 out.1)))

def ArgsFaithful (Γ : Decls) (σ : Substitution) (as : List Atom) (vs : List ValueFlags) : Prop :=
  List.Forall₂ (fun a v => Faithful Γ (a, σ) v) as vs

/-- Arguments a version admits under the ground rule. -/
def Admitted (Γ : Decls) (ps : List Position) (ws : List Atom) : Prop :=
  List.Forall₂ (fun p w => p = .uninterpreted → support w = ∅ ∧ Uninterp Γ w) ps ws

/-- `r` is the argument at the polymorphic position. -/
def ActiveIs (ps : List Position) (ws : List Atom) (r : Atom) : Prop :=
  List.Forall₂ (fun p w => p = .uninterpreted → r = w) ps ws

/-- What a run's calls answer at arguments meeting the facts: a version's
answers are the argument at its polymorphic position; PeTTa's operations
answer ground values. -/
structure OraclesOK (Γ : Decls) (P : Program) (E : Env) (O : Oracle) : Prop where
  self : ∀ ws, Admitted Γ P.positions ws → ∀ r ∈ O.self ws, ActiveIs P.positions ws r
  enter : ∀ f ps, P.versions f = some ps → ∀ ws, Admitted Γ ps ws →
    ∀ r ∈ O.enter f ws, ActiveIs ps ws r
  prim : ∀ op ws, P.prim op ws.length = true → ∀ r ∈ E.prim op ws, support r = ∅

theorem Faithful.keep {Γ : Decls} {σ τ : Substitution} {a : Atom} {v : ValueFlags}
    (faithful : Faithful Γ (a, σ) v) (keeps : KeepsGround σ τ) : Faithful Γ (a, τ) v := by
  refine ⟨faithful.1, fun ground => ?_⟩
  obtain ⟨isGround, clean⟩ := faithful.2 ground
  change support (substA τ a) = ∅ ∧ (v.uninterpreted = true → Uninterp Γ (substA τ a))
  rw [keeps.observe isGround]
  exact ⟨isGround, clean⟩

theorem ArgsFaithful.keep {Γ : Decls} {σ τ : Substitution} {as : List Atom} {vs : List ValueFlags}
    (faithful : ArgsFaithful Γ σ as vs) (keeps : KeepsGround σ τ) : ArgsFaithful Γ τ as vs :=
  faithful.imp fun _ _ each => each.keep keeps

theorem ArgsFaithful.anyBottom_false {Γ : Decls} {σ : Substitution} :
    ∀ {as : List Atom} {vs : List ValueFlags}, ArgsFaithful Γ σ as vs → anyBottom vs = false
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons first rest => by
      simp only [anyBottom, List.any_cons, Bool.or_eq_false_iff]
      exact ⟨first.1, ArgsFaithful.anyBottom_false rest⟩

theorem faithful_join_left {Γ : Decls} {out : Outcome} {a : ValueFlags} (b : ValueFlags)
    (faithful : Faithful Γ out a) : Faithful Γ out (join a b) := by
  obtain ⟨notBottom, claims⟩ := faithful
  unfold join
  rw [if_neg (by simp [notBottom])]
  split
  · exact ⟨notBottom, claims⟩
  · refine ⟨rfl, fun ground => ?_⟩
    have both := Bool.and_eq_true_iff.mp ground
    obtain ⟨isGround, clean⟩ := claims both.1
    exact ⟨isGround, fun unint => clean (Bool.and_eq_true_iff.mp unint).1⟩

theorem faithful_join_right {Γ : Decls} {out : Outcome} (a : ValueFlags) {b : ValueFlags}
    (faithful : Faithful Γ out b) : Faithful Γ out (join a b) := by
  obtain ⟨notBottom, claims⟩ := faithful
  unfold join
  split
  · exact ⟨notBottom, claims⟩
  · rw [if_neg (by simp [notBottom])]
    refine ⟨rfl, fun ground => ?_⟩
    have both := Bool.and_eq_true_iff.mp ground
    obtain ⟨isGround, clean⟩ := claims both.2
    exact ⟨isGround, fun unint => clean (Bool.and_eq_true_iff.mp unint).2⟩

/-- An atom whose variables map to uninterpreted values, itself uninterpreted. -/
theorem uninterp_substA_on {Γ : Decls} {σ : Substitution} {a : Atom} (clean : Uninterp Γ a)
    (values : ∀ x ∈ support a, Uninterp Γ (σ x)) : Uninterp Γ (substA σ a) := by
  classical
  let θ : Substitution := fun x => if x ∈ support a then σ x else .var x
  have same : substA θ a = substA σ a := substA_congr a fun x occurs => by simp [θ, occurs]
  rw [← same]
  apply uninterp_substA _ a clean
  intro x
  by_cases occurs : x ∈ support a
  · simpa [θ, occurs] using values x occurs
  · simp only [θ, occurs, if_false]
    trivial

mutual
/-- Data written as an atom: its ground flag and uninterpreted flag hold. -/
theorem atomFlags_sound {Γ : Decls} {σ : Substitution} {F : Facts} (sound : GroundSound Γ σ F) :
    ∀ a : Atom, (atomFlags Γ F a).ground = true →
      (∀ x ∈ support a, support (σ x) = ∅) ∧
        ((atomFlags Γ F a).uninterpreted = true → Uninterp Γ a ∧ ∀ x ∈ support a, Uninterp Γ (σ x))
  | .var name, ground => by
      have occurs : ∀ x ∈ support (Atom.var name), x = name := by
        intro x occurs
        simpa [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars] using occurs
      cases found : F.lookup name with
      | none => simp [atomFlags, varValue, found] at ground
      | some flags =>
          have g : flags.ground = true := by simpa [atomFlags, varValue, found] using ground
          obtain ⟨isGround, clean⟩ := sound name flags found g
          refine ⟨fun x present => by rw [occurs x present]; exact isGround, fun unint => ?_⟩
          have u : flags.uninterpreted = true := by simpa [atomFlags, varValue, found] using unint
          exact ⟨trivial, fun x present => by rw [occurs x present]; exact clean u⟩
  | .symbol s, _ => by
      have none : ∀ x, x ∉ support (Atom.symbol s) := by
        intro x occurs
        simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars] at occurs
      refine ⟨fun x occurs => absurd occurs (none x), fun unint => ?_⟩
      exact ⟨List.isEmpty_iff.mp (by simpa [atomFlags] using unint),
        fun x occurs => absurd occurs (none x)⟩
  | .grounded g, _ => by
      have none : ∀ x, x ∉ support (Atom.grounded g) := by
        intro x occurs
        simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars] at occurs
      exact ⟨fun x occurs => absurd occurs (none x),
        fun _ => ⟨trivial, fun x occurs => absurd occurs (none x)⟩⟩
  | .expression values, ground => by
      obtain ⟨grounds, cleans⟩ := atomsFlags_sound sound values (by simpa [atomFlags] using ground)
      refine ⟨fun x occurs => ?_, fun unint => ?_⟩
      · obtain ⟨a, present, occurs⟩ := (support_expression values x).mp occurs
        exact grounds a present x occurs
      · obtain ⟨each, images⟩ := cleans (by simpa [atomFlags] using unint)
        refine ⟨UnifyAtoms.uninterp_of_all each, fun x occurs => ?_⟩
        obtain ⟨a, present, occurs⟩ := (support_expression values x).mp occurs
        exact images a present x occurs

theorem atomsFlags_sound {Γ : Decls} {σ : Substitution} {F : Facts} (sound : GroundSound Γ σ F) :
    ∀ values : List Atom, (atomsFlags Γ F values).ground = true →
      (∀ a ∈ values, ∀ x ∈ support a, support (σ x) = ∅) ∧
        ((atomsFlags Γ F values).uninterpreted = true →
          (∀ a ∈ values, Uninterp Γ a) ∧ ∀ a ∈ values, ∀ x ∈ support a, Uninterp Γ (σ x))
  | [], _ => by
      refine ⟨fun _ member => ?_, fun _ => ⟨fun _ member => ?_, fun _ member => ?_⟩⟩ <;> cases member
  | first :: rest, ground => by
      have g := Bool.and_eq_true_iff.mp (by simpa [atomsFlags] using ground)
      obtain ⟨firstGround, firstClean⟩ := atomFlags_sound sound first g.1
      obtain ⟨restGround, restClean⟩ := atomsFlags_sound sound rest g.2
      refine ⟨fun a member => ?_, fun unint => ?_⟩
      · rcases List.mem_cons.mp member with same | present
        · rw [same]; exact firstGround
        · exact restGround a present
      · have u := Bool.and_eq_true_iff.mp (by simpa [atomsFlags] using unint)
        obtain ⟨firstData, firstImages⟩ := firstClean u.1
        obtain ⟨restData, restImages⟩ := restClean u.2
        refine ⟨fun a member => ?_, fun a member => ?_⟩
        · rcases List.mem_cons.mp member with same | present
          · rw [same]; exact firstData
          · exact restData a present
        · rcases List.mem_cons.mp member with same | present
          · rw [same]; exact firstImages
          · exact restImages a present
end

theorem const_faithful {Γ : Decls} {σ : Substitution} {F : Facts} (sound : GroundSound Γ σ F)
    (a : Atom) : Faithful Γ (a, σ) ⟨atomFlags Γ F a, false⟩ := by
  refine ⟨rfl, fun ground => ?_⟩
  obtain ⟨grounds, cleans⟩ := atomFlags_sound sound a ground
  refine ⟨Finset.eq_empty_iff_forall_notMem.mpr fun y present => ?_, fun unint => ?_⟩
  · obtain ⟨x, occurs, image⟩ := (support_subst σ a y).mp present
    rw [grounds x occurs] at image
    exact Finset.notMem_empty y image
  · obtain ⟨clean, images⟩ := cleans unint
    exact uninterp_substA_on clean images

/-- **Binding keeps the ground facts** (`contract_bind_any`). A fact claiming
ground either is older, and ground observations never change, or is new, and
then the value was ground, so every pattern variable now names a part of it;
the C's two tests forbid the one merge that would claim an uninterpreted
ground value from an open claim. -/
theorem bindAny_sound {Γ : Decls} {F F₂ : Facts} {p : Pat} {v : ValueFlags}
    {σ τ : Substitution} {a : Atom} (bind : BindAny Γ F p v F₂) (sound : GroundSound Γ σ F)
    (faithful : Faithful Γ (a, σ) v) (bound : bindPattern σ p a = some τ) :
    GroundSound Γ τ F₂ := by
  have keeps := KeepsGround.bind bound
  have old := sound.keep keeps
  -- a value claimed ground makes every pattern variable a ground part of it
  have parts : v.ground = true → ∀ y ∈ support p.toAtom, support (τ y) = ∅ ∧
      (v.uninterpreted = true → Uninterp Γ (τ y)) := by
    intro g y occurs
    obtain ⟨isGround, clean⟩ := faithful.2 g
    refine ⟨ground_pattern_marks bound isGround y occurs, fun u => ?_⟩
    have equation : substA τ p.toAtom = substA σ a := by
      rw [bindPattern_equation bound, keeps.observe isGround]
    exact uninterpreted_substituted_variable τ p.toAtom (equation ▸ clean u) y occurs
  cases bind with
  | clean unint patternClean =>
      intro y flags found ground
      rw [lookup_markPat] at found
      split at found
      · next occurs =>
          cases v with
          | mk base bottom =>
          cases base with
          | mk vg vu =>
          cases vg with
          | true => exact parts rfl y occurs |>.imp_right fun c _ => c unint
          | false =>
              cases oldFound : F.lookup y with
              | none => simp [oldFound, mergeInto] at found; subst found; simp at ground
              | some o =>
                  simp only [oldFound, mergeInto, Option.some.injEq] at found
                  subst found
                  have og : o.ground = true := by simpa [mergeFlags] using ground
                  have ou := patternUninterpreted_names _ patternClean y occurs o oldFound
                  obtain ⟨isGround, clean⟩ := old y o oldFound og
                  exact ⟨isGround, fun _ => clean ou⟩
      · exact old y flags found ground
  | keeps closedOrGround keepsClaims =>
      intro y flags found ground
      rw [lookup_markPat] at found
      split at found
      · next occurs =>
          cases oldFound : F.lookup y with
          | none =>
              simp only [oldFound, mergeInto, Option.some.injEq] at found
              subst found
              have g : v.ground = true := (Bool.and_eq_true_iff.mp ground).1
              exact ⟨(parts g y occurs).1, fun u => by cases u⟩
          | some o =>
              simp only [oldFound, mergeInto, Option.some.injEq] at found
              subst found
              simp only [mergeFlags, Bool.or_eq_true, Bool.or_false] at ground ⊢
              by_cases og : o.ground = true
              · obtain ⟨isGround, clean⟩ := old y o oldFound og
                exact ⟨isGround, clean⟩
              · have g : v.ground = true := by
                  rcases ground with h | h
                  · exact absurd h og
                  · exact (Bool.and_eq_true_iff.mp h).1
                refine ⟨(parts g y occurs).1, fun u => ?_⟩
                have := patternKeepsClaims_names _ keepsClaims y occurs o oldFound u
                exact absurd this og
      · exact old y flags found ground


theorem meets_iff (rule : Rule) (ps : List Position) (vs : List ValueFlags) :
    meets rule ps vs = true ↔
      List.Forall₂ (fun p v => meetsOne rule (othersGround ps vs) p v = true) ps vs := by
  rw [List.forall₂_iff_zip]
  simp only [meets, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  constructor
  · rintro ⟨len, each⟩
    exact ⟨len, fun member => each _ member⟩
  · rintro ⟨len, each⟩
    exact ⟨len, fun pv member => each member⟩

theorem evalAll_length (E : Env) (O : Oracle) : ∀ (es : List Expr) (σ : Substitution),
    ∀ out ∈ evalAll E O es σ, out.1.length = es.length
  | [], σ, out, member => by
      simp only [evalAll, Multiset.mem_singleton] at member
      subst member
      rfl
  | e :: es, σ, out, member => by
      simp only [evalAll, Multiset.mem_bind, Multiset.mem_map] at member
      obtain ⟨first, _, rest, restPresent, rfl⟩ := member
      simp [evalAll_length E O es first.2 rest restPresent]

/-- Values meeting a version's facts under the ground rule are arguments it admits. -/
theorem admitted_of_meets {Γ : Decls} {τ : Substitution} {others : Bool} {ps : List Position}
    {vs : List ValueFlags}
    (checks : List.Forall₂ (fun p v => meetsOne .ground others p v = true) ps vs) :
    ∀ {as : List Atom}, ArgsFaithful Γ τ as vs → Admitted Γ ps (as.map (substA τ)) := by
  induction checks with
  | nil =>
      intro as faithful
      cases faithful
      exact .nil
  | @cons p v ps vs check _ ih =>
      intro as faithful
      cases faithful with
      | @cons a _ as _ head tail =>
          refine .cons (fun active => ?_) (ih tail)
          subst active
          have both := Bool.and_eq_true_iff.mp (by simpa [meetsOne] using check)
          obtain ⟨isGround, clean⟩ := head.2 both.2
          exact ⟨isGround, clean both.1⟩

theorem ArgsFaithful.mem {Γ : Decls} {σ : Substitution} :
    ∀ {as : List Atom} {vs : List ValueFlags}, ArgsFaithful Γ σ as vs →
      ∀ a ∈ as, ∃ v ∈ vs, Faithful Γ (a, σ) v
  | [], [], .nil, _, member => by cases member
  | _ :: _, v :: _, .cons head tail, a, member => by
      rcases List.mem_cons.mp member with same | present
      · exact ⟨v, by simp, same ▸ head⟩
      · obtain ⟨w, wMember, faithful⟩ := ArgsFaithful.mem tail a present
        exact ⟨w, by simp [wMember], faithful⟩

/-- The answer of a version at the value claimed at its polymorphic position
carries that value's claims. -/
theorem active_faithful {Γ : Decls} {τ : Substitution} {r : Atom} :
    ∀ {ps : List Position} {as : List Atom} {vs : List ValueFlags},
      ArgsFaithful Γ τ as vs → ps.length = vs.length → ActiveIs ps (as.map (substA τ)) r →
      Faithful Γ (r, τ) ⟨activeFlags ps vs, false⟩
  | [], _, _, _, _, _ => ⟨rfl, fun ground => by simp [activeFlags] at ground⟩
  | .uninterpreted :: ps, a :: as, v :: vs, .cons faithful _, _, .cons here _ => by
      have same : r = substA τ a := here rfl
      refine ⟨rfl, fun ground => ?_⟩
      obtain ⟨isGround, clean⟩ := faithful.2 ground
      change support (substA τ r) = ∅ ∧ (v.uninterpreted = true → Uninterp Γ (substA τ r))
      rw [same, subst_ground isGround]
      exact ⟨isGround, clean⟩
  | .any :: ps, a :: as, v :: vs, .cons _ rest, len, .cons _ later => by
      show Faithful Γ (r, τ) ⟨activeFlags ps vs, false⟩
      exact active_faithful rest (by simpa using len) later
  | _ :: _, [], [], .nil, len, _ => by simp at len
  | .uninterpreted :: _, [], _ :: _, faithful, _, _ => by cases faithful
  | .any :: _, [], _ :: _, faithful, _, _ => by cases faithful
  | _ :: _, _ :: _, [], faithful, _, _ => by cases faithful

/-- The calls of two runs agree at arguments the versions admit. -/
structure Agree (Γ : Decls) (P : Program) (O O' : Oracle) : Prop where
  self : ∀ ws, Admitted Γ P.positions ws → O.self ws = O'.self ws
  enter : ∀ f ps, P.versions f = some ps → ∀ ws, Admitted Γ ps ws → O.enter f ws = O'.enter f ws

theorem Agree.refl (Γ : Decls) (P : Program) (O : Oracle) : Agree Γ P O O :=
  ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩

theorem no_outcomes {α : Type} {m : Multiset α} (none : ∀ x ∈ m, False) : m = 0 :=
  Multiset.eq_zero_of_forall_notMem fun x member => none x member

section Runs

variable {Γ : Decls} {P : Program} {E : Env} {O O' : Oracle}

mutual
/-- **The analysis under the ground rule is sound, and a run reads its calls only
where the versions admit them**: every outcome keeps the ground facts and the
value's claims, and two runs whose calls agree there have the same outcomes. -/
theorem admits_run (ok : OraclesOK Γ P E O) (agree : Agree Γ P O O') :
    ∀ {F F' : Facts} {e : Expr} {v : ValueFlags}, Admits Γ .ground P F e v F' →
      ∀ σ, GroundSound Γ σ F →
        eval E O e σ = eval E O' e σ ∧
          ∀ out ∈ eval E O e σ, GroundSound Γ out.2 F' ∧ Faithful Γ out v
  | _, _, _, _, .var F x, σ, sound => by
      refine ⟨rfl, fun out member => ?_⟩
      simp only [eval, Multiset.mem_singleton] at member
      subst member
      refine ⟨sound, ?_⟩
      unfold varValue
      cases found : F.lookup x with
      | none => exact ⟨rfl, fun ground => by cases ground⟩
      | some flags =>
          refine ⟨rfl, fun ground => ?_⟩
          exact sound x flags found ground
  | _, _, _, _, .const F a, σ, sound => by
      refine ⟨rfl, fun out member => ?_⟩
      simp only [eval, Multiset.mem_singleton] at member
      subst member
      exact ⟨sound, const_faithful sound a⟩
  | _, _, _, _, .ctor (c := c) (args := args) (vs := vs) all, σ, sound => by
      obtain ⟨same, each⟩ := admitsAll_run ok agree all σ sound
      refine ⟨by simp only [eval, same], fun out member => ?_⟩
      simp only [eval, Multiset.mem_map] at member
      obtain ⟨values, present, rfl⟩ := member
      obtain ⟨after, faithful⟩ := each values present
      refine ⟨after, ?_⟩
      unfold dataValue
      rw [if_neg (by simp [ArgsFaithful.anyBottom_false faithful])]
      refine ⟨rfl, fun ground => ?_⟩
      have grounds : ∀ a ∈ values.1, support (substA values.2 a) = ∅ := by
        intro a member
        obtain ⟨w, wMember, fa⟩ := faithful.mem a member
        exact (fa.2 (List.all_eq_true.mp ground w wMember)).1
      refine ⟨?_, fun unint => ?_⟩
      · apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y present
        change y ∈ support (substA values.2 (.expression (.symbol c :: values.1))) at present
        rw [substA, UnifyAtoms.substL_eq_map, List.map_cons, support_expression] at present
        obtain ⟨part, partMember, occurs⟩ := present
        rcases List.mem_cons.mp partMember with same | mapped
        · rw [same] at occurs
          simp [substA, support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars] at occurs
        · obtain ⟨a, aMember, rfl⟩ := List.mem_map.mp mapped
          rw [grounds a aMember] at occurs
          exact Finset.notMem_empty y occurs
      · have parts := Bool.and_eq_true_iff.mp unint
        change Uninterp Γ (substA values.2 (.expression (.symbol c :: values.1)))
        rw [substA, UnifyAtoms.substL_eq_map, List.map_cons]
        apply UnifyAtoms.uninterp_of_all
        intro part partMember
        rcases List.mem_cons.mp partMember with same | mapped
        · rw [same]
          exact List.isEmpty_iff.mp parts.1
        · obtain ⟨a, aMember, rfl⟩ := List.mem_map.mp mapped
          obtain ⟨w, wMember, fa⟩ := faithful.mem a aMember
          exact (fa.2 (List.all_eq_true.mp ground w wMember)).2
            (List.all_eq_true.mp parts.2 w wMember)
  | _, _, _, _, .self (args := args) (vs := vs) all discharges, σ, sound => by
      obtain ⟨same, each⟩ := admitsAll_run ok agree all σ sound
      have admitted : ∀ out ∈ evalAll E O args σ,
          Admitted Γ P.positions (out.1.map (substA out.2)) ∧ ArgsFaithful Γ out.2 out.1 vs := by
        intro out member
        obtain ⟨_, faithful⟩ := each out member
        rcases discharges with bottom | checked
        · rw [ArgsFaithful.anyBottom_false faithful] at bottom
          cases bottom
        · exact ⟨admitted_of_meets ((meets_iff _ _ _).mp checked) faithful, faithful⟩
      refine ⟨?_, fun out member => ?_⟩
      · simp only [eval]
        rw [← same]
        refine Multiset.bind_congr fun out member => ?_
        rw [agree.self _ (admitted out member).1]
      · simp only [eval, Multiset.mem_bind, Multiset.mem_map] at member
        obtain ⟨values, present, r, answer, rfl⟩ := member
        obtain ⟨after, faithful⟩ := each values present
        refine ⟨after, ?_⟩
        unfold callValue
        rw [if_neg (by simp [ArgsFaithful.anyBottom_false faithful])]
        have len : P.positions.length = vs.length := by
          rcases discharges with bottom | checked
          · rw [ArgsFaithful.anyBottom_false faithful] at bottom
            cases bottom
          · exact ((meets_iff _ _ _).mp checked).length_eq
        exact active_faithful faithful len (ok.self _ (admitted values present).1 r answer)
  | _, _, _, _, .prim (op := op) (args := args) all known, σ, sound => by
      obtain ⟨same, each⟩ := admitsAll_run ok agree all σ sound
      refine ⟨by simp only [eval, same], fun out member => ?_⟩
      simp only [eval, Multiset.mem_bind, Multiset.mem_map] at member
      obtain ⟨values, present, r, answer, rfl⟩ := member
      obtain ⟨after, faithful⟩ := each values present
      refine ⟨after, ?_⟩
      unfold primValue
      rw [if_neg (by simp [ArgsFaithful.anyBottom_false faithful])]
      have len : (values.1.map (substA values.2)).length = args.length := by
        rw [List.length_map, evalAll_length E O args σ values present]
      have isGround := ok.prim op _ (len ▸ known) r answer
      refine ⟨rfl, fun _ => ⟨?_, fun u => by cases u⟩⟩
      change support (substA values.2 r) = ∅
      rw [subst_ground isGround]
      exact isGround
  | _, _, _, _, .call all, σ, sound => by
      obtain ⟨same, each⟩ := admitsAll_run ok agree all σ sound
      refine ⟨by simp only [eval, same], fun out member => ?_⟩
      simp only [eval, Multiset.mem_bind, Multiset.mem_map] at member
      obtain ⟨values, present, r, _, rfl⟩ := member
      obtain ⟨after, faithful⟩ := each values present
      refine ⟨after, ?_⟩
      unfold keptValue
      rw [if_neg (by simp [ArgsFaithful.anyBottom_false faithful])]
      exact ⟨rfl, fun ground => by cases ground⟩
  | _, _, _, _, .enter (f := f) (args := args) (vs := vs) (ps := ps) all offered discharges, σ, sound => by
      obtain ⟨same, each⟩ := admitsAll_run ok agree all σ sound
      have admitted : ∀ out ∈ evalAll E O args σ,
          Admitted Γ ps (out.1.map (substA out.2)) ∧ ArgsFaithful Γ out.2 out.1 vs := by
        intro out member
        obtain ⟨_, faithful⟩ := each out member
        rcases discharges with bottom | checked
        · rw [ArgsFaithful.anyBottom_false faithful] at bottom
          cases bottom
        · exact ⟨admitted_of_meets ((meets_iff _ _ _).mp checked) faithful, faithful⟩
      refine ⟨?_, fun out member => ?_⟩
      · simp only [eval]
        rw [← same]
        refine Multiset.bind_congr fun out member => ?_
        rw [agree.enter f ps offered _ (admitted out member).1]
      · simp only [eval, Multiset.mem_bind, Multiset.mem_map] at member
        obtain ⟨values, present, r, answer, rfl⟩ := member
        obtain ⟨after, faithful⟩ := each values present
        refine ⟨after, ?_⟩
        unfold callValue
        rw [if_neg (by simp [ArgsFaithful.anyBottom_false faithful])]
        have len : ps.length = vs.length := by
          rcases discharges with bottom | checked
          · rw [ArgsFaithful.anyBottom_false faithful] at bottom
            cases bottom
          · exact ((meets_iff _ _ _).mp checked).length_eq
        exact active_faithful faithful len (ok.enter f ps offered _ (admitted values present).1 r answer)
  | _, _, _, _, .letBottom value bottom, σ, sound => by
      obtain ⟨same, each⟩ := admits_run ok agree value σ sound
      have empty : eval E O _ σ = 0 := no_outcomes fun out member => by
        have := (each out member).2.1
        rw [bottom] at this
        cases this
      refine ⟨?_, fun out member => ?_⟩
      · simp only [eval]
        rw [← same, empty, Multiset.zero_bind, Multiset.zero_bind]
      · simp only [eval, empty, Multiset.zero_bind] at member
        exact absurd member (Multiset.notMem_zero out)
  | _, _, _, _, .letE (p := p) value notBottom bind body, σ, sound => by
      obtain ⟨same, each⟩ := admits_run ok agree value σ sound
      refine ⟨?_, fun out member => ?_⟩
      · simp only [eval]
        rw [← same]
        refine Multiset.bind_congr fun first member => ?_
        obtain ⟨after, faithful⟩ := each first member
        cases bound : bindPattern first.2 p first.1 with
        | none => rfl
        | some τ => exact (admits_run ok agree body τ (bindAny_sound bind after faithful bound)).1
      · simp only [eval, Multiset.mem_bind] at member
        obtain ⟨first, present, member⟩ := member
        obtain ⟨after, faithful⟩ := each first present
        cases bound : bindPattern first.2 p first.1 with
        | none => simp [bound] at member
        | some τ =>
            rw [bound] at member
            exact (admits_run ok agree body τ (bindAny_sound bind after faithful bound)).2 out member
  | _, _, _, _, .ifE (t := t) (e := e) condition yes no, σ, sound => by
      obtain ⟨same, each⟩ := admits_run ok agree condition σ sound
      refine ⟨?_, fun out member => ?_⟩
      · simp only [eval]
        rw [← same]
        refine Multiset.bind_congr fun first member => ?_
        obtain ⟨after, _⟩ := each first member
        rw [(admits_run ok agree yes first.2 after).1, (admits_run ok agree no first.2 after).1]
      · simp only [eval, Multiset.mem_bind] at member
        obtain ⟨first, present, member⟩ := member
        obtain ⟨after, _⟩ := each first present
        split at member
        · exact ⟨after.keep (eval_keeps E O t first.2 out member),
            faithful_join_left _ ((admits_run ok agree yes first.2 after).2 out member).2⟩
        · exact ⟨after.keep (eval_keeps E O e first.2 out member),
            faithful_join_right _ ((admits_run ok agree no first.2 after).2 out member).2⟩
  | _, _, _, _, .empty F, σ, sound => ⟨rfl, fun out member => by simp [eval] at member⟩
  | _, _, _, _, .caseBottom key bottom, σ, sound => by
      obtain ⟨same, each⟩ := admits_run ok agree key σ sound
      have empty : eval E O _ σ = 0 := no_outcomes fun out member => by
        have := (each out member).2.1
        rw [bottom] at this
        cases this
      refine ⟨?_, fun out member => ?_⟩
      · simp only [eval]
        rw [← same, empty, Multiset.zero_bind, Multiset.zero_bind]
      · simp only [eval, empty, Multiset.zero_bind] at member
        exact absurd member (Multiset.notMem_zero out)
  | _, _, _, _, .caseE (ps := ps) (bs := bs) key notBottom arms, σ, sound => by
      obtain ⟨same, each⟩ := admits_run ok agree key σ sound
      refine ⟨?_, fun out member => ?_⟩
      · simp only [eval]
        rw [← same]
        refine Multiset.bind_congr fun first member => ?_
        obtain ⟨after, faithful⟩ := each first member
        exact (admitsArms_run ok agree arms first.2 first.1 after faithful).1
      · simp only [eval, Multiset.mem_bind] at member
        obtain ⟨first, present, member⟩ := member
        obtain ⟨after, faithful⟩ := each first present
        exact ⟨after.keep (evalArms_keeps E O first.2 first.1 ps bs out member),
          (admitsArms_run ok agree arms first.2 first.1 after faithful).2 out member⟩
  | _, _, _, _, .matchE (F₁ := F₁) (src := src) (p := p) source clean template, σ, sound => by
      obtain ⟨same, each⟩ := admits_run ok agree source σ sound
      have bindRow : ∀ first ∈ eval E O src σ, ∀ row τ, bindPattern first.2 p row = some τ →
          GroundSound Γ τ (markPat F₁ p ⟨false, true⟩) := by
        intro first member row τ bound
        exact bindAny_sound (v := ⟨⟨false, true⟩, false⟩) (.clean rfl clean) (each first member).1
          ⟨rfl, fun ground => by cases ground⟩ bound
      refine ⟨?_, fun out member => ?_⟩
      · simp only [eval]
        rw [← same]
        refine Multiset.bind_congr fun first member => Multiset.bind_congr fun row _ => ?_
        cases bound : bindPattern first.2 p row with
        | none => rfl
        | some τ => exact (admits_run ok agree template τ (bindRow first member row τ bound)).1
      · simp only [eval, Multiset.mem_bind] at member
        obtain ⟨first, present, row, _, member⟩ := member
        cases bound : bindPattern first.2 p row with
        | none => simp [bound] at member
        | some τ =>
            rw [bound] at member
            exact (admits_run ok agree template τ (bindRow first present row τ bound)).2 out member

theorem admitsAll_run (ok : OraclesOK Γ P E O) (agree : Agree Γ P O O') :
    ∀ {F F' : Facts} {es : List Expr} {vs : List ValueFlags}, AdmitsAll Γ .ground P F es vs F' →
      ∀ σ, GroundSound Γ σ F →
        evalAll E O es σ = evalAll E O' es σ ∧
          ∀ out ∈ evalAll E O es σ, GroundSound Γ out.2 F' ∧ ArgsFaithful Γ out.2 out.1 vs
  | _, _, _, _, .nil F, σ, sound => by
      refine ⟨rfl, fun out member => ?_⟩
      simp only [evalAll, Multiset.mem_singleton] at member
      subst member
      exact ⟨sound, .nil⟩
  | _, _, _, _, .cons (es := es) first rest, σ, sound => by
      obtain ⟨same, each⟩ := admits_run ok agree first σ sound
      refine ⟨?_, fun out member => ?_⟩
      · simp only [evalAll]
        rw [← same]
        refine Multiset.bind_congr fun head member => ?_
        rw [(admitsAll_run ok agree rest head.2 (each head member).1).1]
      · simp only [evalAll, Multiset.mem_bind, Multiset.mem_map] at member
        obtain ⟨head, present, tail, tailPresent, rfl⟩ := member
        obtain ⟨after, faithful⟩ := each head present
        obtain ⟨final, faithfuls⟩ := (admitsAll_run ok agree rest head.2 after).2 tail tailPresent
        exact ⟨final, .cons (faithful.keep (evalAll_keeps E O es head.2 tail tailPresent)) faithfuls⟩

theorem admitsArms_run (ok : OraclesOK Γ P E O) (agree : Agree Γ P O O') :
    ∀ {F : Facts} {kv : ValueFlags} {ps : List Pat} {bs : List Expr} {v : ValueFlags},
      AdmitsArms Γ .ground P F kv ps bs v →
      ∀ σ key, GroundSound Γ σ F → Faithful Γ (key, σ) kv →
        evalArms E O σ key ps bs = evalArms E O' σ key ps bs ∧
          ∀ out ∈ evalArms E O σ key ps bs, Faithful Γ out v
  | _, _, _, _, _, .nil F kv, σ, key, _, _ => ⟨rfl, fun out member => by simp [evalArms] at member⟩
  | _, _, _, _, _, .cons (p := p) bind body rest, σ, key, sound, keyFaithful => by
      obtain ⟨restSame, restEach⟩ := admitsArms_run ok agree rest σ key sound keyFaithful
      cases bound : bindPattern σ p key with
      | none =>
          simp only [evalArms, bound]
          exact ⟨restSame, fun out member => faithful_join_right _ (restEach out member)⟩
      | some τ =>
          simp only [evalArms, bound]
          obtain ⟨same, each⟩ := admits_run ok agree body τ (bindAny_sound bind sound keyFaithful bound)
          exact ⟨same, fun out member => faithful_join_left _ (each out member).2⟩
end

end Runs


/-! ## The return analysis under two-way evaluation -/

mutual
theorem eval_toExpr (E : Env) (O : Oracle) :
    ∀ (p : Pat) (σ : Substitution), eval E O (Pat.toExpr p) σ = {(p.toAtom, σ)}
  | .var _, _ => rfl
  | .const _, _ => rfl
  | .ctor c ps, σ => by
      simp only [Pat.toExpr, Pat.toAtom, eval, evalAll_toExprs E O ps σ, Multiset.map_singleton]

theorem evalAll_toExprs (E : Env) (O : Oracle) :
    ∀ (ps : List Pat) (σ : Substitution), evalAll E O (Pat.toExprs ps) σ = {(Pat.toAtoms ps, σ)}
  | [], _ => rfl
  | p :: ps, σ => by
      simp only [Pat.toExprs, Pat.toAtoms, evalAll, eval_toExpr E O p σ, Multiset.singleton_bind,
        evalAll_toExprs E O ps σ, Multiset.map_singleton]
end

theorem evalArms_from (E : Env) (O : Oracle) (σ : Substitution) (key : Atom) :
    ∀ (ps : List Pat) (bs : List Expr), ∀ out ∈ evalArms E O σ key ps bs,
      ∃ b ∈ bs, ∃ τ, out ∈ eval E O b τ
  | p :: ps, b :: bs, out, member => by
      simp only [evalArms] at member
      split at member
      · next τ _ => exact ⟨b, by simp, τ, member⟩
      · obtain ⟨b', present, τ, found⟩ := evalArms_from E O σ key ps bs out member
        exact ⟨b', by simp [present], τ, found⟩
  | [], _, out, member => by simp [evalArms] at member
  | _ :: _, [], out, member => by simp [evalArms] at member

/-- **A right-hand side that returns a pattern answers it as unification leaves
it** (`contract_returns_pattern`): every outcome's recipe is the pattern. -/
theorem returns_recipe (E : Env) (O : Oracle) {pu : Pat} {e : Expr}
    (returns : ReturnsPat (Pat.toExpr pu) e) :
    ∀ σ, ∀ out ∈ eval E O e σ, out.1 = pu.toAtom := by
  induction returns with
  | refl =>
      intro σ out member
      rw [eval_toExpr, Multiset.mem_singleton] at member
      rw [member]
  | @letE q v b _ ih =>
      intro σ out member
      simp only [eval, Multiset.mem_bind] at member
      obtain ⟨first, _, member⟩ := member
      split at member
      · exact absurd member (Multiset.notMem_zero out)
      · exact ih _ out member
  | ifE _ _ iht ihe =>
      intro σ out member
      simp only [eval, Multiset.mem_bind] at member
      obtain ⟨first, _, member⟩ := member
      split at member
      · exact iht _ out member
      · exact ihe _ out member
  | empty =>
      intro σ out member
      simp [eval] at member
  | @caseE k ps bs _ ih =>
      intro σ out member
      simp only [eval, Multiset.mem_bind] at member
      obtain ⟨first, _, member⟩ := member
      obtain ⟨b, present, τ, found⟩ := evalArms_from E O first.2 first.1 ps bs out member
      exact ih b present τ out found
  | @matchE src q t _ ih =>
      intro σ out member
      simp only [eval, Multiset.mem_bind] at member
      obtain ⟨first, _, row, _, member⟩ := member
      split at member
      · exact absurd member (Multiset.notMem_zero out)
      · exact ih _ out member

/-! ## Equations, activations, and the version -/

/-- Two-way head unification: each parameter's pattern bound to its argument. -/
def headLets : List Pat → List Atom → Expr → Expr
  | p :: ps, a :: as, e => .letE p (.const a) (headLets ps as e)
  | _, _, e => e

/-- The substitution head unification leaves, if it succeeds. -/
def binds : Substitution → List Pat → List Atom → Option Substitution
  | σ, p :: ps, a :: as => (bindPattern σ p a).bind fun τ => binds τ ps as
  | σ, _, _ => some σ

theorem eval_headLets (E : Env) (O : Oracle) (rhs : Expr) :
    ∀ (pats : List Pat) (args : List Atom) (σ : Substitution),
      eval E O (headLets pats args rhs) σ =
        match binds σ pats args with
        | none => 0
        | some τ => eval E O rhs τ
  | p :: ps, a :: as, σ => by
      simp only [headLets, eval, Multiset.singleton_bind, binds]
      cases bindPattern σ p a with
      | none => rfl
      | some τ => exact eval_headLets E O rhs ps as τ
  | [], _, σ => by simp [headLets, binds]
  | _ :: _, [], σ => by simp [headLets, binds]

/-- `contract_equation`'s entry marks. -/
def entryFacts (rule : Rule) : List Position → List Pat → Facts → Facts
  | .uninterpreted :: ps, p :: pats, F => entryFacts rule ps pats (markPat F p rule.entryFlags)
  | .any :: ps, p :: pats, F => entryFacts rule ps pats (markPat F p ⟨false, false⟩)
  | _, _, F => F

/-- After head unification, each polymorphic pattern observes its argument. -/
def ActiveObserved (τ : Substitution) : List Position → List Pat → List Atom → Prop
  | .uninterpreted :: ps, p :: pats, a :: as => substA τ p.toAtom = a ∧ ActiveObserved τ ps pats as
  | .any :: ps, _ :: pats, _ :: as => ActiveObserved τ ps pats as
  | [], [], [] => True
  | _, _, _ => False

/-- The pattern at the polymorphic position. -/
def ActivePat : List Position → List Pat → Pat → Prop
  | .uninterpreted :: _, p :: _, pu => p = pu
  | .any :: ps, _ :: pats, pu => ActivePat ps pats pu
  | _, _, _ => False

theorem ActiveObserved.keep {Γ : Decls} {τ υ : Substitution} (keeps : KeepsGround τ υ) :
    ∀ {ps : List Position} {pats : List Pat} {as : List Atom}, Admitted Γ ps as →
      ActiveObserved τ ps pats as → ActiveObserved υ ps pats as
  | .uninterpreted :: _, _ :: _, _ :: _, .cons here rest, ⟨observed, later⟩ => by
      refine ⟨?_, ActiveObserved.keep keeps rest later⟩
      rw [keeps.observe (by rw [observed]; exact (here rfl).1), observed]
  | .any :: ps, _ :: pats, _ :: as, .cons _ rest, later => by
      show ActiveObserved υ ps pats as
      exact ActiveObserved.keep keeps rest later
  | [], [], [], _, _ => trivial
  | [], [], _ :: _, admitted, _ => by cases admitted
  | [], _ :: _, _, _, observed => by simp [ActiveObserved] at observed
  | .uninterpreted :: _, [], _, _, observed => by simp [ActiveObserved] at observed
  | .any :: _, [], _, _, observed => by simp [ActiveObserved] at observed
  | .uninterpreted :: _, _ :: _, [], admitted, _ => by cases admitted
  | .any :: _, _ :: _, [], admitted, _ => by cases admitted

/-- The C's mark of an ANY parameter claims nothing. -/
theorem markNothing_sound {Γ : Decls} {F : Facts} {p : Pat} {σ τ : Substitution} {a : Atom}
    (sound : GroundSound Γ σ F) (bound : bindPattern σ p a = some τ) :
    GroundSound Γ τ (markPat F p ⟨false, false⟩) := by
  have old := sound.keep (KeepsGround.bind bound)
  intro y flags found ground
  rw [lookup_markPat] at found
  split at found
  · cases oldFound : F.lookup y with
    | none =>
        simp only [oldFound, mergeInto, Option.some.injEq] at found
        subst found
        cases ground
    | some o =>
        simp only [oldFound, mergeInto, Option.some.injEq] at found
        subst found
        have same : mergeFlags o ⟨false, false⟩ = o := by cases o; simp [mergeFlags]
        rw [same] at ground ⊢
        exact old y o oldFound ground
  · exact old y flags found ground

/-- The ground rule's mark of the polymorphic parameter: bound to a ground,
uninterpreted argument, each of its variables names a ground, uninterpreted
part of it. -/
theorem markActive_sound {Γ : Decls} {F : Facts} {p : Pat} {σ τ : Substitution} {a : Atom}
    (sound : GroundSound Γ σ F) (bound : bindPattern σ p a = some τ)
    (isGround : support a = ∅) (clean : Uninterp Γ a) :
    GroundSound Γ τ (markPat F p ⟨true, true⟩) := by
  have keeps := KeepsGround.bind bound
  have old := sound.keep keeps
  have observed : substA σ a = a := subst_ground isGround σ
  intro y flags found ground
  rw [lookup_markPat] at found
  split at found
  · next occurs =>
      have equation : substA τ p.toAtom = a := by
        rw [bindPattern_equation bound, keeps.observe (by rw [observed]; exact isGround), observed]
      have merged : flags.ground = true ∧ flags.uninterpreted = true := by
        cases oldFound : F.lookup y with
        | none =>
            simp only [oldFound, mergeInto, Option.some.injEq] at found
            subst found
            exact ⟨rfl, rfl⟩
        | some o =>
            simp only [oldFound, mergeInto, Option.some.injEq] at found
            subst found
            simp [mergeFlags]
      refine ⟨ground_pattern_marks bound (by rw [observed]; exact isGround) y occurs, fun _ => ?_⟩
      exact uninterpreted_substituted_variable τ p.toAtom (equation ▸ clean) y occurs
  · exact old y flags found ground

/-- **Entry under the ground rule**: head unification of admitted arguments keeps
the entry marks' claims, and each polymorphic pattern observes its argument. -/
theorem entry_ground {Γ : Decls} :
    ∀ (ps : List Position) (pats : List Pat) (args : List Atom) (F : Facts) (σ τ : Substitution),
      Admitted Γ ps args → ps.length = pats.length → GroundSound Γ σ F →
      binds σ pats args = some τ →
        GroundSound Γ τ (entryFacts .ground ps pats F) ∧ ActiveObserved τ ps pats args
  | .uninterpreted :: ps, p :: pats, a :: as, F, σ, τ, .cons here rest, len, sound, bound => by
      simp only [binds, Option.bind_eq_some_iff] at bound
      obtain ⟨τ₁, first, later⟩ := bound
      obtain ⟨isGround, clean⟩ := here rfl
      have marked := markActive_sound sound first isGround clean
      obtain ⟨after, observed⟩ :=
        entry_ground ps pats as _ τ₁ τ rest (by simpa using len) marked later
      refine ⟨after, ?_, observed⟩
      have equation : substA τ₁ p.toAtom = a := by
        rw [bindPattern_equation first, subst_ground isGround]
      have keeps : KeepsGround τ₁ τ := binds_keeps later
      rw [keeps.observe (by rw [equation]; exact isGround), equation]
  | .any :: ps, p :: pats, a :: as, F, σ, τ, .cons _ rest, len, sound, bound => by
      simp only [binds, Option.bind_eq_some_iff] at bound
      obtain ⟨τ₁, first, later⟩ := bound
      exact entry_ground ps pats as _ τ₁ τ rest (by simpa using len)
        (markNothing_sound sound first) later
  | [], [], [], F, σ, τ, _, _, sound, bound => by
      simp only [binds, Option.some.injEq] at bound
      subst bound
      exact ⟨sound, trivial⟩
  | [], [], _ :: _, _, _, _, admitted, _, _, _ => by cases admitted
  | [], _ :: _, _, _, _, _, _, len, _, _ => by simp at len
  | _ :: _, [], _, _, _, _, _, len, _, _ => by simp at len
  | .uninterpreted :: _, _ :: _, [], _, _, _, admitted, _, _, _ => by cases admitted
  | .any :: _, _ :: _, [], _, _, _, admitted, _, _, _ => by cases admitted
where
  binds_keeps : ∀ {σ τ : Substitution} {pats : List Pat} {args : List Atom},
      binds σ pats args = some τ → KeepsGround σ τ
    | σ, τ, p :: ps, a :: as, bound => by
        simp only [binds, Option.bind_eq_some_iff] at bound
        obtain ⟨τ₁, first, later⟩ := bound
        exact (KeepsGround.bind first).trans (binds_keeps later)
    | σ, τ, [], _, bound => by
        simp only [binds, Option.some.injEq] at bound
        subst bound
        exact KeepsGround.refl σ
    | σ, τ, _ :: _, [], bound => by
        simp only [binds, Option.some.injEq] at bound
        subst bound
        exact KeepsGround.refl σ

/-- A relation's positions: ANY parameters around the one polymorphic parameter. -/
def shapeOf (pre post : ℕ) : List Position :=
  List.replicate pre .any ++ .uninterpreted :: List.replicate post .any

theorem admitted_shape {Γ : Decls} {post : ℕ} :
    ∀ (pre : ℕ) (args : List Atom), Admitted Γ (shapeOf pre post) args →
      ∃ us v ws, args = us ++ v :: ws ∧ us.length = pre ∧ ws.length = post ∧
        support v = ∅ ∧ Uninterp Γ v
  | 0, v :: ws, .cons here rest => by
      obtain ⟨isGround, clean⟩ := here rfl
      refine ⟨[], v, ws, rfl, rfl, ?_, isGround, clean⟩
      simpa using rest.length_eq.symm
  | n + 1, a :: args, .cons _ rest => by
      obtain ⟨us, v, ws, rfl, len, wlen, isGround, clean⟩ := admitted_shape n args rest
      exact ⟨a :: us, v, ws, rfl, by simp [len], wlen, isGround, clean⟩
  | 0, [], admitted => by cases admitted
  | _ + 1, [], admitted => by cases admitted

theorem activeIs_shape {r : Atom} {post : ℕ} :
    ∀ (us : List Atom) {v : Atom} {ws : List Atom},
      ActiveIs (shapeOf us.length post) (us ++ v :: ws) r → r = v
  | [], _, _, .cons here _ => here rfl
  | _ :: us, _, _, .cons _ rest => activeIs_shape us rest

theorem activeIs_any_of_observed {τ : Substitution} {r : Atom} :
    ∀ (m : ℕ) {pats : List Pat} {args : List Atom},
      ActiveObserved τ (List.replicate m .any) pats args → ActiveIs (List.replicate m .any) args r
  | 0, [], [], _ => .nil
  | m + 1, _ :: pats, _ :: args, observed =>
      .cons (fun impossible => by cases impossible) (activeIs_any_of_observed m observed)
  | 0, [], _ :: _, observed => by simp [ActiveObserved] at observed
  | 0, _ :: _, _, observed => by simp [ActiveObserved] at observed
  | _ + 1, [], _, observed => by simp [ActiveObserved, List.replicate] at observed
  | _ + 1, _ :: _, [], observed => by simp [ActiveObserved, List.replicate] at observed

/-- At the shape, the observed polymorphic pattern is the argument at the
polymorphic position. -/
theorem activeIs_of_observed {τ : Substitution} {pu : Pat} {post : ℕ} :
    ∀ (pre : ℕ) {pats : List Pat} {args : List Atom},
      ActiveObserved τ (shapeOf pre post) pats args → ActivePat (shapeOf pre post) pats pu →
      ActiveIs (shapeOf pre post) args (substA τ pu.toAtom)
  | 0, p :: pats, a :: args, ⟨observed, rest⟩, active => by
      change p = pu at active
      subst active
      exact .cons (fun _ => observed) (activeIs_any_of_observed post rest)
  | n + 1, _ :: pats, _ :: args, observed, active =>
      .cons (fun impossible => by cases impossible) (activeIs_of_observed n observed active)
  | 0, [], _, observed, _ => by simp [ActiveObserved, shapeOf] at observed
  | 0, _ :: _, [], observed, _ => by simp [ActiveObserved, shapeOf] at observed
  | _ + 1, [], _, observed, _ => by simp [ActiveObserved, shapeOf, List.replicate] at observed
  | _ + 1, _ :: _, [], observed, _ => by simp [ActiveObserved, shapeOf, List.replicate] at observed


/-- **An equation the analysis accepts** (`contract_equation`): one pattern per
position; from the entry marks, its right-hand side has no answer, or has an
uninterpreted value and returns the polymorphic pattern. -/
def Accepted (Γ : Decls) (rule : Rule) (P : Program) (eq : Equation) : Prop :=
  eq.pats.length = P.positions.length ∧
    ∃ v F', Admits Γ rule P (entryFacts rule P.positions eq.pats []) eq.rhs v F' ∧
      (v.bottom = true ∨ (v.uninterpreted = true ∧
        ∃ pu, ActivePat P.positions eq.pats pu ∧ ReturnsPat (Pat.toExpr pu) eq.rhs))

/-- One equation's answers: two-way head unification, then its right-hand side,
observed through the final substitution. Another arity is another relation. -/
def activation (E : Env) (O : Oracle) (eq : Equation) (args : List Atom) : Multiset Atom :=
  if eq.pats.length = args.length then
    (eval E O (headLets eq.pats args eq.rhs) Atom.var).map observe
  else 0

/-- A relation's equations, every one contributing its answers. -/
def relBody (E : Env) (enter : String → List Atom → Multiset Atom) (eqs : List Equation)
    (o : List Atom → Multiset Atom) (args : List Atom) : Multiset Atom :=
  (eqs : Multiset Equation).bind fun eq => activation E ⟨o, enter⟩ eq args

section Version

variable {Γ : Decls} {P : Program} {E : Env}

/-- **Every answer of an accepted equation, at arguments the ground rule admits,
is the polymorphic argument itself**, however the body binds the parameters. -/
theorem activation_answers {O : Oracle} {pre post : ℕ} (ok : OraclesOK Γ P E O)
    (shape : P.positions = shapeOf pre post) {eq : Equation} (accepted : Accepted Γ .ground P eq)
    {args : List Atom} (admitted : Admitted Γ P.positions args) :
    ∀ r ∈ activation E O eq args, ActiveIs P.positions args r := by
  intro r member
  unfold activation at member
  split at member
  · simp only [Multiset.mem_map] at member
    obtain ⟨out, present, rfl⟩ := member
    rw [eval_headLets] at present
    cases bound : binds Atom.var eq.pats args with
    | none => simp [bound] at present
    | some τ =>
        simp only [bound] at present
        obtain ⟨plen, v, F', admits, result⟩ := accepted
        obtain ⟨entered, observed⟩ := entry_ground P.positions eq.pats args [] Atom.var τ admitted
          plen.symm (GroundSound.nil Γ _) bound
        obtain ⟨_, faithful⟩ := (admits_run ok (Agree.refl Γ P O) admits τ entered).2 out present
        rcases result with bottom | ⟨_, pu, active, returns⟩
        · have := faithful.1
          rw [bottom] at this
          cases this
        · rw [shape] at observed active admitted ⊢
          have activeIs := activeIs_of_observed pre observed active
          obtain ⟨us, w, ws, rfl, ulen, _, isGround, _⟩ := admitted_shape pre args admitted
          have value : substA τ pu.toAtom = w := by
            subst ulen
            exact activeIs_shape us activeIs
          have recipe := returns_recipe E O returns τ out present
          have keeps := eval_keeps E O eq.rhs τ out present
          have answer : observe out = substA τ pu.toAtom := by
            rw [observe, recipe, keeps.observe (by rw [value]; exact isGround)]
          rw [answer]
          exact activeIs
  · exact absurd member (Multiset.notMem_zero r)

/-- Two runs whose calls agree where the versions admit them give an accepted
equation the same answers at admitted arguments. -/
theorem activation_congr {O O' : Oracle} (ok : OraclesOK Γ P E O) (agree : Agree Γ P O O')
    {eq : Equation} (accepted : Accepted Γ .ground P eq) {args : List Atom}
    (admitted : Admitted Γ P.positions args) :
    activation E O eq args = activation E O' eq args := by
  unfold activation
  split
  · rw [eval_headLets, eval_headLets]
    cases bound : binds Atom.var eq.pats args with
    | none => rfl
    | some τ =>
        obtain ⟨plen, v, F', admits, _⟩ := accepted
        obtain ⟨entered, _⟩ := entry_ground P.positions eq.pats args [] Atom.var τ admitted
          plen.symm (GroundSound.nil Γ _) bound
        simp only
        rw [(admits_run ok agree admits τ entered).1]
  · rfl

theorem entryFacts_unguarded {grounded : String → Bool} :
    ∀ {As : List (Ty Empty)} {vs : List Atom}, (∀ A ∈ As, demand A.lift ≠ .guarded) →
      As.length = vs.length → EntryFacts Γ grounded As vs
  | [], [], _, _ => .nil
  | A :: As, _ :: _, unguarded, len =>
      .cons (fun guarded => absurd guarded (unguarded A (by simp)))
        (entryFacts_unguarded (fun B member => unguarded B (by simp [member])) (by simpa using len))
  | [], _ :: _, _, len => by simp at len
  | _ :: _, [], _, len => by simp at len

variable {pre post : List (Ty Empty)} {eqs : List Equation}
  {enP enV : String → List Atom → Multiset Atom}

/-- The hypotheses of the ground version theorem: the relation's shape with
unguarded ANY formals, every equation accepted under the ground rule, and the
callees' version theorems, which a caller reads at the arguments their versions
admit. -/
structure GroundVersionHyps (Γ : Decls) (P : Program) (E : Env) (pre post : List (Ty Empty))
    (eqs : List Equation) (enP enV : String → List Atom → Multiset Atom) : Prop where
  unguarded : ∀ A ∈ pre ++ post, demand A.lift ≠ .guarded
  shape : P.positions = shapeOf pre.length post.length
  accepted : ∀ eq ∈ eqs, Accepted Γ .ground P eq
  enterAgree : ∀ f ps, P.versions f = some ps → ∀ ws, Admitted Γ ps ws → enP f ws = enV f ws
  enterActive : ∀ f ps, P.versions f = some ps → ∀ ws, Admitted Γ ps ws →
    ∀ r ∈ enV f ws, ActiveIs ps ws r
  primGround : ∀ op ws, P.prim op ws.length = true → ∀ r ∈ E.prim op ws, support r = ∅

/-- **The version answers the polymorphic argument itself** at every fuel: what
its callers' analyses claim of a discharged call. -/
theorem ground_version_answers (h : GroundVersionHyps Γ P E pre post eqs enP enV) :
    ∀ fuel args, Admitted Γ P.positions args →
      ∀ r ∈ versionRun (relBody E enV eqs) fuel args, ActiveIs P.positions args r
  | 0, _, _, r, member => absurd member (Multiset.notMem_zero r)
  | n + 1, args, admitted, r, member => by
      simp only [versionRun, relBody, Multiset.mem_bind] at member
      obtain ⟨eq, eqMember, member⟩ := member
      exact activation_answers ⟨ground_version_answers h n, h.enterActive, h.primGround⟩ h.shape
        (h.accepted eq (Multiset.mem_coe.mp eqMember)) admitted r member

/-- **The version is the protocol, exact in multiplicity, under the ground rule**:
at arguments whose polymorphic argument is ground and uninterpreted, whatever
the ANY arguments hold and however the body binds them (aliases of open ANY
arguments included), the run whose calls to itself and discharged calls skip
their protocols has, at every fuel, exactly the answers of the run whose every
call runs the protocol of `(-> A₁ … $t … Aₖ $t)`. No premise on declarations
outside the argument is needed. -/
theorem ground_version_eq_protocol (grounded : String → Bool)
    (h : GroundVersionHyps Γ P E pre post eqs enP enV) (t : String) :
    ∀ fuel args, Admitted Γ P.positions args →
      protocolRun Γ grounded (relBody E enP eqs)
          (arrow (pre.map Ty.lift ++ .var t :: post.map Ty.lift) (.var t)) fuel args =
        versionRun (relBody E enV eqs) fuel args
  | 0, _, _ => rfl
  | n + 1, args, admitted => by
      have ih := ground_version_eq_protocol grounded h t n
      have answers := ground_version_answers h n
      have okP : OraclesOK Γ P E ⟨protocolRun Γ grounded (relBody E enP eqs)
          (arrow (pre.map Ty.lift ++ .var t :: post.map Ty.lift) (.var t)) n, enP⟩ :=
        ⟨fun ws admitted' r member => answers ws admitted' r (by rw [← ih ws admitted']; exact member),
          fun f ps offered ws admitted' r member =>
            h.enterActive f ps offered ws admitted' r (by rw [← h.enterAgree f ps offered ws admitted']; exact member),
          h.primGround⟩
      have agree : Agree Γ P ⟨protocolRun Γ grounded (relBody E enP eqs)
          (arrow (pre.map Ty.lift ++ .var t :: post.map Ty.lift) (.var t)) n, enP⟩
          ⟨versionRun (relBody E enV eqs) n, enV⟩ := ⟨ih, h.enterAgree⟩
      have same : relBody E enP eqs (protocolRun Γ grounded (relBody E enP eqs)
          (arrow (pre.map Ty.lift ++ .var t :: post.map Ty.lift) (.var t)) n) args =
          relBody E enV eqs (versionRun (relBody E enV eqs) n) args := by
        unfold relBody
        refine Multiset.bind_congr fun eq eqMember => ?_
        exact activation_congr okP agree (h.accepted eq (Multiset.mem_coe.mp eqMember)) admitted
      simp only [protocolRun, versionRun]
      rw [chainCall_congr _ _ same]
      have shaped := admitted
      rw [h.shape] at shaped
      obtain ⟨us, v, ws, rfl, ulen, wlen, _, clean⟩ := admitted_shape pre.length args shaped
      rw [UninterpretedLocalMultiplicity.pair_protocol_clean _ pre post t _ us ws v ulen.symm clean (fun r member => ?_),
        argCount_of_entryFacts (entryFacts_unguarded
          (fun A member => h.unguarded A (List.mem_append_left _ member)) ulen.symm),
        argCount_of_entryFacts (entryFacts_unguarded
          (fun A member => h.unguarded A (List.mem_append_right _ member)) wlen.symm),
        mul_one, one_nsmul]
      have active := ground_version_answers h (n + 1) (us ++ v :: ws) admitted r member
      rw [h.shape, ← ulen] at active
      refine ⟨Atom.var, ?_, fun _ => trivial⟩
      rw [activeIs_shape us active, substA_var_self]

end Version

/-! ## The open rules refuted -/

open Classical in
/-- `pair_zero` with a second parameter the protocol does not guard, the row
`(-> $a A $a)`: an answer whose type meets no instance of the argument's has
no answer through the protocol. -/
theorem pair_zero_unguarded {Γ : Decls} (kind : Atom → String) {v w r : Atom} {dv : Deriv}
    {A : Ty String} (unguarded : demand A ≠ .guarded) (hve : eff (info Γ v) = {dv})
    (hdv : dv.eqs = []) (happ : ∃ ts, dv.ty = .app ts)
    (apart : ∀ d ∈ eff (info Γ r), ∀ ρ₀ ρ₁ : DVar → Ty Empty, dv.ty.bind ρ₀ ≠ d.ty.bind ρ₁) :
    chainCall Γ kind (fun _ => {r}) (arrow [.var "a", A] (.var "a")) [v, w] = 0 := by
  let S₀ : List (Eqn CallVar) := [(dv.ty.map (atGuard 0), .var (.inl "a"))]
  have sat0 : Sat ([] ++ dv.eqs.map (Eqn.map (atGuard 0)) ++
      [(dv.ty.map (atGuard 0), (Ty.var (Sum.inl "a") : Ty CallVar))]) := by
    refine ⟨fun u => match u with
      | .inl _ => dv.ty.bind fun _ => default
      | .inr (_, _) => default, ?_⟩
    rw [hdv]
    simp only [List.map_nil, List.nil_append, solves_singleton, Ty.bind_var', Ty.bind_map]
    rfl
  have g0 : guard (atGuard 0) [] ((Ty.var "a" : Ty String).map Sum.inl) (info Γ v) (kind v) = {S₀} := by
    rw [guard_of_getType _ _ _ _ _ (by
        rw [Ty.map_var, getType_of_eff _ _ _ hve, if_pos sat0]
        exact Multiset.singleton_ne_zero _),
      Ty.map_var, getType_of_eff _ _ _ hve, if_pos sat0, hdv]
    rfl
  have g2 : guard (atGuard 2) S₀ ((Ty.var "a" : Ty String).map Sum.inl) (info Γ r) (kind r) = 0 := by
    have none : getType (atGuard 2) S₀ (.var (.inl "a")) (info Γ r) = 0 := by
      unfold getType
      rw [Multiset.filter_eq_nil]
      intro E hE ⟨ρ, hρ⟩
      obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.mp hE
      rw [solves_append, solves_append] at hρ
      have h0 := hρ.1.1
      have h1 := hρ.2
      simp only [S₀, solves_singleton, Ty.bind_var', Ty.bind_map] at h0 h1
      exact apart d hd (ρ ∘ atGuard 0) (ρ ∘ atGuard 2) (h0.trans h1.symm)
    unfold guard
    rw [Ty.map_var, if_pos (by rw [none]; rfl), Multiset.filter_singleton, if_neg]
    · rfl
    · rintro ⟨ρ, hρ⟩
      rw [solves_append] at hρ
      have h0 := hρ.1
      have h2 := hρ.2
      simp only [S₀, solves_singleton, Ty.bind_var', Ty.bind_sym, Ty.bind_map] at h0 h2
      obtain ⟨ts, hts⟩ := happ
      rw [← h0, hts, Ty.bind_app] at h2
      cases h2
  unfold chainCall
  rw [arrowSplit_arrow]
  dsimp only
  have guarded : demand (Ty.var "a" : Ty String) = .guarded := by decide
  simp only [guards, guarded, if_true, g0, Multiset.singleton_bind, if_neg unguarded,
    List.length_cons, List.length_nil]
  unfold resultGuard
  rw [if_pos (by decide), g2, Multiset.map_zero]

/-- Arguments the refined rule admits: the polymorphic one uninterpreted, and
ground or every other argument ground. -/
def AdmittedRefined (Γ : Decls) (ps : List Position) (ws : List Atom) : Prop :=
  List.Forall₂ (fun p w => p = .uninterpreted → Uninterp Γ w ∧
    (support w = ∅ ∨ List.Forall₂ (fun q u => q = .any → support u = ∅) ps ws)) ps ws

namespace Refutations

open TypedCalls.Controls (decls sym num gOne eff_gOne eff_incOne gOne_uninterp
  pair_rejects_declared_head)

/-- An untyped `(= (g $x) $x)`: a pure call answering its argument. -/
def env : Env where
  prim := fun _ _ => 0
  kept := fun f args => if f = "g" then (match args with | [x] => {x} | _ => 0) else 0
  rows := fun _ => 0

def noEnter : String → List Atom → Multiset Atom := fun _ _ => 0

def incOne : Atom := .expression [sym "inc", num 1]

theorem g_in_gOne : "g" ∈ support gOne :=
  (support_expression _ "g").mpr ⟨.var "g", by simp,
    by simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars]⟩

theorem gOne_open : support gOne ≠ ∅ := fun empty => by
  have member := g_in_gOne
  rw [empty] at member
  exact Finset.notMem_empty _ member

theorem inc_ground : support (sym "inc") = ∅ := by
  simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars]

/-! ### An open argument carried by a call's answer (one parameter) -/

/-- `(-> $t $t)`: the polymorphic parameter alone. -/
def single : Program := ⟨shapeOf 0 0, fun _ => none, fun _ _ => false⟩

def kOne : Atom := .expression [.var "k", num 1]

/-- `(= (via-call $a) (let ($k 1) (g $a) (let $k inc $a)))`. -/
def callFlow : Equation :=
  ⟨[.var "a"], .letE (.const kOne) (.call "g" [.var "a"])
    (.letE (.var "k") (.const (sym "inc")) (.var "a"))⟩

/-- Every rule's analysis accepts the equation: the call's answer claims nothing,
so binding `($k 1)` to it and then `$k` to `inc` passes `contract_bind_any`. -/
theorem callFlow_accepted (rule : Rule) : Accepted decls rule single callFlow := by
  cases rule <;>
  exact ⟨rfl, _, _, .letE (.call (.cons (.var _ "a") (.nil _))) rfl
    (.keeps (fun h => by cases h) (by decide +kernel))
    (.letE (.const _ _) rfl (.keeps (fun h => by cases h) (by decide +kernel)) (.var _ "a")),
    Or.inr ⟨by decide +kernel, .var "a", rfl, .letE (.letE .refl)⟩⟩

/-- With one parameter, "every other argument is ground" holds vacuously: the
refined rule admits the open `($g 1)`, the ground rule does not. -/
theorem callFlow_admission :
    AdmittedRefined decls single.positions [gOne] ∧ ¬ Admitted decls single.positions [gOne] := by
  refine ⟨.cons (fun _ => ⟨gOne_uninterp, Or.inr (.cons (fun h => by cases h) .nil)⟩) .nil, ?_⟩
  intro admitted
  cases admitted with
  | cons here _ => exact gOne_open (here rfl).1

theorem callFlow_body (o : List Atom → Multiset Atom) (enter : String → List Atom → Multiset Atom) :
    relBody env enter [callFlow] o [gOne] = {incOne} := by
  cbv

/-- **The refined rule is unsound** (and so was the rule before the alias fix):
the version answers `(inc 1)`, the protocol of `(-> $a $a)` nothing. -/
theorem callFlow_refutes (grounded : String → Bool) :
    versionRun (relBody env noEnter [callFlow]) 1 [gOne] = {incOne} ∧
      protocolRun decls grounded (relBody env noEnter [callFlow])
        (arrow (([] : List (Ty Empty)).map Ty.lift ++ .var "a" :: ([] : List (Ty Empty)).map Ty.lift)
          (.var "a")) 1 [gOne] = 0 := by
  refine ⟨callFlow_body _ _, ?_⟩
  change chainCall decls (metatype grounded) (relBody env noEnter [callFlow] _) _ [gOne] = 0
  rw [chainCall_congr (body' := fun _ => {incOne}) _ _ (callFlow_body _ _)]
  exact (pair_rejects_declared_head grounded).2

/-! ### A head pattern sharing the argument's variable (two parameters) -/

/-- `(-> $t %Undefined% $t)`. -/
def pairAny : Program := ⟨shapeOf 0 1, fun _ => none, fun _ _ => false⟩

def kn : Atom := .expression [.var "k", .var "n"]

/-- `(= (bind-head ($k $n) $k) ($k $n))`. -/
def headShare : Equation := ⟨[.const kn, .var "k"], .const kn⟩

/-- Every rule's analysis accepts it: `contract_equation` merges the two marks of
`$k`, and the right-hand side is the polymorphic pattern. -/
theorem headShare_accepted (rule : Rule) : Accepted decls rule pairAny headShare := by
  refine ⟨rfl, _, _, .const _ _, Or.inr ⟨?_, .const kn, rfl, .refl⟩⟩
  cases rule <;> decide +kernel

/-- The refined rule admits `($g 1)` beside the ground, declared `inc`; the ground
rule does not. -/
theorem headShare_admission :
    AdmittedRefined decls pairAny.positions [gOne, sym "inc"] ∧
      ¬ Admitted decls pairAny.positions [gOne, sym "inc"] := by
  refine ⟨.cons (fun _ => ⟨gOne_uninterp, Or.inr (.cons (fun h => by cases h)
      (.cons (fun _ => inc_ground) .nil))⟩) (.cons (fun h => by cases h) .nil), ?_⟩
  intro admitted
  cases admitted with
  | cons here _ => exact gOne_open (here rfl).1

theorem headShare_body (o : List Atom → Multiset Atom) (enter : String → List Atom → Multiset Atom) :
    relBody env enter [headShare] o [gOne, sym "inc"] = {incOne} := by
  cbv

/-- **"Every other argument is ground" is not enough**: head unification binds the
open argument's head through the variable its pattern shares with the ground
ANY argument. The version answers `(inc 1)`; the protocol of
`(-> $a %Undefined% $a)` answers nothing. -/
theorem headShare_refutes (grounded : String → Bool) :
    versionRun (relBody env noEnter [headShare]) 1 [gOne, sym "inc"] = {incOne} ∧
      protocolRun decls grounded (relBody env noEnter [headShare])
        (arrow (([] : List (Ty Empty)).map Ty.lift ++ .var "a" ::
          ([.sym "%Undefined%"] : List (Ty Empty)).map Ty.lift) (.var "a")) 1 [gOne, sym "inc"] = 0 := by
  refine ⟨headShare_body _ _, ?_⟩
  change chainCall decls (metatype grounded) (relBody env noEnter [headShare] _) _ [gOne, sym "inc"] = 0
  rw [chainCall_congr (body' := fun _ => {incOne}) _ _ (headShare_body _ _)]
  obtain ⟨E, hE⟩ := eff_incOne
  refine pair_zero_unguarded _ (by decide) eff_gOne rfl ⟨_, rfl⟩ fun d hd ρ₀ ρ₁ => ?_
  change d ∈ eff (info decls (.expression [sym "inc", num 1])) at hd
  rw [hE, Multiset.mem_singleton] at hd
  subst hd
  simp

/-- The analysis's claim at a discharged call: the refined test passes on the
values of `($g 1)` and `inc`, the ground test does not. -/
theorem headShare_discharge :
    meets .refined pairAny.positions [⟨⟨false, true⟩, false⟩, ⟨⟨true, false⟩, false⟩] = true ∧
      meets .ground pairAny.positions [⟨⟨false, true⟩, false⟩, ⟨⟨true, false⟩, false⟩] = false := by
  decide +kernel

end Refutations

/-! ## Controls: the alias relation -/

namespace Controls

open TypedCalls.Controls (decls sym num gOne)
open Refutations (env noEnter incOne pairAny inc_ground)

def xOne : Atom := .expression [.var "x", num 1]
def plainboxOne : Atom := .expression [sym "plainbox", num 1]
def plainheadOne : Atom := .expression [sym "plainhead", num 1]

/-- `(= (alias-bind-u $a $b) (let $b inc $a))` at `(-> $t %Undefined% $t)`, the
counterexample's relation with the declared `inc` for `Known`. -/
def aliasBind : Equation := ⟨[.var "a", .var "b"], .letE (.var "b") (.const (sym "inc")) (.var "a")⟩

/-- `(= (clean-bind-u $a $b) (let $b plainhead $a))`: the alias with an undeclared head. -/
def cleanBind : Equation := ⟨[.var "a", .var "b"], .letE (.var "b") (.const (sym "plainhead")) (.var "a")⟩

theorem aliasBind_accepted (rule : Rule) : Accepted decls rule pairAny aliasBind := by
  cases rule <;>
  exact ⟨rfl, _, _, .letE (.const _ _) rfl (.keeps (fun h => by cases h) (by decide +kernel)) (.var _ "a"),
    Or.inr ⟨by decide +kernel, .var "a", rfl, .letE .refl⟩⟩

theorem aliasBind_hyps : GroundVersionHyps decls pairAny env [] [.sym "%Undefined%"] [aliasBind]
    noEnter noEnter where
  unguarded A member := by
    simp only [List.nil_append, List.mem_singleton] at member
    subst member
    decide
  shape := rfl
  accepted eq member := by
    simp only [List.mem_singleton] at member
    subst member
    exact aliasBind_accepted .ground
  enterAgree _ _ offered := by cases offered
  enterActive _ _ offered := by cases offered
  primGround _ _ known := by cases known

/-- **The ground case enters the version**: at `((plainbox 1) $y)` the version is
the protocol at every fuel, the alias binding `$y` to `inc` included, and both
answer the argument. -/
theorem ground_case_enters (grounded : String → Bool) (fuel : ℕ) :
    Admitted decls pairAny.positions [plainboxOne, .var "y"] ∧
      protocolRun decls grounded (relBody env noEnter [aliasBind])
          (arrow (([] : List (Ty Empty)).map Ty.lift ++ .var "a" ::
            ([.sym "%Undefined%"] : List (Ty Empty)).map Ty.lift) (.var "a")) (fuel + 1)
          [plainboxOne, .var "y"] = {plainboxOne} := by
  have admitted : Admitted decls pairAny.positions [plainboxOne, .var "y"] :=
    .cons (fun _ => ⟨Finset.eq_empty_iff_forall_notMem.mpr fun y occurs => by
        obtain ⟨part, member, occurs⟩ := (support_expression _ y).mp occurs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;>
          simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars] at occurs,
      by simp [plainboxOne, Uninterp, Safe, SafeAll, HeadFree, substA, decls, sym, num]⟩)
      (.cons (fun h => by cases h) .nil)
  refine ⟨admitted, ?_⟩
  rw [ground_version_eq_protocol grounded aliasBind_hyps "a" (fuel + 1) _ admitted]
  change relBody env noEnter [aliasBind] _ [plainboxOne, .var "y"] = _
  cbv

/-- The counterexample's call `(alias-bind-u ($x 1) $x)`: both rules decline it at
entry, the open argument sharing `$x` with the other. -/
theorem alias_declined_at_entry :
    ¬ Admitted decls pairAny.positions [xOne, .var "x"] ∧
      ¬ AdmittedRefined decls pairAny.positions [xOne, .var "x"] := by
  have xOpen : support xOne ≠ ∅ := fun empty => by
    have member : "x" ∈ support xOne := (support_expression _ "x").mpr ⟨.var "x", by simp,
      by simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars]⟩
    rw [empty] at member
    exact Finset.notMem_empty _ member
  have varOpen : support (Atom.var "x") ≠ ∅ := by
    simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars]
  refine ⟨fun admitted => ?_, fun admitted => ?_⟩
  · cases admitted with
    | cons here _ => exact xOpen (here rfl).1
  · cases admitted with
    | cons here _ =>
        rcases (here rfl).2 with ground | others
        · exact xOpen ground
        · cases others with
          | cons _ rest =>
              cases rest with
              | cons there _ => exact varOpen (there rfl)

/-- `launch`'s analysis: the call into the version of `alias-bind-u`. -/
def launch : Program := ⟨[.any], fun f => if f = "alias-bind-u" then some (shapeOf 0 1) else none,
  fun _ _ => false⟩

def launchFacts : Facts := [("ignored", ⟨true, false⟩)]

def aliasCall : Expr := .enter "alias-bind-u" [.const xOne, .var "x"]

/-- **The discharge is declined by the ground and the refined rules** and was
admitted by the rule before them: `($x 1)` is open, and so is the other value. -/
theorem alias_discharge :
    (∃ v F', Admits decls .unchecked launch launchFacts aliasCall v F') ∧
      (∀ v F', ¬ Admits decls .ground launch launchFacts aliasCall v F') ∧
      (∀ v F', ¬ Admits decls .refined launch launchFacts aliasCall v F') := by
  refine ⟨⟨_, _, .enter (ps := shapeOf 0 1) (.cons (.const _ _) (.cons (.var _ "x") (.nil _)))
      (by simp [launch]) (Or.inr (by decide +kernel))⟩, fun v F' admits => ?_, fun v F' admits => ?_⟩ <;>
  · cases admits with
    | enter all offered discharges =>
        simp only [launch, if_pos] at offered
        cases offered
        cases all with
        | cons first rest =>
            cases first
            cases rest with
            | cons second last =>
                cases second
                cases last
                unfold Discharges at discharges
                revert discharges
                decide +kernel

/-- **The apart case keeps its protocol and agrees**: `(alias-bind-u ($x 1) $z)` is
declined by both rules (`$z` is open), and its protocol answers what the version
would, `($x 1)`. -/
theorem apart_case (grounded : String → Bool) :
    ¬ Admitted decls pairAny.positions [xOne, .var "z"] ∧
      ¬ AdmittedRefined decls pairAny.positions [xOne, .var "z"] ∧
      versionRun (relBody env noEnter [aliasBind]) 1 [xOne, .var "z"] = {xOne} ∧
      protocolRun decls grounded (relBody env noEnter [aliasBind])
          (arrow (([] : List (Ty Empty)).map Ty.lift ++ .var "a" ::
            ([.sym "%Undefined%"] : List (Ty Empty)).map Ty.lift) (.var "a")) 1 [xOne, .var "z"] =
        {xOne} := by
  have xOpen : support xOne ≠ ∅ := fun empty => by
    have member : "x" ∈ support xOne := (support_expression _ "x").mpr ⟨.var "x", by simp,
      by simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars]⟩
    rw [empty] at member
    exact Finset.notMem_empty _ member
  have zOpen : support (Atom.var "z") ≠ ∅ := by
    simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars]
  have body (o : List Atom → Multiset Atom) :
      relBody env noEnter [aliasBind] o [xOne, .var "z"] = {xOne} := by cbv
  refine ⟨fun admitted => ?_, fun admitted => ?_, body _, ?_⟩
  · cases admitted with
    | cons here _ => exact xOpen (here rfl).1
  · cases admitted with
    | cons here _ =>
        rcases (here rfl).2 with ground | others
        · exact xOpen ground
        · cases others with
          | cons _ rest =>
              cases rest with
              | cons there _ => exact zOpen (there rfl)
  · change chainCall decls (metatype grounded) (relBody env noEnter [aliasBind] _) _ [xOne, .var "z"] = _
    rw [chainCall_congr (body' := fun _ => {xOne}) _ _ (body _)]
    have law := UninterpretedLocalMultiplicity.pair_protocol_clean (Γ := decls) (metatype grounded)
      [] [.sym "%Undefined%"] "a" (fun _ => {xOne}) [] [.var "z"] xOne rfl
      (by simp [xOne, Uninterp, Safe, SafeAll, HeadFree, substA, num])
      (fun r member => ⟨Atom.var, by simpa [substA_var_self] using member, fun _ => trivial⟩)
    simp only [List.nil_append] at law
    rw [law, argCount_of_entryFacts .nil,
      argCount_of_entryFacts (.cons (fun guarded => by cases guarded) .nil), mul_one, one_nsmul]

/-- **The clean alias agrees**: with the undeclared `plainhead` for `inc`, the
version and the protocol both answer `(plainhead 1)` at `(($x 1) $x)`, as
`TrustedAliasControls.clean_alias_protocol_agrees`; both rules still decline it. -/
theorem clean_alias_agrees (grounded : String → Bool) :
    ¬ Admitted decls pairAny.positions [xOne, .var "x"] ∧
      versionRun (relBody env noEnter [cleanBind]) 1 [xOne, .var "x"] = {plainheadOne} ∧
      protocolRun decls grounded (relBody env noEnter [cleanBind])
          (arrow (([] : List (Ty Empty)).map Ty.lift ++ .var "a" ::
            ([.sym "%Undefined%"] : List (Ty Empty)).map Ty.lift) (.var "a")) 1 [xOne, .var "x"] =
        {plainheadOne} := by
  have body (o : List Atom → Multiset Atom) :
      relBody env noEnter [cleanBind] o [xOne, .var "x"] = {plainheadOne} := by cbv
  refine ⟨alias_declined_at_entry.1, body _, ?_⟩
  change chainCall decls (metatype grounded) (relBody env noEnter [cleanBind] _) _ [xOne, .var "x"] = _
  rw [chainCall_congr (body' := fun _ => {plainheadOne}) _ _ (body _)]
  have law := UninterpretedLocalMultiplicity.pair_protocol_clean (Γ := decls) (metatype grounded)
    [] [.sym "%Undefined%"] "a" (fun _ => {plainheadOne}) [] [.var "x"] xOne rfl
    (by simp [xOne, Uninterp, Safe, SafeAll, HeadFree, substA, num])
    (fun r member => ⟨fun y => if y = "x" then sym "plainhead" else .var y, by
      simp only [Multiset.mem_singleton] at member
      subst member
      simp [plainheadOne, xOne, substA, substL, sym, num], fun y => by
        by_cases same : y = "x"
        · simp [same, Uninterp, Safe, decls, sym]
        · simp only [same, if_false]
          trivial⟩)
  simp only [List.nil_append] at law
  rw [law, argCount_of_entryFacts .nil,
    argCount_of_entryFacts (.cons (fun guarded => by cases guarded) .nil), mul_one, one_nsmul]

/-- **The counterexample, checked**: `(alias-bind-u ($g 1) $g)`. Entered, the
version answers `(inc 1)`; the protocol of `(-> $a %Undefined% $a)` answers
nothing; the ground and the refined rules both decline it. -/
theorem alias_counterexample (grounded : String → Bool) :
    versionRun (relBody env noEnter [aliasBind]) 1 [gOne, .var "g"] = {incOne} ∧
      protocolRun decls grounded (relBody env noEnter [aliasBind])
          (arrow (([] : List (Ty Empty)).map Ty.lift ++ .var "a" ::
            ([.sym "%Undefined%"] : List (Ty Empty)).map Ty.lift) (.var "a")) 1 [gOne, .var "g"] = 0 ∧
      ¬ Admitted decls pairAny.positions [gOne, .var "g"] ∧
      ¬ AdmittedRefined decls pairAny.positions [gOne, .var "g"] := by
  have body (o : List Atom → Multiset Atom) :
      relBody env noEnter [aliasBind] o [gOne, .var "g"] = {incOne} := by cbv
  have varOpen : support (Atom.var "g") ≠ ∅ := by
    simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars]
  refine ⟨body _, ?_, fun admitted => ?_, fun admitted => ?_⟩
  · change chainCall decls (metatype grounded) (relBody env noEnter [aliasBind] _) _ [gOne, .var "g"] = 0
    rw [chainCall_congr (body' := fun _ => {incOne}) _ _ (body _)]
    obtain ⟨E, hE⟩ := TypedCalls.Controls.eff_incOne
    refine pair_zero_unguarded _ (by decide) TypedCalls.Controls.eff_gOne rfl ⟨_, rfl⟩
      fun d hd ρ₀ ρ₁ => ?_
    change d ∈ eff (info decls (.expression [sym "inc", num 1])) at hd
    rw [hE, Multiset.mem_singleton] at hd
    subst hd
    simp
  · cases admitted with
    | cons here _ => exact Refutations.gOne_open (here rfl).1
  · cases admitted with
    | cons here _ =>
        rcases (here rfl).2 with ground | others
        · exact Refutations.gOne_open ground
        · cases others with
          | cons _ rest =>
              cases rest with
              | cons there _ => exact varOpen (there rfl)

end Controls

/-! ## The unchecked formal (DIFF-18) -/

/-- **A declaration's formal reads the same to the call protocol and to the type
relation**: away from `Atom`, a formal adds no equation for a constructor's
field exactly when it leaves a typed call's argument unguarded. `_` is such a
formal, as `%Undefined%` is; SWI-PeTTa's `get-type` checks a field declared `_`
as the type named `_` while its calls leave the argument unguarded. -/
theorem formal_reads_alike {A : Ty String} (notAtom : A ≠ .sym "Atom") (i : ℕ)
    (As : List (Ty String)) (d : Deriv) (ds : List Deriv) :
    (Unchecked A → ctorEqs i (A :: As) (d :: ds) = ctorEqs (i + 1) As ds ∧ demand A = .unchecked) ∧
      (¬ Unchecked A → ctorEqs (i + 1) As ds ≠ ctorEqs i (A :: As) (d :: ds) ∧ demand A = .guarded) := by
  refine ⟨fun unchecked => ⟨by simp [ctorEqs, unchecked], by simp [demand, notAtom, unchecked]⟩,
    fun checked => ⟨fun same => ?_, by simp [demand, notAtom, checked]⟩⟩
  have lengths := congrArg List.length same
  simp only [ctorEqs, checked, if_false, List.length_append, List.length_cons] at lengths
  omega

theorem underscore_unchecked : Unchecked (.sym "_" : Ty String) ∧ Unchecked (.sym "%Undefined%" : Ty String) :=
  ⟨Or.inr rfl, Or.inl rfl⟩
end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.GroundUninterpretedVersions
