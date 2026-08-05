import Metamath.Spec.Equivalence

/-!
# The support boundary of declarative Metamath provability

`Metamath.Provable` (the declarative big-step semantics) admits an
unrestricted `var` rule: `Provable axs Γ ↑v` holds for *every* variable
`v`, whether or not any floating hypothesis for `v` is active.
`SupportedProvable Γ fr` strengthens each `var` leaf with a witness that
the variable is present in the frame's floating-hypothesis map — the
exact discipline the operational verifier enforces.

This file settles the direction that was still open between them:

* `SupportedProvable.toSemantic` (proved elsewhere) forgets the witnesses.
* The converse — conservativity of the unrestricted semantics over the
  supported one at a fixed frame — is **false**, and the failure survives
  every database well-formedness condition in the specification.

## The counterexample

One axiom, reachable from concrete Metamath source:

```text
$c |- wff c $.
${
  $v x $.
  wx $f wff x $.
  ha $e wff x $.
  ax-A $a |- c $.
$}
thm $p |- c $= ? $.
```

`ax-A`'s stored frame carries the floating hypothesis `wff x` and the
essential hypothesis `wff x`.  At `thm` the scope has closed: the active
frame is empty.  The unrestricted semantics proves `|- c` by applying
`ax-A` with `σ x := y` for a variable `y` that no frame anywhere
declares — both hypothesis instances become `wff y`, which the
unrestricted `var` rule supplies for free.  The supported semantics
cannot discharge `wff (σ x)` at all: the frame is empty, so no `var`
leaf has a witness, no essential hypothesis is available, and every
stored axiom conclusion carries typecode `|-`, never `wff`.

## The repair witness

The failure is precisely a missing dummy variable, not a defect of the
supported relation: extending the theorem-site frame with a single fresh
floating hypothesis `wff y` restores provability
(`supportedProvable_target_with_dummy`).  The correct general
reconciliation is therefore dummy-supply extension — relating the
unrestricted semantics to the supported one over a frame enlarged with
fresh typed dummies — not a frame-local equivalence.

Positive calibration: `supportedProvable_target_with_dummy`.
Negative calibration: `not_supportedProvable_target`,
`semantic_not_conservative_over_supported`.
-/

namespace Mettapedia.Languages.Metamath.InferenceSupportedProvableBoundary

open Metamath.Spec.Equivalence
open Metamath.Spec.Bridge (MarioVR MarioFormula)

/-- `Metamath.Expr` is a `def` over `List Sym`, so the underlying
decidability instance does not fire through it. -/
local instance : DecidableEq Metamath.Expr :=
  inferInstanceAs (DecidableEq (List Metamath.Sym))

/-- `Metamath.Formula` is a `def` over `CN × Expr`. -/
local instance : DecidableEq Metamath.Formula :=
  inferInstanceAs (DecidableEq (Metamath.CN × Metamath.Expr))

/-! ## The counterexample database -/

/-- Global constants: the provability typecode, the wff typecode, and one
constant symbol `c`. -/
def counterexampleConstants : Metamath.Spec.ConstSet :=
  fun s => s = "|-" ∨ s = "wff" ∨ s = "c"

def xVariable : Metamath.Spec.Variable := ⟨"x"⟩

def wffConstant : Metamath.Spec.Constant := ⟨"wff"⟩

def turnstileConstant : Metamath.Spec.Constant := ⟨"|-"⟩

/-- The essential hypothesis `wff x`. -/
def essentialWffX : Metamath.Spec.Expr := ⟨wffConstant, ["x"]⟩

/-- The axiom conclusion `|- c`. -/
def conclusionC : Metamath.Spec.Expr := ⟨turnstileConstant, ["c"]⟩

/-- The stored frame of `ax-A`: floating `wff x`, essential `wff x`,
no disjointness conditions. -/
def axiomFrame : Metamath.Spec.Frame :=
  ⟨[.floating wffConstant xVariable, .essential essentialWffX], []⟩

/-- The active frame at the theorem site: the scope has closed. -/
def emptyFrame : Metamath.Spec.Frame := ⟨[], []⟩

/-- The database holding exactly `ax-A`. -/
def counterexampleDatabase : Metamath.Spec.Database :=
  fun l => if l = "ax-A" then some (axiomFrame, conclusionC) else none

/-- The image of `x` under the axiom frame's variable map. -/
def xVR : MarioVR := ⟨"wff", 0⟩

/-- A variable no frame in the database declares. -/
def ghostVariable : MarioVR := ⟨"wff", 37⟩

/-- The target formula `|- c`; it mentions no variables at all. -/
def target : MarioFormula := ("|-", [Metamath.Sym.const "c"])

/-- The axiom `ax-A` as a semantic statement. -/
noncomputable def axiomStatement : Metamath.Spec.Semantic.Statement :=
  ⟨frameToContext axiomFrame,
   exprToFormula (varMapOfFrame axiomFrame) conclusionC⟩

/-! ## Computed shapes -/

theorem database_entries {l : Metamath.Spec.Label}
    {fr : Metamath.Spec.Frame} {e : Metamath.Spec.Expr}
    (hlookup : counterexampleDatabase l = some (fr, e)) :
    fr = axiomFrame ∧ e = conclusionC := by
  simp only [counterexampleDatabase] at hlookup
  split at hlookup
  · exact ⟨(congrArg Prod.fst (Option.some.inj hlookup)).symm,
      (congrArg Prod.snd (Option.some.inj hlookup)).symm⟩
  · exact nomatch hlookup

theorem varMapOfFrame_emptyFrame :
    varMapOfFrame emptyFrame = [] := rfl

theorem axiomStatement_fmla_eq :
    axiomStatement.fmla = target := by decide

theorem axiomStatement_hyps_eq :
    axiomStatement.ctx.hyps =
      [(("wff" : Metamath.CN), [Metamath.Sym.var xVR]),
       (("wff" : Metamath.CN), [Metamath.Sym.var xVR])] := by decide

theorem axiomStatement_vars_eq :
    axiomStatement.vars = [xVR, xVR] := by decide

theorem axiomFrame_vars_eq :
    axiomFrame.vars = [xVariable] := by decide

theorem axiomStatement_dj_eq :
    axiomStatement.ctx.dj = Metamath.DJ.mk' [] := rfl

theorem axiomStatement_dj_not {a b : MarioVR} :
    ¬ axiomStatement.ctx.dj a b := by
  rw [axiomStatement_dj_eq]
  rintro ⟨-, h | h⟩ <;> exact nomatch h

/-- Membership of `ax-A` in the axiom set of the database. -/
theorem axiomStatement_mem :
    dbToAxioms counterexampleDatabase axiomStatement :=
  ⟨"ax-A", axiomFrame, conclusionC, by simp [counterexampleDatabase],
    rfl, rfl⟩

/-! ## Positive side: the unrestricted semantics proves `|- c` -/

/-- The substitution feeding the ghost variable to every slot. -/
def ghostSubstitution : MarioVR → Metamath.Expr :=
  fun _ => [Metamath.Sym.var ghostVariable]

theorem semantic_provable_target :
    Metamath.Spec.Semantic.Provable (dbToAxioms counterexampleDatabase)
      (frameToContext emptyFrame) target := by
  have h :=
    Metamath.Provable.ax (axs := dbToAxioms counterexampleDatabase)
      (Γ := frameToContext emptyFrame) (σ := ghostSubstitution)
      (ax := axiomStatement) axiomStatement_mem
      (fun a b hab => (axiomStatement_dj_not hab).elim)
      (by
        intro hyp hmem
        rw [axiomStatement_hyps_eq] at hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact Metamath.Provable.var ghostVariable
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact Metamath.Provable.var ghostVariable
        exact nomatch hmem)
      (by
        intro v hmem
        rw [axiomStatement_vars_eq] at hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact Metamath.Provable.var ghostVariable
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact Metamath.Provable.var ghostVariable
        exact nomatch hmem)
  have hfmla :
      axiomStatement.fmla.subst ghostSubstitution = target := by
    rw [axiomStatement_fmla_eq]
    rfl
  exact hfmla ▸ h

/-! ## Negative side: the supported semantics cannot prove `|- c` -/

/-- Every stored axiom conclusion carries typecode `|-` under every
substitution. -/
theorem no_axiom_concludes_wff
    {ax : Metamath.Spec.Semantic.Statement}
    (hax : dbToAxioms counterexampleDatabase ax)
    (σ : MarioVR → Metamath.Expr) :
    (ax.fmla.subst σ).1 = "|-" := by
  obtain ⟨l, fr, e, hlookup, -, hfmla⟩ := hax
  obtain ⟨rfl, rfl⟩ := database_entries hlookup
  rw [hfmla]
  rfl

/-- Over the empty frame, no supported derivation of a `wff`-typecoded
formula exists: there are no hypotheses, no supported variables, and no
axiom concluding at that typecode. -/
theorem no_supported_wff {e : Metamath.Expr} :
    ¬ SupportedProvable counterexampleDatabase emptyFrame ("wff", e) := by
  intro h
  generalize hf : ((("wff" : Metamath.CN), e) : MarioFormula) = f at h
  cases h with
  | hyp g hmem =>
      simp [frameToContext, emptyFrame] at hmem
  | var v hsupp =>
      obtain ⟨v', hfind⟩ := hsupp
      rw [varMapOfFrame_emptyFrame] at hfind
      simp [findVar] at hfind
  | ax σ hax hdj hhyps hvars hwf =>
      have h1 := congrArg Prod.fst hf
      rw [no_axiom_concludes_wff hax σ] at h1
      have h2 : ("wff" : Metamath.CN) = "|-" := h1
      exact absurd h2 (by decide)

theorem not_supportedProvable_target :
    ¬ SupportedProvable counterexampleDatabase emptyFrame target := by
  intro h
  generalize hf : target = f at h
  cases h with
  | hyp g hmem =>
      simp [frameToContext, emptyFrame] at hmem
  | var v hsupp =>
      have h1 := congrArg Prod.snd hf
      simp only [target, Metamath.VR.vhyp] at h1
      injection h1 with h2 _
      exact Metamath.Sym.noConfusion h2
  | ax σ hax hdj hhyps hvars hwf =>
      obtain ⟨l, fr, e, hlookup, hctx, -⟩ := hax
      obtain ⟨rfl, rfl⟩ := database_entries hlookup
      have hbase : (("wff" : Metamath.CN), [Metamath.Sym.var xVR]) ∈
          (frameToContext axiomFrame).hyps := by
        rw [show (frameToContext axiomFrame).hyps = _ from
          axiomStatement_hyps_eq]
        exact List.Mem.head _
      have hinner := hhyps _ (hctx.symm ▸ hbase)
      exact no_supported_wff hinner

/-! ## Well-formedness of the counterexample -/

theorem wellFormed_counterexampleDatabase :
    WellFormedDatabaseStrong counterexampleDatabase
      counterexampleConstants := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro l fr e hlookup
    obtain ⟨rfl, rfl⟩ := database_entries hlookup
    constructor
    · intro s hs
      simp only [conclusionC] at hs
      rcases List.mem_singleton.mp hs with rfl
      exact Or.inr (Or.inr (Or.inr rfl))
    · intro h hmem
      simp only [axiomFrame, List.mem_cons, List.not_mem_nil,
        or_false] at hmem
      rcases hmem with rfl | rfl
      · trivial
      · intro s hs
        simp only [essentialWffX] at hs
        rcases List.mem_singleton.mp hs with rfl
        exact Or.inl (by rw [axiomFrame_vars_eq]; exact List.Mem.head _)
  · intro l fr e hlookup
    obtain ⟨rfl, -⟩ := database_entries hlookup
    intro v hv
    rw [axiomFrame_vars_eq] at hv
    rcases List.mem_singleton.mp hv with rfl
    rintro (h | h | h) <;> exact absurd h (by decide)
  · intro l fr e hlookup
    obtain ⟨rfl, -⟩ := database_entries hlookup
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro c c' v hc hc'
      simp only [axiomFrame, List.mem_cons, List.not_mem_nil,
        or_false] at hc hc'
      rcases hc with hc | hc <;> rcases hc' with hc' | hc'
      · injection hc with hc1 _
        injection hc' with hc1' _
        rw [hc1, hc1']
      · exact nomatch hc'
      · exact nomatch hc
      · exact nomatch hc
    · unfold FloatVarNoDup
      decide
    · intro v w hvw
      exact nomatch hvw
    · intro v hvv
      exact nomatch hvv

theorem emptyFrame_wellFormed :
    FrameWellFormed emptyFrame ∧ DVWellFormed emptyFrame := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro c c' v hc
    exact nomatch hc
  · unfold FloatVarNoDup
    decide
  · intro v w hvw
    exact nomatch hvw
  · intro v hvv
    exact nomatch hvv

/-- The unrestricted declarative semantics is **not** conservative over
the supported semantics at a fixed frame — even for a strongly
well-formed database, a well-formed frame, and a conclusion mentioning no
variables at all.  The missing ingredient is a dummy-variable supply, not
a well-formedness condition. -/
theorem semantic_not_conservative_over_supported :
    ¬ ∀ (Γ : Metamath.Spec.Database) (consts : Metamath.Spec.ConstSet)
        (fr : Metamath.Spec.Frame) (fmla : MarioFormula),
        WellFormedDatabaseStrong Γ consts →
        FrameWellFormed fr →
        DVWellFormed fr →
        fmla.2.vars = [] →
        Metamath.Spec.Semantic.Provable (dbToAxioms Γ)
          (frameToContext fr) fmla →
        SupportedProvable Γ fr fmla := by
  intro h
  exact not_supportedProvable_target
    (h counterexampleDatabase counterexampleConstants emptyFrame target
      wellFormed_counterexampleDatabase
      emptyFrame_wellFormed.1 emptyFrame_wellFormed.2
      rfl semantic_provable_target)

/-! ## Repair witness: one declared dummy restores provability -/

def dummyVariable : Metamath.Spec.Variable := ⟨"y"⟩

/-- The theorem-site frame extended with one fresh floating hypothesis
`wff y`. -/
def dummyFrame : Metamath.Spec.Frame :=
  ⟨[.floating wffConstant dummyVariable], []⟩

/-- The image of `y` under the dummy frame's variable map. -/
def dummyVR : MarioVR := ⟨"wff", 0⟩

theorem findVar_dummyFrame :
    findVar (varMapOfFrame dummyFrame) dummyVR = some dummyVariable := by
  decide

/-- With a single declared dummy of the right typecode, the supported
semantics proves the same target: the counterexample is exactly a missing
dummy-variable supply. -/
theorem supportedProvable_target_with_dummy :
    SupportedProvable counterexampleDatabase dummyFrame target := by
  have h :=
    SupportedProvable.ax (Γ := counterexampleDatabase) (fr := dummyFrame)
      (σ := fun _ => [Metamath.Sym.var dummyVR]) (ax := axiomStatement)
      axiomStatement_mem
      (fun a b hab => (axiomStatement_dj_not hab).elim)
      (by
        intro hyp hmem
        rw [axiomStatement_hyps_eq] at hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact SupportedProvable.var dummyVR
            ⟨dummyVariable, findVar_dummyFrame⟩
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact SupportedProvable.var dummyVR
            ⟨dummyVariable, findVar_dummyFrame⟩
        exact nomatch hmem)
      (by
        intro v hmem
        rw [axiomStatement_vars_eq] at hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact SupportedProvable.var dummyVR
            ⟨dummyVariable, findVar_dummyFrame⟩
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact SupportedProvable.var dummyVR
            ⟨dummyVariable, findVar_dummyFrame⟩
        exact nomatch hmem)
      (by
        intro v hmem vr hvr
        have h1 := List.mem_singleton.mp hvr
        injection h1 with h2
        subst h2
        exact ⟨dummyVariable, findVar_dummyFrame⟩)
  have hfmla :
      axiomStatement.fmla.subst (fun _ => [Metamath.Sym.var dummyVR]) =
        target := by
    rw [axiomStatement_fmla_eq]
    rfl
  exact hfmla ▸ h

end Mettapedia.Languages.Metamath.InferenceSupportedProvableBoundary
