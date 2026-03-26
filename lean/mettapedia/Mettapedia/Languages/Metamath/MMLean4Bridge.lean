import Metamath.DeclarativeSpec
import Metamath.Verify
import Metamath.KernelClean
import Metamath.OperationalBridge

/-!
# Metamath Bridge to `mm-lean4`

This is the new ground floor for Metamath inside `mettapedia`.

Positive example:
- the bridge names the actual verified carriers from `mm-lean4`
- kernel-facing conversions are the proved `Metamath.Kernel.toExpr`,
  `toFrame`, and `toDatabase`, not opaque stand-ins

Negative example:
- this file does not define a shadow Metamath `LanguageDef`
- this file does not hide semantics behind opaque relation declarations
-/

namespace Mettapedia.Languages.Metamath.MMLean4Bridge

abbrev SpecConst := Metamath.CN
abbrev SpecVar := Metamath.VR
abbrev SpecSym := Metamath.Sym
abbrev SpecExpr := Metamath.Expr
abbrev SpecFormula := Metamath.Formula
abbrev SpecContext := Metamath.Context
abbrev SpecStatement := Metamath.Statement
abbrev SpecProvable := Metamath.Provable

abbrev RuntimeSym := Metamath.Verify.Sym
abbrev RuntimeFormula := Metamath.Verify.Formula
abbrev RuntimeFrame := Metamath.Verify.Frame
abbrev RuntimeProofState := Metamath.Verify.ProofState
abbrev RuntimeDB := Metamath.Verify.DB
abbrev RuntimeError := Metamath.Verify.ProofCheckFail
abbrev RuntimeMode := Metamath.Verify.ModeConfig

abbrev OperationalDatabase := Metamath.Spec.Database
abbrev OperationalFrame := Metamath.Spec.Frame
abbrev OperationalExpr := Metamath.Spec.Expr
abbrev OperationalProvable := Metamath.Spec.Provable

/-- Verified parser entrypoint from `mm-lean4`. -/
abbrev checkBytes := Metamath.Verify.checkBytes

/-- Verified one-step proof transition used by the runtime checker. -/
abbrev stepNormal := Metamath.Verify.DB.stepNormal

/-- Kernel-clean bridge from runtime formulas to operational/spec expressions. -/
abbrev toOperationalExpr := Metamath.Kernel.toExpr

/-- Kernel-clean bridge from runtime frames to operational/spec frames. -/
abbrev toOperationalFrame := Metamath.Kernel.toFrame

/-- Kernel-clean bridge from runtime databases to operational/spec databases. -/
abbrev toOperationalDatabase := Metamath.Kernel.toDatabase

/-- Totalized database bridge used by existing `mm-lean4` theorems. -/
abbrev toOperationalDatabaseTotal := Metamath.Kernel.toDatabaseTotal

/-- End-to-end acceptance theorem already proved in `mm-lean4`. -/
abbrev parserAcceptance_iff_specProvable :=
  Metamath.Kernel.verify_parser_acceptance_iff_spec_provable

/-- Explicit carrier table for the new Metamath bridge.
This is intentionally small and type-directed: it tells us which verified
`mm-lean4` types future Metamath `languageDef!` carriers must correspond to. -/
structure TypeBridge where
  label : Type := String
  specConst : Type := SpecConst
  specVar : Type := SpecVar
  specSym : Type := SpecSym
  specExpr : Type := SpecExpr
  specFormula : Type := SpecFormula
  specContext : Type := SpecContext
  specStatement : Type := SpecStatement
  runtimeSym : Type := RuntimeSym
  runtimeFormula : Type := RuntimeFormula
  runtimeFrame : Type := RuntimeFrame
  runtimeProofState : Type := RuntimeProofState
  runtimeDB : Type := RuntimeDB
  runtimeError : Type := RuntimeError
  operationalDatabase : Type := OperationalDatabase
  operationalFrame : Type := OperationalFrame
  operationalExpr : Type := OperationalExpr

def typeBridge : TypeBridge := {}

/-- Canonical carrier keys for the Metamath bridge boundary. -/
inductive CarrierKey where
  | label
  | specConst
  | specVar
  | specSym
  | specExpr
  | specFormula
  | specContext
  | specStatement
  | runtimeSym
  | runtimeFormula
  | runtimeFrame
  | runtimeProofState
  | runtimeDB
  | runtimeError
  | runtimeMode
  | proofTok
  | includePath
  | operationalDatabase
  | operationalFrame
  | operationalExpr
  deriving DecidableEq, Repr

/-- Type-level correspondence table used by future authored `languageDef!` carriers. -/
def carrierType : CarrierKey → Type
  | .label => String
  | .specConst => SpecConst
  | .specVar => SpecVar
  | .specSym => SpecSym
  | .specExpr => SpecExpr
  | .specFormula => SpecFormula
  | .specContext => SpecContext
  | .specStatement => SpecStatement
  | .runtimeSym => RuntimeSym
  | .runtimeFormula => RuntimeFormula
  | .runtimeFrame => RuntimeFrame
  | .runtimeProofState => RuntimeProofState
  | .runtimeDB => RuntimeDB
  | .runtimeError => RuntimeError
  | .runtimeMode => RuntimeMode
  | .proofTok => String
  | .includePath => String
  | .operationalDatabase => OperationalDatabase
  | .operationalFrame => OperationalFrame
  | .operationalExpr => OperationalExpr

/-- Runtime-side state for Metamath checking. -/
structure RuntimeState where
  db : RuntimeDB
  proof : RuntimeProofState

/-- Operational/spec-side state image used for correspondence proofs. -/
structure SpecState where
  Γ : OperationalDatabase
  frame : OperationalFrame
  goal : OperationalExpr

/-- Explicit state correspondence between runtime and operational/spec images. -/
def StateCorresponds (rt : RuntimeState) (sp : SpecState) : Prop :=
  toOperationalDatabase rt.db = some sp.Γ ∧
    toOperationalFrame rt.db rt.proof.frame = some sp.frame ∧
    sp.goal = toOperationalExpr rt.proof.fmla

/-- Compute the operational/spec image of a runtime state when bridges succeed. -/
def RuntimeState.toSpecState? (rt : RuntimeState) : Option SpecState :=
  match toOperationalDatabase rt.db with
  | none => none
  | some Γ =>
      match toOperationalFrame rt.db rt.proof.frame with
      | none => none
      | some frame =>
          some { Γ := Γ, frame := frame, goal := toOperationalExpr rt.proof.fmla }

/-- Runtime small-step wrapper over the verified `mm-lean4` step transition. -/
def RuntimeState.stepNormal (rt : RuntimeState) (label : String) :
    Except RuntimeError RuntimeState := do
  let proof' ← Metamath.Verify.DB.stepNormal rt.db rt.proof label
  pure { rt with proof := proof' }

theorem RuntimeState.toSpecState?_sound
    (rt : RuntimeState) (sp : SpecState) :
    rt.toSpecState? = some sp → StateCorresponds rt sp := by
  intro h
  unfold RuntimeState.toSpecState? at h
  unfold StateCorresponds
  split at h
  · simp at h
  · rename_i Γ hdb
    split at h
    · simp at h
    · rename_i frame hfr
      cases h
      exact ⟨hdb, hfr, rfl⟩

theorem RuntimeState.toSpecState?_complete
    (rt : RuntimeState) (sp : SpecState) :
    StateCorresponds rt sp → rt.toSpecState? = some sp := by
  cases sp with
  | mk Γ frame goal =>
      intro h
      rcases h with ⟨hdb, hfr, hgoal⟩
      have hgoal' : toOperationalExpr rt.proof.fmla = goal := hgoal.symm
      unfold RuntimeState.toSpecState?
      simp [hdb, hfr, hgoal']

/-- Runtime/kernel state paired with its proved operational/spec image. -/
structure KernelStateWitness (db : RuntimeDB) (pr : RuntimeProofState) where
  Γ : OperationalDatabase
  fr : OperationalFrame
  expr : OperationalExpr
  h_db : toOperationalDatabase db = some Γ
  h_frame : toOperationalFrame db pr.frame = some fr
  h_expr : expr = toOperationalExpr pr.fmla

def mkKernelStateWitness? (db : RuntimeDB) (pr : RuntimeProofState) :
    Option (KernelStateWitness db pr) :=
  match hdb : toOperationalDatabase db with
  | none => none
  | some Γ =>
      match hfr : toOperationalFrame db pr.frame with
      | none => none
      | some fr =>
          some
            { Γ := Γ
              fr := fr
              expr := toOperationalExpr pr.fmla
              h_db := hdb
              h_frame := hfr
              h_expr := rfl }

/-- Re-export the existing `mm-lean4` operational carrier profile so mettapedia
can consume the verified state names directly. -/
abbrev operationalStateCarriers := Metamath.OperationalBridge.stateCarriers

end Mettapedia.Languages.Metamath.MMLean4Bridge
