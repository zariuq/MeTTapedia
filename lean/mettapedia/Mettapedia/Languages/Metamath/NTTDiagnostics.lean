import Mettapedia.Languages.Metamath.LanguageDefDSL
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.Framework.CategoryBridge
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Metamath OSLF → NTT Diagnostics

This module extracts small but real NTT-facing facts from the authored
Metamath `languageDef!` lane.

Positive examples:
- the compile pipeline exposes genuine unary constructor crossings such as
  `Lower : Database → LowerState` and
  `CompileAfterLower : LowerState → CompileState`;
- the staged path `Database → LowerState → CompileState` acts exactly as the
  expected wrapped compiler front-end;
- a concrete `Compile` state has a genuine one-step modal witness into the
  lowering phase.

Negative example:
- we do not pretend the NTT layer already captures the whole multi-step
  compilation proof; this file only extracts the first structurally meaningful
  categorical/modal facts from the real authored DSL.
-/

namespace Mettapedia.Languages.Metamath.NTTDiagnostics

open Mettapedia.Languages.Metamath.LanguageDefDSL
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.ConstructorCategory

def mmStmtSort : LangSort metamathCore :=
  LangSort.mk' metamathCore "Stmt" (by native_decide)

def mmDatabaseSort : LangSort metamathCore :=
  LangSort.mk' metamathCore "Database" (by native_decide)

def mmLowerStateSort : LangSort metamathCore :=
  LangSort.mk' metamathCore "LowerState" (by native_decide)

def mmCompileStateSort : LangSort metamathCore :=
  LangSort.mk' metamathCore "CompileState" (by native_decide)

theorem dbOne_crossing :
    ("DbOne", "Stmt", "Database") ∈ unaryCrossings metamathCore := by
  native_decide

theorem lower_crossing :
    ("Lower", "Database", "LowerState") ∈ unaryCrossings metamathCore := by
  native_decide

theorem compile_crossing :
    ("Compile", "Database", "CompileState") ∈ unaryCrossings metamathCore := by
  native_decide

theorem compileAfterLower_crossing :
    ("CompileAfterLower", "LowerState", "CompileState") ∈ unaryCrossings metamathCore := by
  native_decide

def dbOneArrow : SortArrow metamathCore mmStmtSort mmDatabaseSort :=
  ⟨"DbOne", dbOne_crossing⟩

def lowerArrow : SortArrow metamathCore mmDatabaseSort mmLowerStateSort :=
  ⟨"Lower", lower_crossing⟩

def compileArrow : SortArrow metamathCore mmDatabaseSort mmCompileStateSort :=
  ⟨"Compile", compile_crossing⟩

def compileAfterLowerArrow : SortArrow metamathCore mmLowerStateSort mmCompileStateSort :=
  ⟨"CompileAfterLower", compileAfterLower_crossing⟩

def compileLowerStagePath : SortPath metamathCore mmDatabaseSort mmCompileStateSort :=
  lowerArrow.toPath.comp compileAfterLowerArrow.toPath

def wffSym : Pattern := .fvar "wff"

def phSym : Pattern := .fvar "ph"

def ax1Label : Pattern := .fvar "ax1"

def minimalMath : Pattern :=
  .apply "MathMore" [wffSym, .apply "MathOne" [phSym]]

def minimalAxiomStmt : Pattern :=
  .apply "Axiom" [ax1Label, minimalMath]

def minimalAxiomDb : Pattern :=
  .apply "DbOne" [minimalAxiomStmt]

def minimalCompileStart : Pattern :=
  .apply "Compile" [minimalAxiomDb]

def minimalCompileAfterLower : Pattern :=
  .apply "CompileAfterLower" [.apply "Lower" [minimalAxiomDb]]

example : arrowSem metamathCore dbOneArrow minimalAxiomStmt = minimalAxiomDb := rfl

example : arrowSem metamathCore compileArrow minimalAxiomDb = minimalCompileStart := rfl

example :
    pathSem metamathCore compileLowerStagePath minimalAxiomDb = minimalCompileAfterLower := rfl

def stmtDatabaseOrbitPred (p : Pattern) : Prop :=
  ∃ a : LangSort metamathCore, ∃ h : SortPath metamathCore a mmDatabaseSort,
    p = pathSem metamathCore h minimalAxiomStmt

theorem stmtDatabaseOrbit_natural :
    languageSortPredNaturality metamathCore mmDatabaseSort minimalAxiomStmt
      stmtDatabaseOrbitPred := by
  intro a _ g h _
  exact ⟨a, g.comp h, rfl⟩

noncomputable def stmtDatabaseOrbitFiber : languageSortFiber metamathCore mmDatabaseSort :=
  languageSortFiber_ofPatternPred metamathCore mmDatabaseSort minimalAxiomStmt
    stmtDatabaseOrbitPred stmtDatabaseOrbit_natural

theorem dbOne_in_stmtDatabaseOrbitFiber :
    dbOneArrow.toPath ∈
      stmtDatabaseOrbitFiber.obj (Opposite.op (ConstructorObj.mk mmStmtSort)) := by
  change dbOneArrow.toPath ∈
      (languageSortFiber_ofPatternPred metamathCore mmDatabaseSort minimalAxiomStmt
        stmtDatabaseOrbitPred stmtDatabaseOrbit_natural).obj
        (Opposite.op (ConstructorObj.mk mmStmtSort))
  rw [languageSortFiber_ofPatternPred_mem_iff]
  exact ⟨mmStmtSort, dbOneArrow.toPath, rfl⟩

theorem minimalCompile_begin_diamond :
    langDiamond metamathCore (fun q => q = minimalCompileAfterLower) minimalCompileStart := by
  rw [langDiamond_spec]
  refine ⟨minimalCompileAfterLower, ?_, rfl⟩
  apply exec_to_langReducesUsing
    (relEnv := Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
    (lang := metamathCore)
  simpa [langReducesExecUsing] using
    (show minimalCompileAfterLower ∈
        rewriteWithContextWithPremises metamathCore minimalCompileStart from by
      native_decide)

end Mettapedia.Languages.Metamath.NTTDiagnostics
