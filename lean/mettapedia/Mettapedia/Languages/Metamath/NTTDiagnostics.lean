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
  LangSort.mk' metamathCore "Stmt" (by decide)

def mmDatabaseSort : LangSort metamathCore :=
  LangSort.mk' metamathCore "Database" (by decide)

def mmLowerStateSort : LangSort metamathCore :=
  LangSort.mk' metamathCore "LowerState" (by decide)

def mmCompileStateSort : LangSort metamathCore :=
  LangSort.mk' metamathCore "CompileState" (by decide)

theorem dbOne_crossing :
    ("DbOne", "Stmt", "Database") ∈ unaryCrossings metamathCore := by
  decide

theorem lower_crossing :
    ("Lower", "Database", "LowerState") ∈ unaryCrossings metamathCore := by
  decide

theorem compile_crossing :
    ("Compile", "Database", "CompileState") ∈ unaryCrossings metamathCore := by
  decide

theorem compileAfterLower_crossing :
    ("CompileAfterLower", "LowerState", "CompileState") ∈ unaryCrossings metamathCore := by
  decide

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
  change stmtDatabaseOrbitPred (pathSem metamathCore dbOneArrow.toPath minimalAxiomStmt)
  exact ⟨mmStmtSort, dbOneArrow.toPath, rfl⟩

theorem minimalCompile_begin_diamond :
    langDiamond metamathCore (fun q => q = minimalCompileAfterLower) minimalCompileStart := by
  rw [langDiamond_spec]
  refine ⟨minimalCompileAfterLower, ?_, rfl⟩
  apply exec_to_langReducesUsing
    (relEnv := Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
    (lang := metamathCore)
  have hmem : minimalCompileAfterLower ∈
      rewriteWithContextWithPremisesUsing
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty metamathCore minimalCompileStart := by
    decide +kernel
  simpa [langReducesExecUsing] using hmem

/- RUN the OSLF algorithm on the authored `metamathCore` GSLT and OUTPUT the
    NTT: the full list of constructor-crossings (the native-type arrows). -/
#eval unaryCrossings metamathCore

/-! ## Multi-statement compile coverage oracle

Nothing else drives the ≥2-statement compile path (`KDbCons` kont states only
arise via `CompileReturnStmtDbMore`, which needs a `DbMore` database). This
gate runs the deterministic driver end-to-end and demands the pipeline lands
on `CompileDone` — the executable safety net under the flatten theorem and
under any machine-rule cleanup. -/

def twoStmtDb : Pattern :=
  .apply "DbMore" [minimalAxiomStmt, .apply "DbOne" [minimalAxiomStmt]]

def twoStmtCompileNF : Pattern :=
  Mettapedia.OSLF.MeTTaIL.Match.rewriteToNormalForm metamathCore
    (.apply "Compile" [twoStmtDb])

/-! PERMANENT REGRESSION FIXTURE (do not weaken to a head-only check).
History: until 2026-07-09 the `languageDef!` elaborator turned bare nullary
constructor names in rewrite patterns into fvar WILDCARDS — `ReturnDbDone`'s
`KDone` matched any kont and this very fixture compiled to statement-dropping
garbage (with a head-only check passing!). Fixed generically by
`LanguageDef.resolveNullaryPatterns` (applied by the macro); the content
assertion below is the tripwire that keeps it fixed. -/
#guard (match twoStmtCompileNF with
        | .apply "CompileDone"
            [.apply "CoreProgCat"
              [.apply "CoreProgOne" [.apply "CoreAxiom" [a1, m1]],
               .apply "CoreProgOne" [.apply "CoreAxiom" [a2, m2]]]] =>
          decide (a1 = ax1Label) && decide (m1 = minimalMath) &&
          decide (a2 = ax1Label) && decide (m2 = minimalMath)
        | _ => false)

/-! Empty-block (`${ $}`) coverage (bug B, complete): legal Metamath,
previously unparseable; now compiles to the bare scope bracket — content
asserted (post-resolution, nullary constructors are `apply`-form). -/
def emptyBlockCompileNF : Pattern :=
  Mettapedia.OSLF.MeTTaIL.Match.rewriteToNormalForm metamathCore
    (.apply "Compile" [.apply "DbOne" [.apply "BlockEmpty" []]])

#guard (match emptyBlockCompileNF with
        | .apply "CompileDone"
            [.apply "CoreProgCat"
              [.apply "CoreProgOne" [.apply "CoreEnterScope" []],
               .apply "CoreProgOne" [.apply "CoreExitScope" []]]] => true
        | _ => false)

end Mettapedia.Languages.Metamath.NTTDiagnostics
