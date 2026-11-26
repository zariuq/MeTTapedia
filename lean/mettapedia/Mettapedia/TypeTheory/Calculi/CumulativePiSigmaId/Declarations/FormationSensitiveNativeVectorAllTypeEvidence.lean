import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAll
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorReplayTemplates
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorTypingContexts

/-! Generated finite evidence; independently replayed by the checking companion. -/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.TypeFormation
open Presentation Declaration
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorReplayTemplates

private abbrev S (n : Nat) := StructuralConversionCode.StepCode Tower.Head NativeVectorAll.decoder.Code n
private abbrev C (n : Nat) := StructuralConversionCode.Code Tower.Head NativeVectorAll.decoder.Code n
private abbrev T (n : Nat) := StructuralTypingReplay.Code Tower.Head C n
private abbrev X (n : Nat) := StructuralTypingReplay.ContextCode Tower.Head C n

private def e13 : X 3 :=
.snoc (replay_2b923eba459954dceaf0) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2006796238039c1078f5) (replay_2a0decba183f967a7699)

private def e27 : X 4 :=
.snoc (e13) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (replay_be261adb759aa3486f8c)

private def e366 : T 8 :=
Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorTypingContexts.assemble_6562d93d6c87394cce14 8 (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_773364d509161a7cfc0c) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (replay_9bb95864b7a437c86ef2) (replay_07c41680d17703d7171f)

private def e368 : T 6 :=
Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorTypingContexts.assemble_a951cfdc4e886c32b0c9 6 (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_926d1059d18a7acb855f) (replay_46d87b945667e8b9c6f9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9293fa3cbe0cc12a361b) (replay_0263d1c79861444bbc2b) (e366)

private def e370 : T 4 :=
Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorTypingContexts.assemble_a951cfdc4e886c32b0c9 4 (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0a4c305bb1a5f667cf5a) (replay_3dba47e0d66dd5881da1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_338d0b8a48f1a43dbe00) (replay_b7955d87d66cc2356da8) (e368)

private def e371 : T 4 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1307b628e74cbf939cd4) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fd75b7ede071eab44538) (replay_6c7163c1b19e471e9892) (e370)

private def e372 : T 4 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7090374f1485408a1741) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3f8fd0cbbad6bfbc5baa) (e371) (replay_f89a0d3fd4af1bf7786d)

private def e373 : T 4 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d2fe1eb531662373187) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5978e1f6d4b31cb31598) (e372) (replay_f89a0d3fd4af1bf7786d)

def submission : FormationSensitiveElaboration.Submission Tower.Head NativeVectorAll.decoder.Code 4 :=
{ context := e27, term := e373 }


end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.TypeFormation
