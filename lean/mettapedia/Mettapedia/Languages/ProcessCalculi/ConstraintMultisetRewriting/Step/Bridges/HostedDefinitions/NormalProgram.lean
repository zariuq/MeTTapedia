import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalScannerSyntax
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.PublicQuery

/-!
# An explicit source program for general normal-form results

The source evaluator has a fixed finite equation list and a bag of branch
alternatives with branch-local constraints. Its new entry either checks the
entire native datum with the structural scanner, or takes one directed
reduction through the existing context/substitution machinery and repeats.
Only the successful scan returns the original datum as a held done reply.

This module constructs the program. Scope, execution correspondence and
termination are proved separately; syntax alone is no completion certificate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalProgram

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing
open NormalScanner (nodeAt)

def evaluateTag : String := "hd-normal-eval"
def nextTag : String := "hd-normal-next"

def evaluateAt {X : Type} {declaration : X → MetaArity MSig}
    (datum : Term (signature MSig declaration) [] ()) : Term (signature MSig declaration) [] () :=
  nodeAt evaluateTag [datum]

def nextAt {X : Type} (declaration : X → MetaArity MSig) : Term (signature MSig declaration) [] () :=
  nodeAt nextTag []

def seekAt {X : Type} {declaration : X → MetaArity MSig}
    (datum : Term (signature MSig declaration) [] ()) : Term (signature MSig declaration) [] () :=
  nodeAt activeTag [nodeAt "hd-seek" [datum, nodeAt "hd-context-empty" [], nextAt declaration]]

def resumeAt {X : Type} {declaration : X → MetaArity MSig}
    (datum : Term (signature MSig declaration) [] ()) : Term (signature MSig declaration) [] () :=
  nodeAt activeTag [nodeAt "hd-resume" [datum, nextAt declaration]]

def doneAt {X : Type} {declaration : X → MetaArity MSig}
    (datum : Term (signature MSig declaration) [] ()) : Term (signature MSig declaration) [] () :=
  nodeAt doneTag [datum]

def code (term : Tower.Tm 0) : MClosed := nodeC evaluateTag [encodeTm term]

variable {dev : Definitions.Development} (built : Compiled dev)

def rootIndex (index : Fin built.rules.length) : Bool :=
  LiteralPaths.symbolAt (built.rules.get index).lhs [1, 0] == some "hd-root"

def rootIndices : List (Fin built.rules.length) := (List.finRange built.rules.length).filter (rootIndex built)

def probes (D : Discipline MSig [] ()) :
    List (SourceLanguage.Equation (BinderCore.keys built.rules) [] () D.Ty) :=
  (rootIndices built).map fun index => NormalProbe.equation (BinderCore.embedEquation built.rules index)

def driver (D : Discipline MSig [] ()) :
    List (SourceLanguage.Equation (BinderCore.keys built.rules) [] () D.Ty) :=
  let datum := NormalScanner.datum built 0
  [⟨NormalScanner.site built 0, evaluateAt datum,
      .choice
        (.let_ (NormalScanner.site built 1) (NormalScanner.marker (fam (BinderCore.keys built.rules)))
          (.apply (NormalScanner.scanAt datum)) (.ret (doneAt datum)))
        (.apply (seekAt datum))⟩,
    ⟨NormalScanner.site built 0, resumeAt datum, .apply (evaluateAt datum)⟩]

def program (D : Discipline MSig [] ()) :
    SourceLanguage.Program (BinderCore.keys built.rules) [] () D.Ty :=
  ⟨(BinderCore.program built.rules).equations ++ probes built D ++ NormalScanner.equations built D ++ driver built D,
    fun datum => .apply datum⟩

def query {Ty : Type} (term : Tower.Tm 0) : Comp (BinderCore.keys built.rules) [] () Ty :=
  PublicQuery.query RuntimeSubstitution.rules built.authored (code term)

theorem root_indices_exact (index : Fin built.rules.length) :
    index ∈ rootIndices built ↔ LiteralPaths.symbolAt (built.rules.get index).lhs [1, 0] = some "hd-root" := by
  simp [rootIndices, rootIndex]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalProgram
