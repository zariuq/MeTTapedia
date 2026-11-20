import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.Program
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalProbe

/-!
# Structural normal-form scanner syntax over the actual compiled keys

Every scanner clause first probes the original root call and then scans its
native term children. Scalar variable, constant and head fields are retained
as data. The scanner returns a held marker. Its equation names use the first
real routing site's three holes; its four binders use distinct real prefix
sites of the compiled program.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScanner

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation

def nodeAt {X : Type} {declaration : X → MetaArity MSig}
    (tag : String) (children : List (Term (signature MSig declaration) [] ())) :
    Term (signature MSig declaration) [] () :=
  Toolkit.tupleAt (Toolkit.symAt tag :: children)

def scanTag : String := "hd-normal-scan"
def markerTag : String := "hd-normal"
def stopTag : String := "hd-normal-probe-stop"

def marker {X : Type} (declaration : X → MetaArity MSig) :
    Term (signature MSig declaration) [] () := Toolkit.symAt markerTag

def stopAt {X : Type} (declaration : X → MetaArity MSig) :
    Term (signature MSig declaration) [] () := Toolkit.symAt stopTag

def scanAt {X : Type} {declaration : X → MetaArity MSig}
    (datum : Term (signature MSig declaration) [] ()) :
    Term (signature MSig declaration) [] () := nodeAt scanTag [datum]

def rootAt {X : Type} {declaration : X → MetaArity MSig}
    (datum : Term (signature MSig declaration) [] ()) :
    Term (signature MSig declaration) [] () :=
  nodeAt activeTag [nodeAt "hd-root" [datum, stopAt declaration]]

def probeAt {X : Type} {declaration : X → MetaArity MSig}
    (datum : Term (signature MSig declaration) [] ()) :
    Term (signature MSig declaration) [] () := NormalProbe.wrap (rootAt datum)

variable {dev : NativeTypesOnTheStep.Computing.Definitions.Development} (built : Compiled dev)

theorem at_least_five : 5 ≤ built.rules.length := by
  change 5 ≤ (ProgramLayout.rows RuntimeSubstitution.rules built.authored).length
  simp only [ProgramLayout.rows, List.length_append]
  have prefixBound : 5 ≤ ContextRules.fixed.length := by decide +kernel
  omega

def site (index : Fin 5) : (BinderCore.keys built.rules).Site :=
  ⟨index.val, lt_of_lt_of_le index.isLt (at_least_five built)⟩

theorem site_injective : Function.Injective (site built) := by
  intro first second same
  apply Fin.ext
  change (site built first).val = (site built second).val
  exact congrArg (fun candidate : Fin built.rules.length => candidate.val) same

theorem first_rule : built.rules.get (site built 0) = ContextRules.routing[0] := rfl
theorem second_rule : built.rules.get (site built 1) = ContextRules.routing[1] := rfl
theorem third_rule : built.rules.get (site built 2) = ContextRules.routing[2] := rfl
theorem fourth_rule : built.rules.get (site built 3) =
    (ContextRules.binary "prime-tm-pi" "hd-context-pi-domain" "hd-context-pi-codomain")[0] := rfl
theorem fifth_rule : built.rules.get (site built 4) =
    (ContextRules.binary "prime-tm-pi" "hd-context-pi-domain" "hd-context-pi-codomain")[1] := rfl

def hole (index : Fin 3) : (built.rules.get (site built 0)).Holes := index

theorem hole_arity (index : Fin 3) :
    (built.rules.get (site built 0)).arity (hole built index) = ([], ()) := rfl

def key (index : Fin 3) : (BinderCore.keys built.rules).Key := ⟨site built 0, hole built index⟩

theorem key_arity (index : Fin 3) :
    (BinderCore.keys built.rules).arity (key built index) = ([], ()) := rfl

def datum (index : Fin 3) : Data (BinderCore.keys built.rules) [] () :=
  nameAt (BinderCore.keys built.rules) [] (key built index)

inductive Constructor where
  | var | const | head | pi | sigma | id | lam | app | pair | fst | snd | refl
  deriving DecidableEq

def Constructor.all : List Constructor :=
  [.var, .const, .head, .pi, .sigma, .id, .lam, .app, .pair, .fst, .snd, .refl]

def Constructor.tag : Constructor → String
  | .var => "prime-tm-var"
  | .const => "prime-tm-const"
  | .head => "prime-tm-head"
  | .pi => "prime-tm-pi"
  | .sigma => "prime-tm-sigma"
  | .id => "prime-tm-id"
  | .lam => "prime-tm-lam"
  | .app => "prime-tm-app"
  | .pair => "prime-tm-pair"
  | .fst => "prime-tm-fst"
  | .snd => "prime-tm-snd"
  | .refl => "prime-tm-refl"

def Constructor.fields : Constructor → List (Fin 3)
  | .pi | .sigma | .app | .pair => [0, 1]
  | .id => [0, 1, 2]
  | _ => [0]

def Constructor.children : Constructor → List (Fin 3)
  | .var | .const | .head => []
  | .pi | .sigma | .app | .pair => [0, 1]
  | .id => [0, 1, 2]
  | _ => [0]

def pattern (kind : Constructor) : Data (BinderCore.keys built.rules) [] () :=
  nodeAt kind.tag (kind.fields.map (datum built))

def childTest {Ty : Type} (bindSite : Fin 5) (child : Fin 3)
    (continuation : Comp (BinderCore.keys built.rules) [] () Ty) :
    Comp (BinderCore.keys built.rules) [] () Ty :=
  .let_ (site built bindSite) (marker (fam (BinderCore.keys built.rules)))
    (.apply (scanAt (datum built child))) continuation

def childTests {Ty : Type} (kind : Constructor) :
    Comp (BinderCore.keys built.rules) [] () Ty :=
  let finish := Comp.ret (marker (fam (BinderCore.keys built.rules)))
  match kind with
  | .var | .const | .head => finish
  | .pi | .sigma | .app | .pair =>
      childTest built 2 0 (childTest built 3 1 finish)
  | .id => childTest built 2 0 (childTest built 3 1 (childTest built 4 2 finish))
  | _ => childTest built 2 0 finish

def rootTest {Ty : Type} (term : Data (BinderCore.keys built.rules) [] ())
    (continuation : Comp (BinderCore.keys built.rules) [] () Ty) :
    Comp (BinderCore.keys built.rules) [] () Ty :=
  .let_ (site built 1) (probeAt term) (.apply (probeAt term)) continuation

def equation (D : Discipline MSig [] ()) (kind : Constructor) :
    SourceLanguage.Equation (BinderCore.keys built.rules) [] () D.Ty :=
  ⟨site built 0, scanAt (pattern built kind),
    rootTest built (pattern built kind) (childTests built kind)⟩

def equations (D : Discipline MSig [] ()) :
    List (SourceLanguage.Equation (BinderCore.keys built.rules) [] () D.Ty) :=
  Constructor.all.map (equation built D)

def query {Ty : Type} (term : MClosed) : Comp (BinderCore.keys built.rules) [] () Ty :=
  .apply (scanAt (Rigid.includeTerm (fam (BinderCore.keys built.rules)) term))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScanner
