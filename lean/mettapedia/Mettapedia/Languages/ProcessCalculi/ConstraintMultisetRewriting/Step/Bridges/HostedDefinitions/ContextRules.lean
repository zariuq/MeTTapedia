import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuleBuilder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ControlProtocol
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DirectedAnswers.Data

/-!
# Finite source equations for directed context traversal and value requests

Each entry is an actual binder-core equation. Traversal selects a redex by
moving into one child and recording the other children as literal context
data. Plugging reverses that route. Primitive beta invokes the explicit
substitution helper. No conversion test or object reduction proposition is a
premise of these source rules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions
namespace ContextRules

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Normalization
open SourceLanguage SourceLanguage.Elaboration
open RuleBuilder

abbrev Rule := ProgramBinders.Equation MSig [] ()

def active {n : Nat} (phase : String) (arguments : List (Template n)) : Template n :=
  node activeTag [node phase arguments]

def binary (tag leftFrame rightFrame : String) : List Rule := [
  equation (n := 4)
    (active "hd-seek" [node tag [slot 0, slot 1], slot 2, slot 3])
    (active "hd-seek" [slot 0, node leftFrame [slot 1, slot 2], slot 3]),
  equation (n := 4)
    (active "hd-seek" [node tag [slot 0, slot 1], slot 2, slot 3])
    (active "hd-seek" [slot 1, node rightFrame [slot 0, slot 2], slot 3]),
  equation (n := 4)
    (active "hd-plug" [slot 0, node leftFrame [slot 1, slot 2], slot 3])
    (active "hd-plug" [node tag [slot 0, slot 1], slot 2, slot 3]),
  equation (n := 4)
    (active "hd-plug" [slot 0, node rightFrame [slot 1, slot 2], slot 3])
    (active "hd-plug" [node tag [slot 1, slot 0], slot 2, slot 3])]

def unary (tag frame : String) : List Rule := [
  equation (n := 3)
    (active "hd-seek" [node tag [slot 0], slot 1, slot 2])
    (active "hd-seek" [slot 0, node frame [slot 1], slot 2]),
  equation (n := 3)
    (active "hd-plug" [slot 0, node frame [slot 1], slot 2])
    (active "hd-plug" [node tag [slot 0], slot 1, slot 2])]

def identity : List Rule := [
  equation (n := 5)
    (active "hd-seek" [node "prime-tm-id" [slot 0, slot 1, slot 2], slot 3, slot 4])
    (active "hd-seek" [slot 0, node "hd-context-id-type" [slot 1, slot 2, slot 3], slot 4]),
  equation (n := 5)
    (active "hd-seek" [node "prime-tm-id" [slot 0, slot 1, slot 2], slot 3, slot 4])
    (active "hd-seek" [slot 1, node "hd-context-id-left" [slot 0, slot 2, slot 3], slot 4]),
  equation (n := 5)
    (active "hd-seek" [node "prime-tm-id" [slot 0, slot 1, slot 2], slot 3, slot 4])
    (active "hd-seek" [slot 2, node "hd-context-id-right" [slot 0, slot 1, slot 3], slot 4]),
  equation (n := 5)
    (active "hd-plug" [slot 0, node "hd-context-id-type" [slot 1, slot 2, slot 3], slot 4])
    (active "hd-plug" [node "prime-tm-id" [slot 0, slot 1, slot 2], slot 3, slot 4]),
  equation (n := 5)
    (active "hd-plug" [slot 0, node "hd-context-id-left" [slot 1, slot 2, slot 3], slot 4])
    (active "hd-plug" [node "prime-tm-id" [slot 1, slot 0, slot 2], slot 3, slot 4]),
  equation (n := 5)
    (active "hd-plug" [slot 0, node "hd-context-id-right" [slot 1, slot 2, slot 3], slot 4])
    (active "hd-plug" [node "prime-tm-id" [slot 1, slot 2, slot 0], slot 3, slot 4])]

def routing : List Rule := [
  equation (n := 3)
    (active "hd-seek" [slot 0, slot 1, slot 2])
    (active "hd-root" [slot 0, node "hd-main-plug" [slot 1, slot 2]]),
  equation (n := 3)
    (active "hd-resume" [slot 0, node "hd-main-plug" [slot 1, slot 2]])
    (active "hd-plug" [slot 0, slot 1, slot 2]),
  equation (n := 2)
    (active "hd-plug" [slot 0, node "hd-context-empty" [], slot 1])
    (active "hd-resume" [slot 0, slot 1])]

def traversal : List Rule :=
  routing ++
  binary "prime-tm-pi" "hd-context-pi-domain" "hd-context-pi-codomain" ++
  binary "prime-tm-sigma" "hd-context-sigma-domain" "hd-context-sigma-codomain" ++
  identity ++
  unary "prime-tm-lam" "hd-context-lam" ++
  binary "prime-tm-app" "hd-context-app-function" "hd-context-app-argument" ++
  binary "prime-tm-pair" "hd-context-pair-first" "hd-context-pair-second" ++
  unary "prime-tm-fst" "hd-context-first" ++
  unary "prime-tm-snd" "hd-context-second" ++
  unary "prime-tm-refl" "hd-context-refl"

def primitive : List Rule := [
  equation (n := 3)
    (active "hd-root" [node "prime-tm-app" [node "prime-tm-lam" [slot 0], slot 1], slot 2])
    (active "hd-subst-zero" [slot 1, literal (encodeNat 0), slot 0, slot 2]),
  equation (n := 3)
    (active "hd-root" [node "prime-tm-fst" [node "prime-tm-pair" [slot 0, slot 1]], slot 2])
    (active "hd-resume" [slot 0, slot 2]),
  equation (n := 3)
    (active "hd-root" [node "prime-tm-snd" [node "prime-tm-pair" [slot 0, slot 1]], slot 2])
    (active "hd-resume" [slot 1, slot 2])]

def driver : List Rule := [
  equation (n := 2)
    (active "hd-eval" [slot 0, slot 1])
    (active "hd-value" [slot 0, slot 1]),
  equation (n := 2)
    (active "hd-eval" [slot 0, slot 1])
    (active "hd-seek" [slot 0, node "hd-context-empty" [], node "hd-main-eval-next" [slot 1]]),
  equation (n := 2)
    (active "hd-resume" [slot 0, node "hd-main-eval-next" [slot 1]])
    (active "hd-eval" [slot 0, slot 1]),
  equation (n := 1)
    (active "hd-resume" [slot 0, node "hd-main-finish" []])
    (node doneTag [slot 0]),
  equation (n := 1)
    (active "hd-value" [literal (encodeTm (TowerVectorsModel.zeroC : Tower.Tm 0)), slot 0])
    (active "hd-resume" [literal (encodeTm (TowerVectorsModel.zeroC : Tower.Tm 0)), slot 0]),
  equation (n := 1)
    (active "hd-value" [literal (encodeTm (TowerVectorsModel.ttC : Tower.Tm 0)), slot 0])
    (active "hd-resume" [literal (encodeTm (TowerVectorsModel.ttC : Tower.Tm 0)), slot 0]),
  equation (n := 2)
    (active "hd-value" [node "prime-tm-app" [literal (encodeTm (.const TowerNumbersModel.succ : Tower.Tm 0)), slot 0], slot 1])
    (active "hd-value" [slot 0, node "hd-main-value-succ" [slot 1]]),
  equation (n := 2)
    (active "hd-resume" [slot 0, node "hd-main-value-succ" [slot 1]])
    (active "hd-resume" [node "prime-tm-app" [literal (encodeTm (.const TowerNumbersModel.succ : Tower.Tm 0)), slot 0], slot 1]),
  equation (n := 3)
    (active "hd-value" [node "prime-tm-pair" [slot 0, slot 1], slot 2])
    (active "hd-value" [slot 0, node "hd-main-value-pair-first" [slot 1, slot 2]]),
  equation (n := 3)
    (active "hd-resume" [slot 0, node "hd-main-value-pair-first" [slot 1, slot 2]])
    (active "hd-value" [slot 1, node "hd-main-value-pair-second" [slot 0, slot 2]]),
  equation (n := 3)
    (active "hd-resume" [slot 0, node "hd-main-value-pair-second" [slot 1, slot 2]])
    (active "hd-resume" [node "prime-tm-pair" [slot 1, slot 0], slot 2])]

def fixed : List Rule := traversal ++ primitive ++ driver

end ContextRules
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions
