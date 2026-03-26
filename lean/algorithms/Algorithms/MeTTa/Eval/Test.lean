import Algorithms.MeTTa.Eval.Eval

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Eval

def s0 : Session := {}

private def pp : Pattern → String
  | .apply c [] => c
  | .apply c args => s!"({c} {" ".intercalate (args.map pp)})"
  | .fvar n => s!"${n}"
  | _ => "?"

private def ppList (ps : List Pattern) : String :=
  s!"[{", ".intercalate (ps.map pp)}]"

#eval do
  -- Arithmetic
  IO.println s!"(+ 1 2) = {ppList (eval s0 (.apply "+" [.apply "1" [], .apply "2" []]))}"
  IO.println s!"(+ (+ 1 2) 3) = {ppList (eval s0 (.apply "+" [.apply "+" [.apply "1" [], .apply "2" []], .apply "3" []]))}"
  IO.println s!"(* 3 4) = {ppList (eval s0 (.apply "*" [.apply "3" [], .apply "4" []]))}"
  IO.println s!"(< 1 2) = {ppList (eval s0 (.apply "<" [.apply "1" [], .apply "2" []]))}"

  -- Equation rewriting
  let s1 : Session := { rules := [
    { name := "r1", left := .apply "f" [.apply "a" []], right := .apply "b" [] },
    { name := "r2", left := .apply "g" [.fvar "x"], right := .apply "pair" [.fvar "x", .fvar "x"] }
  ]}
  IO.println s!"(f a) = {ppList (eval s1 (.apply "f" [.apply "a" []]))}"
  IO.println s!"(g hello) = {ppList (eval s1 (.apply "g" [.apply "hello" []]))}"

  -- Pattern ops
  IO.println s!"(car-atom (A B C)) = {ppList (eval s0 (.apply "car-atom" [.apply "" [.apply "A" [], .apply "B" [], .apply "C" []]]))}"
  IO.println s!"(cdr-atom (A B C)) = {ppList (eval s0 (.apply "cdr-atom" [.apply "" [.apply "A" [], .apply "B" [], .apply "C" []]]))}"

  -- If
  IO.println s!"(if True yes no) = {ppList (eval s0 (.apply "if" [.apply "True" [], .apply "yes" [], .apply "no" []]))}"
  IO.println s!"(if False yes no) = {ppList (eval s0 (.apply "if" [.apply "False" [], .apply "yes" [], .apply "no" []]))}"

  -- Let
  IO.println s!"(let $x 42 $x) = {ppList (eval s0 (.apply "let" [.fvar "x", .apply "42" [], .fvar "x"]))}"

  -- Superpose
  IO.println s!"(superpose (A B C)) = {ppList (eval s0 (.apply "superpose" [.apply "" [.apply "A" [], .apply "B" [], .apply "C" []]]))}"

  -- Unify
  IO.println s!"(unify a a yes no) = {ppList (eval s0 (.apply "unify" [.apply "a" [], .apply "a" [], .apply "yes" [], .apply "no" []]))}"
  IO.println s!"(unify a b yes no) = {ppList (eval s0 (.apply "unify" [.apply "a" [], .apply "b" [], .apply "yes" [], .apply "no" []]))}"

  -- Match against space
  let s2 : Session := { space := [
    .apply "Fact" [.apply "cat" [], .apply "animal" []],
    .apply "Fact" [.apply "dog" [], .apply "animal" []]
  ]}
  IO.println s!"match Fact = {ppList (eval s2 (.apply "match" [.apply "&self" [], .apply "Fact" [.fvar "x", .apply "animal" []], .fvar "x"]))}"
