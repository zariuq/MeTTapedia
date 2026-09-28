import Mettapedia.GSLT.LanguageDef.InferenceFiniteHornGSLTRender

/-!
# An executable presentation of an Agda core fragment

This is object-language rule data, not a translation of Agda propositions into
Lean propositions. The native Horn realization executes these rules directly.
The fragment has finite universe levels, dependent functions, dependent pairs,
the eta unit record, natural numbers, and acyclic transparent definitions.

Bound variables are de Bruijn indices in the object syntax. Rule metavariables
are distinct from those indices. Substitution and weakening are judgments of
the presentation; no host substitution enters a guest binder implicitly.

General data/record admission, level polymorphism, Prop, inductive-recursive
definitions, and cubical operations remain outside this fragment.
-/

namespace Mettapedia.Languages.Agda.Core

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

declare_syntax_cat agpat
syntax ident : agpat
syntax "?" ident : agpat
syntax "(" ident agpat* ")" : agpat
syntax "ap[" agpat "]" : term
macro_rules
  | `(ap[ $x:ident ]) => `(Pattern.apply $(Lean.quote x.getId.toString) [])
  | `(ap[ ?$x:ident ]) => `(Pattern.fvar $(Lean.quote x.getId.toString))
  | `(ap[ ($h:ident $xs:agpat*) ]) =>
    `(Pattern.apply $(Lean.quote h.getId.toString) [$[ap[ $xs ]],*])

mutual
private def vars : Pattern → List String
  | .fvar x => [x]
  | .apply _ xs => varsList xs
  | _ => []

private def varsList : List Pattern → List String
  | [] => []
  | x :: xs => vars x ++ varsList xs
end

private def r (name : String) (head : Pattern) (body : List Pattern := []) : RuleSchema :=
  { id := ⟨name⟩
    metavariables := ((vars head ++ body.flatMap vars).eraseDups).map (·, 0)
    premises := body
    conclusion := head }

/-- Binding arity of each term argument. Univ and Var have separate index rules. -/
def termShapes : List (String × List Nat) :=
  [("Pi", [0, 1]), ("Lam", [1]), ("App", [0, 0]), ("Ann", [0, 0]),
   ("Sigma", [0, 1]), ("Pair", [0, 0]), ("Fst", [0]), ("Snd", [0]),
   ("Suc", [0]), ("Nat", []), ("Zero", []), ("Unit", []), ("Star", []),
   ("Empty", []), ("NatSuc", []), ("Natrec", [0, 0, 0, 0, 0])]

private def v (x : String) : Pattern := .fvar x
private def a (x : String) (args : List Pattern := []) : Pattern := .apply x args
private def next (x : Pattern) : Pattern := a "S" [x]

/-- Structural rules are derived from the actual binding signature. -/
private def structuralRules (shape : String × List Nat) : List RuleSchema := Id.run do
  let (head, arities) := shape
  let indices := List.range arities.length
  let inputs := indices.map fun i => v s!"x{i}"
  let outputs := indices.map fun i => v s!"y{i}"
  let children := indices.zip arities
  let scopePremises := children.map fun (i, n) =>
    a "Scope" [if n == 0 then v "d" else next (v "d"), v s!"x{i}"]
  let shifts := children.map fun (i, n) =>
    a "Shift" [if n == 0 then v "k" else next (v "k"), v s!"x{i}", v s!"y{i}"]
  let underBinder := arities.contains 1
  let substitutions := children.map fun (i, n) =>
    a "Sub" [if n == 0 then v "k" else next (v "k"),
      if n == 0 then v "u" else v "up", v s!"x{i}", v s!"y{i}"]
  return [r ("term-" ++ head) (a "Term" [a head inputs])
      (inputs.map fun t => a "Term" [t]),
     r ("scope-" ++ head) (a "Scope" [v "d", a head inputs]) scopePremises,
     r ("shift-" ++ head) (a "Shift" [v "k", a head inputs, a head outputs]) shifts,
     r ("sub-" ++ head) (a "Sub" [v "k", v "u", a head inputs, a head outputs])
       ((if underBinder then [a "Shift" [a "Z", v "u", v "up"]] else []) ++ substitutions)]

def supportRules : List RuleSchema :=
  [r "index-zero" ap[(Index Z)],
   r "index-succ" ap[(Index (S ?n))] [ap[(Index ?n)]],
   r "less-zero" ap[(Less Z (S ?n))] [ap[(Index ?n)]],
   r "less-succ" ap[(Less (S ?m) (S ?n))] [ap[(Less ?m ?n)]],
   r "ge-zero" ap[(Ge ?n Z)] [ap[(Index ?n)]],
   r "ge-succ" ap[(Ge (S ?n) (S ?m))] [ap[(Ge ?n ?m)]],
   r "different-left" ap[(Different Z (S ?n))] [ap[(Index ?n)]],
   r "different-right" ap[(Different (S ?n) Z)] [ap[(Index ?n)]],
   r "different-succ" ap[(Different (S ?n) (S ?m))] [ap[(Different ?n ?m)]],
   r "max-left" ap[(Max Z ?n ?n)] [ap[(Index ?n)]],
   r "max-right" ap[(Max (S ?n) Z (S ?n))] [ap[(Index ?n)]],
   r "max-succ" ap[(Max (S ?m) (S ?n) (S ?k))] [ap[(Max ?m ?n ?k)]],
   r "scope-var" ap[(Scope ?d (Var ?n))] [ap[(Less ?n ?d)]],
   r "scope-sort" ap[(Scope ?d (Univ ?l))] [ap[(Index ?l)]],
   r "scope-global" ap[(Scope ?d (Global ?n))] [ap[(Index ?n)]],
   r "shift-var-below" ap[(Shift ?k (Var ?n) (Var ?n))] [ap[(Less ?n ?k)]],
   r "shift-var-above" ap[(Shift ?k (Var ?n) (Var (S ?n)))] [ap[(Ge ?n ?k)]],
   r "shift-sort" ap[(Shift ?k (Univ ?l) (Univ ?l))] [ap[(Index ?l)]],
   r "shift-global" ap[(Shift ?k (Global ?n) (Global ?n))] [ap[(Index ?n)]],
   r "sub-hit" ap[(Sub ?k ?u (Var ?k) ?u)],
   r "sub-below" ap[(Sub ?k ?u (Var ?n) (Var ?n))] [ap[(Less ?n ?k)]],
   r "sub-above" ap[(Sub ?k ?u (Var (S ?n)) (Var ?n))] [ap[(Ge ?n ?k)]],
   r "sub-sort" ap[(Sub ?k ?u (Univ ?l) (Univ ?l))] [ap[(Index ?l)]],
   r "sub-global" ap[(Sub ?k ?u (Global ?n) (Global ?n))] [ap[(Index ?n)]],
   r "lookup-zero" ap[(Lookup (Cons ?A ?G) Z ?B)] [ap[(Shift Z ?A ?B)]],
   r "lookup-succ" ap[(Lookup (Cons ?A ?G) (S ?n) ?C)]
     [ap[(Lookup ?G ?n ?B)], ap[(Shift Z ?B ?C)]],
   r "def-here" ap[(DefLookup (Def ?n ?A ?t ?D) ?n ?A ?t)],
   r "def-there" ap[(DefLookup (Def ?m ?B ?u ?D) ?n ?A ?t)]
     [ap[(Different ?n ?m)], ap[(DefLookup ?D ?n ?A ?t)]],
   r "fresh-empty" ap[(Fresh ?n DNil)] [ap[(Index ?n)]],
   r "fresh-cons" ap[(Fresh ?n (Def ?m ?A ?t ?D))]
     [ap[(Different ?n ?m)], ap[(Fresh ?n ?D)]],
   r "signature-empty" ap[(Signature DNil)],
   r "signature-definition" ap[(Signature (Def ?n ?A ?t ?D))]
     [ap[(Signature ?D)], ap[(Fresh ?n ?D)], ap[(Scope Z ?A)], ap[(Scope Z ?t)],
      ap[(IsType ?D Nil ?A ?l)], ap[(Check ?D Nil ?t ?A)]],
   r "context-empty" ap[(Context ?D Nil)],
   r "context-cons" ap[(Context ?D (Cons ?A ?G))]
     [ap[(Context ?D ?G)], ap[(IsType ?D ?G ?A ?l)]]]
  ++ termShapes.flatMap structuralRules

def reductionRules : List RuleSchema :=
  [r "wh-var" ap[(Wh ?D (Var ?n) (Var ?n))],
   r "wh-sort" ap[(Wh ?D (Univ ?l) (Univ ?l))],
   r "wh-pi" ap[(Wh ?D (Pi ?A ?B) (Pi ?A ?B))],
   r "wh-sigma" ap[(Wh ?D (Sigma ?A ?B) (Sigma ?A ?B))],
   r "wh-lambda" ap[(Wh ?D (Lam ?t) (Lam ?t))],
   r "wh-pair" ap[(Wh ?D (Pair ?t ?u) (Pair ?t ?u))],
   r "wh-suc" ap[(Wh ?D (Suc ?t) (Suc ?t))],
   r "wh-successor" ap[(Wh ?D NatSuc NatSuc)],
   r "wh-nat" ap[(Wh ?D Nat Nat)], r "wh-zero" ap[(Wh ?D Zero Zero)],
   r "wh-unit" ap[(Wh ?D Unit Unit)], r "wh-star" ap[(Wh ?D Star Star)],
   r "wh-empty" ap[(Wh ?D Empty Empty)],
   r "wh-definition" ap[(Wh ?D (Global ?n) ?v)]
     [ap[(DefLookup ?D ?n ?A ?t)], ap[(Wh ?D ?t ?v)]],
   r "wh-annotation" ap[(Wh ?D (Ann ?t ?A) ?v)] [ap[(Wh ?D ?t ?v)]],
   r "wh-application" ap[(Wh ?D (App ?f ?u) ?v)]
     [ap[(Wh ?D ?f ?g)], ap[(Apply ?D ?g ?u ?v)]],
   r "apply-beta" ap[(Apply ?D (Lam ?t) ?u ?v)]
     [ap[(Sub Z ?u ?t ?b)], ap[(Wh ?D ?b ?v)]],
   r "apply-neutral" ap[(Apply ?D ?f ?u (App ?f ?u))] [ap[(Neutral ?f)]],
   r "apply-successor" ap[(Apply ?D NatSuc ?u (Suc ?u))],
   r "wh-fst" ap[(Wh ?D (Fst ?t) ?v)] [ap[(Wh ?D ?t ?p)], ap[(ProjectFst ?D ?p ?v)]],
   r "wh-snd" ap[(Wh ?D (Snd ?t) ?v)] [ap[(Wh ?D ?t ?p)], ap[(ProjectSnd ?D ?p ?v)]],
   r "fst-pair" ap[(ProjectFst ?D (Pair ?t ?u) ?v)] [ap[(Wh ?D ?t ?v)]],
   r "snd-pair" ap[(ProjectSnd ?D (Pair ?t ?u) ?v)] [ap[(Wh ?D ?u ?v)]],
   r "fst-neutral" ap[(ProjectFst ?D ?t (Fst ?t))] [ap[(Neutral ?t)]],
   r "snd-neutral" ap[(ProjectSnd ?D ?t (Snd ?t))] [ap[(Neutral ?t)]],
   r "neutral-var" ap[(Neutral (Var ?n))],
   r "neutral-app" ap[(Neutral (App ?t ?u))] [ap[(Neutral ?t)]],
   r "neutral-fst" ap[(Neutral (Fst ?t))] [ap[(Neutral ?t)]],
   r "neutral-snd" ap[(Neutral (Snd ?t))] [ap[(Neutral ?t)]]]

def typingRules : List RuleSchema :=
  [r "infer-var" ap[(Infer ?D ?G (Var ?n) ?A)] [ap[(Lookup ?G ?n ?A)]],
   r "infer-global" ap[(Infer ?D ?G (Global ?n) ?A)] [ap[(DefLookup ?D ?n ?A ?t)]],
   r "infer-sort" ap[(Infer ?D ?G (Univ ?l) (Univ (S ?l)))] [ap[(Index ?l)]],
   r "infer-pi" ap[(Infer ?D ?G (Pi ?A ?B) (Univ ?k))]
     [ap[(IsType ?D ?G ?A ?i)], ap[(IsType ?D (Cons ?A ?G) ?B ?j)], ap[(Max ?i ?j ?k)]],
   r "infer-sigma" ap[(Infer ?D ?G (Sigma ?A ?B) (Univ ?k))]
     [ap[(IsType ?D ?G ?A ?i)], ap[(IsType ?D (Cons ?A ?G) ?B ?j)], ap[(Max ?i ?j ?k)]],
   r "infer-app" ap[(Infer ?D ?G (App ?f ?u) ?C)]
     [ap[(Infer ?D ?G ?f ?T)], ap[(Wh ?D ?T (Pi ?A ?B))],
      ap[(Check ?D ?G ?u ?A)], ap[(Sub Z ?u ?B ?C)]],
   r "infer-annotation" ap[(Infer ?D ?G (Ann ?t ?A) ?A)]
     [ap[(IsType ?D ?G ?A ?l)], ap[(Check ?D ?G ?t ?A)]],
   r "infer-nat" ap[(Infer ?D ?G Nat (Univ Z))],
   r "infer-zero" ap[(Infer ?D ?G Zero Nat)],
   r "infer-suc" ap[(Infer ?D ?G (Suc ?t) Nat)] [ap[(Check ?D ?G ?t Nat)]],
   r "infer-successor" ap[(Infer ?D ?G NatSuc (Pi Nat Nat))],
   r "infer-unit" ap[(Infer ?D ?G Unit (Univ Z))],
   r "infer-star" ap[(Infer ?D ?G Star Unit)],
   r "infer-empty" ap[(Infer ?D ?G Empty (Univ Z))],
   r "infer-fst" ap[(Infer ?D ?G (Fst ?t) ?A)]
     [ap[(Infer ?D ?G ?t ?T)], ap[(Wh ?D ?T (Sigma ?A ?B))]],
   r "infer-snd" ap[(Infer ?D ?G (Snd ?t) ?C)]
     [ap[(Infer ?D ?G ?t ?T)], ap[(Wh ?D ?T (Sigma ?A ?B))],
      ap[(Sub Z (Fst ?t) ?B ?C)]],
   r "type" ap[(IsType ?D ?G ?A ?l)]
     [ap[(Infer ?D ?G ?A ?T)], ap[(Wh ?D ?T (Univ ?l))]],
   r "check-lambda" ap[(Check ?D ?G (Lam ?t) ?T)]
     [ap[(Wh ?D ?T (Pi ?A ?B))], ap[(Check ?D (Cons ?A ?G) ?t ?B)]],
   r "check-pair" ap[(Check ?D ?G (Pair ?t ?u) ?T)]
     [ap[(Wh ?D ?T (Sigma ?A ?B))], ap[(Check ?D ?G ?t ?A)],
      ap[(Sub Z ?t ?B ?C)], ap[(Check ?D ?G ?u ?C)]],
   r "check-inferred" ap[(Check ?D ?G ?t ?A)]
     [ap[(Infer ?D ?G ?t ?B)], ap[(TyEq ?D ?G ?A ?B)]],
   r "public-check" ap[(AgdaCheck ?D ?G ?t ?A)]
     [ap[(Signature ?D)], ap[(Context ?D ?G)], ap[(IsType ?D ?G ?A ?l)], ap[(Check ?D ?G ?t ?A)]],
   r "public-equal" ap[(AgdaEqual ?D ?G ?A ?t ?u)]
     [ap[(Signature ?D)], ap[(Context ?D ?G)], ap[(IsType ?D ?G ?A ?l)],
      ap[(Check ?D ?G ?t ?A)], ap[(Check ?D ?G ?u ?A)], ap[(Eq ?D ?G ?A ?t ?u)]]]

def conversionRules : List RuleSchema :=
  [r "types-whnf" ap[(TyEq ?D ?G ?A ?B)]
     [ap[(Wh ?D ?A ?a)], ap[(Wh ?D ?B ?b)], ap[(TyHeadEq ?D ?G ?a ?b)]],
   r "types-sort" ap[(TyHeadEq ?D ?G (Univ ?l) (Univ ?l))] [ap[(Index ?l)]],
   r "types-nat" ap[(TyHeadEq ?D ?G Nat Nat)],
   r "types-unit" ap[(TyHeadEq ?D ?G Unit Unit)],
   r "types-empty" ap[(TyHeadEq ?D ?G Empty Empty)],
   r "types-pi" ap[(TyHeadEq ?D ?G (Pi ?A ?B) (Pi ?C ?E))]
     [ap[(TyEq ?D ?G ?A ?C)], ap[(TyEq ?D (Cons ?A ?G) ?B ?E)]],
   r "types-sigma" ap[(TyHeadEq ?D ?G (Sigma ?A ?B) (Sigma ?C ?E))]
     [ap[(TyEq ?D ?G ?A ?C)], ap[(TyEq ?D (Cons ?A ?G) ?B ?E)]],
   r "types-neutral" ap[(TyHeadEq ?D ?G ?t ?u)] [ap[(NeEq ?D ?G ?t ?u ?A)]],
   r "equal-whnf-type" ap[(Eq ?D ?G ?A ?t ?u)]
     [ap[(Wh ?D ?A ?B)], ap[(At ?D ?G ?B ?t ?u)]],
   r "eta-function" ap[(At ?D ?G (Pi ?A ?B) ?t ?u)]
     [ap[(Shift Z ?t ?t1)], ap[(Shift Z ?u ?u1)],
      ap[(Eq ?D (Cons ?A ?G) ?B (App ?t1 (Var Z)) (App ?u1 (Var Z)))]],
   r "eta-pair" ap[(At ?D ?G (Sigma ?A ?B) ?t ?u)]
     [ap[(Eq ?D ?G ?A (Fst ?t) (Fst ?u))], ap[(Sub Z (Fst ?t) ?B ?C)],
      ap[(Eq ?D ?G ?C (Snd ?t) (Snd ?u))]],
   r "eta-unit" ap[(At ?D ?G Unit ?t ?u)],
   r "equal-sort" ap[(At ?D ?G (Univ ?l) ?t ?u)] [ap[(TyEq ?D ?G ?t ?u)]],
   r "equal-nat" ap[(At ?D ?G Nat ?t ?u)]
     [ap[(Wh ?D ?t ?a)], ap[(Wh ?D ?u ?b)], ap[(NatEq ?D ?G ?a ?b)]],
   r "equal-empty" ap[(At ?D ?G Empty ?t ?u)]
     [ap[(Wh ?D ?t ?a)], ap[(Wh ?D ?u ?b)], ap[(NeEq ?D ?G ?a ?b ?T)]],
   r "equal-neutral-type" ap[(At ?D ?G ?A ?t ?u)]
     [ap[(Neutral ?A)], ap[(Wh ?D ?t ?a)], ap[(Wh ?D ?u ?b)], ap[(NeEq ?D ?G ?a ?b ?T)]],
   r "nat-zero" ap[(NatEq ?D ?G Zero Zero)],
   r "nat-suc" ap[(NatEq ?D ?G (Suc ?a) (Suc ?b))] [ap[(Eq ?D ?G Nat ?a ?b)]],
   r "nat-neutral" ap[(NatEq ?D ?G ?a ?b)] [ap[(NeEq ?D ?G ?a ?b ?T)]],
   r "neutral-equal-var" ap[(NeEq ?D ?G (Var ?n) (Var ?n) ?A)] [ap[(Lookup ?G ?n ?A)]],
   r "neutral-equal-app" ap[(NeEq ?D ?G (App ?f ?a) (App ?g ?b) ?C)]
     [ap[(NeEq ?D ?G ?f ?g ?T)], ap[(Wh ?D ?T (Pi ?A ?B))],
      ap[(Eq ?D ?G ?A ?a ?b)], ap[(Sub Z ?a ?B ?C)]],
   r "neutral-equal-fst" ap[(NeEq ?D ?G (Fst ?t) (Fst ?u) ?A)]
     [ap[(NeEq ?D ?G ?t ?u ?T)], ap[(Wh ?D ?T (Sigma ?A ?B))]],
   r "neutral-equal-snd" ap[(NeEq ?D ?G (Snd ?t) (Snd ?u) ?C)]
     [ap[(NeEq ?D ?G ?t ?u ?T)], ap[(Wh ?D ?T (Sigma ?A ?B))],
      ap[(Sub Z (Fst ?t) ?B ?C)]]]

def requestRules : List RuleSchema :=
  [r "term-var" ap[(Term (Var ?n))] [ap[(Index ?n)]],
   r "term-sort" ap[(Term (Univ ?n))] [ap[(Index ?n)]],
   r "term-global" ap[(Term (Global ?n))] [ap[(Index ?n)]],
   r "context-shape-empty" ap[(ContextShape Nil)],
   r "context-shape-cons" ap[(ContextShape (Cons ?A ?G))]
     [ap[(Term ?A)], ap[(ContextShape ?G)]],
   r "signature-shape-empty" ap[(SignatureShape DNil)],
   r "signature-shape-cons" ap[(SignatureShape (Def ?n ?A ?t ?D))]
     [ap[(Index ?n)], ap[(Term ?A)], ap[(Term ?t)], ap[(SignatureShape ?D)]],
   r "support-check" ap[(AgdaQuery (Support (CheckRequest ?D ?G ?t ?A)) Yes)]
     [ap[(SignatureShape ?D)], ap[(ContextShape ?G)], ap[(Term ?t)], ap[(Term ?A)]],
   r "support-equal" ap[(AgdaQuery (Support (EqualRequest ?D ?G ?A ?t ?u)) Yes)]
     [ap[(SignatureShape ?D)], ap[(ContextShape ?G)], ap[(Term ?A)], ap[(Term ?t)], ap[(Term ?u)]],
   r "support-signature" ap[(AgdaQuery (Support (SignatureRequest ?D)) Yes)]
     [ap[(SignatureShape ?D)]],
   r "request-check" ap[(AgdaQuery (Decide (CheckRequest ?D ?G ?t ?A)) Yes)]
     [ap[(AgdaCheck ?D ?G ?t ?A)]],
   r "request-equal" ap[(AgdaQuery (Decide (EqualRequest ?D ?G ?A ?t ?u)) Yes)]
     [ap[(AgdaEqual ?D ?G ?A ?t ?u)]],
   r "request-signature" ap[(AgdaQuery (Decide (SignatureRequest ?D)) Yes)]
     [ap[(Signature ?D)]]]

mutual
private def heads : Pattern → List (String × Nat)
  | .apply h xs => (h, xs.length) :: headsList xs
  | _ => []

private def headsList : List Pattern → List (String × Nat)
  | [] => []
  | x :: xs => heads x ++ headsList xs
end

def recursionRules : List RuleSchema :=
  [r "nat-step-type" ap[(NatStepType ?P (Pi Nat (Pi (App ?P1 (Var Z)) (App ?P2 (Suc (Var (S Z)))))))]
     [ap[(Shift Z ?P ?P1)], ap[(Shift Z ?P1 ?P2)]],
   r "infer-natrec" ap[(Infer ?D ?G (Natrec (Univ ?l) ?P ?z ?s ?n) (App ?P ?n))]
     [ap[(Index ?l)], ap[(Check ?D ?G ?P (Pi Nat (Univ ?l)))],
      ap[(Check ?D ?G ?z (App ?P Zero))], ap[(NatStepType ?P ?T)],
      ap[(Check ?D ?G ?s ?T)], ap[(Check ?D ?G ?n Nat)]],
   r "wh-natrec" ap[(Wh ?D (Natrec ?l ?P ?z ?s ?n) ?v)]
     [ap[(Wh ?D ?n ?m)], ap[(NatReduce ?D ?l ?P ?z ?s ?m ?v)]],
   r "natrec-zero" ap[(NatReduce ?D ?l ?P ?z ?s Zero ?v)] [ap[(Wh ?D ?z ?v)]],
   r "natrec-suc" ap[(NatReduce ?D ?l ?P ?z ?s (Suc ?n) ?v)]
     [ap[(Wh ?D (App (App ?s ?n) (Natrec ?l ?P ?z ?s ?n)) ?v)]],
   r "natrec-neutral" ap[(NatReduce ?D ?l ?P ?z ?s ?n (Natrec ?l ?P ?z ?s ?n))]
     [ap[(Neutral ?n)]],
   r "neutral-natrec" ap[(Neutral (Natrec ?l ?P ?z ?s ?n))] [ap[(Neutral ?n)]],
   r "neutral-equal-natrec" ap[(NeEq ?D ?G
       (Natrec (Univ ?l) ?P ?z ?s ?n) (Natrec (Univ ?l) ?Q ?w ?t ?m) (App ?P ?n))]
     [ap[(NeEq ?D ?G ?n ?m Nat)], ap[(Eq ?D ?G (Pi Nat (Univ ?l)) ?P ?Q)],
      ap[(Eq ?D ?G (App ?P Zero) ?z ?w)], ap[(NatStepType ?P ?T)], ap[(Eq ?D ?G ?T ?s ?t)]]]

def coreRules : List RuleSchema :=
  supportRules ++ reductionRules ++ typingRules ++ conversionRules ++ requestRules ++ recursionRules

/-- All helper relations are explicit judgments. Conversion is context-indexed
and type-indexed, so it does not use the optional binary certificate root. -/
def presentation : CalculusLanguageDef := Id.run do
  let rules := coreRules
  let js := (rules.map fun rule => match rule.conclusion with
    | .apply h xs => (h, xs.length)
    | _ => ("", 0)).eraseDups
  let constructors := ((rules.flatMap fun rule =>
    heads rule.conclusion ++ rule.premises.flatMap heads).eraseDups).filter
      fun signature => !js.contains signature
  return { name := "AgdaDependentCoreV1"
           types := ["Object"]
           terms := constructors.map fun (head, arity) =>
             { label := head, category := "Object"
               params := (List.range arity).map fun i => .simple s!"x{i}" (.base "Object")
               syntaxPattern := [] }
           equations := [], rewrites := []
           judgments := js.map fun (head, arity) => { head, arity }
           rules := rules }

def rendered : Option String :=
  InferenceFiniteHornGSLTRender.renderDefinition? presentation

end Mettapedia.Languages.Agda.Core
