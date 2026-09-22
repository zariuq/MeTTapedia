import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory

/-!
# A fixed two-sort dependent-calculus presentation in MeTTa-IL

`twoSortDependent` is a concrete `LanguageDef` originating in the historical
MeTTa-Pure experiment.
It presents dependent products and sums, identity formation/reflexivity,
a ground-type head and formation-marker head, and three beta/projection
rules. It is not a selected Prime foundation or an initiality theorem.

The presentation receives the generic OSLF construction and its modal
adjunction. This does not establish typing regularity, normalization,
universe adequacy, or a classifying universal property. Those claims require
theorems about the relevant explicit judgment and fragment. The separate
regular intrinsic calculus proves normalization under its own formation
and declaration-freedom hypotheses; those results are not a totality claim
for arbitrary terms of this language.

The two heads have the fixed interpretation `U0 : U1`, with `U1`
untyped. They are not a cumulative universe hierarchy. Identity elimination
is absent. MeTTa translation and candidate adoption are separate bridges.
-/

namespace Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.ConstructorCategory

/-! ## Language Definition -/

/-- the two-sort experiment: a small intensional dependent type theory.

    - **Sorts**: `["Tm", "Ctx"]`
    - **Tm constructors**: `U0`, `U1`, `Pi`, `Sigma`, `Id`, `Lam`, `App`,
      `Pair`, `Fst`, `Snd`, `Refl`
    - **Ctx constructors**: `CtxEmpty`, `CtxExtend`
    - **Reductions**: BetaPi, BetaSigmaFst, BetaSigmaSnd -/
def twoSortDependent : LanguageDef := {
  name := "MeTTaTwoSortExperiment",
  types := ["Tm", "Ctx"],
  terms := [
    -- U0 : Tm  (distinguished ground type)
    { label := "U0", category := "Tm", params := [],
      syntaxPattern := [.terminal "U0"] },
    -- U1 : Tm  (untyped formation marker)
    { label := "U1", category := "Tm", params := [],
      syntaxPattern := [.terminal "U1"] },
    -- Pi(A, ^B) : Tm  (dependent function type)
    { label := "Pi", category := "Tm",
      params := [.simple "A" (.base "Tm"),
                 .abstraction "B" (.arrow (.base "Tm") (.base "Tm"))],
      syntaxPattern := [.terminal "Pi", .terminal "(",
                        .nonTerminal "A", .terminal ",",
                        .nonTerminal "B", .terminal ")"] },
    -- Sigma(A, ^B) : Tm  (dependent pair type)
    { label := "Sigma", category := "Tm",
      params := [.simple "A" (.base "Tm"),
                 .abstraction "B" (.arrow (.base "Tm") (.base "Tm"))],
      syntaxPattern := [.terminal "Sigma", .terminal "(",
                        .nonTerminal "A", .terminal ",",
                        .nonTerminal "B", .terminal ")"] },
    -- Id(A, a, b) : Tm  (identity type)
    { label := "Id", category := "Tm",
      params := [.simple "A" (.base "Tm"),
                 .simple "a" (.base "Tm"),
                 .simple "b" (.base "Tm")],
      syntaxPattern := [.terminal "Id", .terminal "(",
                        .nonTerminal "A", .terminal ",",
                        .nonTerminal "a", .terminal ",",
                        .nonTerminal "b", .terminal ")"] },
    -- Lam(^body) : Tm  (lambda abstraction)
    { label := "Lam", category := "Tm",
      params := [.abstraction "body" (.arrow (.base "Tm") (.base "Tm"))],
      syntaxPattern := [.terminal "lam", .terminal ".", .nonTerminal "body"] },
    -- App(f, a) : Tm  (application)
    { label := "App", category := "Tm",
      params := [.simple "f" (.base "Tm"), .simple "a" (.base "Tm")],
      syntaxPattern := [.nonTerminal "f", .nonTerminal "a"] },
    -- Pair(a, b) : Tm  (dependent pair introduction)
    { label := "Pair", category := "Tm",
      params := [.simple "a" (.base "Tm"), .simple "b" (.base "Tm")],
      syntaxPattern := [.terminal "(", .nonTerminal "a", .terminal ",",
                        .nonTerminal "b", .terminal ")"] },
    -- Fst(p) : Tm  (first projection)
    { label := "Fst", category := "Tm",
      params := [.simple "p" (.base "Tm")],
      syntaxPattern := [.terminal "fst", .nonTerminal "p"] },
    -- Snd(p) : Tm  (second projection)
    { label := "Snd", category := "Tm",
      params := [.simple "p" (.base "Tm")],
      syntaxPattern := [.terminal "snd", .nonTerminal "p"] },
    -- Refl(a) : Tm  (reflexivity proof)
    { label := "Refl", category := "Tm",
      params := [.simple "a" (.base "Tm")],
      syntaxPattern := [.terminal "refl", .nonTerminal "a"] },
    -- CtxEmpty : Ctx  (empty context)
    { label := "CtxEmpty", category := "Ctx", params := [],
      syntaxPattern := [.terminal "[]"] },
    -- CtxExtend(G, A) : Ctx  (context extension)
    { label := "CtxExtend", category := "Ctx",
      params := [.simple "G" (.base "Ctx"), .simple "A" (.base "Tm")],
      syntaxPattern := [.nonTerminal "G", .terminal ",", .nonTerminal "A"] }
  ],
  equations := [],
  rewrites := [
    -- BetaPi: App(Lam(^body), a) ~> body[a/x]
    { name := "BetaPi",
      typeContext := [("body", .base "Tm"), ("a", .base "Tm")],
      premises := [],
      left := .apply "App" [.apply "Lam" [.lambda none (.fvar "body")], .fvar "a"],
      right := .subst (.fvar "body") (.fvar "a") },
    -- BetaSigmaFst: Fst(Pair(a, b)) ~> a
    { name := "BetaSigmaFst",
      typeContext := [("a", .base "Tm"), ("b", .base "Tm")],
      premises := [],
      left := .apply "Fst" [.apply "Pair" [.fvar "a", .fvar "b"]],
      right := .fvar "a" },
    -- BetaSigmaSnd: Snd(Pair(a, b)) ~> b
    { name := "BetaSigmaSnd",
      typeContext := [("a", .base "Tm"), ("b", .base "Tm")],
      premises := [],
      left := .apply "Snd" [.apply "Pair" [.fvar "a", .fvar "b"]],
      right := .fvar "b" }
  ]
}

/-! ## Helper Constructors -/

/-- Distinguished ground-type head. -/
def u0 : Pattern := .apply "U0" []

/-- Untyped formation-marker head. -/
def u1 : Pattern := .apply "U1" []

/-- Dependent function type `Π(x : A). B`. The body `B` should contain
    `.bvar 0` for references to the bound variable. -/
def mkPi (A B : Pattern) : Pattern := .apply "Pi" [A, .lambda none B]

/-- Dependent pair type `Σ(x : A). B`. -/
def mkSigma (A B : Pattern) : Pattern := .apply "Sigma" [A, .lambda none B]

/-- Identity type `Id_A(a, b)`. -/
def mkId (A a b : Pattern) : Pattern := .apply "Id" [A, a, b]

/-- Lambda abstraction `λx. body`. -/
def mkLam (body : Pattern) : Pattern := .apply "Lam" [.lambda none body]

/-- Application `f a`. -/
def mkApp (f a : Pattern) : Pattern := .apply "App" [f, a]

/-- Dependent pair `(a, b)`. -/
def mkPair (a b : Pattern) : Pattern := .apply "Pair" [a, b]

/-- First projection `fst p`. -/
def mkFst (p : Pattern) : Pattern := .apply "Fst" [p]

/-- Second projection `snd p`. -/
def mkSnd (p : Pattern) : Pattern := .apply "Snd" [p]

/-- Reflexivity proof `refl a`. -/
def mkRefl (a : Pattern) : Pattern := .apply "Refl" [a]

/-- Empty context. -/
def mkCtxEmpty : Pattern := .apply "CtxEmpty" []

/-- Context extension `Γ, A`. -/
def mkCtxExtend (G A : Pattern) : Pattern := .apply "CtxExtend" [G, A]

/-! ## OSLF Pipeline Instantiation -/

/-- The OSLF type system for the two-sort experiment (Tm is the process sort).
    Galois connection ◇ ⊣ □ is proven automatically. -/
def twoSortDependentOSLF := langOSLF twoSortDependent "Tm"

/-- The Galois connection for the two-sort experiment: ◇ ⊣ □. -/
theorem twoSortDependentGalois :
    GaloisConnection (langDiamond twoSortDependent) (langBox twoSortDependent) :=
  langGalois twoSortDependent

/-! ## Constructor Category Instantiation -/

/-- The Tm sort in the two-sort experiment's constructor category. -/
def twoSortTm : LangSort twoSortDependent := ⟨"Tm", by decide⟩

/-- The Ctx sort in the two-sort experiment's constructor category. -/
def twoSortCtx : LangSort twoSortDependent := ⟨"Ctx", by decide⟩

/-- the two-sort experiment has exactly 2 sorts. -/
theorem twoSortDependent_types : twoSortDependent.types = ["Tm", "Ctx"] := rfl

/-- the two-sort experiment has exactly 3 rewrite rules. -/
theorem twoSortDependent_rewrites_length : twoSortDependent.rewrites.length = 3 := by decide

/-- the two-sort experiment has no equations (intensional). -/
theorem twoSortDependent_no_equations : twoSortDependent.equations = [] := rfl

/-! ## Executable Demos -/

#eval!
  let identity := mkLam (.bvar 0)      -- λx. x
  let a := .fvar "a"                   -- free variable a
  let redex := mkApp identity a        -- (λx. x) a
  let result := Mettapedia.OSLF.MeTTaIL.ContextualStep.reducts twoSortDependent 1 redex
  (redex, result)

#eval!
  let a := .fvar "a"
  let b := .fvar "b"
  let redex := mkFst (mkPair a b)      -- fst (a, b)
  let result := Mettapedia.OSLF.MeTTaIL.ContextualStep.reducts twoSortDependent 1 redex
  (redex, result)

#eval!
  let a := .fvar "a"
  let b := .fvar "b"
  let redex := mkSnd (mkPair a b)      -- snd (a, b)
  let result := Mettapedia.OSLF.MeTTaIL.ContextualStep.reducts twoSortDependent 1 redex
  (redex, result)

end Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core
