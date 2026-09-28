import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.Execution

/-!
# The draft's native artifacts against the formal package

The draft prints kernel terms in a fixed spelling: `(DeclConst c)`,
`(App f a)`, `(Lam A b)` with or without a domain, `(Pi A B)`, `(idx i)`,
and in stored rules `(PVar k)` for the `k`-th pattern slot.  A stored rule
`(PrimeRule h n (p₁ … pₙ) r)` fires on a spine of `h` with exactly `n`
arguments matching the patterns; a repeated slot must match the same
normal form, and instantiation shifts slot values under the binders of `r`.

This module records the artifacts `set:native-proof zero-add` and
`set:native-proof ex-falso` returned and the library's stored rules, as data
whose printed form is the captured text, and compares them with the formal
package:

* the native proof term, with lambda domains erased, is the compiler's
  output `zeroAddTerm`, and its binder domains are the represented premises;
* the proof's type is the proof family at the represented conclusion;
* each stored rule of the program is an instance family of root steps of the
  formal rules;
* each declaration of the context has the formal type;
* each stored rule of the library is the formal equation.  On the binary
  preceding `1929c593` the successor equations of `composeCert` and `iterCert`
  were stored in contracted form, one beta step after the formal shared
  equation; on the binary `36b2cf70` they are stored in the shared form, and
  every stored rule is exactly a formal equation.

The proof packages (term, type, context and program rules) are the ones the
draft binary with sha256 prefix `122c1c22` returns, whose signature defines
`Falsum := ∀p. p`; each component prints as the binary printed it
(`capturedTerm_text`, `capturedType_text`, `capturedContext_text`,
`capturedRules_text`, and the same for `ex-falso`). The checker keeps
`Falsum` a declared constant of every context, and selects the rule of its
definition when a request mentions `Falsum`:

* the zero-add package does not mention `Falsum`: its context declares
  `Falsum : prop`, and its rules are those of the chart without the rule
  (`SetProfile.signature`). It is the package first captured on `1929c593`
  (unchanged on `36b2cf70`) with two differences, both from the definition: the
  proof family is named by the new signature digest, and `Falsum` is declared
  after `imp`, where the signature places its definition;
* the package of `ex-falso : ∀r. Falsum → r` mentions `Falsum`: its term is the
  compiler's output `λr. λh. h r` with the hypothesis at `Holds Falsum`, its
  type the proof family at `∀r. Falsum → r` with `Falsum` by its name, and its
  rules are the decoders of `all@prop` and of implication and the rule
  `Falsum ⟶ all@prop (λp. p)`: root steps of the chart with the rule
  (`SetProfile.definedSignature`), the last by the δ-step of the definition
  (`exFalsoCapturedRules_sound`). The captured term is typed at the captured
  type in the formal rules with the rule of `Falsum` (`exFalsoCaptured_typed`).

The library rules come from the binary preceding `1929c593` (the earlier rules)
and from `36b2cf70` (the current rules).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ArtifactComparison

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Presentation.Declaration Presentation.FormationSensitive
open SetProfile (baseName constantName numTy zeroNative sucNative addNative
  eqNumNative holdsName targetRules)
open CertifiedTransforms (stepOver shared sharedBody)
open CertifiedTransformProgram.Package
open CertifiedTransformProgram.Execution
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.AlgebraicSchema
  (SchemaTable SchemaFamily)

/-! ## The kernel spelling -/

/-- Terms in the kernel's printed spelling. -/
inductive KTerm where
  | declConst (name : String)
  | app (function argument : KTerm)
  | lamTyped (domain body : KTerm)
  | lamBare (body : KTerm)
  | pi (domain codomain : KTerm)
  | sigma (domain codomain : KTerm)
  | ident (carrier left right : KTerm)
  | refl (term : KTerm)
  | pair (first second : KTerm)
  | fst (package : KTerm)
  | snd (package : KTerm)
  | idx (index : Nat)
  | pvar (slot : Nat)
  | sortConst (level : Nat)
  deriving DecidableEq, Repr

namespace KTerm

/-- The draft's printed form. -/
def render : KTerm → String
  | .declConst name => "(DeclConst " ++ name ++ ")"
  | .app function argument => "(App " ++ function.render ++ " " ++ argument.render ++ ")"
  | .lamTyped domain body => "(Lam " ++ domain.render ++ " " ++ body.render ++ ")"
  | .lamBare body => "(Lam " ++ body.render ++ ")"
  | .pi domain codomain => "(Pi " ++ domain.render ++ " " ++ codomain.render ++ ")"
  | .sigma domain codomain => "(Sigma " ++ domain.render ++ " " ++ codomain.render ++ ")"
  | .ident carrier left right =>
      "(Id " ++ carrier.render ++ " " ++ left.render ++ " " ++ right.render ++ ")"
  | .refl term => "(Refl " ++ term.render ++ ")"
  | .pair first second => "(Pair " ++ first.render ++ " " ++ second.render ++ ")"
  | .fst package => "(Fst " ++ package.render ++ ")"
  | .snd package => "(Snd " ++ package.render ++ ")"
  | .idx index => "(idx " ++ toString index ++ ")"
  | .pvar slot => "(PVar " ++ toString slot ++ ")"
  | .sortConst level => "(Sort (LevelConst " ++ toString level ++ "))"

/-- Translation into the calculus.  `slot k` is the variable of pattern slot
`k` at the current depth; going under a binder shifts it.  Lambda domains are
erased: the calculus's lambda carries none. -/
def toTm : {n : Nat} → (Nat → Option (Fin n)) → KTerm → Option (Tower.Tm n)
  | _, _, .declConst name => some (.const (.mkSimple name))
  | _, slot, .app function argument => do
      let function ← function.toTm slot
      let argument ← argument.toTm slot
      pure (.app function argument)
  | _, slot, .lamTyped _ body => do
      let body ← body.toTm (fun k => (slot k).map Fin.succ)
      pure (.lam body)
  | _, slot, .lamBare body => do
      let body ← body.toTm (fun k => (slot k).map Fin.succ)
      pure (.lam body)
  | _, slot, .pi domain codomain => do
      let domain ← domain.toTm slot
      let codomain ← codomain.toTm (fun k => (slot k).map Fin.succ)
      pure (.pi domain codomain)
  | _, slot, .sigma domain codomain => do
      let domain ← domain.toTm slot
      let codomain ← codomain.toTm (fun k => (slot k).map Fin.succ)
      pure (.sigma domain codomain)
  | _, slot, .ident carrier left right => do
      let carrier ← carrier.toTm slot
      let left ← left.toTm slot
      let right ← right.toTm slot
      pure (.id carrier left right)
  | _, slot, .refl term => do
      let term ← term.toTm slot
      pure (.refl term)
  | _, slot, .pair first second => do
      let first ← first.toTm slot
      let second ← second.toTm slot
      pure (.pair first second)
  | _, slot, .fst package => do
      let package ← package.toTm slot
      pure (.fst package)
  | _, slot, .snd package => do
      let package ← package.toTm slot
      pure (.snd package)
  | n, _, .idx index => if bound : index < n then some (.var ⟨index, bound⟩) else none
  | _, slot, .pvar k => (slot k).map .var
  | _, _, .sortConst level => some (sortTm (.const level))

/-- A closed term, or a term in a context of `n` bound variables, outside any
stored rule. -/
def toTmAt (n : Nat) (term : KTerm) : Option (Tower.Tm n) := term.toTm (fun _ => none)

/-- The largest pattern slot, plus one. -/
def slots : KTerm → Nat
  | .app function argument => max function.slots argument.slots
  | .lamTyped domain body => max domain.slots body.slots
  | .lamBare body => body.slots
  | .pi domain codomain => max domain.slots codomain.slots
  | .sigma domain codomain => max domain.slots codomain.slots
  | .ident carrier left right => max carrier.slots (max left.slots right.slots)
  | .refl term => term.slots
  | .pair first second => max first.slots second.slots
  | .fst package => package.slots
  | .snd package => package.slots
  | .pvar slot => slot + 1
  | _ => 0

/-- The lambda domains, in order. -/
def domains : KTerm → List KTerm
  | .app function argument => function.domains ++ argument.domains
  | .lamTyped domain body => domain :: (domain.domains ++ body.domains)
  | .lamBare body => body.domains
  | .pi domain codomain => domain.domains ++ codomain.domains
  | .sigma domain codomain => domain.domains ++ codomain.domains
  | .ident carrier left right => carrier.domains ++ left.domains ++ right.domains
  | .refl term => term.domains
  | .pair first second => first.domains ++ second.domains
  | .fst package => package.domains
  | .snd package => package.domains
  | _ => []

/-- A declared name in the kernel's spelling. -/
def nameText : DeclName → Option String
  | .str .anonymous text => some text
  | _ => none

/-- The kernel spelling of a term of the calculus, with bare lambdas. -/
def ofTm : {n : Nat} → Tower.Tm n → Option KTerm
  | _, .var index => some (.idx index.val)
  | _, .const name => (nameText name).map .declConst
  | _, .head (.sort (.const level)) => some (.sortConst level)
  | _, .head _ => none
  | _, .pi domain codomain => do pure (.pi (← ofTm domain) (← ofTm codomain))
  | _, .sigma domain codomain => do pure (.sigma (← ofTm domain) (← ofTm codomain))
  | _, .id carrier left right =>
      do pure (.ident (← ofTm carrier) (← ofTm left) (← ofTm right))
  | _, .lam body => do pure (.lamBare (← ofTm body))
  | _, .app function argument => do pure (.app (← ofTm function) (← ofTm argument))
  | _, .pair first second => do pure (.pair (← ofTm first) (← ofTm second))
  | _, .fst package => do pure (.fst (← ofTm package))
  | _, .snd package => do pure (.snd (← ofTm package))
  | _, .refl term => do pure (.refl (← ofTm term))

theorem nameText_some {name : DeclName} {text : String} (spelled : nameText name = some text) :
    Lean.Name.mkSimple text = name := by
  unfold nameText at spelled
  split at spelled
  · cases spelled; rfl
  · cases spelled

/-- Reading a spelled term back gives the term. -/
theorem toTm_ofTm : ∀ {n : Nat} (term : Tower.Tm n) {spelled : KTerm},
    ofTm term = some spelled → spelled.toTm (fun _ => none) = some term
  | n, .var index, spelled, equal => by
      simp only [ofTm, Option.some.injEq] at equal
      subst equal
      simp [toTm, index.isLt]
  | _, .const name, spelled, equal => by
      simp only [ofTm, Option.map_eq_some_iff] at equal
      obtain ⟨text, named, rfl⟩ := equal
      show some (Tm.const (Lean.Name.mkSimple text) : Tower.Tm _) = some (Tm.const name)
      rw [nameText_some named]
  | _, .head (.sort (.const level)), spelled, equal => by
      simp only [ofTm, Option.some.injEq] at equal
      subst equal
      rfl
  | _, .head (.sort (.param _)), _, equal => by simp [ofTm] at equal
  | _, .head (.sort (.succ _)), _, equal => by simp [ofTm] at equal
  | _, .head (.sort (.max _ _)), _, equal => by simp [ofTm] at equal
  | _, .head .legacyGround, _, equal => by simp [ofTm] at equal
  | _, .pi domain codomain, spelled, equal => by
      simp only [ofTm, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨d, dSpelled, c, cSpelled, rfl⟩ := equal
      have dBack := toTm_ofTm domain dSpelled
      have cBack := toTm_ofTm codomain cSpelled
      simp only [toTm, dBack, Option.map_none, cBack, bind, Option.bind_some, pure]
  | _, .sigma domain codomain, spelled, equal => by
      simp only [ofTm, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨d, dSpelled, c, cSpelled, rfl⟩ := equal
      have dBack := toTm_ofTm domain dSpelled
      have cBack := toTm_ofTm codomain cSpelled
      simp only [toTm, dBack, Option.map_none, cBack, bind, Option.bind_some, pure]
  | _, .id carrier left right, spelled, equal => by
      simp only [ofTm, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨c, cSpelled, l, lSpelled, r, rSpelled, rfl⟩ := equal
      simp only [toTm, toTm_ofTm carrier cSpelled, toTm_ofTm left lSpelled,
        toTm_ofTm right rSpelled, bind, Option.bind_some, pure]
  | _, .lam body, spelled, equal => by
      simp only [ofTm, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨b, bSpelled, rfl⟩ := equal
      have bBack := toTm_ofTm body bSpelled
      simp only [toTm, Option.map_none, bBack, bind, Option.bind_some, pure]
  | _, .app function argument, spelled, equal => by
      simp only [ofTm, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨f, fSpelled, a, aSpelled, rfl⟩ := equal
      simp only [toTm, toTm_ofTm function fSpelled, toTm_ofTm argument aSpelled, bind,
        Option.bind_some, pure]
  | _, .pair first second, spelled, equal => by
      simp only [ofTm, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨f, fSpelled, s, sSpelled, rfl⟩ := equal
      simp only [toTm, toTm_ofTm first fSpelled, toTm_ofTm second sSpelled, bind,
        Option.bind_some, pure]
  | _, .fst package, spelled, equal => by
      simp only [ofTm, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨p, pSpelled, rfl⟩ := equal
      simp only [toTm, toTm_ofTm package pSpelled, bind, Option.bind_some, pure]
  | _, .snd package, spelled, equal => by
      simp only [ofTm, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨p, pSpelled, rfl⟩ := equal
      simp only [toTm, toTm_ofTm package pSpelled, bind, Option.bind_some, pure]
  | _, .refl term, spelled, equal => by
      simp only [ofTm, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨t, tSpelled, rfl⟩ := equal
      simp only [toTm, toTm_ofTm term tSpelled, bind, Option.bind_some, pure]

end KTerm

/-- A stored rule: head, argument count, argument patterns, right side. -/
structure KRule where
  head : String
  arity : Nat
  patterns : List KTerm
  rhs : KTerm
  deriving DecidableEq, Repr

namespace KRule

def render (wrapper : String) (rule : KRule) : String :=
  "(" ++ wrapper ++ " " ++ rule.head ++ " " ++ toString rule.arity ++ " (" ++
    " ".intercalate (rule.patterns.map KTerm.render) ++ ") " ++ rule.rhs.render ++ ")"

/-- The number of pattern slots. -/
def slotCount (rule : KRule) : Nat :=
  (rule.patterns.map KTerm.slots).foldl max 0

/-- Slot `k` of a rule with `m` slots is the de Bruijn variable `m - 1 - k` of
the equation telescope. -/
def slotVariable (m k : Nat) : Option (Fin m) :=
  if bound : k < m then some ⟨m - 1 - k, by omega⟩ else none

/-- The stored rule as an equation of the calculus: the telescope has one variable
per slot, the left side is the head applied to the patterns. -/
def toEquation (rule : KRule) : Option (Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) := do
  let m := rule.slotCount
  let patterns ← rule.patterns.mapM (fun pattern => pattern.toTm (slotVariable m))
  let rhs ← rule.rhs.toTm (slotVariable m)
  pure ⟨m, (patterns.foldl .app (.const (.mkSimple rule.head)), rhs)⟩

end KRule

/-! ### Captured term and type of `set:native-proof zero-add` -/

def capturedTerm : KTerm :=
  (.app (.app (.app (.declConst "__cetta_proof_edb893c30879ea3547bf6b13") (.lamTyped (.declConst "num") (.app (.app (.declConst "eq@num") (.app (.app (.declConst "add") (.declConst "zero")) (.idx 0))) (.idx 0)))) (.app (.declConst "__cetta_proof_3e526d1816b34ee602df380a") (.declConst "zero"))) (.lamTyped (.declConst "num") (.lamTyped (.app (.declConst "__cetta_holds_df87b3cd8ab4b6383b1d0591") (.app (.lamTyped (.declConst "num") (.app (.app (.declConst "eq@num") (.app (.app (.declConst "add") (.declConst "zero")) (.idx 0))) (.idx 0))) (.idx 0))) (.app (.app (.app (.app (.app (.declConst "__cetta_proof_7b7ae677596090a0fb1c398d") (.lamTyped (.declConst "num") (.app (.app (.declConst "eq@num") (.app (.declConst "suc") (.app (.app (.declConst "add") (.declConst "zero")) (.idx 2)))) (.app (.declConst "suc") (.idx 0))))) (.app (.app (.declConst "add") (.declConst "zero")) (.idx 1))) (.idx 1)) (.idx 0)) (.app (.declConst "__cetta_proof_3e526d1816b34ee602df380a") (.app (.declConst "suc") (.app (.app (.declConst "add") (.declConst "zero")) (.idx 1))))))))

def capturedTermText : String :=
  "(App (App (App (DeclConst __cetta_proof_edb893c30879ea3547bf6b13) (Lam (DeclConst num) (App (App (DeclConst eq@num) (App (App (DeclConst add) (DeclConst zero)) (idx 0))) (idx 0)))) (App (DeclConst __cetta_proof_3e526d1816b34ee602df380a) (DeclConst zero))) (Lam (DeclConst num) (Lam (App (DeclConst __cetta_holds_df87b3cd8ab4b6383b1d0591) (App (Lam (DeclConst num) (App (App (DeclConst eq@num) (App (App (DeclConst add) (DeclConst zero)) (idx 0))) (idx 0))) (idx 0))) (App (App (App (App (App (DeclConst __cetta_proof_7b7ae677596090a0fb1c398d) (Lam (DeclConst num) (App (App (DeclConst eq@num) (App (DeclConst suc) (App (App (DeclConst add) (DeclConst zero)) (idx 2)))) (App (DeclConst suc) (idx 0))))) (App (App (DeclConst add) (DeclConst zero)) (idx 1))) (idx 1)) (idx 0)) (App (DeclConst __cetta_proof_3e526d1816b34ee602df380a) (App (DeclConst suc) (App (App (DeclConst add) (DeclConst zero)) (idx 1))))))))"

def capturedType : KTerm :=
  (.app (.declConst "__cetta_holds_df87b3cd8ab4b6383b1d0591") (.app (.declConst "all@num") (.lamTyped (.declConst "num") (.app (.app (.declConst "eq@num") (.app (.app (.declConst "add") (.declConst "zero")) (.idx 0))) (.idx 0)))))

def capturedTypeText : String :=
  "(App (DeclConst __cetta_holds_df87b3cd8ab4b6383b1d0591) (App (DeclConst all@num) (Lam (DeclConst num) (App (App (DeclConst eq@num) (App (App (DeclConst add) (DeclConst zero)) (idx 0))) (idx 0)))))"

/-! ### Captured stored rules of the zero-add program -/

def capturedRules : List KRule :=
  [{ head := "__cetta_holds_df87b3cd8ab4b6383b1d0591", arity := 1, patterns := [(.app (.declConst "all@(Pi num prop)") (.pvar 0))], rhs := (.pi (.pi (.declConst "num") (.declConst "prop")) (.app (.declConst "__cetta_holds_df87b3cd8ab4b6383b1d0591") (.app (.pvar 0) (.idx 0)))) },
   { head := "__cetta_holds_df87b3cd8ab4b6383b1d0591", arity := 1, patterns := [(.app (.declConst "all@num") (.pvar 0))], rhs := (.pi (.declConst "num") (.app (.declConst "__cetta_holds_df87b3cd8ab4b6383b1d0591") (.app (.pvar 0) (.idx 0)))) },
   { head := "__cetta_holds_df87b3cd8ab4b6383b1d0591", arity := 1, patterns := [(.app (.app (.declConst "imp") (.pvar 0)) (.pvar 1))], rhs := (.pi (.app (.declConst "__cetta_holds_df87b3cd8ab4b6383b1d0591") (.pvar 0)) (.app (.declConst "__cetta_holds_df87b3cd8ab4b6383b1d0591") (.pvar 1))) },
   { head := "add", arity := 2, patterns := [(.pvar 0), (.app (.declConst "suc") (.pvar 1))], rhs := (.app (.declConst "suc") (.app (.app (.declConst "add") (.pvar 0)) (.pvar 1))) },
   { head := "add", arity := 2, patterns := [(.pvar 0), (.declConst "zero")], rhs := (.pvar 0) }]

def capturedRulesText : List String :=
  ["(PrimeRule __cetta_holds_df87b3cd8ab4b6383b1d0591 1 ((App (DeclConst all@(Pi num prop)) (PVar 0))) (Pi (Pi (DeclConst num) (DeclConst prop)) (App (DeclConst __cetta_holds_df87b3cd8ab4b6383b1d0591) (App (PVar 0) (idx 0)))))",
   "(PrimeRule __cetta_holds_df87b3cd8ab4b6383b1d0591 1 ((App (DeclConst all@num) (PVar 0))) (Pi (DeclConst num) (App (DeclConst __cetta_holds_df87b3cd8ab4b6383b1d0591) (App (PVar 0) (idx 0)))))",
   "(PrimeRule __cetta_holds_df87b3cd8ab4b6383b1d0591 1 ((App (App (DeclConst imp) (PVar 0)) (PVar 1))) (Pi (App (DeclConst __cetta_holds_df87b3cd8ab4b6383b1d0591) (PVar 0)) (App (DeclConst __cetta_holds_df87b3cd8ab4b6383b1d0591) (PVar 1))))",
   "(PrimeRule add 2 ((PVar 0) (App (DeclConst suc) (PVar 1))) (App (DeclConst suc) (App (App (DeclConst add) (PVar 0)) (PVar 1))))",
   "(PrimeRule add 2 ((PVar 0) (DeclConst zero)) (PVar 0))"]

/-! ### Captured context of the zero-add program -/

def capturedContext : List (String × KTerm) :=
  [("__cetta_proof_7b7ae677596090a0fb1c398d", (.app (.declConst "__cetta_holds_df87b3cd8ab4b6383b1d0591") (.app (.declConst "all@(Pi num prop)") (.lamTyped (.pi (.declConst "num") (.declConst "prop")) (.app (.declConst "all@num") (.lamTyped (.declConst "num") (.app (.declConst "all@num") (.lamTyped (.declConst "num") (.app (.app (.declConst "imp") (.app (.app (.declConst "eq@num") (.idx 1)) (.idx 0))) (.app (.app (.declConst "imp") (.app (.idx 2) (.idx 1))) (.app (.idx 2) (.idx 0)))))))))))),
   ("__cetta_proof_3e526d1816b34ee602df380a", (.app (.declConst "__cetta_holds_df87b3cd8ab4b6383b1d0591") (.app (.declConst "all@num") (.lamTyped (.declConst "num") (.app (.app (.declConst "eq@num") (.idx 0)) (.idx 0)))))),
   ("__cetta_proof_edb893c30879ea3547bf6b13", (.app (.declConst "__cetta_holds_df87b3cd8ab4b6383b1d0591") (.app (.declConst "all@(Pi num prop)") (.lamTyped (.pi (.declConst "num") (.declConst "prop")) (.app (.app (.declConst "imp") (.app (.idx 0) (.declConst "zero"))) (.app (.app (.declConst "imp") (.app (.declConst "all@num") (.lamTyped (.declConst "num") (.app (.app (.declConst "imp") (.app (.idx 1) (.idx 0))) (.app (.idx 1) (.app (.declConst "suc") (.idx 0))))))) (.app (.declConst "all@num") (.lamTyped (.declConst "num") (.app (.idx 1) (.idx 0)))))))))),
   ("__cetta_holds_df87b3cd8ab4b6383b1d0591", (.pi (.declConst "prop") (.sortConst 0))),
   ("all@(Pi num prop)", (.pi (.pi (.pi (.declConst "num") (.declConst "prop")) (.declConst "prop")) (.declConst "prop"))),
   ("all@num", (.pi (.pi (.declConst "num") (.declConst "prop")) (.declConst "prop"))),
   ("suc", (.pi (.declConst "num") (.declConst "num"))),
   ("eq@num", (.pi (.declConst "num") (.pi (.declConst "num") (.declConst "prop")))),
   ("add", (.pi (.declConst "num") (.pi (.declConst "num") (.declConst "num")))),
   ("zero", (.declConst "num")),
   ("num", (.sortConst 0)),
   ("UnivOf", (.pi (.declConst "set") (.declConst "set"))),
   ("Eps_set", (.pi (.pi (.declConst "set") (.declConst "prop")) (.declConst "set"))),
   ("Repl", (.pi (.declConst "set") (.pi (.pi (.declConst "set") (.declConst "set")) (.declConst "set")))),
   ("Sep", (.pi (.declConst "set") (.pi (.pi (.declConst "set") (.declConst "prop")) (.declConst "set")))),
   ("Power", (.pi (.declConst "set") (.declConst "set"))),
   ("Union", (.pi (.declConst "set") (.declConst "set"))),
   ("Empty", (.declConst "set")),
   ("In", (.pi (.declConst "set") (.pi (.declConst "set") (.declConst "prop")))),
   ("Falsum", (.declConst "prop")),
   ("imp", (.pi (.declConst "prop") (.pi (.declConst "prop") (.declConst "prop")))),
   ("prop", (.sortConst 0)),
   ("set", (.sortConst 0))]

def capturedContextTexts : List (String × String) :=
  [("__cetta_proof_7b7ae677596090a0fb1c398d",
    "(App (DeclConst __cetta_holds_df87b3cd8ab4b6383b1d0591) (App (DeclConst all@(Pi num prop)) (Lam (Pi (DeclConst num) (DeclConst prop)) (App (DeclConst all@num) (Lam (DeclConst num) (App (DeclConst all@num) (Lam (DeclConst num) (App (App (DeclConst imp) (App (App (DeclConst eq@num) (idx 1)) (idx 0))) (App (App (DeclConst imp) (App (idx 2) (idx 1))) (App (idx 2) (idx 0)))))))))))"),
   ("__cetta_proof_3e526d1816b34ee602df380a",
    "(App (DeclConst __cetta_holds_df87b3cd8ab4b6383b1d0591) (App (DeclConst all@num) (Lam (DeclConst num) (App (App (DeclConst eq@num) (idx 0)) (idx 0)))))"),
   ("__cetta_proof_edb893c30879ea3547bf6b13",
    "(App (DeclConst __cetta_holds_df87b3cd8ab4b6383b1d0591) (App (DeclConst all@(Pi num prop)) (Lam (Pi (DeclConst num) (DeclConst prop)) (App (App (DeclConst imp) (App (idx 0) (DeclConst zero))) (App (App (DeclConst imp) (App (DeclConst all@num) (Lam (DeclConst num) (App (App (DeclConst imp) (App (idx 1) (idx 0))) (App (idx 1) (App (DeclConst suc) (idx 0))))))) (App (DeclConst all@num) (Lam (DeclConst num) (App (idx 1) (idx 0)))))))))"),
   ("__cetta_holds_df87b3cd8ab4b6383b1d0591",
    "(Pi (DeclConst prop) (Sort (LevelConst 0)))"),
   ("all@(Pi num prop)",
    "(Pi (Pi (Pi (DeclConst num) (DeclConst prop)) (DeclConst prop)) (DeclConst prop))"),
   ("all@num",
    "(Pi (Pi (DeclConst num) (DeclConst prop)) (DeclConst prop))"),
   ("suc",
    "(Pi (DeclConst num) (DeclConst num))"),
   ("eq@num",
    "(Pi (DeclConst num) (Pi (DeclConst num) (DeclConst prop)))"),
   ("add",
    "(Pi (DeclConst num) (Pi (DeclConst num) (DeclConst num)))"),
   ("zero",
    "(DeclConst num)"),
   ("num",
    "(Sort (LevelConst 0))"),
   ("UnivOf",
    "(Pi (DeclConst set) (DeclConst set))"),
   ("Eps_set",
    "(Pi (Pi (DeclConst set) (DeclConst prop)) (DeclConst set))"),
   ("Repl",
    "(Pi (DeclConst set) (Pi (Pi (DeclConst set) (DeclConst set)) (DeclConst set)))"),
   ("Sep",
    "(Pi (DeclConst set) (Pi (Pi (DeclConst set) (DeclConst prop)) (DeclConst set)))"),
   ("Power",
    "(Pi (DeclConst set) (DeclConst set))"),
   ("Union",
    "(Pi (DeclConst set) (DeclConst set))"),
   ("Empty",
    "(DeclConst set)"),
   ("In",
    "(Pi (DeclConst set) (Pi (DeclConst set) (DeclConst prop)))"),
   ("Falsum",
    "(DeclConst prop)"),
   ("imp",
    "(Pi (DeclConst prop) (Pi (DeclConst prop) (DeclConst prop)))"),
   ("prop",
    "(Sort (LevelConst 0))"),
   ("set",
    "(Sort (LevelConst 0))")]

/-! ### Captured stored rules of the certified-transform library -/

def libraryRules : List KRule :=
  [{ head := "num-rec", arity := 4, patterns := [(.pvar 0), (.pvar 1), (.pvar 2), (.declConst "zero")], rhs := (.pvar 1) },
   { head := "num-rec", arity := 4, patterns := [(.pvar 0), (.pvar 1), (.pvar 2), (.app (.declConst "suc") (.pvar 3))], rhs := (.app (.app (.pvar 2) (.pvar 3)) (.app (.app (.app (.app (.declConst "num-rec") (.pvar 0)) (.pvar 1)) (.pvar 2)) (.pvar 3))) },
   { head := "add", arity := 2, patterns := [(.pvar 0), (.declConst "zero")], rhs := (.pvar 0) },
   { head := "add", arity := 2, patterns := [(.pvar 0), (.app (.declConst "suc") (.pvar 1))], rhs := (.app (.declConst "suc") (.app (.app (.declConst "add") (.pvar 0)) (.pvar 1))) },
   { head := "eqAt", arity := 1, patterns := [(.pvar 0)], rhs := (.ident (.declConst "num") (.app (.app (.declConst "add") (.declConst "zero")) (.pvar 0)) (.pvar 0)) },
   { head := "sucMove", arity := 2, patterns := [(.pvar 0), (.pvar 1)], rhs := (.app (.app (.app (.app (.app (.app (.declConst "id:eliminate") (.declConst "num")) (.app (.app (.declConst "add") (.declConst "zero")) (.pvar 0))) (.lamTyped (.declConst "num") (.lamTyped (.ident (.declConst "num") (.app (.app (.declConst "add") (.declConst "zero")) (.pvar 0)) (.idx 0)) (.ident (.declConst "num") (.app (.declConst "suc") (.app (.app (.declConst "add") (.declConst "zero")) (.pvar 0))) (.app (.declConst "suc") (.idx 1)))))) (.refl (.app (.declConst "suc") (.app (.app (.declConst "add") (.declConst "zero")) (.pvar 0))))) (.pvar 0)) (.pvar 1)) },
   { head := "keepCert", arity := 4, patterns := [(.pvar 0), (.pvar 1), (.pvar 2), (.pvar 3)], rhs := (.pair (.pvar 2) (.pvar 3)) },
   { head := "transportCert", arity := 6, patterns := [(.pvar 0), (.pvar 1), (.pvar 2), (.pvar 3), (.pvar 4), (.pvar 5)], rhs := (.pair (.app (.pvar 2) (.pvar 4)) (.app (.app (.pvar 3) (.pvar 4)) (.pvar 5))) },
   { head := "composeCert", arity := 6, patterns := [(.pvar 0), (.pvar 1), (.pvar 2), (.pvar 3), (.pvar 4), (.pvar 5)], rhs := (.app (.app (.pvar 3) (.fst (.app (.app (.pvar 2) (.pvar 4)) (.pvar 5)))) (.snd (.app (.app (.pvar 2) (.pvar 4)) (.pvar 5)))) },
   { head := "iterCert", arity := 6, patterns := [(.declConst "zero"), (.pvar 0), (.pvar 1), (.pvar 2), (.pvar 3), (.pvar 4)], rhs := (.pair (.pvar 3) (.pvar 4)) },
   { head := "iterCert", arity := 6, patterns := [(.app (.declConst "suc") (.pvar 0)), (.pvar 1), (.pvar 2), (.pvar 3), (.pvar 4), (.pvar 5)], rhs := (.app (.app (.app (.app (.app (.app (.declConst "iterCert") (.pvar 0)) (.pvar 1)) (.pvar 2)) (.pvar 3)) (.fst (.app (.app (.pvar 3) (.pvar 4)) (.pvar 5)))) (.snd (.app (.app (.pvar 3) (.pvar 4)) (.pvar 5)))) },
   { head := "returnIter", arity := 1, patterns := [(.pvar 0)], rhs := (.lamBare (.lamBare (.lamBare (.lamBare (.lamBare (.app (.app (.app (.app (.app (.app (.declConst "iterCert") (.idx 3)) (.pvar 0)) (.idx 4)) (.idx 2)) (.idx 1)) (.idx 0))))))) },
   { head := "sucStep", arity := 2, patterns := [(.pvar 0), (.pvar 1)], rhs := (.app (.app (.app (.app (.app (.app (.declConst "transportCert") (.declConst "num")) (.declConst "eqAt")) (.declConst "suc")) (.declConst "sucMove")) (.pvar 0)) (.pvar 1)) }]

def libraryRulesText : List String :=
  ["(Rule num-rec 4 ((PVar 0) (PVar 1) (PVar 2) (DeclConst zero)) (PVar 1))",
   "(Rule num-rec 4 ((PVar 0) (PVar 1) (PVar 2) (App (DeclConst suc) (PVar 3))) (App (App (PVar 2) (PVar 3)) (App (App (App (App (DeclConst num-rec) (PVar 0)) (PVar 1)) (PVar 2)) (PVar 3))))",
   "(Rule add 2 ((PVar 0) (DeclConst zero)) (PVar 0))",
   "(Rule add 2 ((PVar 0) (App (DeclConst suc) (PVar 1))) (App (DeclConst suc) (App (App (DeclConst add) (PVar 0)) (PVar 1))))",
   "(Rule eqAt 1 ((PVar 0)) (Id (DeclConst num) (App (App (DeclConst add) (DeclConst zero)) (PVar 0)) (PVar 0)))",
   "(Rule sucMove 2 ((PVar 0) (PVar 1)) (App (App (App (App (App (App (DeclConst id:eliminate) (DeclConst num)) (App (App (DeclConst add) (DeclConst zero)) (PVar 0))) (Lam (DeclConst num) (Lam (Id (DeclConst num) (App (App (DeclConst add) (DeclConst zero)) (PVar 0)) (idx 0)) (Id (DeclConst num) (App (DeclConst suc) (App (App (DeclConst add) (DeclConst zero)) (PVar 0))) (App (DeclConst suc) (idx 1)))))) (Refl (App (DeclConst suc) (App (App (DeclConst add) (DeclConst zero)) (PVar 0))))) (PVar 0)) (PVar 1)))",
   "(Rule keepCert 4 ((PVar 0) (PVar 1) (PVar 2) (PVar 3)) (Pair (PVar 2) (PVar 3)))",
   "(Rule transportCert 6 ((PVar 0) (PVar 1) (PVar 2) (PVar 3) (PVar 4) (PVar 5)) (Pair (App (PVar 2) (PVar 4)) (App (App (PVar 3) (PVar 4)) (PVar 5))))",
   "(Rule composeCert 6 ((PVar 0) (PVar 1) (PVar 2) (PVar 3) (PVar 4) (PVar 5)) (App (App (PVar 3) (Fst (App (App (PVar 2) (PVar 4)) (PVar 5)))) (Snd (App (App (PVar 2) (PVar 4)) (PVar 5)))))",
   "(Rule iterCert 6 ((DeclConst zero) (PVar 0) (PVar 1) (PVar 2) (PVar 3) (PVar 4)) (Pair (PVar 3) (PVar 4)))",
   "(Rule iterCert 6 ((App (DeclConst suc) (PVar 0)) (PVar 1) (PVar 2) (PVar 3) (PVar 4) (PVar 5)) (App (App (App (App (App (App (DeclConst iterCert) (PVar 0)) (PVar 1)) (PVar 2)) (PVar 3)) (Fst (App (App (PVar 3) (PVar 4)) (PVar 5)))) (Snd (App (App (PVar 3) (PVar 4)) (PVar 5)))))",
   "(Rule returnIter 1 ((PVar 0)) (Lam (Lam (Lam (Lam (Lam (App (App (App (App (App (App (DeclConst iterCert) (idx 3)) (PVar 0)) (idx 4)) (idx 2)) (idx 1)) (idx 0))))))))",
   "(Rule sucStep 2 ((PVar 0) (PVar 1)) (App (App (App (App (App (App (DeclConst transportCert) (DeclConst num)) (DeclConst eqAt)) (DeclConst suc)) (DeclConst sucMove)) (PVar 0)) (PVar 1)))"]

/-! ### Captured stored rules of the library on the binary `36b2cf70` -/

def libraryRulesCurrent : List KRule :=
  [{ head := "num-rec", arity := 4, patterns := [(.pvar 0), (.pvar 1), (.pvar 2), (.declConst "zero")], rhs := (.pvar 1) },
   { head := "num-rec", arity := 4, patterns := [(.pvar 0), (.pvar 1), (.pvar 2), (.app (.declConst "suc") (.pvar 3))], rhs := (.app (.app (.pvar 2) (.pvar 3)) (.app (.app (.app (.app (.declConst "num-rec") (.pvar 0)) (.pvar 1)) (.pvar 2)) (.pvar 3))) },
   { head := "add", arity := 2, patterns := [(.pvar 0), (.declConst "zero")], rhs := (.pvar 0) },
   { head := "add", arity := 2, patterns := [(.pvar 0), (.app (.declConst "suc") (.pvar 1))], rhs := (.app (.declConst "suc") (.app (.app (.declConst "add") (.pvar 0)) (.pvar 1))) },
   { head := "eqAt", arity := 1, patterns := [(.pvar 0)], rhs := (.ident (.declConst "num") (.app (.app (.declConst "add") (.declConst "zero")) (.pvar 0)) (.pvar 0)) },
   { head := "sucMove", arity := 2, patterns := [(.pvar 0), (.pvar 1)], rhs := (.app (.app (.app (.app (.app (.app (.declConst "id:eliminate") (.declConst "num")) (.app (.app (.declConst "add") (.declConst "zero")) (.pvar 0))) (.lamTyped (.declConst "num") (.lamTyped (.ident (.declConst "num") (.app (.app (.declConst "add") (.declConst "zero")) (.pvar 0)) (.idx 0)) (.ident (.declConst "num") (.app (.declConst "suc") (.app (.app (.declConst "add") (.declConst "zero")) (.pvar 0))) (.app (.declConst "suc") (.idx 1)))))) (.refl (.app (.declConst "suc") (.app (.app (.declConst "add") (.declConst "zero")) (.pvar 0))))) (.pvar 0)) (.pvar 1)) },
   { head := "keepCert", arity := 4, patterns := [(.pvar 0), (.pvar 1), (.pvar 2), (.pvar 3)], rhs := (.pair (.pvar 2) (.pvar 3)) },
   { head := "transportCert", arity := 6, patterns := [(.pvar 0), (.pvar 1), (.pvar 2), (.pvar 3), (.pvar 4), (.pvar 5)], rhs := (.pair (.app (.pvar 2) (.pvar 4)) (.app (.app (.pvar 3) (.pvar 4)) (.pvar 5))) },
   { head := "composeCert", arity := 6, patterns := [(.pvar 0), (.pvar 1), (.pvar 2), (.pvar 3), (.pvar 4), (.pvar 5)], rhs := (.app (.lamTyped (.sigma (.pvar 0) (.app (.pvar 1) (.idx 0))) (.app (.app (.pvar 3) (.fst (.idx 0))) (.snd (.idx 0)))) (.app (.app (.pvar 2) (.pvar 4)) (.pvar 5))) },
   { head := "iterCert", arity := 6, patterns := [(.declConst "zero"), (.pvar 0), (.pvar 1), (.pvar 2), (.pvar 3), (.pvar 4)], rhs := (.pair (.pvar 3) (.pvar 4)) },
   { head := "iterCert", arity := 6, patterns := [(.app (.declConst "suc") (.pvar 0)), (.pvar 1), (.pvar 2), (.pvar 3), (.pvar 4), (.pvar 5)], rhs := (.app (.lamTyped (.sigma (.pvar 1) (.app (.pvar 2) (.idx 0))) (.app (.app (.app (.app (.app (.app (.declConst "iterCert") (.pvar 0)) (.pvar 1)) (.pvar 2)) (.pvar 3)) (.fst (.idx 0))) (.snd (.idx 0)))) (.app (.app (.pvar 3) (.pvar 4)) (.pvar 5))) },
   { head := "returnIter", arity := 1, patterns := [(.pvar 0)], rhs := (.lamBare (.lamBare (.lamBare (.lamBare (.lamBare (.app (.app (.app (.app (.app (.app (.declConst "iterCert") (.idx 3)) (.pvar 0)) (.idx 4)) (.idx 2)) (.idx 1)) (.idx 0))))))) },
   { head := "sucStep", arity := 2, patterns := [(.pvar 0), (.pvar 1)], rhs := (.app (.app (.app (.app (.app (.app (.declConst "transportCert") (.declConst "num")) (.declConst "eqAt")) (.declConst "suc")) (.declConst "sucMove")) (.pvar 0)) (.pvar 1)) }]

def libraryRulesCurrentText : List String :=
  ["(Rule num-rec 4 ((PVar 0) (PVar 1) (PVar 2) (DeclConst zero)) (PVar 1))",
   "(Rule num-rec 4 ((PVar 0) (PVar 1) (PVar 2) (App (DeclConst suc) (PVar 3))) (App (App (PVar 2) (PVar 3)) (App (App (App (App (DeclConst num-rec) (PVar 0)) (PVar 1)) (PVar 2)) (PVar 3))))",
   "(Rule add 2 ((PVar 0) (DeclConst zero)) (PVar 0))",
   "(Rule add 2 ((PVar 0) (App (DeclConst suc) (PVar 1))) (App (DeclConst suc) (App (App (DeclConst add) (PVar 0)) (PVar 1))))",
   "(Rule eqAt 1 ((PVar 0)) (Id (DeclConst num) (App (App (DeclConst add) (DeclConst zero)) (PVar 0)) (PVar 0)))",
   "(Rule sucMove 2 ((PVar 0) (PVar 1)) (App (App (App (App (App (App (DeclConst id:eliminate) (DeclConst num)) (App (App (DeclConst add) (DeclConst zero)) (PVar 0))) (Lam (DeclConst num) (Lam (Id (DeclConst num) (App (App (DeclConst add) (DeclConst zero)) (PVar 0)) (idx 0)) (Id (DeclConst num) (App (DeclConst suc) (App (App (DeclConst add) (DeclConst zero)) (PVar 0))) (App (DeclConst suc) (idx 1)))))) (Refl (App (DeclConst suc) (App (App (DeclConst add) (DeclConst zero)) (PVar 0))))) (PVar 0)) (PVar 1)))",
   "(Rule keepCert 4 ((PVar 0) (PVar 1) (PVar 2) (PVar 3)) (Pair (PVar 2) (PVar 3)))",
   "(Rule transportCert 6 ((PVar 0) (PVar 1) (PVar 2) (PVar 3) (PVar 4) (PVar 5)) (Pair (App (PVar 2) (PVar 4)) (App (App (PVar 3) (PVar 4)) (PVar 5))))",
   "(Rule composeCert 6 ((PVar 0) (PVar 1) (PVar 2) (PVar 3) (PVar 4) (PVar 5)) (App (Lam (Sigma (PVar 0) (App (PVar 1) (idx 0))) (App (App (PVar 3) (Fst (idx 0))) (Snd (idx 0)))) (App (App (PVar 2) (PVar 4)) (PVar 5))))",
   "(Rule iterCert 6 ((DeclConst zero) (PVar 0) (PVar 1) (PVar 2) (PVar 3) (PVar 4)) (Pair (PVar 3) (PVar 4)))",
   "(Rule iterCert 6 ((App (DeclConst suc) (PVar 0)) (PVar 1) (PVar 2) (PVar 3) (PVar 4) (PVar 5)) (App (Lam (Sigma (PVar 1) (App (PVar 2) (idx 0))) (App (App (App (App (App (App (DeclConst iterCert) (PVar 0)) (PVar 1)) (PVar 2)) (PVar 3)) (Fst (idx 0))) (Snd (idx 0)))) (App (App (PVar 3) (PVar 4)) (PVar 5))))",
   "(Rule returnIter 1 ((PVar 0)) (Lam (Lam (Lam (Lam (Lam (App (App (App (App (App (App (DeclConst iterCert) (idx 3)) (PVar 0)) (idx 4)) (idx 2)) (idx 1)) (idx 0))))))))",
   "(Rule sucStep 2 ((PVar 0) (PVar 1)) (App (App (App (App (App (App (DeclConst transportCert) (DeclConst num)) (DeclConst eqAt)) (DeclConst suc)) (DeclConst sucMove)) (PVar 0)) (PVar 1)))"]

/-! ## The fixtures print as the captured text -/

set_option maxRecDepth 100000 in
theorem capturedTerm_text : capturedTerm.render = capturedTermText := by rfl

set_option maxRecDepth 100000 in
theorem capturedType_text : capturedType.render = capturedTypeText := by rfl

set_option maxRecDepth 100000 in
theorem capturedRules_text :
    capturedRules.map (KRule.render "PrimeRule") = capturedRulesText := by rfl

set_option maxRecDepth 100000 in
/-- Each declaration of the captured context prints as the draft printed it. -/
theorem capturedContext_text :
    capturedContext.map (fun entry => (entry.1, entry.2.render)) = capturedContextTexts := by rfl

set_option maxRecDepth 100000 in
theorem libraryRules_text : libraryRules.map (KRule.render "Rule") = libraryRulesText := by rfl

set_option maxRecDepth 100000 in
theorem libraryRulesCurrent_text :
    libraryRulesCurrent.map (KRule.render "Rule") = libraryRulesCurrentText := by rfl

/-! ## The native proof -/

/-- With lambda domains erased, the captured proof term is the compiler's output. -/
theorem capturedTerm_erases : capturedTerm.toTmAt 0 = some SetProfile.zeroAddTerm := by
  rfl

/-- The captured type is the proof family at the represented conclusion. -/
theorem capturedType_translates :
    capturedType.toTmAt 0 =
      some (FormationSensitiveHOLGenericProofFamily.proof holdsName SetProfile.zeroAddCode) := by
  rfl

/-- The binder domains: the motive's number, the step's number, and the
induction hypothesis at the represented premise `motive k`, a beta redex as
the compiler represents it. -/
theorem capturedTerm_domains :
    ((capturedTerm.domains[0]?).bind (KTerm.toTmAt 0) = some numT) ∧
      ((capturedTerm.domains[1]?).bind (KTerm.toTmAt 0) = some numT) ∧
      ((capturedTerm.domains[2]?).bind (KTerm.toTmAt 1) =
        some (FormationSensitiveHOLGenericProofFamily.proof holdsName (.app motiveCode (.var 0)))) := by
  refine ⟨rfl, rfl, rfl⟩

/-! ## The program's stored rules -/

/-- The two decoders for the quantifier instances in use, the decoder for
implication, and the two equations of `add`, as equations of the calculus. -/
theorem capturedRules_equations :
    capturedRules.mapM KRule.toEquation = some
      [⟨1, (FormationSensitiveHOLGenericProofFamily.proof holdsName
            (.app (.const (SetProfile.allName (.arr numTy .prop))) (.var 0)),
          .pi (.pi numT propT) (FormationSensitiveHOLGenericProofFamily.proof holdsName
            (.app (.var 1) (.var 0))))⟩,
       ⟨1, (FormationSensitiveHOLGenericProofFamily.proof holdsName
            (.app (.const (SetProfile.allName numTy)) (.var 0)),
          .pi numT (FormationSensitiveHOLGenericProofFamily.proof holdsName (.app (.var 1) (.var 0))))⟩,
       ⟨2, (FormationSensitiveHOLGenericProofFamily.proof holdsName
            (.app (.app (.const SetProfile.impName) (.var 1)) (.var 0)),
          .pi (FormationSensitiveHOLGenericProofFamily.proof holdsName (.var 1))
            (FormationSensitiveHOLGenericProofFamily.proof holdsName (.var 1)))⟩,
       ⟨2, (addNative (.var 1) (sucNative (.var 0)), sucNative (addNative (.var 1) (.var 0)))⟩,
       ⟨1, (addNative (.var 0) zeroNative, .var 0)⟩] := by
  rfl

/-- Every stored rule of the program generates root steps of the formal rules. -/
theorem capturedRules_sound :
    ∀ equation ∈ (capturedRules.mapM KRule.toEquation).getD [],
      ∀ {n : Nat} (substitution : Sub Tower.Head equation.1 n),
        targetRules.computation.step (subst substitution equation.2.1)
          (subst substitution equation.2.2) := by
  rw [capturedRules_equations]
  intro equation listed n substitution
  simp only [Option.getD_some, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl | rfl
  · exact RootStep.inherited (RootStep.declared
      (FormationSensitiveHOLGenericProofFamily.DecoderStep.universal (.arr numTy .prop)
        (substitution 0)))
  · exact RootStep.inherited (RootStep.declared
      (FormationSensitiveHOLGenericProofFamily.DecoderStep.universal numTy (substitution 0)))
  · exact RootStep.inherited (RootStep.declared
      (FormationSensitiveHOLGenericProofFamily.DecoderStep.implication
        (substitution 1) (substitution 0)))
  · exact RootStep.inherited (RootStep.inherited (RootStep.declared
      (SchemaTable.step_of_mem SetProfile.nativeEquations
        (List.getElem_mem (l := SetProfile.nativeEquations) (n := 1) (by decide))
        substitution)))
  · exact RootStep.inherited (RootStep.inherited (RootStep.declared
      (SchemaTable.step_of_mem SetProfile.nativeEquations
        (List.getElem_mem (l := SetProfile.nativeEquations) (n := 0) (by decide))
        substitution)))

/-! ## The program's context -/

theorem target_of_profile {name : DeclName} {type : Tower.Tm 0}
    (known : SetProfile.rules.constantType name = some type) :
    targetRules.constantType name = some type := by
  change combinedType SetProfile.proofRules SetProfile.assumptionDeclarations
    name = some type
  have known' : SetProfile.signature.rules.constantType name = some type := known
  have inProof : SetProfile.proofRules.constantType name = some type := by
    change combinedType SetProfile.signature.rules
      (FormationSensitiveHOLGenericProofFamily.declarations SetProfile.signature holdsName)
      name = some type
    rw [combinedType, known']
  rw [combinedType, inProof]

theorem holds_lookup :
    targetRules.constantType holdsName =
      some (FormationSensitiveHOLGenericProofFamily.proofType SetProfile.signature) := by
  change combinedType SetProfile.proofRules SetProfile.assumptionDeclarations
    holdsName = _
  have inProof : SetProfile.proofRules.constantType holdsName =
      some (FormationSensitiveHOLGenericProofFamily.proofType SetProfile.signature) :=
    combinedType_of_signature SetProfile.signature.rules
      (FormationSensitiveHOLGenericProofFamily.declarations SetProfile.signature holdsName)
      SetProfile.holdsName_fresh rfl
  rw [combinedType, inProof]

/-- Every declaration of the captured context has its formal type. -/
theorem capturedContext_types :
    ∀ entry ∈ capturedContext, ∃ type, entry.2.toTmAt 0 = some type ∧
      targetRules.constantType (.mkSimple entry.1) = some type := by
  intro entry listed
  simp only [capturedContext, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, rfl, SetProfile.target_lookup 2⟩
  · exact ⟨_, rfl, SetProfile.target_lookup 1⟩
  · exact ⟨_, rfl, SetProfile.target_lookup 0⟩
  · exact ⟨_, rfl, holds_lookup⟩
  · exact ⟨_, rfl, target_of_profile (SetProfile.lookup_allName (.arr numTy .prop))⟩
  · exact ⟨_, rfl, target_of_profile (SetProfile.lookup_allName numTy)⟩
  · exact ⟨_, rfl, target_of_profile (SetProfile.lookup_constant .suc)⟩
  · exact ⟨_, rfl, target_of_profile (SetProfile.lookup_eqName numTy)⟩
  · exact ⟨_, rfl, target_of_profile (SetProfile.lookup_constant .add)⟩
  · exact ⟨_, rfl, target_of_profile (SetProfile.lookup_constant .zero)⟩
  · exact ⟨_, rfl, target_of_profile (SetProfile.lookup_base .num)⟩
  · exact ⟨_, rfl, target_of_profile (SetProfile.lookup_constant .universeOf)⟩
  · exact ⟨_, rfl, target_of_profile (SetProfile.lookup_constant .epsilon)⟩
  · exact ⟨_, rfl, target_of_profile (SetProfile.lookup_constant .replacement)⟩
  · exact ⟨_, rfl, target_of_profile (SetProfile.lookup_constant .separation)⟩
  · exact ⟨_, rfl, target_of_profile (SetProfile.lookup_constant .power)⟩
  · exact ⟨_, rfl, target_of_profile (SetProfile.lookup_constant .union)⟩
  · exact ⟨_, rfl, target_of_profile (SetProfile.lookup_constant .empty)⟩
  · exact ⟨_, rfl, target_of_profile (SetProfile.lookup_constant .member)⟩
  · exact ⟨_, rfl, target_of_profile (SetProfile.lookup_constant .falsum)⟩
  · exact ⟨_, rfl, target_of_profile SetProfile.lookup_imp⟩
  · exact ⟨_, rfl, target_of_profile SetProfile.lookup_prop⟩
  · exact ⟨_, rfl, target_of_profile (SetProfile.lookup_base .set)⟩

/-! ## The native proof of ex falso

`set:native-proof ex-falso` for `ex-falso : ∀r. Falsum → r`, checked from
`(pf:all-intro (pf:imp-intro (pf:all-elim (pf:hyp 0) (pf:var 0))))`, on the same
binary. The request mentions `Falsum`, so its package carries the rule of the
definition. -/

def exFalsoCapturedTerm : KTerm :=
  (.lamTyped (.declConst "prop") (.lamTyped (.app (.declConst "__cetta_holds_df87b3cd8ab4b6383b1d0591") (.declConst "Falsum")) (.app (.idx 0) (.idx 1))))

def exFalsoCapturedTermText : String :=
  "(Lam (DeclConst prop) (Lam (App (DeclConst __cetta_holds_df87b3cd8ab4b6383b1d0591) (DeclConst Falsum)) (App (idx 0) (idx 1))))"

def exFalsoCapturedType : KTerm :=
  (.app (.declConst "__cetta_holds_df87b3cd8ab4b6383b1d0591") (.app (.declConst "all@prop") (.lamTyped (.declConst "prop") (.app (.app (.declConst "imp") (.declConst "Falsum")) (.idx 0)))))

def exFalsoCapturedTypeText : String :=
  "(App (DeclConst __cetta_holds_df87b3cd8ab4b6383b1d0591) (App (DeclConst all@prop) (Lam (DeclConst prop) (App (App (DeclConst imp) (DeclConst Falsum)) (idx 0)))))"

def exFalsoCapturedContext : List (String × KTerm) :=
  [("__cetta_holds_df87b3cd8ab4b6383b1d0591", (.pi (.declConst "prop") (.sortConst 0))),
   ("all@prop", (.pi (.pi (.declConst "prop") (.declConst "prop")) (.declConst "prop"))),
   ("UnivOf", (.pi (.declConst "set") (.declConst "set"))),
   ("Eps_set", (.pi (.pi (.declConst "set") (.declConst "prop")) (.declConst "set"))),
   ("Repl", (.pi (.declConst "set") (.pi (.pi (.declConst "set") (.declConst "set")) (.declConst "set")))),
   ("Sep", (.pi (.declConst "set") (.pi (.pi (.declConst "set") (.declConst "prop")) (.declConst "set")))),
   ("Power", (.pi (.declConst "set") (.declConst "set"))),
   ("Union", (.pi (.declConst "set") (.declConst "set"))),
   ("Empty", (.declConst "set")),
   ("In", (.pi (.declConst "set") (.pi (.declConst "set") (.declConst "prop")))),
   ("Falsum", (.declConst "prop")),
   ("imp", (.pi (.declConst "prop") (.pi (.declConst "prop") (.declConst "prop")))),
   ("prop", (.sortConst 0)),
   ("set", (.sortConst 0))]

def exFalsoCapturedContextTexts : List (String × String) :=
  [("__cetta_holds_df87b3cd8ab4b6383b1d0591",
    "(Pi (DeclConst prop) (Sort (LevelConst 0)))"),
   ("all@prop",
    "(Pi (Pi (DeclConst prop) (DeclConst prop)) (DeclConst prop))"),
   ("UnivOf",
    "(Pi (DeclConst set) (DeclConst set))"),
   ("Eps_set",
    "(Pi (Pi (DeclConst set) (DeclConst prop)) (DeclConst set))"),
   ("Repl",
    "(Pi (DeclConst set) (Pi (Pi (DeclConst set) (DeclConst set)) (DeclConst set)))"),
   ("Sep",
    "(Pi (DeclConst set) (Pi (Pi (DeclConst set) (DeclConst prop)) (DeclConst set)))"),
   ("Power",
    "(Pi (DeclConst set) (DeclConst set))"),
   ("Union",
    "(Pi (DeclConst set) (DeclConst set))"),
   ("Empty",
    "(DeclConst set)"),
   ("In",
    "(Pi (DeclConst set) (Pi (DeclConst set) (DeclConst prop)))"),
   ("Falsum",
    "(DeclConst prop)"),
   ("imp",
    "(Pi (DeclConst prop) (Pi (DeclConst prop) (DeclConst prop)))"),
   ("prop",
    "(Sort (LevelConst 0))"),
   ("set",
    "(Sort (LevelConst 0))")]

def exFalsoCapturedRules : List KRule :=
  [{ head := "__cetta_holds_df87b3cd8ab4b6383b1d0591", arity := 1, patterns := [(.app (.declConst "all@prop") (.pvar 0))], rhs := (.pi (.declConst "prop") (.app (.declConst "__cetta_holds_df87b3cd8ab4b6383b1d0591") (.app (.pvar 0) (.idx 0)))) },
   { head := "__cetta_holds_df87b3cd8ab4b6383b1d0591", arity := 1, patterns := [(.app (.app (.declConst "imp") (.pvar 0)) (.pvar 1))], rhs := (.pi (.app (.declConst "__cetta_holds_df87b3cd8ab4b6383b1d0591") (.pvar 0)) (.app (.declConst "__cetta_holds_df87b3cd8ab4b6383b1d0591") (.pvar 1))) },
   { head := "Falsum", arity := 0, patterns := [], rhs := (.app (.declConst "all@prop") (.lamTyped (.declConst "prop") (.idx 0))) }]

def exFalsoCapturedRulesText : List String :=
  ["(PrimeRule __cetta_holds_df87b3cd8ab4b6383b1d0591 1 ((App (DeclConst all@prop) (PVar 0))) (Pi (DeclConst prop) (App (DeclConst __cetta_holds_df87b3cd8ab4b6383b1d0591) (App (PVar 0) (idx 0)))))",
   "(PrimeRule __cetta_holds_df87b3cd8ab4b6383b1d0591 1 ((App (App (DeclConst imp) (PVar 0)) (PVar 1))) (Pi (App (DeclConst __cetta_holds_df87b3cd8ab4b6383b1d0591) (PVar 0)) (App (DeclConst __cetta_holds_df87b3cd8ab4b6383b1d0591) (PVar 1))))",
   "(PrimeRule Falsum 0 () (App (DeclConst all@prop) (Lam (DeclConst prop) (idx 0))))"]

set_option maxRecDepth 100000 in
theorem exFalsoCapturedTerm_text : exFalsoCapturedTerm.render = exFalsoCapturedTermText := by rfl

set_option maxRecDepth 100000 in
theorem exFalsoCapturedType_text : exFalsoCapturedType.render = exFalsoCapturedTypeText := by rfl

set_option maxRecDepth 100000 in
/-- Each declaration of the captured context prints as the draft printed it. -/
theorem exFalsoCapturedContext_text :
    exFalsoCapturedContext.map (fun entry => (entry.1, entry.2.render)) =
      exFalsoCapturedContextTexts := by
  rfl

set_option maxRecDepth 100000 in
theorem exFalsoCapturedRules_text :
    exFalsoCapturedRules.map (KRule.render "PrimeRule") = exFalsoCapturedRulesText := by
  rfl

/-- With lambda domains erased, the captured term is the compiler's output from
the source proof of ex falso, `λr. λh. h r`. -/
theorem exFalsoCapturedTerm_erases :
    exFalsoCapturedTerm.toTmAt 0 = some SetProfile.exFalsoTerm := by
  rfl

theorem exFalso_compiles_captured :
    HOLNativeGenericProofCompiler.Modulo.compileModulo SetProfile.definedSignature
      SetProfile.exFalso Fin.elim0 Fin.elim0 = exFalsoCapturedTerm.toTmAt 0 :=
  SetProfile.exFalso_compiles.trans exFalsoCapturedTerm_erases.symm

/-- The binder domains: the proposition `r`, and the hypothesis at the proof
family of `Falsum`, by its name. -/
theorem exFalsoCapturedTerm_domains :
    ((exFalsoCapturedTerm.domains[0]?).bind (KTerm.toTmAt 0) =
        some (.const SetProfile.propName)) ∧
      ((exFalsoCapturedTerm.domains[1]?).bind (KTerm.toTmAt 1) =
        some (FormationSensitiveHOLGenericProofFamily.proof holdsName
          (.const (constantName .falsum)))) :=
  ⟨rfl, rfl⟩

/-- The captured type is the proof family at the represented statement
`∀r. Falsum → r`, `Falsum` by its name. -/
theorem exFalsoCapturedType_translates :
    exFalsoCapturedType.toTmAt 0 =
      some (FormationSensitiveHOLGenericProofFamily.proof holdsName SetProfile.exFalsoCode) := by
  rfl

/-- The decoder of `all@prop`, the decoder of implication, and the rule of the
definition `Falsum ⟶ all@prop (λp. p)`, as equations of the calculus. -/
theorem exFalsoCapturedRules_equations :
    exFalsoCapturedRules.mapM KRule.toEquation = some
      [⟨1, (FormationSensitiveHOLGenericProofFamily.proof holdsName
            (.app (.const (SetProfile.allName .prop)) (.var 0)),
          .pi (.const SetProfile.propName)
            (FormationSensitiveHOLGenericProofFamily.proof holdsName (.app (.var 1) (.var 0))))⟩,
       ⟨2, (FormationSensitiveHOLGenericProofFamily.proof holdsName
            (.app (.app (.const SetProfile.impName) (.var 1)) (.var 0)),
          .pi (FormationSensitiveHOLGenericProofFamily.proof holdsName (.var 1))
            (FormationSensitiveHOLGenericProofFamily.proof holdsName (.var 1)))⟩,
       ⟨0, (.const (constantName .falsum), SetProfile.falsumBody)⟩] := by
  rfl

/-- **Every stored rule of the request is a root step of the formal rules with
the rule of `Falsum`**: the decoders, and the rule of the definition by its
δ-step. -/
theorem exFalsoCapturedRules_sound :
    ∀ equation ∈ (exFalsoCapturedRules.mapM KRule.toEquation).getD [],
      ∀ {n : Nat} (substitution : Sub Tower.Head equation.1 n),
        SetProfile.definedProofRules.computation.step (subst substitution equation.2.1)
          (subst substitution equation.2.2) := by
  rw [exFalsoCapturedRules_equations]
  intro equation listed n substitution
  simp only [Option.getD_some, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl
  · exact RootStep.declared
      (FormationSensitiveHOLGenericProofFamily.DecoderStep.universal .prop (substitution 0))
  · exact RootStep.declared
      (FormationSensitiveHOLGenericProofFamily.DecoderStep.implication
        (substitution 1) (substitution 0))
  · change SetProfile.definedProofRules.computation.step (.const (constantName .falsum))
      (subst (substitution : Sub Tower.Head 0 n) SetProfile.falsumBody)
    rw [TypedEquality.Normalization.subst_closed]
    exact RootStep.inherited SetProfile.falsum_delta

theorem definedTarget_of_profile {name : DeclName} {type : Tower.Tm 0}
    (known : SetProfile.rules.constantType name = some type) :
    SetProfile.definedProofRules.constantType name = some type := by
  have known' : SetProfile.definedSignature.rules.constantType name = some type := known
  change combinedType SetProfile.definedSignature.rules
    (FormationSensitiveHOLGenericProofFamily.declarations SetProfile.definedSignature holdsName)
    name = some type
  rw [combinedType, known']

theorem definedHolds_lookup :
    SetProfile.definedProofRules.constantType holdsName =
      some (FormationSensitiveHOLGenericProofFamily.proofType SetProfile.definedSignature) :=
  combinedType_of_signature SetProfile.definedSignature.rules
    (FormationSensitiveHOLGenericProofFamily.declarations SetProfile.definedSignature holdsName)
    SetProfile.definedHoldsName_fresh rfl

/-- **Every declaration of the captured context has its formal type** in the
rules with the rule of `Falsum`, the declaration `Falsum : prop` included. -/
theorem exFalsoCapturedContext_types :
    ∀ entry ∈ exFalsoCapturedContext, ∃ type, entry.2.toTmAt 0 = some type ∧
      SetProfile.definedProofRules.constantType (.mkSimple entry.1) = some type := by
  intro entry listed
  simp only [exFalsoCapturedContext, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact ⟨_, rfl, definedHolds_lookup⟩
  · exact ⟨_, rfl, definedTarget_of_profile (SetProfile.lookup_allName .prop)⟩
  · exact ⟨_, rfl, definedTarget_of_profile (SetProfile.lookup_constant .universeOf)⟩
  · exact ⟨_, rfl, definedTarget_of_profile (SetProfile.lookup_constant .epsilon)⟩
  · exact ⟨_, rfl, definedTarget_of_profile (SetProfile.lookup_constant .replacement)⟩
  · exact ⟨_, rfl, definedTarget_of_profile (SetProfile.lookup_constant .separation)⟩
  · exact ⟨_, rfl, definedTarget_of_profile (SetProfile.lookup_constant .power)⟩
  · exact ⟨_, rfl, definedTarget_of_profile (SetProfile.lookup_constant .union)⟩
  · exact ⟨_, rfl, definedTarget_of_profile (SetProfile.lookup_constant .empty)⟩
  · exact ⟨_, rfl, definedTarget_of_profile (SetProfile.lookup_constant .member)⟩
  · exact ⟨_, rfl, definedTarget_of_profile (SetProfile.lookup_constant .falsum)⟩
  · exact ⟨_, rfl, definedTarget_of_profile SetProfile.lookup_imp⟩
  · exact ⟨_, rfl, definedTarget_of_profile SetProfile.lookup_prop⟩
  · exact ⟨_, rfl, definedTarget_of_profile (SetProfile.lookup_base .set)⟩

/-- **The captured proof is typed at the captured type** in the formal rules
with the rule of `Falsum`: the hypothesis at `Holds Falsum` is applied to `r`
after the δ-step and the decoding of the quantifier. -/
theorem exFalsoCaptured_typed :
    ∃ term type, exFalsoCapturedTerm.toTmAt 0 = some term ∧
      exFalsoCapturedType.toTmAt 0 = some type ∧
      Typing SetProfile.definedProofRules .nil term type :=
  ⟨_, _, exFalsoCapturedTerm_erases, exFalsoCapturedType_translates, SetProfile.exFalso_typed⟩

/-! ## The library's stored rules -/

/-- `step₂ (fst (step₁ x e)) (snd (step₁ x e))`: the stored successor of
`composeCert`, one beta step after the shared equation. -/
abbrev composeContracted : Σ arity : Nat, Tower.Tm arity × Tower.Tm arity :=
  ⟨6, (composeEquation.2.1, app2 (.var 2) (.fst (app2 (.var 3) (.var 1) (.var 0)))
    (.snd (app2 (.var 3) (.var 1) (.var 0))))⟩

/-- `iterCert n A P step (fst (step x e)) (snd (step x e))`: the stored
successor of `iterCert`, one beta step after the shared equation. -/
abbrev iterSucContracted : Σ arity : Nat, Tower.Tm arity × Tower.Tm arity :=
  ⟨6, (iterSucEquation.2.1, iterApp (.var 5) (.var 4) (.var 3) (.var 2)
    (.fst (app2 (.var 2) (.var 1) (.var 0))) (.snd (app2 (.var 2) (.var 1) (.var 0))))⟩

/-- The library's stored rules, as equations of the calculus: the formal equations
of the package and of `add`, except the two contracted successors. -/
theorem libraryRules_equations :
    libraryRules.mapM KRule.toEquation = some
      [numRecZeroEquation, numRecSucEquation,
       ⟨1, (addNative (.var 0) zeroNative, .var 0)⟩,
       ⟨2, (addNative (.var 1) (sucNative (.var 0)), sucNative (addNative (.var 1) (.var 0)))⟩,
       eqAtEquation, sucMoveEquation, keepEquation, transportEquation, composeContracted,
       iterZeroEquation, iterSucContracted, returnIterEquation, sucStepEquation] := by
  rfl

/-- On the binary `36b2cf70` the library's stored rules are exactly the formal
equations, the successors of `composeCert` and `iterCert` included: typing
reduction and ordinary evaluation use the same equations. -/
theorem libraryRulesCurrent_equations :
    libraryRulesCurrent.mapM KRule.toEquation = some
      [numRecZeroEquation, numRecSucEquation,
       ⟨1, (addNative (.var 0) zeroNative, .var 0)⟩,
       ⟨2, (addNative (.var 1) (sucNative (.var 0)), sucNative (addNative (.var 1) (.var 0)))⟩,
       eqAtEquation, sucMoveEquation, keepEquation, transportEquation, composeEquation,
       iterZeroEquation, iterSucEquation, returnIterEquation, sucStepEquation] := by
  rfl

/-- A contracted successor is reached from the shared equation's redex by the
equation and one beta step, at every instance. -/
theorem composeContracted_after_shared {n : Nat} (substitution : Sub Tower.Head 6 n) :
    Runs (subst substitution composeContracted.2.1) (subst substitution composeContracted.2.2) := by
  have unfold := Runs.equation listed_compose substitution
  rw [show subst substitution composeEquation.2.2 =
      shared (substitution 3) (substitution 2) (substitution 1) (substitution 0) from
    CertifiedTransforms.subst_shared substitution _ _ _ _] at unfold
  have contract := Runs.beta (sharedBody (substitution 2))
    (app2 (substitution 3) (substitution 1) (substitution 0))
  rw [shared_contracts] at contract
  exact unfold.trans contract

theorem iterSucContracted_after_shared {n : Nat} (substitution : Sub Tower.Head 6 n) :
    Runs (subst substitution iterSucContracted.2.1) (subst substitution iterSucContracted.2.2) := by
  have unfold := Runs.equation listed_iterSuc substitution
  rw [show subst substitution iterSucEquation.2.2 =
      shared (substitution 2) (subst substitution (iterPartial (.var 5) (.var 4) (.var 3) (.var 2)))
        (substitution 1) (substitution 0) from
    CertifiedTransforms.subst_shared substitution _ _ _ _] at unfold
  have contract := Runs.beta (sharedBody (subst substitution (iterPartial (.var 5) (.var 4) (.var 3)
    (.var 2)))) (app2 (substitution 2) (substitution 1) (substitution 0))
  rw [shared_contracts] at contract
  exact unfold.trans contract

/-- The contracted successors are themselves typed at their telescopes. -/
theorem composeContracted_typed :
    Typing R composeTelescope composeContracted.2.2 (.sigma (.var 5) (.app (.var 5) (.var 0))) := by
  have package := CertifiedTransforms.step_application_typed (A := .var 5)
    (P := .app (.var 5) (.var 0)) (Typing.var (R := R) (Γ := composeTelescope) 3)
    (Typing.var 1) (Typing.var 0)
  exact CertifiedTransforms.step_application_typed (Typing.var 2) (Typing.fstElim package)
    (Typing.sndElim package)

theorem iterSucContracted_typed :
    Typing R iterSucTelescope iterSucContracted.2.2 (.sigma (.var 4) (.app (.var 4) (.var 0))) := by
  have package := CertifiedTransforms.step_application_typed (A := .var 4)
    (P := .app (.var 4) (.var 0)) (Typing.var (R := R) (Γ := iterSucTelescope) 2)
    (Typing.var 1) (Typing.var 0)
  have morphism : FormationSensitive.CtxMor R iterSucTelescope iterSucTelescope
      (patternValues ![.var 5, .var 4, .var 3, .var 2, .fst (app2 (.var 2) (.var 1) (.var 0)),
        .snd (app2 (.var 2) (.var 1) (.var 0))]) := by
    intro index
    refine Fin.cases ?_ (fun index => ?_) index
    · exact Typing.sndElim package
    refine Fin.cases ?_ (fun index => ?_) index
    · exact Typing.fstElim package
    refine Fin.cases ?_ (fun index => ?_) index
    · exact Typing.var 2
    refine Fin.cases ?_ (fun index => ?_) index
    · exact Typing.var 3
    refine Fin.cases ?_ (fun index => ?_) index
    · exact Typing.var 4
    refine Fin.cases ?_ (fun index => index.elim0) index
    exact Typing.var 5
  exact iterCall_typed.substitute morphism

/-! ## Axiom audit -/

#print axioms capturedTerm_text
#print axioms libraryRulesCurrent_equations
#print axioms capturedTerm_erases
#print axioms capturedType_translates
#print axioms capturedTerm_domains
#print axioms capturedRules_equations
#print axioms capturedRules_sound
#print axioms capturedContext_types
#print axioms libraryRules_text
#print axioms libraryRules_equations
#print axioms composeContracted_after_shared
#print axioms iterSucContracted_after_shared
#print axioms composeContracted_typed
#print axioms iterSucContracted_typed
#print axioms capturedContext_text
#print axioms exFalsoCapturedContext_text
#print axioms exFalsoCapturedRules_text
#print axioms exFalsoCapturedRules_sound
#print axioms exFalsoCapturedContext_types
#print axioms exFalsoCaptured_typed

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ArtifactComparison
