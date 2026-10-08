import Mettapedia.SetTheory.Profiles.CommonCoreClassical
import Mettapedia.SetTheory.Profiles.CommonCoreSyntax

/-!
# Logical compilation of the common material profile

The first-order core is compiled into the native implication/quantifier
language. Conjunction, disjunction and existence use their Church encodings;
set and proposition binders have separate indexed namespaces. The compiler
preserves truth in every membership structure, before either concrete model
is instantiated. This is a semantic result for compiled logical terms; native
execution and the C reader require their own qualification.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.CommonCoreLogicalCompilation

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualMaterialLogic (Formula)
open ContextualMaterialSetTheory
open Mettapedia.SetTheory.CarveOuts.Sites (Tarski)
open Mettapedia.GSLT.LanguageDef.CertificateGSLT (WireTerm)

universe u

/-- The native logical primitives, with independently scoped set and
proposition variables. -/
inductive Logical : Nat → Nat → Type
  | equal {sets props} (first second : Fin sets) : Logical sets props
  | member {sets props} (child parent : Fin sets) : Logical sets props
  | proposition {sets props} (index : Fin props) : Logical sets props
  | imply {sets props} (first second : Logical sets props) : Logical sets props
  | allSet {sets props} (body : Logical (sets+1) props) : Logical sets props
  | allProp {sets props} (body : Logical sets (props+1)) : Logical sets props

def evaluate {S : Type u} (member : S → S → Prop) :
    {sets props : Nat} → Logical sets props → (Fin sets → S) → (Fin props → Prop) → Prop
  | _, _, .equal first second, environment, _ => environment first = environment second
  | _, _, .member child parent, environment, _ => member (environment child) (environment parent)
  | _, _, .proposition index, _, propositions => propositions index
  | _, _, .imply first second, environment, propositions =>
      evaluate member first environment propositions → evaluate member second environment propositions
  | _, _, .allSet body, environment, propositions =>
      ∀ value, evaluate member body (Fin.cases value environment) propositions
  | _, _, .allProp body, environment, propositions =>
      ∀ value, evaluate member body environment (Fin.cases value propositions)

def compile : {sets : Nat} → Formula sets → (props : Nat) → Logical sets props
  | _, .bottom, _ => .allProp (.proposition 0)
  | _, .equal first second, _ => .equal first second
  | _, .member child parent, _ => .member child parent
  | _, .both first second, props =>
      .allProp (.imply (.imply (compile first (props+1))
        (.imply (compile second (props+1)) (.proposition 0))) (.proposition 0))
  | _, .either first second, props =>
      .allProp (.imply (.imply (compile first (props+1)) (.proposition 0))
        (.imply (.imply (compile second (props+1)) (.proposition 0)) (.proposition 0)))
  | _, .imply first second, props => .imply (compile first props) (compile second props)
  | _, .all body, props => .allSet (compile body props)
  | _, .exist body, props =>
      .allProp (.imply (.allSet (.imply (compile body (props+1)) (.proposition 0)))
        (.proposition 0))

theorem churchFalse_iff : (∀ result : Prop, result) ↔ False :=
  ⟨fun all => all False, fun impossible => impossible.elim⟩

theorem churchAnd_iff (first second : Prop) :
    (∀ result : Prop, (first → second → result) → result) ↔ first ∧ second :=
  ⟨fun use => use (first ∧ second) (fun a b => ⟨a, b⟩),
   fun pair _ use => use pair.1 pair.2⟩

theorem churchOr_iff (first second : Prop) :
    (∀ result : Prop, (first → result) → (second → result) → result) ↔ first ∨ second :=
  ⟨fun use => use (first ∨ second) Or.inl Or.inr,
   fun alternatives _ firstUse secondUse => alternatives.elim firstUse secondUse⟩

theorem churchExists_iff {S : Type u} (predicate : S → Prop) :
    (∀ result : Prop, (∀ value, predicate value → result) → result) ↔ ∃ value, predicate value :=
  ⟨fun use => use (∃ value, predicate value) (fun value witness => ⟨value, witness⟩),
   fun witness _ use => witness.elim use⟩

/-- No classical principle is used to recover the first-order connectives
from their proposition-polymorphic eliminators. -/
theorem evaluate_compile {S : Type u} (member : S → S → Prop) {sets : Nat}
    (body : Formula sets) (props : Nat) (environment : Fin sets → S)
    (propositions : Fin props → Prop) :
    evaluate member (compile body props) environment propositions ↔ Tarski member body environment := by
  induction body generalizing props with
  | bottom => exact churchFalse_iff
  | equal => exact Iff.rfl
  | member => exact Iff.rfl
  | both first second firstIH secondIH =>
      simpa only [compile, evaluate, Tarski, firstIH, secondIH, Fin.cases_zero] using
        churchAnd_iff (Tarski member first environment) (Tarski member second environment)
  | either first second firstIH secondIH =>
      simpa only [compile, evaluate, Tarski, firstIH, secondIH, Fin.cases_zero] using
        churchOr_iff (Tarski member first environment) (Tarski member second environment)
  | imply first second firstIH secondIH =>
      exact imp_congr (firstIH _ _ _) (secondIH _ _ _)
  | all body ih =>
      exact forall_congr' fun value => ih props (Fin.cases value environment) propositions
  | exist body ih =>
      simpa only [compile, evaluate, Tarski, ih, Fin.cases_zero] using
        churchExists_iff (fun value => Tarski member body (Fin.cases value environment))

/-- Universal closure uses exactly the free set-variable slots. -/
def close : (count : Nat) → Formula count → Formula 0
  | 0, body => body
  | count+1, body => close count (.all body)

theorem close_valid {S : Type u} (member : S → S → Prop) (count : Nat)
    (body : Formula count) (valid : ∀ environment, Tarski member body environment)
    (emptyEnvironment : Fin 0 → S) : Tarski member (close count body) emptyEnvironment := by
  induction count with
  | zero => exact valid emptyEnvironment
  | succ count ih =>
      exact ih (.all body) (fun environment value => valid (Fin.cases value environment))

theorem wellFounded_compiled {count : Nat} {body : Formula count}
    (adopted : CommonCore.Axiom body) :
    evaluate (fun child parent : ZFSet.{u} => child ∈ parent)
      (compile (close count body) 0) Fin.elim0 Fin.elim0 :=
  (evaluate_compile _ _ _ _ _).mpr
    (close_valid _ _ _ (CommonCoreClassical.wellFounded_validate adopted) Fin.elim0)

theorem hyperset_compiled {count : Nat} {body : Formula count}
    (adopted : CommonCore.Axiom body) :
    evaluate (fun child parent : HSet.{u} => child ∈ parent)
      (compile (close count body) 0) Fin.elim0 Fin.elim0 :=
  (evaluate_compile _ _ _ _ _).mpr
    (close_valid _ _ _ (CommonCoreClassical.hyperset_validate adopted) Fin.elim0)

/-- Serialization follows the lexical binders in the native language.
For a closed input each binder's name is fresh along its scope; sibling
scopes may reuse a name. Open name environments require a freshness
invariant, established separately by the scope reconstruction theorem. -/
def encode : {sets props : Nat} → Logical sets props →
    (Fin sets → String) → (Fin props → String) → WireTerm
  | _, _, .equal first second, environment, _ =>
      .list [.symbol "eq", .symbol "set", .symbol (environment first), .symbol (environment second)]
  | _, _, .member child parent, environment, _ =>
      .list [.symbol "In", .symbol (environment child), .symbol (environment parent)]
  | _, _, .proposition index, _, propositions => .symbol (propositions index)
  | _, _, .imply first second, environment, propositions =>
      .list [.symbol "imp", encode first environment propositions, encode second environment propositions]
  | sets, props, .allSet body, environment, propositions =>
      let name := "_core_s" ++ toString (sets+props)
      .list [.symbol "all", .symbol "set", .list [.symbol "lam", .symbol name,
        encode body (Fin.cases name environment) propositions]]
  | sets, props, .allProp body, environment, propositions =>
      let name := "_core_p" ++ toString (sets+props)
      .list [.symbol "all", .symbol "prop", .list [.symbol "lam", .symbol name,
        encode body environment (Fin.cases name propositions)]]

def encodeSentence (body : Formula 0) : WireTerm := encode (compile body 0) Fin.elim0 Fin.elim0

def boundedSeparationSentence (count : Nat)
    (body : GraphBoundedFormulaRealization.BoundedFormula (count+1)) : Formula 0 :=
  close count (separationAxiom (GraphBoundedFormulaRealization.toFormula body))

def primitiveLaws : List (String × Formula 0) :=
  [("coreEmpty", emptyAxiom), ("corePairing", pairingAxiom),
   ("coreUnion", unionAxiom), ("coreInfinity", infinityAxiom),
   ("coreExtensionality", close 2 extensionalityAxiom)]

theorem wellFounded_foundation_compiled :
    evaluate (fun child parent : ZFSet.{u} => child ∈ parent)
      (compile CommonCore.foundationAxiom 0) Fin.elim0 Fin.elim0 :=
  (evaluate_compile _ _ _ _ _).mpr (CommonCoreClassical.wellFounded_foundation Fin.elim0)

/-- Excluded middle is a separate logical-profile law, not a common law. -/
def excludedMiddle : Logical 0 0 :=
  .allProp (.allProp (.imply (.imply (.proposition 1) (.proposition 0))
    (.imply (.imply (.imply (.proposition 1) (.allProp (.proposition 0)))
      (.proposition 0)) (.proposition 0))))

theorem excludedMiddle_evaluated {S : Type u} (member : S → S → Prop)
    (environment : Fin 0 → S) : evaluate member excludedMiddle environment Fin.elim0 := by
  intro proposition result positive negative
  rcases Classical.em proposition with yes | no
  · exact positive yes
  · exact negative (fun witness => (no witness).elim)

end Mettapedia.SetTheory.Profiles.CommonCoreLogicalCompilation
