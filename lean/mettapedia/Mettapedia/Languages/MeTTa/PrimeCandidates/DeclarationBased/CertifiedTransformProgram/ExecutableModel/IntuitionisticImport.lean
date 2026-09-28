import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ChoiceNonderivability
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueSound
import Mettapedia.Logic.ModalCompanion

/-!
# Intuitionistic derivations as proofs of the package

Intuitionistic Hilbert derivations from assumptions (`IntDeriv`) become proof terms of the
object package `objectRules`, and propositional formulas become its proposition codes.
Composed with Gödel's proof transformations, classical derivations of geometric implications
and S4 derivations of Gödel translations become proofs of the package as well.

## Formulas as codes

A formula becomes a code by the second-order definitions of the connectives, going back to
Russell and made systematic by Prawitz, here with the quantifier `all@prop` over codes:

* an atom is read through an assignment `atoms : ℕ → Tm n` of codes;
* `φ ⊃ ψ` is `imp φ ψ`, and `⊥` is `∀c. c`, that is `all@prop (λc. c)` (`botCode`);
* `φ ∧ ψ` is `∀c. (φ ⇒ ψ ⇒ c) ⇒ c` and `φ ∨ ψ` is `∀c. (φ ⇒ c) ⇒ (ψ ⇒ c) ⇒ c`.

In Foundation, negation `¬φ` is `φ ⊃ ⊥`, truth `⊤` is `⊥ ⊃ ⊥`, and equivalence is the
conjunction of the two implications, so their codes follow (`encode_neg`, `encode_top`,
`encode_iff`). The code of every formula is a code when every atom is (`encode_typed`).

## Derivations as proof terms

The decoder computes `holds (imp p q)` to `Π (_ : holds p). holds q` and
`holds (all@prop f)` to `Π (c : prop). holds (f c)`. A proof term is typed through these
steps by the typed root-computation rule, and for `all@prop (λc. B)` a β-step under the binder
returns `holds B`. Read through the decoding, the codes have the natural-deduction rules of
their connectives (`impIntroO`, `impElimO`, `allIntroO`, `allElimO`, `botElimO`, `pairO`,
`andElimO`, `inlO`, `inrO`, `caseO`), and each axiom of the Hilbert calculus has a combinator
as its proof:

* `K = λx. λy. x` and `S = λf. λg. λx. f x (g x)` for the implicational axioms;
* `λz. z r` for `⊥ ⊃ r`;
* `λz. z p K`, `λz. z q (λx. λy. y)` and `λx. λy. λc. λk. k x y` for conjunction;
* `λx. λc. λl. λr. l x`, `λy. λc. λl. λr. r y` and `λf. λg. λz. z r f g` for disjunction.

Modus ponens is application. `IntDeriv.toPrime` translates a derivation given a proof term
for each assumption. `IntDeriv.primeProof` places the assumptions as proof variables of type
`holds (encode δ)` in the context `hypCtx Γ atoms Δ` after the context `Γ` of the atoms, the
head of the list innermost. Both are computable functions on derivation trees; their typing
(`IntDeriv.toPrime_typed`, `IntDeriv.primeProof_typed`) is a theorem. Since the package is
strongly normalizing, so is every imported proof (`IntDeriv.primeProof_sn`).

## Classical and modal derivations

* `importGeometric`: a classical derivation of a geometric implication from geometric
  implications is made intuitionistic by Gödel's Theorem 62, the propositional geometric
  case of Barr's theorem (`theorem62OfClassical`), and imported.
* `importS4`: an S4 derivation of the Gödel translation `U(A)` from `U(Δ)` becomes an
  intuitionistic derivation of `A` from `Δ` by Gödel's Theorem 64 (`s4GödelToIntDeriv`),
  and is imported.

## Controls

* Positive. The geometric consequence `p₀ ⊃ p₃` of `p₀ ⊃ p₁ ∨ p₂`, `p₁ ⊃ p₃` and
  `p₂ ⊃ p₃` is imported by Barr's route (`example_importGeometric_typed`). The derivation
  `S K K` of `p ⊃ p` imports to `S K K` (`selfImp_primeProof`), and with its atom bound by
  `all@prop` the closed term `λc. S K K` proves `all@prop (λc. imp c c)`
  (`selfImp_closed`). A classical derivation of `p ⊃ p` by cases on `p ∨ ¬p` is imported
  by Barr's route to a closed proof of the same code (`lemSelfImp_closed`).
* Negative. Excluded middle `p ∨ ¬p` has a classical derivation, but no intuitionistic
  one; it is not a geometric implication, nor intuitionistically equivalent to one; and its
  Gödel translation has no S4 derivation. So no route imports it (`lem₀_not_imported`).
* Consistency. No import proves the bottom code `∀c. c`, by the consistency of the package
  (`consistent_bot`). Hence there is no intuitionistic derivation of `⊥`, no classical
  derivation of the geometric implication `⊤ ⊃ ⊥`, and no S4 derivation of `⊥`
  (`IntDeriv.encode_ne_botCode`, `imports_consistent`).

The transformations of Theorems 62 and 64 can produce exponentially large derivations, so
the examples that use them are typing theorems and are not evaluated.

## References

* B. Russell, *The Principles of Mathematics*, Cambridge University Press, 1903.
* D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*, Almqvist & Wiksell, 1965.
* J.-Y. Girard, Y. Lafont and P. Taylor, *Proofs and Types*, Cambridge University Press,
  1989, ch. 11.
* K. Gödel, *Results on Foundations*, M. Hämeen-Anttila and J. von Plato (eds.), Springer,
  2023 (notebook *Resultate Grundlagen*, Theorems 62–64).
* S. Negri and J. von Plato, *Intuitionistic and modal logic in Gödel's Resultate
  Grundlagen*, Logique et Analyse 268, 439–465, doi:10.2143/LEA.268.0.3295055.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Mettapedia.Logic.ModalCompanion
open LO
open Propositional.Formula (gödelTranslate)
open Package (U0)

namespace CodeModel

/-! ## The codes of formulas -/

section Codes

variable {n : Nat}

/-- The quantifier over codes applied to a family: `all@prop f`. -/
abbrev allPropOf (f : Tower.Tm n) : Tower.Tm n := .app (.const allPropN) f

/-- Conjunction of codes, impredicatively: `∀c. (p ⇒ q ⇒ c) ⇒ c`. -/
def andCode (p q : Tower.Tm n) : Tower.Tm n :=
  allPropOf (.lam (programCodes.impOf
    (programCodes.impOf (Presentation.rename wk p)
      (programCodes.impOf (Presentation.rename wk q) (.var 0)))
    (.var 0)))

/-- Disjunction of codes, impredicatively: `∀c. (p ⇒ c) ⇒ (q ⇒ c) ⇒ c`. -/
def orCode (p q : Tower.Tm n) : Tower.Tm n :=
  allPropOf (.lam (programCodes.impOf
    (programCodes.impOf (Presentation.rename wk p) (.var 0))
    (programCodes.impOf (programCodes.impOf (Presentation.rename wk q) (.var 0)) (.var 0))))

/-- The code of a propositional formula, with the atoms read through `atoms`: `⊃` is `imp`,
`⊥` is `∀c. c`, and `∧`, `∨` are the impredicative codes. -/
def encode (atoms : ℕ → Tower.Tm n) : Propositional.Formula ℕ → Tower.Tm n
  | .atom a => atoms a
  | .falsum => botCode
  | .and φ ψ => andCode (encode atoms φ) (encode atoms ψ)
  | .or φ ψ => orCode (encode atoms φ) (encode atoms ψ)
  | .imp φ ψ => programCodes.impOf (encode atoms φ) (encode atoms ψ)

/-- Negation is Foundation's abbreviation `¬φ = φ ⊃ ⊥`. -/
theorem encode_neg (atoms : ℕ → Tower.Tm n) (φ : Propositional.Formula ℕ) :
    encode atoms (∼φ) = programCodes.impOf (encode atoms φ) botCode := rfl

/-- Truth is Foundation's abbreviation `⊤ = ⊥ ⊃ ⊥`. -/
theorem encode_top (atoms : ℕ → Tower.Tm n) :
    encode atoms ⊤ = programCodes.impOf botCode botCode := rfl

/-- Equivalence is Foundation's abbreviation `(φ ⊃ ψ) ∧ (ψ ⊃ φ)`. -/
theorem encode_iff (atoms : ℕ → Tower.Tm n) (φ ψ : Propositional.Formula ℕ) :
    encode atoms (φ ⭤ ψ) = andCode (programCodes.impOf (encode atoms φ) (encode atoms ψ))
      (programCodes.impOf (encode atoms ψ) (encode atoms φ)) := rfl

variable {m : Nat}

theorem rename_andCode (ρ : Ren n m) (p q : Tower.Tm n) :
    Presentation.rename ρ (andCode p q) =
      andCode (Presentation.rename ρ p) (Presentation.rename ρ q) := by
  change allPropOf (.lam (programCodes.impOf
    (programCodes.impOf (Presentation.rename (liftRen ρ) (Presentation.rename wk p))
      (programCodes.impOf (Presentation.rename (liftRen ρ) (Presentation.rename wk q)) (.var 0)))
    (.var 0))) = _
  rw [TypedEquality.rename_liftRen_wk, TypedEquality.rename_liftRen_wk]
  rfl

theorem rename_orCode (ρ : Ren n m) (p q : Tower.Tm n) :
    Presentation.rename ρ (orCode p q) =
      orCode (Presentation.rename ρ p) (Presentation.rename ρ q) := by
  change allPropOf (.lam (programCodes.impOf
    (programCodes.impOf (Presentation.rename (liftRen ρ) (Presentation.rename wk p)) (.var 0))
    (programCodes.impOf (programCodes.impOf
      (Presentation.rename (liftRen ρ) (Presentation.rename wk q)) (.var 0)) (.var 0)))) = _
  rw [TypedEquality.rename_liftRen_wk, TypedEquality.rename_liftRen_wk]
  rfl

/-- Renaming a code renames the atoms. -/
theorem encode_rename (ρ : Ren n m) (atoms : ℕ → Tower.Tm n) :
    ∀ φ : Propositional.Formula ℕ, Presentation.rename ρ (encode atoms φ) =
      encode (fun a => Presentation.rename ρ (atoms a)) φ
  | .atom _ => rfl
  | .falsum => rfl
  | .and φ ψ => by
    change Presentation.rename ρ (andCode (encode atoms φ) (encode atoms ψ)) = _
    rw [rename_andCode, encode_rename ρ atoms φ, encode_rename ρ atoms ψ]
    rfl
  | .or φ ψ => by
    change Presentation.rename ρ (orCode (encode atoms φ) (encode atoms ψ)) = _
    rw [rename_orCode, encode_rename ρ atoms φ, encode_rename ρ atoms ψ]
    rfl
  | .imp φ ψ => by
    change programCodes.impOf (Presentation.rename ρ (encode atoms φ))
      (Presentation.rename ρ (encode atoms ψ)) = _
    rw [encode_rename ρ atoms φ, encode_rename ρ atoms ψ]
    rfl

end Codes

/-! ## Typing the codes and their decoding -/

section Typing

variable {n : Nat} {Θ : Tower.Ctx n}

/-- The decoding of a code is a type of the lowest universe. -/
theorem holdsO {c : Tower.Tm n} (code : Typed objectRules Θ c (.const propN)) :
    Typed objectRules Θ (programCodes.holdsOf c) U0 :=
  .appElim holds_typedO code

/-- A family of codes indexed by codes. -/
theorem familyO {B : Tower.Tm (n + 1)}
    (body : Typed objectRules (.snoc Θ (.const propN)) B (.const propN)) :
    Typed objectRules Θ (.lam B) (.pi (.const propN) (.const propN)) :=
  .lamIntro (piO prop_typedO prop_typedO) (.sort _) body

/-- `all@prop (λc. B)` is a code when `B` is. -/
theorem allPropO {B : Tower.Tm (n + 1)}
    (body : Typed objectRules (.snoc Θ (.const propN)) B (.const propN)) :
    Typed objectRules Θ (allPropOf (.lam B)) (.const propN) :=
  .appElim allProp_typedO (familyO body)

/-- The conjunction of two codes is a code. -/
theorem andCode_typed {p q : Tower.Tm n} (hp : Typed objectRules Θ p (.const propN))
    (hq : Typed objectRules Θ q (.const propN)) :
    Typed objectRules Θ (andCode p q) (.const propN) :=
  allPropO (impO (impO hp.weaken (impO hq.weaken (.var 0))) (.var 0))

/-- The disjunction of two codes is a code. -/
theorem orCode_typed {p q : Tower.Tm n} (hp : Typed objectRules Θ p (.const propN))
    (hq : Typed objectRules Θ q (.const propN)) :
    Typed objectRules Θ (orCode p q) (.const propN) :=
  allPropO (impO (impO hp.weaken (.var 0)) (impO (impO hq.weaken (.var 0)) (.var 0)))

/-- **The codes of formulas are codes**: `encode atoms φ : prop` whenever every atom is a
code. -/
theorem encode_typed {atoms : ℕ → Tower.Tm n}
    (hatoms : ∀ a, Typed objectRules Θ (atoms a) (.const propN)) :
    ∀ φ : Propositional.Formula ℕ, Typed objectRules Θ (encode atoms φ) (.const propN)
  | .atom a => hatoms a
  | .falsum => botCode_typed
  | .and φ ψ => andCode_typed (encode_typed hatoms φ) (encode_typed hatoms ψ)
  | .or φ ψ => orCode_typed (encode_typed hatoms φ) (encode_typed hatoms ψ)
  | .imp φ ψ => impO (encode_typed hatoms φ) (encode_typed hatoms ψ)

/-- Decoding an implication: `holds (imp p q) ≡ Π (_ : holds p). holds q`. -/
theorem equal_holds_imp {p q : Tower.Tm n} (hp : Typed objectRules Θ p (.const propN))
    (hq : Typed objectRules Θ q (.const propN)) :
    Equal objectRules Θ (programCodes.holdsOf (programCodes.impOf p q))
      (.pi (programCodes.holdsOf p) (programCodes.holdsOf (Presentation.rename wk q))) U0 :=
  .root (programCodes.extend_decoder_step rules (DecoderStep.imp p q))
    (holdsO (impO hp hq)) (piO (holdsO hp) (holdsO hq.weaken))

/-- The carrier of `all@prop` is the type of codes. -/
theorem carrier_allProp :
    programCodes.decoders.allCarrier allPropN = some (typeTerm .prop) := by
  change (SetProfile.allInstance? allPropN).map typeTerm = _
  rw [SetProfile.allInstance?_allName]
  rfl

/-- Decoding the quantifier over codes: `holds (all@prop f) ≡ Π (c : prop). holds (f c)`. -/
theorem equal_holds_allProp {f : Tower.Tm n}
    (family : Typed objectRules Θ f (.pi (.const propN) (.const propN))) :
    Equal objectRules Θ (programCodes.holdsOf (allPropOf f))
      (.pi (.const propN) (programCodes.holdsOf (.app (Presentation.rename wk f) (.var 0)))) U0 :=
  .root (programCodes.extend_decoder_step rules (DecoderStep.all carrier_allProp f))
    (holdsO (.appElim allProp_typedO family))
    (piO prop_typedO (holdsO (.appElim family.weaken (.var 0))))

/-- Congruence of dependent function types in the lowest universe. -/
theorem equal_piO {A A' : Tower.Tm n} {B B' : Tower.Tm (n + 1)}
    (domain : Equal objectRules Θ A A' U0) (codomain : Equal objectRules (.snoc Θ A) B B' U0) :
    Equal objectRules Θ (.pi A B) (.pi A' B') U0 :=
  Derivable.cumulEq (.piCong domain (.sort _) codomain (.sort _) (.sorts _ _))
    (fun _ => Nat.le_of_eq (Nat.max_self _))

/-- Decoding the quantifier over an abstraction, with the β-step under the binder:
`holds (all@prop (λc. B)) ≡ Π (c : prop). holds B`. -/
theorem equal_holds_allProp_lam {B : Tower.Tm (n + 1)}
    (body : Typed objectRules (.snoc Θ (.const propN)) B (.const propN)) :
    Equal objectRules Θ (programCodes.holdsOf (allPropOf (.lam B)))
      (.pi (.const propN) (programCodes.holdsOf B)) U0 := by
  refine .trans (equal_holds_allProp (familyO body))
    (equal_piO (.refl prop_typedO) (.appCong (.refl holds_typedO) ?_))
  have lifted : Typed objectRules (.snoc (.snoc Θ (.const propN)) (.const propN))
      (Presentation.rename (liftRen wk) B) (.const propN) :=
    body.rename (CtxRen.snoc (fun _ => rfl) (.const propN))
  have beta := Derivable.betaPi (piO prop_typedO prop_typedO) (.sort _) lifted (.var 0)
  rw [inst0_var_rename_liftRen_wk] at beta
  exact beta

/-! ### Natural deduction for the codes -/

/-- Introduction of an implication code. -/
theorem impIntroO {p q : Tower.Tm n} {body : Tower.Tm (n + 1)}
    (hp : Typed objectRules Θ p (.const propN)) (hq : Typed objectRules Θ q (.const propN))
    (hbody : Typed objectRules (.snoc Θ (programCodes.holdsOf p)) body
      (programCodes.holdsOf (Presentation.rename wk q))) :
    Typed objectRules Θ (.lam body) (programCodes.holdsOf (programCodes.impOf p q)) :=
  .conv (.lamIntro (piO (holdsO hp) (holdsO hq.weaken)) (.sort _) hbody)
    (.symm (equal_holds_imp hp hq)) (.sort _)

/-- Elimination of an implication code: modus ponens is application. -/
theorem impElimO {p q f a : Tower.Tm n}
    (hp : Typed objectRules Θ p (.const propN)) (hq : Typed objectRules Θ q (.const propN))
    (hf : Typed objectRules Θ f (programCodes.holdsOf (programCodes.impOf p q)))
    (ha : Typed objectRules Θ a (programCodes.holdsOf p)) :
    Typed objectRules Θ (.app f a) (programCodes.holdsOf q) := by
  have applied : Typed objectRules Θ (.app f a)
      (programCodes.holdsOf (inst0 a (Presentation.rename wk q))) :=
    .appElim (.conv hf (equal_holds_imp hp hq) (.sort _)) ha
  rw [inst0_rename_wk] at applied
  exact applied

/-- Introduction of a quantification over codes. -/
theorem allIntroO {B body : Tower.Tm (n + 1)}
    (hB : Typed objectRules (.snoc Θ (.const propN)) B (.const propN))
    (hbody : Typed objectRules (.snoc Θ (.const propN)) body (programCodes.holdsOf B)) :
    Typed objectRules Θ (.lam body) (programCodes.holdsOf (allPropOf (.lam B))) :=
  .conv (.lamIntro (piO prop_typedO (holdsO hB)) (.sort _) hbody)
    (.symm (equal_holds_allProp_lam hB)) (.sort _)

/-- Elimination of a quantification over codes, at a code. -/
theorem allElimO {B : Tower.Tm (n + 1)} {f c : Tower.Tm n}
    (hB : Typed objectRules (.snoc Θ (.const propN)) B (.const propN))
    (hf : Typed objectRules Θ f (programCodes.holdsOf (allPropOf (.lam B))))
    (hc : Typed objectRules Θ c (.const propN)) :
    Typed objectRules Θ (.app f c) (programCodes.holdsOf (inst0 c B)) :=
  .appElim (.conv hf (equal_holds_allProp_lam hB) (.sort _)) hc

/-- Falsity eliminates into every code: `z r : holds r` for `z : holds (∀c. c)`. -/
theorem botElimO {z r : Tower.Tm n} (hz : Typed objectRules Θ z (programCodes.holdsOf botCode))
    (hr : Typed objectRules Θ r (.const propN)) :
    Typed objectRules Θ (.app z r) (programCodes.holdsOf r) :=
  allElimO (B := .var 0) (.var 0) hz hr

/-- Elimination of a conjunction code: `z r k : holds r` for `k : holds (p ⇒ q ⇒ r)`. -/
theorem andElimO {p q r z k : Tower.Tm n}
    (hp : Typed objectRules Θ p (.const propN)) (hq : Typed objectRules Θ q (.const propN))
    (hr : Typed objectRules Θ r (.const propN))
    (hz : Typed objectRules Θ z (programCodes.holdsOf (andCode p q)))
    (hk : Typed objectRules Θ k
      (programCodes.holdsOf (programCodes.impOf p (programCodes.impOf q r)))) :
    Typed objectRules Θ (.app (.app z r) k) (programCodes.holdsOf r) := by
  have instantiated : Typed objectRules Θ (.app z r) (programCodes.holdsOf (programCodes.impOf
      (programCodes.impOf (inst0 r (Presentation.rename wk p))
        (programCodes.impOf (inst0 r (Presentation.rename wk q)) r)) r)) :=
    allElimO (impO (impO hp.weaken (impO hq.weaken (.var 0))) (.var 0)) hz hr
  rw [inst0_rename_wk, inst0_rename_wk] at instantiated
  exact impElimO (impO hp (impO hq hr)) hr instantiated hk

/-- Introduction of a conjunction code: `λc. λk. k a b`. -/
theorem pairO {p q a b : Tower.Tm n}
    (hp : Typed objectRules Θ p (.const propN)) (hq : Typed objectRules Θ q (.const propN))
    (ha : Typed objectRules Θ a (programCodes.holdsOf p))
    (hb : Typed objectRules Θ b (programCodes.holdsOf q)) :
    Typed objectRules Θ (.lam (.lam (.app (.app (.var 0)
        (Presentation.rename wk (Presentation.rename wk a)))
        (Presentation.rename wk (Presentation.rename wk b)))))
      (programCodes.holdsOf (andCode p q)) := by
  refine allIntroO (impO (impO hp.weaken (impO hq.weaken (.var 0))) (.var 0)) ?_
  refine impIntroO (impO hp.weaken (impO hq.weaken (.var 0))) (.var 0) ?_
  exact impElimO hq.weaken.weaken (.var 1)
    (impElimO hp.weaken.weaken (impO hq.weaken.weaken (.var 1)) (.var 0) ha.weaken.weaken)
    hb.weaken.weaken

/-- Left introduction of a disjunction code: `λc. λl. λr. l a`. -/
theorem inlO {p q a : Tower.Tm n}
    (hp : Typed objectRules Θ p (.const propN)) (hq : Typed objectRules Θ q (.const propN))
    (ha : Typed objectRules Θ a (programCodes.holdsOf p)) :
    Typed objectRules Θ (.lam (.lam (.lam (.app (.var 1)
        (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk a)))))))
      (programCodes.holdsOf (orCode p q)) := by
  refine allIntroO (impO (impO hp.weaken (.var 0)) (impO (impO hq.weaken (.var 0)) (.var 0))) ?_
  refine impIntroO (impO hp.weaken (.var 0)) (impO (impO hq.weaken (.var 0)) (.var 0)) ?_
  refine impIntroO (impO hq.weaken.weaken (.var 1)) (.var 1) ?_
  exact impElimO hp.weaken.weaken.weaken (.var 2) (.var 1) ha.weaken.weaken.weaken

/-- Right introduction of a disjunction code: `λc. λl. λr. r b`. -/
theorem inrO {p q b : Tower.Tm n}
    (hp : Typed objectRules Θ p (.const propN)) (hq : Typed objectRules Θ q (.const propN))
    (hb : Typed objectRules Θ b (programCodes.holdsOf q)) :
    Typed objectRules Θ (.lam (.lam (.lam (.app (.var 0)
        (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk b)))))))
      (programCodes.holdsOf (orCode p q)) := by
  refine allIntroO (impO (impO hp.weaken (.var 0)) (impO (impO hq.weaken (.var 0)) (.var 0))) ?_
  refine impIntroO (impO hp.weaken (.var 0)) (impO (impO hq.weaken (.var 0)) (.var 0)) ?_
  refine impIntroO (impO hq.weaken.weaken (.var 1)) (.var 1) ?_
  exact impElimO hq.weaken.weaken.weaken (.var 2) (.var 0) hb.weaken.weaken.weaken

/-- Elimination of a disjunction code: `z r f g : holds r`. -/
theorem caseO {p q r z f g : Tower.Tm n}
    (hp : Typed objectRules Θ p (.const propN)) (hq : Typed objectRules Θ q (.const propN))
    (hr : Typed objectRules Θ r (.const propN))
    (hz : Typed objectRules Θ z (programCodes.holdsOf (orCode p q)))
    (hf : Typed objectRules Θ f (programCodes.holdsOf (programCodes.impOf p r)))
    (hg : Typed objectRules Θ g (programCodes.holdsOf (programCodes.impOf q r))) :
    Typed objectRules Θ (.app (.app (.app z r) f) g) (programCodes.holdsOf r) := by
  have instantiated : Typed objectRules Θ (.app z r) (programCodes.holdsOf (programCodes.impOf
      (programCodes.impOf (inst0 r (Presentation.rename wk p)) r)
      (programCodes.impOf (programCodes.impOf (inst0 r (Presentation.rename wk q)) r) r))) :=
    allElimO (impO (impO hp.weaken (.var 0)) (impO (impO hq.weaken (.var 0)) (.var 0))) hz hr
  rw [inst0_rename_wk, inst0_rename_wk] at instantiated
  exact impElimO (impO hq hr) hr
    (impElimO (impO hp hr) (impO (impO hq hr) hr) instantiated hf) hg

end Typing

/-! ## Proof terms of the axioms -/

section ProofTerms

variable {n : Nat}

/-- Ex falso, `λz. z r`. -/
def efqProof (r : Tower.Tm n) : Tower.Tm n := .lam (.app (.var 0) (Presentation.rename wk r))

/-- `K = λx. λy. x`. -/
def kProof : Tower.Tm n := .lam (.lam (.var 1))

/-- `S = λf. λg. λx. f x (g x)`. -/
def sProof : Tower.Tm n :=
  .lam (.lam (.lam (.app (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0)))))

/-- The first projection, `λz. z p K`. -/
def fstProof (p : Tower.Tm n) : Tower.Tm n :=
  .lam (.app (.app (.var 0) (Presentation.rename wk p)) kProof)

/-- The second projection, `λz. z q (λx. λy. y)`. -/
def sndProof (q : Tower.Tm n) : Tower.Tm n :=
  .lam (.app (.app (.var 0) (Presentation.rename wk q)) (.lam (.lam (.var 0))))

/-- Pairing, `λx. λy. λc. λk. k x y`. -/
def pairProof : Tower.Tm n := .lam (.lam (.lam (.lam (.app (.app (.var 0) (.var 3)) (.var 2)))))

/-- The left injection, `λx. λc. λl. λr. l x`. -/
def inlProof : Tower.Tm n := .lam (.lam (.lam (.lam (.app (.var 1) (.var 3)))))

/-- The right injection, `λy. λc. λl. λr. r y`. -/
def inrProof : Tower.Tm n := .lam (.lam (.lam (.lam (.app (.var 0) (.var 3)))))

/-- Case analysis, `λf. λg. λz. z r f g`. -/
def caseProof (r : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (.lam (.app (.app (.app (.var 0)
    (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk r)))) (.var 2))
    (.var 1))))

end ProofTerms

section ProofTyping

variable {n : Nat} {Θ : Tower.Ctx n} {p q r : Tower.Tm n}

theorem efqProof_typed (hr : Typed objectRules Θ r (.const propN)) :
    Typed objectRules Θ (efqProof r) (programCodes.holdsOf (programCodes.impOf botCode r)) :=
  impIntroO botCode_typed hr (botElimO (.var 0) hr.weaken)

theorem kProof_typed (hp : Typed objectRules Θ p (.const propN))
    (hq : Typed objectRules Θ q (.const propN)) :
    Typed objectRules Θ kProof
      (programCodes.holdsOf (programCodes.impOf p (programCodes.impOf q p))) :=
  impIntroO hp (impO hq hp) (impIntroO hq.weaken hp.weaken (.var 1))

theorem sProof_typed (hp : Typed objectRules Θ p (.const propN))
    (hq : Typed objectRules Θ q (.const propN)) (hr : Typed objectRules Θ r (.const propN)) :
    Typed objectRules Θ sProof (programCodes.holdsOf (programCodes.impOf
      (programCodes.impOf p (programCodes.impOf q r))
      (programCodes.impOf (programCodes.impOf p q) (programCodes.impOf p r)))) := by
  refine impIntroO (impO hp (impO hq hr)) (impO (impO hp hq) (impO hp hr)) ?_
  refine impIntroO (impO hp.weaken hq.weaken) (impO hp.weaken hr.weaken) ?_
  refine impIntroO hp.weaken.weaken hr.weaken.weaken ?_
  exact impElimO hq.weaken.weaken.weaken hr.weaken.weaken.weaken
    (impElimO hp.weaken.weaken.weaken (impO hq.weaken.weaken.weaken hr.weaken.weaken.weaken)
      (.var 2) (.var 0))
    (impElimO hp.weaken.weaken.weaken hq.weaken.weaken.weaken (.var 1) (.var 0))

theorem fstProof_typed (hp : Typed objectRules Θ p (.const propN))
    (hq : Typed objectRules Θ q (.const propN)) :
    Typed objectRules Θ (fstProof p)
      (programCodes.holdsOf (programCodes.impOf (andCode p q) p)) := by
  refine impIntroO (andCode_typed hp hq) hp ?_
  refine andElimO hp.weaken hq.weaken hp.weaken ?_ (kProof_typed hp.weaken hq.weaken)
  rw [← rename_andCode]
  exact .var 0

theorem sndProof_typed (hp : Typed objectRules Θ p (.const propN))
    (hq : Typed objectRules Θ q (.const propN)) :
    Typed objectRules Θ (sndProof q)
      (programCodes.holdsOf (programCodes.impOf (andCode p q) q)) := by
  refine impIntroO (andCode_typed hp hq) hq ?_
  refine andElimO hp.weaken hq.weaken hq.weaken ?_
    (impIntroO hp.weaken (impO hq.weaken hq.weaken)
      (impIntroO hq.weaken.weaken hq.weaken.weaken (.var 0)))
  rw [← rename_andCode]
  exact .var 0

theorem pairProof_typed (hp : Typed objectRules Θ p (.const propN))
    (hq : Typed objectRules Θ q (.const propN)) :
    Typed objectRules Θ pairProof
      (programCodes.holdsOf (programCodes.impOf p (programCodes.impOf q (andCode p q)))) := by
  refine impIntroO hp (impO hq (andCode_typed hp hq))
    (impIntroO hq.weaken (andCode_typed hp hq).weaken ?_)
  rw [rename_andCode, rename_andCode]
  refine pairO (a := .var 1) (b := .var 0) hp.weaken.weaken hq.weaken.weaken ?_ ?_
  · exact .var 1
  · exact .var 0

theorem inlProof_typed (hp : Typed objectRules Θ p (.const propN))
    (hq : Typed objectRules Θ q (.const propN)) :
    Typed objectRules Θ inlProof (programCodes.holdsOf (programCodes.impOf p (orCode p q))) := by
  refine impIntroO hp (orCode_typed hp hq) ?_
  rw [rename_orCode]
  refine inlO (a := .var 0) hp.weaken hq.weaken ?_
  exact .var 0

theorem inrProof_typed (hp : Typed objectRules Θ p (.const propN))
    (hq : Typed objectRules Θ q (.const propN)) :
    Typed objectRules Θ inrProof (programCodes.holdsOf (programCodes.impOf q (orCode p q))) := by
  refine impIntroO hq (orCode_typed hp hq) ?_
  rw [rename_orCode]
  refine inrO (b := .var 0) hp.weaken hq.weaken ?_
  exact .var 0

theorem caseProof_typed (hp : Typed objectRules Θ p (.const propN))
    (hq : Typed objectRules Θ q (.const propN)) (hr : Typed objectRules Θ r (.const propN)) :
    Typed objectRules Θ (caseProof r) (programCodes.holdsOf (programCodes.impOf
      (programCodes.impOf p r)
      (programCodes.impOf (programCodes.impOf q r) (programCodes.impOf (orCode p q) r)))) := by
  have hor := orCode_typed hp hq
  refine impIntroO (impO hp hr) (impO (impO hq hr) (impO hor hr)) ?_
  refine impIntroO (impO hq.weaken hr.weaken) (impO hor.weaken hr.weaken) ?_
  refine impIntroO hor.weaken.weaken hr.weaken.weaken ?_
  refine caseO hp.weaken.weaken.weaken hq.weaken.weaken.weaken hr.weaken.weaken.weaken ?_
    (.var 2) (.var 1)
  rw [← rename_orCode, ← rename_orCode, ← rename_orCode]
  exact .var 0

end ProofTyping

/-! ## The translation of derivations -/

section Translation

/-- **The proof translation.** An intuitionistic derivation of `φ` from the assumptions `Δ`
becomes a proof term, given the codes of the atoms and a proof term for each assumption.
Each axiom becomes its combinator and modus ponens becomes application. -/
def IntDeriv.toPrime {m : Nat} (atoms : ℕ → Tower.Tm m) {Δ : List (Propositional.Formula ℕ)}
    (hyps : (δ : Propositional.Formula ℕ) → δ ∈ Δ → Tower.Tm m) :
    {φ : Propositional.Formula ℕ} → IntDeriv Δ φ → Tower.Tm m
  | _, .hyp h => hyps _ h
  | _, .efq φ => efqProof (encode atoms φ)
  | _, .lem _ h => nomatch h
  | _, .implyK _ _ => kProof
  | _, .implyS _ _ _ => sProof
  | _, .andElimL φ _ => fstProof (encode atoms φ)
  | _, .andElimR _ ψ => sndProof (encode atoms ψ)
  | _, .andIntro _ _ => pairProof
  | _, .orIntroL _ _ => inlProof
  | _, .orIntroR _ _ => inrProof
  | _, .orElim _ _ χ => caseProof (encode atoms χ)
  | _, .mdp d₁ d₂ => .app (IntDeriv.toPrime atoms hyps d₁) (IntDeriv.toPrime atoms hyps d₂)

/-- **Typing of the proof translation.** If the atoms are codes and each assumption `δ` has a
proof term of type `holds (encode δ)`, the translation of a derivation of `φ` has type
`holds (encode φ)`. -/
theorem IntDeriv.toPrime_typed {m : Nat} {Θ : Tower.Ctx m} {atoms : ℕ → Tower.Tm m}
    (hatoms : ∀ a, Typed objectRules Θ (atoms a) (.const propN))
    {Δ : List (Propositional.Formula ℕ)}
    {hyps : (δ : Propositional.Formula ℕ) → δ ∈ Δ → Tower.Tm m}
    (hhyps : ∀ δ (h : δ ∈ Δ),
      Typed objectRules Θ (hyps δ h) (programCodes.holdsOf (encode atoms δ))) :
    ∀ {φ : Propositional.Formula ℕ} (d : IntDeriv Δ φ),
      Typed objectRules Θ (IntDeriv.toPrime atoms hyps d) (programCodes.holdsOf (encode atoms φ))
  | _, .hyp h => hhyps _ h
  | _, .efq φ => efqProof_typed (encode_typed hatoms φ)
  | _, .lem _ h => nomatch h
  | _, .implyK φ ψ => kProof_typed (encode_typed hatoms φ) (encode_typed hatoms ψ)
  | _, .implyS φ ψ χ =>
    sProof_typed (encode_typed hatoms φ) (encode_typed hatoms ψ) (encode_typed hatoms χ)
  | _, .andElimL φ ψ => fstProof_typed (encode_typed hatoms φ) (encode_typed hatoms ψ)
  | _, .andElimR φ ψ => sndProof_typed (encode_typed hatoms φ) (encode_typed hatoms ψ)
  | _, .andIntro φ ψ => pairProof_typed (encode_typed hatoms φ) (encode_typed hatoms ψ)
  | _, .orIntroL φ ψ => inlProof_typed (encode_typed hatoms φ) (encode_typed hatoms ψ)
  | _, .orIntroR φ ψ => inrProof_typed (encode_typed hatoms φ) (encode_typed hatoms ψ)
  | _, .orElim φ ψ χ =>
    caseProof_typed (encode_typed hatoms φ) (encode_typed hatoms ψ) (encode_typed hatoms χ)
  | _, .mdp (φ := φ) (ψ := ψ) d₁ d₂ =>
    impElimO (encode_typed hatoms φ) (encode_typed hatoms ψ)
      (IntDeriv.toPrime_typed hatoms hhyps d₁) (IntDeriv.toPrime_typed hatoms hhyps d₂)

/-- The atom codes seen past the assumptions `Δ`. -/
def atomsPast {n : Nat} (atoms : ℕ → Tower.Tm n) :
    (Δ : List (Propositional.Formula ℕ)) → ℕ → Tower.Tm (n + Δ.length)
  | [] => atoms
  | _ :: Δ => fun a => Presentation.rename wk (atomsPast atoms Δ a)

/-- The context of the assumptions `Δ` after the context `Γ` of the atoms: one proof variable
of type `holds (encode δ)` for each `δ` in `Δ`, the head of `Δ` innermost. -/
def hypCtx {n : Nat} (Γ : Tower.Ctx n) (atoms : ℕ → Tower.Tm n) :
    (Δ : List (Propositional.Formula ℕ)) → Tower.Ctx (n + Δ.length)
  | [] => Γ
  | δ :: Δ => .snoc (hypCtx Γ atoms Δ) (programCodes.holdsOf (encode (atomsPast atoms Δ) δ))

/-- The proof variable of an assumption: the variable of its first occurrence. -/
def hypVar {n : Nat} : (Δ : List (Propositional.Formula ℕ)) → (δ : Propositional.Formula ℕ) →
    δ ∈ Δ → Tower.Tm (n + Δ.length)
  | [], _, h => absurd h List.not_mem_nil
  | δ' :: Δ, δ, h =>
    if e : δ = δ' then (.var 0 : Tower.Tm (n + Δ.length + 1))
    else (Presentation.rename wk (hypVar Δ δ ((List.mem_cons.mp h).resolve_left e)) :
      Tower.Tm (n + Δ.length + 1))

section Context

variable {n : Nat} {Γ : Tower.Ctx n} {atoms : ℕ → Tower.Tm n}

/-- The atoms past the assumptions are codes. -/
theorem atomsPast_typed (hatoms : ∀ a, Typed objectRules Γ (atoms a) (.const propN)) :
    ∀ (Δ : List (Propositional.Formula ℕ)) (a : ℕ),
      Typed objectRules (hypCtx Γ atoms Δ) (atomsPast atoms Δ a) (.const propN)
  | [], a => hatoms a
  | _ :: Δ, a => (atomsPast_typed hatoms Δ a).weaken

/-- Each assumption is a proof variable of the decoding of its code. -/
theorem hypVar_typed :
    ∀ (Δ : List (Propositional.Formula ℕ)) (δ : Propositional.Formula ℕ) (h : δ ∈ Δ),
      Typed objectRules (hypCtx Γ atoms Δ) (hypVar Δ δ h)
        (programCodes.holdsOf (encode (atomsPast atoms Δ) δ))
  | [], _, h => absurd h List.not_mem_nil
  | δ' :: Δ, δ, h => by
    unfold hypVar
    split
    · next e =>
      rw [e]
      have v : Typed objectRules
          (.snoc (hypCtx Γ atoms Δ) (programCodes.holdsOf (encode (atomsPast atoms Δ) δ')))
          (.var 0) (programCodes.holdsOf
            (Presentation.rename wk (encode (atomsPast atoms Δ) δ'))) := .var 0
      rw [encode_rename] at v
      exact v
    · next e =>
      have w : Typed objectRules
          (.snoc (hypCtx Γ atoms Δ) (programCodes.holdsOf (encode (atomsPast atoms Δ) δ')))
          (Presentation.rename wk (hypVar Δ δ ((List.mem_cons.mp h).resolve_left e)))
          (programCodes.holdsOf (Presentation.rename wk (encode (atomsPast atoms Δ) δ))) :=
        (hypVar_typed Δ δ _).weaken
      rw [encode_rename] at w
      exact w

end Context

/-- **The importer.** An intuitionistic derivation of `φ` from the assumptions `Δ` becomes a
proof term in the context `hypCtx Γ atoms Δ`, in which the assumptions are proof variables. -/
def IntDeriv.primeProof {n : Nat} (atoms : ℕ → Tower.Tm n) {Δ : List (Propositional.Formula ℕ)}
    {φ : Propositional.Formula ℕ} (d : IntDeriv Δ φ) : Tower.Tm (n + Δ.length) :=
  IntDeriv.toPrime (atomsPast atoms Δ) (hypVar Δ) d

/-- **Typing of the importer.** If every atom is a code in `Γ`, the imported proof of a
derivation of `φ` from `Δ` has type `holds (encode φ)` in the context of the assumptions after
`Γ`; for `Δ = []` the context is `Γ` and the type is `holds (encode atoms φ)`. -/
theorem IntDeriv.primeProof_typed {n : Nat} {Γ : Tower.Ctx n} {atoms : ℕ → Tower.Tm n}
    (hatoms : ∀ a, Typed objectRules Γ (atoms a) (.const propN))
    {Δ : List (Propositional.Formula ℕ)} {φ : Propositional.Formula ℕ} (d : IntDeriv Δ φ) :
    Typed objectRules (hypCtx Γ atoms Δ) (IntDeriv.primeProof atoms d)
      (programCodes.holdsOf (encode (atomsPast atoms Δ) φ)) :=
  IntDeriv.toPrime_typed (atomsPast_typed hatoms Δ) (hypVar_typed Δ) d

/-- **Typing of the importer without assumptions**: a derivation of `φ` imports to a proof
of `holds (encode atoms φ)` in the context of the atoms. -/
theorem IntDeriv.primeProof_typed_nil {n : Nat} {Γ : Tower.Ctx n} {atoms : ℕ → Tower.Tm n}
    (hatoms : ∀ a, Typed objectRules Γ (atoms a) (.const propN))
    {φ : Propositional.Formula ℕ} (d : IntDeriv [] φ) :
    Typed objectRules Γ (IntDeriv.primeProof atoms d) (programCodes.holdsOf (encode atoms φ)) :=
  IntDeriv.primeProof_typed hatoms d

end Translation

/-! ## Classical and modal derivations -/

section Imports

variable {n : Nat} {Γ : Tower.Ctx n} {atoms : ℕ → Tower.Tm n}

/-- **Barr's route.** A classical derivation of a geometric implication `G` from geometric
implications `𝔄` is made intuitionistic by Gödel's Theorem 62 and imported, the assumptions
`𝔄` becoming proof variables. -/
def importGeometric (atoms : ℕ → Tower.Tm n) (𝔄 : List (GeoImp ℕ)) (G : GeoImp ℕ)
    (d : ClDeriv (𝔄.map (GeoImp.toFormula .atom)) (G.toFormula .atom)) :
    Tower.Tm (n + (𝔄.map (GeoImp.toFormula Propositional.Formula.atom)).length) :=
  IntDeriv.primeProof atoms (theorem62OfClassical 𝔄 G d)

/-- **Typing of Barr's route.** The import of a classical derivation of a geometric
implication proves its code, with the assumptions as proof variables. -/
theorem importGeometric_typed (hatoms : ∀ a, Typed objectRules Γ (atoms a) (.const propN))
    {𝔄 : List (GeoImp ℕ)} {G : GeoImp ℕ}
    (d : ClDeriv (𝔄.map (GeoImp.toFormula .atom)) (G.toFormula .atom)) :
    Typed objectRules (hypCtx Γ atoms (𝔄.map (GeoImp.toFormula .atom)))
      (importGeometric atoms 𝔄 G d)
      (programCodes.holdsOf
        (encode (atomsPast atoms (𝔄.map (GeoImp.toFormula .atom))) (G.toFormula .atom))) :=
  IntDeriv.primeProof_typed hatoms _

/-- **Gödel's route.** An S4 derivation of the Gödel translation `U(A)` from `U(Δ)` is turned
into an intuitionistic derivation of `A` from `Δ` by Gödel's Theorem 64 and imported. -/
def importS4 (atoms : ℕ → Tower.Tm n) {Δ : List (Propositional.Formula ℕ)}
    {φ : Propositional.Formula ℕ} (d : S4Deriv (Δ.map gödelTranslate) (φᵍ)) :
    Tower.Tm (n + Δ.length) :=
  IntDeriv.primeProof atoms (s4GödelToIntDeriv d)

/-- **Typing of Gödel's route.** The import of an S4 derivation of `U(A)` from `U(Δ)` proves
the code of `A`, with `Δ` as proof variables. -/
theorem importS4_typed (hatoms : ∀ a, Typed objectRules Γ (atoms a) (.const propN))
    {Δ : List (Propositional.Formula ℕ)} {φ : Propositional.Formula ℕ}
    (d : S4Deriv (Δ.map gödelTranslate) (φᵍ)) :
    Typed objectRules (hypCtx Γ atoms Δ) (importS4 atoms d)
      (programCodes.holdsOf (encode (atomsPast atoms Δ) φ)) :=
  IntDeriv.primeProof_typed hatoms _

/-- The context of the assumptions is formed when the context of the atoms is. -/
theorem hypCtx_formed (formed : CtxFormed objectRules Γ)
    (hatoms : ∀ a, Typed objectRules Γ (atoms a) (.const propN)) :
    ∀ Δ : List (Propositional.Formula ℕ), CtxFormed objectRules (hypCtx Γ atoms Δ)
  | [] => formed
  | δ :: Δ =>
    .snoc (hypCtx_formed formed hatoms Δ)
      ⟨_, .sort _, holdsO (encode_typed (atomsPast_typed hatoms Δ) δ)⟩

/-- **Imported proofs normalize.** In a formed context of atoms, the import of every
intuitionistic derivation is strongly normalizing, by the strong normalization of the
package. -/
theorem IntDeriv.primeProof_sn (formed : CtxFormed objectRules Γ)
    (hatoms : ∀ a, Typed objectRules Γ (atoms a) (.const propN))
    {Δ : List (Propositional.Formula ℕ)} {φ : Propositional.Formula ℕ} (d : IntDeriv Δ φ) :
    StrongNormalization.SN objectRules (IntDeriv.primeProof atoms d) :=
  (objectRules_sn (hypCtx_formed formed hatoms Δ) (IntDeriv.primeProof_typed hatoms d)).1

end Imports

/-! ## Controls -/

section Controls

/-! ### Positive: the geometric example -/

/-- The assumptions `p₀ ⊃ p₁ ∨ p₂`, `p₁ ⊃ p₃`, `p₂ ⊃ p₃` of the geometric example, as codes. -/
theorem exampleAxioms_encode {n : Nat} (atoms : ℕ → Tower.Tm n) :
    (exampleAxioms.map (GeoImp.toFormula .atom)).map (encode atoms) =
      [programCodes.impOf (atoms 0) (orCode (atoms 1) (atoms 2)),
        programCodes.impOf (atoms 1) (atoms 3), programCodes.impOf (atoms 2) (atoms 3)] :=
  rfl

/-- The goal `p₀ ⊃ p₃` of the geometric example, as a code. -/
theorem exampleGoal_encode {n : Nat} (atoms : ℕ → Tower.Tm n) :
    encode atoms (exampleGoal.toFormula .atom) = programCodes.impOf (atoms 0) (atoms 3) := rfl

/-- **Positive control: Barr's route.** The geometric consequence `p₀ ⊃ p₃` of
`p₀ ⊃ p₁ ∨ p₂`, `p₁ ⊃ p₃` and `p₂ ⊃ p₃`, imported from its classical derivation, proves
`holds (imp p₀ p₃)` with the three assumptions as proof variables. -/
theorem example_importGeometric_typed {n : Nat} {Γ : Tower.Ctx n} {atoms : ℕ → Tower.Tm n}
    (hatoms : ∀ a, Typed objectRules Γ (atoms a) (.const propN)) :
    Typed objectRules (hypCtx Γ atoms (exampleAxioms.map (GeoImp.toFormula .atom)))
      (importGeometric atoms exampleAxioms exampleGoal (PropDeriv.toCl exampleDerivation))
      (programCodes.holdsOf (programCodes.impOf
        (atomsPast atoms (exampleAxioms.map (GeoImp.toFormula .atom)) 0)
        (atomsPast atoms (exampleAxioms.map (GeoImp.toFormula .atom)) 3))) :=
  importGeometric_typed hatoms _

/-! ### Positive: closed proofs, the atom bound by `all@prop` -/

/-- The derivation `S K K` of `p ⊃ p` imports to the term `S K K`. -/
theorem selfImp_primeProof :
    IntDeriv.primeProof (fun _ => (.var 0 : Tower.Tm 1))
        (PropDeriv.selfImp (cl := false) (Γ := []) (#0)) =
      .app (.app sProof kProof) kProof :=
  rfl

/-- **Positive control: a closed proof.** With its atom bound by `all@prop`, the import of
`p ⊃ p` is the closed term `λc. S K K`, a proof of `all@prop (λc. imp c c)`. -/
theorem selfImp_closed :
    Typed objectRules .nil (.lam (.app (.app sProof kProof) kProof))
      (programCodes.holdsOf (allPropOf (.lam (programCodes.impOf (.var 0) (.var 0))))) :=
  allIntroO (impO (.var 0) (.var 0))
    (IntDeriv.primeProof_typed_nil (Γ := .snoc .nil (.const propN)) (fun _ => .var 0)
      (PropDeriv.selfImp (#0)))

/-- A classical derivation of `p₀ ⊃ p₀`, the geometric implication with antecedent and
consequent `p₀`, by cases on the excluded middle `p₀ ∨ ¬p₀`. -/
def lemSelfImp : ClDeriv [] (GeoImp.toFormula .atom (⟨[0], [0]⟩ : GeoImp ℕ)) :=
  .mdp (.mdp (.mdp (.orElim (#0) (∼#0) (#0 ➝ #0)) (.implyK (#0) (#0)))
    (.mdp (.implyK (#0 ➝ #0) (∼#0)) (PropDeriv.selfImp (#0)))) (.lem (#0) rfl)

/-- **Positive control: a classical proof.** The derivation of `p₀ ⊃ p₀` by excluded middle,
made intuitionistic by Theorem 62 and imported with its atom bound by `all@prop`, is a closed
proof of `all@prop (λc. imp c c)`. -/
theorem lemSelfImp_closed :
    Typed objectRules .nil
      (.lam (importGeometric (fun _ => (.var 0 : Tower.Tm 1)) [] ⟨[0], [0]⟩ lemSelfImp))
      (programCodes.holdsOf (allPropOf (.lam (programCodes.impOf (.var 0) (.var 0))))) :=
  allIntroO (impO (.var 0) (.var 0))
    (importGeometric_typed (Γ := .snoc .nil (.const propN)) (fun _ => .var 0)
      (𝔄 := []) (G := ⟨[0], [0]⟩) lemSelfImp)

/-! ### Negative: excluded middle -/

/-- Excluded middle is a disjunction, not a geometric implication. -/
theorem geometric_ne_lem₀ (G : GeoImp ℕ) : G.toFormula .atom ≠ lem₀ := fun h => nomatch h

/-- **Negative control.** Excluded middle `p₀ ∨ ¬p₀` has a classical derivation, but neither
route imports it:

* it has no intuitionistic derivation, so `IntDeriv.primeProof` has no input for it;
* it is not a geometric implication, nor intuitionistically equivalent to one, so Barr's
  route does not reach it, even up to equivalence;
* its Gödel translation has no S4 derivation, so Gödel's route has no input for it. -/
theorem lem₀_not_imported :
    Nonempty (ClDeriv [] lem₀) ∧ ¬ Nonempty (IntDeriv [] lem₀) ∧
      (∀ G : GeoImp ℕ, G.toFormula .atom ≠ lem₀ ∧
        ¬ (Nonempty (IntDeriv [] (G.toFormula .atom ➝ lem₀)) ∧
          Nonempty (IntDeriv [] (lem₀ ➝ G.toFormula .atom)))) ∧
      ¬ Nonempty (S4Deriv [] (lem₀ᵍ)) :=
  ⟨⟨lem₀ClDeriv⟩, not_nonempty_intDeriv_lem₀,
    fun G => ⟨geometric_ne_lem₀ G, lem₀_not_equiv_geometric G⟩,
    fun ⟨d⟩ => not_nonempty_intDeriv_lem₀ ⟨s4GödelToIntDeriv (Γ := []) d⟩⟩

/-! ### Consistency -/

/-- **No import proves the bottom code.** Under closed atom codes, the code of a formula
with a closed intuitionistic derivation is never `∀c. c`: the import of the derivation would
be a closed proof of it, which `consistent_bot` excludes. -/
theorem IntDeriv.encode_ne_botCode {atoms : ℕ → Tower.Tm 0}
    (hatoms : ∀ a, Typed objectRules .nil (atoms a) (.const propN))
    {φ : Propositional.Formula ℕ} (d : IntDeriv [] φ) : encode atoms φ ≠ botCode := by
  intro e
  have h := IntDeriv.primeProof_typed_nil hatoms d
  rw [e] at h
  exact consistent_bot _ h

/-- **Consistency through the importers.** By `consistent_bot`, no route yields a closed
proof of `∀c. c`, so there is no intuitionistic derivation of `⊥`, no classical derivation of
the geometric implication `⊤ ⊃ ⊥` (whose import, applied to `λx. x`, would prove `∀c. c`),
and no S4 derivation of `⊥`, the Gödel translation of `⊥`. -/
theorem imports_consistent :
    ¬ Nonempty (IntDeriv [] ⊥) ∧
      ¬ Nonempty (ClDeriv [] (GeoImp.toFormula .atom (⟨[], []⟩ : GeoImp ℕ))) ∧
      ¬ Nonempty (S4Deriv [] ⊥) :=
  ⟨fun ⟨d⟩ => IntDeriv.encode_ne_botCode (fun _ => botCode_typed) d rfl,
    fun ⟨d⟩ => consistent_bot _
      (impElimO (impO botCode_typed botCode_typed) botCode_typed
        (importGeometric_typed (Γ := .nil) (atoms := fun _ => botCode)
          (fun _ => botCode_typed) (𝔄 := []) (G := ⟨[], []⟩) d)
        (impIntroO botCode_typed botCode_typed (.var 0))),
    fun ⟨d⟩ => consistent_bot _
      (importS4_typed (Γ := .nil) (atoms := fun _ => botCode) (fun _ => botCode_typed)
        (Δ := []) (φ := ⊥) d)⟩

end Controls

end CodeModel

end CertifiedTransformProgram.ExecutableModel
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
