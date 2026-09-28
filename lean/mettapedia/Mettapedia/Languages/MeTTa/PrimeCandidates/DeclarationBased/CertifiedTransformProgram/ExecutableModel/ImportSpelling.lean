import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.IntuitionisticImport
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.KernelSpelling
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.WrittenDomains

/-!
# Imported proofs in the kernel's spelling

The importer turns intuitionistic derivations into proof terms of the object package
(`IntDeriv.primeProof`). This module writes those terms, and their types, in the spelling the
runtime's kernel reads (`KTerm`), so that the kernel can check the same terms at the same types.

## Names

The object package already uses the kernel's names for its constants: `prop`, `imp`, the
quantifier instance `all@prop` (the instance name is the quantifier, `@`, and the printed
domain), and the proof family `__cetta_holds_df87b3cd8ab4b6383b1d0591` (the family prefix and the
first 24 hexadecimal digits of the digest of the runtime's set signature). `KTerm.nameText`
spells them unchanged (`nameText_prop`, `nameText_holds`, `nameText_imp`, `nameText_allProp`).

## Written domains

A λ of the calculus carries no domain, and the package's typing is declarative: `S K K` is
typed although its head `S` is a λ applied to another λ. The kernel checks bidirectionally: the
type of a λ without a domain can be checked against a function type but not synthesized, and a λ
applied to an argument needs one of the two synthesized, so `S` applied to `K` needs its domain
written. The importer's terms are therefore written as terms with written domains (`ATm`), each
λ of a combinator carrying the domain its typing introduces it at: `holds p` for the λ of an
implication `p ⇒ q`, and `prop` for the λ of a quantification over codes.

* `IntDeriv.writtenProof` writes the import of a derivation; erasing its domains gives the
  import (`IntDeriv.writtenProof_erase`).
* The written term is typed by the typing of terms with written domains, `ATyped`, in which a
  written domain is a contract: a type equal to the domain the λ is checked at
  (`IntDeriv.writtenProof_typed`). This is the contract the kernel checks.

## The spelling

`spellWritten` spells a term with written domains, a written domain as the domain of
`(Lam domain body)`; on terms without written domains it is `KTerm.ofTm`
(`spellWritten_ofTm`), and dropping the spelled domains gives the spelling of the erased term
(`ofTm_erase_of_spellWritten`). A spelled term reads back as the term with its domains
(`readWritten_spellWritten`) and, through `KTerm.toTm`, as the erased term
(`toTm_spellWritten`).

A typing judgment `Γ ⊢ t : T` reaches the kernel as one closed term, `judgmentWritten Γ t T`:
the ascription `(λ(y : T). y) t` under one λ per entry of `Γ`, the entry written as its domain.
The ascription is typed at `T` whenever `t` is and `T` is a type of the lowest universe
(`ascription_typed`).

## Examples

* `selfImpWritten`: `λ(c : prop). S K K`, the import of `S K K` with its atom bound, at
  `holds (all@prop (λc. imp c c))` (`selfImpWritten_typed`); its erasure is the term of
  `selfImp_closed`.
* `lemSelfImpWritten`: the classical derivation of `p ⊃ p` by excluded middle, imported by Barr's
  route, at the same type.
* `exampleWritten`: the geometric example `p₀ ⊃ p₃` from `p₀ ⊃ p₁ ∨ p₂`, `p₁ ⊃ p₃` and
  `p₂ ⊃ p₃`, in the context of its four atoms and three assumptions.
* Controls for the kernel: the bare spelling of `λc. S K K`, typed by `ATyped` with no domain
  written (`selfImpBare_typed`); `λc. S K K` at the type `holds (⊥ ⇒ ⊥)`; the closed `λc. K`,
  a proof of `holds (all@prop (λc. imp c (imp c c)))` (`kClosedWritten_typed`), at the type of
  `λc. S K K`; and `λc. S K K` with the domains of its first `K` replaced by those of its
  second, which erases to the same term (`forgedWritten_erase`).
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
open Package (U0)
open CertifiedTransformProgram.ArtifactComparison (KTerm)

namespace CodeModel

/-! ## The kernel's names of the package constants -/

theorem nameText_prop : KTerm.nameText propN = some "prop" := rfl

theorem nameText_holds :
    KTerm.nameText holdsN = some "__cetta_holds_df87b3cd8ab4b6383b1d0591" := rfl

theorem nameText_imp : KTerm.nameText impN = some "imp" := rfl

theorem nameText_allProp : KTerm.nameText allPropN = some "all@prop" := rfl

/-! ## The combinators with their domains written -/

section WrittenCombinators

variable {n : Nat}

/-- Ex falso, `λ(z : holds ⊥). z r`. -/
def efqWritten (r : Tower.Tm n) : ATm Tower.Head n :=
  .lamTyped (ATm.ofTm (programCodes.holdsOf botCode))
    (.app (.var 0) (ATm.ofTm (Presentation.rename wk r)))

/-- `K = λ(x : holds p). λ(y : holds q). x`. -/
def kWritten (p q : Tower.Tm n) : ATm Tower.Head n :=
  .lamTyped (ATm.ofTm (programCodes.holdsOf p))
    (.lamTyped (ATm.ofTm (programCodes.holdsOf (Presentation.rename wk q))) (.var 1))

/-- `S = λ(f : holds (p ⇒ q ⇒ r)). λ(g : holds (p ⇒ q)). λ(x : holds p). f x (g x)`. -/
def sWritten (p q r : Tower.Tm n) : ATm Tower.Head n :=
  .lamTyped
    (ATm.ofTm (programCodes.holdsOf (programCodes.impOf p (programCodes.impOf q r))))
    (.lamTyped
      (ATm.ofTm (programCodes.holdsOf
        (programCodes.impOf (Presentation.rename wk p) (Presentation.rename wk q))))
      (.lamTyped
        (ATm.ofTm (programCodes.holdsOf (Presentation.rename wk (Presentation.rename wk p))))
        (.app (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0)))))

/-- The first projection, `λ(z : holds (p ∧ q)). z p K`. -/
def fstWritten (p q : Tower.Tm n) : ATm Tower.Head n :=
  .lamTyped (ATm.ofTm (programCodes.holdsOf (andCode p q)))
    (.app (.app (.var 0) (ATm.ofTm (Presentation.rename wk p)))
      (kWritten (Presentation.rename wk p) (Presentation.rename wk q)))

/-- The second projection, `λ(z : holds (p ∧ q)). z q (λ(x : holds p). λ(y : holds q). y)`. -/
def sndWritten (p q : Tower.Tm n) : ATm Tower.Head n :=
  .lamTyped (ATm.ofTm (programCodes.holdsOf (andCode p q)))
    (.app (.app (.var 0) (ATm.ofTm (Presentation.rename wk q)))
      (.lamTyped (ATm.ofTm (programCodes.holdsOf (Presentation.rename wk p)))
        (.lamTyped
          (ATm.ofTm (programCodes.holdsOf (Presentation.rename wk (Presentation.rename wk q))))
          (.var 0))))

/-- Pairing, `λ(x : holds p). λ(y : holds q). λ(c : prop). λ(k : holds (p ⇒ q ⇒ c)). k x y`. -/
def pairWritten (p q : Tower.Tm n) : ATm Tower.Head n :=
  .lamTyped (ATm.ofTm (programCodes.holdsOf p))
    (.lamTyped (ATm.ofTm (programCodes.holdsOf (Presentation.rename wk q)))
      (.lamTyped (ATm.ofTm (.const propN))
        (.lamTyped
          (ATm.ofTm (programCodes.holdsOf (programCodes.impOf
            (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk p)))
            (programCodes.impOf
              (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk q)))
              (.var 0)))))
          (.app (.app (.var 0) (.var 3)) (.var 2)))))

/-- The left injection,
`λ(x : holds p). λ(c : prop). λ(l : holds (p ⇒ c)). λ(r : holds (q ⇒ c)). l x`. -/
def inlWritten (p q : Tower.Tm n) : ATm Tower.Head n :=
  .lamTyped (ATm.ofTm (programCodes.holdsOf p))
    (.lamTyped (ATm.ofTm (.const propN))
      (.lamTyped
        (ATm.ofTm (programCodes.holdsOf (programCodes.impOf
          (Presentation.rename wk (Presentation.rename wk p)) (.var 0))))
        (.lamTyped
          (ATm.ofTm (programCodes.holdsOf (programCodes.impOf
            (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk q)))
            (.var 1))))
          (.app (.var 1) (.var 3)))))

/-- The right injection,
`λ(y : holds q). λ(c : prop). λ(l : holds (p ⇒ c)). λ(r : holds (q ⇒ c)). r y`. -/
def inrWritten (p q : Tower.Tm n) : ATm Tower.Head n :=
  .lamTyped (ATm.ofTm (programCodes.holdsOf q))
    (.lamTyped (ATm.ofTm (.const propN))
      (.lamTyped
        (ATm.ofTm (programCodes.holdsOf (programCodes.impOf
          (Presentation.rename wk (Presentation.rename wk p)) (.var 0))))
        (.lamTyped
          (ATm.ofTm (programCodes.holdsOf (programCodes.impOf
            (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk q)))
            (.var 1))))
          (.app (.var 0) (.var 3)))))

/-- Case analysis,
`λ(f : holds (p ⇒ r)). λ(g : holds (q ⇒ r)). λ(z : holds (p ∨ q)). z r f g`. -/
def caseWritten (p q r : Tower.Tm n) : ATm Tower.Head n :=
  .lamTyped (ATm.ofTm (programCodes.holdsOf (programCodes.impOf p r)))
    (.lamTyped
      (ATm.ofTm (programCodes.holdsOf
        (programCodes.impOf (Presentation.rename wk q) (Presentation.rename wk r))))
      (.lamTyped
        (ATm.ofTm (programCodes.holdsOf
          (Presentation.rename wk (Presentation.rename wk (orCode p q)))))
        (.app (.app (.app (.var 0)
          (ATm.ofTm (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk r)))))
          (.var 2)) (.var 1))))

/-! ### Erasing the domains gives the combinators -/

theorem efqWritten_erase (r : Tower.Tm n) : (efqWritten r).erase = efqProof r := by
  simp only [efqWritten, efqProof, ATm.erase, ATm.erase_ofTm]

theorem kWritten_erase (p q : Tower.Tm n) : (kWritten p q).erase = kProof := rfl

theorem sWritten_erase (p q r : Tower.Tm n) : (sWritten p q r).erase = sProof := rfl

theorem fstWritten_erase (p q : Tower.Tm n) : (fstWritten p q).erase = fstProof p := by
  simp only [fstWritten, fstProof, ATm.erase, ATm.erase_ofTm, kWritten_erase]

theorem sndWritten_erase (p q : Tower.Tm n) : (sndWritten p q).erase = sndProof q := by
  simp only [sndWritten, sndProof, ATm.erase, ATm.erase_ofTm]

theorem pairWritten_erase (p q : Tower.Tm n) : (pairWritten p q).erase = pairProof := rfl

theorem inlWritten_erase (p q : Tower.Tm n) : (inlWritten p q).erase = inlProof := rfl

theorem inrWritten_erase (p q : Tower.Tm n) : (inrWritten p q).erase = inrProof := rfl

theorem caseWritten_erase (p q r : Tower.Tm n) : (caseWritten p q r).erase = caseProof r := by
  simp only [caseWritten, caseProof, ATm.erase, ATm.erase_ofTm]

end WrittenCombinators

/-! ## Natural deduction for the codes, with written domains -/

section WrittenTyping

variable {n : Nat} {Θ : Tower.Ctx n}

/-- Introduction of an implication code by a λ whose written domain is `holds p`. -/
theorem impIntroW {p q : Tower.Tm n} {body : ATm Tower.Head (n + 1)}
    (hp : Typed objectRules Θ p (.const propN)) (hq : Typed objectRules Θ q (.const propN))
    (hbody : ATyped objectRules (.snoc Θ (programCodes.holdsOf p)) body
      (programCodes.holdsOf (Presentation.rename wk q))) :
    ATyped objectRules Θ (.lamTyped (ATm.ofTm (programCodes.holdsOf p)) body)
      (programCodes.holdsOf (programCodes.impOf p q)) :=
  .conv (.lamTyped (ATyped.ofTyped (holdsO hp)) (.sort _)
      (by rw [ATm.erase_ofTm]; exact Derivable.refl (holdsO hp))
      (piO (holdsO hp) (holdsO hq.weaken)) (.sort _) hbody)
    (.symm (equal_holds_imp hp hq)) (.sort _)

/-- Elimination of an implication code: application. -/
theorem impElimW {p q : Tower.Tm n} {f a : ATm Tower.Head n}
    (hp : Typed objectRules Θ p (.const propN)) (hq : Typed objectRules Θ q (.const propN))
    (hf : ATyped objectRules Θ f (programCodes.holdsOf (programCodes.impOf p q)))
    (ha : ATyped objectRules Θ a (programCodes.holdsOf p)) :
    ATyped objectRules Θ (.app f a) (programCodes.holdsOf q) := by
  have applied : ATyped objectRules Θ (.app f a)
      (programCodes.holdsOf (inst0 a.erase (Presentation.rename wk q))) :=
    .appElim (.conv hf (equal_holds_imp hp hq) (.sort _)) ha
  rw [inst0_rename_wk] at applied
  exact applied

/-- Introduction of a quantification over codes by a λ whose written domain is `prop`. -/
theorem allIntroW {B : Tower.Tm (n + 1)} {body : ATm Tower.Head (n + 1)}
    (hB : Typed objectRules (.snoc Θ (.const propN)) B (.const propN))
    (hbody : ATyped objectRules (.snoc Θ (.const propN)) body (programCodes.holdsOf B)) :
    ATyped objectRules Θ (.lamTyped (ATm.ofTm (.const propN)) body)
      (programCodes.holdsOf (allPropOf (.lam B))) :=
  .conv (.lamTyped (ATyped.ofTyped prop_typedO) (.sort _) (Derivable.refl prop_typedO)
      (piO prop_typedO (holdsO hB)) (.sort _) hbody)
    (.symm (equal_holds_allProp_lam hB)) (.sort _)

/-- Elimination of a quantification over codes, at a code. -/
theorem allElimW {B : Tower.Tm (n + 1)} {f : ATm Tower.Head n} {c : Tower.Tm n}
    (hB : Typed objectRules (.snoc Θ (.const propN)) B (.const propN))
    (hf : ATyped objectRules Θ f (programCodes.holdsOf (allPropOf (.lam B))))
    (hc : Typed objectRules Θ c (.const propN)) :
    ATyped objectRules Θ (.app f (ATm.ofTm c)) (programCodes.holdsOf (inst0 c B)) := by
  have applied := ATyped.appElim (.conv hf (equal_holds_allProp_lam hB) (.sort _))
    (ATyped.ofTyped hc)
  rw [ATm.erase_ofTm] at applied
  exact applied

/-- Falsity eliminates into every code. -/
theorem botElimW {z : ATm Tower.Head n} {r : Tower.Tm n}
    (hz : ATyped objectRules Θ z (programCodes.holdsOf botCode))
    (hr : Typed objectRules Θ r (.const propN)) :
    ATyped objectRules Θ (.app z (ATm.ofTm r)) (programCodes.holdsOf r) :=
  allElimW (B := .var 0) (.var 0) hz hr

/-- Elimination of a conjunction code. -/
theorem andElimW {p q r : Tower.Tm n} {z k : ATm Tower.Head n}
    (hp : Typed objectRules Θ p (.const propN)) (hq : Typed objectRules Θ q (.const propN))
    (hr : Typed objectRules Θ r (.const propN))
    (hz : ATyped objectRules Θ z (programCodes.holdsOf (andCode p q)))
    (hk : ATyped objectRules Θ k
      (programCodes.holdsOf (programCodes.impOf p (programCodes.impOf q r)))) :
    ATyped objectRules Θ (.app (.app z (ATm.ofTm r)) k) (programCodes.holdsOf r) := by
  have instantiated : ATyped objectRules Θ (.app z (ATm.ofTm r))
      (programCodes.holdsOf (programCodes.impOf
        (programCodes.impOf (inst0 r (Presentation.rename wk p))
          (programCodes.impOf (inst0 r (Presentation.rename wk q)) r)) r)) :=
    allElimW (impO (impO hp.weaken (impO hq.weaken (.var 0))) (.var 0)) hz hr
  rw [inst0_rename_wk, inst0_rename_wk] at instantiated
  exact impElimW (impO hp (impO hq hr)) hr instantiated hk

/-- Introduction of a conjunction code. -/
theorem pairW {p q : Tower.Tm n} {a b : ATm Tower.Head n}
    (hp : Typed objectRules Θ p (.const propN)) (hq : Typed objectRules Θ q (.const propN))
    (ha : ATyped objectRules Θ a (programCodes.holdsOf p))
    (hb : ATyped objectRules Θ b (programCodes.holdsOf q)) :
    ATyped objectRules Θ (.lamTyped (ATm.ofTm (.const propN))
        (.lamTyped (ATm.ofTm (programCodes.holdsOf (programCodes.impOf (Presentation.rename wk p)
            (programCodes.impOf (Presentation.rename wk q) (.var 0)))))
          (.app (.app (.var 0) (ATm.rename wk (ATm.rename wk a)))
            (ATm.rename wk (ATm.rename wk b)))))
      (programCodes.holdsOf (andCode p q)) := by
  refine allIntroW (impO (impO hp.weaken (impO hq.weaken (.var 0))) (.var 0)) ?_
  refine impIntroW (impO hp.weaken (impO hq.weaken (.var 0))) (.var 0) ?_
  exact impElimW hq.weaken.weaken (.var 1)
    (impElimW hp.weaken.weaken (impO hq.weaken.weaken (.var 1)) (.var 0) ha.weaken.weaken)
    hb.weaken.weaken

/-- Left introduction of a disjunction code. -/
theorem inlW {p q : Tower.Tm n} {a : ATm Tower.Head n}
    (hp : Typed objectRules Θ p (.const propN)) (hq : Typed objectRules Θ q (.const propN))
    (ha : ATyped objectRules Θ a (programCodes.holdsOf p)) :
    ATyped objectRules Θ (.lamTyped (ATm.ofTm (.const propN))
        (.lamTyped
          (ATm.ofTm (programCodes.holdsOf
            (programCodes.impOf (Presentation.rename wk p) (.var 0))))
          (.lamTyped
            (ATm.ofTm (programCodes.holdsOf (programCodes.impOf
              (Presentation.rename wk (Presentation.rename wk q)) (.var 1))))
            (.app (.var 1) (ATm.rename wk (ATm.rename wk (ATm.rename wk a)))))))
      (programCodes.holdsOf (orCode p q)) := by
  refine allIntroW (impO (impO hp.weaken (.var 0)) (impO (impO hq.weaken (.var 0)) (.var 0))) ?_
  refine impIntroW (impO hp.weaken (.var 0)) (impO (impO hq.weaken (.var 0)) (.var 0)) ?_
  refine impIntroW (impO hq.weaken.weaken (.var 1)) (.var 1) ?_
  exact impElimW hp.weaken.weaken.weaken (.var 2) (.var 1) ha.weaken.weaken.weaken

/-- Right introduction of a disjunction code. -/
theorem inrW {p q : Tower.Tm n} {b : ATm Tower.Head n}
    (hp : Typed objectRules Θ p (.const propN)) (hq : Typed objectRules Θ q (.const propN))
    (hb : ATyped objectRules Θ b (programCodes.holdsOf q)) :
    ATyped objectRules Θ (.lamTyped (ATm.ofTm (.const propN))
        (.lamTyped
          (ATm.ofTm (programCodes.holdsOf
            (programCodes.impOf (Presentation.rename wk p) (.var 0))))
          (.lamTyped
            (ATm.ofTm (programCodes.holdsOf (programCodes.impOf
              (Presentation.rename wk (Presentation.rename wk q)) (.var 1))))
            (.app (.var 0) (ATm.rename wk (ATm.rename wk (ATm.rename wk b)))))))
      (programCodes.holdsOf (orCode p q)) := by
  refine allIntroW (impO (impO hp.weaken (.var 0)) (impO (impO hq.weaken (.var 0)) (.var 0))) ?_
  refine impIntroW (impO hp.weaken (.var 0)) (impO (impO hq.weaken (.var 0)) (.var 0)) ?_
  refine impIntroW (impO hq.weaken.weaken (.var 1)) (.var 1) ?_
  exact impElimW hq.weaken.weaken.weaken (.var 2) (.var 0) hb.weaken.weaken.weaken

/-- Elimination of a disjunction code. -/
theorem caseW {p q r : Tower.Tm n} {z f g : ATm Tower.Head n}
    (hp : Typed objectRules Θ p (.const propN)) (hq : Typed objectRules Θ q (.const propN))
    (hr : Typed objectRules Θ r (.const propN))
    (hz : ATyped objectRules Θ z (programCodes.holdsOf (orCode p q)))
    (hf : ATyped objectRules Θ f (programCodes.holdsOf (programCodes.impOf p r)))
    (hg : ATyped objectRules Θ g (programCodes.holdsOf (programCodes.impOf q r))) :
    ATyped objectRules Θ (.app (.app (.app z (ATm.ofTm r)) f) g) (programCodes.holdsOf r) := by
  have instantiated : ATyped objectRules Θ (.app z (ATm.ofTm r))
      (programCodes.holdsOf (programCodes.impOf
        (programCodes.impOf (inst0 r (Presentation.rename wk p)) r)
        (programCodes.impOf (programCodes.impOf (inst0 r (Presentation.rename wk q)) r) r))) :=
    allElimW (impO (impO hp.weaken (.var 0)) (impO (impO hq.weaken (.var 0)) (.var 0))) hz hr
  rw [inst0_rename_wk, inst0_rename_wk] at instantiated
  exact impElimW (impO hq hr) hr
    (impElimW (impO hp hr) (impO (impO hq hr) hr) instantiated hf) hg

end WrittenTyping

section WrittenCombinatorTyping

variable {n : Nat} {Θ : Tower.Ctx n} {p q r : Tower.Tm n}

theorem efqWritten_typed (hr : Typed objectRules Θ r (.const propN)) :
    ATyped objectRules Θ (efqWritten r)
      (programCodes.holdsOf (programCodes.impOf botCode r)) :=
  impIntroW botCode_typed hr (botElimW (.var 0) hr.weaken)

theorem kWritten_typed (hp : Typed objectRules Θ p (.const propN))
    (hq : Typed objectRules Θ q (.const propN)) :
    ATyped objectRules Θ (kWritten p q)
      (programCodes.holdsOf (programCodes.impOf p (programCodes.impOf q p))) :=
  impIntroW hp (impO hq hp) (impIntroW hq.weaken hp.weaken (.var 1))

theorem sWritten_typed (hp : Typed objectRules Θ p (.const propN))
    (hq : Typed objectRules Θ q (.const propN)) (hr : Typed objectRules Θ r (.const propN)) :
    ATyped objectRules Θ (sWritten p q r) (programCodes.holdsOf (programCodes.impOf
      (programCodes.impOf p (programCodes.impOf q r))
      (programCodes.impOf (programCodes.impOf p q) (programCodes.impOf p r)))) := by
  refine impIntroW (impO hp (impO hq hr)) (impO (impO hp hq) (impO hp hr)) ?_
  refine impIntroW (impO hp.weaken hq.weaken) (impO hp.weaken hr.weaken) ?_
  refine impIntroW hp.weaken.weaken hr.weaken.weaken ?_
  exact impElimW hq.weaken.weaken.weaken hr.weaken.weaken.weaken
    (impElimW hp.weaken.weaken.weaken (impO hq.weaken.weaken.weaken hr.weaken.weaken.weaken)
      (.var 2) (.var 0))
    (impElimW hp.weaken.weaken.weaken hq.weaken.weaken.weaken (.var 1) (.var 0))

theorem fstWritten_typed (hp : Typed objectRules Θ p (.const propN))
    (hq : Typed objectRules Θ q (.const propN)) :
    ATyped objectRules Θ (fstWritten p q)
      (programCodes.holdsOf (programCodes.impOf (andCode p q) p)) := by
  refine impIntroW (andCode_typed hp hq) hp ?_
  refine andElimW hp.weaken hq.weaken hp.weaken ?_ (kWritten_typed hp.weaken hq.weaken)
  rw [← rename_andCode]
  exact .var 0

theorem sndWritten_typed (hp : Typed objectRules Θ p (.const propN))
    (hq : Typed objectRules Θ q (.const propN)) :
    ATyped objectRules Θ (sndWritten p q)
      (programCodes.holdsOf (programCodes.impOf (andCode p q) q)) := by
  refine impIntroW (andCode_typed hp hq) hq ?_
  refine andElimW hp.weaken hq.weaken hq.weaken ?_
    (impIntroW hp.weaken (impO hq.weaken hq.weaken)
      (impIntroW hq.weaken.weaken hq.weaken.weaken (.var 0)))
  rw [← rename_andCode]
  exact .var 0

theorem pairWritten_typed (hp : Typed objectRules Θ p (.const propN))
    (hq : Typed objectRules Θ q (.const propN)) :
    ATyped objectRules Θ (pairWritten p q)
      (programCodes.holdsOf (programCodes.impOf p (programCodes.impOf q (andCode p q)))) := by
  refine impIntroW hp (impO hq (andCode_typed hp hq))
    (impIntroW hq.weaken (andCode_typed hp hq).weaken ?_)
  rw [rename_andCode, rename_andCode]
  refine pairW (a := .var 1) (b := .var 0) hp.weaken.weaken hq.weaken.weaken ?_ ?_
  · exact .var 1
  · exact .var 0

theorem inlWritten_typed (hp : Typed objectRules Θ p (.const propN))
    (hq : Typed objectRules Θ q (.const propN)) :
    ATyped objectRules Θ (inlWritten p q)
      (programCodes.holdsOf (programCodes.impOf p (orCode p q))) := by
  refine impIntroW hp (orCode_typed hp hq) ?_
  rw [rename_orCode]
  refine inlW (a := .var 0) hp.weaken hq.weaken ?_
  exact .var 0

theorem inrWritten_typed (hp : Typed objectRules Θ p (.const propN))
    (hq : Typed objectRules Θ q (.const propN)) :
    ATyped objectRules Θ (inrWritten p q)
      (programCodes.holdsOf (programCodes.impOf q (orCode p q))) := by
  refine impIntroW hq (orCode_typed hp hq) ?_
  rw [rename_orCode]
  refine inrW (b := .var 0) hp.weaken hq.weaken ?_
  exact .var 0

theorem caseWritten_typed (hp : Typed objectRules Θ p (.const propN))
    (hq : Typed objectRules Θ q (.const propN)) (hr : Typed objectRules Θ r (.const propN)) :
    ATyped objectRules Θ (caseWritten p q r) (programCodes.holdsOf (programCodes.impOf
      (programCodes.impOf p r)
      (programCodes.impOf (programCodes.impOf q r) (programCodes.impOf (orCode p q) r)))) := by
  have hor := orCode_typed hp hq
  refine impIntroW (impO hp hr) (impO (impO hq hr) (impO hor hr)) ?_
  refine impIntroW (impO hq.weaken hr.weaken) (impO hor.weaken hr.weaken) ?_
  refine impIntroW hor.weaken.weaken hr.weaken.weaken ?_
  refine caseW hp.weaken.weaken.weaken hq.weaken.weaken.weaken hr.weaken.weaken.weaken ?_
    (.var 2) (.var 1)
  rw [← rename_orCode, ← rename_orCode, ← rename_orCode]
  exact .var 0

end WrittenCombinatorTyping

/-! ## The importer with written domains -/

section WrittenTranslation

/-- The proof translation with the domains of the combinators written. -/
def IntDeriv.toPrimeWritten {m : Nat} (atoms : ℕ → Tower.Tm m)
    {Δ : List (Propositional.Formula ℕ)}
    (hyps : (δ : Propositional.Formula ℕ) → δ ∈ Δ → ATm Tower.Head m) :
    {φ : Propositional.Formula ℕ} → IntDeriv Δ φ → ATm Tower.Head m
  | _, .hyp h => hyps _ h
  | _, .efq φ => efqWritten (encode atoms φ)
  | _, .lem _ h => nomatch h
  | _, .implyK φ ψ => kWritten (encode atoms φ) (encode atoms ψ)
  | _, .implyS φ ψ χ => sWritten (encode atoms φ) (encode atoms ψ) (encode atoms χ)
  | _, .andElimL φ ψ => fstWritten (encode atoms φ) (encode atoms ψ)
  | _, .andElimR φ ψ => sndWritten (encode atoms φ) (encode atoms ψ)
  | _, .andIntro φ ψ => pairWritten (encode atoms φ) (encode atoms ψ)
  | _, .orIntroL φ ψ => inlWritten (encode atoms φ) (encode atoms ψ)
  | _, .orIntroR φ ψ => inrWritten (encode atoms φ) (encode atoms ψ)
  | _, .orElim φ ψ χ => caseWritten (encode atoms φ) (encode atoms ψ) (encode atoms χ)
  | _, .mdp d₁ d₂ =>
    .app (IntDeriv.toPrimeWritten atoms hyps d₁) (IntDeriv.toPrimeWritten atoms hyps d₂)

/-- Erasing the written domains of the translation gives the proof translation. -/
theorem IntDeriv.toPrimeWritten_erase {m : Nat} (atoms : ℕ → Tower.Tm m)
    {Δ : List (Propositional.Formula ℕ)}
    (hyps : (δ : Propositional.Formula ℕ) → δ ∈ Δ → Tower.Tm m) :
    ∀ {φ : Propositional.Formula ℕ} (d : IntDeriv Δ φ),
      (IntDeriv.toPrimeWritten atoms (fun δ h => ATm.ofTm (hyps δ h)) d).erase =
        IntDeriv.toPrime atoms hyps d
  | _, .hyp h => ATm.erase_ofTm (hyps _ h)
  | _, .efq φ => efqWritten_erase (encode atoms φ)
  | _, .lem _ h => nomatch h
  | _, .implyK _ _ => rfl
  | _, .implyS _ _ _ => rfl
  | _, .andElimL φ ψ => fstWritten_erase (encode atoms φ) (encode atoms ψ)
  | _, .andElimR φ ψ => sndWritten_erase (encode atoms φ) (encode atoms ψ)
  | _, .andIntro _ _ => rfl
  | _, .orIntroL _ _ => rfl
  | _, .orIntroR _ _ => rfl
  | _, .orElim φ ψ χ => caseWritten_erase (encode atoms φ) (encode atoms ψ) (encode atoms χ)
  | _, .mdp d₁ d₂ => by
    change Tm.app (IntDeriv.toPrimeWritten atoms (fun δ h => ATm.ofTm (hyps δ h)) d₁).erase
      (IntDeriv.toPrimeWritten atoms (fun δ h => ATm.ofTm (hyps δ h)) d₂).erase = _
    rw [IntDeriv.toPrimeWritten_erase atoms hyps d₁, IntDeriv.toPrimeWritten_erase atoms hyps d₂]
    rfl

/-- **Typing of the translation with written domains.** Every written domain is the domain
its λ is checked at. -/
theorem IntDeriv.toPrimeWritten_typed {m : Nat} {Θ : Tower.Ctx m} {atoms : ℕ → Tower.Tm m}
    (hatoms : ∀ a, Typed objectRules Θ (atoms a) (.const propN))
    {Δ : List (Propositional.Formula ℕ)}
    {hyps : (δ : Propositional.Formula ℕ) → δ ∈ Δ → ATm Tower.Head m}
    (hhyps : ∀ δ (h : δ ∈ Δ),
      ATyped objectRules Θ (hyps δ h) (programCodes.holdsOf (encode atoms δ))) :
    ∀ {φ : Propositional.Formula ℕ} (d : IntDeriv Δ φ),
      ATyped objectRules Θ (IntDeriv.toPrimeWritten atoms hyps d)
        (programCodes.holdsOf (encode atoms φ))
  | _, .hyp h => hhyps _ h
  | _, .efq φ => efqWritten_typed (encode_typed hatoms φ)
  | _, .lem _ h => nomatch h
  | _, .implyK φ ψ => kWritten_typed (encode_typed hatoms φ) (encode_typed hatoms ψ)
  | _, .implyS φ ψ χ =>
    sWritten_typed (encode_typed hatoms φ) (encode_typed hatoms ψ) (encode_typed hatoms χ)
  | _, .andElimL φ ψ => fstWritten_typed (encode_typed hatoms φ) (encode_typed hatoms ψ)
  | _, .andElimR φ ψ => sndWritten_typed (encode_typed hatoms φ) (encode_typed hatoms ψ)
  | _, .andIntro φ ψ => pairWritten_typed (encode_typed hatoms φ) (encode_typed hatoms ψ)
  | _, .orIntroL φ ψ => inlWritten_typed (encode_typed hatoms φ) (encode_typed hatoms ψ)
  | _, .orIntroR φ ψ => inrWritten_typed (encode_typed hatoms φ) (encode_typed hatoms ψ)
  | _, .orElim φ ψ χ =>
    caseWritten_typed (encode_typed hatoms φ) (encode_typed hatoms ψ) (encode_typed hatoms χ)
  | _, .mdp (φ := φ) (ψ := ψ) d₁ d₂ =>
    impElimW (encode_typed hatoms φ) (encode_typed hatoms ψ)
      (IntDeriv.toPrimeWritten_typed hatoms hhyps d₁)
      (IntDeriv.toPrimeWritten_typed hatoms hhyps d₂)

/-- **The importer with written domains**: the assumptions are the proof variables of
`hypCtx`, as in `IntDeriv.primeProof`. -/
def IntDeriv.writtenProof {n : Nat} (atoms : ℕ → Tower.Tm n)
    {Δ : List (Propositional.Formula ℕ)} {φ : Propositional.Formula ℕ} (d : IntDeriv Δ φ) :
    ATm Tower.Head (n + Δ.length) :=
  IntDeriv.toPrimeWritten (atomsPast atoms Δ) (fun δ h => ATm.ofTm (hypVar Δ δ h)) d

/-- Erasing the written domains gives the import. -/
theorem IntDeriv.writtenProof_erase {n : Nat} (atoms : ℕ → Tower.Tm n)
    {Δ : List (Propositional.Formula ℕ)} {φ : Propositional.Formula ℕ} (d : IntDeriv Δ φ) :
    (IntDeriv.writtenProof atoms d).erase = IntDeriv.primeProof atoms d :=
  IntDeriv.toPrimeWritten_erase (atomsPast atoms Δ) (hypVar Δ) d

/-- **Typing of the importer with written domains**, at the type of `primeProof_typed`. -/
theorem IntDeriv.writtenProof_typed {n : Nat} {Γ : Tower.Ctx n} {atoms : ℕ → Tower.Tm n}
    (hatoms : ∀ a, Typed objectRules Γ (atoms a) (.const propN))
    {Δ : List (Propositional.Formula ℕ)} {φ : Propositional.Formula ℕ} (d : IntDeriv Δ φ) :
    ATyped objectRules (hypCtx Γ atoms Δ) (IntDeriv.writtenProof atoms d)
      (programCodes.holdsOf (encode (atomsPast atoms Δ) φ)) :=
  IntDeriv.toPrimeWritten_typed (atomsPast_typed hatoms Δ)
    (fun δ h => ATyped.ofTyped (hypVar_typed Δ δ h)) d

end WrittenTranslation

/-! ## The kernel spelling of terms with written domains -/

section Spelling

/-- The kernel spelling of a term with written domains: a λ with a written domain is
`(Lam domain body)`, a bare λ is `(Lam body)`. -/
def spellWritten : {n : Nat} → ATm Tower.Head n → Option KTerm
  | _, .var index => some (.idx index.val)
  | _, .const name => (KTerm.nameText name).map .declConst
  | _, .head (.sort (.const level)) => some (.sortConst level)
  | _, .head _ => none
  | _, .pi domain codomain => do pure (.pi (← spellWritten domain) (← spellWritten codomain))
  | _, .sigma domain codomain =>
      do pure (.sigma (← spellWritten domain) (← spellWritten codomain))
  | _, .id carrier left right =>
      do pure (.ident (← spellWritten carrier) (← spellWritten left) (← spellWritten right))
  | _, .lamBare body => do pure (.lamBare (← spellWritten body))
  | _, .lamTyped domain body =>
      do pure (.lamTyped (← spellWritten domain) (← spellWritten body))
  | _, .app function argument =>
      do pure (.app (← spellWritten function) (← spellWritten argument))
  | _, .pair first second => do pure (.pair (← spellWritten first) (← spellWritten second))
  | _, .fst package => do pure (.fst (← spellWritten package))
  | _, .snd package => do pure (.snd (← spellWritten package))
  | _, .refl term => do pure (.refl (← spellWritten term))

/-- Read a kernel spelling back as a term with written domains. -/
def readWritten : {n : Nat} → KTerm → Option (ATm Tower.Head n)
  | _, .declConst name => some (.const (.mkSimple name))
  | n, .app function argument => do
      let function ← readWritten (n := n) function
      let argument ← readWritten (n := n) argument
      pure (.app function argument)
  | n, .lamTyped domain body => do
      let domain ← readWritten (n := n) domain
      let body ← readWritten (n := n + 1) body
      pure (.lamTyped domain body)
  | n, .lamBare body => do
      let body ← readWritten (n := n + 1) body
      pure (.lamBare body)
  | n, .pi domain codomain => do
      let domain ← readWritten (n := n) domain
      let codomain ← readWritten (n := n + 1) codomain
      pure (.pi domain codomain)
  | n, .sigma domain codomain => do
      let domain ← readWritten (n := n) domain
      let codomain ← readWritten (n := n + 1) codomain
      pure (.sigma domain codomain)
  | n, .ident carrier left right => do
      let carrier ← readWritten (n := n) carrier
      let left ← readWritten (n := n) left
      let right ← readWritten (n := n) right
      pure (.id carrier left right)
  | n, .refl term => do
      let term ← readWritten (n := n) term
      pure (.refl term)
  | n, .pair first second => do
      let first ← readWritten (n := n) first
      let second ← readWritten (n := n) second
      pure (.pair first second)
  | n, .fst package => do
      let package ← readWritten (n := n) package
      pure (.fst package)
  | n, .snd package => do
      let package ← readWritten (n := n) package
      pure (.snd package)
  | n, .idx index => if bound : index < n then some (.var ⟨index, bound⟩) else none
  | _, .pvar _ => none
  | _, .sortConst level => some (.head (.sort (.const level)))

/-- **Read-back.** A spelled term reads back as the term, its written domains included. -/
theorem readWritten_spellWritten : ∀ {n : Nat} (term : ATm Tower.Head n) {spelled : KTerm},
    spellWritten term = some spelled → readWritten spelled = some term
  | n, .var index, spelled, equal => by
      simp only [spellWritten, Option.some.injEq] at equal
      subst equal
      simp [readWritten, index.isLt]
  | _, .const name, spelled, equal => by
      simp only [spellWritten, Option.map_eq_some_iff] at equal
      obtain ⟨text, named, rfl⟩ := equal
      show some (ATm.const (Lean.Name.mkSimple text) : ATm Tower.Head _) = some (ATm.const name)
      rw [KTerm.nameText_some named]
  | _, .head (.sort (.const level)), spelled, equal => by
      simp only [spellWritten, Option.some.injEq] at equal
      subst equal
      rfl
  | _, .head (.sort (.param _)), _, equal => by simp [spellWritten] at equal
  | _, .head (.sort (.succ _)), _, equal => by simp [spellWritten] at equal
  | _, .head (.sort (.max _ _)), _, equal => by simp [spellWritten] at equal
  | _, .head .legacyGround, _, equal => by simp [spellWritten] at equal
  | _, .pi domain codomain, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨d, dSpelled, c, cSpelled, rfl⟩ := equal
      simp only [readWritten, readWritten_spellWritten domain dSpelled,
        readWritten_spellWritten codomain cSpelled, bind, Option.bind_some, pure]
  | _, .sigma domain codomain, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨d, dSpelled, c, cSpelled, rfl⟩ := equal
      simp only [readWritten, readWritten_spellWritten domain dSpelled,
        readWritten_spellWritten codomain cSpelled, bind, Option.bind_some, pure]
  | _, .id carrier left right, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨c, cSpelled, l, lSpelled, r, rSpelled, rfl⟩ := equal
      simp only [readWritten, readWritten_spellWritten carrier cSpelled,
        readWritten_spellWritten left lSpelled, readWritten_spellWritten right rSpelled, bind,
        Option.bind_some, pure]
  | _, .lamBare body, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨b, bSpelled, rfl⟩ := equal
      simp only [readWritten, readWritten_spellWritten body bSpelled, bind, Option.bind_some,
        pure]
  | _, .lamTyped domain body, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨d, dSpelled, b, bSpelled, rfl⟩ := equal
      simp only [readWritten, readWritten_spellWritten domain dSpelled,
        readWritten_spellWritten body bSpelled, bind, Option.bind_some, pure]
  | _, .app function argument, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨f, fSpelled, a, aSpelled, rfl⟩ := equal
      simp only [readWritten, readWritten_spellWritten function fSpelled,
        readWritten_spellWritten argument aSpelled, bind, Option.bind_some, pure]
  | _, .pair first second, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨f, fSpelled, s, sSpelled, rfl⟩ := equal
      simp only [readWritten, readWritten_spellWritten first fSpelled,
        readWritten_spellWritten second sSpelled, bind, Option.bind_some, pure]
  | _, .fst package, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨p, pSpelled, rfl⟩ := equal
      simp only [readWritten, readWritten_spellWritten package pSpelled, bind, Option.bind_some,
        pure]
  | _, .snd package, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨p, pSpelled, rfl⟩ := equal
      simp only [readWritten, readWritten_spellWritten package pSpelled, bind, Option.bind_some,
        pure]
  | _, .refl term, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨t, tSpelled, rfl⟩ := equal
      simp only [readWritten, readWritten_spellWritten term tSpelled, bind, Option.bind_some,
        pure]

/-- **Read-back through `KTerm.toTm`.** The existing reading of the kernel's spelling, which
drops the domains of λs, reads a spelled term back as its erasure. -/
theorem toTm_spellWritten : ∀ {n : Nat} (term : ATm Tower.Head n) {spelled : KTerm},
    spellWritten term = some spelled → spelled.toTm (fun _ => none) = some term.erase
  | n, .var index, spelled, equal => by
      simp only [spellWritten, Option.some.injEq] at equal
      subst equal
      simp [KTerm.toTm, index.isLt, ATm.erase]
  | _, .const name, spelled, equal => by
      simp only [spellWritten, Option.map_eq_some_iff] at equal
      obtain ⟨text, named, rfl⟩ := equal
      show some (Tm.const (Lean.Name.mkSimple text) : Tower.Tm _) = some (Tm.const name)
      rw [KTerm.nameText_some named]
  | _, .head (.sort (.const level)), spelled, equal => by
      simp only [spellWritten, Option.some.injEq] at equal
      subst equal
      rfl
  | _, .head (.sort (.param _)), _, equal => by simp [spellWritten] at equal
  | _, .head (.sort (.succ _)), _, equal => by simp [spellWritten] at equal
  | _, .head (.sort (.max _ _)), _, equal => by simp [spellWritten] at equal
  | _, .head .legacyGround, _, equal => by simp [spellWritten] at equal
  | _, .pi domain codomain, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨d, dSpelled, c, cSpelled, rfl⟩ := equal
      simp only [KTerm.toTm, ATm.erase, toTm_spellWritten domain dSpelled, Option.map_none,
        toTm_spellWritten codomain cSpelled, bind, Option.bind_some, pure]
  | _, .sigma domain codomain, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨d, dSpelled, c, cSpelled, rfl⟩ := equal
      simp only [KTerm.toTm, ATm.erase, toTm_spellWritten domain dSpelled, Option.map_none,
        toTm_spellWritten codomain cSpelled, bind, Option.bind_some, pure]
  | _, .id carrier left right, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨c, cSpelled, l, lSpelled, r, rSpelled, rfl⟩ := equal
      simp only [KTerm.toTm, ATm.erase, toTm_spellWritten carrier cSpelled,
        toTm_spellWritten left lSpelled, toTm_spellWritten right rSpelled, bind,
        Option.bind_some, pure]
  | _, .lamBare body, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨b, bSpelled, rfl⟩ := equal
      simp only [KTerm.toTm, ATm.erase, Option.map_none, toTm_spellWritten body bSpelled, bind,
        Option.bind_some, pure]
  | _, .lamTyped domain body, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨d, _, b, bSpelled, rfl⟩ := equal
      simp only [KTerm.toTm, ATm.erase, Option.map_none, toTm_spellWritten body bSpelled, bind,
        Option.bind_some, pure]
  | _, .app function argument, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨f, fSpelled, a, aSpelled, rfl⟩ := equal
      simp only [KTerm.toTm, ATm.erase, toTm_spellWritten function fSpelled,
        toTm_spellWritten argument aSpelled, bind, Option.bind_some, pure]
  | _, .pair first second, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨f, fSpelled, s, sSpelled, rfl⟩ := equal
      simp only [KTerm.toTm, ATm.erase, toTm_spellWritten first fSpelled,
        toTm_spellWritten second sSpelled, bind, Option.bind_some, pure]
  | _, .fst package, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨p, pSpelled, rfl⟩ := equal
      simp only [KTerm.toTm, ATm.erase, toTm_spellWritten package pSpelled, bind,
        Option.bind_some, pure]
  | _, .snd package, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨p, pSpelled, rfl⟩ := equal
      simp only [KTerm.toTm, ATm.erase, toTm_spellWritten package pSpelled, bind,
        Option.bind_some, pure]
  | _, .refl term, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨t, tSpelled, rfl⟩ := equal
      simp only [KTerm.toTm, ATm.erase, toTm_spellWritten term tSpelled, bind, Option.bind_some,
        pure]

/-- On a term with no domain written, the spelling is `KTerm.ofTm`. -/
theorem spellWritten_ofTm : ∀ {n : Nat} (term : Tower.Tm n),
    spellWritten (ATm.ofTm term) = KTerm.ofTm term
  | _, .var _ => rfl
  | _, .const _ => rfl
  | _, .head (.sort (.const _)) => rfl
  | _, .head (.sort (.param _)) => rfl
  | _, .head (.sort (.succ _)) => rfl
  | _, .head (.sort (.max _ _)) => rfl
  | _, .head .legacyGround => rfl
  | _, .pi domain codomain => by
      simp only [ATm.ofTm, spellWritten, KTerm.ofTm, spellWritten_ofTm domain,
        spellWritten_ofTm codomain]
  | _, .sigma domain codomain => by
      simp only [ATm.ofTm, spellWritten, KTerm.ofTm, spellWritten_ofTm domain,
        spellWritten_ofTm codomain]
  | _, .id carrier left right => by
      simp only [ATm.ofTm, spellWritten, KTerm.ofTm, spellWritten_ofTm carrier,
        spellWritten_ofTm left, spellWritten_ofTm right]
  | _, .lam body => by
      simp only [ATm.ofTm, spellWritten, KTerm.ofTm, spellWritten_ofTm body]
  | _, .app function argument => by
      simp only [ATm.ofTm, spellWritten, KTerm.ofTm, spellWritten_ofTm function,
        spellWritten_ofTm argument]
  | _, .pair first second => by
      simp only [ATm.ofTm, spellWritten, KTerm.ofTm, spellWritten_ofTm first,
        spellWritten_ofTm second]
  | _, .fst package => by
      simp only [ATm.ofTm, spellWritten, KTerm.ofTm, spellWritten_ofTm package]
  | _, .snd package => by
      simp only [ATm.ofTm, spellWritten, KTerm.ofTm, spellWritten_ofTm package]
  | _, .refl term => by
      simp only [ATm.ofTm, spellWritten, KTerm.ofTm, spellWritten_ofTm term]

/-- Dropping the spelled domains gives the spelling of the erased term. -/
theorem ofTm_erase_of_spellWritten : ∀ {n : Nat} (term : ATm Tower.Head n) {spelled : KTerm},
    spellWritten term = some spelled →
      KTerm.ofTm term.erase = some (IdentityEquality.KernelSpelling.erase spelled)
  | _, .var _, spelled, equal => by
      simp only [spellWritten, Option.some.injEq] at equal
      subst equal
      rfl
  | _, .const name, spelled, equal => by
      simp only [spellWritten, Option.map_eq_some_iff] at equal
      obtain ⟨text, named, rfl⟩ := equal
      simp only [ATm.erase, KTerm.ofTm, named, Option.map_some]
      rfl
  | _, .head (.sort (.const level)), spelled, equal => by
      simp only [spellWritten, Option.some.injEq] at equal
      subst equal
      rfl
  | _, .head (.sort (.param _)), _, equal => by simp [spellWritten] at equal
  | _, .head (.sort (.succ _)), _, equal => by simp [spellWritten] at equal
  | _, .head (.sort (.max _ _)), _, equal => by simp [spellWritten] at equal
  | _, .head .legacyGround, _, equal => by simp [spellWritten] at equal
  | _, .pi domain codomain, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨d, dSpelled, c, cSpelled, rfl⟩ := equal
      simp only [ATm.erase, KTerm.ofTm, ofTm_erase_of_spellWritten domain dSpelled,
        ofTm_erase_of_spellWritten codomain cSpelled, bind, Option.bind_some, pure]
      rfl
  | _, .sigma domain codomain, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨d, dSpelled, c, cSpelled, rfl⟩ := equal
      simp only [ATm.erase, KTerm.ofTm, ofTm_erase_of_spellWritten domain dSpelled,
        ofTm_erase_of_spellWritten codomain cSpelled, bind, Option.bind_some, pure]
      rfl
  | _, .id carrier left right, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨c, cSpelled, l, lSpelled, r, rSpelled, rfl⟩ := equal
      simp only [ATm.erase, KTerm.ofTm, ofTm_erase_of_spellWritten carrier cSpelled,
        ofTm_erase_of_spellWritten left lSpelled, ofTm_erase_of_spellWritten right rSpelled,
        bind, Option.bind_some, pure]
      rfl
  | _, .lamBare body, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨b, bSpelled, rfl⟩ := equal
      simp only [ATm.erase, KTerm.ofTm, ofTm_erase_of_spellWritten body bSpelled, bind,
        Option.bind_some, pure]
      rfl
  | _, .lamTyped domain body, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨d, _, b, bSpelled, rfl⟩ := equal
      simp only [ATm.erase, KTerm.ofTm, ofTm_erase_of_spellWritten body bSpelled, bind,
        Option.bind_some, pure]
      rfl
  | _, .app function argument, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨f, fSpelled, a, aSpelled, rfl⟩ := equal
      simp only [ATm.erase, KTerm.ofTm, ofTm_erase_of_spellWritten function fSpelled,
        ofTm_erase_of_spellWritten argument aSpelled, bind, Option.bind_some, pure]
      rfl
  | _, .pair first second, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨f, fSpelled, s, sSpelled, rfl⟩ := equal
      simp only [ATm.erase, KTerm.ofTm, ofTm_erase_of_spellWritten first fSpelled,
        ofTm_erase_of_spellWritten second sSpelled, bind, Option.bind_some, pure]
      rfl
  | _, .fst package, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨p, pSpelled, rfl⟩ := equal
      simp only [ATm.erase, KTerm.ofTm, ofTm_erase_of_spellWritten package pSpelled, bind,
        Option.bind_some, pure]
      rfl
  | _, .snd package, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨p, pSpelled, rfl⟩ := equal
      simp only [ATm.erase, KTerm.ofTm, ofTm_erase_of_spellWritten package pSpelled, bind,
        Option.bind_some, pure]
      rfl
  | _, .refl term, spelled, equal => by
      simp only [spellWritten, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at equal
      obtain ⟨t, tSpelled, rfl⟩ := equal
      simp only [ATm.erase, KTerm.ofTm, ofTm_erase_of_spellWritten term tSpelled, bind,
        Option.bind_some, pure]
      rfl

end Spelling

/-! ## Judgments as the kernel receives them -/

section Judgments

/-- `λ(x₁ : A₁). … λ(xₖ : Aₖ). body` over the entries `A₁ … Aₖ` of a context, each entry
written as the domain of its λ. -/
def closeWritten : {n : Nat} → Tower.Ctx n → ATm Tower.Head n → ATm Tower.Head 0
  | _, .nil, body => body
  | _, .snoc Γ A, body => closeWritten Γ (.lamTyped (ATm.ofTm A) body)

/-- The judgment `Γ ⊢ t : T` as one closed term: the ascription `(λ(y : T). y) t` under the
λs of the context. -/
def judgmentWritten {n : Nat} (Γ : Tower.Ctx n) (term : ATm Tower.Head n) (type : Tower.Tm n) :
    ATm Tower.Head 0 :=
  closeWritten Γ (.app (.lamTyped (ATm.ofTm type) (.var 0)) term)

/-- The ascription of a typed term at its type is typed there. -/
theorem ascription_typed {n : Nat} {Γ : Tower.Ctx n} {term : ATm Tower.Head n}
    {type : Tower.Tm n} (formed : Typed objectRules Γ type U0)
    (typed : ATyped objectRules Γ term type) :
    ATyped objectRules Γ (.app (.lamTyped (ATm.ofTm type) (.var 0)) term) type := by
  have identity : ATyped objectRules Γ (.lamTyped (ATm.ofTm type) (.var 0))
      (.pi type (Presentation.rename wk type)) :=
    .lamTyped (ATyped.ofTyped formed) (.sort _)
      (by rw [ATm.erase_ofTm]; exact Derivable.refl formed)
      (piO formed formed.weaken) (.sort _) (.var 0)
  have applied := ATyped.appElim identity typed
  rw [inst0_rename_wk] at applied
  exact applied

end Judgments

/-! ## Examples -/

section Examples

/-- The type `holds (all@prop (λc. imp c c))`. -/
def selfImpType : Tower.Tm 0 :=
  programCodes.holdsOf (allPropOf (.lam (programCodes.impOf (.var 0) (.var 0))))

theorem selfImpType_formed : Typed objectRules .nil selfImpType U0 :=
  holdsO (allPropO (impO (.var 0) (.var 0)))

/-! ### `λc. S K K` -/

/-- `λ(c : prop). S K K`: the import of `S K K` at the atom `c`, with its domains written. -/
def selfImpWritten : ATm Tower.Head 0 :=
  .lamTyped (ATm.ofTm (.const propN))
    (IntDeriv.writtenProof (fun _ => (.var 0 : Tower.Tm 1))
      (PropDeriv.selfImp (cl := false) (Γ := []) (#0)))

/-- Its erasure is the closed proof of `selfImp_closed`. -/
theorem selfImpWritten_erase :
    selfImpWritten.erase = .lam (.app (.app sProof kProof) kProof) := rfl

theorem selfImpWritten_typed : ATyped objectRules .nil selfImpWritten selfImpType :=
  allIntroW (impO (.var 0) (.var 0))
    (IntDeriv.writtenProof_typed (Γ := .snoc .nil (.const propN)) (fun _ => .var 0)
      (Δ := []) (PropDeriv.selfImp (#0)))

/-- The spelled term. -/
def selfImpText : String :=
  "(Lam (DeclConst prop) (App (App (Lam (App (DeclConst \
    __cetta_holds_df87b3cd8ab4b6383b1d0591) (App (App (DeclConst imp) (idx 0)) (App (App \
    (DeclConst imp) (App (App (DeclConst imp) (idx 0)) (idx 0))) (idx 0)))) (Lam (App \
    (DeclConst __cetta_holds_df87b3cd8ab4b6383b1d0591) (App (App (DeclConst imp) (idx 1)) (App \
    (App (DeclConst imp) (idx 1)) (idx 1)))) (Lam (App (DeclConst \
    __cetta_holds_df87b3cd8ab4b6383b1d0591) (idx 2)) (App (App (idx 2) (idx 0)) (App (idx 1) \
    (idx 0)))))) (Lam (App (DeclConst __cetta_holds_df87b3cd8ab4b6383b1d0591) (idx 0)) (Lam \
    (App (DeclConst __cetta_holds_df87b3cd8ab4b6383b1d0591) (App (App (DeclConst imp) (idx 1)) \
    (idx 1))) (idx 1)))) (Lam (App (DeclConst __cetta_holds_df87b3cd8ab4b6383b1d0591) (idx 0)) \
    (Lam (App (DeclConst __cetta_holds_df87b3cd8ab4b6383b1d0591) (idx 1)) (idx 1)))))"

/-- The spelled type. -/
def selfImpTypeText : String :=
  "(App (DeclConst __cetta_holds_df87b3cd8ab4b6383b1d0591) (App (DeclConst all@prop) (Lam (App \
    (App (DeclConst imp) (idx 0)) (idx 0)))))"

#eval (spellWritten selfImpWritten).map KTerm.render
#eval (KTerm.ofTm selfImpType).map KTerm.render

set_option maxRecDepth 100000 in
/-- **The spelled `λc. S K K`**: its text, read back with its domains, and read back through
`KTerm.toTm` as the closed proof of `selfImp_closed`. -/
theorem selfImp_spelled : ∃ spelled : KTerm,
    spellWritten selfImpWritten = some spelled ∧ spelled.render = selfImpText ∧
      readWritten spelled = some selfImpWritten ∧
      spelled.toTmAt 0 = some (.lam (.app (.app sProof kProof) kProof)) := by
  refine ⟨_, rfl, by rfl, readWritten_spellWritten _ rfl, ?_⟩
  rw [← selfImpWritten_erase]
  exact toTm_spellWritten _ rfl

set_option maxRecDepth 100000 in
/-- **The spelled type** `holds (all@prop (λc. imp c c))`, read back as the type. -/
theorem selfImpType_spelled : ∃ spelled : KTerm,
    KTerm.ofTm selfImpType = some spelled ∧ spelled.render = selfImpTypeText ∧
      spelled.toTmAt 0 = some selfImpType :=
  ⟨_, rfl, by rfl, KTerm.toTm_ofTm _ rfl⟩

/-- The closed judgment submitted for `λc. S K K` is typed at its type. -/
theorem selfImpJudgment_typed :
    ATyped objectRules .nil (judgmentWritten .nil selfImpWritten selfImpType) selfImpType :=
  ascription_typed selfImpType_formed selfImpWritten_typed

/-! ### Barr's route: `p ⊃ p` by excluded middle -/

/-- The classical derivation `lemSelfImp` made intuitionistic by Theorem 62 and imported with
its atom bound, domains written. -/
def lemSelfImpWritten : ATm Tower.Head 0 :=
  .lamTyped (ATm.ofTm (.const propN))
    (IntDeriv.writtenProof (fun _ => (.var 0 : Tower.Tm 1))
      (theorem62OfClassical [] ⟨[0], [0]⟩ lemSelfImp))

theorem lemSelfImpWritten_erase :
    lemSelfImpWritten.erase =
      .lam (importGeometric (fun _ => (.var 0 : Tower.Tm 1)) [] ⟨[0], [0]⟩ lemSelfImp) :=
  congrArg Tm.lam (IntDeriv.writtenProof_erase (fun _ => (.var 0 : Tower.Tm 1))
    (theorem62OfClassical [] ⟨[0], [0]⟩ lemSelfImp))

theorem lemSelfImpWritten_typed : ATyped objectRules .nil lemSelfImpWritten selfImpType :=
  allIntroW (impO (.var 0) (.var 0))
    (IntDeriv.writtenProof_typed (Γ := .snoc .nil (.const propN)) (fun _ => .var 0)
      (theorem62OfClassical [] ⟨[0], [0]⟩ lemSelfImp))

/-- The closed judgment submitted for Barr's route is typed at its type. -/
theorem lemSelfImpJudgment_typed :
    ATyped objectRules .nil (judgmentWritten .nil lemSelfImpWritten selfImpType) selfImpType :=
  ascription_typed selfImpType_formed lemSelfImpWritten_typed

/-! ### The geometric example, in context -/

/-- The context of the four atoms `p₀ … p₃`, `p₀` outermost. -/
def exampleAtomCtx : Tower.Ctx 4 :=
  .snoc (.snoc (.snoc (.snoc .nil (.const propN)) (.const propN)) (.const propN)) (.const propN)

/-- The atom `pₐ` is the variable of its binder; the example has no other atoms. -/
def exampleAtoms : ℕ → Tower.Tm 4
  | 0 => .var 3
  | 1 => .var 2
  | 2 => .var 1
  | 3 => .var 0
  | _ => botCode

theorem exampleAtoms_typed :
    ∀ a, Typed objectRules exampleAtomCtx (exampleAtoms a) (.const propN)
  | 0 => .var 3
  | 1 => .var 2
  | 2 => .var 1
  | 3 => .var 0
  | _ + 4 => botCode_typed

/-- The assumptions `p₀ ⊃ p₁ ∨ p₂`, `p₁ ⊃ p₃`, `p₂ ⊃ p₃`. -/
abbrev exampleAssumptions : List (Propositional.Formula ℕ) :=
  exampleAxioms.map (GeoImp.toFormula .atom)

/-- The context of the example: the atoms, then the assumptions as proof variables. -/
def exampleCtx : Tower.Ctx (4 + exampleAssumptions.length) :=
  hypCtx exampleAtomCtx exampleAtoms exampleAssumptions

/-- The goal `holds (imp p₀ p₃)` in that context. -/
def exampleType : Tower.Tm (4 + exampleAssumptions.length) :=
  programCodes.holdsOf (programCodes.impOf (atomsPast exampleAtoms exampleAssumptions 0)
    (atomsPast exampleAtoms exampleAssumptions 3))

/-- The import of the example's classical derivation by Barr's route, domains written. -/
def exampleWritten : ATm Tower.Head (4 + exampleAssumptions.length) :=
  IntDeriv.writtenProof exampleAtoms
    (theorem62OfClassical exampleAxioms exampleGoal (PropDeriv.toCl exampleDerivation))

theorem exampleWritten_erase :
    exampleWritten.erase =
      importGeometric exampleAtoms exampleAxioms exampleGoal (PropDeriv.toCl exampleDerivation) :=
  IntDeriv.writtenProof_erase _ _

theorem exampleWritten_typed : ATyped objectRules exampleCtx exampleWritten exampleType :=
  IntDeriv.writtenProof_typed exampleAtoms_typed _

theorem exampleType_formed : Typed objectRules exampleCtx exampleType U0 :=
  holdsO (impO (atomsPast_typed exampleAtoms_typed _ 0) (atomsPast_typed exampleAtoms_typed _ 3))

/-- The ascription of the example at its goal is typed in the example's context; the query
closes that context with one written λ per entry. -/
theorem exampleAscription_typed :
    ATyped objectRules exampleCtx (.app (.lamTyped (ATm.ofTm exampleType) (.var 0)) exampleWritten)
      exampleType :=
  ascription_typed exampleType_formed exampleWritten_typed

/-- The number of nodes of a term with written domains. -/
def writtenSize {n : Nat} : ATm Tower.Head n → Nat
  | .var _ | .const _ | .head _ => 1
  | .pi A B | .sigma A B | .lamTyped A B => 1 + writtenSize A + writtenSize B
  | .pair A B | .app A B => 1 + writtenSize A + writtenSize B
  | .id A a b => 1 + writtenSize A + writtenSize a + writtenSize b
  | .lamBare b | .fst b | .snd b | .refl b => 1 + writtenSize b

/-- The sizes of the example: the import, and the import with its domains written. -/
def exampleSizes : Nat × Nat :=
  (writtenSize (ATm.ofTm exampleWritten.erase), writtenSize exampleWritten)

#eval exampleSizes

/-! ### Controls for the kernel -/

/-- `λc. S K K` with no domain written, as `KTerm.ofTm` spells it. -/
def selfImpBare : ATm Tower.Head 0 := ATm.ofTm (.lam (.app (.app sProof kProof) kProof))

/-- The bare term is typed as well: with no domain written, each λ takes its domain from its
type. -/
theorem selfImpBare_typed : ATyped objectRules .nil selfImpBare selfImpType :=
  ATyped.ofTyped selfImp_closed

/-- The type `holds (⊥ ⇒ ⊥)`, at which a control checks `λc. S K K`. -/
def botImpType : Tower.Tm 0 := programCodes.holdsOf (programCodes.impOf botCode botCode)

/-- The closed `λ(c : prop). K`, a proof of `all@prop (λc. imp c (imp c c))`. -/
def kClosedWritten : ATm Tower.Head 0 :=
  .lamTyped (ATm.ofTm (.const propN)) (kWritten (.var 0) (.var 0))

theorem kClosedWritten_typed : ATyped objectRules .nil kClosedWritten
    (programCodes.holdsOf (allPropOf (.lam
      (programCodes.impOf (.var 0) (programCodes.impOf (.var 0) (.var 0)))))) :=
  allIntroW (impO (.var 0) (impO (.var 0) (.var 0))) (kWritten_typed (.var 0) (.var 0))

/-- `λc. S K K` with the written domains of its first `K` replaced by those of the second. -/
def forgedWritten : ATm Tower.Head 0 :=
  .lamTyped (ATm.ofTm (.const propN))
    (.app (.app (sWritten (.var 0) (programCodes.impOf (.var 0) (.var 0)) (.var 0))
      (kWritten (.var 0) (.var 0))) (kWritten (.var 0) (.var 0)))

/-- The forged term erases to the same term: only a written domain differs. -/
theorem forgedWritten_erase : forgedWritten.erase = selfImpWritten.erase := rfl

/-! ### The kernel queries -/

/-- A judgment as the kernel receives it, spelled: the body of a consumer `(Lam P body)` of a
checked native proof package, `P` the package's type. -/
def queryText {n : Nat} (Γ : Tower.Ctx n) (term : ATm Tower.Head n) (type : Tower.Tm n) :
    Option String :=
  (spellWritten (judgmentWritten Γ term type)).map KTerm.render

/-- A closed judgment is spelled as the ascription `(App (Lam type (idx 0)) term)` of the
spelled term at the spelled type. -/
theorem judgmentWritten_nil_spelled {term : ATm Tower.Head 0} {type : Tower.Tm 0}
    {spelledTerm spelledType : KTerm} (hterm : spellWritten term = some spelledTerm)
    (htype : KTerm.ofTm type = some spelledType) :
    spellWritten (judgmentWritten .nil term type) =
      some (.app (.lamTyped spelledType (.idx 0)) spelledTerm) := by
  simp only [judgmentWritten, closeWritten, spellWritten, spellWritten_ofTm, htype, hterm, bind,
    Option.bind_some, pure]
  rfl

/-- The spelled terms of the controls and of Barr's route. -/
def termText {n : Nat} (term : ATm Tower.Head n) : Option String :=
  (spellWritten term).map KTerm.render

/-- The spelled types of the controls. -/
def typeText {n : Nat} (type : Tower.Tm n) : Option String := (KTerm.ofTm type).map KTerm.render

#eval termText lemSelfImpWritten
#eval termText selfImpBare
#eval typeText botImpType
#eval termText kClosedWritten
#eval termText forgedWritten

-- The length of the spelled query of the geometric example, in context.
#eval (queryText exampleCtx exampleWritten exampleType).map String.length

end Examples

/-! ## Axiom audit -/

#print axioms nameText_allProp
#print axioms IntDeriv.writtenProof_erase
#print axioms IntDeriv.writtenProof_typed
#print axioms readWritten_spellWritten
#print axioms toTm_spellWritten
#print axioms spellWritten_ofTm
#print axioms ofTm_erase_of_spellWritten
#print axioms ascription_typed
#print axioms selfImpWritten_typed
#print axioms selfImp_spelled
#print axioms selfImpType_spelled
#print axioms lemSelfImpWritten_typed
#print axioms exampleWritten_typed
#print axioms selfImpBare_typed
#print axioms kClosedWritten_typed
#print axioms forgedWritten_erase
#print axioms judgmentWritten_nil_spelled
#print axioms selfImpJudgment_typed
#print axioms lemSelfImpJudgment_typed
#print axioms exampleAscription_typed

end CodeModel

end CertifiedTransformProgram.ExecutableModel
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
