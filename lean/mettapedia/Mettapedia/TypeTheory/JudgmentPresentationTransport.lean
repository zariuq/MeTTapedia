import Mettapedia.TypeTheory.JudgmentEquationInitiality

/-!
# Composing translations of presented dependent judgments

Rule translations retain the explicit change of judgment and dependent
premise positions. Their proof translations compose and commute with model
interpretation. Respecting the generating equations gives a well-defined
map on presented proofs, with an exact model readout. Premise preservation
is an additional condition: an unrestricted map may omit source premises.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.JudgmentPresentationTransport

open JudgmentDerivation JudgmentEquationInitiality

universe u v
variable {S T U : Signature.{u}}

def identity (S : Signature.{u}) : SignatureMap S S where
  judgment := id
  rule := id
  position _ := id
  hypothesis _ _ := rfl

def comp (F : SignatureMap S T) (G : SignatureMap T U) : SignatureMap S U where
  judgment j := G.judgment (F.judgment j)
  rule r := G.rule (F.rule r)
  position r p := F.position r (G.position (F.rule r) p)
  hypothesis r p := (congrArg G.judgment
    (F.hypothesis r (G.position (F.rule r) p))).trans (G.hypothesis (F.rule r) p)

theorem translate_cast (F : SignatureMap S T) {j k : S.Judgment} (same : j = k)
    (d : Derivation S j) :
    F.translate (cast (congrArg (Derivation S) same) d) =
      cast (congrArg (fun j => Derivation T (F.judgment j)) same) (F.translate d) := by
  cases same
  rfl

@[simp] theorem translate_identity {j : S.Judgment} (d : Derivation S j) :
    (identity S).translate d = d := by
  induction d with
  | node r premises ih =>
      change Derivation.node r (fun p => (identity S).translate (premises p)) =
        Derivation.node r premises
      congr 1
      funext p
      exact ih p

/-- The equation includes the canonical changes of dependent premise
judgment; equality of the supplied equality proofs is not an extra axiom. -/
theorem translate_comp (F : SignatureMap S T) (G : SignatureMap T U)
    {j : S.Judgment} (d : Derivation S j) :
    G.translate (F.translate d) = (comp F G).translate d := by
  induction d with
  | node r premises ih =>
      change Derivation.node (G.rule (F.rule r))
          (fun p => cast (congrArg (Derivation U) (G.hypothesis (F.rule r) p))
            (G.translate (cast
              (congrArg (Derivation T) (F.hypothesis r (G.position (F.rule r) p)))
              (F.translate (premises (F.position r (G.position (F.rule r) p))))))) =
        Derivation.node (G.rule (F.rule r))
          (fun p => cast (congrArg (Derivation U) ((comp F G).hypothesis r p))
            ((comp F G).translate (premises ((comp F G).position r p))))
      congr 1
      funext p
      rw [translate_cast G (F.hypothesis r (G.position (F.rule r) p)),
        cast_cast, ih (F.position r (G.position (F.rule r) p))]
      rfl

theorem congruence_cast (E : Equations T) {j k : T.Judgment} (same : j = k)
    {left right : Derivation T j} (related : Congruence E left right) :
    Congruence E (cast (congrArg (Derivation T) same) left)
      (cast (congrArg (Derivation T) same) right) := by
  cases same
  exact related

def Respects (F : SignatureMap S T) (source : Equations S) (target : Equations T) : Prop :=
  ∀ {j : S.Judgment} {left right : Derivation S j}, source left right →
    Congruence target (F.translate left) (F.translate right)

theorem translate_congruence (F : SignatureMap S T) (source : Equations S)
    (target : Equations T) (laws : Respects F source target)
    {j : S.Judgment} {left right : Derivation S j}
    (related : Congruence source left right) :
    Congruence target (F.translate left) (F.translate right) := by
  induction related with
  | equation imposed => exact laws imposed
  | refl d => exact Congruence.refl _
  | symm _ ih => exact Congruence.symm ih
  | trans _ _ first second => exact Congruence.trans first second
  | node r left right _ ih =>
      change Congruence target
        (.node (F.rule r) (fun p => cast
          (congrArg (Derivation T) (F.hypothesis r p)) (F.translate (left (F.position r p)))))
        (.node (F.rule r) (fun p => cast
          (congrArg (Derivation T) (F.hypothesis r p)) (F.translate (right (F.position r p)))))
      apply Congruence.node
      intro p
      exact congruence_cast target (F.hypothesis r p) (ih (F.position r p))

def quotientMap (F : SignatureMap S T) (source : Equations S) (target : Equations T)
    (laws : Respects F source target) {j : S.Judgment} :
    Presented source j → Presented target (F.judgment j) :=
  Quotient.lift (fun d => Quotient.mk _ (F.translate d))
    (fun _ _ related => Quotient.sound (translate_congruence F source target laws related))

@[simp] theorem quotientMap_mk (F : SignatureMap S T) (source : Equations S)
    (target : Equations T) (laws : Respects F source target)
    {j : S.Judgment} (d : Derivation S j) :
    quotientMap F source target laws (Quotient.mk _ d) = Quotient.mk _ (F.translate d) := rfl

/-- Qualification concerns only equation generators. Soundness for every
presented proof follows from the generated congruence. -/
theorem pullback_satisfies (F : SignatureMap S T) (source : Equations S)
    (target : Equations T) (laws : Respects F source target)
    (A : Algebra.{u, v} T) (valid : Satisfies target A) :
    Satisfies source (F.pullback A) := by
  intro j left right imposed
  rw [← SignatureMap.interpret_translate, ← SignatureMap.interpret_translate]
  exact interpretation_respects_congruence target A valid (laws imposed)

theorem evaluate_quotientMap (F : SignatureMap S T) (source : Equations S)
    (target : Equations T) (laws : Respects F source target)
    (A : Algebra.{u, v} T) (valid : Satisfies target A)
    {j : S.Judgment} (proof : Presented source j) :
    evaluate target A valid (quotientMap F source target laws proof) =
      evaluate source (F.pullback A) (pullback_satisfies F source target laws A valid) proof := by
  induction proof using Quotient.inductionOn with
  | h d => exact SignatureMap.interpret_translate F A d

theorem respects_comp (F : SignatureMap S T) (G : SignatureMap T U)
    (source : Equations S) (middle : Equations T) (target : Equations U)
    (first : Respects F source middle) (second : Respects G middle target) :
    Respects (comp F G) source target := by
  intro j left right imposed
  rw [← translate_comp, ← translate_comp]
  exact translate_congruence G middle target second (first imposed)

theorem quotientMap_comp (F : SignatureMap S T) (G : SignatureMap T U)
    (source : Equations S) (middle : Equations T) (target : Equations U)
    (first : Respects F source middle) (second : Respects G middle target)
    {j : S.Judgment} (proof : Presented source j) :
    quotientMap G middle target second (quotientMap F source middle first proof) =
      quotientMap (comp F G) source target (respects_comp F G source middle target first second) proof := by
  induction proof using Quotient.inductionOn with
  | h d => exact congrArg (Quotient.mk _) (translate_comp F G d)

end Mettapedia.TypeTheory.JudgmentPresentationTransport
