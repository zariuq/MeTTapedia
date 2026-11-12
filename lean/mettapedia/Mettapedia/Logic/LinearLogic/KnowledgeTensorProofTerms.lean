import Mathlib.Algebra.Order.Group.Multiset
import Mettapedia.Logic.LinearLogic.KnowledgeTensor

/-!
# Proof terms of the two-zone calculus, and their structural quotient

The proofs of the two-zone calculus are here data: terms built from the identity, a leaf for each
use of a declaration, the frame rule of the linear zone, the frame rule of the knowledge zone,
and cut. A typing judgment says which sequent a term proves.

The **structural equations** are the laws of composition and of the two frame actions: cut is
associative with the identity as unit; framing by nothing is nothing, framing twice is framing by
the sum, and framing commutes with cut and fixes the identity; strengthening commutes with cut
and with framing, fixes the identity, and is absorbed by a leaf.

## Results

* `typed_iff_run`: a term with a given readout proves a sequent exactly when the run with that
  word exists.
* `Typed.normalize`: every typed term is equal, modulo the structural equations, to the
  sequential normal form of its readout: a cut of framed leaves.
* `eqv_iff_readout`: **two proofs from one source are equal modulo the structural equations
  exactly when they have the same readout.** So the proofs of the calculus modulo its structural
  equations are the runs: composition and the two frame actions are free on the declarations.
* `swap_is_not_structural`: exchanging two different leaves is not a structural equation. The
  interchange of independent uses is a further equation, and the quotient by it is the trace
  quotient.

The normal form computes the residual frame of each use by subtraction, so the atoms have
decidable equality here.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LinearLogic.KnowledgeTensor

universe uK uAtom uRule

/-- Proof terms of the two-zone calculus. -/
inductive ProofTerm (K : Type uK) (Atom : Type uAtom) (Rule : Type uRule) :
    Type (max uK uAtom uRule)
  | identity : ProofTerm K Atom Rule
  | rule (declaration : Rule) : ProofTerm K Atom Rule
  | frame (extra : Multiset Atom) (inner : ProofTerm K Atom Rule) : ProofTerm K Atom Rule
  | strengthen (more : K) (inner : ProofTerm K Atom Rule) : ProofTerm K Atom Rule
  | cut (first second : ProofTerm K Atom Rule) : ProofTerm K Atom Rule

namespace ProofTerm

variable {K : Type uK} {Atom : Type uAtom} {Rule : Type uRule}

/-- The left-to-right readout of the leaves of a term. -/
def readout : ProofTerm K Atom Rule → List Rule
  | .identity => []
  | .rule declaration => [declaration]
  | .frame _ inner => inner.readout
  | .strengthen _ inner => inner.readout
  | .cut first second => first.readout ++ second.readout

/-- The structural equations of proof terms: the laws of composition and of the two frame
actions. -/
inductive Eqv : ProofTerm K Atom Rule → ProofTerm K Atom Rule → Prop
  | refl (p : ProofTerm K Atom Rule) : Eqv p p
  | symm {p q : ProofTerm K Atom Rule} : Eqv p q → Eqv q p
  | trans {p q r : ProofTerm K Atom Rule} : Eqv p q → Eqv q r → Eqv p r
  | frame {p q : ProofTerm K Atom Rule} (extra : Multiset Atom) :
      Eqv p q → Eqv (.frame extra p) (.frame extra q)
  | strengthen {p q : ProofTerm K Atom Rule} (more : K) :
      Eqv p q → Eqv (.strengthen more p) (.strengthen more q)
  | cut {p p' q q' : ProofTerm K Atom Rule} : Eqv p p' → Eqv q q' → Eqv (.cut p q) (.cut p' q')
  | cut_assoc (p q r : ProofTerm K Atom Rule) : Eqv (.cut (.cut p q) r) (.cut p (.cut q r))
  | identity_cut (p : ProofTerm K Atom Rule) : Eqv (.cut .identity p) p
  | cut_identity (p : ProofTerm K Atom Rule) : Eqv (.cut p .identity) p
  | frame_zero (p : ProofTerm K Atom Rule) : Eqv (.frame 0 p) p
  | frame_frame (first second : Multiset Atom) (p : ProofTerm K Atom Rule) :
      Eqv (.frame second (.frame first p)) (.frame (first + second) p)
  | frame_cut (extra : Multiset Atom) (p q : ProofTerm K Atom Rule) :
      Eqv (.frame extra (.cut p q)) (.cut (.frame extra p) (.frame extra q))
  | frame_identity (extra : Multiset Atom) : Eqv (.frame extra .identity) .identity
  | strengthen_rule (more : K) (declaration : Rule) :
      Eqv (.strengthen more (.rule declaration)) (.rule declaration)
  | strengthen_identity (more : K) : Eqv (.strengthen more .identity) .identity
  | strengthen_cut (more : K) (p q : ProofTerm K Atom Rule) :
      Eqv (.strengthen more (.cut p q)) (.cut (.strengthen more p) (.strengthen more q))
  | strengthen_frame (more : K) (extra : Multiset Atom) (p : ProofTerm K Atom Rule) :
      Eqv (.strengthen more (.frame extra p)) (.frame extra (.strengthen more p))

/-- **The structural equations keep the readout.** -/
theorem Eqv.readout_eq {p q : ProofTerm K Atom Rule} (same : Eqv p q) : p.readout = q.readout := by
  induction same with
  | refl p => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond
  | frame extra _ ih => exact ih
  | strengthen more _ ih => exact ih
  | cut _ _ ihFirst ihSecond =>
      show _ ++ _ = _ ++ _
      rw [ihFirst, ihSecond]
  | cut_assoc p q r => exact List.append_assoc _ _ _
  | identity_cut p => rfl
  | cut_identity p => exact List.append_nil _
  | frame_zero p => rfl
  | frame_frame first second p => rfl
  | frame_cut extra p q => rfl
  | frame_identity extra => rfl
  | strengthen_rule more declaration => rfl
  | strengthen_identity more => rfl
  | strengthen_cut more p q => rfl
  | strengthen_frame more extra p => rfl

/-- Terms with different readouts are not equal modulo the structural equations. -/
theorem not_eqv_of_readout_ne {p q : ProofTerm K Atom Rule} (different : p.readout ≠ q.readout) :
    ¬ Eqv p q :=
  fun same => different same.readout_eq

/-- **Exchanging two different leaves is not a structural equation.** -/
theorem swap_is_not_structural {first second : Rule} (different : first ≠ second) :
    ¬ Eqv (.cut (.rule first) (.rule second) : ProofTerm K Atom Rule)
      (.cut (.rule second) (.rule first)) :=
  not_eqv_of_readout_ne fun same => different (List.cons.inj same).1

end ProofTerm

namespace System

open ProofTerm

variable {K : Type uK} {Atom : Type uAtom} {Rule : Type uRule} [SemilatticeInf K]
  (sys : System K Atom Rule)

/-- The sequent a term proves. -/
inductive Typed : ProofTerm K Atom Rule → K → Multiset Atom → K → Multiset Atom → Prop
  | identity (k : K) (Γ : Multiset Atom) : Typed .identity k Γ k Γ
  | rule (declaration : Rule) (k : K) (asked : sys.guard declaration (k ⊓ sys.tell declaration)) :
      Typed (.rule declaration) k (sys.premises declaration) (k ⊓ sys.tell declaration)
        (sys.conclusions declaration)
  | frame {p : ProofTerm K Atom Rule} {k k' : K} {Γ Γ' : Multiset Atom} (extra : Multiset Atom) :
      Typed p k Γ k' Γ' → Typed (.frame extra p) k (Γ + extra) k' (Γ' + extra)
  | strengthen {p : ProofTerm K Atom Rule} {k k' : K} {Γ Γ' : Multiset Atom} (more : K) :
      Typed p k Γ k' Γ' → Typed (.strengthen more p) (k ⊓ more) Γ (k' ⊓ more) Γ'
  | cut {p q : ProofTerm K Atom Rule} {k k₁ k' : K} {Γ Γ₁ Γ' : Multiset Atom} :
      Typed p k Γ k₁ Γ₁ → Typed q k₁ Γ₁ k' Γ' → Typed (.cut p q) k Γ k' Γ'

variable {sys}

/-- A typed term is a proof with its readout. -/
theorem Typed.derives {p : ProofTerm K Atom Rule} {k k' : K} {Γ Γ' : Multiset Atom}
    (typed : sys.Typed p k Γ k' Γ') : sys.Derives k Γ p.readout k' Γ' := by
  induction typed with
  | identity k Γ => exact Derives.identity k Γ
  | rule declaration k asked => exact Derives.rule declaration k asked
  | frame extra _ ih => exact Derives.frame extra ih
  | strengthen more _ ih => exact Derives.strengthen more ih
  | cut _ _ ihFirst ihSecond => exact Derives.cut ihFirst ihSecond

/-- A proof is the readout of a typed term. -/
theorem Derives.typed {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule}
    (proof : sys.Derives k Γ uses k' Γ') :
    ∃ p : ProofTerm K Atom Rule, sys.Typed p k Γ k' Γ' ∧ p.readout = uses := by
  induction proof with
  | identity k Γ => exact ⟨.identity, Typed.identity k Γ, rfl⟩
  | rule declaration k asked => exact ⟨.rule declaration, Typed.rule declaration k asked, rfl⟩
  | frame extra _ ih =>
      obtain ⟨p, typed, same⟩ := ih
      exact ⟨.frame extra p, Typed.frame extra typed, same⟩
  | strengthen more _ ih =>
      obtain ⟨p, typed, same⟩ := ih
      exact ⟨.strengthen more p, Typed.strengthen more typed, same⟩
  | cut _ _ ihFirst ihSecond =>
      obtain ⟨p, typedFirst, sameFirst⟩ := ihFirst
      obtain ⟨q, typedSecond, sameSecond⟩ := ihSecond
      exact ⟨.cut p q, Typed.cut typedFirst typedSecond, by
        show p.readout ++ q.readout = _
        rw [sameFirst, sameSecond]⟩

/-- **Typed terms with a given readout exist exactly where the run exists.** -/
theorem typed_iff_run (k k' : K) (Γ Γ' : Multiset Atom) (uses : List Rule) :
    (∃ p : ProofTerm K Atom Rule, sys.Typed p k Γ k' Γ' ∧ p.readout = uses) ↔
      sys.Run k Γ uses k' Γ' := by
  constructor
  · rintro ⟨p, typed, rfl⟩
    exact Derives.run typed.derives
  · intro run
    exact Derives.typed (Run.derives run)

variable [DecidableEq Atom] (sys)

/-- The sequential normal form of a word from a multiset of atoms: a cut of leaves, each framed
by what the use leaves untouched. -/
def normal : Multiset Atom → List Rule → ProofTerm K Atom Rule
  | _, [] => .identity
  | Γ, declaration :: rest =>
      .cut (.frame (Γ - sys.premises declaration) (.rule declaration))
        (normal (sys.conclusions declaration + (Γ - sys.premises declaration)) rest)

/-- The atoms a word leaves. -/
def after : Multiset Atom → List Rule → Multiset Atom
  | Γ, [] => Γ
  | Γ, declaration :: rest =>
      after (sys.conclusions declaration + (Γ - sys.premises declaration)) rest

/-- Each use of a word finds its premises. -/
def Fits : Multiset Atom → List Rule → Prop
  | _, [] => True
  | Γ, declaration :: rest => sys.premises declaration ≤ Γ ∧
      Fits (sys.conclusions declaration + (Γ - sys.premises declaration)) rest

variable {sys}

/-- A run finds the premises of every use, and leaves the atoms the word leaves. -/
theorem Run.fits {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule}
    (run : sys.Run k Γ uses k' Γ') : sys.Fits Γ uses ∧ sys.after Γ uses = Γ' := by
  induction run with
  | done k Γ => exact ⟨trivial, rfl⟩
  | @fire declaration k k₁ k' Γ Γ₁ Γ' rest fires later ih =>
      obtain ⟨frame, source, _, _, target⟩ := fires
      subst source
      subst target
      have cancel : sys.premises declaration + frame - sys.premises declaration = frame :=
        add_tsub_cancel_left _ _
      show (sys.premises declaration ≤ sys.premises declaration + frame ∧
          sys.Fits (sys.conclusions declaration +
            (sys.premises declaration + frame - sys.premises declaration)) rest) ∧
        sys.after (sys.conclusions declaration +
          (sys.premises declaration + frame - sys.premises declaration)) rest = Γ'
      rw [cancel]
      exact ⟨⟨Multiset.le_add_right _ _, ih.1⟩, ih.2⟩

/-- Framing a normal form is the normal form from the framed atoms. -/
theorem eqv_frame_normal : ∀ (word : List Rule) (Γ extra : Multiset Atom), sys.Fits Γ word →
    Eqv (.frame extra (sys.normal Γ word)) (sys.normal (Γ + extra) word)
  | [], _, extra, _ => Eqv.frame_identity extra
  | declaration :: rest, Γ, extra, fits => by
      have ih := eqv_frame_normal rest
      obtain ⟨untouched, rfl⟩ := Multiset.le_iff_exists_add.mp fits.1
      have here : sys.premises declaration + untouched - sys.premises declaration = untouched :=
        add_tsub_cancel_left _ _
      have there : sys.premises declaration + untouched + extra - sys.premises declaration =
          untouched + extra := by
        rw [add_assoc]
        exact add_tsub_cancel_left _ _
      have tail : sys.Fits (sys.conclusions declaration +
          (sys.premises declaration + untouched - sys.premises declaration)) rest := fits.2
      rw [here] at tail
      show Eqv (.frame extra (.cut
          (.frame (sys.premises declaration + untouched - sys.premises declaration)
            (.rule declaration))
          (sys.normal (sys.conclusions declaration +
            (sys.premises declaration + untouched - sys.premises declaration)) rest)))
        (.cut (.frame (sys.premises declaration + untouched + extra - sys.premises declaration)
            (.rule declaration))
          (sys.normal (sys.conclusions declaration +
            (sys.premises declaration + untouched + extra - sys.premises declaration)) rest))
      rw [here, there, ← add_assoc]
      exact .trans (.frame_cut extra _ _)
        (.cut (.frame_frame untouched extra _) (ih _ extra tail))

/-- Strengthening a normal form changes nothing. -/
theorem eqv_strengthen_normal : ∀ (word : List Rule) (Γ : Multiset Atom) (more : K),
    Eqv (.strengthen more (sys.normal Γ word)) (sys.normal Γ word)
  | [], _, more => Eqv.strengthen_identity more
  | declaration :: rest, _, more =>
      .trans (.strengthen_cut more _ _)
        (.cut (.trans (.strengthen_frame more _ _) (.frame _ (.strengthen_rule more declaration)))
          (eqv_strengthen_normal rest _ more))

/-- The cut of two normal forms is the normal form of the concatenated word. -/
theorem eqv_cut_normal : ∀ (first : List Rule) (Γ : Multiset Atom) (second : List Rule),
    Eqv (.cut (sys.normal Γ first) (sys.normal (sys.after Γ first) second))
      (sys.normal Γ (first ++ second))
  | [], _, _ => Eqv.identity_cut _
  | _ :: rest, _, second =>
      .trans (.cut_assoc _ _ _) (.cut (.refl _) (eqv_cut_normal rest _ second))

/-- **Every proof is, modulo the structural equations, the sequential normal form of its
readout.** -/
theorem Typed.normalize {p : ProofTerm K Atom Rule} {k k' : K} {Γ Γ' : Multiset Atom}
    (typed : sys.Typed p k Γ k' Γ') : Eqv p (sys.normal Γ p.readout) := by
  induction typed with
  | identity k Γ => exact .refl _
  | rule declaration k asked =>
      show Eqv (.rule declaration)
        (.cut (.frame (sys.premises declaration - sys.premises declaration) (.rule declaration))
          .identity)
      have nothing : sys.premises declaration - sys.premises declaration = 0 := by
        have cancel := add_tsub_cancel_left (sys.premises declaration) (0 : Multiset Atom)
        rw [add_zero] at cancel
        exact cancel
      rw [nothing]
      exact .symm (.trans (.cut_identity _) (.frame_zero _))
  | @frame p k k' Γ Γ' extra inner ih =>
      exact .trans (.frame extra ih)
        (eqv_frame_normal p.readout Γ extra (Run.fits (Derives.run inner.derives)).1)
  | @strengthen p k k' Γ Γ' more inner ih =>
      exact .trans (.strengthen more ih) (eqv_strengthen_normal p.readout Γ more)
  | @cut p q k k₁ k' Γ Γ₁ Γ' first second ihFirst ihSecond =>
      have ends : sys.after Γ p.readout = Γ₁ := (Run.fits (Derives.run first.derives)).2
      have joined := eqv_cut_normal (sys := sys) p.readout Γ q.readout
      rw [ends] at joined
      exact .trans (.cut ihFirst ihSecond) joined

/-- **Proofs modulo the structural equations are runs.** Two proofs from one source are equal
modulo the structural equations exactly when they have the same readout. -/
theorem eqv_iff_readout {p q : ProofTerm K Atom Rule} {k k' j' : K} {Γ Γ' Δ' : Multiset Atom}
    (first : sys.Typed p k Γ k' Γ') (second : sys.Typed q k Γ j' Δ') :
    Eqv p q ↔ p.readout = q.readout := by
  constructor
  · exact Eqv.readout_eq
  · intro same
    have normalFirst := first.normalize
    have normalSecond := second.normalize
    rw [same] at normalFirst
    exact .trans normalFirst (.symm normalSecond)

end System

end Mettapedia.Logic.LinearLogic.KnowledgeTensor
