import Mathlib.Algebra.FreeMonoid.Basic
import Mettapedia.Logic.LinearLogic.KnowledgeTensorProofTerms

/-!
# Proofs modulo the structural equations are free on the declarations

The structural equations of proof terms are the laws of composition and of the two frame actions.
This module says what their quotient is, with no typing hypothesis.

* `ProofTerm.leaves`: the uses of a term, each with the atoms framed around it.
* `ProofTerm.eqv_iff_leaves`: **two terms are equal modulo the structural equations exactly when
  they have the same framed uses.** The quotient is the lists of framed uses.
* `FrameMonoid`: a monoid on which frames act by endomorphisms. `ProofTerm.eval` interprets a
  term in one, given an interpretation of the declarations.
* `ProofTerm.eqv_iff_every_frameMonoid`: the structural equations are exactly the equations that
  hold in every such interpretation.
* `extend_exists_unique`: **the lists of framed uses are the free monoid with a frame action on
  the declarations**: an interpretation of the declarations extends in exactly one way to a
  homomorphism that commutes with framing.
* `ProofTerm.frame_rule_not_eqv_rule`: a framed use is not the use. Two proofs with one readout
  from different sources are different.

Composition and the two frame actions are free. The exchange of two uses is not among the
structural equations (`ProofTerm.swap_is_not_structural`): it is a further equation, and it is
not sound for every pair of uses.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LinearLogic.KnowledgeTensor

universe uK uAtom uRule uM

/-- A use of a declaration with the atoms framed around it. -/
abbrev FramedUse (Atom : Type uAtom) (Rule : Type uRule) : Type (max uAtom uRule) :=
  Multiset Atom × Rule

namespace FramedUse

variable {Atom : Type uAtom} {Rule : Type uRule}

/-- Framing a use by more atoms. -/
def frame (extra : Multiset Atom) (leaf : FramedUse Atom Rule) : FramedUse Atom Rule :=
  (leaf.1 + extra, leaf.2)

theorem frame_zero (leaf : FramedUse Atom Rule) : frame 0 leaf = leaf :=
  Prod.ext (add_zero leaf.1) rfl

theorem frame_frame (first second : Multiset Atom) (leaf : FramedUse Atom Rule) :
    frame second (frame first leaf) = frame (first + second) leaf :=
  Prod.ext (add_assoc leaf.1 first second) rfl

theorem frame_start (leaf : FramedUse Atom Rule) : frame leaf.1 (0, leaf.2) = leaf :=
  Prod.ext (zero_add leaf.1) rfl

theorem map_frame_zero :
    FreeMonoid.map (frame (0 : Multiset Atom) : FramedUse Atom Rule → FramedUse Atom Rule) =
      MonoidHom.id (FreeMonoid (FramedUse Atom Rule)) :=
  FreeMonoid.hom_eq fun leaf => congrArg FreeMonoid.of (frame_zero leaf)

theorem map_frame_frame (first second : Multiset Atom) :
    (FreeMonoid.map (frame second)).comp
        (FreeMonoid.map (frame first : FramedUse Atom Rule → FramedUse Atom Rule)) =
      FreeMonoid.map (frame (first + second)) :=
  FreeMonoid.hom_eq fun leaf => congrArg FreeMonoid.of (frame_frame first second leaf)

end FramedUse

namespace ProofTerm

variable {K : Type uK} {Atom : Type uAtom} {Rule : Type uRule}

/-- The uses of a term, left to right, each with the atoms framed around it. -/
def leaves : ProofTerm K Atom Rule → List (FramedUse Atom Rule)
  | .identity => []
  | .rule declaration => [(0, declaration)]
  | .frame extra inner => inner.leaves.map (FramedUse.frame extra)
  | .strengthen _ inner => inner.leaves
  | .cut first second => first.leaves ++ second.leaves

/-- The sequential term of a list of framed uses. -/
def ofLeaves : List (FramedUse Atom Rule) → ProofTerm K Atom Rule
  | [] => .identity
  | leaf :: rest => .cut (.frame leaf.1 (.rule leaf.2)) (ofLeaves rest)

/-- The readout forgets the frames of the framed uses. -/
theorem readout_eq_leaves : ∀ p : ProofTerm K Atom Rule, p.readout = p.leaves.map Prod.snd
  | .identity => rfl
  | .rule _ => rfl
  | .frame extra inner => by
      show inner.readout = List.map Prod.snd (List.map (FramedUse.frame extra) inner.leaves)
      rw [List.map_map, readout_eq_leaves inner]
      exact List.map_congr_left fun _ _ => rfl
  | .strengthen _ inner => readout_eq_leaves inner
  | .cut first second => by
      show first.readout ++ second.readout =
        List.map Prod.snd (first.leaves ++ second.leaves)
      rw [List.map_append, readout_eq_leaves first, readout_eq_leaves second]

/-- **The structural equations keep the framed uses.** -/
theorem Eqv.leaves_eq {p q : ProofTerm K Atom Rule} (same : Eqv p q) : p.leaves = q.leaves := by
  induction same with
  | refl p => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond
  | frame extra _ ih =>
      show List.map _ _ = List.map _ _
      rw [ih]
  | strengthen more _ ih => exact ih
  | cut _ _ ihFirst ihSecond =>
      show _ ++ _ = _ ++ _
      rw [ihFirst, ihSecond]
  | cut_assoc p q r => exact List.append_assoc _ _ _
  | identity_cut p => rfl
  | cut_identity p => exact List.append_nil _
  | frame_zero p =>
      have same : (FramedUse.frame (0 : Multiset Atom) :
          FramedUse Atom Rule → FramedUse Atom Rule) = id := funext FramedUse.frame_zero
      show List.map (FramedUse.frame 0) p.leaves = p.leaves
      rw [same, List.map_id]
  | frame_frame first second p =>
      show List.map (FramedUse.frame second) (List.map (FramedUse.frame first) p.leaves) =
        List.map (FramedUse.frame (first + second)) p.leaves
      rw [List.map_map]
      exact List.map_congr_left fun leaf _ => FramedUse.frame_frame first second leaf
  | frame_cut extra p q =>
      show List.map (FramedUse.frame extra) (p.leaves ++ q.leaves) =
        List.map (FramedUse.frame extra) p.leaves ++ List.map (FramedUse.frame extra) q.leaves
      rw [List.map_append]
  | frame_identity extra => rfl
  | strengthen_rule more declaration => rfl
  | strengthen_identity more => rfl
  | strengthen_cut more p q => rfl
  | strengthen_frame more extra p => rfl

theorem leaves_ofLeaves : ∀ framed : List (FramedUse Atom Rule),
    (ofLeaves framed : ProofTerm K Atom Rule).leaves = framed
  | [] => rfl
  | leaf :: rest => by
      show FramedUse.frame leaf.1 (0, leaf.2) ::
        (ofLeaves rest : ProofTerm K Atom Rule).leaves = leaf :: rest
      rw [leaves_ofLeaves rest, FramedUse.frame_start]

theorem eqv_frame_ofLeaves (extra : Multiset Atom) : ∀ framed : List (FramedUse Atom Rule),
    Eqv (.frame extra (ofLeaves framed) : ProofTerm K Atom Rule)
      (ofLeaves (framed.map (FramedUse.frame extra)))
  | [] => Eqv.frame_identity extra
  | leaf :: rest =>
      .trans (.frame_cut extra _ _)
        (.cut (.frame_frame leaf.1 extra _) (eqv_frame_ofLeaves extra rest))

theorem eqv_strengthen_ofLeaves (more : K) : ∀ framed : List (FramedUse Atom Rule),
    Eqv (.strengthen more (ofLeaves framed) : ProofTerm K Atom Rule) (ofLeaves framed)
  | [] => Eqv.strengthen_identity more
  | leaf :: rest =>
      .trans (.strengthen_cut more _ _)
        (.cut (.trans (.strengthen_frame more _ _) (.frame _ (.strengthen_rule more leaf.2)))
          (eqv_strengthen_ofLeaves more rest))

theorem eqv_cut_ofLeaves : ∀ first second : List (FramedUse Atom Rule),
    Eqv (.cut (ofLeaves first) (ofLeaves second) : ProofTerm K Atom Rule)
      (ofLeaves (first ++ second))
  | [], _ => Eqv.identity_cut _
  | _ :: rest, second =>
      .trans (.cut_assoc _ _ _) (.cut (.refl _) (eqv_cut_ofLeaves rest second))

/-- **Every term is, modulo the structural equations, the sequential term of its framed uses.** -/
theorem eqv_ofLeaves : ∀ p : ProofTerm K Atom Rule, Eqv p (ofLeaves p.leaves)
  | .identity => .refl _
  | .rule _ => .symm (.trans (.cut_identity _) (.frame_zero _))
  | .frame extra inner =>
      .trans (.frame extra (eqv_ofLeaves inner)) (eqv_frame_ofLeaves extra inner.leaves)
  | .strengthen more inner =>
      .trans (.strengthen more (eqv_ofLeaves inner)) (eqv_strengthen_ofLeaves more inner.leaves)
  | .cut first second =>
      .trans (.cut (eqv_ofLeaves first) (eqv_ofLeaves second))
        (eqv_cut_ofLeaves first.leaves second.leaves)

/-- **The structural quotient of proof terms is the lists of framed uses.** -/
theorem eqv_iff_leaves (p q : ProofTerm K Atom Rule) : Eqv p q ↔ p.leaves = q.leaves := by
  constructor
  · exact Eqv.leaves_eq
  · intro same
    have first := eqv_ofLeaves p
    rw [same] at first
    exact .trans first (.symm (eqv_ofLeaves q))

/-- **A framed use is not the use.** -/
theorem frame_rule_not_eqv_rule {extra : Multiset Atom} (nonempty : extra ≠ 0)
    (declaration : Rule) :
    ¬ Eqv (.frame extra (.rule declaration) : ProofTerm K Atom Rule) (.rule declaration) := by
  intro same
  have leaves : [FramedUse.frame extra ((0 : Multiset Atom), declaration)] =
      [((0 : Multiset Atom), declaration)] := same.leaves_eq
  have first : (0 : Multiset Atom) + extra = 0 := congrArg Prod.fst (List.cons.inj leaves).1
  rw [zero_add] at first
  exact nonempty first

end ProofTerm

/-- A monoid on which frames act by endomorphisms. -/
structure FrameMonoid (Atom : Type uAtom) (M : Type uM) [Monoid M] where
  act : Multiset Atom → M → M
  act_zero : ∀ x, act 0 x = x
  act_add : ∀ first second x, act second (act first x) = act (first + second) x
  act_one : ∀ extra, act extra 1 = 1
  act_mul : ∀ extra x y, act extra (x * y) = act extra x * act extra y

/-- Frames acting on nothing. -/
def FrameMonoid.forget (Atom : Type uAtom) (M : Type uM) [Monoid M] : FrameMonoid Atom M where
  act := fun _ x => x
  act_zero := fun _ => rfl
  act_add := fun _ _ _ => rfl
  act_one := fun _ => rfl
  act_mul := fun _ _ _ => rfl

/-- Lists of framed uses, with frames acting on every use. -/
def framedUses (Atom : Type uAtom) (Rule : Type uRule) :
    FrameMonoid Atom (FreeMonoid (FramedUse Atom Rule)) where
  act := fun extra x => FreeMonoid.map (FramedUse.frame extra) x
  act_zero := fun x => DFunLike.congr_fun FramedUse.map_frame_zero x
  act_add := fun first second x => DFunLike.congr_fun (FramedUse.map_frame_frame first second) x
  act_one := fun extra => map_one (FreeMonoid.map (FramedUse.frame extra))
  act_mul := fun extra x y => map_mul (FreeMonoid.map (FramedUse.frame extra)) x y

/-- A use with nothing framed around it. -/
def unframed {Atom : Type uAtom} {Rule : Type uRule} (declaration : Rule) :
    FreeMonoid (FramedUse Atom Rule) :=
  FreeMonoid.of (0, declaration)

section Interpretation

variable {K : Type uK} {Atom : Type uAtom} {Rule : Type uRule} {M : Type uM} [Monoid M]

namespace ProofTerm

/-- The interpretation of a term, given the interpretation of the declarations. -/
def eval (frames : FrameMonoid Atom M) (leaf : Rule → M) : ProofTerm K Atom Rule → M
  | .identity => 1
  | .rule declaration => leaf declaration
  | .frame extra inner => frames.act extra (eval frames leaf inner)
  | .strengthen _ inner => eval frames leaf inner
  | .cut first second => eval frames leaf first * eval frames leaf second

/-- **The structural equations hold in every interpretation.** -/
theorem Eqv.eval_eq (frames : FrameMonoid Atom M) (leaf : Rule → M) {p q : ProofTerm K Atom Rule}
    (same : Eqv p q) : eval frames leaf p = eval frames leaf q := by
  induction same with
  | refl p => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond
  | frame extra _ ih => exact congrArg (frames.act extra) ih
  | strengthen more _ ih => exact ih
  | cut _ _ ihFirst ihSecond => exact congrArg₂ (· * ·) ihFirst ihSecond
  | cut_assoc p q r => exact mul_assoc _ _ _
  | identity_cut p => exact one_mul _
  | cut_identity p => exact mul_one _
  | frame_zero p => exact frames.act_zero _
  | frame_frame first second p => exact frames.act_add first second _
  | frame_cut extra p q => exact frames.act_mul extra _ _
  | frame_identity extra => exact frames.act_one extra
  | strengthen_rule more declaration => rfl
  | strengthen_identity more => rfl
  | strengthen_cut more p q => rfl
  | strengthen_frame more extra p => rfl

/-- Forgetting the frames interprets a term by its readout. -/
theorem eval_forget (leaf : Rule → M) : ∀ p : ProofTerm K Atom Rule,
    eval (FrameMonoid.forget Atom M) leaf p = (p.readout.map leaf).prod
  | .identity => rfl
  | .rule declaration => by
      show leaf declaration = [leaf declaration].prod
      simp
  | .frame _ inner => eval_forget leaf inner
  | .strengthen _ inner => eval_forget leaf inner
  | .cut first second => by
      show eval (FrameMonoid.forget Atom M) leaf first *
          eval (FrameMonoid.forget Atom M) leaf second =
        (List.map leaf (first.readout ++ second.readout)).prod
      rw [List.map_append, List.prod_append, eval_forget leaf first, eval_forget leaf second]

/-- In the lists of framed uses, a term is interpreted by its framed uses. -/
theorem eval_framedUses : ∀ p : ProofTerm K Atom Rule,
    eval (framedUses Atom Rule) unframed p = FreeMonoid.ofList p.leaves
  | .identity => rfl
  | .rule _ => rfl
  | .frame extra inner =>
      (congrArg (fun x => FreeMonoid.map (FramedUse.frame extra) x) (eval_framedUses inner)).trans
        (FreeMonoid.ofList_map (FramedUse.frame extra) inner.leaves).symm
  | .strengthen _ inner => eval_framedUses inner
  | .cut first second =>
      (congrArg₂ (· * ·) (eval_framedUses first) (eval_framedUses second)).trans
        (FreeMonoid.ofList_append first.leaves second.leaves).symm

/-- **The structural equations are exactly the equations of all interpretations.** -/
theorem eqv_iff_every_frameMonoid (p q : ProofTerm K Atom Rule) :
    Eqv p q ↔ ∀ (N : Type (max uAtom uRule)) [Monoid N] (frames : FrameMonoid Atom N)
      (leaf : Rule → N), eval frames leaf p = eval frames leaf q := by
  constructor
  · intro same N _ frames leaf
    exact same.eval_eq frames leaf
  · intro all
    have here := all (FreeMonoid (FramedUse Atom Rule)) (framedUses Atom Rule) unframed
    rw [eval_framedUses, eval_framedUses] at here
    exact (eqv_iff_leaves p q).mpr (FreeMonoid.ofList.injective here)

end ProofTerm

/-- The interpretation of lists of framed uses that the declarations determine. -/
def extend (frames : FrameMonoid Atom M) (leaf : Rule → M) :
    FreeMonoid (FramedUse Atom Rule) →* M :=
  FreeMonoid.lift fun framed => frames.act framed.1 (leaf framed.2)

theorem extend_unframed (frames : FrameMonoid Atom M) (leaf : Rule → M) (declaration : Rule) :
    extend frames leaf (unframed declaration) = leaf declaration :=
  frames.act_zero (leaf declaration)

theorem extend_act (frames : FrameMonoid Atom M) (leaf : Rule → M) (extra : Multiset Atom)
    (x : FreeMonoid (FramedUse Atom Rule)) :
    extend frames leaf ((framedUses Atom Rule).act extra x) =
      frames.act extra (extend frames leaf x) := by
  induction x using FreeMonoid.inductionOn with
  | one =>
      show extend frames leaf (FreeMonoid.map (FramedUse.frame extra) 1) =
        frames.act extra (extend frames leaf 1)
      simp only [map_one, frames.act_one]
  | of framed => exact (frames.act_add framed.1 extra (leaf framed.2)).symm
  | mul x y ihFirst ihSecond =>
      have first : extend frames leaf (FreeMonoid.map (FramedUse.frame extra) x) =
          frames.act extra (extend frames leaf x) := ihFirst
      have second : extend frames leaf (FreeMonoid.map (FramedUse.frame extra) y) =
          frames.act extra (extend frames leaf y) := ihSecond
      show extend frames leaf (FreeMonoid.map (FramedUse.frame extra) (x * y)) =
        frames.act extra (extend frames leaf (x * y))
      simp only [map_mul, frames.act_mul, first, second]

theorem extend_unique (frames : FrameMonoid Atom M) (leaf : Rule → M)
    (other : FreeMonoid (FramedUse Atom Rule) →* M)
    (starts : ∀ declaration, other (unframed declaration) = leaf declaration)
    (acts : ∀ extra x, other ((framedUses Atom Rule).act extra x) = frames.act extra (other x)) :
    other = extend frames leaf :=
  FreeMonoid.hom_eq fun framed => by
    have step := acts framed.1 (unframed framed.2)
    rw [starts] at step
    have same : (framedUses Atom Rule).act framed.1 (unframed framed.2) = FreeMonoid.of framed :=
      congrArg FreeMonoid.of (FramedUse.frame_start framed)
    rw [same] at step
    exact step

/-- **The lists of framed uses are the free monoid with a frame action on the declarations.** -/
theorem extend_exists_unique (frames : FrameMonoid Atom M) (leaf : Rule → M) :
    ∃! interpretation : FreeMonoid (FramedUse Atom Rule) →* M,
      (∀ declaration, interpretation (unframed declaration) = leaf declaration) ∧
        ∀ extra x, interpretation ((framedUses Atom Rule).act extra x) =
          frames.act extra (interpretation x) :=
  ⟨extend frames leaf, ⟨extend_unframed frames leaf, extend_act frames leaf⟩,
    fun other laws => extend_unique frames leaf other laws.1 laws.2⟩

/-- Every interpretation of terms factors through the framed uses. -/
theorem ProofTerm.eval_eq_extend (frames : FrameMonoid Atom M) (leaf : Rule → M) :
    ∀ p : ProofTerm K Atom Rule,
      ProofTerm.eval frames leaf p = extend frames leaf (FreeMonoid.ofList p.leaves)
  | .identity => (map_one (extend frames leaf)).symm
  | .rule declaration => (frames.act_zero (leaf declaration)).symm
  | .frame extra inner => by
      show frames.act extra (ProofTerm.eval frames leaf inner) =
        extend frames leaf ((framedUses Atom Rule).act extra (FreeMonoid.ofList inner.leaves))
      rw [extend_act, ProofTerm.eval_eq_extend frames leaf inner]
  | .strengthen _ inner => ProofTerm.eval_eq_extend frames leaf inner
  | .cut first second => by
      show ProofTerm.eval frames leaf first * ProofTerm.eval frames leaf second =
        extend frames leaf (FreeMonoid.ofList first.leaves * FreeMonoid.ofList second.leaves)
      rw [map_mul, ProofTerm.eval_eq_extend frames leaf first,
        ProofTerm.eval_eq_extend frames leaf second]

end Interpretation

end Mettapedia.Logic.LinearLogic.KnowledgeTensor
