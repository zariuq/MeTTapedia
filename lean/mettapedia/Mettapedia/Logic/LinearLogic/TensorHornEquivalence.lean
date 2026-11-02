import Mettapedia.Logic.LinearLogic.TensorStructural
import Mettapedia.Logic.LinearHorn.Derivation

/-!
# Exact equivalence of tensor sequents and multiplicative Horn diagrams

The tensor sequent calculus has ordinary left/right rules, arbitrary tensor
and unit cut formulas, and reusable external transition declarations. Horn
diagrams instead expose parallel composition and composition along a whole
atomic multiset. Translation in both directions retains the complete linear
boundary and the ordered list of declared transition uses.

This is the positive tensor/transition-axiom fragment. It is not an
identification with arbitrary MLL formulas, exponential syntax, quantified
unification or a Bibel mating correctness criterion.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LinearLogic.TensorSequent

universe uAtom uRule
variable {Atom : Type uAtom} {Rule : Type uRule} {premises conclusions : Rule → Multiset Atom}

private def hornCast {before otherBefore after otherAfter : Multiset Atom}
    (source : before = otherBefore) (target : after = otherAfter)
    (diagram : LinearHorn.Derivation premises conclusions before after) :
    LinearHorn.Derivation premises conclusions otherBefore otherAfter := source ▸ target ▸ diagram

private theorem hornCast_uses {before otherBefore after otherAfter : Multiset Atom}
    (source : before = otherBefore) (target : after = otherAfter)
    (diagram : LinearHorn.Derivation premises conclusions before after) :
    (hornCast source target diagram).uses = diagram.uses := by cases source; cases target; rfl

/-- Sequent cut is interpreted by preserving the right premise's other
hypotheses beside the left derivation, and then composing. -/
theorem toHorn {context : Multiset (Formula Atom)} {goal : Formula Atom}
    (proof : Derives premises conclusions context goal) :
    ∃ diagram : LinearHorn.Derivation premises conclusions (contextAtoms context) goal.atoms,
      diagram.uses = proof.uses := by
  induction proof with
  | atomId name => exact ⟨.identity {name}, rfl⟩
  | transition rule =>
      refine ⟨hornCast (contextAtoms_atomContext _).symm (Formula.atoms_ofMultiset _).symm (.rule rule), ?_⟩
      exact hornCast_uses _ _ _
  | oneR => exact ⟨.identity 0, rfl⟩
  | @oneL context goal prior ih =>
      obtain ⟨diagram, uses⟩ := ih
      have source : contextAtoms context = contextAtoms (Formula.one ::ₘ context) := by simp [Formula.atoms]
      exact ⟨hornCast source rfl diagram, (hornCast_uses _ _ _).trans uses⟩
  | @tensorR leftContext rightContext leftGoal rightGoal first second ihFirst ihSecond =>
      obtain ⟨left, leftUses⟩ := ihFirst
      obtain ⟨right, rightUses⟩ := ihSecond
      have source : contextAtoms leftContext + contextAtoms rightContext = contextAtoms (leftContext + rightContext) :=
        (contextAtoms_add _ _).symm
      have target : leftGoal.atoms + rightGoal.atoms = (Formula.tensor leftGoal rightGoal).atoms := rfl
      refine ⟨hornCast source target (.tensor left right), ?_⟩
      simp only [hornCast_uses, LinearHorn.Derivation.uses, leftUses, rightUses, Derives.uses]
  | @tensorL context left right goal prior ih =>
      obtain ⟨diagram, uses⟩ := ih
      have source : contextAtoms (left ::ₘ right ::ₘ context) = contextAtoms (Formula.tensor left right ::ₘ context) := by
        simp [Formula.atoms, add_assoc]
      exact ⟨hornCast source rfl diagram, (hornCast_uses _ _ _).trans uses⟩
  | @cut leftContext rightContext cutFormula goal first second ihFirst ihSecond =>
      obtain ⟨left, leftUses⟩ := ihFirst
      obtain ⟨right, rightUses⟩ := ihSecond
      let rightOpened := hornCast (contextAtoms_cons _ _) rfl right
      have source : contextAtoms leftContext + contextAtoms rightContext = contextAtoms (leftContext + rightContext) :=
        (contextAtoms_add _ _).symm
      refine ⟨hornCast source rfl (.cut (.tensor left (.identity (contextAtoms rightContext))) rightOpened), ?_⟩
      simp only [hornCast_uses, rightOpened, LinearHorn.Derivation.uses,
        List.append_nil, leftUses, rightUses, Derives.uses]

theorem toHornAtomic {before : Multiset Atom} {goal : Formula Atom}
    (proof : Derives premises conclusions (atomContext before) goal) :
    ∃ diagram : LinearHorn.Derivation premises conclusions before goal.atoms,
      diagram.uses = proof.uses := by
  obtain ⟨raw, rawUses⟩ := toHorn proof
  exact ⟨hornCast (contextAtoms_atomContext _) rfl raw, (hornCast_uses _ _ _).trans rawUses⟩

/-- Atomic boundary translation. Tensor packaging adds no transition uses;
cut is realized by the sequent calculus's genuine formula cut rule. -/
theorem ofHornAtomic {before after : Multiset Atom}
    (diagram : LinearHorn.Derivation premises conclusions before after) :
    ∃ proof : Derives premises conclusions (atomContext before) (Formula.ofMultiset after),
      proof.uses = diagram.uses := by
  induction diagram with
  | identity context =>
      obtain ⟨proof, uses⟩ := Derives.fromAtoms (premises := premises) (conclusions := conclusions) (Formula.ofMultiset context)
      exact ⟨Derives.castContext (congrArg atomContext (Formula.atoms_ofMultiset _)) proof,
        (Derives.uses_castContext _ _).trans uses⟩
  | rule declaration => exact ⟨.transition declaration, rfl⟩
  | @tensor left right left' right' first second ihFirst ihSecond =>
      obtain ⟨leftProof, leftUses⟩ := ihFirst
      obtain ⟨rightProof, rightUses⟩ := ihSecond
      obtain ⟨packed, packedUses⟩ := Derives.repackageGoal (.tensorR leftProof rightProof)
        (right := Formula.ofMultiset (right + right')) (by simp [Formula.atoms])
      refine ⟨Derives.castContext (atomContext_add _ _).symm packed, ?_⟩
      simp only [Derives.uses_castContext, packedUses, Derives.uses, leftUses, rightUses,
        LinearHorn.Derivation.uses]
  | @cut before middle after first second ihFirst ihSecond =>
      obtain ⟨leftProof, leftUses⟩ := ihFirst
      obtain ⟨rightProof, rightUses⟩ := ihSecond
      have secondContext : atomContext middle = atomContext (Formula.ofMultiset middle).atoms + 0 := by simp
      obtain ⟨packed, packedUses⟩ := Derives.condenseLeft (Formula.ofMultiset middle) 0
        (Formula.ofMultiset after) (Derives.castContext secondContext rightProof)
      refine ⟨Derives.castContext (add_zero _) (.cut leftProof packed), ?_⟩
      simp only [Derives.uses_castContext, Derives.uses, packedUses, leftUses, rightUses,
        LinearHorn.Derivation.uses]

/-- Every positive tensor sequent, including its arbitrary tensor hypotheses
and units, is represented by the corresponding atomic Horn boundary. -/
theorem ofHorn {context : Multiset (Formula Atom)} {goal : Formula Atom}
    (diagram : LinearHorn.Derivation premises conclusions (contextAtoms context) goal.atoms) :
    ∃ proof : Derives premises conclusions context goal, proof.uses = diagram.uses := by
  obtain ⟨atomic, atomicUses⟩ := ofHornAtomic diagram
  obtain ⟨hypotheses, hypothesesUses⟩ := Derives.contextBundle (premises := premises) (conclusions := conclusions) context
  have source : atomContext (contextAtoms context) =
      atomContext (Formula.ofMultiset (contextAtoms context)).atoms + 0 := by simp
  obtain ⟨packed, packedUses⟩ := Derives.condenseLeft (Formula.ofMultiset (contextAtoms context)) 0
    (Formula.ofMultiset goal.atoms) (Derives.castContext source atomic)
  let composed := Derives.castContext (add_zero _) (.cut hypotheses packed)
  obtain ⟨result, resultUses⟩ := Derives.repackageGoal composed (right := goal) (by simp)
  refine ⟨result, ?_⟩
  simp only [resultUses, composed, Derives.uses_castContext, Derives.uses, packedUses,
    hypothesesUses, atomicUses, List.nil_append]

theorem derives_iff_horn (context : Multiset (Formula Atom)) (goal : Formula Atom) (trace : List Rule) :
    (∃ proof : Derives premises conclusions context goal, proof.uses = trace) ↔
      ∃ diagram : LinearHorn.Derivation premises conclusions (contextAtoms context) goal.atoms,
        diagram.uses = trace := by
  constructor
  · rintro ⟨proof, uses⟩
    obtain ⟨diagram, same⟩ := toHorn proof
    exact ⟨diagram, same.trans uses⟩
  · rintro ⟨diagram, uses⟩
    obtain ⟨proof, same⟩ := ofHorn diagram
    exact ⟨proof, same.trans uses⟩

theorem provable_iff_horn (context : Multiset (Formula Atom)) (goal : Formula Atom) :
    Nonempty (Derives premises conclusions context goal) ↔
      Nonempty (LinearHorn.Derivation premises conclusions (contextAtoms context) goal.atoms) := by
  constructor
  · rintro ⟨proof⟩
    obtain ⟨diagram, _⟩ := toHorn proof
    exact ⟨diagram⟩
  · rintro ⟨diagram⟩
    obtain ⟨proof, _⟩ := ofHorn diagram
    exact ⟨proof⟩

end Mettapedia.Logic.LinearLogic.TensorSequent
