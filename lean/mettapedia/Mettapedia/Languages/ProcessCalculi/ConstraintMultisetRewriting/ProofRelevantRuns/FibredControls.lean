import Mettapedia.Logic.LinearLogic.KnowledgeTensorZonesControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.Fibred

/-!
# Controls for witnessed runs over frames

The system is `KnowledgeTensorControls.names`: frames are numbers, a frame `n` has the names
`Fin n`, and the one declaration births the name `n` along `n ⟶ n + 1`.

* `counts`, `interp_counts`, `counts_unique`: the number of firings is a model over frames, and every
  map of models into it counts the firings of a witnessed run.
* `two_births`: a witnessed run of two births over the frame map `0 ⟶ 2`; `two_births_counted`.
* `carried_name`: a name beside a birth is carried into the target frame as the same name; the frame
  rule of a witnessed run over a frame map is this carrying (`Path.frame`), not the identity of atoms.
* `born_not_carried`: the born name is none of the carried ones.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.FibredControls

open Mettapedia.Logic.LinearLogic.KnowledgeTensor
open Mettapedia.Logic.LinearLogic.KnowledgeTensorControls (names a_born_name_is_not_among_the_carried)
open _root_.CategoryTheory
open Fibred

universe uF uH uK uAtom uRule

section Counting

variable {Frame : Type uF} [Category.{uH} Frame] {K : Frame → Type uK} [∀ a, SemilatticeInf (K a)]
  {Atom : Frame → Type uAtom} {Rule : Frame → Type uRule}

omit [∀ a, SemilatticeInf (K a)] in
theorem recast_const {a b : Frame} {k j : K a} {Γ Δ : Multiset (Atom a)} {f g : a ⟶ b}
    {k' j' : K b} {Γ' Δ' : Multiset (Atom b)} (hk : k = j) (hΓ : Γ = Δ) (hf : f = g) (hk' : k' = j')
    (hΓ' : Γ' = Δ') (x : Nat) : recast (H := fun _ _ _ _ _ _ _ => Nat) hk hΓ hf hk' hΓ' x = x := by
  subst hk hΓ hf hk' hΓ'
  rfl

/-- **The number of firings is a model over frames.** -/
abbrev counts (sys : IndexedSystem Frame K Atom Rule) : FibredModel.{uF, uH, uK, uAtom, uRule, 0} sys where
  Hom _ _ _ _ _ _ _ := Nat
  identity _ _ _ := 0
  rule _ _ _ := 1
  frame _ x := x
  strengthen _ x := x
  cut x y := x + y
  cut_assoc x y z := (Nat.add_assoc x y z).trans (recast_const _ _ _ _ _ _).symm
  identity_cut x := (Nat.zero_add x).trans (recast_const _ _ _ _ _ _).symm
  cut_identity x := (Nat.add_zero x).trans (recast_const _ _ _ _ _ _).symm
  frame_zero x := (recast_const _ _ _ _ _ x).symm
  frame_frame _ _ x := (recast_const _ _ _ _ _ x).symm
  frame_cut _ _ _ := (recast_const _ _ _ _ _ _).symm
  frame_identity _ _ _ _ := (recast_const _ _ _ _ _ 0).symm
  strengthen_rule _ _ _ _ := (recast_const _ _ _ _ _ 1).symm
  strengthen_identity _ _ _ _ := (recast_const _ _ _ _ _ 0).symm
  strengthen_cut _ _ _ := (recast_const _ _ _ _ _ _).symm
  strengthen_frame _ _ _ := rfl

/-- **The interpretation in the counting model is the number of firings.** -/
theorem interp_counts (sys : IndexedSystem Frame K Atom Rule) {a : Frame} {k : K a}
    {Γ : Multiset (Atom a)} {b : Frame} {f : a ⟶ b} {k' : K b} {Γ' : Multiset (Atom b)}
    (p : Path sys a k Γ b f k' Γ') : interp (counts sys) p = p.uses.length := by
  induction p with
  | done route told target => exact recast_const _ _ _ _ _ 0
  | fire declaration φ source asked told target route finalKnowledge finalAtoms rest ih =>
      show recast (H := fun _ _ _ _ _ _ _ => Nat) _ _ _ _ _
          (recast (H := fun _ _ _ _ _ _ _ => Nat) _ _ _ _ _ 1 + interp (counts sys) rest) =
        rest.uses.length + 1
      rw [recast_const, recast_const, ih, Nat.add_comm]

/-- Every map of models into the counting model counts the firings. -/
theorem counts_unique (sys : IndexedSystem Frame K Atom Rule)
    (F : FibredModelMap (Fibred.paths sys) (counts sys)) {a : Frame} {k : K a}
    {Γ : Multiset (Atom a)} {b : Frame} {f : a ⟶ b} {k' : K b} {Γ' : Multiset (Atom b)}
    (p : Path sys a k Γ b f k' Γ') : F.map p = p.uses.length :=
  (lift_unique (counts sys) F p).trans (interp_counts sys p)

end Counting

/-! ## Births -/

/-- One birth at frame `n`, from any state. -/
theorem birth_fires (n : Nat) (k : Set Bool) (Γ : Multiset (Fin n)) :
    names.Fires (a := n) () k Γ (names.know (names.extend (a := n) ()) k ⊓ names.tell (a := n) ())
      (names.conclusions (a := n) () + names.carried (names.extend (a := n) ()) Γ) :=
  ⟨Γ, by simp [IndexedSystem.premises, names], True.intro, rfl, rfl⟩

/-- **Two births over the frame map `0 ⟶ 2`**, as a witnessed run. -/
theorem two_births : ∃ (k : Set Bool) (Γ : Multiset (Fin 2)) (p : Path names 0 Set.univ 0 2
    (names.extend (a := 0) () ≫ names.extend (a := 1) () ≫ 𝟙 2) k Γ),
      p.uses = [⟨0, ()⟩, ⟨1, ()⟩] :=
  let run := IndexedSystem.Run.fire (birth_fires 0 Set.univ 0)
    (IndexedSystem.Run.fire (birth_fires 1 _ _) (IndexedSystem.Run.done (sys := names) 2 _ _))
  let ⟨p, same⟩ := Path.exists_of_run run
  ⟨_, _, p, same⟩

/-- The two births are counted twice. -/
theorem two_births_counted : ∃ (k : Set Bool) (Γ : Multiset (Fin 2)) (p : Path names 0 Set.univ 0 2
    (names.extend (a := 0) () ≫ names.extend (a := 1) () ≫ 𝟙 2) k Γ),
      interp (counts names) p = 2 := by
  obtain ⟨k, Γ, p, same⟩ := two_births
  exact ⟨k, Γ, p, by rw [interp_counts, same]; rfl⟩

/-- **A name beside a birth is carried into the target frame as the same name.** -/
theorem carried_name :
    names.carried (names.extend (a := 1) ()) ({0} : Multiset (Fin 1)) = ({0} : Multiset (Fin 2)) :=
  rfl

/-- **The born name is none of the carried names.** -/
theorem born_not_carried (present : Multiset (Fin 1)) :
    Fin.last 1 ∉ names.carried (names.extend (a := 1) ()) present :=
  a_born_name_is_not_among_the_carried 1 present

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.FibredControls
