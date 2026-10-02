import Mettapedia.OSLF.Syntax.SecondOrderEquationModelNaturality

/-!
# Arrows of equation-class contexts are tuples of equation classes

An arrow of the equation-class context category into a context assigns an
equation class of terms to each of its metavariables, at that metavariable's
arity, and every such tuple of classes is an arrow. Reading the target's own
metavariables through an arrow returns the assigned classes; precomposition
moves each class along the model map.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderContext

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding

variable {S : Signature} {M : List (MetaArity S)} (equations : List (EqAxiom S M))

/-- The equation-class contexts of an authored presentation. -/
local notation "Contexts" => EquationContexts (authoredEquationPresentation S equations)

/-- The class of a term in the equation-class model of its context. -/
abbrev termClass {X : Object S} {Γ : Ctx S} {s : S.Srt} (t : Term (withMetas S X.arities) Γ s) :
    EquationTermClass (authoredEquationPresentation S equations) X Γ s :=
  Quot.mk _ t

/-- The class of a body for one more metavariable, in front of an arrow. -/
def consClass {X Y : Object S} {a : MetaArity S}
    (body : EquationTermClass (authoredEquationPresentation S equations) X a.1 a.2)
    (rest : (⟨X⟩ : Contexts) ⟶ ⟨Y⟩) : (⟨X⟩ : Contexts) ⟶ ⟨⟨a :: Y.arities⟩⟩ :=
  Quot.liftOn₂ body rest
    (fun t raw => Quot.mk _ fun i => Fin.cases (motive := fun i =>
      Term (withMetas S X.arities) ((a :: Y.arities).get i).1 ((a :: Y.arities).get i).2) t raw i)
    (by
      intro t first second related
      apply _root_.CategoryTheory.Quotient.sound
      have same : (authoredEquationPresentation S equations).homRel first second := by
        simpa only [HomRel.compClosure_eq_self] using related
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact .refl _
      · exact same i)
    (by
      intro t t' raw related
      apply _root_.CategoryTheory.Quotient.sound
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact related
      · exact .refl _)

/-- The arrow assigning the given classes to the metavariables of a context. -/
def ofClasses {X : Object S} : ∀ (L : List (MetaArity S)),
    (∀ i : Fin L.length,
      EquationTermClass (authoredEquationPresentation S equations) X (L.get i).1 (L.get i).2) →
    ((⟨X⟩ : Contexts) ⟶ ⟨⟨L⟩⟩)
  | [], _ => Quot.mk _ fun i => i.elim0
  | _ :: L, classes =>
      consClass equations (classes ⟨0, Nat.succ_pos _⟩) (ofClasses L fun i => classes i.succ)

/-- An arrow reads the class of a term by instantiating its metavariables. -/
theorem modelMapQuot_termClass {X Y : Object S} (raw : X ⟶ Y) {Γ : Ctx S} {s : S.Srt}
    (t : Term (withMetas S Y.arities) Γ s) :
    (authoredEquationModelMapQuot S equations
      ((authoredEquationPresentation S equations).quotientFunctor.map raw)).raw.map
        (termClass equations t) =
      termClass equations (instInto raw t) :=
  rfl

theorem consClass_metaVar_zero {X Y : Object S} {a : MetaArity S}
    (body : EquationTermClass (authoredEquationPresentation S equations) X a.1 a.2)
    (rest : (⟨X⟩ : Contexts) ⟶ ⟨Y⟩) :
    (authoredEquationModelMapQuot S equations (consClass equations body rest)).raw.map
        (termClass equations (metaVar (M := a :: Y.arities) ⟨0, Nat.succ_pos _⟩)) = body := by
  induction body using Quot.ind with
  | _ t =>
      induction rest using Quot.ind with
      | _ raw =>
          exact congrArg (termClass equations) (instInto_metaVar _ _)

theorem consClass_metaVar_succ {X Y : Object S} {a : MetaArity S}
    (body : EquationTermClass (authoredEquationPresentation S equations) X a.1 a.2)
    (rest : (⟨X⟩ : Contexts) ⟶ ⟨Y⟩) (i : Fin Y.arities.length) :
    (authoredEquationModelMapQuot S equations (consClass equations body rest)).raw.map
        (termClass equations (metaVar (M := a :: Y.arities) i.succ)) =
      (authoredEquationModelMapQuot S equations rest).raw.map
        (termClass equations (metaVar (M := Y.arities) i)) := by
  induction body using Quot.ind with
  | _ t =>
      induction rest using Quot.ind with
      | _ raw =>
          exact congrArg (termClass equations)
            ((instInto_metaVar (M := a :: Y.arities) _ i.succ).trans (instInto_metaVar raw i).symm)

/-- **Reading a context's own metavariables through the arrow of a tuple of
classes returns the classes.** -/
theorem ofClasses_metaVar {X : Object S} : ∀ (L : List (MetaArity S))
    (classes : ∀ i : Fin L.length,
      EquationTermClass (authoredEquationPresentation S equations) X (L.get i).1 (L.get i).2)
    (i : Fin L.length),
    (authoredEquationModelMapQuot S equations (ofClasses equations L classes)).raw.map
        (termClass equations (metaVar (M := L) i)) = classes i
  | _ :: _, _, ⟨0, _⟩ => consClass_metaVar_zero equations _ _
  | _ :: L, classes, ⟨n + 1, bound⟩ =>
      (consClass_metaVar_succ equations _ _ ⟨n, Nat.lt_of_succ_lt_succ bound⟩).trans
        (ofClasses_metaVar L (fun i => classes i.succ) ⟨n, Nat.lt_of_succ_lt_succ bound⟩)

theorem comp_consClass {W X Y : Object S} {a : MetaArity S}
    (u : (⟨W⟩ : Contexts) ⟶ ⟨X⟩)
    (body : EquationTermClass (authoredEquationPresentation S equations) X a.1 a.2)
    (rest : (⟨X⟩ : Contexts) ⟶ ⟨Y⟩) :
    u ≫ consClass equations body rest =
      consClass equations ((authoredEquationModelMapQuot S equations u).raw.map body) (u ≫ rest) := by
  induction u using Quot.ind with
  | _ rawU =>
      induction body using Quot.ind with
      | _ t =>
          induction rest using Quot.ind with
          | _ raw =>
              change Quot.mk _ (rawU ≫ _) = Quot.mk _ _
              congr 1
              funext i
              refine Fin.cases ?_ (fun i => ?_) i
              · rfl
              · rfl

/-- **Precomposition moves each class along the model map.** -/
theorem comp_ofClasses {W X : Object S} (u : (⟨W⟩ : Contexts) ⟶ ⟨X⟩) :
    ∀ (L : List (MetaArity S))
      (classes : ∀ i : Fin L.length,
        EquationTermClass (authoredEquationPresentation S equations) X (L.get i).1 (L.get i).2),
      u ≫ ofClasses equations L classes =
        ofClasses equations L fun i => (authoredEquationModelMapQuot S equations u).raw.map (classes i)
  | [], _classes => by
      induction u using Quot.ind with
      | _ raw =>
          change Quot.mk _ (raw ≫ _) = Quot.mk _ _
          congr 1
          funext i
          exact i.elim0
  | _ :: L, classes =>
      (comp_consClass equations u _ _).trans
        (congrArg (consClass equations _) (comp_ofClasses u L fun i => classes i.succ))

/-- Forgetting the first metavariable after a pairing returns the rest. -/
theorem consClass_comp_tail {X Y : Object S} {a : MetaArity S}
    (body : EquationTermClass (authoredEquationPresentation S equations) X a.1 a.2)
    (rest : (⟨X⟩ : Contexts) ⟶ ⟨Y⟩) :
    consClass equations body rest ≫
        (authoredEquationPresentation S equations).quotientFunctor.map
          (fun i => metaVar (M := a :: Y.arities) i.succ : (⟨a :: Y.arities⟩ : Object S) ⟶ Y) =
      rest := by
  induction body using Quot.ind with
  | _ t =>
      induction rest using Quot.ind with
      | _ raw =>
          change Quot.mk _ (fun i : Fin Y.arities.length =>
            instInto _ (metaVar (M := a :: Y.arities) i.succ)) = Quot.mk _ raw
          congr 1
          funext i
          exact instInto_metaVar (M := a :: Y.arities) _ i.succ

/-- **An assignment is the tuple of the classes of its bodies.** -/
theorem ofClasses_termClass {X : Object S} : ∀ (L : List (MetaArity S)) (raw : X ⟶ ⟨L⟩),
    ofClasses equations L (fun i => termClass equations (raw i)) =
      (authoredEquationPresentation S equations).quotientFunctor.map raw
  | [], raw => by
      change Quot.mk _ _ = Quot.mk _ raw
      congr 1
      funext i
      exact i.elim0
  | a :: L, raw => by
      have rest := ofClasses_termClass L (fun i => raw i.succ)
      change consClass equations (termClass equations (raw ⟨0, Nat.succ_pos _⟩))
        (ofClasses equations L fun i => termClass equations (raw i.succ)) = _
      rw [rest]
      change Quot.mk _ _ = Quot.mk _ raw
      congr 1
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · rfl

/-- The identity is the tuple of the classes of its own metavariables. -/
theorem ofClasses_metaVar_id (L : List (MetaArity S)) :
    ofClasses equations L (fun i => termClass equations (metaVar (M := L) i)) =
      𝟙 (⟨⟨L⟩⟩ : Contexts) :=
  ofClasses_termClass equations L (𝟙 (⟨L⟩ : Object S))

end Mettapedia.OSLF.Binding.SecondOrderContext
