import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PrincipalAnswers
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveContextualCategory

/-!
# The candidate step at dependently typed frames: the category of frames

The interface of the candidate step (`Frames`) asks for objects, judged terms at each object,
morphisms acting on them, and a `Prop`-valued equivalence that the action preserves, with the action
laws on the nose. This module gives an instance whose frames are dependently typed.

**The source model** is the formation-sensitive syntactic category
(`FormationSensitiveContextual`): formed telescopes, formed types at a universe, terms with their
formation-sensitive typing derivations, and typed simultaneous substitutions. Substitution acts on raw
syntax, so identity and composition laws hold before any quotient. Conversion stays a relation
(`Conv`), so it can be the equivalence of the instance. The typed quotient category would make the
equivalence equality, at the price of choosing representatives; the declaration-aware category has
weaker typing, whose conversion rule does not ask that the target type be formed.

**The instance** (`frames`):
* frames are formed telescopes; a metavariable is a telescope variable;
* a morphism `Hom Γ Δ` is a formed substitution `Δ ⟶ Γ`, which instantiates every variable of `Γ`
  by a term over `Δ`;
* a judged term at `Γ` is a formed type over `Γ` with a term of it (`Entry`);
* the action is substitution, on both components (`Entry.reindex`);
* the equivalence is convertibility of both components (`Entry.Convertible`).

Metavariables of contextual type are reached by raising: a metavariable `M : (Ψ ⊢ A)` is a telescope
variable of type `Π Ψ. A`, and an occurrence `M[σ]` is an application spine.

**The interface at these frames.**
* Two solutions act alike on every judged term exactly when they are pointwise convertible
  (`pointwise_iff`): equivalence of solutions is read off the variables.
* At the empty frame, solvability of a store of conversion equations is convertibility of every
  equation (`solvable_empty_iff`).
* The definition of the newest variable by a term of the older frame, `x ≐ v`, has the principal
  answer that substitutes `v` for `x` (`instantiate`); a principal answer of older knowledge extends
  to one of the knowledge with the definition appended (`principal_definition`). Asks are then
  decided at the answer (`Frames.Principal.entails_models_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

namespace Dependent

open CategoryTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveContextual

variable {Head : Type} {rules : Rules Head}

/-! ## Judged terms -/

/-- **A judged term at a frame**: a formed type over the frame's telescope and a term of it. -/
structure Entry (Γ : Context rules) where
  type : TypeOver Γ
  term : Term Γ type

namespace Entry

theorem ext {Γ : Context rules} {s t : Entry Γ} (sameType : s.type = t.type)
    (sameCode : s.term.code = t.term.code) : s = t := by
  cases s with
  | mk sType sTerm =>
    cases t with
    | mk tType tTerm =>
      dsimp only at sameType sameCode
      subst sameType
      obtain rfl := Term.ext sameCode
      rfl

/-- Reindex a judged term along a substitution into its frame. -/
def reindex {Γ Δ : Context rules} (t : Entry Γ) (σ : Δ ⟶ Γ) : Entry Δ :=
  ⟨t.type.reindex σ, t.term.reindex σ⟩

theorem reindex_id {Γ : Context rules} (t : Entry Γ) : t.reindex (𝟙 Γ) = t :=
  ext t.type.reindex_id (subst_ids t.term.code)

theorem reindex_comp {Γ Δ Θ : Context rules} (t : Entry Θ) (σ : Γ ⟶ Δ) (τ : Δ ⟶ Θ) :
    t.reindex (σ ≫ τ) = (t.reindex τ).reindex σ :=
  ext (t.type.reindex_comp σ τ) (subst_subComp σ.substitution τ.substitution t.term.code).symm

/-- **Convertibility of judged terms**: of their types, and of their terms. -/
def Convertible {Γ : Context rules} (s t : Entry Γ) : Prop :=
  Conv rules.headEq s.type.code t.type.code rules.computation ∧
    Conv rules.headEq s.term.code t.term.code rules.computation

theorem Convertible.refl {Γ : Context rules} (t : Entry Γ) : Convertible t t :=
  ⟨.refl _, .refl _⟩

theorem Convertible.symm {Γ : Context rules} {s t : Entry Γ} (same : Convertible s t) :
    Convertible t s :=
  ⟨.symm _ _ same.1, .symm _ _ same.2⟩

theorem Convertible.trans {Γ : Context rules} {s t u : Entry Γ} (first : Convertible s t)
    (second : Convertible t u) : Convertible s u :=
  ⟨.trans _ _ _ first.1 second.1, .trans _ _ _ first.2 second.2⟩

theorem convertible_of_codes {Γ : Context rules} {s t : Entry Γ}
    (sameType : s.type.code = t.type.code) (sameCode : s.term.code = t.term.code) :
    Convertible s t :=
  ⟨by rw [sameType]; exact .refl _, by rw [sameCode]; exact .refl _⟩

/-- The newest variable of an extended frame, as a judged term. -/
def last (Γ : Context rules) (A : TypeOver Γ) : Entry (extend Γ A) :=
  ⟨A.reindex (projectionHom Γ A), newest Γ A⟩

/-- Comprehension beta, on judged terms: the newest variable read through a pairing is the paired
term. -/
theorem last_reindex_pair {Γ Δ : Context rules} {A : TypeOver Γ} (σ : Δ ⟶ Γ)
    (t : Term Δ (A.reindex σ)) : (last Γ A).reindex (pair σ t) = ⟨A.reindex σ, t⟩ :=
  ext (show (A.reindex (projectionHom Γ A)).reindex (pair σ t) = A.reindex σ by
      rw [← TypeOver.reindex_comp, pair_projection]) rfl

end Entry

/-! ## The category of dependent frames -/

variable (rules) in
/-- **The category of dependent frames.** Frames are formed telescopes, a morphism `Hom Γ Δ` is a
formed substitution `Δ ⟶ Γ`, judged terms are formed types with terms of them, the action is
substitution, and the equivalence is convertibility of both components. The action laws hold on the
nose. -/
def frames : Frames (fun Γ : Context rules => Entry Γ) (fun Γ Δ : Context rules => Δ ⟶ Γ) where
  E s t := Entry.Convertible s t
  equivalence _ := ⟨Entry.Convertible.refl, Entry.Convertible.symm, Entry.Convertible.trans⟩
  act σ t := t.reindex σ
  id Γ := 𝟙 Γ
  comp g f := g ≫ f
  act_id t := t.reindex_id
  act_comp g f t := t.reindex_comp g f
  preserves := @fun _ _ σ _ _ same =>
    ⟨Conv.substitute σ.substitution same.1, Conv.substitute σ.substitution same.2⟩

theorem frames_models_iff {Γ Δ : Context rules} (σ : Δ ⟶ Γ) (store : EquationStore (Entry Γ)) :
    (frames rules).Models (a := Γ) (b := Δ) σ store ↔
      ∀ e ∈ store, Entry.Convertible (e.1.reindex σ) (e.2.reindex σ) :=
  Iff.rfl

/-- Dependent solvability, with the later frame unpacked. -/
theorem frames_solvable_iff {Γ : Context rules} (store : EquationStore (Entry Γ)) :
    (frames rules).Solvable (a := Γ) store ↔
      ∃ (Δ : Context rules) (σ : Δ ⟶ Γ), ∀ e ∈ store, Entry.Convertible (e.1.reindex σ) (e.2.reindex σ) :=
  Iff.rfl

/-! ## Solutions are compared on their variables -/

/-- Pointwise convertible substitutions act convertibly on every judged term. -/
theorem convertible_reindex_of_pointwise {Γ Δ : Context rules} {σ τ : Δ ⟶ Γ}
    (pointwise : ∀ i, Conv rules.headEq (σ.substitution i) (τ.substitution i) rules.computation)
    (t : Entry Γ) : Entry.Convertible (t.reindex σ) (t.reindex τ) :=
  ⟨Conv.substitutePointwise pointwise t.type.code, Conv.substitutePointwise pointwise t.term.code⟩

/-- Substitutions that act convertibly on every judged term are pointwise convertible: each
variable is a judged term at its looked-up type, which is formed. -/
theorem pointwise_of_convertible_reindex {Γ Δ : Context rules} {σ τ : Δ ⟶ Γ}
    (same : ∀ t : Entry Γ, Entry.Convertible (t.reindex σ) (t.reindex τ)) (i : Fin Γ.arity) :
    Conv rules.headEq (σ.substitution i) (τ.substitution i) rules.computation := by
  obtain ⟨u, isUniverse, formed⟩ := Γ.formed.lookup_formed i
  exact (same ⟨⟨Ctx.lookup Γ.raw i, u, isUniverse, formed⟩, ⟨.var i, .var i⟩⟩).2

/-- **Two solutions act alike exactly when they are pointwise convertible.** -/
theorem pointwise_iff {Γ Δ : Context rules} (σ τ : Δ ⟶ Γ) :
    (∀ t : Entry Γ, (frames rules).E ((frames rules).act σ t) ((frames rules).act τ t)) ↔
      ∀ i, Conv rules.headEq (σ.substitution i) (τ.substitution i) rules.computation :=
  ⟨pointwise_of_convertible_reindex, fun pointwise => convertible_reindex_of_pointwise pointwise⟩

/-! ## Closed knowledge -/

/-- A raw substitution closing every variable by one closed raw term. Untyped conversion does not
read types, so any closed raw term will do. -/
def closeAll (n : Nat) : Sub Head n 0 := fun _ => .const .anonymous

/-- Conversion of closed terms is reflected by every substitution of them. -/
theorem conv_of_conv_subst_closed {m : Nat} (σ : Sub Head 0 m) {a b : Tm Head 0}
    (converted : Conv rules.headEq (subst σ a) (subst σ b) rules.computation) :
    Conv rules.headEq a b rules.computation := by
  have back := Conv.substitute (closeAll m) converted
  have closed : subComp (closeAll m) σ = ids := funext fun i => i.elim0
  rwa [subst_subComp, subst_subComp, closed, subst_ids, subst_ids] at back

/-- **At the empty frame, solvability is convertibility**: a store of equations between closed
judged terms is solvable exactly when each equation already converts. -/
theorem solvable_empty_iff (store : EquationStore (Entry (empty rules))) :
    (frames rules).Solvable (a := empty rules) store ↔ ∀ e ∈ store, Entry.Convertible e.1 e.2 := by
  constructor
  · rintro ⟨Δ, σ, solved⟩ e member
    have converted : Entry.Convertible (e.1.reindex σ) (e.2.reindex σ) := solved e member
    exact ⟨conv_of_conv_subst_closed σ.substitution converted.1,
      conv_of_conv_subst_closed σ.substitution converted.2⟩
  · intro convertible
    refine ⟨empty rules, 𝟙 _, fun e member => ?_⟩
    show Entry.Convertible (e.1.reindex (𝟙 _)) (e.2.reindex (𝟙 _))
    rw [Entry.reindex_id, Entry.reindex_id]
    exact convertible e member

/-! ## Definitions have principal answers -/

/-- The definition `x ≐ v` of the newest variable by a term of the older frame. -/
def definition (Γ : Context rules) {A : TypeOver Γ} (v : Term Γ A) : Equation (Entry (extend Γ A)) :=
  (Entry.last Γ A, (⟨A, v⟩ : Entry Γ).reindex (projectionHom Γ A))

/-- Substituting `v` for the newest variable. -/
def instantiate (Γ : Context rules) {A : TypeOver Γ} (v : Term Γ A) : Γ ⟶ extend Γ A :=
  pair (𝟙 Γ) (v.cast A.reindex_id.symm)

theorem instantiate_projection (Γ : Context rules) {A : TypeOver Γ} (v : Term Γ A) :
    instantiate Γ v ≫ projectionHom Γ A = 𝟙 Γ :=
  pair_projection _ _

/-- The identity is a principal answer of the empty store. -/
theorem principal_nil (Γ : Context rules) : (frames rules).Principal (a := Γ) [] (𝟙 Γ) where
  sound := Frames.models_nil _
  factors Δ σ _ := ⟨σ, fun t => by
    show Entry.Convertible (t.reindex σ) (t.reindex (σ ≫ 𝟙 Γ))
    rw [Category.comp_id]
    exact Entry.Convertible.refl _⟩

/-- **A principal answer extends through a definition.** If `m` is a principal answer of older
knowledge, then `m` followed by substituting `v` for the newest variable is a principal answer of
that knowledge read in the extended frame together with the definition `x ≐ v`. -/
theorem principal_definition {Γ M : Context rules} {A : TypeOver Γ} (v : Term Γ A)
    {knowledge : EquationStore (Entry Γ)} {m : M ⟶ Γ}
    (principal : (frames rules).Principal (a := Γ) (m := M) knowledge m) :
    (frames rules).Principal (a := extend Γ A) (m := M)
      ((frames rules).applyStore (projectionHom Γ A) knowledge ++ [definition Γ v])
      (m ≫ instantiate Γ v) where
  sound := by
    refine (Frames.models_append _ _ _).mpr ⟨?_, ?_⟩
    · refine (Frames.models_applyStore (X := frames rules) (projectionHom Γ A) (m ≫ instantiate Γ v)
        knowledge).mpr ?_
      show (frames rules).Models ((m ≫ instantiate Γ v) ≫ projectionHom Γ A) knowledge
      rw [Category.assoc, instantiate_projection, Category.comp_id]
      exact principal.sound
    · intro e member
      obtain rfl := List.mem_singleton.mp member
      show Entry.Convertible ((Entry.last Γ A).reindex (m ≫ instantiate Γ v))
        (((⟨A, v⟩ : Entry Γ).reindex (projectionHom Γ A)).reindex (m ≫ instantiate Γ v))
      rw [← Entry.reindex_comp, Category.assoc, instantiate_projection, Category.comp_id]
      refine Entry.convertible_of_codes ?_ ?_
      · show subst (m ≫ instantiate Γ v).substitution
            (subst projection A.code) = subst m.substitution A.code
        rw [subst_subComp]
        rfl
      · show subst m.substitution (v.cast A.reindex_id.symm).code = subst m.substitution v.code
        rw [Term.cast_code]
  factors := by
    intro Δ f solved
    obtain ⟨old, defined⟩ := (Frames.models_append (X := frames rules) f _ _).mp solved
    have restricted : (frames rules).Models (f ≫ projectionHom Γ A) knowledge :=
      (Frames.models_applyStore (X := frames rules) (projectionHom Γ A) f knowledge).mp old
    obtain ⟨r, through⟩ := principal.factors Δ (f ≫ projectionHom Γ A) restricted
    have older := pointwise_of_convertible_reindex through
    have value : Entry.Convertible ((Entry.last Γ A).reindex f)
        (((⟨A, v⟩ : Entry Γ).reindex (projectionHom Γ A)).reindex f) :=
      defined _ (List.mem_singleton_self _)
    refine ⟨r, convertible_reindex_of_pointwise fun i => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · have newestValue : Conv rules.headEq (f.substitution 0)
          (subst (f ≫ projectionHom Γ A).substitution v.code) rules.computation := by
        have h := value.2
        rw [← Entry.reindex_comp] at h
        exact h
      have moved := Conv.substitutePointwise older v.code
      show Conv rules.headEq (f.substitution 0)
        (subst r.substitution (subst m.substitution (v.cast A.reindex_id.symm).code)) rules.computation
      rw [Term.cast_code, subst_subComp]
      exact .trans _ _ _ newestValue moved
    · exact older j

/-- **The definition of the newest variable has a principal answer**: substituting its value. -/
theorem definition_principal (Γ : Context rules) {A : TypeOver Γ} (v : Term Γ A) :
    (frames rules).Principal (a := extend Γ A) (m := Γ) [definition Γ v] (instantiate Γ v) := by
  have extended := principal_definition v (principal_nil Γ)
  rw [Category.id_comp] at extended
  exact extended

/-- Equality guards on the extended frame are asked by a definition exactly when they hold after
substituting the value. -/
theorem definition_entails_iff (Γ : Context rules) {A : TypeOver Γ} (v : Term Γ A)
    (guards : EquationStore (Entry (extend Γ A))) :
    (frames rules).Entails [definition Γ v] (fun _ σ => (frames rules).Models σ guards) ↔
      (frames rules).Models (instantiate Γ v) guards :=
  (definition_principal Γ v).entails_models_iff guards

end Dependent

#print axioms Dependent.Entry.reindex_comp
#print axioms Dependent.Entry.last_reindex_pair
#print axioms Dependent.frames
#print axioms Dependent.pointwise_iff
#print axioms Dependent.solvable_empty_iff
#print axioms Dependent.principal_nil
#print axioms Dependent.principal_definition
#print axioms Dependent.definition_principal
#print axioms Dependent.definition_entails_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
