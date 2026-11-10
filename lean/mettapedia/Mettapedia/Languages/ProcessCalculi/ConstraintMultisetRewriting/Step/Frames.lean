import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualObservationAction
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep


/-! # Indexed frames and their solution semantics -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uO uT uH

/-- A category of frames acting on terms. A morphism `a ⟶ b` instantiates what the frame `a`
declares by terms of the later frame `b`. Only the action laws are required, as for
`SubstitutionAction`. -/
structure Frames {Obj : Type uO} (Tm : Obj → Type uT) (Hom : Obj → Obj → Type uH) where
  E : {a : Obj} → Tm a → Tm a → Prop
  equivalence : ∀ a : Obj, Equivalence (@E a)
  act : {a b : Obj} → Hom a b → Tm a → Tm b
  id : (a : Obj) → Hom a a
  comp : {a b c : Obj} → Hom b c → Hom a b → Hom a c
  act_id : ∀ {a : Obj} (t : Tm a), act (id a) t = t
  act_comp : ∀ {a b c : Obj} (g : Hom b c) (f : Hom a b) (t : Tm a),
    act (comp g f) t = act g (act f t)
  preserves : ∀ {a b : Obj} (f : Hom a b) {s t : Tm a}, E s t → E (act f s) (act f t)

namespace Frames

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

section Definitions

variable (X : Frames Tm Hom)

def Solves {a b : Obj} (f : Hom a b) (e : Equation (Tm a)) : Prop :=
  X.E (X.act f e.1) (X.act f e.2)

def Models {a b : Obj} (f : Hom a b) (store : EquationStore (Tm a)) : Prop :=
  ∀ e ∈ store, X.Solves f e

/-- **Semantic solvability**: a solution into some later frame. -/
def Solvable {a : Obj} (store : EquationStore (Tm a)) : Prop :=
  ∃ (b : Obj) (f : Hom a b), X.Models f store

/-- An ask: the observation holds at every solution into every later frame. -/
def Entails {a : Obj} (store : EquationStore (Tm a))
    (observation : (b : Obj) → Hom a b → Prop) : Prop :=
  ∀ (b : Obj) (f : Hom a b), X.Models f store → observation b f

/-- Two stores with the same solutions in every later frame. -/
def Equivalent {a : Obj} (one two : EquationStore (Tm a)) : Prop :=
  ∀ (b : Obj) (f : Hom a b), X.Models f one ↔ X.Models f two

/-- Transport a store along a morphism. -/
def applyStore {a b : Obj} (f : Hom a b) (store : EquationStore (Tm a)) :
    EquationStore (Tm b) :=
  store.map fun e => (X.act f e.1, X.act f e.2)

/-- A principal answer: a solution through which every solution factors, on the terms of the
store's own frame. Terms of the answer's helpers are not constrained. -/
structure Principal {a m : Obj} (store : EquationStore (Tm a)) (answer : Hom a m) :
    Prop where
  sound : X.Models answer store
  factors : ∀ (b : Obj) (f : Hom a b), X.Models f store →
    ∃ residual : Hom m b, ∀ t : Tm a, X.E (X.act f t) (X.act (X.comp residual answer) t)

/-- The endomorphism monoid of one frame, as a substitution action. -/
def endo (a : Obj) : SubstitutionAction (Tm a) (Hom a a) where
  E := X.E
  equivalence := X.equivalence a
  apply := X.act
  identity := X.id a
  compose := X.comp
  apply_identity := X.act_id
  apply_compose := X.act_comp
  preserves := X.preserves

end Definitions

variable (Hom) in
/-- A frame that every frame maps to. -/
def WeaklyTerminal (t : Obj) : Prop := ∀ b : Obj, Nonempty (Hom b t)

variable (Hom) in
/-- The solutions of a frame: a later frame with a morphism into it. Predicate queries are
evaluated at a solution. -/
abbrev Solution (a : Obj) : Type (max uO uH) := (b : Obj) × Hom a b

variable {X : Frames Tm Hom}

@[simp] theorem models_nil {a b : Obj} (f : Hom a b) : X.Models f [] := by
  simp [Models]

theorem models_append {a b : Obj} (f : Hom a b) (one two : EquationStore (Tm a)) :
    X.Models f (one ++ two) ↔ X.Models f one ∧ X.Models f two := by
  simp only [Models, List.forall_mem_append]

theorem models_of_subset {a b : Obj} {f : Hom a b} {small big : EquationStore (Tm a)}
    (inside : ∀ e ∈ small, e ∈ big) (solved : X.Models f big) : X.Models f small :=
  fun e member => solved e (inside e member)

/-- Models depend on a morphism only through its action. -/
theorem models_congr {a b : Obj} {f g : Hom a b} (same : ∀ t : Tm a, X.act f t = X.act g t)
    (store : EquationStore (Tm a)) : X.Models f store ↔ X.Models g store := by
  constructor
  · intro solved e member
    have h : X.E (X.act f e.1) (X.act f e.2) := solved e member
    rw [same, same] at h
    exact h
  · intro solved e member
    have h : X.E (X.act g e.1) (X.act g e.2) := solved e member
    rw [← same, ← same] at h
    exact h

/-- Later instantiation keeps a solution a solution. -/
theorem models_comp {a b c : Obj} {f : Hom a b} {store : EquationStore (Tm a)}
    (solved : X.Models f store) (g : Hom b c) : X.Models (X.comp g f) store := by
  intro e member
  have later : X.E (X.act g (X.act f e.1)) (X.act g (X.act f e.2)) :=
    X.preserves g (solved e member)
  show X.E (X.act (X.comp g f) e.1) (X.act (X.comp g f) e.2)
  rw [X.act_comp, X.act_comp]
  exact later

/-- A transported store is solved exactly by the composites. -/
theorem models_applyStore {a b c : Obj} (f : Hom a b) (g : Hom b c)
    (store : EquationStore (Tm a)) :
    X.Models g (X.applyStore f store) ↔ X.Models (X.comp g f) store := by
  constructor
  · intro solved e member
    have transported : X.E (X.act g (X.act f e.1)) (X.act g (X.act f e.2)) :=
      solved _ (List.mem_map.mpr ⟨e, member, rfl⟩)
    show X.E (X.act (X.comp g f) e.1) (X.act (X.comp g f) e.2)
    rw [X.act_comp, X.act_comp]
    exact transported
  · intro solved e member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    have composite : X.E (X.act (X.comp g f) original.1) (X.act (X.comp g f) original.2) :=
      solved original present
    rw [X.act_comp, X.act_comp] at composite
    exact composite

theorem applyStore_id {a : Obj} (store : EquationStore (Tm a)) :
    X.applyStore (X.id a) store = store := by
  simp [applyStore, X.act_id]

/-- Composites act the same however they are bracketed. -/
theorem act_comp_assoc {a b c d : Obj} (h : Hom a b) (f : Hom b c) (g : Hom c d) (t : Tm a) :
    X.act (X.comp (X.comp g f) h) t = X.act (X.comp g (X.comp f h)) t := by
  rw [X.act_comp, X.act_comp, X.act_comp, X.act_comp]

theorem act_comp_id {a b : Obj} (g : Hom a b) (t : Tm a) :
    X.act g t = X.act (X.comp g (X.id a)) t := by
  rw [X.act_comp, X.act_id]

/-- Solvability is reflected along every morphism. -/
theorem solvable_of_applyStore {a b : Obj} (f : Hom a b) {store : EquationStore (Tm a)}
    (solvable : X.Solvable (X.applyStore f store)) : X.Solvable store := by
  obtain ⟨c, g, solved⟩ := solvable
  exact ⟨c, X.comp g f, (models_applyStore f g store).mp solved⟩

theorem solvable_of_subset {a : Obj} {small big : EquationStore (Tm a)}
    (inside : ∀ e ∈ small, e ∈ big) (solvable : X.Solvable big) : X.Solvable small := by
  obtain ⟨b, f, solved⟩ := solvable
  exact ⟨b, f, models_of_subset inside solved⟩

theorem Equivalent.solvable_iff {a : Obj} {one two : EquationStore (Tm a)}
    (same : X.Equivalent one two) : X.Solvable one ↔ X.Solvable two := by
  constructor
  · rintro ⟨b, f, solved⟩
    exact ⟨b, f, (same b f).mp solved⟩
  · rintro ⟨b, f, solved⟩
    exact ⟨b, f, (same b f).mpr solved⟩

theorem Equivalent.entails_iff {a : Obj} {one two : EquationStore (Tm a)}
    (same : X.Equivalent one two) (observation : (b : Obj) → Hom a b → Prop) :
    X.Entails one observation ↔ X.Entails two observation := by
  constructor
  · intro asked b f solved
    exact asked b f ((same b f).mpr solved)
  · intro asked b f solved
    exact asked b f ((same b f).mp solved)

theorem Entails.mono {a : Obj} {store : EquationStore (Tm a)}
    {stronger weaker : (b : Obj) → Hom a b → Prop} (asked : X.Entails store stronger)
    (implies : ∀ b f, stronger b f → weaker b f) : X.Entails store weaker :=
  fun b f solved => implies b f (asked b f solved)

theorem Entails.of_subset {a : Obj} {small big : EquationStore (Tm a)}
    {observation : (b : Obj) → Hom a b → Prop} (inside : ∀ e ∈ small, e ∈ big)
    (asked : X.Entails small observation) : X.Entails big observation :=
  fun b f solved => asked b f (models_of_subset inside solved)

theorem entails_and {a : Obj} {store : EquationStore (Tm a)}
    {first second : (b : Obj) → Hom a b → Prop} :
    X.Entails store (fun b f => first b f ∧ second b f) ↔
      X.Entails store first ∧ X.Entails store second :=
  ⟨fun asked => ⟨fun b f solved => (asked b f solved).1, fun b f solved => (asked b f solved).2⟩,
    fun asked b f solved => ⟨asked.1 b f solved, asked.2 b f solved⟩⟩

/-- A principal answer presents exactly the solutions: those that factor through it. -/
theorem Principal.models_iff {a m : Obj} {store : EquationStore (Tm a)}
    {answer : Hom a m} (principal : X.Principal store answer) {b : Obj} (f : Hom a b) :
    X.Models f store ↔ ∃ residual : Hom m b,
      ∀ t : Tm a, X.E (X.act f t) (X.act (X.comp residual answer) t) := by
  constructor
  · exact principal.factors b f
  · rintro ⟨residual, through⟩ e member
    have middle : X.E (X.act residual (X.act answer e.1)) (X.act residual (X.act answer e.2)) :=
      X.preserves residual (principal.sound e member)
    rw [← X.act_comp, ← X.act_comp] at middle
    exact (X.equivalence b).trans (through e.1)
      ((X.equivalence b).trans middle ((X.equivalence b).symm (through e.2)))

theorem Principal.solvable {a m : Obj} {store : EquationStore (Tm a)}
    {answer : Hom a m} (principal : X.Principal store answer) : X.Solvable store :=
  ⟨m, answer, principal.sound⟩

/-! ## Weakly terminal frames and the endomorphism fibre -/

/-- **Existence is witnessed at a weakly terminal frame.** -/
theorem solvable_iff_into {t : Obj} (terminal : WeaklyTerminal Hom t) {a : Obj}
    (store : EquationStore (Tm a)) :
    X.Solvable store ↔ ∃ f : Hom a t, X.Models f store := by
  constructor
  · rintro ⟨b, f, solved⟩
    obtain ⟨g⟩ := terminal b
    exact ⟨X.comp g f, models_comp solved g⟩
  · rintro ⟨f, solved⟩
    exact ⟨t, f, solved⟩

/-- When the store's own frame receives a morphism from a weakly terminal frame, an
endomorphism solves every solvable store. -/
theorem solvable_iff_endo {t a : Obj} (terminal : WeaklyTerminal Hom t) (back : Hom t a)
    (store : EquationStore (Tm a)) :
    X.Solvable store ↔ ∃ f : Hom a a, X.Models f store := by
  constructor
  · intro solvable
    obtain ⟨f, solved⟩ := (solvable_iff_into terminal store).mp solvable
    exact ⟨X.comp back f, models_comp solved back⟩
  · rintro ⟨f, solved⟩
    exact ⟨a, f, solved⟩

/-- **Solvability is the consistency of the endomorphism monoid**, under the same hypothesis. -/
theorem solvable_iff_endo_consistent {t a : Obj} (terminal : WeaklyTerminal Hom t)
    (back : Hom t a) (store : EquationStore (Tm a)) :
    X.Solvable store ↔ (X.endo a).Consistent store :=
  solvable_iff_endo terminal back store

/-- A principal answer that is an endomorphism is principal for the endomorphism monoid. -/
theorem Principal.endo {a : Obj} {store : EquationStore (Tm a)} {answer : Hom a a}
    (principal : X.Principal store answer) : (X.endo a).Principal store answer :=
  ⟨principal.sound, fun δ solved => principal.factors a δ solved⟩

/-- An ask over every later frame is an ask over the endomorphisms. -/
theorem Entails.endo {a : Obj} {store : EquationStore (Tm a)}
    {observation : (b : Obj) → Hom a b → Prop} (asked : X.Entails store observation) :
    (X.endo a).Entails store (observation a) :=
  fun σ solved => asked a σ solved

/-! ## A substitution action is the one-frame case -/

section OneFrame

universe uA uB

variable {T : Type uA} {S : Type uB} (A : SubstitutionAction T S)

/-- The one-frame category of a substitution action: its morphisms are its substitutions. -/
def ofSubstitution : Frames (fun _ : PUnit.{1} => T) (fun _ _ => S) where
  E := A.E
  equivalence _ := A.equivalence
  act := A.apply
  id _ := A.identity
  comp := A.compose
  act_id := A.apply_identity
  act_comp := A.apply_compose
  preserves := A.preserves

theorem ofSubstitution_models_iff (σ : S) (store : EquationStore T) :
    (ofSubstitution A).Models (a := PUnit.unit) (b := PUnit.unit) σ store ↔ A.Models σ store :=
  Iff.rfl

theorem ofSubstitution_solvable_iff (store : EquationStore T) :
    (ofSubstitution A).Solvable (a := PUnit.unit) store ↔ A.Consistent store := by
  constructor
  · rintro ⟨_, σ, solved⟩
    exact ⟨σ, solved⟩
  · rintro ⟨σ, solved⟩
    exact ⟨PUnit.unit, σ, solved⟩

theorem ofSubstitution_entails_iff (store : EquationStore T) (observation : S → Prop) :
    (ofSubstitution A).Entails (a := PUnit.unit) store (fun _ σ => observation σ) ↔
      A.Entails store observation := by
  constructor
  · intro asked σ solved
    exact asked PUnit.unit σ solved
  · intro asked _ σ solved
    exact asked σ solved

theorem ofSubstitution_principal_iff (store : EquationStore T) (answer : S) :
    (ofSubstitution A).Principal (a := PUnit.unit) (m := PUnit.unit) store answer ↔
      A.Principal store answer := by
  constructor
  · intro principal
    exact ⟨principal.sound, fun δ solved => principal.factors PUnit.unit δ solved⟩
  · intro principal
    exact ⟨principal.sound, fun _ δ solved => principal.factors δ solved⟩

end OneFrame

/-! ## The canonical instance: declaration frames and contextual assignments -/

section Contextual

variable (S : Signature)

/-- A declaration frame: identities with their metavariable arities. -/
structure Frame where
  Names : Type
  arity : Names → MetaArity S

/-- **The category of declaration frames.** Morphisms are contextual assignments and act on
observations by capture-avoiding instantiation. -/
def contextual : Frames (fun F : Frame S => Observation S F.arity)
    (fun F G : Frame S => Assignment F.arity G.arity) where
  E := fun s t => s = t
  equivalence _ := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  act := fun f t => instantiateObservation f t
  id F := generator F.arity
  comp := fun g f => Assignment.compose g f
  act_id := instantiateObservation_identity
  act_comp := fun g f t => (instantiateObservation_comp f g t).symm
  preserves := fun {_ _} f {_ _} same => congrArg (fun t => instantiateObservation f t) same

/-- One parameterless metavariable per sort. -/
def firstOrderFrame : Frame S := ⟨S.Srt, fun sort => ([], sort)⟩

variable {S}

/-- Every frame maps to `firstOrderFrame`: an identity goes to the parameterless metavariable of
its sort, which ignores the parameters. -/
def toFirstOrder (F : Frame S) : Assignment F.arity (firstOrderFrame S).arity :=
  fun identity => .op (.inr (.mk (F.arity identity).2)) .nil

theorem firstOrderFrame_weaklyTerminal :
    WeaklyTerminal (fun F G : Frame S => Assignment F.arity G.arity) (firstOrderFrame S) :=
  fun F => ⟨toFirstOrder F⟩

theorem contextual_models_iff {F G : Frame S} (σ : Assignment F.arity G.arity)
    (store : EquationStore (Observation S F.arity)) :
    (contextual S).Models σ store ↔
      ∀ e ∈ store, instantiateObservation σ e.1 = instantiateObservation σ e.2 :=
  Iff.rfl

/-- Contextual solvability, with the future frame unpacked. -/
theorem contextual_solvable_iff {V : Type} {declaration : V → MetaArity S}
    (store : EquationStore (Observation S declaration)) :
    (contextual S).Solvable (a := ⟨V, declaration⟩) store ↔
      ∃ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment declaration future),
        ∀ e ∈ store, instantiateObservation candidate e.1 = instantiateObservation candidate e.2 := by
  constructor
  · rintro ⟨⟨Future, future⟩, candidate, solved⟩
    exact ⟨Future, future, candidate, solved⟩
  · rintro ⟨Future, future, candidate, solved⟩
    exact ⟨⟨Future, future⟩, candidate, solved⟩

/-- **Existence never needs a higher-order helper**: every solvable store has a solution into
`firstOrderFrame`. -/
theorem contextual_solvable_iff_firstOrder {F : Frame S}
    (store : EquationStore (Observation S F.arity)) :
    (contextual S).Solvable store ↔
      ∃ σ : Assignment F.arity (firstOrderFrame S).arity, (contextual S).Models σ store :=
  solvable_iff_into (X := contextual S) firstOrderFrame_weaklyTerminal store

/-- The endomorphism monoid of a frame is the existing observation action. -/
theorem contextual_endo (F : Frame S) :
    (contextual S).endo F = ContextualObservationAction.action F.arity := rfl

/-- **The endomorphic profile is complete for existence on an inhabited frame**: when every sort
has a term in `F`, a store at `F` is solvable exactly when the existing observation action is
consistent on it. -/
theorem contextual_solvable_iff_consistent {F : Frame S}
    (inhabited : Assignment (firstOrderFrame S).arity F.arity)
    (store : EquationStore (Observation S F.arity)) :
    (contextual S).Solvable store ↔ (ContextualObservationAction.action F.arity).Consistent store := by
  rw [← contextual_endo]
  exact solvable_iff_endo_consistent (X := contextual S) firstOrderFrame_weaklyTerminal inhabited store

end Contextual

end Frames


end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
