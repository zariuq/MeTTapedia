import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PrincipalAnswers

/-!
# Transport of firings along isomorphisms of states

A state of the candidate step lives at a declaration frame, and a firing can create fresh helpers,
so the state after it lives at a larger frame. Comparing firings at different states therefore
needs transport.

* **Isomorphisms of frames** (`Frames.Iso`): morphisms both ways whose composites act as the
  identity. They form a groupoid (`Iso.refl`, `Iso.symm`, `Iso.trans`), keep solvability
  (`Iso.solvable_applyStore_iff`) and carry stores with the same solutions
  (`Iso.equivalent_symm`, `Iso.equivalent_trans`). Renaming fresh helpers is such an isomorphism.
* **Terms carried up to the knowledge** (`Frames.Carried`): a term carried along a morphism agrees with
  another at every solution of the target's knowledge. It is how isomorphisms of states relate what
  clients read, stored rows and public terms, and it is closed under inverses and composites
  (`Carried.symm`, `Carried.trans`).
* **Isomorphisms of states, as the interface sees them** (`Step.StateIso`): an isomorphism of
  frames that carries the knowledge to knowledge with the same solutions, and a renaming of
  occurrence identities that carries the present occurrences (`StateIso.rename`). Isomorphic states
  have solvable knowledge together (`StateIso.solvable_iff`). The interface has no labels and no
  clients, so which identities a renaming must fix is the business of the layer that has them
  (`Transport.Escape`, `EscapeIso.fixes`).
* **Transport** (`Transport`): an instance chooses its isomorphisms of states over the interface's,
  forming a groupoid, and its **alike** firings: firings at one state whose data agree up to the
  frame equivalence once their frames are identified. Alike firings have one selection, are admitted
  together and have isomorphic results (`selection_alike`, `admits_alike`, `result_alike`). Firings
  move along isomorphisms by the functor laws up to alikeness (`move_refl`, `move_trans`,
  `move_symm`, `move_alike`), select the renamed occurrences, keep their admission, and their
  results stay isomorphic. At dependent frames the laws hold only up to conversion: a firing
  moved along an isomorphism and back is convertible, not equal, to itself. A firing also has a
  **residual** after another admitted firing: the same firing read at the other's result, along
  the other's morphism of frames. A residual keeps its selection, and residuals are natural up to
  alikeness.
* **Strict transport** is the case where alike firings are equal: the laws then hold as equations
  (`strict_laws`), and similarity is transport on the nose (`similar_cons_cons_of_strict`).
* **State classes** (`Transport.Same`, `classSetoid`, `StateClass`): states up to isomorphism. The
  relation is a congruence for the step: every admitted firing at one state of a class has a
  counterpart with the renamed selection at every other, and the results are again in one class
  (`same_step`, `Same.admits`).
* **Runs along isomorphisms** (`moveRun`) and **similar runs** (`Similar`): runs whose firings are,
  firing by firing, alike to transports of each other. Similarity is an equivalence (`Similar.refl`,
  `Similar.symm`, `Similar.trans`), is compatible with concatenation (`Similar.append`) and with
  alike prefixes (`Similar.cons_alike`), relates isomorphic starts and ends (`Similar.same_start`,
  `Similar.same_last`), and keeps every site account whose grades are invariant under transport and
  under alikeness (`Similar.account_eq`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

universe uO uT uH uOcc uS uF uI

/-- Renaming by the identity changes no selection. -/
theorem renameSelection_refl {O : Type uOcc} (selection : Selection O) :
    AnnotatedRuns.renameSelection (Equiv.refl O) selection = selection := by
  obtain ⟨taken, read, made⟩ := selection
  simp [AnnotatedRuns.renameSelection]

/-! ## Lists related elementwise -/

section Forall₂

variable {α β γ : Type*}

theorem forall₂_swap {R : α → β → Prop} {R' : β → α → Prop} (h : ∀ a b, R a b → R' b a) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → List.Forall₂ R' l₂ l₁
  | _, _, .nil => .nil
  | _, _, .cons related rest => .cons (h _ _ related) (forall₂_swap h rest)

theorem forall₂_comp {R₁ : α → β → Prop} {R₂ : β → γ → Prop} {R₃ : α → γ → Prop}
    (h : ∀ a b c, R₁ a b → R₂ b c → R₃ a c) :
    ∀ {l₁ : List α} {l₂ : List β} {l₃ : List γ}, List.Forall₂ R₁ l₁ l₂ → List.Forall₂ R₂ l₂ l₃ →
      List.Forall₂ R₃ l₁ l₃
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons first rest, .cons second rest' => .cons (h _ _ _ first second) (forall₂_comp h rest rest')

theorem forall₂_append {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} {m₁ : List α} {m₂ : List β}, List.Forall₂ R l₁ l₂ →
      List.Forall₂ R m₁ m₂ → List.Forall₂ R (l₁ ++ m₁) (l₂ ++ m₂)
  | _, _, _, _, .nil, later => later
  | _, _, _, _, .cons first rest, later => .cons first (forall₂_append rest later)

theorem forall₂_map {δ : Type*} {R : α → β → Prop} {S : γ → δ → Prop} {f : α → γ} {g : β → δ}
    (h : ∀ a b, R a b → S (f a) (g b)) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → List.Forall₂ S (l₁.map f) (l₂.map g)
  | _, _, .nil => .nil
  | _, _, .cons related rest => .cons (h _ _ related) (forall₂_map h rest)

end Forall₂

namespace Frames

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-- **An isomorphism of frames**: morphisms both ways whose composites act as the identity, up to
the equivalence of terms. -/
structure Iso (X : Frames Tm Hom) (a b : Obj) where
  hom : Hom a b
  inv : Hom b a
  inv_hom : ∀ t : Tm a, X.E (X.act inv (X.act hom t)) t
  hom_inv : ∀ t : Tm b, X.E (X.act hom (X.act inv t)) t

variable {X : Frames Tm Hom}

theorem Equivalent.symm {a : Obj} {one two : EquationStore (Tm a)} (same : X.Equivalent one two) :
    X.Equivalent two one :=
  fun b f => (same b f).symm

theorem Equivalent.trans {a : Obj} {one two three : EquationStore (Tm a)}
    (first : X.Equivalent one two) (second : X.Equivalent two three) : X.Equivalent one three :=
  fun b f => (first b f).trans (second b f)

/-- Transport along a morphism keeps stores with the same solutions. -/
theorem Equivalent.applyStore {a b : Obj} (f : Hom a b) {one two : EquationStore (Tm a)}
    (same : X.Equivalent one two) : X.Equivalent (X.applyStore f one) (X.applyStore f two) := by
  intro c g
  exact (models_applyStore f g one).trans ((same c (X.comp g f)).trans (models_applyStore f g two).symm)

/-- Stores with the same members have the same solutions. -/
theorem equivalent_of_mem_iff {a : Obj} {one two : EquationStore (Tm a)}
    (same : ∀ e, e ∈ one ↔ e ∈ two) : X.Equivalent one two :=
  fun _ _ => ⟨fun solved e member => solved e ((same e).mpr member),
    fun solved e member => solved e ((same e).mp member)⟩

/-- **Stores related equation by equation up to the frame equivalence have the same solutions.** -/
theorem equivalent_of_forall₂ {a : Obj} {one two : EquationStore (Tm a)}
    (related : List.Forall₂ (fun e e' => X.E e.1 e'.1 ∧ X.E e.2 e'.2) one two) :
    X.Equivalent one two := by
  intro b f
  induction related with
  | nil => exact Iff.rfl
  | @cons e e' rest rest' head _ ih =>
      have step : X.Solves f e ↔ X.Solves f e' := by
        constructor
        · intro solved
          exact (X.equivalence b).trans ((X.equivalence b).symm (X.preserves f head.1))
            ((X.equivalence b).trans solved (X.preserves f head.2))
        · intro solved
          exact (X.equivalence b).trans (X.preserves f head.1)
            ((X.equivalence b).trans solved ((X.equivalence b).symm (X.preserves f head.2)))
      show (∀ x ∈ e :: rest, X.Solves f x) ↔ ∀ x ∈ e' :: rest', X.Solves f x
      rw [List.forall_mem_cons, List.forall_mem_cons]
      exact and_congr step ih

namespace Iso

/-- The identity isomorphism. -/
def refl (a : Obj) : X.Iso a a where
  hom := X.id a
  inv := X.id a
  inv_hom t := by
    simp only [X.act_id]
    exact (X.equivalence a).refl t
  hom_inv t := by
    simp only [X.act_id]
    exact (X.equivalence a).refl t

/-- The inverse isomorphism. -/
def symm {a b : Obj} (φ : X.Iso a b) : X.Iso b a := ⟨φ.inv, φ.hom, φ.hom_inv, φ.inv_hom⟩

/-- The composite isomorphism. -/
def trans {a b c : Obj} (φ : X.Iso a b) (ψ : X.Iso b c) : X.Iso a c where
  hom := X.comp ψ.hom φ.hom
  inv := X.comp φ.inv ψ.inv
  inv_hom t := by
    simp only [X.act_comp]
    exact (X.equivalence a).trans (X.preserves φ.inv (ψ.inv_hom (X.act φ.hom t))) (φ.inv_hom t)
  hom_inv t := by
    simp only [X.act_comp]
    exact (X.equivalence c).trans (X.preserves ψ.hom (φ.hom_inv (X.act ψ.inv t))) (ψ.hom_inv t)

/-- **Isomorphisms keep solvability.** -/
theorem solvable_applyStore_iff {a b : Obj} (φ : X.Iso a b) (store : EquationStore (Tm a)) :
    X.Solvable (X.applyStore φ.hom store) ↔ X.Solvable store := by
  constructor
  · exact solvable_of_applyStore φ.hom
  · rintro ⟨c, g, solved⟩
    refine ⟨c, X.comp g φ.inv, (models_applyStore φ.hom (X.comp g φ.inv) store).mpr ?_⟩
    refine (models_congrE (fun t => ?_) store).mpr solved
    simp only [X.act_comp]
    exact X.preserves g (φ.inv_hom t)

theorem equivalent_refl {a : Obj} (store : EquationStore (Tm a)) :
    X.Equivalent (X.applyStore (X.id a) store) store := by
  intro b h
  rw [applyStore_id]

/-- Stores related along an isomorphism are related back along its inverse. -/
theorem equivalent_symm {a b : Obj} (φ : X.Iso a b) {one : EquationStore (Tm a)}
    {two : EquationStore (Tm b)} (same : X.Equivalent (X.applyStore φ.hom one) two) :
    X.Equivalent (X.applyStore φ.inv two) one := by
  intro c h
  calc X.Models h (X.applyStore φ.inv two)
      ↔ X.Models (X.comp h φ.inv) two := models_applyStore _ _ _
    _ ↔ X.Models (X.comp h φ.inv) (X.applyStore φ.hom one) := (same c _).symm
    _ ↔ X.Models (X.comp (X.comp h φ.inv) φ.hom) one := models_applyStore _ _ _
    _ ↔ X.Models h one := models_congrE (fun t => by
        simp only [X.act_comp]
        exact X.preserves h (φ.inv_hom t)) one

/-- Relations along isomorphisms compose. -/
theorem equivalent_trans {a b c : Obj} (φ : X.Iso a b) (ψ : X.Iso b c) {one : EquationStore (Tm a)}
    {two : EquationStore (Tm b)} {three : EquationStore (Tm c)}
    (first : X.Equivalent (X.applyStore φ.hom one) two)
    (second : X.Equivalent (X.applyStore ψ.hom two) three) :
    X.Equivalent (X.applyStore (φ.trans ψ).hom one) three := by
  intro d h
  calc X.Models h (X.applyStore (φ.trans ψ).hom one)
      ↔ X.Models (X.comp h (X.comp ψ.hom φ.hom)) one := models_applyStore _ _ _
    _ ↔ X.Models (X.comp (X.comp h ψ.hom) φ.hom) one := models_congrE (fun t => by
        simp only [X.act_comp]
        exact (X.equivalence d).refl _) one
    _ ↔ X.Models (X.comp h ψ.hom) (X.applyStore φ.hom one) := (models_applyStore _ _ _).symm
    _ ↔ X.Models (X.comp h ψ.hom) two := first d _
    _ ↔ X.Models h (X.applyStore ψ.hom two) := (models_applyStore _ _ _).symm
    _ ↔ X.Models h three := second d h

end Iso

/-! ## Terms carried up to the knowledge -/

/-- **A term carried to another along a morphism, up to the knowledge**: at every solution of the
knowledge of the target frame, the carried term and the other agree. Clients read stored rows and
public terms only at solutions, so this is how isomorphisms of states must relate them. -/
def Carried {a b : Obj} (f : Hom a b) (K : EquationStore (Tm b)) (u : Tm a) (v : Tm b) : Prop :=
  X.Entails K fun _ g => X.E (X.act g (X.act f u)) (X.act g v)

namespace Carried

/-- Terms related by the frame equivalence are carried at every knowledge. -/
theorem of_E {a b : Obj} {f : Hom a b} {K : EquationStore (Tm b)} {u : Tm a} {v : Tm b}
    (same : X.E (X.act f u) v) : X.Carried f K u v :=
  fun _ g _ => X.preserves g same

/-- Carrying depends on the morphism only through its action. -/
theorem congr {a b : Obj} {f f' : Hom a b} (agree : ∀ t : Tm a, X.E (X.act f t) (X.act f' t))
    {K : EquationStore (Tm b)} {u : Tm a} {v : Tm b} (carried : X.Carried f K u v) :
    X.Carried f' K u v := fun c g solved =>
  (X.equivalence c).trans ((X.equivalence c).symm (X.preserves g (agree u))) (carried c g solved)

/-- **Carrying back along the inverse**, when the isomorphism carries the knowledge. -/
theorem symm {a b : Obj} (φ : X.Iso a b) {K : EquationStore (Tm a)} {K' : EquationStore (Tm b)}
    (knowledge : X.Equivalent (X.applyStore φ.hom K) K') {u : Tm a} {v : Tm b}
    (carried : X.Carried φ.hom K' u v) : X.Carried φ.inv K v u := by
  intro c g solved
  have back : X.Models (X.comp g φ.inv) K' := by
    refine (knowledge c _).mp ((models_applyStore φ.hom _ K).mpr ?_)
    refine (models_congrE (fun t => ?_) K).mpr solved
    simp only [X.act_comp]
    exact X.preserves g (φ.inv_hom t)
  have there := carried c (X.comp g φ.inv) back
  simp only [X.act_comp] at there
  exact (X.equivalence c).trans ((X.equivalence c).symm there) (X.preserves g (φ.inv_hom u))

/-- **Carrying composes**, along a second morphism that carries the knowledge. -/
theorem trans {a b c : Obj} {f : Hom a b} {f' : Hom b c} {K : EquationStore (Tm b)}
    {K' : EquationStore (Tm c)} (knowledge : X.Equivalent (X.applyStore f' K) K') {u : Tm a}
    {v : Tm b} {w : Tm c} (first : X.Carried f K u v) (second : X.Carried f' K' v w) :
    X.Carried (X.comp f' f) K' u w := by
  intro d g solved
  have before : X.Models (X.comp g f') K :=
    (models_applyStore f' g K).mp ((knowledge d g).mpr solved)
  have carried := first d (X.comp g f') before
  simp only [X.act_comp] at carried ⊢
  exact (X.equivalence d).trans carried (second d g solved)

end Carried

end Frames

namespace Step

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (P : Step X O State Firing)

/-- **An isomorphism of states, as the interface sees it**: an isomorphism of their frames that
carries the knowledge of the first to knowledge with the same solutions as the second's, and a
renaming of occurrence identities that carries the present occurrences of the first to those of the
second. The interface has neither labels nor clients; what an instance shows its clients restricts
the renamings it chooses (`Transport.Escape`). -/
structure StateIso (s t : State) where
  frame : X.Iso (P.frame s) (P.frame t)
  knowledge : X.Equivalent (X.applyStore frame.hom (P.knowledge s)) (P.knowledge t)
  rename : O ≃ O
  present : (P.present s).map rename.toEmbedding = P.present t

namespace StateIso

variable {P}

def refl (s : State) : P.StateIso s s :=
  ⟨Frames.Iso.refl (P.frame s), Frames.Iso.equivalent_refl (P.knowledge s), Equiv.refl O, by simp⟩

def symm {s t : State} (i : P.StateIso s t) : P.StateIso t s :=
  ⟨i.frame.symm, i.frame.equivalent_symm i.knowledge, i.rename.symm, by
    rw [← i.present, Finset.map_map, ← Equiv.trans_toEmbedding, Equiv.self_trans_symm]
    simp⟩

def trans {s t u : State} (i : P.StateIso s t) (j : P.StateIso t u) : P.StateIso s u :=
  ⟨i.frame.trans j.frame, Frames.Iso.equivalent_trans i.frame j.frame i.knowledge j.knowledge,
    i.rename.trans j.rename, by rw [← j.present, ← i.present, Finset.map_map, Equiv.trans_toEmbedding]⟩

/-- A renaming that carries one set of present occurrences to another carries membership. -/
theorem mem_present_iff {s t : State} (i : P.StateIso s t) (o : O) :
    i.rename o ∈ P.present t ↔ o ∈ P.present s := by
  rw [← i.present, Finset.mem_map_equiv, Equiv.symm_apply_apply]

/-- Isomorphic states have solvable knowledge together. -/
theorem solvable_iff {s t : State} (i : P.StateIso s t) :
    X.Solvable (P.knowledge s) ↔ X.Solvable (P.knowledge t) :=
  (i.frame.solvable_applyStore_iff _).symm.trans (Frames.Equivalent.solvable_iff i.knowledge)

end StateIso

end Step

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}

/-- **Transport for the candidate step.** An instance chooses its isomorphisms of states, over the
interface's isomorphisms, and they form a groupoid. It also chooses which firings at one state are
**alike**: firings whose data agree up to the frame equivalence once their frames are identified.
Alike firings have one selection, are admitted together, and have isomorphic results. Firings move
along isomorphisms by the functor laws up to alikeness, keeping their selection and their admission,
and the results of a firing and of its transport are isomorphic. The residual of a firing after
another admitted firing is the same firing read at the other's result along the other's morphism of
frames; it keeps its selection, and transporting a residual gives, up to alikeness, the residual of
the transports. Strict transport is the case where alike firings are equal (`Transport.strict_laws`). -/
structure Transport (P : Step X O State Firing) where
  Iso : State → State → Type uI
  toStateIso : {s t : State} → Iso s t → P.StateIso s t
  refl : (s : State) → Iso s s
  symm : {s t : State} → Iso s t → Iso t s
  trans : {s t u : State} → Iso s t → Iso t u → Iso s u
  /-- Alike firings at one state: their data agree up to the frame equivalence once their frames
  are identified. -/
  Alike : {s : State} → Firing s → Firing s → Prop
  alike_equivalence : ∀ s : State, Equivalence (@Alike s)
  selection_alike : ∀ {s : State} {f f' : Firing s}, Alike f f' → P.selection f = P.selection f'
  admits_alike : ∀ {s : State} {f f' : Firing s}, Alike f f' → (P.Admits f ↔ P.Admits f')
  /-- Alike firings have isomorphic results. -/
  result_alike : ∀ {s : State} {f f' : Firing s}, Alike f f' → (admitted : P.Admits f) →
    (admitted' : P.Admits f') → Iso (P.result f admitted) (P.result f' admitted')
  move : {s t : State} → Iso s t → Firing s → Firing t
  move_alike : ∀ {s t : State} (i : Iso s t) {f f' : Firing s}, Alike f f' → Alike (move i f) (move i f')
  move_refl : ∀ {s : State} (f : Firing s), Alike (move (refl s) f) f
  move_trans : ∀ {s t u : State} (i : Iso s t) (j : Iso t u) (f : Firing s),
    Alike (move (trans i j) f) (move j (move i f))
  move_symm : ∀ {s t : State} (i : Iso s t) (f : Firing s), Alike (move (symm i) (move i f)) f
  /-- A moved firing selects the renamed occurrences. -/
  selection_move : ∀ {s t : State} (i : Iso s t) (f : Firing s),
    P.selection (move i f) = AnnotatedRuns.renameSelection (toStateIso i).rename (P.selection f)
  admits_move : ∀ {s t : State} (i : Iso s t) (f : Firing s), P.Admits (move i f) ↔ P.Admits f
  result_move : ∀ {s t : State} (i : Iso s t) (f : Firing s) (admitted : P.Admits f),
    Iso (P.result f admitted) (P.result (move i f) ((admits_move i f).mpr admitted))
  residual : {s : State} → (g : Firing s) → (admitted : P.Admits g) → Firing s →
    Firing (P.result g admitted)
  selection_residual : ∀ {s : State} (g : Firing s) (admitted : P.Admits g) (f : Firing s),
    P.selection (residual g admitted f) = P.selection f
  /-- Residuals are natural: transporting a residual is, up to alikeness, the residual of the
  transports. -/
  move_residual : ∀ {s t : State} (i : Iso s t) (g : Firing s) (admitted : P.Admits g) (f : Firing s),
    Alike (move (result_move i g admitted) (residual g admitted f))
      (residual (move i g) ((admits_move i g).mpr admitted) (move i f))

namespace Transport

variable {P : Step X O State Firing} (T : Transport P)

/-! ## Alike firings -/

namespace Alike

variable {T}

theorem refl {s : State} (f : Firing s) : T.Alike f f := (T.alike_equivalence s).refl f

theorem symm {s : State} {f f' : Firing s} (alike : T.Alike f f') : T.Alike f' f :=
  (T.alike_equivalence s).symm alike

theorem trans {s : State} {f f' f'' : Firing s} (first : T.Alike f f') (second : T.Alike f' f'') :
    T.Alike f f'' :=
  (T.alike_equivalence s).trans first second

theorem of_eq {s : State} {f f' : Firing s} (same : f = f') : T.Alike f f' := same ▸ refl f

end Alike

/-- **Strict transport is the case where alike firings are equal**: the functor laws and the
naturality of residuals then hold as equations. -/
theorem strict_laws (strict : ∀ {s : State} {f f' : Firing s}, T.Alike f f' ↔ f = f') :
    (∀ {s : State} (f : Firing s), T.move (T.refl s) f = f) ∧
    (∀ {s t u : State} (i : T.Iso s t) (j : T.Iso t u) (f : Firing s),
      T.move (T.trans i j) f = T.move j (T.move i f)) ∧
    (∀ {s t : State} (i : T.Iso s t) (f : Firing s), T.move (T.symm i) (T.move i f) = f) ∧
    (∀ {s t : State} (i : T.Iso s t) (g : Firing s) (admitted : P.Admits g) (f : Firing s),
      T.move (T.result_move i g admitted) (T.residual g admitted f) =
        T.residual (T.move i g) ((T.admits_move i g).mpr admitted) (T.move i f)) :=
  ⟨fun f => strict.mp (T.move_refl f), fun i j f => strict.mp (T.move_trans i j f),
    fun i f => strict.mp (T.move_symm i f), fun i g admitted f => strict.mp (T.move_residual i g admitted f)⟩

/-! ## State classes -/

/-- Two states are in one class when they are isomorphic. -/
abbrev Same (s t : State) : Prop := Nonempty (T.Iso s t)

theorem same_refl (s : State) : T.Same s s := ⟨T.refl s⟩

namespace Same

variable {T}

theorem symm {s t : State} (same : T.Same s t) : T.Same t s :=
  Nonempty.elim same fun i => ⟨T.symm i⟩

theorem trans {s t u : State} (first : T.Same s t) (second : T.Same t u) : T.Same s u :=
  Nonempty.elim first fun i => Nonempty.elim second fun j => ⟨T.trans i j⟩

/-- States of one class have solvable knowledge together. -/
theorem solvable_iff {s t : State} (same : T.Same s t) :
    X.Solvable (P.knowledge s) ↔ X.Solvable (P.knowledge t) :=
  Nonempty.elim same fun i => (T.toStateIso i).solvable_iff

/-- States of one class have present occurrences related by a renaming. -/
theorem present_map {s t : State} (same : T.Same s t) :
    ∃ π : O ≃ O, (P.present s).map π.toEmbedding = P.present t :=
  Nonempty.elim same fun i => ⟨_, (T.toStateIso i).present⟩

/-- Every firing admitted at one state of a class has a counterpart at every other, selecting the
renamed occurrences. -/
theorem admits {s t : State} (same : T.Same s t) {f : Firing s} (admitted : P.Admits f) :
    ∃ (π : O ≃ O) (g : Firing t) (admittedG : P.Admits g),
      P.selection g = AnnotatedRuns.renameSelection π (P.selection f) ∧
      T.Same (P.result f admitted) (P.result g admittedG) :=
  Nonempty.elim same fun i =>
    ⟨_, T.move i f, (T.admits_move i f).mpr admitted, T.selection_move i f, ⟨T.result_move i f admitted⟩⟩

end Same

/-- Alike admitted firings have results in one class. -/
theorem same_result_of_alike {s : State} {f f' : Firing s} (alike : T.Alike f f')
    (admitted : P.Admits f) (admitted' : P.Admits f') :
    T.Same (P.result f admitted) (P.result f' admitted') :=
  ⟨T.result_alike alike admitted admitted'⟩

/-- States up to isomorphism. -/
def classSetoid : Setoid State where
  r := T.Same
  iseqv := ⟨T.same_refl, Same.symm, Same.trans⟩

/-- **A state class**: a state up to isomorphism of states. -/
def StateClass : Type uS := Quotient T.classSetoid

/-- The class of a state. -/
def StateClass.mk (s : State) : T.StateClass := Quotient.mk T.classSetoid s

theorem StateClass.mk_eq_mk_iff {s t : State} : StateClass.mk T s = StateClass.mk T t ↔ T.Same s t :=
  ⟨fun same => Quotient.exact same, fun same => Quotient.sound (s := T.classSetoid) same⟩

/-- **State classes are a congruence for the step**: an isomorphism carries an admitted firing to
an admitted firing with the renamed selection, and their results are in one class. -/
theorem same_step {s t : State} (i : T.Iso s t) (f : Firing s) (admitted : P.Admits f) :
    P.Admits (T.move i f) ∧
      P.selection (T.move i f) = AnnotatedRuns.renameSelection (T.toStateIso i).rename (P.selection f) ∧
      T.Same (P.result f admitted) (P.result (T.move i f) ((T.admits_move i f).mpr admitted)) :=
  ⟨(T.admits_move i f).mpr admitted, T.selection_move i f, ⟨T.result_move i f admitted⟩⟩

/-! ## Runs along isomorphisms -/

/-- A run carried along an isomorphism of its start. -/
def moveRun : {s t : State} → T.Iso s t → P.Run s → P.Run t
  | _, t, _, .nil _ => .nil t
  | _, _, i, .cons f admitted rest =>
      .cons (T.move i f) ((T.admits_move i f).mpr admitted) (moveRun (T.result_move i f admitted) rest)

/-- **Similar runs**: firing by firing, the second is alike to the transport of the first along an
isomorphism of the states they fire at. -/
def Similar : {s t : State} → P.Run s → P.Run t → Prop
  | s, t, .nil _, .nil _ => T.Same s t
  | s, t, .cons f _ rest, .cons f' _ rest' => ∃ i : T.Iso s t, T.Alike (T.move i f) f' ∧ Similar rest rest'
  | _, _, .nil _, .cons _ _ _ => False
  | _, _, .cons _ _ _, .nil _ => False

variable {T}

theorem similar_nil_nil {s t : State} : T.Similar (.nil s : P.Run s) (.nil t : P.Run t) ↔ T.Same s t :=
  Iff.rfl

theorem similar_cons_cons {s t : State} {f : Firing s} {admitted : P.Admits f}
    {rest : P.Run (P.result f admitted)} {f' : Firing t} {admitted' : P.Admits f'}
    {rest' : P.Run (P.result f' admitted')} :
    T.Similar (.cons f admitted rest) (.cons f' admitted' rest') ↔
      ∃ i : T.Iso s t, T.Alike (T.move i f) f' ∧ T.Similar rest rest' :=
  Iff.rfl

/-- For a strict transport, similar runs are transports of each other on the nose. -/
theorem similar_cons_cons_of_strict (strict : ∀ {s : State} {f f' : Firing s}, T.Alike f f' ↔ f = f')
    {s t : State} {f : Firing s} {admitted : P.Admits f}
    {rest : P.Run (P.result f admitted)} {f' : Firing t} {admitted' : P.Admits f'}
    {rest' : P.Run (P.result f' admitted')} :
    T.Similar (.cons f admitted rest) (.cons f' admitted' rest') ↔
      ∃ i : T.Iso s t, T.move i f = f' ∧ T.Similar rest rest' := by
  rw [similar_cons_cons]
  exact exists_congr fun _ => and_congr_left' strict

theorem not_similar_nil_cons {s t : State} {f' : Firing t} {admitted' : P.Admits f'}
    {rest' : P.Run (P.result f' admitted')} : ¬ T.Similar (.nil s : P.Run s) (.cons f' admitted' rest') :=
  id

theorem not_similar_cons_nil {s t : State} {f : Firing s} {admitted : P.Admits f}
    {rest : P.Run (P.result f admitted)} : ¬ T.Similar (.cons f admitted rest) (.nil t : P.Run t) :=
  id

namespace Similar

theorem refl {s : State} (r : P.Run s) : T.Similar r r := by
  induction r with
  | nil s => exact similar_nil_nil.mpr (T.same_refl s)
  | cons f admitted rest ih => exact similar_cons_cons.mpr ⟨T.refl _, T.move_refl f, ih⟩

theorem symm : ∀ {s t : State} {r : P.Run s} {r' : P.Run t}, T.Similar r r' → T.Similar r' r
  | _, _, .nil _, .nil _, similar => similar_nil_nil.mpr (Same.symm (similar_nil_nil.mp similar))
  | _, _, .cons f _ _, .cons f' _ _, similar => by
      obtain ⟨i, moved, tail⟩ := similar_cons_cons.mp similar
      exact similar_cons_cons.mpr ⟨T.symm i,
        (T.move_alike (T.symm i) moved).symm.trans (T.move_symm i f), symm tail⟩
  | _, _, .nil _, .cons _ _ _, similar => False.elim similar
  | _, _, .cons _ _ _, .nil _, similar => False.elim similar

theorem trans : ∀ {s t u : State} {r : P.Run s} {r' : P.Run t} {r'' : P.Run u},
    T.Similar r r' → T.Similar r' r'' → T.Similar r r''
  | _, _, _, .nil _, .nil _, .nil _, first, second =>
      similar_nil_nil.mpr (Same.trans (similar_nil_nil.mp first) (similar_nil_nil.mp second))
  | _, _, _, .cons f _ _, .cons _ _ _, .cons _ _ _, first, second => by
      obtain ⟨i, moved, tail⟩ := similar_cons_cons.mp first
      obtain ⟨j, moved', tail'⟩ := similar_cons_cons.mp second
      exact similar_cons_cons.mpr ⟨T.trans i j,
        (T.move_trans i j f).trans ((T.move_alike j moved).trans moved'), trans tail tail'⟩
  | _, _, _, .nil _, .cons _ _ _, _, first, _ => False.elim first
  | _, _, _, .cons _ _ _, .nil _, _, first, _ => False.elim first
  | _, _, _, .nil _, .nil _, .cons _ _ _, _, second => False.elim second
  | _, _, _, .cons _ _ _, .cons _ _ _, .nil _, _, second => False.elim second

/-- Similar runs start in one class. -/
theorem same_start : ∀ {s t : State} {r : P.Run s} {r' : P.Run t}, T.Similar r r' → T.Same s t
  | _, _, .nil _, .nil _, similar => similar_nil_nil.mp similar
  | _, _, .cons _ _ _, .cons _ _ _, similar => by
      obtain ⟨i, -, -⟩ := similar_cons_cons.mp similar
      exact ⟨i⟩
  | _, _, .nil _, .cons _ _ _, similar => False.elim similar
  | _, _, .cons _ _ _, .nil _, similar => False.elim similar

/-- Similar runs end in one class. -/
theorem same_last : ∀ {s t : State} {r : P.Run s} {r' : P.Run t}, T.Similar r r' → T.Same r.last r'.last
  | _, _, .nil _, .nil _, similar => similar_nil_nil.mp similar
  | _, _, .cons _ _ _, .cons _ _ _, similar => by
      obtain ⟨-, -, tail⟩ := similar_cons_cons.mp similar
      have later := same_last tail
      exact later
  | _, _, .nil _, .cons _ _ _, similar => False.elim similar
  | _, _, .cons _ _ _, .nil _, similar => False.elim similar

/-- **Similarity is compatible with concatenation.** -/
theorem append : ∀ {s t : State} {r : P.Run s} {r' : P.Run t}, T.Similar r r' →
    ∀ {q : P.Run r.last} {q' : P.Run r'.last}, T.Similar q q' → T.Similar (r.append q) (r'.append q')
  | _, _, .nil _, .nil _, _, _, _, similar => similar
  | _, _, .cons _ _ _, .cons _ _ _, first, _, _, similar => by
      obtain ⟨i, moved, tail⟩ := similar_cons_cons.mp first
      exact similar_cons_cons.mpr ⟨i, moved, append tail similar⟩
  | _, _, .nil _, .cons _ _ _, first, _, _, _ => False.elim first
  | _, _, .cons _ _ _, .nil _, first, _, _, _ => False.elim first

/-- Prefixing one firing keeps similarity. -/
theorem cons_self {s : State} {f : Firing s} {admitted : P.Admits f}
    {r r' : P.Run (P.result f admitted)} (similar : T.Similar r r') :
    T.Similar (.cons f admitted r) (.cons f admitted r') :=
  similar_cons_cons.mpr ⟨T.refl s, T.move_refl f, similar⟩

/-- **Prefixing alike firings keeps similarity.** -/
theorem cons_alike {s : State} {f f' : Firing s} (alike : T.Alike f f') (admitted : P.Admits f)
    (admitted' : P.Admits f') {r : P.Run (P.result f admitted)} {r' : P.Run (P.result f' admitted')}
    (similar : T.Similar r r') : T.Similar (.cons f admitted r) (.cons f' admitted' r') :=
  similar_cons_cons.mpr ⟨T.refl s, (T.move_refl f).trans alike, similar⟩

/-- A run is similar to its transport. -/
theorem moveRun : ∀ {s t : State} (i : T.Iso s t) (r : P.Run s), T.Similar r (T.moveRun i r)
  | _, _, i, .nil _ => similar_nil_nil.mpr ⟨i⟩
  | _, _, i, .cons f admitted rest =>
      similar_cons_cons.mpr ⟨i, Alike.refl _, moveRun (T.result_move i f admitted) rest⟩

/-- **Similar runs have the same site accounts** when grades are invariant under transport and
under alikeness. -/
theorem account_eq {M : Type*} [Monoid M] (grade : (t : State) → Firing t → M)
    (invariant : ∀ {s t : State} (i : T.Iso s t) (f : Firing s), grade t (T.move i f) = grade s f)
    (alike : ∀ {s : State} {f f' : Firing s}, T.Alike f f' → grade s f = grade s f') :
    ∀ {s t : State} {r : P.Run s} {r' : P.Run t}, T.Similar r r' →
      r.account grade = r'.account grade
  | _, _, .nil _, .nil _, _ => rfl
  | _, _, .cons f _ _, .cons f' _ _, similar => by
      obtain ⟨i, moved, tail⟩ := similar_cons_cons.mp similar
      have head : grade _ f' = grade _ f := (alike moved).symm.trans (invariant i f)
      show grade _ f * _ = grade _ f' * _
      rw [head, account_eq grade invariant alike tail]
  | _, _, .nil _, .cons _ _ _, similar => False.elim similar
  | _, _, .cons _ _ _, .nil _, similar => False.elim similar

end Similar

end Transport

#print axioms renameSelection_refl
#print axioms forall₂_swap
#print axioms forall₂_comp
#print axioms Frames.equivalent_of_forall₂
#print axioms Frames.Iso.solvable_applyStore_iff
#print axioms Frames.Iso.equivalent_symm
#print axioms Frames.Iso.equivalent_trans
#print axioms Frames.Carried.symm
#print axioms Frames.Carried.trans
#print axioms Step.StateIso.solvable_iff
#print axioms Transport.strict_laws
#print axioms Transport.same_step
#print axioms Transport.same_result_of_alike
#print axioms Transport.Same.admits
#print axioms Transport.Same.solvable_iff
#print axioms Transport.similar_cons_cons_of_strict
#print axioms Transport.Similar.symm
#print axioms Transport.Similar.trans
#print axioms Transport.Similar.same_last
#print axioms Transport.Similar.append
#print axioms Transport.Similar.cons_alike
#print axioms Transport.Similar.moveRun
#print axioms Transport.Similar.account_eq

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
