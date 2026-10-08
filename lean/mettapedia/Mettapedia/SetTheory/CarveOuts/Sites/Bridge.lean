import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogic
import Mettapedia.SetTheory.CarveOuts.HeytingValued.DoubleNegation
import Mettapedia.GSLT.Core.NonFactorization
import Mathlib.CategoryTheory.Action.Concrete
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# The truth values of contextual forcing

Contextual forcing (`ContextualMaterialLogic.force`) reads a formula at a context `s` of a
category, with an environment of values at `s`; implication and the universal quantifier look
along every arrow out of `s`. This module says what its truth values are.

**Any category: cosieves.** The truth value of a formula at `s` is the set of arrows out of `s`
along which it is forced (`cosieveValue`). These sets are closed under composition after them:
they are the cosieves on `s`, which form a frame (`Cosieve.frame`, built by hand; nothing in it
uses choice). Forcing at `s` is membership of the identity (`force_iff_mem_id`), and the
connectives are the frame operations: `cosieveValue_both`, `cosieveValue_either`,
`cosieveValue_bottom`, and `cosieveValue_imply` (Kripke implication is the Heyting implication
of cosieves). The quantifiers are read at the target of each arrow (`mem_cosieveValue_all`,
`mem_cosieveValue_exist`). Truth values move along arrows by pulling back
(`cosieveValue_transport`): they form a presheaf of frames, one frame for each context.

**A preorder of stages: `Persistent P`.** Over a preorder `P` (its category has at most one
arrow between two stages) every one of these frames sits inside the one frame `Persistent P`
of up-closed propositions. The persistent value of a formula (`persistentValue`) holds at the
stages above `s` at which the formula is forced, and

* forcing at `s` is the persistent value at `s` (`force_iff_persistentValue`);
* conjunction, disjunction and falsity are meet, join and bottom of `Persistent P`
  (`persistentValue_both`, `persistentValue_either`, `persistentValue_bottom`);
* implication is the Heyting implication relativised to the stages above `s`
  (`persistentValue_imply`), and for sentences it is exactly the Heyting implication
  (`sentenceValue_imply`);
* the existential quantifier is a join and the universal quantifier a relativised meet of
  the values of the body over later stages and values there (`persistentValue_exist`,
  `persistentValue_all`).

**Where it breaks: a genuine category.** For any category the stages reachable from `s` form a
preorder (`Reach`), and a cosieve has a reading there, the stages it reaches (`Cosieve.reach`).
This reading keeps joins and falsity in every category (`reach_sup`, `reach_bot`), and over a
preorder it forgets nothing (`reach_injective_of_preorder`). It fails in two ways:

* **parallel arrows**: on the walking parallel pair, a formula and its negation are forced
  along the two different arrows into the same stage. Their reaches agree, their cosieves do not
  (`fiber_reach_parallel`), and the reading does not keep meets (`reach_inf_ne`);
* **a non-identity endomorphism**: in the monoid with an idempotent `collapse`, two different
  values become equal after collapsing. The formula `x = y` is forced after the endomorphism and
  not before it, so the reach holds at the context although the formula is not forced there
  (`reach_holds_not_force`); the reading forgets the verdict at the identity
  (`fiber_reach_idempotent`). The cosieves of this one-object category are not determined by
  the identity (`collapseCosieve`), unlike those of a group (see `GSets`).
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts.Sites

open CategoryTheory
open Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogic
open Mettapedia.SetTheory.CarveOuts.HeytingValued
open Mettapedia.GSLT.Core.NonFactorization

universe u v

/-! ## Cosieves -/

/-- A cosieve on a context `s`: arrows out of `s`, closed under composition after them. -/
structure Cosieve {D : Type u} [Category.{u} D] (s : D) where
  mem : (t : D) → (s ⟶ t) → Prop
  comp_mem : ∀ {t w : D} (f : s ⟶ t) (g : t ⟶ w), mem t f → mem w (f ≫ g)

namespace Cosieve

variable {D : Type u} [Category.{u} D] {s : D}

theorem ext' {A B : Cosieve s} (h : ∀ t f, A.mem t f ↔ B.mem t f) : A = B := by
  cases A
  cases B
  congr
  funext t f
  exact propext (h t f)

/-- Cosieves form a frame. Meets and joins are pointwise; implication looks along every later
arrow. Nothing uses choice. -/
instance frame : Order.Frame (Cosieve s) where
  le A B := ∀ t f, A.mem t f → B.mem t f
  lt A B := (∀ t f, A.mem t f → B.mem t f) ∧ ¬ ∀ t f, B.mem t f → A.mem t f
  le_refl _ _ _ h := h
  le_trans _ _ _ hAB hBC t f h := hBC t f (hAB t f h)
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_antisymm _ _ hAB hBA := ext' fun t f => ⟨hAB t f, hBA t f⟩
  sup A B := ⟨fun t f => A.mem t f ∨ B.mem t f, fun f g h => h.imp (A.comp_mem f g) (B.comp_mem f g)⟩
  le_sup_left _ _ _ _ h := Or.inl h
  le_sup_right _ _ _ _ h := Or.inr h
  sup_le _ _ _ hA hB t f h := h.elim (hA t f) (hB t f)
  inf A B := ⟨fun t f => A.mem t f ∧ B.mem t f, fun f g h => h.imp (A.comp_mem f g) (B.comp_mem f g)⟩
  inf_le_left _ _ _ _ h := h.1
  inf_le_right _ _ _ _ h := h.2
  le_inf _ _ _ hB hC t f h := ⟨hB t f h, hC t f h⟩
  sSup S := ⟨fun t f => ∃ A ∈ S, A.mem t f, fun f g ⟨A, hA, h⟩ => ⟨A, hA, A.comp_mem f g h⟩⟩
  isLUB_sSup _ := ⟨fun A hA _ _ h => ⟨A, hA, h⟩, fun _ h t f ⟨A, hA, hf⟩ => h hA t f hf⟩
  sInf S := ⟨fun t f => ∀ A ∈ S, A.mem t f, fun f g h A hA => A.comp_mem f g (h A hA)⟩
  isGLB_sInf _ := ⟨fun A hA _ _ h => h A hA, fun _ h t f hf A hA => h hA t f hf⟩
  top := ⟨fun _ _ => True, fun _ _ _ => trivial⟩
  le_top _ _ _ _ := trivial
  bot := ⟨fun _ _ => False, fun _ _ h => h⟩
  bot_le _ _ _ h := h.elim
  himp A B := ⟨fun t f => ∀ w (g : t ⟶ w), A.mem w (f ≫ g) → B.mem w (f ≫ g),
    fun f g h w k hA => by
      rw [Category.assoc] at hA ⊢
      exact h w (g ≫ k) hA⟩
  le_himp_iff Z A B := by
    constructor
    · intro h t f ⟨hZ, hA⟩
      have := h t f hZ t (𝟙 t)
      rw [Category.comp_id] at this
      exact this hA
    · intro h t f hZ w g hA
      exact h w (f ≫ g) ⟨Z.comp_mem f g hZ, hA⟩
  compl A := ⟨fun t f => ∀ w (g : t ⟶ w), A.mem w (f ≫ g) → False,
    fun f g h w k hA => by
      rw [Category.assoc] at hA
      exact h w (g ≫ k) hA⟩
  himp_bot _ := rfl

theorem mem_inf (A B : Cosieve s) (t : D) (f : s ⟶ t) :
    (A ⊓ B).mem t f ↔ A.mem t f ∧ B.mem t f :=
  Iff.rfl

theorem mem_sup (A B : Cosieve s) (t : D) (f : s ⟶ t) :
    (A ⊔ B).mem t f ↔ A.mem t f ∨ B.mem t f :=
  Iff.rfl

theorem mem_himp (A B : Cosieve s) (t : D) (f : s ⟶ t) :
    (A ⇨ B).mem t f ↔ ∀ w (g : t ⟶ w), A.mem w (f ≫ g) → B.mem w (f ≫ g) :=
  Iff.rfl

theorem not_mem_bot (t : D) (f : s ⟶ t) : ¬ (⊥ : Cosieve s).mem t f :=
  id

theorem mem_top (t : D) (f : s ⟶ t) : (⊤ : Cosieve s).mem t f :=
  trivial

/-- Pulling a cosieve back along an arrow. -/
def pullback {t : D} (f : s ⟶ t) (S : Cosieve s) : Cosieve t where
  mem w g := S.mem w (f ≫ g)
  comp_mem g k h := by
    rw [← Category.assoc]
    exact S.comp_mem _ k h

end Cosieve

/-! ## Truth values of forcing over any category -/

section AnyCategory

variable {D : Type u} [Category.{u} D] {values : D ⥤ Type v} (model : Model values)

/-- The truth value of a formula at a context: the arrows out of it along which the formula is
forced. -/
def cosieveValue {n : ℕ} (φ : Formula n) (s : D) (env : Environment values n s) : Cosieve s where
  mem t f := force values model φ t (transport values f env)
  comp_mem f g h := by
    rw [transport_comp]
    exact force_transport model φ g _ h

/-- **Forcing is membership of the identity.** -/
theorem force_iff_mem_id {n : ℕ} (φ : Formula n) (s : D) (env : Environment values n s) :
    force values model φ s env ↔ (cosieveValue model φ s env).mem s (𝟙 s) := by
  show _ ↔ force values model φ s (transport values (𝟙 s) env)
  rw [transport_id]

theorem cosieveValue_bottom {n : ℕ} (s : D) (env : Environment values n s) :
    cosieveValue model (.bottom : Formula n) s env = ⊥ :=
  Cosieve.ext' fun _ _ => Iff.rfl

theorem cosieveValue_both {n : ℕ} (φ ψ : Formula n) (s : D) (env : Environment values n s) :
    cosieveValue model (.both φ ψ) s env = cosieveValue model φ s env ⊓ cosieveValue model ψ s env :=
  Cosieve.ext' fun _ _ => Iff.rfl

theorem cosieveValue_either {n : ℕ} (φ ψ : Formula n) (s : D) (env : Environment values n s) :
    cosieveValue model (.either φ ψ) s env =
      cosieveValue model φ s env ⊔ cosieveValue model ψ s env :=
  Cosieve.ext' fun _ _ => Iff.rfl

/-- **Kripke implication is the Heyting implication of cosieves.** -/
theorem cosieveValue_imply {n : ℕ} (φ ψ : Formula n) (s : D) (env : Environment values n s) :
    cosieveValue model (.imply φ ψ) s env =
      cosieveValue model φ s env ⇨ cosieveValue model ψ s env := by
  refine Cosieve.ext' fun t f => ?_
  show (∀ (w : D) (g : t ⟶ w), force values model φ w (transport values g (transport values f env)) →
      force values model ψ w (transport values g (transport values f env))) ↔
    ∀ (w : D) (g : t ⟶ w), force values model φ w (transport values (f ≫ g) env) →
      force values model ψ w (transport values (f ≫ g) env)
  simp only [transport_comp]

/-- The universal quantifier, read at the target of each arrow. -/
theorem mem_cosieveValue_all {n : ℕ} (body : Formula (n + 1)) (s : D)
    (env : Environment values n s) (t : D) (f : s ⟶ t) :
    (cosieveValue model (.all body) s env).mem t f ↔
      ∀ (w : D) (g : t ⟶ w) (value : values.obj w),
        force values model body w (extend values (transport values (f ≫ g) env) value) := by
  show (∀ (w : D) (g : t ⟶ w) (value : values.obj w),
      force values model body w (extend values (transport values g (transport values f env)) value)) ↔ _
  simp only [transport_comp]

/-- The existential quantifier, read at the target of each arrow. -/
theorem mem_cosieveValue_exist {n : ℕ} (body : Formula (n + 1)) (s : D)
    (env : Environment values n s) (t : D) (f : s ⟶ t) :
    (cosieveValue model (.exist body) s env).mem t f ↔
      ∃ value : values.obj t, force values model body t (extend values (transport values f env) value) :=
  Iff.rfl

/-- **Truth values form a presheaf of frames.** Transporting the environment pulls the truth
value back. -/
theorem cosieveValue_transport {n : ℕ} (φ : Formula n) {s t : D} (f : s ⟶ t)
    (env : Environment values n s) :
    cosieveValue model φ t (transport values f env) = (cosieveValue model φ s env).pullback f := by
  refine Cosieve.ext' fun w g => ?_
  show force values model φ w (transport values g (transport values f env)) ↔
    force values model φ w (transport values (f ≫ g) env)
  rw [transport_comp]

end AnyCategory

/-! ## A preorder of stages: the frame `Persistent P` -/

namespace Persistent

variable {P : Type u} [Preorder P]

/-- The stages from `s` on. -/
def up (s : P) : Persistent P :=
  ⟨fun t => s ≤ t, fun hst hs => le_trans hs hst⟩

theorem holds_inf (x y : Persistent P) (s : P) : (x ⊓ y).holds s ↔ x.holds s ∧ y.holds s :=
  Iff.rfl

theorem holds_himp (x y : Persistent P) (s : P) :
    (x ⇨ y).holds s ↔ ∀ t, s ≤ t → x.holds t → y.holds t :=
  Iff.rfl

theorem holds_iSup {ι : Sort*} (f : ι → Persistent P) (s : P) :
    (⨆ i, f i).holds s ↔ ∃ i, (f i).holds s := by
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, h⟩
    exact ⟨i, h⟩
  · rintro ⟨i, h⟩
    exact ⟨f i, ⟨i, rfl⟩, h⟩

theorem holds_iInf {ι : Sort*} (f : ι → Persistent P) (s : P) :
    (⨅ i, f i).holds s ↔ ∀ i, (f i).holds s := by
  constructor
  · intro h i
    exact h (f i) ⟨i, rfl⟩
  · rintro h _ ⟨i, rfl⟩
    exact h i

theorem holds_bot (s : P) : ¬ (⊥ : Persistent P).holds s :=
  id

end Persistent

section Preorder

variable {P : Type u} [Preorder P] {values : P ⥤ Type v} (model : Model values)

/-- In a preorder, transport does not depend on the arrow. -/
theorem transport_thin {n : ℕ} {s t : P} (f g : s ⟶ t) (env : Environment values n s) :
    transport values f env = transport values g env := by
  rw [Subsingleton.elim f g]

/-- The persistent value of a formula with an environment at `s`: the stages above `s` at
which it is forced. -/
def persistentValue {n : ℕ} (φ : Formula n) (s : P) (env : Environment values n s) :
    Persistent P where
  holds t := ∃ h : s ≤ t, force values model φ t (transport values (homOfLE h) env)
  mono {t w} htw := fun ⟨h, hf⟩ => ⟨le_trans h htw, by
    have later := force_transport model φ (homOfLE htw) _ hf
    rw [← transport_comp, transport_thin (homOfLE h ≫ homOfLE htw)
      (homOfLE (le_trans h htw))] at later
    exact later⟩

theorem persistentValue_holds_iff {n : ℕ} (φ : Formula n) (s t : P) (env : Environment values n s)
    (f : s ⟶ t) :
    (persistentValue model φ s env).holds t ↔ force values model φ t (transport values f env) := by
  constructor
  · rintro ⟨h, hf⟩
    rwa [transport_thin f (homOfLE h)]
  · intro hf
    exact ⟨leOfHom f, by rwa [transport_thin (homOfLE (leOfHom f)) f]⟩

/-- **The bridge.** Over a preorder, forcing at `s` is the persistent value at `s`. -/
theorem force_iff_persistentValue {n : ℕ} (φ : Formula n) (s : P) (env : Environment values n s) :
    force values model φ s env ↔ (persistentValue model φ s env).holds s := by
  rw [persistentValue_holds_iff model φ s s env (𝟙 s), transport_id]

theorem persistentValue_le_up {n : ℕ} (φ : Formula n) (s : P) (env : Environment values n s) :
    persistentValue model φ s env ≤ Persistent.up s := fun _ ⟨h, _⟩ => h

theorem persistentValue_bottom {n : ℕ} (s : P) (env : Environment values n s) :
    persistentValue model (.bottom : Formula n) s env = ⊥ :=
  Persistent.ext (funext fun _ => propext ⟨fun ⟨_, h⟩ => h, False.elim⟩)

/-- Conjunction is the meet. -/
theorem persistentValue_both {n : ℕ} (φ ψ : Formula n) (s : P) (env : Environment values n s) :
    persistentValue model (.both φ ψ) s env =
      persistentValue model φ s env ⊓ persistentValue model ψ s env :=
  Persistent.ext (funext fun _ => propext
    ⟨fun ⟨h, hφ, hψ⟩ => ⟨⟨h, hφ⟩, ⟨h, hψ⟩⟩, fun ⟨⟨h, hφ⟩, ⟨_, hψ⟩⟩ => ⟨h, hφ, hψ⟩⟩)

/-- Disjunction is the join. -/
theorem persistentValue_either {n : ℕ} (φ ψ : Formula n) (s : P) (env : Environment values n s) :
    persistentValue model (.either φ ψ) s env =
      persistentValue model φ s env ⊔ persistentValue model ψ s env :=
  Persistent.ext (funext fun _ => propext
    ⟨fun ⟨h, hor⟩ => hor.imp (fun hφ => ⟨h, hφ⟩) (fun hψ => ⟨h, hψ⟩),
      fun hor => hor.elim (fun ⟨h, hφ⟩ => ⟨h, Or.inl hφ⟩) (fun ⟨h, hψ⟩ => ⟨h, Or.inr hψ⟩)⟩)

/-- **Implication is the Heyting implication**, relativised to the stages above `s`. -/
theorem persistentValue_imply {n : ℕ} (φ ψ : Formula n) (s : P) (env : Environment values n s) :
    persistentValue model (.imply φ ψ) s env =
      Persistent.up s ⊓ (persistentValue model φ s env ⇨ persistentValue model ψ s env) := by
  refine Persistent.ext (funext fun t => propext ⟨?_, ?_⟩)
  · rintro ⟨h, himp⟩
    refine ⟨h, fun w htw hφ => ?_⟩
    have hφ' := (persistentValue_holds_iff model φ s w env (homOfLE h ≫ homOfLE htw)).mp hφ
    rw [transport_comp] at hφ'
    have hψ := himp w (homOfLE htw) hφ'
    rw [← transport_comp] at hψ
    exact (persistentValue_holds_iff model ψ s w env _).mpr hψ
  · rintro ⟨h, himp⟩
    refine ⟨h, fun w g hφ => ?_⟩
    rw [← transport_comp] at hφ ⊢
    exact (persistentValue_holds_iff model ψ s w env _).mp
      (himp w (leOfHom g) ((persistentValue_holds_iff model φ s w env _).mpr hφ))

/-- **The existential quantifier is a join**, over later stages and values there. -/
theorem persistentValue_exist {n : ℕ} (body : Formula (n + 1)) (s : P)
    (env : Environment values n s) :
    persistentValue model (.exist body) s env =
      ⨆ (t : P) (h : s ≤ t) (value : values.obj t),
        persistentValue model body t (extend values (transport values (homOfLE h) env) value) := by
  refine Persistent.ext (funext fun w => propext ⟨?_, ?_⟩)
  · rintro ⟨h, value, hbody⟩
    refine (Persistent.holds_iSup _ _).mpr ⟨w, (Persistent.holds_iSup _ _).mpr ⟨h,
      (Persistent.holds_iSup _ _).mpr ⟨value, ?_⟩⟩⟩
    refine (persistentValue_holds_iff model body w w _ (𝟙 w)).mpr ?_
    rwa [transport_id]
  · intro hsup
    obtain ⟨t, hsup⟩ := (Persistent.holds_iSup _ _).mp hsup
    obtain ⟨h, hsup⟩ := (Persistent.holds_iSup _ _).mp hsup
    obtain ⟨value, ⟨htw, hbody⟩⟩ := (Persistent.holds_iSup _ _).mp hsup
    refine ⟨le_trans h htw, values.map (homOfLE htw) value, ?_⟩
    rw [transport_extend, ← transport_comp,
      transport_thin (homOfLE h ≫ homOfLE htw) (homOfLE (le_trans h htw))] at hbody
    exact hbody

/-- **The universal quantifier is a relativised meet**, over later stages and values there. -/
theorem persistentValue_all {n : ℕ} (body : Formula (n + 1)) (s : P)
    (env : Environment values n s) :
    persistentValue model (.all body) s env =
      Persistent.up s ⊓ ⨅ (t : P) (h : s ≤ t) (value : values.obj t),
        (Persistent.up t ⇨
          persistentValue model body t (extend values (transport values (homOfLE h) env) value)) := by
  refine Persistent.ext (funext fun w => propext ⟨?_, ?_⟩)
  · rintro ⟨hsw, hall⟩
    refine ⟨hsw, (Persistent.holds_iInf _ _).mpr fun t => (Persistent.holds_iInf _ _).mpr
      fun h => (Persistent.holds_iInf _ _).mpr fun value => ?_⟩
    intro x hwx htx
    refine (persistentValue_holds_iff model body t x _ (homOfLE htx)).mpr ?_
    have hx := hall x (homOfLE hwx) (values.map (homOfLE htx) value)
    rw [transport_extend, ← transport_comp]
    rwa [← transport_comp, transport_thin (homOfLE hsw ≫ homOfLE hwx) (homOfLE h ≫ homOfLE htx)]
      at hx
  · rintro ⟨hsw, hall⟩
    refine ⟨hsw, fun x g value => ?_⟩
    have hx := (Persistent.holds_iInf _ _).mp ((Persistent.holds_iInf _ _).mp
      ((Persistent.holds_iInf _ _).mp hall x) (le_trans hsw (leOfHom g))) value x (leOfHom g) le_rfl
    rw [persistentValue_holds_iff model body x x _ (𝟙 x), transport_id] at hx
    rwa [← transport_comp, transport_thin (homOfLE hsw ≫ g)
      (homOfLE (le_trans hsw (leOfHom g)))]

/-- The empty environment of a sentence. -/
def emptyEnvironment (s : P) : Environment values 0 s :=
  Fin.elim0

theorem transport_emptyEnvironment {s t : P} (f : s ⟶ t) :
    transport values f (emptyEnvironment (values := values) s) = emptyEnvironment t :=
  funext fun i => i.elim0

/-- The truth value of a sentence: the stages at which it is forced. -/
def sentenceValue (φ : Formula 0) : Persistent P where
  holds t := force values model φ t (emptyEnvironment t)
  mono {_ _} h hf := by
    have later := force_transport model φ (homOfLE h) _ hf
    rwa [transport_emptyEnvironment] at later

/-- **For sentences, implication is exactly the Heyting implication of `Persistent P`.** -/
theorem sentenceValue_imply (φ ψ : Formula 0) :
    sentenceValue model (.imply φ ψ) = sentenceValue model φ ⇨ sentenceValue model ψ := by
  refine Persistent.ext (funext fun t => propext ⟨?_, ?_⟩)
  · intro himp w htw hφ
    have := himp w (homOfLE htw)
    rw [transport_emptyEnvironment] at this
    exact this hφ
  · intro himp w g hφ
    rw [transport_emptyEnvironment] at hφ ⊢
    exact himp w (leOfHom g) hφ

theorem sentenceValue_both (φ ψ : Formula 0) :
    sentenceValue model (.both φ ψ) = sentenceValue model φ ⊓ sentenceValue model ψ :=
  rfl

theorem sentenceValue_either (φ ψ : Formula 0) :
    sentenceValue model (.either φ ψ) = sentenceValue model φ ⊔ sentenceValue model ψ :=
  rfl

theorem sentenceValue_bottom : sentenceValue model (.bottom : Formula 0) = ⊥ :=
  rfl

/-- A sentence's value is its persistent value at each stage. -/
theorem sentenceValue_holds_iff (φ : Formula 0) (s : P) :
    (sentenceValue model φ).holds s ↔ (persistentValue model φ s (emptyEnvironment s)).holds s :=
  force_iff_persistentValue model φ s _

end Preorder

/-! ## The reach of a cosieve, in any category -/

/-- The stages reachable from a context, as a preorder. -/
def Reach (D : Type u) : Type u :=
  D

instance (D : Type u) [Category.{u} D] : Preorder (Reach D) where
  le s t := Nonempty (@Quiver.Hom D _ s t)
  le_refl s := ⟨@CategoryStruct.id D _ s⟩
  le_trans _ _ _ := fun ⟨f⟩ ⟨g⟩ => ⟨@CategoryStruct.comp D _ _ _ _ f g⟩

namespace Cosieve

variable {D : Type u} [Category.{u} D] {s : D}

/-- The stages a cosieve reaches. -/
def reach (S : Cosieve s) : Persistent (Reach D) where
  holds t := ∃ f : s ⟶ t, S.mem t f
  mono {t w} htw h := by
    obtain ⟨g⟩ : Nonempty (@Quiver.Hom D _ t w) := htw
    obtain ⟨f, hf⟩ := h
    exact ⟨f ≫ g, S.comp_mem f g hf⟩

theorem reach_sup (A B : Cosieve s) : (A ⊔ B).reach = A.reach ⊔ B.reach :=
  Persistent.ext (funext fun _ => propext
    ⟨fun ⟨f, h⟩ => h.imp (fun hA => ⟨f, hA⟩) (fun hB => ⟨f, hB⟩),
      fun h => h.elim (fun ⟨f, hA⟩ => ⟨f, Or.inl hA⟩) (fun ⟨f, hB⟩ => ⟨f, Or.inr hB⟩)⟩)

theorem reach_bot : (⊥ : Cosieve s).reach = ⊥ :=
  Persistent.ext (funext fun _ => propext ⟨fun ⟨_, h⟩ => h, False.elim⟩)

theorem reach_inf_le (A B : Cosieve s) : (A ⊓ B).reach ≤ A.reach ⊓ B.reach :=
  fun _ ⟨f, hA, hB⟩ => ⟨⟨f, hA⟩, ⟨f, hB⟩⟩

/-- **Over a preorder the reach forgets nothing.** -/
theorem reach_injective_of_preorder {P : Type u} [Preorder P] {s : P} {A B : Cosieve s}
    (h : A.reach = B.reach) : A = B := by
  refine ext' fun t f => ⟨fun hA => ?_, fun hB => ?_⟩
  · obtain ⟨g, hg⟩ := (congrArg (fun x : Persistent (Reach P) => x.holds t) h ▸ ⟨f, hA⟩ :
      B.reach.holds t)
    rwa [Subsingleton.elim g f] at hg
  · obtain ⟨g, hg⟩ := (congrArg (fun x : Persistent (Reach P) => x.holds t) h ▸ ⟨f, hB⟩ :
      A.reach.holds t)
    rwa [Subsingleton.elim g f] at hg

end Cosieve

/-- Forcing at a context implies that its truth value reaches the context. -/
theorem reach_of_force {D : Type u} [Category.{u} D] {values : D ⥤ Type v} (model : Model values)
    {n : ℕ} (φ : Formula n) (s : D) (env : Environment values n s)
    (h : force values model φ s env) : (cosieveValue model φ s env).reach.holds s :=
  ⟨𝟙 s, (force_iff_mem_id model φ s env).mp h⟩

/-! ## Parallel arrows -/

namespace Parallel

open CategoryTheory.Limits WalkingParallelPair WalkingParallelPairHom

/-- The walking parallel pair, with one value at `zero` sent along `left` to `true` and along
`right` to `false`. -/
def values : WalkingParallelPair ⥤ Type :=
  parallelPair (TypeCat.ofHom fun _ : Unit => true) (TypeCat.ofHom fun _ : Unit => false)

/-- Membership holds only of `true` in itself, at `one`. -/
def model : Model values where
  member point := match point with
    | zero => fun _ _ => False
    | one => fun (a b : Bool) => a = true ∧ b = true
  member_transport := by
    intro point target arrow child parent h
    cases arrow with
    | left => exact h.elim
    | right => exact h.elim
    | id => exact h

/-- `x ∈ x`. -/
def selfMember : Formula 1 :=
  .member 0 0

/-- `¬ (x ∈ x)`. -/
def notSelfMember : Formula 1 :=
  .imply selfMember .bottom

/-- The value at `zero`. -/
def env : Environment values 1 zero :=
  fun _ => ()

theorem force_left : force values model selfMember one (transport values left env) :=
  ⟨rfl, rfl⟩

theorem not_force_right : ¬ force values model selfMember one (transport values right env) :=
  fun h => Bool.false_ne_true h.1

theorem force_not_right : force values model notSelfMember one (transport values right env) := by
  intro w g h
  cases g
  exact not_force_right h

theorem not_force_not_left : ¬ force values model notSelfMember one (transport values left env) :=
  fun h => h one (𝟙 one) (by rw [transport_id]; exact force_left)

theorem not_force_zero (e : Environment values 1 zero) : ¬ force values model selfMember zero e :=
  fun h => h

theorem not_force_not_zero : ¬ force values model notSelfMember zero env :=
  fun h => h one left force_left

/-- The truth value of `x ∈ x`: the arrow `left`. -/
abbrev selfValue : Cosieve zero :=
  cosieveValue model selfMember zero env

/-- The truth value of `¬ (x ∈ x)`: the arrow `right`. -/
abbrev notSelfValue : Cosieve zero :=
  cosieveValue model notSelfMember zero env

theorem selfValue_reach_holds_iff (t : WalkingParallelPair) :
    selfValue.reach.holds t ↔ t = one := by
  constructor
  · rintro ⟨f, hf⟩
    cases f with
    | left => rfl
    | right => exact (not_force_right hf).elim
    | id => exact (not_force_zero _ ((force_iff_mem_id model selfMember zero env).mpr hf)).elim
  · rintro rfl
    exact ⟨left, force_left⟩

theorem notSelfValue_reach_holds_iff (t : WalkingParallelPair) :
    notSelfValue.reach.holds t ↔ t = one := by
  constructor
  · rintro ⟨f, hf⟩
    cases f with
    | left => exact (not_force_not_left hf).elim
    | right => rfl
    | id => exact (not_force_not_zero ((force_iff_mem_id model notSelfMember zero env).mpr hf)).elim
  · rintro rfl
    exact ⟨right, force_not_right⟩

theorem same_reach : selfValue.reach = notSelfValue.reach :=
  Persistent.ext (funext fun t => propext
    ((selfValue_reach_holds_iff t).trans (notSelfValue_reach_holds_iff t).symm))

theorem selfValue_ne_notSelfValue : selfValue ≠ notSelfValue := fun h =>
  not_force_not_left (show notSelfValue.mem one left from h ▸ force_left)

/-- **Parallel arrows: the reach forgets which arrow.** A formula and its negation are forced
along the two arrows into `one`; their cosieves differ and their reaches agree. -/
def fiber_reach_parallel : NonTrivialFiber (Cosieve.reach (s := zero)) id where
  left := selfValue
  right := notSelfValue
  sameShadow := same_reach
  differentValue := selfValue_ne_notSelfValue

/-- **Parallel arrows: the reach does not keep meets.** -/
theorem reach_inf_ne : (selfValue ⊓ notSelfValue).reach ≠ selfValue.reach ⊓ notSelfValue.reach := by
  intro h
  have hone : (selfValue.reach ⊓ notSelfValue.reach).holds one :=
    ⟨(selfValue_reach_holds_iff one).mpr rfl, (notSelfValue_reach_holds_iff one).mpr rfl⟩
  rw [← h] at hone
  obtain ⟨f, hself, hnot⟩ := hone
  exact force_modusPonens model _ _ _ _ hnot hself

end Parallel

/-! ## A non-identity endomorphism -/

/-- A monoid acting on a set, as a functor on the one-object category of the monoid. -/
def actionValues {M : Type} [Monoid M] (X : Action Type M) : SingleObj M ⥤ Type where
  obj _ := X.V
  map g := X.ρ g
  map_id _ := X.ρ.map_one
  map_comp f g := X.ρ.map_mul g f

/-- The monoid with one idempotent besides the identity. -/
inductive Collapse : Type where
  | one
  | collapse
  deriving DecidableEq

instance : Monoid Collapse where
  mul a b := match a, b with
    | .one, .one => .one
    | _, _ => .collapse
  one := .one
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl

/-- The identity fixes every value; `collapse` sends every value to `false`. -/
instance : MulAction Collapse Bool where
  smul a b := match a with
    | .one => b
    | .collapse => false
  one_smul _ := rfl
  mul_smul a b x := by cases a <;> cases b <;> rfl

namespace Idempotent

/-- The one-object category of `Collapse`, acting on `Bool`. -/
abbrev values : SingleObj Collapse ⥤ Type :=
  actionValues (Action.ofMulAction Collapse Bool)

/-- No membership. -/
def model : Model values where
  member _ _ _ := False
  member_transport := by
    intro _ _ _ _ _ h
    exact h

/-- `x = y`. -/
def equal : Formula 2 :=
  .equal 0 1

/-- `x := true, y := false`. -/
def env : Environment values 2 (SingleObj.star Collapse) :=
  ![true, false]

theorem not_force : ¬ force values model equal (SingleObj.star Collapse) env :=
  fun h => Bool.noConfusion h

/-- `collapse`, as an arrow to any context. -/
def collapseArrow (t : SingleObj Collapse) : SingleObj.star Collapse ⟶ t :=
  Collapse.collapse

theorem force_collapse (t : SingleObj Collapse) :
    force values model equal t (transport values (collapseArrow t) env) :=
  rfl

theorem mul_collapse (g : Collapse) : g * Collapse.collapse = Collapse.collapse := by
  cases g <;> rfl

theorem force_iff (f : Collapse) :
    force values model equal (SingleObj.star Collapse)
        (transport values (f : SingleObj.star Collapse ⟶ SingleObj.star Collapse) env) ↔
      f = Collapse.collapse := by
  cases f
  · exact ⟨fun h => (not_force h).elim, fun h => Collapse.noConfusion h⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- **A non-identity endomorphism: the reach holds where the formula is not forced.** -/
theorem reach_holds_not_force :
    (cosieveValue model equal (SingleObj.star Collapse) env).reach.holds (SingleObj.star Collapse) ∧
      ¬ force values model equal (SingleObj.star Collapse) env :=
  ⟨⟨collapseArrow _, force_collapse _⟩, not_force⟩

/-- The cosieve of the arrows that factor through `collapse`. -/
def collapseCosieve : Cosieve (SingleObj.star Collapse) where
  mem _ f := f = Collapse.collapse
  comp_mem f g h := by
    subst h
    rw [SingleObj.comp_as_mul]
    exact mul_collapse g

theorem collapseCosieve_not_id : ¬ collapseCosieve.mem _ (𝟙 (SingleObj.star Collapse)) :=
  fun h => Collapse.noConfusion h

theorem collapseCosieve_ne_bot : collapseCosieve ≠ ⊥ := fun h => by
  have hmem : collapseCosieve.mem _ (collapseArrow (SingleObj.star Collapse)) := rfl
  rw [h] at hmem
  exact hmem

theorem collapseCosieve_ne_top : collapseCosieve ≠ ⊤ := fun h =>
  collapseCosieve_not_id (by rw [h]; trivial)

/-- The truth value of `x = y` is the cosieve of `collapse`. -/
theorem cosieveValue_equal : cosieveValue model equal (SingleObj.star Collapse) env = collapseCosieve :=
  Cosieve.ext' fun _ f => force_iff f

/-- **The reach forgets the verdict at the identity.** The cosieve of `collapse` and the top
cosieve reach the same stages; only the second contains the identity. -/
def fiber_reach_idempotent :
    NonTrivialFiber (Cosieve.reach (s := SingleObj.star Collapse))
      (fun S => S.mem (SingleObj.star Collapse) (𝟙 _)) :=
  NonTrivialFiber.ofProp (a := ⊤) (b := cosieveValue model equal (SingleObj.star Collapse) env)
    (Persistent.ext (funext fun t => propext
      ⟨fun _ => ⟨collapseArrow t, force_collapse t⟩, fun _ => ⟨collapseArrow t, trivial⟩⟩))
    trivial
    (fun h => not_force ((force_iff_mem_id model equal _ env).mpr h))

end Idempotent

end Mettapedia.SetTheory.CarveOuts.Sites
