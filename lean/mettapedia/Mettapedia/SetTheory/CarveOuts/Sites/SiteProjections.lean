import Mettapedia.SetTheory.CarveOuts.Sites.ProductSite
import Mettapedia.SetTheory.CarveOuts.HeytingValued.Gunky
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogicControls

/-!
# The two projections of the product site, and Cantor space

The product site has two projection functors, to the contexts and to the regions. Pulling a
model back along each one gives a model on the product site; forcing on the product site then
reads exactly what the model's own semantics reads.

**To contextual forcing.** A model of contextual forcing over `D` pulled back along the
projection to `D` (`contextValues`, `contextModel`) does not vary with the region. Over the open
sets of a topological space, a formula is forced at `(c, U)` exactly when, if `U` is inhabited,
the formula is forced at `c` (`siteForce_context_iff`). So contextual forcing is the part of the
product site that is constant in the regions. Applied to the infinite stages of the contextual
controls, excluded middle is still not forced at the first stage on any inhabited region
(`control_excluded_middle_not_forced`).

**To the Heyting-valued sets on the frame.** The names of the Heyting-valued universe over a
frame `H`, identified on a region `U` when `U` is below their equality (`nameSetoid`), form a
model on the product site that does not vary with the context (`nameValues`, `nameModel`). Every
bounded formula, translated into the language of contextual logic (`translate`; bounded
quantifiers become guarded quantifiers), is forced on a region exactly when the region is below
its Heyting truth value (`siteForce_translate_iff`). The two bounded quantifier laws this needs
are `iInf_mem_himp_eq` and `iSup_mem_inf_eq`.

**Covers matter: Cantor space.** Let a region-model on `Opens (ℕ → Bool)` say that membership
holds on the regions inside a fixed open set.

* For the left half `{f | f 0 = true}`, excluded middle of membership is forced on the whole
  space: the two halves cover it, although neither disjunct is forced there
  (`halves_neither_disjunct`). Contextual forcing over the same category, which has no covers,
  does not force it (`halves_excluded_middle`).
* For the complement of a point, excluded middle is not forced on the whole space: the point
  has no neighbourhood inside the complement or disjoint from it, because Cantor space has no
  isolated point (`puncture_excluded_middle_not_forced`). The internal logic of the product
  site is not classical, whatever the host's logic is.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts.Sites

open CategoryTheory TopologicalSpace
open Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogic
open Mettapedia.SetTheory.CarveOuts.HeytingValued

universe u v

/-! ## Covers of open sets -/

section Opens

variable {X : Type u} [TopologicalSpace X]

theorem covered_opens_iff {U : Opens X} {P : (V : Opens X) → V ≤ U → Prop} :
    Covered U P ↔ ∀ x ∈ U, ∃ V, ∃ h : V ≤ U, P V h ∧ x ∈ V := by
  constructor
  · intro hcov x hx
    obtain ⟨V, ⟨h, hP⟩, hxV⟩ := Opens.mem_sSup.mp (hcov hx)
    exact ⟨V, h, hP, hxV⟩
  · intro h x hx
    obtain ⟨V, hVU, hP, hxV⟩ := h x hx
    exact Opens.mem_sSup.mpr ⟨V, ⟨hVU, hP⟩, hxV⟩

/-- A constant proposition covers an open set exactly when it holds as soon as the set is
inhabited. -/
theorem covered_const_iff {U : Opens X} (c : Prop) :
    (Covered U fun _ _ => c) ↔ ((U : Set X).Nonempty → c) := by
  rw [covered_opens_iff]
  constructor
  · rintro h ⟨x, hx⟩
    obtain ⟨_, _, hc, _⟩ := h x hx
    exact hc
  · intro h x hx
    exact ⟨U, le_rfl, h ⟨x, hx⟩, hx⟩

end Opens

/-! ## The projection to contexts -/

section Contexts

variable {D : Type u} [Category.{u} D] {X : Type u} [TopologicalSpace X]

/-- A value family over the contexts, pulled back to the product site. -/
abbrev contextValues (values : D ⥤ Type v) : (D × (Opens X)ᵒᵈ) ⥤ Type v :=
  CategoryTheory.Prod.fst D (Opens X)ᵒᵈ ⋙ values

variable {values : D ⥤ Type v}

/-- A model of contextual forcing, pulled back to the product site. -/
def contextModel (model : Model values) : Model (contextValues (X := X) values) where
  member p child parent := model.member p.1 child parent
  member_transport := by
    intro _ _ arrow _ _ belongs
    exact model.member_transport arrow.1 belongs

variable (model : Model values)

theorem transport_context {n : ℕ} {p q : D × (Opens X)ᵒᵈ} (a : p ⟶ q)
    (env : Environment (contextValues (X := X) values) n p) :
    transport (contextValues values) a env = transport values a.1 env :=
  rfl

theorem transport_shrink_context {n : ℕ} (p : D × (Opens X)ᵒᵈ) {V : Opens X} (h : V ≤ region p)
    (env : Environment (contextValues (X := X) values) n p) :
    transport (contextValues values) (shrink p h) env = env :=
  transport_id values p.1 env

/-- **The projection to contexts.** Over open sets, forcing a pulled-back formula at `(c, U)` is
forcing it at `c` as soon as `U` is inhabited. -/
theorem siteForce_context_iff {n : ℕ} (φ : Formula n) (p : D × (Opens X)ᵒᵈ)
    (env : Environment (contextValues (X := X) values) n p) :
    siteForce (contextValues values) (contextModel model) φ p env ↔
      (((region p : Opens X) : Set X).Nonempty → force values model φ p.1 env) := by
  induction φ generalizing p with
  | bottom => exact covered_const_iff False
  | equal first second =>
    refine (covered_congr fun V h => ?_).trans (covered_const_iff (env first = env second))
    rw [transport_shrink_context]
  | member child parent =>
    refine (covered_congr fun V h => ?_).trans
      (covered_const_iff (model.member p.1 (env child) (env parent)))
    rw [transport_shrink_context]
    exact Iff.rfl
  | both left right leftIH rightIH =>
    rw [siteForce, leftIH, rightIH]
    exact ⟨fun h hU => ⟨h.1 hU, h.2 hU⟩, fun h => ⟨fun hU => (h hU).1, fun hU => (h hU).2⟩⟩
  | either left right leftIH rightIH =>
    show Covered _ _ ↔ _
    rw [covered_opens_iff]
    constructor
    · rintro h ⟨x, hx⟩
      obtain ⟨V, _, hV, hxV⟩ := h x hx
      rw [leftIH, rightIH, transport_shrink_context] at hV
      exact hV.imp (fun hl => hl ⟨x, hxV⟩) (fun hr => hr ⟨x, hxV⟩)
    · intro h x hx
      refine ⟨region p, le_rfl, ?_, hx⟩
      rw [leftIH, rightIH, transport_shrink_context]
      exact (h ⟨x, hx⟩).imp (fun hl _ => hl) (fun hr _ => hr)
  | imply left right leftIH rightIH =>
    show (∀ (q : D × (Opens X)ᵒᵈ) (a : p ⟶ q),
        siteForce _ _ left q (transport _ a env) → siteForce _ _ right q (transport _ a env)) ↔ _
    constructor
    · intro h hU c f premise
      have step := h (forward p c) (forwardArrow p f)
      rw [leftIH, rightIH] at step
      exact step (fun _ => premise) hU
    · intro h q a premise
      rw [leftIH] at premise
      rw [rightIH]
      rintro ⟨y, hy⟩
      have hU : ((region p : Opens X) : Set X).Nonempty := ⟨y, region_le a hy⟩
      exact h hU q.1 a.1 (premise ⟨y, hy⟩)
  | all body bodyIH =>
    show (∀ (q : D × (Opens X)ᵒᵈ) (a : p ⟶ q) (value : values.obj q.1),
        siteForce _ _ body q (extend _ (transport _ a env) value)) ↔ _
    constructor
    · intro h hU c f value
      have step := h (forward p c) (forwardArrow p f) value
      rw [bodyIH] at step
      exact step hU
    · intro h q a value
      rw [bodyIH]
      rintro ⟨y, hy⟩
      exact h ⟨y, region_le a hy⟩ q.1 a.1 value
  | exist body bodyIH =>
    show Covered _ _ ↔ _
    rw [covered_opens_iff]
    constructor
    · rintro h ⟨x, hx⟩
      obtain ⟨V, _, ⟨value, hV⟩, hxV⟩ := h x hx
      rw [bodyIH, transport_shrink_context] at hV
      exact ⟨value, hV ⟨x, hxV⟩⟩
    · intro h x hx
      obtain ⟨value, hvalue⟩ := h ⟨x, hx⟩
      refine ⟨region p, le_rfl, ⟨value, ?_⟩, hx⟩
      rw [bodyIH, transport_shrink_context]
      exact fun _ => hvalue

end Contexts

open Mettapedia.TypeTheory.MaterialSets.Hypersets in
/-- **The contextual control, read on the product site over Cantor space.** Excluded middle of
self-membership is not forced at the first stage on any inhabited open set. -/
theorem control_excluded_middle_not_forced (U : Opens (ℕ → Bool)) (hU : (U : Set (ℕ → Bool)).Nonempty)
    (value : ℕ) :
    ¬ siteForce (contextValues (X := ℕ → Bool) ContextualMaterialLogicControls.values)
      (contextModel ContextualMaterialLogicControls.model)
      (.either ContextualMaterialLogicControls.selfMember
        (ContextualMaterialLogicControls.negate ContextualMaterialLogicControls.selfMember))
      (0, U) (ContextualMaterialLogicControls.environment value) := by
  rw [siteForce_context_iff]
  exact fun h => ContextualMaterialLogicControls.excluded_middle_fails value (h hU)

/-! ## The projection to the frame: Heyting-valued names -/

section Names

variable {H : Type u} [Order.Frame H]

/-- Names identified on a region below their equality. -/
def nameSetoid (U : H) : Setoid (Name H) where
  r x y := U ≤ Name.eq x y
  iseqv :=
    { refl := fun x => by rw [Name.eq_self]; exact le_top
      symm := fun {x y} h => by rwa [Name.eq_comm]
      trans := fun {x y z} hxy hyz => le_trans (le_inf hxy hyz) (Name.eq_inf_eq_le x y z) }

variable (D : Type u) [Category.{u} D]

/-- The names on each region, at every context. -/
def nameValues : (D × Hᵒᵈ) ⥤ Type (u + 1) where
  obj p := Quotient (nameSetoid (region p))
  map a := TypeCat.ofHom (Quotient.map id fun _ _ h => le_trans (region_le a) h)
  map_id _ := by
    ext x
    induction x using Quotient.ind
    rfl
  map_comp _ _ := by
    ext x
    induction x using Quotient.ind
    rfl

theorem name_member_respects (U : H) {x₁ y₁ x₂ y₂ : Name H} (hx : U ≤ Name.eq x₁ x₂)
    (hy : U ≤ Name.eq y₁ y₂) (h : U ≤ Name.mem x₁ y₁) : U ≤ Name.mem x₂ y₂ :=
  le_trans (le_inf hy (le_trans (le_inf hx h) (Name.eq_inf_mem_le_left x₁ x₂ y₁)))
    (Name.eq_inf_mem_le_right x₂ y₁ y₂)

/-- Membership of names on a region: the region is below the membership value. -/
def nameModel : Model (nameValues (H := H) D) where
  member p := Quotient.lift₂ (s₁ := nameSetoid (region p)) (s₂ := nameSetoid (region p))
    (fun x y => region p ≤ Name.mem x y) fun _ _ _ _ hx hy => propext
      ⟨name_member_respects _ hx hy,
        name_member_respects _ ((nameSetoid _).symm hx) ((nameSetoid _).symm hy)⟩
  member_transport := by
    intro p q a child parent belongs
    induction child using Quotient.ind
    induction parent using Quotient.ind
    exact le_trans (region_le a) belongs

variable {D}

/-- The classes of names, on the region of a point. -/
def classes {n : ℕ} (p : D × Hᵒᵈ) (v : Fin n → Name H) : Environment (nameValues (H := H) D) n p :=
  fun i => Quotient.mk (nameSetoid (region p)) (v i)

theorem transport_classes {n : ℕ} {p q : D × Hᵒᵈ} (a : p ⟶ q) (v : Fin n → Name H) :
    transport (nameValues D) a (classes p v) = classes q v :=
  rfl

theorem extend_classes {n : ℕ} (p : D × Hᵒᵈ) (v : Fin n → Name H) (z : Name H) :
    extend (nameValues D) (classes p v) (Quotient.mk (nameSetoid (region p)) z) =
      classes p (Fin.cons z v : Fin (n + 1) → Name H) := by
  funext i
  refine Fin.cases rfl (fun _ => rfl) i

/-- Bounded formulas, in the language of contextual logic: bounded quantifiers become guarded
ones. -/
def translate : {n : ℕ} → BFormula n → Formula n
  | _, .falsum => .bottom
  | _, .mem a b => .member a b
  | _, .eq a b => .equal a b
  | _, .and φ ψ => .both (translate φ) (translate ψ)
  | _, .or φ ψ => .either (translate φ) (translate ψ)
  | _, .imp φ ψ => .imply (translate φ) (translate ψ)
  | _, .ball b φ => .all (.imply (.member 0 b.succ) (translate φ))
  | _, .bex b φ => .exist (.both (.member 0 b.succ) (translate φ))

/-- **The bounded universal law.** A universal over every name guarded by membership is the
universal over the children. -/
theorem iInf_mem_himp_eq (y : Name H) (F : Name H → H)
    (hF : ∀ x x', Name.eq x x' ⊓ F x ≤ F x') :
    ⨅ z, (Name.mem z y ⇨ F z) = ⨅ i, (y.weight i ⇨ F (y.child i)) := by
  refine le_antisymm (le_iInf fun i => le_trans (iInf_le _ (y.child i))
    (himp_le_himp_right (Name.weight_le_mem y i))) (le_iInf fun z => le_himp_iff.mpr ?_)
  rw [Name.mem_eq_iSup, inf_iSup_eq]
  refine iSup_le fun j => ?_
  calc (⨅ i, (y.weight i ⇨ F (y.child i))) ⊓ (y.weight j ⊓ Name.eq z (y.child j))
      ≤ ((y.weight j ⇨ F (y.child j)) ⊓ y.weight j) ⊓ Name.eq z (y.child j) := by
        rw [inf_assoc]
        exact inf_le_inf_right _ (iInf_le _ j)
    _ ≤ F (y.child j) ⊓ Name.eq (y.child j) z :=
        inf_le_inf himp_inf_le (le_of_eq (Name.eq_comm _ _))
    _ ≤ F z := by
        rw [inf_comm]
        exact hF _ _

/-- **The bounded existential law.** -/
theorem iSup_mem_inf_eq (y : Name H) (F : Name H → H)
    (hF : ∀ x x', Name.eq x x' ⊓ F x ≤ F x') :
    ⨆ z, (Name.mem z y ⊓ F z) = ⨆ i, (y.weight i ⊓ F (y.child i)) := by
  refine le_antisymm (iSup_le fun z => ?_) (iSup_le fun i =>
    le_iSup_of_le (y.child i) (inf_le_inf_right _ (Name.weight_le_mem y i)))
  rw [Name.mem_eq_iSup, iSup_inf_eq]
  refine iSup_le fun j => le_iSup_of_le j ?_
  rw [inf_assoc]
  exact inf_le_inf_left _ (hF _ _)

/-- Membership on the names model. -/
theorem siteForce_member_classes {n : ℕ} (a b : Fin n) (q : D × Hᵒᵈ) (w : Fin n → Name H) :
    siteForce (nameValues D) (nameModel D) (.member a b) q (classes q w) ↔
      region q ≤ Name.mem (w a) (w b) :=
  covered_le_iff (U := region q) (e := Name.mem (w a) (w b))

/-- Implication on the names model is the Heyting implication. -/
theorem siteForce_imply_classes {n : ℕ} (A B : Formula n) (w : Fin n → Name H) (a b : H)
    (hA : ∀ q : D × Hᵒᵈ, siteForce (nameValues D) (nameModel D) A q (classes q w) ↔ region q ≤ a)
    (hB : ∀ q : D × Hᵒᵈ, siteForce (nameValues D) (nameModel D) B q (classes q w) ↔ region q ≤ b)
    (p : D × Hᵒᵈ) :
    siteForce (nameValues D) (nameModel D) (.imply A B) p (classes p w) ↔ region p ≤ a ⇨ b := by
  show (∀ (q : D × Hᵒᵈ) (arrow : p ⟶ q), siteForce _ _ A q (classes q w) →
      siteForce _ _ B q (classes q w)) ↔ _
  constructor
  · intro h
    refine le_himp_iff.mpr ((hB _).mp (h (below p (region p ⊓ a)) (shrink p inf_le_left)
      ((hA _).mpr inf_le_right)))
  · intro h q arrow premise
    exact (hB q).mpr (le_trans (le_inf (le_trans (region_le arrow) h) ((hA q).mp premise))
      himp_inf_le)

/-- **The projection to the frame.** A bounded formula is forced on a region of the names
model exactly when the region is below its Heyting truth value. -/
theorem siteForce_translate_iff {n : ℕ} (φ : BFormula n) (p : D × Hᵒᵈ) (v : Fin n → Name H) :
    siteForce (nameValues D) (nameModel D) (translate φ) p (classes p v) ↔
      region p ≤ Name.eval φ v := by
  induction φ generalizing p with
  | falsum => exact covered_false_iff
  | mem a b => exact siteForce_member_classes a b p v
  | eq a b =>
    refine (covered_congr fun V h => ?_).trans covered_le_iff
    exact Quotient.eq
  | and φ ψ ihφ ihψ =>
    show siteForce _ _ (translate φ) p (classes p v) ∧ siteForce _ _ (translate ψ) p (classes p v) ↔ _
    rw [ihφ, ihψ]
    exact le_inf_iff.symm
  | or φ ψ ihφ ihψ =>
    refine (covered_congr fun V h => ?_).trans covered_or_le_iff
    exact or_congr (ihφ _ v) (ihψ _ v)
  | imp φ ψ ihφ ihψ =>
    exact siteForce_imply_classes _ _ v _ _ (fun q => ihφ q v) (fun q => ihψ q v) p
  | ball b φ ih =>
    have guard : ∀ (z : Name H) (q : D × Hᵒᵈ),
        siteForce (nameValues D) (nameModel D) (.imply (.member 0 b.succ) (translate φ)) q
          (classes q (Fin.cons z v : Fin _ → Name H)) ↔
        region q ≤ Name.mem z (v b) ⇨ Name.eval φ (Fin.cons z v : Fin _ → Name H) := fun z q =>
      siteForce_imply_classes (.member 0 b.succ) (translate φ) _ _ _
        (fun q' => siteForce_member_classes 0 b.succ q' _) (fun q' => ih q' _) q
    show (∀ (q : D × Hᵒᵈ) (arrow : p ⟶ q) (value : (nameValues D).obj q),
        siteForce _ _ _ q (extend _ (classes q v) value)) ↔
      region p ≤ ⨅ i, ((v b).weight i ⇨ Name.eval φ (Fin.cons ((v b).child i) v : Fin _ → Name H))
    rw [← iInf_mem_himp_eq (v b) _ (fun x x' => Name.eval_subst_cons φ v x x')]
    constructor
    · intro h
      refine le_iInf fun z => ?_
      have step := h p (𝟙 p) (Quotient.mk _ z)
      rw [extend_classes] at step
      exact (guard z p).mp step
    · intro h q arrow value
      induction value using Quotient.ind with
      | _ z =>
        rw [extend_classes]
        exact (guard z q).mpr (le_trans (region_le arrow) (le_trans h (iInf_le _ z)))
  | bex b φ ih =>
    show Covered (region p) (fun V h => ∃ value : (nameValues D).obj (below p V),
        siteForce _ _ _ (below p V) (extend _ (classes (below p V) v) value)) ↔
      region p ≤ ⨆ i, ((v b).weight i ⊓ Name.eval φ (Fin.cons ((v b).child i) v : Fin _ → Name H))
    rw [← iSup_mem_inf_eq (v b) _ (fun x x' => Name.eval_subst_cons φ v x x'),
      ← covered_exists_le_iff]
    refine covered_congr fun V h => ⟨?_, ?_⟩
    · rintro ⟨value, holds⟩
      induction value using Quotient.ind with
      | _ z =>
        rw [extend_classes] at holds
        exact ⟨z, le_inf ((siteForce_member_classes 0 b.succ _ _).mp holds.1) ((ih _ _).mp holds.2)⟩
    · rintro ⟨z, hz⟩
      refine ⟨Quotient.mk _ z, ?_⟩
      rw [extend_classes]
      exact ⟨(siteForce_member_classes 0 b.succ _ _).mpr (le_trans hz inf_le_left),
        (ih _ _).mpr (le_trans hz inf_le_right)⟩

end Names

/-! ## Covers matter: Cantor space -/

section Cantor

variable {D : Type} [Category.{0} D] {H : Type} [Order.Frame H]

/-- One value at every point. -/
def unitValues : (D × Hᵒᵈ) ⥤ Type where
  obj _ := PUnit
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Membership holds on the regions inside `e`. -/
def regionModel (e : H) : Model (unitValues (D := D) (H := H)) where
  member p _ _ := region p ≤ e
  member_transport := by
    intro _ _ arrow _ _ belongs
    exact le_trans (region_le arrow) belongs

/-- `x ∈ x`. -/
abbrev inside : Formula 1 :=
  .member 0 0

/-- `¬ (x ∈ x)`. -/
abbrev outside : Formula 1 :=
  .imply inside .bottom

/-- Excluded middle of `x ∈ x`. -/
abbrev insideOrOutside : Formula 1 :=
  .either inside outside

/-- The one value. -/
def unitEnv (p : D × Hᵒᵈ) : Environment (unitValues (D := D) (H := H)) 1 p :=
  fun _ => PUnit.unit

theorem transport_unitEnv {p q : D × Hᵒᵈ} (a : p ⟶ q) :
    transport unitValues a (unitEnv p) = unitEnv q :=
  rfl

theorem siteForce_inside_iff (e : H) (p : D × Hᵒᵈ) :
    siteForce unitValues (regionModel e) inside p (unitEnv p) ↔ region p ≤ e :=
  covered_le_iff (U := region p) (e := e)

theorem siteForce_outside_iff (e : H) (p : D × Hᵒᵈ) :
    siteForce unitValues (regionModel e) outside p (unitEnv p) ↔ region p ⊓ e ≤ ⊥ := by
  show (∀ (q : D × Hᵒᵈ) (arrow : p ⟶ q), siteForce _ _ inside q (unitEnv q) →
      siteForce _ _ .bottom q (unitEnv q)) ↔ _
  constructor
  · intro h
    exact covered_false_iff.mp (h (below p (region p ⊓ e)) (shrink p inf_le_left)
      ((siteForce_inside_iff e _).mpr inf_le_right))
  · intro h q arrow premise
    exact covered_false_iff.mpr (le_trans (le_inf (region_le arrow)
      ((siteForce_inside_iff e q).mp premise)) h)

theorem siteForce_insideOrOutside_iff (e : H) (p : D × Hᵒᵈ) :
    siteForce unitValues (regionModel e) insideOrOutside p (unitEnv p) ↔
      Covered (region p) fun V _ => V ≤ e ∨ V ⊓ e ≤ ⊥ :=
  covered_congr fun _ _ => or_congr (siteForce_inside_iff e _) (siteForce_outside_iff e _)

/-- The left half of Cantor space. -/
def leftHalf : Opens (ℕ → Bool) :=
  ⟨(fun f : ℕ → Bool => f 0) ⁻¹' {true}, (isOpen_discrete _).preimage (continuous_apply 0)⟩

/-- The right half of Cantor space. -/
def rightHalf : Opens (ℕ → Bool) :=
  ⟨(fun f : ℕ → Bool => f 0) ⁻¹' {false}, (isOpen_discrete _).preimage (continuous_apply 0)⟩

theorem halves_disjoint : rightHalf ⊓ leftHalf ≤ ⊥ := by
  rintro f ⟨hr, hl⟩
  exact Bool.false_ne_true (hr.symm.trans hl)

theorem halves_cover : (⊤ : Opens (ℕ → Bool)) ≤ leftHalf ⊔ rightHalf := by
  intro f _
  cases h : f 0
  · exact Or.inr h
  · exact Or.inl h

/-- The constant sequences. -/
def constSeq (b : Bool) : ℕ → Bool :=
  fun _ => b

theorem not_top_le_leftHalf : ¬ (⊤ : Opens (ℕ → Bool)) ≤ leftHalf := fun h =>
  Bool.false_ne_true (h (show constSeq false ∈ (⊤ : Opens (ℕ → Bool)) from trivial))

theorem leftHalf_ne_bot : ¬ leftHalf ≤ ⊥ := fun h =>
  (h (show constSeq true ∈ leftHalf from rfl) : constSeq true ∈ (⊥ : Opens (ℕ → Bool)))

/-- The whole space, at a context. -/
abbrev whole (c : D) : D × (Opens (ℕ → Bool))ᵒᵈ :=
  (c, (⊤ : Opens (ℕ → Bool)))

/-- **Covers matter.** On the product site over Cantor space, excluded middle of membership in
the left half is forced on the whole space; contextual forcing over the same category, without
covers, does not force it. -/
theorem halves_excluded_middle (c : D) :
    siteForce unitValues (regionModel leftHalf) insideOrOutside (whole c) (unitEnv _) ∧
      ¬ force unitValues (regionModel leftHalf) insideOrOutside (whole c) (unitEnv _) := by
  refine ⟨(siteForce_insideOrOutside_iff _ _).mpr ?_, ?_⟩
  · refine le_trans halves_cover (sup_le ?_ ?_)
    · exact le_sSup ⟨le_top, Or.inl le_rfl⟩
    · exact le_sSup ⟨le_top, Or.inr halves_disjoint⟩
  · rintro (hin | hout)
    · exact not_top_le_leftHalf hin
    · exact hout (below (whole c) leftHalf) (shrink (whole c) le_top) le_rfl

/-- On the whole space neither disjunct is forced: excluded middle is forced only through the
cover by the two halves. -/
theorem halves_neither_disjunct (c : D) :
    ¬ siteForce unitValues (regionModel leftHalf) inside (whole c) (unitEnv _) ∧
      ¬ siteForce unitValues (regionModel leftHalf) outside (whole c) (unitEnv _) :=
  ⟨fun h => not_top_le_leftHalf ((siteForce_inside_iff _ _).mp h),
    fun h => leftHalf_ne_bot (le_trans (le_inf le_top le_rfl) ((siteForce_outside_iff _ _).mp h))⟩

/-- The complement of a point. -/
def puncture (f : ℕ → Bool) : Opens (ℕ → Bool) :=
  ⟨{f}ᶜ, isOpen_compl_singleton⟩

/-- **Excluded middle fails on the product site over Cantor space.** For the complement of a
point, no neighbourhood of the point is inside it or disjoint from it. -/
theorem puncture_excluded_middle_not_forced (c : D) (f : ℕ → Bool) :
    ¬ siteForce unitValues (regionModel (puncture f)) insideOrOutside (whole c) (unitEnv _) := by
  rw [siteForce_insideOrOutside_iff, covered_opens_iff]
  intro h
  obtain ⟨V, _, hV, hfV⟩ := h f trivial
  rcases hV with hin | hout
  · exact (hin hfV : f ∈ puncture f) rfl
  · apply cantor_noIsolated f
    have : ((V : Set (ℕ → Bool))) = {f} := by
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨hfV, fun g hg => ?_⟩
      by_contra hne
      exact (hout ⟨hg, hne⟩ : g ∈ (⊥ : Opens (ℕ → Bool)))
    exact this ▸ V.isOpen

end Cantor

end Mettapedia.SetTheory.CarveOuts.Sites
