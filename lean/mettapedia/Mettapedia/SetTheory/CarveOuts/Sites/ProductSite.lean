import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogicSoundness
import Mettapedia.SetTheory.CarveOuts.HeytingValued.Names
import Mathlib.CategoryTheory.Products.Basic

/-!
# The product site: contexts times regions of a frame

The points of the product site are pairs `(c, U)` of a context `c` of a category `D` and a
region `U` of a frame `H` (an element of `H`, read in the order dual so that arrows go to smaller
regions). An arrow `(c, U) ⟶ (c', V)` is an arrow `c ⟶ c'` together with `V ≤ U`. A model is a
model of contextual forcing over this category (`ContextualMaterialLogic.Model`, over
`D × Hᵒᵈ`): a value family with a persistent membership. The regions are covered by their
joins: `V` is covered by the regions below it where a predicate holds when it is below their
join (`Covered`).

**Forcing (Kripke–Joyal).** `siteForce` reads a formula at a point:

* implication and the universal quantifier look along every arrow, to later contexts and to
  smaller regions, as contextual forcing does;
* falsity, equality, membership, disjunction and the existential quantifier hold when they hold
  on a cover of the region: on smaller regions whose join is at least the region. Falsity holds
  only on the bottom region.

**Two structural laws.** Forcing persists along every arrow (`siteForce_transport`) and is local:
a formula forced on a cover of a region is forced on the region (`siteForce_local`). It commutes
with substitution of variables, under binders (`siteForce_substitute`).

**Soundness.** Every natural-deduction derivation of contextual material logic
(`ContextualMaterialLogic.Derivation`, intuitionistic, with equality) is sound for this forcing
(`site_derivation_sound`, `closed_site_derivation_sound`). The proof follows the soundness proof
of contextual forcing; the new cases are elimination of disjunction, of the existential and of
equality, which go through locality.

**The frame reading at a context.** The region value of a formula (`regionValue`) is the join of
the smaller regions where it is forced. A formula is forced on a region below `U` exactly when the
region is below the value (`siteForce_shrink_iff`), and

* conjunction, disjunction and falsity are meet, join and bottom of `H`
  (`regionValue_both`, `regionValue_either`, `regionValue_bottom`);
* implication is a meet, over the arrows out of the context, of the frame's Heyting implication,
  relativised to the region (`regionValue_imply`).

So the frame reading keeps the connectives, and implication keeps the arrows of `D`.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts.Sites

open CategoryTheory
open Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogic

universe u v

/-! ## Covers -/

section Covers

variable {H : Type u} [Order.Frame H]

/-- The region `U` is covered by the regions below it where `P` holds. -/
def Covered (U : H) (P : (V : H) → V ≤ U → Prop) : Prop :=
  U ≤ sSup {V | ∃ h : V ≤ U, P V h}

theorem covered_self {U : H} {P : (V : H) → V ≤ U → Prop} (hU : P U le_rfl) : Covered U P :=
  le_sSup ⟨le_rfl, hU⟩

theorem covered_mono {U : H} {P Q : (V : H) → V ≤ U → Prop} (hPQ : ∀ V h, P V h → Q V h)
    (hP : Covered U P) : Covered U Q :=
  le_trans hP (sSup_le_sSup fun _ ⟨h, hV⟩ => ⟨h, hPQ _ h hV⟩)

theorem covered_congr {U : H} {P Q : (V : H) → V ≤ U → Prop} (hPQ : ∀ V h, P V h ↔ Q V h) :
    Covered U P ↔ Covered U Q :=
  ⟨covered_mono fun V h => (hPQ V h).mp, covered_mono fun V h => (hPQ V h).mpr⟩

/-- A region below the join of the parts of `U` where `P` holds is covered by its meets with
them. -/
theorem covered_of_le_sSup {U W : H} {P : (V : H) → V ≤ U → Prop} {Q : (V : H) → V ≤ W → Prop}
    (hW : W ≤ sSup {V | ∃ h : V ≤ U, P V h})
    (hPQ : ∀ V (h : V ≤ U), P V h → Q (W ⊓ V) inf_le_left) : Covered W Q := by
  refine le_trans (le_inf le_rfl hW) (le_trans (le_of_eq inf_sSup_eq) (iSup₂_le fun V hV => ?_))
  obtain ⟨h, hPV⟩ := hV
  exact le_sSup ⟨inf_le_left, hPQ V h hPV⟩

/-- A cover of `U` restricts to a cover of any smaller `W`. -/
theorem covered_restrict {U W : H} {P : (V : H) → V ≤ U → Prop} {Q : (V : H) → V ≤ W → Prop}
    (hP : Covered U P) (hWU : W ≤ U) (hPQ : ∀ V (h : V ≤ U), P V h → Q (W ⊓ V) inf_le_left) :
    Covered W Q :=
  covered_of_le_sSup (le_trans hWU hP) hPQ

/-- A cover of covers is a cover. -/
theorem covered_trans {U : H} {P : (V : H) → V ≤ U → Prop} {Q : (V : H) → V ≤ U → Prop}
    (hP : Covered U P)
    (hPQ : ∀ V (h : V ≤ U), P V h → Covered V fun W hW => Q W (le_trans hW h)) :
    Covered U Q := by
  refine le_trans hP (sSup_le fun V ⟨h, hPV⟩ => le_trans (hPQ V h hPV) (sSup_le_sSup ?_))
  rintro W ⟨hW, hQ⟩
  exact ⟨le_trans hW h, hQ⟩

theorem covered_le_iff {U e : H} : (Covered U fun V _ => V ≤ e) ↔ U ≤ e :=
  ⟨fun h => le_trans h (sSup_le fun _ ⟨_, hV⟩ => hV), fun h => covered_self h⟩

theorem covered_false_iff {U : H} : (Covered U fun _ _ => False) ↔ U ≤ ⊥ := by
  constructor
  · intro h
    exact le_trans h (sSup_le fun _ ⟨_, hV⟩ => hV.elim)
  · intro h
    exact le_trans h bot_le

/-- A region covered by the parts below `a` or below `b` is below `a ⊔ b`. -/
theorem covered_or_le_iff {U a b : H} : (Covered U fun V _ => V ≤ a ∨ V ≤ b) ↔ U ≤ a ⊔ b := by
  constructor
  · intro h
    exact le_trans h (sSup_le fun _ ⟨_, hV⟩ => hV.elim (fun ha => le_sup_of_le_left ha)
      (fun hb => le_sup_of_le_right hb))
  · intro h
    refine le_trans (le_inf le_rfl h) (le_trans (Mettapedia.SetTheory.CarveOuts.HeytingValued.Name.inf_sup_le_sup_inf
      U a b) (sup_le ?_ ?_))
    · exact le_sSup ⟨inf_le_left, Or.inl inf_le_right⟩
    · exact le_sSup ⟨inf_le_left, Or.inr inf_le_right⟩

/-- A region covered by the parts below some `g i` is below their join. -/
theorem covered_exists_le_iff {U : H} {ι : Sort*} (g : ι → H) :
    (Covered U fun V _ => ∃ i, V ≤ g i) ↔ U ≤ ⨆ i, g i := by
  constructor
  · intro h
    exact le_trans h (sSup_le fun _ ⟨_, i, hV⟩ => le_iSup_of_le i hV)
  · intro h
    refine le_trans (le_inf le_rfl h) (le_trans (le_of_eq (inf_iSup_eq U g)) (iSup_le fun i => ?_))
    exact le_sSup ⟨inf_le_left, i, inf_le_right⟩

end Covers

/-! ## Points and arrows of the product site -/

section Site

variable {D : Type u} [Category.{u} D] {H : Type u} [Order.Frame H]

/-- The region of a point. -/
abbrev region (p : D × Hᵒᵈ) : H :=
  p.2

/-- The point at the same context with a smaller region. -/
abbrev below (p : D × Hᵒᵈ) (V : H) : D × Hᵒᵈ :=
  (p.1, V)

/-- Restriction to a smaller region at the same context. -/
def shrink (p : D × Hᵒᵈ) {V : H} (h : V ≤ region p) : p ⟶ below p V :=
  (𝟙 p.1, homOfLE h)

/-- An arrow shrinks the region. -/
theorem region_le {p q : D × Hᵒᵈ} (a : p ⟶ q) : region q ≤ region p :=
  leOfHom a.2

/-- An arrow, carried to a smaller region of its source. -/
def across {p q : D × Hᵒᵈ} (a : p ⟶ q) (V : H) : below p V ⟶ below q (region q ⊓ V) :=
  (a.1, homOfLE (show region q ⊓ V ≤ V from inf_le_right))

theorem shrink_comp_shrink (p : D × Hᵒᵈ) {V W : H} (h : V ≤ region p) (h' : W ≤ V) :
    shrink p h ≫ shrink (below p V) h' = shrink p (le_trans h' h) :=
  Prod.ext (Category.id_comp _) (Subsingleton.elim _ _)

theorem shrink_comp_across {p q : D × Hᵒᵈ} (a : p ⟶ q) {V : H} (h : V ≤ region p) :
    shrink p h ≫ across a V = a ≫ shrink q inf_le_left :=
  Prod.ext (show 𝟙 p.1 ≫ a.1 = a.1 ≫ 𝟙 q.1 by rw [Category.id_comp, Category.comp_id])
    (Subsingleton.elim _ _)

variable {values : (D × Hᵒᵈ) ⥤ Type v}

theorem transport_shrink_shrink {n : ℕ} (p : D × Hᵒᵈ) {V W : H} (h : V ≤ region p) (h' : W ≤ V)
    (env : Environment values n p) :
    transport values (shrink (below p V) h') (transport values (shrink p h) env) =
      transport values (shrink p (le_trans h' h)) env := by
  rw [← transport_comp, shrink_comp_shrink]

theorem transport_shrink_across {n : ℕ} {p q : D × Hᵒᵈ} (a : p ⟶ q) {V : H} (h : V ≤ region p)
    (env : Environment values n p) :
    transport values (shrink q inf_le_left) (transport values a env) =
      transport values (across a V) (transport values (shrink p h) env) := by
  rw [← transport_comp, ← transport_comp, shrink_comp_across]

/-! ## Forcing -/

variable (values) (model : Model values)

/-- **Kripke–Joyal forcing on the product site.** -/
def siteForce {n : ℕ} : Formula n → (p : D × Hᵒᵈ) → Environment values n p → Prop
  | .bottom, p, _ => Covered (region p) fun _ _ => False
  | .equal first second, p, env => Covered (region p) fun _ h =>
      transport values (shrink p h) env first = transport values (shrink p h) env second
  | .member child parent, p, env => Covered (region p) fun _ h =>
      model.member _ (transport values (shrink p h) env child)
        (transport values (shrink p h) env parent)
  | .both left right, p, env => siteForce left p env ∧ siteForce right p env
  | .either left right, p, env => Covered (region p) fun V h =>
      siteForce left (below p V) (transport values (shrink p h) env) ∨
        siteForce right (below p V) (transport values (shrink p h) env)
  | .imply left right, p, env => ∀ (q : D × Hᵒᵈ) (a : p ⟶ q),
      siteForce left q (transport values a env) → siteForce right q (transport values a env)
  | .all body, p, env => ∀ (q : D × Hᵒᵈ) (a : p ⟶ q) (value : values.obj q),
      siteForce body q (extend values (transport values a env) value)
  | .exist body, p, env => Covered (region p) fun V h =>
      ∃ value : values.obj (below p V),
        siteForce body (below p V) (extend values (transport values (shrink p h) env) value)

variable {values} {model}

/-- **Persistence.** Forcing persists along every arrow of the product site. -/
theorem siteForce_transport {n : ℕ} (φ : Formula n) {p q : D × Hᵒᵈ} (a : p ⟶ q)
    (env : Environment values n p) (holds : siteForce values model φ p env) :
    siteForce values model φ q (transport values a env) := by
  induction φ generalizing p q with
  | bottom => exact covered_restrict holds (region_le a) fun _ _ h => h
  | equal first second =>
    refine covered_restrict holds (region_le a) fun V h same => ?_
    rw [transport_shrink_across a h]
    exact congrArg (values.map (across a V)) same
  | member child parent =>
    refine covered_restrict holds (region_le a) fun V h belongs => ?_
    rw [transport_shrink_across a h]
    exact model.member_transport (across a V) belongs
  | both left right leftIH rightIH => exact ⟨leftIH a env holds.1, rightIH a env holds.2⟩
  | either left right leftIH rightIH =>
    refine covered_restrict holds (region_le a) fun V h alternatives => ?_
    rw [transport_shrink_across a h]
    exact alternatives.imp (leftIH (across a V) _) (rightIH (across a V) _)
  | imply left right _ _ =>
    intro later tail premise
    rw [← transport_comp] at premise ⊢
    exact holds later (a ≫ tail) premise
  | all body _ =>
    intro later tail value
    rw [← transport_comp]
    exact holds later (a ≫ tail) value
  | exist body bodyIH =>
    refine covered_restrict holds (region_le a) fun V h ⟨value, witness⟩ => ?_
    refine ⟨values.map (across a V) value, ?_⟩
    rw [transport_shrink_across a h, ← transport_extend]
    exact bodyIH (across a V) _ witness

/-- **Locality.** A formula forced on a cover of a region is forced on the region. -/
theorem siteForce_local {n : ℕ} (φ : Formula n) (p : D × Hᵒᵈ) (env : Environment values n p)
    (covered : Covered (region p) fun V h =>
      siteForce values model φ (below p V) (transport values (shrink p h) env)) :
    siteForce values model φ p env := by
  induction φ generalizing p with
  | bottom => exact covered_trans covered fun _ _ h => h
  | equal first second =>
    refine covered_trans covered fun V h inner => covered_mono (fun W hW same => ?_) inner
    rwa [transport_shrink_shrink] at same
  | member child parent =>
    refine covered_trans covered fun V h inner => covered_mono (fun W hW belongs => ?_) inner
    rwa [transport_shrink_shrink] at belongs
  | both left right leftIH rightIH =>
    exact ⟨leftIH p env (covered_mono (fun _ _ h => h.1) covered),
      rightIH p env (covered_mono (fun _ _ h => h.2) covered)⟩
  | either left right _ _ =>
    refine covered_trans covered fun V h inner => covered_mono (fun W hW alternatives => ?_) inner
    rwa [transport_shrink_shrink] at alternatives
  | imply left right _ rightIH =>
    intro q a premise
    refine rightIH q _ (covered_restrict covered (region_le a) fun V h step => ?_)
    rw [transport_shrink_across a h]
    refine step _ (across a V) ?_
    rw [← transport_shrink_across a h]
    exact siteForce_transport left _ _ premise
  | all body bodyIH =>
    intro q a value
    refine bodyIH q _ (covered_restrict covered (region_le a) fun V h step => ?_)
    rw [transport_extend, transport_shrink_across a h]
    exact step _ (across a V) _
  | exist body _ =>
    refine covered_trans covered fun V h inner => covered_mono (fun W hW witness => ?_) inner
    rwa [transport_shrink_shrink] at witness

/-! ## Substitution -/

theorem siteForce_substitute {n m : ℕ} (indices : Fin n → Fin m) (φ : Formula n)
    (p : D × Hᵒᵈ) (env : Environment values m p) :
    siteForce values model (substitute indices φ) p env ↔
      siteForce values model φ p (fun index => env (indices index)) := by
  induction φ generalizing m p with
  | bottom => exact Iff.rfl
  | equal first second => exact Iff.rfl
  | member child parent => exact Iff.rfl
  | both left right leftIH rightIH =>
    exact and_congr (leftIH indices p env) (rightIH indices p env)
  | either left right leftIH rightIH =>
    exact covered_congr fun V h =>
      or_congr (leftIH indices _ (transport values (shrink p h) env))
        (rightIH indices _ (transport values (shrink p h) env))
  | imply left right leftIH rightIH =>
    refine forall_congr' fun q => forall_congr' fun a => ?_
    exact imp_congr (leftIH indices q (transport values a env))
      (rightIH indices q (transport values a env))
  | all body bodyIH =>
    refine forall_congr' fun q => forall_congr' fun a => forall_congr' fun value => ?_
    exact (bodyIH (liftVariables indices) q (extend values (transport values a env) value)).trans
      (Iff.of_eq (congrArg (siteForce values model body q)
        (extended_substitution indices q (transport values a env) value)))
  | exist body bodyIH =>
    refine covered_congr fun V h => exists_congr fun value => ?_
    exact (bodyIH (liftVariables indices) _
      (extend values (transport values (shrink p h) env) value)).trans
      (Iff.of_eq (congrArg (siteForce values model body _)
        (extended_substitution indices _ (transport values (shrink p h) env) value)))

theorem siteForce_weaken {n : ℕ} (φ : Formula n) (p : D × Hᵒᵈ) (env : Environment values n p)
    (value : values.obj p) :
    siteForce values model (weakenFormula φ) p (extend values env value) ↔
      siteForce values model φ p env :=
  siteForce_substitute Fin.succ φ p (extend values env value)

theorem siteForce_instantiate {n : ℕ} (body : Formula (n + 1)) (index : Fin n) (p : D × Hᵒᵈ)
    (env : Environment values n p) :
    siteForce values model (substitute (instantiate index) body) p env ↔
      siteForce values model body p (extend values env (env index)) :=
  (siteForce_substitute (instantiate index) body p env).trans
    (Iff.of_eq (congrArg (siteForce values model body p) (instantiate_environment index p env)))

theorem siteForce_modusPonens {n : ℕ} (antecedent consequent : Formula n) (p : D × Hᵒᵈ)
    (env : Environment values n p)
    (step : siteForce values model (.imply antecedent consequent) p env)
    (premise : siteForce values model antecedent p env) :
    siteForce values model consequent p env := by
  have current := step p (𝟙 p)
  rw [transport_id] at current
  exact current premise

/-- A formula forced at a point is forced on the cover of its region by itself. -/
theorem covered_of_siteForce {n : ℕ} (φ : Formula n) (p : D × Hᵒᵈ) (env : Environment values n p)
    (holds : siteForce values model φ p env) :
    Covered (region p) fun V h =>
      siteForce values model φ (below p V) (transport values (shrink p h) env) :=
  covered_self (siteForce_transport φ (shrink p le_rfl) env holds)

/-! ## Soundness -/

theorem site_assumptions_weaken {n : ℕ} (assumptions : List (Formula n)) (p : D × Hᵒᵈ)
    (env : Environment values n p) (value : values.obj p)
    (admitted : ∀ formula, formula ∈ assumptions → siteForce values model formula p env) :
    ∀ formula, formula ∈ assumptions.map weakenFormula →
      siteForce values model formula p (extend values env value) := by
  intro formula included
  obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp included
  exact (siteForce_weaken original p env value).mpr (admitted original originalIn)

theorem site_assumptions_transport {n : ℕ} (assumptions : List (Formula n)) {p q : D × Hᵒᵈ}
    (a : p ⟶ q) (env : Environment values n p)
    (admitted : ∀ formula, formula ∈ assumptions → siteForce values model formula p env) :
    ∀ formula, formula ∈ assumptions → siteForce values model formula q (transport values a env) :=
  fun formula included => siteForce_transport formula a env (admitted formula included)

theorem site_assumptions_cons {n : ℕ} {assumptions : List (Formula n)} {extra : Formula n}
    (p : D × Hᵒᵈ) (env : Environment values n p)
    (admitted : ∀ formula, formula ∈ assumptions → siteForce values model formula p env)
    (holds : siteForce values model extra p env) :
    ∀ formula, formula ∈ extra :: assumptions → siteForce values model formula p env := by
  intro formula included
  rcases List.mem_cons.mp included with rfl | previous
  · exact holds
  · exact admitted formula previous

/-- **Soundness.** Every natural-deduction derivation is sound for forcing on the product
site. -/
theorem site_derivation_sound {n : ℕ} {assumptions : List (Formula n)} {conclusion : Formula n}
    (derivation : Derivation assumptions conclusion) (p : D × Hᵒᵈ) (env : Environment values n p)
    (admitted : ∀ formula, formula ∈ assumptions → siteForce values model formula p env) :
    siteForce values model conclusion p env := by
  induction derivation generalizing p with
  | hypothesis included => exact admitted _ included
  | weakening _ included proofIH =>
    exact proofIH p env (fun formula member => admitted formula (included formula member))
  | bottomElim _ proofIH =>
    exact siteForce_local _ p env (covered_mono (fun _ _ h => h.elim) (proofIH p env admitted))
  | bothIntro _ _ leftIH rightIH => exact ⟨leftIH p env admitted, rightIH p env admitted⟩
  | bothLeft _ proofIH => exact (proofIH p env admitted).1
  | bothRight _ proofIH => exact (proofIH p env admitted).2
  | eitherLeft _ proofIH =>
    exact covered_mono (fun _ _ h => Or.inl h) (covered_of_siteForce _ p env (proofIH p env admitted))
  | eitherRight _ proofIH =>
    exact covered_mono (fun _ _ h => Or.inr h) (covered_of_siteForce _ p env (proofIH p env admitted))
  | eitherElim _ _ _ proofIH leftIH rightIH =>
    refine siteForce_local _ p env (covered_mono (fun V h alternatives => ?_) (proofIH p env admitted))
    exact alternatives.elim
      (fun holds => leftIH _ _ (site_assumptions_cons _ _
        (site_assumptions_transport _ (shrink p h) env admitted) holds))
      (fun holds => rightIH _ _ (site_assumptions_cons _ _
        (site_assumptions_transport _ (shrink p h) env admitted) holds))
  | implyIntro _ proofIH =>
    intro q a premise
    apply proofIH q (transport values a env)
    intro formula included
    rcases List.mem_cons.mp included with rfl | previous
    · exact premise
    · exact siteForce_transport formula a env (admitted formula previous)
  | implyElim _ _ proofIH premiseIH =>
    exact siteForce_modusPonens _ _ p env (proofIH p env admitted) (premiseIH p env admitted)
  | allIntro _ proofIH =>
    intro q a value
    exact proofIH q (extend values (transport values a env) value)
      (site_assumptions_weaken _ q (transport values a env) value
        (site_assumptions_transport _ a env admitted))
  | allElim _ index proofIH =>
    have current := proofIH p env admitted p (𝟙 p) (env index)
    rw [transport_id] at current
    exact (siteForce_instantiate _ index p env).mpr current
  | existIntro index _ proofIH =>
    have holds := (siteForce_instantiate _ index p env).mp (proofIH p env admitted)
    refine covered_self ⟨values.map (shrink p le_rfl) (env index), ?_⟩
    rw [← transport_extend]
    exact siteForce_transport _ (shrink p le_rfl) _ holds
  | existElim _ _ proofIH branchIH =>
    refine siteForce_local _ p env (covered_mono (fun V h ⟨value, holds⟩ => ?_) (proofIH p env admitted))
    apply (siteForce_weaken _ _ _ value).mp
    apply branchIH _ (extend values (transport values (shrink p h) env) value)
    intro formula included
    rcases List.mem_cons.mp included with rfl | previous
    · exact holds
    · exact site_assumptions_weaken _ _ _ value
        (site_assumptions_transport _ (shrink p h) env admitted) formula previous
  | equalRefl _ => exact covered_self rfl
  | equalElim _ _ sameIH proofIH =>
    refine siteForce_local _ p env (covered_mono (fun V h same => ?_) (sameIH p env admitted))
    have premise := (siteForce_instantiate _ _ _ _).mp
      (siteForce_transport _ (shrink p h) env (proofIH p env admitted))
    refine (siteForce_instantiate _ _ _ _).mpr ?_
    exact (congrArg (fun value => siteForce values model _ _
      (extend values (transport values (shrink p h) env) value)) same) ▸ premise

/-- Every closed derivation is valid at every point of every model on the product site. -/
theorem closed_site_derivation_sound {n : ℕ} {conclusion : Formula n}
    (derivation : Derivation [] conclusion) (p : D × Hᵒᵈ) (env : Environment values n p) :
    siteForce values model conclusion p env :=
  site_derivation_sound derivation p env (fun _ included => (List.not_mem_nil included).elim)

/-! ## The frame reading at a context -/

variable (model) in
/-- The region value of a formula: the join of the smaller regions where it is forced. -/
def regionValue {n : ℕ} (φ : Formula n) (p : D × Hᵒᵈ) (env : Environment values n p) : H :=
  sSup {V | ∃ h : V ≤ region p,
    siteForce values model φ (below p V) (transport values (shrink p h) env)}

theorem regionValue_le {n : ℕ} (φ : Formula n) (p : D × Hᵒᵈ) (env : Environment values n p) :
    regionValue model φ p env ≤ region p :=
  sSup_le fun _ ⟨h, _⟩ => h

/-- **The frame reading is exact.** Below the region of `p`, a formula is forced exactly on the
regions below its value. -/
theorem siteForce_shrink_iff {n : ℕ} (φ : Formula n) (p : D × Hᵒᵈ) (env : Environment values n p)
    {V : H} (h : V ≤ region p) :
    siteForce values model φ (below p V) (transport values (shrink p h) env) ↔
      V ≤ regionValue model φ p env := by
  constructor
  · intro holds
    exact le_sSup ⟨h, holds⟩
  · intro hV
    refine siteForce_local φ _ _ (covered_of_le_sSup (U := region p) hV fun W hW holds => ?_)
    rw [transport_shrink_shrink]
    have later := siteForce_transport φ (shrink (below p W) (show V ⊓ W ≤ W from inf_le_right)) _ holds
    rwa [transport_shrink_shrink] at later

theorem siteForce_iff_le_regionValue {n : ℕ} (φ : Formula n) (p : D × Hᵒᵈ)
    (env : Environment values n p) :
    siteForce values model φ p env ↔ region p ≤ regionValue model φ p env :=
  ⟨fun holds => le_sSup ⟨le_rfl, siteForce_transport φ (shrink p le_rfl) env holds⟩,
    siteForce_local φ p env⟩

theorem eq_of_le_iff_below {U x y : H} (hx : x ≤ U) (hy : y ≤ U)
    (h : ∀ V, V ≤ U → (V ≤ x ↔ V ≤ y)) : x = y :=
  le_antisymm ((h x hx).mp le_rfl) ((h y hy).mpr le_rfl)

theorem regionValue_bottom {n : ℕ} (p : D × Hᵒᵈ) (env : Environment values n p) :
    regionValue model (.bottom : Formula n) p env = ⊥ := by
  refine eq_of_le_iff_below (regionValue_le _ p env) bot_le fun V h => ?_
  rw [← siteForce_shrink_iff _ p env h]
  exact covered_false_iff

/-- **Conjunction is the meet.** -/
theorem regionValue_both {n : ℕ} (φ ψ : Formula n) (p : D × Hᵒᵈ) (env : Environment values n p) :
    regionValue model (.both φ ψ) p env = regionValue model φ p env ⊓ regionValue model ψ p env := by
  refine eq_of_le_iff_below (regionValue_le _ p env)
    (le_trans inf_le_left (regionValue_le _ p env)) fun V h => ?_
  rw [← siteForce_shrink_iff _ p env h, le_inf_iff, ← siteForce_shrink_iff _ p env h,
    ← siteForce_shrink_iff _ p env h]
  exact Iff.rfl

/-- **Disjunction is the join.** -/
theorem regionValue_either {n : ℕ} (φ ψ : Formula n) (p : D × Hᵒᵈ) (env : Environment values n p) :
    regionValue model (.either φ ψ) p env = regionValue model φ p env ⊔ regionValue model ψ p env := by
  refine eq_of_le_iff_below (regionValue_le _ p env)
    (sup_le (regionValue_le _ p env) (regionValue_le _ p env)) fun V h => ?_
  rw [← siteForce_shrink_iff _ p env h, ← covered_or_le_iff]
  refine covered_congr (U := V) fun W hW => ?_
  rw [transport_shrink_shrink, siteForce_shrink_iff φ p env, siteForce_shrink_iff ψ p env]

/-- The point at another context with the same region. -/
abbrev forward (p : D × Hᵒᵈ) (c : D) : D × Hᵒᵈ :=
  (c, p.2)

/-- The arrow to a later context, keeping the region. -/
def forwardArrow (p : D × Hᵒᵈ) {c : D} (f : p.1 ⟶ c) : p ⟶ forward p c :=
  (f, 𝟙 p.2)

/-- **Implication is a meet over the arrows of the context of the frame's implication.** -/
theorem regionValue_imply {n : ℕ} (φ ψ : Formula n) (p : D × Hᵒᵈ) (env : Environment values n p) :
    regionValue model (.imply φ ψ) p env =
      region p ⊓ ⨅ (c : D) (f : p.1 ⟶ c),
        (regionValue model φ (forward p c) (transport values (forwardArrow p f) env) ⇨
          regionValue model ψ (forward p c) (transport values (forwardArrow p f) env)) := by
  refine eq_of_le_iff_below (regionValue_le _ p env) inf_le_left fun V h => ?_
  rw [← siteForce_shrink_iff _ p env h]
  have split : ∀ (q : D × Hᵒᵈ) (a : below p V ⟶ q),
      transport values a (transport values (shrink p h) env) =
        transport values (shrink (forward p q.1) (le_trans (region_le a) h))
          (transport values (forwardArrow p a.1) env) := by
    intro q a
    rw [← transport_comp, ← transport_comp]
    exact congrArg (fun arrow => transport values arrow env)
      (Prod.ext (show 𝟙 p.1 ≫ a.1 = a.1 ≫ 𝟙 q.1 by rw [Category.id_comp, Category.comp_id])
        (Subsingleton.elim _ _))
  constructor
  · intro holds
    refine le_inf h (le_iInf₂ fun c f => le_himp_iff.mpr ?_)
    have hle : V ⊓ regionValue model φ (forward p c) (transport values (forwardArrow p f) env) ≤
        region (forward p c) := le_trans inf_le_left h
    have target := holds (below (forward p c)
        (V ⊓ regionValue model φ (forward p c) (transport values (forwardArrow p f) env)))
      (f, homOfLE (show V ⊓ regionValue model φ (forward p c)
        (transport values (forwardArrow p f) env) ≤ V from inf_le_left))
    rw [split] at target
    exact (siteForce_shrink_iff ψ (forward p c) _ hle).mp
      (target ((siteForce_shrink_iff φ (forward p c) _ hle).mpr inf_le_right))
  · intro hV q a premise
    rw [split] at premise ⊢
    have hq : region q ≤ V := region_le a
    have hle : region q ≤ region (forward p q.1) := le_trans hq h
    have hφ : region q ≤ regionValue model φ (forward p q.1)
        (transport values (forwardArrow p a.1) env) :=
      (siteForce_shrink_iff φ (forward p q.1) _ hle).mp premise
    have hmeet : V ≤ regionValue model φ (forward p q.1) (transport values (forwardArrow p a.1) env) ⇨
        regionValue model ψ (forward p q.1) (transport values (forwardArrow p a.1) env) :=
      le_trans hV (le_trans inf_le_right (iInf₂_le (f := fun (c : D) (f : p.1 ⟶ c) =>
        regionValue model φ (forward p c) (transport values (forwardArrow p f) env) ⇨
          regionValue model ψ (forward p c) (transport values (forwardArrow p f) env)) q.1 a.1))
    exact (siteForce_shrink_iff ψ (forward p q.1) _ hle).mpr
      (le_trans (le_inf (le_trans hq hmeet) hφ) himp_inf_le)

end Site

end Mettapedia.SetTheory.CarveOuts.Sites
