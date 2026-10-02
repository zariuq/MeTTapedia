import Mettapedia.GSLT.Scope.Arrows
import Mettapedia.GSLT.Scope.UpdateSquares
import Mettapedia.GSLT.Logic.ObserverPresheaf

/-!
# How the four kinds of scope change interact

Forgetting to an observer `E` sends a class of programs `K` to its
saturation `saturation E K`: the programs `E` cannot tell from a member of
`K`.  This is the model side of forgetting in the theory–model framework,
and the S5 possibility modality of `E`.  A translation acts on classes by
the preimage of its reduct.

**Forget and translate.**  For a reduct `β : Str' → Str` between observers
`E'` and `E`:
* the *forth* law (`Forth`: `β` maps `E'`-pairs to `E`-pairs) gives
  "interpret, then forget" ⊆ "forget, then interpret"
  (`saturation_preimage_subset`);
* the *back* law (`Back`: every `E`-neighbour of a reduct is the reduct of an
  `E'`-neighbour) gives the converse (`preimage_saturation_subset`);
* **they commute for every class exactly when both laws hold**
  (`forget_translate_comm_iff`): the reduct is a bounded morphism of the two
  observers.
* The back law is exactly the weak-pullback condition on the square of
  views (`back_iff_isWeakPullback`), so this is Beck–Chevalley for the
  observer views; the predicate form follows from the weak-pullback
  criterion of the observer presheaf (`forget_translate_views_comm_iff`).
* For a translation of scopes, the models of the translated theory, then
  forgotten, are the reducts' preimage of the forgotten models
  (`Translation.saturation_models_translate`).
* Control: a collapsing reduct satisfies the forth law and not the back law,
  and the square fails (`Collapse.back_fails`, `Collapse.square_fails`).

**Restrict and forget.**  Restricting to `V` commutes with forgetting
exactly when `V` is a union of `E`-classes (`restrict_forget_comm_iff`).
Restriction does not commute with joining two forgettings either
(`Join.restrict_sup_ne`).

**Identify and forget.**  Carving by `Φ` and saturating commute for every
class exactly when the models of `Φ` form a union of `E`-classes
(`identify_forget_comm_iff`), in particular when every axiom is visible to
`E` (`isSaturated_models_of_observable`).  Control: identifying `uip` does
not commute with the truncation observer; forgetting after identifying
readmits the two-loop structure (`identify_forget_not_comm`), which is
`forgetting_versus_identifying` read as a square.  Positive: identifying by
the visible sentence `connected` commutes (`connected_commutes`).

**Identify and restrict** commute (`carve_restrict`); forgettings compose
(`saturation_saturation`); translations compose (`Translation.comp`).

**Identifying restricts the site of observers.**  The observers of an
identified scope are exactly the observers above the identification
(`identifiedObservers`), so after identifying no observer separates
identified programs (`identified_not_separated`); after forgetting, the finer
observers remain available (`forget_reversible_identify_not`).

**Forgetting and update support.**  Support of an update is monotone in
neither direction along forgetting.  Along the chain of views
exact ≤ intermediate ≤ trivial, one update is supported by the exact view
(`Coarse.exact_supports`), not by the intermediate one
(`Coarse.fine_not_supports`), and again by the trivial one
(`Coarse.coarse_supports`).  The refresh canary is a second instance of the
first step (`refresh_not_supported`).

**Approximate laws.**  Post-composing an approximate square with a map of
modulus `ω` turns error `ε` into `ω ε` (`ApproxSquare.postcompose`); a
nonexpansive forgetting never increases the error
(`ApproxSquare.forget_nonexpansive`), while a translation that doubles
distances doubles it (`Doubling.translate_doubles`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Scope

open Set
open Mettapedia.Logic.TheoryModel

universe u u' uSent uSent' uX uY uY' uY'' uD

/-! ## Forget and translate -/

section ForgetTranslate

variable {Str : Type u} {Str' : Type u'}

/-- **The forth law**: the reduct maps indistinguishable target programs to
indistinguishable source programs. -/
def Forth (reduct : Str' → Str) (E : Setoid Str) (E' : Setoid Str') : Prop :=
  ∀ ⦃m m' : Str'⦄, E' m m' → E (reduct m) (reduct m')

/-- **The back law**: every source program indistinguishable from a reduct is
the reduct of an indistinguishable target program. -/
def Back (reduct : Str' → Str) (E : Setoid Str) (E' : Setoid Str') : Prop :=
  ∀ ⦃m : Str'⦄ ⦃s : Str⦄, E (reduct m) s → ∃ m', E' m m' ∧ reduct m' = s

variable {reduct : Str' → Str} {E : Setoid Str} {E' : Setoid Str'}

/-- **Forth: interpret, then forget, lies inside forget, then interpret.** -/
theorem saturation_preimage_subset (forth : Forth reduct E E') (K : Set Str) :
    saturation E' (reduct ⁻¹' K) ⊆ reduct ⁻¹' saturation E K := by
  rintro m ⟨m', member, related⟩
  exact ⟨reduct m', member, forth related⟩

/-- **Back: forget, then interpret, lies inside interpret, then forget.** -/
theorem preimage_saturation_subset (back : Back reduct E E') (K : Set Str) :
    reduct ⁻¹' saturation E K ⊆ saturation E' (reduct ⁻¹' K) := by
  rintro m ⟨s, member, related⟩
  obtain ⟨m', related', equal⟩ := back (E.symm' related)
  refine ⟨m', ?_, E'.symm' related'⟩
  change reduct m' ∈ K
  rw [equal]
  exact member

/-- **Forgetting and translating commute for every class exactly when the
reduct satisfies the forth and the back laws.** -/
theorem forget_translate_comm_iff :
    (∀ K : Set Str, reduct ⁻¹' saturation E K = saturation E' (reduct ⁻¹' K)) ↔
      Forth reduct E E' ∧ Back reduct E E' := by
  constructor
  · intro comm
    constructor
    · intro m m' related
      have member : m' ∈ saturation E' (reduct ⁻¹' {reduct m}) := ⟨m, rfl, related⟩
      rw [← comm] at member
      obtain ⟨s, equal, related'⟩ := member
      change s = reduct m at equal
      rw [equal] at related'
      exact related'
    · intro m s related
      have member : m ∈ reduct ⁻¹' saturation E {s} := ⟨s, rfl, E.symm' related⟩
      rw [comm] at member
      obtain ⟨m', equal, related'⟩ := member
      exact ⟨m', E'.symm' related', equal⟩
  · rintro ⟨forth, back⟩ K
    exact Subset.antisymm (preimage_saturation_subset back K) (saturation_preimage_subset forth K)

/-- The map of views induced by a reduct satisfying the forth law. -/
def viewMap (forth : Forth reduct E E') : Quotient E' → Quotient E :=
  Quotient.map reduct fun _ _ related => forth related

open Mettapedia.GSLT.AdmissibleContextCongruence in
/-- **The back law is the weak-pullback condition** on the square of views
`Quotient.mk E ∘ reduct = viewMap ∘ Quotient.mk E'`. -/
theorem back_iff_isWeakPullback (forth : Forth reduct E E') :
    Back reduct E E' ↔
      IsWeakPullback reduct (Quotient.mk E') (Quotient.mk E) (viewMap forth) := by
  constructor
  · intro back s c equal
    induction c using Quotient.inductionOn with
    | h m =>
      obtain ⟨m', related, image⟩ := back (E.symm' (Quotient.exact equal))
      exact ⟨m', image, Quotient.sound (E'.symm' related)⟩
  · intro weak m s related
    obtain ⟨m', image, sameView⟩ := weak (x := s) (y := Quotient.mk E' m)
      (Quotient.sound (E.symm' related))
    exact ⟨m', E'.symm' (Quotient.exact sameView), image⟩

open Mettapedia.GSLT.AdmissibleContextCongruence in
/-- **Beck–Chevalley for the views**: pulling back along the view map then
taking the image under the target view agrees with taking the image under
the source view then pulling back along the reduct, for every predicate,
exactly under the back law. -/
theorem forget_translate_views_comm_iff (forth : Forth reduct E E') :
    (∀ φ : Set Str, viewMap forth ⁻¹' (Quotient.mk E '' φ) =
        Quotient.mk E' '' (reduct ⁻¹' φ)) ↔ Back reduct E E' := by
  rw [beckChevalley_exists_iff reduct (Quotient.mk E') (Quotient.mk E) (viewMap forth)
    (fun _ => rfl), ← back_iff_isWeakPullback forth]

variable {Sent : Type uSent} {Sent' : Type uSent'}
  {Sat : Str → Sent → Prop} {Sat' : Str' → Sent' → Prop}

/-- **Translating a theory, then forgetting, is forgetting its models, then
taking reducts' preimage**, for a translation whose reduct is a bounded
morphism of the observers. -/
theorem Translation.saturation_models_translate (τ : Translation Sat Sat')
    (forth : Forth τ.reduct E E') (back : Back τ.reduct E E') (T : Set Sent) :
    saturation E' (models Sat' (τ.translate '' T)) =
      τ.reduct ⁻¹' saturation E (models Sat T) := by
  rw [τ.models_translate]
  exact ((forget_translate_comm_iff.mpr ⟨forth, back⟩) (models Sat T)).symm

end ForgetTranslate

/-! ### Control: a collapsing reduct -/

namespace Collapse

/-- The observer that identifies the two booleans. -/
def totalBool : Setoid Bool where
  r _ _ := True
  iseqv := ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩

/-- The trivial observer on the single target program. -/
def totalUnit : Setoid PUnit.{1} where
  r _ _ := True
  iseqv := ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩

theorem forth_holds : Forth collapse.reduct totalBool totalUnit :=
  fun _ _ _ => trivial

/-- The source observer relates `true` to `false`, which is not a reduct. -/
theorem back_fails : ¬ Back collapse.reduct totalBool totalUnit := by
  intro back
  obtain ⟨_, _, equal⟩ := back (m := PUnit.unit) (s := false) trivial
  exact Bool.noConfusion (equal : true = false)

/-- **The square fails** at the class `{false}`: forgetting then interpreting
reaches the target program, interpreting then forgetting reaches nothing. -/
theorem square_fails :
    collapse.reduct ⁻¹' saturation totalBool {false} ≠
      saturation totalUnit (collapse.reduct ⁻¹' {false}) := by
  intro equal
  have member : PUnit.unit ∈ collapse.reduct ⁻¹' saturation totalBool {false} :=
    ⟨false, rfl, trivial⟩
  rw [equal] at member
  obtain ⟨_, image, _⟩ := member
  exact Bool.noConfusion (image : true = false)

end Collapse

/-! ## Restrict and forget -/

section RestrictForget

variable {Str : Type u}

/-- A class is **saturated** for an observer when it is a union of its
classes. -/
def IsSaturated (E : Setoid Str) (V : Set Str) : Prop :=
  ∀ ⦃v s : Str⦄, v ∈ V → E v s → s ∈ V

/-- The inclusion of a fragment satisfies the forth law for the restricted
observer. -/
theorem forth_restrict (E : Setoid Str) (V : Set Str) :
    Forth (Subtype.val : V → Str) E (E.comap Subtype.val) :=
  fun _ _ related => related

/-- The inclusion satisfies the back law exactly when the fragment is
saturated. -/
theorem back_restrict_iff (E : Setoid Str) (V : Set Str) :
    Back (Subtype.val : V → Str) E (E.comap Subtype.val) ↔ IsSaturated E V := by
  constructor
  · intro back v s member related
    obtain ⟨m', _, equal⟩ := back (m := ⟨v, member⟩) related
    rw [← equal]
    exact m'.2
  · intro saturated m s related
    exact ⟨⟨s, saturated m.2 related⟩, related, rfl⟩

/-- **Restricting and forgetting commute for every class exactly when the
fragment is a union of observer classes.** -/
theorem restrict_forget_comm_iff (E : Setoid Str) (V : Set Str) :
    (∀ K : Set Str, (Subtype.val : V → Str) ⁻¹' saturation E K =
        saturation (E.comap Subtype.val) ((Subtype.val : V → Str) ⁻¹' K)) ↔
      IsSaturated E V := by
  rw [forget_translate_comm_iff, back_restrict_iff]
  exact ⟨fun both => both.2, fun saturated => ⟨forth_restrict E V, saturated⟩⟩

/-- Control: the fragment `{true}` is not saturated for the observer that
identifies the two booleans. -/
theorem singleton_not_saturated : ¬ IsSaturated Collapse.totalBool {true} := by
  intro saturated
  exact Bool.noConfusion ((saturated rfl trivial : false ∈ ({true} : Set Bool)) :
    false = true)

end RestrictForget

/-! ### Restriction does not commute with joining forgettings -/

namespace Join

/-- The observer with classes `{0, 1}` and `{2}`. -/
def first : Setoid (Fin 3) where
  r x y := x = y ∨ (x ≠ 2 ∧ y ≠ 2)
  iseqv := ⟨by decide, fun {x y} => by revert x y; decide,
    fun {x y z} => by revert x y z; decide⟩

/-- The observer with classes `{0}` and `{1, 2}`. -/
def second : Setoid (Fin 3) where
  r x y := x = y ∨ (x ≠ 0 ∧ y ≠ 0)
  iseqv := ⟨by decide, fun {x y} => by revert x y; decide,
    fun {x y z} => by revert x y z; decide⟩

/-- The fragment of the two ends. -/
def ends : Set (Fin 3) :=
  {x | x ≠ 1}

/-- The left end. -/
def endZero : ends :=
  ⟨0, show (0 : Fin 3) ≠ 1 by decide⟩

/-- The right end. -/
def endTwo : ends :=
  ⟨2, show (2 : Fin 3) ≠ 1 by decide⟩

/-- Jointly the two observers identify the ends, through the middle. -/
theorem sup_relates_ends : (first ⊔ second) 0 2 := by
  rw [Setoid.sup_eq_eqvGen]
  exact Relation.EqvGen.trans _ 1 _
    (Relation.EqvGen.rel _ _ (Or.inl (Or.inr ⟨by decide, by decide⟩)))
    (Relation.EqvGen.rel _ _ (Or.inr (Or.inr ⟨by decide, by decide⟩)))

/-- On the ends, each restricted observer is equality. -/
theorem restricted_eq {observer : Setoid (Fin 3)}
    (isFirstOrSecond : observer = first ∨ observer = second)
    {x y : ends} (related : observer.comap Subtype.val x y) : x = y := by
  apply Subtype.ext
  have hx := x.2
  have hy := y.2
  change x.1 ≠ 1 at hx
  change y.1 ≠ 1 at hy
  rcases isFirstOrSecond with rfl | rfl
  · change x.1 = y.1 ∨ (x.1 ≠ 2 ∧ y.1 ≠ 2) at related
    revert related hx hy
    generalize x.1 = a
    generalize y.1 = b
    revert a b
    decide
  · change x.1 = y.1 ∨ (x.1 ≠ 0 ∧ y.1 ≠ 0) at related
    revert related hx hy
    generalize x.1 = a
    generalize y.1 = b
    revert a b
    decide

/-- **Restriction does not commute with joining forgettings**: jointly
forgetting then restricting identifies the ends; restricting then jointly
forgetting does not. -/
theorem restrict_sup_ne :
    (first ⊔ second).comap (Subtype.val : ends → Fin 3) endZero endTwo ∧
      ¬ (first.comap (Subtype.val : ends → Fin 3) ⊔ second.comap Subtype.val)
        endZero endTwo := by
  refine ⟨sup_relates_ends, fun related => ?_⟩
  rw [Setoid.sup_eq_eqvGen] at related
  have collapse : ∀ {x y : ends}, Relation.EqvGen
      (fun x y => first.comap Subtype.val x y ∨ second.comap Subtype.val x y) x y → x = y := by
    intro x y generated
    induction generated with
    | rel x y step =>
      rcases step with step | step
      · exact restricted_eq (Or.inl rfl) step
      · exact restricted_eq (Or.inr rfl) step
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ih' => exact ih.trans ih'
  exact absurd (congrArg Subtype.val (collapse related)) (by decide)

end Join

/-! ## Identify and forget -/

section IdentifyForget

variable {Str : Type u} {Sent : Type uSent} {Sat : Str → Sent → Prop}

/-- **Identifying and forgetting commute for every class exactly when the
models of the axioms form a union of observer classes.** -/
theorem identify_forget_comm_iff (E : Setoid Str) (M : Set Str) :
    (∀ K : Set Str, saturation E (K ∩ M) = saturation E K ∩ M) ↔ IsSaturated E M := by
  constructor
  · intro comm m s member related
    have inside : s ∈ saturation E ({m} ∩ M) := ⟨m, ⟨rfl, member⟩, related⟩
    rw [comm] at inside
    exact inside.2
  · intro saturated K
    apply Subset.antisymm
    · rintro m ⟨k, ⟨inK, inM⟩, related⟩
      exact ⟨⟨k, inK, related⟩, saturated inM related⟩
    · rintro m ⟨⟨k, inK, related⟩, inM⟩
      exact ⟨k, ⟨inK, saturated inM (E.symm' related)⟩, related⟩

/-- Axioms visible to the observer have a saturated class of models. -/
theorem isSaturated_models_of_observable {E : Setoid Str} {Φ : Set Sent}
    (visible : Φ ⊆ observable Sat E) : IsSaturated E (models Sat Φ) :=
  fun _ _ model related _ member => (visible member related).mp (model member)

/-- Carving a saturation by visible axioms is saturating the carve. -/
theorem carve_saturation_of_observable {E : Setoid Str} {Φ : Set Sent}
    (visible : Φ ⊆ observable Sat E) (K : Set Str) :
    saturation E (carve Sat K Φ) = carve Sat (saturation E K) Φ :=
  (identify_forget_comm_iff E (models Sat Φ)).mpr (isSaturated_models_of_observable visible) K

open IdentityProofs in
/-- **Control: identifying `uip` does not commute with the truncation
observer.**  Forgetting after identifying readmits the two-loop structure;
identifying after forgetting excludes it. -/
theorem identify_forget_not_comm :
    xorModel.{u} ∈ saturation truncation (carve IdStructure.Sat {eqModel PUnit} {.uip}) ∧
      xorModel.{u} ∉ carve IdStructure.Sat (saturation truncation {eqModel PUnit}) {.uip} :=
  ⟨⟨eqModel PUnit, ⟨rfl, fun φ member => by
      rw [show φ = IdSentence.uip from member]
      exact eqModel_sat_uip PUnit⟩, eqModel_punit_truncation_xor⟩,
    fun member => xorModel_not_uip (member.2 rfl)⟩

open IdentityProofs in
/-- **Positive**: the visible axiom `connected` commutes with the truncation
observer. -/
theorem connected_commutes (K : Set IdStructure.{u}) :
    saturation truncation (carve IdStructure.Sat K {.connected}) =
      carve IdStructure.Sat (saturation truncation K) {.connected} :=
  carve_saturation_of_observable (fun φ member => by
    rw [show φ = IdSentence.connected from member]
    exact connected_observable) K

/-- **Forgettings compose**: saturating by a finer then a coarser observer is
saturating by the coarser. -/
theorem saturation_saturation {E E' : Setoid Str} (finer : E ≤ E') (K : Set Str) :
    saturation E' (saturation E K) = saturation E' K := by
  apply Subset.antisymm
  · rintro m ⟨m', ⟨k, inK, related⟩, related'⟩
    exact ⟨k, inK, E'.trans' (finer related) related'⟩
  · rintro m ⟨k, inK, related⟩
    exact ⟨k, subset_saturation E K inK, related⟩

end IdentifyForget

/-! ## Identifying restricts the site of observers -/

section Site

variable {X : Type u} (R : Setoid X)

/-- **Identifying restricts the observers to those above the
identification**: the observers of the identified scope are exactly the
observers of the original scope that relate every identified pair (Mathlib's
correspondence theorem).  Forgetting moves within this site; identifying cuts
the site down to the principal up-set above `R`. -/
def identifiedObservers : Setoid (Quotient R) ≃o {E : Setoid X // R ≤ E} :=
  (Setoid.correspondence R).symm

/-- **After identifying, no observer separates identified programs.** -/
theorem identified_not_separated (E' : Setoid (Quotient R)) {x y : X} (related : R x y) :
    E'.comap (Quotient.mk R) x y := by
  change E' (Quotient.mk R x) (Quotient.mk R y)
  rw [Quotient.sound related]

/-- The observer that separates every pair of programs. -/
def exact : Setoid X where
  r := Eq
  iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩

/-- **Forgetting is reversible, identifying is not.**  Forgetting to the
observer that identifies the two booleans leaves the exact observer
available, which separates them; after identifying them, no observer of the
identified scope does. -/
theorem forget_reversible_identify_not :
    ¬ (exact : Setoid Bool) true false ∧
      ∀ E' : Setoid (Quotient Collapse.totalBool),
        E'.comap (Quotient.mk Collapse.totalBool) true false :=
  ⟨fun equal => Bool.noConfusion equal,
    fun E' => identified_not_separated Collapse.totalBool E' trivial⟩

end Site

/-! ## Forgetting and update support -/

namespace Coarse

/-- Four states, and an update that separates the first two. -/
def update : Fin 4 → Fin 4
  | 0 => 2
  | 1 => 3
  | x => x

/-- A view that identifies `0` with `1` and nothing else. -/
def fine : Fin 4 → Fin 3
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | _ => 2

/-- The view that forgets everything. -/
def coarse : Fin 4 → Unit :=
  fun _ => ()

theorem coarse_factors_fine : ∀ x, coarse x = (fun _ : Fin 3 => ()) (fine x) :=
  fun _ => rfl

/-- **The exact view supports the update**, as it supports every update. -/
theorem exact_supports : Supports (id : Fin 4 → Fin 4) update :=
  ⟨update, fun _ => rfl⟩

/-- **The coarser view supports the update.** -/
theorem coarse_supports : Supports coarse update :=
  ⟨id, fun _ => rfl⟩

/-- **The finer view does not**: `0` and `1` share its view and are
separated after the update. -/
theorem fine_not_supports : ¬ Supports fine update :=
  not_supports_of_split (x := 0) (y := 1) rfl (by decide)

end Coarse

/-! ## Approximate laws -/

section Approximate

variable {X : Type uX} {Y : Type uY} {Y' : Type uY'} {Y'' : Type uY''} {D : Type uD}

/-- **Post-composing an approximate square with a map of modulus `ω`** turns
the error `ε` into `ω ε`. -/
theorem ApproxSquare.postcompose [Preorder D] {dist' : Y' → Y' → D} {dist'' : Y'' → Y'' → D}
    {view : X → Y} {view' : X → Y'} {f : X → X} {f' : Y → Y'} {ε : D}
    (square : ApproxSquare dist' view view' f f' ε) (c : Y' → Y'') {ω : D → D}
    (ω_mono : Monotone ω) (modulus : ∀ a b, dist'' (c a) (c b) ≤ ω (dist' a b)) :
    ApproxSquare dist'' view (fun x => c (view' x)) f (fun y => c (f' y)) (ω ε) :=
  fun x => (modulus _ _).trans (ω_mono (square x))

/-- **A nonexpansive forgetting never increases the error.** -/
theorem ApproxSquare.forget_nonexpansive [Preorder D] {dist' : Y' → Y' → D}
    {dist'' : Y'' → Y'' → D} {view : X → Y} {view' : X → Y'} {f : X → X} {f' : Y → Y'}
    {ε : D}
    (square : ApproxSquare dist' view view' f f' ε) (forget : Y' → Y'')
    (nonexpansive : ∀ a b, dist'' (forget a) (forget b) ≤ dist' a b) :
    ApproxSquare dist'' view (fun x => forget (view' x)) f (fun y => forget (f' y)) ε :=
  square.postcompose forget (ω := id) monotone_id nonexpansive

end Approximate

namespace Doubling

/-- **A translation that doubles distances doubles the error**: the square of
the successor step, translated by doubling, errs by exactly `2`. -/
theorem translate_doubles :
    ApproxSquare natDist id (fun x => abstract (id x)) Succ.step (fun y => abstract (id y)) 2 ∧
      ¬ ApproxSquare natDist id (fun x => abstract (id x)) Succ.step
        (fun y => abstract (id y)) 1 := by
  refine ⟨Succ.square.postcompose abstract (ω := fun t => 2 * t)
    (fun _ _ le => Nat.mul_le_mul_left 2 le) (fun a b => (abstract_doubles a b).le), ?_⟩
  intro within
  have bound := within 0
  change natDist 2 0 ≤ 1 at bound
  unfold natDist at bound
  omega

end Doubling

end Mettapedia.GSLT.Scope
