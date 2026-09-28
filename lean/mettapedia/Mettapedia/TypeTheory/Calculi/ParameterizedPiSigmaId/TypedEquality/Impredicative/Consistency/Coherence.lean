import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.InterpLaws

/-!
# Coherence of the codes with the interpretation

A carrier of the quantifier and equation codes is also a closed type of the
rule package. Every carrier built from `prop`, the numbers and rigid base
types is interpreted at every level and world by the partial equivalence of a
common meaning:

* at a data carrier, that is the relation of the carrier: its terms compute
  the same numerals;
* at a generic carrier, terms with one meaning.

At a function carrier the interpretation is Kripke: related functions send
related arguments to related results at every world reached by a morphism.
Two such functions have a common meaning, and it is written as a formula: the
meaning of a term at a generic carrier is the truth of its applications to
fresh generics and to closed representatives of data values. No choice is
involved. At a function into data, the Kripke relation is the relation of the
carrier: a function from a generic carrier is tested at a fresh generic, and a
renaming that is not a morphism of worlds factors through two worlds placed
side by side.

In the model `holds` is rigid; the decoding equations of the package hold in
the sense that both sides have the same partial equivalence:

* `holds (imp p q)` and `holds p → holds q`;
* `holds (all@A f)` and `(x : A) → holds (f x)`;
* `holds (eq@A x y)` and the identity type of `x` and `y` at `A`.

Each code constant is related to itself at its declared type.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

open Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

/-! ## Carriers as types -/

/-- A carrier as a closed type of the rule package. -/
def Carrier.term (M : Model Head L) : {k : Kind} → Carrier k → Tm Head 0
  | _, .prop => .const M.prop
  | _, .num => .const M.num
  | _, .rigid T => .const T
  | _, .arr A B => .pi (A.term M) (Presentation.rename wk (B.term M))

/-- The carriers the model interprets as types: every carrier built from the
propositions, the numbers, and the rigid base types other than the codes and
their decoder. -/
inductive Carrier.Interpretable (M : Model Head L) : {k : Kind} → Carrier k → Prop where
  | prop : Carrier.Interpretable M .prop
  | num : Carrier.Interpretable M .num
  | rigid {T : DeclName} (role : M.roles T = .rigid) (notProp : T ≠ M.prop)
      (notHolds : T ≠ M.holds) : Carrier.Interpretable M (.rigid T)
  | arr {k k' : Kind} {A : Carrier k} {B : Carrier k'} (dom : Carrier.Interpretable M A)
      (cod : Carrier.Interpretable M B) : Carrier.Interpretable M (.arr A B)

/-! ## Meanings of the generic carriers -/

section Setting

variable {S : Reading Head}

/-- A meaning at `prop` is a meaning of a code. -/
theorem Read.prop_inv {n : Nat} {ξ : World S n} {t : Tm Head n} {P : S.P}
    (read : Read S ξ t .prop P) : Truth S ξ t P := by
  cases read with
  | prop truth => exact truth

/-- A meaning at a data carrier is the value of a term related to itself. -/
theorem Read.data_inv {n : Nat} {ξ : World S n} {t : Tm Head n} {D : Carrier .data}
    {v : D.V S} (read : Read S ξ t D v) :
    ∃ related : DataEq S D t t, v = dataValue S D t related := by
  cases read with
  | data related => exact ⟨related, rfl⟩

/-- Under the reading by truth values, a code holds exactly when its truth
value does. -/
theorem Truth.holds_iff {T : Setting Head} (laws : T.truthReading.Laws) {n : Nat}
    {ξ : World T.truthReading n} {c : Tm Head n} {P : Prop}
    (truth : Truth T.truthReading ξ c P) : (∃ P', Truth T.truthReading ξ c P' ∧ P') ↔ P :=
  ⟨fun ⟨_, truth', h⟩ => (Truth.deterministic laws truth' truth).mp h, fun h => ⟨P, truth, h⟩⟩

/-- The dependent function family of a non-dependent function type whose
domain and codomain are read the same way at every world. -/
def PiRel.arrow {n : Nat} (ξ : World S n) (D C : ∀ {m : Nat}, World S m → Rel Head m) :
    PiRel Head ξ where
  dom := fun {_ ξ' _} _ => D ξ'
  cod := fun {_ ξ' _} _ {_} _ => C ξ'

namespace Carrier

variable (S) in
/-- The partial equivalence of a carrier: terms with a common meaning. -/
def rel {k : Kind} (A : Carrier k) {n : Nat} (ξ : World S n) : Rel Head n :=
  fun a b => ∃ v, Read S ξ a A v ∧ Read S ξ b A v

/-- At `prop`, a common meaning is a common meaning of codes. -/
theorem rel_prop {n : Nat} (ξ : World S n) :
    Carrier.prop.rel S ξ = fun c c' => ∃ P, Truth S ξ c P ∧ Truth S ξ c' P :=
  funext fun _ => funext fun _ => propext
    ⟨fun ⟨P, ra, rb⟩ => ⟨P, ra.prop_inv, rb.prop_inv⟩, fun ⟨P, ta, tb⟩ => ⟨P, .prop ta, .prop tb⟩⟩

/-- At a rigid base type, every two terms have a common meaning. -/
theorem rel_rigid (T : DeclName) {n : Nat} (ξ : World S n) :
    (Carrier.rigid T).rel S ξ = fun _ _ => True :=
  funext fun _ => funext fun _ => propext ⟨fun _ => trivial, fun _ => ⟨(), .rigid, .rigid⟩⟩

/-- At a data carrier, a common meaning is the relation of the carrier. -/
theorem rel_data (laws : S.Laws) (D : Carrier .data) {n : Nat} (ξ : World S n) :
    D.rel S ξ = DataEq S D := by
  funext a b
  apply propext
  constructor
  · rintro ⟨v, ra, rb⟩
    obtain ⟨relA, rfl⟩ := ra.data_inv
    obtain ⟨relB, equal⟩ := rb.data_inv
    exact dataValue_exact laws.toDataLaws equal
  · intro related
    have relA := related.refl_left laws.toDataLaws
    have relB := related.refl_right laws.toDataLaws
    refine ⟨dataValue S D a relA, .data relA, ?_⟩
    rw [dataValue_sound relA relB related]
    exact .data relB

/-- A term related to itself at a data carrier has a common meaning with itself. -/
theorem rel_of_data {D : Carrier .data} {n : Nat} {ξ : World S n} {a : Tm Head n}
    (related : DataEq S D a a) : D.rel S ξ a a :=
  ⟨_, .data related, .data related⟩

variable (S) in
/-- The meet of a family of meanings at a generic carrier: the reading's meet at
`prop`, pointwise at a function. -/
def meet : (B : Carrier .gen) → {ι : Type} → (ι → B.V S) → B.V S
  | .prop, _, f => S.meet f
  | .rigid _, _, _ => ()
  | @Carrier.arr _ .gen _ B', _, f => fun a => meet B' (fun i => f i a)
termination_by B => B.size
decreasing_by exact Carrier.size_cod _ _

/-- The meet of a family whose members are all one meaning is that meaning. -/
theorem meet_const (laws : S.Laws) : ∀ (B : Carrier .gen) {ι : Type} (f : ι → B.V S)
    (x : B.V S), (∀ i, f i = x) → Nonempty ι → B.meet S f = x
  | .prop, _, f, x, all, nonempty => by
      rw [meet]
      exact laws.meet_const f x all nonempty
  | .rigid _, _, _, _, _, _ => rfl
  | @Carrier.arr _ .gen _ B', _, f, x, all, nonempty => by
      rw [meet]
      funext a
      exact meet_const laws B' (fun i => f i a) (x a) (fun i => congrFun (all i) a) nonempty
termination_by B => B.size
decreasing_by exact Carrier.size_cod _ _

variable (S) in
/-- A meaning of every generic carrier. -/
def default : (B : Carrier .gen) → B.V S
  | .prop => S.top
  | .rigid _ => ()
  | @Carrier.arr _ .gen _ B' => fun _ => default B'
termination_by B => B.size
decreasing_by exact Carrier.size_cod _ _

variable (S) in
/-- The meaning of a term at a generic carrier, written as a formula: at `prop`
the truth of the term; at a function on a data carrier, at each value the meet
of its meanings at the closed representatives of the value; at a function on a
generic carrier, its meaning at a fresh generic. -/
def meaning : (B : Carrier .gen) → {n : Nat} → World S n → Tm Head n → B.V S
  | .prop, _, ξ, t => S.meet (ι := {X : S.P // Truth S ξ t X}) (fun X => X.1)
  | .rigid _, _, _, _ => ()
  | @Carrier.arr .data .gen A B', _, ξ, t => fun q =>
      meet S B' (ι := {s : Tm Head 0 // ∃ related : DataEq S A s s, dataValue S A s related = q})
        (fun s => meaning B' ξ (.app t (liftClosed s.1)))
  | @Carrier.arr .gen .gen A B', _, ξ, t => fun v =>
      meaning B' (ξ.snoc ⟨A, v⟩) (.app (Presentation.rename wk t) (.var 0))
termination_by B => B.size
decreasing_by
  · exact Carrier.size_cod _ _
  · exact Carrier.size_cod _ _

/-- A closed representative of a data value, as a term of any world, reads as
the value. -/
theorem read_representative {A : Carrier .data} {n : Nat} {ξ : World S n} {s : Tm Head 0}
    (related : DataEq S A s s) :
    Read S ξ (liftClosed s) A (dataValue S A s related) := by
  rw [← dataValue_rename related Fin.elim0 (related.rename₂ Fin.elim0)]
  exact .data _

/-- A meaning of a term at a generic carrier is its formula. -/
theorem meaning_eq (laws : S.Laws) : ∀ (B : Carrier .gen) {n : Nat} {ξ : World S n}
    {t : Tm Head n} {w : B.V S}, Read S ξ t B w → B.meaning S ξ t = w
  | .prop, _, _, _, w, read => by
      rw [meaning]
      exact laws.meet_const _ w (fun X => Truth.deterministic laws X.2 read.prop_inv)
        ⟨⟨w, read.prop_inv⟩⟩
  | .rigid _, _, _, _, _, _ => rfl
  | @Carrier.arr .data .gen A B', _, ξ, t, w, read => by
      cases read with
      | dataArg read' =>
          rw [meaning]
          funext q
          refine meet_const laws B' _ (w q) (fun s => ?_) ?_
          · obtain ⟨s, related, equal⟩ := s
            have h := read' (Morph.id ξ) (related.rename₂ (Fin.elim0 : Ren 0 _))
            rw [rename_id, dataValue_rename related Fin.elim0, equal] at h
            exact meaning_eq laws B' h
          · obtain ⟨s, related, equal⟩ := dataValue_surjective q
            exact ⟨⟨s, related, equal⟩⟩
  | @Carrier.arr .gen .gen A B', _, _, _, _, read => by
      cases read with
      | genericArg read' =>
          rw [meaning]
          funext v
          exact meaning_eq laws B' (read' v)
termination_by B => B.size
decreasing_by
  · exact Carrier.size_cod _ _
  · exact Carrier.size_cod _ _

/-! ## Function types between carriers -/

/-- Two terms related at a function type into a generic carrier both read at
the formula of the first. -/
theorem read_meaning (laws : S.Laws) {k : Kind} {A : Carrier k} {B : Carrier .gen}
    {n : Nat} {ξ : World S n} {f g : Tm Head n}
    (related : (PiRel.arrow ξ (A.rel S) (B.rel S)).rel f g) :
    Read S ξ f (.arr A B) ((Carrier.arr A B).meaning S ξ f) ∧
      Read S ξ g (.arr A B) ((Carrier.arr A B).meaning S ξ f) := by
  cases k with
  | data =>
      -- At a realizer `s` in a world reached by `ρ`, the applications of `f` and `g`
      -- have a common meaning, which is the formula at the value of `s`.
      have atRealizer : ∀ {m : Nat} {ξ' : World S m} {ρ : Ren n m} (w : Morph ξ ξ' ρ)
          {s : Tm Head m} (rs : DataEq S A s s),
          Read S ξ' (.app (Presentation.rename ρ f) s) B
              ((Carrier.arr A B).meaning S ξ f (dataValue S A s rs)) ∧
            Read S ξ' (.app (Presentation.rename ρ g) s) B
              ((Carrier.arr A B).meaning S ξ f (dataValue S A s rs)) := by
        intro m ξ' ρ w s rs
        obtain ⟨u, rf, rg⟩ := related w (rel_of_data rs) (rel_of_data rs)
        suffices e : (Carrier.arr A B).meaning S ξ f (dataValue S A s rs) = u by
          rw [e]
          exact ⟨rf, rg⟩
        rw [meaning]
        refine meet_const laws B _ u (fun s₀ => ?_) ?_
        · obtain ⟨s₀, r₀, equal⟩ := s₀
          have lift₀ : DataEq S A (liftClosed s₀ : Tm Head n) (liftClosed s₀) :=
            r₀.rename₂ Fin.elim0
          obtain ⟨u₀, rf₀, _⟩ := related (Morph.id ξ) (rel_of_data lift₀) (rel_of_data lift₀)
          rw [rename_id] at rf₀
          rw [meaning_eq laws B rf₀]
          have liftM : DataEq S A (liftClosed s₀ : Tm Head m) (liftClosed s₀) :=
            r₀.rename₂ Fin.elim0
          have same : DataEq S A (liftClosed s₀ : Tm Head m) s := by
            apply dataValue_exact laws.toDataLaws (rel := liftM) (rel' := rs)
            rw [dataValue_liftClosed r₀, equal]
          have hA : A.rel S ξ' (liftClosed s₀) s := by
            rw [rel_data laws]
            exact same
          obtain ⟨u₁, rf₁, rg₁⟩ := related w (rel_of_data liftM) hA
          have rf₀' := rf₀.rename w
          simp only [Presentation.rename, rename_liftClosed] at rf₀'
          rw [Read.deterministic laws rf₀' rf₁]
          exact Read.deterministic laws rg₁ rg
        · exact ⟨⟨close S s, rs.closure, dataValue_close rs rs.closure⟩⟩
      exact ⟨.dataArg fun w _ rs => (atRealizer w rs).1,
        .dataArg fun w _ rs => (atRealizer w rs).2⟩
  | gen =>
      rw [meaning]
      have atGeneric : ∀ v : A.V S, ∃ u,
          Read S (ξ.snoc ⟨A, v⟩) (.app (Presentation.rename wk f) (.var 0)) B u ∧
            Read S (ξ.snoc ⟨A, v⟩) (.app (Presentation.rename wk g) (.var 0)) B u := by
        intro v
        have hv : A.rel S (ξ.snoc ⟨A, v⟩) (.var 0) (.var 0) :=
          ⟨v, Read.generic' _ rfl, Read.generic' _ rfl⟩
        exact related (Morph.wk ξ ⟨A, v⟩) hv hv
      refine ⟨.genericArg fun v => ?_, .genericArg fun v => ?_⟩
      · obtain ⟨u, rf, _⟩ := atGeneric v
        rw [meaning_eq laws B rf]
        exact rf
      · obtain ⟨u, rf, rg⟩ := atGeneric v
        rw [meaning_eq laws B rf]
        exact rg

/-- A function type into a generic carrier relates two terms exactly when they
have a common meaning. -/
theorem arrow_iff (laws : S.Laws) {k : Kind} {A : Carrier k} {B : Carrier .gen} {n : Nat}
    {ξ : World S n} {f g : Tm Head n} :
    (PiRel.arrow ξ (A.rel S) (B.rel S)).rel f g ↔ (Carrier.arr A B).rel S ξ f g := by
  constructor
  · intro related
    exact ⟨_, read_meaning laws related⟩
  · rintro ⟨φ, rf, rg⟩ _ _ _ w _ _ _ ⟨v, ra, rb⟩
    exact ⟨φ v, Read.app (rf.rename w) ra, Read.app (rg.rename w) rb⟩

/-- The partial equivalence of a function type into a generic carrier is that
of the function carrier. -/
theorem arrow_rel (laws : S.Laws) {k : Kind} {A : Carrier k} {B : Carrier .gen} {n : Nat}
    (ξ : World S n) :
    (PiRel.arrow ξ (A.rel S) (B.rel S)).rel = (Carrier.arr A B).rel S ξ :=
  funext fun _ => funext fun _ => propext (arrow_iff laws)

/-- A world of the given size. -/
def blankWorld (m : Nat) : World S m := fun _ => ⟨.prop, S.top⟩

/-- A function type into a data carrier relates two terms exactly when the
carrier does. -/
theorem arrow_data_iff (laws : S.Laws) {k : Kind} {A : Carrier k} {B : Carrier .data}
    {n : Nat} {ξ : World S n} {f g : Tm Head n} :
    (PiRel.arrow ξ (A.rel S) (B.rel S)).rel f g ↔ DataEq S (.arr A B) f g := by
  cases k with
  | gen =>
      show _ ↔ DataEq S.toDataSetting B _ _
      constructor
      · intro related
        have hv : A.rel S (ξ.snoc ⟨A, default S A⟩) (.var 0) (.var 0) :=
          ⟨default S A, Read.generic' _ rfl, Read.generic' _ rfl⟩
        have h := related (Morph.wk ξ ⟨A, default S A⟩) hv hv
        show DataEq S.toDataSetting B _ _
        rw [← rel_data laws]
        exact h
      · intro related _ _ ρ _ a a' _ _
        show B.rel S _ _ _
        rw [rel_data laws]
        have h := DataEq.subst₂ B related (consSub a (renSub ρ)) (consSub a' (renSub ρ))
        simp only [Presentation.subst, subst_consSub_rename_wk, consSub_zero,
          subst_renSub] at h
        exact h
  | data =>
      constructor
      · intro related m ρ s s' rs
        have rs' : A.rel S ((ξ).append (blankWorld m)) (Presentation.rename (Fin.natAdd n) s)
            (Presentation.rename (Fin.natAdd n) s') := by
          rw [rel_data laws]
          exact rs.rename₂ _
        have hs : A.rel S ((ξ).append (blankWorld m)) (Presentation.rename (Fin.natAdd n) s)
            (Presentation.rename (Fin.natAdd n) s) := by
          rw [rel_data laws]
          exact (rs.refl_left laws.toDataLaws).rename₂ _
        have h := related (Morph.castAdd ξ (blankWorld m)) hs rs'
        change B.rel S _ _ _ at h
        rw [rel_data laws] at h
        have h' := DataEq.subst₂ B h (appendSub (renSub ρ)) (appendSub (renSub ρ))
        simp only [Presentation.subst, subst_appendSub_castAdd, subst_appendSub_natAdd,
          subst_renSub] at h'
        exact h'
      · intro related _ _ ρ _ a a' _ ha
        show B.rel S _ _ _
        rw [rel_data laws]
        have ha' : DataEq S A a a' := by
          have h : A.rel S _ a a' := ha
          rw [rel_data laws] at h
          exact h
        exact related ρ ha'

end Carrier

end Setting

/-! ## Carriers are interpreted by their meanings -/

/-- A closed non-dependent function type, lifted to a world. -/
theorem liftClosed_arrow {n : Nat} (dom cod : Tm Head 0) :
    (liftClosed (.pi dom (Presentation.rename wk cod)) : Tm Head n) =
      .pi (liftClosed dom) (Presentation.rename wk (liftClosed cod)) :=
  congrArg (Tm.pi (liftClosed dom)) (rename_liftRen_wk Fin.elim0 cod)

section Model

variable {M : Model Head L}

/-- A non-dependent function type between closed types, each interpreted the
same way at every world, is interpreted by the functions that send related
arguments to related results. -/
theorem interp_arrow {l : L} {dom cod : Tm Head 0}
    {D C : ∀ {m : Nat}, World M.reading m → Rel Head m}
    (domInterp : ∀ {m : Nat} (ξ : World M.reading m), InterpAt M l ξ (liftClosed dom) (D ξ))
    (codInterp : ∀ {m : Nat} (ξ : World M.reading m), InterpAt M l ξ (liftClosed cod) (C ξ))
    {n : Nat} (ξ : World M.reading n) :
    InterpAt M l ξ (liftClosed (.pi dom (Presentation.rename wk cod))) (PiRel.arrow ξ D C).rel := by
  rw [liftClosed_arrow]
  exact Interp.pi .refl (PiRel.arrow ξ D C)
    (fun {_ _ _} _ => by rw [rename_liftClosed]; exact domInterp _)
    (fun {_ _ _} _ {_} _ => by
      rw [rename_liftRen_wk, inst0_rename_wk, rename_liftClosed]
      exact codInterp _)
    (fun {_ _ _} _ {_ _} _ _ _ => rfl)

namespace Carrier

/-- The type of codes is interpreted by the relation of a common truth value. -/
theorem interp_prop (l : L) {n : Nat} (ξ : World M.reading n) :
    InterpAt M l ξ (liftClosed (Carrier.prop.term M)) (Carrier.prop.rel M.reading ξ) := by
  rw [rel_prop]
  exact Interp.prop .refl

/-- An interpretable carrier, read as a type, is interpreted at every level and
world by the partial equivalence of a common meaning. -/
theorem interp_rel (laws : M.Laws) (l : L) :
    ∀ {k : Kind} {A : Carrier k}, A.Interpretable M → ∀ {n : Nat} (ξ : World M.reading n),
      InterpAt M l ξ (liftClosed (A.term M)) (A.rel M.reading ξ)
  | _, _, .prop, _, ξ => interp_prop l ξ
  | _, _, .num, _, ξ => by
      rw [rel_data laws.reading]
      exact Interp.num .refl
  | _, _, .rigid role notProp notHolds, _, _ => by
      rw [rel_rigid]
      exact Interp.rigid (args := []) .refl role notProp notHolds
  | _, _, @Interpretable.arr _ _ _ _ _ k' A B dom cod, _, ξ => by
      have interpArrow := interp_arrow (l := l) (fun ξ' => interp_rel laws l dom ξ')
        (fun ξ' => interp_rel laws l cod ξ') ξ
      cases k' with
      | gen =>
          rw [← arrow_rel laws.reading]
          exact interpArrow
      | data =>
          have e : (PiRel.arrow ξ (A.rel M.reading) (B.rel M.reading)).rel =
              (Carrier.arr A B).rel M.reading ξ := by
            rw [rel_data laws.reading (.arr A B)]
            funext f g
            exact propext (arrow_data_iff laws.reading)
          rw [← e]
          exact interpArrow

/-- An interpretable carrier, read as a type, is interpreted at every level and
world, and two terms are related exactly when they have a common meaning. -/
theorem interp (laws : M.Laws) {k : Kind} {A : Carrier k} (hA : A.Interpretable M) (l : L)
    {n : Nat} (ξ : World M.reading n) :
    ∃ R, InterpAt M l ξ (liftClosed (A.term M)) R ∧
      ∀ a b, R a b ↔ ∃ v, Read M.reading ξ a A v ∧ Read M.reading ξ b A v :=
  ⟨_, interp_rel laws l hA ξ, fun _ _ => Iff.rfl⟩

/-- Every meaning at a carrier is the meaning of a term in a world reached from
the current one: a fresh generic, or a closed representative of a data value. -/
theorem realized {k : Kind} (A : Carrier k) (v : A.V M.reading) {n : Nat}
    (ξ : World M.reading n) :
    ∃ (m : Nat) (ξ' : World M.reading m) (ρ : Ren n m) (a : Tm Head m),
      Morph ξ ξ' ρ ∧ A.rel M.reading ξ' a a ∧ Read M.reading ξ' a A v := by
  cases k with
  | gen =>
      have r : Read M.reading (ξ.snoc ⟨A, v⟩) (.var 0) A v := Read.generic' _ rfl
      exact ⟨n + 1, ξ.snoc ⟨A, v⟩, wk, .var 0, Morph.wk ξ ⟨A, v⟩, ⟨v, r, r⟩, r⟩
  | data =>
      obtain ⟨s, related, rfl⟩ := dataValue_surjective v
      have r : Read M.reading ξ (liftClosed s) A (dataValue M.reading A s related) :=
        read_representative related
      exact ⟨n, ξ, idRen, liftClosed s, Morph.id ξ, ⟨_, r, r⟩, r⟩

end Carrier

/-! ## Inversions of the interpretation -/

private theorem whRed_eq_of_whnf {n : Nat} {R : Rules Head} {roles : Roles Head}
    {t u : Tm Head n} (red : WhRed R roles t u) (normal : Whnf R roles t) : u = t := by
  cases red using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head step _ => exact absurd step (normal _)

/-- `holds c` of a code with a truth value relates every pair of terms or none,
as that truth value says. -/
theorem Interp.holds_of_truth (laws : M.Laws) {l : L} {below : L → IRel M.reading}
    {n : Nat} {ξ : World M.reading n} {A c : Tm Head n} {P : Prop}
    (red : WhRed M.rules M.roles A (.app (.const M.holds) c))
    (truth : Truth M.reading ξ c P) :
    Interp M l below ξ A (fun _ _ => P) := by
  have e : (fun _ _ : Tm Head n => ∃ P', Truth M.reading ξ c P' ∧ P') = fun _ _ => P :=
    funext fun _ => funext fun _ => propext (Truth.holds_iff laws.reading truth)
  rw [← e]
  exact Interp.holds red ⟨P, truth⟩

/-- A dependent function type is interpreted only by the function clause. -/
theorem Interp.pi_inv (laws : M.Laws) {l : L} {below : L → IRel M.reading} {n : Nat}
    {ξ : World M.reading n} {dom : Tm Head n} {cod : Tm Head (n + 1)} {R : Rel Head n}
    (interp : Interp M l below ξ (.pi dom cod) R) :
    ∃ P : PiRel Head ξ, R = P.rel ∧
      (∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ),
        Interp M l below ξ' (Presentation.rename ρ dom) (P.dom w)) ∧
      ∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ) {a : Tm Head m}
        (ha : P.dom w a a),
        Interp M l below ξ' (inst0 a (Presentation.rename (liftRen ρ) cod)) (P.cod w ha) := by
  have normal := pi_whnf laws.shape dom cod
  cases interp with
  | pi red P domInterp codInterp _ =>
      cases whRed_eq_of_whnf red normal
      exact ⟨P, rfl, domInterp, codInterp⟩
  | sort _ _ red => cases whRed_eq_of_whnf red normal
  | ground _ red => cases whRed_eq_of_whnf red normal
  | sigma red => cases whRed_eq_of_whnf red normal
  | ident red => cases whRed_eq_of_whnf red normal
  | num red => cases whRed_eq_of_whnf red normal
  | prop red => cases whRed_eq_of_whnf red normal
  | holds red => cases whRed_eq_of_whnf red normal
  | rigid red => exact absurd (whRed_eq_of_whnf red normal) appSpine_const_ne_pi

/-- A head is interpreted as a universe below the level or as a ground type. -/
theorem Interp.head_inv (laws : M.Laws) {l : L} {below : L → IRel M.reading} {n : Nat}
    {ξ : World M.reading n} {h : Head} {R : Rel Head n}
    (interp : Interp M l below ξ (.head h) R) :
    (M.rules.isUniverse h ∧ M.levels.level h < l ∧ R = universeRel (below (M.levels.level h)) ξ) ∨
      (¬ M.rules.isUniverse h ∧ R = fun _ _ => True) := by
  have normal := head_whnf laws.shape (n := n) h
  cases interp with
  | sort isUniverse level red =>
      cases whRed_eq_of_whnf red normal
      exact .inl ⟨isUniverse, level, rfl⟩
  | ground notUniverse red =>
      cases whRed_eq_of_whnf red normal
      exact .inr ⟨notUniverse, rfl⟩
  | pi red => cases whRed_eq_of_whnf red normal
  | sigma red => cases whRed_eq_of_whnf red normal
  | ident red => cases whRed_eq_of_whnf red normal
  | num red => cases whRed_eq_of_whnf red normal
  | prop red => cases whRed_eq_of_whnf red normal
  | holds red => cases whRed_eq_of_whnf red normal
  | rigid red => exact absurd (whRed_eq_of_whnf red normal) appSpine_const_ne_head

/-! ## Decoding implication -/

/-- The dependent function family of `holds p → holds q`. -/
def PiRel.holdsArrow (M : Model Head L) {n : Nat} (ξ : World M.reading n) (p q : Tm Head n) :
    PiRel Head ξ where
  dom := fun {_ ξ' ρ} _ _ _ => ∃ P, Truth M.reading ξ' (Presentation.rename ρ p) P ∧ P
  cod := fun {_ ξ' ρ} _ {_} _ _ _ => ∃ Q, Truth M.reading ξ' (Presentation.rename ρ q) Q ∧ Q

/-- `holds p → holds q` is interpreted by the family of the partial equivalences
of `holds p` and `holds q` at every world. -/
theorem holds_imp_interp {l : L} {n : Nat} {ξ : World M.reading n} {p q : Tm Head n} {P Q : Prop}
    (hp : Truth M.reading ξ p P) (hq : Truth M.reading ξ q Q) :
    InterpAt M l ξ
      (.pi (.app (.const M.holds) p) (.app (.const M.holds) (Presentation.rename wk q)))
      (PiRel.holdsArrow M ξ p q).rel :=
  Interp.pi .refl _ (fun {_ _ _} w => Interp.holds .refl ⟨P, hp.rename w⟩)
    (fun {_ _ ρ} w {a} _ => by
      show Interp _ _ _ _ (.app (.const M.holds)
        (inst0 a (Presentation.rename (liftRen ρ) (Presentation.rename wk q)))) _
      rw [rename_liftRen_wk, inst0_rename_wk]
      exact Interp.holds .refl ⟨Q, hq.rename w⟩)
    (fun {_ _ _} _ {_ _} _ _ _ => rfl)

/-- `holds p → holds q` is interpreted when `p` and `q` have truth values. -/
theorem holds_imp_exists {l : L} {n : Nat} {ξ : World M.reading n} {p q : Tm Head n} {P Q : Prop}
    (hp : Truth M.reading ξ p P) (hq : Truth M.reading ξ q Q) :
    ∃ R, InterpAt M l ξ
      (.pi (.app (.const M.holds) p) (.app (.const M.holds) (Presentation.rename wk q))) R :=
  ⟨_, holds_imp_interp hp hq⟩

/-- `holds p → holds q` has the partial equivalence of `holds (imp p q)`. -/
theorem holds_imp_coherent (laws : M.Laws) {l : L} {n : Nat} {ξ : World M.reading n}
    {p q : Tm Head n} {P Q : Prop} (hp : Truth M.reading ξ p P)
    (hq : Truth M.reading ξ q Q) {R : Rel Head n}
    (interp : InterpAt M l ξ
      (.pi (.app (.const M.holds) p) (.app (.const M.holds) (Presentation.rename wk q))) R) :
    R = fun _ _ => ∃ P', Truth M.reading ξ (.app (.app (.const M.imp) p) q) P' ∧ P' := by
  rw [Interp.deterministic laws interp (holds_imp_interp hp hq)]
  have imp : Truth M.reading ξ (.app (.app (.const M.imp) p) q) (P → Q) := .imp .refl hp hq
  funext f g
  rw [Truth.holds_iff laws.reading imp]
  apply propext
  constructor
  · intro related hP
    have hp' : Truth M.reading ξ (Presentation.rename idRen p) P := by
      rw [rename_id]
      exact hp
    obtain ⟨Q', hq', hQ'⟩ := related (Morph.id ξ) (a := f) (b := g) ⟨P, hp', hP⟩ ⟨P, hp', hP⟩
    rw [rename_id] at hq'
    exact (Truth.deterministic laws.reading hq' hq).mp hQ'
  · intro hPQ _ _ _ w _ _ ha _
    obtain ⟨P', hp', hP'⟩ := ha
    exact ⟨Q, hq.rename w, hPQ ((Truth.deterministic laws.reading hp' (hp.rename w)).mp hP')⟩

/-! ## Decoding the quantifiers -/

/-- The dependent function family of `(x : A) → holds (f x)`. -/
def PiRel.holdsAll (M : Model Head L) {k : Kind} (A : Carrier k) {n : Nat}
    (ξ : World M.reading n) (f : Tm Head n) : PiRel Head ξ where
  dom := fun {_ ξ' _} _ => A.rel M.reading ξ'
  cod := fun {_ ξ' ρ} _ {a} _ _ _ =>
    ∃ P, Truth M.reading ξ' (.app (Presentation.rename ρ f) a) P ∧ P

/-- `(x : A) → holds (f x)` is interpreted by the family whose domain is the
partial equivalence of `A` and whose codomain at `a` is that of `holds (f a)`. -/
theorem holds_all_interp (laws : M.Laws) {l : L} {k : Kind} {A : Carrier k}
    (hA : A.Interpretable M) {n : Nat} {ξ : World M.reading n} {f : Tm Head n}
    {φ : A.V M.reading → Prop} (read : Read M.reading ξ f (.arr A .prop) φ) :
    InterpAt M l ξ (.pi (liftClosed (A.term M))
      (.app (.const M.holds) (.app (Presentation.rename wk f) (.var 0))))
      (PiRel.holdsAll M A ξ f).rel :=
  Interp.pi .refl _
    (fun {_ _ _} _ => by rw [rename_liftClosed]; exact Carrier.interp_rel laws l hA _)
    (fun {_ _ ρ} w {a} ha => by
      show Interp _ _ _ _ (.app (.const M.holds)
        (.app (inst0 a (Presentation.rename (liftRen ρ) (Presentation.rename wk f))) a)) _
      rw [rename_liftRen_wk, inst0_rename_wk]
      refine Interp.holds .refl ?_
      obtain ⟨v, ra, _⟩ := ha
      exact ⟨φ v, (Read.app (read.rename w) ra).prop_inv⟩)
    (fun {_ _ _} w {_ _} _ _ hab => by
      obtain ⟨v, ra, rb⟩ := hab
      funext _ _
      exact propext ((Truth.holds_iff laws.reading (Read.app (read.rename w) ra).prop_inv).trans
        (Truth.holds_iff laws.reading (Read.app (read.rename w) rb).prop_inv).symm))

/-- `(x : A) → holds (f x)` is interpreted when `f` is a predicate on `A`. -/
theorem holds_all_exists (laws : M.Laws) {l : L} {k : Kind} {A : Carrier k}
    (hA : A.Interpretable M) {n : Nat} {ξ : World M.reading n} {f : Tm Head n}
    {φ : A.V M.reading → Prop} (read : Read M.reading ξ f (.arr A .prop) φ) :
    ∃ R, InterpAt M l ξ (.pi (liftClosed (A.term M))
      (.app (.const M.holds) (.app (Presentation.rename wk f) (.var 0)))) R :=
  ⟨_, holds_all_interp laws hA read⟩

/-- `(x : A) → holds (f x)` has the partial equivalence of `holds (all@A f)`.
Every meaning at `A` is the meaning of a term in a world reached from the
current one: a fresh generic, or a closed representative of a data value. -/
theorem holds_all_coherent (laws : M.Laws) {l : L} {a : DeclName} {k : Kind}
    {A : Carrier k} (carrier : M.allCarrier a = some ⟨k, A⟩) (hA : A.Interpretable M)
    {n : Nat} {ξ : World M.reading n} {f : Tm Head n} {φ : A.V M.reading → Prop}
    (read : Read M.reading ξ f (.arr A .prop) φ) {R : Rel Head n}
    (interp : InterpAt M l ξ (.pi (liftClosed (A.term M))
      (.app (.const M.holds) (.app (Presentation.rename wk f) (.var 0)))) R) :
    R = fun _ _ => ∃ P', Truth M.reading ξ (.app (.const a) f) P' ∧ P' := by
  rw [Interp.deterministic laws interp (holds_all_interp laws hA read)]
  have all : Truth M.reading ξ (.app (.const a) f) (∀ v, φ v) := .all carrier .refl read
  funext _ _
  rw [Truth.holds_iff laws.reading all]
  apply propext
  constructor
  · intro related v
    obtain ⟨_, ξ', ρ, x, w, hx, rx⟩ := Carrier.realized A v ξ
    obtain ⟨P, tP, hP⟩ := related w hx hx
    exact (Truth.deterministic laws.reading tP (Read.app (read.rename w) rx).prop_inv).mp hP
  · intro hall _ _ _ w _ _ hx _
    obtain ⟨v, rx, _⟩ := hx
    exact ⟨φ v, (Read.app (read.rename w) rx).prop_inv, hall v⟩

/-! ## Decoding the equations -/

/-- The identity type of two terms with meanings relates every pair of terms
when the meanings agree, and none otherwise. -/
theorem holds_eq_interp (laws : M.Laws) {l : L} {k : Kind} {A : Carrier k}
    (hA : A.Interpretable M) {n : Nat} {ξ : World M.reading n} {x y : Tm Head n}
    {v w : A.V M.reading} (readX : Read M.reading ξ x A v)
    (readY : Read M.reading ξ y A w) :
    InterpAt M l ξ (.id (liftClosed (A.term M)) x y)
      (fun _ _ => A.rel M.reading ξ x y) :=
  Interp.ident .refl _ (Carrier.interp_rel laws l hA ξ) ⟨v, readX, readX⟩ ⟨w, readY, readY⟩

/-- The identity type of two terms with meanings is interpreted. -/
theorem holds_eq_exists (laws : M.Laws) {l : L} {k : Kind} {A : Carrier k}
    (hA : A.Interpretable M) {n : Nat} {ξ : World M.reading n} {x y : Tm Head n}
    {v w : A.V M.reading} (readX : Read M.reading ξ x A v)
    (readY : Read M.reading ξ y A w) :
    ∃ R, InterpAt M l ξ (.id (liftClosed (A.term M)) x y) R :=
  ⟨_, holds_eq_interp laws hA readX readY⟩

/-- The identity type of `x` and `y` at `A` has the partial equivalence of
`holds (eq@A x y)`. -/
theorem holds_eq_coherent (laws : M.Laws) {l : L} {e : DeclName} {k : Kind} {A : Carrier k}
    (carrier : M.eqCarrier e = some ⟨k, A⟩) (hA : A.Interpretable M) {n : Nat}
    {ξ : World M.reading n} {x y : Tm Head n} {v w : A.V M.reading}
    (readX : Read M.reading ξ x A v) (readY : Read M.reading ξ y A w) {R : Rel Head n}
    (interp : InterpAt M l ξ (.id (liftClosed (A.term M)) x y) R) :
    R = fun _ _ => ∃ P', Truth M.reading ξ (.app (.app (.const e) x) y) P' ∧ P' := by
  rw [Interp.deterministic laws interp (holds_eq_interp laws hA readX readY)]
  have eq : Truth M.reading ξ (.app (.app (.const e) x) y) (v = w) :=
    .eq carrier .refl readX readY
  funext _ _
  rw [Truth.holds_iff laws.reading eq]
  apply propext
  constructor
  · rintro ⟨u, rx, ry⟩
    exact (Read.deterministic laws.reading readX rx).trans (Read.deterministic laws.reading ry readY)
  · rintro rfl
    exact ⟨v, readX, readY⟩

/-! ## The code constants at their declared types -/

/-- Implication is related to itself at `prop → prop → prop`. -/
theorem imp_sem (laws : M.Laws) {l : L} {n : Nat} {ξ : World M.reading n} {R : Rel Head n}
    (interp : InterpAt M l ξ
      (liftClosed (.pi (.const M.prop) (.pi (.const M.prop) (.const M.prop)))) R) :
    R (.const M.imp) (.const M.imp) := by
  rw [Interp.deterministic laws interp (interp_arrow (Carrier.interp_prop l)
    (fun ξ' => interp_arrow (Carrier.interp_prop l) (Carrier.interp_prop l) ξ') ξ)]
  intro _ _ _ _ _ _ _ hxy _ _ _ w' _ _ _ hzz'
  obtain ⟨P, rx, ry⟩ := hxy
  obtain ⟨Q, rz, rz'⟩ := hzz'
  exact ⟨P → Q, .prop (.imp .refl (rx.prop_inv.rename w') rz.prop_inv),
    .prop (.imp .refl (ry.prop_inv.rename w') rz'.prop_inv)⟩

/-- A quantifier is related to itself at `(A → prop) → prop`. -/
theorem all_sem (laws : M.Laws) {a : DeclName} {k : Kind} {A : Carrier k}
    (carrier : M.allCarrier a = some ⟨k, A⟩) (hA : A.Interpretable M) {l : L} {n : Nat}
    {ξ : World M.reading n} {R : Rel Head n}
    (interp : InterpAt M l ξ
      (liftClosed (.pi (.pi (A.term M) (.const M.prop)) (.const M.prop))) R) :
    R (.const a) (.const a) := by
  rw [Interp.deterministic laws interp (interp_arrow
    (fun ξ' => interp_arrow (Carrier.interp_rel laws l hA) (Carrier.interp_prop l) ξ')
    (Carrier.interp_prop l) ξ)]
  intro _ _ _ _ _ _ _ hfg
  obtain ⟨φ, rf, rg⟩ := (Carrier.arrow_iff laws.reading (B := .prop)).mp hfg
  exact ⟨∀ v, φ v, .prop (.all carrier .refl rf), .prop (.all carrier .refl rg)⟩

/-- An equation code is related to itself at `A → A → prop`. -/
theorem eq_sem (laws : M.Laws) {e : DeclName} {k : Kind} {A : Carrier k}
    (carrier : M.eqCarrier e = some ⟨k, A⟩) (hA : A.Interpretable M) {l : L} {n : Nat}
    {ξ : World M.reading n} {R : Rel Head n}
    (interp : InterpAt M l ξ
      (liftClosed (.pi (A.term M) (.pi (Presentation.rename wk (A.term M)) (.const M.prop)))) R) :
    R (.const e) (.const e) := by
  rw [Interp.deterministic laws interp (interp_arrow (Carrier.interp_rel laws l hA)
    (fun ξ' => interp_arrow (Carrier.interp_rel laws l hA) (Carrier.interp_prop l) ξ') ξ)]
  intro _ _ _ _ _ _ _ hxy _ _ _ w' _ _ _ hzz'
  obtain ⟨v, rx, ry⟩ := hxy
  obtain ⟨u, rz, rz'⟩ := hzz'
  exact ⟨v = u, .prop (.eq carrier .refl (rx.rename w') rz),
    .prop (.eq carrier .refl (ry.rename w') rz')⟩

/-- The decoder is related to itself at `prop → U0`, at every level at which
that type is interpreted. -/
theorem holds_sem (laws : M.Laws) {u : Head} {l : L} {n : Nat} {ξ : World M.reading n}
    {R : Rel Head n} (interp : InterpAt M l ξ (liftClosed (.pi (.const M.prop) (.head u))) R) :
    R (.const M.holds) (.const M.holds) := by
  obtain ⟨P, rfl, domInterp, codInterp⟩ := Interp.pi_inv laws interp
  intro _ ξ' _ w _ _ hx hxy
  have hdom : P.dom w = fun c c' =>
      ∃ Q, Truth M.reading ξ' c Q ∧ Truth M.reading ξ' c' Q := by
    rw [← Carrier.rel_prop]
    exact Interp.deterministic laws (domInterp w) (Carrier.interp_prop l ξ')
  rw [hdom] at hxy
  obtain ⟨Q, tx, ty⟩ := hxy
  rcases Interp.head_inv laws (codInterp w hx) with ⟨_, level, e⟩ | ⟨_, e⟩
  · rw [e]
    intro _ _ _ w'
    exact ⟨fun _ _ => Q,
      (levelsBelow_iff M level _ _ _).mpr (Interp.holds_of_truth laws .refl (tx.rename w')),
      (levelsBelow_iff M level _ _ _).mpr (Interp.holds_of_truth laws .refl (ty.rename w'))⟩
  · rw [e]
    trivial

end Model

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
