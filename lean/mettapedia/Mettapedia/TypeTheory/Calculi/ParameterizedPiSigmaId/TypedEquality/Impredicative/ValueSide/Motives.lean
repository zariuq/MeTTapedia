import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Families
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Eliminator
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.IotaComputation

/-!
# Motives of identity elimination on the value side

Over every realizer algebra:

* **Motives.** A motive related to another, applied to related points and to any
  two paths, gives types related in the motive's universe, since an identity
  type relates every two paths (`idMotive_universe`); so the two applications
  are a pair of one shape with one pack at the motive's level
  (`idMotive_shapePair`).
* **Transports.** Between two types of one shape with one pack, the transport
  of a valid method has the realizers of the method, at the pack of any
  denotation of the target (`coe_realAt`).

And for the recursor of a simple inductive type, the same over every realizer algebra:

* **Shapes.** A value related at an inductive type has a shape (`IndRel.hasShape`), and at most
  one (`HasIndShape.unique`); its realizers are those of its shape
  (`indPack_real_of_shape`).
* **Motives of a recursor.** A motive related to another at `T → v`, at related values, has one
  denotation (`motive_den`), and a method applied to related fields and induction hypotheses
  gives related results, one binder at a time (`method_app`).
* **The values of the recursor** (`rec_related`): at related motives and methods, the recursor at
  related values gives values related at the motive, by induction on the inductive pack. At a
  constructor both sides compute to the method applied to the fields and to the recursive calls;
  at terms stuck on the daimon both are stuck. What this asks of the value side is that the type
  is inductive with the constructors and the recursor computes by their rules
  (`InductiveValues`). Model SN and the conversion model read their recursors' values by this one
  induction.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ValueSide

open Normalization (motiveType inst0_motiveCod)
open UniverseLevel (LevelOrder)
open Consistency (World)

variable {Head L : Type} [LevelOrder L] {V : Model Head L}

section Motives

variable (laws : V.Laws)
include laws

/-- **A motive of identity elimination related to another, applied to related
points and to any two paths, gives types related in the motive's universe**:
an identity type relates every two paths. -/
theorem idMotive_universe {n : Nat} {ξ : World V.reading n} {A x a b f g p q : Tm Head n}
    {w : Head} (hw : V.rules.isUniverse w) {RF : Pack V n}
    (denF : DenS V ξ (motiveType A x w) RF) (hfg : RF.rel f g)
    (hab : ∀ {RA : Pack V n}, DenS V ξ A RA → RA.rel a b) :
    (universeAt V (V.levels.level w) ξ).rel (.app (.app f a) p) (.app (.app g b) q) := by
  obtain ⟨R₁, den₁, h₁⟩ := DenS.pi_app_exists laws denF hfg hab
  rw [inst0_motiveCod] at den₁
  obtain ⟨R₂, den₂, h₂⟩ := DenS.pi_app_exists laws den₁ h₁
    fun denI => DenS.id_rel laws denI p q
  have den₂' : DenS V ξ (.head w) R₂ := den₂
  obtain rfl := DenS.sort_inv laws hw den₂'
  exact @h₂

/-- A motive related to another, applied to related points and to any two
paths, gives a pair of types of one shape with one pack at the level of the
motive's universe. -/
theorem idMotive_shapePair {n : Nat} {ξ : World V.reading n} {A x a b f g p q : Tm Head n}
    {w : Head} (hw : V.rules.isUniverse w) {RF : Pack V n}
    (denF : DenS V ξ (motiveType A x w) RF) (hfg : RF.rel f g)
    (hab : ∀ {RA : Pack V n}, DenS V ξ A RA → RA.rel a b) :
    ∃ Q, ShapePair V (InterpAt V (V.levels.level w)) ξ (.app (.app f a) p)
      (.app (.app g b) q) Q Q := by
  obtain ⟨Q, hl, hr, s⟩ := universeAt.den (idMotive_universe laws hw denF hfg hab)
  exact ⟨Q, hl, hr, rfl, s⟩

/-- **Between two types of one shape with one pack, the transport has the
realizers of its method**, at the pack of any denotation of the target. -/
theorem coe_realAt {coe : DeclName} (transport : CoeRules V coe) {k : L} {n : Nat}
    {ξ : World V.reading n} {X Y d : Tm Head n} {Q : Pack V n}
    (same : ShapePair V (InterpAt V k) ξ X Y Q Q) (hd : Q.Val d) {P : Pack V n}
    (den : DenS V ξ Y P) : P.real (coeApp coe X Y d) = Q.real d := by
  obtain rfl := DenS.deterministic laws den ⟨k, same.right⟩
  exact coe_real laws (InterpAt.facts laws k) transport same hd

end Motives

section Inductive

open Normalization hiding World Pack
open Realizability (Daimonic)

/-! ## Shapes of values of an inductive type -/

/-- A value related at an inductive type has a shape. -/
theorem IndRel.hasShape {n : Nat} {cs : List (DeclName × List (Field Head))}
    {field : Tm Head 0 → Pack V n} {t t' : Tm Head n}
    (related : IndRel V cs field t t') : ∃ s, HasIndShape V cs t s := by
  refine IndRel.rec (motive_1 := fun t _ _ => ∃ s, HasIndShape V cs t s)
    (motive_2 := fun fs as _ _ => ∃ fields, HasIndShapes V cs fs as fields)
    ?_ ?_ ?_ ?_ ?_ related
  · intro k fs t t' as as' mem red _ _ ih
    obtain ⟨fields, h⟩ := ih
    exact ⟨_, .ctor mem red h⟩
  · intro t t' u u' red daimonic _ _
    exact ⟨_, .star red daimonic⟩
  · exact ⟨_, .nil⟩
  · intro fs t t' as as' _ _ ih ihRest
    obtain ⟨s, h⟩ := ih
    obtain ⟨fields, hs⟩ := ihRest
    exact ⟨_, .recursive h hs⟩
  · intro F fs t t' as as' _ _ ihRest
    obtain ⟨fields, hs⟩ := ihRest
    exact ⟨_, .closed hs⟩

/-- Fields related at an inductive type number its fields, on both sides. -/
theorem IndFields.length {n : Nat} {cs : List (DeclName × List (Field Head))}
    {field : Tm Head 0 → Pack V n} :
    ∀ {fs : List (Field Head)} {as as' : List (Tm Head n)},
      IndFields V cs field fs as as' → as.length = fs.length ∧ as'.length = fs.length
  | _, _, _, .nil => ⟨rfl, rfl⟩
  | _, _, _, .recursive _ rest => by
      obtain ⟨h, h'⟩ := IndFields.length rest
      exact ⟨by simp [h], by simp [h']⟩
  | _, _, _, .closed _ rest => by
      obtain ⟨h, h'⟩ := IndFields.length rest
      exact ⟨by simp [h], by simp [h']⟩

/-- The shapes of the fields number its fields. -/
theorem HasIndShapes.reals_length {n : Nat} {cs : List (DeclName × List (Field Head))}
    (T : DeclName) (field : Tm Head 0 → Pack V n) :
    ∀ {fs : List (Field Head)} {as : List (Tm Head n)} {fields : IndShapes Head n},
      HasIndShapes V cs fs as fields →
        (IndShapes.reals V T field fields).length = fs.length
  | _, _, _, .nil => rfl
  | _, _, _, .recursive _ rest => by
      simp [IndShapes.reals, HasIndShapes.reals_length T field rest]
  | _, _, _, .closed rest => by
      simp [IndShapes.reals, HasIndShapes.reals_length T field rest]

section Shapes

variable (laws : V.Laws) {T : DeclName} {cs : List (DeclName × List (Field Head))}
  (role : V.roles T = .inductive cs)
include laws role

/-- **A value has at most one shape**: it reduces to at most one constructor spine, and to no
term stuck on the daimon when it reduces to one. -/
theorem HasIndShape.unique {n : Nat} {t : Tm Head n} {s s' : IndShape Head n}
    (h : HasIndShape V cs t s) (h' : HasIndShape V cs t s') : s = s' := by
  have key : ∀ {t : Tm Head n} {s : IndShape Head n}, HasIndShape V cs t s →
      ∀ {s' : IndShape Head n}, HasIndShape V cs t s' → s = s' := by
    intro t s h
    refine HasIndShape.rec
      (motive_1 := fun t s _ => ∀ {s' : IndShape Head n}, HasIndShape V cs t s' → s = s')
      (motive_2 := fun fs as fields _ => ∀ {fields' : IndShapes Head n},
        HasIndShapes V cs fs as fields' → fields = fields')
      ?_ ?_ ?_ ?_ ?_ h
    · intro k fs t as fields mem red _ ih s' h'
      cases h' with
      | ctor mem' red' shapes' =>
          obtain ⟨rfl, rfl, rfl⟩ := laws.ctorSpine_unique role mem mem' red red'
          rw [ih shapes']
      | star red' daimonic' =>
          exact (laws.ctorSpine_not_daimonic role mem red red' daimonic').elim
    · intro t u red daimonic s' h'
      cases h' with
      | ctor mem' red' _ =>
          exact (laws.ctorSpine_not_daimonic role mem' red' red daimonic).elim
      | star _ _ => rfl
    · intro fields' h'
      cases h'
      rfl
    · intro fs a as shape rest _ _ ih ihRest fields' h'
      cases h' with
      | recursive shape' rest' => rw [ih shape', ihRest rest']
    · intro F fs a as rest _ ihRest fields' h'
      cases h' with
      | closed rest' => rw [ihRest rest']
  exact key h h'

/-- **A value of a shape is realized by the realizers of its shape.** -/
theorem indPack_real_of_shape {n : Nat} {field : Tm Head 0 → Pack V n} {a : Tm Head n}
    {s : IndShape Head n} (shape : HasIndShape V cs a s) :
    (indPack V T cs field).real a = s.real V T field :=
  laws.alg.meet_const _ _
    (fun s' => congrArg (fun s : IndShape Head n => s.real V T field)
      (HasIndShape.unique laws role s'.2 shape))
    ⟨⟨s, shape⟩⟩

end Shapes

/-! ## The values of a recursor -/

/-- **A recursor computing on the value side**: `T` is an inductive type with the constructors
`cs`, and the recursor `rec` computes on its last argument by their rules. -/
structure InductiveValues (V : Model Head L) (T rec : DeclName)
    (cs : List (DeclName × List (Field Head))) : Prop where
  role : V.roles T = .inductive cs
  recRole : V.roles rec =
    .computes (cs.length + 2) (.split (cs.length + 1) .constructor fun _ => .leaf)
  iota : ∀ {n : Nat} {l r : Tm Head n}, IotaStep rec cs l r → V.rules.computation.step l r

/-- Arguments for the fields of a constructor, related at the denotations of the fields'
types. -/
inductive FieldsV {n : Nat} (ξ : World V.reading n) (T : DeclName) :
    List (Field Head) → List (Tm Head n) → List (Tm Head n) → Prop where
  | nil : FieldsV ξ T [] [] []
  | cons {f : Field Head} {a a' : Tm Head n} {fs : List (Field Head)}
      {as as' : List (Tm Head n)} :
      (∀ {PA : Pack V n}, DenS V ξ (liftClosed (f.type T)) PA → PA.rel a a') →
      FieldsV ξ T fs as as' → FieldsV ξ T (f :: fs) (a :: as) (a' :: as')

/-- Induction hypotheses over the motive `p`, related at the motive at their fields. -/
inductive HypsV {n : Nat} (ξ : World V.reading n) (p : Tm Head n) :
    List (Tm Head n) → List (Tm Head n) → List (Tm Head n) → Prop where
  | nil : HypsV ξ p [] [] []
  | cons {x ih ih' : Tm Head n} {xs ihs ihs' : List (Tm Head n)} :
      (∀ {R : Pack V n}, DenS V ξ (.app p x) R → R.rel ih ih') →
      HypsV ξ p xs ihs ihs' → HypsV ξ p (x :: xs) (ih :: ihs) (ih' :: ihs')

/-- Methods over the motive `p`, one for each constructor, related at their case types. -/
def MethodsV {n : Nat} (ξ : World V.reading n) (T : DeclName) (p : Tm Head n)
    (cs : List (DeclName × List (Field Head))) (ms ms' : List (Tm Head n)) : Prop :=
  ms.length = cs.length ∧ ms'.length = cs.length ∧
    ∀ {i : Nat} {k : DeclName} {fs : List (Field Head)}, cs[i]? = some (k, fs) →
      ∃ g g' PM, ms[i]? = some g ∧ ms'[i]? = some g' ∧
        DenS V ξ (caseType T k fs p) PM ∧ PM.rel g g'

section Application

variable (laws : V.Laws)
include laws

/-- A function of the induction hypotheses, applied to related hypotheses. -/
theorem caseHyps_app {n : Nat} {ξ : World V.reading n} {p target : Tm Head n} :
    ∀ {xs ihs ihs' : List (Tm Head n)}, HypsV ξ p xs ihs ihs' →
      ∀ {g g' : Tm Head n} {PM : Pack V n}, DenS V ξ (caseHyps p xs target) PM → PM.rel g g' →
        ∃ R, DenS V ξ (.app p target) R ∧ R.rel (appSpine g ihs) (appSpine g' ihs')
  | _, _, _, .nil, g, g', PM, den, h => by
      rw [caseHyps_nil] at den
      exact ⟨PM, den, h⟩
  | _, _, _, .cons (x := x) hx tail, g, g', PM, den, h => by
      rw [caseHyps_cons] at den
      obtain ⟨PB, denB, hB⟩ := DenS.pi_app_exists laws den h hx
      rw [inst0_caseHyps] at denB
      exact caseHyps_app tail denB hB

/-- A method applied to related fields, through the fields of its case type. -/
theorem caseFields_app {n : Nat} {ξ : World V.reading n} {T k : DeclName} :
    ∀ {fs : List (Field Head)} {as as' : List (Tm Head n)}, FieldsV ξ T fs as as' →
      ∀ {p : Tm Head n} {xs recs : List (Tm Head n)} {g g' : Tm Head n} {PM : Pack V n},
        DenS V ξ (caseFields T k fs p xs recs) PM → PM.rel g g' →
        ∃ PH, DenS V ξ (caseHyps p (recs ++ recArgs fs as) (appSpine (.const k) (xs ++ as))) PH ∧
          PH.rel (appSpine g as) (appSpine g' as')
  | _, _, _, .nil, p, xs, recs, g, g', PM, den, h => by
      simp only [caseFields, recArgs, List.append_nil] at den ⊢
      exact ⟨PM, den, h⟩
  | .recursive :: fs, a :: as, _, .cons ha tail, p, xs, recs, g, g', PM, den, h => by
      simp only [caseFields] at den
      obtain ⟨PB, denB, hB⟩ := DenS.pi_app_exists laws den h ha
      rw [inst0_caseFields T k fs a p xs recs [.var 0] [a] rfl] at denB
      obtain ⟨PH, denH, hH⟩ := caseFields_app tail denB hB
      simp only [List.append_assoc, List.singleton_append] at denH
      exact ⟨PH, denH, hH⟩
  | .closed F :: fs, a :: as, _, .cons ha tail, p, xs, recs, g, g', PM, den, h => by
      simp only [caseFields] at den
      obtain ⟨PB, denB, hB⟩ := DenS.pi_app_exists laws den h ha
      have inst := inst0_caseFields T k fs a p xs recs [] [] rfl
      rw [List.append_nil, List.append_nil] at inst
      rw [inst] at denB
      obtain ⟨PH, denH, hH⟩ := caseFields_app tail denB hB
      simp only [List.append_assoc, List.singleton_append] at denH
      exact ⟨PH, denH, hH⟩

/-- **A method applied to related fields and hypotheses** gives related results, at the motive at
the constructor applied to the fields. -/
theorem method_app {n : Nat} {ξ : World V.reading n} {T k : DeclName} {fs : List (Field Head)}
    {as as' : List (Tm Head n)} (fields : FieldsV ξ T fs as as') {p : Tm Head n}
    {ihs ihs' : List (Tm Head n)} (hyps : HypsV ξ p (recArgs fs as) ihs ihs') {g g' : Tm Head n}
    {PM : Pack V n} (den : DenS V ξ (caseType T k fs p) PM) (hg : PM.rel g g') :
    ∃ R, DenS V ξ (.app p (appSpine (.const k) as)) R ∧
      R.rel (appSpine g (as ++ ihs)) (appSpine g' (as' ++ ihs')) := by
  obtain ⟨PH, denH, hH⟩ := caseFields_app laws fields den hg
  simp only [List.nil_append] at denH
  obtain ⟨R, denR, hR⟩ := caseHyps_app laws hyps denH hH
  refine ⟨R, denR, ?_⟩
  rw [appSpine_append, appSpine_append]
  exact hR

end Application

section Recursor

variable {T rec : DeclName} {cs : List (DeclName × List (Field Head))}
  (decl : InductiveValues V T rec cs)
include decl

/-- Reducing the scrutinee of a full application of the recursor to a constructor spine, and
computing. -/
theorem rec_red_ctor {n : Nat} {p : Tm Head n} {ms : List (Tm Head n)}
    (length : ms.length = cs.length) {t : Tm Head n} {i : Nat} {k : DeclName}
    {fs : List (Field Head)} {as : List (Tm Head n)} {g : Tm Head n}
    (hi : cs[i]? = some (k, fs)) (hg : ms[i]? = some g) (has : as.length = fs.length)
    (red : WhRed V.rules V.roles t (appSpine (.const k) as)) :
    WhRed V.rules V.roles (recApp rec (p :: ms) t)
      (appSpine g (as ++ (recArgs fs as).map (recApp rec (p :: ms)))) := by
  have role : V.roles rec = .computes (cs.length + 2)
      (.split (p :: ms).length .constructor fun _ => .leaf) := by
    rw [List.length_cons, length]
    exact decl.recRole
  have scrutinee := WhRed.scrutinee (before := p :: ms) (after := []) role
    (by simp [length]) red
  exact scrutinee.tail (.root (decl.iota ⟨p, ms, i, k, fs, as, g, length, hi, has, hg, rfl, rfl⟩))

/-- Reducing the scrutinee of a full application of the recursor. -/
theorem rec_red_scrutinee {n : Nat} {p : Tm Head n} {ms : List (Tm Head n)}
    (length : ms.length = cs.length) {t u : Tm Head n} (red : WhRed V.rules V.roles t u) :
    WhRed V.rules V.roles (recApp rec (p :: ms) t) (recApp rec (p :: ms) u) := by
  have role : V.roles rec = .computes (cs.length + 2)
      (.split (p :: ms).length .constructor fun _ => .leaf) := by
    rw [List.length_cons, length]
    exact decl.recRole
  exact WhRed.scrutinee (before := p :: ms) (after := []) role (by simp [length]) red

/-- A full application of the recursor at a term stuck on the daimon is stuck on it. -/
theorem rec_daimonic {n : Nat} {p : Tm Head n} {ms : List (Tm Head n)}
    (length : ms.length = cs.length) {u : Tm Head n} (daimonic : Daimonic V.roles V.star u) :
    Daimonic V.roles V.star (recApp rec (p :: ms) u) := by
  have role : V.roles rec = .computes (cs.length + 2)
      (.split (p :: ms).length .constructor fun _ => .leaf) := by
    rw [List.length_cons, length]
    exact decl.recRole
  exact Daimonic.stuck (before := p :: ms) (after := []) role (by simp [length]) daimonic

variable (laws : V.Laws)
include laws

/-- A value reaching a constructor spine, related to itself, has fields related to
themselves. -/
theorem IndRel.val_fields {n : Nat} {field : Tm Head 0 → Pack V n} {t : Tm Head n}
    (val : IndRel V cs field t t) {k : DeclName} {fs : List (Field Head)}
    (mem : (k, fs) ∈ cs) {as : List (Tm Head n)}
    (red : WhRed V.rules V.roles t (appSpine (.const k) as)) :
    IndFields V cs field fs as as := by
  cases val with
  | ctor mem₁ red₁ red₁' fields₁ =>
      obtain ⟨rfl, rfl, rfl⟩ := laws.ctorSpine_unique decl.role mem mem₁ red red₁
      obtain ⟨-, -, rfl⟩ := laws.ctorSpine_unique decl.role mem mem₁ red red₁'
      exact fields₁
  | star red₁ daimonic _ _ =>
      exact (laws.ctorSpine_not_daimonic decl.role mem red red₁ daimonic).elim

variable {n : Nat} {ξ : World V.reading n} {field : Tm Head 0 → Pack V n}
  (hT : DenS V ξ (.const T) (indPack V T cs field))
  (hF : ∀ {F : Tm Head 0}, F ∈ closedFields cs → DenS V ξ (liftClosed F) (field F))
  {v : Head} (hv : V.rules.isUniverse v) {RP : Pack V n}
  (denP : DenS V ξ (.pi (.const T) (.head v)) RP)
include hT hF hv denP

omit decl hF in
/-- A motive related to another at `T → v`, at related values, has one denotation. -/
theorem motive_den {P P' : Tm Head n} (relP : RP.rel P P') {a b : Tm Head n}
    (hab : IndRel V cs field a b) :
    ∃ R, DenS V ξ (.app P a) R ∧ DenS V ξ (.app P' b) R := by
  obtain ⟨RU, denU, types⟩ := DenS.pi_app_exists laws denP relP fun d => by
    rw [DenS.deterministic laws d hT]
    exact hab
  have denU' : DenS V ξ (.head v) RU := denU
  rw [DenS.sort_inv laws hv denU'] at types
  obtain ⟨R, first, second, -⟩ := universeAt.den types
  exact ⟨R, ⟨_, first⟩, ⟨_, second⟩⟩

/-- **The values of the recursor**: at a motive related to another at `T → v` and related
methods, the recursor at related values gives values related at the motive at the first value.
By induction on the inductive pack: at a constructor both sides compute to the method applied to
the fields and to the recursive calls, related by induction; at terms stuck on the daimon both
sides are stuck. -/
theorem rec_related {P P' : Tm Head n} (relP : RP.rel P P') {ms ms' : List (Tm Head n)}
    (methods : MethodsV ξ T P cs ms ms') {t t' : Tm Head n}
    (related : IndRel V cs field t t') :
    ∀ {R : Pack V n}, DenS V ξ (.app P t) R →
      R.rel (recApp rec (P :: ms) t) (recApp rec (P' :: ms') t') := by
  have relP₀ : RP.rel P P := DenS.refl_left laws denP relP
  have perT := DenS.per laws hT
  intro R den
  refine IndRel.rec
    (motive_1 := fun t t' _ => ∀ (R : Pack V n), DenS V ξ (.app P t) R →
      R.rel (recApp rec (P :: ms) t) (recApp rec (P' :: ms') t'))
    (motive_2 := fun fs as as' _ =>
      (∀ {F : Tm Head 0}, Field.closed F ∈ fs → F ∈ closedFields cs) →
        FieldsV ξ T fs as as' ∧
        HypsV ξ P (recArgs fs as) ((recArgs fs as).map (recApp rec (P :: ms)))
          ((recArgs fs as').map (recApp rec (P' :: ms'))))
    ?_ ?_ ?_ ?_ ?_ related R den
  · intro k fs t t' as as' mem red red' fields ih R den
    obtain ⟨fieldsV, hyps⟩ := ih fun hF' => mem_closedFields mem hF'
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp mem
    obtain ⟨g, g', PM, hg, hg', denM, relM⟩ := methods.2.2 hi
    obtain ⟨R', denR', relR'⟩ := method_app laws fieldsV hyps denM relM
    have toCtor : IndRel V cs field t (appSpine (.const k) as) :=
      perT.trans (.ctor mem red red' fields) (perT.symm (.ctor mem .refl red' fields))
    obtain ⟨R₀, den₀, denCtor⟩ := motive_den laws hT hv denP relP₀ toCtor
    rw [DenS.deterministic laws den den₀, DenS.deterministic laws denCtor denR']
    have expansive := DenS.expansive laws denR'
    obtain ⟨lenA, lenA'⟩ := IndFields.length fields
    exact expansive.left (rec_red_ctor decl methods.1 hi hg lenA red)
      (expansive.right (rec_red_ctor decl methods.2.1 hi hg' lenA' red') relR')
  · intro t t' u u' red daimonic red' daimonic' R den
    have expansive := DenS.expansive laws den
    exact expansive.left (rec_red_scrutinee decl methods.1 red)
      (expansive.right (rec_red_scrutinee decl methods.2.1 red')
        (DenS.daimonic_related laws den (rec_daimonic decl methods.1 daimonic)
          (rec_daimonic decl methods.2.1 daimonic')))
  · intro _
    exact ⟨.nil, .nil⟩
  · intro fs t t' as as' head _ ihHead ihRest closed
    obtain ⟨fieldsV, hyps⟩ := ihRest fun hF' => closed (List.mem_cons_of_mem _ hF')
    refine ⟨.cons (fun d => ?_) fieldsV, .cons (fun d => ihHead _ d) hyps⟩
    rw [DenS.deterministic laws d hT]
    exact head
  · intro F fs t t' as as' hF' _ ihRest closed
    obtain ⟨fieldsV, hyps⟩ := ihRest fun hF'' => closed (List.mem_cons_of_mem _ hF'')
    refine ⟨.cons (fun d => ?_) fieldsV, hyps⟩
    rw [DenS.deterministic laws d (hF (closed List.mem_cons_self))]
    exact hF'

end Recursor

end Inductive

end ValueSide
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
