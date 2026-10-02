import Mettapedia.Logic.TheoryModel.Forgetting

/-!
# Identity proofs: a theory with and without identification of proofs

A tiny signature of identity proofs: points, proofs between points, and
reflexivity, inversion and composition of proofs. Eight sentences are
considered: the five groupoid laws, `uip` (parallel proofs are equal),
`loopComm` (loops commute) and `connected` (any two points are joined).

* `groupoidLaws` is the weak theory and `uipLaws` adds the identification of
  parallel proofs. The structure `xorModel` (one point, two loops composing by
  exclusive or) satisfies the weak theory with two different proofs of the same
  identity; `eqModel α` (Lean's equality on `α`) identifies all of them. The
  model classes differ and the weaker theory has the larger class. `uip`
  entails `loopComm`, so adding `loopComm` to `uipLaws` leaves the class
  unchanged.
* Consequences are computed exactly in a ladder of universes: the universe of
  structures satisfying `uip` validates `uip` and `loopComm`; adding
  `xorModel` still validates `loopComm`; adding `dihedralModel` (loops forming
  the dihedral group of order six) hosts the weak theory faithfully.
* `univalentModel` takes types as points and equivalences as proofs. It
  satisfies the groupoid laws and refutes `uip`, `loopComm` and `connected`, so
  on its own it hosts the weak theory faithfully, while `eqModel Type`, with
  the same points and equality as proofs, validates `uip`.
* Lifting structures to a larger Lean universe preserves and reflects
  satisfaction, so a larger Lean universe validates no more sentences.
* The truncation observer sees only which points are joined. It can evaluate
  `connected` but not `uip` or `loopComm`; forgetting proofs in this sense
  admits `xorModel` as a model of the observed theory of `eqModel PUnit`, while
  the axiom `uip` excludes it.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TheoryModel.IdentityProofs

open Set

universe u v

/-! ## Signature, sentences, satisfaction -/

/-- A structure for the signature of identity proofs. -/
structure IdStructure : Type (u + 1) where
  Pt : Type u
  Pf : Pt → Pt → Type u
  refl : ∀ a, Pf a a
  inv : ∀ {a b}, Pf a b → Pf b a
  comp : ∀ {a b c}, Pf a b → Pf b c → Pf a c

/-- Sentences about identity proofs. -/
inductive IdSentence
  | assoc
  | leftUnit
  | rightUnit
  | leftInv
  | rightInv
  | uip
  | loopComm
  | connected
  deriving DecidableEq

namespace IdStructure

/-- Satisfaction of the identity-proof sentences. -/
def Sat (M : IdStructure.{u}) : IdSentence → Prop
  | .assoc => ∀ {a b c d : M.Pt} (p : M.Pf a b) (q : M.Pf b c) (r : M.Pf c d),
      M.comp (M.comp p q) r = M.comp p (M.comp q r)
  | .leftUnit => ∀ {a b : M.Pt} (p : M.Pf a b), M.comp (M.refl a) p = p
  | .rightUnit => ∀ {a b : M.Pt} (p : M.Pf a b), M.comp p (M.refl b) = p
  | .leftInv => ∀ {a b : M.Pt} (p : M.Pf a b), M.comp (M.inv p) p = M.refl b
  | .rightInv => ∀ {a b : M.Pt} (p : M.Pf a b), M.comp p (M.inv p) = M.refl a
  | .uip => ∀ {a b : M.Pt} (p q : M.Pf a b), p = q
  | .loopComm => ∀ {a : M.Pt} (p q : M.Pf a a), M.comp p q = M.comp q p
  | .connected => ∀ a b : M.Pt, Nonempty (M.Pf a b)

/-- Identification of parallel proofs makes loops commute. -/
theorem sat_loopComm_of_uip {M : IdStructure.{u}} (uip : M.Sat .uip) : M.Sat .loopComm :=
  fun p q => uip (M.comp p q) (M.comp q p)

end IdStructure

/-- The weak theory: the groupoid laws. -/
def groupoidLaws : Set IdSentence :=
  {.assoc, .leftUnit, .rightUnit, .leftInv, .rightInv}

/-- The groupoid laws with all parallel proofs identified. -/
def uipLaws : Set IdSentence :=
  insert .uip groupoidLaws

theorem mem_models_groupoidLaws {M : IdStructure.{u}} (assoc : M.Sat .assoc)
    (leftUnit : M.Sat .leftUnit) (rightUnit : M.Sat .rightUnit) (leftInv : M.Sat .leftInv)
    (rightInv : M.Sat .rightInv) : M ∈ models IdStructure.Sat groupoidLaws := by
  rintro φ (rfl | rfl | rfl | rfl | rfl)
  · exact assoc
  · exact leftUnit
  · exact rightUnit
  · exact leftInv
  · exact rightInv

theorem uip_not_mem_groupoidLaws : IdSentence.uip ∉ groupoidLaws := by
  rintro (h | h | h | h | h) <;> exact IdSentence.noConfusion h

theorem loopComm_not_mem_groupoidLaws : IdSentence.loopComm ∉ groupoidLaws := by
  rintro (h | h | h | h | h) <;> exact IdSentence.noConfusion h

theorem connected_not_mem_groupoidLaws : IdSentence.connected ∉ groupoidLaws := by
  rintro (h | h | h | h | h) <;> exact IdSentence.noConfusion h

theorem groupoidLaws_subset_uipLaws : groupoidLaws ⊆ uipLaws :=
  subset_insert _ _

/-! ## Lean's equality: all proofs identified -/

/-- Points of `α` with Lean's equality as identity proofs. -/
def eqModel (α : Type u) : IdStructure.{u} where
  Pt := α
  Pf a b := ULift.{u} (PLift (a = b))
  refl _ := ⟨⟨rfl⟩⟩
  inv p := ⟨⟨p.down.down.symm⟩⟩
  comp p q := ⟨⟨p.down.down.trans q.down.down⟩⟩

theorem eqModel_sat_uip (α : Type u) : (eqModel α).Sat .uip := by
  intro a b p q
  rcases p with ⟨⟨_⟩⟩
  rcases q with ⟨⟨_⟩⟩
  rfl

theorem eqModel_mem_uipLaws (α : Type u) : eqModel α ∈ models IdStructure.Sat uipLaws := by
  have uip : (eqModel α).Sat .uip := eqModel_sat_uip α
  rintro φ (rfl | rfl | rfl | rfl | rfl | rfl)
  · exact uip
  · exact fun _ _ _ => uip _ _
  · exact fun _ => uip _ _
  · exact fun _ => uip _ _
  · exact fun _ => uip _ _
  · exact fun _ => uip _ _

theorem eqModel_mem_groupoidLaws (α : Type u) :
    eqModel α ∈ models IdStructure.Sat groupoidLaws :=
  models_anti groupoidLaws_subset_uipLaws (eqModel_mem_uipLaws α)

/-- Negative control: equality on `Bool` does not join `true` to `false`. -/
theorem eqModel_bool_not_connected : ¬ (eqModel.{u} (ULift.{u} Bool)).Sat .connected := by
  intro connected
  obtain ⟨⟨⟨equal⟩⟩⟩ := connected ⟨true⟩ ⟨false⟩
  exact Bool.noConfusion (congrArg ULift.down equal)

/-! ## One-object groupoids from loop algebras -/

/-- The one-object structure whose loops are the elements of `L`. -/
def loopModel (L : Type) (unit : L) (inv : L → L) (mul : L → L → L) : IdStructure.{u} where
  Pt := PUnit
  Pf _ _ := ULift.{u} L
  refl _ := ⟨unit⟩
  inv p := ⟨inv p.down⟩
  comp p q := ⟨mul p.down q.down⟩

section LoopModel

variable {L : Type} {unit : L} {inv : L → L} {mul : L → L → L}

theorem loopModel_mem_groupoidLaws
    (assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)) (unit_mul : ∀ x, mul unit x = x)
    (mul_unit : ∀ x, mul x unit = x) (inv_mul : ∀ x, mul (inv x) x = unit)
    (mul_inv : ∀ x, mul x (inv x) = unit) :
    loopModel.{u} L unit inv mul ∈ models IdStructure.Sat groupoidLaws :=
  mem_models_groupoidLaws
    (fun p q r => congrArg ULift.up (assoc p.down q.down r.down))
    (fun p => congrArg ULift.up (unit_mul p.down))
    (fun p => congrArg ULift.up (mul_unit p.down))
    (fun p => congrArg ULift.up (inv_mul p.down))
    (fun p => congrArg ULift.up (mul_inv p.down))

theorem loopModel_sat_uip_iff :
    (loopModel.{u} L unit inv mul).Sat .uip ↔ ∀ x y : L, x = y :=
  ⟨fun uip x y => congrArg ULift.down (@uip PUnit.unit PUnit.unit ⟨x⟩ ⟨y⟩),
    fun equal _ _ p q => congrArg ULift.up (equal p.down q.down)⟩

theorem loopModel_sat_loopComm_iff :
    (loopModel.{u} L unit inv mul).Sat .loopComm ↔ ∀ x y : L, mul x y = mul y x :=
  ⟨fun comm x y => congrArg ULift.down (@comm PUnit.unit ⟨x⟩ ⟨y⟩),
    fun comm _ p q => congrArg ULift.up (comm p.down q.down)⟩

theorem loopModel_sat_connected : (loopModel.{u} L unit inv mul).Sat .connected :=
  fun _ _ => ⟨⟨unit⟩⟩

end LoopModel

/-! ### Two proofs of one identity: exclusive or -/

/-- One point and two loops, `false` (reflexivity) and `true`, composing by
exclusive or: a model with two different proofs of the same identity. -/
def xorModel : IdStructure.{u} :=
  loopModel Bool false id xor

theorem xorModel_mem_groupoidLaws : xorModel.{u} ∈ models IdStructure.Sat groupoidLaws :=
  loopModel_mem_groupoidLaws
    (fun x y z => by cases x <;> cases y <;> cases z <;> rfl)
    (fun x => by cases x <;> rfl) (fun x => by cases x <;> rfl)
    (fun x => by cases x <;> rfl) (fun x => by cases x <;> rfl)

/-- **The two proofs differ.** -/
theorem xorModel_not_uip : ¬ xorModel.{u}.Sat .uip := by
  intro uip
  exact Bool.noConfusion (loopModel_sat_uip_iff.mp uip false true)

theorem xorModel_sat_loopComm : xorModel.{u}.Sat .loopComm :=
  loopModel_sat_loopComm_iff.mpr fun x y => by cases x <;> cases y <;> rfl

/-! ### Non-commuting loops: the dihedral group of order six -/

/-- Rotations of a triangle. -/
inductive Rot
  | r0
  | r1
  | r2
  deriving DecidableEq

/-- Composition of rotations. -/
def Rot.add : Rot → Rot → Rot
  | .r0, k => k
  | .r1, .r0 => .r1
  | .r1, .r1 => .r2
  | .r1, .r2 => .r0
  | .r2, .r0 => .r2
  | .r2, .r1 => .r0
  | .r2, .r2 => .r1

/-- Inverse rotation. -/
def Rot.neg : Rot → Rot
  | .r0 => .r0
  | .r1 => .r2
  | .r2 => .r1

/-- Symmetries of a triangle: a rotation, possibly followed by a reflection. -/
structure D3 where
  rot : Rot
  flip : Bool
  deriving DecidableEq

/-- Composition of symmetries. -/
def D3.mul (x y : D3) : D3 :=
  ⟨Rot.add x.rot (if x.flip then Rot.neg y.rot else y.rot), xor x.flip y.flip⟩

/-- The identity symmetry. -/
def D3.one : D3 :=
  ⟨.r0, false⟩

/-- Inverse symmetry: reflections are involutions, rotations invert. -/
def D3.inv (x : D3) : D3 :=
  if x.flip then x else ⟨Rot.neg x.rot, false⟩

theorem D3.mul_assoc (x y z : D3) : D3.mul (D3.mul x y) z = D3.mul x (D3.mul y z) := by
  obtain ⟨a, s⟩ := x
  obtain ⟨b, t⟩ := y
  obtain ⟨c, w⟩ := z
  cases a <;> cases s <;> cases b <;> cases t <;> cases c <;> cases w <;> rfl

theorem D3.one_mul (x : D3) : D3.mul D3.one x = x := by
  obtain ⟨a, s⟩ := x
  cases a <;> cases s <;> rfl

theorem D3.mul_one (x : D3) : D3.mul x D3.one = x := by
  obtain ⟨a, s⟩ := x
  cases a <;> cases s <;> rfl

theorem D3.inv_mul (x : D3) : D3.mul (D3.inv x) x = D3.one := by
  obtain ⟨a, s⟩ := x
  cases a <;> cases s <;> rfl

theorem D3.mul_inv (x : D3) : D3.mul x (D3.inv x) = D3.one := by
  obtain ⟨a, s⟩ := x
  cases a <;> cases s <;> rfl

/-- A rotation and a reflection that do not commute. -/
theorem D3.not_comm :
    D3.mul ⟨.r1, false⟩ ⟨.r0, true⟩ ≠ D3.mul ⟨.r0, true⟩ ⟨.r1, false⟩ := by
  decide

/-- One point whose loops are the symmetries of a triangle. -/
def dihedralModel : IdStructure.{u} :=
  loopModel D3 D3.one D3.inv D3.mul

theorem dihedralModel_mem_groupoidLaws :
    dihedralModel.{u} ∈ models IdStructure.Sat groupoidLaws :=
  loopModel_mem_groupoidLaws D3.mul_assoc D3.one_mul D3.mul_one D3.inv_mul D3.mul_inv

theorem dihedralModel_not_loopComm : ¬ dihedralModel.{u}.Sat .loopComm := by
  intro comm
  exact D3.not_comm (loopModel_sat_loopComm_iff.mp comm _ _)

/-! ## The weak and the strong theory -/

/-- **The model classes differ, and the weaker theory has the larger class.** -/
theorem models_uipLaws_ssubset :
    models (IdStructure.Sat : IdStructure.{u} → IdSentence → Prop) uipLaws ⊆
        models IdStructure.Sat groupoidLaws ∧
      xorModel.{u} ∈ models IdStructure.Sat groupoidLaws ∧
      xorModel.{u} ∉ models IdStructure.Sat uipLaws :=
  ⟨models_anti groupoidLaws_subset_uipLaws, xorModel_mem_groupoidLaws,
    fun model => xorModel_not_uip (model (mem_insert _ _))⟩

/-- A model in which the two proofs are identified. -/
theorem eqModel_identifies (α : Type u) : eqModel α ∈ models IdStructure.Sat uipLaws :=
  eqModel_mem_uipLaws α

/-- Negative control: the stronger theory does not have the larger class. -/
theorem not_models_groupoidLaws_subset :
    ¬ models (IdStructure.Sat : IdStructure.{u} → IdSentence → Prop) groupoidLaws ⊆
      models IdStructure.Sat uipLaws :=
  fun included => models_uipLaws_ssubset.2.2 (included xorModel_mem_groupoidLaws)

/-- The weak theory does not entail `uip`. -/
theorem not_entails_uip :
    ¬ Entails (IdStructure.Sat : IdStructure.{u} → IdSentence → Prop) groupoidLaws .uip :=
  fun entails => xorModel_not_uip (entails xorModel_mem_groupoidLaws)

/-- Positive control: `uip` entails `loopComm`. -/
theorem entails_loopComm_uipLaws :
    Entails (IdStructure.Sat : IdStructure.{u} → IdSentence → Prop) uipLaws .loopComm :=
  fun _ model => IdStructure.sat_loopComm_of_uip (model (mem_insert _ _))

/-- Negative control for "different theories have different classes": adding
the consequence `loopComm` to `uipLaws` leaves the class unchanged. -/
theorem models_insert_loopComm_uipLaws :
    models (IdStructure.Sat : IdStructure.{u} → IdSentence → Prop) (insert .loopComm uipLaws) =
      models IdStructure.Sat uipLaws :=
  models_insert_eq_iff.mpr entails_loopComm_uipLaws

/-- The weak theory does not entail `loopComm`. -/
theorem not_entails_loopComm :
    ¬ Entails (IdStructure.Sat : IdStructure.{u} → IdSentence → Prop) groupoidLaws .loopComm :=
  fun entails => dihedralModel_not_loopComm (entails dihedralModel_mem_groupoidLaws)

/-- Neither theory entails `connected`. -/
theorem not_entails_connected :
    ¬ Entails (IdStructure.Sat : IdStructure.{u} → IdSentence → Prop) uipLaws .connected :=
  fun entails => eqModel_bool_not_connected (entails (eqModel_mem_uipLaws _))

/-- A structure violating a groupoid law: composition always returns the
non-reflexive loop. -/
def badModel : IdStructure.{u} :=
  loopModel Bool false id fun _ _ => true

/-- Negative control: `badModel` is a model of neither theory. -/
theorem badModel_not_model : badModel.{u} ∉ models IdStructure.Sat groupoidLaws := by
  intro model
  have leftUnit : badModel.{u}.Sat .leftUnit := model (Or.inr (Or.inl rfl))
  exact Bool.noConfusion (congrArg ULift.down (@leftUnit PUnit.unit PUnit.unit ⟨false⟩))

/-- The exact consequences of the weak theory: the groupoid laws are closed. -/
theorem consequences_groupoidLaws :
    theoryOf (IdStructure.Sat : IdStructure.{u} → IdSentence → Prop)
      (models IdStructure.Sat groupoidLaws) = groupoidLaws := by
  apply Subset.antisymm _ (subset_theoryOf_models groupoidLaws)
  intro φ entailed
  cases φ with
  | uip => exact (not_entails_uip entailed).elim
  | loopComm => exact (not_entails_loopComm entailed).elim
  | connected =>
      exact (eqModel_bool_not_connected (entailed (eqModel_mem_groupoidLaws _))).elim
  | assoc => exact Or.inl rfl
  | leftUnit => exact Or.inr (Or.inl rfl)
  | rightUnit => exact Or.inr (Or.inr (Or.inl rfl))
  | leftInv => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | rightInv => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-- The exact consequences of the strong theory: everything except
`connected`. -/
theorem consequences_uipLaws :
    theoryOf (IdStructure.Sat : IdStructure.{u} → IdSentence → Prop)
        (models IdStructure.Sat uipLaws) = {φ | φ ≠ .connected} := by
  ext φ
  constructor
  · intro entailed equal
    subst equal
    exact eqModel_bool_not_connected (entailed (eqModel_mem_uipLaws _))
  · intro notConnected
    cases φ with
    | connected => exact (notConnected rfl).elim
    | loopComm => exact entails_loopComm_uipLaws
    | uip => exact subset_theoryOf_models uipLaws (mem_insert _ _)
    | assoc => exact subset_theoryOf_models uipLaws (Or.inr (Or.inl rfl))
    | leftUnit => exact subset_theoryOf_models uipLaws (Or.inr (Or.inr (Or.inl rfl)))
    | rightUnit => exact subset_theoryOf_models uipLaws (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | leftInv =>
        exact subset_theoryOf_models uipLaws (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | rightInv =>
        exact subset_theoryOf_models uipLaws (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

/-! ## A ladder of universes -/

/-- The universe of structures whose parallel proofs are identified. -/
def thin : Set IdStructure.{u} :=
  {M | M.Sat .uip}

/-- The thin universe with the two-loop structure added. -/
def ladderOne : Set IdStructure.{u} :=
  insert xorModel thin

/-- Then the dihedral structure added. -/
def ladderTwo : Set IdStructure.{u} :=
  insert dihedralModel ladderOne

theorem thin_subset_ladderOne : thin.{u} ⊆ ladderOne := subset_insert _ _

theorem ladderOne_subset_ladderTwo : ladderOne.{u} ⊆ ladderTwo := subset_insert _ _

theorem eqModel_bool_mem_thin : eqModel (ULift.{u} Bool) ∈ thin := eqModel_sat_uip _

/-- The groupoid laws belong to the consequences computed in every universe. -/
theorem groupoidLaws_subset_consequencesIn (U : Set IdStructure.{u}) :
    groupoidLaws ⊆ consequencesIn IdStructure.Sat U groupoidLaws :=
  subset_consequencesIn U groupoidLaws

/-- **The thin universe validates `uip` and `loopComm`**, which the weak theory
does not entail. -/
theorem consequencesIn_thin :
    consequencesIn IdStructure.Sat thin.{u} groupoidLaws = {φ | φ ≠ .connected} := by
  ext φ
  constructor
  · intro validated equal
    subst equal
    exact eqModel_bool_not_connected
      (validated ⟨eqModel_bool_mem_thin, eqModel_mem_groupoidLaws _⟩)
  · intro notConnected
    cases φ with
    | connected => exact (notConnected rfl).elim
    | uip => exact fun _ hosted => hosted.1
    | loopComm => exact fun _ hosted => IdStructure.sat_loopComm_of_uip hosted.1
    | assoc => exact groupoidLaws_subset_consequencesIn _ (Or.inl rfl)
    | leftUnit => exact groupoidLaws_subset_consequencesIn _ (Or.inr (Or.inl rfl))
    | rightUnit => exact groupoidLaws_subset_consequencesIn _ (Or.inr (Or.inr (Or.inl rfl)))
    | leftInv =>
        exact groupoidLaws_subset_consequencesIn _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | rightInv =>
        exact groupoidLaws_subset_consequencesIn _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

theorem not_hostsFaithfully_thin : ¬ HostsFaithfully IdStructure.Sat thin.{u} groupoidLaws := by
  apply not_hostsFaithfully_of (φ := .uip)
  · rw [consequencesIn_thin]
    exact fun h => IdSentence.noConfusion h
  · exact fun entails => xorModel_not_uip (entails xorModel_mem_groupoidLaws)

/-- **Adding the two-loop structure refutes `uip` but still validates
`loopComm`.** -/
theorem consequencesIn_ladderOne :
    consequencesIn IdStructure.Sat ladderOne.{u} groupoidLaws =
      {φ | φ ≠ .connected ∧ φ ≠ .uip} := by
  ext φ
  constructor
  · intro validated
    refine ⟨fun equal => ?_, fun equal => ?_⟩
    · subst equal
      exact eqModel_bool_not_connected
        (validated ⟨thin_subset_ladderOne eqModel_bool_mem_thin, eqModel_mem_groupoidLaws _⟩)
    · subst equal
      exact xorModel_not_uip (validated ⟨mem_insert _ _, xorModel_mem_groupoidLaws⟩)
  · rintro ⟨notConnected, notUip⟩
    cases φ with
    | connected => exact (notConnected rfl).elim
    | uip => exact (notUip rfl).elim
    | loopComm =>
        rintro M ⟨hosted, _⟩
        rcases hosted with rfl | thinM
        · exact xorModel_sat_loopComm
        · exact IdStructure.sat_loopComm_of_uip thinM
    | assoc => exact groupoidLaws_subset_consequencesIn _ (Or.inl rfl)
    | leftUnit => exact groupoidLaws_subset_consequencesIn _ (Or.inr (Or.inl rfl))
    | rightUnit => exact groupoidLaws_subset_consequencesIn _ (Or.inr (Or.inr (Or.inl rfl)))
    | leftInv =>
        exact groupoidLaws_subset_consequencesIn _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | rightInv =>
        exact groupoidLaws_subset_consequencesIn _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

theorem not_hostsFaithfully_ladderOne :
    ¬ HostsFaithfully IdStructure.Sat ladderOne.{u} groupoidLaws := by
  apply not_hostsFaithfully_of (φ := .loopComm)
  · rw [consequencesIn_ladderOne]
    exact ⟨fun h => IdSentence.noConfusion h, fun h => IdSentence.noConfusion h⟩
  · exact fun entails => dihedralModel_not_loopComm (entails dihedralModel_mem_groupoidLaws)

/-- **Adding the dihedral structure hosts the weak theory faithfully.** -/
theorem consequencesIn_ladderTwo :
    consequencesIn IdStructure.Sat ladderTwo.{u} groupoidLaws = groupoidLaws := by
  apply Subset.antisymm _ (groupoidLaws_subset_consequencesIn _)
  intro φ validated
  cases φ with
  | uip =>
      exact (xorModel_not_uip
        (validated ⟨ladderOne_subset_ladderTwo (mem_insert _ _),
          xorModel_mem_groupoidLaws⟩)).elim
  | loopComm =>
      exact (dihedralModel_not_loopComm
        (validated ⟨mem_insert _ _, dihedralModel_mem_groupoidLaws⟩)).elim
  | connected =>
      exact (eqModel_bool_not_connected (validated
        ⟨ladderOne_subset_ladderTwo (thin_subset_ladderOne eqModel_bool_mem_thin),
          eqModel_mem_groupoidLaws _⟩)).elim
  | assoc => exact Or.inl rfl
  | leftUnit => exact Or.inr (Or.inl rfl)
  | rightUnit => exact Or.inr (Or.inr (Or.inl rfl))
  | leftInv => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | rightInv => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem hostsFaithfully_ladderTwo : HostsFaithfully IdStructure.Sat ladderTwo.{u} groupoidLaws := by
  unfold HostsFaithfully
  rw [consequencesIn_ladderTwo]
  apply Subset.antisymm (subset_theoryOf_models groupoidLaws)
  intro φ entailed
  cases φ with
  | uip => exact (xorModel_not_uip.{u} (entailed xorModel_mem_groupoidLaws)).elim
  | loopComm =>
      exact (dihedralModel_not_loopComm.{u} (entailed dihedralModel_mem_groupoidLaws)).elim
  | connected =>
      exact (eqModel_bool_not_connected.{u} (entailed (eqModel_mem_groupoidLaws _))).elim
  | assoc => exact Or.inl rfl
  | leftUnit => exact Or.inr (Or.inl rfl)
  | rightUnit => exact Or.inr (Or.inr (Or.inl rfl))
  | leftInv => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | rightInv => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-! ## Types with equivalences: a univalent structure -/

/-- Two equivalences with the same underlying function are equal. -/
theorem equiv_eq {A B : Type} {e e' : A ≃ B} (same : ∀ x, e x = e' x) : e = e' := by
  obtain ⟨f, g, left, right⟩ := e
  obtain ⟨f', g', left', right'⟩ := e'
  have functions : f = f' := funext same
  subst functions
  have inverses : g = g' := funext fun y => by
    calc g y = g (f (g' y)) := by rw [right' y]
      _ = g' y := left (g' y)
  subst inverses
  rfl

/-- Types as points and equivalences as identity proofs. -/
def univalentModel : IdStructure.{1} where
  Pt := Type
  Pf A B := ULift.{1} (A ≃ B)
  refl A := ⟨Equiv.refl A⟩
  inv p := ⟨p.down.symm⟩
  comp p q := ⟨p.down.trans q.down⟩

theorem univalentModel_mem_groupoidLaws : univalentModel ∈ models IdStructure.Sat groupoidLaws :=
  mem_models_groupoidLaws
    (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun p => congrArg ULift.up (equiv_eq fun x => p.down.right_inv x))
    (fun p => congrArg ULift.up (equiv_eq fun x => p.down.left_inv x))

/-- Negation as a self-equivalence of `Bool`. -/
def notEquiv : Bool ≃ Bool :=
  ⟨not, not, Bool.not_not, Bool.not_not⟩

theorem univalentModel_not_uip : ¬ univalentModel.Sat .uip := by
  intro uip
  have equal := congrArg (fun p : ULift (Bool ≃ Bool) => p.down true)
    (@uip Bool Bool ⟨Equiv.refl Bool⟩ ⟨notEquiv⟩)
  exact Bool.noConfusion equal

/-- Left multiplication by a symmetry, as a self-equivalence of `D3`. -/
def leftMulEquiv (g : D3) : D3 ≃ D3 where
  toFun := D3.mul g
  invFun := D3.mul (D3.inv g)
  left_inv x := by
    rw [← D3.mul_assoc, D3.inv_mul, D3.one_mul]
  right_inv x := by
    rw [← D3.mul_assoc, D3.mul_inv, D3.one_mul]

theorem univalentModel_not_loopComm : ¬ univalentModel.Sat .loopComm := by
  intro comm
  have equal := congrArg (fun p : ULift (D3 ≃ D3) => p.down D3.one)
    (@comm D3 ⟨leftMulEquiv ⟨.r1, false⟩⟩ ⟨leftMulEquiv ⟨.r0, true⟩⟩)
  change D3.mul ⟨.r0, true⟩ (D3.mul ⟨.r1, false⟩ D3.one) =
    D3.mul ⟨.r1, false⟩ (D3.mul ⟨.r0, true⟩ D3.one) at equal
  rw [D3.mul_one, D3.mul_one] at equal
  exact D3.not_comm equal.symm

theorem univalentModel_not_connected : ¬ univalentModel.Sat .connected := by
  intro connected
  obtain ⟨⟨e⟩⟩ := connected PUnit Empty
  exact (e PUnit.unit).elim

/-- **The univalent structure alone hosts the weak theory faithfully.** -/
theorem hostsFaithfully_univalent :
    HostsFaithfully IdStructure.Sat ({univalentModel} : Set IdStructure.{1}) groupoidLaws := by
  apply hostsFaithfully_iff_subset.mpr
  rw [consequences_groupoidLaws]
  intro φ validated
  have hosted : univalentModel ∈ modelsIn IdStructure.Sat {univalentModel} groupoidLaws :=
    ⟨rfl, univalentModel_mem_groupoidLaws⟩
  cases φ with
  | uip => exact (univalentModel_not_uip (validated hosted)).elim
  | loopComm => exact (univalentModel_not_loopComm (validated hosted)).elim
  | connected => exact (univalentModel_not_connected (validated hosted)).elim
  | assoc => exact Or.inl rfl
  | leftUnit => exact Or.inr (Or.inl rfl)
  | rightUnit => exact Or.inr (Or.inr (Or.inl rfl))
  | leftInv => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | rightInv => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-- The same points with Lean's equality as proofs: a thin structure. -/
theorem eqModel_type_thin : eqModel Type ∈ thin.{1} :=
  eqModel_sat_uip Type

/-- Negative control: with equality in place of equivalence the universe of
types validates `uip`. -/
theorem not_hostsFaithfully_eqModel_type :
    ¬ HostsFaithfully IdStructure.Sat ({eqModel Type} : Set IdStructure.{1}) groupoidLaws := by
  apply not_hostsFaithfully_of (φ := .uip)
  · rintro M ⟨rfl, _⟩
    exact eqModel_sat_uip Type
  · exact not_entails_uip.{1}

/-! ## Larger Lean universes -/

/-- Lift a structure to a larger Lean universe. -/
def IdStructure.ulift (M : IdStructure.{u}) : IdStructure.{max u v} where
  Pt := ULift.{v} M.Pt
  Pf a b := ULift.{v} (M.Pf a.down b.down)
  refl a := ⟨M.refl a.down⟩
  inv p := ⟨M.inv p.down⟩
  comp p q := ⟨M.comp p.down q.down⟩

/-- Lifting preserves and reflects satisfaction. -/
theorem sat_ulift (M : IdStructure.{u}) (φ : IdSentence) :
    (IdStructure.ulift.{u, v} M).Sat φ ↔ M.Sat φ := by
  cases φ with
  | assoc =>
      exact ⟨fun h a b c d p q r =>
          congrArg ULift.down (@h ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨d⟩ ⟨p⟩ ⟨q⟩ ⟨r⟩),
        fun h _ _ _ _ p q r => congrArg ULift.up (h p.down q.down r.down)⟩
  | leftUnit =>
      exact ⟨fun h a b p => congrArg ULift.down (@h ⟨a⟩ ⟨b⟩ ⟨p⟩),
        fun h _ _ p => congrArg ULift.up (h p.down)⟩
  | rightUnit =>
      exact ⟨fun h a b p => congrArg ULift.down (@h ⟨a⟩ ⟨b⟩ ⟨p⟩),
        fun h _ _ p => congrArg ULift.up (h p.down)⟩
  | leftInv =>
      exact ⟨fun h a b p => congrArg ULift.down (@h ⟨a⟩ ⟨b⟩ ⟨p⟩),
        fun h _ _ p => congrArg ULift.up (h p.down)⟩
  | rightInv =>
      exact ⟨fun h a b p => congrArg ULift.down (@h ⟨a⟩ ⟨b⟩ ⟨p⟩),
        fun h _ _ p => congrArg ULift.up (h p.down)⟩
  | uip =>
      exact ⟨fun h a b p q => congrArg ULift.down (@h ⟨a⟩ ⟨b⟩ ⟨p⟩ ⟨q⟩),
        fun h _ _ p q => congrArg ULift.up (h p.down q.down)⟩
  | loopComm =>
      exact ⟨fun h a p q => congrArg ULift.down (@h ⟨a⟩ ⟨p⟩ ⟨q⟩),
        fun h _ p q => congrArg ULift.up (h p.down q.down)⟩
  | connected =>
      exact ⟨fun h a b => (h ⟨a⟩ ⟨b⟩).elim fun p => ⟨p.down⟩,
        fun h a b => (h a.down b.down).elim fun p => ⟨⟨p⟩⟩⟩

/-- **A larger Lean universe validates no more sentences.** -/
theorem consequences_ulift_subset (T : Set IdSentence) :
    theoryOf (IdStructure.Sat : IdStructure.{max u v} → IdSentence → Prop)
        (models IdStructure.Sat T) ⊆
      theoryOf (IdStructure.Sat : IdStructure.{u} → IdSentence → Prop)
        (models IdStructure.Sat T) :=
  consequences_subset_of_embedding IdStructure.ulift.{u, v} (sat_ulift) T

/-! ## Forgetting proofs versus identifying them -/

/-- The truncation observer: two structures look alike when a bijection of
their points preserves and reflects which points are joined by a proof. -/
def truncation : Setoid IdStructure.{u} where
  r M N := ∃ e : M.Pt ≃ N.Pt, ∀ a b, Nonempty (M.Pf a b) ↔ Nonempty (N.Pf (e a) (e b))
  iseqv := {
    refl := fun _ => ⟨Equiv.refl _, fun _ _ => Iff.rfl⟩
    symm := fun ⟨e, same⟩ => ⟨e.symm, fun a b => by
      have transported := same (e.symm a) (e.symm b)
      rw [e.apply_symm_apply, e.apply_symm_apply] at transported
      exact transported.symm⟩
    trans := fun ⟨e, same⟩ ⟨e', same'⟩ =>
      ⟨e.trans e', fun a b => (same a b).trans (same' (e a) (e b))⟩ }

/-- The truncation observer can evaluate `connected`. -/
theorem connected_observable :
    IdSentence.connected ∈ observable IdStructure.Sat truncation.{u} := by
  rintro M N ⟨e, same⟩
  constructor
  · intro connected a b
    have transported := (same (e.symm a) (e.symm b)).mp (connected _ _)
    rw [e.apply_symm_apply, e.apply_symm_apply] at transported
    exact transported
  · exact fun connected a b => (same a b).mpr (connected _ _)

/-- One point with its single equality proof and the two-loop structure look
alike to the truncation observer. -/
theorem eqModel_punit_truncation_xor : truncation.{u} (eqModel PUnit) xorModel :=
  ⟨Equiv.refl _, fun _ _ => ⟨fun _ => ⟨⟨false⟩⟩, fun _ => ⟨⟨⟨rfl⟩⟩⟩⟩⟩

/-- The two-loop and the dihedral structure look alike to the truncation
observer. -/
theorem xor_truncation_dihedral : truncation.{u} xorModel dihedralModel :=
  ⟨Equiv.refl _, fun _ _ => ⟨fun _ => ⟨⟨D3.one⟩⟩, fun _ => ⟨⟨false⟩⟩⟩⟩

/-- Negative control: the truncation observer cannot evaluate `uip`. -/
theorem uip_not_observable : IdSentence.uip ∉ observable IdStructure.Sat truncation.{u} :=
  fun invariant => xorModel_not_uip ((invariant eqModel_punit_truncation_xor).mp
    (eqModel_sat_uip PUnit))

/-- Negative control: nor `loopComm`. -/
theorem loopComm_not_observable :
    IdSentence.loopComm ∉ observable IdStructure.Sat truncation.{u} :=
  fun invariant => dihedralModel_not_loopComm ((invariant xor_truncation_dihedral).mp
    xorModel_sat_loopComm)

/-- **Forgetting proofs admits the proof-relevant structure; identifying them
excludes it.** The two-loop structure is a model of the truncation-observed
theory of `eqModel PUnit`, but not of its full theory, which contains `uip`. -/
theorem forgetting_versus_identifying :
    xorModel.{u} ∈ models IdStructure.Sat
        (observedTheory (IdStructure.Sat : IdStructure.{u} → IdSentence → Prop) truncation
          {eqModel PUnit}) ∧
      xorModel.{u} ∉ models IdStructure.Sat
        (theoryOf (IdStructure.Sat : IdStructure.{u} → IdSentence → Prop) {eqModel PUnit}) := by
  constructor
  · exact saturation_subset_models_observedTheory (Sat := IdStructure.Sat) truncation
      {eqModel PUnit}
      ⟨eqModel PUnit, rfl, eqModel_punit_truncation_xor⟩
  · intro model
    apply xorModel_not_uip
    apply model
    rintro M rfl
    exact eqModel_sat_uip PUnit

end Mettapedia.Logic.TheoryModel.IdentityProofs
