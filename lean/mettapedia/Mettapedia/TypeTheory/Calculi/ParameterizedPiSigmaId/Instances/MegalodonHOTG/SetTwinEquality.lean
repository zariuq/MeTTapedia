import Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation
import Mettapedia.Logic.HOL.Embedding.ZFSetUniverseInterpretation
import Mathlib.Order.SuccPred.Basic
import Mathlib.Order.SuccPred.Limit
import Mathlib.SetTheory.ZFC.Rank

/-!
# Equality as sameness of members

A Henkin model reads equality at a base type as identity, so substitution is
valid in every such model. The carrier here is a hereditarily coded set with a
tag. Membership ignores the tag, and equality means having the same members.
Extensionality, the other six set laws, the four universe laws and the choice
law hold. The tag separates two empty sets, so substitution fails, and
Leibniz `same` does not follow from the two inclusions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace MegalodonHOTG
namespace TwinExtensional

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding
open ZFSetHenkinInterpretation

universe u

noncomputable section

/-- A code is a Kuratowski pair of a payload and a tag. Tags are `∅` and `{∅}`. -/
def tagCode : Bool → ZFSet.{u}
  | false => ∅
  | true => ({∅} : ZFSet.{u})

theorem tagCode_false : tagCode false = (∅ : ZFSet.{u}) := rfl

theorem tagCode_true : tagCode true = ({∅} : ZFSet.{u}) := rfl

theorem tagCode_inj {b₁ b₂ : Bool} (h : tagCode b₁ = tagCode b₂) : b₁ = b₂ := by
  cases b₁ <;> cases b₂
  · rfl
  · exfalso
    have hrank := congrArg ZFSet.rank h
    simp only [tagCode, ZFSet.rank_empty, ZFSet.rank_singleton] at hrank
    exact ne_of_lt (Order.lt_succ 0) hrank
  · exfalso
    have hrank := congrArg ZFSet.rank h
    simp only [tagCode, ZFSet.rank_empty, ZFSet.rank_singleton] at hrank
    exact ne_of_gt (Order.lt_succ 0) hrank
  · rfl

/-- Heredity of a payload of codes. The code witness and the recursive payload
stay separate premises, so the recursive occurrence is not inside `Exists`. -/
inductive Hered : ZFSet.{u} → Prop where
  | mk (s : ZFSet.{u})
      (codes : ∀ c, c ∈ s → ∃ t : ZFSet.{u}, ∃ b : Bool, c = ZFSet.pair t (tagCode b))
      (ih : ∀ c, c ∈ s → ∀ t : ZFSet.{u}, ∀ b : Bool,
        c = ZFSet.pair t (tagCode b) → Hered t) :
      Hered s

theorem hered_elim {s c : ZFSet.{u}} (hs : Hered s) (hc : c ∈ s) :
    ∃ t : ZFSet.{u}, ∃ b : Bool, c = ZFSet.pair t (tagCode b) ∧ Hered t := by
  cases hs with
  | mk _ codes ih =>
    obtain ⟨t, b, heq⟩ := codes c hc
    exact ⟨t, b, heq, ih c hc t b heq⟩

theorem hered_payload_of_code {s c t : ZFSet.{u}} {b : Bool} (hs : Hered s)
    (hc : c ∈ s) (heq : c = ZFSet.pair t (tagCode b)) : Hered t := by
  cases hs with
  | mk _ _ ih =>
    exact ih c hc t b heq

/-- A set is its payload of codes, together with a tag membership ignores. -/
@[ext]
structure Twin where
  payload : ZFSet.{u}
  tag : Bool
  hered : Hered payload

def encode (t : Twin) : ZFSet.{u} := ZFSet.pair t.payload (tagCode t.tag)

def memT (x y : Twin) : Prop := encode x ∈ y.payload

/-- Equality of this reading: the same members. -/
def sameMembers (x y : Twin) : Prop := ∀ z, memT z x ↔ memT z y

noncomputable def decode {s c : ZFSet.{u}} (hs : Hered s) (hc : c ∈ s) : Twin :=
  ⟨Classical.choose (hered_elim hs hc),
    Classical.choose (Classical.choose_spec (hered_elim hs hc)),
    (Classical.choose_spec (Classical.choose_spec (hered_elim hs hc))).2⟩

theorem encode_decode {s c : ZFSet.{u}} (hs : Hered s) (hc : c ∈ s) :
    encode (decode hs hc) = c := by
  unfold encode decode
  exact (Classical.choose_spec (Classical.choose_spec (hered_elim hs hc))).1.symm

theorem twin_eq_of_payload_tag {x y : Twin} (hp : x.payload = y.payload)
    (ht : x.tag = y.tag) : x = y := by
  cases x with
  | mk px tx hx =>
    cases y with
    | mk py ty hy =>
      cases hp
      cases ht
      congr

theorem decode_stable {s c : ZFSet.{u}} (hs : Hered s) (h₁ h₂ : c ∈ s) :
    decode hs h₁ = decode hs h₂ := by
  have hinj := ZFSet.pair_inj.mp ((encode_decode hs h₁).trans (encode_decode hs h₂).symm)
  exact twin_eq_of_payload_tag hinj.1 (tagCode_inj hinj.2)

theorem decode_encode {s : ZFSet.{u}} (hs : Hered s) (a : Twin) (h : encode a ∈ s) :
    decode hs h = a := by
  have hinj := ZFSet.pair_inj.mp (encode_decode hs h)
  exact twin_eq_of_payload_tag hinj.1 (tagCode_inj hinj.2)

theorem hered_empty : Hered (∅ : ZFSet.{u}) :=
  Hered.mk ∅
    (fun c hc => (ZFSet.notMem_empty c hc).elim)
    (fun c hc _ _ _ => (ZFSet.notMem_empty c hc).elim)

theorem hered_subset {s t : ZFSet.{u}} (hs : Hered s) (hsub : t ⊆ s) : Hered t := by
  cases hs with
  | mk _ codes ih =>
    exact Hered.mk t
      (fun c hc => codes c (hsub hc))
      (fun c hc p b heq => ih c (hsub hc) p b heq)

def emptyT : Twin := ⟨∅, false, hered_empty⟩

def markedEmpty : Twin := ⟨∅, true, hered_empty⟩

theorem sameMembers_iff_payload {x y : Twin} :
    sameMembers x y ↔ x.payload = y.payload := by
  constructor
  · intro h
    refine ZFSet.ext fun c => ?_
    constructor
    · intro hc
      have hx : memT (decode x.hered hc) x := by
        unfold memT
        rw [encode_decode]
        exact hc
      have hy := (h (decode x.hered hc)).1 hx
      unfold memT at hy
      rw [encode_decode] at hy
      exact hy
    · intro hc
      have hy : memT (decode y.hered hc) y := by
        unfold memT
        rw [encode_decode]
        exact hc
      have hx := (h (decode y.hered hc)).2 hy
      unfold memT at hx
      rw [encode_decode] at hx
      exact hx
  · intro h z
    unfold memT
    rw [h]

theorem same_empty_twins : sameMembers emptyT markedEmpty :=
  sameMembers_iff_payload.mpr rfl

theorem rank_lt_pair_left (x y : ZFSet.{u}) : x.rank < (ZFSet.pair x y).rank := by
  have hsing : x.rank < ({x} : ZFSet.{u}).rank :=
    ZFSet.rank_lt_of_mem (ZFSet.mem_singleton.mpr rfl)
  have hmem : ({x} : ZFSet.{u}) ∈ ZFSet.pair x y := by
    unfold ZFSet.pair
    exact ZFSet.mem_pair.mpr (Or.inl rfl)
  exact hsing.trans (ZFSet.rank_lt_of_mem hmem)

theorem payload_rank_lt_of_mem {x y : Twin} (h : memT x y) :
    x.payload.rank < y.payload.rank := by
  unfold memT at h
  exact (rank_lt_pair_left x.payload (tagCode x.tag)).trans (ZFSet.rank_lt_of_mem h)

theorem twin_induction {P : Twin → Prop}
    (step : ∀ x, (∀ y, memT y x → P y) → P x) (x : Twin) : P x := by
  refine WellFounded.induction
    (InvImage.wf (fun t : Twin => t.payload.rank) wellFounded_lt) x ?_
  intro x ih
  apply step x
  intro y hy
  exact ih y (payload_rank_lt_of_mem hy)

def bothEncodes (p : ZFSet.{u}) : ZFSet.{u} :=
  insert (ZFSet.pair p (tagCode false)) ({ZFSet.pair p (tagCode true)} : ZFSet.{u})

theorem mem_bothEncodes {p c : ZFSet.{u}} :
    c ∈ bothEncodes p ↔
      c = ZFSet.pair p (tagCode false) ∨ c = ZFSet.pair p (tagCode true) := by
  unfold bothEncodes
  rw [ZFSet.mem_insert_iff, ZFSet.mem_singleton]

theorem hered_both {p : ZFSet.{u}} (hp : Hered p) : Hered (bothEncodes p) := by
  refine Hered.mk (bothEncodes p) ?_ ?_
  · intro c hc
    rw [mem_bothEncodes] at hc
    rcases hc with rfl | rfl
    · exact ⟨p, false, rfl⟩
    · exact ⟨p, true, rfl⟩
  · intro c hc t b heq
    rw [mem_bothEncodes] at hc
    rcases hc with h | h
    · obtain ⟨rfl, _⟩ := ZFSet.pair_inj.mp (heq.symm.trans h)
      exact hp
    · obtain ⟨rfl, _⟩ := ZFSet.pair_inj.mp (heq.symm.trans h)
      exact hp

def image1 (f : ZFSet.{u} → ZFSet.{u}) (s : ZFSet.{u}) : ZFSet.{u} := by
  letI : ZFSet.Definable₁ f :=
    Classical.allZFSetDefinable (fun xs : Fin 1 → ZFSet.{u} => f (xs 0))
  exact ZFSet.image f s

theorem mem_image1 {f : ZFSet.{u} → ZFSet.{u}} {s y : ZFSet.{u}} :
    y ∈ image1 f s ↔ ∃ z ∈ s, f z = y := by
  unfold image1
  let : ZFSet.Definable₁ f :=
    Classical.allZFSetDefinable (fun xs : Fin 1 → ZFSet.{u} => f (xs 0))
  exact ZFSet.mem_image

def payloadOf (a : Twin) (c : ZFSet.{u}) : ZFSet.{u} :=
  haveI := Classical.propDecidable (c ∈ a.payload)
  if h : c ∈ a.payload then (decode a.hered h).payload else ∅

theorem payloadOf_mem {a : Twin} {c : ZFSet.{u}} (h : c ∈ a.payload) :
    payloadOf a c = (decode a.hered h).payload := by
  unfold payloadOf
  split
  · next h' =>
    rw [decode_stable a.hered h' h]
  · next hn => exact (hn h).elim

def unionPayload (a : Twin) : ZFSet.{u} :=
  ZFSet.sUnion (image1 (payloadOf a) a.payload)

theorem hered_union (a : Twin) : Hered (unionPayload a) := by
  refine Hered.mk (unionPayload a) ?_ ?_
  · intro c hc
    rw [unionPayload, ZFSet.mem_sUnion] at hc
    obtain ⟨w, hw, hcw⟩ := hc
    rw [mem_image1] at hw
    obtain ⟨d, hd, rfl⟩ := hw
    rw [payloadOf_mem hd] at hcw
    obtain ⟨t, b, heq, _⟩ := hered_elim (decode a.hered hd).hered hcw
    exact ⟨t, b, heq⟩
  · intro c hc t b heq
    rw [unionPayload, ZFSet.mem_sUnion] at hc
    obtain ⟨w, hw, hcw⟩ := hc
    rw [mem_image1] at hw
    obtain ⟨d, hd, rfl⟩ := hw
    rw [payloadOf_mem hd] at hcw
    exact hered_payload_of_code (decode a.hered hd).hered hcw heq

def unionT (a : Twin) : Twin := ⟨unionPayload a, false, hered_union a⟩

theorem mem_unionT {a x : Twin} :
    memT x (unionT a) ↔ ∃ y, memT y a ∧ memT x y := by
  unfold memT unionT
  constructor
  · intro hx
    change encode x ∈ unionPayload a at hx
    rw [unionPayload, ZFSet.mem_sUnion] at hx
    obtain ⟨w, hw, hxw⟩ := hx
    rw [mem_image1] at hw
    obtain ⟨d, hd, rfl⟩ := hw
    rw [payloadOf_mem hd] at hxw
    refine ⟨decode a.hered hd, ?_, hxw⟩
    rw [encode_decode]
    exact hd
  · rintro ⟨y, hya, hxy⟩
    change encode x ∈ unionPayload a
    rw [unionPayload]
    have hy : encode x ∈ payloadOf a (encode y) := by
      rw [payloadOf_mem hya, decode_encode a.hered y hya]
      exact hxy
    have hz : payloadOf a (encode y) ∈ image1 (payloadOf a) a.payload := by
      rw [mem_image1]
      exact ⟨encode y, hya, rfl⟩
    exact ZFSet.mem_sUnion_of_mem hy hz

def subsetCodes (a : Twin) (u : ZFSet.{u}) : ZFSet.{u} :=
  haveI := Classical.propDecidable (u ⊆ a.payload)
  if _h : u ⊆ a.payload then bothEncodes u else ∅

theorem subsetCodes_subset {a : Twin} {u : ZFSet.{u}} (h : u ⊆ a.payload) :
    subsetCodes a u = bothEncodes u := by
  unfold subsetCodes
  split
  · rfl
  · next hn => exact (hn h).elim

def powerPayload (a : Twin) : ZFSet.{u} :=
  ZFSet.sUnion (image1 (subsetCodes a) (ZFSet.powerset a.payload))

theorem hered_power (a : Twin) : Hered (powerPayload a) := by
  refine Hered.mk (powerPayload a) ?_ ?_
  · intro c hc
    rw [powerPayload, ZFSet.mem_sUnion] at hc
    obtain ⟨w, hw, hcw⟩ := hc
    rw [mem_image1] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    have hsub : u ⊆ a.payload := ZFSet.mem_powerset.mp hu
    rw [subsetCodes_subset hsub] at hcw
    obtain ⟨t, b, heq, _⟩ :=
      hered_elim (hered_both (hered_subset a.hered hsub)) hcw
    exact ⟨t, b, heq⟩
  · intro c hc t b heq
    rw [powerPayload, ZFSet.mem_sUnion] at hc
    obtain ⟨w, hw, hcw⟩ := hc
    rw [mem_image1] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    have hsub : u ⊆ a.payload := ZFSet.mem_powerset.mp hu
    rw [subsetCodes_subset hsub] at hcw
    exact hered_payload_of_code (hered_both (hered_subset a.hered hsub)) hcw heq

def powerT (a : Twin) : Twin := ⟨powerPayload a, false, hered_power a⟩

theorem mem_powerT {a b : Twin} :
    memT b (powerT a) ↔ ∀ z, memT z b → memT z a := by
  unfold memT powerT
  constructor
  · intro hb z hz
    change encode b ∈ powerPayload a at hb
    rw [powerPayload, ZFSet.mem_sUnion] at hb
    obtain ⟨w, hw, hbw⟩ := hb
    rw [mem_image1] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    have hsub : u ⊆ a.payload := ZFSet.mem_powerset.mp hu
    rw [subsetCodes_subset hsub, mem_bothEncodes] at hbw
    have hpayload : b.payload = u := by
      rcases hbw with h | h
      · exact (ZFSet.pair_inj.mp h).1
      · exact (ZFSet.pair_inj.mp h).1
    rw [hpayload] at hz
    exact hsub hz
  · intro h
    change encode b ∈ powerPayload a
    rw [powerPayload]
    have hsub : b.payload ⊆ a.payload := by
      intro c hc
      have hz : encode (decode b.hered hc) ∈ b.payload := by
        rw [encode_decode]
        exact hc
      have hmem := h (decode b.hered hc) hz
      rwa [encode_decode] at hmem
    have hy : encode b ∈ subsetCodes a b.payload := by
      rw [subsetCodes_subset hsub, mem_bothEncodes]
      have henc : encode b = ZFSet.pair b.payload (tagCode b.tag) := rfl
      cases htag : b.tag
      · rw [htag] at henc
        exact Or.inl henc
      · rw [htag] at henc
        exact Or.inr henc
    have hz : subsetCodes a b.payload ∈
        image1 (subsetCodes a) (ZFSet.powerset a.payload) := by
      rw [mem_image1]
      exact ⟨b.payload, ZFSet.mem_powerset.mpr hsub, rfl⟩
    exact ZFSet.mem_sUnion_of_mem hy hz

def sepPayload (a : Twin) (P : Twin → ULift.{u + 1} Prop) : ZFSet.{u} :=
  ZFSet.sep (fun c => ∀ h : c ∈ a.payload, (P (decode a.hered h)).down) a.payload

theorem hered_sep (a : Twin) (P : Twin → ULift.{u + 1} Prop) : Hered (sepPayload a P) :=
  hered_subset a.hered (ZFSet.sep_subset (x := a.payload))

def sepT (a : Twin) (P : Twin → ULift.{u + 1} Prop) : Twin :=
  ⟨sepPayload a P, false, hered_sep a P⟩

theorem mem_sepT {a : Twin} {P : Twin → ULift.{u + 1} Prop} {x : Twin} :
    memT x (sepT a P) ↔ memT x a ∧ (P x).down := by
  unfold memT sepT
  constructor
  · intro hx
    change encode x ∈ sepPayload a P at hx
    rw [sepPayload, ZFSet.mem_sep] at hx
    refine ⟨hx.1, ?_⟩
    have hP := hx.2 hx.1
    rwa [decode_encode a.hered x hx.1] at hP
  · intro hx
    change encode x ∈ sepPayload a P
    rw [sepPayload, ZFSet.mem_sep]
    refine ⟨hx.1, ?_⟩
    intro h
    rw [decode_encode a.hered x h]
    exact hx.2

def valueCodes (a : Twin) (F : Twin → Twin) (c : ZFSet.{u}) : ZFSet.{u} :=
  haveI := Classical.propDecidable (c ∈ a.payload)
  if h : c ∈ a.payload then bothEncodes (F (decode a.hered h)).payload else ∅

theorem valueCodes_mem {a : Twin} {F : Twin → Twin} {c : ZFSet.{u}} (h : c ∈ a.payload) :
    valueCodes a F c = bothEncodes (F (decode a.hered h)).payload := by
  unfold valueCodes
  split
  · next h' => rw [decode_stable a.hered h' h]
  · next hn => exact (hn h).elim

def replPayload (a : Twin) (F : Twin → Twin) : ZFSet.{u} :=
  ZFSet.sUnion (image1 (valueCodes a F) a.payload)

theorem hered_repl (a : Twin) (F : Twin → Twin) : Hered (replPayload a F) := by
  refine Hered.mk (replPayload a F) ?_ ?_
  · intro c hc
    rw [replPayload, ZFSet.mem_sUnion] at hc
    obtain ⟨w, hw, hcw⟩ := hc
    rw [mem_image1] at hw
    obtain ⟨d, hd, rfl⟩ := hw
    rw [valueCodes_mem hd, mem_bothEncodes] at hcw
    rcases hcw with rfl | rfl
    · exact ⟨(F (decode a.hered hd)).payload, false, rfl⟩
    · exact ⟨(F (decode a.hered hd)).payload, true, rfl⟩
  · intro c hc t b heq
    rw [replPayload, ZFSet.mem_sUnion] at hc
    obtain ⟨w, hw, hcw⟩ := hc
    rw [mem_image1] at hw
    obtain ⟨d, hd, rfl⟩ := hw
    rw [valueCodes_mem hd, mem_bothEncodes] at hcw
    rcases hcw with h | h
    · obtain ⟨rfl, _⟩ := ZFSet.pair_inj.mp (heq.symm.trans h)
      exact (F (decode a.hered hd)).hered
    · obtain ⟨rfl, _⟩ := ZFSet.pair_inj.mp (heq.symm.trans h)
      exact (F (decode a.hered hd)).hered

def replT (a : Twin) (F : Twin → Twin) : Twin :=
  ⟨replPayload a F, false, hered_repl a F⟩

theorem mem_replT {a : Twin} {F : Twin → Twin} {y : Twin} :
    memT y (replT a F) ↔ ∃ x, memT x a ∧ sameMembers (F x) y := by
  unfold memT replT
  constructor
  · intro hy
    change encode y ∈ replPayload a F at hy
    rw [replPayload, ZFSet.mem_sUnion] at hy
    obtain ⟨w, hw, hyw⟩ := hy
    rw [mem_image1] at hw
    obtain ⟨d, hd, rfl⟩ := hw
    rw [valueCodes_mem hd, mem_bothEncodes] at hyw
    refine ⟨decode a.hered hd, ?_, ?_⟩
    · rw [encode_decode]
      exact hd
    · rw [sameMembers_iff_payload]
      rcases hyw with h | h
      · exact (ZFSet.pair_inj.mp h).1.symm
      · exact (ZFSet.pair_inj.mp h).1.symm
  · rintro ⟨x, hxa, hxy⟩
    change encode y ∈ replPayload a F
    rw [replPayload]
    have hpayload : y.payload = (F x).payload := (sameMembers_iff_payload.mp hxy).symm
    have hdec : decode a.hered hxa = x := decode_encode a.hered x hxa
    have hy : encode y ∈ valueCodes a F (encode x) := by
      rw [valueCodes_mem hxa, mem_bothEncodes, hdec]
      have henc : encode y = ZFSet.pair y.payload (tagCode y.tag) := rfl
      rw [hpayload] at henc
      cases htag : y.tag
      · rw [htag] at henc
        exact Or.inl henc
      · rw [htag] at henc
        exact Or.inr henc
    have hz : valueCodes a F (encode x) ∈ image1 (valueCodes a F) a.payload := by
      rw [mem_image1]
      exact ⟨encode x, hxa, rfl⟩
    exact ZFSet.mem_sUnion_of_mem hy hz

def epsT (P : Twin → ULift.{u + 1} Prop) : Twin :=
  haveI := Classical.propDecidable (∃ x, (P x).down)
  if h : ∃ x, (P x).down then Classical.choose h else emptyT

theorem epsT_spec {P : Twin → ULift.{u + 1} Prop} {x : Twin} (hx : (P x).down) :
    (P (epsT P)).down := by
  have witness : ∃ y, (P y).down := ⟨x, hx⟩
  unfold epsT
  split
  · next h => exact Classical.choose_spec h
  · next h => exact absurd witness h

/-- Carriers for the twin reading. The base type is `Twin`, and a predicate is a
function into `ULift`, both at this section's universe. -/
@[reducible] def TDen : Ty Unit → Type (u + 1)
  | .prop => ULift.{u + 1} Prop
  | .base _ => Twin
  | .arr σ τ => TDen σ → TDen τ

abbrev TVal (Γ : Ctx Unit) := ∀ {τ : Ty Unit}, Var Γ τ → TDen τ

def twinExtend {Γ : Ctx Unit} {σ : Ty Unit} (ρ : TVal Γ) (x : TDen σ) : TVal (σ :: Γ)
  | _, .vz => x
  | _, .vs v => ρ v

def twinEqv : (τ : Ty Unit) → TDen τ → TDen τ → Prop
  | .prop, p, q => p.down ↔ q.down
  | .base _, x, y => sameMembers x y
  | .arr _ τ, f, g => ∀ x, twinEqv τ (f x) (g x)

def twinDenote {Const : Ty Unit → Type} (constDen : {τ : Ty Unit} → Const τ → TDen τ) :
    {Γ : Ctx Unit} → {τ : Ty Unit} → Term Const Γ τ → TVal Γ → TDen τ
  | _, _, .var v, ρ => ρ v
  | _, _, .const c, _ => constDen c
  | _, _, .app f t, ρ => twinDenote constDen f ρ (twinDenote constDen t ρ)
  | _, _, .lam t, ρ => fun x => twinDenote constDen t (twinExtend ρ x)
  | _, _, .top, _ => .up True
  | _, _, .bot, _ => .up False
  | _, _, .and φ ψ, ρ => .up ((twinDenote constDen φ ρ).down ∧ (twinDenote constDen ψ ρ).down)
  | _, _, .or φ ψ, ρ => .up ((twinDenote constDen φ ρ).down ∨ (twinDenote constDen ψ ρ).down)
  | _, _, .imp φ ψ, ρ => .up ((twinDenote constDen φ ρ).down → (twinDenote constDen ψ ρ).down)
  | _, _, .not φ, ρ => .up (¬ (twinDenote constDen φ ρ).down)
  | _, _, .eq t u, ρ => .up (twinEqv _ (twinDenote constDen t ρ) (twinDenote constDen u ρ))
  | _, _, .all φ, ρ => .up (∀ x, (twinDenote constDen φ (twinExtend ρ x)).down)
  | _, _, .ex φ, ρ => .up (∃ x, (twinDenote constDen φ (twinExtend ρ x)).down)

def twinModels {Const : Ty Unit → Type}
    (constDen : {τ : Ty Unit} → Const τ → TDen τ) (φ : ClosedFormula Const) : Prop :=
  (twinDenote constDen φ (fun v => nomatch v)).down

def twinSymbol : {A : Ty Unit} → Symbol A → TDen A
  | _, .member => fun x a => .up (memT x a)
  | _, .empty => emptyT
  | _, .union => unionT
  | _, .power => powerT
  | _, .separate => fun a P => sepT a P
  | _, .replace => fun a F => replT a F

def twinChoice : {A : Ty Unit} → ChoiceSymbol A → TDen A
  | _, .core c => twinSymbol c
  | _, .epsilon => epsT

theorem extensionality_holds : twinModels twinSymbol extensionality := by
  intro a b h z
  exact ⟨(h z).1, (h z).2⟩

theorem empty_holds : twinModels twinSymbol emptyLaw := by
  intro x
  simp only [twinDenote, twinSymbol, member, memT, emptyT]
  exact ZFSet.notMem_empty (encode x)

theorem union_holds : twinModels twinSymbol unionLaw := by
  intro a x
  constructor
  · intro h
    exact mem_unionT.mp h
  · intro h
    exact mem_unionT.mpr h

theorem power_holds : twinModels twinSymbol powerLaw := by
  intro a b
  constructor
  · intro h
    exact mem_powerT.mp h
  · intro h
    exact mem_powerT.mpr h

theorem separation_holds : twinModels twinSymbol separationLaw := by
  intro a P x
  constructor
  · exact mem_sepT.mp
  · exact mem_sepT.mpr

theorem replacement_holds : twinModels twinSymbol replacementLaw := by
  intro a F y
  constructor
  · intro h
    exact mem_replT.mp h
  · intro h
    exact mem_replT.mpr h

theorem induction_holds : twinModels twinSymbol setInduction := by
  intro P step x
  refine twin_induction (P := fun a => (P a).down) ?_ x
  intro a ih
  exact step a ih

theorem choice_holds : twinModels twinChoice choiceLaw := by
  intro P x hx
  exact epsT_spec hx

/-- `∀ a b. eq a b → ∀ P. P a → P b` at `set`, the sets-outside substitution sentence. -/
def substSentence : ClosedFormula Symbol :=
  .all (show Formula Symbol (set :: []) from
    .all (.imp
      (.eq (.var (.vs .vz)) (.var .vz))
      (.all (.imp
        (.app (.var .vz) (.var (.vs (.vs .vz))))
        (.app (.var .vz) (.var (.vs .vz)))))))

/-- `∀ P a b. eq a b → P a → P b` at `set`, the predicate-outside substitution sentence. -/
def substPredicateOutside : ClosedFormula Symbol :=
  .all (show Formula Symbol (predicate :: []) from
    .all (.all (.imp
      (.eq (.var (.vs .vz)) (.var .vz))
      (.imp
        (.app (.var (.vs (.vs .vz))) (.var (.vs .vz)))
        (.app (.var (.vs (.vs .vz))) (.var .vz))))))

theorem subst_fails : ¬ twinModels twinSymbol substSentence := by
  intro h
  unfold twinModels substSentence at h
  dsimp (config := { zeta := true }) only [twinDenote, twinExtend, twinEqv] at h
  have htag :=
    h emptyT markedEmpty same_empty_twins (fun t => .up (t.tag = false)) (by
      simp only [emptyT])
  simp only [markedEmpty] at htag
  cases htag

theorem subst_predicate_outside_fails :
    ¬ twinModels twinSymbol substPredicateOutside := by
  intro h
  unfold twinModels substPredicateOutside at h
  dsimp (config := { zeta := true }) only [twinDenote, twinExtend, twinEqv] at h
  have htag :=
    h (fun t => .up (t.tag = false)) emptyT markedEmpty same_empty_twins (by
      simp only [emptyT])
  simp only [markedEmpty] at htag
  cases htag

def sameLeibniz {Γ : Ctx Unit} (x y : Expr Γ set) : Formula Symbol Γ :=
  .all (.imp (.app (.var .vz) (weaken x)) (.app (.var .vz) (weaken y)))

def included {Γ : Ctx Unit} (x y : Expr Γ set) : Formula Symbol Γ :=
  .all (.imp (member (.var .vz) (weaken x)) (member (.var .vz) (weaken y)))

/-- Two inclusions imply Leibniz `same`. -/
def sameExtSentence : ClosedFormula Symbol :=
  .all (.all (.imp
    (included (.var (.vs .vz)) (.var .vz))
    (.imp
      (included (.var .vz) (.var (.vs .vz)))
      (sameLeibniz (.var (.vs .vz)) (.var .vz)))))

theorem same_ext_fails : ¬ twinModels twinSymbol sameExtSentence := by
  intro h
  unfold twinModels sameExtSentence included sameLeibniz at h
  dsimp (config := { zeta := true }) only [twinDenote, twinSymbol, twinExtend, twinEqv,
    member, weaken, rename, Rename.weaken, memT] at h
  have htag :=
    h emptyT markedEmpty
      (by
        intro z hz
        simp only [emptyT] at hz
        exact (ZFSet.notMem_empty _ hz).elim)
      (by
        intro z hz
        simp only [markedEmpty] at hz
        exact (ZFSet.notMem_empty _ hz).elim)
      (fun t => .up (t.tag = false))
      (by simp only [emptyT])
  simp only [markedEmpty] at htag
  cases htag

/-! ## The four universe laws on the same carrier -/

open ZFSetUniverseClosure ZFSetUniverseInterpretation

theorem zero_lt_of_isSuccLimit {o : Ordinal} (ho : Order.IsSuccLimit o) : (0 : Ordinal) < o := by
  obtain ⟨b, hb⟩ := not_isMin_iff.mp ho.not_isMin
  exact bot_le.trans_lt hb

theorem tagCode_rank_lt {b : Bool} {o : Ordinal} (ho : Order.IsSuccLimit o) :
    (tagCode b).rank < o := by
  cases b
  · simpa only [tagCode, ZFSet.rank_empty] using zero_lt_of_isSuccLimit ho
  · simpa only [tagCode, ZFSet.rank_singleton, ZFSet.rank_empty] using
      ho.succ_lt (zero_lt_of_isSuccLimit ho)

theorem rank_kuratowski_lt {x y : ZFSet.{u}} {o : Ordinal} (ho : Order.IsSuccLimit o)
    (hx : x.rank < o) (hy : y.rank < o) : (ZFSet.pair x y).rank < o := by
  unfold ZFSet.pair
  rw [ZFSet.rank_pair, ZFSet.rank_singleton, ZFSet.rank_pair]
  exact max_lt (ho.succ_lt (ho.succ_lt hx))
    (ho.succ_lt (max_lt (ho.succ_lt hx) (ho.succ_lt hy)))

theorem payload_rank_lt_encode (t : Twin) : t.payload.rank < (encode t).rank :=
  rank_lt_pair_left t.payload (tagCode t.tag)

theorem encode_rank_lt {t : Twin} {o : Ordinal} (ho : Order.IsSuccLimit o)
    (ht : t.payload.rank < o) : (encode t).rank < o :=
  rank_kuratowski_lt ho ht (tagCode_rank_lt ho)

theorem rank_bothEncodes_lt {p : ZFSet.{u}} {o : Ordinal} (ho : Order.IsSuccLimit o)
    (hp : p.rank < o) : (bothEncodes p).rank < o := by
  unfold bothEncodes
  rw [ZFSet.rank_insert, ZFSet.rank_singleton]
  exact max_lt (ho.succ_lt (rank_kuratowski_lt ho hp (tagCode_rank_lt ho)))
    (ho.succ_lt (rank_kuratowski_lt ho hp (tagCode_rank_lt ho)))

theorem image1_eq_range (f : ZFSet.{u} → ZFSet.{u}) (s : ZFSet.{u}) :
    image1 f s = ZFSet.range (fun i : Shrink s => f ((equivShrink s).symm i).1) := by
  apply ZFSet.ext
  intro y
  rw [mem_image1, ZFSet.mem_range]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨equivShrink s ⟨z, hz⟩, ?_⟩
    exact congrArg (fun w : {x // x ∈ s} => f w.1)
      (Equiv.symm_apply_apply (equivShrink s) ⟨z, hz⟩)
  · rintro ⟨i, rfl⟩
    exact ⟨((equivShrink s).symm i).1, ((equivShrink s).symm i).2, rfl⟩

theorem rank_image1 (f : ZFSet.{u} → ZFSet.{u}) (s : ZFSet.{u}) :
    (image1 f s).rank =
      ⨆ i : Shrink s, Order.succ (f ((equivShrink s).symm i).1).rank := by
  rw [image1_eq_range, ZFSet.rank_range]

/-- Codes whose payload lies below `o`, separated from the von Neumann segment. -/
def codeSet (o : Ordinal) : ZFSet.{u} :=
  ZFSet.sep (fun c => ∃ t : Twin, encode t = c ∧ t.payload.rank < o) (ZFSet.vonNeumann o)

theorem hered_codeSet (o : Ordinal) : Hered (codeSet o) := by
  refine Hered.mk (codeSet o) ?_ ?_
  · intro c hc
    obtain ⟨_, hex⟩ := ZFSet.mem_sep.mp hc
    obtain ⟨t, heq, _⟩ := hex
    refine ⟨t.payload, t.tag, ?_⟩
    simpa [encode] using heq.symm
  · intro c hc p b heq
    obtain ⟨_, hex⟩ := ZFSet.mem_sep.mp hc
    obtain ⟨t, henc, _⟩ := hex
    obtain ⟨rfl, _⟩ := ZFSet.pair_inj.mp (henc.trans heq)
    exact t.hered

theorem mem_codeSet {o : Ordinal} (ho : Order.IsSuccLimit o) {t : Twin}
    (ht : t.payload.rank < o) : encode t ∈ codeSet o := by
  refine ZFSet.mem_sep.mpr ⟨ZFSet.mem_vonNeumann.mpr (encode_rank_lt ho ht), ?_⟩
  exact ⟨t, rfl, ht⟩

def enclosure (o : Ordinal) : Twin :=
  ⟨codeSet o, false, hered_codeSet o⟩

theorem payload_rank_lt_of_mem_enclosure {o : Ordinal} {x : Twin}
    (hx : memT x (enclosure o)) : x.payload.rank < o := by
  unfold memT at hx
  dsimp only [enclosure] at hx
  obtain ⟨_, hex⟩ := ZFSet.mem_sep.mp hx
  obtain ⟨t, heq, ht⟩ := hex
  have hpayload : t.payload = x.payload := (ZFSet.pair_inj.mp heq).1
  rw [← hpayload]
  exact ht

theorem unionPayload_rank_lt {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) {a : Twin}
    (ha : a.payload.rank < κ.ord) : (unionPayload a).rank < κ.ord := by
  unfold unionPayload
  apply (ZFSet.rank_sUnion_le _).trans_lt
  rw [rank_image1]
  apply Ordinal.iSup_lt_of_lt_cof
  · rw [hκ.isRegular.cof_ord]
    exact card_lt_of_mem_inaccessible hκ (ZFSet.mem_vonNeumann.mpr ha)
  · intro i
    apply (Cardinal.isSuccLimit_ord hκ.aleph0_lt.le).succ_lt
    have hc : ((equivShrink a.payload).symm i).1 ∈ a.payload :=
      ((equivShrink a.payload).symm i).2
    rw [payloadOf_mem hc]
    have hdec := payload_rank_lt_encode (decode a.hered hc)
    rw [encode_decode a.hered hc] at hdec
    exact (hdec.trans (ZFSet.rank_lt_of_mem hc)).trans ha

theorem powerPayload_rank_lt {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) {a : Twin}
    (ha : a.payload.rank < κ.ord) : (powerPayload a).rank < κ.ord := by
  unfold powerPayload
  apply (ZFSet.rank_sUnion_le _).trans_lt
  rw [rank_image1]
  apply Ordinal.iSup_lt_of_lt_cof
  · rw [hκ.isRegular.cof_ord]
    apply card_lt_of_mem_inaccessible hκ
    rw [ZFSet.mem_vonNeumann, ZFSet.rank_powerset]
    exact (Cardinal.isSuccLimit_ord hκ.aleph0_lt.le).succ_lt ha
  · intro i
    apply (Cardinal.isSuccLimit_ord hκ.aleph0_lt.le).succ_lt
    have hu : ((equivShrink (ZFSet.powerset a.payload)).symm i).1 ∈ ZFSet.powerset a.payload :=
      ((equivShrink (ZFSet.powerset a.payload)).symm i).2
    have hsub : ((equivShrink (ZFSet.powerset a.payload)).symm i).1 ⊆ a.payload :=
      ZFSet.mem_powerset.mp hu
    rw [subsetCodes_subset hsub]
    exact rank_bothEncodes_lt (Cardinal.isSuccLimit_ord hκ.aleph0_lt.le)
      ((ZFSet.rank_mono hsub).trans_lt ha)

theorem replPayload_rank_lt {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) {a : Twin}
    {F : Twin → Twin} (ha : a.payload.rank < κ.ord)
    (hF : ∀ x, memT x a → (F x).payload.rank < κ.ord) : (replPayload a F).rank < κ.ord := by
  unfold replPayload
  apply (ZFSet.rank_sUnion_le _).trans_lt
  rw [rank_image1]
  apply Ordinal.iSup_lt_of_lt_cof
  · rw [hκ.isRegular.cof_ord]
    exact card_lt_of_mem_inaccessible hκ (ZFSet.mem_vonNeumann.mpr ha)
  · intro i
    apply (Cardinal.isSuccLimit_ord hκ.aleph0_lt.le).succ_lt
    have hc : ((equivShrink a.payload).symm i).1 ∈ a.payload :=
      ((equivShrink a.payload).symm i).2
    rw [valueCodes_mem hc]
    apply rank_bothEncodes_lt (Cardinal.isSuccLimit_ord hκ.aleph0_lt.le)
    apply hF
    unfold memT
    rw [encode_decode]
    exact hc

/-- Membership-transitive, and closed under union, power and replacement. -/
structure TwinClosed (U : Twin) : Prop where
  transitive : ∀ x, memT x U → ∀ z, memT z x → memT z U
  union_mem : ∀ a, memT a U → memT (unionT a) U
  power_mem : ∀ a, memT a U → memT (powerT a) U
  repl_mem : ∀ a, memT a U → ∀ F : Twin → Twin,
    (∀ x, memT x a → memT (F x) U) → memT (replT a F) U

theorem enclosure_closed {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    TwinClosed (enclosure κ.ord) where
  transitive x hx z hz := by
    have hxrank := payload_rank_lt_of_mem_enclosure hx
    have hzenc : encode z ∈ x.payload := by
      unfold memT at hz
      exact hz
    have hzrank := (payload_rank_lt_encode z).trans (ZFSet.rank_lt_of_mem hzenc)
    unfold memT enclosure
    exact mem_codeSet (Cardinal.isSuccLimit_ord hκ.aleph0_lt.le) (hzrank.trans hxrank)
  union_mem a ha := by
    have hpayload := unionPayload_rank_lt hκ (payload_rank_lt_of_mem_enclosure ha)
    unfold memT enclosure
    exact mem_codeSet (Cardinal.isSuccLimit_ord hκ.aleph0_lt.le) hpayload
  power_mem a ha := by
    have hpayload := powerPayload_rank_lt hκ (payload_rank_lt_of_mem_enclosure ha)
    unfold memT enclosure
    exact mem_codeSet (Cardinal.isSuccLimit_ord hκ.aleph0_lt.le) hpayload
  repl_mem a ha F hF := by
    have hpayload := replPayload_rank_lt hκ (payload_rank_lt_of_mem_enclosure ha)
      (fun x hx => payload_rank_lt_of_mem_enclosure (hF x hx))
    unfold memT enclosure
    exact mem_codeSet (Cardinal.isSuccLimit_ord hκ.aleph0_lt.le) hpayload

/-- Separate the members that belong to every closed twin containing `N`. -/
def hullT (N bound : Twin) : Twin :=
  sepT bound (fun x => .up (∀ U : Twin, memT N U → TwinClosed U → memT x U))

theorem mem_hullT {N bound x : Twin} :
    memT x (hullT N bound) ↔
      memT x bound ∧ ∀ U : Twin, memT N U → TwinClosed U → memT x U := by
  simpa [hullT] using mem_sepT (a := bound)
    (P := fun x => .up (∀ U : Twin, memT N U → TwinClosed U → memT x U)) (x := x)

theorem contains_hullT {N bound : Twin} (hN : memT N bound) : memT N (hullT N bound) :=
  mem_hullT.mpr ⟨hN, fun _ h _ => h⟩

theorem hullT_minimal {N bound U : Twin} (hN : memT N U) (hU : TwinClosed U) {x : Twin}
    (hx : memT x (hullT N bound)) : memT x U :=
  (mem_hullT.mp hx).2 U hN hU

theorem hullT_closed {N bound : Twin} (hbound : TwinClosed bound) : TwinClosed (hullT N bound) where
  transitive x hx z hz := by
    obtain ⟨hxB, hxAll⟩ := mem_hullT.mp hx
    exact mem_hullT.mpr ⟨hbound.transitive x hxB z hz,
      fun U hN hU => hU.transitive x (hxAll U hN hU) z hz⟩
  union_mem a ha := by
    obtain ⟨haB, haAll⟩ := mem_hullT.mp ha
    exact mem_hullT.mpr ⟨hbound.union_mem a haB,
      fun U hN hU => hU.union_mem a (haAll U hN hU)⟩
  power_mem a ha := by
    obtain ⟨haB, haAll⟩ := mem_hullT.mp ha
    exact mem_hullT.mpr ⟨hbound.power_mem a haB,
      fun U hN hU => hU.power_mem a (haAll U hN hU)⟩
  repl_mem a ha F hF := by
    obtain ⟨haB, haAll⟩ := mem_hullT.mp ha
    refine mem_hullT.mpr ⟨hbound.repl_mem a haB F ?_, ?_⟩
    · intro x hx
      exact (mem_hullT.mp (hF x hx)).1
    · intro U hN hU
      exact hU.repl_mem a (haAll U hN hU) F
        (fun x hx => (mem_hullT.mp (hF x hx)).2 U hN hU)

noncomputable def chosenInaccessible (h : CofinalInaccessibles.{u}) (N : Twin) : Cardinal.{u} :=
  Classical.choose (h (encode N).rank)

theorem chosenInaccessible_spec (h : CofinalInaccessibles.{u}) (N : Twin) :
    (chosenInaccessible h N).IsInaccessible ∧
      (encode N).rank < (chosenInaccessible h N).ord :=
  Classical.choose_spec (h (encode N).rank)

def enclosureOf (h : CofinalInaccessibles.{u}) (N : Twin) : Twin :=
  enclosure (chosenInaccessible h N).ord

theorem mem_enclosureOf (h : CofinalInaccessibles.{u}) (N : Twin) :
    memT N (enclosureOf h N) := by
  have hspec := chosenInaccessible_spec h N
  unfold memT enclosureOf enclosure
  exact mem_codeSet (Cardinal.isSuccLimit_ord hspec.1.aleph0_lt.le)
    ((payload_rank_lt_encode N).trans hspec.2)

theorem enclosureOf_closed (h : CofinalInaccessibles.{u}) (N : Twin) :
    TwinClosed (enclosureOf h N) :=
  enclosure_closed (chosenInaccessible_spec h N).1

def univT (h : CofinalInaccessibles.{u}) (N : Twin) : Twin :=
  hullT N (enclosureOf h N)

theorem mem_univT (h : CofinalInaccessibles.{u}) (N : Twin) : memT N (univT h N) :=
  contains_hullT (mem_enclosureOf h N)

theorem univT_closed (h : CofinalInaccessibles.{u}) (N : Twin) : TwinClosed (univT h N) :=
  hullT_closed (enclosureOf_closed h N)

theorem univT_minimal (h : CofinalInaccessibles.{u}) {N U : Twin} (hN : memT N U)
    (hU : TwinClosed U) {x : Twin} (hx : memT x (univT h N)) : memT x U :=
  hullT_minimal hN hU hx

def twinUniverse (h : CofinalInaccessibles.{u}) :
    {A : Ty Unit} → UniverseSymbol A → TDen A
  | _, .core c => twinSymbol c
  | _, .universe => univT h

theorem universeIn_holds (h : CofinalInaccessibles.{u}) :
    twinModels (twinUniverse h) universeIn := by
  intro N
  exact mem_univT h N

theorem universeTransitive_holds (h : CofinalInaccessibles.{u}) :
    twinModels (twinUniverse h) universeTransitive := by
  intro N
  exact (univT_closed h N).transitive

theorem universeClosed_holds (h : CofinalInaccessibles.{u}) :
    twinModels (twinUniverse h) universeClosed := by
  intro N
  have hU := univT_closed h N
  exact ⟨hU.union_mem, hU.power_mem, hU.repl_mem⟩

theorem universeMinimal_holds (h : CofinalInaccessibles.{u}) :
    twinModels (twinUniverse h) universeMinimal := by
  intro N U hN ht hc z hz
  exact univT_minimal h hN ⟨ht, hc.1, hc.2.1, hc.2.2⟩ hz

end

end TwinExtensional
end MegalodonHOTG
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
