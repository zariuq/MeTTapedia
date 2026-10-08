import Mettapedia.TypeTheory.ContextualLogicalMorphism

/-!
# Contextual type presentations carrying an external mark

Marks are supplied presentation data retained by substitution. Decoding
forgets only that data, preserving the actual family and every supplied
term. Products and sums retain the domain mark. This produces a noninjective
logical family map with genuinely varying domains and codomains.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualMarkedTypes

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualTypeOperations ContextualSumComprehension ContextualLogicalMorphism

universe u v w w'

def marked (C : Cwf.{u, v, w, w'}) : Cwf.{u, v, w, w'} where
  Ctx := C.Ctx
  Sub := C.Sub
  idS := C.idS
  compS := C.compS
  id_comp := C.id_comp
  comp_id := C.comp_id
  comp_assoc := C.comp_assoc
  Ty Γ := C.Ty Γ × Bool
  tySub A σ := ⟨C.tySub A.1 σ, A.2⟩
  tySub_id A := Prod.ext (C.tySub_id A.1) rfl
  tySub_comp A σ τ := Prod.ext (C.tySub_comp A.1 σ τ) rfl
  Tm Γ A := C.Tm Γ A.1
  tmSub a σ := C.tmSub a σ
  tmSub_id a := C.tmSub_id a
  tmSub_comp a σ τ := C.tmSub_comp a σ τ
  ext Γ A := C.ext Γ A.1
  wk A := C.wk A.1
  vz A := C.vz A.1
  pair σ A a := C.pair σ A.1 a
  wk_pair σ A a := C.wk_pair σ A.1 a
  vz_pair σ A a := C.vz_pair σ A.1 a
  pair_eta A σ := C.pair_eta A.1 σ

def withTerminal (C : CwfWithTerminal.{u, v, w, w'}) : CwfWithTerminal.{u, v, w, w'} where
  toCwf := marked C.toCwf
  empty := C.empty
  toEmpty := C.toEmpty
  toEmpty_unique := C.toEmpty_unique

def familyDecoder (C : Cwf.{u, v, w, w'}) : CwfFamilyMorphism (marked C) C where
  base := 𝟭 C.base.Context
  family := {
    app := fun _ => {
      onIndex := Prod.fst
      onFibre := fun _ a => a }
    naturality := by intro Γ Δ σ; rfl }

def decoder (C : CwfWithTerminal.{u, v, w, w'}) : StrictCwfMorphism (withTerminal C) C where
  toFamilyMorphism := familyDecoder C.toCwf
  empty_preserved := rfl
  extension_preserved := fun _ _ => rfl
  projection_preserved := by
    intro Γ A
    change C.toCwf.wk A.1 = C.toCwf.compS (C.toCwf.wk A.1) (C.toCwf.idS _)
    exact (C.toCwf.comp_id _).symm
  variable_preserved := by
    intro Γ A
    change HEq (C.toCwf.vz A.1) (C.toCwf.tmSub (C.toCwf.vz A.1) (C.toCwf.idS _))
    exact ((heq_of_eq (C.toCwf.tmSub_id _)).trans (cast_heq _ _)).symm

theorem selfExtend_eq {C : Cwf.{u, v, w, w'}} {Γ : C.Ctx}
    {A : (marked C).Ty Γ} (a : (marked C).Tm Γ A) :
    ContextualProductComparison.selfExtend (marked C) a =
      ContextualProductComparison.selfExtend C a := by
  unfold ContextualProductComparison.selfExtend
  apply congrArg (C.pair (C.idS Γ) A.1)
  exact eq_of_heq ((ContextualComprehensionMorphism.transport_heq _ a).trans
    (ContextualComprehensionMorphism.transport_heq (C.tySub_id A.1).symm a).symm)

theorem lift_eq {C : Cwf.{u, v, w, w'}} {Γ Δ : C.Ctx}
    (σ : C.Sub Γ Δ) (A : (marked C).Ty Δ) :
    TypeOver.extensionSubstitution (C := marked C) σ A =
      TypeOver.extensionSubstitution σ A.1 := by
  unfold TypeOver.extensionSubstitution
  apply congrArg (C.pair (C.compS σ (C.wk (C.tySub A.1 σ))) A.1)
  exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _).symm)

def products {C : Cwf.{u, v, w, w'}} (original : PiOperations C) : PiOperations (marked C) where
  pi A B := ⟨original.pi A.1 B.1, A.2⟩
  lam b := original.lam b
  app := fun {Γ} {A} {B} f a =>
    cast (congrArg (C.Tm Γ) (congrArg (C.tySub B.1) (selfExtend_eq (A := A) a).symm))
      (original.app f a)

def sums {C : Cwf.{u, v, w, w'}} (original : SigmaOperations C) : SigmaOperations (marked C) where
  sigma A B := ⟨original.sigma A.1 B.1, A.2⟩
  pair := fun {Γ} {A} {B} a b => original.pair a
    (cast (congrArg (C.Tm Γ) (congrArg (C.tySub B.1) (selfExtend_eq (A := A) a))) b)
  fst p := original.fst p
  snd := fun {Γ} {A} {B} p =>
    cast (congrArg (C.Tm Γ) (congrArg (C.tySub B.1) (selfExtend_eq (A := A) (original.fst p)).symm))
      (original.snd p)

theorem products_application_heq {C : Cwf.{u, v, w, w'}} (original : PiOperations C)
    {Γ : C.Ctx} {A : (marked C).Ty Γ} {B : (marked C).Ty ((marked C).ext Γ A)}
    (f : (marked C).Tm Γ ((products original).pi A B)) (a : (marked C).Tm Γ A) :
    HEq ((products original).app f a) (original.app f a) := cast_heq _ _

theorem sums_pairing_heq {C : Cwf.{u, v, w, w'}} (original : SigmaOperations C)
    {Γ : C.Ctx} {A : (marked C).Ty Γ} {B : (marked C).Ty ((marked C).ext Γ A)}
    (a : (marked C).Tm Γ A)
    (b : (marked C).Tm Γ ((marked C).tySub B (ContextualProductComparison.selfExtend (marked C) a))) :
    HEq ((sums original).pair a b)
      (original.pair a (cast (congrArg (C.Tm Γ) (congrArg (C.tySub B.1) (selfExtend_eq a))) b)) := HEq.rfl

theorem sums_second_heq {C : Cwf.{u, v, w, w'}} (original : SigmaOperations C)
    {Γ : C.Ctx} {A : (marked C).Ty Γ} {B : (marked C).Ty ((marked C).ext Γ A)}
    (p : (marked C).Tm Γ ((sums original).sigma A B)) :
    HEq ((sums original).snd p) (original.snd p) := cast_heq _ _

/-- Decoding compares every local product constructor on its actual
supplied sections, including alternative presentations of image types. -/
theorem products_preserved (C : CwfWithTerminal.{u, v, w, w'})
    (original : PiOperations C.toCwf) :
    PiPreservation (decoder C) (products original) original := by
  constructor
  · intro Γ Γ' contexts A A' domains B B' codomains
    change Γ = Γ' at contexts
    cases contexts
    change HEq A.1 A' at domains
    cases eq_of_heq domains
    change HEq B.1 B' at codomains
    cases eq_of_heq codomains
    rfl
  · intro Γ Γ' contexts A A' domains B B' codomains b b' bodies
    change Γ = Γ' at contexts
    cases contexts
    change HEq A.1 A' at domains
    cases eq_of_heq domains
    change HEq B.1 B' at codomains
    cases eq_of_heq codomains
    change HEq b b' at bodies
    cases eq_of_heq bodies
    rfl
  · intro Γ Γ' contexts A A' domains B B' codomains f f' a a' functions arguments
    change Γ = Γ' at contexts
    cases contexts
    change HEq A.1 A' at domains
    cases eq_of_heq domains
    change HEq B.1 B' at codomains
    cases eq_of_heq codomains
    change HEq f f' at functions
    cases eq_of_heq functions
    change HEq a a' at arguments
    cases eq_of_heq arguments
    exact products_application_heq original f a

theorem sums_preserved (C : CwfWithTerminal.{u, v, w, w'})
    (original : SigmaOperations C.toCwf) :
    SigmaPreservation (decoder C) (sums original) original := by
  constructor
  · intro Γ Γ' contexts A A' domains B B' codomains
    change Γ = Γ' at contexts
    cases contexts
    change HEq A.1 A' at domains
    cases eq_of_heq domains
    change HEq B.1 B' at codomains
    cases eq_of_heq codomains
    rfl
  · intro Γ Γ' contexts A A' domains B B' codomains a a' b b' firsts seconds
    change Γ = Γ' at contexts
    cases contexts
    change HEq A.1 A' at domains
    cases eq_of_heq domains
    change HEq B.1 B' at codomains
    cases eq_of_heq codomains
    change HEq a a' at firsts
    cases eq_of_heq firsts
    have body : cast (congrArg (C.toCwf.Tm Γ)
        (congrArg (C.toCwf.tySub B.1) (selfExtend_eq (A := A) a))) b = b' :=
      eq_of_heq ((cast_heq _ _).trans seconds)
    exact (sums_pairing_heq original a b).trans
      (heq_of_eq (congrArg (fun value => original.pair (codomain := B.1) a value) body))
  · intro Γ Γ' contexts A A' domains B B' codomains p p' pairs
    change Γ = Γ' at contexts
    cases contexts
    change HEq A.1 A' at domains
    cases eq_of_heq domains
    change HEq B.1 B' at codomains
    cases eq_of_heq codomains
    change HEq p p' at pairs
    cases eq_of_heq pairs
    rfl
  · intro Γ Γ' contexts A A' domains B B' codomains p p' pairs
    change Γ = Γ' at contexts
    cases contexts
    change HEq A.1 A' at domains
    cases eq_of_heq domains
    change HEq B.1 B' at codomains
    cases eq_of_heq codomains
    change HEq p p' at pairs
    cases eq_of_heq pairs
    exact sums_second_heq original p

end Mettapedia.TypeTheory.ContextualMarkedTypes
