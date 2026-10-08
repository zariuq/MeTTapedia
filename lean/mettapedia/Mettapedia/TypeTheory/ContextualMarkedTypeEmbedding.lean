import Mettapedia.TypeTheory.ContextualMarkedTypes

/-!
# Supplied constant marks as a logical contextual embedding

A chosen external mark is attached to every type presentation and retained
by actual substitution. The underlying family and supplied sections are
unchanged. Local product and sum preservation follows from the explicit
marked constructors, including their genuine annotation transports.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualMarkedTypes

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualTypeOperations ContextualSumComprehension ContextualLogicalMorphism

universe u v w w'

def familyEmbedding (C : Cwf.{u, v, w, w'}) (mark : Bool) :
    CwfFamilyMorphism C (marked C) where
  base := 𝟭 C.base.Context
  family := {
    app := fun _ => {
      onIndex := fun A => ⟨A, mark⟩
      onFibre := fun _ a => a }
    naturality := by intro Γ Δ σ; rfl }

def embedding (C : CwfWithTerminal.{u, v, w, w'}) (mark : Bool) :
    StrictCwfMorphism C (withTerminal C) where
  toFamilyMorphism := familyEmbedding C.toCwf mark
  empty_preserved := rfl
  extension_preserved := fun _ _ => rfl
  projection_preserved := by
    intro Γ A
    change C.toCwf.wk A = C.toCwf.compS (C.toCwf.wk A) (C.toCwf.idS _)
    exact (C.toCwf.comp_id _).symm
  variable_preserved := by
    intro Γ A
    change HEq (C.toCwf.vz A) (C.toCwf.tmSub (C.toCwf.vz A) (C.toCwf.idS _))
    exact ((heq_of_eq (C.toCwf.tmSub_id _)).trans (cast_heq _ _)).symm

theorem products_embedding_preserved (C : CwfWithTerminal.{u, v, w, w'})
    (mark : Bool) (original : PiOperations C.toCwf) :
    PiPreservation (embedding C mark) original (products original) := by
  constructor
  · intro Γ Γ' contexts A A' domains B B' codomains
    change Γ = Γ' at contexts
    cases contexts
    change HEq (A, mark) A' at domains
    cases eq_of_heq domains
    change HEq (B, mark) B' at codomains
    cases eq_of_heq codomains
    rfl
  · intro Γ Γ' contexts A A' domains B B' codomains b b' bodies
    change Γ = Γ' at contexts
    cases contexts
    change HEq (A, mark) A' at domains
    cases eq_of_heq domains
    change HEq (B, mark) B' at codomains
    cases eq_of_heq codomains
    change HEq b b' at bodies
    cases eq_of_heq bodies
    rfl
  · intro Γ Γ' contexts A A' domains B B' codomains f f' a a' functions arguments
    change Γ = Γ' at contexts
    cases contexts
    change HEq (A, mark) A' at domains
    cases eq_of_heq domains
    change HEq (B, mark) B' at codomains
    cases eq_of_heq codomains
    change HEq f f' at functions
    cases eq_of_heq functions
    change HEq a a' at arguments
    cases eq_of_heq arguments
    exact (products_application_heq original (A := (A, mark)) (B := (B, mark)) f a).symm

theorem sums_embedding_preserved (C : CwfWithTerminal.{u, v, w, w'})
    (mark : Bool) (original : SigmaOperations C.toCwf) :
    SigmaPreservation (embedding C mark) original (sums original) := by
  constructor
  · intro Γ Γ' contexts A A' domains B B' codomains
    change Γ = Γ' at contexts
    cases contexts
    change HEq (A, mark) A' at domains
    cases eq_of_heq domains
    change HEq (B, mark) B' at codomains
    cases eq_of_heq codomains
    rfl
  · intro Γ Γ' contexts A A' domains B B' codomains a a' b b' firsts seconds
    change Γ = Γ' at contexts
    cases contexts
    change HEq (A, mark) A' at domains
    cases eq_of_heq domains
    change HEq (B, mark) B' at codomains
    cases eq_of_heq codomains
    change HEq a a' at firsts
    cases eq_of_heq firsts
    change HEq b b' at seconds
    have body : cast (congrArg (C.toCwf.Tm Γ)
        (congrArg (C.toCwf.tySub B) (selfExtend_eq (A := (A, mark)) a))) b' = b :=
      eq_of_heq ((cast_heq _ _).trans seconds.symm)
    exact (heq_of_eq (congrArg (fun value => original.pair (codomain := B) a value) body)).symm.trans
      (sums_pairing_heq original (A := (A, mark)) (B := (B, mark)) a b').symm
  · intro Γ Γ' contexts A A' domains B B' codomains p p' pairs
    change Γ = Γ' at contexts
    cases contexts
    change HEq (A, mark) A' at domains
    cases eq_of_heq domains
    change HEq (B, mark) B' at codomains
    cases eq_of_heq codomains
    change HEq p p' at pairs
    cases eq_of_heq pairs
    rfl
  · intro Γ Γ' contexts A A' domains B B' codomains p p' pairs
    change Γ = Γ' at contexts
    cases contexts
    change HEq (A, mark) A' at domains
    cases eq_of_heq domains
    change HEq (B, mark) B' at codomains
    cases eq_of_heq codomains
    change HEq p p' at pairs
    cases eq_of_heq pairs
    exact (sums_second_heq original (A := (A, mark)) (B := (B, mark)) p).symm

end Mettapedia.TypeTheory.ContextualMarkedTypes
