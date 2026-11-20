import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.DataEmbedding

/-! # Constructor inversion of the lossless native term encoding at its actual ambient scope -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.TermViews

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage.Elaboration

theorem pi_of_code {ambient : Nat} {domain body : MClosed} {term : Tower.Tm ambient}
    (encoded : nodeC "prime-tm-pi" [domain, body] = encodeTm term) :
    ∃ domainTerm bodyTerm, term = .pi domainTerm bodyTerm ∧ domain = encodeTm domainTerm ∧ body = encodeTm bodyTerm := by
  cases term <;> simp_all [DataEmbedding.nodeC_eq_iff]

theorem sigma_of_code {ambient : Nat} {domain body : MClosed} {term : Tower.Tm ambient}
    (encoded : nodeC "prime-tm-sigma" [domain, body] = encodeTm term) :
    ∃ domainTerm bodyTerm, term = .sigma domainTerm bodyTerm ∧ domain = encodeTm domainTerm ∧ body = encodeTm bodyTerm := by
  cases term <;> simp_all [DataEmbedding.nodeC_eq_iff]

theorem lam_of_code {ambient : Nat} {body : MClosed} {term : Tower.Tm ambient}
    (encoded : nodeC "prime-tm-lam" [body] = encodeTm term) :
    ∃ bodyTerm, term = .lam bodyTerm ∧ body = encodeTm bodyTerm := by
  cases term <;> simp_all [DataEmbedding.nodeC_eq_iff]

theorem pair_of_code {ambient : Nat} {left right : MClosed} {term : Tower.Tm ambient}
    (encoded : nodeC "prime-tm-pair" [left, right] = encodeTm term) :
    ∃ first second, term = .pair first second ∧ left = encodeTm first ∧ right = encodeTm second := by
  cases term <;> simp_all [DataEmbedding.nodeC_eq_iff]

theorem fst_of_code {ambient : Nat} {body : MClosed} {term : Tower.Tm ambient}
    (encoded : nodeC "prime-tm-fst" [body] = encodeTm term) :
    ∃ subject, term = .fst subject ∧ body = encodeTm subject := by
  cases term <;> simp_all [DataEmbedding.nodeC_eq_iff]

theorem snd_of_code {ambient : Nat} {body : MClosed} {term : Tower.Tm ambient}
    (encoded : nodeC "prime-tm-snd" [body] = encodeTm term) :
    ∃ subject, term = .snd subject ∧ body = encodeTm subject := by
  cases term <;> simp_all [DataEmbedding.nodeC_eq_iff]

theorem id_of_code {ambient : Nat} {carrier left right : MClosed} {term : Tower.Tm ambient}
    (encoded : nodeC "prime-tm-id" [carrier, left, right] = encodeTm term) :
    ∃ type a b, term = .id type a b ∧ carrier = encodeTm type ∧ left = encodeTm a ∧ right = encodeTm b := by
  cases term <;> simp_all [DataEmbedding.nodeC_eq_iff]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.TermViews
