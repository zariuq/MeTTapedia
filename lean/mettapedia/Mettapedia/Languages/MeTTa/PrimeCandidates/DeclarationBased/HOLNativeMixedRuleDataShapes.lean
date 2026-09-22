import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedRuleDataCompleteness
import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-!
# Reconstructing native source shapes from actual rule matches

Canonical term encoding is injective. Consequently a successful match of an
authored computation root reconstructs its native source shape, including
the equalities of repeated carrier and endpoint parameters.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedRuleData

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open DeclarationAwarePatternCodec DeclarationAwareSubstitutionLanguage
open Presentation NativeIndexedFamilies

theorem encoded_injective (n : Nat) : Function.Injective (@encoded n) :=
  (tmCodec towerHeadCodec n).encode_injective

theorem encoded_app_inversion {n : Nat} {source : Tower.Tm n} {a b : Pattern}
    (equation : encoded source = tmApp a b) :
    ∃ f x, source = .app f x ∧ encoded f = a ∧ encoded x = b := by
  cases source <;> simp_all [encoded, encodeTm, tmApp]

theorem encoded_lam_inversion {n : Nat} {source : Tower.Tm n} {body : Pattern}
    (equation : encoded source = tmLam body) :
    ∃ term, source = .lam term ∧ encoded term = body := by
  cases source <;> simp_all [encoded, encodeTm, tmLam]

theorem encoded_pi_inversion {n : Nat} {source : Tower.Tm n} {a b : Pattern}
    (equation : encoded source = tmPi a b) :
    ∃ domain body, source = .pi domain body ∧ encoded domain = a ∧ encoded body = b := by
  cases source <;> simp_all [encoded, encodeTm, tmPi]

theorem encoded_sigma_inversion {n : Nat} {source : Tower.Tm n} {a b : Pattern}
    (equation : encoded source = tmSigma a b) :
    ∃ domain body, source = .sigma domain body ∧ encoded domain = a ∧ encoded body = b := by
  cases source <;> simp_all [encoded, encodeTm, tmSigma]

theorem encoded_id_inversion {n : Nat} {source : Tower.Tm n} {a b c : Pattern}
    (equation : encoded source = tmId a b c) :
    ∃ type left right, source = .id type left right ∧
      encoded type = a ∧ encoded left = b ∧ encoded right = c := by
  cases source <;> simp_all [encoded, encodeTm, tmId]

theorem encoded_pair_inversion {n : Nat} {source : Tower.Tm n} {a b : Pattern}
    (equation : encoded source = tmPair a b) :
    ∃ x y, source = .pair x y ∧ encoded x = a ∧ encoded y = b := by
  cases source <;> simp_all [encoded, encodeTm, tmPair]

theorem encoded_fst_inversion {n : Nat} {source : Tower.Tm n} {pair : Pattern}
    (equation : encoded source = tmFst pair) :
    ∃ term, source = .fst term ∧ encoded term = pair := by
  cases source <;> simp_all [encoded, encodeTm, tmFst]

theorem encoded_snd_inversion {n : Nat} {source : Tower.Tm n} {pair : Pattern}
    (equation : encoded source = tmSnd pair) :
    ∃ term, source = .snd term ∧ encoded term = pair := by
  cases source <;> simp_all [encoded, encodeTm, tmSnd]

theorem encoded_refl_inversion {n : Nat} {source : Tower.Tm n} {term : Pattern}
    (equation : encoded source = tmRefl term) :
    ∃ value, source = .refl value ∧ encoded value = term := by
  cases source <;> simp_all [encoded, encodeTm, tmRefl]

theorem encoded_const_inversion {n : Nat} {source : Tower.Tm n} {name : Lean.Name}
    (equation : encoded source = constant name) : source = .const name :=
  encoded_injective n equation

theorem same_encoded_output {n : Nat} {first second : Tower.Tm n} {output : Pattern}
    (left : encoded first = output) (right : encoded second = output) : first = second :=
  encoded_injective n (left.trans right.symm)

theorem matched_source_reconstruction {n : Nat} (source : Tower.Tm n)
    (name : String) (input output : Pattern) (premises : List Premise)
    (bindings : Bindings)
    (matched : bindings ∈ matchPatternForRule language
      (computationRule name input output premises) (compute (encoded source)))
    (correct : Mettapedia.OSLF.MeTTaIL.Match.Pattern.isMatchCorrect (compute input) = true) :
    encoded source = Mettapedia.OSLF.MeTTaIL.Match.applyBindings bindings input := by
  rw [matchPatternForRule_eq_syntactic] at matched
  have same := matchPattern_correct matched correct
  simpa only [computationRule, compute, Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
    List.map_cons, List.map_nil,
    Pattern.apply.injEq, List.cons.injEq, and_true, true_and] using same.symm

macro "unfold_native_match" " at " hypothesis:ident : tactic =>
  `(tactic| simp only [apps, listEliminate, nil, cons, identityEliminate,
      relEliminate, nilRel, consRel, proof, implication, universal,
      List.foldl_cons, List.foldl_nil, tmApp, tmPi, tmLam, tmId,
      tmPair, tmFst, tmSnd, tmRefl, constant, tmConst, m,
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings, List.map_cons, List.map_nil,
      applyBindings_encodeDeclName] at $hypothesis:ident)

macro "native_match_correct" : tactic =>
  `(tactic| simp only [compute, apps, listEliminate, nil, cons, identityEliminate,
      relEliminate, nilRel, consRel, proof, implication, universal,
      List.foldl_cons, List.foldl_nil, tmApp, tmPi, tmLam, tmId,
      tmPair, tmFst, tmSnd, tmRefl, constant, tmConst, m,
      Mettapedia.OSLF.MeTTaIL.Match.Pattern.isMatchCorrect,
      isMatchCorrectAux, isMatchCorrectListAux, isMatchCorrectAux_encodeDeclName,
      Bool.and_self])

theorem beta_match_shape {n : Nat} (source : Tower.Tm n) (bindings : Bindings)
    (matched : bindings ∈ matchPatternForRule language betaRule (compute (encoded source))) :
    ∃ body argument, source = .app (.lam body) argument := by
  have equation := matched_source_reconstruction source _ _ _ _ bindings matched (by native_match_correct)
  simp only [tmApp, tmLam, m, Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
    List.map_cons, List.map_nil] at equation
  obtain ⟨function, argument, rfl, functionEq, _⟩ := encoded_app_inversion equation
  obtain ⟨body, rfl, _⟩ := encoded_lam_inversion functionEq
  exact ⟨body, argument, rfl⟩

theorem first_match_shape {n : Nat} (source : Tower.Tm n) (bindings : Bindings)
    (matched : bindings ∈ matchPatternForRule language firstRule (compute (encoded source))) :
    ∃ a b, source = .fst (.pair a b) := by
  have equation := matched_source_reconstruction source _ _ _ _ bindings matched (by native_match_correct)
  unfold_native_match at equation
  obtain ⟨pair, rfl, pairEq⟩ := encoded_fst_inversion equation
  obtain ⟨a, b, rfl, _, _⟩ := encoded_pair_inversion pairEq
  exact ⟨a, b, rfl⟩

theorem second_match_shape {n : Nat} (source : Tower.Tm n) (bindings : Bindings)
    (matched : bindings ∈ matchPatternForRule language secondRule (compute (encoded source))) :
    ∃ a b, source = .snd (.pair a b) := by
  have equation := matched_source_reconstruction source _ _ _ _ bindings matched (by native_match_correct)
  unfold_native_match at equation
  obtain ⟨pair, rfl, pairEq⟩ := encoded_snd_inversion equation
  obtain ⟨a, b, rfl, _, _⟩ := encoded_pair_inversion pairEq
  exact ⟨a, b, rfl⟩

theorem listNil_match_shape {n : Nat} (source : Tower.Tm n) (bindings : Bindings)
    (matched : bindings ∈ matchPatternForRule language listNilRule (compute (encoded source))) :
    ∃ a p z s, source = Intrinsic.eliminateApp a p z s (Intrinsic.nilApp a) := by
  have equation := matched_source_reconstruction source _ _ _ _ bindings matched (by native_match_correct)
  unfold_native_match at equation
  obtain ⟨f₄, xs, rfl, f₄Eq, xsEq⟩ := encoded_app_inversion equation
  obtain ⟨f₃, s, rfl, f₃Eq, _⟩ := encoded_app_inversion f₄Eq
  obtain ⟨f₂, z, rfl, f₂Eq, _⟩ := encoded_app_inversion f₃Eq
  obtain ⟨f₁, p, rfl, f₁Eq, _⟩ := encoded_app_inversion f₂Eq
  obtain ⟨f₀, a, rfl, f₀Eq, aEq⟩ := encoded_app_inversion f₁Eq
  have functionEq := encoded_const_inversion f₀Eq
  subst f₀
  obtain ⟨nilSymbol, innerA, rfl, nilEq, innerAEq⟩ := encoded_app_inversion xsEq
  have symbolEq := encoded_const_inversion nilEq
  subst nilSymbol
  have duplicate := same_encoded_output innerAEq aEq
  subst innerA
  exact ⟨a, p, z, s, rfl⟩

theorem listCons_match_shape {n : Nat} (source : Tower.Tm n) (bindings : Bindings)
    (matched : bindings ∈ matchPatternForRule language listConsRule (compute (encoded source))) :
    ∃ a p z s h t, source = Intrinsic.eliminateApp a p z s (Intrinsic.consApp a h t) := by
  have equation := matched_source_reconstruction source _ _ _ _ bindings matched (by native_match_correct)
  unfold_native_match at equation
  obtain ⟨f₄, xs, rfl, f₄Eq, xsEq⟩ := encoded_app_inversion equation
  obtain ⟨f₃, s, rfl, f₃Eq, _⟩ := encoded_app_inversion f₄Eq
  obtain ⟨f₂, z, rfl, f₂Eq, _⟩ := encoded_app_inversion f₃Eq
  obtain ⟨f₁, p, rfl, f₁Eq, _⟩ := encoded_app_inversion f₂Eq
  obtain ⟨f₀, a, rfl, f₀Eq, aEq⟩ := encoded_app_inversion f₁Eq
  have functionEq := encoded_const_inversion f₀Eq
  subst f₀
  obtain ⟨c₂, t, rfl, c₂Eq, _⟩ := encoded_app_inversion xsEq
  obtain ⟨c₁, h, rfl, c₁Eq, _⟩ := encoded_app_inversion c₂Eq
  obtain ⟨symbol, innerA, rfl, symbolEq, innerAEq⟩ := encoded_app_inversion c₁Eq
  have symbolIsCons := encoded_const_inversion symbolEq
  subst symbol
  have duplicate := same_encoded_output innerAEq aEq
  subst innerA
  exact ⟨a, p, z, s, h, t, rfl⟩

theorem identity_match_shape {n : Nat} (source : Tower.Tm n) (bindings : Bindings)
    (matched : bindings ∈ matchPatternForRule language identityRule (compute (encoded source))) :
    ∃ a x p d, source = Intrinsic.identityEliminateApp a x p d x (.refl x) := by
  have equation := matched_source_reconstruction source _ _ _ _ bindings matched (by native_match_correct)
  unfold_native_match at equation
  obtain ⟨f₅, evidence, rfl, f₅Eq, evidenceEq⟩ := encoded_app_inversion equation
  obtain ⟨f₄, y, rfl, f₄Eq, yEq⟩ := encoded_app_inversion f₅Eq
  obtain ⟨f₃, d, rfl, f₃Eq, _⟩ := encoded_app_inversion f₄Eq
  obtain ⟨f₂, p, rfl, f₂Eq, _⟩ := encoded_app_inversion f₃Eq
  obtain ⟨f₁, x, rfl, f₁Eq, xEq⟩ := encoded_app_inversion f₂Eq
  obtain ⟨f₀, a, rfl, f₀Eq, _⟩ := encoded_app_inversion f₁Eq
  have functionEq := encoded_const_inversion f₀Eq
  subst f₀
  obtain ⟨witness, rfl, witnessEq⟩ := encoded_refl_inversion evidenceEq
  have endpoint := same_encoded_output yEq xEq
  have reflexivity := same_encoded_output witnessEq xEq
  subst y
  subst witness
  exact ⟨a, x, p, d, rfl⟩

theorem relNil_match_shape {n : Nat} (source : Tower.Tm n) (bindings : Bindings)
    (matched : bindings ∈ matchPatternForRule language relNilRule (compute (encoded source))) :
    ∃ a b r p z s, source = IntrinsicRelator.eliminateApp a b r p z s
      (Intrinsic.nilApp a) (Intrinsic.nilApp b) (IntrinsicRelator.nilRelApp a b r) := by
  have equation := matched_source_reconstruction source _ _ _ _ bindings matched (by native_match_correct)
  unfold_native_match at equation
  obtain ⟨f₈, evidence, rfl, f₈Eq, evidenceEq⟩ := encoded_app_inversion equation
  obtain ⟨f₇, ys, rfl, f₇Eq, ysEq⟩ := encoded_app_inversion f₈Eq
  obtain ⟨f₆, xs, rfl, f₆Eq, xsEq⟩ := encoded_app_inversion f₇Eq
  obtain ⟨f₅, s, rfl, f₅Eq, _⟩ := encoded_app_inversion f₆Eq
  obtain ⟨f₄, z, rfl, f₄Eq, _⟩ := encoded_app_inversion f₅Eq
  obtain ⟨f₃, p, rfl, f₃Eq, _⟩ := encoded_app_inversion f₄Eq
  obtain ⟨f₂, r, rfl, f₂Eq, rEq⟩ := encoded_app_inversion f₃Eq
  obtain ⟨f₁, b, rfl, f₁Eq, bEq⟩ := encoded_app_inversion f₂Eq
  obtain ⟨f₀, a, rfl, f₀Eq, aEq⟩ := encoded_app_inversion f₁Eq
  have functionEq := encoded_const_inversion f₀Eq
  subst f₀
  obtain ⟨c₀, a₁, rfl, c₀Eq, a₁Eq⟩ := encoded_app_inversion xsEq
  obtain ⟨d₀, b₁, rfl, d₀Eq, b₁Eq⟩ := encoded_app_inversion ysEq
  have cEq := encoded_const_inversion c₀Eq
  have dEq := encoded_const_inversion d₀Eq
  subst c₀
  subst d₀
  obtain ⟨e₂, r₁, rfl, e₂Eq, r₁Eq⟩ := encoded_app_inversion evidenceEq
  obtain ⟨e₁, b₂, rfl, e₁Eq, b₂Eq⟩ := encoded_app_inversion e₂Eq
  obtain ⟨e₀, a₂, rfl, e₀Eq, a₂Eq⟩ := encoded_app_inversion e₁Eq
  have eEq := encoded_const_inversion e₀Eq
  subst e₀
  have aa := same_encoded_output a₁Eq aEq
  have aaa := same_encoded_output a₂Eq aEq
  have bb := same_encoded_output b₁Eq bEq
  have bbb := same_encoded_output b₂Eq bEq
  have rr := same_encoded_output r₁Eq rEq
  subst a₁
  subst a₂
  subst b₁
  subst b₂
  subst r₁
  exact ⟨a, b, r, p, z, s, rfl⟩

theorem relCons_match_shape {n : Nat} (source : Tower.Tm n) (bindings : Bindings)
    (matched : bindings ∈ matchPatternForRule language relConsRule (compute (encoded source))) :
    ∃ a b r p z s h k t u he te, source = IntrinsicRelator.eliminateApp a b r p z s
      (Intrinsic.consApp a h t) (Intrinsic.consApp b k u)
      (IntrinsicRelator.consRelApp a b r h k t u he te) := by
  have equation := matched_source_reconstruction source _ _ _ _ bindings matched (by native_match_correct)
  unfold_native_match at equation
  obtain ⟨f₈, evidence, rfl, f₈Eq, evidenceEq⟩ := encoded_app_inversion equation
  obtain ⟨f₇, ys, rfl, f₇Eq, ysEq⟩ := encoded_app_inversion f₈Eq
  obtain ⟨f₆, xs, rfl, f₆Eq, xsEq⟩ := encoded_app_inversion f₇Eq
  obtain ⟨f₅, s, rfl, f₅Eq, _⟩ := encoded_app_inversion f₆Eq
  obtain ⟨f₄, z, rfl, f₄Eq, _⟩ := encoded_app_inversion f₅Eq
  obtain ⟨f₃, p, rfl, f₃Eq, _⟩ := encoded_app_inversion f₄Eq
  obtain ⟨f₂, r, rfl, f₂Eq, rEq⟩ := encoded_app_inversion f₃Eq
  obtain ⟨f₁, b, rfl, f₁Eq, bEq⟩ := encoded_app_inversion f₂Eq
  obtain ⟨f₀, a, rfl, f₀Eq, aEq⟩ := encoded_app_inversion f₁Eq
  have functionEq := encoded_const_inversion f₀Eq
  subst f₀
  obtain ⟨c₂, t, rfl, c₂Eq, tEq⟩ := encoded_app_inversion xsEq
  obtain ⟨c₁, h, rfl, c₁Eq, hEq⟩ := encoded_app_inversion c₂Eq
  obtain ⟨c₀, a₁, rfl, c₀Eq, a₁Eq⟩ := encoded_app_inversion c₁Eq
  obtain ⟨d₂, u, rfl, d₂Eq, uEq⟩ := encoded_app_inversion ysEq
  obtain ⟨d₁, k, rfl, d₁Eq, kEq⟩ := encoded_app_inversion d₂Eq
  obtain ⟨d₀, b₁, rfl, d₀Eq, b₁Eq⟩ := encoded_app_inversion d₁Eq
  have cEq := encoded_const_inversion c₀Eq
  have dEq := encoded_const_inversion d₀Eq
  subst c₀
  subst d₀
  obtain ⟨e₈, te, rfl, e₈Eq, _⟩ := encoded_app_inversion evidenceEq
  obtain ⟨e₇, he, rfl, e₇Eq, _⟩ := encoded_app_inversion e₈Eq
  obtain ⟨e₆, u₁, rfl, e₆Eq, u₁Eq⟩ := encoded_app_inversion e₇Eq
  obtain ⟨e₅, t₁, rfl, e₅Eq, t₁Eq⟩ := encoded_app_inversion e₆Eq
  obtain ⟨e₄, k₁, rfl, e₄Eq, k₁Eq⟩ := encoded_app_inversion e₅Eq
  obtain ⟨e₃, h₁, rfl, e₃Eq, h₁Eq⟩ := encoded_app_inversion e₄Eq
  obtain ⟨e₂, r₁, rfl, e₂Eq, r₁Eq⟩ := encoded_app_inversion e₃Eq
  obtain ⟨e₁, b₂, rfl, e₁Eq, b₂Eq⟩ := encoded_app_inversion e₂Eq
  obtain ⟨e₀, a₂, rfl, e₀Eq, a₂Eq⟩ := encoded_app_inversion e₁Eq
  have eEq := encoded_const_inversion e₀Eq
  subst e₀
  have aa := same_encoded_output a₁Eq aEq
  have aaa := same_encoded_output a₂Eq aEq
  have bb := same_encoded_output b₁Eq bEq
  have bbb := same_encoded_output b₂Eq bEq
  have rr := same_encoded_output r₁Eq rEq
  have hh := same_encoded_output h₁Eq hEq
  have kk := same_encoded_output k₁Eq kEq
  have tt := same_encoded_output t₁Eq tEq
  have uu := same_encoded_output u₁Eq uEq
  subst a₁
  subst a₂
  subst b₁
  subst b₂
  subst r₁
  subst h₁
  subst k₁
  subst t₁
  subst u₁
  exact ⟨a, b, r, p, z, s, h, k, t, u, he, te, rfl⟩

theorem implication_match_shape {n : Nat} (source : Tower.Tm n) (bindings : Bindings)
    (matched : bindings ∈ matchPatternForRule language implicationRule (compute (encoded source))) :
    ∃ p q, source = FormationSensitiveHOLProofFamily.proof
      (FormationSensitiveHOLUniformList.rawImp p q) := by
  have equation := matched_source_reconstruction source _ _ _ _ bindings matched (by native_match_correct)
  unfold_native_match at equation
  obtain ⟨proofSymbol, body, rfl, proofEq, bodyEq⟩ := encoded_app_inversion equation
  have prfEq := encoded_const_inversion proofEq
  subst proofSymbol
  obtain ⟨f, q, rfl, fEq, _⟩ := encoded_app_inversion bodyEq
  obtain ⟨symbol, p, rfl, symbolEq, _⟩ := encoded_app_inversion fEq
  have impEq := encoded_const_inversion symbolEq
  subst symbol
  exact ⟨p, q, rfl⟩

theorem universal_match_shape {n : Nat} (source : Tower.Tm n) (bindings : Bindings)
    (matched : bindings ∈ matchPatternForRule language universalRule (compute (encoded source))) :
    ∃ a f, source = FormationSensitiveHOLProofFamily.proof
      (FormationSensitiveHOLProofFamily.universalProposition a f) := by
  have equation := matched_source_reconstruction source _ _ _ _ bindings matched (by native_match_correct)
  unfold_native_match at equation
  obtain ⟨proofSymbol, body, rfl, proofEq, bodyEq⟩ := encoded_app_inversion equation
  have prfEq := encoded_const_inversion proofEq
  subst proofSymbol
  obtain ⟨applied, f, rfl, appliedEq, _⟩ := encoded_app_inversion bodyEq
  obtain ⟨symbol, a, rfl, symbolEq, _⟩ := encoded_app_inversion appliedEq
  have allEq := encoded_const_inversion symbolEq
  subst symbol
  exact ⟨a, f, rfl⟩

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedRuleData
