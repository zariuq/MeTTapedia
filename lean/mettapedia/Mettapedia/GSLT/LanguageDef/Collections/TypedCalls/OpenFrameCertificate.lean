import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OpenFrameSourceAdmission

/-!
# Executable source certificates for open captured frames

The certificate checks the actual Expr grammar, declared-symbol exclusion,
return-to-argument syntax, and finite source effect support. Success derives
the syntactic premises of the existing recursive source/protocol theorem.
It does not accept a whole-run equality as evidence.

The source fragment is explicit: uninterpreted construction, unary active
recursion, two-way let binding, conditionals and failure. Case, match,
external calls and other existing Expr forms remain declined here, even
where the separate return-position scan can recognize their tail syntax.
The native contract analyzer uses a different fact representation; its
correspondence and hidden resource support remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OpenFrameCertificate

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open UnifyingRegions

mutual
/-- The declared-symbol test underlying uninterpreted first-order data. -/
def cleanAtom (Γ : Decls) : Atom → Bool
  | .symbol name => (Γ name).isEmpty
  | .expression values => cleanAtoms Γ values
  | _ => true

def cleanAtoms (Γ : Decls) : List Atom → Bool
  | [] => true
  | value :: values => cleanAtom Γ value && cleanAtoms Γ values
end

mutual
theorem cleanAtom_sound (Γ : Decls) : ∀ value,
    cleanAtom Γ value = true → Uninterp Γ value
  | .symbol _, h => List.isEmpty_iff.mp h
  | .var _, _ => trivial
  | .grounded _, _ => trivial
  | .expression values, h => UnifyAtoms.uninterp_of_all (cleanAtoms_sound Γ values h)

theorem cleanAtoms_sound (Γ : Decls) : ∀ values,
    cleanAtoms Γ values = true → ∀ value ∈ values, Uninterp Γ value
  | [], _, _, h => by cases h
  | first :: rest, h, value, member => by
      have checks := Bool.and_eq_true_iff.mp h
      have head := cleanAtom_sound Γ first checks.1
      have tail := cleanAtoms_sound Γ rest checks.2
      rcases List.mem_cons.mp member with same | member
      · simpa only [same] using head
      · exact tail value member
end

mutual
theorem cleanAtom_complete (Γ : Decls) : ∀ value,
    Uninterp Γ value → cleanAtom Γ value = true
  | .symbol _, h => List.isEmpty_iff.mpr h
  | .var _, _ => rfl
  | .grounded _, _ => rfl
  | .expression values, h => cleanAtoms_complete Γ values (UnifyAtoms.safeAll_of_uninterp h)

theorem cleanAtoms_complete (Γ : Decls) : ∀ values,
    SafeAll Γ Atom.var values → cleanAtoms Γ values = true
  | [], _ => rfl
  | first :: rest, h => by
      rw [cleanAtoms, cleanAtom_complete Γ first h.1, cleanAtoms_complete Γ rest h.2]
      rfl
end

mutual
/-- This recognizer follows the supported source grammar. Unsupported calls
are refused before evaluation; they are not interpreted as empty answers. -/
def accepted (Γ : Decls) : Expr → Bool
  | .var _ => true
  | .const value => cleanAtom Γ value
  | .ctor head args => (Γ head).isEmpty && acceptedAll Γ args
  | .self [arg] => accepted Γ arg
  | .letE pattern value body => cleanAtom Γ pattern.toAtom && accepted Γ value && accepted Γ body
  | .ifE condition yes no => accepted Γ condition && accepted Γ yes && accepted Γ no
  | .empty => true
  | _ => false

def acceptedAll (Γ : Decls) : List Expr → Bool
  | [] => true
  | first :: rest => accepted Γ first && acceptedAll Γ rest
end

mutual
theorem accepted_sound (Γ : Decls) : ∀ e,
    accepted Γ e = true → UnifyingRegions.Accepted Γ e
  | .var x, _ => .var x
  | .const value, h => .const value (cleanAtom_sound Γ value h)
  | .ctor head args, h => by
      have checks := Bool.and_eq_true_iff.mp h
      exact .ctor (List.isEmpty_iff.mp checks.1) (acceptedAll_sound Γ args checks.2)
  | .self [], h => by simp [accepted] at h
  | .self [arg], h => .self (accepted_sound Γ arg h)
  | .self (_ :: _ :: _), h => by simp [accepted] at h
  | .letE pattern value body, h => by
      have checks : (cleanAtom Γ pattern.toAtom = true ∧ accepted Γ value = true) ∧
          accepted Γ body = true := by simpa only [accepted, Bool.and_eq_true] using h
      exact .letE (cleanAtom_sound Γ pattern.toAtom checks.1.1)
        (accepted_sound Γ value checks.1.2) (accepted_sound Γ body checks.2)
  | .ifE condition yes no, h => by
      have checks : (accepted Γ condition = true ∧ accepted Γ yes = true) ∧
          accepted Γ no = true := by simpa only [accepted, Bool.and_eq_true] using h
      exact .ifE (accepted_sound Γ condition checks.1.1)
        (accepted_sound Γ yes checks.1.2) (accepted_sound Γ no checks.2)
  | .empty, _ => .empty
  | .prim _ _, h => by simp [accepted] at h
  | .call _ _, h => by simp [accepted] at h
  | .enter _ _, h => by simp [accepted] at h
  | .caseE _ _ _, h => by simp [accepted] at h
  | .matchE _ _ _, h => by simp [accepted] at h

theorem acceptedAll_sound (Γ : Decls) : ∀ es,
    acceptedAll Γ es = true → ∀ e ∈ es, UnifyingRegions.Accepted Γ e
  | [], _, _, h => by cases h
  | first :: rest, h, e, member => by
      have checks := Bool.and_eq_true_iff.mp h
      have head := accepted_sound Γ first checks.1
      have tail := acceptedAll_sound Γ rest checks.2
      rcases List.mem_cons.mp member with same | member
      · simpa only [same] using head
      · exact tail e member
end

theorem acceptedAll_iff (Γ : Decls) : ∀ es,
    acceptedAll Γ es = true ↔ ∀ e ∈ es, accepted Γ e = true
  | [] => by simp [acceptedAll]
  | e :: es => by simp [acceptedAll, acceptedAll_iff Γ es]

theorem accepted_complete {Γ : Decls} {e : Expr}
    (admitted : UnifyingRegions.Accepted Γ e) : accepted Γ e = true := by
  induction admitted with
  | var => rfl
  | const value clean => exact cleanAtom_complete Γ value clean
  | ctor head parts ih =>
      simp only [accepted, head, List.isEmpty_nil, Bool.true_and]
      exact (acceptedAll_iff Γ _).mpr ih
  | self _ ih => exact ih
  | letE pattern _ _ ihValue ihBody =>
      simp only [accepted, cleanAtom_complete Γ _ pattern, ihValue, ihBody, Bool.and_true]
  | ifE _ _ _ ihCondition ihYes ihNo => simp [accepted, ihCondition, ihYes, ihNo]
  | empty => rfl

theorem accepted_iff (Γ : Decls) (e : Expr) :
    accepted Γ e = true ↔ UnifyingRegions.Accepted Γ e :=
  ⟨accepted_sound Γ e, accepted_complete⟩

mutual
/-- Return-position analysis does not inspect the value or condition paths.
Those paths are checked separately by the source admission recognizer. -/
def returnsArgument (parameter : String) : Expr → Bool
  | .var name => name == parameter
  | .letE _ _ body => returnsArgument parameter body
  | .ifE _ yes no => returnsArgument parameter yes && returnsArgument parameter no
  | .empty => true
  | .caseE _ _ bodies => returnsAll parameter bodies
  | .matchE _ _ body => returnsArgument parameter body
  | _ => false

def returnsAll (parameter : String) : List Expr → Bool
  | [] => true
  | first :: rest => returnsArgument parameter first && returnsAll parameter rest
end

mutual
theorem returnsArgument_sound (parameter : String) : ∀ e,
    returnsArgument parameter e = true → ReturnsPat (.var parameter) e
  | .var name, h => by
      have same : name = parameter := by simpa only [returnsArgument, beq_iff_eq] using h
      subst name
      exact .refl
  | .letE _ _ body, h => .letE (returnsArgument_sound parameter body h)
  | .ifE _ yes no, h => by
      have checks := Bool.and_eq_true_iff.mp h
      exact .ifE (returnsArgument_sound parameter yes checks.1)
        (returnsArgument_sound parameter no checks.2)
  | .empty, _ => .empty
  | .caseE _ _ bodies, h => .caseE (returnsAll_sound parameter bodies h)
  | .matchE _ _ body, h => .matchE (returnsArgument_sound parameter body h)
  | .const _, h => by simp [returnsArgument] at h
  | .ctor _ _, h => by simp [returnsArgument] at h
  | .self _, h => by simp [returnsArgument] at h
  | .prim _ _, h => by simp [returnsArgument] at h
  | .call _ _, h => by simp [returnsArgument] at h
  | .enter _ _, h => by simp [returnsArgument] at h

theorem returnsAll_sound (parameter : String) : ∀ es,
    returnsAll parameter es = true → ∀ e ∈ es, ReturnsPat (.var parameter) e
  | [], _, _, h => by cases h
  | first :: rest, h, e, member => by
      have checks := Bool.and_eq_true_iff.mp h
      have head := returnsArgument_sound parameter first checks.1
      have tail := returnsAll_sound parameter rest checks.2
      rcases List.mem_cons.mp member with same | member
      · simpa only [same] using head
      · exact tail e member
end

theorem returnsAll_iff (parameter : String) : ∀ es,
    returnsAll parameter es = true ↔ ∀ e ∈ es, returnsArgument parameter e = true
  | [] => by simp [returnsAll]
  | e :: es => by simp [returnsAll, returnsAll_iff parameter es]

theorem returnsArgument_complete {parameter : String} {e : Expr}
    (returns : ReturnsPat (.var parameter) e) : returnsArgument parameter e = true := by
  induction returns with
  | refl => simp [returnsArgument]
  | letE _ ih => exact ih
  | ifE _ _ ihYes ihNo => simp [returnsArgument, ihYes, ihNo]
  | empty => rfl
  | caseE _ ih => exact (returnsAll_iff parameter _).mpr ih
  | matchE _ ih => exact ih

theorem returnsArgument_iff (parameter : String) (e : Expr) :
    returnsArgument parameter e = true ↔ ReturnsPat (.var parameter) e :=
  ⟨returnsArgument_sound parameter e, returnsArgument_complete⟩

def certificate (Γ : Decls) (parameter : String) (scope : Finset String) (e : Expr) : Bool :=
  decide (parameter ∈ scope) && accepted Γ e && OpenFrameEffects.check scope e &&
    returnsArgument parameter e

theorem certificate_sound {Γ : Decls} {parameter : String} {scope : Finset String} {e : Expr}
    (certified : certificate Γ parameter scope e = true) :
    parameter ∈ scope ∧ UnifyingRegions.Accepted Γ e ∧
      OpenFrameEffects.check scope e = true ∧ ReturnsPat (.var parameter) e := by
  have checks : ((parameter ∈ scope ∧ accepted Γ e = true) ∧
      OpenFrameEffects.check scope e = true) ∧ returnsArgument parameter e = true := by
    simpa only [certificate, Bool.and_eq_true, decide_eq_true_eq] using certified
  exact ⟨checks.1.1.1, accepted_sound Γ e checks.1.1.2,
    checks.1.2, returnsArgument_sound parameter e checks.2⟩

/-- All source premises are earned by one executable certificate. Only the
ordinary typed entry and the input's current-support gate remain at runtime. -/
theorem certified_source_eq_protocol {Γ : Decls} {parameter : String} {scope : Finset String}
    (grounded : String → Bool) (fallback : Fallback) (typeVariable : String)
    (pre post : List (Ty Empty)) {e : Expr}
    (certified : certificate Γ parameter scope e = true) (fuel : Nat) (args : List Atom)
    (allowed : OpenFrameSourceAdmission.Admitted Γ grounded pre post scope args) :
    protocolRun Γ grounded (CapturedUninterpretedRegions.sourceBody fallback parameter e pre.length)
        (arrow (pre.map Ty.lift ++ .var typeVariable :: post.map Ty.lift) (.var typeVariable)) fuel args =
      versionRun (CapturedUninterpretedRegions.sourceBody fallback parameter e pre.length) fuel args := by
  obtain ⟨inside, admitted, checked, returns⟩ := certificate_sound certified
  exact OpenFrameSourceAdmission.source_version_eq_protocol grounded fallback parameter typeVariable
    inside pre post admitted checked returns fuel args allowed

theorem certified_offer_eq_protocol {Γ : Decls} {parameter : String} {scope : Finset String}
    (grounded : String → Bool) (fallback : Fallback) (typeVariable : String)
    (pre post : List (Ty Empty)) {e : Expr}
    (certified : certificate Γ parameter scope e = true) (fuel : Nat)
    (input : CapturedUninterpretedRegions.CheckedInput Γ grounded pre post) :
    OpenFrameSourceAdmission.offeredRun Γ grounded fallback parameter typeVariable pre post scope
        e fuel input =
      protocolRun Γ grounded (CapturedUninterpretedRegions.sourceBody fallback parameter e pre.length)
        (arrow (pre.map Ty.lift ++ .var typeVariable :: post.map Ty.lift) (.var typeVariable)) fuel input.args := by
  obtain ⟨inside, admitted, checked, returns⟩ := certificate_sound certified
  exact OpenFrameSourceAdmission.offeredRun_eq_protocol grounded fallback parameter typeVariable
    inside pre post admitted checked returns fuel input

namespace Controls

open OpenFrameSourceAdmission.Controls

theorem recursive_open_source_certified : certificate declarations "argument" scope program = true := by
  decide +kernel

theorem recursive_open_source_all_fuels (grounded : String → Bool) (fuel : Nat) :
    protocolRun declarations grounded (CapturedUninterpretedRegions.sourceBody fallback "argument" program 1)
        (arrow [tagged.lift, .var "t", tagged.lift] (.var "t")) fuel [.var "open", input, known] =
      versionRun (CapturedUninterpretedRegions.sourceBody fallback "argument" program 1)
        fuel [.var "open", input, known] :=
  certified_source_eq_protocol grounded fallback "t" [tagged] [tagged]
    recursive_open_source_certified fuel _ ⟨open_entry grounded, open_gate_passes⟩

theorem wrong_return_refused : certificate declarations "argument" scope (.const one) = false := by
  decide +kernel

theorem interpreted_pattern_refused :
    certificate declarations "argument" scope
      (.letE (.ctor "Known" []) (.var "argument") (.var "argument")) = false := by decide +kernel

def unsupportedMatch : Expr := .matchE (.var "argument") (.var "ignored") (.var "argument")

/-- Return syntax by itself proves no operational admission for a host query. -/
theorem recognized_return_does_not_admit_match :
    returnsArgument "argument" unsupportedMatch = true ∧
      certificate declarations "argument" scope unsupportedMatch = false := by decide +kernel

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OpenFrameCertificate
