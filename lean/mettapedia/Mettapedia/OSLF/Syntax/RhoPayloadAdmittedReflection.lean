import Mettapedia.OSLF.Syntax.RhoPayloadExecutorComparison
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParameterizedRewriteSystem

/-!
# Scope-preserving reflection of the payload rho presentation

Reflection selects communication partners from the original process's parallel
inventory. Both the selected redex and its reduct therefore satisfy the
executor's quotation-aware admission judgment. Structural congruence alone
would not establish quotation safety for an arbitrary representative.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoPayloadPresentation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern rhoReflectivePresentation)
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence

theorem safe_of_mem_flatAtoms (quote : String) (depth : Nat) :
    (∀ p : Pattern, binderSafeAt quote depth p = true →
      ∀ e ∈ flatAtoms p, binderSafeAt quote depth e = true) ∧
    (∀ ps : List Pattern, binderSafeListAt quote depth ps = true →
      ∀ e ∈ flatAtomsList ps, binderSafeAt quote depth e = true) := by
  refine flatAtoms.mutual_induct
    (fun p => binderSafeAt quote depth p = true →
      ∀ e ∈ flatAtoms p, binderSafeAt quote depth e = true)
    (fun ps => binderSafeListAt quote depth ps = true →
      ∀ e ∈ flatAtomsList ps, binderSafeAt quote depth e = true)
    ?_ ?_ ?_ ?_ ?_
  · intro elements ih safe e member
    rw [flatAtoms.eq_1] at member
    exact ih safe e member
  · intro _ e member
    rw [flatAtoms.eq_2] at member
    cases member
  · intro p hbag hzero safe e member
    rw [flatAtoms.eq_3 p hbag hzero] at member
    rw [List.mem_singleton.mp member]
    exact safe
  · intro _ e member
    cases member
  · intro p ps ihp ihps safe e member
    have pair : binderSafeAt quote depth p = true ∧
        binderSafeListAt quote depth ps = true := by
      simpa only [binderSafeListAt, Bool.and_eq_true] using safe
    rw [flatAtomsList.eq_2] at member
    rcases List.mem_append.mp member with member | member
    · exact ihp pair.1 e member
    · exact ihps pair.2 e member

private theorem typed_list {free : FreeSortContext} {bound : List String}
    (ps : List Pattern)
    (typed : ∀ p ∈ ps, ProcWellSorted rhoReflectivePresentation free bound p) :
    ProcListWellSorted rhoReflectivePresentation free bound ps := by
  induction ps with
  | nil => exact .nil
  | cons p ps ih =>
      exact .cons (typed p List.mem_cons_self)
        (ih (fun q member => typed q (List.mem_cons_of_mem p member)))

/-- Reflection retains admitted representatives of both endpoints, with the
actual authored communication between them. -/
theorem comm_reflection_admitted {free : FreeSortContext} {P : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] P)
    (safe : binderSafeAt "NQuote" 0 P = true)
    {s₀ : Term sig [] Srt.pr} (hs : tProc (Env.empty []) P = some s₀)
    {u : Term sig [] Srt.pr} (c : Term sig [] Srt.nm) (q : Term sig [] Srt.pr)
    (K : Term sig [Srt.pr] Srt.pr) (others : Multiset (Cls [] Srt.pr))
    (hsrc : atoms s₀ = cls (outT c q) ::ₘ cls (inpT c K) ::ₘ others)
    (htgt : atoms u = atoms (inst K q) + others) :
    ∃ redex contractum : ParameterizedRewriteSystem.Process free,
      StructuralCongruence P redex.1 ∧ RhoStep redex.1 contractum.1 ∧
        ∃ t, tProc (Env.empty []) contractum.1 = some t ∧ cls t = cls u := by
  have hρ : VarEnv (Env.empty ([] : Ctx sig)) := VarEnv.empty
  obtain ⟨L, hLfst, hLtr, hLatoms⟩ := (translate_flatAtoms hρ).1 P s₀ hs
  rw [hLatoms] at hsrc
  obtain ⟨xo, xi, L', hperm, hxo, hxi, hL'⟩ := extract_two L (fun x => cls x.2) hsrc
  have memo : xo ∈ L := hperm.symm.subset List.mem_cons_self
  have memi : xi ∈ L := hperm.symm.subset (List.mem_cons_of_mem _ List.mem_cons_self)
  have memL' : ∀ x ∈ L', x ∈ L := fun x hx =>
    hperm.symm.subset (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
  have inFlat : ∀ x ∈ L, x.1 ∈ flatAtoms P := fun x hx => by
    rw [← hLfst]
    exact List.mem_map_of_mem hx
  have atomAt : ∀ x ∈ L, IsAtom x.1 := fun x hx =>
    isAtom_of_mem_flatAtoms.1 P x.1 (inFlat x hx)
  have typedAt : ∀ x ∈ L, ProcWellSorted rhoReflectivePresentation free [] x.1 := fun x hx =>
    typed_of_mem_flatAtoms.1 P typed x.1 (inFlat x hx)
  have safeAt : ∀ x ∈ L, binderSafeAt "NQuote" 0 x.1 = true := fun x hx =>
    (safe_of_mem_flatAtoms "NQuote" 0).1 P safe x.1 (inFlat x hx)
  obtain ⟨chO, pl, cO, q', hxo1, hcO, hq', ecO, eq'⟩ :=
    output_of_cls hρ (atomAt xo memo) (hLtr xo memo) hxo
  obtain ⟨chI, body, cI, K', hxi1, hcI, hK', ecI, eK'⟩ :=
    input_of_cls hρ (atomAt xi memi) (hLtr xi memi) hxi
  have channels : StructuralCongruence chO chI :=
    sc_of_tName_cls hρ hcO hcI (ecO.trans ecI.symm)
  have outTyped := typedAt xo memo
  rw [hxo1] at outTyped
  obtain ⟨_, payloadTyped⟩ := rho_output_wellSorted_inv outTyped
  have inTyped := typedAt xi memi
  rw [hxi1] at inTyped
  obtain ⟨_, channelTyped, bodyTyped⟩ := rho_input_wellSorted_inv inTyped
  have inSafe := safeAt xi memi
  rw [hxi1] at inSafe
  have inputSafety : binderSafeAt "NQuote" 0 chI = true ∧
      binderSafeAt "NQuote" 1 body = true := by
    simpa [binderSafeAt, binderSafeListAt] using inSafe
  have outSafe := safeAt xo memo
  rw [hxo1] at outSafe
  have outputSafety : binderSafeAt "NQuote" 0 chO = true ∧
      binderSafeAt "NQuote" 0 pl = true := by
    simpa [binderSafeAt, binderSafeListAt] using outSafe
  let rest := L'.map Prod.fst
  have restTyped : ProcListWellSorted rhoReflectivePresentation free [] rest :=
    typed_list rest (by
      intro p member
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp member
      exact typedAt x (memL' x hx))
  have restSafe : binderSafeListAt "NQuote" 0 rest = true := by
    apply (binderSafeListAt_eq_true_iff "NQuote" 0 rest).mpr
    intro p member
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp member
    exact safeAt x (memL' x hx)
  let redexPattern := Pattern.collection .hashBag
    ([.apply "PInput" [chI, .lambda none body], .apply "POutput" [chI, pl]] ++ rest) none
  have redexTyped : ProcWellSorted rhoReflectivePresentation free [] redexPattern :=
    .parallel (.cons (.input channelTyped bodyTyped)
      (.cons (.output channelTyped payloadTyped) restTyped))
  have redexSafe : binderSafeAt "NQuote" 0 redexPattern = true := by
    simp [redexPattern, binderSafeAt, binderSafeListAt,
      inputSafety.1, inputSafety.2, outputSafety.2, restSafe]
  let redex : ParameterizedRewriteSystem.Process free :=
    ⟨redexPattern, (ParameterizedRewriteSystem.process_iff _ _).mpr ⟨redexTyped, redexSafe⟩⟩
  have firing := RhoStep.comm_resolved chI body pl rest bodyTyped payloadTyped
  let contractum := ParameterizedRewriteSystem.stepTarget redex firing
  refine ⟨redex, contractum, ?_, firing, ?_⟩
  · have flat := sc_flatAtoms.1 P
    rw [← hLfst] at flat
    refine flat.trans _ _ _ ?_
    refine (StructuralCongruence.par_perm _ _ (hperm.map Prod.fst)).trans _ _ _ ?_
    refine (StructuralCongruence.par_perm _ _ (List.Perm.swap _ _ _)).trans _ _ _ ?_
    change StructuralCongruence (.collection .hashBag (xi.1 :: xo.1 :: rest) none) _
    rw [hxo1, hxi1]
    exact sc_second rest (sc_apply2 _ channels (.refl pl))
  · obtain ⟨K'', hK'', eK''⟩ := translate_resolveQuotes _ body K' hK'
    obtain ⟨T, hT, eT⟩ := translate_semanticCommSubst hK'' hq'
    obtain ⟨R, hR, hRatoms⟩ := tProcs_atoms hρ L' (fun x hx => hLtr x (memL' x hx))
      (fun x hx => atomAt x (memL' x hx))
    refine ⟨parT T R, ?_, ?_⟩
    · change tProc (Env.empty []) (.collection .hashBag
          (semanticCommSubst (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.resolveQuotes rhoReflectivePresentation body) pl :: rest) none) = _
      rw [tProc.eq_5, tProcs.eq_2, hT, Option.bind_some, hR, Option.map_some]
    · apply cls_eq_of_atoms_eq
      change atoms T + atoms R = atoms u
      rw [atoms_invariant (eT.trans (inst_equiv (eK''.trans (cls_eq_iff.mp eK'))
          (cls_eq_iff.mp eq'))), hRatoms, hL', htgt]

theorem strict_reflection_admitted {free : FreeSortContext} {P : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] P)
    (safe : binderSafeAt "NQuote" 0 P = true)
    {s₀ : Term sig [] Srt.pr} (hs : tProc (Env.empty []) P = some s₀)
    {u : Term sig [] Srt.pr} (step : Steps strictRules s₀ u) :
    ∃ redex contractum : ParameterizedRewriteSystem.Process free,
      StructuralCongruence P redex.1 ∧ RhoStep redex.1 contractum.1 ∧
        ∃ t, tProc (Env.empty []) contractum.1 = some t ∧ cls t = cls u := by
  rcases steps_inversion (rest := []) (.inl rfl) step with
    ⟨c, q, K, others, hsrc, htgt⟩ | ⟨hne, _⟩
  · exact comm_reflection_admitted typed safe hs c q K others hsrc htgt
  · exact absurd hne (by simp)

end Mettapedia.OSLF.Binding.RhoPayloadPresentation
