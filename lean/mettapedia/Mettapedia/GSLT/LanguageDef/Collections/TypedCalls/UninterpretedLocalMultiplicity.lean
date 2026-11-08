import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.UninterpretedVersions
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.RefinedUninterpreted

/-!
# Local multiplicity of uninterpreted values

Unrelated overloaded declarations cannot affect an uninterpreted value: none
of the value's symbol leaves has a declaration. Its typing record agrees with
the empty-signature record, even when the actual space is not functional.
The empty signature is used only as a proved comparison on this footprint;
the closed frame guards continue to use the actual declaration space.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.UninterpretedLocalMultiplicity

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

def emptyDecls : Decls := fun _ => []

theorem empty_functional : Functional emptyDecls := fun _ => by simp [emptyDecls]

theorem empty_headFree (value : Atom) : HeadFree emptyDecls value := by cases value <;> trivial

mutual
theorem empty_safe (theta : String → Atom) : ∀ value : Atom, Safe emptyDecls theta value
  | .symbol _ => rfl
  | .var _ => trivial
  | .grounded _ => trivial
  | .expression [] => trivial
  | .expression (head :: tail) =>
      ⟨empty_headFree _, empty_safe theta head, empty_safeAll theta tail⟩

theorem empty_safeAll (theta : String → Atom) : ∀ values : List Atom, SafeAll emptyDecls theta values
  | [] => trivial
  | value :: values => ⟨empty_safe theta value, empty_safeAll theta values⟩
end

mutual
/-- The complete typing record, not merely an existence test, is independent
of declarations outside an uninterpreted value's footprint. -/
theorem info_eq_empty {Γ : Decls} : ∀ value : Atom, Uninterp Γ value → info Γ value = info emptyDecls value
  | .symbol name, clean => by
      change Γ name = [] at clean
      simp only [info_symbol, clean, emptyDecls]
  | .var _, _ => rfl
  | .grounded g, _ => by cases g <;> rfl
  | .expression values, clean => by
      rw [info_expression, info_expression,
        infoAll_eq_empty values (UnifyAtoms.safeAll_of_uninterp clean)]

theorem infoAll_eq_empty {Γ : Decls} : ∀ values : List Atom, SafeAll Γ Atom.var values →
    values.map (info Γ) = values.map (info emptyDecls)
  | [], _ => rfl
  | value :: values, clean => by
      simp only [List.map_cons, info_eq_empty value clean.1, infoAll_eq_empty values clean.2]
end

/-- Exactly one effective derivation follows from the observed value's own
uninterpreted structure, with no global single-row requirement. -/
theorem card_eff_uninterpreted {Γ : Decls} {value : Atom} (clean : Uninterp Γ value) :
    Multiset.card (eff (info Γ value)) = 1 := by
  rw [info_eq_empty value clean]
  exact card_eff empty_functional value

theorem struct_clean {Γ : Decls} (theta : String → Atom) (value : Atom)
    (substitution : ∀ x, Uninterp Γ (theta x)) (clean : Uninterp Γ value) :
    Struct Γ value (substA theta value) := by
  have reference := struct_of_safe empty_functional theta value (empty_safe theta value)
  unfold Struct at reference ⊢
  rw [info_eq_empty value clean,
    info_eq_empty (substA theta value) (uninterp_substA substitution value clean)]
  exact reference

/-- The result guard reads only the returned uninterpreted instance. Closed
frame guards and their actual multiplicities are not replaced. -/
theorem pair_result_once_clean {Γ : Decls} (kind : Atom → String)
    {a : String} {k m : Nat} (different : k ≠ m)
    {theta : String → Atom} {value : Atom} (clean : Uninterp Γ value)
    (substitution : ∀ x, Uninterp Γ (theta x)) {dv : Deriv}
    (typed : eff (info Γ value) = {dv})
    {opened closed : List (Eqn CallVar)} (stores : PairStores dv.ty a k m opened closed)
    (satisfiable : Sat closed) :
    resultGuard Γ kind m (.var a) opened (substA theta value) = {substA theta value} := by
  have before : eff (info emptyDecls value) = {dv} := by
    rw [← info_eq_empty value clean]
    exact typed
  have reference := pair_result_once empty_functional kind different
    (empty_safe theta value) before stores satisfiable
  unfold resultGuard at reference ⊢
  rw [info_eq_empty (substA theta value) (uninterp_substA substitution value clean)]
  exact reference

/-- The clean-instance row protocol needs only the actual closed-argument
counts. Unrelated overloaded heads are permitted. -/
theorem pair_protocol_clean {Γ : Decls} (kind : Atom → String)
    (pre post : List (Ty Empty)) (a : String) (body : List Atom → Multiset Atom)
    (us ws : List Atom) (value : Atom) (len : pre.length = us.length) (clean : Uninterp Γ value)
    (instances : ∀ r ∈ body (us ++ value :: ws),
      ∃ theta : String → Atom, r = substA theta value ∧ ∀ x, Uninterp Γ (theta x)) :
    chainCall Γ kind body (arrow (pre.map Ty.lift ++ .var a :: post.map Ty.lift) (.var a))
        (us ++ value :: ws) =
      (argCount Γ kind pre us * argCount Γ kind post ws) • body (us ++ value :: ws) := by
  obtain ⟨dv, _, hdv, _, hdve, _⟩ := struct_clean Atom.var value (fun _ => trivial) clean
  unfold chainCall
  rw [arrowSplit_arrow]
  dsimp only
  rw [guards_append _ 0 _ _ _ _ _ (by simpa using len), Multiset.bind_assoc]
  have hlen : (List.map Ty.lift pre ++ Ty.var a :: List.map Ty.lift post).length =
      pre.length + 1 + post.length := by simp; omega
  rw [hlen]
  have inner : ∀ S, StoreOK pre.length S →
      ((guards Γ kind (0 + (pre.map (Ty.lift : Ty Empty → Ty String)).length) (.var a :: post.map Ty.lift)
        (value :: ws) S).bind
        fun S' => (body (us ++ value :: ws)).bind
          (resultGuard Γ kind (pre.length + 1 + post.length) (.var a) S')) =
        argCount Γ kind post ws • body (us ++ value :: ws) := by
    intro S hS
    rw [show 0 + (pre.map (Ty.lift : Ty Empty → Ty String)).length = pre.length by simp]
    have guarded : demand (Ty.var a : Ty String) = .guarded := by
      unfold demand
      rw [if_neg (fun h => by cases h), if_neg (show ¬ Unchecked (Ty.var a : Ty String) from fun h => h)]
    simp only [guards, guarded, if_true]
    rw [guard_var_uninterp hS hdv hdve, Multiset.singleton_bind]
    have clearS : PairClear a pre.length (pre.length + 1 + post.length) S := by
      intro w hw
      obtain ⟨j, d, hj, rfl⟩ := hS.2 w hw
      refine ⟨by simp, fun d' h => ?_, fun d' h => ?_⟩ <;>
        simp only [atGuard, Sum.inr.injEq, Prod.mk.injEq] at h <;> omega
    have related := guards_closed_pairStores (Γ := Γ) (a := a) (k := pre.length)
      (m := pre.length + 1 + post.length) (T := dv.ty) kind (pre.length + 1) post ws (by omega) (by omega)
      (So := S ++ [(dv.ty.map (atGuard pre.length), .var (.inl a))]) (Sc := S)
      ⟨S, [], by simp, by simp, clearS, by simp [PairClear, eqnVars]⟩
    have each : ∀ So ∈ guards Γ kind (pre.length + 1) (post.map Ty.lift) ws
        (S ++ [(dv.ty.map (atGuard pre.length), .var (.inl a))]),
        (body (us ++ value :: ws)).bind (resultGuard Γ kind (pre.length + 1 + post.length) (.var a) So) =
          body (us ++ value :: ws) := by
      intro So hSo
      obtain ⟨Sc, hSc, pair⟩ := Multiset.exists_mem_of_rel_of_mem related hSo
      have closedOK := guards_closed_stores (Γ := Γ) kind (pre.length + 1) post ws S
        (hS.mono (by omega)) Sc hSc
      calc
        _ = (body (us ++ value :: ws)).bind (fun r => ({r} : Multiset Atom)) :=
          Multiset.bind_congr fun r member => by
            obtain ⟨theta, rfl, cleanTheta⟩ := instances r member
            exact pair_result_once_clean kind (by omega) clean cleanTheta hdv pair closedOK.1
        _ = body (us ++ value :: ws) := by rw [Multiset.bind_singleton, Multiset.map_id']
    rw [Multiset.bind_congr each, bind_const', Multiset.card_eq_card_of_rel related,
      card_guards_closed kind (hS.mono (by omega)) post ws]
  rw [guards_closed_bind Γ kind pre.length _ _ inner 0 pre us [] (by omega) StoreOK.nil,
    mul_comm, mul_nsmul]

/-- The admitted recursive version theorem without a global functional-space
premise. Exact frame guard counts still come from the entry derivation. -/
theorem version_eq_protocol_local {Γ : Decls} {grounded : String → Bool}
    {pre post : List (Ty Empty)} {admitted : List Atom → Prop}
    {source compiled : RefinedUninterpreted.Body}
    (typeVariable : String)
    (hyps : RefinedUninterpreted.Hyps Γ grounded pre post admitted source compiled) :
    ∀ fuel args, admitted args →
      protocolRun Γ grounded source
          (arrow (pre.map Ty.lift ++ .var typeVariable :: post.map Ty.lift) (.var typeVariable)) fuel args =
        versionRun compiled fuel args
  | 0, _, _ => rfl
  | fuel + 1, args, allowed => by
      have ih := version_eq_protocol_local typeVariable hyps fuel
      have same := hyps.calls _ _ ih (fun ws hws r member => by
        rw [ih ws hws] at member
        exact RefinedUninterpreted.results_uninterpreted hyps fuel ws hws r member) args allowed
      obtain ⟨us, value, ws, rfl, len, before, clean, after⟩ := hyps.entry args allowed
      simp only [protocolRun, versionRun]
      rw [chainCall_congr _ _ same,
        pair_protocol_clean _ pre post typeVariable _ us ws value len clean (fun r member => ?_),
        argCount_of_entryFacts before, argCount_of_entryFacts after, mul_one, one_nsmul]
      exact hyps.results _ (RefinedUninterpreted.results_uninterpreted hyps fuel)
        us value ws len allowed r member

namespace Controls

def overloaded : Decls := fun name =>
  if name = "ambiguous" then [.sym "Number", .sym "String"] else []

def untouched : Atom := .expression [.symbol "raw", .var "x"]

theorem not_functional : ¬ Functional overloaded := by
  intro h
  have bad := h "ambiguous"
  simp [overloaded] at bad

theorem untouched_clean : Uninterp overloaded untouched := by
  simp [untouched, Uninterp, Safe, SafeAll, substA, HeadFree, overloaded]

/-- The irrelevant overload does not multiply the value's typing. -/
theorem unrelated_overload_keeps_one :
    ¬ Functional overloaded ∧ Multiset.card (eff (info overloaded untouched)) = 1 :=
  ⟨not_functional, card_eff_uninterpreted untouched_clean⟩

/-- The footprint condition is necessary: observing the overloaded symbol
itself has two effective derivations. -/
theorem observed_overload_is_not_uninterpreted :
    ¬ Uninterp overloaded (.symbol "ambiguous") ∧
      Multiset.card (eff (info overloaded (.symbol "ambiguous"))) = 2 := by
  simp [Uninterp, Safe, overloaded, info_symbol, eff]

theorem row_protocol_with_unrelated_overload (kind : Atom → String) :
    chainCall overloaded kind (fun args => (args : Multiset Atom))
        (arrow [.var "a"] (.var "a")) [untouched] = {untouched} := by
  have law := pair_protocol_clean kind [] [] "a" (fun args => (args : Multiset Atom))
    [] [] untouched rfl untouched_clean (by
      intro r member
      have eq : r = untouched := by simpa using member
      subst r
      exact ⟨Atom.var, (substA_var_self untouched).symm, fun _ => trivial⟩)
  simpa [argCount, one_nsmul] using law

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.UninterpretedLocalMultiplicity
