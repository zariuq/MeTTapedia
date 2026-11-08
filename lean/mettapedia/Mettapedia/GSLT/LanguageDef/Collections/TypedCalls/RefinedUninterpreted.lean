import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Polymorphic

/-!
# Uninterpreted versions on an admitted domain

Closed typing facts do not imply that values are ground. A native admission
domain may therefore refine `UnintEntry`. The recursive proof below keeps that
domain explicit, requiring calls to remain inside it. Clients derive these
local obligations from source analysis and a tested entry gate; they need not
make false global claims about every well-typed call.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.RefinedUninterpreted

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

abbrev Body := (List Atom → Multiset Atom) → List Atom → Multiset Atom

structure Hyps (Γ : Decls) (grounded : String → Bool) (pre post : List (Ty Empty))
    (admitted : List Atom → Prop) (source compiled : Body) : Prop where
  entry : ∀ args, admitted args → UnintEntry Γ grounded pre post args
  calls : ∀ o o' : List Atom → Multiset Atom,
    (∀ args, admitted args → o args = o' args) →
    (∀ args, admitted args → ∀ r ∈ o args, Uninterp Γ r) →
    ∀ args, admitted args → source o args = compiled o' args
  results : ∀ o : List Atom → Multiset Atom,
    (∀ args, admitted args → ∀ r ∈ o args, Uninterp Γ r) →
    ∀ us value ws, pre.length = us.length → admitted (us ++ value :: ws) →
      ∀ r ∈ compiled o (us ++ value :: ws),
        ∃ delta : String → Atom, r = substA delta value ∧ ∀ x, Uninterp Γ (delta x)

theorem results_uninterpreted {Γ : Decls} {grounded : String → Bool}
    {pre post : List (Ty Empty)} {admitted : List Atom → Prop} {source compiled : Body}
    (hyps : Hyps Γ grounded pre post admitted source compiled) :
    ∀ fuel args, admitted args → ∀ r ∈ versionRun compiled fuel args, Uninterp Γ r
  | 0, _, _, r, member => False.elim (Multiset.notMem_zero r member)
  | fuel + 1, args, allowed, r, member => by
      obtain ⟨us, value, ws, rfl, len, _, clean, _⟩ := hyps.entry args allowed
      obtain ⟨delta, rfl, cleanDelta⟩ := hyps.results _ (results_uninterpreted hyps fuel)
        us value ws len allowed r member
      exact uninterp_substA cleanDelta value clean

/-- Guard elimination at every recursive fuel on the admitted domain. The
domain may express groundness, support independence or another real boundary
fact, but the call-preservation obligation must be discharged by the client. -/
theorem version_eq_protocol {Γ : Decls} (functional : Functional Γ)
    {grounded : String → Bool} {pre post : List (Ty Empty)}
    {admitted : List Atom → Prop} {source compiled : Body}
    (typeVariable : String) (hyps : Hyps Γ grounded pre post admitted source compiled) :
    ∀ fuel args, admitted args →
      protocolRun Γ grounded source
          (arrow (pre.map Ty.lift ++ .var typeVariable :: post.map Ty.lift) (.var typeVariable)) fuel args =
        versionRun compiled fuel args
  | 0, _, _ => rfl
  | fuel + 1, args, allowed => by
      have ih := version_eq_protocol functional typeVariable hyps fuel
      have same := hyps.calls _ _ ih (fun ws hws r member => by
        rw [ih ws hws] at member
        exact results_uninterpreted hyps fuel ws hws r member) args allowed
      obtain ⟨us, value, ws, rfl, len, before, clean, after⟩ := hyps.entry args allowed
      simp only [protocolRun, versionRun]
      rw [chainCall_congr _ _ same,
        pair_protocol functional _ pre post typeVariable _ us ws value len clean (fun r member => ?_),
        argCount_of_entryFacts before, argCount_of_entryFacts after, mul_one, one_nsmul]
      obtain ⟨delta, rfl, cleanDelta⟩ := hyps.results _ (results_uninterpreted hyps fuel)
        us value ws len allowed r member
      exact ⟨delta, rfl, safe_of_uninterp cleanDelta value clean⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.RefinedUninterpreted
