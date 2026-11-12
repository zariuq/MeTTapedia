import Mettapedia.Languages.MeTTa.PeTTa.UnifyingAllocation
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingRefinement

/-!
# Fresh compiler locals in the actual source substitution

An administrative binder must be absent from existing keys and values and
from the source terms it surrounds. The actual binding operation then keeps
the old substitution literally, and resolution of source terms is unchanged.
This is not permission to erase arbitrary latent branch bindings.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst atomFreeVars)

def Avoids (key : String) (term : Atom) : Prop := key ∉ atomFreeVars term

def FreshLocal (key : String) (bindings : Subst) : Prop :=
  SupportedBindings (fun other => other ≠ key) bindings

theorem avoids_iff_supported (key : String) (term : Atom) :
    Avoids key term ↔ Supported (fun other => other ≠ key) term := by
  simp only [Avoids,Supported]
  constructor
  · intro absent other member same
    exact absent (same ▸ member)
  · intro supported present
    exact supported key present rfl

theorem fresh_local_lookup {key : String} {bindings : Subst} (fresh : FreshLocal key bindings) :
    bindings.lookup key = none := by
  unfold Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup
  cases found : bindings.find? (fun binding => binding.1 == key) with
  | none => rfl
  | some binding =>
      have member := List.mem_of_find?_eq_some found
      have equal : binding.1 = key := by simpa using List.find?_some found
      exact False.elim ((fresh binding member).1 equal)

theorem resolve_single_avoided (key : String) (value term : Atom) (avoids : Avoids key term) :
    resolve [(key,value)] term = term := by
  apply resolve_of_unbound
  intro other present
  have different : key ≠ other := fun same => avoids (same ▸ present)
  simp [Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,different]

theorem fresh_local_bindVar {key : String} {bindings : Subst} (fresh : FreshLocal key bindings)
    (value : Atom) : bindVar bindings key value = (key,value) :: bindings := by
  unfold bindVar
  congr 1
  calc
    bindings.map (fun binding => (binding.1,applySubst [(key,value)] binding.2)) = bindings.map id := by
      apply List.map_congr_left
      intro binding member
      change (binding.1,applySubst [(key,value)] binding.2) = (binding.1,binding.2)
      exact congrArg (Prod.mk binding.1) (resolve_single_avoided key value binding.2
        ((avoids_iff_supported key binding.2).mpr (fresh binding member).2))
    _ = bindings := List.map_id bindings

theorem fresh_local_resolve {key : String} {bindings : Subst}
    (fresh : FreshLocal key bindings) (value term : Atom) (avoids : Avoids key term) :
    resolve (bindVar bindings key value) term = resolve bindings term := by
  rw [resolve_bindVar (fresh_local_lookup fresh)]
  apply resolve_single_avoided
  exact (avoids_iff_supported key _).mpr
    (supported_resolve fresh term ((avoids_iff_supported key term).mp avoids))

theorem fresh_local_resolved_value {key : String} {bindings : Subst}
    (fresh : FreshLocal key bindings) (value : Atom) (avoids : Avoids key value) :
    Avoids key (resolve bindings value) :=
  (avoids_iff_supported key _).mpr
    (supported_resolve fresh value ((avoids_iff_supported key value).mp avoids))

theorem fresh_local_keeps_other_lookup {key other : String} {bindings : Subst}
    (fresh : FreshLocal key bindings) (value : Atom) (different : key ≠ other) :
    (bindVar bindings key value).lookup other = bindings.lookup other := by
  rw [fresh_local_bindVar fresh]
  exact lookup_cons_ne different

def eraseLocal (key : String) (bindings : Subst) : Subst :=
  bindings.filter (fun binding => binding.1 != key)

theorem erase_fresh_local {key : String} {bindings : Subst} (fresh : FreshLocal key bindings) :
    eraseLocal key bindings = bindings := by
  apply List.filter_eq_self.mpr
  intro binding member
  simpa using (fresh binding member).1

theorem erase_new_local {key : String} {bindings : Subst} (fresh : FreshLocal key bindings) (value : Atom) :
    eraseLocal key (bindVar bindings key value) = bindings := by
  rw [fresh_local_bindVar fresh]
  simp only [eraseLocal,List.filter_cons,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
  exact erase_fresh_local fresh

theorem unifyTerms_fresh_local {key : String} {bindings : Subst}
    (fresh : FreshLocal key bindings) (value : Atom) (avoids : Avoids key value) (fuel : Nat) :
    unifyTerms (fuel + 1) bindings (.var key) value =
      .ok ((key,resolve bindings value) :: bindings) := by
  have resolvedAvoids := fresh_local_resolved_value fresh value avoids
  have noOccurs : occurs key (resolve bindings value) = false := by
    simpa only [occurs,List.contains_eq_mem,decide_eq_false_iff_not,Avoids] using resolvedAvoids
  simp only [unifyTerms,resolve_var_free (fresh_local_lookup fresh)]
  generalize resolved : resolve bindings value = result at resolvedAvoids noOccurs ⊢
  cases result with
  | var other =>
      have different : key ≠ other := by simpa [Avoids,atomFreeVars] using resolvedAvoids
      simp [different,fresh_local_bindVar fresh]
  | symbol | grounded | expression => simp [noOccurs,fresh_local_bindVar fresh]

theorem fresh_local_idempotent {key : String} {bindings : Subst} (valid : Idempotent bindings)
    (fresh : FreshLocal key bindings) (value : Atom) (avoids : Avoids key value) :
    Idempotent ((key,resolve bindings value) :: bindings) := by
  rw [← fresh_local_bindVar fresh]
  exact idempotent_bindVar valid (fresh_local_lookup fresh) (unbound_resolve valid value)
    (fresh_local_resolved_value fresh value avoids)

theorem unifyBinding_fresh_local {key : String} {bindings : Subst}
    (fresh : FreshLocal key bindings) (value : Atom) (avoids : Avoids key value) :
    unifyBinding bindings (.var key) value = .ok ((key,resolve bindings value) :: bindings) := by
  have enough : 2 ≤ fuelFor bindings (.var key) value := by
    simp only [fuelFor,atomSize]
    omega
  have fuelEquation : fuelFor bindings (.var key) value =
      (fuelFor bindings (.var key) value - 2) + 2 := by omega
  simp only [unifyBinding,unifyAsPattern]
  rw [fuelEquation]
  change unifyTerms ((fuelFor bindings (.var key) value - 2) + 1) bindings (.var key) value = _
  exact unifyTerms_fresh_local fresh value avoids _

theorem existing_keys_are_not_fresh : ¬FreshLocal "slot" [("slot",.symbol "old")] := by
  intro fresh
  exact (fresh ("slot",.symbol "old") (by simp)).1 rfl

theorem freshness_does_not_make_self_reference_safe :
    unifyTerms 1 [] (.var "slot") (.expression [.var "slot"]) = .clash := by decide

end Mettapedia.Languages.MeTTa.PeTTa.Unifying
