import Mettapedia.Languages.MeTTa.PeTTa.UnifyingCompilerLocals

/-!
# Projection of compiler-local bindings

Erasing a local key preserves resolution of source terms. Ordinary bindings
at other keys commute with projection. Bound values must avoid the local;
otherwise subsequent source unification could read a hidden dependency.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst atomFreeVars)

def CleanValues (key : String) (bindings : Subst) : Prop :=
  ∀ binding ∈ bindings, Avoids key binding.2

theorem lookup_eraseLocal_other (key other : String) (bindings : Subst) (different : other ≠ key) :
    (eraseLocal key bindings).lookup other = bindings.lookup other := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨name,value⟩
      simp only [eraseLocal,Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup] at ih ⊢
      by_cases localKey : name = key
      · subst name
        have miss : (key == other) = false := by simpa using Ne.symm different
        simp only [List.filter_cons,bne_self_eq_false,Bool.false_eq_true,↓reduceIte,List.find?_cons,miss,ih]
      · by_cases same : name = other
        · subst name
          have kept : (other != key) = true := by simpa using different
          simp only [List.filter_cons,kept,↓reduceIte,List.find?_cons,beq_self_eq_true]
        · have kept : (name != key) = true := by simpa using localKey
          have miss : (name == other) = false := by simpa using same
          simp only [List.filter_cons,kept,↓reduceIte,List.find?_cons,miss,ih]

theorem resolve_eraseLocal (key : String) (bindings : Subst) : ∀ term : Atom, Avoids key term →
    resolve (eraseLocal key bindings) term = resolve bindings term
  | .var other, avoids => by
      have different : other ≠ key := by simpa [Avoids,atomFreeVars,eq_comm] using avoids
      simp only [resolve,applySubst,lookup_eraseLocal_other key other bindings different]
  | .symbol _, _ | .grounded _, _ => rfl
  | .expression items, avoids => by
      simp only [resolve,applySubst,Atom.expression.injEq]
      exact list items (fun item member => fun present =>
        avoids (mem_freeVars_expression.mpr ⟨item,member,present⟩))
where
  list : ∀ items : List Atom, (∀ item ∈ items, Avoids key item) →
      applySubst.applySubstList (eraseLocal key bindings) items = applySubst.applySubstList bindings items
    | [], _ => rfl
    | first :: rest, avoids => by
        simp only [applySubst.applySubstList]
        rw [show applySubst (eraseLocal key bindings) first = applySubst bindings first from
          resolve_eraseLocal key bindings first (avoids first (by simp)),
          list rest (fun item member => avoids item (List.mem_cons_of_mem first member))]

theorem clean_projection_fresh {key : String} {bindings : Subst} (clean : CleanValues key bindings) :
    FreshLocal key (eraseLocal key bindings) := by
  intro binding member
  have original := List.mem_filter.mp member
  exact ⟨by simpa using original.2,(avoids_iff_supported key binding.2).mp (clean binding original.1)⟩

theorem clean_resolved_avoids {key : String} {bindings : Subst} (clean : CleanValues key bindings)
    (term : Atom) (avoids : Avoids key term) : Avoids key (resolve bindings term) := by
  rw [← resolve_eraseLocal key bindings term avoids]
  exact fresh_local_resolved_value (clean_projection_fresh clean) term avoids

theorem clean_bindVar {key name : String} {bindings : Subst} {value : Atom}
    (clean : CleanValues key bindings) (different : name ≠ key) (avoids : Avoids key value) :
    CleanValues key (bindVar bindings name value) := by
  intro binding member
  simp only [bindVar,List.mem_cons,List.mem_map] at member
  rcases member with rfl | ⟨old,oldMember,rfl⟩
  · exact avoids
  · apply (avoids_iff_supported key _).mpr
    apply supported_resolve (bindings := [(name,value)]) _ old.2
      ((avoids_iff_supported key old.2).mp (clean old oldMember))
    intro entry present
    simp only [List.mem_singleton] at present
    subst entry
    exact ⟨different,(avoids_iff_supported key value).mp avoids⟩

theorem eraseLocal_bindVar (key name : String) (bindings : Subst) (value : Atom)
    (different : name ≠ key) :
    eraseLocal key (bindVar bindings name value) = bindVar (eraseLocal key bindings) name value := by
  have commute :
      (bindings.map (fun binding => (binding.1,applySubst [(name,value)] binding.2))).filter
          (fun binding => binding.1 != key) =
        (bindings.filter (fun binding => binding.1 != key)).map
          (fun binding => (binding.1,applySubst [(name,value)] binding.2)) := by
    induction bindings with
    | nil => rfl
    | cons binding rest ih =>
        cases selected : binding.1 != key <;>
          simp [List.map_cons,selected,ih]
  have kept : (name != key) = true := by simpa using different
  simp only [eraseLocal,bindVar,List.filter_cons,kept,↓reduceIte,commute]

theorem hidden_value_dependency_is_observable :
    resolve [("local",.symbol "a"),("source",.var "local")] (.var "source") = .var "local" ∧
      resolve [("local",.symbol "a"),("source",.var "local")]
        (resolve [("local",.symbol "a"),("source",.var "local")] (.var "source")) = .symbol "a" := by decide

end Mettapedia.Languages.MeTTa.PeTTa.Unifying
