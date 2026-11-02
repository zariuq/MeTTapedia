import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingGuardedArguments

/-!
# Positional argument spines for MM0 inference templates

The common contextual graft instantiates constructor spines from finite
argument segments. Offsets distinguish left and right congruence arguments
and keep definition parameters separate from fresh dummy images.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open MM0ContextualSupport

def argumentSpine (offset count : Nat) : List Preterm :=
  (List.range count).map (fun index => .var (offset + index))

theorem argumentSpine_length (offset count : Nat) : (argumentSpine offset count).length = count := by
  simp [argumentSpine]

theorem argumentSpine_cons (offset count : Nat) :
    argumentSpine offset (count + 1) = .var offset :: argumentSpine (offset + 1) count := by
  simp [argumentSpine, List.range_succ_eq_map, List.map_map, Function.comp_def, Nat.add_assoc, Nat.add_comm 1]

theorem argumentSpine_substituted (before values after : List Preterm) :
    List.Forall₂ (Preterm.Substitutes (Substitution.ofList (before ++ values ++ after)))
      (argumentSpine before.length values.length) values := by
  apply List.forall₂_of_length_eq_of_get
  · exact argumentSpine_length _ _
  · intro index leftInside rightInside
    simp only [argumentSpine, List.get_eq_getElem, List.getElem_map, List.getElem_range]
    apply Preterm.Substitutes.var
    change (before ++ values ++ after)[before.length + index]? = some values[index]
    rw [List.append_assoc, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getElem?_append_left rightInside, List.getElem?_eq_getElem rightInside]

theorem argumentSpine_bounded (offset count bound : Nat) (within : offset + count ≤ bound) :
    ∀ expression ∈ argumentSpine offset count, expression.VarsBelow bound := by
  intro expression member
  obtain ⟨index, inside, rfl⟩ := List.mem_map.mp member
  have smaller := List.mem_range.mp inside
  change offset + index < bound
  omega

theorem constructorSpine_substituted (symbol : Nat) (before values after : List Preterm) :
    Preterm.Substitutes (Substitution.ofList (before ++ values ++ after))
      (Preterm.applyArgs (.term symbol) (argumentSpine before.length values.length))
      (Preterm.applyArgs (.term symbol) values) :=
  Preterm.Substitutes.applyArgs _ _ _ _ _ (.term symbol) (argumentSpine_substituted before values after)

theorem constructorSpine_bounded (symbol offset count bound : Nat) (within : offset + count ≤ bound) :
    (Preterm.applyArgs (.term symbol) (argumentSpine offset count)).VarsBelow bound := by
  apply (Preterm.varsBelow_applyArgs _ _ _).mpr
  exact ⟨trivial, argumentSpine_bounded offset count bound within⟩

theorem fitted_arguments_have_support {signature : TermSignature}
    {formal target : Context} {arguments : List Preterm}
    (typed : List.Forall₂ (Preterm.FitsBinder signature target) arguments formal) :
    ∀ argument ∈ arguments, ∃ support, Preterm.Supports target argument support := by
  induction typed with
  | nil => simp
  | cons head tail ih =>
      intro argument member
      rcases List.mem_cons.mp member with rfl | member
      · exact head.support_exists
      · exact ih argument member

theorem fitted_arguments_supported {sorts : SortSignature} {signature : TermSignature}
    {formal target : Context} {arguments : List Preterm}
    (formed : Context.WellFormed sorts target)
    (typed : List.Forall₂ (Preterm.FitsBinder signature target) arguments formal) :
    ∀ argument ∈ arguments, Term.supportedAt target.length (encode target argument) = true := by
  intro argument member
  obtain ⟨support, supported⟩ := fitted_arguments_have_support typed argument member
  exact encode_supported formed supported

end Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting
