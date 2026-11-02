import Mettapedia.Languages.ProcessCalculi.Ambient.Decoding

/-!
# Reading back commutes with renaming

Places are read off a component's first argument, so renaming a component renames its place (`placeOf_rename`), and
renaming a block's outer variables renames its outer place (`outerPlace_renameOuter`). An injective renaming keeps
which components share a place, so reading back a renamed block is renaming the reading (`decodeForm_renameOuter`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Decoding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (liftIndex)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex decompose rename rename_bvar rename_fvar rename_apply
  rename_lambda rename_multiLambda rename_subst rename_collection rename_comp liftBVars_eq_rename shiftAbove
  decompose_renameOuter rename_injective liftIndex_injective rename_restricts rename_body)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambientBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedBlock)

/-! ## Variables and places under renaming -/

theorem isVariable_rename (relabel : Nat → Nat) (pattern : Pattern) :
    isVariable (rename relabel pattern) = isVariable pattern := by
  cases pattern <;> simp [isVariable, rename_bvar, rename_fvar, rename_apply, rename_lambda, rename_multiLambda,
    rename_subst, rename_collection]

theorem isMessage_rename (relabel : Nat → Nat) : ∀ pattern : Pattern,
    isMessage (rename relabel pattern) = isMessage pattern
  | .bvar _ => by simp [isMessage, rename_bvar]
  | .fvar _ => by simp [isMessage, rename_fvar]
  | .apply label [] => by simp [isMessage, rename_apply]
  | .apply label [name] => by simp [isMessage, rename_apply, isVariable_rename]
  | .apply label [first, second] => by
      simp [isMessage, rename_apply, isMessage_rename relabel first, isMessage_rename relabel second]
  | .apply label (_ :: _ :: _ :: _) => by simp [isMessage, rename_apply]
  | .lambda _ _ => by simp [isMessage, rename_lambda]
  | .multiLambda _ _ _ => by simp [isMessage, rename_multiLambda]
  | .subst _ _ => by simp [isMessage, rename_subst]
  | .collection _ _ _ => by simp [isMessage, rename_collection]

theorem lowerBy_rename (count : Nat) (relabel : Nat → Nat) (pattern : Pattern) :
    lowerBy count (rename (liftIndex count relabel) pattern) = (lowerBy count pattern).map (rename relabel) := by
  cases pattern with
  | bvar index =>
      simp only [rename_bvar, lowerBy, liftIndex]
      by_cases below : index < count
      · have notAbove : ¬ count ≤ index := by omega
        simp [below, notAbove]
      · have above : count ≤ index := by omega
        simp [below, above, rename_bvar]
  | fvar name => simp [rename_fvar, lowerBy]
  | _ => simp [rename_apply, rename_lambda, rename_multiLambda, rename_subst, rename_collection, lowerBy]

/-- **Places are renamed with their components**, and outer places with their blocks' outer variables. -/
theorem places_rename : ∀ (fuel : Nat),
    (∀ (relabel : Nat → Nat) (component : Pattern),
      placeOf fuel (rename relabel component) = (placeOf fuel component).map (rename relabel)) ∧
    (∀ (relabel : Nat → Nat) (form : Prenex),
      outerPlace fuel (form.renameOuter relabel) = (outerPlace fuel form).map (rename relabel))
  | 0 => ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | fuel + 1 => by
      obtain ⟨placesBelow, outerBelow⟩ := places_rename fuel
      refine ⟨fun relabel component => ?_, fun relabel form => ?_⟩
      · cases component with
        | apply label arguments =>
            match arguments with
            | [] => simp [rename_apply, placeOf]
            | [argument] =>
                simp only [rename_apply, List.map_cons, List.map_nil, placeOf]
                split_ifs
                · rw [decompose_renameOuter, outerBelow]
                · rfl
            | [first, second, third] =>
                simp only [rename_apply, List.map_cons, List.map_nil, placeOf]
                split_ifs <;> rfl
            | [first, second] =>
                simp only [rename_apply, List.map_cons, List.map_nil, placeOf]
                split_ifs <;> rfl
            | _ :: _ :: _ :: _ :: _ => simp [rename_apply, placeOf]
        | _ => simp [rename_bvar, rename_fvar, rename_lambda, rename_multiLambda, rename_subst, rename_collection,
            placeOf]
      · obtain ⟨count, components⟩ := form
        simp only [Prenex.renameOuter, outerPlace]
        rw [List.findSome?_map]
        induction components with
        | nil => rfl
        | cons component rest recurse =>
            simp only [List.findSome?_cons, Function.comp, placesBelow]
            cases placeOf fuel component with
            | none => simpa using recurse
            | some place =>
                simp only [Option.map_some, Option.bind_some, lowerBy_rename]
                cases lowerBy count place with
                | none => simpa using recurse
                | some lowered => rfl

theorem placeOf_rename (fuel : Nat) (relabel : Nat → Nat) (component : Pattern) :
    placeOf fuel (rename relabel component) = (placeOf fuel component).map (rename relabel) :=
  (places_rename fuel).1 relabel component

theorem placeAt_rename (relabel : Nat → Nat) (component : Pattern) :
    placeAt (rename relabel component) = (placeAt component).map (rename relabel) := by
  rw [placeAt, placeAt, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.size_rename, placeOf_rename]

/-! ## Reading back under an injective renaming -/

theorem toPattern_renameOuter (relabel : Nat → Nat) (form : Prenex) :
    Prenex.toPattern ambientBlock (form.renameOuter relabel) = rename relabel (Prenex.toPattern ambientBlock form) := by
  obtain ⟨count, components⟩ := form
  simp only [Prenex.toPattern, Prenex.renameOuter]
  rw [rename_restricts, rename_body]

theorem placedAt_rename {relabel : Nat → Nat} (injective : Function.Injective relabel) (place component : Pattern) :
    placedAt (rename relabel place) (rename relabel component) = placedAt place component := by
  simp only [placedAt, placeAt_rename]
  cases found : placeAt component with
  | none => simp
  | some at' =>
      simp only [Option.map_some]
      exact decide_eq_decide.mpr ⟨fun same => rename_injective injective same, fun same => by rw [same]⟩

theorem filter_placed_rename {relabel : Nat → Nat} (injective : Function.Injective relabel) (place : Pattern)
    (keep : Bool → Bool) (components : List Pattern) :
    (components.map (rename relabel)).filter (fun component => keep (placedAt (rename relabel place) component)) =
      (components.filter fun component => keep (placedAt place component)).map (rename relabel) := by
  rw [List.filter_map]
  congr 2
  funext component
  simp [Function.comp, placedAt_rename injective]

theorem ambientCapability_rename (relabel : Nat → Nat) (label : String) (arguments : List Pattern) :
    rename relabel (.apply (ambientCapability label) arguments) =
      .apply (ambientCapability label) (arguments.map (rename relabel)) := rename_apply _ _ _

/-- No capability is a marker. -/
theorem not_marker_of_capability {label : String} (listed : label ∈ capabilities) : label ∉ markers := by
  simp only [capabilities, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl <;> simp [markers]

/-- No marker is a capability. -/
theorem not_capability_of_marker {label : String} (isMarker : label ∈ markers) : label ∉ capabilities :=
  fun listed => not_marker_of_capability listed isMarker

theorem wrapContent_rename (relabel : Nat → Nat) (label : String) (name content : Pattern) :
    rename relabel (wrapContent label name content) =
      wrapContent label (rename relabel name) (rename relabel content) := by
  unfold wrapContent
  split_ifs <;> simp [rename_apply]

/-- **Reading back commutes with injective renamings**: of a block's outer variables, of the components placed at a
renamed place, of one component. -/
theorem decode_rename : ∀ (fuel : Nat) {relabel : Nat → Nat}, Function.Injective relabel →
    (∀ (place : Pattern) (form : Prenex),
      decodeForm fuel (rename relabel place) (form.renameOuter relabel) = (decodeForm fuel place form).renameOuter relabel) ∧
    (∀ (place : Pattern) (components : List Pattern),
      readPlaced fuel (rename relabel place) (components.map (rename relabel)) =
        (readPlaced fuel place components).map (rename relabel)) ∧
    (∀ (place component : Pattern) (components : List Pattern),
      readComponent fuel (rename relabel place) (rename relabel component) (components.map (rename relabel)) =
        rename relabel (readComponent fuel place component components))
  | 0, _, _ => ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩
  | fuel + 1, relabel, injective => by
      obtain ⟨formsBelow, placedBelow, componentBelow⟩ := decode_rename fuel injective
      refine ⟨fun place form => ?_, fun place components => ?_, fun place component components => ?_⟩
      · obtain ⟨count, components⟩ := form
        have lifted := (decode_rename fuel (liftIndex_injective injective count)).2.1
        simp only [decodeForm, Prenex.renameOuter]
        congr 1
        rw [← lifted, liftBVars_eq_rename, liftBVars_eq_rename, rename_comp, rename_comp]
        congr 2
        funext index
        simp [Function.comp, shiftAbove, liftIndex]
      · simp only [readPlaced]
        have here := filter_placed_rename injective place id components
        have elsewhere := filter_placed_rename injective place (fun placed => !placed) components
        simp only [id] at here elsewhere
        rw [here, elsewhere, List.map_map, List.map_map]
        refine List.map_congr_left fun component _ => ?_
        simp only [Function.comp]
        exact componentBelow place component _
      · cases component with
        | apply label arguments =>
            match arguments with
            | [] => simp [rename_apply, readComponent]
            | [argument] =>
                simp only [rename_apply, List.map_cons, List.map_nil, readComponent]
                split_ifs
                · rw [decompose_renameOuter, formsBelow, toPattern_renameOuter]
                  simp [rename_apply]
                · rfl
            | [first, second, third] =>
                simp only [rename_apply, List.map_cons, List.map_nil, readComponent, isVariable_rename]
                simp only [isMessage_rename]
                split_ifs
                · rw [placedBelow, ← rename_body, wrapContent_rename]
                · rfl
                · rw [decompose_renameOuter, formsBelow, toPattern_renameOuter]
                  simp [rename_apply]
                · rfl
                · rw [decompose_renameOuter, formsBelow, toPattern_renameOuter]
                  simp [rename_apply]
                · rfl
                · rfl
            | [first, second] =>
                simp only [rename_apply, List.map_cons, List.map_nil, readComponent, isMessage_rename]
                split_ifs
                · cases second with
                  | lambda binder body =>
                      have lifted := (decode_rename fuel (liftIndex_injective injective 1)).1
                      have placeLift : liftBVars 0 1 (rename relabel place) =
                          rename (liftIndex 1 relabel) (liftBVars 0 1 place) := by
                        rw [liftBVars_eq_rename, liftBVars_eq_rename, rename_comp, rename_comp]
                        congr 1
                      simp only [rename_lambda, rename_apply, List.map_cons, List.map_nil]
                      rw [decompose_renameOuter, placeLift, lifted, toPattern_renameOuter]
                  | _ => simp [rename_bvar, rename_fvar, rename_apply, rename_multiLambda, rename_subst,
                      rename_collection, inaction]
                · simp [rename_apply]
                · rfl
                · rfl
            | _ :: _ :: _ :: _ :: _ => simp [rename_apply, readComponent]
        | _ => simp [rename_bvar, rename_fvar, rename_lambda, rename_multiLambda, rename_subst, rename_collection,
            readComponent, inaction, rename_apply]

end Mettapedia.Languages.ProcessCalculi.Ambient.Decoding
