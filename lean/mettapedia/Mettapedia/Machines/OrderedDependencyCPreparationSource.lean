import Mettapedia.GSLT.LanguageDef.NativeOpsCReservationSyntax

/-!
# Actual dependency reservation source and retained syntax

The preparation and capacity helper below are supplied as complete C text.
Their independently written syntax keeps pointer-level qualification, guards,
deduplication, allocation calls, failed cleanup and the final initializer.
Source recognition does not establish the allocator or heap contract.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.OrderedDependencyCPreparationSource

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

def typeNames : TypeNames := ["bool".toList, "Space".toList,
  "SpaceDependencyReservation".toList, "uint32_t".toList,
  "uint64_t".toList, "size_t".toList]

def reserveSource : String := r#"static bool space_module_link_reserve(Space ***items, uint32_t *capacity,
                                       uint32_t required) {
    if (required <= *capacity)
        return true;
    uint32_t next = *capacity ? *capacity : 4u;
    while (next < required) {
        if (next > UINT32_MAX / 2u) {
            next = required;
            break;
        }
        next *= 2u;
    }
    if ((uint64_t)next * sizeof(**items) > SIZE_MAX)
        return false;
    Space **grown = space_module_link_try_reallocate(*items, sizeof(**items) * (size_t)next);
    if (!grown)
        return false;
    *items = grown;
    *capacity = next;
    return true;
}"#

def preparationSource : String := r#"static bool space_prepare_dependencies(
        Space *importer, Space *const *dependencies, uint32_t count,
        SpaceDependencyReservation *reservation) {
    *reservation = (SpaceDependencyReservation){0};
    if (!importer || (count != 0u && !dependencies))
        return false;
    bool has_new = false;
    for (uint32_t i = 0u; i < count; i++) {
        Space *dependency = dependencies[i];
        if (!dependency || dependency == importer)
            return false;
        bool present = false;
        for (uint32_t j = 0u; j < importer->dep_count && !present; j++)
            present = importer->deps[j] == dependency;
        has_new |= !present;
    }
    if (!has_new)
        return true;
    if ((uint64_t)count * sizeof(Space *) > SIZE_MAX)
        return false;
    Space **pending = space_module_link_try_reallocate(NULL, sizeof(*pending) * (size_t)count);
    if (!pending)
        return false;
    uint32_t added = 0u;
    bool ok = true;
    for (uint32_t i = 0u; ok && i < count; i++) {
        Space *dependency = dependencies[i];
        if (!dependency || dependency == importer) {
            ok = false;
            break;
        }
        bool present = false;
        for (uint32_t j = 0u; j < importer->dep_count && !present; j++)
            present = importer->deps[j] == dependency;
        for (uint32_t j = 0u; j < added && !present; j++)
            present = pending[j] == dependency;
        if (!present)
            pending[added++] = dependency;
    }
    ok = ok && added <= UINT32_MAX - importer->dep_count &&
        space_module_link_reserve(&importer->deps, &importer->dep_cap,
                                  importer->dep_count + added);
    for (uint32_t i = 0u; ok && i < added; i++) {
        Space *dependency = pending[i];
        ok = dependency->importer_count != UINT32_MAX &&
            space_module_link_reserve(&dependency->importers, &dependency->importer_cap,
                                      dependency->importer_count + 1u);
    }
    if (!ok) {
        free(pending);
        return false;
    }
    *reservation = (SpaceDependencyReservation){pending, added};
    return true;
}"#

private def v (name : String) : CExpr := .identifier name.toList
private def f (record field : String) : CExpr := .field (v record) field.toList true
private def u (value : Nat) : CExpr := .unsignedInteger value
private def deref (value : CExpr) : CExpr := .unary .dereference value
private def neg (value : CExpr) : CExpr := .unary .not value
private def addr (value : CExpr) : CExpr := .unary .address value
private def binary (operator : BinaryOperator) (left right : CExpr) : CExpr :=
  .binary operator left right
private def call (name : String) (arguments : List CExpr) : CExpr := .call name.toList arguments
private def returned (value : Bool) : CStatement := .return (some (.bool value))
private def uint32 : CType := ⟨"uint32_t".toList, 0⟩
private def boolType : CType := ⟨"bool".toList, 0⟩
private def spacePointer : CType := ⟨"Space".toList, 1⟩
private def reservationType : CType := ⟨"SpaceDependencyReservation".toList, 0⟩
private def increment (name : String) : CExpr := .postIncrement (v name)

def reserveBody : List CStatement := [
  .branch (binary .le (v "required") (deref (v "capacity"))) [returned true] [],
  .declare uint32 "next".toList
    (.conditional (deref (v "capacity")) (deref (v "capacity")) (u 4)),
  .whileLoop (binary .lt (v "next") (v "required")) [
    .branch (binary .gt (v "next") (binary .div (v "UINT32_MAX") (u 2)))
      [.assign (v "next") (v "required"), .break] [],
    .compoundAssign .mul (v "next") (u 2)],
  .branch (binary .gt
    (binary .mul (.cast ⟨"uint64_t".toList, 0⟩ (v "next"))
      (.sizeOfExpr (deref (deref (v "items"))))) (v "SIZE_MAX")) [returned false] [],
  .declare ⟨"Space".toList, 2⟩ "grown".toList
    (call "space_module_link_try_reallocate" [deref (v "items"),
      binary .mul (.sizeOfExpr (deref (deref (v "items"))))
        (.cast ⟨"size_t".toList, 0⟩ (v "next"))]),
  .branch (neg (v "grown")) [returned false] [],
  .assign (deref (v "items")) (v "grown"),
  .assign (deref (v "capacity")) (v "next"),
  returned true]

def reserveFunction : CDeclaratorFunction :=
  ⟨boolType, "space_module_link_reserve".toList,
    [⟨⟨"Space".toList, false, [false, false, false]⟩, "items".toList⟩,
     ⟨⟨"uint32_t".toList, false, [false]⟩, "capacity".toList⟩,
     ⟨⟨"uint32_t".toList, false, []⟩, "required".toList⟩], reserveBody⟩

private def invalidDependency : CExpr :=
  binary .or (neg (v "dependency")) (binary .eq (v "dependency") (v "importer"))

private def scanExisting : CStatement :=
  .forLoop uint32 "j".toList (u 0)
    (binary .and (binary .lt (v "j") (f "importer" "dep_count")) (neg (v "present")))
    (increment "j") [.assign (v "present")
      (binary .eq (.index (f "importer" "deps") (v "j")) (v "dependency"))]

def preparationBody : List CStatement := [
  .assign (deref (v "reservation")) (.zero reservationType),
  .branch (binary .or (neg (v "importer"))
    (binary .and (binary .ne (v "count") (u 0)) (neg (v "dependencies"))))
    [returned false] [],
  .declare boolType "has_new".toList (.bool false),
  .forLoop uint32 "i".toList (u 0) (binary .lt (v "i") (v "count")) (increment "i") [
    .declare spacePointer "dependency".toList (.index (v "dependencies") (v "i")),
    .branch invalidDependency [returned false] [],
    .declare boolType "present".toList (.bool false), scanExisting,
    .compoundAssign .bitOr (v "has_new") (neg (v "present"))],
  .branch (neg (v "has_new")) [returned true] [],
  .branch (binary .gt (binary .mul (.cast ⟨"uint64_t".toList, 0⟩ (v "count"))
    (.sizeOf spacePointer)) (v "SIZE_MAX")) [returned false] [],
  .declare ⟨"Space".toList, 2⟩ "pending".toList
    (call "space_module_link_try_reallocate" [.null,
      binary .mul (.sizeOfExpr (deref (v "pending")))
        (.cast ⟨"size_t".toList, 0⟩ (v "count"))]),
  .branch (neg (v "pending")) [returned false] [],
  .declare uint32 "added".toList (u 0),
  .declare boolType "ok".toList (.bool true),
  .forLoop uint32 "i".toList (u 0)
    (binary .and (v "ok") (binary .lt (v "i") (v "count"))) (increment "i") [
    .declare spacePointer "dependency".toList (.index (v "dependencies") (v "i")),
    .branch invalidDependency [.assign (v "ok") (.bool false), .break] [],
    .declare boolType "present".toList (.bool false), scanExisting,
    .forLoop uint32 "j".toList (u 0)
      (binary .and (binary .lt (v "j") (v "added")) (neg (v "present"))) (increment "j")
      [.assign (v "present") (binary .eq (.index (v "pending") (v "j")) (v "dependency"))],
    .branch (neg (v "present"))
      [.assign (.index (v "pending") (increment "added")) (v "dependency")] []],
  .assign (v "ok") (binary .and
    (binary .and (v "ok")
      (binary .le (v "added") (binary .sub (v "UINT32_MAX") (f "importer" "dep_count"))))
    (call "space_module_link_reserve" [addr (f "importer" "deps"),
      addr (f "importer" "dep_cap"), binary .add (f "importer" "dep_count") (v "added")])),
  .forLoop uint32 "i".toList (u 0)
    (binary .and (v "ok") (binary .lt (v "i") (v "added"))) (increment "i") [
    .declare spacePointer "dependency".toList (.index (v "pending") (v "i")),
    .assign (v "ok") (binary .and
      (binary .ne (f "dependency" "importer_count") (v "UINT32_MAX"))
      (call "space_module_link_reserve" [addr (f "dependency" "importers"),
        addr (f "dependency" "importer_cap"),
        binary .add (f "dependency" "importer_count") (u 1)]))],
  .branch (neg (v "ok")) [.effect (call "free" [v "pending"]), returned false] [],
  .assign (deref (v "reservation")) (.aggregate reservationType [v "pending", v "added"]),
  returned true]

def preparationFunction : CDeclaratorFunction :=
  ⟨boolType, "space_prepare_dependencies".toList,
    [⟨⟨"Space".toList, false, [false]⟩, "importer".toList⟩,
     ⟨⟨"Space".toList, false, [true, false]⟩, "dependencies".toList⟩,
     ⟨⟨"uint32_t".toList, false, []⟩, "count".toList⟩,
     ⟨⟨"SpaceDependencyReservation".toList, false, [false]⟩, "reservation".toList⟩],
    preparationBody⟩

end Mettapedia.Machines.OrderedDependencyCPreparationSource
