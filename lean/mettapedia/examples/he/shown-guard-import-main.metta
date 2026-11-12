(: ImportedGuardBox (-> $t $t ImportedGuardRange))
!(import! &self shown_guard_import_annotation)
(: imported-guard-body (-> ImportedGuardRange))
(= (imported-guard-body) (ImportedGuardBox 1 "wrong-field"))

!(get-type (ImportedGuardBox 1 "wrong-field"))
!(imported-guard-body)
