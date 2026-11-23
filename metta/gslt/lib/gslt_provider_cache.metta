; Append checked service rows without moving existing receipt row positions.
; Existing rows belong to the admitted immutable plan. This operation checks
; every new row; callers supply the service's separate semantic guarantee.
(: gslt:provider-cache:append (-> Atom Atom %Undefined%))
(= (gslt:provider-cache:append $plan $newRows)
  (case $plan
    (((CompletePlan (PremiseEnvironment $declarations $rewrites $specifications
          (PremiseProvider $signatures $oldRows) $reflection $free)
         $permissions $bound $expected $rules $equations $admitted)
      (if (gslt:snapshot:check-rows $declarations $free $bound $signatures $newRows)
        (let $rows (gslt:automata:append $oldRows $newRows)
          (Some (CompletePlan (PremiseEnvironment $declarations $rewrites $specifications
                   (PremiseProvider $signatures $rows) $reflection $free)
                 $permissions $bound $expected $rules $equations $admitted))) None))
     ($bad None))))
