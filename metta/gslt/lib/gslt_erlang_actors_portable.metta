; Explicit actor-dispatch profile for hosts without the native rho boundary.
; Uses the same actor operations and retains the complete world and pending
; choices. It does not observe or emit administrative rho COMM transitions.

(: gslt:er-actor:choices-portable (-> Atom Atom %Undefined%))
(= (gslt:er-actor:choices-portable $choices $system)
  (case $choices
    ((LNil $system)
     ((LCons $choice $rest)
      (let $next (gslt:er-actor:dispatch $choice $system)
        (case $next
          (((ErActorSystem $processes $network $fresh $history)
            (gslt:er-actor:choices-portable $rest $next))
           ($pending (ErActorChoicesPending $rest $next)))))))))

(: gslt:er-actor:continue-portable (-> Number Number Atom %Undefined%))
(= (gslt:er-actor:continue-portable $ticks $quantum $pending)
  (case $pending
    (((ErActorChoicesPending $rest $action)
      (let $resumed (gslt:er-actor:continue-portable $ticks $quantum $action)
        (case $resumed
          (((ErActorSystem $processes $network $fresh $history)
            (gslt:er-actor:choices-portable $rest $resumed))
           ($unfinished (ErActorChoicesPending $rest $unfinished))))))
     ($action (gslt:er-actor:continue $ticks $quantum $action)))))
