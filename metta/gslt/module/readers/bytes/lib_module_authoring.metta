!(import! &self fs)
!(import! &self proc)

; Authoring compiles a supplied module pipeline through the existing C API.
; The executable, work budget and artifact paths are explicit caller inputs.
; The returned core/rules remain data until the caller selects a realization.
(= (module-authoring:export $request $compiler $budget $request-path $output-path)
   (let* (($request-text (repr $request))
          ($written (fs:write $request-path $request-text))
          ($result (proc:run ($compiler $budget $request-path $output-path) ())))
     (case $result
       (((proc:result (proc:exited 0) proc:normal $stdout $stderr $capture)
         (let $output (fs:read-text $output-path) (parse $output)))
        ($other (ModuleAuthoringFailed $other))))))
