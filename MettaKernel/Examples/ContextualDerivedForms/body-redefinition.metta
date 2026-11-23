; Calibration fixture: body-redefinition
(= (worker) before)
!(let $unused anything (worker))
!(remove-atom &self (= (worker) before))
!(add-atom &self (= (worker) after))
!(let $unused anything (worker))
