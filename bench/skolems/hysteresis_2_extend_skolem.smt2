(declare-fun $V19_late$2 () Bool)
(declare-fun %init () Bool)
(declare-fun $OK$2 () Bool)

(assert (and (= $OK$2 (ite %init true (not false))) (= $V19_late$2 false)))
(check-sat)
