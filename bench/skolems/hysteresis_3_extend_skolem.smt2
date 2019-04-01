(declare-fun $V20_early$2 () Bool)
(declare-fun %init () Bool)
(declare-fun $OK$2 () Bool)

(assert (and (= $OK$2 (ite %init true (not false))) (= $V20_early$2 false)))
(check-sat)
