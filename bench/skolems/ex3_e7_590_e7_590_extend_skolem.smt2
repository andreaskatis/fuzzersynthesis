(declare-fun $V19_late$2 () Bool)
(declare-fun $V20_early$~1 () Bool)
(declare-fun %init () Bool)
(declare-fun $OK$2 () Bool)

(assert (let ((a!1 (= $OK$2 (ite %init true (or (not $V20_early$~1) (not false))))))
  (and a!1 (= $V19_late$2 false))))
(check-sat)
