(declare-fun $V19_late$2 () Bool)
(declare-fun $V20_early$2 () Bool)
(declare-fun %init () Bool)
(declare-fun $OK$2 () Bool)

(assert (let ((a!1 (= $OK$2
              (and (not false)
                   (ite %init true (not false))
                   (ite %init true (not false))))))
  (and a!1 (= $V19_late$2 false) (= $V20_early$2 false))))
(check-sat)
