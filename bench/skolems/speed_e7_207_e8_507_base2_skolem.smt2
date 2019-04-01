(declare-fun $V20_early$3 () Bool)
(declare-fun $V19_late$3 () Bool)
(declare-fun $OK$3 () Bool)

(assert (and (= $OK$3 true) (= $V19_late$3 false) (= $V20_early$3 true)))
(check-sat)
