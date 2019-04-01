(declare-fun $V20_early$2 () Bool)
(declare-fun $V19_late$2 () Bool)
(declare-fun $OK$2 () Bool)

(assert (and (= $OK$2 true) (= $V19_late$2 false) (= $V20_early$2 true)))
(check-sat)
