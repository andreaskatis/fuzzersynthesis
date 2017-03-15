; K = 2
; Transition relation
(define-fun T ((%init Bool) ($V19_late$0 Bool) ($V20_early$0 Bool) ($OK$0 Bool) ($V19_late$1 Bool) ($V20_early$1 Bool) ($OK$1 Bool)) Bool (= $OK$1 (not (and $V19_late$1 $V20_early$1))))
; Universally quantified variables
(declare-fun $V19_late$~1 () Bool)
(declare-fun $V20_early$~1 () Bool)
(declare-fun $OK$~1 () Bool)
(declare-fun $V19_late$0 () Bool)
(declare-fun $V20_early$0 () Bool)
(declare-fun $OK$0 () Bool)
(declare-fun $V19_late$3 () Bool)
(declare-fun $V20_early$3 () Bool)
(declare-fun $OK$3 () Bool)
(assert (and (T false $V19_late$0 $V20_early$0 $OK$0 $V19_late$3 $V20_early$3 $OK$3) $OK$3))
