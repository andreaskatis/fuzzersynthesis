; K = 1
; Transition relation
(define-fun T ((%init Bool) ($V19_late$0 Bool) ($V20_early$0 Bool) ($OK$0 Bool) ($V19_late$1 Bool) ($V20_early$1 Bool) ($OK$1 Bool)) Bool (= $OK$1 (not (and $V19_late$1 $V20_early$1))))
; Universally quantified variables
(declare-fun $V19_late$~1 () Bool)
(declare-fun $V20_early$~1 () Bool)
(declare-fun $OK$~1 () Bool)
(declare-fun $V19_late$2 () Bool)
(declare-fun $V20_early$2 () Bool)
(declare-fun $OK$2 () Bool)
(assert (and (T true $V19_late$~1 $V20_early$~1 $OK$~1 $V19_late$2 $V20_early$2 $OK$2) $OK$2))
