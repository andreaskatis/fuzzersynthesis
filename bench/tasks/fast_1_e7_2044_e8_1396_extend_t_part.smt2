; K = 0
; Transition relation
(define-fun T ((%init Bool) ($ccseti$0 Bool) ($ccsetd$0 Bool) ($ccr$0 Bool) ($V83_cca$0 Bool) ($OK$0 Bool) ($ccseti$1 Bool) ($ccsetd$1 Bool) ($ccr$1 Bool) ($V83_cca$1 Bool) ($OK$1 Bool)) Bool (= $OK$1 (ite (ite %init false (and $V83_cca$1 (not $V83_cca$0))) (or (or (ite %init false (and $ccseti$1 (not $ccseti$0))) (ite %init false (and $ccsetd$1 (not $ccsetd$0)))) (ite %init false (and $ccr$1 (not $ccr$0)))) true)))
; Universally quantified variables
(declare-fun %init () Bool)
(declare-fun $ccseti$~1 () Bool)
(declare-fun $ccsetd$~1 () Bool)
(declare-fun $ccr$~1 () Bool)
(declare-fun $V83_cca$~1 () Bool)
(declare-fun $OK$~1 () Bool)
(declare-fun $ccseti$0 () Bool)
(declare-fun $ccsetd$0 () Bool)
(declare-fun $ccr$0 () Bool)
(declare-fun $V83_cca$2 () Bool)
(declare-fun $OK$2 () Bool)
(assert (and (T %init $ccseti$~1 $ccsetd$~1 $ccr$~1 $V83_cca$~1 $OK$~1 $ccseti$0 $ccsetd$0 $ccr$0 $V83_cca$2 $OK$2) $OK$2))
