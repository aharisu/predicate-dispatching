(define-module predicate-dispatch.print
  (use predicate-dispatch.classes)
  )

(select-module predicate-dispatch.print)

(define-method write-object ((pred <compound-predicate>) port)
  (let ((prefix (cond
                  [(is-a? pred <and-predicate>) "(and "]
                  [(is-a? pred <or-predicate>) "(or "]
		  [else (concatenate "(" (class-of pred) " ")])))
    ;(pprint-logical-block
    ; (str (subpreds-of pred))
    ; (princ prefix str)
    ; (pprint-indent :current 0 str)
    ; (do ((term (pprint-pop) (pprint-pop)))
    ;     (nil nil)
    ;   (write term :stream str :pretty t)
    ;   (pprint-exit-if-list-exhausted)
    ;   (princ " " str)
    ;   (pprint-newline :fill str))
    ; (princ ">" str))
    (format port "~A~A)" prefix (slot-ref pred 'subpreds))
    ))

(define-method write-object ((pred <not-predicate>) port)
  (format port "(not ~S)" (slot-ref pred 'base)))

(define-method write-object ((pred <test-predicate>) port)
  (if (slot-ref pred 'form)
    (format port "(test ~S)" (slot-ref pred 'form)) 
    (format port "(test ~S)" (slot-ref pred 'test))))

(define-method write-object ((pred <constant-predicate>) port)
  (format port "(const ~S)" (slot-ref pred 'value)))

(define-method write-object ((pred <projected-unary-predicate>) port)
  (format port "(proj ~A ~S)" (slot-ref pred 'argument-index) (slot-ref pred 'base)))

(define-method write-object ((pred <typecheck-predicate>) port)
  (format port "(typep ~A)" (slot-ref pred 'target)))

(define-method write-object ((pred <equality-predicate>) port)
  (format port "(eql ~A)" (slot-ref pred 'target)))

(define-method write-object ((pred <extracting-unary-predicate>) port)
  (format port "(extr ~S ~S)" (slot-ref pred 'accessors) (slot-ref pred 'base)))
