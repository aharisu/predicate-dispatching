(define-module predicate-dispatch
  (use predicate-dispatch.classes)
  (use predicate-dispatch.build)
  (use predicate-dispatch.normalize)
  (export
    define-pd-generic apply-pd-generic add-pd-method!
    ))

(select-module predicate-dispatch)

(define-class <pd-generic> ()
  (
   (name :init-keyword :name)
   (methods :init-form '())
   ))

(define-class <pd-method> ()
  (
   (lambda-list :init-keyword :lambda-list)
   (predicate :init-keyword :predicate)
   (body :init-keyword :body)
   ))

(define-macro (define-pd-generic name)
  `(define ,name (make (quote ,<pd-generic>)
                       :name (quote ,name))))

(define (compute-applicable-sorted-pd-methods pd-generic args)
  (let* ([methods (slot-ref pd-generic 'methods)]
         [applicable (filter
                       (lambda (method) (evaluate-predicate (slot-ref method 'predicate) args))
                       methods)]
         [sorted (sort applicable implies? (cut slot-ref <> 'predicate))])
    sorted))

(define (apply-pd-generic pd-generic . args)
  (define (call-next remaining-methods default-args . args)
    (let1 args (if (null? args) default-args args)
      (let find-next ([methods remaining-methods])
        (if (null? methods)
          (errorf "No applicable method for ~A on ~S."
                  (slot-ref pd-generic 'name)
                  args)
          (if (evaluate-predicate (slot-ref (car methods) 'predicate) args)
            (apply (slot-ref (car methods) 'body)
                   (cons (pa$ call-next (cdr methods) args) args))
            (find-next (cdr methods)))))))
  (let1 methods (compute-applicable-sorted-pd-methods pd-generic args)
    (apply call-next `(,methods ,args ,@args))))

(define-macro (add-pd-method! name lambda-list pred-list . body)
  (let ([pred (build-predicate-qualifier lambda-list pred-list)]
        [method-arguments (make-lambda-arguments lambda-list)])
    `(push! (slot-ref ,name 'methods)
       (make (quote ,<pd-method>)
             :lambda-list (quote ,lambda-list)
             :predicate ,pred
             :body (lambda ,method-arguments ,@body)))))

(define (build-predicate-qualifier lambda-list predicate-bodies)
  (let1 predicate (build-predicate lambda-list predicate-bodies)
    (normalize-predicate (make-and predicate))))

(define (make-lambda-arguments lambda-list)
  (cons 'next-method
        (let loop ([ll lambda-list]
                   [key? #f]
                   [acc '()])
          (cond
            [(null? ll)
             (reverse! acc)]
            [(memq (car ll) '(:optional :key))
             (loop (cdr ll) #t (cons (car ll) acc))]
            [(symbol? (car ll))
             (loop (cdr ll) #f (cons (car ll) acc))]
            [(and key? (pair? (car ll)))
             (loop (cdr ll) key? (cons (car ll) acc))]
            [(pair? (car ll))
             (loop (cdr ll) key? (cons (caar ll) acc))]
            [else
              (loop (cdr ll) key? (cons (car ll) acc))]))))

