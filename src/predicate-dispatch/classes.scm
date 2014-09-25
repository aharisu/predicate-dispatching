(define-module predicate-dispatch.classes
  (use srfi-1)
  (export
    <predicate>
    <test-predicate> 
    <constant-predicate> 
    <typecheck-predicate> 
    <equality-predicate> 
    <projected-unary-predicate> 
    <extracting-unary-predicate> 
    <compound-predicate>
    <not-predicate> 
    <and-predicate> 
    <or-predicate>
    make-or make-and make-not 
    evaluate-predicate 
    ))

(select-module predicate-dispatch.classes)

(define-class <predicate> () ; abstract
  (
   (normal? :init-keyword :normal? :init-value #f)
   ))

(define-class <test-predicate> (<predicate>)
  (
   (test :init-keyword :test)
   (form :init-keyword :form :init-value #f)
   ))

(define-class <constant-predicate> (<predicate>)
  (
   (value :init-keyword :value)
   ))

(define-class <typecheck-predicate> (<predicate>)
  (
   (target :init-keyword :target)
   ))

(define-class <equality-predicate> (<predicate>)
  (
   (target :init-keyword :target)
   ))

(define-class <modified-predicate> (<predicate>) ; abstract
  (
   (base :init-keyword :base)
   ))

(define-class <projected-unary-predicate> (<modified-predicate>)
  (
   (argument-index :init-keyword :index)
   ))

(define-class <extracting-unary-predicate> (<modified-predicate>)
  (
   (accessors :init-keyword :accessors)
   ))

(define-class <not-predicate> (<modified-predicate>)
  ())

(define-class <compound-predicate> (<predicate>) ; abstract
  (
   (subpreds :init-keyword :subpreds)
   ))

(define-class <and-predicate> (<compound-predicate>)
  ())

(define-class <or-predicate> (<compound-predicate>)
  ())

(define (make-or subpreds :optional (normal? #f))
  (make <or-predicate>
        :subpreds subpreds
        :normal? normal?))

(define (make-and subpreds :optional (normal? #f))
  (make <and-predicate>
        :subpreds subpreds
        :normal? normal?))

(define (make-not base :optional (normal? #f))
  (make <not-predicate>
        :base base
        :normal? normal?))

(define-method evaluate-predicate ((predicate <test-predicate>) args)
  (apply (slot-ref predicate 'test) args))

(define-method evaluate-predicate ((predicate <constant-predicate>) args)
  (slot-ref predicate 'value))

(define-method evaluate-predicate ((predicate <typecheck-predicate>) args)
  (is-a? (car args) (slot-ref predicate 'target)))

(define-method evaluate-predicate ((predicate <equality-predicate>) args)
  (eqv? (car args) (slot-ref predicate 'target)))

(define-method evaluate-predicate ((predicate <projected-unary-predicate>) args)
  (evaluate-predicate (slot-ref predicate 'base)
                      (list (list-ref args (slot-ref predicate 'argument-index)))))

(define-method evaluate-predicate ((predicate <extracting-unary-predicate>) args)
  (do ([arg (car args) ((car accessors) arg)]
       [accessors (slot-ref predicate 'accessors) (cdr accessors)])
      [(null? accessors)
       (evaluate-predicate (slot-ref predicate 'base) (list arg))]))

(define-method evaluate-predicate ((predicate <and-predicate>) args)
  (every (lambda (subpred) (evaluate-predicate subpred args))
         (slot-ref predicate 'subpreds)))

(define-method evaluate-predicate ((predicate <or-predicate>) args)
  (any (lambda (subpred) (evaluate-predicate subpred args))
       (slot-ref predicate 'subpreds)))

(define-method evaluate-predicate ((predicate <not-predicate>) args)
  (not (evaluate-predicate (slot-ref predicate 'base) args)))

