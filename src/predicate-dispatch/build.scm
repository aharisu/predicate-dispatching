(define-module predicate-dispatch.build
  (use srfi-1)
  (use predicate-dispatch.classes)
  (export build-predicate)
  )

(select-module predicate-dispatch.build)

(define (build-predicate lambda-list predicate-bodies)
  (receive (ll-analysis ll-predicates)
    (analyze-lambda-list-for-analysis lambda-list)
    (append ll-predicates
            (map
              (lambda (body)
                (build-pred-internal
                  (analyze-expr body ll-analysis)
                  lambda-list))
              predicate-bodies))))


(define-class <expression-analysis> ()
  (
   (arguments-used :init-keyword :args-used)
   ))

(define-class <trivial-analysis> (<expression-analysis>)
  (
   (code :init-keyword :code)
   (subsitute? :init-keyword :substitute? :init-value '())
   ))

(define-class <manifest-constant> (<expression-analysis>)
  (
   (value :init-keyword :value)
   (arguments-used :init-value '())
   ))

(define-class <extraction-or-simple-test> (<expression-analysis>)
  (
   (argument-index :init-keyword :index)
   (unary-chain :init-keyword :chain)
   ))

(define-class <extraction-analysis> (<extraction-or-simple-test>)
  ())

(define-class <typecheck-analysis> (<extraction-or-simple-test>)
  (
   (target :init-keyword :target)
   ))

(define-class <eql-analysis> (<extraction-or-simple-test>)
  (
   (target :init-keyword :target)
   ))

(define-class <not-analysis> (<expression-analysis>)
  (
   (base :init-keyword :base)
   ))

(define-class <compound-analysis> (<expression-analysis>)
  (
   (terms :init-keyword :terms)
   ))

(define-class <and-analysis> (<compound-analysis>)
  ())

(define-class <or-analysis> (<compound-analysis>)
  ())

(define (make-xtriv analysis var code)
  (make <trivial-analysis>
        :args-used (adjoin var (slot-ref analysis 'arguments-used))
        :code code))

(define (make-triv-entry arg)
  (cons arg (make <trivial-analysis>
                  :args-used (list arg)
                  :code arg)))

(define (null-triv expr)
  (make <trivial-analysis>
        :args-used '()
        :code expr))

(define (car-or-identity x)
  (if (pair? x)
    (car x)
    x))

(define (union-arguments-used l)
  (fold
    (lambda (x acc)
      (lset-union eq? (slot-ref x 'arguments-used) acc))
    '()
    l))

(define (extract-arg-name ll-term key?)
  (cond
    [(atom? ll-term) ll-term]
    [(and (pair? (car ll-term)) key?) (cadr ll-term)]
    [else (car ll-term)]))

(define (analyze-lambda-list-for-analysis lambda-list)
  (do ([ll lambda-list (cdr ll)]
       [index 0 (+ index 1)]
       [partial-result '()]
       [ll-predicates '()]
       [last-key #f])
      [(null? ll)
       (values partial-result (reverse ll-predicates))]
    (let* ([car-ll (car ll)]
           [arg-name (extract-arg-name car-ll (eq? last-key :key))])
      (cond
        [(eq? car-ll :allow-other-keys)
         ;do nothing
         ]
        [(memq car-ll '(:optional :rest :key))
         (set! last-key car-ll)]
        [(not last-key)
         (push! partial-result (cons arg-name
                                     (make <extraction-analysis>
                                           :index index
                                           :chain '()
                                           :args-used (list arg-name))))
         (if (and (pair? car-ll) (not (null? (cdr car-ll))))
           (push! ll-predicates (build-pred-internal
                                  (analyze-specializer (cadr car-ll) arg-name index partial-result)
                                  lambda-list)))]
        [(eq? last-key :rest)
         (push! partial-result (make-triv-entry arg-name))]
        [else ; :optional or :key
          (if (or (atom? car-ll) (null? (cdr car-ll)))
            (push! partial-result (make-triv-entry arg-name))
            (let ([analysis (analyze-expr (cadr car-ll) partial-result)])
              (push! partial-result
                (cons arg-name (make-xtriv analysis arg-name `(or ,arg-name ,(cadr car-ll)))))
              (if (not (null? (cddr car-ll)))
                (push! partial-result (make-triv-entry (caddr car-ll))))))]))))

(define (analyze-specializer specializer arg index ll-analysis)
  (cond
    [(symbol? specializer)
     (make <typecheck-analysis>
           :index index
           :chain '()
           :target (eval specializer #f)
           :args-used (list arg))]
    [(and (list? specializer)
       (= (length specializer) 2)
       (eq? (car specializer) 'eql))
     (analyze-expr `(eql ,arg ,(cadr specializer)) ll-analysis)]
    [else
      (errorf "Unsupported specializer ~s for ~s" specializer arg)]))
         
(define (analyze-expr expr ll-analysis)
  (let1 expansion (macroexpand expr)
    (cond
      [(and (not (eq? expr expansion)) ; expanded?
         (not (memq (car expr) '(and eql not or is-a?))))
       (analyze-expr expansion ll-analysis)]
      [(assoc-ref ll-analysis expr)
       ] ;; do nothing
      [(constant? expr)
       (make <manifest-constant>
             :value (eval expr #f))]
      [(atom? expr)
       (null-triv expr)]
      [(pair? (car expr)) ;;must be a lambda form
       (analyze-exprs expr ll-analysis)]
      [(assoc-ref *analysis-helpers* (car expr))
       => (lambda (fun) (fun expr ll-analysis))]
      [else
        (let* ([aa (map (cut analyze-expr <> ll-analysis) (cdr expr))]
               [aa1 (car aa)])
          (if (or (not (null? (cdr aa)))
                (special-operator? (car expr))
                (not (is-a? aa1 <extraction-analysis>)))
            (make <trivial-analysis>
                  :code expr
                  :args-used (fold
                               (lambda (a acc) (lset-union eq? (slot-ref a 'arguments-used) acc))
                               '()
                               aa))
            (make <extraction-analysis>
                  :index (slot-ref aa1 'argument-index)
                  :chain (cons (eval (car expr) #f)
                               (slot-ref aa1 'unary-chain))
                  :args-used (slot-ref aa1 'arguments-used))))])))
                
(define (analyze-exprs ee l :optional (whole #f) (force-trivial? #t))
  (if (or force-trivial? (not (null? (cdr ee))))
    (make <trivial-analysis>
          :args-used (union-arguments-used (map (cut analyze-expr <> l) ee))
          :code whole)
    (analyze-expr (car ee) l)))

(define (analyze-lambda e l)
  (let* ([new-bound-vars (map car (analyze-lambda-list-for-analysis (cadr e)))]
         [s2 (remove shadowed? s)]
         [shadowed? (lambda (a) (memq (car a) new-bound-vars))])
    (analyze-exprs (cddr e)
                   (remove shadowed? l)
                   e
                   #t)))
    
        
(define (analyze-let e l)
  (let* ([binidng-parts (if (symbol? (cadr e))
                          (caddr e)
                          (cadr e))]
         [new-bound-vars (map car binding-parts)]
         [shadowed? (lambda (a) (memq (car a) new-bound-vars))]
         [for-bindings (lambda (x x*) (case (car e)
                                        [(let) x]
                                        [(let* letrec) x*]))]
         [l2 (remove shadowed? l)]
         [bindings-analysis (analyze-exprs
                              (apply append (map cdr binding-parts))
                              (for-bindings l l2))]
         [body-analysis (analyze-exprs (if (symbol? (cadr e))
                                         (cdddr e)
                                         (cddr e))
                                       l2)])
    (make <trivial-analysis>
          :args-used (lset-union eq?
                                 (slot-ref bindings-analysis 'arguments-used)
                                 (slot-ref body-analysis 'arguments-used))
          :code e)))

(define (analyze-set! e l)
  (analyze-exprs (cddr e) l))

(define (analyze-and/or class e l)
  (let1 subanalyses (map
                      (lambda (x) (analyze-expr x l))
                      (cdr e))
    (make class
          :terms subanalyses
          :args-used (union-arguments-used subanalyses))))

(define (analyze-eql e l)
  (let* ([make-eql (lambda (ea mc)
                     (make <eql-analysis>
                           :index (slot-ref ea 'argument-index)
                           :chain (slot-ref ea 'unary-chain)
                           :args-used (slot-ref ea 'arguments-used)
                           :target (slot-ref mc 'value)))]
         [subanalyses (map
                        (cut analyze-expr <> l)
                        (cdr e))]
         [types (map class-of subanalyses)])
    (cond
      [(equal? types `(,<extraction-analysis> ,<manifest-constant>))
       (make-eql (car subanalyses) (cadr subanalyses))]
      [(equal? types '(,<manifest-constant> ,<extraction-analysis>))
       (make-eql (cadr subanalyses) (car subanalyses))]
      [else
        (make <trivial-analysis>
              :args-used (union-arguments-used subanalyses)
              :code e)])))

(define (analyze-not e l)
  (let1 base (analyze-expr (cadr e) l)
    (if (is-a? base <extraction-analysis>)
      (make <extraction-analysis>
            :index (slot-ref base 'argument-index)
            :chain (cons not (slot-ref base 'unary-chain))
            :args-used (slot-ref base 'arguments-used))
      (make <not-analysis>
            :base base))))

(define (analyze-is-a? e l)
  (let1 subanalyses (map
                      (cut analyze-expr <> l)
                      (cdr e))
    (if (and (is-a? (car subanalyses) <extraction-analysis>)
          (is-a? (cadr subanalyses) <manifest-constant>))
      (make <typecheck-analysis>
            :index (slot-ref (car subanalyses) 'argument-index)
            :chain (slot-ref (car subanalyses) 'unary-chain)
            :args-used (slot-ref (car subanalyses) 'arguments-used)
            :target (slot-ref (cadr subanalyses) 'value))
      (make <trivial-analysis>
            :args-used (fold
                         (lambda (x acc)
                           (lset-union eq? (slot-ref x 'arguments-used) acc))
                         '()
                         subanalyses)
            :code e))))

(define-constant *analysis-helpers*
  `((lambda . ,analyze-lambda)
    (let . ,analyze-let)
    (let* . ,analyze-let)
    (letrec . ,analyze-let)
    (set! . ,analyze-set!)
    ;;
    (and . ,(pa$ analyze-and/or <and-analysis>))
    (or . ,(pa$ analyze-and/or <or-analysis>))
    (eql . ,analyze-eql)
    (not . ,analyze-not)
    (is-a? . ,analyze-is-a?)
    ))

(define-method build-pred-internal ((analysis <trivial-analysis>) lambda-list)
  (let ([used (slot-ref analysis 'arguments-used)]
        [code (slot-ref analysis 'code)]
        [rnorm '()]
        [ropt '()]
        [rest #f]
        [rkey '()]
        [last-ll-key #f]
        [remaining-optionals '()])
    (let loop ([ll lambda-list]
               [index 0])
      (let* ([car-ll (car ll)]
             [arg-name (extract-arg-name car-ll (eq? last-ll-key :key))]
             [used? (memq arg-name used)])
        (let1 result (cond
                       [(eq? car-ll :allow-other-keys)
                        #f] 
                       [(eq? car-ll :optional)
                        (set! last-ll-key car-ll)
                        (set! remaining-optionals (cdr ll))
                        #f]
                       [(memq car-ll '(:rest :key))
                        (set! last-ll-key car-ll)
                        #f]
                       [(and (not last-ll-key)
                          (pair? used)
                          (null? (cdr used))
                          (eq? arg-name (car used)))
                        (make <projected-unary-predicate>
                              :index index
                              :base (make <test-predicate>
                                          :test (eval
                                                  `(lambda (,arg-name) ,(slot-ref analysis 'code))
                                                  #f)
                                          :form `(lambda (,arg-name) ,(slot-ref analysis 'code))
                                          ))]
                       [(not last-ll-key)
                        (push! rnorm arg-name)
                        #f]
                       [(and (eq? last-ll-key :rest) used?)
                        (set! rest arg-name)
                        #f]
                       [(and (eq? last-ll-key :key) used?)
                        (push! rkey (list arg-name
                                          (if (and (pair? car-ll) (not (null? (cdr car-ll))))
                                            (cadr car-ll)
                                            (undefined))))
                        #f]
                       [(and (eq? last-ll-key :optional) used?)
                        (for-each
                          (lambda (x)
                            (push! ropt (car-or-identity x)))
                          (ldiff remaining-optionals ll))
                        (set! remaining-optionals (cdr ll))
                        (if used?
                          (push! ropt car-ll)
                          (push! ropt (list arg-name (cadr car-ll))))
                        #f]
                       [else
                         #f])
          (cond
            [result]
            [(null? (cdr ll))
             (make <test-predicate>
                   :test (eval (rlet1 lam `(lambda (,@(reverse rnorm)
                                         ,@(or (and (not (null? ropt))
                                                 (cons ':optional (reverse ropt)))
                                             '())
                                         ,@(or (and rest `(:rest ,rest))
                                             '())
                                         ,@(or (and (not (null? rkey))
                                                 `(:key ,@(reverse rkey) :allow-other-keys))
                                             '()))
                                  ,code))
                               #f)
                   :form `(lambda (,@(reverse rnorm)
                                         ,@(or (and (not (null? ropt))
                                                 (cons ':optional (reverse ropt)))
                                             '())
                                         ,@(or (and rest `(:rest ,rest))
                                             '())
                                         ,@(or (and (not (null? rkey))
                                                 `(:key ,@(reverse rkey) :allow-other-keys))
                                             '()))
                                  ,code)
                   )]
            [else
              (loop (cdr ll) (+ index 1))]))))))

(define-method build-pred-internal ((analysis <manifest-constant>) ll)
  (make <constant-predicate>
        :value (slot-ref analysis 'value)))

(define-method build-pred-internal ((analysis <extraction-analysis>) ll)
  (let* ([chain0 (slot-ref analysis 'unary-chain)]
         [not? (and (pair? chain0) (eq? (car chain0) not))]
         [chain (if not?
                  (cdr chain0)
                  chain0)]
         [test (make <test-predicate>
                     :test (or (and (pair? chain) (car chain)) identity))]
         [subbase (cond
                    [(or (null? chain) (null? (cdr chain)))
                     test]
                    [else
                      (make <extracting-unary-predicate>
                            :accessors (cdr chain)
                            :base test)])]
         [base (make <projected-unary-predicate>
                     :index (slot-ref analysis 'argument-index)
                     :base subbase)])
    (if not?
      (make-not base)
      base)))

(define-method build-pred-internal ((analysis <extraction-or-simple-test>) ll)
  (let ([base (make (if (is-a? analysis <typecheck-analysis>)
                      <typecheck-predicate>
                      <equality-predicate>)
                    :target (slot-ref analysis 'target))]
        [chain (slot-ref analysis 'unary-chain)])
    (make <projected-unary-predicate>
          :index (slot-ref analysis 'argument-index)
          :base (if (not (null? chain))
                  (make <extracting-unary-predicate>
                        :accessors chain
                        :base base)
                  base))))

(define-method build-pred-internal ((analysis <not-analysis>) ll)
  (make-not (build-pred-internal (slot-ref analysis 'base) ll)))

(define-method build-pred-internal ((analysis <compound-analysis>) ll)
  ((if (is-a? analysis <and-analysis>)
     make-and
     make-or)
   (map
     (lambda (a) (build-pred-internal a ll))
     (slot-ref analysis 'terms))))


;;
;; COMMON LISP STUB

(define (adjoin item list)
  (if (memq item list)
    list
    (cons item list)))

(define (atom? object)
  (not (pair? object)))

(define-macro (assert form)
  `(unless ,(form)
     (errorf "The assertion ~a failed" form)))

(define special-operator? (cut memq <> '(let* set! if begin unwind-protect let quote)))

(define (constant? expr)
  (or (number? expr)
    (string? expr)
    (keyword? expr)
    (and (pair? expr) (eq? (car expr) 'quote))))
  
(define (ldiff list object)
  (let loop ([list list]
             [r '()])
    (if (atom? list)
      (if (eq? list object)
        (reverse! r)
        (reverse! r list))
      (if (eq? list object )
        (reverse! r)
        (loop (cdr list) (cons (car list) r))))))
        
