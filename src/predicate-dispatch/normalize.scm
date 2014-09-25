(define-module predicate-dispatch.normalize
  (use srfi-1)
  (use predicate-dispatch.classes)
  (export
    normalize-predicate 
    implies? 
    ))

(select-module predicate-dispatch.normalize)


;; proposed schema for normalized predicates:
;;
;; full multipredicate = PCM | or(PCM{2,}) | constant
;; full unary predicate [predicate class] = PCU | or(PCU{2,}) | constant
;;
;; PCM = SM | and(SM{2,})
;;  SM = test | not(test) | projected-unary(PCU)
;; PCU = PNU | and(PNU{2,})
;; PNU = PEU | not(PEU)
;; PEU = SU | extracting-unary(SU)
;;  SU = typecheck | equality | test
;;
;; abbreviations stand for (Purely Conjunctive)/Simple Multi-arg/Unary and
;; Possibly Negated/Extracting Unary.


(define-constant *true* (make <constant-predicate> :value #t))
(define-constant *false* (make <constant-predicate> :value #f))

;;
;; normalize
;;

(define constant-predicate? (cut is-a? <> <constant-predicate>))

(define-method normalize-predicate ((predicate <predicate>))
  predicate)

(define-method normalize-predicate ((predicate <not-predicate>))
  (if (slot-ref predicate 'normal?)
    predicate
    (normalize-predicate
      (let1 base (normalize-predicate (slot-ref predicate 'base))
        (cond
          [(is-a? base <not-predicate>)
           (slot-ref base 'base)]
          [(is-a? base <and-predicate>)
           (make-or (map make-not (slot-ref base 'subpreds)))]
          [(is-a? base <or-predicate>)
           (make-and (map make-not (slot-ref base 'subpreds)))]
          [(is-a? base <projected-unary-predicate>)
           (make <projected-unary-predicate>
                 :index (slot-ref base 'argument-index)
                 :base (make-not (slot-ref base 'base)))]
          [(is-a? base <constant-predicate>)
           (make <constant-predicate>
                 :value (not (slot-ref base 'value)))]
          [else
            (make-not base #t)])))))

;;
;; normalize-or
;;

;; Abstract transformations:
;; * p v ~p -> *true*
;; * (p+ ^ q*) v p+ -> p+
;; * (p ^ q+) v (~p ^ q+) -> q+
;; * (p ^ q* ^ r+) v (~p ^ q*) -> (q* ^ r+) v (~p ^ q*)
;; * (p ^ q* ^ r+) v (~p ^ q* ^ s+)
;;   -> (q* ^ r+ ^ s+) v (p ^ q* ^ r+) v (~p ^ q* ^ s+)
;;   [may be useful in setting the stage for other transformations]

;; prove complete?

;; interesting test cases:
;; * (p ^ q) v (p ^ ~q) v (~p ^ q) v (~p ^ ~q)
;; * (p ^ q ^ r) v ~p v ~q v ~r
;; * (p ^ q) v (~q ^ r) v (~r ^ ~p) v (p ^ ~q ^ ~r) v (~p ^ q ^ r)

(define (flattened-or-subpredicates p)
  (if (is-a? p <or-predicate>)
    (apply append (map flattened-or-subpredicates (slot-ref p 'subpreds)))
    (list p)))

(define (extra-flattend-and-subpredicates p)
  (cond
    [(is-a? p <and-predicate>)
     (apply append (map extra-flattend-and-subpredicates (slot-ref p 'subpreds)))]
    [(and (is-a? p <projected-unary-predicate>)
       (is-a? (slot-ref p 'base) <and-predicate>))
     (map
       (lambda (subpred)
         (make <projected-unary-predicate>
               :base subpred
               :index (slot-ref p 'argument-index)))
       (slot-ref (slot-ref p 'base) 'subpreds))]
     [else
       (list p)]))

(define (maybe-make-eup base accessors)
  (if (null? accessors)
    base
    (make <extracting-unary-predicate>
          :base base
          :accessors accessors)))

(define (maybe-flip orig pairs flip?)
  (if flip?
    (or (assoc-ref pairs orig)
      (rassoc-ref pairs orig))
    orig))

(define (adjust-comparsion orig neg-x neg-y)
  (maybe-flip (maybe-flip orig
                          '((same . opposite)
                            (forward . comprehensive)
                            (backward . exclusive))
                          neg-x)
              '((same . opposite)
                (forward . exclusive)
                (backward . comprehensive))
              neg-y))

(define (compare-terms x y neg-x neg-y)
  (adjust-comparsion
    (cond
      [(is-a? x <projected-unary-predicate>)
       (and (is-a? y <projected-unary-predicate>)
         (= (slot-ref x 'argument-index) (slot-ref y 'argument-index))
         (compare-terms (slot-ref x 'base) (slot-ref y 'base) neg-x neg-y))]
      [(is-a? y <projected-unary-predicate>)
       #f]
      ;;
      [(and (is-a? x <equality-predicate>)
         (is-a? y <equality-predicate>))
       (if (equal? (slot-ref x 'target) (slot-ref y 'target))
         'same
         'exclusive)]
      [(is-a? x <equality-predicate>)
       (if (evaluate-predicate y (list (slot-ref x 'target)))
         'forward
         'exclusive)]
      [(is-a? y <equality-predicate>)
       (if (evaluate-predicate x (list (slot-ref y 'target)))
         'backward
         'exclusive)]
      ;;
      [(is-a? x <not-predicate>)
       (compare-terms (slot-ref x 'base) y (not neg-x) neg-y)]
      [(is-a? y <not-predicate>)
       (compare-terms x (slot-ref y 'base) neg-x (not neg-y))]
      ;;
      [(and (is-a? x <extracting-unary-predicate>)
         (is-a? y <extracting-unary-predicate>))
       (do ([x-acc (slot-ref x 'accessors) (cdr x-acc)]
            [y-acc (slot-ref y 'accessors) (cdr y-acc)])
           [(or (null? x-acc) (null? y-acc)
              (not (equal? (car x-acc) (car y-acc))))
            (and (or (null? x-acc) (null? y-acc))
              (compare-terms (maybe-make-eup (slot-ref x 'base) x-acc)
                             (maybe-make-eup (slot-ref y 'base) y-acc)
                             neg-x neg-y))])]
      ;;
      [(and (is-a? x <typecheck-predicate>)
         (is-a? y <typecheck-predicate>))
       (let ([tx (slot-ref x 'target)]
             [ty (slot-ref y 'target)])
         ;; In a more static environment, we'd want to compare the sets
         ;; of concrete subtypes.  As it is, we have to be conservative.
         (cond
           [(equal? tx ty) 'same]
           [(subtype? tx ty) 'forward]
           [(subtype? ty tx) 'backward]
           [else #f]))]
      ;;
      [(and (is-a? x <test-predicate>)
         (is-a? y <test-predicate>))
       (if (equal? (slot-ref x 'test) (slot-ref y 'test))
         'same
         #f)]
      ;;
      [else #f])
    neg-x neg-y))

(define (analyze-term x yy)
  (let1 comparisons (delete #f (map (lambda (y) (compare-terms x y #f #f)) yy))
    (cond
      [(null? comparisons) 'extra]
      [(memq 'exclusive comparisons) 'fatal-mismatch]
      [(memq 'opposite comparisons) 'mismatch]
      [(memq 'same comparisons) 'match]
      ;; [(memq 'forward comparisons) 'match]
      [(memq 'backward comparisons) 'weak]
      ;; "comprehensive" and "forward" don't help us.
      [else 'extra])))

(define (annotate-term x yy)
  (cons x (analyze-term x yy)))

(define (keep? x y)
  (or (memq 'extra (map cdr y))
    (memq 'weak (map cdr x))))

(define (compute-safe-patch left right)
  ;; Return values:
  ;; (1) Safe patch if appropriate (single mismatch), nil otherwise.
  ;; (2) Does left cover any extra territory?
  ;; (3) Does right?
  (let* ([fleft (extra-flattend-and-subpredicates left)]
         [fright (extra-flattend-and-subpredicates right)]
         [xleft (map (lambda (l) (annotate-term l fright)) fleft)]
         [mismatches (count (lambda (x) (eq? (cdr x) 'mismatch)) xleft)])
    (if (or (member 'fatal-mismatch xleft (lambda (x y) (eq? x (cdr y))))
          (> mismatches 1))
      (values #f #t #t) ;; We lose.
      (let* ([xright (map (lambda (r) (annotate-term r fleft)) fright)]
             [keep-right (keep? xright xleft)])
        (if (zero? mismatches)
          (values #f
                  (or (not keep-right)
                    (keep? xleft xright))
                  keep-right)
          (values
	   ;; Merge useful terms into a patch.  Keep weak terms on the left
	   ;; despite their redundancy because something may depend on them
	   ;; wrt short-circuiting.
	   ;; Return t instead of an empty patch.
           (let1 l (map car
                        (remove (lambda (x) (eq? 'mismatch (cdr x)))
                                (append! xleft
                                         (remove
                                           (lambda (x) (memq (cdr x) '(match weak)))
                                           xright))))
             (if (null? l)
               #t
               l))
           (keep? xleft xright)
           keep-right))))))

(define-method normalize-predicate ((predicate <or-predicate>))
  (cond
    [(slot-ref predicate 'normal?)
     predicate]
    [(null? (slot-ref predicate 'subpreds))
     *false*]
    [else
      (let1 subpreds (map normalize-predicate (flattened-or-subpredicates predicate))
        (if (any (cut slot-ref <> 'value) (filter constant-predicate? subpreds))
          *true*
          ;; can mutate here because nothing else refers to subpreds.
          (let do-loop ([queue (remove constant-predicate? subpreds)]
                        [new-subpreds '()]
                        [survivors '()]
                        [insert-head #t])
            (if (null? queue)
              (if (and (pair? new-subpreds) (not (null? (cdr new-subpreds))))
                (make-or new-subpreds #t)
                (car new-subpreds))
              (let do-list ([subpreds new-subpreds])
                (if (null? subpreds)
                  (do-loop (cdr queue)
                           (if insert-head
                             (cons (car queue) survivors)
                             survivors)
                           '()
                           (and (not insert-head) (null? survivors)))
                  (receive (patch keep-left keep-right) (compute-safe-patch (car queue) (car subpreds))
                    (if patch
                      (if (eq? patch #t)
                        *true* ;; we win!
                        (begin
                          (push! (cdr queue) (normalize-predicate (make-and patch)))
                          (if keep-left
                            (set! insert-head #t))
                          (if keep-right
                            (push! survivors (car subpreds)))
                          (do-list (cdr subpreds))))
                      (begin
                        (if keep-left
                          (set! insert-head #t))
                        (if keep-right
                          (push! survivors (car subpreds)))
                        (do-list (cdr subpreds)))))))))))]))

;;
;; normalize-and
;;

(define (flattened-and-subpredicates p)
  (if (is-a? p <and-predicate>)
    (apply append (map flattened-and-subpredicates (slot-ref p 'subpreds)))
    (list p)))

(define-method normalize-predicate ((predicate <and-predicate>))
  (cond
    [(slot-ref predicate 'normal?)
     predicate]
    [(null? (slot-ref predicate 'subpreds))
     *true*]
    [(null? (cdr (slot-ref predicate 'subpreds)))
     (normalize-predicate (car (slot-ref predicate 'subpreds)))]
    [else
      (let* ([subpreds (map normalize-predicate (flattened-and-subpredicates predicate))]
             [first-or (find (cut is-a? <> <or-predicate>) subpreds)])
        (if first-or ;; distribute!
          (normalize-predicate
            (make-or
              (map
                (lambda (x) (make-and (substitute x first-or subpreds 1)))
                (slot-ref first-or 'subpreds))))
          (do ([ht (make-hash-table)]
               [rsp (reverse subpreds) (cdr rsp)])
              [(null? rsp)
               (let1 terms (hash-table-get ht #f '())
                 (hash-table-for-each
                   ht
                   (lambda (index preds)
                     (when index
                       (push! terms
                         (make <projected-unary-predicate>
                               :base (normalize-predicate (make-and preds))
                               :index index)))))
                 (make-and terms #t))]
            (if (is-a? (car rsp) <projected-unary-predicate>)
              (hash-table-update! ht (slot-ref (car rsp) 'argument-index)
                                  (lambda (v) (cons (slot-ref (car rsp) 'base) v))
                                  '())
              (hash-table-update! ht #f
                                  (lambda (v) (cons (car rsp) v))
                                  '())))))]))

;;
;; other
;;

(define-method normalize-predicate ((predicate <projected-unary-predicate>))
  (if (slot-ref predicate 'normal?)
    predicate
    (let ([make-cousin (lambda (new-base normal?)
                         (make <projected-unary-predicate>
                               :base new-base
                               :index (slot-ref predicate 'argument-index)
                               :normal? normal?))]
          [base (normalize-predicate (slot-ref predicate 'base))])
      (cond
        [(is-a? base <or-predicate>)
         (normalize-predicate
           (make-or (map (cut make-cousin <> #f) (slot-ref base 'subpreds))))]
        [(is-a? base <constant-predicate>)
         base]
        [else
          (make-cousin base #t)]))))

(define-method normalize-predicate ((predicate <extracting-unary-predicate>))
  (if (slot-ref predicate 'normal?)
    predicate
    (normalize-predicate
      (let ([make-cousin (lambda (new-base normal?)
                           (make <extracting-unary-predicate>
                                 :base new-base
                                 :accessors (slot-ref predicate 'accessors)
                                 :normal? normal?))]
            [base (normalize-predicate (slot-ref predicate 'base))])
        (cond
          [(is-a? base <or-predicate>)
           (make-or (map (cut make-cousin <> #f) (slot-ref base 'subpreds)))]
          [(is-a? base <and-predicate>)
           (make-and (map (cut make-cousin <> #f) (slot-ref base 'subpreds)))]
          [(is-a? base <constant-predicate>)
           base]
          [(is-a? base <not-predicate>)
           (make-not (make-cousin (slot-ref base 'base) #f))]
          [else
            (make-cousin base #t)])))))

(define (implies? pred1 pred2)
  (let1 norm (normalize-predicate (make-or (list (make-not pred1) pred2)))
    (and (constant-predicate? norm) (slot-ref norm 'value))))

(define (substitute newitem olditem list count)
  (let loop ([list list]
             [count count])
    (cond
      [(null? list)
       '()]
      [(equal? (car list) olditem)
       (if (< 1 count)
         (cons newitem (cdr list))
         (cons newitem (loop (cdr list) (- count 1))))]
      [else
        (cons (car list) (loop (cdr list) count))])))
