(use predicate-dispatch)
(use predicate-dispatch.classes)
(use predicate-dispatch.normalize)
(use predicate-dispatch.print)

(define (tp x)
  (<= x 17))

(define (tq x)
  (>= x 17))

(define (tr x)
  (> (sin x) 0))

(define (mkand :rest l)
  (make-and l))

(define (mkor :rest l)
  (make-or l))

(define (mknot p)
  (make-not p))

(define (printnorm p)
  (print "Orig:" p)
  (print "Norm:" (normalize-predicate p)))

(let ([p (make <test-predicate> :test tp)]
      [q (make <test-predicate> :test tq)]
      [r (make <test-predicate> :test tr)])
  (map
    printnorm
    (list (mkor (mkand p q)
                (mkand p (mknot q))
                (mkand (mknot p) q)
                (mkand (mknot p) (mknot q)))
          (mkor (mkand p q r)
                (mknot p)
                (mknot q)
                (mknot r))
          (mkor (mkand p q)
                (mkand (mknot q) r)
                (mkand (mknot r) (mknot p))
                (mkand p (mknot q) (mknot r))
                (mkand (mknot p) q r))
          )))

