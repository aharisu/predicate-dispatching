(use predicate-dispatch)

(define-class <foo> () ())
(define-class <bar> () ())
(define-class <baz> (<bar>) ())

(define-pd-generic pd-test)
(add-pd-method! pd-test ((a <foo>) (b <bar>))
                ()
                (print "method <foo> <bar>"))
(add-pd-method! pd-test (a b)
                ((is-a? a <foo>) (is-a? b <baz>))
                (print "method <foo> <baz>")
                (next-method))

(print "(pd-test <foo> <bar>)")
(apply-pd-generic pd-test (make <foo>) (make <bar>))
(print "(pd-test <foo> <bar>)")
(apply-pd-generic pd-test (make <foo>) (make <baz>))


(define-pd-generic pd-eql-test)
(add-pd-method! pd-eql-test (a b)
                ((eql a 1))
                (print "method a=1"))
(add-pd-method! pd-eql-test (a b)
                ((eql a 1) (eql b 2))
                (print "method a=1 b=2")
                (next-method))

(print "(pd-eql-test 1 1)")
(apply-pd-generic pd-eql-test 1 1)
(print "(pd-eql-test 1 2)")
(apply-pd-generic pd-eql-test 1 2)

