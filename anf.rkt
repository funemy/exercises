;; a direct comparison between anf and monadic transformation
#lang racket

(require racket/pretty)

(define prog
  `(+ (+ a b)
      (+ (+ c d) e)))

(define (monadic p)
  (match p
    [`(+ ,triv1 ,triv2)
      (monadic-triv triv1
           (lambda (t1)
             (monadic-triv triv2
                       (lambda (t2) `(+ ,t1 ,t2)))))]
    [(? symbol?) p]))

(define (monadic-triv v k)
  (match v
    [(? symbol?) (k v)]
    [_
      (let ([t (gensym "tmp")])
        `(let ([,t ,(monadic v)])
           ,(k t)))]))

(define (anf^ p k)
  (match p
    [`(+ ,triv1 ,triv2)
      (anf-triv
        triv1
        (lambda (t1)
          (anf-triv
            triv2
            (lambda (t2)
              (k `(+ ,t1 ,t2))))))]
    [(? symbol?)
     (k p)]))

(define (anf-triv v k)
  (match v
    [(? symbol?)
     (k v)]
    [_
      (let ([t (gensym "tmp")])
        (anf^
          v
          (lambda (t1)
            `(let ([,t ,t1])
               ,(k t)))))]))


(define (anf p)
  (anf^ p (lambda (x) x)))

(pretty-print (monadic prog))
(pretty-print (anf prog))
