#lang rosette

;;; a quick and dirty verifier for our BV language.

(define env (make-hash))

(define MAX_BITWIDTH 4)

(define (bvlang->rosette expr)
  (match expr
    [`(ValueWidth ,x) (hash-ref! env x (lambda () (begin (define-symbolic* x integer?) (assume (&& (> x 0) (<= x MAX_BITWIDTH))) x)))]
    [`(ValueVar   ,x) (hash-ref! env x (lambda () (begin (define-symbolic* x integer?) (assume (&& (>= x 0) (<= x (- (expt 2 MAX_BITWIDTH) 1)))) x)))] 
    [`(Bitvector ,bw ,val) (let ([bw (bvlang->rosette bw)] [val (bvlang->rosette val)])
                               (bv 4 (modulo val bw)))]))

(bvlang->rosette `(ValueWidth p))
(bvlang->rosette `(ValueVar a))
(bvlang->rosette `(ValueVar b))
(bvlang->rosette `(Bitvector (ValueWidth p) (ValueVar a)))


(solve env)
(displayln (format "env: ~a" env))

