#lang racket

;(require "PRIMPLIfier.rkt")
;(require "PRIMPL.rkt")
;(require test-engine/racket-tests)

(define label_nums 0)

(define num-vars 0)
(define var-start 0)

(define (get-name sym)
  (string->symbol (list->string (cons #\_ (string->list (symbol->string sym))))))

(define (get-new-label)
  (set! label_nums (+ 1 label_nums))
  (string->symbol (list->string (cons #\L (string->list (number->string (- label_nums 1)))))))

(define (get-data-stmts prg)
  (define vars (second prg))
  (set! num-vars (length vars))
  (for/list [(i vars)]
    (list 'data (get-name (first i)) (if (symbol? (second i)) (get-name (second i)) (second i)))))

(define exp-map
  (hash
   '+ 'add
   '- 'sub
   '* 'mul
   'div 'div
   'mod 'mod
   '> 'gt
   '< 'lt
   '>= 'ge
   '<= 'le
   '= 'equal
   'not 'lnot
   'and 'land
   'or 'lor
   ))

(define (compile-exp exp)
  (match exp
    [(? symbol? id) (list (list 'move '(0 SP) (get-name id))
                          (list 'add 'SP 'SP 1))]
    [(? number? val) (list (list 'move '(0 SP) val)
                           (list 'add 'SP 'SP 1))]
    [(? boolean? val) (list (list 'move '(0 SP) val)
                           (list 'add 'SP 'SP 1))]
    [(? (λ (instr) (symbol=? 'and (first instr))) ins) (define exps (rest ins))
                                                       (cond [(empty? exps) (compile-exp #t)]
                                                             [(empty? (rest exps)) (compile-exp (first exps))]
                                                             [else (define exp1-res (compile-exp (first exps)))
                                                                   (define rest-res (compile-exp (cons 'and (rest exps))))
                                                                   (define out (list (list 'land '(-2 SP) '(-2 SP) '(-1 SP))
                                                                                     '(sub SP SP 1)))
                                                                   (append exp1-res (append rest-res out))])]
    [(? (λ (instr) (symbol=? 'or (first instr))) ins) (define exps (rest ins))
                                                       (cond [(empty? exps) (compile-exp #f)]
                                                             [(empty? (rest exps)) (compile-exp (first exps))]
                                                             [else (define exp1-res (compile-exp (first exps)))
                                                                   (define rest-res (compile-exp (cons 'or (rest exps))))
                                                                   (define out (list (list 'lor '(-2 SP) '(-2 SP) '(-1 SP))
                                                                                     '(sub SP SP 1)))
                                                                   (append exp1-res (append rest-res out))])]
    [`(,cmd ,exp1 ,exp2) (define exp1-res (compile-exp exp1))
                      (define exp2-res (compile-exp exp2))
                      (define out (list (list (hash-ref exp-map cmd) '(-2 SP) '(-2 SP) '(-1 SP))
                                        '(sub SP SP 1)))
                      (append exp1-res (append exp2-res out))]
    [`(,cmd ,exp1) (define exp1-res (compile-exp exp1))
                      (define out (list (list (hash-ref exp-map cmd) '(-1 SP) '(-1 SP))))
                      (append exp1-res out)]))

(define (compile-iif exp stmt1 stmt2)
  (define exp-res (compile-exp exp))
  (define t-label (get-new-label))
  (define f-label (get-new-label))
  (define end-label (get-new-label))
  (define stmt1-res (append (list (list 'branch '(-1 SP) t-label)
                                  (list 'jump f-label)
                                  (list 'label t-label))
                            (compile-statement stmt1)))
  (define stmt2-res (append (list (list 'jump end-label)
                                  (list 'label f-label))
                            (append (compile-statement stmt2) (list (list 'sub 'SP 'SP 1)
                                                                    (list 'label end-label)))))
  (append exp-res (append stmt1-res stmt2-res)))

(define (compile-set var exp)
  (define exp-res (compile-exp exp))
  (define res (list (list 'move (get-name var) '(-1 SP))
                    (list 'sub 'SP 'SP 1)))
  (append exp-res res))

(define (compile-print exp)
  (cond [(string? exp) (list (list 'print-string exp))]
        [else (define res (compile-exp exp)) (append res (list (list 'print-val (list -1 'SP))
                                                               (list 'sub 'SP 'SP 1)))]))

(define (compile-seq stmts)
  (compile-stmts stmts))

(define (compile-while exp stmts)
  (define label-loop (get-new-label))
  (define exp-res (cons (list 'label label-loop) (compile-exp exp)))
  (define label-body (get-new-label))
  (define label-end (get-new-label))
  (define res (append (list (list 'branch '(-1 SP) label-body)
                            (list 'jump label-end)
                            (list 'label label-body))
                      (compile-stmts stmts)))
  (define close (list (list 'jump label-loop)
                      (list 'sub 'SP 'SP 1)
                      (list 'label label-end)))
  (append exp-res (append res close))
  )


(define (compile-statement stmt)
  (match stmt
    [`(skip) empty]
    [`(iif ,exp ,stmt1 ,stmt2) (compile-iif exp stmt1 stmt2)]
    [`(print ,exp) (compile-print exp)]
    [`(set ,var ,exp) (compile-set var exp)]
    [(? (λ (instr) (symbol=? 'seq (first instr))) ins) (compile-seq (rest ins))]
    [(? (λ (instr) (symbol=? 'while (first instr))) ins) (compile-while (second ins) (rest (rest ins)))]
    [x x])
  )

(define (compile-stmts stmts)
  (cond [(empty? stmts) empty]
        [else (append (compile-statement (first stmts))
                      (compile-stmts (rest stmts)))]))

(define (compile-simpl prg)
  (define var-list (second prg))
  (define stmts (rest (rest prg)))
  (define res (compile-stmts stmts))
  (define data-stmts (get-data-stmts prg))
  (define sp (+ (length res) (length data-stmts) 1))
  (append res (append (cons (list 'data 'SP sp) data-stmts))))


;; TESTING

(define prg1 '(vars [(A 2) (B 3) (C A)] (print (+ A B))))

(define prg2 '(vars [(A 2) (B 3)] (iif #f (print A) (print B))))

(define prg3 '(vars [(A 2) (B 3)] (iif #t (print A) (print B))))

(define prg4 '(vars [(A 2)] (seq (set A 10) (print A))))

(define prg5 '(vars [(x 10) (y 1)]
  (while (> x 0)
     (set y (* 2 y))
     (set x (- x 1))
     (print y)
     (print "\n"))))

(define prg6 '(vars [(x 1) (y 2)]
                    (iif (and (= x 1) (or (>= x 1) (<= y 1) #f #t) (and #t) (or (or ) (and ))) (print x) (print y))))

(define prg7 '(vars [(x 10) (y 1)]
  (while (> x 0)
     (set y (* 2 y))
     (set x (- x 1)))
  (print y)))

(define prg8 '(vars [(n 10) (fj 1) (fjm1 0) (t 0) (ans 0)]
   (iif (= n 0)
        (set ans fjm1)
        (seq
         (while (> n 1)
            (set t fj)
            (set fj (+ fj fjm1))
            (set fjm1 t)
            (set n (- n 1)))
         (set ans fj)))
   (print ans)))

(define prg9 '(vars [(x 2)] (iif (> x 2) (print x) (skip))))

(define prg prg9)
(define compiled (compile-simpl prg))
;compiled
;(load-primp (primplify compiled))
;(run-primp)

;(test)
