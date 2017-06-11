(define (not x)        (if x #f #t))
(define (null? obj)    (if (eqv? obj '()) #t #f))
(define (list . objs)  objs)
(define (id obj)       obj)
(define (flip func)    (lambda (arg1 arg2) (func arg2 arg1)))
(define (curry func arg1) (lambda (arg) (apply func (cons arg1 (list arg)))))
(define (compose f g)  (lambda (arg) (f (apply g arg))))

(define zero?       (curry = 0))
(define positive?   (curry < 0))
(define negative?   (curry > 0))
(define (odd? num)  (= (remainder num 2) 1))
(define (even? num) (= (remainder num 2) 0))

(define (foldr func end lst)
  (if (null? lst)
      end
      (func (car lst) (foldr func end (cdr lst)))))

(define (foldl func acc lst)
  (if (null? lst)
      acc
      (foldl func (func acc (car lst)) (cdr lst))))

(define fold foldl)
(define reduce foldr)

(define (unfold func init pred)
  (if (pred init)
      (cons init '())
      (cons init (unfold func (func init) pred))))

(define (sum . lst)      (fold + 0 lst))
(define (product . lst)  (fold * 1 lst))
(define (and . lst)      (fold && #t lst))
(define (or . lst)       (fold || #f lst))

(define (max first . rest)
        (fold (lambda (old new) (if (> old new) old new)) first rest))
(define (min first . rest)
        (fold (lambda (old new) (if (< old new) old new)) first rest))

(define (length lst) (fold (lambda (x y) (+ x 1)) 0 lst))

(define (reverse lst) (fold (flip cons) '() lst))

(define (mem-helper pred op)
        (lambda (acc next) (if (and (not acc) (pred (op next))) next acc)))
(define (memq obj lst) (fold (mem-helper (curry eq? obj) id) #f lst))
(define (memv obj lst) (fold (mem-helper (curry eqv? obj) id) #f lst))
(define (assq obj lst) (fold (mem-helper (curry eq? obj) car) #f lst))
(define (assv obj lst) (fold (mem-helper (curry eqv? obj) car) #f lst))

(define (map func lst) (foldr (lambda (x xs) (cons (func x) xs) '() lst)))
(define (filter pred lst)
        (foldr (lambda (x xs) (if (pred x) (cons x xs) xs)) '() lst))


