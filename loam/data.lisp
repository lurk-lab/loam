(declaim (optimize safety))

;; TODO:
;; - err

(in-package #:data)
(def-suite* data-suite :in loam:master-suite)

;; '(:nil :cons :sym :fun :num :str :char :comm :u64 :key :env :err :thunk :builtin :bignum)
(deflexical +tags+ (allocation-tag-names (make-instance 'lurk-allocation)))

(let ((builtin-package (find-package :lurk.builtin)))
  (defun* lurk-builtin-p ((s symbol))
    (eq (symbol-package s) builtin-package)))

;; Getting them via do-external-symbols doesn't preserve the order, so here we are...
(deflexical +builtins+
  (list 'lurk.builtin:atom
	'lurk.builtin:apply
	'lurk.builtin:begin
	'lurk.builtin:car
	'lurk.builtin:cdr
	'lurk.builtin:char
	'lurk.builtin:commit
	'lurk.builtin:comm
	'lurk.builtin:bignum
	'lurk.builtin:cons
	'lurk.builtin:current-env
	'lurk.builtin:emit
	'lurk.builtin:empty-env
	'lurk.builtin:eval
	'lurk.builtin:eq
	'lurk.builtin:eqq
	'lurk.builtin:type-eq
	'lurk.builtin:type-eqq
	'lurk.builtin:hide
	'lurk.builtin:if
	'lurk.builtin:lambda
	'lurk.builtin:let
	'lurk.builtin:letrec
	'lurk.builtin:u64
	'lurk.builtin:open
	'lurk.builtin:quote
	'lurk.builtin:secret
	'lurk.builtin:strcons
	'lurk.builtin:list
	'lurk.builtin:+
	'lurk.builtin:-
	'lurk.builtin:*
	'lurk.builtin:/
	'lurk.builtin:%
	'lurk.builtin:=
	'lurk.builtin:<
	'lurk.builtin:>
	'lurk.builtin:<=
	'lurk.builtin:>=
	'lurk.builtin:breakpoint
	'lurk.builtin:fail))

(loop for sym in +builtins+ for i from 0
      do (setf (get sym 'idx) i))

;; Forgive the heresy.
(defun builtin-idx (b) (get b 'idx))

;; bignum is reserved.
(deftype wide-num () '(unsigned-byte 256))

(defstruct (num (:constructor num (value)))
  (value 0 :type element))

(defstruct (comm (:constructor comm (secret value))) secret value)

;; TODO(winston): we use the 'nil-env symbol to represent the empty env and
;; hardcode a check for this when constructing envs.
;; This should be refactored to use an empty env struct, or a flag in the env struct,
;; since that removes potential symbol conflicts.
(deftype maybe-env () '(or symbol env))
(defstruct (env (:constructor env (key value next-env)))
  (key nil :type t) ; Key can be of type :sym, :builtin, or :coroutine.
  (value nil :type t)
  (next-env nil :type maybe-env))

(defstruct (thunk (:constructor thunk (body closed-env))) body (closed-env maybe-env))
(defstruct (fun (:constructor fun (args body closed-env)))
  (args nil :type list)
  (body nil :type t)
  (closed-env nil :type maybe-env))

(defun tag (thing)
  (etypecase thing
    (null :sym) ; nil is also a sym.
    (boolean :sym) ; nil and t are both sym.
    (cons :cons)
    (keyword :key)
    (symbol (if (eql 'nil-env thing)
		:env
		(if (lurk-builtin-p thing) :builtin :sym)))
    (num :num)
    ((unsigned-byte 64) :u64)
    (wide-num :bignum)
    (function :fun)
    (string :str)
    (character :char)
    (comm :comm)
    (thunk :thunk)
    (maybe-env :env)
    (fun :fun)))

;; size is number of elements, bits is bits per 'element'
(defun le-elements<- (x &key size (bits 8))
  (assert (<= bits +element-bits+))
  (let ((bytes (loop for i from 0
                     for n = x then (ash n (- bits))
                     while (or (> n 0) (and size (< i size)))
                     collect (ldb (byte bits 0) n))))
    (when size
      (assert (<= (length bytes) size)))
    ;; TODO: optimize. This implementation is just to figure out types.
    (make-array (length bytes) :initial-contents bytes :element-type 'element)))

(defun symbol-path (symbol)
  ;; All CL symbols have path of length 2 without hierarchical symbols.
  (list (symbol-name symbol) (package-name (symbol-package symbol))))

(defgeneric value<-expr (tag expr)
  (:method ((tag (eql :cons)) (x cons))
    (let ((car (intern-wide-ptr (car x)))
          (cdr (intern-wide-ptr (cdr x))))
      (hash (wide-ptr-tag car) (wide-ptr-value car) (wide-ptr-tag cdr) (wide-ptr-value cdr))))
  (:method ((tag (eql :comm)) (x comm))
    (let ((secret (value<-expr :bignum (comm-secret x)))
          (value (intern-wide-ptr (comm-value x))))
      (hash secret (wide-ptr-tag value) (wide-ptr-value value))))
  (:method ((tag (eql :sym)) (s symbol))
    (let ((str-tag-value (tag-value :str))
          (sym-tag-value (tag-value :sym)))
      (reduce (lambda (acc s)
                (hash str-tag-value (value<-expr :str s) sym-tag-value acc))
              (reverse (symbol-path s))
              :initial-value (widen 0))))
  (:method ((tag (eql :builtin)) (s symbol))
    (value<-expr :sym s))
  (:method ((tag (eql :key)) (s symbol))
    (value<-expr :sym s))
  (:method ((tag (eql :num)) (x num))
    (widen (num-value x)))
  (:method ((tag (eql :str)) (s string))
    (reduce (lambda (acc c)
              (hash (tag-value :char) (value<-expr :char c) (tag-value :str) acc))
            (reverse s)
            :initial-value (widen 0)))
  (:method ((tag (eql :char)) (c character))
    (make-wide :elements (le-elements<- (char-code c) :size 8)))
  (:method ((tag (eql :u64)) x)
    (make-wide :elements (le-elements<- x :size 8)))
  (:method ((tag (eql :bignum)) x)
    (make-wide :elements (le-elements<- x :size 8 :bits +element-bits+)))
  (:method ((tag (eql :env)) (x (eql 'nil-env)))
    (widen 0))
  (:method ((tag (eql :env)) (x env))
    (let ((env-key (intern-wide-ptr (env-key x)))
	  (env-value (intern-wide-ptr (env-value x))))
      (hash (wide-ptr-tag env-key)
	    (wide-ptr-value env-key)
	    (wide-ptr-tag env-value)
            (wide-ptr-value env-value)
	    (etypecase (env-next-env x)
              (env (wide-ptr-value (intern-wide-ptr (env-next-env x))))
              (symbol (widen 0))))))
  (:method ((tag (eql :thunk)) x)
    (let ((body (intern-wide-ptr (thunk-body x)))
          (closed-env (intern-wide-ptr (thunk-closed-env x))))
    (hash (wide-ptr-tag body) (wide-ptr-value body)
          (wide-ptr-tag closed-env) (wide-ptr-value closed-env))))
  (:method ((tag (eql :fun)) x)
    (let ((args (intern-wide-ptr (fun-args x)))
          (body (intern-wide-ptr (fun-body x)))
          (closed-env (intern-wide-ptr (fun-closed-env x))))
    (hash (wide-ptr-tag args) (wide-ptr-value args)
          (wide-ptr-tag body) (wide-ptr-value body)
          (wide-ptr-value closed-env)))))

(defgeneric expr<-wide (tag wide)
  (:method ((tag (eql :num)) (w wide))
    (assert (one-non-zero-limb-p w))
    (num (wide-nth 0 w)))
  (:method ((tag (eql :char)) (w wide))
    (assert (one-non-zero-limb-p w))
    (code-char (wide-nth 0 w)))
  (:method ((tag (eql :bignum)) (w wide))
      (reduce (lambda (acc elt) (+ (ash acc +element-bits+) elt))
              (reverse (wide-elements w))
              :initial-value 0))
  (:method ((tag (eql :u64)) (w wide))
    (reduce (lambda (acc elt) (+ (ash acc 8) elt))
            (reverse (wide-elements w))
            :initial-value 0))
  (:method ((tag (eql :cons)) (w wide))
    (destructuring-bind (car-tag car-value cdr-tag cdr-value)
        (unhash w)
      (cons (expr<-wide-ptr-parts car-tag car-value)
            (expr<-wide-ptr-parts cdr-tag cdr-value))))
  (:method ((tag (eql :comm)) (w wide))
    (destructuring-bind (secret val-tag val-value)
        (unhash w 3)
        (comm (expr<-wide :bignum secret) (expr<-wide-ptr-parts val-tag val-value))))
  (:method ((tag (eql :thunk)) (w wide))
    (destructuring-bind (body-tag body-value env-tag env-value)
        (unhash w 4)
        (thunk (expr<-wide-ptr-parts body-tag body-value) 
               (expr<-wide-ptr-parts env-tag env-value))))
  (:method ((tag (eql :fun)) (w wide))
    (destructuring-bind (args-tag args-value body-tag body-value env-value)
        (unhash w 5)
        (fun (expr<-wide-ptr-parts args-tag args-value)
             (expr<-wide-ptr-parts body-tag body-value)
             (expr<-wide-ptr-parts (tag-value :env) env-value))))
  (:method ((tag (eql :env)) (w wide))
    (if (wide-zero-p w)
	'nil-env
	(destructuring-bind (key-tag key-value val-tag val-value next-env)
            (unhash w 5)
	  (env (expr<-wide-ptr-parts key-tag key-value)
               (expr<-wide-ptr-parts val-tag val-value)
               (expr<-wide :env next-env)))))
  (:method ((tag (eql :str)) (w wide))
    (with-output-to-string (out)
      (loop while (not (wide-zero-p w))
            do (destructuring-bind (char-tag char-value rest-tag rest-value)
                   (unhash w)
                 (assert (== (tag-value :str) rest-tag))
                 (assert (== (tag-value :char) char-tag))
                 (let ((char (expr<-wide-ptr-parts char-tag char-value)))
                   (write-char char out)
                   (setq w rest-value))))))
  (:method ((tag (eql :sym)) (w wide))
    (let ((path (loop while (not (wide-zero-p w))
                      collect (destructuring-bind (string-tag string-value rest-tag rest-value)
                                  (unhash w)
                                (assert (== (tag-value :sym) rest-tag))
                                (assert (== (tag-value :str) string-tag))
                                (let ((name (expr<-wide-ptr-parts string-tag string-value)))
                                  (setq w rest-value)
                                  name)))))
      (assert (= 2 (length path))) ; for CL symbols, which aren't hierarchical
      (intern (car path) (find-package (cadr path)))))
  (:method ((tag (eql :key)) (w wide))
    (expr<-wide :sym w))
  (:method ((tag (eql :builtin)) (w wide))
    (expr<-wide :sym w)))

(defun wide-zero-p (wide) (every #'zerop (wide-elements wide)))
(defun one-non-zero-limb-p (wide) (every #'zerop (subseq (wide-elements wide) 1)))

(defun intern-wide-ptr (thing)
  (let* ((tag (tag thing))
         (value (value<-expr tag thing)))
    (make-wide-ptr (tag-value tag) value)))

(defun tag<-wide (wide)
  (nth-tag *program* (aref (wide-elements wide) 0)))

(defun expr<-wide-ptr-parts (wide-tag wide-value)
  (let ((tag (tag-name (tag<-wide wide-tag))))
    (expr<-wide tag wide-value)))

(defun expr<-wide-ptr (wide-ptr)
  (expr<-wide-ptr-parts (wide-ptr-tag wide-ptr) (wide-ptr-value wide-ptr)))

(defprogram test-program (hash-cache lurk-allocation)
  (relation (tag element wide)) ; (short-tag wide-tag)
  )

(test intern-wide-ptr
  (let ((*program* (make-program-instance 'test-program)))
    (is (== (make-wide-ptr (tag-value :sym)
                           (wide 281884145 1129688213 4120351968 327773871
				 384021070 117463301 2561106250 2236819005))
            (intern-wide-ptr nil)))
    #+nil(is (== (make-wide-ptr (tag-value :sym)
                           (wide 3513864683 4092952692 2311625634 434126079
				 1771964958 3138455192 216228261 3651295992))
            (intern-wide-ptr t)))
    (is (== (make-wide-ptr (tag-value :cons)
                           (wide 2469980295 1055013087 2071707850 3745798905
				 3182302750 3162655254 201317758 1580638714))
            (intern-wide-ptr (cons 123 456))))
    (is (== (make-wide-ptr (tag-value :sym)
                           (wide 4271245205 4041199923 139311603 1349105236
				 664727753 2939019886 3736723608 3286357898))
            (intern-wide-ptr 'asparagus)))
    (is (== (make-wide-ptr (tag-value :builtin)
                           (wide 3968199370 1224537180 3052128672 2224715904
				 3672658990 2925916735 1411103358 1335116285))
            (intern-wide-ptr 'lurk:current-env)))
    (is (== (make-wide-ptr (tag-value :num) (widen 987)) (intern-wide-ptr (num 987))))
    (is (== (make-wide-ptr (tag-value :str) (widen 0)) (intern-wide-ptr "")))
    (is (== (make-wide-ptr (tag-value :str) (wide 3076722117 4024338722 2289365418 698970534
						  3323852321 2245302033 976266832 315509495))
            (intern-wide-ptr "boo")))
    (is (== (make-wide-ptr (tag-value :char) (widen 65)) (intern-wide-ptr #\A)))
    (is (== (make-wide-ptr (tag-value :comm) (wide 311654523 2666201238 1854678539 1180780569
						   3514416075 3591153456 1110633005 2917630731))
            (intern-wide-ptr (comm 0 123))))
    (is (== (make-wide-ptr (tag-value :comm) (wide 1168834247 1827588988 2006807406 2556695211
						   2853839954 3698934260 4200172904 2878587015))
            (intern-wide-ptr (comm 1 123))))
    (is (== (make-wide-ptr (tag-value :comm) (wide 434704492 2111142387 1382466299 1563109978
						   294220625 1775261771 3288317254 2170675192))
            (intern-wide-ptr (comm 0 '(brass monkey)))))
    (is (== (make-wide-ptr (tag-value :u64) (widen 123)) (intern-wide-ptr 123)))
    (is (== (make-wide-ptr (tag-value :key)
                           (wide 1228499544 2092597812 598601078 363335323
				 111897536 3513321278 2999164444 2314684892))
            (intern-wide-ptr :asparagus)))
    (is (== (make-wide-ptr (tag-value :bignum)
                           (wide #xffffffff #xffffffff #xffffffff #xffffffff
                                 #xffffffff #xffffffff #xffffffff #xffffffff))
            (intern-wide-ptr (1- (expt 2 256)))))
    (is (== (make-wide-ptr (tag-value :bignum)
                           (wide #xfffffffe #xffffffff #xffffffff #xffffffff
                                 #xffffffff #xffffffff #xffffffff #xffffffff))
            ;; check endianness: the first limb should be affected.
            (intern-wide-ptr (- (expt 2 256) 2))))
    (is (== (make-wide-ptr (tag-value :cons)
                           (wide 3232492942 3172902725 3905286198 3869388357
				 3770444062 3474609343 2951998298 4004311820))
            (intern-wide-ptr `(foo (bar 1) (:baz #\x "monkey") ,(num 123) ,(1- (expt 2 256))))))
    (let* ((env1 (env 'a 123 'nil-env))
           (env2 (env 'b :xxx env1)))
      (is (== (make-wide-ptr (tag-value :env)
                             (wide 2064456524 2837991327 1206943432 1993810858
				   165399524 1338455424 3431677448 3424566788))
              (intern-wide-ptr env1)))
      (is (== (make-wide-ptr (tag-value :env)
                             (wide 3920784138 2081306664 3462857731 2435250064
				   1090130623 216254371 3470941065 2646990734))
              (intern-wide-ptr env2)))
      (is (== (make-wide-ptr (tag-value :thunk)
                             (wide 3496672372 2677663421 2116635234 3871946652
				   3542027988 2162033960 208146369 2711802215))
              (intern-wide-ptr (thunk '(we want the thunk) env2)))))
    (is (== (make-wide-ptr (tag-value :fun)
                           (wide 1760390733 1018055170 656655793 351132428
				 2417246066 1703544600 286035412 916394790))
            (intern-wide-ptr (fun '(a b c) '(+ a (* b c)) nil))))))

(test expr<-wide-ptr
  (let ((*program* (make-program-instance 'test-program)))
    (flet ((test-roundtrip (x)
             (is (== x (expr<-wide-ptr (intern-wide-ptr x))))))
      (test-roundtrip (num 123))
      (test-roundtrip (expt 2 100)) ; bignum
      (test-roundtrip 123456789) ; u64
      (test-roundtrip #\c)
      (test-roundtrip nil)
      (test-roundtrip '(1 . 2))
      (test-roundtrip '(1 2 (3 4)))
      (test-roundtrip 'a)
      (test-roundtrip :mango)
      ;; TODO: Revert back after restoring :env changes
      (let* ((env0 'nil-env)
	     (env1 (env 'a 123 env0))
             (env2 (env 'b "xxx" env1)))
        (test-roundtrip env0)
        (test-roundtrip env1)
        (test-roundtrip env2)
        (test-roundtrip (thunk '(give up the thunk) '((b . "xxx") (a . 123))))
        )
      (test-roundtrip "roundtrip")
      (test-roundtrip (comm 0 123))
      (test-roundtrip (fun '(a b c) '(+ a (* b c)) (env 'x 1 'nil-env)))
      (test-roundtrip 'lurk:lambda)
      (test-roundtrip '('lurk:cons 1 2)))))
