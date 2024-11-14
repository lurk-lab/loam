(declaim (optimize safety))64;84;34M;22M

(in-package #:evaluation)
(def-suite* evaluation-suite :in loam:master-suite)

(defconstant +wide-size+ 8)
(defconstant +element-bytes+ 4)
(defconstant +element-bits+ (* 8 +element-bytes+))

(defun prog-trace (&rest args)
  (display args))

(defprogram ptr-program (lurk-allocation)
  (relation (tag element wide)) ; (short-tag wide-tag)

  ;; It may be confusing that this relation has the same name as the ptr struct's value accessor, since the struct's field is not wide.
  (relation (ptr-value ptr wide)) ; (ptr value)

  (relation (alloc element wide)) ; (tag value)

  (relation (toplevel-input wide-ptr wide-ptr)) ; (wide-ptr)
  (relation (output-expr wide-ptr)) ; (wide-ptr)
  (relation (input-ptr ptr ptr)) ; (ptr)
  (relation (output-ptr ptr)) ; (ptr)

  (relation (ingress ptr)) ; (ptr)
  (relation (egress ptr)) ; (ptr)

  (rule (alloc expr-tag expr-value) (alloc env-tag env-value) <--
    (toplevel-input expr env)
    (let ((expr-tag (wide-nth 0 (wide-ptr-tag expr)))
	  (expr-value (wide-ptr-value expr))
	  (env-tag (wide-nth 0 (wide-ptr-tag env)))
	  (env-value (wide-ptr-value env)))))

  (rule (input-ptr expr-ptr env-ptr) <--
    (toplevel-input expr env)
    (ptr-value expr-ptr (wide-ptr-value expr))
    (ptr-value env-ptr (wide-ptr-value env))
    (when (and (== (ptr-tag expr-ptr) (wide-nth 0 (wide-ptr-tag expr)))
	       (== (ptr-tag env-ptr) (wide-nth 0 (wide-ptr-tag env)))
	       )))

  ;; Egress
  (rule (egress ptr) <-- (output-ptr ptr))

  ;; Construct output-expr from output-ptr
  (rule (output-expr (make-wide-ptr (widen (ptr-tag ptr)) value)) <--
    (output-ptr ptr)
    (ptr-value ptr value)
    #+nil(let ((x (prog-trace 'output-expr ptr))))))

;; hash-cache takes precedence over program in superclass list
(defprogram hash4 (hash-cache)
  (include ptr-program)
  (relation (hash4 wide wide wide wide)) ; (a b c d)
  (relation (unhash4 wide)) ; (digest)
  (relation (hash4-rel wide wide wide wide wide)) ; (a b c d digest)
  
  ;; signal
  (rule (alloc (wide-nth 0 a-tag) a-value) (alloc (wide-nth 0 b-tag) b-value) <--
    (unhash4 digest)
    (hash4-rel a-tag a-value b-tag b-value digest)))

;; hash-cache takes precedence over program in superclass list
(defprogram hash5 (hash-cache)
  (include ptr-program)
  (relation (hash5 wide wide wide wide wide)) ; (a b c d e)
  (relation (unhash5 wide)) ; (digest)
  (relation (hash5-rel wide wide wide wide wide wide)) ; (a b c d e digest)
  
  ;; signal
  ;; FIXME: We assume that the c-tag must be a :cons.
  (rule (alloc (wide-nth 0 a-tag) a-value) (alloc (wide-nth 0 b-tag) b-value) (alloc (tag-address :cons) c-value) <--
    (unhash5 digest)
    (hash5-rel a-tag a-value b-tag b-value c-value digest)))

(defprogram cons-mem (hash-cache)
  (include ptr-program)
  (include hash4)

  ;; The following relations could be determined by something like:
  ;; (constructor cons (:cons 0 hash4) (car ptr) (cdr ptr))
  ; signal
  (relation (cons ptr ptr)) ; (car cdr)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;; Memory

  ;; The canonical cons Ptr relation.
  (relation (cons-rel ptr ptr ptr)) ; (car cdr cons)

  ;; Memory to support conses allocated by digest or contents.
  (lattice (cons-digest-mem wide dual-element)) ; (digest addr)
  (lattice (cons-mem ptr ptr dual-element)) ; (car cdr addr)

  ;; Populating alloc(...) triggers allocation in cons-digest-mem.
  (rule (cons-digest-mem value  (alloc :cons (dual 0))) <--
    (alloc (tag-address :cons) value))

  ;; Populating cons(...) triggers allocation in cons-mem.
  (rule (cons-mem car cdr (alloc :cons (dual 0))) <-- (cons car cdr))

  ;; Populate cons-digest-mem if a cons in cons-mem has been hashed in hash4-rel.
  (rule (cons-digest-mem digest addr) <--
    (cons-mem car cdr addr)
    (ptr-value car car-value) (ptr-value cdr cdr-value)
    (hash4-rel (widen (ptr-tag car)) car-value (widen (ptr-tag cdr)) cdr-value digest))

  ;; Other way around.
  (rule (cons-mem car cdr addr) <--
    (cons-digest-mem digest addr)
    (hash4-rel car-tag car-value cdr-tag cdr-value digest)
    (ptr-value car car-value) (ptr-value cdr cdr-value)
    (when (and (== (ptr-tag car) (wide-nth 0 car-tag))
	       (== (ptr-tag cdr) (wide-nth 0 cdr-tag)))))

  ;; Register a cons value.
  (rule (ptr-value cons value) <--
    (cons-digest-mem value addr) (let ((cons (ptr :cons (dual-value addr))))))

  ;; Register a cons relation.
  (rule (cons-rel car cdr cons) <--
    (cons-mem car cdr addr)
    (let ((cons (ptr :cons (dual-value addr))))))

  ;; signal
  (rule (unhash4 digest) <--
    (ingress ptr) (when (has-tag-p ptr :cons)) (ptr-value ptr digest))

  ;; signal
  (rule (hash4 car-tag car-value cdr-tag cdr-value) <--
    (egress cons)
    (cons-rel car cdr cons)
    (let ((car-tag (widen (ptr-tag car)))
	  (cdr-tag (widen (ptr-tag cdr)))))
    (ptr-value car car-value) (ptr-value cdr cdr-value)
    #+nil(let ((x (prog-trace 'hash4-cons car-tag car-value cdr-tag cdr-value))))
    )

  ;; signal
  (rule (egress car) (egress cdr) <--
    (egress cons) (cons-rel car cdr cons)))

;; FIXME: Align with Lurk by dropping closed-env-tag in the hash.
(defprogram thunk-mem (hash-cache)
  (include ptr-program)
  (include hash4)

  ; signal
  (relation (thunk ptr ptr)) ; (body closed-env)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;; Memory

  ;; The canonical thunk Ptr relation.
  (relation (thunk-rel ptr ptr ptr)) ; (body closed-env thunk)

  ;; Memory to support thunks allocated by digest or contents.
  (lattice (thunk-digest-mem wide dual-element)) ; (digest addr)
  (lattice (thunk-mem ptr ptr dual-element)) ; (body closed-env addr)

  ;; Populating alloc(...) triggers allocation in thunk-digest-mem.
  (rule (thunk-digest-mem value  (alloc :thunk (dual 0))) <--
    (alloc (tag-address :thunk) value))

  ;; Populating thunk(...) triggers allocation in thunk-mem.
  (rule (thunk-mem body closed-env (alloc :thunk (dual 0))) <-- (thunk body closed-env))

  ;; Populate thunk-digest-mem if a thunk in thunk-mem has been hashed in hash4-rel.
  (rule (thunk-digest-mem digest addr) <--
    (thunk-mem body closed-env addr)
    (ptr-value body body-value) (ptr-value closed-env closed-env-value)
    (hash4-rel (widen (ptr-tag body)) body-value (widen (ptr-tag closed-env)) closed-env-value digest))

  ;; Other way around.
  (rule (thunk-mem body closed-env addr) <--
    (thunk-digest-mem digest addr)
    (hash4-rel body-tag body-value closed-env-tag closed-env-value digest)
    (ptr-value body body-value) (ptr-value closed-env closed-env-value)
    (when (and (== (ptr-tag body) (wide-nth 0 body-tag))
	       (== (ptr-tag closed-env) (wide-nth 0 closed-env-tag)))))

  ;; Register a thunk value.
  (rule (ptr-value thunk value) <--
    (thunk-digest-mem value addr) (let ((thunk (ptr :thunk (dual-value addr))))))

  ;; Register a thunk relation.
  (rule (thunk-rel body closed-env thunk) <--
    (thunk-mem body closed-env addr)
    (let ((thunk (ptr :thunk (dual-value addr))))))

  ;; signal
  (rule (unhash4 digest) <--
    (ingress ptr) (when (has-tag-p ptr :thunk)) (ptr-value ptr digest))

  ;; signal
  (rule (hash4 body-tag body-value closed-env-tag closed-env-value) <--
    (egress thunk)
    (thunk-rel body closed-env thunk)
    (let ((body-tag (widen (ptr-tag body)))
	  (closed-env-tag (widen (ptr-tag closed-env)))))
    (ptr-value body body-value) (ptr-value closed-env closed-env-value)))

(defprogram fun-mem (hash-cache)
  (include ptr-program)
  (include hash5)

  ; signal
  (relation (fun ptr ptr ptr)) ; (args body closed-env)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;; Memory

  ;; The canonical fun Ptr relation.
  (relation (fun-rel ptr ptr ptr ptr)) ; (args body closed-env fun)

  ;; Memory to support funs allocated by digest or contents.
  (lattice (fun-digest-mem wide dual-element)) ; (digest addr)
  (lattice (fun-mem ptr ptr ptr dual-element)) ; (args body closed-env addr)

  ;; Populating alloc(...) triggers allocation in fun-digest-mem.
  (rule (fun-digest-mem value (alloc :fun (dual 0))) <--
    (alloc (tag-address :fun) value))

  ;; Populating fun(...) triggers allocation in fun-mem.
  (rule (fun-mem args body closed-env (alloc :fun (dual 0))) <--
    (fun args body closed-env)
    )

  ;; Populate fun-digest-mem if a fun in fun-mem has been hashed in hash5-rel.
  (rule (fun-digest-mem digest addr) <--
    (fun-mem args body closed-env addr)
    (ptr-value args args-value) (ptr-value body body-value) (ptr-value closed-env closed-env-value)
    (hash5-rel (widen (ptr-tag args)) args-value (widen (ptr-tag body)) body-value closed-env-value digest))

  ;; Other way around.
  (rule (fun-mem args body closed-env addr) <--
    (fun-digest-mem digest addr)
    (hash5-rel args-tag args-value body-tag body-value closed-env-value digest)
    (ptr-value args args-value)
    (ptr-value body body-value)
    (ptr-value closed-env closed-env-value)
    (when (and (== (ptr-tag args) (wide-nth 0 args-tag))
	       (== (ptr-tag body) (wide-nth 0 body-tag))
	       ))) ; FIXME: Check env tag.

  ;; Register a fun value.
  (rule (ptr-value fun value) <--
    (fun-digest-mem value addr) (let ((fun (ptr :fun (dual-value addr)))))
    #+nil(let ((x (prog-trace 'fun-ptr-value)))))

  ;; Register a fun relation.
  (rule (fun-rel args body closed-env fun) <--
    (fun-mem args body closed-env addr)
    (let ((fun (ptr :fun (dual-value addr))))))

  ;; signal
  (rule (unhash5 digest) <--
    (ingress ptr) (when (has-tag-p ptr :fun)) (ptr-value ptr digest))

  ;; signal
  (rule (hash5 args-tag args-value body-tag body-value closed-env-value) <--
    (egress fun)
    (fun-rel args body closed-env fun)
    (let ((args-tag (widen (ptr-tag args)))
	  (body-tag (widen (ptr-tag body)))))
    (ptr-value args args-value)
    (ptr-value body body-value)
    (ptr-value closed-env closed-env-value))

  ;; signal
  (rule (egress args) (egress body) (egress closed-env) <--
    (egress fun) (fun-rel args body closed-env fun)))

(defparameter *initial-sym-addr* 2)

(defprogram sym-mem ()
  (include ptr-program)

  (lattice (sym-digest-mem wide dual-element))

  ;; Populating alloc(...) triggers allocation in sym-digest-mem.
  (rule (sym-digest-mem value (alloc :sym (dual *initial-sym-addr*))) <--
    (alloc (tag-address :sym) value))

  ;; Register a sym value.
  (rule (ptr-value sym value) <--
    (sym-digest-mem value addr) (let ((sym (ptr :sym (dual-value addr)))))
    #+nil(let ((x (prog-trace 'sym-ptr-value sym addr))))))

(defparameter *initial-builtin-addr* 41)

(defprogram builtin-mem (hash-cache)
  (include ptr-program)

  (lattice (builtin-digest-mem wide dual-element))

  ;; Populating alloc(...) triggers allocation in builtin-digest-mem.
  #+nil
  (rule (builtin-digest-mem value (alloc :builtin (dual *initial-builtin-addr*))) <--
    (alloc (tag-address :builtin) value)
    (let ((x (prog-trace 'fire-this-rule)))))

  ;; Register a builtin value.
  (rule (ptr-value builtin value) <--
    (builtin-digest-mem value addr) (let ((builtin (ptr :builtin (dual-value addr)))))
    ))

(defprogram immediate-num ()
  (include ptr-program)
  ;; real
  (rule (ptr-value ptr value) <--
    (alloc tag value)
    (when (is-tag-p tag :num))
    (let ((ptr (ptr :num (wide-nth 0 value)))))
    )

  (rule (ptr-value ptr value) <--
    (egress ptr) (when (has-tag-p ptr :num))
    (let ((value (widen (ptr-value ptr)))))))

;; FIXME for PQ: This is a hack for binding a value in a relation.
;; When I just write a '0', I get something like: 'etypecase failed, expected one of SYMBOL or DATALOG:VAL-FORM'.
;; (defun zero () 0)

;; The Lurk evaluation.
(defprogram evaluation (hash-cache)
  (include ptr-program)
  (include cons-mem)
  (include thunk-mem)
  (include fun-mem)
  (include sym-mem)
  (include builtin-mem)
  (include immediate-num)

  ;; Generate the necessary signal relations

  ;; Input and output.
  (signal-relation (input-output (expr env evaled) (input-ptr expr env) (output-ptr evaled)))

  ;; Eval signals.
  (relation (eval-input ptr ptr))
  (relation (eval ptr ptr ptr))
  (signal-relation (signal-eval (expr env evaled) (eval-input expr env) (eval expr env evaled)))

  (relation (lookup-input ptr ptr))
  (relation (lookup ptr ptr ptr))
  (signal-relation (signal-lookup (var env value) (lookup-input var env) (lookup var env value)))

  (relation (eval-bindings-input ptr ptr boolean))
  (relation (eval-bindings ptr ptr boolean ptr))
  (signal-relation (signal-eval-bindings (bindings env is-rec extended-env)
		    (eval-bindings-input bindings env is-rec)
		    (eval-bindings bindings env is-rec extended-env)))

  #+nil
  (relation (fold-left-input ptr ptr element ptr))
  #+nil
  (relation (fold-left ptr ptr element ptr element))
  #+nil
  (signal-relation (signal-fold-left (env op initial args result)
		    (fold-left-input env op initial args)
		    (fold-left env op initial args result)))

  (relation (eval-binop-input ptr ptr ptr)) ; (env op args)
  (relation (eval-binop ptr ptr ptr element))
  (signal-relation (signal-eval-binop (env op args result)
		    (eval-binop-input env op args)
		    (eval-binop env op args result)))

  (relation (funcall-input ptr ptr ptr ptr ptr))
  (relation (funcall ptr ptr ptr ptr ptr ptr))
  (signal-relation (signal-funcall (args body closed-env values outer-env result)
		    (funcall-input args body closed-env values outer-env)
		    (funcall args body closed-env values outer-env result)))

  ;; Cons signals.
  (signal-relation (ingress-cons (car cdr cons) (ingress cons) (cons-rel car cdr cons)))
  (signal-relation (signal-cons (car cdr cons) (cons car cdr) (cons-rel car cdr cons)))

  ;; Thunk signals.
  (signal-relation (ingress-thunk (body closed-env thunk)
		    (ingress thunk)
		    (thunk-rel body closed-env thunk)))
  (signal-relation (signal-thunk (body closed-env thunk)
		    (thunk body closed-env)
		    (thunk-rel body closed-env thunk)))

  ;; Fun signals.
  (signal-relation (ingress-fun (args body closed-env fun)
		    (ingress fun)
		    (fun-rel args body closed-env fun)))
  (signal-relation (signal-fun (args body closed-env fun)
		    (fun args body closed-env)
                    (fun-rel args body closed-env fun)))

  ;; The hashing rules below are due to a design restriction of the hash-cache.
  ;; Because the hash-cache is local to the subprogram it is defined from,
  ;; when we intern the input and env in the outermost scope, we hash into the
  ;; local hash-cache of the evaluation program instead.

  ;; signal
  (rule (hash4-rel a b c d digest) <--
    (unhash4 digest)
    (let ((preimage (unhash digest 4))
          (a (nth 0 preimage))
          (b (nth 1 preimage))
          (c (nth 2 preimage))
          (d (nth 3 preimage))
	  #+nil(x (prog-trace 'signal-unhash4 a b c d digest)))))
  
  ;; signal
  (rule (hash4-rel a b c d digest) <--
    (hash4 a b c d)
    (let ((digest (hash a b c d))
	  #+nil(x (prog-trace 'signal-hash4 a b c d digest)))))

  ;; signal
  (rule (hash5-rel a b c d e digest) <--
    (unhash5 digest)
    (let ((preimage (unhash digest 5))
          (a (nth 0 preimage))
          (b (nth 1 preimage))
          (c (nth 2 preimage))
          (d (nth 3 preimage))
	  (e (nth 4 preimage)))))

  ;; signal
  (rule (hash5-rel a b c d e (hash a b c d e)) <-- (hash5 a b c d e))

  ;; Connect eval to input/output.
  (synthesize-rule (input-output expr env evaled) <-- (signal-eval expr env evaled))

  (synthesize-rule (signal-eval expr env evaled) <--
    (cond
      ;; Self-evaluating forms.
      ((has-tag-p expr :num) ((let ((evaled expr)))))
      ((has-tag-p expr :err) ((let ((evaled expr)))))
      ((is-nil expr) ((let ((evaled expr)))))
      ((is-t expr) ((let ((evaled expr)))))
      ((has-tag-p expr :sym) ((signal-lookup expr env evaled)))

      ;; Interesting cons case:
      ((has-tag-p expr :cons)
       ((ingress-cons head rest expr)
	(cond
	  ;; Evaluate cons operator.
	  #+nil
	  ((== head (builtin-ptr 'cons)) ((ingress-cons car tail rest)
					  (ingress-cons cdr end tail)
					  (when (is-nil end))
					  (signal-eval car env evaled-car)
					  (signal-eval cdr env evaled-cdr)
					  (signal-cons car cdr evaled)))
	  ;; Evaluate if.
	  ((== head (builtin-ptr 'lurk:if)) ((ingress-cons cond branches rest)
					     (signal-eval cond env evaled-cond)
					     (ingress-cons a more branches)
					     (if (is-nil evaled-cond)
						 ((ingress-cons b end more)
						  (when (is-nil end))
						  (signal-eval b env evaled))
						 ((signal-eval a env evaled)))))
	  ;; Evaluate let/letrec.
	  ((or (== head (builtin-ptr 'lurk:let)) (== head (builtin-ptr 'lurk:letrec)))
	       ((ingress-cons bindings tail rest)
		(ingress-cons body end tail)
		(when (is-nil end))
		(signal-eval-bindings bindings env (== head (builtin-ptr 'lurk:letrec)) extended-env)
		(signal-eval body extended-env evaled)))
	  ;; Evaluate lambda.
	  ((== head (builtin-ptr 'lurk:lambda)) ((ingress-cons args tail rest)
						 (ingress-cons body end tail)
						 (when (is-nil end))
						 (signal-fun args body env evaled)))
	  ;; Evaluate binop. FIXME: Return to variadic implementation later. Just tryna make this work.
	  ((is-binop head) ((signal-eval-binop env head rest evaled)))
	  ;; Evaluate +. FIXME: Generalize to more ops.
	  #+nil
	  ((== head (builtin-ptr 'lurk:+)) ((signal-fold-left env head (zero) rest acc)
					    (let ((evaled (ptr :num acc))))))
	  ;; Evaluate =. FIXME: Generalize to more ops and bool-fold.
	  #+nil
	  ((== head (builtin-ptr 'lurk:=)) ((ingress-cons arg1 tail rest)
					    (ingress-cons arg2 end tail)
					    (when (and (is-nil end) (has-tag-p arg1 :num) (has-tag-p arg2 :num)))
					    (if (== arg1 arg2)
						((let ((evaled *ptr-t*))))
						((let ((evaled *ptr-nil*)))))))
	  ;; Evaluate function.
	  ((has-tag-p head :fun) ((ingress-fun args body closed-env head)
				  (signal-funcall args body closed-env rest env evaled)))
	  ((and (not (has-tag-p head :fun)) (not (has-tag-p head :builtin)))
	   ((signal-eval head env fun)
	    (ingress-fun args body closed-env fun)
	    (signal-funcall args body closed-env rest env evaled)))
	  
	  )))))

  ;; FIXME: Error case when no lookup is found.
  (synthesize-rule (signal-lookup var env value) <--
    (ingress-cons binding more-env env)
    (ingress-cons bound-var bound-value binding)
    (if (== var bound-var)
	((if (has-tag-p bound-value :thunk)
	     ;; If the looked-up value is a thunk.
	     ((ingress-thunk body closed-env bound-value)
	      (signal-cons binding closed-env extended-env)
	      (signal-eval body extended-env value))
	     ((let ((value bound-value)))))) ;; Is this efficient? No... but it works.
	((signal-lookup var more-env value))))

  (synthesize-rule (signal-eval-bindings bindings extended-env is-rec final-env) <--
    (if (is-nil bindings)
	((let ((final-env extended-env))))
	((ingress-cons binding more-bindings bindings)
	 (ingress-cons var binding-tail binding)
	 (ingress-cons unevaled end binding-tail)
	 (when (is-nil end))
	 (if is-rec
	     ;; Recursive case: make a thunk.
	     ((signal-thunk unevaled extended-env thunk)
	      (signal-cons var thunk env-binding)
	      (signal-cons env-binding extended-env new-env)
	      (signal-eval-bindings more-bindings new-env is-rec final-env))
	     ;; Non-recursive case: just evaluate.
	     ;; FIXME: There's unfortunate duplication here, change synthesis so that `if/case/cond`
	     ;; don't have to be the final segment. Kind of a headache.
	     ((signal-eval unevaled extended-env evaled)
	      (signal-cons var evaled env-binding)
	      (signal-cons env-binding extended-env new-env)
	      (signal-eval-bindings more-bindings new-env is-rec final-env)))
	 )))

  (synthesize-rule (signal-eval-binop env op args result) <--
    (ingress-cons arg1 more-args args)
    (ingress-cons arg2 end more-args)
    (when (is-nil end))
    (signal-eval arg1 env evaled1)
    (signal-eval arg2 env evaled2)
    (when (and (has-tag-p evaled1 :num) (has-tag-p evaled2 :num)))
    (let ((result (eval-binop op evaled1 evaled2))))
    )
    

  #+nil
  (synthesize-rule (signal-fold-left env op initial args result) <--
    (if (is-nil args)
	((let ((result initial))))
	((ingress-cons arg more-args args)
	 (signal-eval arg env evaled-arg)
	 (when (has-tag-p evaled-arg :num))
	 (signal-fold-left env op initial more-args acc)
	 (let ((result (cond ;; Slightly annoying thing: case doesn't produce == and incorrectly checks ptr equality.
			 ((== op (builtin-ptr 'lurk:+)) (+ (ptr-value evaled-arg) acc)))))))))

  (synthesize-rule (signal-funcall args body closed-env values outer-env result) <--
    (if (and (is-nil args) (is-nil values))
	((signal-eval body closed-env result))
	((ingress-cons arg more-args args)
	 (ingress-cons unevaled more-values values)
	 (signal-eval unevaled outer-env evaled)
	 (signal-cons arg evaled binding)
	 (signal-cons binding closed-env new-closed-env)
	 (signal-funcall more-args body new-closed-env more-values outer-env result))))
  )

(defparameter *ptr-nil* (make-ptr 10 0))
(defparameter *ptr-t* (make-ptr 10 1))

(defun is-nil (ptr) (== ptr *ptr-nil*))
(defun is-t (ptr) (== ptr *ptr-t*))

(defun lurk-bool (bool)
  (if bool *ptr-t* *ptr-nil*))

(defun builtin-ptr (sym)
  (make-ptr 8 (builtin-idx sym)))

(defun is-binop (op)
  (or (== op (builtin-ptr 'lurk:+))
      (== op (builtin-ptr 'lurk:-))
      (== op (builtin-ptr 'lurk:*))
      (== op (builtin-ptr 'lurk:=))
      (== op (builtin-ptr 'lurk:<))
      (== op (builtin-ptr 'lurk:>))))

(defun eval-binop (op arg1 arg2)
  (cond
    ((== op (builtin-ptr 'lurk:+)) (make-ptr 1 (+ (ptr-value arg1) (ptr-value arg2))))
    ((== op (builtin-ptr 'lurk:-)) (make-ptr 1 (- (ptr-value arg1) (ptr-value arg2))))
    ((== op (builtin-ptr 'lurk:*)) (make-ptr 1 (* (ptr-value arg1) (ptr-value arg2))))
    ((== op (builtin-ptr 'lurk:=)) (lurk-bool (== arg1 arg2)))
    ((== op (builtin-ptr 'lurk:<)) (lurk-bool (< (ptr-value arg1) (ptr-value arg2))))
    ((== op (builtin-ptr 'lurk:>)) (lurk-bool (> (ptr-value arg1) (ptr-value arg2))))
    ))

(defun initial-sym-digest-mem ()
    (loop for sym in (list nil t)
	  for i from 0
	  for sym-value = (wide-ptr-value (intern-wide-ptr sym))
	  collect (list sym-value (dual i))))

(defun initial-builtin-digest-mem ()
  (loop for b in +builtins+
	for i from 0
	for builtin-value = (wide-ptr-value (intern-wide-ptr b))
	collect (list builtin-value (dual i))))

(defun display-relation (program relation)
  (let ((x (find-relation program relation)))
    (display relation (relation-tuple-list x))))

;; Smoke test for catching regressions on the builtin issue.
(test intern-builtin
  (let* ((program (make-program-instance 'builtin-mem))
	 (*program* program)
	 ; (src (spec (find-prototype 'builtin-mem)))
   )
    (init program `(builtin-digest-mem ,(initial-builtin-digest-mem)))
    (run program)
    ))

(defun test-aux (input env expected-output)
  (let* ((program (make-program-instance 'evaluation))
	 (*program* program)
	 ; (src (spec (find-prototype 'evaluation)))
	 )
    ; (display 'src src)
    (init program `(toplevel-input ((,(intern-wide-ptr input) ,(intern-wide-ptr env)))
				   sym-digest-mem ,(initial-sym-digest-mem)
				   builtin-digest-mem ,(initial-builtin-digest-mem)))
    (run program)

    #|
    (display-relation program 'alloc)
    (display-relation program 'ingress)
    (display-relation program 'cons-mem)
    (display-relation program 'cons-digest-mem)
    (display-relation program 'thunk-mem)
    (display-relation program 'thunk-digest-mem)
    (display-relation program 'fun-mem)
    (display-relation program 'fun-digest-mem)
    
    (display-relation program 'ptr-value)
    (display-relation program 'hash4)
    (display-relation program 'unhash4)
    (display-relation program 'hash4-rel)
    (display-relation program 'hash5)
    (display-relation program 'unhash5)
    (display-relation program 'hash5-rel)
    
    (display-relation program 'eval)
    (display-relation program 'output-ptr)
    |#
    
    (is (== `((,(intern-wide-ptr expected-output))) (relation-tuple-list (find-relation program 'output-expr))))))

(test self-evaluating-num
  (test-aux (num 123) nil (num 123)))

(test self-evaluating-nil
  (test-aux nil nil nil))

(test self-evaluating-t
  (test-aux t nil t))

;; TODO: Restore with variadic ops
#+nil
(test zero-arg-addition
  (test-aux '(lurk:+) nil (num 0)))

;; TODO: Restore with variadic ops
#+nil
(test one-arg-addition
  (test-aux `(lurk:+ ,(num 1)) nil (num 1)))

(test two-arg-addition
  (test-aux `(lurk:+ ,(num 1) ,(num 2)) nil (num 3)))

(test two-arg-subtraction
  (test-aux `(lurk:- ,(num 3) ,(num 1)) nil (num 2)))

(test two-arg-multiplication
  (test-aux `(lurk:* ,(num 3) ,(num 4)) nil (num 12)))

;; TODO: Restore with variadic ops
#+nil
(test three-arg-addition
  (test-aux `(lurk:+ ,(num 1) ,(num 2) ,(num 3)) nil (num 6)))

(test eq-t
  (test-aux `(lurk:= ,(num 1) ,(num 1)) nil t))

(test eq-nil
  (test-aux `(lurk:= ,(num 1) ,(num 2)) nil nil))

(test leq-t
  (test-aux `(lurk:< ,(num 1) ,(num 2)) nil t))

(test leq-nil
  (test-aux `(lurk:< ,(num 1) ,(num 1)) nil nil))

(test geq-t
  (test-aux `(lurk:> ,(num 2) ,(num 1)) nil t))

(test geq-nil
  (test-aux `(lurk:> ,(num 1) ,(num 1)) nil nil))

(test if-t
  (test-aux `(lurk:if (lurk:= ,(num 1) ,(num 1)) ,(num 123) ,(num 456)) nil (num 123)))

(test if-nil
  (test-aux `(lurk:if (lurk:= ,(num 1) ,(num 2)) ,(num 123) ,(num 456)) nil (num 456)))

(test var-lookup
  (test-aux 'x `((x . ,(num 9))) (num 9)))

(test deep-var-lookup
  (test-aux 'y `((x . ,(num 9)) (y . ,(num 10))) (num 10)))

(test let-plain
  (test-aux `(lurk:let ((x ,(num 1))) x) nil (num 1)))

(test lambda-plain
  (test-aux `(lurk:lambda (x) (lurk:+ x ,(num 1))) nil (fun '(x) `(lurk:+ x ,(num 1)) nil)))

(test funcall-zero-args
  (test-aux `((lurk:lambda () ,(num 1))) nil (num 1)))

(test funcall-one-args
  (test-aux `((lurk:lambda (x) (lurk:+ x ,(num 1))) ,(num 1)) nil (num 2)))

(test funcall
  (test-aux `(lurk:let ((f (lurk:lambda (x) (lurk:+ x ,(num 1)))))
	       (f ,(num 2)))
	    nil
	    (num 3)))

(test letrec-plain
  (test-aux `(lurk:letrec ((x ,(num 1))) x) nil (num 1)))

(test letrec-funcall
  (test-aux `(lurk:letrec ((f (lurk:lambda (x) (lurk:+ x ,(num 1)))))
			  (f ,(num 2)))
	    nil
	    (num 3)))

(test letrec-fact
  (test-aux `(lurk:letrec ((fact (lurk:lambda (n) (lurk:if (lurk:= n ,(num 0))
							   ,(num 1)
							   (lurk:* (fact (lurk:- n ,(num 1)))
								   n)))))
			  (fact ,(num 4)))
	    nil
	    (num 24)
	    ))

(test letrec-complex
  (test-aux `(lurk:letrec ((fibonacci (lurk:lambda (n) (lurk:if (lurk:< n ,(num 2))
								,(num 1)
								(lurk:+ (fibonacci (lurk:- n ,(num 1)))
									(fibonacci (lurk:- n ,(num 2))))))))
			  (fibonacci ,(num 7)))
	    nil
	    (num 21)
	    ))

#+nil(test evaluation-spec
  (is (compare-spec 'evaluation 'syn-evaluation)))
