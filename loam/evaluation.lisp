(declaim (optimize safety))

(in-package #:evaluation)
(def-suite* evaluation-suite :in loam:master-suite)

(defconstant +wide-size+ 8)
(defconstant +element-bytes+ 4)
(defconstant +element-bits+ (* 8 +element-bytes+))

(setq *trace* nil)

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

  ;; Ingress path
  (rule (alloc expr-tag (wide-ptr-value expr)) (alloc env-tag (wide-ptr-value env)) <--
    (toplevel-input expr env)
    (tag expr-tag (wide-ptr-tag expr))
    (tag env-tag (wide-ptr-tag env))
    )

  (rule (input-ptr expr-ptr env-ptr) <--
    (toplevel-input expr env)
    (ptr-value expr-ptr (wide-ptr-value expr))
    (ptr-value env-ptr (wide-ptr-value env))
    (tag (ptr-tag expr-ptr) (wide-ptr-tag expr))
    (tag (ptr-tag env-ptr) (wide-ptr-tag env))
    )

  ;; Egress
  (rule (egress ptr) <-- (output-ptr ptr))

  ;; Construct output-expr from output-ptr
  (rule (output-expr (make-wide-ptr wide-tag value)) <--
    (output-ptr ptr)
    (ptr-value ptr value)
    (tag (ptr-tag ptr) wide-tag)
    #+nil(let ((x (prog-trace 'output-expr ptr))))))

;; hash-cache takes precedence over program in superclass list
(defprogram hash4 (hash-cache)
  (include ptr-program)
  (relation (hash4 wide wide wide wide)) ; (a b c d)
  (relation (unhash4 wide)) ; (digest)
  (relation (hash4-rel wide wide wide wide wide)) ; (a b c d digest)
  
  ;; signal
  (rule (alloc a-tag a-value) (alloc b-tag b-value) <--
    (unhash4 digest)
    (hash4-rel wide-a-tag a-value wide-b-tag b-value digest)
    (tag a-tag wide-a-tag)
    (tag b-tag wide-b-tag)))

;; hash-cache takes precedence over program in superclass list
(defprogram hash5 (hash-cache)
  (include ptr-program)
  (relation (hash5 wide wide wide wide wide)) ; (a b c d e)
  (relation (unhash5 wide)) ; (digest)
  (relation (hash5-rel wide wide wide wide wide wide)) ; (a b c d e digest)
  
  ;; signal
  ;; FIXME: We assume that the c-tag must be a :cons.
  (rule (alloc a-tag a-value) (alloc b-tag b-value) (alloc (tag-address :cons) c-value) <--
    (unhash5 digest)
    (hash5-rel wide-a-tag a-value wide-b-tag b-value c-value digest)
    (tag a-tag wide-a-tag)
    (tag b-tag wide-b-tag)))

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
    (tag (ptr-tag car) car-tag) (tag (ptr-tag cdr) cdr-tag)
    (hash4-rel car-tag car-value cdr-tag cdr-value digest))

  ;; Other way around.
  (rule (cons-mem car cdr addr) <--
    (cons-digest-mem digest addr)
    (hash4-rel car-tag car-value cdr-tag cdr-value digest)
    (ptr-value car car-value) (ptr-value cdr cdr-value)
    (tag (ptr-tag car) car-tag) (tag (ptr-tag cdr) cdr-tag))

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
    (tag (ptr-tag car) car-tag) (tag (ptr-tag cdr) cdr-tag)
    (ptr-value car car-value) (ptr-value cdr cdr-value))

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
    (tag (ptr-tag body) body-tag) (tag (ptr-tag closed-env) closed-env-tag)
    (hash4-rel body-tag body-value closed-env-tag closed-env-value digest))

  ;; Other way around.
  (rule (thunk-mem body closed-env addr) <--
    (thunk-digest-mem digest addr)
    (hash4-rel body-tag body-value closed-env-tag closed-env-value digest)
    (ptr-value body body-value) (ptr-value closed-env closed-env-value)
    (tag (ptr-tag body) body-tag) (tag (ptr-tag closed-env) closed-env-tag))

  ;; Register a thunk value.
  (rule (ptr-value thunk value) <--
    (thunk-digest-mem value addr) (let ((thunk (ptr :thunk (dual-value addr))))))

  ;; Register a thunk relation.
  (rule (thunk-rel body closed-env thunk) <--
    (thunk-mem body closed-env addr)
    (let ((thunk (ptr :cons (dual-value addr))))))

  ;; signal
  (rule (unhash4 digest) <--
    (ingress ptr) (when (has-tag-p ptr :thunk)) (ptr-value ptr digest))

  ;; signal
  (rule (hash4 body-tag body-value closed-env-tag closed-env-value) <--
    (egress thunk)
    (thunk-rel body closed-env thunk)
    (tag (ptr-tag body) body-tag) (tag (ptr-tag closed-env) closed-env-tag)
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
  (rule (fun-digest-mem value addr) <--
    (alloc (tag-address :fun) value)
    (let ((addr (alloc :fun (dual 0)))
          (x (prog-trace 'alloc-fun-digest-mem addr)))))

  ;; Populating fun(...) triggers allocation in fun-mem.
  (rule (fun-mem args body closed-env addr) <--
    (fun args body closed-env)
    (let ((addr (alloc :fun (dual 0)))
          (x (prog-trace 'alloc-fun-mem addr)))))

  ;; Populate fun-digest-mem if a fun in fun-mem has been hashed in hash5-rel.
  (rule (fun-digest-mem digest addr) <--
    (fun-mem args body closed-env addr)
    (ptr-value args args-value) (ptr-value body body-value) (ptr-value closed-env closed-env-value)
    (tag (ptr-tag args) args-tag) (tag (ptr-tag body) body-tag)
    (hash5-rel args-tag args-value body-tag body-value closed-env-value digest)
    (let ((x (prog-trace 'digest<-mem addr)))))

  ;; Other way around.
  (rule (fun-mem args body closed-env addr) <--
    (fun-digest-mem digest addr)
    (hash5-rel args-tag args-value body-tag body-value closed-env-value digest)
    (ptr-value args args-value)
    (ptr-value body body-value)
    (ptr-value closed-env closed-env-value)
    (tag (ptr-tag args) args-tag)
    (tag (ptr-tag body) body-tag)
    (tag (ptr-tag closed-env) (tag-address :cons))) ; FIXME: Change to :env.

  ;; Register a fun value.
  (rule (ptr-value fun value) <--
    (fun-digest-mem value addr) (let ((fun (ptr :fun (dual-value addr)))))
    (let ((x (prog-trace 'fun-ptr-value)))))

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
    (tag (ptr-tag args) args-tag) (tag (ptr-tag body) body-tag)
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
    (let ((x (prog-trace 'sym-ptr-value sym addr))))))

(defparameter *initial-builtin-addr* 41)

(defprogram builtin-mem ()
  (include ptr-program)

  (lattice (builtin-digest-mem wide dual-element))

  ;; Populating alloc(...) triggers allocation in builtin-digest-mem.
  (rule (builtin-digest-mem value (alloc :builtin (dual *initial-builtin-addr*))) <--
    (alloc (tag-address :builtin) value))

  ;; Register a builtin value.
  (rule (ptr-value builtin value) <--
    (builtin-digest-mem value addr) (let ((builtin (ptr :builtin (dual-value addr)))))
    (let ((x (prog-trace 'builtin-ptr-value builtin addr))))))

(defprogram immediate-num ()
  (include ptr-program)
  ;; real
  (rule (ptr-value ptr value) <--
    (alloc tag value)
    (when (is-tag-p tag :num))
    (let ((ptr (ptr :num (wide-nth 0 value)))
	  (x (prog-trace 'alloc-num tag ptr value)))))

  (rule (ptr-value ptr value) <--
    (egress ptr) (when (has-tag-p ptr :num))
    (let ((value (widen (ptr-value ptr)))))))

;; FIXME for PQ: This is a hack for binding a value in a relation.
;; When I just write a '0', I get something like: 'etypecase failed, expected one of SYMBOL or DATALOG:VAL-FORM'.
(defun zero () 0)

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

  (relation (fold-left-input ptr element ptr))
  (relation (fold-left ptr element ptr element))
  (signal-relation (signal-fold-left (op initial args result)
		    (fold-left-input op initial args)
		    (fold-left op initial args result)))

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
          (d (nth 3 preimage)))))

  ;; signal
  (rule (hash4-rel a b c d (hash a b c d)) <-- (hash4 a b c d))

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
	  #+nil
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
	  ;; Evaluate +. FIXME: Generalize to more ops.
	  ((== head (builtin-ptr 'lurk:+)) ((signal-fold-left head (zero) rest acc)
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

  (synthesize-rule (signal-fold-left op initial args result) <--
    (if (is-nil args)
	((let ((result initial))))
	((ingress-cons arg more-args args)
	 (when (has-tag-p arg :num))
	 (signal-fold-left op initial more-args acc)
	 (let ((result (cond ;; Slightly annoying thing: case doesn't produce == and incorrectly checks ptr equality.
			 ((== op (builtin-ptr 'lurk:+)) (+ (ptr-value arg) acc)))))))))

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

(defprogram syn-evaluation (hash-cache)
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

  (relation (fold-left-input ptr element ptr))
  (relation (fold-left ptr element ptr element))
  (signal-relation (signal-fold-left (op initial args result)
		    (fold-left-input op initial args)
		    (fold-left op initial args result)))

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
          (d (nth 3 preimage)))))

  ;; signal
  (rule (hash4-rel a b c d (hash a b c d)) <-- (hash4 a b c d))

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

  (RULE
    (EVAL EXPR ENV EVALED)
    <--
    (EVAL-INPUT EXPR ENV)
    (WHEN (HAS-TAG-P EXPR :NUM))
    (LET ((EVALED EXPR))))
  
  (RULE
    (EVAL EXPR ENV EVALED)
    <--
    (EVAL-INPUT EXPR ENV)
    (WHEN (HAS-TAG-P EXPR :ERR))
    (LET ((EVALED EXPR))))
  
  (RULE
    (EVAL EXPR ENV EVALED)
    <--
    (EVAL-INPUT EXPR ENV)
    (WHEN (IS-NIL EXPR))
    (LET ((EVALED EXPR))))
  
  (RULE
    (EVAL EXPR ENV EVALED)
    <--
    (EVAL-INPUT EXPR ENV)
    (WHEN (IS-T EXPR))
    (LET ((EVALED EXPR))))
  
  (RULE
    (LOOKUP-INPUT EXPR ENV)
    <--
    (EVAL-INPUT EXPR ENV)
    (WHEN (HAS-TAG-P EXPR :SYM))
    (let ((x (prog-trace 'lookup-start expr env)))))
  (RULE
    (EVAL EXPR ENV EVALED)
    <--
    (EVAL-INPUT EXPR ENV)
    (WHEN (HAS-TAG-P EXPR :SYM))
    (LOOKUP EXPR ENV EVALED)
    (let ((x (prog-trace 'lookup-end expr env evaled)))))

  (RULE
    (INGRESS REST)
    <--
    (EVAL-INPUT EXPR ENV)
    (WHEN (HAS-TAG-P EXPR :CONS))
    (CONS-REL HEAD REST EXPR)
    (WHEN
        (OR (== HEAD (BUILTIN-PTR 'LURK.BUILTIN:LET))
            (== HEAD (BUILTIN-PTR 'LURK.BUILTIN:LETREC)))))
  (RULE
    (INGRESS TAIL)
    <--
    (EVAL-INPUT EXPR ENV)
    (WHEN (HAS-TAG-P EXPR :CONS))
    (CONS-REL HEAD REST EXPR)
    (WHEN
        (OR (== HEAD (BUILTIN-PTR 'LURK.BUILTIN:LET))
            (== HEAD (BUILTIN-PTR 'LURK.BUILTIN:LETREC))))
    (CONS-REL BINDINGS TAIL REST))
  (RULE
    (EVAL-BINDINGS-INPUT BINDINGS ENV
			 (== HEAD (BUILTIN-PTR 'LURK.BUILTIN:LETREC)))
    <--
    (EVAL-INPUT EXPR ENV)
    (WHEN (HAS-TAG-P EXPR :CONS))
    (CONS-REL HEAD REST EXPR)
    (WHEN
        (OR (== HEAD (BUILTIN-PTR 'LURK.BUILTIN:LET))
            (== HEAD (BUILTIN-PTR 'LURK.BUILTIN:LETREC))))
    (CONS-REL BINDINGS TAIL REST)
    (CONS-REL BODY END TAIL)
    (WHEN (IS-NIL END))
    (let ((x (prog-trace 'bindings-start)))))
  (RULE
    (EVAL-INPUT BODY EXTENDED-ENV)
    <--
    (EVAL-INPUT EXPR ENV)
    (WHEN (HAS-TAG-P EXPR :CONS))
    (CONS-REL HEAD REST EXPR)
    (WHEN
        (OR (== HEAD (BUILTIN-PTR 'LURK.BUILTIN:LET))
            (== HEAD (BUILTIN-PTR 'LURK.BUILTIN:LETREC))))
    (CONS-REL BINDINGS TAIL REST)
    (CONS-REL BODY END TAIL)
    (WHEN (IS-NIL END))
    (EVAL-BINDINGS BINDINGS ENV
		   (== HEAD (BUILTIN-PTR 'LURK.BUILTIN:LETREC)) EXTENDED-ENV)
    (let ((x (prog-trace 'bindings-end)))))
  (RULE
    (EVAL EXPR ENV EVALED)
    <--
    (EVAL-INPUT EXPR ENV)
    (WHEN (HAS-TAG-P EXPR :CONS))
    (CONS-REL HEAD REST EXPR)
    (WHEN
        (OR (== HEAD (BUILTIN-PTR 'LURK.BUILTIN:LET))
            (== HEAD (BUILTIN-PTR 'LURK.BUILTIN:LETREC))))
    (CONS-REL BINDINGS TAIL REST)
    (CONS-REL BODY END TAIL)
    (WHEN (IS-NIL END))
    (EVAL-BINDINGS BINDINGS ENV
		   (== HEAD (BUILTIN-PTR 'LURK.BUILTIN:LETREC)) EXTENDED-ENV)
    (EVAL BODY EXTENDED-ENV EVALED))

  ;;;;; LOOKUP
  
  (RULE
    (INGRESS ENV)
    <--
    (LOOKUP-INPUT VAR ENV)
    (let ((x (prog-trace 'lookup-ingress-env var env)))))
  (RULE
    (INGRESS BINDING)
    <--
    (LOOKUP-INPUT VAR ENV)
    (CONS-REL BINDING MORE-ENV ENV)
    (let ((x (prog-trace 'lookup-ingress-binding var binding more-env)))))
  (RULE
    (INGRESS BOUND-VALUE)
    <--
    (LOOKUP-INPUT VAR ENV)
    (CONS-REL BINDING MORE-ENV ENV)
    (CONS-REL BOUND-VAR BOUND-VALUE BINDING)
    (WHEN (== VAR BOUND-VAR))
    (WHEN (HAS-TAG-P BOUND-VALUE :THUNK)))
  (RULE
    (CONS BINDING CLOSED-ENV)
    <--
    (LOOKUP-INPUT VAR ENV)
    (CONS-REL BINDING MORE-ENV ENV)
    (CONS-REL BOUND-VAR BOUND-VALUE BINDING)
    (WHEN (== VAR BOUND-VAR))
    (WHEN (HAS-TAG-P BOUND-VALUE :THUNK))
    (THUNK-REL BODY CLOSED-ENV BOUND-VALUE))
  (RULE
    (EVAL-INPUT BODY EXTENDED-ENV)
    <--
    (LOOKUP-INPUT VAR ENV)
    (CONS-REL BINDING MORE-ENV ENV)
    (CONS-REL BOUND-VAR BOUND-VALUE BINDING)
    (WHEN (== VAR BOUND-VAR))
    (WHEN (HAS-TAG-P BOUND-VALUE :THUNK))
    (THUNK-REL BODY CLOSED-ENV BOUND-VALUE)
    (CONS-REL BINDING CLOSED-ENV EXTENDED-ENV))
  (RULE
    (LOOKUP VAR ENV VALUE)
    <--
    (LOOKUP-INPUT VAR ENV)
    (CONS-REL BINDING MORE-ENV ENV)
    (CONS-REL BOUND-VAR BOUND-VALUE BINDING)
    (WHEN (== VAR BOUND-VAR))
    (WHEN (HAS-TAG-P BOUND-VALUE :THUNK))
    (THUNK-REL BODY CLOSED-ENV BOUND-VALUE)
    (CONS-REL BINDING CLOSED-ENV EXTENDED-ENV)
    (EVAL BODY EXTENDED-ENV VALUE))
  (RULE
    (LOOKUP VAR ENV VALUE)
    <--
    (LOOKUP-INPUT VAR ENV)
    (CONS-REL BINDING MORE-ENV ENV)
    (CONS-REL BOUND-VAR BOUND-VALUE BINDING)
    (WHEN (== VAR BOUND-VAR))
    (WHEN (NOT (HAS-TAG-P BOUND-VALUE :THUNK)))
    (LET ((VALUE BOUND-VALUE)
	  (x (prog-trace 'lookup-not-thunk-eq var bound-var value)))))
  (RULE
    (LOOKUP-INPUT VAR MORE-ENV)
    <--
    (LOOKUP-INPUT VAR ENV)
    (CONS-REL BINDING MORE-ENV ENV)
    (CONS-REL BOUND-VAR BOUND-VALUE BINDING)
    (WHEN (NOT (== VAR BOUND-VAR)))
    (let ((x (prog-trace 'lookup-recurse-start var more-env)))))
  (RULE
    (LOOKUP VAR ENV VALUE)
    <--
    (LOOKUP-INPUT VAR ENV)
    (CONS-REL BINDING MORE-ENV ENV)
    (CONS-REL BOUND-VAR BOUND-VALUE BINDING)
    (WHEN (NOT (== VAR BOUND-VAR)))
    (LOOKUP VAR MORE-ENV VALUE)
    (let ((x (prog-trace 'lookup-recurse-end var more-env value)))))

  ;;;;; EVAL-BINDINGS
  
  (RULE
    (INGRESS BINDINGS)
    <--
    (EVAL-BINDINGS-INPUT BINDINGS EXTENDED-ENV IS-REC)
    (let ((x (prog-trace 'bindings-ingress is-rec)))))
  (RULE
    (INGRESS BINDING)
    <--
    (EVAL-BINDINGS-INPUT BINDINGS EXTENDED-ENV IS-REC)
    (CONS-REL BINDING MORE-BINDINGS BINDINGS)
    (let ((x (prog-trace 'bindings-ingress-binding binding more-bindings)))))
  (RULE
    (INGRESS BINDING-TAIL)
    <--
    (EVAL-BINDINGS-INPUT BINDINGS EXTENDED-ENV IS-REC)
    (CONS-REL BINDING MORE-BINDINGS BINDINGS)
    (CONS-REL VAR BINDING-TAIL BINDING)
    (let ((x (prog-trace 'bindings-ingress-tail var)))))
  (RULE
    (THUNK UNEVALED EXTENDED-ENV)
    <--
    (EVAL-BINDINGS-INPUT BINDINGS EXTENDED-ENV IS-REC)
    (CONS-REL BINDING MORE-BINDINGS BINDINGS)
    (CONS-REL VAR BINDING-TAIL BINDING)
    (CONS-REL UNEVALED END BINDING-TAIL)
    (WHEN (IS-NIL END))
    (WHEN IS-REC)
    (let ((x (prog-trace 'bindings-signal-thunk unevaled (is-nil end) is-rec)))))
  (RULE
    (CONS VAR THUNK)
    <--
    (EVAL-BINDINGS-INPUT BINDINGS EXTENDED-ENV IS-REC)
    (CONS-REL BINDING MORE-BINDINGS BINDINGS)
    (CONS-REL VAR BINDING-TAIL BINDING)
    (CONS-REL UNEVALED END BINDING-TAIL)
    (WHEN (IS-NIL END))
    (WHEN IS-REC)
    (THUNK-REL UNEVALED EXTENDED-ENV THUNK)
    (let ((x (prog-trace 'bindings-signal-cons-binding thunk)))))
  (RULE
    (CONS ENV-BINDING EXTENDED-ENV)
    <--
    (EVAL-BINDINGS-INPUT BINDINGS EXTENDED-ENV IS-REC)
    (CONS-REL BINDING MORE-BINDINGS BINDINGS)
    (CONS-REL VAR BINDING-TAIL BINDING)
    (CONS-REL UNEVALED END BINDING-TAIL)
    (WHEN (IS-NIL END))
    (WHEN IS-REC)
    (THUNK-REL UNEVALED EXTENDED-ENV THUNK)
    (CONS-REL VAR THUNK ENV-BINDING)
    (WHEN (IS-NIL MORE-BINDINGS))
    (let ((x (prog-trace 'bindings-signal-cons-final-env env-binding extended-env)))))
  (RULE
    (EVAL-BINDINGS BINDINGS EXTENDED-ENV IS-REC FINAL-ENV)
    <--
    (EVAL-BINDINGS-INPUT BINDINGS EXTENDED-ENV IS-REC)
    (CONS-REL BINDING MORE-BINDINGS BINDINGS)
    (CONS-REL VAR BINDING-TAIL BINDING)
    (CONS-REL UNEVALED END BINDING-TAIL)
    (WHEN (IS-NIL END))
    (WHEN IS-REC)
    (THUNK-REL UNEVALED EXTENDED-ENV THUNK)
    (CONS-REL VAR THUNK ENV-BINDING)
    (WHEN (IS-NIL MORE-BINDINGS))
    (CONS-REL ENV-BINDING EXTENDED-ENV FINAL-ENV)
    (let ((x (prog-trace 'bindings-signal-return final-env)))))
  (RULE
    (CONS ENV-BINDING EXTENDED-ENV)
    <--
    (EVAL-BINDINGS-INPUT BINDINGS EXTENDED-ENV IS-REC)
    (CONS-REL BINDING MORE-BINDINGS BINDINGS)
    (CONS-REL VAR BINDING-TAIL BINDING)
    (CONS-REL UNEVALED END BINDING-TAIL)
    (WHEN (IS-NIL END))
    (WHEN IS-REC)
    (THUNK-REL UNEVALED EXTENDED-ENV THUNK)
    (CONS-REL VAR THUNK ENV-BINDING)
    (WHEN (NOT (IS-NIL MORE-BINDINGS))))
  (RULE
    (EVAL-BINDINGS-INPUT MORE-BINDINGS NEW-ENV IS-REC)
    <--
    (EVAL-BINDINGS-INPUT BINDINGS EXTENDED-ENV IS-REC)
    (CONS-REL BINDING MORE-BINDINGS BINDINGS)
    (CONS-REL VAR BINDING-TAIL BINDING)
    (CONS-REL UNEVALED END BINDING-TAIL)
    (WHEN (IS-NIL END))
    (WHEN IS-REC)
    (THUNK-REL UNEVALED EXTENDED-ENV THUNK)
    (CONS-REL VAR THUNK ENV-BINDING)
    (WHEN (NOT (IS-NIL MORE-BINDINGS)))
    (CONS-REL ENV-BINDING EXTENDED-ENV NEW-ENV))
  (RULE
    (EVAL-BINDINGS BINDINGS EXTENDED-ENV IS-REC FINAL-ENV)
    <--
    (EVAL-BINDINGS-INPUT BINDINGS EXTENDED-ENV IS-REC)
    (CONS-REL BINDING MORE-BINDINGS BINDINGS)
    (CONS-REL VAR BINDING-TAIL BINDING)
    (CONS-REL UNEVALED END BINDING-TAIL)
    (WHEN (IS-NIL END))
    (WHEN IS-REC)
    (THUNK-REL UNEVALED EXTENDED-ENV THUNK)
    (CONS-REL VAR THUNK ENV-BINDING)
    (WHEN (NOT (IS-NIL MORE-BINDINGS)))
    (CONS-REL ENV-BINDING EXTENDED-ENV NEW-ENV)
    (EVAL-BINDINGS MORE-BINDINGS NEW-ENV IS-REC FINAL-ENV))
  (RULE
    (EVAL-INPUT UNEVALED EXTENDED-ENV)
    <--
    (EVAL-BINDINGS-INPUT BINDINGS EXTENDED-ENV IS-REC)
    (CONS-REL BINDING MORE-BINDINGS BINDINGS)
    (CONS-REL VAR BINDING-TAIL BINDING)
    (CONS-REL UNEVALED END BINDING-TAIL)
    (WHEN (IS-NIL END))
    (WHEN (NOT IS-REC)))
  (RULE
    (CONS VAR EVALED)
    <--
    (EVAL-BINDINGS-INPUT BINDINGS EXTENDED-ENV IS-REC)
    (CONS-REL BINDING MORE-BINDINGS BINDINGS)
    (CONS-REL VAR BINDING-TAIL BINDING)
    (CONS-REL UNEVALED END BINDING-TAIL)
    (WHEN (IS-NIL END))
    (WHEN (NOT IS-REC))
    (EVAL UNEVALED EXTENDED-ENV EVALED))
  (RULE
    (CONS ENV-BINDING EXTENDED-ENV)
    <--
    (EVAL-BINDINGS-INPUT BINDINGS EXTENDED-ENV IS-REC)
    (CONS-REL BINDING MORE-BINDINGS BINDINGS)
    (CONS-REL VAR BINDING-TAIL BINDING)
    (CONS-REL UNEVALED END BINDING-TAIL)
    (WHEN (IS-NIL END))
    (WHEN (NOT IS-REC))
    (EVAL UNEVALED EXTENDED-ENV EVALED)
    (CONS-REL VAR EVALED ENV-BINDING)
    (WHEN (IS-NIL MORE-BINDINGS)))
  (RULE
    (EVAL-BINDINGS BINDINGS EXTENDED-ENV IS-REC FINAL-ENV)
    <--
    (EVAL-BINDINGS-INPUT BINDINGS EXTENDED-ENV IS-REC)
    (CONS-REL BINDING MORE-BINDINGS BINDINGS)
    (CONS-REL VAR BINDING-TAIL BINDING)
    (CONS-REL UNEVALED END BINDING-TAIL)
    (WHEN (IS-NIL END))
    (WHEN (NOT IS-REC))
    (EVAL UNEVALED EXTENDED-ENV EVALED)
    (CONS-REL VAR EVALED ENV-BINDING)
    (WHEN (IS-NIL MORE-BINDINGS))
    (CONS-REL ENV-BINDING EXTENDED-ENV FINAL-ENV)
    (let ((x (prog-trace 'bindings- thunk)))))
  (RULE
    (CONS ENV-BINDING EXTENDED-ENV)
    <--
    (EVAL-BINDINGS-INPUT BINDINGS EXTENDED-ENV IS-REC)
    (CONS-REL BINDING MORE-BINDINGS BINDINGS)
    (CONS-REL VAR BINDING-TAIL BINDING)
    (CONS-REL UNEVALED END BINDING-TAIL)
    (WHEN (IS-NIL END))
    (WHEN (NOT IS-REC))
    (EVAL UNEVALED EXTENDED-ENV EVALED)
    (CONS-REL VAR EVALED ENV-BINDING)
    (WHEN (NOT (IS-NIL MORE-BINDINGS))))
  (RULE
    (EVAL-BINDINGS-INPUT MORE-BINDINGS NEW-ENV IS-REC)
    <--
    (EVAL-BINDINGS-INPUT BINDINGS EXTENDED-ENV IS-REC)
    (CONS-REL BINDING MORE-BINDINGS BINDINGS)
    (CONS-REL VAR BINDING-TAIL BINDING)
    (CONS-REL UNEVALED END BINDING-TAIL)
    (WHEN (IS-NIL END))
    (WHEN (NOT IS-REC))
    (EVAL UNEVALED EXTENDED-ENV EVALED)
    (CONS-REL VAR EVALED ENV-BINDING)
    (WHEN (NOT (IS-NIL MORE-BINDINGS)))
    (CONS-REL ENV-BINDING EXTENDED-ENV NEW-ENV)
    (let ((x (prog-trace 'bindings-recurse-start more-bindings new-env)))))
  (RULE
    (EVAL-BINDINGS BINDINGS EXTENDED-ENV IS-REC FINAL-ENV)
    <--
    (EVAL-BINDINGS-INPUT BINDINGS EXTENDED-ENV IS-REC)
    (CONS-REL BINDING MORE-BINDINGS BINDINGS)
    (CONS-REL VAR BINDING-TAIL BINDING)
    (CONS-REL UNEVALED END BINDING-TAIL)
    (WHEN (IS-NIL END))
    (WHEN (NOT IS-REC))
    (EVAL UNEVALED EXTENDED-ENV EVALED)
    (CONS-REL VAR EVALED ENV-BINDING)
    (WHEN (NOT (IS-NIL MORE-BINDINGS)))
    (CONS-REL ENV-BINDING EXTENDED-ENV NEW-ENV)
    (EVAL-BINDINGS MORE-BINDINGS NEW-ENV IS-REC FINAL-ENV)
    (let ((x (prog-trace 'bindings-recurse-end bindings final-env)))))
  )


(defparameter *ptr-nil* (make-ptr 10 0))
(defparameter *ptr-t* (make-ptr 10 1))

(defun is-nil (ptr) (== ptr *ptr-nil*))
(defun is-t (ptr) (== ptr *ptr-t*))
(defun builtin-ptr (sym)
  (make-ptr 8 (builtin-idx sym)))

(defun initial-sym-digest-mem ()
    (loop for sym in (list nil t)
	  for i from 0
	  for sym-value = (wide-ptr-value (intern-wide-ptr sym))
	  collect (list sym-value (dual i))))

;; FIXME for PQ: When I try to load in all the builtins, the program just freezes up and spins.
;; i.e. tests that were passing before instantly now hang and don't return unless I forcibly exit.
#+nil
(defun initial-builtin-digest-mem ()
  (loop for b in *builtin-list*
	for i from 0
	for builtin-value = (wide-ptr-value (intern-wide-ptr b))
	collect (list builtin-value (dual i))))

(defun initial-builtin-digest-mem ()
  (loop for b in (list 'lurk:lambda 'lurk:+ 'lurk:let)
	for i = (builtin-idx b)
	for builtin-value = (wide-ptr-value (intern-wide-ptr b))
	collect (list builtin-value (dual i))))

(defun display-relation (program relation)
  (let ((x (find-relation program relation)))
    (display relation (relation-tuple-list x))))

(defun test-aux (input env expected-output)
  (let* ((program (make-program-instance 'evaluation))
	 (*program* program)
	 ; (src (spec (find-prototype 'evaluation)))
	 )
    ; (display 'src src)
    (init program `(toplevel-input ((,(display (intern-wide-ptr input)) ,(intern-wide-ptr env)))
				   sym-digest-mem ,(initial-sym-digest-mem)
				   builtin-digest-mem ,(initial-builtin-digest-mem)))
    (run program)

    (display-relation program 'alloc)
    (display-relation program 'ingress)
    (display-relation program 'cons-mem)
    (display-relation program 'cons-digest-mem)
    
    (display-relation program 'ptr-value)
    (display-relation program 'unhash4)
    (display-relation program 'hash4-rel)
    
    (display-relation program 'eval)
    (display-relation program 'output-ptr)
    
    (is (== `((,(intern-wide-ptr expected-output))) (relation-tuple-list (find-relation program 'output-expr))))))

(test self-evaluating-num
  (test-aux (num 123) nil (num 123)))

(test self-evaluating-nil
  (test-aux nil nil nil))

(test self-evaluating-t
  (test-aux t nil t))

(test zero-arg-addition
  (test-aux '(lurk:+) nil (num 0)))

(test one-arg-addition
  (test-aux `(lurk:+ ,(num 1)) nil (num 1)))

(test two-arg-addition
  (test-aux `(lurk:+ ,(num 1) ,(num 2)) nil (num 3)))

(test three-arg-addition
  (test-aux `(lurk:+ ,(num 1) ,(num 2) ,(num 3)) nil (num 6)))

(test relational-t
  (test-aux `(lurk:= ,(num 1) ,(num 1)) nil t))

(test relational-nil
  (test-aux `(lurk:= ,(num 1) ,(num 2)) nil nil))

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

(test funcall
  (test-aux `(lurk:let ((f (lurk:lambda (x) (lurk:+ x ,(num 1)))))
	       (f ,(num 2)))
	    nil
	    (num 3)))

(test letrec-plain
  (test-aux `(lurk:letrec ((x ,(num 1))) x) nil (num 1)))

(test evaluation-spec
  (is (compare-spec 'evaluation 'syn-evaluation)))
