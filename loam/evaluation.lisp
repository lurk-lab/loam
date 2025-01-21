(declaim (optimize safety))

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
    (ptr-value ptr value)))

;; hash-cache takes precedence over program in superclass list
(defprogram hash4 (hash-cache)
  (include ptr-program)
  (relation (hash4 element wide wide wide wide)) ; (tag a b c d)
  (relation (unhash4 element wide)) ; (tag digest)
  (relation (hash4-rel wide wide wide wide wide)) ; (a b c d digest)

  )

;; hash-cache takes precedence over program in superclass list
(defprogram hash5 (hash-cache)
  (include ptr-program)
  (relation (hash5 element wide wide wide wide wide)) ; (tag a b c d e)
  (relation (unhash5 element wide)) ; (tag digest)
  (relation (hash5-rel wide wide wide wide wide wide)) ; (a b c d e digest)
  
  )

(eval-when (:compile-toplevel :load-toplevel :execute)
  ;; Generate a full memory.
  ;; In the config, the :tag spec indicates a possible explicit tag that should be optimized away,
  ;; and the macro will automatically handle these cases and insert the correct tag accordingly.
  ;; For example, for env memory, which consists of (var val inner-env),
  ;; the tag of inner-env is assumed to always be :env, and can be dropped. 
  (defun defmem-full (prog-name superclasses config arg-specs)
    (multiple-value-bind
	  (signal-args
	   signal-type-args
	   digest<-mem-forms
	   mem<-digest-forms
	   hash-args
	   unhash-args
	   alloc-forms
	   egress-forms)
	(loop for arg-spec in arg-specs
	      for arg = (getf arg-spec :arg)
	      for arg-tag = (symbolconc arg '-tag)
	      for arg-value = (symbolconc arg '-value)
	      for type = (getf arg-spec :type)
	      for explicit-tag = (getf arg-spec :tag)
	      for tag-check-form = (if explicit-tag
				       `(when (== (ptr-tag ,arg) (tag-address ,explicit-tag)))
				       `(when (== (ptr-tag ,arg) (wide-nth 0 ,arg-tag))))
	      ;; Collect each form of syntax that we need to use when generating the rules.
	      ;; Depending on whether we have an explicit tag or not, we have to either check
	      ;; for the given tag, or insert the given tag. 
	      collect arg into signal-args
	      collect type into signal-type-args
	      collect `(ptr-value ,arg ,arg-value) into digest<-mem-forms
	      when explicit-tag
		collect tag-check-form into digest<-mem-forms
	      collect `(ptr-value ,arg ,arg-value) into mem<-digest-forms
	      collect tag-check-form into mem<-digest-forms
	      when (not explicit-tag)
		collect `(widen (ptr-tag ,arg)) into hash-args
		and collect arg-tag into unhash-args
	      collect arg-value into hash-args
	      collect arg-value into unhash-args
	      collect (if explicit-tag
			  `(alloc (tag-address ,explicit-tag) ,arg-value)
			  `(alloc (wide-nth 0 ,arg-tag) ,arg-value))
		into alloc-forms
	      collect `(egress ,arg) into egress-forms
	      finally (return (values
			       signal-args
			       signal-type-args
			       digest<-mem-forms
			       mem<-digest-forms
			       hash-args
			       unhash-args
			       alloc-forms
			       egress-forms)))
      (let* ((name (getf config :name))
	     (tag (getf config :tag))
	     (initial-addr (getf config :initial-addr))
	     (hasher (getf config :hasher))
	     (name-rel (symbolconc name '-rel))
	     (name-digest-mem (symbolconc name '-digest-mem))
	     (name-mem (symbolconc name '-mem))
	     (hash-rel (symbolconc hasher '-rel))
	     (unhasher (symbolconc 'un hasher))
	     )
	`(progn
	   (defprogram ,prog-name ,superclasses
	     (include ptr-program)
	     (include ,hasher)
	     
	     ;; Signal.
	     (relation (,name ,@signal-type-args))
	     ;; The canonical `name` Ptr relation.
	     (relation (,name-rel ,@signal-type-args ptr))

	     ;; Memory to support data  allocated by digest or contents.
	     (lattice (,name-digest-mem wide dual-element)) ; (digest addr)
	     (lattice (,name-mem ,@signal-type-args dual-element)) ; (args addr)

	     ;; Populating alloc(...) triggers allocation in cons-digest-mem.
	     (rule (,name-digest-mem ,'value  (alloc ,tag (dual ,initial-addr))) <--
	       (alloc (tag-address ,tag) ,'value))

	     ;; Populating `name`(...) triggers allocation in name-mem.
	     (rule (,name-mem ,@signal-args (alloc ,tag (dual ,initial-addr))) <-- (,name ,@signal-args))
	     
	     ;; Populate name-digest-mem if a name in cons-mem has been hashed in hash4-rel.
	     (rule (,name-digest-mem digest addr) <--
	       (,name-mem ,@signal-args addr)
	       ,@digest<-mem-forms
	       (,hash-rel ,@hash-args digest))

	     ;; Other way around.
	     (rule (,name-mem ,@signal-args addr) <--
	       (,name-digest-mem digest addr)
	       (,hash-rel ,@unhash-args digest)
	       ,@mem<-digest-forms)

	     ;; Register a memory value.
	     (rule (ptr-value ,name value) <--
	       (,name-digest-mem value addr) (let ((,name (ptr ,tag (dual-value addr))))))

	     ;; Register a memory relation.
	     (rule (,name-rel ,@signal-args ,name) <--
	       (,name-mem ,@signal-args addr)
	       (let ((,name (ptr ,tag (dual-value addr))))))

	     ;; signal
	     (rule (,unhasher (tag-address ,tag) digest) <--
	       (ingress ptr) (when (has-tag-p ptr ,tag)) (ptr-value ptr digest))

	     ;; signal
	     (rule ,@alloc-forms <--
	       (,unhasher (tag-address ,tag) digest)
	       (,hash-rel ,@unhash-args digest))

	     ;; signal
	     (rule (,hasher (tag-address ,tag) ,@hash-args) <--
	       (egress ,name)
	       (,name-rel ,@signal-args ,name)
	       ,@digest<-mem-forms)

	     ;; signal
	     (rule ,@egress-forms <--
	       (egress ,name) (,name-rel ,@signal-args ,name))
	     )))))

  ;; Digest only memory. FIXME: Need to define this.
  ;; Example: sym, builtin.
  (defun defmem-digest-only (prog-name superclasses config)
    (let* ((name (getf config :name))
	   (tag (getf config :tag))
	   (initial-addr (getf config :initial-addr))
	   (digest-mem (symbolconc name '-digest-mem))
	  )
     `(progn
       (defprogram ,prog-name ,superclasses
	 (include ptr-program) ;; TODO: Maybe this should not be hardcoded.

	 (relation (,digest-mem wide dual-element))

	 (rule (,digest-mem value (alloc ,tag (dual ,initial-addr))) <--
	   (alloc (tag-address ,tag) value))
	 
	 (rule (ptr-value ,name value) <--
	   (,digest-mem value addr) (let ((,name (ptr ,tag (dual-value addr))))))))))

  ;; Immediate memory, for which the pointer value can be represented by exactly the wide value.
  ;; Thus, instead of allocating memory and managing ptr-value mappings, we can just translate
  ;; directly when ingressing and egressing.
  ;;
  ;; Examples: num, err
  (defun defmem-immediate (prog-name superclasses config)
    (let ((name (getf config :name))
	  (tag (getf config :tag)))
     `(progn
       (defprogram ,prog-name ,superclasses
	 (include ptr-program) ;; TODO: Maybe this should not be hardcoded.

	 ;; When ingressing (a.k.a alloc), just copy the wide value into the ptr.
	 (rule (ptr-value ptr value) <--
	   (alloc tag value)
	   (when (is-tag-p tag ,tag))
	   (let ((ptr (ptr ,tag (wide-nth 0 value))))))

	 ;; When egressing, just copy the ptr vale into the wide.
	 (rule (ptr-value ptr value) <--
	   (egress ptr)
	   (when (has-tag-p ptr ,tag))
	   (let ((value (widen (ptr-value ptr))))))))))
  )

;; FIXME: Annoyingly, I have to copy this over to get the macro expansion to work.
;; When importing, we end up using the symbols shadowed under the allocation package,
;; for example `allocation::ingress`, and this interferes with execution.
;; There should definitely be a way to prevent this from happening in the first place,
;; but I haven't been able to get anything to work.
;;
;; Generate a memory program from a given config of (:type :name :tag :initial-addr :hasher)
;; and a list of specifications for each argument given by (:arg :type :tag).
;; The :type spec indicates which type of memory should be generated.
(defmacro defmem (prog-name superclasses config &body arg-specs)
  (case (getf config :type)
    (full (defmem-full prog-name `,superclasses `,config `,arg-specs))
    (digest-only (defmem-digest-only `,prog-name `,superclasses `,config))
    (immediate (defmem-immediate `,prog-name `,superclasses `,config))))

(defmem cons-mem (hash-cache)
    (:type full :name cons :tag :cons :initial-addr 0 :hasher hash4)
  (:arg car :type ptr)
  (:arg cdr :type ptr))

(defmem thunk-mem (hash-cache)
    (:type full :name thunk :tag :thunk :initial-addr 0 :hasher hash4)
  (:arg body :type ptr)
  (:arg closed-env :type ptr))

(defprogram syn-fun-mem (hash-cache)
  (include ptr-program)
  (include hash5)

  ;; signal
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
    (fun args body closed-env))

  ;; Populate fun-digest-mem if a fun in fun-mem has been hashed in hash5-rel.
  (rule (fun-digest-mem digest addr) <--
    (fun-mem args body closed-env addr)
    (ptr-value args args-value)
    (ptr-value body body-value)
    (ptr-value closed-env closed-env-value)
    (when (== (ptr-tag closed-env) (tag-address :env)))
    (hash5-rel (widen (ptr-tag args)) args-value (widen (ptr-tag body)) body-value closed-env-value digest))

  ;; Other way around.
  (rule (fun-mem args body closed-env addr) <--
    (fun-digest-mem digest addr)
    (hash5-rel args-tag args-value body-tag body-value closed-env-value digest)
    (ptr-value args args-value)
    (when (== (ptr-tag args) (wide-nth 0 args-tag)))
    (ptr-value body body-value)
    (when (== (ptr-tag body) (wide-nth 0 body-tag)))
    (ptr-value closed-env closed-env-value)
    (when (== (ptr-tag closed-env) (tag-address :env))))

  ;; Register a fun value.
  (rule (ptr-value fun value) <--
    (fun-digest-mem value addr) (let ((fun (ptr :fun (dual-value addr))))))
  
  ;; Register a fun relation.
  (rule (fun-rel args body closed-env fun) <--
    (fun-mem args body closed-env addr)
    (let ((fun (ptr :fun (dual-value addr))))))

  ;; signal
  (rule (unhash5 (tag-address :fun) digest) <--
    (ingress ptr) (when (has-tag-p ptr :fun)) (ptr-value ptr digest))
  
  ;; signal
  (rule
    (alloc (wide-nth 0 args-tag) args-value)
    (alloc (wide-nth 0 body-tag) body-value)
    (alloc (tag-address :env) closed-env-value)
    <--
    (unhash5 (tag-address :fun) digest)
    (hash5-rel args-tag args-value body-tag body-value closed-env-value digest))

  ;; signal
  (rule
    (hash5 (tag-address :fun)
	   (widen (ptr-tag args))
	   args-value
	   (widen (ptr-tag body))
	   body-value
	   closed-env-value)
    <--
    (egress fun)
    (fun-rel args body closed-env fun)
    (ptr-value args args-value)
    (ptr-value body body-value)
    (ptr-value closed-env closed-env-value)
    (when (== (ptr-tag closed-env) (tag-address :env))))

  ;; signal
  (rule (egress args) (egress body) (egress closed-env) <--
    (egress fun) (fun-rel args body closed-env fun)))

(defmem fun-mem (hash-cache)
    (:type full :name fun :tag :fun :initial-addr 0 :hasher hash5)
  (:arg args :type ptr)
  (:arg body :type ptr)
  (:arg closed-env :type ptr :tag :env))

(defparameter *initial-env-addr* 1)

(defmem env-mem (hash-cache)
    (:type full :name env :tag :env :initial-addr *initial-env-addr* :hasher hash5)
  (:arg var :type ptr)
  (:arg val :type ptr)
  (:arg inner-env :type ptr :tag :env))

(defparameter *initial-sym-addr* 2)

(defprogram syn-sym-digest-mem ()
  (include ptr-program)

  (lattice (sym-digest-mem wide dual-element))

  ;; Populating alloc(...) triggers allocation in sym-digest-mem.
  (rule (sym-digest-mem value (alloc :sym (dual *initial-sym-addr*))) <--
    (alloc (tag-address :sym) value))

  ;; Register a sym value.
  (rule (ptr-value sym value) <--
    (sym-digest-mem value addr) (let ((sym (ptr :sym (dual-value addr)))))))

(defmem sym-digest-mem ()
    (:type digest-only
     :name sym
     :tag :sym
     :initial-addr *initial-sym-addr*)
  nil)

(defparameter *initial-builtin-addr* 41)

(defprogram syn-builtin-digest-mem (hash-cache)
  (include ptr-program)

  (lattice (builtin-digest-mem wide dual-element))

  ;; Populating alloc(...) triggers allocation in builtin-digest-mem.
  (rule (builtin-digest-mem value (alloc :builtin (dual *initial-builtin-addr*))) <--
    (alloc (tag-address :builtin) value))

  ;; Register a builtin value.
  (rule (ptr-value builtin value) <--
    (builtin-digest-mem value addr) (let ((builtin (ptr :builtin (dual-value addr)))))))

(defmem builtin-digest-mem (hash-cache)
  (:type digest-only
   :name builtin
   :tag :builtin
   :initial-addr *initial-builtin-addr*))


(defprogram syn-immediate-num ()
  (include ptr-program)
  ;; real
  (rule (ptr-value ptr value) <--
	(alloc tag value)
	(when (is-tag-p tag :num))
	(let ((ptr (ptr :num (wide-nth 0 value))))))

  (rule (ptr-value ptr value) <--
	(egress ptr) (when (has-tag-p ptr :num))
	(let ((value (widen (ptr-value ptr)))))))

(defmem immediate-num ()
  (:type immediate
   :name num
   :tag :num))

;; FIXME for PQ: This is a hack for binding a value in a relation.
;; When I just write a '0', I get something like: 'etypecase failed, expected one of SYMBOL or DATALOG:VAL-FORM'.
;; (defun zero () 0)

;; The Lurk evaluation.
(defprogram evaluation (hash-cache)
  (include ptr-program)
  (include cons-mem)
  (include thunk-mem)
  (include fun-mem)
  (include env-mem)
  (include sym-digest-mem)
  (include builtin-digest-mem)
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

  ;; Env signals.
  (signal-relation (ingress-env (var val inner-env env)
		    (ingress env)
		    (env-rel var val inner-env env)))
  (signal-relation (signal-env (var val inner-env env)
		    (env var val inner-env)
		    (env-rel var val inner-env env)))

  ;; The hashing rules below are due to a design restriction of the hash-cache.
  ;; Because the hash-cache is local to the subprogram it is defined from,
  ;; when we intern the input and env in the outermost scope, we hash into the
  ;; local hash-cache of the evaluation program instead.

  ;; signal
  (rule (hash4-rel a b c d digest) <--
    (unhash4 _ digest)
    (when (not (== digest (widen 0)))) ;; Edge case of 0.
    (let ((preimage (unhash digest 4))
          (a (nth 0 preimage))
          (b (nth 1 preimage))
          (c (nth 2 preimage))
          (d (nth 3 preimage))
	  )))
  
  ;; signal
  (rule (hash4-rel a b c d (hash a b c d)) <--
    (hash4 _ a b c d))

  ;; signal
  (rule (hash5-rel a b c d e digest) <--
    (unhash5 _ digest)
    (when (not (== digest (widen 0)))) ;; Edge case of 0.
    (let ((preimage (unhash digest 5))
          (a (nth 0 preimage))
          (b (nth 1 preimage))
          (c (nth 2 preimage))
          (d (nth 3 preimage))
	  (e (nth 4 preimage)))))

  ;; signal
  (rule (hash5-rel a b c d e (hash a b c d e)) <-- (hash5 _ a b c d e))

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
    (ingress-env bound-var bound-value more-env env)
    (if (== var bound-var)
	((if (has-tag-p bound-value :thunk)
	     ;; If the looked-up value is a thunk.
	     ((ingress-thunk body closed-env bound-value)
	      (signal-env bound-var bound-value closed-env extended-env)
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
	      (signal-env var thunk extended-env new-env)
	      (signal-eval-bindings more-bindings new-env is-rec final-env))
	     ;; Non-recursive case: just evaluate.
	     ;; FIXME: There's unfortunate duplication here, change synthesis so that `if/case/cond`
	     ;; don't have to be the final segment. Kind of a headache.
	     ((signal-eval unevaled extended-env evaled)
	      (signal-env var evaled extended-env new-env)
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
	 (signal-env arg evaled closed-env new-closed-env)
	 (signal-funcall more-args body new-closed-env more-values outer-env result))))
  )

(defparameter *ptr-nil* (make-ptr 10 0))
(defparameter *ptr-t* (make-ptr 10 1))
(defparameter *ptr-nil-env* (make-ptr 12 0))

(defun is-nil (ptr) (== ptr *ptr-nil*))
(defun is-t (ptr) (== ptr *ptr-t*))
(defun is-nil-env (ptr) (== ptr *ptr-nil-env*))

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

(defun initial-env-digest-mem ()
  (list (list (widen 0) (dual 0)))) ;; Null env pointer.

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

(test mem-spec
  (is (compare-spec 'fun-mem 'syn-fun-mem))
  (is (compare-spec 'sym-digest-mem 'syn-sym-digest-mem))
  (is (compare-spec 'immediate-num 'syn-immediate-num)))

;; Smoke test for catching regressions on the builtin issue.
(test intern-builtin
  (let* ((program (make-program-instance 'builtin-digest-mem))
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
				   env-digest-mem ,(initial-env-digest-mem)
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
    (display-relation program 'env-mem)
    (display-relation program 'env-digest-mem)
    
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
  (test-aux (num 123) 'lurk:nil-env (num 123)))

(test self-evaluating-nil
  (test-aux nil 'lurk:nil-env nil))

(test self-evaluating-t
  (test-aux t 'lurk:nil-env t))

;; TODO: Restore with variadic ops
#+nil
(test zero-arg-addition
  (test-aux '(lurk:+) 'lurk:nil-env (num 0)))

;; TODO: Restore with variadic ops
#+nil
(test one-arg-addition
  (test-aux `(lurk:+ ,(num 1)) 'lurk:nil-env (num 1)))

(test two-arg-addition
  (test-aux `(lurk:+ ,(num 1) ,(num 2)) 'lurk:nil-env (num 3)))

(test two-arg-subtraction
  (test-aux `(lurk:- ,(num 3) ,(num 1)) 'lurk:nil-env (num 2)))

(test two-arg-multiplication
  (test-aux `(lurk:* ,(num 3) ,(num 4)) 'lurk:nil-env (num 12)))

;; TODO: Restore with variadic ops
#+nil
(test three-arg-addition
  (test-aux `(lurk:+ ,(num 1) ,(num 2) ,(num 3)) 'nil-env (num 6)))

(test eq-t
  (test-aux `(lurk:= ,(num 1) ,(num 1)) 'lurk:nil-env t))

(test eq-nil
  (test-aux `(lurk:= ,(num 1) ,(num 2)) 'lurk:nil-env nil))

(test leq-t
  (test-aux `(lurk:< ,(num 1) ,(num 2)) 'lurk:nil-env t))

(test leq-nil
  (test-aux `(lurk:< ,(num 1) ,(num 1)) 'lurk:nil-env nil))

(test geq-t
  (test-aux `(lurk:> ,(num 2) ,(num 1)) 'lurk:nil-env t))

(test geq-nil
  (test-aux `(lurk:> ,(num 1) ,(num 1)) 'lurk:nil-env nil))

(test if-t
  (test-aux `(lurk:if (lurk:= ,(num 1) ,(num 1)) ,(num 123) ,(num 456)) 'lurk:nil-env (num 123)))

(test if-nil
  (test-aux `(lurk:if (lurk:= ,(num 1) ,(num 2)) ,(num 123) ,(num 456)) 'lurk:nil-env (num 456)))

(test var-lookup
  (test-aux 'x (env 'x (num 9) 'lurk:nil-env) (num 9)))

(test deep-var-lookup
  (test-aux 'y (env 'x (num 9) (env 'y (num 10) 'lurk:nil-env)) (num 10)))

(test let-plain
  (test-aux `(lurk:let ((x ,(num 1))) x) 'lurk:nil-env (num 1)))

(test lambda-plain
  (test-aux `(lurk:lambda (x) (lurk:+ x ,(num 1))) 'lurk:nil-env (fun '(x) `(lurk:+ x ,(num 1)) 'lurk:nil-env)))

(test funcall-zero-args
  (test-aux `((lurk:lambda () ,(num 1))) 'lurk:nil-env (num 1)))

(test funcall-one-args
  (test-aux `((lurk:lambda (x) (lurk:+ x ,(num 1))) ,(num 1)) 'nil-env (num 2)))

(test funcall
  (test-aux `(lurk:let ((f (lurk:lambda (x) (lurk:+ x ,(num 1)))))
	       (f ,(num 2)))
	    'lurk:nil-env
	    (num 3)))

(test letrec-plain
  (test-aux `(lurk:letrec ((x ,(num 1))) x) 'lurk:nil-env (num 1)))

(test letrec-funcall
  (test-aux `(lurk:letrec ((f (lurk:lambda (x) (lurk:+ x ,(num 1)))))
			  (f ,(num 2)))
	    'lurk:nil-env
	    (num 3)))

(test letrec-fact
  (test-aux `(lurk:letrec ((fact (lurk:lambda (n) (lurk:if (lurk:= n ,(num 0))
							   ,(num 1)
							   (lurk:* (fact (lurk:- n ,(num 1)))
								   n)))))
			  (fact ,(num 4)))
	    'lurk:nil-env
	    (num 24)
	    ))

(test letrec-complex
  (test-aux `(lurk:letrec ((fibonacci (lurk:lambda (n) (lurk:if (lurk:< n ,(num 2))
								,(num 1)
								(lurk:+ (fibonacci (lurk:- n ,(num 1)))
									(fibonacci (lurk:- n ,(num 2))))))))
			  (fibonacci ,(num 7)))
	    'nil-env
	    (num 21)
	    ))

#+nil(test evaluation-spec
  (is (compare-spec 'evaluation 'syn-evaluation)))
