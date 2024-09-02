(declaim (optimize safety))

(in-package #:datalog)
(def-suite* datalog-suite :in loam:master-suite)

(defparameter *prototype* nil)

(defparameter *trace* nil)

(defmacro trace-log (&rest args)
  `(when *trace*
     (format *trace* ,@args)))

;; Use explicit vars instead of symbols if symbols are allowable values.
;; For now, don't, since it keeps things simpler.
;; (defstruct (var (:constructor var (name)) :predicate)
;;   (name nil :type symbol))

;; (defmacro ? (name) `(var ',name))

;; (defmethod print-object ((obj var) (s t))
;;   (format s "?~a" (var-name obj)))

(defclass lattice (relation) ())

(defstruct relation-graph (edges) (nodes))

(defclass relation ()
  ((name :initarg :name :type symbol :reader relation-name)
   ;; attribute-types should be a list of types
   (attribute-types :initarg :attribute-types :reader relation-attribute-types)
   (tuples :initarg :tuples :initform (make-hash-table :test #'equalp) :accessor relation-tuples)
   (delta :initarg :delta :initform nil :accessor relation-delta)
   (pending :initarg :pending :initform nil :accessor relation-pending)))

(defmethod print-object ((obj relation) (s t))
  (print-unreadable-object (obj s)
    (format s "~a" (spec obj))))

(defgeneric arity (thing)
  (:method ((tuple cons)) (length tuple))
  (:method ((relation relation)) (length (relation-attribute-types relation))))

(defmethod check-tuple-type ((tuple cons) (relation relation))
  (assert (= (arity tuple) (arity relation)))
  (mapcar (lambda (elt type) (typep elt type)) tuple (relation-attribute-types relation)))

(defmethod relation-tuple-list ((r relation))
  (loop for tuple being the hash-keys of (relation-tuples r) collect tuple))

(defmethod sorted-relation-tuples ((r relation))
  (sort (relation-tuple-list r) #'less))

(defmethod relation-count ((r relation))
  (hash-table-count (relation-tuples r)))

(defmethod relation-types ((r relation))
  (mapcar #'cadr (relation-attribute-types r)))

(defclass rule ()
  ((lhs :initarg :lhs :reader rule-lhs)
   (rhs :initarg :rhs :reader rule-rhs)
   (src :initarg :src :reader rule-src)
   (plans :initarg :plans :reader rule-plans)
   (src-program :initarg :src-program :accessor rule-src-program)
   (program :initarg :program :initarg nil :accessor rule-program)))

(defmethod print-object ((obj rule) (s t))
  (print-unreadable-object (obj s)
    (format s "~a" (spec obj))))

(defgeneric rhs-relations (x)
  (:method ((rule rule))
    (let ((segments (rule-rhs rule)))
      (loop for segment in segments
            append (rhs-relations segment)
            when (eql (car segment) :predicate)
              append (mapcar #'predicate-head (cdr segment)))))
  (:method ((segment cons))
    (when (eql (car segment) :predicate)
       (mapcar #'predicate-head (cdr segment)))))

(defmethod lhs-relations ((rule rule))
  (mapcar #'predicate-head (remove-if-not (lambda (x) (typep x 'predicate)) (rule-lhs rule))))

(defclass relations-mixin ()
  ((relations :initform (make-hash-table) :accessor relations)))

(defmethod relation-counts ((r relations-mixin))
  (loop for name being the hash-keys of (relations r)
        for relation being the hash-values of (relations r)
        collect (cons name (relation-count relation))))

(defmethod print-relation-counts ((r relations-mixin) (s t))
  (loop for (name . count) in (sort (relation-counts r) #'string< :key #'car)
        do (format s "~%~a: ~d" name count)))

(defclass rules-mixin ()
  ((rules :initform () :accessor rules)))

(defclass includes-mixin ()
  (; names of included programs
   (includes :initarg :includes :initform () :accessor includes)
   (included-programs :initarg :included-programs :initform () :accessor included-programs)))

(defclass program (relations-mixin rules-mixin includes-mixin)
  ((use-naive-evaluation :initarg :use-naive-evaluation :initform nil :accessor program-use-naive-evaluation)
   (all-subprograms)
   (all-rules)))

;; Used as key for deduplication.
(defmethod rule-ident ((rule rule))
  (list :src-program (rule-src-program rule) :src (rule-src rule)))

(defun compute-all-rules (program)
  (let* ((sub-program-rules (reduce #'append (mapcar #'all-rules (all-subprograms program))))
         (rules (append (rules program) sub-program-rules)))
    (remove-duplicates rules :key #'rule-ident
                             :test #'equal)))

(defun compute-all-subprograms (program)
  (remove-duplicates (when (slot-boundp program 'included-programs)
                       (loop for program in (included-programs program)
                             append (all-programs program)))))

(defmethod all-subprograms ((program program))
  (if (slot-boundp program 'all-subprograms)
      (slot-value program 'all-subprograms)
      (setf (slot-value program 'all-subprograms) (compute-all-subprograms program))))

(defmethod all-programs ((program program))
  (cons program (all-subprograms program)))

(defmethod all-rules ((program program))
  (if (slot-boundp program 'all-rules)
      (slot-value program 'all-rules)
      (setf (slot-value program 'all-rules) (compute-all-rules program))))

(defun all-relations (program)
  (let ((relations (reduce #'append (mapcar #'relation-list (all-programs program)))))
    (assert (= (length relations) (length (remove-duplicates relations))))
    relations))

(defmethod build-relation-graph ((program program))
  (let ((edges (remove-duplicates
                (loop for rule in (rules program)
                      append (loop for lhs in (lhs-relations rule)
                                   append (loop for rhs in (rhs-relations rule)
                                                collect (list rhs lhs))))
                :test #'equal))
        (nodes (relations program)))
    (make-relation-graph :edges edges :nodes nodes)))

(defmethod cl-dot:graph-object-edges ((graph relation-graph))
  (relation-graph-edges graph))

;; dot -Tpng output.dot > output.png

(defun print-relation-graph (program &rest options &key (stream *standard-output*) (directed t))
  (declare (ignore directed stream))
  (apply #'cl-dot:print-graph (cl-dot:generate-graph-from-roots (datalog::build-relation-graph program) '()) options))

;; (defun show-graph (program)
;;   (let ((dot-stream (make-string-output-stream)))
;;     (print-relation-graph program :stream dot-stream)
;;     (uiop:run-program (format nil "dot -Tpng" (implementation-external-path impl))
;;                     :input 
;;                     :output 'string)

(defmethod cl-dot:graph-object-node ((graph relation-graph) (relation-name symbol))
  (make-instance 'cl-dot:node :attributes (list :label relation-name)))


(defgeneric duplicate (thing)
  (:method ((relation relation))
    (make-instance (class-name (class-of relation))
                              :name (relation-name relation)
                              :attribute-types (relation-attribute-types relation)
                              :tuples (duplicate (relation-tuples relation))
                              :delta (duplicate (relation-delta relation))
                              :pending (duplicate (relation-pending relation))))
  (:method ((rule rule))
    (make-instance (class-name (class-of rule))
                   :lhs (rule-lhs rule)
                   :rhs (rule-rhs rule)
                   :plans (rule-plans rule)
                   :src (rule-src rule)))
  (:method ((list list)) (mapcar #'identity list))
  (:method ((hash-table hash-table))
    (let ((h (make-hash-table :test (hash-table-test hash-table))))
      (loop for k being the hash-keys of hash-table
            for v being the hash-values of hash-table
            do (setf (gethash k h) v))
      h))
  )

(defun duplicate-with-programs (program src-program rule)
  (let ((rule (duplicate rule)))
    (setf (rule-program rule) program
          (rule-src-program rule) src-program)
    rule))

(defmethod add-rule ((r rules-mixin) (rule rule))
  (push rule (rules r)))

(defmethod add-relation ((r relations-mixin) (relation relation))
  (setf (gethash (relation-name relation) (relations r)) relation))

(defmethod add-lattice ((r relations-mixin) (lattice lattice))
  (setf (gethash (relation-name lattice) (relations r)) lattice))

(defgeneric find-relation (thing name)
  ;; highest precedence: if THING directly contains a relation named NAME, return it (via OR method-combination)
  (:method or ((r relations-mixin) (name symbol))
    (gethash name (relations r)))
  ;; lower precedence: otherwise, search its INCLUDES recursively, in order, returning the first match.
  (:method or ((i includes-mixin) (name symbol))
    (dolist (program (included-programs i))
      (awhen (find-relation program name)
        (return-from find-relation it))))
  (:method-combination or))

(defmethod find-relation-for-rule ((outer-program program) (rule rule) (name symbol))
  (let ((local-program (rule-program rule)))
    (or (find-relation local-program name)
        (find-relation outer-program name))))

(defclass prototype (program)
  ((name :initarg :name :type symbol :reader prototype-name)))

(defmethod relation-list ((r relations-mixin))
  (loop for relation being the hash-values of (relations r) collect relation))

(defmethod print-object ((obj prototype) (s t))
  (print-unreadable-object (obj s)
    (format s "~a" (spec obj :print-object t))))

(defgeneric program-superclasses (x)
  (:method ((name symbol))
    (program-superclasses (find-class name)))
  (:method ((class class))
    (remove 'program
            (mapcar #'class-name (sb-mop:class-direct-superclasses class)))))

(test partition
  (is (equal '((:q) (1 2 3) (:a :b) (4 5 6)) (partition '(:q 1 2 3 :a :b 4 5 6) :key #'numberp))))

(defgeneric include-prototype (program &rest keys )
  (:method ((name symbol) &key &allow-other-keys)
    (pushnew name (includes *prototype*)))
  #+(or)
  (:method ((name symbol) &rest keys)
    (let ((prototype (find-prototype name)))
      (assert prototype)
      (apply #'include-prototype prototype keys)))
  (:method ((prototype prototype) &key require-unique-relations require-unique-rules &allow-other-keys)
    (loop for relation being the hash-values of (relations prototype)
          do (when require-unique-relations (assert (not (find-relation *prototype* (relation-name relation)))))
          do (add-relation *prototype* relation))
    (when require-unique-rules
      (assert (not (intersection (rules prototype) (rules *prototype*)))))

    (let ((rules-to-add (set-difference (rules prototype) (rules *prototype*))))
      (when rules-to-add
        (setf (rules *prototype*) (append rules-to-add (rules *prototype*)))))))

;; Returns a list of (rule . bindings).
(defmethod process-rules ((r rules-mixin))
  (trace-log "~%--------------------------------------------------------------------------------~%")
  (loop for rule in (all-rules r)
        collect (cons rule (process-rule rule))))

;; Returns a list of bindings corresponding to each matched rule.
(defun process-rule (rule)
  (let ((program (rule-program rule)))
    (trace-log "~%----------------------------------------~%")
    (trace-log "RULE~a: " (lhs-relations rule))
    (let ((matching-bindings ())
          (initial-segment-p t))
      (labels ((process-with-bindings (segments bindings)
                 (trace-log "->")
                 (cond
                   (segments (destructuring-bind ((segment-kind . segment) . more-segments)
                                 segments
                               (let ((initial-p initial-segment-p))
                                 (setq initial-segment-p nil)
                                 (process-segment segment-kind program segment bindings
                                                  (lambda (new-bindings)
                                        ;(trace-log "new-bindings: ~a~%" new-bindings)
                                                    (process-with-bindings more-segments new-bindings))
                                                  initial-p))))
                   (t
                    (trace-log "!")
                    ;; FIXME: PUSHNEW is expensive, here and below. Use a hash set.
                    (pushnew bindings matching-bindings :test #'==)
                    (dolist (bindings matching-bindings)
                      (dolist (insertion-predicate (rule-lhs rule))
                        (let ((to-insert (mapcar (lambda (term)
                                                   (resolve term bindings program))
                                                 (predicate-args insertion-predicate))))
                          ;; TODO: compile the rule to avoid (e.g.) find-relation below, etc.
                          (add-pending-tuple (find-relation program (predicate-head insertion-predicate)) to-insert program))))))))
        (dolist (plan (rule-plans rule))
          (process-with-bindings (plan-segments plan) ()))

        (when matching-bindings
          (trace-log "SUCCESS with ~d new bindings" (length matching-bindings))
          (trace-log "~%~a~%" matching-bindings)
          (trace-log ".~%")
          )

        matching-bindings))))

;; TODO: Split this into two functions and dispatch from here, rather than entangle with all the case/typecase below.
(defun process-segment (kind program segment bindings continuation initial-segment-p)
  (let ((matching-bindings ()))
    (trace-log "[")
    (labels ((process-with-bindings (rhs bindings use-delta)
               (cond
                 (rhs (destructuring-bind (item . more-rhs)
                          rhs
                        (flet ((continue-processing (new-bindings)
                                 (assert (not (null new-bindings)))
                                 ;(trace-log "$ new-bindings: ~a~%" new-bindings)
                                 (process-with-bindings more-rhs new-bindings nil)))
                          (etypecase item
                            (predicate (trace-log "pred(~a) " (predicate-head item))
                             (query (find-relation program (predicate-head item)) (predicate-args item) bindings
                                              #'continue-processing use-delta program))
                            (restriction
                             (when (evaluate (val-form item) bindings program)
                               (continue-processing bindings)))
                            (rule-binding
                             (let ((new-value (evaluate (val-form item) bindings program)))
                               (multiple-value-bind (existing-value validp)
                                   (resolve (rule-binding-var item) bindings program)
                                 (if validp
                                     (when (eql new-value existing-value)
                                       (continue-processing bindings))
                                     (continue-processing (bind (rule-binding-var item) new-value bindings))))))))))
                 (t
                  (pushnew bindings matching-bindings :test #'==)
                  (dolist (bindings matching-bindings)
                    (funcall continuation bindings))))))
      (ecase kind
        (:predicate
         (if (or (program-use-naive-evaluation program) (not initial-segment-p))
             (process-with-bindings segment bindings nil)
             ;; When using semi-naive evaluation, process all predicates repeatedly, once with each predicate processed
             ;; first, using only its delta from the previous iteration.
             ;; FIXME: This logic is not quite right. It is not minimal.
             ;; specifically, the deltas from each rhs relation are being joined with each other redundantly.
             (loop for item in segment
                   for new-segment = (cons item (remove item segment))
                   do (process-with-bindings new-segment bindings t))))
        (:control (process-with-bindings segment bindings (not (program-use-naive-evaluation program)))))
      (trace-log "]")
      matching-bindings)))

(defgeneric init (thing with)
  (:method ((r relation) (tuples list))
    (dolist (tuple tuples)
      (check-tuple-type tuple r))
    (setf (relation-pending r) tuples))
  (:method ((r relations-mixin) (plist list))
    (loop for (name tuples) on plist by #'cddr
          do (init (find-relation r name) tuples))))

(defgeneric add-pending-tuple (relation tuple program)
  (:method ((r relation) (tuple cons) (program t))
    (declare (ignore program))
    (check-tuple-type tuple r)
    (push tuple (relation-pending r)))
  (:method ((l lattice) (tuple cons) (program program))
    (check-tuple-type tuple l)
    (let* ((foundp nil)
           (found nil)
           (var (gensym "lattice-var"))
           (query-tuple `(,@(butlast tuple) ,var)))
      (query l query-tuple nil (lambda (bindings)
                                 (setq foundp t)
                                 (setq found (resolve var bindings program)))
             nil program :all t)
      (if foundp
          (let* ((supplied (car (last tuple)))
                 (joined (lattice:join found supplied)))
            (unless (equalp joined found)
              (remove-tuple l `(,@(butlast tuple) ,found))
              (push tuple (relation-pending l))))
          (push tuple (relation-pending l))))))

;; Returns t if tuple was newly-added.
(defgeneric add-tuple (r tuple)
  (:method ((r relation) (tuple cons))
    (check-tuple-type tuple r)
    (prog1 (not (gethash tuple (relation-tuples r)))
      (setf (gethash tuple (relation-tuples r)) t))))

(defgeneric remove-tuple (r tuple)
  (:method ((r relation) (tuple t))
    (remhash tuple (relation-tuples r))
    (setf (relation-pending r) (remove tuple (relation-pending r) :test #'equal))
    (setf (relation-delta r) (remove tuple (relation-delta r) :test #'equal))))

(defparameter *step* nil)

(defgeneric update (thing)
  ;; returns t if any deltas are not empty
  (:method ((r relations-mixin))
    (let ((changed (some #'identity (mapcar #'update (all-relations r)))))
      (when (and changed *step*) (break))
      changed))
  ;; Returns t if delta is not empty.
  (:method ((r relation))
    (setf (relation-delta r) (loop for tuple in (relation-pending r)
                                   when (add-tuple r tuple) collect tuple)
          (relation-pending r) nil)
    (let ((changed (not (endp (relation-delta r)))))
      (when changed
        (trace-log "Relation changed: ~a; delta-size: ~a~%" (relation-name r) (length (relation-delta r))))
      changed)))

(defun var= (a b)
  (or (eql a b)
      ;(eql (var-name a) (var-name b))
      ))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defvar *program*)

  (defun var-p (x)
    (and (typep x 'symbol) (not (keywordp x))))

  (defclass val-form ()
    ((form :initarg :form :reader val-form-form)
     (compiled :initarg :compiled :accessor val-form-compiled)
     (free-vars :initarg :free-vars :accessor val-form-free-vars)))

  (defun free-variables (form)
    (let (free-variables)
      (with-output-to-string (*error-output*)
        (setq free-variables
              (mapcar (lambda (x) (slot-value x 'hu.dwim.walker::name))
                      (remove-if-not (lambda (elt)
                                       (typep elt 'hu.dwim.walker:free-variable-reference-form))
                                     (hu.dwim.walker:collect-variable-references 
                                      (hu.dwim.walker:walk-form
                                       form))))))
      free-variables))

  (defun compile-val-form-fun (form)
    "Returns two values: a compiled function which, when called with variable bindings and program, evaluates FORM with bindings lexically and *PROGRAM* dynamically bound;
and a list of free variables in FORM."
    (values (compile nil `(lambda (bindings program)
                            (progv (cons '*program* (mapcar #'car bindings))
                                (cons program (mapcar #'cdr bindings))
                              ,form)))
            (free-variables form)))

  ;; (defmethod initialize-instance :after ((val-form val-form) &key &allow-other-keys)
  ;;   (multiple-value-bind (compiled free-vars)
  ;;       (compile-val-form-fun (val-form-form val-form))
  ;;   (setf (val-form-compiled val-form) compiled
  ;;         (val-form-free-vars val-form) free-vars)))

  (defmethod make-load-form ((val-form val-form) &optional environment)
    (declare (ignore environment))
    `(make-val-form ',(val-form-form val-form)))

  (defun make-val-form (form)
    (multiple-value-bind (compiled free-vars)
        (compile-val-form-fun form)
      (make-instance 'val-form :form form :compiled compiled :free-vars free-vars)))

  (defclass predicate ()
    ((head :initarg :head :reader predicate-head)
     (args :initarg :args :reader predicate-args)
     (src :initarg :src :reader predicate-src)))

  (defmethod make-load-form ((predicate predicate) &optional environment)
    (make-load-form-saving-slots predicate :slot-names '(head args src) :environment environment))


  (defclass predicate-step ()
    ((predicate :initarg :predicate :reader predicate-step-predicate)
     (source :initarg :source :reader predicate-step-source)))

  (defmethod make-load-form ((predicate-step predicate-step) &optional environment)
    (make-load-form-saving-slots predicate-step :slot-names '(predicate source) :environment environment))

  (defclass plan ()
    ((steps :initarg :steps :accessor plan-steps)
     (segments :initarg :segments :initform 666 :accessor plan-segments)))

  (defmethod make-load-form ((plan plan) &optional environment)
    (make-load-form-saving-slots plan :slot-names '(steps segments) :environment environment))

  (defmethod print-object ((obj predicate) (s t))
    (if (not (slot-boundp obj 'src))
        (call-next-method)
    (print-unreadable-object (obj s :type t)
      (format s "~a" (predicate-src obj)))
    ))

  (defclass val-form-mixin ()
    ((val-form :initarg :val-form :reader val-form)))

  (defgeneric free-vars (x)
    (:method ((v val-form)) (val-form-free-vars v))
    (:method ((x val-form-mixin)) (free-vars (val-form x)))
    (:method ((x t)) nil)
    (:method ((p predicate)) (remove-duplicates (loop for arg in (predicate-args p) append (free-vars arg)))))

  (defclass rule-binding (val-form-mixin)
    ((var :initarg :var :reader rule-binding-var)))

  (defmethod make-load-form ((rule-binding rule-binding) &optional environment)
    (make-load-form-saving-slots rule-binding :slot-names '(var val-form) :environment environment))

  (defclass restriction (val-form-mixin) ())

  (defmethod make-load-form ((restriction restriction) &optional environment)
    (make-load-form-saving-slots restriction :slot-names '(val-form) :environment environment))

  ;; Returns the vars this item binds.
  (defgeneric bound-vars (x)
    (:method ((r restriction)) ())
    (:method ((b rule-binding)) (list (rule-binding-var b)))
    (:method ((p predicate)) (remove-if-not #'var-p (predicate-args p))))

  (defgeneric rhs-item-kind (item)
    (:method ((p predicate)) :predicate)
    (:method ((b rule-binding)) :control)
    (:method ((r restriction)) :control))

  (defun segment-rhs (rhs-items)
    (let ((segments ())
          (current-segment ())
          (state :initial))
      (dolist (item rhs-items)
        (let ((new-state (rhs-item-kind item)))
          (unless (eql new-state state)
            (unless (eql state :initial)
              (let ((finalized-segment (cons state (nreverse current-segment))))
                (push finalized-segment segments)))
            (setq current-segment nil))
          (push item current-segment)
          (setq state new-state)))
      (unless (eql state :initial)
        (let ((finalized-segment (cons state (nreverse current-segment))))
          (push finalized-segment segments)))
      (setq current-segment nil)
      (nreverse segments)))

  (defun parse-lhs-item (item)
    (let ((value-producers (mapcar (lambda (src) (etypecase src
                                                   (symbol src)
                                                   (cons (make-val-form src))))
                                   (cdr item))))
      (make-instance 'predicate
                     :head (car item)
                     :args value-producers
                     :src item)))

  (defun parse-rhs-item (item)
    "Returns a list of predicate, rule-bindings, or restrictions."
    (destructuring-bind (head . body) item
      (case head
        (let (assert (endp (cdr body)))
          (mapcar (lambda (pair)
                    (assert (endp (cddr pair)))
                    (destructuring-bind (var val-form) pair
                      (make-instance 'rule-binding
                                     :var var
                                     :val-form (make-val-form val-form))))
                  (car body)))
        (when
            (destructuring-bind (val-form) body
              (list (make-instance 'restriction
                                   :val-form (make-val-form val-form)))))
        (t (list (parse-predicate item))))))

  (defun parse-predicate (item)
    (let ((args (mapcar (lambda (item)
                          (typecase item
                            (cons (make-val-form item))
                            (t item))) (cdr item))))
      (make-instance 'predicate :head (car item) :args args :src item)))

  (defun parse-rule-body (body)
    (let ((lhs ())
          (rhs ())
          (post-separator nil))
      (loop for item in body
            if (eq item '<--) do (progn (setq post-separator t))
              else do (if post-separator
                          (dolist (parsed (parse-rhs-item item))
                            (push parsed rhs))
                          (push (parse-lhs-item item) lhs)))
      (let ((rhs (nreverse rhs)))
        (values (nreverse lhs) (segment-rhs rhs) (make-rhs-plans rhs)))))

  ;; Returns list of plans
  (defun make-rhs-plans (rhs-items)
    (let ((predicates (remove-if-not (lambda (x) (typep x 'predicate)) rhs-items))
          (restrictions (remove-if-not (lambda (x) (typep x 'restriction)) rhs-items))
          (rule-bindings (remove-if-not (lambda (x) (typep x 'rule-binding)) rhs-items)))
      (make-plans predicates restrictions rule-bindings nil)
      ;; See comment at MAKE-PREDICATE-PLAN-STEPS-OLD.
      #+(or)
      (mapcar (lambda (steps)
                (let* ((segments (segment-rhs steps))
                       (plan (make-instance 'plan :steps steps :segments segments)))
                  (assert (plan-segments plan))
                  plan))
              (make-predicate-plan-steps-old predicates restrictions rule-bindings nil))))

  ;; Returns two values:
  ;; - a predicate with vars for all args
  ;; - a list of zero or more restrictions depending on newly-created unique args
  ;; The purpose of this is to convert predicates that dynamically create concrete arg values to be matched
  ;; into predicate-restriction(s) combinations with equivalent effect. This is necessary when the predicate's
  ;; relation has changed, and so the predicate will only be satisfied by examining the relation's delta --
  ;; even if free vars in the args are unbound.
  ;;
  ;; TODO: when we generate smart plans based on which relation is being checked for deltas, we should only perform this
  ;; substitution when the predicate is indeed that one. With indices, it will be cheaper not to perform this expansion
  ;; when not necesssary for correctness.
  (defun expand-predicate (predicate)
    (let (new-args restrictions)
      (dolist (arg (predicate-args predicate))
        (let ((var (if (var-p arg) arg (gensym (symbol-name (symbolconc (predicate-head predicate) '-arg))))))
          (etypecase arg
            (symbol (push var new-args))
            (val-form (push var new-args)
             (push (make-instance 'restriction :val-form (make-val-form `(== ,var ,(val-form-form arg))))
                            restrictions)))))
      (let ((new-args (nreverse new-args)))
        (values (make-instance 'predicate :head (predicate-head predicate) :args new-args :src (cons (predicate-head predicate) new-args))
                restrictions))))

  (defun expand-rhs-items (predicates restrictions rule-bindings)
    (let (new-predicates)
      (dolist (predicate predicates)
        (multiple-value-bind (new-predicate new-restrictions)
            (expand-predicate predicate)
          (push new-predicate new-predicates)
          (dolist (new-restriction new-restrictions)
            (push new-restriction restrictions))))
    (values (nreverse new-predicates) restrictions rule-bindings)))

  ;; For now, this only returns a single plan, which is not well optimized.
  ;; Eventually, we could include distinct plans with each predicate filtering on its deltas first.
  ;; If we ensure that every restriction comes after every predicate/binding that can bind its free variables,
  ;; we can push restrictions left (earlier) and reduce work.
  (defun make-plans (predicates restrictions rule-bindings bound-vars)
    (multiple-value-bind (predicates restrictions rule-bindings)
        (expand-rhs-items predicates restrictions rule-bindings)
      (mapcar #'describe restrictions)
      (let ((segments ()))
        (labels ((eligible-p (item)
                   (let ((eligible (subsetp (free-vars item) bound-vars)))
                     eligible)))
          (loop while predicates
                for eligible-predicates = (remove-if-not #'eligible-p predicates)
                for remaining-predicates = (remove-if #'eligible-p predicates)
                while eligible-predicates
                do (push (cons :predicate eligible-predicates) segments)
                do (dolist (predicate eligible-predicates)
                     (setq bound-vars (union bound-vars (bound-vars predicate))))
                do (setq predicates remaining-predicates))
          (when rule-bindings
            (push `(:control ,@rule-bindings) segments))
          (when restrictions
            (push `(:control ,@restrictions) segments))
          (list
           (make-instance 'plan
                          :steps (append predicates restrictions rule-bindings)
                          :segments (nreverse segments)))))))

  ;; This is defunct and not quite right, but may be useful for reference when returning to multiple pre-optimized plans.
  #+(or)
  (defun make-predicate-plan-steps-old (predicates restrictions rule-bindings bound-vars)
    (let ((steps ()))
      (labels ((eligible-p (item)
                 (let ((eligible (subsetp (free-vars item) bound-vars)))
                   eligible))
               (add-eligible-non-predicates ()
                 ;; Add all usable (no free-vars) restrictions and rule-bindings, preserving order when possible.
                 (let ((remaining-restrictions ())
                       (remaining-rule-bindings ())
                       (repeat t))
                   (loop while repeat
                         do (setq repeat nil)
                         do (dolist (restriction restrictions)
                              (pop restrictions)
                              (cond
                                ((eligible-p restriction)
                                 (push restriction steps))
                                (t (push restriction remaining-restrictions))))
                         do (dolist (binding rule-bindings)
                              (pop rule-bindings)
                              (cond ((eligible-p binding)
                                     (push binding steps)
                                     (setq bound-vars (union bound-vars (bound-vars binding)))
                                     (setq repeat t))
                                    (t (push binding remaining-rule-bindings)))))
                   (setq restrictions remaining-restrictions
                         rule-bindings remaining-rule-bindings))))
        (add-eligible-non-predicates)

        (let* ((eligible-predicates (remove-if-not #'eligible-p predicates))
               (remaining-predicates (remove-if #'eligible-p predicates)))
          (cond
            (eligible-predicates (loop for predicate in eligible-predicates
                                       for sub-steps = (make-predicate-plan-steps remaining-predicates restrictions
                                                                                  rule-bindings (union bound-vars (bound-vars predicate)))
                                       append (loop for sub in sub-steps
                                                    collect (append (reverse (append eligible-predicates steps)) sub))))
            (t (assert (endp predicates))
               (list steps)))))))
)

(defgeneric spec (x &key &allow-other-keys)
  (:method ((p prototype) &key print-object &allow-other-keys)
    `(,(if print-object 'prototype 'defprogram) ,(prototype-name p) ,(program-superclasses (prototype-name p))
       ,@(call-next-method p :toplevel nil)))
  (:method ((p program) &key (toplevel t) &allow-other-keys)
    ;; TODO: Preserve definition order (maybe).
    (let ((items (append (loop for name in (includes p)
                              collect `(include ,name))
                        (mapcar #'spec (relation-list p))
                        (mapcar #'spec (rules p))))
          (superclasses ))
      (if toplevel
          `(program ,(program-superclasses (class-of p)) ,@items)
          items)))
  (:method ((r relation) &key &allow-other-keys)
    `(relation (,(relation-name r) ,@(relation-attribute-types r))))
  (:method ((r rule) &key &allow-other-keys)
    `(rule ,@(mapcar #'spec (rule-lhs r)) <--
       ,@(loop for segment in (rule-rhs r)
               append (segment-spec segment))))
  (:method ((p predicate) &key &allow-other-keys)
    (predicate-src p))
  (:method ((r restriction) &key &allow-other-keys)
    `(when ,(spec (val-form r))))
  (:method ((b rule-binding) &key &allow-other-keys)
    `(,(rule-binding-var b) ,(spec (val-form b))))
  (:method ((v val-form) &key &allow-other-keys)
    (val-form-form v)))

(defun segment-spec (segment)
  (destructuring-bind (descriptor . components)
      segment
    (case descriptor
      (:control
       (loop for partition in (partition components)
             if (typep (car partition) 'rule-binding)
               collect `(let (,@(mapcar #'spec components)))
             else append (mapcar #'spec components)))
      (t (mapcar #'spec components)))))

(defun partition (list &key (key #'type-of) (test #'eql))
  (let ((partitions ())
        (current-partition ())
        (current-key nil))
    (dolist (elt list)
      (let ((k (funcall key elt)))
        (cond
          (current-partition (cond
                               ((funcall test k current-key) (push elt current-partition))
                               (t  (push (nreverse current-partition) partitions)
                                   (setq current-partition (list elt)
                                         current-key k))))
          (t (push elt current-partition)
             (setq current-key k)))))
    (when current-partition
      (push (nreverse current-partition) partitions))
    (nreverse partitions)))

(defmethod evaluate ((val-form val-form) (bindings t) (program program))
  (funcall (val-form-compiled val-form) bindings program))

;; Second value is nil if unbound -- so non-nil indicates result is valid.
(defgeneric resolve (var bindings program)
  #+(or)
  (:method ((var var) (bindings t))
    (let ((found (assoc var bindings :test #'equalp)))
      (if found
          (values (cdr found) t)
          (values nil nil))))
  (:method ((var symbol) (bindings t) (program t))
    (declare (ignore program))
    (let ((found (assoc var bindings :test #'var=)))
      (if found
          (values (cdr found) t)
          (values nil nil))))
  (:method ((val-form val-form) (bindings t) (program program))
    (handler-case (values (evaluate val-form bindings program) t)
      (unbound-variable () (values nil nil))))
  (:method ((val t) (bindings t) (program t))
    (declare (ignore program))
    (values val t)))

(defgeneric bind (var val bindings)
  ;(:method ((var var) (val t) (bindings t))
  (:method ((var symbol) (val t) (bindings t))
    (cons (cons var val) bindings)))

(test bind-resolve
  (multiple-value-bind (val validp) (resolve 'x (bind 'x 123 ()) :ignored)
    (is (eql val 123))
    (is (eql t validp)))
  (multiple-value-bind (val validp) (resolve 'y (bind 'x 123 ()) :ignored)
    (is (null val))
    (is (eql nil validp)))
  (multiple-value-bind (val validp) (resolve 987 (bind 'x 123 ()) :ignored)
    (is (eql 987 val))
    (is (eql t validp))))

(defgeneric query (thing query-tuple bindings callback use-delta program  &key all)
  (:method ((r relation) (query-tuple t) (bindings t) (callback function) (use-delta t) (program program) &key all)
    (let ((source (if all ;; Used when deduplicating tuples in ADD-PENDING-TUPLE
                      (append (relation-tuple-list r) (relation-pending r) (relation-delta r))
                      (if use-delta (relation-delta r) (relation-tuple-list r)))))
      (if (endp source)
          (trace-log "q FAIL ")
          (trace-log "q(~d)" (length source)))

      ;; TODO: indexes
      (loop for tuple in source
            do (query-tuple tuple query-tuple bindings callback program)))))

(defgeneric == (a b)
  (:method ((a t) (b t))
    (equalp a b))
  (:method ((a array) (b array))
    (equalp a b)))

(defun ignored-var-p (var)
  (eql #\_ (char (symbol-name var) 0)))

(test ignored-var-p
  (is (ignored-var-p '_))
  (is (ignored-var-p '_foo))
  (is (not (ignored-var-p 'foo_bar)))
  (is (not (ignored-var-p 'bar))))

(defgeneric query-tuple (tuple query-tuple bindings callback program)
  (:method ((tuple cons) (query-tuple cons) (bindings t) (callback function) (program t))
    (loop for val in tuple
          for maybe-val in query-tuple
          do (multiple-value-bind (query-val boundp)
                 (resolve maybe-val bindings program)
               ;; TODO: should the comparison be specifiable or other than eql?
               (if boundp
                   (unless (== query-val val)
                     (return-from query-tuple))
                   (if (and (var-p maybe-val) (not (ignored-var-p maybe-val)))
                       (setq bindings (bind maybe-val val bindings))
                       (unless (or (ignored-var-p maybe-val) (== query-val val))
                         (continue))))))
    (funcall callback bindings)))

(test query-tuple
  (flet ((test-case (tuple query-tuple expected)
           (let* ((bindings (bind 'x 123 ()))
                  (result nil)
                  (callback (lambda (bindings) tuple (setq result (+ (resolve 'x bindings :ignored) (resolve 'y bindings :ignored))))))
             (query-tuple tuple query-tuple bindings callback :ignored)
             (is (eql expected result)))))

    (test-case '(1 2) '(x y) nil)
    (test-case '(123 2) '(x y) 125)))

(defgeneric run (program)
  (:method ((program program))
    (loop for i from 0
          collect (process-rules program)
          do (trace-log "~%------------------------------------------------------------~%")
          do (trace-log "running iteration: ~a~%" i)
             ;; prevent runaways
          ;do (when (and (> i 0) (zerop (mod i 100))) (break))
          while (update program))))

(defun find-prototype (name)
  (get name '%prototype))


(defmacro relation ((name &body attribute-types))
  `(add-relation *prototype* (make-instance 'relation :name ',name :attribute-types ',attribute-types)))

(defmacro lattice ((name &body attribute-types))
  `(add-lattice *prototype* (make-instance 'lattice :name ',name :attribute-types ',attribute-types)))


(defmacro rule (&body body)
  (multiple-value-bind (lhs rhs plans)
      (parse-rule-body body)
    `(add-rule *prototype* (make-instance 'rule :lhs ',lhs :rhs ',rhs :plans ',plans :src '(rule ,@body)))))

(defmacro include (name &rest options &key require-unique-relations require-unique-rules)
  `(include-prototype ',name ,@options))

;; (defun parse-item (item)
;;   ;; todo: the items can contain constants, so we need to more than just map #'var -- need to parse/process somehow.
;;   (cons (car item) (mapcar #'var (cdr item))))


(defgeneric initialize-program (program &key &allow-other-keys)
  (:method ((program program) &key &allow-other-keys)
    ;; Default does nothing
    (progn)))

(defun intern-program (name program-table)
  (or (gethash name program-table)
      (setf (gethash name program-table)
            (make-program-instance name :program-table program-table))))

(defgeneric make-program-instance (name &key program-table))

(defmacro defprogram (name superclasses &body body)
  `(let ((*prototype* (make-instance 'prototype :name ',name)))
     (progn ,@body)

     (setf (rules *prototype*) (nreverse (rules *prototype*)))
     (setf (get ',name '%prototype) *prototype*)

     (defclass ,name (,@superclasses program) ())

     (defmethod make-program-instance ((program (eql ',name)) &rest keys &key (program-table (make-hash-table :test #'eql)) &allow-other-keys)
       (let ((program (make-instance ',name))
             (prototype (find-prototype ',name)))
         (setf (includes program) (includes prototype))
         (setf (relations program) (make-hash-table))
         (dolist (relation (relation-list prototype))
           (setf (gethash (relation-name relation) (relations program))
                 (duplicate relation)))
         (setf (rules program)
               (loop for rule in (rules prototype) collect (duplicate-with-programs program ',name rule)))
         (setf (included-programs program) (mapcar (lambda (name) (intern-program name program-table)) (includes prototype)))
         (apply #'initialize-program  program keys)
         program))
     ',name))

(defgeneric less (a b)
  (:method ((a null) (b null)) nil)
  (:method ((a null) (b t)) t)
  (:method ((a t) (b null)) nil)
  (:method ((a number) (b number)) (< a b))
  (:method ((a string) (b string)) (string< a b))
  (:method ((a dual) (b dual))
    (less (dual-value a) (dual-value b)))
  (:method ((a cons) (b cons))
    (or (less (car a) (car b))
        (when (== (car a) (car b))
          (less (cdr a) (cdr b))))))

(test less
  (flet ((test-case (a b)
           (is (less a b))
           (is (not (less b a)))))
    (test-case '() '(1))
    (test-case '(1) '(1 2))
    (test-case '(1 2) '(2))
    (test-case "asdf" "fdsa")
    (test-case nil 1)
    ))

(test example
  (defprogram example ()
    (relation (edge t t))
    (relation (reachable t t))
    (rule (reachable a b) <-- (edge a b))

                                        ;      (rule (reachable a c) <-- (edge a b) (reachable b c)))
    (rule (reachable a c) <-- (reachable b c) (edge a b)))

  (let ((prototype (make-program-instance 'example)))
    (init prototype '(edge ((0 1) (1 2) (2 3) (4 5))))

    (run prototype)

    (let* ((r (find-relation prototype 'reachable))
           (reachable (sort (relation-tuple-list r) #'less)))
      ;; (0 1) (0 2) (0 3) (1 2) (1 3) (2 3) (4 5)

      ;; (display r)
      ;; (display reachable)

      (is (= 7 (length reachable)))
      (is (equal '((0 1) (0 2) (0 3) (1 2) (1 3) (2 3) (4 5)) reachable)))))

(test lattice
  (defprogram max-prog ()
    (lattice (max t t number))
    (relation (triples t t number))
    (rule (max a b n) <-- (triples a b n)))

  (let ((prototype (make-program-instance 'max-prog)))
    (init prototype '(triples ((1 2 4) (1 2 3) (1 2 5) (6 7 8) (6 7 9))))

    (run prototype)

    (let* ((r (find-relation prototype 'max))
           (max (sort (relation-tuple-list r) #'less)))

      (is (= 2 (length max)))
      (is (equal '((1 2 5) (6 7 9)) max)))))

(test binding
  (defprogram let-prog ()
    (relation (source number))
    (relation (sink number))

    (rule (sink y) <-- (source x) (let ((y (+ x 1))))))

  (flet ((test-aux (prototype)
           (init prototype '(source ((1) (2) (3))))

           (run prototype)

           (let* ((r (find-relation prototype 'sink))
                  (sink (sort (relation-tuple-list r) #'less)))

             (is (equal '((2) (3) (4)) sink)))))

    (test-aux (make-program-instance 'let-prog))
    (test-aux (make-program-instance 'let-prog :use-naive-evaluation t))))

(test restriction
  (defprogram even ()
    (relation (source number))
    (relation (sink number))

    (rule (sink x) <-- (source x) (when (evenp x))))

  (flet ((test-aux (prototype)
           (init prototype '(source ((1) (2) (3) (4))))

           (run prototype)

           (let* ((r (find-relation prototype 'sink))
                  (sink (sort (relation-tuple-list r) #'less)))

             (is (equal '((2) (4)) sink)))))

    (test-aux (make-program-instance 'even))
    (test-aux (make-program-instance 'even :use-naive-evaluation t))))

(test eval-in-lhs
  (defprogram eval-in-lhs ()
    (relation (source number))
    (relation (sink number))

    (rule (sink (+ x 1)) <-- (source x)))

  (let ((program (make-program-instance 'eval-in-lhs)))
    (init program '(source ((1) (2) (3))))

    (run program)

    (let* ((r (find-relation program 'sink))
           (sink (sort (relation-tuple-list r) #'less)))
      (is (equal '((2) (3) (4)) sink)))))

(test eval-in-rhs
  (defprogram eval-in-rhs ()
    (relation (pairs number number))
    (relation (good number))

    (rule (good x) <-- (pairs x (+ x 1))))

 (let ((program (make-program-instance 'eval-in-rhs)))
    (init program '(pairs ((1 2) (2 4) (3 4))))

    (run program)

    (let* ((r (find-relation program 'good))
           (good (sort (relation-tuple-list r) #'less)))
      (is (equal '((1) (3)) good)))))

(test include
  (defprogram even ()
    (relation (numbers number))
    (relation (even number))

    (rule (even (* 2 x)) <-- (numbers x)))

  (defprogram odd ()
    (include even)

    (relation (odd number))
    (rule (odd (+ 1 x)) <-- (even x)))

  (let ((program (make-program-instance 'even)))
    (init program '(numbers ((0) (1) (2) (3))))
    (run program)
    (setq even program)

    (let* ((r (find-relation program 'even))
           (even (sorted-relation-tuples r)))
      (is (equal '((0) (2) (4) (6)) even))))

  (let ((program (make-program-instance 'odd)))
    (setq odd program)
    (init program '(numbers ((0) (1) (2) (3))))
    (run program)

    (let* ((r (find-relation program 'odd))
           (odd (sorted-relation-tuples r)))
      (is (equal '((1) (3) (5) (7)) odd)))))

(test spec
  ;; These examples are stolen from allocation.lisp and adapted for this test. They don't make perfect sense except as source.
  (defclass hash-cache () ())
  (defprogram ptr-program ())
  (defprogram hash4 (hash-cache)
    (include ptr-program)
    (relation (hash4 ptr wide wide wide wide))
    (relation (unhash4 element wide))
    (relation (hash4-rel wide wide wide wide wide))

    (rule (hash4-rel a b c d digest) <-- (unhash4 _ digest) (let ((preimage (unhash4 digest))
                                                                  (a (nth 0 preimage))
                                                                  (b (nth 1 preimage))
                                                                  (c (nth 2 preimage))
                                                                  (d (nth 3 preimage)))))

    (rule (hash4-rel a b c d (hash4 a b c d)) <-- (hash4 ptr a b c d) (when true))
    (rule (ptr-value ptr digest) <-- (hash4 ptr a b c d) (hash4-rel a b c d digest)))

  (is (equal
       '(defprogram hash4 (hash-cache)
         (include ptr-program)
         (relation (hash4 ptr wide wide wide wide))
         (relation (unhash4 element wide))
         (relation (hash4-rel wide wide wide wide wide))

         (rule (hash4-rel a b c d digest) <-- (unhash4 _ digest) (let ((preimage (unhash4 digest))
                                                                       (a (nth 0 preimage))
                                                                       (b (nth 1 preimage))
                                                                       (c (nth 2 preimage))
                                                                       (d (nth 3 preimage)))))

         (rule (hash4-rel a b c d (hash4 a b c d)) <-- (hash4 ptr a b c d) (when true))
         (rule (ptr-value ptr digest) <-- (hash4 ptr a b c d) (hash4-rel a b c d digest)))
       (spec (find-prototype 'hash4)))))

;; This demonstrates that we can use DEFPROGRAM at toplevel, which requires ensuring the resulting program is loadable.
(defprogram let-prog2 ()
  (relation (source number))
  (relation (second number))
  (relation (sink number))

  (rule (sink y) <-- (source x) (second y) (let ((z (+ x y))))))
