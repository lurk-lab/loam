(declaim (optimize safety))

(in-package #:allocation)
(def-suite* allocation-suite :in loam:master-suite)

(defconstant +wide-size+ 8)
(defconstant +element-bytes+ 4)
(defconstant +element-bits+ (* 8 +element-bytes+))

(deftype element () `(unsigned-byte ,+element-bits+))

(defdual element)

(deftype wide-elements () `(vector element ,+wide-size+))
(deftype wide-bytes () `(vector (unsigned-byte 8) ,(* +wide-size+ +element-bytes+)))

(defstruct wide 
  (elements (make-array '(8) :element-type 'element :initial-element 0) :type wide-elements))

(defmethod == ((a wide) (b wide)) (equalp (wide-elements a) (wide-elements b)))

(defmethod print-object ((obj wide) (s t))
  (print-unreadable-object (obj s :type t)
    (format s "~a" (wide-elements obj))))

(defun* (bytes<-wide -> wide-bytes) ((wide wide))
  (let ((bytes (make-array (list (* +wide-size+ +element-bytes+)) :element-type '(unsigned-byte 8))))
    (loop for element across (wide-elements wide)
          with idx = 0
          do (loop for i below +element-bytes+
                   do (setf (aref bytes idx) (ldb (byte 8 (* 8 i)) element))
                   do (incf idx)))
     bytes))

(test bytes<-wide
  (let ((bytes (bytes<-wide (wide 0 1 2 3 4 5 6 7))))
    (is (== #(0 0 0 0 1 0 0 0 2 0 0 0 3 0 0 0
              4 0 0 0 5 0 0 0 6 0 0 0 7 0 0 0)
            bytes))))

(defun* (wide<-bytes -> (values wide &optional)) ((bytes wide-bytes))
  (let ((elements (loop for i from 0 below 8
                        for element = 0
                        with idx = 0
                        do (loop for j below 4
                                 do (setf (ldb (byte 8 (* 8 j)) element)
                                          (aref bytes idx))
                                 do (incf idx))
                        collect element)))
    (apply #'wide elements)))

(test wide<-bytes
  (let* ((w (wide 0 1 2 3 4 5 6 7))
         (bytes (bytes<-wide w))
         (w2 (wide<-bytes bytes)))
    (is (== w w2))))

(defstruct (ptr (:constructor make-ptr (tag value)))
  (tag 0 :type element)
  (value 0 :type element))

(defmethod print-object ((obj ptr) (s t))
  (print-unreadable-object (obj s :type t)
    (format s "~a | ~a" (ptr-tag obj) (ptr-value obj))))

(defmethod == ((a ptr) (b ptr)) (equalp a b))

(defun* (ptr -> ptr) (tag-spec (value (or element dual)))
  (make-ptr (tag-address tag-spec) (typecase value
                                     (dual (dual-value value))
                                     (t value))))

(defstruct (wide-ptr (:constructor make-wide-ptr (tag value)))
  (tag 0 :type wide)
  (value 0 :type wide))

(defun* (wide-ptr -> wide-ptr) (tag-spec (value wide))
  (make-wide-ptr (tag-value tag-spec) value))

(defmethod == ((a wide-ptr) (b wide-ptr))
  (and (== (wide-ptr-tag a) (wide-ptr-tag b))
       (== (wide-ptr-value a) (wide-ptr-value b))))

(defun wide (&rest args)
  (make-wide :elements (coerce args 'wide-elements)))

(defun widen (element) (wide element 0 0 0 0 0 0 0))

(test wide
  (is (equalp (vector 1 2 3 4 5 6 7 8)
              (wide-elements (wide 1 2 3 4 5 6 7 8)))))

(defclass tag ()
  ((name :initarg :name :type keyword :reader tag-name)
   (value :initarg :value :type wide :reader tag-value)
   (address :initarg :address :type element :reader tag-address)))

(defclass hash-cache ()
  ((digest-cache :initform (make-hash-table :test #'equalp) :reader hash-cache-digest-cache)
   (preimage-cache :initform (make-hash-table :test #'equalp) :reader hash-cache-preimage-cache)))

(defclass allocation ()
  ((allocation-map :initform (make-hash-table) :reader allocation-allocation-map)
   (tag-names :initarg :tag-names :initform nil :reader allocation-tag-names)
   (tags :initform (make-hash-table) :reader allocation-tags)))

(defmethod allocation-tags ((program program))
  (some #'allocation-tags (included-programs program)))

(defclass lurk-allocation (allocation)
  ()
  (:default-initargs :tag-names '(:nil :cons :sym :fun :num :str :char :comm :u64 :key :env :err :thunk :builtin :bignum)))

(defmethod initialize-program :after ((a lurk-allocation) &key &allow-other-keys)
  (initialize-tags a (allocation-tag-names a)))

(defmethod initialize-tags ((a allocation) (tag-names t))
  (let ((tags (loop for i from 0
                    for name in tag-names
                    for tag = (make-instance 'tag :name name :address i :value (widen i))
                    collect tag
                    do (setf (gethash name (allocation-tags a)) tag)))
        (tag-relation (find-relation a 'tag)))
    (loop for tag in tags do
      (datalog::add-tuple tag-relation (list (tag-address tag) (tag-value tag))))
    ))

(defun hash4 (a b c d) (hash-wide *program* (list a b c d)))

(defgeneric* unhash (hash-cache digest)
  (:method ((h hash-cache) (digest wide))
    (unhash h (bytes<-wide digest)))
  (:method ((h hash-cache) ((digest wide-bytes) vector))
    (gethash digest (hash-cache-preimage-cache h))))

(defun unhash4 (digest)
  (awhen (unhash *program* digest)
    (when (= (length it) 4)
      it)))

(defun wide-list-p (expr) (and (listp expr) (every (lambda (x) (typep x 'wide)) expr)))
(deftype wide-list () '(satisfies wide-list-p))

(defmethod hash-cache-preimage-cache ((program program))
  (some #'hash-cache-preimage-cache (included-programs program)))

(defmethod hash-cache-digest-cache ((program program))
  (some #'hash-cache-digest-cache (included-programs program)))

(defun* hash-wide (has-hash-cache (preimage wide-list))
  (let* ((preimage-elements (length preimage))
         (preimage-size (* preimage-elements 8 4))
         (preimage-bytes (make-array (list preimage-size) :element-type '(unsigned-byte 8))))
    ;; little-endian
    (loop for n from 0 below preimage-elements
          for wide in preimage
          with idx = 0
          do (loop for j from 0 below 8
                   for elt across (wide-elements wide)
                   do (loop for k from 0 below 4
                            for byte = (byte 8 (* 8 k))
                            do (setf (aref preimage-bytes idx) (ldb byte elt))
                            do (incf idx))))
    (awhen (gethash preimage-bytes (hash-cache-digest-cache has-hash-cache))
      (return-from hash-wide it))

    (let* ((digest-bytes (ironclad:digest-sequence :sha256 preimage-bytes))
           (wide-digest (wide<-bytes digest-bytes)))
      (setf (gethash digest-bytes (hash-cache-preimage-cache has-hash-cache)) preimage
            (gethash preimage-bytes (hash-cache-digest-cache has-hash-cache)) wide-digest)

      wide-digest)))

(test hash-cache
  (let* ((hash-cache (make-instance 'hash-cache))
         (preimage (list (widen 0) (widen 1) (widen 2) (widen 3)))
         (digest (hash-wide hash-cache preimage))
         (unhashed (unhash hash-cache digest)))
    ;; unhash roundtrips
    (is (equalp preimage unhashed))
    ;; hash with cache is reproducible
    (is (equalp digest (hash-wide hash-cache preimage)))))

;; Returns dual
(defgeneric* (allocate -> (values dual &optional)) (allocation tag initial-address)
  (:method ((allocation allocation) ((tag element) t) ((initial-address dual) t))
    (let* ((allocation-map (allocation-allocation-map allocation))
           (last-address (gethash tag allocation-map))
           (allocated (if last-address (dual (1+ (dual-value last-address))) (dual 0))))
      (setf (gethash tag allocation-map) allocated)))
  (:method ((allocation allocation) ((tag-spec keyword) symbol) ((initial-address dual) t))
    (allocate allocation (tag-address tag-spec) initial-address))
  (:method ((program program) ((tag-spec keyword) symbol) ((initial-address dual) t))
    (some (lambda (included) (allocate included tag-spec initial-address)) (included-programs program))))

(defun* (alloc -> (values dual &optional)) ((tag t) (initial-address dual))
  (allocate *program* tag initial-address))

(defmethod tag-address ((spec symbol))
  (assert (typep spec 'keyword))
  (let ((tag (gethash spec (allocation-tags *program*))))
   (assert tag)
    (tag-address tag)))

(defmethod tag-value ((spec symbol))
  (assert (typep spec 'keyword))
  (let ((tag (gethash spec (allocation-tags *program*))))
    (assert tag)
    (tag-value tag)))

(defun tag-eql (a b) (= (tag-address a) (tag-address b)))

(defun has-tag-p (ptr tag-spec)
  (eql (ptr-tag ptr) (tag-address tag-spec)))

(defprogram ptr-program (lurk-allocation)
  (relation (tag element wide)) ; (short-tag wide-tag)

  (relation (ptr ptr)) ; (ptr)

  ;; It may be confusing that this relation has the same name as the ptr struct's value accessor, since the struct's field is not wide.
  (relation (ptr-value ptr wide)) ; (ptr value)

  (relation (alloc element wide)) ; (tag value)

  (relation (input-expr wide-ptr)) ; (wide-ptr)
  (relation (output-expr wide-ptr)) ; (wide-ptr)
  (relation (input-ptr ptr)) ; (ptr)
  (relation (output-ptr ptr)) ; (ptr)

  (relation (ingress ptr)) ; (ptr)
  (relation (egress ptr)) ; (ptr)

  ;; signal
  (rule (ptr ptr) <-- (alloc tag value) (let ((ptr (make-ptr tag (aref (wide-elements value) 0))))))

  ;; Ingress path
  (rule (alloc tag (wide-ptr-value wide-ptr)) <-- (input-expr wide-ptr) (tag tag (wide-ptr-tag wide-ptr)))

  (rule (ingress ptr) (input-ptr ptr) <-- (input-expr wide-ptr) (ptr-value ptr (wide-ptr-value wide-ptr)) (tag (ptr-tag ptr) (wide-ptr-tag wide-ptr)))

  ;; Egress
  (rule (egress ptr) <-- (output-ptr ptr))

  ;; Construct output-expr from output-ptr
  (rule (output-expr (make-wide-ptr wide-tag value)) <-- (output-ptr ptr) (ptr-value ptr value) (tag (ptr-tag ptr) wide-tag)))

;; hash-cache takes precedence over program in superclass list
(defprogram hash4 (hash-cache)
  (include ptr-program)
  (relation (hash4 ptr wide wide wide wide)) ; (ptr a b c d)
  (relation (unhash4 element wide)) ; (tag digest)
  (relation (hash4-rel wide wide wide wide wide)) ; (a b c d digest)

  ;; signal
  (rule (hash4-rel a b c d digest) <-- (unhash4 _ digest) (let ((preimage (unhash4 digest))
                                                                (a (nth 0 preimage))
                                                                (b (nth 1 preimage))
                                                                (c (nth 2 preimage))
                                                                (d (nth 3 preimage)))))

  ;; signal
  (rule (hash4-rel a b c d (hash4 a b c d)) <-- (hash4 ptr a b c d))

  ;; This is required to satisfy usage of ptr-program.
  ;; TODO: Make this enforceable.
  ;; signal
  (rule (ptr-value ptr digest) <-- (hash4 ptr a b c d) (hash4-rel a b c d digest)))

(defprogram cons-mem ()
  (include ptr-program)
  (include hash4)

  ;; The following relations could be determined by something like:
  ;; (constructor cons ((:tag :cons) (:initial-addr 0) (:hasher hash4))
  ;;   (car ptr) (cdr ptr))
  ; signal
  (relation (cons ptr ptr)) ; (car cdr)
  (relation (car ptr ptr)) ; (cons car)
  (relation (cdr ptr ptr)) ; (cons cdr)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;; Memory

  ;; The canonical cons Ptr relation.
  (relation (cons-rel ptr ptr ptr)) ; (car cdr cons)

  ;; Memory to support conses allocated by digest or contents.
  (lattice (cons-digest-mem wide dual-element)) ; (digest addr)
  (lattice (cons-mem ptr ptr dual-element)) ; (car cdr addr)

  ;; Populating alloc(...) triggers allocation in cons_digest_mem.
  ;; signal
  (rule (cons-digest-mem value  (alloc :cons (dual 0))) <-- (alloc (tag-address :cons) value))

  ;; Convert addr to ptr and register ptr relations.
  ;; real
  (rule (ptr ptr) (ptr-value ptr value) <-- (cons-digest-mem value addr) (let ((ptr (ptr :cons (dual-value addr))))))

  ;; signal
  (rule (cons-mem car cdr (alloc :cons (dual 0))) <-- (cons car cdr))

  ;; real
  (rule (cons-digest-mem digest addr) <--
    (cons-mem car cdr addr)
    (ptr-value car car-value) (ptr-value cdr cdr-value)
    (tag (ptr-tag car) car-tag) (tag (ptr-tag cdr) cdr-tag)
    (hash4-rel car-tag car-value cdr-tag cdr-value digest))

  ;; real
  (rule (cons-rel car cdr (ptr :cons (dual-value addr))) <-- (cons-mem car cdr addr))

  ;; real
  (rule (ptr cons) (car cons car) (cdr cons cdr) <-- (cons-rel car cdr cons))

  ;; Note, all of these (when (has-tag-p ...)) could also be expressed by 'inlining' tags and performing a match on constant data, which will perform better
  ;; with indices and a smart-enough planner.
  ;; signal
  (rule (unhash4 (tag-address :cons) digest) <-- (ingress ptr) (when (has-tag-p ptr :cons)) (ptr-value ptr digest))

  ;; signal
  (rule (alloc car-tag car-value) (alloc cdr-tag cdr-value) <--
    (unhash4 (tag-address :cons) digest)
    (hash4-rel wide-car-tag car-value wide-cdr-tag cdr-value digest)
    (tag car-tag wide-car-tag)
    (tag cdr-tag wide-cdr-tag))

  ;; real
  (rule (cons-rel car cdr (ptr :cons addr)) (cons-mem car cdr addr) <--
    (hash4-rel wide-car-tag car-value wide-cdr-tag cdr-value digest)
    (cons-digest-mem digest addr)
    (tag (ptr-tag car) wide-car-tag) (tag (ptr-tag cdr) wide-cdr-tag)
    (ptr-value car car-value) (ptr-value cdr cdr-value))

  ;; real (but maybe unnecessary)
  (rule (ptr cons) (car cons car) (cdr cons cdr) <-- (cons-rel car cdr cons))

  ;; signal
  (rule (hash4 cons car-tag car-value cdr-tag cdr-value) <--
    (egress cons)
    (cons-rel car cdr cons)
    (tag (ptr-tag car) car-tag) (tag (ptr-tag cdr) cdr-tag)
    (ptr-value car car-value) (ptr-value cdr cdr-value))

  ;; real
  (rule (ptr car) (ptr cdr) <--
    (hash4-rel wide-car-tag car-value wide-cdr-tag cdr-value _)
    (tag (ptr-tag car) wide-car-tag) (tag (ptr-tag cdr) wide-cdr-tag)
    (ptr-value car car-value) (ptr-value cdr cdr-value))

  ;; TODO: Similarly, this should be required somehow.
  ;; signal
  (rule (egress car) (egress cdr) <-- (egress cons) (cons-rel car cdr cons)))

(defprogram immediate-num ()
  (include ptr-program)
  ;; real
  (rule (ptr-value ptr (widen (ptr-value ptr))) <-- (ptr ptr) (when (has-tag-p ptr :num))))

(defprogram map-double ()
  (include ptr-program)
  (include cons-mem)
  (include immediate-num)

  (relation (map-double-input ptr)) ; (input)
  (relation (map-double ptr ptr)) ; (input-ptr output-ptr)

  ;; real
  (rule (ptr doubled) (map-double ptr doubled) <-- (map-double-input ptr) (when (has-tag-p ptr :num)) (let ((doubled (ptr :num (* 2 (ptr-value ptr)))))))

  ; signal
  (rule (map-double-input ptr) <-- (input-ptr ptr))

  ; signal
  (rule (ingress ptr) <-- (map-double-input ptr));

  ; signal
  (rule (map-double-input car) (map-double-input cdr) <-- (map-double-input cons) (cons-rel car cdr cons))

  (relation (map-double-cont ptr ptr ptr))

  ;; These rules are equivalent to the next two and cheaper for the first program.
  ;; But the second 
  ;; (rule (map-double-cont ptr double-car double-cdr) (cons double-car double-cdr) <--
  ;;   (map-double-input ptr)
  ;;   (cons-rel car cdr ptr)
  ;;   (map-double car double-car)
  ;;   (map-double cdr double-cdr))

  ;; (rule (map-double ptr double-cons) <--
  ;;   (map-double-cont ptr double-car double-cdr)
  ;;   (cons-rel double-car double-cdr double-cons))

  ;; The above with MAP-DOUBLE-CONT is equivalent to the following:

  ;; signal
  (rule (cons double-car double-cdr) <--
    (map-double-input ptr)
    (cons-rel car cdr ptr)
    (map-double car double-car)
    (map-double cdr double-cdr))

  ;; This should be the only final rule.
  ;; real
  (rule (map-double ptr double-cons) <--
    (cons-rel car cdr ptr)
    (map-double car double-car)
    (map-double cdr double-cdr)
    (cons-rel double-car double-cdr double-cons))

  ;; These are needed to satisfy PTR-PROGRAM. TODO: enforce.
  ;; real
  (rule (output-ptr output) <-- (input-ptr input) (map-double input output)))

(defun make-cons (a-tag-spec a-wide b-tag-spec b-wide)
  (hash4 (tag-value a-tag-spec) a-wide (tag-value b-tag-spec) b-wide))

(defmethod less ((a ptr) (b ptr))
  (less (cons (ptr-tag a) (ptr-value a))
        (cons (ptr-tag b) (ptr-value b))))

(defmethod cons-mem-contiguous-p ((program program))
  (let* ((cons-mem (find-relation program 'cons-mem))
         (tuples (sort (relation-tuple-list cons-mem) #'less :key #'third))
         (addrs (mapcar (compose #'dual-value #'third) tuples)))
    (loop for (addr next-addr) on addrs
          always (= next-addr (1+ addr)))))

(test allocation
  (let* ((program (make-program-instance 'map-double))
         (*program* program) ;; This is needed for MAKE-CONS.
         (c1-2 (make-cons :num (widen 1) :num (widen 2))) ; (1 . 2)
         (c2-3 (make-cons :num (widen 2) :num (widen 3))) ; (2 . 3)
         (c2-4 (make-cons :num (widen 2) :num (widen 4))) ; (2 . 4)
         (c4-6 (make-cons :num (widen 4) :num (widen 6))) ; (4 . 6)
         (c4-8 (make-cons :num (widen 4) :num (widen 8))) ; (4 . 8)
         ;(c1-2_2-4 (make-cons :cons c1-2 :cons c2-4))
         (c1-2_2-3 (make-cons :cons c1-2 :cons c2-3))
         ;(c2-4_4-8 (make-cons :cons c2-4 :cons c4-8))
         (c2-4_4-6 (make-cons :cons c2-4 :cons c4-6))
         (expected-output (wide-ptr :cons c2-4_4-6)))
    (setq asdf program)
    (init program `(input-expr ((,(wide-ptr :cons c1-2_2-3)))))

    (run program)

    ;(datalog::print-relation-counts program t)

    (is (== `((,expected-output )) (relation-tuple-list (find-relation program 'output-expr))))
    (is (not (cons-mem-contiguous-p program)))
    )
;  (test-alloc-aux 'alloc nil)
  )
