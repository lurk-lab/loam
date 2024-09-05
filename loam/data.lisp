(declaim (optimize safety))

(in-package #:data)
(def-suite* data-suite :in loam:master-suite)

;; '(:nil :cons :sym :fun :num :str :char :comm :u64 :key :env :err :thunk)))
(setf (symbol-value '+tags+) (allocation-tag-names (make-instance 'lurk-allocation)))

;; bignum is reserved.
(deftype wide-num () '(unsigned-byte 256))

(defstruct (num (:constructor num (value)))
  (value 0 :type element))

(defstruct (comm (:constructor comm (value)))
  (value 0 :type wide-num))

(defun tag (thing)
  (etypecase thing
    (null :nil)
    (cons :cons)
    (keyword :key)
    (symbol :sym)
    (num :num)
    ((unsigned-byte 64) :u64)
    (wide-num :bignum)
    (function :fun)
    (string :str)
    (character :char)))

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

(defgeneric value (tag thing)
  (:method ((tag (eql :nil)) x)
    (assert (null x))
    ;; Is this actually the right value for Lurk, currently?
    (widen 0))
  (:method ((tag (eql :cons)) (x cons))
    (let ((car (intern-wide-ptr (car x)))
          (cdr (intern-wide-ptr (cdr x))))
      (hash4 (wide-ptr-tag car) (wide-ptr-value car) (wide-ptr-tag cdr) (wide-ptr-value cdr))))
  (:method ((tag (eql :sym)) (s symbol))
    (reduce (lambda (acc s)
              (hash4 (tag-value :str) (value :str s) (tag-value :str) acc))
            (reverse (symbol-path s))
            :initial-value (widen 0)))
  (:method ((tag (eql :key)) (s symbol))
    (reduce (lambda (acc s)
              (hash4 (tag-value :key) (value :str s) (tag-value :str) acc))
            (reverse (symbol-path s))
            :initial-value (widen 0)))
  (:method ((tag (eql :num)) (x num))
    (widen (num-value x)))
  (:method ((tag (eql :str)) (s string))
    (reduce (lambda (acc c)
              (hash4 (tag-value :char) (value :char c) (tag-value :str) acc))
            (reverse s)
            :initial-value (widen 0)))
  (:method ((tag (eql :char)) (c character))
    (make-wide :elements (le-elements<- (char-code c) :size 8)))
  (:method ((tag (eql :u64)) x)
    (make-wide :elements (le-elements<- x :size 8)))
  (:method ((tag (eql :bignum)) x)
    (make-wide :elements (le-elements<- x :size 8 :bits 32))))

(defun intern-wide-ptr (thing)
  (let* ((tag (tag thing))
         (value (value tag thing)))
    (make-wide-ptr (tag-value tag) value)))

(defprogram test-program (hash-cache lurk-allocation)
  (relation (tag element wide)) ; (short-tag wide-tag)
  )

(test intern-wide-ptr
  (let ((*program* (make-program-instance 'test-program)))
    (is (== (make-wide-ptr (tag-value :nil) (widen 0)) (intern-wide-ptr nil)))
    (is (== (make-wide-ptr (tag-value :cons)
                           (wide 1971744287 3641459736 3774975494 1609894661
                                 2629299411 3809236520 3595245074 62596448))
            (intern-wide-ptr (cons 123 456))))
    (is (== (make-wide-ptr (tag-value :sym)
                           (wide 2124848655 671083439 1461717794 3098496062
                                 1952506637 1679783838 1710627738 3962008700))
            (intern-wide-ptr 'asparagus)))
    (is (== (make-wide-ptr (tag-value :num) (widen 987)) (intern-wide-ptr (num 987))))
    (is (== (make-wide-ptr (tag-value :str) (widen 0)) (intern-wide-ptr "")))
    (is (== (make-wide-ptr (tag-value :str) (wide 3915542193 3963547268 1543020646 761117776
                                                  2609865840 67719049 4263057193 3398353849))
            (intern-wide-ptr "boo")))
    (is (== (make-wide-ptr (tag-value :char) (widen 65)) (intern-wide-ptr #\A)))
    (is (== (make-wide-ptr (tag-value :u64) (widen 123)) (intern-wide-ptr 123)))
    (is (== (make-wide-ptr (tag-value :key)
                           (wide 1270829131 4078411283 1745303874 12646417 3698838549
                                 3212511736 3767934754 2081283370))
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
                           (wide 3508982854 2318477174 820379700 1535513510
                                 2128828907 3288824845 2000843403 2393445986))
            (intern-wide-ptr `(foo (bar 1) (:baz #\x "monkey") ,(num 123) ,(1- (expt 2 256))))))))
