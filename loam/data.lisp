(declaim (optimize safety))

;; TODO:
;; - inverse
;; - :fun
;; - :thunk

(in-package #:data)
(def-suite* data-suite :in loam:master-suite)

;; '(:nil :cons :sym :fun :num :str :char :comm :u64 :key :env :err :thunk)))
(deflexical +tags+ (allocation-tag-names (make-instance 'lurk-allocation)))

(deflexical +lurk-built-in-package+ (find-package :lurk.builtin))

;; bignum is reserved.
(deftype wide-num () '(unsigned-byte 256))

(defstruct (num (:constructor num (value)))
  (value 0 :type element))

(defstruct (comm (:constructor comm (secret value)))
  (secret 0)
  (value 0))


(defun tag (thing)
  (etypecase thing
    (null :nil)
    (cons :cons)
    (keyword :key)
    (symbol (if (eq (symbol-package thing) +lurk-built-in-package+) :builtin :sym))
    (num :num)
    ((unsigned-byte 64) :u64)
    (wide-num :bignum)
    (function :fun)
    (string :str)
    (character :char)
    (comm :comm)))

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
    (value :sym nil))
  (:method ((tag (eql :cons)) (x cons))
    (let ((car (intern-wide-ptr (car x)))
          (cdr (intern-wide-ptr (cdr x))))
      (hash (wide-ptr-tag car) (wide-ptr-value car) (wide-ptr-tag cdr) (wide-ptr-value cdr))))
  (:method ((tag (eql :comm)) (x comm))
    (let ((secret (value :bignum (comm-secret x)))
          (value (intern-wide-ptr (comm-value x))))
      (hash secret (wide-ptr-tag value) (wide-ptr-value value))))
  (:method ((tag (eql :sym)) (s symbol))
    (let ((str-tag-value (tag-value :str)))
      (reduce (lambda (acc s)
                (hash str-tag-value (value :str s) str-tag-value acc))
              (reverse (symbol-path s))
              :initial-value (widen 0))))
  (:method ((tag (eql :builtin)) (s symbol))
    (value :sym s))
  (:method ((tag (eql :key)) (s symbol))
    (let ((str-tag-value (tag-value :str))
          (key-tag-value (tag-value :key)))
      (reduce (lambda (acc s)
                (hash key-tag-value (value :str s) str-tag-value acc))
              (reverse (symbol-path s))
              :initial-value (widen 0))))
  (:method ((tag (eql :num)) (x num))
    (widen (num-value x)))
  (:method ((tag (eql :str)) (s string))
    (reduce (lambda (acc c)
              (hash (tag-value :char) (value :char c) (tag-value :str) acc))
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
    (is (== (make-wide-ptr (tag-value :nil)
                           (wide 3265696281 3773564213 1658540249 4269831010
                                  2605307679 1922097246 3221902070 1193621601))
            (intern-wide-ptr nil)))
    (is (== (make-wide-ptr (tag-value :cons)
                           (wide 1971744287 3641459736 3774975494 1609894661
                                 2629299411 3809236520 3595245074 62596448))
            (intern-wide-ptr (cons 123 456))))
    (is (== (make-wide-ptr (tag-value :sym)
                           (wide 2124848655 671083439 1461717794 3098496062
                                 1952506637 1679783838 1710627738 3962008700))
            (intern-wide-ptr 'asparagus)))
    (is (== (make-wide-ptr (tag-value :builtin)
                           (wide 2370828549 275036126 3725919249 3828056330
                                 4119081769 2867286066 3909579972 2879896449))
            (intern-wide-ptr 'lurk:current-env)))
    (is (== (make-wide-ptr (tag-value :num) (widen 987)) (intern-wide-ptr (num 987))))
    (is (== (make-wide-ptr (tag-value :str) (widen 0)) (intern-wide-ptr "")))
    (is (== (make-wide-ptr (tag-value :str) (wide 3915542193 3963547268 1543020646 761117776
                                                  2609865840 67719049 4263057193 3398353849))
            (intern-wide-ptr "boo")))
    (is (== (make-wide-ptr (tag-value :char) (widen 65)) (intern-wide-ptr #\A)))
    (is (== (make-wide-ptr (tag-value :comm) (wide 1397905034 3832045063 2843405970 3708064556
                                                   1931248981 1080144743 1379707257 644801363))
            (intern-wide-ptr (comm 0 123))))
    (is (== (make-wide-ptr (tag-value :comm) (wide 236359359 1527390219 2343696523 758167213
                                                   871965242 1355972474 190653183 4160106812))
            (intern-wide-ptr (comm 1 123))))
    (is (== (make-wide-ptr (tag-value :comm) (wide 1728579760 934502999 283557377 3913587264
                                                   1911438967 440467652 2636934865 1478398737))
            (intern-wide-ptr (comm 0 '(brass monkey)))))
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
                           (wide 804425473 505204341 2810587548 3771856831
                                 3029221257 2686385941 1603817387 2918411353))
            (intern-wide-ptr `(foo (bar 1) (:baz #\x "monkey") ,(num 123) ,(1- (expt 2 256))))))))
