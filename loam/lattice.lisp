(declaim (optimize safety))

(in-package #:lattice)
(def-suite* lattice-suite :in loam:master-suite)

(defclass dual () ((value :initarg :value :reader dual-value)))

(defmethod print-object ((obj dual) (s t))
  (print-unreadable-object (obj s :type t)
    (format s "~a" (dual-value obj))))

(defparameter *duals* (make-hash-table :test #'eql))

(defmacro with-duals (&body body)
  `(let ((*duals* (make-hash-table :test #'eql)))
     ,@body))

;; Intern duals so they will compare EQL.
(defun dual (value)
  (or (gethash value *duals*)
      (setf (gethash value *duals*) (make-instance 'dual :value value))))

(defmacro defdual (type)
  (let* ((dual-type (symbolconc 'dual- type))
         (dual-type-p (symbolconc dual-type '-p)))
    `(progn
       (defun ,dual-type-p (x)
         (and (typep x 'dual)
              (typep (dual-value x) ',type)))
       (deftype ,dual-type () '(satisfies ,dual-type-p)))))

(defdual number)

(test defdual
;  (defdual number)

  (is (eql nil (dual-number-p 123)))
  (is (eql nil (dual-number-p (dual "asdf"))))
  (is (eql t (dual-number-p (dual 123))))
  )

;; TODO: move lattice operations to own package and rename to MEET and JOIN.
(defgeneric meet (a b)
  (:method ((a dual) (b dual)) (dual (join (dual-value a) (dual-value b))))
  (:method ((a number) (b number)) (min a b)))

(defgeneric join (a b)
  (:method ((a dual) (b dual)) (dual (meet (dual-value a) (dual-value b))))
  (:method ((a number) (b number)) (max a b)))

(defstruct (dummy (:constructor dummy (x))) x)

(test meet
  (is (eql 1 (meet 1 2)))
  (is (eql 1 (meet 2 1)))
  (is (eql (dual 2) (meet (dual 1) (dual 2))))
  (is (eql (dual 2) (meet (dual 2) (dual 1)))))

(test join
  (is (eql 2 (join 1 2)))
  (is (eql 2 (join 2 1)))
  (is (eql (dual 1) (join (dual 1) (dual 2))))
  (is (eql (dual 1) (join (dual 2) (dual 1)))))


(test equality
  (with-duals
    (is (equal (dual 2) (dual 2)))
    (is (not (equal (dual 2) (dual 1))))
    (is (not (equal (dual 2) 1)))))
