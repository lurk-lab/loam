(in-package base)
;(in-suite #:base-suite)

(def-suite* util-suite :in base-suite)


(defun function-object (function-designator)
  (typecase function-designator
    (function function-designator)
    (symbol (symbol-function function-designator))))

(defun compose (&rest functions)
  (let* ((functions (mapcar #'function-object (reverse functions)))
         (first (first functions))
         (rest (reverse (rest functions))))
    (lambda (&rest args)
      (reduce #'funcall rest :initial-value (apply first args) :from-end t))))

(test compose
  (flet ((double (x) (* 2 x)))
    (is (= 3 (funcall (compose #'1+ #'double) 1)))))
