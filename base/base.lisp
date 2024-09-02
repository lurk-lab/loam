(defpackage base
  (:use :common-lisp)
  (:import-from #:it.bese.FiveAm #:def-suite #:def-suite* #:in-suite #:test #:is #:run! #:signals #:finishes #:skip)
  (:export #:todo #:sexp #:compose))

(in-package base)

(def-suite* base-suite)

(deftype sexp () '(cons symbol list))

(defun todo (&rest args)
  (error (format nil "TODO: ~a" args)))
