;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Macros

(defpackage base.macros
  (:use :common-lisp)
  (:nicknames :macros)
  (:export
   #:with-gensyms #:with-gensyms*
   #:aif #:awhen #:if-bind #:when-bind
   #:with-captured-bindings
   #:*debug* #:*break-on-display* #:*break-on-debugging* #:*silence-debug-warning* #:*dval*
   #:*dbg #:display #:dbreak #:isetq
   #:symbolconc
   #:deflexical #:deflexical-var))

(in-package base.macros)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defun symbolconc (&rest symbols)
    (intern (apply #'concatenate 'string (mapcar #'string symbols)))))

;;; Macro-writing macros come first.
(defmacro with-gensyms ((&rest vars) &body body)
  (let ((binding-form
         (lambda (var)
                `(,var (gensym ,(format nil "~a-" (string var)))))))
    `(let (,@(mapcar binding-form vars))
       ,@body)))

(defmacro with-gensyms* (vars &body body)
  (let ((binding-form
         (lambda (var)
                `(,var (gensym ,(format nil "~a-" (string var)))))))
    `(let (,@(mapcar binding-form vars))
       ,@body)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; General/Util -- Could/should have own package.

(defmacro aif (condition then &optional else)
  `(let ((it ,condition))
     (if it
	 ,then
       ,else)))

(defmacro awhen (condition &body body)
  `(let ((it ,condition))
     (when it
       ,@body)))

(defmacro if-bind ((var condition) then &optional else)
  `(let ((,var ,condition))
     (if ,var
       ,then
       ,else)))

(defmacro when-bind ((var condition) &body body)
  `(let ((,var ,condition))
     (when ,var
       ,@body)))


;;; Should this have a better name?
(defmacro with-captured-bindings ((&rest vars) &body body)
  "Establish a scope in which current values of VARS are captured in new bindings."
  `(let ,(mapcar (lambda (var)
                   `(,var ,var))
          vars)
     ,@body))

;;;; Debugging

(defun expand-display (form)
  (with-gensyms (values)
    `(let ((,values (multiple-value-list ,form)))
       (format *debug-io* ,(format nil "~w => ~~w~%" form) (car ,values))
       (values-list ,values))))

(defvar *debug* t)
(defvar *break-on-display* nil)

(defvar *break-on-debugging* nil)
(defvar *silence-debug-warning* nil)

(defvar *dval* nil "Value in which to stash debugging values via DBREAK.")

(defmacro dbg (&body body)
  `(cond (*debug* (progn (unless *silence-debug-warning*
                           (warn (format nil "~w" `(debugging ,',@body))))
                    ,@body))
         (t (when *break-on-debugging*
              (error "debugging form")))))

(defmacro display (&rest forms)
  `(if *debug*
     (multiple-value-prog1 (progn ,@(mapcar #'expand-display forms))
       (when *break-on-display* (break))
       (terpri *debug-io*))
     (progn ,@forms)))

(defmacro dbreak (value-form)
  `(progn
     (setq *dval* ,value-form)
     (break)))

(defmacro isetq (var val)
  `(setf (symbol-value ',var) ,val))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Global Lexicals

;;; I finally decided to use the SYMBOL-VALUE as the location for global lexical
;;; values (rather than stashing it in a symbol property).
;;; I did this so that unbound global lexicals will be handled automatically.
;;; The consequences of locally declaring SPECIAL a symbol which has been conceptually
;;; proclaimed lexical through DEFLEXICAL or DEFLEXICAL-VAR is undefined for now,
;;; but it may make sense to expose the implementation, allowing for some interesting
;;; behavior.  On some level, all this stuff does is suppress the warnings one would
;;; otherwise receive about unbound variables.

(defmacro define-lexical-variable (symbol &key (value nil value-p) 
                                            if-unbound documentation)
  `(progn
     (eval-when (:compile-toplevel :load-toplevel :execute)
       (define-symbol-macro ,symbol (symbol-value ',symbol))
       ,@(when documentation
           (check-type documentation string)
           (list `(setf (documentation ',symbol 'variable) ,documentation))))
     ,@(when value-p
         (list
          `(eval-when (:load-toplevel :execute)
             ,(if if-unbound
                  `(when (not (boundp ',symbol))
                     (setq ,symbol ,value))
                `(setq ,symbol ,value)))))
     ',symbol))

(defmacro deflexical (variable value &optional documentation)
  "Defines VARIABLE as a global lexical variable and sets its initial value to VALUE.
Analogous to DEFPARAMETER."
  `(define-lexical-variable ,variable :value ,value :documentation ,documentation))

(defmacro deflexical-var (variable &optional (value nil value-p) documentation)
  "Define VARIABLE as a global lexical variable and if it is unbound,  sets its
initial value to value.  Analogous to DEFVAR."
  (if value-p
      `(define-lexical-variable ,variable :value ,value :if-unbound t 
                                :documentation ,documentation)
    `(define-lexical-variable ,variable :documentation ,documentation)))
