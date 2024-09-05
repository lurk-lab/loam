(cl:in-package common-lisp)

(defpackage lattice
  (:use #:common-lisp)
  (:import-from #:macros #:symbolconc)
  (:import-from #:it.bese.FiveAm #:def-suite #:def-suite* #:in-suite #:test #:is #:run! #:signals #:finishes #:skip)
  (:export #:dual #:dual-value #:meet #:join #:with-duals #:defdual #:dual-number #:dual-number-p))

(defpackage datalog
  (:use #:common-lisp)
  (:nicknames #:dl)
  (:import-from #:base #:todo)
  (:import-from #:macros #:display #:symbolconc #:awhen #:it)
  (:import-from #:it.bese.FiveAm #:def-suite #:def-suite* #:in-suite #:test #:is #:run! #:signals #:finishes #:skip)
  (:import-from #:lattice #:dual #:dual-value #:defdual #:with-duals #:dual-number)
  (:export #:*prototype* #:*program* #:*trace* #:*step* #:trace-log #:relation #:lattice #:dual #:rule #:include #:make-program-instance
           #:includes #:included-programs #:rule-lhs #:rule-rhs #:rule-src #:rules #:<-- #:_ #:== #:run #:init
           #:program #:defprogram #:prototype #:initialize-program #:find-system #:find-relation #:find-prototype
           #:relation-counts #:print-relation-counts #:relation-tuples #:relation-tuple-list #:less))

(defpackage allocation
  (:use #:common-lisp)
  (:import-from #:base #:todo #:compose)
  (:import-from #:macros #:display #:awhen #:it)
  (:import-from #:it.bese.FiveAm #:def-suite #:def-suite* #:in-suite #:test #:is #:run! #:signals #:finishes #:skip)
  (:import-from #:defstar #:defun* #:defmethod* #:defgeneric* #:->)
  (:import-from #:lattice #:dual #:dual-value #:defdual #:with-duals)
  (:import-from #:datalog #:*program* #:*trace* #:*step* #:trace-log #:relation #:lattice #:dual #:rule #:rules #:make-program-instance
                #:include #:includes #:included-programs #:<-- #:_ #:== #:run #:init #:program #:defprogram #:initialize-program
                #:find-relation #:find-prototype #:relation-counts #:print-relation-counts #:relation-tuples
                #:relation-tuple-list #:less)
  (:export #:*program* #:element #:ptr #:make-ptr #:wide-ptr #:make-wide-ptr #:wide-ptr-tag #:wide-ptr-value #:make-wide
           #:widen #:wide #:element #:tag #:tag-name #:tag-value #:wide-elements #:lurk-allocation
           #:allocation-tag-names #:hash-cache #:hash4 #:+element-bits+))

(defpackage data
  (:use #:common-lisp)
  (:import-from #:it.bese.FiveAm #:def-suite #:def-suite* #:in-suite #:test #:is #:run! #:signals #:finishes #:skip)
  (:import-from #:defstar #:defun* #:defmethod* #:defgeneric* #:->)
  (:import-from #:macros #:display)
  (:import-from #:datalog #:defprogram #:make-program-instance #:relation)
  (:import-from #:allocation #:*program* #:lurk-allocation #:allocation-tag-names #:element #:wide #:make-wide #:widen
                #:wide-ptr #:make-wide-ptr #:wide-ptr-tag #:wide-ptr-value  #:tag-value #:tag #:== #:hash-cache #:hash4 #:+element-bits+)
  (:export #:intern-wide-ptr))

(defpackage loam
  (:use #:common-lisp)
  (:import-from #:it.bese.FiveAm #:def-suite #:def-suite* #:in-suite #:test #:is #:run! #:signals #:finishes #:skip)
  (:import-from #:defstar #:defun* #:defmethod* #:defgeneric* #:->)
  (:import-from #:lattice #:dual #:dual-value #:defdual #:with-duals)
  (:import-from #:datalog #:*program* #:*trace* #:*step* #:trace-log #:relation #:lattice #:dual #:rule #:rules #:<--
                #:_ #:== #:run #:init #:defprogram #:initialize-program #:find-relation #:relation-counts
                #:print-relation-counts #:relation-tuples #:relation-tuple-list #:less)
  (:import-from #:allocation #:ptr #:make-ptr #:wide-ptr #:make-wide-ptr #:widen #:element #:tag #:tag-name #:tag-value #:wide-elements)
  (:export #:master-suite))

(in-package loam)
(def-suite master-suite)

