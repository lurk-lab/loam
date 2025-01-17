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
  (:export #:*prototype* #:*program* #:*trace* #:*trace-success-only* #:*step* #:trace-log #:trace-success-log #:relation #:lattice #:signal-relation #:synthesize-rule #:dual #:rule #:include #:make-program-instance
           #:includes #:included-programs  #:rules #:<-- #:_ #:== #:run #:init
           #:program #:defprogram #:prototype #:initialize-program #:find-system #:find-relation #:find-prototype
           #:relation-counts #:print-relation-counts #:relation-tuples #:relation-tuple-list #:less #:spec #:compare-spec))

(defpackage allocation
  (:use #:common-lisp)
  (:import-from #:base #:todo #:compose)
  (:import-from #:macros #:display #:awhen #:it)
  (:import-from #:it.bese.FiveAm #:def-suite #:def-suite* #:in-suite #:test #:is #:run! #:signals #:finishes #:skip)
  (:import-from #:defstar #:defun* #:defmethod* #:defgeneric* #:->)
  (:import-from #:lattice #:dual #:dual-value #:defdual #:with-duals)
  (:import-from #:datalog #:*program* #:*trace* #:*step* #:trace-log #:relation #:lattice #:signal-relation #:synthesize-rule #:dual #:rule #:rules #:make-program-instance
                #:include #:includes #:included-programs #:<-- #:_ #:== #:run #:init #:program #:defprogram #:initialize-program
                #:find-relation #:find-prototype #:relation-counts #:print-relation-counts #:relation-tuples
                #:relation-tuple-list #:less #:spec #:compare-spec)
  (:export #:*program* #:element #:dual-element #:ptr #:make-ptr #:ptr-tag #:ptr-value #:wide-ptr #:make-wide-ptr #:wide-ptr-tag #:wide-ptr-value #:make-wide
           #:widen #:wide #:wide-elements #:wide-nth #:element #:tag #:tag-name #:tag-value #:tag-address #:nth-tag #:lurk-allocation
           #:allocation-tag-names #:alloc #:hash-cache #:hash #:unhash #:+element-bits+ #:is-tag-p #:has-tag-p #:defmem))

(defpackage lurk.builtin
  (:export #:atom #:apply #:begin #:car #:cdr #:char #:commit #:comm #:bignum #:cons #:current-env #:emit #:empty-env #:eval
           #:eq #:eqq #:type-eq #:type-eqq #:hide #:if #:lambda #:let #:letrec #:u64 #:open #:quote #:secret #:strcons #:list
           #:+ #:- #:* #:/ #:% #:= #:< #:> #:<= #:>= #:breakpoint #:fail))

(defpackage lurk
  (:import-from #:lurk.builtin #:atom #:apply #:begin #:car #:cdr #:char #:commit #:comm #:bignum #:cons #:current-env #:emit
                #:empty-env #:eval #:eq #:eqq #:type-eq #:type-eqq #:hide #:if #:lambda #:let #:letrec #:u64 #:open
                #:quote #:secret #:strcons #:list #:+ #:- #:* #:/ #:% #:= #:< #:> #:<= #:>= #:breakpoint #:fail)
  (:export #:atom #:apply #:begin #:car #:cdr #:char #:commit #:comm #:bignum #:cons #:current-env #:emit #:empty-env #:eval
	   #:eq #:eqq #:type-eq #:type-eqq #:hide #:if #:lambda #:let #:letrec #:u64 #:open #:quote #:secret #:strcons #:list
	   #:+ #:- #:* #:/ #:% #:= #:< #:> #:<= #:>= #:breakpoint #:fail #:nil #:t #:nil-env)
  )

(defpackage lurk-user
  (:import-from #:lurk #:atom #:apply #:begin #:car #:cdr #:char #:commit #:comm #:bignum #:cons #:current-env #:emit #:empty-env #:eval
	   #:eq #:eqq #:type-eq #:type-eqq #:hide #:if #:lambda #:let #:letrec #:u64 #:open #:quote #:secret #:strcons #:list
	   #:+ #:- #:* #:/ #:% #:= #:< #:> #:<= #:>= #:breakpoint #:fail #:nil #:t #:nil-env))

(defpackage data
  (:use #:common-lisp)
  (:import-from #:it.bese.FiveAm #:def-suite #:def-suite* #:in-suite #:test #:is #:run! #:signals #:finishes #:skip)
  (:import-from #:defstar #:defun* #:defmethod* #:defgeneric* #:->)
  (:import-from #:macros #:awhen #:it #:display #:deflexical)
  (:import-from #:datalog #:defprogram #:make-program-instance #:relation)
  (:import-from #:allocation #:*program* #:lurk-allocation #:allocation-tag-names #:element #:wide #:wide-elements #:wide-nth
                #:make-wide #:widen #:wide-ptr #:make-wide-ptr #:wide-ptr-tag #:wide-ptr-value #:tag-name #:tag-value
                #:tag #:== #:hash-cache #:hash #:unhash #:+element-bits+ #:nth-tag)
  (:export #:builtin-idx #:+builtins+ #:intern-wide-ptr #:num #:env #:thunk #:fun))

(defpackage evaluation
  (:use #:common-lisp)
  (:import-from #:base #:todo #:compose)
  (:import-from #:macros #:display #:awhen #:it #:symbolconc)
  (:import-from #:it.bese.FiveAm #:def-suite #:def-suite* #:in-suite #:test #:is #:run! #:signals #:finishes #:skip)
  (:import-from #:defstar #:defun* #:defmethod* #:defgeneric* #:->)
  (:import-from #:lattice #:dual #:dual-value #:defdual #:with-duals)
  (:import-from #:datalog #:*program* #:*trace* #:*trace-success-only* #:*step* #:trace-log #:trace-success-log #:relation #:lattice #:signal-relation #:synthesize-rule #:dual #:rule #:rules #:make-program-instance
                #:include #:includes #:included-programs #:<-- #:_ #:== #:run #:init #:program #:defprogram #:initialize-program
                #:find-relation #:find-prototype #:relation-counts #:print-relation-counts #:relation-tuples
                #:relation-tuple-list #:less #:spec #:compare-spec)
  (:import-from #:allocation #:*program* #:element #:dual-element #:ptr #:make-ptr #:ptr-tag #:ptr-value #:wide-ptr #:make-wide-ptr #:wide-ptr-tag #:wide-ptr-value #:make-wide
           #:widen #:wide #:wide-elements #:wide-nth #:element #:tag #:tag-name #:tag-value #:tag-address #:nth-tag #:lurk-allocation
           #:allocation-tag-names #:alloc #:hash-cache #:hash #:unhash #:+element-bits+ #:is-tag-p #:has-tag-p #:defmem)
  (:import-from #:data #:builtin-idx #:+builtins+ #:intern-wide-ptr #:num #:env #:thunk #:fun))

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

