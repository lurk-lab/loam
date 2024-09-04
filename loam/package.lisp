(cl:in-package common-lisp)

(defpackage field
  (:use #:common-lisp)
  (:import-from #:it.bese.FiveAm #:def-suite #:def-suite* #:in-suite #:test #:is #:run! #:signals #:finishes #:skip)
  (:import-from #:macros #:symbolconc)
  (:export #:field #:field #:field-element #:field-equal #:field-mixin0 #:field-mixin #:field<- #:f<- #:field-element-val #:field-element-field
           #:field-bytes #:field-name #:compatible-p
           #:add #:mul #:sub #:div #:inverse #:add-assign #:mul-assign  #:sub-assign #:div-assign #:invert #:==
           #:*field* #:with-field #:with-lexical-field #:*bls12-381* #:*pallas* #:*vesta* #:*goldilocks* #:*baby-bear* #:*mersenne-31*
           #:*print-field-name*
           ))

(defpackage content-addressing
  (:use #:common-lisp)
  (:nicknames #:ctaddr)
  (:import-from #:it.bese.FiveAm #:def-suite #:def-suite* #:in-suite #:test #:is #:run! #:signals #:finishes #:skip)
  (:import-from #:ironclad #:make-digest #:digest-sequence #:update-digest #:produce-digest #:sha256)
  (:import-from #:field #:field #:*field* #:with-field #:field-equal #:field-mixin #:field-mixin0 #:field<- #:f<-
                #:field-element #:field-element-field #:field-element-val #:field-bytes
                #:add #:mul #:sub #:div #:inverse #:add-assign #:mul-assign  #:sub-assign #:div-assign #:invert #:==)
  (:export #:content-addressing #:store #:cache-zptr  #:make-standard-ctaddr #:zptr #:zptr-tag #:zptr-value #:zptr<- #:zptr<-2 #:*ctaddr* #:*store* #:*zptr-aux*
           #:content-addressable #:word-elements #:inverse-zptr #:word<-ca #:store-ctaddr #:find-tag #:tag-element
           #:cont #:terminal #:outermost))

(defpackage memoset
  (:use #:common-lisp)
  (:import-from #:it.bese.FiveAm #:def-suite #:def-suite* #:in-suite #:test #:is #:run! #:signals #:finishes #:skip)
  (:export #:memoset #:prove #:defer #:consistentp))

(defpackage machine
  (:use :common-lisp)
  (:import-from #:base #:todo #:sexp)
  (:import-from #:macros #:with-gensyms)
  (:import-from #:it.bese.FiveAm #:def-suite #:def-suite* #:in-suite #:test #:is #:run! #:signals #:finishes #:skip)
  (:import-from #:field #:field #:*field* #:field-element #:compatible-p #:== #:field<- #:field-mixin #:with-lexical-field #:*print-field-name*)
  (:import-from #:memoset #:memoset #:prove #:defer #:consistentp)
  (:import-from #:content-addressing #:zptr #:zptr<- #:store #:*store* #:*ctaddr* #:make-standard-ctaddr)
  (:export #:machine #:machine #:machine-state #:machine-store #:defmachine #:with-query #:coprocessor #:query
           #:evaluate #:evaluate-query #:make-claim #:execute #:terminatedp #:f))

(defpackage evaluation
  (:use :common-lisp)
  (:import-from #:base #:todo)
  (:import-from #:macros #:with-gensyms)
  (:import-from #:it.bese.FiveAm #:def-suite #:def-suite* #:in-suite #:test #:is #:run! #:signals #:finishes #:skip)
  (:import-from #:field #:field #:*field* #:compatible-p #:== #:field-element #:field-element-val #:field<- #:f<- #:field-mixin #:with-lexical-field #:*print-field-name*)
  (:import-from #:content-addressing #:zptr #:zptr-tag #:zptr-value #:zptr<- #:zptr<-2 #:store #:*store* #:*ctaddr* #:cache-zptr
                #:*zptr-aux* #:make-standard-ctaddr #:content-addressable #:word-elements #:inverse-zptr #:word<-ca #:store-ctaddr #:find-tag #:tag-element
                #:cont #:terminal #:outermost)
  (:import-from #:machine #:machine #:machine-state #:machine-store #:defmachine #:with-query #:coprocessor #:query
                #:evaluate #:evaluate-query #:make-claim #:execute #:terminatedp))

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
  (:export #:ptr #:make-ptr #:wide-ptr #:make-wide-ptr #:widen #:element #:tag #:tag-name #:tag-value #:wide-elements)
  )

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

