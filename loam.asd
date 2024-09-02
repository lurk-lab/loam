(asdf:defsystem "loam"
  :description "loam"
  :version "0.0.1"
  :author "porcuquine <porcuquine@gmail.com>"
  :licence "MIT"
  :depends-on ("fiveam" "unix-opts" "uiop" "ironclad" "clsql" "clsql-sqlite3" "defstar" "cl-dot" "hu.dwim.walker")
  :components ((:module "base"
                :serial t
                :components ((:file "base")
                             (:file "macros")
                             (:file "util")))
               (:module "loam"
                :serial t
                :depends-on ("base")
                :components
                ((:file "package")
                 (:file "loam")
                 (:file "lattice")
                 (:file "datalog")
                 (:file "allocation")
                 )))

  :in-order-to ((asdf:test-op (asdf:load-op "loam")))
  :perform (asdf:test-op (o c)
		         (flet ((run-suite (suite) (uiop:symbol-call :fiveam :run! suite)))
		           (let* ((suite-specs '((#:base-suite #:base)
                                                 (#:master-suite #:loam)))
                                  (failed (loop for spec in suite-specs
                                                for (name-spec package-spec) = spec
                                                for suite = (find-symbol (string name-spec) (string package-spec))
                                                unless (run-suite suite)
                                                  collect suite)))
			     (when failed
			       (error "Some tests failed: ~A." failed))))))
