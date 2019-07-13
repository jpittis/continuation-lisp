; A continuation based lisp interpreter ported to Common Lisp from the
; sheme implementation found in Lisp in Small Peices. Use the
; try-it-out function at the bottom to experiment with evaluation!

; Some test cases that I've gotten working:
;
; (try-it-out '(if (if '() '() 2) 3 4))
; (try-it-out '((lambda (x) (if x 2 3)) '()))
; (try-it-out '(begin 1 2 3))
; (try-it-out '((lambda (x) (begin 1 (set! x 3) 2 x)) 1))

(defclass value () ())
(defclass environment () ())
(defclass continuation () ((k :initarg :k :accessor k)))

(defmethod invoke (f v* r k)
  (error "not a function (f: ~a, r: ~a, k: ~a)" f r k))

(defmethod resume ((k continuation) v)
  (error "unknown continuation (k: ~a)" k))

(defmethod lookup ((r environment) n k)
  (error "not an environment (r: ~a, n: ~a, k: ~a)" r n k))

(defmethod update! ((r environment) n k v)
  (error "not an environment (r: ~a, n: ~a, k: ~a)" r n k))

(defun evaluate (e r k)
  (if (atom e)
      (cond ((symbolp e) (evaluate-variable e r k))
	    (t
	     (evaluate-quote e r k)))
      (case (car e)
	((quote) (evaluate-quote (cadr e) r k))
	((if) (evaluate-if (cadr e) (caddr e) (cadddr e) r k))
	((begin) (evaluate-begin (cdr e) r k))
	((set!) (evaluate-set! (cadr e) (caddr e) r k))
	((lambda) (evaluate-lambda (cadr e) (cddr e) r k))
	(t
	 (evaluate-application (car e) (cdr e) r k)))))

(defun evaluate-quote (v r k)
  (resume k v))

(defclass if-cont (continuation) ((et :initarg :et :accessor et)
				  (ef :initarg :ef :accessor ef)
				  (r :initarg :r :accessor r)))

(defun evaluate-if (ec et ef r k)
  (evaluate ec r (make-instance 'if-cont :k k :et et :ef ef :r r)))

(defmethod resume ((k if-cont) v)
  (evaluate (if v (slot-value k 'et) (slot-value k 'ef))
	    (slot-value k 'r)
	    (slot-value k 'k)))

(defclass begin-cont (continuation) ((e* :initarg :e* :accessor e*)
				     (r :initarg :r :accessor r)))

(defun evaluate-begin (e* r k)
  (if (pairp e*)
      (if (pairp (cdr e*))
	  (evaluate (car e*) r (make-instance 'begin-cont :k k :e* e* :r r))
	  (evaluate (car e*) r k))
      (resume k nil)))

(defmethod resume ((k begin-cont) v)
  (evaluate-begin (cdr (slot-value k 'e*))
		  (slot-value k 'r)
		  (slot-value k 'k)))

(defclass null-env (environment) ())
(defclass full-env (environment) ((others :initarg :others :accessor others)
				  (name :initarg :name :accessor name)))
(defclass variable-env (full-env) ((value :initarg :value :accessor value)))

(defun evaluate-variable (n r k)
  (lookup r n k))

(defmethod lookup ((r null-env) n k)
  (error "Unknown variable (n: ~a, r: ~a, k: ~a)" n r k))

(defmethod lookup ((r full-env) n k)
  (lookup (slot-value r 'others) n k))

(defmethod lookup ((r variable-env) n k)
  (if (eq n (slot-value r 'name))
      (resume k (slot-value r 'value))
      (lookup (slot-value r 'others) n k)))

(defclass set!-cont (continuation) ((n :initarg :n :accessor n)
				    (r :initarg :r :accessor r)))

(defun evaluate-set! (n e r k)
  (evaluate e r (make-instance 'set!-cont :k k :n n :r r)))

(defmethod resume ((k set!-cont) v)
  (update! (slot-value k 'r) (slot-value k 'n) (slot-value k 'k) v))

(defmethod update! ((r null-env) n k v)
  (error "Unknown variable (n: ~a, r: ~a, k: ~a)" n r k))

(defmethod update! ((r full-env) n k v)
  (update! (slot-value r 'others) n k v))

(defmethod update! ((r variable-env) n k v)
  (if (eq n (slot-value r 'name))
      (progn (setf (slot-value r 'value) v)
	     (resume k v))
      (update! (slot-value r 'others) n k v)))

(defclass functionlol (value) ((variables :initarg :variables :accessor variables)
			       (body :initarg :body :accessor body)
			       (env :initarg :env :accessor env)))

(defun pairp (p)
  (and (listp p)
       (not (null p))))

(defun evaluate-lambda (n* e* r k)
  (resume k (make-instance 'functionlol :variables n* :body e* :env r)))

(defmethod invoke ((f functionlol) v* r k)
  (let ((env (extend-env (slot-value f 'env) (slot-value f 'variables) v*)))
    (evaluate-begin (slot-value f 'body) env k)))

(defun extend-env (env names values)
  (cond ((and (pairp names) (pairp values))
	 (make-instance 'variable-env
			:others (extend-env env (cdr names) (cdr values))
			:name (car names)
			:value (car values)))
	((and (null names) (null values)) env)
	((symbolp names) (make-instance 'variable-env :others env :name names :value values))
	(t (error "Arity mismatch"))))

(defclass evfun-cont (continuation) ((e* :initarg :e* :accessor e*)
				     (r :initarg :r :accessor r)))

(defclass apply-cont (continuation) ((f :initarg :f :accessor f)
				     (r :initarg :r :accessor r)))

(defclass argument-cont (continuation) ((e* :initarg :e* :accessor e*)
					(r :initarg :r :accessor r)))

(defclass gather-cont (continuation) ((v :initarg :v :accessor v)))

(defun evaluate-application (e e* r k)
  (evaluate e r (make-instance 'evfun-cont :k k :e* e* :r r)))

(defmethod resume ((k evfun-cont) f)
  (evaluate-arguments (slot-value k 'e*)
		      (slot-value k 'r)
		      (make-instance 'apply-cont
				     :k (slot-value k 'k)
				     :f f
				     :r (slot-value k 'r))))

(defun evaluate-arguments (e* r k)
  (if (pairp e*)
      (evaluate (car e*) r (make-instance 'argument-cont :k k :e* e* :r r))
      (resume k no-more-arguments)))

(defvar no-more-arguments '())

(defmethod resume ((k argument-cont) v)
  (evaluate-arguments (cdr (slot-value k 'e*))
		      (slot-value k 'r)
		      (make-instance 'gather-cont :k (slot-value k 'k) :v v)))

(defmethod resume ((k gather-cont) v*)
  (resume (slot-value k 'k) (cons (slot-value k 'v) v*)))

(defmethod resume ((k apply-cont) v)
  (invoke (slot-value k 'f)
	  v
	  (slot-value k 'r)
	  (slot-value k 'k)))

(defclass bottom-cont (continuation) ((f :initarg :f :accessor f)))

(defclass primitive (value) ((name :initarg :name :accessor name)
			     (address :initarg :address :accessor address)))

(defmethod resume ((k bottom-cont) v)
  (funcall (slot-value k 'f) v))

(defmethod invoke ((f primitive) v* r k)
  (funcall (primitive-address f) v* r k))

(defun try-it-out (expr)
  (evaluate expr
	    (make-instance 'null-env)
	    (make-instance 'bottom-cont :f (lambda (x) (format t "~a~%" x)))))
