(defpackage :generate
  (:use :cl)
  (:export
   :generate-Zn
   :write-group-table-agda
   :write-group-data-decl-agda
   :write-Zn-agda))

(in-package :generate)


(defun write-Zn-agda (n &optional
			  (stream *standard-output*)
			  (group-name-prefix "G" )
			  (function-name-prefix "fn")
			  (element-name-prefix "a"))
  (format stream "module Group~A~D where~%~%" group-name-prefix n)
  (write-group-data-decl-agda
   (mapcar (lambda (i)
	     (format nil "~A~D" element-name-prefix i))
	   (loop :for i :from 0 :below n :collect i))
   group-name-prefix
   stream)
  (write-group-table-agda (generate-Zn-table n element-name-prefix)
			  stream
			  function-name-prefix
			  group-name-prefix))

(defun generate-Zn-table (n &optional (prefix "a"))
  "Generate the Nth Cyclic Group"
  (declare (type fixnum n))
  (do ((i 0 (1+ i))
       (table nil))
      ((= i n) table)
    (do ((j 0 (1+ j)))
	((= j n))
      (push (list (format nil "~A~D" prefix i)
		  (format nil "~A~D" prefix j)
		  (format nil "~A~D" prefix (mod (+ i j) n)))
	    table))))

(defun write-group-table-agda (table &optional
				       (stream *standard-output*)
				       (fn-prefix "fn")
				       (group-prefix "G"))
  "Write the group table as an Agda function"
  (let* ((order (isqrt (length table)))
	 (fn-name (format nil "~A~D" fn-prefix order))
	 (group-name (format nil "~A~D" group-prefix order)))
    (format stream "~A : ~A -> ~A -> ~A~%"
	    fn-name group-name group-name group-name)
    (loop :with len-str = order
	  :for i :in table 
	  :do (format stream "~A~D ~A ~A = ~A~%"
		      fn-prefix len-str (car i) (cadr i) (caddr i)))))

(defun write-group-data-decl-agda (elements &optional
					      (prefix "G")
					      (stream *standard-output*))
  "Write the data declaration in agda"
  (let ((group-name (format nil "~A~D" prefix (length elements))))
    (format stream "data ~A : Set where~%" group-name)
    (format stream " ~{ ~A~} : ~A~%~%" elements group-name)))


