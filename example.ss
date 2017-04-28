(trace-passes (quote (flatten-set! push-if)))
(let ([path "result.ss"])
  (if (file-exists? path) (delete-file path))
  (with-output-to-file path
    (lambda ()
      (write (my-tiny-compile
              (quote
               (if (if (begin 1 2) (begin 3 4) (begin 5 6)) #f '())
               ))))))