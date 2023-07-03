;;; polytt-mode --- Major mode for the polytt programming language -*- lexical-binding: t; -*-

;;; Commentary:

;; This is a major mode for the `polytt' programming language.
;; Make sure to set the variable `polytt-command' to the location
;; of the `polytt' binary.

;;; Code:

(require 'compile)

(defgroup polytt nil "polytt" :prefix 'polytt :group 'languages)

(defcustom polytt-command "polytt"
  "THe command used to run `polytt'."
  :group 'polytt
  :type 'string
  :tag "Command for `polytt'"
  :options '("polytt" "dune exec polytt"))

(defface polytt-command-keyword-face
  '((t (:inherit font-lock-preprocessor-face)))
  "Face for `polytt' command keywords."
  :group 'polytt)

(defface polytt-declaration-keyword-face
  '((t (:inherit font-lock-keyword-face)))
  "Face for `polytt' declaration keywords."
  :group 'polytt)

(defface polytt-declaration-symbol-face
  '((t (:inherit font-lock-keyword-face)))
  "Face for `polytt' declaration keywords."
  :group 'polytt)

(defface polytt-binder-symbol-face
  '((t (:inherit font-lock-constant-face)))
  "Face for `polytt' binders."
  :group 'polytt)

(defface polytt-expression-keyword-face
  '((t (:inherit font-lock-builtin-face)))
  "Face for `polytt' expression keywords."
  :group 'polytt)

(defface polytt-expression-symbol-face
  '((t (:inherit font-lock-builtin-face)))
  "Face for `polytt' expression symbols."
  :group 'polytt)

(defconst polytt-comment-regex
  (rx line-start (* space) "--" (* not-newline) line-end)
  "Regexp for comments.")

(defconst polytt-command-keywords
  '("#fail" "#normalize" "#print" "#quit")
  "Command keywords.")

(defconst polytt-declaration-keywords
  '("def" "import" "return" "done" "let" "let⁻")
  "Declaration keywords.")

(defconst polytt-declaration-symbols
  '(":=" ";" ":")
  "Declaration symbols.")

(defconst polytt-expression-keywords
  '("base" "fib" "fst" "snd")
  "Expression keywords.")

(defconst polytt-binder-symbols
  '("Π" "λ" "λ⁻")
  "Symbols for binders.")

(defconst polytt-expression-symbols
  '("→" "←" "×" "⇝" "⇜" "∘" "⇒")
  "Expression symbols.")

(defconst polytt-mode-font-lock-keywords
  `(
    ;; Comments
    (,polytt-comment-regex 0 'font-lock-comment-face)

    ;; Top-level statements
    (,(regexp-opt polytt-command-keywords 'nil) 0 'polytt-command-keyword-face)
    (,(regexp-opt polytt-declaration-keywords 'words) 0 'polytt-declaration-keyword-face)
    (,(regexp-opt polytt-declaration-symbols 'nil) 0 'polytt-declaration-symbol-face)

    ;; Expressions
    (,(regexp-opt polytt-expression-keywords 'words) 0 'polytt-expression-keyword-face)
    (,(regexp-opt polytt-binder-symbols 'nil) 0 'polytt-binder-symbol-face)
    (,(regexp-opt polytt-expression-symbols 'nil) 0 'polytt-expression-symbol-face)
    )
  )


(defconst polytt--compilation-buffer-name
  "*polytt*"
  "The name to use for `polytt' compilation buffers.")

(define-compilation-mode polytt-compilation-mode "polytt"
  "`polytt' specific `compilation-mode' derivative.")

(defun polytt--compilation-buffer-name-function (_mode)
  "Compute a buffer name for the `polytt-mode' compilation buffer."
  polytt--compilation-buffer-name)

(defun polytt-compile-buffer ()
  "Load the current file into `polytt'."
  (interactive)
  (let ((filename (buffer-file-name)))
    (if filename
	(progn
	  (when (buffer-modified-p) (save-buffer))
	  (let* ((command (concat polytt-command " " (file-name-nondirectory filename)))
		 ;; Dynamically bind some configuration for `compilation-start'.
		 (compilation-buffer-name-function
		  'polytt--compilation-buffer-name-function)
		 (default-directory (file-name-directory filename)))
	    (compilation-start command 'polytt-compilation-mode nil t)))
	(error "Buffer has no file name"))))

(define-derived-mode polytt-mode prog-mode "polytt"
  "Major mode for editting `polytt' programs.
\\{polytt-mode-map}"
  (set (make-local-variable 'comment-start) "-- ")
  (setq font-lock-defaults '((polytt-mode-font-lock-keywords) nil nil))

  (define-key polytt-mode-map (kbd "C-c C-l") 'polytt-compile-buffer))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.poly\\'" . polytt-mode))

(provide 'polytt-mode)
;;; polytt-mode.el ends here
