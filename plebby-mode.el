;;; plebby-mode.el -- Emacs plebby mode

(require 'font-lock)

;; add a hook, in case people want to use it
(defvar plebby-mode-hook nil)

;; font-lock for highlighting
(defconst plebby-mode-font-locks
  (list
   '("^#.*$" . font-lock-comment-face)
   '("[[:space:]]#.*$" . font-lock-comment-face)
   '("^:\\w*" . font-lock-preprocessor-face)
   '("/[[:alpha:]][^][:space:]\n[(){}<>⟨⟩,|]*" . font-lock-string-face)
   '("[=!~*$]\\|[\\/][\\/]\\|%||%\\|%|\\||%\\|@\\(@\\|\\)"
     . font-lock-keyword-face)
   '("[≝⟨⟩⋊⋉⋀∧⋂∩⋁∨⋃∪∙¬∗↓↑+⧢]" . font-lock-keyword-face)
   '("\\<[[:alpha:]][^][:space:]\n[(){}<>⟨⟩,|]*"
     . font-lock-variable-name-face)
   '("#.*$" . font-lock-comment-face)
   )
  "Highlighting exppressions for plebby mode")

(defvar plebby-mode-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map prog-mode-map)
    (define-key map "\C-ci" (lambda () (interactive) (insert-char ?⋀)))
    (define-key map "\C-ck" (lambda () (interactive) (insert-char ?⇑)))
    (define-key map "\C-cn" (lambda () (interactive) (insert-char ?¬)))
    (define-key map "\C-cr" (lambda () (interactive) (insert-char ?⇄)))
    (define-key map "\C-cu" (lambda () (interactive) (insert-char ?⋁)))
    (define-key map "\C-cv" (lambda () (interactive) (insert-char ?↓)))
    (define-key map "\C-cw" (lambda () (interactive) (insert-char ?⧢)))
    (define-key map "\C-c^" (lambda () (interactive) (insert-char ?↑)))
    (define-key map "\C-c[" (lambda () (interactive) (insert-char ?⋊)))
    (define-key map "\C-c]" (lambda () (interactive) (insert-char ?⋉)))
    (define-key map "\C-c<" (lambda () (interactive) (insert-char ?⟨)))
    (define-key map "\C-c>" (lambda () (interactive) (insert-char ?⟩)))
    (define-key map "\C-c~" (lambda () (interactive) (insert-char ?¬)))
    map)
  "Keymap for plebby mode")

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.pleb\\(by\\|\\)\\'" . plebby-mode))

(defun plebby-mode ()
  "Major mode for editing Piecewise-Local Expression Builder files"
  (interactive)
  (kill-all-local-variables)
  (use-local-map plebby-mode-map)
  (set (make-local-variable 'font-lock-defaults)
       '(plebby-mode-font-locks))
  (setq major-mode 'plebby-mode)
  (setq mode-name "plebby")
  (set (make-local-variable 'require-final-newline)
       mode-require-final-newline)
  (run-hooks 'plebby-mode-hook))

(provide 'plebby-mode)
