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
   '("/[[:alpha:]][^][:space:][(){}<>,]*" . font-lock-string-face)
   '("[=!~*$]\\|[\\/][\\/]\\|%||%\\|%|\\||%\\|@\\(@\\|\\)"
     . font-lock-keyword-face)
   '("[≝⟨⟩⋊⋉⋀∧⋂∩⋁∨⋃∪∙¬∗↓]" . font-lock-keyword-face)
   '("\\<[[:alpha:]][^][:space:][(){}<>,]*" . font-lock-variable-name-face)
   '("#.*$" . font-lock-comment-face)
   )
  "Highlighting exppressions for plebby mode")

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.pleb\\(by\\|\\)\\'" . plebby-mode))

(defun plebby-mode ()
  "Major mode for editing Piecewise-Local Expression Builder files"
  (interactive)
  (kill-all-local-variables)
  (set (make-local-variable 'font-lock-defaults)
       '(plebby-mode-font-locks))
  (setq major-mode 'plebby-mode)
  (setq mode-name "plebby")
  (run-hooks 'plebby-mode-hook))

(provide 'plebby-mode)
