;;; timl.el --- Support for TiML files           -*- lexical-binding: t; -*-

;; Copyright (C) 2016  Clément Pit-Claudel

;; Author: Clément Pit-Claudel <clement.pitclaudel@live.com>
;; Keywords: languages
;; Package-Requires: ((sml-mode "27") (emacs "24.3"))
;; Version: 0.1

;;; Commentary:


;;; Code:

(require 'sml-mode)
(require 'flycheck)

;;; Constants

(defconst timl--this-file (or load-file-name
                          (bound-and-true-p byte-compile-current-file)
                          (buffer-file-name))
  "Full path of this script.")

(defconst timl--default-executable
  (expand-file-name "../impl/main.sh"
                    (file-name-directory timl--this-file)))

(defconst timl--stdlib
  (expand-file-name "../impl/examples/stdlib.pkg"
                    (file-name-directory timl--this-file)))

;;; Customizable settings

(defvar timl-prettify-symbols-alist '(("fn" . ?λ)
                                  ("/\\" . ?∧) ("\\/" . ?∨)
                                  ("->" . ?→) ("=>" . ?⇒)
                                  ("<=" . ?≤) (">=" . ?≥) ("<>" . ?≠) ("==" . ?≡)
                                  ("->>" . ?↠) ("-->" . ?⟶)
                                  ("Nat" . ?ℕ) ("Bool" . ?𝔹)
                                  ("forall" . ?∀) ("|>" . ?▹)
                                  ("'a" . ?α) ("'b" . ?β) ("'c" . ?γ)
                                  ("'d" . ?δ) ("'e" . ?ϵ) ("'v" . ?ν)))

(defvar timl-box-width -1)

;;; Font-locking and mode definition

(defun timl--setup-font-lock ()
  "Set font-lock–related settings for TiML."
  (setq prettify-symbols-alist timl-prettify-symbols-alist)
  (let ((timl-builtins '("BigO" "ceil" "floor" "b2n" "forall" "never" "log2" "log10"))
        (timl-keywords '("return" "using" "absidx")))
    (font-lock-add-keywords
     nil
     `(("\\_<'[a-z]\\_>" 0 '((:slant italic)))
       (,(concat "\\_<\\(absidx\\)\\s-+\\(" sml-id-re "\\)")
        (1 font-lock-keyword-face)
        (2 font-lock-function-name-face))
       ("\\(\\$(\\)\\(.*?\\)\\()\\)"
        (1 '((:weight bold)))
        (2 '((:slant italic)))
        (3 '((:weight bold))))
       ("\\([@]\\)\\w+\\>"
        (1 '((:weight bold))))
       ("\\([$]\\) *\\(\\(\\w\\|\\s_\\)+\\)\\>"
        (1 '((:weight bold)))
        (2 '((:slant italic))))
       ("\\({\\)\\(.*?\\)\\(}\\)"
        (1 '((:weight bold)))
        (3 '((:weight bold))))
       ("\\(\\[\\)\\(.*?\\)\\(\\]\\)"
        (1 '((:weight bold)))
        (3 '((:weight bold))))
       ("\\_<\\([A-Z][a-zA-Z']*\\)\\([.]\\|\\_>\\)" 1 font-lock-type-face)
       (,(regexp-opt timl-builtins 'symbols) 0 'font-lock-builtin-face)
       (,(regexp-opt timl-keywords 'symbols) 0 'font-lock-keyword-face)
       ("\\(--\\)\\( .+? \\)\\(-->\\)"
        (1 (ignore (compose-region (match-beginning 1) (match-end 1) ?–)))
        (2 `((:box (:line-width ,timl-box-width))) append)
        (3 (ignore (compose-region (match-beginning 3) (match-end 3) ?→)))))
     'append)))

(define-derived-mode timl-mode sml-mode "TiML"
  (timl--setup-font-lock)
  ;; (make-variable-buffer-local 'tooltip-functions)
  ;; (push #'timl--tooltip-help-tips tooltip-functions)
  (prettify-symbols-mode))

(add-to-list 'auto-mode-alist '("\\.timl\\'" . timl-mode))

;;; Flycheck

(defun timl--fontify-str (str &optional postproc)
  "Fontify STR as TiML code.
Run POSTPROC after fontifying if non-nil."
  (with-temp-buffer
    (delay-mode-hooks (timl-mode))
    (setq delayed-mode-hooks nil)
    (insert str)
    (if (fboundp 'font-lock-ensure)
        (font-lock-ensure)
      (with-no-warnings (font-lock-fontify-buffer)))
    (when postproc
      (funcall postproc))
    (buffer-string)))

(defun timl--fontify-message-postproc ()
  "Mark parts of error message MSG."
  (goto-char (point-min))
  (while (not (eobp))
    (unless (looking-at-p "  ")
      (remove-text-properties (point-at-bol) (point-at-eol) '(face nil font-lock-face nil)))
    (forward-line)))

(defun timl--error-filter (errors)
  "Fontify messages of ERRORS and adjust column number."
  (flycheck-sanitize-errors errors)
  (flycheck-increment-error-columns errors)
  (dolist (err errors)
    (let ((message (flycheck-error-message err)))
      (when message
        (setq message (replace-regexp-in-string "^  " "" message nil t))
        (setf (flycheck-error-message err)
              (timl--fontify-str message #'timl--fontify-message-postproc)))))
  errors)

(flycheck-def-executable-var timl timl--default-executable)

(flycheck-define-command-checker 'timl
  "A TiML checker."
  :command `(,timl--default-executable (eval timl--stdlib) source-inplace)
  :error-patterns
  '((error line-start "File " (file-name) ", line " line "-" (one-or-more digit)
           ", characters " column "-" (one-or-more digit) ":\n"
           (message (one-or-more "  " (zero-or-more not-newline) "\n"))))
  :error-filter #'timl--error-filter
  :modes '(timl-mode))

(add-to-list 'flycheck-checkers 'timl)

(provide 'timl)
;;; timl.el ends here
