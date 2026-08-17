;;; snel-mode.el --- Major mode for the Snel language  -*- lexical-binding: t; -*-

;; Commentary:
;; Syntax highlighting, comments, and indentation for Snel (see SPEC.md).
;; Install:
;;   (add-to-list 'load-path "/path/to/snel/editors/emacs")
;;   (require 'snel-mode)
;; With eglot, `snel lsp` is registered below as the language server.

;;; Code:

(defvar snel-keywords
  '("let" "fun" "type" "mod" "pub" "use" "do" "end"
    "if" "then" "else" "try" "err" "is" "where")
  "Keywords of the Snel language.")

(defvar snel-constants
  '("nil" "inf" "nan" "true" "false")
  "Literal constants of the Snel language.")

(defvar snel-types
  '("bit" "i64" "f64" "u8" "str" "sym")
  "Built-in type names.")

(defvar snel-builtins
  '("add" "sub" "mul" "div" "rem" "neg" "abs" "itof" "ftoi" "sqrt" "floor"
    "ceil" "sign" "ord" "chr" "eq" "ne" "lt" "le" "gt" "ge" "and" "or" "not"
    "len" "cat" "iota" "grade" "sum" "prod" "min" "max" "isnil" "all" "any"
    "rev" "take" "drop" "first" "last" "which" "distinct" "in" "map" "map2"
    "fold" "scan" "filter" "group" "get" "select" "find" "split" "join"
    "locals" "reflect" "show" "encode" "decode" "parse" "unparse" "at" "rep"
    "scatter" "shift" "sums" "prods" "member" "matches" "runs" "partition"
    "windows" "tojson" "fromjson" "tocsv" "fromcsv")
  "Language-level builtin names (never shadowed).")

(defvar snel-font-lock-keywords
  (let ((kw (regexp-opt snel-keywords 'symbols))
        (co (regexp-opt snel-constants 'symbols))
        (ty (regexp-opt snel-types 'symbols))
        (bi (regexp-opt snel-builtins 'symbols)))
    `((,kw . font-lock-keyword-face)
      (,co . font-lock-constant-face)
      (,ty . font-lock-type-face)
      (,bi . font-lock-builtin-face)
      ;; declaration names: `fun f(`, `let x`, `type t`
      ("\\_<fun\\_>[ \t]+\\([a-zA-Z_][a-zA-Z0-9_]*\\)" 1 font-lock-function-name-face)
      ("\\_<\\(?:let\\|type\\|mod\\|use\\)\\_>[ \t]+\\([a-zA-Z_][a-zA-Z0-9_]*\\)"
       1 font-lock-variable-name-face)
      ;; :1011 bit vector, :name symbol
      (":[01][01_]*" . font-lock-constant-face)
      (":[a-zA-Z_][a-zA-Z0-9_]*" . font-lock-constant-face)
      ;; numbers: decimal / hex / binary, `_` separators allowed
      ("\\_<0[xX][0-9a-fA-F_]+\\_>" . font-lock-constant-face)
      ("\\_<0[bB][01_]+\\_>" . font-lock-constant-face)
      ("\\_<[0-9][0-9_]*\\(\\.[0-9][0-9_]*\\)?\\([eE][-+]?[0-9]+\\)?\\_>"
       . font-lock-constant-face)
      ("|>" . font-lock-keyword-face)))
  "Font-lock rules for `snel-mode'.")

(defvar snel-mode-syntax-table
  (let ((table (make-syntax-table)))
    ;; `--` to end of line is a comment; `-` is also an operator, so use the
    ;; two-character comment-start form.
    (modify-syntax-entry ?- ". 12" table)
    (modify-syntax-entry ?\n ">" table)
    (modify-syntax-entry ?\" "\"" table)
    (modify-syntax-entry ?\\ "\\" table)
    (modify-syntax-entry ?_ "_" table)
    table)
  "Syntax table for `snel-mode'.")

(defun snel-indent-line ()
  "Indent by bracket depth: two spaces per unclosed ( [ { above point."
  (interactive)
  (let ((depth 0))
    (save-excursion
      (goto-char (point-min))
      (let ((end (line-beginning-position
                  (1+ (- (line-number-at-pos) (line-number-at-pos (point-min)))))))
        (ignore end))
      (let ((stop (save-excursion (beginning-of-line) (point))))
        (while (< (point) stop)
          (let ((ch (char-after)))
            (cond ((memq ch '(?\( ?\[ ?{)) (setq depth (1+ depth)))
                  ((memq ch '(?\) ?\] ?})) (setq depth (max 0 (1- depth))))))
          (forward-char 1))))
    (save-excursion
      (beginning-of-line)
      ;; a line that starts with a closer dedents one level
      (when (looking-at "[ \t]*[])}]")
        (setq depth (max 0 (1- depth))))
      (indent-line-to (* 2 depth)))
    (when (looking-back "^[ \t]*" (line-beginning-position))
      (back-to-indentation))))

;;;###autoload
(define-derived-mode snel-mode prog-mode "Snel"
  "Major mode for editing Snel source."
  :syntax-table snel-mode-syntax-table
  (setq-local font-lock-defaults '(snel-font-lock-keywords))
  (setq-local comment-start "-- ")
  (setq-local comment-start-skip "--+[ \t]*")
  (setq-local comment-end "")
  (setq-local indent-line-function #'snel-indent-line)
  (setq-local indent-tabs-mode nil)
  (setq-local tab-width 2))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.sni?\\'" . snel-mode))

;; eglot: use the interpreter's own LSP mode
(with-eval-after-load 'eglot
  (add-to-list 'eglot-server-programs '(snel-mode . ("snel" "lsp"))))

(provide 'snel-mode)
;;; snel-mode.el ends here
