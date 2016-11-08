==============================
 TimL-mode setup instructions
==============================

1. Set up MELPA by adding this to your ``.emacs`` then restarting Emacs::

     (require 'package)
     (add-to-list 'package-archives '("melpa" . "http://melpa.org/packages/") t)
     (package-initialize)

2. Install dependencies

   * ``M-x package-refresh-contents``
   * ``M-x package-install RET flycheck RET``
   * ``M-x package-install RET sml-mode RET``

3. Add the following to your ``.emacs``::

     (load "PATH-TO-TIML-REPO/emacs/timl")
     (add-to-list 'auto-mode-alist '("\\.timl\\'" . timl-mode))
