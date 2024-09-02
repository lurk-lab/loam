# Loam

Research and development prototype of Loam.

## Installation

### sbcl

Code is in Common Lisp, developed and (to the extent it is) tested with SBCL.
```bash
> brew install sbcl
```

or
```bash
> apt-get install sbcl
```

### QuickLisp & ASDF

Install [QuickLisp](https://www.quicklisp.org):

- Download the file for installation. (https://beta.quicklisp.org/quicklisp.lisp)
- Then run sbcl with that file loaded by this command.

```sh
sbcl --load path/of/quicklisp.lisp
```

After sbcl launched, type in the command below.

```lisp
(quicklisp-quickstart:install)
```

Now Quicklisp has been installed. To ensure Quicklisp is loaded every time you start Lisp, type in the command below.

```lisp
(ql:add-to-init-file)
```

### Optional for Emacs Users
*NOTE:* If you intend to develop on or with Loam (as opposed to just use CLI or web interfaces), then use of Emacs +
Slime is strongly recommended.

Type in the command which will create a file you can load in Emacs to configure the right load-path for loading
Quicklisp's installation of SLIME.

```lisp
(ql:quickload "quicklisp-slime-helper")
```

Then configure Emacs to use Slime. Here is a simple but helpful configuration to place in you `.emacs` file:

```lisp
(use-package slime
  :init
  (global-set-key (kbd "C-c z") 'slime-repl)
  (load (expand-file-name "~/quicklisp/slime-helper.el"))
  (setq inferior-lisp-program "/usr/local/bin/sbcl")
  (add-to-list 'slime-contribs 'slime-repl))
```

Ensure the path to your sbcl installation is correct.

You may also need to first [install use-package](https://jwiegley.github.io/use-package/installation/) by carefully
following the linked instructions. This is strongly recommended.

### Integrate the project with quicklisp

QuickLisp needs to find the project, so add a symlink:

```bash
> cd ~/quicklisp/local-projects
> ln -s ~/<installdir>/loam/loam.asd orient.asd
```

### Tests

To run tests:
```
% make test
```
