Scheme-to-C
============

This is a tiny nanopass compiler for compiling a small subset of Scheme to C.
It was developed to be presented at Clojure Conj 2013, in Alexandria, VA.
It has been a little over a week and half since I started working on it and
I've added more documentation and more tests since Clojure Conj.

There is still much to be done.  More tests are needed and a few passes are
still not documented, and I still have not tested the boehm collector, though
I hope to do so soon.

Bartlett's Scheme-&gt;C
=====================
This should not be confused with Bartlett's Fabled Scheme-&gt;C compiler,
available at http://scheme2c.alioth.debian.org/, with a clone of the source
repository at https://github.com/barak/scheme2c/.  (Nod to @barak for pointing
this out!)

Required Libraries
===================
There are two required git repositories to run this compiler.  This repository
(of course), and the nanopass framework repository at
https://github.com/nanopass/nanopass-framework-scheme/.

You will also need one of the supported host compilers listed in the next
section.

Supported Host Compilers
=========================

The current version supports three host compilers: Chez Scheme, Ikarus, and
Vicare.  All three share similar features that are needed by the Nanopass
Framework in order to operate.

Getting Chez Scheme
--------------------
Chez Scheme is available at http://github.com/cisco/ChezScheme/ with
documentaton at http://cisco.github.io/ChezScheme/.

Running on Chez Scheme
-----------------------

In the `scheme-to-c` directory there is Makefile that can be used with the `make`
utility. Use `make init` to enter a new shell with the correct environment variable
set. Then type `scheme` to enter chez scheme REPL:

```scheme
$ make init
$ scheme
Chez Scheme Version 9.4.1
Copyright 1984-2016 Cisco Systems, Inc.

> (import (c))
> (my-tiny-compile '(+ 4 5))
9
```

You can run the tests as:

```scheme
$ make check
```

Getting Ikarus
---------------
Ikarus is no longer under active development, but it is easier to install on a
Mac OS X machine than Vicare, so I recommend it if you are on a Mac.  You can
find Ikarus at https://launchpad.net/ikarus and you can download it using bzr.
The easiest way to install it is to use the `c64` install script.  This installs
it into the `$HOME/.opt64` subdirectory and you can add `$HOME/.opt64/bin` to
the path to run `ikarus`.

Running on Ikarus
------------------
When running on `ikarus` you will also need to add the
`nanopass-framework-scheme` directory to the path in order to run the new
compiler.  This can be done with an environment variable, but I generally find
it easier to do this on the `ikarus` REPL as follows:

```scheme
$ ikarus
Ikarus Scheme version 0.0.4-rc1+, 64-bit (revision 1870, build 2013-10-16)
Copyright (c) 2006-2009 Abdulaziz Ghuloum

> (library-path (cons "../nanopass-framework-scheme" (library-path)))
> (import (c))
> (my-tiny-compiler '(+ 4 5))
9
```

You can also run the tests through `ikarus` as follows:

```scheme
$ ikarus
Ikarus Scheme version 0.0.4-rc1+, 64-bit (revision 1870, build 2013-10-16)
Copyright (c) 2006-2009 Abdulaziz Ghuloum

> (library-path (cons "../nanopass-framework-scheme" (library-path)))
> (import (tests))
> (run-tests)
running test 0:
0
passed
running test 1:
-5
passed
  .
  .
  .
```

Getting Vicare
---------------
Vicare Scheme is a fork of Ikarus that is currently under development.
You can find Vicare at http://marcomaggi.github.io/vicare.html.  This can
be installed using the standard GNU style configure script.  The only
features we require is posix support, since we need the `system` call to
shell out to run `gcc`.

Running on Vicare
------------------
Similar to Ikarus and Chez Scheme, Vicare also needs to be informed of where
to find the `nanopass-framework-scheme` directory.  Vicare also needs to be
told to look for additional Scheme file extensions, since I am using `.ss`
instead of the more recently introduced `.sls` for R6RS Scheme libraries.  Here
we can use the `--more-file-extensions` and two calls to the `--search-path`
command line flag, one to search in the `nanopass-framework-scheme` directory
and one in the current directory, `.`, which is otherwise not included.

```scheme
$ vicare --more-file-extensions \
--search-path ../nanopass-framework-scheme \
--search-path .
Vicare Scheme version 0.3d1, 64-bit
Revision no-branch/no-commit
Build 2013-10-15

Copyright (c) 2006-2010 Abdulaziz Ghuloum and contributors
Copyright (c) 2011-2013 Marco Maggi

vicare> (import (c))
vicare> (my-tiny-compile '(+ 4 5))
9
```

We can also run the tests under Vicare as:

```scheme
$ vicare --more-file-extensions \
--search-path ../nanopass-framework-scheme \
--search-path .
Vicare Scheme version 0.3d1, 64-bit
Revision no-branch/no-commit
Build 2013-10-15

Copyright (c) 2006-2010 Abdulaziz Ghuloum and contributors
Copyright (c) 2011-2013 Marco Maggi

vicare> (import (tests))
vicare> (run-tests)
running test 0:
0
passed
running test 1:
-5
passed
  .
  .
  .
```

More To Do
===========

- [x] start better documentation of code
- [x] add tests for the compiler
- [x] test on Chez, Ikarus, and Vicare
- [ ] test the Boehm garbage collector
- [ ] add more and larger tests
- [ ] improve the testing framework to allow for quieter output and errors
- [ ] add predicates for fixnum and procedure
- [ ] finish documentation of code
