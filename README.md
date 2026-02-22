<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# File Synchroniser

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/liyishuai/file-sync/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/liyishuai/file-sync/actions/workflows/docker-action.yml




Coq formalisation of the Unison file synchroniser

## Meta

- Author(s):
  - Yishuai Li
- License: [Mozilla Public License 2.0](LICENSE)
- Compatible Rocq/Coq versions: 8.14 or later
- Compatible OCaml versions: 4.12 or later
- Additional dependencies:
  - [SimpleIO](https://github.com/Lysxia/coq-simple-io)
  - [AsyncTest](https://github.com/liyishuai/coq-async-test)
  - [OCamlbuild](https://github.com/ocaml/ocamlbuild)
  - [Fileutils](https://github.com/gildor478/ocaml-fileutils)
  - [Unison](https://www.cis.upenn.edu/~bcpierce/unison/)
- Rocq/Coq namespace: `FileSync`
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of File Synchroniser
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install coq-file-sync
```

To instead build and install manually, you need to make sure that all the
libraries this development depends on are installed.  The easiest way to do that
is still to rely on opam:

``` shell
git clone https://github.com/liyishuai/file-sync.git
cd file-sync
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only .
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



