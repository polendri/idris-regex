# idris-regexp

Verified regular expressions in Idris 2. The implementation is based on
https://www.ccs.neu.edu/home/turon/re-deriv.pdf

The `RegExp` module contains the generic regular expression implementation. `RegExp.String` contains
utilities for building regular expressions for `String`s.

Example:

```idris
> idris2 --repl RegExp.ipkg
> matches (plus alpha .+. star digit) "asdf123"
Yes ...
> matches (plus alpha .+. star digit) "123"
No ...
```
