### smt-conv

Converts an smt file to a horn clause (hopefully) accepted by z3 by
piping it through eldarica and working around some bugs in z3.

#### installation

* install [stack](http://docs.haskellstack.org/en/stable/README.html)
* `stack build`
* `stack install`

#### usage

```
smt-conv -i /path/to/smt/to/convert -o /path/to/converted/smt
