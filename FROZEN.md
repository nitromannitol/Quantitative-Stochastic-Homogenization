# Frozen statements

This file records the statements of the library that are frozen: statements that other formalizations
rely on and that are fixed before their proofs are written. At present these are the statements used by
the formalization of the Einstein relation in
[einstein-relation-lean](https://github.com/nitromannitol/einstein-relation-lean).

## Convention

- One frozen statement per file under
  [`QuantitativeStochasticHomogenization/Frozen/`](QuantitativeStochasticHomogenization/Frozen/), in the
  namespace `QSH.Frozen`. The statement is the declaration between the two marker lines

  ```lean
  -- FROZEN-STATEMENT-BEGIN
  theorem QSH.Frozen.example_statement ... :
      ... 
  -- FROZEN-STATEMENT-END
  ```

  and its docstring and the definitions it uses are written above the first marker. A proof, if there
  is one, follows the second marker.
- The hash is the SHA-256 of the UTF-8 bytes strictly between the two markers, with the newline that
  follows the first marker dropped and the newline before the second marker kept. The recipe is that of
  the other repositories of this owner.
- The state of a statement is `draft` (the proof after the second marker is a single `sorry`) or
  `proved`. No `axiom` is allowed.
- A statement changes only by editing its file and its row together, and the change is a decision
  of the owner.
- [`scripts/check_frozen.py`](scripts/check_frozen.py) checks the rows against the files, the hashes,
  the declaration names and the absence of forbidden tokens in the library; CI runs it. The list below
  may be empty.

## Frozen statements

Each row gives: an identifier, the file, the fully qualified declaration, the state, the SHA-256 of
the statement, and the numbered result of the book that it states or uses.

<!-- FROZEN-LIST-BEGIN -->
| id | file | declaration | state | sha256 | source |
| --- | --- | --- | --- | --- | --- |
<!-- FROZEN-LIST-END -->
