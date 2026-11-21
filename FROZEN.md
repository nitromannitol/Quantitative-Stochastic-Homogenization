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
| E1 | `QuantitativeStochasticHomogenization/Frozen/AveragedCorrectorGradient.lean` | `QSH.Frozen.averagedCorrectorGradient` | draft | `dfa9a663aef3678e8ac56dc64ddf4077f1f246fa7dfc8dbe3a3e141b098fba11` | AKM Theorem 4.1, (4.2); einstein input E1 |
| E2 | `QuantitativeStochasticHomogenization/Frozen/BlockBoundary.lean` | `QSH.Frozen.blockBoundary` | draft | `07cb3cb3cb449389d13bee767db4039e90cd420cd800a758965198b13fc69e5a` | AKM Lemma 5.29 (ii), (5.91)-(5.92); einstein input E2 |
| E3 | `QuantitativeStochasticHomogenization/Frozen/BlockChange.lean` | `QSH.Frozen.blockChange` | draft | `f6c9a87d9780b8e97c2a3846b830df9bb729d93e83e10b46aad17e1b6735c25d` | AKM Lemma 5.29 (iii); einstein input E3 |
| E4 | `QuantitativeStochasticHomogenization/Frozen/BlockCLT.lean` | `QSH.Frozen.blockCLT` | draft | `9b68b375fc207f830dcecaa101e1f1551ff879609427aa3ecd4854c65a133e3e` | AKM Lemma 5.29 (i), (5.90); einstein input E4 |
| E5 | `QuantitativeStochasticHomogenization/Frozen/CoarsenedCoefficientEstimates.lean` | `QSH.Frozen.coarsenedCoefficientEstimates` | draft | `1e639713ff130e40746f75578ab7475aaab5e01698408c7d848eac914720430b` | AKM Lemma 5.24, (5.63)-(5.64); einstein input E5 |
| E6 | `QuantitativeStochasticHomogenization/Frozen/LocalizedEnergy.lean` | `QSH.Frozen.localizedEnergy` | draft | `0e115524a724935971182f635b142a8761749a1806f47c61381d39e4283a5f96` | AKM (5.85), Theorem 4.6 (iv), Section 4.4; einstein input E6 |
| E7 | `QuantitativeStochasticHomogenization/Frozen/NegativeSobolevCorrector.lean` | `QSH.Frozen.negativeSobolevCorrector` | draft | `c44e747110e9234c0865539a143c530f6ea87dfc2455649ae42c1f43f7aa78ac` | AKM (4.126), Theorem 4.24; einstein input E7 |
<!-- FROZEN-LIST-END -->
