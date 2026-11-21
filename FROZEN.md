# Frozen statements

This file records the statements of the library that are frozen: statements that other formalizations
rely on and that are fixed before their proofs are written. At present these are the statements used by
the formalization of the Einstein relation in
[einstein-relation-lean](https://github.com/nitromannitol/einstein-relation-lean).

## Convention

- One frozen statement per file under
  [`QuantitativeStochasticHomogenization/Frozen/`](QuantitativeStochasticHomogenization/Frozen/), in the
  namespace `QSH.Frozen`. The statement is the proposition defined between the two marker lines

  ```lean
  -- FROZEN-STATEMENT-BEGIN
  def QSH.Frozen.example_statement : Prop :=
    ...
  -- FROZEN-STATEMENT-END
  ```

  and its docstring is written above the first marker. The definitions it uses are those of the
  section modules of the library; the ones that determine its meaning are listed, with their hashes,
  in the vocabulary table below. A proof, when there is one, is a theorem whose type is the
  proposition, written after the second marker.
- The hash is the SHA-256 of the UTF-8 bytes strictly between the two markers, with the newline that
  follows the first marker dropped and the newline before the second marker kept. The recipe is that of
  the other repositories of this owner.
- The state of a statement is `draft` or `proved`. A `draft` statement has no proof in the library
  yet: after the second marker there is nothing, or a proof attempt containing exactly one `sorry`. A
  `proved` statement has, after the second marker, a theorem whose type is the proposition, and its
  file contains no `sorry`. No `axiom` is allowed.
- A statement changes only by editing its file and its row together, and the change is a decision
  of the owner.
- The same holds for the definitions in the vocabulary table: a change to one of them changes the
  meaning of every statement that uses it. It is made together with the row, it is a decision of the
  owner, and the statements listed in the row are reviewed again before their hashes are recorded.
- [`scripts/check_frozen.py`](scripts/check_frozen.py) checks the rows against the files, the hashes of
  the statements and of the vocabulary, the declaration names and the absence of forbidden tokens in
  the library; CI runs it. The lists below may be empty.

## Frozen statements

Each row gives: an identifier, the file, the fully qualified declaration, the state, the SHA-256 of
the statement, and the numbered result of the book that it states or uses.

<!-- FROZEN-LIST-BEGIN -->
| id | file | declaration | state | sha256 | source |
| --- | --- | --- | --- | --- | --- |
| E1 | `QuantitativeStochasticHomogenization/Frozen/AveragedCorrectorGradient.lean` | `QSH.Frozen.averagedCorrectorGradient` | draft | `dfa9a663aef3678e8ac56dc64ddf4077f1f246fa7dfc8dbe3a3e141b098fba11` | AKM Theorem 4.1, (4.2) |
| E2 | `QuantitativeStochasticHomogenization/Frozen/BlockBoundary.lean` | `QSH.Frozen.blockBoundary` | draft | `07cb3cb3cb449389d13bee767db4039e90cd420cd800a758965198b13fc69e5a` | AKM Lemma 5.29 (ii), (5.91)-(5.92) |
| E3 | `QuantitativeStochasticHomogenization/Frozen/BlockChange.lean` | `QSH.Frozen.blockChange` | draft | `f6c9a87d9780b8e97c2a3846b830df9bb729d93e83e10b46aad17e1b6735c25d` | AKM Lemma 5.29 (iii) |
| E4 | `QuantitativeStochasticHomogenization/Frozen/BlockCLT.lean` | `QSH.Frozen.blockCLT` | draft | `9b68b375fc207f830dcecaa101e1f1551ff879609427aa3ecd4854c65a133e3e` | AKM Lemma 5.29 (i), (5.90) |
| E5 | `QuantitativeStochasticHomogenization/Frozen/CoarsenedCoefficientEstimates.lean` | `QSH.Frozen.coarsenedCoefficientEstimates` | draft | `24884a3b7fced117b752797d6c9e6a04a8ea08456f242e97fbe696cdbf5e2284` | AKM Lemma 5.24, (5.63)-(5.64) |
| E6 | `QuantitativeStochasticHomogenization/Frozen/LocalizedEnergy.lean` | `QSH.Frozen.localizedEnergy` | draft | `0e115524a724935971182f635b142a8761749a1806f47c61381d39e4283a5f96` | AKM (5.85), Theorem 4.6 (iv), Section 4.4 |
| E7 | `QuantitativeStochasticHomogenization/Frozen/NegativeSobolevCorrector.lean` | `QSH.Frozen.negativeSobolevCorrector` | draft | `c44e747110e9234c0865539a143c530f6ea87dfc2455649ae42c1f43f7aa78ac` | AKM (4.126), Theorem 4.24 |
<!-- FROZEN-LIST-END -->

## Vocabulary

Each row gives a definition of the library used by a frozen statement: the file, the name as
written after its keyword, the SHA-256 of its text, and the frozen statements that use it. The
text runs from the line of the keyword up to the next line that begins in the first column, with
trailing blank lines dropped; the docstring and the attributes are not hashed. The rows list every
definition, structure and instance of the library reached from a frozen statement through the
types and values of definitions (proofs are not followed).

<!-- FROZEN-VOCABULARY-BEGIN -->
| file | name | sha256 | used by |
| --- | --- | --- | --- |
| `QuantitativeStochasticHomogenization/AppA/OsNotation.lean` | `OsBound` | `2bba284d9f8a796a4c0271e3a32ee7cac722a14075faf3fcc70468836dacb854` | E1, E2, E3, E4, E7 |
| `QuantitativeStochasticHomogenization/AppA/OsNotation.lean` | `AEOsBound` | `219e94083501809610bbccd1b793ca6964634687267e066693f6de1591c808dc` | E2, E3, E4, E5, E6 |
| `QuantitativeStochasticHomogenization/Ch01/Sec02SubadditiveQuantity.lean` | `H01` | `7f1428c72da5d378c782addc038836df48608cb9a2cb8a333df55f30770ad5c5` | E1, E5, E7 |
| `QuantitativeStochasticHomogenization/Ch01/Sec02SubadditiveQuantity.lean` | `dirichletEnergy` | `115e07d532f9e0c7bc366a9138a06fa6d6a5c5f1aa6c89f506eb34169abc0fa8` | E1, E5, E7 |
| `QuantitativeStochasticHomogenization/Ch03/Sec03HigherOrderRegularityAndLiouville.lean` | `HarmonicA1` | `6bd0e960b2e45e71614c301c7564ccf1fb17acc180a8a1a17f00b782bfdcf638` | E2, E3, E4, E5, E6 |
| `QuantitativeStochasticHomogenization/Ch03/Sec04FirstOrderCorrectors.lean` | `Corrector` | `272d5a669f23aca8b29665089ed77cf1689756264f90803e11edeeb7dd94e6c3` | E1, E5, E7 |
| `QuantitativeStochasticHomogenization/Ch03/Sec04FirstOrderCorrectors.lean` | `HomogenizationData` | `df229927176eedec14c602322e8c929a464bae627e11a36dd2453f80ab8bc19e` | E1, E5, E7 |
| `QuantitativeStochasticHomogenization/Ch04/Opening.lean` | `euclideanHeatKernel` | `6c313e0ac51206cb7e443541f37c3299b11bd6013c93a5c36e7ddbdaee14fe21` | E1, E2, E3, E4, E5, E6 |
| `QuantitativeStochasticHomogenization/Ch04/Opening.lean` | `heatKernel` | `22461f8cd1e35d7cd2bbdb9c5dbe8096a6ee3969a08099d45cf06a9b510ab9e5` | E1, E2, E3, E4, E5, E6 |
| `QuantitativeStochasticHomogenization/Ch04/Sec01EnergyQuantityJ1.lean` | `J1` | `bbd9c8c82f0c7280e68627260a29f8e2b4eccf021fd68a6d932e8bfed50f72dd` | E2, E3, E4, E5, E6 |
| `QuantitativeStochasticHomogenization/Ch04/Sec01EnergyQuantityJ1.lean` | `J1Heat` | `4190f52117da4ea273f4c526613b87d36b71f4f37895c264ee07de4bb28f2a56` | E2, E3, E4, E5, E6 |
| `QuantitativeStochasticHomogenization/Ch04/Sec04LocalizationEstimates.lean` | `localizationEpsilon` | `cf635dba19e3934e6904c89fc09a54b0cdf86b6fd154b99d05071c9965604164` | E2, E3, E4, E6 |
| `QuantitativeStochasticHomogenization/Ch04/Sec04LocalizationEstimates.lean` | `localizationOuterRadius` | `11e3e7122e7e3175d31eb1fead067d77a4aefa720615fcfb1c7ede70bcba143a` | E2, E3, E4, E6 |
| `QuantitativeStochasticHomogenization/Ch04/Sec04LocalizationEstimates.lean` | `localizationIntermediateRadius` | `5637c05815ecacee2d87a7af87808a59db0fdd820aa55f0d248bb47ca478137c` | E2, E3, E4, E6 |
| `QuantitativeStochasticHomogenization/Ch04/Sec04LocalizationEstimates.lean` | `LocalHarmonic` | `c2269d896dd0356549cc8075015a7a448bea4f96948b2a2a4c05ca98f9da3f42` | E2, E3, E4, E6 |
| `QuantitativeStochasticHomogenization/Ch04/Sec04LocalizationEstimates.lean` | `IsLocalizationAdmissible` | `a5ca12bd21a04349f791f459550431cb0793ef9193036dfdd98795b94671401a` | E2, E3, E4, E6 |
| `QuantitativeStochasticHomogenization/Ch04/Sec04LocalizationEstimates.lean` | `localizationObjective` | `37ee616fbc0c68aa36f5412244986f7575ee3d1504606992d55dee8549b46194` | E2, E3, E4, E6 |
| `QuantitativeStochasticHomogenization/Ch04/Sec04LocalizationEstimates.lean` | `IsCoordinateMinimizer` | `5b81764aaecae03d4e09ce1cbf24cbf236e5bfd3d4e4922b04dc1446223d351f` | E2, E3, E4, E6 |
| `QuantitativeStochasticHomogenization/Ch04/Sec04LocalizationEstimates.lean` | `IsLeastNormCoordinateMinimizer` | `bddeacf4482efe50fefba1ee882356faefe34072bcd02363e448f7e5e6d9284a` | E2, E3, E4, E6 |
| `QuantitativeStochasticHomogenization/Ch04/Sec04LocalizationEstimates.lean` | `LocalizedBasis` | `b4032b1a87497767e82a8d9dcb3bf77c76ccdc5d943dce44ecdc15795b78e3f9` | E2, E3, E4, E6 |
| `QuantitativeStochasticHomogenization/Ch04/Sec04LocalizationEstimates.lean` | `localizedGradient` | `47ce7a9032b6e068929d7599557aa782d0a532099fea4fed61696028163e92ff` | E2, E3, E4, E6 |
| `QuantitativeStochasticHomogenization/Ch04/Sec04LocalizationEstimates.lean` | `localizedJ1` | `c6089ecaf05b76018e266aeeefba6ef334abb0cbf1f3c0ce6e990bb2a8cde286` | E2, E3, E4, E6 |
| `QuantitativeStochasticHomogenization/Ch05/Sec03HeuristicScalingLimit.lean` | `coarsenedCoefficient` | `2e7160a703dc9c2ffa740c7465ca27c7d792a56359a0cfd69c53062b11342bdc` | E5 |
| `QuantitativeStochasticHomogenization/Ch05/Sec03HeuristicScalingLimit.lean` | `matrixSize` | `849592b2a703a5b9e881a2ca33abcc1a70c6015afac462e4bf27174da4a70cfe` | E5 |
| `QuantitativeStochasticHomogenization/Ch05/Sec03HeuristicScalingLimit.lean` | `coarseFluxDefect` | `a1d34bc47eb108e0bdba0d8f5356cda03be38e3018222d6ddd35b91c44f67597` | E5 |
| `QuantitativeStochasticHomogenization/Ch05/Sec04CentralLimitTheoremForJ1.lean` | `LocalizationConstants` | `04a36f00ae441f5d880dbd6a4ea7a9e19d2deea171bf8568a2e397488756b207` | E2, E3, E4, E6 |
| `QuantitativeStochasticHomogenization/Ch05/Sec04CentralLimitTheoremForJ1.lean` | `LocalizedFamily` | `25e7493439372ed55441806e94633431fd4fb6bb0db287b9ab1955a4ed248f62` | E2, E3, E4, E6 |
| `QuantitativeStochasticHomogenization/Ch05/Sec04CentralLimitTheoremForJ1.lean` | `IsLocalization` | `21e8d52526b0b73e0fcb7f6dc05ce2b290fd8f63081c28d60bfb1d6005db6cba` | E2, E3, E4, E6 |
| `QuantitativeStochasticHomogenization/Ch05/Sec04CentralLimitTheoremForJ1.lean` | `BlockWindow` | `17891728107d82f48255926ba5c35d9d67f47713d073455002756998fdbc1a0e` | E2, E3, E4 |
| `QuantitativeStochasticHomogenization/Ch05/Sec04CentralLimitTheoremForJ1.lean` | `familyJ1` | `d66ca7ed1903e87387b9c4113ad2d63cba50860a8ae52ebb1166d26345fa2b6e` | E2, E3, E4 |
| `QuantitativeStochasticHomogenization/Ch05/Sec04CentralLimitTheoremForJ1.lean` | `centeredBlock` | `c7743d418cb928223c5147b882e7a619f330c12fc8df25b1f11b2df3f636faf7` | E2, E3, E4 |
| `QuantitativeStochasticHomogenization/Front/Assumptions.lean` | `SmoothCompactTest` | `79e738f581c92adf57a5cf0c2013d6060d9363fdec501ea4336f2360901fb4d9` | E1, E2, E3, E4, E5, E6, E7 |
| `QuantitativeStochasticHomogenization/Front/Assumptions.lean` | `CoefficientField` | `aa28e246662483df7fc5152f66175c4c7928ecc11ac17b2caaa210da0e10125b` | E1, E2, E3, E4, E5, E6, E7 |
| `QuantitativeStochasticHomogenization/Front/Assumptions.lean` | `testIntegral` | `94728d9759b05d260c91014a5dd2eec7a33600021bfd89fa9584ecd3693c8d5c` | E1, E2, E3, E4, E5, E6, E7 |
| `QuantitativeStochasticHomogenization/Front/Assumptions.lean` | `instMeasurableSpaceCoefficientField` | `b42f2732248bf28afab6a3f0657c0b92cb17d5bdf08243bf3c25bd402b071c35` | E1, E2, E3, E4, E5, E6, E7 |
| `QuantitativeStochasticHomogenization/Front/Assumptions.lean` | `localSigma` | `26a76811981cc34b4e41f47635cbe919c3465feebc47d7be7ac7030f1645fc27` | E1, E2, E3, E4, E5, E6, E7 |
| `QuantitativeStochasticHomogenization/Front/Assumptions.lean` | `translate` | `a8231cde99d50ca402539a4fb94c4061e72de13a31669aa74b6b53e3db0925d6` | E1, E2, E3, E4, E5, E6, E7 |
| `QuantitativeStochasticHomogenization/Front/Assumptions.lean` | `LawHypotheses` | `a8eb086f9f33fde96bf15e510d18eff45ca9f52ef0322a819197d98742a0b074` | E1, E2, E3, E4, E5, E6, E7 |
| `QuantitativeStochasticHomogenization/Front/Notation.lean` | `Vec` | `912d4405f638aeaac63dcfade063a404d81e864e7d58ade6c9b288ccd6a37b09` | E1, E2, E3, E4, E5, E6, E7 |
| `QuantitativeStochasticHomogenization/Front/Notation.lean` | `Mat` | `37dff13dfa0d13edb5952a479db5b68d259ce1e23de9714a177046f946e0f1bc` | E1, E2, E3, E4, E5, E6, E7 |
| `QuantitativeStochasticHomogenization/Front/Notation.lean` | `dot` | `96ca5d19f23eddf061aad5d27c02ffb834e573b8c99509481475ed79fc0b217b` | E1, E2, E3, E4, E5, E6, E7 |
| `QuantitativeStochasticHomogenization/Front/Notation.lean` | `euclideanSq` | `bd851ff15f381b06e47f3b17400bfba84baa99054aa4206f640f12651f34221a` | E1, E2, E3, E4, E5, E6, E7 |
| `QuantitativeStochasticHomogenization/Front/Notation.lean` | `euclideanNorm` | `e7208d6dd653ca17665c875f76a644f6afa20a2ce8aacebd9620106919690a6c` | E1, E2, E3, E4, E5, E6, E7 |
| `QuantitativeStochasticHomogenization/Front/Notation.lean` | `unitVector` | `73f611a9a8913a514bc2986538f37a0ec7052f60b6d4e05d2a9c07b4413356e8` | E1, E2, E3, E4, E5, E6, E7 |
| `QuantitativeStochasticHomogenization/Front/Notation.lean` | `ball` | `591d7f3138c44ca74465a784aacaf95b94e9e454937855d67ee7dce71af35bed` | E1, E2, E3, E4, E5, E6, E7 |
| `QuantitativeStochasticHomogenization/Front/Notation.lean` | `originBall` | `f50f70bf612b40b7490dc17b4f11a03235790f19ddca8ea2ec32d60a744b3660` | E7 |
| `QuantitativeStochasticHomogenization/Front/Notation.lean` | `LatticeIndex` | `76e4219b21706f1dff410f862e61fdb930467cd23c9887538039a8e63655d3df` | E1, E2, E3, E4, E5, E6, E7 |
| `QuantitativeStochasticHomogenization/Front/Notation.lean` | `latticeShift` | `95e777d62748187e5c8cd33c2a8518649270821cdce9cd115239e56cd6c84ab7` | E1, E2, E3, E4, E5, E6, E7 |
| `QuantitativeStochasticHomogenization/Front/Notation.lean` | `triadicCube` | `253c17632c01c25f3521c1438dc7d1ccca5b847c1563083d79a9fc7422b5a0d3` | E1, E5, E7 |
| `QuantitativeStochasticHomogenization/Front/Notation.lean` | `cube` | `a017faaa508cd1dd18fd6eb4e85787abc6f19732899736ee2a2802159d43daba` | E2, E3, E4 |
| `QuantitativeStochasticHomogenization/Front/Notation.lean` | `coordinateDerivative` | `ce655390fa9669e7fb445c2fc4906606fdf431934ce3c7c3474a4d12e0f035f4` | E1, E2, E3, E4, E5, E6, E7 |
| `QuantitativeStochasticHomogenization/Front/Notation.lean` | `gradient` | `c39a7611cb4ec55f19b802aeb4774d93d7c0325da9d152156ffa75077d183122` | E1, E2, E3, E4, E5, E6, E7 |
| `QuantitativeStochasticHomogenization/Front/Notation.lean` | `IsSpatialTest` | `13df937a3b17529a5c30c52516de34f730781ed220091b74092e6aa1457c0729` | E1, E2, E3, E4, E5, E6, E7 |
| `QuantitativeStochasticHomogenization/Front/Notation.lean` | `HasWeakPartialDerivative` | `1b4d37784caefc02c99b8c26434bf8f6f1c2263b2cbe3b65a293b2dc26d0ddc7` | E1, E2, E3, E4, E5, E6, E7 |
| `QuantitativeStochasticHomogenization/Front/Notation.lean` | `HasWeakGradient` | `5037422466eeee8b4af0cde497d2241095bd7d9152ce6b4d269cfd138e6054d1` | E1, E2, E3, E4, E5, E6, E7 |
| `QuantitativeStochasticHomogenization/Front/Notation.lean` | `HasWeakDivergence` | `c87bc0d1c94f17060394d390e35397ca0400a405d2d671730c4e5e76261f7669` | E1, E2, E3, E4, E5, E6, E7 |
| `QuantitativeStochasticHomogenization/Front/Notation.lean` | `scalarRms` | `bdbcd18ebc9a0209dc5ac2d11ff3d4939e94f102178f293e1ed44121ceed9076` | E7 |
| `QuantitativeStochasticHomogenization/Front/Notation.lean` | `vectorRms` | `8516b5d8039031184af992d644aa1b7983fab140e921bb851d0e089a9f10a6e6` | E2, E3, E4, E6 |
| `QuantitativeStochasticHomogenization/Front/Notation.lean` | `multiIndexDerivative` | `30deb9fb2d9c55e1e088e2380689ca4194467ec73b3d465c741b733c30cd8d3b` | E7 |
| `QuantitativeStochasticHomogenization/Front/Notation.lean` | `integerSobolevTestNorm` | `fe89e7cbf5b1e586ce9f69c20f27648383329d93517506882a943a7cdfeb5c9b` | E7 |
| `QuantitativeStochasticHomogenization/Front/Notation.lean` | `negativeIntegerSobolevNorm` | `f978b0f1e5257e514b99c062b923f751de3e31afb4ffaab8f4c02fe7f920533b` | E7 |
| `QuantitativeStochasticHomogenization/Front/Notation.lean` | `vectorNegativeIntegerSobolevNorm` | `f474f9e7779560072d057ed5806f3489d8b61f61800b06a793957bb75fa67d2e` | E7 |
<!-- FROZEN-VOCABULARY-END -->
