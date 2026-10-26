# Vendored OpenAI code
Source: https://github.com/openai/math, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a, directory lean/, Apache License 2.0 (copy in LICENSE-APACHE-2.0-OpenAI).
- OAI/Algebra/GroupRing/*.lean: the import closure of OAI.Algebra.GroupRing.Main (Result 196), copied verbatim (CylinderRetention.lean omitted, not in the closure).
- OAI/GroupTheory/Hyperbolic/Model.lean, ThinTriangles.lean: verbatim. DiscreteMetric.lean: verbatim except line 1 (import changed from ...Hyperbolic.Torsion to ...Hyperbolic.Model). GraphMetric.lean: an excerpt of CayleyMetric.lean, namely its lines 1-39 (the generic graph metric) followed by its closing `end OAI`; no line changed.
- OAI/Algebra/OddKaplansky/Cellular.lean: verbatim except line 1 (import Mathlib instead of ...OddKaplansky.Transfer).
The only source changes are the documented import adaptations, the documented GraphMetric excerpt, and a per-file provenance and modification notice (a comment after the import line) in each of the three modified files; any further change must be recorded here.
