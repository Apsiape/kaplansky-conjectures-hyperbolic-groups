# Source manifest

The external sources read for the paper, with SHA-256 hashes of the files read. OpenAI's PDFs are not
redistributed here; fetch them from the URLs below and compare hashes.

## OpenAI's mathematics release (github.com/openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a)

| Key in paper | Title | Path | SHA-256 of the PDF read |
|---|---|---|---|
| [OAI-196] | A torsion-free group algebra with zero divisors (23 Sep 2026) | `preprints/A-Torsion-Free-Group-Algebra-with-Zero-Divisors-September-23-2026/paper.pdf` | `b9788d4579b317fa2487796338fe3413322e105950880ec5a42bc85188a36bc6` |
| [OAI-197a] | A torsion-free group algebra that is not directly finite (4 Oct 2026) | `preprints/A-Torsion-Free-Group-Algebra-That-Is-Not-Directly-Finite-October-4-2026/direct-finiteness.pdf` | `7950476863f21811aaccb99ab12f24f81741e5077ca290394d029063024aaee8` |
| [OAI-197b] | A counterexample to Kaplansky's direct-finiteness conjecture in characteristic two (23 Sep 2026) | `preprints/A-Counterexample-to-Kaplanskys-Direct-Finiteness-Conjecture-in-Characteristic-Two-September-23-2026/paper.pdf` | `a97d7915d43b5112b11b7ae39619cf3a7b9c40f207f8f586fc28f22ff4406d12` |
| [OAI-197d] | A counterexample to Kaplansky's direct-finiteness conjecture in odd characteristic (26 Sep 2026) | `preprints/A-Counterexample-to-Kaplanskys-Direct-Finiteness-Conjecture-in-Odd-Characteristic-September-26-2026/paper.pdf` | `dc312586744d8d1b4fe49672ee36323fd56328f7ff3b9d8a481ddfb12b6965fe` |
| [OAI-207] | The Bass trace conjecture and the characteristic-zero Kaplansky idempotent conjecture (24 Sep 2026) | `preprints/The-Bass-trace-conjecture-for-complex-group-rings-September-24-2026/The-Bass-trace-conjecture-for-complex-group-rings-September-24-2026.pdf` | `1c4d90b5ed4de2ef66b4b07b3d5c3e2bfe8822a538177c64ee1d3c3e091120bf` |
| [OAI-252] | A torsion-free hyperbolic group that is not residually finite (23 Sep 2026) | `preprints/a-torsion-free-hyperbolic-group-that-is-not-residually-finite-September-23-2026/paper.pdf` | `8c67817e29f63b66daf5697bb4bab7913ee7d65c5f656e6be54a6a2e856705f9` |
| [OAI-257] | A hyperbolic group with no geometric CAT(0) action (25 Sep 2026) | `preprints/A-hyperbolic-group-with-no-geometric-CAT0-action-September-25-2026/paper.pdf` | `124f55b0821cc7f18c1b64600b5e5157d939bbc4a6f66294dc1456fc633eb264` |
| [OAI-285] | A torsion-free counterexample to the Kadison-Kaplansky projection conjecture (23 Sep 2026); hash of the PDF at origin/main | `preprints/A-Torsion-Free-Counterexample-to-the-Kadison-Kaplansky-Projection-Conjecture-September-23-2026/paper.pdf` | `df6227b61598580506210a8236216e043d1acd4ba062a9901b3063559ff62a5a` |
| [OAI-Tr] | Summarized chain of thought (Kaplansky direct finiteness in characteristic two) | `reasoning_traces/kaplansky-direct-finiteness-characteristic-two.pdf` | `b10deeca5a022bec37a177da8b5ab9205814c6cdbd1d45ae93553dbc1fa83a24` |
| [OAI-Lean] | Lean development (read for version 1.0.1, not rebuilt then; the modules used are built as part of [Mgh26] since version 1.0.2). Scope documents `lean/docs/196.md`, `lean/docs/197.md`; declarations listed in `DEPENDENCIES.md`. The files used are unchanged at `1581d4cbdd69a0faf34b2089614fe2a814316a6a` (12 Oct 2026). Lean v4.34.1, Mathlib `d13f23b`. Comparator tool: https://github.com/leanprover/comparator | `lean/` | `5edd7a5890540622fdfa39349e8520d66e5edf7ebf2af1685b23125264008667` (196.md), `c9bd633a2d69dc39581a08db24f2a5ceac6d6395c47c938fc9f0f59b60fdca46` (197.md) |

Pinpoint citations to these papers (section, lemma and equation numbers) were checked against the PDFs above.
The numbering of [OAI-197b] in its PDF differs from its source files: the cellular-automaton section is
Section 7 (Proposition 7.2). The idempotent corollary of [OAI-207] is Corollary 1.2(ii) in its PDF.

## Other sources opened for specific statements

| Key | Source | Read from | SHA-256 |
|---|---|---|---|
| [Iva26] | S. V. Ivanov, Zero divisors in group algebras of torsion-free groups in odd characteristic, arXiv:2610.17662v1 (dated 7 Oct, posted 13 Oct 2026). Theorem 1.1, Corollary 1.2, Lemma 2.2, Constructions 3.1, 3.2, 4.1, Lemmas 4.2, 4.4, Props. 5.3, 6.1 (Section 6.1, "Signs in the patterns"), Sections 1.4, 1.5, 3, 8.2, 8.3, Appendix A (Remarks A.1, A.3) | https://arxiv.org/pdf/2610.17662v1 | `e63d1229f05a9d1721a63822280e9718e82b6f2110d4477e8bc034bf842bfe81` |
| [BLR08] | A. Bartels, W. Lueck, H. Reich, On the Farrell-Jones conjecture and its applications, arXiv:math/0703548v1. The quoted sentence is in Section 0.6, p. 9 | https://arxiv.org/pdf/math/0703548v1 | `abf31bb65711d8a439250594f56ee51ac89ee4fdfb1035ef158855e5bad2f07c` |
| [BV98] | M. Burger, A. Valette, Idempotents in complex group rings, J. Lie Theory 8 (1998). Lemma 4.1, Proposition 4.2, Remark 4.3 | https://jolt.centre-mersenne.org/item/10.5802/jolt.142.pdf | `87affcc622bb34971968d97f69d0544c711b80fdb181c473415830ba48d9a04a` |
| [For73] | E. Formanek, Idempotents in Noetherian group rings, Canad. J. Math. 25 (1973). Theorems 1, 2 and 9, Lemma 7 | Cambridge Core PDF, doi:10.4153/CJM-1973-037-6 | `195f1f5f5bb9208d43e63ba0b086b4a325645b9d0097cf61cf8bba1b57f63f9b` |
| [Del97] | T. Delzant, Sur l'anneau d'un groupe hyperbolique, C. R. Acad. Sci. Paris 324 (1997). Theoreme and Proposition, p. 382 | https://irma.math.unistra.fr/~delzant/anneau.pdf | `08220244b4a07a9b1be335d08e58d18eaee905f9282ec5c37681842d1d79de56` |
| [ES04] | G. Elek, E. Szabo, Sofic groups and direct finiteness, arXiv:math/0305440v2. Section 1 (surjunctivity implies direct finiteness over finite fields) | https://arxiv.org/pdf/math/0305440v2 | `6767468abd74657631a7f8cf67e0f840ce3188c8605134774535a9d0d46b9e31` |
| [AD23] | G. Avramidi, T. Delzant, Group rings and hyperbolic geometry, Geom. Topol. 30(6):2337-2365 (2026), doi:10.2140/gt.2026.30.2337 (checked against Crossref); arXiv:2309.16791v2 | https://arxiv.org/abs/2309.16791v2 | - |

Further non-journal sources:

- [DM26a] S. Douglas and N. Mghirbi, *Amenable groups with nearly exponential sofic profile, and quantum channels
  that need nearly linear memory*, arXiv:2610.04271 (3 Oct 2026).
- [DM26b] S. Douglas and N. Mghirbi, *Non-soficity of OpenAI's torsion-free hyperbolic group*, Zenodo v1.0.1,
  doi:10.5281/zenodo.23202474 (record 23345877).
- [ST26] H. Sandhu and A. Thom, *An example of a non-sofic hyperbolic group*,
  https://andreasthom.github.io/pdf/hyperbolicnonsofic.pdf (circulated 13 Oct 2026).
- [OAI-Ten] OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 3,
  https://cdn.openai.com/pdf/ten-proofs-oai.pdf.
- [Min24] I. Mineyev, *The topology and geometry of units and zero-divisors: origami*,
  https://mineyev.web.illinois.edu/art/top-geom-uzd-origami.pdf (SHA-256 of the copy read on 14 Oct 2026:
  `e62e62a25056b3138b10ec9b4bccc6c806c989f17bdae5bb9d4d0e9b201fd3b6`).
- [MO26] MathOverflow question 513707, https://mathoverflow.net/questions/513707.

## Added for version 1.0.2 (read 26 October 2026)

| Key | Source | Read from | SHA-256 |
|---|---|---|---|
| [Mgh26] | N. Mghirbi, Lean 4 formalization of the Main Theorem (package `KaplanskyLean`): as received: statement file `Kaplansky/Challenge.lean`, audit file `docs/Audit.lean`, build record `Kaplansky/Final/PROGRESS.md`, status files `docs/STATUS_*.md`, vendoring record `OAI/VENDOR.md`; read, not rebuilt for this version. Published in `lean/KaplanskyLean/` with `Audit.lean` at its root, without the internal progress and status notes, with a version line added to the statement-file header and per-file modification notices added to three vendored files (so those files differ from the hashes below, which are of the received copy). The vendored OpenAI files were compared with openai/math at commit adc7f12: identical up to line endings, except the import lines recorded in `VENDOR.md` and `GraphMetric.lean`, which is lines 1-39 and the closing `end OAI` of OpenAI's `CayleyMetric.lean` (checked against commit 1581d4c on 26 October 2026) | copy received from the author, 26 October 2026 | `ecd42fc4b81be81132742ccfc9dc29cf125e99f9f58a428020b135733e626312` (Challenge.lean), `49576797253379f08f485195ccae01c614e7e1c58a67f2455361377f0a015508` (Audit.lean), `db0ef11dba520164aa0207f73b18bc5ab4af2230903d3d27157dac1c6c21e03b` (Final/PROGRESS.md), `7ba6e3e7b289124534eb019e2a6e8aa8c4523c613c2de7aa802afcf1bf193e7e` (VENDOR.md) |
| [BLMM26] | E. I. Bunina, W. Lee, A. Miasnikov, K. Muliarchyk, Failure of direct finiteness for group algebras in every odd characteristic, arXiv:2610.22536v1 (15 October 2026). Abstract, Theorem 1, Sections 1-3, 7.3, references | https://arxiv.org/pdf/2610.22536v1 | `284b2a477715f0aa4bcb504a404fa6504ab7b1b78318ae158cdc59ff7f38f9d2` |
| [ST26] | H. Sandhu, A. Thom, An example of a non-sofic hyperbolic group, arXiv:2610.24836v1 (17 October 2026). Section 1 (Agol and Haglund-Wise; Corollary B), Acknowledgments | https://arxiv.org/pdf/2610.24836v1 | `819c267abca9a69af2b5eaf7343cbf59d8990fa9f268bc3bd58593306cb19bdc` |
| [Ago13] | I. Agol, The virtual Haken conjecture, arXiv:1204.2810v1. Theorem 1.1 and the remark after it (hyperbolicity is necessary) | https://arxiv.org/pdf/1204.2810v1 | `ea8c7f392bed7e80a23968b09df7a3414bf0ce7d046ce479373a0d134910bc00` |
| [FSP26] | S. P. Fisher, P. Sanchez-Peralta, arXiv:2303.08165v4. Conjectures 1.1, 1.2, Theorem 1.3(1), Corollary 1.5; journal data from https://ems.press/doi/10.4171/jca/89 (J. Comb. Algebra 10 (2026), no. 1/2, 153-193; online 22 May 2024) | https://arxiv.org/pdf/2303.08165v4 | `4857e44cad3f1c85d53be2992f377d5dc5d5f79f5a6c74cfd1e542af482a4707` |
| [Iva26] | arXiv:2610.17662: still version 1 on 26 October 2026, same file as above | https://arxiv.org/pdf/2610.17662v1 | `e63d1229f05a9d1721a63822280e9718e82b6f2110d4477e8bc034bf842bfe81` |
| [Min24] | unchanged since 14 October 2026 (same hash as above) | https://mineyev.web.illinois.edu/art/top-geom-uzd-origami.pdf | `e62e62a25056b3138b10ec9b4bccc6c806c989f17bdae5bb9d4d0e9b201fd3b6` |
| [DM26b] | now cited at its latest version, 1.1.0 (14 October 2026), doi:10.5281/zenodo.23374284 | Zenodo API, record 23374284 | - |
| [Mia26] | Y. T. Miah, Hadamard designs and incidence repair for Kaplansky's direct-finiteness problem, Zenodo record 23485436 (19 October 2026). Abstract, Section 1 (the terminal matching is found by a terminating existence-based search), Section 8 (the selection) | https://zenodo.org/records/23485436 (file `Miah_Hadamard_Designs.pdf`, MD5 as deposited) | `ddf976693881acdbf42ed52144597fc5ee8edb2c470ce9740d3418cbb7460771` |
| [Sta91] | Contents page of *Group Theory from a Geometrical Viewpoint* (Trieste, 1990; eds. E. Ghys, A. Haefliger, A. Verjovsky; World Scientific, 1991), reproduced at the front of M. R. Bridson's thesis scan: "Non-positively curved triangles of groups", J. R. Stallings alone, p. 491 (next chapter p. 504) | https://people.maths.ox.ac.uk/bridson/papers/thesis.pdf | `dc75f5c9338beab89fdf3c2bc52839813f7c3bfa425e0710779ddd80ec011b63` |
| [DHJ15] | K. Dykema, T. Heister, K. Juschenko, Finitely presented groups related to Kaplansky's direct finiteness conjecture, author-hosted version dated 24 November 2014. Abstract and Section 1 (ULIE groups; ranks (3, n), n <= 11, and (5, 5) over F_2); journal data Exp. Math. 24(3):326-338 (2015), doi:10.1080/10586458.2014.993051, from Crossref | https://web.ma.utexas.edu/users/juschenko/files/Dykema-Juschenko-Heister.pdf | `094c3b5e61bef0a6729eb4029b249895d937bd755c3410787525c139d23f835b` |
| [Bar23] | L. Bartholdi, On Gardam's and Murray's units in group rings, Algebra Discrete Math. 35(1):22-29 (2023), doi:10.12958/adm2053. Abstract and Section 1 | https://admjournal.luguniv.edu.ua/index.php/adm/article/viewFile/2053/pdf | `33d61756a47aaa3aff98ce5e203e8a7bcb5d580dc652cd7292757cdb4f567f45` |

The bibliographic data of the paper's entries were checked on 26 October 2026 against Crossref, the arXiv API,
Zenodo, and publisher or library pages; a few conference volumes, a thesis and an early proceedings paper without
an online record were checked against their standard citations.
