# Licensing

Copyright 2026 Nidhal Mghirbi and Seth Douglas.

- **Paper and documentation.** Unless separately credited, the authors' material in this repository is licensed
  under the **Creative Commons Attribution 4.0 International License (CC BY 4.0)**: the paper (`paper/main.pdf`),
  its LaTeX source (`paper/main.tex`), the recorded outputs of the checks (`verify/*.out`), and the documentation
  (`README.md`, `DEPENDENCIES.md`, `SOURCES.md`). See [the full license](LICENSE-CC-BY-4.0.txt).
- **Scripts.** The authors' scripts (the check programs in `verify/`, `*.py` and `run_all.sh`, the build
  script `paper/build.py` and `tools/check_abstract.py`) are licensed under the **MIT License** or the
  **Apache License 2.0**, at your option.
  See [the MIT License](LICENSE-MIT.txt), [the Apache License 2.0](LICENSE-APACHE-2.0.txt) and [NOTICE](NOTICE).

- **Lean development.** `lean/KaplanskyLean/` (except its `OAI/` folder) is Copyright 2026 Nidhal Mghirbi, licensed under
  the **Apache License 2.0** (`lean/KaplanskyLean/LICENSE`).
- **Vendored OpenAI Lean modules.** `lean/KaplanskyLean/OAI/` redistributes Lean modules from OpenAI's repository
  https://github.com/openai/math (commit 1581d4c) under OpenAI's Apache License 2.0
  (`lean/KaplanskyLean/OAI/LICENSE-APACHE-2.0-OpenAI`). No line is changed except import lines and a per-file modification notice, and one file,
  `GraphMetric.lean`, is an excerpt of OpenAI's `CayleyMetric.lean`; both are recorded in
  `lean/KaplanskyLean/OAI/VENDOR.md`.

These grants do not alter the rights in third-party material or cited work, including OpenAI's preprints and
repository; apart from the vendored Lean modules above, OpenAI's material is not redistributed here. See [NOTICE](NOTICE).
