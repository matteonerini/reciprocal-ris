# Can Reciprocal RIS Perform as Non-Reciprocal RIS?

This repository contains a [Lean 4](https://lean-lang.org) formalization of results in the paper

> M. Nerini, J. Vidal Alegría, B. Clerckx, "[Can reciprocal RIS perform as non-reciprocal RIS?](https://arxiv.org/abs/)," arXiv:, 2026.

## Usage

### Online

The Lean file `ReciprocalRIS.lean` is self-contained, as it only imports Mathlib. Therefore, it can be read, checked, and modified in the browser with [Lean 4 Web](https://live.lean-lang.org), without any installation, by following these links:

- [Open `ReciprocalRIS.lean` in Lean 4 Web](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fmatteonerini%2Freciprocal-ris%2Fmain%2FReciprocalRIS.lean)

Alternatively, copy its content and paste it into the Lean 4 Web editor.

Lean 4 Web uses a recent version of Mathlib, which may differ from the one used in this repository (see [Requirements](#requirements)).

### Local installation

1. Install VS Code and the Lean 4 extension, following the [official instructions](https://lean-lang.org/install/).
2. In VS Code, open the command palette (`Ctrl+Shift+P`, or `Cmd+Shift+P` on macOS) and run `Lean 4: Open Project: Download Project`. Alternatively, open a Lean file, click on the ∀ symbol in the top-right corner of the editor, and select `Open Project…` → `Download Project…`.
3. Enter the URL of this repository:
   ```
   https://github.com/matteonerini/reciprocal-ris
   ```
4. Select the directory where the project should be saved and a name for its folder (e.g., `reciprocal-ris`). The extension downloads the project and the precompiled Mathlib files, which takes a few minutes.
5. After the download, accept the suggestion to open the project folder. When the file `ReciprocalRIS.lean` is opened, the Lean Infoview shows the proof state at the cursor position.

## Requirements

- Lean `v4.35.0-rc2` (see [`lean-toolchain`](lean-toolchain))
- Mathlib `v4.35.0-rc2` (see [`lakefile.toml`](lakefile.toml))

## Acknowledgment

The authors used [Claude](https://claude.ai) (Anthropic) to assist in developing the Lean code, whose proofs are all checked by the Lean kernel.
The authors also thank the Mathlib community for developing and maintaining the [Mathlib](https://github.com/leanprover-community/mathlib4) library, on which this formalization builds.
